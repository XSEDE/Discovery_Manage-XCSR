#!/usr/bin/env python
#
# Router to synchronize XCSR information into the WAREHOUSE
#   *Support Contacts*
#   !   Write_GLUE2Contacts: Support Contacts -> glue2.{AdminDomain,Contact}
#   *ResourceProvider*
#   !   Write_GatewayProviders: Gateways -> ResourceProviders
#   !   Write_HPCProviders: CSR Site Information -> ResourceProviders (including XSEDE)
#   *Resource*
#   !   Write_NetworkService: Operational Software -> Resources
#   !   Write_OperationalSoftware: Operational Software -> Resources
#   !   Write_PackagedSoftware: Packaged Software -> Resources
#   !   Write_GLUE2Service: glue2.{AbstractService, Endpoint}
#   !   Write_GLUE2Software: glue2.{ApplicationEnvironment, ApplicationHandle}
#
# Author: JP Navarro, September 2018
#
# TODO:
#  ...
import argparse
from collections import Counter
import datetime
from datetime import datetime, tzinfo, timedelta
try:
    import http.client as httplib
except ImportError:
    import httplib
import json
import logging
import logging.handlers
import os
import pwd
import re
import shutil
import signal
import ssl
import sys
from time import sleep
from urllib.parse import urlparse

import django
django.setup()
from django.db import DataError, IntegrityError
from django.utils.dateparse import parse_datetime
from glue2_db.models import *
from resource_cat.models import *
from processing_status.process import ProcessingActivity
import pdb

from daemon import runner

class UTC(tzinfo):
    def utcoffset(self, dt):
        return timedelta(0)
    def tzname(self, dt):
        return 'UTC'
    def dst(self, dt):
        return timedelta(0)
utc = UTC()

def eprint(*args, **kwargs):
    print(*args, file=sys.stderr, **kwargs)

class WarehouseRouter():
    def __init__(self, peek_sleep=10, offpeek_sleep=60, max_stale=24 * 60):
        self.args = None
        self.config = {}
        self.src = {}
        self.dest = {}
        for var in ['uri', 'scheme', 'path']: # Where <full> contains <type>:<obj>
            self.src[var] = None
            self.dest[var] = None
        self.peak_sleep = peek_sleep * 60       # 10 minutes in seconds during peak business hours
        self.offpeek_sleep = offpeek_sleep * 60 # 60 minutes in seconds during off hours
        self.max_stale = max_stale * 60         # 24 hours in seconds force refresh
        self.application = os.path.basename(__file__)

        parser = argparse.ArgumentParser()
        parser.add_argument('daemon_action', nargs='?', choices=('start', 'stop', 'restart'), \
                            help='{start, stop, restart} daemon')
        parser.add_argument('-l', '--log', action='store', \
                            help='Logging level (default=warning)')
        parser.add_argument('-c', '--config', action='store', dest='config', required=True, \
                            help='Configuration file')
        parser.add_argument('--verbose', action='store_true', \
                            help='Verbose output')
        parser.add_argument('--daemon', action='store_true', \
                            help='Daemonize execution')
        parser.add_argument('--pdb', action='store_true', \
                            help='Run with Python debugger')
        self.args = parser.parse_args()

        if self.args.pdb:
            pdb.set_trace()

        # Load configuration file
        config_path = os.path.abspath(self.args.config)
        try:
            with open(config_path, 'r') as file:
                conf=file.read()
        except IOError as e:
            raise
        try:
            self.config = json.loads(conf)
        except ValueError as e:
            eprint('Error "{}" parsing config={}'.format(e, config_path))
            sys.exit(1)

        # Initialize logging from arguments, or config file, or default to WARNING as last resort
        numeric_log = None
        if self.args.log is not None:
            numeric_log = getattr(logging, self.args.log.upper(), None)
        if numeric_log is None and 'LOG_LEVEL' in self.config:
            numeric_log = getattr(logging, self.config['LOG_LEVEL'].upper(), None)
        if numeric_log is None:
            numeric_log = getattr(logging, 'WARNING', None)
        if not isinstance(numeric_log, int):
            raise ValueError('Invalid log level: {}'.format(numeric_log))
        self.logger = logging.getLogger('DaemonLog')
        self.logger.setLevel(numeric_log)
        self.formatter = logging.Formatter(fmt='%(asctime)s.%(msecs)03d %(levelname)s %(message)s', \
                                           datefmt='%Y/%m/%d %H:%M:%S')
        self.handler = logging.handlers.TimedRotatingFileHandler(self.config['LOG_FILE'], when='W6', \
                                                                 backupCount=999, utc=True)
        self.handler.setFormatter(self.formatter)
        self.logger.addHandler(self.handler)

        self.steps = []
        for s in self.config['STEPS']:
            try:
                srcurl = urlparse(s['SOURCE'])
            except:
                self.logger.error('Step SOURCE missing or invalid')
                sys.exit(1)
            if srcurl.scheme not in ['file', 'http', 'https']:
                self.logger.error('Source not {file, http, https}')
                sys.exit(1)
            
            try:
                dsturl = urlparse(s['DESTINATION'])
            except:
                self.logger.error('Step DESTINATION missing or invalid')
                sys.exit(1)
            if dsturl.scheme not in ['file', 'analyze', 'warehouse']:
                self.logger.error('Destination not {file, analyze, warehouse}')
                sys.exit(1)
            
            if srcurl.scheme in ['file'] and dsturl.scheme in ['file']:
                self.logger.error('Source and Destination can not both be a {file}')
                sys.exit(1)
            
            self.steps.append({'srcurl': srcurl, 'dsturl': dsturl, 'CONTYPE': s['CONTYPE']})

#        if self.args.daemon_action == 'start':
#            if self.src['scheme'] not in ['http', 'https'] or self.dest['scheme'] not in ['warehouse']:
#                self.logger.error('Can only daemonize when source=[http|https] and destination=warehouse')
#                sys.exit(1)

        if self.args.daemon_action:
            mode = 'daemon({})'.format(self.args.daemon_action)
            # Initialize logging, pidfile
            self.stdin_path = '/dev/null'
            if 'LOG_FILE' in self.config:
                self.stdout_path = self.config['LOG_FILE'].replace('.log', '.daemon.log')
                self.stderr_path = self.stdout_path
            else:
                self.stdout_path = '/dev/tty'
                self.stderr_path = '/dev/tty'
            self.SaveDaemonLog(self.stdout_path)
            self.pidfile_timeout = 5
            if 'PID_FILE' in self.config:
                self.pidfile_path =  self.config['PID_FILE']
            else:
                name = os.path.basename(__file__).replace('.py', '')
                self.pidfile_path = '/var/run/{}/{}.pid'.format(name ,name)
        else:
            mode = 'interactive'

        signal.signal(signal.SIGINT, self.exit_signal)
        signal.signal(signal.SIGTERM, self.exit_signal)
        self.logger.info('Starting {}, program={}, pid={}, uid={}({})'.format(mode, os.path.basename(__file__), os.getpid(), os.geteuid(), pwd.getpwuid(os.geteuid()).pw_name))

    def Get_HTTP(self, url, contype):
        headers = {}
        ctx = ssl.create_default_context(ssl.Purpose.CLIENT_AUTH)
        conn = httplib.HTTPSConnection(host=url.hostname, port=getattr(url, 'port', None), context=ctx)

        conn.request('GET', url.path, None , headers)
        self.logger.debug('HTTP GET {}'.format(url.geturl()))
        response = conn.getresponse()
        result = response.read().decode("utf-8-sig")
        self.logger.debug('HTTP RESP {} {} (returned {}/bytes)'.format(response.status, response.reason, len(result)))
        try:
            content = json.loads(result)
        except ValueError as e:
            self.logger.error('Response not in expected JSON format ({})'.format(e))
            return(None)
        else:
            return({contype: content})

    def Analyze_CONTENT(self, content):
        # Write when needed
        return(0, '')

    def Write_CACHE(self, file, content):
        data = json.dumps(content)
        with open(file, 'w') as my_file:
            my_file.write(data)
        self.logger.info('Serialized and wrote {} bytes to file={}'.format(len(data), file))
        return(0, '')

    def Read_CACHE(self, file, contype):
        with open(file, 'r') as my_file:
            data = my_file.read()
            my_file.close()
        try:
            content = json.loads(data)
            self.logger.info('Read and parsed {} bytes from file={}'.format(len(data), file))
            return({contype: content})
        except ValueError as e:
            self.logger.error('Error "{}" parsing file={}'.format(e, file))
            sys.exit(1)

    def SaveDaemonLog(self, path):
        # Save daemon log file using timestamp only if it has anything unexpected in it
        try:
            with open(path, 'r') as file:
                lines=file.read()
                file.close()
                if not re.match("^started with pid \d+$", lines) and not re.match("^$", lines):
                    ts = datetime.strftime(datetime.now(), '%Y-%m-%d_%H:%M:%S')
                    newpath = '{}.{}'.format(path, ts)
                    shutil.copy(path, newpath)
                    print('SaveDaemonLog as {}'.format(newpath))
        except Exception as e:
            print('Exception in SaveDaemonLog({})'.format(path))
        return

    def exit_signal(self, signal, frame):
        self.logger.critical('Caught signal={}, exiting...'.format(signal))
        sys.exit(0)

    def smart_sleep(self, last_run):
        # This functions sleeps, performs refresh checks, and returns when it's time to refresh
        while True:
            if 12 <= datetime.now(utc).hour <= 24: # Between 6 AM and 6 PM Central (~12 to 24 UTC)
                current_sleep = self.peak_sleep
            else:
                current_sleep = self.offpeek_sleep
            self.logger.debug('sleep({})'.format(current_sleep))
            sleep(current_sleep)

            # Force a refresh every 12 hours at Noon and Midnight UTC
            now_utc = datetime.now(utc)
            if ( (now_utc.hour < 12 and last_run.hour > 12) or \
                (now_utc.hour > 12 and last_run.hour < 12) ):
                self.logger.info('REFRESH TRIGGER: Every 12 hours')
                return

            # Force a refresh every max_stale seconds
            since_last_run = now_utc - last_run
            if since_last_run.seconds > self.max_stale:
                self.logger.info('REFRESH TRIGGER: Stale {}/seconds above thresdhold of {}/seconds'.format(since_last_run.seconds, self.max_stale) )
                return

    def run(self):
        while True:
            self.STATS = Counter()
            self.HANDLED_DURATIONS = {}

            for s in self.steps:
                start_utc = datetime.now(utc)
                pa_application=os.path.basename(__file__)
                pa_function=s['dsturl'].path
                pa_topic = s['CONTYPE']
                pa_id = '{}:{}:{}:{}->{}'.format(pa_application, pa_function, pa_topic, s['srcurl'].scheme, s['dsturl'].scheme)
                pa_about = 'xsede.org'
                pa = ProcessingActivity(pa_application, pa_function, pa_id , pa_topic, pa_about)
                
                if s['srcurl'].scheme == 'file':
                    content = self.Read_CACHE(s['srcurl'].path, s['CONTYPE'])
                else:
                    content = self.Get_HTTP(s['srcurl'], s['CONTYPE'])

                if s['CONTYPE'] not in content:
                    (rc, message) = (False, 'JSON is missing the \'{}\' element'.format(contype))
                    self.logger.error(msg)
                elif s['dsturl'].scheme == 'file':
                    (rc, message) = self.Write_CACHE(s['dsturl'].path, content)
                elif s['dsturl'].scheme == 'analyze':
                    (rc, message) = self.Analyze_CONTENT(content)
                elif s['dsturl'].scheme == 'warehouse':
                    (rc, message) = getattr(self, pa_function)(content, s['CONTYPE'])
                if not rc and message == '':  # No errors
                    message = 'Processed {} in {:.3f}/seconds'.format(pa_function, (datetime.now(utc) - start_utc).total_seconds())
                pa.FinishActivity(rc, message)
     
            if not self.args.daemon_action:
                break
            self.smart_sleep(start_utc)
                
    def log_target(self, me):
        summary_msg = 'Processed {} in {:.3f}/seconds: {}/updates, {}/deletes, {}/skipped'.format(me, self.HANDLED_DURATIONS[me], self.STATS[me + '.Update'], self.STATS[me + '.Delete'], self.STATS[me + '.Skip'])
        self.logger.info(summary_msg)

########## CUSTOMIZATIONS START ##########
    def Write_Glue2Contacts(self, content, contype):
        ####################################
        ### AdminDomain
        ####################################
        me = 'AdminDomain'
#        jp = sys._getframe().f_code.co_name
        self.HANDLED_DURATIONS[me] = getattr(self.HANDLED_DURATIONS, me, 0)
        self.cur = {}   # Current items
        self.new = {}   # New items
        start_utc = datetime.now(utc)

        for item in AdminDomain.objects.all():
            self.cur[item.ID] = item

        for p_res in content[contype]:
            ID='urn:glue2:AdminDomain:{}'.format(p_res['GlobalID'])
            try:
                model = AdminDomain(ID=ID,
                                Name=p_res['Name'],
                                CreationTime=start_utc,
                                Validity=None,
                                EntityJSON=p_res,
                                Description=p_res['Description'],
                                WWW=p_res['ContactURL'],
                                Owner=p_res['GlobalID'],
                                )
                model.save()
                self.logger.debug('{} ID={}'.format(contype, ID))
                self.new[ID]=model
                self.STATS.update({me + '.Update'})
            except (DataError, IntegrityError) as e:
                msg = '{} saving ID={}: {}'.format(type(e).__name__, ID, e.message)
                self.logger.error(msg)
                return(False, msg)

        for id in self.cur:
            if id not in self.new:
                try:
                    AdminDomain.objects.filter(ID=id).delete()
                    self.STATS.update({me + '.Delete'})
                    self.logger.info('Deleted ID={}'.format(id))
                except (DataError, IntegrityError) as e:
                    self.logger.error('{} deleting ID={}: {}'.format(type(e).__name__, id, e.message))

        self.HANDLED_DURATIONS[me] += (datetime.now(utc) - start_utc).total_seconds()
        self.log_target(me)
        
        ####################################
        ### Contact
        ####################################
        me = 'Contact'
        self.HANDLED_DURATIONS[me] = getattr(self.HANDLED_DURATIONS, me, 0)
        self.cur = {}   # Current items
        self.new = {}   # New items
        start_utc = datetime.now(utc)

        for item in Contact.objects.filter(Type=contype):
            self.cur[item.ID] = item

        field_to_method_map = {'ContactURL': 'web',
                    'ContactEmail': 'e-mail',
                    'ContactPhone': 'phone'}

        for p_res in content[contype]:
            for field in field_to_method_map:
                if len(p_res.get(field, '') or '') < 1: # Exclude null, empty
                    continue
                method = field_to_method_map[field]

                ID='urn:glue2:Contact:{}:{}'.format(method, p_res['GlobalID'])

                if field == 'ContactEmail':
                    Name = p_res['Name'] + ' (e-mail)'
                    Detail = 'mailto:{}'.format(p_res[field])
                elif field == 'ContactPhone':
                    Name = p_res['Name'] + ' (phone)'
                    if p_res[field][:1] == '+':
                        Detail = 'tel:{}'.format(p_res[field])
                    else:
                        Detail = 'tel:+{}'.format(p_res[field])
                else: # field == 'ContactURL' and for default
                    Name = p_res['Name'] + ' (web)'
                    Detail = p_res[field]

                try:
                    model = Contact(ID=ID,
                                    Name=Name,
                                    CreationTime=start_utc,
                                    Validity=None,
                                    EntityJSON=p_res,
                                    Detail=Detail,
                                    Type=method,
                                    )
                    model.save()
                    self.logger.debug('{} ID={}'.format(contype, ID))
                    self.new[ID]=model
                    self.STATS.update({me + '.Update'})
                except (DataError, IntegrityError) as e:
                    msg = '{} saving ID={}: {}'.format(type(e).__name__, ID, e.message)
                    self.logger.error(msg)
                    return(False, msg)

        for id in self.cur:
            if id not in self.new:
                try:
                    Contact.objects.filter(ID=id).delete()

                    self.STATS.update({me + '.Delete'})
                    self.logger.info('Deleted ID={}'.format(id))
                except (DataError, IntegrityError) as e:
                    self.logger.error('{} deleting ID={}: {}'.format(type(e).__name__, id, e.message))

        self.HANDLED_DURATIONS[me] += (datetime.now(utc) - start_utc).total_seconds()
        self.log_target(me)
        return(0, '')

    def Write_GatewayProviders(self, content, contype):
        ####################################
        ### ResourceProvider
        ####################################
        me = 'ResourceProvider'
        self.HANDLED_DURATIONS[me] = getattr(self.HANDLED_DURATIONS, me, 0)
        my_idsuffix = 'urn:glue2:GlobalResourceProvider:Gateway'
        my_affiliation = 'xsede.org'
        self.cur = {}   # Current items
        self.new = {}   # New items
        start_utc = datetime.now(utc)

        for item in ResourceProvider.objects.filter(Affiliation__exact=my_affiliation).filter(ID__startswith=my_idsuffix):
            self.cur[item.ID] = item

        for item in content[contype]:
            local_id=item['DrupalNodeid'] + '.drupal.xsede.org'
            ID='{}:{}'.format(my_idsuffix, local_id)

            try:
                model = ResourceProvider(ID=ID,
                                Name=item['Name'],
                                CreationTime=start_utc,
                                Validity=None,
                                EntityJSON=item,
                                Affiliation=my_affiliation,
                                LocalID=local_id,
                        )
                model.save()
                self.logger.debug('{} ID={}'.format(contype, ID))
                self.new[ID]=model
                self.STATS.update({me + '.Update'})
            except (DataError, IntegrityError) as e:
                msg = '{} saving ID={}: {}'.format(type(e).__name__, ID, e.message)
                self.logger.error(msg)
                return(False, msg)

        for id in self.cur:
            if id not in self.new:
                try:
                    ResourceProvider.objects.filter(ID=id).delete()
                    self.STATS.update({me + '.Delete'})
                    self.logger.info('Deleted ID={}'.format(id))
                except (DataError, IntegrityError) as e:
                    self.logger.error('{} deleting ID={}: {}'.format(type(e).__name__, id, e.message))

        self.HANDLED_DURATIONS[me] += (datetime.now(utc) - start_utc).total_seconds()
        self.log_target(me)
        return(0, '')

    def Write_HPCProviders(self, content, contype):
        ####################################
        ### ResourceProvider
        ####################################
        me = 'ResourceProvider'
        self.HANDLED_DURATIONS[me] = getattr(self.HANDLED_DURATIONS, me, 0)
        my_idsuffix = 'urn:glue2:GlobalResourceProvider:HPC_Provider'
        my_affiliation = 'xsede.org'
        self.cur = {}   # Current items
        self.new = {}   # New items
        start_utc = datetime.now(utc)

        for item in ResourceProvider.objects.filter(Affiliation__exact=my_affiliation).filter(ID__startswith=my_idsuffix):
            self.cur[item.ID] = item

        for item in content[contype]:
            local_id=item['DrupalNodeid'] + '.drupal.xsede.org'
            ID='{}:{}'.format(my_idsuffix, item['SiteId'])

            try:
                model = ResourceProvider(ID=ID,
                                Name=item['Name'],
                                CreationTime=start_utc,
                                Validity=None,
                                EntityJSON=item,
                                Affiliation=my_affiliation,
                                LocalID=local_id,
                        )
                model.save()
                self.logger.debug('{} ID={}'.format(contype, ID))
                self.new[ID]=model
                self.STATS.update({me + '.Update'})
            except (DataError, IntegrityError) as e:
                msg = '{} saving ID={}: {}'.format(type(e).__name__, ID, e.message)
                self.logger.error(msg)
                return(False, msg)

        for id in self.cur:
            if id not in self.new:
                try:
                    ResourceProvider.objects.filter(ID=id).delete()
                    self.STATS.update({me + '.Delete'})
                    self.logger.info('Deleted ID={}'.format(id))
                except (DataError, IntegrityError) as e:
                    self.logger.error('{} deleting ID={}: {}'.format(type(e).__name__, id, e.message))

        self.HANDLED_DURATIONS[me] += (datetime.now(utc) - start_utc).total_seconds()
        self.log_target(me)
        return(0, '')

    def Write_NetworkService(self, content, contype):
        ####################################
        ### Resource
        ####################################
        me = 'Resource'
        self.HANDLED_DURATIONS[me] = getattr(self.HANDLED_DURATIONS, me, 0)
        my_idsuffix = 'urn:glue2:NetworkService:XCSR'
        my_affiliation = 'xsede.org'
        self.cur = {}   # Current items
        self.new = {}   # New items
        start_utc = datetime.now(utc)

        for item in Resource.objects.filter(Affiliation__exact=my_affiliation).filter(ID__startswith=my_idsuffix):
            self.cur[item.ID] = item

        for item in content[contype]:
            if item['AccessType'] != 'Network Service':
                continue
            eu=urlparse(item['NetworkServiceEndpoints'])
            local_id=item['DrupalNodeid'] + '.drupal.xsede.org'
            ID='{}:{}:{}'.format(my_idsuffix, eu.netloc, local_id)
            if item['ScienceGateway'] is not None and len(item['ScienceGateway']) > 0:
                provider='urn:glue2:GlobalResourceProvider:Gateway:{}.gateways.xsede.org'.format(item['ScienceGateway'])
            elif item['HostingResource'] is not None and len(item['HostingResource']) > 0 and len(item['HostingResourceID']) > 0:
                provider='urn:glue2:GlobalResourceProvider:HPC_Provider:{}'.format(item['HostingResourceID'])
            else:
                provider='urn:glue2:GlobalResourceProvider:HPC_Provider:xsede.org'

            try:
                model = Resource(ID=ID,
                                Name=item['Title'],
                                CreationTime=start_utc,
                                Validity=None,
                                EntityJSON=item,
                                Affiliation=my_affiliation,
                                ProviderID=provider,
                                Type='NetworkService',
                                Description=item['Description'],
                                QualityLevel=item['ServingState'],
                                LocalID=local_id,
                                Keywords=item['Keywords'],
                        )
                model.save()
                self.logger.debug('{} ID={}'.format(contype, ID))
                self.new[ID]=model
                self.STATS.update({me + '.Update'})
            except (DataError, IntegrityError) as e:
                msg = '{} saving ID={}: {}'.format(type(e).__name__, ID, e.message)
                self.logger.error(msg)
                return(False, msg)

        for id in self.cur:
            if id not in self.new:
                try:
                    Resource.objects.filter(ID=id).delete()
                    self.STATS.update({me + '.Delete'})
                    self.logger.info('Deleted ID={}'.format(id))
                except (DataError, IntegrityError) as e:
                    self.logger.error('{} deleting ID={}: {}'.format(type(e).__name__, id, e.message))

        self.HANDLED_DURATIONS[me] += (datetime.now(utc) - start_utc).total_seconds()
        self.log_target(me)
        return(0, '')

    def Write_GLUE2Service(self, content, contype):
        ####################################
        ### Resource
        ####################################
        me = 'Resource'
        self.HANDLED_DURATIONS[me] = getattr(self.HANDLED_DURATIONS, me, 0)
        my_idsuffix = 'urn:glue2:IPFEndpoint'
        my_affiliation = 'xsede.org'
        self.cur = {}   # Current items
        self.new = {}   # New items
        start_utc = datetime.now(utc)

        for item in Resource.objects.filter(Affiliation__exact=my_affiliation).filter(ID__startswith=my_idsuffix):
            self.cur[item.ID] = item

        for item in content[contype]:
            eu=urlparse(item['URL'])
            local_id=item['ID']
            ID=item['ID'].replace(':Endpoint:', ':IPFEndpoint:')
            provider='urn:glue2:GlobalResourceProvider:HPC_Provider:{}'.format(item['ResourceID'].split('.', 1)[1])
            if item['InterfaceName']=='org.globus.GridFTP':
                Name='GridFTP data transfer endpoint'
                Description='Globus GridFTP data transfer endpoint'
                Keywords='gridftp,data,transfer'
            elif item['InterfaceName']=='org.globus.openssh':
                Name='GSI OpenSSH login service'
                Description='Globus GSI OpenSSH remote login service'
                Keywords='openssh,scp,ssh,login'
            else:
                Name=''
                Description=''
                Keywords=''
            try:
                model = Resource(ID=ID,
                                Name=Name,
                                CreationTime=start_utc,
                                Validity=None,
                                EntityJSON=item,
                                Affiliation=my_affiliation,
                                ProviderID=provider,
                                Type='NetworkService',
                                Description=Description,
                                QualityLevel=item['QualityLevel'],
                                LocalID=local_id,
                                Keywords=Keywords,
                        )
                model.save()
                self.logger.debug('{} ID={}'.format(contype, ID))
                self.new[ID]=model
                self.STATS.update({me + '.Update'})
            except (DataError, IntegrityError) as e:
                msg = '{} saving ID={}: {}'.format(type(e).__name__, ID, e.message)
                self.logger.error(msg)
                return(False, msg)

        for id in self.cur:
            if id not in self.new:
                try:
                    Resource.objects.filter(ID=id).delete()
                    self.STATS.update({me + '.Delete'})
                    self.logger.info('Deleted ID={}'.format(id))
                except (DataError, IntegrityError) as e:
                    self.logger.error('{} deleting ID={}: {}'.format(type(e).__name__, id, e.message))

        self.HANDLED_DURATIONS[me] += (datetime.now(utc) - start_utc).total_seconds()
        self.log_target(me)
        return(0, '')

    def Write_GLUE2Software(self, content, contype):
        ####################################
        ### Resource
        ####################################
        me = 'Resource'
        self.HANDLED_DURATIONS[me] = getattr(self.HANDLED_DURATIONS, me, 0)
        my_idsuffix = 'urn:glue2:IPFSoftware'
        my_affiliation = 'xsede.org'
        self.cur = {}   # Current items
        self.new = {}   # New items
        start_utc = datetime.now(utc)

        for item in Resource.objects.filter(Affiliation__exact=my_affiliation).filter(ID__startswith=my_idsuffix):
            self.cur[item.ID] = item

        for item in content[contype]:
            local_id=item['ID']
            ID=item['ID'].replace(':ApplicationHandle:', ':IPFSoftware:')
            provider='urn:glue2:GlobalResourceProvider:HPC_Provider:{}'.format(item['ResourceID'].split('.', 1)[1])
            try:
                model = Resource(ID=ID,
                                Name=item['AppName'],
                                CreationTime=start_utc,
                                Validity=None,
                                EntityJSON=item,
                                Affiliation=my_affiliation,
                                ProviderID=provider,
                                Type='ExecutableSoftware',
                                Description=item['Description'],
                                QualityLevel='production',
                                LocalID=local_id,
                                Keywords=','.join(item['Keywords']),
                        )
                model.save()
                self.logger.debug('{} ID={}'.format(contype, ID))
                self.new[ID]=model
                self.STATS.update({me + '.Update'})
            except (DataError, IntegrityError) as e:
                msg = '{} saving ID={}: {}'.format(type(e).__name__, ID, e.message)
                self.logger.error(msg)
                return(False, msg)

        for id in self.cur:
            if id not in self.new:
                try:
                    Resource.objects.filter(ID=id).delete()
                    self.STATS.update({me + '.Delete'})
                    self.logger.info('Deleted ID={}'.format(id))
                except (DataError, IntegrityError) as e:
                    self.logger.error('{} deleting ID={}: {}'.format(type(e).__name__, id, e.message))

        self.HANDLED_DURATIONS[me] += (datetime.now(utc) - start_utc).total_seconds()
        self.log_target(me)
        return(0, '')

    def Write_OperationalSoftware(self, content, contype):
        ####################################
        ### Resource
        ####################################
        me = 'Resource'
        self.HANDLED_DURATIONS[me] = getattr(self.HANDLED_DURATIONS, me, 0)
        my_idsuffix = 'urn:glue2:ExecutableSoftware'
        my_affiliation = 'xsede.org'
        self.cur = {}   # Current items
        self.new = {}   # New items
        start_utc = datetime.now(utc)

        for item in Resource.objects.filter(Affiliation__exact=my_affiliation).filter(ID__startswith=my_idsuffix):
            self.cur[item.ID] = item

        for item in content[contype]:
            if item['AccessType'] != 'Execution Environment':
                continue
            local_id=item['DrupalNodeid'] + '.drupal.xsede.org'
            ID='{}:{}:{}:{}'.format(my_idsuffix, item['HostingResourceID'], item['ExecutionHandles'], local_id)
            if item['ScienceGateway'] is not None and len(item['ScienceGateway']) > 0:
                provider='urn:glue2:GlobalResourceProvider:{}.gateways.xsede.org'.format(item['ScienceGateway'])
            elif item['HostingResource'] is not None and len(item['HostingResource']) > 0 and len(item['HostingResourceID']) > 0:
                provider='urn:glue2:GlobalResourceProvider:HPC_Provider:{}'.format(item['HostingResourceID'])
            else:
                provider='urn:glue2:GlobalResourceProvider:HPC_Provider:xsede.org'

            try:
                model = Resource(ID=ID,
                                Name=item['Title'],
                                CreationTime=start_utc,
                                Validity=None,
                                EntityJSON=item,
                                Affiliation=my_affiliation,
                                ProviderID=provider,
                                Type='ExecutableSoftware',
                                Description=item['Description'],
                                QualityLevel=item['ServingState'],
                                LocalID=local_id,
                                Keywords=item['Keywords'],
                        )
                model.save()
                self.logger.debug('{} ID={}'.format(contype, ID))
                self.new[ID]=model
                self.STATS.update({me + '.Update'})
            except (DataError, IntegrityError) as e:
                msg = '{} saving ID={}: {}'.format(type(e).__name__, ID, e.message)
                self.logger.error(msg)
                return(False, msg)

        for id in self.cur:
            if id not in self.new:
                try:
                    Resource.objects.filter(ID=id).delete()
                    self.STATS.update({me + '.Delete'})
                    self.logger.info('Deleted ID={}'.format(id))
                except (DataError, IntegrityError) as e:
                    self.logger.error('{} deleting ID={}: {}'.format(type(e).__name__, id, e.message))

        self.HANDLED_DURATIONS[me] += (datetime.now(utc) - start_utc).total_seconds()
        self.log_target(me)
        return(0, '')

    def Write_PackagedSoftware(self, content, contype):
        ####################################
        ### Resource
        ####################################
        me = 'Resource'
        self.HANDLED_DURATIONS[me] = getattr(self.HANDLED_DURATIONS, me, 0)
        my_idsuffix = 'urn:glue2:PackagedSoftware'
        my_affiliation = 'xsede.org'
        self.cur = {}   # Current items
        self.new = {}   # New items
        start_utc = datetime.now(utc)

        for item in Resource.objects.filter(Affiliation__exact=my_affiliation).filter(ID__startswith=my_idsuffix):
            self.cur[item.ID] = item

        for item in content[contype]:
            local_id=item['DrupalNodeid'] + '.drupal.xsede.org'
            ID='{}:{}:{}:{}'.format(my_idsuffix, item['Title'], item['Version'], local_id)
            provider=''

            try:
                model = Resource(ID=ID,
                                Name=item['Title'],
                                CreationTime=start_utc,
                                Validity=None,
                                EntityJSON=item,
                                Affiliation=my_affiliation,
                                ProviderID=provider,
                                Type='PackagedSoftware',
                                Description=item['Description'],
                                QualityLevel=item['DeclaredStatus'],
                                LocalID=local_id,
                                Keywords=item['Keywords'],
                        )
                model.save()
                self.logger.debug('{} ID={}'.format(contype, ID))
                self.new[ID]=model
                self.STATS.update({me + '.Update'})
            except (DataError, IntegrityError) as e:
                msg = '{} saving ID={}: {}'.format(type(e).__name__, ID, e.message)
                self.logger.error(msg)
                return(False, msg)

        for id in self.cur:
            if id not in self.new:
                try:
                    Resource.objects.filter(ID=id).delete()
                    self.STATS.update({me + '.Delete'})
                    self.logger.info('Deleted ID={}'.format(id))
                except (DataError, IntegrityError) as e:
                    self.logger.error('{} deleting ID={}: {}'.format(type(e).__name__, id, e.message))

        self.HANDLED_DURATIONS[me] += (datetime.now(utc) - start_utc).total_seconds()
        self.log_target(me)
        return(0, '')

########## CUSTOMIZATIONS END ##########

if __name__ == '__main__':
    router = WarehouseRouter()
    if router.args.daemon_action is None:   # Interactive execution, just call the run function
        myrouter = router.run()
        sys.exit(0)
    
    # Daemon execution
    daemon_runner = runner.DaemonRunner(router)
    daemon_runner.daemon_context.files_preserve=[router.handler.stream]
    daemon_runner.daemon_context.working_directory=router.config['RUN_DIR']
    daemon_runner.do_action()