#!/usr/bin/env python3
#
# Router to synchronize RSP manually entered information into the WAREHOUSE
#   Support Contact -> GLUE2
#       Write_Glue2Contacts: CSR Support Contacts -> glue2.{AdminDomain,Contact}
#
#   Gateways, Sites -> ResourceProvider
#       Write_GatewayProviders: CSR Gateways -> ResourceProviders
#            ID_suffix = 'urn:glue2:GlobalResourceProvider:Gateway' + ':' + DrupalNodeid + '.drupal.xsede.org'
#       Write_HPCProviders: CSR Site Information -> ResourceProviders (including XSEDE)
#            ID_suffix = 'urn:glue2:GlobalResourceProvider:HPC_Provider' + ':' + SiteID
#       Write_SupportProviders: CSR Support Contacts -> ResourceProviders
#            ID_suffix = 'urn:glue2:GlobalResourceProvider:Support' + ':' + StandardName
#
#   Operational Software, Services, Glue2 -> Resources
#       Write_NetworkService: CSR Operational Software -> Resources
#            ID_suffix = 'urn:glue2:NetworkService:XCSR' + ':' + Endpoint + DrupalNodeid + '.drupal.xsede.org'
#       Write_GLUE2Service: glue2.{AbstractService, Endpoint} -> Resources
#            ID_suffix = 'urn:glue2:IPFEndpoint' from Resource.ID.replace('Endpoint', 'IPFEndpoint')
#
#       Write_OperationalSoftware: CSR Operational Software -> Resources
#            ID_suffix = 'urn:glue2:ExecutableSoftware' + ':' + HostingResourceID + ':' + ExecutionHandles + ':' + DrupalNodeid + '.drupal.xsede.org'
#       Write_GLUE2Software: glue2.{ApplicationEnvironment, ApplicationHandle} -> Resources
#            ID_suffix = 'urn:glue2:IPFSoftware' from Resource.ID.replace('ApplicationHandle', 'IPFSoftware')
#
#    Packaged Software -> Resources
#       Write_PackagedSoftware: CSR Packaged Software -> Resources
#            ID_suffix = 'urn:glue2:PackagedSoftware' + ':' + Title + ':' + 'Version' + ':' + DrupalNodeid + '.drupal.xsede.org'
#
# Author: JP Navarro, September 2018
#
# DISABLED and RETIRED early in 2021 when XSEDE switched from Resources to Resources V3
#
# TODO:
#  ...
import argparse
from collections import Counter
from datetime import datetime, tzinfo, timedelta
import http.client as httplib
import json
import logging
import logging.handlers
import os
from pid import PidFile
import pwd
import re
import shutil
import signal
import ssl
import sys, traceback
from time import sleep
from urllib.parse import urlparse

import django
django.setup()
from django.db import DataError, IntegrityError
from django.conf import settings
from django.utils.dateparse import parse_datetime
from glue2_db.models import *
from resource_cat.models import *
from processing_status.process import ProcessingActivity

import pdb

class UTC(tzinfo):
    def utcoffset(self, dt):
        return timedelta(0)
    def tzname(self, dt):
        return 'UTC'
    def dst(self, dt):
        return timedelta(0)
utc = UTC()

# Used during initialization before loggin is enabled
def eprint(*args, **kwargs):
    print(*args, file=sys.stderr, **kwargs)

class Router():
    def __init__(self):
        parser = argparse.ArgumentParser()
        parser.add_argument('daemonaction', nargs='?', choices=('start', 'stop', 'restart'), \
                            help='{start, stop, restart} daemon')
        parser.add_argument('--daemon', action='store_true', \
                            help='Daemonize execution')
        parser.add_argument('-l', '--log', action='store', \
                            help='Logging level (default=warning)')
        parser.add_argument('-c', '--config', action='store', dest='config', required=True, \
                            help='Configuration file')
        parser.add_argument('--pdb', action='store_true', \
                            help='Run with Python debugger')
        self.args = parser.parse_args()

        # Trace for debugging as early as possible
        if self.args.pdb:
            pdb.set_trace()

        # Load configuration file
        self.config_file = os.path.abspath(self.args.config)
        try:
            with open(self.config_file, 'r') as file:
                conf=file.read()
        except IOError as e:
            eprint('Error "{}" reading config={}'.format(e, config_path))
            sys.exit(1)
        try:
            self.config = json.loads(conf)
        except ValueError as e:
            eprint('Error "{}" parsing config={}'.format(e, config_path))
            sys.exit(1)

        if self.config.get('PID_FILE'):
            self.pidfile_path =  self.config['PID_FILE']
        else:
            name = os.path.basename(__file__).replace('.py', '')
            self.pidfile_path = '/var/run/{}/{}.pid'.format(name, name)

    def Setup(self, peak_sleep=10, offpeak_sleep=60, max_stale=24 * 60):
        # Initialize log level from arguments, or config file, or default to WARNING
        loglevel_str = (self.args.log or self.config.get('LOG_LEVEL', 'WARNING')).upper()
        loglevel_num = getattr(logging, loglevel_str, None)
        self.logger = logging.getLogger('DaemonLog')
        self.logger.setLevel(loglevel_num)
        self.formatter = logging.Formatter(fmt='%(asctime)s.%(msecs)03d %(levelname)s %(message)s', \
                                           datefmt='%Y/%m/%d %H:%M:%S')
        self.handler = logging.handlers.TimedRotatingFileHandler(self.config['LOG_FILE'], \
            when='W6', backupCount=999, utc=True)
        self.handler.setFormatter(self.formatter)
        self.logger.addHandler(self.handler)

        # Initialize stdout, stderr
        if self.args.daemon and 'LOG_FILE' in self.config:
            self.stdout_path = self.config['LOG_FILE'].replace('.log', '.daemon.log')
            self.stderr_path = self.stdout_path
            self.SaveDaemonStdOut(self.stdout_path)
            sys.stdout = open(self.stdout_path, 'wt+')
            sys.stderr = open(self.stderr_path, 'wt+')

        signal.signal(signal.SIGINT, self.exit_signal)
        signal.signal(signal.SIGTERM, self.exit_signal)

        self.logger.info('Starting program=%s pid=%s, uid=%s(%s)' % \
                     (os.path.basename(__file__), os.getpid(), os.geteuid(), pwd.getpwuid(os.geteuid()).pw_name))

        self.src = {}
        self.dest = {}
        for var in ['uri', 'scheme', 'path']: # Where <full> contains <type>:<obj>
            self.src[var] = None
            self.dest[var] = None
        self.peak_sleep = peak_sleep * 60       # 10 minutes in seconds during peak business hours
        self.offpeak_sleep = offpeak_sleep * 60 # 60 minutes in seconds during off hours
        self.max_stale = max_stale * 60         # 24 hours in seconds force refresh
        self.application = os.path.basename(__file__)
        self.memory = {} # For Memory_CONTENT

        self.steps = []
        show_warehouse = None
        for s in self.config['STEPS']:
            try:
                srcurl = urlparse(s['SOURCE'])
            except:
                self.logger.error('Step SOURCE missing or invalid')
                self.exit(1)
            if srcurl.scheme not in ['file', 'http', 'https']:
                self.logger.error('Source not {file, http, https}')
                self.exit(1)
            
            try:
                dsturl = urlparse(s['DESTINATION'])
            except:
                self.logger.error('Step DESTINATION missing or invalid')
                self.exit(1)
            if dsturl.scheme not in ['file', 'analyze', 'warehouse', 'memory']:
                self.logger.error('Destination not {file, analyze, warehouse, memory}')
                self.exit(1)
            
            if srcurl.scheme in ['file'] and dsturl.scheme in ['file']:
                self.logger.error('Source and Destination can not both be a {file}')
                self.exit(1)
                
            if dsturl.scheme == 'warehouse' and not show_warehouse:
                show_warehouse = settings.DATABASES['default']['HOST']
            self.steps.append({'srcurl': srcurl, 'dsturl': dsturl, 'CONTYPE': s['CONTYPE']})

# Each step has their own source and destination
#        self.logger.info('Source: ' + self.src['display'])
#        self.logger.info('Destination: ' + self.dest['display'])
        self.logger.info('Config: ' + self.config_file)
 
        if show_warehouse:
            self.logger.info('Destination warehouse database={}'.format(settings.DATABASES['default']['HOST']))

    def SaveDaemonStdOut(self, path):
        # Save daemon log file using timestamp only if it has anything unexpected in it
        try:
            file = open(path, 'r')
            lines = file.read()
            file.close()
            if not re.match("^started with pid \d+$", lines) and not re.match("^$", lines):
                ts = datetime.strftime(datetime.now(), '%Y-%m-%d_%H:%M:%S')
                newpath = '{}.{}'.format(path, ts)
                self.logger.debug('Saving previous daemon stdout to {}'.format(newpath))
                shutil.copy(path, newpath)
        except Exception as e:
            self.logger.error('Exception in SaveDaemonStdOut({})'.format(path))
        return

    def exit_signal(self, signum, frame):
        self.logger.critical('Caught signal={}({}), exiting with rc={}'.format(signum, signal.Signals(signum).name, signum))
        sys.exit(signum)

    def exit(self, rc):
        if rc:
            self.logger.error('Exiting with rc={}'.format(rc))
        sys.exit(rc)

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

    def Memory_CONTENT(self, content, contype, conkey):
        # Store in memory dictionary for reference by other processing steps
        self.memory[contype] = {}
        for item in content[contype]:
            try:
                self.memory[contype][item[conkey]] = item
            except:
                pass
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

    def smart_sleep(self, last_run):
        # This functions sleeps
        if 12 <= datetime.now(utc).hour <= 24: # Between 6 AM and 6 PM Central (~12 to 24 UTC)
            current_sleep = self.peak_sleep
        else:
            current_sleep = self.offpeak_sleep
        self.logger.debug('sleep({})'.format(current_sleep))
        sleep(current_sleep)

    def Run(self):
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
                elif s['dsturl'].scheme == 'memory':
                    (rc, message) = self.Memory_CONTENT(content, s['CONTYPE'], s['dsturl'].path)
                elif s['dsturl'].scheme == 'warehouse':
                    (rc, message) = getattr(self, pa_function)(content, s['CONTYPE'])
                if not rc and message == '':  # No errors
                    message = 'Processed {} in {:.3f}/seconds'.format(pa_function, (datetime.now(utc) - start_utc).total_seconds())
                pa.FinishActivity(rc, message)
     
            if not self.args.daemonaction:
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
        me = '{} to AdminDomain'.format(sys._getframe().f_code.co_name)
        self.HANDLED_DURATIONS[me] = getattr(self.HANDLED_DURATIONS, me, 0)
        self.cur = {}   # Current items
        self.new = {}   # New items
        start_utc = datetime.now(utc)

        for item in AdminDomain.objects.all():
            self.cur[item.ID] = item

        for p_res in content[contype]:
            # This now matches what is put in Resources V3
            ID='urn:ogf:glue2:info.xsede.org:resource:rsp:support.organizations:drupalnodeid:{}'.format(p_res['DrupalNodeid'])
            desc = p_res['Description']
            if desc is not None:
                desc = desc[:128]
            try:
                self.tag_from_application(p_res)
                model, created = AdminDomain.objects.update_or_create(
                                    ID=ID,
                                    defaults = {
                                        'Name': p_res['Name'],
                                        'CreationTime': start_utc,
                                        'Validity': None,
                                        'EntityJSON': p_res,
                                        'Description': desc,
                                        'WWW': p_res['ContactURL'],
                                        'Owner': p_res['GlobalID'],
                                    })
                model.save()
                self.logger.debug('{} ID={}'.format(contype, ID))
                self.new[ID]=model
                self.STATS.update({me + '.Update'})
            except (DataError, IntegrityError) as e:
                msg = '{} saving ID={}: {}'.format(type(e).__name__, ID, e)
                self.logger.error(msg)
                return(False, msg)

        for id in self.cur:
            if id not in self.new:
                try:
                    AdminDomain.objects.filter(ID=id).delete()
                    self.STATS.update({me + '.Delete'})
                    self.logger.info('Deleted ID={}'.format(id))
                except (DataError, IntegrityError) as e:
                    self.logger.error('{} deleting ID={}: {}'.format(type(e).__name__, id, e))

        self.HANDLED_DURATIONS[me] += (datetime.now(utc) - start_utc).total_seconds()
        self.log_target(me)
        
        ####################################
        ### Contact
        ####################################
        me = '{} to Contact'.format(sys._getframe().f_code.co_name)
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

                # This now matches what is put in Resources V3
                ID='urn:ogf:glue2:info.xsede.org:resource:rsp:support.organization.contacts:{}:drupalnodeid:{}'.format(method, p_res['DrupalNodeid'])

                if field == 'ContactEmail':
                    Name = p_res['Name'] + ' (by e-mail)'
                    Detail = 'mailto:{}'.format(p_res[field])
                elif field == 'ContactPhone':
                    Name = p_res['Name'] + ' (by phone)'
                    if p_res[field][:1] == '+':
                        Detail = 'tel:{}'.format(p_res[field])
                    else:
                        Detail = 'tel:+{}'.format(p_res[field])
                else: # field == 'ContactURL' and for default
                    Name = p_res['Name'] + ' (on the web)'
                    Detail = p_res[field]

                try:
                    self.tag_from_application(p_res)
                    model, created = Contact.objects.update_or_create(
                                        ID=ID,
                                        defaults = {
                                            'Name': Name,
                                            'CreationTime': start_utc,
                                            'Validity': None,
                                            'EntityJSON': p_res,
                                            'Detail': Detail,
                                            'Type': method
                                        })
                    model.save()
                    self.logger.debug('{} ID={}'.format(contype, ID))
                    self.new[ID]=model
                    self.STATS.update({me + '.Update'})
                except (DataError, IntegrityError) as e:
                    msg = '{} saving ID={}: {}'.format(type(e).__name__, ID, e)
                    self.logger.error(msg)
                    return(False, msg)

        for id in self.cur:
            if id not in self.new:
                try:
                    Contact.objects.filter(ID=id).delete()

                    self.STATS.update({me + '.Delete'})
                    self.logger.info('Deleted ID={}'.format(id))
                except (DataError, IntegrityError) as e:
                    self.logger.error('{} deleting ID={}: {}'.format(type(e).__name__, id, e))

        self.HANDLED_DURATIONS[me] += (datetime.now(utc) - start_utc).total_seconds()
        self.log_target(me)
        return(0, '')

    def Write_GatewayProviders(self, content, contype):
        ####################################
        ### ResourceProvider
        ####################################
        me = '{} to ResourceProvider'.format(sys._getframe().f_code.co_name)
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
            ID='{}:{}.{}'.format(my_idsuffix, item['Name'], 'gateways.xsede.org')

            try:
                model, created = ResourceProvider.objects.update_or_create(
                                    ID=ID,
                                    defaults = {
                                        'Name': item['Name'],
                                        'CreationTime': start_utc,
                                        'Validity': None,
                                        'EntityJSON': item,
                                        'Affiliation': my_affiliation,
                                        'LocalID': local_id
                                    })
                model.save()
                self.logger.debug('{} ID={}'.format(contype, ID))
                self.new[ID]=model
                self.STATS.update({me + '.Update'})
            except (DataError, IntegrityError) as e:
                msg = '{} saving ID={}: {}'.format(type(e).__name__, ID, e)
                self.logger.error(msg)
                return(False, msg)

        for id in self.cur:
            if id not in self.new:
                try:
                    ResourceProvider.objects.filter(ID=id).delete()
                    self.STATS.update({me + '.Delete'})
                    self.logger.info('Deleted ID={}'.format(id))
                except (DataError, IntegrityError) as e:
                    self.logger.error('{} deleting ID={}: {}'.format(type(e).__name__, id, e))

        self.HANDLED_DURATIONS[me] += (datetime.now(utc) - start_utc).total_seconds()
        self.log_target(me)
        return(0, '')

    def Write_HPCProviders(self, content, contype):
        ####################################
        ### ResourceProvider
        ####################################
        me = '{} to ResourceProvider'.format(sys._getframe().f_code.co_name)
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
            ID='{}:{}'.format(my_idsuffix, item['SiteID'])

            try:
                model, created = ResourceProvider.objects.update_or_create(
                                    ID=ID,
                                    defaults = {
                                        'Name': item['Name'],
                                        'CreationTime': start_utc,
                                        'Validity': None,
                                        'EntityJSON': item,
                                        'Affiliation': my_affiliation,
                                        'LocalID': local_id
                                    })
                model.save()
                self.logger.debug('{} ID={}'.format(contype, ID))
                self.new[ID]=model
                self.STATS.update({me + '.Update'})
            except (DataError, IntegrityError) as e:
                msg = '{} saving ID={}: {}'.format(type(e).__name__, ID, e)
                self.logger.error(msg)
                return(False, msg)

        for id in self.cur:
            if id not in self.new:
                try:
                    ResourceProvider.objects.filter(ID=id).delete()
                    self.STATS.update({me + '.Delete'})
                    self.logger.info('Deleted ID={}'.format(id))
                except (DataError, IntegrityError) as e:
                    self.logger.error('{} deleting ID={}: {}'.format(type(e).__name__, id, e))

        self.HANDLED_DURATIONS[me] += (datetime.now(utc) - start_utc).total_seconds()
        self.log_target(me)
        return(0, '')

    def Write_SupportProviders(self, content, contype):
        ####################################
        ### SupportProvider
        ####################################
        me = '{} to SupportProviders'.format(sys._getframe().f_code.co_name)
        self.HANDLED_DURATIONS[me] = getattr(self.HANDLED_DURATIONS, me, 0)
        my_idsuffix = 'urn:glue2:GlobalResourceProvider:Support'

        my_affiliation = 'xsede.org'
        self.cur = {}   # Current items
        self.new = {}   # New items
        start_utc = datetime.now(utc)

        for item in ResourceProvider.objects.filter(Affiliation__exact=my_affiliation).filter(ID__startswith=my_idsuffix):
            self.cur[item.ID] = item

        for item in content[contype]:
            if item['GlobalID'] == 'helpdesk.xsede.org':    # We're only using HPC_Provider for now
                continue
            local_id=item['DrupalNodeid'] + '.drupal.xsede.org'
            ID='{}:{}'.format(my_idsuffix, item['GlobalID'])

            try:
                model, created = ResourceProvider.objects.update_or_create(
                                    ID=ID,
                                    defaults = {
                                        'Name': item['ShortName'],
                                        'CreationTime': start_utc,
                                        'Validity': None,
                                        'EntityJSON': item,
                                        'Affiliation': my_affiliation,
                                        'LocalID': local_id
                                    })
                model.save()
                self.logger.debug('{} ID={}'.format(contype, ID))
                self.new[ID]=model
                self.STATS.update({me + '.Update'})
            except (DataError, IntegrityError) as e:
                msg = '{} saving ID={}: {}'.format(type(e).__name__, ID, e)
                self.logger.error(msg)
                return(False, msg)

        for id in self.cur:
            if id not in self.new:
                try:
                    ResourceProvider.objects.filter(ID=id).delete()
                    self.STATS.update({me + '.Delete'})
                    self.logger.info('Deleted ID={}'.format(id))
                except (DataError, IntegrityError) as e:
                    self.logger.error('{} deleting ID={}: {}'.format(type(e).__name__, id, e))

        self.HANDLED_DURATIONS[me] += (datetime.now(utc) - start_utc).total_seconds()
        self.log_target(me)
        return(0, '')

    def Write_NetworkService(self, content, contype):
        ####################################
        ### Resource
        ####################################
        me = '{} to Resource'.format(sys._getframe().f_code.co_name)
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
            if item['ScienceGatewayName'] is not None and len(item['ScienceGatewayName']) > 0:
                provider='urn:glue2:GlobalResourceProvider:Gateway:{}.gateways.xsede.org'.format(item['ScienceGatewayName'])
            elif item['HostingResourceName'] is not None and len(item['HostingResourceName']) > 0 and len(item['HostingResourceID']) > 0:
                try:
                    provider='urn:glue2:GlobalResourceProvider:HPC_Provider:{}'.format(self.memory['Resources'][item['HostingResourceID']]['SiteID'])
                except:
                    provider='urn:glue2:GlobalResourceProvider:HPC_Provider:{}'.format(item['HostingResourceID'])
            else:
                provider='urn:glue2:GlobalResourceProvider:HPC_Provider:xsede.org'

            new_item = item.copy()
            new_item['record_status'] = 1
            try:
                model, created = Resource.objects.update_or_create(
                                    ID=ID,
                                    defaults = {
                                        'Name': item['Title'],
                                        'CreationTime': start_utc,
                                        'Validity': None,
                                        'EntityJSON': new_item,
                                        'Affiliation': my_affiliation,
                                        'ProviderID': provider,
                                        'Type': 'NetworkService',
                                        'Description': item['Description'],
                                        'QualityLevel': item['ServingState'],
                                        'LocalID': local_id,
                                        'Keywords': item['Keywords']
                                    })
                model.save()
                self.logger.debug('{} ID={}'.format(contype, ID))
                self.new[ID]=model
                self.STATS.update({me + '.Update'})
            except (DataError, IntegrityError) as e:
                msg = '{} saving ID={}: {}'.format(type(e).__name__, ID, e)
                self.logger.error(msg)
                return(False, msg)

        for id in self.cur:
            if id not in self.new:
                try:
                    Resource.objects.filter(ID=id).delete()
                    self.STATS.update({me + '.Delete'})
                    self.logger.info('Deleted ID={}'.format(id))
                except (DataError, IntegrityError) as e:
                    self.logger.error('{} deleting ID={}: {}'.format(type(e).__name__, id, e))

        self.HANDLED_DURATIONS[me] += (datetime.now(utc) - start_utc).total_seconds()
        self.log_target(me)
        return(0, '')

    def Write_GLUE2Service(self, content, contype):
        ####################################
        ### Resource
        ####################################
        me = '{} to Resource'.format(sys._getframe().f_code.co_name)
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
            if item['InterfaceName']=='org.globus.gridftp':
                Name='GridFTP data transfer endpoint'
                Description='Globus GridFTP data transfer endpoint'
                Keywords='gridftp,data,transfer'
            elif item['InterfaceName']=='org.globus.openssh':
                Name='GSI OpenSSH login service'
                Description='Globus GSI OpenSSH remote login service'
                Keywords='openssh,scp,ssh,login'
            elif item['InterfaceName']=='org.globus.gram':
                Name='GRAM5 execution service'
                Description='Globus GRAM5 remote execution service'
                Keywords='gram5,job,execution'
            else:
                Name=item['InterfaceName']
                Description=item['ServiceType'] + ' ' + item['InterfaceName']
                Keywords=''
            
            new_item = item.copy()
            new_item['record_status'] = 1
            try:
                model, created = Resource.objects.update_or_create(
                                    ID=ID,
                                    defaults = {
                                        'Name': Name,
                                        'CreationTime': start_utc,
                                        'Validity': None,
                                        'EntityJSON': new_item,
                                        'Affiliation': my_affiliation,
                                        'ProviderID': provider,
                                        'Type': 'NetworkService',
                                        'Description': Description,
                                        'QualityLevel': item['QualityLevel'],
                                        'LocalID': local_id,
                                        'Keywords': Keywords
                                    })
                model.save()
                self.logger.debug('{} ID={}'.format(contype, ID))
                self.new[ID]=model
                self.STATS.update({me + '.Update'})
            except (DataError, IntegrityError) as e:
                msg = '{} saving ID={}: {}'.format(type(e).__name__, ID, e)
                self.logger.error(msg)
                return(False, msg)

        for id in self.cur:
            if id not in self.new:
                try:
                    Resource.objects.filter(ID=id).delete()
                    self.STATS.update({me + '.Delete'})
                    self.logger.info('Deleted ID={}'.format(id))
                except (DataError, IntegrityError) as e:
                    self.logger.error('{} deleting ID={}: {}'.format(type(e).__name__, id, e))

        self.HANDLED_DURATIONS[me] += (datetime.now(utc) - start_utc).total_seconds()
        self.log_target(me)
        return(0, '')

    def Write_GLUE2Software(self, content, contype):
        ####################################
        ### Resource
        ####################################
        me = '{} to Resource'.format(sys._getframe().f_code.co_name)
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
            new_item = item.copy()
            new_item['record_status'] = 1
            try:
                model, created = Resource.objects.update_or_create(
                                    ID=ID,
                                    defaults = {
                                        'Name': item['AppName'] + ' ' + item['AppVersion'],
                                        'CreationTime': start_utc,
                                        'Validity': None,
                                        'EntityJSON': new_item,
                                        'Affiliation': my_affiliation,
                                        'ProviderID': provider,
                                        'Type': 'ExecutableSoftware',
                                        'Description': item['Description'],
                                        'QualityLevel': item.get('SupportStatus', 'production'),
                                        'LocalID': local_id,
                                        'Keywords': ','.join(item['Keywords'])
                                    })
                model.save()
                self.logger.debug('{} ID={}'.format(contype, ID))
                self.new[ID]=model
                self.STATS.update({me + '.Update'})
            except (DataError, IntegrityError) as e:
                msg = '{} saving ID={}: {}'.format(type(e).__name__, ID, e)
                self.logger.error(msg)
                return(False, msg)

        for id in self.cur:
            if id not in self.new:
                try:
                    Resource.objects.filter(ID=id).delete()
                    self.STATS.update({me + '.Delete'})
                    self.logger.info('Deleted ID={}'.format(id))
                except (DataError, IntegrityError) as e:
                    self.logger.error('{} deleting ID={}: {}'.format(type(e).__name__, id, e))

        self.HANDLED_DURATIONS[me] += (datetime.now(utc) - start_utc).total_seconds()
        self.log_target(me)
        return(0, '')

    def Write_OperationalSoftware(self, content, contype):
        ####################################
        ### Resource
        ####################################
        me = '{} to Resource'.format(sys._getframe().f_code.co_name)
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
            if item['ScienceGatewayName'] is not None and len(item['ScienceGatewayName']) > 0:
                provider='urn:glue2:GlobalResourceProvider:Gateway:{}.gateways.xsede.org'.format(item['ScienceGatewayName'])
                my_type='GatewaySoftware'
            elif item['HostingResourceName'] is not None and len(item['HostingResourceName']) > 0 and len(item['HostingResourceID']) > 0:
                provider='urn:glue2:GlobalResourceProvider:HPC_Provider:{}'.format(item['HostingResourceID'])
                my_type='HPCExecutableSoftware'
            else:
                provider='urn:glue2:GlobalResourceProvider:HPC_Provider:xsede.org'
                my_type='NetworkService'
            
            new_item = item.copy()
            new_item['record_status'] = 1
            try:
                model, created = Resource.objects.update_or_create(
                                    ID=ID,
                                    defaults = {
                                        'Name': item['Title'],
                                        'CreationTime': start_utc,
                                        'Validity': None,
                                        'EntityJSON': new_item,
                                        'Affiliation': my_affiliation,
                                        'ProviderID': provider,
                                        'Type': my_type,
                                        'Description': item['Description'],
                                        'QualityLevel': item['ServingState'],
                                        'LocalID': local_id,
                                        'Keywords': item['Keywords']
                                    })
                model.save()
                self.logger.debug('{} ID={}'.format(contype, ID))
                self.new[ID]=model
                self.STATS.update({me + '.Update'})
            except (DataError, IntegrityError) as e:
                msg = '{} saving ID={}: {}'.format(type(e).__name__, ID, e)
                self.logger.error(msg)
                return(False, msg)

        for id in self.cur:
            if id not in self.new:
                try:
                    Resource.objects.filter(ID=id).delete()
                    self.STATS.update({me + '.Delete'})
                    self.logger.info('Deleted ID={}'.format(id))
                except (DataError, IntegrityError) as e:
                    self.logger.error('{} deleting ID={}: {}'.format(type(e).__name__, id, e))

        self.HANDLED_DURATIONS[me] += (datetime.now(utc) - start_utc).total_seconds()
        self.log_target(me)
        return(0, '')

    def Write_PackagedSoftware(self, content, contype):
        ####################################
        ### Resource
        ####################################
        me = '{} to Resource'.format(sys._getframe().f_code.co_name)
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
            if item['SupportOrganizationGlobalID']=='helpdesk.xsede.org':
                provider='urn:glue2:GlobalResourceProvider:HPC_Provider:xsede.org'
            else:
                provider='urn:glue2:GlobalResourceProvider:Support:{}'.format(item['SupportOrganizationGlobalID'])
            
            new_item = item.copy()
            new_item['record_status'] = 1
            try:
                model, created = Resource.objects.update_or_create(
                                    ID=ID,
                                    defaults = {
                                        'Name': item['Title'],
                                        'CreationTime': start_utc,
                                        'Validity': None,
                                        'EntityJSON': new_item,
                                        'Affiliation': my_affiliation,
                                        'ProviderID': provider,
                                        'Type': 'PackagedSoftware',
                                        'Description': item['Description'],
                                        'QualityLevel': item['DeclaredStatus'],
                                        'LocalID': local_id,
                                        'Keywords': item['Keywords']
                                    })
                model.save()
                self.logger.debug('{} ID={}'.format(contype, ID))
                self.new[ID]=model
                self.STATS.update({me + '.Update'})
            except (DataError, IntegrityError) as e:
                msg = '{} saving ID={}: {}'.format(type(e).__name__, ID, e)
                self.logger.error(msg)
                return(False, msg)

        for id in self.cur:
            if id not in self.new:
                try:
                    Resource.objects.filter(ID=id).delete()
                    self.STATS.update({me + '.Delete'})
                    self.logger.info('Deleted ID={}'.format(id))
                except (DataError, IntegrityError) as e:
                    self.logger.error('{} deleting ID={}: {}'.format(type(e).__name__, id, e))

        self.HANDLED_DURATIONS[me] += (datetime.now(utc) - start_utc).total_seconds()
        self.log_target(me)
        return(0, '')

    def tag_from_application(self, obj):
        # Tag which application this entry came from so that we can insulate those that came
        #   from IPF publishing and from the XCSR so that they do not overwrite each other
        if not isinstance(obj, dict) or not self.application:
            return
        if 'Extension' not in obj:
            obj['Extension'] = {'From_Application': self.application}
        else:
            obj['Extension']['From_Application'] = self.application

########## CUSTOMIZATIONS END ##########

if __name__ == '__main__':
    eprint('Exiting: OBSOLETE')
    sys.exit(1)
    router = Router()
    with PidFile(router.pidfile_path):
        try:
            router.Setup()
            rc = router.Run()
        except Exception as e:
            msg = '{} Exception: {}'.format(type(e).__name__, e)
            router.logger.error(msg)
            traceback.print_exc(file=sys.stdout)
            rc = 1
    router.exit(rc)
