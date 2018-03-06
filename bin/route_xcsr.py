#!/usr/bin/env python
#
# Synchronize information between the XCSR and the Warehouse:
# 1) XCSR Support Contacts to glue2.Contact
#
# TODO:
#  ...
import os
import pwd
import re
import sys
import argparse
import logging
import logging.handlers
import signal
import datetime
from datetime import datetime, tzinfo, timedelta
from time import sleep
import httplib
import json
import ssl
import shutil

import django
django.setup()
from django.db import DataError, IntegrityError
from django.utils.dateparse import parse_datetime
from glue2_db.models import *
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

class HandleXCSR():
    def __init__(self):
        self.args = None
        self.config = {}
        self.src = {}
        self.dest = {}
        for var in ['uri', 'scheme', 'path']: # Where <full> contains <type>:<obj>
            self.src[var] = None
            self.dest[var] = None
        self.peak_sleep = 10 * 60        # 10 minutes in seconds during peak business hours
        self.off_sleep = 60 * 60         # 60 minutes in seconds during off hours
        self.max_stale = 24 * 60 * 60    # 24 hours in seconds force refresh
        # These attributes have their own database column
        # Some fields exist in both parent and sub-resources, while others only in one
        # Those in one will be left empty in the other, or inherit from the parent
        self.have_column = ['resource_id', 'info_resourceid',
                            'resource_descriptive_name', 'resource_description',
                            'project_affiliation', 'provider_level',
                            'resource_status', 'current_statuses', 'updated_at']

        default_file = 'file:./xcsr.json'

        parser = argparse.ArgumentParser(epilog='File SRC|DEST syntax: file:<file path and name')
        parser.add_argument('daemon_action', nargs='?', choices=('start', 'stop', 'restart'), \
                            help='{start, stop, restart} daemon')
        parser.add_argument('-s', '--source', action='store', dest='src', \
                            help='Messages source {file, http[s]} (default=file)')
        parser.add_argument('-d', '--destination', action='store', dest='dest', \
                            help='Message destination {file, analyze, or warehouse} (default=analyze)')
        parser.add_argument('-l', '--log', action='store', \
                            help='Logging level (default=warning)')
        parser.add_argument('-c', '--config', action='store', default='./route_xcsr.conf', \
                            help='Configuration file default=./route_xcsr.conf')
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
                file.close()
        except IOError, e:
            raise
        try:
            self.config = json.loads(conf)
        except ValueError, e:
            print 'Error "{}" parsing config={}'.format(e, config_path)
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

        # Verify arguments and parse compound arguments
        if not getattr(self.args, 'src', None): # Tests for None and empty ''
            if 'CONTACT_INFO_URL' in self.config:
                self.args.src = self.config['CONTACT_INFO_URL']
        if not getattr(self.args, 'src', None): # Tests for None and empty ''
            self.args.src = default_file
        idx = self.args.src.find(':')
        if idx > 0:
            (self.src['scheme'], self.src['path']) = (self.args.src[0:idx], self.args.src[idx+1:])
        else:
            (self.src['scheme'], self.src['path']) = (self.args.src, None)
        if self.src['scheme'] not in ['file', 'http', 'https']:
            self.logger.error('Source not {file, http, https}')
            sys.exit(1)
        if self.src['scheme'] in ['http', 'https']:
            if self.src['path'][0:2] != '//':
                self.logger.error('Source URL not followed by "//"')
                sys.exit(1)
            self.src['path'] = self.src['path'][2:]
        self.src['uri'] = self.args.src
        self.src['contype'] = 'usersupport'        # The only contact type we handle currently

        if not getattr(self.args, 'dest', None): # Tests for None and empty ''
            if 'DESTINATION' in self.config:
                self.args.dest = self.config['DESTINATION']
        if not getattr(self.args, 'dest', None): # Tests for None and empty ''
            self.args.dest = 'analyze'
        idx = self.args.dest.find(':')
        if idx > 0:
            (self.dest['scheme'], self.dest['path']) = (self.args.dest[0:idx], self.args.dest[idx+1:])
        else:
            self.dest['scheme'] = self.args.dest
        if self.dest['scheme'] not in ['file', 'analyze', 'warehouse']:
            self.logger.error('Destination not {file, analyze, warehouse}')
            sys.exit(1)
        self.dest['uri'] = self.args.dest

        if self.src['scheme'] in ['file'] and self.dest['scheme'] in ['file']:
            self.logger.error('Source and Destination can not both be a {file}')
            sys.exit(1)

        if self.args.daemon_action:
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
                self.pidfile_path =  '/var/run/{}/{}.pid'.format(name ,name)

    def Retrieve_XCSR(self, contype, url):
        idx = url.find(':')
        if idx <= 0:
            self.logger.error('Retrieve URL is not valid')
            sys.exit(1)
            
        (type, obj) = (url[0:idx], url[idx+1:])
        if type not in ['http', 'https']:
            self.logger.error('Retrieve URL is not valid')
            sys.exit(1)

        if obj[0:2] != '//':
            self.logger.error('Retrieve URL is not valid')
            sys.exit(1)
            
        obj = obj[2:]
        idx = obj.find('/')
        if idx <= 0:
            self.logger.error('Retrieve URL is not valid')
            sys.exit(1)

        (host, path) = (obj[0:idx], obj[idx:])
        idx = host.find(':')
        if idx > 0:
            port = host[idx+1:]
        elif type == 'https':
            port = '443'
        else:
            port = '80'
      
        headers = {}
#        headers = {'Content-type': 'application/json',
#                    'XA-CLIENT': 'XSEDE',
#                    'XA-KEY-FORMAT': 'underscore'}
        ctx = ssl.create_default_context(ssl.Purpose.CLIENT_AUTH)
        conn = httplib.HTTPSConnection(host=host, port=port, context=ctx)
        if path[0] != '/':
            path = '/' + path
        conn.request('GET', path, None , headers)
        self.logger.debug('HTTP GET  {}'.format(url))
        response = conn.getresponse()
        result = response.read().decode("utf-8-sig")
        self.logger.debug('HTTP RESP {} {} (returned {}/bytes)'.format(response.status, response.reason, len(result)))
        try:
            xcsr_obj = json.loads(result)
        except ValueError, e:
            self.logger.error('Response not in expected JSON format ({})'.format(e))
            return(None)
        else:
            return({contype: xcsr_obj})

    def Analyze_XCSR(self, contype, xcsr_obj):
        if contype not in xcsr_obj:
            self.logger.error('XCSR JSON response is missing the base \'{}\' element'.format(contype))
            self.stats['Skip'] += 1
            sys.exit(1)
        maxlen = {}
        for p_res in xcsr_obj[contype]:  # Parent resources
            if any(x not in p_res for x in ('project_affiliation', 'resource_id', 'info_resourceid')) \
                    or p_res['project_affiliation'] != 'XSEDE' \
                    or str(p_res['info_resourceid']).lower() == 'none' \
                    or p_res['info_resourceid'] == '':
                self.stats['Skip'] += 1
                continue
            self.stats['Update'] += 1
            self.logger.info('ID={}, ResourceID={}, Level="{}", Description="{}"'.format(p_res['resource_id'], p_res['info_resourceid'], p_res['provider_level'], p_res['resource_descriptive_name']))
            
            self.sub = {}   # Sub-resource attributes go here
            for subtype in ['compute_resources', 'storage_resources', 'grid_resources', 'other_resources']:
                if subtype in p_res:
                    self.sub[subtype]=p_res[subtype]
            
            for x in p_res:
                if isinstance(p_res[x], dict):
                    msg='dict({})'.format(len(p_res[x]))
                elif isinstance(p_res[x], list):
                    msg='list({})'.format(len(p_res[x]))
                else:
                    msg=u'"{}"'.format(p_res[x])
                if x in self.have_column:
                    try:
                        if x not in maxlen or (x in maxlen and maxlen[x] <= len(p_res[x])):
                            maxlen[x] = len(p_res[x])
                    except:
                        pass
                self.logger.debug(u'  {}={}'.format(x, msg))
            
        for subtype in self.sub:
            for s_res in self.sub[subtype]: # Sub resources
                for x in s_res:
                    if x in self.have_column:
                        try:
                            if x not in maxlen or (x in maxlen and maxlen[x] <= len(s_res[x])):
                                maxlen[x] = len(s_res[x])
                        except:
                            pass

        for x in maxlen:
            self.logger.debug('Max({})={}'.format(x, maxlen[x]))

    def Write_Cache(self, file, xcsr_obj):
        data = json.dumps(xcsr_obj)
        with open(file, 'w') as my_file:
            my_file.write(data)
            my_file.close()
        self.logger.info('Serialized and wrote {} bytes to file={}'.format(len(data), file))
        return(len(data))

    def Read_Cache(self, contype, file):
        with open(file, 'r') as my_file:
            data = my_file.read()
            my_file.close()
        try:
            xcsr_obj = json.loads(data)
            self.logger.info('Read and parsed {} bytes from file={}'.format(len(data), file))
            return({contype: xcsr_obj})
        except ValueError, e:
            self.logger.error('Error "{}" parsing file={}'.format(e, file))
            sys.exit(1)

    def Warehouse_XCSR(self, contype, xcsr_obj):
        if contype not in xcsr_obj:
            self.stats['Skip'] += 1
            msg = 'XCSR JSON response is missing a \'{}\' element'.format(contype)
            self.logger.error(msg)
            return(False, msg)

        self.cur = {}   # Resources currently in database
        self.new = {}   # New resources in document
        for item in Contact.objects.filter(Type=contype):
            self.cur[item.ID] = item

        now_utc = datetime.now(utc)
        field_to_method_map = {'ContactURL': 'web',
                    'ContactEmail': 'e-mail',
                    'ContactPhone': 'phone'}

        for p_res in xcsr_obj[contype]:
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
                                    CreationTime=now_utc,
                                    Validity=None,
                                    EntityJSON=p_res,
                                    Detail=Detail,
                                    Type=method,
                                    )
                    model.save()
                    self.logger.debug('{} ID={}'.format(contype, ID))
                    self.new[ID]=model
                    self.stats['Update'] += 1
                except (DataError, IntegrityError) as e:
                    msg = '{} saving ID={}: {}'.format(type(e).__name__, ID, e.message)
                    self.logger.error(msg)
                    return(False, msg)

        for id in self.cur:
            if id not in self.new:
                try:
                    Contact.objects.filter(ID=id).delete()
                    self.stats['Delete'] += 1
                    self.logger.info('Deleted ID={}'.format(id))
                except (DataError, IntegrityError) as e:
                    self.logger.error('{} deleting ID={}: {}'.format(type(e).__name__, id, e.message))
        return(True, '')
            
    def latest_status(self, current_statuses):
        for ordered_status in ['decommissioned', 'retired', 'post_production', 'production', 'pre_production', 'friendly', 'coming_soon']:
            if ordered_status in current_statuses:
                return(ordered_status)
        if len(current_statuses) > 0:
           return(current_statuses[0])
        else:
           return('')

    def latest_status_date(self, resource_status_dates, current_status, which_date):
        # which should be 'begin' or 'end'
        fixed_current_status = current_status.replace('-', '_')
        key = '{}_{}_date'.format(fixed_current_status, which_date)
        if key not in resource_status_dates or resource_status_dates[key] is None:
            return(None)
        try:
            return(datetime.strptime(resource_status_dates[key], "%Y-%m-%d"))
        except:
            return(None)

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
                    print 'SaveDaemonLog as {}'.format(newpath)
        except Exception as e:
            print 'Exception in SaveDaemonLog({})'.format(path)
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
                current_sleep = self.off_sleep
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
        signal.signal(signal.SIGINT, self.exit_signal)
        signal.signal(signal.SIGTERM, self.exit_signal)
        self.logger.info('Starting program={} pid={}, uid={}({})'.format(os.path.basename(__file__), os.getpid(), os.geteuid(), pwd.getpwuid(os.geteuid()).pw_name))

        while True:
            self.start = datetime.now(utc)
            self.stats = {
                'Update': 0,
                'Delete': 0,
                'Skip': 0,
            }
            
            if self.src['scheme'] == 'file':
                XCSR = self.Read_Cache(self.src['contype'], self.src['path'])
            else:
                XCSR = self.Retrieve_XCSR(self.src['contype'], self.src['uri'])

            if self.dest['scheme'] == 'file':
                bytes = self.Write_Cache(self.dest['path'], XCSR)
            elif self.dest['scheme'] == 'analyze':
                self.Analyze_XCSR(self.src['contype'], XCSR)
            elif self.dest['scheme'] == 'warehouse':
                pa_application=os.path.basename(__file__)
                pa_function='Warehouse_XCSR'
#                pa_id = self.src['uri']
                pa_id = 'xcsr'
                pa_topic = self.src['contype']
                pa_about = 'xsede.org'
                pa = ProcessingActivity(pa_application, pa_function, pa_id , pa_topic, pa_about)
                (rc, warehouse_msg) = self.Warehouse_XCSR(self.src['contype'], XCSR)
            
            self.end = datetime.now(utc)
            summary_msg = 'Processed in {:.3f}/seconds: {}/updates, {}/deletes, {}/skipped'.format((self.end - self.start).total_seconds(), self.stats['Update'], self.stats['Delete'], self.stats['Skip'])
            self.logger.info(summary_msg)
            if self.dest['scheme'] == 'warehouse':
                if rc:  # No errors
                    pa.FinishActivity(rc, summary_msg)
                else:   # Something failed, use returned message
                    pa.FinishActivity(rc, warehouse_msg)
            if not self.args.daemon_action:
                break
            self.smart_sleep(self.start)

if __name__ == '__main__':
    router = HandleXCSR()
    if router.args.daemon_action is None:  # Interactive execution
        myrouter = router.run()
        sys.exit(0)
    
    if router.args.daemon_action == 'start':
        if router.src['scheme'] not in ['http', 'https'] or router.dest['scheme'] not in ['warehouse']:
            router.logger.error('Can only daemonize when source=[http|https] and destination=warehouse')
            sys.exit(1)

    # Daemon execution
    router.logger.info('Daemon startup')
    daemon_runner = runner.DaemonRunner(router)
    daemon_runner.daemon_context.files_preserve=[router.handler.stream]
    daemon_runner.daemon_context.working_directory=router.config['RUN_DIR']
    daemon_runner.do_action()
