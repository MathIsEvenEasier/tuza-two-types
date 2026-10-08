#!/usr/bin/env python3
"""Prepare/run/recover one ephemeral Azure GitHub Actions build session."""
import argparse
import base64
import contextlib
import datetime as dt
import fcntl
import gzip
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
import time
import urllib.parse
import urllib.request
import urllib.error
import uuid

from common import (AuditError, EXACT_JOBS, GRAVER_JOBS, IMAGE, MAX_ARCHIVE, PINS, REGION,
                    SCAN_JOBS, SOURCES, SUBSCRIPTION, VM_SIZE, blob_request, names, parse_time,
                    read_json, require, safe_extract, sha, stamp, tags, utcnow, validate_state,
                    write_json)
from templates import ARM, compute_template, rg_id, workflow
from verify_result import verify_result

HERE = Path(__file__).resolve().parent
CONTRIBUTOR = 'b24988ac-6180-42a0-ab88-20f7382dd24c'
CODE_FILES = ['audit.py','common.py','templates.py','remote_job.py','verify_result.py','worker.py','run_worker.sh']


class Cloud:
    def __init__(self, directory, state):
        self.directory, self.state = directory, state

    def az(self, *args, env=None):
        command = ['az', *args, '--subscription', SUBSCRIPTION, '--only-show-errors', '--output', 'json']
        try:
            result = subprocess.run(command, text=True, capture_output=True, timeout=180, env=env)
        except subprocess.TimeoutExpired:
            raise AuditError('Azure request timed out; state may have changed. Use status/collect.') from None
        if result.returncode:
            codes = re.findall(r'\(([A-Za-z][A-Za-z0-9_.]+)\)', result.stderr)
            # stderr/argv may contain request bodies and SAS tokens. Report codes only.
            raise AuditError('Azure ' + args[0] + ' failed: ' + ', '.join(codes[:3] or ['see Azure portal']))
        return json.loads(result.stdout) if result.stdout.strip() else None

    def rest(self, method, path, body=None):
        subscription_path = '/subscriptions/' + SUBSCRIPTION
        require(path.startswith(subscription_path + '/') or path.split('?')[0] == subscription_path,
                'Unexpected ARM scope')
        args = ['rest', '--method', method, '--url', ARM + path]
        if body is None:
            return self.az(*args)
        with tempfile.TemporaryDirectory(dir=self.directory) as tmp:
            path = Path(tmp) / 'request.json'
            write_json(path, body)
            return self.az(*args, '--body', '@' + str(path), '--headers', 'Content-Type=application/json')

    def pages(self, path):
        values = []
        for _ in range(200):
            result = self.rest('get', path)
            values.extend(result.get('value', []))
            link = result.get('nextLink')
            if not link:
                return values
            require(link.startswith(ARM + '/subscriptions/' + SUBSCRIPTION + '/'), 'Unexpected pagination URL')
            path = link[len(ARM):]
        raise AuditError('ARM pagination limit exceeded')

    def exists(self, kind):
        value = self.az('group', 'exists', '--name', self.state['names'][kind + '_rg'])
        require(type(value) is bool, 'Invalid resource-group existence response')
        return value

    def owned(self, kind):
        if not self.exists(kind):
            return False
        group = self.az('group', 'show', '--name', self.state['names'][kind + '_rg'])
        require(group['id'].lower() == rg_id(self.state, kind).lower(), 'Wrong group ID')
        require(all((group.get('tags') or {}).get(k) == v
                    for k, v in tags(self.state['job_id']).items()),
                'Refusing unowned or retagged resource group')
        return True

    def inventory(self):
        groups = {kind: self.exists(kind) for kind in ('compute', 'control')}
        resources = self.az('resource', 'list')
        expected = {rg_id(self.state, k).lower() + '/' for k in groups}
        remnants = [r['id'] for r in resources if any(r['id'].lower().startswith(p) for p in expected)
                    or (r.get('tags') or {}).get('job-id') == self.state['job_id']]
        return {'checked_at': stamp(), 'group_exists': groups, 'resource_ids': remnants,
                'all_deleted': not any(groups.values()) and not remnants}


def save(directory, state, phase=None):
    if phase:
        state['phase'] = phase
    state['updated_at'] = stamp()
    write_json(directory / 'state.json', state)


def package_files(job_kind):
    require(job_kind == 'tuza_two_types_lean', 'Unknown job kind')
    files = {name: HERE / name for name in ('remote_job.py','common.py','worker.py','run_worker.sh')}
    return files


def prepare(base, job_kind='tuza_two_types_lean'):
    job_id = uuid.uuid4().hex[:16]
    directory = base.resolve() / job_id
    directory.mkdir(parents=True, mode=0o700)
    require(re.fullmatch(r'[0-9a-f-]{36}', SUBSCRIPTION), 'Set AZURE_SUBSCRIPTION_ID')
    files = package_files(job_kind)
    # Registration tokens are short-lived, repository-scoped and never printed.
    registrations=[]
    for repo in ('tuza-two-types',):
        response=subprocess.run([os.environ.get('GH_BIN','gh'),'api','--method','POST',
            'repos/MathIsEvenEasier/'+repo+'/actions/runners/registration-token'],
            capture_output=True,text=True,check=True)
        token=json.loads(response.stdout)
        registrations.append({'repository':'MathIsEvenEasier/'+repo,
            'token':token['token'],'label':'azure-proof-'+job_id,'name':repo+'-'+job_id})
    private=directory/'registration.json'
    write_json(private,registrations)
    files['registration.json']=private
    state = {'schema': 1, 'job_id': job_id, 'subscription': SUBSCRIPTION, 'region': REGION,
        'vm_size': VM_SIZE, 'image': IMAGE, 'minutes': 125, 'pins': PINS, 'names': names(job_id),
        'job_kind': job_kind, 'files': {k: sha(v) for k, v in files.items()},
        'controller_sha256': {name: sha(HERE / name) for name in CODE_FILES},
        'phase': 'prepared', 'created_at': stamp(), 'compute_attempted': False}
    manifest = {'schema': 1, 'job_id': job_id, 'job_kind': job_kind,
                'files': state['files'], 'pins': PINS}
    write_json(directory / 'input-manifest.json', manifest)
    with tarfile.open(directory / 'input.tgz', 'w:gz') as tf:
        for name, path in sorted(files.items()):
            tf.add(path, arcname=name, recursive=False)
        tf.add(directory / 'input-manifest.json', arcname='input-manifest.json', recursive=False)
    require((directory / 'input.tgz').stat().st_size <= 64*1024**2, 'Input package exceeds 64 MiB')
    state['input_sha256'] = sha(directory / 'input.tgz')
    write_json(directory / 'compute-template.json', compute_template(state))
    write_json(directory / 'plan.json', {
        'job_id': job_id, 'job_kind': job_kind, 'subscription': SUBSCRIPTION,
        'region': REGION, 'vm_size': VM_SIZE,
        'image': IMAGE, 'groups': state['names'], 'minutes_from_start_of_cloud_setup': 125,
        'worker_memory_gib': 24, 'worker_runtime_minutes': 115, 'os_disk_gib': 64, 'inbound_network': 'deny all',
        'guard': 'one-shot Logic App with Contributor on this job compute RG only',
        'compute_rate_usd_per_hour_observed_2026_09_11': 0.238,
        'compute_125_minutes_usd': 0.496,
        'additional_costs': ['OS disk', 'public IPv4', 'Storage', 'Logic App actions', 'transfer'],
        'deadline_is_deletion_request_not_billing_cap': True,
        'recovery_storage_retained_until_download_or_explicit_discard': True,
        'source_files': state['files'], 'cloud_resources_created_by_prepare': []})
    save(directory, state)
    print('Prepared locally: ' + str(directory), flush=True)
    return directory


def quota_check(usages):
    for name in ('cores', 'StandardEasv7Family'):
        rows = [r for r in usages if r['name']['value'].lower() == name.lower()]
        require(len(rows) == 1, 'Quota missing: ' + name)
        require(int(rows[0]['limit']) - int(rows[0]['currentValue']) >= 4, 'Insufficient quota: ' + name)


def retail_price():
    query = urllib.parse.urlencode({'api-version': '2023-01-01-preview', 'currencyCode': 'USD',
        '$filter': f"serviceName eq 'Virtual Machines' and priceType eq 'Consumption' and armSkuName eq '{VM_SIZE}' and armRegionName eq '{REGION}'"})
    url = 'https://prices.azure.com/api/retail/prices?' + query
    try:
        with urllib.request.urlopen(url, timeout=30) as response:
            document = json.load(response)
    except urllib.error.HTTPError:
        raise AuditError('Could not obtain a current Azure price; no compute started') from None
    require(not document.get('NextPageLink'), 'Unexpected price pagination')
    items = [r for r in document['Items'] if r['armSkuName'] == VM_SIZE and r['armRegionName'] == REGION
             and r['type'] == 'Consumption' and r['currencyCode'] == 'USD'
             and not any(word in (r['productName'] + ' ' + r['skuName']).lower()
                         for word in ('windows', 'spot', 'low priority', 'cloudservices'))]
    require(len(items) == 1 and items[0]['unitOfMeasure'] == '1 Hour', 'Ambiguous VM price')
    rate = float(items[0]['retailPrice'])
    require(0 < rate <= 0.25, 'VM retail price exceeds 0.25 USD/h; review before running')
    return {'source': url, 'hourly_usd': rate, 'compute_125_minutes_usd': rate * 125/60,
            'excludes': ['disk', 'IPv4', 'Storage', 'Logic Apps', 'transfer', 'taxes']}


def preflight(cloud, register=False):
    prefix = '/subscriptions/' + SUBSCRIPTION
    account = cloud.rest('get', prefix + '?api-version=2022-12-01')
    require(account['state'] == 'Enabled', 'Subscription is not enabled')
    require(account['subscriptionPolicies']['quotaId'].startswith(('FreeTrial','PayAsYouGo')), 'Unexpected subscription offer')
    require(account['subscriptionPolicies']['spendingLimit'] in ('On','Off'), 'Unknown billing policy')
    for provider in ('Microsoft.Compute', 'Microsoft.Network', 'Microsoft.Storage', 'Microsoft.Logic'):
        provider_state = cloud.az('provider', 'show', '--namespace', provider)['registrationState']
        if provider_state != 'Registered' and register:
            print('Registering provider: ' + provider, flush=True)
            cloud.az('provider', 'register', '--namespace', provider)
            end = time.monotonic() + 600
            while provider_state != 'Registered' and time.monotonic() < end:
                time.sleep(10)
                provider_state = cloud.az('provider', 'show', '--namespace', provider)['registrationState']
        require(provider_state == 'Registered', 'Provider not registered: ' + provider + '; run registers it')
    usages = cloud.az('vm', 'list-usage', '--location', REGION)
    quota_check(usages)
    query = urllib.parse.urlencode({'api-version': '2019-04-01', '$filter': f"location eq '{REGION}'"})
    skus = cloud.pages(prefix + '/providers/Microsoft.Compute/skus?' + query)
    rows = [r for r in skus if r.get('name') == VM_SIZE and r.get('resourceType') == 'virtualMachines']
    require(len(rows) == 1 and not rows[0].get('restrictions'), 'VM SKU restricted or not found')
    caps = {c['name']: c['value'] for c in rows[0]['capabilities']}
    require(int(caps['vCPUs']) == 4 and float(caps['MemoryGB']) >= 32, 'Unexpected SKU resources')
    require(caps.get('CpuArchitectureType') == 'x64' and 'V2' in caps.get('HyperVGenerations', ''), 'Wrong VM architecture')
    image = cloud.az('vm', 'image', 'show', '--location', REGION, '--urn', IMAGE)
    features = {f['name']: f['value'] for f in image.get('features', [])}
    require(image.get('architecture') == 'x64' and image.get('hyperVGeneration') == 'V2'
            and 'NVMe' in features.get('DiskControllerTypes', ''), 'Image does not support this VM')
    summary = {'checked_at': stamp(), 'spending_limit': account['subscriptionPolicies']['spendingLimit'], 'quota_checked': True, 'price': retail_price(),
               'sku_checked': True, 'image_checked': True, 'allocation_tested': False}
    write_json(cloud.directory / 'run-preflight.json', summary)
    return summary


def workflow_path(state):
    return rg_id(state, 'control') + '/providers/Microsoft.Logic/workflows/' + state['names']['workflow']


def guard_is_armed(actions):
    statuses = {a['name']: a['properties']['status'] for a in actions}
    return statuses.get('Verify_scope') == 'Succeeded' and statuses.get('Wait_until_deadline') in ('Running', 'Waiting')


def deadline_allows_deploy(state):
    require(state.get('guard_run_id'), 'No verified cloud guard run')
    require(parse_time(state['deadline']) - utcnow() > dt.timedelta(minutes=15), 'Too little time before deadline')


def arm_guard(cloud, state):
    path = workflow_path(state)
    document = workflow(state)
    write_json(cloud.directory / 'guard-template.json', document)
    response = cloud.rest('put', path + '?api-version=2019-05-01', document)
    principal = response['identity']['principalId']
    scope = rg_id(state, 'compute')
    assignment = str(uuid.uuid5(uuid.NAMESPACE_URL, scope + principal))
    state['guard_principal_id'] = principal
    save(cloud.directory, state, 'assigning_guard_role')
    cloud.rest('put', scope + '/providers/Microsoft.Authorization/roleAssignments/' + assignment + '?api-version=2022-04-01', {
        'properties': {'roleDefinitionId': '/subscriptions/' + SUBSCRIPTION + '/providers/Microsoft.Authorization/roleDefinitions/' + CONTRIBUTOR,
                       'principalId': principal, 'principalType': 'ServicePrincipal'}})
    cloud.rest('post', path + '/triggers/manual/run?api-version=2016-06-01')
    end = time.monotonic() + 600
    last_trigger = time.monotonic()
    while time.monotonic() < end:
        runs = cloud.pages(path + '/runs?api-version=2016-06-01')
        for run in runs:
            actions = cloud.pages(path + '/runs/' + run['name'] + '/actions?api-version=2016-06-01')
            if guard_is_armed(actions):
                state['guard_run_id'] = run['name']
                state['guard_verified_at'] = stamp()
                save(cloud.directory, state, 'guard_armed')
                return
        # HTTP 403 during RBAC propagation is not automatically retried by Logic Apps.
        # A failed probe never arms the timer, and no VM exists yet. Start a fresh run.
        if runs and all(r['properties']['status'] in ('Failed', 'Cancelled', 'TimedOut') for r in runs) \
                and time.monotonic() - last_trigger >= 30:
            cloud.rest('post', path + '/triggers/manual/run?api-version=2016-06-01')
            last_trigger = time.monotonic()
        time.sleep(10)
    raise AuditError('Cloud deletion guard not confirmed; VM will not be deployed')


def storage_path(state):
    return rg_id(state, 'control') + '/providers/Microsoft.Storage/storageAccounts/' + state['names']['storage']


def storage_env(cloud):
    require(cloud.owned('control'), 'Control group is gone')
    response = cloud.rest('post', storage_path(cloud.state) + '/listKeys?api-version=2023-05-01')
    return dict(os.environ, AZURE_STORAGE_KEY=response['keys'][0]['value'],
                AZURE_STORAGE_ACCOUNT=cloud.state['names']['storage'])


def sas_url(cloud, blob, permissions, env):
    expiry = stamp(max(utcnow(), parse_time(cloud.state['deadline'])) + dt.timedelta(hours=2))
    token = cloud.az('storage', 'blob', 'generate-sas', '--container-name', 'audit', '--name', blob,
                     '--permissions', permissions, '--expiry', expiry, '--https-only', env=env)
    require(isinstance(token, str) and 'sig=' in token, 'Missing SAS token')
    return 'https://' + cloud.state['names']['storage'] + '.blob.core.windows.net/audit/' + blob + '?' + token.lstrip('?')


def create_storage(cloud):
    state = cloud.state
    cloud.rest('put', storage_path(state) + '?api-version=2023-05-01', {
        'location': REGION, 'kind': 'StorageV2', 'sku': {'name': 'Standard_LRS'}, 'tags': tags(state['job_id']),
        'properties': {'allowBlobPublicAccess': False, 'allowSharedKeyAccess': True,
                       'supportsHttpsTrafficOnly': True, 'minimumTlsVersion': 'TLS1_2'}})
    end = time.monotonic() + 300
    while time.monotonic() < end:
        response = cloud.rest('get', storage_path(state) + '?api-version=2023-05-01')
        phase = response['properties']['provisioningState']
        if phase == 'Succeeded':
            break
        require(phase != 'Failed', 'Storage provisioning failed')
        time.sleep(10)
    else:
        raise AuditError('Storage provisioning timed out')
    env = storage_env(cloud)
    cloud.az('storage', 'container', 'create', '--name', 'audit', '--public-access', 'off', env=env)
    cloud.az('storage', 'blob', 'upload', '--container-name', 'audit', '--name', 'input.tgz',
             '--file', str(cloud.directory / 'input.tgz'), '--overwrite', 'false', env=env)
    return env


def deployment_parameters(cloud, state, env):
    config = {'job_id': state['job_id'], 'subscription': SUBSCRIPTION,
              'compute_rg': state['names']['compute_rg'], 'deadline': state['deadline'],
              'input_sha256': state['input_sha256'],
              'job_kind': state.get('job_kind', 'tuza_two_types_lean')}
    for key, blob, perm in [('input_url', 'input.tgz', 'r'), ('results_url', 'results.tgz', 'cw'),
                           ('status_url', 'status.json', 'cw'), ('heartbeat_url', 'heartbeat.json', 'cw'),
                           ('request_url', 'request.json', 'r'), ('response_url', 'response.json', 'cw')]:
        config[key] = sas_url(cloud, blob, perm, env)
    files = {'config.json': json.dumps(config).encode(),
             'remote_job.py': (HERE / 'remote_job.py').read_bytes(), 'common.py': (HERE / 'common.py').read_bytes()}
    cloud_config = {'write_files': [{'path': '/opt/mathiseasy-boot/' + name,
        'encoding': 'gzip+base64',
        'content': base64.b64encode(gzip.compress(content, compresslevel=9, mtime=0)).decode(),
        'permissions': '0600', 'owner': 'root:root'}
        for name, content in files.items()],
        'runcmd': [['python3', '-E', '-s', '/opt/mathiseasy-boot/remote_job.py', '/opt/mathiseasy-boot/config.json']]}
    data = ('#cloud-config\n' + json.dumps(cloud_config)).encode()
    require(len(data) <= 64 * 1024, 'Azure customData exceeds 64 KiB')
    private = cloud.directory / 'private'
    private.mkdir(mode=0o700, exist_ok=True)
    key = private / 'provisioning-key'
    subprocess.run(['ssh-keygen', '-q', '-t', 'rsa', '-b', '3072', '-N', '', '-f', str(key)], check=True)
    parameters = {'customData': {'value': base64.b64encode(data).decode()},
                  'sshPublicKey': {'value': key.with_suffix('.pub').read_text().strip()}}
    write_json(private / 'deployment-parameters.json', parameters)
    return parameters


def launch(cloud, state):
    require(state['phase'] == 'prepared', 'Job already started; use collect, not run')
    require(sha(cloud.directory / 'input.tgz') == state['input_sha256'], 'Prepared archive changed')
    for name, expected in state['controller_sha256'].items():
        require(sha(HERE / name) == expected, 'Controller changed after prepare; prepare a new job')
    preflight(cloud, register=True)
    require(not cloud.exists('compute') and not cloud.exists('control'), 'Resource group name collision')
    state['started_at'] = stamp()
    state['deadline'] = stamp(utcnow() + dt.timedelta(minutes=state['minutes']))
    save(cloud.directory, state, 'creating_groups')
    for kind in ('compute', 'control'):
        cloud.az('group', 'create', '--name', state['names'][kind + '_rg'], '--location', REGION,
                 '--tags', *[k + '=' + v for k, v in tags(state['job_id']).items()])
    arm_guard(cloud, state)
    save(cloud.directory, state, 'creating_storage')
    env = create_storage(cloud)
    parameters = deployment_parameters(cloud, state, env)
    # Re-read the running guard immediately before a billable VM deployment.
    actions = cloud.pages(workflow_path(state) + '/runs/' + state['guard_run_id'] + '/actions?api-version=2016-06-01')
    require(guard_is_armed(actions), 'Cloud guard no longer waiting')
    deadline_allows_deploy(state)
    state['compute_attempted'] = True
    save(cloud.directory, state, 'deploying_compute')
    cloud.rest('put', rg_id(state, 'compute') + '/providers/Microsoft.Resources/deployments/audit?api-version=2022-09-01', {
        'properties': {'mode': 'Incremental', 'template': compute_template(state), 'parameters': parameters}})
    save(cloud.directory, state, 'running')
    print('Cloud guard armed. Deadline: ' + state['deadline'] + '. Waiting for results.', flush=True)


def delete_group(cloud, kind):
    if not cloud.owned(kind):
        return
    print('Deleting job ' + kind + ' resource group…', flush=True)
    cloud.az('group', 'delete', '--name', cloud.state['names'][kind + '_rg'], '--yes', '--no-wait')
    end = time.monotonic() + 900
    while time.monotonic() < end:
        if not cloud.exists(kind):
            return
        time.sleep(15)
    raise AuditError('Deletion not confirmed: ' + kind + '. Keep guard; retry collect/cleanup.')


def has_receipt(directory, state):
    path = directory / 'download-receipt.json'
    if not path.exists():
        return False
    receipt = read_json(path)
    require(receipt['job_id'] == state['job_id'] and receipt['input_sha256'] == state['input_sha256'],
            'Invalid local download receipt')
    archive = directory / 'results.tgz'
    require(archive.exists() and sha(archive) == receipt['archive_sha256'], 'Local results missing/corrupted')
    return True


def cleanup(cloud, state, discard=False):
    # Never delete the guard/storage while compute deletion remains uncertain.
    delete_group(cloud, 'compute')
    require(not cloud.exists('compute'), 'Compute group still exists')
    before_control = cloud.inventory()
    compute_prefix = rg_id(state, 'compute').lower() + '/'
    require(not any(r.lower().startswith(compute_prefix) for r in before_control['resource_ids']),
            'Compute resources still listed; retain cloud guard')
    if not state.get('compute_attempted') or discard or has_receipt(cloud.directory, state):
        delete_group(cloud, 'control')
    report = cloud.inventory()
    write_json(cloud.directory / 'cleanup-report.json', report)
    save(cloud.directory, state, 'cleaned' if report['all_deleted'] else 'results_storage_retained')
    if report['all_deleted'] and (cloud.directory / 'private').exists():
        shutil.rmtree(cloud.directory / 'private')
    print(json.dumps(report, indent=2), flush=True)
    return report['all_deleted']


def download_result(cloud, state, env):
    status = json.loads(blob_request(sas_url(cloud, 'status.json', 'r', env), limit=1024**2))
    require(status.get('schema') == 1 and status['job_id'] == state['job_id']
            and status['input_sha256'] == state['input_sha256'], 'Invalid remote status')
    require(type(status['archive_bytes']) is int and 0 < status['archive_bytes'] <= MAX_ARCHIVE, 'Invalid result size')
    temporary = cloud.directory / 'results.tgz.partial'
    blob_request(sas_url(cloud, 'results.tgz', 'r', env), destination=temporary, limit=status['archive_bytes'])
    require(temporary.stat().st_size == status['archive_bytes'] and sha(temporary) == status['archive_sha256'],
            'Downloaded result hash or length mismatch')
    os.replace(temporary, cloud.directory / 'results.tgz')
    write_json(cloud.directory / 'download-receipt.json', dict(status, downloaded_at=stamp()))


def verify_download(directory, state):
    require(has_receipt(directory, state), 'No durable local result archive')
    status = read_json(directory / 'download-receipt.json')
    with tempfile.TemporaryDirectory(prefix='verify-', dir=directory) as tmp:
        extracted = Path(tmp) / 'contents'
        safe_extract(directory / 'results.tgz', extracted)
        result = verify_result(extracted, state, status)
    write_json(directory / 'verification-report.json', result)
    print(json.dumps(result, indent=2), flush=True)


def collect(cloud, state, wait_seconds):
    if not has_receipt(cloud.directory, state):
        require(cloud.owned('control'), 'No control group or local results')
        env = storage_env(cloud)
        end = time.monotonic() + wait_seconds
        last_message = 0.0
        while True:
            exists = cloud.az('storage', 'blob', 'exists', '--container-name', 'audit', '--name', 'status.json', env=env)
            if exists['exists'] is True:
                download_result(cloud, state, env)
                break
            if time.monotonic() >= end:
                raise AuditError('Results not ready; use collect again. Storage and cloud guard retained.')
            if time.monotonic() - last_message >= 60:
                print('Waiting for result commit; deadline ' + state['deadline'], flush=True)
                last_message = time.monotonic()
            if utcnow() > parse_time(state['deadline']) + dt.timedelta(minutes=2):
                raise AuditError('Deadline passed without complete results; recover diagnostics from Azure portal/storage.')
            time.sleep(15)
    # Both successful and failed audit output is worth preserving. Cleanup does not depend on proof success.
    verified = False
    try:
        verify_download(cloud.directory, state)
        verified = True
    finally:
        cleaned = cleanup(cloud, state)
    require(verified and cleaned, 'Audit or resource cleanup incomplete')


@contextlib.contextmanager
def locked(directory):
    with (directory / '.controller.lock').open('a') as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            raise AuditError('Another controller is using this job') from None
        yield


def main():
    os.umask(0o077)
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=['prepare','run','launch','collect','status','cleanup','verify'])
    parser.add_argument('directory', nargs='?', type=Path)
    args=parser.parse_args()
    if args.command=='prepare':
        prepare(HERE/'runs'); return
    require(args.directory is not None, 'Directory required')
    directory=args.directory.resolve()
    with locked(directory):
        state=read_json(directory/'state.json'); validate_state(state)
        cloud=Cloud(directory,state)
        if args.command=='run':
            launch(cloud,state); collect(cloud,state,2400)
        elif args.command=='launch': launch(cloud,state)
        elif args.command=='collect': collect(cloud,state,60)
        elif args.command=='status':
            print(json.dumps({'phase':state['phase'],'inventory':cloud.inventory()}))
        elif args.command=='cleanup': cleanup(cloud,state)
        elif args.command=='verify': verify_download(directory,state)

if __name__=='__main__':
    try: main()
    except AuditError as exc:
        print(str(exc),file=sys.stderr);sys.exit(1)
