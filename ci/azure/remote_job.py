#!/usr/bin/env python3
"""Azure-only bounded supervisor; cloud Logic App remains the deletion guard."""
import json
import os
from pathlib import Path
import platform
import subprocess
import sys
import tarfile
import time
import urllib.request

from common import (AuditError, MAX_ARCHIVE, MAX_EXPANDED, blob_request, parse_time,
                    read_json, require, safe_extract, sha, stamp, utcnow, write_json)

ROOT = Path('/opt/a060957-job')
SOURCE = ROOT / 'source'
PROFILES = {'tuza_two_types_lean': {'runner':'run_worker.sh','outputs':['ci-summary.json']}}


def check_azure(config):
    require(platform.system() == 'Linux' and platform.machine() == 'x86_64', 'Azure x64 guest required')
    request = urllib.request.Request(
        'http://169.254.169.254/metadata/instance/compute?api-version=2021-02-01', headers={'Metadata': 'true'})
    # IMDS must not pass through a proxy.
    with urllib.request.build_opener(urllib.request.ProxyHandler({})).open(request, timeout=5) as response:
        meta = json.load(response)
    require(meta['subscriptionId'].lower() == config['subscription'].lower(), 'Wrong Azure subscription')
    require(meta['resourceGroupName'].lower() == config['compute_rg'].lower(), 'Wrong Azure resource group')
    require(meta['name'] == 'audit-vm', 'Wrong VM identity')
    Path('/run/mathiseasy-azure-verified').write_text(config['job_id'])


def put(url, data):
    for attempt in range(3):
        try:
            blob_request(url, data=data, method='PUT', limit=1024**2)
            return
        except AuditError:
            if attempt == 2:
                raise
            time.sleep(5)


def main(config_path):
    config = read_json(config_path)
    job_kind = config.get('job_kind', 'tuza_two_types_lean')
    require(job_kind in PROFILES, 'Unknown job kind')
    profile = PROFILES[job_kind]
    check_azure(config)
    ROOT.mkdir(parents=True, exist_ok=True)
    result = {'schema': 1, 'job_id': config['job_id'], 'input_sha256': config['input_sha256'],
              'started_at': stamp(), 'exit_code': 125, 'phase': 'setup'}
    log_path = ROOT / 'worker.log'
    log_path.touch()
    try:
        package = ROOT / 'input.tgz'
        blob_request(config['input_url'], destination=package, limit=64*1024**2)
        require(sha(package) == config['input_sha256'], 'Input archive hash mismatch')
        safe_extract(package, SOURCE, max_bytes=96*1024**2)
        manifest = read_json(SOURCE / 'input-manifest.json')
        require(manifest['job_id'] == config['job_id'], 'Wrong manifest job')
        require(manifest.get('job_kind', 'tuza_two_types_lean') == job_kind, 'Wrong manifest job kind')
        for name, expected in manifest['files'].items():
            require(sha(SOURCE / name) == expected, 'Input member hash mismatch')
        # Bound this development session independently of the local controller.
        runtime_cap_minutes = 175
        seconds = min(runtime_cap_minutes * 60,
                      int((parse_time(config['deadline']) - utcnow()).total_seconds()) - 300)
        require(seconds >= 120, 'Insufficient time before external deletion deadline')
        result['phase'] = 'worker'
        # Bound the whole tool install/build/check process, including descendants.
        with log_path.open('ab') as log:
            process = subprocess.Popen(['systemd-run', '--unit=mathiseasy-worker', '--wait', '--pipe',
                '--property=MemoryMax=48G', '--property=MemorySwapMax=0', '--property=TasksMax=512',
                '--property=OOMPolicy=kill', '--property=KillMode=control-group',
                '--property=TimeoutStopSec=15s', f'--property=RuntimeMaxSec={seconds}s',
                '--property=LimitCORE=0', '/bin/bash', str(SOURCE / profile['runner'])],
                stdout=log, stderr=subprocess.STDOUT)
            while process.poll() is None:
                heartbeat = dict(result, checked_at=stamp(), log_bytes=log_path.stat().st_size)
                # Publish bounded, non-sensitive source-build progress, not proof success.
                for record_path in Path('/home/proofci').glob('tuza-two-types-*/_work/tuza-two-types/tuza-two-types/ci-output/rebuild-record.json'):
                    try:
                        rows = json.loads(record_path.read_text())
                        if isinstance(rows, list) and rows:
                            heartbeat['project_modules_checked'] = len(rows)
                            heartbeat['last_module'] = rows[-1]['module']
                    except (OSError, ValueError, KeyError):
                        pass  # The worker may be replacing its progress record.
                try:
                    put(config['heartbeat_url'], json.dumps(heartbeat).encode())
                except AuditError:
                    pass  # A failed heartbeat cannot disable the external guard.
                time.sleep(20)
            result['exit_code'] = process.returncode
    except Exception as exc:
        # Never include exception messages: HTTP errors can contain signed URLs.
        result['failure_type'] = type(exc).__name__
        if isinstance(exc, AuditError):
            result['failure_message'] = str(exc)  # These messages already redact URLs.
    result['finished_at'] = stamp()
    result['phase'] = 'finished'
    write_json(ROOT / 'remote-result.json', result)
    members = {'remote-result.json': ROOT / 'remote-result.json', 'worker.log': log_path}
    if SOURCE.exists():
        manifest_path = SOURCE / 'input-manifest.json'
        if manifest_path.exists():
            manifest = read_json(manifest_path)
            members.update({name: SOURCE / name for name in manifest['files'] if name != 'registration.json'})
            members['input-manifest.json'] = manifest_path
        members.update({name: SOURCE / name for name in profile['outputs']
                        if (SOURCE / name).is_file()})
    require(all(p.is_file() and not p.is_symlink() for p in members.values()), 'Invalid output member')
    require(sum(p.stat().st_size for p in members.values()) <= MAX_EXPANDED, 'Output exceeds limit')
    archive = ROOT / 'results.tgz'
    with tarfile.open(archive, 'w:gz', compresslevel=1) as tf:
        for name, path in sorted(members.items()):
            tf.add(path, arcname=name, recursive=False)
    require(archive.stat().st_size <= MAX_ARCHIVE, 'Compressed output exceeds limit')
    put(config['results_url'], archive.read_bytes())
    # Commit status only after the complete result archive is durably in Blob Storage.
    status = dict(result, archive_sha256=sha(archive), archive_bytes=archive.stat().st_size)
    put(config['status_url'], json.dumps(status).encode())
    # Guest poweroff is not deallocation/deletion. Controller or Logic App deletes the RG.
    subprocess.run(['shutdown', '-h', 'now'], check=False)


if __name__ == '__main__':
    os.umask(0o077)
    try:
        main(sys.argv[1])
    except Exception as exc:
        print('Supervisor failed: ' + type(exc).__name__, flush=True)
        sys.exit(1)
