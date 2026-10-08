from pathlib import Path
import shutil
from common import read_json, require, sha

def verify_result(extracted,state,status):
    target=Path(__file__).resolve().parent/'runs'/state['job_id']/'returned'
    target.mkdir(exist_ok=True)
    for p in extracted.iterdir(): shutil.copy2(p,target/p.name)
    for name,expected in state['files'].items():
        if name != 'registration.json': require(sha(extracted/name)==expected,'Returned source changed')
    remote=read_json(extracted/'remote-result.json')
    summary=read_json(extracted/'ci-summary.json') if (extracted/'ci-summary.json').exists() else []
    return {'job_id':state['job_id'],'worker_exit_code':remote['exit_code'],
            'runners':summary,'note':'Runner transport record only. Check each public GitHub Actions conclusion and downloaded proof report separately.'}
