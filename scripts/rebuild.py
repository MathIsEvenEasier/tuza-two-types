#!/usr/bin/env python3
"""Rebuild every project module from source on a bounded Azure worker."""
import concurrent.futures,hashlib,json,os,pathlib,re,subprocess,sys,time
from sources import prepare,digest
ROOT=pathlib.Path(__file__).resolve().parents[1]
ALLOWED={'propext','Classical.choice','Quot.sound'}
def main():
    if not pathlib.Path('/run/mathiseasy-azure-verified').is_file():raise SystemExit('Use a bounded Azure worker with an independent cloud deletion guard.')
    work=pathlib.Path(sys.argv[1]).resolve(); out=ROOT/'ci-output'; out.mkdir(exist_ok=True)
    source=work/'tuza-source'; manifest=prepare(source)
    target=work/'tuza-objects';target.mkdir(exist_ok=False)
    records=[];names={r['module'] for r in manifest['modules']}; dependencies={}
    for name in names:
        text=(source/(name+'.lean')).read_text()
        if re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by)\b',text):raise RuntimeError('Forbidden source token: '+name)
        imports=re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$',text,re.M)
        unknown={m for m in imports if m not in names and not m.startswith(('Mathlib.','Lean.','Std.'))}
        if unknown:raise RuntimeError('Unknown import in '+name+': '+str(unknown))
        dependencies[name]=set(imports)&names
    # Earlier caches contain both monolithic decisions and newer shared proofs.
    # Reserve memory by source shape, and retain bounded retry evidence if needed.
    limits={name:(6000 if name.startswith('FiniteChunk') and (source/(name+'.lean')).stat().st_size<1500 else 2800) for name in names}
    for name in names:
        if name in {'GraphReductions','CertificateKernel','NormalizedBounds','Result','IntervalResult'} or name.startswith('IntervalRoot'):limits[name]=10000
    attempts=[]
    def memory_for(name):return limits[name]
    def compile_module(name):
        start=time.monotonic(); logfile=out/(name+'.m'+str(memory_for(name))+'.log')
        memory=str(memory_for(name))
        command=['lake','env','lean','-j1','-M'+memory,'-DElab.async=false','-o',str(target/(name+'.olean')),str(source/(name+'.lean'))]
        with logfile.open('w') as f:
            p=subprocess.run(command,cwd=work,env=dict(os.environ,LEAN_PATH=str(target)),stdout=f,stderr=subprocess.STDOUT,timeout=600)
        log=logfile.read_text()
        rec={'module':name,'exit_code':p.returncode,'seconds':round(time.monotonic()-start,3),'source_sha256':digest(source/(name+'.lean')),'memory_limit_mib':memory_for(name)}
        if p.returncode:
            rec['failure_log']=logfile.name
            rec['memory_failure']='excessive memory consumption' in log
            return rec
        (out/(name+'.log')).write_text(log)
        if 'sorryAx' in log or 'error:' in log:raise RuntimeError('Invalid proof log: '+name)
        for ax in re.findall(r'depends on axioms: \[(.*?)\]',log,re.S):
            if {a.strip() for a in ax.split(',') if a.strip()}-ALLOWED:raise RuntimeError('Unexpected axioms: '+name)
        rec['olean_sha256']=digest(target/(name+'.olean'));return rec
    done=set();pending=set(names); running={}
    def record(rec):
        records.append(rec);done.add(rec['module'])
        (out/'rebuild-record.json').write_text(json.dumps(records,indent=2)+'\n')
        if len(done)%40==0 or rec['module'] in {'GraphReductions','CertificateKernel','NormalizedBounds','Result','FiniteResult','IntervalResult'}:
            print(str(len(done))+'/'+str(len(names))+' checked; '+rec['module'],flush=True)
    # Base modules run without competing certificate processes.
    for name in ('GraphReductions','CertificateKernel'):
        if dependencies[name]-done:raise RuntimeError('Unexpected base dependency')
        rec=compile_module(name)
        if rec['exit_code']:raise RuntimeError('Base module failed: '+name)
        record(rec);pending.remove(name)
    with concurrent.futures.ThreadPoolExecutor(max_workers=12) as pool:
        while pending or running:
            available=sorted(n for n in pending if dependencies[n]<=done)
            reserved=sum(memory_for(n) for n in running.values())
            for name in available:
                if len(running)>=12:break
                if reserved+memory_for(name)>38000:continue
                pending.remove(name);running[pool.submit(compile_module,name)]=name
                reserved+=memory_for(name)
            if not running:raise RuntimeError('Cyclic or unresolved module dependencies')
            finished,_=concurrent.futures.wait(running,return_when=concurrent.futures.FIRST_COMPLETED)
            for future in finished:
                name=running.pop(future);rec=future.result()
                if rec['exit_code']:
                    attempts.append(rec)
                    (out/'failed-attempts.json').write_text(json.dumps(attempts,indent=2)+'\n')
                    if rec.get('memory_failure') and limits[name]<10000:
                        limits[name]=6000 if limits[name]<6000 else 10000
                        (target/(name+'.olean')).unlink(missing_ok=True)
                        pending.add(name)
                        print('Memory-limited attempt retained; retrying '+name+' with '+str(limits[name])+' MiB within the same job budget.',flush=True)
                    else:raise RuntimeError('Lean failed for '+name+'; see '+rec['failure_log'])
                else:record(rec)
    if done!=names:raise RuntimeError('Incomplete build')
    final=(out/'Result.log').read_text(); theorem='TuzaTwoTypes.tuza_of_two_active_types'
    match=re.search(re.escape("'"+theorem+"'")+r' depends on axioms: \[(.*?)\]',final,re.S)
    if not match:raise RuntimeError('Missing final axiom audit')
    axioms=sorted(a.strip() for a in match[1].split(','))
    if set(axioms)!=ALLOWED:raise RuntimeError('Final axiom set changed')
    negative=source/'NegativeControl.lean';negative.write_text('import Result\nexample : (1 : ℕ) = 0 := by decide\n')
    p=subprocess.run(['lake','env','lean','-j1','-M2400','-DElab.async=false',str(negative)],cwd=work,env=dict(os.environ,LEAN_PATH=str(target)),capture_output=True,text=True,timeout=60)
    log=p.stdout+p.stderr;(out/'negative-control.log').write_text(log)
    if not(p.returncode==1 and 'error:' in log and 'is false' in log and 'decide' in log):raise RuntimeError('Negative control was not rejected normally')
    report={'status':'VERIFIED','modules':len(done),'theorem':theorem,'axioms':axioms,'negative_control_rejected':True,'all_project_modules_built_from_source':True,'project_olean_inputs':0,'memory_limited_attempts':len(attempts)}
    (out/'rebuild-report.json').write_text(json.dumps(report,indent=2)+'\n');print(final,flush=True);print(json.dumps(report),flush=True)
if __name__=='__main__':main()
