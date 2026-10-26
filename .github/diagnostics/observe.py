import os,sys,json,hashlib,re,subprocess,pathlib,time
P=pathlib.Path.cwd();O=P/'diagnostic-output';O.mkdir(exist_ok=True)
LOCK='/home/bourabbe/.lake-global.lock';CAP='12884901888'
def run(args,*,env=None,cwd=None,output=None):
    command=[str(x) for x in args]
    with (O/'commands.jsonl').open('a') as f:f.write(json.dumps({'argv':command,'cwd':str(cwd or P),'at':time.time()})+'\n')
    if output:
        with (O/output).open('w') as f:
            p=subprocess.run(command,cwd=cwd or P,env=env,stdout=f,stderr=subprocess.STDOUT)
    else:p=subprocess.run(command,cwd=cwd or P,env=env)
    if p.returncode:raise RuntimeError(f'command failed ({p.returncode}): {command}; log={output}')
    return p
lean=pathlib.Path(subprocess.check_output(['elan','which','lean'],text=True).strip());lake=lean.parent/'lake'
assert hashlib.sha256(lean.read_bytes()).hexdigest()=='bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38'
def locked(args,**kw):
    execution_env=kw.get('env') or os.environ
    exports=[k+'='+execution_env[k] for k in ['LEAN_PATH','LEAN_SRC_PATH','PATH'] if k in execution_env]
    return run(['/usr/bin/flock','-x',LOCK,'sudo','systemd-run','--quiet','--scope','--property=MemoryMax='+CAP,'--property=MemorySwapMax=0','--','runuser','-u',os.environ['USER'],'--','env',*exports,*args],**kw)
manifest=json.loads((P/'lake-manifest.json').read_text())
packages={x['name'].removeprefix('«').removesuffix('»'):P/'.lake/packages'/x['name'].removeprefix('«').removesuffix('»') for x in manifest['packages']}
for x in manifest['packages']:
    name=x['name'].removeprefix('«').removesuffix('»');d=packages[name];d.mkdir(parents=True,exist_ok=True)
    run(['git','init',d],output='fetch-'+name+'.log')
    run(['git','-C',d,'remote','add','origin',x['url']],output='remote-'+name+'.log')
    run(['git','-C',d,'fetch','--depth=1','origin',x['rev']],output='fetch-'+name+'.log')
    run(['git','-C',d,'checkout','--detach',x['rev']],output='checkout-'+name+'.log')
# Bootstrap only the exact pinned cache client's small source closure, serially.
# No Lake process, configuration edit, toolchain wrapper or project build cache is used.
bootstrap_roots=list(packages.values());core=lean.parent.parent/'lib/lean'
cacheenv=os.environ.copy();cacheenv['LEAN_PATH']=os.pathsep.join([str(d/'.lake/build/lib/lean') for d in bootstrap_roots]+[str(core)])
cacheenv['LEAN_SRC_PATH']=os.pathsep.join(str(d) for d in bootstrap_roots)
cache_seen=set()
def cache_build(module):
    if module in cache_seen:return
    cache_seen.add(module);rel=pathlib.Path(*module.split('.')).with_suffix('.lean')
    match=next(((d,d/rel) for d in bootstrap_roots if (d/rel).is_file()),None)
    if match is None:return
    root,source=match
    for group in re.findall(r'(?m)^(?:(?:public|private|meta) )*import\s+([^\n]+)',source.read_text()):
        for dep in group.split('--')[0].split():cache_build(dep)
    out=root/'.lake/build/lib/lean'/rel.with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
    locked([lean,'-j1','-o',out,source],cwd=root,env=cacheenv,output='bootstrap-'+module+'.log')
cache_build('Cache.Main')
mathlib=packages['mathlib']
# Preserve the pinned package layout expected by the official cache client.
for n,d in packages.items():
    if n=='mathlib':continue
    link=mathlib/'.lake/packages'/n;link.parent.mkdir(parents=True,exist_ok=True);link.symlink_to(d,target_is_directory=True)
locked([lean,'-j1','--run',mathlib/'Cache/Main.lean','get'],cwd=mathlib,env=cacheenv,output='cache.log')
bindings=[]
for x in manifest['packages']:
    d=packages[x['name'].removeprefix('«').removesuffix('»')];head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=d,text=True).strip();assert head==x['rev'],(x['name'],head,x['rev'])
    bindings.append({'name':x['name'].removeprefix('«').removesuffix('»'),'commit':head})
assert next(x for x in bindings if x['name']=='mathlib')['commit']=='065356127b1dc0016f66b7283ce0ce2c4055aa55'
(O/'bindings.json').write_text(json.dumps({'source_commit':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'lean_sha256':hashlib.sha256(lean.read_bytes()).hexdigest(),'dependencies':bindings},indent=2)+'\n')
# No old project artifact is restored. Only exact pinned Mathlib cache data is used.
roots=[P]+[d for n,d in packages.items() if n=='lattice-probability']
builds=[d/'.lake/build/lib/lean' for d in roots]
for d in builds:d.mkdir(parents=True,exist_ok=True)
trusted=[d/'.lake/build/lib/lean' for n,d in packages.items() if n!='lattice-probability']+[lean.parent.parent/'lib/lean']
env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join(str(d) for d in [*builds,*trusted])
trustedenv=env.copy();trustedenv['LEAN_PATH']=os.pathsep.join(str(d) for d in trusted)
seen=set();failed={}
def build(module):
    if module in seen:return
    if module in failed:raise RuntimeError('prior failed dependency: '+module)
    rel=pathlib.Path(*module.split('.')).with_suffix('.lean')
    match=next(((d,d/rel) for d in roots if (d/rel).is_file()),None)
    if match is None:return
    root,source=match
    imports=re.findall(r'(?m)^(?:(?:public|private|meta) )*import\s+([^\n]+)',source.read_text())
    for group in imports:
        for dep in group.split('--')[0].split():build(dep)
    out=root/'.lake/build/lib/lean'/rel.with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
    opts=['-DautoImplicit=false'] if root!=P else ([] if MODE=='sphere' and module.startswith('BouRabeeGwynne.') else ['-DautoImplicit=false','-DrelaxedAutoImplicit=false'])
    print('COMPILE',module,flush=True)
    try:
        locked([lean,'-j1',*opts,'-o',out,source],cwd=root,env=env,output='build-'+module+'.log')
    except Exception as e:
        failed[module]=str(e)
        raise
    seen.add(module)
    with (O/'compiled.jsonl').open('a') as f:f.write(json.dumps({'module':module,'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'olean_sha256':hashlib.sha256(out.read_bytes()).hexdigest()})+'\n')
MODE='parking'
results=[]
def attempt(label, action):
    try:
        action();results.append({'target':label,'status':'pass'})
    except Exception as e:
        results.append({'target':label,'status':'fail','error':str(e)})
    (O/'target-results.json').write_text(json.dumps(results,indent=2)+'\n')
for module in ['LatticeProb.Prob.DagExploration','LatticeProb.Prob.ExplorationCond',
               'LatticeProb.Invariance','Parking.Support.Parallel','LatticeProb.MomentNorm']:
    attempt(module,lambda module=module:build(module))
attempt('five-helper-and-library-axioms',lambda:locked(
    [lean,'-j1','-DautoImplicit=false',P/'.github/diagnostics/MeasurableBridges.lean'],
    env=env,output='helper-axioms.log'))
for module in ['Parking.Support.BlockTools','Parking.Support.MomentLimits']:
    attempt(module,lambda module=module:build(module))
attempt('two-parking-caller-axioms',lambda:locked(
    [lean,'-j1','-DautoImplicit=false','-DrelaxedAutoImplicit=false',
     P/'.github/diagnostics/OuterCallers.lean'],env=env,output='caller-axioms.log'))
if any(row['status']!='pass' for row in results):raise RuntimeError('See target-results.json')
