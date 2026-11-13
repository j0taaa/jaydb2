#!/usr/bin/env python3
"""Validate fresh checked samples and derive LaTeX/plot data (no benchmarks)."""
import json
import functools
import math
from pathlib import Path
import re
import statistics
import sys

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
OUT=ROOT/'.build/tcc'
FILES=('ordinary','prepared','comparison','verification','scaling','scaling-seed-attempt','gpu-programs','simulation')
PROGRAMS={'read':'Read','indexed':'Indexed','voucher':'Voucher'}
MACROS={}


def canonical(value):
    return json.dumps(value,sort_keys=True,separators=(',',':'),allow_nan=False)


def quartiles(values):
    q1,_,q3=statistics.quantiles(values,n=4,method='inclusive')
    return dict(n=len(values),median=statistics.median(values),qone=q1,qthree=q3,
        iqr=q3-q1)


def summary(samples):
    values=[s['elapsed_ns'] for s in samples]
    return quartiles(values)


def active_throughput(record):
    rows=record['samples']
    return quartiles([30e9/sum(s['elapsed_ns'] for s in rows[i:i+30]) for i in range(0,len(rows),30)])


def checked(sample):
    if sample.get('checked') is not True or canonical(sample.get('actual'))!=canonical(sample.get('expected')):
        raise ValueError('Unchecked or incorrect output')
    if type(sample.get('elapsed_ns')) is not int or sample['elapsed_ns']<=0:
        raise ValueError('Invalid elapsed nanoseconds')


def samples(record,n=None,workload=None):
    n=record['n'] if n is None else n
    rows=record['samples']
    warmup=record['warmup']
    if workload:
        rows=[s for s in rows if s['workload']==workload]
        warmup=[s for s in warmup if s['workload']==workload]
    if len(rows)!=n or any(type(s['iteration']) is not int for s in rows) or {s['iteration'] for s in rows}!=set(range(1,n+1)) or len(warmup)!=1 or warmup[0]['iteration']!=0:
        raise ValueError('Missing or duplicate measured samples/warmup')
    for row in rows+warmup:checked(row)
    return summary(rows)


def validate(data):
    for name in FILES:
        meta=data[name].get('metadata',{})
        for key in ('cpu','kernel','python','node','clang','rust','cargo','bend','toolchain','commit','binary_sha256','source_sha256'):
            if not meta.get(key): raise ValueError('Missing metadata: '+key)
        if not re.fullmatch('[0-9a-f]{40}',meta['commit']): raise ValueError('Invalid commit')
        for key in ('binary_sha256','source_sha256'):
            if not re.fullmatch('[0-9a-f]{64}',meta[key]):raise ValueError('Invalid engine fingerprint: '+key)
    for key in ('binary_sha256','source_sha256'):
        if len({data[name]['metadata'][key] for name in ('ordinary','prepared','comparison','scaling','verification','gpu-programs','simulation')})!=1:
            raise ValueError('Mixed engine fingerprints: '+key)
    for name in ('ordinary','prepared','comparison','scaling','verification','gpu-programs','simulation'):
        if data[name]['metadata'].get('dirty')!=[]:raise ValueError('Dirty measurement: '+name)
        validate_frequency(data[name]['metadata'])
        if canonical(data[name]['metadata']['toolchain'])!=canonical(data['ordinary']['metadata']['toolchain']):raise ValueError('Mixed toolchain metadata')
    validate_compute(data)
    if {r['program'] for r in data['ordinary']['records']}!=set(PROGRAMS) or len(data['ordinary']['records'])!=3:
        raise ValueError('Ordinary program coverage')
    for r in data['ordinary']['records']:
        samples(r,30)
        phases={'staging','primary_check','bendtt_translate_check','c_emission','c_compilation','admission_total','ordinary_worker','publication'}
        if any(not phases<=s['phases_ns'].keys() for s in r['samples']): raise ValueError('Missing ordinary phase timing')
    expected={(p,m) for p in PROGRAMS for m in (False,True)}
    identities=[(r['program'],r['persistent']) for r in data['prepared']['records']]
    if len(identities)!=6 or set(identities)!=expected:raise ValueError('Prepared program/mode coverage')
    for r in data['prepared']['records']:
        samples(r,900)
        if len(r['registrations'])!=9:raise ValueError('Missing registration samples')
        for row in r['registrations']:
            checked(row)
            if row['actual'].get('status')!='prepared' or not re.fullmatch('[a-f0-9]{64}',row['actual'].get('value','')):
                raise ValueError('Invalid prepared receipt')
        if r['program']=='voucher' and any(s.get('untimed_retirement_checked') is not True for s in r['samples']):
            raise ValueError('Unchecked voucher retirement')
    comparisons=data['comparison']['records']
    if len(comparisons)!=12 or {(r['engine'],r['policy'],r['rows']) for r in comparisons}!={(e,p,n) for e in ('jaydb2','postgresql','sqlite') for p in ('point','owner') for n in (10,data['comparison']['large_rows'])}:
        raise ValueError('Comparison engine/policy coverage')
    for r in comparisons:
        if r.get('total_rows_checked') is not True:raise ValueError('Unverified comparison row count')
        for workload in ('read','update'):samples(r,900,workload)
        if r['engine']=='jaydb2':
            for z in r['sessions']:
                population=z['population']
                for call in population['calls']:checked(call)
                if population['total_rows']!=r['rows'] or sum(call['actual']['value'] for call in population['calls'])!=r['rows']:
                    raise ValueError('Comparison population count disagrees')
            for s in r['samples']:
                if s['workload']=='update' and s.get('stored_value_checked') is not True:raise ValueError('Unchecked stored update')
            for w in (('read','update') if r['rows']==10 else ()):
                rows=[s for s in r['ordinary'] if s['workload']==w and s['phase']=='sample']
                if len(rows)!=30:raise ValueError('Ordinary comparison context samples')
                for row in rows:checked(row)
    policy=data['comparison']['policy_checks']
    expected={(e,w,n,sid) for e in ('jaydb2','postgresql','sqlite') for w in ('read','update') for n in (10,data['comparison']['large_rows']) for sid in (1,2,3)}
    if len(policy)!=len(expected) or {(r['engine'],r['workload'],r['rows'],r['session']) for r in policy}!=expected:
        raise ValueError('Missing policy refusal checks')
    for row in policy:
        if row.get('refused') != (row['engine']!='sqlite') or row.get('checked') is not True or canonical(row['actual'])!=canonical(row['expected']) or not row.get('attempt'):
            raise ValueError('Policy check failed')
        if row['engine']=='postgresql' and row['actual']!=[]:raise ValueError('PostgreSQL cross-user SQL returned rows')
        if row['engine']=='jaydb2' and row['actual']!={'status':'certificate','value':None}:raise ValueError('JayDB2 cross-user admission did not reject certificate')
        if row['engine']=='sqlite' and row['actual']!=([[0]] if row['workload']=='read' else [[999]]):raise ValueError('SQLite unconstrained check did not succeed')
    postchecks=data['comparison'].get('policy_postchecks',[])
    expected_post={(e,n,sid) for e in ('jaydb2','postgresql','sqlite') for n in (10,data['comparison']['large_rows']) for sid in (1,2,3)}
    if len(postchecks)!=len(expected_post) or {(r['engine'],r['rows'],r['session']) for r in postchecks}!=expected_post:
        raise ValueError('Missing cross-user postchecks')
    for row in postchecks:
        expected_value={'status':'success','value':0} if row['engine']=='jaydb2' else [[0]]
        if row.get('checked') is not True or row['actual']!=expected_value or row['actual']!=row['expected']:
            raise ValueError('Cross-user stored value changed')
    for pg in [data['comparison']['settings']['postgresql']]+[x['settings'] for r in comparisons if r['engine']=='postgresql' for x in r['sessions']]:
        if pg['fsync']!='on' or pg['synchronous_commit']!='on' or pg['role'][1:]!=[False,False] or ('rls' in pg and pg['rls']!=[True,True]):
            raise ValueError('PostgreSQL durability/RLS settings')
    for sq in [data['comparison']['settings']['sqlite']]+[x['settings'] for r in comparisons if r['engine']=='sqlite' for x in r['sessions']]:
        if sq['synchronous']!=2 or sq['journal_mode']!='wal':raise ValueError('SQLite durability settings')
    for name in ('ordinary','prepared','comparison'):
        validate_frequency(data[name]['metadata'])
        for record in data[name]['records']:validate_sessions(record,name)
    validate_frequency(data['scaling']['metadata'])
    for record in comparisons:
        if record['engine']=='postgresql' and record['policy']=='owner':
            if any(z['settings'].get('rls')!=[True,True] for z in record['sessions']):raise ValueError('PostgreSQL durability/RLS settings')
    validate_frequency(data['verification']['metadata'])
    if 'size_collection_metadata' in data['verification']:
        inventory=data['verification']['size_collection_metadata']
        validate_frequency(inventory)
        if inventory.get('dirty')!=[] or any(inventory[k]!=data['verification']['metadata'][k] for k in ('binary_sha256','source_sha256','commit')):
            raise ValueError('Source inventory measurement provenance')
    commands=data['verification']['commands']
    if {r['command'] for r in commands}!={'make verify-contract','make verify','make test'}:raise ValueError('Missing verification run')
    for row in commands:
        if not row.get('output') or row['elapsed_ns']<=0:raise ValueError('Missing verification output')
        if row['returncode']!=0:raise ValueError('Required verification gate failed; inspect retained output')
        if 'metadata' in row:validate_frequency(row['metadata'])
    count=data['verification']['negative_fixtures']
    verify_output=next(row['output'] for row in commands if row['command']=='make verify')
    if f'OK negative controls: {count} fixtures, {count*2} official-mode rejections' not in verify_output:
        raise ValueError('Core negative inventory disagrees with completed verification')
    native=re.search(r'OK native RLS session: (\d+) checked responses;.*? (\d+) admission denials',
        next(row['output'] for row in commands if row['command']=='make test'))
    rls=data['verification'].get('rls_validation',{})
    if native is None or rls!={'native_responses':int(native[1]),'negative_fixtures':int(native[2])}:
        raise ValueError('RLS inventory disagrees with completed native validation')
    duties=(ROOT/'proof/README.md').read_text().split('**T3 —',1)[1].split('\nThe status table',1)[0]
    if data['verification'].get('host_duty_count')!=len(re.findall(r'^\d+\. ',duties,re.M)):
        raise ValueError('Host duty inventory disagrees with proof/README.md')
    # Failed measurements remain visible; they are never replaced with estimates.
    scaling=data['scaling']
    if not scaling['records']:raise ValueError('No state scaling measurements')
    if not scaling.get('setup_method'):raise ValueError('Missing scaling setup method')
    identities=[(r['rows'],r['persistent']) for r in scaling['records']]
    if len(identities)!=len(set(identities)):raise ValueError('Duplicate scaling point')
    expected={(n,m) for n in (10,30,100,300,600,1000,scaling['max_rows']) for m in (False,True)}
    if not expected<=set(identities):raise ValueError('Missing scaling population/mode coverage')
    for r in scaling['records']:
        for row in r['population']['calls']:checked(row)
        if r['population']['total_rows']!=r['rows'] or r['population']['calls'][0]['actual']!={'status':'success','value':r['rows']}:raise ValueError('Scaling population count disagrees')
        if r['state_bytes']>scaling['state_limit']:raise ValueError('Scaling state exceeds limit')
        for w in ('read','update'):samples(r,50,w)
        for s in r['samples']:
            if s['workload']=='update' and s.get('stored_value_checked') is not True:raise ValueError('Unchecked scaling update')
    for mode in (False,True):
        if len({r['service_pid'] for r in scaling['records'] if r['persistent']==mode})!=1:raise ValueError('Scaling service not reused')
    for r in scaling['records']:
        validate_frequency(r)
        if r['rows'] in (10,scaling['max_rows']):
            samples(dict(n=50,samples=r['first_key_samples'],warmup=r['first_key_warmup']),50,'read')
    for failure in scaling['failures']:
        if not failure.get('reason'):raise ValueError('Unexplained scaling failure')
    for mode in (False,True):
        if (scaling['max_rows'],mode) in identities:
            probes=[s for s in scaling.get('boundary_checks',[]) if s['persistent']==mode]
            if len(probes)!=1:raise ValueError('Missing actual state-limit probe')
            probe=probes[0];checked(probe)
            if probe['actual']!={'status':'limit','value':None} or probe['rows']!=scaling['max_rows']+1 or probe['state_bytes']<=scaling['state_limit']:
                raise ValueError('Invalid state-limit probe')
            checked(probe['rollback_check'])
    for attempt in data['scaling-seed-attempt']['failures']:
        if attempt.get('measured') and not attempt.get('reason'):raise ValueError('Unexplained seed-check failure')
    return data


def validate_frequency(record):
    f=record.get('frequency',{})
    settings=f.get('settings',{})
    if len(settings)!=33 or any(v!=('1' if p.endswith('/no_turbo') else 'performance') for p,v in settings.items()):
        raise ValueError('Missing fixed CPU frequency policy')
    if len(f.get('scaling_cur_freq_khz',{}))!=16 or any(v<=0 for v in f['scaling_cur_freq_khz'].values()):
        raise ValueError('Missing sampled CPU frequencies')


def validate_sessions(record,name):
    sessions=record.get('sessions',[])
    if len(sessions)!=3 or {r.get('session') for r in sessions}!={1,2,3}:raise ValueError('Missing independent sessions')
    n=10 if name=='ordinary' else 300
    for r in sessions:
        validate_frequency(r)
        for w in (('read','update') if name=='comparison' else (None,)):samples(r,n,w)
        if name=='prepared':
            if len(r['registrations'])!=3:raise ValueError('Missing session registrations')
            for x in r['registrations']:checked(x)
    # The pooled view must exactly retain every raw measured observation.
    pooled=[{k:v for k,v in x.items() if k not in ('session','session_iteration','iteration')} for x in record['samples']]
    raw=[{k:v for k,v in x.items() if k!='iteration'} for r in sessions for x in r['samples']]
    if canonical(pooled)!=canonical(raw):raise ValueError('Pooled samples disagree with independent sessions')


# To be integrated in paper/evidence.py after the clean evidence refresh.
def positive_ms(values, count, label):
    if len(values)!=count or any(type(v) not in (float,int) or not math.isfinite(v) or v<=0 for v in values):
        raise ValueError('Invalid '+label+' samples')


def validate_artifacts(preparations, gpu_mib, emitted_bangs=False):
    if len(preparations)!=3 or {p['backend'] for p in preparations}!={'cpu-1','cpu-16','cuda'}:
        raise ValueError('GPU preparation coverage')
    if len({p['artifact']['sourceSha256'] for p in preparations})!=1:
        raise ValueError('CPU/CUDA emitted C differs')
    for p in preparations:
        artifact=p['artifact'];cuda=p['backend']=='cuda'
        if artifact.get('format')!='jaydb-official-c-v1':raise ValueError('GPU artifact format')
        if artifact.get('backend')!=('cuda' if cuda else 'cpu'):
            raise ValueError('GPU artifact backend')
        for key in ('sourceSha256','executableSha256','compilerSha256')+(('gpuSha256',) if cuda else ()):
            if not re.fullmatch('[a-f0-9]{64}',artifact.get(key,'')):raise ValueError('GPU artifact hash: '+key)
        if emitted_bangs and (type(artifact.get('emitted_bangs')) is not int or artifact['emitted_bangs']<=0):
            raise ValueError('Missing emitted bangs')
        if cuda:
            if artifact.get('hasBangs') is not True or artifact.get('gpuMiB')!=gpu_mib:
                raise ValueError('GPU artifact bang/corpus')
            libraries=artifact.get('cudaLibraries',{})
            if set(libraries)!={'libcuda.so.1','libnvrtc.so.12'}:raise ValueError('Missing CUDA library provenance')
            for lib in libraries.values():
                if not lib.get('path','').startswith('/') or not re.fullmatch('[a-f0-9]{64}',lib.get('sha256','')):
                    raise ValueError('Invalid CUDA library provenance')


@functools.lru_cache(maxsize=None)
def gpu_oracle(depth):
    # Independent arithmetic oracle from the benchmark; evaluated at every size.
    from paper.bench.gpu_programs import oracle
    return oracle(depth)


@functools.lru_cache(maxsize=None)
def simulation_oracle(depth, steps, user='alice', vector=True):
    from tests.service.test_simulation import oracle
    return oracle(depth, steps, user, vector=vector)


def validate_compute(data):
    import hashlib
    from tests.service.test_simulation import state as simulation_state, PARAMETERS
    from paper.bench.gpu_programs import state as gpu_state
    gpu=data['gpu-programs'];sim=data['simulation']
    expected_fixtures={'experiments/gpu/HeavyClient.bend','experiments/gpu/ClientProof.bend','paper/bench/gpu_programs.py'}
    expected_simulation={str(p.relative_to(ROOT)) for p in (ROOT/'applications/simulation').glob('*.bend')} | {'paper/bench/simulation.py','paper/bench/simulation-postgres.sql','paper/bench/simulation-sqlite.sql','tests/service/test_simulation.py'}
    if set(gpu['fixture_sha256'])!=expected_fixtures or set(sim['source_sha256'])!=expected_simulation:
        raise ValueError('Compute fixture fingerprint coverage')
    for d,field in ((gpu,'fixture_sha256'),(sim,'source_sha256')):
        for name,digest in d[field].items():
            if hashlib.sha256((ROOT/name).read_bytes()).hexdigest()!=digest:
                raise ValueError('Compute fixture fingerprint: '+name)
    if gpu['revision']!=gpu['metadata']['commit'] or gpu['dirty']!=[] or gpu['binary_sha256']!=gpu['metadata']['binary_sha256'] or canonical(gpu['toolchain'])!=canonical(gpu['metadata']['toolchain']):
        raise ValueError('GPU metadata disagrees')
    validate_frequency(gpu)
    if gpu['gpu_mib']!=512 or gpu['gpu_worker_cap']!=1 or gpu['warmups']!=1 or gpu['repeats']<3:
        raise ValueError('GPU measurement protocol')
    validate_artifacts(gpu['runs'],gpu['gpu_mib'])
    depths=None
    for run in gpu['runs']:
        positive_ms([run['first_preparation_ms']],1,'GPU preparation')
        if run['threads']!=(16 if run['backend']=='cpu-16' else 1):
            raise ValueError('GPU preparation/threads')
        current=[r['depth'] for r in run['records']]
        if len(current)!=2 or current[0]!=2 or not 3<=current[1]<=16 or (depths is not None and current!=depths):
            raise ValueError('GPU size coverage')
        depths=current
        expected=[gpu_state('alice-token')]*3
        for row in run['records']:
            depth=row['depth'];reference=gpu_oracle(depth)
            if (row['leaves'],row['rounds_per_leaf'],row['total_mixing_rounds'])!=(1<<depth,depth*4096,(1<<depth)*depth*4096):
                raise ValueError('GPU workload dimensions')
            if row['result']!=reference or gpu['oracle'][str(depth)]!=reference:
                raise ValueError('GPU oracle disagrees')
            for field in ('native_worker','complete_request'):
                values=row[field+'_ms'];positive_ms(values,gpu['repeats'],'GPU')
                if row['median_'+field+'_ms']!=statistics.median(values):raise ValueError('GPU raw summary disagrees')
            expected.extend([gpu_state('x'*depth)]*(gpu['repeats']+1))
        if run['full_published_states']!=expected:raise ValueError('GPU complete published state')
    scalar=0
    for seed in range(4):
        value=seed
        for _ in range(8192):value=((value^(value>>16))*1664525+1013904223)&0xffffffff
        scalar=(scalar+value)&0xffffffff
    if gpu['small_scalar_oracle']!=scalar or scalar!=gpu_oracle(2):raise ValueError('GPU scalar oracle')
    sizes=sim['sizes'];identities=[(s['depth'],s['steps']) for s in sizes]
    from paper.bench.simulation import SIZES
    if identities!=SIZES:raise ValueError('Simulation size coverage')
    if len(identities)!=4 or len(set(identities))!=4 or any(s['paths']!=1<<s['depth'] for s in sizes):
        raise ValueError('Simulation size coverage')
    if canonical(sim['parameters'])!=canonical({k:list(v) for k,v in PARAMETERS.items()}) or sim['warmups']!=1 or sim['repeats']<3 or sim['gpu_mib']!=512:
        raise ValueError('Simulation measurement protocol')
    if sim['settings']['cuda']['clock_fixed'] is not False or sim['settings']['cpu_threads']!=[1,16] or sim['settings']['cuda']['corpus_mib']!=sim['gpu_mib'] or sim['settings']['cuda']['host_threads']!=1 or sim['metadata']['threads']!=[1,16] or sim['metadata']['session_count']!=1:
        raise ValueError('Simulation clock/threads')
    if sim['settings']['postgresql']['tables']!='TEMP' or sim['settings']['sqlite']['storage']!=':memory:':
        raise ValueError('Simulation volatile SQL settings')
    references={}
    for depth,steps in identities:
        key=f'{depth}:{steps}';references[key]=simulation_oracle(depth,steps)
        if canonical(sim['oracle'][key])!=canonical(references[key]):raise ValueError('Simulation oracle disagrees')
    for user in PARAMETERS:
        if simulation_oracle(3,17,user)!=simulation_oracle(3,17,user,False):raise ValueError('Simulation scalar/vector oracle')
    validate_artifacts(sim['preparations'],sim['gpu_mib'],emitted_bangs=True)
    for prep in sim['preparations']:
        if prep['threads']!=(16 if prep['backend']=='cpu-16' else 1):raise ValueError('Simulation preparation threads')
        positive_ms([prep['elapsed_ms']],1,'simulation preparation')
    backends=('cpu-1','cpu-16','cuda','postgresql','sqlite')
    if len(sim['records'])!=len(backends)*len(sizes):raise ValueError('Simulation backend coverage')
    for backend in backends:
        rows=[r for r in sim['records'] if r['backend']==backend]
        if [(r['depth'],r['steps']) for r in rows]!=identities:raise ValueError('Simulation backend/size coverage')
        capped=False;last=None
        for row in rows:
            if row['paths']!=1<<row['depth']:raise ValueError('Simulation path count')
            if row['status']=='measured':
                if capped:raise ValueError('Simulation measured beyond timeout')
                positive_ms(row['samples_ms'],sim['repeats'],'simulation')
                positive_ms(row['warmup_ms'],1,'simulation warmup')
                if row['median_ms']!=statistics.median(row['samples_ms']) or row['range_ms']!=[min(row['samples_ms']),max(row['samples_ms'])]:
                    raise ValueError('Simulation raw summary disagrees')
                if row['updates']!=row['paths']*row['steps'] or canonical(row['result'])!=canonical(references[f"{row['depth']}:{row['steps']}"]):
                    raise ValueError('Simulation result disagrees')
                if row['complete_state_verified'] is not True:raise ValueError('Simulation unchecked state')
                last=row['updates']
            elif backend in ('postgresql','sqlite') and row['status'] in ('timeout','not run'):
                if row.get('median_ms') is not None or row.get('result') is not None or row['timeout_s']<=0:
                    raise ValueError('Simulation fabricated timeout result')
                if row['status']=='not run' and not capped:raise ValueError('Simulation skipped before timeout')
                if row['status']=='timeout':
                    if capped or row['last_verified_updates']!=last or not row.get('diagnostic'):
                        raise ValueError('Simulation timeout provenance')
                capped=True
            else:raise ValueError('Simulation invalid status')
        if backend in backends[:3]:
            expected=[simulation_state({})]*3
            for reference in references.values():expected.extend([simulation_state({'alice':reference})]*(sim['repeats']+1))
            if canonical(sim['published_states'][backend])!=canonical(expected):raise ValueError('Simulation complete published state')
    gpu_artifact=next(p['artifact'] for p in gpu['runs'] if p['backend']=='cuda')
    sim_artifact=next(p['artifact'] for p in sim['preparations'] if p['backend']=='cuda')
    if canonical(gpu_artifact['cudaLibraries'])!=canonical(sim_artifact['cudaLibraries']) or gpu['gpu']!=sim['settings']['cuda']['device']:
        raise ValueError('Mixed CUDA environment')
    controls=sim['sql_controls']
    expected_controls={(e,u,d,s) for e in backends[3:] for u in PARAMETERS for d,s in ((0,0),(3,17))}
    if len(controls)!=len(expected_controls) or {(c['backend'],c['user'],c['depth'],c['steps']) for c in controls}!=expected_controls:
        raise ValueError('Simulation SQL control coverage')
    states={e:{} for e in backends[3:]}
    for c in controls:
        result=simulation_oracle(c['depth'],c['steps'],c['user'],False)
        if canonical(c['result'])!=canonical(result):raise ValueError('Simulation SQL control oracle')
        states[c['backend']][c['user']]=result
        if canonical(c['complete_tables'])!=canonical(simulation_state(states[c['backend']])['tables']):
            raise ValueError('Simulation SQL control state')


def load():
    return validate({n:json.loads((ROOT/'paper/evidence'/f'{n}.json').read_text()) for n in FILES})


def macro(name,value,meaning,unit):
    if not re.fullmatch('[A-Z][a-zA-Z]*',name):raise ValueError(name)
    MACROS[name]=(value,meaning,unit)


def metric(prefix,s,unit,scale,meaning):
    macro(prefix+'Median'+unit,s['median']/scale,meaning+' median',unit)


def fmt(x):
    return f'{x:,}'.replace(',', '{,}') if isinstance(x,int) else str(x) if isinstance(x,str) else f'{x:.6g}'


def decimal(value,precision=2):
    return f'{value:,.{precision}f}'.replace(',', '{,}')


def cell(s,scale=1e6,precision=2):
    return f"{decimal(s['median']/scale,precision)} [{decimal(s['qone']/scale,precision)}, {decimal(s['qthree']/scale,precision)}]"


def table(name,columns,rows):
    rendered=[' & '.join(fmt(x) if isinstance(x,int) else str(x) for x in row)+r' \\' for row in rows]
    (OUT/name).write_text('\\begin{tabular}{'+columns+'}\\toprule\n'+rendered[0]+'\n\\midrule\n'+'\n'.join(rendered[1:])+'\n\\bottomrule\\end{tabular}\n')


def source_inventory(directory):
    """Count maintained Bend files and nonblank physical lines, including comments."""
    files=sorted(directory.rglob('*.bend'))
    return dict(files=len(files), nonblank_lines=sum(
        bool(line.strip()) for path in files for line in path.read_text().splitlines()))


def write_compute_reports(data):
    gpu=data['gpu-programs'];sim=data['simulation']
    columns=('cpu-1','cpu-16','cuda','postgresql','sqlite')
    def timed(values):return f'{statistics.median(values):.3f} ({min(values):.3f}–{max(values):.3f})'
    header=['# E6: certified table-driven simulation','',
        f"Measured revision `{sim['metadata']['commit']}`; `dirty: {sim['metadata']['dirty']}`.",
        f"Engine source SHA-256 `{sim['metadata']['source_sha256']}`; executable SHA-256 `{sim['metadata']['binary_sha256']}`.",
        '', 'Generated by `paper/evidence.py` from retained raw samples after validation. E6 and E1–E5 share engine fingerprints with the focused GPU benchmark.',
        '', '[Application arithmetic and certificate](../../applications/simulation/README.md); [timing harness](../bench/simulation.py).',
        '', 'The universal certificate confines scenario reads and result writes to the authenticated user and proves finite Action execution; structural checking covers numerical recursion. It does not prove numeric/statistical properties or CUDA correctness. A foreign-result-write negative fails the installed access obligation in both official modes.',
        '', f"Complete request/query wall time in milliseconds: median (min–max), {sim['warmups']} excluded warmup and {sim['repeats']} measured samples per completed cell. Preparation is separate.",
        '', '| Paths × steps | JayDB2 CPU-1 | JayDB2 CPU-16 | JayDB2 CUDA | PostgreSQL PL/pgSQL | SQLite CTE |','|---|---:|---:|---:|---:|---:|']
    compact=['| Paths × steps | CPU-1 | CPU-16 | CUDA | PostgreSQL | SQLite |','|---|---:|---:|---:|---:|---:|']
    for size in sim['sizes']:
        cells=[];medians=[]
        for backend in columns:
            r=next(r for r in sim['records'] if r['backend']==backend and r['depth']==size['depth'] and r['steps']==size['steps'])
            if r['status']=='measured':cells.append(timed(r['samples_ms']));medians.append(f"{statistics.median(r['samples_ms']):.3f}")
            else:
                label=f"timeout {r['timeout_s']:g} s" if r['status']=='timeout' else 'not run'
                cells.append(label);medians.append(label)
        prefix=f"| {size['paths']:,} × {size['steps']:,} | "
        header.append(prefix+' | '.join(cells)+' |');compact.append(prefix+' | '.join(medians)+' |')
    header+=['','## Preparation (one observation, excluded above)','', '| Backend | ms |','|---|---:|']
    for p in sim['preparations']:header.append(f"| {p['backend']} | {p['elapsed_ms']:.3f} |")
    header+=['','## Protocol and limitations','',*['- '+limitation for limitation in sim['limitations']],
        '', 'CPU restoration is verified after every benchmark and in `cpu-restoration.json`/`refresh-log.json`. GPU clocks are unfixed. Artifact reports retain resolved CUDA library paths/hashes, not pinned library guarantees.',
        '', 'Independent scalar/NumPy oracles check every completed size and complete state. SQL controls exercise both users; timeouts retain cancellation diagnostics and rollback is checked by the harness. Timeouts and subsequent unrun sizes supply neither results nor extrapolated timing.',
        '', '[Raw evidence](simulation.json); [standalone figure](simulation.svg). Historical launch/development logs in `simulation-launch.json`, `simulation-validation.json` and `simulation-development.json` describe earlier revisions; they are not fresh E6 timings.']
    (OUT/'simulation.md').write_text('\n'.join(header)+'\n')
    (OUT/'simulation-rendered.md').write_text('\n'.join(compact)+'\n')
    report=['# Focused GPU program evidence','',f"Measured revision `{gpu['metadata']['commit']}`; `dirty: {gpu['metadata']['dirty']}`.",
        f"Engine source SHA-256 `{gpu['metadata']['source_sha256']}`; executable SHA-256 `{gpu['metadata']['binary_sha256']}`.",
        '', 'Generated by `paper/evidence.py` from the current raw JSON, sharing engine fingerprints with E1–E6. CPU is the default; explicit bang calls opt into official Bend CUDA execution.',
        '', 'Both official checkers accept the same sealed Book before CUDA C emission/compilation/prebuild. Proofs concern that Book’s semantics, under identical certificate, termination, access/RLS, size and publication obligations. No GPU validity axiom is introduced.',
        '', 'T2 additionally trusts Bend’s emitted CUDA runtime, NVRTC, CUDA driver, managed memory and GPU hardware. CUDA headers/libraries come from the host environment; resolved library paths/hashes are recorded, not pinned. Differential tests/oracles are implementation evidence, not proof of CUDA correctness.',
        '', 'Reports bind emitted C, executable and cubin hashes. CUDA execution rechecks artifacts before launch and accepting output; prepared calls compare exact sealed bytes. Artifact changes, rebuild notices and device errors discard the proposal. Requested bangs have no CPU fallback. Execution is serial per instance.',
        '', f"Native-worker and complete-request columns are separate trials, not additive phases. Each excludes one warmup and retains {gpu['repeats']} samples. Worker times include fresh process/device startup and exit; requests also include authentication, integrity checking, publication/inspector emission and decoding.",
        '', '| Depth / mixing rounds | Backend | Native worker median (range), ms | Complete request median (range), ms |','|---|---|---:|---:|']
    for run in gpu['runs']:
        for row in run['records']:
            report.append(f"| {row['depth']} / {row['total_mixing_rounds']:,} | {run['backend']} | {timed(row['native_worker_ms'])} | {timed(row['complete_request_ms'])} |")
    report+=['','## Separate preparation','', '| Backend | ms (one observation) |','|---|---:|']
    for run in gpu['runs']:report.append(f"| {run['backend']} | {run['first_preparation_ms']:.3f} |")
    report+=['','The independent Python/NumPy U32 oracle performs every seed/round and a small scalar cross-check. Every native proposal and complete published state is checked, including Bob’s unchanged credential. All modes emit identical C. Benchmarks use the unwrapped real driver.',
        '', 'CPU policy is fixed and restored after each benchmark; GPU clock is unfixed and the device drives the desktop. Fresh process/device costs dominate small work. No kernel-only latency, general speedup, timeout/resource quota, persistent worker, cross-instance scheduling or portability guarantee follows. The corpus does not cap total driver memory, and integrity checks do not defeat hostile same-UID file-use races.',
        '', '[Raw samples and artifact/library hashes](gpu-programs.json); [standalone figure](gpu-programs.svg). Historical implementation/launch validation is retained in `gpu-validation.json` and `gpu-validation-rerun.json`; those records identify their own earlier revisions and are not current paper measurements.']
    (OUT/'gpu-programs.md').write_text('\n'.join(report)+'\n')


def derive_compute(data):
    gpu=data['gpu-programs'];sim=data['simulation']
    device,driver,_=sim['settings']['cuda']['device'].splitlines()[1].split(', ')
    artifact=next(p['artifact'] for p in sim['preparations'] if p['backend']=='cuda')
    nvrtc=Path(artifact['cudaLibraries']['libnvrtc.so.12']['path']).name.split('.so.')[1]
    for name,value,meaning,unit in [
        ('GpuDevice',device,'Measured CUDA device','text'),
        ('GpuDriverVersion',driver,'Recorded NVIDIA driver version','version'),
        ('NvrtcLibraryVersion',nvrtc,'Resolved libnvrtc shared-library version (not pinned)','version'),
        ('GpuCorpusMiB',sim['gpu_mib'],'Requested CUDA managed-memory corpus','MiB'),
        ('SimulationRepeats',sim['repeats'],'E6 measured calls per completed backend/size','samples'),
        ('SimulationWarmups',sim['warmups'],'E6 excluded warmups per backend/size','calls'),
        ('SimulationSessionCount',sim['metadata']['session_count'],'E6 sessions per backend','sessions'),
        ('SimulationLargestPaths',sim['sizes'][-1]['paths'],'Largest E6 path count','paths'),
        ('SimulationLargestSteps',sim['sizes'][-1]['steps'],'Largest E6 steps per path','steps'),
        ('SimulationMeasuredSamples',sum(len(r.get('samples_ms',[])) for r in sim['records']),'E6 completed measured samples across all backends','samples'),
        ('GpuRepeats',gpu['repeats'],'Focused GPU samples per size/backend/timing boundary','samples')]:macro(name,value,meaning,unit)
    labels={'cpu-1':'CpuOne','cpu-16':'CpuSixteen','cuda':'Cuda'}
    for prep in sim['preparations']:
        macro('Simulation'+labels[prep['backend']]+'PreparationMs',prep['elapsed_ms'],'E6 single preparation observation; excluded from call times','ms')
    for backend,label in labels.items():
        records=[r for r in sim['records'] if r['backend']==backend]
        for row,size in ((records[0],'Small'),(records[-1],'Large')):
            macro('Simulation'+size+label+'Ms',statistics.median(row['samples_ms']),'E6 '+size.lower()+' complete '+backend+' request median','ms')
    for run in gpu['runs']:
        if run['backend']=='cuda':
            macro('GpuSmallCudaNativeMs',statistics.median(run['records'][0]['native_worker_ms']),'Small focused CUDA native worker median; includes process/device startup','ms')
    def ms_cell(row,locale='en',ranges=True):
        if row['status']=='timeout':
            seconds=decimal(row['timeout_s'],0)
            return r'\textit{timeout} '+seconds+r' s' if locale=='en' else r'\textit{tempo esgotado} ('+seconds+r' s)'
        if row['status']=='not run':return r'\textit{not run}' if locale=='en' else r'\textit{não executado}'
        values=row['samples_ms']
        def number(v):
            s=decimal(v,3)
            return s if locale=='en' else s.replace('{,}',r'\,').replace('.',',')
        return number(statistics.median(values))+(r' ['+number(min(values))+', '+number(max(values))+']' if ranges else '')
    backends=('cpu-1','cpu-16','cuda','postgresql','sqlite')
    # One derived data contract supplies the HTML table and its speaker notes.
    deck_rows=[]
    for size in sim['sizes']:
        cells=[]
        for backend in backends:
            r=next(r for r in sim['records'] if r['backend']==backend and
                r['depth']==size['depth'] and r['steps']==size['steps'])
            cell=dict(backend=backend,status=r['status'])
            if r['status']=='measured':
                cell.update(median_ms=statistics.median(r['samples_ms']),
                    min_ms=min(r['samples_ms']),max_ms=max(r['samples_ms']))
            elif r['status']=='timeout':cell['timeout_s']=r['timeout_s']
            cells.append(cell)
        deck_rows.append(dict(paths=size['paths'],steps=size['steps'],cells=cells))
    (OUT/'simulation-deck.json').write_text(json.dumps(deck_rows,indent=2)+'\n')
    for locale in ('en','pt'):
        rows=[['Paths $\\times$ steps' if locale=='en' else 'Caminhos $\\times$ passos','CPU-1','CPU-16','CUDA','PostgreSQL','SQLite']]
        for size in sim['sizes']:
            records=[next(r for r in sim['records'] if r['backend']==backend and r['depth']==size['depth'] and r['steps']==size['steps']) for backend in backends]
            n=lambda x:fmt(x) if locale=='en' else fmt(x).replace('{,}',r'\,')
            rows.append([n(size['paths'])+r' $\times$ '+n(size['steps'])]+[ms_cell(r,locale,ranges=False) for r in records])
        table('simulation-table-'+locale+'.tex','@{}lrrrrr@{}',rows)
    # Full ranges remain separately available without crowding the six-column table.
    rows=[['Paths $\\times$ steps','Backend','ms: median [min, max]']]
    for r in sim['records']:
        rows.append([fmt(r['paths'])+r' $\times$ '+fmt(r['steps']),r['backend'],ms_cell(r)])
    table('simulation-ranges.tex','l lr',rows)
    for backend in backends:
        lines=['updates median_ms lower_ms upper_ms']
        for r in sim['records']:
            if r['backend']==backend and r['status']=='measured':
                values=r['samples_ms'];median=statistics.median(values)
                lines.append(f"{r['updates']} {median:.12g} {median-min(values):.12g} {max(values)-median:.12g}")
        (OUT/('simulation-'+backend+'.dat')).write_text('\n'.join(lines)+'\n')


def derive(data):
    MACROS.clear();OUT.mkdir(parents=True,exist_ok=True)
    derive_compute(data)
    write_compute_reports(data)
    for prefix,count in [('Ordinary',30),('Prepared',900),('Registration',9),('Comparison',900),('Scaling',50)]:
        macro(prefix+'Samples',count,prefix.lower()+' measured samples per program/mode/operation','samples')
    macro('CpuGovernor','performance','Linux CPU scaling governor and EPP on all 16 CPUs','text')
    macro('CpuClockGHz',3.6,'Nominal base clock; endpoint frequencies retained in raw metadata','GHz')
    macro('TurboSetting','disabled','Intel turbo disabled (no_turbo=1)','text')
    macro('SessionCount',3,'Independent sessions per E1/E2/E3 condition (E5 uses one)','sessions')
    for name, records, field in [
        ('OrdinarySessionSamples',data['ordinary']['records'],'samples'),
        ('PreparedBatchCalls',data['prepared']['records'],'samples'),
        ('RegistrationSessionSamples',data['prepared']['records'],'registrations')]:
        macro(name,len(records[0]['sessions'][0][field]),'Observations per independent session','samples')
    macro('ThroughputBlockCalls',30,'Consecutive measured calls per active-throughput block','calls')
    macro('ThroughputBlocks',len(data['prepared']['records'][0]['samples'])//30,'Pooled active-throughput blocks, formed within sessions','blocks')
    macro('ScalingSessionCount',data['scaling']['session_count'],'Independent E5 sessions','sessions')
    ordinary={r['program']:summary(r['samples']) for r in data['ordinary']['records']}
    table('ordinary-table.tex','lrr', [['Program','Seconds: median [Q1, Q3]','n']]+[[PROGRAMS[p],cell(s,1e9),s['n']] for p,s in ordinary.items()])
    for p,s in ordinary.items():metric('Ordinary'+PROGRAMS[p],s,'Seconds',1e9,p+' ordinary round-trip latency')
    rows=[['Program / storage','Preparation s','Call ms: median [Q1, Q3]']]
    rates=[['Program / mode','Active calls/s [Q1, Q3]','Blocks','Closed-loop calls/s']]
    registration_phases=[['Program / mode','Checking s','C generation/build s']]
    for r in data['prepared']['records']:
        p=r['program'];mode='Persistent' if r['persistent'] else 'Volatile';s=summary(r['samples']);reg=summary(r['registrations'])
        prefix=PROGRAMS[p]+mode
        metric('Prepared'+prefix,s,'Ms',1e6,p+' '+mode.lower()+' prepared latency')
        metric('Registration'+prefix,reg,'Seconds',1e9,p+' '+mode.lower()+' one-time registration')
        rps=statistics.median([300e9/x['batch_elapsed_ns'] for x in r['sessions']])
        macro('Prepared'+prefix+'CallsPerSecond',rps,'Closed-loop throughput, including checked voucher retirements when applicable','calls/s')
        active=active_throughput(r)
        macro('Prepared'+prefix+'ActiveCallsPerSecond',active['median'],'Median active throughput in thirty 30-call blocks, ten per session; excludes maintenance and validation gaps','calls/s')
        rates.append([PROGRAMS[p]+' / '+('Durable' if r['persistent'] else 'Volatile'),cell(active,1),30,f'{rps:.2f}'])
        if not r['persistent']:
            breakeven=math.ceil(reg['median']/(ordinary[p]['median']-s['median']))
            macro('BreakEven'+PROGRAMS[p]+'Calls',breakeven,'First integer call count where median registration plus prepared calls costs no more than ordinary calls','calls')
        rows.append([PROGRAMS[p]+' / '+('Durable' if r['persistent'] else 'Volatile'),decimal(reg['median']/1e9),cell(s)])
        checks=summary([dict(elapsed_ns=x['phases_ns']['primary_check']+x['phases_ns']['bendtt_translate_check']) for x in r['registrations']])
        compile_times=summary([dict(elapsed_ns=x['phases_ns']['c_emission']+x['phases_ns']['c_compilation']) for x in r['registrations']])
        macro('Registration'+PROGRAMS[p]+mode+'CheckingSeconds',checks['median']/1e9,'Preparation whole-Book checking median','s')
        macro('Registration'+PROGRAMS[p]+mode+'CompilationSeconds',compile_times['median']/1e9,'Preparation C emission/build median at -O2','s')
        registration_phases.append([PROGRAMS[p]+' / '+('Durable' if r['persistent'] else 'Volatile'),cell(checks,1e9),cell(compile_times,1e9)])
    for group in ('Checking','Compilation'):
        values=[MACROS['Registration'+PROGRAMS[r['program']]+('Persistent' if r['persistent'] else 'Volatile')+group+'Seconds'][0] for r in data['prepared']['records']]
        for bound,fn in [('Min',min),('Max',max)]:
            macro('Registration'+group+bound+'Seconds',fn(values),'Range of preparation phase medians across programs/storage modes','s')
    table('prepared-table.tex','lrr',rows)
    table('throughput-table.tex','lrrr',rates)
    table('registration-phase-table.tex','lrr',registration_phases)
    macro('OrdinaryMedianSeconds',ordinary['read']['median']/1e9,'Trivial point read ordinary median','s')
    macro('PreparedMedianMs',MACROS['PreparedReadVolatileMedianMs'][0],'Trivial point read volatile prepared median','ms')
    macro('BreakEvenCalls',MACROS['BreakEvenReadCalls'][0],'Trivial point read volatile preparation break-even','calls')
    phase_rows=[['Program','Phase','Milliseconds: median [Q1, Q3]']]
    for r in data['ordinary']['records']:
        for phase in sorted(r['samples'][0]['phases_ns']):
            s=summary([dict(elapsed_ns=x['phases_ns'][phase]) for x in r['samples']])
            phase_rows.append([PROGRAMS[r['program']],phase.replace('_',r'\_'),cell(s)])
    table('phase-table.tex','llr',phase_rows)
    # Aggregate within each call before summarizing; admission_total is nested.
    phase_summary=[['Phase (s)']+list(PROGRAMS.values())]
    phase_cells={}
    for r in data['ordinary']['records']:
        groups={
            'AdmissionSeconds':('admission_total',),
            'CheckingSeconds':('primary_check','bendtt_translate_check'),
            'CompilationSeconds':('c_emission','c_compilation'),
            'WorkerMs':('ordinary_worker',),
        }
        values={name:[sum(s['phases_ns'][p] for p in phases) for s in r['samples']]
            for name,phases in groups.items()}
        # The BendTT and native-build diagnostics overlap inside admission_total.
        values['OtherSeconds']=[s['elapsed_ns']-values['AdmissionSeconds'][i]-values['WorkerMs'][i]
            for i,s in enumerate(r['samples'])]
        for name,ns in values.items():
            macro('Ordinary'+PROGRAMS[r['program']]+name,statistics.median(ns)/(1e6 if name=='WorkerMs' else 1e9),
                r['program']+' ordinary '+name+' (checking/build overlap inside admission; other = round trip minus admission and worker)',
                'ms' if name=='WorkerMs' else 's')
        macro('Ordinary'+PROGRAMS[r['program']]+'WorkerSharePercent',
            statistics.median([100*s['phases_ns']['ordinary_worker']/s['elapsed_ns'] for s in r['samples']]),
            r['program']+' median per-call worker share of ordinary round trip','percent')
        phase_cells[r['program']]={name:cell(quartiles(ns),1e9,3)
            for name,ns in values.items()}
    for name,label in [('AdmissionSeconds','Admission wall'),('CheckingSeconds','Checking'),('CompilationSeconds','C generation/build'),
            ('WorkerMs','Worker'),('OtherSeconds','Other')]:
        phase_summary.append([label]+[phase_cells[p][name] for p in PROGRAMS])
    table('ordinary-phase-summary.tex','lrrr',phase_summary)
    compare=[['Rows / profile','Engine','Read ms','Update ms']]
    for r in data['comparison']['records']:
        prefix={'jaydb2':'Jay','postgresql':'Postgres','sqlite':'Sqlite'}[r['engine']]+('Owner' if r['policy']=='owner' else 'Point')
        summaries={w:samples(r,900,w) for w in ('read','update')}
        if r['rows']==10:
            for w,s in summaries.items():metric(prefix+w.title(),s,'Ms',1e6,r['engine']+' '+r['policy']+' '+w+' latency')
        else:
            for w,ss in summaries.items():macro('Large'+('Owner' if r['policy']=='owner' else '')+{'jaydb2':'Jay','postgresql':'Pg','sqlite':'Sq'}[r['engine']]+('Read' if w=='read' else 'Write')+'Ms',ss['median']/1e6,'Large-state durable '+r['engine']+' '+r['policy']+' '+w+' median','ms')
        compare.append([fmt(r['rows'])+' / '+r['policy'].title(),{'jaydb2':'JayDB2','postgresql':'PostgreSQL','sqlite':'SQLite'}[r['engine']],cell(summaries['read'],1e6,3),cell(summaries['update'],1e6,3)])
        if r['engine']=='jaydb2' and r['rows']==10:
            for w in ('read','update'):
                s=summary([x for x in r['ordinary'] if x['workload']==w and x['phase']=='sample'])
                metric('Ordinary'+prefix+w.title(),s,'Seconds',1e9,'Durable ordinary '+r['policy']+' '+w+' latency')
    macro('ComparisonOwnerRowsPerUser',data['comparison']['large_rows']//2,'Rows per user in the even large ownership split','rows')
    for workload,op in [('Read','Read'),('Update','Write')]:
        for baseline,engine in [('Postgres','Pg'),('Sqlite','Sq')]:
            macro('LargeJay'+workload+'Over'+baseline,
                MACROS['LargeJay'+op+'Ms'][0]/MACROS['Large'+engine+op+'Ms'][0],
                'Large-state durable point JayDB2 / '+baseline+' median','ratio')
    owner=next(r for r in data['comparison']['records'] if r['rows']==data['comparison']['large_rows'] and r['engine']=='jaydb2' and r['policy']=='owner')
    macro('LargeOwnerJayUpdateQthreeMs',samples(owner,900,'update')['qthree']/1e6,'Large owner update pooled upper quartile','ms')
    session_medians=[samples(z,300,'update')['median']/1e6 for z in owner['sessions']]
    for bound,fn in [('Min',min),('Max',max)]:
        macro('LargeOwnerJayUpdateSession'+bound+'Ms',fn(session_medians),'Large owner update session-median spread','ms')
    macro('ComparisonLargeRows',data['comparison']['large_rows'],'Total rows shared by all engines in the large-state comparison','rows')
    table('database-comparison-table.tex','llrr',compare)
    for policy in ('Point','Owner'):
        for workload in ('Read','Update'):
            for baseline in ('Postgres','Sqlite'):
                macro('Jay'+policy+workload+'Over'+baseline,
                    MACROS['Jay'+policy+workload+'MedianMs'][0]/MACROS[baseline+policy+workload+'MedianMs'][0],
                    'Ratio of durable prepared JayDB2 to '+baseline+' '+policy.lower()+' '+workload.lower()+' medians','ratio')
    v=data['verification']
    for r in v['commands']:
        name={'make verify-contract':'VerifyContract','make verify':'Verify','make test':'Test'}[r['command']]
        macro(name+'Seconds',r['elapsed_ns']/1e9,r['command']+' wall time','s')
        macro(name+'ExitCode',r['returncode'],r['command']+' exit status','exit code')
    for key,name in [('negative_fixtures','NegativeFixtures'),('theorem_types','ContractTheoremTypes'),('proof_law_declarations','ProofLawDeclarations'),('proof_definitions','ProofDefinitions')]:
        macro(name,v[key],key.replace('_',' '),'count')
    macro('ProofTheoremWitnesses',len(v['theorem_witnesses']),'Named top-level theorem witnesses (names ending theorem); excludes supporting lemmas','witnesses')
    wire_witnesses=re.findall(r'^def \w+\(\) -> C\.(\w+)\(\):',
        (ROOT/'proof/WireTheorems.bend').read_text(),re.MULTILINE)
    macro('PublicTheoremWitnesses',len(v['theorem_witnesses'])+len(wire_witnesses),
        'Named top-level theorem witnesses plus the separately named codec/framing witnesses','witnesses')
    for area,s in v['sizes'].items():macro(area.title()+'NonblankLines',s['nonblank_lines'],area+' source nonblank lines (comments included)','lines')
    macro('ProofToImplementationRatio',v['sizes']['proof']['nonblank_lines']/v['sizes']['src']['nonblank_lines'],
        'Nonblank proof/ lines divided by src/ implementation lines, including comments','ratio')
    coverage=re.search(r'OK import coverage: ([^\n]+)',v['commands'][1]['output'])
    if coverage:
        for area,count in re.findall(r'(\w+) (\d+) modules',coverage.group(1)):macro(area.title()+'CoverageModules',int(count),area+' modules covered by verify import roots','modules')
    table('verification-table.tex','lrr',[['Command','Seconds','Exit']]+[[r['command'],f"{r['elapsed_ns']/1e9:.2f}",r['returncode']] for r in v['commands']])
    inventory=[]
    for name,label,directory in [('Library','Library',ROOT/'library'),('VoucherSuite','Voucher proof suite',ROOT/'applications/vouchers/proof')]:
        counts=source_inventory(directory)
        macro(name+'Files',counts['files'],label+' maintained Bend files','files')
        macro(name+'NonblankLines',counts['nonblank_lines'],label+' nonblank Bend lines, including comments','lines')
        inventory.append([label,counts['files'],counts['nonblank_lines']])
    rls=v['detailed_sizes']['applications']['rls']
    inventory.extend([['RLS client program',len(rls['program_files']),rls['client_lines']],
        ['RLS client certificate/termination',len(rls['proof_files']),rls['proof_lines']]])
    table('size-table.tex','lrr',[['Area','Files','Nonblank lines']]+[[a.title(),s['files'],s['nonblank_lines']] for a,s in v['sizes'].items()]+inventory)
    scaling=data['scaling'];macro('StateLimitBytes',scaling['state_limit'],'Configured canonical state ceiling','bytes');macro('StateMaximumRows',scaling['max_rows'],'Largest analytically fitting population of this row shape','rows')
    macro('LargeSeedFuelFailures',sum('Seed.initial_valid' in r['reason'] and 'out of fuel' in r['reason'] for r in data['scaling-seed-attempt']['failures']),'Retained large direct-seed initialization attempts exhausted official BendTT fuel','attempts')
    populations=sorted({r['rows'] for r in scaling['records']})
    for name,count in [('Small',10),('Middle',100),('Large',1000)]:
        macro('Scaling'+name+'Rows',count,'Measured '+name.lower()+' scaling population','rows')
    largest=next(r for r in scaling['records'] if r['rows']==scaling['max_rows'])
    macro('StateMaximumBytes',largest['state_bytes'],'Canonical bytes at the largest fitting measured population','bytes')
    excess=min(scaling['failures'],key=lambda r:r['rows'])
    for name,key in [('StateFirstExcessRows','rows'),('StateFirstExcessBytes','state_bytes')]:
        macro(name,excess[key],'First population above the configured ceiling: '+key.replace('_',' '),key)
    oversized=max(scaling['failures'],key=lambda r:r['rows'])
    macro('StateOversizedRows',oversized['rows'],'Requested oversized population, not timed','rows')
    macro('StateOversizedBytes',oversized['state_bytes'],'Canonical bytes required by oversized population, not timed','bytes')
    macro('StateOversizedKilobytes',oversized['state_bytes']/1000,'Decimal kilobytes required by oversized population','kB')
    rows=[['Rows','State bytes','Mode','Read ms','Update ms']];coordinates={}
    for r in scaling['records']:
        ss={w:samples(r,50,w) for w in ('read','update')}
        rows.append([r['rows'],r['state_bytes'],'Durable' if r['persistent'] else 'Volatile',cell(ss['read']),cell(ss['update'])])
        for w,s in ss.items():
            mode='Persistent' if r['persistent'] else 'Volatile'
            if r['rows']==populations[0] or r['rows']==scaling['max_rows']:
                size='Small' if r['rows']==populations[0] else 'Maximum'
                metric('Scaling'+size+mode+w.title(),s,'Ms',1e6,'Scaling '+size.lower()+' '+mode.lower()+' '+w+' latency')
            coordinates.setdefault(mode.lower()+'_'+w,[]).append((r['rows'],r['state_bytes'],s))
    table('scaling-table.tex','rrlrr',rows)
    (OUT/'scaling-coordinates.tex').write_text('\n'.join(
        '\\newcommand{\\Scaling'+''.join(part.title() for part in name.split('_'))+'Coordinates}{'+
        ' '.join(f"({b/1000:.8g},{s['median']/1e6:.8g})" for _,b,s in points)+'}'
        for name,points in coordinates.items())+'\n')
    for name,xy in coordinates.items():
        (OUT/('scaling-'+name+'.dat')).write_text('rows state_bytes median_ms lower_ms upper_ms\n'+''.join(
            f"{x} {b} {s['median']/1e6:.8g} {(s['median']-s['qone'])/1e6:.8g} {(s['qthree']-s['median'])/1e6:.8g}\n"
            for x,b,s in xy))
    sizes=v['detailed_sizes']
    for name,key in [('RustProductionLines','rust_production_lines'),('RustTestLines','rust_test_lines')]:
        macro(name,sizes[key],sizes['definition'],'lines')
    for app,label in [('indexed','Indexed'),('voucher','Voucher'),('rls','Rls')]:
        a=sizes['applications'][app]
        macro(label+'ClientLines',a['client_lines'],'Nonblank client program lines; see detailed file inventory','lines')
        macro(label+'ProofLines',a['proof_lines'],'Nonblank client certificate and local proof helper lines; see inventory','lines')
        macro(label+'ProofRatio',a['proof_lines']/a['client_lines'],'Local client proof lines / client program lines','ratio')
    rls=v['rls_validation']
    macro('RlsNegativeFixtures',rls['negative_fixtures'],'RLS causal negatives checked in both official modes','fixtures')
    macro('RlsNativeResponses',rls['native_responses'],'Exactly checked responses in the complete native RLS session','responses')
    macro('HostDutyCount',v['host_duty_count'],'Numbered T3 host obligations in proof/README.md; regrouping does not reduce trust','duties')
    for size,label in [(populations[0],'Small'),(scaling['max_rows'],'Large')]:
        r=next(r for r in scaling['records'] if r['rows']==size and not r['persistent'])
        macro('ScalingFirstKey'+label+'Ms',summary(r['first_key_samples'])['median']/1e6,'Volatile first-key read median at '+label.lower()+' population','ms')
    points=coordinates['volatile_read']
    fit=statistics.linear_regression([x for x,_,_ in points],
        [s['median']/1e3 for _,_,s in points])
    macro('ScalingVolatileReadInterceptMs',fit.intercept/1000,
        'Intercept of the same least-squares volatile last-key read fit','ms')
    macro('ScalingVolatileReadSlopeUsPerRow',fit.slope,
        'Least-squares slope of volatile last-key read medians against row count','microseconds/row')
    indexed=next(r for r in data['prepared']['records'] if r['program']=='indexed' and r['persistent'])
    medians=[summary(z['samples'])['median']/1e6 for z in indexed['sessions']]
    macro('PreparedIndexedPersistentSessionMinMs',min(medians),'Minimum durable indexed session median','ms')
    macro('PreparedIndexedPersistentSessionMaxMs',max(medians),'Maximum durable indexed session median','ms')
    registration_rows=[['Program / storage','Min s','Median s','Max s','Session medians s','n']]
    for r in data['prepared']['records']:
        values=[x['elapsed_ns']/1e9 for x in r['registrations']]
        session_medians=[statistics.median(x['elapsed_ns'] for x in z['registrations'])/1e9 for z in r['sessions']]
        registration_rows.append([PROGRAMS[r['program']]+' / '+('Durable' if r['persistent'] else 'Volatile'),f'{min(values):.2f}',f'{statistics.median(values):.2f}',f'{max(values):.2f}',decimal(min(session_medians))+'--'+decimal(max(session_medians)),len(values)])
    table('registration-table.tex','lrrrrr',registration_rows)
    headline=report_rows(data)
    # Keep the article's repeatability table readable; full quartiles and all
    # SQL/throughput/E5 ranges remain in the complete machine-readable report.
    selected=[r for r in headline if r['unit']=='ms' and
        (r['metric'].startswith(('E1 ', 'E2 ')) or
         (r['metric'].startswith('E3 ') and 'JayDB2' in r['metric']))]
    table('session-spread-table.tex','lrrr',
        [['Condition (ms)','Pooled median','Session median min--max','n']]+[
        [r['metric'].replace('JayDB2 ', '').replace('/ volatile', '/ Volatile').replace('/ durable', '/ Durable').replace(',', '{,}'),
         decimal(r['stats']['median']/1e6,3),
         decimal(min(r['session_medians'])/1e6,3)+'--'+decimal(max(r['session_medians'])/1e6,3),r['stats']['n']]
        for r in selected])
    report=dict(measurement_metadata={name:data[name]['metadata'] for name in ('ordinary','prepared','comparison','scaling','verification','gpu-programs','simulation')},registration=[dict(program=r['program'],persistent=r['persistent'],n=len(r['registrations']),min_ns=min(x['elapsed_ns'] for x in r['registrations']),median_ns=statistics.median(x['elapsed_ns'] for x in r['registrations']),max_ns=max(x['elapsed_ns'] for x in r['registrations']),session_medians_ns=[statistics.median(x['elapsed_ns'] for x in z['registrations']) for z in r['sessions']]) for r in data['prepared']['records']],protocol=dict(sessions=3,scaling_sessions=1,governor='performance',epp='performance',no_turbo=1,nominal_ghz=3.6),headline=headline)
    report['compute']=dict(simulation=dict(settings=data['simulation']['settings'],preparations=data['simulation']['preparations'],records=data['simulation']['records']),gpu=dict(runs=data['gpu-programs']['runs']))
    (OUT/'final-summary.json').write_text(json.dumps(report,indent=2)+'\n')
    markdown=['| Metric | Unit | Pooled median [Q1, Q3] | Session median min–max | n |','|---|---|---|---|---|']
    for r in headline:
        v=r['stats'];k=r['scale']
        markdown.append(f"| {r['metric']} | {r['unit']} | {v['median']/k:,.3f} [{v['qone']/k:,.3f}, {v['qthree']/k:,.3f}] | {min(r['session_medians'])/k:,.3f}–{max(r['session_medians'])/k:,.3f} | {v['n']} |")
    compute_headline=['','## E6 complete-request/query medians (ms)','','Ranges are in simulation.md; timeouts are observed cancellations.','',*(OUT/'simulation-rendered.md').read_text().splitlines()]
    (OUT/'final-headlines.md').write_text('\n'.join(markdown+compute_headline)+'\n')
    v=data['verification']
    details=['# Final controlled JayDB2 thesis evidence',
        '', 'Branch: `'+data['scaling']['metadata']['branch']+'`. Engine source SHA-256: `'+data['scaling']['metadata']['source_sha256']+'`; executable SHA-256: `'+data['scaling']['metadata']['binary_sha256']+'`. Raw metadata retain each invocation commit; all refreshed E1–E6 datasets and the focused GPU benchmark must have identical engine fingerprints.',
        '', 'E1–E3: three fresh sessions per condition. E5: one session, one service per storage mode reused across all sizes. Governor/EPP performance; turbo disabled; nominal 3.6 GHz. No CPU pinning. Inclusive quartiles; no outlier removal.',
        '', 'E3 uses 10 and 1,104 total rows in all engines; owner rows are divided equally between Alice and Bob. SQLite is unconstrained. E4 commands were rerun under the same fixed-clock policy; each wall time is one observation.',
        '', 'All latency rows below use milliseconds. Session spread is min–max of session medians; E5 has only one session. Throughput rows use calls/s.', '',*markdown,
        '', '## Registration (nine observations per condition)', '', '| Program / storage | Min (s) | Median (s) | Max (s) | Session median min–max (s) | n |', '|---|---|---|---|---|---|']
    for r in data['prepared']['records']:
        ns=[x['elapsed_ns']/1e9 for x in r['registrations']]
        sm=[statistics.median(x['elapsed_ns'] for x in z['registrations'])/1e9 for z in r['sessions']]
        details.append(f"| {PROGRAMS[r['program']]} / {'durable' if r['persistent'] else 'volatile'} | {min(ns):.2f} | {statistics.median(ns):.2f} | {max(ns):.2f} | {min(sm):.2f}–{max(sm):.2f} | {len(ns)} |")
    details += ['', '## Ordinary phases', '', '| Program | Phase | Median [Q1,Q3] (ms) | n |', '|---|---|---|---|']
    for r in data['ordinary']['records']:
        for label,phases in [('Admission wall',('admission_total',)),('Checking (overlaps build)',('primary_check','bendtt_translate_check')),('C generation/build (overlaps checking)',('c_emission','c_compilation')),('Worker',('ordinary_worker',))]:
            ns=[sum(x['phases_ns'][p] for p in phases) for x in r['samples']]
            z=quartiles(ns)
            details.append(f"| {PROGRAMS[r['program']]} | {label} | {z['median']/1e6:,.2f} [{z['qone']/1e6:,.2f}, {z['qthree']/1e6:,.2f}] | {len(ns)} |")
    details += ['', '## Preparation break-even', '', '| Program | Calls |', '|---|---|']
    for p in PROGRAMS:details.append(f"| {PROGRAMS[p]} | {MACROS['BreakEven'+PROGRAMS[p]+'Calls'][0]} |")
    details += ['', '## E3 ordinary context (10 total rows)', '', '| Policy / operation | Median [Q1,Q3] (s) | n |', '|---|---|---|']
    for policy in ('point','owner'):
        r=next(r for r in data['comparison']['records'] if r['engine']=='jaydb2' and r['policy']==policy and r['rows']==10)
        for workload in ('read','update'):
            z=quartiles([x['elapsed_ns'] for x in r['ordinary'] if x['workload']==workload and x['phase']=='sample'])
            details.append(f"| {policy.title()} / {workload} | {z['median']/1e9:.3f} [{z['qone']/1e9:.3f}, {z['qthree']/1e9:.3f}] | {z['n']} |")
    details += ['', '## Fixed-clock verification times', '', '| Command | Seconds | n | Exit |', '|---|---|---|---|']
    for r in v['commands']:details.append(f"| {r['command']} | {r['elapsed_ns']/1e9:.3f} | 1 | {r['returncode']} |")
    details += ['', 'Quartiles and session spread are undefined for these single fixed-clock command observations. Checking and C generation/build diagnostics overlap inside admission wall time; they must not be added to it or to each other.', '', '## Verification inventory', '', '| Fact | Count |', '|---|---|']
    for name in ('NegativeFixtures','ContractTheoremTypes','ProofLawDeclarations','ProofDefinitions','ProofTheoremWitnesses','PublicTheoremWitnesses','RlsNegativeFixtures','RlsNativeResponses','HostDutyCount'):
        details.append(f"| {name} | {MACROS[name][0]:,} |")
    details += ['', 'The core and RLS negative-fixture counts are separate; every fixture is checked in both official modes. The eight numbered T3 items regroup the previous eleven obligations and do not imply reduced trust.', '', '## Source inventory', '', sizes['definition'], '', '| Area | Program / production lines | Proof / test lines | Proof/program ratio |', '|---|---|---|',f"| Rust host | {sizes['rust_production_lines']:,} | {sizes['rust_test_lines']:,} | — |"]
    for app in ('indexed','voucher','rls'):
        a=sizes['applications'][app]
        details.append(f"| {app.title()} | {a['client_lines']} | {a['proof_lines']} | {a['proof_lines']/a['client_lines']:.3f} |")
    details += ['', '| Source area | Files | Nonblank lines |', '|---|---|---|']
    for area,counts in v['sizes'].items():
        details.append(f"| {area.title()} | {counts['files']} | {counts['nonblank_lines']:,} |")
    names=['CpuGovernor','CpuClockGHz','TurboSetting','SessionCount','RustProductionLines','RustTestLines','IndexedClientLines','IndexedProofLines','IndexedProofRatio','VoucherClientLines','VoucherProofLines','VoucherProofRatio','RlsClientLines','RlsProofLines','RlsProofRatio','RlsNonblankLines','RlsNegativeFixtures','RlsNativeResponses','HostDutyCount','ComparisonLargeRows','ScalingFirstKeySmallMs','ScalingFirstKeyLargeMs']
    names += ['Large'+policy+engine+op+'Ms' for policy in ('','Owner') for engine in ('Jay','Pg','Sq') for op in ('Read','Write')]
    details += ['', '## New macro contract', '', '| Macro | Value | Unit |', '|---|---|---|']
    for name in names:
        value,_,unit=MACROS[name]
        details.append(f"| `\\{name}` | {value if isinstance(value,str) else format(value,',') if isinstance(value,int) else format(value,'.6g')} | {unit} |")
    small=next(r for r in scaling['records'] if r['rows']==10 and not r['persistent'])
    hundred=next(r for r in scaling['records'] if r['rows']==100 and not r['persistent'])
    low=summary([x for x in small['samples'] if x['workload']=='read'])['median']/1e6
    high=summary([x for x in hundred['samples'] if x['workload']=='read'])['median']/1e6
    details += ['', '## Observations and limits', '',f'Fixed-clock volatile last-key read is {low:.3f} ms at 10 rows and {high:.3f} ms at 100 rows ({high/low:.3f}×). Compare the earlier powersave measurements in performance-report.txt; the fresh data are not pooled with that historical run.']
    max_record=next(r for r in scaling['records'] if r['rows']==scaling['max_rows'] and not r['persistent'])
    first=summary(max_record['first_key_samples'])['median']/1e6
    last=summary([x for x in max_record['samples'] if x['workload']=='read'])['median']/1e6
    details += ['',f'At {scaling["max_rows"]:,} rows, volatile first-key read is {first:.3f} ms versus {last:.3f} ms for last-key read. Their similar costs show that lookup position does not account for most observed scaling. Complete-state transfer, decoding, validation and publication remain inside the timing boundary; this comparison does not isolate copying alone.']
    r=next(r for r in data['prepared']['records'] if r['program']=='indexed' and r['persistent'])
    totals=[statistics.median(x['elapsed_ns'] for x in z['samples'])/1e6 for z in r['sessions']]
    pubs=[statistics.median(x['phases_ns']['publication'] for x in z['samples'])/1e6 for z in r['sessions']]
    workers=[statistics.median(x['phases_ns']['prepared_worker'] for x in z['samples'])/1e6 for z in r['sessions']]
    details += ['', 'Durable Indexed session medians (ms): '+', '.join(f'{v:.3f}' for v in totals)+'. Publication phase medians: '+', '.join(f'{v:.3f}' for v in pubs)+'. Worker phase medians: '+', '.join(f'{v:.3f}' for v in workers)+'. The fixed policy does not eliminate publication variability; these observations do not isolate individual fsync calls. No slow session was removed.']
    details += ['', '## Run note', '', 'All E1–E6 datasets and the focused GPU benchmark were refreshed on the frozen opt-in GPU/simulation engine. E1–E3 retain three independent sessions; E5 retains its one-session scaling protocol. Complete command output and exact CPU restoration receipts are retained.']
    attempts=ROOT/'paper/evidence/validation-attempts.json'
    if attempts.exists():
        details += ['', 'Historical validation-attempts.json retains an earlier RLS diagnostic-counter failure and its output. That development record does not supply the current E4 timings; all three current commands were freshly executed on the frozen engine.']
    restoration=ROOT/'paper/evidence/cpu-restoration.json'
    if restoration.exists():
        restored=json.loads(restoration.read_text())
        details += ['', '## CPU restoration', '', 'Final observed values (all 16 CPUs): governor `powersave`; EPP `balance_performance`; `intel_pstate/no_turbo=0`. Exact saved settings and final sampled frequencies are in `cpu-restoration.json`. Verified: '+str(restored['verified'])+'.']
    details += ['', '## E6 certified simulation', '', *(OUT/'simulation.md').read_text().splitlines()[2:], '', '## Focused GPU benchmark', '', *(OUT/'gpu-programs.md').read_text().splitlines()[2:]]
    (OUT/'final-report.md').write_text('\n'.join(details)+'\n')
    # Beamer's existing pgf number helpers require plain numeric tokens. The
    # English article receives grouped integer text that also works in math.
    common=['\\newcommand{\\'+name+'}{'+fmt(value)+'}' for name,(value,_,_) in MACROS.items() if not isinstance(value,int)]
    raw=['\\newcommand{\\'+name+'}{'+str(value)+'}' for name,(value,_,_) in MACROS.items() if isinstance(value,int)]
    grouped=['\\newcommand{\\'+name+'}{'+fmt(value)+'}' for name,(value,_,_) in MACROS.items() if isinstance(value,int)]
    (OUT/'numbers.tex').write_text('\n'.join(common+[
        r'\makeatletter',r'\@ifclassloaded{beamer}{%']+raw+['}{%']+grouped+['}',r'\makeatother'])+'\n')
    (OUT/'macro-reference.md').write_text('| Macro | Meaning | Unit |\n|---|---|---|\n'+''.join(f'| `\\{n}` | {m} | {u} |\n' for n,(_,m,u) in MACROS.items()))
    return MACROS


def report_rows(data):
    rows=[]
    def add(metric,groups,scale=1e6,unit='ms'):
        values=[x for g in groups for x in g]
        rows.append(dict(metric=metric,stats=quartiles(values),session_medians=[statistics.median(g) for g in groups],scale=scale,unit=unit))
    for r in data['ordinary']['records']:
        add('E1 '+PROGRAMS[r['program']],[[x['elapsed_ns'] for x in z['samples']] for z in r['sessions']])
    for r in data['prepared']['records']:
        label='E2 '+PROGRAMS[r['program']]+' / '+('durable' if r['persistent'] else 'volatile')
        add(label,[[x['elapsed_ns'] for x in z['samples']] for z in r['sessions']])
        add(label+' active throughput',[[30e9/sum(x['elapsed_ns'] for x in z['samples'][i:i+30]) for i in range(0,300,30)] for z in r['sessions']],1,'calls/s')
        add(label+' closed-loop throughput',[[300e9/z['batch_elapsed_ns']] for z in r['sessions']],1,'calls/s')
    for r in data['comparison']['records']:
        for w in ('read','update'):
            add('E3 '+format(r['rows'],',')+' '+r['policy'].title()+' '+{'jaydb2':'JayDB2','postgresql':'PostgreSQL','sqlite':'SQLite'}[r['engine']]+' '+w.title(),[[x['elapsed_ns'] for x in z['samples'] if x['workload']==w] for z in r['sessions']])
    for r in data['scaling']['records']:
        label='E5 '+format(r['rows'],',')+' / '+('durable' if r['persistent'] else 'volatile')
        for w in ('read','update'):add(label+' '+w.title(),[[x['elapsed_ns'] for x in r['samples'] if x['workload']==w]])
        if r['first_key_samples']:add(label+' first-key Read',[[x['elapsed_ns'] for x in r['first_key_samples']]])
    return rows


def main():
    data=load();derive(data)
    for name in ('final-summary.json','final-headlines.md','final-report.md','gpu-programs.md','simulation.md'):
        (ROOT/'paper/evidence'/name).write_text((OUT/name).read_text())
    print(f'Validated {len(FILES)} evidence files; generated {len(MACROS)} macros and tables in {OUT}')

if __name__=='__main__':main()
