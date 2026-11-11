#!/usr/bin/env python3
"""Validate fresh checked samples and derive LaTeX/plot data (no benchmarks)."""
import json
import math
from pathlib import Path
import re
import statistics

ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'.build/tcc'
FILES=('ordinary','prepared','comparison','verification','scaling','scaling-seed-attempt')
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
        if len({data[name]['metadata'][key] for name in ('ordinary','prepared','comparison','scaling')})!=1:
            raise ValueError('Mixed engine fingerprints: '+key)
    if {r['program'] for r in data['ordinary']['records']}!=set(PROGRAMS) or len(data['ordinary']['records'])!=3:
        raise ValueError('Ordinary program coverage')
    for r in data['ordinary']['records']:
        samples(r,30)
        phases={'staging','primary_check','bendtt_translate_check','c_compilation','ordinary_worker','publication'}
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
    validate_frequency(data['verification'].get('size_collection_metadata',data['verification']['metadata']))
    commands=data['verification']['commands']
    if {r['command'] for r in commands}!={'make verify-contract','make verify','make test'}:raise ValueError('Missing verification run')
    for row in commands:
        if not row.get('output') or row['elapsed_ns']<=0:raise ValueError('Missing verification output')
        if row['returncode']!=0:raise ValueError('Required verification gate failed; inspect retained output')
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


def derive(data):
    MACROS.clear();OUT.mkdir(parents=True,exist_ok=True)
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
            'CheckingSeconds':('primary_check','bendtt_translate_check'),
            'CompilationSeconds':('c_emission','c_compilation'),
            'WorkerMs':('ordinary_worker',),
        }
        values={name:[sum(s['phases_ns'][p] for p in phases) for s in r['samples']]
            for name,phases in groups.items()}
        values['OtherSeconds']=[s['elapsed_ns']-sum(values[name][i] for name in groups)
            for i,s in enumerate(r['samples'])]
        for name,ns in values.items():
            macro('Ordinary'+PROGRAMS[r['program']]+name,statistics.median(ns)/(1e6 if name=='WorkerMs' else 1e9),
                r['program']+' ordinary '+name+' (other = round trip minus checking, C generation/build and worker)',
                'ms' if name=='WorkerMs' else 's')
        macro('Ordinary'+PROGRAMS[r['program']]+'WorkerSharePercent',
            statistics.median([100*s['phases_ns']['ordinary_worker']/s['elapsed_ns'] for s in r['samples']]),
            r['program']+' median per-call worker share of ordinary round trip','percent')
        phase_cells[r['program']]={name:cell(quartiles(ns),1e9,3)
            for name,ns in values.items()}
    for name,label in [('CheckingSeconds','Checking'),('CompilationSeconds','C generation/build'),
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
    for app,label in [('indexed','Indexed'),('voucher','Voucher')]:
        a=sizes['applications'][app]
        macro(label+'ClientLines',a['client_lines'],'Nonblank client program lines; see detailed file inventory','lines')
        macro(label+'ProofLines',a['proof_lines'],'Nonblank client certificate and local proof helper lines; see inventory','lines')
        macro(label+'ProofRatio',a['proof_lines']/a['client_lines'],'Local client proof lines / client program lines','ratio')
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
    report=dict(measurement_metadata={name:data[name]['metadata'] for name in ('ordinary','prepared','comparison','scaling')},registration=[dict(program=r['program'],persistent=r['persistent'],n=len(r['registrations']),min_ns=min(x['elapsed_ns'] for x in r['registrations']),median_ns=statistics.median(x['elapsed_ns'] for x in r['registrations']),max_ns=max(x['elapsed_ns'] for x in r['registrations']),session_medians_ns=[statistics.median(x['elapsed_ns'] for x in z['registrations']) for z in r['sessions']]) for r in data['prepared']['records']],protocol=dict(sessions=3,scaling_sessions=1,governor='performance',epp='performance',no_turbo=1,nominal_ghz=3.6),headline=headline)
    (OUT/'final-summary.json').write_text(json.dumps(report,indent=2)+'\n')
    markdown=['| Metric | Unit | Pooled median [Q1, Q3] | Session median min–max | n |','|---|---|---|---|---|']
    for r in headline:
        v=r['stats'];k=r['scale']
        markdown.append(f"| {r['metric']} | {r['unit']} | {v['median']/k:,.3f} [{v['qone']/k:,.3f}, {v['qthree']/k:,.3f}] | {min(r['session_medians'])/k:,.3f}–{max(r['session_medians'])/k:,.3f} | {v['n']} |")
    (OUT/'final-headlines.md').write_text('\n'.join(markdown)+'\n')
    v=data['verification']
    details=['# Final controlled JayDB2 thesis evidence',
        '', 'Branch: `'+data['scaling']['metadata']['branch']+'`. Engine source SHA-256: `'+data['scaling']['metadata']['source_sha256']+'`; executable SHA-256: `'+data['scaling']['metadata']['binary_sha256']+'`. Raw metadata retain each invocation commit; all four new latency datasets must have identical engine fingerprints.',
        '', 'E1–E3: three fresh sessions per condition. E5: one session, one service per storage mode reused across all sizes. Governor/EPP performance; turbo disabled; nominal 3.6 GHz. No CPU pinning. Inclusive quartiles; no outlier removal.',
        '', 'E3 uses 10 and 1,104 total rows in all engines; owner rows are divided equally between Alice and Bob. SQLite is unconstrained. E4 wall times are retained historical successful runs under powersave/turbo; only source sizes were collected anew.',
        '', 'All latency rows below use milliseconds. Session spread is min–max of session medians; E5 has only one session. Throughput rows use calls/s.', '',*markdown,
        '', '## Registration (nine observations per condition)', '', '| Program / storage | Min (s) | Median (s) | Max (s) | Session median min–max (s) | n |', '|---|---|---|---|---|---|']
    for r in data['prepared']['records']:
        ns=[x['elapsed_ns']/1e9 for x in r['registrations']]
        sm=[statistics.median(x['elapsed_ns'] for x in z['registrations'])/1e9 for z in r['sessions']]
        details.append(f"| {PROGRAMS[r['program']]} / {'durable' if r['persistent'] else 'volatile'} | {min(ns):.2f} | {statistics.median(ns):.2f} | {max(ns):.2f} | {min(sm):.2f}–{max(sm):.2f} | {len(ns)} |")
    details += ['', '## Ordinary phases', '', '| Program | Phase | Median [Q1,Q3] (ms) | n |', '|---|---|---|---|']
    for r in data['ordinary']['records']:
        for label,phases in [('Checking',('primary_check','bendtt_translate_check')),('C generation/build',('c_emission','c_compilation')),('Worker',('ordinary_worker',))]:
            ns=[sum(x['phases_ns'][p] for p in phases) for x in r['samples']]
            z=quartiles(ns)
            details.append(f"| {PROGRAMS[r['program']]} | {label} | {z['median']/1e6:,.2f} [{z['qone']/1e6:,.2f}, {z['qthree']/1e6:,.2f}] | {len(ns)} |")
    details += ['', '## Preparation break-even', '', '| Program | Calls |', '|---|---|']
    for p in PROGRAMS:details.append(f"| {PROGRAMS[p]} | {MACROS['BreakEven'+PROGRAMS[p]+'Calls'][0]} |")
    details += ['', '## Retained verification times', '', '| Command | Seconds | n | Exit |', '|---|---|---|---|']
    for r in v['commands']:details.append(f"| {r['command']} | {r['elapsed_ns']/1e9:.3f} | 1 | {r['returncode']} |")
    details += ['', 'Quartiles and session spread are undefined for these single historical command observations.', '', '## Source inventory', '', sizes['definition'], '', '| Area | Program / production lines | Proof / test lines | Proof/program ratio |', '|---|---|---|---|',f"| Rust host | {sizes['rust_production_lines']:,} | {sizes['rust_test_lines']:,} | — |"]
    for app in ('indexed','voucher'):
        a=sizes['applications'][app]
        details.append(f"| {app.title()} | {a['client_lines']} | {a['proof_lines']} | {a['proof_lines']/a['client_lines']:.3f} |")
    names=['CpuGovernor','CpuClockGHz','TurboSetting','SessionCount','RustProductionLines','RustTestLines','IndexedClientLines','IndexedProofLines','IndexedProofRatio','VoucherClientLines','VoucherProofLines','VoucherProofRatio','ComparisonLargeRows','ScalingFirstKeySmallMs','ScalingFirstKeyLargeMs']
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
    details += ['', '## Run note', '', 'The E3/E5 measurement commands and both state-limit probes completed successfully. Their outer shell wrapper then exited 127 because its source was edited while Bash was executing it, causing Bash to read stray trailing text after the command returned. The EXIT trap restored and verified all original CPU settings. The finalized wrapper was subsequently checked with normal exit, failure, INT, TERM and HUP; no measured session was removed or replaced.']
    restoration=ROOT/'paper/evidence/cpu-restoration.json'
    if restoration.exists():
        restored=json.loads(restoration.read_text())
        details += ['', '## CPU restoration', '', 'Final observed values (all 16 CPUs): governor `powersave`; EPP `balance_performance`; `intel_pstate/no_turbo=0`. Exact saved settings and final sampled frequencies are in `cpu-restoration.json`. Verified: '+str(restored['verified'])+'.']
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
    for name in ('final-summary.json','final-headlines.md','final-report.md'):
        (ROOT/'paper/evidence'/name).write_text((OUT/name).read_text())
    print(f'Validated {len(FILES)} evidence files; generated {len(MACROS)} macros and tables in {OUT}')

if __name__=='__main__':main()
