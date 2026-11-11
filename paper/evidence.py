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
    return quartiles([30e9/sum(s['elapsed_ns'] for s in rows[i:i+30]) for i in range(0,300,30)])


def checked(sample):
    if sample.get('checked') is not True or canonical(sample.get('actual'))!=canonical(sample.get('expected')):
        raise ValueError('Unchecked or incorrect output')
    if type(sample.get('elapsed_ns')) is not int or sample['elapsed_ns']<=0:
        raise ValueError('Invalid elapsed nanoseconds')


def samples(record,n,workload=None):
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
    if {r['program'] for r in data['ordinary']['records']}!=set(PROGRAMS) or len(data['ordinary']['records'])!=3:
        raise ValueError('Ordinary program coverage')
    for r in data['ordinary']['records']:
        samples(r,10)
        phases={'staging','primary_check','bendtt_translate_check','c_compilation','ordinary_worker','publication'}
        if any(not phases<=s['phases_ns'].keys() for s in r['samples']): raise ValueError('Missing ordinary phase timing')
    expected={(p,m) for p in PROGRAMS for m in (False,True)}
    identities=[(r['program'],r['persistent']) for r in data['prepared']['records']]
    if len(identities)!=6 or set(identities)!=expected:raise ValueError('Prepared program/mode coverage')
    for r in data['prepared']['records']:
        samples(r,300)
        if len(r['registrations'])<3:raise ValueError('Missing registration samples')
        for row in r['registrations']:
            checked(row)
            if row['actual'].get('status')!='prepared' or not re.fullmatch('[a-f0-9]{64}',row['actual'].get('value','')):
                raise ValueError('Invalid prepared receipt')
        if r['program']=='voucher' and any(s.get('untimed_retirement_checked') is not True for s in r['samples']):
            raise ValueError('Unchecked voucher retirement')
    comparisons=data['comparison']['records']
    if len(comparisons)!=6 or {(r['engine'],r['policy']) for r in comparisons}!={(e,p) for e in ('jaydb2','postgresql','sqlite') for p in ('point','owner')}:
        raise ValueError('Comparison engine/policy coverage')
    for r in comparisons:
        for workload in ('read','update'):samples(r,300,workload)
        if r['engine']=='jaydb2':
            for s in r['samples']:
                if s['workload']=='update' and s.get('stored_value_checked') is not True:raise ValueError('Unchecked stored update')
            for w in ('read','update'):
                rows=[s for s in r['ordinary'] if s['workload']==w and s['phase']=='sample']
                if len(rows)!=10:raise ValueError('Ordinary comparison context samples')
                for row in rows:checked(row)
    policy=data['comparison']['policy_checks']
    if len(policy)!=4 or {(r['engine'],r['workload']) for r in policy}!={(e,w) for e in ('jaydb2','postgresql') for w in ('read','update')}:
        raise ValueError('Missing policy refusal checks')
    for row in policy:
        if row.get('refused') is not True or row.get('checked') is not True or canonical(row['actual'])!=canonical(row['expected']):raise ValueError('Policy check failed')
    pg=data['comparison']['settings']['postgresql']
    if pg['fsync']!='on' or pg['synchronous_commit']!='on' or pg['role'][1:]!=[False,False] or pg['rls']!=[True,True]:
        raise ValueError('PostgreSQL durability/RLS settings')
    sq=data['comparison']['settings']['sqlite']
    if sq['synchronous']!=2 or sq['journal_mode']!='wal':raise ValueError('SQLite durability settings')
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
    expected={(n,m) for n in (10,100,1000,scaling['max_rows']) for m in (False,True)}
    attempts=set(identities)|{(r['rows'],r['persistent']) for r in scaling['failures'] if 'persistent' in r}
    if not expected<=attempts:raise ValueError('Missing scaling population/mode coverage')
    for r in scaling['records']:
        checked(r['population'])
        if r['population']['actual']!={'status':'success','value':r['rows']}:raise ValueError('Scaling population count disagrees')
        if r['state_bytes']>scaling['state_limit']:raise ValueError('Scaling state exceeds limit')
        for w in ('read','update'):samples(r,50,w)
        for s in r['samples']:
            if s['workload']=='update' and s.get('stored_value_checked') is not True:raise ValueError('Unchecked scaling update')
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


def load():
    return validate({n:json.loads((ROOT/'paper/evidence'/f'{n}.json').read_text()) for n in FILES})


def macro(name,value,meaning,unit):
    if not re.fullmatch('[A-Z][a-zA-Z]*',name):raise ValueError(name)
    MACROS[name]=(value,meaning,unit)


def metric(prefix,s,unit,scale,meaning):
    macro(prefix+'Median'+unit,s['median']/scale,meaning+' median',unit)


def fmt(x):
    return str(x) if isinstance(x,int) else f'{x:.6g}'


def cell(s,scale=1e6):
    return f"{s['median']/scale:.4g} [{s['qone']/scale:.4g}, {s['qthree']/scale:.4g}]"


def table(name,columns,rows):
    rendered=[' & '.join(map(str,row))+r' \\' for row in rows]
    (OUT/name).write_text('\\begin{tabular}{'+columns+'}\\toprule\n'+rendered[0]+'\n\\midrule\n'+'\n'.join(rendered[1:])+'\n\\bottomrule\\end{tabular}\n')


def derive(data):
    MACROS.clear();OUT.mkdir(parents=True,exist_ok=True)
    for prefix,count in [('Ordinary',10),('Prepared',300),('Registration',3),('Comparison',300),('Scaling',50)]:
        macro(prefix+'Samples',count,prefix.lower()+' measured samples per program/mode/operation','samples')
    ordinary={r['program']:summary(r['samples']) for r in data['ordinary']['records']}
    table('ordinary-table.tex','lrr', [['Program','Seconds: median [Q1, Q3]','n']]+[[PROGRAMS[p],cell(s,1e9),s['n']] for p,s in ordinary.items()])
    for p,s in ordinary.items():metric('Ordinary'+PROGRAMS[p],s,'Seconds',1e9,p+' ordinary round-trip latency')
    rows=[['Program / mode','Registration s','Call ms']]
    rates=[['Program / mode','Active calls/s [Q1, Q3]','Blocks','Closed-loop calls/s']]
    registration_phases=[['Program / mode','Checking s','C generation/build s']]
    for r in data['prepared']['records']:
        p=r['program'];mode='Persistent' if r['persistent'] else 'Volatile';s=summary(r['samples']);reg=summary(r['registrations'])
        prefix=PROGRAMS[p]+mode
        metric('Prepared'+prefix,s,'Ms',1e6,p+' '+mode.lower()+' prepared latency')
        metric('Registration'+prefix,reg,'Seconds',1e9,p+' '+mode.lower()+' one-time registration')
        rps=300e9/r['batch_elapsed_ns']
        macro('Prepared'+prefix+'CallsPerSecond',rps,'Closed-loop throughput, including checked voucher retirements when applicable','calls/s')
        active=active_throughput(r)
        macro('Prepared'+prefix+'ActiveCallsPerSecond',active['median'],'Median active throughput in ten consecutive 30-call blocks; excludes maintenance and validation gaps','calls/s')
        rates.append([p+' / '+mode.lower(),cell(active,1),10,f'{rps:.4g}'])
        if not r['persistent']:
            breakeven=math.ceil(reg['median']/(ordinary[p]['median']-s['median']))
            macro('BreakEven'+PROGRAMS[p]+'Calls',breakeven,'First integer call count where median registration plus prepared calls costs no more than ordinary calls','calls')
        rows.append([p+' / '+mode.lower(),cell(reg,1e9),cell(s)])
        checks=summary([dict(elapsed_ns=x['phases_ns']['primary_check']+x['phases_ns']['bendtt_translate_check']) for x in r['registrations']])
        compile_times=summary([dict(elapsed_ns=x['phases_ns']['c_emission']+x['phases_ns']['c_compilation']) for x in r['registrations']])
        registration_phases.append([p+' / '+mode.lower(),cell(checks,1e9),cell(compile_times,1e9)])
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
            phase_rows.append([r['program'],phase.replace('_',r'\_'),cell(s)])
    table('phase-table.tex','llr',phase_rows)
    # Aggregate within each call before summarizing; admission_total is nested.
    phase_summary=[['Phase (unit)']+list(PROGRAMS.values())]
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
        phase_cells[r['program']]={name:cell(quartiles(ns),1e6 if name=='WorkerMs' else 1e9)
            for name,ns in values.items()}
    for name,label in [('CheckingSeconds','Checking (s)'),('CompilationSeconds','C generation/build (s)'),
            ('WorkerMs','Worker (ms)'),('OtherSeconds','Other (s)')]:
        phase_summary.append([label]+[phase_cells[p][name] for p in PROGRAMS])
    table('ordinary-phase-summary.tex','lrrr',phase_summary)
    compare=[['Policy','Engine','Read ms','Update ms']]
    for r in data['comparison']['records']:
        prefix={'jaydb2':'Jay','postgresql':'Postgres','sqlite':'Sqlite'}[r['engine']]+('Owner' if r['policy']=='owner' else 'Point')
        summaries={w:samples(r,300,w) for w in ('read','update')}
        for w,s in summaries.items():metric(prefix+w.title(),s,'Ms',1e6,r['engine']+' '+r['policy']+' '+w+' latency')
        compare.append([r['policy'],r['engine'],cell(summaries['read']),cell(summaries['update'])])
        if r['engine']=='jaydb2':
            for w in ('read','update'):
                s=summary([x for x in r['ordinary'] if x['workload']==w and x['phase']=='sample'])
                metric('Ordinary'+prefix+w.title(),s,'Seconds',1e9,'Durable ordinary '+r['policy']+' '+w+' latency')
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
    for area,s in v['sizes'].items():macro(area.title()+'NonblankLines',s['nonblank_lines'],area+' source nonblank lines (comments included)','lines')
    macro('ProofToImplementationRatio',v['sizes']['proof']['nonblank_lines']/v['sizes']['src']['nonblank_lines'],
        'Nonblank proof/ lines divided by src/ implementation lines, including comments','ratio')
    coverage=re.search(r'OK import coverage: ([^\n]+)',v['commands'][1]['output'])
    if coverage:
        for area,count in re.findall(r'(\w+) (\d+) modules',coverage.group(1)):macro(area.title()+'CoverageModules',int(count),area+' modules covered by verify import roots','modules')
    table('verification-table.tex','lrr',[['Command','Seconds','Exit']]+[[r['command'],f"{r['elapsed_ns']/1e9:.4g}",r['returncode']] for r in v['commands']])
    table('size-table.tex','lrr',[['Area','Files','Nonblank lines']]+[[a,s['files'],s['nonblank_lines']] for a,s in v['sizes'].items()])
    scaling=data['scaling'];macro('StateLimitBytes',scaling['state_limit'],'Configured canonical state ceiling','bytes');macro('StateMaximumRows',scaling['max_rows'],'Largest analytically fitting population of this row shape','rows')
    macro('LargeSeedFuelFailures',sum('Seed.initial_valid' in r['reason'] and 'out of fuel' in r['reason'] for r in data['scaling-seed-attempt']['failures']),'Retained large direct-seed initialization attempts exhausted official BendTT fuel','attempts')
    populations=sorted({r['rows'] for r in scaling['records']})
    for name,index in [('Small',0),('Middle',1),('Large',2)]:
        macro('Scaling'+name+'Rows',populations[index],'Measured '+name.lower()+' scaling population','rows')
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
        rows.append([r['rows'],r['state_bytes'],'persistent' if r['persistent'] else 'volatile',cell(ss['read']),cell(ss['update'])])
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
    (OUT/'numbers.tex').write_text('\n'.join('\\newcommand{\\'+name+'}{'+fmt(value)+'}' for name,(value,_,_) in MACROS.items())+'\n')
    (OUT/'macro-reference.md').write_text('| Macro | Meaning | Unit |\n|---|---|---|\n'+''.join(f'| `\\{n}` | {m} | {u} |\n' for n,(_,m,u) in MACROS.items()))
    return MACROS


def main():
    data=load();derive(data)
    print(f'Validated {len(FILES)} fresh evidence files; generated {len(MACROS)} macros and tables in {OUT}')

if __name__=='__main__':main()
