"""Durable SQL comparison and complete-state scaling, all outputs checked."""
from contextlib import contextmanager
import os
import shutil
import sqlite3
import subprocess
import time

from paper.bench.run import BUILD, ROOT, metadata, package, save, session, source


@contextmanager
def postgres():
    import psycopg
    prefix=BUILD/'pg'
    binary=prefix/'usr/lib/postgresql/16/bin'
    env=dict(os.environ,LD_LIBRARY_PATH=str(prefix/'usr/lib/x86_64-linux-gnu'))
    cluster=BUILD/'pgdata'; sock=BUILD/'pgsocket'
    sock.mkdir(exist_ok=True)
    # Unix sockets are limited to 108 bytes, so use a short ignored /tmp path.
    import tempfile
    with tempfile.TemporaryDirectory(prefix='jaypg-') as tmp:
        if cluster.exists(): shutil.rmtree(cluster)
        subprocess.run([str(binary/'initdb'),'-D',str(cluster),'-L',str(prefix/'usr/share/postgresql/16'),'-A','trust','--no-locale','--encoding=UTF8'],env=env,check=True,stdout=subprocess.DEVNULL)
        subprocess.run([str(binary/'pg_ctl'),'-D',str(cluster),'-l',str(BUILD/'postgres.log'),'-o',f'-k {tmp} -h "" -p 55439 -c fsync=on -c synchronous_commit=on -c full_page_writes=on','-w','start'],env=env,check=True,stdout=subprocess.DEVNULL)
        try:
            dsn=f'host={tmp} port=55439 dbname=postgres'
            with psycopg.connect(dsn,autocommit=True) as admin:
                admin.execute('CREATE ROLE bench_alice LOGIN NOSUPERUSER NOBYPASSRLS')
                admin.execute('CREATE ROLE bench_bob LOGIN NOSUPERUSER NOBYPASSRLS')
                settings={k:admin.execute('SHOW '+k).fetchone()[0] for k in ('server_version','fsync','synchronous_commit','full_page_writes','shared_buffers','wal_sync_method')}
                settings['role']=admin.execute("SELECT rolname,rolsuper,rolbypassrls FROM pg_roles WHERE rolname='bench_alice'").fetchone()
                yield psycopg,dsn,admin,settings
        finally:
            subprocess.run([str(binary/'pg_ctl'),'-D',str(cluster),'-m','fast','-w','stop'],env=env,check=True,stdout=subprocess.DEVNULL)


# Canonical state accounting is shared by E3 and E5.
def canonical_state(count, policy=False):
    names=['alice','bob'] if policy else ['cells']
    counts=[count//2,count-count//2] if policy else [count]
    return dict(tables=[dict(name=name,rows=[dict(id=f'k{i:06d}',value=0) for i in range(n)]) for name,n in zip(names,counts)],
        users=[dict(credential=u+'-token',id=u,kind='user') for u in ('alice','bob')])


def state_bytes(count,policy=False):
    from tools.client import encode
    return len(encode(canonical_state(count,policy)))


def max_rows(policy=False):
    n=0
    while state_bytes(n+1,policy)<=65536:n+=1
    return n


def populate(s,code,proof,count,policy=False):
    from paper.bench.fixtures import bulk_population,owner_population
    from tools.client import prepared_frame
    population,certificate=owner_population(proof) if policy else bulk_population(proof)
    handle,registration=s.prepare(population,certificate)
    calls=[]
    for user,n in ([('alice',count//2),('bob',count-count//2)] if policy else [('alice',count)]):
        calls.append(s.call(population,certificate,[f'k{i:06d}' for i in range(n)],dict(status='success',value=n),handle=handle,user=user+'-token'))
    s.exchange(prepared_frame(2,handle,'alice-token'),dict(status='invalidated',value=None))
    return dict(calls=calls,registration=registration,total_rows=count)


def sql_record(engine,policy,conn,count,sid):
    rows=[];warmup=[]
    token='?' if engine=='sqlite' else '%s'
    target=f'k{(count//2 if policy else count)-1:06d}'
    for workload in ('read','update'):
        for i in range(301):
            if workload=='read':
                query=f'SELECT value FROM cells WHERE owner={token} AND id={token}'
                params=('bench_alice',target);expected=[(0,)]
            else:
                query=f'UPDATE cells SET value={token} WHERE owner={token} AND id={token} RETURNING value'
                params=(i,'bench_alice',target);expected=[(i,)]
            start=time.perf_counter_ns();actual=conn.execute(query,params).fetchall();elapsed=time.perf_counter_ns()-start
            assert actual==expected,(engine,workload,actual,expected)
            row=dict(workload=workload,iteration=i,elapsed_ns=elapsed,actual=[list(x) for x in actual],expected=[list(x) for x in expected],checked=True)
            (warmup if i==0 else rows).append(row)
    return dict(engine=engine,policy='owner' if policy else 'point',rows=count,session=sid,persistent=True,n=300,samples=rows,warmup=warmup,frequency=metadata()['frequency'],target=target)


def comparison():
    from paper.bench.run import pool_record
    large=min(max_rows(False),max_rows(True))
    data=dict(metadata=metadata(),experiment='E3 durable local comparison',large_rows=large,records=[],policy_checks=[],settings={},
        limitations=['SQLite is an unconstrained WAL/FULL baseline; cross-user access succeeds.',
        'All engines have the same TOTAL row count: owner workload divides rows equally between alice and bob.',
        'Target is the last alice key; JayDB2 owner tables follow the existing access ownership law.',
        'SQL uses execute/fetchall; JayDB2 intervals are encoded request through complete response; checking excluded.',
        'JayDB2 update returns acknowledgement with untimed readback; SQL returns changed integer.',
        'JayDB2 persists a complete changed image; identical images reuse the durable snapshot.',
        'Each session/engine/condition has a fresh process/cluster/database; engine and condition order rotate.'])
    conditions=[(n,p) for n in (10,large) for p in (False,True)]
    engines=['postgresql','sqlite','jaydb2']
    for sid in range(1,4):
        for count,policy in conditions[sid-1:]+conditions[:sid-1]:
            entries=[(owner,f'k{i:06d}') for owner,n in ([('bench_alice',count//2),('bench_bob',count-count//2)] if policy else [('bench_alice',count)]) for i in range(n)]
            for engine in engines[sid-1:]+engines[:sid-1]:
                name=f'comparison-{count}-{policy}-{engine}-{sid}'
                if engine=='postgresql':
                    with postgres() as (psycopg,dsn,admin,settings):
                        admin.execute('CREATE TABLE cells(owner text NOT NULL,id text NOT NULL,value bigint NOT NULL,PRIMARY KEY(owner,id))')
                        with admin.cursor() as cur:cur.executemany('INSERT INTO cells VALUES (%s,%s,0)',entries)
                        admin.execute('GRANT SELECT,UPDATE ON cells TO bench_alice')
                        if policy:
                            admin.execute('ALTER TABLE cells ENABLE ROW LEVEL SECURITY');admin.execute('ALTER TABLE cells FORCE ROW LEVEL SECURITY')
                            admin.execute('CREATE POLICY own_rows ON cells USING (owner=current_user) WITH CHECK (owner=current_user)')
                        with psycopg.connect(dsn+' user=bench_alice',autocommit=True,prepare_threshold=0) as conn:
                            conn.execute('SET synchronous_commit=on')
                            if policy:
                                for w,q in [('read',"SELECT value FROM cells WHERE owner='bench_bob' AND id='k000000'"),('update',"UPDATE cells SET value=999 WHERE owner='bench_bob' AND id='k000000' RETURNING value")]:
                                    actual=conn.execute(q).fetchall();assert actual==[]
                                    data['policy_checks'].append(dict(engine=engine,session=sid,rows=count,workload=w,attempt=q,credential='bench_alice (NOSUPERUSER NOBYPASSRLS)',actual=actual,expected=[],checked=True,refused=True))
                                assert admin.execute("SELECT value FROM cells WHERE owner='bench_bob' AND id='k000000'").fetchone()==(0,)
                                settings['rls']=admin.execute("SELECT relrowsecurity,relforcerowsecurity FROM pg_class WHERE relname='cells'").fetchone()
                            record=sql_record(engine,policy,conn,count,sid)
                            record['settings']=settings;data['settings']['postgresql']=settings
                elif engine=='sqlite':
                    path=BUILD/(name+'.db');path.unlink(missing_ok=True)
                    with sqlite3.connect(path,isolation_level=None) as conn:
                        conn.execute('PRAGMA journal_mode=WAL');conn.execute('PRAGMA synchronous=FULL')
                        conn.execute('CREATE TABLE cells(owner TEXT NOT NULL,id TEXT NOT NULL,value INTEGER NOT NULL,PRIMARY KEY(owner,id)) STRICT')
                        conn.executemany('INSERT INTO cells VALUES (?,?,0)',entries)
                        settings={k:conn.execute('PRAGMA '+k).fetchone()[0] for k in ('journal_mode','synchronous','page_size','wal_autocheckpoint')}
                        if policy:
                            for w,q,expected in [('read',"SELECT value FROM cells WHERE owner='bench_bob' AND id='k000000'",[(0,)]),('update',"UPDATE cells SET value=999 WHERE owner='bench_bob' AND id='k000000' RETURNING value",[(999,)])]:
                                actual=conn.execute(q).fetchall();assert actual==expected
                                data['policy_checks'].append(dict(engine=engine,session=sid,rows=count,workload=w,attempt=q,credential='unconstrained connection (no RLS)',actual=[list(x) for x in actual],expected=[list(x) for x in expected],checked=True,refused=False))
                            conn.execute("UPDATE cells SET value=0 WHERE owner='bench_bob' AND id='k000000'")
                        record=sql_record(engine,policy,conn,count,sid);record['settings']=settings;data['settings']['sqlite']=settings
                else:
                    folder=package(BUILD/name,'policy' if policy else 'read',0)
                    code,proof,universal=source(folder)
                    target=f'k{(count//2 if policy else count)-1:06d}'
                    record=dict(engine=engine,policy='owner' if policy else 'point',rows=count,state_bytes=state_bytes(count,policy),persistent=True,session=sid,frequency=metadata()['frequency'],n=300,samples=[],warmup=[],ordinary=[],target=target)
                    with session(folder,name,persistent=True) as s:
                        record['population']=populate(s,code,proof,count,policy)
                        handle,registration=s.prepare(code,universal);record['registration']=registration
                        if policy:
                            for workload,op in [('read','D.ReadCell'),('update','D.DefineColumn')]:
                                bad=code.replace(op+'{D.Application{owner}',op+'{D.Application{"bob"}')
                                assert bad!=code
                                args=[workload,'k000000']+([999] if workload=='update' else [])
                                row=s.call(bad,proof,args,dict(status='certificate',value=None))
                                row.update(engine=engine,session=sid,rows=count,workload=workload,refused=True,attempt=dict(code=bad,proof=proof,arguments=args,credential='alice-token'),stage='ordinary admission; unchanged ownership certificate rejected')
                                data['policy_checks'].append(row)
                            s.call(code,proof,['read','k000000'],dict(status='success',value=0),handle=handle,user='bob-token')
                        for workload in ('read','update'):
                            # Retain ordinary context at the existing small state only.
                            if count==10:
                                for i in range(11):
                                    args=[workload,target]+([i] if workload=='update' else [])
                                    row=s.call(code,proof,args,dict(status='success',value=True if workload=='update' else 0))
                                    if workload=='update':s.call(code,proof,['read',target],dict(status='success',value=i),handle=handle)
                                    row.update(workload=workload,iteration=i,phase='warmup' if i==0 else 'sample');record['ordinary'].append(row)
                            if workload=='update':s.call(code,proof,['update',target,0],dict(status='success',value=True),handle=handle)
                            for i in range(301):
                                args=[workload,target]+([i] if workload=='update' else [])
                                row=s.call(code,proof,args,dict(status='success',value=True if workload=='update' else 0),handle=handle)
                                if workload=='update':
                                    check=s.call(code,proof,['read',target],dict(status='success',value=i),handle=handle)
                                    row['stored_value_checked']=check['checked'];row['stored_value']=check['actual']['value']
                                row.update(workload=workload,iteration=i);record['warmup' if i==0 else 'samples'].append(row)
                pool_record(data,record,('engine','policy','rows'));save('comparison.json',data)
                print('comparison',sid,count,policy,engine,'complete',flush=True)


def scaling(populations=None):
    n=max_rows()
    data=dict(metadata=metadata(),experiment='E5 state scaling',session_count=1,state_limit=65536,max_rows=n,records=[],failures=[],boundary_checks=[],
        setup_method='One experimental session; one fresh service per storage mode, reused across all ascending sizes. Certified population resets every row to zero between sizes; population handles invalidated before sampling.',
        limitations=['Unchanged 65536-byte ceiling; canonical seven-byte keys, int64 values and two users.',
        'Last-key point operations include complete-state transfer, decoding, validation, lookup and publication.',
        'First-key read endpoints retain complete-state costs but shorten linear lookup.'])
    sizes=sorted(set(populations or [10,30,100,300,600,1000,n]))
    data['populations']=sizes
    for count in (n+1,10000):data['failures'].append(dict(rows=count,state_bytes=state_bytes(count),reason='canonical state exceeds configured state limit',measured=False))
    from paper.bench.fixtures import bulk_population
    from tools.client import prepared_frame
    for persistent in (False,True):
        name=f'scaling-{persistent}';folder=package(BUILD/name,'read',0)
        code,proof,universal=source(folder)
        with session(folder,name,persistent=persistent) as s:
            handle,registration=s.prepare(code,universal)
            for count in sizes:
                record=dict(rows=count,state_bytes=state_bytes(count),persistent=persistent,session=1,service_pid=s.p.pid,frequency=metadata()['frequency'],n=50,samples=[],warmup=[],first_key_samples=[],first_key_warmup=[],registration=registration)
                record['population']=populate(s,code,proof,count)
                for workload in ('read','update'):
                    for i in range(51):
                        args=[workload,f'k{count-1:06d}']+([i] if workload=='update' else [])
                        row=s.call(code,proof,args,dict(status='success',value=True if workload=='update' else 0),handle=handle)
                        if workload=='update':
                            check=s.call(code,proof,['read',f'k{count-1:06d}'],dict(status='success',value=i),handle=handle);row['stored_value_checked']=check['checked']
                        row.update(workload=workload,iteration=i);record['warmup' if i==0 else 'samples'].append(row)
                if count in (sizes[0],sizes[-1]):
                    for i in range(51):
                        row=s.call(code,proof,['read','k000000'],dict(status='success',value=0),handle=handle)
                        row.update(workload='read',iteration=i)
                        record['first_key_warmup' if i==0 else 'first_key_samples'].append(row)
                data['records'].append(record);save('scaling.json',data)
                print('scaling',count,persistent,'complete',flush=True)
            population,certificate=bulk_population(proof);growth,_=s.prepare(population,certificate)
            boundary=s.call(population,certificate,[f'k{n:06d}'],dict(status='limit',value=None),handle=growth)
            boundary.update(rows=n+1,state_bytes=state_bytes(n+1),persistent=persistent)
            boundary['rollback_check']=s.call(code,proof,['read',f'k{n:06d}'],dict(status='refusal',value=None),handle=handle)
            data['boundary_checks'].append(boundary);save('scaling.json',data)
