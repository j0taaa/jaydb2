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


def sql_record(engine,policy,conn):
    rows=[]; warmup=[]
    token='?' if engine=='sqlite' else '%s'
    for workload in ('read','update'):
        for i in range(301):
            if workload=='read':
                query=f'SELECT value FROM cells WHERE owner={token} AND id={token}'
                params=('bench_alice','k000000'); expected=[(0,)]
            else:
                query=f'UPDATE cells SET value={token} WHERE owner={token} AND id={token} RETURNING value'
                params=(i,'bench_alice','k000000'); expected=[(i,)]
            start=time.perf_counter_ns()
            actual=conn.execute(query,params).fetchall()
            elapsed=time.perf_counter_ns()-start
            assert actual==expected,(engine,workload,actual,expected)
            row=dict(workload=workload,iteration=i,elapsed_ns=elapsed,actual=[list(x) for x in actual],expected=[list(x) for x in expected],checked=True)
            (warmup if i==0 else rows).append(row)
    return dict(engine=engine,policy='owner' if policy else 'point',persistent=True,n=300,samples=rows,warmup=warmup)


def comparison():
    data=dict(metadata=metadata(),experiment='E3 durable single-client local comparison',records=[],policy_checks=[],settings={},
        limitations=['SQLite is an unconstrained baseline: no RLS or administrator ownership law.',
        'JayDB2 uses owner-named tables (existing access/tasks policy pattern); PG uses owner column RLS.',
        'Point update returns an acknowledgment in JayDB2; a separate untimed read verifies the stored integer. SQL returns the integer.',
        'JayDB2 changed-state success persists a complete image; byte-identical state reuses the durable image. PG/SQLite read-only SELECT does not fsync a new image.',
        'Prepared SQL queries use psycopg automatic server preparation; SQLite uses its default statement cache.'])
    with postgres() as (psycopg,dsn,admin,settings):
        data['settings']['postgresql']=settings
        for policy in (False,True):
            admin.execute('DROP TABLE IF EXISTS cells')
            admin.execute('CREATE TABLE cells(owner text NOT NULL,id text NOT NULL,value bigint NOT NULL,PRIMARY KEY(owner,id))')
            for owner in (('bench_alice','bench_bob') if policy else ('bench_alice',)):
                for i in range(10): admin.execute('INSERT INTO cells VALUES (%s,%s,0)',(owner,f'k{i:06d}'))
            admin.execute('GRANT SELECT,UPDATE ON cells TO bench_alice')
            if policy:
                admin.execute('ALTER TABLE cells ENABLE ROW LEVEL SECURITY')
                admin.execute('ALTER TABLE cells FORCE ROW LEVEL SECURITY')
                admin.execute('CREATE POLICY own_rows ON cells USING (owner=current_user) WITH CHECK (owner=current_user)')
            with psycopg.connect(dsn+' user=bench_alice',autocommit=True,prepare_threshold=0) as conn:
                conn.execute('SET synchronous_commit=on')
                if policy:
                    for workload,q in [('read',"SELECT value FROM cells WHERE owner='bench_bob' AND id='k000000'"),('update',"UPDATE cells SET value=999 WHERE owner='bench_bob' AND id='k000000' RETURNING value")]:
                        actual=conn.execute(q).fetchall(); assert actual==[]
                        data['policy_checks'].append(dict(engine='postgresql',workload=workload,actual=actual,expected=[],checked=True,refused=True))
                    assert admin.execute("SELECT value FROM cells WHERE owner='bench_bob' AND id='k000000'").fetchone()==(0,)
                    data['settings']['postgresql']['rls']=admin.execute("SELECT relrowsecurity,relforcerowsecurity FROM pg_class WHERE relname='cells'").fetchone()
                data['records'].append(sql_record('postgresql',policy,conn))
            path=BUILD/f'comparison-sqlite-{policy}.db'; path.unlink(missing_ok=True)
            with sqlite3.connect(path,isolation_level=None) as conn:
                conn.execute('PRAGMA journal_mode=WAL');conn.execute('PRAGMA synchronous=FULL')
                conn.execute('CREATE TABLE cells(owner TEXT NOT NULL,id TEXT NOT NULL,value INTEGER NOT NULL,PRIMARY KEY(owner,id)) STRICT')
                conn.executemany('INSERT INTO cells VALUES (?,?,0)',[(owner,f'k{i:06d}') for owner in (('bench_alice','bench_bob') if policy else ('bench_alice',)) for i in range(10)])
                data['settings']['sqlite']={k:conn.execute('PRAGMA '+k).fetchone()[0] for k in ('journal_mode','synchronous','page_size','wal_autocheckpoint')}
                data['records'].append(sql_record('sqlite',policy,conn))
            save('comparison.json',data)
            kind='policy' if policy else 'read'
            name='comparison-'+kind
            folder=package(BUILD/name,kind)
            code,proof,universal=source(folder)
            with session(folder,name,persistent=True) as s:
                handle,registration=s.prepare(code,universal)
                if policy:
                    for workload,op in [('read','D.ReadCell'),('update','D.DefineColumn')]:
                        bad=code.replace(op+'{D.Application{owner}',op+'{D.Application{"bob"}')
                        assert bad!=code
                        row=s.call(bad,proof,[workload,'k000000']+([999] if workload=='update' else []),dict(status='certificate',value=None))
                        row.update(engine='jaydb2',workload=workload,refused=True)
                        data['policy_checks'].append(row)
                    s.call(code,proof,['read','k000000'],dict(status='success',value=0),handle=handle,user='bob-token')
                record=dict(engine='jaydb2',policy='owner' if policy else 'point',persistent=True,n=300,samples=[],warmup=[],ordinary=[],registration=registration)
                for workload in ('read','update'):
                    # Ordinary path context, same durable configuration and operation.
                    for i in range(11):
                        args=[workload,'k000000']+([i] if workload=='update' else [])
                        row=s.call(code,proof,args,dict(status='success',value=True if workload=='update' else 0))
                        if workload=='update': s.call(code,proof,['read','k000000'],dict(status='success',value=i),handle=handle)
                        row.update(workload=workload,iteration=i,phase='warmup' if i==0 else 'sample');record['ordinary'].append(row)
                    if workload=='update': s.call(code,proof,['update','k000000',0],dict(status='success',value=True),handle=handle)
                    for i in range(301):
                        args=[workload,'k000000']+([i] if workload=='update' else [])
                        row=s.call(code,proof,args,dict(status='success',value=True if workload=='update' else 0),handle=handle)
                        if workload=='update':
                            check=s.call(code,proof,['read','k000000'],dict(status='success',value=i),handle=handle)
                            row['stored_value_checked']=check['checked'];row['stored_value']=check['actual']['value']
                        row.update(workload=workload,iteration=i)
                        record['warmup' if i==0 else 'samples'].append(row)
            data['records'].append(record);save('comparison.json',data)
            print('comparison',policy,'complete',flush=True)


def scaling(populations=None):
    # Default 64 KiB state ceiling: report its actual boundary rather than
    # silently increasing the application limit to make larger plots fit.
    data=dict(metadata=metadata(),experiment='E5 state-size scaling',state_limit=65536,records=[],failures=[],
        setup_method='Empty valid seed, certified prepared population transaction, checked row count; population handle invalidated before sampling.',
        limitations=['Default application state limit retained (65536 canonical bytes). Larger requested populations are sized canonically and reported as outside the limit, without timing impossible valid seeds.',
        'Each table row has an id of seven ASCII bytes and one int64 value; two fixed users.',
        'State bytes computed by the canonical wire encoder, matching Data.state_value.'])
    from tools.client import encode
    def state(n):
        return dict(tables=[dict(name='cells',rows=[dict(id=f'k{i:06d}',value=0) for i in range(n)])],users=[dict(credential=u+'-token',id=u,kind='user') for u in ('alice','bob')])
    n=0
    while len(encode(state(n+1)))<=65536:n+=1
    data['max_rows']=n
    for count in sorted(set(populations or [10,100,1000,10000,n,n+1])):
        size=len(encode(state(count)))
        if size>65536:
            data['failures'].append(dict(rows=count,state_bytes=size,reason='canonical state exceeds configured state limit',measured=False))
            save('scaling.json',data);continue
        for persistent in (False,True):
            name=f'scaling-{count}-{persistent}';folder=package(BUILD/name,'read',0)
            code,proof,universal=source(folder)
            record=dict(rows=count,state_bytes=size,persistent=persistent,n=50,samples=[],warmup=[])
            try:
                with session(folder,name,persistent=persistent) as s:
                    handle,registration=s.prepare(code,universal);record['registration']=registration
                    from paper.bench.fixtures import bulk_population
                    population,population_proof=bulk_population(proof)
                    population_handle,_=s.prepare(population,population_proof)
                    record['population']=s.call(population,population_proof,[f'k{i:06d}' for i in range(count)],dict(status='success',value=count),handle=population_handle)
                    from tools.client import prepared_frame
                    s.exchange(prepared_frame(2,population_handle,'alice-token'),dict(status='invalidated',value=None))
                    for workload in ('read','update'):
                        for i in range(51):
                            args=[workload,f'k{count-1:06d}']+([i] if workload=='update' else [])
                            row=s.call(code,proof,args,dict(status='success',value=True if workload=='update' else 0),handle=handle)
                            if workload=='update':
                                check=s.call(code,proof,['read',f'k{count-1:06d}'],dict(status='success',value=i),handle=handle)
                                row['stored_value_checked']=check['checked']
                            row.update(workload=workload,iteration=i)
                            record['warmup' if i==0 else 'samples'].append(row)
                    if count==n:
                        # Re-admit the same population program for one excess
                        # row after all point-operation samples finish.
                        growth_handle,_=s.prepare(population,population_proof)
                        boundary=s.call(population,population_proof,[f'k{count:06d}'],dict(status='limit',value=None),handle=growth_handle)
                        boundary.update(rows=count+1,state_bytes=len(encode(state(count+1))),persistent=persistent)
                        data.setdefault('boundary_checks',[]).append(boundary)
                        boundary['rollback_check']=s.call(code,proof,['read',f'k{count:06d}'],dict(status='refusal',value=None),handle=handle)
                data['records'].append(record)
            except (RuntimeError,AssertionError,TimeoutError) as error:
                data['failures'].append(dict(rows=count,state_bytes=size,persistent=persistent,reason=str(error),measured=True))
            save('scaling.json',data)
            print('scaling',count,persistent,'complete',flush=True)
