#!/usr/bin/env python3
"""Create and compare ten real databases on three engines; invoke run.sh."""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import resource
import shutil
import sqlite3
import statistics
import subprocess
import sys
import tempfile
import time
import traceback

from jay import Jay, ROOT, SUITE
from model import load, state, joined
from sql_engines import SQL
from memory import Memory


def sha(b):
    return hashlib.sha256(b).hexdigest()


def save(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')


def check(actual, expected):
    if actual != expected:
        raise AssertionError(f'Expected {expected!r}, got {actual!r}')


def identity():
    names = subprocess.check_output(['git', 'ls-files', '-z', '--cached', '--others', '--exclude-standard'], cwd=ROOT)
    files = {}
    for name in sorted(set(os.fsdecode(n) for n in names.split(b'\0') if n)):
        if name.startswith(('server/', 'native/', 'src/', 'contract/', 'tools/', 'library/', 'proof/')) or name in ('Cargo.toml', 'Cargo.lock'):
            p = ROOT/name
            files[name] = sha(p.read_bytes()) if p.is_file() else '<missing>'
    return files


def suite_identity():
    return {str(p.relative_to(SUITE)): sha(p.read_bytes()) for p in SUITE.rglob('*')
            if p.is_file() and p.suffix in ('.py', '.bend', '.sh', '.json') and 'evidence' not in p.parts}


def check_sources(actual, expected):
    changed = [k for k in actual.keys() | expected.keys() if actual.get(k) != expected.get(k)]
    if changed:
        raise RuntimeError('Benchmark inputs changed: ' + ', '.join(changed))


class Cluster:
    def __init__(self, output, pg_bin):
        self.output, self.bin = output, pg_bin.resolve()
        self.data = output/'postgres-cluster'
        self.env = dict(os.environ, LD_LIBRARY_PATH=str(self.bin.parents[2]/'x86_64-linux-gnu'))
        self.socket = Path(tempfile.mkdtemp(prefix='jaycmp-pg-'))
        self.running = False
        self.dsn = f'host={self.socket} port=55472 dbname=postgres user={os.environ.get("USER", "jota")}'
        try:
            with (output/'postgres-init.log').open('w') as log:
                subprocess.run([str(self.bin/'initdb'), '-D', str(self.data), '--no-locale', '-E', 'UTF8',
                                '-A', 'trust', '-L', str(self.bin.parents[3]/'share/postgresql/16')],
                               stdout=log, stderr=subprocess.STDOUT, check=True, env=self.env)
            with (self.data/'postgresql.conf').open('a') as conf:
                conf.write("\nlisten_addresses = ''\nunix_socket_permissions = 0700\nshared_buffers = '32MB'\nmax_connections = 20\nfsync = on\nsynchronous_commit = on\nfull_page_writes = on\n")
            subprocess.run([str(self.bin/'pg_ctl'), '-D', str(self.data), '-l', str(output/'postgres.log'),
                            '-o', f'-k {self.socket} -p 55472', '-w', 'start'], check=True, stdout=subprocess.DEVNULL, env=self.env)
            self.running = True
        except BaseException:
            self.close()
            raise

    def close(self):
        if self.running:
            subprocess.run([str(self.bin/'pg_ctl'), '-D', str(self.data), '-m', 'fast', '-w', 'stop'],
                           check=True, stdout=subprocess.DEVNULL, env=self.env)
            self.running = False
        shutil.rmtree(self.socket)

    def restart(self):
        subprocess.run([str(self.bin/'pg_ctl'), '-D', str(self.data), '-m', 'fast', '-w', 'stop'],
                       check=True, stdout=subprocess.DEVNULL, env=self.env)
        self.running = False
        subprocess.run([str(self.bin/'pg_ctl'), '-D', str(self.data), '-l', str(self.output/'postgres.log'),
                        '-o', f'-k {self.socket} -p 55472', '-w', 'start'],
                       check=True, stdout=subprocess.DEVNULL, env=self.env)
        self.running = True


def summarize(xs):
    ordered = sorted(xs)
    return {'n': len(xs), 'median_ns': statistics.median(xs), 'p95_ns': ordered[max(0, (95*len(xs)+99)//100-1)],
            'min_ns': min(xs), 'max_ns': max(xs),
            'mad_ns': statistics.median(abs(x-statistics.median(xs)) for x in xs),
            'serial_ops_per_second': 1e9/statistics.mean(xs)}


def benchmark(engine, scenario, folder, options, binary, env, cluster):
    folder.mkdir(parents=True)
    record = {'engine': engine, 'scenario': scenario['id'], 'status': 'running', 'samples': [], 'checks': {}}
    save(folder/'result.json', record)
    db, memory = None, None
    try:
        started = time.perf_counter_ns()
        db = Jay(scenario, folder, binary, env) if engine == 'jaydb2' else SQL(engine, scenario, folder, cluster.dsn if cluster else None)
        record['create_schema_and_client_ns'] = time.perf_counter_ns()-started
        if engine == 'jaydb2':
            record['jay_setup'] = dict(db.setup)
        else:
            if engine == 'postgresql':
                record['settings'] = {k: db.conn.execute('SHOW '+k).fetchone()[0] for k in
                                      ('server_version', 'fsync', 'synchronous_commit', 'full_page_writes', 'shared_buffers')}
                record['database_dsn'] = db.pg_dsn
            else:
                record['settings'] = {k: db.conn.execute('PRAGMA '+k).fetchone()[0] for k in
                                      ('journal_mode', 'synchronous', 'foreign_keys')}
        started = time.perf_counter_ns()
        for t in scenario['tables']:
            for row in t['rows']:
                check(db.put(t['name'], row), True)
        record['populate_ns'] = time.perf_counter_ns()-started
        data = state(scenario)
        # Verify every initial field through real queries, outside timed workloads.
        check(db.dump(), data)
        record['checks']['full_initial_data_equivalence'] = True
        target = scenario['target']
        table, col, key = target['table'], target['column'], target['key']
        row = next(r for r in data[table] if r['id'] == key)
        first = next(r for r in data[table] if r['id'] != key)
        a = scenario['aggregate']
        workloads = ['point_read', 'point_update', 'two_row_transaction', 'scan_sum']
        if scenario['join']:
            workloads.append('relationship_join')
        pid = db.process.pid if engine == 'jaydb2' else int((cluster.data/'postmaster.pid').read_text().splitlines()[0]) if engine == 'postgresql' else os.getpid()
        memory = Memory(pid)
        memory.start()
        record['memory_scope'] = 'Jay controller and descendants' if engine == 'jaydb2' else 'whole private PostgreSQL cluster' if engine == 'postgresql' else 'Python harness including embedded SQLite; not attributable database memory'
        # Interleave workload types, and evolve the independent model through warmups too.
        for iteration in range(options.warmups + options.samples):
            for workload in workloads:
                phase = 'warmup' if iteration < options.warmups else 'sample'
                value = 10000 + iteration
                if workload == 'point_read':
                    fn, expected = lambda: db.get(table, key, col), row[col]
                elif workload == 'point_update':
                    fn, expected = lambda: db.update(table, key, col, value), True
                elif workload == 'two_row_transaction':
                    fn = lambda: db.batch([(table, first['id'], col, value+100), (table, key, col, value+200)])
                    expected = True
                elif workload == 'scan_sum':
                    fn = lambda: db.aggregate(a['table'], a['column'])
                    expected = sum(r[a['column']] for r in data[a['table']])
                else:
                    fn, expected = lambda: db.join(scenario['join']), joined(scenario, data)
                started = time.perf_counter_ns()
                actual = fn()
                elapsed = time.perf_counter_ns()-started
                check(actual, expected)
                record['samples'].append({'workload': workload, 'phase': phase, 'iteration': iteration,
                                          'elapsed_ns': elapsed, 'checked': True,
                                          'actual': actual, 'expected': expected})
                if workload == 'point_update':
                    row[col] = value
                    check(db.get(table, key, col), value)
                elif workload == 'two_row_transaction':
                    first[col], row[col] = value+100, value+200
                    check(db.get(table, first['id'], col), value+100)
                    check(db.get(table, key, col), value+200)
        record['memory'] = memory.stop()
        memory = None
        record['checks']['all_timed_outputs_and_written_cells'] = True
        check(db.get(table, '__missing__', col), None)
        record['checks']['missing_row_returns_none'] = True
        # Each should reject the nonnumeric string rather than publishing it.
        try:
            db.update(table, key, col, 'not-an-integer')
        except Exception as exc:
            record['checks']['wrong_type_rejected'] = type(exc).__name__ + ': ' + str(exc)
        else:
            raise AssertionError('Wrong type accepted')
        check(db.get(table, key, col), row[col])
        try:
            db.batch([(table, first['id'], col, 99999), (table, key, col, 'not-an-integer')])
        except Exception as exc:
            record['checks']['failed_second_write_rolled_back'] = type(exc).__name__ + ': ' + str(exc)
        else:
            raise AssertionError('Invalid batch accepted')
        check(db.get(table, first['id'], col), first[col])
        check(db.get(table, key, col), row[col])
        # Distinguish upsert from SQL INSERT; restore original model after the probe.
        original = dict(row)
        replacement = dict(row, **{col: 12345})
        try:
            db.put(table, replacement)
        except Exception as exc:
            record['checks']['duplicate_id'] = {'behavior': 'rejected', 'exception': type(exc).__name__}
        else:
            check(db.get(table, key, col), 12345)
            record['checks']['duplicate_id'] = {'behavior': 'replaced_existing_row'}
            db.put(table, original)
        check(db.get(table, key, col), row[col])
        if scenario['join']:
            j = scenario['join']
            child = data[j['from_table']][0]
            try:
                db.update(j['from_table'], child['id'], j['fk'], '__missing_parent__')
            except Exception as exc:
                record['checks']['foreign_key'] = {'behavior': 'rejected', 'exception': type(exc).__name__}
            else:
                check(db.get(j['from_table'], child['id'], j['fk']), '__missing_parent__')
                record['checks']['foreign_key'] = {'behavior': 'accepted_orphan'}
                db.update(j['from_table'], child['id'], j['fk'], child[j['fk']])
            check(db.get(j['from_table'], child['id'], j['fk']), child[j['fk']])
        # CRUD roundtrip on a leaf table avoids deleting referenced parents.
        leaf = scenario['tables'][-1]
        added = dict(leaf['rows'][0], id='__roundtrip__')
        check(db.put(leaf['name'], added), True)
        check(db.get(leaf['name'], added['id'], 'id'), added['id'])
        check(db.delete(leaf['name'], added['id']), True)
        check(db.get(leaf['name'], added['id'], 'id'), None)
        record['checks']['insert_delete_roundtrip'] = True
        started = time.perf_counter_ns()
        db.reopen()
        record['reopen_and_client_prepare_ns'] = time.perf_counter_ns()-started
        # Complete final readback after reopening, not only one sampled cell.
        check(db.dump(), data)
        record['checks']['full_final_data_after_reopen'] = True
        save(folder/'final-data.json', data)
        record['final_data_sha256'] = sha(json.dumps(data, sort_keys=True).encode())
        record['storage_bytes_live'] = db.size_bytes()
        record['summary'] = {w: summarize([x['elapsed_ns'] for x in record['samples'] if x['phase'] == 'sample' and x['workload'] == w]) for w in workloads}
        record['status'] = 'passed'
    except Exception as exc:
        record['status'] = 'failed'
        record['error'] = f'{type(exc).__name__}: {exc}'
        (folder/'error.txt').write_text(traceback.format_exc())
        print(traceback.format_exc(), flush=True)
    finally:
        if memory is not None:
            record['memory'] = memory.stop()
        if db is not None:
            try:
                db.close()
                if engine != 'postgresql':
                    record['storage_bytes_closed'] = db.size_bytes()
            except Exception as exc:
                record['close_error'] = str(exc)
                record['status'] = 'failed'
        save(folder/'result.json', record)
    return record


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--pg-bin', type=Path, default=ROOT/'build/database-comparison-deps/usr/lib/postgresql/16/bin')
    p.add_argument('--scenarios', nargs='+')
    p.add_argument('--engines', nargs='+', choices=['jaydb2', 'postgresql', 'sqlite'], default=['jaydb2', 'postgresql', 'sqlite'])
    p.add_argument('--samples', type=int, default=7)
    p.add_argument('--warmups', type=int, default=1)
    options = p.parse_args()
    if options.samples < 2 or options.warmups < 0:
        p.error('samples >= 2 and warmups >= 0 required')
    output = options.output.resolve()
    if not output.is_relative_to(ROOT/'build'):
        p.error('output must be a new directory under repository build/')
    output.mkdir(parents=True, exist_ok=False)
    (output/'tmp').mkdir()
    resource.setrlimit(resource.RLIMIT_STACK, (resource.RLIM_INFINITY, resource.getrlimit(resource.RLIMIT_STACK)[1]))
    env = dict(os.environ, BEND_NO_TELEMETRY='1', BENDRTS='', TMPDIR=str(output/'tmp'),
               CARGO_TARGET_DIR=str(ROOT/'build/database-comparison-target'))
    scenarios = [load(f) for f in sorted((SUITE/'scenarios').glob('*.json')) if not options.scenarios or f.stem in options.scenarios]
    if not scenarios or (options.scenarios and set(options.scenarios) != {s['id'] for s in scenarios}):
        p.error('unknown or empty scenario selection')
    before, suite_before = identity(), suite_identity()
    manifest = {'started_utc': datetime.now(timezone.utc).isoformat(), 'output': str(output),
                'git_head': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
                'git_branch': subprocess.check_output(['git', 'branch', '--show-current'], cwd=ROOT, text=True).strip(),
                'git_status': subprocess.check_output(['git', 'status', '--short'], cwd=ROOT, text=True),
                'source_sha256': before, 'suite_sha256': suite_before, 'status': 'running', 'results': [],
                'settings': {'samples': options.samples, 'warmups': options.warmups, 'engines': options.engines,
                             'durable': True, 'clients': 1, 'jay_threads': 1, 'read_workers': 1,
                             'timing': 'Python API call through decoded result; encoding/decoding included, validation excluded',
                             'lock': '/tmp/jaydb2-experiments-heavy.lock'},
                'hardware': {'platform': platform.platform(), 'cpu': next(x.split(':', 1)[1].strip() for x in Path('/proc/cpuinfo').read_text().splitlines() if x.startswith('model name')),
                             'logical_cpus': os.cpu_count(), 'affinity': sorted(os.sched_getaffinity(0)),
                             'mem_total': Path('/proc/meminfo').read_text().splitlines()[0], 'load_start': os.getloadavg()},
                'versions': {'python': sys.version, 'sqlite': sqlite3.sqlite_version,
                             'node': subprocess.check_output(['node', '--version'], text=True).strip(),
                             'postgresql': subprocess.check_output([str(options.pg_bin/'postgres'), '--version'], text=True).strip() if 'postgresql' in options.engines else None},
                'scenario_sha256': {s['id']: sha((SUITE/'scenarios'/f'{s["id"]}.json').read_bytes()) for s in scenarios}}
    (output/'preexisting-and-experiment.patch').write_bytes(subprocess.check_output(['git', 'diff', 'HEAD', '--binary'], cwd=ROOT))
    shutil.copytree(SUITE, output/'suite', ignore=shutil.ignore_patterns('__pycache__', 'evidence', 'REPORT.md'))
    cluster = None
    try:
        if 'jaydb2' in options.engines:
            started = time.perf_counter_ns()
            with (output/'build.log').open('w') as log:
                subprocess.run(['cargo', 'build', '--locked', '--release'], cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT, check=True)
            binary = Path(env['CARGO_TARGET_DIR'])/'release/jaydb2'
            manifest['jay_build_ns'] = time.perf_counter_ns()-started
            manifest['jay_binary'] = str(binary)
            manifest['jay_binary_sha256'] = sha(binary.read_bytes())
            check_sources(identity(), before)
            lock = json.loads((ROOT/'tools/admission/toolchain.lock.json').read_text())
            manifest['toolchain_lock'] = lock
            manifest['verified_tools'] = {}
            for name, path, expected in [('bend', ROOT/f'.tools/bend-{lock["version"]}/bin/bend', lock['officialBinarySha256']),
                                         ('bendtt', ROOT/f'.tools/bendtt-{lock["kernelSha256"]}', lock['kernelSha256'])]:
                check(sha(path.read_bytes()), expected)
                manifest['verified_tools'][name] = expected
        else:
            binary = None
        if 'postgresql' in options.engines:
            cluster = Cluster(output, options.pg_bin)
            manifest['postgres_dsn_when_running'] = cluster.dsn
        save(output/'result.json', manifest)
        for i, scenario in enumerate(scenarios):
            # Rotate engine ordering across scenarios. Only one measured engine at a time.
            engines = options.engines[i % len(options.engines):] + options.engines[:i % len(options.engines)]
            for engine in engines:
                print(f'{scenario["id"]}: {engine} start', flush=True)
                r = benchmark(engine, scenario, output/scenario['id']/engine, options, binary, env, cluster)
                manifest['results'].append(r)
                save(output/'result.json', manifest)
                print(f'{scenario["id"]}: {engine} {r["status"]}', flush=True)
        if cluster:
            from psycopg.conninfo import make_conninfo
            import psycopg
            from sql_engines import quote
            started = time.perf_counter_ns()
            cluster.restart()
            manifest['postgres_whole_cluster_restart_ns'] = time.perf_counter_ns()-started
            for r in manifest['results']:
                if r['engine'] != 'postgresql' or r['status'] != 'passed':
                    continue
                scenario = next(s for s in scenarios if s['id'] == r['scenario'])
                folder = output/scenario['id']/'postgresql'
                dsn = make_conninfo(cluster.dsn, dbname='cmp_'+scenario['id'])
                recovered = {}
                with psycopg.connect(dsn, autocommit=True) as conn:
                    for t in scenario['tables']:
                        names = [c['name'] for c in t['columns']]
                        rows = conn.execute('SELECT ' + ', '.join(map(quote, names)) + ' FROM ' + quote(t['name']) + ' ORDER BY id').fetchall()
                        recovered[t['name']] = [dict(zip(names, row, strict=True)) for row in rows]
                check(recovered, json.loads((folder/'final-data.json').read_text()))
                r['checks']['full_final_data_after_server_restart'] = True
                subprocess.run([str(cluster.bin/'pg_dump'), '--dbname', dsn, '--file', str(folder/'database.sql')],
                               env=cluster.env, check=True, stderr=subprocess.PIPE)
                save(folder/'result.json', r)
        check_sources(identity(), before)
        check_sources(suite_identity(), suite_before)
        manifest['status'] = 'passed' if all(r['status'] == 'passed' for r in manifest['results']) else 'failed'
    except BaseException as exc:
        manifest['status'], manifest['error'] = 'failed', f'{type(exc).__name__}: {exc}'
        raise
    finally:
        if cluster:
            cluster.close()
        manifest['finished_utc'] = datetime.now(timezone.utc).isoformat()
        manifest['hardware']['load_end'] = os.getloadavg()
        save(output/'result.json', manifest)
        print(f'{manifest["status"]}: {output}/result.json', flush=True)
    return 0 if manifest['status'] == 'passed' else 1


if __name__ == '__main__':
    raise SystemExit(main())
