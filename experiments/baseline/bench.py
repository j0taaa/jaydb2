#!/usr/bin/env python3
"""External CPU benchmark; invoke run.sh to serialize heavy work with flock."""
from __future__ import annotations

import argparse
from collections import defaultdict
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import platform
import resource
import shutil
import signal
import statistics
import subprocess
import sys
import time

SUITE = Path(__file__).resolve().parent
ANCHOR = '5925c57febd978d44fa24000233647a59e7898a6'
REFERENCE = '9b751fab3c7c349ff473a2d11a7133573b6c4df2'
WORKLOADS = ('read', 'write', 'batch', 'compute')
PAD = 'p' * 128
TOKEN = 'benchmark-token'


def sha(data):
    return hashlib.sha256(data).hexdigest()


def command(argv, cwd=None, env=None):
    return subprocess.check_output(argv, cwd=cwd, env=env, text=True, stderr=subprocess.STDOUT).strip()


def revision(root):
    # The exact patch is retained, rather than calling a dirty tree a revision.
    patch = subprocess.check_output(['git', 'diff', 'HEAD', '--binary'], cwd=root)
    return {'head': command(['git', 'rev-parse', 'HEAD'], root),
            'branch': command(['git', 'branch', '--show-current'], root),
            'status': command(['git', 'status', '--porcelain'], root),
            'tracked_patch_sha256': sha(patch)}


def source_identity(root):
    # Include tracked and untracked, nonignored checkout inputs. Benchmark
    # sources/reports are recorded separately and do not build the controller.
    names = subprocess.check_output(['git', 'ls-files', '-z', '--cached', '--others', '--exclude-standard'], cwd=root)
    files = {}
    for name in sorted(set(os.fsdecode(n) for n in names.split(b'\0') if n)):
        if not name.startswith('experiments/'):
            path = root/name
            files[name] = sha(path.read_bytes()) if path.is_file() else '<missing>'
    return {'sha256': sha(json.dumps(files, sort_keys=True).encode()), 'files_sha256': files}


def build_controller(root, output, env, chosen=None):
    before = source_identity(root)
    build_revision = revision(root)
    started = time.perf_counter_ns()
    with (output/'build.log').open('w') as log:
        subprocess.run(['cargo', 'build', '--locked', '--release'], cwd=root, env=env,
                       stdout=log, stderr=subprocess.STDOUT, check=True)
    elapsed = time.perf_counter_ns() - started
    after = source_identity(root)
    if before != after or build_revision != revision(root):
        raise RuntimeError('Checkout changed during controller build; rerun from stable sources')
    built = Path(env['CARGO_TARGET_DIR'])/'release/jaydb2'
    built_hash = sha(built.read_bytes())
    binary = (root/chosen).resolve() if chosen else built
    if sha(binary.read_bytes()) != built_hash:
        raise RuntimeError(f'Chosen executable {binary} differs from a freshly built selected --root; refusing stale/mixed executable')
    return binary, {'controller_executable': str(binary), 'controller_sha256': built_hash,
                    'build_elapsed_ns': elapsed,
                    'controller_build': {'command': ['cargo', 'build', '--locked', '--release'],
                                         'cwd': str(root), 'target_dir': env['CARGO_TARGET_DIR'],
                                         'revision': build_revision, 'source_identity': before,
                                         'chosen_executable_verified_against_fresh_build': chosen is not None}}


def summary(records):
    groups = defaultdict(list)
    for r in records:
        if r['phase'] == 'sample' and r.get('checked', True):
            groups[(r['rows'], r['mode'], r['workload'])].append(r['elapsed_ns'])
    result = []
    for (rows, mode, workload), xs in sorted(groups.items()):
        med = statistics.median(xs)
        mean = statistics.mean(xs)
        sd = statistics.stdev(xs) if len(xs) > 1 else None
        result.append({'rows': rows, 'mode': mode, 'workload': workload, 'n': len(xs),
                       'median_ns': med, 'min_ns': min(xs), 'max_ns': max(xs),
                       'median_absolute_deviation_ns': statistics.median(abs(x-med) for x in xs),
                       'sample_stdev_ns': sd, 'coefficient_of_variation': sd / mean if sd is not None and mean else None})
    return result


def compute(n, seed):
    for _ in range(n):
        seed = (seed * 1664525 + 1013904223) & 0xffffffff
    return seed


def seed_state(rows):
    return {'tables': [{'name': 'bench', 'rows': [
        {'id': f'k{i:04}', 'pad': PAD, 'value': 0} for i in range(rows)]}],
        'users': [{'credential': TOKEN, 'id': 'bench', 'kind': 'user'}]}


def seed_source(rows):
    values = ',\n    '.join('D.Row{"k%04d", [D.Field{"id", D.VText{"k%04d"}}, '
        'D.Field{"pad", D.VText{"%s"}}, D.Field{"value", D.VInt{0, 0}}]}' % (i, i, PAD)
        for i in range(rows))
    return '''import Base
import ./Data.bend as D
import ./Requirements.bend as R
import ./Logic.bend as L
import ./Configuration.bend as C

def state() -> D.State:
  D.State{[D.Table{"bench", [
    ''' + values + '''] }], [D.Row{"bench", [
    D.Field{"credential", D.VText{"benchmark-token"}},
    D.Field{"id", D.VText{"bench"}}, D.Field{"kind", D.VText{"user"}}]}]}

law initial_valid:
  R.Valid(C.config(), state())
def initial_valid():
  L.Both{{==}, Unit{}}
'''


def fill_source():
    return f'''import Base
import ./Data.bend as D
import ./Semantics.bend as S

def key(args: D.Value) -> String:
  match args:
    case D.VText{{k}}: k
    case _: "missing"

def program() -> S.Program:
  S.Program{{ctx => +args => S.Access{{
    D.DefineRow{{D.Application{{"bench"}}, key(args), [
      D.Field{{"id", D.VText{{key(args)}}}},
      D.Field{{"pad", D.VText{{"{PAD}"}}}},
      D.Field{{"value", D.VInt{{0, 0}}}}]}}, r => S.Finish{{D.VInt{{0, 0}}}}}}}}
'''


def proof_source(workload, universal):
    binders = 'ctx, args, ' if universal else ''
    ctx, args = ('ctx', 'args') if universal else ('I.context()', 'I.arguments()')
    depths = {'read': 2, 'write': 2, 'batch': 9, 'compute': 1, 'fill': 2}
    depth = depths[workload]
    finite = 'Unit{}'
    helper = ''
    if workload == 'read':
        finite = 'read_finite'
        helper = """def read_finite(r: S.Return) -> T.Finite(1n, Client.respond(r)):
  match r:
    case S.UnitValue{}: Unit{}
    case S.Datum{obs}:
      match obs:
        case D.RowAbsent{}: Unit{}
        case D.Cell{v}: Unit{}
        case D.Existence{b}: Unit{}
        case D.Count{n}: Unit{}
        case D.Keys{xs}: Unit{}

"""
    else:
        finite = ''.join(f'r{i} => ' for i in range(depth-1)) + finite
    return f'''import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Free.bend as L
import ./Termination.bend as T
import ./Client.bend as Client
import ./Configuration.bend as C
import ./Instance.bend as I
import ./Bindings.bend as B

def B.certificate({binders}s, valid, identity, n):
  L.execution_trace_free_covers_prefixes_and_final(
    S.execute(n, Client.program(), C.schema(), s, {ctx}, {args}),
    C.schema(), C.limits(), S.environment(I.config()), s, {ctx}, B.code(), {args})

{helper}def finite(ctx: D.Context, args: D.Value) ->
  T.Finite({depth}n, S.start(Client.program(), ctx, args)):
  {finite}

def B.terminates(s, ctx, args):
  +context = ctx
  +arguments = args
  T.program_finite({depth}n, Client.program(), C.schema(), s, context, arguments,
    finite(context, arguments))
'''


class Session:
    def __init__(self, binary, folder, root, env, threads, client, records, rows):
        self.client, self.records, self.rows = client, records, rows
        self.errors = (folder/'server.log').open('wb')
        self.process = subprocess.Popen([str(binary), '--configuration', str(folder/'Configuration.bend'),
            '--seed', str(folder/'Seed.bend'), '--threads', str(threads)], cwd=root, env=env,
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=self.errors, start_new_session=True)

    def read(self, size):
        result = bytearray()
        while len(result) < size:
            part = self.process.stdout.read(size-len(result))
            if not part:
                raise RuntimeError('Incomplete server response; see server.log')
            result.extend(part)
        return bytes(result)

    def exchange(self, message, *, phase, mode, workload, args=None, expected=None):
        started = time.perf_counter_ns()
        self.process.stdin.write(message)
        self.process.stdin.flush()
        header = self.read(8)
        size = int.from_bytes(header, 'big')
        if size > 32768:
            raise RuntimeError('Response exceeds configured response limit')
        raw = header + self.read(size)
        elapsed = time.perf_counter_ns() - started
        actual = self.client.unframe(raw)
        ok = (actual == expected if expected is not None else
              actual.get('status') == 'prepared' and isinstance(actual.get('value'), str)
              and len(actual['value']) == 64 and all(c in '0123456789abcdef' for c in actual['value']))
        record = {'rows': self.rows, 'phase': phase, 'mode': mode, 'workload': workload,
                  'arguments': args, 'elapsed_ns': elapsed, 'request_bytes': len(message),
                  'request_sha256': sha(message), 'response_bytes': len(raw),
                  'expected': expected if expected is not None else {'status': 'prepared', 'value': '<64 hex characters>'},
                  'actual': actual, 'checked': ok}
        self.records.append(record)
        with (Path(self.errors.name).parent/'requests.jsonl').open('a') as journal:
            journal.write(json.dumps(record, sort_keys=True) + '\n')
        if not ok:
            raise AssertionError(f'{workload}/{mode}: expected {record["expected"]}, got {actual}; see {self.errors.name}')
        return actual

    def call(self, source, proof, args, **kw):
        message = self.client.frame({'code': source, 'proof': proof, 'credential': TOKEN, 'arguments': args})
        return self.exchange(message, args=args, **kw)

    def prepared(self, op, handle, args=None, proof='', credential=TOKEN, **kw):
        return self.exchange(self.client.prepared_frame(op, handle, credential, args, proof), args=args, **kw)

    def close(self, success):
        try:
            if success:
                self.process.stdin.close()
                status = self.process.wait()
                if status or self.process.stdout.read():
                    raise RuntimeError(f'Unexpected server exit/output ({status}); see {self.errors.name}')
        finally:
            if self.process.poll() is None:
                os.killpg(self.process.pid, signal.SIGKILL)
                self.process.wait()
            self.process.stdin.close()
            self.process.stdout.close()
            self.errors.close()


def run_size(options, root, output, binary, env, client, records, rows):
    folder = output/f'rows-{rows}'
    folder.mkdir()
    shutil.copyfile(SUITE/'Configuration.bend', folder/'Configuration.bend')
    (folder/'Seed.bend').write_text(seed_source(8))
    model = seed_state(rows)
    values = model['tables'][0]['rows']
    state_bytes = client.encode(model)
    print(f'rows={rows}, canonical state={len(state_bytes)} bytes', flush=True)
    session = Session(binary, folder, root, env, options.threads, client, records, rows)
    success = False
    try:
        # Initialization is lazy from the caller's perspective. A rejected
        # authentication probe is the first response, without client admission.
        session.prepared(1, 'no-handle', credential='invalid', phase='setup', mode='startup',
                         workload='authentication_probe', expected={'status': 'authentication', 'value': None})
        fill_handle = None
        if rows > 8:
            source = fill_source()
            proof = proof_source('fill', True)
            (folder/'fill.bend').write_text(source)
            (folder/'fill.universal-proof.bend').write_text(proof)
            fill_handle = session.prepared(0, source, proof=proof, phase='setup', mode='prepare', workload='fill')['value']
            for i in range(8, rows):
                session.prepared(1, fill_handle, f'k{i:04}', phase='setup', mode='prepared', workload='fill',
                                 expected={'status': 'success', 'value': 0})
            session.prepared(2, fill_handle, phase='setup', mode='invalidate', workload='fill',
                             expected={'status': 'invalidated', 'value': None})
            print(f'  populated {rows-8} rows through checked prepared writes', flush=True)
        sources, proofs, handles = {}, {}, {}
        for workload in WORKLOADS:
            sources[workload] = (SUITE/(workload.title()+'.bend')).read_text()
            proofs[workload] = proof_source(workload, False)
            (folder/(workload+'.ordinary-proof.bend')).write_text(proofs[workload])
            universal = proof_source(workload, True)
            (folder/(workload+'.universal-proof.bend')).write_text(universal)
            # Read is the representative repeated preparation measurement.
            count = options.samples if workload == 'read' else 1
            for i in range(count):
                phase = 'sample' if workload == 'read' else 'setup'
                receipt = session.prepared(0, sources[workload], proof=universal, phase=phase,
                                           mode='prepare', workload=workload)
                if workload in handles:
                    session.prepared(2, handles[workload], phase='setup', mode='invalidate', workload=workload,
                                     expected={'status': 'invalidated', 'value': None})
                handles[workload] = receipt['value']
                print(f'  prepared {workload} {i+1}/{count}', flush=True)

        def check_read(key, expected, phase='validation'):
            session.prepared(1, handles['read'], key, phase=phase, mode='prepared', workload='read',
                             expected={'status': 'success', 'value': expected})

        for row in values:
            check_read(row['id'], 0, 'setup')

        # Identical deterministic input order on every invocation; warmups
        # evolve the model too, and are retained but excluded from summaries.
        for mode in ('ordinary', 'prepared'):
            workloads = ('read', 'write') if mode == 'ordinary' else WORKLOADS
            for workload in workloads:
                for i in range(options.warmups + options.samples):
                    phase = 'warmup' if i < options.warmups else 'sample'
                    value = 1000 + (0 if mode == 'ordinary' else 10000) + WORKLOADS.index(workload)*100 + i
                    key = f'k{rows-1:04}'  # Traverse to the end of the row list.
                    if workload == 'read':
                        args, expected = key, values[-1]['value']
                    elif workload == 'write':
                        args, expected = [key, value], value
                    elif workload == 'batch':
                        args, expected = value, value
                    else:
                        args = [options.compute_iterations + i, value]
                        expected = compute(*args)
                    want = {'status': 'success', 'value': expected}
                    kw = dict(phase=phase, mode=mode, workload=workload, expected=want)
                    if mode == 'ordinary':
                        session.call(sources[workload], proofs[workload], args, **kw)
                    else:
                        session.prepared(1, handles[workload], args, **kw)
                    if workload == 'write':
                        values[-1]['value'] = value
                        check_read(key, value)
                    elif workload == 'batch':
                        for row in values[:8]:
                            row['value'] = value
                            check_read(row['id'], value)
                print(f'  checked {mode}/{workload}', flush=True)

        # Meaningful negative/boundary cases use the same admitted programs.
        session.prepared(1, handles['read'], 'missing', phase='validation', mode='prepared', workload='missing_row',
                         expected={'status': 'refusal', 'value': None})
        session.prepared(1, handles['write'], [f'k{rows-1:04}', 'wrong-type'], phase='validation',
                         mode='prepared', workload='invalid_write', expected={'status': 'data', 'value': None})
        check_read(f'k{rows-1:04}', values[-1]['value'])
        session.prepared(1, handles['batch'], 'wrong-type', phase='validation', mode='prepared',
                         workload='invalid_batch', expected={'status': 'data', 'value': None})
        for row in values[:8]:
            check_read(row['id'], row['value'])
        session.prepared(1, handles['compute'], [0, 7], phase='validation', mode='prepared', workload='zero_compute',
                         expected={'status': 'success', 'value': 7})
        session.prepared(1, handles['read'], 'k0000', credential='invalid', phase='validation',
                         mode='prepared', workload='authentication', expected={'status': 'authentication', 'value': None})
        for workload, handle in handles.items():
            session.prepared(2, handle, phase='validation', mode='invalidate', workload=workload,
                             expected={'status': 'invalidated', 'value': None})
        session.prepared(1, handles['read'], 'k0000', phase='validation', mode='prepared', workload='invalidated_handle',
                         expected={'status': 'failure', 'value': None})
        success = True
        return {'rows': rows, 'seed_rows': 8, 'population_prepared_writes': rows-8, 'initial_state_bytes': len(state_bytes), 'initial_state_sha256': sha(state_bytes),
                'final_model_state_sha256': sha(client.encode(model)),
                'seed_source_sha256': sha((folder/'Seed.bend').read_bytes()),
                'validation': 'Every changed row independently read after each write/batch; invalid write rollback read back.'}
    finally:
        session.close(success)


def metadata(root, options, output):
    lock = json.loads((root/'tools/admission/toolchain.lock.json').read_text())
    tool_files = {}
    for name, expected in lock['files'].items():
        path = root/'.tools'/('bend-source-'+lock['version'])/name
        actual = sha(path.read_bytes())
        if actual != expected:
            raise RuntimeError(f'Pinned compiler source changed: {path}')
        tool_files[name] = actual
    for name, path, expected in [
        ('bendtt', root/'.tools'/('bendtt-'+lock['kernelSha256']), lock['kernelSha256']),
        ('bend', root/'.tools'/('bend-'+lock['version'])/'bin/bend', lock['officialBinarySha256'])]:
        actual = sha(path.read_bytes())
        if actual != expected:
            raise RuntimeError(f'Pinned tool changed: {path}')
        tool_files[name] = actual
    cpu = Path('/proc/cpuinfo').read_text()
    cpu_model = next((line.split(':', 1)[1].strip() for line in cpu.splitlines() if line.startswith('model name')), None)
    versions = {name: command(argv) for name, argv in {
        'python': [sys.executable, '--version'], 'node': ['node', '--version'],
        'cargo': ['cargo', '--version'], 'rustc': ['rustc', '--version'],
        'clang': ['/usr/bin/clang-19', '--version']}.items()}
    # Target-local output paths are mandatory, even when suite lives elsewhere.
    return {'schema_version': 1, 'status': 'running', 'started_utc': datetime.now(timezone.utc).isoformat(),
            'anchor': ANCHOR, 'original_reference': REFERENCE,
            'target_root': str(root), 'suite_root': str(SUITE), 'output': str(output),
            'target_revision': revision(root), 'suite_revision': revision(SUITE),
            'suite_files_sha256': {p.name: sha(p.read_bytes()) for p in sorted(SUITE.iterdir())
                                   if p.suffix in ('.py', '.sh', '.bend')},
            'toolchain_lock': lock, 'verified_tool_sha256': tool_files,
            'tools': versions, 'clang_sha256': sha(Path('/usr/bin/clang-19').read_bytes()),
            'hardware': {'platform': platform.platform(), 'machine': platform.machine(),
                         'cpu_model': cpu_model, 'logical_cpus': os.cpu_count(),
                         'affinity': sorted(os.sched_getaffinity(0)),
                         'mem_total': next(line for line in Path('/proc/meminfo').read_text().splitlines()
                                           if line.startswith('MemTotal:')),
                         'load_average_start': os.getloadavg()},
            'settings': {'backend': 'official-bend-c', 'gpu': 'off', 'cpu_workers': options.threads,
                         'requests_in_flight': 1, 'samples': options.samples, 'warmups': options.warmups,
                         'rows': options.rows, 'padding_bytes_per_row': len(PAD),
                         'compute_iterations_base': options.compute_iterations,
                         'limits': {'message': 32768, 'state': 65536, 'response': 32768},
                         'native_compiler': '/usr/bin/clang-19',
                         'native_flags': ['-std=gnu11', '-O2', '-w', '--no-default-config', '<emitted C>',
                                          '-o', '<program>', '-lm', '-pthread'],
                         'stack_soft_limit': 'unlimited',
                         'native_worker_arguments': ['+RTS', '--threads', str(options.threads), '--gpu', 'off', '-RTS'],
                         'heavy_lock': '/tmp/jaydb2-experiments-heavy.lock',
                         'timing': 'perf_counter_ns, immediately before pipe write through complete response bytes; encode/decode/check excluded',
                         'reset': 'fresh process and 8-row checked seed; populate rows 8..N-1 with admitted prepared writes, read back all rows, then evolve model through every warmup/sample write',
                         'preparation_samples': 'repeated read preparation; other workload preparations are setup only',
                         'ordinary_samples': ['read', 'write'],
                         'environment': {k: os.environ[k] for k in ('CC', 'CFLAGS', 'RUSTFLAGS', 'JAYDB_BEND', 'BENDTT')
                                         if k in os.environ}}}


def parse_args(argv=None):
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root', type=Path, default=SUITE.parents[1], help='Target checkout, also owns build/temp/output paths')
    p.add_argument('--output', type=Path, help='New directory inside target checkout (default build/bench-UTC-pid)')
    p.add_argument('--executable', type=Path, help='Verify an existing controller against a fresh selected-root build; relative to --root')
    p.add_argument('--smoke', action='store_true', help='Two samples, no warmup, 8/64 rows, 4096 compute iterations')
    p.add_argument('--samples', type=int)
    p.add_argument('--warmups', type=int)
    p.add_argument('--rows', type=int, nargs='+')
    p.add_argument('--threads', type=int, default=1)
    p.add_argument('--compute-iterations', type=int)
    a = p.parse_args(argv)
    a.samples = a.samples if a.samples is not None else (2 if a.smoke else 3)
    a.warmups = a.warmups if a.warmups is not None else (0 if a.smoke else 1)
    a.rows = a.rows if a.rows is not None else ([8, 64] if a.smoke else [8, 64, 256])
    a.compute_iterations = a.compute_iterations if a.compute_iterations is not None else (4096 if a.smoke else 250000)
    if a.samples < 2 or a.warmups < 0 or not 1 <= a.threads <= 128:
        p.error('Need samples >= 2, warmups >= 0, threads in 1..128')
    if len(set(a.rows)) != len(a.rows) or any(n < 8 or n > 256 for n in a.rows):
        p.error('Row counts must be distinct and in 8..256 (batch updates eight rows)')
    if not 1 <= a.compute_iterations <= 0xffffffff - a.samples - a.warmups:
        p.error('Compute iterations plus sample index must fit positive U32')
    return a


def main(argv=None):
    options = parse_args(argv)
    root = options.root.resolve()
    output = options.output or Path('build')/datetime.now(timezone.utc).strftime(f'bench-%Y%m%dT%H%M%SZ-{os.getpid()}')
    output = (root/output).resolve()
    if not output.is_relative_to(root) or output == root:
        raise ValueError('Output must be inside the target checkout')
    output.mkdir(parents=True, exist_ok=False)
    result, records = {}, []
    try:
        result = metadata(root, options, output)
        (output/'target.patch').write_bytes(subprocess.check_output(['git', 'diff', 'HEAD', '--binary'], cwd=root))
        (output/'suite.patch').write_bytes(subprocess.check_output(['git', 'diff', 'HEAD', '--binary'], cwd=SUITE))
        # Preserve untracked benchmark sources and generated proofs with the run.
        shutil.copytree(SUITE, output/'suite', ignore=shutil.ignore_patterns('evidence', '__pycache__', 'REPORT.md'))
        env = dict(os.environ, TMPDIR=str(output/'tmp'), CARGO_TARGET_DIR=str(root/'build/benchmark-target'),
                   BEND_NO_TELEMETRY='1')
        Path(env['TMPDIR']).mkdir()
        resource.setrlimit(resource.RLIMIT_STACK, (resource.RLIM_INFINITY, resource.getrlimit(resource.RLIMIT_STACK)[1]))
        binary, build_record = build_controller(root, output, env, options.executable)
        result.update(build_record)
        module = importlib.util.spec_from_file_location('benchmark_wire_client', root/'tools/client.py')
        client = importlib.util.module_from_spec(module)
        module.loader.exec_module(client)
        result['states'] = []
        for rows in options.rows:
            result['states'].append(run_size(options, root, output, binary, env, client, records, rows))
        result['status'] = 'passed'
    except BaseException as exc:
        result['status'] = 'failed'
        result['error'] = f'{type(exc).__name__}: {exc}'
        raise
    finally:
        result['requests'] = records
        result['summary'] = summary(records)
        result['finished_utc'] = datetime.now(timezone.utc).isoformat()
        (output/'result.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
        print(f'{result["status"]}: {output / "result.json"}', flush=True)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
