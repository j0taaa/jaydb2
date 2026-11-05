#!/usr/bin/env python3
"""Actual prepared read bursts at a fixed two-core/two-native-worker budget."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import resource
import select
import signal
import statistics
import subprocess
import sys
import threading
import time

ROOT = Path(__file__).resolve().parents[3]
SUITE = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT))
from tools.client import prepared_frame, unframe

spec = importlib.util.spec_from_file_location('baseline', ROOT/'experiments/baseline/bench.py')
baseline = importlib.util.module_from_spec(spec)
spec.loader.exec_module(baseline)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def reference_compute(n, seed):
    """Compose x -> a*x+c modulo 2^32; independent of the native serial loop."""
    if not 0 <= n < 2**32 or not 0 <= seed < 2**32:
        raise ValueError('Recurrence arguments must be U32')
    mask = 2**32-1
    mul, add, step_mul, step_add = 1, 0, 1664525, 1013904223
    while n:
        if n & 1:
            mul, add = step_mul*mul & mask, (step_mul*add+step_add) & mask
        step_mul, step_add = step_mul*step_mul & mask, (step_mul+1)*step_add & mask
        n >>= 1
    return (mul*seed+add) & mask


def bend_literal(text):
    return '"' + ''.join('\\"' if c == '"' else '\\\\' if c == '\\' else
                         f'\\u{{{ord(c):02x}}}' if ord(c) < 32 else c for c in text) + '"'


def prepare(folder):
    folder.mkdir()
    for directory in ('contract', 'src'):
        for source in (ROOT/directory).glob('*.bend'):
            (folder/source.name).write_text(source.read_text().replace('../contract/', './'))
    for name in ('Configuration', 'Seed'):
        (folder/f'{name}.bend').write_bytes((ROOT/f'examples/credential-exchange/{name}.bend').read_bytes())
    code = (SUITE/'ReadCompute.bend').read_text()
    (folder/'Client.bend').write_text(code)
    (folder/'ClientProof.bend').write_bytes((SUITE/'ReadComputeProof.bend').read_bytes())
    (folder/'Environment.bend').write_text('import Base\ndef identity() -> String:\n  "integration-benchmark-proof"\n')
    (folder/'Instance.bend').write_text('import ./Configuration.bend as C\nimport ./Semantics.bend as S\ndef config() -> S.Configuration: C.config()\n')
    (folder/'Bindings.bend').write_text('''import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Requirements.bend as R
import ./Interface.bend as F
import ./ReadOnly.bend as RO
import ./Instance.bend as I
import ./Client.bend as Client

def code() -> String:
  ''' + bend_literal(code) + '''
law certificate:
  @ctx: D.Context -> @args: D.Value -> R.Certifies(I.config(), code(), Client.program(), ctx, args)
law terminates:
  F.ProgramTerminates(I.config(), Client.program())
law read_only:
  RO.Program(Client.program())
''')
    (folder/'Check.bend').write_text('import ./ClientProof.bend as Proof\nimport ./Seed.bend as Seed\n')


def physical_identity(cpu):
    topology = Path(f'/sys/devices/system/cpu/cpu{cpu}/topology')
    return tuple((topology/name).read_text().strip() for name in ('physical_package_id', 'core_id'))


def physical_pair():
    available = sorted(os.sched_getaffinity(0))
    selected, identities = [], set()
    for cpu in available:
        identity = physical_identity(cpu)
        if identity not in identities:
            selected.append(cpu)
            identities.add(identity)
        if len(selected) == 2:
            return available, selected
    raise RuntimeError('Need at least two distinct physical cores in current CPU affinity')


def tree_rss(pid):
    """Sum resident pages of processes, not tasks; shared pages count repeatedly."""
    pending, seen, rss = [pid], set(), 0
    while pending:
        current = pending.pop()
        if current in seen:
            continue
        seen.add(current)
        try:
            rss += int(Path(f'/proc/{current}/statm').read_text().split()[1]) * os.sysconf('SC_PAGE_SIZE')
            for task in Path(f'/proc/{current}/task').glob('*'):
                try:
                    pending.extend(map(int, (task/'children').read_text().split()))
                except FileNotFoundError:
                    pass
        except (FileNotFoundError, ProcessLookupError):
            pass
    return rss


class MemorySample:
    def __init__(self, pid):
        self.pid, self.values = pid, []
        self.stop = threading.Event()
        self.error = None
        self.thread = threading.Thread(target=self.sample, name='benchmark-rss')

    def sample(self):
        try:
            while not self.stop.is_set():
                self.values.append(tree_rss(self.pid))
                self.stop.wait(.01)
        except BaseException as error:
            self.error = error

    def __enter__(self):
        self.thread.start()
        return self

    def __exit__(self, *_):
        self.stop.set()
        self.thread.join()
        if self.error is not None:
            raise self.error


class Session:
    def __init__(self, binary, folder, workers, cpus, env):
        self.workers = workers
        self.errors = (folder/f'server-{workers}.log').open('wb')
        self.process = subprocess.Popen(['taskset', '--cpu-list', ','.join(map(str, cpus)), str(binary),
            '--configuration', str(folder/'Configuration.bend'), '--seed', str(folder/'Seed.bend'),
            '--threads', '2', '--read-workers', str(workers)], cwd=ROOT, env=env,
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=self.errors, start_new_session=True)
        try:
            started = time.perf_counter_ns()
            self.send(prepared_frame(3, (SUITE/'ReadCompute.bend').read_text(), 'alice-token',
                                     proof=(SUITE/'ReadComputeProof.bend').read_text()))
            receipt = self.response()
            self.preparation_ns = time.perf_counter_ns() - started
            if receipt.get('status') != 'prepared' or not isinstance(receipt.get('value'), str):
                raise AssertionError(f'Checked read preparation failed: {receipt}; see {self.errors.name}')
            self.handle = receipt['value']
        except BaseException:
            self.close()
            raise

    def send(self, message):
        self.process.stdin.write(message)
        self.process.stdin.flush()

    def read(self, size):
        result = bytearray()
        deadline = time.monotonic() + 180
        while len(result) < size:
            remaining = deadline-time.monotonic()
            if remaining <= 0 or not select.select([self.process.stdout], [], [], remaining)[0]:
                raise RuntimeError(f'Response timeout; see {self.errors.name}')
            chunk = os.read(self.process.stdout.fileno(), size-len(result))
            if not chunk:
                raise RuntimeError(f'Incomplete response; see {self.errors.name}')
            result.extend(chunk)
        return bytes(result)

    def response(self):
        header = self.read(8)
        size = int.from_bytes(header, 'big')
        if size > 32768:
            raise RuntimeError('Response exceeded canonical configured bound')
        return unframe(header+self.read(size))

    def burst(self, arguments, expected):
        frames = [prepared_frame(1, self.handle, 'alice-token', value) for value in arguments]
        message = b''.join(frames)
        if len(message) > os.fpathconf(self.process.stdin.fileno(), 'PC_PIPE_BUF'):
            raise RuntimeError('Burst no longer fits one atomic pipe write')
        before = tree_rss(self.process.pid)
        samples, latencies = None, []
        with MemorySample(self.process.pid) as samples:
            started = time.perf_counter_ns()
            self.send(message)
            for value in expected:
                actual = self.response()
                latencies.append(time.perf_counter_ns()-started)
                if actual != {'status': 'success', 'value': ['alice-token', value]}:
                    raise AssertionError(f'Expected credential and checksum {value}, got {actual}')
            elapsed = time.perf_counter_ns()-started
        return {'elapsed_ns': elapsed, 'requests_per_second': len(frames)*1e9/elapsed,
                'response_latency_ns': latencies, 'request_bytes': len(message),
                'checked_responses': len(frames), 'rss_before_bytes': before,
                'rss_after_drained_bytes': tree_rss(self.process.pid),
                'sampled_tree_peak_rss_bytes': max(samples.values, default=before),
                'rss_samples': len(samples.values)}

    def close(self):
        try:
            if self.process.poll() is None:
                self.process.stdin.close()
                if self.process.wait(timeout=30) or self.process.stdout.read():
                    raise RuntimeError(f'Unexpected server termination; see {self.errors.name}')
        finally:
            if self.process.poll() is None:
                os.killpg(self.process.pid, signal.SIGKILL)
                self.process.wait()
            self.process.stdin.close()
            self.process.stdout.close()
            self.errors.close()


def summaries(records):
    result = []
    for count in sorted({r['iterations_base'] for r in records}):
        for workers in (1, 2):
            selected = [r for r in records if r['phase'] == 'sample' and r['iterations_base'] == count
                        and r['read_workers'] == workers]
            latencies = sorted(t for r in selected for t in r['response_latency_ns'])
            result.append({'iterations_base': count, 'read_workers': workers, 'bursts': len(selected),
                'median_requests_per_second': statistics.median(r['requests_per_second'] for r in selected),
                'median_burst_ns': statistics.median(r['elapsed_ns'] for r in selected),
                'min_burst_ns': min(r['elapsed_ns'] for r in selected),
                'max_burst_ns': max(r['elapsed_ns'] for r in selected),
                'burst_median_absolute_deviation_ns': statistics.median(
                    abs(r['elapsed_ns']-statistics.median(x['elapsed_ns'] for x in selected)) for r in selected),
                'response_latency_p50_ns': statistics.median(latencies),
                'response_latency_p95_ns': latencies[(95*len(latencies)+99)//100-1],
                'max_sampled_tree_rss_bytes': max(r['sampled_tree_peak_rss_bytes'] for r in selected),
                'max_drained_rss_bytes': max(r['rss_after_drained_bytes'] for r in selected)})
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path('build/integration/concurrency-benchmark'))
    parser.add_argument('--check-only', action='store_true')
    parser.add_argument('--executable', type=Path)
    parser.add_argument('--samples', type=int, default=7)
    parser.add_argument('--burst', type=int, default=8)
    parser.add_argument('--iterations', type=int, nargs='+', default=[0, 250000, 1000000])
    args = parser.parse_args()
    if args.samples < 5 or not 2 <= args.burst <= 8 or any(not 0 <= n < 2**32-1 for n in args.iterations):
        parser.error('Need samples >=5, burst 2..8, iterations 0..2^32-2')
    output = (ROOT/args.output).resolve()
    if not output.is_relative_to(ROOT) or output.exists():
        parser.error('Output must be a fresh directory inside this worktree')
    output.mkdir(parents=True)
    (output/'tmp').mkdir()
    fixture = output/'fixture'
    prepare(fixture)
    env = dict(os.environ, BENDRTS='', TMPDIR=str(output/'tmp'), BEND_NO_TELEMETRY='1',
               CARGO_TARGET_DIR=str(ROOT/'build/integration-benchmark-target'))
    if args.check_only:
        subprocess.run([sys.executable, '-B', str(ROOT/'tools/check.py'), str(fixture/'Check.bend')],
                       cwd=ROOT, env=env, check=True)
        print(f'Both official fixture checks passed: {fixture}')
        return
    available, cpus = physical_pair()
    # Keep the client, independent oracle and RSS sampler off measured cores.
    selected_topology = {physical_identity(cpu) for cpu in cpus}
    others = {cpu for cpu in available if physical_identity(cpu) not in selected_topology}
    if others:
        os.sched_setaffinity(0, others)
    resource.setrlimit(resource.RLIMIT_STACK, (resource.RLIM_INFINITY, resource.RLIM_INFINITY))
    binary, provenance = baseline.build_controller(ROOT, output, env, args.executable)
    benchmark_sources = [SUITE/name for name in ('ReadCompute.bend', 'ReadComputeProof.bend', 'bench.py', 'run.sh', 'test_bench.py')]
    benchmark_hashes = {p.name: sha(p.read_bytes()) for p in benchmark_sources}
    result = {'created_at': datetime.now(timezone.utc).isoformat(), 'controller': provenance,
        'settings': {'native_threads_total': 2, 'read_workers': [1, 2], 'service_cpus': cpus,
                     'runner_cpus': sorted(os.sched_getaffinity(0)),
                     'service_cpu_topology': {str(cpu): physical_identity(cpu) for cpu in cpus},
                     'runner_avoids_service_core_siblings': bool(others), 'burst': args.burst,
                     'samples': args.samples, 'warmup_bursts': 1, 'iterations': args.iterations,
                     'storage': False, 'timing_log': False, 'rss_interval_seconds': .01},
        'hardware': {'platform': os.uname()._asdict() if hasattr(os.uname(), '_asdict') else list(os.uname()),
                     'lscpu': subprocess.check_output(['lscpu', '-J'], text=True)},
        'benchmark_source_sha256': benchmark_hashes,
        'fixture_sha256': {p.name: sha(p.read_bytes()) for p in (SUITE/'ReadCompute.bend', SUITE/'ReadComputeProof.bend', fixture/'Configuration.bend', fixture/'Seed.bend')},
        'toolchain_lock_sha256': sha((ROOT/'tools/admission/toolchain.lock.json').read_bytes()),
        'limitations': ['End-to-end FIFO latencies include queue waiting; each burst is submitted together.',
                       'Fixed native budget is two workers and two physical cores, including host overhead.',
                       'Sampled descendant RSS counts shared pages repeatedly and may miss brief peaks.',
                       'No storage or timing log is enabled; only a small two-user state is measured.',
                       'Serial recurrence exposes independent-request parallelism; it does not speed up one request.',
                       'Naturally underfilled first batches are included; no injected scheduler gates.'],
        'records': []}
    sessions = {}
    try:
        for workers in (1, 2):
            sessions[workers] = Session(binary, fixture, workers, cpus, env)
        result['preparation_ns'] = {str(k): v.preparation_ns for k, v in sessions.items()}
        for count in args.iterations:
            for round_number in range(args.samples+1):
                arguments = [[count+(round_number % 2 if count else 0), 7+17*round_number+i]
                             for i in range(args.burst)]
                expected = [reference_compute(n, seed) for n, seed in arguments]
                order = (1, 2) if round_number % 2 == 0 else (2, 1)
                for workers in order:
                    record = sessions[workers].burst(arguments, expected)
                    record.update(iterations_base=count, arguments=arguments, expected=expected,
                                  phase='warmup' if round_number == 0 else 'sample',
                                  round=round_number, read_workers=workers)
                    result['records'].append(record)
                    with (output/'requests.jsonl').open('a') as log:
                        log.write(json.dumps(record, sort_keys=True)+'\n')
                print(f'iterations={count}, paired round={round_number} passed', flush=True)
        if provenance['controller_build']['source_identity'] != baseline.source_identity(ROOT):
            raise RuntimeError('Production sources changed during benchmark')
        if provenance['controller_sha256'] != sha(binary.read_bytes()):
            raise RuntimeError('Controller executable changed during benchmark')
        if benchmark_hashes != {p.name: sha(p.read_bytes()) for p in benchmark_sources}:
            raise RuntimeError('Benchmark sources changed during measurement')
        result['summary'] = summaries(result['records'])
        result['paired_comparison'] = []
        for count in args.iterations:
            selected = {(r['round'], r['read_workers']): r['elapsed_ns'] for r in result['records']
                        if r['phase'] == 'sample' and r['iterations_base'] == count}
            ratios = [selected[(number, 1)]/selected[(number, 2)] for number in range(1, args.samples+1)]
            result['paired_comparison'].append({'iterations_base': count,
                'throughput_ratio_parallel_over_serial': ratios,
                'median_throughput_ratio_parallel_over_serial': statistics.median(ratios)})
        result['checked_responses'] = sum(r['checked_responses'] for r in result['records'])
    except BaseException as error:
        result['error'] = repr(error)
        raise
    finally:
        try:
            close_errors = []
            for session in sessions.values():
                try:
                    session.close()
                except BaseException as error:
                    close_errors.append(error)
            if close_errors:
                result['close_errors'] = [repr(error) for error in close_errors]
                raise close_errors[0]
        finally:
            (output/'result.json').write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
    print(json.dumps(result['summary'], indent=2))
    print(output/'result.json')


if __name__ == '__main__':
    main()
