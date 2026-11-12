#!/usr/bin/env python3
"""Focused bang-program comparison. Caller holds the heavy lock and fixed clock.
Native-worker wall time includes process/device startup, checked computation,
proposal encoding and process exit. Complete request time additionally includes
fresh host authentication, bundle integrity, checked selection and publication.
"""
import argparse
import hashlib
import json
import os
import re
from pathlib import Path
import statistics
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from tests.service.test_end_to_end import Server
from tests.service.test_gpu import PROOF, StateFeed
from tools.client import encode, prepared_frame, unframe
from paper.bench.frequency import observe
from paper.bench.run import metadata

CODE = (ROOT/'experiments/gpu/HeavyClient.bend').read_text()


def oracle(depth):
    # Independent bottom-up Python/NumPy arithmetic, no Bend tree, GPU or native
    # result as reference. Vectorize ONLY the seeds; perform every mixing round.
    import numpy as np
    values = np.arange(1 << depth, dtype=np.uint32)
    scratch = np.empty_like(values)
    for _ in range(depth * 4096):
        np.right_shift(values, 16, out=scratch)
        np.bitwise_xor(values, scratch, out=values)
        np.multiply(values, np.uint32(1664525), out=values)
        np.add(values, np.uint32(1013904223), out=values)
    return int(values.sum(dtype=np.uint64)) & 0xffffffff


def state(credential):
    return {'tables': [], 'users': [
        {'credential': credential, 'id': 'alice', 'kind': 'user'},
        {'credential': 'bob-token', 'id': 'bob', 'kind': 'user'}]}


def packet(first, rest):
    return len(first).to_bytes(8, 'big') + first + rest


def split(data):
    size = int.from_bytes(data[:8], 'big')
    assert len(data) >= size+8
    return data[8:8+size], data[8+size:]


def timed(operation):
    start = time.perf_counter_ns()
    result = operation()
    return result, (time.perf_counter_ns()-start)/1e6


def validate(native, gpu):
    report = json.loads(Path(str(native)+'.json').read_text())
    assert report['backend'] == ('cuda' if gpu else 'cpu')
    assert report.get('hasBangs', True)
    assert re.search(rb'^#define\s+BANGS\s+[1-9]', (native.parent/'checked.c').read_bytes(), re.M)
    for path, key in [(native, 'executableSha256'), *([(Path(str(native)+'.gpu'), 'gpuSha256')] if gpu else [])]:
        assert path.is_file() and not path.is_symlink()
        assert hashlib.sha256(path.read_bytes()).hexdigest() == report[key]
    return report


def run_native(native, data, threads, gpu):
    result = subprocess.run([str(native), '+RTS', '--threads', str(threads),
        '--gpu', '512MB' if gpu else 'off', '-RTS'], input=data,
        capture_output=True, env=dict(os.environ, BENDRTS=''), timeout=180, check=True)
    assert b'bend: compiling the GPU program' not in result.stderr
    return result.stdout


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--repeats', type=int, default=3)
    parser.add_argument('--large-depth', type=int, default=16)
    args = parser.parse_args()
    assert 3 <= args.large_depth <= 16 and 1 <= args.repeats <= 5
    assert 'JAYDB_BENCH_FREQUENCY_ORIGINAL' in os.environ, 'use fixed-clock.sh'
    assert not os.environ.get('LD_PRELOAD'), 'measure the unwrapped real runtime'
    depths = [2, args.large_depth]
    reference = {depth: oracle(depth) for depth in depths}
    # Cross-check vectorized arithmetic with plain Python at the small size.
    scalar = 0
    for seed in range(4):
        value = seed
        for _ in range(8192):
            value = ((value ^ (value >> 16))*1664525 + 1013904223) & 0xffffffff
        scalar = (scalar + value) & 0xffffffff
    assert reference[2] == scalar
    output = dict(metadata=metadata(1),
        revision=subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(),
        dirty=subprocess.check_output(['git', 'status', '--porcelain'], text=True).splitlines(),
        utc=time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()), frequency=observe(),
        frequency_original=json.loads(Path(os.environ['JAYDB_BENCH_FREQUENCY_ORIGINAL']).read_text()),
        clock='time.perf_counter_ns (wall clock)', warmups=1, repeats=args.repeats,
        cpu=next(x.split(':',1)[1].strip() for x in Path('/proc/cpuinfo').read_text().splitlines() if x.startswith('model name')),
        gpu=subprocess.check_output(['nvidia-smi', '--query-gpu=name,driver_version,memory.total', '--format=csv'], text=True),
        clang=subprocess.check_output(['/usr/bin/clang-19', '--version'], text=True).splitlines()[0],
        toolchain=json.loads((ROOT/'tools/admission/toolchain.lock.json').read_text()),
        binary_sha256=hashlib.sha256((ROOT/'target/release/jaydb2').read_bytes()).hexdigest(),
        fixture_sha256={name: hashlib.sha256((ROOT/name).read_bytes()).hexdigest() for name in [
            'experiments/gpu/HeavyClient.bend', 'experiments/gpu/ClientProof.bend', 'paper/bench/gpu_programs.py']},
        numpy_version=__import__('numpy').__version__, small_scalar_oracle=scalar,
        gpu_mib=512, gpu_worker_cap=1, oracle=reference, oracle_method='Python/NumPy uint32, all seeds and all rounds; uint64 sum reduced modulo 2^32',
        lock='/tmp/jaydb2-experiments-heavy.lock', runs=[])
    for name, threads, gpu in [('cpu-1', 1, False), ('cpu-16', 16, False), ('cuda', 1, True)]:
        with tempfile.TemporaryDirectory(prefix='gpu-bench-') as tmp:
            feed = StateFeed(Path(tmp)/'admin.sock')
            server = Server(ROOT/'examples/access', options=['--threads', str(threads),
                '--gpu', '512' if gpu else 'off', '--inspect-socket', str(Path(tmp)/'admin.sock')])
            try:
                assert server.prepared(0, CODE, 'invalid', proof=PROOF)['status'] == 'authentication'
                receipt, preparation = timed(lambda: server.prepared(0, CODE, 'alice-token', proof=PROOF))
                assert receipt['status'] == 'prepared', server.diagnostics()
                handle, credential = receipt['value'], 'alice-token'
                private = next(Path(tempfile.gettempdir()).glob(f'jaydb2-{server.process.pid}-*'))
                native, = private.glob('request-*/*.program')
                artifact = validate(native, gpu)
                # Obtain canonical registry bytes from the SAME checked controller
                # and admitted tuple; do not invent a registry serialization.
                control, = (private/'control').glob('*.program')
                registered = run_native(control, packet(encode([handle, 'universal', CODE, PROOF]),
                    packet(b'', packet(encode(state('alice-token')),
                        prepared_frame(0, CODE, 'alice-token', proof=PROOF)[8:]))), 1, False)
                assert registered[0] == 1
                selected, rest = split(registered[1:])
                registry, _ = split(rest)
                assert selected.decode() == handle
                records = []
                for depth in depths:
                    data = packet(registry, packet(encode(state('alice-token')),
                        prepared_frame(1, handle, 'alice-token', 'x'*depth)[8:]))
                    native_samples, complete_samples = [], []
                    for trial in range(args.repeats+1):
                        validate(native, gpu)
                        proposed, elapsed = timed(lambda: run_native(native, data, threads, gpu))
                        validate(native, gpu)
                        assert proposed[0] == 1
                        proposed_state, response = split(proposed[1:])
                        assert proposed_state == encode(state('x'*depth))
                        assert unframe(response) == {'status': 'success', 'value': reference[depth]}
                        if trial: native_samples.append(elapsed)
                    for trial in range(args.repeats+1):
                        result, elapsed = timed(lambda: server.prepared(1, handle, credential, 'x'*depth))
                        assert result == {'status': 'success', 'value': reference[depth]}, server.diagnostics()
                        credential = 'x'*depth
                        if trial: complete_samples.append(elapsed)
                    records.append(dict(depth=depth, leaves=1 << depth, rounds_per_leaf=depth*4096,
                        total_mixing_rounds=(1 << depth)*depth*4096, result=reference[depth],
                        native_worker_ms=native_samples, complete_request_ms=complete_samples,
                        median_native_worker_ms=statistics.median(native_samples),
                        median_complete_request_ms=statistics.median(complete_samples)))
                server.finish()
                feed.finish()
                # Every complete publication has exact independently specified state.
                expected = [state('alice-token')]*3
                for depth in depths: expected.extend([state('x'*depth)]*(args.repeats+1))
                published = [s for s, e in zip(feed.states, feed.events)
                             if e['event'] in ['initialized', 'completed']]
                assert published == expected, 'complete published state differs'
                output['runs'].append(dict(backend=name, threads=threads, first_preparation_ms=preparation,
                    artifact=artifact, records=records, full_published_states=published))
            finally:
                server.close()
        assert len({run['artifact']['sourceSha256'] for run in output['runs']}) == 1, 'different emitted C'
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(output, indent=2)+'\n')
        print(json.dumps(output['runs'][-1]), flush=True)


if __name__ == '__main__':
    main()
