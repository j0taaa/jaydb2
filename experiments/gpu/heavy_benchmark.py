#!/usr/bin/env python3
"""One focused heavy CPU/CUDA comparison; invoke with the shared heavy lock.
Small independent oracle; heavy exact output/state reference is unwrapped CPU.
Native-worker timings are separate from preparation and complete requests.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import statistics
import subprocess
import tempfile
import time

from tests.service.test_end_to_end import ROOT, Server
from tests.service.test_gpu import PROOF
from tools.client import encode, prepared_frame, unframe
from experiments.gpu.benchmark import timed

CODE = (ROOT/'experiments/gpu/HeavyClient.bend').read_text()


def oracle(depth):
    total = 0
    for seed in range(1 << depth):
        x = seed
        for _ in range(depth*4096):
            x = ((x ^ (x >> 16))*1664525 + 1013904223) & 0xffffffff
        total = (total+x) & 0xffffffff
    return total


def state(credential):
    return {'tables': [], 'users': [
        {'credential': credential, 'id': 'alice', 'kind': 'user'},
        {'credential': 'bob-token', 'id': 'bob', 'kind': 'user'}]}


def packet(state_bytes, body):
    return len(state_bytes).to_bytes(8, 'big')+state_bytes+body


def manifest_check(native, gpu):
    report = json.loads(Path(str(native)+'.json').read_text())
    for path, key in [(native, 'executableSha256'), *([(Path(str(native)+'.gpu'), 'gpuSha256')] if gpu else [])]:
        assert path.is_file() and not path.is_symlink()
        assert hashlib.sha256(path.read_bytes()).hexdigest() == report[key]
    assert report['backend'] == ('cuda' if gpu else 'cpu')


def native_trial(native, handle, depth, gpu):
    # This independent child consumes a known seed snapshot; its proposed state
    # never publishes to the host. The host request trials follow separately.
    body = prepared_frame(1, handle, 'alice-token', 'x'*depth)[10:]
    manifest_check(native, gpu)
    result, elapsed = timed(lambda: subprocess.run([str(native), '+RTS', '--threads', '8',
        '--gpu', '512MB' if gpu else 'off', '-RTS'], input=packet(encode(state('alice-token')), body),
        capture_output=True, env=dict(os.environ, BENDRTS=''), timeout=120, check=True))
    assert b'bend: compiling the GPU program' not in result.stderr
    manifest_check(native, gpu)
    assert result.stdout[0] == 1
    length = int.from_bytes(result.stdout[1:9], 'big')
    proposed = result.stdout[9:9+length]
    assert proposed == encode(state('x'*depth)), 'native proposal changed unrelated state'
    response = unframe(result.stdout[9+length:])
    assert response['status'] == 'success', response
    return response['value'], elapsed


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--repeats', type=int, default=2)
    parser.add_argument('--large-depth', type=int, default=16)
    args = parser.parse_args()
    assert 3 <= args.large_depth <= 18 and 1 <= args.repeats <= 3
    depths = [2, args.large_depth]
    reference = {2: oracle(2)}
    output = {'revision': subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(),
        'dirty': bool(subprocess.check_output(['git', 'status', '--porcelain'])),
        'source_sha256': hashlib.sha256(CODE.encode()).hexdigest(), 'rounds_per_depth': 4096,
        'cpu_workers': 8, 'gpu_mib': 512, 'gpu_worker_cap': 1,
        'independent_oracle': {'depth': 2, 'rounds': 8192, 'result': reference[2]},
        'reference_scope': 'Small Python oracle; exact heavy checksum and complete native state compared with real unwrapped CPU',
        'runs': []}
    for gpu in [False, True]:
        server = Server(ROOT/'examples/access', options=['--threads', '8', '--gpu', '512' if gpu else 'off'])
        try:
            assert server.prepared(0, CODE, 'invalid', proof=PROOF)['status'] == 'authentication'
            receipt, preparation = timed(lambda: server.prepared(0, CODE, 'alice-token', proof=PROOF))
            assert receipt['status'] == 'prepared', server.diagnostics()
            handle, credential = receipt['value'], 'alice-token'
            private = next(Path(tempfile.gettempdir()).glob(f'jaydb2-{server.process.pid}-*'))
            native, = private.glob('request-*/*.program')
            records = []
            for depth in depths:
                value, native_ms = native_trial(native, handle, depth, gpu)
                if depth not in reference: reference[depth] = value
                assert value == reference[depth], (gpu, depth, value, reference[depth])
                samples = []
                for _ in range(args.repeats):
                    result, elapsed = timed(lambda: server.prepared(1, handle, credential, 'x'*depth))
                    assert result == {'status': 'success', 'value': reference[depth]}, (result, server.diagnostics())
                    samples.append(elapsed)
                    credential = 'x'*depth
                records.append({'depth': depth, 'leaves': 1 << depth, 'rounds_per_leaf': depth*4096,
                    'total_mixing_rounds': (1 << depth)*depth*4096, 'result': value,
                    'native_worker_ms': native_ms, 'complete_request_ms': samples,
                    'median_complete_request_ms': statistics.median(samples)})
            output['runs'].append({'backend': 'cuda' if gpu else 'cpu',
                'first_preparation_ms': preparation, 'records': records})
            server.finish()
        finally:
            server.close()
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(output, indent=2)+'\n')
        print(json.dumps(output['runs'][-1]), flush=True)


if __name__ == '__main__':
    main()
