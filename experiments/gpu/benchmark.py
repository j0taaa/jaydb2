#!/usr/bin/env python3
"""Complete, unwrapped prepared requests. Run under the shared heavy lock."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import statistics
import subprocess
import time

from tests.service.test_end_to_end import ROOT, Server
from tests.service.test_gpu import CODE, PROOF, oracle


def timed(fn):
    start = time.perf_counter_ns()
    result = fn()
    return result, (time.perf_counter_ns()-start)/1e6


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--repeats', type=int, default=3)
    parser.add_argument('--large-depth', type=int, default=16)
    args = parser.parse_args()
    expected = {d: oracle(d) for d in [2, args.large_depth]}
    output = {'revision': subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(),
        'dirty': bool(subprocess.check_output(['git', 'status', '--porcelain'])),
        'toolchain': json.loads((ROOT/'tools/admission/toolchain.lock.json').read_text()),
        'machine': platform.uname()._asdict(), 'cpu_workers': 8, 'gpu_worker_cap': 1,
        'gpu_inventory': subprocess.check_output(['nvidia-smi', '--query-gpu=name,driver_version,memory.total', '--format=csv,noheader'], text=True).strip(),
        'source_sha256': hashlib.sha256(CODE.encode()).hexdigest(),
        'cuda_compiler': subprocess.check_output(['nvcc', '--version'], text=True).strip(), 'runs': []}
    for gpu in [False, True]:
        startup = time.perf_counter_ns()
        server = Server(ROOT/'examples/access', options=['--threads', '8', '--gpu', '512' if gpu else 'off'])
        try:
            # Separate initialization/checking from preparation/first compilation.
            assert server.prepared(0, CODE, 'invalid', proof=PROOF)['status'] == 'authentication'
            initialized_ms = (time.perf_counter_ns()-startup)/1e6
            receipt, prepare_ms = timed(lambda: server.prepared(0, CODE, 'alice-token', proof=PROOF))
            assert receipt['status'] == 'prepared', server.diagnostics()
            handle, credential = receipt['value'], 'alice-token'
            records = []
            for depth in [2, args.large_depth]:
                samples = []
                for _ in range(args.repeats):
                    replacement = 'x'*depth
                    result, elapsed = timed(lambda: server.prepared(1, handle, credential, replacement))
                    assert result == {'status': 'success', 'value': expected[depth]}, (result, server.diagnostics())
                    samples.append(elapsed)
                    credential = replacement
                records.append({'depth': depth, 'leaves': 1 << depth, 'leaf_rounds': 64,
                    'result': expected[depth], 'request_ms': samples, 'median_ms': statistics.median(samples)})
            output['runs'].append({'backend': 'cuda' if gpu else 'cpu', 'startup_ms': initialized_ms,
                'first_preparation_ms': prepare_ms, 'prepared_requests': records})
            server.finish()
        finally:
            server.close()
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(output, indent=2)+'\n')
        print(json.dumps(output['runs'][-1]), flush=True)


if __name__ == '__main__':
    main()
