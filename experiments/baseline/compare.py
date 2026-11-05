#!/usr/bin/env python3
"""Small alternating-order tiny prepared read comparison. Use compare.sh."""
import argparse
from datetime import datetime, timezone
import importlib.util
import json
import os
from pathlib import Path
import resource
import shutil
import subprocess

import bench


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--anchor-root', type=Path, required=True)
    p.add_argument('--anchor-executable', type=Path, required=True)
    p.add_argument('--candidate-root', type=Path, required=True)
    p.add_argument('--candidate-executable', type=Path, required=True)
    p.add_argument('--samples', type=int, default=7)
    p.add_argument('--warmups', type=int, default=2)
    p.add_argument('--threads', type=int, default=1)
    p.add_argument('--name', default=datetime.now(timezone.utc).strftime('interleaved-%Y%m%dT%H%M%SZ'))
    args = p.parse_args()
    if Path(args.name).name != args.name or args.name in ('', '.', '..'):
        p.error('--name must be a directory name')
    # Reuse the standard driver's validation and settings metadata.
    options = bench.parse_args(['--rows', '8', '--samples', str(args.samples),
                                '--warmups', str(args.warmups), '--threads', str(args.threads)])
    resource.setrlimit(resource.RLIMIT_STACK, (resource.RLIM_INFINITY, resource.getrlimit(resource.RLIMIT_STACK)[1]))
    sessions, results, outputs = [], [], []
    passed = False
    try:
        for side, root, executable in [('anchor', args.anchor_root, args.anchor_executable),
                                       ('candidate', args.candidate_root, args.candidate_executable)]:
            root = root.resolve()
            output = root/'build'/f'{args.name}-{side}'
            output.mkdir(parents=True, exist_ok=False)
            outputs.append(output)
            result = bench.metadata(root, options, output)
            result['comparison'] = {'side': side, 'scope': 'tiny prepared read only',
                                    'schedule': 'alternate AB then BA each round; one request in flight',
                                    'peer_root': str((args.candidate_root if side == 'anchor' else args.anchor_root).resolve())}
            result['requests'] = []
            results.append(result)
            result['settings']['compute_iterations_base'] = None
            result['settings']['ordinary_samples'] = []
            result['settings']['preparation_samples'] = 'one untimed setup preparation'
            shutil.copytree(bench.SUITE, output/'suite', ignore=shutil.ignore_patterns('evidence', '__pycache__', 'REPORT.md'))
            (output/'target.patch').write_bytes(subprocess.check_output(['git', 'diff', 'HEAD', '--binary'], cwd=root))
            (output/'suite.patch').write_bytes(subprocess.check_output(['git', 'diff', 'HEAD', '--binary'], cwd=bench.SUITE))
            env = dict(os.environ, TMPDIR=str(output/'tmp'), BEND_NO_TELEMETRY='1',
                       CARGO_TARGET_DIR=str(root/'build/benchmark-target'))
            Path(env['TMPDIR']).mkdir()
            binary, build_record = bench.build_controller(root, output, env, executable)
            result.update(build_record)
            shutil.copyfile(bench.SUITE/'Configuration.bend', output/'Configuration.bend')
            (output/'Seed.bend').write_text(bench.seed_source(8))
            proof = bench.proof_source('read', True)
            (output/'read.universal-proof.bend').write_text(proof)
            module = importlib.util.spec_from_file_location('wire_'+side, root/'tools/client.py')
            client = importlib.util.module_from_spec(module)
            module.loader.exec_module(client)
            state = client.encode(bench.seed_state(8))
            result['states'] = [{'rows': 8, 'initial_state_bytes': len(state), 'initial_state_sha256': bench.sha(state)}]
            session = bench.Session(binary, output, root, env, args.threads, client, result['requests'], 8)
            sessions.append(session)
            session.prepared(1, 'unknown', credential='invalid', phase='setup', mode='startup', workload='authentication_probe',
                             expected={'status': 'authentication', 'value': None})
            receipt = session.prepared(0, (bench.SUITE/'Read.bend').read_text(), proof=proof,
                                       phase='setup', mode='prepare', workload='read')
            result['handle'] = receipt['value']
            print(f'{side} ready: {output}', flush=True)
        for i in range(args.warmups + args.samples):
            phase = 'warmup' if i < args.warmups else 'sample'
            for side in ((0, 1) if i % 2 == 0 else (1, 0)):
                sessions[side].prepared(1, results[side]['handle'], 'k0007', phase=phase,
                                        mode='prepared', workload='read', expected={'status': 'success', 'value': 0})
            print(f'checked interleaved round {i+1}', flush=True)
        passed = True
    finally:
        # Write evidence even if preparation or an expected output fails.
        cleanup_errors = []
        try:
            for session in sessions:
                try:
                    session.close(passed)
                except Exception as exc:
                    cleanup_errors.append(str(exc))
                    passed = False
        finally:
            for result, output in zip(results, outputs):
                result.pop('handle', None)
                result['summary'] = bench.summary(result['requests'])
                result['status'] = 'passed' if passed else 'failed'
                if cleanup_errors:
                    result['cleanup_errors'] = cleanup_errors
                result['finished_utc'] = datetime.now(timezone.utc).isoformat()
                (output/'result.json').write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
                print(f'{result["status"]}: {output / "result.json"}', flush=True)
        if cleanup_errors:
            raise RuntimeError('; '.join(cleanup_errors))


if __name__ == '__main__':
    main()
