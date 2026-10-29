"""Causal comparison of literal v4-review fixtures on v3, v4 and current code.

Timeouts only bound harness cleanup. They are never a public resource verdict.
All compilation and raw logs live in a fresh temporary directory.
"""
from pathlib import Path
import hashlib
import importlib.util
import json
import subprocess
import tarfile
import tempfile

ROOT = Path(__file__).resolve().parents[2]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main():
    work = Path(tempfile.mkdtemp(prefix='jaydb2-retention-v5-causal-'))
    manifests = {}
    tracers = {}
    for version in ('v3', 'v4'):
        manifest_path = ROOT/f'tests/accounting/checkpoints/retention_{version}.json'
        manifest = json.loads(manifest_path.read_text())
        archive = ROOT/manifest['archive']
        assert sha(archive) == manifest['archiveSha256']
        destination = work/version
        with tarfile.open(archive) as source:
            source.extractall(destination, filter='data')
        assert all(sha(destination/p) == digest for p, digest in manifest['files'].items())
        builder = load(destination/'tools/accounting/build.py', version+'_build')
        tracers[version] = builder.build(work/(version+'-build'))[1]
        manifests[version] = {'archive_sha256': sha(archive), 'manifest_sha256': sha(manifest_path)}
    tracers['current'] = load(ROOT/'tools/accounting/build.py', 'current_build').build(work/'current-build')[1]
    subprocess.run(['/usr/bin/clang-19', '-std=c11', '-O2', '-g', '-Wall', '-Wextra', '-Werror', '-pthread',
                    '-I', str(ROOT/'native/accounting'), str(ROOT/'tests/accounting/review_v4/repro_v4.c'),
                    str(ROOT/'native/accounting/counter.c'), '-o', str(work/'repro_v4')], check=True)
    # The runner and C/report are literal reviewer files. Only their runtime
    # destinations and executable paths are supplied by this separate harness.
    runner = load(ROOT/'tests/accounting/review_v4/run_probes.py', 'literal_review_runner')
    runner.P = work
    runner.EXE = work/'repro_v4'
    results = []
    for version in ('v4', 'current'):
        for attempt in range(3):
            for kind, args in [('close', ['close', 1]), ('dup', ['dup', 1]),
                               ('truncate', ['truncate', 'path']), ('fallocate', ['allocate', 'fallocate'])]:
                record = runner.run(f'{version}-{kind}-{attempt}', args, tracer=tracers[version])
                assert not record['timed_out'] and record['returncode'] == 0, record
                stages = record['stages'];base = int(stages['baseline']['traced_shared_bytes'])
                last = {'close': 'closed', 'dup': 'after_exec', 'truncate': 'truncated', 'fallocate': 'fd_payload'}[kind]
                expected = (1048576 if version == 'v4' else 0) if kind != 'fallocate' else (0 if version == 'v4' else 1048576)
                assert int(stages[last]['traced_shared_bytes'])-base == expected, record
                assert not record['summary']['complete'] and record['summary']['unsupported_object_events'] == 0
                record.update(version=version, case=kind, attempt=attempt)
                results.append(record);print(version, kind, attempt, 'confirmed', flush=True)
            for mode in ('control', 'report', 'no-report'):
                record = runner.run(f'{version}-fifo-{mode}-{attempt}', ['rooted_fifo', '@DIR@', 1, 1],
                                    observed=mode != 'control', report=mode == 'report', tracer=tracers[version])
                expected_timeout = version == 'v4' and mode != 'control'
                assert record['timed_out'] == expected_timeout, record
                if not expected_timeout:
                    assert record['returncode'] == 0 and 'FACT completed 1' in record['stdout'], record
                record.update(version=version, case='rooted_fifo', attempt=attempt, mode=mode)
                results.append(record);print(version, 'fifo', mode, attempt, 'confirmed', flush=True)
    for attempt in range(3):
        for report in (True, False):
            record = runner.run(f'v3-fifo-{report}-{attempt}', ['rooted_fifo', '@DIR@', 1, 1],
                                report=report, tracer=tracers['v3'])
            assert not record['timed_out'] and record['returncode'] == 0, record
            record.update(version='v3', case='rooted_fifo', attempt=attempt, mode='report' if report else 'no-report')
            results.append(record)
    for version, metadata in manifests.items():
        manifest_path = ROOT/f'tests/accounting/checkpoints/retention_{version}.json'
        assert sha(manifest_path) == metadata['manifest_sha256']
        manifest = json.loads(manifest_path.read_text())
        assert sha(ROOT/manifest['archive']) == metadata['archive_sha256']
    output = ROOT/'tests/accounting/REVIEW_V4_RESULTS.json'
    output.write_text(json.dumps({
        'successful': True, 'complete_service_measurement': False, 'results': results,
        'baselines': manifests, 'evidence_directory': str(work),
        'current_build': json.loads((work/'current-build/BUILD.json').read_text()),
        'fixture_sha256': {str(p.relative_to(ROOT)): sha(p) for p in sorted((ROOT/'tests/accounting/review_v4').iterdir()) if p.is_file()},
        'timeout_meaning': 'bounded harness cleanup; never FalhaReal, excess or a statement about service K',
    }, indent=2)+'\n')
    print(output)


if __name__ == '__main__':
    main()
