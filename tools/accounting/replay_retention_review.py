"""Reproduce the v3 counterexamples against immutable v3 and current sources.

Uses real syscalls, real data checks and bounded harness cleanup. Timeouts in
this script are test outcomes, never public resource-excess witnesses.
"""
from __future__ import annotations
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import signal
import subprocess
import tarfile
import tempfile
import time

ROOT = Path(__file__).resolve().parents[2]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def compile_observer(module_path, output):
    spec = importlib.util.spec_from_file_location('review_build', module_path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module.build(output)[1]


def run(command, report=None, timeout=1.5):
    started = time.monotonic_ns()
    process = subprocess.Popen(list(map(str, command)), stdout=subprocess.PIPE,
                               stderr=subprocess.PIPE, start_new_session=True)
    timed_out = False
    try:
        out, err = process.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        timed_out = True
        os.killpg(process.pid, signal.SIGKILL)
        out, err = process.communicate()
    rows = [json.loads(line) for line in report.read_text().splitlines()] if report else []
    snapshots = {int(r['sequence']): r for r in rows if r['type'] == 'snapshot'}
    stages = {}
    for line in out.decode().splitlines():
        fields = line.split()
        if len(fields) == 4 and fields[1].isdigit() and fields[2].isdigit() and fields[3].isdigit():
            stages[fields[0]] = snapshots[int(fields[1])]
    for r in snapshots.values():
        assert r['flags'] & 2
        assert int(r['current']) == sum(int(r[k]) for k in
            ('traced_private_bytes', 'traced_shared_bytes', 'fd_payload_bytes', 'observer_bytes'))
        witness = snapshots[int(r['peak_sequence'])]
        assert witness['current'] == r['peak'] and witness['time_ns'] == r['peak_time_ns']
    return {'command': list(map(str, command)), 'returncode': process.returncode,
            'timed_out': timed_out, 'elapsed_ns': str(time.monotonic_ns()-started),
            'stdout': out.decode(), 'stderr': err.decode(), 'stages': stages,
            'summary': rows[-1] if rows and rows[-1]['type'] == 'summary' else None,
            'report_sha256': sha(report) if report else None}


def main():
    manifest_path = ROOT/'tests/accounting/checkpoints/retention_v3.json'
    manifest = json.loads(manifest_path.read_text())
    archive = ROOT/manifest['archive']
    assert sha(archive) == manifest['archiveSha256']
    work = Path(tempfile.mkdtemp(prefix='jaydb2-retention-v4-causal-'))
    with tarfile.open(archive) as source:
        source.extractall(work/'v3', filter='data')
    assert all(sha(work/'v3'/p) == digest for p, digest in manifest['files'].items())
    observers = {
        'v3': compile_observer(work/'v3/tools/accounting/build.py', work/'old-build'),
        'current': compile_observer(ROOT/'tools/accounting/build.py', work/'current-build'),
    }
    for name in ('reopen', 'offsets', 'blocking_lock'):
        subprocess.run(['/usr/bin/clang-19', '-std=c11', '-O2', '-g', '-Wall', '-Wextra', '-Werror',
                        '-pthread', '-I', str(ROOT/'native/accounting'),
                        str(ROOT/f'tests/accounting/review_v3/repro_{name}.c'),
                        str(ROOT/'native/accounting/counter.c'), '-o', str(work/name)], check=True)
    results = []
    for version, observer in observers.items():
        for name in ('reopen', 'offsets', 'blocking_lock'):
            for attempt in range(3):
                variants = ('report', 'no-report', 'control') if name == 'blocking_lock' else ('report',)
                for variant in variants:
                    report = work/f'{version}-{name}-{attempt}.jsonl' if variant == 'report' else None
                    command = [work/name]
                    if variant != 'control':
                        command = [observer, *(['--report', report] if report else []), '--', *command]
                    record = run(command, report)
                    record.update(version=version, name=name, attempt=attempt, variant=variant)
                    if name == 'blocking_lock':
                        expected_timeout = version == 'v3' and variant != 'control'
                        assert record['timed_out'] == expected_timeout, record
                        if not expected_timeout:
                            assert record['returncode'] == 0 and 'completed' in record['stdout'], record
                    else:
                        assert not record['timed_out'] and record['returncode'] == 0, record
                        s = record['stages'];base = int(s['baseline']['traced_shared_bytes'])
                        if name == 'reopen':
                            assert 'retained_byte 42 same_inode 1' in record['stdout']
                            assert int(s['original_fd_owns']['traced_shared_bytes'])-base == 1048576
                            for stage in ('reopened_fd_owns', 'data_still_retained'):
                                assert int(s[stage]['traced_shared_bytes'])-base == (0 if version == 'v3' else 1048576)
                        else:
                            assert 'retained_bytes 42 43' in record['stdout']
                            assert int(s['offset_zero_acquired']['traced_shared_bytes'])-base == 1048576
                            for stage in ('offset_one_acquired', 'both_offsets_fd_only'):
                                assert int(s[stage]['traced_shared_bytes'])-base == (1048576 if version == 'v3' else 2097152)
                        assert record['summary']['unsupported_object_events'] == 0
                        assert record['summary']['invalidated_observations'] == 0
                        assert not record['summary']['complete']
                    results.append(record)
                    print(version, name, attempt, variant, 'timeout' if record['timed_out'] else 'completed', flush=True)
    assert sha(archive) == manifest['archiveSha256']
    output = ROOT/'tests/accounting/REVIEW_V3_RESULTS.json'
    output.write_text(json.dumps({
        'successful': True, 'complete_service_measurement': False,
        'baseline_archive_sha256': sha(archive), 'baseline_manifest_sha256': sha(manifest_path),
        'fixture_sha256': {str(p.relative_to(ROOT)):sha(p) for p in
            sorted((ROOT/'tests/accounting/review_v3').glob('*')) if p.is_file()},
        'current_build': json.loads((work/'current-build/BUILD.json').read_text()),
        'baseline_build': json.loads((work/'old-build/BUILD.json').read_text()),
        'evidence_directory': str(work), 'results': results,
        'timeout_meaning': 'harness cleanup only; not a public excess/failure result',
    }, indent=2)+'\n')
    print(output)


if __name__ == '__main__':
    main()
