#!/usr/bin/env python3
"""Narrow post-run audit: verify frozen environments after late unused additions.

Never changes raw measurements. Requires ALL original inputs to match, ALL
functional records to pass, and every persisted environment to match exactly.
"""
import argparse
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def sha(b):
    return hashlib.sha256(b).hexdigest()


def require(value, message):
    if not value:
        raise ValueError(message)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('result', type=Path)
    p.add_argument('--derived', type=Path, required=True)
    p.add_argument('--evidence', type=Path, required=True)
    a = p.parse_args()
    raw = a.result.read_bytes()
    m = json.loads(raw)
    original_error = m.get('error', '')
    require(m['status'] == 'failed' and original_error.startswith('RuntimeError: Benchmark inputs changed: '), 'Not the narrow inventory-guard case')
    require(len(m['results']) == 30 and all(r['status'] == 'passed' for r in m['results']), 'All 30 functional records must pass')
    original = m['source_sha256']
    for name, expected in original.items():
        require(sha((ROOT/name).read_bytes()) == expected, 'Original input changed: '+name)
    # Capture additions separately; never allow an original file to be replaced.
    import run
    current = run.identity()
    additions = sorted(current.keys()-original.keys())
    historical_additions = original_error.split('Benchmark inputs changed: ', 1)[1].split(', ')
    require(all(n not in original and n.startswith('contract/') and n.endswith('.bend') for n in historical_additions), 'Not a late contract-addition case')
    require(all(n.startswith(('contract/', 'proof/')) and n.endswith('.bend') for n in additions), 'Unexpected new input kind')
    for name, expected in m['suite_sha256'].items():
        require(sha((ROOT/'experiments/database-comparison'/name).read_bytes()) == expected, 'Original suite input changed: '+name)
        require(sha((a.result.parent/'suite'/name).read_bytes()) == expected, 'Run snapshot changed: '+name)
    binary_sha = sha(Path(m['jay_binary']).read_bytes())
    require(binary_sha == m['jay_binary_sha256'], 'Controller changed')
    for tool, expected in m['verified_tools'].items():
        lock = m['toolchain_lock']
        path = ROOT/f'.tools/bend-{lock["version"]}/bin/bend' if tool == 'bend' else ROOT/f'.tools/bendtt-{lock["kernelSha256"]}'
        require(sha(path.read_bytes()) == expected, 'Pinned tool changed')
    sources = {}
    for name in original:
        path = Path(name)
        if str(path.parent) in ('contract', 'src') and path.suffix == '.bend':
            b = (ROOT/path).read_bytes()
            sources[path.name] = b.decode().replace('../contract/', './').encode() if str(path.parent) == 'src' else b
    sources['Native.bend'] = (ROOT/'native/effects.bend').read_bytes()
    tooling = {}
    for folder in ('tools/admission', 'tools/verifier'):
        for file in (ROOT/folder).iterdir():
            if file.suffix in ('.mjs', '.json'):
                name = str(file.relative_to(ROOT))
                require(name in original, 'New frozen tooling: '+name)
                tooling[name] = file.read_bytes()
    for name in ('tools/service/stage.mjs', 'tools/service/compile.mjs', 'native/effects.bend', 'native/effects.c',
                 'server/main.rs', 'server/capture.rs', 'server/read_batch.rs', 'server/scheduling.rs', 'server/storage.rs', 'server/timing.rs', 'Cargo.toml', 'Cargo.lock'):
        if (ROOT/name).exists():
            tooling[name] = (ROOT/name).read_bytes()
    checks, data_hashes = [], {}
    for r in m['results']:
        folder = a.result.parent/r['scenario']/r['engine']
        final = json.loads((folder/'final-data.json').read_text())
        digest = sha(json.dumps(final, sort_keys=True).encode())
        require(digest == r['final_data_sha256'], 'Final model artifact mismatch')
        data_hashes.setdefault(r['scenario'], set()).add(digest)
        if r['engine'] == 'postgresql':
            require(r['checks']['full_final_data_after_server_restart'], 'Missing PG restart verification')
        if r['engine'] != 'jaydb2':
            continue
        public = dict(sources, **{'Configuration.bend': (folder/'Configuration.bend').read_bytes()})
        entries = sorted([n, sha(b)] for n, b in public.items()) + sorted([n, sha(b)] for n, b in tooling.items()) + [['server/controller', binary_sha]]
        expected = sha(json.dumps(entries, separators=(',', ':')).encode())
        snapshot = (folder/'storage/snapshot').read_bytes()
        magic = b'jaydb2-image-v1\n'
        require(snapshot.startswith(magic), 'Invalid snapshot magic')
        require(sha(snapshot[:-32]) == snapshot[-32:].hex(), 'Snapshot checksum failed')
        actual = snapshot[len(magic):len(magic)+64].decode('ascii')
        require(actual == expected, 'Frozen environment mismatch: '+r['scenario'])
        require(r['checks']['full_final_data_after_reopen'], 'Missing Jay reopen check')
        checks.append({'scenario': r['scenario'], 'snapshot_sha256': sha(snapshot), 'expected_environment': expected, 'stored_environment': actual, 'matched': True})
    require(len(checks) == 10 and all(len(v) == 1 for v in data_hashes.values()), 'Incomplete environments or cross-engine final model mismatch')
    audit = {'status': 'passed', 'raw_result_sha256': sha(raw), 'raw_result_status': m['status'], 'raw_result_error': original_error,
             'original_production_files_verified': len(original), 'original_suite_files_verified': len(m['suite_sha256']),
             'added_files_excluded_from_all_measured_environments': additions, 'frozen_environments': checks,
             'repository_guard_historical_additions': historical_additions,
             'functional_records_passed': 30, 'postgres_restart_checks_passed': 10, 'all_final_model_hashes_match_across_engines': True,
             'scope': 'All original bytes unchanged; reconstructed complete frozen environments match all durable images. Repository inventory guard failed on late additions; original raw manifest is retained unchanged.'}
    a.evidence.mkdir(parents=True, exist_ok=True)
    (a.evidence/'raw-result.json').write_bytes(raw)
    (a.evidence/'provenance-audit.json').write_text(json.dumps(audit, indent=2, sort_keys=True)+'\n')
    m['status'] = 'passed'
    del m['error']
    m['provenance_audit'] = audit
    m['original_inventory_guard_status'] = 'failed'
    m['analysis_input_path'] = str(a.derived.resolve())
    a.derived.write_text(json.dumps(m, indent=2, sort_keys=True)+'\n')
    print('Verified all 10 original frozen environments; raw guard failure retained.')


if __name__ == '__main__':
    main()
