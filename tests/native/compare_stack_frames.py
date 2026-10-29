#!/usr/bin/env python3
"""Compare an admitted emission against frozen68 and the current builder.

Generate with stack_frame_gate.mjs first. No admission bypass or Book edit:
both builders consume the exact C whose hash the gate receipt identifies.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import runpy
import tarfile
import tempfile
import time

ROOT = Path(__file__).resolve().parents[2]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('emission', type=Path)
    args = parser.parse_args()
    source = args.emission.resolve()
    gate = json.loads(Path(str(source) + '.gate.json').read_text())
    assert gate['primary'] and gate['bendtt'] and gate['sameCheckedBook']
    assert hashlib.sha256(source.read_bytes()).hexdigest() == gate['cSha256']
    with tempfile.TemporaryDirectory(prefix='jaydb-compare-stack-') as temp:
        folder = Path(temp)
        with tarfile.open(ROOT/'tests/native/checkpoints/v3_owned.tar.gz') as archive:
            archive.extractall(folder, filter='data')
        for name, builder in [('checkpoint68', folder/'tools/native/build.py'),
                              ('current', ROOT/'tools/native/build.py')]:
            spec = importlib.util.spec_from_file_location('frame_' + name, builder)
            module = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(module)
            started = time.monotonic()
            try:
                output = folder/(name + '.so')
                report = module.build_module(source, output, timeout_seconds=600,
                                             compiler_memory_bytes=2*1024**3)
                record = {'variant': name, 'status': 'compiled',
                          'maximumCFrameBytes': report['maximumCFrameBytes'],
                          'elapsedSeconds': time.monotonic() - started}
                receipt = source.with_name(source.stem + '-' + name + '.so.json')
                receipt.write_text(json.dumps(report, indent=2) + '\n')
                if name == 'current':
                    support = runpy.run_path(str(ROOT/'tests/native/test_native.py'))
                    native = support['Module'](output)
                    result, data = native.run_v3(b'\x07', terms=0, memory=64 << 20,
                                                stack=1 << 20, setup=20_000_000_000)
                    count = gate['fields']
                    extra = 3 if gate['mode'] == 'U32' else 0
                    expected = bytes([(count*7 + count*(count-1)//2 + extra) % 256])
                    record['run'] = {'status': result.status, 'code': result.runtime_code,
                                     'outputHex': data.hex(), 'expectedHex': expected.hex(),
                                     'chargedBytes': result.charged_bytes}
                    assert (result.status, result.runtime_code, data) == (0, 0, expected)
            except Exception as exc:
                record = {'variant': name, 'status': 'error',
                          'category': getattr(exc, 'category', None), 'message': str(exc),
                          'elapsedSeconds': time.monotonic() - started}
            print(json.dumps(record), flush=True)


if __name__ == '__main__':
    main()
