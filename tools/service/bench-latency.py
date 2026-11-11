#!/usr/bin/env python3
"""Measure ordinary E1 calls and preparation; caller holds the common heavy lock.

Run inside paper/bench/fixed-clock.sh. Raw observations always go under .build/;
this script never writes paper/evidence/. One service per program, one excluded
warmup then ten measured calls/preparations, original E1 inputs and assertions.
"""
import argparse
import json
from pathlib import Path
import statistics
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from paper.bench.run import BUILD, metadata, operation, session, source
from paper.bench.fixtures import package


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('label', choices=['before', 'after'])
    args = parser.parse_args()
    output = ROOT/'.build/admission-latency'/(args.label+'.json')
    output.parent.mkdir(parents=True, exist_ok=True)
    BUILD.mkdir(parents=True, exist_ok=True)
    (BUILD/'tmp').mkdir(exist_ok=True)
    data = {'metadata': metadata(1), 'records': []}
    for kind in ('read', 'indexed', 'voucher'):
        name = f'latency-{args.label}-{kind}'
        folder = package(BUILD/name, kind)
        code, proof, universal = source(folder)
        record = {'program': kind, 'ordinary': [], 'registration': [], 'warmups': []}
        data['records'].append(record)
        with session(folder, name, timing=True) as service:
            for i in range(11):
                arguments, value = operation(kind, i)
                row = service.call(code, proof, arguments, {'status': 'success', 'value': value})
                record['warmups' if i == 0 else 'ordinary'].append(row)
                print(args.label, kind, 'ordinary', i, round(row['elapsed_ns']/1e9, 3), flush=True)
                output.write_text(json.dumps(data, indent=2)+'\n')
            for i in range(11):
                _, row = service.prepare(code, universal)
                record['warmups' if i == 0 else 'registration'].append(row)
                print(args.label, kind, 'registration', i, round(row['elapsed_ns']/1e9, 3), flush=True)
                output.write_text(json.dumps(data, indent=2)+'\n')
    for record in data['records']:
        for mode in ('ordinary', 'registration'):
            values = [row['elapsed_ns']/1e6 for row in record[mode]]
            q1, _, q3 = statistics.quantiles(values, n=4, method='inclusive')
            print(record['program'], mode, statistics.median(values), q1, q3)


if __name__ == '__main__':
    main()
