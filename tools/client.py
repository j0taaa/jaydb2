#!/usr/bin/env python3
"""Canonical JayDB wire values and a small request/response command line client."""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import re
import sys

NAME = re.compile(r'[A-Za-z_][A-Za-z0-9_]{0,63}\Z')


def encode(value):
    result = bytearray()
    pending = [value]
    while pending:
        v = pending.pop()
        if v is None:
            result.append(0)
        elif type(v) is bool:
            result.append(2 if v else 1)
        elif type(v) is int:
            if not -(2**63) <= v < 2**63:
                raise ValueError('Integer outside int64')
            result.append(3)
            result.extend(v.to_bytes(8, 'big', signed=True))
        elif type(v) is str:
            b = v.encode('utf-8', errors='strict')
            result.append(4)
            result.extend(len(b).to_bytes(8, 'big'))
            result.extend(b)
        elif type(v) is list:
            result.append(5)
            result.extend(len(v).to_bytes(8, 'big'))
            pending.extend(reversed(v))
        elif type(v) is dict:
            if any(type(k) is not str or not NAME.fullmatch(k) for k in v):
                raise ValueError('Invalid field name')
            result.append(6)
            result.extend(len(v).to_bytes(8, 'big'))
            for k in reversed(sorted(v)):
                pending.extend([v[k], k])
        else:
            raise ValueError('Type not representable in the JayDB protocol')
    return bytes(result)


def decode(data):
    position = 0
    stack = []
    root = []
    target = root

    def take(n):
        nonlocal position
        if n > len(data) - position:
            raise ValueError('Truncated value')
        b = data[position:position+n]
        position += n
        return b

    while True:
        tag = take(1)[0]
        if tag == 0:
            value = None
        elif tag in (1, 2):
            value = tag == 2
        elif tag == 3:
            value = int.from_bytes(take(8), 'big', signed=True)
        elif tag == 4:
            value = take(int.from_bytes(take(8), 'big')).decode('utf-8', errors='strict')
        elif tag in (5, 6):
            n = int.from_bytes(take(8), 'big')
            if n:
                stack.append((tag, n, [], target))
                target = stack[-1][2]
                continue
            value = [] if tag == 5 else {}
        else:
            raise ValueError('Invalid tag')
        target.append(value)
        while stack:
            tag, n, fields, parent = stack[-1]
            if len(fields) != n * (2 if tag == 6 else 1):
                break
            stack.pop()
            if tag == 6:
                names = fields[::2]
                if (any(type(k) is not str or not NAME.fullmatch(k) for k in names)
                    or any(a >= b for a, b in zip(names, names[1:]))):
                    raise ValueError('Noncanonical record')
                value = dict(zip(names, fields[1::2], strict=True))
            else:
                value = fields
            target = parent
            target.append(value)
        if not stack:
            if position != len(data):
                raise ValueError('Bytes after the value')
            return root[0]


def frame(value):
    body = encode(value)
    return len(body).to_bytes(8, 'big') + body


def prepared_frame(operation, code, credential, arguments=None, proof=''):
    """Prepare source (0), execute a handle (1), or invalidate a handle (2)."""
    if type(operation) is not int or operation not in (0, 1, 2):
        raise ValueError('Invalid prepared operation')
    body = bytes((7, operation)) + encode({'arguments': arguments, 'code': code,
                                         'credential': credential, 'proof': proof})
    return len(body).to_bytes(8, 'big') + body


def unframe(data):
    if len(data) < 8 or int.from_bytes(data[:8], 'big') != len(data) - 8:
        raise ValueError('Invalid framing')
    return decode(data[8:])


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--decode', action='store_true')
    p.add_argument('--code', type=Path)
    p.add_argument('--proof', type=Path)
    p.add_argument('--credential')
    p.add_argument('--arguments', default='null', help='JSON value, without fractional numbers')
    mode = p.add_mutually_exclusive_group()
    mode.add_argument('--prepare', action='store_true', help='Prepare source with a universal certificate')
    mode.add_argument('--handle', help='Execute an instance-local prepared handle')
    mode.add_argument('--invalidate', help='Invalidate an instance-local prepared handle')
    a = p.parse_args()
    if a.decode:
        # A server session may return several frames before EOF.
        while header := sys.stdin.buffer.read(8):
            if len(header) != 8:
                raise ValueError('Truncated response header')
            body = sys.stdin.buffer.read(int.from_bytes(header, 'big'))
            print(json.dumps(unframe(header + body), ensure_ascii=False), flush=True)
    else:
        if a.handle is not None or a.invalidate is not None:
            if a.credential is None or a.code is not None or a.proof is not None:
                p.error('Handle operations require --credential and take no --code/--proof')
            sys.stdout.buffer.write(prepared_frame(1 if a.handle is not None else 2,
                a.handle if a.handle is not None else a.invalidate, a.credential, json.loads(a.arguments)))
            return
        if a.code is None or a.proof is None or a.credential is None:
            p.error('--code, --proof and --credential are required')
        # read_bytes preserves CRLF and every original Unicode scalar.
        value = {'arguments': json.loads(a.arguments),
            'code': a.code.read_bytes().decode('utf-8'), 'credential': a.credential,
            'proof': a.proof.read_bytes().decode('utf-8')}
        if a.prepare:
            sys.stdout.buffer.write(prepared_frame(0, value['code'], a.credential, value['arguments'], value['proof']))
        else:
            sys.stdout.buffer.write(frame(value))


if __name__ == '__main__':
    main()
