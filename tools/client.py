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
                raise ValueError('Inteiro fora de int64')
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
                raise ValueError('Nome de campo inválido')
            result.append(6)
            result.extend(len(v).to_bytes(8, 'big'))
            for k in reversed(sorted(v)):
                pending.extend([v[k], k])
        else:
            raise ValueError('Tipo não representável no protocolo JayDB')
    return bytes(result)


def decode(data):
    position = 0
    stack = []
    root = []
    target = root

    def take(n):
        nonlocal position
        if n > len(data) - position:
            raise ValueError('Valor truncado')
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
            raise ValueError('Tag inválida')
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
                    raise ValueError('Registro não canônico')
                value = dict(zip(names, fields[1::2], strict=True))
            else:
                value = fields
            target = parent
            target.append(value)
        if not stack:
            if position != len(data):
                raise ValueError('Bytes depois do valor')
            return root[0]


def frame(value):
    body = encode(value)
    return len(body).to_bytes(8, 'big') + body


def unframe(data):
    if len(data) < 8 or int.from_bytes(data[:8], 'big') != len(data) - 8:
        raise ValueError('Enquadramento inválido')
    return decode(data[8:])


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--decode', action='store_true')
    p.add_argument('--codigo', type=Path)
    p.add_argument('--prova', type=Path)
    p.add_argument('--credencial')
    p.add_argument('--argumentos', default='null', help='Valor JSON, sem números fracionários')
    a = p.parse_args()
    if a.decode:
        # A server session may return several frames before EOF.
        while header := sys.stdin.buffer.read(8):
            if len(header) != 8:
                raise ValueError('Cabeçalho de resposta truncado')
            body = sys.stdin.buffer.read(int.from_bytes(header, 'big'))
            print(json.dumps(unframe(header + body), ensure_ascii=False), flush=True)
    else:
        if a.codigo is None or a.prova is None or a.credencial is None:
            p.error('--codigo, --prova e --credencial exigidos')
        # read_bytes preserves CRLF and every original Unicode scalar.
        value = {'argumentos': json.loads(a.argumentos),
            'codigo': a.codigo.read_bytes().decode('utf-8'), 'credencial': a.credencial,
            'prova': a.prova.read_bytes().decode('utf-8')}
        sys.stdout.buffer.write(frame(value))


if __name__ == '__main__':
    main()
