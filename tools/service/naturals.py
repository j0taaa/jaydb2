"""Decimal conversion for public Nat configuration without interpreter quotas.

Only small chunks pass through Python's decimal conversion. The work and memory
still grow with the actual value and remain part of the verification stage.
"""

BASE = 1_000_000_000
WIDTH = 9


def parse_decimal(value, check=None):
    if not isinstance(value, str) or not value or not value.isascii() or not value.isdecimal():
        raise ValueError('Expected a natural number in decimal')
    number = 0
    for start in range(0, len(value), WIDTH):
        if check is not None:
            check()
        chunk = value[start:start + WIDTH]
        number = number * 10**len(chunk) + int(chunk)
    return number


def decimal(number, check=None):
    if type(number) is not int or number < 0:
        raise ValueError('Expected a natural number')
    if not number:
        return '0'
    chunks = []
    while number:
        if check is not None:
            check()
        number, chunk = divmod(number, BASE)
        chunks.append(chunk)
    return str(chunks[-1]) + ''.join(f'{chunk:09d}' for chunk in reversed(chunks[:-1]))
