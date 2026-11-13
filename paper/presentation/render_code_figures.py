#!/usr/bin/env python3
"""Render literal, locally sourced Bend excerpts as small SVG code figures.

No code is synthesized. Only whitespace between tokens is wrapped for the deck.
Run from any directory with: python3 paper/presentation/render_code_figures.py
"""
from html import escape
from pathlib import Path
import textwrap

ROOT = Path(__file__).resolve().parents[2]
ASSETS = Path(__file__).resolve().parent / 'assets'


def excerpt(path, start, end):
    source = (ROOT / path).read_text()
    begin = source.index(start)
    return source[begin:source.index(end, begin)].rstrip()


def render(filename, path, code, columns):
    lines = []
    for line in code.splitlines():
        lines.extend(textwrap.wrap(
            line, width=columns, subsequent_indent='    ',
            replace_whitespace=False, drop_whitespace=True,
            break_long_words=False, break_on_hyphens=False) or [''])
    width, height = columns * 15.7 + 48, len(lines) * 38 + 48
    # A monospace fallback keeps the self-contained image independent of webfonts.
    body = ''.join(f'<text x="24" y="{45 + i * 38}">{escape(line)}</text>'
                   for i, line in enumerate(lines))
    (ASSETS / filename).write_text(
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" '
        f'viewBox="0 0 {width} {height}" role="img">'
        f'<title>{escape(path + chr(10) + code)}</title>'
        '<rect width="100%" height="100%" fill="#102f3b"/>'
        '<g fill="#f4f1e8" font-family="monospace" font-size="26" '
        f'xml:space="preserve">{body}</g></svg>\n')


if __name__ == '__main__':
    policy = 'applications/rls/Policy.bend'
    render('write-scope.svg', policy,
           excerpt(policy, 'def WriteScope(', '\n\n# Writes reach'), 43)
    proof = 'applications/rls/ClientProof.bend'
    render('client-certificate.svg', proof,
           excerpt(proof, 'def certificate(', '\n  L.Both'), 96)
