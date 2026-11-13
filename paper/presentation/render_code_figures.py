#!/usr/bin/env python3
"""Render literal, locally sourced Bend excerpts as small SVG code figures.

No code is synthesized. Source line breaks are kept; long lines wrap at spaces.
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
    # Keep the source's own line breaks; wrap only lines longer than `columns`,
    # with a hanging indent. Indentation is drawn through the x position because
    # SVG shown through <img> does not reliably preserve leading spaces.
    char = 15.6
    lines = []
    for line in code.splitlines():
        indent = len(line) - len(line.lstrip(' '))
        wrapped = textwrap.wrap(
            line.strip(), width=columns - indent,
            replace_whitespace=False, drop_whitespace=True,
            break_long_words=False, break_on_hyphens=False) or ['']
        lines.append((indent, wrapped[0]))
        lines.extend((indent + 4, rest) for rest in wrapped[1:])
    width, height = columns * char + 48, len(lines) * 38 + 48
    # A monospace fallback keeps the self-contained image independent of webfonts.
    body = ''.join(f'<text x="{24 + indent * char:.1f}" y="{45 + i * 38}">{escape(text)}</text>'
                   for i, (indent, text) in enumerate(lines))
    (ASSETS / filename).write_text(
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width:.0f}" height="{height}" '
        f'viewBox="0 0 {width:.0f} {height}" role="img">'
        f'<title>{escape(path + chr(10) + code)}</title>'
        '<rect width="100%" height="100%" fill="#102f3b"/>'
        '<g fill="#f4f1e8" font-family="monospace" font-size="26">'
        f'{body}</g></svg>\n')


if __name__ == '__main__':
    policy = 'applications/rls/Policy.bend'
    render('write-scope.svg', policy,
           excerpt(policy, 'def WriteScope(', '\n\n# Writes reach'), 52)
    proof = 'applications/rls/ClientProof.bend'
    render('client-certificate.svg', proof,
           excerpt(proof, 'def certificate(', '\n  L.Both'), 80)
