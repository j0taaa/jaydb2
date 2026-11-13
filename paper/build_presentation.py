#!/usr/bin/env python3
"""Build the 16:9 HTML defense, notes, metadata, and a printable PDF."""
import argparse
import base64
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

PAPER = Path(__file__).resolve().parent
ROOT = PAPER.parent
DECK = PAPER / 'presentation'
EVIDENCE = ROOT / '.build/tcc'
OUT = EVIDENCE / 'output'


def inline_asset(path):
    mime = {'.otf': 'font/otf', '.webp': 'image/webp', '.svg': 'image/svg+xml'}[path.suffix]
    return 'data:' + mime + ';base64,' + base64.b64encode(path.read_bytes()).decode()


def read_macros():
    """Read generated macros, including the grouped integer article branch."""
    pattern = r'\\newcommand\{\\(\w+)\}\{((?:[^{}]|\{[^{}]*\})*)\}'
    result = {}
    for name, raw in re.findall(pattern, (EVIDENCE / 'numbers.tex').read_text()):
        normalized = raw.replace('{,}', '').replace(',', '')
        try:
            result[name] = float(normalized)
        except ValueError:
            result[name] = raw
    if not result:
        raise ValueError('Missing numerical evidence. Run make -C paper evidence first.')
    return result


def build_html():
    OUT.mkdir(parents=True, exist_ok=True)
    css = (DECK / 'deck.css').read_text()
    player = (DECK / 'player.js').read_text()
    content = (DECK / 'content.js').read_text()
    def inline_references(text):
        return re.sub(r"assets/([A-Za-z0-9_.-]+)",
                      lambda match: inline_asset(DECK / 'assets' / match[1]), text)
    css, player, content = map(inline_references, (css, player, content))
    macros = read_macros()
    scaling = []
    for name, label in [('volatile_read', 'Leitura volátil'), ('persistent_update', 'Atualização durável')]:
        lines = (EVIDENCE / ('scaling-' + name + '.dat')).read_text().splitlines()
        keys = lines[0].split()
        scaling.append({'name': label, 'points': [
            dict(zip(keys, map(float, line.split()))) for line in lines[1:] if line.strip()
        ]})
    simulation = json.loads((EVIDENCE / 'simulation-deck.json').read_text())
    data = 'window.JAYDB2_SIMULATION=' + json.dumps(simulation) + ';\n' + 'window.JAYDB2_EVIDENCE=' + json.dumps(macros) + ';\nwindow.JAYDB2_SCALING=' + json.dumps(scaling) + ';'
    html = (DECK / 'shell.html').read_text()
    for marker, content in [('DECK_CSS', css), ('EVIDENCE_DATA', data),
                            ('DECK_CONTENT', content), ('DECK_PLAYER', player)]:
        html = html.replace('/* ' + marker + ' */', content)
    license_text = (DECK / 'assets/Inter-LICENSE.txt').read_text()
    html = html.replace('</head>', '<script type="application/json" id="font-license">' +
                        json.dumps(license_text).replace('</', '<\\/') + '</script></head>')
    output = OUT / 'jaydb2-defense.html'
    output.write_text(html)
    evidence_json = EVIDENCE / 'presentation-evidence.json'
    evidence_json.write_text(json.dumps(macros, indent=2))
    subprocess.run(['node', str(DECK / 'export-notes.cjs'), str(evidence_json),
                    str(OUT / 'speaker-notes.html'), str(OUT / 'defense-slides.json'),
                    str(EVIDENCE / 'simulation-deck.json')], check=True)
    return output


def build_pdf(html):
    chrome = os.environ.get('JAYDB2_CHROME_BIN') or next((
        binary for name in ['google-chrome', 'chromium', 'chromium-browser', 'google-chrome-stable']
        if (binary := shutil.which(name))
    ), None)
    if not chrome:
        raise RuntimeError('Chrome/Chromium is required for the slide PDF. Set JAYDB2_CHROME_BIN, or use make slides-html for HTML only.')
    with tempfile.TemporaryDirectory(prefix='jaydb2-defense-chrome-') as profile:
        command = [chrome, '--headless', '--no-sandbox', '--disable-gpu',
                   '--disable-dev-shm-usage', '--no-pdf-header-footer',
                   '--user-data-dir=' + profile, '--virtual-time-budget=1500',
                   '--print-to-pdf=' + str(OUT / 'jaydb2-defense.pdf'), html.as_uri()]
        result = subprocess.run(command, capture_output=True, text=True, timeout=90)
        if result.returncode:
            raise RuntimeError('Slide PDF export failed:\n' + result.stderr[-3000:])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--html-only', action='store_true', help='Skip Chrome PDF export.')
    args = parser.parse_args()
    html = build_html()
    if not args.html_only:
        build_pdf(html)
    print(html)
    if not args.html_only:
        print(OUT / 'jaydb2-defense.pdf')


if __name__ == '__main__':
    main()
