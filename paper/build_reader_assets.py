#!/usr/bin/env python3
"""Export the current article, interactive defense, PDFs, and faithful page renders."""
import argparse
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import statistics
import xml.etree.ElementTree as ET

from PIL import Image

ROOT = Path(__file__).resolve().parent.parent
BUILT = ROOT / '.build/tcc/output'


def run_poppler(command):
    result = subprocess.run(command, capture_output=True, text=True)
    if result.returncode:
        raise RuntimeError('PDF conversion failed:\n' + result.stderr[-3000:])
    return result.stdout


def text_layers(pdf):
    """Word boxes per page, grouped by line, as fractions of the page size.

    Each line is [top, height, [[left, width, word], ...]]. The reader lays these out as
    transparent text over each page image so the text can be selected and copied.
    """
    xhtml = run_poppler(['pdftotext', '-bbox-layout', str(pdf), '-'])
    ns = {'x': 'http://www.w3.org/1999/xhtml'}
    layers = []
    for page in ET.fromstring(xhtml).iterfind('.//x:page', ns):
        width, height = float(page.get('width')), float(page.get('height'))
        lines = []
        for line in page.iterfind('.//x:line', ns):
            words = line.findall('x:word', ns)
            if not words:
                continue
            size = statistics.median(float(w.get('yMax')) - float(w.get('yMin')) for w in words)
            bottom = float(line.get('yMax'))
            lines.append([round((bottom - size) / height, 4), round(size / height, 4),
                          [[round(float(w.get('xMin')) / width, 4),
                            round((float(w.get('xMax')) - float(w.get('xMin'))) / width, 4),
                            w.text or ''] for w in words]])
        layers.append(lines)
    return layers

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--directory', type=Path, default=ROOT / '.build/tcc/reader-assets')
    args = parser.parse_args()
    dest = args.directory.resolve()
    assets = dest / 'assets'
    assets.mkdir(parents=True, exist_ok=True)
    metadata = json.loads((BUILT / 'defense-slides.json').read_text())
    main_slides = sum(not s['backup'] for s in metadata)
    documents = {}
    for kind, name in [('article', 'jaydb2-tcc'), ('slides', 'jaydb2-defense')]:
        pdf = BUILT / (name + '.pdf')
        shutil.copyfile(pdf, assets / pdf.name)
        layers = text_layers(pdf)
        page_dir = assets / kind
        page_dir.mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(prefix='jaydb2-reader-pages-') as temporary:
            prefix = Path(temporary) / 'page'
            run_poppler(['pdftoppm', '-scale-to', '1800', '-png', str(pdf), str(prefix)])
            pages = []
            for number, image_path in enumerate(sorted(Path(temporary).glob('page-*.png')), 1):
                image = Image.open(image_path).convert('RGB')
                image.save(page_dir / f'{number:02}.webp', 'WEBP', quality=92, method=6)
                text = run_poppler(['pdftotext', '-f', str(number), '-l', str(number),
                                    str(pdf), '-']).replace('\f', '').strip()
                page = {'image': f'assets/{kind}/{number:02}.webp', 'text': text,
                        'width': image.width, 'height': image.height,
                        'lines': layers[number - 1]}
                if kind == 'slides':
                    page.update(metadata[number - 1])
                pages.append(page)
        expected = {f'{i:02}.webp' for i in range(1, len(pages) + 1)}
        for old in page_dir.glob('*.webp'):
            if old.name not in expected:
                old.unlink()
        documents[kind] = {'pdf': 'assets/' + pdf.name, 'pages': pages}
    if len(documents['slides']['pages']) != len(metadata):
        raise ValueError('Slide PDF and HTML metadata do not match.')
    documents['article']['title'] = 'JayDB2: Checking What Database Programs Are Allowed to Do'
    documents['slides'].update({'presentation': 'presentation.html', 'mainCount': main_slides,
                                'appendixCount': len(metadata) - main_slides})
    for source, target in [('jaydb2-defense.html', 'presentation.html'), ('speaker-notes.html', 'speaker-notes.html')]:
        html = (BUILT / source).read_text()
        if source == 'speaker-notes.html':
            html = html.replace('href="jaydb2-defense.html"', 'href="presentation.html"')
            html = html.replace('href="jaydb2-tcc.pdf"', 'href="assets/jaydb2-tcc.pdf"')
        (dest / target).write_text(html)
    (assets / 'documents.json').write_text(json.dumps(documents, ensure_ascii=False))
    print(f'Exported {len(documents["article"]["pages"])} article pages, '
          f'{len(metadata)} slides, HTML, and PDFs to {dest}')


if __name__ == '__main__':
    main()
