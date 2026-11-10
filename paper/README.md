# TCC manuscript and defense slides

English article by **Gabriel Jota Lizardo, PUC Minas**, with a **Portuguese
defense presentation**: 16 main slides and two appendices (GPU and the eight
core laws). Both use LaTeX; the slides use Beamer, with
Portuguese speaker notes in each frame. Change wording and layout directly in `slides.tex`.

```sh
make -C paper
```

Requires Python 3 and pdfLaTeX with standard AMS, Times, geometry, microtype,
natbib, booktabs, hyperref, Beamer and PGF packages. Build products stay ignored
under `.build/tcc/`; the deliverables are:

- `.build/tcc/output/jaydb2-tcc.pdf`
- `.build/tcc/output/jaydb2-defense.pdf`

`evidence.py` verifies the retained raw burst counts, medians and paired ratios
and derives the article's quantitative table. It does not run a benchmark or
claim that historical measurements describe a new executable. Full raw
provenance remains at `paper/evidence/benchmark.json`.
The GPU appendix identifies its historical branch and does not present a fresh
measurement. The external point-operation table uses the existing immutable
`results.json`, `raw-result.json` and `provenance-audit.json` under
`paper/evidence/`. The builder checks their digests,
raw/audited correspondence, measured outputs, sample identities and medians.
It preserves the original inventory-guard failure and its subsequent audit.
Historical paths inside these immutable records identify the original checkout;
the referenced reports and source inventories remain in Git history.
These flows have different policy and deployment semantics; the table is not
an equivalent-policy engine ranking.

Run the data rejection controls with:

```sh
python3 -B -m unittest discover -s paper -p test_evidence.py -v
```

The organization roughly follows the author's
[tcc-final article](https://github.com/j0taaa/tcc-final/tree/main/paper), while
using a self-contained article layout and this project's actual evidence.
The current [PUC Minas library guidance](https://www.pucminas.br/biblioteca/DocumentoBiblioteca/ABNT-GUIA-COMPLETO-Elaborar-formatar-trabalho-cientifico.pdf)
and the [2026 ICEI article example](https://www.overleaf.com/latex/templates/modelo-de-artigo-icei-puc-minas/bxwcdrxpdgbc)
informed the format. The specific course's submission template, advisor,
committee, defense date and any mandatory translated abstract still need local
confirmation before submission; they have not been invented. The main text
and abstract are English as requested. Source bibliography titles retain their
original language.

The presentation is a Beamer PDF with editable LaTeX source. Text, tables,
chart values and speaker notes remain in `slides.tex`; the chart values come
from the retained evidence through `evidence.py`. The article remains English.

The manuscript distinguishes source theorems, conditional service composition,
finite tests, and trusted operational assumptions. Neither it nor the slides
assert an unconditional proof of the entire executable or a performance win
against PostgreSQL/SQLite. The complete prepared-service composition, full functional proofs and host
refinement obligations remain unfinished. Component predicates and import
counts do not establish those results.
