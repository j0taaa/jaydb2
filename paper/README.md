# TCC manuscript and defense slides

English article by **Gabriel Jota Lizardo, PUC Minas**, with an editable
16-slide defense presentation. Both use LaTeX; the slides use Beamer, with
speaker notes in each frame. Change wording and layout directly in `slides.tex`.

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
provenance remains at `experiments/integration/evidence/main-review/benchmark.json`.
The historical GPU branch is explicitly identified and is not a current
mainline feature or a fresh measurement.

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

The presentation's PDF and LaTeX sources are supplied because the bundled
PowerPoint authoring runtime is unavailable in this environment. There is no
unvalidated PowerPoint conversion. The slides can be presented directly as a
PDF, and their source keeps text, chart values and layout editable.

The manuscript distinguishes source theorems, conditional service composition,
finite tests, and trusted operational assumptions. Neither it nor the slides
assert an unconditional proof of the entire executable or a performance win
against PostgreSQL/SQLite. The outstanding full functional proof and host
refinement obligations remain research work, not satisfied by import counts.
