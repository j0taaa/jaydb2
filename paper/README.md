# TCC manuscript and defense slides

English article by **Gabriel Jota Lizardo, PUC Minas**, with a **Portuguese
defense presentation**: 18 main frames and six appendix frames (the executable
theorem list and the eleven T3 host duties). Both use LaTeX; the slides use Beamer, with
Portuguese speaker notes in each frame. Change wording and layout directly in `slides.tex`.

```sh
make -C paper
```

Requires Python 3 and pdfLaTeX with standard AMS, Times, geometry, microtype,
natbib, booktabs, hyperref, Beamer, PGF and PGFPlots packages. Build products stay ignored
under `.build/tcc/`; the deliverables are:

- `.build/tcc/output/jaydb2-tcc.pdf`
- `.build/tcc/output/jaydb2-defense.pdf`

The article and slides describe the serial executable Bend gate, generated
admission-oracle proof, worker Commit/Keep decision, and checked prepared
controller and registry. The article develops the model, architecture,
executable guarantees and trusted base T1–T3, then the indexed ownership and
voucher/receipt applications. Its evaluation covers ordinary admission cost,
prepared reuse, durable and owner-only point operations against PostgreSQL 16
and SQLite, verification cost, and complete-state size scaling.

Both LaTeX sources compile independently of generated evidence tables. Red
`\pending{Name}` fields reserve quantitative results for the new measurements;
the state-scaling figure contains no invented samples. Benchmark execution and
evidence generation are maintained separately from the manuscript prose.

While measurements are pending, compile each source twice from `paper/` with
`pdflatex -halt-on-error -interaction=nonstopmode -output-directory=../.build/tcc`
after creating `.build/tcc/` from the repository root.

The direct outputs are `.build/tcc/main.pdf` and `.build/tcc/slides.pdf` from the
repository root. The Makefile also runs the separately maintained evidence
builder and copies PDFs to the delivery paths above.

Run the data rejection controls with:

```sh
python3 -B -m unittest discover -s paper -p test_evidence.py -v
```

The organization roughly follows the author's
[tcc-final article](https://github.com/j0taaa/tcc-final/tree/main/paper), while
using a self-contained article layout and this project's executable specification.
The current [PUC Minas library guidance](https://www.pucminas.br/biblioteca/DocumentoBiblioteca/ABNT-GUIA-COMPLETO-Elaborar-formatar-trabalho-cientifico.pdf)
and the [2026 ICEI article example](https://www.overleaf.com/latex/templates/modelo-de-artigo-icei-puc-minas/bxwcdrxpdgbc)
informed the format. The specific course's submission template, advisor,
committee, defense date and any mandatory translated abstract still need local
confirmation before submission; they have not been invented. The main text
and abstract are English as requested. Source bibliography titles retain their
original language.

The presentation is a Beamer PDF with editable LaTeX source. Text, diagrams,
tables, the state-scaling chart and Portuguese speaker notes remain in
`slides.tex`. The article and its abstract remain English.

The theorem contract covers actual gate execution, direct/registered selection,
checked prepare/invalidate transitions, mixed service runs and handle
non-revival. T1–T3 identify checker/binding, compiler/runtime and physical host
assumptions. A dedicated discussion section collects limitations and threats:
storage durability and crash-recovery proofs, OS failures, physical resources,
checker completeness, application generality and measurement validity.
