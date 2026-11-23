# External

Third-party Lean developments vendored into this project, and the directories reserved for the
sources we expect to draw on.

| Directory | Upstream | License | Status |
|---|---|---|---|
| [`PrimeNumberTheoremAnd/`](PrimeNumberTheoremAnd/) | <https://github.com/AlexKontorovich/PrimeNumberTheoremAnd> | Apache-2.0 | vendored at `a4fb698`: `StrongPNT.lean` (general part: Borel–Carathéodory, Blaschke products, Landau's bound for logarithmic derivatives) |
| [`AlgebraicNumberTheoryLean/`](AlgebraicNumberTheoryLean/) | <https://github.com/jonhanke/algebraic-number-theory-lean> | Apache-2.0 | vendored at `5ea368e`: rational idelic Dirichlet character and its descent to idele classes |
| [`Grh/`](Grh/) | <https://github.com/thatnealpatel/grh> | MIT | Vendored at `e55aab2` for good heights, zero-free disk estimates, weighted spectral jet kernels, and logarithmic derivative reflection |
| [`TauCeti/`](TauCeti/) | <https://github.com/TauCetiProject/TauCeti> | Apache-2.0 | vendored at `8794ab3` for Montel's subsequence theorem in §1.4.3, and Runge's approximation theorem on `ℂ` with its import closure (97 files) for Lemma B.5.3.4(2) |
| [`GaussianField/`](GaussianField/) | <https://github.com/mrdouglasny/gaussian-field> | Apache-2.0 | Vendored at `1283a27` for real one-dimensional Hermite completeness, orthonormality, and Schwartz seminorm growth |
| [`Stacks/`](Stacks/) | <https://github.com/AxiomMath/Stacks> | Apache-2.0 | under consideration |

Further material found by scouting. The exact declarations and pinned commits are listed in
[issue #3](https://github.com/mccorvie/riemann-masullo/issues/3).

| Upstream | License | What it offers |
|---|---|---|
| <https://github.com/jonhanke/algebraic-number-theory-lean> | Apache-2.0 | Additional material on Tate's thesis: adelic theta functions and Poisson summation, the global zeta integral and its functional equation, the functional equation of Hecke L-functions, continuation of the Dedekind zeta function, Pontryagin duality (Chapters 2–3, Appendix D.1) |
| <https://github.com/anthropics/fermats-last-theorem> | Apache-2.0 | adelic Schwartz–Bruhat functions and the Tate global zeta integral on their span (§2.1, §3.2) |
| <https://github.com/ImperialCollegeLondon/FLT> | Apache-2.0 | Haar measure scaling on the adeles (Appendix A.3) |

[`SURVEY.md`](SURVEY.md) has the scout's full list of exact declarations. Proofs ported one at
a time, without vendoring a whole module, are recorded in [`ATTRIBUTION.md`](ATTRIBUTION.md).

## Convention

Vendored code is copied, not added as a Lake dependency, so that each piece is pinned, auditable
and can be adapted to this project's Lean/Mathlib version. Every vendored source `X` lives in
`RiemannMasullo/External/X/` (modules `RiemannMasullo.External.X.…`) and carries:

- `README.md` — upstream URL, the exact pinned commit, authors, and which files were taken.
- `LICENSE` — the upstream license, unmodified. Check that it permits redistribution before
  vendoring; original copyright headers stay in every file.
- `MODIFICATIONS.md` — every change made to the upstream source (toolchain ports, renames,
  removed declarations), as the Apache-2.0 license requires.
- `SOURCE_MAP.json` — for each vendored file, its upstream path and sha256 at the pinned commit.

Rules:

- Take only what is needed, and keep upstream declaration names where possible.
- Vendored files must contain no `sorry` and no new axioms. Upstream `sorry`s are not vendored.
- Mathematics developed for this project goes in the chapter files, not here. If a vendored
  result needs strengthening, do it in a chapter file that imports it.
- One vendoring per pull request, with the build passing.
