# Modifications

- Put the vendored declarations in the `GaussianField` namespace and adopt the Lean module
  system with explicit public imports and an exposed noncomputable section.
- Give the two `MemLp` terms in `deriv_hermiteFunction_memLp` explicit types to avoid the
  Lean 4.36 elaborator timeout when inferring both terms together.
- Omit the Sobolev-Hermite series bound and its `PSeries` import. Shorten the module description
  and omit upstream comments about axioms and modules outside this excerpt.
