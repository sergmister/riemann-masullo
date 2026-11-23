# Modifications

Every Lean file carries a new header with its upstream path, pinned commit and MIT notice.
The upstream files have no per-file copyright headers. In each file, the enclosing namespace
`Masullo` becomes `RiemannMasullo.External.Grh`. Declaration names and proof bodies are unchanged.

## Module changes

- `AnalyticGoodHeightDisk.lean` imports `EntireFiniteFactors` under the vendored module path.
- `InteriorLogJet.lean` imports `ExpAbsDecay` under the vendored module path and makes
  `memLp_interiorLogJet` public so consumers can use the square-integrability estimate directly.
- `HeckeContourReflection.lean` takes lines 26–49, including the docstring and full proof of
  `completed_logDeriv_reflection`. The original module documentation is replaced by a heading
  for this excerpt. The opens retain `Complex`, `Filter` and scoped `Topology`.
  The excerpt keeps the public `Mathlib.Analysis.Calculus.LogDeriv` import and adds public
  `Mathlib.Analysis.SpecialFunctions.ExpDeriv` for the complex exponential, its derivative and
  the complex normed-field instance, plus private `Mathlib.Tactic.LinearCombination` for the proof.
  The compact Mellin, inversion, Bochner integral and ring imports belong to the upstream contour
  file and are omitted with `completed_reflect_left_integral`.

The other five lemma modules are copied in full with the header and namespace changes above.
`LICENSE` is byte-for-byte identical to the upstream license.
