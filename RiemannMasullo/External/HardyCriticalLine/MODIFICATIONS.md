# Modifications to release v0.3.0

- Converted the selected declarations from Lean and Mathlib v4.32.2 to v4.36.0.
  Each source file is a Lean module. The upstream Hardy declarations were in
  `RiemannHypothesisProject.Hardy` and the Binet and Taylor helpers were in
  `RiemannHypothesisProject.ComplexCompactExhaustion`. Both groups now live in
  `HardyCriticalLine`. Imports reflect the retained statements and proofs.
- Replaced the ξ quotient in `HardyFunctionNormalization` by the negative of Mathlib’s
  `hardyZ`. The sign comes from the factor `s * (s - 1)`, which equals `-‖s‖²` on the
  critical line. The continuity, modulus and zero-set lemmas now use Mathlib directly.
  The proof of the signed Gamma-factor identity uses `ofReal_hardyZ` and
  `riemannZeta_def_of_ne_zero`. The formula for `criticalLinePoint` also occurs in
  upstream’s `SpectralModel.lean`.
- In `UpperIntegralBound`, used this signed Gamma factor directly in the pointwise
  approximation. Its phase error follows from the original critical-line Stirling
  estimate. The lower-bound module can use the real normalization independently of
  the Stirling estimate.
- In `ZetaFirstApproximation`, supplied the exponent explicitly to
  `Complex.deriv_ofReal_cpow_const` and updated the conditional simplification lemmas.
  Retained the dyadic approximation and its prerequisites. In `OscillatoryIntegralEstimates`,
  kept the first- and second-derivative estimates used for the small and large modes.
- For the Binet calculation, kept the real log-Gamma derivative estimates, analyticity of
  digamma on the right half-plane, the sawtooth integral and its Laplace transform. The
  remaining Bellotti–Wong lemmas bound the Binet kernel and give the quintic arctangent
  estimate. In `CriticalLineStirlingPhase`, obtained the shifted reciprocal-square
  integrability lemma from its Binet counterpart by commutativity. Updated short tactic
  sequences and simplification lists for v4.36.0 throughout these files.
- In `CriticalLineZeroInfinitude`, stopped at `positiveHardyZeroHeights_infinite`.
  The chapter uses the ordinates directly. The subsequent image-set theorems and
  their critical-line geometry dependencies were omitted.
- All declarations elaborate with the project’s default heartbeat limit.
