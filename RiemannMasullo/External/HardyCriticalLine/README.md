# Hardy’s theorem on critical-line zeros

`HardyCriticalLine.positiveHardyZeroHeights_infinite` proves that the Riemann zeta function
has infinitely many zeros of positive height on the critical line. The endpoint states this
for the real Hardy function. The equivalence `hardyFunctionReal_eq_zero_iff` identifies its
zeros with those of Mathlib’s `riemannZeta` at the same heights.

The proof comes from ArtiFish26’s *Riemann Hypothesis Lean Formalisation*, release v0.3.0
of 25 August 2026, commit `e9b20c778b19b5bba2e9a8e14a9bb4ca0afad850`.
That release says of itself, in its README, that it “does not prove the Riemann Hypothesis”;
only its proof of Hardy's theorem of 1914 is taken here.
Copyright 2026 ArtiFish26. [Upstream source](https://github.com/artifish26/riemann-hypothesis-lean/tree/e9b20c778b19b5bba2e9a8e14a9bb4ca0afad850) · [Apache-2.0 license](LICENSE)

On each sufficiently late interval `[T, 2T]`, the integral of the absolute value of the Hardy
function is at least `T / 2`, while the absolute value of its signed integral is at most
`C T^(3/4)`. If there were only finitely many positive zeros, continuity would force a
constant sign on every sufficiently late interval. The two integrals would then have the
same magnitude, contradicting the bounds. [Lower bound](LowerIntegralBound.lean) · [Upper bound](UpperIntegralBound.lean) · [Infinitude proof](CriticalLineZeroInfinitude.lean)

The lower bound uses a uniform dyadic Dirichlet polynomial approximation. The upper bound
also uses a Stirling estimate for the phase of the Gamma factor and estimates for integrals
of the oscillating terms. [Zeta approximation](ZetaFirstApproximation.lean) · [Stirling phase](CriticalLineStirlingPhase.lean) · [Oscillatory integrals](OscillatoryIntegralEstimates.lean)

The port builds on Lean and Mathlib v4.36.0. The source map records the upstream paths and
SHA-256 hashes for the seven Hardy modules and their Binet, digamma and Taylor dependencies.
[Source map](SOURCE_MAP.json) · [Modifications](MODIFICATIONS.md)
