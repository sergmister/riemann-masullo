# Tau Ceti

- **Source** — [TauCetiProject/TauCeti](https://github.com/TauCetiProject/TauCeti)
- **Pinned commit** — [`8794ab329bb60340fa690a2902cf995f0571721b`](https://github.com/TauCetiProject/TauCeti/tree/8794ab329bb60340fa690a2902cf995f0571721b), built upstream with Lean v4.37.0-rc1
- **License** — Apache-2.0. [Upstream license](LICENSE)
- **Authors** — The Tau Ceti contributors, as credited in the source headers.
- **Intended use** — `introTrace_montel_of_bounded` in §1.4.3 ([#5655](https://github.com/mccorvie/riemann-masullo/issues/5655)). It applies Montel's theorem into `ℂ × ℂ` to select a common subsequence for two holomorphic families.
  Runge's approximation theorem, for the refutation of Lemma B.5.3.4(2), p. 633
  (`Printed.stronglyRecurrentOn_compact_of_closedBall_false`, [#4666](https://github.com/mccorvie/riemann-masullo/issues/4666), ERRATA F22), which builds an entire function by repeated polynomial approximation.

## Files taken

The upstream paths are the same as the paths below, prefixed by `TauCeti/`.
[Source map](SOURCE_MAP.json)

| File | Used for |
|---|---|
| [`Analysis/Normed/Group/LocallyBounded.lean`](Analysis/Normed/Group/LocallyBounded.lean) | `IsLocallyBoundedOn` and its bound lemmas, including the passage from a single bound to bounds on compact subsets. |
| [`Analysis/Complex/Conformal/NormalFamilies.lean`](Analysis/Complex/Conformal/NormalFamilies.lean) | Cauchy's estimates and the mean-value inequality give equicontinuity of locally bounded holomorphic families. |
| [`Topology/ContinuousMap/Ascoli.lean`](Topology/ContinuousMap/Ascoli.lean) | `ArzelaAscoli.isCompact_closure_range_of_equicontinuous` gives compact closure in the compact-open topology. |
| [`Analysis/Complex/Conformal/Montel/Precompact.lean`](Analysis/Complex/Conformal/Montel/Precompact.lean) | `isCompact_closure_range_of_isLocallyBoundedOn` combines equicontinuity and properness of the target to get compact closure. |
| [`Analysis/Complex/Conformal/Montel/Basic.lean`](Analysis/Complex/Conformal/Montel/Basic.lean) | `montel` selects a locally uniformly convergent subsequence and proves that its limit is holomorphic. |

The Montel and local-boundedness declarations are in `RiemannMasullo.External.TauCeti`.
The compact-open lemma retains its upstream namespace `ArzelaAscoli`.

### Runge approximation

[`Analysis/Complex/Runge/Approximation.lean`](Analysis/Complex/Runge/Approximation.lean) and
every Tau Ceti module it imports, transitively: 97 whole files, about 28,600 lines, listed in
the [source map](SOURCE_MAP.json). None of them overlaps the Montel excerpt. The closure is large
because the Runge operator is built from the Cauchy–Pompeiu formula (`Analysis/Complex/Pompeiu`,
Wirtinger derivatives, smooth cutoffs), which pulls in general calculus, `Lp` and Haar-measure
supplements. By the upstream history the Runge files came in with Tau Ceti #38368, #39681 and
#41394.

| Declaration | What it says |
|---|---|
| `IsCompact.isConnected_compl_iff_forall_differentiableOn_exists_polynomial_norm_sub_lt` | **Polynomial Runge theorem**: for compact `K ⊆ ℂ`, `Kᶜ` is connected if and only if every function holomorphic on an open `U ⊇ K` is a uniform limit of polynomials on `K`. |
| `isRungeCompactPair_iff_approximation`, `IsRungeCompactPair.exists_differentiableOn_norm_sub_lt` | Runge relative to an open `Ω ⊆ ℂ`: approximation by `Ω`-holomorphic functions with values in a complex normed space, exactly when no component of `Ω \ K` is relatively compact in `Ω`. |
| `filledExhaustion`, `IsOpen.isRungeCompactPair_filledExhaustion`, `IsOpen.exists_subset_interior_and_isRungeCompactPair` | filled compact exhaustions of an open set, whose stages are Runge compact pairs that absorb every compact subset. |
| `holomorphicHull`, `holomorphicHull_eq_fill`, `IsCompact.isConnected_compl_iff_isPolynomiallyConvex` | holomorphic hulls and polynomial convexity in dimension one. |
| `Differentiable.exists_polynomial_norm_sub_lt` | an entire function is a uniform limit of polynomials on bounded sets. |

Names with an upstream `_root_.` prefix (`IsCompact.…`, `IsOpen.…`) and
`Differentiable.exists_polynomial_norm_sub_lt` are at root level; the others are in
`RiemannMasullo.External.TauCeti`.

Supplementary lemmas that upstream puts in Mathlib namespaces (`MeasureTheory`,
`ContinuousLinearMap`, `Real`, …) keep those namespaces. None of their names occurs in Mathlib at
this project's pin or elsewhere in this project (checked with `scripts/signatures.sh`).
[Modifications](MODIFICATIONS.md), [vendoring convention](../README.md)
