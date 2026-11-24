module

public import RiemannMasullo.AppB_AnalyticNT.Sec4b
import RiemannMasullo.Research.StripNuclearity.FullMellinSummability

/-! # The idelic explicit formula from the nuclear projected convolution

The full-width quotient gives absolute convergence of the positive divisor
sum at each compact test. Appendix B then identifies its sum with the polar
moments and the local principal values, both pointwise and in the strong dual.
-/

@[expose] public noncomputable section

open Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo.StripNuclearity

variable {F : Type*} [Field F] [NumberField F]

attribute [local instance] instIdeleClassT2Sec4b instIdeleClassLocallyCompactSec4b
  instIdeleClassMeasurableSec4b instFiniteCompletionUnitsLocallyCompactSec4b

local notation "C[" k "]" => IdeleClassGroup (𝓞 k) k

/-- Paper: Lemma B.4.4.9, pp. 624–625. For any norm section the centered
zero series converges absolutely with full multiplicities on every compact test.
Deviation: Absolute convergence follows from the trace of the nuclear
projected convolution at half-width one half. -/
theorem idelicExplicitFormula_summable_spectral_of_projected_convolution
    (τ : ℝ≥0ˣ →ₜ* C[F]) (hτ : RightInverse τ (ideleClassNorm F))
    (f : BruhatCompactSupport C[F]) :
    type_of% (idelicExplicitFormula_summable_spectral τ hτ f) := by
  apply (Equiv.Set.univ _).summable_iff.mp
  have he : (((-1 / 2 : ℝ) : ℂ)) = -1 / 2 := by norm_num
  simpa only [Function.comp_def, Equiv.Set.univ_apply, he] using
    summable_ideleClassMellin_completedHeckeZeros_of_projected_convolution τ hτ univ f (-1 / 2)

/-- Paper: Theorem B.4.4.7, pp. 623–626. For each compact idèle-class test the
normalized completed-zero sum equals the two pole moments minus the principal
values of the actual test restrictions.
Deviation: Nuclear projected convolution supplies the absolute convergence
needed to sum the characterwise formulas. -/
theorem idelicExplicitFormula_pointwise_of_projected_convolution
    (τ : ℝ≥0ˣ →ₜ* C[F]) (hτ : RightInverse τ (ideleClassNorm F)) (f : BruhatCompactSupport C[F])
    (testI : ∀ w : InfinitePlace F, BruhatCompactSupport w.Completionˣ)
    (hI : ∀ w u, (testI w).val u = f.val (IdeleClassGroup.ofCompletion (𝓞 F) F w u))
    (testF : ∀ v : HeightOneSpectrum (𝓞 F), BruhatCompactSupport (v.adicCompletion F)ˣ)
    (hF : ∀ v u, (testF v).val u = f.val (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u)) :
    type_of% (idelicExplicitFormula_pointwise τ hτ f testI hI testF hF) :=
  idelicExplicitFormula_pointwise_of_summable τ hτ f
    (idelicExplicitFormula_summable_spectral_of_projected_convolution τ hτ f) testI hI testF hF

/-- Paper: Theorem B.4.4.7, pp. 623–626. The multiplicity-weighted positive
zero distributions converge in the strong dual to the pole distributions
minus the infinite and finite local principal-value distributions.
Deviation: The projected convolution proves the absolute convergence at
each test used to pass to the strong dual. -/
theorem idelicExplicitFormula_of_projected_convolution
    (τ : ℝ≥0ˣ →ₜ* C[F]) (hτ : RightInverse τ (ideleClassNorm F)) :
    type_of% (idelicExplicitFormula τ hτ) :=
  idelicExplicitFormula_of_summable τ hτ (idelicExplicitFormula_summable_spectral_of_projected_convolution τ hτ)

end RiemannMasullo.StripNuclearity
