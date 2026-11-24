module

public import RiemannMasullo.Research.StripNuclearity.Projective
public import RiemannMasullo.Research.StripNuclearity.TraceSandwich

/-! # Nuclear convolution on the spectral quotient

Compress the ambient operator representing convolution after spectral projection
along the quotient map and its orthogonal section.
-/

@[expose] public noncomputable section

open Function MeasureTheory NumberField
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo.StripNuclearity

private theorem nuclear_of_quotient_compression {W Q : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
    [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]
    (T : W →L[ℂ] W) (B : Q →L[ℂ] Q) (j : Q →L[ℂ] W) (q : W →L[ℂ] Q)
    (hT : IsNuclearOperator T) (he : ∀ x, q (T (j x)) = B x) :
    IsNuclearOperator B := by
  have h : q.comp (T.comp j) = B := ContinuousLinearMap.ext he
  exact (congrArg IsNuclearOperator h).mp (traceNorm_sandwich_le T hT j q).choose

variable {F : Type*} [Field F] [NumberField F]

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 instSpectralQuotientPolynormableSec3

set_option quotPrecheck false
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" => (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "logNorm" => (fun g : C𝔽 ↦ Real.log ((ideleClassNorm F g).val : ℝ))

/-- Paper: Theorem 10.3.2.1, pp. 453–454, and (10.4.3.45), p. 473. An ambient
projective tensor representing convolution after projection gives nuclearity
of the induced quotient convolution. This implication holds at every center. -/
theorem spectralConvolution_nuclear_of_projectiveKernel (a : ℝ) {α s : ℝ}
    (hα : 0 ≤ α) (hs : 0 ≤ s) (φ : BruhatCompactSupport C𝔽)
    (hK : ∃ K, sobolevProjectiveKernelOperator (F := F) hα hs K =
      (hardySobolevTestAction μ𝔽 m𝔽 (-α) α s (neg_le_self hα) hs φ).comp
        (spectralProjection (F := F) a hα hs)) :
    IsNuclearOperator (spectralConvolution (F := F) a (neg_le_self hα) hs φ) := by
  let W := CompactIntervalSobolev μ𝔽 logNorm (-α) α s
  let A : W →L[ℂ] W := hardySobolevTestAction μ𝔽 m𝔽 (-α) α s (neg_le_self hα) hs φ
  let P : W →L[ℂ] W := spectralProjection (F := F) a hα hs
  let B := spectralConvolution (F := F) a (neg_le_self hα) hs φ
  let θ := globalThetaSobolev F a (neg_le_self hα) hs
  let q := θ.mkQL
  let j := θ.orthogonal.subtypeL.comp
    θ.quotientEquivOrthogonal.toContinuousLinearEquiv.toContinuousLinearMap
  have hAP : IsNuclearOperator (A.comp P) := (exists_projectiveKernel_iff hα hs _).mp hK
  apply nuclear_of_quotient_compression (A.comp P) B j q hAP
  intro x
  change q (A (P (j x))) = B x
  have hj : P (j x) = j x := θ.orthogonal.starProjection_eq_self_iff.mpr
    (θ.quotientEquivOrthogonal x).property
  rw [hj]
  exact (spectralConvolution_mkQ (F := F) a (neg_le_self hα) hs φ (j x)).symm.trans
    (congrArg B (θ.quotientEquivOrthogonal.symm_apply_apply x))

end RiemannMasullo.StripNuclearity
