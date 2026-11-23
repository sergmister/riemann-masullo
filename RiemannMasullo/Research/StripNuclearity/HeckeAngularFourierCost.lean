module

public import RiemannMasullo.Research.StripNuclearity.HeckeAngularWeights
public import RiemannMasullo.Research.StripNuclearity.HeckeConvolution

/-! # The angular Fourier cost of the admitted Hecke zeros

A compact Bruhat test on the idèle class group has summable quadratic
radial Fourier cost after weighting each angular component by its admitted
Hecke divisor. The positive angular Fourier convention agrees with the
inverse-character radial lifts in the spectral projection.
-/

@[expose] public noncomputable section

open Function MeasureTheory NumberField Set
open scoped NNReal

namespace RiemannMasullo.StripNuclearity

variable {F : Type*} [Field F] [NumberField F]

set_option quotPrecheck false
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "U" => PontryaginDual C𝔽
local notation "X" => PontryaginDual C₁

/-- The Sobolev cutoff can only reduce the full positive multiplicity of a
zero. This includes the strict cutoff for boundary jets in the closed strip. -/
theorem admittedHeckeDivisorMass_le_heckePositiveDivisorMass (ψ : U) (α s : ℝ) :
    admittedHeckeDivisorMass ψ α s ≤ heckePositiveDivisorMass ψ := by
  let D := MeromorphicOn.divisor (continuedCompletedHeckeL ψ) univ
  let Z := {z : ℂ // 0 < D z ∧ |z.re - 1 / 2| ≤ α}
  let f (z : ℂ) := ((D z).toNat : ℝ) / (1 + |z.im|) ^ 2
  let a (z : Z) :=
    (spectralStripMultiplicity α s (z.val.re - 1 / 2) (D z.val).toNat : ℝ) / (1 + |z.val.im|) ^ 2
  have hf : Summable f := summable_heckePositiveDivisor_mass ψ
  have ha (z : Z) : a z ≤ f z := by
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    exact_mod_cast (show
        spectralStripMultiplicity α s (z.val.re - 1 / 2) (D z.val).toNat ≤ (D z.val).toNat by
      unfold spectralStripMultiplicity spectralBoundaryMultiplicity
      split_ifs <;> first | exact le_rfl | exact min_le_left _ _ | exact Nat.zero_le _)
  have hs : Summable a := (hf.comp_injective Subtype.val_injective).of_nonneg_of_le
    (fun _ ↦ div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) ha
  exact hs.tsum_le_tsum_of_inj (↑) Subtype.val_injective
    (fun _ _ ↦ div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) ha hf

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1

/-- For every number field, the quadratic radial Fourier cost of a compact
Bruhat test is summable over its angular components after weighting by the
square of one plus the admitted Hecke zero mass. The compact Haar measure,
canonical radial section, and sign of the angular character are explicit. -/
theorem summable_admittedHeckeDivisorMass_angular_fourierCost
    (φ : BruhatCompactSupport C𝔽) (μ : Measure C₁) [μ.IsHaarMeasure]
    (χ : X →* U) (hχ : IsSpectralBasepointChoice χ) (α s : ℝ) :
    let q : IdeleGroup (𝓞 F) F →ₜ* C𝔽 := ⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩
    let σ : ℝ≥0ˣ →ₜ* C𝔽 := q.comp
      ⟨canonicalIdeleNormSection F, canonicalIdeleNormSection_continuous F⟩
    let p (ξ : X) (t : ℝ) :=
      ∫ k : C₁, φ.val (k.val * σ (radialExponential (Multiplicative.ofAdd t))) * (ξ k : ℂ) ∂μ
    Summable (fun ξ ↦ (1 + admittedHeckeDivisorMass (χ ξ) α s) ^ 2 *
      radialQuadraticFourierCost (p ξ)) := by
  intro q σ p
  let cost (ξ : X) := radialQuadraticFourierCost (p ξ)
  have hpos (ξ) : 0 ≤ cost ξ := radialQuadraticFourierCost_nonneg _
  have hs : Summable (fun ξ ↦ (1 + heckePositiveDivisorMass (χ ξ)) ^ 2 * cost ξ) :=
    summable_heckePositiveDivisorMass_angular_fourierCost φ μ χ hχ
  apply hs.of_nonneg_of_le (fun ξ ↦ mul_nonneg (sq_nonneg _) (hpos ξ))
  intro ξ
  have hh := admittedHeckeDivisorMass_le_heckePositiveDivisorMass (χ ξ) α s
  have hn : 0 ≤ admittedHeckeDivisorMass (χ ξ) α s :=
    tsum_nonneg fun _ ↦ div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) (by linarith) 2) (hpos ξ)

end RiemannMasullo.StripNuclearity
