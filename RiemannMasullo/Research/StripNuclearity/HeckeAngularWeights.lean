module

public import RiemannMasullo.Research.StripNuclearity.AngularHeckeMass
public import RiemannMasullo.Research.StripNuclearity.HeckeConductorZeroMass
public import RiemannMasullo.Research.StripNuclearity.IdeleAngularProfiles

/-! # Hecke zero masses on the nonzero Fourier profiles of an idèle-class test

The conductor-scale functional equation and Jensen's inequality control the
zero masses by real angular frequency weights for every number field.
-/

@[expose] public noncomputable section

open Function MeasureTheory NumberField Set
open scoped FourierTransform NNReal

namespace RiemannMasullo.StripNuclearity

variable {F : Type*} [Field F] [NumberField F]

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1

set_option quotPrecheck false
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "U" => PontryaginDual C𝔽
local notation "X" => PontryaginDual C₁

/-- The square of one plus the full count of positive Hecke zeros with the
inverse-square height weight is dominated on the active profiles of any fixed
Bruhat test by a product of squared angular Fourier frequencies. -/
theorem exists_angular_weight_heckePositiveDivisorMass (φ : BruhatCompactSupport C𝔽)
    (μ : Measure C₁) [μ.IsHaarMeasure] (χ : X →* U) (hχ : IsSpectralBasepointChoice χ) :
    ∃ (C : ℝ) (fs : List (X →ₜ* Multiplicative ℝ)), 0 ≤ C ∧ ∀ ξ : X,
      (∃ g : C𝔽, (∫ k : C₁, φ.val (k.val * g) * (ξ k : ℂ) ∂μ) ≠ 0) →
      (1 + heckePositiveDivisorMass (χ ξ)) ^ 2 ≤
        C * (fs.map (fun f ↦ 1 + ((f ξ).toAdd) ^ 2)).prod := by
  obtain ⟨K, hK, h⟩ := exists_uniform_heckeZeroMass_conductor_bound F
  exact exists_angular_weight_heckePositiveDivisorMass_of_bound (F := F) φ μ χ hχ K hK
    (fun ψ ↦ heckeLogDiscriminantConductor_nonneg ψ) (fun ψ hψ ↦ (h ψ hψ).2)

/-- Any nonnegative cost supported on the angular profiles of a fixed test,
summable against all the product weights, is summable against the square of
one plus the actual Hecke zero mass. -/
theorem summable_angular_heckePositiveDivisorMass_cost (φ : BruhatCompactSupport C𝔽)
    (μ : Measure C₁) [μ.IsHaarMeasure] (χ : X →* U) (hχ : IsSpectralBasepointChoice χ)
    (cost : X → ℝ) (hn : ∀ ξ, 0 ≤ cost ξ)
    (hsupp : ∀ ξ, cost ξ ≠ 0 →
      ∃ g : C𝔽, (∫ k : C₁, φ.val (k.val * g) * (ξ k : ℂ) ∂μ) ≠ 0)
    (hs : ∀ fs : List (X →ₜ* Multiplicative ℝ),
      Summable (fun ξ ↦ (fs.map (fun f ↦ 1 + ((f ξ).toAdd) ^ 2)).prod * cost ξ)) :
    Summable fun ξ ↦ (1 + heckePositiveDivisorMass (χ ξ)) ^ 2 * cost ξ := by
  obtain ⟨C, fs, _, hb⟩ := exists_angular_weight_heckePositiveDivisorMass (F := F) φ μ χ hχ
  apply ((hs fs).mul_left C).of_nonneg_of_le (fun ξ ↦ mul_nonneg (sq_nonneg _) (hn ξ))
  intro ξ
  by_cases hz : cost ξ = 0
  · simp [hz]
  · simpa [mul_assoc] using mul_le_mul_of_nonneg_right (hb ξ (hsupp ξ hz)) (hn ξ)

private theorem fourier_cost_active (φ : BruhatCompactSupport C𝔽)
    (μ : Measure C₁) [μ.IsHaarMeasure]
    (σ : ℝ≥0ˣ →ₜ* C𝔽) (ξ : X) :
    let p (t : ℝ) :=
      ∫ k : C₁, φ.val (k.val * σ (radialExponential (Multiplicative.ofAdd t))) * (ξ k : ℂ) ∂μ
    (∫ u : ℝ, (1 + u ^ 2) * ‖𝓕 p u‖) ≠ 0 →
    ∃ g : C𝔽, (∫ k : C₁, φ.val (k.val * g) * (ξ k : ℂ) ∂μ) ≠ 0 := by
  intro p hn
  by_contra! hnone
  apply hn
  have hp : p = 0 := funext fun t ↦ hnone (σ (radialExponential (Multiplicative.ofAdd t)))
  have hzero (u : ℝ) : 𝓕 (0 : ℝ → ℂ) u = 0 := by
    rw [Real.fourier_real_eq]
    simp
  simp [hp, hzero]

/-- For every number field, the quadratic radial Fourier cost of a compact
Bruhat test is summable over its angular components after weighting by the
square of one plus the full positive Hecke zero mass. The compact Haar measure,
canonical radial section, and sign of the angular character are explicit. -/
theorem summable_heckePositiveDivisorMass_angular_fourierCost
    (φ : BruhatCompactSupport C𝔽) (μ : Measure C₁) [μ.IsHaarMeasure]
    (χ : X →* U) (hχ : IsSpectralBasepointChoice χ) :
    let q : IdeleGroup (𝓞 F) F →ₜ* C𝔽 := ⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩
    let σ : ℝ≥0ˣ →ₜ* C𝔽 := q.comp
      ⟨canonicalIdeleNormSection F, canonicalIdeleNormSection_continuous F⟩
    let p (ξ : X) (t : ℝ) :=
      ∫ k : C₁, φ.val (k.val * σ (radialExponential (Multiplicative.ofAdd t))) * (ξ k : ℂ) ∂μ
    Summable (fun ξ ↦ (1 + heckePositiveDivisorMass (χ ξ)) ^ 2 *
      ∫ u : ℝ, (1 + u ^ 2) * ‖𝓕 (p ξ) u‖) := by
  intro q σ p
  let cost (ξ : X) := ∫ u : ℝ, (1 + u ^ 2) * ‖𝓕 (p ξ) u‖
  have hpos (ξ) : 0 ≤ cost ξ := integral_nonneg fun u ↦ mul_nonneg (by positivity) (norm_nonneg _)
  exact summable_angular_heckePositiveDivisorMass_cost (F := F) φ μ χ hχ cost hpos
    (fun ξ ↦ fourier_cost_active φ μ σ ξ) (fun fs ↦ by
      simpa only [cost, p, pow_one] using
        (ideleClass_summable_angularProfile_fourierMoments μ φ fs 1).2)

end RiemannMasullo.StripNuclearity
