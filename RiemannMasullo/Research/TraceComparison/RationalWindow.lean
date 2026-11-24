module

public import RiemannMasullo.Research.TraceComparison.FiniteWindowInterpolation
public import RiemannMasullo.Research.TraceComparison.RationalThetaSeries

/-! # Physical-window interpolation by the rational homogeneous theta -/

@[expose] public noncomputable section

open IsDedekindDomain MeasureTheory NumberField Set
open scoped ContDiff FourierTransform SchwartzMap

namespace RiemannMasullo.StripNuclearity

set_option quotPrecheck false

local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local instance : MeasurableSpace Cℚ := borel _
local notation "mass" => ((normOneIdeleClassTamagawaMeasure ℚ univ).toReal : ℂ)
local notation "N(" x ")" => ((ideleClassNorm ℚ (x)).val : ℝ)

/-- On each bounded upper norm window one honest adelic test interpolates a
prescribed smooth reciprocal profile. The real Fourier band is fixed and both
polar values vanish. The norm-one Haar mass is in the Chapter 10 normalization. -/
theorem exists_ratStandardAdelicTest_homogeneousTheta_window {a B : ℝ}
    (ha : 0 < a) (hB : 0 < B) (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (he : Function.Even g) (h₀ : g 0 = 0) (hband : ∀ x, B ≤ |x| → g x = 0) :
    ∃ f : 𝓢(ℝ, ℂ), Function.Even (f : ℝ → ℂ) ∧ f 0 = 0 ∧ (𝓕 f) 0 = 0 ∧
      (∀ x, B ≤ |x| → (𝓕 f) x = 0) ∧ ratStandardAdelicTest f ∈ adelePolarSubspace ℚ ∧
      ∀ y : Cℚ, a ≤ N(y)⁻¹ → homogeneousAdelicTheta 1 (ratStandardAdelicTest f) y =
        mass * ((↑(N(y)⁻¹) : ℂ) * (2 * g (N(y)⁻¹))) := by
  obtain ⟨f, hf, hf₀, hF₀, hFband, hsum⟩ :=
    exists_rational_theta_window_interpolant ha hB g hg he h₀ hband
  refine ⟨f, hf, hf₀, hF₀, hFband, (ratStandardAdelicTest_polar_iff f).2 ⟨hf₀, hF₀⟩, ?_⟩
  intro y hy
  let t := N(y)
  have hZ : HasSum (fun n : ℤ ↦ f ((n : ℝ) * t)) ((↑(t⁻¹) : ℂ) * (2 * g t⁻¹)) := by
    simpa only [div_inv_eq_mul] using hsum t⁻¹ hy
  have hsym : Function.Even (fun n : ℤ ↦ f ((n : ℝ) * t)) := by
    intro n
    simpa only [Int.cast_neg, neg_mul] using hf ((n : ℝ) * t)
  rw [ratStandardAdelicTest_homogeneousTheta f hf hf₀ y]
  apply congrArg (mass * ·)
  have h := hZ.tsum_eq
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat hsym hZ.summable] at h
  simp only [Int.cast_zero, zero_mul, hf₀, zero_add, Int.cast_natCast, nsmul_eq_mul] at h
  rw [tsum_pnat_eq_tsum_succ (f := fun n : ℕ ↦ f ((n : ℝ) * t))] at h
  simpa only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] using h

end RiemannMasullo.StripNuclearity
