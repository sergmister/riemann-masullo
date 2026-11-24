module

public import RiemannMasullo.Research.StripNuclearity.WindowComparison
import all RiemannMasullo.Ch12_TraceGeometric.Sec5

/-! # Detecting the coefficients of a Hecke zero distribution

A translated angular test separates an individual zero using only functions
supported beyond any prescribed lower bound on the log norm.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing Topology ContDiff

namespace RiemannMasullo.StripNuclearity

variable {F : Type*} [Field F] [NumberField F]

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

set_option quotPrecheck false
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "X" => PontryaginDual C₁
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" => (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "hm𝔽" => (⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ : IsModulation m𝔽)
local notation "classVolume" => (((normOneIdeleClassTamagawaMeasure F) univ).toReal : ℂ)
local notation "D(" χ ")" => MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ
local notation "zeros(" χ ")" => {z : X × ℂ // 0 < D(χ z.1) z.2}
local notation "M(" φ ", " χ ", " z ")" =>
  modulatedFourierMellin m𝔽 univ hm𝔽 μ𝔽 (φ : BruhatCompactSupport C𝔽).val
    (ideleClassNormTwist (F := F) (χ (z).val.1) ((z).val.2 - 1/2))
local notation "logNorm(" x ")" => Real.log ((ideleClassNorm F x : ℝ≥0) : ℝ)

private theorem angular_eq_of_restriction (χ : X → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice χ) {ξ η : X}
    (h : ∀ u : C₁, (χ ξ * (χ η)⁻¹) u.val = 1) : ξ = η := by
  apply ContinuousMonoidHom.ext
  intro u
  have he (θ : X) : (χ θ) u.val = θ u := DFunLike.congr_fun (hχ θ) u
  exact (he ξ).symm.trans ((mul_inv_eq_one.mp (h u)).trans (he η))

open Classical in
/-- Paper: Section 12.3, p. 514, and (12.5.1.4), p. 520.
Deviation: For any choice of unitary angular extensions, a complex coefficient
at each completed Hecke zero is determined by its Mellin sums against compact
Bruhat tests supported above any prescribed lower bound on the log norm. -/
theorem heckeZeroCoeff_eq_zero_of_oneSided_mellin
    (χ : X → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ) (R : ℝ)
    (c : zeros(χ) → ℂ)
    (hT : ∀ φ : BruhatCompactSupport C𝔽, (∀ x : C𝔽, logNorm(x) ≤ R → φ.val x = 0) →
      HasSum (fun z ↦ c z * M(φ, χ, z)) 0) (z₀ : zeros(χ)) : c z₀ = 0 := by
  let χ₀ := χ z₀.val.1
  let w₀ : ℂ := z₀.val.2 - 1/2
  let β : ContDiffBump (R + 1/2) := ⟨1/8, 1/4, by norm_num, by norm_num⟩
  let H : ℝ → ℂ := fun x ↦ (β x : ℂ) * Complex.exp (-(w₀ * x))
  have hH : ContDiff ℝ (∞) H := (Complex.ofRealCLM.contDiff.comp β.contDiff).mul
    (Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff).neg)
  have hHc : HasCompactSupport H := (β.hasCompactSupport.comp_left Complex.ofReal_zero).mul_right
  have hlow (x : ℝ) (hx : x ≤ R) : H x = 0 := by
    have : β x = 0 := β.zero_of_le_dist (by
      rw [Real.dist_eq, abs_of_neg (by linarith)]
      change (1/4 : ℝ) ≤ _
      linarith)
    simp only [H, this, Complex.ofReal_zero, zero_mul]
  have hg (y : ℝ) : ContDiff ℝ (∞) (fun x ↦ H (x - y)) := hH.comp (contDiff_id.sub contDiff_const)
  have hc (y : ℝ) : HasCompactSupport (fun x ↦ H (x - y)) := hHc.comp_homeomorph (Homeomorph.subRight y)
  choose φ hφ using fun y : ℝ ↦ exists_characterNormTest (F := F) χ₀⁻¹ _ (hg y) (hc y)
  have hvan (y : ℝ) (hy : 0 ≤ y) (x : C𝔽) (hx : logNorm(x) ≤ R) : (φ y).val x = 0 := by
    rw [hφ y, hlow _ (by linarith), mul_zero]
  let K (w : ℂ) := ∫ x : ℝ, H x * Complex.exp (w * x)
  have hterm (y : ℝ) (z : zeros(χ)) : c z * M(φ y, χ, z) =
      if z.val.1 = z₀.val.1 then c z * (classVolume * K (z.val.2 - 1/2)) *
        Complex.exp ((z.val.2 - 1/2) * y) else 0 := by
    rw [characterNormTest_mellin _ (hg y) (hc y) χ₀⁻¹ (φ y) (hφ y)]
    by_cases he : z.val.1 = z₀.val.1
    · have hone : χ z.val.1 * χ₀⁻¹ = 1 := by rw [he, show χ₀ = χ z₀.val.1 from rfl, mul_inv_cancel]
      rw [ite_eq_left he, ite_eq_left (fun u ↦ by rw [hone]; rfl)]
      beta_reduce
      rw [grh_shift_integral H hH.continuous _ (fun t ↦ by rw [hone]; rfl) y]
      ring
    · rw [ite_eq_right he, ite_eq_right (fun h ↦ he (angular_eq_of_restriction χ hχ h)),
        zero_mul, mul_zero]
  let ι := {z : zeros(χ) // z.val.1 = z₀.val.1}
  let w (i : ι) := i.val.val.2 - 1/2
  let b (i : ι) := c i.val * (classVolume * K (w i))
  have hsum (y : ℝ) (hy : 0 ≤ y) : HasSum (fun i : ι ↦ b i * Complex.exp (w i * y)) 0 := by
    have h := hT (φ y) (hvan y hy)
    have hp : support (fun z : zeros(χ) ↦ c z * M(φ y, χ, z)) ⊆ {z | z.val.1 = z₀.val.1} := by
      intro z hz
      by_contra hne
      exact hz ((hterm y z).trans (ite_eq_right hne))
    apply ((hasSum_subtype_iff_of_support_subset hp).mpr h).congr_fun
    intro i
    exact ((hterm y i.val).trans (ite_eq_left i.property)).symm
  have hw : Injective w := by
    intro i j h
    exact Subtype.ext (Subtype.ext (Prod.ext (i.property.trans j.property.symm) (sub_left_inj.mp h)))
  have hd : ∀ z : ℂ, ∀ᶠ u in 𝓝[≠] z, u ∉ range w := fun z ↦ by
    filter_upwards [grh_zeros_discrete χ₀ z] with u hu
    rintro ⟨i, rfl⟩
    apply hu
    have h := i.val.property
    change 0 < D(χ₀) (i.val.val.2 - 1/2 + 1/2)
    rw [sub_add_cancel]
    rwa [i.property] at h
  have hre (i : ι) : (w i).re ≤ 1/2 := by
    have h := (heckePositiveDivisor_open_strip _ i.val.property).2
    change (i.val.val.2 - 1/2).re ≤ 1/2
    rw [Complex.sub_re]
    norm_num
    linarith
  have hb : Summable b := by simpa using (hsum 0 le_rfl).summable
  have h0 := eq_zero_of_hasSum_exp_eq_zero w b hw hd hre hb hsum ⟨z₀, rfl⟩
  have hK : K w₀ = ((∫ x, β x : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    exact integral_congr_ae (.of_forall fun x ↦ grh_bump_mul_exp _ _)
  have hKne : K w₀ ≠ 0 := hK ▸ Complex.ofReal_ne_zero.mpr β.integral_pos.ne'
  exact (mul_eq_zero.mp h0).resolve_right (mul_ne_zero grh_classVolume_ne_zero hKne)

local notation "mult(" χ ", " z ")" => (D(χ (z).val.1) (z).val.2).toNat
local notation "kept(" χ ", " α ", " s ", " z ")" =>
  spectralStripMultiplicity α s ((z).val.2.re - 1/2) mult(χ, z)

/-- Two zero distributions whose difference has the missing-jet expansion
agree on all tests beyond a fixed log norm exactly when every jet is retained. -/
theorem oneSided_comparison_iff_full_multiplicity
    (χ : X → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ) (α s R : ℝ)
    {d e : BruhatCompactSupport C𝔽 → ℂ}
    (h : ∀ φ : BruhatCompactSupport C𝔽, (∀ x : C𝔽, logNorm(x) ≤ R → φ.val x = 0) →
      HasSum (fun z : zeros(χ) ↦ ((mult(χ, z) - kept(χ, α, s, z) : ℕ) : ℂ) * M(φ, χ, z))
        (d φ - e φ)) :
    (∀ φ : BruhatCompactSupport C𝔽, (∀ x : C𝔽, logNorm(x) ≤ R → φ.val x = 0) → d φ = e φ) ↔
      ∀ z : zeros(χ), kept(χ, α, s, z) = mult(χ, z) := by
  constructor
  · intro he z
    have hz := heckeZeroCoeff_eq_zero_of_oneSided_mellin χ hχ R
      (fun z ↦ ((mult(χ, z) - kept(χ, α, s, z) : ℕ) : ℂ))
      (fun φ hφ ↦ by simpa only [he φ hφ, sub_self] using h φ hφ) z
    have hle : mult(χ, z) ≤ kept(χ, α, s, z) := Nat.sub_eq_zero_iff_le.mp (Nat.cast_eq_zero.mp hz)
    apply le_antisymm _ hle
    unfold spectralStripMultiplicity spectralBoundaryMultiplicity
    split_ifs <;> first | exact le_rfl | exact min_le_left _ _ | exact Nat.zero_le _
  · intro hz φ hφ
    apply sub_eq_zero.mp
    apply (h φ hφ).unique
    simpa only [hz, Nat.sub_self, Nat.cast_zero, zero_mul] using
      (hasSum_zero (α := ℂ) (β := zeros(χ)))

/-- One-sided support beyond nonnegative log norm implies vanishing on the norm-one subgroup. -/
theorem vanishes_on_normOne_of_oneSided {R : ℝ} (hR : 0 ≤ R) {φ : BruhatCompactSupport C𝔽}
    (hφ : ∀ x : C𝔽, logNorm(x) ≤ R → φ.val x = 0) (g : C₁) : φ.val g = 0 := by
  apply hφ
  simpa only [show ideleClassNorm F g.val = 1 from g.property, Units.val_one, NNReal.coe_one,
    Real.log_one] using hR

local notation "detect(" χ ", " hχ ", " α ", " s ", " R ", " hR ", " hα ", " hs ", " hβ ", " ht ", "
    U ", " V ", " hU ", " hmU ", " hV ", " hmV ")" =>
  oneSided_comparison_iff_full_multiplicity χ hχ α s R
    (fun φ hφ ↦ (hasSum_missingHeckeJets_centeredStripDiagonalIntegral_sub (F := F) φ
      (vanishes_on_normOne_of_oneSided hR hφ) χ hχ hα hs hβ ht U V hU hmU hV hmV).2)

/-- Paper: Section 12.3, p. 514, and (12.5.1.4), p. 520.
Deviation: At a fixed half-width, the actual projected and wide diagonals
agree on all tests supported above any prescribed nonnegative log norm
exactly when every positive Hecke divisor retains its entire multiplicity.
This includes possible partially represented edge zeros. -/
theorem oneSided_centeredStripDiagonal_comparison_iff
    (χ : X → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ) {R : ℝ} (hR : 0 ≤ R)
    {α s β t : ℝ} (hα : 0 < α) (hs : 3 ≤ s) (hβ : 1/2 ≤ β) (ht : 3 ≤ t)
    (U V : ℕ → Set C𝔽) (hU : IsDPrimeSequence μ𝔽 U) (hmU : ∀ n, MeasurableSet (U n))
    (hV : IsDPrimeSequence μ𝔽 V) (hmV : ∀ n, MeasurableSet (V n)) :
    type_of% detect(χ, hχ, α, s, R, hR, hα, hs, hβ, ht, U, V, hU, hmU, hV, hmV) :=
  detect(χ, hχ, α, s, R, hR, hα, hs, hβ, ht, U, V, hU, hmU, hV, hmV)

end RiemannMasullo.StripNuclearity
