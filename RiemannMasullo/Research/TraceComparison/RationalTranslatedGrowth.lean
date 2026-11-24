module

public import RiemannMasullo.Research.TraceComparison.RationalTranslatedDiagonal
public import RiemannMasullo.Research.TraceComparison.RationalTranslatedPlaces
import RiemannMasullo.Research.TraceComparison.RationalComparisonData
import RiemannMasullo.Research.TraceComparison.RationalDedekindNonvanishing
import RiemannMasullo.Research.StripNuclearity.RationalBoundedWindow
import RiemannMasullo.ForMathlib.Analysis.Complex.ExpSumUniqueness

/-! # Growth of the translated rational trace and its visible zeta zeros -/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set
open scoped Asymptotics ContDiff NNReal Topology
open RiemannMasullo.External.Grh

namespace RiemannMasullo.StripNuclearity

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

set_option quotPrecheck false
local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "μℚ" => ideleClassTamagawaMeasure ℚ
local notation "Vℚ" => (((normOneIdeleClassTamagawaMeasure ℚ) univ).toReal : ℂ)
local notation "logN(" x ")" => Real.log (((ideleClassNorm ℚ) (x : Cℚ)).val : ℝ)
local notation "physical(" g "," y "," x ")" => rationalCenteredLogProfile g (logN(x) - y)
local notation "wide(" φ "," hs "," U ")" =>
  centeredStripGeometricDiagonalIntegral φ (by norm_num : (0:ℝ) < 1/2) hs U

private theorem shifted_zero_eventually_avoids (z : ℂ) : ∀ᶠ u in 𝓝[≠] z, u ∉ range shiftedZetaZero := by
  obtain ⟨δ,hδ,hd⟩ := shiftedZetaZero_separated z
  filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds z hδ), self_mem_nhdsWithin] with u hu hn
  rintro ⟨ρ,rfl⟩
  exact (not_lt.mpr (hd ρ hn)) (by simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hu)

/-- Paper: Section 12.3, p. 514, and (12.5.1.4), p. 520. For a fixed rational radial
test on the positive log half-line, the wide diagonal of its translates is bounded by
O(exp(a y)) exactly when every ordinary zeta zero visible to its Mellin transform lies
in Re ρ ≤ 1/2 + a. The smoothing and Sobolev order may vary with y.
Deviation: The converse uses uniqueness of an absolutely convergent Laplace expansion. -/
theorem rational_translated_wide_diagonal_isBigO_iff (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (hzero : ∀ t ≤ 0, g t = 0)
    (φ : ℝ → BruhatCompactSupport Cℚ) (hφ : ∀ y x, (φ y).val x = physical(g,y,x))
    (s : ℝ → ℝ) (hs : ∀ y, 3 ≤ s y) (U : ℝ → ℕ → Set Cℚ)
    (hU : ∀ y, IsDPrimeSequence μℚ (U y)) (hm : ∀ y n, MeasurableSet (U y n)) (a : ℝ) :
    ((fun y ↦ wide(φ y,hs y,U y)) =O[atTop] (fun y ↦ Real.exp (a*y))) ↔
      ∀ z : criticalStripZetaZeros, compactLogMellin g z.val ≠ 0 → z.val.re ≤ 1/2 + a := by
  let b (z : criticalStripZetaZeros) := Vℚ * (zetaZeroOrder z : ℂ) * compactLogMellin g z.val
  have hb : Summable b := by
    simpa only [b, mul_assoc] using (completedZeta_explicit_formula hg hc).2.2.1.of_norm.mul_left Vℚ
  have hshift (z : criticalStripZetaZeros) : (shiftedZetaZero z).re = z.val.re-1/2 := by simp [shiftedZetaZero]
  have heq : (fun y ↦ -wide(φ y,hs y,U y)) =ᶠ[atTop]
      (fun y : ℝ ↦ ∑' z, b z * Complex.exp (shiftedZetaZero z*y)) := by
    filter_upwards [eventually_ge_atTop (0:ℝ)] with y hy
    have H := hasSum_translatedZeta_neg_diagonal g y (hzero _ (neg_nonpos.mpr hy)) (φ y) (hφ y)
      (by norm_num : (0:ℝ)<1/2) (hs y) (U y) (hU y) (hm y)
    rw [← H.tsum_eq]
    apply tsum_congr
    intro z
    have hz := abs_re_shiftedZetaZero_lt z
    rw [hshift] at hz
    rw [spectralStripMultiplicity_interior (abs_lt.mp hz)]
  have hM (z : criticalStripZetaZeros) : b z ≠ 0 ↔ compactLogMellin g z.val ≠ 0 := by
    have h₀ := mul_ne_zero rationalNormOneTamagawaVolume_ne_zero
      (Nat.cast_ne_zero.mpr (zetaZeroOrder_pos z).ne' : (zetaZeroOrder z : ℂ) ≠ 0)
    simp [b, h₀]
  have hh := expSum_isBigO_iff shiftedZetaZero b shiftedZetaZero_injective shifted_zero_eventually_avoids
    (fun z ↦ (le_abs_self _).trans (abs_re_shiftedZetaZero_lt z).le) hb a
  rw [← Asymptotics.isBigO_neg_left, Asymptotics.isBigO_congr heq (Filter.EventuallyEq.rfl), hh]
  simp only [hM, hshift, sub_le_iff_le_add, add_comm a]

/-- The published seven-eighths zero-free half-plane gives a genuine O(exp(3y/8))
bound on the actual translated global trace, with no restriction on height. -/
theorem rational_translated_wide_diagonal_isBigO_of_zeta_seven_eighths
    (hn : ∀ {z : ℂ}, (7/8:ℝ) < z.re → riemannZeta z ≠ 0)
    (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (hzero : ∀ t ≤ 0, g t = 0)
    (φ : ℝ → BruhatCompactSupport Cℚ) (hφ : ∀ y x, (φ y).val x = physical(g,y,x))
    (s : ℝ → ℝ) (hs : ∀ y, 3 ≤ s y) (U : ℝ → ℕ → Set Cℚ)
    (hU : ∀ y, IsDPrimeSequence μℚ (U y)) (hm : ∀ y n, MeasurableSet (U y n)) :
    (fun y ↦ wide(φ y,hs y,U y)) =O[atTop] (fun y ↦ Real.exp (3/8*y)) := by
  apply (rational_translated_wide_diagonal_isBigO_iff g hg hc hzero φ hφ s hs U hU hm _).mpr
  intro z _
  have h : z.val.re ≤ 7/8 := le_of_not_gt fun hh ↦ hn hh (mem_criticalStripZetaZeros.mp z.property).1
  linarith

/-- For a positive-log rational test, the all-prime error has exponent at most a
exactly when the Mellin-visible zeta zeros lie in Re ρ ≤ 1/2 + a. The local expression
uses all prime powers and the upper polar main term. No geometric comparison or
zero-free region is assumed here. -/
theorem rational_translated_prime_error_isBigO_iff (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (hzero : ∀ t ≤ 0, g t = 0) {a : ℝ} (ha : 0 ≤ a) :
    (rationalTranslatedPrimeError (rationalCenteredLogProfile g) =O[atTop] (fun y ↦ Real.exp (a*y))) ↔
      ∀ z : criticalStripZetaZeros, compactLogMellin g z.val ≠ 0 → z.val.re ≤ 1/2 + a := by
  let G := rationalCenteredLogProfile g
  have hG : ContDiff ℝ ∞ G := (Complex.contDiff_exp.comp (Complex.ofRealCLM.contDiff.div_const 2)).mul hg
  have hgc : HasCompactSupport G := hc.mul_left
  obtain ⟨R,hR'⟩ := hgc.isCompact.isBounded.subset_closedBall (0 : ℝ)
  have hR : tsupport G ⊆ Icc (-R) R := by simpa [Real.closedBall_eq_Icc] using hR'
  obtain ⟨φ,hφ⟩ := exists_rational_translated_normTests g hg hc
  obtain ⟨U,hU,hop⟩ := exists_rational_regular_diagonal_sequence
  have hm (n : ℕ) := (hop n).1.measurableSet
  let d (y : ℝ) := wide(φ y,(le_refl (3:ℝ)),U)
  let C := ‖Vℚ‖ * (Real.exp (5*R/2) / (1-Real.exp (-2))) * (∫ u, ‖G u‖)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (mul_nonneg (norm_nonneg _) (div_nonneg (Real.exp_pos _).le
      (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by norm_num))))) (integral_nonneg (fun _ ↦ norm_nonneg _))
  have hd : (fun y ↦ d y - Vℚ * rationalTranslatedPrimeError G y) =O[atTop] (fun y ↦ Real.exp (a*y)) := by
    apply Asymptotics.IsBigO.of_bound C
    filter_upwards [eventually_ge_atTop (R+1), eventually_ge_atTop (0:ℝ)] with y hy hy₀
    have he := norm_rational_wide_diagonal_sub_translated_prime_error G hG hR hy (φ y) (hφ y)
      (α:=1/2) le_rfl (le_refl (3:ℝ)) U hU hm
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    apply he.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) hC)
    linarith [mul_nonneg ha hy₀]
  have hv := hd.congr_of_sub
  rw [Asymptotics.isBigO_const_mul_left_iff rationalNormOneTamagawaVolume_ne_zero] at hv
  exact hv.symm.trans (rational_translated_wide_diagonal_isBigO_iff g hg hc hzero φ hφ
    (fun _ ↦ 3) (fun _ ↦ le_rfl) (fun _ ↦ U) (fun _ ↦ hU) (fun _ ↦ hm) a)

/-- Almost every real exponential tilt of one compact smooth profile with nonzero
total integral detects the full zero band through its translated prime error.
A single such tilt works simultaneously for all nonnegative exponents. -/
theorem ae_rational_tilted_prime_error_isBigO_iff (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (hzero : ∀ t ≤ 0, g t = 0) (hI : compactLogMellin g 0 ≠ 0) :
    ∀ᵐ b : ℝ, ∀ a : ℝ, 0 ≤ a →
      let f (x : ℝ) := Complex.exp ((b : ℂ)*x) * g x
      (rationalTranslatedPrimeError (rationalCenteredLogProfile f) =O[atTop] (fun y ↦ Real.exp (a*y))) ↔
        ∀ z : criticalStripZetaZeros, z.val.re ≤ 1/2+a := by
  filter_upwards [ae_real_tilt_mellin_ne_zero_at_all_zeta_zeros g hg.continuous hc hI] with b hb
  intro a ha f
  have hf : ContDiff ℝ ∞ f := (Complex.contDiff_exp.comp
    (contDiff_const.mul Complex.ofRealCLM.contDiff)).mul hg
  have hM (z : criticalStripZetaZeros) : compactLogMellin f z.val ≠ 0 := by
    have he : compactLogMellin f z.val = compactLogMellin g (z.val + (b:ℂ)) := by
      apply integral_congr_ae (.of_forall fun x ↦ ?_)
      simp only [f, add_mul, Complex.exp_add]
      ring
    exact he ▸ hb z
  rw [rational_translated_prime_error_isBigO_iff f hf hc.mul_left (fun x hx ↦ by simp [f,hzero x hx]) ha]
  exact ⟨fun h z ↦ h z (hM z), fun h z _ ↦ h z⟩

/-- Bounding every nontrivial zero from the right by 1/2 is ordinary RH. -/
private theorem all_zeta_zeros_re_le_half_iff :
    (∀ z : criticalStripZetaZeros, z.val.re ≤ 1/2) ↔ RiemannHypothesis := by
  constructor
  · intro h
    have hn (z : ℂ) (hs : 1/2 < z.re) (_ : z ≠ 1) : riemannZeta z ≠ 0 := by
      intro hz
      have hlt : z.re < 1 := lt_of_not_ge fun h1 ↦ riemannZeta_ne_zero_of_one_le_re h1 hz
      exact (not_le.mpr hs) (h ⟨z,mem_criticalStripZetaZeros.mpr ⟨hz,by linarith,hlt⟩⟩)
    apply (zeta_all_windows_retain_iff_riemannHypothesis 3).mp
    intro α hα z
    have hz := rational_centered_zero_band_of_riemannZeta_nonvanishing (1/2) hn z
    exact spectralStripMultiplicity_interior (abs_lt.mp (by linarith : |z.val.re-1/2| < α)) _ _
  · intro rh z
    obtain ⟨hz,hpos,hlt⟩ := mem_criticalStripZetaZeros.mp z.property
    have htriv : ¬ ∃ n : ℕ, z.val = -2 * (n+1) := by
      rintro ⟨n,he⟩
      rw [he] at hpos
      norm_num [Complex.mul_re] at hpos
      linarith [Nat.cast_nonneg (α := ℝ) n]
    exact (rh z.val hz htriv (fun he ↦ by simp [he] at hlt)).le

/-- For almost every real tilt of one prescribed smooth positive-log profile with
nonzero integral, boundedness of its translated all-prime error is equivalent to
Mathlib's ordinary Riemann hypothesis. -/
theorem ae_tilted_prime_error_bounded_iff_riemannHypothesis (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (hzero : ∀ t ≤ 0, g t = 0) (hI : compactLogMellin g 0 ≠ 0) :
    ∀ᵐ b : ℝ,
      let f (x : ℝ) := Complex.exp ((b : ℂ)*x) * g x
      (rationalTranslatedPrimeError (rationalCenteredLogProfile f) =O[atTop] (fun _ : ℝ ↦ (1:ℝ))) ↔
        RiemannHypothesis := by
  filter_upwards [ae_rational_tilted_prime_error_isBigO_iff g hg hc hzero hI] with b hb
  simpa only [zero_mul, Real.exp_zero, add_zero] using
    (hb 0 le_rfl).trans (by simpa only [add_zero] using all_zeta_zeros_re_le_half_iff)

end RiemannMasullo.StripNuclearity
