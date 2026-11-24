module

public import RiemannMasullo.Research.TraceComparison.LogLatticePoisson
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-! # A polar-free real test detected by the rational theta row at the prime two

Poisson summation makes the low-norm part of the double dilation difference
constant before its final subtraction. Its log integral is determined by this
constant and the length of a single translation.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory Set
open scoped FourierTransform SchwartzMap Topology

namespace RiemannMasullo.StripNuclearity

/-- Dilation of a Schwartz test on the additive real line. -/
def rationalSchwartzDilation (r : ℝ) (hr : r ≠ 0) (f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 r hr)) f

private theorem dilate_apply (r : ℝ) (hr : r ≠ 0) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    rationalSchwartzDilation r hr f x = f (x * r) := rfl

local notation "Z₀" => {n : ℤ // n ∉ ({0} : Finset ℤ)}

/-- The unsieved theta sum over both signs of the nonzero integers on the logarithmic axis. -/
def rationalLatticeTheta (f : 𝓢(ℝ, ℂ)) (t : ℝ) : ℂ :=
  ∑' n : Z₀, f (((n : ℤ) : ℝ) * Real.exp t)

/-- The dilation polynomial (1−D₂)(1−2D₂) on real Schwartz tests. -/
def primeTwoPolarTest (ψ : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  ψ - (3 : ℂ) • rationalSchwartzDilation 2 (by norm_num) ψ + (2 : ℂ) • rationalSchwartzDilation 4 (by norm_num) ψ

private theorem summable_lattice (f : 𝓢(ℝ, ℂ)) {x : ℝ} (hx : 0 < x) :
    Summable (fun n : ℤ ↦ f ((n : ℝ) * x)) := by
  let g := rationalSchwartzDilation x hx.ne' f
  exact summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
    ((g.isBigO_cocompact_rpow (-2)).comp_tendsto Int.tendsto_coe_cofinite)

private theorem theta_add_zero (f : 𝓢(ℝ, ℂ)) (t : ℝ) :
    f 0 + rationalLatticeTheta f t = ∑' n : ℤ, f ((n : ℝ) * Real.exp t) := by
  simpa [rationalLatticeTheta] using
    (summable_lattice f (Real.exp_pos t)).sum_add_tsum_subtype_compl ({0} : Finset ℤ)

private theorem theta_low (f : 𝓢(ℝ, ℂ)) (hc : HasCompactSupport ((𝓕 f : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) :
    ∃ T : ℝ, ∀ t < T, rationalLatticeTheta f t =
      (Real.exp (-t) : ℂ) * 𝓕 f 0 - f 0 := by
  obtain ⟨R, hR⟩ := (hc.image (continuous_abs : Continuous fun x : ℝ ↦ |x|)).bddAbove
  let c := max 1 (R + 1)
  have hcp : 0 < c := zero_lt_one.trans_le (le_max_left ..)
  refine ⟨-Real.log c, fun t ht ↦ ?_⟩
  have hsmall : c < Real.exp (-t) := by
    rw [← Real.exp_log hcp]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hzero (n : ℤ) (hn : n ≠ 0) : 𝓕 f ((n : ℝ) / Real.exp t) = 0 := by
    by_contra hne
    have hR' := hR (mem_image_of_mem (fun x : ℝ ↦ |x|) (subset_tsupport _ hne))
    have hN : 1 ≤ |(n : ℝ)| := by exact_mod_cast (Int.one_le_abs hn)
    rw [abs_div, abs_of_pos (Real.exp_pos _), div_eq_mul_inv, ← Real.exp_neg] at hR'
    have hN' : Real.exp (-t) ≤ |(n : ℝ)| * Real.exp (-t) :=
      le_mul_of_one_le_left (Real.exp_pos _).le hN
    linarith [le_max_right 1 (R+1)]
  have hsum := (hasSum_fourier_logLattice f (Real.exp_pos t)).tsum_eq
  rw [tsum_eq_single 0 hzero] at hsum
  simp only [Int.cast_zero, zero_div] at hsum
  have he : ((Real.exp (-t) : ℝ) : ℂ) * ↑(Real.exp t) = 1 := by
    rw [Real.exp_neg, Complex.ofReal_inv, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne')]
  rw [← theta_add_zero] at hsum
  rw [hsum, ← mul_assoc, he, one_mul]
  abel

private theorem theta_measurable (f : 𝓢(ℝ, ℂ)) : Measurable (rationalLatticeTheta f) :=
  Measurable.tsum fun _ ↦ f.continuous.measurable.comp (measurable_const.mul Real.measurable_exp)

private theorem theta_integrableOn_right (f : 𝓢(ℝ, ℂ)) (c b : ℝ) :
    IntegrableOn (fun t ↦ rationalLatticeTheta f (t + b)) (Ici c) := by
  let K := SchwartzMap.seminorm ℝ 2 0 f
  let w (n : Z₀) := 1 / (((n : ℤ) : ℝ) ^ 2)
  have hw : Summable w := ((Real.summable_one_div_int_pow (p := 2)).mpr (by norm_num)).subtype _
  have bound (t : ℝ) (n : Z₀) :
      ‖f (((n : ℤ) : ℝ) * Real.exp t)‖ ≤ (K * Real.exp (-2 * t)) * w n := by
    have hn : ((n : ℤ) : ℝ) ≠ 0 := by exact_mod_cast (show (n : ℤ) ≠ 0 by simpa using n.property)
    have h := SchwartzMap.norm_pow_mul_le_seminorm ℝ f 2 (((n : ℤ) : ℝ) * Real.exp t)
    rw [Real.norm_eq_abs, sq_abs, mul_pow] at h
    have he : Real.exp (-2 * t) = (Real.exp t ^ 2)⁻¹ := by
      rw [show -2 * t = -(t+t) by ring, Real.exp_neg, Real.exp_add, sq]
    rw [he]
    dsimp only [w, K]
    rw [show ∀ k : ℝ, k * (Real.exp t ^ 2)⁻¹ * (1 / ((n : ℤ) : ℝ) ^ 2) =
        k / (((n : ℤ) : ℝ) ^ 2 * Real.exp t ^ 2) from fun k ↦ by ring]
    apply (le_div_iff₀ (mul_pos (sq_pos_of_ne_zero hn) (sq_pos_of_pos (Real.exp_pos t)))).mpr
    linarith only [h]
  let C := K * (∑' n, w n) * Real.exp (-2 * b)
  have h_exp : IntegrableOn (fun t ↦ C * Real.exp (-2 * t)) (Ici c) :=
    ((integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr
      (integrableOn_exp_mul_Ioi (by norm_num : (-2 : ℝ) < 0) c)).const_mul C
  apply h_exp.mono' ((theta_measurable f).comp (measurable_id.add_const b)).aestronglyMeasurable
  filter_upwards with t
  have h := norm_tsum_le_tsum_norm (f := fun n : Z₀ ↦ f (((n : ℤ) : ℝ) * Real.exp (t+b)))
    ((summable_lattice f (Real.exp_pos _)).subtype _).norm
  apply h.trans
  calc
    _ ≤ ∑' n, (K * Real.exp (-2 * (t+b))) * w n :=
      ((summable_lattice f (Real.exp_pos _)).subtype _).norm.tsum_le_tsum (bound (t+b)) (hw.mul_left _)
    _ = C * Real.exp (-2*t) := by
      rw [tsum_mul_left, mul_add, Real.exp_add]
      dsimp only [C]
      ring

/-- If a function is constant on a left half-line and integrable on its complement,
the integral of its difference under a positive translation is the constant times
the translation length. -/
theorem integral_step_difference (v : ℝ → ℂ) (c : ℂ) {L : ℝ} (hL : 0 ≤ L)
    (d : ℝ) (hv : ∀ t < d, v t = c) (hi : IntegrableOn v (Ici d)) :
    Integrable (fun t ↦ v t - v (t + L)) ∧ (∫ t, v t - v (t + L)) = (L : ℂ) * c := by
  let w := (Ici d).indicator v
  have hw : Integrable w := (integrable_indicator_iff measurableSet_Ici).mpr hi
  have hwL : Integrable (fun t ↦ w (t+L)) := (measurePreserving_add_right volume L).integrable_comp_of_integrable hw
  let u := (Ico (d - L) d).indicator (fun _ : ℝ ↦ c)
  have hu : Integrable u := (integrable_indicator_iff measurableSet_Ico).mpr
    (integrableOn_const (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top))
  have heq : (fun t ↦ v t - v (t+L)) = fun t ↦ (w t - w (t+L)) + u t := by
    funext t
    by_cases h₁ : d ≤ t
    · have h₂ : d ≤ t + L := by linarith
      have ho : t ∉ Ico (d - L) d := fun h ↦ h.2.not_ge h₁
      simp only [w, u, indicator_of_mem (mem_Ici.mpr h₁), indicator_of_mem (mem_Ici.mpr h₂),
        indicator_of_notMem ho, add_zero]
    · have h₁' : t < d := lt_of_not_ge h₁
      by_cases h₂ : d ≤ t + L
      · have ho : t ∈ Ico (d - L) d := ⟨by linarith, h₁'⟩
        simp only [w, u, indicator_of_notMem (show t ∉ Ici d from h₁), indicator_of_mem (mem_Ici.mpr h₂),
          indicator_of_mem ho, hv t h₁']
        abel
      · have ho : t ∉ Ico (d - L) d := fun hh ↦ h₂ (by linarith [hh.1])
        simp only [w, u, indicator_of_notMem (show t ∉ Ici d from h₁),
          indicator_of_notMem (show t+L ∉ Ici d from h₂), indicator_of_notMem ho, hv t h₁',
          hv _ (lt_of_not_ge h₂), sub_self, add_zero]
  rw [heq]
  refine ⟨(hw.sub hwL).add hu, ?_⟩
  have hsub : Integrable (fun t ↦ w t - w (t+L)) := hw.sub hwL
  rw [integral_add hsub hu, integral_sub hw hwL,
    integral_add_right_eq_self w L, sub_self, zero_add, integral_indicator measurableSet_Ico,
    setIntegral_const, Real.volume_real_Ico, sub_sub_cancel, max_eq_left hL,
    Complex.real_smul]

private theorem theta_difference (ψ : 𝓢(ℝ, ℂ)) (t : ℝ) :
    rationalLatticeTheta (primeTwoPolarTest ψ) t =
      (rationalLatticeTheta ψ t - 2 * rationalLatticeTheta ψ (t + Real.log 2)) -
      (rationalLatticeTheta ψ (t + Real.log 2) - 2 * rationalLatticeTheta ψ ((t + Real.log 2) + Real.log 2)) := by
  let L := Real.log 2
  let q (b : ℝ) (n : Z₀) := ψ (((n : ℤ) : ℝ) * Real.exp b)
  have hs b : Summable (q b) := (summable_lattice ψ (Real.exp_pos b)).subtype _
  have h (n : Z₀) : primeTwoPolarTest ψ (((n : ℤ) : ℝ) * Real.exp t) =
      q t n - 3 * q (t+L) n + 2 * q (t+L+L) n := by
    change _ - 3 * ψ ((_ * Real.exp t) * 2) + 2 * ψ ((_ * Real.exp t) * 4) = _
    simp only [q, L, Real.exp_add, Real.exp_log (by norm_num : (0:ℝ)<2)]
    congr 2 <;> ring_nf
  change (∑' n : Z₀, primeTwoPolarTest ψ (((n : ℤ) : ℝ) * Real.exp t)) = _
  simp_rw [h]
  rw [(((hs t).sub ((hs (t+L)).mul_left 3))).tsum_add ((hs (t+L+L)).mul_left 2),
    (hs t).tsum_sub ((hs (t+L)).mul_left 3), tsum_mul_left, tsum_mul_left]
  change _ = ((tsum (q t)) - 2 * tsum (q (t+L))) - (tsum (q (t+L)) - 2 * tsum (q (t+L+L)))
  ring

/-- For the two-sided rational theta sum, the dilation polynomial gives a log-integrable
function whose integral is the value of the original test at zero times log 2. -/
theorem integral_primeTwoPolarTest (ψ : 𝓢(ℝ, ℂ))
    (hψ : HasCompactSupport ((𝓕 ψ : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) :
    Integrable (rationalLatticeTheta (primeTwoPolarTest ψ)) ∧
      (∫ t, rationalLatticeTheta (primeTwoPolarTest ψ) t) = (Real.log 2 : ℂ) * ψ 0 := by
  let L := Real.log 2
  let v (t : ℝ) := rationalLatticeTheta ψ t - 2 * rationalLatticeTheta ψ (t+L)
  obtain ⟨T, hT⟩ := theta_low ψ hψ
  have hL : 0 ≤ L := Real.log_nonneg (by norm_num)
  have hv (t : ℝ) (ht : t < T - L) : v t = ψ 0 := by
    dsimp only [v]
    rw [hT _ (by linarith), hT _ (by linarith), neg_add_rev, Real.exp_add, Real.exp_neg L,
      Real.exp_log (by norm_num : (0:ℝ)<2)]
    push_cast
    ring
  have hi : IntegrableOn v (Ici (T-L)) := by
    have h₁ : IntegrableOn (rationalLatticeTheta ψ) (Ici (T-L)) := by
      simpa only [add_zero] using theta_integrableOn_right ψ (T-L) 0
    exact h₁.sub ((theta_integrableOn_right ψ (T-L) L).const_mul 2)
  have hh := integral_step_difference v (ψ 0) hL (T-L) hv hi
  simpa only [funext (theta_difference ψ), v, L] using hh

/-- A Fourier-compact test of zero integral has lower lattice cusp minus its value at zero.
Removing multiples of a prime therefore gives the negative boundary value times its log. -/
theorem integral_rationalLatticeTheta_sub_shift_of_fourier_zero (f : 𝓢(ℝ, ℂ))
    (hc : HasCompactSupport ((𝓕 f : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) (h0 : 𝓕 f 0 = 0) {L : ℝ} (hL : 0 ≤ L) :
    Integrable (fun t ↦ rationalLatticeTheta f t - rationalLatticeTheta f (t+L)) ∧
      (∫ t, rationalLatticeTheta f t - rationalLatticeTheta f (t+L)) = -(L : ℂ) * f 0 := by
  obtain ⟨T, hT⟩ := theta_low f hc
  have left (t : ℝ) (ht : t < T) : rationalLatticeTheta f t = -f 0 := by
    simp only [hT t ht, h0, mul_zero, zero_sub]
  have right : IntegrableOn (rationalLatticeTheta f) (Ici T) := by
    simpa only [add_zero] using theta_integrableOn_right f T 0
  simpa only [mul_neg, neg_mul] using integral_step_difference (rationalLatticeTheta f) (-f 0) hL T left right

private theorem fourier_dilate (ψ : 𝓢(ℝ, ℂ)) (r : ℝ) (hr : 0 < r) (u : ℝ) :
    𝓕 (rationalSchwartzDilation r hr.ne' ψ) u = ((r : ℂ)⁻¹) * 𝓕 ψ (u/r) := by
  simp only [SchwartzMap.fourier_coe, Real.fourier_real_eq]
  have hphase (x : ℝ) : x * r * (u / r) = x * u := by field_simp
  simpa only [dilate_apply, hphase, abs_of_pos (inv_pos.mpr hr), Complex.real_smul, smul_eq_mul, Complex.ofReal_inv] using
    Measure.integral_comp_mul_right (fun x : ℝ ↦ 𝐞 (-(x * (u / r))) • ψ x) r

private theorem primeTwoPolarTest_fourier (ψ : 𝓢(ℝ, ℂ)) (u : ℝ) :
    𝓕 (primeTwoPolarTest ψ) u = 𝓕 ψ u - (3 / 2 : ℂ) * 𝓕 ψ (u/2) + (1/2 : ℂ) * 𝓕 ψ (u/4) := by
  rw [primeTwoPolarTest, FourierTransform.fourier_add, FourierTransform.fourier_sub,
    FourierTransform.fourier_smul, FourierTransform.fourier_smul]
  change 𝓕 ψ u - 3 * 𝓕 (rationalSchwartzDilation 2 _ ψ) u + 2 * 𝓕 (rationalSchwartzDilation 4 _ ψ) u = _
  rw [fourier_dilate ψ 2 (by norm_num), fourier_dilate ψ 4 (by norm_num)]
  push_cast
  ring

private theorem fourier_compact_div (ψ : 𝓢(ℝ, ℂ))
    (hc : HasCompactSupport ((𝓕 ψ : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) {r : ℝ} (hr : r ≠ 0) :
    HasCompactSupport (fun u : ℝ ↦ 𝓕 ψ (u / r)) := by
  let e := ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 r⁻¹ (inv_ne_zero hr))
  convert hc.comp_homeomorph e.toHomeomorph using 1
  funext u
  change 𝓕 ψ (u / r) = 𝓕 ψ (u * r⁻¹)
  rw [div_eq_mul_inv]

/-- The dyadic dilation polynomial preserves evenness and compact Fourier support, and
annuls both the original and Fourier values at the origin. -/
theorem primeTwoPolarTest_polar (ψ : 𝓢(ℝ, ℂ)) (he : Function.Even (ψ : ℝ → ℂ))
    (hc : HasCompactSupport ((𝓕 ψ : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) :
    Function.Even (primeTwoPolarTest ψ : ℝ → ℂ) ∧
      HasCompactSupport ((𝓕 (primeTwoPolarTest ψ) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) ∧
      primeTwoPolarTest ψ 0 = 0 ∧ 𝓕 (primeTwoPolarTest ψ) 0 = 0 := by
  refine ⟨fun x ↦ ?_, ?_, ?_, ?_⟩
  · change ψ (-x) - 3 * ψ (-x * 2) + 2 * ψ (-x * 4) = ψ x - 3 * ψ (x * 2) + 2 * ψ (x * 4)
    rw [neg_mul, neg_mul, he, he, he]
  · change HasCompactSupport (fun u ↦ 𝓕 (primeTwoPolarTest ψ) u)
    simp only [primeTwoPolarTest_fourier]
    exact (hc.sub ((fourier_compact_div ψ hc (by norm_num : (2 : ℝ) ≠ 0)).mul_left)).add
      ((fourier_compact_div ψ hc (by norm_num : (4 : ℝ) ≠ 0)).mul_left)
  · change ψ 0 - 3 * ψ (0*2) + 2 * ψ (0*4) = 0
    simp only [zero_mul]
    ring
  · rw [primeTwoPolarTest_fourier]
    simp only [zero_div]
    ring

/-- A real even Schwartz function with compact Fourier support and value one at the origin. -/
theorem exists_real_even_fourier_compact_schwartz :
    ∃ ψ : 𝓢(ℝ, ℂ), Function.Even (ψ : ℝ → ℂ) ∧ (∀ x, (ψ x).im = 0) ∧
      HasCompactSupport ((𝓕 ψ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) ∧ ψ 0 = 1 := by
  let β : ContDiffBump (0:ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  have hc : HasCompactSupport (fun x : ℝ ↦ (β.normed volume x : ℂ)) :=
    β.hasCompactSupport_normed.comp_left Complex.ofReal_zero
  let g : 𝓢(ℝ, ℂ) := hc.toSchwartzMap (Complex.ofRealCLM.contDiff.comp β.contDiff_normed)
  have hneg (x : ℝ) : g (-x) = g x := congrArg Complex.ofReal (β.normed_neg x)
  have hconj (x : ℝ) : starRingEnd ℂ (g x) = g x := Complex.conj_ofReal _
  have hg : (g : ℝ → ℂ) ∘ LinearIsometryEquiv.neg ℝ = g := funext hneg
  have hF (u : ℝ) : 𝓕 g (-u) = 𝓕 g u := by
    simp only [SchwartzMap.fourier_coe]
    have eqn := (Real.fourier_comp_linearIsometry (LinearIsometryEquiv.neg ℝ) (g : ℝ → ℂ) u).symm
    rw [hg] at eqn
    simpa only [LinearIsometryEquiv.coe_neg] using eqn
  have hreal (u : ℝ) : starRingEnd ℂ (𝓕 g u) = 𝓕 g (-u) := by
    simp only [SchwartzMap.fourier_coe, Real.fourier_real_eq, Circle.smul_def, smul_eq_mul]
    rw [← integral_conj]
    apply integral_congr_ae
    filter_upwards with x
    rw [map_mul, hconj, ← Circle.coe_inv_eq_conj, ← AddChar.map_neg_eq_inv]
    ring_nf
  have hmass : (∫ x : ℝ, g x) = 1 := by
    change (∫ x : ℝ, ((β.normed volume x : ℝ) : ℂ)) = 1
    rw [integral_complex_ofReal, β.integral_normed, Complex.ofReal_one]
  refine ⟨𝓕⁻ g, ?_, ?_, ?_, ?_⟩
  · intro x
    change 𝓕 g (- -x) = 𝓕 g (-x)
    rw [neg_neg, hF]
  · intro x
    change (𝓕 g (-x)).im = 0
    exact Complex.conj_eq_iff_im.mp ((hreal (-x)).trans (hF (-x)))
  · rw [FourierTransform.fourier_fourierInv_eq]
    exact hc
  · change 𝓕 g (-(0:ℝ)) = 1
    simpa [SchwartzMap.fourier_coe, Real.fourier_real_eq] using hmass

/-- The normalized theta scalar on the rational logarithmic axis. -/
def rationalHalfTwistedLatticeTheta (f : 𝓢(ℝ, ℂ)) (t : ℝ) : ℂ :=
  (Real.exp (t/2) : ℂ) * rationalLatticeTheta f t

/-- An even real-valued, band-limited polar-free test on which the half-twisted row is log 2. -/
theorem exists_primeTwoPolarWitness :
    ∃ f : 𝓢(ℝ, ℂ), Function.Even (f : ℝ → ℂ) ∧ (∀ x, (f x).im = 0) ∧
      HasCompactSupport ((𝓕 f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) ∧ f 0 = 0 ∧ 𝓕 f 0 = 0 ∧
      Integrable (fun t ↦ (Real.exp (-(t/2)) : ℂ) * rationalHalfTwistedLatticeTheta f t) ∧
        (∫ t, (Real.exp (-(t/2)) : ℂ) * rationalHalfTwistedLatticeTheta f t) = ↑(Real.log 2) := by
  obtain ⟨ψ, he, hr, hc, h0⟩ := exists_real_even_fourier_compact_schwartz
  obtain ⟨hef, hcf, h₀, h₁⟩ := primeTwoPolarTest_polar ψ he hc
  refine ⟨primeTwoPolarTest ψ, hef, ?_, hcf, h₀, h₁, ?_⟩
  · intro x
    change (ψ x - 3 * ψ (x*2) + 2 * ψ (x*4)).im = 0
    simp [Complex.add_im, Complex.sub_im, Complex.mul_im, hr]
  · simpa only [rationalHalfTwistedLatticeTheta, ← mul_assoc, ← Complex.ofReal_mul,
      ← Real.exp_add, neg_add_cancel, Real.exp_zero, Complex.ofReal_one, one_mul, h0,
      mul_one] using integral_primeTwoPolarTest ψ hc

/-- Removing the integer multiples of a positive integer is subtraction of a log translation
of the unsieved nonzero lattice. Both sums count both signs. -/
theorem rationalLatticeTheta_sieve (f : 𝓢(ℝ, ℂ)) {p : ℕ} (hp : 0 < p) (t : ℝ) :
    (∑' n : {n : ℤ // ¬ (p : ℤ) ∣ n}, f (((n : ℤ) : ℝ) * Real.exp t)) =
      rationalLatticeTheta f t - rationalLatticeTheta f (t + Real.log p) := by
  let S : Set ℤ := {n | (p : ℤ) ∣ n}
  have hS : S = Set.range (fun n : ℤ ↦ (p : ℤ) * n) := by
    ext n
    exact ⟨fun ⟨m, hm⟩ ↦ ⟨m, hm.symm⟩, fun ⟨m, hm⟩ ↦ ⟨m, hm.symm⟩⟩
  have hinj : Injective (fun n : ℤ ↦ (p : ℤ) * n) :=
    fun _ _ hh ↦ mul_left_cancel₀ (by exact_mod_cast hp.ne') hh
  have hM : (∑' n : S, f (((n : ℤ) : ℝ) * Real.exp t)) =
      f 0 + rationalLatticeTheta f (t + Real.log p) := by
    rw [hS, tsum_range (fun n : ℤ ↦ f ((n : ℝ) * Real.exp t)) hinj, theta_add_zero,
      Real.exp_add, Real.exp_log (by exact_mod_cast hp)]
    apply tsum_congr
    intro n
    push_cast
    ring_nf
  have hAll := (summable_lattice f (Real.exp_pos t)).tsum_subtype_add_tsum_subtype_compl S
  rw [hM, ← theta_add_zero] at hAll
  linear_combination hAll

/-- A half-twisted translation leaves the weighted row invariant on its integrable domain.
The same row vanishes on the difference of a vector and its translate. -/
theorem integral_halfTwisted_translation (F : ℝ → ℂ) (L : ℝ)
    (hi : Integrable (fun t : ℝ ↦ (Real.exp (-(t / 2)) : ℂ) * F t)) :
    let w (t : ℝ) : ℂ := Real.exp (-(t / 2))
    let T (t : ℝ) := (Real.exp (-(L / 2)) : ℂ) * F (t + L)
    Integrable (fun t ↦ w t * T t) ∧ (∫ t, w t * T t) = (∫ t, w t * F t) ∧
      (∫ t, w t * (F t - T t)) = 0 := by
  dsimp only
  let f (t : ℝ) := (Real.exp (-(t / 2)) : ℂ) * F t
  have eqn : (fun t : ℝ ↦ (Real.exp (-(t / 2)) : ℂ) *
      ((Real.exp (-(L / 2)) : ℂ) * F (t + L))) = fun t ↦ f (t + L) := by
    funext t
    dsimp only [f]
    rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add, add_div, neg_add]
  have hshift : Integrable (fun t ↦ f (t + L)) :=
    (measurePreserving_add_right volume L).integrable_comp_of_integrable hi
  simp_rw [mul_sub, congrFun eqn]
  exact ⟨hshift, integral_add_right_eq_self f L,
    by rw [integral_sub hi hshift, integral_add_right_eq_self f L, sub_self]⟩

/-- The row of the actual sieve on a Fourier-compact real-place test of integral zero. -/
theorem integral_rationalLatticeTheta_sieve (f : 𝓢(ℝ, ℂ))
    (hc : HasCompactSupport ((𝓕 f : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) (h₀ : 𝓕 f 0 = 0)
    {p : ℕ} (hp : 0 < p) :
    Integrable (fun t ↦ ∑' n : {n : ℤ // ¬ (p : ℤ) ∣ n}, f (((n : ℤ) : ℝ) * Real.exp t)) ∧
      (∫ t, ∑' n : {n : ℤ // ¬ (p : ℤ) ∣ n}, f (((n : ℤ) : ℝ) * Real.exp t)) =
        -(Real.log p : ℂ) * f 0 := by
  simp only [rationalLatticeTheta_sieve f hp]
  exact integral_rationalLatticeTheta_sub_shift_of_fourier_zero f hc h₀
    (Real.log_nonneg (by exact_mod_cast Nat.succ_le_of_lt hp))

/-- A single real profile of integral zero and value one at the origin gives
row value −log p after removal of the multiples of p, simultaneously at every prime. -/
theorem exists_rationalLatticeTheta_sieve_witness :
    ∃ f : 𝓢(ℝ, ℂ), Function.Even (f : ℝ → ℂ) ∧ (∀ x, (f x).im = 0) ∧
      HasCompactSupport ((𝓕 f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) ∧ f 0 = 1 ∧ 𝓕 f 0 = 0 ∧
      ∀ p : ℕ, 0 < p →
        (∫ t, ∑' n : {n : ℤ // ¬ (p : ℤ) ∣ n}, f (((n : ℤ) : ℝ) * Real.exp t)) =
          -↑(Real.log p) := by
  obtain ⟨ψ, he, hr, hc, hzero⟩ := exists_real_even_fourier_compact_schwartz
  let f := (2 : ℂ) • rationalSchwartzDilation 2 (by norm_num) ψ - ψ
  have hf (u : ℝ) : 𝓕 f u = 𝓕 ψ (u / 2) - 𝓕 ψ u := by
    dsimp only [f]
    rw [FourierTransform.fourier_sub, FourierTransform.fourier_smul]
    change 2 * 𝓕 (rationalSchwartzDilation 2 _ ψ) u - 𝓕 ψ u = _
    rw [fourier_dilate ψ 2 (by norm_num)]
    push_cast
    ring
  have hfc : HasCompactSupport ((𝓕 f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) := by
    change HasCompactSupport (fun u ↦ 𝓕 f u)
    simp only [hf]
    exact (fourier_compact_div ψ hc (by norm_num : (2 : ℝ) ≠ 0)).sub hc
  have h₀ : f 0 = 1 := by
    change 2 * ψ (0 * 2) - ψ 0 = 1
    norm_num [hzero]
  have h₁ : 𝓕 f 0 = 0 := by simp [hf]
  refine ⟨f, ?_, ?_, hfc, h₀, h₁, ?_⟩
  · intro x
    change 2 * ψ (-x * 2) - ψ (-x) = 2 * ψ (x * 2) - ψ x
    rw [neg_mul, he, he]
  · intro x
    change (2 * ψ (x * 2) - ψ x).im = 0
    simp [Complex.sub_im, Complex.mul_im, hr]
  · intro p hp
    simpa only [h₀, mul_one] using
      (integral_rationalLatticeTheta_sieve f hfc h₁ hp).2

end RiemannMasullo.StripNuclearity
