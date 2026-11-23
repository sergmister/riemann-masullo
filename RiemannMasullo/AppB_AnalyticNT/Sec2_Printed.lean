module

public import RiemannMasullo.AppB_AnalyticNT.Sec2
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Appendix B.2: statements that are false as printed

The printed claim is kept as a proposition with a separate refutation statement.
Nothing imports this file.
-/

@[expose] public noncomputable section

namespace RiemannMasullo

/-- Paper: Theorem B.2.2.4(2), p. 602. As printed: for every holomorphic Schwartz
function on a left half-plane, every positive shift of the boundary to the left, and every
derivative order, the normalized Cauchy integral on the shifted line gives that derivative
to its left and zero to its right. These are (B.2.2.6) and (B.2.2.7).
The absolute convergence assertion is proved in
`cauchyKernel_verticalIntegrable_on_leftHalfPlane`. See ERRATA F14. -/
def Printed.asymptoticCauchy_leftHalfPlane : Prop :=
  ∀ (b : ℝ) (Φ : ℂ → ℂ), SchwartzOnLeftHalfPlane Φ b →
    ∀ ε > (0 : ℝ), ∀ (N : ℕ) (z : ℂ),
      let integral := (Nat.factorial N : ℂ) / (2 * (Real.pi : ℂ) * Complex.I) *
        verticalLineIntegral (fun s ↦ Φ s / (s - z) ^ (N + 1)) (b - ε)
      (z.re < b - ε → integral = iteratedDeriv N Φ z) ∧
        (b - ε < z.re → integral = 0)

/-! ### The counterexample to `Printed.asymptoticCauchy_leftHalfPlane`

Private helpers for `Printed.asymptoticCauchy_leftHalfPlane_false`, following ERRATA F14. -/

namespace AsymptoticCauchyCounterexample

open Complex Filter Set MeasureTheory Topology
open scoped FourierTransform


/-- The function `g(t) = exp(-t log t - t^(-1/2))` of the counterexample, continued to
`ℂ` with the principal logarithm and set to `0` at `t = 0`. -/
private noncomputable def G (t : ℂ) : ℂ :=
  if t = 0 then 0 else cexp (-(t * log t) - cexp (-(log t / 2)))

private theorem cos_half_arg_ge {t : ℂ} (hre : 0 ≤ t.re) : 1 / 2 ≤ Real.cos (-(arg t / 2)) := by
  have h := abs_arg_le_pi_div_two_iff.mpr hre
  have hpi := Real.pi_le_four
  have hpi0 := Real.pi_pos
  have hc := Real.one_sub_sq_div_two_le_cos (x := -(arg t / 2))
  have : (arg t)^2 ≤ (Real.pi/2)^2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
  nlinarith

private theorem norm_G_mul_exp_le {s t : ℂ} (h0 : t ≠ 0) (hre : 0 ≤ t.re) (him : t.im ≤ 0) :
    ‖G t * cexp (-(s * t))‖ ≤ Real.exp (-(t.re * (Real.log ‖t‖ + s.re)) +
      t.im * (s.im - Real.pi / 2) - Real.exp (-(Real.log ‖t‖ / 2)) / 2) := by
  simp only [G, h0, ↓reduceIte]
  rw [← Complex.exp_add, Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hc := cos_half_arg_ge hre
  have ha1 : -(Real.pi / 2) ≤ arg t := neg_pi_div_two_le_arg_iff.mpr (Or.inl hre)
  have ha2 : arg t ≤ 0 := by
    rcases him.lt_or_eq with h | h
    · exact (arg_neg_iff.mpr h).le
    · have : t = (t.re : ℂ) := by apply Complex.ext <;> simp [h]
      rw [this, arg_ofReal_of_nonneg hre]
  have hE := Real.exp_pos (-(Real.log ‖t‖ / 2))
  have key : (-(t * log t) - cexp (-(log t / 2)) + -(s * t)).re =
      -(t.re * Real.log ‖t‖) + t.im * arg t
        - Real.exp (-(Real.log ‖t‖ / 2)) * Real.cos (-(arg t / 2)) - (s.re * t.re - s.im * t.im) := by
    simp only [add_re, sub_re, neg_re, mul_re, exp_re, log_re, log_im, neg_im, div_ofNat_re,
      div_ofNat_im]
    ring
  rw [key]
  nlinarith [mul_le_mul_of_nonpos_left ha1 him]

private theorem G_eventuallyEq {t : ℂ} (ht : t ∈ slitPlane) :
    G =ᶠ[𝓝 t] fun u ↦ cexp (-(u * log u) - cexp (-(log u / 2))) := by
  filter_upwards [isOpen_ne.mem_nhds (slitPlane_ne_zero ht)] with u hu
  simp only [G, hu, ↓reduceIte]

private theorem differentiableAt_G {t : ℂ} (ht : t ∈ slitPlane) : DifferentiableAt ℂ G t := by
  refine DifferentiableAt.congr_of_eventuallyEq ?_ (G_eventuallyEq ht)
  have hl : DifferentiableAt ℂ log t := differentiableAt_id.clog ht
  fun_prop

private theorem exp_bound_aux (x σ : ℝ) (hx : 0 < x) :
    -(x * (Real.log x + σ)) ≤ Real.exp (1 - σ) - 2 * x := by
  have h1 := Real.add_one_le_exp (1 - σ - Real.log x)
  have h2 : Real.exp (1 - σ - Real.log x) * x = Real.exp (1 - σ) := by
    rw [Real.exp_sub, Real.exp_log hx, div_mul_cancel₀ _ hx.ne']
  nlinarith

private theorem norm_G_real_le (s : ℂ) {x : ℝ} (hx : 0 < x) :
    ‖G x * cexp (-(s * x))‖ ≤ Real.exp (Real.exp (1 - s.re)) * Real.exp (-2 * x) := by
  have h := norm_G_mul_exp_le (s := s) (t := (x : ℂ)) (by exact_mod_cast hx.ne')
    (by simp [hx.le]) (by simp)
  simp only [ofReal_re, ofReal_im, zero_mul, add_zero, norm_real, Real.norm_eq_abs,
    abs_of_pos hx] at h
  refine h.trans ?_
  rw [← Real.exp_add, Real.exp_le_exp]
  have := exp_bound_aux x s.re hx
  have := Real.exp_pos (-(Real.log x / 2))
  linarith

private theorem continuousOn_G_real (s : ℂ) :
    ContinuousOn (fun x : ℝ ↦ G x * cexp (-(s * x))) (Ioi 0) := by
  intro x hx
  apply ContinuousAt.continuousWithinAt
  have hG : ContinuousAt G (x : ℂ) :=
    (differentiableAt_G (ofReal_mem_slitPlane.mpr hx)).continuousAt
  have : ContinuousAt (fun x : ℝ ↦ G x) x := hG.comp continuous_ofReal.continuousAt
  fun_prop

private theorem integrableOn_G_real (s : ℂ) :
    IntegrableOn (fun x : ℝ ↦ G x * cexp (-(s * x))) (Ioi 0) := by
  refine Integrable.mono' ((exp_neg_integrableOn_Ioi 0 two_pos).const_mul
    (Real.exp (Real.exp (1 - s.re)))) ((continuousOn_G_real s).aestronglyMeasurable
    measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact norm_G_real_le s hx

/-- The Laplace transform `Φ(s) = ∫₀^∞ g(t) e^(-st) dt` of the counterexample. -/
private noncomputable def Φ (s : ℂ) : ℂ := ∫ x : ℝ in Ioi 0, G x * cexp (-(s * x))

private theorem differentiable_Φ : Differentiable ℂ Φ := by
  intro s₀
  have hmeas : ∀ s : ℂ, AEStronglyMeasurable (fun x : ℝ ↦ G x * cexp (-(s * x)))
      (volume.restrict (Ioi 0)) := fun s ↦
    (continuousOn_G_real s).aestronglyMeasurable measurableSet_Ioi
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := fun s (x : ℝ) ↦ G x * cexp (-(s * x)))
    (F' := fun s (x : ℝ) ↦ G x * (cexp (-(s * x)) * (-(x : ℂ))))
    (bound := fun x ↦ Real.exp (Real.exp (2 - s₀.re)) * Real.exp (-1 * x))
    (x₀ := s₀) (Metric.ball_mem_nhds s₀ one_pos) (Eventually.of_forall hmeas)
    (integrableOn_G_real s₀) ?_ ?_ ((exp_neg_integrableOn_Ioi 0 one_pos).const_mul _) ?_
  · exact key.2.differentiableAt
  · have : (fun x : ℝ ↦ G x * (cexp (-(s₀ * x)) * (-(x : ℂ)))) =
        fun x : ℝ ↦ (G x * cexp (-(s₀ * x))) * (-(x : ℂ)) := by ext; ring
    rw [this]
    exact (hmeas s₀).mul (by fun_prop : Continuous fun x : ℝ ↦ (-(x : ℂ))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x (hx : 0 < x) s hs
    have hsre : s₀.re - 1 ≤ s.re := by
      have := Complex.abs_re_le_norm (s - s₀)
      rw [Metric.mem_ball, dist_eq_norm] at hs
      simp only [sub_re] at this
      linarith [neg_abs_le (s.re - s₀.re)]
    have h := norm_G_real_le s hx
    calc ‖G x * (cexp (-(s * x)) * (-(x : ℂ)))‖ = ‖G x * cexp (-(s * x))‖ * x := by
          rw [← mul_assoc, norm_mul, norm_neg, norm_real, Real.norm_eq_abs, abs_of_pos hx]
      _ ≤ Real.exp (Real.exp (1 - s.re)) * Real.exp (-2 * x) * x := by gcongr
      _ ≤ Real.exp (Real.exp (2 - s₀.re)) * Real.exp (-1 * x) := by
          have e1 : Real.exp (Real.exp (1 - s.re)) ≤ Real.exp (Real.exp (2 - s₀.re)) :=
            Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by linarith))
          have e2 : Real.exp (-2 * x) * x ≤ Real.exp (-1 * x) := by
            have := Real.add_one_le_exp x
            have h3 : Real.exp (-2 * x) * Real.exp x = Real.exp (-1 * x) := by
              rw [← Real.exp_add]; ring_nf
            nlinarith [Real.exp_pos (-2 * x)]
          rw [mul_assoc]
          exact mul_le_mul e1 e2 (by positivity) (by positivity)
  · filter_upwards with x s _
    have : HasDerivAt (fun s : ℂ ↦ cexp (-(s * x))) (cexp (-(s * x)) * (-(x : ℂ))) s := by
      have := ((hasDerivAt_id s).mul_const (x : ℂ)).neg.cexp
      simpa using this
    exact this.const_mul _

private theorem mem_slitPlane_of_quadrant {t : ℂ} (h0 : t ≠ 0) (hre : 0 ≤ t.re) : t ∈ slitPlane := by
  rcases hre.lt_or_eq with h | h
  · exact Or.inl h
  · right; intro him; exact h0 (Complex.ext h.symm him)

private theorem tendsto_G_zero (s : ℂ) :
    Tendsto (fun t ↦ G t * cexp (-(s * t)))
      (𝓝[{t : ℂ | 0 ≤ t.re ∧ t.im ≤ 0} \ {0}] 0) (𝓝 0) := by
  set K := 3 + |s.re| + |s.im|
  have hb : Tendsto (fun t : ℂ ↦ Real.exp (K - Real.exp (-(Real.log ‖t‖ / 2)) / 2))
      (𝓝[≠] 0) (𝓝 0) := by
    have h1 : Tendsto (fun t : ℂ ↦ Real.log ‖t‖) (𝓝[≠] 0) atBot :=
      Real.tendsto_log_nhdsGT_zero.comp tendsto_norm_nhdsNE_zero
    have h2 : Tendsto (fun t : ℂ ↦ Real.exp (-(Real.log ‖t‖ / 2))) (𝓝[≠] 0) atTop :=
      Real.tendsto_exp_atTop.comp (tendsto_neg_atBot_atTop.comp (h1.atBot_div_const two_pos))
    have h3 : Tendsto (fun t : ℂ ↦ K - Real.exp (-(Real.log ‖t‖ / 2)) / 2) (𝓝[≠] 0) atBot := by
      have := tendsto_neg_atTop_atBot.comp (h2.atTop_div_const two_pos)
      simpa [sub_eq_add_neg] using tendsto_atBot_add_const_left _ K this
    exact Real.tendsto_exp_atBot.comp h3
  refine squeeze_zero_norm' ?_ (hb.mono_left (nhdsWithin_mono _ fun t ht ↦ ht.2))
  have hn : ∀ᶠ t in 𝓝[{t : ℂ | 0 ≤ t.re ∧ t.im ≤ 0} \ {0}] (0 : ℂ), t ∈ Metric.ball 0 1 :=
    nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) one_pos)
  filter_upwards [hn, self_mem_nhdsWithin] with t ht1 ⟨⟨hre, him⟩, h0⟩
  replace ht1 : ‖t‖ < 1 := mem_ball_zero_iff.mp ht1
  have h0 : t ≠ 0 := h0
  refine (norm_G_mul_exp_le h0 hre him).trans (Real.exp_le_exp.mpr ?_)
  have hpos : 0 < ‖t‖ := norm_pos_iff.mpr h0
  have hl : Real.log ‖t‖ ≤ 0 := Real.log_nonpos hpos.le ht1.le
  have hl2 := Real.one_sub_inv_le_log_of_pos hpos
  have hxl : -(‖t‖ * Real.log ‖t‖) ≤ 1 := by
    have : ‖t‖ * (1 - ‖t‖⁻¹) ≤ ‖t‖ * Real.log ‖t‖ := mul_le_mul_of_nonneg_left hl2 hpos.le
    rw [mul_sub, mul_inv_cancel₀ hpos.ne'] at this
    linarith
  have hre' : t.re ≤ ‖t‖ := (le_abs_self _).trans (abs_re_le_norm t)
  have him' : |t.im| ≤ ‖t‖ := abs_im_le_norm t
  have e1 : -(t.re * Real.log ‖t‖) ≤ 1 := by nlinarith
  have e2 : -(t.re * s.re) ≤ |s.re| := by
    have : |t.re * s.re| ≤ |s.re| := by
      rw [abs_mul]; nlinarith [abs_nonneg s.re, abs_of_nonneg hre]
    linarith [neg_abs_le (t.re * s.re)]
  have e3 : t.im * (s.im - Real.pi / 2) ≤ |s.im| + 2 := by
    have hpi := Real.pi_le_four
    have : |t.im * (s.im - Real.pi / 2)| ≤ |s.im| + 2 := by
      rw [abs_mul]
      have : |s.im - Real.pi / 2| ≤ |s.im| + 2 := by
        refine (abs_sub _ _).trans ?_
        rw [abs_of_pos (by positivity : (0:ℝ) < Real.pi / 2)]; linarith
      nlinarith [abs_nonneg (s.im - Real.pi / 2), abs_nonneg t.im]
    linarith [le_abs_self (t.im * (s.im - Real.pi / 2))]
  nlinarith

private theorem continuousOn_G_quadrant (s : ℂ) :
    ContinuousOn (fun t ↦ G t * cexp (-(s * t))) {t : ℂ | 0 ≤ t.re ∧ t.im ≤ 0} := by
  intro t ht
  by_cases h0 : t = 0
  · subst h0
    rw [← continuousWithinAt_sdiff_singleton]
    have : G 0 * cexp (-(s * 0)) = 0 := by simp [G]
    rw [ContinuousWithinAt, this]
    exact tendsto_G_zero s
  · apply ContinuousAt.continuousWithinAt
    have := (differentiableAt_G (mem_slitPlane_of_quadrant h0 ht.1)).continuousAt
    fun_prop

private theorem rect_identity (s : ℂ) {R : ℝ} (hR : 0 ≤ R) :
    (∫ x : ℝ in (0:ℝ)..R, G (x + (-R) * I) * cexp (-(s * (x + (-R) * I)))) -
      (∫ x : ℝ in (0:ℝ)..R, G x * cexp (-(s * x))) +
      I • (∫ y : ℝ in -R..0, G (R + y * I) * cexp (-(s * (R + y * I)))) -
      I • (∫ y : ℝ in -R..0, G (y * I) * cexp (-(s * (y * I)))) = 0 := by
  have h := integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
    (fun t ↦ G t * cexp (-(s * t))) (((-R : ℝ) : ℂ) * I) (R : ℂ) ?_ ?_
  · simpa using h
  · refine (continuousOn_G_quadrant s).mono ?_
    intro t ht
    rw [mem_reProdIm] at ht
    simp only [mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero,
      mul_im, add_zero, uIcc_of_le hR, uIcc_of_le (neg_nonpos.mpr hR),
      mem_Icc] at ht
    exact ⟨ht.1.1, ht.2.2⟩
  · intro t ht
    rw [mem_reProdIm] at ht
    simp only [mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero,
      min_eq_left hR, max_eq_right hR, mem_Ioo] at ht
    have hs : t ∈ slitPlane := Or.inl ht.1.1
    apply DifferentiableAt.differentiableWithinAt
    have := differentiableAt_G hs
    fun_prop

private theorem tendsto_mul_exp_neg {c : ℝ} (hc : 0 < c) :
    Tendsto (fun R : ℝ ↦ Real.exp (-(c * R)) * R) atTop (𝓝 0) := by
  have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
    (tendsto_id.const_mul_atTop hc)).const_mul c⁻¹
  rw [mul_zero] at h
  refine h.congr fun R ↦ ?_
  simp only [Function.comp_apply, id, pow_one]
  field_simp

private theorem norm_rot_le (s : ℂ) {τ : ℝ} (hτ : 0 < τ) :
    ‖G (((-τ : ℝ) : ℂ) * I) * cexp (-(s * (((-τ : ℝ) : ℂ) * I)))‖ ≤
      Real.exp (-τ * (s.im - Real.pi / 2) - Real.exp (-(Real.log τ / 2)) / 2) := by
  have h0 : (((-τ : ℝ) : ℂ) * I) ≠ 0 := by
    simp [hτ.ne']
  have h := norm_G_mul_exp_le (s := s) h0 (by simp) (by simp [hτ.le])
  have hn : ‖(((-τ : ℝ) : ℂ) * I)‖ = τ := by
    simp [abs_of_pos hτ]
  simp only [hn, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero,
    mul_im, add_zero, zero_mul, neg_zero, zero_add] at h
  simpa using h

private theorem integrableOn_rot (s : ℂ) (hs : Real.pi / 2 < s.im) :
    IntegrableOn (fun τ : ℝ ↦ G (((-τ : ℝ) : ℂ) * I) * cexp (-(s * (((-τ : ℝ) : ℂ) * I))))
      (Ioi 0) := by
  have hc : 0 < s.im - Real.pi / 2 := by linarith
  refine Integrable.mono' (exp_neg_integrableOn_Ioi 0 hc) ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine (continuousOn_G_quadrant s).comp (by fun_prop) ?_
    intro τ hτ
    simp only [mem_ofPred_eq, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_zero, mul_im, add_zero, le_refl, true_and]
    exact neg_nonpos.mpr (le_of_lt hτ)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
    refine (norm_rot_le s hτ).trans (Real.exp_le_exp.mpr ?_)
    have := Real.exp_pos (-(Real.log τ / 2))
    nlinarith

private theorem Φ_rotate {s : ℂ} (hs : Real.pi / 2 < s.im) :
    Φ s = -I * ∫ τ : ℝ in Ioi 0, G (((-τ : ℝ) : ℂ) * I) * cexp (-(s * (((-τ : ℝ) : ℂ) * I))) := by
  set c := s.im - Real.pi / 2 with hc_def
  have hc : 0 < c := by linarith
  set J := ∫ τ : ℝ in Ioi 0, G (((-τ : ℝ) : ℂ) * I) * cexp (-(s * (((-τ : ℝ) : ℂ) * I)))
  have hA := intervalIntegral_tendsto_integral_Ioi 0 (integrableOn_G_real s) tendsto_id
  have hB := intervalIntegral_tendsto_integral_Ioi 0 (integrableOn_rot s hs) tendsto_id
  have hE1 : Tendsto (fun R : ℝ ↦ ∫ x : ℝ in (0:ℝ)..R,
      G (x + (-R) * I) * cexp (-(s * (x + (-R) * I)))) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_mul_exp_neg hc)
    filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop (Real.exp (1 - s.re))]
      with R hR1 hR2
    have hR0 : (0 : ℝ) ≤ R := by linarith
    refine (intervalIntegral.norm_integral_le_of_norm_le_const ?_).trans_eq
      (by rw [sub_zero, abs_of_nonneg hR0])
    intro x hx
    rw [uIoc_of_le hR0] at hx
    set t : ℂ := x + (-R) * I
    have hre : t.re = x := by simp [t]
    have him : t.im = -R := by simp [t]
    have h0 : t ≠ 0 := fun h ↦ by
      have := congrArg Complex.im h; rw [him] at this; simp at this; linarith
    have hn : R ≤ ‖t‖ := by
      have := abs_im_le_norm t; rw [him, abs_neg, abs_of_nonneg hR0] at this; exact this
    have hlog : 1 - s.re ≤ Real.log ‖t‖ := by
      rw [← Real.log_exp (1 - s.re)]
      exact Real.log_le_log (Real.exp_pos _) (hR2.trans hn)
    refine (norm_G_mul_exp_le h0 (by rw [hre]; exact hx.1.le) (by rw [him]; linarith)).trans
      (Real.exp_le_exp.mpr ?_)
    rw [hre, him]
    have := Real.exp_pos (-(Real.log ‖t‖ / 2))
    have : 0 ≤ x * (Real.log ‖t‖ + s.re) := mul_nonneg hx.1.le (by linarith)
    nlinarith
  have hE2 : Tendsto (fun R : ℝ ↦ ∫ y : ℝ in -R..0,
      G (R + y * I) * cexp (-(s * (R + y * I)))) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_mul_exp_neg one_pos)
    filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop (Real.exp (1 - s.re))]
      with R hR1 hR2
    have hR0 : (0 : ℝ) ≤ R := by linarith
    refine (intervalIntegral.norm_integral_le_of_norm_le_const ?_).trans_eq
      (by rw [zero_sub, neg_neg, abs_of_nonneg hR0])
    intro y hy
    rw [uIoc_of_le (by linarith)] at hy
    set t : ℂ := R + y * I
    have hre : t.re = R := by simp [t]
    have him : t.im = y := by simp [t]
    have h0 : t ≠ 0 := fun h ↦ by
      have := congrArg Complex.re h; rw [hre] at this; simp at this; linarith
    have hn : R ≤ ‖t‖ := by
      have := abs_re_le_norm t; rw [hre, abs_of_nonneg hR0] at this; exact this
    have hlog : 1 - s.re ≤ Real.log ‖t‖ := by
      rw [← Real.log_exp (1 - s.re)]
      exact Real.log_le_log (Real.exp_pos _) (hR2.trans hn)
    refine (norm_G_mul_exp_le h0 (by rw [hre]; exact hR0) (by rw [him]; exact hy.2)).trans
      (Real.exp_le_exp.mpr ?_)
    rw [hre, him]
    have := Real.exp_pos (-(Real.log ‖t‖ / 2))
    have : y * (s.im - Real.pi / 2) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hy.2 hc.le
    have : R * 1 ≤ R * (Real.log ‖t‖ + s.re) := mul_le_mul_of_nonneg_left (by linarith) hR0
    nlinarith
  have hBeq : ∀ R : ℝ, (∫ y : ℝ in -R..0, G (y * I) * cexp (-(s * (y * I)))) =
      ∫ τ : ℝ in (0:ℝ)..R, G (((-τ : ℝ) : ℂ) * I) * cexp (-(s * (((-τ : ℝ) : ℂ) * I))) := by
    intro R
    rw [intervalIntegral.integral_comp_neg (fun y : ℝ ↦ G (y * I) * cexp (-(s * (y * I))))]
    simp
  have hlim := ((hE1.add (hE2.const_smul I)).sub (hB.const_smul I))
  simp only [smul_zero, zero_add, zero_sub, id] at hlim hA
  refine tendsto_nhds_unique hA (hlim.congr' ?_) |>.trans (by rw [smul_eq_mul, neg_mul])
  filter_upwards [eventually_ge_atTop 0] with R hR
  have h := rect_identity s hR
  rw [← hBeq R]
  linear_combination h

private theorem exp_neg_le_pow (N : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    Real.exp (-(Real.exp (-(Real.log τ / 2)) / 2)) ≤
      ((2 * N).factorial * 4 ^ N : ℝ) * τ ^ N := by
  set u := Real.exp (-(Real.log τ / 2)) / 2
  have hu : 0 ≤ u := by positivity
  have h1 := Real.pow_div_factorial_le_exp (x := u) hu (2 * N)
  have hE : u ^ (2 * N) = ((τ ^ N)⁻¹) / 4 ^ N := by
    simp only [u, div_pow, ← Real.exp_nat_mul]
    have : ((2 * N : ℕ) : ℝ) * -(Real.log τ / 2) = -(N * Real.log τ) := by push_cast; ring
    rw [this, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hτ, pow_mul]
    norm_num
  rw [Real.exp_neg]
  rw [hE] at h1
  have hpos : 0 < ((2 * N).factorial * 4 ^ N : ℝ) * τ ^ N := by positivity
  rw [inv_le_comm₀ (Real.exp_pos u) hpos]
  refine le_trans (le_of_eq ?_) h1
  have : (0:ℝ) < τ ^ N := by positivity
  have : (0:ℝ) < (2 * N).factorial := by positivity
  field_simp

private theorem integral_pow_exp (N : ℕ) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun τ : ℝ ↦ τ ^ N * Real.exp (-(c * τ))) (Ioi 0) ∧
      ∫ τ : ℝ in Ioi 0, τ ^ N * Real.exp (-(c * τ)) = N.factorial / c ^ (N + 1) := by
  constructor
  · have := integrableOn_rpow_mul_exp_neg_mul_rpow (s := N) (p := 1) (b := c)
      (by have := N.cast_nonneg (α := ℝ); linarith) one_pos hc
    refine this.congr_fun (fun τ hτ ↦ ?_) measurableSet_Ioi
    simp [Real.rpow_natCast]
  · have := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := N + 1) (r := c) (by positivity) hc
    simp only [add_sub_cancel_right, Real.rpow_natCast] at this
    rw [this, Real.Gamma_nat_eq_factorial,
      show ((N : ℝ) + 1) = ((N + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    rw [one_div, inv_pow]
    field_simp

private theorem norm_Φ_le_upper (N : ℕ) {s : ℂ} (hs : Real.pi ≤ s.im) :
    ‖Φ s‖ ≤ ((2 * N).factorial * 4 ^ N * N.factorial * 2 ^ (N + 1) : ℝ) / s.im ^ N := by
  have hpi0 := Real.pi_pos
  have hpi3 := Real.two_le_pi
  have hpi : Real.pi / 2 < s.im := by linarith
  rw [Φ_rotate hpi, norm_mul, norm_neg, norm_I, one_mul]
  set c := s.im - Real.pi / 2 with hc_def
  have hc : 0 < c := by linarith
  have hc2 : s.im ≤ 2 * c := by linarith
  set M : ℝ := (2 * N).factorial * 4 ^ N
  obtain ⟨hint, hval⟩ := integral_pow_exp N hc
  refine (norm_integral_le_of_norm_le (hint.const_mul M) ?_).trans ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
    refine (norm_rot_le s hτ).trans ?_
    rw [sub_eq_add_neg, Real.exp_add, show -τ * (s.im - Real.pi / 2) = -(c * τ) by ring]
    have := exp_neg_le_pow N hτ
    have := Real.exp_pos (-(c * τ))
    calc Real.exp (-(c * τ)) * Real.exp (-(Real.exp (-(Real.log τ / 2)) / 2))
        ≤ Real.exp (-(c * τ)) * (M * τ ^ N) := by gcongr
      _ = M * (τ ^ N * Real.exp (-(c * τ))) := by ring
  · rw [integral_const_mul, hval]
    have hs1 : 1 ≤ s.im := by linarith
    have hsN : 0 < s.im ^ N := by positivity
    have key : s.im ^ N ≤ 2 ^ (N + 1) * c ^ (N + 1) := by
      calc s.im ^ N ≤ s.im ^ (N + 1) := pow_le_pow_right₀ hs1 (Nat.le_succ N)
        _ ≤ (2 * c) ^ (N + 1) := pow_le_pow_left₀ (by linarith) hc2 _
        _ = 2 ^ (N + 1) * c ^ (N + 1) := by rw [mul_pow]
    have hM : 0 ≤ M := by positivity
    have hcN : 0 < c ^ (N + 1) := by positivity
    rw [mul_div_assoc', div_le_div_iff₀ hcN hsN]
    have hf : (0:ℝ) ≤ N.factorial := by positivity
    calc M * N.factorial * s.im ^ N ≤ M * N.factorial * (2 ^ (N + 1) * c ^ (N + 1)) := by
          gcongr
      _ = _ := by ring

private theorem G_ofReal {x : ℝ} (hx : 0 < x) :
    G x = ((Real.exp (-(x * Real.log x) - Real.exp (-(Real.log x / 2))) : ℝ) : ℂ) := by
  simp only [G, ofReal_eq_zero, hx.ne', ↓reduceIte]
  rw [← ofReal_log hx.le]
  push_cast
  rfl

private theorem Φ_conj (s : ℂ) : Φ ((starRingEnd ℂ) s) = (starRingEnd ℂ) (Φ s) := by
  unfold Φ
  rw [← integral_conj]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
  simp only [G_ofReal hx, map_mul, conj_ofReal, ← exp_conj, map_neg]

private theorem norm_Φ_le (N : ℕ) (σ y : ℝ) (hy : Real.pi ≤ |y|) :
    ‖Φ ((σ : ℂ) + (y : ℂ) * I)‖ ≤
      ((2 * N).factorial * 4 ^ N * N.factorial * 2 ^ (N + 1) : ℝ) / |y| ^ N := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h] at hy ⊢
    have := norm_Φ_le_upper N (s := (σ : ℂ) + (y : ℂ) * I) (by simpa using hy)
    simpa using this
  · rw [abs_of_neg h] at hy ⊢
    have := norm_Φ_le_upper N (s := (σ : ℂ) + ((-y : ℝ) : ℂ) * I) (by simpa using hy)
    have e : (σ : ℂ) + (y : ℂ) * I = (starRingEnd ℂ) ((σ : ℂ) + ((-y : ℝ) : ℂ) * I) := by
      apply Complex.ext <;> simp
    rw [e, Φ_conj, norm_conj]
    simpa using this

private theorem schwartz_Φ (b : ℝ) : SchwartzOnLeftHalfPlane Φ b := by
  refine ⟨differentiable_Φ.differentiableOn, fun ε _ N _ ↦ ?_⟩
  refine ⟨((2 * N).factorial * 4 ^ N * N.factorial * 2 ^ (N + 1) : ℝ), by positivity, ?_⟩
  have : ∀ᶠ y : ℝ in comap abs atTop, Real.pi ≤ |y| :=
    tendsto_comap.eventually (eventually_ge_atTop Real.pi)
  filter_upwards [this] with y hy σ _
  exact norm_Φ_le N σ y hy

private theorem integrableOn_kernel (y : ℝ) :
    IntegrableOn (fun w : ℝ ↦ (w : ℂ) * cexp (-(w : ℂ)) * cexp ((y : ℂ) * w * I)) (Ioi 0) := by
  have h := (integral_pow_exp 1 one_pos).1
  refine Integrable.mono' h (by fun_prop : Continuous fun w : ℝ ↦
    (w : ℂ) * cexp (-(w : ℂ)) * cexp ((y : ℂ) * w * I)).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with w (hw : 0 < w)
  rw [norm_mul, norm_mul, norm_exp, norm_exp, norm_real, Real.norm_eq_abs, abs_of_pos hw]
  simp

private theorem kernel_eq (y : ℝ) :
    ∫ w : ℝ in Ioi 0, (w : ℂ) * cexp (-(w : ℂ)) * cexp ((y : ℂ) * w * I) =
      1 / ((y : ℂ) * I - 1) ^ 2 := by
  set a : ℂ := 1 - (y : ℂ) * I with ha
  have ha0 : a ≠ 0 := fun h ↦ by
    have := congrArg Complex.re h; simp [a] at this
  have hare : a.re = 1 := by simp [a]
  set F : ℝ → ℂ := fun w ↦ -((w : ℂ) / a + 1 / a ^ 2) * cexp (-(a * w))
  have hint : ∀ w : ℝ, (w : ℂ) * cexp (-(w : ℂ)) * cexp ((y : ℂ) * w * I) =
      (w : ℂ) * cexp (-(a * w)) := by
    intro w
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    simp only [a]; ring
  simp_rw [hint]
  have hderiv : ∀ w ∈ Ioi (0 : ℝ), HasDerivAt F ((w : ℂ) * cexp (-(a * w))) w := by
    intro w _
    have h1 : HasDerivAt (fun w : ℝ ↦ (w : ℂ)) 1 w := ofRealCLM.hasDerivAt
    have h2 : HasDerivAt (fun w : ℝ ↦ cexp (-(a * w))) (cexp (-(a * w)) * (-(a * 1))) w :=
      ((h1.const_mul a).neg).cexp
    have h3 := ((h1.div_const a).add_const (1 / a ^ 2)).neg.mul h2
    convert h3 using 1
    simp only [Pi.neg_apply]
    field_simp
    ring
  have hlim : Tendsto F atTop (𝓝 0) := by
    have h1 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    have h0 := Real.tendsto_exp_neg_atTop_nhds_zero
    have hsum := (h1.add h0)
    rw [add_zero] at hsum
    refine squeeze_zero_norm' ?_ hsum
    filter_upwards [eventually_ge_atTop 0] with w hw
    have hna : 1 ≤ ‖a‖ := by
      have := abs_re_le_norm a; rw [hare, abs_one] at this; exact this
    simp only [F, norm_mul, norm_neg, norm_exp, pow_one]
    have hre : (-(a * (w : ℂ))).re = -w := by simp [hare]
    rw [hre]
    have : ‖(w : ℂ) / a + 1 / a ^ 2‖ ≤ w + 1 := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_div, norm_div, norm_real, Real.norm_eq_abs, abs_of_nonneg hw, norm_one,
        norm_pow]
      have h1 : w / ‖a‖ ≤ w := div_le_self hw hna
      have h2 : 1 / ‖a‖ ^ 2 ≤ 1 := by
        rw [div_le_one (by positivity)]; nlinarith
      linarith
    have := Real.exp_pos (-w)
    nlinarith
  have hc : ContinuousWithinAt F (Ici 0) 0 := by
    apply Continuous.continuousWithinAt; fun_prop
  have hI := integral_Ioi_of_hasDerivAt_of_tendsto hc hderiv ?_ hlim
  · rw [hI]
    simp only [F, ofReal_zero, zero_div, zero_add, mul_zero, neg_zero, Complex.exp_zero, mul_one,
      zero_sub, neg_neg]
    rw [show (y : ℂ) * I - 1 = -a by simp [a]]
    rw [neg_sq]
  · exact (integrableOn_kernel y).congr_fun (fun w _ ↦ hint w) measurableSet_Ioi

private theorem continuous_Φ_axis : Continuous fun y : ℝ ↦ Φ ((y : ℂ) * I) :=
  differentiable_Φ.continuous.comp (by fun_prop)

private theorem integrable_Φ_axis : Integrable (fun y : ℝ ↦ Φ ((y : ℂ) * I)) := by
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := -Real.pi) (b := Real.pi)).exists_bound_of_continuousOn
    continuous_Φ_axis.continuousOn
  set C : ℝ := ((2 * 2).factorial * 4 ^ 2 * (2 : ℕ).factorial * 2 ^ (2 + 1) : ℝ)
  have hC : 0 ≤ C := by positivity
  set K : ℝ := |B| * (1 + Real.pi ^ 2) + 2 * C
  refine (integrable_inv_one_add_sq.const_mul K).mono' continuous_Φ_axis.aestronglyMeasurable
    (ae_of_all _ fun y ↦ ?_)
  have hy2 : 0 < 1 + y ^ 2 := by positivity
  rcases le_or_gt |y| Real.pi with h | h
  · have h1 := hB y (abs_le.mp h)
    have hyπ : y ^ 2 ≤ Real.pi ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
    have : |B| ≤ |B| * (1 + Real.pi ^ 2) * (1 + y ^ 2)⁻¹ := by
      have hq : 1 ≤ (1 + Real.pi ^ 2) * (1 + y ^ 2)⁻¹ := by
        rw [le_mul_inv_iff₀ hy2]; linarith
      rw [mul_assoc]
      exact le_mul_of_one_le_right (abs_nonneg B) hq
    calc ‖Φ ((y : ℂ) * I)‖ ≤ |B| := h1.trans (le_abs_self B)
      _ ≤ |B| * (1 + Real.pi ^ 2) * (1 + y ^ 2)⁻¹ := this
      _ ≤ K * (1 + y ^ 2)⁻¹ := by gcongr; simp only [K]; linarith
  · have h1 := norm_Φ_le 2 0 y h.le
    simp only [ofReal_zero, zero_add] at h1
    have hpi := Real.two_le_pi
    have hyy : 1 ≤ y ^ 2 := by
      rw [← sq_abs]; nlinarith
    calc ‖Φ ((y : ℂ) * I)‖ ≤ C / |y| ^ 2 := h1
      _ = C / y ^ 2 := by rw [sq_abs]
      _ ≤ 2 * C * (1 + y ^ 2)⁻¹ := by
          rw [div_le_iff₀ (by positivity)]
          have h3 : 1 / 2 ≤ (1 + y ^ 2)⁻¹ * y ^ 2 := by
            rw [inv_mul_eq_div, le_div_iff₀ hy2]; linarith
          nlinarith
      _ ≤ K * (1 + y ^ 2)⁻¹ := by gcongr; simp only [K]; nlinarith [abs_nonneg B, Real.pi_pos]

/-- `g` on the real line, extended by zero to `t ≤ 0`. -/
private noncomputable def gext : ℝ → ℂ := Set.indicator (Ioi 0) (fun x : ℝ ↦ G x)

private theorem integrable_gext : Integrable gext := by
  have := integrableOn_G_real 0
  simp only [zero_mul, neg_zero, Complex.exp_zero, mul_one] at this
  exact (integrable_indicator_iff measurableSet_Ioi).mpr this

private theorem fourier_gext (ξ : ℝ) : 𝓕 gext ξ = Φ (((2 * Real.pi * ξ : ℝ) : ℂ) * I) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have : (fun v : ℝ ↦ cexp (↑(-2 * Real.pi * v * ξ) * I) • gext v) = (Ioi 0).indicator
      (fun v : ℝ ↦ G v * cexp (-((((2 * Real.pi * ξ : ℝ) : ℂ) * I) * v))) := by
    ext v
    by_cases hv : v ∈ Ioi (0:ℝ)
    · simp only [gext, indicator_of_mem hv, smul_eq_mul]
      rw [mul_comm]; congr 2; push_cast; ring
    · simp [gext, indicator_of_notMem hv]
  rw [this, integral_indicator measurableSet_Ioi]
  rfl

private theorem axis_integral_eq (w : ℝ) (hw : 0 < w) :
    ∫ y : ℝ, Φ ((y : ℂ) * I) * cexp ((y : ℂ) * w * I) = 2 * Real.pi * G w := by
  have hint : Integrable (𝓕 gext) := by
    have := integrable_Φ_axis.comp_mul_left' (R := 2 * Real.pi) (by positivity)
    refine this.congr (ae_of_all _ fun ξ ↦ ?_)
    simp only [fourier_gext]
  have hc : ContinuousAt gext w := by
    have hG : ContinuousAt (fun x : ℝ ↦ G x) w :=
      (differentiableAt_G (ofReal_mem_slitPlane.mpr hw)).continuousAt.comp
        continuous_ofReal.continuousAt
    refine hG.congr ?_
    filter_upwards [Ioi_mem_nhds hw] with x hx
    simp [gext, indicator_of_mem hx]
  have hinv := integrable_gext.fourierInv_fourier_eq hint hc
  rw [Real.fourierInv_eq'] at hinv
  simp only [fourier_gext, smul_eq_mul] at hinv
  rw [show gext w = G w by simp [gext, indicator_of_mem (show w ∈ Ioi (0:ℝ) from hw)]] at hinv
  have hcv := Measure.integral_comp_mul_left (fun y : ℝ ↦ Φ ((y : ℂ) * I) * cexp ((y : ℂ) * w * I))
    (2 * Real.pi)
  have hpi := Real.pi_pos
  rw [abs_inv, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)] at hcv
  have e : (∫ x : ℝ, Φ (((2 * Real.pi * x : ℝ) : ℂ) * I) * cexp (((2 * Real.pi * x : ℝ) : ℂ) * w * I))
      = G w := by
    rw [← hinv]
    refine integral_congr_ae (ae_of_all _ fun v ↦ ?_)
    rw [mul_comm]
    simp only [RCLike.inner_apply, conj_trivial]
    push_cast
    ring
  rw [e] at hcv
  have hne : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  rw [hcv, Complex.real_smul, ← mul_assoc]
  have hpiC : (2 * (Real.pi : ℂ)) ≠ 0 := by exact_mod_cast hne
  push_cast
  rw [mul_inv_cancel₀ hpiC, one_mul]

private theorem real_integral_pos :
    0 < ∫ w : ℝ in Ioi 0, 2 * Real.pi * w * Real.exp (-w) *
      Real.exp (-(w * Real.log w) - Real.exp (-(Real.log w / 2))) := by
  have hpi := Real.pi_pos
  have hint : IntegrableOn (fun w : ℝ ↦ 2 * Real.pi * w * Real.exp (-w) *
      Real.exp (-(w * Real.log w) - Real.exp (-(Real.log w / 2)))) (Ioi 0) := by
    refine Integrable.mono' (((integral_pow_exp 1 one_pos).1).const_mul
      (2 * Real.pi * Real.exp (Real.exp 1))) (by fun_prop : Measurable fun w : ℝ ↦
        2 * Real.pi * w * Real.exp (-w) *
          Real.exp (-(w * Real.log w) - Real.exp (-(Real.log w / 2)))).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with w (hw : 0 < w)
    have h := norm_G_real_le 0 hw
    simp only [zero_mul, neg_zero, Complex.exp_zero, mul_one, G_ofReal hw, norm_real,
      Real.norm_eq_abs, zero_re, sub_zero] at h
    rw [abs_of_pos (Real.exp_pos _)] at h
    have h2 : Real.exp (-(w * Real.log w) - Real.exp (-(Real.log w / 2))) ≤
        Real.exp (Real.exp 1) := by
      refine h.trans ?_
      have : Real.exp (-2 * w) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      nlinarith [Real.exp_pos (Real.exp 1)]
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    simp only [pow_one, one_mul]
    have : 0 < 2 * Real.pi * w * Real.exp (-w) := by positivity
    nlinarith
  rw [setIntegral_pos_iff_support_of_nonneg_ae _ hint]
  · have : Function.support (fun w : ℝ ↦ 2 * Real.pi * w * Real.exp (-w) *
        Real.exp (-(w * Real.log w) - Real.exp (-(Real.log w / 2)))) ∩ Ioi 0 = Ioi 0 := by
      ext w
      simp only [mem_inter_iff, Function.mem_support, mem_Ioi, and_iff_right_iff_imp]
      intro hw
      positivity
    rw [this, Real.volume_Ioi]
    simp
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with w (hw : 0 < w)
    positivity

private theorem cauchy_ne_zero : verticalLineIntegral (fun s ↦ Φ s / (s - 1) ^ 2) 0 ≠ 0 := by
  have hk : Integrable (fun w : ℝ ↦ (w : ℂ) * cexp (-(w : ℂ))) (volume.restrict (Ioi 0)) := by
    have := integrableOn_kernel 0
    simp only [ofReal_zero, zero_mul, Complex.exp_zero, mul_one] at this
    exact this
  have hF : Integrable (Function.uncurry fun (y w : ℝ) ↦ Φ ((y : ℂ) * I) *
      ((w : ℂ) * cexp (-(w : ℂ)) * cexp ((y : ℂ) * w * I)))
      (volume.prod (volume.restrict (Ioi 0))) := by
    refine (integrable_Φ_axis.norm.mul_prod hk.norm).mono' ?_ (ae_of_all _ fun z ↦ ?_)
    · have hc : Continuous (fun z : ℝ × ℝ ↦ Φ ((z.1 : ℂ) * I) *
          ((z.2 : ℂ) * cexp (-(z.2 : ℂ)) * cexp ((z.1 : ℂ) * z.2 * I))) :=
        (continuous_Φ_axis.comp continuous_fst).mul (by fun_prop)
      exact hc.aestronglyMeasurable
    · have h1 : ‖cexp ((z.1 : ℂ) * z.2 * I)‖ = 1 := by
        rw [show ((z.1 : ℂ) * z.2 * I) = ((z.1 * z.2 : ℝ) : ℂ) * I by push_cast; ring]
        exact norm_exp_ofReal_mul_I _
      simp only [Function.uncurry, norm_mul, h1, mul_one]
      rfl
  have step1 : ∫ y : ℝ, Φ ((y : ℂ) * I) / ((y : ℂ) * I - 1) ^ 2 =
      ∫ y : ℝ, ∫ w : ℝ in Ioi 0, Φ ((y : ℂ) * I) *
        ((w : ℂ) * cexp (-(w : ℂ)) * cexp ((y : ℂ) * w * I)) := by
    refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
    simp only
    rw [integral_const_mul, kernel_eq, div_eq_mul_one_div]
  have step2 := integral_integral_swap hF
  have step3 : ∫ w : ℝ in Ioi 0, ∫ y : ℝ, Φ ((y : ℂ) * I) *
        ((w : ℂ) * cexp (-(w : ℂ)) * cexp ((y : ℂ) * w * I)) =
      ∫ w : ℝ in Ioi 0, ((2 * Real.pi * w * Real.exp (-w) *
        Real.exp (-(w * Real.log w) - Real.exp (-(Real.log w / 2))) : ℝ) : ℂ) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun w hw ↦ ?_
    have : ∀ y : ℝ, Φ ((y : ℂ) * I) * ((w : ℂ) * cexp (-(w : ℂ)) * cexp ((y : ℂ) * w * I)) =
        ((w : ℂ) * cexp (-(w : ℂ))) * (Φ ((y : ℂ) * I) * cexp ((y : ℂ) * w * I)) :=
      fun y ↦ by ring
    simp only [this]
    rw [integral_const_mul, axis_integral_eq w hw, G_ofReal hw]
    push_cast
    ring
  unfold verticalLineIntegral
  simp only [ofReal_zero, zero_add]
  rw [step1, step2, step3, integral_complex_ofReal]
  refine mul_ne_zero I_ne_zero ?_
  exact_mod_cast real_integral_pos.ne'

end AsymptoticCauchyCounterexample

/-- Paper: Theorem B.2.2.4(2), p. 602. On `t > 0` set
`g(t) = exp(-t log t - t^(-1/2))` and let `Φ(s) = ∫₀^∞ g(t) exp(-s t) dt`.
This transform is entire. For large positive or negative imaginary part, rotate the
integration ray to the opposite imaginary half-axis to obtain rapid decay uniformly
in the real part. Take `b = ε = 2` and `N = 0`. On the imaginary axis, Fourier
inversion gives zero for the Cauchy integral at `z = -1`, where `Φ(-1) > 0`, and
gives `-Φ(1) ≠ 0` at `z = 1`. -/
theorem Printed.asymptoticCauchy_leftHalfPlane_false :
    ¬ Printed.asymptoticCauchy_leftHalfPlane := by
  intro h
  have := (h 1 AsymptoticCauchyCounterexample.Φ (AsymptoticCauchyCounterexample.schwartz_Φ 1)
    1 one_pos 1 1).2 (by norm_num)
  norm_num at this
  exact AsymptoticCauchyCounterexample.cauchy_ne_zero this

end RiemannMasullo
