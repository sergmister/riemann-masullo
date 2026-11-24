module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! # The interval Paley–Wiener theorem

The converse uses exponential damping of the real trace. Rotation of the two
half-line Laplace integrals to the imaginary axis gives cancellation outside
the interval of exponential type. Plancherel convergence then gives the same
support bound for the square-integrable Fourier transform.
-/

open MeasureTheory Set Filter Complex Topology
open scoped FourierTransform ENNReal SchwartzMap

@[expose] public noncomputable section

namespace RiemannMasullo

private def halfLaplace (g : ℝ → ℂ) (s : ℂ) := ∫ t in Ioi (0 : ℝ), g t * exp (-s * t)

/-- Absolute convergence rates on the positive ray. -/
private def LaplaceRates (g : ℝ → ℂ) (a : ℝ) :=
  ∀ c : ℝ, a < c → IntegrableOn (fun t ↦ ‖g t‖ * Real.exp (-c * t)) (Ioi 0)

private theorem laplace_norm (g : ℝ → ℂ) (s : ℂ) (t : ℝ) :
    ‖g t * exp (-s * t)‖ = ‖g t‖ * Real.exp (-s.re * t) := by
  simp [norm_exp]

private theorem laplace_integrable {g : ℝ → ℂ} (hg : Continuous g) {a : ℝ}
    (hr : LaplaceRates g a) {s : ℂ} (hs : a < s.re) :
    IntegrableOn (fun t : ℝ ↦ g t * exp (-s * t)) (Ioi 0) := by
  apply (hr _ hs).mono' (by fun_prop)
  exact ae_of_all _ fun x ↦ (laplace_norm _ _ _).le

private theorem halfLaplace_diff {g : ℝ → ℂ} (hg : Continuous g) {a : ℝ}
    (hr : LaplaceRates g a) {s : ℂ} (hs : a < s.re) :
    DifferentiableAt ℂ (halfLaplace g) s := by
  obtain ⟨b, hab, hbs⟩ := exists_between hs
  obtain ⟨c, hbc, hcs⟩ := exists_between hbs
  let d := c - b
  have hd : 0 < d := sub_pos.mpr hbc
  let bound (t : ℝ) := d⁻¹ * (‖g t‖ * Real.exp (-b * t))
  have hdiff (t : ℝ) (z : ℂ) : HasDerivAt (fun w : ℂ ↦ g t * exp (-w * t))
      (g t * exp (-z * t) * (-t)) z := by
    convert (((hasDerivAt_id z).neg.mul_const (t : ℂ)).cexp.const_mul (g t)) using 1 <;> simp [mul_comm, mul_left_comm]
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := bound)
    (μ := volume.restrict (Ioi (0 : ℝ))) (F := fun z (t : ℝ) ↦ g t * exp (-z * t))
    (s := {z : ℂ | c < z.re}) (isOpen_lt continuous_const continuous_re |>.mem_nhds hcs)
    (Eventually.of_forall fun z ↦ by fun_prop) (laplace_integrable hg hr hs)
    (F' := fun z (t : ℝ) ↦ g t * exp (-z * t) * (-t)) (by fun_prop) ?_
    ((hr _ hab).const_mul _) (ae_of_all _ fun t z _ ↦ hdiff t z)).2.differentiableAt
  filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioi] with t ht
  intro z hz
  change c < z.re at hz
  change 0 < t at ht
  rw [norm_mul, laplace_norm, norm_neg, norm_real, Real.norm_of_nonneg ht.le]
  have htexp : t ≤ d⁻¹ * Real.exp (d * t) := by
    rw [← div_eq_inv_mul, le_div_iff₀ hd]
    linarith [Real.add_one_le_exp (d * t), mul_comm t d]
  calc
    _ ≤ ‖g t‖ * Real.exp (-z.re * t) * (d⁻¹ * Real.exp (d * t)) := by gcongr
    _ = d⁻¹ * (‖g t‖ * Real.exp ((-z.re + d) * t)) := by rw [add_mul, Real.exp_add]; ring
    _ ≤ bound t := by
      dsimp only [bound, d]
      gcongr
      linarith

private theorem laplaceRates_l2 {g : ℝ → ℂ} (hg : MemLp g 2 (volume.restrict (Ioi 0))) :
    LaplaceRates g 0 := by
  intro c hc
  have he : MemLp (fun t : ℝ ↦ Real.exp (-c * t)) 2 (volume.restrict (Ioi 0)) := by
    apply (memLp_two_iff_integrable_sq (by fun_prop)).2
    simp_rw [← Real.exp_nat_mul]
    simp only [Nat.cast_ofNat]
    have he (x : ℝ) : 2 * (-c * x) = (-2 * c) * x := by ring
    simp_rw [he]
    exact integrableOn_exp_mul_Ioi (by linarith) 0
  exact hg.norm.integrable_mul he

private theorem laplaceRates_growth {g : ℝ → ℂ} (hg : Continuous g) {A C : ℝ}
    (hb : ∀ t : ℝ, 0 < t → ‖g t‖ ≤ C * Real.exp (A * t)) : LaplaceRates g A := by
  intro c hc
  apply ((integrableOn_exp_mul_Ioi (sub_neg.mpr hc) 0).const_mul C).mono' (by fun_prop)
  filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioi] with t ht
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)]
  calc
    _ ≤ C * Real.exp (A * t) * Real.exp (-c * t) := by gcongr; exact hb t ht
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring

/-- The positive half-line Laplace transform of a continuous function that grows at
most like `exp (a * t)` is holomorphic on the open half-plane `a < Re s`. -/
theorem differentiableAt_halfLaplace_of_exp_bound {g : ℝ → ℂ} (hg : Continuous g)
    {a C : ℝ} (hb : ∀ t : ℝ, 0 < t → ‖g t‖ ≤ C * Real.exp (a * t))
    {s : ℂ} (hs : a < s.re) :
    DifferentiableAt ℂ (fun z : ℂ ↦ ∫ t in Ioi (0 : ℝ), g t * exp (-z * t)) s :=
  halfLaplace_diff hg (laplaceRates_growth hg hb) hs

/-- In the first quadrant, exponential decay makes the two remote edges of a
square tend to zero, so the integrals along its two rays agree after rotation. -/
private theorem rotate_integral_of_decay {G : ℂ → ℂ} (hG : Differentiable ℂ G)
    {d C : ℝ} (hd : 0 < d) (hC : 0 ≤ C)
    (hb : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
      ‖G (x + y * I)‖ ≤ C * Real.exp (-d * (x + y)))
    (hr : IntegrableOn (fun x : ℝ ↦ G x) (Ioi 0))
    (hi : IntegrableOn (fun y : ℝ ↦ G (y * I)) (Ioi 0)) :
    (∫ x : ℝ in Ioi 0, G x) = I * ∫ y : ℝ in Ioi 0, G (y * I) := by
  have hlim : Tendsto (fun R : ℝ ↦ C * Real.exp (-d * R) * R) atTop (𝓝 0) := by
    have hh := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
      (tendsto_id.const_mul_atTop hd)
    convert hh.const_mul (C/d) using 1
    · funext x
      simp only [Function.comp_apply, pow_one, id_eq, neg_mul]
      field_simp
    · simp
  have hside {g : ℝ → ℝ → ℂ}
      (hg : ∀ R t, 0 ≤ R → 0 ≤ t → ‖g R t‖ ≤ C * Real.exp (-d * (t + R))) :
      Tendsto (fun R : ℝ ↦ ∫ t in (0 : ℝ)..R, g R t) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hlim
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
    simpa only [sub_zero, abs_of_nonneg hR] using
      intervalIntegral.norm_integral_le_of_norm_le_const (f := g R) (a := 0) (b := R)
        (C := C * Real.exp (-d * R)) (fun t ht ↦ by
          rw [uIoc_of_le hR] at ht
          exact (hg R t hR ht.1.le).trans (mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hd.le ht.1.le])) hC))
  have h₁ := hside (g := fun R t ↦ G (t + R * I)) fun R t hR ht ↦ hb t R ht hR
  have h₂ := hside (g := fun R t ↦ G (R + t * I)) fun R t hR ht ↦ by simpa [add_comm t R] using hb R t hR ht
  have h := (((intervalIntegral_tendsto_integral_Ioi 0 hr tendsto_id).sub h₁).add
    (h₂.const_mul I)).sub ((intervalIntegral_tendsto_integral_Ioi 0 hi tendsto_id).const_mul I)
  have he (R : ℝ) : (∫ t in (0 : ℝ)..R, G t) - (∫ t in (0 : ℝ)..R, G (t + R * I)) +
      I * (∫ t in (0 : ℝ)..R, G (R + t * I)) - I * (∫ t in (0 : ℝ)..R, G (t * I)) = 0 := by
    simpa only [zero_re, zero_im, ofReal_zero, zero_mul, add_zero, smul_eq_mul, zero_add] using
      integral_boundary_rect_eq_zero_of_differentiableOn G 0 ⟨R, R⟩ hG.differentiableOn
  simp only [id_eq, he, sub_zero, mul_zero, add_zero] at h
  exact sub_eq_zero.mp (tendsto_nhds_unique tendsto_const_nhds h).symm

private theorem laplace_rotate {f : ℂ → ℂ} (hf : Differentiable ℂ f) {A C u v : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hb : ∀ z, ‖f z‖ ≤ C * Real.exp (A * ‖z‖))
    (hu : LaplaceRates (fun t ↦ f t) u) (hv : LaplaceRates (fun t ↦ f (t * I)) v)
    {s : ℂ} (hs₁ : u < s.re) (hs₂ : v < -s.im) :
    halfLaplace (fun t ↦ f t) s = I * halfLaplace (fun t ↦ f (t * I)) (s * I) := by
  let U := {z : ℂ | u < z.re ∧ v < -z.im}
  have hU : IsOpen U := (isOpen_lt continuous_const continuous_re).inter
    (isOpen_lt continuous_const continuous_im.neg)
  have hpre : IsPreconnected U := by
    apply Convex.isPreconnected
    exact ((convex_Ioi u).linear_preimage reLm).inter
      ((convex_Ioi v).linear_preimage (-imLm))
  have hreal : Continuous (fun t : ℝ ↦ f t) := hf.continuous.comp continuous_ofReal
  have himag : Continuous (fun t : ℝ ↦ f (t * I)) := hf.continuous.comp (continuous_ofReal.mul_const _)
  have h₁ : DifferentiableOn ℂ (halfLaplace (fun t ↦ f t)) U :=
    fun z hz ↦ (halfLaplace_diff hreal hu hz.1).differentiableWithinAt
  have h₂ : DifferentiableOn ℂ (fun z ↦ I * halfLaplace (fun t ↦ f (t * I)) (z * I)) U := by
    intro z hz
    exact ((halfLaplace_diff himag hv (by simpa using hz.2 : v < (z * I).re)).comp z
      (differentiableAt_id.mul_const I)).const_mul I |>.differentiableWithinAt
  let z₀ : ℂ := ⟨max A u + 1, -(max A v + 1)⟩
  have hz₀ : z₀ ∈ U := ⟨by change u < max A u + 1; linarith [le_max_right A u], by
    change v < - -(max A v + 1); linarith [le_max_right A v]⟩
  apply (h₁.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq (h₂.analyticOnNhd hU) hpre hz₀ _ ⟨hs₁, hs₂⟩
  have hn : {z : ℂ | A < z.re ∧ A < -z.im} ∈ 𝓝 z₀ :=
    ((isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_const continuous_im.neg)).mem_nhds
      ⟨by change A < max A u + 1; linarith [le_max_left A u], by
        change A < - -(max A v + 1); linarith [le_max_left A v]⟩
  filter_upwards [hn, hU.mem_nhds hz₀] with z hz hzU
  let d := min (z.re - A) (-z.im - A)
  have hd : 0 < d := lt_min (sub_pos.mpr hz.1) (sub_pos.mpr hz.2)
  let G (w : ℂ) := f w * exp (-z * w)
  have hrot (t : ℝ) : G (t * I) = f (t * I) * exp (-(z * I) * t) := by dsimp [G]; ring_nf
  have hGi : IntegrableOn (fun t : ℝ ↦ G (t * I)) (Ioi 0) := by
    simp_rw [hrot]
    exact laplace_integrable himag hv (by simpa using hzU.2 : v < (z * I).re)
  have hh := rotate_integral_of_decay (G := G) (by dsimp [G]; fun_prop)
    hd hC (fun x y hx hy ↦ ?_) (laplace_integrable hreal hu hzU.1) hGi
  · simpa only [halfLaplace, hrot, G] using hh
  · have hn : ‖(x : ℂ) + y * I‖ ≤ x + y := by
      simpa [abs_of_nonneg hx, abs_of_nonneg hy] using norm_le_abs_re_add_abs_im ((x : ℂ) + y * I)
    dsimp only [G]
    rw [norm_mul, norm_exp]
    apply le_trans (mul_le_mul_of_nonneg_right (hb _) (Real.exp_pos _).le)
    rw [mul_assoc, ← Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ hC
    apply Real.exp_le_exp.mpr
    simp [mul_re]
    dsimp only [d]
    nlinarith [mul_le_mul_of_nonneg_left hn hA, mul_le_mul_of_nonneg_right (min_le_left (z.re - A) (-z.im - A)) hx,
      mul_le_mul_of_nonneg_right (min_le_right (z.re - A) (-z.im - A)) hy]

private def damp (g : ℝ → ℂ) (r : ℝ) (t : ℝ) := (Real.exp (-r * |t|) : ℂ) * g t

private theorem damp_integrable {g : ℝ → ℂ} (hg : MemLp g 2) {r : ℝ} (hr : 0 < r) :
    Integrable (damp g r) := by
  have he : MemLp (fun t : ℝ ↦ (Real.exp (-r * |t|) : ℂ)) 2 := by
    apply (memLp_two_iff_integrable_sq_norm (by fun_prop)).2
    have hn (t : ℝ) : ‖(Real.exp (-r * |t|) : ℂ)‖ ^ 2 = Real.exp ((-2 * r) * |t|) := by
      rw [norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, ← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    simp_rw [hn]
    rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
    constructor
    · exact (integrableOn_exp_mul_Iic (a := 2 * r) (by linarith) 0).congr_fun
        (fun t ht ↦ by rw [abs_of_nonpos ht]; ring_nf) measurableSet_Iic
    · exact (integrableOn_exp_mul_Ioi (a := -2 * r) (by linarith) 0).congr_fun
        (fun t ht ↦ by rw [abs_of_pos ht]) measurableSet_Ioi
  exact he.integrable_mul hg

private theorem damp_memLp {g : ℝ → ℂ} (hg : MemLp g 2) {r : ℝ} (hr : 0 ≤ r) :
    MemLp (damp g r) 2 := by
  apply hg.mono ((by fun_prop : Continuous fun t : ℝ ↦ (Real.exp (-r * |t|) : ℂ)).aestronglyMeasurable.mul hg.aestronglyMeasurable)
  exact ae_of_all _ fun t ↦ by
    change ‖(Real.exp (-r * |t|) : ℂ) * g t‖ ≤ ‖g t‖
    rw [norm_mul, norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hr) (abs_nonneg _)))

private def abelIntegral (f : ℂ → ℂ) (r ξ : ℝ) :=
  ∫ t : ℝ, damp (fun x ↦ f x) r t * exp (I * ξ * t)

/-- At a frequency greater than the type, rotation expresses the two damped
half-line integrals on the same imaginary ray with opposite orientations. -/
private theorem abelIntegral_tendsto {f : ℂ → ℂ} (hf : Differentiable ℂ f) {A C ξ : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hb : ∀ z, ‖f z‖ ≤ C * Real.exp (A * ‖z‖))
    (h₂ : MemLp (fun t : ℝ ↦ f t) 2) (hξ : A < ξ) :
    Tendsto (fun r ↦ abelIntegral f r ξ) (𝓝[>] 0) (𝓝 0) := by
  let H (z : ℂ) := halfLaplace (fun t ↦ f (t * I)) z
  have him : Continuous (fun t : ℝ ↦ f (t * I)) := hf.continuous.comp (continuous_ofReal.mul_const _)
  have hv : LaplaceRates (fun t ↦ f (t * I)) A := laplaceRates_growth him fun t ht ↦ by
    simpa [norm_mul, Real.norm_of_nonneg ht.le] using hb (t * I)
  have hH := (halfLaplace_diff him hv (s := (ξ : ℂ)) hξ).continuousAt
  have hhpos : Tendsto (fun r : ℝ ↦ H (ξ + r * I)) (𝓝 0) (𝓝 (H ξ)) := by
    apply hH.tendsto.comp
    simpa using (show Continuous (fun r : ℝ ↦ (ξ : ℂ) + r * I) by fun_prop).tendsto (0 : ℝ)
  have hhneg : Tendsto (fun r : ℝ ↦ H (ξ - r * I)) (𝓝 0) (𝓝 (H ξ)) := by
    apply hH.tendsto.comp
    simpa using (show Continuous (fun r : ℝ ↦ (ξ : ℂ) - r * I) by fun_prop).tendsto (0 : ℝ)
  have hlim := ((hhpos.sub hhneg).const_mul I).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  simp only [sub_self, mul_zero] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  change 0 < r at hr
  have hp := laplace_rotate hf hA hC hb (laplaceRates_l2 (h₂.mono_measure Measure.restrict_le_self)) hv
    (s := ⟨r, -ξ⟩) hr (by simpa using hξ)
  have hn' : MemLp (fun t : ℝ ↦ f (-t)) 2 := by
    simpa only [Function.comp_def, ofReal_neg] using h₂.comp_measurePreserving (Measure.measurePreserving_neg (volume : Measure ℝ))
  let fI (z : ℂ) := f (z * I)
  have hneg (t : ℝ) : fI (t * I) = f (-t) := by simp [fI, mul_assoc]
  have hn := laplace_rotate (f := fI) (hf.comp (differentiable_id.mul_const I))
    hA hC (fun z ↦ by simpa [fI] using hb (z * I)) hv
    (by simpa only [hneg] using laplaceRates_l2 (hn'.mono_measure Measure.restrict_le_self))
    (s := ⟨ξ, -r⟩) hξ (by simpa using hr)
  have hp' : halfLaplace (fun t ↦ f t) ⟨r, -ξ⟩ = I * H (ξ + r * I) := by
    convert hp using 3
    apply Complex.ext <;> simp
  have hn'' : H (ξ - r * I) = I * halfLaplace (fun t ↦ f (-t)) ⟨r, ξ⟩ := by
    simp only [hneg] at hn
    convert hn using 3 <;> first | solve | simp | exact Complex.ext (by simp) (by simp)
  let g (t : ℝ) := damp (fun t ↦ f t) r t * exp (I * ξ * t)
  have hg : Integrable g := by
    have hgc : Continuous g := by
      have := hf.continuous
      dsimp [g, damp]
      fun_prop
    apply (damp_integrable h₂ hr).mono hgc.aestronglyMeasurable
    exact ae_of_all _ fun t ↦ by simp [g, norm_exp]
  have hplus : (∫ t in Ioi (0 : ℝ), g t) = halfLaplace (fun t ↦ f t) ⟨r, -ξ⟩ := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp [g, damp]
    rw [abs_of_pos ht, ofReal_exp, mul_comm _ (f _), mul_assoc, ← exp_add]
    congr 2
    apply Complex.ext <;> simp [mul_re, mul_im]
  have hminus : (∫ t in Iic (0 : ℝ), g t) = halfLaplace (fun t ↦ f (-t)) ⟨r, ξ⟩ := by
    rw [← neg_zero, ← integral_comp_neg_Ioi]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp [g, damp]
    rw [abs_neg, abs_of_pos ht, ofReal_exp, mul_comm _ (f _), mul_assoc, ← exp_add, ofReal_neg]
    congr 2
    apply Complex.ext <;> simp [mul_re, mul_im]
  change _ = ∫ t, g t
  rw [← intervalIntegral.integral_Iic_add_Ioi hg.integrableOn hg.integrableOn, hplus, hminus, hp', hn'']
  linear_combination -(I_mul_I) * (halfLaplace (fun t ↦ f (-t)) ⟨r, ξ⟩)

private theorem ae_eq_of_schwartz_pairing {f : ℝ → ℂ} (hf : Continuous f)
    {u : Lp ℂ 2 (volume : Measure ℝ)}
    (h : ∀ φ : 𝓢(ℝ, ℂ), (∫ t, φ t * f t) = ∫ t, φ t * u t) :
    f =ᵐ[volume] (u : ℝ → ℂ) := by
  apply ae_eq_of_integral_contDiff_smul_eq hf.locallyIntegrable ((Lp.memLp u).locallyIntegrable one_le_two)
  intro g hg hc
  let gC : ℝ → ℂ := ofRealCLM ∘ g
  have hcC : HasCompactSupport gC := hc.comp_left rfl
  let φ := hcC.toSchwartzMap (ofRealCLM.contDiff.comp hg)
  exact h φ

private theorem fourier_L2_ae {g : ℝ → ℂ} (h₁ : Integrable g) (h₂ : MemLp g 2) :
    𝓕 g =ᵐ[volume] (𝓕 (h₂.toLp g) : Lp ℂ 2 (volume : Measure ℝ)) ∧
    𝓕⁻ g =ᵐ[volume] (𝓕⁻ (h₂.toLp g) : Lp ℂ 2 (volume : Measure ℝ)) := by
  have hflip : (-innerₗ ℝ).flip = -innerₗ ℝ := by ext; simp
  have hcont (L : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ) (hL : Continuous fun p : ℝ × ℝ ↦ L p.1 p.2) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar hL h₁
  constructor
  · apply ae_eq_of_schwartz_pairing (hcont _ continuous_inner)
    intro φ
    have hd := congrArg (fun D : 𝓢'(ℝ, ℂ) ↦ D φ) (Lp.fourier_toTemperedDistribution_eq (h₂.toLp g))
    simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply, smul_eq_mul] at hd
    rw [← hd]
    have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (μ := volume) (ν := volume) (L := innerₗ ℝ)
      Real.continuous_fourierChar continuous_inner h₁ φ.integrable
    rw [flip_innerₗ] at h
    simp only [smul_eq_mul] at h
    calc
      _ = ∫ t, (𝓕 g) t * φ t := by simp_rw [mul_comm (φ _)]; rfl
      _ = ∫ t, g t * 𝓕 (φ : ℝ → ℂ) t := h
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [h₂.coeFn_toLp] with t ht
        rw [ht, mul_comm, SchwartzMap.fourier_coe]
  · apply ae_eq_of_schwartz_pairing (hcont (-innerₗ ℝ) continuous_inner.neg)
    intro φ
    have hd := congrArg (fun D : 𝓢'(ℝ, ℂ) ↦ D φ) (Lp.fourierInv_toTemperedDistribution_eq (h₂.toLp g))
    simp only [TemperedDistribution.fourierInv_apply, Lp.toTemperedDistribution_apply, smul_eq_mul] at hd
    rw [← hd]
    have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (μ := volume) (ν := volume) (L := -innerₗ ℝ)
      Real.continuous_fourierChar continuous_inner.neg h₁ φ.integrable
    rw [hflip] at h
    simp only [smul_eq_mul] at h
    calc
      _ = ∫ t, (𝓕⁻ g) t * φ t := by simp_rw [mul_comm (φ _)]; rfl
      _ = ∫ t, g t * 𝓕⁻ (φ : ℝ → ℂ) t := h
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [h₂.coeFn_toLp] with t ht
        rw [ht, mul_comm, SchwartzMap.fourierInv_coe]

private def dampingRate (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

private theorem dampingRate_pos (n : ℕ) : 0 < dampingRate n := by unfold dampingRate; positivity

private theorem damp_tendsto_L2 {g : ℝ → ℂ} (hg : MemLp g 2) :
    Tendsto (fun n ↦ (damp_memLp hg (dampingRate_pos n).le).toLp (damp g (dampingRate n)))
      atTop (𝓝 (hg.toLp g)) := by
  let d (n : ℕ) := damp g (dampingRate n)
  let D (n : ℕ) := (damp_memLp hg (dampingRate_pos n).le).toLp (d n)
  have ht (n : ℕ) (x : ℝ) : ‖d n x - g x‖ ≤ ‖g x‖ := by
    change ‖(Real.exp (-(dampingRate n) * |x|) : ℂ) * g x - g x‖ ≤ _
    rw [← sub_one_mul, norm_mul, ← Complex.ofReal_one, ← ofReal_sub, norm_real, Real.norm_eq_abs]
    have he := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (dampingRate_pos n).le) (abs_nonneg x))
    rw [abs_of_nonpos (sub_nonpos.mpr he)]
    exact mul_le_of_le_one_left (norm_nonneg _) (by linarith [Real.exp_pos (-(dampingRate n) * |x|)])
  have hd (x : ℝ) : Tendsto (fun n ↦ d n x) atTop (𝓝 (g x)) := by
    have h : Tendsto dampingRate atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [d, damp] using ((continuous_ofReal.tendsto _).comp
      (Real.continuous_exp.tendsto _ |>.comp (h.neg.mul_const |x|))).mul_const (g x)
  have hconv := tendsto_integral_of_dominated_convergence (fun x ↦ ‖g x‖ ^ 2)
    (F := fun n x ↦ ‖d n x - g x‖ ^ 2) (f := fun _ ↦ (0 : ℝ))
    (fun n ↦ ((damp_memLp hg (dampingRate_pos n).le).aestronglyMeasurable.sub hg.aestronglyMeasurable).norm.aemeasurable.pow_const 2 |>.aestronglyMeasurable)
    ((memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg)
    (fun n ↦ ae_of_all _ fun x ↦ by rw [Real.norm_of_nonneg (sq_nonneg _)]; gcongr; exact ht n x)
    (ae_of_all _ fun x ↦ by simpa using ((hd x).sub_const (g x)).norm.pow 2)
  simp only [integral_zero] at hconv
  have he (n : ℕ) : ‖D n - hg.toLp g‖ ^ 2 = ∫ x, ‖d n x - g x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (D n) (hg.toLp g), (damp_memLp hg (dampingRate_pos n).le).coeFn_toLp,
      hg.coeFn_toLp] with x hsub h₁ h₂
    change (D n - hg.toLp g) x = D n x - (hg.toLp g) x at hsub
    change D n x = d n x at h₁
    rw [real_inner_self_eq_norm_sq, hsub, h₁, h₂]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hs := (Real.continuous_sqrt.tendsto 0).comp hconv
  change Tendsto (fun n ↦ √(∫ x, ‖d n x - g x‖ ^ 2)) atTop (𝓝 √0) at hs
  simpa only [← he, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hs

private theorem fourier_damp_tendsto_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {A C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hb : ∀ z, ‖f z‖ ≤ C * Real.exp (A * ‖z‖))
    (h₂ : MemLp (fun t : ℝ ↦ f t) 2) (w : ℝ) (hw : A < |2 * Real.pi * w|) :
    Tendsto (fun n ↦ 𝓕 (damp (fun t : ℝ ↦ f t) (dampingRate n)) w) atTop (𝓝 0) := by
  have ht : Tendsto dampingRate atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr
    ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall dampingRate_pos⟩
  have he (r : ℝ) : 𝓕 (damp (fun t : ℝ ↦ f t) r) w = abelIntegral f r (-2 * Real.pi * w) := by
    rw [Real.fourier_real_eq_integral_exp_smul, abelIntegral]
    apply integral_congr_ae
    exact ae_of_all _ fun t ↦ by simp only [smul_eq_mul]; rw [mul_comm]; congr 2; push_cast; ring
  simp_rw [he]
  rcases lt_abs.mp hw with hp | hm
  · have href : MemLp (fun t : ℝ ↦ f (-t)) 2 := by
      simpa only [Function.comp_def, ofReal_neg] using h₂.comp_measurePreserving (Measure.measurePreserving_neg volume)
    have h := (abelIntegral_tendsto (f := fun z ↦ f (-z)) (hf.comp differentiable_neg) hA hC
      (fun z ↦ by simpa using hb (-z)) href hp).comp ht
    apply h.congr (fun n ↦ ?_)
    change abelIntegral (fun z ↦ f (-z)) (dampingRate n) _ = abelIntegral f (dampingRate n) _
    unfold abelIntegral
    conv_lhs => rw [← integral_neg_eq_self]
    apply integral_congr_ae
    exact ae_of_all _ fun t ↦ by simp [damp]
  · apply (abelIntegral_tendsto hf hA hC hb h₂ (ξ := -2 * Real.pi * w) (by linarith)).comp ht

private theorem fourier_trace_support {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {A C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hb : ∀ z, ‖f z‖ ≤ C * Real.exp (A * ‖z‖))
    (h₂ : MemLp (fun t : ℝ ↦ f t) 2) :
    ∀ᵐ w : ℝ, A < |2 * Real.pi * w| → (𝓕 (h₂.toLp (fun t : ℝ ↦ f t)) : Lp ℂ 2) w = 0 := by
  let d (n : ℕ) := damp (fun t : ℝ ↦ f t) (dampingRate n)
  let hmem (n : ℕ) : MemLp (d n) 2 := damp_memLp h₂ (dampingRate_pos n).le
  let D (n : ℕ) := 𝓕 ((hmem n).toLp (d n))
  let F := 𝓕 (h₂.toLp (fun t : ℝ ↦ f t))
  have hc : Tendsto D atTop (𝓝 F) := (Lp.fourierTransformₗᵢ ℝ ℂ).continuous.continuousAt.tendsto.comp
    (damp_tendsto_L2 h₂)
  obtain ⟨m, hm, hsub⟩ := (tendstoInMeasure_of_tendsto_Lp hc).exists_seq_tendsto_ae
  have he (n : ℕ) : 𝓕 (d n) =ᵐ[volume] (D n : ℝ → ℂ) :=
    (fourier_L2_ae (damp_integrable h₂ (dampingRate_pos n)) (hmem n)).1
  filter_upwards [hsub, ae_all_iff.mpr he] with w hwhe hew
  intro hw
  apply tendsto_nhds_unique hwhe
  exact ((fourier_damp_tendsto_zero hf hA hC hb h₂ w hw).comp hm.tendsto_atTop).congr
    fun n ↦ hew (m n)

private def intervalExtension (A : ℝ) (F : ℝ → ℂ) (z : ℂ) :=
  ∫ t in Ioo (-A) A, F t * exp (I * t * z)

private theorem kernel_bound {x A : ℝ} (hx : x ∈ Ioo (-A) A) (z : ℂ) :
    ‖exp (I * x * z)‖ ≤ Real.exp (A * ‖z‖) := by
  rw [norm_exp]
  apply Real.exp_le_exp.mpr
  apply (re_le_norm _).trans
  simp only [norm_mul, norm_I, one_mul, norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (abs_le.mpr ⟨hx.1.le, hx.2.le⟩) (norm_nonneg _)

private theorem intervalExtension_bound {A : ℝ} {F : ℝ → ℂ}
    (hF : IntegrableOn F (Ioo (-A) A)) (z : ℂ) :
    ‖intervalExtension A F z‖ ≤ (∫ t in Ioo (-A) A, ‖F t‖) * Real.exp (A * ‖z‖) := by
  rw [← integral_mul_const]
  apply norm_integral_le_of_norm_le (hF.norm.mul_const _)
  filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioo] with x hx
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (kernel_bound hx z) (norm_nonneg _)

private theorem intervalExtension_diff {A : ℝ} (hA : 0 ≤ A) {F : ℝ → ℂ}
    (hF : IntegrableOn F (Ioo (-A) A)) : Differentiable ℂ (intervalExtension A F) := by
  intro z
  let μ := (volume : Measure ℝ).restrict (Ioo (-A) A)
  let G (w : ℂ) (t : ℝ) := F t * exp (I * t * w)
  let G' (w : ℂ) (t : ℝ) := G w t * (I * t)
  have hmeas (w : ℂ) : AEStronglyMeasurable (G w) μ :=
    hF.aestronglyMeasurable.mul (show Continuous fun t : ℝ ↦ exp (I * t * w) by fun_prop).aestronglyMeasurable
  have hg (w : ℂ) : Integrable (G w) μ := by
    apply (hF.norm.mul_const (Real.exp (A * ‖w‖))).mono' (hmeas w)
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioo] with x hx
    exact (norm_mul ..).le.trans (mul_le_mul_of_nonneg_left (kernel_bound hx w) (norm_nonneg _))
  have hder (w : ℂ) (t : ℝ) : HasDerivAt (G · t) (G' w t) w := by
    simpa [G, G', mul_assoc] using (((hasDerivAt_id w).const_mul (I * t)).cexp.const_mul (F t))
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := G) (F' := G')
    (Metric.ball_mem_nhds z zero_lt_one) (Eventually.of_forall hmeas) (hg z)
    ((hmeas z).mul (show Continuous fun t : ℝ ↦ I * t by fun_prop).aestronglyMeasurable)
    (bound := fun t ↦ ‖F t‖ * Real.exp (A * (‖z‖ + 1)) * A) ?_
    ((hF.norm.mul_const _).mul_const _) (ae_of_all _ fun t w _ ↦ hder w t)).2.differentiableAt
  filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioo] with t ht
  intro w hw
  have hw' : ‖w‖ ≤ ‖z‖ + 1 := by
    have h := norm_add_le (w - z) z
    rw [sub_add_cancel] at h
    linarith [show ‖w - z‖ < 1 by simpa only [Metric.mem_ball, dist_eq_norm] using hw]
  have ht' : |t| ≤ A := abs_le.mpr ⟨ht.1.le, ht.2.le⟩
  simp only [G', G, norm_mul, norm_I, one_mul, norm_real, Real.norm_eq_abs]
  apply mul_le_mul _ ht' (abs_nonneg _) (by positivity)
  exact mul_le_mul_of_nonneg_left ((kernel_bound ht w).trans
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hw' hA))) (norm_nonneg _)

private theorem intervalExtension_real (A : ℝ) (F : ℝ → ℂ) (x : ℝ) :
    intervalExtension A F ((2 * Real.pi * x : ℝ) : ℂ) = 𝓕⁻ ((Ioo (-A) A).indicator F) x := by
  rw [intervalExtension, ← integral_indicator measurableSet_Ioo, Real.fourierInv_eq']
  apply integral_congr_ae
  exact ae_of_all _ fun t ↦ by
    by_cases ht : t ∈ Ioo (-A) A
    · simp only [indicator_of_mem ht, smul_eq_mul, Real.inner_apply,
        ofReal_mul, ofReal_ofNat]
      rw [mul_comm (F t)]
      congr 2
      ring
    · simp [ht]

private theorem memLp_dilate {g : ℝ → ℂ} (h : MemLp g 2) {r : ℝ} (hr : r ≠ 0) :
    MemLp (fun x : ℝ ↦ g (r * x)) 2 := by
  have hm : MemLp g 2 (Measure.map (fun x : ℝ ↦ r • x) volume) := by
    rw [Measure.map_addHaar_smul volume hr]
    exact h.smul_measure ENNReal.ofReal_ne_top
  exact (memLp_map_measure_iff hm.aestronglyMeasurable (measurable_const_smul _).aemeasurable).mp hm

/-- Paper: Theorem 4.2.2.1, p. 170. The interval Fourier integral realizes the entire functions of the
given exponential type whose restriction to the real line is square integrable.
The kernel here uses angular frequency, without a factor of two pi. -/
theorem paleyWiener_interval (A : ℝ) (hA : 0 < A) (f : ℂ → ℂ) (hf : Differentiable ℂ f) :
    (∃ F : ℝ → ℂ, MemLp F 2 (volume.restrict (Ioo (-A) A)) ∧
      ∀ z, f z = ∫ t in Ioo (-A) A, F t * exp (I * t * z)) ↔
    ((∃ C : ℝ, 0 < C ∧ ∀ z, ‖f z‖ ≤ C * Real.exp (A * ‖z‖)) ∧
      MemLp (fun x : ℝ ↦ f x) 2 volume) := by
  let J := Ioo (-A) A
  let τ := 2 * Real.pi
  have hτ : 0 < τ := mul_pos zero_lt_two Real.pi_pos
  have hJ : IsFiniteMeasure (volume.restrict J) := isFiniteMeasure_restrict.mpr
    (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  constructor
  · rintro ⟨F, hF, he⟩
    have hF₁ : IntegrableOn F J := hF.integrable one_le_two
    let v := J.indicator F
    have hv : MemLp v 2 := (memLp_indicator_iff_restrict measurableSet_Ioo.nullMeasurableSet).mpr hF
    have hv₁ : Integrable v := hF₁.integrable_indicator measurableSet_Ioo
    constructor
    · let M := ∫ t in J, ‖F t‖
      refine ⟨M + 1, by have h : 0 ≤ M := integral_nonneg (fun t ↦ norm_nonneg _); linarith, fun z ↦ ?_⟩
      rw [he]
      exact (intervalExtension_bound hF₁ z).trans (mul_le_mul_of_nonneg_right (by linarith : M ≤ M + 1) (Real.exp_pos _).le)
    · have hv₂ := (memLp_two_fourier_and_eLpNorm_eq hv₁ hv).1
      have hx (x : ℝ) : f x = 𝓕 v ((-τ⁻¹) * x) := by
        have h := intervalExtension_real A F (τ⁻¹ * x)
        rw [Real.fourierInv_eq_fourier_neg] at h
        change intervalExtension A F ((τ * (τ⁻¹ * x) : ℝ) : ℂ) = 𝓕 v (-(τ⁻¹ * x)) at h
        rw [← mul_assoc, mul_inv_cancel₀ hτ.ne', one_mul] at h
        exact (he _).trans (by simpa only [intervalExtension, neg_mul] using h)
      simpa only [hx] using memLp_dilate hv₂ (neg_ne_zero.mpr (inv_ne_zero hτ.ne'))
  · rintro ⟨⟨C, hC, hb⟩, h₂⟩
    let g (z : ℂ) := f ((τ : ℂ) * z)
    have hg : Differentiable ℂ g := hf.comp (differentiable_id.const_mul _)
    have hg₂ : MemLp (fun t : ℝ ↦ g t) 2 := by
      simpa only [g, ← ofReal_mul] using memLp_dilate h₂ hτ.ne'
    let F := 𝓕 (hg₂.toLp (fun t : ℝ ↦ g t))
    have hs := fourier_trace_support hg (mul_nonneg hτ.le hA.le) hC.le (fun z ↦ by
      simpa [g, norm_mul, Real.norm_of_nonneg hτ.le, mul_assoc, mul_left_comm, mul_comm] using hb ((τ : ℂ) * z)) hg₂
    have he : J.indicator (F : ℝ → ℂ) =ᵐ[volume] (F : ℝ → ℂ) := by
      filter_upwards [hs, volume.ae_ne A, volume.ae_ne (-A)] with x hx hxA hxa
      by_cases h : x ∈ J
      · exact indicator_of_mem h _
      · rw [indicator_of_notMem h]
        apply Eq.symm
        apply hx
        change τ * A < |τ * x|
        rw [abs_mul, abs_of_pos hτ]
        apply mul_lt_mul_of_pos_left _ hτ
        change ¬(-A < x ∧ x < A) at h
        exact lt_abs.mpr (by rcases le_total A x with hx | hx <;> grind)
    have hF : MemLp (F : ℝ → ℂ) 2 (volume.restrict J) := (Lp.memLp F).mono_measure Measure.restrict_le_self
    have hF₁ : IntegrableOn (F : ℝ → ℂ) J := hF.integrable one_le_two
    let v := J.indicator (F : ℝ → ℂ)
    have hv : MemLp v 2 := (memLp_indicator_iff_restrict measurableSet_Ioo.nullMeasurableSet).mpr hF
    have hvF : hv.toLp v = F := Lp.ext (hv.coeFn_toLp.trans he)
    have hinv := (fourier_L2_ae (hF₁.integrable_indicator measurableSet_Ioo) hv).2
    rw [hvF, show 𝓕⁻ F = hg₂.toLp (fun t : ℝ ↦ g t) from FourierTransform.fourierInv_fourier_eq _] at hinv
    have hdiff := intervalExtension_diff hA.le hF₁
    have hreal : ∀ x : ℝ, intervalExtension A (F : ℝ → ℂ) x = f x := by
      have hh : (fun t : ℝ ↦ intervalExtension A (F : ℝ → ℂ) ((τ * t : ℝ) : ℂ)) =
          (fun t : ℝ ↦ g t) := by
        apply ((show Continuous (fun t : ℝ ↦ intervalExtension A (F : ℝ → ℂ) ((τ * t : ℝ) : ℂ)) from
          hdiff.continuous.comp (continuous_ofReal.comp (continuous_const.mul continuous_id))).ae_eq_iff_eq volume
          (hg.continuous.comp continuous_ofReal)).mp
        simpa only [J, Function.comp_def, τ, intervalExtension_real] using hinv.trans hg₂.coeFn_toLp
      intro x
      have hh' := congrFun hh (τ⁻¹ * x)
      simpa only [g, ← ofReal_mul, ← mul_assoc, mul_inv_cancel₀ hτ.ne', one_mul] using hh'
    refine ⟨F, hF, fun z ↦ ?_⟩
    have hpt : Tendsto (fun n ↦ ((dampingRate n : ℝ) : ℂ)) atTop (𝓝[≠] (0 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n ↦ ?_⟩
      · simpa only [Function.comp_def, ofReal_zero] using continuous_ofReal.continuousAt.tendsto.comp
          (show Tendsto dampingRate atTop (𝓝 0) from tendsto_one_div_add_atTop_nhds_zero_nat)
      · exact ofReal_ne_zero.mpr (dampingRate_pos n).ne'
    exact congrFun ((hf.differentiableOn.analyticOnNhd isOpen_univ).eq_of_frequently_eq (hdiff.differentiableOn.analyticOnNhd isOpen_univ)
      (hpt.frequently (.of_forall fun n ↦ (hreal (dampingRate n)).symm))) z

end RiemannMasullo
