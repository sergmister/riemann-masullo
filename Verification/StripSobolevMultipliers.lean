import RiemannMasullo.Ch09_HardySobolev.Sec2
import Mathlib.MeasureTheory.Measure.Prod

/-! # Uniform Mellin multiplier bounds on a symmetric Hardy–Sobolev strip

This auxiliary result for the geometric common-kernel question in §10.2 uses the
project's actual compact-interval density. If a family of holomorphic multipliers
is contractive on a wider strip and tends to one pointwise there, its operators
on the whole weighted L² space are uniformly bounded and converge strongly to
the identity. The argument uses Plancherel on two lines, local exponential windows,
and a positive average of their translates. The final theorem states the width
and degree assumptions explicitly.
-/

noncomputable section
open Filter Function MeasureTheory Set
open scoped SchwartzMap FourierTransform Topology ENNReal
namespace RiemannMasullo.StripMultiplier

private def reflectedTwist {I : Set ℝ} (a : I) (p : PositiveRealExponentialDecay I) : 𝓢(ℝ, ℂ) :=
  schwartzChangeVariable ℂ (LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ).toContinuousLinearEquiv
    (logExponentialDecayTwist I a p)

private theorem mellin_eq_fourier_twist {I : Set ℝ} (a : I) (p : PositiveRealExponentialDecay I)
    (u : ℝ) :
    mellin (fun t ↦ p.val (Real.log t)) ⟨a.val, u * (2 * Real.pi)⟩ = 𝓕 (reflectedTwist a p) u := by
  rw [SchwartzMap.fourier_coe, mellin_eq_fourier]
  rw [mul_div_cancel_right₀ _ (mul_ne_zero two_ne_zero Real.pi_ne_zero)]
  apply congrArg (fun g : ℝ → ℂ ↦ 𝓕 g u)
  funext x
  change _ = logExponentialDecayTwist I a p (-x)
  rw [logExponentialDecayTwist_apply I a p (-x), Real.log_exp, Complex.real_smul, neg_mul, mul_neg]

private theorem norm_twist_sq {I : Set ℝ} (a : I) (p : PositiveRealExponentialDecay I) (x : ℝ) :
    ‖logExponentialDecayTwist I a p x‖ ^ 2 = Real.exp (2 * a.val * x) * ‖p.val x‖ ^ 2 := by
  rw [logExponentialDecayTwist_apply I a p x, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), mul_pow, ← Real.exp_nat_mul]
  congr 2
  push_cast
  ring

private theorem reflected_integral {I : Set ℝ} (a : I) (p : PositiveRealExponentialDecay I) :
    ∫ x, ‖reflectedTwist a p x‖ ^ 2 = ∫ x, Real.exp (2 * a.val * x) * ‖p.val x‖ ^ 2 := by
  change ∫ x, ‖logExponentialDecayTwist I a p (-x)‖ ^ 2 = _
  rw [integral_neg_eq_self (fun x ↦ ‖logExponentialDecayTwist I a p x‖ ^ 2)]
  exact integral_congr_ae (Eventually.of_forall (norm_twist_sq a p))

/-- A multiplier contractive on one vertical Mellin line is contractive for the
corresponding exponential square norm of logarithmic test profiles. -/
theorem line_contraction {I : Set ℝ} (a : I) (p q : PositiveRealExponentialDecay I)
    (h : ∀ v : ℝ, ‖mellin (fun t ↦ q.val (Real.log t)) ⟨a.val, v⟩‖ ≤
      ‖mellin (fun t ↦ p.val (Real.log t)) ⟨a.val, v⟩‖) :
    ∫ x, Real.exp (2 * a.val * x) * ‖q.val x‖ ^ 2 ≤
      ∫ x, Real.exp (2 * a.val * x) * ‖p.val x‖ ^ 2 := by
  rw [← reflected_integral, ← reflected_integral, ← SchwartzMap.integral_norm_sq_fourier,
    ← SchwartzMap.integral_norm_sq_fourier (reflectedTwist a p)]
  apply integral_mono
  · exact ((𝓕 (reflectedTwist a q)).memLp 2 volume).integrable_norm_pow (by norm_num : 2 ≠ 0)
  · exact ((𝓕 (reflectedTwist a p)).memLp 2 volume).integrable_norm_pow (by norm_num : 2 ≠ 0)
  · intro u
    have hu := h (u * (2 * Real.pi))
    rw [mellin_eq_fourier_twist, mellin_eq_fourier_twist] at hu
    exact pow_le_pow_left₀ (norm_nonneg _) hu 2

/-- A uniform bound for translates of a nonnegative window passes to every
positive mixture of those windows. -/
theorem integrate_window_bounds {X U : Type*} [MeasurableSpace X] [MeasurableSpace U]
    (μ : Measure X) (ν : Measure U) [SFinite μ] [SFinite ν]
    (K : U → X → ℝ≥0∞) (hK : Measurable (uncurry K)) (f g : X → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) (C : ℝ≥0∞)
    (h : ∀ u, ∫⁻ x, K u x * g x ∂μ ≤ C * ∫⁻ x, K u x * f x ∂μ) :
    ∫⁻ x, (∫⁻ u, K u x ∂ν) * g x ∂μ ≤ C * ∫⁻ x, (∫⁻ u, K u x ∂ν) * f x ∂μ := by
  have swap (F : X → ℝ≥0∞) (hF : Measurable F) :
      ∫⁻ x, (∫⁻ u, K u x ∂ν) * F x ∂μ = ∫⁻ u, ∫⁻ x, K u x * F x ∂μ ∂ν := by
    calc
      _ = ∫⁻ x, ∫⁻ u, K u x * F x ∂ν ∂μ := by
        apply lintegral_congr
        intro x
        exact (lintegral_mul_const _ (hK.comp (measurable_id.prodMk measurable_const))).symm
      _ = _ := lintegral_lintegral_swap ((hK.comp measurable_swap).mul (hF.comp measurable_fst)).aemeasurable
  rw [swap g hg, swap f hf]
  calc
    _ ≤ ∫⁻ u, C * ∫⁻ x, K u x * f x ∂μ ∂ν := lintegral_mono h
    _ = _ := lintegral_const_mul _ ((hK.mul (hf.comp measurable_snd)).lintegral_prod_right')

/-- The smooth step is temperate. Every derivative of positive order vanishes
outside the unit interval. -/
private theorem smoothTransition_temperate : Function.HasTemperateGrowth Real.smoothTransition := by
  have hc : ContDiff ℝ (⊤ : ℕ∞) Real.smoothTransition := Real.smoothTransition.contDiff
  have hcompact : HasCompactSupport (fderiv ℝ Real.smoothTransition) := by
    apply HasCompactSupport.intro (isCompact_Icc (α := ℝ) (a := 0) (b := 1))
    intro x hx
    rcases (not_and_or.mp hx) with hl | hr
    · have h : Real.smoothTransition =ᶠ[𝓝 x] fun _ ↦ 0 := by
        filter_upwards [gt_mem_nhds (lt_of_not_ge hl)] with y hy
        exact Real.smoothTransition.zero_of_nonpos hy.le
      simpa using h.fderiv_eq (𝕜 := ℝ)
    · have h : Real.smoothTransition =ᶠ[𝓝 x] fun _ ↦ 1 := by
        filter_upwards [lt_mem_nhds (lt_of_not_ge hr)] with y hy
        exact Real.smoothTransition.one_of_one_le hy.le
      simpa using h.fderiv_eq (𝕜 := ℝ)
  apply Function.HasTemperateGrowth.of_fderiv (hcompact.hasTemperateGrowth (hc.fderiv_right (by simp)))
    (hc.differentiable (by simp)) (C := 1) (k := 0)
  intro x
  simpa [Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg _)] using Real.smoothTransition.le_one x

private def multiplyProfile {I : Set ℝ} (g : ℝ → ℂ) (hg : g.HasTemperateGrowth)
    (p : PositiveRealExponentialDecay I) : PositiveRealExponentialDecay I := by
  refine ⟨fun x ↦ g x * p.val x, (Submodule.mem_iInf _).2 ?_⟩
  intro a
  refine ⟨SchwartzMap.smulLeftCLM ℂ g (logExponentialDecayTwist I a p), ?_⟩
  funext x
  change SchwartzMap.smulLeftCLM ℂ g (logExponentialDecayTwist I a p) x =
    (Real.exp (a.val * x) : ℂ) * (g x * p.val x)
  rw [SchwartzMap.smulLeftCLM_apply_apply hg, logExponentialDecayTwist_apply I a p x, smul_eq_mul]
  ring

private def window (β u x : ℝ) : ℝ := Real.exp (-(2 * β) * |x-u|)

private theorem window_le_line (β u x : ℝ) (hβ : 0 ≤ β) :
    window β u x ≤ Real.exp (2 * β * (x-u)) ∧ window β u x ≤ Real.exp (-(2 * β) * (x-u)) := by
  unfold window
  constructor <;> apply Real.exp_le_exp.mpr
  · nlinarith [mul_nonneg hβ (show 0 ≤ |x-u| + (x-u) from by linarith [neg_abs_le (x-u)])]
  · nlinarith [mul_nonneg hβ (sub_nonneg.mpr (le_abs_self (x-u)))]

private theorem line_step_bounds (β y : ℝ) (hβ : 0 ≤ β) :
    Real.exp (-(2 * β) * y) * Real.smoothTransition y ^ 2 ≤ window β 0 y ∧
    Real.exp (2 * β * y) * (1 - Real.smoothTransition y) ^ 2 ≤ Real.exp (4 * β) * window β 0 y := by
  have h0 := Real.smoothTransition.nonneg y
  have h1 := Real.smoothTransition.le_one y
  have hpow : Real.smoothTransition y ^ 2 ≤ 1 := by nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1)]
  have hpow' : (1 - Real.smoothTransition y) ^ 2 ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr h1) (show 0 ≤ 2 - Real.smoothTransition y by linarith)]
  simp only [window, sub_zero]
  constructor
  · by_cases hy : y ≤ 0
    · simp [Real.smoothTransition.zero_of_nonpos hy, (Real.exp_pos _).le]
    · rw [abs_of_nonneg (le_of_not_ge hy)]
      exact (mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le).trans_eq (mul_one _)
  · by_cases hy : 1 ≤ y
    · simp only [Real.smoothTransition.one_of_one_le hy, sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero]
      positivity
    · calc
        _ ≤ Real.exp (2 * β * y) := (mul_le_mul_of_nonneg_left hpow' (Real.exp_pos _).le).trans_eq (mul_one _)
        _ ≤ _ := by
          rw [← Real.exp_add, Real.exp_le_exp]
          by_cases h : 0 ≤ y
          · rw [abs_of_nonneg h]
            nlinarith [mul_nonneg hβ (sub_nonneg.mpr (le_of_not_ge hy))]
          · rw [abs_of_nonpos (le_of_not_ge h)]
            nlinarith


private def lineWeight (v u x : ℝ) : ℝ := Real.exp (2 * v * (x - u))

private def energy {I : Set ℝ} (w : ℝ → ℝ) (p : PositiveRealExponentialDecay I) : ℝ :=
  ∫ x, w x * ‖p.val x‖ ^ 2

private theorem profile_continuous {I : Set ℝ} (h0 : 0 ∈ I) (p : PositiveRealExponentialDecay I) :
    Continuous p.val := by
  apply (logExponentialDecayTwist I ⟨0, h0⟩ p).continuous.congr
  intro x
  simpa using logExponentialDecayTwist_apply I ⟨0, h0⟩ p x

private theorem shifted_line_split (v u x : ℝ) :
    lineWeight v u x = Real.exp (-(2 * v * u)) * Real.exp (2 * v * x) := by
  rw [lineWeight, ← Real.exp_add]
  congr 1
  ring

private theorem line_integrable {I : Set ℝ} (v : I) (u : ℝ) (p : PositiveRealExponentialDecay I) :
    Integrable (fun x ↦ lineWeight v.val u x * ‖p.val x‖ ^ 2) := by
  have h := ((logExponentialDecayTwist I v p).memLp 2 volume).integrable_norm_pow (by norm_num : 2 ≠ 0)
  apply (h.const_mul (Real.exp (-(2 * v.val * u)))).congr
  filter_upwards with x
  rw [shifted_line_split, norm_twist_sq]
  ring

private theorem window_integrable {I : Set ℝ} (h0 : 0 ∈ I) {β : ℝ} (hβ : 0 ≤ β)
    (hβI : β ∈ I) (u : ℝ) (p : PositiveRealExponentialDecay I) :
    Integrable (fun x ↦ window β u x * ‖p.val x‖ ^ 2) := by
  refine (line_integrable ⟨β, hβI⟩ u p).mono' ?_ (Eventually.of_forall fun x ↦ ?_)
  · exact ((show Continuous (window β u) from by unfold window; fun_prop).mul
      ((profile_continuous h0 p).norm.pow 2)).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (mul_nonneg (show 0 ≤ window β u x from (Real.exp_pos _).le) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_right (window_le_line β u x hβ).1 (sq_nonneg _)

private theorem line_energy_split {I : Set ℝ} (v u : ℝ) (p : PositiveRealExponentialDecay I) :
    energy (lineWeight v u) p = Real.exp (-(2 * v * u)) * ∫ x, Real.exp (2 * v * x) * ‖p.val x‖ ^ 2 := by
  simp only [energy, shifted_line_split, mul_assoc, integral_const_mul]

/-- Uniform bounds on two exponential lines imply a uniform bound in every
translate of the decaying two-sided exponential window. -/
theorem window_energy_bound {I : Set ℝ} (h0 : 0 ∈ I) {β : ℝ} (hβ : 0 ≤ β)
    (hp : β ∈ I) (hm : -β ∈ I)
    (T : PositiveRealExponentialDecay I →ₗ[ℂ] PositiveRealExponentialDecay I)
    (hT : ∀ (v : I) (p : PositiveRealExponentialDecay I),
      ∫ x, Real.exp (2 * v.val * x) * ‖(T p).val x‖ ^ 2 ≤
        ∫ x, Real.exp (2 * v.val * x) * ‖p.val x‖ ^ 2)
    (u : ℝ) (p : PositiveRealExponentialDecay I) :
    energy (window β u) (T p) ≤ 2 * (1 + Real.exp (4 * β)) * energy (window β u) p := by
  let h (x : ℝ) : ℂ := Real.smoothTransition (x-u)
  have hh : h.HasTemperateGrowth := Complex.hasTemperateGrowth_ofReal.comp <|
    smoothTransition_temperate.comp <| Function.HasTemperateGrowth.id'.sub (Function.HasTemperateGrowth.const u)
  let r := multiplyProfile h hh p
  let l := p - r
  have hlr (x : ℝ) : (T p).val x = (T l).val x + (T r).val x := by
    have he : T p = T l + T r := by rw [← map_add, sub_add_cancel]
    exact congrArg (fun q : PositiveRealExponentialDecay I ↦ q.val x) he
  have hleft (x : ℝ) : l.val x = ((1 - Real.smoothTransition (x-u) : ℝ) : ℂ) * p.val x := by
    change p.val x - h x * p.val x = _
    dsimp only [h]
    push_cast
    ring
  have hright (x : ℝ) : r.val x = (Real.smoothTransition (x-u) : ℂ) * p.val x := rfl
  have trans (v : I) (f : PositiveRealExponentialDecay I) :
      energy (lineWeight v.val u) (T f) ≤ energy (lineWeight v.val u) f := by
    rw [line_energy_split, line_energy_split]
    exact mul_le_mul_of_nonneg_left (hT v f) (Real.exp_pos _).le
  have hupp :
      energy (window β u) (T p) ≤ 2 * (energy (lineWeight β u) (T l) + energy (lineWeight (-β) u) (T r)) := by
    unfold energy
    rw [← integral_add (line_integrable ⟨β, hp⟩ u (T l)) (line_integrable ⟨-β, hm⟩ u (T r)),
      ← integral_const_mul]
    apply integral_mono (window_integrable h0 hβ hp u (T p)) (((line_integrable ⟨β, hp⟩ u (T l)).add
      (line_integrable ⟨-β, hm⟩ u (T r))).const_mul 2)
    intro x
    change window β u x * ‖(T p).val x‖ ^ 2 ≤ 2 * (lineWeight β u x * ‖(T l).val x‖ ^ 2 + lineWeight (-β) u x * ‖(T r).val x‖ ^ 2)
    rw [hlr x]
    have hs : ‖(T l).val x + (T r).val x‖ ^ 2 ≤ 2 * (‖(T l).val x‖^2 + ‖(T r).val x‖^2) := by
      exact (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2).trans (by nlinarith [sq_nonneg (‖(T l).val x‖-‖(T r).val x‖)])
    have hpm := window_le_line β u x hβ
    have hmn : window β u x ≤ lineWeight (-β) u x := by simpa [lineWeight, mul_neg] using hpm.2
    calc
      _ ≤ window β u x * (2 * (‖(T l).val x‖^2 + ‖(T r).val x‖^2)) := mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le
      _ = 2 * (window β u x * ‖(T l).val x‖^2 + window β u x * ‖(T r).val x‖^2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_right hpm.1 (sq_nonneg _))
        (mul_le_mul_of_nonneg_right hmn (sq_nonneg _))) (by norm_num)
  have hu (x : ℝ) : window β 0 (x-u) = window β u x := by simp [window]
  have hle : energy (lineWeight β u) l ≤ Real.exp (4 * β) * energy (window β u) p := by
    unfold energy
    rw [← integral_const_mul]
    apply integral_mono (line_integrable ⟨β, hp⟩ u l) ((window_integrable h0 hβ hp u p).const_mul _)
    intro x
    change lineWeight β u x * ‖l.val x‖ ^ 2 ≤ Real.exp (4 * β) * (window β u x * ‖p.val x‖ ^ 2)
    rw [hleft x, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (Real.smoothTransition.le_one _)),
      mul_pow, ← mul_assoc, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right ((line_step_bounds β (x-u) hβ).2.trans_eq (by rw [hu])) (sq_nonneg _)
  have hre : energy (lineWeight (-β) u) r ≤ energy (window β u) p := by
    apply integral_mono (line_integrable ⟨-β, hm⟩ u r) (window_integrable h0 hβ hp u p)
    intro x
    change lineWeight (-β) u x * ‖r.val x‖ ^ 2 ≤ window β u x * ‖p.val x‖ ^ 2
    rw [hright x, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg _),
      mul_pow, ← mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    simpa [lineWeight, mul_neg, hu] using (line_step_bounds β (x-u) hβ).1
  calc
    _ ≤ _ := hupp
    _ ≤ 2 * (energy (lineWeight β u) l + energy (lineWeight (-β) u) r) :=
      mul_le_mul_of_nonneg_left (add_le_add (trans ⟨β, hp⟩ l) (trans ⟨-β, hm⟩ r)) (by norm_num)
    _ ≤ 2 * (Real.exp (4 * β) * energy (window β u) p + energy (window β u) p) :=
      mul_le_mul_of_nonneg_left (add_le_add hle hre) (by norm_num)
    _ = _ := by ring


/-- The positive and negative halves of a decaying two-sided exponential have
equal finite mass. -/
private theorem laplace_mass {c : ℝ} (hc : 0 < c) (x : ℝ) :
    ∫⁻ u : ℝ, ENNReal.ofReal (Real.exp (-c * |u-x|)) = ENNReal.ofReal (2/c) := by
  let f (t : ℝ) := Real.exp (-c * |t|)
  have hlo : IntegrableOn f (Iic 0) := by
    apply (integrableOn_exp_mul_Iic hc 0).congr_fun _ measurableSet_Iic
    intro t ht
    simp [f, abs_of_nonpos (Set.mem_Iic.mp ht)]
  have hhi : IntegrableOn f (Ioi 0) := by
    apply (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hc) 0).congr_fun _ measurableSet_Ioi
    intro t ht
    simp [f, abs_of_nonneg (Set.mem_Ioi.mp ht).le]
  have hf : Integrable f := by
    rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
    exact ⟨hlo,hhi⟩
  have h1 : ∫ t in Iic 0, f t = 1/c := by
    calc
      _ = ∫ t : ℝ in Iic 0, Real.exp (c*t) := setIntegral_congr_fun measurableSet_Iic (fun t ht ↦ by simp [f, abs_of_nonpos (Set.mem_Iic.mp ht)])
      _ = _ := by simp [integral_exp_mul_Iic hc]
  have h2 : ∫ t in Ioi 0, f t = 1/c := by
    calc
      _ = ∫ t : ℝ in Ioi 0, Real.exp ((-c)*t) := setIntegral_congr_fun measurableSet_Ioi (fun t ht ↦ by simp [f, abs_of_nonneg (Set.mem_Ioi.mp ht).le])
      _ = _ := by rw [integral_exp_mul_Ioi (neg_lt_zero.mpr hc)]; simp
  rw [← ofReal_integral_eq_lintegral_ofReal (hf.comp_sub_right x) (Eventually.of_forall fun t ↦ (Real.exp_pos _).le)]
  change ENNReal.ofReal (∫ u : ℝ, f (u-x)) = _
  rw [integral_sub_right_eq_self f x, ← integral_add_compl (s := Iic (0:ℝ)) measurableSet_Iic hf,
    compl_Iic, h1, h2]
  congr 1
  ring

/-- If a density has a fixed exponential translation bound, convolution with
a faster two-sided exponential gives a uniformly comparable density. -/
theorem compare_window_density {w : ℝ → ℝ} {κ β : ℝ} (hκ : 0 ≤ κ)
    (hm : ∀ u x, w u ≤ Real.exp (κ * |u-x|) * w x) (hβ : κ < 2*β) (x : ℝ) :
    let mass := ∫⁻ u : ℝ, ENNReal.ofReal (window β u x * w u)
    ENNReal.ofReal (2/(2*β+κ)) * ENNReal.ofReal (w x) ≤ mass ∧
      mass ≤ ENNReal.ofReal (2/(2*β-κ)) * ENNReal.ofReal (w x) := by
  intro mass
  have shape (c : ℝ) (hc : 0 < c) :
      ∫⁻ u : ℝ, ENNReal.ofReal (Real.exp (-c * |u-x|) * w x) =
        ENNReal.ofReal (2/c) * ENNReal.ofReal (w x) := by
    simp_rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
    rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, laplace_mass hc]
  constructor
  · rw [← shape _ (by linarith)]
    apply lintegral_mono
    intro u
    apply ENNReal.ofReal_le_ofReal
    have hu : Real.exp (-κ*|u-x|) * w x ≤ w u := by
      have hh := mul_le_mul_of_nonneg_left (hm x u) (Real.exp_pos (-κ*|u-x|)).le
      rw [abs_sub_comm x u, ← mul_assoc, ← Real.exp_add, show -κ*|u-x| + κ*|u-x| = 0 by ring,
        Real.exp_zero, one_mul] at hh
      exact hh
    calc
      _ = Real.exp (-(2*β)*|u-x|) * (Real.exp (-κ*|u-x|) * w x) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ window β u x * w u := by
        rw [window, abs_sub_comm x u]
        exact mul_le_mul_of_nonneg_left hu (Real.exp_pos _).le
  · rw [← shape _ (sub_pos.mpr hβ)]
    apply lintegral_mono
    intro u
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ window β u x * (Real.exp (κ*|u-x|) * w x) := mul_le_mul_of_nonneg_left (hm u x) (Real.exp_pos _).le
      _ = _ := by
        rw [window, abs_sub_comm x u, ← mul_assoc, ← Real.exp_add]
        congr 2
        ring


/-- A weighted square norm written with a nonnegative integral. -/
private def eEnergy {I : Set ℝ} (w : ℝ → ℝ) (p : PositiveRealExponentialDecay I) :=
  ∫⁻ (x : ℝ), ENNReal.ofReal (w x) * ENNReal.ofReal (‖p.val x‖ ^ 2)

private theorem eEnergy_eq {I : Set ℝ} {w : ℝ → ℝ} (hw : ∀ x, 0 ≤ w x) (p : PositiveRealExponentialDecay I)
    (hi : Integrable (fun x ↦ w x * ‖p.val x‖^2)) :
    eEnergy w p = ENNReal.ofReal (energy w p) := by
  unfold eEnergy energy
  rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun x ↦ mul_nonneg (hw x) (sq_nonneg _))]
  simp_rw [ENNReal.ofReal_mul (hw _)]

/-- The two one-line contractions give a single square-norm bound, uniform in
the multiplier, for any continuous density with controlled translation growth. -/
theorem eEnergy_bound {I : Set ℝ} (h0 : 0 ∈ I) {β κ : ℝ} (hκ : 0 ≤ κ) (hβ : κ < 2*β)
    (hp : β ∈ I) (hm : -β ∈ I) (w : ℝ → ℝ) (hwc : Continuous w)
    (hmod : ∀ u x, w u ≤ Real.exp (κ * |u-x|) * w x)
    (T : PositiveRealExponentialDecay I →ₗ[ℂ] PositiveRealExponentialDecay I)
    (hT : ∀ (v : I) (p : PositiveRealExponentialDecay I),
      ∫ x, Real.exp (2 * v.val * x) * ‖(T p).val x‖ ^ 2 ≤
        ∫ x, Real.exp (2 * v.val * x) * ‖p.val x‖ ^ 2)
    (p : PositiveRealExponentialDecay I) :
    ENNReal.ofReal (2/(2*β+κ)) * eEnergy w (T p) ≤
      (ENNReal.ofReal (2*(1+Real.exp (4*β))) * ENNReal.ofReal (2/(2*β-κ))) * eEnergy w p := by
  let K (u x : ℝ) := ENNReal.ofReal (window β u x * w u)
  let R (p : PositiveRealExponentialDecay I) (x : ℝ) := ENNReal.ofReal (‖p.val x‖^2)
  let C := ENNReal.ofReal (2*(1+Real.exp (4*β)))
  have hR (p : PositiveRealExponentialDecay I) : Measurable (R p) :=
    ((profile_continuous h0 p).norm.pow 2).measurable.ennreal_ofReal
  have hK : Measurable (uncurry K) := by
    change Measurable (fun t : ℝ × ℝ ↦ ENNReal.ofReal (Real.exp (-(2*β)*|t.2-t.1|) * w t.1))
    fun_prop
  have pull (u : ℝ) (f : PositiveRealExponentialDecay I) :
      ∫⁻ x, K u x * R f x = ENNReal.ofReal (w u) * ENNReal.ofReal (energy (window β u) f) := by
    have hw0 (x : ℝ) : 0 ≤ window β u x := (Real.exp_pos _).le
    simp only [K, ENNReal.ofReal_mul (hw0 _)]
    simp_rw [mul_comm (ENNReal.ofReal (window β u _)) (ENNReal.ofReal (w u)), mul_assoc]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact congrArg _ (eEnergy_eq (fun _ ↦ (Real.exp_pos _).le) f (window_integrable h0 (by linarith) hp u f))
  have hh (u : ℝ) : ∫⁻ x, K u x * R (T p) x ≤ C * ∫⁻ x, K u x * R p x := by
    rw [pull, pull, mul_left_comm]
    apply mul_le_mul' le_rfl
    change ENNReal.ofReal _ ≤ ENNReal.ofReal _ * ENNReal.ofReal _
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * (1+Real.exp (4*β)))]
    exact ENNReal.ofReal_le_ofReal (window_energy_bound h0 (by linarith) hp hm T hT u p)
  have avg := integrate_window_bounds volume volume K hK (R p) (R (T p)) (hR _) (hR _) C hh
  have factor (d : ℝ) (f : PositiveRealExponentialDecay I) :
      ENNReal.ofReal d * eEnergy w f = ∫⁻ x, (ENNReal.ofReal d * ENNReal.ofReal (w x)) * R f x := by
    simp_rw [mul_assoc]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    rfl
  calc
    _ = _ := factor _ (T p)
    _ ≤ ∫⁻ x, (∫⁻ u, K u x) * R (T p) x := lintegral_mono fun x ↦ mul_le_mul'
      (compare_window_density hκ hmod hβ x).1 le_rfl
    _ ≤ _ := avg
    _ ≤ C * (ENNReal.ofReal (2/(2*β-κ)) * eEnergy w p) := by
      rw [factor]
      exact mul_le_mul' le_rfl (lintegral_mono fun x ↦ mul_le_mul' (compare_window_density hκ hmod hβ x).2 le_rfl)
    _ = _ := (mul_assoc _ _ _).symm


private theorem density_symmetric {α : ℝ} (hα : 0 ≤ α) (s x : ℝ) :
    intervalSobolevDensity (-α) α s x = Real.exp (2*α*|x|) * (1+x^2)^(s/2) := by
  unfold intervalSobolevDensity
  congr 1
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h, max_eq_right (Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hα h]))]
  · rw [abs_of_nonpos h, max_eq_left (Real.exp_le_exp.mpr (by nlinarith [mul_nonpos_of_nonneg_of_nonpos hα h]))]
    congr 1
    ring

private theorem polynomial_shift (x d : ℝ) :
    1 + (x+d)^2 ≤ (1+|d|)^2 * (1+x^2) := by
  rcases le_total 0 d with h | h
  · rw [abs_of_nonneg h]
    nlinarith [mul_nonneg h (sq_nonneg (x-1)), mul_nonneg h (sq_nonneg x), sq_nonneg (d*x)]
  · rw [abs_of_nonpos h]
    nlinarith [mul_nonneg (neg_nonneg.mpr h) (sq_nonneg (x+1)), mul_nonneg (neg_nonneg.mpr h) (sq_nonneg x), sq_nonneg (d*x)]

/-- An explicit exponential translation bound for the actual symmetric
Hardy–Sobolev weight. -/
theorem density_translation {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (u x : ℝ) :
    intervalSobolevDensity (-α) α s u ≤ Real.exp ((2*α+s)*|u-x|) * intervalSobolevDensity (-α) α s x := by
  let d := u-x
  have hd : x+d = u := by dsimp [d]; ring
  have hsum : |u| ≤ |d| + |x| := by simpa only [← hd, add_comm |d|] using abs_add_le x d
  have hpoly : 1+u^2 ≤ Real.exp (2*|d|) * (1+x^2) := by
    calc
      _ ≤ (1+|d|)^2 * (1+x^2) := hd ▸ polynomial_shift x d
      _ ≤ (Real.exp |d|)^2 * (1+x^2) := by
        gcongr
        linarith [Real.add_one_le_exp |d|]
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hp : (1+u^2)^(s/2) ≤ Real.exp (s*|d|)*(1+x^2)^(s/2) := by
    calc
      _ ≤ (Real.exp (2*|d|) * (1+x^2))^(s/2) := Real.rpow_le_rpow (by positivity) hpoly (by positivity)
      _ = _ := by
        rw [Real.mul_rpow (Real.exp_pos _).le (by positivity), ← Real.exp_mul]
        congr 2
        ring
  have hx : Real.exp (2*α*|u|) ≤ Real.exp (2*α*|d|)*Real.exp (2*α*|x|) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    nlinarith [mul_le_mul_of_nonneg_left hsum (by linarith : 0 ≤ 2*α)]
  rw [density_symmetric hα, density_symmetric hα]
  calc
    _ ≤ (Real.exp (2*α*|d|)*Real.exp (2*α*|x|)) * (Real.exp (s*|d|)*(1+x^2)^(s/2)) :=
      mul_le_mul hx hp (Real.rpow_nonneg (by positivity) _) (by positivity)
    _ = _ := by
      rw [show (2*α+s)*|u-x| = 2*α*|d|+s*|d| by dsimp [d]; ring, Real.exp_add]
      ring

private theorem eEnergy_rep {I : Set ℝ} {w : ℝ → ℝ} (hw : Measurable w)
    (p : PositiveRealExponentialDecay I)
    (e : Lp ℂ 2 (volume.withDensity fun x ↦ ENNReal.ofReal (w x)))
    (he : (e : ℝ → ℂ) =ᵐ[volume] p.val) :
    eEnergy w p = ENNReal.ofReal (‖e‖ ^ 2) := by
  let ν := volume.withDensity fun x ↦ ENNReal.ofReal (w x)
  have h := (Lp.memLp e).integrable_norm_pow (by norm_num : 2 ≠ 0)
  have hi := ofReal_integral_eq_lintegral_ofReal h (Eventually.of_forall fun x ↦ sq_nonneg ‖e x‖)
  rw [L2.integral_sq_norm (𝕜 := ℂ)] at hi
  rw [hi, lintegral_withDensity_eq_lintegral_mul_non_measurable volume hw.ennreal_ofReal
    (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  apply lintegral_congr_ae
  filter_upwards [he] with x hx
  change _ = ENNReal.ofReal (w x) * ENNReal.ofReal (‖e x‖ ^ 2)
  rw [hx]


/-- Every contraction on the vertical test lines extends to the symmetric
Hardy–Sobolev space with a bound depending only on the widths and degree. -/
theorem scalar_sobolev_multiplier_extension {I : Set ℝ} (h0 : 0 ∈ I)
    {α s β : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (hβ : 2*α+s < 2*β)
    (hp : β ∈ I) (hm : -β ∈ I)
    (j : PositiveRealExponentialDecay I →L[ℂ] CompactIntervalSobolev volume id (-α) α s)
    (hd : DenseRange j) (hr : ∀ p, (j p : ℝ → ℂ) =ᵐ[volume] p.val) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : PositiveRealExponentialDecay I →ₗ[ℂ] PositiveRealExponentialDecay I),
      (∀ (v : I) (p : PositiveRealExponentialDecay I),
        ∫ x, Real.exp (2*v.val*x) * ‖(T p).val x‖^2 ≤ ∫ x, Real.exp (2*v.val*x) * ‖p.val x‖ ^ 2) →
      ∃ U : CompactIntervalSobolev volume id (-α) α s →L[ℂ] CompactIntervalSobolev volume id (-α) α s,
        ‖U‖ ≤ C ∧ ∀ p, U (j p) = j (T p) := by
  let w := intervalSobolevDensity (-α) α s
  let κ := 2*α+s
  let A := 2/(2*β + κ)
  let D := 2/(2*β - κ)
  let B := 2*(1+Real.exp (4*β))
  have hk : 0 ≤ κ := by dsimp [κ]; positivity
  have hab : κ < 2*β := hβ
  have hA : 0 < A := div_pos (by norm_num) (by linarith)
  have hD : 0 < D := div_pos (by norm_num) (sub_pos.mpr hab)
  have hB : 0 < B := by dsimp [B]; positivity
  have hc : Continuous w := by
    have hfun : w = fun x ↦ Real.exp (2*α*|x|)*(1+x^2)^(s/2) := funext (density_symmetric hα s)
    rw [hfun]
    exact Continuous.mul (by fun_prop) (Continuous.rpow_const (by fun_prop) (fun x ↦ Or.inl (by positivity)))
  let C := Real.sqrt ((B*D)/A)
  refine ⟨C, Real.sqrt_nonneg _, fun T ht ↦ ?_⟩
  have hbound (p : PositiveRealExponentialDecay I) : ‖j (T p)‖ ≤ C * ‖j p‖ := by
    have H := eEnergy_bound h0 hk hab hp hm w hc (density_translation hα hs) T ht p
    have rep (q : PositiveRealExponentialDecay I) :
        eEnergy w q = ENNReal.ofReal (‖j q‖^2) := eEnergy_rep hc.measurable q (j q) (hr q)
    change ENNReal.ofReal A * eEnergy w (T p) ≤ ENNReal.ofReal B * ENNReal.ofReal D * eEnergy w p at H
    rw [rep, rep, ← ENNReal.ofReal_mul hA.le, ← ENNReal.ofReal_mul hB.le,
      ← ENNReal.ofReal_mul (mul_nonneg hB.le hD.le)] at H
    have h := (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ B*D*‖j p‖^2)).mp H
    have hsq : ‖j (T p)‖^2 ≤ ((B*D)/A)*‖j p‖^2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hA]
      linarith only [h, mul_comm A (‖j (T p)‖ ^ 2)]
    calc
      _ = Real.sqrt (‖j (T p)‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (((B*D)/A)*‖j p‖^2) := Real.sqrt_le_sqrt hsq
      _ = _ := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _) ]
  let t := j.toLinearMap.comp T
  let U := t.extendOfNorm j.toLinearMap
  exact ⟨U, U.opNorm_le_bound (Real.sqrt_nonneg _) (LinearMap.norm_extendOfNorm_apply_le hd C hbound),
    LinearMap.extendOfNorm_eq hd ⟨C, hbound⟩⟩


end RiemannMasullo.StripMultiplier

noncomputable section
open Filter Function MeasureTheory Set
open scoped Topology

namespace RiemannMasullo.StripTailPhysical

/-- Pointwise convergence to zero under an L² envelope gives convergence in L². -/
theorem l2_dominated {X ι : Type*} [MeasurableSpace X] {μ : Measure X} {l : Filter ι}
    [l.IsCountablyGenerated] (u : ι → X → ℂ) (hu : ∀ n, MemLp (u n) 2 μ)
    (f : X → ℂ) (hf : MemLp f 2 μ) (hbound : ∀ n x, ‖u n x‖ ≤ 2 * ‖f x‖)
    (hlim : ∀ x, Tendsto (fun n ↦ u n x) l (𝓝 0)) :
    Tendsto (fun n ↦ (eLpNorm (u n) 2 μ).toReal) l (𝓝 0) := by
  let D (n : ι) (x : X) := ‖u n x‖ ^ 2
  have h : Tendsto (fun n ↦ ∫ x, D n x ∂μ) l (𝓝 (∫ _ : X, (0 : ℝ) ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun x ↦ 4 * ‖f x‖ ^ 2)
    · exact .of_forall fun n ↦ (hu n).aestronglyMeasurable.norm.pow 2
    · refine .of_forall fun n ↦ .of_forall fun x ↦ ?_
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      calc
        _ ≤ (2 * ‖f x‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hbound n x) _
        _ = _ := by ring
    · exact hf.norm.integrable_sq.const_mul 4
    · exact .of_forall fun x ↦ by simpa [D] using (hlim x).norm.pow 2
  have hs (n : ι) : ‖(hu n).toLp _‖ ^ 2 = ∫ x, D n x ∂μ := by
    rw [← L2.integral_sq_norm (𝕜 := ℂ)]
    exact integral_congr_ae ((hu n).coeFn_toLp.fun_comp fun t ↦ ‖t‖ ^ 2)
  simpa only [integral_zero, comp_def, ← hs, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero,
    Lp.norm_toLp, Real.sqrt_sq ENNReal.toReal_nonneg] using (Real.continuous_sqrt.tendsto _).comp h

/-- A bounded holomorphic multiplier preserves the entire family of substrip
bounds in the Schwartz–Bergman space. -/
theorem multiply_mem {I : Set ℝ} (H : SchwartzBergman I) (b : ℂ → ℂ)
    (hb : DifferentiableOn ℂ b (Complex.re ⁻¹' I)) (hc : ∀ z, z.re ∈ I → ‖b z‖ ≤ 1) :
    (fun z ↦ b z * H.val z) ∈ schwartzBergmanSubmodule I := by
  refine ⟨fun z hz ↦ ?_, hb.mul H.property.2.1, ?_⟩
  · exact (congrArg (b z * ·) (H.property.1 hz)).trans (mul_zero _)
  · intro a c hac hsub k
    obtain ⟨M, hM⟩ := H.property.2.2 a c hac hsub k
    refine ⟨M, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    change ‖z ^ k * (b z * H.val z)‖ ≤ M
    rw [mul_left_comm, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hc z (hsub hz))).trans (hM ⟨z, hz, rfl⟩)

/-- Multiplication by bounded, pointwise convergent analytic multipliers converges
in the full Schwartz–Bergman topology on the open strip. -/
theorem tendsto_multiply {I : Set ℝ} {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (H : SchwartzBergman I) (b : ι → ℂ → ℂ) (hb : ∀ n, DifferentiableOn ℂ (b n) (Complex.re ⁻¹' I))
    (hc : ∀ n z, z.re ∈ I → ‖b n z‖ ≤ 1)
    (hl : ∀ z, z.re ∈ I → Tendsto (fun n ↦ b n z) l (𝓝 1)) :
    let G (n : ι) : SchwartzBergman I := ⟨_, multiply_mem H (b n) (hb n) (hc n)⟩
    Tendsto G l (𝓝 H) := by
  intro G
  let P (i : I × ℕ) : Seminorm ℂ (schwartzBergmanSubmodule I) :=
    Seminorm.of (fun f ↦ (eLpNorm (weightedVerticalTrace i.1 i.2 f.val) 2 volume).toReal)
      (schwartzBergman_l2_seminorm I i).1 (schwartzBergman_l2_seminorm I i).2
  apply ((withGeneratingSeminorms_spec (schwartzBergmanSubmodule I) P).tendsto_nhds G H).mpr
  rintro ⟨a, k⟩ ε hε
  let z (t : ℝ) := (a.val : ℂ) + t * Complex.I
  have hz (t : ℝ) : (z t).re ∈ I := by simp [z]
  let F := weightedVerticalTrace a k H.val
  let U (n : ι) := weightedVerticalTrace a k (G n - H).val
  have hU (n : ι) (t : ℝ) : U n t = (b n (z t) - 1) * F t := by
    change (z t)^k * (b n (z t) * H.val (z t) - H.val (z t)) = (b n (z t) - 1) * ((z t)^k * H.val (z t))
    ring
  have hB (n : ι) (t : ℝ) : ‖U n t‖ ≤ 2 * ‖F t‖ := by
    rw [hU, norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    calc
      _ ≤ ‖b n (z t)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ 2 := by rw [norm_one]; linarith [hc n (z t) (hz t)]
  have ht (t : ℝ) : Tendsto (fun n ↦ U n t) l (𝓝 0) := by
    simp only [hU]
    simpa using ((hl (z t) (hz t)).sub_const (1 : ℂ)).mul_const (F t)
  have hx := l2_dominated U (fun n ↦ schwartzBergman_trace_memLp I a 2 (by norm_num)
    (by norm_num) k (G n - H)) F (schwartzBergman_trace_memLp I a 2 (by norm_num) (by norm_num) k H) hB ht
  exact hx.eventually (gt_mem_nhds hε)

end RiemannMasullo.StripTailPhysical

noncomputable section
open Filter Function MeasureTheory Set
open scoped Topology
namespace RiemannMasullo.StripMultiplier

private def multiplyTest {I : Set ℝ} (hI : IsOpen I) (hi : OrdConnected I) (hne : I.Nonempty)
    (b : ℂ → ℂ) (hb : DifferentiableOn ℂ b (Complex.re ⁻¹' I)) (hc : ∀ z, z.re ∈ I → ‖b z‖ ≤ 1) :
    PositiveRealExponentialDecay I →ₗ[ℂ] PositiveRealExponentialDecay I :=
  let M := positiveRealFourierMellin I hI hi hne
  let B : SchwartzBergman I →ₗ[ℂ] SchwartzBergman I :=
    { toFun := fun H ↦ ⟨_, StripTailPhysical.multiply_mem H b hb hc⟩
      map_add' := fun H K ↦ Subtype.ext (funext fun z ↦ mul_add (b z) (H.val z) (K.val z))
      map_smul' := fun c H ↦ Subtype.ext (funext fun z ↦ mul_left_comm (b z) c (H.val z)) }
  M.symm.toLinearMap.comp (B.comp M.toLinearMap)

private theorem multiplyTest_mellin {I : Set ℝ} (hI : IsOpen I) (hi : OrdConnected I) (hne : I.Nonempty)
    (b : ℂ → ℂ) (hb : DifferentiableOn ℂ b (Complex.re ⁻¹' I)) (hc : ∀ z, z.re ∈ I → ‖b z‖ ≤ 1)
    (p : PositiveRealExponentialDecay I) (z : ℂ) (hz : z.re ∈ I) :
    mellin (fun t ↦ (multiplyTest hI hi hne b hb hc p).val (Real.log t)) z =
      b z * mellin (fun t ↦ p.val (Real.log t)) z := by
  let M := positiveRealFourierMellin I hI hi hne
  let G : SchwartzBergman I := ⟨_, StripTailPhysical.multiply_mem (M p) b hb hc⟩
  change mellin (fun t ↦ (M.symm G).val (Real.log t)) z = _
  rw [← positiveRealFourierMellin_apply I hI hi hne (M.symm G) z hz]
  change (M (M.symm G)).val z = _
  rw [M.apply_symm_apply]
  exact congrArg (b z * ·) (positiveRealFourierMellin_apply I hI hi hne p z hz)

private theorem strong_limit_of_dense {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (j : X → E) (hd : DenseRange j) (l : Filter ι) (U : ι → E →L[ℂ] E)
    (C : ℝ) (hC : 0 ≤ C) (hu : ∀ n, ‖U n‖ ≤ C)
    (ht : ∀ p, Tendsto (fun n ↦ U n (j p)) l (𝓝 (j p))) (y : E) :
    Tendsto (fun n ↦ U n y) l (𝓝 y) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hc : 0 < C+1 := by linarith
  obtain ⟨p, hp⟩ := hd.exists_dist_lt y (div_pos (show 0 < ε/2 by positivity) hc)
  have h := (lt_div_iff₀ hc).mp hp
  filter_upwards [Metric.tendsto_nhds.mp (ht p) (ε/2) (by positivity)] with n hn
  have h1 : dist (U n y) (U n (j p)) ≤ C * dist y (j p) := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact ((U n).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hu n) (norm_nonneg _))
  have h2 := dist_triangle (U n y) (U n (j p)) y
  have h3 := dist_triangle (U n (j p)) (j p) y
  rw [dist_comm (j p) y] at h3
  nlinarith

/-- Contractive holomorphic multipliers on a wider vertical strip act uniformly
boundedly on the full Hardy–Sobolev norm. Pointwise convergence to one implies
strong convergence on that whole space. -/
theorem exists_sobolev_mellin_multiplier_family {I : Set ℝ} (hI : IsOpen I) (hi : OrdConnected I)
    (h0 : 0 ∈ I) {α s β : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (hβ : 2*α+s < 2*β)
    (hp : β ∈ I) (hm : -β ∈ I) (hsub : Icc (-α) α ⊆ I)
    {ι : Type*} (l : Filter ι) [l.IsCountablyGenerated] (b : ι → ℂ → ℂ)
    (hb : ∀ n, DifferentiableOn ℂ (b n) (Complex.re ⁻¹' I)) (hc : ∀ n z, z.re ∈ I → ‖b n z‖ ≤ 1)
    (hl : ∀ z, z.re ∈ I → Tendsto (fun n ↦ b n z) l (𝓝 1)) :
    let E := CompactIntervalSobolev volume id (-α) α s
    ∃ (j : PositiveRealExponentialDecay I →L[ℂ] E) (U : ι → E →L[ℂ] E) (C : ℝ),
      Injective j ∧ DenseRange j ∧ (∀ p, (j p : ℝ → ℂ) =ᵐ[volume] p.val) ∧
      (∀ n, ‖U n‖ ≤ C) ∧ (∀ y, Tendsto (fun n ↦ U n y) l (𝓝 y)) ∧
      ∀ p n, ∃ q : PositiveRealExponentialDecay I, U n (j p) = j q ∧
        ∀ z, z.re ∈ I → mellin (fun t ↦ q.val (Real.log t)) z =
          b n z * mellin (fun t ↦ p.val (Real.log t)) z := by
  intro E
  have hne : I.Nonempty := ⟨0,h0⟩
  let M := positiveRealFourierMellin I hI hi hne
  obtain ⟨j, hinj, hd, hr⟩ := scalarIntervalSobolev_dense (-α) α s (by linarith) hs I hI hi hsub
  obtain ⟨C, hC, H⟩ := scalar_sobolev_multiplier_extension h0 hα hs hβ hp hm j hd hr
  let T n := multiplyTest hI hi hne (b n) (hb n) (hc n)
  have hD (n : ι) (v : I) (p : PositiveRealExponentialDecay I) :
      ∫ x, Real.exp (2*v.val*x) * ‖(T n p).val x‖ ^ 2 ≤ ∫ x, Real.exp (2*v.val*x) * ‖p.val x‖ ^ 2 := by
    apply line_contraction
    intro t
    rw [multiplyTest_mellin hI hi hne (b n) (hb n) (hc n) p ⟨v,t⟩ v.property, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hc n _ v.property)
  choose U hu he using fun n ↦ H (T n) (hD n)
  refine ⟨j,U,C,hinj,hd,hr,hu, ?_, fun p n ↦ ⟨T n p, he n p, multiplyTest_mellin hI hi hne (b n) (hb n) (hc n) p⟩⟩
  apply strong_limit_of_dense j hd l U C hC hu
  intro p
  simp_rw [he]
  apply (j.continuous.tendsto p).comp
  let G n : SchwartzBergman I := ⟨_, StripTailPhysical.multiply_mem (M p) (b n) (hb n) (hc n)⟩
  have hg : Tendsto G l (𝓝 (M p)) := StripTailPhysical.tendsto_multiply (M p) b hb hc hl
  have hq := (M.symm.continuous.tendsto (M p)).comp hg
  rw [M.symm_apply_apply] at hq
  exact hq

end RiemannMasullo.StripMultiplier
#print axioms RiemannMasullo.StripMultiplier.exists_sobolev_mellin_multiplier_family
