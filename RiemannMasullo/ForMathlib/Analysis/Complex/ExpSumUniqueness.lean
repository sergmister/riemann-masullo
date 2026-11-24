module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Topology.Algebra.InfiniteSum.Defs

import RiemannMasullo.ForMathlib.Analysis.Fourier.PaleyWiener
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! # Uniqueness of coefficients of exponential sums on a half-line

An exponential sum with absolutely summable coefficients and distinct, locally finite
frequencies of bounded real part is `O(exp(a y))` on the positive ray precisely when
every frequency with nonzero coefficient lies in `Re w ≤ a`. In particular, vanishing
on the ray determines all coefficients. The Laplace transform continues the resolvent
through every frequency to the right of `a`, so that its residue there vanishes.
-/

public section

open Filter Topology Set MeasureTheory

namespace RiemannMasullo

/-- A set without accumulation points in `ℂ` is closed and countable. -/
private theorem expSum_range_closed_countable {ι : Type*} (w : ι → ℂ)
    (hdisc : ∀ z : ℂ, ∀ᶠ u in 𝓝[≠] z, u ∉ Set.range w) :
    IsClosed (range w) ∧ (range w).Countable := by
  have h : IsClosed (range w) ∧ IsDiscrete (range w) :=
    isClosed_and_discrete_iff.2 fun x => Filter.disjoint_principal_right.2 (hdisc x)
  exact ⟨h.1, h.1.isLindelof.countable_of_isDiscrete h.2⟩

private theorem expSum_norm_div_le {a x : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hx : ρ ≤ ‖x‖) :
    ‖a / x‖ ≤ ‖a‖ * (1 / ρ) := by
  rw [norm_div, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left (by rw [one_div]; exact inv_anti₀ hρ hx) (norm_nonneg _)

private theorem expSum_aux_dist {x z w : ℂ} {r : ℝ} (h1 : dist x z < r / 2) (h2 : r ≤ dist w z) :
    r / 2 ≤ ‖x - w‖ := by
  rw [← dist_eq_norm]
  have := dist_triangle w x z
  rw [dist_comm w x] at this
  linarith

/-- Above all the frequencies, the resolvent is the Laplace transform of the sum. -/
private theorem expSum_resolvent_eq_laplace {ι : Type*} [Countable ι] (w b : ι → ℂ)
    {M : ℝ} (hre : ∀ i, (w i).re ≤ M) (hb : Summable b) (z : ℂ) (hz : M < z.re) :
    ∑' i, b i / (z - w i) =
      ∫ y in Ioi (0 : ℝ), (∑' i, b i * Complex.exp (w i * y)) * Complex.exp (-z * y) := by
  set F : ι → ℝ → ℂ := fun i y => b i * Complex.exp ((w i - z) * y) with hF
  have hlt : ∀ i, (w i - z).re < 0 := fun i => by simp; linarith [hre i]
  have hint : ∀ i, Integrable (F i) (volume.restrict (Ioi 0)) := fun i =>
    (integrableOn_exp_mul_complex_Ioi (hlt i) 0).const_mul (b i)
  have hval : ∀ i, ∫ y in Ioi (0 : ℝ), F i y = b i / (z - w i) := by
    intro i
    simp only [F]
    rw [integral_const_mul, integral_exp_mul_complex_Ioi (hlt i)]
    have h1 : w i - z ≠ 0 := fun h0 => by have := hlt i; rw [h0] at this; simp at this
    have h2 : z - w i ≠ 0 := fun h0 => h1 (by rw [← neg_sub, h0, neg_zero])
    field_simp
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    ring
  have hnorm : ∀ i, ∫ y in Ioi (0 : ℝ), ‖F i y‖ = ‖b i‖ * (1 / (z.re - (w i).re)) := by
    intro i
    have : ∀ y : ℝ, ‖F i y‖ = ‖b i‖ * Real.exp ((w i - z).re * y) := by
      intro y; simp [F, Complex.norm_exp]
    simp_rw [this]
    rw [integral_const_mul, integral_exp_mul_Ioi (hlt i)]
    congr 1
    simp only [mul_zero, Real.exp_zero, Complex.sub_re]
    rw [neg_div, ← div_neg, neg_sub]
  have hsum : Summable fun i => ∫ y in Ioi (0 : ℝ), ‖F i y‖ := by
    simp_rw [hnorm]
    refine (hb.norm.mul_right (1 / (z.re - M))).of_nonneg_of_le (fun i => ?_) (fun i => ?_)
    · have := hre i
      exact mul_nonneg (norm_nonneg _) (by rw [one_div]; exact inv_nonneg.2 (by linarith))
    · have := hre i
      gcongr
  have key := integral_tsum_of_summable_integral_norm hint hsum
  simp_rw [hval] at key
  rw [key]
  refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
  have he (i) : F i y = (b i * Complex.exp (w i * y)) * Complex.exp (-z * y) := by
    simp only [F, sub_eq_add_neg, add_mul, Complex.exp_add, neg_mul]
    ring
  simp_rw [he, tsum_mul_right]

/-- A vanishing exponential sum has zero resolvent above its frequencies. -/
private theorem expSum_resolvent_eq_zero {ι : Type*} [Countable ι] (w b : ι → ℂ)
    (hre : ∀ i, (w i).re ≤ 1 / 2) (hb : Summable b)
    (h : ∀ y : ℝ, 0 ≤ y → HasSum (fun i ↦ b i * Complex.exp (w i * y)) 0)
    (z : ℂ) (hz : 1 / 2 < z.re) : ∑' i, b i / (z - w i) = 0 := by
  rw [expSum_resolvent_eq_laplace w b hre hb z hz]
  exact setIntegral_eq_zero_of_forall_eq_zero fun y hy ↦ by rw [(h y (le_of_lt hy)).tsum_eq, zero_mul]

/-- The resolvent sum is holomorphic off the (closed) range of `w`. -/
private theorem expSum_resolvent_differentiableOn {ι : Type*} (w b : ι → ℂ) (hb : Summable b)
    (hcl : IsClosed (range w)) :
    DifferentiableOn ℂ (fun z => ∑' i, b i / (z - w i)) (range w)ᶜ := by
  intro z hz
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hcl.isOpen_compl z hz
  have hfar : ∀ i, r ≤ dist (w i) z := fun i => by
    by_contra hcon
    exact hball (Metric.mem_ball.2 (not_le.1 hcon)) ⟨i, rfl⟩
  have hd : DifferentiableOn ℂ (fun z => ∑' i, b i / (z - w i)) (Metric.ball z (r / 2)) := by
    refine Complex.differentiableOn_tsum_of_summable_norm
      (F := fun i x => b i / (x - w i)) (u := fun i => ‖b i‖ * (1 / (r / 2)))
      (hb.norm.mul_right _) (fun i => ?_) Metric.isOpen_ball (fun i x hx => ?_)
    · have hne : ∀ x ∈ Metric.ball z (r / 2), x - w i ≠ 0 := fun x hx h0 => by
        have := expSum_aux_dist (Metric.mem_ball.1 hx) (hfar i)
        rw [h0, norm_zero] at this
        linarith
      exact (differentiableOn_const (b i)).div (differentiableOn_id.sub_const (w i)) hne
    · exact expSum_norm_div_le (by linarith) (expSum_aux_dist (Metric.mem_ball.1 hx) (hfar i))
  exact (hd.differentiableAt (Metric.ball_mem_nhds z (by linarith))).differentiableWithinAt

/-- Removing a countable set from an open right half-plane leaves it connected. -/
private theorem expSum_preconnected_halfPlane_diff (a : ℝ) {s : Set ℂ} (hs : s.Countable) :
    IsPreconnected ({z : ℂ | a < z.re} \ s) := by
  let e (u : ℂ) : ℂ := ⟨a + Real.exp u.re, u.im⟩
  have he : Continuous e := by
    simp only [e, Complex.mk_eq_add_mul_I]
    fun_prop
  have hi : Function.Injective e := by
    intro u v h
    have hr := congrArg Complex.re h
    have hm := congrArg Complex.im h
    exact Complex.ext (Real.exp_injective (add_left_cancel (show a + _ = a + _ from hr))) hm
  have him : e '' (e ⁻¹' s)ᶜ = {z : ℂ | a < z.re} \ s := by
    ext z
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨lt_add_of_pos_right _ (Real.exp_pos _), hu⟩
    · rintro ⟨hz, hzs⟩
      let u : ℂ := ⟨Real.log (z.re - a), z.im⟩
      have hez : e u = z := by
        refine Complex.ext ?_ rfl
        change a + Real.exp (Real.log (z.re - a)) = z.re
        rw [Real.exp_log (sub_pos.mpr hz)]
        ring
      exact ⟨u, fun hu ↦ hzs (hez ▸ hu), hez⟩
  rw [← him]
  exact ((hs.preimage hi).isConnected_compl_of_one_lt_rank
    (by simp [Complex.rank_real_complex])).isPreconnected.image e he.continuousOn

/-- A holomorphic continuation of the resolvent across a frequency forces its residue to
vanish. Agreement sufficiently far to the right identifies the continuation uniquely. -/
private theorem expSum_coeff_eq_zero_of_continuation {ι : Type*} (w b : ι → ℂ)
    (hw : Function.Injective w) (hdisc : ∀ z : ℂ, ∀ᶠ u in 𝓝[≠] z, u ∉ range w)
    {M a : ℝ} (hre : ∀ i, (w i).re ≤ M) (hb : Summable b) (L : ℂ → ℂ)
    (hL : DifferentiableOn ℂ L {z : ℂ | a < z.re})
    (hfar : ∀ z : ℂ, max M a < z.re → ∑' i, b i / (z - w i) = L z)
    (i : ι) (hi : a < (w i).re) : b i = 0 := by
  classical
  obtain ⟨hcl, hc⟩ := expSum_range_closed_countable w hdisc
  let R (z : ℂ) := ∑' j, b j / (z - w j)
  let U := {z : ℂ | a < z.re} \ range w
  have hop : IsOpen {z : ℂ | a < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have har : AnalyticOnNhd ℂ R U :=
    ((expSum_resolvent_differentiableOn w b hb hcl).analyticOnNhd hcl.isOpen_compl).mono
      fun _ hz ↦ hz.2
  let z₀ : ℂ := (max M a + 1 : ℝ)
  have hright : max M a < z₀.re := by simp [z₀]
  have hz₀ : z₀ ∈ U := by
    refine ⟨(le_max_right _ _).trans_lt hright, ?_⟩
    rintro ⟨j, hj⟩
    exact (not_lt_of_ge ((hre j).trans (le_max_left _ _))) (hj ▸ hright)
  have heq : EqOn R L U := har.eqOn_of_preconnected_of_eventuallyEq
    ((hL.analyticOnNhd hop).mono fun _ hz ↦ hz.1) (expSum_preconnected_halfPlane_diff a hc)
    hz₀ (Filter.mem_of_superset ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hright)
      (fun z hz ↦ hfar z hz))
  let J := {j : ι // j ∉ ({i} : Finset ι)}
  let w' (j : J) := w j.val
  let b' (j : J) := b j.val
  have hd' (z : ℂ) : ∀ᶠ u in 𝓝[≠] z, u ∉ range w' :=
    (hdisc z).mono fun _ hu ⟨j, hj⟩ ↦ hu ⟨j.val, hj⟩
  have hc' := (expSum_range_closed_countable w' hd').1
  have hwi : w i ∈ (range w')ᶜ := by rintro ⟨j, hj⟩; exact j.property (Finset.mem_singleton.mpr (hw hj))
  let R' (z : ℂ) := ∑' j, b' j / (z - w' j)
  have hR' : ContinuousAt R' (w i) :=
    ((expSum_resolvent_differentiableOn w' b' (hb.subtype _) hc').differentiableAt
      (hc'.isOpen_compl.mem_nhds hwi)).continuousAt
  have hder : ContinuousAt (fun z : ℂ ↦ (z - w i) * (L z - R' z)) (w i) :=
    (continuousAt_id.sub continuousAt_const).mul
      ((hL.differentiableAt (hop.mem_nhds hi)).continuousAt.sub hR')
  have hlim := hder.tendsto.mono_left (nhdsWithin_le_nhds (s := {w i}ᶜ))
  have hres : ∀ᶠ z in 𝓝[≠] (w i), (z - w i) * (L z - R' z) = b i := by
    filter_upwards [hdisc (w i), Filter.Eventually.filter_mono nhdsWithin_le_nhds (hop.mem_nhds hi)] with z hz hza
    have hzwi : z - w i ≠ 0 := sub_ne_zero.mpr fun h ↦ hz ⟨i, h.symm⟩
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hcl.isOpen_compl z hz
    have hs : Summable fun j ↦ b j / (z - w j) := by
      refine Summable.of_norm_bounded (hb.norm.mul_right (1 / r)) fun j ↦ expSum_norm_div_le hr ?_
      rw [← dist_eq_norm, dist_comm]
      exact le_of_not_gt fun h ↦ hball (Metric.mem_ball.2 h) ⟨j, rfl⟩
    have hsplit := hs.sum_add_tsum_subtype_compl {i}
    have hsplit' : b i / (z - w i) + R' z = R z := by
      simpa [R', b', w', J, R] using hsplit
    rw [← heq ⟨hza, hz⟩, ← hsplit', add_sub_cancel_right, mul_div_cancel₀ _ hzwi]
  have := tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hres.mono fun _ hz ↦ hz.symm))
  simpa using this.symm

private theorem expSum_continuous_on_ray {ι : Type*} (w b : ι → ℂ) {M : ℝ}
    (hre : ∀ i, (w i).re ≤ M) (hb : Summable b) :
    Continuous fun y : ℝ ↦ ∑' i, b i * Complex.exp (w i * (max y 0 : ℝ)) := by
  let v (i : ι) (y : ℝ) := b i * Complex.exp ((w i - (M : ℂ)) * (max y 0 : ℝ))
  have hv : Continuous fun y ↦ ∑' i, v i y := by
    refine continuous_tsum (fun i ↦ by dsimp [v]; fun_prop) hb.norm fun i y ↦ ?_
    have he : ((w i).re - M) * max y 0 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hre i)) (le_max_right _ _)
    simpa [v, Complex.norm_exp] using
      (mul_le_of_le_one_right (norm_nonneg (b i)) (Real.exp_le_one_iff.mpr he))
  have heq (y : ℝ) : ∑' i, b i * Complex.exp (w i * (max y 0 : ℝ)) =
      (∑' i, v i y) * Complex.exp ((M : ℂ) * (max y 0 : ℝ)) := by
    rw [← tsum_mul_right]
    apply tsum_congr
    intro i
    simp only [v, mul_assoc, ← Complex.exp_add, ← add_mul, sub_add_cancel]
  simp_rw [heq]
  exact hv.mul (by fun_prop)

/-- For a continuous function an eventual exponential estimate extends, with a new
constant, over the bounded initial segment of the positive ray. -/
private theorem expSum_growth_on_ray {f : ℝ → ℂ} (hf : Continuous f) {a : ℝ}
    (h : f =O[atTop] (fun y : ℝ ↦ Real.exp (a * y))) :
    ∃ C : ℝ, ∀ y : ℝ, 0 < y → ‖f y‖ ≤ C * Real.exp (a * y) := by
  obtain ⟨c, htop⟩ := Asymptotics.isBigO_iff.mp h
  obtain ⟨Y, hY⟩ := eventually_atTop.1 htop
  have hcont : Continuous fun y : ℝ ↦ ‖f y‖ / Real.exp (a * y) :=
    hf.norm.div (by fun_prop) fun _ ↦ (Real.exp_pos _).ne'
  obtain ⟨d, hd⟩ := isCompact_Icc.bddAbove_image (K := Icc (0 : ℝ) Y) hcont.continuousOn
  refine ⟨max c d, fun y hy ↦ ?_⟩
  by_cases h : Y ≤ y
  · exact (by simpa only [Real.norm_of_nonneg (Real.exp_pos _).le] using hY y h :
      ‖f y‖ ≤ c * Real.exp (a * y)).trans (by gcongr; exact le_max_left _ _)
  · apply (div_le_iff₀ (Real.exp_pos _)).mp
    exact (hd (mem_image_of_mem _ ⟨hy.le, le_of_not_ge h⟩)).trans (le_max_right _ _)

/-- A translated exponential sum is `O(exp(a y))` at positive infinity precisely when every
frequency with nonzero coefficient has real part at most `a`. The frequencies are distinct
and locally finite in the plane, their real parts are bounded above, and the coefficients are
absolutely summable. The estimate allows nonzero coefficients on the boundary `Re w = a`. -/
theorem expSum_isBigO_iff {ι : Type*} (w b : ι → ℂ) (hw : Function.Injective w)
    (hdisc : ∀ z : ℂ, ∀ᶠ u in 𝓝[≠] z, u ∉ range w)
    {M : ℝ} (hre : ∀ i, (w i).re ≤ M) (hb : Summable b) (a : ℝ) :
    ((fun y : ℝ ↦ ∑' i, b i * Complex.exp (w i * y)) =O[atTop]
      (fun y : ℝ ↦ Real.exp (a * y))) ↔ ∀ i, b i ≠ 0 → (w i).re ≤ a := by
  classical
  constructor
  · intro h
    have hc := (expSum_range_closed_countable w hdisc).2.to_subtype
    have : Countable ι := Function.Injective.countable
      (f := fun i ↦ (⟨w i, i, rfl⟩ : range w)) fun _ _ he ↦ hw (congrArg Subtype.val he)
    let f (y : ℝ) := ∑' i, b i * Complex.exp (w i * (max y 0 : ℝ))
    have hf := expSum_continuous_on_ray w b hre hb
    have hg : f =O[atTop] (fun y : ℝ ↦ Real.exp (a * y)) := by
      refine h.congr' ?_ (by rfl)
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
      simp [f, max_eq_left hy]
    obtain ⟨C, hC⟩ := expSum_growth_on_ray hf hg
    let L (z : ℂ) := ∫ y in Ioi (0 : ℝ), f y * Complex.exp (-z * y)
    have hL : DifferentiableOn ℂ L {z : ℂ | a < z.re} := fun z hz ↦
      (differentiableAt_halfLaplace_of_exp_bound hf hC hz).differentiableWithinAt
    have heq (z : ℂ) (hz : max M a < z.re) : ∑' i, b i / (z - w i) = L z := by
      rw [expSum_resolvent_eq_laplace w b hre hb z ((le_max_left _ _).trans_lt hz)]
      exact setIntegral_congr_fun measurableSet_Ioi fun y hy ↦ by simp [f, max_eq_left (le_of_lt hy)]
    intro i hi
    exact le_of_not_gt fun he ↦ hi (expSum_coeff_eq_zero_of_continuation w b hw hdisc hre hb L hL heq i he)
  · intro h
    refine Asymptotics.isBigO_iff.mpr ⟨∑' i, ‖b i‖, ?_⟩
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, ← tsum_mul_right]
    apply tsum_of_norm_bounded (hb.norm.mul_right _).hasSum
    intro i
    by_cases hi : b i = 0
    · simp [hi]
    · simp only [norm_mul, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero]
      gcongr
      exact h i hi

/-- Uniqueness of coefficients of an exponential sum on a half-line. Let the frequencies `w i`
be distinct, have no accumulation point in `ℂ`, and satisfy `Re (w i) ≤ 1/2`. If the
coefficients `b` are summable and `∑ i, b i * exp (w i * y) = 0` for every `y ≥ 0`, then every
`b i` is zero. The proof takes a Laplace transform for `Re z > 1/2`, which gives
`∑ i, b i / (z - w i) = 0`, extends this to the complement of the frequencies by the identity
theorem, and lets `z` tend to each frequency. -/
theorem eq_zero_of_hasSum_exp_eq_zero {ι : Type*} (w : ι → ℂ) (b : ι → ℂ)
    (hw : Function.Injective w)
    (hdisc : ∀ z : ℂ, ∀ᶠ u in nhdsWithin z {z}ᶜ, u ∉ Set.range w)
    (hre : ∀ i, (w i).re ≤ 1 / 2)
    (hb : Summable b)
    (h : ∀ y : ℝ, 0 ≤ y → HasSum (fun i ↦ b i * Complex.exp (w i * y)) 0) :
    ∀ i, b i = 0 := by
  classical
  have hc := (expSum_range_closed_countable w hdisc).2.to_subtype
  have : Countable ι := Function.Injective.countable
    (f := fun i ↦ (⟨w i, i, rfl⟩ : range w)) fun _ _ he ↦ hw (congrArg Subtype.val he)
  intro i
  exact expSum_coeff_eq_zero_of_continuation w b hw hdisc (a := (w i).re - 1) hre hb
    (fun _ ↦ 0) (differentiableOn_const 0) (fun z hz ↦
      expSum_resolvent_eq_zero w b hre hb h z ((le_max_left _ _).trans_lt hz)) i (by linarith)

end RiemannMasullo
