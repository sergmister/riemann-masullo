module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Topology.Algebra.InfiniteSum.Defs

import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! # Uniqueness of coefficients of exponential sums on a half-line

If `∑ i, b i * exp (w i * y) = 0` for every `y ≥ 0`, where the frequencies `w i` are distinct,
have no accumulation point in `ℂ` and real parts at most `1/2`, and the coefficients are
summable, then every coefficient vanishes.
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

/-- Laplace transform step: the resolvent sum vanishes on `Re z > 1/2`. -/
private theorem expSum_resolvent_eq_zero {ι : Type*} [Countable ι] (w b : ι → ℂ)
    (hre : ∀ i, (w i).re ≤ 1 / 2) (hb : Summable b)
    (h : ∀ y : ℝ, 0 ≤ y → HasSum (fun i ↦ b i * Complex.exp (w i * y)) 0)
    (z : ℂ) (hz : 1 / 2 < z.re) :
    ∑' i, b i / (z - w i) = 0 := by
  set F : ι → ℝ → ℂ := fun i y => b i * Complex.exp ((w i - z) * y) with hF
  have hlt : ∀ i, (w i - z).re < 0 := fun i => by simp; linarith [hre i]
  have hint : ∀ i, Integrable (F i) (volume.restrict (Ioi 0)) := fun i =>
    (integrableOn_exp_mul_complex_Ioi (hlt i) 0).const_mul (b i)
  have hval : ∀ i, ∫ y in Ioi (0:ℝ), F i y = b i / (z - w i) := by
    intro i
    simp only [F]
    rw [integral_const_mul, integral_exp_mul_complex_Ioi (hlt i)]
    have h1 : w i - z ≠ 0 := fun h0 => by have := hlt i; rw [h0] at this; simp at this
    have h2 : z - w i ≠ 0 := fun h0 => h1 (by rw [← neg_sub, h0, neg_zero])
    field_simp
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    ring
  have hnorm : ∀ i, ∫ y in Ioi (0:ℝ), ‖F i y‖ = ‖b i‖ * (1 / (z.re - (w i).re)) := by
    intro i
    have : ∀ y : ℝ, ‖F i y‖ = ‖b i‖ * Real.exp ((w i - z).re * y) := by
      intro y; simp [F, Complex.norm_exp]
    simp_rw [this]
    rw [integral_const_mul, integral_exp_mul_Ioi (hlt i)]
    congr 1
    simp only [mul_zero, Real.exp_zero, Complex.sub_re]
    rw [neg_div, ← div_neg, neg_sub]
  have hsum : Summable fun i => ∫ y in Ioi (0:ℝ), ‖F i y‖ := by
    simp_rw [hnorm]
    refine (hb.norm.mul_right (1 / (z.re - 1 / 2))).of_nonneg_of_le (fun i => ?_) (fun i => ?_)
    · have := hre i
      exact mul_nonneg (norm_nonneg _) (by rw [one_div]; exact inv_nonneg.2 (by linarith))
    · have := hre i
      gcongr
  have key := integral_tsum_of_summable_integral_norm hint hsum
  simp_rw [hval] at key
  rw [key]
  refine setIntegral_eq_zero_of_forall_eq_zero fun y hy => ?_
  have : ∀ i, F i y = Complex.exp (-z * y) * (b i * Complex.exp (w i * y)) := by
    intro i
    simp only [F, sub_eq_add_neg, add_mul, Complex.exp_add, neg_mul]
    ring
  simp_rw [this, tsum_mul_left, (h y (le_of_lt hy)).tsum_eq, mul_zero]

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
  obtain ⟨hcl, hcount⟩ := expSum_range_closed_countable w hdisc
  have hre' : ∀ i, (w i).re ≤ 1 / 2 := hre
  have : Countable ι := by
    have := hcount.to_subtype
    exact Function.Injective.countable (f := fun i => (⟨w i, i, rfl⟩ : range w))
      fun a b hab => hw (congrArg Subtype.val hab)
  set R : ℂ → ℂ := fun z => ∑' i, b i / (z - w i) with hR
  have hU : IsPreconnected (range w)ᶜ :=
    (hcount.isConnected_compl_of_one_lt_rank (by simp [Complex.rank_real_complex])).isPreconnected
  have han : AnalyticOnNhd ℂ R (range w)ᶜ :=
    (expSum_resolvent_differentiableOn w b hb hcl).analyticOnNhd hcl.isOpen_compl
  have h1 : (1 : ℂ) ∈ (range w)ᶜ := by
    rintro ⟨i, hi⟩
    have := hre' i
    rw [hi] at this
    norm_num at this
  have hev : ∀ᶠ z in 𝓝 (1 : ℂ), R z = 0 := by
    have hopen : IsOpen {z : ℂ | 1 / 2 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (by norm_num : (1 : ℂ) ∈ {z : ℂ | 1 / 2 < z.re})] with z hz
    exact expSum_resolvent_eq_zero w b hre' hb h z hz
  have hzero := han.eqOn_zero_of_preconnected_of_frequently_eq_zero hU h1
    (hev.filter_mono nhdsWithin_le_nhds).frequently
  intro i₀
  obtain ⟨ε, hε, hεball⟩ := Metric.eventually_nhds_iff.1
    (eventually_nhdsWithin_iff.1 (hdisc (w i₀)))
  have hfar : ∀ i, i ≠ i₀ → ε ≤ dist (w i) (w i₀) := fun i hi => by
    by_contra hcon
    exact hεball (not_le.1 hcon) (fun h0 => hi (hw h0)) ⟨i, rfl⟩
  set C := (∑' i, ‖b i‖) * (1 / (ε / 2)) with hC
  have hbound : ∀ δ : ℝ, δ ∈ Ioo 0 (ε / 2) → ‖b i₀‖ ≤ δ * C := by
    rintro δ ⟨hδ0, hδε⟩
    set z : ℂ := w i₀ + δ with hz
    have hzw : z - w i₀ = δ := by rw [hz]; ring
    have hdist : dist z (w i₀) = δ := by
      rw [dist_eq_norm, hzw, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ0]
    have hzU : z ∈ (range w)ᶜ :=
      hεball (by rw [hdist]; linarith) (fun h0 => by
        rw [h0, dist_self] at hdist; linarith)
    have hRz : R z = 0 := hzero hzU
    have hfar' : ∀ i, i ≠ i₀ → ε / 2 ≤ ‖z - w i‖ := fun i hi => by
      have := hfar i hi
      have := expSum_aux_dist (x := z) (z := w i₀) (w := w i) (r := ε) (by rw [hdist]; linarith) this
      exact this
    have hsumm : Summable fun i => b i / (z - w i) := by
      refine Summable.of_norm_bounded (g := fun i => ‖b i‖ * (1 / δ)) (hb.norm.mul_right _)
        fun i => ?_
      by_cases hi : i = i₀
      · subst hi
        exact expSum_norm_div_le hδ0 (by rw [hzw, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ0])
      · exact expSum_norm_div_le hδ0 (by linarith [hfar' i hi])
    have hsplit := hsumm.tsum_eq_add_tsum_ite i₀
    have hS : ‖∑' i, if i = i₀ then 0 else b i / (z - w i)‖ ≤ C := by
      rw [hC, ← tsum_mul_right]
      refine tsum_of_norm_bounded (hb.norm.mul_right (1 / (ε / 2))).hasSum fun i => ?_
      · by_cases hi : i = i₀
        · simp only [hi, ite_true, norm_zero]
          exact mul_nonneg (norm_nonneg _) (by positivity)
        · simp only [hi, ite_false]
          exact expSum_norm_div_le (by linarith) (hfar' i hi)
    have h0 : b i₀ / (z - w i₀) = -∑' i, if i = i₀ then 0 else b i / (z - w i) := by
      have : R z = ∑' i, b i / (z - w i) := rfl
      rw [hRz, hsplit] at this
      linear_combination -this
    have hn : ‖b i₀‖ / δ ≤ C := by
      have := congrArg norm h0
      rw [norm_neg, norm_div, hzw, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ0] at this
      rw [this]; exact hS
    rw [div_le_iff₀ hδ0] at hn
    linarith
  have hlim : Tendsto (fun δ : ℝ => δ * C) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun δ : ℝ => δ * C) (𝓝 0) (𝓝 (0 * C)) :=
      (continuous_id.mul continuous_const).tendsto 0
    rw [zero_mul] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hle : ‖b i₀‖ ≤ 0 :=
    ge_of_tendsto hlim (Filter.mem_of_superset (Ioo_mem_nhdsGT (half_pos hε))
      fun δ hδ => hbound δ hδ)
  exact norm_le_zero_iff.1 hle

end RiemannMasullo
