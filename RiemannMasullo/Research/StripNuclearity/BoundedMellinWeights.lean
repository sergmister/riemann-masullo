module

public import RiemannMasullo.Research.StripNuclearity.RationalZeroWindow
import Mathlib.Analysis.Normed.Group.Tannery

/-! # Two positive translates that remove one Mellin frequency

A probability measure on zero and a positive shift kills the exponential
at a prescribed nonreal frequency. Absolute summability permits passing
from finite products of these filters to an individual coefficient.
-/

@[expose] public noncomputable section

open Filter Finset Function MeasureTheory Set
open scoped BigOperators Topology
namespace RiemannMasullo.StripNuclearity

/-- There are two positive weights of total mass one whose exponential
moment vanishes at any frequency with nonzero imaginary part. The second
atom is at distance π divided by the absolute imaginary part. -/
theorem exists_positive_mellin_killing_weight (w : ℂ) (hw : w.im ≠ 0) :
    ∃ p : ℝ, 0 ≤ p ∧ p ≤ 1 ∧ (p : ℂ) + (1-p : ℂ) *
      Complex.exp (w * ((Real.pi / |w.im| : ℝ) : ℂ)) = 0 := by
  let h := Real.pi / |w.im|
  let t := Real.exp (w.re*h)
  have ht : 0 < t := Real.exp_pos _
  have he : Complex.exp (w * (h : ℂ)) = -(t : ℂ) := by
    rw [Complex.exp_eq_exp_re_mul_sin_add_cos]
    have hi : w.im * h = Real.pi ∨ w.im * h = -Real.pi := by
      rcases lt_or_gt_of_ne hw with hw | hw
      · right
        dsimp only [h]
        rw [abs_of_neg hw]
        field_simp
      · left
        dsimp only [h]
        rw [abs_of_pos hw]
        field_simp
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, zero_add, sub_zero]
    rcases hi with hi | hi <;> simp [hi,t]
  refine ⟨t/(1+t), by positivity, (div_le_one (by positivity)).mpr (by linarith), ?_⟩
  change _ + _ * Complex.exp (w*(h:ℂ)) = _
  rw [he]
  have hden : (1 + (t : ℂ)) ≠ 0 := by exact_mod_cast (show 1+t ≠ 0 by positivity)
  push_cast
  field_simp
  ring

/-- On a strip with upper real bound one, each normalized two-point
filter has norm at most the exponential of its shift. -/
theorem norm_mellin_two_point_le (w : ℂ) (hw : w.re ≤ 1) {h p : ℝ}
    (hh : 0 ≤ h) (hp : 0 ≤ p) (hp' : p ≤ 1) :
    ‖(p : ℂ) + (1-p : ℂ) * Complex.exp (w*h)‖ ≤ Real.exp h := by
  have hE : 1 ≤ Real.exp h := Real.one_le_exp_iff.mpr hh
  have hx : ‖Complex.exp (w*(h:ℂ))‖ ≤ Real.exp h := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simpa using mul_le_mul_of_nonneg_right hw hh
  calc
    _ ≤ ‖(p:ℂ)‖ + ‖(1-p:ℂ) * Complex.exp (w*h)‖ := norm_add_le _ _
    _ = p + (1-p) * ‖Complex.exp (w*h)‖ := by
      rw [norm_mul, show (1-p:ℂ) = ((1-p:ℝ):ℂ) by push_cast; rfl]
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp, abs_of_nonneg (sub_nonneg.mpr hp')]
    _ ≤ p * Real.exp h + (1-p)*Real.exp h := by
      gcongr
      simpa using mul_le_mul_of_nonneg_left hE hp
    _ = _ := by ring

/-- If finite test filters kill arbitrary finite sets of competing terms,
retain the target, and have a common bound, an absolutely summable zero
distribution has zero coefficient at the target. -/
theorem coeff_eq_zero_of_bounded_finite_filters {ι : Type*} (i₀ : ι) (a : ι → ℂ)
    (hs : Summable (fun i ↦ ‖a i‖)) (C : ℝ)
    (h : ∀ T : Finset ι, ∃ k : ι → ℂ, k i₀ = 1 ∧ (∀ i ∈ T, i ≠ i₀ → a i * k i = 0) ∧
      (∀ i, ‖k i‖ ≤ C) ∧ HasSum (fun i ↦ a i * k i) 0) : a i₀ = 0 := by
  classical
  choose k hk hkill hbound hzero using h
  let v (i : ι) := if i = i₀ then a i₀ else 0
  have hp (i : ι) : Tendsto (fun T : Finset ι ↦ a i * k T i) atTop (𝓝 (v i)) := by
    apply tendsto_nhds_of_eventually_eq
    by_cases he : i = i₀
    · subst i
      exact .of_forall fun T ↦ by simp [hk, v]
    · filter_upwards [eventually_ge_atTop ({i} : Finset ι)] with T ht
      simpa [v, he] using hkill T i (ht (mem_singleton_self i)) he
  have ht := tendsto_tsum_of_dominated_convergence (hs.mul_right C) hp
    (.of_forall fun T i ↦ (norm_mul (a i) (k T i)).le.trans
      (mul_le_mul_of_nonneg_left (hbound T i) (norm_nonneg _)))
  have hz : (∑' i, v i) = 0 := tendsto_nhds_unique ht
    (tendsto_const_nhds.congr (fun T ↦ (hzero T).tsum_eq.symm))
  simpa [v] using hz

/-- For reciprocal-summable ordinates, a finite exceptional set leaves
nonreal competitors whose total positive killing shifts are as small as
prescribed. This is the zero-density input needed by bounded windows. -/
theorem exists_small_mellin_shift_tail {ι : Type*} (u : ι → ℝ)
    (hu : Summable (fun j ↦ 1/(1+|u j|))) (ε : ℝ) (hε : 0 < ε) :
    ∃ E : Finset ι, (∀ j ∉ E, u j ≠ 0) ∧
      ∀ T : Finset ι, (∀ j ∈ T, j ∉ E) → (∑ j ∈ T, Real.pi/|u j|) ≤ ε := by
  classical
  let v (j : ι) := 1/(1+|u j|)
  have hv (j : ι) : 0 ≤ v j := by dsimp [v]; positivity
  let δ := min (1/2 : ℝ) (ε/(2*Real.pi))
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  obtain ⟨E,hE⟩ := ((tendsto_order.1 (tendsto_tsum_compl_atTop_zero v)).2 δ hδ).exists
  have hbig (j : ι) (hj : j ∉ E) : 1 < |u j| := by
    have hb : v j ≤ ∑' k : {k // k ∉ E}, v k.val :=
      (hu.subtype _).le_tsum ⟨j,hj⟩ (fun k _ ↦ hv k.val)
    have hhalf := (hb.trans_lt hE).trans_le (min_le_left _ _)
    change 1/(1+|u j|) < 1/2 at hhalf
    have he := (div_lt_iff₀ (show 0 < 1+|u j| by positivity)).mp hhalf
    linarith
  refine ⟨E, fun j hj ↦ abs_pos.mp (zero_lt_one.trans (hbig j hj)), fun T hT ↦ ?_⟩
  · let e : {j // j ∈ T} ↪ {j // j ∉ E} :=
      ⟨fun j ↦ ⟨j.val,hT j.val j.property⟩, fun _ _ h ↦ Subtype.ext (congrArg (fun y : {j // j ∉ E} ↦ y.val) h)⟩
    have hs : (∑ j ∈ T, v j) ≤ ∑' k : {k // k ∉ E}, v k.val := by
      calc _ = ∑ j ∈ T.attach.map e, v j.val := by
             rw [Finset.sum_map]
             change _ = ∑ j ∈ T.attach, v j.val
             exact (Finset.sum_attach T v).symm
           _ ≤ _ := (hu.subtype _).sum_le_tsum _ (fun j _ ↦ hv j.val)
    calc
      _ ≤ ∑ j ∈ T, (2*Real.pi)*v j := by
        apply sum_le_sum fun j hj ↦ ?_
        have hgt := hbig j (hT j hj)
        calc
          _ = Real.pi * (1/|u j|) := by ring
          _ ≤ Real.pi * (2/(1+|u j|)) := by
            apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
            apply (div_le_div_iff₀ (by linarith) (by positivity)).mpr
            linarith
          _ = _ := by dsimp [v]; ring
      _ = (2*Real.pi) * ∑ j ∈ T, v j := (Finset.mul_sum ..).symm
      _ ≤ (2*Real.pi) * (ε/(2*Real.pi)) := mul_le_mul_of_nonneg_left
        ((hs.trans hE.le).trans (min_le_right _ _)) (by positivity)
      _ = ε := by field_simp

end RiemannMasullo.StripNuclearity
