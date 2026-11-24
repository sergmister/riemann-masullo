module

public import RiemannMasullo.Ch09_HardySobolev.Sec3
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.Ring.GeomSum

/-! # Recovery after applying a finite Euler factor

On a compact strip whose lower endpoint exceeds `-1/2`, the powers of the
inverse translation with the central half twist tend to zero in operator norm.
The finite geometric sums then recover every vector of an invariant test
submodule in the norm closure of the image of the corresponding Euler factor.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set Topology
open scoped NNReal

namespace RiemannMasullo.StripNuclearity

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]

variable (μ : Measure G) [μ.IsHaarMeasure] (m : G →ₜ* ℝ≥0ˣ)

set_option quotPrecheck false
local notation "t(" p ")" => Real.log ((m p).val : ℝ)
local notation "W" => (fun a b s ↦ CompactIntervalSobolev μ (fun g ↦ t(g)) a b s)

/-- The inverse prime translation with the central half twist. Its Euler factor is
one minus this operator. -/
def finiteEulerTranslation (a b s : ℝ) (hab : a ≤ b) (hs : 0 ≤ s) (p : G) :
    W a b s →L[ℂ] W a b s :=
  Real.exp (-t(p) / 2) • hardySobolevTranslation μ m a b s hab hs p⁻¹

/-- The lower strip endpoint controls the exponential rate for inverse translation.
The Sobolev order contributes the polynomial loss in the log norm. -/
theorem norm_finiteEulerTranslation_pow_le (a b s : ℝ) (hab : a ≤ b) (hs : 0 ≤ s)
    (p : G) (hp : 0 < t(p)) (n : ℕ) :
    ‖finiteEulerTranslation μ m a b s hab hs p ^ n‖ ≤
      Real.exp (-(a + 1 / 2) * (n * t(p))) * (1 + n * t(p)) ^ (s / 2) := by
  have hn : 0 ≤ (n : ℝ) * t(p) := mul_nonneg n.cast_nonneg hp.le
  have hlog : t(p⁻¹ ^ n) = -(n * t(p)) := by
    simp only [map_pow, map_inv, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val,
      NNReal.coe_pow, NNReal.coe_inv, Real.log_pow, Real.log_inv, mul_neg]
  have h := norm_hardySobolevTranslation_le μ m a b s hab hs (p⁻¹ ^ n)
  dsimp only at h
  rw [hlog, abs_neg, abs_of_nonneg hn, max_eq_left (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonpos_right hab (neg_nonpos.mpr hn)))] at h
  rw [finiteEulerTranslation, smul_pow, ← map_pow, norm_smul,
    Real.norm_of_nonneg (pow_nonneg (Real.exp_pos _).le _), ← Real.exp_nat_mul]
  calc
    _ ≤ Real.exp (n * (-t(p) / 2)) *
        (Real.exp (a * -(n * t(p))) * (1 + n * t(p)) ^ (s / 2)) :=
      mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = _ := by rw [← mul_assoc, ← Real.exp_add]; congr 2; ring

/-- On every compact strip strictly to the right of `-1/2`, the twisted inverse
translation has powers tending to zero in operator norm. -/
theorem finiteEulerTranslation_pow_tendsto_zero (a b s : ℝ) (hab : a ≤ b) (hs : 0 ≤ s)
    (ha : -(1 / 2 : ℝ) < a) (p : G) (hp : 0 < t(p)) :
    Tendsto (fun n : ℕ ↦ finiteEulerTranslation μ m a b s hab hs p ^ n) atTop (𝓝 0) := by
  let c := a + 1 / 2
  have hc : 0 < c := by dsimp [c]; linarith
  have hu : Tendsto (fun n : ℕ ↦ (1 : ℝ) + n * t(p)) atTop atTop :=
    tendsto_atTop_add_const_left _ 1 (tendsto_natCast_atTop_atTop.atTop_mul_const hp)
  have he := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (s / 2) c hc).comp hu).mul_const
    (Real.exp c)
  apply squeeze_zero_norm (norm_finiteEulerTranslation_pow_le μ m a b s hab hs p hp)
  convert he using 1
  · funext n
    dsimp [Function.comp_def]
    rw [mul_assoc, ← Real.exp_add, mul_comm (Real.exp _)]
    congr 2
    dsimp [c]
    ring
  · simp

private theorem closure_map_one_sub_of_pow_tendsto_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (T : E →L[ℂ] E) (hT : Tendsto (fun n : ℕ ↦ T ^ n) atTop (𝓝 0))
    (U : Submodule ℂ E) (hU : ∀ x ∈ U, T x ∈ U) :
    (U.map (1 - T).toLinearMap).topologicalClosure = U.topologicalClosure := by
  let V := U.map (1 - T).toLinearMap
  apply le_antisymm
  · apply Submodule.topologicalClosure_mono
    rintro _ ⟨x, hx, rfl⟩
    exact U.sub_mem hx (hU x hx)
  · apply U.topologicalClosure_minimal _ V.isClosed_topologicalClosure
    intro x hx
    have hp (n : ℕ) : (T ^ n) x ∈ U := by
      induction n with
      | zero => simpa using hx
      | succ n ih => simpa [pow_succ', mul_apply_eq_comp] using hU _ ih
    have him (n : ℕ) : x - (T ^ n) x ∈ V := by
      refine ⟨(∑ i ∈ Finset.range n, T ^ i) x, ?_, ?_⟩
      · change (∑ i ∈ Finset.range n, T ^ i) x ∈ U
        rw [sum_apply]
        exact U.sum_mem (fun i _ ↦ hp i)
      · exact DFunLike.congr_fun (mul_neg_geom_sum T n) x
    have hz : Tendsto (fun n : ℕ ↦ (T ^ n) x) atTop (𝓝 0) := by
      simpa only [Function.comp_def, ContinuousLinearMap.apply_apply, zero_apply] using
        (((ContinuousLinearMap.apply ℂ E x).continuous.tendsto 0).comp hT)
    have hlim : Tendsto (fun n : ℕ ↦ x - (T ^ n) x) atTop (𝓝 x) := by
      simpa only [sub_zero] using hz.const_sub x
    exact V.isClosed_topologicalClosure.mem_of_tendsto hlim
      (Eventually.of_forall fun n ↦ V.le_topologicalClosure (him n))

/-- Every invariant test submodule is recovered, up to norm closure, from the image
of its finite Euler factor on a strip with lower endpoint strictly above `-1/2`. -/
theorem finiteEulerFactor_topologicalClosure (a b s : ℝ) (hab : a ≤ b) (hs : 0 ≤ s)
    (ha : -(1 / 2 : ℝ) < a) (p : G) (hp : 0 < t(p)) (U : Submodule ℂ (W a b s))
    (hU : ∀ x ∈ U, finiteEulerTranslation μ m a b s hab hs p x ∈ U) :
    (U.map (1 - finiteEulerTranslation μ m a b s hab hs p).toLinearMap).topologicalClosure =
      U.topologicalClosure :=
  closure_map_one_sub_of_pow_tendsto_zero _
    (finiteEulerTranslation_pow_tendsto_zero μ m a b s hab hs ha p hp) U hU

end RiemannMasullo.StripNuclearity
