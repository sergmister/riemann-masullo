module

public import RiemannMasullo.Ch09_HardySobolev.Sec3
import RiemannMasullo.ForMathlib.MeasureTheory.Group.Arithmetic

/-! # The absolute cutoff injectivity claim in §9.3.3 -/

@[expose] public noncomputable section

open Function MeasureTheory Set
open scoped ENNReal NNReal

namespace RiemannMasullo

/-- Paper: Remark 9.3.3.4, p. 428. As printed: On the weighted space W^{s,2}(G)
of every ℝ₊-modulated group with a choice of Haar measure, each of the positive,
negative and two-sided absolute cutoffs is injective, for every radius Λ > 0
and every s ≥ 0. See `modulatedAbsoluteCutoffOperator_projection` and ERRATA F238. -/
def Printed.modulatedAbsoluteCutoffOperator_injective : Prop :=
  ∀ (G : Type) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    (m : G →ₜ* ℝ≥0ˣ), IsModulation m → Surjective m → ∀ (Λ s : ℝ), 0 < Λ → 0 ≤ s →
      let ν := sobolevMeasure μ (modulatedSobolevWeight m) s
      Injective (modulatedAbsoluteCutoffOperator m ν (Ici Λ⁻¹) measurableSet_Ici) ∧
      Injective (modulatedAbsoluteCutoffOperator m ν (Iic Λ) measurableSet_Iic) ∧
      Injective (modulatedAbsoluteCutoffOperator m ν (Icc Λ⁻¹ Λ) measurableSet_Icc)

private theorem Printed.modulatedAbsoluteCutoffOperator_injective_false_logPreimage
    (K : Set ℝ) (hK : MeasurableSet K) :
    positiveRealHaar {t : ℝ≥0ˣ | Real.log (t.val : ℝ) ∈ K} = volume K := by
  let e (x : ℝ) := Units.mk0 (Real.exp x).toNNReal (Real.toNNReal_pos.mpr (Real.exp_pos x)).ne'
  have he : Measurable e :=
    measurable_comap_iff.mpr (continuous_real_toNNReal.comp Real.continuous_exp).measurable
  have hset : MeasurableSet {t : ℝ≥0ˣ | Real.log (t.val : ℝ) ∈ K} :=
    hK.preimage (Real.measurable_log.comp
      (NNReal.continuous_coe.measurable.comp MeasurableSpace.le_map_comap))
  change (volume.map e) _ = _
  rw [Measure.map_apply he hset]
  congr 1
  ext x
  change Real.log ((Real.exp x).toNNReal : ℝ) ∈ K ↔ x ∈ K
  rw [Real.coe_toNNReal _ (Real.exp_pos x).le, Real.log_exp]

/-- Paper: Remark 9.3.3.4, p. 428. Take the positive reals with the identity
modulation, s = 0 and Λ = 2. A nonzero smooth log-coordinate bump supported
in (−log 2−2, −log 2−1) is a nonzero L² class killed by the positive and
two-sided cutoffs. A bump supported in (log 2+1, log 2+2) is killed by
the negative cutoff. -/
theorem Printed.modulatedAbsoluteCutoffOperator_injective_false :
    ¬ Printed.modulatedAbsoluteCutoffOperator_injective := by
  intro h
  have : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  have : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  have : positiveRealHaar.IsHaarMeasure := positiveRealHaar_isHaarMeasure
  have hm : IsModulation (ContinuousMonoidHom.id ℝ≥0ˣ) :=
    ⟨isProperMap_id, ⟨Units.mk0 2 (by norm_num), by
      intro h
      have := congrArg (fun t : ℝ≥0ˣ ↦ (t.val : ℝ)) h
      norm_num at this⟩⟩
  have hinj := (h ℝ≥0ˣ positiveRealHaar (ContinuousMonoidHom.id ℝ≥0ˣ) hm surjective_id 2 0
    (by norm_num) le_rfl).1
  set ν := sobolevMeasure positiveRealHaar (modulatedSobolevWeight (ContinuousMonoidHom.id ℝ≥0ˣ))
    0 with hν
  have hν0 : ν = positiveRealHaar := sobolevMeasure_zero _ _
  let S : Set ℝ≥0ˣ := {t | Real.log (t.val : ℝ) ∈ Icc (-3 : ℝ) (-2)}
  have hS : MeasurableSet S := measurableSet_Icc.preimage (Real.measurable_log.comp
    (NNReal.continuous_coe.measurable.comp MeasurableSpace.le_map_comap))
  have hμS : positiveRealHaar S = 1 := by
    rw [Printed.modulatedAbsoluteCutoffOperator_injective_false_logPreimage _ measurableSet_Icc,
      Real.volume_Icc]
    norm_num
  have hfin : ν S ≠ ∞ := by rw [hν0, hμS]; exact ENNReal.one_ne_top
  have hpos : ν S ≠ 0 := by rw [hν0, hμS]; exact one_ne_zero
  let u := indicatorConstLp 2 hS hfin (1 : ℂ)
  have hu : u ≠ 0 := by
    intro h0
    have hn := congrArg norm h0
    rw [norm_zero, norm_indicatorConstLp' (by norm_num) hpos, norm_one, one_mul] at hn
    have : 0 < ν.real S := ENNReal.toReal_pos hpos hfin
    exact (Real.rpow_pos_of_pos this _).ne' hn
  have hdisj : ∀ t ∈ S, ¬ (((ContinuousMonoidHom.id ℝ≥0ˣ) t).val : ℝ) ∈ Ici (2 : ℝ)⁻¹ := by
    intro t ht hge
    have hle : Real.log (t.val : ℝ) ≤ -2 := ht.2
    have htpos : (0 : ℝ) < (t.val : ℝ) := by
      have := t.ne_zero
      exact lt_of_le_of_ne (NNReal.coe_nonneg _) (by exact_mod_cast this.symm)
    have h1 : (t.val : ℝ) ≤ Real.exp (-2) := by
      rw [← Real.exp_log htpos]
      exact Real.exp_le_exp.mpr hle
    have h2 : Real.exp (-2) < (2 : ℝ)⁻¹ := by
      have := Real.add_one_lt_exp (show (2 : ℝ) ≠ 0 by norm_num)
      rw [Real.exp_neg]
      exact inv_strictAnti₀ (by norm_num) (by linarith)
    exact absurd (lt_of_le_of_lt h1 h2) (not_lt.mpr (mem_Ici.mp hge))
  apply hu
  apply hinj
  rw [map_zero, modulatedAbsoluteCutoffOperator_eq_hardySobolevCutoff]
  refine Lp.ext ((MemLp.coeFn_toLp _).trans ?_)
  filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hS) (hμs := hfin) (c := (1 : ℂ)),
    Lp.coeFn_zero ℂ 2 ν] with x h2 h3
  rw [h3, Pi.zero_apply, Set.indicator_apply_eq_zero]
  intro hx
  rw [h2, Set.indicator_of_notMem]
  exact fun hxS ↦ hdisj x hxS hx

end RiemannMasullo
