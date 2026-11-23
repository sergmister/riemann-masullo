module

public import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec5
import all RiemannMasullo.Ch04_PeriodicSchauderBases.Sec5
import RiemannMasullo.ForMathlib.MeasureTheory.Group.Arithmetic
import all RiemannMasullo.AppD_SchwartzBruhat.Sec3a_part2
import all RiemannMasullo.AppC_LCTVS.Sec2b

/-! # §4.5: statements that are false as printed -/

@[expose] public noncomputable section

open Function MeasureTheory Set UniformSpace
open scoped NNReal TensorProduct

namespace RiemannMasullo

set_option quotPrecheck false

local instance printedCh04Sec5QuotientMeasurableSpace {G : Type} [CommGroup G]
    [TopologicalSpace G] (γ : G) : MeasurableSpace (G ⧸ Subgroup.zpowers γ) := borel _

/-- Paper: Remarks 4.5.1.2 and 4.5.1.4, pp. 198, 203. Agreement with (4.5.1.1)
on the original tests, using the split coordinates of
`modulatedExponentialDecay_tensor_equiv` and the canonical tensor comparison. -/
def Printed.AgreesWithFullPeriodization {G : Type} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m) (hms : Surjective m)
    (τ : ℝ≥0ˣ →ₜ* G) (γ : G) (hγ : 1 < (m γ).val) (I : Set ℝ)
    (A : Completion (ProjectiveTensor (SchwartzBruhat m.toMonoidHom.ker)
        (PositiveRealExponentialDecay I)) → SchwartzBruhat (G ⧸ Subgroup.zpowers γ)) : Prop :=
  let K := m.toMonoidHom.ker
  let TI := InductiveTensor (SchwartzBruhat K) (PositiveRealExponentialDecay I)
  let TP := ProjectiveTensor (SchwartzBruhat K) (PositiveRealExponentialDecay I)
  letI : UniformContinuousConstSMul ℂ TI := uniformContinuousConstSMul_of_continuousConstSMul ℂ TI
  ∀ e : Completion TI ≃L[ℂ] ModulatedExponentialDecay m I,
    (∀ (h : SchwartzBruhat K) (p : PositiveRealExponentialDecay I) (u : K) (t : ℝ≥0ˣ),
      (e (Completion.coe' (α := TI) (h ⊗ₜ[ℂ] p))).val (u.val * τ t) =
        h u * p.val (Real.log (t.val : ℝ))) →
    ∀ (z : Completion TI) (f : ModulatedExponentialDecay m univ), (e z).val = f.val →
      A (@Completion.map TI _ TP _ (fun v : TI ↦ (show TP from v)) z) = modulatedPeriodizationCLM m γ hm hms hγ f

/-- Paper: Remark 4.5.1.2, p. 198. Ordinary periodization extends sequentially
continuously to the projective completion. The remark leaves I implicit.
Deviation: This records the reading with an arbitrary nonempty interval from
Definition D.3.3.1. The case with zero in I is treated by
`modulatedIntervalPeriodization_projective`. See ERRATA F174. -/
def Printed.modulatedIntervalPeriodization_projective_sequential : Prop :=
  ∀ (G : Type) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m) (hms : Surjective m)
    (τ : ℝ≥0ˣ →ₜ* G), RightInverse τ m → ∀ (γ : G) (hγ : 1 < (m γ).val)
    (I : Set ℝ), OrdConnected I → I.Nonempty →
    let T := ProjectiveTensor (SchwartzBruhat m.toMonoidHom.ker) (PositiveRealExponentialDecay I)
    letI : UniformContinuousConstSMul ℂ T := uniformContinuousConstSMul_of_continuousConstSMul ℂ T
    ∃ A : Completion T →ₗ[ℂ] SchwartzBruhat (G ⧸ Subgroup.zpowers γ),
      SeqContinuous A ∧ Printed.AgreesWithFullPeriodization m hm hms τ γ hγ I A

section

open Filter
open scoped Topology SchwartzMap ContDiff

/-- Geometric damping beats polynomial growth of Schwartz translation seminorms. -/
private theorem modulatedIntervalPeriodization_false_translate_tendsto (f : 𝓢(ℝ, ℂ)) (c : ℝ)
    (hc : 0 < c) (hc' : c < 1) :
    Tendsto (fun n : ℕ ↦ (c : ℂ)^n • f.compSubConstCLM ℂ (-(n : ℝ))) atTop (𝓝 0) := by
  let T (n : ℕ) := f.compSubConstCLM ℂ (-(n : ℝ))
  have hb (k l n : ℕ) : SchwartzMap.seminorm ℂ k l (T n) ≤
      (n + 1 : ℝ)^k * (2 * 2^k) *
        (SchwartzMap.seminorm ℂ 0 l f + SchwartzMap.seminorm ℂ k l f) := by
    apply SchwartzMap.seminorm_le_bound' ℂ k l (T n) (by positivity)
    intro x
    have hd : iteratedDeriv l (T n) x = iteratedDeriv l f (x + n) := by
      change iteratedDeriv l (fun y ↦ f (y - -(n : ℝ))) x = _
      simp only [sub_neg_eq_add, iteratedDeriv_comp_add_const]
    rw [hd]
    have hw := intervalPrimitive_weight_bound x (1 : ℝ) n k
    simp only [norm_one, one_add_one_eq_two, nsmul_eq_mul, mul_one, Real.norm_eq_abs] at hw
    have h0 := SchwartzMap.le_seminorm' ℂ 0 l f (x + n)
    have hk := SchwartzMap.le_seminorm' ℂ k l f (x + n)
    simp only [pow_zero, one_mul] at h0
    calc
      |x|^k * ‖iteratedDeriv l f (x+n)‖ ≤ (1+|x|^k) * ‖iteratedDeriv l f (x+n)‖ := by gcongr; linarith
      _ ≤ ((n+1 : ℝ)^k * (2*2^k) * (1+|x+n|^k)) * ‖iteratedDeriv l f (x+n)‖ :=
        mul_le_mul_of_nonneg_right hw (norm_nonneg _)
      _ = ((n+1 : ℝ)^k * (2*2^k)) *
          (‖iteratedDeriv l f (x+n)‖ + |x+n|^k * ‖iteratedDeriv l f (x+n)‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add h0 hk) (by positivity)
  rw [(schwartz_withSeminorms ℂ ℝ ℂ).tendsto_nhds]
  intro i ε hε
  have hs := (summable_pow_mul_geometric_of_norm_lt_one i.1
    (show ‖c‖ < 1 by rwa [Real.norm_of_nonneg hc.le])).comp_injective Nat.succ_injective
  have hs' : Summable (fun n : ℕ ↦ (n+1 : ℝ)^i.1 * c^n) := by
    simpa only [Function.comp_def, Nat.cast_succ, pow_succ c, mul_assoc,
      mul_inv_cancel₀ hc.ne', mul_one] using hs.mul_right c⁻¹
  have ht := (hs'.mul_right ((2*2^i.1) *
    (SchwartzMap.seminorm ℂ 0 i.2 f + SchwartzMap.seminorm ℂ i.1 i.2 f))).tendsto_atTop_zero
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with n hn
  simp only [sub_zero]
  change SchwartzMap.seminorm ℂ i.1 i.2 ((c : ℂ)^n • T n) < ε
  rw [map_smul_eq_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hc.le]
  apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hb i.1 i.2 n) (pow_nonneg hc.le _))
  convert hn using 1 <;> ring
/-- Left-translated compact profiles tend to zero under the positive singleton weight. -/
private theorem modulatedIntervalPeriodization_false_profiles (ψ : ℝ → ℂ) (hc : HasCompactSupport ψ)
    (hd : ContDiff ℝ ∞ ψ) :
    ∃ (p : ℕ → PositiveRealExponentialDecay ({1} : Set ℝ))
      (q : ℕ → PositiveRealExponentialDecay univ),
      Tendsto p atTop (𝓝 0) ∧ ∀ n x, (p n).val x = ψ (x+n) ∧ (q n).val x = ψ (x+n) := by
  let u (I : Set ℝ) (n : ℕ) : PositiveRealExponentialDecay I :=
    ⟨fun x ↦ ψ (x+n), mem_logExponentialDecaySubmodule_of_hasCompactSupport I
      (hc.comp_homeomorph (Homeomorph.addRight (n : ℝ)))
      (hd.comp (contDiff_id.add contDiff_const))⟩
  let a : ({1} : Set ℝ) := ⟨1, mem_singleton 1⟩
  let f := logExponentialDecayTwist univ ⟨1, mem_univ 1⟩ (u univ 0)
  have hpow (n : ℕ) : Real.exp (-1)^n = Real.exp (-(n : ℝ)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have he (n : ℕ) : logExponentialDecayTwist {1} a (u {1} n) =
      (Real.exp (-1) : ℂ)^n • f.compSubConstCLM ℂ (-(n : ℝ)) := by
    ext x
    simp only [SchwartzMap.smul_apply, SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add, smul_eq_mul]
    change logExponentialDecayTwist {1} a (u {1} n) x =
      (Real.exp (-1) : ℂ)^n * f (x + n)
    rw [logExponentialDecayTwist_apply]
    change _ = (Real.exp (-1) : ℂ)^n *
      logExponentialDecayTwist univ ⟨1, mem_univ 1⟩ (u univ 0) (x+n)
    rw [logExponentialDecayTwist_apply]
    simp only [a, u, Nat.cast_zero, add_zero, one_mul]
    rw [← Complex.ofReal_pow, hpow, ← mul_assoc,
      ← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  refine ⟨u {1}, u univ, ?_, fun _ _ ↦ ⟨rfl,rfl⟩⟩
  apply (positiveRealExponentialDecay_isEmbedding {1} ⟨1, mem_singleton 1⟩).isInducing.tendsto_nhds_iff.mpr
  apply tendsto_pi_nhds.mpr
  intro b
  have hb : b = a := Subtype.ext (mem_singleton_iff.mp b.property)
  subst b
  change Tendsto (fun n ↦ logExponentialDecayTwist {1} a (u {1} n)) atTop
    (𝓝 (logExponentialDecayTwist {1} a 0))
  rw [map_zero]
  exact (modulatedIntervalPeriodization_false_translate_tendsto f (Real.exp (-1)) (Real.exp_pos _)
    (by simpa only [Real.exp_lt_one_iff] using (by norm_num : (-1 : ℝ) < 0))).congr'
      (Filter.Eventually.of_forall fun n ↦ (he n).symm)

/-- Paper: Remark 4.5.1.2, p. 198. Take the positive reals, period exp 1, and
I = {1}. In log coordinates take a smooth bump ψ supported in (−1/2,1/2)
with ψ(0) = 1. Its translates ψ(x+n) are full-decay tests tending to zero in
the singleton-weight space, since the twist gains exp(−n) against polynomial
growth in n. Tensor with the constant 1 on the trivial kernel and pass to the completion.
Every periodization has value 1 at the identity class. -/
theorem Printed.modulatedIntervalPeriodization_projective_sequential_false :
    ¬ Printed.modulatedIntervalPeriodization_projective_sequential := by
  intro h
  have : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  have : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let m := ContinuousMonoidHom.id ℝ≥0ˣ
  have hm : IsModulation m := ⟨isProperMap_id, ⟨Units.mk0 2 (by norm_num), by
    intro he
    have := congrArg (fun t : ℝ≥0ˣ ↦ (t.val : ℝ)) he
    norm_num [m] at this⟩⟩
  let eLog : ℝ≥0ˣ ≃ₜ ℝ := (Nonneg.unitsHomeomorphPos ℝ).trans Real.expOrderIso.symm.toHomeomorph
  have hlog (t : ℝ≥0ˣ) : eLog t = Real.log (t.val : ℝ) :=
    (Real.log_of_pos (NNReal.coe_pos.mpr t.zero_lt)).symm
  let γ := eLog.symm 1
  have hlogγ : Real.log (γ.val : ℝ) = 1 := (hlog γ).symm.trans (eLog.apply_symm_apply 1)
  have hγ : 1 < (m γ).val := by
    exact_mod_cast (Real.log_pos_iff (NNReal.coe_nonneg _)).mp (hlogγ.symm ▸ one_pos)
  have hpow (k : ℤ) : Real.log ((γ^k).val : ℝ) = k := by
    rw [← mul_one (γ^k), modulatedCompactSupport_isotypicQuotient_equiv_log,
      Units.val_one, NNReal.coe_one, Real.log_one, zero_add]
    exact (congrArg ((k : ℝ) * ·) hlogγ).trans (mul_one _)
  let I : Set ℝ := {1}
  have hI : OrdConnected I := ordConnected_singleton
  have hne : I.Nonempty := ⟨1, mem_singleton 1⟩
  let K := m.toMonoidHom.ker
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let : SecondCountableTopology K := TopologicalSpace.Subtype.secondCountableTopology (K : Set ℝ≥0ˣ)
  let : T2Space (SchwartzBruhat K) := schwartzBruhat_t2
  let : T2Space (PositiveRealExponentialDecay I) := (positiveRealExponentialDecay_isEmbedding I hne).t2Space
  let oneK := (compact_schwartzBruhat_one (H := K)).choose
  have honeK := (compact_schwartzBruhat_one (H := K)).choose_spec
  let TI := InductiveTensor (SchwartzBruhat K) (PositiveRealExponentialDecay I)
  let TP := ProjectiveTensor (SchwartzBruhat K) (PositiveRealExponentialDecay I)
  let TU := InductiveTensor (SchwartzBruhat K) (PositiveRealExponentialDecay univ)
  letI : UniformContinuousConstSMul ℂ TI := uniformContinuousConstSMul_of_continuousConstSMul ℂ TI
  letI : UniformContinuousConstSMul ℂ TP := uniformContinuousConstSMul_of_continuousConstSMul ℂ TP
  letI : UniformContinuousConstSMul ℂ TU := uniformContinuousConstSMul_of_continuousConstSMul ℂ TU
  let eI := (modulatedExponentialDecay_tensor_equiv m I hm hI hne m (fun _ ↦ rfl)).choose
  have heI := (modulatedExponentialDecay_tensor_equiv m I hm hI hne m (fun _ ↦ rfl)).choose_spec
  let eU := (modulatedExponentialDecay_tensor_equiv m univ hm ordConnected_univ univ_nonempty m (fun _ ↦ rfl)).choose
  have heU := (modulatedExponentialDecay_tensor_equiv m univ hm ordConnected_univ univ_nonempty m (fun _ ↦ rfl)).choose_spec
  let β : ContDiffBump (0 : ℝ) := ⟨1/4, 1/2, by norm_num, by norm_num⟩
  have hbC := β.hasCompactSupport.comp_left Complex.ofReal_zero
  obtain ⟨p, q, hp, hpq⟩ := modulatedIntervalPeriodization_false_profiles (fun x ↦ (β x : ℂ)) hbC
    (Complex.ofRealCLM.contDiff.comp β.contDiff)
  let z (n : ℕ) : Completion TI := Completion.coe' (oneK ⊗ₜ[ℂ] p n)
  let w (n : ℕ) : Completion TP := Completion.coe' (oneK ⊗ₜ[ℂ] p n)
  let f (n : ℕ) := eU (Completion.coe' (oneK ⊗ₜ[ℂ] q n))
  have hpt (t : ℝ≥0ˣ) : (1 : K).val * m t = t := one_mul t
  have hval (n : ℕ) (t : ℝ≥0ˣ) : (f n).val t = (β (Real.log (t.val : ℝ)+n) : ℂ) := by
    have h0 : (f n).val t = oneK 1 * (q n).val (Real.log (t.val : ℝ)) :=
      (congrArg (f n).val (hpt t)).symm.trans (heU oneK (q n) (1 : K) t)
    exact h0.trans ((congrArg₂ (· * ·) (honeK 1) (hpq n (Real.log (t.val : ℝ))).2).trans (one_mul _))
  have hmatch (n : ℕ) : (eI (z n)).val = (f n).val := by
    funext t
    have h0 : (eI (z n)).val t = oneK 1 * (p n).val (Real.log (t.val : ℝ)) :=
      (congrArg (eI (z n)).val (hpt t)).symm.trans (heI oneK (p n) (1 : K) t)
    have h1 := (hpq n (Real.log (t.val : ℝ))).1.trans (hpq n (Real.log (t.val : ℝ))).2.symm
    exact h0.trans ((congrArg (oneK 1 * ·) h1).trans
      ((heU oneK (q n) (1 : K) t).symm.trans (congrArg (f n).val (hpt t))))
  obtain ⟨A, hseq, hA⟩ := h ℝ≥0ˣ m hm surjective_id m (fun _ ↦ rfl) γ hγ I hI hne
  have hcmp (n : ℕ) : Completion.map (fun v : TI ↦ (show TP from v)) (z n) = w n :=
    Completion.map_coe (inductiveProjectiveComparison (X := SchwartzBruhat K)
      (Y := PositiveRealExponentialDecay I)).uniformContinuous _
  have hAw (n : ℕ) : A (w n) = modulatedPeriodizationCLM m γ hm surjective_id hγ (f n) := by
    exact (congrArg A (hcmp n)).symm.trans (hA eI heI (z n) (f n) (hmatch n))
  have hw : Tendsto w atTop (𝓝 0) := by
    have hcont : Continuous (fun p : PositiveRealExponentialDecay I ↦
        (Completion.coe' (α := TP) (oneK ⊗ₜ[ℂ] p))) :=
      (@Completion.continuous_coe TP _).comp
        (continuous_projectiveTensor_tmul_left (F := PositiveRealExponentialDecay I) oneK)
    have ht : Tendsto w atTop (𝓝 (Completion.coe' (α := TP) (oneK ⊗ₜ[ℂ] (0 : PositiveRealExponentialDecay I)))) :=
      hcont.continuousAt.tendsto.comp hp
    have hz : Completion.coe' (α := TP) (oneK ⊗ₜ[ℂ] (0 : PositiveRealExponentialDecay I)) = 0 := by
      rw [TensorProduct.tmul_zero]
      rfl
    exact hz ▸ ht
  have hev : Tendsto (fun n ↦ A (w n) (QuotientGroup.mk (1 : ℝ≥0ˣ))) atTop
      (𝓝 (A 0 (QuotientGroup.mk (1 : ℝ≥0ˣ)))) :=
    (continuous_schwartzBruhat_eval (QuotientGroup.mk (1 : ℝ≥0ˣ))).continuousAt.tendsto.comp (hseq hw)
  have hAz : A 0 (QuotientGroup.mk (1 : ℝ≥0ˣ)) = 0 :=
    congrArg (fun f : SchwartzBruhat (ℝ≥0ˣ ⧸ Subgroup.zpowers γ) ↦ f (QuotientGroup.mk 1)) (map_zero A)
  rw [hAz] at hev
  have hOne (n : ℕ) : A (w n) (QuotientGroup.mk (1 : ℝ≥0ˣ)) = 1 := by
    rw [hAw]
    have hs := modulatedPeriodization_hasSum m γ hm surjective_id hγ (f n) 1
    have hterm (k : ℤ) : (f n).val (γ^k * 1) = (β ((k : ℝ)+n) : ℂ) := by
      rw [mul_one, hval, hpow]
    have hb : HasSum (fun k : ℤ ↦ (β ((k : ℝ)+n) : ℂ)) 1 := by
      have hz (k : ℤ) (hk : k ≠ -(n : ℤ)) : (β ((k : ℝ)+n) : ℂ) = 0 := by
        have hkn : k + (n : ℤ) ≠ 0 := by omega
        have ha : (1 : ℝ) ≤ |(k : ℝ)+n| := by exact_mod_cast Int.one_le_abs hkn
        have hb : β.rOut ≤ dist ((k : ℝ)+n) 0 := by
          rw [Real.dist_0_eq_abs]
          change 1/2 ≤ _
          linarith
        rw [β.zero_of_le_dist hb, Complex.ofReal_zero]
      have hzero : (β ((-(n : ℤ) : ℤ)+n : ℝ) : ℂ) = 1 := by
        simp only [Int.cast_neg, Int.cast_natCast, neg_add_cancel]
        exact_mod_cast β.one_of_mem_closedBall (Metric.mem_closedBall_self β.rIn_pos.le)
      exact hzero ▸ hasSum_single (-(n : ℤ)) hz
    exact (hs.congr_fun fun k ↦ (hterm k).symm).unique hb
  have ht : Tendsto (fun _ : ℕ ↦ (1 : ℂ)) atTop (𝓝 0) := by
    exact hev.congr' (Filter.Eventually.of_forall hOne)
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds ht)


end

/-- Paper: Remark 4.5.1.4, p. 203. The forward map induced by ordinary
periodization on the quotient by its kernel is continuous. In the quotient
topology this is equivalent to continuity of the extension to the projective
completion. It agrees with (4.5.1.1) on its original full-decay domain.
Deviation: I is implicit in the remark. The counterexample works already for
full decay, I = ℝ. See ERRATA F174. -/
def Printed.modulatedIntervalPeriodization_projectiveQuotient_continuous : Prop :=
  ∀ (G : Type) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m) (hms : Surjective m)
    (τ : ℝ≥0ˣ →ₜ* G), RightInverse τ m → ∀ (γ : G) (hγ : 1 < (m γ).val)
    (I : Set ℝ), OrdConnected I → I.Nonempty →
    let T := ProjectiveTensor (SchwartzBruhat m.toMonoidHom.ker) (PositiveRealExponentialDecay I)
    letI : UniformContinuousConstSMul ℂ T := uniformContinuousConstSMul_of_continuousConstSMul ℂ T
    ∃ A : Completion T →L[ℂ] SchwartzBruhat (G ⧸ Subgroup.zpowers γ),
      Printed.AgreesWithFullPeriodization m hm hms τ γ hγ I A

/-- Paper: Remark 4.5.1.4, p. 203. Any continuous extension is sequentially
continuous. The positive singleton-weight shifted-bump counterexample above
therefore also refutes the universally quantified continuous extension. -/
theorem Printed.modulatedIntervalPeriodization_projectiveQuotient_continuous_false :
    ¬ Printed.modulatedIntervalPeriodization_projectiveQuotient_continuous := by
  intro h
  apply Printed.modulatedIntervalPeriodization_projective_sequential_false
  intro G _ _ _ _ _ _ m hm hms τ hτ γ hγ I hI hne
  let T := ProjectiveTensor (SchwartzBruhat m.toMonoidHom.ker) (PositiveRealExponentialDecay I)
  letI : UniformContinuousConstSMul ℂ T := uniformContinuousConstSMul_of_continuousConstSMul ℂ T
  obtain ⟨A, hA⟩ := h G m hm hms τ hτ γ hγ I hI hne
  exact ⟨A.toLinearMap, A.continuous.seqContinuous, hA⟩

/-- Paper: Theorem 4.5.2.3, (4.5.2.2), p. 207. As printed: For every compact
module window with nonempty interior, the map induced by inclusion from the
supported quotient to the full isotypic periodization quotient is a linear
homeomorphism. This is the isomorphism preceding the numbered parts.
The repaired statement is `modulatedCompactSupport_isotypicQuotient_equiv`.
See ERRATA F174. -/
def Printed.modulatedCompactSupport_isotypicQuotient_equiv : Prop :=
  ∀ (G : Type) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m) (hms : Surjective m) (γ : G) (hγ : 1 < (m γ).val)
    (μ₁ : Measure m.toMonoidHom.ker) [μ₁.IsHaarMeasure]
    (χ : PontryaginDual m.toMonoidHom.ker → PontryaginDual G),
    (∀ (ω : PontryaginDual m.toMonoidHom.ker) (k : m.toMonoidHom.ker), χ ω k.val = ω k) →
    ∀ (ω : PontryaginDual m.toMonoidHom.ker) (B : Set ℝ≥0ˣ), IsCompact B → (interior B).Nonempty →
    let P := modulatedIsotypicPeriodizationCLM m γ hm hms hγ μ₁ (χ ω)
    let D := modulatedCompactSupportSubmodule m B
    let N := P.ker.comap D.subtype
    ∃ e : (D ⧸ N) ≃L[ℂ] (ModulatedExponentialDecay m univ ⧸ P.ker),
      ∀ f : D, e (N.mkQ f) = P.ker.mkQ f.val

/-- A test in the decay space of the positive reals that vanishes off a closed window
vanishes at every point outside the interior of the window: its support is open. -/
private theorem Printed.modulatedCompactSupport_isotypicQuotient_equiv_false_vanish
    (B : Set ℝ≥0ˣ) (hB : IsClosed B)
    (d : modulatedCompactSupportSubmodule (ContinuousMonoidHom.id ℝ≥0ˣ) B)
    (x : ℝ≥0ˣ) (hx : x ∉ interior B) : d.val.val x = 0 := by
  have : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  have hmem : d.val.val ∈ schwartzBruhatSubmodule ℝ≥0ˣ := by
    have h := (Submodule.mem_iInf _).mp d.val.property ⟨0, mem_univ 0⟩
    rwa [Submodule.mem_comap, modulationWeight_zero] at h
  have hc : Continuous d.val.val := schwartzBruhat_continuous (G := ℝ≥0ˣ) ⟨d.val.val, hmem⟩
  have hsupp := ((mem_modulatedCompactSupportSubmodule_iff (ContinuousMonoidHom.id ℝ≥0ˣ) B hB
    d.val).mp d.property).2
  by_contra hne
  exact hx (interior_maximal (subset_tsupport _ |>.trans hsupp)
    hc.isOpen_support (mem_support.mpr hne))

/-- On the positive reals with identity module, a test that vanishes off a closed window
whose interior misses the orbit of the identity has homogeneous periodization zero at the
identity class. -/
private theorem Printed.modulatedCompactSupport_isotypicQuotient_equiv_false_supported
    (_hSC : SecondCountableTopology ℝ≥0ˣ) (hBo : BorelSpace ℝ≥0ˣ)
    (hm : IsModulation (ContinuousMonoidHom.id ℝ≥0ˣ)) (γ : ℝ≥0ˣ)
    (hγ : 1 < (ContinuousMonoidHom.id ℝ≥0ˣ γ).val)
    (μ₁ : Measure (ContinuousMonoidHom.id ℝ≥0ˣ).toMonoidHom.ker) [μ₁.IsHaarMeasure]
    (ξ : PontryaginDual ℝ≥0ˣ) (B : Set ℝ≥0ˣ) (hB : IsClosed B)
    (hγB : ∀ n : ℤ, γ ^ n ∉ interior B)
    (d : modulatedCompactSupportSubmodule (ContinuousMonoidHom.id ℝ≥0ˣ) B) :
    modulatedIsotypicPeriodizationCLM (ContinuousMonoidHom.id ℝ≥0ˣ) γ hm surjective_id hγ μ₁ ξ
      d.val (QuotientGroup.mk 1) = 0 := by
  have hs := modulatedIsotypicPeriodization_hasSum (ContinuousMonoidHom.id ℝ≥0ˣ) γ hm
    surjective_id hγ μ₁ ξ d.val 1
  have hz (n : ℤ) : (∫ k : (ContinuousMonoidHom.id ℝ≥0ˣ).toMonoidHom.ker,
      (ξ k.val : ℂ) * d.val.val (γ ^ n * (k.val * 1)) ∂μ₁) = 0 := by
    refine integral_eq_zero_of_ae (.of_forall fun k ↦ ?_)
    change (ξ k.val : ℂ) * d.val.val (γ ^ n * (k.val * 1)) = 0
    have hk : k.val = 1 := k.property
    rw [hk, mul_one, mul_one]
    exact mul_eq_zero_of_right _
      (Printed.modulatedCompactSupport_isotypicQuotient_equiv_false_vanish B hB d _ (hγB n))
  have h0 : HasSum (fun n : ℤ ↦ ∫ k : (ContinuousMonoidHom.id ℝ≥0ˣ).toMonoidHom.ker,
      (ξ k.val : ℂ) * d.val.val (γ ^ n * (k.val * 1)) ∂μ₁) 0 := by
    simp only [hz]
    exact hasSum_zero
  exact hs.unique h0

/-- A smooth bump of radius 1/2 at the origin sums to one over the integers. -/
private theorem Printed.modulatedCompactSupport_isotypicQuotient_equiv_false_bumpSum
    (φ : ContDiffBump (0 : ℝ)) (hφ : φ.rOut = 1 / 2) :
    HasSum (fun n : ℤ ↦ (φ (n : ℝ) : ℂ)) 1 := by
  have hs1 := hasSum_single (f := fun n : ℤ ↦ (φ (n : ℝ) : ℂ)) 0 fun n hn ↦ by
    have hn' : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
    have hdist : φ.rOut ≤ dist (n : ℝ) 0 := by
      rw [Real.dist_0_eq_abs, hφ]
      linarith
    change ((φ (n : ℝ) : ℝ) : ℂ) = 0
    rw [φ.zero_of_le_dist hdist, Complex.ofReal_zero]
  have hv : (fun n : ℤ ↦ (φ (n : ℝ) : ℂ)) 0 = 1 := by
    change ((φ ((0 : ℤ) : ℝ) : ℝ) : ℂ) = 1
    rw [Int.cast_zero, φ.one_of_mem_closedBall (Metric.mem_closedBall_self φ.rIn_pos.le),
      Complex.ofReal_one]
  exact hv ▸ hs1

/-- On the positive reals with identity module, if the generator has logarithm one, a
lifted logarithmic bump has homogeneous periodization one at the identity class. -/
private theorem Printed.modulatedCompactSupport_isotypicQuotient_equiv_false_bump
    (hSC : SecondCountableTopology ℝ≥0ˣ) (hBo : BorelSpace ℝ≥0ˣ)
    (hm : IsModulation (ContinuousMonoidHom.id ℝ≥0ˣ)) (γ : ℝ≥0ˣ)
    (hγ : 1 < (ContinuousMonoidHom.id ℝ≥0ˣ γ).val)
    (hpow : ∀ n : ℤ, Real.log ((γ ^ n).val : ℝ) = n)
    (μ₁ : Measure (ContinuousMonoidHom.id ℝ≥0ˣ).toMonoidHom.ker) [μ₁.IsHaarMeasure]
    (ξ : PontryaginDual ℝ≥0ˣ) :
    ∃ g : ModulatedExponentialDecay (ContinuousMonoidHom.id ℝ≥0ˣ) univ,
      modulatedIsotypicPeriodizationCLM (ContinuousMonoidHom.id ℝ≥0ˣ) γ hm surjective_id hγ μ₁ ξ
        g (QuotientGroup.mk 1) = 1 := by
  let m := ContinuousMonoidHom.id ℝ≥0ˣ
  let C : TopologicalSpace.Compacts ℝ := ⟨Metric.closedBall 0 (1 / 2), isCompact_closedBall 0 _⟩
  let φ : ContDiffBump (0 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  let w : ContDiffMapSupportedIn ℝ ℂ ⊤ C :=
    ⟨fun x ↦ (φ x : ℂ), Complex.ofRealCLM.contDiff.comp φ.contDiff, fun x hx ↦ by
      have hx' : φ.rOut ≤ dist x 0 := le_of_lt (not_le.mp hx)
      change ((φ x : ℝ) : ℂ) = 0
      rw [φ.zero_of_le_dist hx', Complex.ofReal_zero]⟩
  let p := compactLogProfileInclusion C w
  let τ : ℝ≥0ˣ →ₜ* ℝ≥0ˣ := ContinuousMonoidHom.id _
  have hτ : RightInverse τ m := fun _ ↦ rfl
  have hJ₀ := modulatedCompactSupport_isotypicQuotient_equiv_profileLift m hm μ₁ τ hτ ξ
  have hJ := hJ₀.choose_spec.1
  refine ⟨hJ₀.choose p, ?_⟩
  have hs := modulatedIsotypicPeriodization_hasSum m γ hm surjective_id hγ μ₁ ξ (hJ₀.choose p) 1
  have hterm (n : ℤ) : (∫ k : m.toMonoidHom.ker,
      (ξ k.val : ℂ) * (hJ₀.choose p).val (γ ^ n * (k.val * 1)) ∂μ₁) = (φ (n : ℝ) : ℂ) := by
    have hpt (k : m.toMonoidHom.ker) : γ ^ n * (k.val * 1) = k.val * τ (γ ^ n) := by
      rw [mul_one]
      exact mul_comm _ _
    calc _ = ∫ k : m.toMonoidHom.ker, (ξ k.val : ℂ) * (hJ₀.choose p).val (k.val * τ (γ ^ n)) ∂μ₁ :=
          integral_congr_ae (.of_forall fun k ↦
            congrArg (fun y ↦ (ξ k.val : ℂ) * (hJ₀.choose p).val y) (hpt k))
      _ = p.val (Real.log ((γ ^ n).val : ℝ)) := hJ p (γ ^ n)
      _ = _ := by
        rw [hpow]
        rfl
  have hs' : HasSum (fun n : ℤ ↦ (φ (n : ℝ) : ℂ))
      (modulatedIsotypicPeriodizationCLM m γ hm surjective_id hγ μ₁ ξ (hJ₀.choose p)
        (QuotientGroup.mk 1)) := by
    simp only [← hterm]
    exact hs
  exact hs'.unique
    (Printed.modulatedCompactSupport_isotypicQuotient_equiv_false_bumpSum φ rfl)

/-- Paper: Theorem 4.5.2.3, (4.5.2.2), p. 207. Take the positive reals with
identity module, the trivial character, γ > 1 and B = [1, γ]. Every smooth
test supported in B vanishes at both endpoints. These are the only orbit
points of the identity in B, so every supported periodization vanishes there.
A nonnegative smooth compactly supported test positive at 1 has nonzero
periodization at the identity, giving a missing class in the full quotient. -/
theorem Printed.modulatedCompactSupport_isotypicQuotient_equiv_false :
    ¬ Printed.modulatedCompactSupport_isotypicQuotient_equiv := by
  intro h
  have : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  have : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  have hm : IsModulation (ContinuousMonoidHom.id ℝ≥0ˣ) :=
    ⟨isProperMap_id, ⟨Units.mk0 2 (by norm_num), by
      intro h
      have := congrArg (fun t : ℝ≥0ˣ ↦ (t.val : ℝ)) h
      norm_num at this⟩⟩
  -- Logarithmic coordinates.
  let e : ℝ≥0ˣ ≃ₜ ℝ := (Nonneg.unitsHomeomorphPos ℝ).trans Real.expOrderIso.symm.toHomeomorph
  have he (t : ℝ≥0ˣ) : e t = Real.log (t.val : ℝ) :=
    (Real.log_of_pos (NNReal.coe_pos.mpr t.zero_lt)).symm
  let γ : ℝ≥0ˣ := e.symm 1
  have hlogγ : Real.log (γ.val : ℝ) = 1 := (he γ).symm.trans (e.apply_symm_apply 1)
  have hγ : 1 < (ContinuousMonoidHom.id ℝ≥0ˣ γ).val := by
    have h1 := (Real.log_pos_iff (NNReal.coe_nonneg _)).mp (hlogγ.symm ▸ one_pos)
    exact_mod_cast h1
  have hpow (n : ℤ) : Real.log ((γ ^ n).val : ℝ) = n := by
    rw [← mul_one (γ ^ n), modulatedCompactSupport_isotypicQuotient_equiv_log,
      Units.val_one, NNReal.coe_one, Real.log_one, zero_add]
    exact (congrArg ((n : ℝ) * ·) hlogγ).trans (mul_one _)
  -- The norm-one group is trivial.
  let K := (ContinuousMonoidHom.id ℝ≥0ˣ).toMonoidHom.ker
  have : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let μ₁ : Measure K := Measure.haar
  let χ : PontryaginDual K → PontryaginDual ℝ≥0ˣ := fun _ ↦ 1
  have hχ (ω : PontryaginDual K) (k : K) : χ ω k.val = ω k := by
    have hk : k = 1 := Subtype.ext k.property
    rw [hk]
    exact (map_one (χ ω)).trans (map_one ω).symm
  -- The window B = exp [0, 1] = [1, γ].
  let B : Set ℝ≥0ˣ := e ⁻¹' Icc 0 1
  have hBc : IsCompact B := e.isCompact_preimage.mpr isCompact_Icc
  have hBint : interior B = e ⁻¹' Ioo 0 1 := by
    change interior (e ⁻¹' Icc 0 1) = _
    rw [← e.preimage_interior, interior_Icc]
  have hBi : (interior B).Nonempty :=
    ⟨e.symm (1 / 2), by rw [hBint, mem_preimage, e.apply_symm_apply]; norm_num⟩
  have hγB (n : ℤ) : γ ^ n ∉ interior B := by
    rw [hBint, mem_preimage, he, hpow]
    rintro ⟨h0, h1⟩
    have h0' : (0 : ℤ) < n := by exact_mod_cast h0
    have h1' : n < 1 := by exact_mod_cast h1
    omega
  have hF₀ := h ℝ≥0ˣ (ContinuousMonoidHom.id ℝ≥0ˣ) hm surjective_id γ hγ μ₁ χ hχ 1 B hBc hBi
  have hd := Printed.modulatedCompactSupport_isotypicQuotient_equiv_false_supported ‹_› ‹_› hm γ hγ μ₁
    (χ 1) B hBc.isClosed hγB
  have hg := Printed.modulatedCompactSupport_isotypicQuotient_equiv_false_bump ‹_› ‹_› hm γ hγ hpow μ₁
    (χ 1)
  -- Inclusion is onto, so some supported test has the periodization of g.
  obtain ⟨g, hg1⟩ := hg
  obtain ⟨F, hF⟩ := hF₀
  obtain ⟨z, hz⟩ := F.surjective (Submodule.mkQ _ g)
  obtain ⟨d, rfl⟩ := Submodule.mkQ_surjective _ z
  have h1 := (hF d).symm.trans hz
  have h2 := (Submodule.Quotient.eq _).mp h1
  have h3 : modulatedIsotypicPeriodizationCLM (ContinuousMonoidHom.id ℝ≥0ˣ) γ hm surjective_id
      hγ μ₁ (χ 1) (d.val - g) = 0 := h2
  rw [map_sub, sub_eq_zero] at h3
  have h4 := congrArg (fun f : SchwartzBruhat (ℝ≥0ˣ ⧸ Subgroup.zpowers γ) ↦
    f (QuotientGroup.mk 1)) h3
  exact zero_ne_one ((hd d).symm.trans (h4.trans hg1))

end RiemannMasullo
