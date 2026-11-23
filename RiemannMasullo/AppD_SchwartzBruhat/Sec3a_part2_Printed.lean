module

public import RiemannMasullo.AppD_SchwartzBruhat.Sec3a_part2
import all RiemannMasullo.AppD_SchwartzBruhat.Sec3a
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-! # Appendix D.3.3: the printed countable boundedness test -/

@[expose] public noncomputable section

namespace RiemannMasullo

open Bornology Filter Function Set
open scoped NNReal

/-- Paper: Proposition D.3.3.10(3), p. 807. As printed: a set of decay functions is
bounded precisely when its weighted images are bounded at each exponent in a countable
subset with both endpoints of the interval as accumulation points. The endpoints are taken
in the extended real line to include infinite endpoints. The countable test in
`modulatedExponentialDecay_bounded_iff_countable_twists` requires exponents on both sides
of each exponent of the interval, allowing equality. See ERRATA F12. -/
def Printed.modulatedExponentialDecay_bounded_iff_countable_twists : Prop :=
  ∀ (G : Type) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    (m : G →ₜ* ℝ≥0ˣ) (τ : ℝ≥0ˣ →ₜ* G),
    IsModulation m → RightInverse τ m →
    ∀ (I : Set ℝ), OrdConnected I → I.Nonempty →
    ∀ (B : Set (ModulatedExponentialDecay m I)) (J : Set I), J.Countable →
      let ends := (fun x : ℝ ↦ (x : EReal)) '' I
      let tests := (fun a : I ↦ ((a : ℝ) : EReal)) '' J
      AccPt (sInf ends) (𝓟 tests) → AccPt (sSup ends) (𝓟 tests) →
        (IsVonNBounded ℂ B ↔
          ∀ a ∈ J, IsVonNBounded ℂ (modulatedExponentialDecayTwist m I a '' B))

/-- Translates of a fixed Schwartz function by `n`, damped by `exp (-c n)` with `c > 0`,
form a bounded set: the polynomial growth of the seminorms in `n` loses to the damping. -/
private theorem printed_countable_twists_damped_translates_bounded (c : ℝ) (hc : 0 < c)
    (h : SchwartzMap ℝ ℂ) (G : ℕ → SchwartzMap ℝ ℂ)
    (hG : ∀ (n : ℕ) (x : ℝ), G n x = (Real.exp (-(c * n)) : ℂ) * h (x - n)) :
    Bornology.IsVonNBounded ℂ (range G) := by
  refine (schwartz_withSeminorms ℂ ℝ ℂ).isVonNBounded_iff_seminorm_bounded.mpr ?_
  rintro ⟨k, l⟩
  let Ch := 2 ^ k * (Finset.Iic (k, l)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) h
  have hCh : 0 ≤ Ch := by positivity
  let M := (k.factorial : ℝ) * Real.exp c / c ^ k * Ch
  refine ⟨M + 1, by positivity, ?_⟩
  rintro _ ⟨n, rfl⟩
  refine lt_of_le_of_lt ?_ (lt_add_one M)
  refine SchwartzMap.seminorm_le_bound ℂ k l (G n) (by positivity) fun x ↦ ?_
  have hfun : (G n : ℝ → ℂ) = fun x ↦ (Real.exp (-(c * n)) : ℂ) • h (x - n) :=
    funext fun x ↦ hG n x
  have hd : iteratedFDeriv ℝ l (G n : ℝ → ℂ) x =
      (Real.exp (-(c * n)) : ℂ) • iteratedFDeriv ℝ l (h : ℝ → ℂ) (x - n) := by
    have hsm : ContDiffAt ℝ l (fun z : ℝ ↦ h (z - n)) x :=
      ((h.smooth ⊤).comp (contDiff_id.sub contDiff_const)).contDiffAt.of_le
        (by exact_mod_cast le_top)
    rw [hfun, iteratedFDeriv_const_smul_apply' hsm, iteratedFDeriv_comp_sub]
  rw [hd, norm_smul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  have hx : ‖x‖ ≤ (1 + n) * (1 + ‖x - n‖) := by
    have : ‖x‖ ≤ ‖x - n‖ + n := by
      have := norm_add_le (x - n) (n : ℝ)
      rwa [sub_add_cancel, Real.norm_natCast] at this
    nlinarith [norm_nonneg (x - n), (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hh := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k, l)) le_rfl le_rfl h
    (x - n)
  have hpow : ‖x‖ ^ k ≤ (1 + n) ^ k * (1 + ‖x - n‖) ^ k := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hx k
  have hexp : (1 + (n : ℝ)) ^ k * Real.exp (-(c * n)) ≤ (k.factorial : ℝ) * Real.exp c / c ^ k := by
    have h1 := Real.pow_div_factorial_le_exp (x := c * (1 + n)) (by positivity) k
    rw [div_le_iff₀ (by positivity)] at h1
    rw [le_div_iff₀ (by positivity)]
    have h4 : Real.exp (c * (1 + n)) * Real.exp (-(c * n)) = Real.exp c := by
      rw [← Real.exp_add]; congr 1; ring
    calc (1 + (n : ℝ)) ^ k * Real.exp (-(c * n)) * c ^ k
        = (c * (1 + n)) ^ k * Real.exp (-(c * n)) := by rw [mul_pow]; ring
      _ ≤ (Real.exp (c * (1 + n)) * k.factorial) * Real.exp (-(c * n)) := by gcongr
      _ = k.factorial * Real.exp c := by rw [mul_right_comm, h4, mul_comm]
  calc ‖x‖ ^ k * (Real.exp (-(c * n)) * ‖iteratedFDeriv ℝ l (h : ℝ → ℂ) (x - n)‖)
      ≤ (1 + n) ^ k * (1 + ‖x - n‖) ^ k *
          (Real.exp (-(c * n)) * ‖iteratedFDeriv ℝ l (h : ℝ → ℂ) (x - n)‖) := by
        gcongr
    _ = ((1 + n) ^ k * Real.exp (-(c * n))) *
          ((1 + ‖x - n‖) ^ k * ‖iteratedFDeriv ℝ l (h : ℝ → ℂ) (x - n)‖) := by ring
    _ ≤ ((k.factorial : ℝ) * Real.exp c / c ^ k) * Ch := by
        gcongr
    _ = M := rfl

/-- A family of Schwartz functions with `G n n = 1` is unbounded: the seminorm
`sup |x| |G x|` of `G n` is at least `n`. -/
private theorem printed_countable_twists_not_bounded (G : ℕ → SchwartzMap ℝ ℂ)
    (hG : ∀ n : ℕ, G n (n : ℝ) = 1) : ¬ Bornology.IsVonNBounded ℂ (range G) := by
  intro hB
  obtain ⟨r, -, hr⟩ := (schwartz_withSeminorms ℂ ℝ ℂ).isVonNBounded_iff_seminorm_bounded.mp hB
    (1, 0)
  have h1 := hr _ (mem_range_self ⌈r⌉₊)
  have h2 := SchwartzMap.norm_pow_mul_le_seminorm ℂ (G ⌈r⌉₊) 1 (⌈r⌉₊ : ℝ)
  rw [hG, norm_one, mul_one, pow_one, Real.norm_natCast] at h2
  have h3 := Nat.le_ceil r
  change SchwartzMap.seminorm ℂ 1 0 (G ⌈r⌉₊) < r at h1
  linarith


/-- The bump profiles `exp (-n) ψ (x - n)`, twisted by an exponent `a < 1`, are damped
translates of their `n = 0` member, so they form a bounded set of Schwartz functions. -/
private theorem printed_countable_twists_log_bounded (b : ContDiffBump (0 : ℝ))
    (F : ℕ → PositiveRealExponentialDecay (Icc (0 : ℝ) 1))
    (hF : ∀ (n : ℕ) (x : ℝ), (F n).val x = ((Real.exp (-(n : ℝ)) * b (x - n) : ℝ) : ℂ))
    (a : Icc (0 : ℝ) 1) (ha : (a : ℝ) < 1) :
    Bornology.IsVonNBounded ℂ
      (range fun n ↦ logExponentialDecayTwist (Icc (0 : ℝ) 1) a (F n)) := by
  refine printed_countable_twists_damped_translates_bounded (1 - a) (sub_pos.mpr ha)
    (logExponentialDecayTwist (Icc (0 : ℝ) 1) a (F 0)) _ fun n x ↦ ?_
  have e1 : logExponentialDecayTwist (Icc (0 : ℝ) 1) a (F n) x =
      (Real.exp ((a : ℝ) * x) : ℂ) * (F n).val x := logExponentialDecayTwist_apply _ a (F n) x
  have e2 : logExponentialDecayTwist (Icc (0 : ℝ) 1) a (F 0) (x - n) =
      (Real.exp ((a : ℝ) * (x - n)) : ℂ) * (F 0).val (x - n) :=
    logExponentialDecayTwist_apply _ a (F 0) (x - n)
  rw [e1, e2, hF, hF]
  have key : Real.exp ((a : ℝ) * x) * (Real.exp (-(n : ℝ)) * b (x - n)) =
      Real.exp (-((1 - (a : ℝ)) * n)) * (Real.exp ((a : ℝ) * (x - n)) *
        (Real.exp (-((0 : ℕ) : ℝ)) * b (x - n - ((0 : ℕ) : ℝ)))) := by
    simp only [Nat.cast_zero, neg_zero, Real.exp_zero, one_mul, sub_zero]
    rw [← mul_assoc, ← mul_assoc, ← Real.exp_add, ← Real.exp_add,
      show (a : ℝ) * x + -(n : ℝ) = -((1 - (a : ℝ)) * n) + (a : ℝ) * (x - n) by ring]
  exact_mod_cast key

/-- The same profiles twisted by the endpoint exponent 1 take the value 1 at `x = n`, so the
family itself is unbounded in the logarithmic model. -/
private theorem printed_countable_twists_log_not_bounded (b : ContDiffBump (0 : ℝ))
    (F : ℕ → PositiveRealExponentialDecay (Icc (0 : ℝ) 1))
    (hF : ∀ (n : ℕ) (x : ℝ), (F n).val x = ((Real.exp (-(n : ℝ)) * b (x - n) : ℝ) : ℂ)) :
    ¬ Bornology.IsVonNBounded ℂ (range F) := by
  intro hB
  have hne : (Icc (0 : ℝ) 1).Nonempty := ⟨0, left_mem_Icc.mpr zero_le_one⟩
  let one : Icc (0 : ℝ) 1 := ⟨1, right_mem_Icc.mpr zero_le_one⟩
  let T : PositiveRealExponentialDecay (Icc (0 : ℝ) 1) →L[ℂ] SchwartzMap ℝ ℂ :=
    ⟨logExponentialDecayTwist (Icc (0 : ℝ) 1) one,
      (continuous_apply one).comp (positiveRealExponentialDecay_isEmbedding _ hne).continuous⟩
  refine printed_countable_twists_not_bounded (fun n ↦ T (F n)) (fun n ↦ ?_) ?_
  · change logExponentialDecayTwist (Icc (0 : ℝ) 1) one (F n) (n : ℝ) = 1
    have e1 : logExponentialDecayTwist (Icc (0 : ℝ) 1) one (F n) (n : ℝ) =
        (Real.exp ((one : ℝ) * n) : ℂ) * (F n).val n :=
      logExponentialDecayTwist_apply _ one (F n) n
    rw [e1, hF, sub_self,
      b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le), mul_one,
      ← Complex.ofReal_mul, ← Real.exp_add]
    change ((Real.exp (1 * (n : ℝ) + -(n : ℝ)) : ℝ) : ℂ) = 1
    rw [one_mul, add_neg_cancel, Real.exp_zero, Complex.ofReal_one]
  · refine (hB.image T).subset ?_
    rintro _ ⟨n, rfl⟩
    exact ⟨F n, ⟨n, rfl⟩, rfl⟩

/-- In the identity-modulation model on the positive reals, an interior twist of the family is
the Schwartz–Bruhat function with the corresponding logarithmic profile. -/
private theorem printed_countable_twists_transfer
    (F : ℕ → PositiveRealExponentialDecay (Icc (0 : ℝ) 1))
    (e : PositiveRealExponentialDecay (Icc (0 : ℝ) 1) ≃L[ℂ]
      ModulatedExponentialDecay (ContinuousMonoidHom.id ℝ≥0ˣ) (Icc (0 : ℝ) 1))
    (he : ∀ (f : PositiveRealExponentialDecay (Icc (0 : ℝ) 1)) (t : ℝ≥0ˣ),
      (e f).val t = f.val (Real.log (t.val : ℝ)))
    (a : Icc (0 : ℝ) 1)
    (ha : Bornology.IsVonNBounded ℂ
      (range fun n ↦ logExponentialDecayTwist (Icc (0 : ℝ) 1) a (F n))) :
    Bornology.IsVonNBounded ℂ (modulatedExponentialDecayTwist (ContinuousMonoidHom.id ℝ≥0ˣ)
      (Icc (0 : ℝ) 1) a '' range fun n ↦ e (F n)) := by
  have hS := schwartzBruhat_realCoordinate_equiv (G := ℝ≥0ˣ) positiveRealLogEquiv
  let S := hS.choose
  have hS' := hS.choose_spec
  have heq (n : ℕ) : modulatedExponentialDecayTwist (ContinuousMonoidHom.id ℝ≥0ˣ)
      (Icc (0 : ℝ) 1) a (e (F n)) = S (logExponentialDecayTwist (Icc (0 : ℝ) 1) a (F n)) := by
    refine SchwartzBruhat.ext fun t ↦ ?_
    refine (modulatedExponentialDecayTwist_apply (ContinuousMonoidHom.id ℝ≥0ˣ) (Icc (0 : ℝ) 1)
      a (e (F n)) t).trans (Eq.trans ?_ (hS' _ t).symm)
    rw [positiveRealLogEquiv_apply]
    refine Eq.trans ?_ (logExponentialDecayTwist_apply _ a (F n) _).symm
    change ((((t.val : ℝ) ^ (a : ℝ) : ℝ)) : ℂ) * (e (F n)).val t = _
    rw [he, Real.rpow_def_of_pos (NNReal.coe_pos.mpr (Units.zero_lt t)), mul_comm (Real.log _)]
  refine (ha.image (S : SchwartzMap ℝ ℂ →L[ℂ] SchwartzBruhat ℝ≥0ˣ)).subset ?_
  rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
  exact ⟨_, ⟨n, rfl⟩, (heq n).symm⟩

/-- The test exponents `1/(k+2)` tend to the lower endpoint 0, and `1 - 1/(k+2)` to the upper
endpoint 1, in the extended reals, without reaching them. -/
private theorem printed_countable_twists_accPt (s : ℕ → ℝ) (x : ℝ)
    (hs : Tendsto s atTop (nhds x)) (hne : ∀ k, s k ≠ x) (C : Set EReal)
    (hC : ∀ k, ((s k : ℝ) : EReal) ∈ C) : AccPt ((x : ℝ) : EReal) (𝓟 C) := by
  refine accPt_iff_frequently.mpr ((EReal.tendsto_coe.mpr hs).frequently
    (Frequently.of_forall fun k ↦ ⟨?_, hC k⟩))
  exact_mod_cast hne k

/-- Paper: Proposition D.3.3.10(3), p. 807. Take the positive real multiplicative group,
with identity modulation and section, I = [0,1] and J the points `1/(k+2)` and
`1 - 1/(k+2)`, which accumulate at both endpoints. For a smooth bump ψ on ℝ supported in
[-1,1] with ψ(0) = 1, take B to consist of the functions with log profiles
`fₙ(x) = exp(-n) ψ(x - n)`. The a-twists for a < 1 are damped translates `exp((a-1)n) h(x - n)`
of one Schwartz function, hence bounded. The 1-twist takes the value 1 at x = n, so its
seminorm `supₓ |x g(x)|` is at least n, and B is unbounded. -/
theorem Printed.modulatedExponentialDecay_bounded_iff_countable_twists_false :
    ¬ Printed.modulatedExponentialDecay_bounded_iff_countable_twists := by
  intro hP
  have : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  have hm : IsModulation (ContinuousMonoidHom.id ℝ≥0ˣ) :=
    ⟨isProperMap_id, ⟨Units.mk0 2 (by norm_num), by
      intro h
      have := congrArg (fun t : ℝ≥0ˣ ↦ (t.val : ℝ)) h
      norm_num at this⟩⟩
  have hne : (Icc (0 : ℝ) 1).Nonempty := ⟨0, left_mem_Icc.mpr zero_le_one⟩
  have hE := identityModulationExponentialDecay_equiv (Icc (0 : ℝ) 1) ordConnected_Icc hne
  let e := hE.choose
  have he := hE.choose_spec
  let b : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  let p (n : ℕ) (x : ℝ) : ℂ := ((Real.exp (-(n : ℝ)) * b (x - n) : ℝ) : ℂ)
  have hp (n : ℕ) : p n ∈ logExponentialDecaySubmodule (Icc (0 : ℝ) 1) := by
    refine mem_logExponentialDecaySubmodule_of_hasCompactSupport _ ?_ ?_
    · refine HasCompactSupport.intro (isCompact_closedBall (n : ℝ) 1) fun x hx ↦ ?_
      have h1 : b.rOut ≤ dist (x - n) 0 := by
        rw [dist_zero_right, Real.norm_eq_abs, ← Real.dist_eq]
        exact (lt_of_not_ge (fun h ↦ hx (Metric.mem_closedBall.mpr h))).le
      change ((Real.exp (-(n : ℝ)) * b (x - n) : ℝ) : ℂ) = 0
      rw [b.zero_of_le_dist h1, mul_zero, Complex.ofReal_zero]
    · exact Complex.ofRealCLM.contDiff.comp
        (contDiff_const.mul (b.contDiff.comp (contDiff_id.sub contDiff_const)))
  let F (n : ℕ) : PositiveRealExponentialDecay (Icc (0 : ℝ) 1) := ⟨p n, hp n⟩
  have hF (n : ℕ) (x : ℝ) : (F n).val x = ((Real.exp (-(n : ℝ)) * b (x - n) : ℝ) : ℂ) := rfl
  -- the test exponents
  let s (k : ℕ) : ℝ := 1 / (((k + 1 : ℕ) : ℝ) + 1)
  have hs0 (k : ℕ) : 0 < s k := by positivity
  have hs1 (k : ℕ) : s k < 1 := by
    refine (div_lt_one (by positivity)).mpr ?_
    have : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    linarith
  have hst : Tendsto s atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)
  let g (k : ℕ) : Icc (0 : ℝ) 1 := ⟨s k, (hs0 k).le, (hs1 k).le⟩
  let g' (k : ℕ) : Icc (0 : ℝ) 1 := ⟨1 - s k, by linarith [hs1 k], by linarith [hs0 k]⟩
  let J : Set (Icc (0 : ℝ) 1) := range g ∪ range g'
  have hJ : J.Countable := (countable_range g).union (countable_range g')
  have hJ1 : ∀ a ∈ J, (a : ℝ) < 1 := by
    rintro a (⟨k, rfl⟩ | ⟨k, rfl⟩)
    · exact hs1 k
    · change 1 - s k < 1
      linarith [hs0 k]
  let tests := (fun a : Icc (0 : ℝ) 1 ↦ ((a : ℝ) : EReal)) '' J
  have hInf : sInf ((fun x : ℝ ↦ (x : EReal)) '' Icc 0 1) = ((0 : ℝ) : EReal) := by
    refine IsLeast.csInf_eq ⟨⟨0, left_mem_Icc.mpr zero_le_one, rfl⟩, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact EReal.coe_le_coe_iff.mpr hx.1
  have hSup : sSup ((fun x : ℝ ↦ (x : EReal)) '' Icc 0 1) = ((1 : ℝ) : EReal) := by
    refine IsGreatest.csSup_eq ⟨⟨1, right_mem_Icc.mpr zero_le_one, rfl⟩, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact EReal.coe_le_coe_iff.mpr hx.2
  have hacc0 : AccPt (sInf ((fun x : ℝ ↦ (x : EReal)) '' Icc 0 1)) (𝓟 tests) := by
    rw [hInf]
    exact printed_countable_twists_accPt s 0 hst (fun k ↦ (hs0 k).ne') tests
      fun k ↦ ⟨g k, Or.inl ⟨k, rfl⟩, rfl⟩
  have hacc1 : AccPt (sSup ((fun x : ℝ ↦ (x : EReal)) '' Icc 0 1)) (𝓟 tests) := by
    rw [hSup]
    refine printed_countable_twists_accPt (fun k ↦ 1 - s k) 1 ?_ (fun k ↦ ?_) tests
      fun k ↦ ⟨g' k, Or.inr ⟨k, rfl⟩, rfl⟩
    · simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hst
    · linarith [hs0 k]
  have key := hP ℝ≥0ˣ (ContinuousMonoidHom.id ℝ≥0ˣ) (ContinuousMonoidHom.id ℝ≥0ˣ) hm
    (fun _ ↦ rfl) (Icc (0 : ℝ) 1) ordConnected_Icc hne (range fun n ↦ e (F n)) J hJ hacc0 hacc1
  have hB := key.mpr fun a ha ↦ printed_countable_twists_transfer F e he a
    (printed_countable_twists_log_bounded b F hF a (hJ1 a ha))
  apply printed_countable_twists_log_not_bounded b F hF
  refine (hB.image (e.symm : ModulatedExponentialDecay (ContinuousMonoidHom.id ℝ≥0ˣ)
    (Icc (0 : ℝ) 1) →L[ℂ] PositiveRealExponentialDecay (Icc (0 : ℝ) 1))).subset ?_
  rintro _ ⟨n, rfl⟩
  exact ⟨e (F n), ⟨n, rfl⟩, e.symm_apply_apply (F n)⟩

end RiemannMasullo
