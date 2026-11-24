module
public import RiemannMasullo.Ch10_TraceSpectral.Sec2
import RiemannMasullo.Ch09_HardySobolev.Sec2

open Filter Function MeasureTheory Set
open scoped ENNReal Topology
@[expose] public noncomputable section
namespace RiemannMasullo.SharpStripEval

private theorem polynomial_le_exp {s d : ℝ} (hs : 0 ≤ s) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, (1 + x ^ 2) ^ (s / 2) ≤ C * Real.exp (d * |x|) := by
  let r := d / (s + 1)
  let A := max 1 (1 / r)
  have hsp : 0 < s + 1 := by linarith
  have hr : 0 < r := div_pos hd hsp
  have hA : 1 ≤ A := le_max_left _ _
  have hA0 : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hAr : 1 ≤ A * r := (div_le_iff₀ hr).mp (le_max_right _ _)
  have hrs : r * s ≤ d := by
    have hh : r * (s + 1) = d := div_mul_cancel₀ _ hsp.ne'
    nlinarith
  refine ⟨A ^ s, Real.rpow_pos_of_pos hA0 _, fun x ↦ ?_⟩
  have hx := abs_nonneg x
  have he : 1 + |x| ≤ A * Real.exp (r * |x|) := calc
    _ ≤ A + (A * r) * |x| := add_le_add hA (le_mul_of_one_le_left hx hAr)
    _ = A * (r * |x| + 1) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) hA0.le
  calc
    _ ≤ ((1 + |x|) ^ 2) ^ (s / 2) :=
      Real.rpow_le_rpow (by positivity) (by nlinarith [sq_abs x]) (by linarith)
    _ = (1 + |x|) ^ s := by
      rw [← Real.rpow_natCast (1 + |x|) 2, ← Real.rpow_mul (by positivity)]
      congr 1
      push_cast
      ring
    _ ≤ (A * Real.exp (r * |x|)) ^ s := Real.rpow_le_rpow (by positivity) he hs
    _ = A ^ s * Real.exp ((r * s) * |x|) := by
      rw [Real.mul_rpow hA0.le (Real.exp_pos _).le, ← Real.exp_mul]
      ring_nf
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hrs hx))
      (Real.rpow_nonneg hA0.le _)

private theorem sym_weight {α : ℝ} (hα : 0 ≤ α) (s x : ℝ) :
    intervalSobolevDensity (-α) α s x = Real.exp (2 * α * |x|) * (1 + x ^ 2) ^ (s / 2) := by
  unfold intervalSobolevDensity
  congr 1
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx, max_eq_right]
    exact Real.exp_le_exp.mpr (by nlinarith)
  · rw [abs_of_nonpos hx, max_eq_left]
    · congr 1
      ring
    · exact Real.exp_le_exp.mpr (by nlinarith)

/-- Any strict increase in strip width absorbs every nonnegative polynomial Sobolev degree. -/
theorem exists_id_on_wider_strip {α β s t : ℝ} (hα : 0 ≤ α) (hαβ : α < β)
    (hs : 0 ≤ s) (ht : 0 ≤ t) :
    ∃ J : CompactIntervalSobolev volume id (-β) β t →L[ℂ]
        CompactIntervalSobolev volume id (-α) α s,
      ∀ f, (J f : ℝ → ℂ) =ᵐ[volume] (f : ℝ → ℂ) := by
  let D (a p : ℝ) := intervalSobolevDensity (-a) a p
  let ν (a p : ℝ) := volume.withDensity (fun x ↦ ENNReal.ofReal (D a p x))
  obtain ⟨C, hC, hpow⟩ := polynomial_le_exp hs (by linarith : 0 < 2 * (β - α))
  have hD (x : ℝ) : D α s x ≤ C * D β t x := by
    change intervalSobolevDensity (-α) α s x ≤ C * intervalSobolevDensity (-β) β t x
    rw [sym_weight hα, sym_weight (hα.trans hαβ.le)]
    have ht1 : (1 : ℝ) ≤ (1 + x ^ 2) ^ (t / 2) :=
      Real.one_le_rpow (by linarith [sq_nonneg x]) (by linarith)
    calc
      _ ≤ Real.exp (2 * α * |x|) * (C * Real.exp (2 * (β - α) * |x|)) :=
        mul_le_mul_of_nonneg_left (hpow x) (Real.exp_pos _).le
      _ = C * Real.exp (2 * β * |x|) := by
        rw [mul_left_comm, ← Real.exp_add]
        ring_nf
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (le_mul_of_one_le_right (Real.exp_pos _).le ht1) hC.le
  have hle : ν α s ≤ ENNReal.ofReal C • ν β t := by
    dsimp only [ν]
    rw [← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
    apply withDensity_mono (.of_forall fun x ↦ ?_)
    change ENNReal.ofReal (D α s x) ≤ ENNReal.ofReal C * ENNReal.ofReal (D β t x)
    rw [← ENNReal.ofReal_mul hC.le]
    exact ENNReal.ofReal_le_ofReal (hD x)
  have hac := Measure.absolutelyContinuous_of_le_smul hle
  let L := Lp.LpToLpOfMeasureLeSMul (E := ℂ) (p := 2) ENNReal.ofReal_ne_top hle
  have hL (f : Lp ℂ 2 (ν β t)) : (L f : ℝ → ℂ) =ᵐ[ν α s] (f : ℝ → ℂ) :=
    Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top hle f
  let J : Lp ℂ 2 (ν β t) →L[ℂ] Lp ℂ 2 (ν α s) :=
    { toFun := L
      map_add' := L.map_add
      map_smul' := fun c f ↦ Lp.ext ((hL (c • f)).trans ((hac.ae_eq (Lp.coeFn_smul c f)).trans
        (((hL f).symm.fun_comp (c • ·)).trans (Lp.coeFn_smul c (L f)).symm)))
      cont := L.continuous }
  have hm : Measurable (D α s) := by unfold D intervalSobolevDensity; fun_prop
  have hp (x : ℝ) : 0 < D α s x := by
    change 0 < intervalSobolevDensity (-α) α s x
    rw [sym_weight hα]
    positivity
  have hbase : volume ≪ ν α s := withDensity_absolutelyContinuous'
    hm.ennreal_ofReal.aemeasurable (.of_forall fun x ↦ ENNReal.ofReal_ne_zero_iff.mpr (hp x))
  exact ⟨J, fun f ↦ hbase.ae_eq (hL f)⟩

/-- The full abscissa and sharp boundary-order test for bounded Mellin derivative evaluations. -/
theorem scalarIntervalSobolev_eval_iff (α s : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s) (k : ℕ) (z : ℂ) :
    (∃ Λ : CompactIntervalSobolev volume id (-α) α s →L[ℂ] ℂ,
      ∀ (f : PositiveRealExponentialDecay univ) (u : CompactIntervalSobolev volume id (-α) α s),
        (u : ℝ → ℂ) =ᵐ[volume] f.val →
        Λ u = iteratedDeriv k (mellin (fun t ↦ f.val (Real.log t))) z) ↔
      |z.re| < α ∨ |z.re| = α ∧ 2 * (k : ℝ) + 1 < s := by
  let β := |z.re|
  have hβ : 0 ≤ β := abs_nonneg _
  have hmem : z.re ∈ ({-β, β} : Set ℝ) := by
    by_cases hz : 0 ≤ z.re
    · exact Or.inr (by simp [β, abs_of_nonneg hz])
    · exact Or.inl (by simp [β, abs_of_nonpos (le_of_not_ge hz)])
  have eint (p : ℝ) (hp : 0 ≤ p) := scalarIntervalSobolev_eval_boundary_iff (-β) β p
    ((neg_nonpos.mpr hβ).trans hβ) hp k z hmem
  rcases lt_trichotomy β α with h | he | h
  · refine ⟨fun _ ↦ Or.inl h, fun _ ↦ ?_⟩
    let p : ℝ := 2 * k + 2
    obtain ⟨Λ, hΛ⟩ := (eint p (by dsimp [p]; positivity)).mpr (by dsimp [p]; linarith)
    obtain ⟨J, hJ⟩ := exists_id_on_wider_strip hβ h (s := p) (t := s) (by dsimp [p]; positivity) hs
    exact ⟨Λ.comp J, fun f u hu ↦ hΛ f (J u) ((hJ u).trans hu)⟩
  · subst α
    constructor
    · intro hbounded
      exact Or.inr ⟨rfl, (eint s hs).mp hbounded⟩
    · rintro (hlt | ⟨_, horder⟩)
      · exact (lt_irrefl _ hlt).elim
      · exact (eint s hs).mpr horder
  · refine ⟨?_, fun hc ↦ False.elim ?_⟩
    · rintro ⟨Λ, hΛ⟩
      obtain ⟨J, hJ⟩ := exists_id_on_wider_strip hα h hs (show (0 : ℝ) ≤ 0 from le_rfl)
      have hi := (eint 0 le_rfl).mp ⟨Λ.comp J, fun f u hu ↦ hΛ f (J u) ((hJ u).trans hu)⟩
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
      linarith
    · rcases hc with hh | ⟨hh, _⟩ <;> change α < |z.re| at h <;> linarith

end RiemannMasullo.SharpStripEval
