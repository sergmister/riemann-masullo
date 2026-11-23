module

public import RiemannMasullo.Research.StripNuclearity.Resolvent

/-!
The admitted Mellin functionals construct the radial spectral projection directly on the weighted space.
-/

@[expose] public noncomputable section
open Function MeasureTheory Set

namespace RiemannMasullo.StripNuclearity

/-- The orthogonal complement of the common kernel is separated by its moments,
and the orthogonal projection preserves each individual moment. -/
private theorem common_kernel_projection {E J : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (Λ : J → StrongDual ℂ E) :
    let N := ⨅ l, (Λ l).ker
    let P := N.orthogonal.starProjection
    (∀ x ∈ P.toLinearMap.range, (∀ l, Λ l x = 0) → x = 0) ∧
      ∀ l x, Λ l (P x) = Λ l x := by
  intro N P
  have hN : IsClosed (N : Set E) := by
    simp only [N, Submodule.coe_iInf]
    exact isClosed_iInter fun l ↦ (Λ l).isClosed_ker
  let : CompleteSpace N := hN.completeSpace_coe
  have hmem (x : E) : x ∈ N ↔ ∀ l, Λ l x = 0 := by
    change x ∈ ⨅ l, (Λ l).ker ↔ _
    rw [Submodule.mem_iInf]
    rfl
  constructor
  · rintro x ⟨v, rfl⟩ h
    let y : N.orthogonal := ⟨P v, N.orthogonal.starProjection_apply_mem v⟩
    exact congrArg Subtype.val ((Submodule.mem_left_iff_eq_zero_of_disjoint (x := y)
      N.orthogonal_disjoint).mp ((hmem _).mpr h))
  · intro l x
    have hdiff : x - P x ∈ N := by
      rw [show x-P x = N.starProjection x from sub_eq_of_eq_add (N.starProjection_add_starProjection_orthogonal _).symm]
      exact N.starProjection_apply_mem x
    exact (sub_eq_zero.mp (by simpa only [map_sub] using (hmem _).mp hdiff l)).symm

universe uJet

/-- Uniform trace norm on a family of scalar spectral components. At fixed width
and Sobolev order the resolvent and constant are common to every admissible
divisor, including divisors with boundary jets. -/
theorem exists_scalar_resolvent_on_admitted_jets_uniform {α s : ℝ} (ha : 0 ≤ α) (hs : 0 ≤ s) :
    let d := α+s+2
    let E := CompactIntervalSobolev volume id (-α) α s
    let I := Ioo (-d) d
    let r := fun z : ℂ ↦ ((((d+1 : ℝ) : ℂ)^2 - z^2)⁻¹)
    ∃ (j : PositiveRealExponentialDecay I →L[ℂ] E) (R : E →L[ℂ] E) (C : ℝ), 0 ≤ C ∧
      DenseRange j ∧ (∀ p, (j p : ℝ → ℂ) =ᵐ[volume] p.val) ∧
      (∀ p, ∃ q : PositiveRealExponentialDecay I, R (j p) = j q ∧
        ∀ z, z.re ∈ I → mellin (fun t ↦ q.val (Real.log t)) z =
          r z * mellin (fun t ↦ p.val (Real.log t)) z) ∧
      ∀ {ι : Type uJet} (w : ι → ℂ) (m : ι → ℕ) (_ : ∀ i, 0 < m i)
        (_ : Summable fun i ↦ (m i : ℝ) / (1+|(w i).im|)^2)
        (_ : ∀ i (l : Fin (m i)), (w i).re ∈ Ioo (-α) α ∨
          (w i).re ∈ Icc (-α) α ∧ 2 * (l.val : ℝ) + 1 < s),
        let J := Σ i, Fin (m i)
        let W := ∑' i, (m i : ℝ)/(1+|(w i).im|)^2
        ∃ Λ : J → StrongDual ℂ E,
          (∀ (l : J) p, Λ l (j p) = iteratedDeriv l.2.val
            (mellin (fun t ↦ p.val (Real.log t))) (w l.1)) ∧
          let P := (⨅ l, (Λ l).ker).orthogonal.starProjection
          ∃ hn : IsNuclearOperator (R.adjoint.comp P),
            traceNorm ⟨R.adjoint.comp P,hn⟩ ≤ C*(1+W)^(2:ℕ) := by
  intro d E I r
  let β := α+s+1
  let A := α+1
  let L := (d+|A|)+1
  let k := (Real.pi/2)/L
  have hL : 0 < L := by dsimp [L,d]; linarith [abs_nonneg A]
  have hk : 0 < k := div_pos (by positivity) hL
  have hβ : 2*α+s < 2*β := by dsimp [β]; linarith
  have hd : β < d := by dsimp [β,d]; linarith
  have hwidth : k*(d+|A|) < Real.pi/2 := by
    calc
      _ < k*L := mul_lt_mul_of_pos_left (lt_add_one _) hk
      _ = _ := div_mul_cancel₀ _ hL.ne'
  obtain ⟨j,R,C,hC,hdense,hjrep,hr,hu⟩ := exists_projected_scalar_resolvent_uniform.{uJet}
    ha hs hβ hd hk hwidth
  refine ⟨j,R,C,hC,hdense,hjrep,hr,?_⟩
  intro ι w m hm hsum hj J W
  have hw (i : ι) : |(w i).re| < d := by
    rcases hj i ⟨0, hm i⟩ with ⟨hx,hy⟩ | ⟨⟨hx,hy⟩,-⟩ <;>
      exact abs_lt.mpr ⟨by linarith, by linarith⟩
  have h0 (i : ι) : stripBlaschkeToDisk (A : ℂ) k (w i) ≠ 0 := by
    intro he
    have harg : |(w i).re-A| < (Real.pi/2)/k :=
      (abs_sub _ _).trans_lt ((add_lt_add_left (hw i) _).trans_le ((le_div_iff₀ hk).mpr (by linarith)))
    have hinv := stripBlaschkeFromDisk_toDisk (w₀ := (A:ℂ)) (w := w i) hk (by simpa using harg)
    rw [he] at hinv
    have hp : (w i).re = A := by simpa [stripBlaschkeFromDisk] using (congrArg Complex.re hinv).symm
    rcases hj i ⟨0,hm i⟩ with ⟨-,hy⟩ | ⟨⟨-,hy⟩,-⟩ <;> dsimp [A] at hp <;> linarith
  have hΛ (l : J) : ∃ L : StrongDual ℂ E, ∀ p : PositiveRealExponentialDecay I,
      L (j p) = iteratedDeriv l.2.val (mellin (fun t ↦ p.val (Real.log t))) (w l.1) := by
    obtain ⟨L,hL⟩ := scalarIntervalSobolev_admitted_mellin_functional (-α) α s hs (w l.1) l.2.val (hj _ _)
    exact ⟨L, fun p ↦ hL I isOpen_Ioo (abs_lt.mp (hw l.1)) p _ (hjrep p)⟩
  choose Λ hΛ using hΛ
  have hP := common_kernel_projection Λ
  let P := (⨅ l, (Λ l).ker).orthogonal.starProjection
  obtain ⟨hn,hb⟩ := hu w m hm hsum hw h0 P (isSelfAdjoint_starProjection _) Λ hP.1 hP.2 hΛ
  exact ⟨Λ,hΛ,hn,hb.trans (mul_le_of_le_one_right (by positivity) (Submodule.starProjection_norm_le _))⟩

/-- The radial resolvent on the spectral component of a prescribed admissible
Mellin divisor is trace class after projection. Both the projection and every
moment are constructed on the actual weighted space. -/
theorem exists_scalar_resolvent_on_admitted_jets {ι : Type*} (w : ι → ℂ) (m : ι → ℕ)
    (hm : ∀ i, 0 < m i) (hsum : Summable fun i ↦ (m i : ℝ) / (1+|(w i).im|)^2)
    {α s : ℝ} (ha : 0 ≤ α) (hs : 0 ≤ s)
    (hj : ∀ i (l : Fin (m i)), (w i).re ∈ Ioo (-α) α ∨
      (w i).re ∈ Icc (-α) α ∧ 2 * (l.val : ℝ) + 1 < s) :
    let d := α+s+2
    let E := CompactIntervalSobolev volume id (-α) α s
    let I := Ioo (-d) d
    let J := Σ i, Fin (m i)
    let r := fun z : ℂ ↦ ((((d+1 : ℝ) : ℂ)^2 - z^2)⁻¹)
    ∃ (j : PositiveRealExponentialDecay I →L[ℂ] E) (R : E →L[ℂ] E) (Λ : J → StrongDual ℂ E),
      DenseRange j ∧ (∀ p, (j p : ℝ → ℂ) =ᵐ[volume] p.val) ∧
      (∀ p, ∃ q : PositiveRealExponentialDecay I, R (j p) = j q ∧
        ∀ z, z.re ∈ I → mellin (fun t ↦ q.val (Real.log t)) z =
          r z * mellin (fun t ↦ p.val (Real.log t)) z) ∧
      (∀ (l : J) p, Λ l (j p) = iteratedDeriv l.2.val
        (mellin (fun t ↦ p.val (Real.log t))) (w l.1)) ∧
      IsNuclearOperator (R.adjoint.comp ((⨅ l, (Λ l).ker).orthogonal.starProjection)) := by
  intro d E I J r
  obtain ⟨j,R,C,-,hdense,hjrep,hr,hu⟩ := exists_scalar_resolvent_on_admitted_jets_uniform ha hs
  obtain ⟨Λ,hΛ,hn,-⟩ := hu w m hm hsum hj
  exact ⟨j,R,Λ,hdense,hjrep,hr,hΛ,hn⟩

end RiemannMasullo.StripNuclearity
