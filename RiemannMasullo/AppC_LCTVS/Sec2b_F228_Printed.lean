module

public import RiemannMasullo.AppC_LCTVS.Sec2b

/-! # Appendix C.2.4: the printed continuity claim for the strong-dual pairing -/

@[expose] public noncomputable section

namespace RiemannMasullo

universe u v

/-- Paper: After (C.2.4.9), p. 691. As printed: for every complete nuclear Hausdorff
locally convex complex space E, a continuous linear map T to its strong dual
makes (x, y) ↦ (Ty)(x) jointly continuous. This is the continuity clause of the
specialization. The statement `schwartz_kernel_series` assumes joint continuity.
See ERRATA F228. -/
def Printed.strongDual_pairing_continuous : Prop :=
  ∀ (E : Type u) [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    [PolynormableSpace ℂ E] [T2Space E] [CompleteSpace E],
    IsNuclearTVS.{v, u} E → ∀ T : E →L[ℂ] StrongDual ℂ E,
      Continuous (fun z : E × E ↦ T z.2 z.1)

/-- Joint evaluation would bound every functional in some strong-dual neighborhood
on a fixed neighborhood of zero. Such a dual neighborhood contains all multiples
of any functional vanishing on its defining bounded set. -/
private theorem strongDual_pairing_not_continuous {M : Type u} [AddCommGroup M]
    [Module ℂ M] (hM : ¬ FiniteDimensional ℂ M) :
    ¬ Continuous (fun z : FinestLocallyConvex M × StrongDual ℂ (FinestLocallyConvex M) ↦
      z.2 z.1) := by
  classical
  intro hc
  let D := FinestLocallyConvex M
  let Ω := StrongDual ℂ D
  have hU : IsOpen ((fun z : D × Ω ↦ z.2 z.1) ⁻¹' Metric.ball 0 1) :=
    Metric.isOpen_ball.preimage hc
  have h0 : ((0 : D), (0 : Ω)) ∈ (fun z : D × Ω ↦ z.2 z.1) ⁻¹' Metric.ball 0 1 := by simp
  obtain ⟨V, W, hV, hW, h₀V, h₀W, hVW⟩ := isOpen_prod_iff.mp hU _ _ h0
  obtain ⟨⟨B, U⟩, ⟨hB, hU₀⟩, hBW⟩ :=
    ContinuousLinearMap.hasBasis_nhds_zero.mem_iff.mp (hW.mem_nhds h₀W)
  obtain ⟨S, hS, hBS, _⟩ := (finestLocallyConvex_isVonNBounded_iff B).mp hB
  obtain ⟨x, hx⟩ : ∃ x : D, x ∉ S := by
    by_contra! h
    apply hM
    exact Module.Finite.of_surjective S.subtype fun y ↦
      ⟨⟨y, h y⟩, rfl⟩
  obtain ⟨f, hfx, hfS⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
  let : ContinuousSMul ℂ D := (finestLocallyConvex_withSeminorms M).continuousSMul
  have hscalar : Continuous (fun a : ℂ ↦ a • x) := continuous_id.smul continuous_const
  obtain ⟨ε, hε, hsmall⟩ := Metric.mem_nhds_iff.mp
    ((hV.preimage hscalar).mem_nhds (show (0 : ℂ) ∈ (fun a : ℂ ↦ a • x) ⁻¹' V by
      simpa using h₀V))
  obtain ⟨a, ha, haε⟩ := NormedField.exists_norm_lt ℂ hε
  have hax : a • x ∈ V := hsmall (by simpa [Metric.mem_ball, dist_zero_right] using haε)
  have hfaz : f (a • x) ≠ 0 := by simpa using mul_ne_zero (norm_pos_iff.mp ha) hfx
  let g : D →ₗ[ℂ] ℂ := (f (a • x))⁻¹ • f
  let φ : Ω := ⟨g, continuous_of_finestLocallyConvex M g⟩
  have hφ : φ ∈ W := by
    apply hBW
    intro y hy
    have hfy : f y = 0 := by
      have hb : f y ∈ S.map f := Submodule.mem_map_of_mem (hBS hy)
      simpa [hfS] using hb
    change g y ∈ U
    have hg : g y = 0 := by
      change (f (a • x))⁻¹ * f y = 0
      rw [hfy, mul_zero]
    exact hg ▸ mem_of_mem_nhds hU₀
  have h := hVW (show (a • x, φ) ∈ V ×ˢ W from ⟨hax, hφ⟩)
  change (f (a • x))⁻¹ * f (a • x) ∈ Metric.ball 0 1 at h
  rw [inv_mul_cancel₀ hfaz] at h
  simp at h

/-- Paper: After (C.2.4.9), p. 691. Take E = ω × φ, where ω = ℂ^ℕ has the product
topology and φ = ℂ^(ℕ) has the finest locally convex topology. Both factors are
complete and nuclear. Set T(y, b)(x, a) = ∑ₙ aₙ yₙ. The φ-projection of each
bounded set is supported on finitely many coordinates, so T is continuous in the
strong dual topology. Every zero-neighborhood in ω leaves some coordinate
unrestricted, and every zero-neighborhood in φ contains a nonzero multiple of its
basis vector. Hence the pairing is unbounded on every product of zero-neighborhoods. -/
theorem Printed.strongDual_pairing_continuous_false :
    ¬ Printed.strongDual_pairing_continuous := by
  classical
  let ι := ULift ℕ
  let M := ι →₀ ℂ
  let D := FinestLocallyConvex M
  let Ω := StrongDual ℂ D
  have hRank : Module.rank ℂ M = Cardinal.aleph0 := by
    simp [M, ι]
  have hM : ¬ FiniteDimensional ℂ M := by
    intro h
    exact (not_lt_of_ge hRank.ge) (Module.rank_lt_aleph0 ℂ M)
  let : CompleteSpace D := finestLocallyConvex_completeSpace (E := M)
  obtain ⟨_, _, _, hComplete⟩ := finestLocallyConvex_strongDual_isFrechetTVS hRank.le
  let : CompleteSpace Ω := by
    rw [← IsUniformAddGroup.rightUniformSpace_eq (G := Ω)]
    exact hComplete
  -- The strong dual of D has the product topology on its basis coordinates.
  -- Present the two factors as a dependent product to use isNuclearTVS_pi.
  let X : Bool → Type _ := fun b ↦ match b with
    | false => D
    | true => Ω
  let : ∀ b, AddCommGroup (X b) := fun b ↦ by cases b <;> exact inferInstance
  let : ∀ b, Module ℂ (X b) := fun b ↦ by cases b <;> exact inferInstance
  let : ∀ b, UniformSpace (X b) := fun b ↦ by cases b <;> exact inferInstance
  let : ∀ b, IsUniformAddGroup (X b) := fun b ↦ by cases b <;> exact inferInstance
  let : ∀ b, CompleteSpace (X b) := fun b ↦ by cases b <;> exact inferInstance
  let E := (b : Bool) → X b
  have hNX (b : Bool) : IsNuclearTVS (X b) := by
    cases b
    · exact finestLocallyConvex_isNuclearTVS hRank.le
    · exact finestLocallyConvex_strongDual_isNuclearTVS hRank.le
  have hN : IsNuclearTVS E := isNuclearTVS_pi hNX
  let : PolynormableSpace ℂ E := hN.2.1
  let : T2Space E := hN.1
  let p : E →L[ℂ] D := ContinuousLinearMap.proj false
  let q : E →L[ℂ] Ω := ContinuousLinearMap.proj true
  let jD : D →L[ℂ] E := ContinuousLinearMap.single ℂ X false
  let jΩ : Ω →L[ℂ] E := ContinuousLinearMap.single ℂ X true
  let T : E →L[ℂ] StrongDual ℂ E := (p.precomp ℂ).comp q
  intro h
  have hc := h E hN T
  have hh := hc.comp ((jD.continuous.comp continuous_fst).prodMk
    (jΩ.continuous.comp continuous_snd))
  apply strongDual_pairing_not_continuous hM
  refine hh.congr fun z ↦ ?_
  change ((Pi.single (M := X) true z.2) true) ((Pi.single (M := X) false z.1) false) = z.2 z.1
  simp only [Pi.single_eq_same]

end RiemannMasullo
