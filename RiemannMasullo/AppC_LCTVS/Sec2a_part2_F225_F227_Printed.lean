module

public import RiemannMasullo.AppC_LCTVS.Sec2a_part2
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Cardinal.Cofinality.Club
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.Ordinal.Topology
import Mathlib.Topology.ContinuousMap.LocallyConvex
import Mathlib.Topology.InductiveDimension.Classes
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Data.Set.FiniteExhaustion
import Mathlib.Topology.Algebra.Indicator
import Mathlib.Topology.Algebra.UniformConvergence
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.RCLike.Lemmas

/-! # Appendix C.2.3: printed claims on tensor operators, limits and bornological spaces -/

@[expose] public noncomputable section

namespace RiemannMasullo

open Bornology Topology UniformSpace
open scoped TensorProduct

universe u v i j

/-- Paper: Remark C.2.3.2, p. 677. As printed: every finite-rank continuous linear
operator from the dual of a Hausdorff locally convex space with the μ-topology to a Hausdorff
locally convex space with its weak topology is represented by a tensor. This is the
image inclusion omitted by `tensorDualOperator_finiteRank` and
`tensorDualOperator_continuous_mu`. See ERRATA F225. -/
def Printed.tensorDualOperator_represents_finiteRank : Prop :=
  ∀ (E : Type u) [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    [PolynormableSpace ℂ E] [T2Space E]
    (F : Type v) [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    [PolynormableSpace ℂ F] [T2Space F]
    (T : StrongDual ℂ E →ₗ[ℂ] F),
    FiniteDimensional ℂ (LinearMap.range T) →
    @Continuous _ (WeakSpace ℂ F) (completionCompactDualTopology E) _
      (fun φ ↦ toWeakSpace ℂ F (T φ)) →
    ∃ z : E ⊗[ℂ] F, tensorDualOperator z = T

/-- A non-complete normed space refutes the representation claim. -/
private theorem tensorDualOperator_represents_finiteRank_false_of_not_complete
    (E : Type u) [NormedAddCommGroup E] [NormedSpace ℂ E] (hE : ¬ CompleteSpace E) :
    ¬ Printed.tensorDualOperator_represents_finiteRank.{u, v} := by
  intro H
  have hex : ∃ h : Completion E, h ∉ Set.range ((↑) : E → Completion E) := by
    by_contra hc
    push Not at hc
    exact hE (((Completion.isUniformInducing_coe E).completeSpace_congr
      fun h ↦ hc h).mpr inferInstance)
  obtain ⟨h, hh⟩ := hex
  let ev : StrongDual ℂ E →ₗ[ℂ] ℂ :=
    { toFun := fun φ ↦ φ.fromCompletion h
      map_add' := fun φ ψ ↦ congrArg (fun T : Completion E →L[ℂ] ℂ ↦ T h)
        (ContinuousLinearMap.fromCompletion_unique (φ + ψ)
          (φ.fromCompletion + ψ.fromCompletion) fun e ↦ by simp)
      map_smul' := fun c φ ↦ congrArg (fun T : Completion E →L[ℂ] ℂ ↦ T h)
        (ContinuousLinearMap.fromCompletion_unique (c • φ)
          (c • φ.fromCompletion) fun e ↦ by simp) }
  let T : StrongDual ℂ E →ₗ[ℂ] ULift.{v} ℂ :=
    (ULift.moduleEquiv : ULift.{v} ℂ ≃ₗ[ℂ] ℂ).symm.toLinearMap ∘ₗ ev
  have hfin : FiniteDimensional ℂ (LinearMap.range T) := by
    have : FiniteDimensional ℂ (ULift.{v} ℂ) :=
      Module.Finite.equiv (ULift.moduleEquiv : ULift.{v} ℂ ≃ₗ[ℂ] ℂ).symm
    infer_instance
  have hcont' : @Continuous _ (WeakSpace ℂ (ULift.{v} ℂ)) (completionCompactDualTopology E) _
      (fun φ ↦ toWeakSpace ℂ (ULift.{v} ℂ) (T φ)) := by
    let : TopologicalSpace (StrongDual ℂ E) := completionCompactDualTopology E
    let K : Set (Set (Completion E)) := {A | IsCompact A}
    have hext : Continuous (fun φ : StrongDual ℂ E ↦
        UniformOnFun.ofFun K (φ.fromCompletion : Completion E → ℂ)) := continuous_induced_dom
    have heval : Continuous (fun φ : StrongDual ℂ E ↦ φ.fromCompletion h) :=
      (UniformOnFun.uniformContinuous_eval_of_mem (β := ℂ) K (Set.mem_singleton h)
        isCompact_singleton).continuous.comp hext
    exact (toWeakSpaceCLM ℂ (ULift.{v} ℂ)).continuous.comp (continuous_uliftUp.comp heval)
  obtain ⟨z, hz⟩ := H E (ULift.{v} ℂ) T hfin hcont'
  let L : E ⊗[ℂ] ULift.{v} ℂ →ₗ[ℂ] E :=
    (TensorProduct.rid ℂ E).toLinearMap ∘ₗ
      TensorProduct.map LinearMap.id (ULift.moduleEquiv : ULift.{v} ℂ ≃ₗ[ℂ] ℂ).toLinearMap
  have key : ∀ (w : E ⊗[ℂ] ULift.{v} ℂ) (φ : StrongDual ℂ E),
      (tensorDualOperator w φ).down = φ (L w) := by
    intro w φ
    induction w using TensorProduct.inductionOn with
    | tmul x y =>
      rw [tensorDualOperator_tmul]
      simp [L, mul_comm]
    | add a b ha hb => simp [ha, hb]
  have heq : ∀ φ : StrongDual ℂ E, φ.fromCompletion h = φ (L z) := by
    intro φ
    rw [← key z φ, hz]
    rfl
  obtain ⟨ψ, hψ⟩ := SeparatingDual.exists_separating_of_ne (R := ℂ)
    (x := h) (y := ((L z : E) : Completion E)) fun e ↦ hh ⟨_, e.symm⟩
  have hφ : (ψ.comp (Completion.toComplL (S := ℂ))).fromCompletion = ψ :=
    ContinuousLinearMap.fromCompletion_unique _ _ fun e ↦ rfl
  apply hψ
  have := heq (ψ.comp (Completion.toComplL (S := ℂ)))
  rw [hφ] at this
  exact this

/-- The finitely supported vectors of ℓ²(ℕ) (index lifted to `Type u`) are not complete. -/
private theorem tensorDualOperator_represents_finiteRank_false_span_not_complete :
    ¬ CompleteSpace (Submodule.span ℂ
      (Set.range fun i : ULift.{u} ℕ ↦ lp.single (E := fun _ : ULift.{u} ℕ ↦ ℂ) 2 i (1 : ℂ)) :
        Submodule ℂ (lp (fun _ : ULift.{u} ℕ ↦ ℂ) 2)) := by
  set D := Submodule.span ℂ
    (Set.range fun i : ULift.{u} ℕ ↦ lp.single (E := fun _ : ULift.{u} ℕ ↦ ℂ) 2 i (1 : ℂ)) with hD
  intro hc
  have hcl : IsClosed (D : Set (lp (fun _ : ULift.{u} ℕ ↦ ℂ) 2)) :=
    (completeSpace_coe_iff_isComplete.mp hc).isClosed
  have hmem : Memℓp (fun i : ULift.{u} ℕ ↦ (1 / 2 : ℂ) ^ i.down) 2 := by
    refine memℓp_gen ?_
    have hs : Summable (fun n : ℕ ↦ ((1 / 4 : ℝ)) ^ n) :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    refine (Equiv.ulift.{u}.symm.summable_iff).mp ?_
    convert hs using 1
    funext n
    simp only [Function.comp_apply, Equiv.ulift_symm_down, norm_pow, norm_div, norm_one,
      Complex.norm_ofNat, ENNReal.toReal_ofNat]
    rw [Real.rpow_two, ← pow_mul, mul_comm, pow_mul]
    norm_num
  let x : lp (fun _ : ULift.{u} ℕ ↦ ℂ) 2 := ⟨_, hmem⟩
  have hxD : x ∈ D := by
    refine hcl.mem_of_tendsto (lp.hasSum_single (by norm_num) x)
      (Filter.Eventually.of_forall fun s ↦ D.sum_mem fun i _ ↦ ?_)
    have : lp.single (E := fun _ : ULift.{u} ℕ ↦ ℂ) 2 i (x i) =
        x i • lp.single (E := fun _ : ULift.{u} ℕ ↦ ℂ) 2 i (1 : ℂ) := by
      rw [← lp.single_smul, smul_eq_mul, mul_one]
    rw [this]
    exact D.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
  have hfin : ∀ y ∈ D, (Function.support (y : ULift.{u} ℕ → ℂ)).Finite := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      refine (Set.finite_singleton i).subset ?_
      rw [lp.coeFn_single]
      exact Pi.support_single_subset
    | zero =>
      rw [lp.coeFn_zero, Function.support_zero]
      exact Set.finite_empty
    | add a b _ _ ha hb =>
      rw [lp.coeFn_add]
      exact (ha.union hb).subset (Function.support_add _ _)
    | smul c a _ ha =>
      rw [lp.coeFn_smul]
      exact ha.subset (Function.support_const_smul_subset c _)
  have hsupp : Function.support (x : ULift.{u} ℕ → ℂ) = Set.univ := by
    ext i
    simp [x]
  exact Set.infinite_univ (hsupp ▸ hfin x hxD)

/-- Paper: Remark C.2.3.2, p. 677. Take E to be the finitely supported complex
sequences with the ℓ² norm and F to be ℂ. In the completion of E the vector with
coordinates 2⁻ⁿ, n ≥ 0, defines a rank-one evaluation on E′, μ-continuous by the
singleton compact set. Each tensor with scalar second factor evaluates at a finitely
supported vector. The coordinate functionals distinguish that vector from (2⁻ⁿ). -/
theorem Printed.tensorDualOperator_represents_finiteRank_false :
    ¬ Printed.tensorDualOperator_represents_finiteRank :=
  tensorDualOperator_represents_finiteRank_false_of_not_complete _
    tensorDualOperator_represents_finiteRank_false_span_not_complete

attribute [local instance] uniformContinuousConstSMul_of_continuousConstSMul

/-- The map induced on completed inductive tensors by two continuous linear maps. -/
def Printed.completedInductiveTensorMap {E F A B : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [PolynormableSpace ℂ E] [T2Space E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [PolynormableSpace ℂ F] [T2Space F]
    [AddCommGroup A] [Module ℂ A] [TopologicalSpace A] [PolynormableSpace ℂ A] [T2Space A]
    [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] [PolynormableSpace ℂ B] [T2Space B]
    (f : E →L[ℂ] A) (g : F →L[ℂ] B) :
    Completion (InductiveTensor E F) →ₗ[ℂ] Completion (InductiveTensor A B) :=
  let T : InductiveTensor E F →L[ℂ] InductiveTensor A B :=
    ⟨inductiveTensorMap f.toLinearMap g.toLinearMap, inductiveTensorMap_continuous f g⟩
  T.completion.toLinearMap

/-- Paper: Proposition C.2.3.13(2), p. 683. As printed: the canonical map (C.2.3.27)
from the locally convex direct limit of the completed inductive tensor stages to the
completed inductive tensor of the two Hausdorff limits is a topological embedding.
This is the embedding clause. See `completedInductiveTensor_isQuotientMap_stageSpan`,
`completedInductiveTensor_stages_dense` and ERRATA F226. -/
def Printed.completedInductiveTensor_directLimits_isEmbedding : Prop :=
  ∀ (I : Type i) (J : Type j) [Preorder I] [Preorder J] [DecidableEq I] [DecidableEq J]
    [Nonempty I] [Nonempty J] [IsDirectedOrder I] [IsDirectedOrder J]
    (X : I → Type u) (Y : J → Type v)
    [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)] [∀ i, TopologicalSpace (X i)]
    [∀ i, PolynormableSpace ℂ (X i)] [∀ i, T2Space (X i)]
    [∀ j, AddCommGroup (Y j)] [∀ j, Module ℂ (Y j)] [∀ j, TopologicalSpace (Y j)]
    [∀ j, PolynormableSpace ℂ (Y j)] [∀ j, T2Space (Y j)]
    (f : ∀ i j, i ≤ j → X i →ₗ[ℂ] X j) [DirectedSystem X (f · · ·)]
    (g : ∀ i j, i ≤ j → Y i →ₗ[ℂ] Y j) [DirectedSystem Y (g · · ·)]
    (hf : ∀ i j h, Continuous (f i j h)) (hg : ∀ i j h, Continuous (g i j h))
    [@T2Space _ (lcDirectLimitTopology f)] [@T2Space _ (lcDirectLimitTopology g)],
    let u := Module.DirectLimit.of ℂ I X f
    let v := Module.DirectLimit.of ℂ J Y g
    letI := lcDirectLimitTopology f
    letI := lcDirectLimitTopology g
    let Z (p : I × J) := Completion (InductiveTensor (X p.1) (Y p.2))
    let transition (p q : I × J) (h : p ≤ q) : Z p →ₗ[ℂ] Z q :=
      Printed.completedInductiveTensorMap
        ⟨f p.1 q.1 h.1, hf p.1 q.1 h.1⟩ ⟨g p.2 q.2 h.2, hg p.2 q.2 h.2⟩
    letI := lcDirectLimitTopology transition
    ∃ T : Module.DirectLimit Z transition →ₗ[ℂ]
        Completion (InductiveTensor (Module.DirectLimit X f) (Module.DirectLimit Y g)),
      (∀ p z, T (Module.DirectLimit.of ℂ (I × J) Z transition p z) =
        Completion.map (inductiveTensorMap (u p.1) (v p.2)) z) ∧ IsEmbedding T

/-- Coordinates of the tail projection that zeroes the first `m` coordinates of ℓ². -/
private theorem completedInductiveTensor_directLimits_isEmbedding_false_proj_apply
    (m : ℕ) (y : lp (fun _ : ULift.{u} ℕ ↦ ℂ) 2) (k : ULift.{u} ℕ) :
    ((ContinuousLinearMap.id ℂ (lp (fun _ : ULift.{u} ℕ ↦ ℂ) 2) -
      ∑ n ∈ Finset.range m, (lp.evalCLM ℂ (fun _ : ULift.{u} ℕ ↦ ℂ) 2 (ULift.up n)).smulRight
        (lp.single (E := fun _ : ULift.{u} ℕ ↦ ℂ) 2 (ULift.up n) (1 : ℂ))) y : _) k =
      if k.down < m then 0 else y k := by
  rw [sub_apply, sum_apply, lp.coeFn_sub,
    lp.coeFn_sum, Pi.sub_apply, Finset.sum_apply]
  simp only [ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply, lp.coeFn_smul,
    Pi.smul_apply, lp.coeFn_single, smul_eq_mul]
  have : ∀ n ∈ Finset.range m, lp.evalCLM ℂ (fun _ : ULift.{u} ℕ ↦ ℂ) 2 (ULift.up n) y *
      Pi.single (M := fun _ : ULift.{u} ℕ ↦ ℂ) (ULift.up n) (1 : ℂ) k = if n = k.down then y k else 0 := by
    intro n _
    by_cases h : n = k.down
    · subst h
      simp
      rfl
    · have hk : k ≠ ULift.up n := fun e ↦ h (by rw [e])
      simp [h, hk]
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
  simp only [Finset.mem_range]
  split_ifs <;> simp

/-- Elements of the span of the coordinate vectors of ℓ² vanish beyond some index. -/
private theorem completedInductiveTensor_directLimits_isEmbedding_false_eventually_zero
    (y : lp (fun _ : ULift.{u} ℕ ↦ ℂ) 2)
    (hy : y ∈ Submodule.span ℂ (Set.range fun n : ULift.{u} ℕ ↦
      lp.single (E := fun _ : ULift.{u} ℕ ↦ ℂ) 2 n (1 : ℂ))) :
    ∃ N : ℕ, ∀ k : ULift.{u} ℕ, N ≤ k.down → y k = 0 := by
  have hfin : (Function.support (y : ULift.{u} ℕ → ℂ)).Finite := by
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      refine (Set.finite_singleton i).subset ?_
      rw [lp.coeFn_single]
      exact Pi.support_single_subset
    | zero =>
      rw [lp.coeFn_zero, Function.support_zero]
      exact Set.finite_empty
    | add a b _ _ ha hb =>
      rw [lp.coeFn_add]
      exact (ha.union hb).subset (Function.support_add _ _)
    | smul c a _ ha =>
      rw [lp.coeFn_smul]
      exact ha.subset (Function.support_const_smul_subset c _)
  obtain ⟨N, hN⟩ := (hfin.image ULift.down).bddAbove
  refine ⟨N + 1, fun k hk ↦ ?_⟩
  by_contra hne
  have := hN ⟨k, hne, rfl⟩
  omega

/-- A single-stage system over `PUnit` has a Hausdorff locally convex direct limit. -/
private theorem completedInductiveTensor_directLimits_isEmbedding_false_t2_single
    (V : Type v) [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] [PolynormableSpace ℂ V]
    [T2Space V] :
    @T2Space (Module.DirectLimit (fun _ : PUnit.{j + 1} ↦ V) (fun _ _ _ ↦ LinearMap.id))
      (lcDirectLimitTopology (X := fun _ : PUnit.{j + 1} ↦ V) (fun _ _ _ ↦ LinearMap.id)) := by
  let f : ∀ a b : PUnit.{j + 1}, a ≤ b → V →ₗ[ℂ] V := fun _ _ _ ↦ LinearMap.id
  let : TopologicalSpace (Module.DirectLimit (fun _ : PUnit.{j + 1} ↦ V) f) :=
    lcDirectLimitTopology (X := fun _ : PUnit.{j + 1} ↦ V) f
  let L := Module.DirectLimit (fun _ : PUnit.{j + 1} ↦ V) f
  let e := Module.DirectLimit.of ℂ PUnit.{j + 1} (fun _ ↦ V) f
  let g : L →ₗ[ℂ] V :=
    Module.DirectLimit.lift ℂ PUnit.{j + 1} (fun _ ↦ V) f (fun _ ↦ LinearMap.id)
      (fun _ _ _ _ ↦ rfl)
  have hge (x : V) : g (e PUnit.unit x) = x :=
    Module.DirectLimit.lift_of (G := fun _ ↦ V) (f := f) (fun _ ↦ LinearMap.id)
      (fun _ _ _ _ ↦ rfl) x
  have hinj : Function.Injective g := by
    intro z w hzw
    obtain ⟨⟨⟩, x, rfl⟩ := Module.DirectLimit.exists_of z
    obtain ⟨⟨⟩, y, rfl⟩ := Module.DirectLimit.exists_of w
    rw [hge, hge] at hzw
    rw [hzw]
  let P : SeminormFamily ℂ L {p : Seminorm ℂ L // ∀ k, Continuous (p ∘ e k)} := Subtype.val
  have hP : WithSeminorms P := ⟨rfl⟩
  have hV := PolynormableSpace.withSeminorms ℂ V
  have := hV.isTopologicalAddGroup
  have hg : Continuous g := hV.continuous_of_continuous_comp _ fun q ↦ by
    have hq : ∀ k, Continuous (((q.1).comp g) ∘ e k) := by
      rintro ⟨⟩
      have : ((q.1).comp g) ∘ e PUnit.unit = q.1 := funext fun x ↦ by simp [hge]
      rw [this]
      exact q.2
    exact hP.continuous_seminorm ⟨(q.1).comp g, hq⟩
  exact T2Space.of_injective_continuous hinj hg

/-- The completed inductive tensor map is continuous and acts on the dense image by the
inductive tensor map. -/
private theorem completedInductiveTensor_directLimits_isEmbedding_false_map
    {E F A B : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [PolynormableSpace ℂ E] [T2Space E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [PolynormableSpace ℂ F] [T2Space F]
    [AddCommGroup A] [Module ℂ A] [TopologicalSpace A] [PolynormableSpace ℂ A] [T2Space A]
    [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] [PolynormableSpace ℂ B] [T2Space B]
    (f : E →L[ℂ] A) (g : F →L[ℂ] B) :
    Continuous (Printed.completedInductiveTensorMap f g) ∧
      ∀ t : InductiveTensor E F, Printed.completedInductiveTensorMap f g (t : Completion _) =
        ((inductiveTensorMap f.toLinearMap g.toLinearMap t : InductiveTensor A B) :
          Completion _) := by
  let T : InductiveTensor E F →L[ℂ] InductiveTensor A B :=
    ⟨inductiveTensorMap f.toLinearMap g.toLinearMap, inductiveTensorMap_continuous f g⟩
  have h : Printed.completedInductiveTensorMap f g = T.completion.toLinearMap := rfl
  rw [h]
  exact ⟨T.completion.continuous, fun t ↦ ContinuousLinearMap.completion_apply_coe T t⟩

/-- The completed inductive tensor stages of two directed systems form a directed system. -/
private theorem completedInductiveTensor_directLimits_isEmbedding_false_directed
    {I : Type i} {J : Type j} [Preorder I] [Preorder J] (X : I → Type u) (Y : J → Type v)
    [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)] [∀ i, TopologicalSpace (X i)]
    [∀ i, PolynormableSpace ℂ (X i)] [∀ i, T2Space (X i)]
    [∀ j, AddCommGroup (Y j)] [∀ j, Module ℂ (Y j)] [∀ j, TopologicalSpace (Y j)]
    [∀ j, PolynormableSpace ℂ (Y j)] [∀ j, T2Space (Y j)]
    (f : ∀ i j, i ≤ j → X i →ₗ[ℂ] X j) [DirectedSystem X (f · · ·)]
    (g : ∀ i j, i ≤ j → Y i →ₗ[ℂ] Y j) [DirectedSystem Y (g · · ·)]
    (hf : ∀ i j h, Continuous (f i j h)) (hg : ∀ i j h, Continuous (g i j h)) :
    DirectedSystem (fun p : I × J ↦ Completion (InductiveTensor (X p.1) (Y p.2)))
      (fun (p q : I × J) (h : p ≤ q) z ↦ Printed.completedInductiveTensorMap
        ⟨f p.1 q.1 h.1, hf p.1 q.1 h.1⟩ ⟨g p.2 q.2 h.2, hg p.2 q.2 h.2⟩ z) := by
  constructor
  · intro p z
    have h : p ≤ p := le_rfl
    obtain ⟨hc, hcoe⟩ := completedInductiveTensor_directLimits_isEmbedding_false_map
      ⟨f p.1 p.1 h.1, hf p.1 p.1 h.1⟩ ⟨g p.2 p.2 h.2, hg p.2 p.2 h.2⟩
    induction z using Completion.induction_on with
    | hp => exact isClosed_eq hc continuous_id
    | ih t =>
      rw [hcoe]
      congr 1
      change TensorProduct.map (f p.1 p.1 h.1) (g p.2 p.2 h.2) t = t
      induction t using TensorProduct.inductionOn with
      | tmul x y =>
        rw [TensorProduct.map_tmul, DirectedSystem.map_self (f := (f · · ·)),
          DirectedSystem.map_self (f := (g · · ·))]
      | add a b ha hb => rw [map_add, ha, hb]
  · intro r q p hpq hqr z
    obtain ⟨hc1, hcoe1⟩ := completedInductiveTensor_directLimits_isEmbedding_false_map
      ⟨f p.1 q.1 hpq.1, hf p.1 q.1 hpq.1⟩ ⟨g p.2 q.2 hpq.2, hg p.2 q.2 hpq.2⟩
    obtain ⟨hc2, hcoe2⟩ := completedInductiveTensor_directLimits_isEmbedding_false_map
      ⟨f q.1 r.1 hqr.1, hf q.1 r.1 hqr.1⟩ ⟨g q.2 r.2 hqr.2, hg q.2 r.2 hqr.2⟩
    obtain ⟨hc3, hcoe3⟩ := completedInductiveTensor_directLimits_isEmbedding_false_map
      ⟨f p.1 r.1 (hpq.trans hqr).1, hf p.1 r.1 (hpq.trans hqr).1⟩
      ⟨g p.2 r.2 (hpq.trans hqr).2, hg p.2 r.2 (hpq.trans hqr).2⟩
    induction z using Completion.induction_on with
    | hp => exact isClosed_eq (hc2.comp hc1) hc3
    | ih t =>
      rw [hcoe1, hcoe2, hcoe3]
      congr 1
      change TensorProduct.map (f q.1 r.1 hqr.1) (g q.2 r.2 hqr.2)
        (TensorProduct.map (f p.1 q.1 hpq.1) (g p.2 q.2 hpq.2) t) =
          TensorProduct.map (f p.1 r.1 (hpq.trans hqr).1) (g p.2 r.2 (hpq.trans hqr).2) t
      induction t using TensorProduct.inductionOn with
      | tmul x y =>
        rw [TensorProduct.map_tmul, TensorProduct.map_tmul, TensorProduct.map_tmul,
          DirectedSystem.map_map (f := (f · · ·)), DirectedSystem.map_map (f := (g · · ·))]
      | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]

/-- The completion of a space with a single point has a single point. -/
private theorem completedInductiveTensor_directLimits_isEmbedding_false_completion_zero
    {α : Type*} {_ : UniformSpace α} {_ : Zero α} (h : ∀ x : α, x = 0) (c : Completion α) :
    c = 0 := by
  induction c using Completion.induction_on with
  | hp => exact isClosed_eq continuous_id continuous_const
  | ih x => rw [h x, Completion.coe_zero]

/-- Functoriality of completions for a functional evaluated after two maps. -/
private theorem completedInductiveTensor_directLimits_isEmbedding_false_key
    {E C C' : Type*} [UniformSpace E] [AddCommGroup E] [IsUniformAddGroup E] [Module ℂ E]
    [UniformContinuousConstSMul ℂ E] [UniformSpace C] [AddCommGroup C] [IsUniformAddGroup C]
    [Module ℂ C] [UniformContinuousConstSMul ℂ C] [UniformSpace C'] [AddCommGroup C']
    [IsUniformAddGroup C'] [Module ℂ C'] [UniformContinuousConstSMul ℂ C']
    (J : E →L[ℂ] C) (Ψ : C → C') (Φ : Completion C → Completion C') (hΦc : Continuous Φ)
    (hΦ : ∀ t : C, Φ t = (Ψ t : Completion C')) (ℓ : C' →L[ℂ] ℂ) (κ : E →L[ℂ] ℂ)
    (h : ∀ x, ℓ (Ψ (J x)) = κ x) (c : Completion E) :
    ℓ.fromCompletion (Φ (J.completion c)) = κ.fromCompletion c := by
  induction c using Completion.induction_on with
  | hp =>
    exact isClosed_eq (ℓ.fromCompletion.continuous.comp (hΦc.comp J.completion.continuous))
      κ.fromCompletion.continuous
  | ih x =>
    rw [ContinuousLinearMap.completion_apply_coe, hΦ, ContinuousLinearMap.fromCompletion_apply_coe,
      ContinuousLinearMap.fromCompletion_apply_coe, h]

/-- If the limit of the first system is zero and some completed stage has an element that
no transition kills, the printed embedding claim fails for the two systems. -/
private theorem completedInductiveTensor_directLimits_isEmbedding_false_of_nonvanishing
    (H : Printed.completedInductiveTensor_directLimits_isEmbedding.{u, v, i, j})
    (I : Type i) (J : Type j) [Preorder I] [Preorder J] [DecidableEq I] [DecidableEq J]
    [Nonempty I] [Nonempty J] [IsDirectedOrder I] [IsDirectedOrder J]
    (X : I → Type u) (Y : J → Type v)
    [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)] [∀ i, TopologicalSpace (X i)]
    [∀ i, PolynormableSpace ℂ (X i)] [∀ i, T2Space (X i)]
    [∀ j, AddCommGroup (Y j)] [∀ j, Module ℂ (Y j)] [∀ j, TopologicalSpace (Y j)]
    [∀ j, PolynormableSpace ℂ (Y j)] [∀ j, T2Space (Y j)]
    (f : ∀ i j, i ≤ j → X i →ₗ[ℂ] X j) [DirectedSystem X (f · · ·)]
    (g : ∀ i j, i ≤ j → Y i →ₗ[ℂ] Y j) [DirectedSystem Y (g · · ·)]
    (hf : ∀ i j h, Continuous (f i j h)) (hg : ∀ i j h, Continuous (g i j h))
    [@T2Space _ (lcDirectLimitTopology f)] [@T2Space _ (lcDirectLimitTopology g)]
    (hXsub : ∀ z : Module.DirectLimit X f, z = 0) (p0 : I × J)
    (w : Completion (InductiveTensor (X p0.1) (Y p0.2)))
    (hw : ∀ (q : I × J) (h : p0 ≤ q), Printed.completedInductiveTensorMap
      ⟨f p0.1 q.1 h.1, hf p0.1 q.1 h.1⟩ ⟨g p0.2 q.2 h.2, hg p0.2 q.2 h.2⟩ w ≠ 0) : False := by
  have hdir := completedInductiveTensor_directLimits_isEmbedding_false_directed X Y f g hf hg
  obtain ⟨T, hT, hemb⟩ := H I J X Y f g hf hg
  have hT0 : T (Module.DirectLimit.of ℂ _ _ _ p0 w) = T 0 := by
    rw [map_zero, hT]
    have hzero : ∀ r : Module.DirectLimit X f ⊗[ℂ] Module.DirectLimit Y g, r = 0 := by
      intro r
      induction r using TensorProduct.inductionOn with
      | tmul x y => rw [hXsub x, TensorProduct.zero_tmul]
      | add r₁ r₂ h₁ h₂ => rw [h₁, h₂, add_zero]
    exact completedInductiveTensor_directLimits_isEmbedding_false_completion_zero hzero _
  obtain ⟨-, hinj⟩ := hemb
  have : IsDirectedOrder (I × J) := ⟨fun a b ↦ by
    obtain ⟨c, hac, hbc⟩ := exists_ge_ge a.1 b.1
    obtain ⟨d, had, hbd⟩ := exists_ge_ge a.2 b.2
    exact ⟨(c, d), ⟨hac, had⟩, ⟨hbc, hbd⟩⟩⟩
  obtain ⟨q, hq, hqz⟩ := Module.DirectLimit.of.zero_exact (hinj hT0)
  exact hw q hq hqz

/-- The printed embedding claim fails for the tail stages of the finitely supported vectors
of ℓ², with projections as transitions, against the single stage ℂ. -/
private theorem completedInductiveTensor_directLimits_isEmbedding_false_main :
    ¬ Printed.completedInductiveTensor_directLimits_isEmbedding.{u, v, i, j} := by
  intro H
  let P : ℕ → lp (fun _ : ULift.{u} ℕ ↦ ℂ) 2 →L[ℂ] lp (fun _ : ULift.{u} ℕ ↦ ℂ) 2 := fun m ↦
    ContinuousLinearMap.id ℂ (lp (fun _ : ULift.{u} ℕ ↦ ℂ) 2) -
      ∑ n ∈ Finset.range m, (lp.evalCLM ℂ (fun _ : ULift.{u} ℕ ↦ ℂ) 2 (ULift.up n)).smulRight
        (lp.single (E := fun _ : ULift.{u} ℕ ↦ ℂ) 2 (ULift.up n) (1 : ℂ))
  have hP : ∀ m y k, (P m y : ULift.{u} ℕ → ℂ) k = if k.down < m then 0 else y k :=
    completedInductiveTensor_directLimits_isEmbedding_false_proj_apply
  have hPP : ∀ n m y, n ≤ m → P m (P n y) = P m y := by
    intro n m y hnm
    ext k
    rw [hP, hP, hP]
    split_ifs <;> first | rfl | omega
  let D : Submodule ℂ (lp (fun _ : ULift.{u} ℕ ↦ ℂ) 2) := Submodule.span ℂ
    (Set.range fun n : ULift.{u} ℕ ↦ lp.single (E := fun _ : ULift.{u} ℕ ↦ ℂ) 2 n (1 : ℂ))
  let Xs : ULift.{i} ℕ → Submodule ℂ (lp (fun _ : ULift.{u} ℕ ↦ ℂ) 2) :=
    fun n ↦ D.map (P n.down).toLinearMap
  let X : ULift.{i} ℕ → Type u := fun n ↦ Xs n
  have hmaps : ∀ n m : ULift.{i} ℕ, n ≤ m → ∀ y ∈ Xs n, P m.down y ∈ Xs m := by
    rintro n m hnm _ ⟨x, hx, rfl⟩
    exact ⟨x, hx, (hPP _ _ _ hnm).symm⟩
  let f : ∀ n m : ULift.{i} ℕ, n ≤ m → X n →ₗ[ℂ] X m := fun n m h ↦
    (P m.down).toLinearMap.restrict (hmaps n m h)
  have hfapply : ∀ n m h (x : X n), ((f n m h x : Xs m) : lp (fun _ : ULift.{u} ℕ ↦ ℂ) 2) =
      P m.down (x : lp (fun _ : ULift.{u} ℕ ↦ ℂ) 2) := fun _ _ _ _ ↦ rfl
  have hfc : ∀ n m h, Continuous (f n m h) := fun n m h ↦
    ((P m.down).continuous.comp continuous_subtype_val).subtype_mk _
  have : DirectedSystem X (f · · ·) := by
    constructor
    · rintro n ⟨_, ⟨x, hx, rfl⟩⟩
      exact Subtype.ext (hPP _ _ _ le_rfl)
    · intro a b c hab hbc x
      exact Subtype.ext (hPP _ _ _ hbc)
  have hXsub : ∀ z : Module.DirectLimit X f, z = 0 := by
    intro z
    obtain ⟨n, x, rfl⟩ := Module.DirectLimit.exists_of z
    obtain ⟨y, hy, hyx⟩ := x.2
    obtain ⟨N, hN⟩ :=
      completedInductiveTensor_directLimits_isEmbedding_false_eventually_zero y hy
    let m : ULift.{i} ℕ := ⟨max n.down N⟩
    have hnm : n ≤ m := (le_max_left n.down N : n.down ≤ max n.down N)
    have hzero : f n m hnm x = 0 := by
      apply Subtype.ext
      rw [hfapply n m hnm x, ← hyx]
      change P m.down (P n.down y) = 0
      rw [hPP _ _ _ (le_max_left _ _)]
      ext k
      rw [hP]
      split_ifs with hk
      · rfl
      · have hk' : ¬ k.down < max n.down N := hk
        exact hN k (by omega)
    rw [← Module.DirectLimit.of_f (hij := hnm), hzero, map_zero]
  have hXT2 : @T2Space _ (lcDirectLimitTopology f) := by
    let := lcDirectLimitTopology f
    exact T2Space.of_injective_continuous (Y := PUnit.{1}) (f := fun _ ↦ PUnit.unit)
      (fun a b _ ↦ (hXsub a).trans (hXsub b).symm) continuous_const
  let g : ∀ a b : PUnit.{j + 1}, a ≤ b → ULift.{v} ℂ →ₗ[ℂ] ULift.{v} ℂ :=
    fun _ _ _ ↦ LinearMap.id
  have : DirectedSystem (fun _ : PUnit.{j + 1} ↦ ULift.{v} ℂ) (g · · ·) := by
    constructor <;> intros <;> rfl
  have hYT2 : @T2Space _ (lcDirectLimitTopology g) :=
    completedInductiveTensor_directLimits_isEmbedding_false_t2_single (ULift.{v} ℂ)
  have hgc : ∀ a b h, Continuous (g a b h) := fun _ _ _ ↦ continuous_id
  -- the vector (2⁻ⁿ) of ℓ²
  have hmem : Memℓp (fun k : ULift.{u} ℕ ↦ (1 / 2 : ℂ) ^ k.down) 2 := by
    refine memℓp_gen ?_
    have hs : Summable (fun n : ℕ ↦ ((1 / 4 : ℝ)) ^ n) :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    refine (Equiv.ulift.{u}.symm.summable_iff).mp ?_
    convert hs using 1
    funext n
    simp only [Function.comp_apply, Equiv.ulift_symm_down, norm_pow, norm_div, norm_one,
      Complex.norm_ofNat, ENNReal.toReal_ofNat]
    rw [Real.rpow_two, ← pow_mul, mul_comm, pow_mul]
    norm_num
  let a : lp (fun _ : ULift.{u} ℕ ↦ ℂ) 2 := ⟨_, hmem⟩
  have hP0 : ∀ y, P 0 y = y := fun y ↦ by
    ext k
    rw [hP]
    simp
  have hsmem : ∀ N, P 0 (∑ k ∈ Finset.range N,
      lp.single (E := fun _ : ULift.{u} ℕ ↦ ℂ) 2 (ULift.up k) (a (ULift.up k))) ∈ Xs ⟨0⟩ :=
    fun N ↦ ⟨_, D.sum_mem fun k _ ↦ by
      have : lp.single (E := fun _ : ULift.{u} ℕ ↦ ℂ) 2 (ULift.up k) (a (ULift.up k)) =
          a (ULift.up k) • lp.single (E := fun _ : ULift.{u} ℕ ↦ ℂ) 2 (ULift.up k) (1 : ℂ) := by
        rw [← lp.single_smul, smul_eq_mul, mul_one]
      rw [this]
      exact D.smul_mem _ (Submodule.subset_span ⟨_, rfl⟩), rfl⟩
  let s : ℕ → X ⟨0⟩ := fun N ↦ ⟨_, hsmem N⟩
  have hs : Filter.Tendsto (fun N ↦ ((s N : Xs ⟨0⟩) : lp (fun _ : ULift.{u} ℕ ↦ ℂ) 2))
      Filter.atTop (𝓝 a) := by
    have h := (Equiv.ulift.{u}.symm.hasSum_iff).mpr (lp.hasSum_single (by norm_num) a)
    convert h.tendsto_sum_nat using 1
    funext N
    exact hP0 _
  have hcs : CauchySeq (fun N ↦ ((s N : X ⟨0⟩) : Completion (X ⟨0⟩))) := by
    have h1 : CauchySeq s := by
      unfold CauchySeq
      rw [← (isUniformEmbedding_subtype_val.isUniformInducing).cauchy_map_iff, Filter.map_map]
      exact hs.cauchySeq
    exact (Completion.uniformContinuous_coe _).comp_cauchySeq h1
  obtain ⟨b, hb⟩ := cauchySeq_tendsto_of_complete hcs
  let ι : X ⟨0⟩ →L[ℂ] lp (fun _ : ULift.{u} ℕ ↦ ℂ) 2 := (Xs ⟨0⟩).subtypeL
  have hιb : ι.fromCompletion b = a := by
    refine tendsto_nhds_unique ((ι.fromCompletion.continuous.tendsto b).comp hb) ?_
    convert hs using 1
    funext N
    simp only [Function.comp_apply, ContinuousLinearMap.fromCompletion_apply_coe]
    rfl
  have hJc : @Continuous (X ⟨0⟩) (InductiveTensor (X ⟨0⟩) (ULift.{v} ℂ)) _ _
      (fun x : X ⟨0⟩ ↦ x ⊗ₜ[ℂ] (ULift.up 1 : ULift.{v} ℂ)) :=
    (withGeneratingSeminorms_spec (X ⟨0⟩ ⊗[ℂ] ULift.{v} ℂ)
      (fun p : {p : Seminorm ℂ (X ⟨0⟩ ⊗[ℂ] ULift.{v} ℂ) //
        (∀ x : X ⟨0⟩, Continuous (fun y : ULift.{v} ℂ ↦ p (x ⊗ₜ[ℂ] y))) ∧
        (∀ y : ULift.{v} ℂ, Continuous (fun x : X ⟨0⟩ ↦ p (x ⊗ₜ[ℂ] y)))} ↦ p.val)
      ).continuous_of_continuous_comp
      ((TensorProduct.mk ℂ (X ⟨0⟩) (ULift.{v} ℂ)).flip (ULift.up 1)) fun p ↦ p.2.2 (ULift.up 1)
  let Jm : X ⟨0⟩ →L[ℂ] InductiveTensor (X ⟨0⟩) (ULift.{v} ℂ) :=
    ⟨(TensorProduct.mk ℂ (X ⟨0⟩) (ULift.{v} ℂ)).flip (ULift.up 1), hJc⟩
  let p0 : ULift.{i} ℕ × PUnit.{j + 1} := (⟨0⟩, PUnit.unit)
  let w : Completion (InductiveTensor (X p0.1) (ULift.{v} ℂ)) := Jm.completion b
  refine completedInductiveTensor_directLimits_isEmbedding_false_of_nonvanishing H
    (ULift.{i} ℕ) PUnit.{j + 1} X (fun _ ↦ ULift.{v} ℂ) f g hfc hgc hXsub p0 w ?_
  intro q hq hqz
  let m := q.1.down
  let bil : X q.1 →ₗ[ℂ] ULift.{v} ℂ →ₗ[ℂ] ℂ := (LinearMap.mul ℂ ℂ).compl₁₂
    ((lp.evalCLM ℂ (fun _ : ULift.{u} ℕ ↦ ℂ) 2 (ULift.up m)).toLinearMap ∘ₗ (Xs q.1).subtype)
    (ULift.moduleEquiv : ULift.{v} ℂ ≃ₗ[ℂ] ℂ).toLinearMap
  let ℓl : InductiveTensor (X q.1) (ULift.{v} ℂ) →ₗ[ℂ] ℂ := TensorProduct.lift bil
  have hℓ : ∀ (x : X q.1) (c : ULift.{v} ℂ),
      ℓl (x ⊗ₜ[ℂ] c) = (x : lp (fun _ : ULift.{u} ℕ ↦ ℂ) 2) (ULift.up m) * c.down :=
    fun _ _ ↦ rfl
  have hℓc : Continuous ℓl := by
    refine (continuous_inductiveTensor_iff ℓl).mpr ⟨fun x ↦ ?_, fun c ↦ ?_⟩
    · simp_rw [hℓ]
      exact continuous_const.mul continuous_uliftDown
    · simp_rw [hℓ]
      exact ((lp.evalCLM ℂ (fun _ : ULift.{u} ℕ ↦ ℂ) 2 (ULift.up m)).continuous.comp
        continuous_subtype_val).mul continuous_const
  let ℓ : InductiveTensor (X q.1) (ULift.{v} ℂ) →L[ℂ] ℂ := ⟨ℓl, hℓc⟩
  obtain ⟨hc, hcoe⟩ := completedInductiveTensor_directLimits_isEmbedding_false_map
    ⟨f p0.1 q.1 hq.1, hfc p0.1 q.1 hq.1⟩ ⟨g p0.2 q.2 hq.2, hgc p0.2 q.2 hq.2⟩
  let κ : X ⟨0⟩ →L[ℂ] ℂ := (lp.evalCLM ℂ (fun _ : ULift.{u} ℕ ↦ ℂ) 2 (ULift.up m)).comp ι
  have hκ : κ.fromCompletion b = (a : ULift.{u} ℕ → ℂ) (ULift.up m) := by
    have : κ.fromCompletion =
        (lp.evalCLM ℂ (fun _ : ULift.{u} ℕ ↦ ℂ) 2 (ULift.up m)).comp ι.fromCompletion :=
      ContinuousLinearMap.fromCompletion_unique _ _ fun x ↦ by
        simp only [κ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.fromCompletion_apply_coe]
    rw [this, ContinuousLinearMap.comp_apply, hιb]
    rfl
  have hstep : ∀ x : X ⟨0⟩, ℓ (inductiveTensorMap (f p0.1 q.1 hq.1) (g p0.2 q.2 hq.2) (Jm x)) =
      κ x := by
    intro x
    change ℓl (f p0.1 q.1 hq.1 x ⊗ₜ[ℂ] g p0.2 q.2 hq.2 (ULift.up 1)) = _
    rw [hℓ, hfapply p0.1 q.1 hq.1 x]
    change (P m (x : lp (fun _ : ULift.{u} ℕ ↦ ℂ) 2) : ULift.{u} ℕ → ℂ) (ULift.up m) * 1 =
      (x : lp (fun _ : ULift.{u} ℕ ↦ ℂ) 2) (ULift.up m)
    rw [hP]
    simp
  have key := completedInductiveTensor_directLimits_isEmbedding_false_key Jm _ _ hc hcoe ℓ κ
    hstep b
  rw [hqz, map_zero, hκ] at key
  have hne : (a : ULift.{u} ℕ → ℂ) (ULift.up m) ≠ 0 := by
    change (1 / 2 : ℂ) ^ m ≠ 0
    exact pow_ne_zero _ (by norm_num)
  exact hne key.symm

/-- Paper: Proposition C.2.3.13(2), p. 683. Take Xₙ to be the finitely supported
complex sequences with the ℓ² norm modulo the span of the first n coordinate
vectors, with the quotient maps as transitions. Take Y to be the single stage ℂ.
The X-limit and the target are zero. The completed stages are ℓ² modulo the same
coordinate spans, so the class of (2⁻ⁿ) in their limit is nonzero and maps to zero. -/
theorem Printed.completedInductiveTensor_directLimits_isEmbedding_false :
    ¬ Printed.completedInductiveTensor_directLimits_isEmbedding :=
  completedInductiveTensor_directLimits_isEmbedding_false_main

/-- A locally convex space is bornological if each seminorm bounded on its von Neumann
bounded sets is continuous. -/
def Printed.IsBornologicalTVS (E : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] :
    Prop :=
  ∀ p : Seminorm ℂ E, (∀ s : Set E, IsVonNBounded ℂ s → BddAbove (p '' s)) → Continuous p

/-- Paper: Proposition C.2.3.13(3), p. 683. As printed: the completed inductive
tensor product of two Hausdorff bornological locally convex complex spaces is
bornological. This is the bornological half. The barrelled half is
`completedInductiveTensor_barrelled`. See ERRATA F227. -/
def Printed.completedInductiveTensor_bornological : Prop :=
  ∀ (E : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [PolynormableSpace ℂ E] [T2Space E]
    (F : Type v) [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    [PolynormableSpace ℂ F] [T2Space F],
    Printed.IsBornologicalTVS E → Printed.IsBornologicalTVS F →
      Printed.IsBornologicalTVS (Completion (InductiveTensor E F))


section completedInductiveTensor_bornological_false_aux

open Set Order Function
open scoped Ordinal Cardinal Topology

/-- The scalar field is bornological: a seminorm bounded on the closed unit ball is continuous. -/
private theorem completedInductiveTensor_bornological_false_complex :
    Printed.IsBornologicalTVS ℂ := by
  intro p hp
  obtain ⟨M, hM⟩ := hp _ (NormedSpace.isVonNBounded_closedBall ℂ ℂ 1)
  have hball : p.closedBall 0 (max M 0 + 1) ∈ 𝓝 (0 : ℂ) := by
    refine Filter.mem_of_superset (Metric.closedBall_mem_nhds (0 : ℂ) zero_lt_one) ?_
    intro x hx
    rw [Seminorm.mem_closedBall_zero]
    exact (hM ⟨x, hx, rfl⟩).trans (le_of_lt <| lt_of_le_of_lt (le_max_left M 0) (lt_add_one _))
  exact p.continuous' hball

/-- The inductive tensor with the scalar field is the space itself. -/
private theorem completedInductiveTensor_bornological_false_scalar
    (E : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [PolynormableSpace ℂ E] [T2Space E] :
    Nonempty (InductiveTensor E ℂ ≃L[ℂ] E) := by
  have := PolynormableSpace.isTopologicalAddGroup ℂ E
  let e : InductiveTensor E ℂ ≃ₗ[ℂ] E := TensorProduct.rid ℂ E
  have hsp := withGeneratingSeminorms_spec (E ⊗[ℂ] ℂ)
    (fun p : {p : Seminorm ℂ (E ⊗[ℂ] ℂ) //
      (∀ x : E, Continuous (fun y : ℂ ↦ p (x ⊗ₜ[ℂ] y))) ∧
      (∀ y : ℂ, Continuous (fun x : E ↦ p (x ⊗ₜ[ℂ] y)))} ↦ p.val)
  have hcont : Continuous (e : InductiveTensor E ℂ → E) := by
    refine (continuous_inductiveTensor_iff e.toLinearMap).mpr ⟨fun x ↦ ?_, fun y ↦ ?_⟩
    · have hscalar : Continuous (fun y : ℂ ↦ y • x) := continuous_id.smul continuous_const
      have hfun : (fun y : ℂ ↦ (TensorProduct.rid ℂ E) (x ⊗ₜ[ℂ] y)) = fun y ↦ y • x :=
        funext fun y ↦ TensorProduct.rid_tmul x y
      exact hfun.symm ▸ hscalar
    · have hscalar : Continuous (fun x : E ↦ y • x) := continuous_const.smul continuous_id
      have hfun : (fun x : E ↦ (TensorProduct.rid ℂ E) (x ⊗ₜ[ℂ] y)) = fun x ↦ y • x :=
        funext fun x ↦ TensorProduct.rid_tmul x y
      exact hfun.symm ▸ hscalar
  have hcont_inv : Continuous (e.symm : E → InductiveTensor E ℂ) :=
    hsp.continuous_of_continuous_comp ((TensorProduct.mk ℂ E ℂ).flip (1 : ℂ))
      fun p ↦ p.2.2 (1 : ℂ)
  exact ⟨{ e with continuous_toFun := hcont, continuous_invFun := hcont_inv }⟩

section ScalarCompletion

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [PolynormableSpace ℂ E] [T2Space E]

local instance : IsTopologicalAddGroup E :=
  PolynormableSpace.isTopologicalAddGroup ℂ E

local instance : UniformSpace E :=
  IsTopologicalAddGroup.rightUniformSpace E

local instance : IsUniformAddGroup E :=
  isUniformAddGroup_of_addCommGroup

/-- Completion preserves the scalar identification. -/
private theorem completedInductiveTensor_bornological_false_scalar_completion :
    Nonempty (Completion (InductiveTensor E ℂ) ≃L[ℂ] Completion E) := by
  obtain ⟨e⟩ := completedInductiveTensor_bornological_false_scalar E
  let f := e.toContinuousLinearMap.completion
  let g := e.symm.toContinuousLinearMap.completion
  refine ⟨ContinuousLinearEquiv.equivOfInverse f g ?_ ?_⟩
  · intro x
    refine Completion.induction_on (p := fun x ↦ g (f x) = x) x ?_ ?_
    · exact isClosed_eq (g.continuous.comp f.continuous) continuous_id
    · intro a
      rw [ContinuousLinearMap.completion_apply_coe, ContinuousLinearMap.completion_apply_coe]
      apply congrArg (fun z : InductiveTensor E ℂ ↦ (z : Completion (InductiveTensor E ℂ)))
      exact ContinuousLinearEquiv.symm_apply_apply e a
  · intro y
    refine Completion.induction_on (p := fun y ↦ f (g y) = y) y ?_ ?_
    · exact isClosed_eq (f.continuous.comp g.continuous) continuous_id
    · intro a
      rw [ContinuousLinearMap.completion_apply_coe, ContinuousLinearMap.completion_apply_coe]
      apply congrArg (fun z : E ↦ (z : Completion E))
      exact ContinuousLinearEquiv.apply_symm_apply e a

end ScalarCompletion

/-- Bornology passes across a continuous linear equivalence. -/
private theorem completedInductiveTensor_bornological_false_transfer
    {E F : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    (e : E ≃L[ℂ] F) (hE : Printed.IsBornologicalTVS E) :
    Printed.IsBornologicalTVS F := by
  intro p hp
  have hpe : ∀ s : Set E, IsVonNBounded ℂ s →
      BddAbove ((p.comp e.toLinearMap) '' s) := by
    intro s hs
    obtain ⟨M, hM⟩ := hp _ (hs.image e.toContinuousLinearMap)
    refine ⟨M, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hM ⟨e x, ⟨x, hx, rfl⟩, rfl⟩
  have hcont : Continuous (fun x : E ↦ (p.comp e.toLinearMap) x) := hE _ hpe
  have hcomp : Continuous (fun y : F ↦ (p.comp e.toLinearMap) (e.symm y)) :=
    hcont.comp e.symm.continuous
  change Continuous (fun y : F ↦ p y)
  have hfun : (fun y : F ↦ (p.comp e.toLinearMap) (e.symm y)) = fun y ↦ p y := by
    funext y
    show (p.comp e.toLinearMap) (e.symm y) = p y
    have : p (e (e.symm y)) = p y := congrArg p (e.apply_symm_apply y)
    rw [← this]
    with_unfolding_all rfl
  exact hfun ▸ hcomp

open Set Order Function
open scoped Ordinal Cardinal

/-- Ulam's matrix splits the ordinals below `ω₁` into a stationary set with stationary complement. -/
private theorem completedInductiveTensor_bornological_false_split :
    ∃ S : Set (Iio (Ordinal.omega (1 : Ordinal.{0}))), IsStationary S ∧ IsStationary Sᶜ := by
  let Ω : Type 1 := Iio (Ordinal.omega (1 : Ordinal.{0}))
  have hcof : Order.cof Ω ≠ ℵ₀ := by
    rw [Ordinal.cof_Iio, ← Ordinal.lift_cof, Cardinal.cof_omega_one]
    exact (Cardinal.aleph0_lt_lift.mpr Cardinal.aleph0_lt_aleph_one).ne.symm
  have : NoMaxOrder Ω := (Cardinal.isSuccLimit_omega 1).isSuccPrelimit.noMaxOrder_Iio
  have : Nonempty Ω :=
    ⟨⟨0, lt_of_le_of_lt (bot_le : (⊥ : Ordinal) ≤ Ordinal.omega 0)
      (Ordinal.omega_lt_omega.mpr zero_lt_one)⟩⟩
  have hC (a : Ω) : Countable (Iio a.1) :=
    (Cardinal.countable_Iio_of_lt_omega_one a.2).to_subtype
  let f (a : Ω) : Iio a.1 → ℕ :=
    @Countable.exists_injective_nat _ (hC a) |>.choose
  have hf (a : Ω) : Injective (f a) :=
    @Countable.exists_injective_nat _ (hC a) |>.choose_spec
  let A (n : ℕ) (ξ : Ω) : Set Ω :=
    {α | ∃ h : ξ.1 < α.1, f α ⟨ξ.1, h⟩ = n}
  have hdisj (n : ℕ) {ξ η : Ω} (hne : ξ ≠ η) : Disjoint (A n ξ) (A n η) := by
    rw [Set.disjoint_left]
    intro α ⟨hξ, hξn⟩ ⟨hη, hηn⟩
    apply hne
    exact Subtype.ext
      (congrArg (Subtype.val : Iio α.1 → Ordinal) (hf α (hξn.trans hηn.symm)))
  have hsome : ∃ n : ℕ, ¬ ({ξ : Ω | IsStationary (A n ξ)}).Countable := by
    by_contra hnone
    push Not at hnone
    let U : Set Ω := ⋃ n, {ξ | IsStationary (A n ξ)}
    have hUc : U.Countable := countable_iUnion hnone
    have hCcount : Countable U := hUc.to_subtype
    have hsup : (⨆ ξ : U, ξ.1.1) < Ordinal.omega 1 :=
      Ordinal.iSup_lt_omega_one fun ξ ↦ ξ.1.2
    let σ : Ordinal := Order.succ (⨆ ξ : U, ξ.1.1)
    have hσ : σ < Ordinal.omega 1 := (Cardinal.isSuccLimit_omega 1).succ_lt hsup
    let ξ₀ : Ω := ⟨σ, hσ⟩
    have hξ₀U : ξ₀ ∉ U := by
      intro hmem
      have hle : ξ₀.1 ≤ ⨆ ξ : U, ξ.1.1 :=
        Ordinal.le_iSup (fun ξ : U ↦ ξ.1.1) ⟨ξ₀, hmem⟩
      exact (lt_succ_of_not_isMax (not_isMax_of_lt hsup)).not_ge hle
    have htail : Ioi ξ₀ ⊆ ⋃ n, A n ξ₀ := by
      intro α hα
      have hlt : ξ₀.1 < α.1 := hα
      exact mem_iUnion.mpr ⟨f α ⟨ξ₀.1, hlt⟩, ⟨hlt, rfl⟩⟩
    have hunion : IsStationary (⋃ n, A n ξ₀) :=
      ((isClub_Ioi ξ₀).isStationary hcof).mono htail
    rw [isStationary_iUnion_iff_of_countable hcof] at hunion
    obtain ⟨n, hn⟩ := hunion
    exact hξ₀U (mem_iUnion.mpr ⟨n, hn⟩)
  obtain ⟨n, hn⟩ := hsome
  let T : Set Ω := {ξ | IsStationary (A n ξ)}
  have hTne : T.Nonempty := by
    rw [nonempty_iff_ne_empty]
    intro hempty
    exact hn (by simp [T, hempty])
  obtain ⟨ξ, hξ⟩ := hTne
  have hrest : ¬ (T \ {ξ}).Countable := by
    intro hc
    apply hn
    change T.Countable
    have heq : T = insert ξ (T \ {ξ}) := by
      ext η
      simp only [mem_insert_iff, mem_sdiff, mem_singleton_iff, T]
      constructor
      · intro hη
        exact (eq_or_ne η ξ).imp id (fun hne ↦ ⟨hη, hne⟩)
      · intro hη
        rcases hη with rfl | ⟨hη, _⟩
        · exact hξ
        · exact hη
    rw [heq]
    exact hc.insert ξ
  have hrestne : (T \ {ξ}).Nonempty := by
    rw [nonempty_iff_ne_empty]
    intro hempty
    exact hrest (by simp [hempty])
  obtain ⟨η, hη⟩ := hrestne
  rw [mem_sdiff] at hη
  obtain ⟨hηT, hneq⟩ := hη
  refine ⟨A n ξ, hξ, ?_⟩
  exact hηT.mono (hdisj n hneq).symm.subset_compl_left

/-- `Iio ω₁` has the order type of a regular uncountable cardinal, so Fodor applies. -/
private theorem completedInductiveTensor_bornological_false_regular :
    IsRegularCardinalOrder (Iio (Ordinal.omega (1 : Ordinal.{0}))) := by
  refine ⟨le_of_eq ?_⟩
  have hcof : Order.cof (Iio (Ordinal.omega (1 : Ordinal.{0}))) =
      Cardinal.lift.{1} (ℵ₁ : Cardinal.{0}) := by
    rw [Ordinal.cof_Iio, ← Ordinal.lift_cof, Cardinal.cof_omega_one]
  rw [Ordinal.type_lt_Iio, hcof, ← Cardinal.lift_ord, Cardinal.ord_aleph]

/-- Limit points of a stationary subset of `Iio ω₁` form a club. -/
private theorem completedInductiveTensor_bornological_false_limitClub
    (S : Set (Iio (Ordinal.omega (1 : Ordinal.{0})))) (hS : IsStationary S) :
    IsClub {α | (∃ β, β < α) ∧ ∀ β < α, ∃ γ ∈ S, β < γ ∧ γ < α} := by
  let Ω := Iio (Ordinal.omega (1 : Ordinal.{0}))
  let C : Set Ω := {α | (∃ β, β < α) ∧ ∀ β < α, ∃ γ ∈ S, β < γ ∧ γ < α}
  have hcof : Order.cof Ω ≠ ℵ₀ := by
    rw [Ordinal.cof_Iio, ← Ordinal.lift_cof, Cardinal.cof_omega_one]
    exact (Cardinal.aleph0_lt_lift.mpr Cardinal.aleph0_lt_aleph_one).ne.symm
  change IsClub C
  have habove (β : Ω) : ∃ γ : Ω, β < γ ∧ γ ∈ S := by
    have hsucc : β.1 + 1 < Ordinal.omega (1 : Ordinal) :=
      (Cardinal.isSuccLimit_omega 1).succ_lt β.2
    obtain ⟨γ, hγS, hle⟩ := hS.isCofinal ⟨β.1 + 1, hsucc⟩
    have hβ : β.1 < β.1 + 1 :=
      lt_succ_of_not_isMax (not_isMax_of_lt (β.2 : β.1 < Ordinal.omega 1))
    refine ⟨γ, lt_of_lt_of_le hβ (Subtype.coe_le_coe.mp hle), hγS⟩
  refine ⟨?_, ?_⟩
  · intro d hd hne _ a ha
    refine ⟨?_, ?_⟩
    · obtain ⟨δ, hδ⟩ := hne
      obtain ⟨β, hβ⟩ := (hd hδ).1
      exact ⟨β, lt_of_lt_of_le hβ (ha.1 hδ)⟩
    · intro β hβ
      have : ∃ δ ∈ d, β < δ := by
        by_contra h
        push Not at h
        exact not_le_of_gt hβ (ha.2 (fun δ hδ => h δ hδ))
      obtain ⟨δ, hδd, hβδ⟩ := this
      obtain ⟨γ, hγS, hβγ, hγδ⟩ := (hd hδd).2 β hβδ
      exact ⟨γ, hγS, hβγ, lt_of_lt_of_le hγδ (ha.1 hδd)⟩
  · intro α
    let seq : ℕ → Ω := Nat.rec (Classical.choose (habove α))
      (fun _ prev => Classical.choose (habove prev))
    have hseq (n : ℕ) : seq n < seq (n + 1) ∧ seq (n + 1) ∈ S := by
      simpa [seq] using Classical.choose_spec (habove (seq n))
    have hseed : α < seq 0 ∧ seq 0 ∈ S := by
      simpa [seq] using Classical.choose_spec (habove α)
    have hbdd : BddAbove (range fun n => (seq n).1) :=
      ⟨Ordinal.omega 1, by rintro _ ⟨n, rfl⟩; exact le_of_lt (seq n).2⟩
    have hsup : (⨆ n, (seq n).1) < Ordinal.omega 1 :=
      Ordinal.iSup_lt_omega_one fun n => (seq n).2
    refine ⟨⟨⨆ n, (seq n).1, hsup⟩, ?_, ?_⟩
    · have h01 : (seq 0).1 < (seq 1).1 := by rw [Subtype.coe_lt_coe]; exact (hseq 0).1
      refine ⟨⟨seq 0, lt_of_lt_of_le h01 (le_ciSup hbdd 1)⟩, ?_⟩
      intro β hβ
      obtain ⟨n, hn⟩ := exists_lt_of_lt_ciSup (f := fun n => (seq n).1) hβ
      have hstep : (seq n).1 < (seq (n + 1)).1 := by
        rw [Subtype.coe_lt_coe]; exact (hseq n).1
      have hstep' : (seq (n + 1)).1 < (seq (n + 2)).1 := by
        rw [Subtype.coe_lt_coe]; exact (hseq (n + 1)).1
      refine ⟨seq (n + 1), (hseq n).2, hn.trans hstep,
        lt_of_lt_of_le hstep' (le_ciSup hbdd (n + 2))⟩
    · have hα : α.1 ≤ (seq 0).1 := by
        rw [Subtype.coe_le_coe]; exact le_of_lt hseed.1
      exact le_trans hα (le_ciSup hbdd 0)

/-- For each `ε`, past some ordinal all values of `f` on stationary `S` lie within `2ε`. -/
private theorem completedInductiveTensor_bornological_false_epsTail
    (S : Set (Iio (Ordinal.omega (1 : Ordinal.{0})))) (hS : IsStationary S)
    (f : S → ℂ) (hf : Continuous f) {ε : ℝ} (hε : 0 < ε) :
    ∃ β : Iio (Ordinal.omega (1 : Ordinal.{0})),
      ∀ (γ γ' : Iio (Ordinal.omega (1 : Ordinal.{0}))) (hγ : γ ∈ S) (hγ' : γ' ∈ S),
        β < γ → β < γ' → dist (f ⟨γ, hγ⟩) (f ⟨γ', hγ'⟩) < 2 * ε := by
  classical
  let bot0 : Iio (Ordinal.omega (1 : Ordinal.{0})) :=
    ⟨0, lt_of_le_of_lt (bot_le : (⊥ : Ordinal) ≤ Ordinal.omega 0)
      (Ordinal.omega_lt_omega.mpr zero_lt_one)⟩
  have hcof : Order.cof (Iio (Ordinal.omega (1 : Ordinal.{0}))) ≠ ℵ₀ := by
    rw [Ordinal.cof_Iio, ← Ordinal.lift_cof, Cardinal.cof_omega_one]
    exact (Cardinal.aleph0_lt_lift.mpr Cardinal.aleph0_lt_aleph_one).ne.symm
  have : NoMaxOrder (Iio (Ordinal.omega (1 : Ordinal.{0}))) :=
    (Cardinal.isSuccLimit_omega 1).isSuccPrelimit.noMaxOrder_Iio
  have := completedInductiveTensor_bornological_false_regular
  have hS' : IsStationary (S \ {bot0}) := by
    have hsub : S ⊆ (S \ {bot0}) ∪ {bot0} := by
      intro x hx
      by_cases hxb : x = bot0
      · exact Or.inr hxb
      · exact Or.inl ⟨hx, hxb⟩
    rcases (isStationary_union_iff hcof).mp (hS.mono hsub) with h | h
    · exact h
    · exact absurd h (not_isStationary_singleton bot0)
  have key : ∀ (α : Iio (Ordinal.omega (1 : Ordinal.{0}))) (hα : α ∈ S \ {bot0}),
      ∃ l, l < α ∧ ∀ (γ : Iio (Ordinal.omega (1 : Ordinal.{0}))) (hγ : γ ∈ S),
        l < γ → γ ≤ α → dist (f ⟨γ, hγ⟩) (f ⟨α, hα.1⟩) < ε := by
    intro α hα
    have hev := Metric.continuousAt_iff'.mp (hf.continuousAt (x := ⟨α, hα.1⟩)) ε hε
    rw [Filter.eventually_iff, mem_nhds_subtype] at hev
    obtain ⟨u, hu, husub⟩ := hev
    have hbl : bot0 < α := by
      refine lt_of_le_of_ne ?_ (fun h => hα.2 (Set.mem_singleton_iff.mpr h.symm))
      refine Subtype.coe_le_coe.mp ?_
      show (0 : Ordinal) ≤ (α : Ordinal)
      rw [← Ordinal.bot_eq_zero]
      exact bot_le
    obtain ⟨l, hl, hIoc⟩ := exists_Ioc_subset_of_mem_nhds hu ⟨bot0, hbl⟩
    exact ⟨l, hl, fun γ hγ hlγ hγα => husub (hIoc ⟨hlγ, hγα⟩)⟩
  choose g hg1 hg2 using key
  obtain ⟨β₀, hT⟩ := exists_isStationary_preimage_singleton
    (f := fun α => if h : α ∈ S \ {bot0} then g α h else bot0) hcof hS'
    (fun α hα => by rw [dite_eq_left hα]; exact hg1 α hα)
  refine ⟨β₀, fun γ γ' hγ hγ' hβγ hβγ' => ?_⟩
  obtain ⟨α', hα'T, hmax⟩ := hT.isCofinal (max γ γ')
  obtain ⟨hα'S', hα'g⟩ := hα'T
  have hgval : g α' hα'S' = β₀ := by
    have h : (if h : α' ∈ S \ {bot0} then g α' h else bot0) = β₀ :=
      Set.mem_singleton_iff.mp hα'g
    rwa [dite_eq_left hα'S'] at h
  have h1 : dist (f ⟨γ, hγ⟩) (f ⟨α', hα'S'.1⟩) < ε := by
    refine hg2 α' hα'S' γ hγ ?_ (le_trans (le_max_left γ γ') hmax)
    rw [hgval]; exact hβγ
  have h2 : dist (f ⟨γ', hγ'⟩) (f ⟨α', hα'S'.1⟩) < ε := by
    refine hg2 α' hα'S' γ' hγ' ?_ (le_trans (le_max_right γ γ') hmax)
    rw [hgval]; exact hβγ'
  calc dist (f ⟨γ, hγ⟩) (f ⟨γ', hγ'⟩)
      ≤ dist (f ⟨γ, hγ⟩) (f ⟨α', hα'S'.1⟩) + dist (f ⟨γ', hγ'⟩) (f ⟨α', hα'S'.1⟩) :=
        dist_triangle_right _ _ _
    _ < ε + ε := add_lt_add h1 h2
    _ = 2 * ε := (two_mul ε).symm

/-- A continuous complex function on a stationary subset of `ω₁` is constant on a tail. -/
private theorem completedInductiveTensor_bornological_false_constantTail
    (S : Set (Iio (Ordinal.omega (1 : Ordinal.{0})))) (hS : IsStationary S)
    (f : S → ℂ) (hf : Continuous f) :
    ∃ (β : Iio (Ordinal.omega (1 : Ordinal.{0}))) (c : ℂ),
      ∀ (α : Iio (Ordinal.omega (1 : Ordinal.{0}))) (hα : α ∈ S), β < α → f ⟨α, hα⟩ = c := by
  choose B hB using fun n : ℕ =>
    completedInductiveTensor_bornological_false_epsTail S hS f hf
      (ε := ((n : ℝ) + 1)⁻¹) (by positivity)
  have hsup : (⨆ n, (B n).1) < Ordinal.omega 1 :=
    Ordinal.iSup_lt_omega_one fun n => (B n).2
  let β : Iio (Ordinal.omega (1 : Ordinal.{0})) := ⟨⨆ n, (B n).1, hsup⟩
  have hBle : ∀ n, B n ≤ β := fun n =>
    Subtype.coe_le_coe.mp (Ordinal.le_iSup (fun n => (B n).1) n)
  have hsucc : β.1 + 1 < Ordinal.omega 1 := (Cardinal.isSuccLimit_omega 1).succ_lt hsup
  obtain ⟨γ₀, hγ₀S, hle⟩ := hS.isCofinal ⟨β.1 + 1, hsucc⟩
  have hββ1 : β.1 < β.1 + 1 :=
    lt_succ_of_not_isMax (not_isMax_of_lt (β.2 : β.1 < Ordinal.omega 1))
  have hβγ₀ : β < γ₀ := lt_of_lt_of_le hββ1 (Subtype.coe_le_coe.mp hle)
  refine ⟨β, f ⟨γ₀, hγ₀S⟩, fun α hα hβα => ?_⟩
  refine eq_of_forall_dist_le fun ε hε => ?_
  obtain ⟨n, hn⟩ := exists_nat_gt (2 / ε)
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hn1 : 2 / ε < (n : ℝ) + 1 := hn.trans (lt_add_one _)
  have h2 : 2 < ((n : ℝ) + 1) * ε := by
    rwa [div_lt_iff₀ hε] at hn1
  have hεn : 2 * ((n : ℝ) + 1)⁻¹ < ε := by
    rw [mul_comm ((n : ℝ) + 1) ε] at h2
    rwa [mul_inv_lt_iff₀ hpos]
  have hd := hB n α γ₀ hα hγ₀S
    (lt_of_le_of_lt (hBle n) hβα) (lt_of_le_of_lt (hBle n) hβγ₀)
  exact le_of_lt (lt_trans hd hεn)

/-- A continuous linear equivalence completes to one, for the uniform structures already on
both sides. -/
private theorem completedInductiveTensor_bornological_false_completionEquiv
    {E F : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    [UniformContinuousConstSMul ℂ E] [AddCommGroup F] [Module ℂ F] [UniformSpace F]
    [IsUniformAddGroup F] [UniformContinuousConstSMul ℂ F] (e : E ≃L[ℂ] F) :
    Nonempty (Completion E ≃L[ℂ] Completion F) := by
  let f := e.toContinuousLinearMap.completion
  let g := e.symm.toContinuousLinearMap.completion
  refine ⟨ContinuousLinearEquiv.equivOfInverse f g ?_ ?_⟩
  · intro x
    refine Completion.induction_on (p := fun x ↦ g (f x) = x) x ?_ ?_
    · exact isClosed_eq (g.continuous.comp f.continuous) continuous_id
    · intro a
      rw [ContinuousLinearMap.completion_apply_coe, ContinuousLinearMap.completion_apply_coe]
      apply congrArg (fun z : E ↦ (z : Completion E))
      exact ContinuousLinearEquiv.symm_apply_apply e a
  · intro y
    refine Completion.induction_on (p := fun y ↦ f (g y) = y) y ?_ ?_
    · exact isClosed_eq (f.continuous.comp g.continuous) continuous_id
    · intro a
      rw [ContinuousLinearMap.completion_apply_coe, ContinuousLinearMap.completion_apply_coe]
      apply congrArg (fun z : F ↦ (z : Completion F))
      exact ContinuousLinearEquiv.apply_symm_apply e a

/-- The inductive tensor with a lifted copy of `ℂ` is the inductive tensor with `ℂ`.
The second factor of the printed statement lives in `Type v`. -/
private theorem completedInductiveTensor_bornological_false_ulift
    (E : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [PolynormableSpace ℂ E] [T2Space E] :
    Nonempty (InductiveTensor E (ULift.{v} ℂ) ≃L[ℂ] E) := by
  have := PolynormableSpace.isTopologicalAddGroup ℂ E
  let e₀ : E ⊗[ℂ] ULift.{v} ℂ ≃ₗ[ℂ] E ⊗[ℂ] ℂ :=
    TensorProduct.congr (LinearEquiv.refl ℂ E) (ULift.moduleEquiv : ULift.{v} ℂ ≃ₗ[ℂ] ℂ)
  let e : InductiveTensor E (ULift.{v} ℂ) ≃ₗ[ℂ] E :=
    e₀.trans (TensorProduct.rid ℂ E)
  have hsp := withGeneratingSeminorms_spec (E ⊗[ℂ] ULift.{v} ℂ)
    (fun p : {p : Seminorm ℂ (E ⊗[ℂ] ULift.{v} ℂ) //
      (∀ x : E, Continuous (fun y : ULift.{v} ℂ ↦ p (x ⊗ₜ[ℂ] y))) ∧
      (∀ y : ULift.{v} ℂ, Continuous (fun x : E ↦ p (x ⊗ₜ[ℂ] y)))} ↦ p.val)
  have hcont : Continuous (e : InductiveTensor E (ULift.{v} ℂ) → E) := by
    refine (continuous_inductiveTensor_iff e.toLinearMap).mpr ⟨fun x ↦ ?_, fun y ↦ ?_⟩
    · have hscalar : Continuous (fun z : ℂ ↦ z • x) := continuous_id.smul continuous_const
      have hfun : (fun y : ULift.{v} ℂ ↦ e (x ⊗ₜ[ℂ] y)) = fun y ↦ y.down • x :=
        funext fun y ↦ by
          have h1 : (e₀.trans (TensorProduct.rid ℂ E)) (x ⊗ₜ[ℂ] y) =
              (TensorProduct.rid ℂ E) (e₀ (x ⊗ₜ[ℂ] y)) := rfl
          unfold e₀ at h1
          rw [TensorProduct.congr_tmul, LinearEquiv.refl_apply, ULift.moduleEquiv_apply,
            TensorProduct.rid_tmul] at h1
          exact h1
      exact hfun.symm ▸ hscalar.comp continuous_uliftDown
    · have hscalar : Continuous (fun x : E ↦ y.down • x) := continuous_const.smul continuous_id
      have hfun : (fun x : E ↦ e (x ⊗ₜ[ℂ] y)) = fun x ↦ y.down • x :=
        funext fun x ↦ by
          have h1 : (e₀.trans (TensorProduct.rid ℂ E)) (x ⊗ₜ[ℂ] y) =
              (TensorProduct.rid ℂ E) (e₀ (x ⊗ₜ[ℂ] y)) := rfl
          unfold e₀ at h1
          rw [TensorProduct.congr_tmul, LinearEquiv.refl_apply, ULift.moduleEquiv_apply,
            TensorProduct.rid_tmul] at h1
          exact h1
      exact hfun.symm ▸ hscalar
  have hcont_mk :=
    hsp.continuous_of_continuous_comp
      ((TensorProduct.mk ℂ E (ULift.{v} ℂ)).flip (ULift.up (1 : ℂ)))
      fun p ↦ p.2.2 (ULift.up (1 : ℂ))
  have hinv : (e.symm : E → InductiveTensor E (ULift.{v} ℂ)) =
      (TensorProduct.mk ℂ E (ULift.{v} ℂ)).flip (ULift.up (1 : ℂ)) := by
    funext x
    have hs : (e₀.trans (TensorProduct.rid ℂ E)).symm =
        (TensorProduct.rid ℂ E).symm.trans e₀.symm := rfl
    have h1 : ((TensorProduct.rid ℂ E).symm.trans e₀.symm) x =
        e₀.symm ((TensorProduct.rid ℂ E).symm x) := rfl
    rw [← hs] at h1
    unfold e₀ at h1
    rw [TensorProduct.rid_symm_apply, TensorProduct.congr_symm_tmul,
      ULift.moduleEquiv_symm_apply, LinearEquiv.refl_symm, LinearEquiv.refl_apply] at h1
    exact h1
  exact ⟨{ e with
    continuous_toFun := hcont
    continuous_invFun := by
      change Continuous (e.symm : E → InductiveTensor E (ULift.{v} ℂ))
      exact hinv.symm ▸ hcont_mk }⟩

/-- One bornological space whose right-uniform completion is not bornological refutes the
printed claim. The second factor is `ULift.{v} ℂ`, since the statement quantifies a space
in `Type v`. -/
private theorem completedInductiveTensor_bornological_false_fromBad
    (hpack : ∃ (E : Type u) (hA : AddCommGroup E) (hM : Module ℂ E) (hT : TopologicalSpace E)
      (hP : PolynormableSpace ℂ E) (h2 : T2Space E),
      letI : AddCommGroup E := hA
      letI : Module ℂ E := hM
      letI : TopologicalSpace E := hT
      letI : PolynormableSpace ℂ E := hP
      letI : T2Space E := h2
      letI : IsTopologicalAddGroup E := PolynormableSpace.isTopologicalAddGroup ℂ E
      letI : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
      letI : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
      Printed.IsBornologicalTVS E ∧ ¬ Printed.IsBornologicalTVS (Completion E)) :
    ¬ Printed.completedInductiveTensor_bornological.{u, v} := by
  intro H
  obtain ⟨E, hA, hM, hT, hP, h2, hpair⟩ := hpack
  let : AddCommGroup E := hA
  let : Module ℂ E := hM
  let : TopologicalSpace E := hT
  let : PolynormableSpace ℂ E := hP
  let : T2Space E := h2
  let : IsTopologicalAddGroup E := PolynormableSpace.isTopologicalAddGroup ℂ E
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  obtain ⟨hE, hbad⟩ := hpair
  have hF : Printed.IsBornologicalTVS (ULift.{v} ℂ) :=
    completedInductiveTensor_bornological_false_transfer
      (ContinuousLinearEquiv.ulift (R₁ := ℂ) (M₁ := ℂ)).symm
      completedInductiveTensor_bornological_false_complex
  obtain ⟨eU⟩ := completedInductiveTensor_bornological_false_ulift E
  obtain ⟨eC⟩ := completedInductiveTensor_bornological_false_completionEquiv eU
  exact hbad <| completedInductiveTensor_bornological_false_transfer eC <|
    H E (ULift.{v} ℂ) hE hF

open Filter

section

variable {X : Type*} [TopologicalSpace X]
private def clopenNull (p : Seminorm ℂ C(X, ℂ)) (U : Set X) : Prop :=
  ∀ f : C(X, ℂ), (∀ x ∉ U, f x = 0) → p f = 0

private theorem clopenNull_mono {p : Seminorm ℂ C(X, ℂ)} {U V : Set X}
    (h : clopenNull p V) (hUV : U ⊆ V) : clopenNull p U :=
  fun f hf => h f (fun x hx => hf x (mt (@hUV x) hx))

private theorem clopenNull_union {p : Seminorm ℂ C(X, ℂ)} {U V : Set X}
    (hU : IsClopen U) (h1 : clopenNull p U) (h2 : clopenNull p V) :
    clopenNull p (U ∪ V) := by
  classical
  intro f hf
  let g : C(X, ℂ) := ⟨U.indicator f, hU.continuous_indicator f.continuous⟩
  have hg : p g = 0 := h1 g fun x hx => indicator_of_notMem hx _
  have hh : p (f - g) = 0 := by
    apply h2
    intro x hx
    by_cases h : x ∈ U
    · simp [g, h]
    · simp [g, h, hf x (fun hUV => hUV.elim h hx)]
  have hb := map_add_le_add p (f - g) g
  simpa [hg, hh] using le_antisymm (by simpa [hg, hh] using hb) (apply_nonneg p f)

private theorem clopenNull_fin {ι : Type*} (p : Seminorm ℂ C(X, ℂ)) (V : ι → Set X)
    (s : Finset ι) (hV : ∀ i ∈ s, IsClopen (V i)) (hN : ∀ i ∈ s, clopenNull p (V i)) :
    clopenNull p (⋃ i ∈ s, V i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty]
    intro f hf
    have : f = 0 := ContinuousMap.ext fun x => hf x (notMem_empty x)
    simp [this]
  | insert a s ha ih =>
    simp only [Finset.set_biUnion_insert]
    exact clopenNull_union (hV _ (Finset.mem_insert_self ..)) (hN _ (Finset.mem_insert_self ..))
      (ih (fun i hi => hV i (Finset.mem_insert_of_mem hi))
        (fun i hi => hN i (Finset.mem_insert_of_mem hi)))

private theorem seminorm_null_finite_complement [LindelofSpace X]
    (p : Seminorm ℂ C(X, ℂ))
    (hp : ∀ s : Set C(X, ℂ), IsVonNBounded ℂ s → BddAbove (p '' s))
    (U : X → Set X) (hU : ∀ x, IsClopen (U x)) (hxU : ∀ x, x ∈ U x) :
    ∃ a : Finset X, clopenNull p (⋃ x ∈ a, U x)ᶜ := by
  classical
  obtain ⟨t, ht, htU⟩ := countable_cover_nhds (fun x => (hU x).isOpen.mem_nhds (hxU x))
  let e := ht.finiteExhaustion
  let V (n : ℕ) := ⋃ x ∈ e n, U x
  have hopen (n : ℕ) : IsOpen (V n) := isOpen_iUnion fun x => isOpen_iUnion fun _ => (hU x).isOpen
  have hmono : Monotone V := fun n m hnm => iUnion₂_mono' fun x hx =>
    ⟨x, (OrderHomClass.mono e hnm hx), Subset.rfl⟩
  have hcov : ⋃ n, V n = univ := by
    ext y
    simp only [mem_iUnion, mem_univ, iff_true, V]
    obtain ⟨x, hx, hy⟩ : ∃ x ∈ t, y ∈ U x := by simpa [← htU] using (mem_univ y)
    obtain ⟨n, hn⟩ : ∃ n, x ∈ e n := by rwa [← mem_iUnion, e.iUnion_eq]
    exact ⟨n, x, hn, hy⟩
  by_contra! h
  have hbad (n : ℕ) : ∃ f : C(X, ℂ), (∀ x ∈ V n, f x = 0) ∧ n < p f := by
    have H := h ((e.finite n).toFinset)
    simp only [Set.Finite.mem_toFinset, clopenNull, mem_compl_iff, not_not] at H
    push Not at H
    obtain ⟨g, hg, hpg⟩ := H
    have hpos := lt_of_le_of_ne (apply_nonneg p g) (Ne.symm hpg)
    let a : ℝ := (n + 1) / p g
    have ha : 0 < a := div_pos (by positivity) hpos
    refine ⟨(a : ℂ) • g, fun x hx => by simp [hg x hx], ?_⟩
    rw [map_smul_eq_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
    dsimp [a]
    rw [div_mul_cancel₀ _ hpg]
    linarith
  choose f hf hpf using hbad
  have hconv : Tendsto f atTop (𝓝 0) := by
    apply ContinuousMap.tendsto_nhds_compactOpen.mpr
    intro K hK W _ hW
    obtain ⟨a, ha⟩ := hK.elim_finite_subcover V hopen (by rw [hcov]; exact subset_univ _)
    filter_upwards [eventually_ge_atTop (a.sup id)] with n hn
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (ha hx)
    rw [hf n x (hmono (le_trans (Finset.le_sup (f := id) hi) hn) hxi)]
    exact hW hx
  obtain ⟨M, hM⟩ := hp _ (hconv.isVonNBounded_range ℂ)
  obtain ⟨n, hn⟩ := exists_nat_gt M
  exact ((hpf n).trans_le (hM ⟨f n, mem_range_self _, rfl⟩)).not_ge hn.le

private def seminormSupport (p : Seminorm ℂ C(X, ℂ)) : Set X :=
  {x | ∀ U : Set X, IsClopen U → x ∈ U → ¬ clopenNull p U}

private theorem seminorm_support_finite [LindelofSpace X]
    (p : Seminorm ℂ C(X, ℂ))
    (hp : ∀ s : Set C(X, ℂ), IsVonNBounded ℂ s → BddAbove (p '' s))
    (U : X → Set X) (hU : ∀ x ∈ seminormSupport p, IsClopen (U x) ∧ x ∈ U x) :
    ∃ a : Finset X, (∀ x ∈ a, x ∈ seminormSupport p) ∧
      clopenNull p (⋃ x ∈ a, U x)ᶜ ∧ seminormSupport p ⊆ ⋃ x ∈ a, U x := by
  classical
  have hloc (x : X) : ∃ V : Set X, IsClopen V ∧ x ∈ V ∧
      (x ∈ seminormSupport p → V = U x) ∧ (x ∉ seminormSupport p → clopenNull p V) := by
    by_cases h : x ∈ seminormSupport p
    · exact ⟨U x, (hU x h).1, (hU x h).2, fun _ => rfl, fun hn => (hn h).elim⟩
    · have h' := h
      simp only [seminormSupport, mem_ofPred_eq, not_forall] at h'
      obtain ⟨V, hV, hx, hnull⟩ := h'
      exact ⟨V, hV, hx, fun hx => (h hx).elim, fun _ => not_not.mp hnull⟩
  choose V hV hxV hVU hVN using hloc
  obtain ⟨b, hb⟩ := seminorm_null_finite_complement p hp V hV hxV
  let a := b.filter (· ∈ seminormSupport p)
  let d := b.filter (· ∉ seminormSupport p)
  have ha (x : X) (hx : x ∈ a) : x ∈ seminormSupport p := (Finset.mem_filter.mp hx).2
  have hnull := clopenNull_fin p V d (fun x _ => hV x) (fun x hx => hVN x (Finset.mem_filter.mp hx).2)
  have hbig := clopenNull_union (isClopen_biUnion_finset (fun x (_ : x ∈ b) => hV x)).compl hb hnull
  have hcomp : clopenNull p (⋃ x ∈ a, U x)ᶜ := by
    apply clopenNull_mono hbig
    intro y hy
    by_cases h : y ∈ ⋃ x ∈ b, V x
    · obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.mp h
      have hx' : x ∉ seminormSupport p := by
        intro hk
        apply hy
        exact mem_iUnion₂.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hk⟩, hVU x hk ▸ hyx⟩
      exact Or.inr (mem_iUnion₂.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hx'⟩, hyx⟩)
    · exact Or.inl h
  refine ⟨a, ha, hcomp, fun y hy => ?_⟩
  by_contra h
  exact hy _ (isClopen_biUnion_finset (fun x hx => (hU x (ha x hx)).1)).compl h hcomp

private theorem seminormSupport_compact [ZeroDimensionalSpace X] [LindelofSpace X]
    (p : Seminorm ℂ C(X, ℂ))
    (hp : ∀ s : Set C(X, ℂ), IsVonNBounded ℂ s → BddAbove (p '' s)) :
    IsCompact (seminormSupport p) := by
  classical
  refine isCompact_of_finite_subcover fun {ι} W hW hcov => ?_
  cases isEmpty_or_nonempty ι with
  | inl hi => exact ⟨∅, by simpa using hcov⟩
  | inr hi =>
    have hchoice (x : X) : ∃ (i : ι) (U : Set X),
        x ∈ seminormSupport p → IsClopen U ∧ x ∈ U ∧ U ⊆ W i := by
      by_cases h : x ∈ seminormSupport p
      · obtain ⟨i, hi⟩ := mem_iUnion.mp (hcov h)
        obtain ⟨U, hU⟩ := exists_isClopen_mem_of_isOpen (hW i) hi
        exact ⟨i, U, fun _ => hU⟩
      · exact ⟨Classical.choice ‹Nonempty ι›, ∅, fun hx => (h hx).elim⟩
    choose i U hU using hchoice
    obtain ⟨a, ha, _, hca⟩ := seminorm_support_finite p hp U
      (fun x hx => ⟨(hU x hx).1, (hU x hx).2.1⟩)
    refine ⟨a.image i, fun y hy => ?_⟩
    obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.mp (hca hy)
    exact mem_iUnion₂.mpr ⟨i x, Finset.mem_image_of_mem i hx, (hU x (ha x hx)).2.2 hyx⟩

private theorem uniformUnitBall_bounded :
    IsVonNBounded ℂ {f : C(X, ℂ) | ∀ x, ‖f x‖ ≤ 1} := by
  apply isVonNBounded_of_smul_tendsto_zero (l := 𝓝[≠] (0 : ℂ)) (ε := id) self_mem_nhdsWithin
  intro g hg
  apply ContinuousMap.tendsto_nhds_compactOpen.mpr
  intro K _ W hW hKW
  rcases K.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · exact .of_forall fun _ => mapsTo_empty _ _
  have hz : (0 : ℂ) ∈ W := hKW hx
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds hz)
  filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (0 : ℂ) hr)] with c hc
  intro y _
  apply hball
  simp only [Metric.mem_ball, dist_zero_right] at hc ⊢
  change ‖c * g c y‖ < r
  exact (norm_mul_le _ _).trans_lt ((mul_le_of_le_one_right (norm_nonneg c) (hg c y)).trans_lt hc)

/-- A seminorm on the compact-open space of a zero-dimensional Lindelöf domain, bounded on
each von Neumann bounded set, is controlled by its compact support. -/
private theorem bornological_continuousMap_zeroDimensional_lindelof (X : Type*) [TopologicalSpace X]
    [ZeroDimensionalSpace X] [LindelofSpace X] : Printed.IsBornologicalTVS C(X, ℂ) := by
  classical
  intro p hp
  obtain ⟨M, hM⟩ := hp _ (uniformUnitBall_bounded (X := X))
  let K := seminormSupport p
  have hK : IsCompact K := seminormSupport_compact p hp
  apply p.continuous' (r := max M 0 + 1)
  have hnh := ContinuousMap.eventually_mapsTo (f := (0 : C(X, ℂ))) hK
    (Metric.isOpen_ball (x := (0 : ℂ)) (ε := 1)) (fun x _ => Metric.mem_ball_self zero_lt_one)
  filter_upwards [hnh] with f hf
  have hloc (x : X) : ∃ U : Set X, x ∈ K → IsClopen U ∧ x ∈ U ∧
      U ⊆ f ⁻¹' Metric.ball (0 : ℂ) 1 := by
    by_cases hx : x ∈ K
    · obtain ⟨V, hV⟩ := exists_isClopen_mem_of_isOpen
        (Metric.isOpen_ball.preimage f.continuous) (hf hx)
      exact ⟨V, fun _ => hV⟩
    · exact ⟨∅, fun h => (hx h).elim⟩
  choose U hU using hloc
  obtain ⟨a, ha, hnull, _⟩ := seminorm_support_finite p hp U
      (fun x hx => ⟨(hU x hx).1, (hU x hx).2.1⟩)
  let W := ⋃ x ∈ a, U x
  have hW : IsClopen W := isClopen_biUnion_finset (fun x hx => (hU x (ha x hx)).1)
  let g : C(X, ℂ) := ⟨W.indicator f, hW.continuous_indicator f.continuous⟩
  have hg : ∀ x, ‖g x‖ ≤ 1 := by
    intro x
    by_cases hx : x ∈ W
    · obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp hx
      have ht := (hU y (ha y hy)).2.2 hxy
      simpa [g, hx, Metric.mem_ball] using (show ‖f x‖ ≤ 1 by simpa [Metric.mem_ball] using (le_of_lt (show dist (f x) 0 < 1 from ht)))
    · simp [g, hx]
  have hdiff : p (f - g) = 0 := hnull _ (fun x hx => by
    have hx' : x ∈ W := not_not.mp hx
    simp [g, hx'])
  have hle : p f ≤ p g := by simpa [hdiff] using map_add_le_add p (f - g) g
  rw [Seminorm.mem_closedBall_zero]
  exact hle.trans ((hM ⟨g, hg, rfl⟩).trans ((le_max_left M 0).trans (le_of_lt (lt_add_one _))))

end

private def omegaOne : Ordinal.{0} := Ordinal.omega 1
local notation "OmegaOne" => Iio omegaOne

private theorem omegaOne_noMax : NoMaxOrder OmegaOne :=
  (Cardinal.isSuccLimit_omega 1).isSuccPrelimit.noMaxOrder_Iio

/-- The value on a final segment is uniquely specified. -/
private theorem stationaryTail_unique {S : Set OmegaOne} (hS : IsStationary S)
    {f : S → ℂ} {a b : OmegaOne} {c d : ℂ}
    (hc : ∀ x : S, a < x.1 → f x = c)
    (hd : ∀ x : S, b < x.1 → f x = d) : c = d := by
  let := omegaOne_noMax
  obtain ⟨y, hy⟩ := exists_gt (max a b)
  obtain ⟨z, hz, he⟩ := hS.isCofinal y
  exact (hc ⟨z, hz⟩ ((le_max_left a b).trans_lt (hy.trans_le he))).symm.trans
    (hd ⟨z, hz⟩ ((le_max_right a b).trans_lt (hy.trans_le he)))

private theorem stationaryTail_exists {S : Set OmegaOne} (hS : IsStationary S)
    (f : C(S, ℂ)) : ∃ c : ℂ, ∃ b : OmegaOne, ∀ x : S, b < x.1 → f x = c := by
  obtain ⟨b, c, hc⟩ := completedInductiveTensor_bornological_false_constantTail S hS f f.continuous
  exact ⟨c, b, fun x hx ↦ hc x.1 x.2 hx⟩

/-- Evaluation at the eventual constant value on a stationary set. -/
private def stationaryTail {S : Set OmegaOne} (hS : IsStationary S) : C(S, ℂ) →ₗ[ℂ] ℂ where
  toFun f := (stationaryTail_exists hS f).choose
  map_add' f g := by
    obtain ⟨a, ha⟩ := (stationaryTail_exists hS f).choose_spec
    obtain ⟨b, hb⟩ := (stationaryTail_exists hS g).choose_spec
    obtain ⟨c, hc⟩ := (stationaryTail_exists hS (f + g)).choose_spec
    apply stationaryTail_unique hS hc (b := max a b)
    intro x hx
    change f x + g x = _
    rw [ha x ((le_max_left a b).trans_lt hx), hb x ((le_max_right a b).trans_lt hx)]
  map_smul' r f := by
    obtain ⟨a, ha⟩ := (stationaryTail_exists hS f).choose_spec
    obtain ⟨b, hb⟩ := (stationaryTail_exists hS (r • f)).choose_spec
    apply stationaryTail_unique hS hb (b := a)
    intro x hx
    change r • f x = _
    rw [ha x hx]
    rfl

private theorem stationaryTail_spec {S : Set OmegaOne} (hS : IsStationary S)
    (f : C(S, ℂ)) : ∃ b : OmegaOne, ∀ x : S, b < x.1 → f x = stationaryTail hS f :=
  (stationaryTail_exists hS f).choose_spec

private theorem stationaryTail_bounded {S : Set OmegaOne} (hS : IsStationary S)
    {B : Set C(S, ℂ)} (hB : IsVonNBounded ℂ B) :
    BddAbove (((normSeminorm ℂ ℂ).comp (stationaryTail hS)) '' B) := by
  classical
  by_contra hb
  have hlarge (n : ℕ) : ∃ f ∈ B, (n : ℝ) < ‖stationaryTail hS f‖ := by
    by_contra hn
    push Not at hn
    exact hb ⟨n, by rintro _ ⟨f, hf, rfl⟩; exact hn f hf⟩
  choose f hf hnorm using hlarge
  choose b hb' using fun n ↦ stationaryTail_spec hS (f n)
  have hsup : (⨆ n, (b n).1) < Ordinal.omega 1 :=
    Ordinal.iSup_lt_omega_one fun n ↦ (b n).2
  let := omegaOne_noMax
  obtain ⟨y, hy⟩ := exists_gt (⟨_, hsup⟩ : OmegaOne)
  obtain ⟨z, hz, he⟩ := hS.isCofinal y
  let x : S := ⟨z, hz⟩
  let ev : C(S, ℂ) →L[ℂ] ℂ :=
    { toFun := fun g ↦ g x
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      cont := continuous_eval_const x }
  obtain ⟨M, hM⟩ := (NormedSpace.isVonNBounded_iff' (𝕜 := ℂ)).mp (hB.image ev)
  obtain ⟨n, hn⟩ := exists_nat_gt M
  have hle : b n ≤ (⟨_, hsup⟩ : OmegaOne) :=
    Ordinal.le_iSup (fun n ↦ (b n).1) n
  have hx : b n < x.1 := hle.trans_lt (hy.trans_le he)
  apply (hM (ev (f n)) ⟨f n, hf n, rfl⟩).not_gt
  change M < ‖f n x‖
  rw [hb' n x hx]
  exact hn.trans (hnorm n)

private theorem stationaryTail_discontinuous {S : Set OmegaOne} (hS : IsStationary S) :
    ¬ Continuous ((normSeminorm ℂ ℂ).comp (stationaryTail hS) : C(S, ℂ) → ℝ) := by
  classical
  intro h
  let p := (normSeminorm ℂ ℂ).comp (stationaryTail hS)
  have hn : {f : C(S, ℂ) | p f < 1} ∈ 𝓝 (0 : C(S, ℂ)) :=
    (isOpen_lt h continuous_const).mem_nhds (by change p 0 < 1; simp)
  change _ ∈ 𝓝 (ContinuousMap.const S (0 : ℂ)) at hn
  obtain ⟨⟨K, ε⟩, ⟨hK, hε⟩, hsub⟩ := Metric.nhds_basis_ball.nhds_continuousMapConst.mem_iff.mp hn
  let := omegaOne_noMax
  have : Nonempty OmegaOne := ⟨⟨0, lt_of_le_of_lt (bot_le : (⊥ : Ordinal) ≤ Ordinal.omega 0)
    (Ordinal.omega_lt_omega.mpr zero_lt_one)⟩⟩
  obtain ⟨b, hb⟩ := hK.bddAbove_image (f := (Subtype.val : S → OmegaOne)) continuous_subtype_val.continuousOn
  let U : Set S := {x | b.1 < x.1.1}
  have hval : Continuous (fun x : S ↦ x.1.1) := continuous_subtype_val.comp continuous_subtype_val
  have hU : IsClopen U := by
    change IsClopen ((fun x : S ↦ x.1.1) ⁻¹' Ioi b.1)
    have hClosed : IsClosed (Ioi b.1) := by
      rw [← compl_Iic]
      exact SuccOrder.isOpen_Iic.isClosed_compl
    exact ⟨hClosed.preimage hval, isOpen_Ioi.preimage hval⟩
  let f : C(S, ℂ) := ⟨U.piecewise (fun _ ↦ 1) (fun _ ↦ 0),
    Continuous.piecewise (by simp [hU.frontier_eq]) continuous_const continuous_const⟩
  have hfx : ∀ x ∈ K, f x = 0 := by
    intro x hx
    have hxb : x.1 ≤ b := hb ⟨x, hx, rfl⟩
    change U.piecewise (fun _ ↦ (1 : ℂ)) (fun _ ↦ 0) x = 0
    exact piecewise_eq_of_notMem U _ _ ((not_lt_of_ge hxb) : x ∉ U)
  have hf : p f < 1 := hsub (by
    intro x hx
    rw [hfx x hx]
    exact Metric.mem_ball_self hε)
  obtain ⟨a, ha⟩ := stationaryTail_spec hS f
  have heq : stationaryTail hS f = 1 := stationaryTail_unique hS ha (b := b)
    (fun x hx ↦ by
      change U.piecewise (fun _ ↦ (1 : ℂ)) (fun _ ↦ 0) x = 1
      exact piecewise_eq_of_mem U _ _ (show x ∈ U from hx))
  change ‖stationaryTail hS f‖ < 1 at hf
  simp [heq] at hf

/-- A stationary subspace of the countable ordinals, with the first uncountable ordinal added. -/
private def stationaryWithEndpoint (S : Set OmegaOne) : Set Ordinal.{0} :=
  insert omegaOne (Subtype.val '' S)

private def stationaryEndpoint (S : Set OmegaOne) : stationaryWithEndpoint S :=
  ⟨omegaOne, mem_insert _ _⟩

private def stationaryIncl (S : Set OmegaOne) : C(S, stationaryWithEndpoint S) :=
  ⟨fun x ↦ ⟨x.1.1, mem_insert_of_mem _ ⟨x.1, x.2, rfl⟩⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩

private theorem stationaryIncl_cases (S : Set OmegaOne) (x : stationaryWithEndpoint S) :
    x = stationaryEndpoint S ∨ ∃ y : S, stationaryIncl S y = x := by
  rcases x.2 with hx | ⟨y, hy, e⟩
  · exact Or.inl (Subtype.ext hx)
  · exact Or.inr ⟨⟨y, hy⟩, Subtype.ext e⟩

/-- The initial intervals of ordinals are clopen. -/
private theorem ordinal_isClopen_Iic (a : Ordinal.{0}) : IsClopen (Iic a) :=
  ⟨isClosed_Iic, SuccOrder.isOpen_Iic⟩

private theorem stationaryWithEndpoint_zeroDimensional (S : Set OmegaOne) :
    ZeroDimensionalSpace (stationaryWithEndpoint S) := by
  rw [zeroDimensionalSpace_iff_nhds_hasBasis_isClopen]
  intro x
  refine ⟨fun U ↦ ⟨fun hU ↦ ?_, ?_⟩⟩
  · rw [mem_nhds_subtype] at hU
    obtain ⟨V, hV, hsub⟩ := hU
    by_cases hx : (x : Ordinal) = ⊥
    · exact ⟨Subtype.val ⁻¹' ({⊥} : Set Ordinal),
        ⟨⟨isClosed_singleton.preimage continuous_subtype_val,
          SuccOrder.isOpen_singleton_bot.preimage continuous_subtype_val⟩, hx⟩,
        fun y hy ↦ hsub (by simpa [show (y : Ordinal) = ⊥ from hy, hx]
          using mem_of_mem_nhds hV)⟩
    · obtain ⟨a, ha, hI⟩ := exists_Ioc_subset_of_mem_nhds hV ⟨⊥, bot_lt_iff_ne_bot.mpr hx⟩
      have he : Ioc a (x : Ordinal) = (Iic (x : Ordinal)) \ Iic a := by
        ext y
        simp [and_comm]
      have hcl : IsClopen (Ioc a (x : Ordinal)) :=
        he ▸ (ordinal_isClopen_Iic _).diff (ordinal_isClopen_Iic _)
      exact ⟨Subtype.val ⁻¹' Ioc a (x : Ordinal), ⟨hcl.preimage continuous_subtype_val,
        ⟨ha, le_rfl⟩⟩, fun _ hy ↦ hsub (hI hy)⟩
  · rintro ⟨V, ⟨hcl, hx⟩, hVU⟩
    exact Filter.mem_of_superset (hcl.isOpen.mem_nhds hx) hVU

private theorem omegaOne_pos : (⊥ : Ordinal) < omegaOne :=
  lt_of_le_of_lt bot_le (Ordinal.omega_lt_omega.mpr zero_lt_one)

/-- One member of an open cover covers a tail, and only countably many points precede it. -/
private theorem stationaryWithEndpoint_lindelof (S : Set OmegaOne) :
    LindelofSpace (stationaryWithEndpoint S) := by
  refine ⟨isLindelof_of_countable_subcover fun U hU hcover ↦ ?_⟩
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover (mem_univ (stationaryEndpoint S)))
  have hN := (hU i).mem_nhds hi
  rw [mem_nhds_subtype] at hN
  obtain ⟨V, hV, hsub⟩ := hN
  have hV' : V ∈ 𝓝 omegaOne := hV
  obtain ⟨a, ha, hI⟩ := exists_Ioc_subset_of_mem_nhds hV' ⟨⊥, omegaOne_pos⟩
  have hcount : (Iic a).Countable := by
    have ha' : Order.succ a < omegaOne := (Cardinal.isSuccLimit_omega 1).succ_lt ha
    exact (Cardinal.countable_Iio_of_lt_omega_one ha').mono
      (fun _ hb ↦ (show _ < Order.succ a from (lt_succ_of_le_of_not_isMax hb (not_isMax_of_lt ha))))
  have hL : IsLindelof ((Subtype.val : stationaryWithEndpoint S → Ordinal) ⁻¹' Iic a) :=
    (hcount.preimage (fun _ _ e ↦ Subtype.ext e)).isLindelof
  obtain ⟨t, ht, htcover⟩ := hL.elim_countable_subcover U hU
    (subset_univ _ |>.trans hcover)
  refine ⟨insert i t, ht.insert _, fun x _ ↦ ?_⟩
  by_cases hx : (x : Ordinal) ≤ a
  · obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp (htcover hx)
    exact mem_iUnion₂.mpr ⟨j, mem_insert_of_mem _ hj, hxj⟩
  · have hxle : (x : Ordinal) ≤ omegaOne := by
      rcases x.2 with hx' | ⟨z, _, hz⟩
      · exact le_of_eq hx'
      · exact hz ▸ z.2.le
    exact mem_iUnion₂.mpr ⟨i, mem_insert _ _, hsub (hI ⟨lt_of_not_ge hx, hxle⟩)⟩

/-- A compact set in the space with the endpoint has bounded intersection with the countable
ordinals, since a closed cofinal intersection would be a club contained in S. -/
private theorem stationaryCompact_bounded (S : Set OmegaOne) (hSc : IsStationary Sᶜ)
    {K : Set (stationaryWithEndpoint S)} (hK : IsCompact K) :
    BddAbove ((Subtype.val : S → OmegaOne) '' ((stationaryIncl S) ⁻¹' K)) := by
  let J : Set Ordinal := Subtype.val '' K
  let T : Set OmegaOne := Subtype.val ⁻¹' J
  have hJ : IsClosed J := (hK.image continuous_subtype_val).isClosed
  have hsub : T ⊆ S := by
    rintro x ⟨y, _, he⟩
    rcases y.2 with e | ⟨z, hz, hz'⟩
    · exact False.elim (x.2.ne (he.symm.trans e))
    · exact (Subtype.ext (hz'.trans he) : z = x) ▸ hz
  have hT : BddAbove T := by
    by_contra hn
    let := omegaOne_noMax
    have hclub : IsClub T := by
      refine ⟨?_, not_bddAbove_iff_isCofinal.mp hn⟩
      intro U hUT hUne _ a ha
      have ha' : IsLUB (Subtype.val '' U) (a : Ordinal) := by
        refine ⟨?_, ?_⟩
        · rintro _ ⟨z, hz, rfl⟩
          exact ha.1 hz
        · intro b hb
          by_cases hba : b < omegaOne
          · exact ha.2 (show (⟨b, hba⟩ : OmegaOne) ∈ upperBounds U from
              fun z hz ↦ hb ⟨z, hz, rfl⟩)
          · exact a.2.le.trans (le_of_not_gt hba)
      have hmem := ha'.mem_closure (hUne.image Subtype.val)
      exact closure_subset_iff_isClosed.mpr hJ (closure_mono (by
        rintro _ ⟨z, hz, rfl⟩
        exact hUT hz) hmem)
    obtain ⟨x, hxSc, hxT⟩ := hSc hclub
    exact hxSc (hsub hxT)
  refine hT.mono ?_
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨stationaryIncl S x, hx, rfl⟩

private theorem firstCountable_omegaOne : FirstCountableTopology (Iio (Ordinal.omega (1 : Ordinal.{0}))) := by
  constructor
  intro x
  have h : (𝓝 (x : Ordinal)).IsCountablyGenerated := by
    by_cases hm : IsMin (x : Ordinal)
    · rw [SuccOrder.nhds_of_isMin hm]
      infer_instance
    · exact HasCountableBasis.isCountablyGenerated
        ⟨SuccOrder.hasBasis_nhds_Ioc_of_exists_lt (not_isMin_iff.mp hm),
          Cardinal.countable_Iio_of_lt_omega_one x.2⟩
  rw [nhds_subtype]
  infer_instance

private theorem firstCountable_omegaOne_subset (S : Set (Iio (Ordinal.omega (1 : Ordinal.{0})))) :
    FirstCountableTopology S := by
  let := firstCountable_omegaOne
  infer_instance

private theorem small_omegaOne_endpoint (S : Set (Iio (Ordinal.omega (1 : Ordinal.{0})))) :
    Small.{u} ↥(insert (Ordinal.omega 1) (Subtype.val '' S) : Set Ordinal.{0}) := by
  let X : Set Ordinal.{0} := insert (Ordinal.omega 1) (Subtype.val '' S)
  have h : X ⊆ Iic (Ordinal.omega 1) := by
    rintro z (rfl | ⟨w, _, rfl⟩)
    · exact mem_Iic.mpr le_rfl
    · exact mem_Iic.mpr (mem_Iio.mp w.2).le
  let : Small.{0} X := small_subset h
  exact small_of_injective (equivShrink.{0} X).injective
private theorem stationaryIncl_inducing (S : Set OmegaOne) :
    IsInducing (stationaryIncl S) := by
  apply (IsInducing.of_comp_iff (f := stationaryIncl S) (g := Subtype.val) IsInducing.subtypeVal).mp
  change IsInducing ((Subtype.val : OmegaOne → Ordinal) ∘ (Subtype.val : S → OmegaOne))
  exact IsInducing.subtypeVal.comp IsInducing.subtypeVal

/-- Restriction to the stationary set and evaluation at the endpoint. -/
private def stationaryRestriction (S : Set OmegaOne) :
    C(stationaryWithEndpoint S, ℂ) →L[ℂ] C(S, ℂ) × ℂ :=
  (ContinuousMap.compCLM ℂ ℂ (stationaryIncl S)).prod
    (ContinuousMap.evalCLM ℂ (stationaryEndpoint S))

private theorem stationaryRestriction_inducing (S : Set OmegaOne) (hSc : IsStationary Sᶜ) :
    IsInducing (stationaryRestriction S) := by
  rw [IsTopologicalAddGroup.isInducing_iff_nhds_zero]
  apply le_antisymm ((stationaryRestriction S).continuous.tendsto' _ _ (map_zero _)).le_comap
  rw [Filter.le_def]
  intro V hV
  change V ∈ 𝓝 (ContinuousMap.const _ (0 : ℂ)) at hV
  obtain ⟨⟨K, ε⟩, ⟨hK, hε⟩, hsub⟩ := Metric.nhds_basis_ball.nhds_continuousMapConst.mem_iff.mp hV
  obtain ⟨b, hb⟩ := stationaryCompact_bounded S hSc hK
  let L : Set S := stationaryIncl S ⁻¹' (K ∩ Subtype.val ⁻¹' Iic b.1)
  have hkr : K ∩ (Subtype.val : stationaryWithEndpoint S → Ordinal) ⁻¹' Iic b.1 ⊆
      range (stationaryIncl S) := by
    intro x hx
    rcases stationaryIncl_cases S x with rfl | ⟨y, rfl⟩
    · exact False.elim ((show b.1 < omegaOne from b.2).not_ge (show omegaOne ≤ b.1 from hx.2))
    · exact mem_range_self y
  have hL : IsCompact L := (stationaryIncl_inducing S).isCompact_preimage'
    (hK.inter_right (isClosed_Iic.preimage continuous_subtype_val)) hkr
  let W : Set C(S, ℂ) := {f | MapsTo f L (Metric.ball 0 ε)}
  have hW : W ∈ 𝓝 (0 : C(S, ℂ)) :=
    Metric.nhds_basis_ball.nhds_continuousMapConst.mem_of_mem (i := (L, ε)) ⟨hL, hε⟩
  have hp : W ×ˢ Metric.ball 0 ε ∈ 𝓝 (0 : C(S, ℂ) × ℂ) := by
    change W ×ˢ Metric.ball 0 ε ∈ 𝓝 ((0 : C(S, ℂ)), (0 : ℂ))
    rw [nhds_prod_eq]
    exact Filter.prod_mem_prod hW (Metric.ball_mem_nhds _ hε)
  refine Filter.mem_of_superset (Filter.preimage_mem_comap hp) fun f hf ↦ hsub ?_
  intro x hx
  rcases stationaryIncl_cases S x with rfl | ⟨y, rfl⟩
  · exact hf.2
  · have hy : y.1 ≤ b := hb ⟨y, hx, rfl⟩
    exact hf.1 ⟨hx, hy⟩

/-- Extend a function on an initial clopen interval by a constant on the complementary tail. -/
private def stationaryExtend (S : Set OmegaOne) (b : OmegaOne) (f : C(S, ℂ)) (c : ℂ) :
    C(stationaryWithEndpoint S, ℂ) := by
  classical
  let A : Set (stationaryWithEndpoint S) := Subtype.val ⁻¹' Iic b.1
  have hA : IsClopen A := (ordinal_isClopen_Iic _).preimage continuous_subtype_val
  let k (x : A) : S :=
    ⟨⟨x.1.1, (show x.1.1 ≤ b.1 from x.2).trans_lt b.2⟩, by
      rcases x.1.2 with e | ⟨z, hz, e⟩
      · have hx : x.1.1 ≤ b.1 := x.2
        rw [e] at hx
        exact False.elim ((show b.1 < omegaOne from b.2).not_ge hx)
      · have hz' : (⟨x.1.1, (show x.1.1 ≤ b.1 from x.2).trans_lt b.2⟩ : OmegaOne) = z :=
          Subtype.ext e.symm
        exact hz' ▸ hz⟩
  have hk : Continuous k :=
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _
  let g (x : stationaryWithEndpoint S) := if h : x ∈ A then f (k ⟨x, h⟩) else c
  have h₁ : ContinuousOn g A := by
    rw [continuousOn_iff_continuous_domRestrict]
    apply (f.continuous.comp hk).congr
    intro x
    change f (k x) = g x.1
    simp [g, x.2]
  have h₂ : ContinuousOn g Aᶜ :=
    continuousOn_const.congr (fun _ hx ↦ dite_eq_right hx)
  refine ⟨g, ?_⟩
  simpa [continuousOn_univ] using h₁.union_of_isOpen h₂ hA.isOpen hA.isClosed.isOpen_compl

private theorem stationaryExtend_endpoint (S : Set OmegaOne) (b : OmegaOne)
    (f : C(S, ℂ)) (c : ℂ) : stationaryExtend S b f c (stationaryEndpoint S) = c := by
  classical
  unfold stationaryExtend
  exact dite_eq_right ((show b.1 < omegaOne from b.2).not_ge)

private theorem stationaryExtend_incl (S : Set OmegaOne) (b : OmegaOne)
    (f : C(S, ℂ)) (c : ℂ) (x : S) (hx : x.1 ≤ b) :
    stationaryExtend S b f c (stationaryIncl S x) = f x := by
  classical
  unfold stationaryExtend
  exact dite_eq_left hx

private theorem stationaryRestriction_dense (S : Set OmegaOne) :
    DenseRange (stationaryRestriction S) := by
  intro ⟨f, c⟩
  have : Nonempty OmegaOne := ⟨⟨⊥, omegaOne_pos⟩⟩
  have h₁ (K : Set S) (hK : IsCompact K) (U : Set ℂ) (_ : IsOpen U) (hU : MapsTo f K U) :
      ∀ᶠ b : OmegaOne in Filter.atTop,
        MapsTo (fun x ↦ stationaryExtend S b f c (stationaryIncl S x)) K U := by
    obtain ⟨a, ha⟩ := hK.bddAbove_image (f := (Subtype.val : S → OmegaOne))
      continuous_subtype_val.continuousOn
    filter_upwards [Filter.eventually_ge_atTop a] with b hab x hx
    change stationaryExtend S b f c (stationaryIncl S x) ∈ U
    rw [stationaryExtend_incl S b f c x ((ha ⟨x, hx, rfl⟩).trans hab)]
    exact hU hx
  have ht₁ :
      Filter.Tendsto (fun b : OmegaOne ↦ (stationaryRestriction S (stationaryExtend S b f c)).1)
        Filter.atTop (𝓝 f) :=
    ContinuousMap.tendsto_nhds_compactOpen.mpr h₁
  have ht₂ :
      Filter.Tendsto (fun b : OmegaOne ↦ (stationaryRestriction S (stationaryExtend S b f c)).2)
        Filter.atTop (𝓝 c) := by
    convert (tendsto_const_nhds : Filter.Tendsto (fun _ : OmegaOne ↦ c) Filter.atTop (𝓝 c))
      using 2
    exact stationaryExtend_endpoint S _ f c
  exact mem_closure_of_tendsto (ht₁.prodMk_nhds ht₂) (.of_forall fun b ↦
    mem_range_self (stationaryExtend S b f c))

/-- A dense linear uniform embedding into a Hausdorff complete space exhibits a completion. -/
private theorem completionEquivOfDenseInducing
    {E F : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    [UniformContinuousConstSMul ℂ E] [AddCommGroup F] [Module ℂ F] [UniformSpace F]
    [IsUniformAddGroup F] [UniformContinuousConstSMul ℂ F] [T2Space F] [CompleteSpace F]
    (f : E →L[ℂ] F) (hi : IsInducing f) (hd : DenseRange f) :
    Nonempty (Completion E ≃L[ℂ] F) := by
  have hu : IsUniformInducing f := AddMonoidHom.isUniformInducing_of_isInducing hi
  have he : IsUniformInducing f.fromCompletion :=
    Completion.isUniformInducing_extension hu
  have hd' : DenseRange f.fromCompletion := hd.mono (by
    rintro _ ⟨x, rfl⟩
    exact ⟨(x : Completion E), f.fromCompletion_apply_coe x⟩)
  have hs : Surjective f.fromCompletion :=
    range_eq_univ.mp (he.isComplete_range.isClosed.closure_eq ▸ hd'.closure_range)
  let e := LinearEquiv.ofBijective f.fromCompletion.toLinearMap ⟨he.isInducing.injective, hs⟩
  exact ⟨{e with continuous_toFun := f.fromCompletion.continuous
                 continuous_invFun := he.isInducing.continuous_iff.mpr
                   (continuous_id.congr fun x ↦ (e.apply_symm_apply x).symm) }⟩

/-- The eventual-value seminorm, pulled back by the first projection, obstructs bornologicity
of the product with the endpoint coordinate. -/
private theorem stationaryProduct_not_bornological (S : Set OmegaOne) (hS : IsStationary S) :
    ¬ Printed.IsBornologicalTVS (C(S, ℂ) × ℂ) := by
  intro h
  let p := (normSeminorm ℂ ℂ).comp (stationaryTail hS)
  let fst := ContinuousLinearMap.fst ℂ C(S, ℂ) ℂ
  have hcont : Continuous (p.comp fst.toLinearMap) := h _ (fun B hB ↦ by
    obtain ⟨M, hM⟩ := stationaryTail_bounded hS (hB.image fst)
    refine ⟨M, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hM ⟨fst x, ⟨x, hx, rfl⟩, rfl⟩)
  have hcomp := hcont.comp (continuous_id.prodMk (continuous_const (y := (0 : ℂ))))
  exact stationaryTail_discontinuous hS hcomp

/-- A homeomorphism of the domains identifies their spaces of continuous functions. -/
private def continuousMapEquivOfHomeomorph {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) : C(Y, ℂ) ≃L[ℂ] C(X, ℂ) :=
  ContinuousLinearEquiv.equivOfInverse
    (ContinuousMap.compCLM ℂ ℂ ⟨e, e.continuous⟩)
    (ContinuousMap.compCLM ℂ ℂ ⟨e.symm, e.symm.continuous⟩)
    (fun f ↦ ContinuousMap.ext fun x ↦ congrArg f (e.apply_symm_apply x))
    (fun f ↦ ContinuousMap.ext fun x ↦ congrArg f (e.symm_apply_apply x))


/-- The compact-convergence uniformity is compatible with pointwise addition. -/
private theorem compactConvergence_isUniformAddGroup (X : Type*) [TopologicalSpace X] :
    IsUniformAddGroup C(X, ℂ) := by
  let i : C(X, ℂ) →+ UniformOnFun X ℂ {K | IsCompact K} :=
    { toFun := ContinuousMap.toUniformOnFunIsCompact
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  exact IsUniformInducing.isUniformAddGroup i (show IsUniformInducing ContinuousMap.toUniformOnFunIsCompact from
      ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isUniformInducing)

open scoped ComplexOrder in
private theorem continuousMap_polynormable (X : Type*) [TopologicalSpace X] :
    PolynormableSpace ℂ C(X, ℂ) := by
  let : LocallyConvexSpace ℂ ℂ := LocallyConvexSpace.ofBasisZero ℂ ℂ _ _
    Metric.nhds_basis_ball (fun r _ ↦
      convex_RCLike_iff_convex_real.mpr (convex_ball (0 : ℂ) r))
  infer_instance

/-- A Hausdorff polynormable complex space that is bornological, with a right-uniform
completion that is not. The space is the compact-open space of functions on a stationary
subset with the endpoint adjoined. The eventual-value seminorm obstructs bornologicity
of its completion. -/
private theorem completedInductiveTensor_bornological_false_badCompletion :
    ∃ (E : Type u) (hA : AddCommGroup E) (hM : Module ℂ E) (hT : TopologicalSpace E)
      (hP : PolynormableSpace ℂ E) (h2 : T2Space E),
      letI : AddCommGroup E := hA
      letI : Module ℂ E := hM
      letI : TopologicalSpace E := hT
      letI : PolynormableSpace ℂ E := hP
      letI : T2Space E := h2
      letI : IsTopologicalAddGroup E := PolynormableSpace.isTopologicalAddGroup ℂ E
      letI : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
      letI : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
      Printed.IsBornologicalTVS E ∧ ¬ Printed.IsBornologicalTVS (Completion E) := by
  obtain ⟨S, hS, hSc⟩ := completedInductiveTensor_bornological_false_split
  let X := stationaryWithEndpoint S
  let : Small.{u} X := small_omegaOne_endpoint S
  let Y := Shrink.{u} X
  let e₀ : Y ≃ X := (equivShrink X).symm
  let : TopologicalSpace Y := TopologicalSpace.induced e₀ inferInstance
  let e : Y ≃ₜ X :=
    { e₀ with
      continuous_toFun := continuous_induced_dom
      continuous_invFun := continuous_induced_rng.mpr <|
        (continuous_id (X := X)).congr fun x ↦ (e₀.apply_symm_apply x).symm }
  let E := C(Y, ℂ)
  let hA : AddCommGroup E := inferInstanceAs (AddCommGroup C(Y, ℂ))
  let hM : Module ℂ E := inferInstanceAs (Module ℂ C(Y, ℂ))
  let hT : TopologicalSpace E := inferInstanceAs (TopologicalSpace C(Y, ℂ))
  let hP : PolynormableSpace ℂ E := continuousMap_polynormable Y
  let h2 : T2Space E := inferInstanceAs (T2Space C(Y, ℂ))
  refine ⟨E, hA, hM, hT, hP, h2, ?_⟩
  let : ZeroDimensionalSpace X := stationaryWithEndpoint_zeroDimensional S
  let : LindelofSpace X := stationaryWithEndpoint_lindelof S
  let eL : C(X, ℂ) ≃L[ℂ] E := continuousMapEquivOfHomeomorph e
  have hE := completedInductiveTensor_bornological_false_transfer eL
    (bornological_continuousMap_zeroDimensional_lindelof X)
  refine ⟨hE, ?_⟩
  let : IsTopologicalAddGroup E := PolynormableSpace.isTopologicalAddGroup ℂ E
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  let : FirstCountableTopology S := firstCountable_omegaOne_subset S
  let R := stationaryRestriction S
  let f : E →L[ℂ] C(S, ℂ) × ℂ := R.comp eL.symm.toContinuousLinearMap
  have hi : IsInducing f := (stationaryRestriction_inducing S hSc).comp
    eL.symm.toHomeomorph.isInducing
  have hd : DenseRange f := (stationaryRestriction_dense S).mono (by
    rintro _ ⟨g, rfl⟩
    exact ⟨eL g, congrArg R (eL.symm_apply_apply g)⟩)
  let : IsUniformAddGroup C(S, ℂ) := compactConvergence_isUniformAddGroup S
  let : UniformContinuousConstSMul ℂ C(S, ℂ) := uniformContinuousConstSMul_of_continuousConstSMul _ _
  obtain ⟨F⟩ := completionEquivOfDenseInducing f hi hd
  intro h
  exact stationaryProduct_not_bornological S hS
    (completedInductiveTensor_bornological_false_transfer F h)

end completedInductiveTensor_bornological_false_aux

/-- Paper: Proposition C.2.3.13(3), p. 683. Let S be stationary in ω₁ with stationary
complement and let X = S ∪ {ω₁} have the subspace topology from ω₁ + 1. Take E = C(X, ℂ)
with compact convergence and F = ℂ. The space X is zero-dimensional and Lindelöf,
so every seminorm bounded on bounded sets is controlled by a compact support. Its completion
is C(S, ℂ) × ℂ with compact convergence on S. Each continuous function on S is eventually constant.
The norm of its eventual value is a seminorm bounded on bounded sets, since countably
many stabilization ordinals have a countable supremum. It is discontinuous, since
one can set the function to zero on any prescribed compact set and to one on a tail. -/
theorem Printed.completedInductiveTensor_bornological_false :
    ¬ Printed.completedInductiveTensor_bornological :=
  completedInductiveTensor_bornological_false_fromBad
    completedInductiveTensor_bornological_false_badCompletion

end RiemannMasullo
