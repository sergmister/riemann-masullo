module

public import RiemannMasullo.AppD_SchwartzBruhat.Sec1a
public import RiemannMasullo.AppC_LCTVS.Sec2b
public import RiemannMasullo.AppA_AlgebraicNT.Sec1
public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Mathlib.Topology.Instances.ZMod
import all RiemannMasullo.AppC_LCTVS.Sec2b
import all RiemannMasullo.AppD_SchwartzBruhat.Sec1a
import Mathlib.Algebra.Category.Grp.Injective
import RiemannMasullo.ForMathlib.Analysis.Calculus.FDeriv.Symmetric
import all RiemannMasullo.AppC_LCTVS.Sec1
import Mathlib.Analysis.LocallyConvex.ContinuousOfBounded
import RiemannMasullo.ForMathlib.MeasureTheory.Integral.Bochner.Convex
import RiemannMasullo.ForMathlib.Analysis.Calculus.IteratedDeriv.UnitCube
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.ProjectionCompleteness
import Mathlib.Analysis.PSeries
import Mathlib.Data.Set.Finite.List
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import RiemannMasullo.ForMathlib.Topology.Algebra.PontryaginDual.Separation
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import RiemannMasullo.ForMathlib.Algebra.Module.ZLattice.Quotient
import RiemannMasullo.ForMathlib.Topology.Algebra.ContinuousMonoidHom
import RiemannMasullo.ForMathlib.Topology.Algebra.Group.Divisible
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.StrongDual
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.StrongBidual
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.HahnBanach
import RiemannMasullo.ForMathlib.Analysis.Normed.Module.LocalHom
import RiemannMasullo.ForMathlib.Analysis.Normed.Module.LocalSubgroup
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Complex.CircleLocalHom
import RiemannMasullo.ForMathlib.Topology.Algebra.PontryaginDual
import RiemannMasullo.ForMathlib.Topology.Algebra.PontryaginDual.Compact
import RiemannMasullo.ForMathlib.Topology.Covering.AddCircle
import RiemannMasullo.ForMathlib.Topology.Algebra.PontryaginDual.Real
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Geometry.Manifold.HasGroupoid
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Order.WellQuasiOrder
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Analysis.RCLike.Lemmas

/-!
# Structure of locally compact abelian groups and their Schwartz–Bruhat spaces

Masullo, §§D.1.4–D.1.5, pp. 757–765.
-/

@[expose] public noncomputable section

open Bornology Filter MeasureTheory Set Topology TopologicalSpace
open scoped Cardinal ContDiff DirectSum Topology

namespace RiemannMasullo

section TorusHom

variable {G : Type*} [CommGroup G] [TopologicalSpace G]
  [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]

/-- A neighborhood containing no nontrivial cyclic subgroup gives finitely many characters
whose joint kernel is discrete. -/
theorem exists_torusHom_of_noSmallCyclicSubgroups
    {W : Set G} (hW : W ∈ 𝓝 (1 : G))
    (hPow : ∀ x : G, (∀ k : ℕ, x ^ k ∈ W) → x = 1) :
    ∃ (t : Finset (PontryaginDual G)) (f : G →ₜ* (t → Circle)),
      (∀ x (χ : t), f x χ = χ.val x) ∧ DiscreteTopology f.toMonoidHom.ker := by
  classical
  obtain ⟨K, hK, hKnhds⟩ := exists_compact_mem_nhds (1 : G)
  obtain ⟨V, hV, hOne, hVV⟩ := exists_open_nhds_one_mul_subset (inter_mem hKnhds hW)
  have hVW : V ⊆ W := fun x hx ↦ (hVV (mul_one x ▸ Set.mul_mem_mul hx hOne)).2
  let S (χ : PontryaginDual G) : Set G := {x | χ x ≠ 1}
  have hCover : K \ V ⊆ ⋃ χ, S χ := by
    intro x hx
    have hx1 : x ≠ 1 := fun h ↦ hx.2 (h ▸ hOne)
    have hSep := (pontryaginDual_pairing_separates (G := G)).1
    obtain ⟨χ, hχ⟩ : ∃ χ : PontryaginDual G, χ x ≠ 1 := by
      by_contra! hn
      exact hx1 (hSep (funext fun χ ↦ (hn χ).trans (map_one χ).symm))
    exact mem_iUnion.mpr ⟨χ, hχ⟩
  obtain ⟨t, ht⟩ := (hK.diff hV).elim_finite_subcover S
    (fun χ ↦ (isClosed_eq χ.continuous continuous_const).isOpen_compl) hCover
  let f : G →ₜ* (t → Circle) :=
    { toFun := fun x χ ↦ χ.val x
      map_one' := funext fun χ ↦ map_one χ.val
      map_mul' := fun x y ↦ funext fun χ ↦ map_mul χ.val x y
      continuous_toFun := continuous_pi fun χ ↦ χ.val.continuous }
  refine ⟨t, f, fun _ _ ↦ rfl, discreteTopology_of_isOpen_singleton_one ?_⟩
  have hKer (x : f.toMonoidHom.ker) (hx : (x : G) ∈ V) : x = 1 := by
    have hr (k : ℕ) : (x : G) ^ k ∈ V := by
      induction k with
      | zero => simpa using hOne
      | succ k ih =>
        have hKmem : (x : G) ^ (k + 1) ∈ K :=
          (hVV (pow_succ (x : G) k ▸ Set.mul_mem_mul ih hx)).1
        by_contra hn
        obtain ⟨χ, hχt, hχ⟩ := mem_iUnion₂.mp (ht ⟨hKmem, hn⟩)
        have hχx : χ (x : G) = 1 :=
          congrFun (MonoidHom.mem_ker.mp x.property) ⟨χ, hχt⟩
        exact hχ (by rw [map_pow, hχx, one_pow])
    exact Subtype.ext (hPow x fun k ↦ hVW (hr k))
  have hPreimage : (Subtype.val : f.toMonoidHom.ker → G) ⁻¹' V = {1} := by
    ext x
    exact ⟨fun hx ↦ mem_singleton_iff.mpr (hKer x hx), by
      rintro (rfl : x = 1)
      exact hOne⟩
  exact hPreimage ▸ hV.preimage continuous_subtype_val

omit [T2Space G] in
open scoped Pointwise in
/-- A continuous homomorphism to a finite-dimensional torus with discrete kernel has a
continuous local section over a ball in a linear subspace of the logarithm space. The
section is a local homomorphism, and the images of small balls are identity neighborhoods. -/
theorem exists_localSection_of_discrete_torusKernel {ι : Type*} [Fintype ι]
    (f : G →ₜ* (ι → Circle)) (hf : DiscreteTopology f.toMonoidHom.ker) :
    ∃ (L : Submodule ℝ (EuclideanSpace ℝ ι)) (ρ : ℝ) (σ : L → G), 0 < ρ ∧ ρ ≤ 1 ∧
      (∀ v : L, ‖v‖ < ρ → ∀ i, f (σ v) i = Circle.exp ((v : EuclideanSpace ℝ ι) i)) ∧
      ContinuousOn σ (Metric.ball 0 ρ) ∧
      (∀ v w : L, ‖v‖ < ρ → ‖w‖ < ρ → ‖v + w‖ < ρ → σ (v + w) = σ v * σ w) ∧
      (∀ ε > 0, σ '' Metric.ball 0 ε ∈ 𝓝 1) := by
  classical
  let ex : EuclideanSpace ℝ ι → (ι → Circle) := fun v i ↦ Circle.exp (v i)
  have hex : Continuous ex := continuous_pi fun i ↦ Circle.exp.continuous.comp (by fun_prop)
  have hex0 : ex 0 = 1 := funext fun i ↦ by simp [ex]
  have hexadd : ∀ v w, ex (v + w) = ex v * ex w := fun v w ↦ funext fun i ↦ by
    simp [ex, Circle.exp_add]
  have hexneg : ∀ v, ex (-v) = (ex v)⁻¹ := fun v ↦ funext fun i ↦ by simp [ex]
  -- A neighborhood meeting the kernel only at the identity.
  obtain ⟨O, hO, h1O, hOker⟩ : ∃ O : Set G, IsOpen O ∧ (1 : G) ∈ O ∧
      ∀ x ∈ O, f x = 1 → x = 1 := by
    have hopen1 : IsOpen ({1} : Set f.toMonoidHom.ker) := isOpen_discrete _
    obtain ⟨U0, hU0o, hpre⟩ := isOpen_induced_iff.mp hopen1
    refine ⟨U0, hU0o, ?_, ?_⟩
    · have : (1 : f.toMonoidHom.ker) ∈ Subtype.val ⁻¹' U0 := by rw [hpre]; rfl
      simpa using this
    · intro x hx hfx
      have hmem : (⟨x, MonoidHom.mem_ker.mpr hfx⟩ : f.toMonoidHom.ker) ∈
          Subtype.val ⁻¹' U0 := hx
      rw [hpre] at hmem
      exact congrArg Subtype.val (Set.mem_singleton_iff.mp hmem)
  obtain ⟨W, hW, h1W, hWW⟩ := exists_open_nhds_one_mul_subset (hO.mem_nhds h1O)
  have hWW' : W ∩ W⁻¹ ∈ 𝓝 (1 : G) :=
    inter_mem (hW.mem_nhds h1W) (inv_mem_nhds_one G (hW.mem_nhds h1W))
  obtain ⟨V, hV, hVW, hVc⟩ := local_compact_nhds hWW'
  have hinj : ∀ x ∈ V, ∀ y ∈ V, f x = f y → x = y := by
    intro x hx y hy hxy
    have hy' : y⁻¹ ∈ W := (hVW hy).2
    have hm : x * y⁻¹ ∈ O := hWW (Set.mul_mem_mul (hVW hx).1 hy')
    have : f (x * y⁻¹) = 1 := by rw [map_mul, map_inv, hxy, mul_inv_cancel]
    exact mul_inv_eq_one.mp (hOker _ hm this)
  obtain ⟨C, hC, -, hCinv, hCC⟩ := exists_closed_nhds_one_inv_eq_mul_subset hV
  have h1C : (1 : G) ∈ C := mem_of_mem_nhds hC
  have hCV : C ⊆ V := fun x hx ↦ by simpa using hCC (Set.mul_mem_mul hx h1C)
  -- Small logarithms of values on `V` come from `C`.
  have hD : IsCompact (f '' (V \ interior C)) :=
    (hVc.diff isOpen_interior).image f.continuous
  have h1D : (1 : ι → Circle) ∉ f '' (V \ interior C) := by
    rintro ⟨x, ⟨hxV, hxC⟩, hfx⟩
    have : x = 1 := hinj x hxV 1 (mem_of_mem_nhds hV) (by rw [hfx, map_one])
    exact hxC (this ▸ mem_interior_iff_mem_nhds.mpr hC)
  obtain ⟨ε, hε, hεD⟩ : ∃ ε > 0, ∀ v : EuclideanSpace ℝ ι, ‖v‖ < ε →
      ex v ∉ f '' (V \ interior C) := by
    have hnhds : (f '' (V \ interior C))ᶜ ∈ 𝓝 (ex 0) := by
      rw [hex0]; exact hD.isClosed.isOpen_compl.mem_nhds h1D
    obtain ⟨ε, hε, H⟩ := Metric.mem_nhds_iff.mp (hex.continuousAt hnhds)
    exact ⟨ε, hε, fun v hv ↦ H (by simpa using hv)⟩
  have hlift : ∀ v : EuclideanSpace ℝ ι, ‖v‖ < ε → ∀ x ∈ V, f x = ex v → x ∈ C := by
    intro v hv x hx hfx
    by_contra hxC
    exact hεD v hv ⟨x, ⟨hx, fun h ↦ hxC (interior_subset h)⟩, hfx⟩
  -- The logarithms of the image form a closed local subgroup.
  set R := min (ε / 2) 1 with hRdef
  have hR : 0 < R := lt_min (half_pos hε) one_pos
  have hRε : R < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  have hR1 : R ≤ 1 := min_le_right _ _
  let A : Set (EuclideanSpace ℝ ι) := {v | ‖v‖ ≤ R ∧ ex v ∈ f '' V}
  have hAc : IsClosed A :=
    (isClosed_le continuous_norm continuous_const).inter
      ((hVc.image f.continuous).isClosed.preimage hex)
  have hA0 : (0 : EuclideanSpace ℝ ι) ∈ A :=
    ⟨by simp [hR.le], ⟨1, mem_of_mem_nhds hV, by rw [map_one, hex0]⟩⟩
  have hAmemC : ∀ v ∈ A, ∃ x ∈ C, f x = ex v := by
    rintro v ⟨hv, x, hx, hfx⟩
    exact ⟨x, hlift v (hv.trans_lt hRε) x hx hfx, hfx⟩
  have hAsym : ∀ v ∈ A, -v ∈ A := by
    intro v hvA
    obtain ⟨x, hxC, hfx⟩ := hAmemC v hvA
    have hxC' : x⁻¹ ∈ C := by rw [← hCinv]; simpa using hxC
    exact ⟨by simpa using hvA.1, x⁻¹, hCV hxC', by rw [map_inv, hfx, hexneg]⟩
  have hAadd : ∀ v ∈ A, ∀ w ∈ A, ‖v + w‖ ≤ R → v + w ∈ A := by
    intro v hv w hw hvw
    obtain ⟨x, hxC, hfx⟩ := hAmemC v hv
    obtain ⟨y, hyC, hfy⟩ := hAmemC w hw
    exact ⟨hvw, x * y, hCC (Set.mul_mem_mul hxC hyC), by rw [map_mul, hfx, hfy, hexadd]⟩
  obtain ⟨L, ε₁, hε₁, hε₁R, hAL⟩ :=
    exists_subspace_ball_eq_of_localSubgroup hR hAc hA0 hAsym hAadd
  have hLA : ∀ v : EuclideanSpace ℝ ι, v ∈ L → ‖v‖ ≤ ε₁ → v ∈ A := by
    intro v hvL hv
    have : v ∈ (L : Set (EuclideanSpace ℝ ι)) ∩ Metric.closedBall 0 ε₁ :=
      ⟨hvL, by simpa using hv⟩
    rw [← hAL] at this
    exact this.1
  have hAL' : ∀ v ∈ A, ‖v‖ ≤ ε₁ → v ∈ L := by
    intro v hvA hv
    have : v ∈ A ∩ Metric.closedBall 0 ε₁ := ⟨hvA, by simpa using hv⟩
    rw [hAL] at this
    exact this.1
  let σ : L → G := fun v ↦ Function.invFunOn f C (ex v)
  have hσ : ∀ v : L, ‖v‖ < ε₁ → σ v ∈ C ∧ f (σ v) = ex v := by
    intro v hv
    exact Function.invFunOn_pos (hAmemC _ (hLA _ v.2 hv.le))
  refine ⟨L, ε₁, σ, hε₁, hε₁R.trans hR1, ?_, ?_, ?_, ?_⟩
  · intro v hv i
    exact congrFun (hσ v hv).2 i
  · rw [continuousOn_iff_continuous_domRestrict]
    let gV : V → (ι → Circle) := fun x ↦ f x
    have : CompactSpace V := isCompact_iff_compactSpace.mp hVc
    have hgV : IsClosedEmbedding gV :=
      (f.continuous.comp continuous_subtype_val).isClosedEmbedding
        (fun x y hxy ↦ Subtype.ext (hinj x x.2 y y.2 hxy))
    let σ' : Metric.ball (0 : L) ε₁ → V := fun v ↦
      ⟨σ v, hCV (hσ v (mem_ball_zero_iff.mp v.2)).1⟩
    have hσ' : Continuous σ' := by
      rw [hgV.isInducing.continuous_iff]
      have e : gV ∘ σ' = fun v : Metric.ball (0 : L) ε₁ ↦ ex ((v : L) : EuclideanSpace ℝ ι) :=
        funext fun v ↦ (hσ v (mem_ball_zero_iff.mp v.2)).2
      rw [e]
      exact hex.comp (continuous_subtype_val.comp continuous_subtype_val)
    exact continuous_subtype_val.comp hσ'
  · intro v w hv hw hvw
    have h1 := hσ v hv
    have h2 := hσ w hw
    have h3 := hσ (v + w) hvw
    refine hinj _ (hCV h3.1) _ (hCC (Set.mul_mem_mul h1.1 h2.1)) ?_
    rw [map_mul, h1.2, h2.2, h3.2, ← hexadd]
    rfl
  · intro ε' hε'
    set ε'' := min ε' ε₁ with hε''def
    have hε'' : 0 < ε'' := lt_min hε' hε₁
    have hnear : ∀ᶠ x in 𝓝 (1 : G), x ∈ interior C ∧
        ∃ u : EuclideanSpace ℝ ι, ‖u‖ < ε'' ∧ ∀ i, Circle.exp (u i) = f x i := by
      refine Filter.Eventually.and (show ∀ᶠ x in 𝓝 (1 : G), x ∈ interior C from
        isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hC)) ?_
      have ht : Tendsto f (𝓝 (1 : G)) (𝓝 1) := by
        have := (map_continuous f).tendsto (1 : G)
        rwa [map_one] at this
      exact ht.eventually (eventually_exists_small_circleLog hε'')
    apply Filter.mem_of_superset hnear
    rintro x ⟨hxC, u, hu, hux⟩
    have hfx : f x = ex u := funext fun i ↦ (hux i).symm
    have hu1 : ‖u‖ < ε₁ := hu.trans_le (min_le_right _ _)
    have huA : u ∈ A := ⟨hu1.le.trans hε₁R, x, hCV (interior_subset hxC), hfx⟩
    have huL : u ∈ L := hAL' u huA hu1.le
    refine ⟨⟨u, huL⟩, by simpa using hu.trans_le (min_le_left _ _), ?_⟩
    have hs := hσ ⟨u, huL⟩ (by simpa using hu1)
    exact hinj _ (hCV hs.1) _ (hCV (interior_subset hxC)) (by rw [hs.2, hfx])

end TorusHom

section Structure

universe u

variable {G : Type u} [CommGroup G] [TopologicalSpace G]

/-- Paper: Definition D.1.4.1, p. 757. A compact neighborhood of the identity
generates the whole group. -/
def IsCompactlyGeneratedGroup (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  ∃ U : Set G, U ∈ 𝓝 (1 : G) ∧ IsCompact U ∧ Subgroup.closure U = ⊤

/-- Paper: Definition D.1.4.1, p. 757. A compact group is compactly generated.
Deviation: Sanity check using the whole group as the generating neighborhood. -/
theorem isCompactlyGeneratedGroup_of_compact [CompactSpace G] :
    IsCompactlyGeneratedGroup G :=
  ⟨Set.univ, Filter.univ_mem, isCompact_univ, Subgroup.closure_univ⟩

/-- Paper: Theorem D.1.4.2, p. 757. A locally Euclidean space admits charts in
some fixed finite real dimension. -/
def IsLocallyEuclidean (X : Type*) [TopologicalSpace X] : Prop :=
  ∃ n : ℕ, Nonempty (ChartedSpace (EuclideanSpace ℝ (Fin n)) X)

/-- Paper: Theorem D.1.4.2, p. 757. A discrete space is locally Euclidean in
dimension zero.
Deviation: Sanity check for the locally Euclidean condition. -/
theorem isLocallyEuclidean_of_discrete (X : Type*) [TopologicalSpace X]
    [DiscreteTopology X] : IsLocallyEuclidean X :=
  ⟨0, ⟨ChartedSpace.ofDiscreteTopology⟩⟩

/-- Paper: (D.1.4.2), p. 757. A presentation identifies a group topologically
with a product of real, torus, free discrete and finite discrete abelian factors. -/
structure ElementaryLCAPresentation (G : Type*) [CommGroup G] [TopologicalSpace G] where
  realDim : ℕ
  torusDim : ℕ
  latticeRank : ℕ
  finiteFactor : Type
  [finiteGroup : AddCommGroup finiteFactor]
  [finiteFintype : Fintype finiteFactor]
  [finiteTopology : TopologicalSpace finiteFactor]
  [finiteDiscrete : DiscreteTopology finiteFactor]
  equiv : G ≃ₜ* Multiplicative (ElementaryLieGroup realDim torusDim latticeRank finiteFactor)

attribute [instance] ElementaryLCAPresentation.finiteGroup ElementaryLCAPresentation.finiteFintype
  ElementaryLCAPresentation.finiteTopology ElementaryLCAPresentation.finiteDiscrete

/-- The product of two groups of order two is not cyclic, since its exponent is two. -/
private theorem zmodTwoProd_not_isAddCyclic : ¬ IsAddCyclic (ZMod 2 × ZMod 2) := by
  intro h
  have h1 : AddMonoid.exponent (ZMod 2 × ZMod 2) = Nat.card (ZMod 2 × ZMod 2) :=
    IsAddCyclic.exponent_eq_card
  have h2 : AddMonoid.exponent (ZMod 2 × ZMod 2) ∣ 2 :=
    AddMonoid.exponent_dvd_of_forall_nsmul_eq_zero (by decide)
  rw [h1, Nat.card_eq_fintype_card] at h2
  revert h2
  decide

/-- Paper: (D.1.4.2), p. 757. The Klein four group admits an elementary presentation
whose finite factor has order four and is noncyclic.
Deviation: Sanity check for the finite abelian factor. -/
theorem ElementaryLCAPresentation.exists_kleinFour :
    ∃ e : ElementaryLCAPresentation (Multiplicative (ZMod 2 × ZMod 2)),
      Fintype.card e.finiteFactor = 4 ∧ ¬ IsAddCyclic e.finiteFactor := by
  let a : (ZMod 2 × ZMod 2) ≃+ ElementaryLieGroup 0 0 0 (ZMod 2 × ZMod 2) :=
    { toFun := fun x ↦ (0, 0, 0, x)
      invFun := fun p ↦ p.2.2.2
      left_inv := fun _ ↦ rfl
      right_inv := fun p ↦ Prod.ext (by ext i; exact i.elim0)
        (Prod.ext (by ext i; exact i.elim0) (Prod.ext (by ext i; exact i.elim0) rfl))
      map_add' := fun x y ↦ Prod.ext (by ext i; exact i.elim0)
        (Prod.ext (by ext i; exact i.elim0) (Prod.ext (by ext i; exact i.elim0) rfl)) }
  refine ⟨{ realDim := 0, torusDim := 0, latticeRank := 0, finiteFactor := ZMod 2 × ZMod 2
            equiv := { AddEquiv.toMultiplicative a with
              continuous_toFun := continuous_of_discreteTopology
              continuous_invFun := continuous_of_discreteTopology } }, ?_, ?_⟩
  · change Fintype.card (ZMod 2 × ZMod 2) = 4
    decide
  · exact zmodTwoProd_not_isAddCyclic

/-- A continuous homomorphism from a torus to a real vector group vanishes,
since the multiples of a nonzero vector cannot all lie in a compact range. -/
private theorem elementary_torus_to_euclidean_eq_zero {m n : ℕ}
    (f : (Fin n → AddCircle (1 : ℝ)) →+ EuclideanSpace ℝ (Fin m))
    (hf : Continuous f) (x : Fin n → AddCircle (1 : ℝ)) : f x = 0 := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp (isCompact_range hf).isBounded
  by_contra hx
  have hpos : 0 < ‖f x‖ := norm_pos_iff.mpr hx
  obtain ⟨k, hk⟩ := exists_nat_gt (C / ‖f x‖)
  have hbound := hC (f (k • x)) ⟨k • x, rfl⟩
  rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, norm_smul,
    Real.norm_of_nonneg (Nat.cast_nonneg k)] at hbound
  exact (not_lt_of_ge hbound) ((div_lt_iff₀ hpos).mp hk)

/-- The subgroup of a finite torus killed by doubling has cardinality two to
the power of the number of circle coordinates. -/
private theorem elementary_torus_two_torsion_card (n : ℕ) :
    Nat.card {x : Fin n → AddCircle (1 : ℝ) // (2 : ℕ) • x = 0} = 2 ^ n := by
  let half : AddCircle (1 : ℝ) := ((1 / 2 : ℝ) : AddCircle (1 : ℝ))
  have horder : addOrderOf half = 2 := by
    simpa [half] using
      (AddCircle.addOrderOf_period_div (p := (1 : ℝ)) (n := 2) (by decide))
  have hhalf : half ≠ 0 := by
    intro h
    simp [h] at horder
  let f (i : Fin 2) : {x : AddCircle (1 : ℝ) // (2 : ℕ) • x = 0} :=
    ⟨if i = 0 then 0 else half, by
      split
      · exact nsmul_zero _
      · exact horder ▸ addOrderOf_nsmul_eq_zero half⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j h
      have hval := congrArg Subtype.val h
      fin_cases i <;> fin_cases j <;> simp_all [f, Ne.symm hhalf]
    · intro x
      obtain ⟨k, hk, he⟩ := (AddCircle.nsmul_eq_zero_iff (by decide : 0 < 2)).mp x.property
      refine ⟨⟨k, hk⟩, Subtype.ext ?_⟩
      interval_cases k <;> simpa [f, half] using he
  let coords : {x : Fin n → AddCircle (1 : ℝ) // (2 : ℕ) • x = 0} ≃
      (Fin n → Fin 2) :=
    (Equiv.subtypeEquiv (Equiv.refl _) (fun _ ↦ funext_iff)).trans
      (Equiv.subtypePiEquivPi.trans (Equiv.piCongrRight fun _ ↦ (Equiv.ofBijective f hf).symm))
  rw [Nat.card_congr coords, Nat.card_fun, Nat.card_fin, Nat.card_fin]

/-- Paper: (D.1.4.2), p. 757. Two elementary presentations have the same real
dimension, torus dimension and free lattice rank, and isomorphic finite factors.
Deviation: The finite factors are compared up to group isomorphism. -/
theorem ElementaryLCAPresentation.invariants (e e' : ElementaryLCAPresentation G) :
    e.realDim = e'.realDim ∧ e.torusDim = e'.torusDim ∧ e.latticeRank = e'.latticeRank ∧
      Nonempty (e.finiteFactor ≃+ e'.finiteFactor) := by
  let model (p : ElementaryLCAPresentation G) :=
    ElementaryLieGroup p.realDim p.torusDim p.latticeRank p.finiteFactor
  let compare := e.equiv.symm.trans e'.equiv
  let φ : model e ≃ₜ+ model e' :=
    { MulEquiv.toAdditive compare.toMulEquiv with
      continuous_toFun := compare.continuous_toFun
      continuous_invFun := compare.continuous_invFun }
  let assoc (p : ElementaryLCAPresentation G) :
      (EuclideanSpace ℝ (Fin p.realDim) × (Fin p.torusDim → AddCircle (1 : ℝ))) ×
        ((Fin p.latticeRank → ℤ) × p.finiteFactor) ≃ₜ+ model p :=
    ContinuousAddEquiv.mk' (Homeomorph.prodAssoc _ _ _) (fun _ _ ↦ rfl)
  let ψ := (assoc e).trans (φ.trans (assoc e').symm)
  have connected_to_discrete {A B A' B' : Type} [AddZeroClass A] [AddZeroClass B]
      [AddZeroClass A'] [AddZeroClass B'] [TopologicalSpace A] [TopologicalSpace B]
      [TopologicalSpace A'] [TopologicalSpace B'] [PreconnectedSpace A] [DiscreteTopology B']
      (g : A × B ≃ₜ+ A' × B') (a : A) : (g (a, 0)).2 = 0 := by
    let f : A → B' := fun x ↦ (g (x, 0)).2
    have hf : Continuous f := (g.continuous_toFun.comp (continuous_id.prodMk continuous_const)).snd
    calc
      (g (a, 0)).2 = (g (0, 0)).2 := TotallyDisconnectedSpace.eq_of_continuous f hf a 0
      _ = 0 := congrArg Prod.snd (map_zero g)
  obtain ⟨⟨connected⟩, ⟨discrete⟩⟩ := continuousAddEquiv_factors_of_snd_eq_zero ψ
    (connected_to_discrete ψ) (connected_to_discrete ψ.symm)
  let swap {A B : Type} [AddZeroClass A] [AddZeroClass B]
      [TopologicalSpace A] [TopologicalSpace B] : B × A ≃ₜ+ A × B :=
    ContinuousAddEquiv.mk' (Homeomorph.prodComm _ _) (fun _ _ ↦ rfl)
  let γ := swap.trans (connected.trans swap.symm)
  have torus_to_real {m n m' n' : ℕ}
      (g : (Fin n → AddCircle (1 : ℝ)) × EuclideanSpace ℝ (Fin m) ≃ₜ+
        (Fin n' → AddCircle (1 : ℝ)) × EuclideanSpace ℝ (Fin m')) (x : Fin n → AddCircle (1 : ℝ)) :
      (g (x, 0)).2 = 0 :=
    elementary_torus_to_euclidean_eq_zero
      ((AddMonoidHom.snd _ _).comp (g.toAddEquiv.toAddMonoidHom.comp (AddMonoidHom.inl _ _)))
      (g.continuous_toFun.comp (continuous_id.prodMk continuous_const)).snd x
  obtain ⟨⟨torus⟩, ⟨real⟩⟩ := continuousAddEquiv_factors_of_snd_eq_zero γ
    (torus_to_real γ) (torus_to_real γ.symm)
  let δ := swap.trans (discrete.trans swap.symm)
  have finite_to_lattice {F F' : Type} [AddCommGroup F] [AddCommGroup F']
      [TopologicalSpace F] [TopologicalSpace F'] [Finite F] {r r' : ℕ}
      (g : F × (Fin r → ℤ) ≃ₜ+ F' × (Fin r' → ℤ)) (x : F) : (g (x, 0)).2 = 0 := by
    let f : F →+ (Fin r' → ℤ) :=
      (AddMonoidHom.snd _ _).comp (g.toAddEquiv.toAddMonoidHom.comp (AddMonoidHom.inl _ _))
    have h := congrArg f (addOrderOf_nsmul_eq_zero x)
    rw [map_nsmul, map_zero] at h
    exact (nsmul_eq_zero_iff_right (addOrderOf_pos x).ne').mp h
  obtain ⟨⟨finite⟩, ⟨lattice⟩⟩ := continuousAddEquiv_factors_of_snd_eq_zero δ
    (finite_to_lattice δ) (finite_to_lattice δ.symm)
  refine ⟨?_, ?_, ?_, ⟨finite.toAddEquiv⟩⟩
  · let linear := real.toAddEquiv.toRealLinearEquiv real.continuous_toFun real.continuous_invFun
    simpa only [finrank_euclideanSpace, Fintype.card_fin] using linear.toLinearEquiv.finrank_eq
  · have h := Nat.card_congr (torus.toEquiv.subtypeEquiv (p := fun x ↦ (2 : ℕ) • x = 0)
      (q := fun y ↦ (2 : ℕ) • y = 0) fun x ↦ by
        change (2 : ℕ) • x = 0 ↔ (2 : ℕ) • torus x = 0
        rw [← map_nsmul, ← map_zero torus, torus.injective.eq_iff])
    rw [elementary_torus_two_torsion_card, elementary_torus_two_torsion_card] at h
    exact Nat.pow_right_injective (by decide : 2 ≤ 2) h
  · simpa only [Module.finrank_pi, Fintype.card_fin] using
      lattice.toAddEquiv.toIntLinearEquiv.finrank_eq

variable [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]

open scoped Pointwise in
/-- Circle-valued characters lift to real logarithms on a simply connected chart.
These logarithms rule out nontrivial cyclic subgroups in a smaller neighborhood. -/
private theorem exists_nhds_one_of_isLocallyEuclidean (hG : IsLocallyEuclidean G) :
    ∃ W ∈ 𝓝 (1 : G), ∀ x : G, (∀ k : ℕ, x ^ k ∈ W) → x = 1 := by
  obtain ⟨n, ⟨charts⟩⟩ := hG
  let E := EuclideanSpace ℝ (Fin n)
  let e := chartAt E (1 : G)
  have he : (1 : G) ∈ e.source := mem_chart_source E 1
  obtain ⟨r, hr, hrb⟩ := Metric.mem_nhds_iff.mp (e.open_target.mem_nhds (e.map_source he))
  -- Pull back a ball to obtain a simply connected identity neighborhood.
  let B := Metric.ball (e 1) r
  let U := e.symm '' B
  have hU : IsOpen U := (e.symm.isOpen_image_iff_of_subset_source hrb).mpr Metric.isOpen_ball
  have h1U : (1 : G) ∈ U :=
    ⟨e 1, Metric.mem_ball_self hr, e.left_inv he⟩
  let b : B ≃ₜ U := e.symm.homeomorphOfImageSubsetSource hrb rfl
  let : ContractibleSpace B := (convex_ball _ _).contractibleSpace ⟨_, Metric.mem_ball_self hr⟩
  let : SimplyConnectedSpace U := b.symm.toHomotopyEquiv.simplyConnectedSpace
  let : LocallyPathConnectedSpace B := Metric.isOpen_ball.locallyPathConnectedSpace
  let : LocallyPathConnectedSpace U := b.locallyPathConnectedSpace
  let : LocallyConnectedSpace G := ChartedSpace.locallyConnectedSpace E G
  obtain ⟨V₀, hV₀, h1V₀, hprod⟩ := exists_open_nhds_one_mul_subset (hU.mem_nhds h1U)
  obtain ⟨V, ⟨hV, h1V, hVconn⟩, hVsub⟩ :=
    (LocallyConnectedSpace.open_connected_basis (1 : G)).mem_iff.mp (hV₀.mem_nhds h1V₀)
  have hVV : V * V ⊆ U := (Set.mul_subset_mul hVsub hVsub).trans hprod
  have hVU : V ⊆ U := fun x hx ↦ hVV (mul_one x ▸ Set.mul_mem_mul hx h1V)
  obtain ⟨K, hK, hKV, hKc⟩ := local_compact_nhds (hV.mem_nhds h1V)
  refine ⟨K, hK, fun x hx ↦ ?_⟩
  apply (pontryaginDual_pairing_separates (G := G)).1
  funext χ
  let χU : C(U, Circle) := ⟨fun u ↦ χ u, χ.continuous.comp continuous_subtype_val⟩
  let oneU : U := ⟨1, h1U⟩
  let oneV : V := ⟨1, h1V⟩
  obtain ⟨L, ⟨hL0, hL⟩, _⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
    χU oneU 0 (Circle.exp_zero.trans (map_one χ).symm)
  have hl (u : U) : Circle.exp (L u) = χ u := congrFun hL u
  let incl (v : V) : U := ⟨v, hVU v.property⟩
  let mul (p : V × V) : U := ⟨p.1 * p.2, hVV (Set.mul_mem_mul p.1.property p.2.property)⟩
  let : ConnectedSpace V := isConnected_iff_connectedSpace.mp hVconn
  -- Uniqueness of lifts makes the logarithm additive on pairs from the smaller neighborhood.
  have hAdd (a b : V) : L (mul (a, b)) = L (incl a) + L (incl b) := by
    have hMul : Continuous mul :=
      (continuous_subtype_val.comp continuous_fst).mul
        (continuous_subtype_val.comp continuous_snd) |>.subtype_mk _
    have hIncl : Continuous incl := continuous_subtype_val.subtype_mk _
    have hAgree : Circle.exp ∘ (fun p : V × V ↦ L (mul p)) =
        Circle.exp ∘ (fun p : V × V ↦ L (incl p.1) + L (incl p.2)) := by
      funext p
      simp [Circle.exp_add, hl, mul, incl, map_mul]
    have hStart : L (mul (oneV, oneV)) = L (incl oneV) + L (incl oneV) := by
      have hmul : mul (oneV, oneV) = oneU := Subtype.ext (one_mul 1)
      have hincl : incl oneV = oneU := rfl
      simp [hmul, hincl, hL0]
    exact congrFun (Circle.isCoveringMap_exp.eq_of_comp_eq (L.continuous.comp hMul)
      ((L.continuous.comp (hIncl.comp continuous_fst)).add
        (L.continuous.comp (hIncl.comp continuous_snd))) hAgree (oneV, oneV) hStart) (a, b)
  -- A nonzero logarithm would grow without bound along the powers inside the compact set.
  let z (k : ℕ) : V := ⟨x ^ k, hKV (hx k)⟩
  have hPow (k : ℕ) : L (incl (z k)) = k * L (incl (z 1)) := by
    induction k with
    | zero =>
      have hz : incl (z 0) = oneU := Subtype.ext (pow_zero x)
      simpa [hz] using hL0
    | succ k ih =>
      have hz : incl (z (k + 1)) = mul (z k, z 1) := Subtype.ext (by simp [incl, mul, z, pow_succ])
      rw [hz, hAdd, ih, Nat.cast_succ, add_mul, one_mul]
  have hKb : IsCompact (Subtype.val ⁻¹' K : Set U) := by
    exact IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hKc
      (Subtype.range_coe.symm ▸ hKV.trans hVU)
  obtain ⟨M, hM⟩ := (hKb.image L.continuous).isBounded.exists_norm_le
  have hZero : L (incl (z 1)) = 0 := by
    by_contra hNe
    obtain ⟨k, hk⟩ := exists_nat_gt (M / ‖L (incl (z 1))‖)
    have hLe := hM _ (mem_image_of_mem L (show incl (z k) ∈ Subtype.val ⁻¹' K from hx k))
    rw [hPow, norm_mul, Real.norm_natCast] at hLe
    exact (not_lt_of_ge hLe) ((div_lt_iff₀ (norm_pos_iff.mpr hNe)).mp hk)
  have hValue := hl (incl (z 1))
  rw [hZero, Circle.exp_zero] at hValue
  simpa [incl, z] using hValue.symm

/-- Paper: Theorem D.1.4.2, p. 757. A connected, locally Euclidean abelian
topological group admits an additive homomorphism from a finite-dimensional real vector
group that is a local homeomorphism.
Deviation: This isolates the local exponential map. After equipping the group with a
compatible Lie group structure, its exponential is a homomorphism by commutativity
and is a local homeomorphism by the inverse function theorem and translation. -/
theorem exists_euclidean_localHomeomorph {A : Type*} [AddCommGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [T2Space A] [LocallyCompactSpace A] [ConnectedSpace A]
    (hA : IsLocallyEuclidean A) :
    ∃ (k : ℕ) (f : EuclideanSpace ℝ (Fin k) →+ A), IsLocalHomeomorph f := by
  let : T2Space (Multiplicative A) := ‹T2Space A›
  obtain ⟨W, hW, hPow⟩ := exists_nhds_one_of_isLocallyEuclidean (G := Multiplicative A) hA
  obtain ⟨t, g, -, hker⟩ := exists_torusHom_of_noSmallCyclicSubgroups hW hPow
  obtain ⟨L, ρ, σ, hρ, hρ1, hgσ, hσc, hσmul, hσnhds⟩ :=
    exists_localSection_of_discrete_torusKernel g hker
  obtain ⟨f, hf⟩ := exists_addMonoidHom_eqOn_ball_of_local_additive hρ
    (fun v ↦ Multiplicative.toAdd (σ v)) (fun v w hv hw hvw ↦ hσmul v w hv hw hvw)
  have hcont : Continuous f := continuous_of_continuousAt_zero f <|
    ((continuousOn_congr hf).mpr hσc).continuousAt (Metric.ball_mem_nhds 0 hρ)
  have hopen : IsOpenMap f := by
    apply IsTopologicalAddGroup.isOpenMap_iff_nhds_zero.mpr
    rw [Filter.le_map_iff]
    intro U hU
    obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp hU
    have hδ : 0 < min ε ρ := lt_min hε hρ
    refine mem_of_superset (hσnhds _ hδ) ?_
    rintro _ ⟨v, hv, rfl⟩
    have hvε := Metric.ball_subset_ball (min_le_left ε ρ) hv
    have hvρ := Metric.ball_subset_ball (min_le_right ε ρ) hv
    exact ⟨v, hεU hvε, hf hvρ⟩
  have hinj : Set.InjOn f (Metric.ball 0 ρ) := by
    intro v hv w hw hvw
    have hv' := mem_ball_zero_iff.mp hv
    have hw' := mem_ball_zero_iff.mp hw
    have hσ : σ v = σ w := (hf hv).symm.trans (hvw.trans (hf hw))
    apply Subtype.ext
    refine circleExp_coord_injective (hv'.le.trans hρ1) (hw'.le.trans hρ1) fun i ↦ ?_
    rw [← hgσ v hv' i, ← hgσ w hw' i, hσ]
  have hlocal : IsLocalHomeomorph f := by
    refine isLocalHomeomorph_iff_isOpenEmbedding_restrict.mpr fun x ↦
      ⟨Metric.ball x ρ, Metric.ball_mem_nhds x hρ, ?_⟩
    refine IsOpenEmbedding.of_continuous_injective_isOpenMap
      (hcont.comp continuous_subtype_val) ?_
      (hopen.comp Metric.isOpen_ball.isOpenEmbedding_subtypeVal.isOpenMap)
    intro v w hvw
    have hv : (v : L) - x ∈ Metric.ball 0 ρ := by
      simpa only [mem_ball_zero_iff, ← dist_eq_norm] using Metric.mem_ball.mp v.property
    have hw : (w : L) - x ∈ Metric.ball 0 ρ := by
      simpa only [mem_ball_zero_iff, ← dist_eq_norm] using Metric.mem_ball.mp w.property
    change f (v : L) = f (w : L) at hvw
    apply Subtype.ext
    exact sub_left_inj.mp (hinj hv hw (by rw [map_sub, map_sub, hvw]))
  let e := (stdOrthonormalBasis ℝ L).repr.symm
  exact ⟨Module.finrank ℝ L, f.comp e.toLinearEquiv.toAddMonoidHom,
    hlocal.comp e.toHomeomorph.isLocalHomeomorph⟩

/-- Paper: Theorem D.1.4.2, p. 757. A locally Euclidean LCA group is a product
of real and torus factors and a discrete abelian group. -/
theorem lca_equiv_real_torus_discrete (hG : IsLocallyEuclidean G) :
    ∃ (m n : ℕ) (D : Type u) (_ : AddCommGroup D) (_ : TopologicalSpace D)
      (_ : DiscreteTopology D),
      Nonempty (G ≃ₜ* Multiplicative (EuclideanSpace ℝ (Fin m) ×
        (Fin n → AddCircle (1 : ℝ)) × D)) := by
  let A := Additive G
  have : T2Space A := ‹T2Space G›
  have : LocallyCompactSpace A := ‹LocallyCompactSpace G›
  let H := AddSubgroup.connectedComponentOfZero A
  obtain ⟨k, ⟨charts⟩⟩ := hG
  let : ChartedSpace (EuclideanSpace ℝ (Fin k)) A := charts
  have : LocallyConnectedSpace A := ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin k)) A
  have hH : IsOpen (H : Set A) := isOpen_connectedComponent
  have : ConnectedSpace H := isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  have : LocallyCompactSpace H := hH.isOpenEmbedding_subtypeVal.locallyCompactSpace
  obtain ⟨d, f, hf⟩ := exists_euclidean_localHomeomorph (A := H)
    ⟨k, ⟨TopologicalSpace.Opens.instChartedSpace (⟨H, hH⟩ : TopologicalSpace.Opens A)⟩⟩
  have hRange : IsOpen (f.range : Set H) := by
    rw [AddMonoidHom.coe_range, ← Set.image_univ]
    exact hf.isOpenMap _ isOpen_univ
  let U : OpenAddSubgroup H := ⟨f.range, hRange⟩
  have hSurj : Function.Surjective f := by
    have hTop := U.isClopen.eq_univ ⟨0, U.zero_mem⟩
    exact Set.range_eq_univ.mp (by
      change (f.range : Set H) = Set.univ at hTop
      simpa only [AddMonoidHom.coe_range] using hTop)
  have hF : IsOpenQuotientMap f := ⟨hSurj, hf.continuous, hf.isOpenMap⟩
  have hKer : DiscreteTopology f.ker := by
    obtain ⟨V, hV, h0, hinj⟩ := hf.isLocallyInjective 0
    rw [discreteTopology_iff_isOpen_singleton_zero]
    have hs : (Subtype.val : f.ker → EuclideanSpace ℝ (Fin d)) ⁻¹' V = {0} := by
      ext x
      exact ⟨fun hx ↦ Set.mem_singleton_iff.mpr
        (Subtype.ext (hinj hx h0 (x.property.trans (map_zero f).symm))),
        fun hx ↦ by
          obtain rfl := Set.mem_singleton_iff.mp hx
          exact h0⟩
    exact hs ▸ hV.preimage continuous_subtype_val
  let : DivisibleBy H ℤ := divisibleByOfSMulRightSurj H ℤ (fun {z} hz y ↦ by
    obtain ⟨x, rfl⟩ := hSurj y
    have hzR : (z : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hz
    refine ⟨f ((z : ℝ)⁻¹ • x), ?_⟩
    change z • f ((z : ℝ)⁻¹ • x) = f x
    rw [← map_zsmul, ← Int.cast_smul_eq_zsmul ℝ, smul_smul, mul_inv_cancel₀ hzR, one_smul])
  have : DiscreteTopology f.ker.toIntSubmodule := hKer
  -- Both quotient maps have the same kernel, so they induce a topological isomorphism.
  obtain ⟨m, n, q, hQ, hQker⟩ := exists_euclidean_torus_quotient f.ker.toIntSubmodule
  have hSameKer : f.ker = q.ker := hQker.symm
  let eF := QuotientAddGroup.quotientKerEquivOfSurjective f hF.surjective
  let eQ := QuotientAddGroup.quotientKerEquivOfSurjective q hQ.surjective
  let eKer := QuotientAddGroup.quotientAddEquivOfEq hSameKer
  let e := eF.symm.trans (eKer.trans eQ)
  have he (x : EuclideanSpace ℝ (Fin d)) : e (f x) = q x := by
    have hfmk : eF (QuotientAddGroup.mk x) = f x := rfl
    rw [← hfmk]
    change eQ (eKer (eF.symm (eF _))) = _
    rw [eF.symm_apply_apply]
    rfl
  have eH : H ≃ₜ+ EuclideanSpace ℝ (Fin m) × (Fin n → AddCircle (1 : ℝ)) :=
    { e with
      continuous_toFun := hF.continuous_comp_iff.mp
        (show Continuous (e ∘ f) from (funext he : e ∘ f = q) ▸ hQ.continuous)
      continuous_invFun := hQ.continuous_comp_iff.mp
        (show Continuous (e.symm ∘ q) from
          (funext fun x ↦ e.symm_apply_eq.mpr (he x).symm : e.symm ∘ q = f) ▸ hF.continuous) }
  obtain ⟨split⟩ := exists_continuousAddEquiv_prod_quotient_of_open H hH
  let D := A ⧸ H
  have : DiscreteTopology D := QuotientAddGroup.discreteTopology hH
  let product := split.toAddEquiv.trans (AddEquiv.prodCongr eH.toAddEquiv (AddEquiv.refl D))
  let assoc := Homeomorph.prodAssoc (EuclideanSpace ℝ (Fin m)) (Fin n → AddCircle (1 : ℝ)) D
  refine ⟨m, n, D, inferInstance, inferInstance, inferInstance, ⟨{
    AddEquiv.toMultiplicativeRight (product.trans AddEquiv.prodAssoc) with
    continuous_toFun := assoc.continuous.comp
      ((eH.continuous_toFun.prodMap continuous_id).comp split.continuous_toFun)
    continuous_invFun := split.continuous_invFun.comp
      ((eH.continuous_invFun.prodMap continuous_id).comp assoc.symm.continuous) }⟩⟩

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
/-- The compact-open neighborhoods of the trivial character test values on compact sets. -/
private theorem pontryaginDual_nhds_one_hasBasis :
    (𝓝 (1 : PontryaginDual G)).HasBasis
      (fun p : Set G × Set Circle ↦ IsCompact p.1 ∧ p.2 ∈ 𝓝 (1 : Circle))
      (fun p ↦ {χ | MapsTo χ p.1 p.2}) := by
  let f : PontryaginDual G → C(G, Circle) := ContinuousMonoidHom.toContinuousMap
  have hf : IsInducing f := ContinuousMonoidHom.isInducing_toContinuousMap G Circle
  rw [hf.nhds_eq_comap]
  exact ((𝓝 (1 : Circle)).basis_sets.nhds_continuousMapConst (X := G)).comap f

end Structure

section TorusCharts

variable {G : Type*} [CommGroup G] [TopologicalSpace G]
variable [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]

omit [T2Space G] [LocallyCompactSpace G] in
/-- Translating a chart at the identity gives charts everywhere. -/
theorem isLocallyEuclidean_of_chart_at_one {k : ℕ}
    (e : OpenPartialHomeomorph G (EuclideanSpace ℝ (Fin k))) (he : (1 : G) ∈ e.source) :
    IsLocallyEuclidean G := by
  classical
  exact ⟨k, ⟨{
    atlas := Set.range fun g : G ↦
      ((Homeomorph.mulLeft g⁻¹).toOpenPartialHomeomorph).trans e
    chartAt := fun g ↦ ((Homeomorph.mulLeft g⁻¹).toOpenPartialHomeomorph).trans e
    mem_chart_source := fun g ↦ by
      change g ∈ ((Homeomorph.mulLeft g⁻¹).toOpenPartialHomeomorph).source ∩
        (Homeomorph.mulLeft g⁻¹) ⁻¹' e.source
      refine ⟨trivial, ?_⟩
      simpa using he
    chart_mem_atlas := fun g ↦ ⟨g, rfl⟩ }⟩⟩

omit [T2Space G] in
/-- A continuous homomorphism to a finite-dimensional torus with discrete kernel makes
the group locally Euclidean. -/
theorem isLocallyEuclidean_of_torusHom_discreteKernel {ι : Type*} [Fintype ι]
    (f : G →ₜ* (ι → Circle)) (hf : DiscreteTopology f.toMonoidHom.ker) :
    IsLocallyEuclidean G := by
  classical
  obtain ⟨L, ρ, σ, hρ, hρ1, hfσ, hσc, hσmul, hσnhds⟩ :=
    exists_localSection_of_discrete_torusKernel f hf
  have hσ0 : σ 0 = 1 := by
    have e := hσmul 0 0 (by simpa using hρ) (by simpa using hρ) (by simpa using hρ)
    rw [add_zero] at e
    exact mul_eq_left.mp e.symm
  let B := Metric.ball (0 : L) ρ
  let τ : B → G := fun v ↦ σ v
  have hτc : Continuous τ := continuousOn_iff_continuous_domRestrict.mp hσc
  have hτinj : Function.Injective τ := by
    intro v w hvw
    have hv : ‖(v : L)‖ < ρ := mem_ball_zero_iff.mp v.2
    have hw : ‖(w : L)‖ < ρ := mem_ball_zero_iff.mp w.2
    apply Subtype.ext
    apply Subtype.ext
    refine circleExp_coord_injective (hv.le.trans hρ1) (hw.le.trans hρ1) fun i ↦ ?_
    rw [← hfσ v hv i, ← hfσ w hw i]
    exact congrArg (fun x ↦ f x i) hvw
  have hτopen : IsOpenMap τ := by
    intro S hS
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨v, hvS, rfl⟩
    have hv : ‖(v : L)‖ < ρ := mem_ball_zero_iff.mp v.2
    obtain ⟨δ, hδ, hδS⟩ := Metric.isOpen_iff.mp hS v hvS
    set δ' := min δ (ρ - ‖(v : L)‖) with hδ'def
    have hδ' : 0 < δ' := lt_min hδ (sub_pos.mpr hv)
    have hδ'1 : δ' ≤ δ := min_le_left _ _
    have hδ'2 : δ' ≤ ρ - ‖(v : L)‖ := min_le_right _ _
    have hnhds : (fun x ↦ σ v * x) '' (σ '' Metric.ball (0 : L) δ') ∈ 𝓝 (σ v) := by
      rw [← map_mul_left_nhds_one (σ v)]
      exact image_mem_map (hσnhds δ' hδ')
    apply Filter.mem_of_superset hnhds
    rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    have hw' : ‖w‖ < δ' := mem_ball_zero_iff.mp hw
    have hvw : ‖(v : L) + w‖ < ρ :=
      (norm_add_le _ _).trans_lt (by linarith)
    refine ⟨⟨(v : L) + w, mem_ball_zero_iff.mpr hvw⟩, hδS ?_, ?_⟩
    · rw [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm]
      simpa using hw'.trans_le hδ'1
    · exact (hσmul v w hv (by linarith [norm_nonneg (v : L)]) hvw)
  have hτ : IsOpenEmbedding τ := .of_continuous_injective_isOpenMap hτc hτinj hτopen
  let iso := (stdOrthonormalBasis ℝ L).repr
  let j : B → EuclideanSpace ℝ (Fin (Module.finrank ℝ L)) := fun v ↦ iso v
  have hj : IsOpenEmbedding j :=
    iso.toHomeomorph.isOpenEmbedding.comp Metric.isOpen_ball.isOpenEmbedding_subtypeVal
  have : Nonempty B := ⟨⟨0, Metric.mem_ball_self hρ⟩⟩
  let e := (hτ.toOpenPartialHomeomorph τ).symm.trans (hj.toOpenPartialHomeomorph j)
  have he : (1 : G) ∈ e.source := by
    simp only [e, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      IsOpenEmbedding.toOpenPartialHomeomorph_target,
      IsOpenEmbedding.toOpenPartialHomeomorph_source, preimage_univ, inter_univ]
    exact ⟨⟨0, Metric.mem_ball_self hρ⟩, hσ0⟩
  exact isLocallyEuclidean_of_chart_at_one e he

end TorusCharts

section Structure

universe u

variable {G : Type u} [CommGroup G] [TopologicalSpace G]
variable [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]

/-- Paper: Theorem D.1.4.3(1), p. 757. A locally compact Hausdorff abelian group
with a continuous homomorphism to a finite-dimensional torus and discrete kernel
is locally Euclidean.
Deviation: This isolates the local chart construction. On a sufficiently small
compact identity neighborhood the homomorphism is an embedding. In logarithm
coordinates its image near zero is a relatively closed local additive subgroup
of a finite-dimensional real vector space, hence locally a linear subspace.
Translation gives charts at every point. -/
theorem isLocallyEuclidean_of_discrete_torus_kernel {ι : Type*} [Finite ι]
    (f : G →ₜ* (ι → Circle)) (hf : DiscreteTopology f.toMonoidHom.ker) :
    IsLocallyEuclidean G := by
  let : Fintype ι := Fintype.ofFinite ι
  exact isLocallyEuclidean_of_torusHom_discreteKernel f hf

open scoped Pointwise in
/-- A neighborhood containing no nontrivial cyclic subgroup lets finitely many
characters detect the identity locally. -/
private theorem isLocallyEuclidean_of_noSmallCyclicSubgroups
    {W : Set G} (hW : W ∈ 𝓝 (1 : G))
    (hPow : ∀ x : G, (∀ k : ℕ, x ^ k ∈ W) → x = 1) : IsLocallyEuclidean G := by
  classical
  obtain ⟨K, hK, hKnhds⟩ := exists_compact_mem_nhds (1 : G)
  obtain ⟨V, hV, hOne, hVV⟩ := exists_open_nhds_one_mul_subset (inter_mem hKnhds hW)
  have hVW : V ⊆ W := fun x hx ↦ (hVV (mul_one x ▸ Set.mul_mem_mul hx hOne)).2
  let S (χ : PontryaginDual G) : Set G := {x | χ x ≠ 1}
  have hCover : K \ V ⊆ ⋃ χ, S χ := by
    intro x hx
    have hx1 : x ≠ 1 := fun h ↦ hx.2 (h ▸ hOne)
    have hSep := (pontryaginDual_pairing_separates (G := G)).1
    obtain ⟨χ, hχ⟩ : ∃ χ : PontryaginDual G, χ x ≠ 1 := by
      by_contra! hn
      exact hx1 (hSep (funext fun χ ↦ (hn χ).trans (map_one χ).symm))
    exact mem_iUnion.mpr ⟨χ, hχ⟩
  obtain ⟨t, ht⟩ := (hK.diff hV).elim_finite_subcover S
    (fun χ ↦ (isClosed_eq χ.continuous continuous_const).isOpen_compl) hCover
  let f : G →ₜ* (t → Circle) :=
    { toFun := fun x χ ↦ χ.val x
      map_one' := funext fun χ ↦ map_one χ.val
      map_mul' := fun x y ↦ funext fun χ ↦ map_mul χ.val x y
      continuous_toFun := continuous_pi fun χ ↦ χ.val.continuous }
  refine isLocallyEuclidean_of_discrete_torus_kernel f
    (discreteTopology_of_isOpen_singleton_one ?_)
  have hKer (x : f.toMonoidHom.ker) (hx : (x : G) ∈ V) : x = 1 := by
    have hr (k : ℕ) : (x : G) ^ k ∈ V := by
      induction k with
      | zero => simpa using hOne
      | succ k ih =>
        have hKmem : (x : G) ^ (k + 1) ∈ K :=
          (hVV (pow_succ (x : G) k ▸ Set.mul_mem_mul ih hx)).1
        by_contra hn
        obtain ⟨χ, hχt, hχ⟩ := mem_iUnion₂.mp (ht ⟨hKmem, hn⟩)
        have hχx : χ (x : G) = 1 :=
          congrFun (MonoidHom.mem_ker.mp x.property) ⟨χ, hχt⟩
        exact hχ (by rw [map_pow, hχx, one_pow])
    exact Subtype.ext (hPow x fun k ↦ hVW (hr k))
  have hPreimage : (Subtype.val : f.toMonoidHom.ker → G) ⁻¹' V = {1} := by
    ext x
    exact ⟨fun hx ↦ mem_singleton_iff.mpr (hKer x hx), by
      rintro (rfl : x = 1)
      exact hOne⟩
  exact hPreimage ▸ hV.preimage continuous_subtype_val

omit [T2Space G] in
/-- If the dual is locally Euclidean, the subgroup generated by a suitable compact
neighborhood has no nontrivial characters on its quotient, so it equals the whole group. -/
private theorem isCompactlyGeneratedGroup_of_dual_locallyEuclidean
    (h : IsLocallyEuclidean (PontryaginDual G)) : IsCompactlyGeneratedGroup G := by
  obtain ⟨W, hW, hPow⟩ := exists_nhds_one_of_isLocallyEuclidean h
  obtain ⟨⟨K, U⟩, ⟨hK, hU⟩, hSub⟩ := pontryaginDual_nhds_one_hasBasis.mem_iff.mp hW
  obtain ⟨L, hL, hLnhds⟩ := exists_compact_mem_nhds (1 : G)
  let H := Subgroup.closure (K ∪ L)
  refine ⟨K ∪ L, mem_of_superset hLnhds subset_union_right, hK.union hL, ?_⟩
  have hH : IsOpen (H : Set G) := H.isOpen_of_mem_nhds
    (mem_of_superset hLnhds (subset_union_right.trans Subgroup.subset_closure))
  let : DiscreteTopology (G ⧸ H) := QuotientGroup.discreteTopology hH
  let q : G →ₜ* (G ⧸ H) := ⟨QuotientGroup.mk' H, QuotientGroup.continuous_mk⟩
  have hKill (ψ : PontryaginDual (G ⧸ H)) : PontryaginDual.map q ψ = 1 := by
    let φ : G →ₜ* Circle := PontryaginDual.map q ψ
    apply hPow
    intro k
    apply hSub
    intro x hx
    have hqx : q x = 1 := (QuotientGroup.eq_one_iff x).mpr
      (Subgroup.subset_closure (Or.inl hx))
    change (φ ^ k) x ∈ U
    rw [ContinuousMonoidHom.pow_apply]
    change (PontryaginDual.map q ψ x) ^ k ∈ U
    rw [PontryaginDual.map_apply, hqx, map_one, one_pow]
    exact mem_of_mem_nhds hU
  refine eq_top_iff.mpr fun x _ ↦ (QuotientGroup.eq_one_iff x).mp ?_
  apply (pontryaginDual_pairing_separates (G := G ⧸ H)).1
  funext ψ
  exact DFunLike.congr_fun (hKill ψ) x |>.trans (map_one ψ).symm

-- Retain `T2Space G` in the existing signature.
set_option linter.unusedSectionVars false in
/-- Paper: Theorem D.1.4.3(1), p. 757. An LCA group is compactly generated
exactly when its dual is locally Euclidean. -/
theorem isCompactlyGeneratedGroup_iff_dual_locallyEuclidean :
    IsCompactlyGeneratedGroup G ↔ IsLocallyEuclidean (PontryaginDual G) := by
  constructor
  · rintro ⟨K, _, hK, hGen⟩
    have hC : Circle.centeredArc (Real.pi / 2) ∈ 𝓝 (1 : Circle) := by
      simpa using Circle.hasBasis_centeredArc_div_two_pow.mem_of_mem (i := 0) trivial
    refine isLocallyEuclidean_of_noSmallCyclicSubgroups
      (pontryaginDual_nhds_one_hasBasis.mem_of_mem (i := (K, _)) ⟨hK, hC⟩) ?_
    intro χ hχ
    have hTrivial : K ⊆ (χ : G →ₜ* Circle).toMonoidHom.ker := by
      intro x hx
      apply MonoidHom.mem_ker.mpr
      apply Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two
      intro k _
      let φ : G →ₜ* Circle := χ
      change φ x ^ k ∈ Circle.centeredArc (Real.pi / 2)
      rw [← ContinuousMonoidHom.pow_apply]
      exact hχ k hx
    have hTop : ⊤ ≤ (χ : G →ₜ* Circle).toMonoidHom.ker :=
      hGen ▸ (Subgroup.closure_le _).mpr hTrivial
    exact PontryaginDual.ext fun x ↦ MonoidHom.mem_ker.mp (hTop (Subgroup.mem_top x))
  · exact isCompactlyGeneratedGroup_of_dual_locallyEuclidean

open scoped Pointwise in
-- Retain the Hausdorff and local compactness assumptions in the existing signature.
set_option linter.unusedSectionVars false in
/-- Paper: Theorem D.1.4.3(1), p. 757. A closed subgroup of a compactly generated
LCA group is compactly generated. -/
theorem isCompactlyGeneratedGroup_closedSubgroup (hG : IsCompactlyGeneratedGroup G)
    (H : Subgroup G) (hH : IsClosed (H : Set G)) : IsCompactlyGeneratedGroup H := by
  classical
  obtain ⟨U, hU, hUc, hGen⟩ := hG
  -- Write every element as a product of finitely many fixed directions and a remainder in U.
  obtain ⟨t, ht⟩ := compact_covered_by_mul_left_translates
    ((hUc.union hUc.inv).mul hUc) ⟨1, mem_interior_iff_mem_nhds.mpr hU⟩
  let a (n : t → ℕ) : G := ∏ i : t, ((i : G)⁻¹) ^ n i
  have ha0 : a 0 = 1 := by simp [a]
  have haAdd (m n : t → ℕ) : a (m + n) = a m * a n := by
    simp only [a, Pi.add_apply, pow_add, Finset.prod_mul_distrib]
  have haSingle (i : t) : a (Pi.single i 1) = (i : G)⁻¹ := by
    unfold a
    rw [Finset.prod_eq_single i (fun j _ hj ↦ by rw [Pi.single_eq_of_ne hj, pow_zero])
      (fun hi ↦ (hi (Finset.mem_univ i)).elim), Pi.single_eq_same, pow_one]
  have hStep (x : G) (hx : x ∈ U ∪ U⁻¹) (y : G)
      (hy : ∃ n : t → ℕ, ∃ u ∈ U, y = a n * u) :
      ∃ n : t → ℕ, ∃ u ∈ U, x * y = a n * u := by
    obtain ⟨n, u, hu, rfl⟩ := hy
    obtain ⟨i, hi, hiu⟩ := mem_iUnion₂.mp (ht (Set.mul_mem_mul hx hu))
    change i * (x * u) ∈ U at hiu
    refine ⟨n + Pi.single ⟨i, hi⟩ 1, i * (x * u), hiu, ?_⟩
    rw [haAdd, haSingle]
    simp [mul_assoc, mul_left_comm]
  have hRepresent (x : G) : ∃ n : t → ℕ, ∃ u ∈ U, x = a n * u := by
    have hx : x ∈ Subgroup.closure U := hGen.symm ▸ Subgroup.mem_top x
    refine Subgroup.closure_induction_left (p := fun z _ ↦ ∃ n : t → ℕ, ∃ u ∈ U, z = a n * u)
      ⟨0, 1, mem_of_mem_nhds hU, by simp [ha0]⟩ ?_ ?_ hx
    · exact fun z hz y _ ↦ hStep z (Or.inl hz) y
    · exact fun z hz y _ ↦ hStep z⁻¹ (Or.inr (by simpa using hz)) y
  obtain ⟨V, hV, _, hVinv, hVV⟩ := exists_closed_nhds_one_inv_eq_mul_subset hU
  obtain ⟨s, hs⟩ := compact_covered_by_mul_left_translates hUc
    ⟨1, mem_interior_iff_mem_nhds.mpr hV⟩
  -- For each translate, Dickson's lemma bounds the minimal nonzero exponent vectors.
  let P (i : s) (n : t → ℕ) : Prop :=
    n ≠ 0 ∧ ∃ u ∈ U, (i : G) * u ∈ V ∧ a n * u ∈ H
  let M : Set (t → ℕ) := {0} ∪ ⋃ i : s, {n | Minimal (P i) n}
  have hM : M.Finite := (finite_singleton 0).union (finite_iUnion fun i ↦
    WellQuasiOrderedLE.finite_of_isAntichain (setOfPred_minimal_antichain (P i)))
  let K : Set G := (a '' M) * U
  let S : Set H := Subtype.val ⁻¹' K
  let J : Subgroup G := (Subgroup.closure S).map H.subtype
  have hK : IsCompact K := (hM.image a).isCompact.mul hUc
  have hUK : U ⊆ K := by
    intro u hu
    rw [← one_mul u, ← ha0]
    exact Set.mul_mem_mul (mem_image_of_mem a (Or.inl rfl)) hu
  have hMem (x : G) (hx : x ∈ H) (hxK : x ∈ K) : x ∈ J :=
    Subgroup.mem_map.mpr ⟨⟨x, hx⟩, Subgroup.subset_closure hxK, rfl⟩
  have hReduce (n : t → ℕ) : ∀ u ∈ U, a n * u ∈ H → a n * u ∈ J := by
    refine wellFounded_lt.induction (C := fun m ↦ ∀ u ∈ U, a m * u ∈ H → a m * u ∈ J) n ?_
    clear n
    intro n ih u hu hnu
    by_cases hn : n = 0
    · exact hMem _ hnu (Set.mul_mem_mul (mem_image_of_mem a (Or.inl hn)) hu)
    obtain ⟨i, hi, hiu⟩ := mem_iUnion₂.mp (hs hu)
    let j : s := ⟨i, hi⟩
    obtain ⟨m, hmn, hm⟩ := exists_minimal_le_of_wellFoundedLT (P j) n
      ⟨hn, u, hu, hiu, hnu⟩
    obtain ⟨hm0, v, hv, hiv, hmv⟩ := hm.prop
    obtain ⟨d, hd⟩ := exists_add_of_le hmn
    have hdn : d < n := by
      rw [hd]
      exact lt_add_of_pos_left d (lt_of_le_of_ne (fun i ↦ Nat.zero_le (m i)) hm0.symm)
    have huv : u / v ∈ U := by
      have hInv : (i * v)⁻¹ ∈ V := hVinv ▸ Set.mem_inv.mpr (by simpa using hiv)
      have hMul := hVV (Set.mul_mem_mul hiu hInv)
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hMul
    have hFactor : a n * u = (a m * v) * (a d * (u / v)) := by
      rw [hd, haAdd]
      simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    have hdH : a d * (u / v) ∈ H := by
      simpa only [hFactor, inv_mul_cancel_left] using H.mul_mem (H.inv_mem hmv) hnu
    rw [hFactor]
    exact J.mul_mem (hMem _ hmv (Set.mul_mem_mul (mem_image_of_mem a
      (Or.inr (mem_iUnion.mpr ⟨j, hm⟩))) hv)) (ih d hdn (u / v) huv hdH)
  refine ⟨S, continuous_subtype_val.continuousAt.preimage_mem_nhds (mem_of_superset hU hUK),
    hH.isClosedEmbedding_subtypeVal.isCompact_preimage hK, eq_top_iff.mpr ?_⟩
  intro x _
  obtain ⟨n, u, hu, hx⟩ := hRepresent x
  have hxJ : (x : G) ∈ J := hx ▸ hReduce n u hu (hx ▸ x.property)
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxJ
  exact (Subtype.ext hyx : y = x) ▸ hy

-- Retain the LCA and closedness assumptions in the existing signature.
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
/-- Paper: Theorem D.1.4.3(1), p. 757. The quotient of a compactly generated LCA
group by a closed subgroup is compactly generated. -/
theorem isCompactlyGeneratedGroup_quotient (hG : IsCompactlyGeneratedGroup G)
    (H : Subgroup G) (hH : IsClosed (H : Set G)) : IsCompactlyGeneratedGroup (G ⧸ H) := by
  obtain ⟨U, hU, hCompact, hGen⟩ := hG
  let q := QuotientGroup.mk' H
  have hq : IsOpenQuotientMap q := QuotientGroup.isOpenQuotientMap_mk
  refine ⟨q '' U, ?_, hCompact.image hq.continuous, ?_⟩
  · simpa only [map_one] using hq.isOpenMap.image_mem_nhds hU
  · rw [← MonoidHom.map_closure, hGen, Subgroup.map_top_of_surjective q hq.surjective]

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
/-- The real, torus and discrete factors of an elementary presentation give product charts. -/
private theorem locallyEuclidean_of_elementaryPresentation
    (e : ElementaryLCAPresentation G) : IsLocallyEuclidean G := by
  let R := Fin e.realDim → ℝ
  let T := ModelPi (fun _ : Fin e.torusDim ↦ ℝ)
  let D := (Fin e.latticeRank → ℤ) × e.finiteFactor
  let : ChartedSpace R (EuclideanSpace ℝ (Fin e.realDim)) :=
    (PiLp.homeomorph 2 (fun _ : Fin e.realDim ↦ ℝ)).symm.chartedSpace
  let : ChartedSpace ℝ (AddCircle (1 : ℝ)) :=
    (AddCircle.isLocalHomeomorph_coe (1 : ℝ)).chartedSpace QuotientAddGroup.mk_surjective
  let : ChartedSpace PUnit.{1} D := ChartedSpace.ofDiscreteTopology
  let M := ModelProd R (ModelProd T PUnit.{1})
  let charts : ChartedSpace M
      (ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor) :=
    prodChartedSpace _ _ _ _
  let : ChartedSpace M
      (Multiplicative (ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor)) := charts
  let : ChartedSpace M G := e.equiv.toHomeomorph.symm.chartedSpace
  let h : M ≃ₜ EuclideanSpace ℝ (Fin (e.realDim + e.torusDim)) :=
    (Homeomorph.prodCongr (Homeomorph.refl R) (Homeomorph.prodUnique T PUnit)).trans
      ((Fin.appendHomeomorph e.realDim e.torusDim).trans (PiLp.homeomorph 2 _).symm)
  let : ChartedSpace (EuclideanSpace ℝ (Fin (e.realDim + e.torusDim))) M := h.symm.chartedSpace
  exact ⟨e.realDim + e.torusDim, ⟨ChartedSpace.comp _ M G⟩⟩

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
/-- An elementary presentation gives a compact generating neighborhood. -/
private theorem compactlyGenerated_of_elementaryPresentation
    (e : ElementaryLCAPresentation G) : IsCompactlyGeneratedGroup G := by
  let R := EuclideanSpace ℝ (Fin e.realDim)
  let T := Fin e.torusDim → AddCircle (1 : ℝ)
  let D := (Fin e.latticeRank → ℤ) × e.finiteFactor
  obtain ⟨K, hK, hKnhds⟩ := exists_compact_mem_nhds (0 : R)
  have hKgen : AddSubgroup.closure K = ⊤ := by
    let H := AddSubgroup.closure K
    have hH := H.isOpen_of_mem_nhds (mem_of_superset hKnhds AddSubgroup.subset_closure)
    exact SetLike.coe_injective ((OpenAddSubgroup.mk H hH).isClopen.eq_univ ⟨0, H.zero_mem⟩)
  obtain ⟨S, hSgen, hS⟩ := AddGroup.fg_iff.mp (inferInstance : AddGroup.FG D)
  let U : Set (ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor) :=
    K ×ˢ ((univ : Set T) ×ˢ insert 0 S)
  have hD : insert 0 S ∈ 𝓝 (0 : D) := (isOpen_discrete _).mem_nhds (mem_insert _ _)
  have hU : U ∈ 𝓝 0 := prod_mem_nhds hKnhds (prod_mem_nhds univ_mem hD)
  have hUc : IsCompact U := hK.prod (isCompact_univ.prod (hS.insert 0).isCompact)
  have hUgen : AddSubgroup.closure U = ⊤ := by
    change AddSubgroup.closure (K ×ˢ ((univ : Set T) ×ˢ insert 0 S)) = ⊤
    rw [AddSubgroup.closure_prod (mem_of_mem_nhds hKnhds) (by simp),
      AddSubgroup.closure_prod (mem_univ (0 : T)) (mem_insert 0 S), hKgen,
      AddSubgroup.closure_univ, AddSubgroup.closure_insert_zero, hSgen,
      AddSubgroup.top_prod_top, AddSubgroup.top_prod_top]
  let f := e.equiv.symm.toMulEquiv.toMonoidHom
  let V : Set (Multiplicative (ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor)) :=
    Multiplicative.toAdd ⁻¹' U
  have hV : V ∈ 𝓝 1 := hU
  refine ⟨f '' V, ?_, hUc.image e.equiv.symm.continuous, ?_⟩
  · have h := e.equiv.symm.toHomeomorph.isOpenMap.image_mem_nhds hV
    change f '' V ∈ 𝓝 (f 1) at h
    rwa [map_one] at h
  · have hVgen : Subgroup.closure V = ⊤ := by
      rw [← AddSubgroup.toSubgroup_closure, hUgen]
      rfl
    rw [← MonoidHom.map_closure, hVgen,
      Subgroup.map_top_of_surjective f e.equiv.symm.surjective]

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
/-- In a real–torus–discrete decomposition of a compactly generated group, the discrete
factor is finitely generated and splits as a free abelian group times a finite group. -/
private theorem elementaryPresentation_of_compactlyGenerated
    {m n : ℕ} {D : Type*} [AddCommGroup D] [TopologicalSpace D] [DiscreteTopology D]
    (hG : IsCompactlyGeneratedGroup G)
    (e : G ≃ₜ* Multiplicative (EuclideanSpace ℝ (Fin m) × (Fin n → AddCircle (1 : ℝ)) × D)) :
    Nonempty (ElementaryLCAPresentation G) := by
  classical
  obtain ⟨U, _, hUc, hUgen⟩ := hG
  let R := EuclideanSpace ℝ (Fin m)
  let T := Fin n → AddCircle (1 : ℝ)
  let eA := MulEquiv.toAdditiveLeft e.toMulEquiv
  let p := ((AddMonoidHom.snd T D).comp (AddMonoidHom.snd R (T × D))).comp eA.toAddMonoidHom
  have hp : Function.Surjective p := fun d ↦
    ⟨eA.symm (0, 0, d), congrArg (fun a : R × T × D ↦ a.2.2) (eA.apply_symm_apply _)⟩
  have hpc : Continuous p := (continuous_snd.comp continuous_snd).comp e.continuous
  let V : Set (Additive G) := Additive.toMul ⁻¹' U
  have hVgen : AddSubgroup.closure V = ⊤ := by
    rw [← Subgroup.toAddSubgroup_closure, hUgen]
    rfl
  have : AddGroup.FG D := AddGroup.fg_iff.mpr
    ⟨p '' V, by
      rw [← AddMonoidHom.map_closure, hVgen,
        AddSubgroup.map_top_of_surjective p hp],
      (hUc.image hpc).finite DiscreteTopology.isDiscrete⟩
  obtain ⟨r, ι, _, q, hq, k, ⟨d⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod D
  let F := (i : ι) → ZMod (q i ^ k i)
  let (i : ι) : NeZero (q i ^ k i) := ⟨pow_ne_zero _ (hq i).ne_zero⟩
  let : Fintype F := inferInstanceAs (Fintype ((i : ι) → ZMod (q i ^ k i)))
  let : TopologicalSpace F := ⊥
  let : DiscreteTopology F := ⟨rfl⟩
  let d' : D ≃+ (Fin r → ℤ) × F :=
    d.trans (AddEquiv.prodCongr Finsupp.addEquivFunOnFinite (DirectSum.addEquivProd _))
  let e' := AddEquiv.toMultiplicativeRight
    (eA.trans (AddEquiv.prodCongr (AddEquiv.refl R) (AddEquiv.prodCongr (AddEquiv.refl T) d')))
  refine ⟨{ realDim := m, torusDim := n, latticeRank := r, finiteFactor := F
            equiv := ?_ }⟩
  exact { e' with
    continuous_toFun := (continuous_id.prodMap
      (continuous_id.prodMap (continuous_of_discreteTopology (f := d')))).comp e.continuous
    continuous_invFun := e.symm.continuous.comp (continuous_id.prodMap
      (continuous_id.prodMap (continuous_of_discreteTopology (f := d'.symm)))) }

/-- Paper: Theorem D.1.4.3(2), p. 757. An LCA group has an elementary presentation
exactly when it is compactly generated and locally Euclidean. -/
theorem lca_elementary_iff :
    (IsCompactlyGeneratedGroup G ∧ IsLocallyEuclidean G) ↔
      Nonempty (ElementaryLCAPresentation G) := by
  constructor
  · rintro ⟨hCompact, hEuclidean⟩
    obtain ⟨m, n, D, _, _, _, ⟨e⟩⟩ := lca_equiv_real_torus_discrete hEuclidean
    exact elementaryPresentation_of_compactlyGenerated hCompact e
  · rintro ⟨e⟩
    exact ⟨compactlyGenerated_of_elementaryPresentation e,
      locallyEuclidean_of_elementaryPresentation e⟩

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
/-- Paper: (D.1.4.3), p. 758. The indexing set consists of open compactly
generated subgroups ordered by inclusion. -/
abbrev OpenCompactlyGeneratedSubgroups (G : Type*) [CommGroup G] [TopologicalSpace G] :=
  {H : Subgroup G // IsOpen (H : Set G) ∧ IsCompactlyGeneratedGroup H}

-- Retain `T2Space G` in the existing signature.
set_option linter.unusedSectionVars false in
/-- Paper: (D.1.4.3), p. 758. The open compactly generated subgroups are filtered
and cover the group. The topology is final for their open inclusions. -/
theorem openCompactlyGeneratedSubgroups_colimit :
    IsDirectedOrder (OpenCompactlyGeneratedSubgroups G) ∧
      (∀ x : G, ∃ H : OpenCompactlyGeneratedSubgroups G, x ∈ H.val) ∧
      (∀ U : Set G, IsOpen U ↔
        ∀ H : OpenCompactlyGeneratedSubgroups G, IsOpen (Subtype.val ⁻¹' U : Set H.val)) := by
  let ofCompactNeighborhood (K : Set G) (hK : IsCompact K) (hKnhds : K ∈ 𝓝 (1 : G)) :
      OpenCompactlyGeneratedSubgroups G := by
    let H := Subgroup.closure K
    have hH : IsOpen (H : Set G) := H.isOpen_of_mem_nhds
      (mem_of_superset hKnhds Subgroup.subset_closure)
    exact ⟨H, hH, Subtype.val ⁻¹' K,
      continuous_subtype_val.continuousAt.preimage_mem_nhds hKnhds,
      (H.isClosed_of_isOpen hH).isClosedEmbedding_subtypeVal.isCompact_preimage hK,
      Subgroup.closure_preimage_eq_top K⟩
  have hCover (x : G) : ∃ H : OpenCompactlyGeneratedSubgroups G, x ∈ H.val := by
    obtain ⟨K, hK, hKnhds⟩ := exists_compact_mem_nhds (1 : G)
    exact ⟨ofCompactNeighborhood (insert x K) (hK.insert x)
      (mem_of_superset hKnhds (subset_insert x K)), Subgroup.subset_closure (mem_insert x K)⟩
  refine ⟨⟨?_⟩, hCover, ?_⟩
  · intro H J
    obtain ⟨A, hAnhds, hA, hAgen⟩ := H.property.2
    obtain ⟨B, _, hB, hBgen⟩ := J.property.2
    have hAnhds' : H.val.subtype '' A ∈ 𝓝 (1 : G) :=
      H.property.1.isOpenEmbedding_subtypeVal.isOpenMap.image_mem_nhds hAnhds
    let L := ofCompactNeighborhood (H.val.subtype '' A ∪ J.val.subtype '' B)
      ((hA.image continuous_subtype_val).union (hB.image continuous_subtype_val))
      (mem_of_superset hAnhds' subset_union_left)
    have hL : L.val = H.val ⊔ J.val := by
      change Subgroup.closure (H.val.subtype '' A ∪ J.val.subtype '' B) = _
      rw [Subgroup.closure_union, ← MonoidHom.map_closure, ← MonoidHom.map_closure,
        hAgen, hBgen, Subgroup.map_top, Subgroup.map_top, Subgroup.range_subtype,
        Subgroup.range_subtype]
    exact ⟨L, le_sup_left.trans hL.ge, le_sup_right.trans hL.ge⟩
  · intro U
    refine ⟨fun hU H ↦ hU.preimage continuous_subtype_val, ?_⟩
    intro hU
    refine isOpen_iff_mem_nhds.mpr fun x hx ↦ ?_
    obtain ⟨H, hxH⟩ := hCover x
    have hImage := H.property.1.isOpenEmbedding_subtypeVal.isOpenMap _ (hU H)
    exact mem_of_superset (hImage.mem_nhds ⟨⟨x, hxH⟩, hx, rfl⟩)
      (fun _ ⟨_, hy, hEq⟩ ↦ hEq ▸ hy)

omit [T2Space G] in
/-- Every compact set is contained in an open compactly generated subgroup. -/
private theorem exists_openCompactlyGeneratedSubgroup_contains {K : Set G} (hK : IsCompact K) :
    ∃ H : OpenCompactlyGeneratedSubgroups G, K ⊆ (H.val : Set G) := by
  obtain ⟨U, hU, hU₁⟩ := exists_compact_mem_nhds (1 : G)
  let H := Subgroup.closure (U ∪ K)
  have hSubset : U ∪ K ⊆ (H : Set G) := Subgroup.subset_closure
  have hOpen : IsOpen (H : Set G) :=
    H.isOpen_of_mem_nhds (mem_of_superset hU₁ (subset_union_left.trans hSubset))
  refine ⟨⟨H, hOpen, ⟨Subtype.val ⁻¹' (U ∪ K), ?_, ?_, ?_⟩⟩,
    subset_union_right.trans hSubset⟩
  · exact continuous_subtype_val.continuousAt.preimage_mem_nhds
      (mem_of_superset hU₁ subset_union_left)
  · exact IsEmbedding.subtypeVal.isInducing.isCompact_preimage' (hU.union hK)
      (Subtype.range_coe.symm ▸ hSubset)
  · exact Subgroup.closure_preimage_eq_top _

/-- Paper: Lemma D.1.4.4, p. 758. Evaluation on the open compactly generated
subgroups of the dual identifies the group with their duals' inverse limit.
Deviation: The limit is expressed as the range in the product, with the subspace topology. -/
theorem lca_dualSubgroups_inverseLimit :
    let I := OpenCompactlyGeneratedSubgroups (PontryaginDual G)
    ∃ γ : G →ₜ* ((H : I) → PontryaginDual H.val),
      (∀ x H (χ : H.val), γ x H χ = χ.val x) ∧ IsEmbedding γ ∧
        range γ = {a | ∀ (H J : I) (h : H ≤ J) (χ : H.val),
          a H χ = a J (Subgroup.inclusion h χ)} := by
  classical
  let I := OpenCompactlyGeneratedSubgroups (PontryaginDual G)
  change ∃ γ : G →ₜ* ((H : I) → PontryaginDual H.val), _
  have hCover (χ : PontryaginDual G) : ∃ H : I, χ ∈ H.val := by
    obtain ⟨H, hH⟩ := exists_openCompactlyGeneratedSubgroup_contains (isCompact_singleton (x := χ))
    exact ⟨H, hH (mem_singleton χ)⟩
  have hDirected (H J : I) : ∃ L : I, H ≤ L ∧ J ≤ L := by
    obtain ⟨U, _, hU, hUgen⟩ := H.property.2
    obtain ⟨V, _, hV, hVgen⟩ := J.property.2
    obtain ⟨L, hL⟩ := exists_openCompactlyGeneratedSubgroup_contains
      ((hU.image continuous_subtype_val).union (hV.image continuous_subtype_val))
    have hLe (M : I) {S : Set M.val} (hGen : Subgroup.closure S = ⊤)
        (hSub : Subtype.val '' S ⊆ (L.val : Set (PontryaginDual G))) : M ≤ L := by
      have hTop : (⊤ : Subgroup M.val) ≤ L.val.comap M.val.subtype :=
        hGen ▸ (Subgroup.closure_le _).mpr (fun x hx ↦ hSub (mem_image_of_mem Subtype.val hx))
      exact fun x hx ↦ hTop (Subgroup.mem_top (⟨x, hx⟩ : M.val))
    exact ⟨L, hLe H hUgen (subset_union_left.trans hL), hLe J hVgen (subset_union_right.trans hL)⟩
  let restrict (H : I) : PontryaginDual (PontryaginDual G) →ₜ* PontryaginDual H.val :=
    PontryaginDual.map ⟨H.val.subtype, continuous_subtype_val⟩
  let γ : G →ₜ* ((H : I) → PontryaginDual H.val) :=
    { toFun := fun x H ↦ restrict H (pontryaginDual_eval x)
      map_one' := funext fun H ↦ (restrict H).comp pontryaginDual_eval |>.map_one
      map_mul' := fun x y ↦ funext fun H ↦ (restrict H).comp pontryaginDual_eval |>.map_mul x y
      continuous_toFun := continuous_pi fun H ↦ (restrict H).continuous.comp
        (pontryaginDual_eval (G := G)).continuous }
  have hEval (x : G) (H : I) (χ : H.val) : γ x H χ = χ.val x := rfl
  refine ⟨γ, hEval, ⟨?_, ?_⟩, ?_⟩
  · rw [IsTopologicalGroup.isInducing_iff_nhds_one]
    refine le_antisymm ?_ ?_
    · have h : Tendsto γ (𝓝 1) (𝓝 (γ 1)) := γ.continuous.tendsto 1
      rw [map_one] at h
      exact h.le_comap
    · intro U hU
      -- A single coordinate contains all the characters needed to test this neighborhood.
      obtain ⟨K, hK, hTest⟩ := exists_pontryaginDual_compact_test hU
      obtain ⟨H, hH⟩ := exists_openCompactlyGeneratedSubgroup_contains hK
      have hKH : IsCompact (Subtype.val ⁻¹' K : Set H.val) :=
        IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hK (Subtype.range_coe.symm ▸ hH)
      let V : Set (PontryaginDual H.val) :=
        {ψ | MapsTo ψ (Subtype.val ⁻¹' K) (Metric.ball 1 (1 / 4))}
      have hV : IsOpen V :=
        (ContinuousMap.isOpen_setOfPred_mapsTo hKH Metric.isOpen_ball).preimage
          (ContinuousMonoidHom.isInducing_toContinuousMap H.val Circle).continuous
      refine Filter.mem_comap.mpr ⟨(fun a ↦ a H) ⁻¹' V,
        (hV.preimage (continuous_apply H)).mem_nhds ?_, ?_⟩
      · intro χ _
        simp [Metric.mem_ball]
      · intro x hx
        apply hTest x
        intro χ hχ
        exact hx (show (⟨χ, hH hχ⟩ : H.val) ∈ Subtype.val ⁻¹' K from hχ)
  · intro x y hxy
    apply (pontryaginDual_pairing_separates (G := G)).1
    funext χ
    obtain ⟨H, hH⟩ := hCover χ
    exact congrArg (fun a ↦ a H ⟨χ, hH⟩) hxy
  · ext a
    constructor
    · rintro ⟨x, rfl⟩ H J h χ
      rfl
    · intro ha
      change ∀ (H J : I) (h : H ≤ J) (χ : H.val),
        a H χ = a J (Subgroup.inclusion h χ) at ha
      choose H hH using hCover
      let f (χ : PontryaginDual G) := a (H χ) ⟨χ, hH χ⟩
      -- Compatibility makes the chosen subgroup irrelevant.
      have hf (J : I) (χ : J.val) : f χ.val = a J χ := by
        obtain ⟨L, h₁, h₂⟩ := hDirected (H χ.val) J
        exact (ha _ _ h₁ _).trans (ha _ _ h₂ χ).symm
      let J := H 1
      let ψ : PontryaginDual (PontryaginDual G) :=
        { toFun := f
          map_one' := (hf J 1).trans (map_one (a J))
          map_mul' := fun χ ξ ↦ by
            obtain ⟨L, hχ, hξ⟩ := hDirected (H χ) (H ξ)
            let χL : L.val := ⟨χ, hχ (hH χ)⟩
            let ξL : L.val := ⟨ξ, hξ (hH ξ)⟩
            exact (hf L (χL * ξL)).trans
              ((map_mul (a L) χL ξL).trans (congrArg₂ (· * ·) (hf L χL).symm (hf L ξL).symm))
          continuous_toFun := by
            rw [continuous_iff_continuousAt]
            intro χ
            let J := H χ
            have hComp : f ∘ (Subtype.val : J.val → PontryaginDual G) = a J := funext (hf J)
            exact J.property.1.isOpenEmbedding_subtypeVal.continuousAt_iff.mp
              (hComp.symm ▸ (a J).continuous.continuousAt (x := (⟨χ, hH χ⟩ : J.val))) }
      obtain ⟨e, he⟩ := pontryaginDual_bidual (G := G)
      refine ⟨e.symm ψ, funext fun J ↦ PontryaginDual.ext fun χ ↦ ?_⟩
      rw [hEval, ← he, e.apply_symm_apply]
      exact hf J χ

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
/-- Paper: Definition D.1.4.5, p. 758. The annihilator consists of characters
whose restriction to the subgroup is trivial. -/
def lcaAnnihilator (H : Subgroup G) : Subgroup (PontryaginDual G) :=
  (PontryaginDual.map (⟨H.subtype, continuous_subtype_val⟩ : H →ₜ* G)).toMonoidHom.ker

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
/-- Paper: Definition D.1.4.5, p. 758. The annihilator in the original group is
the intersection of the kernels of the characters in the given subgroup. -/
def lcaDualAnnihilator (J : Subgroup (PontryaginDual G)) : Subgroup G :=
  ⨅ χ : J, (show G →ₜ* Circle from χ.val).toMonoidHom.ker

/-- Paper: Definition D.1.4.5, p. 758. A character is in the annihilator exactly
when its value on every element of the subgroup is one. -/
theorem mem_lcaAnnihilator_iff (H : Subgroup G) (χ : PontryaginDual G) :
    χ ∈ lcaAnnihilator H ↔ ∀ x : H, χ x.val = 1 := by
  rw [lcaAnnihilator, MonoidHom.mem_ker]
  constructor
  · intro h x
    exact congrArg (fun ψ : PontryaginDual H ↦ ψ x) h
  · exact fun h ↦ PontryaginDual.ext h

/-- Paper: Definition D.1.4.5, p. 758. A group element is in the dual annihilator
exactly when every character of the subgroup takes value one there. -/
theorem mem_lcaDualAnnihilator_iff (J : Subgroup (PontryaginDual G)) (x : G) :
    x ∈ lcaDualAnnihilator J ↔ ∀ χ : J, χ.val x = 1 :=
  Subgroup.mem_iInf

-- Retain `T2Space G` in the existing signature.
set_option linter.unusedSectionVars false in
/-- Paper: Lemma D.1.4.6(1), p. 758. Taking the annihilator twice recovers a
closed subgroup under the evaluation pairing. -/
theorem lcaDualAnnihilator_annihilator (H : Subgroup G) (hH : IsClosed (H : Set G)) :
    lcaDualAnnihilator (lcaAnnihilator H) = H := by
  ext x
  rw [mem_lcaDualAnnihilator_iff]
  constructor
  · intro hx
    let : T1Space (G ⧸ H) := QuotientGroup.t1Space_iff.mpr hH
    let q : G →ₜ* (G ⧸ H) := ⟨QuotientGroup.mk' H, QuotientGroup.continuous_mk⟩
    apply (QuotientGroup.eq_one_iff x).mp
    apply (pontryaginDual_pairing_separates (G := G ⧸ H)).1
    funext ψ
    have hψ : PontryaginDual.map q ψ ∈ lcaAnnihilator H := by
      apply (mem_lcaAnnihilator_iff H _).mpr
      intro y
      have hy : q y.val = 1 := (QuotientGroup.eq_one_iff y.val).mpr y.property
      rw [PontryaginDual.map_apply, hy, map_one]
    exact (hx ⟨PontryaginDual.map q ψ, hψ⟩).trans (map_one ψ).symm
  · intro hx χ
    exact (mem_lcaAnnihilator_iff H χ.val).mp χ.property ⟨x, hx⟩

omit [T2Space G] in
/-- A compact subset of a quotient of a locally compact group lies in the image of a compact set. -/
private theorem exists_isCompact_quotient_preimage (H : Subgroup G) {K : Set (G ⧸ H)}
    (hK : IsCompact K) : ∃ C : Set G, IsCompact C ∧ K ⊆ QuotientGroup.mk '' C := by
  obtain ⟨L, hLcomp, hL⟩ := exists_compact_mem_nhds (1 : G)
  have hU : QuotientGroup.mk '' L ∈ 𝓝 (1 : G ⧸ H) :=
    (QuotientGroup.isOpenMap_coe (N := H)).image_mem_nhds hL
  obtain ⟨t, ht⟩ := compact_covered_by_mul_left_translates hK
    ⟨(1 : G ⧸ H), mem_interior_iff_mem_nhds.mpr hU⟩
  refine ⟨⋃ g ∈ t, Homeomorph.mulLeft (g.out)⁻¹ '' L,
    t.isCompact_biUnion fun g _ =>
      hLcomp.image (Homeomorph.mulLeft (g.out)⁻¹).continuous, ?_⟩
  intro k hk
  obtain ⟨g, hg, hkU⟩ := mem_iUnion₂.mp (ht hk)
  rw [mem_preimage, mem_image] at hkU
  obtain ⟨y, hy, hgy⟩ := hkU
  refine ⟨(g.out)⁻¹ * y, mem_iUnion₂.mpr ⟨g, hg, mem_image_of_mem _ hy⟩, ?_⟩
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.out_eq', hgy,
    inv_mul_cancel_left]

/-- Paper: Lemma D.1.4.6(2), p. 758. Pullback by the quotient map identifies
the dual of a quotient with the annihilator. -/
theorem lcaQuotientDual_equiv_annihilator (H : Subgroup G) (hH : IsClosed (H : Set G)) :
    ∃ e : PontryaginDual (G ⧸ H) ≃ₜ* lcaAnnihilator H,
      ∀ (χ : PontryaginDual (G ⧸ H)) x, (e χ).val x = χ (QuotientGroup.mk x) := by
  -- Closedness of `H` makes the quotient Hausdorff.
  have hpre : QuotientGroup.mk ⁻¹' ({1} : Set (G ⧸ H)) = (H : Set G) := by
    simpa [QuotientGroup.mk_one] using QuotientGroup.preimage_mk_one H
  have : T2Space (G ⧸ H) := IsTopologicalGroup.t2Space_iff_one_closed.mpr <| by
    rw [← (QuotientGroup.isQuotientMap_mk H).isCoinducing.isClosed_preimage, hpre]
    exact hH
  let q : G →ₜ* G ⧸ H :=
    { toMonoidHom := QuotientGroup.mk' H
      continuous_toFun := QuotientGroup.continuous_mk }
  have hq (x : G) : q x = QuotientGroup.mk x := by
    change QuotientGroup.mk' H x = QuotientGroup.mk x
    exact QuotientGroup.mk'_apply H x
  have hker (ψ : lcaAnnihilator H) : H ≤ ψ.val.toMonoidHom.ker := by
    intro x hx
    exact (mem_lcaAnnihilator_iff H ψ.val).1 ψ.property ⟨x, hx⟩
  let toAnn : PontryaginDual (G ⧸ H) →* lcaAnnihilator H :=
    { toFun := fun χ => ⟨PontryaginDual.map q χ, by
        rw [mem_lcaAnnihilator_iff]
        intro x
        rw [PontryaginDual.map_apply]
        have : q x.val = 1 := by
          change QuotientGroup.mk x.val = 1
          exact (QuotientGroup.eq_one_iff _).2 x.property
        rw [this, map_one]⟩
      map_one' := Subtype.ext (map_one (PontryaginDual.map q))
      map_mul' := fun χ φ => Subtype.ext (map_mul (PontryaginDual.map q) χ φ) }
  let fromAnnFun (ψ : lcaAnnihilator H) : PontryaginDual (G ⧸ H) :=
    { toMonoidHom := QuotientGroup.lift H ψ.val.toMonoidHom (hker ψ)
      continuous_toFun :=
        (QuotientGroup.isQuotientMap_mk H).continuous_iff.2 ψ.val.continuous_toFun }
  have happly (ψ : lcaAnnihilator H) (x : G) :
      fromAnnFun ψ (QuotientGroup.mk x) = ψ.val x := by
    dsimp [fromAnnFun]
    exact QuotientGroup.lift_mk' H (hker ψ) x
  let fromAnn : lcaAnnihilator H →* PontryaginDual (G ⧸ H) :=
    { toFun := fromAnnFun
      map_one' := by
        apply PontryaginDual.ext
        intro y
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
        rw [happly 1 x]
        rfl
      map_mul' := fun ψ φ => by
        apply PontryaginDual.ext
        intro y
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
        rw [happly (ψ * φ) x]
        have hr :
            (fromAnnFun ψ * fromAnnFun φ) (QuotientGroup.mk x) =
              fromAnnFun ψ (QuotientGroup.mk x) * fromAnnFun φ (QuotientGroup.mk x) :=
          ContinuousMonoidHom.mul_apply _ _ _
        rw [hr, happly ψ x, happly φ x, Subgroup.coe_mul]
        rfl }
  have hinv_left (χ : PontryaginDual (G ⧸ H)) : fromAnn (toAnn χ) = χ := by
    apply PontryaginDual.ext
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    dsimp [fromAnn]
    rw [happly (toAnn χ) x]
    dsimp [toAnn]
    rw [hq]
  have hinv_right (ψ : lcaAnnihilator H) : toAnn (fromAnn ψ) = ψ := by
    apply Subtype.ext
    apply PontryaginDual.ext
    intro x
    dsimp [toAnn, fromAnn]
    rw [hq, happly ψ x]
  have hbij : Function.Bijective toAnn :=
    ⟨fun χ φ h => (hinv_left χ).symm.trans ((congrArg fromAnn h).trans (hinv_left φ)),
      fun ψ => ⟨fromAnn ψ, hinv_right ψ⟩⟩
  have hto_cont : Continuous toAnn := by
    rw [IsInducing.subtypeVal.continuous_iff (f := toAnn)]
    exact (PontryaginDual.map q).continuous
  have hfrom_cont : Continuous fromAnn := by
    refine continuous_of_continuousAt_one fromAnn ?_
    rw [ContinuousAt, map_one fromAnn]
    refine (pontryaginDual_nhds_one_hasBasis (G := G ⧸ H)).tendsto_right_iff.mpr ?_
    rintro ⟨K, V⟩ ⟨hK, hV⟩
    obtain ⟨C, hC, hKC⟩ := exists_isCompact_quotient_preimage H hK
    rw [IsInducing.subtypeVal.nhds_eq_comap (1 : lcaAnnihilator H)]
    refine mem_comap.mpr ⟨{ψ : PontryaginDual G | MapsTo ψ C V},
      pontryaginDual_nhds_one_hasBasis.mem_of_mem (i := (C, V)) ⟨hC, hV⟩, ?_⟩
    intro ψ hψ
    replace hψ : MapsTo (ψ.val : G → Circle) C V := by
      simpa [Set.mem_ofPred] using hψ
    show MapsTo (fromAnn ψ) K V
    intro k hk
    obtain ⟨x, hxC, rfl⟩ := hKC hk
    dsimp [fromAnn]
    rw [happly ψ x]
    exact hψ hxC
  let e : PontryaginDual (G ⧸ H) ≃ₜ* lcaAnnihilator H :=
    { toFun := toAnn
      invFun := fromAnn
      left_inv := hinv_left
      right_inv := hinv_right
      map_mul' := toAnn.map_mul
      continuous_toFun := hto_cont
      continuous_invFun := hfrom_cont }
  refine ⟨e, fun χ x => ?_⟩
  dsimp [e, toAnn]
  rw [hq]

open scoped Pointwise in
/-- Some compact subgroup has a σ-compact annihilator. The subgroup is the
intersection of a decreasing sequence of compact identity neighborhoods. -/
private theorem exists_compact_subgroup_sigmaCompact_annihilator :
    ∃ K : Subgroup G, IsCompact (K : Set G) ∧ SigmaCompactSpace (lcaAnnihilator K) := by
  let N := {U : Set G // U ∈ 𝓝 (1 : G) ∧ IsCompact U}
  have hNext (U : N) : ∃ V : N, (V : Set G)⁻¹ = V.val ∧ V.val * V.val ⊆ U.val := by
    obtain ⟨V, hV, hVc, hVi, hVV⟩ := exists_closed_nhds_one_inv_eq_mul_subset U.property.1
    have hVU : V ⊆ U.val := fun x hx ↦ hVV (mul_one x ▸ Set.mul_mem_mul hx (mem_of_mem_nhds hV))
    exact ⟨⟨V, hV, U.property.2.of_isClosed_subset hVc hVU⟩, hVi, hVV⟩
  choose next hInv hMul using hNext
  obtain ⟨U₀, hU₀, hU₀nhds⟩ := exists_compact_mem_nhds (1 : G)
  let seq : ℕ → N := Nat.rec ⟨U₀, hU₀nhds, hU₀⟩ fun _ U ↦ next U
  let U (n : ℕ) : Set G := (seq n).val
  have hOne (n : ℕ) : (1 : G) ∈ U n := mem_of_mem_nhds (seq n).property.1
  have hMulU (n : ℕ) : U (n + 1) * U (n + 1) ⊆ U n := hMul (seq n)
  have hAnti : Antitone U := antitone_nat_of_succ_le fun n x hx ↦
    hMulU n (mul_one x ▸ Set.mul_mem_mul hx (hOne (n + 1)))
  let K : Subgroup G :=
    { carrier := ⋂ n, U n
      one_mem' := mem_iInter.mpr hOne
      mul_mem' := fun hx hy ↦ mem_iInter.mpr fun n ↦ hMulU n
        (Set.mul_mem_mul (mem_iInter.mp hx (n + 1)) (mem_iInter.mp hy (n + 1)))
      inv_mem' := fun hx ↦ mem_iInter.mpr fun n ↦ hAnti (Nat.le_succ n) (by
          change _ ∈ (next (seq n)).val
          rw [← hInv (seq n)]
          simpa only [Set.mem_inv, inv_inv] using mem_iInter.mp hx (n + 1)) }
  have hUc (n) : IsCompact (U n) := (seq n).property.2
  have hUK : IsClosed (K : Set G) := isClosed_iInter fun n ↦ (hUc n).isClosed
  have hK : IsCompact (K : Set G) := (hUc 0).of_isClosed_subset hUK (iInter_subset U 0)
  refine ⟨K, hK, ?_⟩
  obtain ⟨r, hr, hPolar⟩ := exists_isCompact_pontryaginDual_polar (G := G)
  let A := lcaAnnihilator K
  have hA : IsClosed (A : Set (PontryaginDual G)) :=
    isClosed_singleton.preimage
      (PontryaginDual.map (⟨K.subtype, continuous_subtype_val⟩ : K →ₜ* G)).continuous
  let P (n : ℕ) : Set A := Subtype.val ⁻¹' {χ | MapsTo χ (U n) (Metric.closedBall 1 r)}
  refine ⟨⟨P, fun n ↦ (?_ : IsCompact (P n)), eq_univ_of_forall fun χ ↦ ?_⟩⟩
  · exact hA.isClosedEmbedding_subtypeVal.isCompact_preimage (hPolar _ (seq n).property.1)
  · let W := (χ.val : PontryaginDual G) ⁻¹' Metric.ball 1 r
    have hW : IsOpen W := Metric.isOpen_ball.preimage χ.val.continuous
    have hKW : (K : Set G) ⊆ W := fun x hx ↦
      show χ.val x ∈ Metric.ball 1 r by
        rw [(mem_lcaAnnihilator_iff K χ.val).mp χ.property ⟨x, hx⟩]
        exact Metric.mem_ball_self hr
    have hDisj : Disjoint (U 0 \ W) (⋂ n, U n) :=
      Set.disjoint_left.mpr fun x hx hxn ↦ hx.2 (hKW hxn)
    obtain ⟨n, hn⟩ := ((hUc 0).diff hW).elim_directed_family_closed U
      (fun n ↦ (hUc n).isClosed) hDisj hAnti.directed_ge
    refine mem_iUnion.mpr ⟨n, fun x hx ↦ Metric.ball_subset_closedBall ?_⟩
    by_contra hxW
    exact Set.disjoint_left.mp hn ⟨hAnti (Nat.zero_le n) hx, hxW⟩ hx

/-- Restriction to a closed subgroup is an open map on the dual groups. -/
private theorem isOpenMap_restrict_dual (H : Subgroup G) (hH : IsClosed (H : Set G)) :
    IsOpenMap (PontryaginDual.map (⟨H.subtype, continuous_subtype_val⟩ : H →ₜ* G)) := by
  let f := PontryaginDual.map (⟨H.subtype, continuous_subtype_val⟩ : H →ₜ* G)
  let : LocallyCompactSpace H := hH.locallyCompactSpace
  obtain ⟨K, hK, hSigma⟩ := exists_compact_subgroup_sigmaCompact_annihilator (G := G)
  -- The restriction between the two open annihilators is surjective.
  let L := K.comap H.subtype
  have hL : IsCompact (L : Set H) := hH.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  let A := lcaAnnihilator K
  let B := lcaAnnihilator L
  let : SigmaCompactSpace A := hSigma
  let : CompactSpace L := isCompact_iff_compactSpace.mp hL
  have hB : IsOpen (B : Set (PontryaginDual H)) :=
    (isOpen_discrete ({1} : Set (PontryaginDual L))).preimage
      (PontryaginDual.map (⟨L.subtype, continuous_subtype_val⟩ : L →ₜ* H)).continuous
  let : LocallyCompactSpace B := hB.isOpenEmbedding_subtypeVal.locallyCompactSpace
  let g : A →* B := (f.toMonoidHom.comp A.subtype).codRestrict B fun χ ↦
    (mem_lcaAnnihilator_iff L _).mpr fun x ↦
      (mem_lcaAnnihilator_iff K χ.val).mp χ.property ⟨(x.val : G), x.property⟩
  have hg : Continuous g := (f.continuous.comp continuous_subtype_val).subtype_mk _
  have hgSurj : Function.Surjective g := by
    intro χ
    obtain ⟨ψ, hψ, hψK⟩ := exists_pontryaginDual_extension_trivial_on_compact H K hH hK χ.val
      (fun x hx ↦ (mem_lcaAnnihilator_iff L χ.val).mp χ.property ⟨x, hx⟩)
    exact ⟨⟨ψ, (mem_lcaAnnihilator_iff K ψ).mpr hψK⟩, Subtype.ext (PontryaginDual.ext hψ)⟩
  have hOpen := g.isOpenMap_of_sigmaCompact hgSurj hg
  have hImg (U : Set (PontryaginDual G)) (hU : U ∈ 𝓝 1) : f '' U ∈ 𝓝 1 := by
    have hU' : (Subtype.val : A → PontryaginDual G) ⁻¹' U ∈ 𝓝 (1 : A) :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds hU
    have hV := hOpen.image_mem_nhds hU'
    rw [map_one g] at hV
    apply mem_of_superset (hB.isOpenEmbedding_subtypeVal.isOpenMap.image_mem_nhds hV)
    rintro _ ⟨_, ⟨χ, hχ, rfl⟩, rfl⟩
    exact ⟨χ.val, hχ, rfl⟩
  exact IsTopologicalGroup.isOpenMap_iff_nhds_one.mpr fun U hU ↦
    mem_of_superset (hImg (f ⁻¹' U) hU) (image_preimage_subset f U)

/-- Paper: Lemma D.1.4.6(2), p. 758. Restriction of characters identifies the
dual modulo the annihilator with the dual of the subgroup. -/
theorem lcaDualQuotient_equiv_subgroupDual (H : Subgroup G) (hH : IsClosed (H : Set G)) :
    ∃ e : (PontryaginDual G ⧸ lcaAnnihilator H) ≃ₜ* PontryaginDual H,
      ∀ (χ : PontryaginDual G) (x : H), e (QuotientGroup.mk χ) x = χ x.val := by
  let f := PontryaginDual.map (⟨H.subtype, continuous_subtype_val⟩ : H →ₜ* G)
  have hSurj : Function.Surjective f := by
    intro χ
    obtain ⟨ψ, hψ, _⟩ := exists_pontryaginDual_extension_trivial_on_compact H ⊥ hH
      (by simp) χ (fun x hx ↦ by
        have hx1 : x = 1 := Subtype.ext (Subgroup.mem_bot.mp hx)
        rw [hx1, map_one])
    exact ⟨ψ, PontryaginDual.ext hψ⟩
  have hOpen := isOpenMap_restrict_dual H hH
  let e := QuotientGroup.quotientKerEquivOfSurjective f.toMonoidHom hSurj
  have hq := QuotientGroup.isQuotientMap_mk (lcaAnnihilator H)
  have hf := hOpen.isQuotientMap f.continuous hSurj
  refine ⟨e.toContinuousMulEquiv fun _ ↦ ?_, fun _ _ ↦ rfl⟩
  exact (hq.isCoinducing.isOpen_preimage.symm.trans hf.isCoinducing.isOpen_preimage)

-- Retain the LCA assumptions in the existing signature.
set_option linter.unusedSectionVars false in
/-- Paper: Lemma D.1.4.6(3), p. 758. The annihilator of a compact subgroup is open. -/
theorem isOpen_lcaAnnihilator (H : Subgroup G) (hH : IsCompact (H : Set G)) :
    IsOpen (lcaAnnihilator H : Set (PontryaginDual G)) := by
  let : CompactSpace H := isCompact_iff_compactSpace.mp hH
  let restrict := PontryaginDual.map (⟨H.subtype, continuous_subtype_val⟩ : H →ₜ* G)
  change IsOpen (restrict ⁻¹' ({1} : Set (PontryaginDual H)))
  exact (isOpen_discrete _).preimage restrict.continuous

/-- Paper: Lemma D.1.4.6(4), p. 758. The annihilator of an open subgroup is compact. -/
theorem isCompact_lcaAnnihilator (H : Subgroup G) (hH : IsOpen (H : Set G)) :
    IsCompact (lcaAnnihilator H : Set (PontryaginDual G)) := by
  let : DiscreteTopology (G ⧸ H) := QuotientGroup.discreteTopology hH
  obtain ⟨e, _⟩ := lcaQuotientDual_equiv_annihilator H (H.isClosed_of_isOpen hH)
  exact isCompact_iff_compactSpace.mpr e.toHomeomorph.compactSpace

/-- Paper: (D.1.4.9), p. 759. Evaluation at points of the original group is dense
in the dual of each open compactly generated subgroup of its Pontryagin dual.
Deviation: This isolates the density consequence of biduality and character extension. -/
theorem lca_dualSubgroup_eval_denseRange
    (H : OpenCompactlyGeneratedSubgroups (PontryaginDual G)) :
    DenseRange ((PontryaginDual.map
      (⟨H.val.subtype, continuous_subtype_val⟩ : H.val →ₜ* PontryaginDual G)).comp
        (pontryaginDual_eval (G := G))) := by
  refine Function.Surjective.denseRange ?_
  obtain ⟨restrict, hRestrict⟩ :=
    lcaDualQuotient_equiv_subgroupDual H.val (H.val.isClosed_of_isOpen H.property.1)
  obtain ⟨eval, hEval⟩ := pontryaginDual_bidual (G := G)
  intro ψ
  obtain ⟨q, rfl⟩ := restrict.surjective ψ
  obtain ⟨η, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨x, rfl⟩ := eval.surjective η
  refine ⟨x, PontryaginDual.ext fun χ ↦ ?_⟩
  change χ.val x = restrict (QuotientGroup.mk (eval x)) χ
  rw [hRestrict, hEval]

/-- Paper: (D.1.4.9)–(D.1.4.10), p. 759. The evaluation map onto the dual of
an open compactly generated subgroup of the dual is an open quotient. Its
kernel is the compact annihilator of the subgroup. -/
theorem lca_dualSubgroup_quotient (H : OpenCompactlyGeneratedSubgroups (PontryaginDual G)) :
    ∃ γ : G →ₜ* PontryaginDual H.val,
      (∀ x (χ : H.val), γ x χ = χ.val x) ∧ IsOpenQuotientMap γ ∧
        γ.toMonoidHom.ker = lcaDualAnnihilator H.val ∧ IsCompact (γ.toMonoidHom.ker : Set G) := by
  let r := PontryaginDual.map (⟨H.val.subtype, continuous_subtype_val⟩ : H.val →ₜ* PontryaginDual G)
  let γ := r.comp (pontryaginDual_eval (G := G))
  have hEval (x : G) (χ : H.val) : γ x χ = χ.val x := rfl
  have hH := H.val.isClosed_of_isOpen H.property.1
  -- The kernel of restriction is dual to the discrete quotient by the open subgroup.
  let : DiscreteTopology (PontryaginDual G ⧸ H.val) := QuotientGroup.discreteTopology H.property.1
  obtain ⟨a, _⟩ := lcaQuotientDual_equiv_annihilator H.val hH
  have hCompact : IsCompact (lcaAnnihilator H.val : Set (PontryaginDual (PontryaginDual G))) :=
    isCompact_iff_compactSpace.mpr a.toHomeomorph.compactSpace
  obtain ⟨e, he⟩ := lcaDualQuotient_equiv_subgroupDual H.val hH
  have hr : (r : PontryaginDual (PontryaginDual G) → PontryaginDual H.val) =
      e ∘ QuotientGroup.mk := funext fun χ ↦ PontryaginDual.ext fun ψ ↦ (he χ ψ).symm
  have hClosedR : IsClosedMap r := hr ▸
    e.toHomeomorph.isClosedMap.comp (QuotientGroup.isClosedMap_coe hCompact)
  have hEmb := isClosedEmbedding_pontryaginDual_eval (G := G)
  have hClosed : IsClosedMap γ := hClosedR.comp hEmb.isClosedMap
  have hRange : IsClosed (range γ) := by
    rw [← image_univ]
    exact hClosed _ isClosed_univ
  have hSurj : Function.Surjective γ := by
    intro ψ
    change ψ ∈ range γ
    rw [← hRange.closure_eq]
    exact lca_dualSubgroup_eval_denseRange H ψ
  have hQ := hClosed.isQuotientMap γ.continuous hSurj
  let iso := (QuotientGroup.quotientKerEquivOfSurjective γ.toMonoidHom hSurj).toContinuousMulEquiv
    fun _ ↦ (QuotientGroup.isQuotientMap_mk γ.toMonoidHom.ker).isCoinducing.isOpen_preimage.symm.trans
      hQ.isCoinducing.isOpen_preimage
  refine ⟨γ, hEval, iso.toHomeomorph.isOpenQuotientMap.comp QuotientGroup.isOpenQuotientMap_mk,
    ?_, hEmb.isCompact_preimage hCompact⟩
  ext x
  rw [MonoidHom.mem_ker, mem_lcaDualAnnihilator_iff]
  exact ⟨fun h χ ↦ congrArg (fun ψ : PontryaginDual H.val ↦ ψ χ) h,
    fun h ↦ PontryaginDual.ext (fun χ ↦ h χ)⟩

-- TODO(paper-gap): p. 759 calls the quotient codomains Uᵢ small subgroups of G.
-- The kernels Kᵢ are the subgroups that become small, as on p. 760.

/-- Paper: After (D.1.4.10), p. 759. Every identity neighborhood contains
one of the compact annihilators.
Deviation: The small subgroups are the kernels Kᵢ, as stated on p. 760. -/
theorem exists_lcaDualAnnihilator_subset_nhds {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ H : OpenCompactlyGeneratedSubgroups (PontryaginDual G),
      (lcaDualAnnihilator H.val : Set G) ⊆ U := by
  obtain ⟨K, hK, hTest⟩ := exists_pontryaginDual_compact_test hU
  obtain ⟨H, hKH⟩ := exists_openCompactlyGeneratedSubgroup_contains hK
  refine ⟨H, fun x hx ↦ hTest x ?_⟩
  intro χ hχ
  have hχx := (mem_lcaDualAnnihilator_iff H.val x).mp hx ⟨χ, hKH hχ⟩
  change χ x = 1 at hχx
  rw [hχx, dist_self]
  norm_num

-- TODO(paper-gap): The component group of Aᵢⱼ can be infinite, as for G = ℤ with
-- Gⱼ = ℤ and Kᵢ = 1. Its component group is finitely generated by (D.1.4.12).

/-- Paper: (D.1.4.12), p. 759. A quotient in the inverse system of an open
compactly generated subgroup has an elementary presentation. -/
theorem lca_openSubgroup_quotient_elementary (J : OpenCompactlyGeneratedSubgroups G)
    (H : OpenCompactlyGeneratedSubgroups (PontryaginDual G))
    (_h : lcaDualAnnihilator H.val ≤ J.val) :
    Nonempty (ElementaryLCAPresentation (J.val ⧸ (lcaDualAnnihilator H.val).comap J.val.subtype)) := by
  let N := (lcaDualAnnihilator H.val).comap J.val.subtype
  let : LocallyCompactSpace J.val :=
    J.property.1.isOpenEmbedding_subtypeVal.locallyCompactSpace
  let : LocallyCompactSpace H.val :=
    H.property.1.isOpenEmbedding_subtypeVal.locallyCompactSpace
  let ι : H.val →ₜ* PontryaginDual G :=
    ⟨H.val.subtype, continuous_subtype_val⟩
  let f : J.val →ₜ* PontryaginDual H.val :=
    (PontryaginDual.map ι).comp
      (pontryaginDual_eval.comp
        ⟨J.val.subtype, continuous_subtype_val⟩)
  have hker : f.toMonoidHom.ker = N := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_comap, Subgroup.coe_subtype,
      mem_lcaDualAnnihilator_iff]
    exact
      ⟨fun hx χ ↦ congrArg (fun ψ : PontryaginDual H.val ↦ ψ χ) hx,
        fun hx ↦ PontryaginDual.ext hx⟩
  have hN : IsClosed (N : Set J.val) := by
    rw [← hker]
    exact isClosed_eq f.continuous continuous_const
  let : T1Space (J.val ⧸ N) :=
    QuotientGroup.t1Space_iff.mpr hN
  refine lca_elementary_iff.mp
    ⟨isCompactlyGeneratedGroup_quotient J.property.2 N hN, ?_⟩
  let e : (J.val ⧸ N) →ₜ* PontryaginDual H.val :=
    ⟨QuotientGroup.lift N f.toMonoidHom hker.ge,
      (QuotientGroup.isQuotientMap_mk N).continuous_iff.mpr
        f.continuous⟩
  have he : Function.Injective e :=
    (QuotientGroup.injective_lift_iff N f.toMonoidHom hker.ge).mpr
      hker.symm
  obtain ⟨W, hW, hPow⟩ := exists_nhds_one_of_isLocallyEuclidean
    (isCompactlyGeneratedGroup_iff_dual_locallyEuclidean.mp
      H.property.2)
  have hW' : W ∈ 𝓝 (e 1) := by
    rwa [map_one]
  refine isLocallyEuclidean_of_noSmallCyclicSubgroups
    (e.continuous.continuousAt.preimage_mem_nhds hW') ?_
  intro x hx
  apply he
  rw [map_one]
  exact hPow (e x) fun n ↦ map_pow e x n ▸ hx n

/-- Paper: Lemma D.1.4.7, p. 760. Each open compactly generated subgroup is the
inverse limit of its quotients by the annihilators it contains.
Deviation: We express the compatible families as the range in the product. At comparable
indices the coordinates are compatible exactly when they have a common representative.
Together with the open exhaustion (D.1.4.3), this realizes (D.1.4.16). -/
theorem lca_openSubgroup_inverseLimit (J : OpenCompactlyGeneratedSubgroups G) :
    let I := {H : OpenCompactlyGeneratedSubgroups (PontryaginDual G) //
      lcaDualAnnihilator H.val ≤ J.val}
    let K : I → Subgroup J.val := fun H ↦ (lcaDualAnnihilator H.val.val).comap J.val.subtype
    let δ : J.val → ((H : I) → J.val ⧸ K H) := fun x _ ↦ QuotientGroup.mk x
    Nonempty I ∧ IsDirectedOrder I ∧
      IsEmbedding δ ∧ range δ = {a | ∀ (H H' : I), H ≤ H' →
      ∃ x : J.val, δ x H = a H ∧ δ x H' = a H'} := by
  let I := {H : OpenCompactlyGeneratedSubgroups (PontryaginDual G) //
    lcaDualAnnihilator H.val ≤ J.val}
  let K (H : I) : Subgroup J.val := (lcaDualAnnihilator H.val.val).comap J.val.subtype
  let δ : J.val →ₜ* ((H : I) → J.val ⧸ K H) :=
    { toFun := fun x H ↦ QuotientGroup.mk x
      map_one' := funext fun H ↦ QuotientGroup.mk_one (N := K H)
      map_mul' := fun x y ↦ funext fun H ↦ QuotientGroup.mk_mul (K H) x y
      continuous_toFun := continuous_pi fun H ↦ QuotientGroup.continuous_mk }
  change Nonempty I ∧ IsDirectedOrder I ∧ IsEmbedding δ ∧
    range δ = {a | ∀ (H H' : I), H ≤ H' → ∃ x : J.val, δ x H = a H ∧ δ x H' = a H'}
  have hSmall {V : Set J.val} (hV : V ∈ 𝓝 (1 : J.val)) :
      ∃ H : I, (K H : Set J.val) ⊆ V := by
    obtain ⟨H, hH⟩ := exists_lcaDualAnnihilator_subset_nhds
      (J.property.1.isOpenEmbedding_subtypeVal.isOpenMap.image_mem_nhds hV)
    refine ⟨⟨H, fun x hx ↦ ?_⟩, ?_⟩
    · obtain ⟨y, _, rfl⟩ := hH hx
      exact y.property
    · intro x hx
      obtain ⟨y, hy, hyx⟩ := hH (Subgroup.mem_comap.mp hx)
      exact (Subtype.ext hyx : y = x) ▸ hy
  let : Nonempty I := ⟨(hSmall Filter.univ_mem).choose⟩
  let : IsDirectedOrder (OpenCompactlyGeneratedSubgroups (PontryaginDual G)) :=
    (openCompactlyGeneratedSubgroups_colimit (G := PontryaginDual G)).1
  have hAnti : Antitone (fun H : OpenCompactlyGeneratedSubgroups (PontryaginDual G) ↦
      lcaDualAnnihilator H.val) := by
    intro H H' h x hx
    exact (mem_lcaDualAnnihilator_iff H.val x).mpr fun χ ↦
      (mem_lcaDualAnnihilator_iff H'.val x).mp hx (Subgroup.inclusion h χ)
  let : IsDirectedOrder I := ⟨fun H H' ↦ by
    obtain ⟨L, hHL, hH'L⟩ := exists_ge_ge H.val H'.val
    exact ⟨⟨L, (hAnti hHL).trans H.property⟩, hHL, hH'L⟩⟩
  -- A neighborhood can be tested in a quotient whose kernel lies in a smaller neighborhood.
  have hInducing : IsInducing δ := by
    rw [IsTopologicalGroup.isInducing_iff_nhds_one]
    refine le_antisymm ?_ ?_
    · have h : Tendsto δ (𝓝 1) (𝓝 (δ 1)) := δ.continuous.tendsto 1
      rw [map_one] at h
      exact h.le_comap
    · intro U hU
      obtain ⟨V, hV, h1V, hVV⟩ := exists_open_nhds_one_mul_subset hU
      obtain ⟨H, hH⟩ := hSmall (hV.mem_nhds h1V)
      let q : J.val → J.val ⧸ K H := QuotientGroup.mk
      have hqV : q '' V ∈ 𝓝 (1 : J.val ⧸ K H) :=
        (QuotientGroup.isOpenMap_coe (N := K H)).image_mem_nhds (hV.mem_nhds h1V)
      refine Filter.mem_comap.mpr ⟨(fun a ↦ a H) ⁻¹' (q '' V),
        (continuous_apply H).continuousAt.preimage_mem_nhds hqV, ?_⟩
      intro x hx
      obtain ⟨y, hy, hyx⟩ : q x ∈ q '' V := hx
      have hDiff : y⁻¹ * x ∈ K H := QuotientGroup.eq.mp hyx
      exact hVV ⟨y, hy, y⁻¹ * x, hH hDiff, mul_inv_cancel_left y x⟩
  refine ⟨inferInstance, inferInstance, ⟨hInducing, hInducing.injective⟩, ?_⟩
  ext a
  constructor
  · rintro ⟨x, rfl⟩ H H' _
    exact ⟨x, rfl, rfl⟩
  · intro ha
    change ∀ (H H' : I), H ≤ H' → ∃ x : J.val, δ x H = a H ∧ δ x H' = a H' at ha
    let F (H : I) : Set J.val := {x | δ x H = a H}
    have hNonempty (H : I) : (F H).Nonempty := by
      obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (a H)
      exact ⟨x, hx⟩
    have hCompact (H : I) : IsCompact (K H : Set J.val) := by
      have hEval := (isClosedEmbedding_pontryaginDual_eval (G := G)).comp
        (J.val.isClosed_of_isOpen J.property.1).isClosedEmbedding_subtypeVal
      have hPreimage : (K H : Set J.val) =
          (pontryaginDual_eval ∘ (Subtype.val : J.val → G)) ⁻¹'
            (lcaAnnihilator H.val.val : Set (PontryaginDual (PontryaginDual G))) := by
        ext x
        exact (mem_lcaDualAnnihilator_iff H.val.val x.val).trans
          (mem_lcaAnnihilator_iff H.val.val (pontryaginDual_eval x.val)).symm
      rw [hPreimage]
      exact hEval.isCompact_preimage (isCompact_lcaAnnihilator H.val.val H.val.property.1)
    -- The fibers are translates of compact kernels and decrease along the index order.
    have hFiberCompact (H : I) : IsCompact (F H) := by
      obtain ⟨y, hy⟩ := hNonempty H
      have hFiber : F H = (fun z : J.val ↦ y * z) '' (K H : Set J.val) := by
        ext x
        constructor
        · intro hx
          exact ⟨y⁻¹ * x, QuotientGroup.eq.mp (hy.trans hx.symm), mul_inv_cancel_left y x⟩
        · rintro ⟨z, hz, rfl⟩
          change (QuotientGroup.mk (y * z) : J.val ⧸ K H) = a H
          rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff z).mpr hz, mul_one]
          exact hy
      rw [hFiber]
      exact (hCompact H).image (continuous_const.mul continuous_id)
    have hFiberAnti : Antitone F := by
      intro H H' h x hx
      obtain ⟨y, hy, hy'⟩ := ha H H' h
      have hDiff : x⁻¹ * y ∈ K H' := QuotientGroup.eq.mp (hx.trans hy'.symm)
      have hK : K H' ≤ K H := Subgroup.comap_mono (hAnti (show H.val ≤ H'.val from h))
      exact (QuotientGroup.eq.mpr (hK hDiff)).trans hy
    obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      F (directed_of_isDirected_le hFiberAnti) hNonempty hFiberCompact
      (fun H ↦ (hFiberCompact H).isClosed)
    exact ⟨x, funext (mem_iInter.mp hx)⟩

end Structure

section StructuralPairs

variable {G : Type*} [CommGroup G] [TopologicalSpace G]

/-- Paper: Definition D.1.5.1(1), p. 760. A good subgroup is closed and has an
open compactly generated annihilator in the dual. -/
def IsBruhatGoodSubgroup (k : Subgroup G) : Prop :=
  IsClosed (k : Set G) ∧ IsOpen (lcaAnnihilator k : Set (PontryaginDual G)) ∧
    IsCompactlyGeneratedGroup (lcaAnnihilator k)

/-- Paper: Definition D.1.5.1(2), p. 760. A structural pair consists of an open
compactly generated subgroup and a good subgroup contained in it.
The order enlarges the first subgroup and shrinks the second. -/
abbrev BruhatStructuralPair (G : Type*) [CommGroup G] [TopologicalSpace G] :=
  {p : Subgroup G × (Subgroup G)ᵒᵈ //
    IsOpen (p.1 : Set G) ∧ IsCompactlyGeneratedGroup p.1 ∧
      IsBruhatGoodSubgroup (OrderDual.ofDual p.2) ∧ OrderDual.ofDual p.2 ≤ p.1}

/-- Paper: (D.1.5.2), p. 761. The quotient associated to a pair divides the
open subgroup by the good subgroup inside it. -/
abbrev BruhatStructuralPair.quotient (p : BruhatStructuralPair G) :=
  p.val.1 ⧸ (OrderDual.ofDual p.val.2).comap p.val.1.subtype

/-- Paper: (D.1.5.2), p. 761. The quotient sends a point to the identity if and
only if it belongs to the good subgroup. -/
theorem BruhatStructuralPair.quotient_mk_eq_one (p : BruhatStructuralPair G) (x : p.val.1) :
    (QuotientGroup.mk x : p.quotient) = 1 ↔ (x : G) ∈ OrderDual.ofDual p.val.2 := by
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_comap, Subgroup.coe_subtype]

variable [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]


/-- The dual of a locally Euclidean LCA group is compactly generated: the characters
from a torus homomorphism with discrete kernel, together with a compact polar
neighborhood, generate it. -/
theorem isCompactlyGeneratedGroup_dual_of_isLocallyEuclidean (hG : IsLocallyEuclidean G) :
    IsCompactlyGeneratedGroup (PontryaginDual G) := by
  classical
  obtain ⟨W, hW, hPow⟩ := exists_nhds_one_of_isLocallyEuclidean hG
  obtain ⟨t, f, hft, hker⟩ := exists_torusHom_of_noSmallCyclicSubgroups hW hPow
  obtain ⟨L, ρ, σ, hρ, hρ1, hfσ, hσc, hσmul, hσnhds⟩ :=
    exists_localSection_of_discrete_torusKernel f hker
  obtain ⟨r, hr, hpolar⟩ := exists_isCompact_pontryaginDual_polar (G := G)
  set n : ℕ := Fintype.card t with hn
  set ρ₀ := min (ρ / 4) (r / (n + 1)) with hρ₀def
  have hρ₀ : 0 < ρ₀ := lt_min (by positivity) (by positivity)
  have hρ₀ρ : ρ₀ < ρ / 2 := (min_le_left _ _).trans_lt (by linarith)
  have hnρ₀ : (n : ℝ) * ρ₀ ≤ r := by
    have h1 : ρ₀ ≤ r / (n + 1) := min_le_right _ _
    have h2 : (n : ℝ) * (r / (n + 1)) ≤ r := by
      rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
      nlinarith
    calc (n : ℝ) * ρ₀ ≤ n * (r / (n + 1)) := by gcongr
      _ ≤ r := h2
  set K := σ '' Metric.closedBall (0 : L) ρ₀ with hKdef
  have hKc : IsCompact K :=
    (isCompact_closedBall 0 ρ₀).image_of_continuousOn
      (hσc.mono (Metric.closedBall_subset_ball (hρ₀ρ.trans (half_lt_self hρ))))
  have hK : K ∈ 𝓝 (1 : G) :=
    mem_of_superset (hσnhds ρ₀ hρ₀) (image_mono Metric.ball_subset_closedBall)
  set P := {χ : PontryaginDual G | MapsTo χ K (Metric.closedBall 1 r)} with hPdef
  have hPc : IsCompact P := hpolar K hK
  have hP : P ∈ 𝓝 (1 : PontryaginDual G) := by
    have h1 := pontryaginDual_nhds_one_hasBasis.mem_of_mem
      (i := (K, Metric.ball (1 : Circle) r)) ⟨hKc, Metric.ball_mem_nhds 1 hr⟩
    exact mem_of_superset h1 fun χ hχ ↦ hχ.mono_right Metric.ball_subset_closedBall
  refine ⟨P ∪ (t : Set (PontryaginDual G)), mem_of_superset hP subset_union_left,
    hPc.union t.finite_toSet.isCompact, ?_⟩
  rw [eq_top_iff]
  intro ψ _
  have hψc : ContinuousAt (fun v : L ↦ ψ (σ v)) 0 :=
    ψ.continuous.continuousAt.comp (hσc.continuousAt (Metric.ball_mem_nhds 0 hρ))
  have hψadd : ∀ v w : L, ‖v‖ < ρ / 2 → ‖w‖ < ρ / 2 →
      ψ (σ (v + w)) = ψ (σ v) * ψ (σ w) := by
    intro v w hv hw
    rw [hσmul v w (by linarith) (by linarith) ((norm_add_le v w).trans_lt (by linarith)),
      map_mul]
  obtain ⟨l, hl⟩ := exists_linearMap_circleExp_of_localHom (half_pos hρ) _ hψc hψadd
  obtain ⟨m, hm⟩ := LinearMap.exists_extend l
  let a : t → ℝ := fun i ↦ m (EuclideanSpace.basisFun t ℝ i)
  let k : t → ℤ := fun i ↦ ⌊a i⌋
  set ψ' := ψ * ∏ i : t, (i.val) ^ (-k i) with hψ'def
  have hψ'P : ψ' ∈ P := by
    rintro _ ⟨v, hv, rfl⟩
    have hv' : ‖v‖ ≤ ρ₀ := mem_closedBall_zero_iff.mp hv
    have hvρ : ‖v‖ < ρ / 2 := hv'.trans_lt hρ₀ρ
    let ev : PontryaginDual G →* Circle :=
      { toFun := fun χ ↦ χ (σ v), map_one' := rfl, map_mul' := fun _ _ ↦ rfl }
    have hmv : m (v : EuclideanSpace ℝ t) = ∑ i : t, (v : EuclideanSpace ℝ t) i * a i := by
      conv_lhs => rw [← (EuclideanSpace.basisFun t ℝ).sum_repr (v : EuclideanSpace ℝ t)]
      simp [map_sum, map_smul, a]
    have hlv : l v = m (v : EuclideanSpace ℝ t) := (LinearMap.congr_fun hm v).symm
    have hev : ψ' (σ v) = Circle.exp (∑ i : t, (a i - k i) * (v : EuclideanSpace ℝ t) i) := by
      change ev ψ' = _
      rw [hψ'def, map_mul, map_prod]
      change ψ (σ v) * ∏ i : t, ev (i.val ^ (-k i)) = _
      simp only [map_zpow]
      change ψ (σ v) * ∏ i : t, (i.val (σ v)) ^ (-k i) = _
      have hcoord : ∀ i : t, i.val (σ v) = Circle.exp ((v : EuclideanSpace ℝ t) i) := by
        intro i
        rw [← hft, hfσ v (hvρ.trans (half_lt_self hρ)) i]
      simp only [hcoord, ← Circle.exp_intCast_mul]
      rw [hl v hvρ, hlv, hmv, ← circleExp_sum, ← Circle.exp_add, ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      push_cast
      ring
    rw [hev, Metric.mem_closedBall]
    refine (dist_circleExp_one_le _).trans ?_
    calc |∑ i : t, (a i - k i) * (v : EuclideanSpace ℝ t) i|
        ≤ ∑ i : t, |(a i - k i) * (v : EuclideanSpace ℝ t) i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : t, ‖v‖ := by
          refine Finset.sum_le_sum fun i _ ↦ ?_
          rw [abs_mul]
          have h0 : 0 ≤ a i - k i := by
            have := Int.fract_nonneg (a i); rwa [Int.fract] at this
          have h1 : a i - k i < 1 := by
            have := Int.fract_lt_one (a i); rwa [Int.fract] at this
          have hvi : |(v : EuclideanSpace ℝ t) i| ≤ ‖v‖ := by
            simpa using PiLp.norm_apply_le (v : EuclideanSpace ℝ t) i
          rw [abs_of_nonneg h0]
          nlinarith [abs_nonneg ((v : EuclideanSpace ℝ t) i)]
      _ = n * ‖v‖ := by simp [hn]
      _ ≤ n * ρ₀ := by gcongr
      _ ≤ r := hnρ₀
  have hψ : ψ = ψ' * ∏ i : t, (i.val) ^ (k i) := by
    rw [hψ'def, mul_assoc, ← Finset.prod_mul_distrib]
    simp
  rw [hψ]
  exact Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inl hψ'P))
    (Subgroup.prod_mem _ fun i _ ↦ Subgroup.zpow_mem _ (Subgroup.subset_closure (Or.inr i.2)) _)

/-- If the dual is compactly generated, the group has a neighborhood of the identity
containing no nontrivial cyclic subgroup, hence it is locally Euclidean. -/
theorem isLocallyEuclidean_of_isCompactlyGeneratedGroup_dual
    (h : IsCompactlyGeneratedGroup (PontryaginDual G)) : IsLocallyEuclidean G := by
  obtain ⟨K, -, hK, hGen⟩ := h
  have hC : Circle.centeredArc (Real.pi / 2) ∈ 𝓝 (1 : Circle) := by
    simpa using Circle.hasBasis_centeredArc_div_two_pow.mem_of_mem (i := 0) trivial
  let W : Set G := (pontryaginDual_eval (G := G)) ⁻¹'
    {ψ | MapsTo ψ K (Circle.centeredArc (Real.pi / 2))}
  have hW : W ∈ 𝓝 (1 : G) := by
    have h1 := (pontryaginDual_nhds_one_hasBasis (G := PontryaginDual G)).mem_of_mem
      (i := (K, _)) ⟨hK, hC⟩
    have ht := (map_continuous (pontryaginDual_eval (G := G))).tendsto 1
    rw [map_one] at ht
    exact ht h1
  have hPow : ∀ x : G, (∀ k : ℕ, x ^ k ∈ W) → x = 1 := by
    intro x hx
    let evx : PontryaginDual G →* Circle :=
      { toFun := fun χ ↦ χ x, map_one' := rfl, map_mul' := fun _ _ ↦ rfl }
    have hKx : K ⊆ evx.ker := by
      intro χ hχ
      apply MonoidHom.mem_ker.mpr
      apply Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two
      intro k _
      have := hx k hχ
      change χ (x ^ k) ∈ _ at this
      rwa [map_pow] at this
    have hTop : ⊤ ≤ evx.ker := hGen ▸ (Subgroup.closure_le _).mpr hKx
    apply (pontryaginDual_pairing_separates (G := G)).1
    funext χ
    exact (MonoidHom.mem_ker.mp (hTop (Subgroup.mem_top χ))).trans (map_one χ).symm
  obtain ⟨t, f, -, hker⟩ := exists_torusHom_of_noSmallCyclicSubgroups hW hPow
  exact isLocallyEuclidean_of_torusHom_discreteKernel f hker

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
/-- Compact generation is invariant under topological group isomorphisms. -/
theorem isCompactlyGeneratedGroup_of_continuousMulEquiv {H : Type*} [CommGroup H]
    [TopologicalSpace H] (e : G ≃ₜ* H) (h : IsCompactlyGeneratedGroup G) :
    IsCompactlyGeneratedGroup H := by
  obtain ⟨U, hU, hUc, hGen⟩ := h
  refine ⟨e '' U, ?_, hUc.image e.continuous, ?_⟩
  · have := e.toHomeomorph.isOpenMap.image_mem_nhds hU
    rw [show e.toHomeomorph (1 : G) = 1 from map_one e] at this
    exact this
  · have := MonoidHom.map_closure (e.toMulEquiv.toMonoidHom) U
    rw [hGen, Subgroup.map_top_of_surjective _ e.surjective] at this
    exact this.symm

/-- Paper: Definition D.1.5.1(1), p. 760. The trivial subgroup is good exactly
when the group is locally Euclidean.
Deviation: Sanity check using the fact that its annihilator is the entire dual. -/
theorem isBruhatGoodSubgroup_bot_iff :
    IsBruhatGoodSubgroup (⊥ : Subgroup G) ↔ IsLocallyEuclidean G := by
  have htop : lcaAnnihilator (⊥ : Subgroup G) = ⊤ := by
    ext χ
    simp only [Subgroup.mem_top, iff_true]
    rw [mem_lcaAnnihilator_iff]
    intro x
    rw [Subgroup.mem_bot.mp x.2]
    exact map_one χ
  let eTop : (⊤ : Subgroup (PontryaginDual G)) ≃ₜ* PontryaginDual G :=
    { Subgroup.topEquiv with
      continuous_toFun := continuous_subtype_val
      continuous_invFun := continuous_id.subtype_mk _ }
  unfold IsBruhatGoodSubgroup
  rw [htop]
  constructor
  · rintro ⟨-, -, hcg⟩
    exact isLocallyEuclidean_of_isCompactlyGeneratedGroup_dual
      (isCompactlyGeneratedGroup_of_continuousMulEquiv eTop hcg)
  · intro h
    refine ⟨by simp, by simp, ?_⟩
    exact isCompactlyGeneratedGroup_of_continuousMulEquiv eTop.symm
      (isCompactlyGeneratedGroup_dual_of_isLocallyEuclidean h)

/-- Paper: Lemma D.1.4.6(4), p. 758. An open subgroup of the dual has a
compact annihilator in the original group. -/
private theorem isCompact_lcaDualAnnihilator (H : Subgroup (PontryaginDual G))
    (hH : IsOpen (H : Set (PontryaginDual G))) :
    IsCompact (lcaDualAnnihilator H : Set G) := by
  have hCompact := isCompact_lcaAnnihilator H hH
  convert (isClosedEmbedding_pontryaginDual_eval (G := G)).isCompact_preimage hCompact using 1
  ext x
  exact (mem_lcaDualAnnihilator_iff H x).trans
    (mem_lcaAnnihilator_iff H (pontryaginDual_eval x)).symm

/-- Paper: Definition D.1.5.1, p. 760. The intersection of two good
subgroups is good. Its annihilator is the join of their annihilators. -/
private theorem isBruhatGoodSubgroup_inf {K L : Subgroup G}
    (hK : IsBruhatGoodSubgroup K) (hL : IsBruhatGoodSubgroup L) :
    IsBruhatGoodSubgroup (K ⊓ L) := by
  have hLc := isCompact_lcaDualAnnihilator (lcaAnnihilator L) hL.2.1
  rw [lcaDualAnnihilator_annihilator L hL.1] at hLc
  have hAnti : Antitone (lcaAnnihilator (G := G)) := fun _ _ h χ hχ ↦
    (mem_lcaAnnihilator_iff _ χ).mpr fun x ↦
      (mem_lcaAnnihilator_iff _ χ).mp hχ ⟨x, h x.property⟩
  have hAnn : lcaAnnihilator (K ⊓ L) = lcaAnnihilator K ⊔ lcaAnnihilator L := by
    apply le_antisymm _ (sup_le (hAnti inf_le_left) (hAnti inf_le_right))
    intro χ hχ
    let restrict : PontryaginDual K :=
      PontryaginDual.map ⟨K.subtype, continuous_subtype_val⟩ χ
    obtain ⟨ψ, hψ, hψL⟩ := exists_pontryaginDual_extension_trivial_on_compact K L hK.1 hLc
      restrict (fun x hx ↦ (mem_lcaAnnihilator_iff _ χ).mp hχ ⟨x, x.property, hx⟩)
    refine Subgroup.mem_sup.mpr ⟨χ * ψ⁻¹, ?_, ψ, (mem_lcaAnnihilator_iff L ψ).mpr hψL, ?_⟩
    · refine (mem_lcaAnnihilator_iff K _).mpr fun x ↦ ?_
      change χ x * (ψ x)⁻¹ = 1
      rw [hψ x]
      exact mul_inv_cancel _
    · exact inv_mul_cancel_right χ ψ
  let A : OpenCompactlyGeneratedSubgroups (PontryaginDual G) := ⟨lcaAnnihilator K, hK.2⟩
  let B : OpenCompactlyGeneratedSubgroups (PontryaginDual G) := ⟨lcaAnnihilator L, hL.2⟩
  obtain ⟨C, hAC, hBC⟩ := (openCompactlyGeneratedSubgroups_colimit
    (G := PontryaginDual G)).1.directed A B
  have hOpen : IsOpen (lcaAnnihilator (K ⊓ L) : Set (PontryaginDual G)) :=
    Subgroup.isOpen_mono (hAnti inf_le_left) hK.2.1
  refine ⟨hK.1.inter hL.1, hOpen, ?_⟩
  let J := lcaAnnihilator (K ⊓ L)
  have hJC : J ≤ C.val := by
    change lcaAnnihilator (K ⊓ L) ≤ C.val
    rw [hAnn]
    exact sup_le (show A.val ≤ C.val from hAC) (show B.val ≤ C.val from hBC)
  have hClosed : IsClosed (J.subgroupOf C.val : Set C.val) :=
    (J.isClosed_of_isOpen hOpen).preimage continuous_subtype_val
  let : LocallyCompactSpace C.val := C.property.1.isOpenEmbedding_subtypeVal.locallyCompactSpace
  obtain ⟨U, hU, hUc, hGen⟩ := isCompactlyGeneratedGroup_closedSubgroup C.property.2
    (J.subgroupOf C.val) hClosed
  let e := Subgroup.subgroupOfEquivOfLe hJC
  have he : Continuous e := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have he' : Continuous e.symm := (continuous_subtype_val.subtype_mk _).subtype_mk _
  refine ⟨e '' U, ?_, hUc.image he, ?_⟩
  · have hEq : e '' U = e.symm ⁻¹' U := e.toEquiv.image_eq_preimage_symm U
    rw [hEq]
    exact he'.continuousAt.preimage_mem_nhds (by simpa only [map_one] using hU)
  · change Subgroup.closure (e.toMonoidHom '' U) = ⊤
    rw [← MonoidHom.map_closure e.toMonoidHom, hGen,
      Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]

/-- Paper: Lemma D.1.4.6(1), p. 758. An open subgroup of the dual is recovered
from its annihilator in the original group.
Deviation: We isolate the open-subgroup case on the dual side. Once evaluation
is surjective onto the bidual, this follows by separating points in the discrete quotient. -/
theorem lcaAnnihilator_dualAnnihilator_of_open (H : Subgroup (PontryaginDual G))
    (hH : IsOpen (H : Set (PontryaginDual G))) :
    lcaAnnihilator (lcaDualAnnihilator H) = H := by
  apply le_antisymm
  · -- A character outside `H` is separated from `H` by a character of the discrete quotient.
    -- By biduality that character is evaluation at a point of the dual annihilator.
    intro χ hχ
    by_contra hχH
    let D := PontryaginDual G ⧸ H
    let : DiscreteTopology D := QuotientGroup.discreteTopology hH
    let q : PontryaginDual G →ₜ* D := ⟨QuotientGroup.mk' H, QuotientGroup.continuous_mk⟩
    have hq : q χ ≠ 1 := fun h ↦ hχH ((QuotientGroup.eq_one_iff χ).mp h)
    obtain ⟨ψ, hψ⟩ : ∃ ψ : PontryaginDual D, ψ (q χ) ≠ 1 := by
      by_contra! h
      apply hq
      apply (pontryaginDual_pairing_separates (G := D)).1
      funext ψ
      exact (h ψ).trans (map_one ψ).symm
    obtain ⟨e, he⟩ := pontryaginDual_bidual (G := G)
    let Ψ : PontryaginDual (PontryaginDual G) := PontryaginDual.map q ψ
    have hx (η : PontryaginDual G) : η (e.symm Ψ) = ψ (q η) := by
      rw [← he (e.symm Ψ) η, e.apply_symm_apply]
      rfl
    have hxmem : e.symm Ψ ∈ lcaDualAnnihilator H := by
      refine (mem_lcaDualAnnihilator_iff H _).mpr fun η ↦ ?_
      have hη : q η.val = 1 := (QuotientGroup.eq_one_iff η.val).mpr η.property
      rw [hx, hη, map_one]
    exact hψ ((hx χ).symm.trans ((mem_lcaAnnihilator_iff _ χ).mp hχ ⟨_, hxmem⟩))
  · intro χ hχ
    refine (mem_lcaAnnihilator_iff _ χ).mpr fun x ↦ ?_
    exact (mem_lcaDualAnnihilator_iff H x.val).mp x.property ⟨χ, hχ⟩

/-- Paper: Lemma D.1.5.2, p. 760. Structural pairs form a nonempty directed order. -/
theorem bruhatStructuralPair_filtered :
    Nonempty (BruhatStructuralPair G) ∧ IsDirectedOrder (BruhatStructuralPair G) := by
  constructor
  · obtain ⟨A, _⟩ := (openCompactlyGeneratedSubgroups_colimit (G := PontryaginDual G)).2.1 1
    let K := lcaDualAnnihilator A.val
    have hKc : IsCompact (K : Set G) := isCompact_lcaDualAnnihilator A.val A.property.1
    have hAnn : lcaAnnihilator K = A.val :=
      lcaAnnihilator_dualAnnihilator_of_open A.val A.property.1
    have hK : IsBruhatGoodSubgroup K :=
      ⟨hKc.isClosed, hAnn.symm ▸ A.property⟩
    obtain ⟨H, hKH⟩ := exists_openCompactlyGeneratedSubgroup_contains hKc
    exact ⟨⟨(H.val, OrderDual.toDual K), H.property.1, H.property.2, hK, hKH⟩⟩
  · constructor
    intro p q
    obtain ⟨H, hp, hq⟩ := (openCompactlyGeneratedSubgroups_colimit (G := G)).1.directed
      ⟨p.val.1, p.property.1, p.property.2.1⟩ ⟨q.val.1, q.property.1, q.property.2.1⟩
    let K := OrderDual.ofDual p.val.2 ⊓ OrderDual.ofDual q.val.2
    have hK := isBruhatGoodSubgroup_inf p.property.2.2.1 q.property.2.2.1
    have hKH : K ≤ H.val := inf_le_left.trans (p.property.2.2.2.trans hp)
    have hKp : K ≤ OrderDual.ofDual p.val.2 := inf_le_left
    have hKq : K ≤ OrderDual.ofDual q.val.2 := inf_le_right
    exact ⟨⟨(H.val, OrderDual.toDual K), H.property.1, H.property.2, hK, hKH⟩, ⟨hp, hKp⟩, ⟨hq, hKq⟩⟩

/-- Paper: Lemma D.1.5.2(1), p. 761. The quotient attached to a structural pair
has an elementary presentation. -/
theorem BruhatStructuralPair.elementary (p : BruhatStructuralPair G) :
    Nonempty (ElementaryLCAPresentation p.quotient) := by
  let H := p.val.1
  let k := OrderDual.ofDual p.val.2
  let N := k.comap H.subtype
  obtain ⟨hH, hGen, ⟨hk, hkOpen, hkGen⟩, _⟩ := p.property
  let : LocallyCompactSpace H := hH.isOpenEmbedding_subtypeVal.locallyCompactSpace
  let hN : IsClosed (N : Set H) := hk.preimage continuous_subtype_val
  refine lca_elementary_iff.mp ⟨isCompactlyGeneratedGroup_quotient hGen N hN, ?_⟩
  let A := lcaAnnihilator k
  let : LocallyCompactSpace A := hkOpen.isOpenEmbedding_subtypeVal.locallyCompactSpace
  -- Evaluation on the annihilator has kernel exactly the good subgroup.
  let ι : A →ₜ* PontryaginDual G := ⟨A.subtype, continuous_subtype_val⟩
  let f : H →ₜ* PontryaginDual A :=
    (PontryaginDual.map ι).comp (pontryaginDual_eval.comp ⟨H.subtype, continuous_subtype_val⟩)
  have hker : f.toMonoidHom.ker = N := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_comap, Subgroup.coe_subtype,
      ← lcaDualAnnihilator_annihilator k hk, mem_lcaDualAnnihilator_iff]
    exact ⟨fun hx χ ↦ congrArg (fun ψ : PontryaginDual A ↦ ψ χ) hx,
      fun hx ↦ PontryaginDual.ext hx⟩
  let e : p.quotient →ₜ* PontryaginDual A :=
    ⟨QuotientGroup.lift N f.toMonoidHom hker.ge,
      (QuotientGroup.isQuotientMap_mk N).continuous_iff.mpr f.continuous⟩
  have he : Function.Injective e :=
    (QuotientGroup.injective_lift_iff N f.toMonoidHom hker.ge).mpr hker.symm
  -- A neighborhood with no nontrivial cyclic subgroups pulls back along this injection.
  obtain ⟨W, hW, hPow⟩ := exists_nhds_one_of_isLocallyEuclidean
    (isCompactlyGeneratedGroup_iff_dual_locallyEuclidean.mp hkGen)
  have hW' : W ∈ 𝓝 (e 1) := by rwa [map_one]
  refine isLocallyEuclidean_of_noSmallCyclicSubgroups
    (e.continuous.continuousAt.preimage_mem_nhds hW') ?_
  intro x hx
  apply he
  rw [map_one]
  exact hPow (e x) fun n ↦ map_pow e x n ▸ hx n

/-- Paper: Lemma D.1.5.2(2), p. 761. The two annihilators form a structural pair
in the dual, with the annihilator of the good subgroup as the open subgroup. -/
theorem BruhatStructuralPair.dual (p : BruhatStructuralPair G) :
    ∃ q : BruhatStructuralPair (PontryaginDual G),
      q.val.1 = lcaAnnihilator (OrderDual.ofDual p.val.2) ∧
      OrderDual.ofDual q.val.2 = lcaAnnihilator p.val.1 := by
  let H := p.val.1
  let k := OrderDual.ofDual p.val.2
  obtain ⟨hH, hGen, ⟨_, hkOpen, hkGen⟩, hkH⟩ := p.property
  have hCompact := isCompact_lcaAnnihilator H hH
  refine ⟨⟨(lcaAnnihilator k, OrderDual.toDual (lcaAnnihilator H)), hkOpen, hkGen,
    ⟨hCompact.isClosed, isOpen_lcaAnnihilator _ hCompact, ?_⟩, ?_⟩, rfl, rfl⟩
  · obtain ⟨e, he⟩ := pontryaginDual_bidual (G := G)
    let A := lcaAnnihilator (lcaAnnihilator H)
    change IsCompactlyGeneratedGroup A
    have hMem (x : G) : e x ∈ A ↔ x ∈ H := by
      change e x ∈ lcaAnnihilator (lcaAnnihilator H) ↔ x ∈ H
      rw [mem_lcaAnnihilator_iff]
      simp_rw [he]
      rw [← mem_lcaDualAnnihilator_iff, lcaDualAnnihilator_annihilator H
        (H.isClosed_of_isOpen hH)]
    let f : H →* A := (e.toMonoidHom.comp H.subtype).codRestrict A
      fun x ↦ (hMem x).mpr x.property
    have hSurj : Function.Surjective f := by
      intro y
      obtain ⟨x, hx⟩ := e.surjective (y : PontryaginDual (PontryaginDual G))
      exact ⟨⟨x, (hMem x).mp (hx.symm ▸ y.property)⟩, Subtype.ext hx⟩
    have hInducing : IsInducing f := IsInducing.subtypeVal.of_comp_iff.mp
      (e.toHomeomorph.isInducing.comp IsInducing.subtypeVal)
    have hOpen : IsOpenMap f := hInducing.isOpenMap (hSurj.range_eq ▸ isOpen_univ)
    obtain ⟨U, hU, hUc, hUgen⟩ := hGen
    refine ⟨f '' U, ?_, hUc.image hInducing.continuous, ?_⟩
    · simpa only [map_one] using hOpen.image_mem_nhds hU
    · rw [← MonoidHom.map_closure, hUgen, Subgroup.map_top_of_surjective f hSurj]
  · intro χ hχ
    exact (mem_lcaAnnihilator_iff k χ).mpr fun x ↦
      (mem_lcaAnnihilator_iff H χ).mp hχ ⟨x, hkH x.property⟩

section Fourier

variable [MeasurableSpace G] [BorelSpace G]

local instance : MeasurableSpace (PontryaginDual G) := borel _

variable {μ : Measure G} [μ.IsHaarMeasure] [μ.Regular]
variable {ν : Measure (PontryaginDual G)}

-- TODO(paper-gap): D.1.5.2(3) asserts pointwise converses for arbitrary integrable
-- representatives. On ℝ a function nonzero only at 0 has zero Fourier transform.

-- Retain the integrability hypothesis in the existing signature.
set_option linter.unusedVariables false in
/-- Paper: Lemma D.1.5.2(3), p. 761. Invariance under a subgroup forces the Fourier
transform to vanish off the annihilator.
Deviation: Stated in the forward direction because pointwise invariance can fail
for an integrable representative of an invariant class. -/
theorem lcaFourier_support_subset_annihilator (_hν : IsLCAPlancherelMeasure μ ν)
    {f : G → ℂ} (hf : Integrable f μ) (_hfhat : Integrable (lcaFourier μ f) ν)
    (H : Subgroup G) (_hH : IsClosed (H : Set G)) (hinv : ∀ h : H, ∀ x, f (h.val * x) = f x) :
    Function.support (lcaFourier μ f) ⊆ (lcaAnnihilator H : Set (PontryaginDual G)) := by
  intro χ hχ
  refine (mem_lcaAnnihilator_iff H χ).mpr fun h ↦ ?_
  have htranslate : lcaFourier μ f χ = lcaFourier μ f χ * star (χ h.val : ℂ) := by
    unfold lcaFourier
    calc
      (∫ x, f x * star (χ x : ℂ) ∂μ) =
          ∫ x, f (h.val * x) * star (χ (h.val * x) : ℂ) ∂μ :=
        (integral_mul_left_eq_self (μ := μ) (fun x ↦ f x * star (χ x : ℂ)) h.val).symm
      _ = (∫ x, f x * star (χ x : ℂ) ∂μ) * star (χ h.val : ℂ) := by
        rw [← integral_mul_const]
        apply integral_congr_ae
        exact .of_forall fun x ↦ by
          change f (h.val * x) * star (χ (h.val * x) : ℂ) =
            (f x * star (χ x : ℂ)) * star (χ h.val : ℂ)
          rw [hinv h x, map_mul, Circle.coe_mul, star_mul, mul_assoc]
  have hstar : star (χ h.val : ℂ) = 1 :=
    mul_left_cancel₀ (Function.mem_support.mp hχ) (htranslate.symm.trans (mul_one _).symm)
  exact Circle.coe_eq_one.mp (by simpa only [star_star, star_one] using congrArg star hstar)

-- Keep the existing hypotheses on integrability and regularity in the statement.
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
/-- Paper: Lemma D.1.5.2(3), p. 761. Support in the open subgroup and invariance
under the good subgroup give the corresponding conditions for the dual pair.
Deviation: Stated in the forward direction because pointwise support and invariance
can fail after changing a representative on a null set. -/
theorem lcaFourier_structuralPair_imp (_hν : IsLCAPlancherelMeasure μ ν)
    {f : G → ℂ} (hf : Integrable f μ) (_hfhat : Integrable (lcaFourier μ f) ν)
    (a : BruhatStructuralPair G) (hs : Function.support f ⊆ (a.val.1 : Set G))
    (hinv : ∀ h : ↥(OrderDual.ofDual a.val.2 : Subgroup G), ∀ x, f (h.val * x) = f x) :
    (∀ χ : lcaAnnihilator a.val.1, ∀ ψ : PontryaginDual G,
      lcaFourier μ f (χ.val * ψ) = lcaFourier μ f ψ) ∧
      Function.support (lcaFourier μ f) ⊆
        (lcaAnnihilator (OrderDual.ofDual a.val.2) : Set (PontryaginDual G)) := by
  constructor
  · intro χ ψ
    unfold lcaFourier
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    by_cases hx : x ∈ a.val.1
    · have hχ : χ.val x = 1 := (mem_lcaAnnihilator_iff a.val.1 χ.val).mp χ.property ⟨x, hx⟩
      change f x * star ((χ.val x * ψ x : Circle) : ℂ) = f x * star (ψ x : ℂ)
      rw [hχ, one_mul]
    · have hfx : f x = 0 := Function.notMem_support.mp fun hx' ↦ hx (hs hx')
      simp only [hfx, zero_mul]
  · intro ψ hψ
    refine (mem_lcaAnnihilator_iff _ ψ).mpr fun h ↦ ?_
    have hmul : lcaFourier μ f ψ * star (ψ h.val : ℂ) = lcaFourier μ f ψ := by
      unfold lcaFourier
      rw [← integral_mul_const]
      calc
        _ = ∫ x, f (h.val * x) * star (ψ (h.val * x) : ℂ) ∂μ := by
          refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
          simp only [hinv h x, map_mul, Circle.coe_mul, star_mul, mul_assoc]
        _ = _ := integral_mul_left_eq_self (fun x ↦ f x * star (ψ x : ℂ)) h.val
    have hstar := (mul_eq_left₀ (Function.mem_support.mp hψ)).mp hmul
    apply Circle.coe_injective
    simpa only [Circle.coe_one, star_star, star_one] using congrArg star hstar

end Fourier
end StructuralPairs

section SchwartzBruhat

variable {G : Type*} [CommGroup G] [TopologicalSpace G]

/-- Paper: Definition D.1.5.3(1), p. 762. A single good subgroup fixes the
function and its descent to each structural quotient with that subgroup is of class Cᵖ.
The derivatives are tested on the real and torus covers of the discrete fibers. -/
def IsBruhatContDiff (p : ℕ) (f : G → ℂ) : Prop :=
  ∃ k : Subgroup G, IsBruhatGoodSubgroup k ∧ (∀ h : k, ∀ x, f (h.val * x) = f x) ∧
    ∀ a : BruhatStructuralPair G, OrderDual.ofDual a.val.2 = k →
      ∃ f₀ : a.quotient → ℂ, (∀ x : a.val.1, f₀ (QuotientGroup.mk x) = f x.val) ∧
        ∀ (e : ElementaryLCAPresentation a.quotient)
          (z : Fin e.latticeRank → ℤ) (b : e.finiteFactor),
          ContDiff ℝ (p : ℕ∞) (fun xt ↦ f₀ (e.equiv.symm (Multiplicative.ofAdd
            (elementaryCover xt z b))))

/-- Paper: Definition D.1.5.3(1), p. 762. A function is smooth if it is of class Cᵖ
for every finite order p. -/
def IsBruhatSmooth (f : G → ℂ) : Prop :=
  ∀ p : ℕ, IsBruhatContDiff p f

/-- A good subgroup of the real line is trivial, since a compact subgroup cannot
contain all integer multiples of a nonzero real number. -/
private theorem isBruhatGoodSubgroup_real_eq_bot {k : Subgroup (Multiplicative ℝ)}
    (hk : IsBruhatGoodSubgroup k) : k = ⊥ := by
  have hc : IsCompact (k : Set (Multiplicative ℝ)) := by
    rw [← lcaDualAnnihilator_annihilator k hk.1]
    exact isCompact_lcaDualAnnihilator _ hk.2.1
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp (hc.image
    (show Continuous (Multiplicative.toAdd : Multiplicative ℝ → ℝ) from continuous_id)).isBounded
  refine le_antisymm (fun x hx ↦ Subgroup.mem_bot.mpr ?_) bot_le
  by_contra h
  have hxpos : 0 < |x.toAdd| := abs_pos.mpr (show x.toAdd ≠ 0 from h)
  obtain ⟨n, hn⟩ := exists_nat_gt (C / |x.toAdd|)
  have hbound := hC (x ^ n).toAdd ⟨x ^ n, k.pow_mem hx n, rfl⟩
  change ‖n • x.toAdd‖ ≤ C at hbound
  rw [nsmul_eq_mul, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Nat.cast_nonneg n)] at hbound
  exact (not_lt_of_ge hbound) ((div_lt_iff₀ hxpos).mp hn)

/-- The interval from `-1` to `1` is a compact generating neighborhood of the real line. -/
private theorem isCompactlyGeneratedGroup_real :
    IsCompactlyGeneratedGroup (Multiplicative ℝ) := by
  let U : Set (Multiplicative ℝ) := Multiplicative.toAdd ⁻¹' Icc (-1 : ℝ) 1
  refine ⟨U, ?_, ?_, eq_top_iff.mpr fun x _ ↦ ?_⟩
  · change Icc (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ)
    exact Icc_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1)
  · change IsCompact (Icc (-1 : ℝ) 1)
    exact isCompact_Icc
  · obtain ⟨n, hn⟩ := exists_nat_gt (|x.toAdd|)
    have hnpos : (0 : ℝ) < n := (abs_nonneg _).trans_lt hn
    let y := Multiplicative.ofAdd (x.toAdd / n)
    have hy : y ∈ U := by
      change x.toAdd / n ∈ Icc (-1 : ℝ) 1
      apply abs_le.mp
      rw [abs_div, abs_of_pos hnpos, div_le_iff₀ hnpos, one_mul]
      exact hn.le
    have he : (y ^ n : Multiplicative ℝ) = x := by
      apply Multiplicative.toAdd.injective
      change n • (x.toAdd / n) = x.toAdd
      rw [nsmul_eq_mul]
      change (n : ℝ) * (x.toAdd / n) = x.toAdd
      rw [mul_comm, div_mul_cancel₀ _ hnpos.ne']
    exact he ▸ (Subgroup.closure U).pow_mem (Subgroup.subset_closure hy) n

/-- For a real structural pair with trivial good subgroup, the quotient identifies
with the real line by sending the class of each element to that element. -/
private theorem exists_bruhatQuotientEquiv_real (a : BruhatStructuralPair (Multiplicative ℝ))
    (hk : OrderDual.ofDual a.val.2 = ⊥) :
    ∃ q : a.quotient ≃ₜ* Multiplicative ℝ, ∀ x : a.val.1, q (QuotientGroup.mk x) = x.val := by
  letI : PreconnectedSpace (Multiplicative ℝ) := inferInstanceAs (PreconnectedSpace ℝ)
  have hTop : (a.val.1 : Set (Multiplicative ℝ)) = univ :=
    (show IsClopen (a.val.1 : Set (Multiplicative ℝ)) from
      ⟨a.val.1.isClosed_of_isOpen a.property.1, a.property.1⟩).eq_univ ⟨1, a.val.1.one_mem⟩
  let incl (x : Multiplicative ℝ) : a.val.1 := ⟨x, by
    change x ∈ (a.val.1 : Set (Multiplicative ℝ))
    rw [hTop]
    exact mem_univ x⟩
  let N := (OrderDual.ofDual a.val.2).comap a.val.1.subtype
  have hN : N = a.val.1.subtype.ker := by
    change (OrderDual.ofDual a.val.2).comap a.val.1.subtype = _
    rw [hk]
    rfl
  let e : a.quotient ≃* Multiplicative ℝ :=
    (QuotientGroup.quotientMulEquivOfEq hN).trans
      (QuotientGroup.quotientKerEquivOfRightInverse a.val.1.subtype incl fun _ ↦ rfl)
  have he (x : a.val.1) : e (QuotientGroup.mk x) = x.val := rfl
  refine ⟨{ e with
    continuous_toFun := (QuotientGroup.isQuotientMap_mk N).continuous_iff.mpr
      (show Continuous (fun x : a.val.1 ↦ e (QuotientGroup.mk x)) by
        simp only [he]
        exact continuous_subtype_val)
    continuous_invFun := ?_ }, he⟩
  have hinv (x : Multiplicative ℝ) :
      e.symm x = QuotientGroup.mk (incl x) :=
    e.symm_apply_eq.mpr (he (incl x)).symm
  change Continuous (fun x ↦ e.symm x)
  simp only [hinv]
  exact QuotientGroup.continuous_mk.comp (continuous_id.subtype_mk _)

/-- Paper: Definition D.1.5.3(1), p. 762. On the real additive group, finite
orders of Bruhat differentiability agree with ordinary differentiability.
Deviation: Sanity check on the real group. -/
theorem isBruhatContDiff_real_iff (p : ℕ) (f : Multiplicative ℝ → ℂ) :
    IsBruhatContDiff p f ↔ ContDiff ℝ (p : ℕ∞) (f ∘ Multiplicative.ofAdd) := by
  let line := (EuclideanSpace.equiv (Fin 1) ℝ).trans
    (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ)
  let chart : EuclideanSpace ℝ (Fin 1) ≃ₜ Multiplicative ℝ := line.toHomeomorph
  have hGood : IsBruhatGoodSubgroup (⊥ : Subgroup (Multiplicative ℝ)) :=
    isBruhatGoodSubgroup_bot_iff.mpr ⟨1, ⟨chart.chartedSpace⟩⟩
  constructor
  · rintro ⟨k, hk, -, h⟩
    have hkbot := isBruhatGoodSubgroup_real_eq_bot hk
    subst k
    let topEquiv : (⊤ : Subgroup (Multiplicative ℝ)) ≃ₜ* Multiplicative ℝ :=
      { Subgroup.topEquiv with
        continuous_toFun := continuous_subtype_val
        continuous_invFun := continuous_id.subtype_mk _ }
    let a : BruhatStructuralPair (Multiplicative ℝ) :=
      ⟨(⊤, OrderDual.toDual ⊥), by simp,
        isCompactlyGeneratedGroup_of_continuousMulEquiv topEquiv.symm isCompactlyGeneratedGroup_real,
        hGood, bot_le⟩
    obtain ⟨q, hq⟩ := exists_bruhatQuotientEquiv_real a rfl
    -- Test differentiability on the presentation with only one real coordinate.
    let : Unique ((Fin 0 → AddCircle (1 : ℝ)) × (Fin 0 → ℤ) × PUnit) :=
      uniqueOfSubsingleton 0
    let m : Multiplicative (ElementaryLieGroup 1 0 0 PUnit) ≃ₜ* Multiplicative ℝ :=
      ContinuousMulEquiv.mk' ((Homeomorph.prodUnique _ _).trans line.toHomeomorph)
        (fun x y ↦ line.map_add x.toAdd.1 y.toAdd.1)
    let e : ElementaryLCAPresentation a.quotient := ⟨1, 0, 0, PUnit, q.trans m.symm⟩
    obtain ⟨g, hg, hs⟩ := h a rfl
    have hg' (y : a.quotient) : g y = f (q y) := by
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
      exact (hg x).trans (congrArg f (hq x).symm)
    have hcomp := (hs e 0 0).comp
      (line.symm.contDiff.prodMk (contDiff_const (c := (0 : EuclideanSpace ℝ (Fin 0)))))
    convert hcomp using 1
    funext t
    simp only [Function.comp_apply, hg']
    change f (Multiplicative.ofAdd t) =
      f (q (q.symm (m (Multiplicative.ofAdd (elementaryCover (line.symm t, 0) 0 0)))))
    rw [q.apply_symm_apply]
    exact congrArg (f ∘ Multiplicative.ofAdd) (line.apply_symm_apply t).symm
  · intro hf
    refine ⟨⊥, hGood, ?_, fun a ha ↦ ?_⟩
    · intro h x
      rw [Subgroup.mem_bot.mp h.property, one_mul]
    obtain ⟨q, hq⟩ := exists_bruhatQuotientEquiv_real a ha
    refine ⟨f ∘ q, fun x ↦ congrArg f (hq x), ?_⟩
    intro e z b
    -- In the cover of each discrete fiber, the map to the real quotient is affine.
    let ψ := AddMonoidHom.toMultiplicative.symm
      ((e.equiv.symm.trans q).toMulEquiv.toMonoidHom)
    let cover : EuclideanSpace ℝ (Fin e.realDim) × EuclideanSpace ℝ (Fin e.torusDim) →+
        ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor :=
      { toFun := fun u ↦ elementaryCover u 0 0
        map_zero' := by simp [elementaryCover, Pi.zero_def]
        map_add' := fun u v ↦ by simp [elementaryCover, Pi.add_def] }
    have hcover : Continuous cover :=
      continuous_fst.prodMk ((continuous_pi fun i ↦
        (AddCircle.continuous_mk' (1 : ℝ)).comp
          ((continuous_apply i).comp (EuclideanSpace.equiv _ ℝ).continuous |>.comp
            continuous_snd)).prodMk
        continuous_const)
    have hψ : Continuous ψ := (e.equiv.symm.trans q).continuous
    have hlin := ((ψ.comp cover).toRealLinearMap (hψ.comp hcover)).contDiff
      (n := (p : ℕ∞))
    have hshift (u : EuclideanSpace ℝ (Fin e.realDim) × EuclideanSpace ℝ (Fin e.torusDim)) :
        elementaryCover u z b = cover u + (0, 0, z, b) := by
      simp [cover, elementaryCover]
    simp_rw [hshift]
    exact hf.comp (show ContDiff ℝ (p : ℕ∞) (fun u ↦ ψ (cover u + (0, 0, z, b))) by
      simp only [map_add]
      exact hlin.add contDiff_const)

/-- The Pontryagin dual of the additive reals is connected. -/
private theorem connectedSpace_pontryaginDual_multiplicative_real :
    ConnectedSpace (PontryaginDual (Multiplicative ℝ)) := by
  obtain ⟨d, _⟩ := exists_realPontryaginDualEquiv
  have : ConnectedSpace (Multiplicative ℝ) := inferInstanceAs (ConnectedSpace ℝ)
  exact d.surjective.connectedSpace d.continuous

/-- A compact identity neighborhood generates a connected locally compact group. -/
private theorem realSmooth_compactlyGenerated (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [PreconnectedSpace G] :
    IsCompactlyGeneratedGroup G := by
  obtain ⟨K, hc, hK⟩ := exists_compact_mem_nhds (1 : G)
  have hOpen : IsOpen (Subgroup.closure K : Set G) :=
    Subgroup.isOpen_of_mem_nhds _ (mem_of_superset hK Subgroup.subset_closure)
  exact ⟨K, hK, hc, SetLike.coe_injective
    ((OpenSubgroup.isClopen ⟨Subgroup.closure K, hOpen⟩).eq_univ ⟨1, Subgroup.one_mem _⟩)⟩

/-- The trivial subgroup is the only good subgroup of the additive reals. -/
private theorem isBruhatGoodSubgroup_real_bot :
    IsBruhatGoodSubgroup (⊥ : Subgroup (Multiplicative ℝ)) := by
  have := connectedSpace_pontryaginDual_multiplicative_real
  have hAnn : lcaAnnihilator (⊥ : Subgroup (Multiplicative ℝ)) = ⊤ := by
    refine eq_top_iff.mpr fun χ _ ↦ (mem_lcaAnnihilator_iff _ _).mpr fun x ↦ ?_
    rw [Subgroup.mem_bot.mp x.property, map_one]
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Subgroup.coe_bot] using isClosed_singleton
  · rw [hAnn, Subgroup.coe_top]
    exact isOpen_univ
  · rw [hAnn]
    let : ConnectedSpace (⊤ : Subgroup (PontryaginDual (Multiplicative ℝ))) :=
      (Subgroup.topEquiv.symm.surjective.connectedSpace (continuous_id.subtype_mk _))
    have hOpen : IsOpen ((⊤ : Subgroup (PontryaginDual (Multiplicative ℝ))) :
        Set (PontryaginDual (Multiplicative ℝ))) := by simp
    let : LocallyCompactSpace (⊤ : Subgroup (PontryaginDual (Multiplicative ℝ))) :=
      hOpen.isOpenEmbedding_subtypeVal.locallyCompactSpace
    exact realSmooth_compactlyGenerated _

private theorem isBruhatGoodSubgroup_real_iff (k : Subgroup (Multiplicative ℝ)) :
    IsBruhatGoodSubgroup k ↔ k = ⊥ := by
  constructor
  · intro hk
    have := connectedSpace_pontryaginDual_multiplicative_real
    let U : OpenSubgroup (PontryaginDual (Multiplicative ℝ)) :=
      ⟨lcaAnnihilator k, hk.2.1⟩
    have hann : lcaAnnihilator k = ⊤ :=
      SetLike.coe_injective (U.isClopen.eq_univ ⟨1, U.one_mem⟩)
    refine le_antisymm (fun x hx ↦ Subgroup.mem_bot.mpr ?_) bot_le
    apply (pontryaginDual_pairing_separates (G := Multiplicative ℝ)).1
    funext χ
    exact ((mem_lcaAnnihilator_iff k χ).mp (hann ▸ Subgroup.mem_top χ) ⟨x, hx⟩).trans
      (map_one χ).symm
  · rintro rfl
    exact isBruhatGoodSubgroup_real_bot

/-- A real structural pair has full open subgroup and trivial kernel, so its quotient
map identifies it with the real group. -/
private theorem realSmooth_pair_quotient (a : BruhatStructuralPair (Multiplicative ℝ)) :
    ∃ (h : ∀ x : Multiplicative ℝ, x ∈ a.val.1) (q : Multiplicative ℝ ≃ₜ* a.quotient),
      ∀ x, q x = QuotientGroup.mk ⟨x, h x⟩ := by
  have : ConnectedSpace (Multiplicative ℝ) := inferInstanceAs (ConnectedSpace ℝ)
  have ha : a.val.1 = ⊤ := SetLike.coe_injective
    ((OpenSubgroup.isClopen ⟨a.val.1, a.property.1⟩).eq_univ ⟨1, Subgroup.one_mem _⟩)
  have hk : OrderDual.ofDual a.val.2 = ⊥ :=
    (isBruhatGoodSubgroup_real_iff _).mp a.property.2.2.1
  have h (x : Multiplicative ℝ) : x ∈ a.val.1 := ha ▸ Subgroup.mem_top x
  let i : Multiplicative ℝ ≃ₜ* a.val.1 :=
    { toMulEquiv :=
        { toFun := fun x ↦ ⟨x, h x⟩
          invFun := Subtype.val
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl
          map_mul' := fun _ _ ↦ rfl }
      continuous_toFun := continuous_id.subtype_mk _
      continuous_invFun := continuous_subtype_val }
  let k := OrderDual.ofDual a.val.2
  let p := (QuotientGroup.mk' (k.comap a.val.1.subtype)).comp i.toMulEquiv.toMonoidHom
  have hp : IsOpenQuotientMap p :=
    QuotientGroup.isOpenQuotientMap_mk.comp i.toHomeomorph.isOpenQuotientMap
  have hpInj : Function.Injective p := (MonoidHom.ker_eq_bot_iff p).mp (le_antisymm (fun x hx ↦ by
    change (QuotientGroup.mk (i x) : a.quotient) = 1 at hx
    exact hk ▸ (a.quotient_mk_eq_one (i x)).mp hx) bot_le)
  let q := MulEquiv.ofBijective p ⟨hpInj, hp.surjective⟩
  exact ⟨h, q.toContinuousMulEquiv (fun _ ↦ hp.isQuotientMap.isOpen_preimage), fun _ ↦ rfl⟩

/-- In any elementary presentation of a real structural quotient, the torus and
discrete factors are trivial and the real coordinate is a linear equivalence. -/
private theorem realSmooth_coordinates (a : BruhatStructuralPair (Multiplicative ℝ))
    (e : ElementaryLCAPresentation a.quotient) :
    e.torusDim = 0 ∧ e.latticeRank = 0 ∧ Subsingleton e.finiteFactor ∧
      ∃ (h : ∀ x : Multiplicative ℝ, x ∈ a.val.1)
        (L : ℝ ≃L[ℝ] EuclideanSpace ℝ (Fin e.realDim)),
        ∀ x : ℝ, (e.equiv (QuotientGroup.mk ⟨Multiplicative.ofAdd x, h _⟩)).toAdd =
          (L x, 0, 0, 0) := by
  obtain ⟨h, q, hq⟩ := realSmooth_pair_quotient a
  let E := EuclideanSpace ℝ (Fin e.realDim)
  let T := Fin e.torusDim → AddCircle (1 : ℝ)
  let Z := Fin e.latticeRank → ℤ
  let F := e.finiteFactor
  let P := ElementaryLieGroup e.realDim e.torusDim e.latticeRank F
  let w := q.trans e.equiv
  let W : ℝ ≃+ P := MulEquiv.toAdditive w.toMulEquiv
  have hW : Continuous W := w.continuous
  have hWi : Continuous W.symm := w.symm.continuous
  let : ConnectedSpace P := W.surjective.connectedSpace hW
  let : ConnectedSpace Z :=
    (show Function.Surjective (fun p : P ↦ p.2.2.1) from fun z ↦ ⟨(0, 0, z, 0), rfl⟩).connectedSpace
      (continuous_fst.comp (continuous_snd.comp continuous_snd))
  let : ConnectedSpace F :=
    (show Function.Surjective (fun p : P ↦ p.2.2.2) from fun b ↦ ⟨(0, 0, 0, b), rfl⟩).connectedSpace
      (continuous_snd.comp (continuous_snd.comp continuous_snd))
  have hZ : Subsingleton Z := subsingleton_of_preconnected_totallyDisconnected
  have hF : Subsingleton F := subsingleton_of_preconnected_totallyDisconnected
  have hz : e.latticeRank = 0 := by
    by_contra hn
    let i : Fin e.latticeRank := ⟨0, Nat.pos_of_ne_zero hn⟩
    have hi := congrFun (hZ.elim (0 : Z) 1) i
    exact zero_ne_one hi
  let tor : T →+ ℝ :=
    { toFun := fun t ↦ W.symm (0, t, 0, 0)
      map_zero' := by
        let p : P := (0, 0, 0, 0)
        have he : p + p = p :=
          Prod.ext (zero_add _) (Prod.ext (zero_add _) (Prod.ext (zero_add _) (hF.elim _ _)))
        have hzero := W.symm.map_add p p
        rw [he] at hzero
        change W.symm p = 0
        linarith
      map_add' := fun t u ↦ by
        rw [← W.symm.map_add]
        apply congrArg W.symm
        exact Prod.ext (zero_add _).symm
          (Prod.ext rfl (Prod.ext (zero_add _).symm (hF.elim _ _))) }
  have htor : Continuous tor :=
    hWi.comp (continuous_const.prodMk (continuous_id.prodMk continuous_const))
  obtain ⟨C, hC⟩ := (isCompact_univ.image htor).isBounded.exists_norm_le
  have htor0 (t : T) : tor t = 0 := by
    by_contra ht
    obtain ⟨n, hn⟩ := exists_nat_gt (C / ‖tor t‖)
    have hb := hC (tor (n • t)) (mem_image_of_mem tor (mem_univ (n • t)))
    rw [map_nsmul, nsmul_eq_mul, norm_mul, Real.norm_natCast] at hb
    exact (not_lt_of_ge hb) ((div_lt_iff₀ (norm_pos_iff.mpr ht)).mp hn)
  have hT : Subsingleton T := ⟨fun t u ↦ by
    have hu : tor t = tor u := (htor0 t).trans (htor0 u).symm
    exact congrArg (fun p : P ↦ p.2.1) (W.symm.injective hu)⟩
  have ht : e.torusDim = 0 := by
    by_contra hn
    let i : Fin e.torusDim := ⟨0, Nat.pos_of_ne_zero hn⟩
    have hi := congrFun (hT.elim (fun _ ↦ ((1 / 2 : ℝ) : AddCircle (1 : ℝ))) 0) i
    exact (show (1 / 2 : ℝ) ≠ 0 by norm_num)
      ((AddCircle.coe_eq_zero_iff_of_mem_Ico (by norm_num : (1 / 2 : ℝ) ∈ Ico 0 1)).mp hi)
  let I : P ≃+ E :=
    { toFun := Prod.fst
      invFun := fun x ↦ (x, 0, 0, 0)
      left_inv := fun p ↦ Prod.ext rfl (Subsingleton.elim _ _)
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl }
  let L := (W.trans I).toRealLinearEquiv (continuous_fst.comp hW)
    (hWi.comp (continuous_id.prodMk continuous_const))
  refine ⟨ht, hz, hF, h, L, fun x ↦ ?_⟩
  rw [← hq]
  exact Prod.ext rfl (Subsingleton.elim _ _)

/-- The full real group with trivial kernel has a one-dimensional elementary presentation. -/
private theorem realSmooth_stage :
    ∃ a : BruhatStructuralPair (Multiplicative ℝ), Nonempty (ElementaryLCAPresentation a.quotient) := by
  have : ConnectedSpace (Multiplicative ℝ) := inferInstanceAs (ConnectedSpace ℝ)
  have hTop : IsOpen ((⊤ : Subgroup (Multiplicative ℝ)) : Set (Multiplicative ℝ)) := by simp
  let : ConnectedSpace (⊤ : Subgroup (Multiplicative ℝ)) :=
    Subgroup.topEquiv.symm.surjective.connectedSpace (continuous_id.subtype_mk _)
  let : LocallyCompactSpace (⊤ : Subgroup (Multiplicative ℝ)) :=
    hTop.isOpenEmbedding_subtypeVal.locallyCompactSpace
  let a : BruhatStructuralPair (Multiplicative ℝ) := ⟨(⊤, OrderDual.toDual ⊥),
    hTop, realSmooth_compactlyGenerated _, isBruhatGoodSubgroup_real_bot, bot_le⟩
  obtain ⟨_, q, _⟩ := realSmooth_pair_quotient a
  let E := EuclideanSpace ℝ (Fin 1)
  let L : ℝ ≃L[ℝ] E := ContinuousLinearEquiv.ofFinrankEq (by simp [E, finrank_euclideanSpace])
  let B := (Fin 0 → AddCircle (1 : ℝ)) × (Fin 0 → ℤ) × Fin 1
  let : Unique B := uniqueOfSubsingleton 0
  let M : ℝ ≃+ ElementaryLieGroup 1 0 0 (Fin 1) :=
    L.toLinearEquiv.toAddEquiv.trans (AddEquiv.prodUnique (M := E) (N := B)).symm
  let M' : Multiplicative ℝ ≃ₜ* Multiplicative (ElementaryLieGroup 1 0 0 (Fin 1)) :=
    ⟨AddEquiv.toMultiplicative M,
      show Continuous (fun x : ℝ ↦ (L x, (default : B))) from
        L.continuous.prodMk continuous_const,
      show Continuous (fun x : E × B ↦ L.symm x.1) from
        L.symm.continuous.comp continuous_fst⟩
  exact ⟨a, ⟨({ realDim := 1, torusDim := 0, latticeRank := 0, finiteFactor := Fin 1, equiv := q.symm.trans M' } : ElementaryLCAPresentation a.quotient)⟩⟩

/-- Along any elementary chart of a real structural quotient, the descended function
is the original function precomposed with a linear projection. -/
private theorem realSmooth_pullback_eq (f : Multiplicative ℝ → ℂ)
    (a : BruhatStructuralPair (Multiplicative ℝ)) (e : ElementaryLCAPresentation a.quotient)
    (f₀ : a.quotient → ℂ) (hf₀ : ∀ x : a.val.1, f₀ (QuotientGroup.mk x) = f x.val)
    (z : Fin e.latticeRank → ℤ) (b : e.finiteFactor) :
    ∃ L : ℝ ≃L[ℝ] EuclideanSpace ℝ (Fin e.realDim),
      (fun xt ↦ f₀ (e.equiv.symm (Multiplicative.ofAdd (elementaryCover xt z b)))) =
        fun xt ↦ (f ∘ Multiplicative.ofAdd) (L.symm xt.1) := by
  obtain ⟨ht, hz, hF, hmem, L, hL⟩ := realSmooth_coordinates a e
  have : IsEmpty (Fin e.torusDim) := by rw [ht]; exact Fin.isEmpty
  have : IsEmpty (Fin e.latticeRank) := by rw [hz]; exact Fin.isEmpty
  have : Subsingleton e.finiteFactor := hF
  refine ⟨L, funext fun xt ↦ ?_⟩
  have htail : elementaryCover xt z b = (xt.1, 0, 0, 0) := by
    apply Prod.ext
    · rfl
    · exact Subsingleton.elim _ _
  rw [htail]
  have hpoint := hL (L.symm xt.1)
  rw [L.apply_symm_apply] at hpoint
  have hmul := congrArg Multiplicative.ofAdd hpoint
  simp only [ofAdd_toAdd] at hmul
  rw [← hmul, e.equiv.symm_apply_apply, hf₀]
  rfl

/-- Paper: Definition D.1.5.3(1), p. 762. On the real additive group, Bruhat
smoothness agrees with ordinary smoothness.
Deviation: Sanity check on the real group. -/
theorem isBruhatSmooth_real_iff (f : Multiplicative ℝ → ℂ) :
    IsBruhatSmooth f ↔ ContDiff ℝ ∞ (f ∘ Multiplicative.ofAdd) := by
  constructor
  · intro hf
    rw [contDiff_infty]
    intro n
    rcases hf n with ⟨k, hk, -, hpair⟩
    have hk0 : k = ⊥ := (isBruhatGoodSubgroup_real_iff k).mp hk
    obtain ⟨a, ⟨e⟩⟩ := realSmooth_stage
    have ha : OrderDual.ofDual a.val.2 = k := by
      rw [hk0]
      exact (isBruhatGoodSubgroup_real_iff _).mp a.property.2.2.1
    obtain ⟨f₀, hf₀, hcover⟩ := hpair a ha
    obtain ⟨L, hEq⟩ := realSmooth_pullback_eq f a e f₀ hf₀ 0 0
    have hfun : f ∘ Multiplicative.ofAdd =
        (fun xt ↦ f₀ (e.equiv.symm (Multiplicative.ofAdd (elementaryCover xt 0 0)))) ∘
          fun x ↦ (L x, (0 : EuclideanSpace ℝ (Fin e.torusDim))) := by
      funext x
      rw [Function.comp_apply, hEq]
      simp [L.symm_apply_apply]
    rw [hfun]
    exact (hcover e 0 0).comp (L.contDiff.prodMk contDiff_const)
  · intro hf n
    refine ⟨⊥, isBruhatGoodSubgroup_real_bot, ?_, ?_⟩
    · intro h x
      rw [Subgroup.mem_bot.mp h.property, one_mul]
    · intro a _ha
      obtain ⟨hmem, q, hquot⟩ := realSmooth_pair_quotient a
      let f₀ : a.quotient → ℂ := fun y ↦ f (q.symm y)
      have hf₀ : ∀ x : a.val.1, f₀ (QuotientGroup.mk x) = f x.val := by
        intro x
        change f (q.symm (QuotientGroup.mk x)) = f x.val
        apply congrArg f
        apply q.injective
        rw [q.apply_symm_apply, hquot x.val]
      refine ⟨f₀, hf₀, fun e z b ↦ ?_⟩
      obtain ⟨L, hEq⟩ := realSmooth_pullback_eq f a e f₀ hf₀ z b
      rw [hEq]
      exact (hf.of_le (by simp)).comp (L.symm.contDiff.comp contDiff_fst)

variable [hTop : IsTopologicalGroup G] [hT2 : T2Space G] [hLC : LocallyCompactSpace G]

/-- An LCA group has a good subgroup. The annihilator of an open compactly generated
subgroup of the dual is compact. Evaluation gives a continuous injection from the quotient
into a group with no small subgroups, so the quotient is locally Euclidean. -/
private theorem exists_bruhatGoodSubgroup : ∃ k : Subgroup G, IsBruhatGoodSubgroup k := by
  obtain ⟨H, _⟩ := (openCompactlyGeneratedSubgroups_colimit (G := PontryaginDual G)).2.1 1
  let k := lcaDualAnnihilator H.val
  have hk := isCompact_lcaDualAnnihilator H.val H.property.1
  refine ⟨k, hk.isClosed, isOpen_lcaAnnihilator k hk, ?_⟩
  let : T1Space (G ⧸ k) := QuotientGroup.t1Space_iff.mpr hk.isClosed
  let r := PontryaginDual.map (⟨H.val.subtype, continuous_subtype_val⟩ : H.val →ₜ* PontryaginDual G)
  let γ := r.comp (pontryaginDual_eval (G := G))
  have hker : γ.toMonoidHom.ker = k := by
    ext x
    rw [MonoidHom.mem_ker, mem_lcaDualAnnihilator_iff]
    exact ⟨fun h χ ↦ congrArg (fun ψ : PontryaginDual H.val ↦ ψ χ) h,
      fun h ↦ PontryaginDual.ext h⟩
  let f : G ⧸ k →ₜ* PontryaginDual H.val :=
    ⟨QuotientGroup.lift k γ.toMonoidHom hker.ge,
      (QuotientGroup.isQuotientMap_mk k).continuous_iff.mpr γ.continuous⟩
  have hf : Function.Injective f :=
    (QuotientGroup.injective_lift_iff k γ.toMonoidHom hker.ge).mpr hker.symm
  obtain ⟨C, _, hC, hGen⟩ := H.property.2
  have hArc : Circle.centeredArc (Real.pi / 2) ∈ 𝓝 (1 : Circle) := by
    simpa using Circle.hasBasis_centeredArc_div_two_pow.mem_of_mem (i := 0) trivial
  let W : Set (PontryaginDual H.val) := {ψ | MapsTo ψ C (Circle.centeredArc (Real.pi / 2))}
  have hW : W ∈ 𝓝 (1 : PontryaginDual H.val) :=
    pontryaginDual_nhds_one_hasBasis.mem_of_mem (i := (C, _)) ⟨hC, hArc⟩
  have hW' : W ∈ 𝓝 (f 1) := by rwa [map_one]
  have hPre : f ⁻¹' W ∈ 𝓝 (1 : G ⧸ k) :=
    f.continuous.continuousAt.preimage_mem_nhds hW'
  have hPow (x : G ⧸ k) (hx : ∀ n : ℕ, x ^ n ∈ f ⁻¹' W) : x = 1 := by
    have hCker : C ⊆ (f x).toMonoidHom.ker := by
      intro χ hχ
      apply MonoidHom.mem_ker.mpr
      apply Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two
      intro n _
      have hn : f (x ^ n) χ ∈ Circle.centeredArc (Real.pi / 2) := hx n hχ
      rw [map_pow] at hn
      exact (ContinuousMonoidHom.pow_apply (f x) n χ) ▸ hn
    have hTop : ⊤ ≤ (f x).toMonoidHom.ker := hGen ▸ (Subgroup.closure_le _).mpr hCker
    apply hf
    rw [map_one]
    exact PontryaginDual.ext fun χ ↦ MonoidHom.mem_ker.mp (hTop (Subgroup.mem_top χ))
  obtain ⟨_, φ, _, hφ⟩ := exists_torusHom_of_noSmallCyclicSubgroups hPre hPow
  obtain ⟨e, _⟩ := lcaQuotientDual_equiv_annihilator k hk.isClosed
  exact isCompactlyGeneratedGroup_of_continuousMulEquiv e
    (isCompactlyGeneratedGroup_dual_of_isLocallyEuclidean
      (isLocallyEuclidean_of_torusHom_discreteKernel φ hφ))

/-- Paper: Definition D.1.5.3(1), p. 762. The zero function is of class Cᵖ. -/
theorem isBruhatContDiff_zero (p : ℕ) : IsBruhatContDiff p (0 : G → ℂ) := by
  obtain ⟨k, hk⟩ := exists_bruhatGoodSubgroup (G := G)
  refine ⟨k, hk, fun _ _ ↦ rfl, fun a _ ↦ ⟨(0 : a.quotient → ℂ), fun _ ↦ rfl, ?_⟩⟩
  intro e z b
  exact contDiff_const

/-- The target of an open continuous map from a real vector group has an elementary
presentation if it is compactly generated. -/
private theorem elementaryPresentation_of_open_vector_map {E B : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CommGroup B] [TopologicalSpace B] [IsTopologicalGroup B] [T2Space B]
    (f : E →+ Additive B) (hf : Continuous f) (hopen : IsOpenMap f)
    (hB : IsCompactlyGeneratedGroup B) : Nonempty (ElementaryLCAPresentation B) := by
  let : T2Space (Additive B) := ‹T2Space B›
  obtain ⟨m, n, ⟨e⟩⟩ := exists_real_torus_equiv_of_open_vector_range f hf hopen
  have hRange : IsOpen (f.range : Set (Additive B)) := by
    rw [AddMonoidHom.coe_range, ← Set.image_univ]
    exact hopen _ isOpen_univ
  let : DivisibleBy f.range ℤ := divisibleByOfSMulRightSurj f.range ℤ (fun {z} hz y ↦ by
    obtain ⟨x, rfl⟩ := f.rangeRestrict_surjective y
    have hzR : (z : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hz
    refine ⟨f.rangeRestrict ((z : ℝ)⁻¹ • x), ?_⟩
    change z • f.rangeRestrict ((z : ℝ)⁻¹ • x) = f.rangeRestrict x
    rw [← map_zsmul, ← Int.cast_smul_eq_zsmul ℝ, smul_smul, mul_inv_cancel₀ hzR, one_smul])
  obtain ⟨split⟩ := exists_continuousAddEquiv_prod_quotient_of_open f.range hRange
  let D := Additive B ⧸ f.range
  let : DiscreteTopology D := QuotientAddGroup.discreteTopology hRange
  let product := split.toAddEquiv.trans (AddEquiv.prodCongr e.toAddEquiv (AddEquiv.refl D))
  let assoc := Homeomorph.prodAssoc (EuclideanSpace ℝ (Fin m)) (Fin n → AddCircle (1 : ℝ)) D
  exact elementaryPresentation_of_compactlyGenerated hB {
    AddEquiv.toMultiplicativeRight (product.trans AddEquiv.prodAssoc) with
    continuous_toFun := assoc.continuous.comp
      ((e.continuous_toFun.prodMap continuous_id).comp split.continuous_toFun)
    continuous_invFun := split.continuous_invFun.comp
      ((e.continuous_invFun.prodMap continuous_id).comp assoc.symm.continuous) }

/-- The cover of the identity component of an elementary group as a homomorphism. -/
private def elementaryCoverZeroHom {m n r : ℕ} {F : Type*} [AddCommGroup F] :
    EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) →+ ElementaryLieGroup m n r F where
  toFun := fun xt ↦ elementaryCover xt 0 0
  map_zero' := Prod.ext rfl (Prod.ext (funext fun _ ↦ AddCircle.coe_zero (1 : ℝ)) rfl)
  map_add' x y := Prod.ext rfl
    (Prod.ext (funext fun i ↦ AddCircle.coe_add (1 : ℝ) (x.2 i) (y.2 i)) (zero_add _).symm)

/-- The cover of the identity component is continuous and open in the elementary group. -/
private theorem elementaryCoverZeroHom_continuous_isOpenMap {m n r : ℕ} {F : Type*}
    [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] :
    let c := elementaryCoverZeroHom (m := m) (n := n) (r := r) (F := F)
    Continuous c ∧ IsOpenMap c := by
  refine ⟨continuous_fst.prodMk
    ((continuous_pi fun i ↦ (AddCircle.continuous_mk' (1 : ℝ)).comp
      ((PiLp.continuous_apply 2 _ i).comp continuous_snd)).prodMk continuous_const), ?_⟩
  let q : (Fin n → ℝ) → (Fin n → AddCircle (1 : ℝ)) := fun u i ↦ (u i : AddCircle (1 : ℝ))
  have hq : IsOpenMap q := IsOpenMap.piMap
    (fun _ ↦ (QuotientAddGroup.isOpenQuotientMap_mk
      (N := AddSubgroup.zmultiples (1 : ℝ))).isOpenMap)
    (Eventually.of_forall fun _ ↦ QuotientAddGroup.mk_surjective)
  have hzero : IsOpenMap (fun _ : Unit ↦ (0 : (Fin r → ℤ) × F)) := fun _ _ ↦ isOpen_discrete _
  have he : IsOpenMap (fun u : EuclideanSpace ℝ (Fin n) ↦
      ((u, ()) : EuclideanSpace ℝ (Fin n) × Unit)) :=
    (Homeomorph.prodUnique _ _).symm.isOpenMap
  exact IsOpenMap.id.prodMap
    (((hq.comp (EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph.isOpenMap).prodMap hzero).comp he)

/-- On a covered discrete fiber, a continuous homomorphism of elementary groups
is represented in the target cover by a continuous affine map. -/
private theorem contDiff_comp_elementaryHom {m n r m' n' r' : ℕ} {F F' : Type*}
    [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F]
    [AddCommGroup F'] [TopologicalSpace F'] [DiscreteTopology F'] [Finite F']
    {p : ℕ∞} (a : ElementaryLieGroup m n r F →+ ElementaryLieGroup m' n' r' F')
    (ha : Continuous a) {f : ElementaryLieGroup m' n' r' F' → ℂ}
    (hf : ∀ z b, ContDiff ℝ p (fun u ↦ f (elementaryCover u z b)))
    (z : Fin r → ℤ) (b : F) :
    ContDiff ℝ p (fun u ↦ f (a (elementaryCover u z b))) := by
  let cover := elementaryCoverZeroHom (m := m) (n := n) (r := r) (F := F)
  let A := a.comp cover
  have hA : Continuous A := ha.comp elementaryCoverZeroHom_continuous_isOpenMap.1
  let R := (AddMonoidHom.fst _ _).comp A
  let T := (AddMonoidHom.fst _ _).comp ((AddMonoidHom.snd _ _).comp A)
  choose l hl using fun i : Fin n' ↦ exists_addCircle_coe_linearMap_eq
    ((Pi.evalAddMonoidHom _ i).comp T) ((continuous_apply i).comp hA.snd.fst)
  let L := (R.toRealLinearMap hA.fst).prod
    ((EuclideanSpace.equiv (Fin n') ℝ).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi l))
  let c := a (elementaryCover 0 z b)
  obtain ⟨t, ht⟩ := elementaryCover_surjective c.2.2.1 c.2.2.2 c.1 c.2.1
  have hLift (u : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) :
      elementaryCover (L u + (c.1, t)) c.2.2.1 c.2.2.2 = a (elementaryCover u z b) := by
    have hshift : cover u + elementaryCover 0 z b = elementaryCover u z b := by
      simp [cover, elementaryCoverZeroHom, elementaryCover, Pi.zero_def]
    rw [← hshift, map_add]
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · funext i
      have hti := congrArg (fun y : ElementaryLieGroup m' n' r' F' ↦ y.2.1 i) ht
      change ((l i u + t i : ℝ) : AddCircle (1 : ℝ)) = (A u).2.1 i + c.2.1 i
      rw [AddCircle.coe_add, hl i u]
      exact congrArg ((A u).2.1 i + ·) hti
    · have h := hA.snd.snd.isConst_of_preconnectedSpace u 0
      rw [map_zero A] at h
      change c.2.2 = (A u).2.2 + c.2.2
      rw [h]
      exact (zero_add _).symm
  simp_rw [← hLift]
  exact (hf c.2.2.1 c.2.2.2).comp (L.contDiff.add (contDiff_const (c := (c.1, t))))

/-- Smooth descents for a good subgroup pull back to structural quotients by
smaller good subgroups. -/
private theorem bruhatContDiff_descend_of_le {p : ℕ} {f : G → ℂ}
    {k : Subgroup G} (hk : IsBruhatGoodSubgroup k)
    (hdesc : ∀ b : BruhatStructuralPair G, OrderDual.ofDual b.val.2 = k →
      ∃ f₀ : b.quotient → ℂ, (∀ x : b.val.1, f₀ (QuotientGroup.mk x) = f x.val) ∧
        ∀ (e : ElementaryLCAPresentation b.quotient)
          (z : Fin e.latticeRank → ℤ) (d : e.finiteFactor),
          ContDiff ℝ (p : ℕ∞) (fun u ↦ f₀ (e.equiv.symm
            (Multiplicative.ofAdd (elementaryCover u z d)))))
    (a : BruhatStructuralPair G) (hak : OrderDual.ofDual a.val.2 ≤ k) :
    ∃ f₀ : a.quotient → ℂ, (∀ x : a.val.1, f₀ (QuotientGroup.mk x) = f x.val) ∧
      ∀ (e : ElementaryLCAPresentation a.quotient)
        (z : Fin e.latticeRank → ℤ) (d : e.finiteFactor),
        ContDiff ℝ (p : ℕ∞) (fun u ↦ f₀ (e.equiv.symm
          (Multiplicative.ofAdd (elementaryCover u z d)))) := by
  have hkc := isCompact_lcaDualAnnihilator (lcaAnnihilator k) hk.2.1
  rw [lcaDualAnnihilator_annihilator k hk.1] at hkc
  obtain ⟨J, hkJ⟩ := exists_openCompactlyGeneratedSubgroup_contains hkc
  obtain ⟨H, haH, hJH⟩ := (openCompactlyGeneratedSubgroups_colimit (G := G)).1.directed
    ⟨a.val.1, a.property.1, a.property.2.1⟩ J
  let b : BruhatStructuralPair G :=
    ⟨(H.val, OrderDual.toDual k), H.property.1, H.property.2, hk, hkJ.trans hJH⟩
  let i := Subgroup.inclusion (show a.val.1 ≤ H.val from haH)
  let j : a.quotient →* b.quotient := QuotientGroup.map _ _ i (fun _ hx ↦ hak hx)
  have hi : Continuous i := (continuous_subtype_val : Continuous ((↑) : a.val.1 → G)).subtype_mk _
  have hj : Continuous j := (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
    (QuotientGroup.continuous_mk.comp hi)
  have hio : IsOpenMap i := a.property.1.isOpenMap_inclusion haH
  have hjo : IsOpenMap j := by
    intro U hU
    let qa : a.val.1 → a.quotient := QuotientGroup.mk
    let qb : b.val.1 → b.quotient := QuotientGroup.mk
    have hEq : j '' U = (qb ∘ i) '' (qa ⁻¹' U) := by
      rw [show qb ∘ i = j ∘ qa from rfl, Set.image_comp,
        Set.image_preimage_eq _ QuotientGroup.mk_surjective]
    rw [hEq]
    exact (QuotientGroup.isOpenQuotientMap_mk.isOpenMap.comp hio) _
      (hU.preimage QuotientGroup.continuous_mk)
  obtain ⟨f₀, hf₀, hSmooth⟩ := hdesc b rfl
  refine ⟨f₀ ∘ j, fun x ↦ hf₀ (i x), ?_⟩
  intro e z d
  -- The image of the identity-component cover is open in the larger quotient.
  let c := elementaryCoverZeroHom (m := e.realDim) (n := e.torusDim) (r := e.latticeRank)
    (F := e.finiteFactor)
  let j' := MonoidHom.toAdditiveRight (j.comp e.equiv.symm.toMulEquiv.toMonoidHom)
  have hContinuous : Continuous (j'.comp c) :=
    hj.comp (e.equiv.symm.continuous.comp elementaryCoverZeroHom_continuous_isOpenMap.1)
  have hOpen : IsOpenMap (j'.comp c) :=
    hjo.comp (e.equiv.symm.toHomeomorph.isOpenMap.comp
      elementaryCoverZeroHom_continuous_isOpenMap.2)
  have hkClosed : IsClosed ((k.comap b.val.1.subtype : Subgroup b.val.1) : Set b.val.1) :=
    hk.1.preimage continuous_subtype_val
  let : LocallyCompactSpace H.val := H.property.1.isOpenEmbedding_subtypeVal.locallyCompactSpace
  let : T1Space b.quotient := QuotientGroup.t1Space_iff.mpr hkClosed
  obtain ⟨e'⟩ := elementaryPresentation_of_open_vector_map (j'.comp c) hContinuous hOpen
    (isCompactlyGeneratedGroup_quotient H.property.2 _ hkClosed)
  let L := AddMonoidHom.toMultiplicative.symm
    (e'.equiv.toMulEquiv.toMonoidHom.comp (j.comp e.equiv.symm.toMulEquiv.toMonoidHom))
  have hL : Continuous L := e'.equiv.continuous.comp (hj.comp e.equiv.symm.continuous)
  let φ := fun y ↦ f₀ (e'.equiv.symm (Multiplicative.ofAdd y))
  have hs := contDiff_comp_elementaryHom L hL (f := φ) (hSmooth e') z d
  convert hs using 1
  funext u
  change f₀ (j (e.equiv.symm _)) = f₀ (e'.equiv.symm (e'.equiv (j (e.equiv.symm _))))
  rw [e'.equiv.symm_apply_apply]

/-- Paper: Definition D.1.5.3(1), p. 762. The sum of two functions of class Cᵖ
is of class Cᵖ. -/
theorem IsBruhatContDiff.add {p : ℕ} {f g : G → ℂ}
    (hf : IsBruhatContDiff p f) (hg : IsBruhatContDiff p g) :
    IsBruhatContDiff p (f + g) := by
  obtain ⟨k, hk, hfk, hfd⟩ := hf
  obtain ⟨l, hl, hgl, hgd⟩ := hg
  refine ⟨k ⊓ l, isBruhatGoodSubgroup_inf hk hl, ?_, ?_⟩
  · intro h x
    exact congrArg₂ (· + ·) (hfk ⟨h, h.property.1⟩ x) (hgl ⟨h, h.property.2⟩ x)
  · intro a ha
    obtain ⟨f₀, hf₀, hfSmooth⟩ := bruhatContDiff_descend_of_le hk hfd a (ha ▸ inf_le_left)
    obtain ⟨g₀, hg₀, hgSmooth⟩ := bruhatContDiff_descend_of_le hl hgd a (ha ▸ inf_le_right)
    exact ⟨f₀ + g₀, fun x ↦ congrArg₂ (· + ·) (hf₀ x) (hg₀ x),
      fun e z d ↦ (hfSmooth e z d).add (hgSmooth e z d)⟩

/-- Paper: Definition D.1.5.3(1), p. 762. A complex scalar multiple of a function
of class Cᵖ is of class Cᵖ. -/
theorem IsBruhatContDiff.smul {p : ℕ} {f : G → ℂ}
    (hf : IsBruhatContDiff p f) (z : ℂ) : IsBruhatContDiff p (z • f) := by
  obtain ⟨k, hk, hInv, hDescend⟩ := hf
  refine ⟨k, hk, fun h x ↦ congrArg (z • ·) (hInv h x), ?_⟩
  intro a ha
  obtain ⟨f₀, hf₀, hSmooth⟩ := hDescend a ha
  exact ⟨z • f₀, fun x ↦ congrArg (z • ·) (hf₀ x),
    fun e l b ↦ (hSmooth e l b).const_smul z⟩

/-- Paper: Definition D.1.5.3(1), p. 762. The Cᵖ functions form a complex vector
subspace of the functions on G. -/
def bruhatContDiffSubmodule (p : ℕ) : Submodule ℂ (G → ℂ) where
  carrier := {f | IsBruhatContDiff p f}
  zero_mem' := isBruhatContDiff_zero p
  add_mem' hf hg := hf.add hg
  smul_mem' z _ hf := hf.smul z

/-- Paper: Definition D.1.5.3(1), p. 762. The smooth functions are the
intersection of the Cᵖ subspaces over all finite orders. -/
def bruhatSmoothSubmodule : Submodule ℂ (G → ℂ) :=
  ⨅ p : ℕ, bruhatContDiffSubmodule p

/-- Paper: Definition D.1.5.3(1), p. 762. Membership in the Cᵖ submodule is
equivalent to the stated Bruhat differentiability condition. -/
theorem mem_bruhatContDiffSubmodule_iff (p : ℕ) (f : G → ℂ) :
    f ∈ bruhatContDiffSubmodule p ↔ IsBruhatContDiff p f := Iff.rfl

/-- Paper: Definition D.1.5.3(1), p. 762. Membership in the smooth submodule
means Bruhat differentiability at every finite order. -/
theorem mem_bruhatSmoothSubmodule_iff (f : G → ℂ) :
    f ∈ bruhatSmoothSubmodule ↔ IsBruhatSmooth f := by
  simp only [bruhatSmoothSubmodule, Submodule.mem_iInf]
  rfl

omit hTop hT2 hLC

/-- Paper: Definition D.1.5.3(2), p. 762. In an elementary presentation, a stage
is the existing elementary Schwartz space with its seminorm topology. -/
abbrev SchwartzBruhatStage {A : Type*} [CommGroup A] [TopologicalSpace A]
    (e : ElementaryLCAPresentation A) :=
  ElementarySchwartz e.realDim e.torusDim e.latticeRank e.finiteFactor

open Classical in
/-- Paper: Definition D.1.5.3(2), p. 762. A stage function is pulled back along
the quotient and extended by zero outside the open subgroup.
Deviation: The printed composition is reversed and omits restriction to the open subgroup. -/
def schwartzBruhatStageRealization (a : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation a.quotient) : SchwartzBruhatStage e →ₗ[ℂ] (G → ℂ) :=
  (LinearMap.pi fun x : G ↦
    if hx : x ∈ a.val.1 then
      LinearMap.proj (Multiplicative.toAdd (e.equiv (QuotientGroup.mk ⟨x, hx⟩)))
    else 0).comp (elementarySchwartzSubmodule e.realDim e.torusDim e.latticeRank
      e.finiteFactor).subtype

open Classical in
/-- Paper: Definition D.1.5.3(2), p. 762. The realization evaluates a stage
function at the quotient coordinate on the open subgroup and vanishes outside it. -/
theorem schwartzBruhatStageRealization_apply (a : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation a.quotient) (f : SchwartzBruhatStage e) (x : G) :
    schwartzBruhatStageRealization a e f x =
      if hx : x ∈ a.val.1 then
        f (Multiplicative.toAdd (e.equiv (QuotientGroup.mk ⟨x, hx⟩)))
      else 0 := by
  unfold schwartzBruhatStageRealization
  erw [LinearMap.comp_apply, LinearMap.pi_apply]
  split_ifs <;> rfl

section StageTransitions

open scoped ENNReal NNReal

/-- A stage function is determined by its realization because every elementary coordinate
is represented by a point in the open subgroup. -/
private theorem schwartzBruhatStageRealization_injective (a : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation a.quotient) :
    Function.Injective (schwartzBruhatStageRealization a e) := by
  classical
  intro f g hfg
  apply Subtype.ext
  funext z
  obtain ⟨q, hq⟩ := e.equiv.surjective (Multiplicative.ofAdd z)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  have h := congrFun hfg x.val
  change schwartzBruhatStageRealization a e f x.val = schwartzBruhatStageRealization a e g x.val at h
  simpa only [schwartzBruhatStageRealization_apply, dite_eq_left x.property, hq,
    toAdd_ofAdd] using h

/-- A realized stage function is constant on cosets of its kernel. -/
private theorem stage_realization_mul_kernel (a : BruhatStructuralPair G)
    (d : ElementaryLCAPresentation a.quotient) (s : SchwartzBruhatStage d)
    {g : G} (hg : g ∈ OrderDual.ofDual a.val.2) (x : G) :
    schwartzBruhatStageRealization a d s (g * x) = schwartzBruhatStageRealization a d s x := by
  classical
  have hh := a.property.2.2.2 hg
  simp only [schwartzBruhatStageRealization_apply, a.val.1.mul_mem_cancel_left hh]
  split_ifs with hx
  · let u : a.val.1 := ⟨g, hh⟩
    let v : a.val.1 := ⟨x, hx⟩
    have hu := (a.quotient_mk_eq_one u).mpr hg
    have huv : (QuotientGroup.mk (u * v) : a.quotient) = QuotientGroup.mk v := by
      rw [QuotientGroup.mk_mul, hu, one_mul]
    exact congrArg (fun q : a.quotient ↦ s (d.equiv q).toAdd) huv
  · rfl

/-- The zero-weight stage seminorm bounds every point of the realization. -/
private theorem norm_stage_realization_le (a : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation a.quotient) (f : SchwartzBruhatStage e) (x : G) :
    ‖schwartzBruhatStageRealization a e f x‖ ≤ elementarySchwartzSeminorm (0, 0, 0, 0) f := by
  rw [schwartzBruhatStageRealization_apply]
  split_ifs
  · change (‖f _‖₊ : ENNReal).toReal ≤ (elementarySchwartzBound f.val (0, 0, 0, 0)).toReal
    apply ENNReal.toReal_mono (f.property.2 _).ne
    rw [elementarySchwartzBound_zero]
    exact le_iSup (fun y ↦ (‖f y‖₊ : ENNReal)) _
  · exact norm_zero.trans_le (apply_nonneg _ _)

/-- Point evaluation on an elementary Schwartz stage is continuous by the
zero-order, zero-weight seminorm. -/
private theorem continuous_schwartzBruhatStage_eval
    (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient) (x : G) :
    Continuous (fun f : SchwartzBruhatStage e ↦ schwartzBruhatStageRealization a e f x) := by
  let L := (LinearMap.proj x).comp (schwartzBruhatStageRealization a e)
  refine (norm_withSeminorms ℂ ℂ).continuous_of_continuous_comp L fun _ ↦ ?_
  apply Seminorm.continuous_of_le (elementarySchwartz_withSeminorms.continuous_seminorm (0, 0, 0, 0))
  exact fun f ↦ norm_stage_realization_le a e f x

/-- Evaluation of a higher derivative on fixed vectors is a fixed finite
linear combination of coordinate partials. -/
private theorem elementary_iterated_expansion {m n r k : ℕ} {F : Type*}
    (v : Fin k → EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) :
    ∃ (s : Finset ((Fin m → ℕ) × (Fin n → ℕ))) (c : ((Fin m → ℕ) × (Fin n → ℕ)) → ℝ),
      ∀ (f : ElementaryLieGroup m n r F → ℂ) a b,
      ContDiff ℝ ∞ (fun x ↦ f (elementaryCover x a b)) → ∀ x,
        iteratedFDeriv ℝ k (fun z ↦ f (elementaryCover z a b)) x v =
          ∑ p ∈ s, c p • elementaryPartial f p.1 p.2 x a b := by
  classical
  let X := EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
  let J := Fin m ⊕ Fin n
  let B : Module.Basis J ℝ X :=
    (EuclideanSpace.basisFun (Fin m) ℝ).toBasis.prod (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let dirs (b : Fin m → ℕ) (g : Fin n → ℕ) : List J :=
    (List.ofFn fun i ↦ List.replicate (b i) (Sum.inl i)).flatten ++
      (List.ofFn fun i ↦ List.replicate (g i) (Sum.inr i)).flatten
  have hdirs (b : Fin m → ℕ) (g : Fin n → ℕ) :
      (dirs b g).map B =
        (List.ofFn fun i ↦ List.replicate (b i) (EuclideanSpace.single i 1, 0)).flatten ++
        (List.ofFn fun i ↦ List.replicate (g i) (0, EuclideanSpace.single i 1)).flatten := by
    have hInl (i : Fin m) : B (.inl i) = (EuclideanSpace.single i 1, 0) := by
      dsimp only [B]
      rw [Module.Basis.prod_apply]
      simp only [Sum.elim_inl, Function.comp_apply, OrthonormalBasis.coe_toBasis,
        EuclideanSpace.basisFun_apply, LinearMap.inl_apply]
    have hInr (i : Fin n) : B (.inr i) = (0, EuclideanSpace.single i 1) := by
      dsimp only [B]
      rw [Module.Basis.prod_apply]
      simp only [Sum.elim_inr, Function.comp_apply, OrthonormalBasis.coe_toBasis,
        EuclideanSpace.basisFun_apply, LinearMap.inr_apply]
    simp only [dirs, List.map_append, List.map_flatten, List.map_ofFn, Function.comp_def,
      List.map_replicate, hInl, hInr]
  have hpartial (f : ElementaryLieGroup m n r F → ℂ) (a : Fin r → ℤ) (b : F)
      (d : Fin m → ℕ) (e : Fin n → ℕ) (x : X) :
      elementaryPartial f d e x a b =
        iteratedFDeriv ℝ (dirs d e).length (fun z ↦ f (elementaryCover z a b)) x
          (fun i ↦ B ((dirs d e).get i)) := by
    dsimp only [elementaryPartial]
    rw [← hdirs d e]
    have hlength (k : ℕ) (hk : k = (dirs d e).length) :
        iteratedFDeriv ℝ k (fun z ↦ f (elementaryCover z a b)) x
          (fun i ↦ B ((dirs d e).get (Fin.cast hk i))) =
          iteratedFDeriv ℝ (dirs d e).length (fun z ↦ f (elementaryCover z a b)) x
            (fun i ↦ B ((dirs d e).get i)) := by
      subst k
      rfl
    have hlen : ((dirs d e).map B).length = (dirs d e).length := List.length_map B
    have hget : ((dirs d e).map B).get =
        fun i ↦ B ((dirs d e).get (Fin.cast hlen i)) := by
      funext i
      simp only [List.get_eq_getElem, List.getElem_map, Fin.val_cast]
    rw [hget]
    exact hlength _ hlen
  let T := Fin k → J
  let indices (t : T) : (Fin m → ℕ) × (Fin n → ℕ) :=
    (fun i ↦ (List.ofFn t).count (.inl i), fun j ↦ (List.ofFn t).count (.inr j))
  let coeff (t : T) := ∏ i, B.repr (v i) (t i)
  let s := Finset.univ.image indices
  refine ⟨s, fun p ↦ ∑ t ∈ Finset.univ.filter (fun t ↦ indices t = p), coeff t, ?_⟩
  intro f a' b' hf x
  let f₀ : X → ℂ := fun z ↦ f (elementaryCover z a' b')
  let D := iteratedFDeriv ℝ k f₀ x
  have hPerm (t : T) : (List.ofFn t).Perm (dirs (indices t).1 (indices t).2) := by
    apply List.perm_iff_count.mpr
    intro j
    cases j with
    | inl i =>
      simp [dirs, indices, List.count_flatten, List.map_ofFn, List.count_replicate, List.sum_ofFn]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        exact ite_eq_right (fun h ↦ hj (Sum.inl.inj h))
      · simp
    | inr i =>
      simp [dirs, indices, List.count_flatten, List.map_ofFn, List.count_replicate, List.sum_ofFn]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        exact ite_eq_right (fun h ↦ hj (Sum.inr.inj h))
      · simp
  have hterm (t : T) : D (fun i ↦ B (t i)) =
      elementaryPartial f (indices t).1 (indices t).2 x a' b' := by
    rw [hpartial]
    have hlength (n : ℕ) (hk : n = k) :
        iteratedFDeriv ℝ n f₀ x (fun i ↦ B (t (Fin.cast hk i))) =
          D (fun i ↦ B (t i)) := by
      subst n
      rfl
    rw [← hlength _ List.length_ofFn]
    simpa only [f₀, List.get_ofFn] using
      iteratedFDeriv_apply_list_perm hf B (hPerm t) x
  change D.toMultilinearMap v = _
  conv_lhs => rw [show v = (fun i ↦ ∑ j, B.repr (v i) j • B j) from
    funext fun i ↦ (B.sum_repr (v i)).symm]
  rw [D.toMultilinearMap.map_sum]
  simp_rw [D.toMultilinearMap.map_smul_univ, ContinuousMultilinearMap.coe_coe,
    hterm, Finset.sum_smul]
  rw [← Finset.sum_fiberwise_of_maps_to (t := s)
    (fun t _ ↦ Finset.mem_image_of_mem indices (Finset.mem_univ t))]
  refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun t ht ↦ ?_
  rw [(Finset.mem_filter.mp ht).2]
  rfl

include hTop hT2 hLC in
/-- A good subgroup is compact by double annihilation. -/
private theorem compact_bruhat_kernel (a : BruhatStructuralPair G) :
    IsCompact ((OrderDual.ofDual a.val.2 : Subgroup G) : Set G) := by
  let k := OrderDual.ofDual a.val.2
  change IsCompact (k : Set G)
  rw [← lcaDualAnnihilator_annihilator k a.property.2.2.1.1]
  exact isCompact_lcaDualAnnihilator _ a.property.2.2.1.2.1

/-- A compact group has no nontrivial continuous additive real coordinate. -/
private theorem compact_hom_real_zero {K : Type*} [AddGroup K] [TopologicalSpace K]
    [CompactSpace K] (f : K →+ ℝ) (hf : Continuous f) (x : K) : f x = 0 := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp (isCompact_range hf).isBounded
  by_contra hx
  have hpos := norm_pos_iff.mpr hx
  obtain ⟨n, hn⟩ := exists_nat_gt (C / ‖f x‖)
  have hb := hC _ (mem_range_self (n • x))
  rw [map_nsmul, nsmul_eq_mul, norm_mul, Real.norm_natCast] at hb
  exact (not_lt_of_ge hb) ((div_lt_iff₀ hpos).mp hn)

/-- An open quotient onto an elementary group has a linear lift of its vector
cover when the source is a vector space. -/
private theorem elementary_linear_section {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m n r : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
    (φ : E →+ ElementaryLieGroup m n r F) (hc : Continuous φ) (ho : IsOpenMap φ) :
    ∃ L : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) →L[ℝ] E,
      ∀ x, φ (L x) = elementaryCover x 0 0 := by
  let X := EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
  let B := ElementaryLieGroup m n r F
  let q : X →+ B := elementaryCoverZeroHom
  let R := (AddMonoidHom.fst _ _).comp φ
  let T := (AddMonoidHom.fst _ _).comp ((AddMonoidHom.snd _ _).comp φ)
  choose l hl using fun i : Fin n ↦ exists_addCircle_coe_linearMap_eq
    ((Pi.evalAddMonoidHom _ i).comp T) ((continuous_apply i).comp hc.snd.fst)
  let A : E →L[ℝ] X := (R.toRealLinearMap hc.fst).prod
    ((EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap.comp (ContinuousLinearMap.pi l))
  have hcomp (u : E) : q (A u) = φ u := by
    refine Prod.ext rfl (Prod.ext (funext fun i ↦ hl i u) ?_)
    have h := hc.snd.snd.isConst_of_preconnectedSpace 0 u
    rw [map_zero] at h
    exact h
  let U : Set X := {x | ∀ i, x.2 i ∈ Ioo (-(1/2 : ℝ)) (1/2)}
  have hU : IsOpen U := by
    rw [show U = ⋂ i : Fin n, (fun x : X ↦ x.2 i) ⁻¹' Ioo (-(1/2 : ℝ)) (1/2) from
      Set.ext fun x ↦ by simp only [U, mem_ofPred_eq, mem_iInter, mem_preimage]]
    exact isOpen_iInter_of_finite fun i ↦ isOpen_Ioo.preimage ((PiLp.continuous_apply 2 _ i).comp continuous_snd)
  have h0 : (0 : X) ∈ U := fun _ ↦ by change (-(1/2 : ℝ)) < 0 ∧ (0 : ℝ) < 1/2; norm_num
  have hinj : InjOn q U := by
    intro x hx y hy h
    refine Prod.ext (congrArg (fun z : B ↦ z.1) h) (by
      ext j
      apply AddCircle.injOn_coe_Ico (1 : ℝ) (-(1/2 : ℝ)) _ _ (congrArg (fun g : B ↦ g.2.1 j) h)
      · exact ⟨(hx j).1.le, (hx j).2.trans_le (by norm_num)⟩
      · exact ⟨(hy j).1.le, (hy j).2.trans_le (by norm_num)⟩)
  let W := φ '' (A ⁻¹' U)
  have hW := ho _ (hU.preimage A.continuous)
  have hW0 : q 0 ∈ W := ⟨0, by simpa only [mem_preimage, map_zero] using h0, by simp⟩
  have hnh : ((LinearMap.range A.toLinearMap : Submodule ℝ X) : Set X) ∈ 𝓝 0 := by
    refine mem_of_superset (inter_mem (hU.mem_nhds h0)
      (((elementaryCoverZeroHom_continuous_isOpenMap (m := m) (n := n) (r := r) (F := F)).1).continuousAt.preimage_mem_nhds
        (hW.mem_nhds hW0))) ?_
    intro x hx
    obtain ⟨u, hu, he⟩ := hx.2
    exact ⟨u, hinj hu hx.1 ((hcomp u).trans he)⟩
  obtain ⟨L, hL⟩ := A.toLinearMap.exists_rightInverse_of_surjective
    (A.toLinearMap.range.eq_top_of_nonempty_interior' ⟨0, mem_interior_iff_mem_nhds.mpr hnh⟩)
  refine ⟨⟨L, L.continuous_of_finiteDimensional⟩, fun x ↦ ?_⟩
  exact (hcomp (L x)).symm.trans (congrArg q (DFunLike.congr_fun hL x))

/-- An affine lift on every discrete fibre uses the same linear part. -/
private theorem elementary_open_quotient_charts {m n r m' n' r' : ℕ} {F F' : Type}
    [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
    [AddCommGroup F'] [TopologicalSpace F'] [DiscreteTopology F'] [Finite F']
    (H : AddSubgroup (ElementaryLieGroup m n r F)) (hH : IsOpen (H : Set (ElementaryLieGroup m n r F)))
    (φ : H →+ ElementaryLieGroup m' n' r' F') (hc : Continuous φ) (ho : IsOpenMap φ)
    (hs : Function.Surjective φ) :
    ∃ L : (EuclideanSpace ℝ (Fin m') × EuclideanSpace ℝ (Fin n')) →L[ℝ]
        (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)),
      ∀ a b, ∃ y a' b', ∀ x, ∃ w : H, w.val = elementaryCover (L x + y) a' b' ∧
        φ w = elementaryCover x a b := by
  let q := elementaryCoverZeroHom (m := m) (n := n) (r := r) (F := F)
  have hq := elementaryCoverZeroHom_continuous_isOpenMap (m := m) (n := n) (r := r) (F := F)
  have hmem (x) : q x ∈ H := by
    have he := ((show IsClopen (H : Set (ElementaryLieGroup m n r F)) from ⟨H.isClosed_of_isOpen hH, hH⟩).preimage hq.1).eq_univ
      (show (q ⁻¹' (H : Set (ElementaryLieGroup m n r F))).Nonempty from ⟨0, by simp [q]⟩)
    exact eq_univ_iff_forall.mp he x
  let j := q.codRestrict H hmem
  have hj : Continuous j := hq.1.subtype_mk _
  have hjOpen : IsOpenMap j := by
    intro U hU
    rw [show j '' U = Subtype.val ⁻¹' (q '' U) from Set.ext fun w ↦
      ⟨fun ⟨x, hx, h⟩ ↦ ⟨x, hx, congrArg Subtype.val h⟩,
        fun ⟨x, hx, h⟩ ↦ ⟨x, hx, Subtype.ext h⟩⟩]
    exact (hq.2 U hU).preimage continuous_subtype_val
  obtain ⟨L, hL⟩ := elementary_linear_section (φ.comp j) (hc.comp hj) (ho.comp hjOpen)
  refine ⟨L, fun a b ↦ ?_⟩
  obtain ⟨w, hw⟩ := hs (elementaryCover 0 a b)
  obtain ⟨t, ht⟩ := elementaryCover_surjective w.val.2.2.1 w.val.2.2.2 w.val.1 w.val.2.1
  refine ⟨(w.val.1, t), w.val.2.2.1, w.val.2.2.2, fun x ↦ ⟨j (L x) + w, ?_, ?_⟩⟩
  · change q (L x) + w.val = _
    conv_lhs => rw [← show elementaryCover (w.val.1,t) w.val.2.2.1 w.val.2.2.2 = w.val from ht]
    refine Prod.ext rfl (Prod.ext (funext fun i ↦ (AddCircle.coe_add _ _ _).symm) (zero_add _))
  · rw [map_add, show φ (j (L x)) = _ from hL x, hw]
    simp [elementaryCover, Pi.zero_def]

/-- A partial after an affine lift between two vector covers is a fixed finite
linear combination of partials in the source elementary group. -/
private theorem elementaryPartial_comp_lift {m n r m' n' r' : ℕ} {F F' : Type*}
    (L : (EuclideanSpace ℝ (Fin m') × EuclideanSpace ℝ (Fin n')) →L[ℝ]
      (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)))
    (β : Fin m' → ℕ) (γ : Fin n' → ℕ) :
    ∃ (s : Finset ((Fin m → ℕ) × (Fin n → ℕ)))
      (c : ((Fin m → ℕ) × (Fin n → ℕ)) → ℝ),
      ∀ (f : ElementaryLieGroup m n r F → ℂ) (h : ElementaryLieGroup m' n' r' F' → ℂ) y a b a' b',
        ContDiff ℝ ∞ (fun x ↦ f (elementaryCover x a' b')) →
        (∀ x, h (elementaryCover x a b) = f (elementaryCover (L x + y) a' b')) →
        ∀ x, elementaryPartial h β γ x a b =
          ∑ p ∈ s, c p • elementaryPartial f p.1 p.2 (L x + y) a' b' := by
  let X := EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
  let l : List (EuclideanSpace ℝ (Fin m') × EuclideanSpace ℝ (Fin n')) :=
    (List.ofFn (fun i : Fin m' ↦ List.replicate (β i) (EuclideanSpace.single i 1, 0))).flatten ++
    (List.ofFn (fun i : Fin n' ↦ List.replicate (γ i) (0, EuclideanSpace.single i 1))).flatten
  obtain ⟨T, c, hT⟩ := elementary_iterated_expansion (r := r) (F := F) (fun i ↦ L (l.get i))
  refine ⟨T, c, fun f h y a b a' b' hf he x ↦ ?_⟩
  let f₀ : X → ℂ := fun z ↦ f (elementaryCover z a' b')
  change iteratedFDeriv ℝ l.length (fun z ↦ h (elementaryCover z a b)) x l.get = _
  rw [show (fun z ↦ h (elementaryCover z a b)) = (fun z ↦ f₀ (z + y)) ∘ L from funext he,
    L.iteratedFDeriv_comp_right
      (show ContDiff ℝ ∞ (fun z : X ↦ f₀ (z + y)) from hf.comp (contDiff_id.add contDiff_const))
      x (by simp),
    ContinuousMultilinearMap.compContinuousLinearMap_apply, iteratedFDeriv_comp_add_right]
  exact hT f a' b' hf (L x + y)

/-- A continuous real character in additive coordinates is a linear polynomial
in the real and integer coordinates of an elementary group. -/
private theorem elementary_real_hom_polynomial {m n r : ℕ} {F : Type*} [AddCommGroup F]
    [TopologicalSpace F] [DiscreteTopology F] [Finite F]
    (h : ElementaryLieGroup m n r F →+ ℝ) (hh : Continuous h) :
    ∃ p : MvPolynomial (Fin m ⊕ Fin r) ℂ, ∀ g : ElementaryLieGroup m n r F,
      MvPolynomial.eval (Sum.elim (fun i ↦ (g.1 i : ℂ)) (fun j ↦ (g.2.2.1 j : ℂ))) p =
        (h g : ℂ) := by
  classical
  let V := EuclideanSpace ℝ (Fin m)
  let Z := Fin r → ℤ
  let K := (Fin n → AddCircle (1 : ℝ)) × F
  let G := ElementaryLieGroup m n r F
  let J := Fin m ⊕ Fin r
  let eR : V →+ G :=
    ⟨⟨fun x ↦ (x, 0, 0, 0), rfl⟩, fun _ _ ↦
      Prod.ext rfl (Prod.ext (zero_add _).symm (Prod.ext (zero_add _).symm (zero_add _).symm))⟩
  let eZ : Z →+ G :=
    ⟨⟨fun a ↦ (0, 0, a, 0), rfl⟩, fun _ _ ↦
      Prod.ext (zero_add _).symm (Prod.ext (zero_add _).symm (Prod.ext rfl (zero_add _).symm))⟩
  let eK : K →+ G :=
    ⟨⟨fun z ↦ (0, z.1, 0, z.2), rfl⟩, fun _ _ ↦
      Prod.ext (zero_add _).symm (Prod.ext rfl (Prod.ext (zero_add _).symm rfl))⟩
  let e (j : J) : G := Sum.elim
    (fun i ↦ eR (EuclideanSpace.single i 1)) (fun i ↦ eZ (Pi.single i 1)) j
  let coord (j : J) : G →+ ℝ := Sum.elim
    (fun i : Fin m ↦
      ⟨⟨fun g : G ↦ g.1 i, rfl⟩, fun _ _ ↦ rfl⟩)
    (fun i : Fin r ↦
      (Int.castAddHom ℝ).comp ⟨⟨fun g : G ↦ g.2.2.1 i, rfl⟩, fun _ _ ↦ rfl⟩) j
  have hcoord (j : J) : Continuous (coord j) := by
    cases j with
    | inl i => exact (PiLp.continuous_apply 2 _ i).comp continuous_fst
    | inr i =>
      exact (continuous_of_discreteTopology (f := fun z : ℤ ↦ (z : ℝ))).comp
        ((continuous_apply i).comp continuous_snd.snd.fst)
  have hlinear (h : G →+ ℝ) (hh : Continuous h) (g : G) :
      h g = ∑ j, coord j g * h (e j) := by
    let : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
    let hK := h.comp eK
    have hKcont : Continuous hK :=
      hh.comp (continuous_const.prodMk (continuous_fst.prodMk
        (continuous_const.prodMk continuous_snd)))
    have hvanish (z : K) : hK z = 0 := compact_hom_real_zero hK hKcont z
    let hR := (h.comp eR).toRealLinearMap (hh.comp (continuous_id.prodMk continuous_const))
    let basisR := (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
    let basisZ := Pi.basisFun ℤ (Fin r)
    have hr (x : V) : h (eR x) = ∑ i, x i * h (eR (EuclideanSpace.single i 1)) := by
      have he := congrArg hR (basisR.sum_repr x)
      simpa [hR, basisR, smul_eq_mul] using he.symm
    have hz (a : Z) : h (eZ a) = ∑ i, (a i : ℝ) * h (eZ (Pi.single i 1)) := by
      have he := congrArg (h.comp eZ) (basisZ.sum_repr a)
      rw [map_sum] at he
      simp_rw [map_zsmul, zsmul_eq_mul] at he
      simpa [basisZ] using he.symm
    rcases g with ⟨x, z, a, b⟩
    have hdecomp : (x, z, a, b) = eR x + eZ a + eK (z, b) := by
      change (x, z, a, b) = ((x + 0) + 0, (0 + 0) + z, (0 + a) + 0, (0 + 0) + b)
      simp
    have hKzero : h (eK (z, b)) = 0 := hvanish (z, b)
    rw [Fintype.sum_sum_type]
    change h (x, z, a, b) =
      (∑ i, x i * h (eR (EuclideanSpace.single i 1))) +
        ∑ i, (a i : ℝ) * h (eZ (Pi.single i 1))
    rw [hdecomp, map_add, map_add, hKzero, add_zero, hr, hz]
  refine ⟨∑ k, MvPolynomial.C ((h (e k) : ℝ) : ℂ) * MvPolynomial.X k, fun g ↦ ?_⟩
  rw [hlinear h hh g]
  simp only [map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, Complex.ofReal_sum, Complex.ofReal_mul]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  cases k with
  | inl i => exact mul_comm _ _
  | inr i => rw [mul_comm]; exact congrArg (· * _) (Complex.ofReal_intCast _).symm

/-- A real-valued additive character on an open subgroup extends across the
discrete quotient, preserving continuity. -/
private theorem extend_real_hom_open {A : Type} [AddCommGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] (H : AddSubgroup A) (hH : IsOpen (H : Set A))
    (f : H →+ ℝ) (hf : Continuous f) : ∃ l : A →+ ℝ, Continuous l ∧ ∀ w : H, l w.val = f w := by
  let : Module.Injective ℤ ℝ := (Module.Baer.of_divisible ℝ).injective
  obtain ⟨l, hl⟩ := Module.Injective.out H.subtype.toIntLinearMap Subtype.val_injective f.toIntLinearMap
  refine ⟨l.toAddMonoidHom, ?_, fun w ↦ hl w⟩
  refine continuous_of_continuousAt_zero l.toAddMonoidHom (ContinuousOn.continuousAt ?_ (hH.mem_nhds H.zero_mem))
  rw [continuousOn_iff_continuous_domRestrict]
  exact hf.congr fun w ↦ (hl w).symm

/-- On the open subgroup every target monomial agrees with a polynomial in
the ambient real and lattice coordinates. -/
private theorem elementary_open_quotient_weight {m n r m' n' r' : ℕ} {F F' : Type}
    [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
    [AddCommGroup F'] [TopologicalSpace F'] [DiscreteTopology F'] [Finite F']
    (H : AddSubgroup (ElementaryLieGroup m n r F)) (hH : IsOpen (H : Set (ElementaryLieGroup m n r F)))
    (φ : H →+ ElementaryLieGroup m' n' r' F') (hc : Continuous φ)
    (α : Fin m' → ℕ) (δ : Fin r' → ℕ) :
    ∃ p : MvPolynomial (Fin m ⊕ Fin r) ℂ, ∀ w : H,
      MvPolynomial.eval (Sum.elim (fun i ↦ (w.val.1 i : ℂ)) (fun j ↦ (w.val.2.2.1 j : ℂ))) p =
        (∏ i, ((φ w).1 i : ℂ) ^ α i) * ∏ j, ((φ w).2.2.1 j : ℂ) ^ δ j := by
  let Y := ElementaryLieGroup m' n' r' F'
  let coord (j : Fin m' ⊕ Fin r') : Y →+ ℝ := Sum.elim
    (fun i : Fin m' ↦ ⟨⟨fun g : Y ↦ g.1 i, rfl⟩, fun _ _ ↦ rfl⟩)
    (fun i : Fin r' ↦ (Int.castAddHom ℝ).comp
      ⟨⟨fun g : Y ↦ g.2.2.1 i, rfl⟩, fun _ _ ↦ rfl⟩) j
  have hcoord (j) : Continuous (coord j) := by
    cases j with
    | inl i => exact (PiLp.continuous_apply 2 _ i).comp continuous_fst
    | inr i =>
      exact (continuous_of_discreteTopology (f := Int.castAddHom ℝ)).comp
        ((continuous_apply i).comp continuous_snd.snd.fst)
  choose l hl he using fun j ↦ extend_real_hom_open H hH ((coord j).comp φ) ((hcoord j).comp hc)
  choose P hP using fun j ↦ elementary_real_hom_polynomial (l j) (hl j)
  refine ⟨(∏ i, P (.inl i) ^ α i) * ∏ j, P (.inr j) ^ δ j, fun w ↦ ?_⟩
  simp only [map_mul, map_prod, map_pow, hP, he]
  change _ * (∏ j, (((φ w).2.2.1 j : ℝ) : ℂ) ^ δ j) = _
  simp only [Complex.ofReal_intCast]
  rfl

/-- A Schwartz function on an elementary group which descends from an open
subgroup through an open quotient is Schwartz on the quotient. -/
private theorem elementarySchwartz_open_quotient {m n r m' n' r' : ℕ} {F F' : Type}
    [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
    [AddCommGroup F'] [TopologicalSpace F'] [DiscreteTopology F'] [Finite F']
    (H : AddSubgroup (ElementaryLieGroup m n r F)) (hH : IsOpen (H : Set (ElementaryLieGroup m n r F)))
    (φ : H →+ ElementaryLieGroup m' n' r' F') (hc : Continuous φ) (ho : IsOpenMap φ)
    (hs : Function.Surjective φ) (s : ElementarySchwartz m n r F)
    (g : ElementaryLieGroup m' n' r' F' → ℂ) (hg : ∀ w : H, s w.val = g (φ w)) :
    g ∈ elementarySchwartzSubmodule m' n' r' F' := by
  classical
  obtain ⟨L, hL⟩ := elementary_open_quotient_charts H hH φ hc ho hs
  have hfiber (a b) : ∃ y a' b', ∀ x, g (elementaryCover x a b) = s (elementaryCover (L x + y) a' b') := by
    obtain ⟨y, a', b', h⟩ := hL a b
    refine ⟨y, a', b', fun x ↦ ?_⟩
    obtain ⟨w, hw, hp⟩ := h x
    rw [← hp, ← hw, hg]
  refine ⟨fun a b ↦ ?_, fun i ↦ ?_⟩
  · obtain ⟨y, a', b', h⟩ := hfiber a b
    rw [funext h]
    exact (s.property.1 a' b').comp (L.contDiff.add contDiff_const)
  obtain ⟨p, hp⟩ := elementary_open_quotient_weight H hH φ hc i.1 i.2.2.2
  obtain ⟨T, c, hT⟩ := elementaryPartial_comp_lift (r := r) (r' := r') (F := F) (F' := F') L i.2.1 i.2.2.1
  let M (v : (Fin m → ℕ) × (Fin n → ℕ)) := ∑ d ∈ p.support, ‖p.coeff d‖ *
    elementarySchwartzSeminorm (fun k ↦ d (Sum.inl k), v.1, v.2, fun j ↦ d (Sum.inr j)) s
  refine lt_of_le_of_lt ?_ (ENNReal.ofReal_lt_top (r := ∑ v ∈ T, ‖c v‖ * M v))
  refine iSup_le fun x ↦ iSup_le fun a ↦ iSup_le fun b ↦ ?_
  obtain ⟨y, a', b', h⟩ := hL a b
  have hfun (u) : g (elementaryCover u a b) = s (elementaryCover (L u + y) a' b') := by
    obtain ⟨w, hw, hp⟩ := h u
    rw [← hp, ← hw, hg]
  have hpart := hT s g y a b a' b' (s.property.1 a' b') hfun x
  obtain ⟨w, hw, hφ⟩ := h x
  have hwgt := hp w
  rw [hw,hφ] at hwgt
  let vcoord := Sum.elim (fun k : Fin m ↦ ((L x + y).1 k : ℂ)) (fun j : Fin r ↦ (a' j : ℂ))
  change MvPolynomial.eval vcoord p =
    (∏ k, (x.1 k : ℂ) ^ i.1 k) * ∏ j, (a j : ℂ) ^ i.2.2.2 j at hwgt
  rw [← ENNReal.ofReal_coe_nnreal]
  apply ENNReal.ofReal_le_ofReal
  change ‖_ * elementaryPartial g i.2.1 i.2.2.1 x a b‖ ≤ _
  rw [← hwgt, hpart, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun v _ ↦ ?_)
  rw [norm_mul, norm_smul, mul_left_comm]
  exact mul_le_mul_of_nonneg_left
    (elementarySchwartz_polynomial_weight_le_monomial_sum p s v.1 v.2 (L x + y) a' b') (norm_nonneg _)

/-- Two open coordinate maps with nested kernels identify the pullback from the
quotient with restriction to an open elementary subgroup. -/
private theorem elementarySchwartz_of_common_pullback {m n r m' n' r' : ℕ} {F F' : Type}
    [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
    [AddCommGroup F'] [TopologicalSpace F'] [DiscreteTopology F'] [Finite F']
    {A : Type*} [AddCommGroup A] [TopologicalSpace A]
    (p : A →+ ElementaryLieGroup m n r F) (pc : Continuous p) (po : IsOpenMap p)
    (q : A →+ ElementaryLieGroup m' n' r' F') (qc : Continuous q) (qo : IsOpenMap q)
    (qs : Function.Surjective q) (hk : p.ker ≤ q.ker)
    (s : ElementarySchwartz m n r F) (g : ElementaryLieGroup m' n' r' F' → ℂ)
    (hg : ∀ x, s (p x) = g (q x)) : g ∈ elementarySchwartzSubmodule m' n' r' F' := by
  let H := p.range
  have hH : IsOpen (H : Set (ElementaryLieGroup m n r F)) := by
    rw [AddMonoidHom.coe_range, ← image_univ]
    exact po _ isOpen_univ
  let j := p.rangeRestrict
  have hj : IsOpenQuotientMap j := by
    refine ⟨p.rangeRestrict_surjective, pc.subtype_mk _, ?_⟩
    intro U hU
    have he : j '' U = Subtype.val ⁻¹' (p '' U) := Set.ext fun w ↦
      ⟨fun ⟨x,hx,h⟩ ↦ ⟨x,hx,congrArg Subtype.val h⟩, fun ⟨x,hx,h⟩ ↦ ⟨x,hx,Subtype.ext h⟩⟩
    exact he ▸ (po _ hU).preimage continuous_subtype_val
  have hker : j.ker ≤ q.ker := fun x hx ↦ hk (congrArg Subtype.val (show j x = 0 from hx))
  let φ := j.liftOfRightInverseAux (Function.surjInv hj.surjective) (Function.rightInverse_surjInv _) q hker
  have hφ (x) : φ (j x) = q x := j.liftOfRightInverseAux_comp_apply _ _ _ _ x
  have hφc : Continuous φ := hj.isQuotientMap.continuous_iff.mpr (qc.congr (fun x ↦ (hφ x).symm))
  have hφo : IsOpenMap φ := by
    intro U hU
    rw [← image_preimage_eq U hj.surjective, ← image_comp, show φ ∘ j = q from funext hφ]
    exact qo _ (hU.preimage hj.continuous)
  refine elementarySchwartz_open_quotient H hH φ hφc hφo
    (fun y ↦ (qs y).elim fun x hx ↦ ⟨j x, (hφ x).trans hx⟩) s g ?_
  intro w
  obtain ⟨x,rfl⟩ := hj.surjective w
  rw [hφ]
  exact hg x

include hTop in
/-- A function supported on the smaller open subgroup and invariant under its
kernel descends into the specified stage as soon as it is Schwartz in a
larger stage. -/
private theorem schwartzBruhatStage_descend_of_invariant {a c : BruhatStructuralPair G}
    (hac : a ≤ c) (e : ElementaryLCAPresentation a.quotient) (d : ElementaryLCAPresentation c.quotient)
    (s : SchwartzBruhatStage d) (f : G → ℂ) (hs : schwartzBruhatStageRealization c d s = f)
    (hsupp : ∀ x ∉ a.val.1, f x = 0)
    (hinv : ∀ h ∈ OrderDual.ofDual a.val.2, ∀ x, f (h * x) = f x) :
    ∃ t : SchwartzBruhatStage e, schwartzBruhatStageRealization a e t = f := by
  classical
  let inc := Subgroup.inclusion hac.1
  let p := MonoidHom.toAdditive ((d.equiv.toMulEquiv.toMonoidHom.comp (QuotientGroup.mk' _)).comp inc)
  let q := MonoidHom.toAdditive (e.equiv.toMulEquiv.toMonoidHom.comp (QuotientGroup.mk' _))
  let lift : a.quotient → ℂ := Quotient.lift (fun x : a.val.1 ↦ f x.val) (by
    intro x y h
    have hk : x⁻¹ * y ∈ (OrderDual.ofDual a.val.2).comap a.val.1.subtype :=
      QuotientGroup.eq.mp (show (QuotientGroup.mk x : a.quotient) = QuotientGroup.mk y from Quotient.sound h)
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, mul_right_comm, inv_mul_cancel, one_mul]
      using (hinv (x⁻¹ * y).val hk x.val).symm)
  let g := fun w ↦ lift (e.equiv.symm (Multiplicative.ofAdd w))
  have hg (x : a.val.1) : g (q (Additive.ofMul x)) = f x.val := by
    change lift (e.equiv.symm (e.equiv (QuotientGroup.mk x))) = _
    rw [e.equiv.symm_apply_apply]
    rfl
  have pc : Continuous p := d.equiv.continuous.comp (QuotientGroup.continuous_mk.comp
    (show Continuous inc from continuous_subtype_val.subtype_mk _))
  have po : IsOpenMap p := d.equiv.toHomeomorph.isOpenMap.comp
    ((QuotientGroup.isOpenMap_coe (N := (OrderDual.ofDual c.val.2).comap c.val.1.subtype)).comp
      (a.property.1.isOpenMap_inclusion hac.1))
  have qc : Continuous q := e.equiv.continuous.comp (QuotientGroup.continuous_mk
    (N := (OrderDual.ofDual a.val.2).comap a.val.1.subtype))
  have qo : IsOpenMap q := e.equiv.toHomeomorph.isOpenMap.comp (QuotientGroup.isOpenMap_coe
    (N := (OrderDual.ofDual a.val.2).comap a.val.1.subtype))
  have qs : Function.Surjective q := fun w ↦ (e.equiv.surjective (Multiplicative.ofAdd w)).elim
    fun t ht ↦ (QuotientGroup.mk_surjective t).elim fun x hx ↦ ⟨Additive.ofMul x, (congrArg e.equiv hx).trans ht⟩
  have hk : p.ker ≤ q.ker := by
    intro x hx
    change e.equiv (QuotientGroup.mk (Additive.toMul x)) = 1
    refine (congrArg e.equiv ((a.quotient_mk_eq_one _).mpr ?_)).trans (map_one _)
    apply (show OrderDual.ofDual c.val.2 ≤ OrderDual.ofDual a.val.2 from hac.2)
    apply (c.quotient_mk_eq_one (inc (Additive.toMul x))).mp
    apply d.equiv.injective
    exact (show d.equiv (QuotientGroup.mk (inc (Additive.toMul x))) = 1 from hx).trans (map_one d.equiv).symm
  have he (x : Additive a.val.1) : s (p x) = g (q x) := by
    refine Eq.trans ?_ (hg (Additive.toMul x)).symm
    rw [← hs, schwartzBruhatStageRealization_apply, dite_eq_left (hac.1 (Additive.toMul x).property)]
    rfl
  let t : SchwartzBruhatStage e := ⟨g, elementarySchwartz_of_common_pullback p pc po q qc qo qs hk s g he⟩
  refine ⟨t, funext fun x ↦ ?_⟩
  rw [schwartzBruhatStageRealization_apply a e t]
  split_ifs with hx
  · exact hg ⟨x,hx⟩
  · exact (hsupp _ hx).symm

section Pullback

variable {m n r m' n' r' : ℕ} {F F' : Type}
  [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
  [AddCommGroup F'] [TopologicalSpace F'] [DiscreteTopology F'] [Finite F']

omit [DiscreteTopology F] [Finite F] in
/-- The ambient noncompact coordinates descend through an open surjection with compact kernel.
Consequently their monomials are polynomial weights in the quotient coordinates. -/
private lemma stage_pullback_weight
    (H : AddSubgroup (ElementaryLieGroup m n r F))
    (φ : H →+ ElementaryLieGroup m' n' r' F') (hφ : IsOpenQuotientMap φ)
    (hK : IsCompact (φ.ker : Set H)) (α : Fin m → ℕ) (δ : Fin r → ℕ) :
    ∃ p : MvPolynomial (Fin m' ⊕ Fin r') ℂ, ∀ w : H,
      MvPolynomial.eval (Sum.elim (fun i ↦ ((φ w).1 i : ℂ)) (fun j ↦ ((φ w).2.2.1 j : ℂ))) p =
        (∏ i, (w.val.1 i : ℂ) ^ α i) * ∏ j, (w.val.2.2.1 j : ℂ) ^ δ j := by
  let coord (j : Fin m ⊕ Fin r) : H →+ ℝ := Sum.elim
    (fun i : Fin m ↦ ⟨⟨fun w : H ↦ w.val.1 i, rfl⟩, fun _ _ ↦ rfl⟩)
    (fun i : Fin r ↦ (Int.castAddHom ℝ).comp
      ⟨⟨fun w : H ↦ w.val.2.2.1 i, rfl⟩, fun _ _ ↦ rfl⟩) j
  have hc (j) : Continuous (coord j) := by
    cases j with
    | inl i => exact (PiLp.continuous_apply 2 _ i).comp continuous_subtype_val.fst
    | inr i =>
      exact (continuous_of_discreteTopology (f := Int.castAddHom ℝ)).comp
        ((continuous_apply i).comp continuous_subtype_val.snd.snd.fst)
  let : CompactSpace φ.ker := isCompact_iff_compactSpace.mp hK
  have hk (j) : φ.ker ≤ (coord j).ker := fun w hw ↦
    compact_hom_real_zero ((coord j).comp φ.ker.subtype) ((hc j).comp continuous_subtype_val) ⟨w,hw⟩
  let l (j) := φ.liftOfRightInverseAux (Function.surjInv hφ.surjective)
    (Function.rightInverse_surjInv _) (coord j) (hk j)
  have he (j) (w : H) : l j (φ w) = coord j w := φ.liftOfRightInverseAux_comp_apply _ _ _ _ _
  have hl (j) : Continuous (l j) := hφ.isQuotientMap.continuous_iff.mpr
    ((hc j).congr fun w ↦ (he j w).symm)
  choose P hP using fun j ↦ elementary_real_hom_polynomial (l j) (hl j)
  refine ⟨(∏ i, P (.inl i) ^ α i) * ∏ j, P (.inr j) ^ δ j, fun w ↦ ?_⟩
  simp only [map_mul, map_prod, map_pow, hP, he]
  change _ * (∏ j, ((w.val.2.2.1 j : ℝ) : ℂ) ^ δ j) = _
  simp only [Complex.ofReal_intCast]
  rfl

omit [Finite F] in
/-- On a discrete fibre an open-subgroup cutoff either vanishes identically or
its quotient coordinate lifts to an affine map with fibre-independent linear part. -/
private lemma stage_pullback_charts
    (H : AddSubgroup (ElementaryLieGroup m n r F)) (hH : IsOpen (H : Set (ElementaryLieGroup m n r F)))
    (φ : H →+ ElementaryLieGroup m' n' r' F') (hc : Continuous φ) :
    ∃ L : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) →L[ℝ]
        (EuclideanSpace ℝ (Fin m') × EuclideanSpace ℝ (Fin n')),
      ∀ a b, (∀ x, elementaryCover x a b ∉ H) ∨
        ∃ y a' b', ∀ x, ∃ hw : elementaryCover x a b ∈ H,
          φ ⟨_, hw⟩ = elementaryCover (L x + y) a' b' := by
  let q := elementaryCoverZeroHom (m := m) (n := n) (r := r) (F := F)
  have hq := (elementaryCoverZeroHom_continuous_isOpenMap (m := m) (n := n) (r := r) (F := F)).1
  have hmem (x) : q x ∈ H := by
    have he := ((show IsClopen (H : Set (ElementaryLieGroup m n r F)) from ⟨H.isClosed_of_isOpen hH, hH⟩).preimage hq).eq_univ
      (show (q ⁻¹' (H : Set _)).Nonempty from ⟨0, by simp [q]⟩)
    exact eq_univ_iff_forall.mp he x
  let A := φ.comp (q.codRestrict H hmem)
  have hA : Continuous A := hc.comp (hq.subtype_mk _)
  let R := (AddMonoidHom.fst _ _).comp A
  let T := (AddMonoidHom.fst _ _).comp ((AddMonoidHom.snd _ _).comp A)
  choose l hl using fun i : Fin n' ↦ exists_addCircle_coe_linearMap_eq
    ((Pi.evalAddMonoidHom _ i).comp T) ((continuous_apply i).comp hA.snd.fst)
  let L := (R.toRealLinearMap hA.fst).prod
    ((EuclideanSpace.equiv (Fin n') ℝ).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi l))
  refine ⟨L, fun a b ↦ ?_⟩
  have hshift (x) : q x + elementaryCover 0 a b = elementaryCover x a b := by
    simp [q, elementaryCoverZeroHom, elementaryCover, Pi.zero_def]
  by_cases hb : elementaryCover 0 a b ∈ H
  · right
    let c := φ ⟨_, hb⟩
    obtain ⟨t, ht⟩ := elementaryCover_surjective c.2.2.1 c.2.2.2 c.1 c.2.1
    refine ⟨(c.1, t), c.2.2.1, c.2.2.2, fun x ↦ ⟨(hshift x) ▸ H.add_mem (hmem x) hb, ?_⟩⟩
    have hs : (⟨elementaryCover x a b, (hshift x) ▸ H.add_mem (hmem x) hb⟩ : H) = q.codRestrict H hmem x + ⟨_,hb⟩ :=
      Subtype.ext (hshift x).symm
    rw [hs, map_add]
    change A x + c = _
    symm
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · funext i
      have hti := congrArg (fun y : ElementaryLieGroup m' n' r' F' ↦ y.2.1 i) ht
      change ((l i x + t i : ℝ) : AddCircle (1 : ℝ)) = (A x).2.1 i + c.2.1 i
      rw [AddCircle.coe_add, hl i x]
      exact congrArg ((A x).2.1 i + ·) hti
    · have h := hA.snd.snd.isConst_of_preconnectedSpace x 0
      rw [map_zero A] at h
      change c.2.2 = (A x).2.2 + c.2.2
      rw [h]
      exact (zero_add _).symm
  · left
    intro x
    rwa [← hshift, H.add_mem_cancel_left (hmem x)]

omit [Finite F] in
/-- A Schwartz function pulled back by a quotient with compact kernel and extended by zero
from an open subgroup is still Schwartz. -/
private lemma stage_pullback_elementary
    (H : AddSubgroup (ElementaryLieGroup m n r F)) (hH : IsOpen (H : Set (ElementaryLieGroup m n r F)))
    (φ : H →+ ElementaryLieGroup m' n' r' F') (hφ : IsOpenQuotientMap φ)
    (hK : IsCompact (φ.ker : Set H)) (s : ElementarySchwartz m' n' r' F')
    (g : ElementaryLieGroup m n r F → ℂ) (hon : ∀ w : H, g w.val = s (φ w))
    (hoff : ∀ w ∉ H, g w = 0) : g ∈ elementarySchwartzSubmodule m n r F := by
  classical
  obtain ⟨L, hL⟩ := stage_pullback_charts H hH φ hφ.continuous
  refine ⟨fun a b ↦ ?_, fun i ↦ ?_⟩
  · rcases hL a b with h | ⟨y, a', b', h⟩
    · simpa only [funext (fun x ↦ hoff _ (h x))] using (contDiff_const (c := (0 : ℂ)))
    · have he (x) : g (elementaryCover x a b) = s (elementaryCover (L x + y) a' b') := by
        obtain ⟨hw, hp⟩ := h x
        exact (hon ⟨_, hw⟩).trans (congrArg s.val hp)
      rw [funext he]
      exact (s.property.1 a' b').comp (L.contDiff.add contDiff_const)
  obtain ⟨p, hp⟩ := stage_pullback_weight H φ hφ hK i.1 i.2.2.2
  obtain ⟨T, c, hT⟩ := elementaryPartial_comp_lift (r := r') (r' := r) (F := F') (F' := F)
    L i.2.1 i.2.2.1
  let M (v : (Fin m' → ℕ) × (Fin n' → ℕ)) := ∑ d ∈ p.support, ‖p.coeff d‖ *
    elementarySchwartzSeminorm (fun k ↦ d (Sum.inl k), v.1, v.2, fun j ↦ d (Sum.inr j)) s
  refine lt_of_le_of_lt ?_ (ENNReal.ofReal_lt_top (r := ∑ v ∈ T, ‖c v‖ * M v))
  refine iSup_le fun x ↦ iSup_le fun a ↦ iSup_le fun b ↦ ?_
  rcases hL a b with h | ⟨y, a', b', h⟩
  · simp [elementaryPartial, funext (fun u ↦ hoff _ (h u))]
  have he (x) : g (elementaryCover x a b) = s (elementaryCover (L x + y) a' b') := by
    obtain ⟨hw, hp⟩ := h x
    exact (hon ⟨_, hw⟩).trans (congrArg s.val hp)
  have hpart := hT s g y a b a' b' (s.property.1 a' b') he x
  obtain ⟨hw, hφw⟩ := h x
  have hwgt := hp ⟨_, hw⟩
  rw [hφw] at hwgt
  let vcoord := Sum.elim (fun k : Fin m' ↦ ((L x + y).1 k : ℂ)) (fun j : Fin r' ↦ (a' j : ℂ))
  change MvPolynomial.eval vcoord p =
    (∏ k, (x.1 k : ℂ) ^ i.1 k) * ∏ j, (a j : ℂ) ^ i.2.2.2 j at hwgt
  rw [← ENNReal.ofReal_coe_nnreal]
  apply ENNReal.ofReal_le_ofReal
  change ‖_ * elementaryPartial g i.2.1 i.2.2.1 x a b‖ ≤ _
  rw [← hwgt, hpart, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun v _ ↦ ?_)
  rw [norm_mul, norm_smul, mul_left_comm]
  exact mul_le_mul_of_nonneg_left
    (elementarySchwartz_polynomial_weight_le_monomial_sum p s v.1 v.2 (L x + y) a' b') (norm_nonneg _)

omit [Finite F] in
/-- Two open coordinate maps from a common group produce the elementary representative, with
zero extension off the range of the larger-stage coordinate map. -/
private lemma stage_pullback_common {A : Type*} [AddCommGroup A] [TopologicalSpace A]
    (p : A →+ ElementaryLieGroup m n r F) (pc : Continuous p) (po : IsOpenMap p)
    (q : A →+ ElementaryLieGroup m' n' r' F') (hq : IsOpenQuotientMap q)
    (hk : p.ker ≤ q.ker) (hK : IsCompact (q.ker : Set A)) (s : ElementarySchwartz m' n' r' F') :
    ∃ t : ElementarySchwartz m n r F, (∀ x, t (p x) = s (q x)) ∧ ∀ w ∉ p.range, t w = 0 := by
  classical
  let H := p.range
  have hH : IsOpen (H : Set (ElementaryLieGroup m n r F)) := by
    rw [AddMonoidHom.coe_range, ← image_univ]
    exact po _ isOpen_univ
  let j := p.rangeRestrict
  have hj : IsOpenQuotientMap j := by
    refine ⟨p.rangeRestrict_surjective, pc.subtype_mk _, ?_⟩
    intro U hU
    have he : j '' U = Subtype.val ⁻¹' (p '' U) := Set.ext fun w ↦
      ⟨fun ⟨x,hx,h⟩ ↦ ⟨x,hx,congrArg Subtype.val h⟩, fun ⟨x,hx,h⟩ ↦ ⟨x,hx,Subtype.ext h⟩⟩
    exact he ▸ (po _ hU).preimage continuous_subtype_val
  have hker : j.ker ≤ q.ker := fun x hx ↦ hk (congrArg Subtype.val (show j x = 0 from hx))
  let φ := j.liftOfRightInverseAux (Function.surjInv hj.surjective) (Function.rightInverse_surjInv _) q hker
  have he (x) : φ (j x) = q x := j.liftOfRightInverseAux_comp_apply _ _ _ _ x
  have hφ : IsOpenQuotientMap φ := by
    refine ⟨fun y ↦ (hq.surjective y).elim fun x hx ↦ ⟨j x, (he x).trans hx⟩,
      hj.isQuotientMap.continuous_iff.mpr (hq.continuous.congr (fun x ↦ (he x).symm)), ?_⟩
    intro U hU
    rw [← image_preimage_eq U hj.surjective, ← image_comp, show φ ∘ j = q from funext he]
    exact hq.isOpenMap _ (hU.preimage hj.continuous)
  have hKφ : IsCompact (φ.ker : Set H) := by
    have hEq : j ⁻¹' (φ.ker : Set H) = (q.ker : Set A) := Set.ext fun x ↦ by
      change φ (j x) = 0 ↔ q x = 0
      rw [he]
    rw [← image_preimage_eq (φ.ker : Set H) hj.surjective, hEq]
    exact hK.image hj.continuous
  let g (w : ElementaryLieGroup m n r F) := if hw : w ∈ H then s (φ ⟨_,hw⟩) else 0
  have hon (w : H) : g w = s (φ w) := dite_eq_left w.property
  have hoff (w) (hw : w ∉ H) : g w = 0 := dite_eq_right hw
  exact ⟨⟨g, stage_pullback_elementary H hH φ hφ hKφ s g hon hoff⟩,
    fun x ↦ (hon (j x)).trans (congrArg s.val (he x)), hoff⟩

end Pullback

section Stages
variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]
/-- Range inclusion, constructed in elementary coordinates, without using a transition map. -/
private lemma kernelStage_realization_mono {a b : BruhatStructuralPair G} (h : a ≤ b)
    (e : ElementaryLCAPresentation a.quotient) (d : ElementaryLCAPresentation b.quotient)
    (s : SchwartzBruhatStage e) : ∃ t : SchwartzBruhatStage d,
      schwartzBruhatStageRealization b d t = schwartzBruhatStageRealization a e s := by
  classical
  let inc := Subgroup.inclusion h.1
  let π := d.equiv.toMulEquiv.toMonoidHom.comp (QuotientGroup.mk' _)
  let p := MonoidHom.toAdditive (π.comp inc)
  let q := MonoidHom.toAdditive (e.equiv.toMulEquiv.toMonoidHom.comp (QuotientGroup.mk' _))
  have pc : Continuous p := d.equiv.continuous.comp (QuotientGroup.continuous_mk.comp
    (show Continuous inc from continuous_subtype_val.subtype_mk _))
  have po : IsOpenMap p := d.equiv.toHomeomorph.isOpenMap.comp
    ((QuotientGroup.isOpenMap_coe (N := (OrderDual.ofDual b.val.2).comap b.val.1.subtype)).comp
      (a.property.1.isOpenMap_inclusion h.1))
  have hq : IsOpenQuotientMap q := by
    refine ⟨fun w ↦ (e.equiv.surjective (Multiplicative.ofAdd w)).elim fun t ht ↦
      (QuotientGroup.mk_surjective t).elim fun x hx ↦ ⟨Additive.ofMul x, (congrArg e.equiv hx).trans ht⟩,
      e.equiv.continuous.comp (QuotientGroup.continuous_mk
        (N := (OrderDual.ofDual a.val.2).comap a.val.1.subtype)),
      e.equiv.toHomeomorph.isOpenMap.comp (QuotientGroup.isOpenMap_coe
        (N := (OrderDual.ofDual a.val.2).comap a.val.1.subtype))⟩
  have hkle : OrderDual.ofDual b.val.2 ≤ OrderDual.ofDual a.val.2 := h.2
  have hker (x : Additive a.val.1) : x ∈ q.ker ↔ (Additive.toMul x).val ∈ OrderDual.ofDual a.val.2 := by
    change e.equiv (QuotientGroup.mk (Additive.toMul x)) = 1 ↔ _
    rw [← map_one e.equiv, e.equiv.injective.eq_iff, a.quotient_mk_eq_one]
  have hk : p.ker ≤ q.ker := by
    intro x hx
    apply (hker x).2
    apply hkle
    apply (b.quotient_mk_eq_one (inc (Additive.toMul x))).mp
    apply d.equiv.injective
    exact (show d.equiv (QuotientGroup.mk (inc (Additive.toMul x))) = 1 from hx).trans (map_one d.equiv).symm
  have hK : IsCompact (q.ker : Set (Additive a.val.1)) := by
    have heq : (q.ker : Set (Additive a.val.1)) =
        Subtype.val ⁻¹' ((OrderDual.ofDual a.val.2 : Subgroup G) : Set G) := Set.ext hker
    rw [heq]
    exact (a.val.1.isClosed_of_isOpen a.property.1).isClosedEmbedding_subtypeVal.isCompact_preimage
      (compact_bruhat_kernel a)
  obtain ⟨t, hon, hoff⟩ := stage_pullback_common p pc po q hq hk hK s
  refine ⟨t, funext fun x ↦ ?_⟩
  rw [schwartzBruhatStageRealization_apply, schwartzBruhatStageRealization_apply]
  by_cases ha : x ∈ a.val.1
  · rw [dite_eq_left ha, dite_eq_left (h.1 ha)]
    exact hon (Additive.ofMul ⟨x, ha⟩)
  rw [dite_eq_right ha]
  split_ifs with hb
  · let z : b.val.1 := ⟨x,hb⟩
    apply hoff
    rintro ⟨w, hw⟩
    change π (inc (Additive.toMul w)) = π z at hw
    have hkz : π (z / inc (Additive.toMul w)) = 1 := by rw [map_div, hw, div_self']
    have hk' := (b.quotient_mk_eq_one (z / inc (Additive.toMul w))).mp
      (d.equiv.injective (hkz.trans (map_one d.equiv).symm))
    apply ha
    have he := a.val.1.mul_mem (a.property.2.2.2 (hkle hk')) (Additive.toMul w).property
    change x / (Additive.toMul w).val * (Additive.toMul w).val ∈ a.val.1 at he
    simpa only [div_mul_cancel] using he
  · rfl

/-- The forward lift is continuous: both stages map continuously into the pointwise
range of the second, so Fréchet factorization applies to the constant second stage. -/
private lemma kernelStage_transitionMap {a b : BruhatStructuralPair G} (h : a ≤ b)
    (e : ElementaryLCAPresentation a.quotient) (d : ElementaryLCAPresentation b.quotient) :
    ∃ j : SchwartzBruhatStage e →L[ℂ] SchwartzBruhatStage d,
      ∀ s, schwartzBruhatStageRealization b d (j s) = schwartzBruhatStageRealization a e s := by
  let A := schwartzBruhatStageRealization a e
  let B := schwartzBruhatStageRealization b d
  have hcA : Continuous A := continuous_pi (continuous_schwartzBruhatStage_eval a e)
  have hcB : Continuous B := continuous_pi (continuous_schwartzBruhatStage_eval b d)
  let i : SchwartzBruhatStage d →L[ℂ] B.range := ⟨B.rangeRestrict, hcB.subtype_mk _⟩
  let u : SchwartzBruhatStage e →L[ℂ] B.range :=
    ⟨A.codRestrict _ (kernelStage_realization_mono h e d), hcA.subtype_mk _⟩
  have hi : Function.Injective i := fun _ _ hz ↦
    schwartzBruhatStageRealization_injective b d (congrArg (fun z : B.range ↦ z.val) hz)
  obtain ⟨_, j, hj⟩ := frechet_factorization (X := fun _ ↦ SchwartzBruhatStage d)
    (fun _ ↦ elementarySchwartz_isFrechet) (fun _ ↦ i) (fun _ ↦ hi) (fun _ ↦ Subset.rfl)
    (fun z ↦ ⟨0, z.property.elim fun t ht ↦ ⟨t, Subtype.ext ht⟩⟩) elementarySchwartz_isFrechet u
  exact ⟨j, fun s ↦ congrArg Subtype.val (DFunLike.congr_fun hj s)⟩

omit [T2Space G] [LocallyCompactSpace G] in
/-- Inside the larger stage, support and invariance are closed pointwise equations.
Descent identifies their common solution space with the range of the transition. -/
private lemma stage_clm_closed_range {a b : BruhatStructuralPair G} (h : a ≤ b)
    (e : ElementaryLCAPresentation a.quotient) (d : ElementaryLCAPresentation b.quotient)
    (j : SchwartzBruhatStage e →L[ℂ] SchwartzBruhatStage d)
    (hj : ∀ s, schwartzBruhatStageRealization b d (j s) = schwartzBruhatStageRealization a e s) :
    IsClosed (range j) := by
  classical
  let B := schwartzBruhatStageRealization b d
  let S := ⋂ x ∉ a.val.1, {t : SchwartzBruhatStage d | B t x = 0}
  let T := ⋂ (k : (OrderDual.ofDual a.val.2 : Subgroup G)), ⋂ x, {t : SchwartzBruhatStage d | B t (k.val*x) = B t x}
  have hEq : range j = S ∩ T := by
    ext t
    simp only [S, T, mem_inter_iff, mem_iInter, mem_ofPred_eq]
    refine ⟨?_, fun ⟨hs,ht⟩ ↦ ?_⟩
    · rintro ⟨s,rfl⟩
      rw [show B (j s) = _ from hj s]
      exact ⟨fun x hx ↦ by rw [schwartzBruhatStageRealization_apply, dite_eq_right hx],
        fun k x ↦ stage_realization_mul_kernel a e s k.property x⟩
    · obtain ⟨s,he⟩ := schwartzBruhatStage_descend_of_invariant h e d t (B t) rfl hs
        (fun k hk ↦ ht ⟨k,hk⟩)
      exact ⟨s, schwartzBruhatStageRealization_injective b d ((hj s).trans he)⟩
  rw [hEq]
  exact (isClosed_iInter fun x ↦ isClosed_iInter fun _ ↦ isClosed_eq
    (continuous_schwartzBruhatStage_eval b d x) continuous_const).inter
    (isClosed_iInter fun k ↦ isClosed_iInter fun x ↦ isClosed_eq
      (continuous_schwartzBruhatStage_eval b d (k.val*x)) (continuous_schwartzBruhatStage_eval b d x))

/-- An injective continuous linear map between Fréchet spaces with closed range is a closed
embedding: apply open mapping to its corestriction onto that complete subspace. -/
private lemma stage_frechet_closed_embedding {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    (hX : IsFrechetTVS X) (hY : IsFrechetTVS Y) (j : X →L[ℂ] Y) (hi : Function.Injective j)
    (hc : IsClosed (range j)) : IsClosedEmbedding j := by
  obtain ⟨hTX, hPX, hMX, hCX⟩ := hX
  obtain ⟨hTY, hPY, hMY, hCY⟩ := hY
  let : UniformSpace X := IsTopologicalAddGroup.rightUniformSpace X
  have : IsUniformAddGroup X := isUniformAddGroup_of_addCommGroup
  have : CompleteSpace X := hCX
  let : UniformSpace Y := IsTopologicalAddGroup.rightUniformSpace Y
  have : IsUniformAddGroup Y := isUniformAddGroup_of_addCommGroup
  have : CompleteSpace Y := hCY
  let Z := j.range
  have hZ : IsClosed (Z : Set Y) := hc
  have : CompleteSpace Z := completeSpace_coe_iff_isComplete.mpr hZ.isComplete
  have : IsUniformAddGroup Z := Z.toAddSubgroup.isUniformAddGroup
  have : FirstCountableTopology Z := inferInstanceAs (FirstCountableTopology (Z : Set Y))
  have : (uniformity Z).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_zero Z]
    infer_instance
  have : BaireSpace Z := by
    let := UniformSpace.metricSpace Z
    infer_instance
  let p : X →L[ℂ] Z := j.rangeRestrict
  have hs : Function.Surjective p := fun z ↦ z.property.elim fun x hx ↦ ⟨x, Subtype.ext hx⟩
  have hop := isOpenMap_of_not_isMeagre_range p (hs.range_eq ▸ not_isMeagre_of_isOpen isOpen_univ univ_nonempty)
  let eqv := Equiv.ofBijective p ⟨fun _ _ h ↦ hi (congrArg (fun z : Z ↦ z.val) h), hs⟩
  let homeo : X ≃ₜ Z := ⟨eqv, p.continuous, eqv.continuous_symm_iff.mpr hop⟩
  exact hZ.isClosedEmbedding_subtypeVal.comp homeo.isClosedEmbedding

end Stages

end StageTransitions

include hTop hT2 hLC in
/-- Paper: Lemma D.1.5.4, p. 762. Pullback to the smaller kernel and extension by
zero to the larger open subgroup give a closed embedding of stages.
Deviation: The map is characterized by equality of the realized functions on G,
which determines the pullback and extension on the elementary quotients. -/
theorem schwartzBruhatStage_transition {a b : BruhatStructuralPair G} (h : a ≤ b)
    (e : ElementaryLCAPresentation a.quotient) (e' : ElementaryLCAPresentation b.quotient) :
    ∃ j : SchwartzBruhatStage e →L[ℂ] SchwartzBruhatStage e',
      (∀ f, schwartzBruhatStageRealization b e' (j f) = schwartzBruhatStageRealization a e f) ∧
        IsClosedEmbedding j := by
  obtain ⟨j,hj⟩ := kernelStage_transitionMap h e e'
  refine ⟨j,hj, stage_frechet_closed_embedding elementarySchwartz_isFrechet elementarySchwartz_isFrechet
    j (fun x y hxy ↦ ?_) (stage_clm_closed_range h e e' j hj)⟩
  apply schwartzBruhatStageRealization_injective a e
  exact (hj x).symm.trans ((congrArg (schwartzBruhatStageRealization b e') hxy).trans (hj y))

/-- Paper: (D.1.5.4), p. 763. The underlying Schwartz–Bruhat submodule is generated
by the realizations in every structural pair and every elementary presentation. -/
def schwartzBruhatSubmodule (G : Type*) [CommGroup G] [TopologicalSpace G] :
    Submodule ℂ (G → ℂ) :=
  ⨆ (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient),
    (schwartzBruhatStageRealization a e).range

/-- Paper: (D.1.5.4), p. 763. The stage realization takes values in the
Schwartz–Bruhat submodule and gives the canonical linear stage map. -/
def schwartzBruhatStageInclusion (a : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation a.quotient) :
    SchwartzBruhatStage e →ₗ[ℂ] schwartzBruhatSubmodule G :=
  (schwartzBruhatStageRealization a e).codRestrict (schwartzBruhatSubmodule G)
    (fun f ↦ Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem e ⟨f, rfl⟩))

/-- Paper: (D.1.5.4), p. 763. The Schwartz–Bruhat topology is generated by the
seminorms that pull back continuously to each stage.
Deviation: Using all elementary presentations avoids fixing any choice of coordinates. -/
def SchwartzBruhat (G : Type*) [CommGroup G] [TopologicalSpace G] :=
  WithGeneratingSeminorms (schwartzBruhatSubmodule G)
    (Subtype.val : {p : Seminorm ℂ (schwartzBruhatSubmodule G) //
      ∀ (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient),
        Continuous (p ∘ schwartzBruhatStageInclusion a e)} → _)

section SchwartzBruhatInstances
variable (G : Type*) [CommGroup G] [TopologicalSpace G]

/-- The type `SchwartzBruhat G` unfolds to, with its seminorm family left to unification. Used
only to declare the instances once. -/
local notation "Unfolded" G => WithGeneratingSeminorms (schwartzBruhatSubmodule G) _

instance instAddCommGroupSchwartzBruhat : AddCommGroup (SchwartzBruhat G) :=
  inferInstanceAs (AddCommGroup (Unfolded G))

instance instModuleSchwartzBruhat : Module ℂ (SchwartzBruhat G) :=
  inferInstanceAs (Module ℂ (Unfolded G))

instance instTopologicalSpaceSchwartzBruhat : TopologicalSpace (SchwartzBruhat G) :=
  inferInstanceAs (TopologicalSpace (Unfolded G))

instance instPolynormableSpaceSchwartzBruhat : PolynormableSpace ℂ (SchwartzBruhat G) :=
  inferInstanceAs (PolynormableSpace ℂ (Unfolded G))

instance instIsTopologicalAddGroupSchwartzBruhat : IsTopologicalAddGroup (SchwartzBruhat G) :=
  inferInstanceAs (IsTopologicalAddGroup (Unfolded G))

instance instUniformSpaceSchwartzBruhat : UniformSpace (SchwartzBruhat G) :=
  inferInstanceAs (UniformSpace (Unfolded G))

instance instIsUniformAddGroupSchwartzBruhat : IsUniformAddGroup (SchwartzBruhat G) :=
  inferInstanceAs (IsUniformAddGroup (Unfolded G))

end SchwartzBruhatInstances

instance : CoeFun (SchwartzBruhat G) (fun _ ↦ G → ℂ) where
  coe f := (show schwartzBruhatSubmodule G from f).val

namespace SchwartzBruhat

variable (G) in
/-- A Schwartz–Bruhat function is an element of the Schwartz–Bruhat submodule of `G → ℂ`;
`SchwartzBruhat G` only adds the topology. -/
def toSubmodule : SchwartzBruhat G ≃ₗ[ℂ] schwartzBruhatSubmodule G := LinearEquiv.refl ℂ _

@[simp]
theorem coe_toSubmodule (f : SchwartzBruhat G) :
    ((toSubmodule G f : schwartzBruhatSubmodule G) : G → ℂ) = f := (rfl)

@[simp]
theorem toSubmodule_symm_apply (u : schwartzBruhatSubmodule G) (x : G) :
    (toSubmodule G).symm u x = (u : G → ℂ) x := (rfl)

theorem coe_injective : Function.Injective (fun f : SchwartzBruhat G ↦ (f : G → ℂ)) :=
  fun _ _ h ↦ (toSubmodule G).injective (Subtype.ext h)

@[ext]
theorem ext {f g : SchwartzBruhat G} (h : ∀ x, f x = g x) : f = g :=
  coe_injective (funext h)

@[simp] theorem coe_zero : ⇑(0 : SchwartzBruhat G) = 0 := (rfl)

@[simp] theorem coe_add (f g : SchwartzBruhat G) : ⇑(f + g) = ⇑f + ⇑g := (rfl)

@[simp] theorem coe_neg (f : SchwartzBruhat G) : ⇑(-f) = -⇑f := (rfl)

@[simp] theorem coe_sub (f g : SchwartzBruhat G) : ⇑(f - g) = ⇑f - ⇑g := (rfl)

@[simp] theorem coe_smul (c : ℂ) (f : SchwartzBruhat G) : ⇑(c • f) = c • ⇑f := (rfl)

/-- The inclusion of a stage into the Schwartz–Bruhat space: pull back along the quotient map
and extend by zero (`schwartzBruhatStageInclusion`, with values in `SchwartzBruhat G`). -/
def ofStage (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient) :
    SchwartzBruhatStage e →ₗ[ℂ] SchwartzBruhat G :=
  (toSubmodule G).symm.toLinearMap ∘ₗ schwartzBruhatStageInclusion a e

@[simp]
theorem ofStage_apply (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient)
    (f : SchwartzBruhatStage e) (x : G) :
    ofStage a e f x = schwartzBruhatStageRealization a e f x := (rfl)

variable (G) in
/-- The seminorms on `SchwartzBruhat G` whose composites with every stage inclusion are
continuous. They generate its topology (`SchwartzBruhat.withSeminorms`). -/
def seminormFamily : SeminormFamily ℂ (SchwartzBruhat G)
    {p : Seminorm ℂ (schwartzBruhatSubmodule G) //
      ∀ (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient),
        Continuous (p ∘ schwartzBruhatStageInclusion a e)} :=
  fun p ↦ p.val.comp (toSubmodule G).toLinearMap

theorem seminormFamily_apply (p) (f : SchwartzBruhat G) :
    seminormFamily G p f = p.val (toSubmodule G f) := (rfl)

variable (G) in
/-- The topology of `SchwartzBruhat G` is the one generated by `SchwartzBruhat.seminormFamily`. -/
theorem withSeminorms : WithSeminorms (seminormFamily G) :=
  withGeneratingSeminorms_spec _ _

/-- The stage inclusions are continuous. -/
theorem continuous_ofStage (a : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation a.quotient) : Continuous (ofStage a e) :=
  (withSeminorms G).continuous_of_continuous_comp _ (fun p ↦ p.2 a e)

/-- A linear map out of `SchwartzBruhat G` into a locally convex space is continuous once its
composites with all stage inclusions are. -/
theorem continuous_of_continuous_comp_ofStage {F : Type*} [AddCommGroup F] [Module ℂ F]
    [TopologicalSpace F] [PolynormableSpace ℂ F] (g : SchwartzBruhat G →ₗ[ℂ] F)
    (hg : ∀ (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient),
      Continuous (g ∘ ofStage a e)) : Continuous g :=
  (PolynormableSpace.withSeminorms ℂ F).continuous_of_continuous_comp g fun q ↦
    (withSeminorms G).continuous_seminorm
      ⟨(q.val.comp g).comp (toSubmodule G).symm.toLinearMap, fun a e ↦ q.2.comp (hg a e)⟩

end SchwartzBruhat

/-- Paper: (D.1.5.4), p. 763. The stage inclusion evaluates to the function
obtained by pullback and extension by zero. -/
theorem schwartzBruhatStageInclusion_apply (a : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation a.quotient) (f : SchwartzBruhatStage e) (x : G) :
    (show SchwartzBruhat G from schwartzBruhatStageInclusion a e f) x =
      schwartzBruhatStageRealization a e f x := rfl

/-- Membership in a double supremum of submodules whose sigma-indexed family is
nonempty and directed is membership in one of the submodules. -/
private theorem mem_iSup₂_iff_of_directed_sigma {M : Type*} [AddCommMonoid M] [Module ℂ M]
    {ι : Type*} {κ : ι → Type*} (F : (i : ι) → κ i → Submodule ℂ M)
    (hne : Nonempty ((i : ι) × κ i))
    (hd : Directed (· ≤ ·) (fun s : (i : ι) × κ i ↦ F s.1 s.2)) (m : M) :
    m ∈ ⨆ (i : ι) (j : κ i), F i j ↔ ∃ (i : ι) (j : κ i), m ∈ F i j := by
  rw [iSup_sigma' F, Submodule.mem_iSup_of_directed _ hd, Sigma.exists]

include hTop hT2 hLC in
/-- The range of a stage realization grows along the order on structural pairs,
for any choice of elementary presentations of the two quotients. -/
private theorem schwartzBruhatStageRealization_range_mono {a b : BruhatStructuralPair G}
    (h : a ≤ b) (e : ElementaryLCAPresentation a.quotient)
    (e' : ElementaryLCAPresentation b.quotient) :
    LinearMap.range (schwartzBruhatStageRealization a e) ≤
      LinearMap.range (schwartzBruhatStageRealization b e') := by
  obtain ⟨j, hj, -⟩ := schwartzBruhatStage_transition h e e'
  rintro _ ⟨f, rfl⟩
  exact ⟨j f, hj f⟩

include hTop hT2 hLC in
/-- Any two structural pairs have a common upper bound. -/
private theorem bruhatStructuralPair_exists_ge (a b : BruhatStructuralPair G) :
    ∃ c : BruhatStructuralPair G, a ≤ c ∧ b ≤ c :=
  (bruhatStructuralPair_filtered (G := G)).2.directed a b

include hTop hT2 hLC in
/-- The ranges of the stage realizations, indexed by a pair and a presentation of
its quotient, form a directed family of submodules. -/
private theorem schwartzBruhatStageRealization_range_directed :
    Directed (· ≤ ·)
      (fun s : (a : BruhatStructuralPair G) × ElementaryLCAPresentation a.quotient ↦
        LinearMap.range (schwartzBruhatStageRealization s.1 s.2)) := fun s t ↦
  (bruhatStructuralPair_exists_ge s.1 t.1).elim fun c hc ↦
    ⟨⟨c, (BruhatStructuralPair.elementary c).some⟩,
      schwartzBruhatStageRealization_range_mono hc.1 s.2 _,
      schwartzBruhatStageRealization_range_mono hc.2 t.2 _⟩

include hTop hT2 hLC in
/-- Some structural pair with an elementary presentation exists. -/
private theorem schwartzBruhatStage_index_nonempty :
    Nonempty ((a : BruhatStructuralPair G) × ElementaryLCAPresentation a.quotient) :=
  (bruhatStructuralPair_filtered (G := G)).1.elim fun a ↦
    ⟨⟨a, (BruhatStructuralPair.elementary a).some⟩⟩

include hTop hT2 hLC

/-- Paper: Definition D.1.5.3(2), p. 762. A function belongs to the
Schwartz–Bruhat submodule exactly when a single structural pair and a single
elementary Schwartz function realize it. -/
theorem mem_schwartzBruhatSubmodule_iff (f : G → ℂ) :
    f ∈ schwartzBruhatSubmodule G ↔
      ∃ (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient)
        (s : SchwartzBruhatStage e), schwartzBruhatStageRealization a e s = f :=
  (mem_iSup₂_iff_of_directed_sigma
    (fun (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient) ↦
      LinearMap.range (schwartzBruhatStageRealization a e))
    (schwartzBruhatStage_index_nonempty (G := G))
    (schwartzBruhatStageRealization_range_directed (G := G)) f).trans
    (exists_congr fun _ ↦ exists_congr fun _ ↦ LinearMap.mem_range)

/-- Paper: (D.1.5.4), p. 763. The topology has the final locally convex property
for the canonical linear stage maps. -/
theorem schwartzBruhat_topology_eq_final :
    (inferInstance : TopologicalSpace (SchwartzBruhat G)) =
      locallyConvexFinalTopology
        (fun i : (a : BruhatStructuralPair G) × ElementaryLCAPresentation a.quotient ↦
          (show SchwartzBruhatStage i.2 →ₗ[ℂ] SchwartzBruhat G from
            schwartzBruhatStageInclusion i.1 i.2)) := by
  let E := schwartzBruhatSubmodule G
  have h (p : Seminorm ℂ E) :
      (∀ (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient),
        Continuous (p ∘ schwartzBruhatStageInclusion a e)) =
      (∀ i : (a : BruhatStructuralPair G) × ElementaryLCAPresentation a.quotient,
        Continuous (p ∘ schwartzBruhatStageInclusion i.1 i.2)) :=
    propext ⟨fun hp i ↦ hp i.1 i.2, fun hp a e ↦ hp ⟨a, e⟩⟩
  exact congrArg (fun P : Seminorm ℂ E → Prop ↦
    (SeminormFamily.moduleFilterBasis (Subtype.val : Subtype P → Seminorm ℂ E)).topology)
    (funext h)

-- TODO(paper-gap): Remark D.1.5.5 identifies global smooth functions with a
-- colimit of the smooth structural quotients. For the same extension-by-zero
-- maps, that colimit contains only functions supported in an open compactly
-- generated subgroup. The constant function 1 on discrete ℚ is smooth but
-- has no such support.

/-- Paper: Remark D.1.5.5, p. 763. Every Schwartz–Bruhat function is smooth in
the sense of Definition D.1.5.3(1). -/
theorem schwartzBruhat_isBruhatSmooth (f : SchwartzBruhat G) : IsBruhatSmooth f := by
  classical
  have hf := (mem_schwartzBruhatSubmodule_iff _).mp
    (show schwartzBruhatSubmodule G from f).property
  refine hf.elim fun a ha ↦ ha.elim fun d hd ↦ hd.elim fun s hs ↦ ?_
  intro p
  refine ⟨OrderDual.ofDual a.val.2, a.property.2.2.1, ?_, ?_⟩
  · intro h x
    rw [← hs]
    exact stage_realization_mul_kernel a d s h.property x
  · intro b hb
    -- Enlarge the open subgroup to contain both stages, keeping the original kernel.
    obtain ⟨H, haH, hbH⟩ := (openCompactlyGeneratedSubgroups_colimit (G := G)).1.directed
      ⟨a.val.1, a.property.1, a.property.2.1⟩ ⟨b.val.1, b.property.1, b.property.2.1⟩
    let c : BruhatStructuralPair G := ⟨(H.val, a.val.2), H.property.1, H.property.2,
      a.property.2.2.1, a.property.2.2.2.trans haH⟩
    let d' := Classical.choice c.elementary
    have htrans := schwartzBruhatStage_transition (show a ≤ c from ⟨haH, le_rfl⟩) d d'
    let t := htrans.choose s
    let inc := Subgroup.inclusion (show b.val.1 ≤ H.val from hbH)
    let j : b.quotient →* c.quotient := QuotientGroup.map _ _ inc (fun x hx ↦ hb ▸ hx)
    have hj : Continuous j := (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
      (QuotientGroup.continuous_mk.comp (continuous_subtype_val.subtype_mk _))
    refine ⟨fun q ↦ t (d'.equiv (j q)).toAdd, ?_, ?_⟩
    · intro x
      have hreal := congrFun ((htrans.choose_spec.1 s).trans hs) x.val
      simp only [j, QuotientGroup.map_mk]
      rw [schwartzBruhatStageRealization_apply, dite_eq_left (hbH x.property)] at hreal
      exact hreal
    · intro e z b'
      let L := AddMonoidHom.toMultiplicative.symm
        (d'.equiv.toMulEquiv.toMonoidHom.comp (j.comp e.equiv.symm.toMulEquiv.toMonoidHom))
      have hL : Continuous L := d'.equiv.continuous.comp (hj.comp e.equiv.symm.continuous)
      exact (contDiff_comp_elementaryHom L hL (f := t.val) t.property.1 z b').of_le
        (by exact_mod_cast le_top)

omit hTop hT2 hLC in
/-- A continuous character of a real vector space is the exponential of a linear form. -/
private theorem contDiff_vector_character {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (χ : PontryaginDual (Multiplicative E)) {p : ℕ∞} :
    ContDiff ℝ p (fun x : E ↦ (χ (Multiplicative.ofAdd x) : ℂ)) := by
  let e := AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0)
  have he (x : AddCircle (1 : ℝ)) : e x = x.toCircle := AddCircle.homeomorphCircle_apply _ x
  let a : E →+ AddCircle (1 : ℝ) :=
    { toFun := fun x ↦ e.symm (χ (Multiplicative.ofAdd x))
      map_zero' := e.injective (by rw [e.apply_symm_apply, he]; exact (map_one χ).trans AddCircle.toCircle_zero.symm)
      map_add' := fun x y ↦ e.injective (by
        rw [e.apply_symm_apply, he, AddCircle.toCircle_add, ← he, ← he, e.apply_symm_apply,
          e.apply_symm_apply]
        exact map_mul χ _ _) }
  have ha : Continuous a := e.symm.continuous.comp χ.continuous
  obtain ⟨l, hl⟩ := exists_addCircle_coe_linearMap_eq a ha
  have hχ (x : E) : (χ (Multiplicative.ofAdd x) : ℂ) =
      Complex.exp (↑(2 * Real.pi / 1 * l x) * Complex.I) := by
    have h := congrArg e (hl x)
    change e ((l x : ℝ) : AddCircle (1 : ℝ)) = e (e.symm _) at h
    rw [e.apply_symm_apply, he, AddCircle.toCircle_apply_mk] at h
    exact congrArg (fun t : Circle ↦ (t : ℂ)) h.symm
  simp_rw [hχ]
  exact ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul l.contDiff)).mul contDiff_const).cexp

omit hTop hT2 hLC in
/-- On each discrete fiber of an elementary group a character is a constant
multiple of its restriction to the vector cover at zero. -/
private theorem contDiff_elementary_character {m n r : ℕ} {F : Type*} [AddCommGroup F]
    [TopologicalSpace F] [DiscreteTopology F] (φ' : PontryaginDual (Multiplicative
      (ElementaryLieGroup m n r F))) (z : Fin r → ℤ) (b : F) {p : ℕ∞} :
    ContDiff ℝ p (fun u ↦ (φ' (Multiplicative.ofAdd (elementaryCover u z b)) : ℂ)) := by
  let c := elementaryCoverZeroHom (m := m) (n := n)
    (r := r) (F := F)
  let ψ' : PontryaginDual _ := φ'.comp
    ⟨AddMonoidHom.toMultiplicative c, elementaryCoverZeroHom_continuous_isOpenMap.1⟩
  have hshift u : c u + elementaryCover 0 z b = elementaryCover u z b := by
    simp [c, elementaryCoverZeroHom, elementaryCover, Pi.zero_def]
  change ContDiff ℝ _ (fun u ↦ (φ' (Multiplicative.ofAdd (elementaryCover u z b)) : ℂ))
  have heq u : (φ' (Multiplicative.ofAdd (elementaryCover u z b)) : ℂ) =
      (ψ' (Multiplicative.ofAdd u) : ℂ) * (φ' (Multiplicative.ofAdd (elementaryCover 0 z b)) : ℂ) := by
    rw [← hshift u, ofAdd_add, map_mul, Circle.coe_mul]
    rfl
  rw [show (fun u ↦ (φ' (Multiplicative.ofAdd (elementaryCover u z b)) : ℂ)) = _ from funext heq]
  exact (contDiff_vector_character ψ').mul contDiff_const

/-- Paper: Remark D.1.5.5, p. 763. A character restricts to a smooth function on
each open compactly generated subgroup. -/
theorem pontryaginDual_restriction_isBruhatSmooth (χ : PontryaginDual G)
    (J : OpenCompactlyGeneratedSubgroups G) :
    IsBruhatSmooth (fun x : J.val ↦ (χ x.val : ℂ)) := by
  let : LocallyCompactSpace J.val := J.property.1.isOpenEmbedding_subtypeVal.locallyCompactSpace
  let ψ : PontryaginDual J.val := χ.comp ⟨J.val.subtype, continuous_subtype_val⟩
  obtain ⟨H, hψ⟩ := (openCompactlyGeneratedSubgroups_colimit (G := PontryaginDual J.val)).2.1 ψ
  let k := lcaDualAnnihilator H.val
  have hk : IsBruhatGoodSubgroup k := ⟨(isCompact_lcaDualAnnihilator H.val H.property.1).isClosed,
    (lcaAnnihilator_dualAnnihilator_of_open H.val H.property.1).symm ▸ H.property⟩
  have hker {x : J.val} (hx : x ∈ k) : ψ x = 1 :=
    (mem_lcaDualAnnihilator_iff H.val x).mp hx ⟨ψ, hψ⟩
  intro p
  refine ⟨k, hk, fun h x ↦ ?_, fun a ha ↦ ?_⟩
  · change (↑(ψ (h.val * x)) : ℂ) = _
    rw [map_mul, hker h.property, one_mul]
    rfl
  · let φ := ψ.comp (⟨a.val.1.subtype, continuous_subtype_val⟩ : a.val.1 →ₜ* J.val)
    let N := (OrderDual.ofDual a.val.2).comap a.val.1.subtype
    let q : a.quotient →ₜ* Circle :=
      ⟨QuotientGroup.lift N φ.toMonoidHom (fun x hx ↦ hker (ha ▸ hx)),
        (QuotientGroup.isQuotientMap_mk N).continuous_iff.mpr φ.continuous⟩
    refine ⟨fun x ↦ (q x : ℂ), fun x ↦ rfl, fun e z b ↦ ?_⟩
    exact contDiff_elementary_character
      (q.comp ⟨e.equiv.symm.toMulEquiv.toMonoidHom, e.equiv.symm.continuous⟩) z b

omit hTop hT2 hLC in
/-- Point evaluations separate Schwartz–Bruhat functions for every group. -/
private theorem schwartzBruhat_t2_of_stages : T2Space (SchwartzBruhat G) := by
  refine T2Space.of_injective_continuous (f := fun f : SchwartzBruhat G ↦ f.val)
    (fun _ _ h ↦ Subtype.ext h) (continuous_pi fun x ↦ ?_)
  let ev : SchwartzBruhat G →ₗ[ℂ] ℂ :=
    (LinearMap.proj x).comp (schwartzBruhatSubmodule G).subtype
  let p : {p : Seminorm ℂ (schwartzBruhatSubmodule G) //
      ∀ (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient),
        Continuous (p ∘ schwartzBruhatStageInclusion a e)} :=
    ⟨(normSeminorm ℂ ℂ).comp ev, fun a e ↦ (continuous_schwartzBruhatStage_eval a e x).norm⟩
  exact (norm_withSeminorms ℂ ℂ).continuous_of_continuous_comp («E» := SchwartzBruhat G) ev
    fun _ ↦ (withGeneratingSeminorms_spec _ _).continuous_seminorm p

/-- Paper: Lemma D.1.5.6(1), p. 763. The final locally convex topology is Hausdorff
when the group is second countable. -/
theorem schwartzBruhat_t2 [SecondCountableTopology G] : T2Space (SchwartzBruhat G) :=
  schwartzBruhat_t2_of_stages

/-- Paper: Lemma D.1.5.6, p. 763. A compact exhaustion controls the open subgroups,
and shrinking identity neighborhoods control the kernels, since the elementary quotients
have no small subgroups. Together they give an increasing cofinal sequence. -/
private theorem exists_cofinal_bruhatStructuralPairs [SecondCountableTopology G] :
    ∃ b : ℕ → BruhatStructuralPair G, Monotone b ∧ ∀ a, ∃ n, a ≤ b n := by
  classical
  let C := CompactExhaustion.choice G
  obtain ⟨U, hU⟩ := (𝓝 (1 : G)).exists_antitone_basis
  choose H hH using fun n ↦ exists_openCompactlyGeneratedSubgroup_contains (C.isCompact n)
  choose A hA using fun n ↦ exists_lcaDualAnnihilator_subset_nhds
    (inter_mem (hU.mem n) ((H n).property.1.mem_nhds (H n).val.one_mem))
  let K (n : ℕ) := lcaDualAnnihilator (A n).val
  have hGood (n : ℕ) : IsBruhatGoodSubgroup (K n) := by
    refine ⟨(isCompact_lcaDualAnnihilator _ (A n).property.1).isClosed, ?_⟩
    rw [show lcaAnnihilator (K n) = (A n).val from
      lcaAnnihilator_dualAnnihilator_of_open _ (A n).property.1]
    exact (A n).property
  let b (n : ℕ) : BruhatStructuralPair G :=
    ⟨((H n).val, OrderDual.toDual (K n)), (H n).property.1, (H n).property.2,
      hGood n, fun _ hx ↦ (hA n hx).2⟩
  have hCofinal (a : BruhatStructuralPair G) : ∃ n, a ≤ b n := by
    obtain ⟨D, _, hDc, hDgen⟩ := a.property.2.1
    obtain ⟨m, hm⟩ := C.exists_superset_of_isCompact (hDc.image continuous_subtype_val)
    let : LocallyCompactSpace a.val.1 := a.property.1.isOpenEmbedding_subtypeVal.locallyCompactSpace
    let : T1Space a.quotient :=
      QuotientGroup.t1Space_iff.mpr (a.property.2.2.1.1.preimage continuous_subtype_val)
    obtain ⟨e⟩ := a.elementary
    obtain ⟨W, hW, hPow⟩ :=
      exists_nhds_one_of_isLocallyEuclidean (locallyEuclidean_of_elementaryPresentation e)
    let π : a.val.1 →* a.quotient := QuotientGroup.mk' _
    have hPre : π ⁻¹' W ∈ 𝓝 (1 : a.val.1) :=
      (QuotientGroup.continuous_mk (N := _) : Continuous π).continuousAt.preimage_mem_nhds
        (by change W ∈ 𝓝 (π 1); rwa [map_one])
    have hImage : Subtype.val '' (π ⁻¹' W) ∈ 𝓝 (1 : G) :=
      a.property.1.isOpenEmbedding_subtypeVal.isOpenMap.image_mem_nhds hPre
    obtain ⟨l, _, hl⟩ := hU.1.mem_iff.mp hImage
    let n := max m l
    refine ⟨n, ?_, ?_⟩
    · have hD : D ⊆ ((H n).val.comap a.val.1.subtype : Set a.val.1) :=
        fun x hx ↦ hH n (C.subset (le_max_left m l) (hm ⟨x, hx, rfl⟩))
      have htop : ⊤ ≤ (H n).val.comap a.val.1.subtype :=
        hDgen ▸ (Subgroup.closure_le _).mpr hD
      exact fun x hx ↦ htop (Subgroup.mem_top ⟨x, hx⟩)
    · have hSmall : (K n : Set G) ⊆ Subtype.val '' (π ⁻¹' W) :=
        fun _ hx ↦ hl (hU.2 (le_max_right m l) (hA n hx).1)
      intro x hx
      obtain ⟨y, _, rfl⟩ := hSmall hx
      apply (a.quotient_mk_eq_one y).mp
      change π y = 1
      apply hPow
      intro k
      rw [← map_pow]
      obtain ⟨z, hz, hzy⟩ := hSmall ((K n).pow_mem hx k)
      exact (Subtype.ext hzy : z = y ^ k) ▸ hz
  let := (bruhatStructuralPair_filtered (G := G)).2
  choose upper hleft hright using (exists_ge_ge (α := BruhatStructuralPair G))
  let chain : ℕ → BruhatStructuralPair G :=
    Nat.rec (b 0) fun n prev ↦ upper prev (b (n + 1))
  have hdom (n : ℕ) : b n ≤ chain n := by
    cases n with
    | zero => exact le_rfl
    | succ n => exact hright (chain n) (b (n + 1))
  exact ⟨chain, monotone_nat_of_le_succ fun n ↦ hleft (chain n) (b (n + 1)), fun a ↦ by
    obtain ⟨n, hn⟩ := hCofinal a
    exact ⟨n, hn.trans (hdom n)⟩⟩

omit hTop hT2 hLC in
/-- A stage function is determined by its realization because every elementary coordinate
is represented by a point in the open subgroup. -/
private theorem schwartzBruhatStageInclusion_injective (a : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation a.quotient) :
    Function.Injective (schwartzBruhatStageInclusion a e) := by
  exact fun _ _ h ↦ schwartzBruhatStageRealization_injective a e (congrArg Subtype.val h)

omit hTop hT2 hLC in
/-- A cofinal sequence with embedding transitions induces the same final locally convex
topology as the full system. Each stage embeds by factoring through a stage of that sequence. -/
private theorem isEmbedding_of_cofinal_lcStages {ι E : Type*}
    [AddCommGroup E] [Module ℂ E] [t : TopologicalSpace E] [IsTopologicalAddGroup E]
    {X : ι → Type*} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    [∀ a, TopologicalSpace (X a)] [∀ a, IsTopologicalAddGroup (X a)]
    [∀ a, PolynormableSpace ℂ (X a)]
    (inc : ∀ a, X a →ₗ[ℂ] E) (s : ℕ → ι)
    (hinj : ∀ n, Function.Injective (inc (s n)))
    (hex : ∀ x : E, ∃ a, x ∈ (inc a).range)
    (ht : t = locallyConvexFinalTopology inc)
    (hstep : ∀ n, ∃ j : X (s n) →L[ℂ] X (s (n + 1)),
      (∀ x, inc (s (n + 1)) (j x) = inc (s n) x) ∧ IsEmbedding j)
    (hfactor : ∀ a, ∃ n, ∃ j : X a →L[ℂ] X (s n),
      (∀ x, inc (s n) (j x) = inc a x) ∧ IsEmbedding j)
    (a : ι) : IsEmbedding (inc a) := by
  classical
  let stage (n : ℕ) := inc (s n)
  have htests : (fun q : Seminorm ℂ E ↦ ∀ a, Continuous (q ∘ inc a)) =
      (fun q : Seminorm ℂ E ↦ ∀ n, Continuous (q ∘ stage n)) := by
    funext q
    exact propext ⟨fun h n ↦ h (s n), fun h a ↦ by
      obtain ⟨n, j, hj, _⟩ := hfactor a
      exact ((h n).comp j.continuous).congr fun x ↦ congrArg q (hj x)⟩
  have ht' : t = locallyConvexFinalTopology stage :=
    ht.trans (congrArg (fun P : Seminorm ℂ E → Prop ↦
      (SeminormFamily.moduleFilterBasis (Subtype.val : Subtype P → Seminorm ℂ E)).topology) htests)
  have hseminorms : WithSeminorms
      (Subtype.val : {q : Seminorm ℂ E // ∀ n, Continuous (q ∘ stage n)} → Seminorm ℂ E) := ⟨ht'⟩
  let i (n : ℕ) : X (s n) →L[ℂ] E :=
    ⟨stage n, hseminorms.continuous_of_continuous_comp _ fun q ↦ q.property n⟩
  choose j hj hEmb using hstep
  have hlim : IsInjectiveLCLimit (X := fun n ↦ X (s n)) j i := by
    refine ⟨hinj, fun n ↦ ContinuousLinearMap.ext (hj n), ?_, ht'⟩
    intro x
    obtain ⟨c, y, rfl⟩ := hex x
    obtain ⟨n, k, hk, _⟩ := hfactor c
    exact ⟨n, k y, hk y⟩
  obtain ⟨n, k, hk, hkEmb⟩ := hfactor a
  have hcomp : (i n : X (s n) → E) ∘ k = inc a := funext hk
  exact hcomp ▸ (hlim.isEmbedding_stage hEmb n).comp hkEmb

/-- Paper: Lemma D.1.5.6(1), p. 763. Each structural stage inherits its intrinsic
topology from the final locally convex topology. -/
theorem schwartzBruhatStage_isEmbedding [SecondCountableTopology G]
    (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient) :
    IsEmbedding (show SchwartzBruhatStage e →ₗ[ℂ] SchwartzBruhat G from
      schwartzBruhatStageInclusion a e) := by
  classical
  let ι := (c : BruhatStructuralPair G) × ElementaryLCAPresentation c.quotient
  let X (c : ι) := SchwartzBruhatStage c.2
  let inc (c : ι) : X c →ₗ[ℂ] SchwartzBruhat G := schwartzBruhatStageInclusion c.1 c.2
  have hseq := exists_cofinal_bruhatStructuralPairs (G := G)
  let b := hseq.choose
  let s (n : ℕ) : ι := ⟨b n, Classical.choice (b n).elementary⟩
  have htransition (c c' : ι) (hc : c.1 ≤ c'.1) :
      ∃ j : X c →L[ℂ] X c', (∀ x, inc c' (j x) = inc c x) ∧ IsEmbedding j := by
    have h := schwartzBruhatStage_transition hc c.2 c'.2
    exact ⟨h.choose, fun x ↦ Subtype.ext (h.choose_spec.1 x), h.choose_spec.2.isEmbedding⟩
  refine isEmbedding_of_cofinal_lcStages (X := X) inc s
    (fun n ↦ schwartzBruhatStageInclusion_injective (s n).1 (s n).2)
    ?_ schwartzBruhat_topology_eq_final
    (fun n ↦ htransition (s n) (s (n + 1)) (hseq.choose_spec.1 (Nat.le_succ n))) ?_ ⟨a, e⟩
  · intro f
    have hf := (mem_schwartzBruhatSubmodule_iff _).mp
      (show schwartzBruhatSubmodule G from f).property
    exact hf.elim fun c hc ↦ hc.elim fun p hp ↦ hp.elim fun x hx ↦
      ⟨⟨c, p⟩, x, Subtype.ext hx⟩
  · intro c
    have hc := hseq.choose_spec.2 c.1
    exact ⟨hc.choose, htransition c (s hc.choose) hc.choose_spec⟩

omit hTop hT2 hLC in
/-- The inclusion of a stage is continuous by the definition of the generating seminorms. -/
private theorem continuous_schwartzBruhatStageInclusion
    (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient) :
    Continuous (show SchwartzBruhatStage e →ₗ[ℂ] SchwartzBruhat G from
      schwartzBruhatStageInclusion a e) := by
  exact (withGeneratingSeminorms_spec _ _).continuous_of_continuous_comp _ (fun p ↦ p.2 a e)

/-- The continuous linear inclusion of an elementary stage. -/
private def schwartzBruhatStageCLM (a : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation a.quotient) : SchwartzBruhatStage e →L[ℂ] SchwartzBruhat G :=
  ⟨schwartzBruhatStageInclusion a e, continuous_schwartzBruhatStageInclusion a e⟩

/-- A cofinal sequence of structural pairs with compatible transitions presents the
Schwartz–Bruhat space as a locally convex inductive limit. -/
private theorem schwartzBruhat_isInjectiveLCLimit
    (a : ℕ → BruhatStructuralPair G) (e : ∀ n, ElementaryLCAPresentation (a n).quotient)
    (hcof : ∀ b, ∃ n, b ≤ a n)
    (j : ∀ n, SchwartzBruhatStage (e n) →L[ℂ] SchwartzBruhatStage (e (n + 1)))
    (hj : ∀ n x, schwartzBruhatStageRealization (a (n + 1)) (e (n + 1)) (j n x) =
      schwartzBruhatStageRealization (a n) (e n) x) :
    IsInjectiveLCLimit j (fun n ↦ schwartzBruhatStageCLM (a n) (e n)) := by
  have hfactor (b : BruhatStructuralPair G) (d : ElementaryLCAPresentation b.quotient) :
      ∃ n, ∃ t : SchwartzBruhatStage d →L[ℂ] SchwartzBruhatStage (e n),
        ∀ x, schwartzBruhatStageCLM (a n) (e n) (t x) = schwartzBruhatStageCLM b d x := by
    let n := (hcof b).choose
    have h := schwartzBruhatStage_transition (hcof b).choose_spec d (e n)
    exact ⟨n, h.choose, fun x ↦ Subtype.ext (h.choose_spec.1 x)⟩
  refine ⟨fun n ↦ schwartzBruhatStageInclusion_injective _ _,
    fun n ↦ ContinuousLinearMap.ext (fun x ↦ Subtype.ext (hj n x)), ?_, ?_⟩
  · intro f
    have hf := (mem_schwartzBruhatSubmodule_iff _).mp
      (show schwartzBruhatSubmodule G from f).property
    refine hf.elim fun b hb ↦ hb.elim fun d hd ↦ hd.elim fun s hs ↦ ?_
    refine (hfactor b d).elim fun n hn ↦ hn.elim fun t ht ↦ ?_
    exact ⟨n, t s, (ht s).trans (Subtype.ext hs)⟩
  · apply congrArg (fun P : Seminorm ℂ (schwartzBruhatSubmodule G) → Prop ↦
      (SeminormFamily.moduleFilterBasis (Subtype.val : Subtype P → Seminorm ℂ _)).topology)
    funext p
    apply propext
    refine ⟨fun h n ↦ h (a n) (e n), fun h b d ↦ ?_⟩
    refine (hfactor b d).elim fun n hn ↦ hn.elim fun t ht ↦ ?_
    exact ((h n).comp t.continuous).congr fun x ↦ congrArg p (ht x)

/-- Choose a countable cofinal presentation with closed transition maps. -/
private theorem schwartzBruhat_exists_cofinal_system [SecondCountableTopology G] :
    ∃ (a : ℕ → BruhatStructuralPair G) (e : ∀ n, ElementaryLCAPresentation (a n).quotient)
      (j : ∀ n, SchwartzBruhatStage (e n) →L[ℂ] SchwartzBruhatStage (e (n + 1))),
      Monotone a ∧ (∀ b, ∃ n, b ≤ a n) ∧
      (∀ n f, schwartzBruhatStageRealization (a (n + 1)) (e (n + 1)) (j n f) =
        schwartzBruhatStageRealization (a n) (e n) f) ∧
      (∀ n, IsClosedEmbedding (j n)) ∧
      IsInjectiveLCLimit j (fun n ↦ schwartzBruhatStageCLM (a n) (e n)) := by
  have hs := exists_cofinal_bruhatStructuralPairs (G := G)
  let a := hs.choose
  let e (n : ℕ) := Classical.choice (a n).elementary
  have step (n : ℕ) := schwartzBruhatStage_transition
    (hs.choose_spec.1 (Nat.le_succ n)) (e n) (e (n + 1))
  let j (n : ℕ) := (step n).choose
  have hj (n : ℕ) := (step n).choose_spec.1
  exact ⟨a, e, j, hs.choose_spec.1, hs.choose_spec.2, hj, fun n ↦ (step n).choose_spec.2,
    schwartzBruhat_isInjectiveLCLimit a e hs.choose_spec.2 j hj⟩

/-- Paper: Lemma D.1.5.6(2), p. 763. Every bounded subset of the limit is
the image of a bounded subset of a single stage. -/
theorem schwartzBruhat_bounded_image_stage [SecondCountableTopology G]
    {B : Set (SchwartzBruhat G)} (hB : IsVonNBounded ℂ B) :
    ∃ (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient)
      (C : Set (SchwartzBruhatStage e)), IsVonNBounded ℂ C ∧
        (show SchwartzBruhatStage e →ₗ[ℂ] SchwartzBruhat G from
          schwartzBruhatStageInclusion a e) '' C = B := by
  have hs := schwartzBruhat_exists_cofinal_system (G := G)
  refine hs.elim fun a ha ↦ ha.elim fun e he ↦ he.elim fun j hj ↦ ?_
  let : ∀ n, T2Space (SchwartzBruhatStage (e n)) := fun _ ↦ elementarySchwartz_t2
  have hlift := (isVonNBounded_iff_bounded_stage hj.2.2.2.2 hj.2.2.2.1 B).mp hB
  exact hlift.elim fun n hn ↦ hn.elim fun C hC ↦ ⟨a n, e n, C, hC⟩

end SchwartzBruhat

section MainTheorems

universe v

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

/-- A seminorm continuous on all elementary stages belongs to the defining family. -/
private theorem schwartzBruhat_continuous_seminorm (p : Seminorm ℂ (SchwartzBruhat G))
    (hp : ∀ (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient),
      Continuous (p ∘ schwartzBruhatStageInclusion a e)) : Continuous p :=
  (withGeneratingSeminorms_spec _ (Subtype.val : {q : Seminorm ℂ (schwartzBruhatSubmodule G) //
    ∀ (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient),
      Continuous (q ∘ schwartzBruhatStageInclusion a e)} → _)).continuous_seminorm ⟨p, hp⟩

/-- Lower semicontinuous seminorms are continuous on each barrelled elementary stage. -/
private theorem schwartzBruhat_barrelled_of_stages : BarrelledSpace ℂ (SchwartzBruhat G) := by
  refine ⟨fun p hp ↦ schwartzBruhat_continuous_seminorm p ?_⟩
  intro a e
  let : BarrelledSpace ℂ (SchwartzBruhatStage e) := elementarySchwartz_barrelled
  exact (p.comp (schwartzBruhatStageInclusion a e)).continuous_of_lowerSemicontinuous
    (hp.comp (continuous_schwartzBruhatStageInclusion a e))

/-- Paper: Theorem D.1.5.7, p. 763. The Schwartz–Bruhat space is barrelled. -/
theorem schwartzBruhat_barrelled [SecondCountableTopology G] :
    BarrelledSpace ℂ (SchwartzBruhat G) := by
  exact schwartzBruhat_barrelled_of_stages

/-- Restrict a bounded seminorm along a continuous linear map from a first-countable stage. -/
private theorem continuous_stage_seminorm_of_bounded {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [FirstCountableTopology E]
    {F : Type*} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [ContinuousSMul ℂ F]
    (i : E →L[ℂ] F) (p : Seminorm ℂ F)
    (hp : ∀ B : Set F, IsVonNBounded ℂ B → BddAbove (p '' B)) :
    Continuous (p ∘ i) := by
  let L : E →ₗ[ℂ] WithLocalSeminorm p := i.toLinearMap
  have hL : Continuous L := by
    apply L.continuous_of_locally_bounded
    intro B hB
    obtain ⟨C, hC⟩ := hp (i '' B) (hB.image i)
    apply (NormedSpace.isVonNBounded_iff ℂ).mpr
    refine isBounded_iff_forall_norm_le.mpr ⟨C, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hC (mem_image_of_mem p (mem_image_of_mem i hx))
  exact hL.norm

/-- Paper: Theorem D.1.5.7 and Remark D.1.5.8, p. 764. The Schwartz–Bruhat space
is bornological, including beyond the second-countable case.
Deviation: We use the criterion that a seminorm bounded on every bounded set is continuous. -/
theorem schwartzBruhat_bornological :
    ∀ p : Seminorm ℂ (SchwartzBruhat G),
      (∀ B : Set (SchwartzBruhat G), IsVonNBounded ℂ B → BddAbove (p '' B)) →
        Continuous p := by
  intro p hp
  apply schwartzBruhat_continuous_seminorm
  intro a e
  let : MetrizableSpace (SchwartzBruhatStage e) := elementarySchwartz_isFrechet.choose_spec.2.1
  exact continuous_stage_seminorm_of_bounded (schwartzBruhatStageCLM a e) p hp

/-- The restrictions of a functional to the stages form a closed subspace of the
product of the strong duals, with topology induced by bounded lifting. -/
private theorem strongDual_closedEmbedding_of_strict_limit
    {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [T2Space E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [PolynormableSpace ℂ E]
    {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Module ℂ (X n)]
    [∀ n, TopologicalSpace (X n)] [∀ n, IsTopologicalAddGroup (X n)]
    [∀ n, ContinuousSMul ℂ (X n)] [∀ n, PolynormableSpace ℂ (X n)] [∀ n, T2Space (X n)]
    {j : ∀ n, X n →L[ℂ] X (n + 1)} {i : ∀ n, X n →L[ℂ] E}
    (h : IsInjectiveLCLimit j i) (hj : ∀ n, IsClosedEmbedding (j n)) :
    IsClosedEmbedding (fun (L : StrongDual ℂ E) n ↦ L.comp (i n)) := by
  have hd := dual_of_injectiveLCLimit h
  refine ⟨hd.2.2 (fun B hB ↦ ?_), ?_⟩
  · obtain ⟨n, A, hA, heq⟩ := (isVonNBounded_iff_bounded_stage h hj B).mp hB
    exact ⟨n, A, hA, heq.symm⟩
  · let D := (n : ℕ) → StrongDual ℂ (X n)
    have hrange : range (fun (L : StrongDual ℂ E) n ↦ L.comp (i n)) =
        ⋂ n, {l : D | (l (n + 1)).comp (j n) = l n} := by
      ext l
      constructor
      · rintro ⟨L, rfl⟩
        exact mem_iInter.mpr fun n ↦ ContinuousLinearMap.ext fun x ↦
          congrArg L (DFunLike.congr_fun (h.compatible n) x)
      · intro hl
        obtain ⟨L, hL, _⟩ := hd.1 l (mem_iInter.mp hl)
        exact ⟨L, funext hL⟩
    rw [hrange]
    apply isClosed_iInter
    intro n
    let t : StrongDual ℂ (X (n + 1)) →L[ℂ] StrongDual ℂ (X n) :=
      ContinuousLinearMap.precomp ℂ (j n)
    exact isClosed_eq (t.continuous.comp (continuous_apply (n + 1))) (continuous_apply n)

/-- Paper: Theorem D.1.5.7, p. 764. The strong dual of the Schwartz–Bruhat space
is complete. -/
theorem schwartzBruhat_strongDual_complete [SecondCountableTopology G] :
    CompleteSpace (StrongDual ℂ (SchwartzBruhat G)) := by
  let : T2Space (SchwartzBruhat G) := schwartzBruhat_t2
  have hs := schwartzBruhat_exists_cofinal_system (G := G)
  refine hs.elim fun a ha ↦ ha.elim fun e he ↦ he.elim fun j hj ↦ ?_
  let i n := schwartzBruhatStageCLM (a n) (e n)
  let : ∀ n, T2Space (SchwartzBruhatStage (e n)) := fun _ ↦ elementarySchwartz_t2
  let : ∀ n, CompleteSpace (StrongDual ℂ (SchwartzBruhatStage (e n))) :=
    fun _ ↦ elementarySchwartz_strongDual_complete
  let res : StrongDual ℂ (SchwartzBruhat G) →L[ℂ] ((n : ℕ) → StrongDual ℂ (SchwartzBruhatStage (e n))) :=
    ContinuousLinearMap.pi fun n ↦ ContinuousLinearMap.precomp ℂ (i n)
  have hr : IsClosedEmbedding res := strongDual_closedEmbedding_of_strict_limit hj.2.2.2.2 hj.2.2.2.1
  exact (completeSpace_iff_isComplete_range (AddMonoidHom.isUniformInducing_of_isInducing
    (f := res.toLinearMap.toAddMonoidHom) hr.isInducing)).mpr hr.isClosed_range.isComplete

open scoped TensorProduct in
/-- A topologically embedded linear subspace inherits nuclearity through the
continuous linear equivalence with its range. -/
private theorem schwartzBruhat_nuclear_of_embedding.{test, u} {X : Type u} {Y : Type}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    (f : X →ₗ[ℂ] Y) (hf : IsEmbedding f) (hY : IsNuclearTVS.{max test u, 0} Y) :
    IsNuclearTVS.{test, u} X := by
  let := hY.1
  let := hY.2.1
  let : PolynormableSpace ℂ X := hf.isInducing.polynormableSpace (f := f)
  have hn := isNuclearTVS_submodule hY f.range
  let e := LinearEquiv.ofInjective f hf.injective
  have he : IsInducing e := IsInducing.subtypeVal.of_comp_iff.mp hf.isInducing
  let h := e.toEquiv.toHomeomorphOfIsInducing he
  let L : X ≃L[ℂ] f.range := ⟨e, h.continuous, h.continuous_symm⟩
  have : T2Space X := hf.t2Space
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro F _ _ _ _ _
  let cmp := (hn.2.2 F inferInstance inferInstance inferInstance inferInstance
    inferInstance).homeomorph
  let idF := ContinuousLinearMap.id ℂ F
  have hroundtrip (z : X ⊗[ℂ] F) :
      L.symm.toLinearMap.rTensor F (L.toLinearMap.rTensor F z) = z := by
    rw [← LinearMap.rTensor_comp_apply, show L.symm.toLinearMap.comp L.toLinearMap =
      LinearMap.id from LinearMap.ext L.symm_apply_apply, LinearMap.rTensor_id_apply]
  have hforward : Continuous (show ProjectiveTensor X F → InjectiveTensor X F from id) :=
    ((injectiveTensorMap_continuous L.symm.toContinuousLinearMap idF).comp
      (cmp.continuous.comp (projectiveTensorMap_continuous L.toContinuousLinearMap idF))).congr
      hroundtrip
  have hcmp : Continuous (show InjectiveTensor f.range F → ProjectiveTensor f.range F from id) :=
    cmp.continuous_symm.congr fun z ↦ cmp.apply_symm_apply z
  have hback : Continuous (show InjectiveTensor X F → ProjectiveTensor X F from id) :=
    ((projectiveTensorMap_continuous L.symm.toContinuousLinearMap idF).comp
      (hcmp.comp (injectiveTensorMap_continuous L.toContinuousLinearMap idF))).congr hroundtrip
  exact (⟨Equiv.refl (X ⊗[ℂ] F), hforward, hback⟩ :
    ProjectiveTensor X F ≃ₜ InjectiveTensor X F).isHomeomorph

/-- The product of the one-dimensional summable lattice weights is summable
over every finite product of integer lattices. -/
private theorem summable_lattice_product {J : Type*} [Fintype J] :
    Summable (fun k : J → ℤ ↦ ∏ j, (1 + (k j : ℝ)^2)⁻¹) := by
  classical
  have h₁ : Summable (fun k : ℤ ↦ (1 + (k : ℝ)^2)⁻¹) := by
    have h := (Real.summable_one_div_int_pow (p := 2)).mpr (by norm_num)
    apply (summable_of_ne_finset_zero (s := ({0} : Finset ℤ)) (f := fun k : ℤ ↦ if k = 0 then (1:ℝ) else 0)
      (by simp)).add h |>.of_nonneg_of_le (fun _ ↦ by positivity)
    intro k
    by_cases hk : k = 0
    · simp [hk]
    · simp only [ite_eq_right hk, zero_add, one_div]
      exact inv_anti₀ (sq_pos_of_ne_zero (Int.cast_ne_zero.mpr hk)) (by linarith)
  have hFin (n : ℕ) : Summable (fun k : Fin n → ℤ ↦ ∏ i, (1 + (k i : ℝ)^2)⁻¹) := by
    induction n with
    | zero => exact .of_finite
    | succ n ih =>
      have h := h₁.mul_of_nonneg ih (fun _ ↦ by positivity) (fun _ ↦ Finset.prod_nonneg fun _ _ ↦ by positivity)
      apply (Fin.consEquiv (fun _ : Fin (n+1) ↦ ℤ)).summable_iff.mp
      simpa [Function.comp_def, Fin.prod_univ_succ, mul_comm] using h
  let e := Fintype.equivFin J
  let t := Equiv.arrowCongr e (Equiv.refl ℤ)
  apply (t.summable_iff.mpr (hFin (Fintype.card J))).congr
  intro k
  change (∏ i, (1 + (k (e.symm i) : ℝ)^2)⁻¹) = _
  exact e.symm.prod_comp (fun i ↦ (1 + (k i : ℝ)^2)⁻¹)

private def schwartzCubeWeight {J : Type*} [Fintype J] (d : J → ℕ) (k : J → ℤ) : ℝ :=
  ∏ j, ((2 * (1 + (k j : ℝ)^2))^(d j) * (1 + (k j : ℝ)^2))

private def schwartzCubePolynomial {J : Type*} [Fintype J] (d : J → ℕ) : MvPolynomial J ℂ :=
  ∏ j, (8 * (1 + MvPolynomial.X j ^ 2))^(d j + 1)

/-- A single positive polynomial controls the lattice weight throughout the unit cube. -/
private theorem schwartzCubeWeight_le {J : Type*} [Fintype J] (d : J → ℕ) (k : J → ℤ)
    (x : J → ℝ) (hx : ∀ j, (k j : ℝ) ≤ x j ∧ x j ≤ k j + 1) :
    schwartzCubeWeight d k ≤ ‖MvPolynomial.eval (fun j ↦ (x j : ℂ)) (schwartzCubePolynomial d)‖ := by
  unfold schwartzCubeWeight schwartzCubePolynomial
  rw [map_prod, norm_prod]
  apply Finset.prod_le_prod₀ (fun j _ ↦ by positivity) (fun j _ ↦ ?_)
  have hpos : 0 ≤ 8 * (1 + x j ^ 2) := by positivity
  have he : MvPolynomial.eval (fun j ↦ (x j : ℂ)) (8 * (1 + MvPolynomial.X j ^ 2)) =
      ((8 * (1 + x j ^ 2) : ℝ) : ℂ) := by simp
  rw [map_pow, he, norm_pow, Complex.norm_real, Real.norm_of_nonneg hpos, pow_succ]
  have hsmall : (k j : ℝ)^2 ≤ 2*x j^2 + 2 := by
    have hl := mul_nonneg (sub_nonneg.mpr (hx j).1) (sub_nonneg.mpr (hx j).2)
    nlinarith [sq_nonneg (x j - ((k j : ℝ) - x j))]
  have h₁ : 0 ≤ 2 * (1 + (k j : ℝ)^2) := by positivity
  have h₂ : 2 * (1+(k j : ℝ)^2) ≤ 8*(1+x j^2) := by linarith [sq_nonneg (x j)]
  exact mul_le_mul (pow_le_pow_left₀ h₁ h₂ (d j)) (by linarith [sq_nonneg (k j : ℝ)]) (by exact add_nonneg zero_le_one (sq_nonneg (k j : ℝ))) (pow_nonneg hpos _)

/-- Multiplying by a coordinate monomial spends only the polynomial part of the
weight, leaving a summable factor on the cube labels. -/
private theorem schwartzCube_monomial_weight {J : Type*} [Fintype J] (d : J → ℕ) (k : J → ℤ)
    (x : J → ℝ) (hx : ∀ j, (k j : ℝ) ≤ x j ∧ x j ≤ k j + 1) :
    (∏ j, |x j|^d j) ≤ (∏ j, (1 + (k j : ℝ)^2)⁻¹) * schwartzCubeWeight d k := by
  rw [schwartzCubeWeight, ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod₀ (fun _ _ ↦ by positivity) (fun j _ ↦ ?_)
  rw [mul_left_comm, inv_mul_cancel₀ (by positivity), mul_one]
  apply pow_le_pow_left₀ (abs_nonneg _) (abs_le.mpr ⟨?_,?_⟩)
  · linarith [(hx j).1, sq_nonneg ((k j : ℝ)+1), sq_nonneg (k j : ℝ)]
  · linarith [(hx j).2, sq_nonneg ((k j : ℝ)-1), sq_nonneg (k j : ℝ)]

/-- Choosing the opposite phase at each value of a functional realizes the sum
of their norms as the norm of one signed sum. -/
private theorem sum_norm_linear_signed {E : Type*} [AddCommGroup E] [Module ℂ E]
    (L : E →ₗ[ℂ] ℂ) {n : ℕ} (f : Fin n → E) :
    ∃ c : Fin n → ℂ, (∀ i, ‖c i‖ ≤ 1) ∧ ∑ i, ‖L (f i)‖ = ‖L (∑ i, c i • f i)‖ := by
  let c (i) : ℂ := (‖L (f i)‖ : ℂ) / L (f i)
  have hc (i) : ‖c i‖ ≤ 1 := by
    change ‖(‖L (f i)‖ : ℂ) / L (f i)‖ ≤ 1
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
    exact div_self_le_one _
  have he (i) : c i * L (f i) = (‖L (f i)‖ : ℂ) := by
    by_cases h : L (f i) = 0
    · simp [c,h]
    · exact div_mul_cancel₀ _ h
  refine ⟨c,hc,?_⟩
  simp only [map_sum, map_smul, smul_eq_mul, he, ← Complex.ofReal_sum, Complex.norm_real,
    Real.norm_of_nonneg (Finset.sum_nonneg fun i _ ↦ norm_nonneg _)]

/-- Each polynomially weighted directional derivative admits a neighborhood
bound for the sum of absolute evaluations at a common point. -/
private theorem elementary_signed_point_bound {m n r : ℕ} {F : Type}
    [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
    (p : MvPolynomial (Fin m ⊕ Fin r) ℂ)
    (v : List (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n))) :
    ∃ U ∈ 𝓝 (0 : ElementarySchwartz m n r F), ∀ (N : ℕ) (f : Fin N → ElementarySchwartz m n r F),
      (∀ c : Fin N → ℂ, (∀ i, ‖c i‖ ≤ 1) → ∑ i, c i • f i ∈ U) →
      ∀ x a b, ‖MvPolynomial.eval (Sum.elim (fun i ↦ (x.1 i : ℂ)) (fun j ↦ (a j : ℂ))) p‖ *
        ∑ i, ‖listDerivative (fun y ↦ f i (elementaryCover y a b)) v x‖ ≤ 1 := by
  classical
  let E := ElementarySchwartz m n r F
  obtain ⟨T, c, hT⟩ := elementary_iterated_expansion (r := r) (F := F) v.get
  choose q hq hqp using fun t : (Fin m → ℕ) × (Fin n → ℕ) ↦
    elementarySchwartz_polynomial_weight_continuous_seminorm (F := F) p t.1 t.2
  let Q : Seminorm ℂ E := ∑ t ∈ T, ‖c t‖₊ • q t
  have hQ : Continuous Q := Seminorm.continuous_finsetSum fun t _ ↦ (hq t).const_smul _
  refine ⟨Q.ball 0 1, Q.ball_mem_nhds hQ zero_lt_one, fun N f hcomb x a b ↦ ?_⟩
  let w := MvPolynomial.eval (Sum.elim (fun i ↦ (x.1 i : ℂ)) (fun j ↦ (a j : ℂ))) p
  choose L hL using fun t : (Fin m → ℕ) × (Fin n → ℕ) ↦
    elementaryPartial_evaluation_continuousLinear (F := F) t.1 t.2 x a b
  let D : E →ₗ[ℂ] ℂ := ∑ t ∈ T, (c t : ℂ) • (L t).toLinearMap
  have hD (s : E) : D s = listDerivative (fun y ↦ s (elementaryCover y a b)) v x := by
    rw [listDerivative, hT s.val a b (s.property.1 a b) x]
    simp [D, hL, Complex.real_smul]
  have hle (s : E) : ‖w‖ * ‖D s‖ ≤ Q s := by
    have hqv (t) : ‖w‖ * ‖L t s‖ ≤ q t s := by
      rw [hL]
      apply (ENNReal.ofReal_le_ofReal_iff (apply_nonneg _ _)).mp
      rw [hqp]
      exact le_iSup_of_le x (le_iSup_of_le a (le_iSup_of_le b le_rfl))
    change _ ≤ FunLike.coeAddMonoidHom _ _ _ (∑ t ∈ T, ‖c t‖₊ • q t) s
    rw [map_sum, Finset.sum_apply]
    simp only [D, LinearMap.sum_apply, LinearMap.smul_apply, ContinuousLinearMap.coe_coe]
    apply (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg w)).trans
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun t ht ↦ ?_
    rw [norm_smul, Complex.norm_real, mul_left_comm]
    exact mul_le_mul_of_nonneg_left (hqv t) (norm_nonneg _)
  obtain ⟨c', hc', hsum⟩ := sum_norm_linear_signed D f
  change ‖w‖ * _ ≤ _
  simp_rw [← hD, hsum]
  exact (hle _).trans (Q.mem_ball_zero.mp (hcomb c' hc')).le

/-- Assemble the real and torus coordinates of one unit cube. -/
private def schwartzCubeMap (m n : ℕ) : ((Fin m ⊕ Fin n) → ℝ) →L[ℝ]
    EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) :=
  let getR := ContinuousLinearMap.pi (fun i : Fin m ↦ ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m ⊕ Fin n ↦ ℝ) (.inl i))
  let getT := ContinuousLinearMap.pi (fun j : Fin n ↦ ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m ⊕ Fin n ↦ ℝ) (.inr j))
  (((EuclideanSpace.equiv (Fin m) ℝ).symm.toContinuousLinearMap).comp getR).prod
    (((EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap).comp getT)

private def schwartzCubeOrigin {m n r : ℕ} (k : (Fin m ⊕ Fin r) → ℤ) :
    EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) :=
  (WithLp.toLp 2 (fun i ↦ (k (.inl i) : ℝ)),0)

/-- On each real cube and lattice fibre a fixed extra polynomial weight
controls the sum of mixed partials even at independently chosen points. -/
private theorem elementary_signed_cube_bound {m n r : ℕ} {F : Type}
    [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
    (d : (Fin m ⊕ Fin r) → ℕ) (v : List (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n))) :
    ∃ U ∈ 𝓝 (0 : ElementarySchwartz m n r F), ∀ (N : ℕ) (f : Fin N → ElementarySchwartz m n r F),
      (∀ c : Fin N → ℂ, (∀ i, ‖c i‖ ≤ 1) → ∑ i, c i • f i ∈ U) →
      ∀ (k : (Fin m ⊕ Fin r) → ℤ) b (u : Fin N → (Fin m ⊕ Fin n) → ℝ), (∀ i j, u i j ∈ Icc 0 1) →
      ∑ i, ‖listDerivative (fun x ↦ f i (elementaryCover x (fun j ↦ k (.inr j)) b)) v
        (schwartzCubeOrigin k + schwartzCubeMap m n (u i))‖ ≤ 2^Fintype.card (Fin m ⊕ Fin n) / schwartzCubeWeight d k := by
  classical
  let J := Fin m ⊕ Fin n
  let A := schwartzCubeMap m n
  let p := schwartzCubePolynomial d
  choose U hU he using fun l : List J ↦ elementary_signed_point_bound (F := F) p (l.map (fun j ↦ A (Pi.single j 1)) ++ v)
  let T := {l : List J | l.length ≤ Fintype.card J}
  refine ⟨⋂ l ∈ T, U l, (Filter.biInter_mem (List.finite_length_le J _)).mpr fun l _ ↦ hU l, fun N f hc k b u hu ↦ ?_⟩
  let origin := schwartzCubeOrigin (n := n) k
  let z (j : Fin r) := k (.inr j)
  have hW : 0 < schwartzCubeWeight d k := Finset.prod_pos fun _ _ ↦ by positivity
  rw [div_eq_mul_inv]
  apply sum_norm_of_cube_bounds A origin _ (fun i ↦ (f i).property.1 z b) v _ _ u hu
  intro l hl x hx
  let y := origin + A x
  let coord := Sum.elim (fun i : Fin m ↦ y.1 i) (fun j : Fin r ↦ (z j : ℝ))
  have hcoord (j) : (k j : ℝ) ≤ coord j ∧ coord j ≤ k j + 1 := by
    cases j with
    | inl i =>
      change (k (.inl i) : ℝ) ≤ (k (.inl i) : ℝ) + x (.inl i) ∧ (k (.inl i) : ℝ) + x (.inl i) ≤ k (.inl i) + 1
      constructor <;> linarith [(hx (.inl i)).1,(hx (.inl i)).2]
    | inr j => change (k (.inr j) : ℝ) ≤ k (.inr j) ∧ (k (.inr j) : ℝ) ≤ k (.inr j) + 1; exact ⟨le_rfl, by linarith⟩
  have hC := he l N f (fun c hc' ↦ mem_iInter₂.mp (hc c hc') l hl) y z b
  have hw := schwartzCubeWeight_le d k coord hcoord
  have hz : (fun j ↦ (coord j : ℂ)) = Sum.elim (fun i ↦ (y.1 i : ℂ)) (fun j ↦ (z j : ℂ)) := by
    funext j
    cases j with
    | inl i => rfl
    | inr i => exact Complex.ofReal_intCast _
  rw [hz] at hw
  rw [← mul_one (schwartzCubeWeight d k)⁻¹]
  apply (le_inv_mul_iff₀ hW).mpr
  exact (mul_le_mul_of_nonneg_right hw (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)).trans hC

/-- Each elementary seminorm can be estimated at one lifted point up to a
factor of two. The zero seminorm value permits any point. -/
private theorem elementary_some_weighted_value {m n r : ℕ} {F : Type}
    [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
    (i : ElementarySchwartzIndex m n r) (f : ElementarySchwartz m n r F) :
    ∃ x a b, elementarySchwartzSeminorm i f ≤ 2 * ‖((∏ j, (x.1 j : ℂ)^i.1 j) *
      (∏ j, (a j : ℂ)^i.2.2.2 j)) * elementaryPartial f i.2.1 i.2.2.1 x a b‖ := by
  let q := elementarySchwartzSeminorm i f
  by_cases h : q = 0
  · refine ⟨0,0,0,?_⟩
    change q ≤ _
    rw [h]
    positivity
  by_contra! hu
  have hle : elementarySchwartzBound f.val i ≤ ENNReal.ofReal (q/2) := by
    refine iSup_le fun x ↦ iSup_le fun a ↦ iSup_le fun b ↦ ?_
    rw [← ENNReal.ofReal_coe_nnreal]
    apply ENNReal.ofReal_le_ofReal
    rw [le_div_iff₀ (by norm_num : (0:ℝ)<2), mul_comm]
    exact (hu x a b).le
  have hq := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
  have hqpos : 0 ≤ q / 2 := div_nonneg (apply_nonneg _ _) (by norm_num)
  rw [ENNReal.toReal_ofReal hqpos] at hq
  change q ≤ q / 2 at hq
  exact h (le_antisymm (by linarith) (apply_nonneg _ _))

/-- Regroup a finite sum by labels and dominate it by a summable majorant. -/
private theorem sum_le_tsum_of_label {N : ℕ} {T : Type*} [DecidableEq T] (label : Fin N → T) (f : Fin N → ℝ)
    (g : T → ℝ) (hg : Summable g) (hpos : ∀ t, 0 ≤ g t)
    (h : ∀ t, ∑ i ∈ Finset.univ.filter (fun i ↦ label i = t), f i ≤ g t) :
    ∑ i, f i ≤ ∑' t, g t := by
  classical
  let S := Finset.univ.image label
  rw [← Finset.sum_fiberwise_of_maps_to (t := S) (fun i hi ↦ Finset.mem_image_of_mem label hi)]
  exact (Finset.sum_le_sum fun t _ ↦ h t).trans (hg.sum_le_tsum S (fun t _ ↦ hpos t))

/-- Each seminorm of an elementary Schwartz space satisfies the absolute
summability estimate on a suitable neighborhood of signed sums. -/
private theorem elementary_seminorm_signed_bound {m n r : ℕ} {F : Type}
    [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
    (idx : ElementarySchwartzIndex m n r) :
    ∃ U ∈ 𝓝 (0 : ElementarySchwartz m n r F), ∃ C : ℝ, 0 ≤ C ∧
      ∀ (N : ℕ) (f : Fin N → ElementarySchwartz m n r F),
        (∀ c : Fin N → ℂ, (∀ i, ‖c i‖ ≤ 1) → ∑ i, c i • f i ∈ U) →
          ∑ i, elementarySchwartzSeminorm idx (f i) ≤ C := by
  classical
  let J := Fin m ⊕ Fin n
  let K := Fin m ⊕ Fin r
  let X := EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
  let d : K → ℕ := Sum.elim idx.1 idx.2.2.2
  let v : List X := (List.ofFn fun j ↦ List.replicate (idx.2.1 j) (EuclideanSpace.single j 1,0)).flatten ++
    (List.ofFn fun j ↦ List.replicate (idx.2.2.1 j) (0,EuclideanSpace.single j 1)).flatten
  let dec (k : K → ℤ) := ∏ j, (1 + (k j : ℝ)^2)⁻¹
  have hdec : Summable dec := summable_lattice_product
  have hdec0 (k) : 0 ≤ dec k := Finset.prod_nonneg fun _ _ ↦ by positivity
  let B : ℝ := 2^Fintype.card J
  let g (w : (K → ℤ) × F) := (2*B) * dec w.1
  have hg : Summable g := by
    have hs := hdec.mul_of_nonneg (show Summable (fun _ : F ↦ (1:ℝ)) from .of_finite) hdec0 (fun _ ↦ zero_le_one)
    simpa only [g,mul_one] using hs.mul_left (2*B)
  have hpos (w) : 0 ≤ g w := mul_nonneg (by positivity) (hdec0 w.1)
  obtain ⟨U,hU,hC⟩ := elementary_signed_cube_bound (F := F) d v
  refine ⟨U,hU,∑' w, g w, tsum_nonneg hpos, fun N f hc ↦ ?_⟩
  choose x a b hv using fun i ↦ elementary_some_weighted_value idx (f i)
  let k (i : Fin N) : K → ℤ := Sum.elim (fun j ↦ ⌊(x i).1 j⌋) (a i)
  let u (i : Fin N) : J → ℝ := Sum.elim (fun j ↦ Int.fract ((x i).1 j)) (fun j ↦ Int.fract ((x i).2 j))
  have hu (i j) : u i j ∈ Icc 0 1 := by
    cases j <;> exact ⟨Int.fract_nonneg _,(Int.fract_lt_one _).le⟩
  let y (i : Fin N) := schwartzCubeOrigin (n := n) (k i) + schwartzCubeMap m n (u i)
  have hyR (i j) : (y i).1 j = (x i).1 j := by
    change (⌊(x i).1 j⌋ : ℝ) + Int.fract ((x i).1 j) = _
    exact Int.floor_add_fract _
  have hycover (i) : elementaryCover (x i) (a i) (b i) = elementaryCover (y i) (a i) (b i) := by
    refine Prod.ext (by ext j; exact (hyR i j).symm) (Prod.ext (funext fun j ↦ ?_) rfl)
    change (((x i).2 j : ℝ) : AddCircle (1:ℝ)) = ((0 + Int.fract ((x i).2 j) : ℝ) : AddCircle (1:ℝ))
    simp
  let D (w : (K → ℤ) × F) (i : Fin N) := ‖listDerivative
    (fun t ↦ f i (elementaryCover t (fun j ↦ w.1 (.inr j)) w.2)) v
    (schwartzCubeOrigin w.1 + schwartzCubeMap m n (u i))‖
  let label (i : Fin N) := (k i,b i)
  have htest (i) : elementarySchwartzSeminorm idx (f i) ≤ 2 * (dec (k i) * schwartzCubeWeight d (k i)) * D (label i) i := by
    have hpartial := (elementaryPartial_descends (f i).val idx.2.1 idx.2.2.1 (a i) (b i)
      ((f i).property.1 (a i) (b i))).2 _ _ (hycover i)
    have hmul : ‖(∏ j, ((x i).1 j : ℂ)^idx.1 j) * (∏ j, (a i j : ℂ)^idx.2.2.2 j)‖ ≤
        dec (k i) * schwartzCubeWeight d (k i) := by
      let z : K → ℝ := Sum.elim (fun j ↦ (x i).1 j) (fun j ↦ (a i j : ℝ))
      have hz (j) : (k i j : ℝ) ≤ z j ∧ z j ≤ k i j + 1 := by
        cases j with
        | inl j => exact ⟨Int.floor_le _, (Int.lt_floor_add_one _).le⟩
        | inr j => exact ⟨le_rfl, le_add_of_nonneg_right zero_le_one⟩
      have h := schwartzCube_monomial_weight d (k i) z hz
      rw [Fintype.prod_sum_type] at h
      simpa [norm_mul, norm_prod, norm_pow, Complex.norm_real, Complex.norm_intCast, Real.norm_eq_abs, d,z,dec] using h
    have hv' := hv i
    change elementarySchwartzSeminorm idx (f i) ≤ 2 * ‖_ * elementaryPartial (f i).val idx.2.1 idx.2.2.1 (x i) (a i) (b i)‖ at hv'
    rw [norm_mul, hpartial, ← mul_assoc] at hv'
    exact hv'.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmul (by norm_num)) (norm_nonneg _))
  refine sum_le_tsum_of_label label _ g hg hpos (fun w ↦ ?_)
  let S := Finset.univ.filter (fun i ↦ label i = w)
  have hW : 0 < schwartzCubeWeight d w.1 := Finset.prod_pos fun _ _ ↦ by positivity
  have hle : ∑ i ∈ S, elementarySchwartzSeminorm idx (f i) ≤ ∑ i ∈ S, (2*(dec w.1 * schwartzCubeWeight d w.1)) * D w i := by
    refine Finset.sum_le_sum fun i hi ↦ ?_
    have he := (Finset.mem_filter.mp hi).2
    have hk : k i = w.1 := congrArg Prod.fst he
    calc
      _ ≤ 2 * (dec (k i) * schwartzCubeWeight d (k i)) * D (label i) i := htest i
      _ = _ := congrArg₂ (· * ·) (congrArg (fun k ↦ 2 * (dec k * schwartzCubeWeight d k)) hk) (congrArg (fun w ↦ D w i) he)
  rw [← Finset.mul_sum] at hle
  have hnn : 0 ≤ 2 * (dec w.1 * schwartzCubeWeight d w.1) := mul_nonneg (by norm_num) (mul_nonneg (hdec0 _) hW.le)
  have hsub : ∑ i ∈ S, D w i ≤ ∑ i, D w i := Finset.sum_le_univ_sum_of_nonneg fun i ↦ norm_nonneg _
  refine hle.trans ((mul_le_mul_of_nonneg_left hsub hnn).trans ?_)
  have hs : ∑ i, D w i ≤ B / schwartzCubeWeight d w.1 := hC N f hc w.1 w.2 u hu
  refine (mul_le_mul_of_nonneg_left hs hnn).trans_eq ?_
  change _ = 2 * B * dec w.1
  field_simp

/-- It suffices to check the signed-sum criterion on a generating family of
seminorms: the bounds are stable under sums, nonnegative multiples and domination. -/
private theorem nuclear_of_generating_signed_bounds {E I : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [T2Space E] [PolynormableSpace ℂ E] (p : I → Seminorm ℂ E)
    (hp : WithSeminorms p) (h : ∀ i, ∃ U ∈ 𝓝 (0 : E), ∃ C : ℝ, 0 ≤ C ∧
      ∀ (N : ℕ) (f : Fin N → E), (∀ c : Fin N → ℂ, (∀ i, ‖c i‖ ≤ 1) → ∑ i, c i • f i ∈ U) →
        ∑ j, p i (f j) ≤ C) : IsNuclearTVS.{v} E := by
  let P (q : Seminorm ℂ E) := ∃ U ∈ 𝓝 (0 : E), ∃ C : ℝ, 0 ≤ C ∧
    ∀ (N : ℕ) (f : Fin N → E), (∀ c : Fin N → ℂ, (∀ i, ‖c i‖ ≤ 1) → ∑ i, c i • f i ∈ U) →
        ∑ j, q (f j) ≤ C
  apply isNuclearTVS_of_signedSum_bound
  intro q hq
  apply hp.induction_add_of_continuous (motive := P) h _ _ _ _ hq
  · exact ⟨univ,univ_mem,0,le_rfl,by simp⟩
  · intro p q hp hq
    obtain ⟨U,hU,C,hC,hu⟩ := hp
    obtain ⟨V,hV,D,hD,hv⟩ := hq
    refine ⟨U ∩ V,inter_mem hU hV,C+D,add_nonneg hC hD,fun N f h ↦ ?_⟩
    simpa only [add_apply, Finset.sum_add_distrib] using add_le_add
      (hu N f fun c hc ↦ (h c hc).1) (hv N f fun c hc ↦ (h c hc).2)
  · rintro p q hp ⟨U,hU,C,hC,h⟩
    exact ⟨U,hU,C,hC,fun N f hc ↦ (Finset.sum_le_sum (fun i _ ↦ hp (f i))).trans (h N f hc)⟩
  · rintro p t ⟨U,hU,C,hC,h⟩
    refine ⟨U,hU,t*C,mul_nonneg t.property hC,fun N f hc ↦ ?_⟩
    change (∑ j, (t : ℝ) * p (f j)) ≤ _
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (h N f hc) t.property

/-- Smoothness controls independent evaluations on each unit cube, and rapid
decay makes the resulting cube bounds summable. -/
private theorem elementarySchwartz_nuclear {m n r : ℕ} {F : Type} [AddCommGroup F]
    [TopologicalSpace F] [DiscreteTopology F] [Finite F] :
    IsNuclearTVS.{v} (ElementarySchwartz m n r F) := by
  let : T2Space (ElementarySchwartz m n r F) := elementarySchwartz_t2
  exact nuclear_of_generating_signed_bounds elementarySchwartzSeminorm elementarySchwartz_withSeminorms
    elementary_seminorm_signed_bound

/-- A strict inductive sequence of nuclear Fréchet stages is nuclear, using
the images of its embeddings as the increasing submodule presentation. -/
private theorem nuclear_of_injective_frechet_sequence.{u} {E : Type u} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [T2Space E] [PolynormableSpace ℂ E]
    {X : ℕ → Type} [∀ n, AddCommGroup (X n)] [∀ n, Module ℂ (X n)] [∀ n, TopologicalSpace (X n)]
    (hX : ∀ n, IsFrechetTVS (X n)) (hn : ∀ n, IsNuclearTVS.{max v u} (X n))
    (j : ∀ n, X n →L[ℂ] X (n+1)) (i : ∀ n, X n →L[ℂ] E)
    (h : IsInjectiveLCLimit j i) (hj : ∀ n, IsEmbedding (j n)) : IsNuclearTVS.{v} E := by
  let : ∀ n, IsTopologicalAddGroup (X n) := fun n ↦ (hX n).choose
  let : ∀ n, PolynormableSpace ℂ (X n) := fun n ↦ (hX n).choose_spec.1
  let S (n) := (i n).toLinearMap.range
  let e (n) : X n ≃ₗ[ℂ] S n := LinearEquiv.ofInjective _ (h.injective n)
  have he (n) : IsInducing (e n) := IsInducing.subtypeVal.of_comp_iff.mp
    (show IsInducing (Subtype.val ∘ e n) from (h.isEmbedding_stage hj n).isInducing)
  let L (n) : X n ≃L[ℂ] S n :=
    ⟨e n,(he n).continuous,((e n).toEquiv.toHomeomorphOfIsInducing (he n)).continuous_symm⟩
  apply isNuclearTVS_of_strictLF_stages S
  · apply monotone_nat_of_le_succ
    rintro n _ ⟨x,rfl⟩
    exact ⟨j n x, DFunLike.congr_fun (h.compatible n) x⟩
  · intro n
    let : MetrizableSpace (X n) := (hX n).choose_spec.2.1
    let : UniformSpace (X n) := IsTopologicalAddGroup.rightUniformSpace (X n)
    let : IsUniformAddGroup (X n) := isUniformAddGroup_of_addCommGroup
    let : UniformSpace (S n) := IsTopologicalAddGroup.rightUniformSpace (S n)
    let : IsUniformAddGroup (S n) := isUniformAddGroup_of_addCommGroup
    refine ⟨inferInstance, inferInstance, (L n).symm.toHomeomorph.isEmbedding.metrizableSpace, ?_⟩
    exact ((AddMonoidHom.isUniformInducing_of_isInducing (f := (L n).toLinearMap.toAddMonoidHom)
      (he n)).completeSpace_congr (L n).surjective).mp (hX n).choose_spec.2.2
  · intro n
    exact schwartzBruhat_nuclear_of_embedding (L n).symm.toLinearMap (L n).symm.toHomeomorph.isEmbedding (hn n)
  · exact h.exhaustive
  · refine h.topology_eq.trans ?_
    apply congrArg (fun P : Seminorm ℂ E → Prop ↦
      (SeminormFamily.moduleFilterBasis (Subtype.val : Subtype P → Seminorm ℂ E)).topology)
    funext p
    apply propext
    exact ⟨fun hp n ↦ (hp n).comp (L n).symm.continuous |>.congr (fun x ↦ congrArg p (congrArg Subtype.val ((L n).apply_symm_apply x))),
      fun hp n ↦ (hp n).comp (L n).continuous⟩

/-- Paper: Theorem D.1.5.7, p. 764. The Schwartz–Bruhat space of a second-countable
group is nuclear. -/
theorem schwartzBruhat_nuclear [SecondCountableTopology G] :
    IsNuclearTVS.{v} (SchwartzBruhat G) := by
  let : T2Space (SchwartzBruhat G) := schwartzBruhat_t2
  refine (schwartzBruhat_exists_cofinal_system (G := G)).elim fun a ha ↦ ha.elim fun e he ↦ he.elim fun j hj ↦ ?_
  exact nuclear_of_injective_frechet_sequence (fun _ ↦ elementarySchwartz_isFrechet)
    (fun _ ↦ elementarySchwartz_nuclear) j (fun n ↦ schwartzBruhatStageCLM (a n) (e n))
    hj.2.2.2.2 (fun n ↦ (hj.2.2.2.1 n).isEmbedding)

/-- Paper: Theorem D.1.5.7, p. 764. The strong dual of the Schwartz–Bruhat space
of a second-countable group is nuclear. -/
theorem schwartzBruhat_strongDual_nuclear [SecondCountableTopology G] :
    IsNuclearTVS.{v} (StrongDual ℂ (SchwartzBruhat G)) := by
  let : T2Space (SchwartzBruhat G) := schwartzBruhat_t2
  have hs := schwartzBruhat_exists_cofinal_system (G := G)
  refine hs.elim fun a ha ↦ ha.elim fun e he ↦ he.elim fun j hj ↦ ?_
  let i n := schwartzBruhatStageCLM (a n) (e n)
  let : ∀ n, T2Space (SchwartzBruhatStage (e n)) := fun _ ↦ elementarySchwartz_t2
  let res : StrongDual ℂ (SchwartzBruhat G) →L[ℂ] ((n : ℕ) → StrongDual ℂ (SchwartzBruhatStage (e n))) :=
    ContinuousLinearMap.pi fun n ↦ ContinuousLinearMap.precomp ℂ (i n)
  have hr : IsClosedEmbedding res := strongDual_closedEmbedding_of_strict_limit hj.2.2.2.2 hj.2.2.2.1
  have hstage (n : ℕ) : IsNuclearTVS.{max v _} (SchwartzBruhatStage (e n)) :=
    isNuclearTVS_strictLF_stage hj.2.2.2.2 (fun n ↦ (hj.2.2.2.1 n).isEmbedding)
      (fun _ ↦ elementarySchwartz_isFrechet) schwartzBruhat_nuclear n
  exact schwartzBruhat_nuclear_of_embedding res.toLinearMap hr.isEmbedding
    (isNuclearTVS_pi fun n ↦ (isNuclearTVS_strongDual_iff elementarySchwartz_isFrechet).mpr (hstage n))

/-- The intersection of an open ascending union with a compactly generated subgroup
is already contained in one member of the union. -/
private theorem compactlyGenerated_inter_iSup_open {H : Subgroup G}
    (hH : IsCompactlyGeneratedGroup H) (hHOpen : IsOpen (H : Set G))
    {J : ℕ → Subgroup G} (hJ : Monotone J)
    (hOpen : ∀ n, IsOpen (J n : Set G)) :
    ∃ N, H ⊓ (⨆ n, J n) ≤ J N := by
  let L : Subgroup G := ⨆ n, J n
  have hL : IsOpen (L : Set G) := Subgroup.isOpen_mono (le_iSup J 0) (hOpen 0)
  let M := L.comap H.subtype
  have hM : IsClosed (M : Set H) :=
    (L.isClosed_of_isOpen hL).preimage continuous_subtype_val
  let : LocallyCompactSpace H := hHOpen.isOpenEmbedding_subtypeVal.locallyCompactSpace
  obtain ⟨K, _, hK, hGen⟩ := isCompactlyGeneratedGroup_closedSubgroup hH M hM
  let i : M →* G := H.subtype.comp M.subtype
  have hi : Continuous i := continuous_subtype_val.comp continuous_subtype_val
  obtain ⟨N, hN⟩ := (hK.image hi).elim_directed_cover
    (fun n ↦ (J n : Set G)) hOpen (by
      rw [← Subgroup.coe_iSup_of_directed hJ.directed_le]
      rintro _ ⟨x, _, rfl⟩
      exact x.property) (hJ.directed_le.mono fun _ _ h ↦ h)
  refine ⟨N, fun x hx ↦ ?_⟩
  have hgen : Subgroup.closure K ≤ (J N).comap i :=
    Subgroup.closure_le _ |>.mpr fun y hy ↦ hN (mem_image_of_mem i hy)
  exact hgen (hGen.symm ▸ Subgroup.mem_top (⟨⟨x, hx.1⟩, hx.2⟩ : M))

open Classical in
/-- Paper: Lemma D.1.5.6, p. 763. The stage projection on functions restricts the
support to the open subgroup and averages translates over the compact good subgroup. -/
def schwartzBruhatStageAverage (a : BruhatStructuralPair G) (f : G → ℂ) (x : G) : ℂ :=
  let k : Subgroup G := OrderDual.ofDual a.val.2
  letI : MeasurableSpace k := borel k
  letI : BorelSpace k := ⟨rfl⟩
  have hk : IsCompact (k : Set G) := by
    rw [← lcaDualAnnihilator_annihilator k a.property.2.2.1.1]
    exact isCompact_lcaDualAnnihilator _ a.property.2.2.1.2.1
  letI : CompactSpace k := isCompact_iff_compactSpace.mp hk
  let μ := Measure.haarMeasure (⟨⟨univ, isCompact_univ⟩, by simp⟩ : PositiveCompacts k)
  if x ∈ a.val.1 then ∫ h : k, f (h.val * x) ∂μ else 0

/-- Smoothness on the covering vector spaces gives continuity on the elementary group. -/
private theorem continuous_elementary_stage {m n r : ℕ} {F : Type*} [AddCommGroup F]
    [TopologicalSpace F] [DiscreteTopology F] [Finite F] (s : ElementarySchwartz m n r F) :
    Continuous (s : ElementaryLieGroup m n r F → ℂ) := by
  let V := EuclideanSpace ℝ (Fin m)
  let W := EuclideanSpace ℝ (Fin n)
  let D := (Fin r → ℤ) × F
  let q : (V × W) × D → ElementaryLieGroup m n r F := fun p ↦ elementaryCover p.1 p.2.1 p.2.2
  have hW : IsOpenQuotientMap (fun u : W ↦ fun i ↦ (u i : AddCircle (1 : ℝ))) :=
    (IsOpenQuotientMap.piMap fun _ ↦ QuotientAddGroup.isOpenQuotientMap_mk).comp
      (PiLp.homeomorph 2 (fun _ : Fin n ↦ ℝ)).isOpenQuotientMap
  have hq : IsOpenQuotientMap q :=
    (Homeomorph.prodAssoc V (Fin n → AddCircle (1 : ℝ)) D).isOpenQuotientMap.comp
      ((IsOpenQuotientMap.id.prodMap hW).prodMap IsOpenQuotientMap.id)
  apply hq.continuous_comp_iff.mp
  refine continuous_iff_continuousAt.mpr fun x ↦ ?_
  have hd : ∀ᶠ y : (V × W) × D in 𝓝 x, y.2 = x.2 :=
    continuousAt_snd.preimage_mem_nhds ((isOpen_discrete {x.2}).mem_nhds (mem_singleton _))
  refine (((s.property.1 x.2.1 x.2.2).continuous.comp continuous_fst).continuousAt).congr ?_
  filter_upwards [hd] with y hy
  change s (elementaryCover y.1 x.2.1 x.2.2) = s (elementaryCover y.1 y.2.1 y.2.2)
  rw [hy]

/-- Extension by zero from the clopen support subgroup preserves continuity. -/
private theorem continuous_stage_realization (b : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation b.quotient) (s : SchwartzBruhatStage e) :
    Continuous (schwartzBruhatStageRealization b e s) := by
  classical
  refine continuous_iff_continuousAt.mpr fun x ↦ ?_
  by_cases hx : x ∈ b.val.1
  · apply (b.property.1.isOpenEmbedding_subtypeVal.continuousAt_iff (x := ⟨x, hx⟩)).mp
    have heq (y : b.val.1) : schwartzBruhatStageRealization b e s y.val =
        s (e.equiv (QuotientGroup.mk y)).toAdd := by
      rw [schwartzBruhatStageRealization_apply, dite_eq_left y.property]
    exact (((continuous_elementary_stage s).comp
      (e.equiv.continuous.comp QuotientGroup.continuous_mk)).congr (fun y ↦ (heq y).symm)).continuousAt
  · apply (continuousAt_const (y := (0 : ℂ))).congr
    filter_upwards [(b.val.1.isClosed_of_isOpen b.property.1).isOpen_compl.mem_nhds hx] with y hy
    change y ∉ b.val.1 at hy
    rw [schwartzBruhatStageRealization_apply, dite_eq_right hy]

/-- Descend the realized function, including its extension by zero, to the
quotient of the entire group by the stage kernel. -/
private theorem exists_continuous_stage_descent (b : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation b.quotient) (s : SchwartzBruhatStage e) :
    ∃ f : (G ⧸ OrderDual.ofDual b.val.2) → ℂ, Continuous f ∧
      ∀ x : G, f (QuotientGroup.mk x) = schwartzBruhatStageRealization b e s x := by
  let k := OrderDual.ofDual b.val.2
  let f : G ⧸ k → ℂ := Quotient.lift (schwartzBruhatStageRealization b e s) (by
    intro x y hxy
    have h : x⁻¹ * y ∈ k := QuotientGroup.eq.mp (Quotient.sound hxy)
    have he := stage_realization_mul_kernel b e s h x
    simpa only [mul_right_comm, inv_mul_cancel_left, inv_mul_cancel, one_mul] using he.symm)
  exact ⟨f, (QuotientGroup.isQuotientMap_mk k).continuous_iff.mpr (continuous_stage_realization b e s),
    fun _ ↦ rfl⟩
/-- Integrate against Haar measure normalized to mass one on a compact group. -/
private def compactHaarIntegral {A : Type*} [CommGroup A] [TopologicalSpace A]
    [IsTopologicalGroup A] [CompactSpace A] (f : A → ℂ) : ℂ :=
  letI : MeasurableSpace A := borel A
  letI : BorelSpace A := ⟨rfl⟩
  ∫ x, f x ∂Measure.haarMeasure (⟨⟨univ, isCompact_univ⟩, by simp⟩ : PositiveCompacts A)

/-- A surjective continuous homomorphism pushes normalized Haar measure to normalized Haar measure. -/
private theorem compactHaarIntegral_comp {A B : Type*} [CommGroup A] [TopologicalSpace A]
    [IsTopologicalGroup A] [CompactSpace A] [T2Space A] [CommGroup B] [TopologicalSpace B]
    [IsTopologicalGroup B] [CompactSpace B] [T2Space B] (q : A →* B) (hq : Continuous q)
    (hs : Function.Surjective q) (f : B → ℂ) (hf : Continuous f) :
    compactHaarIntegral (f ∘ q) = compactHaarIntegral f := by
  let : MeasurableSpace A := borel A
  let : BorelSpace A := ⟨rfl⟩
  let : MeasurableSpace B := borel B
  let : BorelSpace B := ⟨rfl⟩
  let μ := Measure.haarMeasure (⟨⟨univ, isCompact_univ⟩, by simp⟩ : PositiveCompacts A)
  let ν := Measure.haarMeasure (⟨⟨univ, isCompact_univ⟩, by simp⟩ : PositiveCompacts B)
  have hm : MeasurePreserving q μ ν := q.measurePreserving hq hs
    ((show μ univ = 1 from Measure.haarMeasure_self).trans (show ν univ = 1 from Measure.haarMeasure_self).symm)
  change (∫ x, f (q x) ∂μ) = ∫ y, f y ∂ν
  rw [← hm.map_eq, integral_map hq.measurable.aemeasurable hf.aestronglyMeasurable]

/-- Equality of annihilator intersections gives equality of the images of the
compact averaging groups modulo the source kernel. -/
private theorem compact_kernel_images_eq (A B C : Subgroup G)
    (hA : IsCompact (A : Set G)) (hB : IsCompact (B : Set G)) (hC : IsCompact (C : Set G))
    (h : lcaAnnihilator A ⊓ lcaAnnihilator B = lcaAnnihilator C ⊓ lcaAnnihilator B) :
    A.map (QuotientGroup.mk' B) = C.map (QuotientGroup.mk' B) := by
  have ann (K M : Subgroup G) : lcaAnnihilator (K ⊔ M) = lcaAnnihilator K ⊓ lcaAnnihilator M := by
    ext χ
    have iffker (S : Subgroup G) : χ ∈ lcaAnnihilator S ↔ S ≤ χ.toMonoidHom.ker :=
      (mem_lcaAnnihilator_iff S χ).trans ⟨fun h x hx ↦ h ⟨x, hx⟩, fun h x ↦ h x.property⟩
    simp only [Subgroup.mem_inf, iffker, sup_le_iff]
  have closedSup (K : Subgroup G) (hK : IsCompact (K : Set G)) : IsClosed ((K ⊔ B : Subgroup G) : Set G) := by
    rw [Subgroup.mul_normal]
    exact (hK.mul hB).isClosed
  rw [← ann, ← ann] at h
  have hsup := congrArg (lcaDualAnnihilator (G := G)) h
  rw [lcaDualAnnihilator_annihilator _ (closedSup _ hA),
    lcaDualAnnihilator_annihilator _ (closedSup _ hC)] at hsup
  apply Subgroup.comap_injective (f := QuotientGroup.mk' B) QuotientGroup.mk_surjective
  simpa only [QuotientGroup.comap_map_mk', sup_comm B] using hsup
/-- Compute a kernel average on the image group in the structural quotient. -/
private theorem compactHaarIntegral_quotient_image {N K : Subgroup G}
    [T2Space (G ⧸ N)] [CompactSpace K] (T : Subgroup (G ⧸ N)) [CompactSpace T]
    (heq : K.map (QuotientGroup.mk' N) = T) (f : (G ⧸ N) → ℂ) (hf : Continuous f) :
    compactHaarIntegral (fun x : K ↦ f (QuotientGroup.mk x.val)) =
      compactHaarIntegral (fun x : T ↦ f x.val) := by
  let q := QuotientGroup.mk' N
  let g := (q.comp K.subtype).codRestrict T fun x ↦ heq ▸ Subgroup.mem_map_of_mem q x.property
  have hg : Continuous g :=
    (QuotientGroup.continuous_mk.comp continuous_subtype_val).subtype_mk _
  have hs : Function.Surjective g := by
    intro x
    obtain ⟨y, hy, he⟩ := (show x.val ∈ K.map q from heq.symm ▸ x.property)
    exact ⟨⟨y, hy⟩, Subtype.ext he⟩
  exact compactHaarIntegral_comp g hg hs _ (hf.comp continuous_subtype_val)

/-- For a function from a fixed stage, two comparable cutoff and averaging operations
agree when their open subgroups have the same intersection with the source support
subgroup and their averaging subgroups have the same image modulo the source kernel.
The equality of annihilator intersections expresses the latter condition. -/
theorem schwartzBruhatStage_average_eq_of_inf
    {a c : BruhatStructuralPair G} (b : BruhatStructuralPair G) (hac : a ≤ c)
    (hOpen : a.val.1 ⊓ b.val.1 = c.val.1 ⊓ b.val.1)
    (hKernel : lcaAnnihilator (OrderDual.ofDual a.val.2) ⊓
      lcaAnnihilator (OrderDual.ofDual b.val.2) =
      lcaAnnihilator (OrderDual.ofDual c.val.2) ⊓ lcaAnnihilator (OrderDual.ofDual b.val.2))
    (e : ElementaryLCAPresentation b.quotient) (f : SchwartzBruhatStage e) :
    schwartzBruhatStageAverage a (schwartzBruhatStageRealization b e f) =
      schwartzBruhatStageAverage c (schwartzBruhatStageRealization b e f) := by
  classical
  let A := OrderDual.ofDual a.val.2
  let B := OrderDual.ofDual b.val.2
  let C := OrderDual.ofDual c.val.2
  let F := schwartzBruhatStageRealization b e f
  let q := QuotientGroup.mk' B
  let T := A.map q
  let : CompactSpace A := isCompact_iff_compactSpace.mp (compact_bruhat_kernel a)
  let : CompactSpace C := isCompact_iff_compactSpace.mp (compact_bruhat_kernel c)
  let : T1Space (G ⧸ B) := QuotientGroup.t1Space_iff.mpr b.property.2.2.1.1
  let : CompactSpace T := isCompact_iff_compactSpace.mp
    ((compact_bruhat_kernel a).image (QuotientGroup.continuous_mk (N := B)))
  have heq : C.map q = T := (compact_kernel_images_eq A B C (compact_bruhat_kernel a)
    (compact_bruhat_kernel b) (compact_bruhat_kernel c) hKernel).symm
  obtain ⟨g, hg, hF⟩ := exists_continuous_stage_descent b e f
  funext x
  change (if x ∈ a.val.1 then compactHaarIntegral (fun h : A ↦ F (h.val * x)) else 0) =
    (if x ∈ c.val.1 then compactHaarIntegral (fun h : C ↦ F (h.val * x)) else 0)
  by_cases hx : x ∈ a.val.1
  · rw [ite_eq_left hx, ite_eq_left (hac.1 hx)]
    let u (y : G ⧸ B) := g (y * q x)
    have hu : Continuous u := hg.comp (continuous_id.mul continuous_const)
    have hux (y : G) : F (y * x) = u (q y) := (hF _).symm.trans (congrArg g (map_mul q y x))
    simp_rw [hux]
    exact (compactHaarIntegral_quotient_image (K := A) T rfl u hu).trans
      (compactHaarIntegral_quotient_image (K := C) T heq u hu).symm
  · rw [ite_eq_right hx]
    split_ifs with hc
    · have hzero (h : C) : F (h.val * x) = 0 := by
        have hy : h.val * x ∉ b.val.1 := by
          intro hmem
          have hh := c.property.2.2.2 h.property
          have ha : h.val * x ∈ a.val.1 ⊓ b.val.1 :=
            hOpen.symm ▸ (show h.val * x ∈ c.val.1 ⊓ b.val.1 from ⟨c.val.1.mul_mem hh hc, hmem⟩)
          exact hx ((a.val.1.mul_mem_cancel_left (a.property.2.2.2 (hac.2 h.property))).mp ha.1)
        change schwartzBruhatStageRealization b e f (h.val * x) = 0
        rw [schwartzBruhatStageRealization_apply, dite_eq_right hy]
      simp only [hzero, compactHaarIntegral, integral_zero]
    · rfl

/-- The intersections of a fixed stage's open subgroups in the group and its dual
with the corresponding subgroups in an ascending chain both stabilize. -/
private theorem schwartzBruhatStage_intersections_stabilize
    {a : ℕ → BruhatStructuralPair G} (ha : Monotone a) (b : BruhatStructuralPair G) :
    ∃ N, ∀ n ≥ N,
      (a n).val.1 ⊓ b.val.1 = (a (n + 1)).val.1 ⊓ b.val.1 ∧
      lcaAnnihilator (OrderDual.ofDual (a n).val.2) ⊓
        lcaAnnihilator (OrderDual.ofDual b.val.2) =
      lcaAnnihilator (OrderDual.ofDual (a (n + 1)).val.2) ⊓
        lcaAnnihilator (OrderDual.ofDual b.val.2) := by
  let H (n : ℕ) := (a n).val.1
  let A (n : ℕ) := lcaAnnihilator (OrderDual.ofDual (a n).val.2)
  have hH : Monotone H := fun _ _ h ↦ (ha h).1
  have hA : Monotone A := fun _ _ h χ hχ ↦
    (mem_lcaAnnihilator_iff _ χ).mpr fun x ↦
      (mem_lcaAnnihilator_iff _ χ).mp hχ ⟨x, (ha h).2 x.property⟩
  obtain ⟨N, hN⟩ := compactlyGenerated_inter_iSup_open b.property.2.1 b.property.1 hH
    (fun n ↦ (a n).property.1)
  obtain ⟨M, hM⟩ := compactlyGenerated_inter_iSup_open b.property.2.2.1.2.2
    b.property.2.2.1.2.1 hA (fun n ↦ (a n).property.2.2.1.2.1)
  refine ⟨max N M, fun n hn ↦ ⟨?_, ?_⟩⟩
  · exact le_antisymm (inf_le_inf_right _ (hH (Nat.le_succ n)))
      (le_inf ((inf_le_inf (le_iSup H (n + 1)) le_rfl).trans
        ((inf_comm _ _).le.trans (hN.trans (hH ((le_max_left _ _).trans hn))))) inf_le_right)
  · exact le_antisymm (inf_le_inf_right _ (hA (Nat.le_succ n)))
      (le_inf ((inf_le_inf (le_iSup A (n + 1)) le_rfl).trans
        ((inf_comm _ _).le.trans (hM.trans (hA ((le_max_right _ _).trans hn))))) inf_le_right)

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
/-- A sequence of linear functionals that eventually vanish on each stage cannot be
nonzero on a corresponding sequence in a bounded set. The functionals can be rescaled
and combined into one seminorm continuous on every stage. -/
private theorem exists_zero_evaluation_of_bounded
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    {ι : Type*} {X : ι → Type*} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    [∀ a, TopologicalSpace (X a)] [∀ a, IsTopologicalAddGroup (X a)]
    (i : ∀ a, X a →ₗ[ℂ] E)
    (hCover : ∀ u : E, ∃ a, u ∈ range (i a))
    {B : Set E} (hBound : ∀ p : Seminorm ℂ E, (∀ a, Continuous (p ∘ i a)) →
      ∃ C : ℝ, ∀ u ∈ B, p u < C)
    (f : ℕ → E) (hfB : ∀ n, f n ∈ B)
    (L : ℕ → E →ₗ[ℂ] ℂ)
    (hL : ∀ n a, Continuous (L n ∘ i a))
    (hzero : ∀ a, ∃ N, ∀ n ≥ N, ∀ s, L n (i a s) = 0) :
    ¬ ∀ n, L n (f n) ≠ 0 := by
  intro hne
  let w (n : ℕ) : ℝ := (n : ℝ) / ‖L n (f n)‖
  let p (n : ℕ) : Seminorm ℂ E :=
    (Real.toNNReal (w n)) • (normSeminorm ℂ ℂ).comp (L n)
  have hp (n : ℕ) (u : E) : p n u = w n * ‖L n u‖ := by
    change (↑(Real.toNNReal (w n)) : ℝ) * ‖L n u‖ = w n * ‖L n u‖
    rw [Real.coe_toNNReal _ (div_nonneg (Nat.cast_nonneg n) (norm_nonneg _))]
  have hfin (a : ι) : ∃ N, ∀ n (s : X a), p n (i a s) ≤ ((Finset.range N).sup p) (i a s) := by
    obtain ⟨N, hN⟩ := hzero a
    refine ⟨N, fun n s ↦ ?_⟩
    by_cases hn : n < N
    · exact Seminorm.le_finset_sup_apply (Finset.mem_range.mpr hn)
    · rw [hp, hN n (Nat.le_of_not_gt hn) s, norm_zero, mul_zero]
      exact apply_nonneg _ _
  have hbound : BddAbove (range p) := Seminorm.bddAbove_range_iff.mpr fun u ↦ by
    obtain ⟨a, s, rfl⟩ := hCover u
    obtain ⟨N, hN⟩ := hfin a
    exact ⟨((Finset.range N).sup p) (i a s), forall_mem_range.mpr fun n ↦ hN n s⟩
  let q : Seminorm ℂ E := ⨆ n, p n
  have hcont (a : ι) : Continuous (q ∘ i a) := by
    obtain ⟨N, hN⟩ := hfin a
    let p' := SeminormFamily.comp p (i a)
    apply Seminorm.continuous_of_le (p := q.comp (i a))
      (q := (Finset.range N).sup p')
    · apply Seminorm.continuous_finsetSup
      intro n _
      exact ((hL n a).norm.const_mul (w n)).congr fun s ↦ (hp n (i a s)).symm
    · intro s
      rw [← SeminormFamily.finset_sup_comp]
      change (⨆ n, p n) (i a s) ≤ ((Finset.range N).sup p) (i a s)
      rw [Seminorm.iSup_apply hbound]
      exact ciSup_le fun n ↦ hN n s
  obtain ⟨C, hC⟩ := hBound q hcont
  obtain ⟨n, hn⟩ := exists_nat_gt C
  have hpn : p n (f n) = (n : ℝ) := by
    rw [hp]
    exact div_mul_cancel₀ _ (norm_ne_zero_iff.mpr (hne n))
  exact (not_lt_of_ge (hn.le.trans (hpn.ge.trans (le_ciSup hbound n (f n))))) (hC _ (hfB n))

/-- If projections along an ascending chain eventually agree on each fixed stage,
their successive differences rule out a bounded set escaping every stage. -/
private theorem bounded_subset_stage_of_projections
    {E A : Type*} [AddCommGroup E] [Module ℂ E]
    {ι κ : Type*} [Preorder κ] [Nonempty κ] {X : ι → Type*}
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    [∀ a, TopologicalSpace (X a)] [∀ a, IsTopologicalAddGroup (X a)]
    (i : ∀ a, X a →ₗ[ℂ] E) (hCover : ∀ u : E, ∃ a, u ∈ range (i a))
    {B : Set E} (hBound : ∀ p : Seminorm ℂ E, (∀ a, Continuous (p ∘ i a)) →
      ∃ C : ℝ, ∀ u ∈ B, p u < C)
    (S : κ → Set E) (hNext : ∀ k u, ∃ l, k ≤ l ∧ u ∈ S l)
    (P : κ → E →ₗ[ℂ] (A → ℂ)) (realize : E → (A → ℂ))
    (hFix : ∀ k u, P k u = realize u ↔ u ∈ S k)
    (hCont : ∀ k x b, Continuous (fun s : X b ↦ P k (i b s) x))
    (hStable : ∀ (a : ℕ → κ), Monotone a → ∀ b, ∃ N, ∀ n ≥ N, ∀ s,
      P (a (n + 1)) (i b s) = P (a n) (i b s)) :
    ∃ k, B ⊆ S k := by
  classical
  by_contra hEscape
  simp only [not_exists, not_subset] at hEscape
  choose f hfB hfOut using hEscape
  choose next hnext hmem using fun k ↦ hNext k (f k)
  let a : ℕ → κ := Nat.rec (Classical.choice ‹Nonempty κ›) (fun _ k ↦ next k)
  have ha : Monotone a := monotone_nat_of_le_succ fun n ↦ hnext (a n)
  have hPoint (n : ℕ) : ∃ x, P (a (n + 1)) (f (a n)) x ≠ P (a n) (f (a n)) x := by
    by_contra! h
    exact hfOut (a n) ((hFix _ _).mp ((funext h).symm.trans ((hFix _ _).mpr (hmem (a n)))))
  choose x hx using hPoint
  let L (n : ℕ) : E →ₗ[ℂ] ℂ := (LinearMap.proj (x n)).comp (P (a (n + 1)) - P (a n))
  apply exists_zero_evaluation_of_bounded i hCover hBound (f ∘ a) (fun n ↦ hfB (a n)) L
  · exact fun n b ↦ (hCont (a (n + 1)) (x n) b).sub (hCont (a n) (x n) b)
  · intro b
    obtain ⟨N, hN⟩ := hStable a ha b
    exact ⟨N, fun n hn s ↦ sub_eq_zero.mpr (congrFun (hN n hn s) (x n))⟩
  · exact fun n ↦ sub_ne_zero.mpr (hx n)

/-- An element can be realized in a stage above any given structural pair,
with any chosen presentation of the larger quotient. -/
private theorem schwartzBruhat_exists_stage_above
    (e : ∀ b : BruhatStructuralPair G, ElementaryLCAPresentation b.quotient)
    (a : BruhatStructuralPair G) (u : schwartzBruhatSubmodule G) :
    ∃ b, a ≤ b ∧ u ∈ range (schwartzBruhatStageInclusion b (e b)) := by
  obtain ⟨b, d, s, hs⟩ := (mem_schwartzBruhatSubmodule_iff (G := G) u.val).mp u.property
  obtain ⟨c, hac, hbc⟩ := (bruhatStructuralPair_filtered (G := G)).2.directed a b
  obtain ⟨j, hj, _⟩ := schwartzBruhatStage_transition hbc d (e c)
  exact ⟨c, hac, j s, Subtype.ext ((hj s).trans hs)⟩

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
/-- Each generating seminorm is bounded on every von Neumann bounded set. -/
private theorem schwartzBruhat_seminorm_bounded {B : Set (SchwartzBruhat G)}
    (hB : IsVonNBounded ℂ B) (p : Seminorm ℂ (schwartzBruhatSubmodule G))
    (hp : ∀ (b : BruhatStructuralPair G) (d : ElementaryLCAPresentation b.quotient),
      Continuous (p ∘ schwartzBruhatStageInclusion b d)) :
    ∃ C : ℝ, ∀ u ∈ B, p u < C := by
  let I := {q : Seminorm ℂ (schwartzBruhatSubmodule G) //
    ∀ (b : BruhatStructuralPair G) (d : ElementaryLCAPresentation b.quotient),
      Continuous (q ∘ schwartzBruhatStageInclusion b d)}
  have hSeminorms := withGeneratingSeminorms_spec (schwartzBruhatSubmodule G)
    (Subtype.val : I → Seminorm ℂ (schwartzBruhatSubmodule G))
  exact (hSeminorms.isVonNBounded_iff_seminorm_bounded.mp hB ⟨p, hp⟩).imp (fun _ h ↦ h.2)

/-- The stage maps for all pairs and presentations cover the Schwartz–Bruhat space. -/
private theorem schwartzBruhat_stage_cover (u : schwartzBruhatSubmodule G) :
    ∃ b : (a : BruhatStructuralPair G) × ElementaryLCAPresentation a.quotient,
      u ∈ range (schwartzBruhatStageInclusion b.1 b.2) := by
  exact ((mem_schwartzBruhatSubmodule_iff (G := G) u.val).mp u.property).elim
    (fun b hb ↦ hb.elim fun d hd ↦ hd.elim fun s hs ↦ ⟨⟨b, d⟩, s, Subtype.ext hs⟩)

/-- Averaging along an ascending chain eventually gives the same result on every
element of a fixed stage. -/
private theorem schwartzBruhatStage_average_stabilizes
    {a : ℕ → BruhatStructuralPair G} (ha : Monotone a)
    (b : BruhatStructuralPair G) (d : ElementaryLCAPresentation b.quotient) :
    ∃ N, ∀ n ≥ N, ∀ s : SchwartzBruhatStage d,
      schwartzBruhatStageAverage (a (n + 1)) (schwartzBruhatStageRealization b d s) =
      schwartzBruhatStageAverage (a n) (schwartzBruhatStageRealization b d s) := by
  refine (schwartzBruhatStage_intersections_stabilize (G := G) ha b).imp ?_
  intro N hN n hn s
  exact (schwartzBruhatStage_average_eq_of_inf b (ha (Nat.le_succ n))
    (hN n hn).1 (hN n hn).2 d s).symm

/-- Successive differences of the cutoff and averaging projections force a bounded
set to lie in one stage. -/
private theorem schwartzBruhat_bounded_subset_stage
    {B : Set (SchwartzBruhat G)} (hB : IsVonNBounded ℂ B)
    (e : ∀ a : BruhatStructuralPair G, ElementaryLCAPresentation a.quotient)
    (R : ∀ a, SchwartzBruhat G →L[ℂ] SchwartzBruhatStage (e a))
    (hRi : ∀ a, Function.LeftInverse (R a) (schwartzBruhatStageInclusion a (e a)))
    (hR : ∀ (a : BruhatStructuralPair G) (u : SchwartzBruhat G) (x : G),
      schwartzBruhatStageRealization a (e a) (R a u) x = schwartzBruhatStageAverage a u x) :
    ∃ a, B ⊆ range (schwartzBruhatStageInclusion a (e a)) := by
  let : Nonempty (BruhatStructuralPair G) := (bruhatStructuralPair_filtered (G := G)).1
  let i (a : BruhatStructuralPair G) := schwartzBruhatStageInclusion a (e a)
  let P (b : BruhatStructuralPair G) : schwartzBruhatSubmodule G →ₗ[ℂ] (G → ℂ) :=
    (schwartzBruhatStageRealization b (e b)).comp (R b).toLinearMap
  have hP (b : BruhatStructuralPair G) (u : SchwartzBruhat G) :
      P b u = schwartzBruhatStageAverage b u := funext (hR b u)
  have hFix (b : BruhatStructuralPair G) (u : SchwartzBruhat G) : P b u = u.val ↔ u ∈ range (i b) :=
    ⟨fun h ↦ ⟨R b u, Subtype.ext h⟩,
      fun hu ↦ congrArg (fun w : SchwartzBruhat G ↦ w.val)
        ((Function.LeftInverse.rightInvOn_range (hRi b)) hu)⟩
  let J := (b : BruhatStructuralPair G) × ElementaryLCAPresentation b.quotient
  let j (b : J) := schwartzBruhatStageInclusion b.1 b.2
  have hBound (p : Seminorm ℂ (schwartzBruhatSubmodule G)) (hp : ∀ b : J, Continuous (p ∘ j b)) :
      ∃ C : ℝ, ∀ u ∈ B, p u < C :=
    schwartzBruhat_seminorm_bounded (G := G) hB p (fun b d ↦ hp ⟨b, d⟩)
  refine bounded_subset_stage_of_projections (X := fun b : J ↦ SchwartzBruhatStage b.2)
    j (schwartzBruhat_stage_cover (G := G)) hBound (fun b ↦ range (i b))
    (schwartzBruhat_exists_stage_above (G := G) e) P (fun u ↦ u.val) hFix ?_ ?_
  · rintro c x ⟨b, d⟩
    exact (continuous_schwartzBruhatStage_eval c (e c) x).comp
      ((R c).continuous.comp (continuous_schwartzBruhatStageInclusion b d))
  · rintro a ha ⟨b, d⟩
    refine (schwartzBruhatStage_average_stabilizes (G := G) ha b d).imp ?_
    intro N hN n hn s
    let u : SchwartzBruhat G := schwartzBruhatStageInclusion b d s
    exact (hP (a (n + 1)) u).trans ((hN n hn s).trans (hP (a n) u).symm)

/-- Independent closed seminorm bounds cut out a compact convex disk in an
elementary Schwartz space. -/
private theorem elementary_compact_seminorm_disk {m n r : ℕ} {F : Type} [AddCommGroup F]
    [TopologicalSpace F] [DiscreteTopology F] [Finite F] (s : ElementarySchwartz m n r F) :
    ∃ C : Set (ElementarySchwartz m n r F), IsCompact C ∧ Convex ℝ C ∧
      ∀ t, (∀ i, elementarySchwartzSeminorm i t ≤ elementarySchwartzSeminorm i s) → t ∈ C := by
  let E := ElementarySchwartz m n r F
  let p (i : ElementarySchwartzIndex m n r) : Seminorm ℂ E := elementarySchwartzSeminorm i
  let C := ⋂ i, (p i).closedBall 0 (p i s)
  have hf := elementarySchwartz_withSeminorms (m := m) (n := n) (r := r) (F := F)
  have hcont (i) : Continuous (p i) := hf.continuous_seminorm i
  have hc : IsClosed C := isClosed_iInter fun i ↦ by
    simpa only [Seminorm.closedBall_zero_eq] using isClosed_le (hcont i) (continuous_const (y := p i s))
  have hB : IsVonNBounded ℂ C := hf.isVonNBounded_iff_seminorm_bounded.mpr fun i ↦
    ⟨p i s + 1, by positivity, fun x hx ↦ ((p i).mem_closedBall_zero.mp (mem_iInter.mp hx i)).trans_lt
      (lt_add_one _)⟩
  refine ⟨C, elementarySchwartz_isCompact_of_isClosed_isVonNBounded hc hB,
    convex_iInter fun i ↦ (p i).convex_closedBall _ _, fun t ht ↦ ?_⟩
  exact mem_iInter.mpr fun i ↦ (p i).mem_closedBall_zero.mpr (ht i)

open Classical in
/-- Translating the compact coordinates and cutting out whole discrete fibers
does not increase any elementary Schwartz seminorm. -/
private theorem elementary_cut_shift {m n r : ℕ} {F : Type} [AddCommGroup F]
    [TopologicalSpace F] [DiscreteTopology F] [Finite F] (s : ElementarySchwartz m n r F)
    (θ : Fin n → AddCircle (1 : ℝ)) (d : F) (keep : (Fin r → ℤ) → F → Prop) :
    ∃ t : ElementarySchwartz m n r F, (∀ i, elementarySchwartzSeminorm i t ≤ elementarySchwartzSeminorm i s) ∧
      ∀ y, t y = (if keep y.2.2.1 y.2.2.2 then s ((0, θ, 0, d) + y) else 0) := by
  classical
  let X := EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
  choose lift hl using fun i ↦ QuotientAddGroup.mk_surjective (θ i)
  let v : X := (0, WithLp.toLp 2 lift)
  let f (y : ElementaryLieGroup m n r F) := if keep y.2.2.1 y.2.2.2 then s ((0, θ, 0, d) + y) else 0
  have hshift (z : Fin r → ℤ) (b : F) (x : X) :
      (0, θ, 0, d) + elementaryCover x z b = elementaryCover (v + x) z (d + b) := by
    apply Prod.ext (show 0 + x.1 = 0 + x.1 from rfl)
    refine Prod.ext (funext fun i ↦ ?_) (Prod.ext (zero_add z) rfl)
    change θ i + (x.2 i : AddCircle (1 : ℝ)) = ((lift i + x.2 i : ℝ) : AddCircle (1 : ℝ))
    rw [AddCircle.coe_add, ← hl i]
  have hf (z : Fin r → ℤ) (b : F) : (fun x : X ↦ f (elementaryCover x z b)) =
      if keep z b then (fun x ↦ s (elementaryCover (v + x) z (d + b))) else 0 := by
    split_ifs with h <;> funext x
    · exact (ite_eq_left h).trans (congrArg s (hshift z b x))
    · exact ite_eq_right h
  have hd (z : Fin r → ℤ) (b : F) : ContDiff ℝ ∞ (fun x ↦ f (elementaryCover x z b)) := by
    rw [hf]
    split_ifs
    · exact (s.property.1 z (d + b)).comp (contDiff_const.add contDiff_id)
    · exact contDiff_const
  have hb (i : ElementarySchwartzIndex m n r) : elementarySchwartzBound f i ≤ elementarySchwartzBound s.val i := by
    unfold elementarySchwartzBound
    refine iSup_le fun x ↦ iSup_le fun z ↦ iSup_le fun b ↦ ?_
    by_cases h : keep z b
    · apply le_iSup_of_le (v + x)
      apply le_iSup_of_le z
      apply le_iSup_of_le (d + b)
      have he : elementaryPartial f i.2.1 i.2.2.1 x z b =
          elementaryPartial s.val i.2.1 i.2.2.1 (v + x) z (d + b) := by
        unfold elementaryPartial
        rw [hf, ite_eq_left h]
        have hdshift (k : ℕ) := iteratedFDeriv_comp_add_left (𝕜 := ℝ)
          (f := fun w ↦ s.val (elementaryCover w z (d+b))) k v x
        exact DFunLike.congr_fun (hdshift _) _
      rw [he, show (v + x).1 = x.1 from zero_add x.1]
    · have he : elementaryPartial f i.2.1 i.2.2.1 x z b = 0 := by
        unfold elementaryPartial
        rw [hf, ite_eq_right h]
        simp
      simp [he]
  let t : ElementarySchwartz m n r F := ⟨f, hd, fun i ↦ (hb i).trans_lt (s.property.2 i)⟩
  exact ⟨t, fun i ↦ ENNReal.toReal_mono (s.property.2 i).ne (hb i), fun _ ↦ rfl⟩

/-- Only the torus and finite coordinates of an elementary group can receive
a nonzero continuous homomorphism from a compact group. -/
private theorem elementary_compact_coordinates {m n r : ℕ} {F : Type} [AddCommGroup F]
    [TopologicalSpace F] {K : Type*} [AddCommGroup K] [TopologicalSpace K] [CompactSpace K]
    (f : K →+ ElementaryLieGroup m n r F) (hf : Continuous f) (x : K) :
    (f x).1 = 0 ∧ (f x).2.2.1 = 0 := by
  constructor
  · ext i
    let g := (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ).toLinearMap.toAddMonoidHom.comp
      ((AddMonoidHom.fst _ _).comp f)
    exact compact_hom_real_zero g ((EuclideanSpace.proj i).continuous.comp hf.fst) x
  · ext i
    let g : K →+ ℤ := (Pi.evalAddMonoidHom _ i).comp ((AddMonoidHom.fst _ _).comp
      ((AddMonoidHom.snd _ _).comp ((AddMonoidHom.snd _ _).comp f)))
    have hg : Continuous g := (continuous_apply i).comp hf.snd.snd.fst
    have hz := compact_hom_real_zero ((Int.castAddHom ℝ).comp g)
      ((continuous_of_discreteTopology (f := Int.castAddHom ℝ)).comp hg) x
    change ((g x : ℤ) : ℝ) = 0 at hz
    change g x = 0
    exact_mod_cast hz

/-- Membership in an open subgroup of an elementary group is constant on each
connected real-torus fiber. -/
private theorem elementary_open_mask {m n r : ℕ} {F : Type} [AddCommGroup F]
    [TopologicalSpace F] [DiscreteTopology F] [Finite F]
    (H : OpenSubgroup (Multiplicative (ElementaryLieGroup m n r F))) (y : ElementaryLieGroup m n r F) :
    Multiplicative.ofAdd y ∈ H ↔ Multiplicative.ofAdd (0, 0, y.2.2.1, y.2.2.2) ∈ H := by
  let g : (EuclideanSpace ℝ (Fin m) × (Fin n → AddCircle (1 : ℝ))) →
      Multiplicative (ElementaryLieGroup m n r F) := fun x ↦ Multiplicative.ofAdd (x.1, x.2, 0, 0)
  have hg : Continuous g := continuous_fst.prodMk (continuous_snd.prodMk continuous_const)
  have htop : g ⁻¹' (H : Set _) = univ := (H.isClopen.preimage hg).eq_univ ⟨0, H.one_mem⟩
  have hmem : g (y.1, y.2.1) ∈ H := eq_univ_iff_forall.mp htop _
  have hdecomp : Multiplicative.ofAdd y = g (y.1, y.2.1) * Multiplicative.ofAdd (0, 0, y.2.2.1, y.2.2.2) := by
    change y = (y.1, y.2.1, 0, 0) + (0, 0, y.2.2.1, y.2.2.2)
    ext <;> simp
  rw [hdecomp]
  exact H.toSubgroup.mul_mem_cancel_left hmem

open Classical in
/-- Inside a common stage, every cutoff and compact translate is represented
by an elementary test satisfying the original seminorm bounds. -/
private theorem stage_cut_shift_bounded (a c : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation c.quotient) (s : SchwartzBruhatStage e)
    (hac : OrderDual.ofDual a.val.2 ≤ c.val.1) (hca : OrderDual.ofDual c.val.2 ≤ a.val.1)
    (h : (OrderDual.ofDual a.val.2 : Subgroup G)) :
    ∃ t : SchwartzBruhatStage e, (∀ i, elementarySchwartzSeminorm i t ≤ elementarySchwartzSeminorm i s) ∧
      ∀ x, schwartzBruhatStageRealization c e t x =
        (if x ∈ a.val.1 then schwartzBruhatStageRealization c e s (h.val * x) else 0) := by
  classical
  let K := OrderDual.ofDual a.val.2
  let : CompactSpace K := isCompact_iff_compactSpace.mp (compact_bruhat_kernel a)
  let q : c.val.1 →* c.quotient := QuotientGroup.mk' _
  let π := e.equiv.toMulEquiv.toMonoidHom.comp q
  have hπ : Continuous π := e.equiv.continuous.comp QuotientGroup.continuous_mk
  let j := π.comp (Subgroup.inclusion hac)
  have hj : Continuous j := hπ.comp (continuous_subtype_val.subtype_mk _)
  let f := MonoidHom.toAdditive j
  obtain ⟨hr, hz⟩ := elementary_compact_coordinates f hj (Additive.ofMul h)
  let u := (j h).toAdd
  have hu : u = (0, u.2.1, 0, u.2.2.2) := Prod.ext hr (Prod.ext rfl (Prod.ext hz rfl))
  let B := a.val.1.comap c.val.1.subtype
  let H : OpenSubgroup _ := ⟨B.map π, (e.equiv.toHomeomorph.isOpenMap.comp (QuotientGroup.isOpenMap_coe (N := (OrderDual.ofDual c.val.2).comap c.val.1.subtype)))
    _ (a.property.1.preimage continuous_subtype_val)⟩
  have hH (z : c.val.1) : π z ∈ H ↔ z.val ∈ a.val.1 := by
    refine ⟨fun he ↦ ?_, fun hz ↦ ⟨z, hz, rfl⟩⟩
    obtain ⟨w, hw, hwz⟩ := he
    have heq : q w = q z := e.equiv.injective hwz
    have hk : (z / w).val ∈ OrderDual.ofDual c.val.2 := (c.quotient_mk_eq_one _).mp
      (show q (z / w) = 1 by rw [map_div, heq, div_self'])
    simpa only [Subgroup.coe_div, div_mul_cancel] using a.val.1.mul_mem (hca hk) (show w.val ∈ a.val.1 from hw)
  let keep (z : Fin e.latticeRank → ℤ) (b : e.finiteFactor) :=
    Multiplicative.ofAdd (0, 0, z, b) ∈ H
  obtain ⟨t, ht, hval⟩ := elementary_cut_shift s u.2.1 u.2.2.2 keep
  refine ⟨t, ht, fun x ↦ ?_⟩
  have hh := hac h.property
  simp only [schwartzBruhatStageRealization_apply, c.val.1.mul_mem_cancel_left hh]
  split_ifs with hxC hxA hxA
  · let z : c.val.1 := ⟨x, hxC⟩
    let w := (π z).toAdd
    have hkeep : keep w.2.2.1 w.2.2.2 := (elementary_open_mask H w).mp ((hH z).mpr hxA)
    change t w = _
    refine (hval w).trans ((ite_eq_left hkeep).trans ?_)
    rw [← hu]
    exact congrArg (fun b ↦ s (Multiplicative.toAdd b))
      (map_mul π (Subgroup.inclusion hac h) z).symm
  · let z : c.val.1 := ⟨x, hxC⟩
    let w := (π z).toAdd
    have hkeep : ¬ keep w.2.2.1 w.2.2.2 := fun hk ↦ hxA ((hH z).mp ((elementary_open_mask H w).mpr hk))
    exact (hval w).trans (ite_eq_right hkeep)
  · rfl
  · rfl

open Classical in
/-- A compact convex set of pointwise functions containing every cutoff translate
of a test also contains its normalized stage average. -/
private theorem stage_average_mem_compact_convex (a : BruhatStructuralPair G) (u : G → ℂ)
    (hc : Continuous u) (T : Set (G → ℂ)) (hTc : IsCompact T) (hTv : Convex ℝ T)
    (hmem : ∀ h : (OrderDual.ofDual a.val.2 : Subgroup G),
      (fun x ↦ if x ∈ a.val.1 then u (h.val * x) else 0) ∈ T) :
    schwartzBruhatStageAverage a u ∈ T := by
  classical
  let K : Subgroup G := OrderDual.ofDual a.val.2
  let : MeasurableSpace K := borel _
  let : BorelSpace K := ⟨rfl⟩
  let : CompactSpace K := isCompact_iff_compactSpace.mp (compact_bruhat_kernel a)
  let μ := Measure.haarMeasure (⟨⟨univ, isCompact_univ⟩, by simp⟩ : PositiveCompacts K)
  let : IsProbabilityMeasure μ := ⟨Measure.haarMeasure_self⟩
  let F (h : K) (x : G) := if x ∈ a.val.1 then u (h.val * x) else 0
  have hf (x : G) : Continuous (fun h : K ↦ F h x) := by
    by_cases hx : x ∈ a.val.1
    · simp only [F, ite_eq_left hx]
      exact hc.comp (continuous_subtype_val.mul continuous_const)
    · simpa only [F, ite_eq_right hx] using (continuous_const (X := K) (y := (0 : ℂ)))
  have hmean := integral_mem_compact_convex_functions μ T hTc hTv F hmem
    (fun x ↦ (hf x).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  convert hmean using 1
  funext x
  symm
  change (∫ h : K, (if x ∈ a.val.1 then u (h.val * x) else 0) ∂μ) =
    (if x ∈ a.val.1 then ∫ h : K, u (h.val * x) ∂μ else 0)
  split_ifs <;> simp_all only [integral_zero]

/-- For a fixed elementary test a compact disk in its own stage represents all
averages whose cutoff contains its kernel and whose kernel lies in its support subgroup. -/
private theorem stage_averages_in_compact_disk (c : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation c.quotient) (s : SchwartzBruhatStage e) :
    ∃ C : Set (SchwartzBruhatStage e), IsCompact C ∧ ∀ a : BruhatStructuralPair G,
      OrderDual.ofDual a.val.2 ≤ c.val.1 → OrderDual.ofDual c.val.2 ≤ a.val.1 →
      schwartzBruhatStageAverage a (schwartzBruhatStageRealization c e s) ∈ schwartzBruhatStageRealization c e '' C := by
  obtain ⟨C, hc, hv, hbound⟩ := elementary_compact_seminorm_disk s
  have hreal : Continuous (schwartzBruhatStageRealization c e) :=
    continuous_pi (continuous_schwartzBruhatStage_eval c e)
  let T := schwartzBruhatStageRealization c e '' C
  have hTc : IsCompact T := hc.image hreal
  have hTv : Convex ℝ T := hv.linear_image ((schwartzBruhatStageRealization c e).restrictScalars ℝ)
  refine ⟨C, hc, fun a hac hca ↦ stage_average_mem_compact_convex a _
    (continuous_stage_realization c e s) T hTc hTv (fun h ↦ ?_)⟩
  obtain ⟨t, ht, heq⟩ := stage_cut_shift_bounded a c e s hac hca h
  exact ⟨t, hbound _ ht, funext heq⟩

/-- A stage bound also bounds a realized function on the whole group. -/
private theorem schwartzBruhat_norm_bounded (f : schwartzBruhatSubmodule G) :
    ∃ C : ℝ, ∀ x : G, ‖f.val x‖ ≤ C := by
  obtain ⟨a, e, s, hs⟩ := (mem_schwartzBruhatSubmodule_iff f.val).mp f.property
  exact ⟨_, fun x ↦ hs ▸ norm_stage_realization_le a e s x⟩

/-- The uniform norm on functions is continuous in the final topology, since
the zero-order seminorm of each stage dominates it. -/
private theorem exists_schwartzBruhat_uniform_seminorm :
    ∃ p : Seminorm ℂ (SchwartzBruhat G), Continuous p ∧
      ∀ (f : SchwartzBruhat G) x, ‖f x‖ ≤ p f := by
  let ev (x : G) : schwartzBruhatSubmodule G →ₗ[ℂ] ℂ :=
    (LinearMap.proj x).comp (schwartzBruhatSubmodule G).subtype
  let q (x : G) := (normSeminorm ℂ ℂ).comp (ev x)
  have hb : BddAbove (range q) := by
    apply Seminorm.bddAbove_range_iff.mpr
    intro f
    obtain ⟨C, hC⟩ := schwartzBruhat_norm_bounded f
    exact ⟨C, forall_mem_range.mpr hC⟩
  let p : Seminorm ℂ (schwartzBruhatSubmodule G) := ⨆ x, q x
  have hp (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient) :
      Continuous (p ∘ schwartzBruhatStageInclusion a e) := by
    let r := p.comp (schwartzBruhatStageInclusion a e)
    change Continuous r
    apply Seminorm.continuous_of_le (elementarySchwartz_withSeminorms.continuous_seminorm (0,0,0,0))
    intro s
    change (⨆ x, q x) (schwartzBruhatStageInclusion a e s) ≤ _
    rw [Seminorm.iSup_apply hb]
    exact ciSup_le fun x ↦ norm_stage_realization_le a e s x
  refine ⟨p, ?_, fun f x ↦ ?_⟩
  · exact schwartzBruhat_continuous_seminorm p hp
  · exact (le_ciSup hb x : q x ≤ p) f

/-- Normalized averaging is linear on continuous functions, is invariant under
kernel translations, and fixes a function already realized in this stage. -/
private theorem schwartzBruhatStage_average_properties (a : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation a.quotient) :
    (∀ f g : G → ℂ, Continuous f → Continuous g → schwartzBruhatStageAverage a (f + g) =
      schwartzBruhatStageAverage a f + schwartzBruhatStageAverage a g) ∧
    (∀ (c : ℂ) (f : G → ℂ), schwartzBruhatStageAverage a (c • f) = c • schwartzBruhatStageAverage a f) ∧
    (∀ (f : G → ℂ) x, x ∉ a.val.1 → schwartzBruhatStageAverage a f x = 0) ∧
    (∀ (f : G → ℂ) h, h ∈ OrderDual.ofDual a.val.2 → ∀ x,
      schwartzBruhatStageAverage a f (h*x) = schwartzBruhatStageAverage a f x) ∧
    (∀ s : SchwartzBruhatStage e, schwartzBruhatStageAverage a (schwartzBruhatStageRealization a e s) =
      schwartzBruhatStageRealization a e s) ∧
    (∀ (f : G → ℂ) (C : ℝ), 0 ≤ C → (∀ x, ‖f x‖ ≤ C) → ∀ x, ‖schwartzBruhatStageAverage a f x‖ ≤ C) := by
  classical
  let K := OrderDual.ofDual a.val.2
  let : MeasurableSpace K := borel _
  let : BorelSpace K := ⟨rfl⟩
  let : CompactSpace K := isCompact_iff_compactSpace.mp (compact_bruhat_kernel a)
  let μ := Measure.haarMeasure (⟨⟨univ, isCompact_univ⟩, by simp⟩ : PositiveCompacts K)
  let : IsProbabilityMeasure μ := ⟨Measure.haarMeasure_self⟩
  have hav (f : G → ℂ) (x : G) : schwartzBruhatStageAverage a f x =
      if x ∈ a.val.1 then ∫ h : K, f (h.val * x) ∂μ else 0 := rfl
  have hi (f : G → ℂ) (hf : Continuous f) (x : G) : Integrable (fun h : K ↦ f (h.val * x)) μ :=
    (hf.comp (continuous_subtype_val.mul continuous_const)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine ⟨fun f g hf hg ↦ funext fun x ↦ ?_, fun c f ↦ funext fun x ↦ ?_, fun f x hx ↦ ?_,
    fun f h hh x ↦ ?_, fun s ↦ funext fun x ↦ ?_, fun f C hC hf x ↦ ?_⟩
  · simp only [Pi.add_apply, hav]
    split_ifs <;> simp [integral_add (hi f hf x) (hi g hg x)]
  · simp only [Pi.smul_apply, hav]
    split_ifs <;> simp [integral_const_mul]
  · rw [hav, ite_eq_right hx]
  · simp only [hav, a.val.1.mul_mem_cancel_left (a.property.2.2.2 hh)]
    split_ifs
    · have he := integral_mul_right_eq_self (μ := μ) (fun k : K ↦ f (k.val * x)) (⟨h,hh⟩ : K)
      simpa only [Subgroup.coe_mul, mul_assoc] using he
    · rfl
  · rw [hav]
    split_ifs with hx
    · have hf (h : K) := stage_realization_mul_kernel a e s h.property x
      simp_rw [hf]
      simp
    · rw [schwartzBruhatStageRealization_apply, dite_eq_right hx]
  · rw [hav]
    split_ifs
    · simpa using norm_integral_le_of_norm_le_const (μ := μ) (.of_forall fun h : K ↦ hf (h.val * x))
    · simpa using hC

/-- Every stage average has a representative in the averaged stage. First realize
it in a common larger stage, then descend using kernel invariance. -/
private theorem schwartzBruhat_average_has_stage (a : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation a.quotient) (f : SchwartzBruhat G) :
    ∃ s : SchwartzBruhatStage e, schwartzBruhatStageRealization a e s = schwartzBruhatStageAverage a f.val := by
  let d (c : BruhatStructuralPair G) := c.elementary.some
  refine (schwartzBruhat_exists_stage_above d a f).elim fun c hc ↦ hc.2.elim fun s hs ↦ ?_
  have he : schwartzBruhatStageRealization c (d c) s = f.val := congrArg (fun u : schwartzBruhatSubmodule G ↦ u.val) hs
  obtain ⟨C, _, hC⟩ := stage_averages_in_compact_disk c (d c) s
  have hca : OrderDual.ofDual c.val.2 ≤ OrderDual.ofDual a.val.2 := hc.1.2
  obtain ⟨t, _, ht⟩ := hC a (a.property.2.2.2.trans hc.1.1) (hca.trans a.property.2.2.2)
  have hh := (schwartzBruhatStage_average_properties a e).2.2
  exact schwartzBruhatStage_descend_of_invariant hc.1 e (d c) t _ (he ▸ ht) (hh.1 f.val) (hh.2.1 f.val)

/-- Continuous evaluation of a linear map to a normed space follows from a
single continuous seminorm bound. -/
private theorem continuous_of_norm_le_seminorm {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] (L : E →ₗ[ℂ] ℂ)
    (p : Seminorm ℂ E) (hp : Continuous p) (h : ∀ x, ‖L x‖ ≤ p x) : Continuous L := by
  apply (norm_withSeminorms ℂ ℂ).continuous_of_continuous_comp L
  intro _
  exact Seminorm.continuous_of_le hp (show (normSeminorm ℂ ℂ).comp L ≤ p from h)

/-- Linearity and uniqueness of the representative lift averaging to a linear
map into the elementary stage. -/
private theorem schwartzBruhat_average_linear (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient) :
    ∃ R : SchwartzBruhat G →ₗ[ℂ] SchwartzBruhatStage e,
      ∀ f, schwartzBruhatStageRealization a e (R f) = schwartzBruhatStageAverage a f.val := by
  let i := schwartzBruhatStageRealization a e
  have hi : Function.Injective i := fun _ _ h ↦ schwartzBruhatStageInclusion_injective a e (Subtype.ext h)
  let r (f : SchwartzBruhat G) := (schwartzBruhat_average_has_stage a e f).choose
  have hr (f : SchwartzBruhat G) := (schwartzBruhat_average_has_stage a e f).choose_spec
  have hc (f : SchwartzBruhat G) : Continuous f.val := by
    refine ((mem_schwartzBruhatSubmodule_iff f.val).mp f.property).elim fun b hb ↦
      hb.elim fun d hd ↦ hd.elim fun s hs ↦ ?_
    exact hs ▸ continuous_stage_realization b d s
  have props := schwartzBruhatStage_average_properties a e
  refine ⟨{ toFun := r, map_add' := fun f g ↦ ?_, map_smul' := fun c f ↦ ?_ }, hr⟩
  · exact hi ((hr (f+g)).trans ((props.1 f.val g.val (hc f) (hc g)).trans
      (((congrArg₂ (·+·) (hr f) (hr g)).symm).trans (map_add i _ _).symm)))
  · exact hi ((hr (c • f)).trans ((props.2.1 c f.val).trans
      ((congrArg (c • ·) (hr f)).symm.trans (map_smul i _ _).symm)))

/-- A uniform bound on all evaluations gives a continuous map into an
elementary Schwartz space from a barrelled space. -/
private theorem continuous_to_elementary_of_uniform {E : Type*} [AddCommGroup E] [Module ℂ E]
    [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℂ E] [BarrelledSpace ℂ E]
    {m n r : ℕ} {F : Type} (R : E →ₗ[ℂ] ElementarySchwartz m n r F)
    (p : Seminorm ℂ E) (hp : Continuous p) (h : ∀ f g, ‖R f g‖ ≤ p f) : Continuous R := by
  apply continuous_toElementarySchwartz_of_eval R
  intro g
  let L := ((LinearMap.proj g).comp (elementarySchwartzSubmodule m n r F).subtype).comp R
  exact ⟨⟨L, continuous_of_norm_le_seminorm L p hp fun f ↦ h f g⟩, fun _ ↦ rfl⟩

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
/-- Every value in the elementary chart is attained at a point of the open subgroup. -/
private theorem stage_value_le_of_realization_bound (a : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation a.quotient) (s : SchwartzBruhatStage e) (C : ℝ)
    (h : ∀ x, ‖schwartzBruhatStageRealization a e s x‖ ≤ C) :
    ∀ g, ‖s g‖ ≤ C := by
  intro g
  obtain ⟨q,hq⟩ := e.equiv.surjective (Multiplicative.ofAdd g)
  obtain ⟨x,rfl⟩ := QuotientGroup.mk_surjective q
  have he := h x.val
  rw [schwartzBruhatStageRealization_apply a e s, dite_eq_left x.property, hq] at he
  exact he

/-- The uniform seminorm of the input bounds the values of its averaged
representative. -/
private theorem stage_average_value_bound (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient)
    (s : SchwartzBruhatStage e) (f : G → ℂ) (hs : schwartzBruhatStageRealization a e s = schwartzBruhatStageAverage a f)
    (C : ℝ) (hC : 0 ≤ C) (hf : ∀ x, ‖f x‖ ≤ C) : ∀ g, ‖s g‖ ≤ C := by
  apply stage_value_le_of_realization_bound a e s C
  exact hs.symm ▸ (schwartzBruhatStage_average_properties a e).2.2.2.2.2 f C hC hf

/-- The stage-valued averaging map is continuous by barrelledness and the
uniform bound for each of its evaluations. -/
private theorem continuous_schwartzBruhat_average (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient)
    (R : SchwartzBruhat G →ₗ[ℂ] SchwartzBruhatStage e)
    (hr : ∀ f, schwartzBruhatStageRealization a e (R f) = schwartzBruhatStageAverage a f.val) :
    Continuous R := by
  let : BarrelledSpace ℂ (SchwartzBruhat G) := schwartzBruhat_barrelled_of_stages
  let p := (exists_schwartzBruhat_uniform_seminorm (G := G)).choose
  have hp := (exists_schwartzBruhat_uniform_seminorm (G := G)).choose_spec
  exact continuous_to_elementary_of_uniform (m := e.realDim) (n := e.torusDim) (r := e.latticeRank)
    (F := e.finiteFactor) R p hp.1 (fun f ↦ stage_average_value_bound a e (R f) f.val
      (hr f) (p f) (apply_nonneg p f) (hp.2 f))

/-- Paper: Lemma D.1.5.6, p. 763. Cutoff and normalized Haar averaging yield a
continuous stage retraction, with the stated pointwise formula on the limit. -/
theorem schwartzBruhatStage_average_retraction
    (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient) :
    ∃ R : SchwartzBruhat G →L[ℂ] SchwartzBruhatStage e,
      (∀ f, R (schwartzBruhatStageInclusion a e f) = f) ∧
        ∀ f x, schwartzBruhatStageRealization a e (R f) x = schwartzBruhatStageAverage a f x := by
  refine (schwartzBruhat_average_linear a e).elim fun R hr ↦ ?_
  refine ⟨⟨R, continuous_schwartzBruhat_average a e R hr⟩, fun s ↦ ?_, fun f x ↦ congrFun (hr f) x⟩
  apply schwartzBruhatStageInclusion_injective a e
  apply Subtype.ext
  exact (hr (schwartzBruhatStageInclusion a e s)).trans ((schwartzBruhatStage_average_properties a e).2.2.2.2.1 s)

/-- A bounded set in the full Schwartz–Bruhat space is the image of a bounded
set in one stage, obtained by applying that stage's continuous retraction. -/
private theorem schwartzBruhat_bounded_lift
    {B : Set (SchwartzBruhat G)} (hB : IsVonNBounded ℂ B) :
    ∃ (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient)
      (C : Set (SchwartzBruhatStage e)), IsVonNBounded ℂ C ∧
        (show SchwartzBruhatStage e →ₗ[ℂ] SchwartzBruhat G from
          schwartzBruhatStageInclusion a e) '' C = B := by
  let e (a : BruhatStructuralPair G) := Classical.choice a.elementary
  let R (a : BruhatStructuralPair G) : SchwartzBruhat G →L[ℂ] SchwartzBruhatStage (e a) :=
    (schwartzBruhatStage_average_retraction a (e a)).choose
  have hRi (a : BruhatStructuralPair G) :
      Function.LeftInverse (R a) (schwartzBruhatStageInclusion a (e a)) :=
    (schwartzBruhatStage_average_retraction a (e a)).choose_spec.1
  refine (schwartzBruhat_bounded_subset_stage (G := G) hB e R hRi
    (fun b ↦ (schwartzBruhatStage_average_retraction b (e b)).choose_spec.2)).elim ?_
  intro a ha
  let i := schwartzBruhatStageInclusion a (e a)
  have hInv : LeftInvOn i (R a) B := fun _ hu ↦ (hRi a).rightInvOn_range (ha hu)
  exact ⟨a, e a, R a '' B, hB.image (R a), hInv.image_image⟩

/-- Paper: Theorem D.1.5.7 and Remark D.1.5.8, p. 764. Closed bounded subsets
of the Schwartz–Bruhat space are compact, including beyond the second-countable case. -/
theorem schwartzBruhat_montel :
    MontelSpace ℂ (SchwartzBruhat G) := by
  refine ⟨fun B hClosed hBounded ↦ ?_⟩
  obtain ⟨a, e, C, hC, hImage⟩ := schwartzBruhat_bounded_lift (G := G) hBounded
  let i : SchwartzBruhatStage e →ₗ[ℂ] SchwartzBruhat G := schwartzBruhatStageInclusion a e
  have hi : Continuous i := continuous_schwartzBruhatStageInclusion a e
  let : T2Space (SchwartzBruhatStage e) := elementarySchwartz_t2
  let : ContinuousSMul ℂ (SchwartzBruhatStage e) := elementarySchwartz_withSeminorms.continuousSMul
  have hCompact : IsCompact (closure C) :=
    elementarySchwartz_isCompact_of_isClosed_isVonNBounded isClosed_closure hC.closure
  have hEq : i '' closure C = B := subset_antisymm
    ((image_closure_subset_closure_image hi).trans (hImage ▸ hClosed.closure_eq.le))
    (hImage ▸ image_mono subset_closure)
  exact hEq ▸ hCompact.image hi

/-- Paper: Theorem D.1.5.7, p. 764. Closed bounded subsets of the strong dual
of the Schwartz–Bruhat space are compact. -/
theorem schwartzBruhat_strongDual_montel [SecondCountableTopology G] :
    MontelSpace ℂ (StrongDual ℂ (SchwartzBruhat G)) := by
  letI : T2Space (SchwartzBruhat G) := schwartzBruhat_t2
  letI : BarrelledSpace ℂ (SchwartzBruhat G) := schwartzBruhat_barrelled
  letI : MontelSpace ℂ (SchwartzBruhat G) := schwartzBruhat_montel
  exact montelSpace_strongDual

/-- Paper: Theorem D.1.5.7 and Remark D.1.5.8, p. 764. Evaluation gives a
linear homeomorphism with the strong bidual, the paper's reflexivity property
of Montel spaces, including beyond the second-countable case. -/
theorem schwartzBruhat_reflexive :
    ∃ e : SchwartzBruhat G ≃L[ℂ] StrongDual ℂ (StrongDual ℂ (SchwartzBruhat G)),
      ∀ f L, e f L = L f := by
  suffices h : ∀ (E : Type _) [AddCommGroup E] [Module ℂ E] [UniformSpace E]
      [IsUniformAddGroup E] [ContinuousSMul ℂ E] [PolynormableSpace ℂ E] [T2Space E]
      [BarrelledSpace ℂ E] [MontelSpace ℂ E],
      ∃ e : E ≃L[ℂ] StrongDual ℂ (StrongDual ℂ E), ∀ x l, e x l = l x by
    let : T2Space (SchwartzBruhat G) := schwartzBruhat_t2_of_stages
    let : BarrelledSpace ℂ (SchwartzBruhat G) := schwartzBruhat_barrelled_of_stages
    let : MontelSpace ℂ (SchwartzBruhat G) := schwartzBruhat_montel
    exact h _
  intro E _ _ _ _ _ _ _ _ _
  let j := ContinuousLinearMap.applyₗ (E := E) ℂ (RingHom.id ℂ)
  have hj : IsEmbedding j := isEmbedding_strongBidual_eval
  have hs : Function.Surjective j := surjective_strongBidual_eval
  exact ⟨ContinuousLinearEquiv.ofIsHomeomorph (LinearEquiv.ofBijective j ⟨hj.injective, hs⟩)
    (isHomeomorph_iff_isEmbedding_surjective.mpr ⟨hj, hs⟩), fun _ _ ↦ rfl⟩

-- Checking section-variable usage is expensive for the nested strong duals here.
set_option linter.unusedSectionVars false in
/-- Paper: Theorem D.1.5.7, p. 764. Evaluation identifies the strong dual
linearly and topologically with its own strong bidual. -/
theorem schwartzBruhat_strongDual_reflexive [SecondCountableTopology G] :
    let D := StrongDual ℂ (SchwartzBruhat G)
    letI : TopologicalSpace D := inferInstanceAs (TopologicalSpace (StrongDual ℂ (SchwartzBruhat G)))
    let DD := StrongDual ℂ D
    letI : TopologicalSpace DD := ContinuousLinearMap.topologicalSpace
    letI : TopologicalSpace (StrongDual ℂ DD) := ContinuousLinearMap.topologicalSpace
    ∃ e : D ≃L[ℂ] StrongDual ℂ DD, ∀ L M, e L M = M L := by
  refine (schwartzBruhat_reflexive (G := G)).elim ?_
  intro e he
  refine ⟨e.arrowCongr (ContinuousLinearEquiv.refl ℂ ℂ), ?_⟩
  intro L M
  change L (e.symm M) = M L
  simpa only [e.apply_symm_apply] using (he (e.symm M) L).symm

open scoped ComplexOrder in
/-- Paper: Theorem D.1.5.7, p. 764. The strong dual of the Schwartz–Bruhat space
is barrelled. -/
theorem schwartzBruhat_strongDual_barrelled [SecondCountableTopology G] :
    BarrelledSpace ℂ (StrongDual ℂ (SchwartzBruhat G)) := by
  suffices h : ∀ (E : Type _) [AddCommGroup E] [Module ℂ E] [UniformSpace E]
      [IsUniformAddGroup E] [ContinuousSMul ℂ E] [PolynormableSpace ℂ E] [T2Space E]
      [MontelSpace ℂ E], BarrelledSpace ℂ (StrongDual ℂ E) by
    let : T2Space (SchwartzBruhat G) := schwartzBruhat_t2
    let : MontelSpace ℂ (SchwartzBruhat G) := schwartzBruhat_montel
    exact h (SchwartzBruhat G)
  intro E _ _ _ _ _ _ _ _
  let D := StrongDual ℂ E
  let S : Set (Set E) := {s | IsVonNBounded ℂ s}
  have hS : ⋃₀ S = (univ : Set E) := sUnion_isVonNBounded_eq_univ (𝕜 := ℂ) (E := E)
  have hdense : Dense (Submodule.span ℂ (⋃₀ S) : Set E) := by
    rw [hS, Submodule.span_univ, Submodule.top_coe]
    exact dense_univ
  let : PolynormableSpace ℂ D :=
    uniformConvergenceCLM_polynormable (E := E) (F := ℂ) S (fun _ hs ↦ hs) hdense
  refine ⟨fun p hp ↦ Seminorm.continuous' (r := 1) ?_⟩
  let U := p.closedBall 0 1
  let A := (topDualPairing ℂ E).polar U
  -- The polar of the absorbing unit ball is bounded under every functional on E.
  have hA : IsVonNBounded ℂ A := by
    apply (isVonNBounded_iff_dual_image (E := E) A).mpr
    intro φ
    obtain ⟨c, hc⟩ := (p.absorbent_closedBall_zero one_pos φ).exists
    refine isBounded_iff_forall_norm_le.mpr ⟨‖c‖, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨ψ, hψ, hφ⟩ := hc (mem_singleton φ)
    rw [← hφ]
    change ‖(c • ψ) x‖ ≤ ‖c‖
    rw [smul_apply, norm_smul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hx ψ hψ)
  have hU : IsClosed U := by
    rw [show U = {φ | p φ ≤ 1} from p.closedBall_zero_eq]
    exact hp.isClosed_preimage 1
  let : Module ℝ D := Module.restrictScalars ℝ ℂ D
  let : IsScalarTower ℝ ℂ D := IsScalarTower.restrictScalars ℝ ℂ D
  have haU : AbsConvex ℂ U := ⟨p.balanced_closedBall_zero 1,
    convex_RCLike_iff_convex_real.mpr (p.convex_closedBall 0 1)⟩
  have hzU : 0 ∈ U := p.mem_closedBall_zero.mpr (by simp)
  -- A separating functional is evaluation at a point of A.
  filter_upwards [ContinuousLinearMap.eventually_nhds_zero_mapsTo (σ := RingHom.id ℂ) hA
    (Metric.ball_mem_nhds (0 : ℂ) one_pos)] with φ hφ
  by_contra hnot
  obtain ⟨l, hl, hlt⟩ := exists_dual_norm_le_one_lt_of_notMem hU haU hzU hnot
  obtain ⟨x, rfl⟩ := surjective_strongBidual_eval (E := E) l
  have hx : x ∈ A := fun ψ hψ ↦ hl ψ hψ
  exact (not_lt_of_ge (mem_ball_zero_iff.mp (hφ hx)).le) hlt

/-- On a torus a character is Schwartz. Translation multiplies every derivative
on its vector cover by a scalar of norm one. -/
private theorem torus_character_mem_elementary {n : ℕ}
    (χ : PontryaginDual (Multiplicative (Fin n → AddCircle (1 : ℝ)))) :
    (fun y : ElementaryLieGroup 0 n 0 PUnit.{1} ↦ (χ (Multiplicative.ofAdd y.2.1) : ℂ)) ∈
      elementarySchwartzSubmodule 0 n 0 PUnit.{1} := by
  let X := EuclideanSpace ℝ (Fin 0) × EuclideanSpace ℝ (Fin n)
  let c := (AddMonoidHom.fst _ _).comp ((AddMonoidHom.snd _ _).comp
    (elementaryCoverZeroHom (m := 0) (n := n) (r := 0) (F := PUnit.{1})))
  let ψ : PontryaginDual (Multiplicative X) := χ.comp ⟨AddMonoidHom.toMultiplicative c,
    (elementaryCoverZeroHom_continuous_isOpenMap (m := 0) (n := n) (r := 0) (F := PUnit.{1})).1.snd.fst⟩
  let g (x : X) := (ψ (Multiplicative.ofAdd x) : ℂ)
  have hg : ContDiff ℝ ∞ g := contDiff_vector_character ψ
  have hnorm (k : ℕ) (x : X) (d : Fin k → X) :
      ‖iteratedFDeriv ℝ k g x d‖₊ = ‖iteratedFDeriv ℝ k g 0 d‖₊ := by
    have hshift : (fun z ↦ g (x + z)) = g x • g :=
      funext fun z ↦ congrArg (fun t : Circle ↦ (t : ℂ)) (map_mul ψ (Multiplicative.ofAdd x) (Multiplicative.ofAdd z))
    have he := iteratedFDeriv_comp_add_left (𝕜 := ℝ) (f := g) k x 0
    rw [add_zero, hshift, iteratedFDeriv_const_smul_apply (hg.of_le (by simp)).contDiffAt] at he
    rw [← he]
    simp [g]
  refine ⟨fun _ _ ↦ hg, fun i ↦ ?_⟩
  let f (y : ElementaryLieGroup 0 n 0 PUnit.{1}) := (χ (Multiplicative.ofAdd y.2.1) : ℂ)
  have hpartial (x : X) (z : Fin 0 → ℤ) (b : PUnit.{1}) :
      ‖elementaryPartial f i.2.1 i.2.2.1 x z b‖₊ =
      ‖elementaryPartial f i.2.1 i.2.2.1 0 0 PUnit.unit‖₊ := by
    unfold elementaryPartial
    exact hnorm _ _ _
  change elementarySchwartzBound f i < ⊤
  simp only [elementarySchwartzBound, Finset.univ_eq_empty (α := Fin 0), Finset.prod_empty,
    mul_one, one_mul, hpartial, iSup_const, ENNReal.coe_lt_top]

/-- A Euclidean Schwartz bump can take value one at one point and vanish at a second. -/
private theorem exists_schwartz_bump {m : ℕ} (x y : EuclideanSpace ℝ (Fin m)) :
    ∃ u : SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ, u x = 1 ∧ (y ≠ x → u y = 0) := by
  classical
  let U := if y = x then univ else ({y} : Set (EuclideanSpace ℝ (Fin m)))ᶜ
  have hU : U ∈ 𝓝 x := by
    dsimp only [U]
    split_ifs with hx
    · exact univ_mem
    · exact isOpen_compl_singleton.mem_nhds (fun h ↦ hx (mem_singleton_iff.mp h).symm)
  obtain ⟨f, hs, hc, hd, _, hzero⟩ := exists_contDiff_tsupport_subset (n := ⊤) hU
  let g := Complex.ofRealCLM ∘ f
  have hgc : HasCompactSupport g := hc.comp_left rfl
  refine ⟨hgc.toSchwartzMap (Complex.ofRealCLM.contDiff.comp hd), ?_, ?_⟩
  · change (f x : ℂ) = 1
    rw [hzero, Complex.ofReal_one]
  · intro hx
    have hnot : y ∉ tsupport f := fun h ↦ (show y ∉ ({y} : Set _) by simpa [U, hx] using hs h) rfl
    change (f y : ℂ) = 0
    rw [image_eq_zero_of_notMem_tsupport hnot, Complex.ofReal_zero]

/-- Elementary Schwartz functions separate points and have no common zero.
A pure tensor tests the Euclidean, torus, lattice and finite coordinates. -/
private theorem elementary_stage_separates {m n r : ℕ} {F : Type} [AddCommGroup F]
    [TopologicalSpace F] [DiscreteTopology F] [Finite F] (x y : ElementaryLieGroup m n r F) :
    ∃ f : ElementarySchwartz m n r F, f x ≠ 0 ∧ (y ≠ x → f y ≠ f x) := by
  classical
  let T := Fin n → AddCircle (1 : ℝ)
  obtain ⟨u, hu, huy⟩ := exists_schwartz_bump x.1 y.1
  have hχ : ∃ χ : PontryaginDual (Multiplicative T),
      y.2.1 ≠ x.2.1 → χ (Multiplicative.ofAdd y.2.1) ≠ χ (Multiplicative.ofAdd x.2.1) := by
    by_cases ht : y.2.1 = x.2.1
    · exact ⟨1, fun h ↦ (h ht).elim⟩
    · obtain ⟨χ, hχ⟩ := exists_pontryaginDual_apply_ne_one
        (show Multiplicative.ofAdd y.2.1 / Multiplicative.ofAdd x.2.1 ≠ (1 : Multiplicative T) from div_ne_one.mpr ht)
      rw [map_div, div_ne_one] at hχ
      exact ⟨χ, fun _ ↦ hχ⟩
  obtain ⟨χ, hχ⟩ := hχ
  let v : ElementarySchwartz 0 n 0 PUnit.{1} := ⟨_, torus_character_mem_elementary χ⟩
  let δ (z : Fin r → ℤ) : ℂ := if z = x.2.2.1 then 1 else 0
  have hs : (Function.support δ).Finite :=
    (finite_singleton x.2.2.1).subset fun x hx ↦ by
      by_contra h
      exact hx (ite_eq_right h)
  let s : RapidDecaySequence r := ⟨δ, mem_rapidDecaySequenceSubmodule_of_finiteSupport δ hs⟩
  let c (b : F) : ℂ := if b = x.2.2.2 then 1 else 0
  obtain ⟨φ, _, hφ⟩ := elementarySchwartzTensor_isEmbedding (m := m) (n := n) (r := r) (F := F)
  let test := φ (elementarySchwartzTmul u v s c)
  have htest (w : ElementaryLieGroup m n r F) :
      test w = u w.1 * (χ (Multiplicative.ofAdd w.2.1) : ℂ) * δ w.2.2.1 * c w.2.2.2 :=
    hφ u v s c w
  have hval : test x = (χ (Multiplicative.ofAdd x.2.1) : ℂ) := by simp [htest, hu, δ, c]
  have hne : test x ≠ 0 := hval ▸ Circle.coe_ne_zero _
  refine ⟨test, hne, fun hy ↦ ?_⟩
  rw [htest, hval]
  by_cases hx : y.1 = x.1
  · by_cases hz : y.2.2.1 = x.2.2.1
    · by_cases hb : y.2.2.2 = x.2.2.2
      · have ht : y.2.1 ≠ x.2.1 := fun h ↦ hy (Prod.ext hx (Prod.ext h (Prod.ext hz hb)))
        simpa [hx, hu, hz, hb, δ, c] using
          (show (χ (Multiplicative.ofAdd y.2.1) : ℂ) ≠ (χ (Multiplicative.ofAdd x.2.1) : ℂ) from
            fun he ↦ hχ ht (Subtype.ext he))
      · simpa [c, hb] using (Circle.coe_ne_zero (χ (Multiplicative.ofAdd x.2.1))).symm
    · simpa [δ, hz] using (Circle.coe_ne_zero (χ (Multiplicative.ofAdd x.2.1))).symm
  · simpa [huy hx] using (Circle.coe_ne_zero (χ (Multiplicative.ofAdd x.2.1))).symm
/-- Tests can be nonzero at any given point and distinguish it from any other
point by passing to an elementary quotient in which their ratio survives. -/
private theorem schwartzBruhat_exists_test (x y : G) :
    ∃ f : SchwartzBruhat G, f x ≠ 0 ∧ (y ≠ x → f y ≠ f x) := by
  classical
  let U := if y = x then univ else ({y / x} : Set G)ᶜ
  have hU : U ∈ 𝓝 1 := by
    dsimp only [U]
    split_ifs with h
    · exact univ_mem
    · exact isOpen_compl_singleton.mem_nhds (Ne.symm (div_ne_one.mpr h))
  obtain ⟨D, hD⟩ := exists_lcaDualAnnihilator_subset_nhds hU
  let K := lcaDualAnnihilator D.val
  have hc : IsCompact (K : Set G) := isCompact_lcaDualAnnihilator D.val D.property.1
  have hg : IsBruhatGoodSubgroup K := by
    refine ⟨hc.isClosed, ?_⟩
    rw [show lcaAnnihilator K = D.val from lcaAnnihilator_dualAnnihilator_of_open _ D.property.1]
    exact D.property
  obtain ⟨H, hH⟩ := exists_openCompactlyGeneratedSubgroup_contains ((hc.insert x).insert y)
  let a : BruhatStructuralPair G := ⟨(H.val, OrderDual.toDual K), H.property.1,
    H.property.2, hg, (subset_insert x _).trans ((subset_insert y _).trans hH)⟩
  obtain ⟨e⟩ := a.elementary
  let t : a.val.1 := ⟨x, hH (mem_insert_of_mem _ (mem_insert x _))⟩
  let u : a.val.1 := ⟨y, hH (mem_insert y _)⟩
  let q : a.val.1 →* a.quotient := QuotientGroup.mk' _
  obtain ⟨s, hs, hsep⟩ := elementary_stage_separates (e.equiv (q t)).toAdd (e.equiv (q u)).toAdd
  let f : SchwartzBruhat G := schwartzBruhatStageInclusion a e s
  have hf (z : a.val.1) : f z.val = s (e.equiv (q z)).toAdd := by
    rw [show f z.val = schwartzBruhatStageRealization a e s z.val from rfl,
      schwartzBruhatStageRealization_apply, dite_eq_left z.property]
    rfl
  refine ⟨f, (hf t).symm ▸ hs, fun hxy he ↦ ?_⟩
  have ht := hsep.mt (not_not_intro ((hf u).symm.trans (he.trans (hf t))))
  have hq : q u = q t := e.equiv.injective (not_not.mp ht)
  have hk : y / x ∈ K := (a.quotient_mk_eq_one (u / t)).mp
    (show q (u / t) = 1 by rw [map_div, hq, div_self'])
  simpa [U, hxy] using hD hk

/-- A nuclear space is separable for each of its continuous seminorms. A
totally bounded zero-neighborhood spans the space and has separable span. -/
private theorem seminorm_separable_of_nuclear {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    [PolynormableSpace ℂ E] [T2Space E]
    (h : IsNuclearTVS.{v} E) (p : Seminorm ℂ E) (hp : Continuous p) :
    SeparableSpace (WithLocalSeminorm p) := by
  obtain ⟨V, hV, htot⟩ := (isSchwartzTVS_of_isNuclearTVS h).2 p hp
  let W : Set (WithLocalSeminorm p) := V
  have hW : TotallyBounded W := htot
  have hAbs : Absorbent ℂ W := by
    change Absorbent ℂ V
    exact absorbent_nhds_zero (𝕜 := ℂ) hV
  have hspan : Submodule.span ℂ W = ⊤ := (hAbs.mono (Submodule.subset_span (R := ℂ))).submodule_eq_top
  have hS := hW.isSeparable.span (R := ℂ)
  rw [hspan, Submodule.top_coe] at hS
  exact isSeparable_univ_iff.mp hS

open scoped Pointwise in
/-- Finite products of a compact generating set and its inverse give a countable
compact covering of a compactly generated group. -/
private theorem sigmaCompact_of_compactlyGenerated {A : Type*} [Group A] [TopologicalSpace A]
    [IsTopologicalGroup A] (h : IsCompactlyGeneratedGroup A) : SigmaCompactSpace A := by
  obtain ⟨U, _, hU, hgen⟩ := h
  let V := U ∪ U⁻¹
  have hc (n : ℕ) : IsCompact (V ^ n) := by
    induction n with
    | zero => rw [pow_zero]; exact isCompact_singleton (x := (1 : A))
    | succ n ih => exact pow_succ V n ▸ ih.mul (hU.union hU.inv)
  refine ⟨⟨fun n ↦ V ^ n, hc, iUnion_eq_univ_iff.mpr fun a ↦ ?_⟩⟩
  apply Subgroup.closure_induction_left (p := fun a _ ↦ ∃ n : ℕ, a ∈ V ^ n)
    ⟨0, by simp⟩ _ _ (hgen.symm ▸ Subgroup.mem_top a)
  · rintro x hx y _ ⟨n, hn⟩
    exact ⟨n+1, pow_succ' V n ▸ Set.mul_mem_mul (Or.inl hx : x ∈ V) hn⟩
  · rintro x hx y _ ⟨n, hn⟩
    exact ⟨n+1, pow_succ' V n ▸ Set.mul_mem_mul (Or.inr (Set.inv_mem_inv.mpr hx) : x⁻¹ ∈ V) hn⟩

/-- A countable separating family induces a second-countable topology on each
compact set. The interiors of a compact exhaustion then cover the group. -/
private theorem secondCountable_of_continuous_injection {A : Type*} [TopologicalSpace A]
    [LocallyCompactSpace A] [SigmaCompactSpace A] [T2Space A] {u : A → (ℕ → ℂ)}
    (hu : Continuous u) (hinj : Function.Injective u) : SecondCountableTopology A := by
  let K := CompactExhaustion.choice A
  let (n : ℕ) : CompactSpace (K n) := isCompact_iff_compactSpace.mp (K.isCompact n)
  let (n : ℕ) : SecondCountableTopology (K n) :=
    ((hu.comp (continuous_subtype_val (p := fun x ↦ x ∈ K n))).isClosedEmbedding
      (hinj.comp Subtype.val_injective)).isEmbedding.secondCountableTopology
  let (n : ℕ) : SecondCountableTopology (interior (K n)) :=
    (Topology.IsEmbedding.inclusion (interior_subset : interior (K n) ⊆ K n)).secondCountableTopology
  exact secondCountableTopology_of_countable_cover (fun n ↦ isOpen_interior (s := K n))
    (iUnion_eq_univ_iff.mpr fun x ↦ (K.exists_mem x).elim fun n hn ↦
      ⟨n + 1, K.subset_interior_succ n hn⟩)

/-- Countably many tests that have no common zero cover the group by countably
many compactly generated support subgroups. -/
private theorem sigmaCompact_of_countable_tests (f : ℕ → SchwartzBruhat G)
    (hne : ∀ x : G, ∃ n, f n x ≠ 0) : SigmaCompactSpace G := by
  choose b s hs using fun n ↦ schwartzBruhat_stage_cover (f n)
  let H (n : ℕ) := (b n).1.val.1
  have hc (n : ℕ) : IsSigmaCompact (H n : Set G) := by
    let : SigmaCompactSpace (H n) := sigmaCompact_of_compactlyGenerated (b n).1.property.2.1
    exact isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance
  have hU : ⋃ n, (H n : Set G) = univ := by
    apply iUnion_eq_univ_iff.mpr
    intro x
    obtain ⟨n, hn⟩ := hne x
    refine ⟨n, ?_⟩
    by_contra hnot
    have h := congrArg (fun u : schwartzBruhatSubmodule G ↦ u.val x) (hs n)
    change schwartzBruhatStageRealization (b n).1 (b n).2 (s n) x = f n x at h
    change x ∉ (b n).1.val.1 at hnot
    rw [schwartzBruhatStageRealization_apply, dite_eq_right hnot] at h
    exact hn h.symm
  exact isSigmaCompact_univ_iff.mp (hU ▸ isSigmaCompact_iUnion _ hc)

/-- Evaluation on a countable family of uniformly dense tests separates points
and supplies at least one nonzero value at every point of the group. -/
private theorem countable_tests_of_nuclear (h : IsNuclearTVS.{v} (SchwartzBruhat G)) :
    ∃ u : ℕ → SchwartzBruhat G, (∀ x : G, ∃ n, u n x ≠ 0) ∧
      Function.Injective (fun x : G ↦ fun n ↦ u n x) := by
  let : T2Space (SchwartzBruhat G) := schwartzBruhat_t2_of_stages
  obtain ⟨p, hp, hbound⟩ := exists_schwartzBruhat_uniform_seminorm (G := G)
  let X := WithLocalSeminorm p
  let : SeparableSpace X := seminorm_separable_of_nuclear h p hp
  obtain ⟨u, hu⟩ := exists_dense_seq X
  let ev (x : G) : X →ₗ[ℂ] ℂ := (LinearMap.proj x).comp (schwartzBruhatSubmodule G).subtype
  have hc (x : G) : Continuous (ev x) :=
    ((ev x).mkContinuous 1 (fun f ↦ (hbound f x).trans_eq (one_mul _).symm)).continuous
  refine ⟨u, fun x ↦ ?_, fun x y hxy ↦ ?_⟩
  · by_contra! hz
    have he := hu.equalizer (hc x) (continuous_const (y := (0 : ℂ))) (funext hz)
    obtain ⟨f, hf, _⟩ := schwartzBruhat_exists_test x x
    exact hf (congrFun he f)
  · by_contra hne
    have he := hu.equalizer (hc x) (hc y) (funext fun n ↦ congrFun hxy n)
    obtain ⟨f, _, hf⟩ := schwartzBruhat_exists_test y x
    exact hf hne (congrFun he f)

/-- Paper: Remark D.1.5.8, p. 764. The Schwartz–Bruhat space of a group that
fails second countability fails nuclearity. -/
theorem schwartzBruhat_not_nuclear (hG : ¬ SecondCountableTopology G) :
    ¬ IsNuclearTVS.{v} (SchwartzBruhat G) := by
  intro h
  obtain ⟨u, hne, hinj⟩ := countable_tests_of_nuclear h
  let : SigmaCompactSpace G := sigmaCompact_of_countable_tests u hne
  apply hG (secondCountable_of_continuous_injection (continuous_pi fun n ↦ ?_) hinj)
  obtain ⟨b, e, s, hs⟩ := (mem_schwartzBruhatSubmodule_iff (u n).val).mp (u n).property
  exact hs ▸ continuous_stage_realization b e s

/-- A pointwise family lifting a compact set has bounded range. -/
private theorem bounded_range_of_compact_image {E V W ι : Type*}
    [TopologicalSpace E] [TopologicalSpace V] [AddCommGroup E] [Module ℂ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] (i : V → E) (hi : Continuous i)
    (v : E → W) (hv : Function.Injective v) (P : ι → E) (C : Set V) (hc : IsCompact C)
    (h : ∀ a, v (P a) ∈ (v ∘ i) '' C) : IsVonNBounded ℂ (range P) := by
  refine ((hc.image hi).isVonNBounded (𝕜 := ℂ)).subset (range_subset_iff.mpr fun a ↦ ?_)
  exact (h a).elim fun t ht ↦ ⟨t, ht.1, hv ht.2⟩

/-- On a cofinal cone the projections of a fixed test form a bounded set. -/
private theorem schwartzBruhat_projection_orbit_bounded
    (d : BruhatStructuralPair G) (e : ∀ a : BruhatStructuralPair G, ElementaryLCAPresentation a.quotient)
    (u : SchwartzBruhat G) (P : BruhatStructuralPair G → SchwartzBruhat G)
    (hP : ∀ a, (P a).val = schwartzBruhatStageAverage a u.val) :
    IsVonNBounded ℂ (range fun a : {a : BruhatStructuralPair G // d ≤ a} ↦ P a.val) := by
  refine (schwartzBruhat_exists_stage_above e d u).elim fun c hc ↦ hc.2.elim fun s hs ↦ ?_
  have hu : schwartzBruhatStageRealization c (e c) s = u.val :=
    congrArg (fun f : schwartzBruhatSubmodule G ↦ f.val) hs
  refine (stage_averages_in_compact_disk c (e c) s).elim fun C hC ↦ ?_
  let i := schwartzBruhatStageCLM c (e c)
  refine bounded_range_of_compact_image i i.continuous (fun f : SchwartzBruhat G ↦ f.val)
    Subtype.val_injective _ C hC.1 (fun a ↦ ?_)
  change (P a.val).val ∈ schwartzBruhatStageRealization c (e c) '' C
  rw [hP, ← hu]
  have h₁ : OrderDual.ofDual a.val.val.2 ≤ OrderDual.ofDual d.val.2 := a.property.2
  have h₂ : OrderDual.ofDual c.val.2 ≤ OrderDual.ofDual d.val.2 := hc.1.2
  exact hC.2 a.val (h₁.trans (d.property.2.2.2.trans hc.1.1))
    (h₂.trans (d.property.2.2.2.trans a.property.1))

/-- On each test, consecutive projections in an increasing chain eventually
agree because the two intersection subgroups stabilize on its stage. -/
private theorem schwartzBruhat_projections_stabilize
    (f : SchwartzBruhat G) (P : BruhatStructuralPair G → SchwartzBruhat G)
    (hP : ∀ a, (P a).val = schwartzBruhatStageAverage a f.val)
    (a : ℕ → BruhatStructuralPair G) (ha : Monotone a) :
    ∃ N, ∀ n ≥ N, P (a (n+1)) = P (a n) := by
  refine ((mem_schwartzBruhatSubmodule_iff f.val).mp f.property).elim fun b hb ↦ ?_
  refine hb.elim fun e he ↦ he.elim fun s hs ↦ ?_
  refine (schwartzBruhatStage_average_stabilizes ha b e).imp fun N hN n hn ↦ ?_
  apply Subtype.ext
  rw [hP, hP, ← hs]
  exact hN n hn s

/-- Paper: Theorem D.1.5.7 and Remark D.1.5.8, p. 764. The Schwartz–Bruhat space
is complete for its additive uniformity, including beyond the second-countable case. -/
theorem schwartzBruhat_complete :
    CompleteSpace (SchwartzBruhat G) := by
  classical
  let E := SchwartzBruhat G
  let A := BruhatStructuralPair G
  let : BarrelledSpace ℂ E := schwartzBruhat_barrelled_of_stages
  let d : A := (bruhatStructuralPair_filtered (G := G)).1.some
  let e (a : A) := a.elementary.some
  let R (a : A) : E →L[ℂ] SchwartzBruhatStage (e a) := (schwartzBruhatStage_average_retraction a (e a)).choose
  have hR (a : A) := (schwartzBruhatStage_average_retraction a (e a)).choose_spec
  let i (a : A) := schwartzBruhatStageCLM a (e a)
  let P (a : A) := (i a).comp (R a)
  have hP (a : A) (u : E) : (P a u).val = schwartzBruhatStageAverage a u.val := funext ((hR a).2 u)
  let I := {a : A // d ≤ a}
  let : Nonempty I := ⟨⟨d, le_rfl⟩⟩
  let Q (a : I) := P a.val
  have hB (u : E) : IsVonNBounded ℂ (range fun a : I ↦ Q a u) :=
    schwartzBruhat_projection_orbit_bounded d e u (fun a ↦ P a u) (fun a ↦ hP a u)
  have hfix (u : E) (a : I) : ∃ b ≥ a, Q b u = u := by
    refine (schwartzBruhat_exists_stage_above e a.val u).elim fun b hb ↦ ?_
    obtain ⟨hb, s, hs⟩ := hb
    refine ⟨⟨b, a.property.trans hb⟩, hb, ?_⟩
    change i b (R b u) = u
    change i b s = u at hs
    rw [← hs]
    exact congrArg (i b) ((hR b).1 s)
  have hstable (a : ℕ → I) (ha : Monotone a) (u : E) :
      ∃ N, ∀ n ≥ N, Q (a (n+1)) u = Q (a n) u :=
    schwartzBruhat_projections_stabilize u (fun b ↦ P b u) (fun b ↦ hP b u) (fun n ↦ (a n).val) (fun _ _ h ↦ ha h)
  obtain ⟨p, hp, hsep⟩ := exists_schwartzBruhat_uniform_seminorm (G := G)
  have hpos (u : E) (hu : u ≠ 0) : 0 < p u := by
    by_contra! hn
    apply hu
    refine Subtype.ext (funext fun x ↦ ?_)
    exact norm_le_zero_iff.mp ((hsep u x).trans hn)
  refine complete_of_stabilizing_projections Q hB hfix hstable p hp hpos (fun F hF a ↦ ?_)
  let : CompleteSpace (SchwartzBruhatStage (e a.val)) := elementarySchwartz_isFrechet.choose_spec.2.2
  exact cauchy_projection_limit (R a.val) (i a.val) (R a.val).uniformContinuous (i a.val).continuous hF

/-- Compact lifting controls all the continuous direct sum seminorms by seminorms
of the difference coordinates. This suffices for acyclicity of a Fréchet system. -/
private theorem acyclic_of_compact_lifting
    {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [T2Space E]
    {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Module ℂ (X n)]
    [∀ n, TopologicalSpace (X n)] (hX : ∀ n, IsFrechetTVS (X n))
    {j : ∀ n, X n →L[ℂ] X (n + 1)} {i : ∀ n, X n →L[ℂ] E}
    (h : IsInjectiveLCLimit j i) (hlift : ∀ K : Set E, IsCompact K →
      ∃ n, ∃ C : Set (X n), IsCompact C ∧ i n '' C = K) : IsAcyclicSystem j := by
  classical
  let _ : ∀ (k : ℕ) (z : X k), Decidable (z ≠ 0) := fun _ _ ↦ Classical.propDecidable _
  choose hadd hpoly hmetric _ using hX
  let : ∀ k, IsTopologicalAddGroup (X k) := hadd
  let : ∀ k, PolynormableSpace ℂ (X k) := hpoly
  let : ∀ k, MetrizableSpace (X k) := hmetric
  let D := ⨁ k, X k
  let lof := DirectSum.lof ℂ ℕ X
  let : TopologicalSpace D := locallyConvexFinalTopology lof
  have hD : WithSeminorms
      (Subtype.val : {p : Seminorm ℂ D // ∀ k, Continuous (p ∘ lof k)} → Seminorm ℂ D) :=
    ⟨rfl⟩
  let : IsTopologicalAddGroup D := hD.isTopologicalAddGroup
  let : PolynormableSpace ℂ D := hD.toPolynormableSpace
  have hlof (k : ℕ) : Continuous (lof k) :=
    hD.continuous_of_continuous_comp _ fun p ↦ p.property k
  let σ : D →ₗ[ℂ] D := directSumDifference j
  have hσ : Continuous σ := by
    apply hD.continuous_of_continuous_comp
    intro p
    refine hD.continuous_seminorm (i := ⟨p.val.comp σ, fun k ↦ ?_⟩)
    change Continuous (fun z : X k ↦ p.val (directSumDifference j (DirectSum.lof ℂ ℕ X k z)))
    simp_rw [directSumDifference_lof]
    exact (hD.continuous_seminorm (i := p)).comp
      ((hlof k).sub ((hlof (k+1)).comp (j k).continuous))
  have hinj : Function.Injective σ := by
    intro x y hxy
    apply DFinsupp.ext
    intro k
    induction k with
    | zero =>
      exact (directSumDifference_apply j x).1.symm.trans
        ((congrArg (fun z : D ↦ z 0) hxy).trans (directSumDifference_apply j y).1)
    | succ k ih =>
      have heq : directSumDifference j x (k+1) = directSumDifference j y (k+1) :=
        congrArg (fun z : D ↦ z (k+1)) hxy
      rwa [(directSumDifference_apply j x).2 k, (directSumDifference_apply j y).2 k, ih,
        sub_left_inj] at heq
  refine ⟨⟨IsTopologicalAddGroup.isInducing_iff_nhds_zero.mpr ?_, hinj⟩,
    h.closedRange_directSumDifference_iff.mpr inferInstance⟩
  apply le_antisymm
  · simpa only [← map_le_iff_le_comap, Tendsto, map_zero] using hσ.tendsto 0
  · apply (PolynormableSpace.hasBasis_zero_ball ℂ D).ge_iff.mpr
    intro p hp
    let s (n : ℕ) := p.comp (lof n)
    obtain ⟨r, hr, hbound⟩ := directSumDifference_seminorm_bound_of_interpolation
      (h.exists_stage_seminorm_interpolation hlift) s (fun n ↦ hp.comp (hlof n))
    let q := directSumSeminorm r
    have hq : Continuous q := by
      refine hD.continuous_seminorm (i := ⟨q, fun n ↦ ?_⟩)
      change Continuous (fun z : X n ↦ directSumSeminorm r (DirectSum.lof ℂ ℕ X n z))
      simpa only [directSumSeminorm_lof] using hr n
    refine Filter.mem_comap.mpr ⟨q.ball 0 1, q.ball_mem_nhds hq zero_lt_one, ?_⟩
    intro x hx
    apply p.mem_ball_zero.mpr
    apply lt_of_le_of_lt _ (q.mem_ball_zero.mp hx)
    refine le_trans ?_ (hbound x)
    rw [directSumSeminorm_apply _ _ x.support Subset.rfl]
    have hsum := Finset.le_sum_of_subadditive p (map_zero p).le
      (map_add_le_add p) x.support (fun n ↦ lof n (x n))
    rwa [show (∑ n ∈ x.support, lof n (x n)) = x from DirectSum.sum_support_of x] at hsum
/-- A Fréchet source factors through a stage of any exhaustive injective Fréchet system. -/
private theorem factor_through_frechet_stage
    {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [T2Space E]
    {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Module ℂ (X n)]
    [∀ n, TopologicalSpace (X n)] (hX : ∀ n, IsFrechetTVS (X n))
    {j : ∀ n, X n →L[ℂ] X (n + 1)} {i : ∀ n, X n →L[ℂ] E} (h : IsInjectiveLCLimit j i)
    {Y : Type*} [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    (hY : IsFrechetTVS Y) (f : Y →L[ℂ] E) :
    ∃ n, ∃ g : Y →L[ℂ] X n, (i n).comp g = f := by
  apply frechet_factorization hX i h.injective _ h.exhaustive hY f
  rintro n _ ⟨x, rfl⟩
  exact ⟨j n x, DFunLike.congr_fun (h.compatible n) x⟩

/-- Paper: Proposition D.1.5.9, p. 764. Every defining countable sequence
of Fréchet stages for the Schwartz–Bruhat space is acyclic in the sense of §C.1.5.
Deviation: A defining sequence is expressed using the compatible injections and the
locally convex limit topology of `IsInjectiveLCLimit`. -/
theorem schwartzBruhat_acyclic [SecondCountableTopology G]
    {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Module ℂ (X n)]
    [∀ n, TopologicalSpace (X n)] (hX : ∀ n, IsFrechetTVS (X n))
    {j : ∀ n, X n →L[ℂ] X (n + 1)} {i : ∀ n, X n →L[ℂ] SchwartzBruhat G}
    (h : IsInjectiveLCLimit j i) : IsAcyclicSystem j := by
  let : T2Space (SchwartzBruhat G) := schwartzBruhat_t2
  apply acyclic_of_compact_lifting hX h
  intro K hK
  have hB := schwartzBruhat_bounded_image_stage (G := G) (hK.isVonNBounded ℂ)
  refine hB.elim fun a ha ↦ ha.elim fun e he ↦ he.elim fun C hC ↦ ?_
  let f := schwartzBruhatStageCLM a e
  have hKC : IsCompact C := (schwartzBruhatStage_isEmbedding a e).isCompact_iff.mpr
    (hC.2.symm ▸ hK)
  have hfac := factor_through_frechet_stage hX h elementarySchwartz_isFrechet f
  refine hfac.elim fun n hn ↦ hn.elim fun g hg ↦ ?_
  refine ⟨n, g '' C, hKC.image g.continuous, ?_⟩
  rw [image_image]
  exact (congrArg (fun l : SchwartzBruhatStage e →L[ℂ] SchwartzBruhat G ↦ l '' C) hg).trans hC.2

/-- Paper: Theorem D.1.5.10, p. 765. A cofinal increasing sequence of structural
stages gives a short topologically exact sequence. The difference map embeds
as the closed kernel of the quotient map given by summing the stage inclusions.
Deviation: Each stage is expressed in an elementary presentation and the difference
map uses the induced maps between successive presentations. -/
theorem schwartzBruhat_exists_topologicallyExact [SecondCountableTopology G] :
    ∃ (a : ℕ → BruhatStructuralPair G)
      (e : ∀ n, ElementaryLCAPresentation (a n).quotient)
      (j : ∀ n, SchwartzBruhatStage (e n) →L[ℂ] SchwartzBruhatStage (e (n + 1))),
      Monotone a ∧ (∀ b, ∃ n, b ≤ a n) ∧
      (∀ n f, schwartzBruhatStageRealization (a (n + 1)) (e (n + 1)) (j n f) =
        schwartzBruhatStageRealization (a n) (e n) f) ∧
      let X := fun n ↦ SchwartzBruhatStage (e n)
      let q := DirectSum.toModule ℂ ℕ (SchwartzBruhat G)
        (fun n ↦ (show X n →ₗ[ℂ] SchwartzBruhat G from schwartzBruhatStageInclusion (a n) (e n)))
      letI := locallyConvexFinalTopology (DirectSum.lof ℂ ℕ X)
      IsClosedEmbedding (directSumDifference j) ∧
        LinearMap.range (directSumDifference j) = LinearMap.ker q ∧ IsQuotientMap q := by
  have hs := schwartzBruhat_exists_cofinal_system (G := G)
  refine hs.elim fun a ha ↦ ha.elim fun e he ↦ he.elim fun j hj ↦ ?_
  have h := hj.2.2.2.2
  refine ⟨a, e, j, hj.1, hj.2.1, hj.2.2.1,
    isAcyclicSystem_of_strict_frechet (fun n ↦ elementarySchwartz_isFrechet) j
      (fun n ↦ (hj.2.2.2.1 n).isEmbedding), ?_, ?_⟩
  · exact SetLike.ext' h.range_directSumDifference
  · exact h.isQuotientMap_directSum

/-- If the Schwartz–Bruhat limit is metrizable, a single structural stage covers it.
The strict Fréchet presentation is then complete, so its identity factors through a stage. -/
private theorem schwartzBruhat_surjective_stage_of_metrizable [SecondCountableTopology G]
    [MetrizableSpace (SchwartzBruhat G)] :
    ∃ (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient),
      Function.Surjective (schwartzBruhatStageCLM a e) := by
  let : T2Space (SchwartzBruhat G) := schwartzBruhat_t2
  have hs := schwartzBruhat_exists_cofinal_system (G := G)
  refine hs.elim fun a ha ↦ ha.elim fun e he ↦ he.elim fun j hj ↦ ?_
  let : ∀ n, T2Space (SchwartzBruhatStage (e n)) := fun _ ↦ elementarySchwartz_t2
  have hF (n : ℕ) : IsFrechetTVS (SchwartzBruhatStage (e n)) := elementarySchwartz_isFrechet
  have hc := (strictLCLimit_complete_nonmetrizable (fun n ↦ (hF n).choose_spec.2.2)
    hj.2.2.2.2 (fun n ↦ (hj.2.2.2.1 n).isEmbedding)).1
  have hlim : IsFrechetTVS (SchwartzBruhat G) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  have hfac := factor_through_frechet_stage hF hj.2.2.2.2 hlim (ContinuousLinearMap.id ℂ _)
  refine hfac.elim fun n hn ↦ hn.elim fun g hg ↦ ⟨a n, e n, fun x ↦ ?_⟩
  exact ⟨g x, DFunLike.congr_fun hg x⟩

/-- The indicator of a compact open subgroup is realized on its one-point quotient. -/
private theorem schwartzBruhat_compactOpen_indicator (H : OpenSubgroup G)
    (hc : IsCompact (H : Set G)) : ∃ f : SchwartzBruhat G, ∀ x ∈ H, f x = 1 := by
  let : CompactSpace H.toSubgroup := isCompact_iff_compactSpace.mp hc
  let : CompactSpace (lcaAnnihilator H.toSubgroup) :=
    isCompact_iff_compactSpace.mp (isCompact_lcaAnnihilator _ H.isOpen)
  let a : BruhatStructuralPair G := ⟨(H.toSubgroup, OrderDual.toDual H.toSubgroup),
    H.isOpen, isCompactlyGeneratedGroup_of_compact, ⟨H.isClosed, isOpen_lcaAnnihilator _ hc,
      (isCompactlyGeneratedGroup_of_compact (G := lcaAnnihilator H.toSubgroup))⟩, le_rfl⟩
  let : Subsingleton a.quotient := QuotientGroup.subsingleton_iff.mpr (by
    exact top_unique fun x _ ↦ x.property)
  let : Unique a.quotient := uniqueOfSubsingleton 1
  let Y := Multiplicative (ElementaryLieGroup 0 0 0 PUnit)
  let : Unique Y := uniqueOfSubsingleton 1
  let e : ElementaryLCAPresentation a.quotient :=
    ⟨0, 0, 0, PUnit, (MulEquiv.ofUnique : a.quotient ≃* Y).toContinuousMulEquiv
      (fun S ↦ iff_of_true (isOpen_discrete _) (isOpen_discrete _))⟩
  have hf : (fun _ ↦ (1 : ℂ)) ∈ elementarySchwartzSubmodule 0 0 0 PUnit := by
    refine ⟨fun _ _ ↦ contDiff_const, fun i ↦ ?_⟩
    rw [Subsingleton.elim i (0, 0, 0, 0), elementarySchwartzBound_zero]
    simp
  let s : SchwartzBruhatStage e := ⟨_, hf⟩
  refine ⟨schwartzBruhatStageInclusion a e s, fun x hx ↦ ?_⟩
  rw [schwartzBruhatStageInclusion_apply, schwartzBruhatStageRealization_apply,
    dite_eq_left (show x ∈ a.val.1 from hx)]

end MainTheorems

/-! ## Deferred from §C.1 -/

section DeferredFromC1

section SmallSubgroups

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [hT2 : T2Space G] [LocallyCompactSpace G]

/-- A first countable vector topology admits a nonzero rescaling of any sequence
whose terms then form a bounded set. -/
private theorem exists_bounded_rescaling {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [FirstCountableTopology E] (f : ℕ → E) : ∃ c : ℕ → ℂ, (∀ n, c n ≠ 0) ∧
      IsVonNBounded ℂ (range fun n ↦ c n • f n) := by
  obtain ⟨U, hU⟩ := (𝓝 (0 : E)).exists_antitone_basis
  have h (n : ℕ) : ∃ z : ℂ, z ≠ 0 ∧ z • f n ∈ U n := by
    have hm : (fun z : ℂ ↦ z • f n) ⁻¹' U n ∈ 𝓝 (0 : ℂ) :=
      (continuous_id.smul continuous_const).continuousAt.preimage_mem_nhds (by change U n ∈ 𝓝 ((0 : ℂ) • f n); simpa only [zero_smul] using hU.mem n)
    have hz : ∀ᶠ z : ℂ in 𝓝[≠] 0, z ≠ 0 := self_mem_nhdsWithin
    exact (hz.and (nhdsWithin_le_nhds hm : ∀ᶠ z : ℂ in 𝓝[≠] 0, z • f n ∈ U n)).exists
  choose c hc hmem using h
  refine ⟨c, hc, Filter.Tendsto.isVonNBounded_range (𝕜 := ℂ) (x := (0 : E)) ?_⟩
  apply hU.1.tendsto_right_iff.mpr
  intro n _
  filter_upwards [eventually_ge_atTop n] with m hm
  exact hU.2 hm (hmem m)

omit hT2 in
/-- In a structural stage all sufficiently small cyclic subgroups of the ambient
group lie in the kernel of the elementary quotient. -/
private theorem stage_kernel_contains_small_powers (a : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation a.quotient) :
    ∃ U ∈ 𝓝 (1 : G), ∀ x : G, (∀ k : ℕ, x ^ k ∈ U) → x ∈ OrderDual.ofDual a.val.2 := by
  let : LocallyCompactSpace a.val.1 := a.property.1.isOpenEmbedding_subtypeVal.locallyCompactSpace
  let : T1Space a.quotient :=
    QuotientGroup.t1Space_iff.mpr (a.property.2.2.1.1.preimage continuous_subtype_val)
  obtain ⟨W, hW, hPow⟩ := exists_nhds_one_of_isLocallyEuclidean
    (locallyEuclidean_of_elementaryPresentation e)
  let q : a.val.1 →* a.quotient := QuotientGroup.mk' _
  have hpre : q ⁻¹' W ∈ 𝓝 (1 : a.val.1) :=
    (QuotientGroup.continuous_mk (N := _) : Continuous q).continuousAt.preimage_mem_nhds
      (by change W ∈ 𝓝 (q 1); rwa [map_one])
  refine ⟨Subtype.val '' (q ⁻¹' W),
    a.property.1.isOpenEmbedding_subtypeVal.isOpenMap.image_mem_nhds hpre, fun x hx ↦ ?_⟩
  obtain ⟨y, _, rfl⟩ := (pow_one x ▸ hx 1 : x ∈ Subtype.val '' (q ⁻¹' W))
  apply (a.quotient_mk_eq_one y).mp
  apply hPow
  intro k
  change q y ^ k ∈ W
  rw [← map_pow]
  obtain ⟨z, hz, hzy⟩ := hx k
  exact (Subtype.ext hzy : z = y ^ k) ▸ hz

/-- A sequence of nonidentity points generating arbitrarily small cyclic groups
obstructs metrizability, since bounded tests must share a single stage kernel. -/
private theorem schwartzBruhat_not_metrizable_of_small_powers (y : ℕ → G)
    (hne : ∀ n, y n ≠ 1)
    (hsmall : ∀ U ∈ 𝓝 (1 : G), ∀ᶠ n in atTop, ∀ k : ℕ, (y n) ^ k ∈ U) :
    ¬ MetrizableSpace (SchwartzBruhat G) := by
  intro hmetric
  choose f _ hsep using fun n ↦ schwartzBruhat_exists_test 1 (y n)
  have hf (n : ℕ) := hsep n (hne n)
  obtain ⟨c, hc, hbounded⟩ := exists_bounded_rescaling f
  obtain ⟨a, e, C, _, hC⟩ := schwartzBruhat_bounded_lift hbounded
  obtain ⟨U, hU, hK⟩ := stage_kernel_contains_small_powers a e
  obtain ⟨n, hn⟩ := (hsmall U hU).exists
  obtain ⟨s, _, hs⟩ := hC.ge (mem_range_self n)
  have hval := stage_realization_mul_kernel a e s (hK _ hn) 1
  rw [mul_one] at hval
  let i : SchwartzBruhatStage e →ₗ[ℂ] SchwartzBruhat G := schwartzBruhatStageInclusion a e
  change i s = _ at hs
  change (i s) (y n) = (i s) 1 at hval
  rw [hs] at hval
  exact hf n (mul_left_cancel₀ (hc n) hval)

/-- In an additive ultrametric field, powers of a small nonzero scalar generate
cyclic additive subgroups eventually contained in each zero-neighborhood. -/
private theorem not_metrizable_of_additive_local_embedding {L : Type*} [NontriviallyNormedField L]
    [IsUltrametricDist L] (j : Multiplicative L →* G) (hj : Continuous j)
    (hinj : ∀ {x : L}, j (Multiplicative.ofAdd x) = 1 → x = 0) :
    ¬ MetrizableSpace (SchwartzBruhat G) := by
  obtain ⟨π, hpos, hlt⟩ := NormedField.exists_norm_lt_one L
  let y (n : ℕ) := j (Multiplicative.ofAdd (π ^ n))
  apply schwartzBruhat_not_metrizable_of_small_powers y
  · intro n he
    exact pow_ne_zero _ (norm_pos_iff.mp hpos) (hinj (by simpa [y] using he))
  · intro U hU
    have hpre : (j ∘ Multiplicative.ofAdd) ⁻¹' U ∈ 𝓝 (0 : L) :=
      (hj.comp continuous_ofAdd).continuousAt.preimage_mem_nhds (by simpa [Function.comp_def] using hU)
    obtain ⟨H, hH⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ hpre
    filter_upwards [(tendsto_pow_atTop_nhds_zero_of_norm_lt_one hlt)
      (H.isOpen.mem_nhds H.zero_mem)] with n hn
    intro k
    have h := hH (H.nsmul_mem hn k)
    change j (Multiplicative.ofAdd (k • π ^ n)) ∈ U at h
    simpa only [ofAdd_nsmul, map_pow] using h

/-- At a nonarchimedean place, all positive powers of a unit close to one stay
within the same distance of one. -/
private theorem local_unit_pow_bound {L : Type*} [NormedField L] [IsUltrametricDist L]
    (x : L) (hx : ‖x‖ ≤ 1) (k : ℕ) : ‖x ^ k - 1‖ ≤ ‖x - 1‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, show x ^ k * x - 1 = (x ^ k - 1) * x + (x - 1) by ring]
    apply (IsUltrametricDist.norm_add_le_max _ _).trans
    rw [max_le_iff, norm_mul]
    exact ⟨(mul_le_of_le_one_right (norm_nonneg _) hx).trans ih, le_rfl⟩

/-- Principal units approaching one give small cyclic groups under any continuous
homomorphism with trivial kernel. -/
private theorem not_metrizable_of_local_unit_embedding {L : Type*} [NontriviallyNormedField L]
    [IsUltrametricDist L] (j : Lˣ →* G) (hj : Continuous j)
    (hinj : ∀ u, j u = 1 → u = 1) : ¬ MetrizableSpace (SchwartzBruhat G) := by
  obtain ⟨π, hpos, hlt⟩ := NormedField.exists_norm_lt_one L
  let a (n : ℕ) := π ^ (n + 1)
  have ha (n : ℕ) : ‖a n‖ < 1 := by
    change ‖π ^ (n + 1)‖ < 1
    rw [norm_pow]
    exact pow_lt_one₀ hpos.le hlt n.succ_ne_zero
  have hne (n : ℕ) : 1 + a n ≠ 0 := by
    intro he
    have h := ha n
    rw [show a n = -1 by linear_combination he, norm_neg, norm_one] at h
    exact lt_irrefl _ h
  let u (n : ℕ) := Units.mk0 (1 + a n) (hne n)
  apply schwartzBruhat_not_metrizable_of_small_powers (fun n ↦ j (u n))
  · intro n h
    have := congrArg Units.val (hinj _ h)
    exact pow_ne_zero _ (norm_pos_iff.mp hpos) (add_eq_left.mp this)
  · intro U hU
    have hpre : j ⁻¹' U ∈ 𝓝 (1 : Lˣ) :=
      hj.continuousAt.preimage_mem_nhds (by rwa [map_one])
    rw [Units.isEmbedding_val₀.isInducing.nhds_eq_comap] at hpre
    obtain ⟨W, hW, hsub⟩ := mem_comap.mp hpre
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hW
    have hlim : Tendsto a atTop (𝓝 0) := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hlt).comp
      (tendsto_add_atTop_nat 1)
    filter_upwards [hlim (Metric.ball_mem_nhds (0 : L) hr)] with n hn
    intro k
    rw [← map_pow]
    apply hsub
    apply hball
    rw [Metric.mem_ball, dist_eq_norm]
    change ‖(1 + a n) ^ k - 1‖ < r
    have hb : ‖1 + a n‖ ≤ 1 := (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (norm_one.le) (ha n).le)
    exact (local_unit_pow_bound _ hb k).trans_lt (by simpa [dist_eq_norm] using hn)

end SmallSubgroups

open NumberField

section NumberFields

open IsDedekindDomain
open scoped RestrictedProduct NumberField.AdeleRing IsDedekindDomain.FiniteAdeleRing

/-- A number field has a finite place since its ring of integers is not a field. -/
private theorem finitePlace_nonempty (F : Type*) [Field F] [NumberField F] :
    Nonempty (HeightOneSpectrum (𝓞 F)) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 F)
  exact ⟨⟨m, hm.isPrime, NeZero.ne m⟩⟩

/-- Paper: Remark C.1.3.3, p. 660. The Schwartz–Bruhat space of the additive
adele ring of a number field is nonmetrizable. -/
theorem schwartzBruhat_adele_not_metrizable (F : Type*) [Field F] [NumberField F] :
    ¬ MetrizableSpace (SchwartzBruhat (Multiplicative (AdeleRing (𝓞 F) F))) := by
  classical
  let V := HeightOneSpectrum (𝓞 F)
  let v : V := (finitePlace_nonempty F).some
  let A (w : V) := w.adicCompletionIntegers F
  let L := v.adicCompletion F
  let : NontriviallyNormedField L := Valued.toNontriviallyNormedField (v.adicCompletion F) _
  let (w : V) : CompactSpace (A w) := compactSpace_adicCompletionIntegers w
  let : Fact (∀ w : V, IsOpen (A w : Set (w.adicCompletion F))) :=
    ⟨fun w ↦ Valued.isOpen_valuationSubring _⟩
  let : LocallyCompactSpace (Multiplicative 𝔸[F]) := by
    change LocallyCompactSpace (InfiniteAdeleRing F × (Πʳ w : V, [w.adicCompletion F, A w]))
    infer_instance
  let : T2Space (Multiplicative 𝔸[F]) := by
    change T2Space (((w : InfinitePlace F) → w.Completion) × (Πʳ w : V, [w.adicCompletion F, A w]))
    infer_instance
  let j : L →+ 𝔸[F] := (0 : L →+ InfiniteAdeleRing F).prod (RestrictedProduct.singleAddMonoidHom A v)
  have hj : Continuous j := by
    apply continuous_const.prodMk
    apply continuous_restrictedProduct_of_uniform
    · intro w
      exact (continuous_apply w).comp (continuous_single (A := fun u : V ↦ u.adicCompletion F) v)
    · filter_upwards [eventually_cofinite_ne v] with w hw x
      change Pi.single v x w ∈ A w
      rw [Pi.single_eq_of_ne hw]
      exact (A w).zero_mem
  apply not_metrizable_of_additive_local_embedding (AddMonoidHom.toMultiplicative j) hj
  intro x he
  have h := congrArg (fun t : Multiplicative 𝔸[F] ↦ t.toAdd.2 v) he
  change RestrictedProduct.single A v x v = 0 at h
  exact (RestrictedProduct.single_eq_same ..).symm.trans h

/-- Paper: Remark C.1.3.3, p. 660. The Schwartz–Bruhat space of a number field's
idele class group is nonmetrizable. -/
theorem schwartzBruhat_ideleClass_not_metrizable (F : Type*) [Field F] [NumberField F] :
    ¬ MetrizableSpace (SchwartzBruhat (IdeleClassGroup (𝓞 F) F)) := by
  classical
  let V := HeightOneSpectrum (𝓞 F)
  let v : V := (finitePlace_nonempty F).some
  let L := v.adicCompletion F
  let : NontriviallyNormedField L := Valued.toNontriviallyNormedField (v.adicCompletion F) _
  let C := IdeleClassGroup (𝓞 F) F
  let : T2Space C := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.1
  let : LocallyCompactSpace C := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.1
  let : IsTopologicalGroup (IdeleGroup (𝓞 F) F) := (ideleGroup_topology F).2.2.1
  let j : Lˣ →* C := IdeleClassGroup.ofAdicCompletion (𝓞 F) F v
  have hj : Continuous j := by
    apply QuotientGroup.continuous_mk.comp
    apply Continuous.units_map
    apply continuous_const.prodMk
    apply continuous_restrictedProduct_of_uniform
    · intro w
      exact (continuous_apply w).comp (continuous_mulSingle (A := fun u : V ↦ u.adicCompletion F) v)
    · filter_upwards [eventually_cofinite_ne v] with w hw x
      change Pi.mulSingle v x w ∈ w.adicCompletionIntegers F
      rw [Pi.mulSingle_eq_of_ne hw]
      exact (w.adicCompletionIntegers F).one_mem
  have hinj (u : Lˣ) (h : j u = 1) : u = 1 := by
    obtain ⟨b, hb⟩ := (QuotientGroup.eq_one_iff (N := IdeleGroup.principalSubgroup (𝓞 F) F)
      (IdeleGroup.ofAdicCompletion (𝓞 F) F v u)).mp h
    have hb₁ := congrArg (fun d : IdeleGroup (𝓞 F) F ↦ d.val.1) hb
    have hbone : b = 1 := by
      apply Units.ext
      apply (algebraMap F (InfiniteAdeleRing F)).injective
      change algebraMap F (InfiniteAdeleRing F) b.val = 1 at hb₁
      change algebraMap F (InfiniteAdeleRing F) b.val = algebraMap F (InfiniteAdeleRing F) 1
      rwa [map_one]
    subst b
    have hv := congrArg (fun d : IdeleGroup (𝓞 F) F ↦ d.val.2 v) hb
    apply Units.ext
    change (1 : L) = RestrictedProduct.mulSingle (fun w : V ↦ w.adicCompletionIntegers F) v u.val v at hv
    exact (RestrictedProduct.mulSingle_eq_same ..).symm.trans hv.symm
  exact not_metrizable_of_local_unit_embedding j hj hinj

end NumberFields

variable (L : Type*) [NontriviallyNormedField L] [IsUltrametricDist L] [LocallyCompactSpace L]

/-- The compact sets of the additive completion are contained in compact open subgroups. -/
private theorem localField_exists_compactOpenSubgroup {s : Set (Multiplicative L)} (hs : IsCompact s) :
    ∃ H : OpenSubgroup (Multiplicative L), IsCompact (H : Set (Multiplicative L)) ∧ s ⊆ H := by
  let := (ProperSpace.of_locallyCompactSpace L : ProperSpace L)
  have hs' : IsCompact (Multiplicative.toAdd '' s) := hs.image continuous_toAdd
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall 0).1 hs'.isBounded
  let B := IsUltrametricDist.closedBall_openAddSubgroup L
    (lt_max_of_lt_right (zero_lt_one' ℝ) : 0 < max r 1)
  let H : OpenSubgroup (Multiplicative L) := ⟨B.toAddSubgroup.toSubgroup, B.isOpen⟩
  refine ⟨H, isCompact_closedBall (0 : L) _, fun x hx ↦ ?_⟩
  exact Metric.closedBall_subset_closedBall (le_max_left r _) (hr (mem_image_of_mem _ hx))

/-- The open subgroup of a structural pair for the additive completion is compact. -/
private theorem localField_bruhatSubgroup_compact (a : BruhatStructuralPair (Multiplicative L)) :
    IsCompact (a.val.1 : Set (Multiplicative L)) := by
  obtain ⟨U, -, hU, hgen⟩ := a.property.2.1
  obtain ⟨H, hH, hUH⟩ :=
    localField_exists_compactOpenSubgroup L (hU.image continuous_subtype_val)
  refine hH.of_isClosed_subset (a.val.1.isClosed_of_isOpen a.property.1) ?_
  have h := ((H.toSubgroup.comap a.val.1.subtype).closure_le).2
    (fun x hx ↦ hUH (mem_image_of_mem _ hx))
  rw [hgen] at h
  exact fun x hx ↦ h (Subgroup.mem_top (x := (⟨x, hx⟩ : a.val.1)))

/-- Paper: Remark C.1.3.3, p. 660. The Schwartz–Bruhat space of the additive
group of a nonarchimedean local field is nonmetrizable. -/
theorem schwartzBruhat_localField_not_metrizable :
    ¬ MetrizableSpace (SchwartzBruhat (Multiplicative L)) := by
  intro hmetric
  let : ProperSpace L := ProperSpace.of_locallyCompactSpace L
  let : SecondCountableTopology (Multiplicative L) := inferInstanceAs (SecondCountableTopology L)
  have hs := schwartzBruhat_surjective_stage_of_metrizable (G := Multiplicative L)
  refine hs.elim fun a ha ↦ ha.elim fun e h ↦ ?_
  have hAll (x : Multiplicative L) : x ∈ a.val.1 := by
    obtain ⟨H, hH, hx⟩ := localField_exists_compactOpenSubgroup L (isCompact_singleton (x := x))
    obtain ⟨f, hf⟩ := schwartzBruhat_compactOpen_indicator H hH
    obtain ⟨s, rfl⟩ := h f
    by_contra hnot
    have hval := hf x (hx (mem_singleton x))
    change schwartzBruhatStageRealization a e s x = 1 at hval
    rw [schwartzBruhatStageRealization_apply, dite_eq_right hnot] at hval
    exact zero_ne_one hval
  have hcompact := localField_bruhatSubgroup_compact L a
  rw [show (a.val.1 : Set (Multiplicative L)) = univ from eq_univ_of_forall hAll] at hcompact
  exact (not_compactSpace_iff.mpr (inferInstance : NoncompactSpace L)) ⟨hcompact⟩

/-- Every elementary stage of an ultrametric local field is finite-dimensional.
A sufficiently small open subgroup maps trivially to its elementary quotient. -/
private theorem localField_stage_finiteDimensional
    (a : BruhatStructuralPair (Multiplicative L)) (e : ElementaryLCAPresentation a.quotient) :
    FiniteDimensional ℂ (SchwartzBruhatStage e) := by
  let : CompactSpace a.val.1 := isCompact_iff_compactSpace.mp (localField_bruhatSubgroup_compact L a)
  let : T1Space a.quotient := QuotientGroup.t1Space_iff.mpr
    (a.property.2.2.1.1.preimage continuous_subtype_val)
  obtain ⟨W, hW, hPow⟩ := exists_nhds_one_of_isLocallyEuclidean (locallyEuclidean_of_elementaryPresentation e)
  let q := QuotientGroup.mk' ((OrderDual.ofDual a.val.2).comap a.val.1.subtype)
  have hq : Continuous q := QuotientGroup.continuous_mk
  have hpre : q ⁻¹' W ∈ 𝓝 (1 : a.val.1) :=
    hq.continuousAt.preimage_mem_nhds (by simpa only [map_one] using hW)
  rw [nhds_subtype_eq_comap] at hpre
  obtain ⟨V, hV, hsub⟩ := mem_comap.mp hpre
  obtain ⟨B, hB⟩ := NonarchimedeanAddGroup.is_nonarchimedean (Multiplicative.ofAdd ⁻¹' V)
    (continuous_ofAdd.continuousAt.preimage_mem_nhds hV)
  let H := OpenSubgroup.comap a.val.1.subtype continuous_subtype_val
    (⟨B.toAddSubgroup.toSubgroup, B.isOpen⟩ : OpenSubgroup (Multiplicative L))
  have hIm : q '' (H : Set a.val.1) = {1} := by
    refine eq_singleton_iff_unique_mem.mpr ⟨⟨1, H.one_mem, map_one _⟩, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    apply hPow
    intro n
    rw [← map_pow]
    exact hsub (hB (H.pow_mem hx n))
  let : DiscreteTopology a.quotient := discreteTopology_iff_isOpen_singleton_one.mpr
    (hIm ▸ QuotientGroup.isOpenMap_coe _ H.isOpen)
  let : Finite a.quotient := finite_of_compact_of_discrete
  let : Finite (ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor) :=
    Finite.of_equiv a.quotient e.equiv.toEquiv
  change FiniteDimensional ℂ (elementarySchwartzSubmodule _ _ _ _)
  infer_instance

/-- A countable union of images of finite-dimensional stages has countable rank. -/
private theorem rank_le_aleph0_of_finite_stages {E : Type*} [AddCommGroup E] [Module ℂ E]
    {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Module ℂ (X n)]
    [∀ n, FiniteDimensional ℂ (X n)] (i : ∀ n, X n →ₗ[ℂ] E)
    (hcov : ∀ x, ∃ n, x ∈ range (i n)) : Module.rank ℂ E ≤ ℵ₀ := by
  let b (n : ℕ) := Module.finBasis ℂ (X n)
  let s : Set E := ⋃ n, range (i n ∘ b n)
  have hs : s.Countable := countable_iUnion fun n ↦ countable_range _
  have htop : Submodule.span ℂ s = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨n, y, rfl⟩ := hcov x
    have hle : ⊤ ≤ (Submodule.span ℂ s).comap (i n) := by
      rw [← (b n).span_eq]
      apply Submodule.span_le.mpr
      rintro _ ⟨k, rfl⟩
      exact Submodule.subset_span (mem_iUnion.mpr ⟨n, k, rfl⟩)
    exact hle (Submodule.mem_top (x := y))
  rw [← rank_top ℂ E, ← htop]
  exact (rank_span_le s).trans (Cardinal.mk_le_aleph0_iff.mpr hs.to_subtype)

/-- Paper: Remark C.1.3.3, p. 660. The Schwartz–Bruhat space of a nonarchimedean
local field has countably infinite complex dimension. -/
theorem schwartzBruhat_localField_rank :
    Module.rank ℂ (SchwartzBruhat (Multiplicative L)) = ℵ₀ := by
  let : ProperSpace L := ProperSpace.of_locallyCompactSpace L
  let : SecondCountableTopology (Multiplicative L) := inferInstanceAs (SecondCountableTopology L)
  let E := SchwartzBruhat (Multiplicative L)
  apply le_antisymm
  · have hs := schwartzBruhat_exists_cofinal_system (G := Multiplicative L)
    refine hs.elim fun a ha ↦ ha.elim fun e he ↦ he.elim fun j hj ↦ ?_
    let : ∀ n, FiniteDimensional ℂ (SchwartzBruhatStage (e n)) :=
      fun n ↦ localField_stage_finiteDimensional L (a n) (e n)
    exact rank_le_aleph0_of_finite_stages (fun n ↦ (schwartzBruhatStageCLM (a n) (e n)).toLinearMap)
      hj.2.2.2.2.exhaustive
  · by_contra! h
    let : FiniteDimensional ℂ E := Module.rank_lt_aleph0_iff.mp h
    let : T2Space E := schwartzBruhat_t2
    let b := (Module.finBasis ℂ E).equivFun.toContinuousLinearEquiv
    exact schwartzBruhat_localField_not_metrizable L b.toHomeomorph.isEmbedding.metrizableSpace

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]

/-- Paper: Example C.1.4.6(3), p. 662. The complete Schwartz–Bruhat space of a
second-countable LCA group is quasi-complete. The example's other properties
are `schwartzBruhat_complete`, `schwartzBruhat_nuclear`, `schwartzBruhat_montel`
and `schwartzBruhat_reflexive` from Theorem D.1.5.7. -/
theorem schwartzBruhat_quasiComplete :
    QuasiCompleteSpace ℂ (SchwartzBruhat G) := by
  let : CompleteSpace (SchwartzBruhat G) := schwartzBruhat_complete
  infer_instance

end DeferredFromC1

end RiemannMasullo
