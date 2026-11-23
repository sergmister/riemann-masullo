module

public import RiemannMasullo.AppD_SchwartzBruhat.Sec1c
import RiemannMasullo.ForMathlib.Topology.Algebra.PontryaginDual.Real

/-! # Appendix D.1.6: the printed local compactness claim for the dual hom group -/

@[expose] public noncomputable section

namespace RiemannMasullo

universe u

/-- Paper: Lemma D.1.6.4, p. 766. As printed: for every Hausdorff locally compact
abelian G, the group of continuous homomorphisms from its Pontryagin dual to the
dual of ℝ is locally compact in the compact-open topology. This is the local
compactness clause. The canonical isomorphism is `lcaTopologicalLie_dual`.
See ERRATA F231. -/
def Printed.lcaTopologicalLie_dual_locallyCompact : Prop :=
  ∀ (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G],
    LocallyCompactSpace (PontryaginDual G →ₜ* PontryaginDual (Multiplicative ℝ))

open Filter Topology Set in
/-- Helper for `Printed.lcaTopologicalLie_dual_locallyCompact_false`: the one-parameter
subgroups of the countable product of circles do not form a locally compact space. A compact
neighbourhood of `1` would contain every one-parameter subgroup supported on a far coordinate,
and projecting to that coordinate would make the dual of `ℝ` compact. -/
private theorem lcaTopologicalLie_dual_locallyCompact_false_aux
    (hlc : LocallyCompactSpace (Multiplicative ℝ →ₜ* ULift.{u} (ℕ → Circle))) : False := by
  obtain ⟨C, hCc, hC1⟩ :=
    exists_compact_mem_nhds (1 : Multiplicative ℝ →ₜ* ULift.{u} (ℕ → Circle))
  let ι : ℕ → (Circle →ₜ* ULift.{u} (ℕ → Circle)) := fun N ↦
    { toMonoidHom := (MulEquiv.ulift.symm.toMonoidHom).comp
        (MonoidHom.mulSingle (fun _ : ℕ ↦ Circle) N)
      continuous_toFun := by
        change Continuous fun x : Circle ↦ ULift.up.{u} (Pi.mulSingle N x : ℕ → Circle)
        exact continuous_uliftUp.comp (continuous_mulSingle (A := fun _ : ℕ ↦ Circle) N) }
  let π : ℕ → (ULift.{u} (ℕ → Circle) →ₜ* Circle) := fun N ↦
    { toMonoidHom := (Pi.evalMonoidHom (fun _ : ℕ ↦ Circle) N).comp MulEquiv.ulift.toMonoidHom
      continuous_toFun := by
        change Continuous fun x : ULift.{u} (ℕ → Circle) ↦ x.down N
        exact (continuous_apply N).comp continuous_uliftDown }
  have hπι : ∀ N (χ : Multiplicative ℝ →ₜ* Circle), (π N).comp ((ι N).comp χ) = χ := by
    intro N χ
    ext t
    exact congrArg Subtype.val (Pi.mulSingle_eq_same (M := fun _ : ℕ ↦ Circle) N (χ t))
  have ht : Tendsto (fun p : ℕ × (Multiplicative ℝ →ₜ* Circle) ↦ (ι p.1).comp p.2)
      (atTop ×ˢ ⊤) (𝓝 1) := by
    rw [(ContinuousMonoidHom.isInducing_toContinuousMap _ _).tendsto_nhds_iff,
      ContinuousMap.tendsto_nhds_compactOpen]
    intro K _ U hU hmaps
    rcases K.eq_empty_or_nonempty with rfl | ⟨t₀, ht₀⟩
    · exact Eventually.of_forall fun _ ↦ mapsTo_empty _ _
    have h1U : (1 : ULift.{u} (ℕ → Circle)) ∈ U := hmaps ht₀
    have hU' : ULift.up ⁻¹' U ∈ 𝓝 (1 : ℕ → Circle) :=
      continuous_uliftUp.continuousAt.preimage_mem_nhds (hU.mem_nhds h1U)
    rw [nhds_pi, Filter.mem_pi'] at hU'
    obtain ⟨I, s, hs, hsub⟩ := hU'
    refine ((eventually_gt_atTop (I.sup id)).prod_inl ⊤).mono fun p hp t _ ↦ ?_
    refine hsub fun n hn ↦ ?_
    have hne : n ≠ p.1 := fun h ↦ (lt_irrefl _ (lt_of_le_of_lt (I.le_sup (f := id) hn)
      (h ▸ hp)))
    change (Pi.mulSingle p.1 (p.2 t) : ℕ → Circle) n ∈ s n
    rw [Pi.mulSingle_eq_of_ne hne]
    exact mem_of_mem_nhds (hs n)
  have hev := ht hC1
  rw [Filter.mem_map, Filter.mem_prod_top] at hev
  obtain ⟨N, hN⟩ := (Filter.eventually_atTop.mp hev)
  have hcomp : IsCompact ((fun g ↦ (π N).comp g) '' C) :=
    hCc.image (π N).continuous_comp_right
  have huniv : IsCompact (univ : Set (Multiplicative ℝ →ₜ* Circle)) :=
    hcomp.of_isClosed_subset isClosed_univ fun χ _ ↦ ⟨_, hN N le_rfl χ, hπι N χ⟩
  obtain ⟨e, -⟩ := exists_realPontryaginDualEquiv
  have : CompactSpace (PontryaginDual (Multiplicative ℝ)) := ⟨huniv⟩
  have : CompactSpace (Multiplicative ℝ) := e.symm.toHomeomorph.compactSpace
  have hR' : IsCompact (univ : Set ℝ) := by
    have := (isCompact_univ (X := Multiplicative ℝ)).image (continuous_toAdd (X := ℝ))
    rwa [image_univ_of_surjective Multiplicative.toAdd.surjective] at this
  exact noncompact_univ ℝ hR'

/-- Paper: Lemma D.1.6.4, p. 766. Take G to be the countable product of circles.
Its dual is the discrete direct sum of countably many copies of ℤ. The hom group
from that direct sum to the dual of ℝ is ℝ^ℕ in the product topology, since compact
sets in the discrete direct sum are finite. Every neighborhood of zero contains a
basic neighborhood with an unrestricted coordinate, so it cannot be compact. -/
theorem Printed.lcaTopologicalLie_dual_locallyCompact_false :
    ¬ Printed.lcaTopologicalLie_dual_locallyCompact := by
  intro h
  have hG := h (ULift (ℕ → Circle))
  obtain ⟨e, -⟩ := lcaTopologicalLie_dual (G := ULift (ℕ → Circle))
  exact lcaTopologicalLie_dual_locallyCompact_false_aux
    (e.symm.toHomeomorph.locallyCompactSpace_iff.mp hG)

end RiemannMasullo
