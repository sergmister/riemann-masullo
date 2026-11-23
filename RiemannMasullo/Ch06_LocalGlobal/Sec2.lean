module

public import RiemannMasullo.Ch06_LocalGlobal.Sec1
public import RiemannMasullo.Ch05_ThetaZSpaces.Sec3a
public import RiemannMasullo.AppD_SchwartzBruhat.Sec3a
import all RiemannMasullo.Ch02_AdelicTheta.Sec1
import all RiemannMasullo.Ch04_PeriodicSchauderBases.Sec3b
import all RiemannMasullo.AppC_LCTVS.Sec2b
import RiemannMasullo.ForMathlib.Analysis.Fourier.CompactGroup
import Mathlib.LinearAlgebra.Eigenspace.Basic

import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Topology.Algebra.IsOpenUnits

import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace

/-! # Structure Theorem V: isotypic exhaustiveness

Masullo, §6.2, pp. 295–302. Finite sets of places index only the finite factors.
Every S-adelic space includes all archimedean places.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Topology
open scoped DirectSum NNReal NumberField.AdeleRing TensorProduct

namespace RiemannMasullo

set_option quotPrecheck false

variable {F : Type*} [Field F] [NumberField F]
variable {S T : Finset (HeightOneSpectrum (𝓞 F))}

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "Iₛ(" S ")" => (SAdeleRing F S)ˣ
local notation "Nₛ(" S ")" => (sIdeleNorm F S).ker
local notation "Jₛ(" S ")" => SIdeleQuotient F S
local notation "J₁(" S ")" => (sIdeleQuotientNorm F S).ker
local notation "C₁" => (ideleClassNorm F).ker
local notation "Picₛ(" S ")" => CommRing.Pic ((S : Set V).integer F)
local notation "ℬ(" R ")" => SchwartzBruhat (Multiplicative R)
local notation "ℬₛ(" S ")" => ℬ(SAdeleRing F S)
local notation "ℬ∞" => ℬ(InfiniteAdeleRing F)
local notation "Θₛ(" S ")" => SLocalAdelicThetaSpace F S
local notation "Θ𝔽" => GlobalAdelicThetaSpace F
local notation "Θₛω(" S ", " χ ")" => SLocalHomogeneousThetaSpace F S χ
local notation "Θ𝔽ω(" ω ")" => GlobalHomogeneousThetaSpace F ω
local notation "Kₛω(" S ", " χ ")" => LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap F S χ)
local notation "ρₛ(" S ")" => (existsUnique_sLocalThetaAction (F := F) (S := S)).exists.choose
local notation "ρ𝔽" => (existsUnique_globalThetaAction (F := F)).exists.choose

section Exhaustiveness

/-- Paper: (6.2.1.1), p. 297.
The norm-one quotient at T maps openly onto the norm-one quotient at S when the
S-integer Picard group is trivial. Its kernel is the image of the integral units at
the additional places, and the map reverses insertion on representatives at S. -/
theorem existsUnique_sLocalNormOneQuotientTransition (hST : S ⊂ T)
    (_hPic : Subsingleton Picₛ(S)) :
    ∃! q : J₁(T) →ₜ* J₁(S), Surjective q ∧ IsOpenMap q ∧
      (∀ x : J₁(T), q x = 1 ↔
        ∃ u : relativeIntegralIdeleUnits F S T, x.val = QuotientGroup.mk u.val) ∧
      ∀ (g : Nₛ(S)) (x : J₁(T)) (y : J₁(S)),
        x.val = QuotientGroup.mk (Units.map (adeleProjection F T).toMonoidHom
          (sIdeleInsertion F S g.val)) →
        y.val = QuotientGroup.mk g.val → q x = y := by sorry

/-- Paper: Theorem 6.2.1.1(1), p. 295.
For a T-local character trivial on the additional integer units, adjoining integer
indicators gives a surjective topological linear isomorphism on homogeneous classes.
The source character is the unique descent of the target character. -/
theorem sLocalHomogeneousThetaTransition_equiv_of_unramified
    (hST : S ⊂ T) (hPic : Subsingleton Picₛ(S)) (χ : PontryaginDual J₁(T))
    (_hχ : ∀ (x : J₁(T)) (u : relativeIntegralIdeleUnits F S T),
      x.val = QuotientGroup.mk u.val → χ x = 1) :
    let q := (existsUnique_sLocalNormOneQuotientTransition hST hPic).exists.choose
    ∃ (χS : PontryaginDual J₁(S)) (e : Θₛω(S, χS) ≃L[ℂ] Θₛω(T, χ)),
      (∀ x, χS (q x) = χ x) ∧
      ∀ f : ℬₛ(S), e ((Kₛω(S, χS)).mkQ f) =
        (Kₛω(T, χ)).mkQ (sAdeleSchwartzTransition F hST.le f) := by sorry

/-- The descended character at a larger stage kills the additional integral units:
use the same global lift to evaluate the descent identity at both stages. -/
private theorem sLocalHomogeneousThetaToGlobal_equiv_of_unramified_units
    (hST : S ⊆ T) {ω : PontryaginDual C₁} (hω : NormOneCharacterUnramifiedOutside ω S)
    (x : J₁(T)) (u : relativeIntegralIdeleUnits F S T) (hx : x.val = QuotientGroup.mk u.val) :
    sLocalNormOneCharacter T ω (hω.mono hST) x = 1 := by
  obtain ⟨g, hg, hgu⟩ := u.property
  obtain ⟨a, ha⟩ := hg.1
  have hp : Units.map (adeleProjection F S).toMonoidHom g = 1 := hg.2
  have hn : ideleNorm F g = 1 := by
    have h := (sIdeleNorm_spec F S).1 a
    change ideleNorm F (integralIdeleInsertion F S a) =
      sIdeleNorm F S (Units.map (adeleProjection F S).toMonoidHom (integralIdeleInsertion F S a)) at h
    rwa [ha, hp, map_one] at h
  let z : C₁ := ⟨QuotientGroup.mk g, hn⟩
  have hz := sLocalNormOneCharacter_apply ω hω a z 1 (congrArg QuotientGroup.mk ha.symm)
    (by rw [ha, hp]; rfl)
  have hb : g ∈ Set.range (integralIdeleInsertion F T) :=
    (mem_range_integralIdeleInsertion F T g).mpr (fun v hv ↦
      (mem_range_integralIdeleInsertion F S g).mp ⟨a, ha⟩ v (fun hs ↦ hv (hST hs)))
  obtain ⟨b, hb⟩ := hb
  exact (sLocalNormOneCharacter_apply ω (hω.mono hST) b z x (congrArg QuotientGroup.mk hb.symm)
    (by rw [hb, hgu]; exact hx)).trans (hz.symm.trans (map_one _))

/-- Surjectivity on homogeneous classes can be checked on test representatives, so no
identification of the two descriptions of the descended source character is needed. -/
private theorem sLocalHomogeneousThetaToGlobal_equiv_of_unramified_stage
    (hST : S ⊂ T) (hPic : Subsingleton Picₛ(S)) {ω : PontryaginDual C₁}
    (hω : NormOneCharacterUnramifiedOutside ω S) :
    Surjective (sLocalHomogeneousThetaTransition (ω := ω) hω hST.le) := by
  let χT := sLocalNormOneCharacter T ω (hω.mono hST.le)
  have hex := sLocalHomogeneousThetaTransition_equiv_of_unramified hST hPic χT
    (sLocalHomogeneousThetaToGlobal_equiv_of_unramified_units hST.le hω)
  with_reducible refine hex.elim fun χS hS ↦ ?_
  with_reducible refine hS.elim fun e he ↦ ?_
  intro y
  have hrep := (Kₛω(S, χS)).mkQ_surjective (e.symm y)
  with_reducible refine hrep.elim fun f hf ↦ ?_
  refine ⟨(Kₛω(S, sLocalNormOneCharacter S ω hω)).mkQ f, ?_⟩
  change (Kₛω(T, χT)).mkQ (sAdeleSchwartzTransition F hST.le f) = y
  with_reducible exact (he.2 f).symm.trans ((congrArg e hf).trans (e.apply_symm_apply y))

/-- A stage in an exhaustive family of closed embeddings exhausts the limit if its
transition to every strictly larger stage is surjective. -/
private theorem sLocalHomogeneousThetaToGlobal_equiv_of_unramified_of_limit
    {ι : Type*} [PartialOrder ι] {P : ι → Prop} (s : ι) (p : P s)
    (m : ∀ {t u}, P t → t ≤ u → P u) (X : (t : ι) → P t → Type*)
    [∀ t h, AddCommGroup (X t h)] [∀ t h, Module ℂ (X t h)] [∀ t h, TopologicalSpace (X t h)]
    {Y : Type*} [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    (i : ∀ t (q : P t), X t q →ₗ[ℂ] Y)
    (j : ∀ t u (q : P t) (h : t ≤ u), X t q →ₗ[ℂ] X u (m q h))
    (hs : ∀ t (h : s < t), Surjective (j s t p h.le))
    (hc : let I := {t : ι // s ≤ t}
      let q := fun t : I ↦ m p t.property
      let f := fun t : I ↦ i t.val (q t)
      (∀ t, IsClosedEmbedding (f t)) ∧
      (∀ (t u : I) (htu : t.val ≤ u.val), (f u).comp (j t u (q t) htu) = f t) ∧
      (∀ y, ∃ t x, f t x = y)) :
    ∃ e : X s p ≃L[ℂ] Y, e.toLinearMap = i s p := by
  have he := hc.1 ⟨s, le_rfl⟩
  have hi : Surjective (i s p) := by
    intro y
    obtain ⟨⟨t, ht⟩, x, rfl⟩ := hc.2.2 y
    rcases eq_or_lt_of_le ht with rfl | hlt
    · exact ⟨x, rfl⟩
    obtain ⟨z, rfl⟩ := hs t hlt x
    exact ⟨z, (LinearMap.congr_fun (hc.2.1 ⟨s, le_rfl⟩ ⟨t, ht⟩ ht) z).symm⟩
  let e := LinearEquiv.ofBijective (i s p) ⟨he.injective, hi⟩
  exact ⟨⟨e, he.continuous, (e.toEquiv.toHomeomorphOfIsInducing he.isInducing).symm.continuous⟩, rfl⟩

/-- Paper: Theorem 6.2.1.1(2), p. 295.
If the S-integer Picard group is trivial and the global character is unramified
outside S, the existing homogeneous insertion is a topological linear isomorphism. -/
theorem sLocalHomogeneousThetaToGlobal_equiv_of_unramified
    (_hPic : Subsingleton Picₛ(S)) {ω : PontryaginDual C₁}
    (hω : NormOneCharacterUnramifiedOutside ω S) :
    ∃ e : Θₛω(S, sLocalNormOneCharacter S ω hω) ≃L[ℂ] Θ𝔽ω(ω),
      e.toLinearMap = sLocalHomogeneousThetaToGlobal hω := by
  let X (T : Finset V) (q : NormOneCharacterUnramifiedOutside ω T) :=
    Θₛω(T, sLocalNormOneCharacter T ω q)
  have h := sLocalHomogeneousTheta_inductiveLimit (F := F) (S := S) (ω := ω) hω
  with_reducible
    exact sLocalHomogeneousThetaToGlobal_equiv_of_unramified_of_limit (Y := Θ𝔽ω(ω)) S hω
      (fun q h ↦ NormOneCharacterUnramifiedOutside.mono q h) X
      (fun T ↦ sLocalHomogeneousThetaToGlobal (F := F) (S := T) (ω := ω))
      (fun T U ↦ sLocalHomogeneousThetaTransition (F := F) (S := T) (T := U) (ω := ω))
      (fun t hst ↦ sLocalHomogeneousThetaToGlobal_equiv_of_unramified_stage
        (F := F) (S := S) (T := t) (ω := ω) hst _hPic hω) ⟨h.1, h.2.1, h.2.2.1⟩

/-- Paper: Corollary 6.2.1.2, p. 295.
Each global homogeneous theta quotient is a nuclear Fréchet space. -/
theorem globalHomogeneousThetaSpace_nuclearFrechet (ω : PontryaginDual C₁) :
    IsFrechetTVS Θ𝔽ω(ω) ∧ IsNuclearTVS Θ𝔽ω(ω) := by sorry

-- TODO(paper-gap): The proof of Lemma 6.2.1.3 repeats the componentwise-seminorm
-- error in ERRATA I125. Joint continuity of the action and compactness apply.

/-- Paper: Lemma 6.2.1.3(1), p. 296.
Convergence of a net of local theta classes implies uniform convergence of its orbit
maps over the compact norm-one quotient. -/
theorem sLocalThetaAction_tendstoUniformly {ι : Type*} (l : Filter ι)
    (f : ι → Θₛ(S)) (x : Θₛ(S)) (hf : Tendsto f l (𝓝 x)) :
    ∀ U ∈ 𝓝 (0 : Θₛ(S)), ∀ᶠ i in l, ∀ g : J₁(S),
      ρₛ(S) g.val (f i) - ρₛ(S) g.val x ∈ U := by
  have uniform {G X : Type _} [TopologicalSpace G] [AddCommGroup X] [TopologicalSpace X]
      [IsTopologicalAddGroup X] {K : Set G} (hK : IsCompact K)
      (A : G → X → X) (hA : Continuous (fun p : G × X ↦ A p.1 p.2))
      (u : ι → X) (v : X) (hu : Tendsto u l (𝓝 v)) (U : Set X) (hU : U ∈ 𝓝 0) :
      ∀ᶠ i in l, ∀ g ∈ K, A g (u i) - A g v ∈ U := by
    have hd : Continuous (fun p : X × G ↦ A p.2 p.1 - A p.2 v) :=
      (hA.comp (continuous_snd.prodMk continuous_fst)).sub
        (hA.comp (continuous_snd.prodMk continuous_const))
    exact hu.eventually (hK.eventually_forall_of_forall_eventually (P := fun y g ↦ A g y - A g v ∈ U)
      fun g _ ↦
        hd.continuousAt (x := (v, g)) (by simpa only [sub_self] using hU))
  let : PolynormableSpace ℂ (Θₛ(S)) := sLocalAdelicThetaSpace_polynormable
  let : IsTopologicalAddGroup (Θₛ(S)) := PolynormableSpace.isTopologicalAddGroup ℂ _
  have hc := (isProperMap_sIdeleQuotientNorm F S).isCompact_preimage
    (isCompact_singleton (x := (1 : ℝ≥0ˣ)))
  have hA := (existsUnique_sLocalThetaAction (F := F) (S := S)).exists.choose_spec.1
  intro U hU
  have h := uniform (G := Jₛ(S)) (X := Θₛ(S)) hc (fun g y ↦ ρₛ(S) g y) hA f x hf U hU
  exact h.mono fun i hi g ↦ hi g.val g.property

/-- Multiplication by scalars of norm at most one keeps uniform convergence of differences. -/
private theorem smul_sub_eventually_mem_of_norm_le_one {E ι κ : Type*} [AddCommGroup E]
    [Module ℂ E] [TopologicalSpace E] [ContinuousSMul ℂ E] (l : Filter ι) (u : ι → κ → E)
    (w : κ → E) (c : κ → ℂ) (hc : ∀ k, ‖c k‖ ≤ 1)
    (h : ∀ U ∈ 𝓝 (0 : E), ∀ᶠ i in l, ∀ k, u i k - w k ∈ U) :
    ∀ U ∈ 𝓝 (0 : E), ∀ᶠ i in l, ∀ k, c k • u i k - c k • w k ∈ U := by
  intro U hU
  obtain ⟨W, ⟨hW, hWb⟩, hWU⟩ := (nhds_basis_balanced ℂ E).mem_iff.mp hU
  filter_upwards [h W hW] with i hi k
  rw [← smul_sub]
  exact hWU (hWb.smul_mem (hc k) (hi k))

/-- Paper: Lemma 6.2.1.3(2), p. 296.
Uniform convergence over the norm-one quotient also holds after twisting the action
by a unitary character. -/
theorem sLocalThetaAction_twist_tendstoUniformly {ι : Type*} (l : Filter ι)
    (f : ι → Θₛ(S)) (x : Θₛ(S)) (hf : Tendsto f l (𝓝 x)) (χ : PontryaginDual J₁(S)) :
    ∀ U ∈ 𝓝 (0 : Θₛ(S)), ∀ᶠ i in l, ∀ g : J₁(S),
      (χ g : ℂ) • ρₛ(S) g.val (f i) - (χ g : ℂ) • ρₛ(S) g.val x ∈ U :=
  smul_sub_eventually_mem_of_norm_le_one l _ _ (fun g ↦ (χ g : ℂ))
    (fun g ↦ (Circle.norm_coe (χ g)).le) (sLocalThetaAction_tendstoUniformly l f x hf)

end Exhaustiveness

section IsotypicSums

local notation "ρₛ₁(" S ")" => (ρₛ(S)).comp (MonoidHom.ker (sIdeleQuotientNorm F S)).subtype
local notation "ρ𝔽₁" => (ρ𝔽).comp (MonoidHom.ker (ideleClassNorm F)).subtype
local notation "Eₛ(" χ ")" => actionIsotype (ρₛ₁(S)) χ
local notation "E𝔽(" ω ")" => actionIsotype ρ𝔽₁ ω

-- TODO(paper-gap): In Remark 6.2.1.4(1)–(2), neither local topology comparison is
-- strict for F = ℚ and the archimedean stage. Its norm-one quotient is trivial,
-- so both comparisons reduce to the topology on the sole isotype.
-- The global comparison can also be equality over ℚ: each finite test stage
-- factors through a finite quotient of the norm-one unit action.
-- The proof of strictness also assumes infinitely many everywhere unramified
-- characters, which fails over ℚ.

/-- A separating functional for the closed sum would give a nonzero continuous
matrix coefficient on the compact group with all Fourier coefficients zero. -/
private theorem sLocalThetaIsotypeSum_dense_aux {H E : Type*} [CommGroup H]
    [TopologicalSpace H] [IsTopologicalGroup H] (N : Subgroup H) [T2Space N] [CompactSpace N]
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [PolynormableSpace ℂ E] [T2Space E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    (hc : @CompleteSpace E (IsTopologicalAddGroup.rightUniformSpace E))
    (σ : H →* (E →L[ℂ] E)) (hσ : Continuous fun p : H × E ↦ σ p.1 p.2) :
    let X := fun χ : PontryaginDual N ↦ ↥(actionIsotype (σ.comp N.subtype) χ)
    letI := Classical.decEq (PontryaginDual N)
    letI := locallyConvexFinalTopology (DirectSum.lof ℂ _ X)
    let i := DirectSum.toModule ℂ _ E (fun χ ↦ (actionIsotype (σ.comp N.subtype) χ).subtype)
    Continuous i ∧ Injective i ∧ DenseRange i := by
  classical
  let ρ := σ.comp N.subtype
  have hρ : Continuous fun p : N × E ↦ ρ p.1 p.2 :=
    hσ.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  let X := actionIsotype ρ
  let := locallyConvexFinalTopology (DirectSum.lof ℂ _ (fun χ ↦ ↥(X χ)))
  change Continuous (DirectSum.coeLinearMap X) ∧ Injective _ ∧ DenseRange _
  refine ⟨?_, ?_, ?_⟩
  · apply continuous_of_locallyConvexFinalTopology (DirectSum.lof ℂ _ (fun χ ↦ ↥(X χ)))
    intro χ
    simpa only [Function.comp_def, DirectSum.coeLinearMap_lof] using
      (continuous_subtype_val : Continuous (fun x : X χ ↦ (x : E)))
  · let f (g : N) : Module.End ℂ E := (ρ g).toLinearMap
    let v (χ : PontryaginDual N) (g : N) : ℂ := χ g
    have hv : Injective v := fun χ ψ h ↦ DFunLike.ext _ _ fun g ↦ Subtype.ext (congrFun h g)
    have hi := iSupIndep.iInf (fun g ↦ (f g).eigenspace) (fun g ↦ (f g).eigenspaces_iSupIndep)
    apply iSupIndep.dfinsupp_lsum_injective (p := X)
    refine (hi.comp hv).mono fun χ x hx ↦ (Submodule.mem_iInf _).mpr fun g ↦ ?_
    exact Module.End.mem_eigenspace_iff.mpr ((mem_actionIsotype ρ χ x).mp hx g)
  · let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
    let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
    let : CompleteSpace E := hc
    let : Module ℝ E := Module.restrictScalars ℝ ℂ E
    let : IsScalarTower ℝ ℂ E := IsScalarTower.restrictScalars ℝ ℂ E
    let : LocallyConvexSpace ℝ E := (PolynormableSpace.withSeminorms ℂ E).toLocallyConvexSpace
    let : SeparatingDual ℂ E := locallyConvexSpace_separatingDual ℂ E
    let : MeasurableSpace N := borel N
    let : BorelSpace N := ⟨rfl⟩
    let μ : Measure N := Measure.haar
    intro x
    let D := (LinearMap.range (DirectSum.coeLinearMap X)).topologicalClosure
    change x ∈ D
    by_contra hn
    obtain ⟨φ, hne, hz⟩ := exists_dual_eq_zero_on_submodule_of_notMem D
      (Submodule.isClosed_topologicalClosure _) hn
    let u : N → ℂ := fun g ↦ φ (ρ g x)
    have hu : Continuous u := φ.continuous.comp (hρ.comp (continuous_id.prodMk continuous_const))
    have hcoeff (χ : PontryaginDual N) : ∫ g, star (χ g : ℂ) * u g ∂μ = 0 := by
      let A (g : N) := star (χ g : ℂ) • ρ g
      have hA : Continuous fun p : N × E ↦ A p.1 p.2 :=
        (show Continuous (fun p : N × E ↦ star (χ p.1 : ℂ)) from by fun_prop).smul hρ
      obtain ⟨P, hP, _⟩ := existsUnique_pettisIntegral_continuousFamily μ isCompact_univ
        (ae_of_all _ fun _ ↦ Set.mem_univ _) A hA
      have hav : IsPettisIsotypicAverageOn μ Set.univ ρ χ P := by
        simpa [IsPettisIsotypicAverageOn, A] using hP
      rw [← compactActionAverage_dual_apply μ ρ χ P hav x φ]
      apply hz _ (Submodule.le_topologicalClosure _ ?_)
      rw [DirectSum.range_coeLinearMap]
      exact le_iSup X χ (compactActionAverage_mem_isotype μ ρ χ P hav x)
    have hae := ae_eq_zero_of_character_integral_eq_zero μ
      (hu.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) hcoeff
    have heq := Measure.eq_of_ae_eq hae hu continuous_const
    exact hne (by simpa [u] using congrFun heq 1)

/-- Paper: Remark 6.2.1.4(1), pp. 297–298.
The direct sum of the S-local isotypes maps continuously and injectively to the
theta quotient with dense range.
Deviation: The topology of the direct sum is the locally convex final topology.
The strict comparison in the remark fails in general. -/
theorem sLocalThetaIsotypeSum_dense :
    let X := fun χ : PontryaginDual J₁(S) ↦ ↥(Eₛ(χ))
    letI := Classical.decEq (PontryaginDual J₁(S))
    letI := locallyConvexFinalTopology (DirectSum.lof ℂ _ X)
    let i := DirectSum.toModule ℂ _ Θₛ(S) (fun χ ↦ (Eₛ(χ)).subtype)
    Continuous i ∧ Injective i ∧ DenseRange i := by
  have hclosed := isClosed_sProjectedDiagonal (F := F) (S := S)
  let : T2Space (Jₛ(S)) := inferInstanceAs (T2Space (_ ⧸ _))
  let : T2Space (J₁(S)) := inferInstanceAs (T2Space ((sIdeleQuotientNorm F S).ker : Set (Jₛ(S))))
  let : CompactSpace (J₁(S)) := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage (isCompact_singleton (x := 1)))
  let : T2Space (Θₛ(S)) := sLocalAdelicThetaSpace_t2_of_isClosed
    (sLocalAdelicTheta_ker_isClosed (F := F) (S := S))
  let : PolynormableSpace ℂ (Θₛ(S)) := sLocalAdelicThetaSpace_polynormable
  let : IsTopologicalAddGroup (Θₛ(S)) := PolynormableSpace.isTopologicalAddGroup ℂ _
  let : ContinuousSMul ℂ (Θₛ(S)) := PolynormableSpace.continuousSMul ℂ _
  with_reducible_and_instances
    exact sLocalThetaIsotypeSum_dense_aux (H := Jₛ(S)) (E := Θₛ(S)) (sIdeleQuotientNorm F S).ker
      (sLocalAdelicThetaSpace_complete (F := F) (S := S)) ρₛ(S)
      (existsUnique_sLocalThetaAction (F := F) (S := S)).exists.choose_spec.1

/-- Paper: Remark 6.2.1.4(1), pp. 297–298.
The direct sum of the global isotypes maps continuously and injectively to the
global theta quotient with dense range.
Deviation: The topology of the direct sum is the locally convex final topology.
The strict comparison is omitted. -/
theorem globalThetaIsotypeSum_dense :
    let X := fun ω : PontryaginDual C₁ ↦ ↥(E𝔽(ω))
    letI := Classical.decEq (PontryaginDual C₁)
    letI := locallyConvexFinalTopology (DirectSum.lof ℂ _ X)
    let i := DirectSum.toModule ℂ _ Θ𝔽 (fun ω ↦ (E𝔽(ω)).subtype)
    Continuous i ∧ Injective i ∧ DenseRange i := by sorry

/-- Paper: Remark 6.2.1.4(1), p. 297.
The locally convex direct sum of the S-local isotypes is Hausdorff and complete. -/
theorem sLocalThetaIsotypeSum_complete :
    let X := fun χ : PontryaginDual J₁(S) ↦ ↥(Eₛ(χ))
    letI := Classical.decEq (PontryaginDual J₁(S))
    let D := ⨁ χ, X χ
    letI := locallyConvexFinalTopology (DirectSum.lof ℂ _ X)
    T2Space D ∧ PolynormableSpace ℂ D ∧
      ∀ (u : UniformSpace D), u.toTopologicalSpace = (inferInstance : TopologicalSpace D) →
        @IsUniformAddGroup D u _ → @CompleteSpace D u := by sorry

/-- The generating seminorms for the final locally convex topology are tested on each stage. -/
private theorem globalThetaIsotypeSum_finalTopology_withSeminorms {K Z : Type*} {Y : K → Type*}
    [AddCommGroup Z] [Module ℂ Z] [∀ k, AddCommGroup (Y k)] [∀ k, Module ℂ (Y k)]
    [∀ k, TopologicalSpace (Y k)] (j : ∀ k, Y k →ₗ[ℂ] Z) :
    letI := locallyConvexFinalTopology j
    WithSeminorms (E := Z) (Subtype.val : {p : Seminorm ℂ Z // ∀ k, Continuous (p ∘ j k)} → _) := by
  let := locallyConvexFinalTopology j
  exact ⟨rfl⟩

/-- Each stage map into the final locally convex topology is continuous. -/
private theorem globalThetaIsotypeSum_continuous_finalTopology_stage {K Z : Type*} {Y : K → Type*}
    [AddCommGroup Z] [Module ℂ Z] [∀ k, AddCommGroup (Y k)] [∀ k, Module ℂ (Y k)]
    [∀ k, TopologicalSpace (Y k)] [∀ k, IsTopologicalAddGroup (Y k)]
    (j : ∀ k, Y k →ₗ[ℂ] Z) (k : K) :
    letI := locallyConvexFinalTopology j
    Continuous (j k) := by
  let := locallyConvexFinalTopology j
  exact (globalThetaIsotypeSum_finalTopology_withSeminorms j).continuous_of_continuous_comp _ fun p ↦ p.property k

/-- A linear map on a space with the final locally convex topology is continuous if all
its restrictions to the defining stages are continuous. -/
private theorem globalThetaIsotypeSum_continuous_finalTopology_lift {K Z W : Type*} {Y : K → Type*}
    [AddCommGroup Z] [Module ℂ Z] [∀ i, AddCommGroup (Y i)] [∀ i, Module ℂ (Y i)]
    [∀ i, TopologicalSpace (Y i)] [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
    [PolynormableSpace ℂ W] (u : ∀ i, Y i →ₗ[ℂ] Z) (T : Z →ₗ[ℂ] W)
    (h : ∀ i, Continuous (T ∘ u i)) :
    letI := locallyConvexFinalTopology u
    Continuous T := by
  let := locallyConvexFinalTopology u
  have hs := globalThetaIsotypeSum_finalTopology_withSeminorms u
  have := hs.isTopologicalAddGroup
  exact (PolynormableSpace.withSeminorms ℂ W).continuous_of_continuous_comp T fun p ↦
    hs.continuous_seminorm ⟨p.val.comp T, fun i ↦ p.property.comp (h i)⟩

/-- Coordinate projections are continuous on the locally convex direct sum. -/
private theorem globalThetaIsotypeSum_continuous_lcDirectSum_component {K : Type*} [DecidableEq K] (Y : K → Type*)
    [∀ i, AddCommGroup (Y i)] [∀ i, Module ℂ (Y i)] [∀ i, TopologicalSpace (Y i)]
    [∀ i, PolynormableSpace ℂ (Y i)] (i : K) :
    letI := locallyConvexFinalTopology (DirectSum.lof ℂ K Y)
    Continuous (DirectSum.component ℂ K Y i) := by
  let lof := DirectSum.lof ℂ K Y
  let := locallyConvexFinalTopology lof
  apply globalThetaIsotypeSum_continuous_finalTopology_lift lof
  intro k
  change Continuous ((DirectSum.component ℂ K Y i).comp (DirectSum.lof ℂ K Y k))
  by_cases h : k = i
  · subst k
    simp only [DirectSum.component_comp_lof_same, LinearMap.id_coe, continuous_id]
  · rw [DirectSum.component_comp_lof, dite_eq_right h]
    exact continuous_const

/-- A Cauchy filter in a locally convex direct sum of complete spaces converges.
Its coordinate limits have finite support, as seen by testing a seminorm that takes
value one on each nonzero limit coordinate. -/
private theorem globalThetaIsotypeSum_completeSpace_lcDirectSum {K : Type*} [DecidableEq K] (Y : K → Type*)
    [∀ i, AddCommGroup (Y i)] [∀ i, Module ℂ (Y i)] [∀ i, UniformSpace (Y i)]
    [∀ i, IsUniformAddGroup (Y i)] [∀ i, PolynormableSpace ℂ (Y i)]
    [∀ i, T2Space (Y i)] [∀ i, CompleteSpace (Y i)] :
    letI := locallyConvexFinalTopology (DirectSum.lof ℂ K Y)
    letI := (globalThetaIsotypeSum_finalTopology_withSeminorms (DirectSum.lof ℂ K Y)).isTopologicalAddGroup
    @CompleteSpace (⨁ i, Y i) (IsTopologicalAddGroup.rightUniformSpace _) := by
  classical
  let D := ⨁ i, Y i
  let lof := DirectSum.lof ℂ K Y
  let := locallyConvexFinalTopology lof
  have hD := globalThetaIsotypeSum_finalTopology_withSeminorms lof
  have : IsTopologicalAddGroup D := hD.isTopologicalAddGroup
  let := IsTopologicalAddGroup.rightUniformSpace D
  have : IsUniformAddGroup D := isUniformAddGroup_of_addCommGroup
  have : PolynormableSpace ℂ D := hD.toPolynormableSpace
  let pr := DirectSum.component ℂ K Y
  have hpr := globalThetaIsotypeSum_continuous_lcDirectSum_component Y
  constructor
  intro l hl
  have : l.NeBot := hl.1
  obtain ⟨v, hv⟩ : ∃ v : ∀ i, Y i, ∀ i, Tendsto (pr i) l (𝓝 (v i)) := by
    choose v hv using fun i ↦ CompleteSpace.complete (hl.map
      ((pr i).toAddMonoidHom.uniformContinuous_of_continuousAt_zero (hpr i).continuousAt))
    exact ⟨v, hv⟩
  -- Finite sums of coordinate seminorms stay close to the coordinatewise limit.
  have approx (q : ∀ i, Seminorm ℂ (Y i)) (hq : ∀ i, Continuous (q i)) :
      ∀ᶠ x : D in l, ∀ s : Finset K, (∑ i ∈ s, q i (x i - v i)) ≤ 1/2 := by
    let p := directSumSeminorm q
    have hp : Continuous p := hD.continuous_seminorm ⟨p, fun i ↦ by
      change Continuous (fun a ↦ directSumSeminorm q (DirectSum.lof ℂ K Y i a))
      simpa only [directSumSeminorm_lof] using hq i⟩
    have ht := (IsUniformAddGroup.cauchy_iff_tendsto l).mp hl
    obtain ⟨S, hS, hSS⟩ := l.basis_sets.prod_self.mem_iff.mp
      (ht.2 (p.ball_mem_nhds hp (show (0 : ℝ) < 1/2 by norm_num)))
    filter_upwards [hS] with x hx
    intro s
    have htend : Tendsto (fun y : D ↦ ∑ i ∈ s, q i (x i - y i)) l
        (𝓝 (∑ i ∈ s, q i (x i - v i))) :=
      tendsto_finsetSum _ fun i _ ↦ (hq i).continuousAt.tendsto.comp ((hv i).const_sub (x i))
    apply le_of_tendsto htend
    filter_upwards [hS] with y hy
    exact (sum_le_directSumSeminorm q (x-y) s).trans (p.mem_ball_zero.mp (hSS (a := (x,y)) ⟨hx,hy⟩)).le
  have hsep (i : K) : ∃ q : Seminorm ℂ (Y i), Continuous q ∧ (v i ≠ 0 → q (v i) = 1) := by
    by_cases h : v i = 0
    · exact ⟨0, continuous_zero, fun hn ↦ (hn h).elim⟩
    have := polynormableSpace_separatingDual ℂ (Y i)
    obtain ⟨φ, hφ⟩ := SeparatingDual.exists_eq_one (R := ℂ) h
    exact ⟨(normSeminorm ℂ ℂ).comp φ.toLinearMap, φ.continuous.norm, fun _ ↦ by
      change ‖φ (v i)‖ = 1
      simp [hφ]⟩
  choose q hq hsep using hsep
  obtain ⟨a, ha⟩ := (approx q hq).exists
  let z : D := DFinsupp.mk a.support fun i ↦ v i
  have hz (i : K) : z i = v i := by
    rw [show z i = _ from DFinsupp.mk_apply]
    split_ifs with hi
    · rfl
    · by_contra h
      have := ha {i}
      have hai : a i = 0 := DFinsupp.notMem_support_iff.mp hi
      simp [hai, hsep i (Ne.symm h)] at this
      linarith
  refine ⟨z, (Filter.tendsto_sub_const_iff z).mp ?_⟩
  rw [sub_self]
  apply (PolynormableSpace.hasBasis_zero_ball ℂ D).tendsto_right_iff.mpr
  intro p hp
  let r (i : K) := p.comp (lof i)
  have hr i : Continuous (r i) := hp.comp (globalThetaIsotypeSum_continuous_finalTopology_stage lof i)
  filter_upwards [approx r hr] with x hx
  let d := x - z
  have hsum := Finset.le_sum_of_subadditive p (map_zero p).le (map_add_le_add p)
    d.support (fun i ↦ lof i (d i))
  rw [show (∑ i ∈ d.support, lof i (d i)) = d from DirectSum.sum_support_of d] at hsum
  apply p.mem_ball_zero.mpr
  refine hsum.trans_lt ((le_trans ?_ (hx d.support)).trans_lt (by norm_num))
  apply Finset.sum_le_sum
  intro i _
  change p (lof i (x i - z i)) ≤ p (lof i (x i - v i))
  rw [hz]

/-- A compatible uniform additive group structure is determined by its topology. -/
private theorem globalThetaIsotypeSum_uniform_eq {A : Type*} [AddCommGroup A] (t : TopologicalSpace A)
    (h : @IsTopologicalAddGroup A t _) (u : UniformSpace A) (hu : u.toTopologicalSpace = t)
    (hg : @IsUniformAddGroup A u _) : u = @IsTopologicalAddGroup.rightUniformSpace A _ t h := by
  subst t
  exact (@IsUniformAddGroup.rightUniformSpace_eq A u _ hg).symm

/-- Paper: Remark 6.2.1.4(1), p. 297.
The locally convex direct sum of the global isotypes is Hausdorff and complete. -/
theorem globalThetaIsotypeSum_complete :
    let X := fun ω : PontryaginDual C₁ ↦ ↥(E𝔽(ω))
    letI := Classical.decEq (PontryaginDual C₁)
    let D := ⨁ ω, X ω
    letI := locallyConvexFinalTopology (DirectSum.lof ℂ _ X)
    T2Space D ∧ PolynormableSpace ℂ D ∧
      ∀ (u : UniformSpace D), u.toTopologicalSpace = (inferInstance : TopologicalSpace D) →
        @IsUniformAddGroup D u _ → @CompleteSpace D u := by
  classical
  let : T2Space Θ𝔽 := globalAdelicThetaSpace_t2_of_isClosed (adelicTheta_ker_isClosed (F := F))
  let : PolynormableSpace ℂ Θ𝔽 := globalAdelicThetaSpace_polynormable
  let : IsTopologicalAddGroup Θ𝔽 := PolynormableSpace.isTopologicalAddGroup ℂ _
  let : UniformSpace Θ𝔽 := IsTopologicalAddGroup.rightUniformSpace _
  let : IsUniformAddGroup Θ𝔽 := isUniformAddGroup_of_addCommGroup
  let : CompleteSpace Θ𝔽 := globalAdelicThetaSpace_complete
  let X := fun ω : PontryaginDual C₁ ↦ ↥(E𝔽(ω))
  let D := ⨁ ω, X ω
  let lof := DirectSum.lof ℂ (PontryaginDual C₁) X
  let : ∀ ω, UniformSpace (X ω) := fun ω ↦ UniformSpace.comap Subtype.val inferInstance
  let : ∀ ω, IsUniformAddGroup (X ω) := fun ω ↦
    IsUniformAddGroup.comap (f := (E𝔽(ω)).subtype.toAddMonoidHom)
  let : ∀ ω, CompleteSpace (X ω) := fun ω ↦ (globalThetaIsotypicAverage_equiv ω).1.completeSpace_coe
  let : TopologicalSpace D := locallyConvexFinalTopology lof
  have hD := globalThetaIsotypeSum_finalTopology_withSeminorms lof
  let : IsTopologicalAddGroup D := hD.isTopologicalAddGroup
  let : PolynormableSpace ℂ D := hD.toPolynormableSpace
  refine ⟨T2Space.of_injective_continuous (f := fun x : D ↦ fun i ↦ x i)
    (fun _ _ h ↦ DFinsupp.ext (congrFun h))
    (continuous_pi (globalThetaIsotypeSum_continuous_lcDirectSum_component X)), inferInstance, ?_⟩
  intro u hu hg
  have ht : u.toTopologicalSpace = locallyConvexFinalTopology lof := hu
  let : UniformSpace D := u
  let : IsUniformAddGroup D := hg
  have heq : u = @IsTopologicalAddGroup.rightUniformSpace D _
      (locallyConvexFinalTopology lof) hD.isTopologicalAddGroup :=
    globalThetaIsotypeSum_uniform_eq _ hD.isTopologicalAddGroup u ht hg
  rw [heq]
  exact globalThetaIsotypeSum_completeSpace_lcDirectSum X

-- The properties referred to in Remark 6.2.1.4(1) are listed in Theorem 5.2.3.1(2).
local notation "sumProperties(" D ")" =>
  IsLFSpace D ∧ IsNuclearTVS D ∧ BarrelledSpace ℂ D ∧ MontelSpace ℂ D ∧
    CompleteSpace (StrongDual ℂ D) ∧ IsNuclearTVS (StrongDual ℂ D) ∧
    BarrelledSpace ℂ (StrongDual ℂ D) ∧ MontelSpace ℂ (StrongDual ℂ D)

/-- Paper: Remark 6.2.1.4(1), p. 297.
The locally convex sum of the local isotypes inherits the space and strong-dual properties
listed in Theorem 5.2.3.1(2). -/
theorem sLocalThetaIsotypeSum_inherited_properties :
    let X := fun χ : PontryaginDual J₁(S) ↦ ↥(Eₛ(χ))
    letI := Classical.decEq (PontryaginDual J₁(S))
    let D := ⨁ χ, X χ
    letI := locallyConvexFinalTopology (DirectSum.lof ℂ _ X)
    sumProperties(D) := by sorry

/-- Paper: Remark 6.2.1.4(1), p. 297.
The locally convex sum of the global isotypes inherits the space and strong-dual properties
listed in Theorem 5.2.3.1(2). -/
theorem globalThetaIsotypeSum_inherited_properties :
    let X := fun ω : PontryaginDual C₁ ↦ ↥(E𝔽(ω))
    letI := Classical.decEq (PontryaginDual C₁)
    let D := ⨁ ω, X ω
    letI := locallyConvexFinalTopology (DirectSum.lof ℂ _ X)
    sumProperties(D) := by sorry

-- TODO(paper-gap): Remark 6.2.1.4(2) also asserts nonclosed product images.
-- At the rational archimedean stage the image in the product of homogeneous
-- theta quotients is the whole product. The remark conflates that product
-- with the product of the meromorphic Mellin target spaces.

/-- Paper: Remark 6.2.1.4(2), p. 298.
The global theta quotient has nonclosed image in the product of its homogeneous
quotients.
Deviation: The earlier continuous injection in (5.2.3.13) identifies the product map. -/
theorem globalThetaToHomogeneousProduct_not_isClosed_range :
    ¬ IsClosed (Set.range (exists_globalThetaToHomogeneousProduct (F := F)).choose) := by sorry

/-- Paper: Remark 6.2.1.4(2), p. 298.
The topology on the global theta quotient induced by the product of homogeneous
quotients is strictly coarser than its intrinsic topology.
Deviation: The earlier continuous injection in (5.2.3.13) identifies the product map. -/
theorem globalThetaToHomogeneousProduct_not_isInducing :
    ¬ IsInducing (exists_globalThetaToHomogeneousProduct (F := F)).choose := by
  intro h
  let P := (exists_globalThetaToHomogeneousProduct (F := F)).choose
  let : UniformSpace Θ𝔽 := IsTopologicalAddGroup.rightUniformSpace _
  let : IsUniformAddGroup Θ𝔽 := isUniformAddGroup_of_addCommGroup
  let : CompleteSpace Θ𝔽 := globalAdelicThetaSpace_complete
  let (ω : PontryaginDual C₁) : UniformSpace (Θ𝔽ω(ω)) := IsTopologicalAddGroup.rightUniformSpace _
  let (ω : PontryaginDual C₁) : IsUniformAddGroup (Θ𝔽ω(ω)) := isUniformAddGroup_of_addCommGroup
  let (ω : PontryaginDual C₁) : T2Space (Θ𝔽ω(ω)) := by
    have : IsClosed (LinearMap.ker (homogeneousAdelicThetaLinearMap F ω) :
        Set (SchwartzBruhat (Multiplicative 𝔸[F]))) :=
      homogeneousAdelicTheta_ker_isClosed ω
    infer_instance
  exact globalThetaToHomogeneousProduct_not_isClosed_range (F := F)
    (AddMonoidHom.isUniformInducing_of_isInducing (f := P.toAddMonoidHom) h).isComplete_range.isClosed

end IsotypicSums

section StandardFunctions

local notation "L(" v ")" => HeightOneSpectrum.adicCompletion (R := 𝓞 F) F v
local notation "O(" v ")" => HeightOneSpectrum.adicCompletionIntegers (R := 𝓞 F) F v
local notation "U(" v ")" => ((O(v)).units : Set (L(v))ˣ)
local notation "μ(" v ")" => finiteLocalMultiplicativeTamagawaMeasure F v

local instance finiteIdeleMeasurableSpaceSec2 (v : V) : MeasurableSpace (L(v))ˣ := borel _

open Classical in
/-- Paper: Theorem 6.2.2.1, p. 298.
In the ramified case the zeta integral is the integer-unit mass for matching unit
characters and zero for all others. Compact support in the multiplicative group
gives integrability for every local quasi-character. -/
theorem finiteStandardGaussian_zeta_of_ramified (v : V) (c d : QuasiCharacter (L(v))ˣ)
    (_hc : ∃ u ∈ U(v), c u ≠ 1) :
    Integrable (fun g : (L(v))ˣ ↦ finiteStandardGaussian v c
      (Multiplicative.ofAdd g.val) * d g) (μ(v)) ∧
    (localIdelicZetaIntegral (μ(v)) (fun x ↦ finiteStandardGaussian v c
      (Multiplicative.ofAdd x)) d =
      if (∀ u ∈ U(v), d u = c u) then ((μ(v)) (U(v))).toReal else 0) := by
  classical
  let : BorelSpace (L(v))ˣ := ⟨rfl⟩
  let : (μ(v)).IsHaarMeasure := finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure v
  let q (g : (L(v))ˣ) := d g / c g
  have hc (g : (L(v))ˣ) : c g ≠ 0 := ((Group.isUnit g).map c).ne_zero
  have hram : ¬ ∀ u ∈ U(v), c u = 1 := fun h ↦
    _hc.elim fun u hu ↦ hu.2 (h u hu.1)
  have hfun : (fun g : (L(v))ˣ ↦ finiteStandardGaussian v c (Multiplicative.ofAdd g.val) * d g) =
      (U(v)).indicator q := by
    funext g
    by_cases hg : g ∈ U(v)
    · rw [Set.indicator_of_mem hg, finiteStandardGaussian_integerUnit v c g hg]
      exact (mul_comm _ _).trans (div_eq_mul_inv _ _).symm
    · rw [Set.indicator_of_notMem hg]
      have hv : g.val ∉ Units.val '' U(v) := fun ⟨u, hu, h⟩ ↦ hg ((Units.ext h) ▸ hu)
      have hz : finiteStandardGaussian v c (Multiplicative.ofAdd g.val) = 0 :=
        (ite_eq_right hram).trans (Set.indicator_of_notMem hv _)
      rw [hz, zero_mul]
  have hopen : IsOpen (U(v)) := Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)
  have hcompact : IsCompact (U(v)) := Submonoid.units_isCompact
    (isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v))
  have hq : Continuous q := d.continuous.div c.continuous hc
  constructor
  · rw [hfun, integrable_indicator_iff hopen.measurableSet]
    exact hq.continuousOn.integrableOn_compact hcompact
  · change (∫ g : (L(v))ˣ, finiteStandardGaussian v c (Multiplicative.ofAdd g.val) * d g ∂μ(v)) = _
    rw [hfun, integral_indicator hopen.measurableSet]
    split_ifs with hmatch
    · have eqOne : Set.EqOn q (fun _ ↦ (1 : ℂ)) (U(v)) := fun u hu ↦
        (div_eq_one_iff_eq (hc u)).mpr (hmatch u hu)
      rw [setIntegral_congr_fun hopen.measurableSet eqOne, setIntegral_const]
      simp [measureReal_def]
    · push Not at hmatch
      obtain ⟨a, ha, hne⟩ := hmatch
      have hpre : (fun y : (L(v))ˣ ↦ a * y) ⁻¹' U(v) = U(v) := by
        ext y
        exact (O(v)).units.mul_mem_cancel_left ha
      have hI := (measurePreserving_mul_left (μ(v)) a).setIntegral_preimage_emb
        (Homeomorph.mulLeft a).toMeasurableEquiv.measurableEmbedding q (U(v))
      rw [hpre] at hI
      change (∫ y in U(v), q (a * y) ∂μ(v)) = ∫ y in U(v), q y ∂μ(v) at hI
      have hmul (y : (L(v))ˣ) : q (a * y) = q a * q y := by
        simp only [q, map_mul, mul_div_mul_comm]
      simp_rw [hmul] at hI
      rw [integral_const_mul, ← sub_eq_zero, ← sub_one_mul] at hI
      exact (mul_eq_zero.mp hI).resolve_left
        (sub_ne_zero.mpr (fun h ↦ hne ((div_eq_one_iff_eq (hc a)).mp h)))

/-- Paper: Theorem 6.2.2.1, p. 298.
Tensoring an archimedean test with the fixed standard tests at the finite places
gives a linear map into the S-adelic test space.
Deviation: The tensor identification uses the inductive topology of §2.1.4. -/
def sLocalStandardThetaTensor (c : QuasiCharacter Jₛ(S)) : ℬ∞ →ₗ[ℂ] ℬₛ(S) :=
  let e := (sAdeleSchwartz_inductiveTensor_equiv F S).choose
  let W := FinestLocallyConvex (⨂[ℂ] v : S, ℬ(L(v.val)))
  let g : W := ⨂ₜ[ℂ] v : S, finiteStandardGaussian v.val (sLocalFiniteRestriction v c)
  e.toLinearMap.comp ((TensorProduct.mk ℂ ℬ∞ W).flip g)

/-- Paper: Theorem 6.2.2.1, p. 298.
Evaluation on an S-adele multiplies the archimedean test value by the standard
finite test value at each finite coordinate. -/
theorem sLocalStandardThetaTensor_apply (c : QuasiCharacter Jₛ(S)) (f : ℬ∞)
    (x : SAdeleRing F S) :
    sLocalStandardThetaTensor c f (Multiplicative.ofAdd x) =
      f (Multiplicative.ofAdd x.1) * ∏ v : S, finiteStandardGaussian v.val
        (sLocalFiniteRestriction v c) (Multiplicative.ofAdd (x.2 v)) := by
  let factors (v : S) : ℬ(L(v.val)) :=
    finiteStandardGaussian (F := F) v.val (sLocalFiniteRestriction (F := F) v c)
  let W := FinestLocallyConvex (⨂[ℂ] v : S, ℬ(L(v.val)))
  let b : W := ⨂ₜ[ℂ] v : S, factors v
  let e := (sAdeleSchwartz_inductiveTensor_equiv F S).choose
  have slice {X Y Z : Type _} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
      [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
      [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z]
      (E : InductiveTensor X Y ≃L[ℂ] Z) (a : X) (b : Y) (p : Z → ℂ) (r : ℂ)
      (h : p (E (a ⊗ₜ[ℂ] b)) = r) :
      p (E.toLinearMap.comp ((TensorProduct.mk ℂ X Y).flip b) a) = r := h
  have hx := (sAdeleSchwartz_inductiveTensor_equiv F S).choose_spec f factors x
  unfold sLocalStandardThetaTensor
  with_reducible_and_instances
    exact slice (X := ℬ∞) (Y := W) (Z := ℬₛ(S)) e f b
      (fun φ : ℬₛ(S) ↦ φ (Multiplicative.ofAdd x)) _ hx

/-- Paper: Theorem 6.2.2.1, p. 298.
For trivial S-integer Picard group, the archimedean test space maps continuously,
surjectively and openly onto the global isotype after tensoring with the standard tests.
Deviation: The existence of the stated descent requires unramifiedness outside S.
The fixed finite tensor factor identifies its domain with the archimedean test space. -/
theorem sLocalStandardThetaTensor_toGlobal_openQuotient
    (_hPic : Subsingleton Picₛ(S)) {ω : PontryaginDual C₁}
    (hω : NormOneCharacterUnramifiedOutside ω S) :
    let c := sIdeleRestriction F S hω.choose
    let χ := sLocalNormOneCharacter S ω hω
    IsOpenQuotientMap (fun f : ℬ∞ ↦ sLocalHomogeneousThetaToGlobal (ω := ω) hω
      ((Kₛω(S, χ)).mkQ (sLocalStandardThetaTensor (F := F) (S := S) c f))) := by sorry

local notation "I∞" => (InfiniteAdeleRing F)ˣ
local notation "N∞" => Nₛ((∅ : Finset V))
local notation "archPart(" D ")" => Units.map (RingHom.fst (InfiniteAdeleRing F)
  (∀ v : D, L(v.val))).toMonoidHom
local notation "archInsert(" D ")" =>
  Units.map (MonoidHom.inl (InfiniteAdeleRing F) (∀ v : D, L(v.val)))

/-- Paper: (6.2.2.3), p. 298.
Every term of the archimedean integral is absolutely integrable. The norm-one
archimedean measure is the Tamagawa measure for the stage with no finite places. -/
theorem infiniteStandardThetaAverage_integrable (χ : PontryaginDual Iₛ(S))
    (f : ℬ∞) (a x : I∞) :
    Integrable (fun g : N∞ ↦
      f (Multiplicative.ofAdd ((a * archPart((∅ : Finset V)) g.val)⁻¹ * x).val) *
        (χ (archInsert(S) (a * archPart((∅ : Finset V)) g.val)) : ℂ))
      (sNormOneIdeleTamagawaMeasure F ∅) := by sorry

/-- Paper: (6.2.2.3), p. 298.
The sum of archimedean integrals specifies a continuous linear map into the
continuous functions on the archimedean ideles. -/
theorem exists_infiniteStandardThetaAverage (χ : PontryaginDual Iₛ(S))
    (r : Fin (classNumber F) → Nₛ(S)) :
    ∃ A : ℬ∞ →L[ℂ] C(I∞, ℂ), ∀ f x,
      A f x = ∑ k, ∫ g : N∞,
        let a := archPart(S) (r k).val * archPart((∅ : Finset V)) g.val
        f (Multiplicative.ofAdd (a⁻¹ * x).val) * (χ (archInsert(S) a) : ℂ)
        ∂sNormOneIdeleTamagawaMeasure F ∅ := by sorry

/-- Paper: (6.2.2.3), p. 298.
The archimedean operator sums the character-weighted integrals over the
norm-one archimedean ideles, one translate for each entry of the supplied family.
Deviation: The analytic formula works for arbitrary entries. To obtain the printed sum,
choose ideal class representatives with the identity representing the principal class. -/
def infiniteStandardThetaAverage (χ : PontryaginDual Iₛ(S))
    (r : Fin (classNumber F) → Nₛ(S)) : ℬ∞ →L[ℂ] C(I∞, ℂ) :=
  (exists_infiniteStandardThetaAverage χ r).choose

/-- Paper: (6.2.2.3), p. 298.
Evaluation on an archimedean idele gives the finite sum in the paper. -/
theorem infiniteStandardThetaAverage_apply (χ : PontryaginDual Iₛ(S))
    (r : Fin (classNumber F) → Nₛ(S)) (f : ℬ∞) (x : I∞) :
    infiniteStandardThetaAverage χ r f x = ∑ k, ∫ g : N∞,
      let a := archPart(S) (r k).val * archPart((∅ : Finset V)) g.val
      f (Multiplicative.ofAdd (a⁻¹ * x).val) * (χ (archInsert(S) a) : ℂ)
      ∂sNormOneIdeleTamagawaMeasure F ∅ :=
  (exists_infiniteStandardThetaAverage χ r).choose_spec f x

-- In §5.3.1 the punctured-field tests are additive tests vanishing at zero.
-- Local constancy makes these vanish on a neighborhood of zero.
/-- Paper: (6.2.2.4), p. 299.
The punctured-field tests form the subspace of additive Schwartz–Bruhat functions with
value zero at the origin, equipped with its induced topology as in §5.3.1. -/
def finitePuncturedThetaTestSpace (v : V) : Submodule ℂ ℬ(L(v)) :=
  LinearMap.ker ((LinearMap.proj (Multiplicative.ofAdd (0 : L(v)))).comp
    (schwartzBruhatSubmodule (Multiplicative (L(v)))).subtype)

/-- Paper: (6.2.2.4), p. 299.
An additive test belongs to the punctured-field subspace exactly when it vanishes at zero. -/
theorem mem_finitePuncturedThetaTestSpace (v : V) (f : ℬ(L(v))) :
    f ∈ finitePuncturedThetaTestSpace v ↔ f (Multiplicative.ofAdd (0 : L(v))) = 0 := Iff.rfl

local notation "ℬ₀(" v ")" => ↥(finitePuncturedThetaTestSpace v)

/-- A locally constant compactly supported field test vanishing at zero is integrable
after inverse translation on the unit group and multiplication by a continuous factor. -/
private theorem finiteStandardThetaAverage_integrable_of_locallyConstant
    {K : Type*} [NormedField K] [MeasurableSpace Kˣ] [BorelSpace Kˣ]
    (μ : Measure Kˣ) [IsFiniteMeasureOnCompacts μ] (test : K → ℂ)
    (hloc : IsLocallyConstant test) (hcompact : HasCompactSupport test) (hzero : test 0 = 0)
    (c : Kˣ → ℂ) (hc : Continuous c) (x : Kˣ) :
    Integrable (fun g : Kˣ ↦ test (g⁻¹ * x).val * c g) μ := by
  have hclosed : IsClosed (Function.support test) := (hloc.isClopen_fiber 0).2.isClosed_compl
  have hrange : tsupport test ⊆ Set.range (Units.val : Kˣ → K) := by
    intro y hy
    have hmem : y ∈ Function.support test := by
      rwa [tsupport, hclosed.closure_eq] at hy
    have hy0 : y ≠ 0 := by
      rintro rfl
      exact hmem hzero
    exact ⟨Units.mk0 y hy0, rfl⟩
  have hpre : IsCompact (Units.val ⁻¹' tsupport test : Set Kˣ) := by
    rw [(Units.isEmbedding_val₀ (G₀ := K)).isCompact_iff,
      Set.image_preimage_eq_of_subset hrange]
    exact hcompact
  let unitTest : Kˣ → ℂ := test ∘ Units.val
  have hsupport : HasCompactSupport unitTest :=
    hpre.of_isClosed_subset (isClosed_tsupport _)
      (tsupport_comp_subset_preimage test Units.continuous_val)
  let shift : Kˣ ≃ₜ Kˣ := (Homeomorph.inv Kˣ).trans (Homeomorph.mulRight x)
  have hcont : Continuous (unitTest ∘ shift) :=
    (hloc.continuous.comp Units.continuous_val).comp shift.continuous
  change Integrable (fun g : Kˣ ↦ (unitTest ∘ shift) g * c g) μ
  exact (hcont.mul hc).integrable_of_hasCompactSupport (hsupport.comp_homeomorph shift).mul_right

/-- Paper: (6.2.2.4), p. 299.
The finite-place integral of a compactly supported test on the punctured field is absolutely
integrable for every translation and unitary character. -/
theorem finiteStandardThetaAverage_integrable (v : V) (χ : PontryaginDual (L(v))ˣ)
    (f : ℬ₀(v)) (x : (L(v))ˣ) :
    Integrable (fun g : (L(v))ˣ ↦ f.val (Multiplicative.ofAdd (g⁻¹ * x).val) * (χ g : ℂ)) (μ(v)) := by
  let test (y : L(v)) : ℂ := f.val (Multiplicative.ofAdd y)
  have htest : IsLocallyConstant test ∧ HasCompactSupport test :=
    (mem_finitePlaceSchwartz_iff F v test).mp ⟨f.val, fun _ ↦ rfl⟩
  have hzero : test 0 = 0 := (mem_finitePuncturedThetaTestSpace v f.val).mp f.property
  have hχ : Continuous (fun g : (L(v))ˣ ↦ (χ g : ℂ)) :=
    continuous_subtype_val.comp χ.continuous
  let : BorelSpace (L(v))ˣ := ⟨rfl⟩
  let : (μ(v)).IsHaarMeasure := finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure v
  exact finiteStandardThetaAverage_integrable_of_locallyConstant (μ(v)) test htest.1 htest.2 hzero
    (fun g : (L(v))ˣ ↦ (χ g : ℂ)) hχ x

/-- On a group with a left-invariant measure, convolving against a character
factors as the character times the value at the identity. -/
private theorem exists_finiteStandardThetaAverage_factor {G : Type*} [Group G]
    [MeasurableSpace G] [MeasurableMul G] (ν : Measure G) [ν.IsMulLeftInvariant]
    (φ : G → ℂ) (c : G →* Circle) (x : G) :
    (∫ g, φ (g⁻¹ * x) * (c g : ℂ) ∂ν) = (c x : ℂ) * ∫ g, φ g⁻¹ * (c g : ℂ) ∂ν := by
  rw [← integral_mul_left_eq_self (fun g ↦ φ (g⁻¹ * x) * (c g : ℂ)) x, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g ↦ ?_)
  simp only [mul_inv_rev, inv_mul_cancel_right, map_mul, Circle.coe_mul]
  ring

/-- Convolution against a character, on a subspace of a space where every linear functional
is continuous, is a continuous linear map into the continuous functions: it is the character
times the value of a linear functional. -/
private theorem exists_finiteStandardThetaAverage_abstract {B G : Type*} [AddCommGroup B]
    [Module ℂ B] [TopologicalSpace B] (p : Submodule ℂ B)
    (hB : ∀ L : B →ₗ[ℂ] ℂ, Continuous L) [Group G] [TopologicalSpace G]
    {_ : MeasurableSpace G} [MeasurableMul G] (ν : Measure G) [ν.IsMulLeftInvariant]
    (χ : G →* Circle) (hχ : Continuous χ) (ev : p →ₗ[ℂ] G → ℂ)
    (hint : ∀ f, Integrable (fun g ↦ ev f g⁻¹ * (χ g : ℂ)) ν) :
    ∃ A : p →L[ℂ] C(G, ℂ), ∀ f x, A f x = ∫ g, ev f (g⁻¹ * x) * (χ g : ℂ) ∂ν := by
  let c₀ : p →ₗ[ℂ] ℂ :=
    { toFun := fun f ↦ ∫ g, ev f g⁻¹ * (χ g : ℂ) ∂ν
      map_add' := fun f h ↦ by
        simp only [map_add, Pi.add_apply, add_mul]
        exact integral_add (hint f) (hint h)
      map_smul' := fun a f ↦ by
        simp only [map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc, RingHom.id_apply]
        exact integral_const_mul a _ }
  obtain ⟨P, hP⟩ := LinearMap.exists_leftInverse_of_injective p.subtype p.ker_subtype
  have hc₀ : Continuous c₀ :=
    ((hB (c₀.comp P)).comp continuous_subtype_val).congr fun f ↦
      congrArg c₀ (LinearMap.congr_fun hP f)
  let χC : C(G, ℂ) := ⟨fun g ↦ (χ g : ℂ), continuous_subtype_val.comp hχ⟩
  refine ⟨(ContinuousLinearMap.mk c₀ hc₀).smulRight χC, fun f x ↦ ?_⟩
  rw [exists_finiteStandardThetaAverage_factor ν (ev f) χ x, mul_comm]
  rfl

/-- Paper: (6.2.2.4), p. 299.
The finite-place convolution formula specifies a continuous linear map on
locally constant, compactly supported functions on the punctured field. -/
theorem exists_finiteStandardThetaAverage (v : V) (χ : PontryaginDual (L(v))ˣ) :
    ∃ A : ℬ₀(v) →L[ℂ] C((L(v))ˣ, ℂ), ∀ f x,
      A f x = ∫ g : (L(v))ˣ, f.val (Multiplicative.ofAdd (g⁻¹ * x).val) * (χ g : ℂ) ∂μ(v) := by
  let : BorelSpace (L(v))ˣ := ⟨rfl⟩
  let : (μ(v)).IsHaarMeasure := finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure v
  let ev : ℬ₀(v) →ₗ[ℂ] (L(v))ˣ → ℂ :=
    (LinearMap.funLeft ℂ ℂ fun y : (L(v))ˣ ↦ Multiplicative.ofAdd y.val).comp
      (((schwartzBruhatSubmodule (Multiplicative (L(v)))).subtype : ℬ(L(v)) →ₗ[ℂ] _).comp
        (finitePuncturedThetaTestSpace v).subtype)
  have hB (L : ℬ(L(v)) →ₗ[ℂ] ℂ) : Continuous L :=
    (congrArg (fun t ↦ @Continuous ℬ(L(v)) ℂ t _ L)
      (finitePlaceSchwartz_finestTopology F v)).mpr
      (continuous_of_finestLocallyConvex ℬ(L(v)) L)
  have hint (f : ℬ₀(v)) : Integrable (fun g ↦ ev f g⁻¹ * (χ g : ℂ)) (μ(v)) :=
    (finiteStandardThetaAverage_integrable v χ f 1).congr
      (Filter.Eventually.of_forall fun g ↦ congrArg (fun y : (L(v))ˣ ↦ ev f y * (χ g : ℂ))
        (mul_one g⁻¹))
  exact exists_finiteStandardThetaAverage_abstract (finitePuncturedThetaTestSpace v) hB (μ(v))
    χ.toMonoidHom χ.continuous ev hint

/-- Paper: (6.2.2.4), p. 299.
The finite operator convolves a compactly supported punctured-field test with the local
character against multiplicative Tamagawa measure. The inverse in the test gives the
Mellin functional for the inverse character at the identity. -/
def finiteStandardThetaAverage (v : V) (χ : PontryaginDual (L(v))ˣ) :
    ℬ₀(v) →L[ℂ] C((L(v))ˣ, ℂ) :=
  (exists_finiteStandardThetaAverage v χ).choose

/-- Paper: (6.2.2.4), p. 299.
At the identity, the finite convolution integrates the inverse pullback of the test
against the local character. -/
theorem finiteStandardThetaAverage_one (v : V) (χ : PontryaginDual (L(v))ˣ)
    (f : ℬ₀(v)) :
    finiteStandardThetaAverage v χ f 1 =
      ∫ g : (L(v))ˣ, f.val (Multiplicative.ofAdd (g⁻¹).val) * (χ g : ℂ) ∂μ(v) := by
  have h := (exists_finiteStandardThetaAverage v χ).choose_spec f 1
  simpa [finiteStandardThetaAverage] using h

/-- Paper: (6.2.2.11), p. 301.
The finite convolution is the character times the Mellin integral with the inverse character.
Deviation: On the test χ times the unit indicator, the coefficient is the integer-unit mass. -/
theorem finiteStandardThetaAverage_eq_character_mul_integral (v : V)
    (χ : PontryaginDual (L(v))ˣ) (f : ℬ₀(v)) (x : (L(v))ˣ) :
    finiteStandardThetaAverage v χ f x = (χ x : ℂ) *
      ∫ y : (L(v))ˣ, f.val (Multiplicative.ofAdd y.val) * (χ y : ℂ)⁻¹ ∂μ(v) := by
  let : BorelSpace (L(v))ˣ := ⟨rfl⟩
  let : (μ(v)).IsHaarMeasure := finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure v
  let : ProperSpace (L(v)) := properSpace_adicCompletion v
  let : LocallyCompactSpace (L(v))ˣ :=
    (IsOpenUnits.isOpenEmbedding_unitsVal (M := L(v))).locallyCompactSpace
  have : (μ(v)).IsInvInvariant := by
    constructor
    unfold finiteLocalMultiplicativeTamagawaMeasure
    rw [Measure.inv_def, Measure.map_smul, Measure.map_inv_eq_self]
    exact measurable_inv.aemeasurable
  have factor {G : Type _} [CommGroup G] [MeasurableSpace G] [MeasurableMul G] [MeasurableInv G]
      (ν : Measure G) [ν.IsInvInvariant] [ν.IsMulLeftInvariant]
      (φ : G → ℂ) (c : G →* Circle) (x : G) :
      (∫ g, φ (g⁻¹ * x) * (c g : ℂ) ∂ν) = (c x : ℂ) * ∫ y, φ y * (c y : ℂ)⁻¹ ∂ν := by
    let k (g : G) := φ (g⁻¹ * x) * (c g : ℂ)
    refine (integral_div_left_eq_self k ν x).symm.trans ?_
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    change φ ((x / y)⁻¹ * x) * (c (x / y) : ℂ) = _
    rw [inv_div, div_mul_cancel, map_div, Circle.coe_div, div_eq_mul_inv]
    ring
  exact ((exists_finiteStandardThetaAverage v χ).choose_spec f x).trans
    (factor (μ(v)) (fun y ↦ f.val (Multiplicative.ofAdd y.val)) χ.toMonoidHom x)

/-- Paper: Theorem 6.2.2.1(1), p. 299.
The kernel of the archimedean operator is closed in the archimedean test space. -/
theorem infiniteStandardThetaAverage_isClosed_ker (χ : PontryaginDual Iₛ(S))
    (r : Fin (classNumber F) → Nₛ(S)) :
    IsClosed ((infiniteStandardThetaAverage χ r).ker : Set ℬ∞) :=
  ContinuousLinearMap.isClosed_ker _

/-- Paper: Theorem 6.2.2.1(1), p. 299.
The kernel of the finite convolution is closed in the multiplicative test space. -/
theorem finiteStandardThetaAverage_isClosed_ker (v : V) (χ : PontryaginDual (L(v))ˣ) :
    IsClosed ((finiteStandardThetaAverage v χ).ker : Set (ℬ₀(v))) :=
  ContinuousLinearMap.isClosed_ker _

-- TODO(paper-gap): The tensor agreement in Theorem 6.2.2.1(1), p. 299, fails.
-- For ℚ at S = {∞, p} with trivial character, take a finite test 1_{pℤₚˣ}
-- and a nonnegative even archimedean bump at ±1 supported away from ±p.
-- At the identity the full norm-one integral is zero, because the finite
-- support forces the absolute value of the inverse real component to be p.
-- The product of the separate integrals is strictly positive.

/-- Paper: Theorem 6.2.2.1(1), p. 299.
Integrating over a single archimedean norm fibre gives the archimedean factor of the
Mellin transform with the character convention of §5.2.
Deviation: (6.2.2.3) uses the inverse argument and sums translates over ideal classes.
The product formula of §3.3 uses one fibre with the positive argument. -/
theorem exists_infiniteStandardThetaMellinAverage (χ : PontryaginDual Iₛ(S)) :
    ∃ A : ℬ∞ →L[ℂ] C(I∞, ℂ), ∀ f x,
      A f x = ∫ g : N∞,
        let h := archPart((∅ : Finset V)) g.val
        f (Multiplicative.ofAdd (h * x).val) * (χ (archInsert(S) h) : ℂ)
        ∂sNormOneIdeleTamagawaMeasure F ∅ := by
  let D : Finset V := ∅
  let (w : InfinitePlace F) : MeasurableSpace w.Completion := borel _
  let (v : V) : MeasurableSpace (v.adicCompletion F) := borel _
  let (w : InfinitePlace F) : BorelSpace w.Completion := ⟨rfl⟩
  let (v : V) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let (v : V) : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
  let : MeasurableSpace (SAdeleRing F D) := inferInstanceAs
    (MeasurableSpace (((w : InfinitePlace F) → w.Completion) × ((v : D) → v.val.adicCompletion F)))
  let : BorelSpace (SAdeleRing F D) := inferInstanceAs
    (BorelSpace (((w : InfinitePlace F) → w.Completion) × ((v : D) → v.val.adicCompletion F)))
  let : BorelSpace Iₛ(D) := by
    refine ⟨?_⟩
    rw [(sIdeleGroup_description F D).1.eq_induced, borel_comap, ← BorelSpace.measurable_eq]
    rfl
  let ν := sNormOneIdeleTamagawaMeasure F (∅ : Finset V)
  let : LocallyCompactSpace Iₛ((∅ : Finset V)) := (sIdeleGroup_description F ∅).2.2.1
  have hn : Continuous (sIdeleNorm F (∅ : Finset V)) :=
    (isProperMap_sIdeleQuotientNorm F ∅).continuous.comp continuous_quotient_mk'
  have hK : IsClosed (N∞ : Set Iₛ((∅ : Finset V))) :=
    isClosed_eq hn continuous_const
  let : LocallyCompactSpace N∞ := hK.locallyCompactSpace
  let : ν.IsHaarMeasure := (sNormOneIdeleTamagawaMeasure_existsUnique F ∅).exists.choose_spec.1
  let : ν.Regular := (sNormOneIdeleTamagawaMeasure_existsUnique F ∅).exists.choose_spec.2.1
  obtain ⟨A, hA⟩ := exists_infiniteStandardThetaAverage χ⁻¹ (fun _ ↦ 1)
  refine ⟨(classNumber F : ℂ)⁻¹ • A, fun f x ↦ ?_⟩
  let K (g : N∞) := f (Multiplicative.ofAdd ((archPart((∅ : Finset V)) g.val) * x).val) *
    (χ (archInsert(S) (archPart((∅ : Finset V)) g.val)) : ℂ)
  have hf := hA f x
  have hi : (∫ g : N∞, K g⁻¹ ∂ν) = ∫ g : N∞, K g ∂ν := integral_inv_eq_self K ν
  have hj : A f x = (classNumber F : ℂ) * ∫ g : N∞, K g ∂ν := by
    rw [hf, ← hi]
    simp only [OneMemClass.coe_one, map_one, one_mul, K, InvMemClass.coe_inv, map_inv,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rfl
  change (classNumber F : ℂ)⁻¹ * A f x = ∫ g : N∞, K g ∂ν
  rw [hj, ← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (classNumber_pos F).ne'), one_mul]

/-- Paper: Theorem 6.2.2.1(1), p. 299.
The archimedean Mellin average integrates the positive translate against the given character.
Deviation: This uses the single norm fibre occurring in the Mellin integral of §3.3. -/
def infiniteStandardThetaMellinAverage (χ : PontryaginDual Iₛ(S)) : ℬ∞ →L[ℂ] C(I∞, ℂ) :=
  (exists_infiniteStandardThetaMellinAverage χ).choose

/-- Paper: Theorem 6.2.2.1(1), p. 299.
At each idele the Mellin average evaluates to the character-weighted norm-fibre integral.
Deviation: The factors follow the homogeneous transform of §5.2. -/
theorem infiniteStandardThetaMellinAverage_apply (χ : PontryaginDual Iₛ(S)) (f : ℬ∞)
    (x : I∞) :
    infiniteStandardThetaMellinAverage χ f x = ∫ g : N∞,
      let h := archPart((∅ : Finset V)) g.val
      f (Multiplicative.ofAdd (h * x).val) * (χ (archInsert(S) h) : ℂ)
      ∂sNormOneIdeleTamagawaMeasure F ∅ :=
  (exists_infiniteStandardThetaMellinAverage χ).choose_spec f x

/-- Paper: Theorem 6.2.2.1(1), p. 299.
Tensoring with the standard finite test identifies the local homogeneous quotient with
the archimedean quotient by the kernel of the archimedean Mellin average.
Deviation: This kernel uses the character orientation of §5.2 and the single norm fibre
of §3.3. The fixed tensor factor is expressed by insertion. -/
theorem sLocalStandardThetaTensor_quotient_equiv
    (_hPic : Subsingleton Picₛ(S)) {ω : PontryaginDual C₁}
    (hω : NormOneCharacterUnramifiedOutside ω S) (χ : PontryaginDual Iₛ(S))
    (_hχ : ∀ (g : Nₛ(S)) (y : J₁(S)), y.val = QuotientGroup.mk g.val →
      χ g.val = sLocalNormOneCharacter S ω hω y) :
    let c := sIdeleRestriction F S hω.choose
    let χS := sLocalNormOneCharacter S ω hω
    let K := (infiniteStandardThetaMellinAverage χ).ker
    ∃ e : (ℬ∞ ⧸ K) ≃L[ℂ] Θₛω(S, χS), ∀ f : ℬ∞,
      e (K.mkQ f) = (Kₛω(S, χS)).mkQ (sLocalStandardThetaTensor c f) := by sorry

-- TODO(paper-gap): The archimedean output need not be constant on norm fibres
-- for nontrivial characters. Use a norm section for the logarithmic profile.
-- At norm zero the paper only obtains logarithmic growth, so a Schwartz
-- profile without a positive weight would fail even over ℚ with a Gaussian.

/-- Paper: Theorem 6.2.2.1(2), p. 299.
The archimedean operator has forward semi-exponential decay along the norm
coordinate, including all logarithmic derivatives.
Deviation: The profile is evaluated on the canonical norm section. Every strictly
positive norm weight gives a Schwartz profile, as allowed by the growth in (6.2.2.12). -/
theorem infiniteStandardThetaAverage_forwardDecay (χ : PontryaginDual Iₛ(S))
    (r : Fin (classNumber F) → Nₛ(S)) (f : ℬ∞) :
    (fun t : ℝ ↦
      let u : ℝ≥0ˣ := Units.mk0 (Real.toNNReal (Real.exp t))
        (Real.toNNReal_eq_zero.not.mpr (not_le_of_gt (Real.exp_pos t)))
      let x := Units.map (RingHom.fst (InfiniteAdeleRing F)
        (FiniteAdeleRing (𝓞 F) F)).toMonoidHom (canonicalIdeleNormSection F u)
      infiniteStandardThetaAverage χ r f x) ∈ logExponentialDecaySubmodule (Set.Ioi 0) := by sorry

/-- Paper: (6.2.2.12), p. 302.
Near norm zero, the archimedean operator grows at most as the logarithm to the
power of the number of archimedean places minus one. -/
theorem infiniteStandardThetaAverage_logBound (χ : PontryaginDual Iₛ(S))
    (r : Fin (classNumber F) → Nₛ(S)) (f : ℬ∞) :
    ∃ C ε : ℝ, 0 < C ∧ 0 < ε ∧ ∀ x : I∞,
      ((infiniteIdeleNorm F x).val : ℝ) < ε →
      ‖infiniteStandardThetaAverage χ r f x‖ ≤
        C * |Real.log (infiniteIdeleNorm F x).val| ^ (Fintype.card (InfinitePlace F) - 1) := by sorry

end StandardFunctions

/-- Pullback along the unique real coordinate identifies real Schwartz functions with
the rational adelic test functions at the stage with no finite places. -/
private theorem ratTrivialHomogeneousTheta_quotient_realEquiv :
    ∃ E : SchwartzMap ℝ ℂ ≃L[ℂ] ℬ(SAdeleRing ℚ ∅),
      ∀ (f : SchwartzMap ℝ ℂ) (x : SAdeleRing ℚ ∅),
        E f (Multiplicative.ofAdd x) = f (InfinitePlace.Completion.ringEquivRealOfIsReal
          Rat.isReal_infinitePlace (x.1 Rat.infinitePlace)) := by
  let D : Type := (v : (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))) → v.val.adicCompletion ℚ
  let _ : Unique D := uniqueOfSubsingleton 0
  let real : Rat.infinitePlace.Completion ≃ᵢ ℝ :=
    InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace
  let coord : SAdeleRing ℚ ∅ ≃ₜ ℝ := (Homeomorph.prodUnique (InfiniteAdeleRing ℚ) D).trans
    ((Homeomorph.piUnique (fun v : InfinitePlace ℚ ↦ v.Completion)).trans real.toHomeomorph)
  let e : Multiplicative (SAdeleRing ℚ ∅) ≃ₜ* Multiplicative ℝ :=
    ContinuousMulEquiv.mk' coord fun x y ↦
      (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).map_add
        (x.toAdd.1 Rat.infinitePlace) (y.toAdd.1 Rat.infinitePlace)
  with_reducible refine realSchwartzBruhat_equiv.elim fun R hR ↦ ?_
  refine ⟨R.trans (schwartzBruhatPullbackEquiv e), ?_⟩
  intro f x
  exact hR f (coord x)

/-- Paper: Example 6.2.2.2, p. 299.
The trivial homogeneous theta space over the rationals is a topological linear
quotient of real Schwartz functions, inserted with the integer indicator at every finite place. -/
theorem ratTrivialHomogeneousTheta_quotient :
    ∃ q : SchwartzMap ℝ ℂ →L[ℂ] GlobalHomogeneousThetaSpace ℚ 1,
      IsOpenQuotientMap q ∧
      ∀ (f : SchwartzMap ℝ ℂ) (g : ℬ(InfiniteAdeleRing ℚ)),
        (∀ x : InfiniteAdeleRing ℚ, g (Multiplicative.ofAdd x) =
          f (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
            (x Rat.infinitePlace))) →
        q f = (LinearMap.ker (homogeneousAdelicThetaLinearMap ℚ 1)).mkQ
          (sAdeleSchwartzToGlobal ℚ ∅ (sLocalStandardThetaTensor (F := ℚ) (S := ∅) 1 g)) := by
  have hω : NormOneCharacterUnramifiedOutside (F := ℚ) 1 ∅ := by
    refine ⟨⟨1, (mem_unramifiedOutside_iff ℚ ∅ 1).mpr (fun _ _ _ ↦ rfl)⟩, fun _ ↦ ?_⟩
    rfl
  with_reducible refine ratTrivialHomogeneousTheta_quotient_realEquiv.elim fun E hE ↦ ?_
  with_reducible refine (sLocalHomogeneousThetaToGlobal_equiv_of_unramified
    (F := ℚ) (S := ∅) (ω := 1) ?_ hω).elim fun T hT ↦ ?_
  · rw [Finset.coe_empty, integer_empty]
    let e := (Algebra.botEquivOfInjective (IsFractionRing.injective (𝓞 ℚ) ℚ)).toRingEquiv
    let i := Rat.ringOfIntegersEquiv.symm.trans e.symm
    let := IsPrincipalIdealRing.of_surjective i i.surjective
    infer_instance
  let K := (sLocalHomogeneousAdelicThetaLinearMap ℚ ∅
    (sLocalNormOneCharacter (F := ℚ) ∅ 1 hω)).ker
  refine ⟨T.toContinuousLinearMap.comp (K.mkQL.comp E.toContinuousLinearMap), ?_, ?_⟩
  · change IsOpenQuotientMap (T.toHomeomorph ∘ (K.mkQL ∘ E.toHomeomorph))
    exact T.toHomeomorph.isOpenQuotientMap.comp
      (K.isOpenQuotientMap_mkQL.comp E.toHomeomorph.isOpenQuotientMap)
  intro f g hg
  have hfg : E f = sLocalStandardThetaTensor (F := ℚ) (S := ∅) 1 g := by
    refine Subtype.ext (funext fun (x : Multiplicative (SAdeleRing ℚ ∅)) ↦ ?_)
    have h := sLocalStandardThetaTensor_apply (F := ℚ) (S := ∅) 1 g x.toAdd
    have ht : sLocalStandardThetaTensor (F := ℚ) (S := ∅) 1 g x =
        g (Multiplicative.ofAdd x.toAdd.1) :=
      h.trans ((congrArg (g (Multiplicative.ofAdd x.toAdd.1) * ·)
        (Fintype.prod_empty _)).trans (mul_one _))
    exact ((hE f x.toAdd).trans (hg x.toAdd.1).symm).trans ht.symm
  let t := sLocalStandardThetaTensor (F := ℚ) (S := ∅) 1 g
  change T.toLinearMap (K.mkQ (E f)) = _
  have hrep := sLocalHomogeneousThetaToGlobal_mk (F := ℚ) (S := ∅) (ω := 1) hω t
  have hglobal := LinearMap.congr_fun hT (K.mkQ t)
  with_reducible exact (congrArg (fun b ↦ T.toLinearMap (K.mkQ b)) hfg).trans (hglobal.trans hrep)

end RiemannMasullo
