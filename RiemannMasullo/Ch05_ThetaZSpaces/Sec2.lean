module

public import RiemannMasullo.Ch05_ThetaZSpaces.Sec1
import all RiemannMasullo.Ch05_ThetaZSpaces.Sec1
import all RiemannMasullo.Ch04_PeriodicSchauderBases.Sec3b
public import RiemannMasullo.AppD_SchwartzBruhat.Sec1d
import all RiemannMasullo.AppA_AlgebraicNT.Sec1
import all RiemannMasullo.AppA_AlgebraicNT.Sec3
import all RiemannMasullo.AppD_SchwartzBruhat.Sec2b
import all RiemannMasullo.Ch02_AdelicTheta.Sec1
import all RiemannMasullo.Ch02_AdelicTheta.Sec2b
import all RiemannMasullo.Ch02_AdelicTheta.Sec3
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.StrongDualPrecompact
import RiemannMasullo.ForMathlib.Analysis.Distribution.SchwartzSpace.ChangeOfVariables
import Mathlib.Data.Finset.Lattice.Union
import all RiemannMasullo.AppC_LCTVS.Sec1
import all RiemannMasullo.AppC_LCTVS.Sec2b
import RiemannMasullo.ForMathlib.Topology.Algebra.Module.StrongDualQuotient
import RiemannMasullo.ForMathlib.Analysis.Normed.Group.InfiniteSum
import RiemannMasullo.ForMathlib.Topology.Algebra.Valued.LocallyConstant

/-! # Structure Theorem I for adelic theta spaces

Masullo, §5.2.1–5.2.2, pp. 230–232. The finite sets index the finite places.
Every S-adelic space below includes all archimedean places.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Topology
open scoped NumberField.AdeleRing NNReal

namespace RiemannMasullo

variable {F : Type*} [Field F] [NumberField F]
variable {S T U : Finset (HeightOneSpectrum (𝓞 F))}

local notation "ℬ𝔽" => SchwartzBruhat (Multiplicative 𝔸[F])
local notation "ℬₛ(" S ")" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "Θ𝔽" => GlobalAdelicThetaSpace F
local notation "Θₛ(" S ")" => SLocalAdelicThetaSpace F S
local notation "K𝔽" => LinearMap.ker (adelicThetaLinearMap F)
local notation "Kₛ(" S ")" => LinearMap.ker (sLocalAdelicTheta F S)
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "Jₛ(" S ")" => SIdeleQuotient F S
local notation "C₁" => MonoidHom.ker (ideleClassNorm F)
local notation "J₁(" S ")" => MonoidHom.ker (sIdeleQuotientNorm F S)

section Topology

-- TODO(paper-gap): On p. 231 the Fréchet quotients of the test-function stages
-- give an LF presentation. Strictness requires control of their induced topologies.
-- See Example C.1.4.6(4) and Corollary C.1.5.13 for the bounded-lifting issue in (5.2.1.4).

/-- The global quotient by the closed theta kernel is an LF-space. -/
theorem globalAdelicThetaSpace_lf : IsLFSpace Θ𝔽 :=
  lfSpace_quotient_properties.2 (lfSpace_quotient_properties.1
    (adeleSchwartz_strictLF (F := F)).2) _ adelicTheta_ker_isClosed

/-- The local quotient by the closed theta kernel is an LF-space. -/
theorem sLocalAdelicThetaSpace_lf : IsLFSpace (Θₛ(S)) :=
  lfSpace_quotient_properties.2 (lfSpace_quotient_properties.1
    (sAdeleSchwartz_strictLF F S)) _ sLocalAdelicTheta_ker_isClosed

private theorem frechet_quotient_of_metrizable_strictLF {E : Type*} [AddCommGroup E]
    [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    (he : IsStrictLFSpace E) (hp : PolynormableSpace ℂ E) (hm : TopologicalSpace.MetrizableSpace E)
    (K : Submodule ℂ E) (hK : IsClosed (K : Set E)) : IsFrechetTVS (E ⧸ K) :=
  isFrechetTVS_quotient ⟨inferInstance, hp, hm, IsStrictLFSpace.completeSpace (E := E) he⟩ K hK

private theorem empty_test_metrizable : TopologicalSpace.MetrizableSpace (ℬₛ(∅)) := by
  classical
  let S : Finset (HeightOneSpectrum (𝓞 F)) := ∅
  let D := (v : S) → v.val.adicCompletion F
  let : IsEmpty S := ⟨fun v ↦ Finset.notMem_empty v.val v.property⟩
  let : Unique D := uniqueOfSubsingleton 0
  let e : Multiplicative (SAdeleRing F S) ≃ₜ* Multiplicative (InfiniteAdeleRing F) :=
    { toMulEquiv := (AddEquiv.prodUnique (M := InfiniteAdeleRing F) (N := D)).toMultiplicative
      continuous_toFun := (continuous_fst : Continuous (Prod.fst : InfiniteAdeleRing F × D → _))
      continuous_invFun := (continuous_id.prodMk continuous_const :
        Continuous (fun x : InfiniteAdeleRing F ↦ (x, (default : D)))) }
  let : T2Space (Multiplicative (InfiniteAdeleRing F)) := inferInstanceAs (T2Space ((v : InfinitePlace F) → v.Completion))
  let : LocallyCompactSpace (Multiplicative (InfiniteAdeleRing F)) := InfiniteAdeleRing.locallyCompactSpace F
  let : T2Space (Multiplicative (SAdeleRing F S)) := e.toHomeomorph.isEmbedding.t2Space
  let : LocallyCompactSpace (Multiplicative (SAdeleRing F S)) := e.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  let T := (schwartzBruhat_congr e).choose
  let J := (archimedeanSchwartzBruhat_equiv (F := F)).choose
  let V := mixedEmbedding.mixedSpace F
  have : (uniformity (SchwartzMap V ℂ)).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_zero]
    infer_instance
  let : TopologicalSpace.MetrizableSpace (SchwartzMap V ℂ) := UniformSpace.metrizableSpace
  exact (T.trans J.symm).toHomeomorph.isEmbedding.metrizableSpace

/-- For the archimedean stage there are no finite coordinates. Its test space is
classical Schwartz space, so the theta quotient by its closed kernel is Fréchet. -/
theorem sLocalAdelicThetaSpace_empty_frechet : IsFrechetTVS (Θₛ(∅)) :=
  frechet_quotient_of_metrizable_strictLF (E := ℬₛ(∅)) (sAdeleSchwartz_strictLF F ∅)
    (show IsNuclearTVS.{0} (ℬₛ(∅)) from sAdeleSchwartz_nuclear F ∅).2.1
    (empty_test_metrizable (F := F)) (Kₛ(∅)) (sLocalAdelicTheta_ker_isClosed (F := F) (S := ∅))

/-- Paper: Theorem 5.2.1.1(1), p. 230.
The S-local theta space is a strict LF-space.
Deviation: The Fréchet stages inherit nuclearity from the separately stated
nuclearity of the whole space under `isNuclearTVS_submodule`. -/
theorem sLocalAdelicThetaSpace_strictLF : IsStrictLFSpace (Θₛ(S)) := by sorry

/-- Paper: Theorem 5.2.1.1(1), p. 230.
The S-local theta quotient is complete. -/
theorem sLocalAdelicThetaSpace_complete :
    @CompleteSpace (Θₛ(S)) (IsTopologicalAddGroup.rightUniformSpace (Θₛ(S))) := by
  exact IsStrictLFSpace.completeSpace (E := (Θₛ(S))) sLocalAdelicThetaSpace_strictLF

/-- Paper: Theorem 5.2.1.1(1), p. 230.
The global theta quotient is nuclear. -/
theorem globalAdelicThetaSpace_nuclear : IsNuclearTVS Θ𝔽 := by
  let : T2Space Θ𝔽 := globalAdelicThetaSpace_t2_of_isClosed adelicTheta_ker_isClosed
  exact isNuclearTVS_quotient (adeleSchwartz_nuclear (F := F)).2 _

/-- Paper: Theorem 5.2.1.1(1), p. 230.
The S-local theta quotient is nuclear. -/
theorem sLocalAdelicThetaSpace_nuclear : IsNuclearTVS (Θₛ(S)) := by
  let : T2Space (Θₛ(S)) := sLocalAdelicThetaSpace_t2_of_isClosed sLocalAdelicTheta_ker_isClosed
  exact isNuclearTVS_quotient (sAdeleSchwartz_nuclear F S) _

section BoundedSets

open Bornology Set
open scoped Pointwise

/-- Each continuous seminorm on a Schwartz space admits finite nets on bounded sets. -/
private theorem totallyBounded_of_schwartz
    {E : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    (hS : IsSchwartzTVS E) {B : Set E} (hB : IsVonNBounded ℂ B) :
    TotallyBounded B := by
  let : PolynormableSpace ℂ E := hS.1
  apply (PolynormableSpace.hasBasis_zero_ball ℂ E).uniformity_of_nhds_zero_swapped.totallyBounded_iff.mpr
  intro p hp
  obtain ⟨V, hV, htotal⟩ := hS.2 p hp
  obtain ⟨r, hr, hsub⟩ := (hB hV).exists_pos
  let c : ℂ := r
  have hBV : B ⊆ c • V := hsub c (by simp [c, abs_of_pos hr])
  let := p.toSeminormedAddCommGroup
  let : UniformSpace E := p.toSeminormedAddCommGroup.toUniformSpace
  have hsmul : LipschitzWith ‖c‖₊ (c • · : E → E) :=
    LipschitzWith.of_dist_le_mul fun x y ↦ by
      rw [dist_eq_norm_sub, dist_eq_norm_sub, ← smul_sub]
      exact (map_smul_eq_mul p c (x - y)).le
  have htotalB : TotallyBounded B :=
    (htotal.image hsmul.uniformContinuous).subset hBV
  obtain ⟨A, hA, hcover⟩ := Metric.totallyBounded_iff.mp htotalB 1 zero_lt_one
  refine ⟨A, hA, fun x hx ↦ ?_⟩
  obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.mp (hcover hx)
  refine mem_iUnion₂.mpr ⟨a, ha, ?_⟩
  change x - a ∈ p.ball 0 1
  rwa [p.sub_mem_ball, add_zero, p.ball_eq_metric]

/-- Bounded sets in the global theta space are totally bounded, independently of
the completeness of its quotient topology. -/
theorem globalAdelicThetaSpace_bounded_totallyBounded {B : Set Θ𝔽} (hB : Bornology.IsVonNBounded ℂ B) :
    @TotallyBounded Θ𝔽 (IsTopologicalAddGroup.rightUniformSpace _) B := by
  let : UniformSpace Θ𝔽 := IsTopologicalAddGroup.rightUniformSpace _
  let : IsUniformAddGroup Θ𝔽 := isUniformAddGroup_of_addCommGroup
  exact totallyBounded_of_schwartz (isSchwartzTVS_of_isNuclearTVS.{0} (globalAdelicThetaSpace_nuclear (F := F))) hB

/-- Bounded sets in every finite theta quotient are totally bounded. -/
theorem sLocalAdelicThetaSpace_bounded_totallyBounded {B : Set (Θₛ(S))} (hB : Bornology.IsVonNBounded ℂ B) :
    @TotallyBounded (Θₛ(S)) (IsTopologicalAddGroup.rightUniformSpace _) B := by
  let : UniformSpace (Θₛ(S)) := IsTopologicalAddGroup.rightUniformSpace _
  let : IsUniformAddGroup (Θₛ(S)) := isUniformAddGroup_of_addCommGroup
  exact totallyBounded_of_schwartz (isSchwartzTVS_of_isNuclearTVS.{0} (sLocalAdelicThetaSpace_nuclear (F := F) (S := S))) hB

end BoundedSets

/-- Paper: Theorem 5.2.1.1(1), p. 230.
The global theta quotient is barrelled. -/
theorem globalAdelicThetaSpace_barrelled : BarrelledSpace ℂ Θ𝔽 :=
  IsLFSpace.barrelled (E := Θ𝔽) globalAdelicThetaSpace_lf

/-- Paper: Theorem 5.2.1.1(1), p. 230.
The S-local theta quotient is barrelled. -/
theorem sLocalAdelicThetaSpace_barrelled : BarrelledSpace ℂ (Θₛ(S)) :=
  IsLFSpace.barrelled (E := Θₛ(S)) sLocalAdelicThetaSpace_lf

/-- Paper: Theorem 5.2.1.1(1), p. 230.
Closed bounded subsets are compact in the S-local theta quotient. -/
theorem sLocalAdelicThetaSpace_montel : MontelSpace ℂ (Θₛ(S)) := montelSpace_of_nuclear_strictLF.{0} sLocalAdelicThetaSpace_strictLF
    sLocalAdelicThetaSpace_nuclear

/-- Paper: Theorem 5.2.1.1(1), p. 230.
The strong dual of the global theta quotient is complete. -/
theorem globalAdelicThetaSpace_strongDual_complete : CompleteSpace (StrongDual ℂ Θ𝔽) := by
  let : CompleteSpace (StrongDual ℂ ℬ𝔽) := (adeleSchwartz_strongDual_complete (F := F)).2
  exact completeSpace_strongDual_quotient _

/-- Paper: Theorem 5.2.1.1(1), p. 230.
The strong dual of the S-local theta quotient is complete. -/
theorem sLocalAdelicThetaSpace_strongDual_complete : CompleteSpace (StrongDual ℂ (Θₛ(S))) := by
  let : CompleteSpace (StrongDual ℂ (ℬₛ(S))) := sAdeleSchwartz_strongDual_complete F S
  exact completeSpace_strongDual_quotient _

private theorem isEmbedding_transpose_quotient_of_strictLF {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    (K : Submodule ℂ E)
    (hE : IsStrictLFSpace E) (hN : IsNuclearTVS.{0} E) (hK : IsClosed (K : Set E))
    (hQ : IsStrictLFSpace (E ⧸ K)) : IsEmbedding (fun l : StrongDual ℂ (E ⧸ K) ↦ l.comp K.mkQL) := by
  let := hN.1
  let := hQ.1
  obtain ⟨_, V, hV, hF, hex, ht⟩ := hE
  let j (n : ℕ) := (V n).subtypeL.codRestrict (V (n+1)) fun x ↦ hV n.le_succ x.property
  have hj (n : ℕ) : IsEmbedding (j n) :=
    IsEmbedding.of_comp (j n).continuous continuous_subtype_val IsEmbedding.subtypeVal
  have hlim : IsInjectiveLCLimit j (fun n ↦ (V n).subtypeL) := by
    refine ⟨fun _ ↦ Subtype.val_injective, fun _ ↦ rfl, fun x ↦ ?_, ht⟩
    obtain ⟨n, hn⟩ := hex x
    exact ⟨n, ⟨x, hn⟩, rfl⟩
  have hlift := (liftsBoundedSets_quotient_of_nuclear_strictLF hlim hj hF
    (fun n ↦ isNuclearTVS_submodule hN (V n)) K hK hQ (isNuclearTVS_quotient hN K)).1
  let R : StrongDual ℂ (E ⧸ K) →L[ℂ] StrongDual ℂ E := ContinuousLinearMap.precomp ℂ K.mkQL
  change IsEmbedding R
  constructor
  · apply IsTopologicalAddGroup.isInducing_iff_nhds_zero.mpr
    refine le_antisymm (map_le_iff_le_comap.mp ?_) ?_
    · simpa only [Tendsto, map_zero] using R.continuous.tendsto 0
    · apply ContinuousLinearMap.hasBasis_nhds_zero.ge_iff.mpr
      rintro ⟨B, U⟩ ⟨hB, hU⟩
      obtain ⟨A, hA, hBA⟩ := hlift B hB
      refine mem_comap.mpr ⟨{l : StrongDual ℂ E | Set.MapsTo l A U},
        ContinuousLinearMap.eventually_nhds_zero_mapsTo hA hU, ?_⟩
      intro l hl b hb
      obtain ⟨a, ha, rfl⟩ := hBA hb
      exact hl ha
  · intro l m he
    ext x
    obtain ⟨a, rfl⟩ := K.mkQ_surjective x
    exact DFunLike.congr_fun he a

universe v

private theorem nuclear_of_linear_embedding {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] (i : X →L[ℂ] Y)
    (hi : IsEmbedding i) (hY : IsNuclearTVS.{v} Y) : IsNuclearTVS.{v} X := by
  let : PolynormableSpace ℂ Y := hY.2.1
  have : PolynormableSpace ℂ X := hi.eq_induced ▸ PolynormableSpace.induced i.toLinearMap
  let e := LinearEquiv.ofInjective i.toLinearMap hi.injective
  have he : IsInducing e := IsInducing.subtypeVal.of_comp_iff.mp hi.isInducing
  let h := e.toEquiv.toHomeomorphOfIsInducing he
  let L : X ≃L[ℂ] i.toLinearMap.range := ⟨e, h.continuous, h.continuous_symm⟩
  exact nuclear_of_equiv L.symm (isNuclearTVS_submodule hY _)

/-- Paper: Theorem 5.2.1.1(1), p. 230.
The strong dual of the S-local theta quotient is nuclear. -/
theorem sLocalAdelicThetaSpace_strongDual_nuclear : IsNuclearTVS (StrongDual ℂ (Θₛ(S))) := by
  apply nuclear_of_linear_embedding (ContinuousLinearMap.precomp ℂ (Kₛ(S)).mkQL)
  · exact isEmbedding_transpose_quotient_of_strictLF _ (sAdeleSchwartz_strictLF F S)
      (sAdeleSchwartz_nuclear F S) sLocalAdelicTheta_ker_isClosed sLocalAdelicThetaSpace_strictLF
  · exact (sAdeleSchwartz_strongDual_nuclear F S)

private theorem barrelled_strongDual_of_montel {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    [PolynormableSpace ℂ E] [T2Space E] [MontelSpace ℂ E] : BarrelledSpace ℂ (StrongDual ℂ E) := by
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  apply barrelled_of_barrel_nbhd
  apply strongDual_barrel_nbhd
  intro l
  obtain ⟨x, rfl⟩ := surjective_strongBidual_eval l
  exact ⟨x, fun _ ↦ rfl⟩

/-- Paper: Theorem 5.2.1.1(1), p. 230.
The strong dual of the S-local theta quotient is barrelled. -/
theorem sLocalAdelicThetaSpace_strongDual_barrelled :
    BarrelledSpace ℂ (StrongDual ℂ (Θₛ(S))) := by
    let : T2Space (Θₛ(S)) := (sLocalAdelicThetaSpace_lf (F := F) (S := S)).1
    let : PolynormableSpace ℂ (Θₛ(S)) := sLocalAdelicThetaSpace_polynormable
    let : MontelSpace ℂ (Θₛ(S)) := sLocalAdelicThetaSpace_montel
    exact barrelled_strongDual_of_montel

/-- Paper: Theorem 5.2.1.1(1), p. 230.
Closed bounded subsets are compact in the strong dual of the S-local theta quotient. -/
theorem sLocalAdelicThetaSpace_strongDual_montel : MontelSpace ℂ (StrongDual ℂ (Θₛ(S))) := by
  let : UniformSpace (Θₛ(S)) := IsTopologicalAddGroup.rightUniformSpace _
  let : IsUniformAddGroup (Θₛ(S)) := isUniformAddGroup_of_addCommGroup
  let : BarrelledSpace ℂ (Θₛ(S)) := sLocalAdelicThetaSpace_barrelled (F := F) (S := S)
  exact montelSpace_strongDual_of_precompact (fun _ hb ↦ sLocalAdelicThetaSpace_bounded_totallyBounded (F := F) (S := S) hb)

/-- On every family bounded after pullback, the global theta transpose is an
embedding for bounded convergence. This does not require strictness of the quotient. -/
theorem globalThetaQuotient_transpose_isEmbedding_of_bounded_image (B : Set (StrongDual ℂ Θ𝔽))
    (hB : Bornology.IsVonNBounded ℂ ((fun l : StrongDual ℂ Θ𝔽 ↦ l.comp (K𝔽).mkQL) '' B)) :
    IsEmbedding (fun l : B ↦ l.val.comp (K𝔽).mkQL) := by
  let : UniformSpace Θ𝔽 := IsTopologicalAddGroup.rightUniformSpace _
  let : IsUniformAddGroup Θ𝔽 := isUniformAddGroup_of_addCommGroup
  let : BarrelledSpace ℂ Θ𝔽 := globalAdelicThetaSpace_barrelled (F := F)
  exact isEmbedding_transpose_of_bounded_image (K𝔽).mkQL (K𝔽).mkQ_surjective
    (fun _ hb ↦ globalAdelicThetaSpace_bounded_totallyBounded (F := F) hb) B hB

/-- In bounded convergence the transpose has closed range independently of strictness. -/
theorem globalThetaQuotient_transpose_isClosed_range :
    IsClosed (Set.range (fun l : StrongDual ℂ Θ𝔽 ↦ l.comp (K𝔽).mkQL)) :=
  isClosed_range_transpose_mkQL _

end Topology

-- TODO(paper-gap): Footnote 1 on p. 230 asks for a version with an
-- I-exponentially decaying target without giving a statement.
-- TODO(paper-gap): Footnote 2 on p. 231 asks to adjust Theorem 5.2.1.1
-- and gives no replacement. Its proof needs a stage projection preserving
-- the theta kernel. For ℚ and S = {∞}, put e = 1_{ℤ̂}. Every tail functional
-- fixing e sends f − ρ(2)f, for f = φ ⊗ e, to (φ − c φ(·/2)) ⊗ e for some c.
-- For an even bump φ supported within 1/4 of ±1 with φ(±1) = 1, this has
-- theta values 2(1−c) and −2c at real scales 1 and 2. Thus the tensor
-- projections used on p. 73 cannot descend. The assertion on p. 232 about
-- convergence on bounded sets requires a family of projections on the quotients.

section Transitions

section KernelDescent

open Set

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "I" => IdeleGroup (𝓞 F) F
local notation "A" => 𝔸[F]
local notation "O(" v ")" => HeightOneSpectrum.adicCompletionIntegers F v
local notation "Uₛ(" S ")" => (Set.integer (S : Set V) F)ˣ
local notation "Aₛ(" S ")" => integralAdelesOutside F S

private theorem mul_integralUnit_mem_iff {R : Type*} [CommRing R] {D : Subring R} (u : Dˣ) (x : R) :
    u.val.val * x ∈ D ↔ x ∈ D := by
  constructor
  · intro h
    have hh := D.mul_mem u.inv.property h
    rwa [← mul_assoc, show u.inv.val * u.val.val = 1 from congrArg Subtype.val u.inv_val, one_mul] at hh
  · exact D.mul_mem u.val.property

private theorem toGlobal_apply_integral (f : ℬₛ(S)) (x : 𝔸[F]) :
    sAdeleSchwartzToGlobal F S f (Multiplicative.ofAdd x) =
      open Classical in if x ∈ Aₛ(S) then f (Multiplicative.ofAdd (adeleProjection F S x)) else 0 := by
  classical
  have hi : x ∈ integralAdelesOutside F S ↔ ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S →
      x.2 v ∈ v.adicCompletionIntegers F := by
    simp only [integralAdelesOutside, Subring.mem_iInf]
    rfl
  exact (sAdeleSchwartzToGlobal_apply F S f x).trans
    (if_congr hi.symm rfl rfl)

/-- On a fixed coset of the S-units, outside integrality holds everywhere or nowhere.
In the first case its sum is the local theta value at the projected idele. -/
private theorem thetaSum_zero_globalInsert (S : Finset (HeightOneSpectrum (𝓞 F))) (f : ℬₛ(S))
    (hf : sLocalAdelicTheta F S f = 0) (g : IdeleGroup (𝓞 F) F) :
    adelicTheta (sAdeleSchwartzToGlobal F S f) (QuotientGroup.mk g) = 0 := by
  classical
  let d := Units.map ((S : Set (HeightOneSpectrum (𝓞 F))).integer F).subtype.toMonoidHom
  let diag := Units.map (algebraMap F 𝔸[F]).toMonoidHom
  let a (t : Fˣ) := sAdeleSchwartzToGlobal F S f (Multiplicative.ofAdd ((diag t).val * g.val))
  have hd : Injective d := fun x y h ↦ Units.ext (Subtype.ext (congrArg Units.val h))
  have ha : Summable (fun t : Fˣ ↦ sAdeleSchwartzToGlobal F S f
      (Multiplicative.ofAdd (algebraMap F 𝔸[F] t.val * g.val))) := by
    have h := ((adelicAverage_summableUniformlyOn (sAdeleSchwartzToGlobal F S f)
      {(g, 0)} isCompact_singleton).summable rfl).of_norm
    exact h.congr fun t ↦ congrArg (fun x ↦ sAdeleSchwartzToGlobal F S f (Multiplicative.ofAdd x))
      ((congrArg (g.val * ·) (add_zero _)).trans (mul_comm _ _))
  refine (adelicTheta_mk (sAdeleSchwartzToGlobal F S f) g).trans
    (tsum_zero_of_cosets (a := a) d hd ha (fun t ↦ ?_))
  let y := diag t * g
  let G := Units.map (integralAdeleDiagonal F S).toMonoidHom
  let proj := Units.map (adeleProjection F S).toMonoidHom
  let ψ (u : Uₛ(S)) := f (Multiplicative.ofAdd (adeleProjection F S ((G u).val.val * y.val)))
  have hterm (u : Uₛ(S)) : a (t * d u) =
      if y.val ∈ Aₛ(S) then ψ u else 0 := by
    have hm : (diag (t * d u)).val * g.val = (G u).val.val * y.val := by
      change algebraMap F 𝔸[F] (t.val * (d u).val) * g.val =
        algebraMap F 𝔸[F] (d u).val * (algebraMap F 𝔸[F] t.val * g.val)
      exact (congrArg (· * g.val) (map_mul (algebraMap F 𝔸[F]) _ _)).trans ((mul_assoc _ _ _).trans (mul_left_comm _ _ _))
    refine (congrArg (fun w ↦ sAdeleSchwartzToGlobal F S f (Multiplicative.ofAdd w)) hm).trans ?_
    exact (toGlobal_apply_integral f ((G u).val.val * y.val)).trans
      (if_congr (mul_integralUnit_mem_iff (G u) y.val) rfl rfl)
  refine (tsum_congr hterm).trans ?_
  by_cases hy : y.val ∈ Aₛ(S)
  · have localSum : ∑' u, ψ u = sLocalAdelicTheta F S f (proj y) := by
      exact tsum_congr fun u ↦ congrArg (fun x ↦ f (Multiplicative.ofAdd x))
        (map_mul (adeleProjection F S) (G u).val.val y.val)
    refine (tsum_congr (fun u ↦ ite_eq_left (t := ψ u) hy)).trans ?_
    exact localSum.trans (congrArg (fun φ : C((SAdeleRing F S)ˣ, ℂ) ↦ φ (proj y)) hf)
  · exact (tsum_congr fun u ↦ ite_eq_right (t := ψ u) hy).trans tsum_zero

/-- Paper: Theorem 5.2.1.1(3), p. 230.
The global insertion of a test function sends the corresponding S-local theta kernel
into the global theta kernel. -/
theorem sLocalThetaToGlobal_preserves_kernel :
    Kₛ(S) ≤ (K𝔽).comap (sAdeleSchwartzToGlobal F S) := by
  intro f hf
  change adelicThetaLinearMap F (sAdeleSchwartzToGlobal F S f) = 0
  refine ContinuousMap.ext fun q ↦ ?_
  exact QuotientGroup.induction_on q (thetaSum_zero_globalInsert S f hf)

open Classical in
/-- Prescribe a finite set of strict valuation cutoffs outside S. -/
private theorem exists_cutIdele (S : Finset V) (B : Finset {v : V // v ∉ S}) :
    ∃ z : I, adeleProjection F S z.val = 1 ∧
      ∀ (v : V) (hv : v ∉ S) (t : Fˣ),
        ((algebraMap F A (t : F)).2 v * z.val.2 v ∈ O(v)) ↔
          if (⟨v, hv⟩ : {v : V // v ∉ S}) ∈ B then v.valuation F t.val < 1
          else v.valuation F t.val ≤ 1 := by
  classical
  choose b hb using fun v : V ↦ (v.valuation_surjective F (WithZero.exp (1 : ℤ)))
  have hb0 (v : V) : b v ≠ 0 := by
    intro h
    simpa [h] using (hb v).symm
  let β (v : V) := Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom (Units.mk0 (b v) (hb0 v))
  let B' := B.image Subtype.val
  let a (v : V) : (v.adicCompletion F)ˣ := if v ∈ B' then β v else 1
  let zFin : (FiniteAdeleRing (𝓞 F) F)ˣ :=
    { val := ⟨fun v ↦ (a v).val, by
        filter_upwards [B'.finite_toSet.compl_mem_cofinite] with v hv
        simp [a, show v ∉ B' from hv]⟩
      inv := ⟨fun v ↦ (a v).inv, by
        filter_upwards [B'.finite_toSet.compl_mem_cofinite] with v hv
        simp [a, show v ∉ B' from hv]⟩
      val_inv := by ext1 v; exact (a v).val_inv
      inv_val := by ext1 v; exact (a v).inv_val }
  let z : I := (MulEquiv.prodUnits ..).symm (1, zFin)
  refine ⟨z, Prod.ext rfl (funext fun v ↦ ?_), fun v hv t ↦ ?_⟩
  · have h : v.val ∉ B' := by
      rintro h
      obtain ⟨w, _, hw⟩ := Finset.mem_image.mp h
      exact w.property (hw ▸ v.property)
    change (a v.val).val = 1
    simp [a, h]
  · change Valued.v (((t : F) : v.adicCompletion F) * (a v).val) ≤ 1 ↔ _
    rw [map_mul, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    by_cases h : (⟨v, hv⟩ : {v : V // v ∉ S}) ∈ B
    · have hvB : v ∈ B' := Finset.mem_image_of_mem Subtype.val h
      simp only [ite_eq_left h, a, ite_eq_left hvB]
      change v.valuation F t.val * Valued.v ((b v : F) : v.adicCompletion F) ≤ 1 ↔ _
      rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hb]
      have ht : v.valuation F t.val ≠ 0 := by simp
      rw [← WithZero.exp_log ht, ← WithZero.exp_add, ← WithZero.exp_zero (M := ℤ)]
      simp only [WithZero.exp_le_exp, WithZero.exp_lt_exp]
      omega
    · have hvB : v ∉ B' := by
        rintro hx
        obtain ⟨w, hw, heq⟩ := Finset.mem_image.mp hx
        exact h ((Subtype.ext heq : w = ⟨v, hv⟩) ▸ hw)
      simp [a, hvB, h]

private theorem outsideCut_iff {ι : Type*} {L : Type*} [PartialOrder L] [One L]
    [DecidableEq ι] (B : Finset ι) (v : ι → L) :
     (∀ i, if i ∈ B then v i < 1 else v i ≤ 1) ↔
      (∀ i, v i ≤ 1) ∧ ∀ i ∈ B, v i < 1 := by
  classical
  constructor
  · intro h
    refine ⟨fun i ↦ ?_, fun i hi ↦ by simpa only [ite_eq_left hi] using h i⟩
    by_cases hi : i ∈ B
    · exact (show v i < 1 from by simpa only [ite_eq_left hi] using h i).le
    · simpa only [ite_eq_right hi] using h i
  · rintro ⟨ha,hb⟩ i
    split_ifs with hi
    · exact hb i hi
    · exact ha i

/-- Evaluating an inserted test at a shifted idele selects a finite intersection of valuation cutoffs. -/
private theorem cutIdeleTest_eval {S : Finset V} (f : SchwartzBruhat (Multiplicative (SAdeleRing F S)))
    (g : (SAdeleRing F S)ˣ) (B : Finset {v : V // v ∉ S}) :
    open Classical in ∃ z : I, ∀ t : Fˣ,
      sAdeleSchwartzToGlobal F S f (Multiplicative.ofAdd (algebraMap F A t.val * z.val)) =
      if ∀ v ∈ B, v.val.valuation F t.val < 1 then
        if ∀ v : {v : V // v ∉ S}, v.val.valuation F t.val ≤ 1 then
          f (Multiplicative.ofAdd (adeleProjection F S (algebraMap F A t.val) * g.val))
        else 0 else 0 := by
  classical
  let g₀ := sIdeleInsertion F S g
  have hproj : adeleProjection F S g₀.val = g.val :=
    Prod.ext (sIdeleInsertion_apply F S g).1 (funext (sIdeleInsertion_apply F S g).2.1)
  refine (exists_cutIdele (F := F) S B).elim fun z ⟨hzs, hz⟩ ↦ ⟨g₀ * z, fun t ↦ ?_⟩
  let x := algebraMap F A t.val
  have hcoord (v : V) (hv : v ∉ S) :
      (x * (g₀ * z).val).2 v = x.2 v * z.val.2 v := by
    change x.2 v * (g₀.val.2 v * z.val.2 v) = _
    exact congrArg (x.2 v * ·) ((congrArg (· * z.val.2 v) ((sIdeleInsertion_apply F S g).2.2 v hv)).trans (one_mul _))
  have hint : (∀ v : V, v ∉ S → (x * (g₀ * z).val).2 v ∈ O(v)) ↔
      (∀ v : {v : V // v ∉ S}, v.val.valuation F t.val ≤ 1) ∧
        ∀ v ∈ B, v.val.valuation F t.val < 1 := by
    refine Iff.trans ?_ (outsideCut_iff B fun v ↦ v.val.valuation F t.val)
    constructor
    · intro h v
      exact (hz v.val v.property t).mp (hcoord v.val v.property ▸ h v.val v.property)
    · intro h v hv
      exact (hcoord v hv).symm ▸ (hz v hv t).mpr (h ⟨v, hv⟩)
  have hxs : adeleProjection F S (x * (g₀ * z).val) = adeleProjection F S x * g.val := by
    calc
      _ = adeleProjection F S x * (adeleProjection F S g₀.val * adeleProjection F S z.val) :=
        ((map_mul (adeleProjection F S) x (g₀.val * z.val))).trans
          (congrArg (_ * ·) (map_mul (adeleProjection F S) g₀.val z.val))
      _ = _ := congrArg (adeleProjection F S x * ·)
        ((congrArg₂ (· * ·) hproj hzs).trans (mul_one _))
  refine (sAdeleSchwartzToGlobal_apply F S f (x * (g₀ * z).val)).trans ?_
  refine (if_congr hint (congrArg (fun y ↦ f (Multiplicative.ofAdd y)) hxs) rfl).trans ?_
  split_ifs <;> tauto

/-- Finite exclusion followed by dominated convergence leaves exactly the S-units. -/
private theorem localSum_of_globalKernel {S : Finset V} (f : SchwartzBruhat (Multiplicative (SAdeleRing F S)))
    (hf : sAdeleSchwartzToGlobal F S f ∈ LinearMap.ker (adelicThetaLinearMap F)) :
    ∀ g : (SAdeleRing F S)ˣ, sLocalAdelicTheta F S f g = 0 := by
  classical
  intro g
  let W := {v : V // v ∉ S}
  let ok (t : Fˣ) := ∀ v : W, v.val.valuation F t.val ≤ 1
  let P (v : W) (t : Fˣ) := v.val.valuation F t.val < 1
  let b (t : Fˣ) := f (Multiplicative.ofAdd
    (adeleProjection F S (algebraMap F A t.val) * g.val))
  let a (t : Fˣ) := if ok t then b t else 0
  have hterm (B : Finset W) : ∃ z : I, ∀ t : Fˣ,
      sAdeleSchwartzToGlobal F S f (Multiplicative.ofAdd (algebraMap F A t.val * z.val)) =
        if ∀ v ∈ B, P v t then a t else 0 := cutIdeleTest_eval f g B
  let z (B : Finset W) := (hterm B).choose
  have hz (B : Finset W) := (hterm B).choose_spec
  have hsum : Summable (fun t ↦ ‖a t‖) := by
    have he (t : Fˣ) :
        sAdeleSchwartzToGlobal F S f (Multiplicative.ofAdd (algebraMap F A t.val * (z ∅).val)) = a t :=
      (hz ∅ t).trans (ite_eq_left (by simp))
    have H := (adelicAverage_summableUniformlyOn (sAdeleSchwartzToGlobal F S f)
      {(z ∅, 0)} isCompact_singleton).summable rfl
    change Summable (fun t : Fˣ ↦ ‖sAdeleSchwartzToGlobal F S f
      (Multiplicative.ofAdd ((z ∅).val * (algebraMap F A t.val + 0)))‖) at H
    exact H.congr fun t ↦ congrArg norm ((congrArg (fun y ↦ sAdeleSchwartzToGlobal F S f (Multiplicative.ofAdd y))
      ((congrArg ((z ∅).val * ·) (add_zero _)).trans (mul_comm _ _))).trans (he t))
  have hzero (B : Finset W) : (∑' t, if ∀ v ∈ B, P v t then a t else 0) = 0 := by
    have h := congrArg (fun φ : C(IdeleClassGroup (𝓞 F) F, ℂ) ↦ φ (QuotientGroup.mk (z B)))
      (show adelicThetaLinearMap F (sAdeleSchwartzToGlobal F S f) = 0 from hf)
    exact (tsum_congr (hz B)).symm.trans ((adelicTheta_mk (sAdeleSchwartzToGlobal F S f) (z B)).symm.trans h)
  have hall := tsum_avoiding_of_tsum_intersections a P hsum hzero
  let H := (S : Set V).unit F
  have hsel (t : Fˣ) : (if ∀ v, ¬ P v t then a t else 0) =
      (H : Set Fˣ).indicator b t := by
    have heq : t ∈ H ↔ ok t ∧ ∀ v, ¬ P v t := by
      constructor
      · intro ht
        exact ⟨fun v ↦ (ht v.val v.property).le, fun v ↦ (ht v.val v.property).ge.not_gt⟩
      · rintro ⟨h₁, h₂⟩ v hv
        exact le_antisymm (h₁ ⟨v, hv⟩) (not_lt.mp (h₂ ⟨v, hv⟩))
    by_cases ht : t ∈ H
    · simp [indicator_of_mem ht, a, (heq.mp ht).1, (heq.mp ht).2]
    · rw [indicator_of_notMem ht]
      unfold a
      split_ifs <;> tauto
  rw [tsum_congr hsel, ← tsum_subtype] at hall
  let e := (Set.unitEquivUnitsInteger (S : Set V) F).symm
  exact (e.tsum_eq (fun u ↦ b u.val)).trans hall

/-- An inserted test of zero global theta already has zero S-local theta. -/
theorem sLocalThetaToGlobal_reflects_kernel :
    (K𝔽).comap (sAdeleSchwartzToGlobal F S) ≤ Kₛ(S) := by
  intro f hf
  exact ContinuousMap.ext (localSum_of_globalKernel f hf)

/-- Paper: Theorem 5.2.1.1(2), p. 230.
Schwartz–Bruhat transition sends the S-local theta kernel into the T-local theta kernel. -/
theorem sLocalThetaTransition_preserves_kernel (hST : S ⊆ T) :
    Kₛ(S) ≤ (Kₛ(T)).comap (sAdeleSchwartzTransition F hST) := by
  intro f hf
  apply sLocalThetaToGlobal_reflects_kernel (S := T)
  have h := DFunLike.congr_fun (sAdeleSchwartzToGlobal_comp F hST) f
  exact (congrArg (fun z : ℬ𝔽 ↦ z ∈ K𝔽) h).mpr
    (sLocalThetaToGlobal_preserves_kernel (S := S) hf)

/-- Paper: (5.2.1.1), p. 230.
The transition on theta quotients is induced by the Schwartz–Bruhat stage transition. -/
def sLocalThetaTransition (hST : S ⊆ T) : Θₛ(S) →ₗ[ℂ] Θₛ(T) :=
  (Kₛ(S)).mapQ (Kₛ(T)) (sAdeleSchwartzTransition F hST)
    (sLocalThetaTransition_preserves_kernel hST)

private theorem localCut_eval {S T : Finset V} (hST : S ⊆ T) (g : (SAdeleRing F S)ˣ)
    (B : Finset {w : T // w.val ∉ S}) :
    open Classical in ∃ y : (SAdeleRing F T)ˣ, ∀ (f : ℬₛ(S)) (t : Fˣ),
      sAdeleSchwartzTransition F hST f (Multiplicative.ofAdd
        (adeleProjection F T (algebraMap F A t.val) * y.val)) =
      if ∀ w ∈ B, w.val.val.valuation F t.val < 1 then
        if ∀ w : {w : T // w.val ∉ S}, w.val.val.valuation F t.val ≤ 1 then
          f (Multiplicative.ofAdd (adeleProjection F S (algebraMap F A t.val) * g.val))
        else 0 else 0 := by
  classical
  let W := {w : T // w.val ∉ S}
  let cast (w : W) : {v : V // v ∉ S} := ⟨w.val.val, w.property⟩
  let B' := B.image cast
  have hB (w : W) : cast w ∈ B' ↔ w ∈ B := by
    refine ⟨fun h ↦ ?_, Finset.mem_image_of_mem cast⟩
    obtain ⟨q,hq,he⟩ := Finset.mem_image.mp h
    have hv : q.val.val = w.val.val :=
      congrArg (fun v : {v : V // v ∉ S} ↦ v.val) he
    exact (show q = w from Subtype.ext (Subtype.ext hv)) ▸ hq
  let z := (exists_cutIdele (F := F) S B').choose
  have hs := (exists_cutIdele (F := F) S B').choose_spec.1
  have hz := (exists_cutIdele (F := F) S B').choose_spec.2
  let g₀ := sIdeleInsertion F S g
  let y := Units.map (adeleProjection F T).toMonoidHom (g₀ * z)
  have hg₀ : adeleProjection F S g₀.val = g.val :=
    Prod.ext (sIdeleInsertion_apply F S g).1 (funext (sIdeleInsertion_apply F S g).2.1)
  have hy : adeleProjection F S (g₀.val * z.val) = g.val :=
    (map_mul (adeleProjection F S) _ _).trans ((congrArg₂ (· * ·) hg₀ hs).trans (mul_one _))
  refine ⟨y, fun f t ↦ ?_⟩
  let x := algebraMap F A t.val
  let xT := adeleProjection F T x * y.val
  have hS : (xT.1, fun w : S ↦ xT.2 ⟨w.val, hST w.property⟩) =
      adeleProjection F S x * g.val :=
    congrArg (adeleProjection F S x * ·) hy
  have hcoord (w : W) : xT.2 w.val = x.2 w.val.val * z.val.2 w.val.val :=
    congrArg (x.2 w.val.val * ·) ((congrArg (· * z.val.2 w.val.val)
      ((sIdeleInsertion_apply F S g).2.2 w.val.val w.property)).trans (one_mul _))
  have hint (w : W) : xT.2 w.val ∈ O(w.val.val) ↔
      if w ∈ B then w.val.val.valuation F t.val < 1 else w.val.val.valuation F t.val ≤ 1 := by
    exact (hcoord w).symm ▸ ((hz w.val.val w.property t).trans
      (Iff.of_eq (if_congr (hB w) rfl rfl)))
  have hcut : (∀ w : T, w.val ∉ S → xT.2 w ∈ O(w.val)) ↔
      (∀ w : W, w.val.val.valuation F t.val ≤ 1) ∧ ∀ w ∈ B, w.val.val.valuation F t.val < 1 := by
    refine Iff.trans ?_ (outsideCut_iff B fun w ↦ w.val.val.valuation F t.val)
    exact ⟨fun h w ↦ (hint w).mp (h w.val w.property),
      fun h w hw ↦ (hint ⟨w,hw⟩).mpr (h ⟨w,hw⟩)⟩
  refine (sAdeleSchwartzTransition_apply F hST f xT).trans
    ((if_congr hcut (congrArg (fun q ↦ f (Multiplicative.ofAdd q)) hS) rfl).trans ?_)
  split_ifs <;> tauto

/-- A continuous point evaluation of a linear transform descends to its kernel quotient. -/
def thetaQuotientEval {X Q : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [TopologicalSpace Q] (θ : X →ₗ[ℂ] C(Q, ℂ)) (a : Q) (hc : Continuous (fun f ↦ θ f a)) :
    StrongDual ℂ (X ⧸ θ.ker) := by
  let l : X →L[ℂ] ℂ := ⟨(ContinuousMap.evalCLM ℂ a).toLinearMap.comp θ, hc⟩
  exact θ.ker.liftQL l fun f h ↦ congrArg (fun φ : C(Q, ℂ) ↦ φ a) (LinearMap.mem_ker.mp h)

/-- Each S-local theta evaluation is continuous on the Schwartz–Bruhat test space. -/
theorem sLocalAdelicTheta_continuous_eval {S : Finset V} (g : (SAdeleRing F S)ˣ) :
    Continuous (fun f ↦ sLocalAdelicTheta F S f g) := by
  let : BarrelledSpace ℂ (ℬₛ(S)) := (sAdeleSchwartz_montel (F := F) S).1
  let : Countable F := Countable.of_moduleFinite (R := ℚ)
  let : Countable (Set.integer (S : Set (HeightOneSpectrum (𝓞 F))) F)ˣ := Units.val_injective.countable
  exact schwartzBruhat_continuous_of_hasSum _ _ fun f ↦
    (sLocalAdelicTheta_hasSumUniformlyOn F S f {g} isCompact_singleton).hasSum rfl

private theorem localTheta_indicator_hasSum (S : Finset V) (f : ℬₛ(S)) (y : (SAdeleRing F S)ˣ) :
    HasSum (((S : Set V).unit F : Set Fˣ).indicator (fun t ↦
      f (Multiplicative.ofAdd (adeleProjection F S (algebraMap F A t.val) * y.val))))
      (sLocalAdelicTheta F S f y) := by
  let e := (Set.unitEquivUnitsInteger (S : Set V) F).symm
  apply hasSum_subtype_iff_indicator.mp
  exact (e.toEquiv.hasSum_iff).mp ((sLocalAdelicTheta_hasSumUniformlyOn F S f {y} isCompact_singleton).hasSum rfl)

private theorem units_in_smaller_stage {S T : Finset V} (hST : S ⊆ T) (t : Fˣ) :
    t ∈ (S : Set V).unit F ↔ t ∈ (T : Set V).unit F ∧
      ∀ w : {w : T // w.val ∉ S}, w.val.val.valuation F t.val = 1 := by
  refine ⟨fun h ↦ ⟨fun v hv ↦ h v (fun h ↦ hv (hST h)), fun w ↦ h w.val.val w.property⟩, ?_⟩
  intro ⟨ht,hw⟩ v hv
  by_cases hT : v ∈ T
  · exact hw ⟨⟨v,hT⟩,hv⟩
  · exact ht v hT

private theorem cutoff_indicator {W α : Type*} [Fintype W]
    (H K : Set α) (v : W → α → WithZero (Multiplicative ℤ)) (b : α → ℂ)
    (h : ∀ t, t ∈ H ↔ t ∈ K ∧ ∀ w, v w t = 1) (t : α) :
    open Classical in
    (if ∀ w, ¬ v w t < 1 then
      K.indicator (fun s ↦ if ∀ w, v w s ≤ 1 then b s else 0) t else 0) = H.indicator b t := by
  classical
  by_cases ht : t ∈ H
  · obtain ⟨hK,hv⟩ := (h t).mp ht
    simp [Set.indicator_of_mem ht, Set.indicator_of_mem hK, hv]
  · rw [Set.indicator_of_notMem ht]
    by_cases hK : t ∈ K
    · rw [Set.indicator_of_mem hK]
      split_ifs with h₁ h₂
      · exact (ht ((h t).mpr ⟨hK, fun w ↦ le_antisymm (h₂ w) (not_lt.mp (h₁ w))⟩)).elim
      all_goals rfl
    · simp only [Set.indicator_of_notMem hK, ite_self]

private noncomputable def cutSummand {W α : Type*} (B : Finset W) (K : Set α)
    (v : W → α → WithZero (Multiplicative ℤ)) (b : α → ℂ) (t : α) : ℂ :=
  open Classical in if ∀ w ∈ B, v w t < 1 then
    K.indicator (fun z ↦ if ∀ w, v w z ≤ 1 then b z else 0) t else 0

private theorem cutSummand_eq_ite {W α : Type*} (B : Finset W) (K : Set α)
    (v : W → α → WithZero (Multiplicative ℤ)) (b : α → ℂ) (t : α)
    [d : Decidable (∀ w ∈ B, v w t < 1)] [e : ∀ z, Decidable (∀ w, v w z ≤ 1)] :
    cutSummand B K v b t = if ∀ w ∈ B, v w t < 1 then
      K.indicator (fun z ↦ if ∀ w, v w z ≤ 1 then b z else 0) t else 0 := by
  classical
  by_cases ht : t ∈ K <;> by_cases hp : ∀ w ∈ B, v w t < 1 <;>
    by_cases hq : ∀ w, v w t ≤ 1 <;> simp [cutSummand, ht, hp, hq]

private theorem cutSummand_indicator {W α : Type*} (B : Finset W) (K : Set α)
    (v : W → α → WithZero (Multiplicative ℤ)) (q b : α → ℂ) (t : α)
    {d : Decidable (∀ w ∈ B, v w t < 1)} {e : Decidable (∀ w, v w t ≤ 1)}
    (hq : q t = @ite ℂ _ d (@ite ℂ _ e (b t) 0) 0) :
    cutSummand B K v b t = K.indicator q t := by
  classical
  by_cases ht : t ∈ K
  · by_cases h₁ : ∀ w ∈ B, v w t < 1 <;> by_cases h₂ : ∀ w, v w t ≤ 1 <;>
      simpa only [cutSummand, Set.indicator_of_mem ht, h₁, h₂, ite_true, ite_false] using hq.symm
  · simp only [cutSummand, Set.indicator_of_notMem ht, ite_self]

private theorem ite_decision_irrel {P : Prop} (a b : ℂ) (d e : Decidable P) :
    @ite ℂ P d a b = @ite ℂ P e a b :=
  congrArg (fun i ↦ @ite ℂ P i a b) (Subsingleton.elim d e)

private theorem extendFiniteCutIn {W α X Y : Type*} [Fintype W] [AddCommGroup Y] [Module ℂ Y]
    [TopologicalSpace Y] (M : Submodule ℂ (StrongDual ℂ Y)) (j : X → Y) (H K : Set α) (v : W → α → WithZero (Multiplicative ℤ))
    (b : X → α → ℂ) (c : X → ℂ) (h : ∀ t, t ∈ H ↔ t ∈ K ∧ ∀ w, v w t = 1)
    (hc : ∀ x, HasSum (H.indicator (b x)) (c x))
    (hi : ∀ B : Finset W, ∃ L : M, ∀ x,
      HasSum (cutSummand B K v (b x)) (L.val (j x))) :
    ∃ L : M, ∀ x, L.val (j x) = c x := by
  classical
  let a (x : X) := K.indicator (fun t ↦ if ∀ w, v w t ≤ 1 then b x t else 0)
  let p : M →ₗ[ℂ] (X → ℂ) :=
    { toFun := fun l x ↦ l.val (j x)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have ha (f : X) : Summable (a f) :=
    ((hi ∅).choose_spec f).summable.congr fun t ↦
      (cutSummand_eq_ite ∅ K v (b f) t).trans (ite_eq_left (by simp))
  have hm (B : Finset W) : (fun f ↦ ∑' t, if ∀ w ∈ B, v w t < 1 then a f t else 0) ∈ p.range :=
    ⟨(hi B).choose, funext fun f ↦ ((hi B).choose_spec f).tsum_eq.symm.trans
      (tsum_congr (fun t ↦ cutSummand_eq_ite B K v (b f) t))⟩
  have hmem := tsum_avoiding_finset_mem p.range.toAddSubgroup a (fun f ↦ (ha f).norm)
    (fun w t ↦ v w t < 1) (fun B ↦ by
    obtain ⟨l,hl⟩ := hm B
    refine ⟨l, hl.trans (funext fun f ↦ tsum_congr fun t ↦ ?_)⟩
    exact ite_decision_irrel (P := ∀ w ∈ B, v w t < 1) (a f t) 0 _ _) Finset.univ
  obtain ⟨L,hh⟩ := hmem
  have hL : p L = fun f ↦ ∑' t, if ∀ w, ¬ v w t < 1 then a f t else 0 := by
    refine hh.trans (funext fun f ↦ tsum_congr fun t ↦ ?_)
    simp only [Finset.mem_univ, forall_true_left]
  exact ⟨L, fun f ↦ (congrFun hL f).trans ((tsum_congr
    (cutoff_indicator H K v (b f) h)).trans (hc f).tsum_eq)⟩

/-- The span of evaluation functionals on an S-local theta quotient. -/
def sLocalThetaEvaluationSpan (F : Type*) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) :
    Submodule ℂ (StrongDual ℂ (SLocalAdelicThetaSpace F S)) :=
  Submodule.span ℂ (range fun x ↦ thetaQuotientEval (sLocalAdelicTheta F S) x (sLocalAdelicTheta_continuous_eval x))

private theorem localCut_inSpan {S T : Finset V} (hST : S ⊆ T) (g : (SAdeleRing F S)ˣ)
    (B : Finset {w : T // w.val ∉ S}) : ∃ L : sLocalThetaEvaluationSpan F T, ∀ f : ℬₛ(S),
      HasSum (cutSummand (α := Fˣ) B ((T : Set V).unit F) (fun w t ↦ w.val.val.valuation F t.val)
        (fun t ↦ f (Multiplicative.ofAdd (adeleProjection F S (algebraMap F A t.val) * g.val))))
        (L.val ((Kₛ(T)).mkQ (sAdeleSchwartzTransition F hST f))) := by
  classical
  let y := (localCut_eval hST g B).choose
  have hy := (localCut_eval hST g B).choose_spec
  refine ⟨⟨thetaQuotientEval (sLocalAdelicTheta F T) y (sLocalAdelicTheta_continuous_eval y), Submodule.subset_span (mem_range_self y)⟩, fun f ↦ ?_⟩
  refine (localTheta_indicator_hasSum T (sAdeleSchwartzTransition F hST f) y).congr_fun fun t ↦ ?_
  exact cutSummand_indicator (α := Fˣ) B ((T : Set V).unit F)
    (fun w t ↦ w.val.val.valuation F t.val) _
    (fun t ↦ f (Multiplicative.ofAdd (adeleProjection F S (algebraMap F A t.val) * g.val))) t (hy f t)

/-- A theta evaluation on an old stage extends to a finite linear combination of
theta evaluations on a larger stage. -/
theorem sLocalThetaTransition_extend_eval_in_span {S T : Finset V} (hST : S ⊆ T) (g : (SAdeleRing F S)ˣ) :
    ∃ L : sLocalThetaEvaluationSpan F T, ∀ f : ℬₛ(S),
      L.val ((Kₛ(T)).mkQ (sAdeleSchwartzTransition F hST f)) = sLocalAdelicTheta F S f g := by
  classical
  refine extendFiniteCutIn (α := Fˣ) (X := ℬₛ(S)) (Y := Θₛ(T)) (W := {w : T // w.val ∉ S})
    (sLocalThetaEvaluationSpan F T) (fun f : ℬₛ(S) ↦ (Kₛ(T)).mkQ (sAdeleSchwartzTransition F hST f))
    ((S : Set V).unit F) ((T : Set V).unit F) (fun w t ↦ w.val.val.valuation F t.val)
    (fun f t ↦ f (Multiplicative.ofAdd (adeleProjection F S (algebraMap F A t.val) * g.val)))
    (fun f ↦ sLocalAdelicTheta F S f g) ?_ ?_ ?_
  · exact units_in_smaller_stage (F := F) hST
  · exact fun f ↦ localTheta_indicator_hasSum S f g
  · exact localCut_inSpan (F := F) hST g

private theorem hasSum_group_fiber {G Q E : Type*} [CommGroup G] [Group Q]
    [AddCommMonoid E] [TopologicalSpace E] (K H : Subgroup G) (v : G →* Q)
    (hH : ∀ t, t ∈ H ↔ t ∈ K ∧ v t = 1) (k : Q) (t₀ : G)
    (hk : t₀ ∈ K ∧ v t₀ = k) (f : G → E) {s : E}
    (h : HasSum (fun u : H ↦ f (u.val * t₀)) s) :
    HasSum (({t : G | t ∈ K ∧ v t = k} : Set G).indicator f) s := by
  let Z := {t : G | t ∈ K ∧ v t = k}
  let e (u : H) : Z := ⟨u.val * t₀, K.mul_mem ((hH _).mp u.property).1 hk.1,
    (v.map_mul _ _).trans (by rw [((hH _).mp u.property).2, one_mul, hk.2])⟩
  have he : Bijective e := by
    refine ⟨fun x y h ↦ Subtype.ext (mul_right_cancel (congrArg Subtype.val h)), ?_⟩
    rintro ⟨t, ht, hv⟩
    refine ⟨⟨t / t₀, (hH _).mpr ⟨K.div_mem ht hk.1, ?_⟩⟩, Subtype.ext (div_mul_cancel t t₀)⟩
    rw [map_div, hv, hk.2]
    exact div_self' k
  exact hasSum_subtype_iff_indicator.mp (((Equiv.ofBijective e he).hasSum_iff).mp h)

private theorem exists_translate_fiber {G Q J X : Type*} [CommGroup G] [Group Q] [Group J]
    (K H : Subgroup G) (v : G →* Q) (d : G →* J) (b θ : X → J → ℂ)
    (hH : ∀ t, t ∈ H ↔ t ∈ K ∧ v t = 1)
    (hθ : ∀ f x, HasSum (fun u : H ↦ b f (d u.val * x)) (θ f x)) (k : Q) :
    ∃ y : Option J, ∀ f x,
      HasSum (({t : G | t ∈ K ∧ v t = k} : Set G).indicator (fun t ↦ b f (d t * x)))
        (y.elim 0 (fun g ↦ θ f (g * x))) := by
  classical
  by_cases hex : ∃ t : G, t ∈ K ∧ v t = k
  · obtain ⟨t₀,ht⟩ := hex
    refine ⟨some (d t₀), fun f x ↦ hasSum_group_fiber K H v hH k t₀ ht _ ?_⟩
    exact (hθ f (d t₀ * x)).congr_fun fun u ↦ congrArg (b f) <|
      (congrArg (· * x) (d.map_mul u.val t₀)).trans (mul_assoc _ _ _)
  · refine ⟨none, fun f x ↦ ?_⟩
    refine hasSum_zero.congr_fun fun t ↦ ?_
    exact Set.indicator_of_notMem (fun ht ↦ hex ⟨t,ht⟩) _

private theorem localTheta_unit_hasSum (S : Finset V) (f : ℬₛ(S)) (x : (SAdeleRing F S)ˣ) :
    HasSum (fun u : (S : Set V).unit F ↦ f (Multiplicative.ofAdd
        (adeleProjection F S (algebraMap F A u.val.val) * x.val))) (sLocalAdelicTheta F S f x) :=
  hasSum_subtype_iff_indicator.mpr (localTheta_indicator_hasSum S f x)

private theorem unit_fun_eq_iff {W M : Type*} [Monoid M] (u v : W → Mˣ) :
    (∀ w, (u w).val = (v w).val) ↔ u = v :=
  ⟨fun h ↦ funext fun w ↦ Units.ext (h w), fun h w ↦ congrArg Units.val (congrFun h w)⟩

/-- On a single valuation fiber the sum over the larger unit group is a translate
of the S-local theta sum. Empty fibers contribute zero. The representative works
for all test functions and all evaluation points simultaneously. -/
theorem sLocalTheta_valuationFiber {S T : Finset V} (hST : S ⊆ T)
    (k : {w : T // w.val ∉ S} → (WithZero (Multiplicative ℤ))ˣ) :
    let v : Fˣ →* ({w : T // w.val ∉ S} → (WithZero (Multiplicative ℤ))ˣ) :=
      MonoidHom.pi fun w ↦ Units.map (w.val.val.valuation F).toMonoidHom
    ∃ y : Option (SAdeleRing F S)ˣ, ∀ (f : ℬₛ(S)) (x : (SAdeleRing F S)ˣ),
      HasSum (({t : Fˣ | t ∈ (T : Set V).unit F ∧ v t = k} : Set Fˣ).indicator
        (fun t ↦ f (Multiplicative.ofAdd (adeleProjection F S (algebraMap F A t.val) * x.val))))
        (y.elim 0 fun g ↦ sLocalAdelicTheta F S f (g * x)) := by
  classical
  let W := {w : T // w.val ∉ S}
  let v : Fˣ →* (W → (WithZero (Multiplicative ℤ))ˣ) :=
    MonoidHom.pi fun w ↦ Units.map (w.val.val.valuation F).toMonoidHom
  have hh (t : Fˣ) : t ∈ (S : Set V).unit F ↔ t ∈ (T : Set V).unit F ∧ v t = 1 :=
    (units_in_smaller_stage (F := F) hST t).trans (and_congr_right' (unit_fun_eq_iff (v t) 1))
  let d := Units.map ((adeleProjection F S).toMonoidHom.comp (algebraMap F A).toMonoidHom)
  let b (f : ℬₛ(S)) (x : (SAdeleRing F S)ˣ) := f (Multiplicative.ofAdd x.val)
  have hθ (f : ℬₛ(S)) (x : (SAdeleRing F S)ˣ) :
      HasSum (fun u : (S : Set V).unit F ↦ b f (d u.val * x)) (sLocalAdelicTheta F S f x) :=
    localTheta_unit_hasSum S f x
  have result := exists_translate_fiber ((T : Set V).unit F) ((S : Set V).unit F) v d b
    (fun f x ↦ sLocalAdelicTheta F S f x) hh hθ k
  exact result

end KernelDescent

private theorem quotientMap_unique {R X Y : Type*} [Ring R] [AddCommGroup X] [AddCommGroup Y]
    [Module R X] [Module R Y] (K : Submodule R X) (L : Submodule R Y)
    (j : X →ₗ[R] Y) (hj : K ≤ L.comap j) :
    (K.mapQ L j hj).comp K.mkQ = L.mkQ.comp j ∧
      ∀ π : (X ⧸ K) →ₗ[R] (Y ⧸ L), π.comp K.mkQ = L.mkQ.comp j → π = K.mapQ L j hj := by
  refine ⟨K.mapQ_mkQ L j, fun π hπ ↦ LinearMap.ext fun x ↦ ?_⟩
  obtain ⟨a, rfl⟩ := K.mkQ_surjective x
  exact DFunLike.congr_fun hπ a

/-- Paper: Theorem 5.2.1.1(2), p. 230.
The theta transition is the unique linear map taking each class to the class of its
Schwartz–Bruhat transition. -/
theorem sLocalThetaTransition_unique (hST : S ⊆ T) :
    let descends := fun π : Θₛ(S) →ₗ[ℂ] Θₛ(T) ↦
      π.comp (Kₛ(S)).mkQ = (Kₛ(T)).mkQ.comp (sAdeleSchwartzTransition F hST)
    descends (sLocalThetaTransition hST) ∧
      ∀ π, descends π → π = sLocalThetaTransition hST :=
  quotientMap_unique (Kₛ(S)) (Kₛ(T)) (sAdeleSchwartzTransition F hST)
    (sLocalThetaTransition_preserves_kernel hST)

private theorem quotientMap_comp {R X Y Z : Type*} [Ring R] [AddCommGroup X] [AddCommGroup Y]
    [AddCommGroup Z] [Module R X] [Module R Y] [Module R Z] (K : Submodule R X) (L : Submodule R Y) (M : Submodule R Z)
    (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z) (h : X →ₗ[R] Z)
    (hf : K ≤ L.comap f) (hg : L ≤ M.comap g) (hh : K ≤ M.comap h) (hc : g.comp f = h) :
    (L.mapQ M g hg).comp (K.mapQ L f hf) = K.mapQ M h hh := by
  subst h
  exact (K.mapQ_comp L M f g hf hg).symm

private theorem testTransition_comp (hST : S ⊆ T) (hTU : T ⊆ U) :
    (sAdeleSchwartzTransition F hTU).comp (sAdeleSchwartzTransition F hST) =
      sAdeleSchwartzTransition F (hST.trans hTU) := by
  refine LinearMap.ext fun f ↦ (sAdeleSchwartzToGlobal_isEmbedding F U).injective ?_
  have h {A B : Finset (HeightOneSpectrum (𝓞 F))} (hAB : A ⊆ B) (g : ℬₛ(A)) :
      sAdeleSchwartzToGlobal F B (sAdeleSchwartzTransition F hAB g) =
        sAdeleSchwartzToGlobal F A g := DFunLike.congr_fun (sAdeleSchwartzToGlobal_comp F hAB) g
  exact ((h hTU _).trans (h hST f)).trans (h (hST.trans hTU) f).symm

/-- Paper: Theorem 5.2.1.1(2), p. 230.
Two successive theta transitions agree with the direct transition. -/
theorem sLocalThetaTransition_comp (hST : S ⊆ T) (hTU : T ⊆ U) :
    (sLocalThetaTransition (F := F) hTU).comp (sLocalThetaTransition hST) =
      sLocalThetaTransition (hST.trans hTU) := quotientMap_comp _ _ _ _ _ _
    (sLocalThetaTransition_preserves_kernel hST) (sLocalThetaTransition_preserves_kernel hTU)
    (sLocalThetaTransition_preserves_kernel (hST.trans hTU)) (testTransition_comp hST hTU)

variable (F S) in
/-- Paper: (5.2.1.3), p. 230.
The insertion of S-local theta classes into global theta classes is the map
induced by the insertion of test functions. -/
def sLocalThetaToGlobal : Θₛ(S) →ₗ[ℂ] Θ𝔽 :=
  (Kₛ(S)).mapQ K𝔽 (sAdeleSchwartzToGlobal F S) sLocalThetaToGlobal_preserves_kernel

/-- Continuity descends from the transition of test functions through the quotient map. -/
theorem sLocalThetaTransition_continuous (hST : S ⊆ T) :
    Continuous (sLocalThetaTransition (F := F) hST) := by
  apply (Kₛ(S)).isQuotientMap_mkQ.continuous_iff.mpr
  exact (Kₛ(T)).mkQL.continuous.comp (sAdeleSchwartzTransition_isEmbedding F hST).continuous

/-- Continuity of the global insertion descends through the local quotient. -/
theorem sLocalThetaToGlobal_continuous : Continuous (sLocalThetaToGlobal F S) := by
  apply (Kₛ(S)).isQuotientMap_mkQ.continuous_iff.mpr
  exact (K𝔽).mkQL.continuous.comp (sAdeleSchwartzToGlobal_isEmbedding F S).continuous

/-- Paper: (5.2.1.3), p. 230.
Inserting the class of a local test function gives the class of its extension to the adeles. -/
theorem sLocalThetaToGlobal_mk (f : ℬₛ(S)) :
    sLocalThetaToGlobal F S (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (sAdeleSchwartzToGlobal F S f) := rfl

private theorem injective_mapQ_of_comap_le {R X Y : Type*} [Ring R] [AddCommGroup X]
    [AddCommGroup Y] [Module R X] [Module R Y] (K : Submodule R X) (L : Submodule R Y)
    (j : X →ₗ[R] Y) (hj : K ≤ L.comap j) (hr : L.comap j ≤ K) :
    Injective (K.mapQ L j hj) := by
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.ker_mapQ, le_antisymm hr hj, Submodule.mkQ_map_self]

/-- Insertion is injective because global theta detects the S-unit sum on an inserted test. -/
theorem sLocalThetaToGlobal_injective : Injective (sLocalThetaToGlobal F S) :=
  injective_mapQ_of_comap_le (Kₛ(S)) (K𝔽) (sAdeleSchwartzToGlobal F S)
    (sLocalThetaToGlobal_preserves_kernel (F := F) (S := S))
    (sLocalThetaToGlobal_reflects_kernel (F := F) (S := S))

/-- Paper: Theorem 5.2.1.1(2), p. 230.
The stage insertions and transitions form a compatible family in the global quotient. -/
theorem sLocalThetaToGlobal_comp (hST : S ⊆ T) :
    (sLocalThetaToGlobal F T).comp (sLocalThetaTransition hST) = sLocalThetaToGlobal F S :=
  quotientMap_comp _ _ _ _ _ _
    (sLocalThetaTransition_preserves_kernel hST) sLocalThetaToGlobal_preserves_kernel
    sLocalThetaToGlobal_preserves_kernel (sAdeleSchwartzToGlobal_comp F hST)

private theorem quotientMap_exhaustive {ι R Y : Type*} [Ring R] [AddCommGroup Y] [Module R Y]
    {X : ι → Type*} [∀ i, AddCommGroup (X i)] [∀ i, Module R (X i)] (K : Submodule R Y)
    (D : ∀ i, Submodule R (X i)) (j : ∀ i, X i →ₗ[R] Y) (hj : ∀ i, D i ≤ K.comap (j i))
    (he : ∀ y, ∃ i, y ∈ (j i).range) (x : Y ⧸ K) :
    ∃ i z, (D i).mapQ K (j i) (hj i) z = x := by
  obtain ⟨f,rfl⟩ := K.mkQ_surjective x
  obtain ⟨i,g,rfl⟩ := he f
  exact ⟨i, (D i).mkQ g, rfl⟩

/-- The compatible injections into global theta space detect equality at every finite stage. -/
theorem sLocalThetaTransition_injective (hST : S ⊆ T) :
    Injective (sLocalThetaTransition (F := F) hST) := by
  intro x y h
  have hc := sLocalThetaToGlobal_comp (F := F) hST
  exact sLocalThetaToGlobal_injective (F := F) (S := S) (((DFunLike.congr_fun hc x).symm.trans
    (congrArg (sLocalThetaToGlobal F T) h)).trans (DFunLike.congr_fun hc y))

private theorem closedEmbedding_of_linear_comp {R X Y Z : Type*} [Semiring R]
    [AddCommMonoid X] [AddCommMonoid Y] [AddCommMonoid Z] [Module R X] [Module R Y] [Module R Z]
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z) (h : X →ₗ[R] Z) (he : IsEmbedding g)
    (hc : IsClosedEmbedding h) (eq : g.comp f = h) : IsClosedEmbedding f := by
  subst h
  exact IsClosedEmbedding.of_comp he hc

/-- Paper: Theorem 5.2.1.1(2), p. 230.
Every global theta class comes from a finite stage. -/
theorem sLocalThetaToGlobal_exhaustive (x : Θ𝔽) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 F))) (y : Θₛ(S)),
      sLocalThetaToGlobal F S y = x :=
  quotientMap_exhaustive (K𝔽) (fun S ↦ Kₛ(S)) (sAdeleSchwartzToGlobal F)
    (fun S ↦ sLocalThetaToGlobal_preserves_kernel (F := F) (S := S))
    (sAdeleSchwartzToGlobal_exhaustive F) x

private theorem quotient_finalTopology {ι E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] {X : ι → Type*}
    [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)] [∀ i, TopologicalSpace (X i)]
    (j : ∀ i, X i →ₗ[ℂ] E) (hj : ∀ i, Continuous (j i)) (K : Submodule ℂ E)
    (D : ∀ i, Submodule ℂ (X i)) (hD : ∀ i, D i ≤ K.comap (j i))
    [PolynormableSpace ℂ (E ⧸ K)]
    (ht : (inferInstance : TopologicalSpace E) = locallyConvexFinalTopology j) :
    (inferInstance : TopologicalSpace (E ⧸ K)) = locallyConvexFinalTopology
      (fun i ↦ (D i).mapQ K (j i) (hD i)) := by
  let jQ i := (D i).mapQ K (j i) (hD i)
  have hP : WithSeminorms (Subtype.val : {p : Seminorm ℂ E // ∀ i, Continuous (p ∘ j i)} → _) := ⟨ht⟩
  have h : (fun p : Seminorm ℂ (E ⧸ K) ↦ ∀ i, Continuous (p ∘ jQ i)) =
      (fun p : Seminorm ℂ (E ⧸ K) ↦ Continuous p) := by
    funext p
    apply propext
    refine ⟨fun hp ↦ K.isQuotientMap_mkQ.continuous_iff.mpr ?_, fun hp i ↦ ?_⟩
    · exact hP.continuous_seminorm ⟨p.comp K.mkQ, fun i ↦ (hp i).comp (D i).mkQL.continuous⟩
    · exact (D i).isQuotientMap_mkQ.continuous_iff.mpr ((hp.comp K.mkQL.continuous).comp (hj i))
  let gen (P : Seminorm ℂ (E ⧸ K) → Prop) := (SeminormFamily.moduleFilterBasis
    (Subtype.val : {p : Seminorm ℂ (E ⧸ K) // P p} → Seminorm ℂ (E ⧸ K))).topology
  exact (PolynormableSpace.withSeminorms ℂ (E ⧸ K)).withSeminorms_eq.trans (congrArg gen h.symm)

/-- Paper: Theorem 5.2.1.1(2), p. 230.
The global quotient has the final locally convex topology for the S-local insertions.
Deviation: The compatible embeddings and exhaustion identify the algebraic colimit
with the global space, where the assertion becomes an equality of topologies. -/
theorem sLocalThetaToGlobal_finalTopology :
    (inferInstance : TopologicalSpace Θ𝔽) = locallyConvexFinalTopology (sLocalThetaToGlobal F) := by
  let : PolynormableSpace ℂ Θ𝔽 := globalAdelicThetaSpace_polynormable
  exact quotient_finalTopology (sAdeleSchwartzToGlobal F)
    (fun S ↦ (sAdeleSchwartzToGlobal_isEmbedding F S).continuous) (K𝔽)
    (fun S ↦ Kₛ(S)) (fun _ ↦ sLocalThetaToGlobal_preserves_kernel)
    (sAdeleSchwartzToGlobal_finalTopology F)

section CofinalStages

open Set

/-- Cofinal countable chains of finite sets recover the topology of a locally convex
limit. It suffices to embed across one new coordinate at a time. -/
private theorem finset_limit_isEmbedding {V E : Type*} [Countable V] [DecidableEq V]
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    {X : Finset V → Type*} [∀ S, AddCommGroup (X S)] [∀ S, Module ℂ (X S)]
    [∀ S, TopologicalSpace (X S)] [∀ S, IsTopologicalAddGroup (X S)] [∀ S, PolynormableSpace ℂ (X S)]
    (i : ∀ S, X S →L[ℂ] E) (j : ∀ {S T}, S ⊆ T → X S →L[ℂ] X T)
    (hi : ∀ S, Injective (i S)) (hc : ∀ (S T) (h : S ⊆ T), (i T).comp (j h) = i S)
    (hx : ∀ x, ∃ S y, i S y = x)
    (ht : (inferInstance : TopologicalSpace E) = locallyConvexFinalTopology (fun S ↦ (i S).toLinearMap))
    (he : ∀ (S : Finset V) (v : V), IsEmbedding (j (Finset.subset_insert v S))) (S : Finset V) : IsEmbedding (i S) := by
  classical
  let h := exists_surjective_nat (Finset V)
  let e := h.choose
  let C (n : ℕ) := S ∪ (Finset.range n).biUnion e
  have hm : Monotone C := fun a b hab ↦ Finset.union_subset_union_right <|
    Finset.biUnion_subset_biUnion_of_subset_left e (Finset.range_mono hab)
  have hco (U : Finset V) : ∃ n, U ⊆ C n := by
    obtain ⟨n,hn⟩ := h.choose_spec U
    refine ⟨n+1, fun u hu ↦ Finset.mem_union_right _ ?_⟩
    exact Finset.mem_biUnion.mpr ⟨n, Finset.mem_range.mpr n.lt_succ_self, show u ∈ e n from (show e n = U from hn).symm ▸ hu⟩
  have hcomp {U T : Finset V} (hUT : U ⊆ T) (x : X U) : i T (j hUT x) = i U x :=
    DFunLike.congr_fun (hc U T hUT) x
  have hj {U T : Finset V} (hUT : U ⊆ T) : IsEmbedding (j hUT) := by
    have hrefl {Q : Finset V} (eq : U = Q) (H : U ⊆ Q) : IsEmbedding (j H) := by
      subst Q
      have hid : ⇑(j H) = id := funext fun x ↦ hi U (hcomp H x)
      exact (congrArg IsEmbedding hid).mpr IsEmbedding.id
    have hu (B : Finset V) : ∀ (H : U ⊆ U ∪ B), IsEmbedding (j H) := by
      induction B using Finset.induction_on with
      | empty =>
        exact hrefl (Finset.union_empty U).symm
      | insert v B _ ih =>
        rw [Finset.union_insert]
        intro H
        let hB : U ⊆ U ∪ B := Finset.subset_union_left
        let hv := Finset.subset_insert v (U ∪ B)
        have hjc : ⇑(j H) = (j hv) ∘ (j hB) := funext fun x ↦ hi _
          ((hcomp H x).trans ((hcomp hv (j hB x)).trans (hcomp hB x)).symm)
        rw [hjc]
        exact (he _ _).comp (ih hB)
    have heq := Finset.union_eq_right.mpr hUT
    have hh := hu T
    rw [heq] at hh
    exact hh hUT
  let m n := j (hm (Nat.le_succ n))
  have hlim : IsInjectiveLCLimit m (fun n ↦ i (C n)) := by
    refine ⟨fun n ↦ hi _, fun n ↦ hc _ _ _, fun x ↦ ?_, ?_⟩
    · obtain ⟨U,y,rfl⟩ := hx x
      obtain ⟨n,hn⟩ := hco U
      exact ⟨n,j hn y,hcomp hn y⟩
    · have hk : (fun p : Seminorm ℂ E ↦ ∀ n : ℕ, Continuous (p ∘ (i (C n)).toLinearMap)) =
          (fun p : Seminorm ℂ E ↦ ∀ U, Continuous (p ∘ (i U).toLinearMap)) := by
        funext p
        apply propext
        refine ⟨fun hp U ↦ ?_, fun hp n ↦ hp (C n)⟩
        obtain ⟨n,hn⟩ := hco U
        exact ((hp n).comp (j hn).continuous).congr fun x ↦ congrArg p (hcomp hn x)
      unfold locallyConvexFinalTopology at ht ⊢
      rwa [hk]
  have h0 : C 0 = S := by simp [C]
  have hh := hlim.isEmbedding_stage (fun n ↦ hj _) 0
  rw [h0] at hh
  exact hh

local notation "V" => HeightOneSpectrum (𝓞 F)

open Classical in
/-- Embeddings for one-place enlargements suffice to embed every finite theta stage
in the global quotient endowed with its final locally convex topology. -/
theorem sLocalThetaToGlobal_isEmbedding_of_insert
    (he : ∀ (T : Finset V) (v : V),
      IsEmbedding (sLocalThetaTransition (F := F) (Finset.subset_insert v T))) (S : Finset V) :
    IsEmbedding (sLocalThetaToGlobal F S) := by
  classical
  let : Countable V := finitePlaces_countable F
  let (T : Finset V) : PolynormableSpace ℂ (Θₛ(T)) :=
    sLocalAdelicThetaSpace_polynormable (F := F) (S := T)
  let i (T : Finset V) : Θₛ(T) →L[ℂ] Θ𝔽 :=
    ⟨sLocalThetaToGlobal F T, sLocalThetaToGlobal_continuous (F := F) (S := T)⟩
  let j {T U : Finset V} (h : T ⊆ U) : Θₛ(T) →L[ℂ] Θₛ(U) :=
    ⟨sLocalThetaTransition (F := F) h, sLocalThetaTransition_continuous (F := F) h⟩
  have hcomp (T U : Finset V) (h : T ⊆ U) : (i U).comp (j h) = i T :=
    ContinuousLinearMap.ext fun x ↦ DFunLike.congr_fun (sLocalThetaToGlobal_comp (F := F) h) x
  exact finset_limit_isEmbedding (X := fun T : Finset V ↦ Θₛ(T)) i (fun h ↦ j h)
    (fun T ↦ sLocalThetaToGlobal_injective (F := F) (S := T))
    hcomp
    (sLocalThetaToGlobal_exhaustive (F := F)) (sLocalThetaToGlobal_finalTopology (F := F)) he S

end CofinalStages

section UnitActions

open Bornology Set
open scoped Uniformity Classical TensorProduct RestrictedProduct

/-- Pointwise continuity of a locally compact family of continuous linear maps
gives joint continuity when the domain is barrelled. -/
private theorem continuous_family_of_orbits {G E : Type*} [TopologicalSpace G] [WeaklyLocallyCompactSpace G]
    [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℂ E]
    [PolynormableSpace ℂ E] [BarrelledSpace ℂ E]
    (T : G → E →L[ℂ] E) (hT : ∀ x, Continuous fun g ↦ T g x) :
    Continuous fun p : G × E ↦ T p.1 p.2 := by
  apply continuous_iff_continuousAt.mpr
  rintro ⟨g,x⟩
  obtain ⟨K, hK, hKg⟩ := exists_compact_mem_nhds g
  have hb (y : E) : IsVonNBounded ℂ (range fun k : K ↦ T k.val y) := by
    exact (congrArg (IsVonNBounded ℂ) (image_eq_range (fun g ↦ T g y) K)).mp ((hK.image (hT y)).isVonNBounded ℂ)
  have hEq := (PolynormableSpace.banach_steinhaus hb).equicontinuous x
  apply ((hT x).continuousAt.comp (continuousAt_fst (p := (g,x)))).congr_uniformity
  intro U hU
  change ∀ᶠ p : G × E in 𝓝 (g,x), (T p.1 x, T p.1 p.2) ∈ U
  filter_upwards [continuousAt_fst.preimage_mem_nhds hKg, continuousAt_snd.preimage_mem_nhds (hEq U hU)]
    with p hp he
  exact he ⟨p.1,hp⟩

private theorem finiteDimensional_schwartz_montel {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] : MontelSpace ℂ (SchwartzMap V ℂ) := by
  let m := Module.finrank ℝ V
  let E := EuclideanSpace ℝ (Fin m)
  let L : V ≃L[ℝ] E := ContinuousLinearEquiv.ofFinrankEq (by simp [E, m, finrank_euclideanSpace])
  let P := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm (F := ℂ)
  let Q := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L (F := ℂ)
  let e := ContinuousLinearEquiv.equivOfInverse P Q
    (fun f ↦ SchwartzMap.ext fun x ↦ congrArg f (L.symm_apply_apply x))
    (fun f ↦ SchwartzMap.ext fun x ↦ congrArg f (L.apply_symm_apply x))
  let : MontelSpace ℂ (SchwartzMap E ℂ) := montel_euclideanSchwartz m
  constructor
  intro s hs hb
  exact e.toHomeomorph.isEmbedding.isCompact_iff.mpr
    (MontelSpace.isCompact_of_isClosed_of_isVonNBounded ℂ
      (e.toHomeomorph.isClosedMap s hs) (hb.image e.toContinuousLinearMap))

private def mulUnitLinearEquiv {V : Type*} [NormedCommRing V] [NormedAlgebra ℝ V]
    (u : Vˣ) : V ≃L[ℝ] V :=
  ContinuousLinearEquiv.equivOfInverse (ContinuousLinearMap.mul ℝ V u.val)
    (ContinuousLinearMap.mul ℝ V u.inv)
    (fun x ↦ by change u.inv * (u.val * x) = x; rw [← mul_assoc, u.inv_val, one_mul])
    (fun x ↦ by change u.val * (u.inv * x) = x; rw [← mul_assoc, u.val_inv, one_mul])

private theorem continuous_mixedCoordinates (F : Type*) [Field F] [NumberField F] :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  let M := InfiniteAdeleRing.ringEquiv_mixedSpace F
  have h : ⇑M = fun x ↦
      ((fun (v : {w : InfinitePlace F // InfinitePlace.IsReal w}) ↦
        InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
       (fun (v : {w : InfinitePlace F // InfinitePlace.IsComplex w}) ↦
        InfinitePlace.Completion.extensionEmbedding v.1 (x v))) :=
    funext (InfiniteAdeleRing.ringEquiv_mixedSpace_apply F)
  exact h ▸ ((continuous_pi fun v ↦
    (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp
      (continuous_apply v.1)).prodMk (continuous_pi fun v ↦
    (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp
      (continuous_apply v.1)))

private theorem continuous_schwartzUnitOrbit_of_coordinates
    {R V G : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [NormedCommRing V] [NormedAlgebra ℝ V] [FiniteDimensional ℝ V]
    [TopologicalSpace G] [WeaklyLocallyCompactSpace G]
    (M : R ≃+* V) (hM : Continuous M)
    (J : SchwartzMap V ℂ ≃L[ℂ] SchwartzBruhat (Multiplicative R))
    (hJ : ∀ f x, J f (Multiplicative.ofAdd x) = f (M x))
    (g : G → Rˣ) (hg : Continuous g) (f : SchwartzBruhat (Multiplicative R)) :
    Continuous fun t ↦ schwartzBruhatUnitTranslate (g t) f := by
  let u (t : G) := Units.map M.toMonoidHom (g t)
  let A (t : G) : V ≃L[ℝ] V := mulUnitLinearEquiv (u t)⁻¹
  have hA : Continuous fun t ↦ (A t).toContinuousLinearMap :=
    (ContinuousLinearMap.mul ℝ V).continuous.comp (hM.comp (Units.continuous_coe_inv.comp hg))
  have hB : Continuous fun t ↦ (A t).symm.toContinuousLinearMap :=
    (ContinuousLinearMap.mul ℝ V).continuous.comp (hM.comp (Units.continuous_val.comp hg))
  let : MontelSpace ℂ (SchwartzMap V ℂ) := finiteDimensional_schwartz_montel
  refine (J.continuous.comp (continuous_schwartz_comp_family A hA hB (J.symm f))).congr ?_
  intro t
  apply Subtype.ext
  funext x
  refine (hJ _ x.toAdd).trans ?_
  exact (congrArg (J.symm f) (M.map_mul (g t).inv x.toAdd).symm).trans
    ((hJ (J.symm f) ((g t).inv * x.toAdd)).symm.trans
      (congrArg (fun φ : SchwartzBruhat (Multiplicative R) ↦
        φ (Multiplicative.ofAdd ((g t).inv * x.toAdd))) (J.apply_symm_apply f)))

private theorem continuous_archUnitOrbit {F G : Type*} [Field F] [NumberField F]
    [TopologicalSpace G] [WeaklyLocallyCompactSpace G]
    (g : G → (InfiniteAdeleRing F)ˣ) (hg : Continuous g)
    (f : SchwartzBruhat (Multiplicative (InfiniteAdeleRing F))) :
    Continuous fun t ↦ schwartzBruhatUnitTranslate (g t) f :=
  continuous_schwartzUnitOrbit_of_coordinates (InfiniteAdeleRing.ringEquiv_mixedSpace F)
    (continuous_mixedCoordinates F) (archimedeanSchwartzBruhat_equiv (F := F)).choose
    (archimedeanSchwartzBruhat_equiv (F := F)).choose_spec g hg f

private theorem locallyConstant_unit_family {G R Y : Type*} [TopologicalSpace G] [WeaklyLocallyCompactSpace G]
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [Zero Y]
    (u : G → Rˣ) (hu : Continuous u) (f : R → Y) (hf : IsLocallyConstant f) (hK : HasCompactSupport f) :
    IsLocallyConstant fun g x ↦ f ((u g).inv * x) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro g
  obtain ⟨L,hL,hLg⟩ := exists_compact_mem_nhds g
  let K := (fun p : G × R ↦ (u p.1).val * p.2) '' (L ×ˢ tsupport f)
  have hc : IsCompact K := (hL.prod hK).image ((Units.continuous_val.comp (hu.comp continuous_fst)).mul continuous_snd)
  let W := {p : G × R | f ((u p.1).inv * p.2) = f ((u g).inv * p.2)}
  have hW : IsOpen W := by
    apply isOpen_iff_mem_nhds.mpr
    intro p hp
    have h₁ := (Units.continuous_coe_inv.comp (hu.comp continuous_fst)).mul (continuous_snd (X := G) (Y := R))
    have h₂ : Continuous (fun p : G × R ↦ (u g).inv * p.2) := continuous_const.mul continuous_snd
    filter_upwards [h₁.continuousAt (hf.eventually_eq _), h₂.continuousAt (hf.eventually_eq _)]
      with q hq hq'
    exact hq.trans (hp.trans hq'.symm)
  obtain ⟨U,V,hU,_,hu₀,hV,hUV⟩ := generalized_tube_lemma (isCompact_singleton (x := g)) hc hW
    (fun ⟨g',x⟩ h ↦ by rw [show g' = g from h.1]; rfl)
  filter_upwards [hLg, hU.mem_nhds (hu₀ (mem_singleton g))] with t ht hu'
  funext x
  by_cases hx : x ∈ K
  · exact @hUV (t,x) ⟨hu',hV hx⟩
  · have hz (a : G) (ha : a ∈ L) : f ((u a).inv * x) = 0 := by
      by_contra hn
      exact hx ⟨(a, (u a).inv * x), ⟨ha, subset_closure (show (u a).inv * x ∈ support f from hn)⟩,
        by change (u a).val * ((u a).inv * x) = x; rw [← mul_assoc, (u a).val_inv, one_mul]⟩
    exact (hz t ht).trans (hz g (mem_of_mem_nhds hLg)).symm

section
variable {F : Type*} [Field F] [NumberField F]

private theorem compact_subgroups_of_equiv {A B : Type*} [Group A] [Group B]
    [TopologicalSpace A] [TopologicalSpace B] (e : A ≃* B) (he : IsHomeomorph e)
    (h : ∀ s : Set A, IsCompact s → ∃ H : Subgroup A, IsCompact (H : Set A) ∧ s ⊆ H)
    (s : Set B) (hs : IsCompact s) : ∃ H : Subgroup B, IsCompact (H : Set B) ∧ s ⊆ H := by
  obtain ⟨K,hK,hsub⟩ := h (e ⁻¹' s) (he.isClosedEmbedding.isCompact_preimage hs)
  exact ⟨K.map e, hK.image he.continuous, fun x hx ↦
    ⟨e.symm x, hsub (show e (e.symm x) ∈ s from (e.apply_symm_apply x).symm ▸ hx), e.apply_symm_apply x⟩⟩

private theorem finiteAdele_test_locallyConstant (f : SchwartzBruhat (Multiplicative (FiniteAdeleRing (𝓞 F) F))) :
    IsLocallyConstant (fun x ↦ f (Multiplicative.ofAdd x)) ∧
      HasCompactSupport (fun x ↦ f (Multiplicative.ofAdd x)) := by
  let G := Multiplicative (FiniteAdeleRing (𝓞 F) F)
  let E := (finiteAdeleTail_empty F).choose
  have hE := (finiteAdeleTail_empty F).choose_spec.1
  let e := E.toAddEquiv.toMultiplicative
  have he : IsHomeomorph e := hE
  let : TotallyDisconnectedSpace G :=
    ⟨isTotallyDisconnected_of_image
      (RestrictedProduct.continuous_coe.comp continuous_toAdd).continuousOn
      (DFunLike.coe_injective.comp Multiplicative.toAdd.injective)
      (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩
  let : T2Space G := by
    change T2Space (Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F])
    infer_instance
  let M : Submodule ℂ (G → ℂ) :=
    { carrier := {h | IsLocallyConstant h ∧ HasCompactSupport h}
      zero_mem' := ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩
      add_mem' := fun hf hh ↦ ⟨hf.1.comp₂ hh.1 (· + ·), hf.2.add hh.2⟩
      smul_mem' := fun c _ hf ↦ ⟨hf.1.comp (c • ·), hf.2.smul_left⟩ }
  have hle : schwartzBruhatSubmodule G ≤ M := by
    refine iSup_le fun a ↦ iSup_le fun w ↦ ?_
    rintro _ ⟨s, rfl⟩
    exact bruhatStage_locallyConstant_compactSupport
      (compact_subgroups_of_equiv e he (finiteAdeleTail_compact_subset_subgroup F ∅)) a w s
  exact hle f.property
end

section
variable {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
local notation "B" => SchwartzBruhat (Multiplicative R)

private def unitTranslateEnd : Rˣ →* Module.End ℂ B where
  toFun u :=
    { toFun := schwartzBruhatUnitTranslate u
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  map_one' := LinearMap.ext fun f ↦ Subtype.ext (funext fun x ↦
    congrArg (fun y ↦ f (Multiplicative.ofAdd y)) (one_mul x.toAdd))
  map_mul' := fun u v ↦ LinearMap.ext fun f ↦ Subtype.ext (funext fun x ↦
    congrArg (fun y ↦ f (Multiplicative.ofAdd y)) (mul_assoc v.inv u.inv x.toAdd))

private theorem continuous_unitTranslate [T2Space R] [LocallyCompactSpace R] (g : Rˣ) :
    Continuous (schwartzBruhatUnitTranslate g) := by
  let : T2Space (Multiplicative R) := inferInstanceAs (T2Space R)
  let : LocallyCompactSpace (Multiplicative R) := inferInstanceAs (LocallyCompactSpace R)
  let d : Multiplicative R ≃ₜ* Multiplicative R :=
    { toFun := fun x ↦ Multiplicative.ofAdd (g.val * x.toAdd)
      invFun := fun x ↦ Multiplicative.ofAdd (g.inv * x.toAdd)
      left_inv := fun x ↦ congrArg Multiplicative.ofAdd (by change g.inv * (g.val * x.toAdd) = x.toAdd; rw [← mul_assoc, g.inv_val, one_mul])
      right_inv := fun x ↦ congrArg Multiplicative.ofAdd (by change g.val * (g.inv * x.toAdd) = x.toAdd; rw [← mul_assoc, g.val_inv, one_mul])
      map_mul' := fun x y ↦ congrArg Multiplicative.ofAdd (mul_add g.val x.toAdd y.toAdd)
      continuous_toFun := continuous_ofAdd.comp (continuous_const.mul continuous_toAdd)
      continuous_invFun := continuous_ofAdd.comp (continuous_const.mul continuous_toAdd) }
  obtain ⟨L, hL⟩ := schwartzBruhat_transport d
  exact L.continuous.congr fun f ↦ Subtype.ext (funext (hL f))

end

private theorem tensor_orbits_continuous {G X Y Z : Type*} [TopologicalSpace G]
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z] [IsTopologicalAddGroup Z]
    (e : InductiveTensor X Y ≃L[ℂ] Z) (T : G → Module.End ℂ Z)
    (a : G → X → X) (b : G → Y → Y) (ha : ∀ x, Continuous fun g ↦ a g x)
    (hb : ∀ y, IsLocallyConstant fun g ↦ b g y)
    (he : ∀ g x y, T g (e (x ⊗ₜ[ℂ] y)) = e (a g x ⊗ₜ[ℂ] b g y)) :
    ∀ z, Continuous fun g ↦ T g z := by
  have hsp := withGeneratingSeminorms_spec (X ⊗[ℂ] Y)
    (fun p : {p : Seminorm ℂ (X ⊗[ℂ] Y) //
      (∀ x : X, Continuous (fun y : Y ↦ p (x ⊗ₜ[ℂ] y))) ∧
      (∀ y : Y, Continuous (fun x : X ↦ p (x ⊗ₜ[ℂ] y)))} ↦ p.val)
  have hleft (y : Y) : Continuous (fun x : X ↦ e (x ⊗ₜ[ℂ] y)) := e.continuous.comp
    (hsp.continuous_of_continuous_comp ((TensorProduct.mk ℂ X Y).flip y) fun p ↦ p.2.2 y)
  intro z
  obtain ⟨w, rfl⟩ := e.surjective z
  induction w using TensorProduct.inductionOn with
  | tmul x y =>
    apply continuous_iff_continuousAt.mpr
    intro g
    apply ((hleft (b g y)).comp (ha x)).continuousAt.congr_of_eventuallyEq
    filter_upwards [(hb y).eventually_eq g] with t ht
    exact (he t x y).trans (congrArg (fun s ↦ e (a t x ⊗ₜ[ℂ] s)) ht)
  | add u v hu hv =>
    exact (hu.add hv).congr fun g ↦ ((congrArg (T g) (e.map_add u v)).trans
      ((T g).map_add (e u) (e v))).symm
private theorem continuous_global_unit_orbits {F : Type*} [Field F] [NumberField F]
    (f : SchwartzBruhat (Multiplicative 𝔸[F])) :
    Continuous fun u : IdeleGroup (𝓞 F) F ↦ schwartzBruhatUnitTranslate u f := by
  let I := IdeleGroup (𝓞 F) F
  let R := FiniteAdeleRing (𝓞 F) F
  let : LocallyCompactSpace I := (ideleGroup_topology F).2.1
  let πa : I →* (InfiniteAdeleRing F)ˣ := Units.map (MonoidHom.fst _ _)
  let πb : I →* Rˣ := Units.map (MonoidHom.snd _ _)
  have hπa : Continuous πa := continuous_fst.units_map _
  have hπb : Continuous πb := continuous_snd.units_map _
  let e := (adeleSchwartz_inductiveTensor_equiv F).choose
  have he := (adeleSchwartz_inductiveTensor_equiv F).choose_spec
  refine tensor_orbits_continuous (G := I) e (fun u ↦ unitTranslateEnd (R := 𝔸[F]) u)
    (fun u ↦ schwartzBruhatUnitTranslate (πa u)) (fun u ↦ schwartzBruhatUnitTranslate (πb u))
    (continuous_archUnitOrbit πa hπa) ?_ ?_ f
  · intro φ
    obtain ⟨hl, hc⟩ := finiteAdele_test_locallyConstant φ
    have H := locallyConstant_unit_family πb hπb (fun x ↦ φ (Multiplicative.ofAdd x)) hl hc
    refine (IsLocallyConstant.iff_eventually_eq _).mpr fun u ↦ ?_
    filter_upwards [H.eventually_eq u] with t ht
    exact Subtype.ext (funext fun x ↦ congrFun ht x.toAdd)
  · intro u a b
    apply Subtype.ext
    funext x
    exact (he a b (u.inv * x.toAdd)).trans
      (he (schwartzBruhatUnitTranslate (πa u) a) (schwartzBruhatUnitTranslate (πb u) b) x.toAdd).symm

private theorem global_unit_joint {F : Type*} [Field F] [NumberField F] :
    Continuous fun p : IdeleGroup (𝓞 F) F × SchwartzBruhat (Multiplicative 𝔸[F]) ↦
      schwartzBruhatUnitTranslate p.1 p.2 := by
  let E := SchwartzBruhat (Multiplicative 𝔸[F])
  let : LocallyCompactSpace (IdeleGroup (𝓞 F) F) := (ideleGroup_topology F).2.1
  let : LocallyCompactSpace 𝔸[F] := adele_locallyCompact F
  let : T2Space 𝔸[F] := (adeleHausdorff_ideleLocallyCompact F).1
  let : BarrelledSpace ℂ E := (adeleSchwartz_montel (F := F)).2.1
  let : PolynormableSpace ℂ E := (show IsNuclearTVS.{0} E from (adeleSchwartz_nuclear (F := F)).2).2.1
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  exact continuous_family_of_orbits (G := IdeleGroup (𝓞 F) F) (E := E) (fun u ↦ ⟨unitTranslateEnd (R := 𝔸[F]) u, continuous_unitTranslate (R := 𝔸[F]) u⟩)
    (continuous_global_unit_orbits (F := F))

/-- Descend a jointly continuous family through open quotient maps on both factors.
The stabilizing subgroup acts trivially on the quotient module. -/
private theorem descendQuotientAction {G E : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] (N : Subgroup G) [N.Normal] (K : Submodule ℂ E)
    (T : G →* (Module.End ℂ E)) (hc : Continuous fun p : G × E ↦ T p.1 p.2)
    (hs : ∀ g, K ≤ K.comap (T g)) (ht : ∀ g ∈ N, ∀ x, K.mkQ (T g x) = K.mkQ x) :
    ∃! ρ : G ⧸ N →* ((E ⧸ K) →L[ℂ] (E ⧸ K)),
      (Continuous fun p : (G ⧸ N) × (E ⧸ K) ↦ ρ p.1 p.2) ∧
      ∀ g x, ρ (QuotientGroup.mk g) (K.mkQ x) = K.mkQ (T g x) := by
  let L (g : G) : (E ⧸ K) →L[ℂ] (E ⧸ K) :=
    ⟨K.mapQ K (T g) (hs g), K.isQuotientMap_mkQ.continuous_iff.mpr
      (K.mkQL.continuous.comp (hc.comp (continuous_const.prodMk continuous_id)))⟩
  have hL (g : G) (x : E) : L g (K.mkQ x) = K.mkQ (T g x) := rfl
  let A : G →* ((E ⧸ K) →L[ℂ] (E ⧸ K)) :=
    { toFun := L
      map_one' := ContinuousLinearMap.ext fun x ↦ K.mkQ_surjective x |>.elim fun f hf ↦ by
        rw [← hf, hL, map_one]; rfl
      map_mul' := fun a b ↦ ContinuousLinearMap.ext fun x ↦ K.mkQ_surjective x |>.elim fun f hf ↦ by
        rw [← hf]
        exact (hL (a*b) f).trans (congrArg K.mkQ (DFunLike.congr_fun (T.map_mul a b) f)) }
  have hN : N ≤ A.ker := fun g hg ↦ ContinuousLinearMap.ext fun x ↦
    (K.mkQ_surjective x).elim fun f hf ↦ hf ▸ ht g hg f
  let ρ := QuotientGroup.lift N A hN
  have hprod := (QuotientGroup.isOpenQuotientMap_mk (N := N)).prodMap K.isOpenQuotientMap_mkQ
  refine ⟨ρ, ⟨hprod.isQuotientMap.continuous_iff.mpr (K.mkQL.continuous.comp hc),
    fun _ _ ↦ rfl⟩, ?_⟩
  intro τ hτ
  refine MonoidHom.ext fun a ↦ ContinuousLinearMap.ext fun x ↦ ?_
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨f, rfl⟩ := K.mkQ_surjective x
  exact hτ.2 g f

private theorem globalTheta_translate_apply (g : IdeleGroup (𝓞 F) F) (f : ℬ𝔽) (a : C𝔽) :
    adelicTheta (schwartzBruhatUnitTranslate g f) a = adelicTheta f ((QuotientGroup.mk g)⁻¹ * a) := by
  induction a using QuotientGroup.induction_on with | H x => ?_
  change _ = adelicTheta f (QuotientGroup.mk (g⁻¹ * x))
  rw [adelicTheta_mk (schwartzBruhatUnitTranslate g f) x, adelicTheta_mk f (g⁻¹ * x)]
  exact tsum_congr fun t ↦ congrArg (fun y ↦ f (Multiplicative.ofAdd y))
    (mul_left_comm g.inv (algebraMap F 𝔸[F] (t : F)) x.val)

private theorem thetaAction_of_translate {G E A : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [TopologicalSpace A] (N : Subgroup G) [N.Normal]
    (θ : E →ₗ[ℂ] C(A, ℂ)) (T : G →* Module.End ℂ E) (t : G → E → E)
    (ht : ∀ g x, T g x = t g x)
    (hc : Continuous fun p : G × E ↦ t p.1 p.2) (r : G → A → A)
    (hr : ∀ g f a, θ (t g f) a = θ f (r g a))
    (hN : ∀ g ∈ N, ∀ f a, θ f (r g a) = θ f a) :
    ∃! ρ : G ⧸ N →* ((E ⧸ θ.ker) →L[ℂ] (E ⧸ θ.ker)),
      (Continuous fun p : (G ⧸ N) × (E ⧸ θ.ker) ↦ ρ p.1 p.2) ∧
      ∀ g x, ρ (QuotientGroup.mk g) (Submodule.Quotient.mk x) = Submodule.Quotient.mk (t g x) := by
  have he : t = fun g x ↦ T g x := funext fun g ↦ funext fun x ↦ (ht g x).symm
  subst t
  apply descendQuotientAction N θ.ker T hc
  · intro g f hf
    exact ContinuousMap.ext fun a ↦ (hr g f a).trans
      (congrArg (fun φ : C(A, ℂ) ↦ φ (r g a)) (LinearMap.mem_ker.mp hf))
  · intro g hg f
    apply (Submodule.Quotient.eq _).mpr
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero]
    exact ContinuousMap.ext fun a ↦ (hr g f a).trans (hN g hg f a)

/-- The radial dilation difference on the added finite place has only finitely
many valuation shells, uniformly in the other variables of a pure tensor. -/
theorem finitePlaceSchwartz_dilation_sub_valuation (w : HeightOneSpectrum (𝓞 F))
    (f : SchwartzBruhat (Multiplicative (w.adicCompletion F))) (c : (w.adicCompletion F)ˣ)
    (hr : ∀ x y : w.adicCompletion F, x ≠ 0 → y ≠ 0 → Valued.v x = Valued.v y →
      f (Multiplicative.ofAdd x) = f (Multiplicative.ofAdd y)) :
    ∃ b : WithZero (Multiplicative ℤ) →₀ ℂ, ∀ x : w.adicCompletion F, x ≠ 0 →
      b (Valued.v x) = f (Multiplicative.ofAdd x) - f (Multiplicative.ofAdd (c.val * x)) := by
  obtain ⟨hf, hc⟩ := (mem_finitePlaceSchwartz_iff F w _).mp ⟨f, fun _ ↦ rfl⟩
  exact exists_finsupp_valuation_dilation_sub Valued.v
    (fun x hx ↦ Valued.locally_const ((Valuation.ne_zero_iff _).mpr hx))
    _ hf hc hr c

private theorem sum_orbit_invariant {G E : Type*} [Group G] [AddCommMonoid E] [Module ℂ E]
    (r : G →* Module.End ℂ E) (f : E) (hf : (range fun g ↦ r g f).Finite) (g : G) :
    r g (∑ y ∈ hf.toFinset, y) = ∑ y ∈ hf.toFinset, y := by
  classical
  have he (a b : G) (x : E) : r (a * b) x = r a (r b x) := DFunLike.congr_fun (r.map_mul a b) x
  have hi (x : E) (h : x ∈ hf.toFinset) (a : G) : r a x ∈ hf.toFinset := by
    obtain ⟨b,rfl⟩ := hf.mem_toFinset.mp h
    exact hf.mem_toFinset.mpr ⟨a*b, he _ _ _⟩
  have hinv (a : G) (x : E) : r a⁻¹ (r a x) = x := by rw [← he, inv_mul_cancel, map_one]; rfl
  rw [map_sum]
  exact Finset.sum_bij' (fun a _ ↦ r g a) (fun a _ ↦ r g⁻¹ a)
    (fun a ha ↦ hi a ha g) (fun a ha ↦ hi a ha g⁻¹) (fun a _ ↦ hinv g a)
    (fun a _ ↦ by simpa using hinv g⁻¹ a) (fun _ _ ↦ rfl)

/-- Normalized averaging over the finite orbit under local units gives a radial
test function. Each dilation difference of that average has finite valuation support. -/
theorem finitePlaceSchwartz_average_dilation (w : HeightOneSpectrum (𝓞 F))
    (f : SchwartzBruhat (Multiplicative (w.adicCompletion F))) :
    ∃ O : Finset (SchwartzBruhat (Multiplicative (w.adicCompletion F))),
      (∀ h, h ∈ O ↔ ∃ u : (w.adicCompletionIntegers F).units, schwartzBruhatUnitTranslate u.val f = h) ∧
      ∀ c : (w.adicCompletion F)ˣ, ∃ b : WithZero (Multiplicative ℤ) →₀ ℂ,
        ∀ x : w.adicCompletion F, x ≠ 0 →
          b (Valued.v x) = (O.card : ℂ)⁻¹ * ∑ h ∈ O,
            (h (Multiplicative.ofAdd x) - h (Multiplicative.ofAdd (c.val * x))) := by
  classical
  let H := (w.adicCompletionIntegers F).units
  let : CompactSpace H := isCompact_iff_compactSpace.mp
    (Submonoid.units_isCompact (isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers w)))
  let r := (unitTranslateEnd (R := w.adicCompletion F)).comp H.subtype
  obtain ⟨hf,hc⟩ := (mem_finitePlaceSchwartz_iff F w _).mp ⟨f, fun _ ↦ rfl⟩
  have hloc := locallyConstant_unit_family (H.subtype : H → (w.adicCompletion F)ˣ)
    continuous_subtype_val (fun x ↦ f (Multiplicative.ofAdd x)) hf hc
  have hfinite : (range fun u : H ↦ r u f).Finite := by
    apply IsLocallyConstant.range_finite
    exact (IsLocallyConstant.iff_eventually_eq _).mpr fun u ↦
      (hloc.eventually_eq u).mono fun a h ↦ Subtype.ext h
  let O := hfinite.toFinset
  let avg := (O.card : ℂ)⁻¹ • ∑ h ∈ O, h
  refine ⟨O, fun h ↦ hfinite.mem_toFinset, fun c ↦ ?_⟩
  have hinv (a : H) : r a avg = avg :=
    (map_smul (r a) _ _).trans (congrArg ((O.card : ℂ)⁻¹ • ·) (sum_orbit_invariant r f hfinite a))
  have hr (x y : w.adicCompletion F) (hx : x ≠ 0) (hy : y ≠ 0) (he : Valued.v x = Valued.v y) :
      avg (Multiplicative.ofAdd x) = avg (Multiplicative.ofAdd y) := by
    let u := Units.mk0 y hy / Units.mk0 x hx
    have hu : u ∈ H := HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mpr
      (show Valued.v (y / x) = 1 by rw [map_div₀, he, div_self ((Valuation.ne_zero_iff _).mpr hy)])
    have hu' : u.val * x = y := div_mul_cancel₀ _ hx
    have hh := congrArg (fun h : SchwartzBruhat (Multiplicative (w.adicCompletion F)) ↦
      h (Multiplicative.ofAdd x)) (hinv (⟨u,hu⟩ : H)⁻¹)
    exact hh.symm.trans (congrArg (fun z ↦ avg (Multiplicative.ofAdd z)) hu')
  obtain ⟨b,hb⟩ := finitePlaceSchwartz_dilation_sub_valuation w avg c hr
  refine ⟨b, fun x hx ↦ (hb x hx).trans ?_⟩
  have havg (y : w.adicCompletion F) : avg (Multiplicative.ofAdd y) =
      (O.card : ℂ)⁻¹ * ∑ h ∈ O, h (Multiplicative.ofAdd y) := by
    change (O.card : ℂ)⁻¹ * ((∑ h ∈ O, h : SchwartzBruhat _) (Multiplicative.ofAdd y)) = _
    exact congrArg ((O.card : ℂ)⁻¹ * ·) (map_sum (schwartzBruhatEvalCLM (Multiplicative.ofAdd y)) _ _)
  rw [havg, havg, ← mul_sub, Finset.sum_sub_distrib]

end UnitActions

/-- Paper: Theorem 5.2.1.1(2), p. 230.
Left translation by the global idele class group induces a jointly continuous linear
action on the global theta quotient.
Deviation: The action is characterized on test functions by idele representatives. -/
theorem existsUnique_globalThetaAction :
    ∃! ρ : C𝔽 →* (Θ𝔽 →L[ℂ] Θ𝔽),
      Continuous (fun p : C𝔽 × Θ𝔽 ↦ ρ p.1 p.2) ∧
      ∀ (g : IdeleGroup (𝓞 F) F) (f : ℬ𝔽),
        ρ (QuotientGroup.mk g) (Submodule.Quotient.mk f) =
          Submodule.Quotient.mk (schwartzBruhatUnitTranslate g f) := by
  let π : IdeleGroup (𝓞 F) F →* C𝔽 := QuotientGroup.mk' _
  have h (g : IdeleGroup (𝓞 F) F) (hg : g ∈ IdeleGroup.principalSubgroup (𝓞 F) F)
      (f : ℬ𝔽) (a : C𝔽) : adelicTheta f ((π g)⁻¹ * a) = adelicTheta f a :=
    congrArg (adelicTheta f) ((congrArg (fun z : C𝔽 ↦ z⁻¹ * a)
      ((QuotientGroup.eq_one_iff g).mpr hg)).trans ((congrArg (· * a) inv_one).trans (one_mul a)))
  let N := IdeleGroup.principalSubgroup (𝓞 F) F
  let Tt := unitTranslateEnd (R := 𝔸[F])
  let θ := adelicThetaLinearMap F
  let t := schwartzBruhatUnitTranslate (R := 𝔸[F])
  let r (g : IdeleGroup (𝓞 F) F) (a : C𝔽) := (π g)⁻¹ * a
  have hr : ∀ g f a, θ (t g f) a = θ f (r g a) := globalTheta_translate_apply (F := F)
  have hc : Continuous (fun p : IdeleGroup (𝓞 F) F × ℬ𝔽 ↦ t p.1 p.2) :=
    global_unit_joint (F := F)
  have htt : ∀ g f, Tt g f = t g f := fun _ _ ↦ rfl
  have result := thetaAction_of_translate (G := IdeleGroup (𝓞 F) F) (E := ℬ𝔽) (A := C𝔽)
    N θ Tt t htt hc r hr h
  with_reducible exact result

private theorem insert_translate_eq (u : (integralAdelesOutside F S)ˣ) (f : ℬₛ(S)) :
    let g := integralIdeleInsertion F S u
    let gS := Units.map (adeleProjection F S).toMonoidHom g
    sAdeleSchwartzToGlobal F S (schwartzBruhatUnitTranslate gS f) =
      schwartzBruhatUnitTranslate g (sAdeleSchwartzToGlobal F S f) := by
  classical
  let g := integralIdeleInsertion F S u
  let gS := Units.map (adeleProjection F S).toMonoidHom g
  refine Subtype.ext (funext fun x ↦ ?_)
  let y := x.toAdd
  have h := mul_integralUnit_mem_iff u⁻¹ y
  change g.inv * y ∈ integralAdelesOutside F S ↔ y ∈ integralAdelesOutside F S at h
  refine (toGlobal_apply_integral (schwartzBruhatUnitTranslate gS f) y).trans ?_
  refine Eq.trans (if_congr h.symm ?_ rfl) (toGlobal_apply_integral f (g.inv * y)).symm
  exact congrArg (fun t ↦ f (Multiplicative.ofAdd t)) (map_mul (adeleProjection F S) g.inv y).symm

private theorem insert_translate_of_mem_range {g : IdeleGroup (𝓞 F) F}
    (hg : g ∈ Set.range (integralIdeleInsertion F T)) (f : ℬₛ(T)) :
    sAdeleSchwartzToGlobal F T
      (schwartzBruhatUnitTranslate (Units.map (adeleProjection F T).toMonoidHom g) f) =
        schwartzBruhatUnitTranslate g (sAdeleSchwartzToGlobal F T f) := by
  obtain ⟨u, rfl⟩ := hg
  exact insert_translate_eq u f

private theorem localTheta_translate_apply (g x : (SAdeleRing F S)ˣ) (f : ℬₛ(S)) :
    sLocalAdelicTheta F S (schwartzBruhatUnitTranslate g f) x = sLocalAdelicTheta F S f (g⁻¹ * x) := by
  let d := (Units.map ((adeleProjection F S).comp (integralAdelesOutside F S).subtype).toMonoidHom).comp
    (Units.map (integralAdeleDiagonal F S).toMonoidHom)
  refine (sLocalAdelicTheta_apply F S (schwartzBruhatUnitTranslate g f) x).trans
    (Eq.trans ?_ (sLocalAdelicTheta_apply F S f (g⁻¹ * x)).symm)
  exact tsum_congr fun t ↦ congrArg (fun y ↦ f (Multiplicative.ofAdd y)) (mul_left_comm g.inv (d t).val x.val)

private theorem test_insert_translate (g : (SAdeleRing F S)ˣ) (f : ℬₛ(S)) :
    sAdeleSchwartzToGlobal F S (schwartzBruhatUnitTranslate g f) =
      schwartzBruhatUnitTranslate (sIdeleInsertion F S g) (sAdeleSchwartzToGlobal F S f) := by
  let j := sIdeleInsertion F S
  have hu : j g ∈ Set.range (integralIdeleInsertion F S) :=
    (mem_range_integralIdeleInsertion F S (j g)).mpr fun v hv ↦ by
      refine ⟨(sIdeleInsertion_apply F S g).2.2 v hv ▸ (v.adicCompletionIntegers F).one_mem, ?_⟩
      have h' : (j g).inv.2 v = 1 := (congrArg (fun x : IdeleGroup (𝓞 F) F ↦ x.val.2 v)
        (map_inv j g).symm).trans ((sIdeleInsertion_apply F S g⁻¹).2.2 v hv)
      exact h' ▸ (v.adicCompletionIntegers F).one_mem
  have hp : Units.map (adeleProjection F S).toMonoidHom (j g) = g := Units.ext
    (Prod.ext (sIdeleInsertion_apply F S g).1 (funext (sIdeleInsertion_apply F S g).2.1))
  exact (congrArg (fun v ↦ sAdeleSchwartzToGlobal F S (schwartzBruhatUnitTranslate v f)) hp.symm).trans
    (insert_translate_of_mem_range (F := F) (T := S) (g := j g) hu f)

private theorem joint_of_inducing {H G X Y : Type*} [TopologicalSpace H] [TopologicalSpace G]
    [TopologicalSpace X] [TopologicalSpace Y] (a : H → X → X) (b : G → Y → Y)
    (u : H → G) (i : X → Y) (hu : Continuous u) (hi : IsInducing i)
    (hb : Continuous fun p : G × Y ↦ b p.1 p.2)
    (h : ∀ v x, i (a v x) = b (u v) (i x)) : Continuous fun p : H × X ↦ a p.1 p.2 :=
  hi.continuous_iff.mpr <| (hb.comp ((hu.comp continuous_fst).prodMk
    (hi.continuous.comp continuous_snd))).congr fun p ↦ (h p.1 p.2).symm

private theorem local_unit_joint :
    Continuous fun p : (SAdeleRing F S)ˣ × ℬₛ(S) ↦ schwartzBruhatUnitTranslate p.1 p.2 :=
  joint_of_inducing (H := (SAdeleRing F S)ˣ) (G := IdeleGroup (𝓞 F) F)
    (X := ℬₛ(S)) (Y := ℬ𝔽) schwartzBruhatUnitTranslate schwartzBruhatUnitTranslate
    (sIdeleInsertion F S) (sAdeleSchwartzToGlobal F S) (isClosedEmbedding_sIdeleInsertion F S).continuous
    (sAdeleSchwartzToGlobal_isEmbedding F S).isInducing (global_unit_joint (F := F))
    (test_insert_translate (F := F) (S := S))

private theorem mk_inv_mul_of_mem {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    {g : G} (hg : g ∈ N) (a : G) :
    (QuotientGroup.mk (g⁻¹ * a) : G ⧸ N) = QuotientGroup.mk a := by
  let π := QuotientGroup.mk' N
  change π (g⁻¹ * a) = π a
  rw [map_mul, map_inv, show π g = 1 from (QuotientGroup.eq_one_iff g).mpr hg, inv_one, one_mul]

/-- Paper: Theorem 5.2.1.1(2), p. 230.
Left translation by the S-idele quotient induces a jointly continuous linear
action on the S-local theta quotient.
Deviation: The action is characterized on test functions by S-idele representatives. -/
theorem existsUnique_sLocalThetaAction :
    ∃! ρ : Jₛ(S) →* (Θₛ(S) →L[ℂ] Θₛ(S)),
      Continuous (fun p : Jₛ(S) × Θₛ(S) ↦ ρ p.1 p.2) ∧
      ∀ (g : (SAdeleRing F S)ˣ) (f : ℬₛ(S)),
        ρ (QuotientGroup.mk g) (Submodule.Quotient.mk f) =
          Submodule.Quotient.mk (schwartzBruhatUnitTranslate g f) := by
  let N := Subgroup.map (Units.map ((adeleProjection F S).comp (integralAdelesOutside F S).subtype).toMonoidHom)
    (MonoidHom.range (Units.map (integralAdeleDiagonal F S).toMonoidHom))
  have h (g : (SAdeleRing F S)ˣ) (hg : g ∈ N) (f : ℬₛ(S)) (a : (SAdeleRing F S)ˣ) :
      sLocalAdelicTheta F S f (g⁻¹ * a) = sLocalAdelicTheta F S f a :=
    sLocalAdelicTheta_factorsThrough F S f (mk_inv_mul_of_mem N hg a)
  let Tt := unitTranslateEnd (R := SAdeleRing F S)
  let θ := sLocalAdelicTheta F S
  let t := schwartzBruhatUnitTranslate (R := SAdeleRing F S)
  let r (g a : (SAdeleRing F S)ˣ) := g⁻¹ * a
  have hr : ∀ g f a, θ (t g f) a = θ f (r g a) :=
    fun g f a ↦ localTheta_translate_apply (F := F) (S := S) g a f
  have hc : Continuous (fun p : (SAdeleRing F S)ˣ × ℬₛ(S) ↦ t p.1 p.2) :=
    local_unit_joint (F := F) (S := S)
  have htt : ∀ g f, Tt g f = t g f := fun _ _ ↦ rfl
  have result := thetaAction_of_translate (G := (SAdeleRing F S)ˣ) (E := ℬₛ(S)) (A := (SAdeleRing F S)ˣ)
    N θ Tt t htt hc r hr h
  with_reducible exact result

private theorem insert_mem_larger (hST : S ⊆ T) (u : (integralAdelesOutside F S)ˣ) :
    integralIdeleInsertion F S u ∈ Set.range (integralIdeleInsertion F T) := by
  let g := integralIdeleInsertion F S u
  have hg : g ∈ Set.range (integralIdeleInsertion F S) := ⟨u, rfl⟩
  exact (mem_range_integralIdeleInsertion F T g).mpr fun v hv ↦
    (mem_range_integralIdeleInsertion F S g).mp hg v (fun h ↦ hv (hST h))

private theorem testTransition_translate_eq (hST : S ⊆ T)
    (u : (integralAdelesOutside F S)ˣ) (f : ℬₛ(S)) :
    let g := integralIdeleInsertion F S u
    let gS := Units.map (adeleProjection F S).toMonoidHom g
    let gT := Units.map (adeleProjection F T).toMonoidHom g
    sAdeleSchwartzTransition F hST (schwartzBruhatUnitTranslate gS f) =
      schwartzBruhatUnitTranslate gT (sAdeleSchwartzTransition F hST f) := by
  let g := integralIdeleInsertion F S u
  let gS := Units.map (adeleProjection F S).toMonoidHom g
  let gT := Units.map (adeleProjection F T).toMonoidHom g
  have hTS (k : ℬₛ(S)) : sAdeleSchwartzToGlobal F T (sAdeleSchwartzTransition F hST k) =
      sAdeleSchwartzToGlobal F S k := DFunLike.congr_fun (sAdeleSchwartzToGlobal_comp F hST) k
  have hT := insert_translate_of_mem_range (insert_mem_larger hST u) (sAdeleSchwartzTransition F hST f)
  exact (sAdeleSchwartzToGlobal_isEmbedding F T).injective
    ((hTS _).trans ((insert_translate_eq u f).trans
        ((congrArg (schwartzBruhatUnitTranslate g) (hTS f).symm).trans hT.symm)))

/-- Paper: Theorem 5.2.1.1(2), p. 230.
The S-to-T theta transition intertwines the actions of the S-idele classes.
Deviation: On an integral-outside-S idele representative, the two actions are
given by projecting it to S and T, respectively. -/
theorem sLocalThetaTransition_equivariant (hST : S ⊆ T)
    (u : (integralAdelesOutside F S)ˣ) (f : ℬₛ(S)) :
    let g := integralIdeleInsertion F S u
    let gS := Units.map (adeleProjection F S).toMonoidHom g
    let gT := Units.map (adeleProjection F T).toMonoidHom g
    sLocalThetaTransition hST (Submodule.Quotient.mk (schwartzBruhatUnitTranslate gS f)) =
      Submodule.Quotient.mk
        (schwartzBruhatUnitTranslate gT (sAdeleSchwartzTransition F hST f)) := congrArg (Kₛ(T)).mkQ (testTransition_translate_eq hST u f)

/-- Paper: Theorem 5.2.1.1(3), p. 230.
The S-local insertion intertwines the actions of S-idele classes through their
projection to the S-idele quotient and their inclusion in the global classes.
Deviation: The equation is on representatives of the acting group and the theta quotient. -/
theorem sLocalThetaToGlobal_equivariant (u : (integralAdelesOutside F S)ˣ) (f : ℬₛ(S)) :
    let g := integralIdeleInsertion F S u
    let gS := Units.map (adeleProjection F S).toMonoidHom g
    sLocalThetaToGlobal F S (Submodule.Quotient.mk (schwartzBruhatUnitTranslate gS f)) =
      Submodule.Quotient.mk
        (schwartzBruhatUnitTranslate g (sAdeleSchwartzToGlobal F S f)) := congrArg (K𝔽).mkQ (insert_translate_eq u f)

section OnePlaceRetraction

/-! To retract a one-place enlargement, average its theta values over the new unit group
and subtract the same average shifted by an inverse uniformizer. On a pure tensor the
difference has finitely many valuation shells, each giving a translate of the old test.
Separate continuity on tensors and descent along the theta quotient extend this formula
to a continuous linear left inverse on the entire larger space. -/

open TensorProduct Set
open scoped TensorProduct Classical


/-- Recover a quotient-valued operator from its separated scalar evaluations on each tensor slice. -/
private theorem recover_tensor_quotient {X V Z Q A : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [PolynormableSpace ℂ X] [T2Space X]
    [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] [PolynormableSpace ℂ V] [T2Space V]
    [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z] [PolynormableSpace ℂ Z] [T2Space Z]
    [AddCommGroup Q] [Module ℂ Q] [TopologicalSpace Q]
    (q : InductiveTensor X V →ₗ[ℂ] Q) (hq : IsQuotientMap q)
    (ev : Z →ₗ[ℂ] (A → ℂ)) (hinj : Injective ev) (sample : Q →ₗ[ℂ] (A → ℂ))
    (hfin : ∀ L : V →ₗ[ℂ] Z, Continuous L)
    (hslice : ∀ v : V, ∃ L : X →L[ℂ] Z, ∀ x : X, ev (L x) = sample (q (x ⊗ₜ[ℂ] v))) :
    ∃ r : Q →L[ℂ] Z, ∀ z, ev (r z) = sample z := by
  have hrange (z : Q) : sample z ∈ ev.range := by
    obtain ⟨t, rfl⟩ := hq.surjective z
    let q' : X ⊗[ℂ] V →ₗ[ℂ] Q := q
    change sample (q' t) ∈ ev.range
    induction t using TensorProduct.inductionOn with
    | tmul x v =>
      obtain ⟨L, hL⟩ := hslice v
      exact ⟨L x, hL x⟩
    | add x y hx hy => rw [q'.map_add x y, sample.map_add]; exact ev.range.add_mem hx hy
  let e := LinearEquiv.ofInjective ev hinj
  let r := e.symm.toLinearMap.comp (sample.codRestrict ev.range hrange)
  have he (z : Q) : ev (r z) = sample z :=
    congrArg Subtype.val (e.apply_symm_apply ⟨sample z, hrange z⟩)
  refine ⟨⟨r, hq.continuous_iff.mpr ((continuous_inductiveTensor_iff (r.comp q)).mpr ⟨?_, ?_⟩)⟩, he⟩
  · intro x
    exact hfin ((r.comp q).comp (TensorProduct.mk ℂ X V x))
  · intro v
    obtain ⟨L, hL⟩ := hslice v
    exact L.continuous.congr fun x ↦ hinj ((hL x).trans (he (q (x ⊗ₜ[ℂ] v))).symm)

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "B(" S ")" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "Y(" S ")" => SchwartzBruhat (Multiplicative (FinitePlaceProduct F S))
local notation "Q(" S ")" => SLocalAdelicThetaSpace F S
local notation "K(" S ")" => LinearMap.ker (sLocalAdelicTheta F S)

private def testValues {X A : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace A]
    (θ : X →ₗ[ℂ] C(A, ℂ)) : (X ⧸ θ.ker) →ₗ[ℂ] (A → ℂ) :=
  LinearMap.pi fun a ↦ (ContinuousMap.evalCLM ℂ a).toLinearMap.comp (θ.ker.liftQ θ le_rfl)

private theorem testValues_injective {X A : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace A]
    (θ : X →ₗ[ℂ] C(A, ℂ)) : Injective (testValues θ) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro z hz
  obtain ⟨x, rfl⟩ := θ.ker.mkQ_surjective z
  exact (Submodule.Quotient.mk_eq_zero _).mpr (ContinuousMap.ext fun a ↦ congrFun (LinearMap.mem_ker.mp hz) a)

private def localValues (F : Type*) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) :
    SLocalAdelicThetaSpace F S →ₗ[ℂ] ((SAdeleRing F S)ˣ → ℂ) :=
  testValues (sLocalAdelicTheta F S)

private def localClass (S : Finset V) (f : B(S)) : Q(S) := Submodule.Quotient.mk f

/-- Separate continuity for the inductive tensor product descends through the larger quotient. -/
private theorem quotient_retraction_of_classes {X N Y A B : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [PolynormableSpace ℂ X] [T2Space X]
    [AddCommGroup N] [Module ℂ N] [TopologicalSpace N] [PolynormableSpace ℂ N] [T2Space N]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [TopologicalSpace A] [TopologicalSpace B]
    (θ : X →ₗ[ℂ] C(A, ℂ)) (τ : Y →ₗ[ℂ] C(B, ℂ))
    [T2Space (X ⧸ θ.ker)] [PolynormableSpace ℂ (X ⧸ θ.ker)]
    (j : X →ₗ[ℂ] Y) (hj : θ.ker ≤ τ.ker.comap j) (e : InductiveTensor X N ≃L[ℂ] Y)
    (hfin : (inferInstance : TopologicalSpace N) = (inferInstance : TopologicalSpace (FinestLocallyConvex N)))
    (sample : (Y ⧸ τ.ker) →ₗ[ℂ] (A → ℂ))
    (hslice : ∀ v : N, ∃ L : X →L[ℂ] (X ⧸ θ.ker), ∀ x,
      testValues θ (L x) = sample (Submodule.Quotient.mk (e (x ⊗ₜ[ℂ] v))))
    (hfix : ∀ x, sample (Submodule.Quotient.mk (j x)) = ⇑(θ x)) :
    ∃ r : (Y ⧸ τ.ker) →L[ℂ] (X ⧸ θ.ker), LeftInverse r (θ.ker.mapQ τ.ker j hj) := by
  let q := τ.ker.mkQ.comp e.toLinearMap
  have hq : IsQuotientMap q := τ.ker.isQuotientMap_mkQ.comp e.toHomeomorph.isQuotientMap
  have hc (L : N →ₗ[ℂ] (X ⧸ θ.ker)) : Continuous L :=
    Eq.mpr (congrArg (fun t ↦ @Continuous N (X ⧸ θ.ker) t _ L) hfin) (continuous_of_finestLocallyConvex N L)
  obtain ⟨r, hr⟩ := recover_tensor_quotient (X := X) («V» := N) q hq _ (testValues_injective θ) sample hc hslice
  refine ⟨r, fun z ↦ ?_⟩
  obtain ⟨x, rfl⟩ := θ.ker.mkQ_surjective z
  exact testValues_injective θ ((hr _).trans (hfix x))

open Classical in
private theorem finiteTheta_retraction_of_classes {S T : Finset V} (h : S ⊆ T)
    (e : InductiveTensor B(S) Y(T \ S) ≃L[ℂ] B(T))
    (sample : Q(T) →ₗ[ℂ] ((SAdeleRing F S)ˣ → ℂ))
    (hslice : ∀ v : Y(T \ S), ∃ L : B(S) →L[ℂ] Q(S), ∀ x,
      localValues F S (L x) = sample (localClass (F := F) T (e (x ⊗ₜ[ℂ] v))))
    (hfix : ∀ f : B(S), sample (localClass (F := F) T (sAdeleSchwartzTransition F h f)) =
      ⇑(sLocalAdelicTheta F S f)) :
    ∃ r : Q(T) →L[ℂ] Q(S), LeftInverse r (sLocalThetaTransition (F := F) h) := by
  classical
  let D := T \ S
  let : T2Space B(S) := (sAdeleSchwartz_strictLF F S).1
  let : T2Space Y(D) := (finiteProduct_tailSchwartz_strictLF F D ∅).1.1
  let : T2Space Q(S) := sLocalAdelicThetaSpace_t2_of_isClosed (F := F) (S := S)
    (sLocalAdelicTheta_ker_isClosed (F := F) (S := S))
  let : PolynormableSpace ℂ Q(S) := sLocalAdelicThetaSpace_polynormable (F := F) (S := S)
  change ∃ r : Q(T) →L[ℂ] Q(S), LeftInverse r ((K(S)).mapQ (K(T)) (sAdeleSchwartzTransition F h)
    (sLocalThetaTransition_preserves_kernel (F := F) h))
  unfold localClass at hslice hfix
  unfold localValues at hslice
  with_reducible_and_instances
    exact quotient_retraction_of_classes (X := B(S)) (N := Y(D)) (Y := B(T))
      (A := (SAdeleRing F S)ˣ) (B := (SAdeleRing F T)ˣ) (sLocalAdelicTheta F S) (sLocalAdelicTheta F T)
      (sAdeleSchwartzTransition F h) (sLocalThetaTransition_preserves_kernel (F := F) h) e
      (finiteProduct_tailSchwartz_finestTopology F D ∅).1 sample hslice hfix

set_option quotPrecheck false in
local notation "H(" v ")" => (HeightOneSpectrum.adicCompletionIntegers F v).units

open Classical in
private def newUnits (S : Finset V) (v : V) (x : (SAdeleRing F S)ˣ)
    (u : (v.adicCompletion F)ˣ) (w : ↥(insert v S)) : (w.val.adicCompletion F)ˣ := by
  classical
  let split (T : Finset V) := ContinuousMulEquiv.prodUnits (InfiniteAdeleRing F) (FinitePlaceProduct F T)
  let old := ContinuousMulEquiv.piUnits (M := fun w : S ↦ w.val.adicCompletion F) ((split S x).2)
  exact if hw : w.val = v then hw.symm ▸ u else old ⟨w.val, (Finset.mem_insert.mp w.property).resolve_left hw⟩

open Classical in
private def onePlaceIdele (S : Finset V) (v : V) (x : (SAdeleRing F S)ˣ) :
    C((v.adicCompletion F)ˣ, (SAdeleRing F (insert v S))ˣ) := by
  classical
  let split (T : Finset V) := ContinuousMulEquiv.prodUnits (InfiniteAdeleRing F) (FinitePlaceProduct F T)
  let old := ContinuousMulEquiv.piUnits (M := fun w : S ↦ w.val.adicCompletion F) ((split S x).2)
  let fin := ContinuousMulEquiv.piUnits (M := fun w : ↥(insert v S) ↦ w.val.adicCompletion F)
  let j := newUnits S v x
  refine ⟨fun u ↦ (split (insert v S)).symm ((split S x).1, fin.symm (j u)),
    (split (insert v S)).symm.continuous.comp (continuous_const.prodMk
      (fin.symm.continuous.comp (continuous_pi fun w ↦ ?_)))⟩
  have hcast (v₁ v₂ : V) (h : v₁ = v₂) : Continuous (fun u : (v₁.adicCompletion F)ˣ ↦ (h ▸ u : (v₂.adicCompletion F)ˣ)) := by
    cases h
    exact continuous_id
  by_cases hw : w.val = v
  · simpa only [j, newUnits, dite_eq_left hw] using hcast _ _ hw.symm
  · simp only [j, newUnits, dite_eq_right hw]
    exact continuous_const

open TensorProduct
open scoped TensorProduct Classical
private theorem new_coord_eq {S : Finset V} {v : V} (w : ↥(insert v S \ S)) : w.val = v := by
  obtain ⟨ht, hs⟩ := Finset.mem_sdiff.mp w.property
  exact (Finset.mem_insert.mp ht).resolve_right hs

private def newCoords {S : Finset V} (v : V) (hv : v ∉ S) :
    v.adicCompletion F ≃ₜ FinitePlaceProduct F (insert v S \ S) := by
  let w : ↥(insert v S \ S) := ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_insert_self _ _, hv⟩⟩
  let : Unique ↥(insert v S \ S) := ⟨⟨w⟩, fun z ↦ Subtype.ext (new_coord_eq z)⟩
  exact (Homeomorph.piUnique (fun z : ↥(insert v S \ S) ↦ z.val.adicCompletion F)).symm

private theorem coordinates_old {S : Finset V} {v : V} (hv : v ∉ S) (x : (SAdeleRing F S)ˣ)
    (u : (v.adicCompletion F)ˣ) (t : Fˣ) :
    let T := insert v S
    let h := Finset.subset_insert v S
    let z := adeleProjection F T (algebraMap F 𝔸[F] t.val) * (onePlaceIdele S v x u).val
    (z.1, fun w : S ↦ z.2 ⟨w.val, h w.property⟩) =
      adeleProjection F S (algebraMap F 𝔸[F] t.val) * x.val := by
  dsimp only
  refine Prod.ext rfl (funext fun w ↦ ?_)
  have hw : w.val ≠ v := fun e ↦ hv (e ▸ w.property)
  let w' : ↥(insert v S) := ⟨w.val, (Finset.subset_insert v S) w.property⟩
  have h : (newUnits S v x u w').val = x.val.2 w := by
    simp only [newUnits, show w'.val ≠ v from hw, dite_false]
    rfl
  exact congrArg ((algebraMap F (w.val.adicCompletion F) t.val) * ·) h

private theorem coordinates_new {S : Finset V} {v : V} (hv : v ∉ S) (x : (SAdeleRing F S)ˣ)
    (u : (v.adicCompletion F)ˣ) (t : Fˣ) :
    let T := insert v S
    let z := adeleProjection F T (algebraMap F 𝔸[F] t.val) * (onePlaceIdele S v x u).val
    (fun w : ↥(T \ S) ↦ z.2 ⟨w.val, (Finset.mem_sdiff.mp w.property).1⟩) =
      newCoords v hv (algebraMap F (v.adicCompletion F) t.val * u.val) := by
  dsimp only
  apply (newCoords v hv).symm.injective
  rw [Homeomorph.symm_apply_apply]
  let w' : ↥(insert v S) := ⟨v, Finset.mem_insert_self _ _⟩
  have h : (newUnits S v x u w').val = u.val := by
    simp only [newUnits, show w'.val = v from rfl, dite_true]
    rfl
  exact congrArg ((algebraMap F (v.adicCompletion F) t.val) * ·) h

private theorem newTest_exists {S : Finset V} {v : V} (hv : v ∉ S)
    (g : SchwartzBruhat (Multiplicative (FinitePlaceProduct F (insert v S \ S)))) :
    ∃ φ : SchwartzBruhat (Multiplicative (v.adicCompletion F)), ∀ x,
      φ (Multiplicative.ofAdd x) = g (Multiplicative.ofAdd (newCoords v hv x)) := by
  apply (mem_finitePlaceSchwartz_iff F v _).mpr
  let D := insert v S \ S
  let : TotallyDisconnectedSpace (Multiplicative (FinitePlaceProduct F D)) :=
    inferInstanceAs (TotallyDisconnectedSpace (∀ w : D, w.val.adicCompletion F))
  obtain ⟨hl, hc⟩ := schwartzBruhat_locallyConstant_compactSupport (finitePlaceProduct_compact_subset_subgroup F D) g
  exact ⟨hl.comp_continuous (continuous_ofAdd.comp (newCoords v hv).continuous),
    hc.comp_homeomorph (newCoords v hv)⟩

/-- The dilation difference vanishes near zero. Its Haar averages are constant on valuation
shells and are supported on the finite valuation image of a compact set. -/
private theorem shell_weights (w : V) [MeasurableSpace H(w)] [BorelSpace H(w)] (ν : Measure H(w))
    [ν.IsMulLeftInvariant] (φ : w.adicCompletion F → ℂ) (hl : IsLocallyConstant φ)
    (hc : HasCompactSupport φ) (c : (w.adicCompletion F)ˣ) :
    ∃ b : WithZero (Multiplicative ℤ) →₀ ℂ, ∀ x : w.adicCompletion F, x ≠ 0 →
      b (Valued.v x) = ∫ u : H(w), φ (x * u.val.val) - φ (c.val * (x * u.val.val)) ∂ν := by
  classical
  let K := w.adicCompletion F
  let D (x : K) := φ x - φ (c.val * x)
  let hdil := Homeomorph.mulLeft₀ c.val c.ne_zero
  have hd : HasCompactSupport D := hc.sub (hc.comp_homeomorph hdil)
  have hloc : IsLocallyConstant D := hl.comp₂ (hl.comp_continuous hdil.continuous) (· - ·)
  have hzero : 0 ∉ tsupport D := by
    have hz : D 0 = 0 := by simp [D]
    have hcl : IsClosed (support D) := (hloc.isClopen_fiber 0).isOpen.isClosed_compl
    exact fun h ↦ (hcl.closure_eq ▸ h : 0 ∈ support D) hz
  let Z := tsupport D
  let : CompactSpace Z := isCompact_iff_compactSpace.mp hd
  have hfinite : (Valued.v '' Z).Finite := by
    rw [image_eq_range]
    apply IsLocallyConstant.range_finite
    exact (IsLocallyConstant.iff_eventually_eq _).mpr fun x ↦
      continuous_subtype_val.continuousAt (Valued.locally_const
        ((Valuation.ne_zero_iff _).mpr fun h ↦ hzero (h ▸ x.property)))
  let β (x : K) := ∫ u : H(w), D (x * u.val.val) ∂ν
  have hinv (x y : K) (hx : x ≠ 0) (hy : y ≠ 0) (he : Valued.v x = Valued.v y) : β x = β y := by
    let d := Units.mk0 y hy / Units.mk0 x hx
    have hmem : d ∈ H(w) := HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mpr
      (show Valued.v (y / x) = 1 by rw [map_div₀, he, div_self ((Valuation.ne_zero_iff _).mpr hy)])
    let a : H(w) := ⟨d, hmem⟩
    have heq (u : H(w)) : D (x * (a * u).val.val) = D (y * u.val.val) := by
      apply congrArg D
      change x * ((y / x) * u.val.val) = _
      rw [← mul_assoc, mul_div_cancel₀ y hx]
    exact (integral_mul_left_eq_self (μ := ν) (fun u : H(w) ↦ D (x * u.val.val)) a).symm.trans
      (integral_congr_ae (.of_forall heq))
  let b (r : WithZero (Multiplicative ℤ)) :=
    if h : ∃ x : K, x ≠ 0 ∧ Valued.v x = r then β h.choose else 0
  have hb (x : K) (hx : x ≠ 0) : b (Valued.v x) = β x := by
    have h : ∃ y : K, y ≠ 0 ∧ Valued.v y = Valued.v x := ⟨x, hx, rfl⟩
    exact (dite_eq_left h).trans (hinv _ _ h.choose_spec.1 hx h.choose_spec.2)
  have hsupport : (support b).Finite := hfinite.subset fun r hr ↦ by
    by_cases h : ∃ x : K, x ≠ 0 ∧ Valued.v x = r
    · obtain ⟨x, hx, rfl⟩ := h
      have hu : ∃ u : H(w), D (x * u.val.val) ≠ 0 := by
        by_contra! hn
        apply hr
        rw [hb x hx]
        simp [β, hn]
      obtain ⟨u, hu⟩ := hu
      refine ⟨x * u.val.val, subset_closure hu, ?_⟩
      rw [map_mul, HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp u.property, mul_one]
    · exact (hr (dite_eq_right h)).elim
  exact ⟨Finsupp.ofSupportFinite b hsupport, hb⟩

open Set in
private theorem integral_series {ι Z P : Type*} [Countable ι] [TopologicalSpace Z]
    [TopologicalSpace P] [MeasurableSpace P] [BorelSpace P]
    (ν : Measure P) [IsFiniteMeasure ν] (p : C(P, Z)) (t : ι → Z → ℂ)
    (ht : ∀ i, Continuous (t i)) (s : Z → ℂ) (hs : ∀ z, HasSum (fun i ↦ t i z) (s z))
    (hb : ∃ b : ι → ℝ, Summable b ∧ ∀ i z, z ∈ range p → ‖t i z‖ ≤ b i) :
    HasSum (fun i ↦ ∫ u, t i (p u) ∂ν) (∫ u, s (p u) ∂ν) := by
  obtain ⟨b, h, hbound⟩ := hb
  exact hasSum_integral_of_dominated_convergence (fun i _ ↦ b i)
    (fun i ↦ ((ht i).comp p.continuous).aestronglyMeasurable)
    (fun i ↦ .of_forall fun u ↦ hbound i _ ⟨u, rfl⟩) (.of_forall fun _ ↦ h)
    (integrable_const _) (.of_forall fun u ↦ hs (p u))
open Set in
/-- The compact-uniform summable bound allows integration of the theta series term by term. -/
private theorem integral_theta_series {T : Finset V} {P : Type*}
    [TopologicalSpace P] [CompactSpace P] [MeasurableSpace P] [BorelSpace P]
    (p : C(P, (SAdeleRing F T)ˣ)) (ν : Measure P) [IsFiniteMeasure ν] (f : B(T)) :
    HasSum (fun t : (T : Set V).unit F ↦ ∫ u, f (Multiplicative.ofAdd
      (adeleProjection F T (algebraMap F 𝔸[F] t.val.val) * (p u).val)) ∂ν)
      (∫ u, sLocalAdelicTheta F T f (p u) ∂ν) := by

  let D := (Set.integer (T : Set V) F)ˣ
  let d := (Units.map ((adeleProjection F T).comp (integralAdelesOutside F T).subtype).toMonoidHom).comp
    (Units.map (integralAdeleDiagonal F T).toMonoidHom)
  let term (t : D) (z : (SAdeleRing F T)ˣ) := f (Multiplicative.ofAdd ((d t * z).val))
  let e := (Set.unitEquivUnitsInteger (T : Set V) F).symm
  let : Countable F := Countable.of_moduleFinite (R := ℚ)
  let : Countable D := Units.val_injective.countable
  have hbound : ∃ b : D → ℝ, Summable b ∧ ∀ i (z : (SAdeleRing F T)ˣ), z ∈ range p → ‖term i z‖ ≤ b i :=
    sLocalAdelicTheta_exists_summable_bound F T f (range p) (isCompact_range p.continuous)
  have ht (t : D) : Continuous (term t) := (continuous_schwartzBruhat_apply f).comp
    (continuous_ofAdd.comp (Units.continuous_val.comp (continuous_const.mul continuous_id)))
  have hsum (z : (SAdeleRing F T)ˣ) : HasSum (fun i : D ↦ term i z) (sLocalAdelicTheta F T f z) :=
    (sLocalAdelicTheta_hasSumUniformlyOn F T f {z} isCompact_singleton).hasSum rfl
  have h := integral_series (ι := D) ν p term ht (sLocalAdelicTheta F T f) hsum hbound
  let a (i : (T : Set V).unit F) := ∫ u, f (Multiplicative.ofAdd
      (adeleProjection F T (algebraMap F 𝔸[F] i.val.val) * (p u).val)) ∂ν
  change HasSum a _
  apply (e.toEquiv.hasSum_iff (f := a)).mp
  exact h

private theorem integral_pair_hasSum {P I : Type*} [TopologicalSpace P] [CompactSpace P]
    [MeasurableSpace P] [BorelSpace P] (ν : Measure P) [IsFiniteMeasure ν]
    (t₀ t₁ : I → C(P, ℂ)) (s₀ s₁ : C(P, ℂ))
    (h₀ : HasSum (fun i ↦ ∫ u, t₀ i u ∂ν) (∫ u, s₀ u ∂ν))
    (h₁ : HasSum (fun i ↦ ∫ u, t₁ i u ∂ν) (∫ u, s₁ u ∂ν)) :
    HasSum (fun i ↦ ∫ u, t₀ i u - t₁ i u ∂ν) (∫ u, s₀ u - s₁ u ∂ν) := by
  have hi (f : C(P, ℂ)) : Integrable f ν := f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_sub (hi s₀) (hi s₁)]
  exact (h₀.sub h₁).congr_fun fun i ↦ integral_sub (hi (t₀ i)) (hi (t₁ i))

private def scalarReadings {A B U : Type*} [TopologicalSpace B] [TopologicalSpace U]
    [MeasurableSpace U] [BorelSpace U] [CompactSpace U] (ν : Measure U) [IsFiniteMeasure ν]
    (p₀ p₁ : A → C(U, B)) : C(B, ℂ) →ₗ[ℂ] (A → ℂ) := by
  let d (z : C(B, ℂ)) (a : A) : C(U, ℂ) := z.comp (p₀ a) - z.comp (p₁ a)
  have hi (z a) : Integrable (d z a) ν := (d z a).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  refine { toFun z a := ∫ u, d z a u ∂ν, map_add' := ?_, map_smul' := ?_ }
  · intro x y
    funext a
    refine (integral_congr_ae (.of_forall (fun u ↦ ?_))).trans (integral_add (hi x a) (hi y a))
    simp only [d, ContinuousMap.sub_apply, ContinuousMap.comp_apply, ContinuousMap.add_apply]
    abel
  · intro c x
    funext a
    refine (integral_congr_ae (.of_forall (fun u ↦ ?_))).trans (integral_smul c (d x a))
    simp [d, mul_sub]

private def quotientReadings {Y B A : Type*} [TopologicalSpace B] [AddCommGroup Y] [Module ℂ Y]
    (θ : Y →ₗ[ℂ] C(B, ℂ)) (sample : C(B, ℂ) →ₗ[ℂ] (A → ℂ)) := sample.comp (θ.ker.liftQ θ le_rfl)

/-- Evaluate a larger theta class at the old idele and average the difference between two
adjacent shells at the new place. -/
private def unitCut {S : Finset V} (v : V) (c : (v.adicCompletion F)ˣ)
    [MeasurableSpace H(v)] [BorelSpace H(v)] (ν : Measure H(v)) [IsFiniteMeasure ν] :
    Q(insert v S) →ₗ[ℂ] ((SAdeleRing F S)ˣ → ℂ) := by
  let : CompactSpace H(v) := isCompact_iff_compactSpace.mp
    (Submonoid.units_isCompact (isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v)))
  let T := insert v S
  let p₀ (x : (SAdeleRing F S)ˣ) : C(H(v), (SAdeleRing F T)ˣ) :=
    (onePlaceIdele S v x).comp ⟨Subtype.val, continuous_subtype_val⟩
  let p₁ (x : (SAdeleRing F S)ˣ) : C(H(v), (SAdeleRing F T)ˣ) :=
    (onePlaceIdele S v x).comp ⟨fun u ↦ c * u.val, continuous_const.mul continuous_subtype_val⟩
  let read := scalarReadings (A := (SAdeleRing F S)ˣ) (B := (SAdeleRing F T)ˣ) (U := H(v)) ν p₀ p₁
  let L := quotientReadings (Y := B(T)) (B := (SAdeleRing F T)ˣ) (A := (SAdeleRing F S)ˣ)
    (sLocalAdelicTheta F T) read
  with_reducible_and_instances exact L

private theorem unitCut_mk {S : Finset V} (v : V) (c : (v.adicCompletion F)ˣ)
    [MeasurableSpace H(v)] [BorelSpace H(v)] (ν : Measure H(v)) [IsFiniteMeasure ν]
    (f : B(insert v S)) (x : (SAdeleRing F S)ˣ) :
    let T := insert v S
    let a := onePlaceIdele S v x
    unitCut (S := S) (F := F) v c ν (localClass (F := F) (insert v S) f) x =
      ∫ u : H(v), sLocalAdelicTheta F T f (a u.val) - sLocalAdelicTheta F T f (a (c * u.val)) ∂ν := rfl

private theorem sum_value {I : Type*} {f : I → ℂ} {x y : ℂ} (h : HasSum f x) (e : y = x) : HasSum f y := e.symm ▸ h

open Set in
private theorem pair_theta_sum {T : Finset V} {P : Type*}
    [TopologicalSpace P] [CompactSpace P] [MeasurableSpace P] [BorelSpace P]
    (ν : Measure P) [IsFiniteMeasure ν] (f : B(T)) (p₀ p₁ : C(P, (SAdeleRing F T)ˣ)) :
    let d (t : (T : Set V).unit F) := adeleProjection F T (algebraMap F 𝔸[F] t.val.val)
    HasSum (fun t ↦ ∫ u, f (Multiplicative.ofAdd (d t * (p₀ u).val)) -
      f (Multiplicative.ofAdd (d t * (p₁ u).val)) ∂ν)
      (∫ u, sLocalAdelicTheta F T f (p₀ u) - sLocalAdelicTheta F T f (p₁ u) ∂ν) := by
  let s (p : C(P, (SAdeleRing F T)ˣ)) := (sLocalAdelicTheta F T f).comp p
  let val (t : (T : Set V).unit F) := adeleProjection F T (algebraMap F 𝔸[F] t.val.val)
  let t (p : C(P, (SAdeleRing F T)ˣ)) (ξ : (T : Set V).unit F) : C(P, ℂ) :=
    ⟨fun u ↦ f (Multiplicative.ofAdd (val ξ * (p u).val)), (continuous_schwartzBruhat_apply f).comp
      (continuous_ofAdd.comp (continuous_const.mul (Units.continuous_val.comp p.continuous)))⟩
  have hs (p : C(P, (SAdeleRing F T)ˣ)) :
      HasSum (fun ξ ↦ ∫ u, t p ξ u ∂ν) (∫ u, s p u ∂ν) := integral_theta_series (F := F) (T := T) p ν f
  have result := integral_pair_hasSum ν (t p₀) (t p₁) (s p₀) (s p₁) (hs p₀) (hs p₁)
  exact result

open Set in
private theorem cut_hasSum {S : Finset V} (v : V) (c : (v.adicCompletion F)ˣ)
    [MeasurableSpace H(v)] [BorelSpace H(v)] (ν : Measure H(v)) [IsFiniteMeasure ν]
    (f : B(insert v S)) (x : (SAdeleRing F S)ˣ) :
    let T := insert v S
    let a := onePlaceIdele S v x
    let d (t : (T : Set V).unit F) := adeleProjection F T (algebraMap F 𝔸[F] t.val.val)
    HasSum (fun t : (T : Set V).unit F ↦ ∫ u : H(v),
      f (Multiplicative.ofAdd (d t * (a u.val).val)) -
      f (Multiplicative.ofAdd (d t * (a (c * u.val)).val)) ∂ν)
      (unitCut (F := F) (S := S) v c ν (localClass (F := F) (insert v S) f) x) := by
  let T := insert v S
  let : CompactSpace H(v) := isCompact_iff_compactSpace.mp
    (Submonoid.units_isCompact (isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v)))
  let j := onePlaceIdele S v x
  let p₀ : C(H(v), (SAdeleRing F T)ˣ) := j.comp ⟨Subtype.val, continuous_subtype_val⟩
  let p₁ : C(H(v), (SAdeleRing F T)ˣ) := j.comp ⟨fun u ↦ c * u.val, continuous_const.mul continuous_subtype_val⟩
  have result := pair_theta_sum (F := F) (T := T) ν f p₀ p₁
  have he := unitCut_mk (F := F) (S := S) v c ν f x
  have out := sum_value result he
  exact out

private theorem weighted_slices {G I X Q A : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Q] [Module ℂ Q] [TopologicalSpace Q] [IsTopologicalAddGroup Q] [ContinuousSMul ℂ Q]
    (H : Set G) (v : G → I) (val : X → A → G → ℂ) (ev : Q →ₗ[ℂ] (A → ℂ))
    (hs : ∀ i : I, ∃ L : X →L[ℂ] Q, ∀ f a, HasSum
      (({t | t ∈ H ∧ v t = i} : Set G).indicator (val f a)) (ev (L f) a))
    (b : I →₀ ℂ) : ∃ L : X →L[ℂ] Q, ∀ f a, HasSum
      (H.indicator (fun t ↦ b (v t) * val f a t)) (ev (L f) a) := by
  induction b using Finsupp.induction_linear with
  | zero => exact ⟨0, fun f a ↦ by simp⟩
  | add b d hb hd =>
    obtain ⟨L, hL⟩ := hb
    obtain ⟨M, hM⟩ := hd
    refine ⟨L + M, fun f a ↦ ?_⟩
    simp only [add_apply, map_add, Pi.add_apply]
    exact ((hL f a).add (hM f a)).congr_fun fun t ↦ by by_cases h : t ∈ H <;> simp [h, add_mul]
  | single i c =>
    obtain ⟨L, hL⟩ := hs i
    refine ⟨c • L, fun f a ↦ ?_⟩
    simp only [smul_apply, map_smul, Pi.smul_apply]
    exact ((hL f a).const_smul c).congr_fun fun t ↦ by
      by_cases h : t ∈ H <;> by_cases he : v t = i <;> simp [h, he, Ne.symm, eq_comm, Finsupp.single_apply, smul_eq_mul]

private def translationCLM {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (u : Rˣ) (hc : Continuous (schwartzBruhatUnitTranslate u)) :
    SchwartzBruhat (Multiplicative R) →L[ℂ] SchwartzBruhat (Multiplicative R) :=
  ⟨unitTranslateEnd (R := R) u, hc⟩

private theorem eval_translate_slice {S : Finset V} (g : (SAdeleRing F S)ˣ) :
    ∃ L : B(S) →L[ℂ] Q(S), ∀ f a, localValues F S (L f) a =
      sLocalAdelicTheta F S f (g * a) := by
  have hc : Continuous (schwartzBruhatUnitTranslate (R := SAdeleRing F S) g⁻¹) :=
    (local_unit_joint (F := F) (S := S)).comp (continuous_const.prodMk continuous_id)
  let tr := translationCLM (R := SAdeleRing F S) g⁻¹ hc
  let L := (K(S)).mkQL.comp tr
  refine ⟨L, fun f a ↦ ?_⟩
  change sLocalAdelicTheta F S (schwartzBruhatUnitTranslate g⁻¹ f) a = _
  exact (localTheta_translate_apply (F := F) (S := S) g⁻¹ a f).trans
    (congrArg (fun t ↦ sLocalAdelicTheta F S f (t * a)) (inv_inv g))

private theorem old_mem_iff {S : Finset V} (v : V) (hv : v ∉ S) (t : Fˣ) :
    t ∈ (S : Set V).unit F ↔ t ∈ ((insert v S : Finset V) : Set V).unit F ∧ v.valuation F t.val = 1 := by
  refine ⟨fun h ↦ ⟨fun w hw ↦ h w (fun hs ↦ hw (Finset.mem_insert_of_mem hs)), h v hv⟩, ?_⟩
  intro ⟨h, he⟩ w hw
  by_cases eq : w = v
  · exact eq ▸ he
  · exact h w fun ht ↦ (Finset.mem_insert.mp ht).elim eq hw

private theorem value_unit_eq_one {G M : Type*} [Monoid G] [Monoid M] (v : G →* M) (t : Gˣ) :
    v t.val = 1 ↔ Units.map v t = 1 := ⟨fun h ↦ Units.ext h, fun h ↦ congrArg Units.val h⟩

/-- Each occupied valuation fiber is a translate of the old unit group. Take the finite
linear combination of the corresponding continuous translation operators. -/
private theorem weighted_translation_slices {G I A X Z : Type*} [CommGroup G] [Group I] [Group A]
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z] [IsTopologicalAddGroup Z] [ContinuousSMul ℂ Z]
    (J H : Subgroup G) (i : G →* I) (d : G →* A) (φ θ : X → A → ℂ) (ev : Z →ₗ[ℂ] (A → ℂ))
    (hh : ∀ t, t ∈ H ↔ t ∈ J ∧ i t = 1)
    (sum : ∀ f a, HasSum (fun u : H ↦ φ f (d u.val * a)) (θ f a))
    (tr : ∀ g : A, ∃ L : X →L[ℂ] Z, ∀ f a, ev (L f) a = θ f (g * a)) (b : I →₀ ℂ) :
    ∃ L : X →L[ℂ] Z, ∀ f a, HasSum (fun t : J ↦ b (i t.val) * φ f (d t.val * a)) (ev (L f) a) := by
  let val (f : X) (a : A) (t : G) := φ f (d t * a)
  have hs (k : I) : ∃ L : X →L[ℂ] Z, ∀ f a,
      HasSum (({t : G | t ∈ J ∧ i t = k} : Set G).indicator (val f a)) (ev (L f) a) := by
    obtain ⟨y, hy⟩ := exists_translate_fiber J H i d φ θ hh sum k
    cases y with
    | none =>
      refine ⟨0, fun f a ↦ ?_⟩
      rw [zero_apply, ev.map_zero]
      exact hy f a
    | some g =>
      obtain ⟨L, hL⟩ := tr g
      refine ⟨L, fun f a ↦ ?_⟩
      rw [hL]
      exact hy f a
  obtain ⟨L, hL⟩ := weighted_slices (J : Set G) i val ev hs b
  exact ⟨L, fun f a ↦ hasSum_subtype_iff_indicator.mpr (hL f a)⟩

private theorem weighted_theta_slice {S : Finset V} (w : V) (hw : w ∉ S) (b : WithZero (Multiplicative ℤ) →₀ ℂ) :
    let T := insert w S
    ∃ L : B(S) →L[ℂ] Q(S), ∀ (f : B(S)) (x : (SAdeleRing F S)ˣ),
      HasSum (fun t : (T : Set V).unit F ↦ b (w.valuation F t.val.val) *
        f (Multiplicative.ofAdd (adeleProjection F S (algebraMap F 𝔸[F] t.val.val) * x.val)))
        (localValues F S (L f) x) := by
  let T := insert w S
  let J := (T : Set V).unit F
  let H := (S : Set V).unit F
  let i := Units.map (w.valuation F).toMonoidHom
  let d := Units.map ((adeleProjection F S).toMonoidHom.comp (algebraMap F 𝔸[F]).toMonoidHom)
  let φ (f : B(S)) (x : (SAdeleRing F S)ˣ) := f (Multiplicative.ofAdd x.val)
  let ev := localValues F S
  let θ (f : B(S)) (x : (SAdeleRing F S)ˣ) := sLocalAdelicTheta F S f x
  have hh (t : Fˣ) : t ∈ H ↔ t ∈ J ∧ i t = 1 := (old_mem_iff (F := F) (S := S) w hw t).trans
    (and_congr_right' (value_unit_eq_one (w.valuation F).toMonoidHom t))
  let coeff := b.comapDomain Units.val Units.val_injective.injOn
  have res := weighted_translation_slices (G := Fˣ) (I := (WithZero (Multiplicative ℤ))ˣ)
    (A := (SAdeleRing F S)ˣ) (X := B(S)) (Z := Q(S))
    J H i d φ θ ev hh (localTheta_unit_hasSum (F := F) S) (eval_translate_slice (F := F) (S := S)) coeff
  obtain ⟨L, hL⟩ := res
  refine ⟨L, fun f x ↦ ?_⟩
  exact hL f x

private theorem shell_integral_mul {U : Type*} [MeasurableSpace U] (ν : Measure U)
    (a b : ℂ) (g₀ g₁ t₀ t₁ : U → ℂ) (h₀ : ∀ u, t₀ u = a * g₀ u)
    (h₁ : ∀ u, t₁ u = a * g₁ u) (hb : b = ∫ u, g₀ u - g₁ u ∂ν) :
    b * a = ∫ u, t₀ u - t₁ u ∂ν := by
  symm
  calc
    _ = ∫ u, a * (g₀ u - g₁ u) ∂ν := integral_congr_ae (.of_forall fun u ↦ (congrArg₂ (· - ·) (h₀ u) (h₁ u)).trans (mul_sub _ _ _).symm)
    _ = _ := (integral_const_mul (μ := ν) a (fun u ↦ g₀ u - g₁ u)).trans ((congrArg (a * ·) hb.symm).trans (mul_comm _ _))

private theorem cut_term_of_product {S : Finset V} (v : V) (c : (v.adicCompletion F)ˣ)
    [MeasurableSpace H(v)] (ν : Measure H(v)) (f : B(S))
    (k : B(insert v S)) (ψ : v.adicCompletion F → ℂ)
    (x : (SAdeleRing F S)ˣ) (t : Fˣ)
    (eval : ∀ (u : (v.adicCompletion F)ˣ),
      k (Multiplicative.ofAdd (adeleProjection F (insert v S) (algebraMap F 𝔸[F] t.val) * (onePlaceIdele S v x u).val)) =
        f (Multiplicative.ofAdd (adeleProjection F S (algebraMap F 𝔸[F] t.val) * x.val)) *
          ψ (algebraMap F (v.adicCompletion F) t.val * u.val))
    (b : WithZero (Multiplicative ℤ) →₀ ℂ) (hb : ∀ y : v.adicCompletion F, y ≠ 0 →
      b (Valued.v y) = ∫ u : H(v), ψ (y * u.val.val) - ψ (c.val * (y * u.val.val)) ∂ν)
    :
    let T := insert v S
    let a := onePlaceIdele S v x
    let z (u : (v.adicCompletion F)ˣ) := adeleProjection F T (algebraMap F 𝔸[F] t.val) * (a u).val
    let v₀ := f (Multiplicative.ofAdd (adeleProjection F S (algebraMap F 𝔸[F] t.val) * x.val))
    b (v.valuation F t.val) * v₀ = ∫ u : H(v),
      k (Multiplicative.ofAdd (z u.val)) - k (Multiplicative.ofAdd (z (c * u.val))) ∂ν := by
  let T := insert v S
  let a := onePlaceIdele S v x
  let z (u : (v.adicCompletion F)ˣ) := adeleProjection F T (algebraMap F 𝔸[F] t.val) * (a u).val
  let w := f (Multiplicative.ofAdd (adeleProjection F S (algebraMap F 𝔸[F] t.val) * x.val))
  let y := algebraMap F (v.adicCompletion F) t.val
  let g₀ (u : H(v)) := ψ (y * u.val.val)
  let g₁ (u : H(v)) := ψ (c.val * (y * u.val.val))
  let t₀ (u : H(v)) := k (Multiplicative.ofAdd (z u.val))
  let t₁ (u : H(v)) := k (Multiplicative.ofAdd (z (c * u.val)))
  have h₁ (u : H(v)) : t₁ u = w * g₁ u := (eval (c * u.val)).trans
    (congrArg (fun q ↦ w * ψ q) (mul_left_comm y c.val u.val.val))
  have hy : y ≠ 0 := (map_ne_zero (algebraMap F (v.adicCompletion F))).mpr t.ne_zero
  have heval : Valued.v y = v.valuation F t.val := v.valuedAdicCompletion_eq_valuation' t.val
  have weight := hb y hy
  rw [heval] at weight
  have h := shell_integral_mul ν w (b (v.valuation F t.val)) g₀ g₁ t₀ t₁
    (fun u ↦ eval u.val) h₁ weight
  with_reducible_and_instances exact h

private theorem sums_agree {I : Type*} {w z : I → ℂ} {a b : ℂ}
    (h₁ : HasSum w a) (h₂ : HasSum z b) (eq : ∀ t, w t = z t) : a = b :=
  h₁.unique (h₂.congr_fun eq)

private theorem cut_value_of_product {S : Finset V} (v : V) (c : (v.adicCompletion F)ˣ)
    [MeasurableSpace H(v)] [BorelSpace H(v)] (ν : Measure H(v)) [IsFiniteMeasure ν]
    (f : B(S)) (k : B(insert v S)) (x : (SAdeleRing F S)ˣ) (ψ : v.adicCompletion F → ℂ)
    (eval : ∀ (t : Fˣ) (u : (v.adicCompletion F)ˣ),
      k (Multiplicative.ofAdd (adeleProjection F (insert v S) (algebraMap F 𝔸[F] t.val) * (onePlaceIdele S v x u).val)) =
        f (Multiplicative.ofAdd (adeleProjection F S (algebraMap F 𝔸[F] t.val) * x.val)) *
          ψ (algebraMap F (v.adicCompletion F) t.val * u.val))
    (b : WithZero (Multiplicative ℤ) →₀ ℂ)
    (hb : ∀ y : v.adicCompletion F, y ≠ 0 → b (Valued.v y) =
      ∫ u : H(v), ψ (y * u.val.val) - ψ (c.val * (y * u.val.val)) ∂ν)
    (value : ℂ) (hval : HasSum (fun t : ((insert v S : Finset V) : Set V).unit F ↦
      b (v.valuation F t.val.val) * f (Multiplicative.ofAdd (adeleProjection F S (algebraMap F 𝔸[F] t.val.val) * x.val))) value) :
    value = unitCut (F := F) (S := S) v c ν (localClass (F := F) (insert v S) k) x := by
  let T := insert v S
  have h := cut_hasSum (F := F) (S := S) v c ν k x
  have term (t : (T : Set V).unit F) := cut_term_of_product (F := F) (S := S) v c ν f k ψ x t.val (eval t.val) b hb
  with_reducible_and_instances exact sums_agree hval h term

private theorem slice_of_product {S : Finset V} (v : V) (hv : v ∉ S) (c : (v.adicCompletion F)ˣ)
    [MeasurableSpace H(v)] [BorelSpace H(v)] (ν : Measure H(v)) [IsFiniteMeasure ν] [ν.IsMulLeftInvariant]
    (k : B(S) → B(insert v S)) (ψ : v.adicCompletion F → ℂ) (hl : IsLocallyConstant ψ) (hp : HasCompactSupport ψ)
    (eval : ∀ (f : B(S)) (x : (SAdeleRing F S)ˣ) (t : Fˣ) (u : (v.adicCompletion F)ˣ),
      k f (Multiplicative.ofAdd (adeleProjection F (insert v S) (algebraMap F 𝔸[F] t.val) * (onePlaceIdele S v x u).val)) =
        f (Multiplicative.ofAdd (adeleProjection F S (algebraMap F 𝔸[F] t.val) * x.val)) *
          ψ (algebraMap F (v.adicCompletion F) t.val * u.val)) :
    ∃ L : B(S) →L[ℂ] Q(S), ∀ f, localValues F S (L f) =
      unitCut (F := F) (S := S) v c ν (localClass (F := F) (insert v S) (k f)) := by
  have W := shell_weights (F := F) v ν ψ hl hp c
  let b := W.choose
  have ops := weighted_theta_slice (F := F) (S := S) v hv b
  let L := ops.choose
  have eq (f : B(S)) (x : (SAdeleRing F S)ˣ) := cut_value_of_product (F := F) (S := S)
    v c ν f (k f) x ψ (eval f x) b W.choose_spec (localValues F S (L f) x) (ops.choose_spec f x)
  exact ⟨L, fun f ↦ funext (eq f)⟩

/-- On a pure tensor, the scalar cut is the old theta transform of a finite sum of
translates. The operator on old tests is continuous for each fixed new test. -/
private theorem unitCut_tensor_slice {S : Finset V} (v : V) (hv : v ∉ S) (c : (v.adicCompletion F)ˣ)
    [MeasurableSpace H(v)] [BorelSpace H(v)] (ν : Measure H(v)) [IsFiniteMeasure ν] [ν.IsMulLeftInvariant]
    (g : SchwartzBruhat (Multiplicative (FinitePlaceProduct F (insert v S \ S))))
    (k : B(S) → B(insert v S))
    (hk : ∀ (f : B(S)) (z : SAdeleRing F (insert v S)), k f (Multiplicative.ofAdd z) =
      f (Multiplicative.ofAdd (z.1, fun w : S ↦ z.2 ⟨w.val, Finset.mem_insert_of_mem w.property⟩)) *
      g (Multiplicative.ofAdd (fun w : ↥(insert v S \ S) ↦ z.2 ⟨w.val, (Finset.mem_sdiff.mp w.property).1⟩))) :
    ∃ L : B(S) →L[ℂ] Q(S), ∀ f, localValues F S (L f) =
      unitCut (F := F) (S := S) v c ν (localClass (F := F) (insert v S) (k f)) := by
  have witness := newTest_exists (F := F) (S := S) (v := v) hv g
  let φ := witness.choose
  have hφ := witness.choose_spec
  let ψ (y : v.adicCompletion F) := φ (Multiplicative.ofAdd y)
  have hp := (mem_finitePlaceSchwartz_iff F v ψ).mp ⟨φ, fun _ ↦ rfl⟩
  apply slice_of_product (F := F) (S := S) v hv c ν k ψ hp.1 hp.2
  intro f x t u
  let z : SAdeleRing F (insert v S) := adeleProjection F (insert v S) (algebraMap F 𝔸[F] t.val) * (onePlaceIdele S v x u).val
  have h₀ := congrArg (fun q : SAdeleRing F S ↦ f (Multiplicative.ofAdd q))
    (coordinates_old (F := F) (S := S) (v := v) hv x u t)
  have h₁ := congrArg (fun q : FinitePlaceProduct F (insert v S \ S) ↦ g (Multiplicative.ofAdd q))
    (coordinates_new (F := F) (S := S) (v := v) hv x u t)
  have h' := h₁.trans (hφ (algebraMap F (v.adicCompletion F) t.val * u.val)).symm
  have H := (hk f z).trans (congrArg₂ (fun a b : ℂ ↦ a * b) h₀ h')
  exact H

private theorem strict_shell {r : WithZero (Multiplicative ℤ)} (h : r ≠ 0) :
    r * WithZero.exp (1 : ℤ) ≤ 1 ↔ r < 1 := by
  rw [← WithZero.exp_log h, ← WithZero.exp_add]
  simp only [WithZero.exp_le_one_iff, WithZero.exp_lt_one_iff]
  omega

private theorem forall_new_iff {α : Type*} [DecidableEq α] (S : Finset α) (v : α) (hv : v ∉ S)
    (P : ↥(insert v S) → Prop) : (∀ w : ↥(insert v S), w.val ∉ S → P w) ↔ P ⟨v, Finset.mem_insert_self v S⟩ := by
  refine ⟨fun h ↦ h ⟨v, Finset.mem_insert_self v S⟩ hv, fun h w hw ↦ ?_⟩
  have eq : w = ⟨v, Finset.mem_insert_self v S⟩ := Subtype.ext ((Finset.mem_insert.mp w.property).resolve_right hw)
  exact eq.symm ▸ h

private theorem last_coordinate {S : Finset V} (v : V)
    (x : (SAdeleRing F S)ˣ) (u : (v.adicCompletion F)ˣ) (t : Fˣ) :
    let T := insert v S
    let z := adeleProjection F T (algebraMap F 𝔸[F] t.val) * (onePlaceIdele S v x u).val
    z.2 ⟨v, Finset.mem_insert_self _ _⟩ = algebraMap F (v.adicCompletion F) t.val * u.val := by
  let w' : ↥(insert v S) := ⟨v, Finset.mem_insert_self _ _⟩
  have h : (newUnits S v x u w').val = u.val := by
    simp only [newUnits, show w'.val = v from rfl, dite_true]
    rfl
  exact congrArg ((algebraMap F (v.adicCompletion F) t.val) * ·) h

open Set in
private theorem inserted_test_value {S : Finset V} (v : V) (hv : v ∉ S)
    (f : B(S)) (x : (SAdeleRing F S)ˣ) (t : Fˣ) (u : (v.adicCompletion F)ˣ) :
    let T := insert v S
    let z := adeleProjection F T (algebraMap F 𝔸[F] t.val) * (onePlaceIdele S v x u).val
    sAdeleSchwartzTransition F (Finset.subset_insert v S) f (Multiplicative.ofAdd z) =
      if v.valuation F t.val * Valued.v u.val ≤ 1 then
        f (Multiplicative.ofAdd (adeleProjection F S (algebraMap F 𝔸[F] t.val) * x.val)) else 0 := by
  let T := insert v S
  let h := Finset.subset_insert v S
  let val (t : Fˣ) := f (Multiplicative.ofAdd (adeleProjection F S (algebraMap F 𝔸[F] t.val) * x.val))
  let a := onePlaceIdele S v x
  let z (t : Fˣ) (u : (v.adicCompletion F)ˣ) := adeleProjection F T (algebraMap F 𝔸[F] t.val) * (a u).val
  have integral_iff (p : SAdeleRing F T) : (∀ w : T, w.val ∉ S → p.2 w ∈ w.val.adicCompletionIntegers F) ↔
      p.2 ⟨v, Finset.mem_insert_self _ _⟩ ∈ v.adicCompletionIntegers F :=
    forall_new_iff S v hv (fun w ↦ p.2 w ∈ w.val.adicCompletionIntegers F)
  have hnew := last_coordinate (F := F) (S := S) v x u t
  have hcond : (∀ w : T, w.val ∉ S → (z t u).2 w ∈ w.val.adicCompletionIntegers F) ↔
      v.valuation F t.val * Valued.v u.val ≤ 1 := by
    refine (integral_iff _).trans ?_
    change Valued.v ((z t u).2 ⟨v, Finset.mem_insert_self _ _⟩) ≤ 1 ↔ _
    change (z t u).2 ⟨v, Finset.mem_insert_self _ _⟩ = _ at hnew
    have he : Valued.v (algebraMap F (v.adicCompletion F) t.val) = v.valuation F t.val :=
      v.valuedAdicCompletion_eq_valuation' t.val
    rw [hnew, map_mul, he]
  exact (sAdeleSchwartzTransition_apply F h f _).trans (if_congr hcond
    (congrArg (fun q ↦ f (Multiplicative.ofAdd q)) (coordinates_old (F := F) (S := S) (v := v) hv x u t)) rfl)

private theorem shell_indicator_difference (q r r' : WithZero (Multiplicative ℤ)) (a : ℂ)
    (P : Prop) [Decidable P] (hq : q ≠ 0) (hr : r = 1) (hr' : r' = WithZero.exp (1 : ℤ))
    (hP : P ↔ q = 1) : (if q * r ≤ 1 then a else 0) - (if q * r' ≤ 1 then a else 0) =
      if P then a else 0 := by
  simp only [hr, hr', mul_one, strict_shell hq, hP]
  rcases lt_trichotomy q 1 with h | h | h
  · simp [h.le, h, h.ne]
  · simp [h]
  · simp [h.not_ge, h.not_gt, h.ne']

private theorem integral_const_value {U : Type*} [MeasurableSpace U] (ν : Measure U) [IsProbabilityMeasure ν]
    (f : U → ℂ) (b : ℂ) (hf : ∀ u, f u = b) : b = ∫ u, f u ∂ν := by
  rw [funext hf]
  simp

private def insertedTest (S : Finset V) (v : V) (f : B(S)) : B(insert v S) :=
  sAdeleSchwartzTransition F (Finset.subset_insert v S) f

private theorem inserted_term_difference {S : Finset V} (v : V) (hv : v ∉ S)
    (c : (v.adicCompletion F)ˣ) (hc : Valued.v c.val = WithZero.exp (1 : ℤ))
    (f : B(S)) (x : (SAdeleRing F S)ˣ) (t : ((insert v S : Finset V) : Set V).unit F) (u : H(v)) :
    let T := insert v S
    let a := onePlaceIdele S v x
    let z (q : (v.adicCompletion F)ˣ) := adeleProjection F T (algebraMap F 𝔸[F] t.val.val) * (a q).val
    let val := f (Multiplicative.ofAdd (adeleProjection F S (algebraMap F 𝔸[F] t.val.val) * x.val))
    let g := insertedTest (F := F) S v f
    g (Multiplicative.ofAdd (z u.val)) - g (Multiplicative.ofAdd (z (c * u.val))) =
      if t.val ∈ (S : Set V).unit F then val else 0 := by
  let val (t : Fˣ) := f (Multiplicative.ofAdd (adeleProjection F S (algebraMap F 𝔸[F] t.val) * x.val))
  have hu : Valued.v u.val.val = 1 := HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp u.property
  have ht : v.valuation F t.val.val ≠ 0 := (Valuation.ne_zero_iff _).mpr t.val.ne_zero
  have e₀ := inserted_test_value (F := F) (S := S) v hv f x t.val u.val
  have e₁ := inserted_test_value (F := F) (S := S) v hv f x t.val (c * u.val)
  have hcu : Valued.v (c * u.val).val = WithZero.exp (1 : ℤ) := by
    rw [Units.val_mul, map_mul, hu, mul_one, hc]
  have hh : t.val ∈ (S : Set V).unit F ↔ v.valuation F t.val.val = 1 :=
    (old_mem_iff (F := F) (S := S) v hv t.val).trans (and_iff_right t.property)
  have result := shell_indicator_difference _ _ _ (val t.val) _ ht hu hcu hh
  exact (congrArg₂ (· - ·) e₀ e₁).trans result

open Set in
/-- For the inserted integer-ring indicator, only the terms whose new component is a unit survive. -/
private theorem unitCut_hasSum_inserted {S : Finset V} (v : V) (hv : v ∉ S) (c : (v.adicCompletion F)ˣ)
    (hc : Valued.v c.val = WithZero.exp (1 : ℤ))
    [MeasurableSpace H(v)] [BorelSpace H(v)] (ν : Measure H(v)) [IsProbabilityMeasure ν]
    (f : B(S)) (x : (SAdeleRing F S)ˣ) :
    let T := insert v S
    let val (t : Fˣ) := f (Multiplicative.ofAdd (adeleProjection F S (algebraMap F 𝔸[F] t.val) * x.val))
    HasSum (fun t : (T : Set V).unit F ↦ if t.val ∈ (S : Set V).unit F then val t.val else 0)
      (unitCut (F := F) (S := S) v c ν (localClass (F := F) (insert v S) (insertedTest (F := F) S v f)) x) := by
  let T := insert v S
  let g := insertedTest (F := F) S v f
  let w (t : (T : Set V).unit F) := if t.val ∈ (S : Set V).unit F then
    f (Multiplicative.ofAdd (adeleProjection F S (algebraMap F 𝔸[F] t.val.val) * x.val)) else 0
  have eq (t : (T : Set V).unit F) := integral_const_value ν _ (w t)
    (inserted_term_difference (F := F) (S := S) v hv c hc f x t)
  have h := (cut_hasSum (F := F) (S := S) v c ν g x).congr_fun (g := w) eq
  exact h

private theorem extend_subtype_sum {A : Type*} {J H : Set A} (hj : H ⊆ J)
    (f : A → ℂ) {z : ℂ} (h : HasSum (H.indicator f) z) :
    HasSum (fun t : J ↦ if t.val ∈ H then f t.val else 0) z := by
  apply (hasSum_subtype_iff_indicator (f := fun a : A ↦ if a ∈ H then f a else 0) (s := J)).mpr
  refine h.congr_fun fun t ↦ ?_
  by_cases ht : t ∈ H
  · simp [ht, hj ht]
  · by_cases hJ : t ∈ J <;> simp [ht, hJ]

open Set in
private theorem unitCut_section {S : Finset V} (v : V) (hv : v ∉ S) (c : (v.adicCompletion F)ˣ)
    (hc : Valued.v c.val = WithZero.exp (1 : ℤ))
    [MeasurableSpace H(v)] [BorelSpace H(v)] (ν : Measure H(v)) [IsProbabilityMeasure ν] (f : B(S)) :
    unitCut (F := F) (S := S) v c ν (localClass (F := F) (insert v S) (insertedTest (F := F) S v f)) =
      ⇑(sLocalAdelicTheta F S f) := by
  let T := insert v S
  let val (t : Fˣ) (x : (SAdeleRing F S)ˣ) := f (Multiplicative.ofAdd (adeleProjection F S (algebraMap F 𝔸[F] t.val) * x.val))
  funext x
  apply (unitCut_hasSum_inserted (F := F) (S := S) v hv c hc ν f x).unique
  have hi : ((S : Set V).unit F : Set Fˣ) ⊆ ((T : Set V).unit F : Set Fˣ) :=
    fun {t} ht ↦ ((old_mem_iff (F := F) (S := S) v hv t).mp ht).1
  have result := extend_subtype_sum hi (fun t ↦ val t x) (localTheta_indicator_hasSum (F := F) S f x)
  with_reducible_and_instances exact result

private theorem cut_retraction_for_equiv {S : Finset V} (v : V) (hv : v ∉ S)
    (c : (v.adicCompletion F)ˣ) (hc : Valued.v c.val = WithZero.exp (1 : ℤ))
    [MeasurableSpace H(v)] [BorelSpace H(v)] (ν : Measure H(v)) [IsProbabilityMeasure ν] [ν.IsMulLeftInvariant]
    (e : InductiveTensor B(S) (SchwartzBruhat (Multiplicative (FinitePlaceProduct F (insert v S \ S)))) ≃L[ℂ] B(insert v S))
    (he : ∀ (f : B(S)) (g : SchwartzBruhat (Multiplicative (FinitePlaceProduct F (insert v S \ S))))
      (z : SAdeleRing F (insert v S)), e (f ⊗ₜ[ℂ] g) (Multiplicative.ofAdd z) =
        f (Multiplicative.ofAdd (z.1, fun w : S ↦ z.2 ⟨w.val, Finset.mem_insert_of_mem w.property⟩)) *
        g (Multiplicative.ofAdd (fun w : ↥(insert v S \ S) ↦ z.2 ⟨w.val, (Finset.mem_sdiff.mp w.property).1⟩))) :
    ∃ r : Q(insert v S) →L[ℂ] Q(S), LeftInverse r (sLocalThetaTransition (F := F) (Finset.subset_insert v S)) := by
  with_reducible_and_instances
    refine finiteTheta_retraction_of_classes (F := F) (S := S) (T := insert v S)
      (Finset.subset_insert v S) e (unitCut (F := F) (S := S) v c ν) ?_ ?_
  · intro g
    let k (f : B(S)) : B(insert v S) := e (f ⊗ₜ[ℂ] g)
    have eq (f : B(S)) (z : SAdeleRing F (insert v S)) := he f g z
    with_reducible_and_instances exact unitCut_tensor_slice (F := F) (S := S) v hv c ν g k eq
  · intro f
    exact unitCut_section (F := F) (S := S) v hv c hc ν f

private theorem cut_retraction {S : Finset V} (v : V) (hv : v ∉ S)
    (c : (v.adicCompletion F)ˣ) (hc : Valued.v c.val = WithZero.exp (1 : ℤ))
    [MeasurableSpace H(v)] [BorelSpace H(v)] (ν : Measure H(v)) [IsProbabilityMeasure ν] [ν.IsMulLeftInvariant] :
    ∃ r : Q(insert v S) →L[ℂ] Q(S), LeftInverse r (sLocalThetaTransition (F := F) (Finset.subset_insert v S)) := by
  have ht := sAdeleDifferenceSchwartz_inductiveTensor_equiv (S := S) (T := insert v S) F (Finset.subset_insert v S)
  refine ht.elim ?_
  intro e he
  with_reducible_and_instances exact cut_retraction_for_equiv (F := F) (S := S) v hv c hc ν e he

private theorem exists_unit_probability (U : Type*) [CommGroup U] [TopologicalSpace U] [IsTopologicalGroup U]
    [T2Space U] [CompactSpace U] [MeasurableSpace U] [BorelSpace U] :
    ∃ ν : Measure U, IsProbabilityMeasure ν ∧ ν.IsMulLeftInvariant := by
  let K : TopologicalSpace.PositiveCompacts U := ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩
  let ν := Measure.haarMeasure K
  exact ⟨ν, ⟨Measure.haarMeasure_self (K₀ := K)⟩, inferInstance⟩

private theorem exists_unit_cut_parameter (v : V) : ∃ c : (v.adicCompletion F)ˣ, Valued.v c.val = WithZero.exp (1 : ℤ) := by
  have h := v.valuedAdicCompletion_surjective F (WithZero.exp (1 : ℤ))
  let p := h.choose
  have hp : Valued.v p = WithZero.exp (1 : ℤ) := h.choose_spec
  have hp0 : p ≠ 0 := fun hn ↦ WithZero.exp_ne_zero (a := (1 : ℤ)) (hp.symm.trans (by rw [hn, map_zero]))
  exact ⟨Units.mk0 p hp0, hp⟩

/-- Averaging the difference of two adjacent local-unit orbits gives a continuous linear
left inverse to insertion at one new finite place. -/
theorem sLocalThetaTransition_exists_leftInverse_insert {S : Finset V} (v : V) (hv : v ∉ S) :
    ∃ r : Q(insert v S) →L[ℂ] Q(S), LeftInverse r (sLocalThetaTransition (F := F) (Finset.subset_insert v S)) := by
  let : CompactSpace H(v) := isCompact_iff_compactSpace.mp
    (Submonoid.units_isCompact (isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v)))
  let : MeasurableSpace H(v) := borel _
  let : BorelSpace H(v) := ⟨rfl⟩
  have hm := exists_unit_probability H(v)
  let ν := hm.choose
  let : IsProbabilityMeasure ν := hm.choose_spec.1
  let : ν.IsMulLeftInvariant := hm.choose_spec.2
  have hc := exists_unit_cut_parameter (F := F) v
  with_reducible_and_instances exact cut_retraction (F := F) (S := S) v hv hc.choose hc.choose_spec ν

private theorem embedding_of_fixed {X : Type*} [TopologicalSpace X] (f : X → X)
    (h : ∀ x, f x = x) : IsEmbedding f := by
  have hf : f = id := funext h
  rw [hf]
  exact IsEmbedding.id

private theorem self_embedding_of_comp {X Z : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Z] [Module ℂ Z] (i : X →ₗ[ℂ] Z) (j : X →ₗ[ℂ] X) (hi : Injective i)
    (h : i.comp j = i) : IsEmbedding j :=
  embedding_of_fixed j fun x ↦ hi (DFunLike.congr_fun h x)

private theorem insert_cases_prop {A : Type*} [DecidableEq A] (S : Finset A) (v : A)
    (P : ∀ T : Finset A, S ⊆ T → Prop) (hS : ∀ h : S ⊆ S, P S h)
    (hI : v ∉ S → P (insert v S) (Finset.subset_insert v S)) : P (insert v S) (Finset.subset_insert v S) := by
  by_cases hv : v ∈ S
  · have h (T : Finset A) (hT : T = S) (hs : S ⊆ T) : P T hs := by
      subst T
      exact hS hs
    exact h _ (Finset.insert_eq_of_mem hv) _
  · exact hI hv

private theorem embedding_of_split_linear {X Y : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] (j : X →ₗ[ℂ] Y) (hc : Continuous j)
    (hs : ∃ r : Y →L[ℂ] X, LeftInverse r j) : IsEmbedding j := by
  obtain ⟨r, h⟩ := hs
  exact h.isEmbedding r.continuous hc

private theorem self_transition_embedding (T : Finset V) (h : T ⊆ T) :
    IsEmbedding (sLocalThetaTransition (F := F) (S := T) (T := T) h) := by
  with_reducible_and_instances
    exact self_embedding_of_comp (X := Q(T)) (Z := GlobalAdelicThetaSpace F)
      (sLocalThetaToGlobal F T) (sLocalThetaTransition (F := F) (S := T) (T := T) h)
      (sLocalThetaToGlobal_injective (F := F) (S := T)) (sLocalThetaToGlobal_comp (F := F) (S := T) (T := T) h)

private theorem new_transition_embedding (T : Finset V) (v : V)
    (ret : ∃ r : Q(insert v T) →L[ℂ] Q(T), LeftInverse r (sLocalThetaTransition (F := F) (Finset.subset_insert v T))) :
    IsEmbedding (sLocalThetaTransition (F := F) (Finset.subset_insert v T)) := by
  with_reducible_and_instances
    exact embedding_of_split_linear (X := Q(T)) (Y := Q(insert v T))
      (sLocalThetaTransition (F := F) (S := T) (T := insert v T) (Finset.subset_insert v T))
      (sLocalThetaTransition_continuous (F := F) (S := T) (T := insert v T) (Finset.subset_insert v T)) ret

private def stageEmb {S T : Finset V} (h : S ⊆ T) : Prop :=
  IsEmbedding (sLocalThetaTransition (F := F) (S := S) (T := T) h)

private theorem all_stage_emb (T : Finset V) (v : V) (he : v ∉ T →
    stageEmb (F := F) (S := T) (T := insert v T) (Finset.subset_insert v T)) :
    stageEmb (F := F) (S := T) (T := insert v T) (Finset.subset_insert v T) := by
  have hs (h : T ⊆ T) : stageEmb (F := F) (S := T) (T := T) h := self_transition_embedding (F := F) T h
  exact insert_cases_prop T v (fun U h ↦ stageEmb (F := F) (S := T) (T := U) h) hs he

private theorem stage_of_retraction (T : Finset V) (v : V)
    (ret : v ∉ T → ∃ r : Q(insert v T) →L[ℂ] Q(T), LeftInverse r (sLocalThetaTransition (F := F) (S := T) (T := insert v T) (Finset.subset_insert v T))) :
    stageEmb (F := F) (S := T) (T := insert v T) (Finset.subset_insert v T) := by
  refine all_stage_emb (F := F) T v ?_
  intro hv
  unfold stageEmb
  with_reducible_and_instances exact new_transition_embedding (F := F) T v (ret hv)

private theorem global_of_stages (he : ∀ (T : Finset V) (v : V),
    stageEmb (F := F) (S := T) (T := insert v T) (Finset.subset_insert v T)) (S : Finset V) :
    IsEmbedding (sLocalThetaToGlobal F S) := by
  refine sLocalThetaToGlobal_isEmbedding_of_insert (F := F) (fun T v ↦ ?_) S
  exact he T v

private theorem global_embedding_from_cut (S : Finset V) : IsEmbedding (sLocalThetaToGlobal F S) := by
  refine global_of_stages (F := F) (fun T v ↦ ?_) S
  exact stage_of_retraction (F := F) T v (sLocalThetaTransition_exists_leftInverse_insert (F := F) (S := T) v)

end OnePlaceRetraction

/-- Paper: Theorem 5.2.1.1(3), p. 230.
The S-local theta space embeds topologically in the global theta space. -/
theorem sLocalThetaToGlobal_isEmbedding : IsEmbedding (sLocalThetaToGlobal F S) :=
  global_embedding_from_cut (F := F) S

/-- Paper: Theorem 5.2.1.1(3), p. 231.
The global stage insertion has closed range, as used in Lemma 5.3.1.5. -/
theorem sLocalThetaToGlobal_isClosed_range :
    IsClosed (Set.range (sLocalThetaToGlobal F S)) := by
  let : UniformSpace (Θₛ(S)) := IsTopologicalAddGroup.rightUniformSpace _
  let : UniformSpace Θ𝔽 := IsTopologicalAddGroup.rightUniformSpace _
  let : IsUniformAddGroup (Θₛ(S)) := isUniformAddGroup_of_addCommGroup
  let : IsUniformAddGroup Θ𝔽 := isUniformAddGroup_of_addCommGroup
  let : CompleteSpace (Θₛ(S)) := sLocalAdelicThetaSpace_complete
  let : T2Space Θ𝔽 := (globalAdelicThetaSpace_lf (F := F)).1
  exact (AddMonoidHom.isUniformInducing_of_isInducing
    (sLocalThetaToGlobal_isEmbedding (F := F) (S := S)).isInducing).isComplete_range.isClosed

/-- Paper: Theorem 5.2.1.1(2), p. 230.
The transition on theta quotients embeds each stage as a closed subspace of a larger stage. -/
theorem sLocalThetaTransition_isClosedEmbedding (hST : S ⊆ T) :
    IsClosedEmbedding (sLocalThetaTransition (F := F) hST) :=
  closedEmbedding_of_linear_comp (sLocalThetaTransition hST) (sLocalThetaToGlobal F T)
    (sLocalThetaToGlobal F S) (sLocalThetaToGlobal_isEmbedding (F := F) (S := T))
    ⟨sLocalThetaToGlobal_isEmbedding (F := F) (S := S), sLocalThetaToGlobal_isClosed_range (F := F) (S := S)⟩
    (sLocalThetaToGlobal_comp (F := F) hST)

end Transitions

section GlobalTopology

open Set TopologicalSpace

private theorem frechet_of_closed_embedding {X Y : Type*} [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] [IsTopologicalAddGroup X] [AddCommGroup Y] [Module ℂ Y]
    [TopologicalSpace Y] (i : X →L[ℂ] Y) (hi : IsClosedEmbedding i) (hY : IsFrechetTVS Y) :
    IsFrechetTVS X := by
  obtain ⟨a,p,m,c⟩ := hY
  let : UniformSpace Y := IsTopologicalAddGroup.rightUniformSpace Y
  let : IsUniformAddGroup Y := isUniformAddGroup_of_addCommGroup
  let : CompleteSpace Y := c
  let : UniformSpace X := IsTopologicalAddGroup.rightUniformSpace X
  let : IsUniformAddGroup X := isUniformAddGroup_of_addCommGroup
  have hu := AddMonoidHom.isUniformInducing_of_isInducing (f := i.toLinearMap.toAddMonoidHom) hi.isInducing
  exact ⟨inferInstance, hi.eq_induced ▸ PolynormableSpace.induced i.toLinearMap,
    hi.isEmbedding.metrizableSpace, hu.completeSpace hi.isClosed_range.isComplete⟩

private theorem embedded_frechet_range {X E : Type*} [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [T2Space E] (i : X →L[ℂ] E) (hi : IsEmbedding i)
    (hX : IsFrechetTVS X) : IsClosed (range i) ∧ IsFrechetTVS i.toLinearMap.range := by
  obtain ⟨a,p,m,c⟩ := hX
  let : UniformSpace X := IsTopologicalAddGroup.rightUniformSpace X
  let : IsUniformAddGroup X := isUniformAddGroup_of_addCommGroup
  let : CompleteSpace X := c
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  let e := LinearEquiv.ofInjective i.toLinearMap hi.injective
  have he : IsInducing e := IsInducing.subtypeVal.of_comp_iff.mp hi.isInducing
  let h := e.toEquiv.toHomeomorphOfIsInducing he
  let L : X ≃L[ℂ] i.toLinearMap.range := ⟨e, h.continuous, h.continuous_symm⟩
  exact ⟨(AddMonoidHom.isUniformInducing_of_isInducing (f := i.toLinearMap.toAddMonoidHom)
      hi.isInducing).isComplete_range.isClosed,
    frechet_of_closed_embedding L.symm.toContinuousLinearMap L.symm.toHomeomorph.isClosedEmbedding ⟨a,p,m,c⟩⟩

private theorem frechet_range_in_cover {ι X E : Type*} [Countable ι] [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (i : X →L[ℂ] E) (hX : IsFrechetTVS X) (D : ι → Submodule ℂ E)
    (hd : ∀ t, IsClosed (D t : Set E)) (hc : ∀ x : E, ∃ t, x ∈ D t) :
    ∃ t, i.toLinearMap.range ≤ D t := by
  obtain ⟨a,p,m,c⟩ := hX
  let : UniformSpace X := IsTopologicalAddGroup.rightUniformSpace X
  let : IsUniformAddGroup X := isUniformAddGroup_of_addCommGroup
  let : CompleteSpace X := c
  have : (uniformity X).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_zero X]
    infer_instance
  let : BaireSpace X := by
    let := UniformSpace.metricSpace X
    infer_instance
  let K (t : ι) := (D t).comap i.toLinearMap
  have hcov : (⋃ t, (K t : Set X)) = univ :=
    eq_univ_of_forall fun x ↦ (hc (i x)).elim fun t ht ↦ mem_iUnion.mpr ⟨t, ht⟩
  obtain ⟨t, ht⟩ := nonempty_interior_of_iUnion_of_closed (fun t ↦ (hd t).preimage i.continuous) hcov
  have htop : K t = ⊤ := (K t).eq_top_of_nonempty_interior' ht
  exact ⟨t, fun _ ⟨x,hx⟩ ↦ hx ▸ (show x ∈ K t from htop.symm ▸ Submodule.mem_top)⟩

/-- An LF-space covered by countably many closed Fréchet subspaces is strict.
The closure of each defining stage lies in a single member of the cover by Baire. -/
private theorem strictLF_of_countable_frechet_cover {ι E : Type*} [Countable ι] [AddCommGroup E]
    [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    (hLF : IsLFSpace E) (D : ι → Submodule ℂ E) (hd : ∀ t, IsClosed (D t : Set E))
    (hD : ∀ t, IsFrechetTVS (D t)) (hc : ∀ x : E, ∃ t, x ∈ D t) : IsStrictLFSpace E := by
  obtain ⟨h₂,X,_,_,_,hX,j,i,h⟩ := hLF
  let R (k : ℕ) := (i k).toLinearMap.range
  let S (k : ℕ) := (R k).topologicalClosure
  have hP : WithSeminorms (Subtype.val :
      {p : Seminorm ℂ E // ∀ k, Continuous (p ∘ (i k).toLinearMap)} → _) := ⟨h.topology_eq⟩
  have hS (k : ℕ) : IsFrechetTVS (S k) := by
    obtain ⟨t,ht⟩ := frechet_range_in_cover (i k) (hX k) D hd hc
    have hst : S k ≤ D t := closure_minimal ht (hd t)
    let l := Submodule.inclusion hst
    have he : IsEmbedding l := IsEmbedding.subtypeVal.of_comp_iff.mp IsEmbedding.subtypeVal
    have hr : range l = Subtype.val ⁻¹' (S k : Set E) := by
      ext x
      exact ⟨fun ⟨y,hy⟩ ↦ hy ▸ y.property, fun hx ↦ ⟨⟨x.val, hx⟩, rfl⟩⟩
    exact frechet_of_closed_embedding ⟨l, he.continuous⟩
      ⟨he, hr ▸ (R k).isClosed_topologicalClosure.preimage continuous_subtype_val⟩ (hD t)
  refine ⟨h₂, S, monotone_nat_of_le_succ (fun k ↦ ?_), hS, fun x ↦ ?_, ?_⟩
  · apply closure_mono
    rintro _ ⟨y,rfl⟩
    exact ⟨j k y, DFunLike.congr_fun (h.compatible k) y⟩
  · obtain ⟨k,hk⟩ := h.exhaustive x
    exact ⟨k, subset_closure hk⟩
  · have hs : (fun p : Seminorm ℂ E ↦ ∀ k, Continuous (p ∘ (S k).subtype)) =
        (fun p : Seminorm ℂ E ↦ ∀ k, Continuous (p ∘ (i k).toLinearMap)) := by
      funext p
      apply propext
      refine ⟨fun hp k ↦ ?_, fun hp k ↦ (hP.continuous_seminorm ⟨p,hp⟩).comp continuous_subtype_val⟩
      exact (hp k).comp ((i k).codRestrict (S k) (fun y ↦ subset_closure (mem_range_self y))).continuous
    unfold locallyConvexFinalTopology
    rw [hs]
    exact hP.withSeminorms_eq

private theorem strictLF_of_embedded_strictLF_cover {ι E : Type*} [Countable ι]
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    {X : ι → Type*} [∀ t, AddCommGroup (X t)] [∀ t, Module ℂ (X t)] [∀ t, TopologicalSpace (X t)]
    (hLF : IsLFSpace E) (j : ∀ t, X t →L[ℂ] E) (hi : ∀ t, IsEmbedding (j t))
    (hx : ∀ t, IsStrictLFSpace (X t)) (hc : ∀ x, ∃ t y, j t y = x) : IsStrictLFSpace E := by
  let : T2Space E := hLF.1
  let S t := (hx t).2.choose
  have hS t := (hx t).2.choose_spec
  let u (p : ι × ℕ) := (j p.1).comp ((S p.1 p.2).subtypeL)
  have he (p : ι × ℕ) := embedded_frechet_range (u p) ((hi p.1).comp IsEmbedding.subtypeVal)
    ((hS p.1).2.1 p.2)
  apply strictLF_of_countable_frechet_cover hLF (fun p ↦ (u p).toLinearMap.range) (fun p ↦ (he p).1) (fun p ↦ (he p).2)
  intro x
  obtain ⟨t,y,rfl⟩ := hc x
  obtain ⟨n,hn⟩ := (hS t).2.2.1 y
  exact ⟨(t,n), ⟨y,hn⟩,rfl⟩
/-- Paper: Theorem 5.2.1.1(1), p. 230.
The global theta space is a strict LF-space.
Deviation: The Fréchet stages inherit nuclearity from the separately stated
nuclearity of the whole space under `isNuclearTVS_submodule`. -/
theorem globalAdelicThetaSpace_strictLF : IsStrictLFSpace Θ𝔽 := by
  let : Countable (HeightOneSpectrum (𝓞 F)) := finitePlaces_countable F
  let j (S : Finset (HeightOneSpectrum (𝓞 F))) : Θₛ(S) →L[ℂ] Θ𝔽 :=
    ⟨sLocalThetaToGlobal F S, sLocalThetaToGlobal_continuous (F := F) (S := S)⟩
  exact strictLF_of_embedded_strictLF_cover (globalAdelicThetaSpace_lf (F := F)) j
    (fun S ↦ sLocalThetaToGlobal_isEmbedding (F := F) (S := S))
    (fun S ↦ sLocalAdelicThetaSpace_strictLF (F := F) (S := S))
    (sLocalThetaToGlobal_exhaustive (F := F))

/-- Paper: Theorem 5.2.1.1(1), p. 230.
The global theta quotient is complete. -/
theorem globalAdelicThetaSpace_complete :
    @CompleteSpace Θ𝔽 (IsTopologicalAddGroup.rightUniformSpace Θ𝔽) := by
  exact IsStrictLFSpace.completeSpace (E := Θ𝔽) globalAdelicThetaSpace_strictLF

/-- Paper: Theorem 5.2.1.1(1), p. 230.
Closed bounded subsets are compact in the global theta quotient. -/
theorem globalAdelicThetaSpace_montel : MontelSpace ℂ Θ𝔽 := montelSpace_of_nuclear_strictLF.{0} globalAdelicThetaSpace_strictLF
    globalAdelicThetaSpace_nuclear

/-- Paper: Theorem 5.2.1.1(1), p. 230.
The strong dual of the global theta quotient is nuclear. -/
theorem globalAdelicThetaSpace_strongDual_nuclear : IsNuclearTVS (StrongDual ℂ Θ𝔽) := by
  apply nuclear_of_linear_embedding (ContinuousLinearMap.precomp ℂ (K𝔽).mkQL)
  · exact isEmbedding_transpose_quotient_of_strictLF _ (adeleSchwartz_strictLF (F := F)).2
      (adeleSchwartz_nuclear (F := F)).2 adelicTheta_ker_isClosed globalAdelicThetaSpace_strictLF
  · exact (adeleSchwartz_strongDual_nuclear (F := F)).2

/-- Paper: Theorem 5.2.1.1(1), p. 230.
The strong dual of the global theta quotient is barrelled. -/
theorem globalAdelicThetaSpace_strongDual_barrelled :
    BarrelledSpace ℂ (StrongDual ℂ Θ𝔽) := by
    let : T2Space Θ𝔽 := (globalAdelicThetaSpace_lf (F := F) ).1
    let : PolynormableSpace ℂ Θ𝔽 := globalAdelicThetaSpace_polynormable
    let : MontelSpace ℂ Θ𝔽 := globalAdelicThetaSpace_montel
    exact barrelled_strongDual_of_montel

/-- Paper: Theorem 5.2.1.1(1), p. 230.
Closed bounded subsets are compact in the strong dual of the global theta quotient. -/
theorem globalAdelicThetaSpace_strongDual_montel : MontelSpace ℂ (StrongDual ℂ Θ𝔽) := by
  let : UniformSpace Θ𝔽 := IsTopologicalAddGroup.rightUniformSpace _
  let : IsUniformAddGroup Θ𝔽 := isUniformAddGroup_of_addCommGroup
  let : BarrelledSpace ℂ Θ𝔽 := globalAdelicThetaSpace_barrelled (F := F)
  exact montelSpace_strongDual_of_precompact (fun _ hb ↦ globalAdelicThetaSpace_bounded_totallyBounded (F := F) hb)

/-- Paper: (5.2.1.4), p. 231.
The transpose of the global theta quotient map is an embedding for the strong dual topologies. -/
theorem globalThetaQuotient_transpose_isEmbedding :
    IsEmbedding (fun l : StrongDual ℂ Θ𝔽 ↦ l.comp (K𝔽).mkQL) := by
  exact isEmbedding_transpose_quotient_of_strictLF _ (adeleSchwartz_strictLF (F := F)).2
    (adeleSchwartz_nuclear (F := F)).2 adelicTheta_ker_isClosed globalAdelicThetaSpace_strictLF

end GlobalTopology

section HomogeneousQuotients

-- TODO(paper-gap): Footnote 3 on p. 232 asks to adjust the introduction
-- to §5.2.2 without specifying the adjustment.

-- Use the Borel structure and the Haar normalization in §3.3.1, as in §5.1.
local instance normOneSIdeleQuotientMeasurableSpaceSec2 (F : Type*) [Field F]
    [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) :
    MeasurableSpace (MonoidHom.ker (sIdeleQuotientNorm F S)) := borel _

local instance normOneSIdeleQuotientHaarSec2 :
    Measure.IsHaarMeasure (sLocalNormOneQuotientMeasure F S) :=
  (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1

variable (F) in
/-- Paper: Definition 5.2.2.1(1), p. 232.
The global homogeneous theta transform is the complex-linear map of §2.2.5. -/
def homogeneousAdelicThetaLinearMap (ω : PontryaginDual C₁) :
    ℬ𝔽 →ₗ[ℂ] C(C𝔽, ℂ) :=
  IsLinearMap.mk' (homogeneousAdelicTheta ω) (homogeneousAdelicTheta_isLinear ω)

/-- Paper: Definition 5.2.2.1(1), p. 232.
The linear transform evaluates to the global homogeneous theta function. -/
theorem homogeneousAdelicThetaLinearMap_apply (ω : PontryaginDual C₁) (f : ℬ𝔽) :
    homogeneousAdelicThetaLinearMap F ω f = homogeneousAdelicTheta ω f := rfl

variable (F S) in
/-- Paper: Definition 5.2.2.1(2), p. 232.
The S-local homogeneous theta transform uses the norm-one quotient measure of §3.3.1. -/
def sLocalHomogeneousAdelicThetaLinearMap (ω : PontryaginDual (J₁(S))) :
    ℬₛ(S) →ₗ[ℂ] C(Jₛ(S), ℂ) :=
  sLocalHomogeneousAdelicTheta F S (sLocalNormOneQuotientMeasure F S) ω

/-- Paper: Definition 5.2.2.1(2), p. 232.
The linear transform evaluates to the S-local homogeneous theta function
with the norm-one Tamagawa measure of §3.3.1. -/
theorem sLocalHomogeneousAdelicThetaLinearMap_apply (ω : PontryaginDual (J₁(S)))
    (f : ℬₛ(S)) (g : Jₛ(S)) :
    sLocalHomogeneousAdelicThetaLinearMap F S ω f g =
      ∫ h : J₁(S), sLocalAdelicThetaOnClasses F S f (g * h.val) * (ω h : ℂ)
        ∂sLocalNormOneQuotientMeasure F S := rfl

local notation "K𝔽ω(" ω ")" => LinearMap.ker (homogeneousAdelicThetaLinearMap F ω)
local notation "Kₛω(" ω ")" => LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap F _ ω)

variable (F) in
/-- Paper: Definition 5.2.2.1(1), p. 232.
The global homogeneous theta space is the topological quotient of Schwartz–Bruhat
functions by the kernel of the homogeneous theta transform. -/
abbrev GlobalHomogeneousThetaSpace (ω : PontryaginDual C₁) :=
  ℬ𝔽 ⧸ K𝔽ω(ω)

private theorem quotient_ker_mk_eq {R X Y : Type*} [Ring R] [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] (θ : X →ₗ[R] Y) (f g : X) :
    θ.ker.mkQ f = θ.ker.mkQ g ↔ θ f = θ g := by
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, LinearMap.mem_ker, map_sub, sub_eq_zero]

/-- Paper: Definition 5.2.2.1(1), p. 232.
Two test functions give the same global homogeneous theta class exactly when
their homogeneous theta functions agree. -/
theorem globalHomogeneousThetaSpace_mk_eq_iff (ω : PontryaginDual C₁) (f g : ℬ𝔽) :
    (Submodule.Quotient.mk f : GlobalHomogeneousThetaSpace F ω) = Submodule.Quotient.mk g ↔
      homogeneousAdelicTheta ω f = homogeneousAdelicTheta ω g := quotient_ker_mk_eq (homogeneousAdelicThetaLinearMap F ω) f g

variable (F S) in
/-- Paper: Definition 5.2.2.1(2), p. 232.
The S-local homogeneous theta space is the topological quotient of S-local
Schwartz–Bruhat functions by the kernel of the S-local homogeneous transform.

Kept as an `abbrev` for now (#5398): as a `def` with its own instances it breaks proofs and
statements that use it, see the issue. Do not copy this pattern: a new type synonym with
structure is a `def` with its own instances (`AGENTS.md`). -/
abbrev SLocalHomogeneousThetaSpace (ω : PontryaginDual (J₁(S))) :=
  ℬₛ(S) ⧸ Kₛω(ω)

/-- Paper: Definition 5.2.2.1(2), p. 232.
Two S-local test functions give the same homogeneous theta class exactly when
their homogeneous theta functions agree. -/
theorem sLocalHomogeneousThetaSpace_mk_eq_iff (ω : PontryaginDual (J₁(S))) (f g : ℬₛ(S)) :
    (Submodule.Quotient.mk f : SLocalHomogeneousThetaSpace F S ω) = Submodule.Quotient.mk g ↔
      sLocalHomogeneousAdelicThetaLinearMap F S ω f =
        sLocalHomogeneousAdelicThetaLinearMap F S ω g := quotient_ker_mk_eq (sLocalHomogeneousAdelicThetaLinearMap F S ω) f g

section CoinvariantAverages

open Set

private theorem quotientEquiv_of_comap {X : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    (K H : Submodule ℂ X) (D : Submodule ℂ (X ⧸ K)) (h : H = D.comap K.mkQ) :
    ∃ e : (X ⧸ H) ≃L[ℂ] ((X ⧸ K) ⧸ D), ∀ f, e (H.mkQ f) = D.mkQ (K.mkQ f) := by
  let q := D.mkQ.comp K.mkQ
  have hq : H = q.ker := h.trans (by rw [LinearMap.ker_comp, Submodule.ker_mkQ])
  let e := (Submodule.quotEquivOfEq _ _ hq).trans (q.quotKerEquivOfSurjective
    (D.mkQ_surjective.comp K.mkQ_surjective))
  have he (f : X) : e (H.mkQ f) = q f := q.quotKerEquivOfSurjective_apply_mk (D.mkQ_surjective.comp K.mkQ_surjective) f
  have hquot : IsQuotientMap q := D.isQuotientMap_mkQ.comp K.isQuotientMap_mkQ
  have hcont : Continuous e := H.isQuotientMap_mkQ.continuous_iff.mpr
    (hquot.continuous.congr fun f ↦ (he f).symm)
  have hinv : Continuous e.symm := hquot.continuous_iff.mpr
    (H.mkQL.continuous.congr fun f ↦ (e.symm_apply_eq.mpr (he f).symm).symm)
  exact ⟨⟨e, hcont, hinv⟩, he⟩

private theorem ker_isotypicIntegral {G E A : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℂ E] [PolynormableSpace ℂ E] [T2Space E]
    (hcomplete : @CompleteSpace E (IsTopologicalAddGroup.rightUniformSpace E))
    (μ : Measure G) [μ.IsHaarMeasure] (ρ : G →* (E →L[ℂ] E))
    (hρ : Continuous fun p : G × E ↦ ρ p.1 p.2) (ω : PontryaginDual G)
    (ev : A → StrongDual ℂ E) (hsep : ∀ x, (∀ a, ev a x = 0) → x = 0) (x : E) :
    x ∈ (Submodule.span ℂ (range (fun p : G × E ↦
      p.2 - star (ω p.1 : ℂ) • ρ p.1 p.2))).topologicalClosure ↔
      ∀ a, (∫ g, star (ω g : ℂ) * ev a (ρ g x) ∂μ) = 0 := by
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  let : CompleteSpace E := hcomplete
  let : Module ℝ E := Module.restrictScalars ℝ ℂ E
  let : IsScalarTower ℝ ℂ E := IsScalarTower.restrictScalars ℝ ℂ E
  let : LocallyConvexSpace ℝ E := (PolynormableSpace.withSeminorms ℂ E).toLocallyConvexSpace
  let : SeparatingDual ℂ E := locallyConvexSpace_separatingDual ℂ E
  let A' (g : G) := star (ω g : ℂ) • ρ g
  have hA : Continuous fun p : G × E ↦ A' p.1 p.2 :=
    (show Continuous (fun p : G × E ↦ star (ω p.1 : ℂ)) from by fun_prop).smul hρ
  obtain ⟨P, hP, _⟩ := existsUnique_pettisIntegral_continuousFamily μ isCompact_univ
    (ae_of_all _ fun _ ↦ mem_univ _) A' hA
  have hav : IsPettisIsotypicAverageOn μ univ ρ ω P := by
    simpa [IsPettisIsotypicAverageOn, A'] using hP
  rw [← compactActionAverage_ker μ ρ hρ ω P hav, LinearMap.mem_ker]
  simp_rw [← compactActionAverage_dual_apply μ ρ ω P hav x]
  exact ⟨fun h a ↦ h ▸ map_zero _, hsep _⟩
private theorem thetaQuotientEval_separates {X A : Type*} [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] [TopologicalSpace A] (θ : X →ₗ[ℂ] C(A, ℂ))
    (hc : ∀ a, Continuous (fun f ↦ θ f a)) (x : X ⧸ θ.ker)
    (h : ∀ a, thetaQuotientEval θ a (hc a) x = 0) : x = 0 := by
  obtain ⟨f, rfl⟩ := θ.ker.mkQ_surjective x
  exact (Submodule.Quotient.mk_eq_zero _).mpr (ContinuousMap.ext h)

private theorem inv_character_integral {G : Type*} [CommGroup G] [TopologicalSpace G]
    [MeasurableSpace G] [MeasurableInv G] (μ : Measure G) [μ.IsInvInvariant]
    (ω : PontryaginDual G) (φ : G → ℂ) :
    (∫ g, star (ω g : ℂ) * φ g⁻¹ ∂μ) = ∫ g, φ g * (ω g : ℂ) ∂μ := by
  refine Eq.trans (integral_congr_ae (.of_forall fun g ↦ ?_))
    (integral_inv_eq_self (fun g ↦ φ g * (ω g : ℂ)) μ)
  rw [map_inv, Circle.coe_inv_eq_conj, mul_comm]
  rfl

private theorem coinvariantEquiv_of_formula {G E A B : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℂ E] [TopologicalSpace A] [TopologicalSpace B]
    (θ : E →ₗ[ℂ] C(A, ℂ)) (cθ : ∀ a, Continuous (fun f ↦ θ f a))
    [PolynormableSpace ℂ (E ⧸ θ.ker)] [T2Space (E ⧸ θ.ker)]
    (hcomplete : @CompleteSpace (E ⧸ θ.ker) (IsTopologicalAddGroup.rightUniformSpace _))
    (μ : Measure G) [μ.IsHaarMeasure] (ρ : G →* ((E ⧸ θ.ker) →L[ℂ] (E ⧸ θ.ker)))
    (hρ : Continuous fun p : G × (E ⧸ θ.ker) ↦ ρ p.1 p.2) (ω : PontryaginDual G)
    (H : E →ₗ[ℂ] C(B, ℂ)) (j : A → B) (hj : Surjective j)
    (h : ∀ f a, (∫ g, star (ω g : ℂ) * thetaQuotientEval θ a (cθ a) (ρ g (θ.ker.mkQ f)) ∂μ) =
      H f (j a)) :
    let D := (Submodule.span ℂ (range (fun p : G × (E ⧸ θ.ker) ↦
      p.2 - star (ω p.1 : ℂ) • ρ p.1 p.2))).topologicalClosure
    ∃ e : (E ⧸ H.ker) ≃L[ℂ] ((E ⧸ θ.ker) ⧸ D),
      ∀ f, e (H.ker.mkQ f) = D.mkQ (θ.ker.mkQ f) := by
  apply quotientEquiv_of_comap
  refine Submodule.ext fun f ↦ ?_
  refine Iff.trans ?_ (ker_isotypicIntegral hcomplete μ ρ hρ ω
    (fun a ↦ thetaQuotientEval θ a (cθ a)) (thetaQuotientEval_separates θ cθ) _).symm
  refine ⟨fun hf a ↦ (h f a).trans (congrArg (fun s : C(B, ℂ) ↦ s (j a)) (LinearMap.mem_ker.mp hf)),
    fun he ↦ LinearMap.mem_ker.mpr (ContinuousMap.ext fun b ↦ ?_)⟩
  obtain ⟨a, rfl⟩ := hj b
  exact (h f a).symm.trans (he a)

/-- A character average on a compact subgroup identifies the homogeneous quotient with
the quotient by the closed span of the twisted differences. The ordinary theta
quotient must be complete, and its point evaluations separate its elements. -/
theorem thetaQuotient_equiv_coinvariants_of_average {G E A B : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] (N : Subgroup G) [CompactSpace N] [T2Space N] [MeasurableSpace N]
    [BorelSpace N] [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℂ E] [TopologicalSpace A] [TopologicalSpace B]
    (θ : E →ₗ[ℂ] C(A, ℂ)) (cθ : ∀ a, Continuous (fun f ↦ θ f a))
    [PolynormableSpace ℂ (E ⧸ θ.ker)] [T2Space (E ⧸ θ.ker)]
    (hcomplete : @CompleteSpace (E ⧸ θ.ker) (IsTopologicalAddGroup.rightUniformSpace _))
    (μ : Measure N) [μ.IsHaarMeasure] (ρ : G →* ((E ⧸ θ.ker) →L[ℂ] (E ⧸ θ.ker)))
    (hρ : Continuous fun p : G × (E ⧸ θ.ker) ↦ ρ p.1 p.2) (ω : PontryaginDual N)
    (H : E →ₗ[ℂ] C(B, ℂ)) (j : A → B) (hj : Surjective j)
    (φ : E → A → N → ℂ)
    (hφ : ∀ (g : N) f a, thetaQuotientEval θ a (cθ a) (ρ g.val (θ.ker.mkQ f)) = φ f a g⁻¹)
    (hH : ∀ f a, H f (j a) = ∫ g, φ f a g * (ω g : ℂ) ∂μ) :
    let D := (Submodule.span ℂ (range (fun p : N × (E ⧸ θ.ker) ↦
      p.2 - star (ω p.1 : ℂ) • ρ p.1.val p.2))).topologicalClosure
    ∃ e : (E ⧸ H.ker) ≃L[ℂ] ((E ⧸ θ.ker) ⧸ D),
      ∀ f, e (Submodule.Quotient.mk f) = D.mkQ (θ.ker.mkQ f) := by
  refine coinvariantEquiv_of_formula θ cθ hcomplete μ (ρ.comp N.subtype)
    (hρ.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)) ω H j hj ?_
  intro f a
  exact (integral_congr_ae (μ := μ) (.of_forall fun g : N ↦
    congrArg (star (ω g : ℂ) * ·) (hφ g f a))).trans
      ((inv_character_integral μ ω (φ f a)).trans (hH f a).symm)

/-- On the global theta quotient, translation shifts the argument of every evaluation. -/
theorem globalThetaAction_eval
    (ρ : C𝔽 →* (Θ𝔽 →L[ℂ] Θ𝔽))
    (h : ∀ (g : IdeleGroup (𝓞 F) F) f, ρ (QuotientGroup.mk g) ((K𝔽).mkQ f) =
      (K𝔽).mkQ (schwartzBruhatUnitTranslate g f)) (f : ℬ𝔽) (a q : C𝔽)
    (hc : Continuous (fun f ↦ (adelicThetaLinearMap F f) a)) :
    thetaQuotientEval (adelicThetaLinearMap F) a hc
      (ρ q ((K𝔽).mkQ f)) = adelicTheta f (q⁻¹ * a) :=
  QuotientGroup.induction_on q fun g ↦ (congrArg
    (thetaQuotientEval (adelicThetaLinearMap F) a (adelicTheta_eval_continuous a))
    (h g f)).trans (globalTheta_translate_apply g f a)

end CoinvariantAverages

private theorem global_coinvariants_of_action
    (ρ : C𝔽 →* (Θ𝔽 →L[ℂ] Θ𝔽))
    (horbit : Continuous (fun p : C𝔽 × Θ𝔽 ↦ ρ p.1 p.2))
    (hrep : ∀ (g : IdeleGroup (𝓞 F) F) (f : ℬ𝔽), ρ (QuotientGroup.mk g) (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (schwartzBruhatUnitTranslate g f))
    (ω : PontryaginDual C₁) :
    let D := (Submodule.span ℂ (Set.range (fun p : C₁ × Θ𝔽 ↦
      p.2 - star (ω p.1 : ℂ) • ρ p.1.val p.2))).topologicalClosure
    ∃ e : GlobalHomogeneousThetaSpace F ω ≃L[ℂ] (Θ𝔽 ⧸ D),
      ∀ f : ℬ𝔽, e (Submodule.Quotient.mk f) = D.mkQ ((K𝔽).mkQ f) := by
  let μ := normOneIdeleClassTamagawaMeasure F
  let : MeasurableSpace C𝔽 := borel _
  let : BorelSpace C𝔽 := ⟨rfl⟩
  let : T2Space C₁ := (ideleClassGroup_finiteness F).2.2.1
  let : CompactSpace C₁ := (ideleClassGroup_finiteness F).2.1
  let : μ.IsHaarMeasure := (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  let : T2Space Θ𝔽 := globalAdelicThetaSpace_t2_of_isClosed (F := F) (adelicTheta_ker_isClosed (F := F))
  let : PolynormableSpace ℂ Θ𝔽 := globalAdelicThetaSpace_polynormable (F := F)
  let φ (f : ℬ𝔽) (a : C𝔽) (g : C₁) := adelicTheta f (g.val * a)
  have heval (g : C₁) (f : ℬ𝔽) (a : C𝔽) :
      thetaQuotientEval (adelicThetaLinearMap F) a (adelicTheta_eval_continuous a)
        (ρ g.val ((K𝔽).mkQ f)) = φ f a g⁻¹ := by
    exact globalThetaAction_eval (F := F) ρ hrep f a g.val (adelicTheta_eval_continuous a)
  have hint (f : ℬ𝔽) (a : C𝔽) :
      homogeneousAdelicThetaLinearMap F ω f a = ∫ g, φ f a g * (ω g : ℂ) ∂μ := rfl
  have cθ (a : C𝔽) : Continuous (fun f ↦ adelicThetaLinearMap F f a) :=
    (adelicTheta_eval_continuous (F := F) a).congr fun f ↦
      DFunLike.congr_fun (adelicThetaLinearMap_apply (F := F) f).symm a
  have hj : Surjective (fun a : C𝔽 ↦ a) := surjective_id
  with_reducible_and_instances
    exact thetaQuotient_equiv_coinvariants_of_average (G := C𝔽) (E := ℬ𝔽) (A := C𝔽) (B := C𝔽)
      (MonoidHom.ker (ideleClassNorm F)) (adelicThetaLinearMap F) cθ
      (globalAdelicThetaSpace_complete (F := F)) μ ρ horbit ω (homogeneousAdelicThetaLinearMap F ω)
      (fun a : C𝔽 ↦ a) hj φ heval hint

/-- Paper: Definition 5.2.2.1(1), p. 232.
The homogeneous theta quotient identifies canonically with the quotient of ordinary
theta space by the closed span of the character-twisted translation differences. -/
theorem globalHomogeneousThetaSpace_equiv_coinvariants (ω : PontryaginDual C₁) :
    let ρ := (existsUnique_globalThetaAction (F := F)).exists.choose
    let D := (Submodule.span ℂ (Set.range (fun p : C₁ × Θ𝔽 ↦
      p.2 - star (ω p.1 : ℂ) • ρ p.1.val p.2))).topologicalClosure
    ∃ e : GlobalHomogeneousThetaSpace F ω ≃L[ℂ] (Θ𝔽 ⧸ D),
      ∀ f : ℬ𝔽, e (Submodule.Quotient.mk f) = D.mkQ ((K𝔽).mkQ f) := by
  with_reducible_and_instances
    exact global_coinvariants_of_action (F := F) (existsUnique_globalThetaAction (F := F)).exists.choose
      (existsUnique_globalThetaAction (F := F)).exists.choose_spec.1
      (existsUnique_globalThetaAction (F := F)).exists.choose_spec.2 ω

/-- On local test representatives the translation action shifts the S-idele class
in the theta evaluation by the inverse translating class. -/
theorem sLocalThetaAction_eval
    (ρ : Jₛ(S) →* (Θₛ(S) →L[ℂ] Θₛ(S)))
    (h : ∀ (g : (SAdeleRing F S)ˣ) f, ρ (QuotientGroup.mk g) ((Kₛ(S)).mkQ f) =
      (Kₛ(S)).mkQ (schwartzBruhatUnitTranslate g f)) (f : ℬₛ(S)) (a : (SAdeleRing F S)ˣ) (q : Jₛ(S))
    (hc : Continuous (fun f ↦ sLocalAdelicTheta F S f a)) :
    thetaQuotientEval (sLocalAdelicTheta F S) a hc
      (ρ q ((Kₛ(S)).mkQ f)) = sLocalAdelicThetaOnClasses F S f (QuotientGroup.mk a * q⁻¹) := by
  let π : (SAdeleRing F S)ˣ →* Jₛ(S) := QuotientGroup.mk' _
  refine QuotientGroup.induction_on q fun g ↦ (congrArg
    (thetaQuotientEval (sLocalAdelicTheta F S) a (sLocalAdelicTheta_continuous_eval a)) (h g f)).trans ?_
  exact (localTheta_translate_apply g a f).trans
    ((sLocalAdelicThetaOnClasses_mk F S f (g⁻¹ * a)).symm.trans
      (congrArg (sLocalAdelicThetaOnClasses F S f) ((π.map_mul _ _).trans
        ((congrArg (· * π a) (π.map_inv g)).trans (mul_comm ((π g)⁻¹) (π a))))))

private theorem local_coinvariants_of_action
    (ρ : Jₛ(S) →* (Θₛ(S) →L[ℂ] Θₛ(S)))
    (horbit : Continuous (fun p : Jₛ(S) × Θₛ(S) ↦ ρ p.1 p.2))
    (hrep : ∀ (g : (SAdeleRing F S)ˣ) (f : ℬₛ(S)), ρ (QuotientGroup.mk g) (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (schwartzBruhatUnitTranslate g f))
    (ω : PontryaginDual (J₁(S))) :
    let D := (Submodule.span ℂ (Set.range (fun p : J₁(S) × Θₛ(S) ↦
      p.2 - star (ω p.1 : ℂ) • ρ p.1.val p.2))).topologicalClosure
    ∃ e : SLocalHomogeneousThetaSpace F S ω ≃L[ℂ] (Θₛ(S) ⧸ D),
      ∀ f : ℬₛ(S), e (Submodule.Quotient.mk f) = D.mkQ ((Kₛ(S)).mkQ f) := by
  let μ := sLocalNormOneQuotientMeasure F S
  have hclosed := isClosed_sProjectedDiagonal (F := F) (S := S)
  let : T2Space (Jₛ(S)) := inferInstanceAs (T2Space (_ ⧸ _))
  let : T2Space (J₁(S)) := inferInstanceAs (T2Space ((sIdeleQuotientNorm F S).ker : Set (Jₛ(S))))
  let : BorelSpace (J₁(S)) := ⟨rfl⟩
  let : CompactSpace (J₁(S)) := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage (isCompact_singleton (x := 1)))
  let : T2Space (Θₛ(S)) := sLocalAdelicThetaSpace_t2_of_isClosed (F := F) (S := S) (sLocalAdelicTheta_ker_isClosed (F := F) (S := S))
  let : PolynormableSpace ℂ (Θₛ(S)) := sLocalAdelicThetaSpace_polynormable (F := F) (S := S)
  let φ (f : ℬₛ(S)) (a : (SAdeleRing F S)ˣ) (g : J₁(S)) :=
    sLocalAdelicThetaOnClasses F S f (QuotientGroup.mk a * g.val)
  have heval (g : J₁(S)) (f : ℬₛ(S)) (a : (SAdeleRing F S)ˣ) :
      thetaQuotientEval (sLocalAdelicTheta F S) a (sLocalAdelicTheta_continuous_eval a)
        (ρ g.val ((Kₛ(S)).mkQ f)) = φ f a g⁻¹ := sLocalThetaAction_eval (F := F) (S := S) ρ hrep f a g.val (sLocalAdelicTheta_continuous_eval a)
  have hint (f : ℬₛ(S)) (a : (SAdeleRing F S)ˣ) :
      sLocalHomogeneousAdelicThetaLinearMap F S ω f (QuotientGroup.mk a) =
        ∫ g, φ f a g * (ω g : ℂ) ∂μ := rfl
  with_reducible_and_instances
    exact thetaQuotient_equiv_coinvariants_of_average (G := Jₛ(S)) (E := ℬₛ(S)) (A := (SAdeleRing F S)ˣ) (B := Jₛ(S))
      (MonoidHom.ker (sIdeleQuotientNorm F S)) (sLocalAdelicTheta F S)
      (sLocalAdelicTheta_continuous_eval (F := F) (S := S)) (sLocalAdelicThetaSpace_complete (F := F) (S := S))
      μ ρ horbit ω (sLocalHomogeneousAdelicThetaLinearMap F S ω) (QuotientGroup.mk : (SAdeleRing F S)ˣ → Jₛ(S))
      QuotientGroup.mk_surjective φ heval hint

/-- Paper: Definition 5.2.2.1(2), p. 232.
The S-local homogeneous quotient identifies canonically with the quotient of ordinary
S-local theta space by the closed span of the twisted norm-one translation differences. -/
theorem sLocalHomogeneousThetaSpace_equiv_coinvariants (ω : PontryaginDual (J₁(S))) :
    let ρ := (existsUnique_sLocalThetaAction (F := F) (S := S)).exists.choose
    let D := (Submodule.span ℂ (Set.range (fun p : J₁(S) × Θₛ(S) ↦
      p.2 - star (ω p.1 : ℂ) • ρ p.1.val p.2))).topologicalClosure
    ∃ e : SLocalHomogeneousThetaSpace F S ω ≃L[ℂ] (Θₛ(S) ⧸ D),
      ∀ f : ℬₛ(S), e (Submodule.Quotient.mk f) = D.mkQ ((Kₛ(S)).mkQ f) := by
  with_reducible_and_instances
    exact local_coinvariants_of_action (F := F) (S := S)
      (existsUnique_sLocalThetaAction (F := F) (S := S)).exists.choose
      (existsUnique_sLocalThetaAction (F := F) (S := S)).exists.choose_spec.1
      (existsUnique_sLocalThetaAction (F := F) (S := S)).exists.choose_spec.2 ω

end HomogeneousQuotients

-- The first digest ends at Definition 5.2.2.1. The isotypic structure
-- results and the Fourier descent statements remain for a subsequent digest.
-- TODO(continuation): (5.2.2.2), Theorem 5.2.3.1, Proposition 5.2.3.2,
-- Remarks 5.2.3.3–5.2.3.5 and the individual involutions in Theorem 5.2.4.1.
-- TODO(paper-gap): The global L² argument on p. 237 fails for the rational
-- Gaussian, whose theta is asymptotic to 1/t at the origin. Character
-- uniqueness can be applied on each compact norm-one fiber instead.
-- TODO(paper-gap): On p. 234 the proof of Theorem 5.2.3.1 refers to the
-- descending idempotent as "(??)". The proof on p. 231 does not construct
-- a kernel-preserving Schwartz–Bruhat projection.
-- TODO(paper-gap): In Remark 5.2.3.4 the topology induced from the theta
-- quotient is called Hausdorff on the test space. For ℚ it identifies every
-- odd test function with zero.
-- TODO(paper-gap): The Fourier compatibility in Theorem 5.2.4.1 fails upon
-- adding a place dividing the different. For ℚ(i) at the place above 2,
-- Fourier sends the integer indicator to half the inverse-different indicator.

end RiemannMasullo
