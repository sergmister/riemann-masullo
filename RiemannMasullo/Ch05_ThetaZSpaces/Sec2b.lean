module

public import RiemannMasullo.Ch05_ThetaZSpaces.Sec2

import RiemannMasullo.Ch03_IdelicZeta.Sec2
import RiemannMasullo.Ch03_IdelicZeta.Sec4
import all RiemannMasullo.Ch05_ThetaZSpaces.Sec2
import all RiemannMasullo.AppD_SchwartzBruhat.Sec1b
import all RiemannMasullo.AppA_AlgebraicNT.Sec3
import RiemannMasullo.ForMathlib.Topology.Algebra.Group.AutomaticContinuity
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.Separable
public import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec3b
import all RiemannMasullo.Ch04_PeriodicSchauderBases.Sec3b
import RiemannMasullo.ForMathlib.Topology.Algebra.Module.StrongDualQuotient
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.StrongDual
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.StrongBidual

import all RiemannMasullo.Ch05_ThetaZSpaces.Sec2
import RiemannMasullo.ForMathlib.Topology.ContinuousMap.Sigma
import RiemannMasullo.ForMathlib.MeasureTheory.Integral.Bochner.Regular
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace

import Mathlib.MeasureTheory.Integral.Pi

import all RiemannMasullo.AppC_LCTVS.Sec1

import all RiemannMasullo.AppC_LCTVS.Sec1

/-! # Homogeneous theta spaces and Fourier descent

Masullo, §5.2.2–5.2.4, pp. 232–239. Every S-local space includes all archimedean places.
-/

@[expose] public noncomputable section

open Bornology Filter Function IsDedekindDomain MeasureTheory NumberField Topology
open scoped NumberField.AdeleRing NNReal

namespace RiemannMasullo

set_option quotPrecheck false

section MeromorphicComponents

variable {G : Type*} [CommGroup G] [TopologicalSpace G]
variable (m : G →* ℝ≥0ˣ) (hm : Continuous m) (ω : PontryaginDual m.ker)

local notation "Ωω(" χ ")" => {c : QuasiCharacter G // ∀ g : m.ker, c g.val = (χ g : ℂ)}

/-- Paper: (5.2.2.1), p. 232.
Twisting a quasi-character by a complex power of the norm preserves its norm-one restriction. -/
theorem quasiCharacterNormTwist_mem_component (c : Ωω(ω)) (z : ℂ) :
    ∀ g : m.ker, quasiCharacterNormTwist m hm c.val z g.val = (ω g : ℂ) := by
  intro g
  change c.val g.val * ((((m g.val : ℝ≥0) : ℝ) : ℂ)) ^ z = _
  rw [MonoidHom.mem_ker.mp g.property, Units.val_one, NNReal.coe_one, Complex.ofReal_one,
    Complex.one_cpow, mul_one]
  exact c.property g

/-- Paper: (5.2.2.2), p. 232.
The meromorphic space on a component uses the pole bounds restricted to that component.
Its topology is compact convergence on the component's regular locus. -/
def meromorphicNormOneComponent (orderBound : QuasiCharacter G → WithTop ℤ) :
    Submodule ℂ C({c : Ωω(ω) // 0 ≤ orderBound c.val}, ℂ) :=
  meromorphicWithPoleBound (X := Ωω(ω))
    (fun c z ↦ ⟨quasiCharacterNormTwist m hm c.val z,
      quasiCharacterNormTwist_mem_component m hm ω c z⟩)
    (fun c ↦ orderBound c.val)

/-- Restriction and gluing for meromorphic functions on a disjoint open partition
preserved by the charts. The pole bound need not make the regular locus open. -/
private theorem meromorphicWithPoleBound_equiv_openPartition {X I : Type*} [TopologicalSpace X]
    (chart : X → ℂ → X) (b : X → WithTop ℤ) (U : I → Set X)
    (ho : ∀ i, IsOpen (U i)) (hu : ∀ x, ∃! i, x ∈ U i)
    (ht : ∀ i (x : U i) z, chart x z ∈ U i) :
    let V := fun i ↦ meromorphicWithPoleBound (X := U i)
      (fun x z ↦ ⟨chart x z, ht i x z⟩) (fun x ↦ b x.val)
    ∃ e : ↥(meromorphicWithPoleBound chart b) ≃L[ℂ] (∀ i, ↥(V i)),
      ∀ f i x, (e f i).val x = f.val ⟨x.val.val, x.property⟩ := by
  classical
  intro V
  let M := meromorphicWithPoleBound chart b
  let R := {x : X // 0 ≤ b x}
  let S := fun i ↦ {x : U i // 0 ≤ b x.val}
  let inc (i) : C(S i, R) := ⟨fun x ↦ ⟨x.val.val, x.property⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
  let idx (x : X) := (hu x).exists.choose
  have hidx (x : X) : x ∈ U (idx x) := (hu x).exists.choose_spec
  -- The regular locus itself is the topological sum of its pieces.
  let forget (p : Σ i, S i) : R := inc p.1 p.2
  have bij : Bijective forget := by
    constructor
    · rintro ⟨i, x⟩ ⟨j, y⟩ h
      have he : x.val.val = y.val.val := congrArg Subtype.val h
      have hij := (hu x.val.val).unique x.val.property (he ▸ y.val.property)
      subst j
      exact congrArg (Sigma.mk i) (Subtype.ext (Subtype.ext he))
    · intro x
      exact ⟨⟨idx x, ⟨⟨x, hidx x⟩, x.property⟩⟩, rfl⟩
  let D : (Σ i, S i) ≃ₜ R := (Equiv.ofBijective forget bij).toHomeomorphOfContinuousOpen
    (continuous_sigma fun i ↦ (inc i).continuous)
    (isOpenMap_sigma.mpr fun i ↦ (ho i).isOpenMap_subtype_val.restrictPreimage {x | 0 ≤ b x})
  let res (f : M) (i : I) : V i := ⟨f.val.comp (inc i), by
    obtain ⟨Z, hreg, hchart⟩ := f.property
    exact ⟨fun x ↦ Z x.val, fun x ↦ hreg (inc i x), fun x ↦ hchart x.val⟩⟩
  let onSum (f : ∀ i, V i) : C((Σ i, S i), ℂ) :=
    ⟨fun p ↦ (f p.1).val p.2, continuous_sigma fun i ↦ (f i).val.continuous⟩
  let assemble (f : ∀ i, V i) := (onSum f).comp (D.symm : C(R, (Σ i, S i)))
  have hpart (f : ∀ i, V i) (i : I) (x : S i) : assemble f (inc i x) = (f i).val x := by
    change onSum f (D.symm (D ⟨i, x⟩)) = _
    rw [D.symm_apply_apply]
    rfl
  let inv (f : ∀ i, V i) : M := ⟨assemble f, by
    -- Choose one continuation per piece. At any center, the entire germ stays
    -- in that piece, so the glued continuation inherits exactly the same order.
    choose Z hreg hchart using fun i ↦ (f i).property
    let glue (x : X) := Z (idx x) ⟨x, hidx x⟩
    have hg (i : I) (x : U i) : glue x.val = Z i x := by
      rcases x with ⟨x, hx⟩
      obtain rfl : i = idx x := (hu x).unique hx (hidx x)
      rfl
    refine ⟨glue, fun x ↦ ?_, fun x ↦ ?_⟩
    · let y : S (idx x.val) := ⟨⟨x.val, hidx x.val⟩, x.property⟩
      exact (hg _ y.val).trans ((hreg _ y).trans (hpart f _ y).symm)
    · let i := idx x
      let y : U i := ⟨x, hidx x⟩
      have he : (fun z ↦ glue (chart x z)) = fun z ↦ Z i ⟨chart x z, ht i y z⟩ :=
        funext fun z ↦ hg i ⟨chart x z, ht i y z⟩
      dsimp only
      rw [he]
      exact hchart i y⟩
  refine ⟨{ toFun := res
            invFun := inv
            map_add' := fun _ _ ↦ rfl
            map_smul' := fun _ _ ↦ rfl
            left_inv := ?_
            right_inv := ?_
            continuous_toFun := ?_
            continuous_invFun := ?_ }, fun _ _ _ ↦ rfl⟩
  · intro f
    apply Subtype.ext
    apply ContinuousMap.ext
    intro x
    obtain ⟨⟨i, y⟩, rfl⟩ := bij.surjective x
    exact hpart (res f) i y
  · intro f
    funext i
    exact Subtype.ext (ContinuousMap.ext (hpart f i))
  · exact continuous_pi fun i ↦ ((ContinuousMap.continuous_precomp (inc i)).comp
      continuous_subtype_val).subtype_mk _
  · have hsum : Continuous onSum := continuous_continuousMap_sigma_of_components _ fun i ↦
      show Continuous (fun f : ∀ i, V i ↦ (f i).val) from
        continuous_subtype_val.comp (continuous_apply i)
    exact ((ContinuousMap.continuous_precomp _).comp hsum).subtype_mk _


/-- Paper: (5.2.2.2), p. 232.
Restriction to the norm-one components identifies the meromorphic space with the product
of its component spaces, with their compact-convergence topologies.
Deviation: The two idelic instances are expressed by the common norm-chart statement.
The formula on regular values specifies the restriction map. -/
theorem meromorphicWithPoleBound_equiv_components [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] (hproper : IsProperMap m) (hn : ∃ g, m g ≠ 1)
    (orderBound : QuasiCharacter G → WithTop ℤ) :
    ∃ e : ↥(meromorphicWithPoleBound (quasiCharacterNormTwist m hm) orderBound) ≃L[ℂ]
        (∀ χ : PontryaginDual m.ker, ↥(meromorphicNormOneComponent m hm χ orderBound)),
      ∀ f χ c, (e f χ).val c = f.val ⟨c.val.val, c.property⟩ := by
  let U (χ : PontryaginDual m.ker) : Set (QuasiCharacter G) :=
    {c | ∀ g : m.ker, c g.val = (χ g : ℂ)}
  apply meromorphicWithPoleBound_equiv_openPartition (quasiCharacterNormTwist m hm) orderBound U
    _ _ (quasiCharacterNormTwist_mem_component m hm)
  · intro χ
    apply isOpen_iff_mem_nhds.mpr
    intro c hc
    obtain ⟨e, he, -, htwist⟩ := hasNormTwistCharts_of_proper m hproper hn c
    filter_upwards [e.open_source.mem_nhds he] with d hd
    intro g
    have h := htwist (e d) (e.map_source hd) g.val
    simp only [e.left_inv hd, show m g.val = 1 from g.property, Units.val_one, NNReal.coe_one,
      Complex.ofReal_one, Complex.one_cpow, mul_one] at h
    exact h.trans (hc g)
  · intro c
    obtain ⟨χ, hχ⟩ := (range_normOneRestriction m hproper hn ▸
      (Set.mem_range_self c : normOneRestriction m c ∈ Set.range (normOneRestriction m)))
    refine ⟨χ, fun g ↦ (DFunLike.congr_fun hχ g).symm, ?_⟩
    intro ψ hψ
    exact ContinuousMonoidHom.ext fun g ↦
      Circle.ext ((hψ g).symm.trans (DFunLike.congr_fun hχ g).symm)

end MeromorphicComponents

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
local notation "m𝔽" => ideleClassNorm F
local notation "mₛ(" S ")" => sIdeleQuotientNorm F S
local notation "C₁" => MonoidHom.ker m𝔽
local notation "J₁(" S ")" => MonoidHom.ker (mₛ(S))
local notation "Θ𝔽ω(" ω ")" => GlobalHomogeneousThetaSpace F ω
local notation "Θₛω(" S ", " ω ")" => SLocalHomogeneousThetaSpace F S ω
local notation "K𝔽ω(" ω ")" => LinearMap.ker (homogeneousAdelicThetaLinearMap F ω)
local notation "Kₛω(" S ", " ω ")" => LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap F S ω)

section StructureTheorem

-- TODO(paper-gap): Footnotes 4–6 on pp. 233–235 request revisions or flag unfinished
-- work. The proof invokes a descended stage projection through "(??)" on p. 234.
-- Equation (5.2.3.4) also omits the local Haar masses; see ERRATA I96.

/-- Paper: Theorem 5.2.3.1, p. 233.
A norm-one character is unramified outside S if it extends to an idelic quasi-character
unramified outside S. Norm twists are trivial on every local integer unit. -/
def NormOneCharacterUnramifiedOutside (ω : PontryaginDual C₁)
    (S : Finset (HeightOneSpectrum (𝓞 F))) : Prop :=
  ∃ c : unramifiedOutside F S, ∀ x : C₁, c.val x.val = (ω x : ℂ)

/-- An idele class character unramified outside `S` takes the same value at an idele that is
a unit outside `S` and at the reinsertion of its `S`-coordinates. The two differ by a family of
local integer units outside `S`, on which the character is trivial by continuity. -/
theorem normOneCharacterUnramifiedOutside_iff_reinsert (c : unramifiedOutside F S)
    (u : (integralAdelesOutside F S)ˣ) :
    c.val (QuotientGroup.mk (integralIdeleInsertion F S u)) =
      c.val (QuotientGroup.mk (sIdeleInsertion F S
        (Units.map (adeleProjection F S).toMonoidHom (integralIdeleInsertion F S u)))) := by
  classical
  let fin : (∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletionIntegers F)ˣ) →ₜ*
      IdeleClassGroup (𝓞 F) F :=
    let f : (∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletionIntegers F)) →* AdeleRing (𝓞 F) F :=
      (1 : _ →* InfiniteAdeleRing F).prod
        { toFun := RestrictedProduct.structureMap
            (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
            (fun v => ((v.adicCompletionIntegers F) : Set (v.adicCompletion F))) Filter.cofinite
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
    ⟨(QuotientGroup.mk' _).comp ((Units.map f).comp
      (ContinuousMulEquiv.piUnits.symm :
        (∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletionIntegers F)ˣ) ≃ₜ* _).toMonoidHom),
      QuotientGroup.continuous_mk.comp
        ((continuous_const.prodMk RestrictedProduct.isEmbedding_structureMap.continuous).units_map f
          |>.comp (ContinuousMulEquiv.piUnits.symm :
            (∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletionIntegers F)ˣ) ≃ₜ* _).continuous)⟩
  have hsingle (v : HeightOneSpectrum (𝓞 F)) (w : (v.adicCompletionIntegers F)ˣ) :
      fin (Pi.mulSingle v w) =
        IdeleClassGroup.ofAdicCompletion (𝓞 F) F v
          (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom w) := by
    apply congrArg (QuotientGroup.mk : IdeleGroup (𝓞 F) F → IdeleClassGroup (𝓞 F) F)
    apply Units.ext
    refine Prod.ext rfl ?_
    apply RestrictedProduct.ext
    intro w'
    change (((Pi.mulSingle v w : ∀ w : HeightOneSpectrum (𝓞 F),
        (w.adicCompletionIntegers F)ˣ) w').val :
        w'.adicCompletion F) =
      RestrictedProduct.mulSingle (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v
        (w.val : v.adicCompletion F) w'
    rcases eq_or_ne w' v with rfl | hw
    · rw [Pi.mulSingle_eq_same]
      exact (RestrictedProduct.mulSingle_eq_same _ _ _).symm
    · rw [Pi.mulSingle_eq_of_ne hw]
      exact (RestrictedProduct.mulSingle_eq_of_ne _ _ hw).symm
  let i := (integralAdelesOutside F S).subtype
  let a := Units.map i.toMonoidHom u
  let s := Units.map ((adeleProjection F S).comp i).toMonoidHom u
  let q := QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 F) F)
  let localEval (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S) :
      integralAdelesOutside F S →+* (v.adicCompletionIntegers F) :=
    (((RestrictedProduct.evalRingHom _ v).comp (RingHom.snd _ _)).comp i).codRestrict _
      (fun x => by
        have hx := x.property
        simp only [integralAdelesOutside, Subring.mem_iInf] at hx
        exact hx v hv)
  let outsideUnits (v : HeightOneSpectrum (𝓞 F)) : (v.adicCompletionIntegers F)ˣ :=
    if hv : v ∈ S then 1 else Units.map (localEval v hv).toMonoidHom u
  have hb : c.val (fin outsideUnits) = 1 := by
    let χ := c.val.comp fin
    have hp : HasProd (fun v => Pi.mulSingle v (outsideUnits v)) outsideUnits := by
      refine Pi.hasProd.mpr fun w => ?_
      convert hasProd_pi_single w (outsideUnits w) using 1
      funext v
      rcases eq_or_ne v w with rfl | hv
      · simp
      · simp [hv, hv.symm]
    refine (hp.map χ χ.continuous).unique (hasProd_one.congr_fun fun v => ?_)
    change c.val (fin (Pi.mulSingle v (outsideUnits v))) = 1
    by_cases hv : v ∈ S
    · simp [outsideUnits, hv]
    · rw [hsingle]
      have hc : ∀ v ∉ S, c.val.IsUnramifiedAt v := c.property
      have h := (hc v hv).restrict_apply_unit_eq_one (outsideUnits v)
      change c.val.restrict v
        ↑(Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom (outsideUnits v)) = 1 at h
      rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe] at h
      exact h
  have hfactor : q a = q (sIdeleInsertion F S s) * fin outsideUnits := by
    change q a = q (sIdeleInsertion F S s) * q _
    rw [← map_mul]
    apply congrArg q
    apply Units.ext
    obtain ⟨hinf, hin, hout⟩ := sIdeleInsertion_apply F S s
    refine Prod.ext ?_ ?_
    · change a.val.1 = (sIdeleInsertion F S s).val.1 * 1
      rw [mul_one, hinf]
      rfl
    · apply RestrictedProduct.ext
      intro v
      change a.val.2 v =
        (sIdeleInsertion F S s).val.2 v * ((outsideUnits v).val : v.adicCompletion F)
      by_cases hv : v ∈ S
      · rw [hin ⟨v, hv⟩]
        change a.val.2 v = a.val.2 v * ((outsideUnits v).val : v.adicCompletion F)
        simp [outsideUnits, hv]
      · rw [hout v hv, one_mul]
        dsimp [outsideUnits]
        rw [dite_eq_right hv]
        rfl
  have h := congrArg c.val hfactor
  rw [map_mul, hb, mul_one] at h
  exact h

/-- Every norm-one class of `S`-ideles is the projection of an idele that is a unit outside `S`
and whose idele class has norm one. -/
private theorem normOneCharacterUnramifiedOutside_iff_lift (y : J₁(S)) :
    ∃ (u : (integralAdelesOutside F S)ˣ) (x : C₁),
      x.val = QuotientGroup.mk (integralIdeleInsertion F S u) ∧
      y.val = QuotientGroup.mk
        (Units.map (adeleProjection F S).toMonoidHom (integralIdeleInsertion F S u)) := by
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective y.val
  have hmem : sIdeleInsertion F S a ∈ Set.range (integralIdeleInsertion F S) := by
    rw [mem_range_integralIdeleInsertion]
    intro v hv
    have h1 := (sIdeleInsertion_apply F S a).2.2 v hv
    have h2 := (sIdeleInsertion_apply F S a⁻¹).2.2 v hv
    rw [map_inv] at h2
    refine ⟨?_, ?_⟩
    · rw [h1]; exact one_mem _
    · change ((sIdeleInsertion F S a)⁻¹).val.2 v ∈ _
      rw [h2]; exact one_mem _
  obtain ⟨u, hu⟩ := hmem
  have hproj : Units.map (adeleProjection F S).toMonoidHom (integralIdeleInsertion F S u) = a := by
    rw [hu]
    obtain ⟨hinf, hin, -⟩ := sIdeleInsertion_apply F S a
    apply Units.ext
    refine Prod.ext hinf (funext fun v ↦ hin v)
  have hnorm : m𝔽 (QuotientGroup.mk (integralIdeleInsertion F S u)) = 1 := by
    rw [hu]
    change ideleNorm F (sIdeleInsertion F S a) = 1
    rw [ideleNorm_sIdeleInsertion, ← sIdeleQuotientNorm_mk, ha]
    exact y.property
  exact ⟨u, ⟨_, hnorm⟩, rfl, by rw [hproj, ha]⟩

/-- Paper: Remark 5.2.3.3, p. 236.
Unramifiedness is equivalent to unique descent to the norm-one S-idele quotient.
Deviation: The descent identity is tested on norm-one ideles integral outside S. -/
theorem normOneCharacterUnramifiedOutside_iff (ω : PontryaginDual C₁) :
    NormOneCharacterUnramifiedOutside (F := F) ω S ↔
      ∃! χ : PontryaginDual (J₁(S)),
        ∀ (u : (integralAdelesOutside F S)ˣ) (x : C₁) (y : J₁(S)),
          let g := integralIdeleInsertion F S u
          x.val = QuotientGroup.mk g →
          y.val = QuotientGroup.mk (Units.map (adeleProjection F S).toMonoidHom g) →
          χ y = ω x := by
  constructor
  · rintro ⟨c, hc⟩
    let r := sIdeleRestriction F S c
    have hval (u : (integralAdelesOutside F S)ˣ) (x : C₁) (y : J₁(S))
        (hx : x.val = QuotientGroup.mk (integralIdeleInsertion F S u))
        (hy : y.val = QuotientGroup.mk
          (Units.map (adeleProjection F S).toMonoidHom (integralIdeleInsertion F S u))) :
        r y.val = ω x := by
      rw [hy, sIdeleRestriction_mk, ← normOneCharacterUnramifiedOutside_iff_reinsert, ← hx, hc]
    have hr (y : J₁(S)) : r y.val ∈ Submonoid.unitSphere ℂ := by
      obtain ⟨u, x, hx, hy⟩ := normOneCharacterUnramifiedOutside_iff_lift y
      rw [hval u x y hx hy]
      exact (ω x).property
    let χ : PontryaginDual (J₁(S)) :=
      ⟨(r.toMonoidHom.comp (J₁(S)).subtype).codRestrict (Submonoid.unitSphere ℂ) hr,
        (r.continuous.comp continuous_subtype_val).subtype_mk _⟩
    refine ⟨χ, fun u x y hx hy ↦ Subtype.ext (hval u x y hx hy), fun χ' hχ' ↦ ?_⟩
    ext y
    obtain ⟨u, x, hx, hy⟩ := normOneCharacterUnramifiedOutside_iff_lift y
    rw [hχ' u x y hx hy]
    exact (hval u x y hx hy).symm
  · classical
    rintro ⟨χ, hχ, -⟩
    let τ : ℝ≥0ˣ →* C𝔽 :=
      (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 F) F)).comp (canonicalIdeleNormSection F)
    have hτ (t : ℝ≥0ˣ) : m𝔽 (τ t) = t := canonicalIdeleNormSection_rightInverse F t
    have hτc : Continuous τ :=
      QuotientGroup.continuous_mk.comp (canonicalIdeleNormSection_continuous F)
    let D₀ : C𝔽 →* C𝔽 := MonoidHom.id C𝔽 / τ.comp m𝔽
    have hD (x : C𝔽) : D₀ x ∈ C₁ := by
      rw [MonoidHom.mem_ker]
      simp [D₀, hτ]
    let D : C𝔽 →ₜ* C₁ := ⟨D₀.codRestrict _ hD,
      (continuous_id.div' (hτc.comp (isProperMap_ideleClassNorm F).continuous)).subtype_mk _⟩
    have hD1 (x : C₁) : D x.val = x := by
      apply Subtype.ext
      have hx : m𝔽 x.val = 1 := x.property
      change x.val / τ (m𝔽 x.val) = x.val
      rw [hx, map_one, div_one]
    let c : HeckeCharacter (𝓞 F) F :=
      (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp (ω.comp D)
    have hcu : c ∈ unramifiedOutside F S := by
      rw [mem_unramifiedOutside_iff]
      intro v hv w
      let gi := IdeleGroup.ofAdicCompletion (𝓞 F) F v
        (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom w)
      have hnorm : m𝔽 (QuotientGroup.mk gi) = 1 := by
        change m𝔽 (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v _) = 1
        rw [ideleClassNorm_ofAdicCompletion]
        apply Units.ext
        change ‖((w : (v.adicCompletionIntegers F)) : v.adicCompletion F)‖₊ = 1
        let a : v.adicCompletionIntegers F := w
        let b : v.adicCompletionIntegers F := ((w⁻¹ : (v.adicCompletionIntegers F)ˣ) :
          v.adicCompletionIntegers F)
        have h1 : ‖(a : v.adicCompletion F)‖ ≤ 1 :=
          Valued.toNormedField.norm_le_one_iff.mpr a.property
        have h2 : ‖(b : v.adicCompletion F)‖ ≤ 1 :=
          Valued.toNormedField.norm_le_one_iff.mpr b.property
        have h3 : ‖(a : v.adicCompletion F)‖ * ‖(b : v.adicCompletion F)‖ = 1 := by
          rw [← norm_mul, ← MulMemClass.coe_mul]
          simp only [a, b, Units.mul_inv, OneMemClass.coe_one, norm_one]
        apply NNReal.coe_injective
        simp only [coe_nnNorm, NNReal.coe_one]
        nlinarith [norm_nonneg (a : v.adicCompletion F), norm_nonneg (b : v.adicCompletion F)]
      obtain ⟨u, hu⟩ : gi ∈ Set.range (integralIdeleInsertion F S) := by
        rw [mem_range_integralIdeleInsertion]
        intro v' hv'
        have hc (z : (v.adicCompletion F)ˣ)
            (hz : (z : v.adicCompletion F) ∈ v.adicCompletionIntegers F) :
            (IdeleGroup.ofAdicCompletion (𝓞 F) F v z).val.2 v' ∈ (v'.adicCompletionIntegers F) := by
          change RestrictedProduct.mulSingle (fun w : HeightOneSpectrum (𝓞 F) ↦
            w.adicCompletionIntegers F) v z.val v' ∈ _
          rcases eq_or_ne v' v with rfl | hne
          · rw [RestrictedProduct.mulSingle_eq_same]
            exact hz
          · rw [RestrictedProduct.mulSingle_eq_of_ne _ _ hne]
            exact one_mem _
        refine ⟨hc _ w.val.property, ?_⟩
        rw [Units.inv_eq_val_inv, show gi⁻¹ = IdeleGroup.ofAdicCompletion (𝓞 F) F v
          (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom w⁻¹) by
            simp only [gi, map_inv]]
        exact hc _ (w⁻¹).val.property
      have hproj : Units.map (adeleProjection F S).toMonoidHom gi = 1 := by
        apply Units.ext
        refine Prod.ext rfl (funext fun v'' ↦ ?_)
        change RestrictedProduct.mulSingle (fun w : HeightOneSpectrum (𝓞 F) ↦
          w.adicCompletionIntegers F) v _ v''.val = 1
        exact RestrictedProduct.mulSingle_eq_of_ne _ _ (fun h ↦ hv (h ▸ v''.property))
      have h := hχ u ⟨_, hnorm⟩ 1 (by rw [hu]) (by rw [hu, hproj]; rfl)
      change ((ω (D (QuotientGroup.mk gi)) : Circle) : ℂ) = 1
      rw [show D (QuotientGroup.mk gi) = ⟨_, hnorm⟩ from hD1 ⟨_, hnorm⟩, ← h, map_one]
      rfl
    exact ⟨⟨c, hcu⟩, fun x ↦ by
      change ((ω (D x.val) : Circle) : ℂ) = ω x
      rw [hD1]⟩


variable (S) in
/-- Paper: Theorem 5.2.3.1, p. 233.
The descended S-local character is determined on the norm-one S-idele classes. -/
def sLocalNormOneCharacter (ω : PontryaginDual C₁)
    (hω : NormOneCharacterUnramifiedOutside (F := F) ω S) : PontryaginDual (J₁(S)) :=
  ((normOneCharacterUnramifiedOutside_iff (F := F) (S := S) ω).mp hω).exists.choose

/-- Paper: Theorem 5.2.3.1, p. 233.
The descended character agrees with the global character on representatives. -/
theorem sLocalNormOneCharacter_apply (ω : PontryaginDual C₁)
    (hω : NormOneCharacterUnramifiedOutside (F := F) ω S)
    (u : (integralAdelesOutside F S)ˣ) (x : C₁) (y : J₁(S))
    (hx : x.val = QuotientGroup.mk (integralIdeleInsertion F S u))
    (hy : y.val = QuotientGroup.mk (Units.map (adeleProjection F S).toMonoidHom
      (integralIdeleInsertion F S u))) :
    sLocalNormOneCharacter (F := F) S ω hω y = ω x :=
  ((normOneCharacterUnramifiedOutside_iff (F := F) (S := S) ω).mp hω).exists.choose_spec
    u x y hx hy

/-- Paper: Remark 5.2.3.3, p. 236.
The descended character agrees on norm-one classes with the S-idelic restriction
of any unramified extension from §3.1.2. -/
theorem sLocalNormOneCharacter_eq_sIdeleRestriction
    (ω : PontryaginDual C₁) (c : unramifiedOutside F S)
    (hc : ∀ x : C₁, c.val x.val = (ω x : ℂ)) (y : J₁(S)) :
    (sLocalNormOneCharacter (F := F) S ω ⟨c, hc⟩ y : ℂ) = sIdeleRestriction F S c y.val := by
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective y.val
  -- Insert ones off S to lift this representative to both norm-one groups.
  let a := sIdeleInsertion F S g
  have ha : a ∈ Set.range (integralIdeleInsertion F S) := by
    apply (mem_range_integralIdeleInsertion F S a).2
    intro v hv
    have hi : a⁻¹ = sIdeleInsertion F S g⁻¹ := (map_inv _ _).symm
    change a.val.2 v ∈ _ ∧ (a⁻¹).val.2 v ∈ _
    rw [hi, (sIdeleInsertion_apply F S g).2.2 v hv, (sIdeleInsertion_apply F S g⁻¹).2.2 v hv]
    exact ⟨one_mem _, one_mem _⟩
  obtain ⟨u, hu⟩ := ha
  have hp : Units.map (adeleProjection F S).toMonoidHom a = g :=
    Units.ext (Prod.ext (sIdeleInsertion_apply F S g).1
      (funext (sIdeleInsertion_apply F S g).2.1))
  have hn : ideleNorm F a = 1 := by
    rw [ideleNorm_sIdeleInsertion, ← sIdeleQuotientNorm_mk, hg]
    exact y.property
  let x : C₁ := ⟨QuotientGroup.mk a, hn⟩
  have hdesc := ((normOneCharacterUnramifiedOutside_iff (F := F) (S := S) ω).mp
    ⟨c, hc⟩).exists.choose_spec u x y (by rw [hu]) (by rw [hu, hp, hg])
  rw [← hg, sIdeleRestriction_mk]
  exact (congrArg (fun t : Circle ↦ (t : ℂ)) hdesc).trans (hc x).symm

/-- Paper: Theorem 5.2.3.1, p. 233.
Unramifiedness outside S implies unramifiedness outside every larger set of places. -/
theorem NormOneCharacterUnramifiedOutside.mono {ω : PontryaginDual C₁}
    (hω : NormOneCharacterUnramifiedOutside (F := F) ω S) (hST : S ⊆ T) :
    NormOneCharacterUnramifiedOutside (F := F) ω T := by
  obtain ⟨c, hc⟩ := hω
  exact ⟨⟨c.val, fun v hv ↦ c.property v fun h ↦ hv (hST h)⟩, hc⟩

variable {ω : PontryaginDual (ideleClassNorm F).ker}

local notation "ωₛ(" S ", " h ")" => sLocalNormOneCharacter (F := F) S ω h

/-- Extend a representative of a norm-one S-class by one. Its projections to S and T
represent classes on which the two descended characters agree. -/
private theorem sLocalHomogeneousThetaTransition_preserves_kernel_lift
    (hω : NormOneCharacterUnramifiedOutside (F := F) ω S) (hST : S ⊆ T) (a : J₁(S)) :
    ∃ (u : (integralAdelesOutside F S)ˣ) (b : J₁(T)),
      a.val = QuotientGroup.mk (Units.map (adeleProjection F S).toMonoidHom
        (integralIdeleInsertion F S u)) ∧
      b.val = QuotientGroup.mk (Units.map (adeleProjection F T).toMonoidHom
        (integralIdeleInsertion F S u)) ∧
      ωₛ(S, hω) a = ωₛ(T, hω.mono hST) b := by
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective a.val
  let j := sIdeleInsertion F S g
  let gT := Units.map (adeleProjection F T).toMonoidHom j
  obtain ⟨hinf, hin, hout⟩ := sIdeleInsertion_apply F S g
  have hS : Units.map (adeleProjection F S).toMonoidHom j = g :=
    Units.ext (Prod.ext hinf (funext hin))
  have hTj : sIdeleInsertion F T gT = j := by
    obtain ⟨hinf', hin', hout'⟩ := sIdeleInsertion_apply F T gT
    apply Units.ext
    refine Prod.ext hinf' ?_
    apply RestrictedProduct.ext
    intro v
    by_cases hv : v ∈ T
    · exact hin' ⟨v, hv⟩
    · exact (hout' v hv).trans (hout v (fun h ↦ hv (hST h))).symm
  have hn : ideleNorm F j = 1 := by
    rw [ideleNorm_sIdeleInsertion, ← sIdeleQuotientNorm_mk, hg]
    exact a.property
  let x : C₁ := ⟨QuotientGroup.mk j, hn⟩
  let b : J₁(T) := ⟨QuotientGroup.mk gT, (ideleNorm_sIdeleInsertion F T gT).symm.trans
    ((congrArg (ideleNorm F) hTj).trans hn)⟩
  have hj : j ∈ Set.range (integralIdeleInsertion F S) := by
    apply (mem_range_integralIdeleInsertion F S j).2
    intro v hv
    have hi : j⁻¹.val.2 v = 1 := by
      change ((sIdeleInsertion F S g)⁻¹).val.2 v = 1
      rw [← map_inv]
      exact (sIdeleInsertion_apply F S g⁻¹).2.2 v hv
    exact ⟨(hout v hv) ▸ (v.adicCompletionIntegers F).one_mem,
      hi ▸ (v.adicCompletionIntegers F).one_mem⟩
  obtain ⟨uT, huT⟩ := (integralIdeleInsertion_exhaustive F).1 hST hj
  obtain ⟨u, hu⟩ := hj
  have ha : a.val = QuotientGroup.mk (Units.map (adeleProjection F S).toMonoidHom j) := by
    rw [hS, hg]
  refine ⟨u, b, ?_, ?_, ?_⟩
  · simpa only [hu] using ha
  · simp only [hu]; rfl
  · exact (sLocalNormOneCharacter_apply ω hω u x a (by rw [hu]) (by simpa only [hu] using ha)).trans
      (sLocalNormOneCharacter_apply ω (hω.mono hST) uT x b (by rw [huT]) (by rw [huT])).symm

/-- Paper: (5.2.3.1), p. 233.
The stage map of test functions preserves the homogeneous theta kernels. -/
theorem sLocalHomogeneousThetaTransition_preserves_kernel
    (hω : NormOneCharacterUnramifiedOutside (F := F) ω S) (hST : S ⊆ T) :
    let hT := NormOneCharacterUnramifiedOutside.mono (F := F) (ω := ω) hω hST
    Kₛω(S, ωₛ(S, hω)) ≤ (Kₛω(T, ωₛ(T, hT))).comap
      (sAdeleSchwartzTransition F hST) := by
  intro hT
  let ρ (U : Finset (HeightOneSpectrum (𝓞 F))) :=
    (existsUnique_sLocalThetaAction (F := F) (S := U)).exists.choose
  have action (U : Finset (HeightOneSpectrum (𝓞 F))) (g : (SAdeleRing F U)ˣ) (k : ℬₛ(U))
      (a : SIdeleQuotient F U) (ha : a = QuotientGroup.mk g) :
      ρ U a (Submodule.Quotient.mk k) = Submodule.Quotient.mk (schwartzBruhatUnitTranslate g k) := by
    subst a
    unfold ρ
    with_reducible exact (existsUnique_sLocalThetaAction (F := F) (S := U)).exists.choose_spec.2 g k
  let rel (U : Finset (HeightOneSpectrum (𝓞 F))) (χ : PontryaginDual (J₁(U)))
      (p : J₁(U) × Θₛ(U)) := p.2 - star (χ p.1 : ℂ) • ρ U p.1.val p.2
  let D (U : Finset (HeightOneSpectrum (𝓞 F))) (χ : PontryaginDual (J₁(U))) :=
    (Submodule.span ℂ (Set.range (rel U χ))).topologicalClosure
  -- In the coinvariant description, the kernel is the preimage of the closed relation span.
  have hmem (U : Finset (HeightOneSpectrum (𝓞 F))) (χ : PontryaginDual (J₁(U))) (f : ℬₛ(U)) :
      f ∈ Kₛω(U, χ) ↔ (Kₛ(U)).mkQ f ∈ D U χ := by
    have h : ∃ e : SLocalHomogeneousThetaSpace F U χ ≃L[ℂ] (Θₛ(U) ⧸ D U χ),
        ∀ k : ℬₛ(U), e (Submodule.Quotient.mk k) = (D U χ).mkQ ((Kₛ(U)).mkQ k) := by
      unfold D rel ρ
      with_reducible exact sLocalHomogeneousThetaSpace_equiv_coinvariants (F := F) (S := U) χ
    refine h.elim fun e he ↦ ?_
    have he' := congrArg (fun z : Θₛ(U) ⧸ D U χ ↦ z = 0) (he f)
    have hz := ContinuousLinearEquiv.map_eq_zero_iff e (x := Submodule.Quotient.mk f)
    exact (Submodule.Quotient.mk_eq_zero (Kₛω(U, χ))).symm.trans
      (hz.symm.trans (he'.to_iff.trans (Submodule.Quotient.mk_eq_zero (D U χ))))
  let π := sLocalThetaTransition (F := F) hST
  have hmap : D S (ωₛ(S, hω)) ≤ (D T (ωₛ(T, hT))).comap π := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨⟨a, y⟩, rfl⟩
      refine (Submodule.Quotient.mk_surjective (Kₛ(S)) y).elim fun f hy ↦ ?_
      rw [← hy]
      have lift := sLocalHomogeneousThetaTransition_preserves_kernel_lift
        (F := F) (ω := ω) (S := S) (T := T) hω hST a
      refine lift.elim fun u hu ↦ hu.elim fun b hb ↦ ?_
      let j := integralIdeleInsertion F S u
      let gS := Units.map (adeleProjection F S).toMonoidHom j
      let gT := Units.map (adeleProjection F T).toMonoidHom j
      let fT := sAdeleSchwartzTransition F hST f
      have hρS := action S gS f a.val hb.1
      have hρT := action T gT fT b.val hb.2.1
      let yS : Θₛ(S) := Submodule.Quotient.mk f
      let yT : Θₛ(T) := Submodule.Quotient.mk fT
      -- The ordinary transition intertwines translations by this common representative.
      have heq : π (ρ S a.val yS) = ρ T b.val yT :=
        (congrArg π hρS).trans ((sLocalThetaTransition_equivariant hST u f).trans hρT.symm)
      have hπ : π yS = yT := by
        unfold π yS yT fT sLocalThetaTransition
        exact Submodule.mapQ_apply _ _ _ f
      have hχ := congrArg (fun z : Circle ↦ star (z : ℂ)) hb.2.2
      have hs := congrArg₂ (fun (c : ℂ) (z : Θₛ(T)) ↦ c • z) hχ heq
      have hrel := (map_sub π yS (star (ωₛ(S, hω) a : ℂ) • ρ S a.val yS)).trans
        (congrArg₂ (fun v w : Θₛ(T) ↦ v - w) hπ ((map_smul π _ _).trans hs))
      have he : π (rel S (ωₛ(S, hω)) (a, yS)) = rel T (ωₛ(T, hT)) (b, yT) := by
        with_reducible exact hrel
      have hm : rel T (ωₛ(T, hT)) (b, yT) ∈ D T (ωₛ(T, hT)) :=
        Submodule.le_topologicalClosure _ (Submodule.subset_span (Set.mem_range_self (b, yT)))
      have h := (congrArg (fun z ↦ z ∈ D T (ωₛ(T, hT))) he).mpr hm
      apply Submodule.mem_comap.mpr
      with_reducible exact h
    · have hc : IsClosed (D T (ωₛ(T, hT)) : Set Θₛ(T)) :=
        (Submodule.span ℂ (Set.range (rel T (ωₛ(T, hT))))).isClosed_topologicalClosure
      exact hc.preimage (sLocalThetaTransition_isClosedEmbedding (F := F) hST).continuous
  intro f hf
  exact (hmem T (ωₛ(T, hT)) _).mpr (hmap ((hmem S (ωₛ(S, hω)) f).mp hf))

/-- Paper: (5.2.3.1), p. 233.
The homogeneous theta transition is induced by adjoining integer indicators. -/
def sLocalHomogeneousThetaTransition (hω : NormOneCharacterUnramifiedOutside (F := F) ω S)
    (hST : S ⊆ T) : Θₛω(S, ωₛ(S, hω)) →ₗ[ℂ]
      Θₛω(T, ωₛ(T, NormOneCharacterUnramifiedOutside.mono (F := F) (ω := ω) hω hST)) :=
  let hT := NormOneCharacterUnramifiedOutside.mono (F := F) (ω := ω) hω hST
  (Kₛω(S, ωₛ(S, hω))).mapQ (Kₛω(T, ωₛ(T, hT))) (sAdeleSchwartzTransition F hST)
    (sLocalHomogeneousThetaTransition_preserves_kernel (F := F) (ω := ω) hω hST)

/-- Paper: (5.2.3.1), p. 233.
The transition is the unique linear map induced on homogeneous theta classes
by the test function transition. -/
theorem sLocalHomogeneousThetaTransition_spec
    (hω : NormOneCharacterUnramifiedOutside (F := F) ω S) (hST : S ⊆ T) :
    let hT := NormOneCharacterUnramifiedOutside.mono (F := F) (ω := ω) hω hST
    let descends := fun π : Θₛω(S, ωₛ(S, hω)) →ₗ[ℂ] Θₛω(T, ωₛ(T, hT)) ↦
      π.comp (Kₛω(S, ωₛ(S, hω))).mkQ =
        (Kₛω(T, ωₛ(T, hT))).mkQ.comp (sAdeleSchwartzTransition F hST)
    descends (sLocalHomogeneousThetaTransition (F := F) (ω := ω) hω hST) ∧
      ∀ π, descends π → π = sLocalHomogeneousThetaTransition (F := F) (ω := ω) hω hST := by
  intro hT descends
  have h : descends (sLocalHomogeneousThetaTransition (F := F) (ω := ω) hω hST) :=
    Submodule.mapQ_mkQ _ _ _
      (h := sLocalHomogeneousThetaTransition_preserves_kernel (F := F) (ω := ω) hω hST)
  exact ⟨h, fun π hπ ↦ Submodule.linearMap_qext _ (Eq.trans hπ (Eq.symm h))⟩

section
open Set TopologicalSpace

/-- A neighborhood of the kernel in the ambient group which contains no subgroup
larger than the kernel (in fact every subgroup inside it lies in the kernel). -/
private theorem bruhat_kernel_open_tube {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] (a : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation a.quotient) :
    ∃ V : Set G, IsOpen V ∧ ((OrderDual.ofDual a.val.2 : Subgroup G) : Set G) ⊆ V ∧
      ∀ L : Subgroup G, (L : Set G) ⊆ V → L ≤ OrderDual.ofDual a.val.2 := by
  let : LocallyCompactSpace a.val.1 := a.property.1.isOpenEmbedding_subtypeVal.locallyCompactSpace
  let : T1Space a.quotient := QuotientGroup.t1Space_iff.mpr
    (a.property.2.2.1.1.preimage continuous_subtype_val)
  obtain ⟨W, hW, hPow⟩ := exists_nhds_one_of_isLocallyEuclidean
    (locallyEuclidean_of_elementaryPresentation e)
  let q : a.val.1 →* a.quotient := QuotientGroup.mk' _
  refine ⟨Subtype.val '' (q ⁻¹' interior W), a.property.1.isOpenEmbedding_subtypeVal.isOpenMap _
    (isOpen_interior.preimage (QuotientGroup.continuous_mk : Continuous q)), ?_, ?_⟩
  · intro x hx
    let y : a.val.1 := ⟨x, a.property.2.2.2 hx⟩
    refine ⟨y, ?_, rfl⟩
    change q y ∈ interior W
    rw [show q y = 1 from (a.quotient_mk_eq_one y).mpr hx]
    exact mem_interior_iff_mem_nhds.mpr hW
  · intro L hL x hx
    obtain ⟨y, _, rfl⟩ := hL hx
    apply (a.quotient_mk_eq_one y).mp
    change q y = 1
    apply hPow
    intro k
    rw [← map_pow]
    obtain ⟨z, hz, he⟩ := hL (L.pow_mem hx k)
    exact (Subtype.ext he : z = y ^ k) ▸ interior_subset hz

/-- A compact set inside an open set is still mapped into that open set by
sufficiently small continuous perturbations of the identity. -/
private theorem bruhat_eventually_mapsTo {U G : Type*} [TopologicalSpace U] [TopologicalSpace G]
    (f : U → G → G) (hf : Continuous (Function.uncurry f)) (u : U) (hu : ∀ x, f u x = x)
    {C V : Set G} (hC : IsCompact C) (hV : IsOpen V) (hCV : C ⊆ V) :
    ∀ᶠ v in 𝓝 u, MapsTo (f v) C V := by
  let F (v : U) : C(G, G) := ⟨f v, continuous_curry v hf⟩
  have hF : Continuous F := ContinuousMap.continuous_of_continuous_uncurry F hf
  exact hF.continuousAt.preimage_mem_nhds (ContinuousMap.eventually_mapsTo hC hV
    (f := F u) (fun x hx ↦ by change f u x ∈ V; rw [hu]; exact hCV hx))

/-- Units close to one preserve each Bruhat structural subgroup, jointly with their inverses. -/
private theorem exists_open_unit_stabilizer {R : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [LocallyCompactSpace R] [T2Space R]
    (a : BruhatStructuralPair (Multiplicative R)) (e : ElementaryLCAPresentation a.quotient) :
    ∃ H : OpenSubgroup Rˣ, ∀ u : H,
      (∀ x ∈ a.val.1, Multiplicative.ofAdd (u.val.val * x.toAdd) ∈ a.val.1) ∧
      (∀ x ∈ OrderDual.ofDual a.val.2,
        Multiplicative.ofAdd (u.val.val * x.toAdd) ∈ OrderDual.ofDual a.val.2) := by
  let G := Multiplicative R
  let : LocallyCompactSpace (Multiplicative R) := ‹LocallyCompactSpace R›
  let : T2Space (Multiplicative R) := ‹T2Space R›
  obtain ⟨D, _, hDc, hDgen⟩ := a.property.2.1
  let f (u : Rˣ) : G →* G := (AddMonoidHom.mulLeft u.val).toMultiplicative
  have hf : Continuous (fun p : Rˣ × G ↦ f p.1 p.2) :=
    continuous_ofAdd.comp ((Units.continuous_val.comp continuous_fst).mul
      (continuous_toAdd.comp continuous_snd))
  have h1 (x : G) : f 1 x = x := by change Multiplicative.ofAdd (1 * x.toAdd) = x; simp
  have hm (u v : Rˣ) (x : G) : f (u * v) x = f u (f v x) := by
    change Multiplicative.ofAdd ((u.val * v.val) * x.toAdd) = _
    rw [mul_assoc]; rfl
  let K := OrderDual.ofDual a.val.2
  let P (u : Rˣ) := MapsTo (f u) (a.val.1 : Set G) a.val.1 ∧ MapsTo (f u) (K : Set G) K
  have hp : ∀ᶠ u in 𝓝 (1 : Rˣ), P u := by
    obtain ⟨V, hV, hKV, hsmall⟩ := bruhat_kernel_open_tube a e
    filter_upwards [bruhat_eventually_mapsTo (fun u x ↦ f u x) hf 1 h1 (hDc.image continuous_subtype_val)
      a.property.1 (image_subset_iff.mpr fun x _ ↦ x.property),
      bruhat_eventually_mapsTo (fun u x ↦ f u x) hf 1 h1 (compact_bruhat_kernel a) hV hKV] with u hD hK
    constructor
    · let J := a.val.1.comap ((f u).comp a.val.1.subtype)
      have hJD : D ⊆ J := fun d hd ↦ hD (mem_image_of_mem _ hd)
      have hJ : ⊤ ≤ J := hDgen ▸ J.closure_le.mpr hJD
      exact fun x hx ↦ hJ (Subgroup.mem_top (x := (⟨x, hx⟩ : a.val.1)))
    · have hL := hsmall (K.map (f u)) (by rintro _ ⟨x, hx, rfl⟩; exact hK hx)
      exact fun x hx ↦ hL (Subgroup.mem_map_of_mem _ hx)
  have pid : P 1 := by
    constructor <;> intro x hx <;> rw [h1] <;> exact hx
  have pmul {u v : Rˣ} (hu : P u) (hv : P v) : P (u * v) :=
    ⟨fun x hx ↦ hm u v x ▸ hu.1 (hv.1 hx), fun x hx ↦ hm u v x ▸ hu.2 (hv.2 hx)⟩
  let H : Subgroup Rˣ := {
    carrier := {u | P u ∧ P u⁻¹}
    one_mem' := ⟨pid, by simpa using pid⟩
    mul_mem' := fun ha hb ↦ ⟨pmul ha.1 hb.1, by simpa using pmul hb.2 ha.2⟩
    inv_mem' := fun ha ↦ ⟨ha.2, by simpa using ha.1⟩ }
  have hi : Tendsto Inv.inv (𝓝 (1 : Rˣ)) (𝓝 1) := continuous_inv.tendsto' _ _ inv_one
  have ho : IsOpen (H : Set Rˣ) := H.isOpen_of_mem_nhds (g := 1) (hp.and (hi.eventually hp))
  exact ⟨⟨H, ho⟩, fun u ↦ ⟨fun _ hx ↦ u.property.1.1 hx, fun _ hx ↦ u.property.1.2 hx⟩⟩

/-- A continuous group automorphism preserving a structural pair pulls realized
stage functions back by a continuous linear equivalence of the very same stage. -/
private theorem fixedStage_pullback {G : Type*} [CommGroup G] [TopologicalSpace G]
    (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient)
    (d : G ≃ₜ* G) (hO : ∀ x, d x ∈ a.val.1 ↔ x ∈ a.val.1)
    (hK : ∀ x, d x ∈ OrderDual.ofDual a.val.2 ↔ x ∈ OrderDual.ofDual a.val.2) :
    ∃ L : SchwartzBruhatStage e ≃L[ℂ] SchwartzBruhatStage e,
      ∀ f x, schwartzBruhatStageRealization a e (L f) x =
        schwartzBruhatStageRealization a e f (d x) := by
  classical
  let b : a.val.1 ≃ₜ* a.val.1 :=
    { toFun := fun x ↦ ⟨d x, (hO x).mpr x.property⟩
      invFun := fun x ↦ ⟨d.symm x, (hO _).mp (by simpa only [d.apply_symm_apply] using x.property)⟩
      left_inv := fun x ↦ Subtype.ext (d.symm_apply_apply x)
      right_inv := fun x ↦ Subtype.ext (d.apply_symm_apply x)
      map_mul' := fun x y ↦ Subtype.ext (map_mul d x.val y.val)
      continuous_toFun := (d.continuous.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (d.symm.continuous.comp continuous_subtype_val).subtype_mk _ }
  let K := (OrderDual.ofDual a.val.2).comap a.val.1.subtype
  have hb : K.map b.toMulEquiv = K := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hK y).mpr hy
    · intro hx
      refine ⟨b.symm x, ?_, b.apply_symm_apply x⟩
      apply (hK (d.symm x.val)).mp
      rw [d.apply_symm_apply]
      exact hx
  let q : a.quotient ≃ₜ* a.quotient :=
    { QuotientGroup.congr K K b.toMulEquiv hb with
      continuous_toFun := (QuotientGroup.isQuotientMap_mk K).continuous_iff.mpr
        (QuotientGroup.continuous_mk.comp b.continuous)
      continuous_invFun := (QuotientGroup.isQuotientMap_mk K).continuous_iff.mpr
        (QuotientGroup.continuous_mk.comp b.symm.continuous) }
  let c := (e.equiv.symm.trans q).trans e.equiv
  let E := ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor
  let ψ : E ≃ₜ+ E :=
    { MulEquiv.toAdditive c.toMulEquiv with
      continuous_toFun := c.continuous_toFun
      continuous_invFun := c.continuous_invFun }
  obtain ⟨L, hL⟩ := elementarySchwartz_pullback ψ
  refine ⟨L, fun f x ↦ ?_⟩
  have hin (s : SchwartzBruhatStage e) (t : a.val.1) :
      schwartzBruhatStageRealization a e s t.val = s (e.equiv (QuotientGroup.mk t)).toAdd := by
    rw [schwartzBruhatStageRealization_apply, dite_eq_left t.property]
  have hout (s : SchwartzBruhatStage e) {t : G} (ht : t ∉ a.val.1) :
      schwartzBruhatStageRealization a e s t = 0 := by
    rw [schwartzBruhatStageRealization_apply, dite_eq_right ht]
  by_cases hx : x ∈ a.val.1
  · let t : a.val.1 := ⟨x, hx⟩
    refine (hin (L f) t).trans ((hL f _).trans (Eq.trans ?_ (hin f (b t)).symm))
    change f (e.equiv (q (e.equiv.symm (e.equiv (QuotientGroup.mk t))))).toAdd = _
    rw [e.equiv.symm_apply_apply]
    rfl
  · exact (hout (L f) hx).trans (hout f (mt (hO x).mp hx)).symm

/-- Every elementary coordinate is realized by evaluation at a representative. -/
private theorem fixedStage_eval_representative {G : Type*} [CommGroup G] [TopologicalSpace G]
    (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient)
    (y : ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor) :
    ∃ x : a.val.1, ∀ f : SchwartzBruhatStage e,
      schwartzBruhatStageRealization a e f x.val = f y := by
  classical
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (e.equiv.symm (Multiplicative.ofAdd y))
  exact ⟨x, fun f ↦ by rw [schwartzBruhatStageRealization_apply, dite_eq_left x.property,
    hx, e.equiv.apply_symm_apply]; rfl⟩

/-- Point evaluations on the elementary model are continuous for the stage topology. -/
private theorem fixedStage_continuous_eval {A : Type*} [CommGroup A] [TopologicalSpace A]
    (e : ElementaryLCAPresentation A)
    (y : ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor) :
    Continuous (fun f : SchwartzBruhatStage e ↦ f y) := by
  let L := (LinearMap.proj y).comp
    (elementarySchwartzSubmodule e.realDim e.torusDim e.latticeRank e.finiteFactor).subtype
  refine (norm_withSeminorms ℂ ℂ).continuous_of_continuous_comp (E := SchwartzBruhatStage e) L
    fun _ ↦ ?_
  apply Seminorm.continuous_of_le (elementarySchwartz_withSeminorms.continuous_seminorm (0, 0, 0, 0))
  intro f
  change (‖f y‖₊ : ENNReal).toReal ≤ (elementarySchwartzBound f.val (0, 0, 0, 0)).toReal
  apply ENNReal.toReal_mono (f.property.2 _).ne
  rw [elementarySchwartzBound_zero]
  exact le_iSup (fun w ↦ (‖f w‖₊ : ENNReal)) y

/-- Left multiplication by a unit is a topological automorphism of the additive group. -/
private theorem fixedStage_unitEquiv {R : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] (u : Rˣ) :
    ∃ d : Multiplicative R ≃ₜ* Multiplicative R, ∀ x : Multiplicative R,
      d x = Multiplicative.ofAdd (u.val * x.toAdd) := by
  let d : Multiplicative R ≃ₜ* Multiplicative R :=
    { toFun := fun x ↦ Multiplicative.ofAdd (u.val * x.toAdd)
      invFun := fun x ↦ Multiplicative.ofAdd (u.inv * x.toAdd)
      left_inv := fun x ↦ congrArg Multiplicative.ofAdd (by
        change u.inv * (u.val * x.toAdd) = x.toAdd
        rw [← mul_assoc, u.inv_val, one_mul])
      right_inv := fun x ↦ congrArg Multiplicative.ofAdd (by
        change u.val * (u.inv * x.toAdd) = x.toAdd
        rw [← mul_assoc, u.val_inv, one_mul])
      map_mul' := fun x y ↦ congrArg Multiplicative.ofAdd (mul_add _ x.toAdd y.toAdd)
      continuous_toFun := continuous_ofAdd.comp (continuous_const.mul continuous_toAdd)
      continuous_invFun := continuous_ofAdd.comp (continuous_const.mul continuous_toAdd) }
  exact ⟨d, fun _ ↦ rfl⟩

/-- Inverse dilation via the unit induces an equivalence by stage pullback. -/
private theorem fixedStage_unitPullback {R : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] (a : BruhatStructuralPair (Multiplicative R))
    (e : ElementaryLCAPresentation a.quotient) (H : Subgroup Rˣ)
    (hO : ∀ (u : H) (x : R), Multiplicative.ofAdd x ∈ a.val.1 →
      Multiplicative.ofAdd (u.val.val * x) ∈ a.val.1)
    (hK : ∀ (u : H) (x : R), Multiplicative.ofAdd x ∈ OrderDual.ofDual a.val.2 →
      Multiplicative.ofAdd (u.val.val * x) ∈ OrderDual.ofDual a.val.2) (u : H) :
    ∃ T : SchwartzBruhatStage e →L[ℂ] SchwartzBruhatStage e,
      ∀ (f : SchwartzBruhatStage e) (x : R),
        schwartzBruhatStageRealization a e (T f) (Multiplicative.ofAdd x) =
          schwartzBruhatStageRealization a e f (Multiplicative.ofAdd (u.val.inv * x)) := by
  classical
  choose d hd using fun t : H ↦ fixedStage_unitEquiv t.val
  have iff_mem (U : Subgroup (Multiplicative R))
      (hU : ∀ (u : H) (x : R), Multiplicative.ofAdd x ∈ U → Multiplicative.ofAdd (u.val.val * x) ∈ U)
      (u : H) (x : Multiplicative R) : d u x ∈ U ↔ x ∈ U := by
    rw [hd]
    refine ⟨fun hx ↦ ?_, hU u x.toAdd⟩
    have h := hU u⁻¹ _ hx
    change Multiplicative.ofAdd (u.val.inv * (u.val.val * x.toAdd)) ∈ U at h
    rwa [← mul_assoc, u.val.inv_val, one_mul] at h
  have ho := iff_mem a.val.1 hO u⁻¹
  have hk := iff_mem (OrderDual.ofDual a.val.2) hK u⁻¹
  have h := fixedStage_pullback (G := Multiplicative R) a e (d u⁻¹) ho hk
  obtain ⟨L, hL⟩ := h
  exact ⟨L.toContinuousLinearMap, fun f x ↦ (hL f (Multiplicative.ofAdd x)).trans
    (congrArg (schwartzBruhatStageRealization a e f) (hd u⁻¹ (Multiplicative.ofAdd x)))⟩

/-- Coordinates in a presentation detect equality after realization. -/
private theorem fixedStage_realization_injective {G : Type*} [CommGroup G] [TopologicalSpace G]
    (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient) :
    Injective (schwartzBruhatStageRealization a e) := by
  intro f k hfk
  apply Subtype.ext
  funext y
  obtain ⟨x, hx⟩ := fixedStage_eval_representative a e y
  exact (hx f).symm.trans ((congrFun hfk x.val).trans (hx k))

/-- Scalar orbit continuity follows directly from continuity of the projected coordinate in the quotient. -/
private theorem fixedStage_unitOrbit_continuous_eval {R : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] (a : BruhatStructuralPair (Multiplicative R))
    (e : ElementaryLCAPresentation a.quotient) (H : Subgroup Rˣ)
    (hO : ∀ (u : H) (x : R), Multiplicative.ofAdd x ∈ a.val.1 →
      Multiplicative.ofAdd (u.val.val * x) ∈ a.val.1)
    (T : H → (SchwartzBruhatStage e →L[ℂ] SchwartzBruhatStage e))
    (heval : ∀ (u : H) (f : SchwartzBruhatStage e) (x : R),
        schwartzBruhatStageRealization a e (T u f) (Multiplicative.ofAdd x) =
          schwartzBruhatStageRealization a e f (Multiplicative.ofAdd (u.val.inv * x))) :
    ∀ (f : SchwartzBruhatStage e) y, Continuous (fun u : H ↦ T u f y) := by
  classical
  intro f y
  obtain ⟨x, hx⟩ := fixedStage_eval_representative a e y
  let p (u : H) : a.val.1 := ⟨Multiplicative.ofAdd (u.val.inv * x.val.toAdd), hO u⁻¹ _ x.property⟩
  have hp : Continuous p := (continuous_ofAdd.comp
    ((Units.continuous_coe_inv.comp continuous_subtype_val).mul_const x.val.toAdd)).subtype_mk _
  have hc := (elementarySchwartz_continuous f).comp (continuous_toAdd.comp
    (e.equiv.continuous.comp (QuotientGroup.continuous_mk.comp hp)))
  refine hc.congr fun u ↦ ?_
  refine Eq.trans ?_ ((heval u f x.val.toAdd).symm.trans (hx (T u f)))
  exact (by rw [schwartzBruhatStageRealization_apply, dite_eq_left (p u).property] :
    f (e.equiv (QuotientGroup.mk (p u))).toAdd = schwartzBruhatStageRealization a e f (p u).val)

/-- A subgroup of units preserving a structural pair acts on its elementary
Schwartz stage. The action realizes inverse-dilation, and each scalar coordinate
of each orbit varies continuously with the unit. -/
private theorem fixedStage_exists_unitAction {R : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] (a : BruhatStructuralPair (Multiplicative R))
    (e : ElementaryLCAPresentation a.quotient) (H : OpenSubgroup Rˣ)
    (hs : ∀ u : H,
      (∀ x ∈ a.val.1, Multiplicative.ofAdd (u.val.val * x.toAdd) ∈ a.val.1) ∧
      (∀ x ∈ OrderDual.ofDual a.val.2,
        Multiplicative.ofAdd (u.val.val * x.toAdd) ∈ OrderDual.ofDual a.val.2)) :
    ∃ ρ : H →* (SchwartzBruhatStage e →L[ℂ] SchwartzBruhatStage e),
      (∀ (u : H) (f : SchwartzBruhatStage e) (x : R),
        schwartzBruhatStageRealization a e (ρ u f) (Multiplicative.ofAdd x) =
          schwartzBruhatStageRealization a e f (Multiplicative.ofAdd (u.val.inv * x))) ∧
      ∀ (f : SchwartzBruhatStage e) y, Continuous (fun u : H ↦ ρ u f y) := by
  classical
  have hO (u : H) (x : R) := (hs u).1 (Multiplicative.ofAdd x)
  have hK (u : H) (x : R) := (hs u).2 (Multiplicative.ofAdd x)
  choose T heval using fixedStage_unitPullback a e H.toSubgroup hO hK
  have hinj := fixedStage_realization_injective a e
  let ρ : H →* (SchwartzBruhatStage e →L[ℂ] SchwartzBruhatStage e) :=
    { toFun := T
      map_one' := by
        apply ContinuousLinearMap.ext
        intro f
        apply hinj
        funext x
        exact (heval 1 f x.toAdd).trans (congrArg (fun y ↦
          schwartzBruhatStageRealization a e f (Multiplicative.ofAdd y)) (one_mul x.toAdd))
      map_mul' := by
        intro u v
        apply ContinuousLinearMap.ext
        intro f
        apply hinj
        funext x
        change schwartzBruhatStageRealization a e (T (u * v) f) (Multiplicative.ofAdd x.toAdd) =
          schwartzBruhatStageRealization a e (T u (T v f)) (Multiplicative.ofAdd x.toAdd)
        exact (heval (u*v) f x.toAdd).trans ((congrArg (fun y ↦
          schwartzBruhatStageRealization a e f (Multiplicative.ofAdd y))
          (mul_assoc v.val.inv u.val.inv x.toAdd)).trans ((heval v f (u.val.inv * x.toAdd)).symm.trans
          (heval u (T v f) x.toAdd).symm)) }
  exact ⟨ρ, heval, fixedStage_unitOrbit_continuous_eval a e H.toSubgroup hO T heval⟩

/-- Every elementary Schwartz–Bruhat stage admits a compatible complete separable metric. -/
private theorem schwartzBruhatStage_polishSpace {A : Type*} [CommGroup A] [TopologicalSpace A]
    (e : ElementaryLCAPresentation A) :
    PolishSpace (SchwartzBruhatStage e) := by
  let E := SchwartzBruhatStage e
  have hF : IsFrechetTVS E := elementarySchwartz_isFrechet
  have : MetrizableSpace E := hF.choose_spec.2.1
  have : CompleteSpace E := by
    have h := hF.choose_spec.2.2
    rwa [IsUniformAddGroup.rightUniformSpace_eq] at h
  have := IsUniformAddGroup.uniformity_countably_generated (α := E)
  have : SeparableSpace E := separableSpace_of_withSeminorms_of_compact_bounded
    elementarySchwartz_withSeminorms elementarySchwartz_isCompact_of_isClosed_isVonNBounded
  exact inferInstanceAs (PolishSpace E)

private theorem unitTranslate_barrelled (G : Type*) [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] : BarrelledSpace ℂ (SchwartzBruhat G) := by
  constructor
  intro p hp
  apply schwartzBruhat_continuous_seminorm p
  intro a e
  let : ContinuousSMul ℂ (SchwartzBruhatStage e) := elementarySchwartz_withSeminorms.continuousSMul
  let : BarrelledSpace ℂ (SchwartzBruhatStage e) := isFrechetTVS_barrelled elementarySchwartz_isFrechet
  exact (p.comp (schwartzBruhatStageInclusion a e)).continuous_of_lowerSemicontinuous
    (hp.comp (continuous_schwartzBruhatStageInclusion a e))

/-- Vectors with continuous orbit form a submodule. It suffices to check the stage
inclusions, and on each stage one may restrict to an open subgroup of units. -/
private theorem unitTranslate_orbit_of_stages {R : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [LocallyCompactSpace R] [T2Space R]
    (hs : ∀ (a : BruhatStructuralPair (Multiplicative R))
      (e : ElementaryLCAPresentation a.quotient) (s : SchwartzBruhatStage e),
      ∃ H : OpenSubgroup Rˣ, Continuous fun u : H ↦ schwartzBruhatUnitTranslate u.val
        (schwartzBruhatStageInclusion a e s)) :
    ∀ f : SchwartzBruhat (Multiplicative R), Continuous fun u ↦ schwartzBruhatUnitTranslate u f := by
  let B := SchwartzBruhat (Multiplicative R)
  let T := unitTranslateEnd (R := R)
  have hc (u : Rˣ) : Continuous (T u) := continuous_unitTranslate u
  let P : Submodule ℂ B :=
    { carrier := {f | Continuous fun u ↦ T u f}
      zero_mem' := continuous_const.congr fun u ↦ ((T u).map_zero).symm
      add_mem' := fun hf hg ↦ (Continuous.add hf hg).congr fun u ↦ ((T u).map_add _ _).symm
      smul_mem' := fun c f hf ↦ (hf.const_smul c).congr fun u ↦ ((T u).map_smul c f).symm }
  have hall : schwartzBruhatSubmodule (Multiplicative R) ≤
      P.map (schwartzBruhatSubmodule (Multiplicative R)).subtype := by
    apply iSup_le
    intro a
    apply iSup_le
    intro e
    rintro _ ⟨s, rfl⟩
    let f : B := schwartzBruhatStageInclusion a e s
    refine ⟨f, ?_, rfl⟩
    obtain ⟨H, hH⟩ := hs a e s
    have h1 : ContinuousAt (fun u : Rˣ ↦ T u f) 1 :=
      (H.isOpen.isOpenEmbedding_subtypeVal.continuousAt_iff (x := (1 : H))).mp hH.continuousAt
    apply continuous_iff_continuousAt.mpr
    intro g
    have h := h1.comp_of_eq ((continuous_const.mul continuous_id).continuousAt (x := g))
      (inv_mul_cancel g)
    apply ((hc g).continuousAt.comp h).congr
    filter_upwards with x
    change T g (T (g⁻¹ * x) f) = T x f
    exact (DFunLike.congr_fun (T.map_mul g (g⁻¹ * x)).symm f).trans
      (congrArg (fun y ↦ T y f) (mul_inv_cancel_left g x))
  intro f
  obtain ⟨v,hv,h⟩ := Submodule.mem_map.mp (hall (x := f.val) f.property)
  exact (Subtype.ext h : v = f) ▸ hv

private theorem unitTranslate_joint_of_stage_orbits {R : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [LocallyCompactSpace R] [T2Space R] [WeaklyLocallyCompactSpace Rˣ]
    (hs : ∀ (a : BruhatStructuralPair (Multiplicative R))
      (e : ElementaryLCAPresentation a.quotient) (s : SchwartzBruhatStage e),
      ∃ H : OpenSubgroup Rˣ, Continuous fun u : H ↦ schwartzBruhatUnitTranslate u.val
        (schwartzBruhatStageInclusion a e s)) :
    Continuous fun p : Rˣ × SchwartzBruhat (Multiplicative R) ↦
      schwartzBruhatUnitTranslate p.1 p.2 := by
  let B := SchwartzBruhat (Multiplicative R)
  let T := unitTranslateEnd (R := R)
  have hc (u : Rˣ) : Continuous (T u) := continuous_unitTranslate u
  let : T2Space (Multiplicative R) := ‹T2Space R›
  let : LocallyCompactSpace (Multiplicative R) := ‹LocallyCompactSpace R›
  let : BarrelledSpace ℂ B := unitTranslate_barrelled (Multiplicative R)
  let : PolynormableSpace ℂ B := (withGeneratingSeminorms_spec _ _).toPolynormableSpace
  let : UniformSpace B := IsTopologicalAddGroup.rightUniformSpace B
  let : IsUniformAddGroup B := isUniformAddGroup_of_addCommGroup
  exact continuous_family_of_orbits (fun u ↦ (⟨T u, hc u⟩ : B →L[ℂ] B))
    (unitTranslate_orbit_of_stages hs)

private theorem continuous_elementary_unitOrbit {A H : Type*} [CommGroup A] [TopologicalSpace A]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [SequentialSpace H] [BaireSpace H]
    (e : ElementaryLCAPresentation A) (ρ : H →* (SchwartzBruhatStage e →L[ℂ] SchwartzBruhatStage e))
    (s : SchwartzBruhatStage e) (he : ∀ y, Continuous (fun u : H ↦ ρ u s y)) :
    Continuous (fun u : H ↦ ρ u s) := by
  let : PolishSpace (SchwartzBruhatStage e) := schwartzBruhatStage_polishSpace e
  exact continuous_equivariant_of_continuous_injective_comp (fun u : H ↦ ρ u s)
    (fun b y ↦ ρ b y) (fun b ↦ (ρ b).continuous)
    (fun b h ↦ DFunLike.congr_fun (ρ.map_mul b h).symm s)
    (fun f : SchwartzBruhatStage e ↦ f.val) (continuous_pi (fixedStage_continuous_eval e))
    Subtype.val_injective (continuous_pi he)

/-- On the open stabilizer of a stage the orbit has continuous scalar evaluations.
Automatic continuity upgrades this to continuity in the Polish stage topology;
barrelledness then gives joint continuity of unit translation. -/
private theorem unitTranslate_joint {R : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [LocallyCompactSpace R] [T2Space R] [FirstCountableTopology Rˣ]
    [LocallyCompactSpace Rˣ] : Continuous fun p : Rˣ × SchwartzBruhat (Multiplicative R) ↦
      schwartzBruhatUnitTranslate p.1 p.2 := by
  apply unitTranslate_joint_of_stage_orbits
  intro a e s
  obtain ⟨H, hs⟩ := exists_open_unit_stabilizer a e
  have A := fixedStage_exists_unitAction (R := R) a e H hs
  let ρ := A.choose
  have hr := A.choose_spec.1
  have he := A.choose_spec.2
  let : LocallyCompactSpace H := H.isOpen.isOpenEmbedding_subtypeVal.locallyCompactSpace
  let : IsTopologicalGroup H := inferInstanceAs (IsTopologicalGroup H.toSubgroup)
  have hρ := continuous_elementary_unitOrbit e ρ s (he s)
  refine ⟨H, ((continuous_schwartzBruhatStageInclusion a e).comp hρ).congr fun u ↦ ?_⟩
  exact Subtype.ext (funext fun x ↦ hr u s x.toAdd)

/-- Unit translation on S-adelic Schwartz–Bruhat tests is jointly continuous. -/
theorem continuous_sAdeleSchwartz_unitTranslate :
    Continuous fun p : (SAdeleRing F S)ˣ × ℬₛ(S) ↦ schwartzBruhatUnitTranslate p.1 p.2 := by
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let : LocallyCompactSpace (SAdeleRing F S) :=
    inferInstanceAs (LocallyCompactSpace (InfiniteAdeleRing F × ((v : S) → v.val.adicCompletion F)))
  let : T2Space (SAdeleRing F S) := inferInstanceAs (T2Space (((w : InfinitePlace F) → w.Completion) ×
    ((v : S) → v.val.adicCompletion F)))
  let : FirstCountableTopology (SAdeleRing F S) := inferInstanceAs (FirstCountableTopology
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : FirstCountableTopology (SAdeleRing F S)ˣ := (sIdeleGroup_description F S).1.firstCountableTopology
  let : LocallyCompactSpace (SAdeleRing F S)ˣ := (sIdeleGroup_description F S).2.2.1
  exact unitTranslate_joint

end

/-- Unit translation of an S-adelic test translates its theta function on quotient classes. -/
theorem sLocalTheta_translate_onClasses (g : (SAdeleRing F S)ˣ)
    (f : SchwartzBruhat (Multiplicative (SAdeleRing F S))) (x : SIdeleQuotient F S) :
    sLocalAdelicThetaOnClasses F S (schwartzBruhatUnitTranslate g f) x =
      sLocalAdelicThetaOnClasses F S f ((QuotientGroup.mk g)⁻¹ * x) := by
  induction x using QuotientGroup.induction_on with | H x =>
    have hx : ((QuotientGroup.mk g : SIdeleQuotient F S)⁻¹ * QuotientGroup.mk x) =
        QuotientGroup.mk (g⁻¹ * x) := by
      change (QuotientGroup.mk' _) g ⁻¹ * (QuotientGroup.mk' _) x = _
      exact (map_mul (QuotientGroup.mk' _) _ _).symm
    rw [hx]
    exact (sLocalAdelicThetaOnClasses_mk F S _ _).trans
      ((localTheta_translate_apply g x f).trans (sLocalAdelicThetaOnClasses_mk F S f _).symm)

private theorem sLocalHomogeneousTheta_translate_apply (χ : PontryaginDual (MonoidHom.ker (sIdeleQuotientNorm F S)))
    (g : (SAdeleRing F S)ˣ) (f : SchwartzBruhat (Multiplicative (SAdeleRing F S)))
    (x : SIdeleQuotient F S) :
    sLocalHomogeneousAdelicThetaLinearMap F S χ (schwartzBruhatUnitTranslate g f) x =
      sLocalHomogeneousAdelicThetaLinearMap F S χ f ((QuotientGroup.mk g)⁻¹ * x) := by
  calc
    _ = ∫ h : (sIdeleQuotientNorm F S).ker,
        sLocalAdelicThetaOnClasses F S (schwartzBruhatUnitTranslate g f) (x * h.val) * (χ h : ℂ)
        ∂sLocalNormOneQuotientMeasure F S := sLocalHomogeneousAdelicThetaLinearMap_apply χ _ _
    _ = ∫ h : (sIdeleQuotientNorm F S).ker,
        sLocalAdelicThetaOnClasses F S f (((QuotientGroup.mk g)⁻¹ * x) * h.val) * (χ h : ℂ)
        ∂sLocalNormOneQuotientMeasure F S := ?_
    _ = _ := (sLocalHomogeneousAdelicThetaLinearMap_apply χ _ _).symm
  apply integral_congr_ae
  filter_upwards with h
  exact congrArg (fun z : ℂ ↦ z * (χ h : ℂ))
    ((sLocalTheta_translate_onClasses g f (x * h.val)).trans (congrArg (sLocalAdelicThetaOnClasses F S f)
      (show ((QuotientGroup.mk g : SIdeleQuotient F S)⁻¹ * (x * h.val)) =
        ((QuotientGroup.mk g : SIdeleQuotient F S)⁻¹ * x) * h.val from
          (mul_assoc ((QuotientGroup.mk g : SIdeleQuotient F S)⁻¹) x h.val).symm)))

/-- Paper: Theorem 5.2.3.1(1), p. 233.
The S-idele quotient acts jointly continuously on each homogeneous theta quotient.
Translation by a representative induces the action on its test-function class. -/
theorem existsUnique_sLocalHomogeneousThetaAction (χ : PontryaginDual (J₁(S))) :
    ∃! ρ : Jₛ(S) →* (Θₛω(S, χ) →L[ℂ] Θₛω(S, χ)),
      Continuous (fun p : Jₛ(S) × Θₛω(S, χ) ↦ ρ p.1 p.2) ∧
      ∀ (g : (SAdeleRing F S)ˣ) (f : ℬₛ(S)),
        ρ (QuotientGroup.mk g) ((Kₛω(S, χ)).mkQ f) =
          (Kₛω(S, χ)).mkQ (schwartzBruhatUnitTranslate g f) := by
  let N := Subgroup.map (Units.map ((adeleProjection F S).comp (integralAdelesOutside F S).subtype).toMonoidHom)
    (MonoidHom.range (Units.map (integralAdeleDiagonal F S).toMonoidHom))
  let θ := sLocalHomogeneousAdelicThetaLinearMap F S χ
  let Tt := unitTranslateEnd (R := SAdeleRing F S)
  let t := schwartzBruhatUnitTranslate (R := SAdeleRing F S)
  let r (g : (SAdeleRing F S)ˣ) (a : Jₛ(S)) := (QuotientGroup.mk g : Jₛ(S))⁻¹ * a
  have ht : ∀ g f, Tt g f = t g f := fun _ _ ↦ rfl
  have hr : ∀ g f a, θ (t g f) a = θ f (r g a) := sLocalHomogeneousTheta_translate_apply χ
  have hN (g : (SAdeleRing F S)ˣ) (hg : g ∈ N) (f : ℬₛ(S)) (a : Jₛ(S)) :
      θ f (r g a) = θ f a := by
    have h : (QuotientGroup.mk g : (SAdeleRing F S)ˣ ⧸ N) = 1 := (QuotientGroup.eq_one_iff g).mpr hg
    exact congrArg (θ f) ((congrArg (fun b : Jₛ(S) ↦ b⁻¹ * a) h).trans (by simp only [inv_one, one_mul]))
  have result := thetaAction_of_translate (G := (SAdeleRing F S)ˣ) (E := ℬₛ(S)) (A := Jₛ(S))
    N θ Tt t ht continuous_sAdeleSchwartz_unitTranslate r hr hN
  simp only [Submodule.mkQ_apply]
  with_reducible exact result

private theorem sLocalHomogeneousThetaTransition_equivariant_mul_mem {R : Type*} [CommRing R]
    {D : Subring R} (u : Dˣ) (x : R) : u.val.val * x ∈ D ↔ x ∈ D := by
  constructor
  · intro h
    have hh := D.mul_mem u.inv.property h
    rwa [← mul_assoc, show u.inv.val * u.val.val = 1 from congrArg Subtype.val u.inv_val,
      one_mul] at hh
  · exact D.mul_mem u.val.property

private theorem sLocalHomogeneousThetaTransition_equivariant_toGlobal
    (S : Finset (HeightOneSpectrum (𝓞 F))) (f : ℬₛ(S)) (x : 𝔸[F]) :
    sAdeleSchwartzToGlobal F S f (Multiplicative.ofAdd x) =
      open Classical in if x ∈ integralAdelesOutside F S then
        f (Multiplicative.ofAdd (adeleProjection F S x)) else 0 := by
  classical
  have hi : x ∈ integralAdelesOutside F S ↔ ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S →
      x.2 v ∈ v.adicCompletionIntegers F := by
    simp only [integralAdelesOutside, Subring.mem_iInf]
    rfl
  exact (sAdeleSchwartzToGlobal_apply F S f x).trans (if_congr hi.symm rfl rfl)

private theorem sLocalHomogeneousThetaTransition_equivariant_insert
    (S : Finset (HeightOneSpectrum (𝓞 F))) (u : (integralAdelesOutside F S)ˣ) (f : ℬₛ(S)) :
    sAdeleSchwartzToGlobal F S (schwartzBruhatUnitTranslate
        (Units.map (adeleProjection F S).toMonoidHom (integralIdeleInsertion F S u)) f) =
      schwartzBruhatUnitTranslate (integralIdeleInsertion F S u)
        (sAdeleSchwartzToGlobal F S f) := by
  classical
  let g := integralIdeleInsertion F S u
  let gS := Units.map (adeleProjection F S).toMonoidHom g
  refine Subtype.ext (funext fun x ↦ ?_)
  let y := x.toAdd
  have h := sLocalHomogeneousThetaTransition_equivariant_mul_mem u⁻¹ y
  change g.inv * y ∈ integralAdelesOutside F S ↔ y ∈ integralAdelesOutside F S at h
  refine (sLocalHomogeneousThetaTransition_equivariant_toGlobal S
    (schwartzBruhatUnitTranslate gS f) y).trans ?_
  refine Eq.trans (if_congr h.symm ?_ rfl)
    (sLocalHomogeneousThetaTransition_equivariant_toGlobal S f (g.inv * y)).symm
  exact congrArg (fun t ↦ f (Multiplicative.ofAdd t)) (map_mul (adeleProjection F S) g.inv y).symm

private theorem sLocalHomogeneousThetaTransition_equivariant_range {g : IdeleGroup (𝓞 F) F}
    (hg : g ∈ Set.range (integralIdeleInsertion F T)) (f : ℬₛ(T)) :
    sAdeleSchwartzToGlobal F T
      (schwartzBruhatUnitTranslate (Units.map (adeleProjection F T).toMonoidHom g) f) =
        schwartzBruhatUnitTranslate g (sAdeleSchwartzToGlobal F T f) := by
  obtain ⟨u, rfl⟩ := hg
  exact sLocalHomogeneousThetaTransition_equivariant_insert T u f

private theorem sLocalHomogeneousThetaTransition_equivariant_test (hST : S ⊆ T)
    (u : (integralAdelesOutside F S)ˣ) (f : ℬₛ(S)) :
    let g := integralIdeleInsertion F S u
    let gS := Units.map (adeleProjection F S).toMonoidHom g
    let gT := Units.map (adeleProjection F T).toMonoidHom g
    sAdeleSchwartzTransition F hST (schwartzBruhatUnitTranslate gS f) =
      schwartzBruhatUnitTranslate gT (sAdeleSchwartzTransition F hST f) := by
  let g := integralIdeleInsertion F S u
  have hg : g ∈ Set.range (integralIdeleInsertion F T) :=
    (mem_range_integralIdeleInsertion F T g).mpr fun v hv ↦
      (mem_range_integralIdeleInsertion F S g).mp ⟨u, rfl⟩ v (fun h ↦ hv (hST h))
  have hTS (k : ℬₛ(S)) : sAdeleSchwartzToGlobal F T (sAdeleSchwartzTransition F hST k) =
      sAdeleSchwartzToGlobal F S k := DFunLike.congr_fun (sAdeleSchwartzToGlobal_comp F hST) k
  have hT := sLocalHomogeneousThetaTransition_equivariant_range hg
    (sAdeleSchwartzTransition F hST f)
  exact (sAdeleSchwartzToGlobal_isEmbedding F T).injective
    ((hTS _).trans ((sLocalHomogeneousThetaTransition_equivariant_insert S u f).trans
        ((congrArg (schwartzBruhatUnitTranslate g) (hTS f).symm).trans hT.symm)))

private theorem sLocalHomogeneousThetaTransition_equivariant_gen {E E' Q Q' : Type*}
    (q : E → Q) (q' : E' → Q')
    (hq : Surjective q)
    (π : Q → Q') (T : E → E') (hπ : ∀ f, π (q f) = q' (T f))
    (a : Q → Q) (b : Q' → Q') (s : E → E) (t : E' → E')
    (ha : ∀ f, a (q f) = q (s f)) (hb : ∀ f, b (q' f) = q' (t f))
    (hst : ∀ f, T (s f) = t (T f)) (x : Q) : π (a x) = b (π x) := by
  obtain ⟨f, rfl⟩ := hq x
  rw [ha f, hπ, hπ, hb, hst]

private theorem sLocalHomogeneousThetaTransition_equivariant_aux (hST : S ⊆ T)
    (χS : PontryaginDual (J₁(S)))
    (χT : PontryaginDual (J₁(T)))
    (π : Θₛω(S, χS) → Θₛω(T, χT))
    (hπ : ∀ f, π ((Kₛω(S, χS)).mkQ f) = (Kₛω(T, χT)).mkQ (sAdeleSchwartzTransition F hST f))
    (gS : (SAdeleRing F S)ˣ) (gT : (SAdeleRing F T)ˣ)
    (hst : ∀ f, sAdeleSchwartzTransition F hST (schwartzBruhatUnitTranslate gS f) =
      schwartzBruhatUnitTranslate gT (sAdeleSchwartzTransition F hST f))
    (x : Θₛω(S, χS)) :
    π ((existsUnique_sLocalHomogeneousThetaAction (F := F) (S := S) χS).exists.choose
        (QuotientGroup.mk gS) x) =
      (existsUnique_sLocalHomogeneousThetaAction (F := F) (S := T) χT).exists.choose
        (QuotientGroup.mk gT) (π x) :=
  sLocalHomogeneousThetaTransition_equivariant_gen (Kₛω(S, χS)).mkQ (Kₛω(T, χT)).mkQ
    (Submodule.mkQ_surjective _) π _ hπ _ _ _ _
    (fun f ↦ (existsUnique_sLocalHomogeneousThetaAction (F := F) (S := S) χS).exists.choose_spec.2
      gS f)
    (fun f ↦ (existsUnique_sLocalHomogeneousThetaAction (F := F) (S := T) χT).exists.choose_spec.2
      gT f)
    hst x

private theorem sLocalHomogeneousThetaTransition_equivariant_aux2
    (hω : NormOneCharacterUnramifiedOutside (F := F) ω S) (hST : S ⊆ T)
    (gS : (SAdeleRing F S)ˣ) (gT : (SAdeleRing F T)ˣ)
    (hst : ∀ f, sAdeleSchwartzTransition F hST (schwartzBruhatUnitTranslate gS f) =
      schwartzBruhatUnitTranslate gT (sAdeleSchwartzTransition F hST f))
    (x : Θₛω(S, ωₛ(S, hω))) :
    sLocalHomogeneousThetaTransition (F := F) (ω := ω) hω hST
        ((existsUnique_sLocalHomogeneousThetaAction (F := F) (S := S) (ωₛ(S, hω))).exists.choose
          (QuotientGroup.mk gS) x) =
      (existsUnique_sLocalHomogeneousThetaAction (F := F) (S := T)
          (ωₛ(T, NormOneCharacterUnramifiedOutside.mono (F := F) (ω := ω) hω hST))).exists.choose
        (QuotientGroup.mk gT) (sLocalHomogeneousThetaTransition (F := F) (ω := ω) hω hST x) :=
  sLocalHomogeneousThetaTransition_equivariant_aux hST _ _
    (⇑(sLocalHomogeneousThetaTransition (F := F) (ω := ω) hω hST))
    (fun f ↦ LinearMap.congr_fun
      (sLocalHomogeneousThetaTransition_spec (F := F) (ω := ω) hω hST).1 f) gS gT hst x

/-- Paper: Theorem 5.2.3.1(1), p. 233.
The homogeneous transition intertwines the descended actions on theta classes.
Deviation: The acting class is represented by an idele integral and invertible outside S. -/
theorem sLocalHomogeneousThetaTransition_equivariant
    (hω : NormOneCharacterUnramifiedOutside (F := F) ω S) (hST : S ⊆ T)
    (u : (integralAdelesOutside F S)ˣ) (x : Θₛω(S, ωₛ(S, hω))) :
    let hT := NormOneCharacterUnramifiedOutside.mono (F := F) (ω := ω) hω hST
    let ρS := (existsUnique_sLocalHomogeneousThetaAction (F := F) (S := S) (ωₛ(S, hω))).exists.choose
    let ρT := (existsUnique_sLocalHomogeneousThetaAction (F := F) (S := T) (ωₛ(T, hT))).exists.choose
    let π := sLocalHomogeneousThetaTransition (F := F) (ω := ω) hω hST
    let g := integralIdeleInsertion F S u
    let gS := Units.map (adeleProjection F S).toMonoidHom g
    let gT := Units.map (adeleProjection F T).toMonoidHom g
    π (ρS (QuotientGroup.mk gS) x) = ρT (QuotientGroup.mk gT) (π x) :=
  sLocalHomogeneousThetaTransition_equivariant_aux2 hω hST _ _
    (sLocalHomogeneousThetaTransition_equivariant_test (F := F) hST u) x

/-- Paper: Theorem 5.2.3.1(1), pp. 233–234.
Insertion of test functions into the adeles preserves the homogeneous theta kernels. -/
theorem sLocalHomogeneousThetaToGlobal_preserves_kernel
    (hω : NormOneCharacterUnramifiedOutside (F := F) ω S) :
    Kₛω(S, ωₛ(S, hω)) ≤ (K𝔽ω(ω)).comap (sAdeleSchwartzToGlobal F S) := by
  let ρS := (existsUnique_sLocalThetaAction (F := F) (S := S)).exists.choose
  let relS (p : J₁(S) × Θₛ(S)) := p.2 - star (ωₛ(S, hω) p.1 : ℂ) • ρS p.1.val p.2
  let DS := (Submodule.span ℂ (Set.range relS)).topologicalClosure
  let ρF := (existsUnique_globalThetaAction (F := F)).exists.choose
  let relF (p : C₁ × Θ𝔽) := p.2 - star (ω p.1 : ℂ) • ρF p.1.val p.2
  let DF := (Submodule.span ℂ (Set.range relF)).topologicalClosure
  have hmemS (f : ℬₛ(S)) : f ∈ Kₛω(S, ωₛ(S, hω)) ↔ (Kₛ(S)).mkQ f ∈ DS := by
    have h : ∃ e : Θₛω(S, ωₛ(S, hω)) ≃L[ℂ] (Θₛ(S) ⧸ DS),
        ∀ k : ℬₛ(S), e (Submodule.Quotient.mk k) = DS.mkQ ((Kₛ(S)).mkQ k) := by
      unfold DS relS ρS
      with_reducible exact sLocalHomogeneousThetaSpace_equiv_coinvariants (F := F) (S := S) (ωₛ(S, hω))
    refine h.elim fun e he ↦ ?_
    have he' := congrArg (fun z : Θₛ(S) ⧸ DS ↦ z = 0) (he f)
    have hz := ContinuousLinearEquiv.map_eq_zero_iff e (x := Submodule.Quotient.mk f)
    exact (Submodule.Quotient.mk_eq_zero (Kₛω(S, ωₛ(S, hω)))).symm.trans
      (hz.symm.trans (he'.to_iff.trans (Submodule.Quotient.mk_eq_zero DS)))
  have hmemF (f : ℬ𝔽) : f ∈ K𝔽ω(ω) ↔ (K𝔽).mkQ f ∈ DF := by
    have h : ∃ e : Θ𝔽ω(ω) ≃L[ℂ] (Θ𝔽 ⧸ DF),
        ∀ k : ℬ𝔽, e (Submodule.Quotient.mk k) = DF.mkQ ((K𝔽).mkQ k) := by
      unfold DF relF ρF
      with_reducible exact globalHomogeneousThetaSpace_equiv_coinvariants (F := F) ω
    refine h.elim fun e he ↦ ?_
    have he' := congrArg (fun z : Θ𝔽 ⧸ DF ↦ z = 0) (he f)
    have hz := ContinuousLinearEquiv.map_eq_zero_iff e (x := Submodule.Quotient.mk f)
    exact (Submodule.Quotient.mk_eq_zero (K𝔽ω(ω))).symm.trans
      (hz.symm.trans (he'.to_iff.trans (Submodule.Quotient.mk_eq_zero DF)))
  let π := sLocalThetaToGlobal F S
  have hmap : DS ≤ DF.comap π := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨⟨a, y⟩, rfl⟩
      refine (Submodule.Quotient.mk_surjective (Kₛ(S)) y).elim fun f hy ↦ ?_
      rw [← hy]
      obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective a.val
      let j := sIdeleInsertion F S g
      have hS : Units.map (adeleProjection F S).toMonoidHom j = g :=
        Units.ext (Prod.ext (sIdeleInsertion_apply F S g).1
          (funext (sIdeleInsertion_apply F S g).2.1))
      have hn : ideleNorm F j = 1 := by
        rw [ideleNorm_sIdeleInsertion, ← sIdeleQuotientNorm_mk, hg]
        exact a.property
      let x : C₁ := ⟨QuotientGroup.mk j, hn⟩
      have hj : j ∈ Set.range (integralIdeleInsertion F S) := by
        apply (mem_range_integralIdeleInsertion F S j).2
        intro v hv
        have hi : j⁻¹.val.2 v = 1 := by
          change ((sIdeleInsertion F S g)⁻¹).val.2 v = 1
          rw [← map_inv]
          exact (sIdeleInsertion_apply F S g⁻¹).2.2 v hv
        exact ⟨(sIdeleInsertion_apply F S g).2.2 v hv ▸ (v.adicCompletionIntegers F).one_mem,
          hi ▸ (v.adicCompletionIntegers F).one_mem⟩
      obtain ⟨u, hu⟩ := hj
      have ha : a.val = QuotientGroup.mk (Units.map (adeleProjection F S).toMonoidHom
          (integralIdeleInsertion F S u)) := by
        rw [hu, hS]
        exact hg.symm
      have hx : x.val = QuotientGroup.mk (integralIdeleInsertion F S u) := by
        change QuotientGroup.mk j = _
        rw [hu]
      have hχ : ωₛ(S, hω) a = ω x :=
        sLocalNormOneCharacter_apply ω hω u x a hx ha
      let gS := Units.map (adeleProjection F S).toMonoidHom (integralIdeleInsertion F S u)
      let fF := sAdeleSchwartzToGlobal F S f
      let yS : Θₛ(S) := Submodule.Quotient.mk f
      have hρS : ρS a.val yS =
          Submodule.Quotient.mk (schwartzBruhatUnitTranslate gS f) := by
        have : a.val = QuotientGroup.mk gS := ha
        rw [this]
        change ρS (QuotientGroup.mk gS) (Submodule.Quotient.mk f) = _
        exact (existsUnique_sLocalThetaAction (F := F) (S := S)).exists.choose_spec.2 gS f
      have hρF : ρF x.val (Submodule.Quotient.mk fF) =
          Submodule.Quotient.mk
            (schwartzBruhatUnitTranslate (integralIdeleInsertion F S u) fF) := by
        have : x.val = QuotientGroup.mk (integralIdeleInsertion F S u) := hx
        rw [this]
        exact (existsUnique_globalThetaAction (F := F)).exists.choose_spec.2
          (integralIdeleInsertion F S u) fF
      have hπ : π yS = Submodule.Quotient.mk fF := by
        unfold π yS fF sLocalThetaToGlobal
        exact Submodule.mapQ_apply _ _ _ f
      have heq : π (ρS a.val yS) = ρF x.val (π yS) :=
        calc
          π (ρS a.val yS) = π (Submodule.Quotient.mk (schwartzBruhatUnitTranslate gS f)) := by
            rw [hρS]
          _ = Submodule.Quotient.mk
              (schwartzBruhatUnitTranslate (integralIdeleInsertion F S u) fF) :=
            sLocalThetaToGlobal_equivariant u f
          _ = ρF x.val (Submodule.Quotient.mk fF) := hρF.symm
          _ = ρF x.val (π yS) := by rw [hπ]
      have hχ' : star (ωₛ(S, hω) a : ℂ) = star (ω x : ℂ) :=
        congrArg (fun z : Circle ↦ star (z : ℂ)) hχ
      have hrel : π (relS (a, yS)) = relF (x, π yS) := by
        unfold relS relF
        rw [map_sub, map_smul, hχ', heq]
      apply Submodule.mem_comap.mpr
      rw [hrel]
      exact Submodule.le_topologicalClosure _ (Submodule.subset_span (Set.mem_range_self (x, π yS)))
    · have hc : IsClosed (DF : Set Θ𝔽) :=
        (Submodule.span ℂ (Set.range relF)).isClosed_topologicalClosure
      exact hc.preimage sLocalThetaToGlobal_continuous
  intro f hf
  have h2 : π ((Kₛ(S)).mkQ f) ∈ DF := hmap ((hmemS f).mp hf)
  have h3 : (K𝔽).mkQ (sAdeleSchwartzToGlobal F S f) ∈ DF := by
    have hπf : π ((Kₛ(S)).mkQ f) = (K𝔽).mkQ (sAdeleSchwartzToGlobal F S f) := by
      unfold π sLocalThetaToGlobal
      exact Submodule.mapQ_apply _ _ _ f
    exact hπf ▸ h2
  exact (hmemF _).mpr h3

/-- Paper: (5.2.3.2), p. 233.
The stage insertion into the global homogeneous quotient is induced by extension
of test functions with integer indicators outside S. -/
def sLocalHomogeneousThetaToGlobal (hω : NormOneCharacterUnramifiedOutside (F := F) ω S) :
    Θₛω(S, ωₛ(S, hω)) →ₗ[ℂ] Θ𝔽ω(ω) :=
  (Kₛω(S, ωₛ(S, hω))).mapQ (K𝔽ω(ω)) (sAdeleSchwartzToGlobal F S)
    (sLocalHomogeneousThetaToGlobal_preserves_kernel (F := F) (ω := ω) hω)

/-- Paper: (5.2.3.2), p. 233.
The global homogeneous insertion agrees with test function insertion on representatives. -/
theorem sLocalHomogeneousThetaToGlobal_mk (hω : NormOneCharacterUnramifiedOutside (F := F) ω S)
    (f : ℬₛ(S)) :
    sLocalHomogeneousThetaToGlobal (F := F) (ω := ω) hω ((Kₛω(S, ωₛ(S, hω))).mkQ f) =
      (K𝔽ω(ω)).mkQ (sAdeleSchwartzToGlobal F S f) :=
  rfl

section HomogeneousStageImages

/-- Subtract the value at zero times the integer ball. The remaining radial function
has compact support away from zero, meeting only finitely many valuation shells. -/
private theorem radialTest_mem_of_balls (v : HeightOneSpectrum (𝓞 F))
    (b : SchwartzBruhat (Multiplicative (v.adicCompletion F)))
    (hb : ∀ x : v.adicCompletion F, b (Multiplicative.ofAdd x) =
      (v.adicCompletionIntegers F : Set _).indicator (fun _ ↦ 1) x)
    (M : Submodule ℂ (SchwartzBruhat (Multiplicative (v.adicCompletion F))))
    (hballs : ∀ u, schwartzBruhatUnitTranslate u b ∈ M)
    (f : SchwartzBruhat (Multiplicative (v.adicCompletion F)))
    (hrad : ∀ x y : v.adicCompletion F, Valued.v x = Valued.v y →
      f (Multiplicative.ofAdd x) = f (Multiplicative.ofAdd y)) : f ∈ M := by
  classical
  let K := v.adicCompletion F
  let ev (x : K) := schwartzBruhatEvalCLM (Multiplicative.ofAdd x)
  let d := f - (ev 0 f) • b
  have hbv (x : K) : ev x b = if Valued.v x ≤ 1 then 1 else 0 := by
    change b (Multiplicative.ofAdd x) = _
    rw [hb]
    exact if_congr (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v) rfl rfl
  have hd (x : K) : ev x d = ev x f - ev 0 f * ev x b := by
    dsimp only [d]
    rw [map_sub, map_smul, smul_eq_mul]
  have hd0 : ev 0 d = 0 := by rw [hd, hbv, map_zero, ite_eq_left zero_le_one, mul_one, sub_self]
  have hdr (x y : K) (h : Valued.v x = Valued.v y) : ev x d = ev y d := by
    rw [hd, hd, show ev x f = ev y f from hrad x y h, hbv, hbv, h]
  let Z := Function.support (fun x : K ↦ ev x d)
  obtain ⟨hl, hc⟩ := (mem_finitePlaceSchwartz_iff F v _).mp ⟨d, fun _ ↦ rfl⟩
  have hcl : IsClosed Z := (hl.isClopen_fiber 0).isOpen.isClosed_compl
  have hcompact : IsCompact Z := by
    change IsCompact (closure Z) at hc
    rwa [hcl.closure_eq] at hc
  let : CompactSpace Z := isCompact_iff_compactSpace.mp hcompact
  let value (x : Z) := Valued.v x.val
  have hvfin : (Set.range value).Finite := by
    apply IsLocallyConstant.range_finite
    refine (IsLocallyConstant.iff_eventually_eq _).mpr fun x ↦ ?_
    have hx : x.val ≠ 0 := fun hz ↦ x.property (hz ▸ hd0)
    exact continuous_subtype_val.continuousAt.eventually
      (Valued.locally_const ((Valuation.ne_zero_iff Valued.v).mpr hx))
  let A := hvfin.toFinset
  have hre (r) (hr : r ∈ A) : ∃ u : Kˣ, Valued.v u.val = r := by
    obtain ⟨x, hx⟩ := hvfin.mem_toFinset.mp hr
    exact ⟨Units.mk0 x.val (fun hz ↦ x.property (hz ▸ hd0)), hx⟩
  obtain ⟨p, hp⟩ := exists_unit_cut_parameter (F := F) v
  let ball (u : Kˣ) := schwartzBruhatUnitTranslate u b
  have hball (u : Kˣ) (x : K) : ev x (ball u) = if Valued.v x ≤ Valued.v u.val then 1 else 0 := by
    change b (Multiplicative.ofAdd (u.inv * x)) = _
    rw [show b (Multiplicative.ofAdd (u.inv * x)) = ev (u.inv * x) b from rfl, hbv]
    congr 1
    have hu : Valued.v u.val ≠ 0 := (Valuation.ne_zero_iff _).mpr u.ne_zero
    change (Valued.v ((u⁻¹).val * x) ≤ 1) = _
    rw [Units.val_inv_eq_inv_val, map_mul, map_inv₀, inv_mul_le_iff₀ (zero_lt_iff.mpr hu), mul_one]
  have shell (u : Kˣ) (x : K) : ev x (ball u - ball (u / p)) =
      if Valued.v x = Valued.v u.val then 1 else 0 := by
    rw [map_sub, hball, hball, Units.val_div_eq_div_val, map_div₀, hp]
    have hu : Valued.v u.val ≠ 0 := (Valuation.ne_zero_iff _).mpr u.ne_zero
    rcases eq_or_ne x 0 with rfl | hx
    · simp [Ne.symm hu]
    have hxv : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
    rw [← WithZero.exp_log hu, ← WithZero.exp_log hxv, ← WithZero.exp_sub]
    simp only [WithZero.exp_le_exp, WithZero.exp_inj]
    split_ifs <;> first | omega | norm_num
  let u (r : ↥A) := (hre r.val r.property).choose
  have hu (r : ↥A) : Valued.v (u r).val = r.val := (hre r.val r.property).choose_spec
  have he : d = ∑ r : ↥A, ev (u r).val d • (ball (u r) - ball (u r / p)) := by
    apply SchwartzBruhat.ext
    intro y
    let x := y.toAdd
    change ev x d = ev x _
    rw [map_sum]
    simp only [map_smul, smul_eq_mul, shell, hu, mul_ite, mul_one, mul_zero]
    by_cases hm : Valued.v x ∈ A
    · let r : ↥A := ⟨_, hm⟩
      rw [Finset.sum_eq_single r]
      · rw [ite_eq_left (show Valued.v x = r.val from rfl)]
        exact hdr x (u r).val (hu r).symm
      · intro t _ h
        exact ite_eq_right (fun e ↦ h (Subtype.ext e.symm))
      · simp
    · have hz : ev x d = 0 := by
        by_contra hn
        exact hm (hvfin.mem_toFinset.mpr ⟨⟨x, hn⟩, rfl⟩)
      rw [hz]
      exact (Finset.sum_eq_zero fun (r : ↥A) _ ↦ ite_eq_right
        (fun e : Valued.v x = r.val ↦ hm (e.symm ▸ r.property))).symm
  have hdM : d ∈ M := he ▸ M.sum_mem fun r _ ↦ M.smul_mem _ (M.sub_mem (hballs _) (hballs _))
  have hbM : b ∈ M := by
    have h1 : ball 1 = b := SchwartzBruhat.ext fun x ↦ by
      change b (Multiplicative.ofAdd (1 * x.toAdd)) = _; rw [one_mul]; rfl
    exact h1 ▸ hballs 1
  exact sub_add_cancel f ((ev 0 f) • b) ▸ M.add_mem hdM (M.smul_mem _ hbM)

/-- Modulo unit translation differences a finite-place test is represented by its
finite orbit average. A radial test is a sum of dilated integer-ball indicators. -/
private theorem finiteTest_mem_of_unit_differences (v : HeightOneSpectrum (𝓞 F))
    (b : SchwartzBruhat (Multiplicative (v.adicCompletion F)))
    (hb : ∀ x : v.adicCompletion F, b (Multiplicative.ofAdd x) =
      (v.adicCompletionIntegers F : Set _).indicator (fun _ ↦ 1) x)
    (M : Submodule ℂ (SchwartzBruhat (Multiplicative (v.adicCompletion F))))
    (hballs : ∀ u, schwartzBruhatUnitTranslate u b ∈ M)
    (hdiff : ∀ (u : (v.adicCompletionIntegers F).units) f,
      schwartzBruhatUnitTranslate u.val f - f ∈ M)
    (f : SchwartzBruhat (Multiplicative (v.adicCompletion F))) : f ∈ M := by
  classical
  let H := (v.adicCompletionIntegers F).units
  let ρ := (unitTranslateEnd (R := v.adicCompletion F)).comp H.subtype
  obtain ⟨O, hO, -⟩ := finitePlaceSchwartz_average_dilation v f
  have hf : (Set.range fun u : H ↦ ρ u f).Finite :=
    O.finite_toSet.subset fun x hx ↦ (hO x).mpr hx
  let B := hf.toFinset
  have hB : B.Nonempty := ⟨ρ 1 f, hf.mem_toFinset.mpr ⟨1, rfl⟩⟩
  let s := ∑ y ∈ B, y
  have hs : s ∈ M := by
    apply radialTest_mem_of_balls v b hb M hballs s
    intro x y hxy
    by_cases hx : x = 0
    · have hy : y = 0 := (Valuation.zero_iff _).mp (hxy.symm.trans (hx ▸ map_zero _))
      rw [hx, hy]
    have hy : y ≠ 0 := fun h ↦ hx ((Valuation.zero_iff _).mp (hxy.trans (h ▸ map_zero _)))
    let u := Units.mk0 y hy / Units.mk0 x hx
    have hu : u ∈ H := HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mpr
      (show Valued.v (y / x) = 1 by rw [map_div₀, hxy, div_self ((Valuation.ne_zero_iff _).mpr hy)])
    have hi := sum_orbit_invariant ρ f hf (⟨u, hu⟩ : H)⁻¹
    have he := congrArg (fun k : SchwartzBruhat (Multiplicative (v.adicCompletion F)) ↦
      k (Multiplicative.ofAdd x)) hi.symm
    exact he.trans (congrArg (fun z ↦ s (Multiplicative.ofAdd z)) (div_mul_cancel₀ y hx))
  have hzero : M.mkQ s = 0 := (Submodule.Quotient.mk_eq_zero M).mpr hs
  have hsum : M.mkQ s = (B.card : ℂ) • M.mkQ f := by
    dsimp only [s]
    rw [map_sum, Finset.sum_congr rfl (g := fun _ ↦ M.mkQ f) (fun x hx ↦ ?_), Finset.sum_const,
      Nat.cast_smul_eq_nsmul]
    obtain ⟨u, rfl⟩ := hf.mem_toFinset.mp hx
    exact (Submodule.Quotient.eq M).mpr (hdiff u f)
  rw [hsum, smul_eq_zero] at hzero
  exact (Submodule.Quotient.mk_eq_zero M).mp (by
    exact hzero.resolve_left (Nat.cast_ne_zero.mpr hB.card_pos.ne'))

local notation "𝕀" => IdeleGroup (𝓞 F) F

/-- On a fixed norm-one component, a norm-one translate acts by its character. -/
private theorem homogeneousClass_translate_normOne (g : 𝕀) (a : C₁)
    (ha : QuotientGroup.mk g = a.val) (f : ℬ𝔽) :
    (K𝔽ω(ω)).mkQ (schwartzBruhatUnitTranslate g f) = (ω a : ℂ) • (K𝔽ω(ω)).mkQ f := by
  rw [← map_smul]
  apply (Submodule.Quotient.eq _).mpr
  apply LinearMap.sub_mem_ker_iff.mpr
  apply ContinuousMap.ext
  intro x
  change homogeneousAdelicTheta ω (schwartzBruhatUnitTranslate g f) x = _
  calc
    _ = homogeneousAdelicTheta ω f (a.val⁻¹ * x) := by
      apply congrArg (MeasureTheory.integral _)
      funext h
      exact congrArg (· * (ω h : ℂ)) ((globalTheta_translate_apply g f _).trans (by rw [ha, mul_left_comm]))
    _ = _ := (homogeneousAdelicTheta_homogeneous ω f a x).trans (by rw [map_smul]; rfl)

/-- A stage image in the homogeneous quotient is stable under all idele translations.
The canonical archimedean section realizes the norm within the stage. -/
private theorem homogeneousStage_translate_mem (g : 𝕀) (f : ℬₛ(S)) :
    (K𝔽ω(ω)).mkQ (schwartzBruhatUnitTranslate g (sAdeleSchwartzToGlobal F S f)) ∈
      LinearMap.range ((K𝔽ω(ω)).mkQ.comp (sAdeleSchwartzToGlobal F S)) := by
  let a := canonicalIdeleNormSection F (ideleNorm F g)
  let x : C₁ := ⟨QuotientGroup.mk (g / a), by
    change ideleNorm F (g / a) = 1
    rw [map_div, canonicalIdeleNormSection_rightInverse F (ideleNorm F g), div_self']⟩
  have ha : a ∈ Set.range (integralIdeleInsertion F S) := by
    apply (mem_range_integralIdeleInsertion F S a).mpr
    intro v _
    have he := canonicalIdeleNormSection_finite F (ideleNorm F g)
    have hi := canonicalIdeleNormSection_finite F (ideleNorm F g)⁻¹
    rw [map_inv] at hi
    exact ⟨he ▸ (v.adicCompletionIntegers F).one_mem, hi ▸ (v.adicCompletionIntegers F).one_mem⟩
  let k := schwartzBruhatUnitTranslate (Units.map (adeleProjection F S).toMonoidHom a) f
  have hk : sAdeleSchwartzToGlobal F S k = schwartzBruhatUnitTranslate a (sAdeleSchwartzToGlobal F S f) :=
    insert_translate_of_mem_range ha f
  have hcomp : schwartzBruhatUnitTranslate (g / a) (schwartzBruhatUnitTranslate a (sAdeleSchwartzToGlobal F S f)) =
      schwartzBruhatUnitTranslate g (sAdeleSchwartzToGlobal F S f) := by
    exact (DFunLike.congr_fun (unitTranslateEnd.map_mul (g / a) a).symm _).trans
      (congrArg (fun u ↦ schwartzBruhatUnitTranslate u _) (div_mul_cancel g a))
  refine ⟨(ω x : ℂ) • k, ?_⟩
  rw [map_smul, LinearMap.comp_apply, hk, ← hcomp]
  exact (homogeneousClass_translate_normOne (g / a) x rfl _).symm

private theorem ideleClassNorm_of_integerUnit (v : HeightOneSpectrum (𝓞 F))
    (u : (v.adicCompletionIntegers F).units) :
    m𝔽 (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u.val) = 1 := by
  rw [ideleClassNorm_ofAdicCompletion]
  exact Units.ext (NNReal.eq (Valued.toNormedField.norm_eq_one_iff.mpr
    (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp u.property)))

/-- An unramified character is trivial on the embedded integer units. -/
private theorem homogeneousClass_translate_unit {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S)
    (hω : NormOneCharacterUnramifiedOutside (F := F) ω S)
    (u : (v.adicCompletionIntegers F).units) (f : ℬ𝔽) :
    (K𝔽ω(ω)).mkQ (schwartzBruhatUnitTranslate (IdeleGroup.ofAdicCompletion (𝓞 F) F v u.val) f) =
      (K𝔽ω(ω)).mkQ f := by
  let g := IdeleGroup.ofAdicCompletion (𝓞 F) F v u.val
  let x : C₁ := ⟨QuotientGroup.mk g, ideleClassNorm_of_integerUnit v u⟩
  obtain ⟨c, hc⟩ := hω
  have hu : (ω x : ℂ) = 1 := (hc x).symm.trans (by
    exact (mem_unramifiedOutside_iff F S c.val).mp c.property v hv
      ((v.adicCompletionIntegers F).toSubmonoid.unitsEquivUnitsType u))
  exact (homogeneousClass_translate_normOne g x rfl f).trans (by rw [hu, one_smul])

open scoped TensorProduct

local notation "Bᵥ(" v ")" => SchwartzBruhat (Multiplicative ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F))
local notation "B∞" => SchwartzBruhat (Multiplicative (InfiniteAdeleRing F))
local notation "pure(" T ")" => (sAdeleSchwartz_inductiveTensor_equiv F T).choose

open Classical in
/-- Varying one finite factor of a pure test commutes with the idele translation
supported at that place. -/
private theorem stagePure_translate (w : T) (u : (w.val.adicCompletion F)ˣ)
    (a : B∞) (g : ∀ j : T, Bᵥ(j.val)) :
    let e := pure(T)
    let γ := IdeleGroup.ofAdicCompletion (𝓞 F) F w.val u
    sAdeleSchwartzToGlobal F T
      (e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] j, Function.update g w (schwartzBruhatUnitTranslate u (g w)) j))) =
      schwartzBruhatUnitTranslate γ (sAdeleSchwartzToGlobal F T (e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] j, g j)))) := by
  classical
  intro e γ
  let σ := IdeleGroup.ofAdicCompletion (𝓞 F) F w.val
  have hs (b : (w.val.adicCompletion F)ˣ) (j : HeightOneSpectrum (𝓞 F)) (hj : j ≠ w.val) :
      (σ b).val.2 j = 1 := RestrictedProduct.mulSingle_eq_of_ne _ _ hj
  have hg : γ ∈ Set.range (integralIdeleInsertion F T) := by
    apply (mem_range_integralIdeleInsertion F T γ).mpr
    intro j hj
    have hne : j ≠ w.val := fun h ↦ hj (h ▸ w.property)
    change (σ u).val.2 j ∈ _ ∧ ((σ u)⁻¹).val.2 j ∈ _
    rw [← map_inv, hs _ _ hne, hs _ _ hne]
    exact ⟨one_mem _, one_mem _⟩
  refine Eq.trans ?_ (insert_translate_of_mem_range hg (e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] j, g j))))
  apply congrArg (sAdeleSchwartzToGlobal F T)
  apply SchwartzBruhat.ext
  intro y
  let z := y.toAdd
  let G := Units.map (adeleProjection F T).toMonoidHom γ
  change e _ (Multiplicative.ofAdd z) = e _ (Multiplicative.ofAdd (G.inv * z))
  refine ((sAdeleSchwartz_inductiveTensor_equiv F T).choose_spec a _ z).trans
    (Eq.trans ?_ ((sAdeleSchwartz_inductiveTensor_equiv F T).choose_spec a g (G.inv * z)).symm)
  have harch : (G.inv * z).1 = z.1 := one_mul _
  rw [harch]
  apply congrArg (_ * ·)
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  by_cases hj : j = w
  · subst j
    rw [Function.update_self, schwartzBruhatUnitTranslate_apply]
    exact congrArg (fun t ↦ g w (Multiplicative.ofAdd (t * z.2 w)))
      (RestrictedProduct.mulSingle_eq_same (fun j : HeightOneSpectrum (𝓞 F) ↦ j.adicCompletionIntegers F)
        w.val u.inv).symm
  · rw [Function.update_of_ne hj]
    change g j _ = g j (Multiplicative.ofAdd ((σ u⁻¹).val.2 j.val * z.2 j))
    rw [hs _ _ (fun h ↦ hj (Subtype.ext h)), one_mul]

open Classical in
private theorem stagePure_insert (h : S ⊆ T) (w : T) (hw : w.val ∉ S)
    (hnew : ∀ j : T, j.val ∉ S → j = w) (a : B∞) (g : ∀ j : T, Bᵥ(j.val))
    (b : Bᵥ(w.val)) (hb : ∀ x : w.val.adicCompletion F, b (Multiplicative.ofAdd x) =
      (w.val.adicCompletionIntegers F : Set _).indicator (fun _ ↦ 1) x) :
    pure(T) (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] j, Function.update g w b j)) =
      sAdeleSchwartzTransition F h (pure(S) (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] j : S, g ⟨j.val, h j.property⟩))) := by
  classical
  let f := pure(S) (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] j : S, g ⟨j.val, h j.property⟩))
  apply SchwartzBruhat.ext
  intro x
  refine ((sAdeleSchwartz_inductiveTensor_equiv F T).choose_spec a _ x.toAdd).trans ?_
  symm
  refine sAdeleSchwartzTransition_pure F h a (Function.update g w b) ?_ f ?_ x.toAdd
  · intro j hj
    have he : j = w := hnew j hj
    subst j
    simpa only [Function.update_self] using hb
  · intro z
    refine ((sAdeleSchwartz_inductiveTensor_equiv F S).choose_spec a _ z).trans ?_
    apply congrArg (_ * ·)
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    rw [Function.update_of_ne (show (⟨j.val, h j.property⟩ : T) ≠ w from
      fun he ↦ hw ((show j.val = w.val from congrArg Subtype.val he) ▸ j.property))]

/-- A larger stage adds no new global homogeneous classes at an unramified place.
After averaging the new factor over units, each dilated ball is absorbed by a
translate of the old test. -/
private theorem homogeneousStage_range_insert (hω : NormOneCharacterUnramifiedOutside (F := F) ω S)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S) :
    open Classical in
    LinearMap.range ((K𝔽ω(ω)).mkQ.comp (sAdeleSchwartzToGlobal F (insert v S))) ≤
      LinearMap.range ((K𝔽ω(ω)).mkQ.comp (sAdeleSchwartzToGlobal F S)) := by
  classical
  let T := insert v S
  let w : T := ⟨v, Finset.mem_insert_self _ _⟩
  let hST : S ⊆ T := Finset.subset_insert v S
  let J := (K𝔽ω(ω)).mkQ.comp (sAdeleSchwartzToGlobal F T)
  let R := LinearMap.range ((K𝔽ω(ω)).mkQ.comp (sAdeleSchwartzToGlobal F S))
  let D := R.comap J
  let V := FinestLocallyConvex (⨂[ℂ] j : T, Bᵥ(j.val))
  let e := pure(T)
  have hpure (a : B∞) (g : ∀ j : T, Bᵥ(j.val)) : e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] j, g j)) ∈ D := by
    let k : Bᵥ(v) →ₗ[ℂ] ℬₛ(T) := e.toLinearMap.comp ((TensorProduct.mk ℂ B∞ V a).comp
      ((PiTensorProduct.tprod ℂ).toLinearMap g w))
    have hk (b : Bᵥ(v)) : k b = e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] j, Function.update g w b j)) := rfl
    let G := IdeleGroup.ofAdicCompletion (𝓞 F) F v
    have ht (u : (v.adicCompletion F)ˣ) (b : Bᵥ(v)) :
        sAdeleSchwartzToGlobal F T (k (schwartzBruhatUnitTranslate u b)) =
          schwartzBruhatUnitTranslate (G u) (sAdeleSchwartzToGlobal F T (k b)) := by
      have h := stagePure_translate w u a (Function.update g w b)
      simpa only [hk, Function.update_self, Function.update_idem] using h
    let b := finiteStandardGaussian v 1
    have hb (x : v.adicCompletion F) : b (Multiplicative.ofAdd x) =
        (v.adicCompletionIntegers F : Set _).indicator (fun _ ↦ 1) x := by
      change finiteStandardGaussianValue v 1 x = _
      unfold finiteStandardGaussianValue
      exact ite_eq_left fun _ _ ↦ rfl
    let f := pure(S) (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] j, g ⟨j.val, hST j.property⟩))
    have hnew (j : T) (hj : j.val ∉ S) : j = w :=
      Subtype.ext ((Finset.mem_insert.mp j.property).resolve_right hj)
    have hkb : k b = sAdeleSchwartzTransition F hST f :=
      (hk b).trans (stagePure_insert hST w hv hnew a g b hb)
    have hball (u : (v.adicCompletion F)ˣ) : schwartzBruhatUnitTranslate u b ∈ D.comap k := by
      change (K𝔽ω(ω)).mkQ (sAdeleSchwartzToGlobal F T (k _)) ∈ R
      have he : sAdeleSchwartzToGlobal F T (sAdeleSchwartzTransition F hST f) =
          sAdeleSchwartzToGlobal F S f := LinearMap.congr_fun (sAdeleSchwartzToGlobal_comp F hST) f
      rw [ht, hkb, he]
      exact homogeneousStage_translate_mem (ω := ω) (G u) f
    have hd (u : (v.adicCompletionIntegers F).units) (b' : Bᵥ(v)) :
        schwartzBruhatUnitTranslate u.val b' - b' ∈ D.comap k := by
      change J (k _) ∈ R
      rw [map_sub, map_sub]
      change (K𝔽ω(ω)).mkQ (sAdeleSchwartzToGlobal F T (k _)) - (K𝔽ω(ω)).mkQ _ ∈ R
      rw [ht, homogeneousClass_translate_unit hv hω, sub_self]
      exact R.zero_mem
    have H : k (g w) ∈ D := finiteTest_mem_of_unit_differences v b hb (D.comap k) hball hd (g w)
    simpa only [hk, Function.update_eq_self] using H
  have hgen (a : B∞) (z : V) : e (a ⊗ₜ[ℂ] z) ∈ D := by
    let L := e.toLinearMap.comp (TensorProduct.mk ℂ B∞ V a)
    change L z ∈ D
    refine PiTensorProduct.induction_on (motive := fun z : ⨂[ℂ] j : T, Bᵥ(j.val) ↦ L z ∈ D) z ?_ ?_
    · intro r g
      change L (r • (show V from (⨂ₜ[ℂ] j, g j))) ∈ D
      rw [map_smul]
      exact D.smul_mem _ (hpure a g)
    · exact fun _ _ ↦ (D.comap L).add_mem
  rintro _ ⟨y, rfl⟩
  obtain ⟨z, rfl⟩ := e.surjective y
  exact TensorProduct.inductionOn (motive := fun z ↦ e z ∈ D) z hgen
    (fun _ _ ↦ (D.comap e.toLinearMap).add_mem)

/-- The extension from any stage containing the ramified places is surjective on
homogeneous classes. Exhaust global tests by finite stages and remove one unramified
place at a time. -/
private theorem homogeneousStage_surjective
    (hω : NormOneCharacterUnramifiedOutside (F := F) ω S) :
    Surjective (sLocalHomogeneousThetaToGlobal (F := F) (ω := ω) hω) := by
  classical
  let J (T : Finset (HeightOneSpectrum (𝓞 F))) := (K𝔽ω(ω)).mkQ.comp (sAdeleSchwartzToGlobal F T)
  have hle (T : Finset (HeightOneSpectrum (𝓞 F))) : (J (S ∪ T)).range ≤ (J S).range := by
    induction T using Finset.induction_on with
    | empty => rw [Finset.union_empty]
    | insert v T _ ih =>
      rw [Finset.union_insert]
      by_cases hv : v ∈ S ∪ T
      · rwa [Finset.insert_eq_of_mem hv]
      · exact (homogeneousStage_range_insert (hω.mono (show S ⊆ S ∪ T from Finset.subset_union_left)) v hv).trans ih
  intro x
  obtain ⟨f, rfl⟩ := (K𝔽ω(ω)).mkQ_surjective x
  obtain ⟨T, g, hg⟩ := sAdeleSchwartzToGlobal_exhaustive F f
  let h : T ⊆ S ∪ T := Finset.subset_union_right
  have he := (LinearMap.congr_fun (sAdeleSchwartzToGlobal_comp F h) g).trans hg
  obtain ⟨k, hk⟩ := hle T ⟨sAdeleSchwartzTransition F h g, congrArg (K𝔽ω(ω)).mkQ he⟩
  exact ⟨(Kₛω(S, ωₛ(S, hω))).mkQ k, hk⟩

end HomogeneousStageImages

section HomogeneousStageTopology

local notation "ιℂ" => (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ)
local notation "twₛ" => quasiCharacterNormTwist (mₛ(S)) (isProperMap_sIdeleQuotientNorm F S).continuous

/-- In a split norm group, every character with the given norm-one restriction
is a norm twist of any one extension. -/
private theorem exists_normTwist_of_agree_on_ker {G : Type*} [CommGroup G] [TopologicalSpace G]
    (m : G →* ℝ≥0ˣ) (hm : Continuous m) (σ : ℝ≥0ˣ →ₜ* G) (hσ : RightInverse σ m)
    (b c : QuasiCharacter G) (hc : ∀ x : m.ker, c x.val = b x.val) :
    ∃ z, quasiCharacterNormTwist m hm b z = c := by
  obtain ⟨u, hu, -⟩ := existsUnique_complexPower (b.comp σ)
  obtain ⟨v, hv, -⟩ := existsUnique_complexPower (c.comp σ)
  refine ⟨v - u, ContinuousMonoidHom.ext fun x ↦ ?_⟩
  let t := m x
  let y : m.ker := ⟨x / σ t, by simp [MonoidHom.mem_ker, t, hσ (m x)]⟩
  have hxy : y.val * σ t = x := div_mul_cancel x _
  have hb : b x = b y.val * (((t.val : ℝ) : ℂ)) ^ u := hxy ▸ (map_mul b y.val (σ t)).trans
    (congrArg (b y.val * ·) (hu t))
  have he : c x = c y.val * (((t.val : ℝ) : ℂ)) ^ v := hxy ▸ (map_mul c y.val (σ t)).trans
    (congrArg (c y.val * ·) (hv t))
  change b x * (((t.val : ℝ) : ℂ)) ^ (v - u) = c x
  rw [hb, he, hc y, mul_assoc, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr
    (NNReal.coe_ne_zero.mpr t.ne_zero)), add_sub_cancel]

/-- Deleting finitely many places leaves a nonzero Euler multiplier in the
half-plane of absolute convergence. -/
private theorem outsideEuler_ne_zero (S : Finset (HeightOneSpectrum (𝓞 F)))
    (χ : PontryaginDual C𝔽) (s : ℂ) (hs : 1 < s.re) :
    (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, finiteHeckeEulerFactor χ v.val s) ≠ 0 := by
  classical
  let E (v : HeightOneSpectrum (𝓞 F)) := finiteHeckeEulerFactor χ v s
  let C := {v : HeightOneSpectrum (𝓞 F) | v ∉ S}
  have hprod := finiteHeckeL_hasProd χ ⟨s, hs⟩
  have hL := finiteHeckeL_ne_zero_of_one_lt_re χ ⟨s, hs⟩
  have he (v) : E v ≠ 0 := fun h ↦ hL (hprod.tprod_eq.symm.trans (tprod_of_exists_eq_zero ⟨v, h⟩))
  -- Remove the finitely many factors as in §3.4, tprod_finiteHeckeEulerFactor_outside.
  have hp := hprod.congr_cofinite₀ (s := S) (g := C.mulIndicator E)
    (fun v _ ↦ he v) (fun v hv ↦ (Set.mulIndicator_of_mem hv E).symm)
  have ht : (∏' v : C, E v.val) = _ := (hasProd_subtype_iff_mulIndicator.mpr hp).tprod_eq
  change (∏' v : C, E v.val) ≠ 0
  rw [ht]
  refine mul_ne_zero hL (div_ne_zero (Finset.prod_ne_zero_iff.mpr ?_)
    (Finset.prod_ne_zero_iff.mpr fun v _ ↦ he v))
  intro v hv
  rw [Set.mulIndicator_of_notMem (show v ∉ C from not_not_intro hv)]
  exact one_ne_zero

/-- Weil's insertion formula reflects a vanishing zeta integral at every
unramified character in the right half-plane. -/
private theorem localIntegral_zero_of_insert (χ : PontryaginDual C𝔽) (s : ℂ) (hs : 1 < s.re)
    (hu : ideleClassNormTwist χ s ∈ unramifiedOutside F S) (f : ℬₛ(S))
    (h : globalIdelicZetaIntegral (sAdeleSchwartzToGlobal F S f) (ideleClassNormTwist χ s) = 0) :
    sLocalIdelicZetaIntegral f (sIdeleRestriction F S ⟨_, hu⟩) = 0 := by
  rw [weilIdentity_unramifiedOutside S f χ s hs hu] at h
  refine (mul_eq_zero.mp ((mul_eq_zero.mp h).resolve_right (outsideEuler_ne_zero S χ s hs))).resolve_left
    (finprod_ne_zero fun v ↦ ?_)
  rw [finiteLocalMultiplicativeTamagawaMeasure_integerUnits, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
  have hq : 0 < (v.val.asIdeal.absNorm : ℝ) := by
    exact_mod_cast (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v.val))
  exact Complex.ofReal_ne_zero.mpr (inv_ne_zero (Real.sqrt_pos.mpr (pow_pos hq _)).ne')

/-- Every chart on the global component is unramified outside the same places,
and its restriction is a single unitary norm chart on the stage. -/
private theorem homogeneousStage_restriction_chart
    (hω : NormOneCharacterUnramifiedOutside (F := F) ω S) :
    ∃ (χ : PontryaginDual C𝔽) (ψ : PontryaginDual (Jₛ(S)))
      (hu : ∀ z, ideleClassNormTwist χ z ∈ unramifiedOutside F S),
      (∀ z (x : C₁), ideleClassNormTwist χ z x.val = (ω x : ℂ)) ∧
      (∀ z, sIdeleRestriction F S ⟨_, hu z⟩ = twₛ ((ιℂ).comp ψ) z) ∧
      ∀ y : J₁(S), (ψ y.val : ℂ) = ωₛ(S, hω) y := by
  obtain ⟨c, hc⟩ := hω
  obtain ⟨χ, s, hs⟩ := exists_ideleClassNormTwist c.val
  have hres (z : ℂ) (x : C₁) : ideleClassNormTwist χ z x.val = (ω x : ℂ) :=
    (normOneRestriction_unitaryChart m𝔽 (isProperMap_ideleClassNorm F).continuous χ z x).trans
      ((normOneRestriction_unitaryChart m𝔽 (isProperMap_ideleClassNorm F).continuous χ s x).symm.trans
        ((DFunLike.congr_fun hs x.val).trans (hc x)))
  have hu (z : ℂ) : ideleClassNormTwist χ z ∈ unramifiedOutside F S := by
    apply (mem_unramifiedOutside_iff F S _).mpr
    intro v hv u
    let g := Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u
    let y := IdeleClassGroup.ofAdicCompletion (𝓞 F) F v g
    have hy : m𝔽 y = 1 := ideleClassNorm_of_integerUnit v ⟨g, u.val.property, u.inv.property⟩
    exact (hres z ⟨y, hy⟩).trans ((hc ⟨y, hy⟩).symm.trans
      ((mem_unramifiedOutside_iff F S c.val).mp c.property v hv u))
  let b := sIdeleRestriction F S ⟨_, hu 0⟩
  have hb (g : (SAdeleRing F S)ˣ) : b (QuotientGroup.mk g) =
      (χ (QuotientGroup.mk (sIdeleInsertion F S g)) : ℂ) := by
    rw [show b (QuotientGroup.mk g) = _ from sIdeleRestriction_mk F S _ g]
    let y : C𝔽 := QuotientGroup.mk (sIdeleInsertion F S g)
    change (χ y : ℂ) * (((m𝔽 y : ℝ≥0) : ℝ) : ℂ) ^ (0 : ℂ) = _
    rw [Complex.cpow_zero, mul_one]
  have hnorm (x : Jₛ(S)) : ‖b x‖ = 1 := by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    rw [hb, Circle.norm_coe]
  let ψ : PontryaginDual (Jₛ(S)) :=
    { toFun := fun x ↦ ⟨b x, mem_sphere_zero_iff_norm.mpr (hnorm x)⟩
      map_one' := Circle.ext (map_one b)
      map_mul' := fun x y ↦ Circle.ext (map_mul b x y)
      continuous_toFun := b.continuous.subtype_mk _ }
  refine ⟨χ, ψ, hu, hres, fun z ↦ ContinuousMonoidHom.ext fun x ↦ ?_, fun y ↦ ?_⟩
  · obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    rw [sIdeleRestriction_mk]
    let y : C𝔽 := QuotientGroup.mk (sIdeleInsertion F S g)
    change (χ y : ℂ) * (((m𝔽 y : ℝ≥0) : ℝ) : ℂ) ^ z =
      b (QuotientGroup.mk g) * (((mₛ(S) (QuotientGroup.mk g) : ℝ≥0) : ℝ) : ℂ) ^ z
    rw [hb, sIdeleQuotientNorm_mk, ← ideleNorm_sIdeleInsertion]
    rfl
  · exact (sLocalNormOneCharacter_eq_sIdeleRestriction ω ⟨_, hu 0⟩ (hres 0) y).symm

private theorem homogeneousStage_injective (hω : NormOneCharacterUnramifiedOutside (F := F) ω S) :
    Injective (sLocalHomogeneousThetaToGlobal (F := F) (ω := ω) hω) := by
  refine injective_mapQ_of_comap_le _ _ _ _ ?_
  intro f hf
  have hg := (mem_homogeneousAdelicTheta_ker_iff ω (sAdeleSchwartzToGlobal F S f)).mp hf
  apply (mem_sLocalHomogeneousAdelicTheta_ker_iff (ωₛ(S, hω)) f).mpr
  obtain ⟨χ, ψ, hu, hres, hchart, hψ⟩ := homogeneousStage_restriction_chart hω
  have hz (s : ℂ) (hs : 1 < s.re) : sLocalIdelicZFunction f (twₛ ((ιℂ).comp ψ) s) = 0 := by
    rw [sLocalIdelicZFunction_eq_integral f ⟨ψ, s, zero_lt_one.trans hs, rfl⟩, ← hchart]
    apply localIntegral_zero_of_insert χ s hs
    rw [← globalIdelicZFunction_eq_integral _ (globalTwist_mem_rightHalf χ hs)]
    exact hg ⟨_, globalOrderBound_rightHalf χ hs⟩ (hres s)
  have hzero := eq_of_agree_rightHalf (sLocalIdelicZFunction_meromorphic f ψ)
    (V := 0) (fun _ _ ↦ analyticAt_const.meromorphicNFAt) 1 hz
  obtain ⟨σ, hσ⟩ := sIdeleQuotientNorm_exists_section F S
  intro c hc
  obtain ⟨z, h⟩ := exists_normTwist_of_agree_on_ker (mₛ(S)) (isProperMap_sIdeleQuotientNorm F S).continuous
    σ hσ ((ιℂ).comp ψ) c.val (fun y ↦ (hc y).trans (hψ y).symm)
  change sLocalIdelicZFunction f c.val = 0
  exact h ▸ congrFun hzero z

/-- A continuous linear bijection of LF-spaces is a homeomorphism, by the LF open
mapping theorem applied to a Fréchet presentation of its source. -/
private theorem closedEmbedding_of_lf_bijective {E Q : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    [AddCommGroup Q] [Module ℂ Q] [TopologicalSpace Q] (hE : IsLFSpace E)
    (hQ : IsLFSpace Q) (j : E →ₗ[ℂ] Q) (hj : Continuous j) (hb : Bijective j) :
    IsClosedEmbedding j := by
  obtain ⟨h₂, X, _, _, _, hX, u, i, h⟩ := hE
  let J : E →L[ℂ] Q := ⟨j, hj⟩
  have ho : IsOpenMap J := isOpenMap_of_surjective_toLF hQ hX i (fun n _ ⟨x, hx⟩ ↦
    ⟨u n x, (DFunLike.congr_fun (h.compatible n) x).trans hx⟩) h.exhaustive J hb.2
  exact ((Equiv.ofBijective j hb).toHomeomorphOfContinuousOpen hj ho).isClosedEmbedding

private theorem homogeneousStage_closedEmbedding (hω : NormOneCharacterUnramifiedOutside (F := F) ω S) :
    IsClosedEmbedding (sLocalHomogeneousThetaToGlobal (F := F) (ω := ω) hω) := by
  have hS : IsLFSpace (Θₛω(S, ωₛ(S, hω))) := lfSpace_quotient_properties.2
    (lfSpace_quotient_properties.1 (sAdeleSchwartz_strictLF F S)) _
    (sLocalHomogeneousAdelicTheta_ker_isClosed _)
  have hF : IsLFSpace Θ𝔽ω(ω) := lfSpace_quotient_properties.2
    (lfSpace_quotient_properties.1 (adeleSchwartz_strictLF (F := F)).2) _
    (homogeneousAdelicTheta_ker_isClosed ω)
  apply closedEmbedding_of_lf_bijective hS hF
  · apply (Kₛω(S, ωₛ(S, hω))).isQuotientMap_mkQ.continuous_iff.mpr
    exact (K𝔽ω(ω)).mkQL.continuous.comp (sAdeleSchwartzToGlobal_isEmbedding F S).continuous
  · exact ⟨homogeneousStage_injective hω, homogeneousStage_surjective hω⟩

end HomogeneousStageTopology

/-- Paper: Theorem 5.2.3.1(1), pp. 233–234.
The stages form a strict system under the transition maps and identify the global
homogeneous space with its locally convex inductive limit.
Deviation: The compatible closed embeddings and exhaustion realize the algebraic
colimit inside the global space. The topology is specified by the final topology. -/
theorem sLocalHomogeneousTheta_inductiveLimit (hω : NormOneCharacterUnramifiedOutside (F := F) ω S) :
    let I := {T : Finset (HeightOneSpectrum (𝓞 F)) // S ⊆ T}
    let h := fun T : I ↦ NormOneCharacterUnramifiedOutside.mono (F := F) (ω := ω) hω T.property
    let i := fun T : I ↦ sLocalHomogeneousThetaToGlobal (F := F) (ω := ω) (h T)
    (∀ T, IsClosedEmbedding (i T)) ∧
    (∀ (T U : I) (hTU : T.val ⊆ U.val),
      (i U).comp (sLocalHomogeneousThetaTransition (F := F) (ω := ω) (h T) hTU) = i T) ∧
    (∀ x : Θ𝔽ω(ω), ∃ T y, i T y = x) ∧
    (inferInstance : TopologicalSpace Θ𝔽ω(ω)) = locallyConvexFinalTopology i := by
  intro I h i
  have he (T : I) : IsClosedEmbedding (i T) := homogeneousStage_closedEmbedding (h T)
  let t : I := ⟨S, Finset.Subset.refl _⟩
  have hs : Surjective (i t) := homogeneousStage_surjective (h t)
  refine ⟨he, fun T U hTU ↦ ?_, fun x ↦ ⟨t, hs x⟩, ?_⟩
  · exact quotientMap_comp _ _ _ _ _ _
      (sLocalHomogeneousThetaTransition_preserves_kernel (h T) hTU)
      (sLocalHomogeneousThetaToGlobal_preserves_kernel (h U))
      (sLocalHomogeneousThetaToGlobal_preserves_kernel (h T)) (sAdeleSchwartzToGlobal_comp F hTU)
  · let : PolynormableSpace ℂ Θ𝔽ω(ω) := polynormableSpace_quotient (K𝔽ω(ω))
    have hq : IsQuotientMap (i t) := (he t).isEmbedding.isInducing.isQuotientMap_of_surjective hs
    have hp : (fun p : Seminorm ℂ Θ𝔽ω(ω) ↦ ∀ T, Continuous (p ∘ i T)) =
        (fun p : Seminorm ℂ Θ𝔽ω(ω) ↦ Continuous p) := by
      funext p
      exact propext ⟨fun hh ↦ hq.continuous_iff.mpr (hh t), fun hh T ↦ hh.comp (he T).continuous⟩
    unfold locallyConvexFinalTopology
    rw [hp]
    exact (PolynormableSpace.withSeminorms ℂ Θ𝔽ω(ω)).withSeminorms_eq

/-- Paper: Theorem 5.2.3.1(1), p. 233.
Each homogeneous stage is embedded as a closed subspace of a larger stage. -/
theorem sLocalHomogeneousThetaTransition_isClosedEmbedding
    (hω : NormOneCharacterUnramifiedOutside (F := F) ω S) (hST : S ⊆ T) :
    IsClosedEmbedding (sLocalHomogeneousThetaTransition (F := F) (ω := ω) hω hST) := by
  let I := {U : Finset (HeightOneSpectrum (𝓞 F)) // S ⊆ U}
  let s : I := ⟨S, Finset.Subset.refl S⟩
  let t : I := ⟨T, hST⟩
  let i (u : I) := sLocalHomogeneousThetaToGlobal (F := F) (ω := ω) (hω.mono u.property)
  have h := sLocalHomogeneousTheta_inductiveLimit (F := F) (S := S) (ω := ω) hω
  have he : IsClosedEmbedding (i t) := h.1 t
  apply he.of_comp_iff.mp
  have hc : (i t) ∘ (sLocalHomogeneousThetaTransition (F := F) (ω := ω) hω hST) = i s :=
    funext (LinearMap.congr_fun (h.2.1 s t hST))
  rw [hc]
  exact h.1 s

/-- Paper: Theorem 5.2.3.1(2), p. 233.
A Hausdorff space admits a countable locally convex inductive presentation whose
stages, with their own topologies, are nuclear Fréchet spaces. -/
def HasNuclearFrechetPresentation.{v,u} (E : Type u) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] : Prop :=
  T2Space E ∧ ∃ (X : ℕ → Type u) (_ : ∀ k, AddCommGroup (X k)) (_ : ∀ k, Module ℂ (X k))
    (_ : ∀ k, TopologicalSpace (X k)), (∀ k, IsFrechetTVS (X k) ∧ IsNuclearTVS.{v} (X k)) ∧
      ∃ (j : ∀ k, X k →L[ℂ] X (k+1)) (i : ∀ k, X k →L[ℂ] E), IsInjectiveLCLimit j i

/-- Paper: Theorem 5.2.3.1(2), p. 233.
A countable nuclear Fréchet presentation gives an LF presentation. -/
theorem HasNuclearFrechetPresentation.isLFSpace {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (h : HasNuclearFrechetPresentation E) : IsLFSpace E := by
  obtain ⟨hE, X, a, m, t, hX, hlim⟩ := h
  exact ⟨hE, X, a, m, t, fun k ↦ (hX k).1, hlim⟩

private theorem nuclearFrechetPresentation_quotient_of_strictLF.{v,u}
    {E : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (hs : IsStrictLFSpace E) (hn : IsNuclearTVS.{v} E)
    (M : Submodule ℂ E) (hM : IsClosed (M : Set E)) :
    HasNuclearFrechetPresentation.{v} (E ⧸ M) := by
  obtain ⟨_, V, hV, hF, hex, ht⟩ := hs
  have hN (k : ℕ) : IsNuclearTVS.{v} (V k) := isNuclearTVS_submodule hn (V k)
  let j (k : ℕ) := (V k).subtypeL.codRestrict (V (k+1)) fun x ↦ hV k.le_succ x.property
  let i (k : ℕ) := (V k).subtypeL
  have h : IsInjectiveLCLimit j i := by
    refine ⟨fun _ ↦ Subtype.val_injective, fun _ ↦ rfl, ?_, ht⟩
    intro x
    obtain ⟨k, hk⟩ := hex x
    exact ⟨k, ⟨x, hk⟩, rfl⟩
  have hP : WithSeminorms
      (Subtype.val : {p : Seminorm ℂ E // ∀ k, Continuous (p ∘ (i k).toLinearMap)} →
        Seminorm ℂ E) := ⟨h.topology_eq⟩
  let : IsTopologicalAddGroup E := hP.isTopologicalAddGroup
  let : T2Space (E ⧸ M) := inferInstance
  let f (k : ℕ) := M.mkQL.comp (i k)
  let K (k : ℕ) := (f k).ker
  have hf (k : ℕ) (x : V k) : f (k+1) (j k x) = f k x :=
    congrArg M.mkQ (DFunLike.congr_fun (h.compatible k) x)
  let iQ (k : ℕ) : V k ⧸ K k →L[ℂ] E ⧸ M := (K k).liftQL (f k) le_rfl
  let jQ (k : ℕ) : V k ⧸ K k →L[ℂ] V (k+1) ⧸ K (k+1) :=
    (K k).liftQL ((K (k+1)).mkQL.comp (j k)) (by
      intro x hx
      change (K (k+1)).mkQ (j k x) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      change f (k+1) (j k x) = 0
      rwa [hf])
  have hiQ (k : ℕ) (x : V k) : iQ k ((K k).mkQ x) = f k x := rfl
  have hjQ (k : ℕ) (x : V k) : jQ k ((K k).mkQ x) = (K (k+1)).mkQ (j k x) := rfl
  refine ⟨inferInstance, fun k ↦ V k ⧸ K k, _, _, _, fun k ↦
    ⟨isFrechetTVS_quotient (hF k) (K k) (f k).isClosed_ker, by
      let : IsClosed (K k : Set (V k)) := (f k).isClosed_ker
      exact isNuclearTVS_quotient (hN k) (K k)⟩, jQ, iQ, ⟨?_, ?_, ?_, ?_⟩⟩
  · intro k
    apply (LinearMap.ker_eq_bot (f := (iQ k).toLinearMap)).mp
    exact (K k).ker_liftQ_eq_bot' (f k).toLinearMap rfl
  · intro k
    ext y
    obtain ⟨x, rfl⟩ := (K k).mkQ_surjective y
    change iQ (k+1) (jQ k ((K k).mkQ x)) = iQ k ((K k).mkQ x)
    rw [hjQ, hiQ, hiQ, hf]
  · intro y
    obtain ⟨x, rfl⟩ := M.mkQ_surjective y
    obtain ⟨k, z, rfl⟩ := h.exhaustive x
    exact ⟨k, (K k).mkQ z, hiQ k z⟩
  · let : PolynormableSpace ℂ E := hP.toPolynormableSpace
    let : PolynormableSpace ℂ (E ⧸ M) := (isNuclearTVS_quotient hn M).2.1
    have hseminorms : (fun p : Seminorm ℂ (E ⧸ M) ↦
        ∀ k, Continuous (p ∘ (iQ k).toLinearMap)) =
        (fun p : Seminorm ℂ (E ⧸ M) ↦ Continuous p) := by
      funext p
      apply propext
      refine ⟨fun hp ↦ M.isQuotientMap_mkQL.continuous_iff.mpr ?_,
        fun hp k ↦ hp.comp (iQ k).continuous⟩
      apply hP.continuous_seminorm (⟨p.comp M.mkQ, fun k ↦ ?_⟩ : _)
      change Continuous (fun x : V k ↦ p (f k x))
      simpa only [Function.comp_def, ContinuousLinearMap.coe_coe, Submodule.coe_mkQL, hiQ] using
        (hp k).comp (K k).mkQL.continuous
    change (inferInstance : TopologicalSpace (E ⧸ M)) =
      (SeminormFamily.moduleFilterBasis
        (Subtype.val : {p : Seminorm ℂ (E ⧸ M) // ∀ k, Continuous (p ∘ (iQ k).toLinearMap)} →
          Seminorm ℂ (E ⧸ M))).topology
    rw [hseminorms]
    exact (PolynormableSpace.withSeminorms ℂ (E ⧸ M)).withSeminorms_eq

/-- Paper: Theorem 5.2.3.1(2), p. 233.
The global homogeneous theta quotient is a locally convex inductive limit of nuclear
Fréchet spaces. The test-function stages can be quotiented by the restricted kernel. -/
theorem globalHomogeneousThetaSpace_nuclearFrechetPresentation :
    HasNuclearFrechetPresentation Θ𝔽ω(ω) := by
  apply nuclearFrechetPresentation_quotient_of_strictLF
  · exact (adeleSchwartz_strictLF (F := F)).2
  · exact (adeleSchwartz_nuclear (F := F)).2
  · exact homogeneousAdelicTheta_ker_isClosed ω

/-- A closed quotient of a nuclear strict LF-space has nuclear Fréchet quotient stages. -/
private theorem sLocalHomogeneousThetaSpace_nuclearFrechetPresentation_quotient.{v}
    {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] (M : Submodule ℂ E)
    (hM : IsClosed (M : Set E)) (hE : IsStrictLFSpace E) (hN : IsNuclearTVS.{v} E) :
    HasNuclearFrechetPresentation.{v} (E ⧸ M) := by
  obtain ⟨_, X, hmono, hFrechet, hcover, htop⟩ := hE
  let : T2Space (E ⧸ M) := inferInstance
  let i (k : ℕ) : X k →L[ℂ] E := (X k).subtypeL
  let j (k : ℕ) : X k →L[ℂ] X (k+1) :=
    (X k).subtypeL.codRestrict (X (k+1)) fun x ↦ hmono k.le_succ x.property
  have h : IsInjectiveLCLimit j i :=
    ⟨fun _ ↦ Subtype.val_injective, fun _ ↦ rfl, fun x ↦ by
      obtain ⟨k, hk⟩ := hcover x
      exact ⟨k, ⟨⟨x, hk⟩, rfl⟩⟩, htop⟩
  have hNstage (k : ℕ) : IsNuclearTVS (X k) := isNuclearTVS_submodule hN (X k)
  let f (k : ℕ) := M.mkQL.comp (i k)
  let K (k : ℕ) := (f k).ker
  have hf (k : ℕ) (x : X k) : f (k+1) (j k x) = f k x :=
    congrArg M.mkQ (DFunLike.congr_fun (h.compatible k) x)
  let iQ (k : ℕ) : X k ⧸ K k →L[ℂ] E ⧸ M := (K k).liftQL (f k) le_rfl
  let jQ (k : ℕ) : X k ⧸ K k →L[ℂ] X (k+1) ⧸ K (k+1) :=
    (K k).liftQL ((K (k+1)).mkQL.comp (j k)) (by
      intro x hx
      change (K (k+1)).mkQ (j k x) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      change f (k+1) (j k x) = 0
      rwa [hf])
  have hiQ (k : ℕ) (x : X k) : iQ k ((K k).mkQ x) = f k x := rfl
  have hjQ (k : ℕ) (x : X k) : jQ k ((K k).mkQ x) = (K (k+1)).mkQ (j k x) := rfl
  have hP : WithSeminorms
      (Subtype.val : {p : Seminorm ℂ E // ∀ k, Continuous (p ∘ (i k).toLinearMap)} →
        Seminorm ℂ E) := ⟨h.topology_eq⟩
  have hlim : IsInjectiveLCLimit jQ iQ := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro k
      apply (LinearMap.ker_eq_bot (f := (iQ k).toLinearMap)).mp
      exact (K k).ker_liftQ_eq_bot' (f k).toLinearMap rfl
    · intro k
      ext y
      obtain ⟨x, rfl⟩ := (K k).mkQ_surjective y
      change iQ (k+1) (jQ k ((K k).mkQ x)) = iQ k ((K k).mkQ x)
      rw [hjQ, hiQ, hiQ, hf]
    · intro y
      obtain ⟨x, rfl⟩ := M.mkQ_surjective y
      obtain ⟨k, z, rfl⟩ := h.exhaustive x
      exact ⟨k, (K k).mkQ z, hiQ k z⟩
    · let : PolynormableSpace ℂ E := hP.toPolynormableSpace
      let : PolynormableSpace ℂ (E ⧸ M) := (isNuclearTVS_quotient hN M).2.1
      have hseminorms : (fun p : Seminorm ℂ (E ⧸ M) ↦
          ∀ k, Continuous (p ∘ (iQ k).toLinearMap)) =
          (fun p : Seminorm ℂ (E ⧸ M) ↦ Continuous p) := by
        funext p
        apply propext
        refine ⟨fun hp ↦ M.isQuotientMap_mkQL.continuous_iff.mpr ?_,
          fun hp k ↦ hp.comp (iQ k).continuous⟩
        apply hP.continuous_seminorm (⟨p.comp M.mkQ, fun k ↦ ?_⟩ : _)
        change Continuous (fun x : X k ↦ p (f k x))
        simpa only [Function.comp_def, ContinuousLinearMap.coe_coe, Submodule.coe_mkQL, hiQ] using
          (hp k).comp (K k).mkQL.continuous
      change (inferInstance : TopologicalSpace (E ⧸ M)) =
        (SeminormFamily.moduleFilterBasis
          (Subtype.val : {p : Seminorm ℂ (E ⧸ M) // ∀ k, Continuous (p ∘ (iQ k).toLinearMap)} →
            Seminorm ℂ (E ⧸ M))).topology
      rw [hseminorms]
      exact (PolynormableSpace.withSeminorms ℂ (E ⧸ M)).withSeminorms_eq
  have : T2Space (E ⧸ M) := inferInstance
  refine ⟨inferInstance, fun k ↦ X k ⧸ K k, _, _, _, ?_, jQ, iQ, hlim⟩
  intro k
  have : IsClosed (K k : Set (X k)) := (f k).isClosed_ker
  let : IsTopologicalAddGroup (X k) := (hFrechet k).1
  let : T2Space (X k ⧸ K k) := inferInstance
  exact ⟨isFrechetTVS_quotient (hFrechet k) (K k) (f k).isClosed_ker,
    isNuclearTVS_quotient (hNstage k) (K k)⟩

/-- Paper: Theorem 5.2.3.1(2), p. 233.
The S-local homogeneous theta quotient is a locally convex inductive limit of nuclear
Fréchet spaces. The test-function stages can be quotiented by the restricted kernel. -/
theorem sLocalHomogeneousThetaSpace_nuclearFrechetPresentation (χ : PontryaginDual (J₁(S))) :
    HasNuclearFrechetPresentation (Θₛω(S, χ)) := by
  exact sLocalHomogeneousThetaSpace_nuclearFrechetPresentation_quotient _
    (sLocalHomogeneousAdelicTheta_ker_isClosed χ) (sAdeleSchwartz_strictLF F S)
    (sAdeleSchwartz_nuclear F S)

/-- Paper: Theorem 5.2.3.1(2), p. 233.
The global homogeneous theta space is an LF-space. -/
theorem globalHomogeneousThetaSpace_lf : IsLFSpace Θ𝔽ω(ω) := by
  have h : HasNuclearFrechetPresentation.{0} Θ𝔽ω(ω) :=
    globalHomogeneousThetaSpace_nuclearFrechetPresentation
  exact h.isLFSpace

/-- Paper: Theorem 5.2.3.1(2), p. 233.
The S-local homogeneous theta space is an LF-space. -/
theorem sLocalHomogeneousThetaSpace_lf (χ : PontryaginDual (J₁(S))) :
    IsLFSpace (Θₛω(S, χ)) := by
  have h : HasNuclearFrechetPresentation.{0} (Θₛω(S, χ)) :=
    sLocalHomogeneousThetaSpace_nuclearFrechetPresentation χ
  exact h.isLFSpace

private theorem globalHomogeneousThetaSpace_complete_coinvariants {G E : Type*}
    [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [T2Space E] [ContinuousSMul ℂ E] [PolynormableSpace ℂ E]
    (hE : @CompleteSpace E (IsTopologicalAddGroup.rightUniformSpace E))
    (μ : Measure G) [μ.IsHaarMeasure] (ρ : G →* (E →L[ℂ] E))
    (hρ : Continuous fun p : G × E ↦ ρ p.1 p.2) (ω : PontryaginDual G) :
    @CompleteSpace (E ⧸ (Submodule.span ℂ (Set.range (fun p : G × E ↦
      p.2 - star (ω p.1 : ℂ) • ρ p.1 p.2))).topologicalClosure)
      (IsTopologicalAddGroup.rightUniformSpace _) := by
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  let : CompleteSpace E := hE
  let : Module ℝ E := Module.restrictScalars ℝ ℂ E
  let : IsScalarTower ℝ ℂ E := IsScalarTower.restrictScalars ℝ ℂ E
  let : LocallyConvexSpace ℝ E := (PolynormableSpace.withSeminorms ℂ E).toLocallyConvexSpace
  let : SeparatingDual ℂ E := locallyConvexSpace_separatingDual ℂ E
  let A (g : G) := star (ω g : ℂ) • ρ g
  have hA : Continuous (fun p : G × E ↦ A p.1 p.2) :=
    (show Continuous (fun p : G × E ↦ star (ω p.1 : ℂ)) from by fun_prop).smul hρ
  obtain ⟨P, hP, _⟩ := existsUnique_pettisIntegral_continuousFamily μ isCompact_univ
    (ae_of_all _ fun _ ↦ Set.mem_univ _) A hA
  have hav : IsPettisIsotypicAverageOn μ Set.univ ρ ω P := by
    simpa [IsPettisIsotypicAverageOn, A] using hP
  have hk := compactActionAverage_ker μ ρ hρ ω P hav
  obtain ⟨e, _⟩ := compactActionAverage_quotient_equiv μ ρ hρ ω P hav
  let : IsUniformAddGroup (actionIsotype ρ ω) := IsUniformAddGroup.comap (actionIsotype ρ ω).subtype
  have hc : CompleteSpace (actionIsotype ρ ω) :=
    completeSpace_coe_iff_isComplete.mpr (isClosed_actionIsotype ρ ω).isComplete
  rw [← hk]
  let : UniformSpace (E ⧸ P.ker) := IsTopologicalAddGroup.rightUniformSpace _
  let : IsUniformAddGroup (E ⧸ P.ker) := isUniformAddGroup_of_addCommGroup
  exact (completeSpace_congr (e := e.toEquiv) e.isUniformEmbedding).2 hc

private theorem globalHomogeneousThetaSpace_complete_subgroup {H E : Type*}
    [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H]
    (N : Subgroup H) [CompactSpace N] [T2Space N] [MeasurableSpace N] [BorelSpace N]
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [T2Space E] [ContinuousSMul ℂ E] [PolynormableSpace ℂ E]
    (hE : @CompleteSpace E (IsTopologicalAddGroup.rightUniformSpace E))
    (μ : Measure N) [μ.IsHaarMeasure] (ρ : H →* (E →L[ℂ] E))
    (hρ : Continuous fun p : N × E ↦ ρ p.1.val p.2) (ω : PontryaginDual N) :
    @CompleteSpace (E ⧸ (Submodule.span ℂ (Set.range (fun p : N × E ↦
      p.2 - star (ω p.1 : ℂ) • ρ p.1.val p.2))).topologicalClosure)
      (IsTopologicalAddGroup.rightUniformSpace _) := by
  exact globalHomogeneousThetaSpace_complete_coinvariants hE μ (ρ.comp N.subtype) hρ ω

private theorem globalHomogeneousThetaSpace_complete_transfer {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    [IsTopologicalAddGroup Y] (e : X ≃L[ℂ] Y)
    (h : @CompleteSpace Y (IsTopologicalAddGroup.rightUniformSpace Y)) :
    @CompleteSpace X (IsTopologicalAddGroup.rightUniformSpace X) := by
  let : UniformSpace X := IsTopologicalAddGroup.rightUniformSpace X
  let : IsUniformAddGroup X := isUniformAddGroup_of_addCommGroup
  let : UniformSpace Y := IsTopologicalAddGroup.rightUniformSpace Y
  let : IsUniformAddGroup Y := isUniformAddGroup_of_addCommGroup
  exact (completeSpace_congr (e := e.toEquiv) e.isUniformEmbedding).2 h

/-- Paper: Theorem 5.2.3.1(2), p. 233.
The global homogeneous quotient is complete for its additive uniformity. -/
theorem globalHomogeneousThetaSpace_complete :
    @CompleteSpace Θ𝔽ω(ω) (IsTopologicalAddGroup.rightUniformSpace _) := by
  let E := GlobalAdelicThetaSpace F
  let G := (ideleClassNorm F).ker
  let : T2Space E := globalAdelicThetaSpace_t2_of_isClosed (F := F) (adelicTheta_ker_isClosed (F := F))
  let : PolynormableSpace ℂ E := globalAdelicThetaSpace_polynormable (F := F)
  let : T2Space G := (ideleClassGroup_finiteness F).2.2.1
  let : CompactSpace G := (ideleClassGroup_finiteness F).2.1
  let : MeasurableSpace (IdeleClassGroup (𝓞 F) F) := borel _
  let : BorelSpace (IdeleClassGroup (𝓞 F) F) := ⟨rfl⟩
  let μ := normOneIdeleClassTamagawaMeasure F
  let : μ.IsHaarMeasure := (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  let ρ : IdeleClassGroup (𝓞 F) F →* (E →L[ℂ] E) := (existsUnique_globalThetaAction (F := F)).exists.choose
  let σ : G →* (E →L[ℂ] E) := ρ.comp G.subtype
  have hσ : Continuous (fun p : G × E ↦ σ p.1 p.2) :=
    (existsUnique_globalThetaAction (F := F)).exists.choose_spec.1.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hq := globalHomogeneousThetaSpace_complete_subgroup G
    (globalAdelicThetaSpace_complete (F := F)) μ ρ hσ ω
  have he := (globalHomogeneousThetaSpace_equiv_coinvariants (F := F) ω).choose
  with_reducible_and_instances
    exact globalHomogeneousThetaSpace_complete_transfer he hq

/-- Paper: Theorem 5.2.3.1(2), p. 233.
The S-local homogeneous quotient is complete for its additive uniformity. -/
theorem sLocalHomogeneousThetaSpace_complete (χ : PontryaginDual (J₁(S))) :
    @CompleteSpace (Θₛω(S, χ)) (IsTopologicalAddGroup.rightUniformSpace _) := by
  let E := SLocalAdelicThetaSpace F S
  let G := J₁(S)
  have := isClosed_sProjectedDiagonal (F := F) (S := S)
  let : T2Space (Jₛ(S)) := inferInstanceAs (T2Space (_ ⧸ _))
  let : T2Space G := inferInstanceAs (T2Space ((sIdeleQuotientNorm F S).ker : Set (Jₛ(S))))
  let : MeasurableSpace G := borel _
  let : BorelSpace G := ⟨rfl⟩
  let : CompactSpace G := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage (isCompact_singleton (x := 1)))
  let : T2Space E := sLocalAdelicThetaSpace_t2_of_isClosed (F := F) (S := S)
    (sLocalAdelicTheta_ker_isClosed (F := F) (S := S))
  let : PolynormableSpace ℂ E := sLocalAdelicThetaSpace_polynormable (F := F) (S := S)
  let μ := sLocalNormOneQuotientMeasure F S
  have : μ.IsHaarMeasure := (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1
  let ρ := (existsUnique_sLocalThetaAction (F := F) (S := S)).exists.choose
  have hσ : Continuous (fun p : G × E ↦ ρ p.1.val p.2) :=
    (existsUnique_sLocalThetaAction (F := F) (S := S)).exists.choose_spec.1.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hq := globalHomogeneousThetaSpace_complete_subgroup G
    (sLocalAdelicThetaSpace_complete (F := F) (S := S)) μ ρ hσ χ
  have he := (sLocalHomogeneousThetaSpace_equiv_coinvariants (F := F) (S := S) χ).choose
  with_reducible_and_instances
    exact globalHomogeneousThetaSpace_complete_transfer he hq

/-- Paper: Theorem 5.2.3.1(2), p. 233.
The global homogeneous quotient is nuclear. -/
theorem globalHomogeneousThetaSpace_nuclear : IsNuclearTVS Θ𝔽ω(ω) := by
  have : IsClosed (K𝔽ω(ω) : Set ℬ𝔽) := homogeneousAdelicTheta_ker_isClosed ω
  let : T2Space Θ𝔽ω(ω) := inferInstance
  exact isNuclearTVS_quotient (adeleSchwartz_nuclear (F := F)).2 (K𝔽ω(ω))

/-- Paper: Theorem 5.2.3.1(2), p. 233.
The S-local homogeneous quotient is nuclear. -/
theorem sLocalHomogeneousThetaSpace_nuclear (χ : PontryaginDual (J₁(S))) :
    IsNuclearTVS (Θₛω(S, χ)) := by
  have : IsClosed (Kₛω(S, χ) : Set (SchwartzBruhat (Multiplicative (SAdeleRing F S)))) :=
    sLocalHomogeneousAdelicTheta_ker_isClosed χ
  let : T2Space (Θₛω(S, χ)) := inferInstance
  exact isNuclearTVS_quotient (sAdeleSchwartz_nuclear F S) (Kₛω(S, χ))

/-- Paper: Theorem 5.2.3.1(2), p. 233.
The global homogeneous quotient is Montel. -/
theorem globalHomogeneousThetaSpace_montel :
    BarrelledSpace ℂ Θ𝔽ω(ω) ∧ MontelSpace ℂ Θ𝔽ω(ω) := by
  have hN : IsNuclearTVS.{0} Θ𝔽ω(ω) := globalHomogeneousThetaSpace_nuclear (F := F) (ω := ω)
  let : T2Space Θ𝔽ω(ω) := hN.1
  let : PolynormableSpace ℂ Θ𝔽ω(ω) := hN.2.1
  let : UniformSpace Θ𝔽ω(ω) := IsTopologicalAddGroup.rightUniformSpace _
  let : IsUniformAddGroup Θ𝔽ω(ω) := isUniformAddGroup_of_addCommGroup
  let : CompleteSpace Θ𝔽ω(ω) := globalHomogeneousThetaSpace_complete (F := F) (ω := ω)
  refine ⟨IsLFSpace.barrelled (E := Θ𝔽ω(ω)) (globalHomogeneousThetaSpace_lf (F := F) (ω := ω)), ⟨fun B hc hb ↦ ?_⟩⟩
  simpa only [hc.closure_eq] using isCompact_closure_of_isNuclearTVS Θ𝔽ω(ω) hN hb

/-- Paper: Theorem 5.2.3.1(2), p. 233.
The S-local homogeneous quotient is Montel. -/
theorem sLocalHomogeneousThetaSpace_montel (χ : PontryaginDual (J₁(S))) :
    BarrelledSpace ℂ (Θₛω(S, χ)) ∧ MontelSpace ℂ (Θₛω(S, χ)) := by
  have hN : IsNuclearTVS.{0} (Θₛω(S, χ)) := sLocalHomogeneousThetaSpace_nuclear (F := F) (S := S) χ
  let : T2Space (Θₛω(S, χ)) := hN.1
  let : PolynormableSpace ℂ (Θₛω(S, χ)) := hN.2.1
  let : UniformSpace (Θₛω(S, χ)) := IsTopologicalAddGroup.rightUniformSpace _
  let : IsUniformAddGroup (Θₛω(S, χ)) := isUniformAddGroup_of_addCommGroup
  let : CompleteSpace (Θₛω(S, χ)) := sLocalHomogeneousThetaSpace_complete (F := F) (S := S) χ
  refine ⟨IsLFSpace.barrelled (E := (Θₛω(S, χ))) (sLocalHomogeneousThetaSpace_lf (F := F) (S := S) χ), ⟨fun B hc hb ↦ ?_⟩⟩
  simpa only [hc.closure_eq] using isCompact_closure_of_isNuclearTVS (Θₛω(S, χ)) hN hb

/-- Paper: Theorem 5.2.3.1(2), p. 233.
The strong dual of the global homogeneous quotient is complete. -/
theorem globalHomogeneousThetaSpace_strongDual_complete :
    CompleteSpace (StrongDual ℂ Θ𝔽ω(ω)) := by
  let : CompleteSpace (StrongDual ℂ (SchwartzBruhat (Multiplicative (𝔸[F])))) :=
    (adeleSchwartz_strongDual_complete (F := F)).2
  exact completeSpace_strongDual_quotient _

/-- Paper: Theorem 5.2.3.1(2), p. 233.
The strong dual of the S-local homogeneous quotient is complete. -/
theorem sLocalHomogeneousThetaSpace_strongDual_complete (χ : PontryaginDual (J₁(S))) :
    CompleteSpace (StrongDual ℂ (Θₛω(S, χ))) := by
  let : CompleteSpace (StrongDual ℂ (SchwartzBruhat (Multiplicative (SAdeleRing F S)))) :=
    sAdeleSchwartz_strongDual_complete F S
  exact completeSpace_strongDual_quotient _

private theorem sLocalHomogeneousThetaSpace_strongDual_montel_aux {E : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℂ E] [T2Space E] [PolynormableSpace ℂ E]
    [BarrelledSpace ℂ E] [MontelSpace ℂ E] :
    BarrelledSpace ℂ (StrongDual ℂ E) ∧ MontelSpace ℂ (StrongDual ℂ E) := by
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace _
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  constructor
  · apply barrelled_of_barrel_nbhd
    apply strongDual_barrel_nbhd
    intro l
    obtain ⟨x, rfl⟩ := surjective_strongBidual_eval l
    exact ⟨x, fun _ ↦ rfl⟩
  · exact montelSpace_strongDual

/-- Paper: Theorem 5.2.3.1(2), p. 233.
The strong dual of the S-local homogeneous quotient is Montel. -/
theorem sLocalHomogeneousThetaSpace_strongDual_montel (χ : PontryaginDual (J₁(S))) :
    BarrelledSpace ℂ (StrongDual ℂ (Θₛω(S, χ))) ∧ MontelSpace ℂ (StrongDual ℂ (Θₛω(S, χ))) := by
  let : T2Space (Θₛω(S, χ)) := (sLocalHomogeneousThetaSpace_lf χ).1
  have hn : IsNuclearTVS.{0} (Θₛω(S, χ)) := sLocalHomogeneousThetaSpace_nuclear χ
  let : PolynormableSpace ℂ (Θₛω(S, χ)) := hn.2.1
  let : BarrelledSpace ℂ (Θₛω(S, χ)) := (sLocalHomogeneousThetaSpace_montel χ).1
  let : MontelSpace ℂ (Θₛω(S, χ)) := (sLocalHomogeneousThetaSpace_montel χ).2
  exact sLocalHomogeneousThetaSpace_strongDual_montel_aux

/-- Paper: Theorem 5.2.3.1(3), p. 233.
There are continuous idempotents onto the stage images. The net of these idempotents
converges to the identity uniformly on von Neumann bounded sets. -/
theorem sLocalHomogeneousTheta_projections (hω : NormOneCharacterUnramifiedOutside (F := F) ω S) :
    let I := {T : Finset (HeightOneSpectrum (𝓞 F)) // S ⊆ T}
    let E := Θ𝔽ω(ω)
    let e := UniformConvergenceCLM.ofFun (σ := RingHom.id ℂ) (F := E)
      {B : Set E | IsVonNBounded ℂ B}
    ∃ P : I → E →L[ℂ] E,
      (∀ T : I,
        let hT := NormOneCharacterUnramifiedOutside.mono (F := F) (ω := ω) hω T.property
        let i := sLocalHomogeneousThetaToGlobal (F := F) (ω := ω) hT
        (P T).toLinearMap.comp i = i ∧ LinearMap.range (P T).toLinearMap = LinearMap.range i) ∧
      Tendsto (fun T ↦ e (P T)) atTop (𝓝 (e (ContinuousLinearMap.id ℂ E))) := by
  intro I E e
  refine ⟨fun _ ↦ ContinuousLinearMap.id ℂ E, fun T ↦ ⟨rfl, ?_⟩, tendsto_const_nhds⟩
  exact LinearMap.range_id.trans (LinearMap.range_eq_top.mpr (homogeneousStage_surjective
    (NormOneCharacterUnramifiedOutside.mono (F := F) (ω := ω) hω T.property))).symm

end StructureTheorem

local notation "ρ𝔽" => (existsUnique_globalThetaAction (F := F)).exists.choose
local notation "ρₛ(" S ")" => (existsUnique_sLocalThetaAction (F := F) (S := S)).exists.choose
local notation "ρ𝔽₁" => (ρ𝔽).comp (MonoidHom.ker m𝔽).subtype
local notation "ρₛ₁(" S ")" => (ρₛ(S)).comp (MonoidHom.ker (mₛ(S))).subtype
local notation "E𝔽ω(" ω ")" => actionIsotype ρ𝔽₁ ω
local notation "Eₛω(" S ", " ω ")" => actionIsotype (ρₛ₁(S)) ω

local notation "μ𝔽₁" => normOneIdeleClassTamagawaMeasure F
local notation "μₛ₁(" S ")" => sLocalNormOneQuotientMeasure F S

section IsotypicAverages

local instance ideleClassGroupMeasurableSpaceSec2b (F : Type*) [Field F] [NumberField F] :
    MeasurableSpace (IdeleClassGroup (𝓞 F) F) := borel _

local instance normOneSIdeleQuotientMeasurableSpaceSec2b (F : Type*) [Field F]
    [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) :
    MeasurableSpace (MonoidHom.ker (sIdeleQuotientNorm F S)) := borel _

-- TODO(paper-gap): The proof on pp. 236–237 gives no quotient-topology argument for
-- equicontinuity. Use the jointly continuous action on the theta quotient and compactness.
-- The Tamagawa averages act on their isotypes by Haar mass.

/-- On a compact group the character twist is itself a jointly continuous action,
and compactness makes its operators equicontinuous at zero. -/
theorem existsUnique_globalThetaIsotypicAverage_of_compact {H E : Type*}
    [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] (G : Subgroup H)
    [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [T2Space E] [ContinuousSMul ℂ E] [PolynormableSpace ℂ E]
    (hc : @CompleteSpace E (IsTopologicalAddGroup.rightUniformSpace E))
    (μ : Measure G) [μ.IsHaarMeasure] (ρ : H →* (E →L[ℂ] E))
    (hρ : Continuous fun p : H × E ↦ ρ p.1 p.2) (ω : PontryaginDual G) :
    ∃! P : E →L[ℂ] E, IsPettisIsotypicAverageOn μ Set.univ (ρ.comp G.subtype) ω P := by
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  let : CompleteSpace E := hc
  let : Module ℝ E := Module.restrictScalars ℝ ℂ E
  let : IsScalarTower ℝ ℂ E := IsScalarTower.restrictScalars ℝ ℂ E
  let : LocallyConvexSpace ℝ E := (PolynormableSpace.withSeminorms ℂ E).toLocallyConvexSpace
  let τ : G →* (E →L[ℂ] E) :=
    { toFun := fun g ↦ star (ω g : ℂ) • (ρ.comp G.subtype) g
      map_one' := by simp
      map_mul' := fun g h ↦ by simp only [map_mul, Circle.coe_mul, star_mul', smul_mul_smul_comm] }
  have hτ : Continuous (fun p : G × E ↦ τ p.1 p.2) :=
    (show Continuous (fun p : G × E ↦ star (ω p.1 : ℂ)) from by fun_prop).smul
      (hρ.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd))
  have heq : EquicontinuousAt (fun g : G ↦ (τ g : E → E)) 0 := by
    intro U hU
    obtain ⟨W, hW, h⟩ := (isCompact_univ (X := G)).mem_uniformity_of_prod
      (f := fun x g ↦ τ g x) (s := Set.univ) (q := (0 : E))
      (hτ.comp continuous_swap).continuousOn (Set.mem_univ _) (symm_le_uniformity hU)
    rw [nhdsWithin_univ] at hW
    exact Filter.mem_of_superset hW fun x hx g ↦ h x hx g (Set.mem_univ g)
  have hτ_apply (g : G) (x : E) : τ g x = star (ω g : ℂ) • (ρ.comp G.subtype) g x := rfl
  simpa only [IsPettisIsotypicAverageOn, PontryaginDual.one_apply, Circle.coe_one,
    star_one, one_smul, hτ_apply] using existsUnique_compactActionAverage μ τ hτ (Or.inl heq)

/-- Paper: Proposition 5.2.3.2(1), p. 236.
There is a unique continuous linear global Pettis average with the norm-one
Tamagawa measure and the conjugate character weight. -/
theorem existsUnique_globalThetaIsotypicAverage (ω : PontryaginDual C₁) :
    ∃! P : Θ𝔽 →L[ℂ] Θ𝔽,
      IsPettisIsotypicAverageOn μ𝔽₁ Set.univ ρ𝔽₁ ω P := by
  let : BorelSpace C𝔽 := ⟨rfl⟩
  let : T2Space C₁ := (ideleClassGroup_finiteness F).2.2.1
  let : CompactSpace C₁ := (ideleClassGroup_finiteness F).2.1
  let : (μ𝔽₁).IsHaarMeasure :=
    (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  let : T2Space Θ𝔽 := globalAdelicThetaSpace_t2_of_isClosed (adelicTheta_ker_isClosed (F := F))
  let : PolynormableSpace ℂ Θ𝔽 := globalAdelicThetaSpace_polynormable (F := F)
  with_reducible_and_instances
    exact existsUnique_globalThetaIsotypicAverage_of_compact (H := C𝔽) (E := Θ𝔽) (ideleClassNorm F).ker
      (globalAdelicThetaSpace_complete (F := F)) μ𝔽₁ ρ𝔽
      (existsUnique_globalThetaAction (F := F)).exists.choose_spec.1 ω

/-- Paper: Proposition 5.2.3.2(1), p. 236.
There is a unique continuous linear S-local Pettis average with the norm-one
quotient measure and the conjugate character weight. -/
theorem existsUnique_sLocalThetaIsotypicAverage (χ : PontryaginDual (J₁(S))) :
    ∃! P : Θₛ(S) →L[ℂ] Θₛ(S),
      IsPettisIsotypicAverageOn (μₛ₁(S)) Set.univ (ρₛ₁(S)) χ P := by
  let E := SLocalAdelicThetaSpace F S
  let G := J₁(S)
  have := isClosed_sProjectedDiagonal (F := F) (S := S)
  let : T2Space (Jₛ(S)) := inferInstanceAs (T2Space (_ ⧸ _))
  let : T2Space G := inferInstanceAs (T2Space ((sIdeleQuotientNorm F S).ker : Set (Jₛ(S))))
  let : BorelSpace G := ⟨rfl⟩
  let : CompactSpace G := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage (isCompact_singleton (x := 1)))
  let : T2Space E := sLocalAdelicThetaSpace_t2_of_isClosed (F := F) (S := S)
    (sLocalAdelicTheta_ker_isClosed (F := F) (S := S))
  let : PolynormableSpace ℂ E := sLocalAdelicThetaSpace_polynormable (F := F) (S := S)
  let : (μₛ₁(S)).IsHaarMeasure := (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1
  with_reducible_and_instances
    exact existsUnique_globalThetaIsotypicAverage_of_compact (H := Jₛ(S)) (E := E) G
      (sLocalAdelicThetaSpace_complete (F := F) (S := S)) (μₛ₁(S)) (ρₛ(S))
      (existsUnique_sLocalThetaAction (F := F) (S := S)).exists.choose_spec.1 χ

end IsotypicAverages

local notation "P𝔽(" ω ")" => (existsUnique_globalThetaIsotypicAverage (F := F) ω).exists.choose
local notation "Pₛ(" S ", " χ ")" =>
  (existsUnique_sLocalThetaIsotypicAverage (F := F) (S := S) χ).exists.choose

/-- A normalized character average splits the inclusion of its isotype. Transposing
the splitting realizes the strong dual of any equivalent space inside the ambient strong dual. -/
private theorem strongDual_nuclear_of_compact_isotype.{test} {G E Q : Type*}
    [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G] [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [T2Space E] [ContinuousSMul ℂ E] [LocallyConvexSpace ℝ E]
    [AddCommGroup Q] [Module ℂ Q] [TopologicalSpace Q]
    (μ : Measure G) [μ.IsHaarMeasure] (ρ : G →* (E →L[ℂ] E))
    (ω : PontryaginDual G) (P : E →L[ℂ] E) (hP : IsPettisIsotypicAverageOn μ Set.univ ρ ω P)
    (e : Q ≃L[ℂ] actionIsotype ρ ω) (hE : IsNuclearTVS.{test} (StrongDual ℂ E)) :
    IsNuclearTVS.{test} (StrongDual ℂ Q) := by
  let V := actionIsotype ρ ω
  let c : ℂ := μ.real Set.univ
  have hc : c ≠ 0 := Complex.ofReal_ne_zero.mpr (measureReal_univ_pos (μ := μ)).ne'
  let A := P.codRestrict V (compactActionAverage_mem_isotype μ ρ ω P hP)
  let q := e.symm.toContinuousLinearMap.comp A
  let i := c⁻¹ • (V.subtypeL.comp e.toContinuousLinearMap)
  have hretract (y : Q) : q (i y) = y := by
    apply e.injective
    change e (e.symm _) = e y
    rw [e.apply_symm_apply]
    apply Subtype.ext
    change P (c⁻¹ • (e y : E)) = (e y : E)
    rw [map_smul, compactActionAverage_apply_isotype μ ρ ω P hP (e y).property]
    exact inv_smul_smul₀ hc _
  let pull := ContinuousLinearMap.precomp (τ := RingHom.id ℂ) ℂ q
  let back := ContinuousLinearMap.precomp (τ := RingHom.id ℂ) ℂ i
  have hleft : Function.LeftInverse back pull := fun φ ↦
    ContinuousLinearMap.ext fun y ↦ congrArg φ (hretract y)
  exact nuclear_of_linear_embedding pull (hleft.isEmbedding back.continuous pull.continuous) hE

/-- Compose the homogeneous-to-coinvariant identification with the compact average's
identification of its kernel quotient with the isotype. -/
private theorem globalThetaIsotypicAverage_equiv_of_coinvariants {G E T : Type*}
    [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] (N : Subgroup G)
    [CompactSpace N] [T2Space N] [MeasurableSpace N] [BorelSpace N]
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [T2Space E] [ContinuousSMul ℂ E] [LocallyConvexSpace ℝ E]
    [AddCommGroup T] [Module ℂ T] [TopologicalSpace T] (H : Submodule ℂ T) (q : T → E)
    (μ : Measure N) [μ.IsHaarMeasure] (ρ : G →* (E →L[ℂ] E))
    (hρ : Continuous (fun p : G × E ↦ ρ p.1 p.2)) (ω : PontryaginDual N) (P : E →L[ℂ] E)
    (hP : IsPettisIsotypicAverageOn μ Set.univ (ρ.comp N.subtype) ω P)
    (h : let D := (Submodule.span ℂ (Set.range (fun p : N × E ↦
      p.2 - star (ω p.1 : ℂ) • ρ p.1.val p.2))).topologicalClosure
      ∃ e : (T ⧸ H) ≃L[ℂ] (E ⧸ D), ∀ f : T, e (Submodule.Quotient.mk f) = D.mkQ (q f)) :
    IsClosed (actionIsotype (ρ.comp N.subtype) ω : Set E) ∧
      ∃ e : (T ⧸ H) ≃L[ℂ] actionIsotype (ρ.comp N.subtype) ω, ∀ f, (e (H.mkQ f) : E) = P (q f) := by
  have hc : Continuous (fun p : N × E ↦ (ρ.comp N.subtype) p.1 p.2) :=
    hρ.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hker := compactActionAverage_ker μ (ρ.comp N.subtype) hc ω P hP
  simp only [MonoidHom.comp_apply, Subgroup.subtype_apply] at hker
  dsimp only at h
  rw [← hker] at h
  obtain ⟨e, he⟩ := h
  obtain ⟨a, ha⟩ := compactActionAverage_quotient_equiv μ (ρ.comp N.subtype) hc ω P hP
  exact ⟨isClosed_actionIsotype _ ω, e.trans a, fun f ↦
    (congrArg (fun v ↦ (a v : E)) (he f)).trans (ha (q f))⟩

/-- Paper: Proposition 5.2.3.2(1), p. 236.
The global average induces a topological linear equivalence from the homogeneous quotient
to the closed isotype. Its map on ordinary theta classes is therefore open onto the isotype.
Deviation: The continuous coinvariant quotient is identified via Definition 5.2.2.1. -/
theorem globalThetaIsotypicAverage_equiv (ω : PontryaginDual C₁) :
    IsClosed (E𝔽ω(ω) : Set Θ𝔽) ∧
      ∃ e : Θ𝔽ω(ω) ≃L[ℂ] E𝔽ω(ω), ∀ f : ℬ𝔽,
        (e ((K𝔽ω(ω)).mkQ f) : Θ𝔽) = P𝔽(ω) ((K𝔽).mkQ f) := by
  let : MeasurableSpace C𝔽 := borel _
  let : BorelSpace C𝔽 := ⟨rfl⟩
  let : T2Space C₁ := (ideleClassGroup_finiteness F).2.2.1
  let : CompactSpace C₁ := (ideleClassGroup_finiteness F).2.1
  let : (μ𝔽₁).IsHaarMeasure :=
    (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  let : T2Space Θ𝔽 := globalAdelicThetaSpace_t2_of_isClosed (F := F) adelicTheta_ker_isClosed
  let : PolynormableSpace ℂ Θ𝔽 := globalAdelicThetaSpace_polynormable (F := F)
  let : Module ℝ Θ𝔽 := Module.restrictScalars ℝ ℂ _
  let : IsScalarTower ℝ ℂ Θ𝔽 := IsScalarTower.restrictScalars ℝ ℂ _
  let : LocallyConvexSpace ℝ Θ𝔽 := (PolynormableSpace.withSeminorms ℂ Θ𝔽).toLocallyConvexSpace
  with_reducible_and_instances
    exact globalThetaIsotypicAverage_equiv_of_coinvariants (G := C𝔽) (E := Θ𝔽) (T := ℬ𝔽)
      C₁ (K𝔽ω(ω)) (K𝔽).mkQ μ𝔽₁ ρ𝔽 (existsUnique_globalThetaAction (F := F)).exists.choose_spec.1
      ω (P𝔽(ω)) (existsUnique_globalThetaIsotypicAverage (F := F) ω).exists.choose_spec
      (globalHomogeneousThetaSpace_equiv_coinvariants (F := F) ω)

section
variable {ω : PontryaginDual (ideleClassNorm F).ker}

/-- Paper: Theorem 5.2.3.1(2), p. 233.
The strong dual of the global homogeneous quotient is nuclear. -/
theorem globalHomogeneousThetaSpace_strongDual_nuclear :
    IsNuclearTVS (StrongDual ℂ Θ𝔽ω(ω)) := by
  let : MeasurableSpace C𝔽 := borel _
  let : BorelSpace C𝔽 := ⟨rfl⟩
  let : T2Space C₁ := (ideleClassGroup_finiteness F).2.2.1
  let : CompactSpace C₁ := (ideleClassGroup_finiteness F).2.1
  let : (μ𝔽₁).IsHaarMeasure :=
    (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  let : T2Space Θ𝔽 := globalAdelicThetaSpace_t2_of_isClosed (F := F) adelicTheta_ker_isClosed
  let : PolynormableSpace ℂ Θ𝔽 := globalAdelicThetaSpace_polynormable (F := F)
  let : Module ℝ Θ𝔽 := Module.restrictScalars ℝ ℂ _
  let : IsScalarTower ℝ ℂ Θ𝔽 := IsScalarTower.restrictScalars ℝ ℂ _
  let : LocallyConvexSpace ℝ Θ𝔽 := (PolynormableSpace.withSeminorms ℂ Θ𝔽).toLocallyConvexSpace
  with_reducible_and_instances
    exact strongDual_nuclear_of_compact_isotype μ𝔽₁ ρ𝔽₁ ω (P𝔽(ω))
      (existsUnique_globalThetaIsotypicAverage (F := F) ω).exists.choose_spec
      (globalThetaIsotypicAverage_equiv (F := F) ω).2.choose
      (globalAdelicThetaSpace_strongDual_nuclear (F := F))

/-- Paper: Theorem 5.2.3.1(2), p. 233.
The strong dual of the global homogeneous quotient is Montel. -/
theorem globalHomogeneousThetaSpace_strongDual_montel :
    BarrelledSpace ℂ (StrongDual ℂ Θ𝔽ω(ω)) ∧ MontelSpace ℂ (StrongDual ℂ Θ𝔽ω(ω)) := by
  have hN : IsNuclearTVS.{0} Θ𝔽ω(ω) :=
    globalHomogeneousThetaSpace_nuclear (F := F) (ω := ω)
  let : T2Space Θ𝔽ω(ω) := hN.1
  let : PolynormableSpace ℂ Θ𝔽ω(ω) := hN.2.1
  let : MontelSpace ℂ Θ𝔽ω(ω) := (globalHomogeneousThetaSpace_montel (F := F) (ω := ω)).2
  let : CompleteSpace (StrongDual ℂ Θ𝔽ω(ω)) :=
    globalHomogeneousThetaSpace_strongDual_complete (F := F) (ω := ω)
  have hdual : IsNuclearTVS.{0} (StrongDual ℂ Θ𝔽ω(ω)) :=
    globalHomogeneousThetaSpace_strongDual_nuclear (F := F) (ω := ω)
  let : PolynormableSpace ℂ (StrongDual ℂ Θ𝔽ω(ω)) := hdual.2.1
  refine ⟨barrelled_strongDual_of_montel, ⟨fun B hc hb ↦ ?_⟩⟩
  simpa only [hc.closure_eq] using
    isCompact_closure_of_isNuclearTVS (StrongDual ℂ Θ𝔽ω(ω)) hdual hb

end

/-- Paper: Proposition 5.2.3.2(1), p. 236.
The S-local average induces a topological linear equivalence from the homogeneous quotient
to the closed isotype. Its map on ordinary theta classes is therefore open onto the isotype.
Deviation: The continuous coinvariant quotient is identified via Definition 5.2.2.1. -/
theorem sLocalThetaIsotypicAverage_equiv (χ : PontryaginDual (J₁(S))) :
    IsClosed (Eₛω(S, χ) : Set (Θₛ(S))) ∧
      ∃ e : Θₛω(S, χ) ≃L[ℂ] Eₛω(S, χ), ∀ f : ℬₛ(S),
        (e ((Kₛω(S, χ)).mkQ f) : Θₛ(S)) = Pₛ(S, χ) ((Kₛ(S)).mkQ f) := by
  let E := SLocalAdelicThetaSpace F S
  let G := J₁(S)
  have := isClosed_sProjectedDiagonal (F := F) (S := S)
  let : T2Space (Jₛ(S)) := inferInstanceAs (T2Space (_ ⧸ _))
  let : T2Space G := inferInstanceAs (T2Space ((sIdeleQuotientNorm F S).ker : Set (Jₛ(S))))
  let : MeasurableSpace G := borel _
  let : BorelSpace G := ⟨rfl⟩
  let : CompactSpace G := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage (isCompact_singleton (x := 1)))
  let : T2Space E := sLocalAdelicThetaSpace_t2_of_isClosed (F := F) (S := S)
    (sLocalAdelicTheta_ker_isClosed (F := F) (S := S))
  let : PolynormableSpace ℂ E := sLocalAdelicThetaSpace_polynormable (F := F) (S := S)
  let : (μₛ₁(S)).IsHaarMeasure := (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1
  let : Module ℝ E := Module.restrictScalars ℝ ℂ E
  let : IsScalarTower ℝ ℂ E := IsScalarTower.restrictScalars ℝ ℂ E
  let : LocallyConvexSpace ℝ E := (PolynormableSpace.withSeminorms ℂ E).toLocallyConvexSpace
  with_reducible_and_instances
    exact globalThetaIsotypicAverage_equiv_of_coinvariants (G := Jₛ(S)) (E := E) (T := ℬₛ(S))
      G (Kₛω(S, χ)) (Kₛ(S)).mkQ (μₛ₁(S)) (ρₛ(S))
      (existsUnique_sLocalThetaAction (F := F) (S := S)).exists.choose_spec.1 χ (Pₛ(S, χ))
      (existsUnique_sLocalThetaIsotypicAverage (F := F) (S := S) χ).exists.choose_spec
      (sLocalHomogeneousThetaSpace_equiv_coinvariants (F := F) (S := S) χ)

/-- Paper: Theorem 5.2.3.1(2), p. 233.
The strong dual of the S-local homogeneous quotient is nuclear. -/
theorem sLocalHomogeneousThetaSpace_strongDual_nuclear (χ : PontryaginDual (J₁(S))) :
    IsNuclearTVS (StrongDual ℂ (Θₛω(S, χ))) := by
  let E := SLocalAdelicThetaSpace F S
  let G := J₁(S)
  have := isClosed_sProjectedDiagonal (F := F) (S := S)
  let : T2Space (Jₛ(S)) := inferInstanceAs (T2Space (_ ⧸ _))
  let : T2Space G := inferInstanceAs (T2Space ((sIdeleQuotientNorm F S).ker : Set (Jₛ(S))))
  let : MeasurableSpace G := borel _
  let : BorelSpace G := ⟨rfl⟩
  let : CompactSpace G := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage (isCompact_singleton (x := 1)))
  let : T2Space E := sLocalAdelicThetaSpace_t2_of_isClosed (F := F) (S := S)
    (sLocalAdelicTheta_ker_isClosed (F := F) (S := S))
  let : PolynormableSpace ℂ E := sLocalAdelicThetaSpace_polynormable (F := F) (S := S)
  let : (μₛ₁(S)).IsHaarMeasure := (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1
  let : Module ℝ E := Module.restrictScalars ℝ ℂ E
  let : IsScalarTower ℝ ℂ E := IsScalarTower.restrictScalars ℝ ℂ E
  let : LocallyConvexSpace ℝ E := (PolynormableSpace.withSeminorms ℂ E).toLocallyConvexSpace
  with_reducible_and_instances
    exact strongDual_nuclear_of_compact_isotype (μₛ₁(S)) (ρₛ₁(S)) χ (Pₛ(S, χ))
      (existsUnique_sLocalThetaIsotypicAverage (F := F) (S := S) χ).exists.choose_spec
      (sLocalThetaIsotypicAverage_equiv (F := F) (S := S) χ).2.choose
      (sLocalAdelicThetaSpace_strongDual_nuclear (F := F) (S := S))

-- TODO(paper-gap): The global L² argument on p. 237 fails at norm zero for
-- the rational Gaussian. Apply character uniqueness on each compact norm-one fibre.

set_option linter.overlappingInstances false in
/-- A continuous function on a compact abelian group whose integrals against all characters
vanish is zero. -/
private theorem exists_globalThetaToHomogeneousProduct_charUnique {G : Type*} [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] (φ : C(G, ℂ))
    (hz : ∀ χ : PontryaginDual G, ∫ x, φ x * (χ x : ℂ) ∂μ = 0) : φ = 0 := by
  let ev (x : G) : PontryaginDual G →* Circle :=
    { toFun := fun χ ↦ χ x, map_one' := rfl, map_mul' := fun _ _ ↦ rfl }
  have hsep : Injective ev := fun _ _ h ↦
    pontryaginDual_pairing_separates.1 (funext (DFunLike.congr_fun h))
  have hi : Integrable φ μ :=
    φ.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hae := ae_eq_zero_of_integral_mul_circle_eq_zero ev (fun χ ↦ χ.continuous) hsep hi hz
  have heq := Measure.eq_of_ae_eq hae φ.continuous continuous_const
  exact ContinuousMap.ext fun g ↦ congrFun heq g

private theorem exists_globalThetaToHomogeneousProduct_pi {E : Type*} [AddCommGroup E]
    [Module ℂ E] [TopologicalSpace E] {ι : Type*} (K : Submodule ℂ E) (L : ι → Submodule ℂ E)
    (hKL : ∀ i, K ≤ L i) (hinj : ∀ f, (∀ i, f ∈ L i) → f ∈ K) :
    ∃ P : (E ⧸ K) →L[ℂ] (∀ i, E ⧸ L i),
      Injective P ∧ ∀ (f : E) i, P (K.mkQ f) i = (L i).mkQ f := by
  let P : (E ⧸ K) →ₗ[ℂ] (∀ i, E ⧸ L i) :=
    LinearMap.pi fun i ↦ K.mapQ (L i) LinearMap.id (hKL i)
  have hc : Continuous P :=
    K.isQuotientMap_mkQ.continuous_iff.mpr
      (continuous_pi fun i ↦ (L i).isQuotientMap_mkQ.continuous)
  refine ⟨⟨P, hc⟩, ?_, fun f i ↦ rfl⟩
  change Injective P
  refine LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr fun q hq ↦ ?_)
  induction q using Submodule.Quotient.induction_on with
  | _ f =>
    refine (Submodule.Quotient.mk_eq_zero K).mpr (hinj f fun i ↦ ?_)
    exact (Submodule.Quotient.mk_eq_zero (L i)).mp (congrFun hq i)

private theorem exists_sLocalThetaToHomogeneousProduct_le (χ : PontryaginDual (J₁(S))) :
    Kₛ(S) ≤ Kₛω(S, χ) := by
  intro f hf
  have hθ (g : Jₛ(S)) : sLocalAdelicThetaOnClasses F S f g = 0 := by
    induction g using QuotientGroup.induction_on with | H x => ?_
    exact (sLocalAdelicThetaOnClasses_mk F S f x).trans
      (DFunLike.congr_fun (LinearMap.mem_ker.mp hf) x)
  refine LinearMap.mem_ker.mpr (ContinuousMap.ext fun g ↦ ?_)
  rw [sLocalHomogeneousAdelicThetaLinearMap_apply]
  simp [hθ]

private theorem exists_globalThetaToHomogeneousProduct_le (ω : PontryaginDual C₁) :
    K𝔽 ≤ K𝔽ω(ω) := by
  intro f hf
  have hθ : adelicTheta f = 0 := hf
  refine LinearMap.mem_ker.mpr (ContinuousMap.ext fun g ↦ ?_)
  change homogeneousAdelicTheta ω f g = 0
  simp [homogeneousAdelicTheta, hθ]

private theorem exists_sLocalThetaToHomogeneousProduct_ker (f : ℬₛ(S))
    (hf : ∀ χ : PontryaginDual (J₁(S)), f ∈ Kₛω(S, χ)) : f ∈ Kₛ(S) := by
  let : MeasurableSpace (J₁(S)) := borel _
  have : BorelSpace (J₁(S)) := ⟨rfl⟩
  have : CompactSpace (J₁(S)) := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage isCompact_singleton)
  have : T2Space (Jₛ(S)) :=
    letI := isClosed_sProjectedDiagonal (F := F) (S := S)
    inferInstance
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let : SecondCountableTopology (SAdeleRing F S) := inferInstanceAs (SecondCountableTopology
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : SecondCountableTopology (SAdeleRing F S)ˣ :=
    (sIdeleGroup_description F S).1.secondCountableTopology
  let : SecondCountableTopology (Jₛ(S)) := inferInstance
  let : SecondCountableTopology (J₁(S)) := TopologicalSpace.Subtype.secondCountableTopology _
  let μ := sLocalNormOneQuotientMeasure F S
  have : μ.IsHaarMeasure := (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1
  have : μ.Regular := Measure.regular_of_isMulLeftInvariant isCompact_univ
    (by simp) (measure_ne_top μ _)
  have hθ : sLocalAdelicThetaOnClasses F S f = 0 := by
    ext g
    let φ : C(J₁(S), ℂ) := ⟨fun h ↦ sLocalAdelicThetaOnClasses F S f (g * h.val),
      (sLocalAdelicThetaOnClasses F S f).continuous.comp
        (continuous_const.mul continuous_subtype_val)⟩
    have hφ : φ = 0 := exists_globalThetaToHomogeneousProduct_charUnique μ φ fun χ ↦ by
      have h := DFunLike.congr_fun (LinearMap.mem_ker.mp (hf χ)) g
      rw [sLocalHomogeneousAdelicThetaLinearMap_apply] at h
      exact h
    simpa [φ] using DFunLike.congr_fun hφ 1
  refine LinearMap.mem_ker.mpr (ContinuousMap.ext fun x ↦ ?_)
  refine (sLocalAdelicThetaOnClasses_mk F S f x).symm.trans ?_
  rw [hθ]
  rfl

private theorem exists_globalThetaToHomogeneousProduct_ker (f : ℬ𝔽)
    (hf : ∀ ω : PontryaginDual C₁, f ∈ K𝔽ω(ω)) : f ∈ K𝔽 := by
  let : MeasurableSpace C𝔽 := borel _
  have : BorelSpace C𝔽 := ⟨rfl⟩
  have : T2Space C𝔽 := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.1
  have : CompactSpace C₁ := (ideleClassGroup_finiteness F).2.1
  let μ := normOneIdeleClassTamagawaMeasure F
  have hspec := (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec
  have : μ.IsHaarMeasure := hspec.2.2.2.1
  have : μ.Regular := hspec.2.2.2.2.1
  have hθ : adelicTheta f = 0 := by
    ext g
    let φ : C(C₁, ℂ) := ⟨fun h ↦ adelicTheta f (h.val * g),
      (adelicTheta f).continuous.comp (continuous_subtype_val.mul continuous_const)⟩
    have hφ : φ = 0 := exists_globalThetaToHomogeneousProduct_charUnique μ φ fun ω ↦ by
      have h := DFunLike.congr_fun (LinearMap.mem_ker.mp (hf ω)) g
      exact h
    simpa [φ] using DFunLike.congr_fun hφ 1
  exact hθ

/-- Paper: Proposition 5.2.3.2(2), p. 236.
The canonical global map to the product of homogeneous theta quotients is
continuous and injective. -/
theorem exists_globalThetaToHomogeneousProduct :
    ∃ P : Θ𝔽 →L[ℂ] (∀ ω : PontryaginDual C₁, Θ𝔽ω(ω)),
      Injective P ∧ ∀ (f : ℬ𝔽) ω, P ((K𝔽).mkQ f) ω = (K𝔽ω(ω)).mkQ f :=
  exists_globalThetaToHomogeneousProduct_pi (K𝔽) (fun ω ↦ K𝔽ω(ω))
    exists_globalThetaToHomogeneousProduct_le exists_globalThetaToHomogeneousProduct_ker

/-- Paper: Proposition 5.2.3.2(2), p. 236.
The canonical S-local map to the product of homogeneous theta quotients is
continuous and injective. -/
theorem exists_sLocalThetaToHomogeneousProduct :
    ∃ P : Θₛ(S) →L[ℂ] (∀ χ : PontryaginDual (J₁(S)), Θₛω(S, χ)),
      Injective P ∧ ∀ (f : ℬₛ(S)) χ, P ((Kₛ(S)).mkQ f) χ = (Kₛω(S, χ)).mkQ f :=
  exists_globalThetaToHomogeneousProduct_pi (Kₛ(S)) (fun χ ↦ Kₛω(S, χ))
    exists_sLocalThetaToHomogeneousProduct_le exists_sLocalThetaToHomogeneousProduct_ker

local notation "M𝔽ω(" ω ")" => meromorphicNormOneComponent m𝔽
  (isProperMap_ideleClassNorm F).continuous ω (globalIdelicOrderBound (F := F))
local notation "Mₛω(" S ", " ω ")" => meromorphicNormOneComponent (mₛ(S))
  (isProperMap_sIdeleQuotientNorm F S).continuous ω (sLocalIdelicOrderBound (F := F) (S := S))

/-- Restriction to a norm-one component is continuous for compact convergence, and
restricting a continuation preserves its pole bound. -/
private theorem exists_globalHomogeneousThetaMellin_restriction {G : Type*}
    [CommGroup G] [TopologicalSpace G] (m : G →* ℝ≥0ˣ) (hm : Continuous m)
    (ω : PontryaginDual m.ker) (b : QuasiCharacter G → WithTop ℤ) :
    ∃ R : ↥(meromorphicWithPoleBound (quasiCharacterNormTwist m hm) b) →L[ℂ]
        ↥(meromorphicNormOneComponent m hm ω b),
      ∀ u c, (R u).val c = u.val ⟨c.val.val, c.property⟩ := by
  let Ω := {c : QuasiCharacter G // ∀ h : m.ker, c h.val = (ω h : ℂ)}
  let i : C({c : Ω // 0 ≤ b c.val}, {c : QuasiCharacter G // 0 ≤ b c}) :=
    ⟨fun c ↦ ⟨c.val.val, c.property⟩,
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
  let M := meromorphicWithPoleBound (quasiCharacterNormTwist m hm) b
  let A := (ContinuousMap.compCLM ℂ ℂ i).comp M.subtypeL
  refine ⟨A.codRestrict _ ?_, fun _ _ ↦ rfl⟩
  intro u
  obtain ⟨Z, hZ, hgerm⟩ := u.property
  exact ⟨fun c ↦ Z c.val, fun c ↦ hZ (i c), fun c ↦ hgerm c.val⟩

/-- Paper: (5.2.3.14), p. 236.
The global Mellin transform on homogeneous classes is continuous and injective.
On a representative it gives the component of the global Mellin transform in (5.2.2.2). -/
theorem exists_globalHomogeneousThetaMellin (ω : PontryaginDual C₁) :
    ∃ Z : Θ𝔽ω(ω) →L[ℂ] ↥(M𝔽ω(ω)), Injective Z ∧
      ∀ (f : ℬ𝔽) c,
        (Z ((K𝔽ω(ω)).mkQ f)).val c =
          (globalIdelicMellin (F := F) f).val ⟨c.val.val, c.property⟩ := by
  refine (exists_globalHomogeneousThetaMellin_restriction m𝔽
    (isProperMap_ideleClassNorm F).continuous ω (globalIdelicOrderBound (F := F))).elim fun R hR ↦ ?_
  let L : ℬ𝔽 →L[ℂ] _ := ⟨globalIdelicMellin (F := F), globalIdelicMellin_continuous⟩
  let T : ℬ𝔽 →L[ℂ] ↥(M𝔽ω(ω)) := R.comp L
  have hT (f : ℬ𝔽) c : (T f).val c =
      (globalIdelicMellin (F := F) f).val ⟨c.val.val, c.property⟩ := hR _ c
  have hker : K𝔽ω(ω) = T.ker := by
    apply SetLike.ext
    intro f
    constructor
    · intro hf
      apply LinearMap.mem_ker.mpr
      apply Subtype.ext
      exact ContinuousMap.ext fun c ↦ (hT f c).trans
        ((mem_homogeneousAdelicTheta_ker_iff ω f).mp hf _ c.val.property)
    · intro hf
      apply (mem_homogeneousAdelicTheta_ker_iff ω f).mpr
      intro c hc
      exact (hT f ⟨⟨c.val, hc⟩, c.property⟩).symm.trans
        (congrArg (fun v : ↥(M𝔽ω(ω)) ↦ v.val ⟨⟨c.val, hc⟩, c.property⟩)
          (LinearMap.mem_ker.mp hf))
  exact ⟨(K𝔽ω(ω)).liftQL T hker.le,
    LinearMap.ker_eq_bot.mp ((K𝔽ω(ω)).ker_liftQ_eq_bot T.toLinearMap hker.le hker.ge), hT⟩

/-- Restrict a bounded-pole continuation and its regular values along the component inclusion. -/
private theorem exists_sLocalHomogeneousThetaMellin_restrict {G : Type*} [CommGroup G]
    [TopologicalSpace G] (m : G →* ℝ≥0ˣ) (hm : Continuous m) (χ : PontryaginDual m.ker)
    (b : QuasiCharacter G → WithTop ℤ) :
    ∃ R : ↥(meromorphicWithPoleBound (quasiCharacterNormTwist m hm) b) →L[ℂ]
        ↥(meromorphicNormOneComponent m hm χ b),
      ∀ u c, (R u).val c = u.val ⟨c.val.val, c.property⟩ := by
  let X := {c : QuasiCharacter G // ∀ h : m.ker, c h.val = (χ h : ℂ)}
  let i : C({c : X // 0 ≤ b c.val}, {c // 0 ≤ b c}) :=
    ⟨fun c ↦ ⟨c.val.val, c.property⟩,
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
  have hmem (u : ↥(meromorphicWithPoleBound (quasiCharacterNormTwist m hm) b)) :
      u.val.comp i ∈ meromorphicNormOneComponent m hm χ b := by
    obtain ⟨Z, hZ, hgerm⟩ := u.property
    exact ⟨fun c ↦ Z c.val, fun c ↦ hZ (i c), fun c ↦ hgerm c.val⟩
  exact ⟨{ toFun := fun u ↦ ⟨u.val.comp i, hmem u⟩
           map_add' := fun _ _ ↦ rfl
           map_smul' := fun _ _ ↦ rfl
           cont := ((ContinuousMap.continuous_precomp i).comp continuous_subtype_val).subtype_mk hmem },
    fun _ _ ↦ rfl⟩

/-- Descend the component restriction when vanishing on its regular locus characterizes the kernel. -/
private theorem exists_sLocalHomogeneousThetaMellin_of_ker {G : Type*} [CommGroup G]
    [TopologicalSpace G] (m : G →* ℝ≥0ˣ) (hm : Continuous m) (χ : PontryaginDual m.ker)
    (b : QuasiCharacter G → WithTop ℤ) {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (K : Submodule ℂ E)
    (M : E →L[ℂ] ↥(meromorphicWithPoleBound (quasiCharacterNormTwist m hm) b))
    (hK : ∀ f, f ∈ K ↔ ∀ c : {c // 0 ≤ b c},
      (∀ h : m.ker, c.val h.val = (χ h : ℂ)) → (M f).val c = 0) :
    ∃ Z : (E ⧸ K) →L[ℂ] ↥(meromorphicNormOneComponent m hm χ b), Injective Z ∧
      ∀ f c, (Z (K.mkQ f)).val c = (M f).val ⟨c.val.val, c.property⟩ := by
  obtain ⟨R, hR⟩ := exists_sLocalHomogeneousThetaMellin_restrict m hm χ b
  let L := R.comp M
  have hker : K = L.ker := by
    refine Submodule.ext fun f ↦ (hK f).trans ?_
    change _ ↔ R (M f) = 0
    constructor
    · intro hf
      exact Subtype.ext (ContinuousMap.ext fun c ↦ (hR (M f) c).trans
        (hf ⟨c.val.val, c.property⟩ c.val.property))
    · intro hf c hc
      let d : {x : {x : QuasiCharacter G // ∀ h : m.ker, x h.val = (χ h : ℂ)} //
          0 ≤ b x.val} := ⟨⟨c.val, hc⟩, c.property⟩
      exact (hR (M f) d).symm.trans
        (congrArg (fun u : ↥(meromorphicNormOneComponent m hm χ b) ↦ u.val d) hf)
  refine ⟨K.liftQL L hker.le, ?_, fun f c ↦ hR (M f) c⟩
  exact LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot' _ L.toLinearMap hker)

/-- Paper: (5.2.3.14), p. 236.
The S-local Mellin transform on homogeneous classes is continuous and injective.
On a representative it gives the component of the S-local Mellin transform in (5.2.2.2). -/
theorem exists_sLocalHomogeneousThetaMellin (χ : PontryaginDual (J₁(S))) :
    ∃ Z : Θₛω(S, χ) →L[ℂ] ↥(Mₛω(S, χ)), Injective Z ∧
      ∀ (f : ℬₛ(S)) c,
        (Z ((Kₛω(S, χ)).mkQ f)).val c =
          (sLocalIdelicMellin (F := F) (S := S) f).val ⟨c.val.val, c.property⟩ := by
  exact exists_sLocalHomogeneousThetaMellin_of_ker (mₛ(S))
    (isProperMap_sIdeleQuotientNorm F S).continuous χ (sLocalIdelicOrderBound (F := F) (S := S))
    (Kₛω(S, χ)) ⟨sLocalIdelicMellin (F := F) (S := S), sLocalIdelicMellin_continuous⟩
    (mem_sLocalHomogeneousAdelicTheta_ker_iff (F := F) (S := S) χ)

-- TODO(paper-gap): Ordinary insertion does not in general intertwine isotype
-- projections onto subspaces. Normalizing the averages does not fix this.

/-- Paper: (5.2.3.15), p. 236.
Global insertion commutes with passage to homogeneous theta quotients.
Deviation: The vertical arrows are the canonical quotients. The averages implement
these arrows via the respective identifications of the quotients with the isotypes. -/
theorem sLocalThetaToHomogeneous_commutes {ω : PontryaginDual C₁}
    (hω : NormOneCharacterUnramifiedOutside (F := F) ω S) (x : Θₛ(S)) :
    let P := (exists_globalThetaToHomogeneousProduct (F := F)).choose
    let Q := (exists_sLocalThetaToHomogeneousProduct (F := F) (S := S)).choose
    P (sLocalThetaToGlobal F S x) ω =
      sLocalHomogeneousThetaToGlobal (F := F) (ω := ω) hω
        (Q x (sLocalNormOneCharacter (F := F) S ω hω)) := by
  intro P Q
  induction x using Submodule.Quotient.induction_on with
  | _ f =>
    exact ((exists_globalThetaToHomogeneousProduct (F := F)).choose_spec.2
      (sAdeleSchwartzToGlobal F S f) ω).trans
      ((congrArg (sLocalHomogeneousThetaToGlobal (F := F) (ω := ω) hω)
        ((exists_sLocalThetaToHomogeneousProduct (F := F) (S := S)).choose_spec.2 f
          (sLocalNormOneCharacter (F := F) S ω hω))).trans
        (sLocalHomogeneousThetaToGlobal_mk (F := F) (ω := ω) hω f)).symm

section TranslationRelations

local notation "diag𝔽" => IdeleGroup.unitEmbedding (𝓞 F) F
local notation "diagₛ(" S ")" => Units.map
  (((adeleProjection F S).comp (integralAdelesOutside F S).subtype).comp
    (integralAdeleDiagonal F S)).toMonoidHom

local notation "V𝔽" => Submodule.span ℂ (Set.range (fun p : Fˣ × ℬ𝔽 ↦
  p.2 - schwartzBruhatUnitTranslate (R := 𝔸[F]) (diag𝔽 p.1) p.2))
local notation "Vₛ(" S ")" => Submodule.span ℂ (Set.range (fun
  p : ((S : Set (HeightOneSpectrum (𝓞 F))).integer F)ˣ × ℬₛ(S) ↦
    p.2 - schwartzBruhatUnitTranslate (R := SAdeleRing F S) (diagₛ(S) p.1) p.2))

-- TODO(paper-gap): The pullback topologies below identify the whole theta kernel
-- with zero. For example, an odd rational Schwartz function with even finite part
-- is in the global kernel. The bornological closure assertion on p. 238 needs a
-- separate argument and the bornological quotient and module constructions.

/-- For a closed submodule `K` and a submodule `V ≤ K`, the closure of `V` in the topology
pulled back along the quotient map by `K` is `K`: the image of `V` is `{0}`, which is closed
in the quotient, and its preimage is `K`. -/
private theorem sLocalThetaKernel_eq_induced_closure_of_le {E : Type*} [AddCommGroup E]
    [Module ℂ E] [TopologicalSpace E] (K V : Submodule ℂ E) (hK : IsClosed (K : Set E))
    (hV : V ≤ K) :
    @closure E (TopologicalSpace.induced K.mkQ inferInstance) (V : Set E) = (K : Set E) := by
  have h0 : K.mkQ '' (V : Set E) = {0} := by
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨0, V.zero_mem, map_zero _⟩, ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    exact (Submodule.Quotient.mk_eq_zero K).mpr (hV hv)
  have hc : IsClosed ({0} : Set (E ⧸ K)) := by
    refine K.isQuotientMap_mkQ.isCoinducing.isClosed_preimage.mp ?_
    convert hK using 1
    ext f
    exact Submodule.Quotient.mk_eq_zero K
  ext f
  rw [closure_induced, h0, hc.closure_eq, Set.mem_singleton_iff, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero, SetLike.mem_coe]

/-- S-local theta of a translate is S-local theta evaluated at the inverse-translated idele. -/
private theorem sLocalThetaKernel_eq_induced_closure_translate_apply
    (S : Finset (HeightOneSpectrum (𝓞 F))) (g x : (SAdeleRing F S)ˣ) (f : ℬₛ(S)) :
    sLocalAdelicTheta F S (schwartzBruhatUnitTranslate g f) x =
      sLocalAdelicTheta F S f (g⁻¹ * x) := by
  let d := (Units.map ((adeleProjection F S).comp
    (integralAdelesOutside F S).subtype).toMonoidHom).comp
      (Units.map (integralAdeleDiagonal F S).toMonoidHom)
  refine (sLocalAdelicTheta_apply F S (schwartzBruhatUnitTranslate g f) x).trans
    (Eq.trans ?_ (sLocalAdelicTheta_apply F S f (g⁻¹ * x)).symm)
  exact tsum_congr fun t ↦ congrArg (fun y ↦ f (Multiplicative.ofAdd y))
    (mul_left_comm g.inv (d t).val x.val)

/-- S-local theta is unchanged when a test function is translated by a diagonal S-unit,
since S-local theta factors through the S-idele quotient. -/
private theorem sLocalThetaKernel_eq_induced_closure_translate
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (u : ((S : Set (HeightOneSpectrum (𝓞 F))).integer F)ˣ) (f : ℬₛ(S)) :
    sLocalAdelicTheta F S (schwartzBruhatUnitTranslate (R := SAdeleRing F S) (diagₛ(S) u) f) =
      sLocalAdelicTheta F S f := by
  refine ContinuousMap.ext fun x ↦
    (sLocalThetaKernel_eq_induced_closure_translate_apply S _ x f).trans
      (sLocalAdelicTheta_factorsThrough F S f ?_)
  refine QuotientGroup.eq.mpr ?_
  rw [mul_inv_rev, inv_inv, mul_comm _ x, mul_inv_cancel_left]
  exact ⟨Units.map (integralAdeleDiagonal F S).toMonoidHom u, ⟨u, rfl⟩, Units.ext rfl⟩

/-- Paper: Remark 5.2.3.4(1), p. 237.
The S-local theta kernel is the closure of the span of S-unit translation differences
for the topology pulled back from the theta quotient.
Deviation: This topology on test functions need not be Hausdorff. -/
theorem sLocalThetaKernel_eq_induced_closure (S : Finset (HeightOneSpectrum (𝓞 F))) :
    let q : ℬₛ(S) → Θₛ(S) := (Kₛ(S)).mkQ
    let t : TopologicalSpace (ℬₛ(S)) := TopologicalSpace.induced q inferInstance
    let V := Vₛ(S)
    let K : Set (ℬₛ(S)) := (Kₛ(S) : Set (ℬₛ(S)))
    @closure _ t V.carrier = K := by
  refine sLocalThetaKernel_eq_induced_closure_of_le (Kₛ(S)) _
    (sLocalAdelicTheta_ker_isClosed (F := F) (S := S)) (Submodule.span_le.mpr ?_)
  rintro _ ⟨p, rfl⟩
  exact LinearMap.sub_mem_ker_iff.mpr
    (sLocalThetaKernel_eq_induced_closure_translate S p.1 p.2).symm

/-- Global theta of a translate is global theta evaluated at the inverse-translated class. -/
private theorem globalThetaKernel_eq_induced_closure_translate_apply (g : IdeleGroup (𝓞 F) F)
    (f : ℬ𝔽) (a : C𝔽) :
    adelicTheta (schwartzBruhatUnitTranslate g f) a =
      adelicTheta f ((QuotientGroup.mk g)⁻¹ * a) := by
  induction a using QuotientGroup.induction_on with | H x => ?_
  change _ = adelicTheta f (QuotientGroup.mk (g⁻¹ * x))
  rw [adelicTheta_mk (schwartzBruhatUnitTranslate g f) x, adelicTheta_mk f (g⁻¹ * x)]
  exact tsum_congr fun t ↦ congrArg (fun y ↦ f (Multiplicative.ofAdd y))
    (mul_left_comm g.inv (algebraMap F 𝔸[F] (t : F)) x.val)

/-- Global theta is unchanged when a test function is translated by a principal idele,
since principal ideles are trivial in the idele class group. -/
private theorem globalThetaKernel_eq_induced_closure_translate (a : Fˣ) (f : ℬ𝔽) (c : C𝔽) :
    adelicTheta (schwartzBruhatUnitTranslate (R := 𝔸[F]) (diag𝔽 a) f) c = adelicTheta f c := by
  have h1 : (QuotientGroup.mk (diag𝔽 a) : C𝔽) = 1 := (QuotientGroup.eq_one_iff _).mpr ⟨a, rfl⟩
  have h2 : (QuotientGroup.mk (diag𝔽 a) : C𝔽)⁻¹ * c = c := by
    rw [h1, inv_one, one_mul]
  exact (globalThetaKernel_eq_induced_closure_translate_apply (diag𝔽 a) f c).trans
    (congrArg (adelicTheta f) h2)

/-- Paper: Remark 5.2.3.4(2), p. 237.
The global theta kernel is the closure of the span of principal translation differences
for the topology pulled back from the theta quotient.
Deviation: This topology on test functions need not be Hausdorff. -/
theorem globalThetaKernel_eq_induced_closure :
    let q : ℬ𝔽 → Θ𝔽 := (K𝔽).mkQ
    let t := TopologicalSpace.induced q inferInstance
    let V : Set ℬ𝔽 := (V𝔽).carrier
    @closure _ t V = (K𝔽 : Set ℬ𝔽) := by
  refine sLocalThetaKernel_eq_induced_closure_of_le (K𝔽) _ (adelicTheta_ker_isClosed (F := F))
    (Submodule.span_le.mpr ?_)
  rintro _ ⟨p, rfl⟩
  exact LinearMap.sub_mem_ker_iff.mpr ((adelicThetaLinearMap_apply (F := F) p.2).trans
    ((ContinuousMap.ext fun c ↦
      (globalThetaKernel_eq_induced_closure_translate p.1 p.2 c).symm).trans
        (adelicThetaLinearMap_apply (F := F) _).symm))

local notation "unitAtₛ(" S ")" => sUnitEmbedding F S

/-- A quotient by a smaller submodule maps onto the quotient by a larger one, compatibly
with the quotient maps. -/
private theorem exists_quotient_to_quotient_of_le {R M : Type*} [Ring R] [AddCommGroup M]
    [Module R M] {V K : Submodule R M} (h : V ≤ K) :
    ∃ q : (M ⧸ V) →ₗ[R] (M ⧸ K), Surjective q ∧ q.comp V.mkQ = K.mkQ :=
  ⟨V.liftQ K.mkQ (by rwa [Submodule.ker_mkQ]),
    fun y ↦ by obtain ⟨x, rfl⟩ := K.mkQ_surjective y; exact ⟨V.mkQ x, rfl⟩,
    V.liftQ_mkQ _ _⟩

/-- S-local theta is invariant under translation by a diagonal S-unit. -/
private theorem sLocalAdelicTheta_translate_diag
    (u : ((S : Set (HeightOneSpectrum (𝓞 F))).integer F)ˣ) (f : ℬₛ(S)) :
    sLocalAdelicTheta F S (schwartzBruhatUnitTranslate (R := SAdeleRing F S) (diagₛ(S) u) f) =
      sLocalAdelicTheta F S f := by
  refine ContinuousMap.ext fun g ↦ ?_
  change ∑' ξ : ((S : Set (HeightOneSpectrum (𝓞 F))).integer F)ˣ,
      schwartzBruhatUnitTranslate (R := SAdeleRing F S) (diagₛ(S) u) f
        (Multiplicative.ofAdd (Units.val (unitAtₛ(S) ξ * g))) =
    ∑' ξ : ((S : Set (HeightOneSpectrum (𝓞 F))).integer F)ˣ,
      f (Multiplicative.ofAdd (Units.val (unitAtₛ(S) ξ * g)))
  refine ((Equiv.mulLeft u).tsum_eq _).symm.trans (tsum_congr fun ξ ↦ ?_)
  rw [Equiv.coe_mulLeft, schwartzBruhatUnitTranslate_apply]
  refine congrArg (fun x : SAdeleRing F S ↦ f (Multiplicative.ofAdd x)) ?_
  exact congrArg Units.val (show (diagₛ(S) u)⁻¹ * (unitAtₛ(S) (u * ξ) * g) =
      unitAtₛ(S) ξ * g by
    rw [map_mul, mul_assoc]; exact inv_mul_cancel_left (diagₛ(S) u) _)

/-- The S-unit translation differences lie in the S-local theta kernel. -/
private theorem sLocalSpan_le_ker : Vₛ(S) ≤ Kₛ(S) :=
  Submodule.span_le.mpr (Set.range_subset_iff.mpr fun p ↦ LinearMap.mem_ker.mpr
    (((sLocalAdelicTheta F S).map_sub _ _).trans
      (sub_eq_zero.mpr (sLocalAdelicTheta_translate_diag p.1 p.2).symm)))

/-- Global theta is invariant under translation by a principal idele. -/
private theorem adelicThetaLinearMap_translate_diag (u : Fˣ) (f : ℬ𝔽) :
    adelicThetaLinearMap F (schwartzBruhatUnitTranslate (R := 𝔸[F]) (diag𝔽 u) f) =
      adelicThetaLinearMap F f := by
  change adelicTheta (schwartzBruhatUnitTranslate (R := 𝔸[F]) (diag𝔽 u) f) = adelicTheta f
  refine ContinuousMap.ext fun c ↦ ?_
  induction c using QuotientGroup.induction_on with | H g => ?_
  refine (adelicTheta_mk _ g).trans (Eq.trans ?_ (adelicTheta_mk f g).symm)
  refine ((Equiv.mulLeft u).tsum_eq _).symm.trans (tsum_congr fun ξ ↦ ?_)
  rw [Equiv.coe_mulLeft, schwartzBruhatUnitTranslate_apply]
  refine congrArg (fun x : 𝔸[F] ↦ f (Multiplicative.ofAdd x)) ?_
  exact congrArg Units.val (show (diag𝔽 u)⁻¹ * (diag𝔽 (u * ξ) * g) = diag𝔽 ξ * g by
    rw [map_mul, mul_assoc, inv_mul_cancel_left])

/-- The principal translation differences lie in the global theta kernel. -/
private theorem globalSpan_le_ker : V𝔽 ≤ K𝔽 :=
  Submodule.span_le.mpr (Set.range_subset_iff.mpr fun p ↦ LinearMap.mem_ker.mpr
    (((adelicThetaLinearMap F).map_sub _ _).trans
      (sub_eq_zero.mpr (adelicThetaLinearMap_translate_diag p.1 p.2).symm)))

/-- Paper: Remark 5.2.3.4, p. 238.
The algebraic S-unit coinvariants surject canonically onto the S-local theta quotient.
Deviation: The source is the quotient by the relation span. -/
theorem exists_sLocalAlgebraicCoinvariants_to_theta (S : Finset (HeightOneSpectrum (𝓞 F))) :
    let V := Vₛ(S)
    ∃ q : (ℬₛ(S) ⧸ V) →ₗ[ℂ] Θₛ(S),
      Surjective q ∧ q.comp V.mkQ = (Kₛ(S)).mkQ := by
  intro V
  exact exists_quotient_to_quotient_of_le (sLocalSpan_le_ker (S := S))

/-- Paper: Remark 5.2.3.4, p. 238.
The algebraic principal coinvariants surject canonically onto the global theta quotient.
Deviation: The source is the quotient by the relation span. -/
theorem exists_globalAlgebraicCoinvariants_to_theta :
    let V : Submodule ℂ ℬ𝔽 := V𝔽
    ∃ q : (ℬ𝔽 ⧸ V) →ₗ[ℂ] Θ𝔽, Surjective q ∧ q.comp V.mkQ = (K𝔽).mkQ := by
  intro V
  have h := globalSpan_le_ker (F := F)
  exact exists_quotient_to_quotient_of_le h

private theorem sLocalBornologicalOfQuotient {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] (K : Submodule ℂ E)
    (hE : ∀ p : Seminorm ℂ E,
      (∀ B : Set E, IsVonNBounded ℂ B → BddAbove (p '' B)) → Continuous p)
    (p : Seminorm ℂ (E ⧸ K))
    (hp : ∀ B : Set (E ⧸ K), IsVonNBounded ℂ B → BddAbove (p '' B)) :
    Continuous p := by
  apply K.isQuotientMap_mkQL.continuous_iff.mpr
  refine hE (p.comp K.mkQ) ?_
  intro B hB
  change BddAbove ((fun x : E ↦ p (K.mkQL x)) '' B)
  simpa only [Set.image_image] using hp (K.mkQL '' B) (hB.image K.mkQL)

/-- Paper: Remark 5.2.3.4, pp. 237–238.
The S-local theta quotient is bornological. Every seminorm bounded on all of its
von Neumann bounded sets is continuous. -/
theorem sLocalTheta_bornological :
    ∀ p : Seminorm ℂ (Θₛ(S)),
      (∀ B : Set (Θₛ(S)), IsVonNBounded ℂ B → BddAbove (p '' B)) →
      Continuous p :=
  sLocalBornologicalOfQuotient (LinearMap.ker (sLocalAdelicTheta F S))
    (sAdeleSchwartz_bornological F S)

private theorem bornological_quotient {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] (K : Submodule ℂ E)
    (hE : ∀ p : Seminorm ℂ E,
      (∀ B : Set E, IsVonNBounded ℂ B → BddAbove (p '' B)) → Continuous p)
    (p : Seminorm ℂ (E ⧸ K))
    (hp : ∀ B : Set (E ⧸ K), IsVonNBounded ℂ B → BddAbove (p '' B)) :
    Continuous p := by
  apply K.isQuotientMap_mkQL.continuous_iff.mpr
  refine hE (p.comp K.mkQ) ?_
  intro B hB
  change BddAbove ((fun x : E ↦ p (K.mkQL x)) '' B)
  simpa only [Set.image_image] using hp (K.mkQL '' B) (hB.image K.mkQL)

/-- Paper: Remark 5.2.3.4, pp. 237–238.
The global theta quotient is bornological. Every seminorm bounded on all of its
von Neumann bounded sets is continuous. -/
theorem globalTheta_bornological :
    ∀ p : Seminorm ℂ Θ𝔽, (∀ B : Set Θ𝔽, IsVonNBounded ℂ B → BddAbove (p '' B)) →
      Continuous p :=
  bornological_quotient (K𝔽) (adeleSchwartz_bornological (F := F))

end TranslationRelations

section IsotypicMellin

attribute [local instance] ideleClassGroupMeasurableSpaceSec2b normOneSIdeleQuotientMeasurableSpaceSec2b

/-- A Pettis isotypic average multiplies by the Haar mass at any evaluation of a continuous
linear map into continuous functions on which the action is the character. -/
private theorem globalThetaMellin_isotypicAverage_eval {G E X : Type*} [Monoid G]
    [TopologicalSpace G] [MeasurableSpace G] [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [TopologicalSpace X] (M : Submodule ℂ C(X, ℂ)) (L : E →ₗ[ℂ] M) (hL : Continuous L) (x0 : X)
    (μ : Measure G) (ρ : G →* (E →L[ℂ] E)) (ω : PontryaginDual G) (P : E →L[ℂ] E)
    (hP : IsPettisIsotypicAverageOn μ Set.univ ρ ω P) (u : E)
    (hu : ∀ g, (L (ρ g u)).val x0 = (ω g : ℂ) * (L u).val x0) :
    (L (P u)).val x0 = (μ.real Set.univ : ℂ) * (L u).val x0 := by
  let φ : StrongDual ℂ E :=
    { toFun := fun y ↦ (L y).val x0
      map_add' := fun a b ↦ by simp
      map_smul' := fun a b ↦ by simp
      cont := (continuous_eval_const x0).comp (continuous_subtype_val.comp hL) }
  obtain ⟨_, he⟩ := hP u
  have h := LinearMap.congr_fun he φ
  change φ (P u) = ∫ g, φ (star (ω g : ℂ) • ρ g u) ∂(μ.restrict Set.univ) at h
  refine h.trans ?_
  have hg : ∀ g, φ (star (ω g : ℂ) • ρ g u) = φ u := fun g ↦ by
    rw [map_smul, smul_eq_mul]
    change star (ω g : ℂ) * (L (ρ g u)).val x0 = (L u).val x0
    rw [hu g, ← mul_assoc]
    have h1 : star (ω g : ℂ) * (ω g : ℂ) = 1 := by
      rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Circle.normSq_coe,
        Complex.ofReal_one]
    rw [h1, one_mul]
  simp only [hg, Measure.restrict_univ, integral_const]
  rfl

/-- A functional that scales translates of representatives by a character scales the
induced action on the quotient by the same character. -/
private theorem globalThetaMellin_isotypicAverage_translate {IG CG Q B : Type*} (q : B → Q)
    (hq : Surjective q) (π : IG → CG) (hπ : Surjective π) (ρ : CG → Q → Q) (T : IG → B → B)
    (hρ : ∀ g f, ρ (π g) (q f) = q (T g f)) (φ : Q → ℂ) (χ : CG → ℂ)
    (hT : ∀ g f, φ (q (T g f)) = χ (π g) * φ (q f)) (g : CG) (x : Q) :
    φ (ρ g x) = χ g * φ x := by
  obtain ⟨f, rfl⟩ := hq x
  obtain ⟨g, rfl⟩ := hπ g
  rw [hρ, hT]

/-- A map induced on a quotient by a continuous linear map is continuous. -/
private theorem globalThetaMellin_isotypicAverage_continuous {E Y : Type*} [AddCommGroup E]
    [Module ℂ E] [TopologicalSpace E] [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    (K : Submodule ℂ E) (L : E →ₗ[ℂ] Y) (h : K ≤ LinearMap.ker L) (hL : Continuous L) :
    Continuous (K.liftQ L h) :=
  K.isQuotientMap_mkQ.continuous_iff.mpr hL

/-- Paper: Remark 5.2.3.5, p. 238.
On each component the global Mellin transform of the Tamagawa average equals
the Mellin transform of the original class times the norm-one Haar mass. -/
theorem globalThetaMellin_isotypicAverage (ω : PontryaginDual C₁) (x : Θ𝔽)
    (c : {c : QuasiCharacter C𝔽 // 0 ≤ globalIdelicOrderBound c})
    (hc : ∀ g : C₁, c.val g.val = (ω g : ℂ)) :
    (globalThetaMellin (F := F) (P𝔽(ω) x)).val c =
      ((μ𝔽₁).real Set.univ : ℂ) * (globalThetaMellin (F := F) x).val c :=
  globalThetaMellin_isotypicAverage_eval _ (globalThetaMellin (F := F))
    (globalThetaMellin_isotypicAverage_continuous _ _
      (globalIdelicMellin_vanishes_on_theta_kernel (F := F))
      (globalIdelicMellin_continuous (F := F))) c _ _ ω _
    (existsUnique_globalThetaIsotypicAverage (F := F) ω).exists.choose_spec x
    (fun g ↦ (globalThetaMellin_isotypicAverage_translate Submodule.Quotient.mk
      (Submodule.mkQ_surjective _) QuotientGroup.mk QuotientGroup.mk_surjective
      (fun g y ↦ (existsUnique_globalThetaAction (F := F)).exists.choose g y)
      schwartzBruhatUnitTranslate
      (existsUnique_globalThetaAction (F := F)).exists.choose_spec.2
      (fun y ↦ (globalThetaMellin (F := F) y).val c) (fun g ↦ c.val g)
      (fun g f ↦ globalIdelicMellin_unitTranslate g f c) g.val x).trans
      (congrArg (· * _) (hc g)))

/-- Paper: Remark 5.2.3.5, p. 238.
On each S-local component the Mellin transform of the Tamagawa average equals
the Mellin transform of the original class times the S-local norm-one Haar mass. -/
theorem sLocalThetaMellin_isotypicAverage (χ : PontryaginDual (J₁(S))) (x : Θₛ(S))
    (c : {c : QuasiCharacter (Jₛ(S)) // 0 ≤ sLocalIdelicOrderBound c})
    (hc : ∀ g : J₁(S), c.val g.val = (χ g : ℂ)) :
    (sLocalThetaMellin (F := F) (S := S) (Pₛ(S, χ) x)).val c =
      ((μₛ₁(S)).real Set.univ : ℂ) * (sLocalThetaMellin (F := F) (S := S) x).val c :=
  globalThetaMellin_isotypicAverage_eval _ (sLocalThetaMellin (F := F) (S := S))
    (globalThetaMellin_isotypicAverage_continuous _ _
      (sLocalIdelicMellin_vanishes_on_theta_kernel (F := F) (S := S))
      (sLocalIdelicMellin_continuous (F := F) (S := S))) c _ _ χ _
    (existsUnique_sLocalThetaIsotypicAverage (F := F) (S := S) χ).exists.choose_spec x
    (fun g ↦ (globalThetaMellin_isotypicAverage_translate Submodule.Quotient.mk
      (Submodule.mkQ_surjective _) QuotientGroup.mk QuotientGroup.mk_surjective
      (fun g y ↦ (existsUnique_sLocalThetaAction (F := F) (S := S)).exists.choose g y)
      schwartzBruhatUnitTranslate
      (existsUnique_sLocalThetaAction (F := F) (S := S)).exists.choose_spec.2
      (fun y ↦ (sLocalThetaMellin (F := F) (S := S) y).val c) (fun g ↦ c.val g)
      (fun g f ↦ sLocalIdelicMellin_unitTranslate g f c) g.val x).trans
      (congrArg (· * _) (hc g)))

end IsotypicMellin

section Fourier

-- TODO(paper-gap): The global map is described as inversion on p. 238.
-- The identity on theta functions has a norm factor and two zero terms,
-- as in adelicTheta_riemannRoch.

/-- Testing a weighted continuous function against all characters recovers the function. -/
private theorem existsUnique_sLocalThetaFourier_weighted {G : Type*} [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    (θ : C(G, ℂ)) (w : QuasiCharacter G) (hi : Integrable (fun x ↦ θ x * w x) μ)
    (hz : ∀ χ : PontryaginDual G, ∫ x, θ x * w x * (χ x : ℂ) ∂μ = 0) : θ = 0 := by
  let ev (x : G) : PontryaginDual G →* Circle :=
    { toFun := fun χ ↦ χ x, map_one' := rfl, map_mul' := fun _ _ ↦ rfl }
  have hsep : Injective ev := fun _ _ h ↦
    pontryaginDual_pairing_separates.1 (funext (DFunLike.congr_fun h))
  have hae := ae_eq_zero_of_integral_mul_circle_eq_zero ev (fun χ ↦ χ.continuous) hsep hi hz
  have heq := Measure.eq_of_ae_eq hae (θ.continuous.mul w.continuous) continuous_const
  exact ContinuousMap.ext fun g ↦ (mul_eq_zero.mp (congrFun heq g)).resolve_right
    ((Group.isUnit g).map w).ne_zero

/-- Duality in a norm chart reflects the exponent in one. -/
private theorem existsUnique_sLocalThetaFourier_dual {G : Type*} [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G] (m : G →* ℝ≥0ˣ) (hm : Continuous m)
    (χ : PontryaginDual G) (s : ℂ) :
    let u : Circle →ₜ* ℂ := ⟨Circle.coeHom, continuous_subtype_val⟩
    dualQuasiCharacter m hm (quasiCharacterNormTwist m hm (u.comp χ) s) =
      quasiCharacterNormTwist m hm (u.comp χ⁻¹) (1 - s) := by
  intro u
  ext1 g
  have hp : 0 < ((m g : ℝ≥0) : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
  change (((m g : ℝ≥0) : ℝ) : ℂ) * (quasiCharacterNormTwist m hm (u.comp χ) s) g⁻¹ =
    ((χ⁻¹ g : Circle) : ℂ) * (((m g : ℝ≥0) : ℝ) : ℂ) ^ (1 - s)
  rw [map_inv]
  change _ * ((χ g : ℂ) * (((m g : ℝ≥0) : ℝ) : ℂ) ^ s)⁻¹ = (χ g : ℂ)⁻¹ * _
  rw [Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr hp.ne'), Complex.cpow_one, mul_inv_rev,
    div_eq_mul_inv]
  ring

/-- The double S-adelic Fourier transform is reflection, and minus one is an `S`-unit,
so it has the same theta function. -/
private theorem existsUnique_sLocalThetaFourier_inv (f : ℬₛ(S)) :
    sLocalAdelicTheta F S (sAdeleSchwartzFourier (sAdeleSchwartzFourier f)) =
      sLocalAdelicTheta F S f := by
  ext g
  have hneg : sLocalAdelicTheta F S f (-g) = sLocalAdelicTheta F S f g := by
    refine sLocalAdelicTheta_factorsThrough F S f ?_
    have hm1 : (QuotientGroup.mk (-1 : (SAdeleRing F S)ˣ) : Jₛ(S)) = 1 := by
      refine (sIdeleQuotient_mk_eq_one F S _).2 ⟨-1, ?_⟩
      apply Units.ext
      simp
    rw [show -g = (-1) * g by simp, QuotientGroup.mk_mul, hm1, one_mul]
  rw [← hneg]
  simp only [sLocalAdelicTheta_apply]
  refine tsum_congr fun ξ ↦ ?_
  rw [sLocal_fourier_inversion]
  simp [mul_neg]

/-- The S-adelic Fourier transform preserves the S-local theta kernel. At the center of
the critical strip the functional equation sends each weighted theta integral of the
transform to one of the double transform, which has the original theta function. -/
private theorem existsUnique_sLocalThetaFourier_ker (f : ℬₛ(S))
    (hf : sLocalAdelicTheta F S f = 0) :
    sLocalAdelicTheta F S (sAdeleSchwartzFourier f) = 0 := by
  let : MeasurableSpace (Jₛ(S)) := borel _
  let : BorelSpace (Jₛ(S)) := ⟨rfl⟩
  let : LocallyCompactSpace (SAdeleRing F S)ˣ := (sIdeleGroup_description F S).2.2.1
  have := isClosed_sProjectedDiagonal (F := F) (S := S)
  let μ := sLocalQuotientTamagawaMeasure F S
  have : μ.IsHaarMeasure := (sLocalQuotientTamagawaMeasure_isWeil (F := F) (S := S)).1
  have : μ.Regular := (sLocalQuotientTamagawaMeasure_isWeil (F := F) (S := S)).2.1
  let u : Circle →ₜ* ℂ := ⟨Circle.coeHom, continuous_subtype_val⟩
  let chart (χ : PontryaginDual (Jₛ(S))) : QuasiCharacter (Jₛ(S)) :=
    quasiCharacterNormTwist (sIdeleQuotientNorm F S) (isProperMap_sIdeleQuotientNorm F S).continuous
      (u.comp χ) (1 / 2)
  have hpos (χ : PontryaginDual (Jₛ(S))) :
      ∃ (ψ : PontryaginDual (Jₛ(S))) (s : ℂ), 0 < s.re ∧ chart χ = quasiCharacterNormTwist
        (sIdeleQuotientNorm F S) (isProperMap_sIdeleQuotientNorm F S).continuous (u.comp ψ) s :=
    ⟨χ, 1 / 2, by norm_num, rfl⟩
  have hclasses (h : ℬₛ(S)) (hh : sLocalAdelicTheta F S h = 0) :
      sLocalAdelicThetaOnClasses F S h = 0 := by
    ext g
    induction g using QuotientGroup.induction_on with
    | H x => rw [sLocalAdelicThetaOnClasses_mk, hh]; rfl
  have hθff := hclasses _ ((existsUnique_sLocalThetaFourier_inv f).trans hf)
  have hθ : sLocalAdelicThetaOnClasses F S (sAdeleSchwartzFourier f) = 0 := by
    refine existsUnique_sLocalThetaFourier_weighted μ _ (chart 1)
      (sLocalThetaMellinIntegral_integrable _ _ (hpos 1)) fun χ ↦ ?_
    have hfe := sLocalIdelicZetaIntegral_functionalEquation (sAdeleSchwartzFourier f) χ (1 / 2)
      (by norm_num)
    dsimp only at hfe
    rw [existsUnique_sLocalThetaFourier_dual, show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num] at hfe
    have hc : sLocalThetaMellinIntegral (sAdeleSchwartzFourier f) (chart χ) = 0 := by
      rw [sLocalThetaMellinIntegral_eq_zeta _ (hpos χ)]
      change sLocalIdelicZetaIntegral _ (quasiCharacterNormTwist _ _ (u.comp χ) (1 / 2)) = 0
      have h2 := sLocalThetaMellinIntegral_eq_zeta
        (sAdeleSchwartzFourier (sAdeleSchwartzFourier f)) (hpos χ⁻¹)
      rw [hfe]
      change _ * sLocalIdelicZetaIntegral _ (chart χ⁻¹) = 0
      rw [← h2]
      simp [sLocalThetaMellinIntegral, hθff]
    refine (integral_congr_ae (Filter.Eventually.of_forall fun g ↦ ?_)).trans hc
    change sLocalAdelicThetaOnClasses F S _ g * (1 * _ ^ (1 / 2 : ℂ)) * (χ g : ℂ) =
      sLocalAdelicThetaOnClasses F S _ g * ((χ g : ℂ) * _ ^ (1 / 2 : ℂ))
    rw [one_mul, mul_right_comm, mul_assoc]
  ext g
  rw [← sLocalAdelicThetaOnClasses_mk, hθ]
  rfl

/-- Paper: Theorem 5.2.4.1(1), pp. 238–239.
S-adelic Fourier transform descends to a unique continuous linear involution
on the S-local theta quotient. -/
theorem existsUnique_sLocalThetaFourier :
    ∃! e : Θₛ(S) ≃L[ℂ] Θₛ(S),
      Involutive e ∧ ∀ f : ℬₛ(S),
        e ((Kₛ(S)).mkQ f) = (Kₛ(S)).mkQ (sAdeleSchwartzFourier (F := F) (S := S) f) := by
  obtain ⟨P, hP⟩ := sLocal_fourier_continuousLinear (F := F) (S := S)
  have hK : Kₛ(S) ≤ (Kₛ(S)).comap P.toLinearMap := fun f hf ↦ by
    rw [Submodule.mem_comap, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hP]
    exact existsUnique_sLocalThetaFourier_ker f (LinearMap.mem_ker.mp hf)
  let E₀ : Θₛ(S) →ₗ[ℂ] Θₛ(S) := (Kₛ(S)).mapQ (Kₛ(S)) P.toLinearMap hK
  have hE₀ (f : ℬₛ(S)) : E₀ ((Kₛ(S)).mkQ f) = (Kₛ(S)).mkQ (sAdeleSchwartzFourier f) := by
    rw [← hP]
    rfl
  have hcont : Continuous E₀ := by
    refine (Kₛ(S)).isQuotientMap_mkQ.continuous_iff.mpr ?_
    have : (E₀ ∘ (Kₛ(S)).mkQ) = (Kₛ(S)).mkQ ∘ P :=
      funext fun f ↦ (hE₀ f).trans (by simp only [Function.comp_apply, hP])
    rw [this]
    exact (Kₛ(S)).isQuotientMap_mkQ.continuous.comp P.continuous
  let E : Θₛ(S) →L[ℂ] Θₛ(S) := ⟨E₀, hcont⟩
  have hEE (x : Θₛ(S)) : E (E x) = x := by
    obtain ⟨f, rfl⟩ := (Kₛ(S)).mkQ_surjective x
    change E₀ (E₀ _) = _
    rw [hE₀, hE₀]
    refine (sLocalAdelicThetaSpace_mk_eq_iff _ _).mpr (ContinuousMap.ext fun g ↦ ?_)
    induction g using QuotientGroup.induction_on with
    | H x =>
      rw [sLocalAdelicThetaOnClasses_mk, sLocalAdelicThetaOnClasses_mk,
        existsUnique_sLocalThetaFourier_inv]
  refine ⟨ContinuousLinearEquiv.equivOfInverse E E hEE hEE, ⟨hEE, hE₀⟩, ?_⟩
  rintro e' ⟨-, he'⟩
  ext x
  obtain ⟨f, rfl⟩ := (Kₛ(S)).mkQ_surjective x
  exact (he' f).trans (hE₀ f).symm


open scoped IsDedekindDomain.FiniteAdeleRing RestrictedProduct in
/-- The adelic Fourier transform is a continuous linear operator on the global tests. It is
linear because it is the Pontryagin-dual transform read through self-duality, and continuous
because it maps bounded sets to bounded sets. -/
private theorem existsUnique_globalThetaFourier_clm :
    ∃ P : ℬ𝔽 →L[ℂ] ℬ𝔽, ∀ f, P f = adeleSchwartzFourier f := by
  let : MeasurableSpace 𝔸[F] := borel _
  let G := Multiplicative 𝔸[F]
  let : MeasurableSpace G := borel G
  let μ : Measure G := additiveTamagawaMeasure F
  let (v : HeightOneSpectrum (𝓞 F)) : LocallyCompactSpace (v.adicCompletion F) :=
    locallyCompactSpace_adicCompletion v
  let (v : HeightOneSpectrum (𝓞 F)) : CompactSpace (v.adicCompletionIntegers F) :=
    compactSpace_adicCompletionIntegers v
  let : Fact (∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    ⟨fun _ ↦ Valued.isOpen_valuationSubring _⟩
  let : LocallyCompactSpace G := by
    change LocallyCompactSpace (InfiniteAdeleRing F ×
      (Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F]))
    infer_instance
  let : T2Space G := by
    change T2Space (((v : InfinitePlace F) → v.Completion) ×
      (Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F]))
    infer_instance
  let : BorelSpace G := ⟨rfl⟩
  have hμ := (additiveTamagawaMeasure_existsUnique F).exists.choose_spec
  let : μ.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := hμ.1.toIsFiniteMeasureOnCompacts
      toIsOpenPosMeasure := hμ.1.toIsOpenPosMeasure
      map_mul_left_eq_self := fun x ↦ hμ.1.map_add_left_eq_self x.toAdd }
  let : μ.Regular := hμ.2.1
  obtain ⟨e, he⟩ := additiveTamagawaMeasure_selfDual F
  obtain ⟨Fo, hFo⟩ := schwartzBruhat_fourier_equiv μ
  have hpt (f : ℬ𝔽) (y : G) : adeleSchwartzFourier f y = Fo f (e y) := by
    refine (tamagawaFourier_eq_lcaFourier _ _ _ _ (e y) (fun x ↦ ?_)).trans ((hFo f).2 _).symm
    rw [mul_comm x y.toAdd]
    exact he.1 y.toAdd x
  let L : ℬ𝔽 →ₗ[ℂ] ℬ𝔽 :=
    { toFun := adeleSchwartzFourier
      map_add' := fun f g ↦ Subtype.ext (funext fun y ↦ by
        change adeleSchwartzFourier (f + g) y =
          adeleSchwartzFourier f y + adeleSchwartzFourier g y
        rw [hpt, hpt, hpt, map_add]
        rfl)
      map_smul' := fun c f ↦ Subtype.ext (funext fun y ↦ by
        change adeleSchwartzFourier (c • f) y = c * adeleSchwartzFourier f y
        rw [hpt, hpt, map_smul]
        rfl) }
  exact ⟨⟨L, continuous_of_bornological_image schwartzBruhat_bornological L
    adeleSchwartzFourier_image_isVonNBounded⟩, fun _ ↦ rfl⟩

/-- There are idele classes of every norm `n + 1`. -/
private theorem existsUnique_globalThetaFourier_seq :
    ∃ g : ℕ → IdeleClassGroup (𝓞 F) F,
      ∀ n, ((ideleClassNorm F (g n) : ℝ≥0) : ℝ) = n + 1 := by
  refine ⟨fun n ↦ QuotientGroup.mk (canonicalIdeleNormSection F
    (Units.mk0 ((n : ℝ≥0) + 1) (Nat.cast_add_one_ne_zero n))), fun n ↦ ?_⟩
  change ((ideleNorm F (canonicalIdeleNormSection F _) : ℝ≥0) : ℝ) = _
  rw [canonicalIdeleNormSection_rightInverse F]
  simp

/-- Global theta decays faster than the inverse norm along classes of norm `n + 1`. -/
private theorem existsUnique_globalThetaFourier_tendsto (h : ℬ𝔽)
    (g : ℕ → IdeleClassGroup (𝓞 F) F) (hg : ∀ n, ((ideleClassNorm F (g n) : ℝ≥0) : ℝ) = n + 1) :
    Tendsto (fun n : ℕ ↦ ((n : ℂ) + 1) * adelicTheta h (g n)) atTop (𝓝 0) := by
  obtain ⟨C, T, hC, -, hdec⟩ := adelicTheta_decay_large h 2
  refine squeeze_zero_norm' ?_ (tendsto_const_div_atTop_nhds_zero_nat C)
  filter_upwards [eventually_gt_atTop ⌈T⌉₊, eventually_ge_atTop 1] with n hn hn1
  have hT : T < ((ideleClassNorm F (g n) : ℝ≥0) : ℝ) := by
    rw [hg]
    have := Nat.lt_of_ceil_lt hn
    linarith
  have hb := hdec (g n) hT
  simp only [hg] at hb
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn1
  rw [norm_mul, show ((n : ℂ) + 1) = ((n + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]
  calc ((n : ℝ) + 1) * ‖adelicTheta h (g n)‖ ≤ ((n : ℝ) + 1) * (C * (((n : ℝ) + 1) ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = C / ((n : ℝ) + 1) := by field_simp
    _ ≤ C / n := div_le_div_of_nonneg_left hC.le hpos (by linarith)

/-- A constant whose multiples by `n + 1` converge is zero. -/
private theorem existsUnique_globalThetaFourier_const {z w : ℂ}
    (h : Tendsto (fun n : ℕ ↦ ((n : ℂ) + 1) * z) atTop (𝓝 w)) : z = 0 := by
  have hinv : Tendsto (fun n : ℕ ↦ ((n : ℂ) + 1)⁻¹) atTop (𝓝 0) := by
    have := (Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [Function.comp_def] using this
  have hz := h.mul hinv
  rw [mul_zero] at hz
  refine tendsto_nhds_unique (tendsto_const_nhds.congr fun n ↦ ?_) hz
  field_simp [Nat.cast_add_one_ne_zero n]

/-- A test with vanishing theta function vanishes at zero, and so does its Fourier transform.
By Riemann–Roch the Fourier theta is `a / ‖g‖ - b` with `a`, `b` the two values at zero,
and theta decays at infinity. -/
private theorem existsUnique_globalThetaFourier_zero (f : ℬ𝔽) (hf : adelicTheta f = 0) :
    f (Multiplicative.ofAdd 0) = 0 ∧ adeleSchwartzFourier f (Multiplicative.ofAdd 0) = 0 := by
  obtain ⟨g, hg⟩ := existsUnique_globalThetaFourier_seq (F := F)
  set a := f (Multiplicative.ofAdd (0 : 𝔸[F]))
  set b := adeleSchwartzFourier f (Multiplicative.ofAdd (0 : 𝔸[F]))
  have hval (n : ℕ) :
      ((n : ℂ) + 1) * adelicTheta (adeleSchwartzFourier f) (g n) = a - ((n : ℂ) + 1) * b := by
    have h := adelicTheta_riemannRoch f (g n)⁻¹
    simp only [hf, ContinuousMap.zero_apply, inv_inv, map_inv, Units.val_inv_eq_inv_val,
      NNReal.coe_inv, hg, Complex.real_smul] at h
    push_cast at h
    linear_combination (-1 : ℂ) * h
  have ht := existsUnique_globalThetaFourier_tendsto (adeleSchwartzFourier f) g hg
  simp_rw [hval] at ht
  have hb : b = 0 := by
    have h2 : Tendsto (fun n : ℕ ↦ ((n : ℂ) + 1) * (-b)) atTop (𝓝 (0 - a)) :=
      (ht.sub (tendsto_const_nhds (x := a))).congr fun n ↦ by ring
    exact neg_eq_zero.mp (existsUnique_globalThetaFourier_const h2)
  simp only [hb, mul_zero, sub_zero] at ht
  exact ⟨tendsto_nhds_unique tendsto_const_nhds ht, hb⟩

/-- The adelic Fourier transform preserves the global theta kernel. -/
private theorem existsUnique_globalThetaFourier_ker (f : ℬ𝔽) (hf : adelicTheta f = 0) :
    adelicTheta (adeleSchwartzFourier f) = 0 := by
  obtain ⟨h0, h1⟩ := existsUnique_globalThetaFourier_zero f hf
  ext g
  have h := adelicTheta_riemannRoch f g⁻¹
  have hn : ((ideleClassNorm F g⁻¹ : ℝ≥0) : ℝ)⁻¹ ≠ 0 :=
    inv_ne_zero (NNReal.coe_ne_zero.mpr (ideleClassNorm F g⁻¹).ne_zero)
  simp only [hf, ContinuousMap.zero_apply, inv_inv, h0, h1, smul_zero, add_zero,
    sub_zero] at h
  exact (smul_eq_zero.mp h.symm).resolve_left hn

/-- The double adelic Fourier transform has the same theta function. Riemann–Roch twice
shows the two theta functions differ by a constant, and both decay at infinity. -/
private theorem existsUnique_globalThetaFourier_inv (f : ℬ𝔽) :
    adelicTheta (adeleSchwartzFourier (adeleSchwartzFourier f)) = adelicTheta f := by
  set a := f (Multiplicative.ofAdd (0 : 𝔸[F]))
  set b := adeleSchwartzFourier f (Multiplicative.ofAdd (0 : 𝔸[F]))
  set c := adeleSchwartzFourier (adeleSchwartzFourier f) (Multiplicative.ofAdd (0 : 𝔸[F]))
  have hrr (g : IdeleClassGroup (𝓞 F) F) :
      adelicTheta f g = adelicTheta (adeleSchwartzFourier (adeleSchwartzFourier f)) g + c - a := by
    have h1 := adelicTheta_riemannRoch f g
    have h2 := adelicTheta_riemannRoch (adeleSchwartzFourier f) g⁻¹
    have hn : ((ideleClassNorm F g : ℝ≥0) : ℝ) ≠ 0 :=
      NNReal.coe_ne_zero.mpr (ideleClassNorm F g).ne_zero
    simp only [inv_inv, map_inv, Units.val_inv_eq_inv_val, NNReal.coe_inv,
      Complex.real_smul] at h1 h2
    rw [h1, h2]
    have hn' : (((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
    push_cast
    field_simp
    ring
  obtain ⟨g, hg⟩ := existsUnique_globalThetaFourier_seq (F := F)
  have hca : c - a = 0 := by
    refine existsUnique_globalThetaFourier_const (w := 0 - 0) ?_
    refine ((existsUnique_globalThetaFourier_tendsto f g hg).sub
      (existsUnique_globalThetaFourier_tendsto
        (adeleSchwartzFourier (adeleSchwartzFourier f)) g hg)).congr fun n ↦ ?_
    rw [hrr]
    ring
  ext g
  rw [hrr]
  linear_combination -hca

/-- Paper: Theorem 5.2.4.1(2), p. 239.
Adelic Fourier transform descends to a unique continuous linear involution
on the global theta quotient.
Deviation: The descent identity is tested on global test functions, as in the proof. -/
theorem existsUnique_globalThetaFourier :
    ∃! e : Θ𝔽 ≃L[ℂ] Θ𝔽,
      Involutive e ∧ ∀ f : ℬ𝔽,
        e ((K𝔽).mkQ f) = (K𝔽).mkQ (adeleSchwartzFourier (F := F) f) := by
  obtain ⟨P, hP⟩ := existsUnique_globalThetaFourier_clm (F := F)
  have hK : K𝔽 ≤ (K𝔽).comap P.toLinearMap := fun f hf ↦ by
    rw [Submodule.mem_comap, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hP]
    exact existsUnique_globalThetaFourier_ker f (LinearMap.mem_ker.mp hf)
  let E₀ : Θ𝔽 →ₗ[ℂ] Θ𝔽 := (K𝔽).mapQ K𝔽 P.toLinearMap hK
  have hE₀ (f : ℬ𝔽) : E₀ ((K𝔽).mkQ f) = (K𝔽).mkQ (adeleSchwartzFourier f) := by
    rw [← hP]
    rfl
  have hcont : Continuous E₀ := by
    refine (K𝔽).isQuotientMap_mkQ.continuous_iff.mpr ?_
    have : (E₀ ∘ (K𝔽).mkQ) = (K𝔽).mkQ ∘ P :=
      funext fun f ↦ (hE₀ f).trans (by simp only [Function.comp_apply, hP])
    rw [this]
    exact (K𝔽).isQuotientMap_mkQ.continuous.comp P.continuous
  let E : Θ𝔽 →L[ℂ] Θ𝔽 := ⟨E₀, hcont⟩
  have hEE (x : Θ𝔽) : E (E x) = x := by
    obtain ⟨f, rfl⟩ := (K𝔽).mkQ_surjective x
    change E₀ (E₀ _) = _
    rw [hE₀, hE₀]
    exact (globalAdelicThetaSpace_mk_eq_iff _ _).mpr (existsUnique_globalThetaFourier_inv f)
  refine ⟨ContinuousLinearEquiv.equivOfInverse E E hEE hEE, ⟨hEE, hE₀⟩, ?_⟩
  rintro e' ⟨-, he'⟩
  ext x
  obtain ⟨f, rfl⟩ := (K𝔽).mkQ_surjective x
  exact (he' f).trans (hE₀ f).symm


-- TODO(paper-gap): The unrestricted compatibility assertions on p. 239 fail.
-- For ℚ(i) above 2 the Fourier image of the integer indicator is half the inverse-
-- different indicator. An archimedean bump supported near 1/2 detects the difference.

set_option maxSynthPendingDepth 8 in
open Classical in
/-- Integrating a stage function times one factor at each new place separates over the
additive Tamagawa measure, without a pure-tensor hypothesis on the old stage function. -/
private theorem sLocalThetaFourier_transition_integral
    {D : Finset (HeightOneSpectrum (𝓞 F))} (hD : Disjoint S D)
    (g : SAdeleRing F S → ℂ) (k : (v : D) → v.val.adicCompletion F → ℂ) :
    (∫ z : SAdeleRing F (S ∪ D),
      g (z.1, fun v ↦ z.2 ⟨v.val, Finset.mem_union_left D v.property⟩) *
        ∏ v : D, k v (z.2 ⟨v.val, Finset.mem_union_right S v.property⟩)
        ∂sAdditiveTamagawaMeasure F (S ∪ D)) =
      (∫ z, g z ∂sAdditiveTamagawaMeasure F S) *
        ∏ v : D, ∫ x, k v x ∂finiteLocalAdditiveTamagawaMeasure F v.val := by
  classical
  let V := HeightOneSpectrum (𝓞 F)
  let K (v : V) := v.adicCompletion F
  let (v : V) : MeasurableSpace (K v) := borel (v.adicCompletion F)
  let (w : InfinitePlace F) : MeasurableSpace w.Completion := borel _
  let : MeasurableSpace (InfiniteAdeleRing F) :=
    inferInstanceAs (MeasurableSpace ((w : InfinitePlace F) → w.Completion))
  let μ (v : V) : Measure (K v) := finiteLocalAdditiveTamagawaMeasure F v
  let (v : V) : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
  let (v : V) : (finiteLocalAdditiveTamagawaMeasure F v).IsAddHaarMeasure :=
    finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  let (v : V) : SigmaFinite (μ v) :=
    inferInstanceAs (SigmaFinite (finiteLocalAdditiveTamagawaMeasure F v))
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let (w : InfinitePlace F) : (infiniteLocalAdditiveTamagawaMeasure F w).IsAddHaarMeasure :=
    infiniteLocalAdditiveTamagawaMeasure_haar F w
  let μa := Measure.pi (infiniteLocalAdditiveTamagawaMeasure F)
  let η (A : Finset V) := Measure.pi (fun v : A ↦ μ v.val)
  let e := MeasurableEquiv.piFinsetUnion K hD
  let E := MeasurableEquiv.prodAssoc.trans ((MeasurableEquiv.refl (InfiniteAdeleRing F)).prodCongr e)
  have hE : MeasurePreserving E ((μa.prod (η S)).prod (η D)) (μa.prod (η (S ∪ D))) :=
    ((MeasurePreserving.id μa).prod (measurePreserving_piFinsetUnion hD μ)).comp
      (measurePreserving_prodAssoc μa (η S) (η D))
  let H (z : SAdeleRing F (S ∪ D)) :=
    g (z.1, fun v ↦ z.2 ⟨v.val, Finset.mem_union_left D v.property⟩) *
      ∏ v : D, k v (z.2 ⟨v.val, Finset.mem_union_right S v.property⟩)
  change (∫ z, H z ∂μa.prod (η (S ∪ D))) = _
  refine (hE.integral_comp' H).symm.trans ?_
  have h (p : SAdeleRing F S × ((v : D) → K v.val)) :
      H (E p) = g p.1 * ∏ v : D, k v (p.2 v) := by
    change g (p.1.1, fun v ↦ Equiv.piFinsetUnion K hD (p.1.2, p.2) ⟨v.val, Finset.mem_union_left D v.property⟩) *
      ∏ v : D, k v (Equiv.piFinsetUnion K hD (p.1.2, p.2) ⟨v.val, Finset.mem_union_right S v.property⟩) = _
    simp only [Equiv.piFinsetUnion_left K hD (Subtype.property _),
      Equiv.piFinsetUnion_right K hD (Subtype.property _)]
    rfl
  simp_rw [h]
  exact (integral_prod_mul (μ := μa.prod (η S)) (ν := η D) g (fun x ↦ ∏ v : D, k v (x v))).trans
    (congrArg (_ * ·) (integral_fintype_prod_eq_prod k (μ := fun v : D ↦ μ v.val)))

open Classical in
/-- Extending to a disjoint union multiplies by the integer indicators on its second summand. -/
private theorem sLocalThetaFourier_transition_apply
    {D : Finset (HeightOneSpectrum (𝓞 F))} (hD : Disjoint S D)
    (f : ℬₛ(S)) (z : SAdeleRing F (S ∪ D)) :
    sAdeleSchwartzTransition F (Finset.subset_union_left (s₁ := S) (s₂ := D)) f
        (Multiplicative.ofAdd z) =
      f (Multiplicative.ofAdd (z.1, fun v : S ↦ z.2 ⟨v.val, Finset.mem_union_left D v.property⟩)) *
        ∏ v : D, (v.val.adicCompletionIntegers F : Set (v.val.adicCompletion F)).indicator
          (fun _ ↦ (1 : ℂ)) (z.2 ⟨v.val, Finset.mem_union_right S v.property⟩) := by
  classical
  rw [sAdeleSchwartzTransition_apply]
  split_ifs with h
  · rw [Finset.prod_eq_one (fun v _ ↦ Set.indicator_of_mem
      (h ⟨v.val, Finset.mem_union_right S v.property⟩
        (fun hv ↦ Finset.disjoint_left.mp hD hv v.property)) _), mul_one]
  · push Not at h
    obtain ⟨v, hv, hz⟩ := h
    have hvD := (Finset.mem_union.mp v.property).resolve_left hv
    rw [Finset.prod_eq_zero (Finset.mem_univ (⟨v.val, hvD⟩ : D))
      (Set.indicator_of_notMem hz _), mul_zero]

open Classical in
/-- The Fourier integral for an enlarged test function factors into its stage transform
and the local transforms of the newly inserted integer indicators. -/
private theorem sLocalThetaFourier_transition_union
    {D : Finset (HeightOneSpectrum (𝓞 F))} (hD : Disjoint S D)
    (hgood : ∀ v ∈ D, ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 F)) (f : ℬₛ(S)) :
    let i := sAdeleSchwartzTransition F (Finset.subset_union_left (s₁ := S) (s₂ := D))
    sAdeleSchwartzFourier (i f) = i (sAdeleSchwartzFourier f) := by
  classical
  intro i
  apply Subtype.ext
  funext y
  let p (z : SAdeleRing F (S ∪ D)) : SAdeleRing F S :=
    (z.1, fun v ↦ z.2 ⟨v.val, Finset.mem_union_left D v.property⟩)
  let j (v : D) : ↥(S ∪ D) := ⟨v.val, Finset.mem_union_right S v.property⟩
  let I (v : D) := (v.val.adicCompletionIntegers F : Set (v.val.adicCompletion F)).indicator
    (fun _ ↦ (1 : ℂ))
  let C := (starRingEnd ℂ).toMonoidHom.comp Circle.coeHom
  let g (x : SAdeleRing F S) := f (Multiplicative.ofAdd x) * C (sAdeleStandardCharacter F S (x * p y.toAdd))
  let k (v : D) (x : v.val.adicCompletion F) :=
    I v x * C (finiteLocalStandardCharacter F v.val (x * y.toAdd.2 (j v)))
  have hψ (z : SAdeleRing F (S ∪ D)) : sAdeleStandardCharacter F (S ∪ D) (z * y.toAdd) =
      sAdeleStandardCharacter F S (p z * p y.toAdd) *
        ∏ v : D, finiteLocalStandardCharacter F v.val (z.2 (j v) * y.toAdd.2 (j v)) := by
    let b (v : ↥(S ∪ D)) := finiteLocalStandardCharacter F v.val (z.2 v * y.toAdd.2 v)
    change _ * (∏ v, b v) = (_ * _) * _
    rw [← (Equiv.Finset.union S D hD).prod_comp b, Fintype.prod_sum_type, ← mul_assoc]
    rfl
  have hInt (z : SAdeleRing F (S ∪ D)) :
      i f (Multiplicative.ofAdd z) * C (sAdeleStandardCharacter F (S ∪ D) (z * y.toAdd)) =
        g (p z) * ∏ v : D, k v (z.2 (j v)) := by
    rw [show i f (Multiplicative.ofAdd z) = _ from sLocalThetaFourier_transition_apply hD f z,
      hψ, map_mul, map_prod]
    simp only [g, k, Finset.prod_mul_distrib]
    ring
  have hfix (v : D) : (∫ x, k v x ∂finiteLocalAdditiveTamagawaMeasure F v.val) =
      I v (y.toAdd.2 (j v)) :=
    congrFun ((finiteLocalTamagawaFourier_fixes_integers_iff F v.val).mpr (hgood v.val v.property)) _
  change (∫ z, i f (Multiplicative.ofAdd z) * C (sAdeleStandardCharacter F (S ∪ D) (z * y.toAdd))
      ∂sAdditiveTamagawaMeasure F (S ∪ D)) = _
  simp_rw [hInt]
  exact (sLocalThetaFourier_transition_integral hD g k).trans
    ((congrArg (_ * ·) (Finset.prod_congr rfl fun v _ ↦ hfix v)).trans
      (sLocalThetaFourier_transition_apply hD (sAdeleSchwartzFourier f) y.toAdd).symm)

/-- Paper: Theorem 5.2.4.1(1), p. 239.
The S-local Fourier involutions commute with stage enlargement away from the different.
Deviation: Every added place is required to have a Fourier-fixed integer indicator. -/
theorem sLocalThetaFourier_transition (hST : S ⊆ T)
    (hgood : ∀ v : HeightOneSpectrum (𝓞 F),
      v ∈ T → v ∉ S → ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 F))
    (x : Θₛ(S)) :
    let fourierS := (existsUnique_sLocalThetaFourier (F := F) (S := S)).exists.choose
    let fourierT := (existsUnique_sLocalThetaFourier (F := F) (S := T)).exists.choose
    let transition := sLocalThetaTransition (F := F) (S := S) (T := T) hST
    fourierT (transition x) = transition (fourierS x) := by
  classical
  intro fourierS fourierT transition
  induction x using Submodule.Quotient.induction_on with
  | _ f =>
    let P (A : Finset (HeightOneSpectrum (𝓞 F))) := ∀ h : S ⊆ A,
      let i := sAdeleSchwartzTransition F h
      sAdeleSchwartzFourier (i f) = i (sAdeleSchwartzFourier f)
    have hu : P (S ∪ (T \ S)) := fun _ ↦
      sLocalThetaFourier_transition_union Finset.disjoint_sdiff
        (fun v hv ↦ hgood v (Finset.mem_sdiff.mp hv).1 (Finset.mem_sdiff.mp hv).2) f
    have hT : P T := (Finset.union_sdiff_of_subset hST) ▸ hu
    exact ((existsUnique_sLocalThetaFourier (F := F) (S := T)).exists.choose_spec.2
      (sAdeleSchwartzTransition F hST f)).trans
      ((congrArg (Kₛ(T)).mkQ (hT hST)).trans (congrArg transition
        ((existsUnique_sLocalThetaFourier (F := F) (S := S)).exists.choose_spec.2 f).symm))

set_option maxSynthPendingDepth 8 in
/-- Paper: (5.2.4.4), p. 239.
The local and global Fourier involutions commute with insertion once S contains
every place dividing the different.
Deviation: The places outside S must have Fourier-fixed integer indicators. -/
theorem sLocalThetaFourier_toGlobal
    (hgood : ∀ v : HeightOneSpectrum (𝓞 F), v.asIdeal ∣ differentIdeal ℤ (𝓞 F) → v ∈ S)
    (x : Θₛ(S)) :
    let fourierS := (existsUnique_sLocalThetaFourier (F := F) (S := S)).exists.choose
    let fourier := (existsUnique_globalThetaFourier (F := F)).exists.choose
    fourier (sLocalThetaToGlobal F S x) = sLocalThetaToGlobal F S (fourierS x) := by
  intro fourierS fourier
  induction x using Submodule.Quotient.induction_on with | _ f => ?_
  have hS := (existsUnique_sLocalThetaFourier (F := F) (S := S)).exists.choose_spec.2 f
  have hF := (existsUnique_globalThetaFourier (F := F)).exists.choose_spec.2
    (sAdeleSchwartzToGlobal F S f)
  calc
    _ = (K𝔽).mkQ (adeleSchwartzFourier (sAdeleSchwartzToGlobal F S f)) := hF
    _ = (K𝔽).mkQ (sAdeleSchwartzToGlobal F S (sAdeleSchwartzFourier f)) :=
      congrArg (K𝔽).mkQ
        (adeleSchwartzFourier_sAdeleSchwartzToGlobal_of_different F S hgood f (sAdeleSchwartzFourier f) rfl)
    _ = _ := (congrArg (sLocalThetaToGlobal F S) hS).symm

section

local instance sLocalThetaFourier_mem_isotype_measurableSpace :
    MeasurableSpace (SAdeleRing F S) := by
  letI (w : InfinitePlace F) : MeasurableSpace w.Completion := borel _
  letI (v : S) : MeasurableSpace (v.val.adicCompletion F) := borel _
  exact inferInstanceAs (MeasurableSpace
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))

/-- Paper: Theorem 5.2.4.1(1), p. 239.
Multiplication by a norm-one S-idele preserves additive Tamagawa measure.
This isolates the change of variables needed to exchange character isotypes:
the product of the local additive Haar scaling factors is the S-idele norm. -/
private theorem sLocalThetaFourier_mem_isotype_measurePreserving (u : (SAdeleRing F S)ˣ)
    (hu : sIdeleNorm F S u = 1) :
    MeasurePreserving (fun z : SAdeleRing F S ↦ u.val * z)
      (sAdditiveTamagawaMeasure F S) (sAdditiveTamagawaMeasure F S) := by
  classical
  let := sAdeleRing_borelSpace (F := F) (S := S)
  letI : MeasurableSpace 𝔸[F] := borel _
  letI : BorelSpace 𝔸[F] := ⟨rfl⟩
  let μ := additiveTamagawaMeasure F
  letI : μ.IsAddHaarMeasure := (additiveTamagawaMeasure_existsUnique F).exists.choose_spec.1
  let g := sIdeleInsertion F S u
  have hgn : ideleNorm F g = 1 := (ideleNorm_sIdeleInsertion F S u).trans hu
  have hg : MeasurePreserving (fun a : 𝔸[F] ↦ g.val * a) μ μ := by
    refine ⟨(continuous_const.mul continuous_id).measurable, ?_⟩
    ext B hB
    rw [Measure.map_apply (show Measurable (fun a : 𝔸[F] ↦ g.val * a) from
      (continuous_const.mul continuous_id).measurable) hB]
    have hpre : (fun a : 𝔸[F] ↦ g.val * a) ⁻¹' B =
        (fun a : 𝔸[F] ↦ g⁻¹.val * a) '' B := by
      ext a
      constructor
      · intro ha
        refine ⟨g.val * a, ha, ?_⟩
        exact Units.inv_mul_cancel_left g a
      · rintro ⟨b, hb, rfl⟩
        change g.val * (g⁻¹.val * b) ∈ B
        simpa only [Units.mul_inv_cancel_left] using hb
    rw [hpre, adeleHaar_mul_image F μ g⁻¹ B hB]
    simp [map_inv, hgn]
  let U : Set 𝔸[F] := integralAdelesOutside F S
  have hi := sIdeleInsertion_apply F S u
  have hpre : (fun a : 𝔸[F] ↦ g.val * a) ⁻¹' U = U := by
    ext a
    change g.val * a ∈ integralAdelesOutside F S ↔ a ∈ integralAdelesOutside F S
    simp only [integralAdelesOutside, Subring.mem_iInf, Subring.mem_comap]
    change (∀ v, v ∉ S → g.val.2 v * a.2 v ∈ v.adicCompletionIntegers F) ↔
      ∀ v, v ∉ S → a.2 v ∈ v.adicCompletionIntegers F
    constructor <;> intro h v hv
    · simpa only [g, hi.2.2 v hv, one_mul] using h v hv
    · simpa only [g, hi.2.2 v hv, one_mul] using h v hv
  have hgU := hg.restrict_preimage_emb (measurableEmbedding_const_smul g) U
  rw [hpre] at hgU
  obtain ⟨c, hc, _, hp, _⟩ := sAdeleProjection_dual_masses F S
  have hproj : adeleProjection F S g.val = u.val := by
    apply Prod.ext
    · exact hi.1
    · funext v
      exact hi.2.1 v
  have hcomm : Semiconj (adeleProjection F S) (fun a : 𝔸[F] ↦ g.val * a)
      (fun z : SAdeleRing F S ↦ u.val * z) := by
    intro a
    rw [map_mul, hproj]
  have hs := hp.of_semiconj hgU hcomm (continuous_const.mul continuous_id).measurable
  simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using hs.smul_measure c⁻¹

private theorem sLocalThetaFourier_mem_isotype_unitTranslate (u : (SAdeleRing F S)ˣ)
    (hu : sIdeleNorm F S u = 1) (f : ℬₛ(S)) :
    sAdeleSchwartzFourier (schwartzBruhatUnitTranslate u f) =
      schwartzBruhatUnitTranslate u⁻¹ (sAdeleSchwartzFourier f) := by
  let := sAdeleRing_borelSpace (F := F) (S := S)
  apply Subtype.ext
  funext y
  change (∫ z : SAdeleRing F S, f (Multiplicative.ofAdd (u⁻¹.val * z)) *
    star (sAdeleStandardCharacter F S (z * y.toAdd) : ℂ)
    ∂sAdditiveTamagawaMeasure F S) =
    ∫ z : SAdeleRing F S, f (Multiplicative.ofAdd z) *
      star (sAdeleStandardCharacter F S (z * (u.val * y.toAdd)) : ℂ)
      ∂sAdditiveTamagawaMeasure F S
  have h := (sLocalThetaFourier_mem_isotype_measurePreserving u hu).integral_comp
    (measurableEmbedding_const_smul u)
    (fun z : SAdeleRing F S ↦ f (Multiplicative.ofAdd (u⁻¹.val * z)) *
      star (sAdeleStandardCharacter F S (z * y.toAdd) : ℂ))
  refine h.symm.trans ?_
  apply integral_congr_ae
  filter_upwards [] with z
  rw [Units.inv_mul_cancel_left]
  have hm : (u.val * z) * y.toAdd = z * (u.val * y.toAdd) := by ring
  rw [hm]

end

section

private theorem sLocalThetaFourier_mem_isotype_descend
    {A E : Type*} (q : A → E) (hq : Surjective q)
    (e r r' : E → E) (f t t' : A → A)
    (he : ∀ a, e (q a) = q (f a))
    (hr : ∀ a, r (q a) = q (t a))
    (hr' : ∀ a, r' (q a) = q (t' a))
    (hft : ∀ a, f (t a) = t' (f a)) (x : E) : e (r x) = r' (e x) := by
  obtain ⟨a, rfl⟩ := hq x
  rw [hr, he, he, hr', hft]

private theorem sLocalThetaFourier_mem_isotype_of_intertwining
    {G E : Type*} [CommGroup G] [TopologicalSpace G]
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (ρ : G →* (E →L[ℂ] E)) (e : E ≃L[ℂ] E) (he : Involutive e)
    (hρ : ∀ (g : G) (x : E), e (ρ g x) = ρ g⁻¹ (e x))
    (χ : PontryaginDual G) (x : E) :
    e x ∈ actionIsotype ρ χ⁻¹ ↔ x ∈ actionIsotype ρ χ := by
  have forward (ω : PontryaginDual G) (y : E) (hy : y ∈ actionIsotype ρ ω) :
      e y ∈ actionIsotype ρ ω⁻¹ := by
    rw [mem_actionIsotype] at hy ⊢
    intro g
    rw [← inv_inv g, ← hρ, hy, map_smul]
    simp only [map_inv, inv_inv]
    change (↑(ω g) : ℂ)⁻¹ • e y = (↑((ω g)⁻¹) : ℂ) • e y
    rw [Circle.coe_inv]
  constructor
  · intro hx
    simpa only [he x, inv_inv] using forward χ⁻¹ (e x) hx
  · exact forward χ x

end

private theorem sLocalThetaFourier_mem_isotype_unit_intertwines
    (u : (SAdeleRing F S)ˣ) (hu : sIdeleNorm F S u = 1) (y : Θₛ(S)) :
    let fourier := (existsUnique_sLocalThetaFourier (F := F) (S := S)).exists.choose
    fourier (ρₛ(S) (QuotientGroup.mk u) y) =
      ρₛ(S) (QuotientGroup.mk u⁻¹) (fourier y) := by
  let fourier := (existsUnique_sLocalThetaFourier (F := F) (S := S)).exists.choose
  have hf := (existsUnique_sLocalThetaFourier (F := F) (S := S)).exists.choose_spec
  have ha := (existsUnique_sLocalThetaAction (F := F) (S := S)).exists.choose_spec.2
  exact sLocalThetaFourier_mem_isotype_descend
    (A := ℬₛ(S)) (E := Θₛ(S)) (Kₛ(S)).mkQ (Kₛ(S)).mkQ_surjective
    fourier (ρₛ(S) (QuotientGroup.mk u)) (ρₛ(S) (QuotientGroup.mk u⁻¹))
    sAdeleSchwartzFourier (schwartzBruhatUnitTranslate u) (schwartzBruhatUnitTranslate u⁻¹)
    hf.2 (ha u) (ha u⁻¹) (sLocalThetaFourier_mem_isotype_unitTranslate u hu) y

private theorem sLocalThetaFourier_mem_isotype_intertwines
    (g : J₁(S)) (y : Θₛ(S)) :
    let fourier := (existsUnique_sLocalThetaFourier (F := F) (S := S)).exists.choose
    fourier (ρₛ(S) g.val y) = ρₛ(S) g.val⁻¹ (fourier y) := by
  obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective g.val
  have hn : sIdeleNorm F S u = 1 :=
    (sIdeleQuotientNorm_mk F S u).symm.trans ((congrArg (mₛ(S)) hu).trans g.property)
  have h := sLocalThetaFourier_mem_isotype_unit_intertwines u hn y
  simpa only [QuotientGroup.mk_inv, hu] using h

/-- Paper: Theorem 5.2.4.1(1), p. 239.
S-local Fourier transform exchanges each norm-one isotype with its conjugate. -/
theorem sLocalThetaFourier_mem_isotype (χ : PontryaginDual (J₁(S))) (x : Θₛ(S)) :
    let fourier := (existsUnique_sLocalThetaFourier (F := F) (S := S)).exists.choose
    fourier x ∈ Eₛω(S, χ⁻¹) ↔ x ∈ Eₛω(S, χ) := by
  let fourier := (existsUnique_sLocalThetaFourier (F := F) (S := S)).exists.choose
  exact sLocalThetaFourier_mem_isotype_of_intertwining
    (G := J₁(S)) (E := Θₛ(S)) (ρₛ₁(S)) fourier
    (existsUnique_sLocalThetaFourier (F := F) (S := S)).exists.choose_spec.1
    (sLocalThetaFourier_mem_isotype_intertwines (F := F) (S := S)) χ x

/-- Norm-one dilations preserve additive Tamagawa measure, so Fourier transform
intertwines translation by such an idele with translation by its inverse. -/
private theorem globalThetaFourier_mem_isotype_translate (g : IdeleGroup (𝓞 F) F)
    (hg : ideleNorm F g = 1) (f : ℬ𝔽) :
    adeleSchwartzFourier (schwartzBruhatUnitTranslate g f) =
      schwartzBruhatUnitTranslate g⁻¹ (adeleSchwartzFourier f) := by
  let : MeasurableSpace 𝔸[F] := borel _
  let : BorelSpace 𝔸[F] := ⟨rfl⟩
  let μ := additiveTamagawaMeasure F
  let : μ.IsAddHaarMeasure := (additiveTamagawaMeasure_existsUnique F).exists.choose_spec.1
  let d := Homeomorph.smul (α := 𝔸[F]) g⁻¹
  have hd : MeasurePreserving d μ μ := by
    refine ⟨d.continuous.measurable, Measure.ext fun s hs ↦ ?_⟩
    rw [Measure.map_apply d.continuous.measurable hs]
    change μ ((fun x : 𝔸[F] ↦ g⁻¹ • x) ⁻¹' s) = μ s
    rw [Set.preimage_smul_inv]
    change μ ((fun a : 𝔸[F] ↦ g.val * a) '' s) = μ s
    simpa only [hg, Units.val_one, ENNReal.coe_one, one_mul] using adeleHaar_mul_image F μ g s hs
  apply Subtype.ext
  funext y
  let k (z : 𝔸[F]) := f (Multiplicative.ofAdd z) *
    star (adeleStandardCharacter F (z * (g.val * y.toAdd)) : ℂ)
  refine Eq.trans ?_ (hd.integral_comp d.toMeasurableEquiv.measurableEmbedding k)
  apply integral_congr_ae
  refine Eventually.of_forall fun z ↦ ?_
  change _ * star (adeleStandardCharacter F (z * y.toAdd) : ℂ) =
    _ * star (adeleStandardCharacter F ((g⁻¹.val * z) * (g.val * y.toAdd)) : ℂ)
  rw [mul_mul_mul_comm, show g⁻¹.val * g.val = (1 : 𝔸[F]) from g.inv_val, one_mul]
  rfl

/-- On theta classes, norm-one translation therefore passes through the Fourier
involution as inverse translation. -/
private theorem globalThetaFourier_mem_isotype_intertwine (g : C₁) (x : Θ𝔽) :
    let e := (existsUnique_globalThetaFourier (F := F)).exists.choose
    e (ρ𝔽₁ g x) = ρ𝔽₁ g⁻¹ (e x) := by
  intro e
  obtain ⟨a, ha⟩ := g
  induction a using QuotientGroup.induction_on with | H u => ?_
  induction x using Submodule.Quotient.induction_on with | _ f => ?_
  have hρ := (existsUnique_globalThetaAction (F := F)).exists.choose_spec.2
  have he := (existsUnique_globalThetaFourier (F := F)).exists.choose_spec.2
  calc
    _ = e ((K𝔽).mkQ (schwartzBruhatUnitTranslate u f)) := congrArg e (hρ u f)
    _ = (K𝔽).mkQ (adeleSchwartzFourier (schwartzBruhatUnitTranslate u f)) := he _
    _ = (K𝔽).mkQ (schwartzBruhatUnitTranslate u⁻¹ (adeleSchwartzFourier f)) :=
      congrArg (K𝔽).mkQ (globalThetaFourier_mem_isotype_translate u ha f)
    _ = ρ𝔽 (QuotientGroup.mk u⁻¹) ((K𝔽).mkQ (adeleSchwartzFourier f)) := (hρ u⁻¹ _).symm
    _ = _ := congrArg (ρ𝔽 (QuotientGroup.mk u⁻¹)) (he f).symm

/-- An invertible linear intertwiner for an action and the inverse action
exchanges the eigenspaces for a character and its inverse. -/
private theorem globalThetaFourier_mem_isotype_of_intertwine {G E : Type*}
    [CommGroup G] [TopologicalSpace G] [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (ρ : G →* (E →L[ℂ] E)) (e : E ≃L[ℂ] E)
    (he : ∀ g x, e (ρ g x) = ρ g⁻¹ (e x)) (ω : PontryaginDual G) (x : E) :
    e x ∈ actionIsotype ρ ω⁻¹ ↔ x ∈ actionIsotype ρ ω := by
  rw [mem_actionIsotype, mem_actionIsotype]
  have hχ (g : G) : ω⁻¹ g = ω g⁻¹ := (map_inv ω g).symm
  constructor
  · intro h g
    apply e.injective
    rw [he, h, hχ, inv_inv, map_smul]
  · intro h g
    calc
      ρ g (e x) = e (ρ g⁻¹ x) := by simpa only [inv_inv] using (he g⁻¹ x).symm
      _ = _ := by rw [h, hχ, map_smul]

/-- Paper: Theorem 5.2.4.1(2), p. 239.
Global Fourier transform exchanges each norm-one isotype with its conjugate. -/
theorem globalThetaFourier_mem_isotype (ω : PontryaginDual C₁) (x : Θ𝔽) :
    let fourier := (existsUnique_globalThetaFourier (F := F)).exists.choose
    fourier x ∈ E𝔽ω(ω⁻¹) ↔ x ∈ E𝔽ω(ω) := by
  exact globalThetaFourier_mem_isotype_of_intertwine ρ𝔽₁ _
    globalThetaFourier_mem_isotype_intertwine ω x

end Fourier

end RiemannMasullo
