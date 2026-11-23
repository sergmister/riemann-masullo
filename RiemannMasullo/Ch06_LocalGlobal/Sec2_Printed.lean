module

public import RiemannMasullo.Ch06_LocalGlobal.Sec2
import all RiemannMasullo.Ch02_AdelicTheta.Sec2a
import all RiemannMasullo.Ch02_AdelicTheta.Sec4
import all RiemannMasullo.Ch03_IdelicZeta.Sec3b
import RiemannMasullo.External.AlgebraicNumberTheoryLean.Chebotarev.DirichletHecke
import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.NumberTheory.DirichletCharacter.Bounds

/-! # Chapter 6.2: statements that are false as printed -/

@[expose] public noncomputable section

open Function IsDedekindDomain MeasureTheory NumberField Topology
open scoped DirectSum NNReal

namespace RiemannMasullo

set_option quotPrecheck false

local notation "Places(" F ")" => HeightOneSpectrum (𝓞 F)
local notation "Picₛ(" F ", " S ")" => CommRing.Pic ((S : Set (Places(F))).integer F)
local notation "Iₛ(" F ", " S ")" => (SAdeleRing F S)ˣ
local notation "Nₛ(" F ", " S ")" => (sIdeleNorm F S).ker
local notation "J₁(" F ", " S ")" => (sIdeleQuotientNorm F S).ker
local notation "C₁(" F ")" => (ideleClassNorm F).ker
local notation "ℬ(" R ")" => SchwartzBruhat (Multiplicative R)
local notation "ℬ∞(" F ")" => ℬ(InfiniteAdeleRing F)
local notation "L(" F ", " v ")" => HeightOneSpectrum.adicCompletion (R := 𝓞 F) F v
local notation "O(" F ", " v ")" => HeightOneSpectrum.adicCompletionIntegers (R := 𝓞 F) F v

open Classical in
/-- Paper: Remark 6.2.1.4(1), (6.2.1.2), p. 297. As printed: the locally convex direct sum
topologies of the S-local and global isotypes are strictly finer than the topologies induced by
their inclusions into the ordinary theta quotients. See `sLocalThetaIsotypeSum_dense`,
`globalThetaIsotypeSum_dense` and ERRATA F71. -/
def Printed.thetaIsotypeSum_strictlyFiner : Prop :=
  ∀ (F : Type) [Field F] [NumberField F],
    (∀ S : Finset (Places(F)),
      let ρ := (existsUnique_sLocalThetaAction (F := F) (S := S)).exists.choose
      let E := actionIsotype (ρ.comp (sIdeleQuotientNorm F S).ker.subtype)
      let X := fun χ : PontryaginDual J₁(F, S) ↦ ↥(E χ)
      let _ := locallyConvexFinalTopology (DirectSum.lof ℂ _ X)
      ¬ IsInducing (DirectSum.toModule ℂ _ (SLocalAdelicThetaSpace F S) fun χ ↦ (E χ).subtype)) ∧
    (let ρ := (existsUnique_globalThetaAction (F := F)).exists.choose
      let E := actionIsotype (ρ.comp (ideleClassNorm F).ker.subtype)
      let X := fun ω : PontryaginDual C₁(F) ↦ ↥(E ω)
      let _ := locallyConvexFinalTopology (DirectSum.lof ℂ _ X)
      ¬ IsInducing (DirectSum.toModule ℂ _ (GlobalAdelicThetaSpace F) fun ω ↦ (E ω).subtype))

/-- A norm-one rational idele at the archimedean stage is represented by a diagonal sign. -/
private theorem thetaIsotypeSum_strictlyFiner_false_rat :
    Subsingleton (sIdeleQuotientNorm ℚ ∅).ker := by
  classical
  refine subsingleton_of_forall_eq 1 ?_
  rintro ⟨q, hq⟩
  apply Subtype.ext
  change q = 1
  revert hq
  refine Quotient.inductionOn q fun g hg ↦ ?_
  change sIdeleNorm ℚ ∅ g = 1 at hg
  let w := Rat.infinitePlace
  let coord : SAdeleRing ℚ ∅ ≃+* ℝ :=
    ((RingEquiv.prodZeroRing _ _).symm.trans
      (RingEquiv.piUnique fun v : InfinitePlace ℚ ↦ v.Completion)).trans
      (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace)
  have hn : ‖g.val.1 w‖ = 1 := by
    have h := congrArg (fun t : ℝ≥0ˣ ↦ (t.val : ℝ)) hg
    rwa [sIdeleNorm, Finset.univ_eq_empty (α := (∅ : Finset (Places(ℚ)))),
      Finset.prod_empty, mul_one, Fintype.prod_subsingleton _ w,
      Rat.isReal_infinitePlace.mult_eq_one, pow_one] at h
  have ha : |coord g.val| = 1 :=
    ((InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
      Rat.isReal_infinitePlace).norm_map_of_map_zero (map_zero _) _).trans hn
  apply (sIdeleQuotient_mk_eq_one ℚ ∅ g).mpr
  rcases eq_or_eq_neg_of_abs_eq ha with h | h
  · refine ⟨1, Units.ext (coord.injective ?_)⟩
    simpa only [map_one, Units.val_one] using h
  · refine ⟨-1, Units.ext (coord.injective ?_)⟩
    change coord g.val = coord (((adeleProjection ℚ ∅).comp (integralAdelesOutside ℚ ∅).subtype)
      (integralAdeleDiagonal ℚ ∅ (-1)))
    simpa only [map_neg, map_one] using h

/-- For a single submodule, the locally convex direct sum induces the subspace topology. -/
private theorem thetaIsotypeSum_strictlyFiner_false_single
    {E I : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [PolynormableSpace ℂ E]
    [Subsingleton I] [DecidableEq I] (X : I → Submodule ℂ E) (k : I) :
    letI := locallyConvexFinalTopology (DirectSum.lof ℂ I fun i ↦ ↥(X i))
    IsInducing (DirectSum.toModule ℂ I E fun i ↦ (X i).subtype) := by
  let D := ⨁ i, ↥(X i)
  let j := DirectSum.lof ℂ I fun i ↦ ↥(X i)
  let : TopologicalSpace D := locallyConvexFinalTopology j
  have hD : WithSeminorms
      (Subtype.val : {p : Seminorm ℂ D // ∀ i, Continuous (p ∘ j i)} → Seminorm ℂ D) := ⟨rfl⟩
  let := hD.isTopologicalAddGroup
  let := PolynormableSpace.isTopologicalAddGroup ℂ E
  let c := DirectSum.component ℂ I (fun i ↦ ↥(X i)) k
  have hj : Continuous (j k) := hD.continuous_of_continuous_comp _ fun p ↦ p.property k
  have hc : Continuous c := by
    apply (PolynormableSpace.withSeminorms ℂ (X k)).continuous_of_continuous_comp c
    intro p
    apply hD.continuous_seminorm ⟨p.val.comp c, ?_⟩
    intro i
    obtain rfl := Subsingleton.elim i k
    change Continuous fun x : X i ↦ p.val ((j i x) i)
    simp only [j, DirectSum.lof_apply]
    exact p.property
  -- Projection onto the only component is inverse to its inclusion.
  have hleft : LeftInverse (j k) c := by
    intro x
    apply DFinsupp.ext
    intro i
    obtain rfl := Subsingleton.elim i k
    exact DFinsupp.single_eq_same
  have hsum : ⇑(DirectSum.toModule ℂ I E fun i ↦ (X i).subtype) = Subtype.val ∘ c := by
    funext x
    conv_lhs => rw [← hleft x]
    exact DirectSum.toModule_lof (M := fun i ↦ ↥(X i)) (φ := fun i ↦ (X i).subtype) ℂ k (c x)
  rw [hsum]
  exact IsInducing.subtypeVal.comp (hleft.isEmbedding hj hc).isInducing

/-- Paper: Remark 6.2.1.4(1), (6.2.1.2), p. 297. Over ℚ at the archimedean stage the norm-one
quotient is `{±1}/{±1}`, so the sole summand is the entire theta space with its own topology.
Globally over ℚ, the action of the profinite norm-one group factors through a finite group on
each finite test level. The finite character projections extend through the inductive limit and
the theta quotient to a continuous inverse to the sum map. -/
theorem Printed.thetaIsotypeSum_strictlyFiner_false :
    ¬ Printed.thetaIsotypeSum_strictlyFiner := by
  classical
  intro h
  apply (h ℚ).1 ∅
  let G := (sIdeleQuotientNorm ℚ ∅).ker
  let : Subsingleton G := thetaIsotypeSum_strictlyFiner_false_rat
  let : Subsingleton (PontryaginDual G) := subsingleton_of_forall_eq 1 fun χ ↦
    PontryaginDual.ext fun g ↦ by rw [Subsingleton.elim g 1, map_one, map_one]
  let : DecidableEq (PontryaginDual G) := Classical.decEq _
  let : PolynormableSpace ℂ (SLocalAdelicThetaSpace ℚ ∅) := sLocalAdelicThetaSpace_polynormable
  let ρ := (existsUnique_sLocalThetaAction (F := ℚ) (S := ∅)).exists.choose
  let X := actionIsotype (ρ.comp (sIdeleQuotientNorm ℚ ∅).ker.subtype)
  exact thetaIsotypeSum_strictlyFiner_false_single (E := SLocalAdelicThetaSpace ℚ ∅)
    (I := PontryaginDual G) X 1

/-- Paper: Remark 6.2.1.4(2), p. 298. As printed: the S-local theta quotient has nonclosed
image in the product of its homogeneous theta quotients, and the topology induced by the product
is strictly coarser. We take the product in (5.2.3.13), Proposition 5.2.3.2(2), p. 236.
The remark gives conflicting references, including (5.2.2.3), which defines a quotient. See the
global versions `globalThetaToHomogeneousProduct_not_isClosed_range` and
`globalThetaToHomogeneousProduct_not_isInducing`, and ERRATA F72. -/
def Printed.sLocalThetaToHomogeneousProduct_strictlyCoarser_nonclosed : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (Places(F))),
    let P := (exists_sLocalThetaToHomogeneousProduct (F := F) (S := S)).choose
    ¬ IsInducing P ∧ ¬ IsClosed (Set.range P)

/-- At the rational archimedean stage, the two norm-one ideles are both diagonal units. -/
private theorem sLocalThetaToHomogeneousProduct_normOne_rat :
    Subsingleton (sIdeleQuotientNorm ℚ ∅).ker := by
  refine subsingleton_of_forall_eq 1 fun ⟨x, hx⟩ ↦ Subtype.ext ?_
  change x = 1
  revert hx
  refine Quotient.inductionOn x fun g hg ↦ ?_
  change sIdeleNorm ℚ ∅ g = 1 at hg
  let j := InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
  let e : SAdeleRing ℚ ∅ ≃+* ℝ := ((RingEquiv.prodZeroRing _ _).symm.trans
    (RingEquiv.piUnique fun w : InfinitePlace ℚ ↦ w.Completion)).trans j
  have hnorm : |e g.val| = 1 := by
    trans ‖g.val.1 Rat.infinitePlace‖
    · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
        Rat.isReal_infinitePlace).norm_map_of_map_zero (map_zero _) _
    have h := congrArg (fun t : ℝ≥0ˣ ↦ (t.val : ℝ)) hg
    rw [sIdeleNorm, Finset.univ_eq_empty (α := (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))),
      Finset.prod_empty, mul_one, Fintype.prod_subsingleton _ Rat.infinitePlace,
      Rat.isReal_infinitePlace.mult_eq_one, pow_one] at h
    exact h
  rcases eq_or_eq_neg_of_abs_eq hnorm with h | h
  · have hg1 : g = 1 := Units.ext (e.injective (h.trans (map_one e).symm))
    simp [hg1]
  · have hgneg : g = -1 := Units.ext (e.injective (by simpa using h))
    refine (sIdeleQuotient_mk_eq_one ℚ ∅ g).2 ⟨-1, ?_⟩
    apply Units.ext
    simp [hgneg]

/-- With just the trivial norm-one character, any element of the product is represented
by a test function in its sole coordinate. Thus the product map has closed range. -/
private theorem sLocalThetaToHomogeneousProduct_isClosed_of_subsingleton
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hG : Subsingleton (sIdeleQuotientNorm F S).ker) :
    IsClosed (Set.range (exists_sLocalThetaToHomogeneousProduct (F := F) (S := S)).choose) := by
  let P := (exists_sLocalThetaToHomogeneousProduct (F := F) (S := S)).choose
  suffices hs : Surjective P by
    exact (congrArg IsClosed hs.range_eq).mpr isClosed_univ
  let χ₀ : PontryaginDual (sIdeleQuotientNorm F S).ker := 1
  have hχ (χ : PontryaginDual (sIdeleQuotientNorm F S).ker) : χ = χ₀ := by
    apply PontryaginDual.ext
    intro g
    rw [hG.allEq g 1, map_one, map_one]
  intro y
  let K := LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap F S χ₀)
  let f := (K.mkQ_surjective (y χ₀)).choose
  have hf : K.mkQ f = y χ₀ := (K.mkQ_surjective (y χ₀)).choose_spec
  let x := (sLocalAdelicTheta F S).ker.mkQ f
  have hx := (exists_sLocalThetaToHomogeneousProduct (F := F) (S := S)).choose_spec.2 f χ₀
  refine ⟨x, ?_⟩
  funext χ
  exact (congrArg (fun i ↦ P x i = y i) (hχ χ)).mpr (hx.trans hf)

/-- Paper: Remark 6.2.1.4(2), p. 298. Take ℚ and the archimedean stage. The norm-one quotient
is trivial, and projection to the sole factor identifies the product map with the identity on
the theta quotient. The range is closed and the induced topology is the intrinsic topology. -/
theorem Printed.sLocalThetaToHomogeneousProduct_strictlyCoarser_nonclosed_false :
    ¬ Printed.sLocalThetaToHomogeneousProduct_strictlyCoarser_nonclosed := by
  intro h
  exact (h ℚ ∅).2 (sLocalThetaToHomogeneousProduct_isClosed_of_subsingleton ℚ ∅
    sLocalThetaToHomogeneousProduct_normOne_rat)

section StandardFunctions

variable {F : Type*} [Field F] [NumberField F]

local instance printedCh06Sec2FiniteIdeleMeasurableSpace (v : Places(F)) :
    MeasurableSpace (L(F, v))ˣ := borel _

local notation "U(" F ", " v ")" => ((O(F, v)).units : Set (L(F, v))ˣ)
local notation "μ(" F ", " v ")" => finiteLocalMultiplicativeTamagawaMeasure F v

open Classical in
/-- Paper: Theorem 6.2.2.1, first numbered definition, p. 298. As printed: at a ramified place
in S the standard test has zeta integral equal to the integer-unit mass when the character
matches on integer units and has positive abscissa, and zero otherwise. See
`finiteStandardGaussian_zeta_of_ramified` and ERRATA F73. -/
def Printed.finiteStandardGaussian_zeta_of_ramified_positive : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (Places(F))),
    Subsingleton Picₛ(F, S) →
    ∀ (ω : PontryaginDual C₁(F)) (hω : NormOneCharacterUnramifiedOutside ω S) (v : S)
      (d : QuasiCharacter (L(F, v.val))ˣ),
      let c := sLocalFiniteRestriction v (sIdeleRestriction F S hω.choose)
      let Uv := U(F, v.val)
      (∃ u ∈ Uv, c u ≠ 1) →
        localIdelicZetaIntegral (μ(F, v.val))
          (fun x ↦ finiteStandardGaussian v.val c (Multiplicative.ofAdd x)) d =
        if (∀ u ∈ Uv, d u = c u) ∧ (∃ σ : ℝ, 0 < σ ∧ ∀ g : (L(F, v.val))ˣ,
          ‖d g‖ = ‖g.val‖ ^ σ) then ((μ(F, v.val)) Uv).toReal else 0

open NumberFieldKB.Chebotarev.RatIdele in
/-- The idelic character of a Dirichlet character modulo 5, at the idele with `2` at the place
over 5 and `1` elsewhere, is the inverse of the character value at `2`. -/
private theorem Printed.finiteStandardGaussian_zeta_of_ramified_positive_false_two
    (χ : DirichletCharacter ℂ 5) (v : Pl) (hv : pr v = 5) (u : (v.adicCompletion ℚ)ˣ)
    (hu : (u : v.adicCompletion ℚ) = ((2 : ℕ) : v.adicCompletion ℚ)) :
    ((ideleChar 5 χ (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v u) : ℂˣ) : ℂ) =
      (χ (2 : ZMod 5))⁻¹ := by
  have hval : Valued.v (u : v.adicCompletion ℚ) = WithZero.exp (-(0 : ℤ)) := by
    rw [neg_zero, WithZero.exp_zero, hu, ← Rat.cast_natCast, valued_ratCast,
      ← map_natCast (algebraMap (𝓞 ℚ) ℚ) 2,
      IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem, natCast_mem_asIdeal_iff, hv]
    norm_num
  have hq : ratPart (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v u) = 1 := by
    rw [ratPart_ofAdicCompletion v u 0 hval, zpow_zero]
  have hU : unitPart (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v u) =
      IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v u := by
    rw [unitPart_apply, hq, map_one, inv_one, mul_one]
  have hr : resMod 5 (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v u) = (2 : ZMod 5) := by
    rw [resMod_apply, resModFun, hU]
    refine (ZMod.equivPi 5 (NeZero.ne 5)).symm_apply_eq.mpr (funext fun q ↦ ?_)
    have hq5 : (q : ℕ) = 5 :=
      (Nat.prime_dvd_prime_iff_eq (Nat.prime_of_mem_primeFactors q.2) Nat.prime_five).mp
        (Nat.dvd_of_mem_primeFactors q.2)
    have hqN : (q : ℕ) ^ (5 : ℕ).factorization q ∣ 5 := Nat.ordProj_dvd 5 q
    have hcomp : ZMod.equivPi 5 (NeZero.ne 5) (2 : ZMod 5) q =
        ZMod.castHom hqN (ZMod ((q : ℕ) ^ (5 : ℕ).factorization q)) (2 : ZMod 5) :=
      RingHom.congr_fun (Subsingleton.elim ((Pi.evalRingHom _ q).comp
        (ZMod.equivPi 5 (NeZero.ne 5)).toRingHom) (ZMod.castHom hqN _)) (2 : ZMod 5)
    rw [hcomp, map_ofNat]
    have hqv : placeP 5 q = v := pr_injective (by rw [placeP, pr_placeOf, hq5, hv])
    subst hqv
    rw [compV_ofAdicCompletion_self]
    erw [hu, redP_natCast]
    rfl
  rw [coe_ideleChar, MulChar.coe_toUnitHom, MonoidHom.coe_toHomUnits, hr]

/-- Paper: Theorem 6.2.2.1, first numbered definition, p. 298. Over ℚ take the even quadratic
idele class character modulo 5, S consisting of the infinite place and 5, and the unitary local
character at 5 as d. Its abscissa is zero. The standard test is its conjugate on the integer
units, so the integrand is their indicator and the integral is their positive mass. -/
theorem Printed.finiteStandardGaussian_zeta_of_ramified_positive_false :
    ¬ Printed.finiteStandardGaussian_zeta_of_ramified_positive := by
  classical
  intro h
  let v5 : Places(ℚ) := NumberFieldKB.Chebotarev.RatIdele.placeOf 5 Nat.prime_five
  have hv5 : NumberFieldKB.Chebotarev.RatIdele.pr v5 = 5 := NumberFieldKB.Chebotarev.RatIdele.pr_placeOf 5 Nat.prime_five
  let S : Finset Places(ℚ) := {v5}
  -- A character modulo 5 that is nontrivial at 2.
  obtain ⟨χ, hχ2⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity (ZMod 5) ℂ
    (a := (2 : ZMod 5)) (by decide)
  -- The idelic character and its norm-one restriction.
  let H : HeckeCharacter (𝓞 ℚ) ℚ := (⟨Units.coeHom ℂ, Units.continuous_val⟩ : ℂˣ →ₜ* ℂ).comp
    (NumberFieldKB.Chebotarev.RatIdele.ratDirichletChar 5 χ)
  have hH (x : IdeleClassGroup (𝓞 ℚ) ℚ) : ‖H x‖ = 1 := by
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    change ‖((NumberFieldKB.Chebotarev.RatIdele.ideleChar 5 χ y : ℂˣ) : ℂ)‖ = 1
    rw [NumberFieldKB.Chebotarev.RatIdele.coe_ideleChar, norm_inv, MulChar.coe_toUnitHom,
      DirichletCharacter.unit_norm_eq_one χ, inv_one]
  let ψ : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ) :=
    ⟨{ toFun := fun x ↦ ⟨H x, mem_sphere_zero_iff_norm.2 (hH x)⟩
       map_one' := Circle.ext H.map_one
       map_mul' := fun x y ↦ Circle.ext (H.map_mul x y) }, H.continuous.subtype_mk _⟩
  let ω : PontryaginDual C₁(ℚ) :=
    ψ.comp ⟨(ideleClassNorm ℚ).ker.subtype, continuous_subtype_val⟩
  have hHS : H ∈ unramifiedOutside ℚ S := by
    refine (mem_unramifiedOutside_iff ℚ S H).mpr fun v hv u ↦ ?_
    have hne : v ≠ v5 := fun e ↦ hv (e ▸ Finset.mem_singleton_self v5)
    have hcop : (NumberFieldKB.Chebotarev.RatIdele.pr v).Coprime 5 := by
      refine (Nat.coprime_primes (NumberFieldKB.Chebotarev.RatIdele.pr_prime v) Nat.prime_five).mpr fun e ↦ hne ?_
      exact NumberFieldKB.Chebotarev.RatIdele.pr_injective (e.trans hv5.symm)
    let x := Units.map (v.adicCompletionIntegers ℚ).subtype.toMonoidHom u
    have hx : Valued.v (x : v.adicCompletion ℚ) = 1 :=
      (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one (a := x)).mp
        ⟨u.val.property, u.inv.property⟩
    change ((NumberFieldKB.Chebotarev.RatIdele.ideleChar 5 χ (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v x) : ℂˣ) : ℂ) = 1
    rw [NumberFieldKB.Chebotarev.RatIdele.ideleChar_unit 5 χ hcop x hx, Units.val_one]
  have hω : NormOneCharacterUnramifiedOutside ω S := ⟨⟨H, hHS⟩, fun _ ↦ rfl⟩
  have hPic : Subsingleton Picₛ(ℚ, S) := by
    have : IsPrincipalIdealRing (𝓞 ℚ) := classNumber_eq_one_iff.mp Rat.classNumber_eq
    have h0 : Subsingleton Picₛ(ℚ, (∅ : Finset Places(ℚ))) := by
      rw [Finset.coe_empty, integer_empty]
      let e := Algebra.botEquivOfInjective (IsFractionRing.injective (𝓞 ℚ) ℚ)
      let := IsPrincipalIdealRing.of_surjective e.symm e.symm.surjective
      infer_instance
    obtain ⟨_, _, _, hsurj, _⟩ := picard_localization_exact ℚ ∅ S (Finset.empty_subset S)
    exact hsurj.subsingleton
  let w : S := ⟨v5, Finset.mem_singleton_self v5⟩
  let c := sLocalFiniteRestriction w (sIdeleRestriction ℚ S hω.choose)
  -- Values of `c` on local units of norm one are values of `H`.
  have hcH (u : (L(ℚ, v5))ˣ) (hu : ‖(u : L(ℚ, v5))‖ = 1) :
      c u = ((NumberFieldKB.Chebotarev.RatIdele.ideleChar 5 χ (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v5 u) : ℂˣ) : ℂ) := by
    have hins := sIdeleInsertion_finiteUnit (F := ℚ) (S := S) w u
    have hmem : (IdeleClassGroup.ofAdicCompletion (𝓞 ℚ) ℚ v5 u) ∈ (ideleClassNorm ℚ).ker := by
      rw [MonoidHom.mem_ker, ideleClassNorm_ofAdicCompletion]
      ext
      simpa using hu
    have hspec := hω.choose_spec ⟨_, hmem⟩
    change hω.choose.val (QuotientGroup.mk (sIdeleInsertion ℚ S _)) = _
    rw [hins]
    exact hspec
  -- An integer unit of `ℚ₅` on which `c` is not trivial.
  have hval2 : Valued.v ((2 : ℕ) : L(ℚ, v5)) = 1 := by
    rw [← Rat.cast_natCast, NumberFieldKB.Chebotarev.RatIdele.valued_ratCast,
      ← map_natCast (algebraMap (𝓞 ℚ) ℚ) 2,
      IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem,
      NumberFieldKB.Chebotarev.RatIdele.natCast_mem_asIdeal_iff, hv5]
    norm_num
  have h2ne : ((2 : ℕ) : L(ℚ, v5)) ≠ 0 := fun e ↦ by
    rw [e, map_zero] at hval2
    exact zero_ne_one hval2
  let u2 : (L(ℚ, v5))ˣ := Units.mk0 _ h2ne
  have hu2v : Valued.v (u2 : L(ℚ, v5)) = 1 := hval2
  have hu2U : u2 ∈ U(ℚ, v5) :=
    (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one (a := u2)).mpr hu2v
  have hunorm (u : (L(ℚ, v5))ˣ) (hu : u ∈ U(ℚ, v5)) : ‖(u : L(ℚ, v5))‖ = 1 :=
    Valued.toNormedField.norm_eq_one_iff.mpr
      ((HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one (a := u)).mp hu)
  have hcram : ∃ u ∈ U(ℚ, v5), c u ≠ 1 := by
    refine ⟨u2, hu2U, ?_⟩
    rw [hcH u2 (hunorm u2 hu2U),
      Printed.finiteStandardGaussian_zeta_of_ramified_positive_false_two χ v5 hv5 u2 rfl]
    exact fun e ↦ hχ2 (inv_eq_one.mp e)
  -- A local quasi-character agreeing with `c` on integer units and of abscissa zero.
  let σ0 : ℝ := if hσ : ∃ σ : ℝ, 0 < σ ∧ ∀ g : (L(ℚ, v5))ˣ, ‖c g‖ = ‖(g : L(ℚ, v5))‖ ^ σ then
    hσ.choose else 0
  let tw : QuasiCharacter (L(ℚ, v5))ˣ :=
    ⟨{ toFun := fun g ↦ ((‖(g : L(ℚ, v5))‖ ^ (-σ0) : ℝ) : ℂ)
       map_one' := by simp
       map_mul' := fun g g' ↦ by
         rw [Units.val_mul, norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _),
           Complex.ofReal_mul] },
      Complex.continuous_ofReal.comp ((continuous_norm.comp Units.continuous_val).rpow_const
        fun g ↦ Or.inl (norm_ne_zero_iff.mpr g.ne_zero))⟩
  let d : QuasiCharacter (L(ℚ, v5))ˣ := c * tw
  have hdg (g : (L(ℚ, v5))ˣ) : d g = c g * ((‖(g : L(ℚ, v5))‖ ^ (-σ0) : ℝ) : ℂ) := rfl
  have hdc : ∀ u ∈ U(ℚ, v5), d u = c u := fun u hu ↦ by
    rw [hdg, hunorm u hu, Real.one_rpow, Complex.ofReal_one, mul_one]
  have hdσ : ¬ ∃ σ : ℝ, 0 < σ ∧ ∀ g : (L(ℚ, v5))ˣ, ‖d g‖ = ‖(g : L(ℚ, v5))‖ ^ σ := by
    rintro ⟨σ, hσpos, hd⟩
    by_cases hσ : ∃ σ : ℝ, 0 < σ ∧ ∀ g : (L(ℚ, v5))ˣ, ‖c g‖ = ‖(g : L(ℚ, v5))‖ ^ σ
    · have hσ0 : σ0 = hσ.choose := dite_eq_left hσ
      let val : Valuation (L(ℚ, v5)) (WithZero (Multiplicative ℤ)) := Valued.v
      have hπ := val.exists_isUniformizer_of_isCyclic_of_nontrivial.choose_spec
      let π : (L(ℚ, v5))ˣ := Units.mk0 _ hπ.ne_zero
      have hπn : ‖(π : L(ℚ, v5))‖ = 5⁻¹ := by
        rw [Units.val_mk0, norm_uniformizer_adicCompletion v5 _ hπ,
          NumberFieldKB.Chebotarev.RatIdele.absNorm_asIdeal, hv5]
        norm_num
      have h1 := hd π
      rw [hdg, norm_mul, hσ.choose_spec.2 π, ← hσ0, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
        ← Real.rpow_add (norm_pos_iff.mpr π.ne_zero), add_neg_cancel, Real.rpow_zero, hπn] at h1
      have h2 : (5⁻¹ : ℝ) ^ σ < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hσpos
      linarith
    · have hσ0 : σ0 = 0 := dite_eq_right hσ
      refine hσ ⟨σ, hσpos, fun g ↦ ?_⟩
      rw [← hd g, hdg, hσ0, neg_zero, Real.rpow_zero, Complex.ofReal_one, mul_one]
  -- The printed formula and the corrected one disagree.
  have hP := h ℚ S hPic ω hω w d hcram
  have hT := (finiteStandardGaussian_zeta_of_ramified v5 c d hcram).2
  rw [ite_eq_left hdc] at hT
  rw [ite_eq_right (fun hh ↦ hdσ hh.2)] at hP
  have hpos : 0 < ((μ(ℚ, v5)) U(ℚ, v5)).toReal := by
    let : CompactSpace O(ℚ, v5) := compactSpace_adicCompletionIntegers v5
    let : BorelSpace (L(ℚ, v5))ˣ := ⟨rfl⟩
    let : (μ(ℚ, v5)).IsHaarMeasure := finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure v5
    exact ENNReal.toReal_pos ((Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)).measure_pos
      _ ⟨1, (O(ℚ, v5)).units.one_mem⟩).ne' (Submonoid.units_isCompact
        (isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v5))).measure_ne_top
  exact hpos.ne' (by exact_mod_cast hT.symm.trans hP)

-- The sum in (6.2.2.3) uses a list of norm-one representatives of the full class group.
local notation "ClassRepresentatives(" F ", " S ", " r ")" =>
  (r ⟨0, classNumber_pos F⟩ = 1 ∧
    Bijective (fun k ↦ ideleIdealClass F (sIdeleInsertion F S (r k).val)))

local notation "Lifts(" F ", " S ", " χ ", " ωₛ ")" =>
  (∀ (g : Nₛ(F, S)) (y : J₁(F, S)), y.val = QuotientGroup.mk g.val → χ g.val = ωₛ y)

open Classical in
/-- Paper: Theorem 6.2.2.1(1), (6.2.2.7)–(6.2.2.10), pp. 299–301. As printed: on pure tensors
of archimedean tests and punctured finite tests the norm-one integral (6.2.2.7) equals the product
of the archimedean operator (6.2.2.3) and the finite convolutions (6.2.2.4). This is the
pointwise identity asserted for the tensor extension. See
`sLocalStandardThetaTensor_toGlobal_openQuotient` and ERRATA F74. -/
def Printed.sLocalStandardThetaTensor_factorization : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (Places(F))),
    Subsingleton Picₛ(F, S) →
    ∀ (ω : PontryaginDual C₁(F)) (hω : NormOneCharacterUnramifiedOutside ω S)
      (χ : PontryaginDual Iₛ(F, S)),
      Lifts(F, S, χ, sLocalNormOneCharacter S ω hω) →
      ∀ (r : Fin (classNumber F) → Nₛ(F, S)), ClassRepresentatives(F, S, r) →
      ∀ (f : ℬ∞(F)) (fv : ∀ v : S, finitePuncturedThetaTestSpace v.val) (x : Iₛ(F, S)),
        let xArch := Units.map (RingHom.fst (InfiniteAdeleRing F) (∀ v : S, L(F, v.val))).toMonoidHom x
        let ins (v : S) := Units.map ((MonoidHom.inr (InfiniteAdeleRing F) _).comp
          (MonoidHom.mulSingle (fun v : S ↦ L(F, v.val)) v))
        (∫ g : Nₛ(F, S),
          let y := g.val⁻¹ * x
          f (Multiplicative.ofAdd y.val.1) *
            (∏ v : S, (fv v).val (Multiplicative.ofAdd (y.val.2 v))) * (χ g.val : ℂ)
          ∂sNormOneIdeleTamagawaMeasure F S) =
        infiniteStandardThetaAverage χ r f xArch *
          ∏ v : S, ∫ g : (L(F, v.val))ˣ,
            (fv v).val (Multiplicative.ofAdd ((g⁻¹).val * x.val.2 v)) * (χ (ins v g) : ℂ)
            ∂μ(F, v.val)

/-- Paper: Theorem 6.2.2.1(1), (6.2.2.7)–(6.2.2.10), pp. 299–301. Over ℚ take S with one finite
prime p, the trivial character, the identity class representative, and x = 1. Use the finite
indicator of `pℤₚˣ` and an even nonnegative smooth compactly supported function positive at ±1
and supported away from ±p. The norm-one integral is zero since the finite support forces the
inverse real component to have absolute value p. The separate factors are both positive. -/
theorem Printed.sLocalStandardThetaTensor_factorization_false :
    ¬ Printed.sLocalStandardThetaTensor_factorization := by sorry

/-- Paper: Theorem 6.2.2.1(1), (6.2.2.5), p. 299. As printed: the insertion with the fixed
standard finite tests induces a linear homeomorphism from the quotient by the kernel of the
inverse-argument archimedean average (6.2.2.3) to the S-local homogeneous theta quotient. The
fixed tensor line is expressed by insertion. See `sLocalStandardThetaTensor_quotient_equiv`
and ERRATA F75. -/
def Printed.sLocalStandardThetaTensor_inverseAverage_quotient_equiv : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (Places(F))),
    Subsingleton Picₛ(F, S) →
    ∀ (ω : PontryaginDual C₁(F)) (hω : NormOneCharacterUnramifiedOutside ω S)
      (χ : PontryaginDual Iₛ(F, S)),
      let ωₛ := sLocalNormOneCharacter S ω hω
      Lifts(F, S, χ, ωₛ) →
      ∀ (r : Fin (classNumber F) → Nₛ(F, S)), ClassRepresentatives(F, S, r) →
        let K := (infiniteStandardThetaAverage χ r).ker
        let c := sIdeleRestriction F S hω.choose
        ∃ e : (ℬ∞(F) ⧸ K) ≃L[ℂ] SLocalHomogeneousThetaSpace F S ωₛ,
          ∀ f : ℬ∞(F), e (K.mkQ f) = (sLocalHomogeneousAdelicThetaLinearMap F S ωₛ).ker.mkQ
            (sLocalStandardThetaTensor c f)

/-- Paper: Theorem 6.2.2.1(1), (6.2.2.5), p. 299. Take ℚ(i) at its complex stage, the
identity representative, `χ(z) = (z/|z|)^4` and `f(z) = z^4 exp(-|z|²)`. The character kills
the four global units and extends unramified at all finite places since the class group is
trivial. The inverse-argument average at 1 is the integral of `exp(-1)` on the circle. The
homogeneous theta average uses the positive argument, so its circle integrand has weight 8
and averages to zero. The proposed map sends the resulting nonzero source class to zero. -/
theorem Printed.sLocalStandardThetaTensor_inverseAverage_quotient_equiv_false :
    ¬ Printed.sLocalStandardThetaTensor_inverseAverage_quotient_equiv := by sorry

/-- Paper: Theorem 6.2.2.1(2), p. 299. As printed: the archimedean operator has semi-exponential
decay in the norm coordinate. This isolates the requirement of Definition B.2.1.1 that its
unweighted logarithmic profile be Schwartz, tested on the canonical norm section. See
`infiniteStandardThetaAverage_forwardDecay`, `infiniteStandardThetaAverage_logBound` and
ERRATA F76. -/
def Printed.infiniteStandardThetaAverage_schwartz_logProfile : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (Places(F))),
    Subsingleton Picₛ(F, S) →
    ∀ (ω : PontryaginDual C₁(F)) (hω : NormOneCharacterUnramifiedOutside ω S)
      (χ : PontryaginDual Iₛ(F, S)),
      Lifts(F, S, χ, sLocalNormOneCharacter S ω hω) →
      ∀ (r : Fin (classNumber F) → Nₛ(F, S)), ClassRepresentatives(F, S, r) →
      ∀ f : ℬ∞(F), ∃ φ : SchwartzMap ℝ ℂ, ∀ t : ℝ,
        let u : ℝ≥0ˣ := Units.mk0 (Real.toNNReal (Real.exp t))
          (Real.toNNReal_eq_zero.not.mpr (not_le_of_gt (Real.exp_pos t)))
        let x := Units.map (RingHom.fst (InfiniteAdeleRing F)
          (FiniteAdeleRing (𝓞 F) F)).toMonoidHom (canonicalIdeleNormSection F u)
        φ t = infiniteStandardThetaAverage χ r f x

private theorem infiniteStandardThetaAverage_ratGaussian : ∃ f : ℬ∞(ℚ), ∀ x : InfiniteAdeleRing ℚ,
    f (Multiplicative.ofAdd x) = (Real.exp (-Real.pi * ‖x Rat.infinitePlace‖ ^ 2) : ℂ) := by
  let e : Multiplicative (InfiniteAdeleRing ℚ) ≃ₜ* Multiplicative Rat.infinitePlace.Completion :=
    { Homeomorph.piUnique InfinitePlace.Completion with map_mul' := fun _ _ ↦ rfl }
  let s := infiniteStandardGaussian Rat.infinitePlace 1
  let : LocallyCompactSpace (Multiplicative (InfiniteAdeleRing ℚ)) :=
    inferInstanceAs (LocallyCompactSpace (InfiniteAdeleRing ℚ))
  let : LocallyCompactSpace (Multiplicative Rat.infinitePlace.Completion) :=
    inferInstanceAs (LocallyCompactSpace Rat.infinitePlace.Completion)
  let : T2Space (Multiplicative (InfiniteAdeleRing ℚ)) :=
    inferInstanceAs (T2Space ((v : InfinitePlace ℚ) → v.Completion))
  let : T2Space (Multiplicative Rat.infinitePlace.Completion) :=
    inferInstanceAs (T2Space Rat.infinitePlace.Completion)
  refine ⟨⟨_, schwartzBruhat_mem_comp_equiv e s.property⟩, fun x ↦ ?_⟩
  change infiniteStandardGaussianValue Rat.infinitePlace 1 (x Rat.infinitePlace) = _
  have hi := InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal Rat.isReal_infinitePlace
  have hn := hi.norm_map_of_map_zero (map_zero _) (x Rat.infinitePlace)
  simp [infiniteStandardGaussianValue, Rat.isReal_infinitePlace,
    ← hn, Real.norm_eq_abs, sq_abs]

private theorem infiniteStandardThetaAverage_ratNormOne (g : Nₛ(ℚ, ∅)) :
    ‖g.val.val.1 Rat.infinitePlace‖ = 1 := by
  simpa [MonoidHom.mem_ker.mp g.property] using (rat_sIdeleNorm_eq ∅ g.val).symm

private theorem infiniteStandardThetaAverage_ratFinite : Finite Nₛ(ℚ, ∅) := by
  classical
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
  let c (g : Nₛ(ℚ, ∅)) := e (g.val.val.1 Rat.infinitePlace)
  have hi := InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal Rat.isReal_infinitePlace
  have hc (g : Nₛ(ℚ, ∅)) : |c g| = 1 :=
    (hi.norm_map_of_map_zero (map_zero _) _).trans (infiniteStandardThetaAverage_ratNormOne g)
  let signs : Finset ℝ := {1, -1}
  have hmem (g : Nₛ(ℚ, ∅)) : c g ∈ signs := by
    simpa [signs] using (abs_eq (zero_le_one : (0 : ℝ) ≤ 1)).mp (hc g)
  apply Finite.of_injective (fun g : Nₛ(ℚ, ∅) ↦ (⟨c g, hmem g⟩ : signs))
  intro g h eq
  apply Subtype.ext
  apply Units.ext
  apply Prod.ext _ (Subsingleton.elim _ _)
  funext v
  obtain rfl := Subsingleton.elim v Rat.infinitePlace
  exact e.injective (congrArg Subtype.val eq)

private theorem infiniteStandardThetaAverage_ratGaussian_apply (f : ℬ∞(ℚ))
    (hf : ∀ x : InfiniteAdeleRing ℚ, f (Multiplicative.ofAdd x) =
      (Real.exp (-Real.pi * ‖x Rat.infinitePlace‖ ^ 2) : ℂ))
    (x : (InfiniteAdeleRing ℚ)ˣ) :
    infiniteStandardThetaAverage (F := ℚ) (S := ∅) 1 (fun _ ↦ 1) f x =
      (sNormOneIdeleTamagawaMeasure ℚ ∅).real Set.univ •
        (Real.exp (-Real.pi * ‖x.val Rat.infinitePlace‖ ^ 2) : ℂ) := by
  classical
  have : Subsingleton (Fin (classNumber ℚ)) := by
    rw [Rat.classNumber_eq]
    infer_instance
  rw [infiniteStandardThetaAverage_apply, Fintype.sum_subsingleton _ ⟨0, classNumber_pos ℚ⟩,
    ← integral_const]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro g
  simp only [Subgroup.coe_one, map_one, one_mul, PontryaginDual.one_apply, Circle.coe_one,
    mul_one, hf]
  let v := Units.map (Pi.evalRingHom InfinitePlace.Completion Rat.infinitePlace).toMonoidHom
  let a := Units.map (RingHom.fst (InfiniteAdeleRing ℚ)
    (∀ p : (∅ : Finset Places(ℚ)), L(ℚ, p.val))).toMonoidHom g.val
  have harg : ‖(a⁻¹ * x).val Rat.infinitePlace‖ = ‖x.val Rat.infinitePlace‖ := by
    change ‖(v (a⁻¹ * x)).val‖ = _
    rw [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, norm_mul, norm_inv]
    change ‖g.val.val.1 Rat.infinitePlace‖⁻¹ * ‖x.val Rat.infinitePlace‖ = _
    rw [infiniteStandardThetaAverage_ratNormOne, inv_one, one_mul]
  rw [harg]

private theorem infiniteStandardThetaAverage_ratSection_norm (u : ℝ≥0ˣ) :
    ‖(canonicalIdeleNormSection ℚ u).val.1 Rat.infinitePlace‖ = (u.val : ℝ) := by
  have hi := InfinitePlace.Completion.isometry_extensionEmbedding Rat.infinitePlace
  have hn := hi.norm_map_of_map_zero (map_zero _) ((canonicalIdeleNormSection ℚ u).val.1 Rat.infinitePlace)
  rw [← hn, canonicalIdeleNormSection_infinite]
  simp

/-- Paper: Theorem 6.2.2.1(2), pp. 299, 302. Over ℚ at the archimedean stage, take the
trivial character, the identity representative and the real Gaussian `exp(-πx²)`. Its unweighted
logarithmic profile is a positive constant times `exp(-π exp(2t))`, which has a nonzero limit
as t tends to negative infinity. -/
theorem Printed.infiniteStandardThetaAverage_schwartz_logProfile_false :
    ¬ Printed.infiniteStandardThetaAverage_schwartz_logProfile := by
  classical
  intro h
  have hω : NormOneCharacterUnramifiedOutside (F := ℚ) 1 ∅ :=
    ⟨⟨1, (mem_unramifiedOutside_iff ℚ ∅ 1).mpr (fun _ _ _ ↦ rfl)⟩, fun _ ↦ rfl⟩
  have hchar : sLocalNormOneCharacter (F := ℚ) ∅ 1 hω = 1 := by
    let hu := (normOneCharacterUnramifiedOutside_iff (F := ℚ) 1).mp hω
    exact hu.unique hu.exists.choose_spec (fun _ _ _ _ _ ↦ rfl)
  have : IsPrincipalIdealRing (𝓞 ℚ) := classNumber_eq_one_iff.mp Rat.classNumber_eq
  have hPic : Subsingleton Picₛ(ℚ, (∅ : Finset Places(ℚ))) := by
    rw [Finset.coe_empty, integer_empty]
    let e := Algebra.botEquivOfInjective (IsFractionRing.injective (𝓞 ℚ) ℚ)
    let := IsPrincipalIdealRing.of_surjective e.symm e.symm.surjective
    infer_instance
  have : Subsingleton (Fin (classNumber ℚ)) := by
    rw [Rat.classNumber_eq]
    infer_instance
  have : Nonempty (Fin (classNumber ℚ)) := ⟨⟨0, classNumber_pos ℚ⟩⟩
  obtain ⟨f, hf⟩ := infiniteStandardThetaAverage_ratGaussian
  obtain ⟨φ, hφ⟩ := h ℚ ∅ hPic 1 hω 1 (by simp [hchar]) (fun _ ↦ 1)
    ⟨rfl, bijective_of_subsingleton' _⟩ f
  let μ := sNormOneIdeleTamagawaMeasure ℚ ∅
  have haar := (sNormOneIdeleTamagawaMeasure_existsUnique ℚ ∅).exists.choose_spec.1
  have : Finite Nₛ(ℚ, ∅) := infiniteStandardThetaAverage_ratFinite
  have : CompactSpace Nₛ(ℚ, ∅) := Finite.compactSpace
  have hm : (μ.real Set.univ : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    exact (ENNReal.toReal_pos (haar.open_pos Set.univ isOpen_univ Set.univ_nonempty)
      (haar.lt_top_of_isCompact isCompact_univ).ne).ne'
  have hval (t : ℝ) : φ t =
      (μ.real Set.univ : ℂ) * (Real.exp (-Real.pi * Real.exp t ^ 2) : ℂ) := by
    rw [hφ, infiniteStandardThetaAverage_ratGaussian_apply f hf]
    simp [infiniteStandardThetaAverage_ratSection_norm, Units.coe_map,
      Real.toNNReal_of_nonneg (Real.exp_pos t).le, Algebra.smul_def, μ]
  have hlim : Filter.Tendsto φ Filter.atBot (𝓝 (μ.real Set.univ : ℂ)) := by
    have hc : Continuous (fun s : ℝ ↦ (μ.real Set.univ : ℂ) *
        (Real.exp (-Real.pi * s ^ 2) : ℂ)) := by fun_prop
    rw [funext hval]
    simpa [Function.comp_def] using (hc.tendsto 0).comp Real.tendsto_exp_atBot
  exact hm (tendsto_nhds_unique hlim (φ.tendsto_cocompact.mono_left atBot_le_cocompact))

end StandardFunctions

end RiemannMasullo
