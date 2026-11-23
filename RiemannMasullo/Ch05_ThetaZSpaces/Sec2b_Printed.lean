module

public import RiemannMasullo.Ch05_ThetaZSpaces.Sec2b
import RiemannMasullo.ForMathlib.Topology.Algebra.PontryaginDual.Separation
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace

/-!
# Chapter 5.2.3–5.2.4: statements that are false as printed

The printed claims are propositions, with separate statements of their negations.
The corresponding theta-space results are in `Sec2b.lean`, and `ERRATA.md` records the errors.
-/

@[expose] public noncomputable section

namespace RiemannMasullo

open IsDedekindDomain NumberField
open scoped NumberField.AdeleRing

local notation "Places(" F ")" => HeightOneSpectrum (𝓞 F)
local notation "Test(" F ", " S ")" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "GlobalTest(" F ")" => SchwartzBruhat (Multiplicative 𝔸[F])

open Classical in
/-- Paper: Theorem 5.2.3.1, (5.2.3.4), p. 233.
The displayed formula gives one geometric Euler factor per place added to S on insertion into T.
Deviation: We read the two-argument `L_T` as the test-function transform `Z_T` of §5.1 and
record (5.2.3.4) as an identity of transforms for arbitrary tests. The proof invokes it
under source-kernel vanishing on p. 233 and target-kernel vanishing on p. 234. The missing
mass affects the identity but cancels in both kernel arguments. Global extensions
parametrize the indicated local components, and equality is tested at common regular values.
See ERRATA F26 and I96. The mass correction appears in
`weilIdentity_unramifiedOutside_meromorphic`, and
`sLocalHomogeneousThetaTransition_preserves_kernel` gives the kernel implication.
-/
def Printed.sLocalIdelicMellin_transition : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S T : Finset (Places(F))) (hST : S ⊆ T)
    (f : Test(F, S)) (c : unramifiedOutside F S)
    (π : (v : Places(F)) → (v.adicCompletion F)ˣ),
    (∀ v ∈ T \ S, (Valued.v :
      Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).IsUniformizer (π v).val) →
    let cS := sIdeleRestriction F S c
    let cT := sIdeleRestriction F T ⟨c.val, fun v hv ↦ c.property v (fun h ↦ hv (hST h))⟩
    0 ≤ sLocalIdelicOrderBound (F := F) (S := S) cS →
    0 ≤ sLocalIdelicOrderBound (F := F) (S := T) cT →
    (∀ v ∈ T \ S, finitePlaceRestriction F v c.val (π v) ≠ 1) →
    sLocalIdelicZFunction (F := F) (S := T) (sAdeleSchwartzTransition F hST f) cT =
      sLocalIdelicZFunction (F := F) (S := S) f cS *
        ∏ v ∈ T \ S, (1 - finitePlaceRestriction F v c.val (π v))⁻¹

/-- Paper: Theorem 5.2.3.1, (5.2.3.4), p. 233.
Take F = ℚ(i), S consisting of the complex place, and T adding the place v above 2.
Use the Gaussian z ↦ exp(−2π|z|²), the square of the idelic norm, and the uniformizer 1 + i
at v. The local value of the quasi-character there is 1/4. Summing the valuation shells of
the inserted integer indicator gives the claimed Euler factor times the unit mass 1/2.
The archimedean integral is positive, and the square of the norm is in the convergence region.
-/
theorem Printed.sLocalIdelicMellin_transition_false :
    ¬ Printed.sLocalIdelicMellin_transition := by
  sorry

/-- Paper: Introduction to Proposition 5.2.3.2, (5.2.3.9), pp. 235–236.
As printed: for every number field, every finite stage containing the archimedean places,
and every character of the respective norm-one group, the global and S-local Pettis averages
are projectors. This records the idempotence asserted by the word “projectors.”
The averages and their quotient identifications are given by
`existsUnique_globalThetaIsotypicAverage`, `existsUnique_sLocalThetaIsotypicAverage`,
`globalThetaIsotypicAverage_equiv` and `sLocalThetaIsotypicAverage_equiv`.
`compactActionAverage_idempotent` gives idempotence after normalization. See ERRATA F27.
-/
def Printed.thetaIsotypicAverage_idempotent : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (Places(F))),
    (∀ ω : PontryaginDual (ideleClassNorm F).ker,
      let P := (existsUnique_globalThetaIsotypicAverage (F := F) ω).exists.choose
      P.comp P = P) ∧
    (∀ χ : PontryaginDual (sIdeleQuotientNorm F S).ker,
      let P := (existsUnique_sLocalThetaIsotypicAverage (F := F) (S := S) χ).exists.choose
      P.comp P = P)

/-- Paper: Introduction to Proposition 5.2.3.2, (5.2.3.9), pp. 235–236.
Take F = ℚ(i), the trivial character, and, locally, S consisting of the complex place.
The Gaussian z ↦ exp(−2π|z|²) gives a nonzero fixed theta class, with the finite integer
indicator in the global case. Since ℚ(i) has class number one, every global norm-one class
has a representative with complex modulus one and integer units at all finite places.
On fixed vectors the averages act by π/4 globally and π/2 locally, so applying either twice
multiplies the class by the square of that mass.
-/
theorem Printed.thetaIsotypicAverage_idempotent_false :
    ¬ Printed.thetaIsotypicAverage_idempotent := by
  sorry

/-- Paper: Remark 5.2.3.4(1)–(2), p. 237.
As printed: for every number field and finite stage containing the archimedean places,
the topologies on global and S-local test functions induced by the theta maps are Hausdorff.
This records the Hausdorff assertions in the two closure statements.
`globalThetaKernel_eq_induced_closure` and `sLocalThetaKernel_eq_induced_closure`
give the closure identities with the indicated pullback topologies. See ERRATA F28.
-/
def Printed.thetaInducedTopology_t2 : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (Places(F))),
    let q := (LinearMap.ker (adelicThetaLinearMap F)).mkQ
    let qS := (LinearMap.ker (sLocalAdelicTheta F S)).mkQ
    @T2Space (GlobalTest(F)) (TopologicalSpace.induced q inferInstance) ∧
    @T2Space (Test(F, S)) (TopologicalSpace.induced qS inferInstance)

/-- In the topology induced by a map, a Hausdorff space identifies points with equal images. -/
private theorem thetaInducedTopology_t2_false_eq {X Y : Type*} [t : TopologicalSpace Y]
    (q : X → Y) (h : @T2Space X (TopologicalSpace.induced q t)) {a b : X} (hab : q a = q b) :
    a = b := by
  let : TopologicalSpace X := TopologicalSpace.induced q t
  exact Inseparable.eq (show nhds a = nhds b by rw [nhds_induced, nhds_induced, hab])

open scoped RestrictedProduct in
/-- The rational adeles are a nontrivial Hausdorff locally compact group. -/
private theorem thetaInducedTopology_t2_false_adeles :
    Nontrivial 𝔸[ℚ] ∧ T2Space (Multiplicative 𝔸[ℚ]) ∧
      LocallyCompactSpace (Multiplicative 𝔸[ℚ]) := by
  let (v : Places(ℚ)) : CompactSpace (v.adicCompletionIntegers ℚ) :=
    compactSpace_adicCompletionIntegers v
  let : Fact (∀ v : Places(ℚ), IsOpen (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))) :=
    ⟨fun v ↦ Valued.isOpen_valuationSubring _⟩
  refine ⟨?_, ?_, ?_⟩
  · change Nontrivial (InfiniteAdeleRing ℚ ×
      (Πʳ v : Places(ℚ), [v.adicCompletion ℚ, v.adicCompletionIntegers ℚ]))
    infer_instance
  · change T2Space (((v : InfinitePlace ℚ) → v.Completion) ×
      (Πʳ v : Places(ℚ), [v.adicCompletion ℚ, v.adicCompletionIntegers ℚ]))
    infer_instance
  · change LocallyCompactSpace (InfiniteAdeleRing ℚ ×
      (Πʳ v : Places(ℚ), [v.adicCompletion ℚ, v.adicCompletionIntegers ℚ]))
    infer_instance

/-- The global theta function of a test does not change under pullback by negation:
the principal multiples are reindexed by `ξ ↦ -ξ`. -/
private theorem thetaInducedTopology_t2_false_neg (f : GlobalTest(ℚ)) :
    adelicTheta (schwartzBruhatUnitTranslate (-1) f) = adelicTheta f := by
  ext c
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
  rw [adelicTheta_mk, adelicTheta_mk]
  refine (tsum_congr fun ξ ↦ ?_).trans ((Equiv.neg ℚˣ).tsum_eq
    (fun ξ : ℚˣ ↦ f (Multiplicative.ofAdd (algebraMap ℚ 𝔸[ℚ] (ξ : ℚ) * g.val))))
  rw [schwartzBruhatUnitTranslate_apply]
  simp [Units.val_neg, map_neg]

/-- Paper: Remark 5.2.3.4(1)–(2), p. 237.
For F = ℚ use the odd real test x ↦ x exp(−πx²), at S consisting of the real place
and globally tensored with the indicator of the finite integer adeles. Each test is nonzero,
and the terms at opposite nonzero rational elements cancel at every global idele.
The real-stage sum pairs the terms at the two units ±1. Each theta map sends its test
and zero to the same point, so the pullback topology cannot separate them.
-/
theorem Printed.thetaInducedTopology_t2_false : ¬ Printed.thetaInducedTopology_t2 := by
  classical
  intro h
  have hG := (h ℚ ∅).1
  obtain ⟨_, _, _⟩ := thetaInducedTopology_t2_false_adeles
  let x : Multiplicative 𝔸[ℚ] := Multiplicative.ofAdd 1
  let y : Multiplicative 𝔸[ℚ] := Multiplicative.ofAdd (-1)
  have hxy : x ≠ y := by
    intro hxy
    have h1 : (1 : 𝔸[ℚ]) = -1 := congrArg Multiplicative.toAdd hxy
    have h2 : algebraMap ℚ 𝔸[ℚ] 1 = algebraMap ℚ 𝔸[ℚ] (-1) := by simpa using h1
    have := (algebraMap ℚ 𝔸[ℚ]).injective h2
    norm_num at this
  obtain ⟨δ, hδ, hvan, -⟩ := schwartzBruhat_dirac_support x
  have hex : ∃ f : GlobalTest(ℚ), tsupport (f : Multiplicative 𝔸[ℚ] → ℂ) ⊆ {y}ᶜ ∧ f x ≠ 0 := by
    by_contra! hc
    have hmem : x ∈ schwartzBruhatVanishingLocus δ :=
      ⟨{y}ᶜ, ⟨isOpen_compl_singleton, fun f hf ↦ (hδ f).trans (hc f hf)⟩, hxy⟩
    rw [hvan] at hmem
    exact hmem rfl
  obtain ⟨f, hfs, hfx⟩ := hex
  have hfy : f y = 0 := image_eq_zero_of_notMem_tsupport (fun hy ↦ hfs hy rfl)
  let d : GlobalTest(ℚ) := f - schwartzBruhatUnitTranslate (-1) f
  have hdx : d x = f x := by
    have e : schwartzBruhatUnitTranslate (-1) f x = f y := by
      change schwartzBruhatUnitTranslate (-1) f (Multiplicative.ofAdd 1) = _
      rw [schwartzBruhatUnitTranslate_apply]
      simp [y]
    change f x - schwartzBruhatUnitTranslate (-1) f x = f x
    rw [e, hfy, sub_zero]
  have hd0 : d ≠ 0 := by
    intro hd
    apply hfx
    rw [← hdx, hd]
    rfl
  have hker : d ∈ LinearMap.ker (adelicThetaLinearMap ℚ) := by
    rw [LinearMap.mem_ker, map_sub, adelicThetaLinearMap_apply, adelicThetaLinearMap_apply,
      thetaInducedTopology_t2_false_neg, sub_self]
  have hq : (LinearMap.ker (adelicThetaLinearMap ℚ)).mkQ d =
      (LinearMap.ker (adelicThetaLinearMap ℚ)).mkQ 0 := by
    rw [map_zero]
    exact (Submodule.Quotient.mk_eq_zero _).2 hker
  exact hd0 (thetaInducedTopology_t2_false_eq _ hG hq)

/-- Paper: §5.2.4, introduction to Theorem 5.2.4.1, p. 238.
The introduction says that the local Fourier maps tend to “the inversion automorphism”
on the global theta space. We record the existence of the named target automorphism.
Deviation: We read inversion as pullback of theta functions by `g ↦ g⁻¹` on idele classes.
`existsUnique_globalThetaFourier` gives the Fourier automorphism, whose action on theta values
is governed by `adelicTheta_riemannRoch`. See ERRATA F29.
-/
def Printed.globalTheta_inversionAutomorphism : Prop :=
  ∀ (F : Type) [Field F] [NumberField F],
    let K := LinearMap.ker (adelicThetaLinearMap F)
    let theta := K.liftQ (adelicThetaLinearMap F) le_rfl
    ∃ J : GlobalAdelicThetaSpace F ≃L[ℂ] GlobalAdelicThetaSpace F,
      ∀ (f : GlobalTest(F)) (g : IdeleClassGroup (𝓞 F) F),
        theta (J (K.mkQ f)) g = adelicTheta f g⁻¹

/-- Paper: §5.2.4, introduction to Theorem 5.2.4.1, p. 238.
Take F = ℚ and the self-dual test exp(−πx²) times the indicator of the finite integer adeles.
On the idele with real component t > 0 and finite components 1, its inverted theta value
is asymptotic to t as t tends to infinity. Every global theta function decays there by
`adelicTheta_decay_large`, so the inverted function cannot represent a global theta class.
-/
theorem Printed.globalTheta_inversionAutomorphism_false :
    ¬ Printed.globalTheta_inversionAutomorphism := by
  classical
  intro h
  obtain ⟨f, hf⟩ := (adelePolarValues_surjective (F := ℚ)) (0, 1)
  have hf0 : f (Multiplicative.ofAdd (0 : 𝔸[ℚ])) = 0 := congrArg Prod.fst hf
  have hf1 : adeleSchwartzFourier f (Multiplicative.ofAdd (0 : 𝔸[ℚ])) = 1 := congrArg Prod.snd hf
  obtain ⟨J, hJ⟩ := h ℚ
  let K := LinearMap.ker (adelicThetaLinearMap ℚ)
  obtain ⟨d, hd⟩ := Submodule.mkQ_surjective K (J (K.mkQ f))
  have heq (g : IdeleClassGroup (𝓞 ℚ) ℚ) : adelicTheta d g = adelicTheta f g⁻¹ := by
    have hh := hJ f g
    change (K.liftQ (adelicThetaLinearMap ℚ) le_rfl) (J (K.mkQ f)) g = _ at hh
    have hd' := congrArg (fun x => (K.liftQ (adelicThetaLinearMap ℚ) le_rfl) x g) hd
    exact hd'.trans hh
  obtain ⟨C, T, hC, hT, hsmall⟩ := adelicTheta_decay_small f 0
  obtain ⟨D, U, hD, hU, hlarge⟩ := adelicTheta_decay_large d 0
  let r : ℝ := max (max (C + D + 1) U) (T⁻¹) + 1
  have hr : 0 < r := by dsimp [r]; positivity
  have hrU : U < r := by
    dsimp [r]
    linarith [le_max_right (C + D + 1) U, le_max_left (max (C + D + 1) U) T⁻¹]
  have hrT : T⁻¹ < r := by
    dsimp [r]
    linarith [le_max_right (max (C + D + 1) U) T⁻¹]
  have hrCD : C + D < r := by
    dsimp [r]
    linarith [le_max_left (C + D + 1) U, le_max_left (max (C + D + 1) U) T⁻¹]
  let t : Units NNReal := Units.mk0 (⟨r, hr.le⟩ : NNReal)
    (by intro h; exact hr.ne' (congrArg NNReal.toReal h))
  let g : IdeleClassGroup (𝓞 ℚ) ℚ := QuotientGroup.mk (canonicalIdeleNormSection ℚ t)
  have hn : ((ideleClassNorm ℚ g : NNReal) : ℝ) = r := by
    change ((ideleNorm ℚ (canonicalIdeleNormSection ℚ t) : NNReal) : ℝ) = r
    rw [canonicalIdeleNormSection_rightInverse]
    rfl
  have hni : ((ideleClassNorm ℚ g⁻¹ : NNReal) : ℝ) = r⁻¹ := by
    simp only [map_inv, Units.val_inv_eq_inv_val, NNReal.coe_inv, hn]
  have hsm : ((ideleClassNorm ℚ g⁻¹ : NNReal) : ℝ) < T := by
    rw [hni]
    exact (inv_lt_comm₀ hr hT).2 hrT
  have hs := hsmall g⁻¹ hsm
  have hl := hlarge g (by change U < ((ideleClassNorm ℚ g : NNReal) : ℝ); rw [hn]; exact hrU)
  dsimp only at hs
  rw [hni, inv_inv, hf0, hf1] at hs
  simp only [Complex.real_smul, mul_one, add_zero, pow_zero] at hs
  simp only [pow_zero, inv_one, mul_one] at hl
  rw [heq] at hl
  have hb : r ≤ ‖adelicTheta f g⁻¹‖ + C := by
    have hh := norm_le_norm_add_norm_sub (adelicTheta f g⁻¹) (r : ℂ)
    simp only [Complex.norm_real, Real.norm_of_nonneg hr.le] at hh
    linarith
  linarith

/-- Paper: Theorem 5.2.4.1(1)–(2), (5.2.4.2) and (5.2.4.4), p. 239.
As printed: for every number field and every pair of nested finite stages containing the
archimedean places, Fourier on the theta quotients commutes with stage enlargement and
with insertion into the global theta quotient. This records the two insertion assertions.
See ERRATA F30. The repaired statements are `sLocalThetaFourier_transition` and
`sLocalThetaFourier_toGlobal`, with restrictions at places dividing the different.
-/
def Printed.thetaFourier_insertion : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (Places(F))),
    let fourierS := (existsUnique_sLocalThetaFourier (F := F) (S := S)).exists.choose
    let fourier := (existsUnique_globalThetaFourier (F := F)).exists.choose
    (∀ (T : Finset (Places(F))) (hST : S ⊆ T) (x : SLocalAdelicThetaSpace F S),
      let fourierT := (existsUnique_sLocalThetaFourier (F := F) (S := T)).exists.choose
      let transition := sLocalThetaTransition (F := F) hST
      fourierT (transition x) = transition (fourierS x)) ∧
    (∀ x : SLocalAdelicThetaSpace F S,
      fourier (sLocalThetaToGlobal F S x) = sLocalThetaToGlobal F S (fourierS x))

/-- Paper: Theorem 5.2.4.1(1)–(2), (5.2.4.2) and (5.2.4.4), p. 239.
For F = ℚ(i), let S consist of the complex place and T add the place v above 2.
Choose the archimedean Fourier image to be a smooth bump equal to 1 at 1/2, with support
meeting (1/2)ℤ[i] only at 1/2. Fourier after insertion replaces the integer indicator at v
by half the indicator of (1/2)O_v, so the theta value at the identity is 1/2, from the
single term at 1/2. Insertion after Fourier uses the integer indicator and gives zero.
The same values hold after passage to the global theta space.
-/
theorem Printed.thetaFourier_insertion_false : ¬ Printed.thetaFourier_insertion := by
  sorry

/-- Paper: Theorem 5.2.4.1(1)–(2), p. 239.
As printed: for every number field, every finite stage containing the archimedean places,
and every continuous global norm-one character, the descended local character used in the
isotype assertions exists. This records the existence required by the printed scope.
The descent criterion is `normOneCharacterUnramifiedOutside_iff`, and
`sLocalThetaFourier_mem_isotype` states exchange for local characters. See ERRATA F31.
-/
def Printed.exists_sLocalNormOneCharacter : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (Places(F)))
    (ω : PontryaginDual (ideleClassNorm F).ker),
    ∃ χ : PontryaginDual (sIdeleQuotientNorm F S).ker,
      ∀ (u : (integralAdelesOutside F S)ˣ) (x : (ideleClassNorm F).ker)
        (y : (sIdeleQuotientNorm F S).ker),
        let g := integralIdeleInsertion F S u
        x.val = QuotientGroup.mk g →
        y.val = QuotientGroup.mk (Units.map (adeleProjection F S).toMonoidHom g) →
        χ y = ω x

/-- Paper: Theorem 5.2.4.1(1)–(2), p. 239.
Take F = ℚ, S consisting of the real place, and the quadratic character modulo 3.
The idele with component −1 at 3 and 1 everywhere else is a unit outside S and has norm
one. Its S-projection is the identity, while the global character takes value −1 there.
-/
theorem Printed.exists_sLocalNormOneCharacter_false :
    ¬ Printed.exists_sLocalNormOneCharacter := by
  classical
  let S : Finset (HeightOneSpectrum (𝓞 ℚ)) := ∅
  -- The single nontrivial finite component can be placed at any finite place.
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 ℚ)
  let v : HeightOneSpectrum (𝓞 ℚ) := ⟨m, hm.isPrime, NeZero.ne m⟩
  let g := IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v (-1)
  have hself : g.val.2 v = -1 := RestrictedProduct.mulSingle_eq_same _ _ _
  have hoff (w : HeightOneSpectrum (𝓞 ℚ)) (hw : w ≠ v) : g.val.2 w = 1 :=
    RestrictedProduct.mulSingle_eq_of_ne _ _ hw
  have hinv : g⁻¹ = g := by simp [g, ← map_inv]
  have hmem : g ∈ (integralIdeleInsertion ℚ S).range := by
    apply (mem_range_integralIdeleInsertion ℚ S g).2
    intro w _
    have hw : g.val.2 w ∈ w.adicCompletionIntegers ℚ := by
      rcases eq_or_ne w v with rfl | h
      · rw [hself]
        exact neg_mem (one_mem _)
      · rw [hoff _ h]
        exact one_mem _
    exact ⟨hw, by change (g⁻¹).val.2 w ∈ _; rwa [hinv]⟩
  obtain ⟨u, hu⟩ := hmem
  have hproj : Units.map (adeleProjection ℚ S).toMonoidHom g = 1 := by
    apply Units.ext
    exact Prod.ext rfl (funext fun w ↦ (Finset.notMem_empty w.val w.property).elim)
  let c := IdeleClassGroup.ofAdicCompletion (𝓞 ℚ) ℚ v (-1)
  have hc : c ∈ (ideleClassNorm ℚ).ker := by
    change ideleClassNorm ℚ (IdeleClassGroup.ofAdicCompletion (𝓞 ℚ) ℚ v (-1)) = 1
    rw [ideleClassNorm_ofAdicCompletion]
    apply Units.ext
    change ‖(-1 : v.adicCompletion ℚ)‖₊ = 1
    simp
  let x : (ideleClassNorm ℚ).ker := ⟨c, hc⟩
  have hne : x ≠ 1 := by
    intro hx
    have he : QuotientGroup.mk g = (1 : IdeleClassGroup (𝓞 ℚ) ℚ) := congrArg Subtype.val hx
    obtain ⟨q, hq⟩ := (QuotientGroup.eq_one_iff g).mp he
    -- A principal representative with infinite component 1 must come from 1.
    have hreal : algebraMap ℚ (InfiniteAdeleRing ℚ) q.val = 1 :=
      congrArg (fun a : 𝔸[ℚ]ˣ ↦ a.val.1) hq
    have hq1 : q = 1 := Units.ext ((algebraMap ℚ (InfiniteAdeleRing ℚ)).injective
      (hreal.trans (map_one _).symm))
    rw [hq1, map_one] at hq
    have hcontra : (1 : v.adicCompletion ℚ) = -1 :=
      (congrArg (fun a : 𝔸[ℚ]ˣ ↦ a.val.2 v) hq).trans hself
    have : (1 : ℚ) = -1 := (algebraMap ℚ (v.adicCompletion ℚ)).injective
      (by simpa only [map_one, map_neg] using hcontra)
    norm_num at this
  -- Separate the global class from 1; no local character can do so after projection.
  let : T2Space (ideleClassNorm ℚ).ker := (ideleClassGroup_finiteness ℚ).2.2.1
  let : CompactSpace (ideleClassNorm ℚ).ker := (ideleClassGroup_finiteness ℚ).2.1
  obtain ⟨ω, hω⟩ := exists_pontryaginDual_apply_ne_one (G := (ideleClassNorm ℚ).ker) hne
  intro h
  obtain ⟨χ, hχ⟩ := h ℚ S ω
  apply hω
  have h := hχ u x 1 (by rw [hu]; rfl) (by rw [hu, hproj]; rfl)
  simpa using h.symm

end RiemannMasullo
