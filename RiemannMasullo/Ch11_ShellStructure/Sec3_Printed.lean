module

public import Mathlib.NumberTheory.Cyclotomic.Basic
public import RiemannMasullo.Ch10_TraceSpectral.Sec4b
public import RiemannMasullo.Ch11_ShellStructure.Sec3

import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import RiemannMasullo.AppA_AlgebraicNT.Sec2
import RiemannMasullo.Ch05_ThetaZSpaces.Sec3a
import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.Ch11_ShellStructure.Sec1a

/-! # False printed claims from §11.3 -/

@[expose] public noncomputable section

open Function IsDedekindDomain MeasureTheory NumberField Set
open scoped Classical NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 instIdeleMeasurableSpaceSec1a instMeasurableSpaceAdicUnitsSec3a

/-- Paper: §11.3.1.1, p. 493. As printed, the unit conditions at all places above
the first k rational primes define the full preimage of the corresponding rational
stratum under the idelic norm. The base satisfies the conditions on pp. 491–492. -/
def Printed.primaryDivisorialStratum_eq_norm_preimage : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
    (S : Finset (HeightOneSpectrum (𝓞 F))),
    (∀ v ∈ S, ∀ w : HeightOneSpectrum (𝓞 F), w.under (𝓞 ℚ) = v.under (𝓞 ℚ) → w ∈ S) →
    (∀ v ∉ S, v.asIdeal.ramificationIdx (𝓞 ℚ) = 1) →
    (∀ v ∉ S, (ideleClassNormTwist χ 0).IsUnramifiedAt v) →
    Subsingleton (CommRing.Pic ((S : Set (HeightOneSpectrum (𝓞 F))).integer F)) →
    ∀ k : ℕ,
      let T := (Finset.range k).image fun j ↦
        Rat.HeightOneSpectrum.primesEquiv.symm ⟨Nat.nth Nat.Prime j, Nat.prime_nth_prime j⟩
      divisorialStratum F (T.biUnion fun p ↦ (finite_nuclearityPlacesAbove (F := F) p).toFinset) =
        (relativeIdeleNormRat F) ⁻¹' divisorialStratum ℚ T

local notation "V(" F ")" => HeightOneSpectrum (𝓞 F)
local notation "Vℚ" => HeightOneSpectrum (𝓞 ℚ)
local notation "I(" F ")" => IdeleGroup (𝓞 F) F
local notation "C(" F ")" => IdeleClassGroup (𝓞 F) F
local notation "N(" F ")" => (ideleNorm F).ker
local notation "classOf(" F ")" => QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 F) F)
local notation "above(" F ", " p ")" => (finite_nuclearityPlacesAbove (F := F) p).toFinset
local notation "πclass(" F ", " v ", " π ")" => IdeleClassGroup.ofAdicCompletion (𝓞 F) F v π
local notation "unitMass(" F ", " v ")" =>
  (finiteLocalMultiplicativeTamagawaMeasure F v).real ((v).adicCompletionIntegers F).units
local notation "ramificationIndex(" v ")" => (v).asIdeal.ramificationIdx (𝓞 ℚ)

private theorem uniformizerExists {F : Type} [Field F] [NumberField F] (v : V(F)) :
    ∃ π : (v.adicCompletion F)ˣ, Valued.v.IsUniformizer (π : v.adicCompletion F) := by
  let val : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
  obtain ⟨π, hπ⟩ : ∃ π : v.adicCompletionIntegers F, val.IsUniformizer (π : v.adicCompletion F) :=
    val.exists_isUniformizer_of_isCyclic_of_nontrivial
  exact ⟨Units.mk0 π.val hπ.ne_zero, hπ⟩

private theorem finitePlaceNorm_eq_one {F : Type} [Field F] [NumberField F]
    (v : V(F)) (x : v.adicCompletion F) : ‖x‖ = 1 ↔ Valued.v x = 1 := by
  rw [FinitePlace.norm_def, NNReal.coe_eq_one,
    WithZeroMulInt.toNNReal_eq_one_iff _ _ (HeightOneSpectrum.one_lt_absNorm_nnreal v).ne']

private theorem splitPrime_norm_cancellation {F : Type} [Field F] [NumberField F]
    {p : Vℚ} {v w : V(F)} (hvw : v ≠ w) (hv : v.under (𝓞 ℚ) = p)
    (hw : w.under (𝓞 ℚ) = p) (hNorm : v.asIdeal.absNorm = w.asIdeal.absNorm)
    (T : Finset Vℚ) (hp : p ∈ T) :
    ∃ g ∈ (relativeIdeleNormRat F) ⁻¹' divisorialStratum ℚ T,
      g ∉ divisorialStratum F (T.biUnion fun q ↦ above(F, q)) := by
  obtain ⟨πv, hπv⟩ := uniformizerExists v
  obtain ⟨πw, hπw⟩ := uniformizerExists w
  let g := IdeleGroup.ofAdicCompletion (𝓞 F) F v πv *
    IdeleGroup.ofAdicCompletion (𝓞 F) F w πw⁻¹
  have hcoord (z : V(F)) :
      g.val.2 z =
        Pi.mulSingle (M := fun u : V(F) ↦ u.adicCompletion F) v πv.val z *
        Pi.mulSingle (M := fun u : V(F) ↦ u.adicCompletion F) w (πw⁻¹).val z := rfl
  have hgv : g.val.2 v = πv.val := by
    rw [hcoord, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hvw, mul_one]
  have hgw : g.val.2 w = (πw⁻¹).val := by
    rw [hcoord, Pi.mulSingle_eq_of_ne hvw.symm, Pi.mulSingle_eq_same, one_mul]
  have hgo (z : V(F)) (hzv : z ≠ v) (hzw : z ≠ w) : g.val.2 z = 1 := by
    rw [hcoord, Pi.mulSingle_eq_of_ne hzv, Pi.mulSingle_eq_of_ne hzw, mul_one]
  have hlt : (1 : ℝ) < w.asIdeal.absNorm := by
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm_nnreal w
  refine ⟨g, ?_, ?_⟩
  · intro q _
    apply (finitePlaceNorm_eq_one q _).mp
    refine (rationalAdeleNorm_finitePlace F q g.val).trans ?_
    by_cases hqp : q = p
    · subst q
      simp only [finprod_eq_if]
      rw [finprod_eq_finsetProd_of_mulSupport_subset _ (s := {v, w})]
      · rw [Finset.prod_pair hvw, ite_eq_left hv, ite_eq_left hw, hgv, hgw,
          Units.val_inv_eq_inv_val, norm_inv, norm_uniformizer_adicCompletion v _ hπv,
          norm_uniformizer_adicCompletion w _ hπw, hNorm]
        exact mul_inv_cancel₀ (inv_ne_zero (ne_of_gt (lt_trans zero_lt_one hlt)))
      · intro z hz
        by_contra h
        have hzv : z ≠ v := fun h' ↦ h (by simp [h'])
        have hzw : z ≠ w := fun h' ↦ h (by simp [h'])
        have he : (if z.under (𝓞 ℚ) = p then ‖g.val.2 z‖ else 1) = 1 := by
          rw [hgo z hzv hzw, norm_one]
          split_ifs <;> rfl
        exact hz he
    · apply finprod_eq_one_of_forall_eq_one
      intro z
      rw [finprod_eq_if]
      split_ifs with hz
      · rw [hgo z (by rintro rfl; exact hqp (hz.symm.trans hv))
          (by rintro rfl; exact hqp (hz.symm.trans hw)), norm_one]
      · rfl
  · intro hg
    have hmem : v ∈ T.biUnion (fun q ↦ above(F, q)) := Finset.mem_biUnion.mpr
      ⟨p, hp, (finite_nuclearityPlacesAbove p).mem_toFinset.mpr hv⟩
    have hvval := hg v hmem
    change Valued.v (g.val.2 v) = 1 at hvval
    rw [hgv] at hvval
    have he : ‖πv.val‖ = 1 := (finitePlaceNorm_eq_one v _).mpr hvval
    rw [norm_uniformizer_adicCompletion v _ hπv, hNorm] at he
    exact (ne_of_lt (inv_lt_one_of_one_lt₀ hlt)) he

private theorem trivialNormTwist (F : Type) [Field F] [NumberField F] :
    ideleClassNormTwist (1 : PontryaginDual C(F)) 0 = 1 := by
  ext g
  change (1 : ℂ) * _ ^ (0 : ℂ) = 1
  simp

private theorem trivialUnramified {F : Type} [Field F] [NumberField F] (v : V(F)) :
    (ideleClassNormTwist (1 : PontryaginDual C(F)) 0).IsUnramifiedAt v := by
  rw [trivialNormTwist, HeckeCharacter.isUnramifiedAt_iff]
  intro x
  simp

section CyclotomicWitness

local notation "K₃" => CyclotomicField 3 ℚ
local instance instCyclotomicThreeDivisorialStratum : IsCyclotomicExtension ({3} : Set ℕ) ℚ K₃ :=
  CyclotomicField.isCyclotomicExtension 3 ℚ

private theorem rationalPrimeBelow (v : HeightOneSpectrum (𝓞 K₃)) :
    ∃ p : ℕ, p.Prime ∧ v.asIdeal.under ℤ = Ideal.span {(p : ℤ)} := by
  let P := v.asIdeal.under ℤ
  have hP : P.IsPrime := Ideal.IsPrime.under ℤ v.asIdeal
  have hP0 : P ≠ ⊥ := mt Ideal.eq_bot_of_under_eq_bot v.ne_bot
  obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal P).principal
  have hg' : P = Ideal.span {g} := hg
  have hg0 : g ≠ 0 := by rintro rfl; exact hP0 (by rw [hg']; simp)
  have hgp : Prime g := (Ideal.span_singleton_prime hg0).mp (hg' ▸ hP)
  exact ⟨g.natAbs, Int.prime_iff_natAbs_prime.mp hgp, by change P = _; rw [hg', Int.span_natAbs]⟩

private theorem ramificationOutsideThree (v : HeightOneSpectrum (𝓞 K₃))
    (hv : (3 : 𝓞 K₃) ∉ v.asIdeal) : v.asIdeal.ramificationIdx (𝓞 ℚ) = 1 := by
  obtain ⟨p, hp, hP⟩ := rationalPrimeBelow v
  have : Fact p.Prime := ⟨hp⟩
  have : v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := ⟨hP.symm⟩
  have hnd : ¬ p ∣ 3 := by
    intro hd
    have he := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hd
    subst p
    apply hv
    change algebraMap ℤ (𝓞 K₃) 3 ∈ v.asIdeal
    change (3 : ℤ) ∈ v.asIdeal.under ℤ
    rw [hP]
    exact Ideal.subset_span rfl
  have he := IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd p K₃ v.asIdeal hnd
  have : v.asIdeal.LiesOver (v.under (𝓞 ℚ)).asIdeal := ⟨rfl⟩
  rw [Ideal.ramificationIdx_tower (R := ℤ) (v.under (𝓞 ℚ)).asIdeal v.asIdeal] at he
  exact Nat.dvd_one.mp ⟨_, he.symm.trans (Nat.mul_comm _ _)⟩

private theorem twoPlacesAboveSeven :
    ∃ v w : HeightOneSpectrum (𝓞 K₃),
      v ≠ w ∧ v.under (𝓞 ℚ) = w.under (𝓞 ℚ) ∧ v.asIdeal.absNorm = w.asIdeal.absNorm := by
  let P : Ideal ℤ := Ideal.span {(7 : ℤ)}
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hP0 : P ≠ ⊥ := by simp [P]
  have : P.IsPrime := (Ideal.span_singleton_prime (by decide : (7 : ℤ) ≠ 0)).2 (by decide)
  have : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP0
  let : Fintype (P.primesOver (𝓞 K₃)) := (IsDedekindDomain.primesOver_finite P (𝓞 K₃)).fintype
  have hinertia (Q : P.primesOver (𝓞 K₃)) : Q.val.inertiaDeg ℤ = 1 := by
    have := Q.property.1
    have := Q.property.2
    rw [IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd 7 K₃ Q.val (show ¬ 7 ∣ 3 by decide)]
    change orderOf ((7 : ℕ) : ZMod 3) = 1
    rw [show ((7 : ℕ) : ZMod 3) = 1 by decide, orderOf_one]
  have hram (Q : P.primesOver (𝓞 K₃)) : Q.val.ramificationIdx ℤ = 1 := by
    have := Q.property.1
    have := Q.property.2
    exact IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd 7 K₃ Q.val (show ¬ 7 ∣ 3 by decide)
  have hs := Ideal.sum_ramification_inertia_eq_finrank P (𝓞 K₃)
  simp only [hinertia, hram, mul_one, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    RingOfIntegers.rank] at hs
  have hrank : Module.finrank ℚ K₃ = 2 := by
    rw [IsCyclotomicExtension.Rat.finrank 3 K₃]
    decide
  rw [hrank] at hs
  have hnon : 1 < (P.primesOver (𝓞 K₃)).ncard := by
    rw [← Set.fintypeCard_eq_ncard, hs]
    decide
  obtain ⟨V, W, hV, hW, hVW⟩ :=
    (Set.one_lt_ncard_iff (IsDedekindDomain.primesOver_finite P (𝓞 K₃))).mp hnon
  let v : HeightOneSpectrum (𝓞 K₃) := ⟨V, hV.1, Ideal.ne_bot_of_mem_primesOver hP0 hV⟩
  let w : HeightOneSpectrum (𝓞 K₃) := ⟨W, hW.1, Ideal.ne_bot_of_mem_primesOver hP0 hW⟩
  have : V.IsPrime := hV.1
  have : W.IsPrime := hW.1
  have : V.LiesOver P := hV.2
  have : W.LiesOver P := hW.2
  have hVunder : V.under ℤ = P := (Ideal.over_def V P).symm
  have hWunder : W.under ℤ = P := (Ideal.over_def W P).symm
  refine ⟨v, w, fun h ↦ hVW (congrArg HeightOneSpectrum.asIdeal h), ?_, ?_⟩
  · apply HeightOneSpectrum.ext
    apply Ideal.comap_injective_of_surjective (algebraMap ℤ (𝓞 ℚ))
    · intro x
      obtain ⟨n, rfl⟩ := Rat.ringOfIntegersEquiv.symm.surjective x
      exact ⟨n, by simp⟩
    · change (V.under (𝓞 ℚ)).under ℤ = (W.under (𝓞 ℚ)).under ℤ
      rw [Ideal.under_under, Ideal.under_under, hVunder, hWunder]
  · change V.absNorm = W.absNorm
    rw [← Ideal.absNorm_pow_inertiaDeg P V, ← Ideal.absNorm_pow_inertiaDeg P W,
      hinertia ⟨V, hV⟩, hinertia ⟨W, hW⟩]

private theorem counterexampleBase :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K₃)),
      (∀ v ∈ S, ∀ w : HeightOneSpectrum (𝓞 K₃), w.under (𝓞 ℚ) = v.under (𝓞 ℚ) → w ∈ S) ∧
      (∀ v ∉ S, v.asIdeal.ramificationIdx (𝓞 ℚ) = 1) ∧
      Subsingleton (CommRing.Pic ((S : Set (HeightOneSpectrum (𝓞 K₃))).integer K₃)) := by
  obtain ⟨U, hU⟩ := eventually_trivial_sIdealClassGroup K₃
  let p : HeightOneSpectrum (𝓞 ℚ) :=
    Rat.HeightOneSpectrum.primesEquiv.symm ⟨3, Nat.prime_three⟩
  let T := insert p (U.image (HeightOneSpectrum.under (𝓞 ℚ)))
  let S := T.biUnion fun q ↦ (finite_nuclearityPlacesAbove (F := K₃) q).toFinset
  have hmem (v : HeightOneSpectrum (𝓞 K₃)) : v ∈ S ↔ v.under (𝓞 ℚ) ∈ T := by
    change v ∈ T.biUnion _ ↔ _
    simp only [Finset.mem_biUnion, Set.Finite.mem_toFinset,
      Set.mem_ofPred_eq]
    exact ⟨fun ⟨q, hq, hv⟩ ↦ hv.symm ▸ hq, fun hv ↦ ⟨_, hv, rfl⟩⟩
  refine ⟨S, fun v hv w hw ↦ (hmem w).2 (hw.symm ▸ (hmem v).1 hv), ?_, hU S ?_⟩
  · intro v hv
    apply ramificationOutsideThree v
    intro h3
    have hg : Rat.HeightOneSpectrum.natGenerator p = 3 := congrArg Subtype.val
      (Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply ⟨3, Nat.prime_three⟩)
    let e := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)
    have hi : p.asIdeal = Ideal.span {(3 : 𝓞 ℚ)} := by
      apply (Ideal.relIsoOfBijective (f := e.toRingHom) e.bijective).symm.injective
      change Ideal.map e _ = Ideal.map e _
      rw [Ideal.map_span, Set.image_singleton, map_ofNat]
      simpa [hg] using (Rat.HeightOneSpectrum.span_natGenerator p).symm
    have hle : p.asIdeal ≤ (v.under (𝓞 ℚ)).asIdeal := by
      rw [hi, Ideal.span_singleton_le_iff_mem]
      simpa only [HeightOneSpectrum.under, Ideal.mem_comap, map_ofNat] using h3
    have he := HeightOneSpectrum.ext
      (p.isMaximal.eq_of_le (v.under (𝓞 ℚ)).isPrime.ne_top hle).symm
    exact hv ((hmem v).2 (he ▸ Finset.mem_insert_self p _))
  · intro v hv
    exact (hmem v).2 (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hv))

/-- Paper: §11.3.1.1, p. 493. In the third cyclotomic field, choose two places over
7 with equal residue-field cardinalities. Insert a uniformizer at one and an inverse
uniformizer at the other. The relative norm has unit components at every finite
place of ℚ, while the two selected components upstairs are nonunits. -/
theorem Printed.primaryDivisorialStratum_eq_norm_preimage_false :
    ¬ Printed.primaryDivisorialStratum_eq_norm_preimage := by
  intro printed
  obtain ⟨S, hSat, hRam, hPic⟩ := counterexampleBase
  obtain ⟨v, w, hvw, huv, hNorm⟩ := twoPlacesAboveSeven
  let p := w.under (𝓞 ℚ)
  let e : Vℚ ≃ Nat.Primes := Rat.HeightOneSpectrum.primesEquiv
  let n := e p
  obtain ⟨j, hj⟩ := Nat.subset_range_nth
    (show n.val ∈ {a : ℕ | Nat.Prime a} from n.property)
  let T : Finset Vℚ := (Finset.range (j + 1)).image fun i ↦
    Rat.HeightOneSpectrum.primesEquiv.symm ⟨Nat.nth Nat.Prime i, Nat.prime_nth_prime i⟩
  have hp : p ∈ T := by
    refine Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (Nat.lt_succ_self j), ?_⟩
    change e.symm ⟨Nat.nth Nat.Prime j, Nat.prime_nth_prime j⟩ = p
    exact (congrArg e.symm (Subtype.ext hj)).trans (e.symm_apply_apply p)
  obtain ⟨g, hNormG, hg⟩ := splitPrime_norm_cancellation hvw huv rfl hNorm T hp
  have he := printed K₃ 1 S hSat hRam (fun z _ ↦ trivialUnramified z) hPic (j + 1)
  exact hg (he.symm ▸ hNormG)

end CyclotomicWitness

/-- Paper: §11.3.1.1(2), p. 494. As printed, the Poisson evaluation of
the half-shifted Euler-zero sum uses unweighted point evaluations at powers
of the uniformizers. The prime lies outside the base of p. 491, so it is
unramified in the field and the character is unramified above it. -/
def Printed.orbitalEulerSum_eq_poisson : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C(F))
    (φ : BruhatCompactSupport C(F)) (p : Vℚ),
    (∀ v ∈ above(F, p), ramificationIndex(v) = 1) →
    (∀ v ∈ above(F, p), (ideleClassNormTwist χ 0).IsUnramifiedAt v) →
    ∀ π : ∀ v : V(F), (v.adicCompletion F)ˣ,
      (∀ v ∈ above(F, p), Valued.v.IsUniformizer (π v : v.adicCompletion F)) →
      let zeros := {z : ℂ // reciprocalPartialHeckeEulerProduct χ above(F, p) z = 0}
      HasSum (fun z : zeros ↦ (orbitalEulerMultiplicity χ above(F, p) z.val : ℂ) *
        nuclearityTestMellin χ φ (z.val - 1 / 2))
        (∑ v ∈ above(F, p), (Real.log (v.asIdeal.absNorm : ℝ) / unitMass(F, v) : ℂ) *
          ∑' n : ℤ, φ.val (πclass(F, v, π v) ^ n))

open scoped ContDiff Topology

local notation "ratNorm(" x ")" => (((ideleClassNorm ℚ x).val : ℝ≥0) : ℝ)

private def twoPlace : Vℚ := Rat.HeightOneSpectrum.primesEquiv.symm ⟨2, Nat.prime_two⟩

private theorem placeNorm : twoPlace.asIdeal.absNorm = 2 := by
  let e := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)
  have hg : Rat.HeightOneSpectrum.natGenerator twoPlace = 2 := congrArg Subtype.val
    (Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply ⟨2, Nat.prime_two⟩)
  have he := Rat.HeightOneSpectrum.span_natGenerator twoPlace
  rw [hg] at he
  have hi : twoPlace.asIdeal = Ideal.span {(2 : 𝓞 ℚ)} := by
    apply (Ideal.relIsoOfBijective (f := e.toRingHom) e.bijective).symm.injective
    change Ideal.map e _ = Ideal.map e _
    rw [Ideal.map_span, Set.image_singleton, map_ofNat]
    exact he.symm
  rw [hi, show (2 : 𝓞 ℚ) = (2 : ℕ) by norm_num, Ideal.absNorm_span_natCast,
    RingOfIntegers.rank]
  simp

private theorem smooth_comp_bruhat {G : Type*} [CommGroup G] [TopologicalSpace G]
    {v : G → ℂ} (hv : IsBruhatSmooth v) {f : ℂ → ℂ} (hf : ContDiff ℝ (∞) f) :
    IsBruhatSmooth (fun x ↦ f (v x)) := by
  intro p
  obtain ⟨k, hk, hi, hdesc⟩ := hv p
  refine ⟨k, hk, fun h x ↦ congrArg f (hi h x), ?_⟩
  intro a ha
  obtain ⟨q, hq, hdiff⟩ := hdesc a ha
  exact ⟨fun y ↦ f (q y), fun x ↦ congrArg f (hq x),
    fun e z b ↦ (hf.of_le (by simp)).comp (hdiff e z b)⟩

private theorem radialTest :
    ∃ φ ψ : BruhatCompactSupport C(ℚ),
      tsupport φ.val ⊆ {x | ratNorm(x) ∈ Icc (7 / 4 : ℝ) (9 / 4)} ∧
      (∀ x, ratNorm(x) = 2 → φ.val x = 1) ∧
      (∀ x y, ratNorm(x) = ratNorm(y) → φ.val x = φ.val y) ∧
      (∀ x y, ratNorm(y) = ratNorm(x) / 2 → ψ.val x = φ.val y) := by
  let B : ContDiffBump (2 : ℝ) := ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩
  have mkTest (d : ℝ) (hd : 0 < d) :
      ∃ φ : BruhatCompactSupport C(ℚ), ∀ x, φ.val x = (B (ratNorm(x) / d) : ℂ) := by
    let χ : QuasiCharacter C(ℚ) :=
      { toFun := fun x ↦ (ratNorm(x) : ℂ)
        map_one' := by simp
        map_mul' := fun x y ↦ by simp
        continuous_toFun := Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp
          (Units.continuous_val.comp (isProperMap_ideleClassNorm ℚ).continuous)) }
    let f (z : ℂ) : ℂ := B (z.re / d)
    have hs : IsBruhatSmooth (fun x ↦ (B (ratNorm(x) / d) : ℂ)) := by
      apply smooth_comp_bruhat (v := fun x ↦ χ x) (f := f)
        ((mem_bruhatSmoothSubmodule_iff _).1 (quasiCharacter_mem_bruhatSmooth χ))
      exact Complex.ofRealCLM.contDiff.comp (B.contDiff.comp (Complex.reCLM.contDiff.div_const d))
    let unit (t : ℝ) : ℝ≥0ˣ := Units.mk0 (Real.exp t).toNNReal
      (Real.toNNReal_pos.mpr (Real.exp_pos t)).ne'
    have hu : Continuous unit := Units.continuous_iff.mpr
      ⟨continuous_real_toNNReal.comp Real.continuous_exp,
        (continuous_real_toNNReal.comp Real.continuous_exp).inv₀ fun t ↦
          (Real.toNNReal_pos.mpr (Real.exp_pos t)).ne'⟩
    have hc : HasCompactSupport (fun x ↦ (B (ratNorm(x) / d) : ℂ)) := by
      apply HasCompactSupport.intro ((isProperMap_ideleClassNorm ℚ).isCompact_preimage
        ((isCompact_Icc (a := Real.log (7 / 4 * d)) (b := Real.log (9 / 4 * d))).image hu))
      intro x hx
      by_contra hn
      have hB : B (ratNorm(x) / d) ≠ 0 := fun h ↦ hn (by simp [h])
      have hm := subset_tsupport _ hB
      rw [B.tsupport_eq, Metric.mem_closedBall, Real.dist_eq, abs_le] at hm
      change -(1 / 4 : ℝ) ≤ _ ∧ _ ≤ 1 / 4 at hm
      have hl : 7 / 4 ≤ ratNorm(x) / d := by linarith [hm.1]
      have hr : ratNorm(x) / d ≤ 9 / 4 := by linarith [hm.2]
      have hp : 0 < ratNorm(x) := NNReal.coe_pos.mpr (Units.zero_lt _)
      apply hx
      refine ⟨Real.log ratNorm(x), ⟨Real.log_le_log (by positivity) ((le_div_iff₀ hd).1 hl),
        Real.log_le_log hp ((div_le_iff₀ hd).1 hr)⟩, ?_⟩
      apply Units.ext
      change (Real.exp (Real.log _)).toNNReal = _
      rw [Real.exp_log hp, Real.toNNReal_coe]
    exact ⟨⟨_, (mem_bruhatSmoothSubmodule_iff _).2 hs, hc⟩, fun _ ↦ rfl⟩
  obtain ⟨φ, hφ⟩ := mkTest 1 one_pos
  have hv (x : C(ℚ)) : φ.val x = (B ratNorm(x) : ℂ) := by simpa using hφ x
  obtain ⟨ψ, hw⟩ := mkTest 2 two_pos
  refine ⟨φ, ψ, ?_, fun x hx ↦ ?_, fun x y h ↦ by rw [hv, hv, h], fun x y h ↦ by rw [hw, hv, h]⟩
  · apply closure_minimal _ (isClosed_Icc.preimage
      (NNReal.continuous_coe.comp (Units.continuous_val.comp (isProperMap_ideleClassNorm ℚ).continuous)))
    intro x hx
    have hh : B ratNorm(x) ≠ 0 := fun h ↦ hx (by simp [hv, h])
    have hm := subset_tsupport _ hh
    rw [B.tsupport_eq, Metric.mem_closedBall, Real.dist_eq, abs_le] at hm
    change -(1 / 4 : ℝ) ≤ _ ∧ _ ≤ 1 / 4 at hm
    change 7 / 4 ≤ ratNorm(x) ∧ ratNorm(x) ≤ 9 / 4
    exact ⟨by linarith [hm.1], by linarith [hm.2]⟩
  · simp [hv, hx, B.one_of_mem_closedBall (Metric.mem_closedBall_self B.rIn_pos.le)]

private theorem orbitNorm (v : Vℚ) (π : (v.adicCompletion ℚ)ˣ)
    (hπ : Valued.v.IsUniformizer (π : v.adicCompletion ℚ)) (n : ℤ) :
    ratNorm(πclass(ℚ, v, π) ^ n) = (v.asIdeal.absNorm : ℝ) ^ (-n) := by
  rw [map_zpow, ideleClassNorm_ofAdicCompletion, Units.val_zpow_eq_zpow_val, NNReal.coe_zpow, Units.coe_map]
  change ‖π.val‖ ^ n = _
  rw [norm_uniformizer_adicCompletion v _ hπ, inv_zpow', zpow_neg]

private theorem orbitOff (φ : BruhatCompactSupport C(ℚ))
    (hs : tsupport φ.val ⊆ {x | ratNorm(x) ∈ Icc (7 / 4 : ℝ) (9 / 4)})
    (π : (twoPlace.adicCompletion ℚ)ˣ)
    (hπ : Valued.v.IsUniformizer (π : twoPlace.adicCompletion ℚ))
    (n : ℤ) (hn : n ≠ -1) :
    φ.val (πclass(ℚ, twoPlace, π) ^ n) = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro h
  have hh := hs h
  change _ ≤ ratNorm(_) ∧ ratNorm(_) ≤ _ at hh
  rw [orbitNorm _ _ hπ, placeNorm] at hh
  norm_num only [Nat.cast_ofNat] at hh
  rcases le_or_gt 0 n with hpos | hneg
  · have hb : (2 : ℝ) ^ (-n) ≤ 2 ^ (0 : ℤ) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    rw [zpow_zero] at hb
    linarith [hh.1]
  · have hb : (2 : ℝ) ^ (2 : ℤ) ≤ 2 ^ (-n) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    norm_num only [zpow_ofNat, Nat.reducePow, Nat.cast_ofNat] at hb
    linarith [hh.2]

private theorem localMass (v : Vℚ) :
    (finiteLocalMultiplicativeTamagawaMeasure ℚ v).real (v.adicCompletionIntegers ℚ).units = 1 := by
  have hd : differentIdeal ℤ (𝓞 ℚ) = 1 := by
    rw [Ideal.one_eq_top, ← Ideal.absNorm_eq_one_iff, NumberField.absNorm_differentIdeal ℚ (𝓞 ℚ), NumberField.discr_rat]
    rfl
  rw [Measure.real, finiteLocalMultiplicativeTamagawaMeasure_integerUnits, hd, multiplicity_one_right]
  simp

private theorem twoPlaceOrbitSum (φ : BruhatCompactSupport C(ℚ))
    (hs : tsupport φ.val ⊆ {x | ratNorm(x) ∈ Icc (7 / 4 : ℝ) (9 / 4)})
    (hc : ∀ x, ratNorm(x) = 2 → φ.val x = 1)
    (π : (twoPlace.adicCompletion ℚ)ˣ) (hπ : Valued.v.IsUniformizer (π : twoPlace.adicCompletion ℚ)) :
    (∑' n : ℤ, φ.val (πclass(ℚ, twoPlace, π) ^ n)) = 1 := by
  rw [tsum_eq_single (-1 : ℤ)]
  · apply hc
    rw [orbitNorm _ _ hπ, placeNorm]
    norm_num
  · exact orbitOff φ hs π hπ

/-- Paper: §11.3.1.1(2), p. 494. Over ℚ take the trivial character, the
prime 2 and a radial bump supported at norms in (3/2, 5/2) with value one
at 2. There is just one point evaluation, at the inverse uniformizer.
Translation by the inverse uniformizer preserves the orbit sum and scales
the half-shifted spectral sum by 2⁻¹ᐟ². The claimed common value is nonzero. -/
theorem Printed.orbitalEulerSum_eq_poisson_false :
    ¬ Printed.orbitalEulerSum_eq_poisson := by
  intro printed
  obtain ⟨φ, ψ, hs, hc, _, hψN⟩ := radialTest
  let v := twoPlace
  let π := fun w : Vℚ ↦ (uniformizerExists w).choose
  have hπ (w : Vℚ) : Valued.v.IsUniformizer (π w : w.adicCompletion ℚ) :=
    (uniformizerExists w).choose_spec
  let a := πclass(ℚ, v, π v)
  have hsum := twoPlaceOrbitSum φ hs hc (π v) (hπ v)
  change (∑' n : ℤ, φ.val (a ^ n)) = 1 at hsum
  let fibre := (finite_nuclearityPlacesAbove (F := ℚ) v).toFinset
  have hf : fibre = {v} := by
    ext w
    change w ∈ (finite_nuclearityPlacesAbove (F := ℚ) v).toFinset ↔ _
    simp only [Set.Finite.mem_toFinset, mem_ofPred_eq, Finset.mem_singleton]
    rfl
  let b := a ^ (-1 : ℤ)
  have hb : ratNorm(b) = 2 := by
    rw [show ratNorm(b) = _ from orbitNorm v (π v) (hπ v) (-1), placeNorm]
    norm_num
  have hψ (x : C(ℚ)) : ψ.val x = φ.val (b⁻¹ * x) := by
    apply hψN
    rw [map_mul, map_inv, Units.val_mul, NNReal.coe_mul, Units.val_inv_eq_inv_val,
      NNReal.coe_inv, show ((ideleClassNorm ℚ b).val : ℝ) = ratNorm(b) from rfl, hb]
    ring
  have hshift (n : ℤ) : ψ.val (a ^ n) = φ.val (a ^ (n + 1)) := by
    rw [hψ]; simp [b, zpow_add_one, mul_comm]
  have hsum' : (∑' n : ℤ, ψ.val (a ^ n)) = 1 := by
    simp_rw [hshift]
    exact ((Equiv.addRight (1 : ℤ)).tsum_eq (fun n ↦ φ.val (a ^ n))).trans hsum
  let Z := {z : ℂ // reciprocalPartialHeckeEulerProduct (1 : PontryaginDual C(ℚ)) fibre z = 0}
  have hm (z : Z) : (2 : ℂ) ^ z.val = 1 := by
    let s : ℂ := z.val
    have h : reciprocalPartialHeckeEulerProduct (1 : PontryaginDual C(ℚ)) fibre s = 0 := z.2
    have hu := trivialUnramified v
    rw [hf, reciprocalPartialHeckeEulerProduct_singleton _ v hu, placeNorm,
      hu.localValue_eq (π v) (hπ v)] at h
    rw [trivialNormTwist ℚ, HeckeCharacter.restrict, MulChar.ofUnitHom_coe] at h
    change 1 - 1 * (↑(2 : ℕ) : ℂ) ^ (-s) = 0 at h
    simpa [Complex.cpow_neg] using (sub_eq_zero.mp h).symm
  let c := (2 : ℂ) ^ (-(1 / 2 : ℂ))
  have hmel (z : Z) : nuclearityTestMellin 1 ψ (z.val - 1 / 2) =
      c * nuclearityTestMellin 1 φ (z.val - 1 / 2) := by
    unfold nuclearityTestMellin
    simp_rw [hψ]
    let χ := (ideleClassNormTwist (1 : PontryaginDual C(ℚ)) (z.val - 1 / 2)).toMonoidHom
    let μ := ideleClassTamagawaMeasure ℚ
    have ht : (∫ x, φ.val (b⁻¹ * x) * χ x ∂μ) = χ b * ∫ x, φ.val x * χ x ∂μ := by
      rw [← integral_mul_left_eq_self (μ := μ) (fun x ↦ φ.val (b⁻¹ * x) * χ x) b,
        ← integral_const_mul]
      exact integral_congr_ae (.of_forall fun x ↦ by
        simp only [mul_inv_cancel_left, map_mul, mul_left_comm])
    refine ht.trans ?_
    congr 1
    change (1 : ℂ) * (ratNorm(b) : ℂ) ^ (z.val - 1 / 2) = _
    rw [hb, Complex.ofReal_ofNat, one_mul, sub_eq_add_neg, Complex.cpow_add _ _ (by norm_num), hm, one_mul]
  let term (g : BruhatCompactSupport C(ℚ)) (z : Z) :=
    (orbitalEulerMultiplicity (1 : PontryaginDual C(ℚ)) fibre z.val : ℂ) *
      nuclearityTestMellin 1 g (z.val - 1 / 2)
  have H (g : BruhatCompactSupport C(ℚ)) (h : (∑' n : ℤ, g.val (a ^ n)) = 1) :
      HasSum (term g) (Real.log 2 : ℂ) := by
    have hp := printed ℚ 1 g v (fun w _ ↦ Ideal.ramificationIdx_eq_one w.asIdeal (𝓞 ℚ))
      (fun w _ ↦ trivialUnramified w) π (fun w _ ↦ hπ w)
    change HasSum (term g) (∑ w ∈ fibre, (Real.log (w.asIdeal.absNorm : ℝ) /
      (finiteLocalMultiplicativeTamagawaMeasure ℚ w).real (w.adicCompletionIntegers ℚ).units : ℂ) *
      ∑' n : ℤ, g.val (πclass(ℚ, w, π w) ^ n)) at hp
    rw [hf, Finset.sum_singleton, h, localMass, placeNorm] at hp
    simpa using hp
  have hscaled := ((H φ hsum).mul_left c).congr_fun (g := term ψ) (fun z ↦ by
    simp only [term, hmel]; ring)
  have e := hscaled.unique (H ψ hsum')
  have hn : (Real.log 2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.log_pos (by norm_num)).ne'
  have hw : c = 1 := mul_right_cancel₀ hn (e.trans (one_mul _).symm)
  have hsq := congrArg (fun z : ℂ ↦ z * z) hw
  simp only [c, ← Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0), one_mul] at hsq
  norm_num at hsq
  rw [Complex.cpow_neg_one] at hsq
  norm_num at hsq

set_option maxSynthPendingDepth 3 in
/-- Paper: Theorem 11.3.2.1, (11.3.2.1)–(11.3.2.2), p. 495.
The printed orbital integral uses the section weight and equates a layer
to the term for its displayed place.
Deviation: Bind the displayed place in the indicated layer. Make existence
of the spectral tensor used to specify the §10.4 strip kernel explicit.
The counterexample uses a layer consisting of a single place. -/
def Printed.orbitalTracesOnPaleyWienerLevels : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C(F))
    (φ : BruhatCompactSupport C(F)) (S : Finset V(F)),
    (∀ v ∈ S, ∀ w : V(F), w.under (𝓞 ℚ) = v.under (𝓞 ℚ) → w ∈ S) →
    (∀ v ∉ S, ramificationIndex(v) = 1) →
    (∀ v ∉ S, (ideleClassNormTwist χ 0).IsUnramifiedAt v) →
    (∀ u : outsideIntegralIdeleUnits F S, ∀ x : C(F), φ.val (classOf(F) u.val * x) = φ.val x) →
    Subsingleton (CommRing.Pic ((S : Set V(F)).integer F)) →
    tsupport φ.val ⊆ {x : C(F) | 1 < ((ideleClassNorm F x).val : ℝ)} →
    ∀ (s α : ℝ) (hs : 1 < s) (hα : 0 ≤ α) (τ : ℝ≥0ˣ →* I(F)),
      Continuous τ → RightInverse τ (ideleNorm F) →
      ∀ (b : Module.Basis (Fin (Units.rank F)) ℤ (Additive ((𝓞 F)ˣ ⧸ Units.torsion F)))
        (w : InfinitePlace F) (σ : ℂ ≃ₐ[ℝ] ℂ) (r : CommRing.Pic (𝓞 F) → N(F)),
        r 1 = 1 → (∀ c, ideleIdealClass F (r c).val = c) →
        ∀ (k : ℕ) (v : V(F)),
          v ∈ primaryDivisorialPlaces F S (k + 1) \ primaryDivisorialPlaces F S k →
          ∀ (π : (v.adicCompletion F)ˣ), Valued.v.IsUniformizer (π : v.adicCompletion F) →
            ∃ hK,
              let K := globalStripGeometricKernel (F := F) (1 / 2) hα hs φ hK
              let E := ideleFundamentalDomain F b w σ r
              let lift := fun xy : I(F) × I(F) ↦
                (orbitalSectionWeight E τ xy : ℂ) * K (classOf(F) xy.1, classOf(F) xy.2)
              (∑' ξ : Fˣ, ∫ t, ∫ g in E,
                divisorialKernelDifference S k lift
                  (τ t, IdeleGroup.unitEmbedding (𝓞 F) F ξ * g.val * τ t)
                ∂normOneIdeleTamagawaMeasure F ∂positiveRealHaar) =
                (Real.log (v.asIdeal.absNorm : ℝ) / unitMass(F, v) : ℂ) *
                  ∑' n : ℤ, φ.val (πclass(F, v, π) ^ n)

private theorem firstLayer : twoPlace ∈ primaryDivisorialPlaces ℚ ∅ (0 + 1) \
    primaryDivisorialPlaces ℚ ∅ 0 := by
  simp only [Nat.zero_add, primaryDivisorialPlaces, Finset.range_zero, Finset.biUnion_empty,
    Finset.range_one, Finset.singleton_biUnion, Finset.mem_sdiff, Finset.notMem_empty,
    not_false_eq_true, and_true, Set.Finite.mem_toFinset, mem_ofPred_eq,
    primaryDivisorialPrime_empty_zero]
  rfl

private theorem outsideNorm (u : outsideIntegralIdeleUnits ℚ ∅) :
    ideleNorm ℚ u.val = 1 := by
  obtain ⟨ha, _, hf⟩ := (mem_outsideIntegralIdeleUnits_iff u.val).mp u.property
  have hfinite (v : Vℚ) : ‖u.val.val.2 v‖ = 1 := by
    let ev := (RestrictedProduct.evalRingHom (fun w : Vℚ ↦ w.adicCompletion ℚ) v).comp
      (RingHom.snd (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ))
    apply Valued.toNormedField.norm_eq_one_iff.mpr
    exact (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one
      (a := Units.map ev.toMonoidHom u.val)).mp (hf v (by simp))
  apply Units.ext
  apply NNReal.coe_injective
  rw [((ideleNorm_spec ℚ).1 u.val).2, ha, finprod_eq_one_of_forall_eq_one hfinite]
  simp
  change ‖(1 : (default : InfinitePlace ℚ).Completion)‖ = 1
  exact norm_one

private theorem primeTwoWitness :
    ∃ (φ : BruhatCompactSupport C(ℚ)) (v : Vℚ) (π : (v.adicCompletion ℚ)ˣ),
      v ∈ primaryDivisorialPlaces ℚ ∅ (0 + 1) \ primaryDivisorialPlaces ℚ ∅ 0 ∧
      v.asIdeal.absNorm = 2 ∧ Valued.v.IsUniformizer (π : v.adicCompletion ℚ) ∧
      tsupport φ.val ⊆ {x | 1 < ratNorm(x)} ∧
      (∀ u : outsideIntegralIdeleUnits ℚ ∅, ∀ x : C(ℚ),
        φ.val (classOf(ℚ) u.val * x) = φ.val x) ∧
      (∑' n : ℤ, φ.val (πclass(ℚ, v, π) ^ n)) = 1 := by
  obtain ⟨φ, _, hs, hc, hr, _⟩ := radialTest
  obtain ⟨π, hπ⟩ := uniformizerExists twoPlace
  refine ⟨φ, twoPlace, π, firstLayer, placeNorm, hπ, ?_, ?_, twoPlaceOrbitSum φ hs hc π hπ⟩
  · intro x hx
    exact lt_of_lt_of_le (by norm_num : (1 : ℝ) < 7 / 4) (hs hx).1
  · intro u x
    apply hr
    rw [map_mul]
    change (((ideleNorm ℚ u.val * ideleClassNorm ℚ x).val : ℝ≥0) : ℝ) = _
    rw [outsideNorm, one_mul]

local notation "τq" => canonicalIdeleNormSection ℚ

-- When x is in the section, membership of d*x and d*y in its range forces y
-- into that same subgroup. This makes the weight vanish off the section.
private theorem offSection (E : Set (ideleNorm ℚ).ker) (t : ℝ≥0ˣ)
    (y : I(ℚ)) (hy : y ∉ Set.range τq) :
    orbitalSectionWeight E τq (τq t, y) = 0 := by
  have hz (d : I(ℚ)) :
      (Set.range τq).indicator (fun _ ↦ (1 : ℝ)) (d * τq t) *
      (Set.range τq).indicator (fun _ ↦ (1 : ℝ)) (d * y) = 0 := by
    by_cases hx : d * τq t ∈ Set.range τq
    · obtain ⟨u, hu⟩ := hx
      have hdy : d * y ∉ Set.range τq := by
        rintro ⟨v, hv⟩
        apply hy
        refine ⟨t * u⁻¹ * v, ?_⟩
        rw [map_mul, map_mul, map_inv, hu, hv]
        group
      simp [Set.indicator_of_notMem hdy]
    · simp [Set.indicator_of_notMem hx]
  simp only [orbitalSectionWeight, hz, integral_zero, tsum_zero]

private theorem indicatorOnSection (T : Finset Vℚ) (t : ℝ≥0ˣ) :
    divisorialIndicator T (τq t) = 1 := by
  rw [divisorialIndicator_eq_indicator]
  apply Set.indicator_of_mem
  intro v _
  rw [canonicalIdeleNormSection_finite]
  exact map_one _

private theorem shellWeightZero (E : Set (ideleNorm ℚ).ker) (t : ℝ≥0ˣ)
    (y : I(ℚ)) (K : I(ℚ) × I(ℚ) → ℂ) :
    divisorialKernelDifference ∅ 0
      (fun xy ↦ (orbitalSectionWeight E τq xy : ℂ) * K xy) (τq t, y) = 0 := by
  by_cases hy : y ∈ Set.range τq
  · obtain ⟨u, rfl⟩ := hy
    simp only [divisorialKernelDifference, indicatorOnSection, sub_self, zero_mul]
  · simp only [divisorialKernelDifference, offSection E t y hy, Complex.ofReal_zero,
      zero_mul, mul_zero]

private theorem orbitalZero (E : Set (ideleNorm ℚ).ker) (K : C(ℚ) × C(ℚ) → ℂ) :
    (∑' ξ : ℚˣ, ∫ t, ∫ g in E, divisorialKernelDifference ∅ 0
      (fun xy ↦ (orbitalSectionWeight E τq xy : ℂ) * K (classOf(ℚ) xy.1,
        classOf(ℚ) xy.2))
      (τq t, IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ ξ * g.val * τq t)
      ∂normOneIdeleTamagawaMeasure ℚ ∂positiveRealHaar) = 0 := by
  simp only [shellWeightZero E _ _ (fun xy ↦ K (QuotientGroup.mk' _ xy.1,
    QuotientGroup.mk' _ xy.2)), integral_zero, tsum_zero]

private theorem rationalEmptyBase_picTrivial :
    Subsingleton (CommRing.Pic (((∅ : Finset Vℚ) : Set Vℚ).integer ℚ)) := by
  rw [Finset.coe_empty, integer_empty]
  let e := (Algebra.botEquivOfInjective (IsFractionRing.injective (𝓞 ℚ) ℚ)).toRingEquiv
  let i := Rat.ringOfIntegersEquiv.symm.trans e.symm
  let := IsPrincipalIdealRing.of_surjective i i.surjective
  infer_instance

/-- Paper: Theorem 11.3.2.1, p. 495. Take F = ℚ, the trivial character,
the archimedean base, the standard norm section and the first layer at 2.
Choose a nonnegative smooth log-norm bump with value one at norm 2,
supported at norms in (3/2, 5/2). The weight vanishes off the section. On the
section the two divisorial indicators agree. The right side is log 2. -/
theorem Printed.orbitalTracesOnPaleyWienerLevels_false :
    ¬ Printed.orbitalTracesOnPaleyWienerLevels := by
  intro claim
  obtain ⟨φ, v, π, hv, hq, hπ, hs, hu, hsum⟩ := primeTwoWitness
  let : IsPrincipalIdealRing (𝓞 ℚ) := IsPrincipalIdealRing.of_surjective
    Rat.ringOfIntegersEquiv.symm Rat.ringOfIntegersEquiv.symm.surjective
  have hex := claim ℚ 1 φ ∅ (by simp)
    (fun w _ ↦ Ideal.ramificationIdx_eq_one w.asIdeal (𝓞 ℚ))
    (fun w _ ↦ trivialUnramified w) hu rationalEmptyBase_picTrivial hs 2 0 (by norm_num) (by norm_num)
    (canonicalIdeleNormSection ℚ) (canonicalIdeleNormSection_continuous ℚ)
    (canonicalIdeleNormSection_rightInverse ℚ) (Units.basisModTorsion ℚ)
    Rat.infinitePlace (AlgEquiv.refl : ℂ ≃ₐ[ℝ] ℂ) (fun _ ↦ 1) rfl
    (fun _ ↦ Subsingleton.elim _ _) 0 v hv π hπ
  obtain ⟨hK, h⟩ := hex
  extract_lets K E lift at h
  -- The zero integral holds for every kernel and domain. Keeping both abstract
  -- avoids reducing the projective tensor during the equality check.
  clear_value K E
  have hz := orbitalZero E K
  have he : (0 : ℂ) = (Real.log (v.asIdeal.absNorm : ℝ) /
      (finiteLocalMultiplicativeTamagawaMeasure ℚ v).real (v.adicCompletionIntegers ℚ).units : ℂ) *
      ∑' n : ℤ, φ.val (πclass(ℚ, v, π) ^ n) := by
    exact hz.symm.trans h
  rw [hsum, mul_one, hq] at he
  have hn : Real.log (↑(2 : ℕ) : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
  rw [localMass, Complex.ofReal_one, div_one] at he
  exact Complex.ofReal_ne_zero.mpr hn he.symm

/-- Paper: Proof of Theorem 11.3.2.1, p. 496. On the kth stratum, the later
indicators are claimed to tend to the indicator of the ideles that are units
outside an enlarged set containing the current prime packet.
Deviation: State the pointwise identity of indicators on the support stratum.
Allow any such enlargement, and specialize the character to the trivial one. -/
def Printed.primaryDivisorialIndicator_localLimit : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset V(F)),
    (∀ v ∈ S, ∀ w : V(F), w.under (𝓞 ℚ) = v.under (𝓞 ℚ) → w ∈ S) →
    (∀ v ∉ S, ramificationIndex(v) = 1) →
    Subsingleton (CommRing.Pic ((S : Set V(F)).integer F)) →
    ∀ k : ℕ, ∃ T : Finset V(F), S ⊆ T ∧
      primaryDivisorialPlaces F S (k + 1) \ primaryDivisorialPlaces F S k ⊆ T ∧
      ∀ y ∈ divisorialStratum F (primaryDivisorialPlaces F S k),
        Filter.Tendsto (fun j ↦ divisorialIndicator (primaryDivisorialPlaces F S j) y)
          Filter.atTop (nhds ((sLocalDivisorialStratum F T).indicator (fun _ ↦ (1 : ℂ)) y))

/-- Paper: Proof of Theorem 11.3.2.1, p. 496. At the first rational shell take
an idele with a uniformizer at 2 and ones elsewhere. Every later mask is zero,
whereas every allowed enlarged local indicator is one. -/
theorem Printed.primaryDivisorialIndicator_localLimit_false :
    ¬ Printed.primaryDivisorialIndicator_localLimit := by
  intro claim
  let : IsPrincipalIdealRing (𝓞 ℚ) := IsPrincipalIdealRing.of_surjective
    Rat.ringOfIntegersEquiv.symm Rat.ringOfIntegersEquiv.symm.surjective
  obtain ⟨T, _, hnew, hlim⟩ := claim ℚ ∅ (by simp)
    (fun w _ ↦ Ideal.ramificationIdx_eq_one w.asIdeal (𝓞 ℚ)) rationalEmptyBase_picTrivial 0
  obtain ⟨π, hπ⟩ := uniformizerExists twoPlace
  let y := IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ twoPlace π
  have hy : y ∈ sLocalDivisorialStratum ℚ T := by
    intro w hw
    have hne : w ≠ twoPlace := by
      rintro rfl
      exact hw (hnew firstLayer)
    change Valued.v (Pi.mulSingle (M := fun v : Vℚ ↦ v.adicCompletion ℚ) twoPlace π.val w) = 1
    rw [Pi.mulSingle_eq_of_ne hne, map_one]
  have hfirst : y ∈ divisorialStratum ℚ (primaryDivisorialPlaces ℚ ∅ 0) := by
    intro w hw
    simp [primaryDivisorialPlaces] at hw
  have hone := hlim y hfirst
  rw [Set.indicator_of_mem hy] at hone
  have hzero : ∀ᶠ j : ℕ in Filter.atTop,
      divisorialIndicator (primaryDivisorialPlaces ℚ ∅ j) y = 0 := by
    filter_upwards [Filter.eventually_ge_atTop 1] with j hj
    rw [divisorialIndicator_eq_indicator]
    apply Set.indicator_of_notMem
    intro h
    have hv := h twoPlace
      (primaryDivisorialPlaces_mono (F := ℚ) ∅ hj (Finset.mem_sdiff.mp firstLayer).1)
    change Valued.v
      (Pi.mulSingle (M := fun v : Vℚ ↦ v.adicCompletion ℚ) twoPlace π.val twoPlace) = 1 at hv
    rw [Pi.mulSingle_eq_same] at hv
    exact hπ.val_lt_one.ne hv
  have hz : Filter.Tendsto (fun j ↦ divisorialIndicator (primaryDivisorialPlaces ℚ ∅ j) y)
      Filter.atTop (nhds 0) := tendsto_const_nhds.congr' (Filter.EventuallyEq.symm hzero)
  exact zero_ne_one (tendsto_nhds_unique hz hone)

/-- Paper: (11.3.2.3)–(11.3.2.5), p. 496. The traces of the cut shell kernels
are claimed to recover the orbital trace of (11.3.2.1) by taking the input
limit and then removing the output cutoff.
Deviation: Specialize to the first rational packet and the trivial character.
Allow arbitrary kernels depending on both cutoffs, absorbing the smooth
output cutoff and indentation. This gives a necessary scalar consequence of
the proposed trace-norm approximation. -/
def Printed.primaryDivisorialCutTrace : Prop :=
  ∀ (φ : BruhatCompactSupport C(ℚ)), tsupport φ.val ⊆ {x | 1 < ratNorm(x)} →
    (∀ u : outsideIntegralIdeleUnits ℚ ∅, ∀ x : C(ℚ),
      φ.val (classOf(ℚ) u.val * x) = φ.val x) →
    ∀ v ∈ primaryDivisorialPlaces ℚ ∅ (0 + 1) \ primaryDivisorialPlaces ℚ ∅ 0,
      ∀ π : (v.adicCompletion ℚ)ˣ, Valued.v.IsUniformizer (π : v.adicCompletion ℚ) →
      ∃ (K : ℕ → ℕ → I(ℚ) × I(ℚ) → ℂ) (E : Set (ideleNorm ℚ).ker) (c : ℕ → ℂ),
        (∀ m, Filter.Tendsto (fun j ↦ ∑' ξ : ℚˣ, ∫ t, ∫ g in E,
          let y := IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ ξ * g.val * τq t
          divisorialKernelDifference ∅ 0 (K m j) (τq t, y) *
            divisorialIndicator (primaryDivisorialPlaces ℚ ∅ j) y
          ∂normOneIdeleTamagawaMeasure ℚ ∂positiveRealHaar) Filter.atTop (nhds (c m))) ∧
        Filter.Tendsto c Filter.atTop (nhds ((Real.log (v.asIdeal.absNorm : ℝ) /
          unitMass(ℚ, v) : ℂ) * ∑' n : ℤ, φ.val (πclass(ℚ, v, π) ^ n)))

/-- Paper: (11.3.2.3)–(11.3.2.5), p. 496. The input limit is zero for every
kernel and output cutoff. A radial test supported above norm one with value
one at norm two gives orbital mass log 2. -/
theorem Printed.primaryDivisorialCutTrace_false : ¬ Printed.primaryDivisorialCutTrace := by
  intro claim
  obtain ⟨φ, v, π, hv, hq, hπ, hs, hu, hsum⟩ := primeTwoWitness
  obtain ⟨K, E, c, hinner, houter⟩ := claim φ hs hu v hv π hπ
  have hc (m : ℕ) : c m = 0 := by
    apply tendsto_nhds_unique (hinner m)
    apply tendsto_const_nhds.congr'
    filter_upwards [Filter.eventually_ge_atTop 1] with j hj
    simp only [divisorialKernelDifference_mul_laterIndicator ∅ (show 0 < j from hj),
      integral_zero, tsum_zero]
  rw [show c = fun _ ↦ 0 from funext hc, hsum, mul_one, hq, localMass,
    Complex.ofReal_one, div_one] at houter
  have he := tendsto_nhds_unique tendsto_const_nhds houter
  have hn : Real.log (↑(2 : ℕ) : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
  exact Complex.ofReal_ne_zero.mpr hn he.symm

end RiemannMasullo
