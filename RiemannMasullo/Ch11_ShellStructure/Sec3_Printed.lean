module

public import RiemannMasullo.Ch10_TraceSpectral.Sec4b
public import RiemannMasullo.Ch11_ShellStructure.Sec3

import Mathlib.NumberTheory.NumberField.Discriminant.Different
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

/-- Paper: §11.3.1.1, p. 493. Take F = ℚ(√−7), the trivial character and the
finite base above 7. The field has discriminant −7 and class number one.
At k = 1 the sole rational prime is 2, outside the base. The integral generator
(1+√−7)/2 has polynomial X²−X+2, with two distinct roots modulo 2.
At the two places over 2 take components 2 and 2⁻¹ and put one elsewhere.
Their local norms multiply to one, although neither component is a unit. -/
theorem Printed.primaryDivisorialStratum_eq_norm_preimage_false :
    ¬ Printed.primaryDivisorialStratum_eq_norm_preimage := by sorry

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

private theorem uniformizerExists (v : Vℚ) :
    ∃ π : (v.adicCompletion ℚ)ˣ, Valued.v.IsUniformizer (π : v.adicCompletion ℚ) := by
  let val : Valuation (v.adicCompletion ℚ) (WithZero (Multiplicative ℤ)) := Valued.v
  obtain ⟨π, hπ⟩ : ∃ π : v.adicCompletionIntegers ℚ, val.IsUniformizer (π : v.adicCompletion ℚ) :=
    val.exists_isUniformizer_of_isCyclic_of_nontrivial
  exact ⟨Units.mk0 π.val hπ.ne_zero, hπ⟩

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

private theorem ratTrivialNormTwist : ideleClassNormTwist (1 : PontryaginDual C(ℚ)) 0 = 1 := by
  ext g
  change (1 : ℂ) * _ ^ (0 : ℂ) = 1
  simp

private theorem ratTrivialUnramified (v : Vℚ) :
    (ideleClassNormTwist (1 : PontryaginDual C(ℚ)) 0).IsUnramifiedAt v := by
  rw [ratTrivialNormTwist, HeckeCharacter.isUnramifiedAt_iff]
  intro x
  simp

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
    have hu := ratTrivialUnramified v
    rw [hf, reciprocalPartialHeckeEulerProduct_singleton _ v hu, placeNorm,
      hu.localValue_eq (π v) (hπ v)] at h
    rw [ratTrivialNormTwist, HeckeCharacter.restrict, MulChar.ofUnitHom_coe] at h
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
      (fun w _ ↦ ratTrivialUnramified w) π (fun w _ ↦ hπ w)
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

/-- Paper: Theorem 11.3.2.1, p. 495. Take F = ℚ, the trivial character,
the archimedean base, the standard norm section and the first layer at 2.
Choose a nonnegative smooth log-norm bump with value one at norm 2,
supported at norms in (3/2, 5/2). The weight vanishes off the section. On the
section the two divisorial indicators agree. The right side is log 2. -/
theorem Printed.orbitalTracesOnPaleyWienerLevels_false :
    ¬ Printed.orbitalTracesOnPaleyWienerLevels := by
  intro claim
  obtain ⟨φ, v, π, hv, hq, hπ, hs, hu, hsum⟩ := primeTwoWitness
  have hpic : Subsingleton (CommRing.Pic (((∅ : Finset Vℚ) : Set Vℚ).integer ℚ)) := by
    rw [Finset.coe_empty, integer_empty]
    let e := (Algebra.botEquivOfInjective (IsFractionRing.injective (𝓞 ℚ) ℚ)).toRingEquiv
    let i := Rat.ringOfIntegersEquiv.symm.trans e.symm
    let := IsPrincipalIdealRing.of_surjective i i.surjective
    infer_instance
  let : IsPrincipalIdealRing (𝓞 ℚ) := IsPrincipalIdealRing.of_surjective
    Rat.ringOfIntegersEquiv.symm Rat.ringOfIntegersEquiv.symm.surjective
  have hex := claim ℚ 1 φ ∅ (by simp)
    (fun w _ ↦ Ideal.ramificationIdx_eq_one w.asIdeal (𝓞 ℚ))
    (fun w _ ↦ ratTrivialUnramified w) hu hpic hs 2 0 (by norm_num) (by norm_num)
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

end RiemannMasullo
