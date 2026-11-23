module

public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec1a
import Mathlib.Algebra.Field.ULift
import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings
import Mathlib.Analysis.Real.Pi.Irrational

import Mathlib.Analysis.Meromorphic.RCLike

import Mathlib.Algebra.Field.ULift
import all RiemannMasullo.Ch07_SchauderBasesZeta.Sec1a
import all RiemannMasullo.Ch02_AdelicTheta.Sec2a
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Gaussian.Schwartz

import Mathlib.Algebra.Field.ULift
import all RiemannMasullo.AppB_AnalyticNT.Sec3
import all RiemannMasullo.Ch02_AdelicTheta.Sec2a
import all RiemannMasullo.Ch03_IdelicZeta.Sec3b

/-! # §7.1.1–7.1.2 Statements that are false as printed -/

@[expose] public noncomputable section

open Asymptotics Filter IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped BigOperators NNReal

namespace RiemannMasullo

set_option quotPrecheck false

universe u

local notation "Places(" F ")" => HeightOneSpectrum (𝓞 F)
local notation "Jₛ(" F ", " S ")" => SIdeleQuotient F S
local notation "Tests(" F ", " S ")" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "normₛ(" F ", " S ")" => sIdeleQuotientNorm F S
local notation "twistₛ(" F ", " S ")" =>
  quasiCharacterNormTwist (G := Jₛ(F, S)) normₛ(F, S) (isProperMap_sIdeleQuotientNorm F S).continuous
local notation "circleToComplex" => (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ)
local notation "period(" v ")" => (2 * Real.pi / Real.log (Ideal.absNorm (HeightOneSpectrum.asIdeal v) : ℝ))

/-- Paper: Before Lemma 7.1.1.1, p. 313.
As printed: Each point of every unshifted lattice is a zero of the product
(7.1.1.1) with real phases tᵥ. The shift in the repaired finite-place pole list is in
`finiteHeckeEulerFactor_poles_iff`. See ERRATA F85. -/
def Printed.reciprocalPartialHeckeEulerProduct_unshifted_zeros : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset Places(F)) (t : S → ℝ)
    (v : S) (m : ℤ),
    let s : ℂ := ((m : ℝ) * period(v.val) : ℝ) * Complex.I
    ∏ w : S, (1 - (w.val.asIdeal.absNorm : ℂ) ^ (-s - (t w : ℂ) * Complex.I)) = 0

private theorem Printed.reciprocalPartialHeckeEulerProduct_unshifted_zeros_false_factor (q : ℕ)
    (hq : 1 < q) :
    1 - (q : ℂ) ^ (-(0 : ℂ) - ((Real.pi / Real.log q : ℝ) : ℂ) * Complex.I) ≠ 0 := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans hq).ne'
  have hlog : Real.log q ≠ 0 := by
    have : (1 : ℝ) < q := by exact_mod_cast hq
    exact (Real.log_pos this).ne'
  rw [Complex.cpow_def_of_ne_zero hq0, ← Complex.ofReal_natCast,
    ← Complex.ofReal_log (Nat.cast_nonneg q)]
  have : ((Real.log q : ℝ) : ℂ) * (-(0 : ℂ) - ((Real.pi / Real.log q : ℝ) : ℂ) * Complex.I) =
      -(Real.pi * Complex.I) := by
    have hlogc : ((Real.log q : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlog
    rw [Complex.ofReal_div]
    field_simp
    ring
  rw [this, Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

private theorem Printed.reciprocalPartialHeckeEulerProduct_unshifted_zeros_false_ulift
    (h : Printed.reciprocalPartialHeckeEulerProduct_unshifted_zeros.{u}) : False := by
  have : CharZero (ULift.{u} ℚ) := ⟨fun a b hab ↦ by simpa using congrArg ULift.down hab⟩
  have : NumberField (ULift.{u} ℚ) := ⟨⟩
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 (ULift.{u} ℚ))
  let v : HeightOneSpectrum (𝓞 (ULift.{u} ℚ)) := ⟨m, hm.isPrime, NeZero.ne m⟩
  have hq : 1 < Ideal.absNorm v.asIdeal := by
    have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact v.ne_bot
    have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]
      exact v.isPrime.ne_top
    omega
  have key := h (ULift.{u} ℚ) {v} (fun _ ↦ Real.pi / Real.log (Ideal.absNorm v.asIdeal))
    ⟨v, Finset.mem_singleton_self v⟩ 0
  simp only [Int.cast_zero, zero_mul, Complex.ofReal_zero] at key
  rw [Finset.prod_coe_sort ({v} : Finset _)
    (fun w ↦ 1 - (w.asIdeal.absNorm : ℂ) ^ (-(0 : ℂ) - ((Real.pi / Real.log
      (Ideal.absNorm v.asIdeal) : ℝ) : ℂ) * Complex.I)), Finset.prod_singleton] at key
  exact Printed.reciprocalPartialHeckeEulerProduct_unshifted_zeros_false_factor _ hq key

/-- Paper: Before Lemma 7.1.1.1, p. 313.
Take the rational field, the singleton place above 2, and tᵥ = π/(2 log 2).
At m = 0 the factor is 1 − exp(−iπ/2) = 1 + i. -/
theorem Printed.reciprocalPartialHeckeEulerProduct_unshifted_zeros_false :
    ¬ Printed.reciprocalPartialHeckeEulerProduct_unshifted_zeros :=
  fun h ↦ Printed.reciprocalPartialHeckeEulerProduct_unshifted_zeros_false_ulift h

/-- Paper: Lemma 7.1.2.2(1), p. 317.
As printed: At every complex place of angular weight k, a nonpositive integer in
`|k|/2 - ℕ` gives a pole of the correcting factor after the local imaginary shift.
This is the inclusion from the complex-place part of the pole list. The repaired list is
`sLocalRhoFactor_poles_iff`. See ERRATA F86. -/
def Printed.sLocalRhoFactor_complex_positive_shift : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset Places(F))
    (χ : PontryaginDual Jₛ(F, S)) (w : InfinitePlace F) (hw : w.IsComplex) (m : ℤ),
    let chart := twistₛ(F, S) ((circleToComplex).comp χ)
    let p := (complexLocalEulerParameters w hw (sLocalInfiniteRestriction w (chart 0))).exists.choose
    m ≤ 0 → (∃ n : ℕ, (m : ℝ) = (p.2.natAbs : ℝ) / 2 - n) →
      meromorphicOrderAt (fun z ↦ sLocalRhoFactor (chart z)) ((m : ℂ) - p.1) < 0

/-- The number `exp i` is not a root of unity, since `π` is irrational. -/
private theorem Printed.sLocalRhoFactor_complex_positive_shift_false_exp_I_pow (n : ℕ)
    (hn : 0 < n) : Complex.exp Complex.I ^ n ≠ 1 := by
  intro h
  rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff] at h
  obtain ⟨k, hk⟩ := h
  have h1 : (n : ℝ) = k * (2 * Real.pi) := by
    have := congrArg Complex.im hk
    simpa using this
  have hk0 : (k : ℝ) ≠ 0 := by
    rintro h0
    rw [h0, zero_mul] at h1
    exact hn.ne' (by exact_mod_cast h1)
  apply irrational_pi
  refine ⟨n / (2 * k), ?_⟩
  push_cast
  field_simp
  linarith

/-- With a single infinite place, which is complex, and no finite places, some unitary
character is nontrivial on the class of `exp i` inserted at that place. -/
private theorem Printed.sLocalRhoFactor_complex_positive_shift_false_exists_character
    (F : Type u) [Field F] [NumberField F] (w : InfinitePlace F)
    (hw : w.IsComplex) (huniq : ∀ w' : InfinitePlace F, w' = w) :
    ∃ η : PontryaginDual Jₛ(F, ∅),
      sLocalInfiniteRestriction w ((circleToComplex).comp η)
        (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm.toMonoidHom
          (Units.mk0 (Complex.exp Complex.I) (Complex.exp_ne_zero _))) ≠ 1 := by
  classical
  let S : Finset Places(F) := ∅
  let x0 : w.Completionˣ :=
    Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm.toMonoidHom
      (Units.mk0 (Complex.exp Complex.I) (Complex.exp_ne_zero _))
  let f : (v : InfinitePlace F) → v.Completionˣ := @Pi.mulSingle _ _ _ (Classical.decEq _) w x0
  have hf : f w = x0 := Pi.mulSingle_eq_same _ _
  let g : (SAdeleRing F S)ˣ :=
    (ContinuousMulEquiv.prodUnits (InfiniteAdeleRing F) ((i : S) → i.val.adicCompletion F)).symm
      (ContinuousMulEquiv.piUnits.symm f, 1)
  have hg : (QuotientGroup.mk g : Jₛ(F, S)) ≠ 1 := by
    intro he
    obtain ⟨u, hu⟩ := (sIdeleQuotient_mk_eq_one F S g).mp he
    have ha := congrArg (fun a : (SAdeleRing F S)ˣ ↦ a.val.1 w) hu
    change ((f w : w.Completionˣ) : w.Completion) =
      algebraMap F w.Completion (u.val : F) at ha
    rw [hf] at ha
    have hb := congrArg (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw) ha
    have hx0 : InfinitePlace.Completion.ringEquivComplexOfIsComplex hw (x0 : w.Completion) =
        Complex.exp Complex.I := by
      simp [x0]
    rw [hx0, InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply,
      AbsoluteValue.Completion.algebraMap_def,
      InfinitePlace.Completion.extensionEmbedding_coe] at hb
    have hwu : w (u.val : F) = 1 := by
      rw [← InfinitePlace.norm_embedding_eq]
      have := congrArg norm hb
      have h1 : ‖Complex.exp Complex.I‖ = 1 := by simpa using Complex.norm_exp_ofReal_mul_I 1
      rw [h1] at this
      exact this.symm
    have hint : IsIntegral ℤ (u.val : F) := by
      have hmem : (u.val : F) ∈ ((∅ : Finset Places(F)) : Set Places(F)).integer F := (u.val).2
      simp only [Finset.coe_empty, IsDedekindDomain.integer_empty, Algebra.mem_bot] at hmem
      obtain ⟨a, ha⟩ := hmem
      rw [← ha]
      exact a.isIntegral_coe
    obtain ⟨n, hn, hpow⟩ := Embeddings.pow_eq_one_of_norm_eq_one F ℂ hint (fun φ ↦ by
      rw [← InfinitePlace.apply, huniq (InfinitePlace.mk φ), hwu])
    apply Printed.sLocalRhoFactor_complex_positive_shift_false_exp_I_pow n hn
    have := congrArg w.embedding hpow
    rw [map_pow, map_one] at this
    rw [hb]
    exact this
  let : LocallyCompactSpace (SAdeleRing F S)ˣ := (sIdeleGroup_description F S).2.2.1
  have := isClosed_sProjectedDiagonal (F := F) (S := S)
  obtain ⟨η, hη⟩ := exists_pontryaginDual_apply_ne_one hg
  exact ⟨η, fun h ↦ hη (Subtype.ext h)⟩


/-- A field whose only infinite place is complex refutes the printed pole list: the square
of the character above has even nonzero weight, and zero is listed but is not a pole. -/
private theorem Printed.sLocalRhoFactor_complex_positive_shift_false_of_unique
    (F : Type u) [Field F] [NumberField F] (w : InfinitePlace F)
    (hw : w.IsComplex) (huniq : ∀ w' : InfinitePlace F, w' = w)
    (h : Printed.sLocalRhoFactor_complex_positive_shift.{u}) : False := by
  classical
  obtain ⟨η, hη⟩ :=
    Printed.sLocalRhoFactor_complex_positive_shift_false_exists_character F w hw huniq
  let S : Finset Places(F) := ∅
  have hzero : ∀ θ : PontryaginDual Jₛ(F, S),
      twistₛ(F, S) ((circleToComplex).comp θ) 0 = (circleToComplex).comp θ := by
    intro θ
    ext1 g
    change ((circleToComplex).comp θ) g * _ ^ (0 : ℂ) = ((circleToComplex).comp θ) g
    simp
  let χ : PontryaginDual Jₛ(F, S) := η * η
  let e : ℂˣ →* w.Completionˣ :=
    Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm.toMonoidHom
  let c := sLocalInfiniteRestriction w (twistₛ(F, S) ((circleToComplex).comp χ) 0)
  let c' := sLocalInfiniteRestriction w (twistₛ(F, S) ((circleToComplex).comp η) 0)
  let p := (complexLocalEulerParameters w hw c).exists.choose
  let q := (complexLocalEulerParameters w hw c').exists.choose
  have hq : ∀ x : ℂˣ, c' (e x) =
      ((‖(x : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ q.1 * ((x : ℂ) / (‖(x : ℂ)‖ : ℂ)) ^ q.2 :=
    (complexLocalEulerParameters w hw c').exists.choose_spec
  have hcc : ∀ y, c y = c' y * c' y := by
    intro y
    change twistₛ(F, S) ((circleToComplex).comp χ) 0 _ =
      twistₛ(F, S) ((circleToComplex).comp η) 0 _ * twistₛ(F, S) ((circleToComplex).comp η) 0 _
    rw [hzero, hzero]
    change (((η * η) _ : Circle) : ℂ) = ((η _ : Circle) : ℂ) * ((η _ : Circle) : ℂ)
    rfl
  have hq0 : q.2 ≠ 0 := by
    intro hk
    apply hη
    have h1 := hq (Units.mk0 (Complex.exp Complex.I) (Complex.exp_ne_zero _))
    have hn : ‖Complex.exp Complex.I‖ = 1 := by simpa using Complex.norm_exp_ofReal_mul_I 1
    rw [hk] at h1
    simp only [Units.val_mk0, hn, zpow_zero, mul_one, one_pow, Complex.ofReal_one,
      Complex.one_cpow] at h1
    rw [← h1]
    change _ = twistₛ(F, S) ((circleToComplex).comp η) 0 _
    rw [hzero]
    rfl
  have hp : p = (2 * q.1, q.2 * 2) := by
    refine (complexLocalEulerParameters w hw c).unique
      (complexLocalEulerParameters w hw c).exists.choose_spec ?_
    intro x
    rw [hcc, hq x]
    change _ = ((‖(x : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ (((2 : ℕ) : ℂ) * q.1) *
      ((x : ℂ) / (‖(x : ℂ)‖ : ℂ)) ^ (q.2 * 2)
    rw [Complex.cpow_nat_mul, zpow_mul, show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast]
    ring
  have key := h F S χ w hw 0 le_rfl ⟨q.2.natAbs, by
    change ((0 : ℤ) : ℝ) = (p.2.natAbs : ℝ) / 2 - q.2.natAbs
    rw [hp]
    simp only [Int.natAbs_mul]
    push_cast
    ring⟩
  have hpole := (sLocalRhoFactor_poles_iff χ _).1 key
  rcases hpole with ⟨w', hw', -, -⟩ | ⟨w', hw', n, hs⟩ | ⟨v, -⟩
  · exact (InfinitePlace.not_isReal_iff_isComplex.mpr hw) (huniq w' ▸ hw')
  · obtain rfl := huniq w'
    change ((0 : ℤ) : ℂ) - p.1 = -p.1 - (p.2.natAbs : ℂ) / 2 - (n : ℂ) at hs
    have h2 : |(p.2 : ℝ)| / 2 + n = 0 := by
      have := congrArg Complex.re hs
      simp at this
      linarith
    have h3 : (p.2 : ℝ) = 0 := abs_eq_zero.mp (by
      linarith [abs_nonneg (p.2 : ℝ), (Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    have h4 : p.2 = 0 := by exact_mod_cast h3
    rw [hp] at h4
    exact hq0 (by simpa using h4)
  · exact absurd v.2 (Finset.notMem_empty _)


/-- A quadratic field containing a primitive fourth root of unity has exactly one infinite
place, and it is complex. -/
private theorem Printed.sLocalRhoFactor_complex_positive_shift_false_unique_place
    (F : Type u) [Field F] [NumberField F] (hd : Module.finrank ℚ F = 2)
    (ζ : F) (hζ : IsPrimitiveRoot ζ 4) :
    ∃ w : InfinitePlace F, w.IsComplex ∧ ∀ w' : InfinitePlace F, w' = w := by
  classical
  have hr := InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt (by norm_num) hζ
  have h2 := InfinitePlace.card_add_two_mul_card_eq_rank (K := F)
  have hc : Fintype.card (InfinitePlace F) = 1 := by
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
    omega
  obtain ⟨w, hw⟩ := Fintype.card_eq_one_iff.mp hc
  refine ⟨w, ?_, hw⟩
  rcases InfinitePlace.isReal_or_isComplex w with h | h
  · have : 0 < InfinitePlace.nrRealPlaces F :=
      Fintype.card_pos_iff.mpr ⟨⟨w, h⟩⟩
    omega
  · exact h

/-- The Gaussian field `ℚ(i)`, lifted to universe `u`, refutes the printed pole list. -/
private theorem Printed.sLocalRhoFactor_complex_positive_shift_false_ulift
    (h : Printed.sLocalRhoFactor_complex_positive_shift.{u}) : False := by
  have : NeZero ((4 : ℕ) : ℚ) := ⟨by norm_num⟩
  have : IsCyclotomicExtension {4} ℚ (CyclotomicField 4 ℚ) :=
    CyclotomicField.isCyclotomicExtension 4 ℚ
  have : CharZero (ULift.{u} (CyclotomicField 4 ℚ)) := ⟨fun a b hab ↦ by
    have := congrArg ULift.down hab
    simpa using this⟩
  have : FiniteDimensional ℚ (ULift.{u} (CyclotomicField 4 ℚ)) :=
    LinearEquiv.finiteDimensional (ULift.moduleEquiv (R := ℚ) (M := CyclotomicField 4 ℚ)).symm
  have : NumberField (ULift.{u} (CyclotomicField 4 ℚ)) := ⟨⟩
  have hd : Module.finrank ℚ (ULift.{u} (CyclotomicField 4 ℚ)) = 2 := by
    rw [LinearEquiv.finrank_eq (ULift.moduleEquiv (R := ℚ) (M := CyclotomicField 4 ℚ)),
      IsCyclotomicExtension.finrank (CyclotomicField 4 ℚ)
        (Polynomial.cyclotomic.irreducible_rat (n := 4) (by norm_num))]
    decide
  have hζ : IsPrimitiveRoot
      (ULift.up.{u} (IsCyclotomicExtension.zeta 4 ℚ (CyclotomicField 4 ℚ))) 4 :=
    (IsCyclotomicExtension.zeta_spec 4 ℚ (CyclotomicField 4 ℚ)).map_of_injective
      (f := (ULift.ringEquiv (R := CyclotomicField 4 ℚ)).symm.toRingHom)
      ULift.ringEquiv.symm.injective
  obtain ⟨w, hw, huniq⟩ := Printed.sLocalRhoFactor_complex_positive_shift_false_unique_place
    (ULift.{u} (CyclotomicField 4 ℚ)) hd _ hζ
  exact Printed.sLocalRhoFactor_complex_positive_shift_false_of_unique
    (ULift.{u} (CyclotomicField 4 ℚ)) w hw huniq h

/-- Paper: Lemma 7.1.2.2(1), p. 317.
Take ℚ(i) with only its complex place and the character `(z/|z|)^4`, which descends
through the four units. The printed list includes zero, but the numerator Γℂ(s + 2)
and the denominator Γℂ(3 − s) are regular and nonzero there. -/
theorem Printed.sLocalRhoFactor_complex_positive_shift_false :
    ¬ Printed.sLocalRhoFactor_complex_positive_shift :=
  fun h ↦ Printed.sLocalRhoFactor_complex_positive_shift_false_ulift h

section Theta

variable {F : Type u} [Field F] [NumberField F] {S : Finset Places(F)}

local instance printedCh07Sec1aNormOneMeasurableSpace :
    MeasurableSpace (normₛ(F, S)).ker := borel _

local instance printedCh07Sec1aNormOneHaar :
    (sLocalNormOneQuotientMeasure F S).IsHaarMeasure :=
  (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1

open Classical in
/-- Paper: Theorem 7.1.2.3, equation (7.1.2.3), p. 318.
As printed: This is the scalar expansion for every A > 0. The first sum uses
0 < m < A. Its coefficient is evaluated at the printed expression for cᵥ,ₘ,χ,
with exponent m − itᵥ from p. 317, while its norm weight has exponent m + itᵥ.
The pole list on p. 316 only admits m ≤ 0. For positive m the displayed
expression is in the holomorphic half-plane and the inner sum is empty.
At A = 1/2 even the outer integer range is empty, independently of this
index conflict. Each unramified finite place contributes its own copy of
the full Laurent coefficients.
The series converges uniformly on compact sets along horizontal contour cutoffs
(p. 322), and the scalar remainder is of order `O(|g|^A)`.
See `sLocalHomogeneousAdelicTheta_rat_not_isBigO_sqrt` and ERRATA F87–F89. -/
def Printed.sLocalHomogeneousAdelicTheta_asymptotic : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset Places(F))
    (χ : PontryaginDual Jₛ(F, S)) (f : Tests(F, S)) (A : ℝ), 0 < A →
    let chart := twistₛ(F, S) ((circleToComplex).comp χ)
    let normℝ (g : Jₛ(F, S)) := ((normₛ(F, S) g : ℝ≥0) : ℝ)
    let ω := χ.comp (⟨(normₛ(F, S)).ker.subtype, continuous_subtype_val⟩ :
      (normₛ(F, S)).ker →ₜ* Jₛ(F, S))
    let term (a weight : ℂ) (g : Jₛ(F, S)) :=
      ∑ j ∈ Finset.range (sLocalPolarMultiplicity f (chart a)),
        (-1 : ℂ) ^ j * sLocalZLaurentCoeff f (chart a) (j : ℤ) / (j.factorial : ℂ) *
          star (χ g : ℂ) * (normℝ g : ℂ) ^ weight * (Real.log (normℝ g) : ℂ) ^ j
    let archPhase (w : InfinitePlace F) :=
      let c := sLocalInfiniteRestriction w (chart 0)
      if hw : w.IsReal then (realLocalEulerParameters w hw c).exists.choose.1
      else
        (complexLocalEulerParameters w (InfinitePlace.not_isReal_iff_isComplex.mp hw) c).exists.choose.1
    let archSum (g : Jₛ(F, S)) :=
      ∑ w : InfinitePlace F, ∑ m ∈ Finset.Ioo 0 (Nat.ceil A),
        term ((m : ℂ) - archPhase w) ((m : ℂ) + archPhase w) g
    let phase (v : S) (t : ℝ) :=
      t ∈ Ico 0 (period(v.val)) ∧ ∀ x : (v.val.adicCompletion F)ˣ,
        sLocalFiniteRestriction v (chart 0) x =
          (‖(x : v.val.adicCompletion F)‖ : ℂ) ^ ((t : ℂ) * Complex.I)
    let finitePlaces := Finset.univ.filter (fun v : S ↦ ∃ t, phase v t)
    let partialSum (height : ℝ) (g : Jₛ(F, S)) :=
      ∑ v : ↥finitePlaces,
        let t := (Finset.mem_filter.mp v.property).2.choose
        let d := period(v.val.val)
        ∑ m ∈ Finset.Ioo ⌊(t - height) / d⌋ ⌈(t + height) / d⌉,
          let a : ℂ := ((m : ℝ) * d - t : ℝ) * Complex.I
          term a (-a) g
    ∃ (T : ℕ → ℝ) (finiteSum : Jₛ(F, S) → ℂ), Tendsto T atTop atTop ∧
      (∀ K : Set Jₛ(F, S), IsCompact K →
        TendstoUniformlyOn (fun n ↦ partialSum (T n)) finiteSum atTop K) ∧
      IsBigO (comap normℝ (𝓝[>] 0))
        (fun g ↦ sLocalHomogeneousAdelicTheta F S (sLocalNormOneQuotientMeasure F S) ω f g -
          (archSum g + finiteSum g))
        (fun g ↦ Real.rpow (normℝ g) A)

/-- With no finite places and cutoff one half, the printed expansion has only its remainder. -/
private theorem sLocalHomogeneousAdelicTheta_asymptotic_false_empty
    (h : Printed.sLocalHomogeneousAdelicTheta_asymptotic.{u})
    (F : Type u) [Field F] [NumberField F] (f : Tests(F, ∅)) :
    let r (g : Jₛ(F, ∅)) : ℝ := (normₛ(F, ∅) g).val
    IsBigO (comap r (𝓝[>] 0))
      (sLocalHomogeneousAdelicTheta F ∅ (sLocalNormOneQuotientMeasure F ∅) 1 f : Jₛ(F, ∅) → ℂ)
      (fun g ↦ r g ^ (1 / 2 : ℝ)) := by
  classical
  have H := h F ∅ 1 f (1 / 2) one_half_pos
  extract_lets chart r ω term archPhase archSum phase places partialSum at H
  obtain ⟨T, L, _, hlim, hO⟩ := H
  have hL (g : Jₛ(F, ∅)) : L g = 0 := by
    refine tendsto_nhds_unique ((hlim {g} isCompact_singleton).tendsto_at (mem_singleton g)) ?_
    refine tendsto_const_nhds.congr fun n ↦ ?_
    dsimp only [partialSum]
    exact (Finset.sum_eq_zero fun v _ ↦ (Finset.notMem_empty _ v.val.property).elim).symm
  have hm : Finset.Ioo 0 ⌈(1 / 2 : ℝ)⌉₊ = ∅ := by
    have hceil : ⌈(1 / 2 : ℝ)⌉₊ ≤ 1 := Nat.ceil_le.mpr (by norm_num)
    ext m
    simp only [Finset.mem_Ioo, Finset.notMem_empty, iff_false]
    omega
  refine hO.congr_left fun g ↦ sub_eq_self.2 ?_
  have ha : archSum g = 0 := by simp only [archSum, hm, Finset.sum_empty, Finset.sum_const_zero]
  rw [ha, hL, add_zero]

/-- At a single real place the pullback of the real Gaussian depends only on the idelic norm. -/
private theorem sLocalHomogeneousAdelicTheta_asymptotic_false_gaussian
    (F : Type u) [Field F] [NumberField F] [Unique (InfinitePlace F)]
    (hw : (default : InfinitePlace F).IsReal) :
    ∃ f : Tests(F, ∅), ∀ g : (SAdeleRing F ∅)ˣ, f (Multiplicative.ofAdd g.val) =
      (Real.exp (-(((sIdeleNorm F ∅ g).val : ℝ) ^ 2)) : ℂ) := by
  let w : InfinitePlace F := default
  let j := InfinitePlace.Completion.isometryEquivRealOfIsReal hw
  let e : SAdeleRing F ∅ ≃ₜ ℝ := ((Homeomorph.prodUnique _ _).trans
    (Homeomorph.piUnique fun v : InfinitePlace F ↦ v.Completion)).trans j.toHomeomorph
  let a : SAdeleRing F ∅ ≃+ ℝ :=
    { e.toEquiv with
      map_add' := fun x y ↦ map_add (InfinitePlace.Completion.ringEquivRealOfIsReal hw)
        (x.1 w) (y.1 w) }
  let E : Multiplicative (SAdeleRing F ∅) ≃ₜ* Multiplicative ℝ :=
    { a.toMultiplicative with
      continuous_toFun := e.continuous
      continuous_invFun := e.symm.continuous }
  have : T2Space (Multiplicative (SAdeleRing F ∅)) := e.isEmbedding.t2Space
  have : LocallyCompactSpace (Multiplicative (SAdeleRing F ∅)) :=
    e.isOpenEmbedding.locallyCompactSpace
  have : T2Space (Multiplicative ℝ) := inferInstanceAs (T2Space ℝ)
  have : LocallyCompactSpace (Multiplicative ℝ) := inferInstanceAs (LocallyCompactSpace ℝ)
  obtain ⟨b, hb⟩ := exists_gaussian_schwartz (E := ℝ) 1 zero_lt_one
  obtain ⟨T, hT⟩ := realSchwartzBruhat_equiv
  refine ⟨⟨(T b).val ∘ E, schwartzBruhat_mem_comp_equiv E (T b).property⟩, fun g ↦ ?_⟩
  change T b (Multiplicative.ofAdd (j (g.val.1 w))) = _
  rw [hT, hb, neg_one_mul, j.isometry.norm_map_of_map_zero (map_zero
    (InfinitePlace.Completion.ringEquivRealOfIsReal hw))]
  rw [sIdeleNorm, Finset.univ_eq_empty (α := (∅ : Finset Places(F))), Finset.prod_empty,
    mul_one, Fintype.prod_subsingleton _ w, hw.mult_eq_one, pow_one]
  rfl

/-- For a copy of ℚ the two unit translates of a radial Gaussian agree, and averaging
over norm-one classes contributes the total Haar mass. -/
private theorem sLocalHomogeneousAdelicTheta_asymptotic_false_average
    (F : Type u) [Field F] [NumberField F] (e : F ≃+* ℚ) (f : Tests(F, ∅))
    (hf : ∀ g : (SAdeleRing F ∅)ˣ, f (Multiplicative.ofAdd g.val) =
      (Real.exp (-(((sIdeleNorm F ∅ g).val : ℝ) ^ 2)) : ℂ)) (g : Jₛ(F, ∅)) :
    sLocalHomogeneousAdelicTheta F ∅ (sLocalNormOneQuotientMeasure F ∅) 1 f g =
      ((sLocalNormOneQuotientMeasure F ∅).real univ : ℂ) *
        (2 * (Real.exp (-(((normₛ(F, ∅) g).val : ℝ) ^ 2)) : ℂ)) := by
  let φ (t : ℝ≥0ˣ) : ℂ := Real.exp (-((t.val : ℝ) ^ 2))
  let U := (((∅ : Finset Places(F)) : Set Places(F)).integer F)ˣ
  have hcard : Nat.card U = 2 := by
    dsimp only [U]
    rw [Finset.coe_empty, integer_empty]
    let a := Algebra.botEquivOfInjective (IsFractionRing.injective (𝓞 F) F)
    let b := (RingOfIntegers.mapRingEquiv e).trans Rat.ringOfIntegersEquiv
    rw [Nat.card_congr (Units.mapEquiv (a.toRingEquiv.trans b).toMulEquiv).toEquiv,
      Nat.card_eq_fintype_card, Fintype.card_units_int]
  have hclass (x : Jₛ(F, ∅)) : sLocalAdelicThetaOnClasses F ∅ f x = 2 * φ (normₛ(F, ∅) x) := by
    refine Quotient.inductionOn x fun y ↦ ?_
    refine (sLocalAdelicThetaOnClasses_mk F ∅ f y).trans ((sLocalAdelicTheta_apply F ∅ f y).trans ?_)
    calc
      _ = ∑' _ : U, φ (sIdeleNorm F ∅ y) := by
        apply tsum_congr
        intro u
        refine (hf (_ * y)).trans (congrArg φ ?_)
        rw [map_mul, MonoidHom.comp_apply,
          show sIdeleNorm F ∅ _ = 1 from (sIdeleNorm_spec F ∅).2 ⟨u, rfl⟩, one_mul]
      _ = _ := by
        rw [tsum_const, hcard, nsmul_eq_mul, Nat.cast_ofNat, sIdeleQuotientNorm_mk]
  change (∫ h : (normₛ(F, ∅)).ker, sLocalAdelicThetaOnClasses F ∅ f (g * h.val) *
    ((1 : PontryaginDual (normₛ(F, ∅)).ker) h : ℂ) ∂_) = _
  have hker (h : (normₛ(F, ∅)).ker) : normₛ(F, ∅) h.val = 1 := h.property
  simp only [hclass, map_mul, hker, mul_one, PontryaginDual.one_apply, Circle.coe_one,
    integral_const, Complex.real_smul, φ]

/-- Every type universe contains a number field isomorphic to ℚ. -/
private theorem sLocalHomogeneousAdelicTheta_asymptotic_false_ratCopy :
    ∃ (F : Type u) (_ : Field F) (_ : NumberField F), Nonempty (F ≃+* ℚ) := by
  let e : ULift.{u} ℚ ≃+* ℚ := ULift.ringEquiv
  have : CharZero (ULift.{u} ℚ) := RingHom.charZero e.toRingHom
  have : FiniteDimensional ℚ (ULift.{u} ℚ) :=
    Module.Finite.equiv e.toRatAlgEquiv.toLinearEquiv.symm
  exact ⟨ULift.{u} ℚ, inferInstance, {}, ⟨e⟩⟩

/-- Paper: Theorem 7.1.2.3, equation (7.1.2.3), p. 318.
Over ℚ with only the real place, take the trivial character, `A = 1/2`, and a real
Gaussian. Both sums are empty and theta has a positive limit at norm zero.
For the finite-place overlap take ℚ with finite places 2 and 3, the trivial character,
and `A = 1/2`. At the finite places use the integer-ring indicators. At the real place
take a positive log-profile obtained by convolving a nonzero nonnegative smooth bump in
(0,1) with the indicators of [0, log 2] and [0, log 3]. The zeta function is a positive
constant times `6^s H(s)/s^2`, where H is the Mellin transform of the original bump
in the log coordinate. The origin is its only pole. Each finite-place series contributes
the printed logarithmic coefficient `-a₁`, whereas the inverse Mellin transform has
coefficient `-a₋₂`. The ratio 2a₁/a₋₂ is the bump-weighted mean of
(u + log 6)³/3, which exceeds one on (0,1). -/
theorem Printed.sLocalHomogeneousAdelicTheta_asymptotic_false :
    ¬ Printed.sLocalHomogeneousAdelicTheta_asymptotic := by
  classical
  intro h
  obtain ⟨F, _, _, ⟨e⟩⟩ := sLocalHomogeneousAdelicTheta_asymptotic_false_ratCopy
  have hd : Module.finrank ℚ F = 1 :=
    e.toRatAlgEquiv.toLinearEquiv.finrank_eq.trans (Module.finrank_self ℚ)
  have hR := InfinitePlace.nrRealPlaces_eq_one_of_finrank_eq_one hd
  have hC := InfinitePlace.nrComplexPlaces_eq_zero_of_finrank_eq_one hd
  have : Subsingleton (InfinitePlace F) := Fintype.card_le_one_iff_subsingleton.mp
    (by rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, hR, hC])
  obtain ⟨⟨w, hw⟩⟩ := Fintype.card_pos_iff.mp (show 0 < InfinitePlace.nrRealPlaces F by omega)
  let : Unique (InfinitePlace F) := uniqueOfSubsingleton w
  obtain ⟨f, hf⟩ := sLocalHomogeneousAdelicTheta_asymptotic_false_gaussian F hw
  let r (g : Jₛ(F, ∅)) : ℝ := (normₛ(F, ∅) g).val
  have hr : Ioi 0 ⊆ range r := by
    intro t ht
    obtain ⟨s, hs⟩ := sIdeleQuotientNorm_exists_section F ∅
    let v : ℝ≥0ˣ := Units.mk0 ⟨t, ht.le⟩ (ne_of_gt (show (0 : ℝ≥0) < ⟨t, ht.le⟩ from ht))
    exact ⟨s v, congrArg (fun v : ℝ≥0ˣ ↦ (v.val : ℝ)) (hs v)⟩
  have : CompactSpace (normₛ(F, ∅)).ker := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm F ∅).isCompact_preimage (isCompact_singleton (x := 1)))
  have : IsFiniteMeasure (sLocalNormOneQuotientMeasure F ∅) := CompactSpace.isFiniteMeasure
  exact sLocalHomogeneousAdelicTheta_rat_not_isBigO_sqrt_limit r hr _
    (Complex.ofReal_ne_zero.mpr (measureReal_univ_pos (μ := sLocalNormOneQuotientMeasure F ∅)).ne') _
    (sLocalHomogeneousAdelicTheta_asymptotic_false_average F e f hf)
    (sLocalHomogeneousAdelicTheta_asymptotic_false_empty h F f)

end Theta

/-- Paper: Theorem 7.1.2.3, equation (7.1.2.3), p. 318.
As printed: In the finite-place contribution of a pole to Mellin inversion, the coefficient of
`(-log t)^(k-1)/(k-1)!` is the Laurent coefficient of index k − 1. This states the
residue formula in the centered coordinate, with the common weight at the center removed.
The signed indices are those of `sLocalZLaurentCoeff`. See ERRATA F89. -/
def Printed.sLocalZLaurentCoeff_mellinResidue : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset Places(F))
    (χ : PontryaginDual Jₛ(F, S)) (v : S) (tᵥ : ℝ) (m : ℤ) (f : Tests(F, S)),
    let chart := twistₛ(F, S) ((circleToComplex).comp χ)
    tᵥ ∈ Ico 0 (period(v.val)) →
    (∀ x : (v.val.adicCompletion F)ˣ, sLocalFiniteRestriction v (chart 0) x =
      (‖(x : v.val.adicCompletion F)‖ : ℂ) ^ ((tᵥ : ℂ) * Complex.I)) →
    let c := chart (((m : ℝ) * period(v.val) - tᵥ : ℝ) * Complex.I)
    ∀ t : ℝ, 0 < t →
      complexResidue (fun z ↦ (t : ℂ) ^ (-z) * sLocalIdelicZFunction f (twistₛ(F, S) c z)) 0 =
        ∑ j ∈ Finset.range (sLocalPolarMultiplicity f c),
          sLocalZLaurentCoeff f c (j : ℤ) * (-(Real.log t : ℂ)) ^ j / (j.factorial : ℂ)

/-- Cauchy's differentiation formula, in the normalization used for the Laurent coefficients. -/
private theorem sLocalZLaurentCoeff_mellinResidue_false_residue_sq
    {A : ℂ → ℂ} (hA : AnalyticAt ℂ A 0) :
    complexResidue (fun z ↦ A z / z ^ 2) 0 = deriv A 0 := by
  obtain ⟨R, hR, ha⟩ := hA.exists_ball_analyticOnNhd
  refine (tendsto_const_nhds.congr' ?_).limUnder_eq
  filter_upwards [Ioo_mem_nhdsGT hR] with r hr
  have hd := (ha.mono (Metric.closedBall_subset_ball hr.2)).differentiableOn
  have hc := hd.deriv_eq_smul_circleIntegral hr.1
  simpa only [sub_zero, smul_eq_mul, one_div, ← div_eq_inv_mul, mul_div_cancel_left₀ _
    (show 2 * (Real.pi : ℂ) * Complex.I ≠ 0 by simp [Real.pi_ne_zero])] using
      (congrArg (· / (2 * (Real.pi : ℂ) * Complex.I)) hc).symm

/-- At the trivial center and `t = 1`, the printed identity forces the numerator of every
simple pole to agree with its derivative. -/
private theorem sLocalZLaurentCoeff_mellinResidue_false_numerator
    {F : Type u} [Field F] [NumberField F]
    {S : Finset Places(F)} (v : S) (h : Printed.sLocalZLaurentCoeff_mellinResidue.{u})
    (f : Tests(F, S)) (A : ℂ → ℂ) (hA : AnalyticAt ℂ A 0) (hne : A 0 ≠ 0)
    (he : (fun z ↦ sLocalIdelicZFunction f (twistₛ(F, S) 1 z)) =ᶠ[𝓝[≠] 0]
      (fun z ↦ A z / z)) : A 0 = deriv A 0 := by
  let chart := twistₛ(F, S) ((circleToComplex).comp (1 : PontryaginDual Jₛ(F, S)))
  have base : (circleToComplex).comp (1 : PontryaginDual Jₛ(F, S)) = 1 := by ext; rfl
  have h0 : chart 0 = 1 := by
    ext x
    change ((1 : Circle) : ℂ) * _ ^ (0 : ℂ) = 1
    simp
  have hm : MeromorphicAt (fun z ↦ sLocalIdelicZFunction f (twistₛ(F, S) 1 z)) 0 := by
    rw [← base]
    exact ((sLocalIdelicZFunction_meromorphic f 1) (mem_univ _)).meromorphicAt
  have hord := (meromorphicOrderAt_eq_int_iff (n := -1) hm).mpr ⟨A, hA, hne, by
    filter_upwards [he] with z hz
    simpa only [sub_zero, zpow_neg_one, smul_eq_mul, ← div_eq_inv_mul] using hz⟩
  have hmult : sLocalPolarMultiplicity f 1 = 1 := by simp [sLocalPolarMultiplicity, hord]
  have hv : 0 < period(v.val) := div_pos (mul_pos (by norm_num) Real.pi_pos)
    (Real.log_pos (by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v.val))
  have hres := h F S 1 v 0 0 f ⟨le_rfl, hv⟩ (by
    intro x
    change sLocalFiniteRestriction v (chart 0) x = _
    rw [h0]; simp; rfl) 1 zero_lt_one
  let ξ := chart ((((0 : ℤ) : ℝ) * period(v.val) - 0 : ℝ) * Complex.I)
  have hξ : ξ = 1 := by simpa [ξ] using h0
  change complexResidue (fun z ↦ ((1 : ℝ) : ℂ) ^ (-z) *
      sLocalIdelicZFunction f (twistₛ(F, S) ξ z)) 0 =
    ∑ j ∈ Finset.range (sLocalPolarMultiplicity f ξ),
      sLocalZLaurentCoeff f ξ (j : ℤ) * (-(Real.log 1 : ℂ)) ^ j / (j.factorial : ℂ) at hres
  rw [hξ, hmult] at hres
  simp [sLocalZLaurentCoeff] at hres
  have hl : complexResidue _ 0 = A 0 := (complexResidue_congr he).trans
    (by simpa only [sub_zero] using complexResidue_div_sub hA)
  refine hl.symm.trans (hres.trans ((complexResidue_congr ?_).trans
    (sLocalZLaurentCoeff_mellinResidue_false_residue_sq hA)))
  filter_upwards [he] with z hz
  simp only [hz, div_div, pow_two]

/-- With one infinite place the archimedean test is pulled back by coordinate evaluation. -/
private theorem sLocalZLaurentCoeff_mellinResidue_false_tensor
    {F : Type u} [Field F] [NumberField F]
    [Unique (InfinitePlace F)] {S : Finset Places(F)}
    (a : (w : InfinitePlace F) → SchwartzBruhat (Multiplicative w.Completion))
    (b : (v : S) → SchwartzBruhat (Multiplicative (v.val.adicCompletion F))) :
    ∃ f : Tests(F, S), ∀ x : SAdeleRing F S, f (Multiplicative.ofAdd x) =
      (∏ w, a w (Multiplicative.ofAdd (x.1 w))) * ∏ v, b v (Multiplicative.ofAdd (x.2 v)) := by
  let w : InfinitePlace F := default
  let e : Multiplicative (InfiniteAdeleRing F) ≃ₜ* Multiplicative w.Completion :=
    { Homeomorph.piUnique (fun i : InfinitePlace F ↦ i.Completion) with map_mul' := fun _ _ ↦ rfl }
  let : T2Space (Multiplicative w.Completion) := inferInstanceAs (T2Space w.Completion)
  let : LocallyCompactSpace (Multiplicative w.Completion) :=
    inferInstanceAs (LocallyCompactSpace w.Completion)
  let : T2Space (Multiplicative (InfiniteAdeleRing F)) := e.toHomeomorph.isEmbedding.t2Space
  let : LocallyCompactSpace (Multiplicative (InfiniteAdeleRing F)) :=
    e.toHomeomorph.isOpenEmbedding.locallyCompactSpace
  let g : SchwartzBruhat (Multiplicative (InfiniteAdeleRing F)) :=
    ⟨(a w).val ∘ e, schwartzBruhat_mem_comp_equiv e (a w).property⟩
  obtain ⟨T, hT⟩ := sAdeleSchwartz_inductiveTensor_equiv F S
  refine ⟨T (TensorProduct.tmul ℂ g (PiTensorProduct.tprod ℂ b)), fun x ↦ ?_⟩
  rw [hT, Fintype.prod_subsingleton _ w]
  rfl

/-- Pair a real test giving a simple pole with a finite test having nonzero constant transform.
Translating the latter multiplies the numerator by the complex power of the idelic norm. -/
private theorem sLocalZLaurentCoeff_mellinResidue_false_contradiction
    {F : Type u} [Field F] [NumberField F]
    [Unique (InfinitePlace F)] (hw : ∀ w : InfinitePlace F, w.IsReal)
    (S : Finset Places(F)) [Unique S] (h : Printed.sLocalZLaurentCoeff_mellinResidue.{u}) : False := by
  classical
  let w : InfinitePlace F := default
  let v : S := default
  let α (i : InfinitePlace F) := quasiCharacterNormTwist
    ((Units.map nnNormHom.toMonoidHom) ^ i.mult) (continuous_infiniteLocalModule i)
    ((circleToComplex).comp (1 : PontryaginDual i.Completionˣ))
  let β (i : S) := quasiCharacterNormTwist (Units.map nnNormHom.toMonoidHom)
    (continuous_finiteLocalModule i.val)
    ((circleToComplex).comp (1 : PontryaginDual (i.val.adicCompletion F)ˣ))
  let chart := twistₛ(F, S) ((circleToComplex).comp (1 : PontryaginDual Jₛ(F, S)))
  have harch (i : InfinitePlace F) (s : ℂ) : sLocalInfiniteRestriction i (chart s) = α i s := by
    ext1 x
    rw [sLocalInfiniteRestriction_normTwist]
    change _ = ((1 : Circle) : ℂ) * _
    rw [Circle.coe_one, one_mul]; rfl
  have hfin (i : S) (s : ℂ) : sLocalFiniteRestriction i (chart s) = β i s := by
    ext1 x
    have hn := sLocalFiniteRestriction_norm i x
    change ((1 : Circle) : ℂ) * (_ : ℂ) ^ (1 : ℂ) = _ at hn
    simp only [Circle.coe_one, one_mul, Complex.cpow_one] at hn
    change ((1 : Circle) : ℂ) * _ ^ s = ((1 : Circle) : ℂ) * _ ^ s
    rw [hn]
  -- Use the even, trivial-character pole at the real place.
  have hpole (i : InfinitePlace F) := (infiniteLocalIdelicZFunction_real_poles i (hw i) 1 0
    (fun _ ↦ by simp; rfl) 0).2.mpr ⟨0, by simp⟩
  choose a ha using hpole
  let Z (z : ℂ) := infiniteLocalIdelicZFunction w (a w) (α w z)
  have hm : Meromorphic Z := fun z ↦
    (((infiniteLocalIdelicZFunction_existsUnique w (a w)).exists.choose_spec 1).1
      (mem_univ z)).meromorphicAt
  obtain ⟨H, hH, hnH, hZ⟩ := (meromorphicOrderAt_eq_int_iff (n := -1) (hm 0)).mp (ha w)
  choose b C hnC hb using fun i : S ↦ exists_finite_constant_zeta_test i.val 1
  let B (z : ℂ) := H z * C v
  have hB : AnalyticAt ℂ B 0 := hH.mul analyticAt_const
  have hnB : B 0 ≠ 0 := mul_ne_zero hnH (hnC v)
  have allD (p : (i : S) → (i.val.adicCompletion F)ˣ) :
      B 0 = deriv (fun z : ℂ ↦ B z * (‖(p v).val‖ : ℂ) ^ z) 0 := by
    let r : ℂ := ‖(p v).val‖
    have hr : r ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (p v).ne_zero)
    have hrA := (differentiable_id.const_cpow (c := r) (Or.inl hr)).analyticAt
    let d := fun i ↦ schwartzBruhatUnitTranslate (p i) (b i)
    obtain ⟨f, hf⟩ := sLocalZLaurentCoeff_mellinResidue_false_tensor a d
    let G (z : ℂ) := sLocalIdelicZFunction f (chart z)
    have heq (z : ℂ) (hz : 0 < z.re) : G z = Z z * (r ^ z * C v) := by
      have eq := sLocalIdelicZetaIntegral_pureTensor (chart z) ⟨1, z, hz, rfl⟩ f a d hf
      rw [Fintype.prod_subsingleton _ w, Fintype.prod_subsingleton _ v, harch, hfin] at eq
      refine (sLocalIdelicZFunction_eq_integral f ⟨1, z, hz, rfl⟩).trans (eq.trans ?_)
      congr 1
      · exact (infiniteLocalIdelicZFunction_eq_integral w (a w) 1 hz).symm
      · exact (finiteZeta_dilate v.val _ (β v z) (p v)).trans
          (congrArg₂ (· * ·) (finite_norm_chart_apply v.val z (p v)) (hb v z))
    -- Continue the product identity from the right half-plane to the punctured germ.
    have hM : Meromorphic G := fun z ↦
      ((sLocalIdelicZFunction_meromorphic f 1) (mem_univ z)).meromorphicAt
    have he := meromorphic_eq_of_germ hM
      (fun z ↦ (hm z).mul (((hrA z).mul analyticAt_const).meromorphicAt))
      (z := 1) (by
        have hh : {z : ℂ | 0 < z.re} ∈ 𝓝 (1 : ℂ) :=
          (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)
        filter_upwards [nhdsWithin_le_nhds hh] with z hz using heq z hz)
    have base : (circleToComplex).comp (1 : PontryaginDual Jₛ(F, S)) = 1 := by ext; rfl
    have hG : (fun z ↦ sLocalIdelicZFunction f (twistₛ(F, S) 1 z)) =ᶠ[𝓝[≠] 0]
        fun z ↦ (B z * r ^ z) / z := by
      rw [← base]
      filter_upwards [he.filter_mono (nhdsNE_le_codiscrete 0), hZ] with z hz hzz
      change G z = _
      change G z = Z z * (r ^ z * C v) at hz
      rw [hz, hzz]
      simp only [B, sub_zero, zpow_neg_one, smul_eq_mul, div_eq_mul_inv]
      ring
    simpa only [Complex.cpow_zero, mul_one] using
      sLocalZLaurentCoeff_mellinResidue_false_numerator v h f
        (fun z ↦ B z * r ^ z) (hB.mul (hrA 0)) (by simpa using hnB) hG
  -- Compare the unit translate with the uniformizer translate.
  have hd : B 0 = deriv B 0 := by simpa using allD (fun _ ↦ 1)
  choose p hp using fun i : S ↦ exists_finite_norm_uniformizer i.val
  have hd' := allD p
  let r : ℂ := ‖(p v).val‖
  have hr : r ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (p v).ne_zero)
  change B 0 = deriv (fun z ↦ B z * r ^ z) 0 at hd'
  have hdiff : DifferentiableAt ℂ (fun z : ℂ ↦ r ^ z) 0 :=
    (differentiable_id.const_cpow (c := r) (Or.inl hr)).differentiableAt
  rw [deriv_fun_mul hB.differentiableAt hdiff, Complex.deriv_const_cpow_id] at hd'
  simp only [Complex.cpow_zero, mul_one] at hd'
  have hdiff₀ : B 0 * Complex.log r = 0 := by linear_combination hd - hd'
  have hlog : Complex.log r = 0 := (mul_eq_zero.mp hdiff₀).resolve_left hnB
  have hone : r = 1 := by rw [← Complex.exp_log hr, hlog, Complex.exp_zero]
  have hlt : ‖(p v).val‖ < 1 := by
    rw [hp]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v.val)
  exact hlt.ne (Complex.ofReal_injective (hone.trans Complex.ofReal_one.symm))

/-- Paper: Theorem 7.1.2.3, equation (7.1.2.3), p. 318.
Over ℚ take the place above 2, χ = 1, tᵥ = m = 0 and t = 1. Use a smooth
nonzero nonnegative real bump supported in (exp 1, exp 2) times the indicator of ℤ₂.
Its transform is B(s)/(1 − 2⁻ˢ), where B′(0) > B(0) > 0 since log x > 1
on the bump. The residue is B(0)/log 2. The printed coefficient is
a₀ = B′(0)/log 2 + B(0)/2, strictly larger. -/
theorem Printed.sLocalZLaurentCoeff_mellinResidue_false :
    ¬ Printed.sLocalZLaurentCoeff_mellinResidue := by
  classical
  intro h
  have : CharZero (ULift ℚ) := ⟨fun a b hab ↦ by simpa using congrArg ULift.down hab⟩
  have : NumberField (ULift ℚ) := ⟨⟩
  let F := ULift ℚ
  have hd : Module.finrank ℚ F = 1 := by
    change Module.finrank ℚ (ULift ℚ) = 1
    rw [finrank_ulift, Module.finrank_self]
  have hreal := InfinitePlace.nrRealPlaces_eq_one_of_finrank_eq_one hd
  have hcomplex := InfinitePlace.nrComplexPlaces_eq_zero_of_finrank_eq_one hd
  have hcard : Fintype.card (InfinitePlace F) = 1 := by
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, hreal, hcomplex, add_zero]
  let := (Fintype.card_eq_one_iff_nonempty_unique.mp hcard).some
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 F)
  let v : Places(F) := ⟨m, hm.isPrime, NeZero.ne m⟩
  apply sLocalZLaurentCoeff_mellinResidue_false_contradiction (F := F) (S := {v}) _ h
  intro w
  have hr : Nonempty {i : InfinitePlace F // i.IsReal} :=
    Fintype.card_pos_iff.mp (by rw [← InfinitePlace.nrRealPlaces, hreal]; decide)
  obtain ⟨i, hi⟩ := hr
  simpa only [Subsingleton.elim i w] using hi

/-- Paper: Proof of Theorem 7.1.2.3, p. 322.
As printed: The continued S-local zeta transform has a finite L¹ norm on the vertical
line of real part −A for every positive A, as required for the stated remainder
bound. The obstruction is recorded in `Sec1a`. See ERRATA F90. -/
def Printed.sLocalIdelicZFunction_verticalIntegrable_neg : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset Places(F))
    (χ : PontryaginDual Jₛ(F, S)) (f : Tests(F, S)) (A : ℝ), 0 < A →
      Complex.VerticalIntegrable
        (fun s ↦ sLocalIdelicZFunction f (twistₛ(F, S) ((circleToComplex).comp χ) s)) (-A)

/-- At a simple pole the vertical restriction dominates a constant times `1 / |t|`. -/
private theorem sLocalIdelicZFunction_verticalIntegrable_neg_simplePole {Z : ℂ → ℂ} {σ : ℝ}
    (hZ : MeromorphicAt Z (σ : ℂ)) (hp : meromorphicOrderAt Z (σ : ℂ) = -1) :
    ¬ Complex.VerticalIntegrable Z σ := by
  obtain ⟨g, hg, hg₀, he⟩ := (meromorphicOrderAt_eq_int_iff (n := -1) hZ).mp hp
  let l (t : ℝ) : ℂ := σ + t * Complex.I
  have hl : Tendsto l (𝓝 (0 : ℝ)) (𝓝 (σ : ℂ)) := by
    have hc : Continuous l := by dsimp [l]; fun_prop
    simpa [l] using hc.tendsto 0
  have hle : Tendsto l (𝓝[≠] (0 : ℝ)) (𝓝[≠] (σ : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hl.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin (α := ℝ) (a := 0) (s := {0}ᶜ)] with t ht
    simpa [l] using ht
  have hpos : 0 < ‖g (σ : ℂ)‖ := norm_pos_iff.mpr hg₀
  have hbound : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ‖g (σ : ℂ)‖ / 2 < ‖g (l t)‖ :=
    ((hg.continuousAt.norm.tendsto.comp hl).eventually
      (lt_mem_nhds (half_lt_self hpos))).filter_mono nhdsWithin_le_nhds
  have hO : (fun t : ℝ ↦ (t - 0)⁻¹) =O[𝓝[≠] 0] (fun t ↦ Z (l t)) := by
    refine isBigO_iff''.mpr ⟨_, half_pos hpos, ?_⟩
    filter_upwards [hbound, hle.eventually he] with t ht heq
    simp only [heq, norm_smul, zpow_neg_one, norm_inv, show l t - (σ : ℂ) = t * Complex.I by simp [l],
      norm_mul, Complex.norm_I, mul_one, Complex.norm_real, sub_zero]
    rw [mul_comm (‖g (σ : ℂ)‖ / 2)]
    exact mul_le_mul_of_nonneg_left ht.le (by positivity)
  intro hi
  exact not_intervalIntegrable_of_sub_inv_isBigO_punctured hO zero_ne_one left_mem_uIcc
    (hi.intervalIntegrable (a := 0) (b := 1))

/-- For a field with just one place at infinity, real, transport a test realizing the local
simple pole at −2. Its S-local transform agrees with the local one by continuation. -/
private theorem sLocalIdelicZFunction_verticalIntegrable_neg_onePlace (F : Type u) [Field F] [NumberField F]
    [Unique (InfinitePlace F)] (hw : (default : InfinitePlace F).IsReal) :
    ∃ f : Tests(F, ∅), ¬ Complex.VerticalIntegrable
      (fun s ↦ sLocalIdelicZFunction f (twistₛ(F, ∅) ((circleToComplex).comp
        (1 : PontryaginDual Jₛ(F, ∅))) s)) (-2) := by
  classical
  let w := (default : InfinitePlace F)
  let χ := (1 : PontryaginDual Jₛ(F, ∅))
  let chart := twistₛ(F, ∅) ((circleToComplex).comp χ)
  let localChart := quasiCharacterNormTwist (Units.map nnNormHom.toMonoidHom ^ w.mult)
    (continuous_infiniteLocalModule w) ((circleToComplex).comp (1 : PontryaginDual w.Completionˣ))
  obtain ⟨g, hgp⟩ := (infiniteLocalIdelicZFunction_real_poles w hw 1 0
    (fun x ↦ by simp only [Fin.val_zero, pow_zero, Complex.cpow_zero, mul_one]; rfl) (-2)).2.mpr
      ⟨1, by norm_num⟩
  let D := infiniteLocalIdelicZFunction w g ∘ localChart
  let e : SAdeleRing F ∅ ≃ₜ w.Completion := (Homeomorph.prodUnique _ _).trans
    (Homeomorph.piUnique fun v : InfinitePlace F ↦ v.Completion)
  let E : Multiplicative (SAdeleRing F ∅) ≃ₜ* Multiplicative w.Completion :=
    ContinuousMulEquiv.mk' e (fun _ _ ↦ rfl)
  have : LocallyCompactSpace (Multiplicative w.Completion) :=
    inferInstanceAs (LocallyCompactSpace w.Completion)
  have : LocallyCompactSpace (Multiplicative (SAdeleRing F ∅)) :=
    e.isOpenEmbedding.locallyCompactSpace
  have : T2Space (Multiplicative (SAdeleRing F ∅)) := e.isEmbedding.t2Space
  let f : Tests(F, ∅) := ⟨g.val ∘ E, schwartzBruhat_mem_comp_equiv E g.property⟩
  let Z (s : ℂ) := sLocalIdelicZFunction f (chart s)
  let a (v : InfinitePlace F) : SchwartzBruhat (Multiplicative v.Completion) :=
    Subsingleton.elim w v ▸ g
  let b (v : (∅ : Finset Places(F))) : SchwartzBruhat (Multiplicative (v.val.adicCompletion F)) := 0
  have hf (x : SAdeleRing F ∅) : f (Multiplicative.ofAdd x) =
      (∏ v, a v (Multiplicative.ofAdd (x.1 v))) *
        ∏ v : (∅ : Finset Places(F)), b v (Multiplicative.ofAdd (x.2 v)) := by
    simp only [Finset.univ_eq_empty (α := (∅ : Finset Places(F))), Finset.prod_empty, mul_one]
    rw [Fintype.prod_subsingleton (fun v ↦ a v (Multiplicative.ofAdd (x.1 v))) w]
    rfl
  have hch (s : ℂ) : sLocalInfiniteRestriction w (chart s) = localChart s := by
    ext1 x
    rw [sLocalInfiniteRestriction_normTwist]
    exact (one_mul _).symm
  have heq (s : ℂ) (hs : 0 < s.re) : Z s = D s := by
    have hc := sLocalIdelicZFunction_eq_integral f (x := chart s) ⟨χ, s, hs, rfl⟩
    have ht := sLocalIdelicZetaIntegral_pureTensor (chart s) ⟨χ, s, hs, rfl⟩ f a b hf
    simp only [Finset.univ_eq_empty (α := (∅ : Finset Places(F))), Finset.prod_empty, mul_one] at ht
    rw [Fintype.prod_subsingleton _ w, hch] at ht
    exact hc.trans (ht.trans (infiniteLocalIdelicZFunction_eq_integral w g 1 hs).symm)
  have hZ : MeromorphicNFOn Z univ := sLocalIdelicZFunction_meromorphic f χ
  have hD : MeromorphicNFOn D univ :=
    ((infiniteLocalIdelicZFunction_existsUnique w g).exists.choose_spec 1).1
  have hZD : Z = D := by
    funext s
    have hnear : Z =ᶠ[𝓝[≠] (1 : ℂ)] D := by
      have hpos : ∀ᶠ z : ℂ in 𝓝 (1 : ℂ), 0 < z.re :=
        (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
      exact (hpos.filter_mono nhdsWithin_le_nhds).mono (fun z hz ↦ heq z hz)
    have h0 := (hZ.meromorphicOn.sub hD.meromorphicOn).meromorphicOrderAt_eq_top_of_isPreconnected
      isPreconnected_univ (mem_univ (1 : ℂ)) (mem_univ s)
      (meromorphicOrderAt_eq_top_iff.mpr (hnear.mono fun _ hz ↦ sub_eq_zero.mpr hz))
    have h1 : Z =ᶠ[𝓝[≠] s] D := (meromorphicOrderAt_eq_top_iff.mp h0).mono fun _ hz ↦ sub_eq_zero.mp hz
    exact (((hZ (mem_univ s)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds (hD (mem_univ s))).mp h1).self_of_nhds
  refine ⟨f, sLocalIdelicZFunction_verticalIntegrable_neg_simplePole (hZ (mem_univ _)).meromorphicAt ?_⟩
  change meromorphicOrderAt Z ((-2 : ℝ) : ℂ) = -1
  rw [hZD]
  simpa using hgp

/-- Paper: Proof of Theorem 7.1.2.3, p. 322.
Take ℚ(√2), only its two real places, the trivial character, and at each place
`x² exp(-πx²)`. The zeta transform is a nonzero constant times Γℝ(s + 2)².
At A = 2 its norm on the vertical line is of order `|Im s|⁻²` near −2. -/
theorem Printed.sLocalIdelicZFunction_verticalIntegrable_neg_false :
    ¬ Printed.sLocalIdelicZFunction_verticalIntegrable_neg := by
  classical
  intro h
  have : CharZero (ULift ℚ) := ⟨fun a b hab ↦ by simpa using congrArg ULift.down hab⟩
  have : NumberField (ULift ℚ) := ⟨⟩
  let F := ULift ℚ
  have hd : Module.finrank ℚ F = 1 := by simp [F, finrank_ulift]
  have hr := InfinitePlace.nrRealPlaces_eq_one_of_finrank_eq_one hd
  have hc := InfinitePlace.nrComplexPlaces_eq_zero_of_finrank_eq_one hd
  have hcard : Fintype.card (InfinitePlace F) = 1 := by
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, hr, hc, add_zero]
  let : Unique (InfinitePlace F) := (Fintype.card_eq_one_iff_nonempty_unique.mp hcard).some
  obtain ⟨v⟩ : Nonempty {v : InfinitePlace F // v.IsReal} :=
    Fintype.card_pos_iff.mp (by change 0 < InfinitePlace.nrRealPlaces F; omega)
  have hw : (default : InfinitePlace F).IsReal := Subsingleton.elim v.val default ▸ v.property
  obtain ⟨f, hf⟩ := sLocalIdelicZFunction_verticalIntegrable_neg_onePlace F hw
  exact hf (h F ∅ 1 f 2 (by norm_num))

/-- Paper: Discussion of Theorem 7.1.2.3, p. 320.
As printed: Each nonnegative Laurent coefficient at c is an S-local eigendistribution
of weight c. This states the eigencharacter law using the scalar coefficient
`sLocalZLaurentCoeff` and the translation action of §5.5. See ERRATA F91. -/
def Printed.sLocalZLaurentCoeff_eigendistribution : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset Places(F))
    (c : QuasiCharacter Jₛ(F, S)) (m : ℕ) (g : (SAdeleRing F S)ˣ) (f : Tests(F, S)),
    sLocalZLaurentCoeff (schwartzBruhatUnitTranslate g f) c (m : ℤ) =
      c (QuotientGroup.mk g) * sLocalZLaurentCoeff f c (m : ℤ)

/-- Paper: Discussion of Theorem 7.1.2.3, p. 320.
Over ℚ with only the real place and the trivial center, use m = 0 and the
Gaussian `exp(-πx²)`. Replacing it by `exp(-π(x/2)²)` multiplies its zeta
transform by `2^s`. The residue is 2, so the constant coefficient changes
by `2 log 2`, contrary to the trivial weight law. -/
theorem Printed.sLocalZLaurentCoeff_eigendistribution_false :
    ¬ Printed.sLocalZLaurentCoeff_eigendistribution := by sorry

/-- Paper: Discussion of Theorem 7.1.2.3, p. 321.
As printed: The coefficient whose Laurent index equals the finite-place lattice
index is supported on the corresponding periodic locus. In particular it vanishes on
tests whose support misses the inverse image of that locus, where the indicated
finite coordinate is zero. The scalar coefficient is `sLocalZLaurentCoeff`.
See ERRATA F92. -/
def Printed.sLocalZLaurentCoeff_finitePlace_support : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset Places(F))
    (χ : PontryaginDual Jₛ(F, S)) (v : S) (t : ℝ) (m : ℤ) (f : Tests(F, S)),
    let chart := twistₛ(F, S) ((circleToComplex).comp χ)
    t ∈ Ico 0 (period(v.val)) →
      (∀ x : (v.val.adicCompletion F)ˣ, sLocalFiniteRestriction v (chart 0) x =
        (‖(x : v.val.adicCompletion F)‖ : ℂ) ^ ((t : ℂ) * Complex.I)) →
      Disjoint (tsupport (fun x ↦ f x))
        {x : Multiplicative (SAdeleRing F S) | x.toAdd.2 v = 0} →
      sLocalZLaurentCoeff f (chart ((((m : ℝ) * period(v.val) - t : ℝ) : ℂ) * Complex.I)) m = 0

/-- Paper: Discussion of Theorem 7.1.2.3, p. 321.
Take ℚ with the real place and the place above 2, the trivial character and m = 0.
Use a nonzero nonnegative smooth bump supported in (1,2) times the indicator of
ℤ₂ˣ. The support avoids the zero at the finite coordinate, but the zeta integral
is holomorphic at zero and its constant term is strictly positive. -/
theorem Printed.sLocalZLaurentCoeff_finitePlace_support_false :
    ¬ Printed.sLocalZLaurentCoeff_finitePlace_support := by sorry

/-- Paper: Proof of Theorem 7.1.2.3, p. 321.
As printed: For every test the trivial-character zeta function has pole order equal
to the number of infinite places at the origin. The test-dependent order is
`sLocalPolarMultiplicity`. See ERRATA F93. -/
def Printed.sLocalPolarMultiplicity_trivial_origin : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset Places(F)) (f : Tests(F, S)),
    sLocalPolarMultiplicity f 1 = Fintype.card (InfinitePlace F)

/-- Paper: Proof of Theorem 7.1.2.3, p. 321.
The zero test over ℚ with only the real place has no pole. Over ℚ with the real
place and the place above 2, the Gaussian times the indicator of ℤ₂ instead
has a double pole from Γℝ(s) and the Euler factor at 2. -/
theorem Printed.sLocalPolarMultiplicity_trivial_origin_false :
    ¬ Printed.sLocalPolarMultiplicity_trivial_origin := by
  intro h
  let F := ULift ℚ
  let : NumberField F := NumberField.of_ringEquiv ℚ F ULift.ringEquiv.symm
  let f : Tests(F, ∅) := ⟨0, (schwartzBruhatSubmodule _).zero_mem⟩
  have hZ : sLocalIdelicZFunction f = fun _ ↦ 0 := by
    have hcont := sLocalIdelicZetaIntegral_exists_continuation f
    exact hcont.unique hcont.exists.choose_spec
      ⟨fun _ _ _ ↦ analyticAt_const.meromorphicNFAt, fun c _ ↦ by
        simp [sLocalIdelicZetaIntegral, f]⟩
  have hmult : sLocalPolarMultiplicity f 1 = 0 := by
    simp [sLocalPolarMultiplicity, hZ, meromorphicOrderAt_const]
  exact Fintype.card_ne_zero ((h F ∅ f).symm.trans hmult)

/-- Paper: Coefficient formula after Theorem 7.1.2.3, p. 323.
As printed: The Laurent coefficient of index k − 1 is given by the contour integral
around any continuously differentiable simple contour enclosing the center.
The local coefficient is `sLocalZLaurentCoeff`. See ERRATA F94. -/
def Printed.sLocalZLaurentCoeff_any_contour : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset Places(F))
    (χ : PontryaginDual Jₛ(F, S)) (f : Tests(F, S)) (a : ℂ) (k : ℕ), 1 ≤ k →
    ∀ γ : ComplexContour, ContDiffOn ℝ 1 γ.toContinuousMap (Icc 0 1) →
      InjOn γ.toContinuousMap (Ico 0 1) → a ∉ γ.trace → γ.index a ≠ 0 →
        let chart := twistₛ(F, S) ((circleToComplex).comp χ)
        let integrand := fun s ↦ sLocalIdelicZFunction f (chart s) / (s - a) ^ k
        HasPettisIntegral (PettisMeasure.complex γ.measure) integrand
          (2 * (Real.pi : ℂ) * Complex.I * sLocalZLaurentCoeff f (chart a) ((k : ℤ) - 1))

/-- Paper: Coefficient formula after Theorem 7.1.2.3, p. 323.
For ℚ with only its real place take the Gaussian, the trivial character,
a = 0 and k = 1. The counterclockwise circle of radius 3 centered at zero also
encloses −2. The residue of Γℝ(s)/s at −2 adds π to the local coefficient. -/
theorem Printed.sLocalZLaurentCoeff_any_contour_false :
    ¬ Printed.sLocalZLaurentCoeff_any_contour := by sorry

end RiemannMasullo
