module

public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec1b
import all RiemannMasullo.Ch05_ThetaZSpaces.Sec1
import Mathlib.Algebra.Field.ULift

/-! # §7.1.3–7.1.4 Statements that are false as printed -/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped NNReal

namespace RiemannMasullo

set_option quotPrecheck false

universe u

local notation "Places(" F ")" => HeightOneSpectrum (𝓞 F)
local notation "RatPrimes" => HeightOneSpectrum (𝓞 ℚ)
local notation "C𝔽(" F ")" => IdeleClassGroup (𝓞 F) F
local notation "U𝔽(" F ")" => PontryaginDual C𝔽(F)
local notation "Jₛ(" F ", " S ")" => SIdeleQuotient F S
local notation "normₛ(" F ", " S ")" => sIdeleQuotientNorm F S
local notation "twistₛ(" F ", " S ")" =>
  quasiCharacterNormTwist (G := Jₛ(F, S)) normₛ(F, S) (isProperMap_sIdeleQuotientNorm F S).continuous
local notation "circleToComplex" => (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ)
local notation "overₚ(" T "," p ")" =>
  ((T).filter (fun v ↦ HeightOneSpectrum.under (𝓞 ℚ) v = p))
local notation "Bergman" => SchwartzBergman (univ : Set ℝ)
local notation "halfPlane" => Complex.re ⁻¹' Ioi (1 : ℝ)
local notation "Entire" => Subtype (fun f : C(ℂ, ℂ) ↦ f ∈ entireContinuousMapSubalgebra)
local notation "Zeros(" L ")" => {ρ : ℂ // 0 < meromorphicOrderAt L ρ}
local notation "Jet(" L ", " ρ ")" =>
  entireJetSpace ρ (meromorphicOrderAt L ρ).untop₀.toNat

local instance printedCh07Sec1bStrongDualTopology : TopologicalSpace (StrongDual ℂ Entire) :=
  ContinuousLinearMap.topologicalSpace (σ := RingHom.id ℂ) (E := Entire) (F := ℂ)

open Classical in
/-- Paper: Remark 7.1.3.1, equation (7.1.3.1), p. 324.
As printed: For a finite-order character twisted by an imaginary norm power, infinitely
many rational primes satisfy the product identity with unshifted exponent once the
selected places contain all places above the prime. The translated formula is
`infinite_split_primes_reciprocalEulerProduct_normTwist`. See ERRATA F95. -/
def Printed.infinite_split_primes_reciprocalEulerProduct_normTwist : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (χ χ₀ : U𝔽(F)),
    IsOfFinOrder χ₀ → ∀ x : ℝ,
      ideleClassNormTwist χ 0 = ideleClassNormTwist χ₀ ((x : ℂ) * Complex.I) →
      {p : RatPrimes | ∀ S₀ : Finset Places(F),
        (∀ v : Places(F), v.under (𝓞 ℚ) = p → v ∈ S₀) →
        ∀ s : ℂ, reciprocalPartialHeckeEulerProduct χ overₚ(S₀, p) s =
          (1 - (p.asIdeal.absNorm : ℂ) ^ (-s)) ^ Module.finrank ℚ F}.Infinite

private theorem infinite_split_primes_reciprocalEulerProduct_normTwist_char (F : Type*) [Field F] [NumberField F] (x : ℝ) : ∃ χ : PontryaginDual (IdeleClassGroup (𝓞 F) F),
    ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) ((x : ℂ) * Complex.I) := by
  let c := ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) ((x : ℂ) * Complex.I)
  have hn (g : IdeleClassGroup (𝓞 F) F) : ‖c g‖ = 1 := by
    change ‖(1 : ℂ) * (((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ ((x : ℂ) * Complex.I)‖ = 1
    rw [one_mul, Complex.norm_cpow_eq_rpow_re_of_pos
      (NNReal.coe_pos.mpr (Units.zero_lt _))]
    simp
  let χ : PontryaginDual (IdeleClassGroup (𝓞 F) F) :=
    { toFun := fun g ↦ ⟨c g, mem_sphere_zero_iff_norm.mpr (hn g)⟩
      map_one' := Subtype.ext (map_one c)
      map_mul' := fun a b ↦ Subtype.ext (map_mul c a b)
      continuous_toFun := c.continuous.subtype_mk _ }
  refine ⟨χ, ?_⟩
  ext1 g
  change c g * _ ^ (0 : ℂ) = c g
  simp

private theorem infinite_split_primes_reciprocalEulerProduct_normTwist_local (F : Type*) [Field F] [NumberField F] (x : ℝ) (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) ((x : ℂ) * Complex.I))
    (p : HeightOneSpectrum (𝓞 F)) (hu : (ideleClassNormTwist χ 0).IsUnramifiedAt p) :
    (ideleClassNormTwist χ 0).localValue p = (p.asIdeal.absNorm : ℂ) ^ (-((x : ℂ) * Complex.I)) := by
  let val : Valuation (p.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
  obtain ⟨π, hπ⟩ := val.exists_isUniformizer_of_isCyclic_of_nontrivial
  let u := Units.mk0 (π : p.adicCompletion F) hπ.ne_zero
  rw [hu.localValue_eq u hπ, HeckeCharacter.restrict, MulChar.ofUnitHom_coe, hχ]
  change (1 : ℂ) * (((ideleClassNorm F (IdeleClassGroup.ofAdicCompletion (𝓞 F) F p u) : ℝ≥0) : ℝ) : ℂ) ^ ((x : ℂ) * Complex.I) = _
  rw [one_mul, ideleClassNorm_ofAdicCompletion]
  change (‖(π : p.adicCompletion F)‖ : ℂ) ^ _ = _
  have hn : ‖(π : p.adicCompletion F)‖ = (p.asIdeal.absNorm : ℝ)⁻¹ := by
    have hval : Valued.v (π : p.adicCompletion F) = WithZero.exp (-1 : ℤ) := hπ.trans
      (congrArg Units.val (Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
        (p.valuedAdicCompletion_surjective F)))
    rw [FinitePlace.norm_def, hval, WithZeroMulInt.toNNReal_neg_apply _ (by simp)]
    simp
  rw [hn,
      Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg (Nat.cast_nonneg _) , ← Complex.cpow_neg, Complex.ofReal_natCast]

private theorem infinite_split_primes_reciprocalEulerProduct_normTwist_generic : ∃ x : ℝ, ∀ n : ℕ, 1 < n → (n : ℂ) ^ (-((x : ℂ) * Complex.I)) ≠ 1 := by
  -- A generic twist avoids even the exceptional prime in the explicit example:
  -- for each possible norm n > 1, only countably many x give n^(-ix) = 1.
  let bad : ℕ → Set ℝ := fun n ↦ {x | 1 < n ∧ (n : ℂ) ^ (-((x : ℂ) * Complex.I)) = 1}
  have hc (n : ℕ) : (bad n).Countable := by
    by_cases hn : 1 < n
    · have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      have hlog : Complex.log (n : ℂ) ≠ 0 := by
        rw [← Complex.natCast_log]
        apply Complex.ofReal_ne_zero.mpr
        exact (Real.log_pos (by exact_mod_cast hn)).ne'
      have hi : Function.Injective (fun x : ℝ ↦ Complex.log (n : ℂ) * (-((x : ℂ) * Complex.I))) := by
        intro a b h
        apply Complex.ofReal_injective
        have h' := mul_left_cancel₀ hlog h
        have h'' : (a : ℂ) * Complex.I = (b : ℂ) * Complex.I := neg_injective h'
        exact mul_right_cancel₀ Complex.I_ne_zero h''
      have he : (Complex.exp ⁻¹' ({1} : Set ℂ)).Countable := (Set.countable_singleton 1).preimage_cexp
      apply (he.preimage hi).mono
      intro x hx
      change Complex.exp (Complex.log (n : ℂ) * (-((x : ℂ) * Complex.I))) = 1
      exact (Complex.cpow_def_of_ne_zero hn0 _).symm.trans hx.2
    · have : bad n = ∅ := by ext x; simp [bad, hn]
      simp [this]
  have hall := Set.countable_iUnion hc
  have hne : (⋃ n, bad n) ≠ Set.univ := fun h ↦ Set.not_countable_univ (h ▸ hall)
  obtain ⟨x, hx⟩ : ∃ x, x ∉ ⋃ n, bad n := by simpa [Set.eq_univ_iff_forall] using hne
  refine ⟨x, ?_⟩
  intro n hn he
  exact hx (Set.mem_iUnion.mpr ⟨n, ⟨hn, he⟩⟩)

open Classical in
private theorem infinite_split_primes_reciprocalEulerProduct_normTwist_aux (F : Type*) [Field F] [NumberField F]
    (h : ∀ (χ χ₀ : PontryaginDual (IdeleClassGroup (𝓞 F) F)),
      IsOfFinOrder χ₀ → ∀ x : ℝ,
        ideleClassNormTwist χ 0 = ideleClassNormTwist χ₀ ((x : ℂ) * Complex.I) →
        {p : HeightOneSpectrum (𝓞 ℚ) | ∀ S₀ : Finset (HeightOneSpectrum (𝓞 F)),
          (∀ v, v.under (𝓞 ℚ) = p → v ∈ S₀) → ∀ s : ℂ,
          reciprocalPartialHeckeEulerProduct χ (S₀.filter (fun v ↦ v.under (𝓞 ℚ) = p)) s =
            (1 - (p.asIdeal.absNorm : ℂ) ^ (-s)) ^ Module.finrank ℚ F}.Infinite) : False := by
  classical
  obtain ⟨x, hx⟩ := infinite_split_primes_reciprocalEulerProduct_normTwist_generic
  obtain ⟨χ, hχ⟩ := infinite_split_primes_reciprocalEulerProduct_normTwist_char F x
  have hi := h χ 1 IsOfFinOrder.one x hχ
  obtain ⟨p, hp⟩ := hi.nonempty
  let A : Set (HeightOneSpectrum (𝓞 F)) := {v | v.under (𝓞 ℚ) = p}
  have hf : A.Finite := by
    let f : A → p.asIdeal.primesOver (𝓞 F) := fun v ↦ ⟨v.1.asIdeal, v.1.isPrime,
      ⟨(congrArg HeightOneSpectrum.asIdeal v.2).symm⟩⟩
    have hfi : Function.Injective f := by
      intro a b hab
      exact Subtype.ext (HeightOneSpectrum.ext (congrArg Subtype.val hab))
    let : Finite A := Finite.of_injective f hfi
    exact Set.toFinite A
  let S := hf.toFinset
  have hs := hp S (fun v hv ↦ hf.mem_toFinset.mpr hv) 0
  have hd : Module.finrank ℚ F ≠ 0 := (Module.finrank_pos (R := ℚ) (M := F)).ne'
  simp only [neg_zero, Complex.cpow_zero, sub_self, zero_pow hd] at hs
  change (∏ v ∈ S.filter (fun v ↦ v.under (𝓞 ℚ) = p), (finiteHeckeEulerFactor χ v 0)⁻¹) = 0 at hs
  obtain ⟨v, hv, hz⟩ := Finset.prod_eq_zero_iff.mp hs
  by_cases hu : (ideleClassNormTwist χ 0).IsUnramifiedAt v
  · rw [finiteHeckeEulerFactor, ite_eq_left hu, inv_inv] at hz
    simp only [neg_zero, Complex.cpow_zero, mul_one, sub_eq_zero] at hz
    have he := infinite_split_primes_reciprocalEulerProduct_normTwist_local F x χ hχ v hu
    exact hx v.asIdeal.absNorm (HeightOneSpectrum.one_lt_absNorm v) (he.symm.trans hz.symm)
  · simp [finiteHeckeEulerFactor, hu] at hz

/-- Paper: Remark 7.1.3.1, equation (7.1.3.1), p. 324.
Use ℚ, the trivial finite-order character, and x = 2π/log 2. At s = 0 the
identity requires p^(-ix) = 1, so the rational prime p is an integral power
of 2. Only the prime 2 can satisfy the identity. -/
theorem Printed.infinite_split_primes_reciprocalEulerProduct_normTwist_false :
    ¬ Printed.infinite_split_primes_reciprocalEulerProduct_normTwist := by
  intro h
  -- Lift ℚ to the universe quantified over by the printed claim.
  let : Field (ULift ℚ) := { ULift.ring, ULift.groupWithZero, Equiv.ulift.field with }
  have : CharZero (ULift ℚ) := ⟨fun a b hab ↦ by simpa using congrArg ULift.down hab⟩
  have : NumberField (ULift ℚ) :=
    { to_finiteDimensional := Module.Finite.ulift (R := ℚ) (M := ℚ) }
  exact infinite_split_primes_reciprocalEulerProduct_normTwist_aux (ULift ℚ) (h (ULift ℚ))


open Classical in
/-- Paper: Theorem 7.1.3.2(2), p. 324.
As printed: At an archimedean point of the stated pole list whose real part is a
negative odd integer, the pole order of the correcting factor is bounded by the number
of complex places. The repaired bound is `sLocalRhoPoleOrder_le_of_re_neg_odd`.
See ERRATA F97. -/
def Printed.sLocalRhoPoleOrder_le_of_re_neg_odd : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset Places(F)) (χ : U𝔽(F))
    (hχ : ideleClassNormTwist χ 0 ∈ unramifiedOutside F S)
    (w : InfinitePlace F) (n : ℕ),
    let chart := twistₛ(F, S) (sIdeleRestriction F S ⟨ideleClassNormTwist χ 0, hχ⟩)
    let c := sLocalInfiniteRestriction w (chart 0)
    let m : ℝ := -((2 * n + 1 : ℕ) : ℝ)
    let r₂ := (Finset.univ.filter (fun v : InfinitePlace F ↦ v.IsComplex)).card
    (∀ hw : w.IsReal,
      let p := (realLocalEulerParameters w hw c).exists.choose
      p.2.val = 1 → sLocalRhoPoleOrder (chart ((m : ℂ) - p.1)) ≤ r₂) ∧
    (∀ hw : w.IsComplex,
      let p := (complexLocalEulerParameters w hw c).exists.choose
      (∃ j : ℕ, m = (p.2.natAbs : ℝ) / 2 - j) →
        sLocalRhoPoleOrder (chart ((m : ℂ) - p.1)) ≤ r₂)

/-- At a singleton finite stage, a unitary character detects the idele with
value minus one at the chosen infinite place and one everywhere else. -/
private theorem Printed.sLocalRhoPoleOrder_le_of_re_neg_odd_false_exists_character
    (F : Type u) [Field F] [NumberField F] (v : Places(F)) (w : InfinitePlace F) :
    ∃ η : PontryaginDual Jₛ(F, {v}),
      sLocalInfiniteRestriction w ((circleToComplex).comp η) (-1) ≠ 1 := by
  classical
  let S : Finset Places(F) := {v}
  let signs : (t : InfinitePlace F) → t.Completionˣ := Pi.mulSingle w (-1)
  let g : (SAdeleRing F S)ˣ :=
    (ContinuousMulEquiv.prodUnits (InfiniteAdeleRing F) ((i : S) → i.val.adicCompletion F)).symm
      (ContinuousMulEquiv.piUnits.symm signs, 1)
  -- Its finite coordinate forces a diagonal representative to be one.
  have hg : (QuotientGroup.mk g : Jₛ(F, S)) ≠ 1 := by
    intro he
    obtain ⟨u, hu⟩ := (sIdeleQuotient_mk_eq_one F S g).mp he
    let i : S := ⟨v, Finset.mem_singleton_self _⟩
    have hf := congrArg (fun a : (SAdeleRing F S)ˣ ↦ a.val.2 i) hu
    change 1 = algebraMap F (v.adicCompletion F) (u.val : F) at hf
    have hu1 : (u.val : F) = 1 := (algebraMap F (v.adicCompletion F)).injective
      (hf.symm.trans (map_one _).symm)
    have ha := congrArg (fun a : (SAdeleRing F S)ˣ ↦ a.val.1 w) hu
    change (signs w : w.Completion) = algebraMap F w.Completion (u.val : F) at ha
    have : CharZero w.Completion := charZero_of_injective_algebraMap (algebraMap F _).injective
    norm_num [signs, hu1] at ha
  let : LocallyCompactSpace (SAdeleRing F S)ˣ := (sIdeleGroup_description F S).2.2.1
  have := isClosed_sProjectedDiagonal (F := F) (S := S)
  obtain ⟨η, hη⟩ := exists_pontryaginDual_apply_ne_one hg
  exact ⟨η, fun h ↦ hη (Subtype.ext h)⟩

/-- Over a degree-one field the first pole of an odd real factor contradicts
the bound by the number of complex places. -/
private theorem Printed.sLocalRhoPoleOrder_le_of_re_neg_odd_false_of_degree_one
    (F : Type u) [Field F] [NumberField F] (hd : Module.finrank ℚ F = 1)
    (h : Printed.sLocalRhoPoleOrder_le_of_re_neg_odd.{u}) : False := by
  classical
  have hcard := InfinitePlace.nrComplexPlaces_eq_zero_of_finrank_eq_one hd
  let w : InfinitePlace F := Classical.arbitrary _
  have hw := (nrComplexPlaces_eq_zero_iff.mp hcard).isReal w
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 F)
  let v : Places(F) := ⟨m, hm.isPrime, NeZero.ne m⟩
  let S : Finset Places(F) := {v}
  obtain ⟨η, hsign⟩ :=
    Printed.sLocalRhoPoleOrder_le_of_re_neg_odd_false_exists_character F v w
  let c := (circleToComplex).comp η
  let chart := twistₛ(F, S) c
  have hzero : chart 0 = c := by
    ext1 g
    change c g * _ ^ (0 : ℂ) = c g
    simp
  obtain ⟨χ, hχ, hext, -⟩ := sLocal_character_extension η
  have hbase : sIdeleRestriction F S ⟨ideleClassNormTwist χ 0, hχ⟩ = c := hext.trans hzero
  let p := (realLocalEulerParameters w hw (sLocalInfiniteRestriction w (chart 0))).exists.choose
  have hp : p.2.val = 1 := by
    have he := (realLocalEulerParameters w hw
      (sLocalInfiniteRestriction w (chart 0))).exists.choose_spec (-1 : ℝˣ)
    have hneg : Units.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toMonoidHom
        (-1 : ℝˣ) = -1 := Units.ext (by simp)
    by_contra hne
    have hp0 : p.2.val = 0 := by
      have := p.2.isLt
      omega
    change _ = _ * _ ^ p.2.val at he
    rw [hneg, hp0, hzero] at he
    exact hsign (by simpa using he)
  let s : ℂ := -1 - p.1
  have hpole : meromorphicOrderAt (fun z ↦ sLocalRhoFactor (chart z)) s < 0 := by
    apply (sLocalRhoFactor_poles_iff η s).2
    refine Or.inl ⟨w, hw, 0, ?_⟩
    change s = -p.1 - ((2 * 0 + p.2.val : ℕ) : ℂ)
    rw [hp]
    dsimp [s]
    ring
  have bound := (h F S χ hχ w 0).1 hw
  simp only [hbase] at bound
  specialize bound hp
  have hbound : sLocalRhoPoleOrder (chart s) ≤ 0 := by
    simpa [s, p, chart, S, ← Fintype.card_subtype, hcard] using bound
  have hord := sLocalIdelicOrderBound_eq_neg_poleOrder (chart s)
  rw [Nat.le_zero.mp hbound] at hord
  rw [sLocalOrderBound_chart η s, min_eq_right hpole.le] at hord
  simp [hord] at hpole

/-- Paper: Theorem 7.1.3.2(2), p. 324.
Over ℚ the odd Dirichlet character modulo 4 has real factor Γℝ(s + 1)
and a pole at −1, while there are zero complex places. The proof obtains an
odd character by separating the sign idele with any one finite place included. -/
theorem Printed.sLocalRhoPoleOrder_le_of_re_neg_odd_false :
    ¬ Printed.sLocalRhoPoleOrder_le_of_re_neg_odd := by
  intro h
  have : CharZero (ULift ℚ) := ⟨fun a b hab ↦ by simpa using congrArg ULift.down hab⟩
  have : NumberField (ULift ℚ) := ⟨⟩
  exact Printed.sLocalRhoPoleOrder_le_of_re_neg_odd_false_of_degree_one (ULift ℚ) (by simp) h

/-- Paper: Corollary 7.1.3.3, p. 326.
As printed: There is a highest positive pole order and a highest positive order
strictly below it for the continued zeta transform of every test in the setting of
the corollary. This is the clause defining the remainder exponent.
The least-bound formulation is in `sLocalHomogeneousAdelicTheta_log_bound`.
See ERRATA F98. -/
def Printed.sLocalPolarMultiplicity_greatest_smaller : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset Places(F)),
    Fintype.card (InfinitePlace F) = 1 →
    ∀ (χ : PontryaginDual Jₛ(F, S)) (f : SchwartzBruhat (Multiplicative (SAdeleRing F S))),
      let chart := twistₛ(F, S) ((circleToComplex).comp χ)
      let orders : Set ℕ := {m | 0 < m ∧ ∃ s : ℂ, sLocalPolarMultiplicity f (chart s) = m}
      ∃ M m : ℕ, IsGreatest orders M ∧ IsGreatest (orders ∩ Iio M) m

/-- The S-local Z-function of the zero test is identically zero: the zero function is
meromorphic in normal form and agrees with the zero integral, and the continuation is unique. -/
private theorem Printed.sLocalPolarMultiplicity_greatest_smaller_false_zFunction_zero
    (F : Type u) [Field F] [NumberField F] (S : Finset Places(F)) :
    sLocalIdelicZFunction (F := F) (S := S) 0 = 0 :=
  (sLocalIdelicZetaIntegral_exists_continuation (F := F) (S := S) 0).unique
    (sLocalIdelicZetaIntegral_exists_continuation (F := F) (S := S) 0).exists.choose_spec
    ⟨fun _ ↦ analyticOnNhd_const.meromorphicNFOn, fun c _ ↦ by
      simp only [Pi.zero_apply, sLocalIdelicZetaIntegral]
      exact (integral_eq_zero_of_ae (Eventually.of_forall fun _ ↦ zero_mul _)).symm⟩

/-- The zero test has polar multiplicity zero at every quasi-character. -/
private theorem Printed.sLocalPolarMultiplicity_greatest_smaller_false_zero
    (F : Type u) [Field F] [NumberField F] (S : Finset Places(F))
    (c : QuasiCharacter Jₛ(F, S)) :
    sLocalPolarMultiplicity (0 : SchwartzBruhat (Multiplicative (SAdeleRing F S))) c = 0 := by
  rw [sLocalPolarMultiplicity_eq_zero_iff]
  refine le_top.trans_eq (meromorphicOrderAt_eq_top_iff.mpr (Eventually.of_forall fun z ↦ ?_)).symm
  rw [Printed.sLocalPolarMultiplicity_greatest_smaller_false_zFunction_zero F S]
  rfl

/-- Paper: Corollary 7.1.3.3, p. 326.
Use ℚ with only the real place, the trivial character and the zero test, for which
the set of pole orders is empty. The Gaussian `exp(-πx²)` gives a second example:
Γℝ(s) has only simple poles, so there is no positive order below one. -/
theorem Printed.sLocalPolarMultiplicity_greatest_smaller_false :
    ¬ Printed.sLocalPolarMultiplicity_greatest_smaller := by
  intro h
  have : CharZero (ULift ℚ) := ⟨fun a b hab ↦ by simpa using congrArg ULift.down hab⟩
  have : NumberField (ULift ℚ) := ⟨⟩
  have hd : Module.finrank ℚ (ULift ℚ) = 1 := by simp
  have hcard : Fintype.card (InfinitePlace (ULift ℚ)) = 1 := by
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      InfinitePlace.nrRealPlaces_eq_one_of_finrank_eq_one hd,
      InfinitePlace.nrComplexPlaces_eq_zero_of_finrank_eq_one hd]
  obtain ⟨M, m, hM, -⟩ := h (ULift ℚ) ∅ hcard 1 0
  obtain ⟨hpos, s, hs⟩ := hM.1
  rw [Printed.sLocalPolarMultiplicity_greatest_smaller_false_zero] at hs
  omega

/-- Paper: Theorem 7.1.4.2(1), equation (7.1.4.2), p. 326.
As printed: The strong annihilator of the regularized completed Hecke ideal is linearly
and topologically isomorphic to the product of the jet spaces at the completed Hecke zeros.
The direct-sum statement is `spectralAnnihilator_directSum`. See ERRATA F99. -/
def Printed.spectralAnnihilator_product : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (χ : U𝔽(F))
    (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F) (hτ : RightInverse τ (ideleNorm F))
    (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (hEq : ∀ s : halfPlane, L s = completedHeckeL χ s),
    let Λ := regularizedCompletedHeckeL χ τ hτ L hL hEq
    Nonempty ((∀ ρ : Zeros(L), ↥(Jet(L, ρ.val))) ≃L[ℂ] entireIdealAnnihilator Λ)

/-- Paper: Theorem 7.1.4.2(1), equation (7.1.4.2), p. 326.
Take the trivial rational character and the meromorphic normal form of the completed
Riemann zeta function. There are countably infinitely many distinct zeros and
each jet space is nonzero and
finite-dimensional. The annihilator consists of finite-support jets and has countable
algebraic dimension. The product has uncountable dimension, as seen by embedding
complex sequences and using the independent sequences `(a^n)ₙ` for distinct a. -/
theorem Printed.spectralAnnihilator_product_false :
    ¬ Printed.spectralAnnihilator_product := by sorry

/-- Paper: Theorem 7.1.4.2(2), equation (7.1.4.6), p. 327.
As printed: The derivative functional at a completed Hecke zero is the moment of the
inverse Mellin transform in the coordinate (7.1.4.1), with exponent shifted by the
section frequency x₀. The formula of `schwartzBergman_jet_eq_mellinInv_moment`
uses the unshifted exponent. See ERRATA F100. -/
def Printed.schwartzBergman_jet_eq_mellinInv_shifted_moment : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (χ : U𝔽(F))
    (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F) (hτ : RightInverse τ (ideleNorm F))
    (L : ℂ → ℂ) (_hL : MeromorphicNFOn L univ)
    (_hEq : ∀ s : halfPlane, L s = completedHeckeL χ s)
    (ρ : Zeros(L)) (m : ℕ), m < (meromorphicOrderAt L ρ.val).untop₀.toNat →
    ∀ f : Bergman,
      let x₀ := (existsUnique_ideleNormSection_character_phase χ τ hτ).exists.choose
      let φ : ℂ → ℂ := f.val
      let moment := fun t : ℝ ↦ (Real.log t : ℂ) ^ m * mellinInv 0 φ t
      iteratedDeriv m φ ρ.val = mellin moment (ρ.val + (x₀ : ℂ) * Complex.I)

/-- Paper: Theorem 7.1.4.2(2), equation (7.1.4.6), p. 327.
Take ℚ, the pure norm character with exponent i and x₀ = 1. Use the meromorphic
normal form of the shifted completed zeta, with a zero ρ obtained by shifting
a completed zeta zero by −i.
At m = 0 take `φ(s) = (s - ρ) exp(s²)`. The derivative functional is zero, while
the convergent shifted moment is `φ(ρ + i) = i exp((ρ + i)²) ≠ 0`. -/
theorem Printed.schwartzBergman_jet_eq_mellinInv_shifted_moment_false :
    ¬ Printed.schwartzBergman_jet_eq_mellinInv_shifted_moment := by sorry

/-- Paper: Theorem 7.1.4.2(4), p. 327.
As printed: The jet functionals are continuous on the ordinary Schwartz quotient.
The chosen section identifies the isotype with ordinary Schwartz norm profiles.
The denominator consists of the profiles of homogeneous theta functions of polar
tests. On every exponentially decaying profile the functional is the jet in the
Mellin coordinate (7.1.4.1). The repaired estimate
`schwartzBergman_normalizedJets` uses the exponentially decaying tests.
See ERRATA F101, also for the analogous topology in Theorem 7.1.4.3(3). -/
def Printed.schwartzBergman_jet_continuous_on_ordinary_schwartz : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (χ : U𝔽(F))
    (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F) (hτ : RightInverse τ (ideleNorm F))
    (L : ℂ → ℂ) (_hL : MeromorphicNFOn L univ)
    (_hEq : ∀ s : halfPlane, L s = completedHeckeL χ s)
    (ρ : Zeros(L)) (m : ℕ), m < (meromorphicOrderAt L ρ.val).untop₀.toNat →
      let x₀ := (existsUnique_ideleNormSection_character_phase χ τ hτ).exists.choose
      let expUnit := fun s : ℝ ↦ (Nonneg.unitsHomeomorphPos ℝ).symm (Real.expOrderIso s)
      let ω := χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ :
        (ideleClassNorm F).ker →ₜ* C𝔽(F))
      let H := Submodule.span ℂ {f : SchwartzBruhat ℝ≥0ˣ | ∃ a : adelePolarSubspace F,
        ∀ t, f t = homogeneousAdelicThetaLinearMap F ω a.val (QuotientGroup.mk (τ t))}
      ∃ ℓ : (SchwartzBruhat ℝ≥0ˣ ⧸ H) →L[ℂ] ℂ,
        ∀ f : SchwartzBruhat ℝ≥0ˣ, (fun u ↦ f (expUnit u)) ∈ logExponentialDecaySubmodule univ →
          ℓ (Submodule.Quotient.mk f) =
            ∫ u : ℝ, f (expUnit u) * Complex.exp ((ρ.val + (x₀ : ℂ) * Complex.I) * u) *
              (u : ℂ) ^ m

/-- Paper: Theorem 7.1.4.2(4), p. 327.
Take the trivial rational character, a completed zeta zero ρ with a = Re ρ > 0,
and m = 0. Take a smooth nonzero nonnegative bump b supported in (0,1) and the
log-profile `h(u) = b(u) exp(-i Im(ρ) u)`. The ordinary Schwartz profiles
`exp(-an) h(u - n)` tend to zero, while their ρ-moments have the same strictly
positive modulus as the ρ-moment of h. -/
theorem Printed.schwartzBergman_jet_continuous_on_ordinary_schwartz_false :
    ¬ Printed.schwartzBergman_jet_continuous_on_ordinary_schwartz := by sorry

/-- Paper: Estimate after equation (7.1.4.22), p. 330.
As printed: The norm of the normalized derivative throughout the closed critical strip
is at most 1/(2π) times the larger of the two vertical L¹ norms. The equicontinuity
statement is `schwartzBergman_normalizedJets`. See ERRATA F102. -/
def Printed.schwartzBergman_normalizedJet_le_max : Prop :=
  ∀ (f : Bergman) (s : ℂ), s.re ∈ Icc 0 1 → ∀ k : ℕ,
    let lineNorm (σ : ℝ) :=
      ∫ y : ℝ, ‖f.val ((σ : ℂ) + (y : ℂ) * Complex.I)‖
    ‖iteratedDeriv k f.val s / (k.factorial : ℂ)‖ ≤
      (2 * Real.pi)⁻¹ * max (lineNorm (-1)) (lineNorm 2)

private theorem schwartzBergman_normalizedJet_le_max_mem :
    (fun z : ℂ ↦ Complex.exp (2 / 9 * (z - 1 / 2) ^ 2)) ∈ schwartzBergmanSubmodule univ := by
  refine ⟨fun z hz ↦ absurd (mem_univ _) hz, ?_, ?_⟩
  · exact (by fun_prop : Differentiable ℂ (fun z : ℂ ↦ Complex.exp (2 / 9 * (z - 1 / 2) ^ 2)))
      |>.differentiableOn
  · intro a b _ _ N
    let M := max |a| |b|
    refine ⟨N.factorial * Real.exp (M + 9 / 8 + 2 / 9 * (2 * M ^ 2 + 1 / 2)), ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    have hstrip : z.re ∈ Icc a b := hz
    have hM : |z.re| ≤ M := abs_le_max_abs_abs hstrip.1 hstrip.2
    have hsq : z.re ^ 2 ≤ M ^ 2 := by
      simpa using pow_le_pow_left₀ (abs_nonneg _) hM 2
    have hweight : ‖z‖ ^ N ≤ N.factorial * Real.exp ‖z‖ := by
      have h := (div_le_iff₀ (show 0 < (N.factorial : ℝ) by positivity)).mp
        (Real.pow_div_factorial_le_exp ‖z‖ (norm_nonneg z) N)
      simpa [mul_comm] using h
    have hz' : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    have hre : (2 / 9 * (z - 1 / 2) ^ 2 : ℂ).re = 2 / 9 * ((z.re - 1 / 2) ^ 2 - z.im ^ 2) := by
      simp [sq, Complex.mul_re, Complex.mul_im]
    change ‖z ^ N * Complex.exp (2 / 9 * (z - 1 / 2) ^ 2)‖ ≤ _
    rw [norm_mul, norm_pow, Complex.norm_exp, hre]
    calc
      _ ≤ (N.factorial * Real.exp ‖z‖) * Real.exp (2 / 9 * ((z.re - 1 / 2) ^ 2 - z.im ^ 2)) :=
        mul_le_mul_of_nonneg_right hweight (Real.exp_pos _).le
      _ = N.factorial * Real.exp (‖z‖ + 2 / 9 * ((z.re - 1 / 2) ^ 2 - z.im ^ 2)) := by
        rw [Real.exp_add, mul_assoc]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
        have h1 : |z.im| - 2 / 9 * z.im ^ 2 ≤ 9 / 8 := by
          nlinarith [sq_nonneg (|z.im| - 9 / 4), sq_abs z.im]
        nlinarith [sq_nonneg (z.re + 1 / 2)]

private theorem schwartzBergman_normalizedJet_le_max_line (σ : ℝ) (hσ : (σ - 1 / 2) ^ 2 = 9 / 4) :
    ∫ y : ℝ, ‖Complex.exp (2 / 9 * (((σ : ℂ) + (y : ℂ) * Complex.I) - 1 / 2) ^ 2)‖ =
      Real.exp (1 / 2) * Real.sqrt (Real.pi / (2 / 9)) := by
  have hpt (y : ℝ) : ‖Complex.exp (2 / 9 * (((σ : ℂ) + (y : ℂ) * Complex.I) - 1 / 2) ^ 2)‖ =
      Real.exp (1 / 2) * Real.exp (-(2 / 9) * y ^ 2) := by
    rw [Complex.norm_exp, ← Real.exp_add]
    congr 1
    simp [sq, Complex.mul_re, Complex.mul_im]
    nlinarith [hσ]
  simp_rw [hpt]
  rw [integral_const_mul, integral_gaussian]

private theorem schwartzBergman_normalizedJet_le_max_num :
    (2 * Real.pi)⁻¹ * (Real.exp (1 / 2) * Real.sqrt (Real.pi / (2 / 9))) < 1 := by
  have hpi := Real.pi_gt_d2
  have he := Real.exp_one_lt_d9
  have hpos : 0 < Real.pi := Real.pi_pos
  rw [inv_mul_lt_iff₀ (by positivity), mul_one]
  have hx : 0 ≤ Real.exp (1 / 2) * Real.sqrt (Real.pi / (2 / 9)) := by positivity
  apply lt_of_pow_lt_pow_left₀ 2 (by positivity)
  rw [mul_pow, Real.sq_sqrt (by positivity), ← Real.exp_nat_mul]
  norm_num
  nlinarith

/-- Paper: Estimate after equation (7.1.4.22), p. 330.
Use `Φ(s) = exp(2 (s - 1/2)^2 / 9)`, s = 1/2, and k = 0. The left side is 1.
Each line norm is `3 √(π e/2)`, so the right side is `√(9 e/(8π)) < 1`. -/
theorem Printed.schwartzBergman_normalizedJet_le_max_false :
    ¬ Printed.schwartzBergman_normalizedJet_le_max := by
  intro h
  let f : schwartzBergmanSubmodule univ := ⟨_, schwartzBergman_normalizedJet_le_max_mem⟩
  have key := h f ((1 / 2 : ℝ) : ℂ) (by norm_num) 0
  have hl : ∀ σ : ℝ, (σ - 1 / 2) ^ 2 = 9 / 4 →
      ∫ y : ℝ, ‖f.val ((σ : ℂ) + (y : ℂ) * Complex.I)‖ =
        Real.exp (1 / 2) * Real.sqrt (Real.pi / (2 / 9)) :=
    schwartzBergman_normalizedJet_le_max_line
  have h1 : ‖iteratedDeriv 0 f.val ((1 / 2 : ℝ) : ℂ) / ((Nat.factorial 0 : ℕ) : ℂ)‖ = 1 := by
    simp [f]
  simp only [] at key
  rw [h1, hl (-1) (by norm_num), hl 2 (by norm_num), max_self] at key
  exact absurd key (not_le.mpr schwartzBergman_normalizedJet_le_max_num)

section Orbital

variable {F : Type u} [Field F] [NumberField F]

open Classical in
/-- Paper: Equation (7.1.4.24), p. 331.
The prime block spans the derivative evaluations over all zeros of that prime's
Euler polynomial, with the order cutoff taken from that polynomial alone. -/
def Printed.orbitalPrimeJetSpace (χ : U𝔽(F)) (S₀ : Finset Places(F)) (p : RatPrimes) :
    Submodule ℂ (StrongDual ℂ Entire) :=
  let P := reciprocalPartialHeckeEulerProduct χ overₚ(S₀, p)
  Submodule.span ℂ {ℓ | ∃ (ε : ℂ) (m : ℕ),
    m < (meromorphicOrderAt P ε).untop₀.toNat ∧ ℓ = entireJet ε m}

/-- Paper: Theorem 7.1.4.3(1), equations (7.1.4.23)–(7.1.4.25), p. 331.
As printed: The orbital strong annihilator is linearly and topologically isomorphic
to the product of the separate prime blocks and the product of the completed Hecke jets.
Each prime block uses the zeros of its own Euler polynomial. The corrected decomposition
`orbitalAnnihilator_directSum` uses the order of the full generator at each point.
See ERRATA F99 and F103. -/
def Printed.orbitalAnnihilator_prime_products : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (χ : U𝔽(F)) (S₀ : Finset Places(F))
    (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F) (hτ : RightInverse τ (ideleNorm F))
    (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (hEq : ∀ s : halfPlane, L s = completedHeckeL χ s),
    let g := orbitalHeckeGenerator χ τ hτ L hL hEq S₀
    let primes := {p : RatPrimes // ∃ v ∈ S₀, HeightOneSpectrum.under (𝓞 ℚ) v = p}
    Nonempty (((∀ p : primes, ↥(Printed.orbitalPrimeJetSpace χ S₀ p.val)) ×
      (∀ ρ : Zeros(L), ↥(Jet(L, ρ.val)))) ≃L[ℂ] entireIdealAnnihilator g)

/-- Paper: Theorem 7.1.4.3(1), equations (7.1.4.23)–(7.1.4.25), p. 331.
Take ℚ, the trivial character and S₀ consisting of the places above 2 and 3. The
annihilator of the entire generator consists of finite-support jets at countably
many zeros, while the product of the completed zeta jets has uncountable dimension.
At the origin the regularized completed zeta is nonzero, and each prime block
contributes the same value functional. Their difference vanishes under the jet
identification, and the first derivative at the resulting double zero is missing. -/
theorem Printed.orbitalAnnihilator_prime_products_false :
    ¬ Printed.orbitalAnnihilator_prime_products := by
  intro h
  apply Printed.spectralAnnihilator_product_false
  intro F _ _ χ τ hτ L hL hEq
  let P := {p : RatPrimes // ∃ v ∈ (∅ : Finset Places(F)),
    HeightOneSpectrum.under (𝓞 ℚ) v = p}
  let A := ∀ p : P, ↥(Printed.orbitalPrimeJetSpace χ ∅ p.val)
  let B := ∀ ρ : Zeros(L), ↥(Jet(L, ρ.val))
  have : IsEmpty P := ⟨fun p => by obtain ⟨v, hv, _⟩ := p.property; simp at hv⟩
  let : Unique A := { default := 0, uniq := fun a => Subsingleton.elim _ _ }
  obtain ⟨e⟩ := h F χ ∅ τ hτ L hL hEq
  rw [orbitalHeckeGenerator_empty] at e
  exact ⟨(ContinuousLinearEquiv.uniqueProd ℂ B A).symm.trans e⟩

/-- Paper: Theorem 7.1.4.3(1), equation (7.1.4.24), p. 331.
As printed: The space of all jets associated with a rational prime block is
finite-dimensional. The fixed-zero dimension is computed by `entireJetSpace_finrank`,
and `orbitalAnnihilator_directSum` uses one space per zero. See ERRATA F104. -/
def Printed.orbitalPrimeJetSpace_finite : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (χ : U𝔽(F)) (S₀ : Finset Places(F))
    (p : RatPrimes), (∃ v ∈ S₀, v.under (𝓞 ℚ) = p) →
      Module.Finite ℂ (Printed.orbitalPrimeJetSpace χ S₀ p)

private theorem orbitalPrimeJetSpace_finite_order (q : ℝ) (hq : 1 < q) (z : ℂ)
    (hz : (q : ℂ) ^ (-z) = 1) :
    0 < (meromorphicOrderAt (fun s : ℂ ↦ 1 - (q : ℂ) ^ (-s)) z).untop₀.toNat := by
  have hq0 : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have han : AnalyticAt ℂ (fun s : ℂ ↦ 1 - (q : ℂ) ^ (-s)) z :=
    Differentiable.analyticAt (fun w ↦
      (((hasDerivAt_neg w).const_cpow (Or.inl hq0)).const_sub 1).differentiableAt) z
  have hd : HasDerivAt (fun s : ℂ ↦ 1 - (q : ℂ) ^ (-s))
      (-((q : ℂ) ^ (-z) * Complex.log q * (-1))) z :=
    ((hasDerivAt_neg z).const_cpow (Or.inl hq0)).const_sub 1
  have hlog : Complex.log (q : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_log (by linarith)]
    exact Complex.ofReal_ne_zero.mpr (Real.log_pos hq).ne'
  have hne : analyticOrderAt (fun s : ℂ ↦ 1 - (q : ℂ) ^ (-s)) z ≠ ⊤ := by
    intro htop
    rw [analyticOrderAt_eq_top] at htop
    have h0 : deriv (fun s : ℂ ↦ 1 - (q : ℂ) ^ (-s)) z = 0 := by
      rw [Filter.EventuallyEq.deriv_eq (show (fun s : ℂ ↦ 1 - (q : ℂ) ^ (-s)) =ᶠ[𝓝 z]
        fun _ ↦ (0 : ℂ) from htop)]
      simp
    rw [hd.deriv, hz] at h0
    simp [hlog] at h0
  have hpos : analyticOrderAt (fun s : ℂ ↦ 1 - (q : ℂ) ^ (-s)) z ≠ 0 := by
    rw [ne_eq, han.analyticOrderAt_eq_zero, not_not]
    simp [hz]
  rw [han.meromorphicOrderAt_eq]
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hne
  rw [← hn] at hpos ⊢
  have : n ≠ 0 := by exact_mod_cast hpos
  simp
  omega

private theorem orbitalPrimeJetSpace_finite_linearIndependent (z : ℕ → ℂ) (hz : Injective z) :
    LinearIndependent ℂ (fun k ↦ entireJet (z k) 0) := by
  classical
  rw [linearIndependent_iff']
  intro s g hg i hi
  let p : Subtype (fun f : C(ℂ, ℂ) ↦ f ∈ entireContinuousMapSubalgebra) :=
    ⟨⟨fun w ↦ ∏ j ∈ s.erase i, (w - z j), by fun_prop⟩,
      (by fun_prop : Differentiable ℂ (fun w : ℂ ↦ ∏ j ∈ s.erase i, (w - z j)))⟩
  have hp := congrArg (fun ℓ : StrongDual ℂ _ ↦ ℓ p) hg
  simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
    Pi.smul_apply, entireJet_apply, iteratedDeriv_zero, smul_eq_mul] at hp
  rw [Finset.sum_eq_single i] at hp
  · have hne : (∏ j ∈ s.erase i, (z i - z j)) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro j hj
      exact sub_ne_zero.mpr fun h ↦ (Finset.ne_of_mem_erase hj) (hz h).symm
    exact (mul_eq_zero.mp hp).resolve_right hne
  · intro j hj hji
    apply mul_eq_zero_of_right
    exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hji, hj⟩) (sub_self _)
  · intro h; exact absurd hi h

open Classical in
private theorem orbitalPrimeJetSpace_finite_aux (F : Type*) [Field F] [NumberField F]
    (h : ∀ (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
      (p : HeightOneSpectrum (𝓞 ℚ)), (∃ v ∈ S₀, v.under (𝓞 ℚ) = p) →
        Module.Finite ℂ (Printed.orbitalPrimeJetSpace χ S₀ p)) : False := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 F)
  let v : HeightOneSpectrum (𝓞 F) := ⟨m, hm.isPrime, NeZero.ne m⟩
  have hone :
      ∀ g, ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) 0 g = 1 := by
    intro g
    change ((1 : Circle) : ℂ) * (_ : ℂ) ^ (0 : ℂ) = 1
    simp
  have hres : ∀ x : v.adicCompletion F, x ≠ 0 →
      (ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) 0).restrict v x =
        1 := by
    intro x hx
    rw [show x = ((Units.mk0 x hx : (v.adicCompletion F)ˣ) : v.adicCompletion F) from rfl,
      HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
    simp [hone]
  have hunr :
      (ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) 0).IsUnramifiedAt
        v := by
    rw [HeckeCharacter.isUnramifiedAt_iff]
    intro x
    exact hres _ (by simp)
  let p := v.under (𝓞 ℚ)
  have hfin := h 1 {v} p ⟨v, Finset.mem_singleton_self v, rfl⟩
  let q : ℝ := v.asIdeal.absNorm
  have hq : 1 < q := by
    dsimp only [q]
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hP : reciprocalPartialHeckeEulerProduct (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F))
      (({v} : Finset (HeightOneSpectrum (𝓞 F))).filter (fun w ↦ w.under (𝓞 ℚ) = p)) =
      fun s ↦ 1 - (q : ℂ) ^ (-s) := by
    rw [Finset.filter_singleton, ite_eq_left rfl]
    funext s
    rw [reciprocalPartialHeckeEulerProduct_singleton _ v hunr,
      hunr.localValue_eq _ Valued.v.exists_isUniformizer_of_isCyclic_of_nontrivial.choose_spec,
      hres _ (Valued.v.exists_isUniformizer_of_isCyclic_of_nontrivial.choose_spec.ne_zero)]
    simp [q]
  have hlog : (Real.log q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.log_pos hq).ne'
  let c : ℂ := 2 * Real.pi * Complex.I / Real.log q
  have hc : c ≠ 0 := div_ne_zero (by simp [Real.pi_ne_zero]) hlog
  let z : ℕ → ℂ := fun k ↦ (k : ℂ) * c
  have hz : Injective z := fun a b hab ↦ by
    exact_mod_cast mul_right_cancel₀ hc hab
  have hzq (k : ℕ) : (q : ℂ) ^ (-z k) = 1 := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (by linarith)),
      ← Complex.ofReal_log (by linarith), Complex.exp_eq_one_iff]
    refine ⟨-(k : ℤ), ?_⟩
    simp only [z, c]
    field_simp
    push_cast
    ring
  have hmem (k : ℕ) : entireJet (z k) 0 ∈
      Printed.orbitalPrimeJetSpace (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) {v} p := by
    apply Submodule.subset_span
    refine ⟨z k, 0, ?_, rfl⟩
    rw [hP]
    exact orbitalPrimeJetSpace_finite_order q hq (z k) (hzq k)
  have hli := orbitalPrimeJetSpace_finite_linearIndependent z hz
  have hli' : LinearIndependent ℂ (fun k ↦ (⟨entireJet (z k) 0, hmem k⟩ :
      Printed.orbitalPrimeJetSpace (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) {v} p)) :=
    LinearIndependent.of_comp (Submodule.subtype _) hli
  have := hli'.finite
  exact not_finite ℕ

/-- Paper: Theorem 7.1.4.3(1), equation (7.1.4.24), p. 331.
Take the trivial rational character and S₀ consisting of the place above 2.
The polynomial `1 - 2^(-s)` has a simple zero at each `2πim/log 2`. Evaluations
at these distinct points are linearly independent by interpolation with polynomials
on any finite subset. -/
theorem Printed.orbitalPrimeJetSpace_finite_false :
    ¬ Printed.orbitalPrimeJetSpace_finite := by
  intro h
  -- Lift ℚ to the universe quantified over by the printed claim.
  let : Field (ULift ℚ) := { ULift.ring, ULift.groupWithZero, Equiv.ulift.field with }
  have : CharZero (ULift ℚ) := ⟨fun a b hab ↦ by simpa using congrArg ULift.down hab⟩
  have : NumberField (ULift ℚ) :=
    { to_finiteDimensional := Module.Finite.ulift (R := ℚ) (M := ℚ) }
  exact orbitalPrimeJetSpace_finite_aux (ULift ℚ) (h (ULift ℚ))

end Orbital

end RiemannMasullo
