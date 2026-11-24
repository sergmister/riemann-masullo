module

public import RiemannMasullo.Research.StripNuclearity.RationalFiniteShells

/-! # The rational prime-two contribution and a change of the finite set of places

For a radial bump whose only possible prime power is 2, adding the place above 2
transfers exactly its normalized local value from the outside sum to the inside sum.
The corrected local sum can also be compared with the actual geometric diagonal at
every half-width at least one half. This gives an independent test of the shell
calculation in §11.3 and the large-set choice on p. 520.
-/

@[expose] public noncomputable section
set_option quotPrecheck false
open Classical Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped ContDiff NNReal NumberField.AdeleRing Topology
namespace RiemannMasullo.StripNuclearity

section
variable {F : Type*} [Field F] [NumberField F]
local notation "Pl" => HeightOneSpectrum (𝓞 F)
local notation "K(" v ")" => ((v : Pl).adicCompletion F)
local instance primeTwoLocalCompact (v : Pl) : LocallyCompactSpace K(v)ˣ :=
  letI : ProperSpace K(v) := properSpace_adicCompletion v
  inferInstance
local instance primeTwoMeasurable (v : Pl) : MeasurableSpace K(v)ˣ := borel _
local instance primeTwoBorel (v : Pl) : BorelSpace K(v)ˣ := ⟨rfl⟩
end
attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 primeTwoLocalCompact primeTwoMeasurable primeTwoBorel

local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "N(" x ")" => (((ideleClassNorm ℚ) (x : Cℚ)).val : ℝ)
local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation "U∞" => ((w : InfinitePlace ℚ) → BruhatCompactSupport w.Completionˣ)
local notation "U𝔭" => ((v : V) → BruhatCompactSupport (v.adicCompletion ℚ)ˣ)
local notation "infClass(" w ")" => IdeleClassGroup.ofCompletion (𝓞 ℚ) ℚ w
local notation "finClass(" v ")" => IdeleClassGroup.ofAdicCompletion (𝓞 ℚ) ℚ v
local notation "finTerm(" v ", " B ")" =>
  ((Real.log ((v : V).asIdeal.absNorm : ℝ) / ((finiteLocalMultiplicativeTamagawaMeasure ℚ v)
    ((HeightOneSpectrum.adicCompletionIntegers ℚ v).units : Set _)).toReal : ℝ) : ℂ) *
    finiteConnesWeilPrincipalValue v 1 B
local notation "radial(" φ ", " g ")" =>
  (∀ x : Cℚ, (φ : BruhatCompactSupport Cℚ).val x = rationalCenteredLogProfile g (Real.log N(x)))
local notation "archRep(" A ", " φ ")" =>
  (∀ (w : InfinitePlace ℚ) (u : w.Completionˣ), ((A : U∞) w).val u = (φ : BruhatCompactSupport Cℚ).val (infClass(w) u))
local notation "finRep(" B ", " φ ")" =>
  (∀ (v : V) (u : (v.adicCompletion ℚ)ˣ), ((B : U𝔭) v).val u = (φ : BruhatCompactSupport Cℚ).val (finClass(v) u))
local notation "twoPlace" => (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨2, Nat.prime_two⟩


/-- Paper: Theorem 11.3.2.1, p. 495. For a radial test supported strictly between
norms one and three, the normalized local principal value at two is its actual
physical value at norm two times log(2)/√2.
Deviation: The printed unshifted point evaluation has coefficient log(2). -/
theorem rational_prime_two_principalValue_physical (g : ℝ → ℂ) {a b : ℝ} (ha : 0 < a)
    (hb : b < Real.log 3) (hs : tsupport g ⊆ Icc a b) (φ : BruhatCompactSupport Cℚ)
    (hφ : radial(φ, g)) (B : U𝔭) (hB : finRep(B, φ)) (y : Cℚ) (hy : N(y) = 2) :
    finTerm(twoPlace, B twoPlace) = ((Real.log 2 : ℂ) / (Real.sqrt 2 : ℂ)) * φ.val y := by
  have hx : φ.val y = (Real.sqrt 2 : ℂ) * g (Real.log 2) := by
    rw [hφ, hy, rationalCenteredLogProfile]
    congr 1
    rw [show ((Real.log (2 : ℝ) : ℂ) / 2) = ((Real.log 2 / 2 : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_exp, Real.exp_half, Real.exp_log (by norm_num)]
  rw [(rational_finite_principalValues_prime_two g ha hb hs φ hφ B hB).1, hx]
  have h : (Real.sqrt 2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (by norm_num)).ne'
  field_simp

/-- Paper: Theorem 12.5.1.1, p. 520. With a fixed centered bump the raw tail is eventually zero, since precisely the
place above two can contribute. Nothing here depends on the width of a spectral strip. -/
theorem rational_prime_two_tail_by_places (g : ℝ → ℂ) {a b : ℝ} (ha : 0 < a)
    (hb : b < Real.log 3) (hs : tsupport g ⊆ Icc a b) (φ : BruhatCompactSupport Cℚ)
    (hφ : radial(φ, g)) (B : U𝔭) (hB : finRep(B, φ)) (S : Finset V) :
    (∑' v, if v ∈ S then 0 else finTerm(v, B v)) =
      if twoPlace ∈ S then 0 else (Real.log 2 : ℂ) * g (Real.log 2) := by
  obtain ⟨h₂, hout⟩ := rational_finite_principalValues_prime_two g ha hb hs φ hφ B hB
  calc (∑' v, if v ∈ S then 0 else finTerm(v, B v)) =
      (if twoPlace ∈ S then 0 else finTerm(twoPlace, B twoPlace)) := by
        apply tsum_eq_single twoPlace
        intro v hv
        split_ifs with h
        · rfl
        · exact hout v hv
    _ = _ := by rw [h₂]

/-- Paper: Theorem 12.5.1.1, p. 520. For a rational radial test supported strictly
between norms one and three, with nonzero value at norm two, the printed support
condition on the set S holds exactly when S contains the place above two. -/
theorem rational_prime_two_support_condition_iff {g : ℝ → ℂ} {a b : ℝ} (ha : 0 < a)
    (hb : b < Real.log 3) (h₂ : g (Real.log 2) ≠ 0) (hs : tsupport g ⊆ Icc a b)
    (φ : BruhatCompactSupport Cℚ) (hφ : radial(φ, g)) (S : Finset V) :
    (∃ T : ℝ, 1 < T ∧ (∀ x ∈ tsupport φ.val, N(x) ∈ Ioo T⁻¹ T) ∧
      ∀ v : V, v ∉ S → T < (v.asIdeal.absNorm : ℝ)) ↔ twoPlace ∈ S := by
  let e : V ≃ Nat.Primes := Rat.HeightOneSpectrum.primesEquiv
  have hq (v : V) : v.asIdeal.absNorm = (e v).val := NumberFieldKB.Chebotarev.RatIdele.absNorm_asIdeal v
  have hq₂ : (twoPlace : V).asIdeal.absNorm = 2 := (hq _).trans
    (congrArg Subtype.val (e.apply_symm_apply ⟨2, Nat.prime_two⟩))
  have hN (x : Cℚ) : 0 < N(x) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (ideleClassNorm ℚ x).ne_zero)
  constructor
  · rintro ⟨T, _, hT, hqT⟩
    by_contra hn
    let q : ℝ≥0ˣ := Units.mk0 (2 : ℝ≥0) (by norm_num)
    let y : Cℚ := QuotientGroup.mk' _ (canonicalIdeleNormSection ℚ q)
    have hy : ideleClassNorm ℚ y = q := canonicalIdeleNormSection_rightInverse ℚ q
    have hy' : N(y) = 2 := by rw [hy]; rfl
    have hval : φ.val y ≠ 0 := by
      rw [hφ, hy', rationalCenteredLogProfile]
      exact mul_ne_zero (Complex.exp_ne_zero _) h₂
    have ht := (hT y (subset_tsupport _ hval)).2
    have hqT' := hqT twoPlace hn
    rw [hy'] at ht
    rw [hq₂] at hqT'
    norm_cast at hqT'
    linarith
  · intro hS
    have hlog : Continuous (fun x : Cℚ ↦ Real.log N(x)) :=
      (NNReal.continuous_coe.comp (Units.continuous_val.comp
        (isProperMap_ideleClassNorm ℚ).continuous)).log (fun x ↦ (hN x).ne')
    have hsub : tsupport φ.val ⊆ (fun x : Cℚ ↦ Real.log N(x)) ⁻¹' Icc a b := by
      refine closure_minimal (fun x hx ↦ ?_) (isClosed_Icc.preimage hlog)
      apply hs (subset_tsupport _ ?_)
      intro hz
      exact hx (by rw [hφ, rationalCenteredLogProfile, hz, mul_zero])
    let T : ℝ := (Real.exp b + 3)/2
    have hab : a ≤ b := (hs (subset_tsupport _ h₂)).1.trans (hs (subset_tsupport _ h₂)).2
    have h3 : Real.exp b < 3 := (Real.lt_log_iff_exp_lt (by norm_num)).mp hb
    have h1 : 1 < Real.exp b := Real.one_lt_exp_iff.mpr (ha.trans_le hab)
    have hbT : Real.exp b < T := by dsimp [T]; linarith
    have hT3 : T < 3 := by dsimp [T]; linarith
    refine ⟨T, h1.trans hbT, ?_, ?_⟩
    · intro x hx
      have hbounds := hsub hx
      change Real.log N(x) ∈ Icc a b at hbounds
      have hn : 1 < N(x) := Real.log_pos_iff (hN x).le |>.mp (ha.trans_le hbounds.1)
      exact ⟨(inv_lt_one_of_one_lt₀ (h1.trans hbT)).trans hn,
        (Real.le_exp_of_log_le hbounds.2).trans_lt hbT⟩
    · intro v hv
      have hne : v ≠ twoPlace := fun h ↦ hv (h ▸ hS)
      have hn : (e v).val ≠ 2 := fun h ↦ hne (e.symm_apply_eq.mpr (Subtype.ext h.symm)).symm
      have hp : 3 ≤ (e v).val := by have := (e v).property.two_le; omega
      apply hT3.trans_le
      rw [hq]
      exact_mod_cast hp

local notation "μℚ" => ideleClassTamagawaMeasure ℚ

/-- If a place sum is supported at one place, a finite truncation omits exactly
that summand when the place is outside the truncating set. -/
theorem one_place_diagonal_difference {ι : Type*} [DecidableEq ι]
    (p : ι) (c : ι → ℂ) {d v a b₁ b₂ u : ℂ} (h : d = v * (a + ∑' i, c i) - b₁ - b₂)
    (hp : c p = u) (hzero : ∀ i ≠ p, c i = 0) (S : Finset ι) :
    d - (v * (a + ∑ i ∈ S, c i) - b₁ - b₂) = if p ∈ S then 0 else v * u := by
  rw [h, tsum_eq_single p hzero, hp]
  by_cases hS : p ∈ S
  · rw [ite_eq_left hS, Finset.sum_eq_single_of_mem p hS (fun i _ hi ↦ hzero i hi), hp, sub_self]
  · rw [ite_eq_right hS, Finset.sum_eq_zero (fun i hi ↦ hzero i (fun e ↦ hS (e ▸ hi)))]
    ring

local notation "calibration(" g ", " hg ", " hc ", " ha ", " hp ", " φ ", " hφ ", " A ", " B ", " hA ", " hB ", " hw ", " hs ", " U ", " hU ", " hm ")" =>
  integral_rational_positive_log_diagonal_eq_principalValues_sub_poles
    g hg hc ha hp φ hφ A B hA hB hw hs U hU hm
local notation "primeTwoData(" g ", " ha ", " hb ", " hp ", " φ ", " hφ ", " B ", " hB ")" =>
  rational_finite_principalValues_prime_two g ha hb hp φ hφ B hB
local notation "jump(" g ", " hg ", " hc ", " ha ", " hb ", " hp ", " φ ", " hφ ", " A ", " B ", " hA ", " hB ", " hw ", " hs ", " U ", " hU ", " hm ", " S ")" =>
  one_place_diagonal_difference twoPlace (fun v : V ↦ finTerm(v, (B : U𝔭) v))
    (calibration(g, hg, hc, ha, hp, φ, hφ, A, B, hA, hB, hw, hs, U, hU, hm))
    (primeTwoData(g, ha, hb, hp, φ, hφ, B, hB)).1 (primeTwoData(g, ha, hb, hp, φ, hφ, B, hB)).2 S

/-- Paper: Theorem 12.5.1.1, p. 520. For rational radial tests with norms
strictly between one and three, the wide diagonal minus the local values in S
with their polar correction is the Tamagawa-scaled value at the prime two if
two is omitted, and zero if two is included.
Deviation: This evaluates the place distributions and the actual projected
diagonal directly. An identification with the S-local cutoff operator would
require a separate comparison. -/
theorem rational_wide_diagonal_sub_places_prime_two (g : ℝ → ℂ) (hg : ContDiff ℝ (∞) g)
    (hc : HasCompactSupport g) {a b : ℝ} (ha : 0 < a) (hb : b < Real.log 3)
    (hsupp : tsupport g ⊆ Icc a b) (φ : BruhatCompactSupport Cℚ) (hφ : radial(φ, g))
    (A : U∞) (B : U𝔭) (hA : archRep(A, φ)) (hB : finRep(B, φ))
    {α s : ℝ} (hw : 1/2 ≤ α) (hs : 3 ≤ s) (U : ℕ → Set Cℚ)
    (hU : IsDPrimeSequence μℚ U) (hm : ∀ n, MeasurableSet (U n)) (S : Finset V) :
    type_of% jump(g, hg, hc, ha, hb, hsupp, φ, hφ, A, B, hA, hB, hw, hs, U, hU, hm, S) :=
  jump(g, hg, hc, ha, hb, hsupp, φ, hφ, A, B, hA, hB, hw, hs, U, hU, hm, S)

/-- Record the full and finite truncation of the same normalized one-place sum. -/
theorem normalized_one_place_calibration {ι : Type*} [DecidableEq ι]
    (p : ι) (c : ι → ℂ) {d v a b₁ b₂ m t : ℂ} (h : d = v * (a + ∑' i, c i) - b₁ - b₂)
    (hp : c p = m * t) (hzero : ∀ i ≠ p, c i = 0) (ht : t = 1) :
    d - (v * (a + ∑' i, c i) - b₁ - b₂) = 0 ∧
      ∀ S : Finset ι, d - (v * (a + ∑ i ∈ S, c i) - b₁ - b₂) = if p ∈ S then 0 else v * m :=
  ⟨sub_eq_zero.mpr h, one_place_diagonal_difference p c h (by simpa only [ht, mul_one] using hp) hzero⟩

local notation "pulse(" g ", " hg ", " hc ", " ha ", " hb ", " hp ", " h₂ ", " φ ", " hφ ", " A ", " B ", " hA ", " hB ", " hw ", " hs ", " U ", " hU ", " hm ")" =>
  normalized_one_place_calibration twoPlace (fun v : V ↦ finTerm(v, (B : U𝔭) v))
    (calibration(g, hg, hc, ha, hp, φ, hφ, A, B, hA, hB, hw, hs, U, hU, hm))
    (primeTwoData(g, ha, hb, hp, φ, hφ, B, hB)).1 (primeTwoData(g, ha, hb, hp, φ, hφ, B, hB)).2 h₂

/-- Paper: pp. 495 and 520. Fix one rational test with normalized local value
log(2). Its full local and polar expression agrees with its geometric diagonal
at every wide window. Omitting two has residual volume times log(2), while
including it gives zero, for that same test, width and smoothing sequence.
Deviation: The finite set controls the arithmetic truncation of the local
expression. The normalized geometric shell lift on p. 495 is a separate input. -/
theorem exists_rational_prime_two_pulse_wide_diagonal_jump {a b : ℝ}
    (ha : 0 < a) (hl : a < Real.log 2) (hr : Real.log 2 < b) (hb : b < Real.log 3) :
    ∃ (g : ℝ → ℂ) (φ : BruhatCompactSupport Cℚ) (A : U∞) (B : U𝔭)
      (hg : ContDiff ℝ (∞) g) (hc : HasCompactSupport g) (hp : tsupport g ⊆ Icc a b)
      (h₂ : g (Real.log 2) = 1) (hφ : radial(φ, g)) (hA : archRep(A, φ)) (hB : finRep(B, φ)),
      ∀ {α s : ℝ} (hw : 1/2 ≤ α) (hs : 3 ≤ s) (U : ℕ → Set Cℚ)
        (hU : IsDPrimeSequence μℚ U) (hm : ∀ n, MeasurableSet (U n)),
        type_of% pulse(g, hg, hc, ha, hb, hp, h₂, φ, hφ, A, B, hA, hB, hw, hs, U, hU, hm) := by
  obtain ⟨g, φ, A, B, hg, hc, hp, h₂, hφ, hA, hB, _, _⟩ :=
    exists_rational_pulse_with_prime_two_principalValue ha hl hr hb
  exact ⟨g, φ, A, B, hg, hc, hp, h₂, hφ, hA, hB, fun hw hs U hU hm ↦
    pulse(g, hg, hc, ha, hb, hp, h₂, φ, hφ, A, B, hA, hB, hw, hs, U, hU, hm)⟩

end RiemannMasullo.StripNuclearity
