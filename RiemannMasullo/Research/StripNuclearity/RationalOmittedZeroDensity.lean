module

public import RiemannMasullo.Research.StripNuclearity.RationalBoundedWindow
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Log

/-! # Sublinear counts of the omitted rational zeta zeros

A count bounded by `K q^n` below height `2^(n+1)`, with `q<2`, gives a
convergent reciprocal-height sum. The constants can depend on the fixed strip
width. This supplies the arithmetic hypothesis in the bounded-window comparison.
-/

@[expose] public noncomputable section

open Function IsDedekindDomain MeasureTheory NumberField Set
open scoped BigOperators ContDiff NNReal NumberField.AdeleRing

namespace RiemannMasullo.StripNuclearity

/-- A sublinear dyadic counting bound implies reciprocal-height summability, counting
each index once. The finite-subset formulation also covers an arbitrary index type. -/
theorem summable_reciprocal_of_dyadic_card_bound {ι : Type*} (t : ι → ℝ)
    {K q : ℝ} (hK : 0 ≤ K) (hq : 0 < q) (hq₂ : q < 2)
    (hcount : ∀ (n : ℕ) (T : Finset ι),
      (∀ i ∈ T, |t i| < (2 : ℝ) ^ (n + 1)) → (T.card : ℝ) ≤ K * q ^ n) :
    Summable (fun i ↦ 1 / (1 + |t i|)) := by
  classical
  let shell (i : ι) := Nat.log 2 (⌊|t i|⌋₊ + 1)
  have hb (i : ι) : (2 : ℝ) ^ shell i ≤ 1 + |t i| ∧ |t i| < (2 : ℝ) ^ (shell i + 1) := by
    have hlo : (2 : ℝ) ^ shell i ≤ (⌊|t i|⌋₊ : ℝ) + 1 := by
      exact_mod_cast Nat.pow_log_le_self 2 (Nat.succ_ne_zero ⌊|t i|⌋₊)
    have hhi : (⌊|t i|⌋₊ : ℝ) + 1 < (2 : ℝ) ^ (shell i + 1) := by
      exact_mod_cast Nat.lt_pow_succ_log_self Nat.one_lt_two (⌊|t i|⌋₊ + 1)
    exact ⟨hlo.trans (by linarith [Nat.floor_le (abs_nonneg (t i))]), (Nat.lt_floor_add_one _).trans hhi⟩
  let B (n : ℕ) := K * (q / 2) ^ n
  have hB : Summable B := (summable_geometric_of_lt_one (show 0 ≤ q/2 by positivity)
    (show q/2 < 1 by linarith)).mul_left K
  apply summable_of_sum_le (c := ∑' n, B n) (fun i ↦ by positivity)
  intro S
  have hblock (n : ℕ) (T : Finset ι) (hT : ∀ i ∈ T, shell i = n) :
      ∑ i ∈ T, 1 / (1 + |t i|) ≤ B n := by
    calc
      _ ≤ ∑ _i ∈ T, 1 / (2 : ℝ) ^ n := by
        refine Finset.sum_le_sum fun i hi ↦ ?_
        exact one_div_le_one_div_of_le (by positivity) (hT i hi ▸ (hb i).1)
      _ = (T.card : ℝ) / 2 ^ n := by simp [div_eq_mul_inv]
      _ ≤ (K * q ^ n) / 2 ^ n := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact hcount n T fun i hi ↦ hT i hi ▸ (hb i).2
      _ = B n := by simp only [B, div_pow, mul_div_assoc]
  calc
    _ = ∑ n ∈ S.image shell, ∑ i ∈ S with shell i = n, 1 / (1 + |t i|) :=
      (Finset.sum_fiberwise_of_maps_to (fun _ hi ↦ Finset.mem_image_of_mem shell hi) _).symm
    _ ≤ ∑ n ∈ S.image shell, B n :=
      Finset.sum_le_sum fun n _ ↦ hblock n _ fun _ hi ↦ (Finset.mem_filter.mp hi).2
    _ ≤ ∑' n, B n := hB.sum_le_tsum _ fun n _ ↦ by dsimp [B]; positivity

open RiemannMasullo.External.Grh

/-- At width `α` and Sobolev order `s`, the number of distinct ordinary zeros
with positive omitted multiplicity and ordinate of magnitude below `2^(n+1)`
is bounded by `K q^n` for some `q<2`. -/
def RationalOmittedZeroDyadicBound (α s : ℝ) : Prop :=
  ∃ K q : ℝ, 0 ≤ K ∧ 0 < q ∧ q < 2 ∧ ∀ (n : ℕ) (T : Finset (rationalWindowOmittedZeros α s)),
    (∀ z ∈ T, |z.val.val.im| < (2 : ℝ) ^ (n + 1)) → (T.card : ℝ) ≤ K * q ^ n

/-- A sublinear bound at one width implies the reciprocal summability for precisely
the distinct ordinary zeros with missing multiplicity at that width. -/
theorem RationalOmittedZeroDyadicBound.summable_reciprocal {α s : ℝ}
    (h : RationalOmittedZeroDyadicBound α s) :
    Summable (fun z : rationalWindowOmittedZeros α s ↦ 1 / (1 + |z.val.val.im|)) := by
  obtain ⟨K, q, hK, hq, hq₂, hcount⟩ := h
  exact summable_reciprocal_of_dyadic_card_bound _ hK hq hq₂ hcount

/-- Every omitted zero is separated from the critical line by at least the strip
half-width. This includes the case of partial omission at the boundary. -/
theorem rationalWindowOmittedZeros_le_abs_re_sub_half {α s : ℝ}
    (z : rationalWindowOmittedZeros α s) : α ≤ |z.val.val.re - 1/2| := by
  by_contra! h
  have hz := z.property
  change 0 < zetaZeroOrder z.val - spectralStripMultiplicity α s _ _ at hz
  simp only [spectralStripMultiplicity, ite_eq_left (abs_lt.mp h), Nat.sub_self, lt_self_iff_false] at hz

/-- A density estimate on all ordinary zeros at distance at least `α` from the
critical line also applies to the omitted ones. A factor polynomial in the dyadic
index can be absorbed into a larger geometric base still strictly below two. -/
theorem RationalOmittedZeroDyadicBound.of_offLine_polynomial_count {α s K q : ℝ}
    (p : ℕ) (hK : 0 ≤ K) (hq : 0 < q) (hq₂ : q < 2)
    (hcount : ∀ (n : ℕ) (T : Finset criticalStripZetaZeros),
      (∀ z ∈ T, α ≤ |z.val.re - 1/2| ∧ |z.val.im| < (2 : ℝ) ^ (n + 1)) →
      (T.card : ℝ) ≤ K * ((n : ℝ) + 1) ^ p * q ^ n) :
    RationalOmittedZeroDyadicBound α s := by
  let q' := (q + 2) / 2
  let r := q' / q
  have hq' : q < q' := by dsimp [q']; linarith
  have hr : 1 < r := (one_lt_div hq).mpr hq'
  have hrq : r * q = q' := div_mul_cancel₀ _ hq.ne'
  obtain ⟨C, hC⟩ := (tendsto_pow_const_div_const_pow_of_one_lt p hr).bddAbove_range
  have hpoly (n : ℕ) : ((n : ℝ) + 1) ^ p ≤ C * r ^ (n + 1) := by
    apply (div_le_iff₀ (pow_pos (zero_lt_one.trans hr) _)).mp
    simpa only [Nat.cast_add, Nat.cast_one] using hC (mem_range_self (n + 1))
  have hC₀ : 0 ≤ C := by
    have hb := hC (mem_range_self 1)
    exact (by positivity : 0 ≤ ((1 : ℕ) : ℝ) ^ p / r ^ (1 : ℕ)).trans hb
  refine ⟨K * C * r, q', mul_nonneg (mul_nonneg hK hC₀) (zero_lt_one.trans hr).le,
    hq.trans hq', (by dsimp [q']; linarith), fun n T ht ↦ ?_⟩
  let e : rationalWindowOmittedZeros α s ↪ criticalStripZetaZeros := Embedding.subtype _
  have hb := hcount n (T.map e) (by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hz
    exact ⟨rationalWindowOmittedZeros_le_abs_re_sub_half w, ht w hw⟩)
  rw [Finset.card_map] at hb
  calc
    _ ≤ K * ((n : ℝ) + 1) ^ p * q ^ n := hb
    _ ≤ K * (C * r ^ (n + 1)) * q ^ n := by gcongr; exact hpoly n
    _ = K * C * r * q' ^ n := by rw [← hrq, mul_pow, pow_succ]; ring

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

set_option quotPrecheck false

local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "μℚ" => ideleClassTamagawaMeasure ℚ
local notation "allWidths(" ha "," hab "," hb "," hs "," hcount "," U "," hU "," hm ")" =>
  rational_allWidths_primeFree_boundedLog_geometric_real_comparison_iff_riemannHypothesis
    ha hab hb hs (fun α hα ↦ ((hcount) α hα).summable_reciprocal) U hU hm

/-- Paper: §12.3, p. 514 and p. 520. Assuming a sublinear dyadic count for the
omitted ordinary zeta zeros at each positive strip width, agreement of the actual
rational geometric diagonals with the real gamma integral minus both Mellin poles
on all smooth tests in one fixed prime-free interval and at all positive widths is
equivalent to the ordinary Riemann hypothesis. The dyadic constants may depend on
the width. -/
theorem rational_allWidths_primeFree_real_comparison_iff_riemannHypothesis_of_dyadicCount
    {a b s : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < Real.log 2) (hs : 3 ≤ s)
    (hcount : ∀ α : ℝ, 0 < α → RationalOmittedZeroDyadicBound α s)
    (U : ℕ → Set Cℚ) (hU : IsDPrimeSequence μℚ U) (hm : ∀ k, MeasurableSet (U k)) :
    type_of% allWidths(ha,hab,hb,hs,hcount,U,hU,hm) := allWidths(ha,hab,hb,hs,hcount,U,hU,hm)

end RiemannMasullo.StripNuclearity
