module

public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Simultaneous realization of coefficient data (a Borel–Mittag-Leffler lift)

Let `E` be a complete locally convex space with a countable basis at zero and
`L k i : E →L[ℂ] ℂ` a sequence of levels of continuous functionals. Suppose that the data at
each level can be prescribed on the common kernel of the lower levels and, from some level on
that depends only on the seminorm, by arbitrarily small elements for each continuous seminorm.
Then every array of data is realized by one element of `E`: choose the corrections inductively,
each one small for a seminorm that grows with the level, and sum them. Each functional sees
only finitely many nonzero terms of the series.
-/

public section

open Filter Topology

namespace RiemannMasullo

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
  [CompleteSpace E] {ι : ℕ → Type*}

/-- The lift for a monotone sequence of seminorms whose balls control the neighbourhoods
of zero. -/
private theorem surjective_coeff_of_eventually_small_aux (L : (k : ℕ) → ι k → E →L[ℂ] ℂ)
    (q : ℕ → Seminorm ℂ E) (hqm : Monotone q)
    (hq : ∀ U ∈ 𝓝 (0 : E), ∃ n, ∃ ε : ℝ, 0 < ε ∧ ∀ x, q n x < ε → x ∈ U)
    (h1 : ∀ k (c : ι k → ℂ), ∃ x : E, (∀ j < k, ∀ i, L j i x = 0) ∧ ∀ i, L k i x = c i)
    (h2 : ∀ n, ∃ K, ∀ k ≥ K, ∀ (c : ι k → ℂ) (ε : ℝ), 0 < ε →
      ∃ x : E, (∀ j < k, ∀ i, L j i x = 0) ∧ (∀ i, L k i x = c i) ∧ q n x < ε) :
    Function.Surjective (fun x : E ↦ fun k i ↦ L k i x) := by
  intro c
  choose K hK using h2
  -- A monotone majorant of the thresholds, and the seminorm index usable at level `k`.
  let K' : ℕ → ℕ := fun n ↦ (Finset.range (n + 1)).sup K
  have hKK' (n : ℕ) : K n ≤ K' n := Finset.le_sup (Finset.mem_range.2 (Nat.lt_succ_self n))
  have hK'm : Monotone K' := fun m n hmn ↦
    Finset.sup_mono (Finset.range_subset_range.2 (Nat.succ_le_succ hmn))
  let r : ℕ → ℕ := fun k ↦ Nat.findGreatest (fun n ↦ K' n ≤ k) k
  have hr (k : ℕ) (hk : K' 0 ≤ k) : K' (r k) ≤ k :=
    Nat.findGreatest_spec (P := fun n ↦ K' n ≤ k) (Nat.zero_le k) hk
  have hr' (n k : ℕ) (hn : n ≤ k) (hk : K' n ≤ k) : n ≤ r k :=
    Nat.le_findGreatest (P := fun n ↦ K' n ≤ k) hn hk
  have hsel (k : ℕ) (d : ι k → ℂ) : ∃ x : E, (∀ j < k, ∀ i, L j i x = 0) ∧
      (∀ i, L k i x = d i) ∧ (K' 0 ≤ k → q (r k) x < (1 / 2 : ℝ) ^ k) := by
    by_cases hk : K' 0 ≤ k
    · obtain ⟨x, hx0, hx1, hx2⟩ :=
        hK (r k) k ((hKK' _).trans (hr k hk)) d ((1 / 2 : ℝ) ^ k) (by positivity)
      exact ⟨x, hx0, hx1, fun _ ↦ hx2⟩
    · obtain ⟨x, hx0, hx1⟩ := h1 k d
      exact ⟨x, hx0, hx1, fun h ↦ absurd h hk⟩
  choose y hy0 hy1 hy2 using hsel
  -- Partial sums, each correcting the data at the next level.
  let s : ℕ → E := fun k ↦
    Nat.rec (motive := fun _ ↦ E) 0 (fun k sk ↦ sk + y k (fun i ↦ c k i - L k i sk)) k
  let x : ℕ → E := fun k ↦ y k (fun i ↦ c k i - L k i (s k))
  have hs_succ (k : ℕ) : s (k + 1) = s k + x k := rfl
  have hs_sum (k : ℕ) : s k = ∑ m ∈ Finset.range k, x m := by
    induction k with
    | zero => exact (Finset.sum_range_zero _).symm
    | succ k ih => rw [hs_succ, ih, Finset.sum_range_succ]
  have hs_coeff (k : ℕ) : ∀ j < k, ∀ i, L j i (s k) = c j i := by
    induction k with
    | zero => exact fun j hj ↦ absurd hj (Nat.not_lt_zero j)
    | succ k ih =>
      intro j hj i
      rw [hs_succ, map_add]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [ih j hj i, hy0 k _ j hj i, add_zero]
      · rw [hy1]
        exact add_sub_cancel _ _
  -- The corrections are summable.
  have hsum : Summable x := by
    refine summable_iff_vanishing.mpr fun U hU ↦ ?_
    obtain ⟨n, ε, hε, hn⟩ := hq U hU
    obtain ⟨t0, ht0⟩ := summable_geometric_two.vanishing (Iio_mem_nhds hε)
    refine ⟨t0 ∪ Finset.range (max n (K' n)), fun t ht ↦ hn _ ?_⟩
    have hb (b : ℕ) (hb : b ∈ t) : q n (x b) ≤ (1 / 2 : ℝ) ^ b := by
      have hb' : max n (K' n) ≤ b := by
        by_contra h
        exact Finset.disjoint_left.mp ht hb
          (Finset.mem_union_right _ (Finset.mem_range.2 (Nat.lt_of_not_le h)))
      have h0 : K' 0 ≤ b := (hK'm (Nat.zero_le n)).trans (le_of_max_le_right hb')
      have hnr : n ≤ r b := hr' n b (le_of_max_le_left hb') (le_of_max_le_right hb')
      exact (hqm hnr (x b)).trans (hy2 b _ h0).le
    calc q n (∑ b ∈ t, x b) ≤ ∑ b ∈ t, q n (x b) := Finset.le_sum_of_subadditive (q n) (map_zero _).le (map_add_le_add _) _ _
      _ ≤ ∑ b ∈ t, (1 / 2 : ℝ) ^ b := Finset.sum_le_sum hb
      _ < ε := ht0 t (Finset.disjoint_of_subset_right Finset.subset_union_left ht)
  obtain ⟨a, ha⟩ := hsum
  refine ⟨a, funext fun j ↦ funext fun i ↦ ?_⟩
  have hs : Tendsto s atTop (𝓝 a) := ha.tendsto_sum_nat.congr fun k ↦ (hs_sum k).symm
  have hlim : Tendsto (fun k ↦ L j i (s k)) atTop (𝓝 (L j i a)) :=
    ((L j i).continuous.tendsto a).comp hs
  have hconst : Tendsto (fun k ↦ L j i (s k)) atTop (𝓝 (c j i)) :=
    tendsto_const_nhds.congr' (eventually_atTop.2 ⟨j + 1, fun k hk ↦
      (hs_coeff k j (Nat.lt_of_succ_le hk) i).symm⟩)
  exact tendsto_nhds_unique hlim hconst

/-- **Borel–Mittag-Leffler lift.** In a complete locally convex space with a countable basis
at zero, consider levels `L k i` of continuous functionals. Suppose that the data at each level
can be prescribed on the common kernel of the lower levels, and that for every continuous
seminorm `q` there is a level from which on this can be done with elements of arbitrarily small
`q`-seminorm. Then every array of data is the array of values of one element. -/
theorem surjective_coeff_of_eventually_small [FirstCountableTopology E] [PolynormableSpace ℂ E]
    (L : (k : ℕ) → ι k → E →L[ℂ] ℂ)
    (h1 : ∀ k (c : ι k → ℂ), ∃ x : E, (∀ j < k, ∀ i, L j i x = 0) ∧ ∀ i, L k i x = c i)
    (h2 : ∀ q : Seminorm ℂ E, Continuous q → ∃ K, ∀ k ≥ K, ∀ (c : ι k → ℂ) (ε : ℝ), 0 < ε →
      ∃ x : E, (∀ j < k, ∀ i, L j i x = 0) ∧ (∀ i, L k i x = c i) ∧ q x < ε) :
    Function.Surjective (fun x : E ↦ fun k i ↦ L k i x) := by
  obtain ⟨q, hqc, hq⟩ := (PolynormableSpace.hasBasis_zero_ball ℂ E).exists_antitone_subbasis
  let Q : ℕ → Seminorm ℂ E := fun n ↦ (Finset.range (n + 1)).sup q
  have hQm : Monotone Q := fun m n hmn ↦
    Finset.sup_mono (Finset.range_subset_range.2 (Nat.succ_le_succ hmn))
  refine surjective_coeff_of_eventually_small_aux L Q hQm (fun U hU ↦ ?_) h1
    fun n ↦ h2 (Q n) (Seminorm.continuous_finsetSup fun m _ ↦ hqc m)
  obtain ⟨n, -, hn⟩ := hq.toHasBasis.mem_iff.mp hU
  refine ⟨n, 1, one_pos, fun x hx ↦ hn ?_⟩
  have hle : q n ≤ Q n := Finset.le_sup (Finset.mem_range.2 (Nat.lt_succ_self n))
  exact (Seminorm.mem_ball_zero _).mpr ((hle x).trans_lt hx)

/-- **Borel–Mittag-Leffler lift**, for a monotone countable family of seminorms inducing the
topology: the smallness in the second hypothesis is asked for each seminorm of the family. -/
theorem surjective_coeff_of_withSeminorms {p : SeminormFamily ℂ E ℕ} (hp : WithSeminorms p)
    (hpm : Monotone p) (L : (k : ℕ) → ι k → E →L[ℂ] ℂ)
    (h1 : ∀ k (c : ι k → ℂ), ∃ x : E, (∀ j < k, ∀ i, L j i x = 0) ∧ ∀ i, L k i x = c i)
    (h2 : ∀ n, ∃ K, ∀ k ≥ K, ∀ (c : ι k → ℂ) (ε : ℝ), 0 < ε →
      ∃ x : E, (∀ j < k, ∀ i, L j i x = 0) ∧ (∀ i, L k i x = c i) ∧ p n x < ε) :
    Function.Surjective (fun x : E ↦ fun k i ↦ L k i x) := by
  refine surjective_coeff_of_eventually_small_aux L p hpm (fun U hU ↦ ?_) h1 h2
  obtain ⟨⟨s, ε⟩, hε, hsU⟩ := hp.hasBasis_zero_ball.mem_iff.mp hU
  refine ⟨s.sup id, ε, hε, fun x hx ↦ hsU ((Seminorm.mem_ball_zero _).mpr ?_)⟩
  have hle : s.sup p ≤ p (s.sup id) := Finset.sup_le fun i hi ↦ hpm (Finset.le_sup (f := id) hi)
  exact (hle x).trans_lt hx

end RiemannMasullo
