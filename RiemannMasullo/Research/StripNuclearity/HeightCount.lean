module

public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

/-!
# Dyadic dimensions from a quadratic height moment

A zero contributes to every larger height cutoff. Summing its contributions in
the opposite order gives the quadratic endpoint needed for a second-order
resolvent.
-/

@[expose] public noncomputable section

open Filter Function Set

namespace RiemannMasullo.StripNuclearity

private theorem geometric_tail {q : ℝ} (hq : 0 ≤ q) (hq' : q < 1) (b : ℕ) :
    (∑' n : ℕ, if b ≤ n then q ^ n else 0) = (1-q)⁻¹ * q ^ b := by
  have hgeom := summable_geometric_of_lt_one hq hq'
  have h : Summable fun n : ℕ ↦ if b ≤ n then q ^ n else 0 := by
    apply hgeom.of_nonneg_of_le <;> intro n <;> split_ifs <;> first | exact le_rfl | positivity
  have hn : (∑ n ∈ Finset.range b, if b ≤ n then q ^ n else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    simp [not_le_of_gt (Finset.mem_range.mp hn)]
  rw [← h.sum_add_tsum_nat_add b, hn, zero_add]
  simp only [Nat.le_add_left, ↓reduceIte, pow_add, tsum_mul_right, tsum_geometric_of_lt_one hq hq']

/-- A uniform quantitative estimate for the dyadic window dimensions. Each
individual index contributes at most a constant times its inverse squared height. -/
theorem dyadic_card_mass_le {ι : Type*} (h : ι → ℝ)
    (hp : ∀ i, 0 < h i) (hs : Summable fun i ↦ (h i ^ 2)⁻¹)
    (D : ℝ) (hD : 0 < D) (K : ℕ → Finset ι)
    (hK : ∀ n i, i ∈ K n → h i ≤ D * (2 : ℝ)^n) :
    Summable (fun n : ℕ ↦ ((K n).card : ℝ) * (1/4 : ℝ)^n) ∧
      ∑' n : ℕ, ((K n).card : ℝ) * (1/4 : ℝ)^n ≤
        (1-(1/4 : ℝ))⁻¹ * (D^2 * ∑' i, (h i^2)⁻¹) := by
  classical
  let q := (1/4 : ℝ)
  have hq : 0 ≤ q := by norm_num [q]
  have hq' : q < 1 := by norm_num [q]
  have hg := summable_geometric_of_lt_one hq hq'
  have hex (i : ι) : ∃ n : ℕ, h i ≤ D * (2 : ℝ)^n := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (h i / D) (by norm_num : (1 : ℝ) < 2)
    exact ⟨n, (div_le_iff₀' hD).mp hn.le⟩
  let b (i : ι) := Nat.find (hex i)
  have hb (i : ι) : q ^ b i ≤ D ^ 2 * (h i ^ 2)⁻¹ := by
    have hx := pow_le_pow_left₀ (hp i).le (Nat.find_spec (hex i)) 2
    change h i ^ 2 ≤ (D * (2 : ℝ) ^ b i) ^ 2 at hx
    rw [mul_pow] at hx
    have he : q ^ b i = (((2 : ℝ) ^ b i) ^ 2)⁻¹ := by
      rw [← pow_mul, Nat.mul_comm, pow_mul, ← inv_pow]
      norm_num [q]
    have hp2 : 0 < h i ^ 2 := pow_pos (hp i) 2
    rw [he, ← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    simpa only [one_mul] using hx
  let f (i : ι × ℕ) : ℝ := if i.1 ∈ K i.2 then q ^ i.2 else 0
  have hf : 0 ≤ f := fun i ↦ by dsimp [f]; split_ifs <;> first | exact le_rfl | positivity
  have hsrow (i : ι) : Summable fun n ↦ f (i,n) := hg.of_nonneg_of_le (fun n ↦ hf _)
    (fun n ↦ by dsimp [f]; split_ifs <;> first | exact le_rfl | positivity)
  have row (i : ι) : ∑' n, f (i,n) ≤ (1-q)⁻¹ * (D^2 * (h i ^2)⁻¹) := by
    have hsge : Summable fun n : ℕ ↦ if b i ≤ n then q ^ n else 0 :=
      hg.of_nonneg_of_le (fun n ↦ by split_ifs <;> first | exact le_rfl | positivity) (fun n ↦ by split_ifs <;> first | exact le_rfl | positivity)
    calc
      _ ≤ ∑' n : ℕ, if b i ≤ n then q ^ n else 0 := by
        apply (hsrow i).tsum_le_tsum _ hsge
        intro n
        by_cases hIn : i ∈ K n
        · have hbi : b i ≤ n := Nat.find_min' _ (hK n i hIn)
          simp [f, hIn, hbi]
        · simp only [f, hIn, ↓reduceIte]
          split_ifs <;> first | exact le_rfl | positivity
      _ = (1-q)⁻¹ * q ^ b i := geometric_tail hq hq' _
      _ ≤ _ := mul_le_mul_of_nonneg_left (hb i) (inv_nonneg.mpr (sub_nonneg.mpr hq'.le))
  have hrows := ((hs.mul_left (D ^ 2)).mul_left (1-q)⁻¹).of_nonneg_of_le
    (fun i ↦ tsum_nonneg (fun n ↦ hf (i,n))) row
  have hsum : Summable f := (summable_prod_of_nonneg hf).mpr ⟨hsrow,hrows⟩
  have hcols := ((summable_prod_of_nonneg (f := fun p : ℕ × ι ↦ f p.swap) (fun p ↦ hf p.swap)).mp hsum.prod_symm).2
  have hcol (n : ℕ) : ∑' i, f (i,n) = ((K n).card : ℝ) * (1/4 : ℝ)^n := by
    change (∑' i, if i ∈ K n then q ^ n else 0) = _
    rw [tsum_eq_sum (s := K n) (fun i hi ↦ by simp [hi])]
    simp [q, Finset.sum_ite_mem]
  refine ⟨hcols.congr hcol,?_⟩
  simp_rw [← hcol]
  rw [show (∑' n, ∑' i, f (i,n)) = ∑' i, ∑' n, f (i,n) from
    (Summable.tsum_comm (f := fun (i : ι) (n : ℕ) ↦ f (i,n)) hsum)]
  exact (hrows.tsum_le_tsum row ((hs.mul_left (D^2)).mul_left (1-q)⁻¹)).trans_eq
    (by simp only [tsum_mul_left]; rfl)

/-- If every retained index has height at most `D * 2^n`, the dimensions of
the retained windows are summable against `4⁻ⁿ` whenever the sum of inverse
squared heights is finite. Repeated zeros are separate indices here. -/
theorem summable_dyadic_card_of_quadratic_heights {ι : Type*} (h : ι → ℝ)
    (hp : ∀ i, 0 < h i) (hs : Summable fun i ↦ (h i ^ 2)⁻¹)
    (D : ℝ) (hD : 0 < D) (K : ℕ → Finset ι)
    (hK : ∀ n i, i ∈ K n → h i ≤ D * (2 : ℝ)^n) :
    Summable fun n : ℕ ↦ ((K n).card : ℝ) * (1/4 : ℝ)^n := (dyadic_card_mass_le h hp hs D hD K hK).1

end RiemannMasullo.StripNuclearity
