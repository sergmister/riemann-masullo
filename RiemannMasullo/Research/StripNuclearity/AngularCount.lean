module

public import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

/-!
# From conductor-uniform dyadic zero counts to divisor mass

A counting bound of order (n+1)2ⁿ at height 2ⁿ gives a uniform bound for
the reciprocal second moment, preserving its conductor-dependent coefficient.
-/

@[expose] public noncomputable section

namespace RiemannMasullo.StripNuclearity

/-- A dyadic zero count bounded by D(n+1)2ⁿ bounds the reciprocal second
moment by 16D. Both the counts and the moment include full multiplicities. -/
theorem quadratic_mass_le_of_dyadic_count {ι : Type*} (t m : ι → ℝ)
    (ht : ∀ i, 0 ≤ t i) (hm : ∀ i, 0 ≤ m i) (K : ℕ → Finset ι)
    (hK : ∀ n i, i ∈ K n ↔ t i ≤ (2:ℝ)^n) {D : ℝ}
    (hc : ∀ n : ℕ, ∑ i ∈ K n, m i ≤ D*((n:ℝ)+1)*2^n) :
    Summable (fun i ↦ m i/(1+t i)^2) ∧ (∑' i, m i/(1+t i)^2) ≤ 16*D := by
  classical
  let f (p : ℕ × ι) := if p.2 ∈ K p.1 then (4*(1/4:ℝ)^p.1)*m p.2 else 0
  have hf (p) : 0 ≤ f p := by dsimp [f]; split_ifs <;> first | exact le_rfl | positivity [hm p.2]
  have heq (n : ℕ) : (∑' i, f (n,i)) = 4*(1/4:ℝ)^n * ∑ i ∈ K n, m i := by
    rw [tsum_eq_sum (s := K n) (fun i hi ↦ by simp [f,hi]),Finset.mul_sum]
    exact Finset.sum_congr rfl fun i hi ↦ by simp [f,hi]
  have hlocal (n : ℕ) : Summable fun i ↦ f (n,i) :=
    (hasSum_sum_of_ne_finset_zero (s := K n) (fun i hi ↦ by simp [f,hi])).summable
  have hgeom : HasSum (fun n : ℕ ↦ (n+1:ℝ)*(1/2:ℝ)^n) 4 := by
    have h1 := hasSum_coe_mul_geometric_of_norm_lt_one (r := (1/2:ℝ)) (by norm_num)
    have h2 := hasSum_geometric_of_lt_one (by norm_num : 0 ≤ (1/2:ℝ)) (by norm_num)
    convert h1.add h2 using 1
    · funext n
      ring
    · norm_num
  have hbound (n : ℕ) : (∑' i, f (n,i)) ≤ (4*D)*((n+1:ℝ)*(1/2:ℝ)^n) := by
    rw [heq]
    apply (mul_le_mul_of_nonneg_left (hc n) (by positivity)).trans_eq
    have hpow : (1/4:ℝ)^n*2^n = (1/2:ℝ)^n := by rw [← mul_pow]; norm_num
    calc
      _ = (4*D*(n+1:ℝ))*((1/4:ℝ)^n*2^n) := by ring
      _ = _ := by rw [hpow]; ring
  have hrows := (hgeom.mul_left (4*D)).summable.of_nonneg_of_le (fun n ↦ tsum_nonneg (fun i ↦ hf (n,i))) hbound
  have hall : Summable f := (summable_prod_of_nonneg hf).mpr ⟨hlocal,hrows⟩
  have hcols := (summable_prod_of_nonneg (f := fun p : ι × ℕ ↦ f p.swap) (fun p ↦ hf p.swap)).mp hall.prod_symm
  have hweight (i : ι) : m i/(1+t i)^2 ≤ ∑' n, f (n,i) := by
    have hex : ∃ n : ℕ, t i ≤ (2:ℝ)^n := (pow_unbounded_of_one_lt (t i) (by norm_num : (1:ℝ)<2)).imp fun _ h ↦ h.le
    let n := Nat.find hex
    have hn : i ∈ K n := (hK n i).mpr (Nat.find_spec hex)
    apply le_trans _ ((hcols.1 i).le_tsum n (fun k _ ↦ hf (k,i)))
    change m i/(1+t i)^2 ≤ f (n,i)
    simp only [f,hn,ite_true]
    have htwo : (2:ℝ)^n ≤ 2*(1+t i) := by
      cases hn' : n with
      | zero => simp only [pow_zero]; linarith [ht i]
      | succ k =>
        have hlt : (2:ℝ)^k < t i := lt_of_not_ge (Nat.find_min hex (show k < n by omega))
        rw [pow_succ]
        linarith
    have hfour : (1/4:ℝ)^n = (((2:ℝ)^n)^2)⁻¹ := by
      rw [← pow_mul,Nat.mul_comm,pow_mul,← inv_pow]
      norm_num
    rw [div_eq_mul_inv, mul_comm (m i),hfour]
    apply mul_le_mul_of_nonneg_right _ (hm i)
    rw [← div_eq_mul_inv,inv_eq_one_div,div_le_div_iff₀ (by positivity [ht i]) (by positivity)]
    nlinarith [sq_le_sq' (by linarith [show 0 ≤ (2:ℝ)^n by positivity,ht i]) htwo]
  have hs := hcols.2.of_nonneg_of_le (fun i ↦ by positivity [hm i]) hweight
  refine ⟨hs,(hs.tsum_le_tsum hweight hcols.2).trans ?_⟩
  rw [(Summable.tsum_comm (f := fun (n : ℕ) (i : ι) ↦ f (n,i)) hall)]
  apply (hrows.tsum_le_tsum hbound (hgeom.mul_left (4*D)).summable).trans_eq
  rw [(hgeom.mul_left (4*D)).tsum_eq]
  ring

end RiemannMasullo.StripNuclearity
