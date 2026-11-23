module

public import RiemannMasullo.AppC_LCTVS.Sec3a_part2

/-!
# Summing angular operator components

The trace norm is lower semicontinuous for convergence in operator norm on
trace-norm bounded families. Consequently a summable bound on separate
angular components can be used directly on the ambient operator.
-/

@[expose] public noncomputable section

open Filter
open scoped Topology

namespace RiemannMasullo.StripNuclearity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- An operator-norm limit of nuclear maps with uniformly bounded trace norm
is nuclear with the same bound. The finite partial sums of its approximation
numbers pass to the limit separately. -/
theorem traceNorm_le_of_tendsto {ι : Type*} {b : Filter ι} [b.NeBot]
    (S : ι → nuclearEndomorphisms H) (T : H →L[ℂ] H)
    (hT : Tendsto (fun i ↦ (S i).val) b (𝓝 T)) {M : ℝ} (hM : ∀ᶠ i in b, traceNorm (S i) ≤ M) :
    ∃ h : IsNuclearOperator T, traceNorm ⟨T,h⟩ ≤ M := by
  have hmem (i : ι) := (mem_traceClassOperators_iff_isNuclearOperator (S i).val).mpr (S i).property
  have hcompact := isCompactOperator_of_tendsto hT (.of_forall fun i ↦ (hmem i).1)
  have hpos (A : H →L[ℂ] H) (k : ℕ) : 0 ≤ approximationNumber A k :=
    Real.sInf_nonneg (by rintro _ ⟨B,-,rfl⟩; exact norm_nonneg _)
  have hpart (N : ℕ) : ∑ k ∈ Finset.range N, approximationNumber T k ≤ M := by
    have hlim : Tendsto (fun i ↦ ∑ k ∈ Finset.range N, approximationNumber (S i).val k) b
        (𝓝 (∑ k ∈ Finset.range N, approximationNumber T k)) := by
      apply tendsto_finsetSum
      intro k _
      apply tendsto_iff_dist_tendsto_zero.mpr
      exact squeeze_zero' (Eventually.of_forall fun _ ↦ dist_nonneg)
        (.of_forall fun i ↦ by simpa only [Real.dist_eq] using abs_approximationNumber_sub_le (S i).val T k)
        (tendsto_iff_norm_sub_tendsto_zero.mp hT)
    apply le_of_tendsto hlim
    filter_upwards [hM] with i hi
    have hn : Summable fun n ↦ approximationNumber (S i).val n := by
      simpa only [Real.rpow_one] using (hmem i).2
    have he : traceNorm (S i) = ∑' k, approximationNumber (S i).val k := by
      rw [← schattenNorm_one_eq_traceNorm]
      simp only [schattenNorm, Real.rpow_one,div_one]
    exact (hn.sum_le_tsum (Finset.range N) (fun k _ ↦ hpos _ k)).trans (he.symm.le.trans hi)
  have hn : IsNuclearOperator T := (mem_traceClassOperators_iff_isNuclearOperator T).mp
    ⟨hcompact,by simpa only [Real.rpow_one] using summable_of_sum_range_le (hpos T) hpart⟩
  refine ⟨hn,?_⟩
  rw [← schattenNorm_one_eq_traceNorm]
  simpa only [schattenNorm, Real.rpow_one,div_one] using Real.tsum_le_of_sum_range_le (hpos T) hpart

/-- An operator-norm sum of angular components is nuclear whenever their
trace norms have a summable majorant. The conclusion also bounds the trace
norm of the resulting ambient operator. -/
theorem traceNorm_le_of_hasSum {ι : Type*} (S : ι → nuclearEndomorphisms H)
    (T : H →L[ℂ] H) (hs : HasSum (fun i ↦ (S i).val) T) (c : ι → ℝ) (hc : Summable c)
    (hb : ∀ i, traceNorm (S i) ≤ c i) :
    ∃ h : IsNuclearOperator T, traceNorm ⟨T,h⟩ ≤ ∑' i, c i := by
  classical
  let : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
  have hcore := traceNorm_normedSpaceCore (H := H)
  have hfin (K : Finset ι) : traceNorm (∑ i ∈ K, S i) ≤ ∑ i ∈ K, c i := by
    induction K using Finset.induction with
    | empty => simpa using (hcore.norm_eq_zero_iff (0 : nuclearEndomorphisms H)).mpr rfl |>.le
    | insert i K hi ih =>
      rw [Finset.sum_insert hi,Finset.sum_insert hi]
      exact (hcore.norm_triangle _ _).trans (add_le_add (hb i) ih)
  apply traceNorm_le_of_tendsto (b := atTop) (fun K : Finset ι ↦ ∑ i ∈ K, S i) T
  · convert hs using 1
    simp only [Submodule.coe_sum]
    rfl
  · exact .of_forall fun K ↦ (hfin K).trans
      (hc.sum_le_tsum K (fun i _ ↦ (hcore.norm_nonneg (S i)).trans (hb i)))

end RiemannMasullo.StripNuclearity
