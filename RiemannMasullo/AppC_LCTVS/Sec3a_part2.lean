module

public import RiemannMasullo.AppC_LCTVS.Sec3a
public import Mathlib.Analysis.InnerProductSpace.OfNorm
public import Mathlib.Analysis.InnerProductSpace.SingularValues
public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.LinearAlgebra.Dimension.LinearMap
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Topology.MetricSpace.UniformConvergence
import all RiemannMasullo.AppC_LCTVS.Sec3a  -- projective seminorm model and its comparison maps
import RiemannMasullo.ForMathlib.Analysis.Normed.Operator.Compact.NormAttainment

/-!
# Nuclear convergence and Schatten classes

Masullo, Appendix C, §§C.3.5–C.3.6.
-/

@[expose] public noncomputable section

open Filter Function Set Topology TopologicalSpace UniformSpace
open scoped BigOperators InnerProductSpace NNReal TensorProduct

namespace RiemannMasullo

attribute [local instance] uniformContinuousConstSMul_of_continuousConstSMul

section ProjectionConvergence

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section OrthogonalSummands

variable {ι : Type*} (V : ι → ClosedSubmodule ℂ H)

local notation "P(" i ")" => Submodule.starProjection (V i : Submodule ℂ H)
local notation "PairwiseOrthogonal" =>
  Pairwise (fun i j ↦ (V i : Submodule ℂ H) ⟂ (V j : Submodule ℂ H))

/-- Paper: Proposition C.3.5.1, p. 699. A pairwise orthogonal family of nonzero
closed subspaces of a separable Hilbert space has a countable index type. -/
theorem countable_orthogonalSummands [SeparableSpace H]
    (hV : PairwiseOrthogonal) (hne : ∀ i, V i ≠ ⊥) : Countable ι := by
  have exists_unit (i : ι) : ∃ x ∈ (V i : Submodule ℂ H), ‖x‖ = 1 := by
    have hi : (V i : Submodule ℂ H) ≠ ⊥ :=
      fun h ↦ hne i (ClosedSubmodule.toSubmodule_injective h)
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hi
    exact ⟨(‖x‖⁻¹ : ℂ) • x, (V i : Submodule ℂ H).smul_mem _ hx, norm_smul_inv_norm hx0⟩
  choose u hu hunit using exists_unit
  refine Pairwise.countable_of_isOpen_disjoint (s := fun i ↦ Metric.ball (u i) (1 / 2))
    ?_ (fun _ ↦ Metric.isOpen_ball) (fun _ ↦ Metric.nonempty_ball.mpr (by norm_num))
  intro i j hij
  apply Metric.ball_disjoint_ball
  have hsq : dist (u i) (u j) ^ 2 = 2 := by
    rw [dist_eq_norm, @norm_sub_sq ℂ, (hV hij).inner_eq (hu i) (hu j), hunit i, hunit j]
    norm_num
  rw [show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num]
  apply (sq_le_sq₀ zero_le_one dist_nonneg).mp
  rw [hsq]
  norm_num

-- TODO(paper-gap): The proof on p. 701 calls each PᵢT finite-rank. A single
-- summand equal to ℓ²(ℕ) and T diagonal with entries 2^(-n-1) gives a counterexample.

omit [CompleteSpace H] in
/-- The canonical operator associated to an algebraic tensor has finite-dimensional range. -/
private theorem finiteDimensional_range_tensorToFiniteRank
    (z : StrongDual ℂ H ⊗[ℂ] H) :
    FiniteDimensional ℂ (tensorToFiniteRank z).toLinearMap.range := by
  induction z using TensorProduct.inductionOn with
  | tmul φ y =>
    have := FiniteDimensional.span_of_finite ℂ (Set.finite_singleton y)
    apply Submodule.finiteDimensional_of_le (S₂ := ℂ ∙ y)
    rintro _ ⟨x, rfl⟩
    exact Submodule.mem_span_singleton.mpr ⟨φ x, (tensorToFiniteRank_tmul φ y x).symm⟩
  | add z w hz hw =>
    rw [map_add, ContinuousLinearMap.toLinearMap_add]
    exact Submodule.finiteDimensional_of_le (LinearMap.range_add_le _ _)

/-- Paper: Proposition C.3.5.1(1), p. 699. Along any increasing cofinal sequence
of finite subsets, the finite sums of projected nuclear operators converge
in trace norm to the original operator. -/
theorem tendsto_traceNorm_sum_orthogonalProjections_mul [SeparableSpace H]
    (hV : PairwiseOrthogonal) (hne : ∀ i, V i ≠ ⊥)
    (hSOT : ∀ x, Tendsto (fun s : Finset ι ↦ (∑ i ∈ s, P(i)) x) atTop (𝓝 x))
    (s : ℕ → Finset ι) (hs : Monotone s) (hcofinal : ∀ t, ∃ k, t ≤ s k)
    (T : nuclearEndomorphisms H) :
    Tendsto (fun k ↦ traceNorm
      ((∑ i ∈ s k, (⟨P(i) * T.val, mul_mem_nuclearEndomorphisms_left (P(i)) T⟩ :
        nuclearEndomorphisms H)) - T)) atTop (𝓝 0) := by
  let Q (k : ℕ) : H →L[ℂ] H := (∑ i ∈ s k, P(i)) - 1
  have hQ : ∀ x, Tendsto (fun k ↦ Q k x) atTop (𝓝 0) := by
    intro x
    have hx := (hSOT x).comp (hs.tendsto_atTop_atTop hcofinal)
    simpa [Q, Function.comp_def] using hx.sub tendsto_const_nhds (b := x)
  have hP (i : ι) : IsStarProjection (P(i)) := isStarProjection_starProjection
  have hQ_norm (k : ℕ) : ‖Q k‖ ≤ 1 := by
    have hsum : IsStarProjection (∑ i ∈ s k, P(i)) := by
      refine IsStarProjection.sum (fun i _ ↦ hP i) ?_
      intro i _ j _ hij
      exact ((hP i).isSelfAdjoint.isStarOrtho_iff_mul_eq_zero (hP j).isSelfAdjoint).mpr
        (hV hij).starProjection_comp_starProjection
    simpa [Q, norm_sub_rev] using hsum.one_sub.norm_le _
  let product (k : ℕ) (A : nuclearEndomorphisms H) : nuclearEndomorphisms H :=
    ⟨Q k * A.val, mul_mem_nuclearEndomorphisms_left (Q k) A⟩
  have hsum (k : ℕ) :
      (∑ i ∈ s k, (⟨P(i) * T.val, mul_mem_nuclearEndomorphisms_left (P(i)) T⟩ :
        nuclearEndomorphisms H)) - T = product k T := by
    apply Subtype.ext
    simp [product, Q, sub_mul, Finset.sum_mul]
  simp_rw [hsum]
  let : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
  have hcore := (traceNorm_normedSpaceCore (H := H)).toCore
  have hnonneg (A : nuclearEndomorphisms H) : 0 ≤ traceNorm A :=
    hcore.norm_nonneg A
  refine Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
  obtain ⟨z, hz⟩ := exists_tensorToFiniteRank_traceNorm_sub_lt T (half_pos hε)
  let F : nuclearEndomorphisms H :=
    ⟨tensorToFiniteRank z, tensorToFiniteRank_mem_nuclearEndomorphisms z⟩
  obtain ⟨_, hF⟩ := tendsto_traceNorm_mul_finiteRank Q hQ F.val
    (finiteDimensional_range_tensorToFiniteRank z)
  have hF' : Tendsto (fun k ↦ traceNorm (product k F)) atTop (𝓝 0) := hF
  filter_upwards [Metric.tendsto_nhds.mp hF' (ε / 2) (half_pos hε)] with k hk
  have hsplit : product k T = product k (T - F) + product k F := by
    apply Subtype.ext
    simp [product, mul_sub]
  have hbound : traceNorm (product k (T - F)) ≤ traceNorm (T - F) :=
    (traceNorm_mul_left_le (Q k) (T - F)).trans
      (by simpa using mul_le_mul_of_nonneg_right (hQ_norm k) (hnonneg (T - F)))
  have htriangle : traceNorm (product k T) ≤
      traceNorm (product k (T - F)) + traceNorm (product k F) := by
    rw [hsplit]
    exact hcore.norm_triangle _ _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hnonneg (product k F))] at hk
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hnonneg (product k T))]
  change traceNorm (T - F) < ε / 2 at hz
  linarith

/-- Paper: Proposition C.3.5.1(2), p. 699. The finite sums of the traces of
the projected operators converge to the trace of the original operator. -/
theorem tendsto_sum_hilbertTrace_orthogonalProjections_mul [SeparableSpace H]
    (hV : PairwiseOrthogonal) (hne : ∀ i, V i ≠ ⊥)
    (hSOT : ∀ x, Tendsto (fun s : Finset ι ↦ (∑ i ∈ s, P(i)) x) atTop (𝓝 x))
    (s : ℕ → Finset ι) (hs : Monotone s) (hcofinal : ∀ t, ∃ k, t ≤ s k)
    (T : nuclearEndomorphisms H) :
    Tendsto (fun k ↦ ∑ i ∈ s k,
      hilbertTrace ⟨P(i) * T.val, mul_mem_nuclearEndomorphisms_left (P(i)) T⟩)
      atTop (𝓝 (hilbertTrace T)) := by
  obtain ⟨tr, htr⟩ := hilbertTrace_linear (H := H)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [← htr, ← map_sum, ← map_sub]
  simp only [htr]
  exact squeeze_zero (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_hilbertTrace_le _)
    (tendsto_traceNorm_sum_orthogonalProjections_mul V hV hne hSOT s hs hcofinal T)

/-- Paper: Remark C.3.5.2, p. 699. The finite sums of pairwise orthogonal
projections converge strongly to the identity exactly when the algebraic
sum of the subspaces is dense.
The supremum is taken among submodules and only then viewed as a set: written with the set
ascription outside, Lean coerces each summand first and forms the union, for which the statement
is false (two coordinate axes in the plane). -/
theorem tendsto_sum_orthogonalProjections_iff_dense_iSup (hV : PairwiseOrthogonal) :
    (∀ x, Tendsto (fun s : Finset ι ↦ (∑ i ∈ s, P(i)) x) atTop (𝓝 x)) ↔
      Dense (((⨆ i, V i : Submodule ℂ H) : Submodule ℂ H) : Set H) := by
  classical
  let Q (s : Finset ι) : H →L[ℂ] H := ∑ i ∈ s, P(i)
  constructor
  · intro h x
    refine mem_closure_of_tendsto (h x) (Eventually.of_forall fun s ↦ ?_)
    change (∑ i ∈ s, P(i)) x ∈ ⨆ i, (V i : Submodule ℂ H)
    rw [sum_apply]
    exact Submodule.sum_mem _ fun i _ ↦ Submodule.mem_iSup_of_mem i
      (Submodule.starProjection_apply_mem _ x)
  · intro hd x
    refine Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
    -- Approximate x by a vector in the sum of finitely many summands.
    obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp (hd x) ε hε
    change y ∈ ⨆ i, (V i : Submodule ℂ H) at hy
    rw [iSup_eq_iSup_finset] at hy
    have hmono : Monotone (fun s : Finset ι ↦ ⨆ i ∈ s, (V i : Submodule ℂ H)) :=
      fun _ _ h ↦ iSup_le fun i ↦ iSup_le fun hi ↦ le_iSup_of_le i (le_iSup_of_le (h hi) le_rfl)
    obtain ⟨t, ht⟩ := (Submodule.mem_iSup_of_directed _ hmono.directed_le).mp hy
    filter_upwards [eventually_ge_atTop t] with s hs
    have hrange : (⨆ i ∈ s, (V i : Submodule ℂ H)) ≤ (Q s).range := by
      refine iSup_le fun i ↦ iSup_le fun hi z hz ↦ ⟨z, ?_⟩
      change (∑ i ∈ s, P(i)) z = z
      rw [sum_apply, Finset.sum_eq_single_of_mem i hi]
      · exact Submodule.starProjection_eq_self_iff.mpr hz
      · intro j _ hji
        exact (Submodule.starProjection_apply_eq_zero_iff _).mpr ((hV hji.symm) hz)
    have hP (i : ι) : IsStarProjection (P(i)) := isStarProjection_starProjection
    have hQs : IsStarProjection (Q s) := by
      refine IsStarProjection.sum (fun i _ ↦ hP i) ?_
      intro i _ j _ hij
      exact ((hP i).isSelfAdjoint.isStarOrtho_iff_mul_eq_zero (hP j).isSelfAdjoint).mpr
        (hV hij).starProjection_comp_starProjection
    obtain ⟨hproj, hQ⟩ := isStarProjection_iff_eq_starProjection_range.mp hQs
    -- The projection onto the range of Q s is at least as close to x as y is.
    change dist (Q s x) x < ε
    rw [dist_comm, hQ, Submodule.dist_starProjection_eq_infDist]
    exact (Metric.infDist_le_dist_of_mem (hrange (hmono hs ht))).trans_lt hxy

end OrthogonalSummands

end ProjectionConvergence

section ApproximationNumbers

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Paper: (C.3.6.2), p. 704. The approximation number is the infimum of the
operator-norm errors of approximants of bounded finite rank.
Deviation: Indices start at zero, so index n allows rank at most n. The definition is
placed here for the singular-value statements in §C.3.5. -/
def approximationNumber (T : E →L[ℂ] F) (n : ℕ) : ℝ :=
  sInf {r | ∃ S : E →L[ℂ] F, Module.rank ℂ S.toLinearMap.range ≤ (n : Cardinal) ∧ r = ‖S - T‖}

/-- Paper: (C.3.6.2), p. 704. In finite dimensions the approximation
numbers agree with Mathlib's singular values, including the zero tail.
Deviation: This checks the rank cutoff and the zero-based indexing. -/
theorem approximationNumber_eq_singularValues [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    (T : E →L[ℂ] F) (n : ℕ) :
    approximationNumber T n = T.toLinearMap.singularValues n := by
  classical
  let errors : Set ℝ := {r | ∃ S : E →L[ℂ] F,
    Module.rank ℂ S.toLinearMap.range ≤ (n : Cardinal) ∧ r = ‖S - T‖}
  change sInf errors = _
  have hnonneg : (0 : ℝ) ∈ lowerBounds errors := by
    rintro r ⟨S, _, rfl⟩
    exact norm_nonneg _
  have hzero : Module.rank ℂ (0 : E →L[ℂ] F).toLinearMap.range ≤ (n : Cardinal) := by simp
  by_cases hlarge : Module.finrank ℂ T.toLinearMap.range ≤ n
  · have hrank : Module.rank ℂ T.toLinearMap.range ≤ (n : Cardinal) := by
      simpa only [← Module.finrank_eq_rank, Nat.cast_le] using hlarge
    rw [T.toLinearMap.singularValues_eq_zero_iff_le_finrank_range.mpr hlarge]
    apply le_antisymm
    · exact (csInf_le ⟨0, hnonneg⟩ ⟨T, hrank, rfl⟩).trans_eq (by simp)
    · exact le_csInf ⟨_, T, hrank, rfl⟩ hnonneg
  have hn := (Nat.lt_of_not_ge hlarge).trans_le T.toLinearMap.finrank_range_le
  let hSymm := T.toLinearMap.isSymmetric_adjoint_comp_self
  let b := hSymm.eigenvectorBasis rfl
  let σ := T.toLinearMap.singularValues
  have hσ : ∀ i, 0 ≤ σ i := T.toLinearMap.singularValues_nonneg
  have hanti : Antitone σ := T.toLinearMap.singularValues_antitone
  -- In the eigenbasis of T†T, the squared norm of T x is a weighted sum of coordinates.
  have henergy (x : E) : ‖T x‖ ^ 2 =
      ∑ i : Fin (Module.finrank ℂ E), σ i ^ 2 * ‖⟪b i, x⟫_ℂ‖ ^ 2 := by
    rw [show ‖T x‖ ^ 2 = RCLike.re ⟪x, (T.toLinearMap.adjoint ∘ₗ T.toLinearMap) x⟫_ℂ by
      rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right, ← norm_sq_eq_re_inner]
      rfl]
    rw [← b.sum_inner_mul_inner, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← b.repr_apply_apply, hSymm.eigenvectorBasis_apply_self_apply rfl,
      ← T.toLinearMap.sq_singularValues_fin rfl i, b.repr_apply_apply]
    rw [mul_left_comm, RCLike.re_ofReal_mul, inner_mul_symm_re_eq_norm, norm_mul,
      ← inner_conj_symm x, RCLike.norm_conj, ← pow_two]
  let V (k : ℕ) := Submodule.span ℂ (b '' {i | (i : ℕ) < k})
  have hdim (k : ℕ) (hk : k ≤ Module.finrank ℂ E) : Module.finrank ℂ (V k) = k := by
    have hind := b.orthonormal.linearIndependent.comp (Fin.castLE hk) (Fin.castLE_injective hk)
    change Module.finrank ℂ (Submodule.span ℂ (b '' {i | (i : ℕ) < k})) = k
    rw [← Fin.range_castLE hk, ← Set.range_comp]
    simpa only [Fintype.card_fin] using finrank_span_eq_card hind
  apply le_antisymm
  · -- Truncate T to the first n eigenvectors.
    let S := T.comp (V n).starProjection
    have hS : Module.rank ℂ S.toLinearMap.range ≤ (n : Cardinal) := by
      rw [← Module.finrank_eq_rank, Nat.cast_le]
      change Module.finrank ℂ (T.toLinearMap.comp (V n).starProjection.toLinearMap).range ≤ n
      rw [LinearMap.range_comp, Submodule.range_starProjection]
      exact (Submodule.finrank_map_le _ _).trans_eq (hdim n hn.le)
    refine (csInf_le ⟨0, hnonneg⟩ ⟨S, hS, rfl⟩).trans ?_
    rw [norm_sub_rev]
    apply ContinuousLinearMap.opNorm_le_bound _ (hσ n)
    intro x
    let y := (V n)ᗮ.starProjection x
    have hy : y ∈ (V n)ᗮ := ((V n)ᗮ.orthogonalProjectionOnto x).property
    have heq : (T - S) x = T y := by
      simp [S, y, map_sub]
    rw [heq]
    refine (show ‖T y‖ ≤ σ n * ‖y‖ from ?_).trans
      (mul_le_mul_of_nonneg_left ((V n)ᗮ.norm_starProjection_apply_le x) (hσ n))
    apply le_of_sq_le_sq _ (mul_nonneg (hσ n) (norm_nonneg _))
    rw [henergy, mul_pow, ← b.sum_sq_norm_inner_right y, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : (i : ℕ) < n
    · have hz := ((V n).mem_orthogonal y).mp hy (b i)
          (Submodule.subset_span (Set.mem_image_of_mem _ hi))
      simp [hz]
    · exact mul_le_mul_of_nonneg_right
        ((sq_le_sq₀ (hσ i) (hσ n)).mpr (hanti (Nat.le_of_not_lt hi))) (sq_nonneg _)
  · refine le_csInf ⟨_, 0, hzero, rfl⟩ ?_
    rintro r ⟨S, hS, rfl⟩
    have hSdim : Module.finrank ℂ S.toLinearMap.range ≤ n := by
      simpa only [← Module.finrank_eq_rank, Nat.cast_le] using hS
    -- Every admissible S kills a nonzero vector in the span of the first n + 1 eigenvectors.
    let R := S.toLinearMap.rangeRestrict.comp (V (n + 1)).subtype
    have hker : R.ker ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by
      rw [hdim (n + 1) hn]
      exact Nat.lt_succ_of_le hSdim)
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    have hSx : S (x : E) = 0 := congrArg Subtype.val (LinearMap.mem_ker.mp hx)
    have hxnorm : 0 < ‖(x : E)‖ := norm_pos_iff.mpr (fun h ↦ hx0 (Subtype.ext h))
    have hlower : σ n * ‖(x : E)‖ ≤ ‖T (x : E)‖ := by
      apply le_of_sq_le_sq _ (norm_nonneg _)
      rw [henergy, mul_pow, ← b.sum_sq_norm_inner_right (x : E), Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : (i : ℕ) ≤ n
      · exact mul_le_mul_of_nonneg_right
          ((sq_le_sq₀ (hσ n) (hσ i)).mpr (hanti hi)) (sq_nonneg _)
      · have hsupport := (b.toBasis.repr_support_subset_of_mem_span _ x.property)
        have hz : ⟪b i, (x : E)⟫_ℂ = 0 := by
          rw [← b.repr_apply_apply, ← b.coe_toBasis_repr_apply, ← Finsupp.notMem_support_iff]
          exact fun hs ↦ hi (Nat.lt_succ_iff.mp (hsupport hs))
        simp [hz]
    have hbound := (S - T).le_opNorm (x : E)
    rw [sub_apply, hSx, zero_sub, norm_neg] at hbound
    exact le_of_mul_le_mul_right (hlower.trans hbound) hxnorm

end ApproximationNumbers

section SingularValues

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Within any positive operator-norm distance of `A.adjoint` there is a compact operator.
The approximant is `A.adjoint` postcomposed with the orthogonal projection onto a
finite-dimensional subspace, so it factors through a locally compact space. -/
private theorem exists_isCompactOperator_norm_sub_adjoint_le (A : H →L[ℂ] H)
    (hA : IsCompactOperator A) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : H →L[ℂ] H, IsCompactOperator C ∧ ‖A.adjoint - C‖ ≤ ε := by
  obtain ⟨t, -, ht_fin, ht_cover⟩ :=
    (hA.isCompact_closure_image_closedBall 1).finite_cover_balls hε
  let U : Submodule ℂ H := Submodule.span ℂ t
  have : FiniteDimensional ℂ U := FiniteDimensional.span_of_finite ℂ ht_fin
  have : CompleteSpace U := FiniteDimensional.completeSpace ℂ U
  have : U.HasOrthogonalProjection := inferInstance
  have hnorm : ‖A - U.starProjection ∘L A‖ ≤ ε := by
    refine ContinuousLinearMap.opNorm_le_bound _ hε.le fun x ↦ ?_
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
      let u : H := (‖x‖⁻¹ : ℂ) • x
      have hu : ‖u‖ = 1 := by
        rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0,
          inv_mul_cancel₀ hx0.ne']
      have hBu : ‖(A - U.starProjection ∘L A) u‖ < ε := by
        have hu_ball : u ∈ Metric.closedBall (0 : H) 1 := by
          rw [Metric.mem_closedBall, dist_zero_right, hu]
        have hAu : A u ∈ closure (A '' Metric.closedBall (0 : H) 1) :=
          subset_closure ⟨u, hu_ball, rfl⟩
        obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht_cover hAu)
        have hdist : Metric.infDist (A u) (U : Set H) < ε :=
          (Metric.infDist_lt_iff ⟨0, Submodule.zero_mem U⟩).2
            ⟨y, Submodule.subset_span hy, Metric.mem_ball.mp hxy⟩
        rw [sub_apply, ContinuousLinearMap.comp_apply, ← dist_eq_norm,
          U.dist_starProjection_eq_infDist]
        exact hdist
      have hxeq : (‖x‖ : ℂ) • u = x := by
        simp only [u, smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hx0.ne'), one_smul]
      have hBx : ‖(A - U.starProjection ∘L A) x‖ =
          ‖x‖ * ‖(A - U.starProjection ∘L A) u‖ := by
        conv_lhs => rw [← hxeq]
        rw [(A - U.starProjection ∘L A).map_smul, norm_smul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg hx0.le]
      rw [hBx]
      calc
        ‖x‖ * ‖(A - U.starProjection ∘L A) u‖ ≤ ‖x‖ * ε :=
          mul_le_mul_of_nonneg_left hBu.le hx0.le
        _ = ε * ‖x‖ := mul_comm _ _
  refine ⟨A.adjoint ∘L U.starProjection, ?_, ?_⟩
  · have : LocallyCompactSpace U :=
      LocallyCompactSpace.of_finiteDimensional_of_complete ℂ U
    have hfac : A.adjoint ∘L U.starProjection =
        (A.adjoint ∘L U.subtypeL) ∘L U.orthogonalProjectionOnto := rfl
    rw [hfac]
    exact (isCompactOperator_of_locallyCompactSpace_rng
      (A.adjoint ∘L U.subtypeL)).comp_clm U.orthogonalProjectionOnto
  · rw [← (isSelfAdjoint_starProjection U).adjoint_eq, ← ContinuousLinearMap.adjoint_comp,
      ← (ContinuousLinearMap.adjoint (E := H) (F := H)).map_sub,
      (ContinuousLinearMap.adjoint (E := H) (F := H)).norm_map]
    exact hnorm

/-- Paper: Lemma C.3.5.3(1), p. 700. The adjoint of a compact endomorphism is compact. -/
theorem isCompactOperator_adjoint_of_compact (A : H →L[ℂ] H)
    (hA : IsCompactOperator A) : IsCompactOperator A.adjoint := by
  have happrox : ∀ n : ℕ, ∃ C : H →L[ℂ] H,
      IsCompactOperator C ∧ ‖A.adjoint - C‖ ≤ 1 / (n + 1 : ℝ) := by
    intro n
    exact exists_isCompactOperator_norm_sub_adjoint_le A hA (by positivity)
  choose C hC hle using happrox
  refine isCompactOperator_of_tendsto (l := atTop) (F := C) ?_ (Eventually.of_forall hC)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [dist_eq_norm, norm_sub_rev]
  refine (hle n).trans_lt ?_
  have hbig : 1 / ε < (n : ℝ) + 1 :=
    lt_trans (lt_of_lt_of_le hN (Nat.cast_le.mpr hn)) (lt_add_one _)
  have hmul : 1 < ((n : ℝ) + 1) * ε := (div_lt_iff₀ hε).mp hbig
  rw [show (1 : ℝ) / (n + 1 : ℝ) = 1 / ((n : ℝ) + 1) by simp,
    div_lt_iff₀' (by positivity)]
  exact hmul

/-- Paper: Lemma C.3.5.3(1), p. 700. A compact endomorphism and its adjoint
have the same singular values at every index up to the Hilbert space dimension.
Deviation: The singular values use the approximation-number definition with zero-based indices. -/
theorem approximationNumber_adjoint (A : H →L[ℂ] H) (hA : IsCompactOperator A)
    (n : ℕ) (hn : (n : Cardinal) < Module.rank ℂ H) :
    approximationNumber A n = approximationNumber A.adjoint n := by
  clear hA hn
  have rank_adjoint_le (S : H →L[ℂ] H)
      (hS : Module.rank ℂ S.toLinearMap.range ≤ (n : Cardinal)) :
      Module.rank ℂ S.adjoint.toLinearMap.range ≤ (n : Cardinal) := by
    let V := S.toLinearMap.range
    have : FiniteDimensional ℂ V :=
      Module.rank_lt_aleph0_iff.mp (hS.trans_lt Cardinal.natCast_lt_aleph0)
    have : CompleteSpace V := FiniteDimensional.completeSpace ℂ V
    -- Factoring S through its range gives a factorization of its adjoint through V.
    have hfac : V.subtypeL.comp S.rangeRestrict = S := rfl
    have hadj : S.adjoint = S.rangeRestrict.adjoint.comp V.subtypeL.adjoint := by
      rw [← ContinuousLinearMap.adjoint_comp, hfac]
    rw [hadj]
    exact (LinearMap.rank_comp_le_left _ _).trans
      (S.rangeRestrict.adjoint.toLinearMap.rank_le_domain.trans hS)
  let errors (T : H →L[ℂ] H) : Set ℝ :=
    {r | ∃ S : H →L[ℂ] H, Module.rank ℂ S.toLinearMap.range ≤ (n : Cardinal) ∧ r = ‖S - T‖}
  have errors_subset (T : H →L[ℂ] H) : errors T ⊆ errors T.adjoint := by
    rintro _ ⟨S, hS, rfl⟩
    refine ⟨S.adjoint, rank_adjoint_le S hS, ?_⟩
    rw [← ContinuousLinearMap.adjoint.map_sub, LinearIsometryEquiv.norm_map]
  change sInf (errors A) = sInf (errors A.adjoint)
  apply congrArg sInf
  exact Set.Subset.antisymm (errors_subset A)
    (by simpa only [ContinuousLinearMap.adjoint_adjoint] using errors_subset A.adjoint)

/-- Paper: Lemma C.3.5.3(2), p. 700. The first singular value of a compact
endomorphism equals its operator norm.
Deviation: The first approximation number has index zero. -/
theorem approximationNumber_zero_eq_opNorm (A : H →L[ℂ] H) (hA : IsCompactOperator A) :
    approximationNumber A 0 = ‖A‖ := by
  have hset : {r | ∃ S : H →L[ℂ] H, Module.rank ℂ S.toLinearMap.range ≤ ((0 : ℕ) : Cardinal) ∧
      r = ‖S - A‖} = {‖A‖} := by
    ext r
    constructor
    · rintro ⟨S, hS, rfl⟩
      have h0 : Module.rank ℂ S.toLinearMap.range = 0 := by
        rw [Nat.cast_zero] at hS
        exact le_zero_iff.mp hS
      rw [Submodule.rank_eq_zero, LinearMap.range_eq_bot] at h0
      have hS0 : S = 0 := ContinuousLinearMap.coe_injective h0
      simp [hS0]
    · rintro rfl
      exact ⟨0, by simp, by simp⟩
  unfold approximationNumber
  rw [hset, csInf_singleton]

-- TODO(paper-gap): The proof of (C.3.5.4) uses global weak continuity of the
-- quadratic form of a compact operator and weak compactness of the unit sphere.
-- The quadratic form is weakly continuous on bounded sets, and the closed unit
-- ball is weakly compact. The proof also writes the rank-one spectral
-- projector in (C.3.5.5) as a projection onto a kernel, and the tail span
-- argument can fail for repeated eigenvalues. The min-max identities still hold.
-- The polar isometry used in part (1) has initial space (ker A)ᗮ.

/-- The restriction of `A` to the orthogonal complement of a proper finite-dimensional
subspace has a maximizing unit vector. Its image is orthogonal to the images of all vectors
in the complement that are orthogonal to it. -/
private theorem exists_unit_maximizer_on_orthogonal (A : H →L[ℂ] H) (hA : IsCompactOperator A)
    {n : ℕ} (hn : (n : Cardinal) < Module.rank ℂ H)
    {V : Submodule ℂ H} (hV : Module.rank ℂ V = (n : Cardinal)) :
    ∃ e ∈ Vᗮ, ‖e‖ = 1 ∧ ‖A e‖ = ‖A.comp Vᗮ.subtypeL‖ ∧
      ∀ y ∈ Vᗮ, ⟪e, y⟫_ℂ = 0 → ⟪A e, A y⟫_ℂ = 0 := by
  have : FiniteDimensional ℂ V :=
    Module.rank_lt_aleph0_iff.mp (hV.trans_lt Cardinal.natCast_lt_aleph0)
  let : CompleteSpace V := FiniteDimensional.completeSpace ℂ V
  have hproper : V ≠ ⊤ := by
    intro h
    exact hn.ne (by rw [← hV, h, rank_top])
  have : Nontrivial Vᗮ := Submodule.nontrivial_iff_ne_bot.mpr
    (fun h ↦ hproper (V.orthogonal_eq_bot_iff.mp h))
  let T := A.comp Vᗮ.subtypeL
  obtain ⟨e, he, heA, heig⟩ :=
    exists_unit_norm_eq_opNorm_of_isCompactOperator T (hA.comp_clm Vᗮ.subtypeL)
  refine ⟨e, e.property, he, heA, fun y hy hinner ↦ ?_⟩
  let z : Vᗮ := ⟨y, hy⟩
  change ⟪T e, T z⟫_ℂ = 0
  rw [← T.adjoint_inner_left, heig, inner_smul_left]
  change (starRingEnd ℂ _) * ⟪(e : H), y⟫_ℂ = 0
  rw [hinner, mul_zero]

/-- Adjoin a maximizing line to a subspace whose image is orthogonal to the image of its
orthogonal complement. The enlarged subspace retains this property and has a lower
norm bound given by the old restriction norm. -/
private theorem exists_succ_rank_subspace_of_compact (A : H →L[ℂ] H)
    (hA : IsCompactOperator A) {n : ℕ} (hn : (n : Cardinal) < Module.rank ℂ H)
    {V : Submodule ℂ H} (hV : Module.rank ℂ V = (n : Cardinal))
    (horth : ∀ x ∈ V, ∀ y ∈ Vᗮ, ⟪A x, A y⟫_ℂ = 0)
    (hlower : ∀ x ∈ V, ‖A.comp Vᗮ.subtypeL‖ * ‖x‖ ≤ ‖A x‖) :
    ∃ U : Submodule ℂ H, V ≤ U ∧ Module.rank ℂ U = ((n + 1 : ℕ) : Cardinal) ∧
      (∀ x ∈ U, ∀ y ∈ Uᗮ, ⟪A x, A y⟫_ℂ = 0) ∧
      ∀ x ∈ U, ‖A.comp Vᗮ.subtypeL‖ * ‖x‖ ≤ ‖A x‖ := by
  obtain ⟨e, heV, he, heA, heorth⟩ := exists_unit_maximizer_on_orthogonal A hA hn hV
  let L : Submodule ℂ H := ℂ ∙ e
  have hL : L ≤ Vᗮ := Submodule.span_le.mpr (Set.singleton_subset_iff.mpr heV)
  have he0 : e ≠ 0 := by
    intro h
    simp [h] at he
  have hrankL : Module.rank ℂ L = 1 := by
    rw [← Module.finrank_eq_rank, finrank_span_singleton he0, Nat.cast_one]
  have hrank : Module.rank ℂ (V ⊔ L : Submodule ℂ H) = ((n + 1 : ℕ) : Cardinal) := by
    have hinf : V ⊓ L = ⊥ := (V.orthogonal_disjoint.mono_right hL).eq_bot
    have h := V.rank_sup_add_rank_inf_eq L
    rw [hinf, rank_bot, add_zero, hV, hrankL] at h
    simpa only [Nat.cast_add, Nat.cast_one] using h
  refine ⟨V ⊔ L, le_sup_left, hrank, ?_, ?_⟩
  · intro x hx y hy
    obtain ⟨v, hv, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
    have hyV : y ∈ Vᗮ := Submodule.orthogonal_le le_sup_left hy
    have hyL : y ∈ Lᗮ := Submodule.orthogonal_le le_sup_right hy
    rw [map_add, map_smul, inner_add_left, inner_smul_left, horth v hv y hyV,
      heorth y hyV (Submodule.mem_orthogonal_singleton_iff_inner_right.mp hyL), mul_zero,
      add_zero]
  · intro x hx
    obtain ⟨v, hv, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    have hzV : z ∈ Vᗮ := hL hz
    let c := ‖A.comp Vᗮ.subtypeL‖
    have hz_eq : ‖A z‖ = c * ‖z‖ := by
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
      rw [map_smul, norm_smul, norm_smul, heA, he, mul_one, mul_comm]
    apply le_of_sq_le_sq _ (norm_nonneg _)
    change (c * ‖v + z‖) ^ 2 ≤ ‖A (v + z)‖ ^ 2
    calc
      (c * ‖v + z‖) ^ 2 = (c * ‖v‖) ^ 2 + (c * ‖z‖) ^ 2 := by
        rw [mul_pow, norm_add_sq (𝕜 := ℂ) v z, (V.mem_orthogonal z).mp hzV v hv]
        simp only [RCLike.zero_re, mul_zero, add_zero, mul_add, mul_pow]
      _ ≤ ‖A v‖ ^ 2 + ‖A z‖ ^ 2 := by
        rw [← hz_eq]
        exact add_le_add ((sq_le_sq₀ (by positivity) (norm_nonneg _)).mpr (hlower v hv)) le_rfl
      _ = ‖A (v + z)‖ ^ 2 := by
        rw [map_add, norm_add_sq (𝕜 := ℂ) (A v) (A z), horth v hv z hzV]
        simp

/-- There are `n` dimensions whose image is orthogonal to the image of the complement, with
norm bounded below by the norm of the operator on the complement. -/
private theorem exists_rank_subspace_of_compact (A : H →L[ℂ] H) (hA : IsCompactOperator A)
    (n : ℕ) (hn : (n : Cardinal) ≤ Module.rank ℂ H) :
    ∃ V : Submodule ℂ H, Module.rank ℂ V = (n : Cardinal) ∧
      (∀ x ∈ V, ∀ y ∈ Vᗮ, ⟪A x, A y⟫_ℂ = 0) ∧
      ∀ x ∈ V, ‖A.comp Vᗮ.subtypeL‖ * ‖x‖ ≤ ‖A x‖ := by
  induction n with
  | zero =>
    refine ⟨⊥, by simp, ?_, ?_⟩ <;> simp
  | succ n ih =>
    have hlt : (n : Cardinal) < Module.rank ℂ H :=
      (Nat.cast_lt.mpr (Nat.lt_succ_self n)).trans_le hn
    obtain ⟨V, hV, horth, hlower⟩ := ih hlt.le
    obtain ⟨U, hVU, hU, hUorth, hUlower⟩ :=
      exists_succ_rank_subspace_of_compact A hA hlt hV horth hlower
    refine ⟨U, hU, hUorth, fun x hx ↦ ?_⟩
    have hmono : ‖A.comp Uᗮ.subtypeL‖ ≤ ‖A.comp Vᗮ.subtypeL‖ := by
      refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun y ↦ ?_
      exact (A.comp Vᗮ.subtypeL).le_opNorm ⟨y, Submodule.orthogonal_le hVU y.property⟩
    exact (mul_le_mul_of_nonneg_right hmono (norm_nonneg _)).trans (hUlower x hx)

/-- Paper: Lemma C.3.5.3(3), p. 700. The singular value is the smallest of
the attained maxima of the norm of A on the unit sphere of each orthogonal
complement of an n-dimensional subspace.
Deviation: The singular value has zero-based index n. -/
theorem approximationNumber_min_max (A : H →L[ℂ] H) (hA : IsCompactOperator A)
    (n : ℕ) (hn : (n : Cardinal) < Module.rank ℂ H) :
    ∃ maxima : {V : Submodule ℂ H // Module.rank ℂ V = (n : Cardinal)} → ℝ,
      (∀ V, IsGreatest {r | ∃ x ∈ Submodule.orthogonal (Subtype.val V), ‖x‖ = 1 ∧ r = ‖A x‖} (maxima V)) ∧
        IsLeast (Set.range maxima) (approximationNumber A n) := by
  let maxima (V : {V : Submodule ℂ H // Module.rank ℂ V = (n : Cardinal)}) :=
    ‖A.comp (Subtype.val V)ᗮ.subtypeL‖
  have hmax (V : {V : Submodule ℂ H // Module.rank ℂ V = (n : Cardinal)}) :
      IsGreatest {r | ∃ x ∈ (Subtype.val V)ᗮ, ‖x‖ = 1 ∧ r = ‖A x‖} (maxima V) := by
    obtain ⟨e, he, he1, heA, _⟩ := exists_unit_maximizer_on_orthogonal A hA hn V.property
    refine ⟨⟨e, he, he1, heA.symm⟩, ?_⟩
    rintro _ ⟨x, hx, hx1, rfl⟩
    simpa [maxima, hx1] using (A.comp V.valᗮ.subtypeL).le_opNorm ⟨x, hx⟩
  have hle (V : {V : Submodule ℂ H // Module.rank ℂ V = (n : Cardinal)}) :
      approximationNumber A n ≤ maxima V := by
    have : FiniteDimensional ℂ V.val :=
      Module.rank_lt_aleph0_iff.mp (V.property.trans_lt Cardinal.natCast_lt_aleph0)
    let : CompleteSpace V.val := FiniteDimensional.completeSpace ℂ V.val
    -- Projecting onto V gives an admissible rank-n approximation.
    let S := A.comp V.val.starProjection
    have hS : Module.rank ℂ S.toLinearMap.range ≤ (n : Cardinal) := by
      refine (LinearMap.rank_comp_le_right V.val.starProjection.toLinearMap A.toLinearMap).trans ?_
      change Module.rank ℂ V.val.starProjection.toLinearMap.range ≤ (n : Cardinal)
      rw [Submodule.range_starProjection, V.property]
    have hdiff : A - S = (A.comp V.valᗮ.subtypeL).comp V.valᗮ.orthogonalProjectionOnto := by
      change A - S = A.comp V.valᗮ.starProjection
      ext x
      simp [S, map_sub]
    have happ : approximationNumber A n ≤ ‖S - A‖ :=
      csInf_le ⟨0, by rintro _ ⟨_, _, rfl⟩; exact norm_nonneg _⟩ ⟨S, hS, rfl⟩
    refine happ.trans ?_
    rw [norm_sub_rev, hdiff]
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x ↦ ?_
    exact ((A.comp V.valᗮ.subtypeL).le_opNorm (V.valᗮ.orthogonalProjectionOnto x)).trans
      (mul_le_mul_of_nonneg_left (V.valᗮ.norm_orthogonalProjectionOnto_apply_le x) (norm_nonneg _))
  obtain ⟨V, hV, horth, hlower⟩ := exists_rank_subspace_of_compact A hA n hn.le
  obtain ⟨U, _, hU, _, hUlower⟩ := exists_succ_rank_subspace_of_compact A hA hn hV horth hlower
  let V₀ : {V : Submodule ℂ H // Module.rank ℂ V = (n : Cardinal)} := ⟨V, hV⟩
  have hge : maxima V₀ ≤ approximationNumber A n := by
    refine le_csInf ⟨_, 0, by simp, rfl⟩ ?_
    rintro _ ⟨S, hS, rfl⟩
    -- Every admissible approximant kills a nonzero vector in U.
    let R := S.toLinearMap.rangeRestrict.comp U.subtype
    have hker : R.ker ≠ ⊥ := by
      intro h
      have hr := (R.rank_le_of_injective (LinearMap.ker_eq_bot.mp h)).trans hS
      rw [hU] at hr
      exact (not_le_of_gt (Nat.cast_lt.mpr (Nat.lt_succ_self n))) hr
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    have hSx : S (x : H) = 0 := congrArg Subtype.val (LinearMap.mem_ker.mp hx)
    have hnorm : 0 < ‖(x : H)‖ := norm_pos_iff.mpr fun h ↦ hx0 (Subtype.ext h)
    have hbound := (S - A).le_opNorm (x : H)
    rw [sub_apply, hSx, zero_sub, norm_neg] at hbound
    exact le_of_mul_le_mul_right ((hUlower x x.property).trans hbound) hnorm
  refine ⟨maxima, hmax, ⟨⟨V₀, le_antisymm hge (hle V₀)⟩, ?_⟩⟩
  rintro _ ⟨W, rfl⟩
  exact hle W

/-- Paper: Lemma C.3.5.3(3), p. 700. The singular value is the largest of
the attained minima of the norm of A on the unit sphere of each
(n + 1)-dimensional subspace.
Deviation: The singular value has zero-based index n. -/
theorem approximationNumber_max_min (A : H →L[ℂ] H) (hA : IsCompactOperator A)
    (n : ℕ) (hn : (n : Cardinal) < Module.rank ℂ H) :
    ∃ minima : {V : Submodule ℂ H // Module.rank ℂ V = ((n + 1 : ℕ) : Cardinal)} → ℝ,
      (∀ V, IsLeast {r | ∃ x ∈ Subtype.val V, ‖x‖ = 1 ∧ r = ‖A x‖} (minima V)) ∧
        IsGreatest (Set.range minima) (approximationNumber A n) := by
  classical
  have hmin (U : {V : Submodule ℂ H // Module.rank ℂ V = ((n + 1 : ℕ) : Cardinal)}) :
      ∃ m : ℝ, IsLeast {r | ∃ x ∈ U.val, ‖x‖ = 1 ∧ r = ‖A x‖} m := by
    have : FiniteDimensional ℂ U.val :=
      Module.rank_lt_aleph0_iff.mp (U.property.trans_lt Cardinal.natCast_lt_aleph0)
    have : Nontrivial U.val := Submodule.nontrivial_iff_ne_bot.mpr fun h ↦
      (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)) (U.property.symm.trans (Submodule.rank_eq_zero.mpr h))
    let : ProperSpace U.val := FiniteDimensional.proper ℂ U.val
    obtain ⟨x, hx, hxmin⟩ := (isCompact_sphere (0 : U.val) 1).exists_isMinOn
      (Set.nonempty_coe_sort.mp (NormedSpace.sphere_nonempty_rclike ℂ zero_le_one))
      (A.comp U.val.subtypeL).continuous.norm.continuousOn
    refine ⟨‖A x‖, ⟨x, x.property, mem_sphere_zero_iff_norm.mp hx, rfl⟩, ?_⟩
    rintro _ ⟨y, hy, hy1, rfl⟩
    exact isMinOn_iff.mp hxmin ⟨y, hy⟩ (mem_sphere_zero_iff_norm.mpr hy1)
  choose minima hminima using hmin
  obtain ⟨maxima, hmaxima, hleast⟩ := approximationNumber_min_max A hA n hn
  obtain ⟨W, hW⟩ := hleast.1
  -- Every (n + 1)-dimensional subspace contains a unit vector orthogonal to W.
  have hle (U : {V : Submodule ℂ H // Module.rank ℂ V = ((n + 1 : ℕ) : Cardinal)}) :
      minima U ≤ approximationNumber A n := by
    have : FiniteDimensional ℂ W.val :=
      Module.rank_lt_aleph0_iff.mp (W.property.trans_lt Cardinal.natCast_lt_aleph0)
    let : CompleteSpace W.val := FiniteDimensional.completeSpace ℂ W.val
    let R := W.val.orthogonalProjectionOnto.toLinearMap.comp U.val.subtype
    have hker : R.ker ≠ ⊥ := by
      intro h
      have hrank := R.rank_le_of_injective (LinearMap.ker_eq_bot.mp h)
      rw [U.property, W.property] at hrank
      exact (not_le_of_gt (Nat.cast_lt.mpr (Nat.lt_succ_self n))) hrank
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    let y : U.val := (↑‖x‖ : ℂ)⁻¹ • x
    have hy1 : ‖y‖ = 1 := norm_smul_inv_norm hx0
    have hyker : y ∈ R.ker := R.ker.smul_mem _ hx
    have hyW : (y : H) ∈ W.valᗮ := by
      rw [← W.val.ker_orthogonalProjectionOnto]
      exact hyker
    rw [← hW]
    exact (hminima U).2 ⟨y, y.property, hy1, rfl⟩ |>.trans
      ((hmaxima W).2 ⟨y, hyW, hy1, rfl⟩)
  -- Enlarging V by a maximizing line bounds the new minimum from below.
  obtain ⟨V, hV, horth, hlower⟩ := exists_rank_subspace_of_compact A hA n hn.le
  obtain ⟨U, _, hU, _, hUlower⟩ := exists_succ_rank_subspace_of_compact A hA hn hV horth hlower
  let V₀ : {V : Submodule ℂ H // Module.rank ℂ V = (n : Cardinal)} := ⟨V, hV⟩
  let U₀ : {V : Submodule ℂ H // Module.rank ℂ V = ((n + 1 : ℕ) : Cardinal)} := ⟨U, hU⟩
  have hge : approximationNumber A n ≤ minima U₀ := by
    obtain ⟨v, hv, hv1, hvA⟩ := (hmaxima V₀).1
    obtain ⟨u, hu, hu1, huA⟩ := (hminima U₀).1
    calc
      approximationNumber A n ≤ maxima V₀ := hleast.2 ⟨V₀, rfl⟩
      _ ≤ ‖A.comp Vᗮ.subtypeL‖ := by
        rw [hvA]
        simpa [hv1] using (A.comp Vᗮ.subtypeL).le_opNorm ⟨v, hv⟩
      _ ≤ minima U₀ := by simpa [hu1, huA] using hUlower u hu
  refine ⟨minima, hminima, ⟨⟨U₀, le_antisymm (hle U₀) hge⟩, ?_⟩⟩
  rintro _ ⟨U, rfl⟩
  exact hle U

-- Lemma C.3.5.4(1) is Mathlib's IsCompactOperator.comp_clm and IsCompactOperator.clm_comp.

omit [CompleteSpace H] in
/-- An approximation number is bounded by the error of any admissible approximant. -/
private theorem approximationNumber_le_norm_sub (T S : H →L[ℂ] H) {n : ℕ}
    (hS : Module.rank ℂ S.toLinearMap.range ≤ (n : Cardinal)) :
    approximationNumber T n ≤ ‖S - T‖ :=
  csInf_le ⟨0, by rintro _ ⟨_, _, rfl⟩; exact norm_nonneg _⟩ ⟨S, hS, rfl⟩

omit [CompleteSpace H] in
/-- If an operation `S ↦ S'` on approximants does not raise the rank and multiplies the
error by at most `‖B‖`, then it bounds the approximation numbers of the new operator `A'`. -/
private theorem approximationNumber_mul_le_of_rank_le (A B : H →L[ℂ] H) {n : ℕ}
    {A' : H →L[ℂ] H} {op : (H →L[ℂ] H) → H →L[ℂ] H}
    (hrank : ∀ S, Module.rank ℂ (op S).toLinearMap.range ≤ Module.rank ℂ S.toLinearMap.range)
    (hnorm : ∀ S, ‖op S - A'‖ ≤ ‖S - A‖ * ‖B‖) :
    approximationNumber A' n ≤ approximationNumber A n * ‖B‖ := by
  rcases (norm_nonneg B).eq_or_lt with hB | hB
  · rw [← hB, mul_zero]
    have h := approximationNumber_le_norm_sub A' (op 0) (n := n)
      ((hrank 0).trans (by simp))
    simpa [← hB] using h.trans (hnorm 0)
  · rw [← div_le_iff₀ hB]
    refine le_csInf ⟨_, 0, by simp, rfl⟩ ?_
    rintro _ ⟨S, hS, rfl⟩
    rw [div_le_iff₀ hB]
    exact (approximationNumber_le_norm_sub A' (op S) ((hrank S).trans hS)).trans (hnorm S)

/-- Paper: Lemma C.3.5.4(2), p. 701. The singular value of a compact
endomorphism composed on the right by a bounded operator is bounded by the
same singular value times the norm of the right factor.
Deviation: The approximation-number index starts at zero. -/
theorem approximationNumber_mul_le_right (A B : H →L[ℂ] H) (hA : IsCompactOperator A)
    (n : ℕ) (hn : (n : Cardinal) < Module.rank ℂ H) :
    approximationNumber (A * B) n ≤ approximationNumber A n * ‖B‖ :=
  approximationNumber_mul_le_of_rank_le A B (op := fun S ↦ S * B)
    (fun S ↦ Submodule.rank_mono (LinearMap.range_comp_le_range B.toLinearMap S.toLinearMap))
    (fun S ↦ by rw [← sub_mul]; exact norm_mul_le _ _)

/-- Paper: Lemma C.3.5.4(2), p. 701. The singular value of a compact
endomorphism composed on the left by a bounded operator is bounded by the
same singular value times the norm of the left factor.
Deviation: The approximation-number index starts at zero. -/
theorem approximationNumber_mul_le_left (A B : H →L[ℂ] H) (hA : IsCompactOperator A)
    (n : ℕ) (hn : (n : Cardinal) < Module.rank ℂ H) :
    approximationNumber (B * A) n ≤ approximationNumber A n * ‖B‖ :=
  approximationNumber_mul_le_of_rank_le A B (op := fun S ↦ B * S)
    (fun S ↦ by
      change Module.rank ℂ (B.toLinearMap ∘ₗ S.toLinearMap).range ≤ _
      rw [LinearMap.range_comp]
      exact rank_map_le _ _)
    (fun S ↦ by rw [← mul_sub, mul_comm ‖S - A‖]; exact norm_mul_le _ _)

end SingularValues

section FiltrationConvergence

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [hsep : SeparableSpace H] (V : ℕ → ClosedSubmodule ℂ H) (hV : Monotone V)
  (hdense : Dense (⋃ i, (V i : Set H)))

local notation "P(" i ")" => Submodule.starProjection (V i : Submodule ℂ H)

include hsep hV hdense

-- TODO(paper-gap): The text says the projections are onto H, though their
-- codomains and the proof specify Hᵢ. The proof also needs to allow zero
-- orthogonal differences when consecutive subspaces coincide.

/-- Paper: Corollary C.3.5.5(1), p. 702. The orthogonal projections of an
increasing sequence of closed subspaces with dense union converge strongly
to the identity.
Deviation: The projections are onto the individual subspaces, as their declared
codomains and the proof specify. The sequence is indexed from zero. -/
theorem tendsto_filtration_orthogonalProjections :
    ∀ x, Tendsto (fun i ↦ (P(i)) x) atTop (𝓝 x) := by
  intro x
  refine Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp (hdense x) ε hε
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hy
  filter_upwards [eventually_ge_atTop j] with i hi
  have hyi : y ∈ (V i : Submodule ℂ H) := hV hi hj
  rw [dist_comm, (V i : Submodule ℂ H).dist_starProjection_eq_infDist]
  exact (Metric.infDist_le_dist_of_mem hyi).trans_lt hxy

-- Keep the separability hypothesis in the existing signature.
set_option linter.unusedSectionVars false in
/-- Paper: Corollary C.3.5.5(2), p. 702. Left multiplication by the
projections of a dense filtration converges in trace norm to the original operator. -/
theorem tendsto_traceNorm_filtration_orthogonalProjections_mul (T : nuclearEndomorphisms H) :
    Tendsto (fun i ↦ traceNorm
      (⟨P(i) * T.val, mul_mem_nuclearEndomorphisms_left (P(i)) T⟩ - T)) atTop (𝓝 0) := by
  let Q (i : ℕ) : H →L[ℂ] H := 1 - P(i)
  have hQ_tendsto (x : H) : Tendsto (fun i ↦ Q i x) atTop (𝓝 0) := by
    refine Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
    obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp (hdense x) ε hε
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hy
    filter_upwards [eventually_ge_atTop j] with i hi
    have hyi : y ∈ (V i : Submodule ℂ H) := hV hi hj
    change dist (x - P(i) x) 0 < ε
    rw [dist_zero_right, ← dist_eq_norm, (V i : Submodule ℂ H).dist_starProjection_eq_infDist]
    exact (Metric.infDist_le_dist_of_mem hyi).trans_lt hxy
  let A (i : ℕ) : nuclearEndomorphisms H :=
    ⟨P(i) * T.val, mul_mem_nuclearEndomorphisms_left (P(i)) T⟩ - T
  have hA (i : ℕ) : (A i).val = -(Q i * T.val) := by
    change P(i) * T.val - T.val = -((1 - P(i)) * T.val)
    rw [sub_mul, one_mul, neg_sub]
  let B (S : H →L[ℂ] H) := CFC.sqrt (star S * S)
  have hB_pos (S : H →L[ℂ] H) : (B S).IsPositive :=
    ContinuousLinearMap.nonneg_iff_isPositive.mp (CFC.sqrt_nonneg _)
  have hB_norm (S : H →L[ℂ] H) (x : H) : ‖B S x‖ = ‖S x‖ := by
    have hsq : B S * B S = star S * S := CFC.sqrt_mul_sqrt_self _ (star_mul_self_nonneg S)
    rw [(B S).apply_norm_eq_sqrt_inner_adjoint_right, S.apply_norm_eq_sqrt_inner_adjoint_right]
    change Real.sqrt (⟪x, ((B S).adjoint * B S) x⟫_ℂ).re =
      Real.sqrt (⟪x, (star S * S) x⟫_ℂ).re
    rw [(hB_pos S).isSelfAdjoint.adjoint_eq, hsq]
  -- The complementary projections bound the Gram operators, and square root preserves order.
  have hB_le (i : ℕ) : B (A i).val ≤ B T.val := by
    have hP : IsStarProjection (P(i)) := isStarProjection_starProjection
    have hQ : IsStarProjection (Q i) := hP.one_sub
    have hQ_le : Q i ≤ 1 := sub_le_self _ hP.nonneg
    apply CFC.monotone_sqrt
    calc
      star (A i).val * (A i).val = star T.val * Q i * T.val := by
        simp only [hA, star_neg, neg_mul_neg, star_mul, hQ.isSelfAdjoint.star_eq, mul_assoc]
        rw [← mul_assoc (Q i), hQ.isIdempotentElem.eq]
      _ ≤ star T.val * T.val := by
        simpa only [mul_one] using star_left_conjugate_le_conjugate hQ_le T.val
  let b := (exists_hilbertBasis (𝕜 := ℂ) (E := H)).choose_spec.choose
  let d (S : H →L[ℂ] H) i : ℝ := (⟪b i, B S (b i)⟫_ℂ).re
  have htrace (S : nuclearEndomorphisms H) : HasSum (d S.val) (traceNorm S) :=
    hasSum_traceNorm_diagonal b S
  have hd_nonneg (S : H →L[ℂ] H) i : 0 ≤ d S i :=
    (hB_pos S).re_inner_nonneg_right (b i)
  have hd_bound (i : ℕ) j : ‖d (A i).val j‖ ≤ d T.val j := by
    rw [Real.norm_of_nonneg (hd_nonneg _ _)]
    have h := (ContinuousLinearMap.le_def.mp (hB_le i)).re_inner_nonneg_right (b j)
    change 0 ≤ (⟪b j, (B T.val - B (A i).val) (b j)⟫_ℂ).re at h
    simpa only [sub_apply, inner_sub_right, Complex.sub_re, sub_nonneg] using h
  have hd_tendsto (j) : Tendsto (fun i ↦ d (A i).val j) atTop (𝓝 0) := by
    refine squeeze_zero (g := fun i ↦ ‖b j‖ * ‖Q i (T.val (b j))‖)
      (fun i ↦ hd_nonneg _ _) (fun i ↦ ?_) ?_
    · calc
        d (A i).val j ≤ ‖b j‖ * ‖B (A i).val (b j)‖ :=
          (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
        _ = ‖b j‖ * ‖Q i (T.val (b j))‖ := by
          rw [hB_norm, hA, neg_apply, norm_neg]
          rfl
    · simpa only [norm_zero, mul_zero] using
        tendsto_const_nhds.mul (hQ_tendsto (T.val (b j))).norm
  have hsum (i : ℕ) : (∑' j, d (A i).val j) = traceNorm (A i) := (htrace (A i)).tsum_eq
  simpa only [tsum_zero, hsum] using
    tendsto_tsum_of_dominated_convergence (g := fun _ ↦ 0)
      (htrace T).summable hd_tendsto (Eventually.of_forall hd_bound)

omit hsep hV hdense in
open scoped CStarAlgebra in
/-- The trace norm of a nuclear rank-one series is bounded by the sum of its rank-one norms. -/
private theorem traceNorm_le_of_rankOne_series (A : nuclearEndomorphisms H)
    (φ : ℕ → StrongDual ℂ H) (y : ℕ → H)
    (hs : Summable (fun n ↦ ‖φ n‖ * ‖y n‖))
    (hA : ∀ x, HasSum (fun n ↦ φ n x • y n) (A.val x)) :
    traceNorm A ≤ ∑' n, ‖φ n‖ * ‖y n‖ := by
  let R (n : ℕ) : nuclearEndomorphisms H :=
    ⟨(φ n).smulRight (y n), smulRight_mem_nuclearEndomorphisms (φ n) (y n)⟩
  have hR : Summable (fun n ↦ ‖(R n).val‖) := by
    simpa only [R, ContinuousLinearMap.norm_smulRight_apply] using hs
  have hsum : HasSum (fun n ↦ (R n).val) A.val := by
    obtain ⟨B, hB⟩ := hR.of_norm
    have hBA : B = A.val := by
      ext x
      exact ((ContinuousLinearMap.apply ℂ H x).hasSum hB).unique (hA x)
    rwa [hBA] at hB
  have hfin : Tendsto (fun s : Finset ℕ ↦ CFC.abs (∑ n ∈ s, R n).val) atTop
      (𝓝 (CFC.abs A.val)) := by
    simpa only [Submodule.coe_sum, Function.comp_def, SummationFilter.unconditional_filter] using
      (CFC.continuous_abs.tendsto A.val).comp hsum
  -- Pass to the limit in each finite sum of the nonnegative trace diagonal.
  obtain ⟨ι, b, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  let diag (B : H →L[ℂ] H) (i : ι) : ℝ := (⟪b i, B (b i)⟫_ℂ).re
  have hdiag (X : nuclearEndomorphisms H) :
      HasSum (diag (CFC.abs X.val)) (traceNorm X) := hasSum_traceNorm_diagonal b X
  have hnonneg (B : H →L[ℂ] H) (i : ι) : 0 ≤ diag (CFC.abs B) i :=
    (ContinuousLinearMap.nonneg_iff_isPositive.mp (CFC.abs_nonneg B)).re_inner_nonneg_right _
  refine le_of_tendsto' (hdiag A) fun t ↦ ?_
  have hcont : Continuous (fun B : H →L[ℂ] H ↦ ∑ i ∈ t, diag B i) := by
    unfold diag
    fun_prop
  refine le_of_tendsto' ((hcont.tendsto (CFC.abs A.val)).comp hfin) fun s ↦ ?_
  calc
    ∑ i ∈ t, diag (CFC.abs (∑ n ∈ s, R n).val) i ≤ traceNorm (∑ n ∈ s, R n) :=
      sum_le_hasSum t (fun i _ ↦ hnonneg _ i) (hdiag _)
    _ ≤ ∑ n ∈ s, ‖φ n‖ * ‖y n‖ := by
      let : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
      have hcore := traceNorm_normedSpaceCore (H := H)
      have hzero : traceNorm (0 : nuclearEndomorphisms H) = 0 :=
        (hcore.norm_eq_zero_iff 0).mpr rfl
      exact (s.le_sum_of_subadditive traceNorm hzero.le hcore.toCore.norm_triangle R).trans_eq
        (Finset.sum_congr rfl fun n _ ↦ traceNorm_smulRight _ _)
    _ ≤ ∑' n, ‖φ n‖ * ‖y n‖ :=
      hs.sum_le_tsum s (fun _ _ ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _))

set_option linter.unusedSectionVars false in
open InnerProductSpace in
/-- Paper: Corollary C.3.5.5(2), p. 702. Right multiplication by the
projections of a dense filtration converges in trace norm to the original operator. -/
theorem tendsto_traceNorm_mul_filtration_orthogonalProjections (T : nuclearEndomorphisms H) :
    Tendsto (fun i ↦ traceNorm
      (⟨T.val * P(i), mul_mem_nuclearEndomorphisms_right (P(i)) T⟩ - T)) atTop (𝓝 0) := by
  let Q (i : ℕ) : H →L[ℂ] H := P(i) - 1
  have hQ (x : H) : Tendsto (fun i ↦ Q i x) atTop (𝓝 0) := by
    have hd : Dense ((⨆ i, (V i : Submodule ℂ H) : Submodule ℂ H) : Set H) :=
      hdense.mono (iUnion_subset fun i ↦ le_iSup (fun j ↦ (V j : Submodule ℂ H)) i)
    have h := Submodule.starProjection_tendsto_self (fun i ↦ (V i : Submodule ℂ H))
      (fun _ _ hij ↦ ClosedSubmodule.toSubmodule_le_toSubmodule.mpr (hV hij)) x
      (Submodule.dense_iff_topologicalClosure_eq_top.mp hd).ge
    simpa [Q] using h.sub tendsto_const_nhds (b := x)
  have hQa (i : ℕ) : (Q i).adjoint = Q i :=
    ((isSelfAdjoint_starProjection (V i : Submodule ℂ H)).sub
      (IsSelfAdjoint.one (H →L[ℂ] H))).adjoint_eq
  have hQc (i : ℕ) (x : H) : ‖Q i x‖ ≤ ‖x‖ := by
    have hP : IsStarProjection (P(i)) := isStarProjection_starProjection
    have h := hP.one_sub.norm_le _
    rw [norm_sub_rev] at h
    simpa only [one_mul] using (ContinuousLinearMap.opNorm_le_iff zero_le_one).mp h x
  obtain ⟨c, φ, y, hc, hφ, hy, hT⟩ := (isNuclearOperator_iff_isBanachNuclear T.val).mp T.property
  -- Since Q i is self-adjoint, right composition applies Q i to each Riesz vector.
  let u (n : ℕ) := (toDual ℂ H).symm (φ n)
  have hu (n : ℕ) : ‖u n‖ = ‖φ n‖ := (toDual ℂ H).symm.norm_map _
  let cost (i n : ℕ) := ‖c n‖ * (‖Q i (u n)‖ * ‖y n‖)
  let bound (n : ℕ) := ‖c n‖ * (‖φ n‖ * ‖y n‖)
  have hcost_nonneg (i n : ℕ) : 0 ≤ cost i n := by dsimp [cost]; positivity
  have hbound (i n : ℕ) : ‖cost i n‖ ≤ bound n := by
    rw [Real.norm_of_nonneg (hcost_nonneg i n)]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right ((hQc i (u n)).trans_eq (hu n)) (norm_nonneg _))
      (norm_nonneg _)
  have hs : Summable bound := by
    obtain ⟨C, hC, hφC⟩ := (Metric.isBounded_range_of_tendsto φ hφ).exists_pos_norm_le
    obtain ⟨D, _, hyD⟩ := (Metric.isBounded_range_of_tendsto y hy).exists_pos_norm_le
    refine (hc.mul_right (C * D)).of_norm_bounded fun n ↦ ?_
    rw [Real.norm_of_nonneg (by dsimp [bound]; positivity)]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul (hφC _ (mem_range_self n)) (hyD _ (mem_range_self n))
        (norm_nonneg _) hC.le) (norm_nonneg _)
  have hlim : Tendsto (fun i ↦ ∑' n, cost i n) atTop (𝓝 0) := by
    have hterm (n : ℕ) : Tendsto (fun i ↦ cost i n) atTop (𝓝 0) := by
      simpa [cost] using ((hQ (u n)).norm.mul_const ‖y n‖).const_mul ‖c n‖
    simpa only [tsum_zero] using
      tendsto_tsum_of_dominated_convergence hs hterm (Eventually.of_forall hbound)
  let : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
  refine squeeze_zero (fun _ ↦ (traceNorm_normedSpaceCore (H := H)).toCore.norm_nonneg _)
    ?_ hlim
  intro i
  let ψ (n : ℕ) : StrongDual ℂ H := c n • innerSL ℂ (Q i (u n))
  have hψ (n : ℕ) : ‖ψ n‖ * ‖y n‖ = cost i n := by
    simp only [ψ, cost, norm_smul, innerSL_apply_norm, mul_assoc]
  simp_rw [← hψ]
  refine traceNorm_le_of_rankOne_series _ ψ y
    ((hs.of_norm_bounded (hbound i)).congr fun n ↦ (hψ n).symm) fun x ↦ ?_
  have heval (n : ℕ) : ψ n x = c n * φ n (Q i x) := by
    have hinner := (Q i).adjoint_inner_left x (u n)
    rw [hQa] at hinner
    simp only [ψ, smul_apply, smul_eq_mul, innerSL_apply_apply, hinner, u, toDual_symm_apply]
  simpa [heval, Q, map_sub, mul_apply_eq_comp] using hT (Q i x)

/-- Paper: Corollary C.3.5.5(3), p. 702. The traces of the left-projected
operators converge to the trace of the original operator. -/
theorem tendsto_hilbertTrace_filtration_orthogonalProjections_mul (T : nuclearEndomorphisms H) :
    Tendsto (fun i ↦ hilbertTrace
      ⟨P(i) * T.val, mul_mem_nuclearEndomorphisms_left (P(i)) T⟩)
      atTop (𝓝 (hilbertTrace T)) := by
  obtain ⟨tr, htr⟩ := hilbertTrace_linear (H := H)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [← htr, ← map_sub]
  simp only [htr]
  exact squeeze_zero (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_hilbertTrace_le _)
    (tendsto_traceNorm_filtration_orthogonalProjections_mul V hV hdense T)

/-- Paper: Corollary C.3.5.5(3), p. 702. The traces of the right-projected
operators converge to the trace of the original operator. -/
theorem tendsto_hilbertTrace_mul_filtration_orthogonalProjections (T : nuclearEndomorphisms H) :
    Tendsto (fun i ↦ hilbertTrace
      ⟨T.val * P(i), mul_mem_nuclearEndomorphisms_right (P(i)) T⟩)
      atTop (𝓝 (hilbertTrace T)) := by
  obtain ⟨tr, htr⟩ := hilbertTrace_linear (H := H)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [← htr, ← map_sub]
  simp only [htr]
  exact squeeze_zero (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_hilbertTrace_le _)
    (tendsto_traceNorm_mul_filtration_orthogonalProjections V hV hdense T)

end FiltrationConvergence

section SchattenClasses

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

-- TODO(paper-gap): Theorem C.3.6.1(2) requires infinite orthonormal
-- sequences even for finite-rank operators, such as the identity on ℂ.

/-- Paper: Theorem C.3.6.1(2), p. 703. A singular expansion has decreasing
nonnegative coefficients tending to zero and gives a pointwise sum of
rank-one terms from two orthonormal families.
Deviation: The orthonormal families are indexed by the nonzero coefficients.
Mathlib's inner product is linear in its second argument. -/
structure SingularExpansion (T : E →L[ℂ] F) where
  coeff : ℕ → ℝ≥0
  antitone_coeff : Antitone coeff
  tendsto_coeff : Tendsto coeff atTop (𝓝 0)
  source : {n // coeff n ≠ 0} → E
  target : {n // coeff n ≠ 0} → F
  orthonormal_source : Orthonormal ℂ source
  orthonormal_target : Orthonormal ℂ target
  hasSum_apply : ∀ x, HasSum
    (fun n : {n // coeff n ≠ 0} ↦ ((coeff n : ℝ) * ⟪source n, x⟫_ℂ) • target n) (T x)

/-- Paper: Theorem C.3.6.1(2), p. 703. A rank-one map from a pair of unit
vectors has a singular expansion with first coefficient one and all later
coefficients zero.
Deviation: This checks the vectors and coefficient normalization for a rank-one map. -/
theorem singularExpansion_smulRight (e : E) (f : F) (he : ‖e‖ = 1) (hf : ‖f‖ = 1) :
    ∃ d : SingularExpansion ((innerSL ℂ e).smulRight f),
      d.coeff 0 = 1 ∧ ∀ n, d.coeff (n + 1) = 0 := by
  let c : ℕ → ℝ≥0 := fun n ↦ if n = 0 then 1 else 0
  have hc (n : {n // c n ≠ 0}) : n.1 = 0 := by
    by_contra h
    exact n.2 (by simp [c, h])
  have : Subsingleton {n // c n ≠ 0} :=
    ⟨fun a b ↦ Subtype.ext ((hc a).trans (hc b).symm)⟩
  refine ⟨{
    coeff := c
    antitone_coeff := ?_
    tendsto_coeff := ?_
    source := fun _ ↦ e
    target := fun _ ↦ f
    orthonormal_source := orthonormal_subsingleton_iff.mpr fun _ ↦ he
    orthonormal_target := orthonormal_subsingleton_iff.mpr fun _ ↦ hf
    hasSum_apply := ?_ }, ?_, fun n ↦ ?_⟩
  · intro m n hmn
    by_cases hn : n = 0
    · subst hn
      obtain rfl : m = 0 := Nat.le_zero.mp hmn
      exact le_rfl
    · simp [c, hn]
  · exact tendsto_const_nhds.congr'
      (eventually_atTop.mpr ⟨1, fun n hn ↦ by simp [c, Nat.pos_iff_ne_zero.mp hn]⟩)
  · intro x
    convert hasSum_single (⟨0, by simp [c]⟩ : {n // c n ≠ 0})
      (fun b hb ↦ absurd (Subsingleton.elim _ _) hb) using 1
    simp [c]
  · simp [c]
  · simp [c]

section

open InnerProductSpace

omit [CompleteSpace E] [CompleteSpace F] in
/-- Bessel's inequality bounds the action of a finite sum of singular terms by
any nonnegative upper bound for its coefficients times the norm of the input. -/
private theorem norm_sum_singularTerms_le (c : ℕ → ℝ≥0)
    {e : {n // c n ≠ 0} → E} {f : {n // c n ≠ 0} → F}
    (he : Orthonormal ℂ e) (hf : Orthonormal ℂ f)
    (s : Finset {n // c n ≠ 0}) {r : ℝ} (hr : 0 ≤ r)
    (hs : ∀ i ∈ s, (c i : ℝ) ≤ r) (x : E) :
    ‖∑ i ∈ s, ((c i : ℝ) * ⟪e i, x⟫_ℂ) • f i‖ ≤ r * ‖x‖ := by
  let a (i : {n // c n ≠ 0}) : ℂ := (c i : ℝ) * ⟪e i, x⟫_ℂ
  change ‖∑ i ∈ s, a i • f i‖ ≤ _
  apply le_of_sq_le_sq _ (mul_nonneg hr (norm_nonneg x))
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), hf.inner_sum a a, map_sum, mul_pow]
  calc
    ∑ i ∈ s, RCLike.re (starRingEnd ℂ (a i) * a i) ≤ ∑ i ∈ s, r ^ 2 * ‖⟪e i, x⟫_ℂ‖ ^ 2 := by
      refine Finset.sum_le_sum fun i hi ↦ ?_
      rw [RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]
      have hi0 : 0 ≤ (c i : ℝ) := (c i).2
      simp only [a, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hi0, mul_pow]
      exact mul_le_mul_of_nonneg_right
        ((sq_le_sq₀ (c i).2 hr).mpr (hs i hi)) (sq_nonneg _)
    _ ≤ r ^ 2 * ‖x‖ ^ 2 := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (he.sum_inner_products_le x) (sq_nonneg _)

omit [CompleteSpace E] in
/-- The rank-one terms from two orthonormal families and coefficients tending to zero
are summable in operator norm. -/
private theorem summable_singularTerms (c : ℕ → ℝ≥0) (hc : Tendsto c atTop (𝓝 0))
    {e : {n // c n ≠ 0} → E} {f : {n // c n ≠ 0} → F}
    (he : Orthonormal ℂ e) (hf : Orthonormal ℂ f) :
    Summable (fun i : {n // c n ≠ 0} ↦ ((c i : ℝ) : ℂ) • rankOne ℂ (f i) (e i)) := by
  classical
  let A (i : {n // c n ≠ 0}) : E →L[ℂ] F := ((c i : ℝ) : ℂ) • rankOne ℂ (f i) (e i)
  have hbound (s : Finset {n // c n ≠ 0}) {r : ℝ} (hr : 0 ≤ r)
      (hs : ∀ i ∈ s, (c i : ℝ) ≤ r) : ‖∑ i ∈ s, A i‖ ≤ r := by
    refine ContinuousLinearMap.opNorm_le_bound _ hr fun x ↦ ?_
    simpa only [A, sum_apply, smul_apply, rankOne_apply, smul_smul] using
      norm_sum_singularTerms_le c he hf s hr hs x
  change Summable A
  rw [summable_iff_cauchySeq_finset, NormedAddCommGroup.cauchySeq_iff]
  intro ε hε
  have hc' := NNReal.tendsto_coe.mpr hc
  rw [NNReal.coe_zero, Metric.tendsto_atTop] at hc'
  obtain ⟨N, hN⟩ := hc' (ε / 3) (by positivity)
  let initial := (Finset.range N).subtype (fun n ↦ c n ≠ 0)
  have htail (s : Finset {n // c n ≠ 0}) (hs : Disjoint s initial) :
      ‖∑ i ∈ s, A i‖ ≤ ε / 3 := by
    refine hbound s (by positivity) fun i hi ↦ ?_
    have hiN : N ≤ i.val := by
      by_contra! h
      exact (Finset.disjoint_left.mp hs hi) (Finset.mem_subtype.mpr (Finset.mem_range.mpr h))
    have hi0 : 0 ≤ (c i : ℝ) := (c i).2
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hi0] using (hN i hiN).le
  refine ⟨initial, fun s hs t ht ↦ ?_⟩
  rw [neg_add_eq_sub, ← Finset.sum_sdiff_sub_sum_sdiff]
  have hts := htail (t \ s) (disjoint_sdiff_self_left.mono_right hs)
  have hst := htail (s \ t) (disjoint_sdiff_self_left.mono_right ht)
  exact (norm_sub_le _ _).trans_lt (by linarith)

/-- Successive norm-maximizing singular vectors of a compact operator yield a singular
expansion. Each step removes a rank-one term, and compactness forces the residual norms
to tend to zero. -/
private theorem nonempty_singularExpansion_of_isCompactOperator (T : E →L[ℂ] F)
    (hT : IsCompactOperator T) : Nonempty (SingularExpansion T) := by
  classical
  let CompactMap := {R : E →L[ℂ] F // IsCompactOperator R}
  have hexists (S : CompactMap) : ∃ x : E, (S.val ≠ 0 → ‖x‖ = 1) ∧
      (S.val = 0 → x = 0) ∧ ‖S.val x‖ = ‖S.val‖ ∧
      S.val.adjoint (S.val x) = (↑‖S.val‖ ^ 2 : ℂ) • x := by
    by_cases hS : S.val = 0
    · exact ⟨0, fun h ↦ (h hS).elim, fun _ ↦ rfl, by simp [hS], by simp [hS]⟩
    have : Nontrivial E := not_subsingleton_iff_nontrivial.mp fun h ↦
      hS (ContinuousLinearMap.ext fun x ↦ by rw [h.elim x 0]; simp)
    obtain ⟨x, hx, hnorm, heig⟩ :=
      exists_unit_norm_eq_opNorm_of_isCompactOperator S.val S.property
    exact ⟨x, fun _ ↦ hx, fun h ↦ (hS h).elim, hnorm, heig⟩
  choose vector hunit hzero hnorm heig using hexists
  let P (x : E) : E →L[ℂ] E := 1 - rankOne ℂ x x
  let residual : ℕ → CompactMap :=
    Nat.rec ⟨T, hT⟩ (fun _ S ↦ ⟨S.val ∘L P (vector S), S.property.comp_clm _⟩)
  let R (n : ℕ) : E →L[ℂ] F := (residual n).val
  let e (n : ℕ) : E := vector (residual n)
  let y (n : ℕ) : F := R n (e n)
  let A (n : ℕ) : E →L[ℂ] F := rankOne ℂ (y n) (e n)
  have hstep (n : ℕ) : R (n + 1) = R n ∘L P (e n) := rfl
  have hsub (n : ℕ) : R (n + 1) = R n - A n := by
    rw [hstep]
    simp [P, A, y, ContinuousLinearMap.comp_sub, comp_rankOne,
      show (1 : E →L[ℂ] E) = ContinuousLinearMap.id ℂ E from rfl]
  have hproj (n : ℕ) : IsStarProjection (P (e n)) := by
    by_cases hn : R n = 0
    · have hz : e n = 0 := hzero (residual n) hn
      simp [P, hz]
    · exact (isStarProjection_rankOne_self (hunit (residual n) hn)).one_sub
  have hproj_zero (n : ℕ) : P (e n) (e n) = 0 := by
    by_cases hn : R n = 0
    · rw [show e n = 0 from hzero (residual n) hn, map_zero]
    · have hn' : ‖e n‖ = 1 := hunit (residual n) hn
      simp [P, inner_self_eq_norm_sq_to_K, hn']
  have horth_source (n : ℕ) (z : E) (hz : R n z = 0) : ⟪e n, z⟫_ℂ = 0 := by
    by_cases hn : R n = 0
    · simp [show e n = 0 from hzero (residual n) hn]
    have h := (R n).adjoint_inner_left z (y n)
    change ⟪(R n).adjoint (R n (e n)), z⟫_ℂ = _ at h
    rw [heig (residual n), inner_smul_left, hz, inner_zero_right] at h
    have hn' : (↑‖R n‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hn)
    exact (mul_eq_zero.mp h).resolve_left ((map_ne_zero (starRingEnd ℂ)).mpr (pow_ne_zero _ hn'))
  -- Each residual and its adjoint annihilate the vectors already selected.
  have hkill (n : ℕ) : ∀ i < n, R n (e i) = 0 ∧ (R n).adjoint (y i) = 0 := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hadj : (R (n + 1)).adjoint = P (e n) ∘L (R n).adjoint := by
        rw [hstep, ContinuousLinearMap.adjoint_comp, (hproj n).isSelfAdjoint.adjoint_eq]
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hin
      · obtain ⟨hRi, hRai⟩ := ih i hi
        constructor
        · simp [hsub, A, hRi, horth_source n (e i) hRi]
        · simp [hadj, hRai]
      · subst i
        constructor
        · simp [hstep, hproj_zero]
        · rw [hadj, ContinuousLinearMap.comp_apply]
          change P (e n) ((R n).adjoint (R n (e n))) = 0
          rw [heig (residual n), map_smul, hproj_zero, smul_zero]
  have hsource (i j : ℕ) (hij : i < j) : ⟪e i, e j⟫_ℂ = 0 :=
    inner_eq_zero_symm.mp (horth_source j (e i) (hkill j i hij).1)
  have htarget (i j : ℕ) (hij : i < j) : ⟪y i, y j⟫_ℂ = 0 := by
    change ⟪y i, R j (e j)⟫_ℂ = 0
    rw [← (R j).adjoint_inner_left, (hkill j i hij).2, inner_zero_left]
  have hpartial (n : ℕ) : ∑ i ∈ Finset.range n, A i = T - R n := by
    induction n with
    | zero => simp [show R 0 = T from rfl]
    | succ n ih => rw [Finset.sum_range_succ, ih, hsub]; abel
  have hTy (n : ℕ) : T (e n) = y n := by
    have hz : (∑ i ∈ Finset.range n, A i) (e n) = 0 := by
      rw [sum_apply]
      exact Finset.sum_eq_zero fun i hi ↦ by simp [A, hsource i n (Finset.mem_range.mp hi)]
    rw [hpartial, sub_apply, sub_eq_zero] at hz
    exact hz
  have hanti : Antitone (fun n ↦ ‖R n‖) := by
    refine antitone_nat_of_succ_le fun n ↦ ?_
    rw [hstep]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_of_le_one_right (norm_nonneg _) ((hproj n).norm_le _))
  -- Consecutive terms of a convergent subsequence have vanishing distance,
  -- which bounds their norms by orthogonality.
  have hlim : Tendsto (fun n ↦ ‖R n‖) atTop (𝓝 0) := by
    obtain ⟨z, _, φ, hφ, hz⟩ :=
      (hT.isCompact_closure_image_closedBall 1).tendsto_subseq (x := y) fun n ↦ by
        refine subset_closure ⟨e n, ?_, hTy n⟩
        rw [Metric.mem_closedBall, dist_zero_right]
        by_cases hn : R n = 0
        · simp [show e n = 0 from hzero (residual n) hn]
        · exact (hunit (residual n) hn).le
    have hdist : Tendsto (fun n ↦ ‖y (φ n) - y (φ (n + 1))‖) atTop (𝓝 0) := by
      have h := (hz.sub (hz.comp (tendsto_add_atTop_nat 1))).norm
      simpa [Function.comp_def] using h
    apply (tendsto_iff_tendsto_subseq_of_antitone hanti hφ.tendsto_atTop).mpr
    refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ ?_) hdist
    change ‖R (φ n)‖ ≤ ‖y (φ n) - y (φ (n + 1))‖
    rw [← hnorm (residual (φ n))]
    apply le_of_sq_le_sq _ (norm_nonneg _)
    change ‖y (φ n)‖ ^ 2 ≤ _
    rw [@norm_sub_sq ℂ, htarget _ _ (hφ (Nat.lt_succ_self n))]
    simp
  let c (n : ℕ) : ℝ≥0 := ‖R n‖₊
  let f (i : {n // c n ≠ 0}) : F := (↑(c i : ℝ) : ℂ)⁻¹ • y i
  have hc : Tendsto c atTop (𝓝 0) := NNReal.tendsto_coe.mp (by simpa [c] using hlim)
  have hcn (i : {n // c n ≠ 0}) : ‖R i‖ ≠ 0 :=
    fun h ↦ i.property (NNReal.eq h)
  have he : Orthonormal ℂ (fun i : {n // c n ≠ 0} ↦ e i) := by
    refine ⟨fun i ↦ hunit (residual i) (norm_ne_zero_iff.mp (hcn i)), ?_⟩
    intro i j hij
    rcases lt_or_gt_of_ne (fun h : i.val = j.val ↦ hij (Subtype.ext h)) with h | h
    · exact hsource i j h
    · exact inner_eq_zero_symm.mp (hsource j i h)
  have hf : Orthonormal ℂ f := by
    refine ⟨fun i ↦ ?_, ?_⟩
    · have hy : ‖y i‖ = ‖R i‖ := hnorm (residual i)
      change ‖(↑‖R i‖ : ℂ)⁻¹ • y i‖ = 1
      rw [← hy]
      exact norm_smul_inv_norm (norm_ne_zero_iff.mp (hy.trans_ne (hcn i)))
    · intro i j hij
      have hz : ⟪y i, y j⟫_ℂ = 0 := by
        rcases lt_or_gt_of_ne (fun h : i.val = j.val ↦ hij (Subtype.ext h)) with h | h
        · exact htarget i j h
        · exact inner_eq_zero_symm.mp (htarget j i h)
      simp [f, inner_smul_left, inner_smul_right, hz]
  have hA (i : {n // c n ≠ 0}) : ((c i : ℝ) : ℂ) • rankOne ℂ (f i) (e i) = A i := by
    ext x
    have hci : ((c i : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hcn i)
    simp only [smul_apply, rankOne_apply, f, smul_smul, A]
    rw [mul_left_comm, mul_inv_cancel₀ hci, mul_one]
  have hsupp : Function.support A ⊆ {n | c n ≠ 0} := by
    intro n hn h
    have hz : R n = 0 := norm_eq_zero.mp (congrArg NNReal.toReal h)
    exact hn (by simp [A, y, hz])
  have hs : Summable (A ∘ (Subtype.val : {n // c n ≠ 0} → ℕ)) :=
    (summable_singularTerms c hc he hf).congr hA
  have hfull := (hasSum_subtype_iff_of_support_subset hsupp).mp hs.hasSum
  have hnat : Tendsto (fun n ↦ ∑ i ∈ Finset.range n, A i) atTop (𝓝 T) := by
    refine tendsto_iff_norm_sub_tendsto_zero.mpr (hlim.congr fun n ↦ ?_)
    rw [hpartial, sub_right_comm, sub_self, zero_sub, norm_neg]
  have hsum : HasSum (A ∘ (Subtype.val : {n // c n ≠ 0} → ℕ)) T :=
    (tendsto_nhds_unique hfull.tendsto_sum_nat hnat) ▸ hs.hasSum
  refine ⟨⟨c, hanti, hc, (fun i ↦ e i), f, he, hf, fun x ↦ ?_⟩⟩
  have hmapped := hsum.map (ContinuousLinearMap.apply ℂ F x)
    (ContinuousLinearMap.apply ℂ F x).continuous
  refine hmapped.congr_fun fun i ↦ ?_
  change _ = A i x
  rw [← hA i]
  simp only [smul_apply, rankOne_apply, smul_smul]

/-- Paper: Theorem C.3.6.1(1)–(2), p. 703. A bounded operator is compact
exactly when it admits a singular expansion.
Deviation: The expansion uses orthonormal vectors only for nonzero coefficients. -/
theorem isCompactOperator_iff_nonempty_singularExpansion (T : E →L[ℂ] F) :
    IsCompactOperator T ↔ Nonempty (SingularExpansion T) := by
  refine ⟨nonempty_singularExpansion_of_isCompactOperator T, ?_⟩
  rintro ⟨d⟩
  let A (i : {n // d.coeff n ≠ 0}) : E →L[ℂ] F :=
    ((d.coeff i : ℝ) : ℂ) • rankOne ℂ (d.target i) (d.source i)
  have hs : Summable A :=
    summable_singularTerms d.coeff d.tendsto_coeff d.orthonormal_source d.orthonormal_target
  have hT : (∑' i, A i) = T := by
    ext x
    have hmapped := hs.hasSum.map (ContinuousLinearMap.apply ℂ F x)
      (ContinuousLinearMap.apply ℂ F x).continuous
    apply hmapped.unique
    refine (d.hasSum_apply x).congr_fun fun i ↦ ?_
    change A i x = _
    simp only [A, smul_apply, rankOne_apply, smul_smul]
  have hc (i : {n // d.coeff n ≠ 0}) : IsCompactOperator (A i) := by
    change IsCompactOperator (((d.coeff i : ℝ) : ℂ) • rankOne ℂ (d.target i) (d.source i))
    rw [rankOne_def']
    exact ((isCompactOperator_of_locallyCompactSpace_rng
      (ContinuousLinearMap.toSpanSingleton ℂ (d.target i))).comp_clm
        (innerSL ℂ (d.source i))).smul _
  rw [← hT]
  apply isCompactOperator_of_tendsto hs.hasSum
  exact Eventually.of_forall fun s ↦ (compactOperator (RingHom.id ℂ) E F).sum_mem
    (fun i _ ↦ hc i)

end

omit [CompleteSpace E] [CompleteSpace F] in
/-- After including every term with index below `N`, the operator-norm error
of the finite sum is bounded by the coefficient at `N`. -/
private theorem SingularExpansion.norm_sub_sum_le_coeff {T : E →L[ℂ] F}
    (d : SingularExpansion T) (N : ℕ) (s : Finset {n // d.coeff n ≠ 0})
    (hs : ∀ i : {n // d.coeff n ≠ 0}, (i : ℕ) < N → i ∈ s) :
    ‖T - ∑ i ∈ s, ((d.coeff i : ℝ) : ℂ) •
      (innerSL ℂ (d.source i)).smulRight (d.target i)‖ ≤ (d.coeff N : ℝ) := by
  classical
  let ι := {n // d.coeff n ≠ 0}
  let A (i : ι) : E →L[ℂ] F :=
    ((d.coeff i : ℝ) : ℂ) • (innerSL ℂ (d.source i)).smulRight (d.target i)
  let S (s : Finset ι) := ∑ i ∈ s, A i
  have happly (s : Finset ι) (x : E) :
      S s x = ∑ i ∈ s, (((d.coeff i : ℝ) : ℂ) * ⟪d.source i, x⟫_ℂ) • d.target i := by
    simp only [S, A, sum_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_smul]
  have hpointwise (x : E) : Tendsto (fun s ↦ S s x) atTop (𝓝 (T x)) := by
    simpa only [HasSum, SummationFilter.unconditional_filter, happly] using d.hasSum_apply x
  let c : ℝ := d.coeff N
  have hc : 0 ≤ c := NNReal.coe_nonneg _
  -- Use Pythagoras in the target and Bessel's inequality in the source.
  have htail (u : Finset ι) (hu : ∀ i ∈ u, N ≤ (i : ℕ)) (x : E) :
      ‖S u x‖ ≤ c * ‖x‖ := by
    apply le_of_sq_le_sq _ (mul_nonneg hc (norm_nonneg _))
    rw [happly, mul_pow]
    calc
      _ = ∑ i ∈ u, ‖((d.coeff i : ℝ) : ℂ) * ⟪d.source i, x⟫_ℂ‖ ^ 2 := by
        simpa only [LinearIsometry.toSpanSingleton_apply] using
          d.orthonormal_target.orthogonalFamily.norm_sum
            (fun i ↦ ((d.coeff i : ℝ) : ℂ) * ⟪d.source i, x⟫_ℂ) u
      _ ≤ ∑ i ∈ u, c ^ 2 * ‖⟪d.source i, x⟫_ℂ‖ ^ 2 := by
        refine Finset.sum_le_sum fun i hi ↦ ?_
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (NNReal.coe_nonneg _), mul_pow]
        exact mul_le_mul_of_nonneg_right
          ((sq_le_sq₀ (NNReal.coe_nonneg _) hc).mpr (NNReal.coe_le_coe.mpr
            (d.antitone_coeff (hu i hi)))) (sq_nonneg _)
      _ ≤ c ^ 2 * ‖x‖ ^ 2 := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (d.orthonormal_source.sum_inner_products_le x)
          (sq_nonneg c)
  change ‖T - S s‖ ≤ c
  refine ContinuousLinearMap.opNorm_le_bound _ hc fun x ↦ ?_
  -- Pass the finite tail bound to the pointwise limit.
  have hlim : Tendsto (fun t ↦ ‖S t x - S s x‖) atTop (𝓝 ‖(T - S s) x‖) := by
    simpa only [sub_apply] using
      ((hpointwise x).sub tendsto_const_nhds).norm
  apply le_of_tendsto hlim
  filter_upwards [eventually_ge_atTop s] with t ht
  have hdiff : S t - S s = S (t \ s) := by
    have hsum : S (t \ s) + S s = S t := Finset.sum_sdiff ht
    exact (eq_sub_of_add_eq hsum).symm
  rw [← sub_apply, hdiff]
  refine htail _ (fun i hi ↦ ?_) x
  exact Nat.le_of_not_gt fun hiN ↦ (Finset.mem_sdiff.mp hi).2 (hs i hiN)

-- Keep the completeness hypotheses in the existing signature.
set_option linter.unusedSectionVars false in
/-- Paper: Theorem C.3.6.1, p. 703. The series of rank-one maps in a
singular expansion converges in operator norm. -/
theorem SingularExpansion.hasSum_opNorm {T : E →L[ℂ] F} (d : SingularExpansion T) :
    HasSum (fun n : {n // d.coeff n ≠ 0} ↦
      ((d.coeff n : ℝ) : ℂ) • (innerSL ℂ (d.source n)).smulRight (d.target n)) T := by
  classical
  change Tendsto (fun s : Finset {n // d.coeff n ≠ 0} ↦
    ∑ i ∈ s, ((d.coeff i : ℝ) : ℂ) •
      (innerSL ℂ (d.source i)).smulRight (d.target i)) atTop (𝓝 T)
  refine Metric.tendsto_atTop.mpr fun ε hε ↦ ?_
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp d.tendsto_coeff ε hε
  have hcoeff : (d.coeff N : ℝ) < ε := by
    simpa only [NNReal.dist_eq, NNReal.coe_zero, sub_zero, abs_of_nonneg (NNReal.coe_nonneg _)]
      using hN N le_rfl
  refine ⟨(Finset.range N).subtype (fun n ↦ d.coeff n ≠ 0), fun s hs ↦ ?_⟩
  rw [dist_eq_norm, norm_sub_rev]
  exact (d.norm_sub_sum_le_coeff N s fun i hi ↦
    hs (Finset.mem_subtype.mpr (Finset.mem_range.mpr hi))).trans_lt hcoeff

-- TODO(paper-gap): The proof on p. 704 bounds the squared norm using any
-- coefficient. For a leading singular vector, the squared norm is the square
-- of the first coefficient.

/-- Paper: Theorem C.3.6.1, p. 703. The first coefficient of a singular
expansion equals the operator norm, including for the zero operator. -/
theorem SingularExpansion.coeff_zero_eq_opNorm {T : E →L[ℂ] F} (d : SingularExpansion T) :
    (d.coeff 0 : ℝ) = ‖T‖ := by
  apply le_antisymm
  · by_cases h : d.coeff 0 = 0
    · simpa only [h, NNReal.coe_zero] using norm_nonneg T
    let i : {n // d.coeff n ≠ 0} := ⟨0, h⟩
    have hT : T (d.source i) = ((d.coeff i : ℝ) * ⟪d.source i, d.source i⟫_ℂ) • d.target i :=
      (d.hasSum_apply (d.source i)).unique (hasSum_single i fun j hj ↦ by
        rw [d.orthonormal_source.inner_eq_zero hj, mul_zero, zero_smul])
    have hinner : ⟪d.source i, d.source i⟫_ℂ = 1 := by
      simp [inner_self_eq_norm_sq_to_K, d.orthonormal_source.norm_eq_one i]
    have hi0 : 0 ≤ (d.coeff i : ℝ) := (d.coeff i).2
    simpa only [hT, hinner, mul_one, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hi0, d.orthonormal_target.norm_eq_one i,
      d.orthonormal_source.norm_eq_one i] using T.le_opNorm (d.source i)
  · refine ContinuousLinearMap.opNorm_le_bound T (d.coeff 0).2 fun x ↦ ?_
    refine le_of_tendsto' (d.hasSum_apply x).norm fun s ↦ ?_
    exact norm_sum_singularTerms_le d.coeff d.orthonormal_source d.orthonormal_target
      s (d.coeff 0).2 (fun i _ ↦ d.antitone_coeff (Nat.zero_le i.val)) x

-- Keep the completeness hypotheses in the existing signature.
set_option linter.unusedSectionVars false in
/-- Paper: §C.3.6, p. 704. The coefficients of a singular expansion are
the approximation numbers and are independent of the orthonormal vectors.
Deviation: The sequences are indexed from zero and include any zero tail. -/
theorem SingularExpansion.coeff_eq_approximationNumber {T : E →L[ℂ] F}
    (d : SingularExpansion T) (n : ℕ) :
    (d.coeff n : ℝ) = approximationNumber T n := by
  classical
  apply le_antisymm
  · refine le_csInf ⟨_, 0, by simp, rfl⟩ ?_
    rintro _ ⟨S, hS, rfl⟩
    by_cases hn : d.coeff n = 0
    · simp [hn]
    -- Every admissible approximant kills a nonzero combination of the first n + 1 vectors.
    let index (i : Fin (n + 1)) : {k // d.coeff k ≠ 0} :=
      ⟨i, ne_of_gt ((pos_iff_ne_zero.mpr hn).trans_le
        (d.antitone_coeff (Nat.lt_succ_iff.mp i.isLt)))⟩
    have hindex : Injective index := fun _ _ h ↦ Fin.val_injective (congrArg Subtype.val h)
    let e := d.source ∘ index
    let f := d.target ∘ index
    have he : Orthonormal ℂ e := d.orthonormal_source.comp index hindex
    have hf : Orthonormal ℂ f := d.orthonormal_target.comp index hindex
    let v := Fintype.linearCombination ℂ e
    let R := S.toLinearMap.rangeRestrict.comp v
    have : FiniteDimensional ℂ S.toLinearMap.range :=
      Module.rank_lt_aleph0_iff.mp (hS.trans_lt Cardinal.natCast_lt_aleph0)
    have hker : R.ker ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by
      rw [Module.finrank_pi, Fintype.card_fin]
      exact Nat.lt_succ_of_le (Module.finrank_le_of_rank_le hS))
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    have hSx : S (v a) = 0 := congrArg Subtype.val (LinearMap.mem_ker.mp ha)
    have hxnorm : 0 < ‖v a‖ := norm_pos_iff.mpr fun h ↦ ha0
      (linearIndependent_iff_injective_fintypeLinearCombination.mp he.linearIndependent
        (h.trans (map_zero v).symm))
    have hTe (i : Fin (n + 1)) : T (e i) = ((d.coeff i : ℝ) : ℂ) • f i := by
      let j := index i
      change T (d.source j) = ((d.coeff j : ℝ) : ℂ) • d.target j
      have hsum := d.hasSum_apply (d.source j)
      rw [hsum.unique (hasSum_single j fun k hk ↦ by
        simp [d.orthonormal_source.inner_eq_zero hk])]
      simp [d.orthonormal_source.norm_eq_one j]
    have hTx : T (v a) = ∑ i, (a i * ((d.coeff i : ℝ) : ℂ)) • f i := by
      simp only [v, Fintype.linearCombination_apply, map_sum, map_smul, hTe, smul_smul]
    have hlower : (d.coeff n : ℝ) * ‖v a‖ ≤ ‖T (v a)‖ := by
      apply le_of_sq_le_sq _ (norm_nonneg _)
      have he_sq : ‖v a‖ ^ 2 = ∑ i, ‖a i‖ ^ 2 := by
        simpa only [v, Fintype.linearCombination_apply, LinearIsometry.toSpanSingleton_apply]
          using he.orthogonalFamily.norm_sum a Finset.univ
      have hf_sq : ‖T (v a)‖ ^ 2 = ∑ i, ‖a i * ((d.coeff i : ℝ) : ℂ)‖ ^ 2 := by
        rw [hTx]
        simpa only [LinearIsometry.toSpanSingleton_apply] using
          hf.orthogonalFamily.norm_sum (fun i ↦ a i * ((d.coeff i : ℝ) : ℂ)) Finset.univ
      rw [mul_pow, he_sq, Finset.mul_sum, hf_sq]
      refine Finset.sum_le_sum fun i _ ↦ ?_
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (NNReal.coe_nonneg _),
        mul_pow, mul_comm (‖a i‖ ^ 2)]
      exact mul_le_mul_of_nonneg_right
        ((sq_le_sq₀ (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)).mpr
          (NNReal.coe_le_coe.mpr (d.antitone_coeff (Nat.lt_succ_iff.mp i.isLt)))) (sq_nonneg _)
    have hbound := (S - T).le_opNorm (v a)
    rw [sub_apply, hSx, zero_sub, norm_neg] at hbound
    exact le_of_mul_le_mul_right (hlower.trans hbound) hxnorm
  · -- Truncating at n gives an admissible approximant with error at most the nth coefficient.
    let s := (Finset.range n).subtype (fun i ↦ d.coeff i ≠ 0)
    let S : E →L[ℂ] F := ∑ i ∈ s, ((d.coeff i : ℝ) : ℂ) •
      (innerSL ℂ (d.source i)).smulRight (d.target i)
    have hrange : S.toLinearMap.range ≤ Submodule.span ℂ (↑(s.image d.target) : Set F) := by
      rintro _ ⟨x, rfl⟩
      change S x ∈ Submodule.span ℂ (↑(s.image d.target) : Set F)
      simp only [S, sum_apply, smul_apply, ContinuousLinearMap.smulRight_apply, smul_smul]
      exact Submodule.sum_mem _ fun i hi ↦ Submodule.smul_mem _ _
        (Submodule.subset_span (Finset.mem_image_of_mem d.target hi))
    have hcard : (s.image d.target).card ≤ n := by
      refine Finset.card_image_le.trans ?_
      rw [show s.card = ((Finset.range n).filter fun i ↦ d.coeff i ≠ 0).card
        from Finset.card_subtype _ _]
      exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range n)
    have hS := (Submodule.rank_mono hrange).trans
      ((rank_span_finset_le (s.image d.target)).trans (Nat.cast_le.mpr hcard))
    have happ : approximationNumber T n ≤ ‖S - T‖ :=
      csInf_le ⟨0, by rintro _ ⟨_, _, rfl⟩; exact norm_nonneg _⟩ ⟨S, hS, rfl⟩
    rw [norm_sub_rev] at happ
    exact happ.trans (d.norm_sub_sum_le_coeff n s fun i hi ↦
      Finset.mem_subtype.mpr (Finset.mem_range.mpr hi))

/-- Paper: Definition C.3.6.2(1), p. 704. The compact operators with summable
p-th powers of the approximation numbers contain zero and are closed under
addition and complex scalar multiplication. -/
theorem schattenClass_submodule_axioms (p : ℝ) (hp : 1 ≤ p) :
    let s : Set (E →L[ℂ] F) :=
      {T | IsCompactOperator T ∧ Summable (fun n ↦ (approximationNumber T n) ^ p)}
    0 ∈ s ∧
      (∀ {A B : E →L[ℂ] F}, A ∈ s → B ∈ s → A + B ∈ s) ∧
      (∀ (c : ℂ) {A : E →L[ℂ] F}, A ∈ s → c • A ∈ s) := by
  let errors (T : E →L[ℂ] F) (n : ℕ) : Set ℝ :=
    {r | ∃ S : E →L[ℂ] F, S.toLinearMap.rank ≤ (n : Cardinal) ∧ r = ‖S - T‖}
  have errors_nonempty (T : E →L[ℂ] F) (n : ℕ) : (errors T n).Nonempty :=
    ⟨_, 0, by simp, rfl⟩
  have errors_nonneg (T : E →L[ℂ] F) (n : ℕ) : (0 : ℝ) ∈ lowerBounds (errors T n) := by
    rintro _ ⟨S, _, rfl⟩
    exact norm_nonneg _
  have nonneg (T : E →L[ℂ] F) (n : ℕ) : 0 ≤ approximationNumber T n :=
    le_csInf (errors_nonempty T n) (errors_nonneg T n)
  have le_error (T S : E →L[ℂ] F) {n : ℕ} (hS : S.toLinearMap.rank ≤ (n : Cardinal)) :
      approximationNumber T n ≤ ‖S - T‖ :=
    csInf_le ⟨0, errors_nonneg T n⟩ ⟨S, hS, rfl⟩
  have exists_approximation {T : E →L[ℂ] F} {n : ℕ} {a : ℝ}
      (ha : approximationNumber T n < a) :
      ∃ S : E →L[ℂ] F, S.toLinearMap.rank ≤ (n : Cardinal) ∧ ‖S - T‖ < a := by
    obtain ⟨_, ⟨S, hS, rfl⟩, hSa⟩ := exists_lt_of_csInf_lt (errors_nonempty T n) ha
    exact ⟨S, hS, hSa⟩
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  refine ⟨⟨isCompactOperator_zero, ?_⟩, ?_, ?_⟩
  · have hzero (n : ℕ) : approximationNumber (0 : E →L[ℂ] F) n = 0 :=
      le_antisymm (by simpa using le_error 0 0 (n := n) (by simp)) (nonneg _ _)
    simp [hzero, Real.zero_rpow hp0.ne']
  · intro A B hA hB
    refine ⟨hA.1.add hB.1, ?_⟩
    -- Rank bounds add when the two approximants are added.
    have hadd (n k : ℕ) (hnk : n + n ≤ k) :
        approximationNumber (A + B) k ≤ approximationNumber A n + approximationNumber B n := by
      refine le_add_of_forall_lt fun a ha b hb ↦ ?_
      obtain ⟨S, hS, hSa⟩ := exists_approximation ha
      obtain ⟨T, hT, hTb⟩ := exists_approximation hb
      have hrank : (S + T).toLinearMap.rank ≤ (k : Cardinal) := by
        refine (LinearMap.rank_add_le _ _).trans ((add_le_add hS hT).trans ?_)
        exact_mod_cast hnk
      calc
        approximationNumber (A + B) k ≤ ‖S + T - (A + B)‖ := le_error _ _ hrank
        _ = ‖(S - A) + (T - B)‖ := by congr 1; abel
        _ ≤ ‖S - A‖ + ‖T - B‖ := norm_add_le _ _
        _ ≤ a + b := add_le_add hSa.le hTb.le
    -- Both the even and odd subsequences have the same summable majorant.
    have bound (n k : ℕ) (hnk : n + n ≤ k) : approximationNumber (A + B) k ^ p ≤
        (2 : ℝ) ^ (p - 1) * (approximationNumber A n ^ p + approximationNumber B n ^ p) := by
      refine (Real.rpow_le_rpow (nonneg _ _) (hadd n k hnk) hp0.le).trans ?_
      exact_mod_cast NNReal.rpow_add_le_mul_rpow_add_rpow
        ⟨approximationNumber A n, nonneg _ _⟩ ⟨approximationNumber B n, nonneg _ _⟩ hp
    have hs := (hA.2.add hB.2).mul_left ((2 : ℝ) ^ (p - 1))
    exact Summable.even_add_odd
      (hs.of_nonneg_of_le (fun n ↦ Real.rpow_nonneg (nonneg _ _) _) (fun n ↦ bound n _ (by omega)))
      (hs.of_nonneg_of_le (fun n ↦ Real.rpow_nonneg (nonneg _ _) _) (fun n ↦ bound n _ (by omega)))
  · intro c A hA
    refine ⟨hA.1.smul c, (hA.2.mul_left (‖c‖ ^ p)).of_nonneg_of_le
      (fun n ↦ Real.rpow_nonneg (nonneg _ _) _) (fun n ↦ ?_)⟩
    have hsmul : approximationNumber (c • A) n ≤ ‖c‖ * approximationNumber A n := by
      refine le_mul_of_forall_lt₀ fun a ha b hb ↦ ?_
      obtain ⟨S, hS, hSb⟩ := exists_approximation hb
      have hrank : (c • S).toLinearMap.rank ≤ (n : Cardinal) :=
        (Submodule.rank_mono (S.toLinearMap.range_smul_le_range c)).trans hS
      refine (le_error _ _ hrank).trans ?_
      rw [← smul_sub, norm_smul]
      exact mul_le_mul ha.le hSb.le (norm_nonneg _) ((norm_nonneg c).trans ha.le)
    rw [← Real.mul_rpow (norm_nonneg c) (nonneg A n)]
    exact Real.rpow_le_rpow (nonneg _ _) hsmul hp0.le

variable (E F) in
/-- Paper: Definition C.3.6.2(1), p. 704. The Schatten class of index p is
the submodule of compact operators with summable p-th powers of their
approximation numbers. -/
def schattenClass (p : ℝ) (hp : 1 ≤ p) : Submodule ℂ (E →L[ℂ] F) where
  carrier := {T | IsCompactOperator T ∧ Summable (fun n ↦ (approximationNumber T n) ^ p)}
  zero_mem' := (schattenClass_submodule_axioms p hp).1
  add_mem' := (schattenClass_submodule_axioms p hp).2.1
  smul_mem' := (schattenClass_submodule_axioms p hp).2.2

/-- Paper: Definition C.3.6.2(1), p. 704. The Schatten norm is the p-th root
of the sum of the p-th powers of the approximation numbers. -/
def schattenNorm {p : ℝ} {hp : 1 ≤ p} (T : schattenClass E F p hp) : ℝ :=
  (∑' n, (approximationNumber T.val n) ^ p) ^ (1 / p)

omit [CompleteSpace E] [CompleteSpace F] in
/-- An approximation number vanishes once its index bounds the rank of the operator,
since the operator approximates itself. -/
private theorem approximationNumber_eq_zero_of_rank_le (T : E →L[ℂ] F) {n : ℕ}
    (hn : Module.rank ℂ T.toLinearMap.range ≤ (n : Cardinal)) :
    approximationNumber T n = 0 := by
  have hlow : ∀ r ∈ {r | ∃ S : E →L[ℂ] F,
      Module.rank ℂ S.toLinearMap.range ≤ (n : Cardinal) ∧ r = ‖S - T‖}, 0 ≤ r :=
    fun _ ⟨_, _, h⟩ ↦ h ▸ norm_nonneg _
  apply le_antisymm
  · exact (csInf_le ⟨0, hlow⟩ ⟨T, hn, rfl⟩).trans_eq (by simp)
  · exact le_csInf ⟨_, T, hn, rfl⟩ hlow

omit [CompleteSpace E] [CompleteSpace F] in
/-- The zeroth approximation number is the operator norm, since the only approximant of
rank zero is the zero operator. -/
private theorem approximationNumber_zero_eq_norm (T : E →L[ℂ] F) :
    approximationNumber T 0 = ‖T‖ := by
  have hset : {r | ∃ S : E →L[ℂ] F, Module.rank ℂ S.toLinearMap.range ≤ ((0 : ℕ) : Cardinal) ∧
      r = ‖S - T‖} = {‖T‖} := by
    ext r
    constructor
    · rintro ⟨S, hS, rfl⟩
      have h0 : Module.rank ℂ S.toLinearMap.range = 0 := by
        rw [Nat.cast_zero] at hS
        exact le_zero_iff.mp hS
      rw [Submodule.rank_eq_zero, LinearMap.range_eq_bot] at h0
      have hS0 : S = 0 := ContinuousLinearMap.coe_injective h0
      simp [hS0]
    · rintro rfl
      exact ⟨0, by simp, by simp⟩
  unfold approximationNumber
  rw [hset, csInf_singleton]

/-- An operator with finite-dimensional range is compact and its approximation numbers
vanish from the dimension of the range on, so it lies in every Schatten class. -/
private theorem mem_schattenClass_of_finiteDimensional_range {p : ℝ} (hp : 1 ≤ p)
    (T : E →L[ℂ] F) (hT : FiniteDimensional ℂ T.toLinearMap.range) :
    T ∈ schattenClass E F p hp := by
  have : ProperSpace T.toLinearMap.range := FiniteDimensional.proper_rclike ℂ _
  refine ⟨?_, ?_⟩
  · let T' : E →L[ℂ] T.toLinearMap.range :=
      T.codRestrict _ (fun x ↦ LinearMap.mem_range_self T.toLinearMap x)
    exact (isCompactOperator_of_locallyCompactSpace_dom T').continuous_comp
      continuous_subtype_val
  · apply summable_of_ne_finset_zero (s := Finset.range (Module.finrank ℂ T.toLinearMap.range))
    intro n hn
    have hn : Module.finrank ℂ T.toLinearMap.range ≤ n := by simpa using hn
    rw [approximationNumber_eq_zero_of_rank_le T (by
      rw [← Module.finrank_eq_rank]
      exact_mod_cast hn), Real.zero_rpow (by linarith)]

omit [CompleteSpace E] [CompleteSpace F] in
/-- The range of a rank-one map lies in the span of its vector. -/
private theorem range_smulRight_le (φ : E →L[ℂ] ℂ) (f : F) :
    (φ.smulRight f).toLinearMap.range ≤ ℂ ∙ f := by
  rintro _ ⟨x, rfl⟩
  exact Submodule.mem_span_singleton.mpr ⟨φ x, rfl⟩

/-- Paper: Definition C.3.6.2(1), p. 704. A rank-one map belongs to every
Schatten class.
Deviation: This checks class membership on rank-one maps. -/
theorem smulRight_mem_schattenClass {p : ℝ} (hp : 1 ≤ p) (φ : E →L[ℂ] ℂ) (f : F) :
    φ.smulRight f ∈ schattenClass E F p hp := by
  have := FiniteDimensional.span_of_finite ℂ (Set.finite_singleton f)
  exact mem_schattenClass_of_finiteDimensional_range hp _
    (Submodule.finiteDimensional_of_le (range_smulRight_le φ f))

/-- Paper: Definition C.3.6.2(1), p. 704. A rank-one map has Schatten norm
equal to the product of the norms of its functional and its vector.
Deviation: This checks the normalization of the Schatten norm for all indices. -/
theorem schattenNorm_smulRight {p : ℝ} (hp : 1 ≤ p) (φ : E →L[ℂ] ℂ) (f : F) :
    schattenNorm ⟨φ.smulRight f, smulRight_mem_schattenClass hp φ f⟩ = ‖φ‖ * ‖f‖ := by
  have hp0 : p ≠ 0 := by linarith
  have hrank : Module.rank ℂ (φ.smulRight f).toLinearMap.range ≤ 1 :=
    (Submodule.rank_mono (range_smulRight_le φ f)).trans
      ((rank_span_le _).trans_eq (Cardinal.mk_singleton f))
  have hterm (n : ℕ) : approximationNumber (φ.smulRight f) n ^ p =
      if n = 0 then ‖φ.smulRight f‖ ^ p else 0 := by
    rcases n with _ | n
    · simp [approximationNumber_zero_eq_norm]
    · have h1 : (1 : Cardinal) ≤ ((n + 1 : ℕ) : Cardinal) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      rw [approximationNumber_eq_zero_of_rank_le _ (hrank.trans h1), Real.zero_rpow hp0]
      simp
  unfold schattenNorm
  simp only [hterm, tsum_ite_eq]
  rw [one_div, Real.rpow_rpow_inv (norm_nonneg _) hp0,
    ContinuousLinearMap.norm_smulRight_apply]

variable (E F) in
/-- Paper: Definition C.3.6.2(2), p. 704. The Hilbert-Schmidt operators
are the Schatten class of index two. -/
abbrev hilbertSchmidtOperators : Submodule ℂ (E →L[ℂ] F) :=
  schattenClass E F 2 one_le_two

omit [CompleteSpace E] in
/-- Square summability on a Hilbert basis gives an operator-norm limit of finite-rank maps. -/
private theorem isCompactOperator_of_summable_basis {ι : Type*} (b : HilbertBasis ι ℂ E)
    (T : E →L[ℂ] F) (h : Summable (fun i ↦ ‖T (b i)‖ ^ (2 : ℕ))) :
    IsCompactOperator T := by
  let A (i : ι) : E →L[ℂ] F := InnerProductSpace.rankOne ℂ (T (b i)) (b i)
  have hbound (s : Finset ι) : ‖∑ i ∈ s, A i‖ ≤ √(∑ i ∈ s, ‖T (b i)‖ ^ 2) := by
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x ↦ ?_
    rw [sum_apply]
    calc
      ‖∑ i ∈ s, A i x‖ ≤ ∑ i ∈ s, ‖T (b i)‖ * ‖⟪b i, x⟫_ℂ‖ := by
        simpa only [A, InnerProductSpace.rankOne_apply, norm_smul, mul_comm] using
          (norm_sum_le s (fun i ↦ A i x))
      _ ≤ √(∑ i ∈ s, ‖T (b i)‖ ^ 2) * √(∑ i ∈ s, ‖⟪b i, x⟫_ℂ‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt s _ _
      _ ≤ √(∑ i ∈ s, ‖T (b i)‖ ^ 2) * ‖x‖ := by
        rw [← Real.sqrt_sq (norm_nonneg x)]
        exact mul_le_mul_of_nonneg_left
          (Real.sqrt_le_sqrt (b.orthonormal.sum_inner_products_le x)) (Real.sqrt_nonneg _)
  have hA : Summable A := by
    refine summable_iff_vanishing_norm.mpr fun ε hε ↦ ?_
    obtain ⟨s, hs⟩ := summable_iff_vanishing_norm.mp h (ε ^ 2) (by positivity)
    exact ⟨s, fun t ht ↦ (hbound t).trans_lt
      ((Real.sqrt_lt' hε).mpr ((le_abs_self _).trans_lt (hs t ht)))⟩
  have hsum : (∑' i, A i) = T := by
    ext x
    have hpoint : HasSum (fun i ↦ A i x) (T x) := by
      simpa only [A, InnerProductSpace.rankOne_apply, b.repr_apply_apply, map_smul] using
        T.hasSum (b.hasSum_repr x)
    exact ((ContinuousLinearMap.apply ℂ F x).hasSum hA.hasSum).unique hpoint
  rw [← hsum]
  refine isCompactOperator_of_tendsto hA.hasSum (Eventually.of_forall fun s ↦ ?_)
  refine (compactOperator (RingHom.id ℂ) E F).sum_mem fun i _ ↦ ?_
  change IsCompactOperator (InnerProductSpace.rankOne ℂ (T (b i)) (b i))
  rw [InnerProductSpace.rankOne_def']
  exact (isCompactOperator_of_locallyCompactSpace_rng
    (ContinuousLinearMap.toSpanSingleton ℂ (T (b i)))).comp_clm (innerSL ℂ (b i))

omit [CompleteSpace E] [CompleteSpace F] in
/-- Parseval in the given basis and orthogonality in the singular expansion identify the
two square-summability criteria by summing the same nonnegative family in either order. -/
private theorem SingularExpansion.summable_sq_iff_summable_basis {ι : Type*}
    (b : HilbertBasis ι ℂ E) {T : E →L[ℂ] F} (d : SingularExpansion T) :
    Summable (fun n ↦ (d.coeff n : ℝ) ^ (2 : ℕ)) ↔
      Summable (fun i ↦ ‖T (b i)‖ ^ (2 : ℕ)) := by
  let J := {n : ℕ // d.coeff n ≠ 0}
  let a (j : J) (i : ι) : ℝ := (d.coeff j : ℝ) ^ 2 * ‖⟪d.source j, b i⟫_ℂ‖ ^ 2
  have hrow (j : J) : HasSum (a j) ((d.coeff j : ℝ) ^ 2) := by
    have hparseval : HasSum (fun i ↦ ‖⟪d.source j, b i⟫_ℂ‖ ^ (2 : ℕ)) 1 := by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two, LinearIsometryEquiv.norm_map,
        b.repr_apply_apply, norm_inner_symm (b _) (d.source j),
        d.orthonormal_source.norm_eq_one j, one_pow] using
        lp.hasSum_norm (p := 2) (by norm_num) (b.repr (d.source j))
    simpa only [a, mul_one] using hparseval.mul_left ((d.coeff j : ℝ) ^ (2 : ℕ))
  have hcol (i : ι) : HasSum (fun j ↦ a j i) (‖T (b i)‖ ^ 2) := by
    let c (j : J) : ℂ := (d.coeff j : ℝ) * ⟪d.source j, b i⟫_ℂ
    have hnorm (s : Finset J) : ‖∑ j ∈ s, c j • d.target j‖ ^ 2 = ∑ j ∈ s, a j i := by
      simpa only [LinearIsometry.toSpanSingleton_apply, c, a, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (NNReal.coe_nonneg _), mul_pow] using
        d.orthonormal_target.orthogonalFamily.norm_sum c s
    exact ((d.hasSum_apply (b i)).norm.pow 2).congr hnorm
  have hrows : Summable (fun p : J × ι ↦ a p.1 p.2) ↔
      Summable (fun j : J ↦ (d.coeff j : ℝ) ^ (2 : ℕ)) := by
    have hnonneg (p : J × ι) : 0 ≤ a p.1 p.2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
    have htsum (j : J) : (∑' i, a j i) = (d.coeff j : ℝ) ^ 2 := (hrow j).tsum_eq
    rw [summable_prod_of_nonneg hnonneg, and_iff_right (fun j ↦ (hrow j).summable)]
    simp only [htsum]
  have hcols : Summable (fun p : ι × J ↦ a p.2 p.1) ↔
      Summable (fun i ↦ ‖T (b i)‖ ^ (2 : ℕ)) := by
    have hnonneg (p : ι × J) : 0 ≤ a p.2 p.1 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
    have htsum (i : ι) : (∑' j, a j i) = ‖T (b i)‖ ^ 2 := (hcol i).tsum_eq
    rw [summable_prod_of_nonneg hnonneg, and_iff_right (fun i ↦ (hcol i).summable)]
    simp only [htsum]
  have hsupp : Function.support (fun n ↦ (d.coeff n : ℝ) ^ (2 : ℕ)) ⊆
      {n | d.coeff n ≠ 0} := by
    intro n hn hz
    exact hn (by simp [hz])
  have hsub : Summable (fun j : J ↦ (d.coeff j : ℝ) ^ (2 : ℕ)) ↔
      Summable (fun n ↦ (d.coeff n : ℝ) ^ (2 : ℕ)) :=
    exists_congr fun _ ↦ hasSum_subtype_iff_of_support_subset hsupp
  exact hsub.symm.trans (hrows.symm.trans ((Equiv.prodComm ι J).summable_iff.symm.trans hcols))

/-- Paper: Definition C.3.6.2(2), p. 704. An operator is Hilbert-Schmidt
exactly when the squared norms of the images of any given Hilbert basis
form a summable family.
Deviation: This checks the index-two class against the basis criterion. -/
theorem mem_hilbertSchmidtOperators_iff_summable_basis {ι : Type*} (b : HilbertBasis ι ℂ E)
    (T : E →L[ℂ] F) :
    T ∈ hilbertSchmidtOperators E F ↔ Summable (fun i ↦ ‖T (b i)‖ ^ (2 : ℕ)) := by
  change (IsCompactOperator T ∧ Summable (fun n ↦ approximationNumber T n ^ (2 : ℝ))) ↔ _
  simp only [Real.rpow_two]
  have hcompact (hT : IsCompactOperator T) :
      Summable (fun n ↦ approximationNumber T n ^ (2 : ℕ)) ↔
        Summable (fun i ↦ ‖T (b i)‖ ^ (2 : ℕ)) := by
    obtain ⟨d⟩ := (isCompactOperator_iff_nonempty_singularExpansion T).mp hT
    simpa only [d.coeff_eq_approximationNumber] using d.summable_sq_iff_summable_basis b
  refine ⟨fun ⟨hT, hs⟩ ↦ (hcompact hT).mp hs, fun hs ↦ ?_⟩
  have hT := isCompactOperator_of_summable_basis b T hs
  exact ⟨hT, (hcompact hT).mpr hs⟩

variable (E F) in
/-- Paper: Definition C.3.6.2(3), p. 704. The trace-class operators are
the Schatten class of index one. -/
abbrev traceClassOperators : Submodule ℂ (E →L[ℂ] F) :=
  schattenClass E F 1 le_rfl

/-- Paper: Lemma C.3.1.2, p. 694. A nuclear Hilbert endomorphism is compact. -/
private theorem isCompactOperator_of_isNuclearOperator {T : E →L[ℂ] E}
    (hT : IsNuclearOperator T) : IsCompactOperator T := by
  obtain ⟨z, rfl⟩ := (isBanachNuclear_iff_mem_range T).mp
    ((isNuclearOperator_iff_isBanachNuclear T).mp hT)
  let A := completedProjectiveTensorToOperators (E := E) (F := E)
  change IsCompactOperator (A z)
  refine Completion.induction_on z
    (isClosed_setOfPred_isCompactOperator.preimage A.continuous) fun w ↦ ?_
  rw [completedProjectiveTensorToOperators_coe]
  let S := tensorToFiniteRank w
  have : FiniteDimensional ℂ S.toLinearMap.range := finiteDimensional_range_tensorToFiniteRank w
  have : ProperSpace S.toLinearMap.range := FiniteDimensional.proper_rclike ℂ _
  exact (isCompactOperator_of_locallyCompactSpace_dom
    (S.codRestrict _ (LinearMap.mem_range_self S.toLinearMap))).continuous_comp
    continuous_subtype_val

open InnerProductSpace in
/-- A singular expansion with summable coefficients gives a nuclear presentation. -/
private theorem SingularExpansion.isNuclearOperator_of_summable_coeff {T : E →L[ℂ] E}
    (d : SingularExpansion T) (hc : Summable (fun n ↦ (d.coeff n : ℝ))) :
    IsNuclearOperator T := by
  classical
  let e (n : ℕ) : E := if hn : d.coeff n ≠ 0 then d.source ⟨n, hn⟩ else 0
  let f (n : ℕ) : E := if hn : d.coeff n ≠ 0 then d.target ⟨n, hn⟩ else 0
  let B := Metric.closedBall (0 : E) 1
  have hf (n : ℕ) : f n ∈ B := by
    by_cases hn : d.coeff n ≠ 0
    · simp [B, f, hn, d.orthonormal_target.norm_eq_one]
    · simp [B, f, not_ne_iff.mp hn]
  apply (isNuclearOperator_iff_nonempty_presentation T).mpr
  refine ⟨{
    coeff := fun n ↦ (d.coeff n : ℝ)
    functional := fun n ↦ innerSL ℂ (e n)
    disc := B
    isBanachDisc := isBanachDisc_closedUnitBall
    vector := fun n ↦ ⟨f n, Submodule.subset_span (hf n)⟩
    vector_mem := hf
    summable_coeff := by simpa [Complex.norm_real, abs_of_nonneg (NNReal.coe_nonneg _)] using hc
    equicontinuous := ?_
    hasSum := ?_ }⟩
  · refine (LipschitzWith.uniformEquicontinuous _ 1 fun n ↦ ?_).equicontinuous 0
    apply (innerSL ℂ (e n)).lipschitzWith.weaken
    rw [← NNReal.coe_le_coe, coe_nnNorm, NNReal.coe_one, innerSL_apply_norm]
    by_cases hn : d.coeff n ≠ 0
    · simp [e, hn, d.orthonormal_source.norm_eq_one]
    · simp [e, not_ne_iff.mp hn]
  · intro x
    refine (hasSum_subtype_iff_of_support_subset (s := {n | d.coeff n ≠ 0}) ?_).mp ?_
    · intro n hn
      by_contra h
      exact hn (by simp [show d.coeff n = 0 by simpa using h])
    · refine (d.hasSum_apply x).congr_fun fun i ↦ ?_
      simp [e, f, i.property]

open InnerProductSpace in
/-- In the singular vector coordinates, the absolute diagonal of a nuclear operator
is its family of nonzero singular coefficients. -/
private theorem SingularExpansion.summable_coeff_of_isNuclearOperator {T : E →L[ℂ] E}
    (d : SingularExpansion T) (hT : IsNuclearOperator T) :
    Summable (fun n ↦ (d.coeff n : ℝ)) := by
  classical
  let I := {n // d.coeff n ≠ 0}
  let K := lp (fun _ : I ↦ ℂ) 2
  let b : HilbertBasis I ℂ K := HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ K)
  let U : K →L[ℂ] E := d.orthonormal_source.orthogonalFamily.linearIsometry.toContinuousLinearMap
  let V : K →L[ℂ] E := d.orthonormal_target.orthogonalFamily.linearIsometry.toContinuousLinearMap
  let D := V.adjoint.comp (T.comp U)
  have hD : IsNuclearOperator D := by
    obtain ⟨c, φ, y, hc, hφ, hy, hsum⟩ := (isNuclearOperator_iff_isBanachNuclear T).mp hT
    let P := (ContinuousLinearMap.compL ℂ K E ℂ).flip U
    exact (isNuclearOperator_iff_isBanachNuclear D).mpr
      ⟨c, P ∘ φ, V.adjoint ∘ y, hc, (P.continuous.tendsto' 0 0 (map_zero P)).comp hφ,
        (V.adjoint.continuous.tendsto' 0 0 (map_zero V.adjoint)).comp hy, fun x ↦ by
          simpa only [Function.comp_apply, map_smul, P, D, ContinuousLinearMap.flip_apply,
            ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply] using
            V.adjoint.hasSum (hsum (U x))⟩
  have hb (i : I) : b i = lp.single 2 i 1 := b.repr_self i
  have hU (i : I) : U (b i) = d.source i := by
    rw [hb]
    exact (d.orthonormal_source.orthogonalFamily.linearIsometry_apply_single (i := i) 1).trans
      (one_smul ℂ _)
  have hV (i : I) : V (b i) = d.target i := by
    rw [hb]
    exact (d.orthonormal_target.orthogonalFamily.linearIsometry_apply_single (i := i) 1).trans
      (one_smul ℂ _)
  have hdiag (i : I) : ‖⟪b i, D (b i)⟫_ℂ‖ = (d.coeff i : ℝ) := by
    change ‖⟪b i, V.adjoint (T (U (b i)))⟫_ℂ‖ = _
    rw [V.adjoint_inner_right, hU, hV]
    have hsingular : T (d.source i) = ((d.coeff i : ℝ) : ℂ) • d.target i := by
      apply (d.hasSum_apply (d.source i)).unique
      convert hasSum_single i (fun j hj ↦ ?_) using 1
      · simp [d.orthonormal_source.norm_eq_one i]
      · simp [d.orthonormal_source.inner_eq_zero hj]
    have hunit : ⟪d.target i, d.target i⟫_ℂ = 1 := by
      simp [inner_self_eq_norm_sq_to_K, d.orthonormal_target.norm_eq_one i]
    rw [hsingular, inner_smul_right, hunit, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (NNReal.coe_nonneg _)]
  obtain ⟨r, hr⟩ := (summable_norm_hilbertDiagonal b D hD).congr hdiag
  have hsupp : Function.support (fun n ↦ (d.coeff n : ℝ)) ⊆ {n | d.coeff n ≠ 0} := by
    intro n hn hz
    exact hn (by simp [hz])
  exact ⟨r, (hasSum_subtype_iff_of_support_subset hsupp).mp hr⟩

/-- Paper: Definition C.3.6.2(3), p. 704. For Hilbert endomorphisms, the
index-one Schatten condition is equivalent to nuclearity.
Deviation: This checks that trace class agrees with §C.3.4 on endomorphisms. -/
theorem mem_traceClassOperators_iff_isNuclearOperator (T : E →L[ℂ] E) :
    T ∈ traceClassOperators E E ↔ IsNuclearOperator T := by
  change (IsCompactOperator T ∧ Summable (fun n ↦ approximationNumber T n ^ (1 : ℝ))) ↔ _
  simp only [Real.rpow_one]
  constructor
  · rintro ⟨hT, hs⟩
    obtain ⟨d⟩ := (isCompactOperator_iff_nonempty_singularExpansion T).mp hT
    exact d.isNuclearOperator_of_summable_coeff (hs.congr fun n ↦
      (d.coeff_eq_approximationNumber n).symm)
  · intro hT
    have hc := isCompactOperator_of_isNuclearOperator hT
    obtain ⟨d⟩ := (isCompactOperator_iff_nonempty_singularExpansion T).mp hc
    exact ⟨hc, (d.summable_coeff_of_isNuclearOperator hT).congr d.coeff_eq_approximationNumber⟩

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

-- TODO(paper-gap): Lemma C.3.6.3(1) is false. The second approximation numbers
-- of diag(1, 0) and diag(0, 1) on ℂ² vanish, while their sum has second
-- approximation number one.

/-- Paper: Lemma C.3.6.3(2), p. 704. Each approximation number changes
by at most the operator norm of the difference of the two operators.
Deviation: The approximation-number index starts at zero. -/
theorem abs_approximationNumber_sub_le (A B : E →L[ℂ] F) (n : ℕ) :
    |approximationNumber A n - approximationNumber B n| ≤ ‖A - B‖ := by
  have key (A B : E →L[ℂ] F) :
      approximationNumber A n ≤ approximationNumber B n + ‖A - B‖ := by
    have hz : Module.rank ℂ (0 : E →L[ℂ] F).toLinearMap.range ≤ (n : Cardinal) := by simp
    rw [← sub_le_iff_le_add]
    unfold approximationNumber
    refine le_csInf (by exact ⟨_, 0, hz, rfl⟩) ?_
    rintro _ ⟨S, hS, rfl⟩
    rw [sub_le_iff_le_add]
    calc
      approximationNumber A n ≤ ‖S - A‖ :=
        csInf_le ⟨0, fun r ⟨S, _, h⟩ ↦ h ▸ norm_nonneg _⟩ ⟨S, hS, rfl⟩
      _ = ‖(S - B) + (B - A)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖S - B‖ + ‖A - B‖ := (norm_add_le _ _).trans_eq (by rw [norm_sub_rev B A])
  rw [abs_sub_le_iff]
  constructor
  · linarith [key A B]
  · linarith [key B A, norm_sub_rev A B]

/-- Every strict upper bound for an approximation number is realized as a strict error bound
by some approximant of the prescribed rank. -/
private theorem exists_approximation_of_lt {T : E →L[ℂ] F} {n : ℕ} {a : ℝ}
    (h : approximationNumber T n < a) :
    ∃ S : E →L[ℂ] F, S.toLinearMap.rank ≤ (n : Cardinal) ∧ ‖S - T‖ < a := by
  have hz : (0 : E →L[ℂ] F).toLinearMap.rank ≤ (n : Cardinal) := by simp
  unfold approximationNumber at h
  obtain ⟨r, ⟨S, hS, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt (by exact ⟨_, 0, hz, rfl⟩) h
  exact ⟨S, hS, hlt⟩

/-- Paper: Lemma C.3.6.3(3), p. 704. The approximation number of a product
at the sum of two one-based indices is bounded by the product of the
approximation numbers of its factors at the corresponding indices.
Deviation: The one-based index sum becomes m + n + 1 in zero-based indexing. -/
theorem approximationNumber_comp_le (A : F →L[ℂ] G) (B : E →L[ℂ] F) (m n : ℕ) :
    approximationNumber (A.comp B) (m + n + 1) ≤
      approximationNumber A m * approximationNumber B n := by
  apply le_mul_of_forall_lt₀
  intro a ha b hb
  obtain ⟨S, hS, hSa⟩ := exists_approximation_of_lt ha
  obtain ⟨T, hT, hTb⟩ := exists_approximation_of_lt hb
  -- Subtract the product of the errors from the composite to get an approximant.
  let R := S.comp B + (A - S).comp T
  have hleft := (LinearMap.rank_comp_le_left B.toLinearMap S.toLinearMap).trans hS
  have hright : ((A - S).comp T).toLinearMap.rank ≤ (n : Cardinal) := by
    apply Cardinal.lift_le.mp
    exact (LinearMap.lift_rank_comp_le_right T.toLinearMap (A - S).toLinearMap).trans
      (by simpa only [Cardinal.lift_natCast] using Cardinal.lift_le.mpr hT)
  have hR : R.toLinearMap.rank ≤ ((m + n + 1 : ℕ) : Cardinal) := by
    refine (LinearMap.rank_add_le _ _).trans ((add_le_add hleft hright).trans ?_)
    exact_mod_cast Nat.le_succ (m + n)
  have herr : R - A.comp B = (S - A).comp (B - T) := by
    simp only [R, ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]
    abel
  calc
    approximationNumber (A.comp B) (m + n + 1) ≤ ‖R - A.comp B‖ := by
      unfold approximationNumber
      refine csInf_le ?_ ⟨R, hR, rfl⟩
      exact ⟨0, fun r ⟨S, _, h⟩ ↦ h ▸ norm_nonneg _⟩
    _ ≤ ‖S - A‖ * ‖T - B‖ := by
      rw [herr, norm_sub_rev T B]
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ a * b := mul_le_mul hSa.le hTb.le (norm_nonneg _) ((norm_nonneg _).trans hSa.le)

end SchattenClasses

-- The compact submodule and its closedness are Mathlib's compactOperator and
-- isClosed_setOfPred_isCompactOperator.

section HilbertSchmidtKernels

open MeasureTheory

open scoped ComplexConjugate ENNReal

private theorem kernelLp_norm_sq {Z : Type*} [MeasurableSpace Z] {ρ : Measure Z}
    (g : Lp ℂ 2 ρ) : ‖g‖ ^ 2 = ∫ z, ‖g z‖ ^ 2 ∂ρ := by
  rw [@InnerProductSpace.norm_sq_eq_re_inner ℂ, L2.inner_def]
  simp_rw [inner_self_eq_norm_sq_to_K]
  norm_cast

private theorem kernelLp_norm_sq_toLp {Z : Type*} [MeasurableSpace Z] {ρ : Measure Z}
    {g : Z → ℂ} (hg : MemLp g 2 ρ) :
    ‖hg.toLp g‖ ^ 2 = ∫ z, ‖g z‖ ^ 2 ∂ρ := by
  rw [kernelLp_norm_sq]
  exact integral_congr_ae (hg.coeFn_toLp.fun_comp (fun c ↦ ‖c‖ ^ 2))

private theorem kernelLp_slice_integrable {Z : Type*} [MeasurableSpace Z] {ρ : Measure Z}
    {g h : Z → ℂ} (hg : MemLp g 2 ρ) (hh : MemLp h 2 ρ) :
    Integrable (fun z ↦ g z * h z) ρ := by
  have : ENNReal.HolderTriple 2 2 1 := by infer_instance
  exact memLp_one_iff_integrable.mp (hg.fun_mul hh)

private theorem kernelLp_conj {Z : Type*} [MeasurableSpace Z] {ρ : Measure Z}
    {g : Z → ℂ} (hg : MemLp g 2 ρ) :
    ∃ u : Lp ℂ 2 ρ, (u =ᵐ[ρ] fun z ↦ conj (g z)) ∧ ‖u‖ = ‖hg.toLp g‖ := by
  let h : Z → ℂ := fun z ↦ conj (g z)
  have hh : MemLp h 2 ρ := by
    apply (memLp_two_iff_integrable_sq_norm _).mpr
    · simpa [h] using (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
    · exact Complex.continuous_conj.comp_aestronglyMeasurable hg.aestronglyMeasurable
  refine ⟨hh.toLp h, hh.coeFn_toLp, (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_⟩
  rw [kernelLp_norm_sq_toLp, kernelLp_norm_sq_toLp]
  simp [h]

private theorem kernelLp_integral_eq_inner {Z : Type*} [MeasurableSpace Z] {ρ : Measure Z}
    {g : Z → ℂ} {u : Lp ℂ 2 ρ} (hu : u =ᵐ[ρ] fun z ↦ conj (g z)) (f : Lp ℂ 2 ρ) :
    (∫ z, g z * f z ∂ρ) = ⟪u, f⟫_ℂ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hu] with z hz
  simp [hz, RCLike.inner_apply, mul_comm]

section
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} [SigmaFinite μ] [SigmaFinite ν]

/-- For almost every target point, an L² kernel has an L² source slice. -/
private theorem kernelLp_slices (k : Lp ℂ 2 (μ.prod ν)) :
    ∀ᵐ y ∂ν, MemLp (fun x ↦ k (x, y)) 2 μ := by
  have h := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable k)).mp (Lp.memLp k)
  filter_upwards [h.prod_left_ae] with y hy
  exact (memLp_two_iff_integrable_sq_norm
    ((Lp.stronglyMeasurable k).comp_measurable measurable_prodMk_right).aestronglyMeasurable).mpr hy

private theorem kernelLp_slice_norm_sq (k : Lp ℂ 2 (μ.prod ν)) :
    Integrable (fun y ↦ ∫ x, ‖k (x, y)‖ ^ 2 ∂μ) ν ∧
      (∫ y, ∫ x, ‖k (x, y)‖ ^ 2 ∂μ ∂ν) = ‖k‖ ^ 2 := by
  have h := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable k)).mp (Lp.memLp k)
  exact ⟨h.swap.integral_prod_left, (integral_prod_symm _ h).symm.trans (kernelLp_norm_sq k).symm⟩

omit [SigmaFinite μ] in
private theorem kernelLp_apply_bound {g : X → ℂ} (hg : MemLp g 2 μ) (f : Lp ℂ 2 μ) :
    ‖∫ x, g x * f x ∂μ‖ ≤ ‖hg.toLp g‖ * ‖f‖ := by
  obtain ⟨u, hu, hnorm⟩ := kernelLp_conj hg
  rw [← hnorm]
  exact (le_of_eq (congrArg norm (kernelLp_integral_eq_inner hu f))).trans (norm_inner_le_norm _ _)

private theorem kernelLp_memLp (k : Lp ℂ 2 (μ.prod ν)) (f : Lp ℂ 2 μ) :
    MemLp (fun y ↦ ∫ x, k (x, y) * f x ∂μ) 2 ν := by
  have hmeas : StronglyMeasurable (fun z : X × Y ↦ k z * f z.1) :=
    (Lp.stronglyMeasurable k).mul ((Lp.stronglyMeasurable f).comp_measurable measurable_fst)
  apply (memLp_two_iff_integrable_sq_norm hmeas.integral_prod_left'.aestronglyMeasurable).mpr
  refine ((kernelLp_slice_norm_sq k).1.const_mul (‖f‖ ^ 2)).mono'
    (hmeas.integral_prod_left'.norm.pow 2).aestronglyMeasurable ?_
  filter_upwards [kernelLp_slices k] with y hy
  rw [Real.norm_of_nonneg (sq_nonneg _), mul_comm, ← kernelLp_norm_sq_toLp hy, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (kernelLp_apply_bound hy f) 2

private theorem kernelLpOperator_bound (k : Lp ℂ 2 (μ.prod ν)) (f : Lp ℂ 2 μ) :
    ‖(kernelLp_memLp k f).toLp _‖ ≤ ‖k‖ * ‖f‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [kernelLp_norm_sq_toLp, mul_pow, ← (kernelLp_slice_norm_sq k).2, ← integral_mul_const]
  apply integral_mono_ae
    ((memLp_two_iff_integrable_sq_norm (kernelLp_memLp k f).aestronglyMeasurable).mp
      (kernelLp_memLp k f)) ((kernelLp_slice_norm_sq k).1.mul_const _)
  filter_upwards [kernelLp_slices k] with y hy
  rw [← kernelLp_norm_sq_toLp hy, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (kernelLp_apply_bound hy f) 2

private def kernelLpOperator (k : Lp ℂ 2 (μ.prod ν)) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 ν :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ (kernelLp_memLp k f).toLp _
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [(kernelLp_memLp k (f + g)).coeFn_toLp,
          (kernelLp_memLp k f).coeFn_toLp, (kernelLp_memLp k g).coeFn_toLp,
          Lp.coeFn_add ((kernelLp_memLp k f).toLp _) ((kernelLp_memLp k g).toLp _),
          kernelLp_slices k] with y hfg hf hg hadd hy
        rw [hfg, hadd, Pi.add_apply, hf, hg, ← integral_add
          (kernelLp_slice_integrable hy (Lp.memLp f)) (kernelLp_slice_integrable hy (Lp.memLp g))]
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_add f g] with x hx
        rw [hx, Pi.add_apply, mul_add]
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [(kernelLp_memLp k (c • f)).coeFn_toLp,
          (kernelLp_memLp k f).coeFn_toLp,
          Lp.coeFn_smul c ((kernelLp_memLp k f).toLp _)] with y hcf hf hsmul
        simp only [RingHom.id_apply]
        rw [hcf, hsmul, Pi.smul_apply, hf, ← integral_smul]
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_smul c f] with x hx
        rw [hx, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
        ring } ‖k‖ (kernelLpOperator_bound k)

private theorem kernelLpOperator_apply (k : Lp ℂ 2 (μ.prod ν)) (f : Lp ℂ 2 μ) :
    ∀ᵐ y ∂ν, Integrable (fun x ↦ k (x, y) * f x) μ ∧
      kernelLpOperator k f y = ∫ x, k (x, y) * f x ∂μ := by
  filter_upwards [kernelLp_slices k, (kernelLp_memLp k f).coeFn_toLp] with y hy h
  exact ⟨kernelLp_slice_integrable hy (Lp.memLp f), h⟩

/-- Integration against an L² kernel is linear in the kernel. -/
private def kernelLpToOperator :
    Lp ℂ 2 (μ.prod ν) →ₗ[ℂ] (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 ν) where
  toFun := kernelLpOperator
  map_add' k l := by
    ext1 f
    apply Lp.ext
    have h := Measure.ae_ae_of_ae_prod
      ((Measure.measurePreserving_swap (μ := ν) (ν := μ)).quasiMeasurePreserving.ae (Lp.coeFn_add k l))
    filter_upwards [kernelLpOperator_apply (k + l) f, kernelLpOperator_apply k f,
      kernelLpOperator_apply l f, h, Lp.coeFn_add (kernelLpOperator k f) (kernelLpOperator l f)]
      with y hkl hk hl hy hadd
    change kernelLpOperator (k + l) f y = (kernelLpOperator k f + kernelLpOperator l f) y
    rw [hkl.2, hadd, Pi.add_apply, hk.2, hl.2, ← integral_add hk.1 hl.1]
    apply integral_congr_ae
    filter_upwards [hy] with x hx
    exact (congrArg (fun z : ℂ ↦ z * f x) hx).trans (add_mul _ _ _)
  map_smul' c k := by
    ext1 f
    apply Lp.ext
    have h := Measure.ae_ae_of_ae_prod
      ((Measure.measurePreserving_swap (μ := ν) (ν := μ)).quasiMeasurePreserving.ae (Lp.coeFn_smul c k))
    filter_upwards [kernelLpOperator_apply (c • k) f, kernelLpOperator_apply k f,
      h, Lp.coeFn_smul c (kernelLpOperator k f)] with y hck hk hy hsmul
    change kernelLpOperator (c • k) f y = (c • kernelLpOperator k f) y
    rw [hck.2, hsmul, Pi.smul_apply, hk.2, ← integral_smul]
    apply integral_congr_ae
    filter_upwards [hy] with x hx
    exact (congrArg (fun z : ℂ ↦ z * f x) hx).trans (mul_assoc _ _ _)


/-- Parseval on the source slices gives the squared L² norm of the kernel. -/
private theorem hasSum_norm_sq_kernelLpOperator {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℂ (Lp ℂ 2 μ)) (k : Lp ℂ 2 (μ.prod ν)) :
    HasSum (fun i ↦ ‖kernelLpOperator k (b i)‖ ^ 2) (‖k‖ ^ 2) := by
  let F (i : ι) (y : Y) := ‖kernelLpOperator k (b i) y‖ ^ 2
  have hF (i : ι) : Integrable (F i) ν :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp (Lp.memLp _)
  have hpoint : ∀ᵐ y ∂ν, (∑' i, ENNReal.ofReal (F i y)) =
      ENNReal.ofReal (∫ x, ‖k (x, y)‖ ^ 2 ∂μ) := by
    filter_upwards [kernelLp_slices k, ae_all_iff.mpr (fun i ↦ kernelLpOperator_apply k (b i))]
      with y hy heval
    obtain ⟨u, hu, hnorm⟩ := kernelLp_conj hy
    have hsum : HasSum (fun i ↦ F i y) (‖u‖ ^ 2) := by
      have hnormsum := lp.hasSum_norm (p := 2) (by norm_num) (b.repr u)
      convert hnormsum using 1
      · funext i
        change ‖kernelLpOperator k (b i) y‖ ^ 2 = ‖b.repr u i‖ ^ (2 : ℝ≥0∞).toReal
        rw [b.repr_apply_apply, show (2 : ℝ≥0∞).toReal = (2 : ℕ) by norm_num,
          Real.rpow_natCast, (heval i).2, kernelLp_integral_eq_inner hu, norm_inner_symm]
      · rw [b.repr.norm_map, show (2 : ℝ≥0∞).toReal = (2 : ℕ) by norm_num, Real.rpow_natCast]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ sq_nonneg _) hsum.summable,
      hsum.tsum_eq, hnorm, kernelLp_norm_sq_toLp]
  have ht : (∑' i, ENNReal.ofReal (‖kernelLpOperator k (b i)‖ ^ 2)) =
      ENNReal.ofReal (‖k‖ ^ 2) := by
    have heq (i : ι) : ENNReal.ofReal (‖kernelLpOperator k (b i)‖ ^ 2) =
        ∫⁻ y, ENNReal.ofReal (F i y) ∂ν := by
      rw [kernelLp_norm_sq, ofReal_integral_eq_lintegral_ofReal (hF i)
        (ae_of_all _ fun _ ↦ sq_nonneg _)]
    simp_rw [heq]
    rw [← lintegral_tsum (fun i ↦ (hF i).aemeasurable.ennreal_ofReal),
      lintegral_congr_ae hpoint,
      ← ofReal_integral_eq_lintegral_ofReal (kernelLp_slice_norm_sq k).1
        (ae_of_all _ fun _ ↦ integral_nonneg fun _ ↦ sq_nonneg _),
      (kernelLp_slice_norm_sq k).2]
  have hsum : Summable (fun i ↦ ‖kernelLpOperator k (b i)‖ ^ 2) := by
    have hfin := ht.trans_ne ENNReal.ofReal_ne_top
    have hn := ENNReal.tsum_coe_ne_top_iff_summable_coe.mp hfin
    simpa only [Real.coe_toNNReal _ (sq_nonneg _)] using hn
  have heq : (∑' i, ‖kernelLpOperator k (b i)‖ ^ 2) = ‖k‖ ^ 2 := by
    rw [← ENNReal.ofReal_eq_ofReal_iff (tsum_nonneg fun _ ↦ sq_nonneg _) (sq_nonneg _),
      ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ sq_nonneg _) hsum]
    exact ht
  exact heq ▸ hsum.hasSum


private theorem kernelLpToOperator_norm_le (k : Lp ℂ 2 (μ.prod ν)) :
    ‖kernelLpToOperator k‖ ≤ ‖k‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg _) (kernelLpOperator_bound k)

omit [SigmaFinite μ] [SigmaFinite ν] in
private theorem rankOneKernel_memLp (e : Lp ℂ 2 μ) (f : Lp ℂ 2 ν) :
    MemLp (fun z : X × Y ↦ conj (e z.1) * f z.2) 2 (μ.prod ν) := by
  have he := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable e)).mp (Lp.memLp e)
  have hf := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  apply (memLp_two_iff_integrable_sq_norm
    (((Complex.continuous_conj.comp_stronglyMeasurable (Lp.stronglyMeasurable e)).comp_measurable
      measurable_fst).mul ((Lp.stronglyMeasurable f).comp_measurable
        measurable_snd)).aestronglyMeasurable).mpr
  change Integrable (fun z : X × Y ↦ ‖conj (e z.1) * f z.2‖ ^ 2) (μ.prod ν)
  simpa only [norm_mul, Complex.norm_conj, mul_pow] using he.mul_prod hf

/-- The product kernel of the operator sending `g` to `⟪e, g⟫_ℂ • f`. -/
private def rankOneKernel (e : Lp ℂ 2 μ) (f : Lp ℂ 2 ν) : Lp ℂ 2 (μ.prod ν) :=
  (rankOneKernel_memLp e f).toLp _

private theorem rankOneKernel_inner (e e' : Lp ℂ 2 μ) (f f' : Lp ℂ 2 ν) :
    ⟪rankOneKernel e f, rankOneKernel e' f'⟫_ℂ = ⟪e', e⟫_ℂ * ⟪f, f'⟫_ℂ := by
  simp only [L2.inner_def]
  rw [← integral_prod_mul]
  apply integral_congr_ae
  filter_upwards [(rankOneKernel_memLp e f).coeFn_toLp,
    (rankOneKernel_memLp e' f').coeFn_toLp] with z hz hz'
  change (rankOneKernel e f) z = _ at hz
  change (rankOneKernel e' f') z = _ at hz'
  rw [hz, hz']
  simp only [RCLike.inner_apply, map_mul, starRingEnd_apply, star_star]
  ring

private theorem kernelLpToOperator_rankOne (e : Lp ℂ 2 μ) (f : Lp ℂ 2 ν) :
    kernelLpToOperator (rankOneKernel e f) = (innerSL ℂ e).smulRight f := by
  ext1 g
  apply Lp.ext
  have h := Measure.ae_ae_of_ae_prod ((Measure.measurePreserving_swap
    (μ := ν) (ν := μ)).quasiMeasurePreserving.ae (rankOneKernel_memLp e f).coeFn_toLp)
  filter_upwards [kernelLpOperator_apply (rankOneKernel e f) g, h,
    Lp.coeFn_smul ⟪e, g⟫_ℂ f] with y hy hker hsmul
  change kernelLpOperator (rankOneKernel e f) g y = (⟪e, g⟫_ℂ • f) y
  rw [hy.2, hsmul, Pi.smul_apply, smul_eq_mul, L2.inner_def, ← integral_mul_const]
  apply integral_congr_ae
  filter_upwards [hker] with x hx
  change (rankOneKernel e f) (x, y) = conj (e x) * f y at hx
  rw [hx]
  simp only [RCLike.inner_apply, starRingEnd_apply]
  ring

/-- A singular expansion yields a convergent orthogonal series of rank-one kernels. -/
private theorem kernelLpToOperator_surjective_of_mem_hilbertSchmidt
    (T : hilbertSchmidtOperators (Lp ℂ 2 μ) (Lp ℂ 2 ν)) :
    ∃ k, kernelLpToOperator k = T.val := by
  classical
  have hT : IsCompactOperator T.val ∧
      Summable (fun n ↦ approximationNumber T.val n ^ (2 : ℝ)) := T.property
  obtain ⟨d⟩ := (isCompactOperator_iff_nonempty_singularExpansion T.val).mp hT.1
  let I := {n // d.coeff n ≠ 0}
  let w (i : I) := rankOneKernel (d.source i) (d.target i)
  have hw : Orthonormal ℂ w := by
    rw [orthonormal_iff_ite]
    intro i j
    change ⟪rankOneKernel (d.source i) (d.target i),
      rankOneKernel (d.source j) (d.target j)⟫_ℂ = _
    rw [rankOneKernel_inner, orthonormal_iff_ite.mp d.orthonormal_target]
    split_ifs with h
    · subst j
      rw [orthonormal_iff_ite.mp d.orthonormal_source]
      simp
    · simp
  have hcoeff : Summable (fun n ↦ (d.coeff n : ℝ) ^ 2) := by
    simpa only [d.coeff_eq_approximationNumber, Real.rpow_two] using hT.2
  have hs : Summable (fun i : I ↦ ((d.coeff i : ℝ) : ℂ) • w i) := by
    have h := (hw.orthogonalFamily.summable_iff_norm_sq_summable
      (fun i : I ↦ ((d.coeff i : ℝ) : ℂ))).mpr
    apply h
    change Summable (fun i : I ↦ ‖((d.coeff i : ℝ) : ℂ)‖ ^ 2)
    simp only [Complex.norm_real, Real.norm_of_nonneg (NNReal.coe_nonneg _)]
    exact hcoeff.subtype (fun n ↦ d.coeff n ≠ 0)
  let A := (kernelLpToOperator (μ := μ) (ν := ν)).mkContinuous 1 (fun k ↦
    (kernelLpToOperator_norm_le k).trans_eq (one_mul _).symm)
  refine ⟨∑' i : I, ((d.coeff i : ℝ) : ℂ) • w i, ?_⟩
  have hsum := A.hasSum hs.hasSum
  change HasSum (fun i : I ↦ kernelLpToOperator (((d.coeff i : ℝ) : ℂ) • w i)) _ at hsum
  simp only [map_smul, w, kernelLpToOperator_rankOne] at hsum
  exact hsum.unique d.hasSum_opNorm

omit [SigmaFinite μ] in
private theorem countable_kernelLp_basis {ι : Type*} [SeparableSpace (Lp ℂ 2 μ)]
    (b : HilbertBasis ι ℂ (Lp ℂ 2 μ)) : Countable ι := by
  refine Pairwise.countable_of_isOpen_disjoint (s := fun i ↦ Metric.ball (b i) (1 / 2))
    ?_ (fun _ ↦ Metric.isOpen_ball) (fun _ ↦ Metric.nonempty_ball.mpr (by norm_num))
  intro i j hij
  apply Metric.ball_disjoint_ball
  have hsq : dist (b i) (b j) ^ 2 = 2 := by
    rw [dist_eq_norm, @norm_sub_sq ℂ, b.orthonormal.inner_eq_zero hij,
      b.orthonormal.norm_eq_one, b.orthonormal.norm_eq_one]
    norm_num
  rw [show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num]
  apply (sq_le_sq₀ zero_le_one dist_nonneg).mp
  rw [hsq]
  norm_num

private theorem kernelLpToOperator_mem_hilbertSchmidt [SeparableSpace (Lp ℂ 2 μ)]
    (k : Lp ℂ 2 (μ.prod ν)) :
    kernelLpToOperator k ∈ hilbertSchmidtOperators (Lp ℂ 2 μ) (Lp ℂ 2 ν) := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ (Lp ℂ 2 μ)
  have := countable_kernelLp_basis b
  exact (mem_hilbertSchmidtOperators_iff_summable_basis b _).mpr
    (hasSum_norm_sq_kernelLpOperator b k).summable

/-- Extend the right singular vectors to a basis to compute the Schatten norm by Parseval. -/
private theorem schattenNorm_kernelLpToOperator [SeparableSpace (Lp ℂ 2 μ)]
    (k : Lp ℂ 2 (μ.prod ν)) :
    schattenNorm ⟨kernelLpToOperator k, kernelLpToOperator_mem_hilbertSchmidt k⟩ = ‖k‖ := by
  classical
  let T := kernelLpToOperator k
  have hT : IsCompactOperator T ∧ Summable (fun n ↦ approximationNumber T n ^ (2 : ℝ)) :=
    kernelLpToOperator_mem_hilbertSchmidt k
  obtain ⟨d⟩ := (isCompactOperator_iff_nonempty_singularExpansion T).mp hT.1
  obtain ⟨w, b, hw, hb⟩ := d.orthonormal_source.toSubtypeRange.exists_hilbertBasis_extension
  have := countable_kernelLp_basis b
  let I := {n // d.coeff n ≠ 0}
  let j (i : I) : w := ⟨d.source i, hw (mem_range_self i)⟩
  have hj : Injective j := fun i i' h ↦
    d.orthonormal_source.linearIndependent.injective (congrArg Subtype.val h)
  have hTj (i : I) : T (b (j i)) = ((d.coeff i : ℝ) : ℂ) • d.target i := by
    rw [show b (j i) = d.source i from congrFun hb (j i)]
    rw [(d.hasSum_apply (d.source i)).unique (hasSum_single i (fun i' hi ↦ by
      simp [d.orthonormal_source.inner_eq_zero hi]))]
    simp [d.orthonormal_source.norm_eq_one]
  have hzero (a : w) (ha : a ∉ range j) : T (b a) = 0 := by
    refine (d.hasSum_apply (b a)).unique ?_
    convert (hasSum_zero (β := I) (α := Lp ℂ 2 ν)) using 1
    funext i
    rw [show d.source i = b (j i) from (congrFun hb (j i)).symm,
      b.orthonormal.inner_eq_zero (fun h ↦ ha ⟨i, h⟩)]
    simp
  have hcoeff : Summable (fun n ↦ (d.coeff n : ℝ) ^ 2) := by
    simpa only [d.coeff_eq_approximationNumber, Real.rpow_two] using hT.2
  have hsub : HasSum (fun i : I ↦ ‖T (b (j i))‖ ^ 2) (∑' n, (d.coeff n : ℝ) ^ 2) := by
    have hz : support (fun n ↦ (d.coeff n : ℝ) ^ 2) ⊆ {n | d.coeff n ≠ 0} := by
      intro n hn
      change d.coeff n ≠ 0
      intro h
      exact hn (by simp [h])
    simp only [hTj, norm_smul, Complex.norm_real, Real.norm_of_nonneg (NNReal.coe_nonneg _),
      d.orthonormal_target.norm_eq_one, mul_one]
    exact (hasSum_subtype_iff_of_support_subset hz).mpr hcoeff.hasSum
  have hsum := (hj.hasSum_iff (f := fun a ↦ ‖T (b a)‖ ^ 2)
    (fun a ha ↦ by simp [hzero a ha])).mp hsub
  have heq := hsum.unique (hasSum_norm_sq_kernelLpOperator b k)
  change (∑' n, approximationNumber T n ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) = ‖k‖
  simp_rw [Real.rpow_two, ← d.coeff_eq_approximationNumber]
  rw [heq, ← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg _)]

end
variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y]

/-- Paper: (C.3.6.5)–(C.3.6.6), p. 705. Square-integrable kernels on the product
of two Radon measure spaces correspond to Hilbert-Schmidt operators between their
L² spaces. The operator acts by integrating in the source variable, almost
everywhere in the target variable.
Deviation: The identification is written as a linear norm-preserving equivalence
of equivalence classes. The integral is required to be defined almost everywhere. -/
theorem hilbertSchmidtOperators_equiv_Lp_prod (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasureOnCompacts μ] [Measure.InnerRegular μ]
    [IsFiniteMeasureOnCompacts ν] [Measure.InnerRegular ν] :
    ∃ e : Lp ℂ 2 (μ.prod ν) ≃ₗ[ℂ] hilbertSchmidtOperators (Lp ℂ 2 μ) (Lp ℂ 2 ν),
      (∀ k, schattenNorm (e k) = ‖k‖) ∧
      ∀ (k : Lp ℂ 2 (μ.prod ν)) (f : Lp ℂ 2 μ), ∀ᵐ y ∂ν,
        Integrable (fun x ↦ k (x, y) * f x) μ ∧
          (e k).val f y = ∫ x, k (x, y) * f x ∂μ := by
  have : SigmaFinite μ := inferInstance
  have : SigmaFinite ν := inferInstance
  have : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  have : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  have : SecondCountableTopology (Lp ℂ 2 μ) := Lp.SecondCountableTopology
  let S := hilbertSchmidtOperators (Lp ℂ 2 μ) (Lp ℂ 2 ν)
  let L := kernelLpToOperator.codRestrict S kernelLpToOperator_mem_hilbertSchmidt
  have hL : Bijective L := by
    constructor
    · apply (injective_iff_map_eq_zero L).mpr
      intro k hk
      have hk' : kernelLpToOperator k = 0 := congrArg Subtype.val hk
      obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ (Lp ℂ 2 μ)
      have := countable_kernelLp_basis b
      have hs := hasSum_norm_sq_kernelLpOperator b k
      change HasSum (fun i ↦ ‖kernelLpToOperator k (b i)‖ ^ 2) (‖k‖ ^ 2) at hs
      rw [hk'] at hs
      have heq : ‖k‖ ^ 2 = 0 := hs.unique (by simp)
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp heq)
    · intro T
      obtain ⟨k, hk⟩ := kernelLpToOperator_surjective_of_mem_hilbertSchmidt T
      exact ⟨k, Subtype.ext hk⟩
  exact ⟨LinearEquiv.ofBijective L hL, schattenNorm_kernelLpToOperator,
    kernelLpOperator_apply⟩

end HilbertSchmidtKernels

section TensorProducts

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

-- (C.3.6.7) and its injectivity are tensorToFiniteRank and tensorToFiniteRank_injective.

/-- Paper: Proposition C.3.6.4(1), p. 705. The image of every algebraic
tensor under the canonical map belongs to each Schatten class. -/
theorem tensorToFiniteRank_mem_schattenClass {p : ℝ} (hp : 1 ≤ p)
    (z : StrongDual ℂ E ⊗[ℂ] F) :
    tensorToFiniteRank z ∈ schattenClass E F p hp := by
  refine mem_schattenClass_of_finiteDimensional_range hp _ ?_
  induction z using TensorProduct.inductionOn with
  | tmul φ y =>
    have := FiniteDimensional.span_of_finite ℂ (Set.finite_singleton y)
    apply Submodule.finiteDimensional_of_le (S₂ := ℂ ∙ y)
    rintro _ ⟨x, rfl⟩
    exact Submodule.mem_span_singleton.mpr ⟨φ x, (tensorToFiniteRank_tmul φ y x).symm⟩
  | add z w hz hw =>
    rw [map_add, ContinuousLinearMap.toLinearMap_add]
    exact Submodule.finiteDimensional_of_le (LinearMap.range_add_le _ _)

/-- Paper: (C.3.6.8), p. 705. The norm of the dual of a Hilbert space satisfies
the parallelogram identity.
Deviation: This supplies the compatible inner product on the dual factor. -/
theorem strongDual_parallelogram (φ ψ : StrongDual ℂ E) :
    ‖φ + ψ‖ * ‖φ + ψ‖ + ‖φ - ψ‖ * ‖φ - ψ‖ =
      2 * (‖φ‖ * ‖φ‖ + ‖ψ‖ * ‖ψ‖) := by
  let R := (InnerProductSpace.toDual ℂ E).symm
  have h := parallelogram_law_with_norm_mul ℂ (R φ) (R ψ)
  simpa only [← map_add, ← map_sub, LinearIsometryEquiv.norm_map] using h

/-- Paper: (C.3.6.8), p. 705. The continuous dual of a Hilbert space has the
inner product compatible with its operator norm. -/
@[instance_reducible]
def strongDualInnerProductSpace : InnerProductSpace ℂ (StrongDual ℂ E) :=
  InnerProductSpace.ofNorm ℂ strongDual_parallelogram

attribute [local instance] strongDualInnerProductSpace

/-- Paper: (C.3.6.8), p. 705. The dual inner product reverses the order of
the arguments under the conjugate-linear Riesz identification.
Deviation: This checks the dual inner product convention. -/
theorem strongDual_inner_eq (φ ψ : StrongDual ℂ E) :
    ⟪φ, ψ⟫_ℂ = ⟪(InnerProductSpace.toDual ℂ E).symm ψ,
      (InnerProductSpace.toDual ℂ E).symm φ⟫_ℂ := by
  let R := (InnerProductSpace.toDual ℂ E).symm
  have hI : ‖(Complex.I : ℂ)‖ = 1 := Complex.norm_I
  have h1 : ‖R ψ + R φ‖ = ‖φ + ψ‖ := by
    rw [← map_add, LinearIsometryEquiv.norm_map, add_comm]
  have h2 : ‖R ψ - R φ‖ = ‖φ - ψ‖ := by
    rw [← map_sub, LinearIsometryEquiv.norm_map, norm_sub_rev]
  have h3 : ‖R ψ - Complex.I • R φ‖ = ‖φ - Complex.I • ψ‖ := by
    have e : R ψ - Complex.I • R φ = R (Complex.I • (φ - Complex.I • ψ)) := by
      simp only [map_smulₛₗ, map_sub, Complex.conj_I, smul_sub, smul_smul]
      simp
      abel
    rw [e, LinearIsometryEquiv.norm_map, norm_smul, hI, one_mul]
  have h4 : ‖R ψ + Complex.I • R φ‖ = ‖φ + Complex.I • ψ‖ := by
    have e : R ψ + Complex.I • R φ = R ((-Complex.I) • (φ + Complex.I • ψ)) := by
      simp only [map_smulₛₗ, map_add, map_neg, Complex.conj_I, neg_neg, smul_add, smul_smul]
      simp [add_comm]
    rw [e, LinearIsometryEquiv.norm_map, norm_smul, norm_neg, hI, one_mul]
  rw [inner_eq_sum_norm_sq_div_four (𝕜 := ℂ) φ ψ, inner_eq_sum_norm_sq_div_four (𝕜 := ℂ) (R ψ) (R φ)]
  simp only [RCLike.I_to_complex]
  rw [h1, h2, h3, h4]

omit [CompleteSpace F] in
private theorem hasSum_tensorColumn_inner {ι : Type*} (b : HilbertBasis ι ℂ E)
    (z w : StrongDual ℂ E ⊗[ℂ] F) :
    HasSum (fun i ↦ ⟪tensorToFiniteRank z (b i), tensorToFiniteRank w (b i)⟫_ℂ) ⟪z, w⟫_ℂ := by
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' =>
    erw [inner_add_left (𝕜 := ℂ) z z' w]
    simpa only [map_add, add_apply, inner_add_left] using hz.add hz'
  | tmul φ y =>
    induction w using TensorProduct.inductionOn with
    | add w w' hw hw' =>
      erw [inner_add_right (𝕜 := ℂ) (φ ⊗ₜ[ℂ] y) w w']
      simpa only [map_add, add_apply, inner_add_right] using hw.add hw'
    | tmul ψ v =>
      let R := (InnerProductSpace.toDual ℂ E).symm
      have h := (b.hasSum_inner_mul_inner (R ψ) (R φ)).mul_right ⟪y, v⟫_ℂ
      rw [TensorProduct.inner_tmul, strongDual_inner_eq]
      refine h.congr_fun fun i ↦ ?_
      simp only [tensorToFiniteRank_tmul, inner_smul_left, inner_smul_right,
        ← InnerProductSpace.toDual_symm_apply, R, ← inner_conj_symm (b i)]
      ring

omit [CompleteSpace F] in
private theorem hasSum_tensorColumn_norm_sq {ι : Type*} (b : HilbertBasis ι ℂ E)
    (z : StrongDual ℂ E ⊗[ℂ] F) :
    HasSum (fun i ↦ ‖tensorToFiniteRank z (b i)‖ ^ 2) (‖z‖ ^ 2) := by
  have h := (hasSum_tensorColumn_inner b z z).mapL Complex.reCLM
  have hz : Complex.reCLM ⟪z, z⟫_ℂ = ‖z‖ ^ 2 :=
    (@norm_sq_eq_re_inner ℂ (StrongDual ℂ E ⊗[ℂ] F) _ inferInstance inferInstance z).symm
  rw [hz] at h
  exact h.congr_fun fun i ↦ (norm_sq_eq_re_inner (𝕜 := ℂ) _)

omit [CompleteSpace E] [CompleteSpace F] in
private theorem SingularExpansion.apply_source {T : E →L[ℂ] F} (d : SingularExpansion T)
    (i : {n // d.coeff n ≠ 0}) :
    T (d.source i) = ((d.coeff i : ℝ) : ℂ) • d.target i := by
  rw [(d.hasSum_apply (d.source i)).unique (hasSum_single i (fun k hk ↦ by
    simp [d.orthonormal_source.inner_eq_zero hk]))]
  simp [d.orthonormal_source.norm_eq_one]

omit [CompleteSpace F] in
private theorem SingularExpansion.exists_source_basis {T : E →L[ℂ] F} (d : SingularExpansion T) :
    ∃ (w : Set E) (b : HilbertBasis w ℂ E) (j : {n // d.coeff n ≠ 0} → w),
      Injective j ∧ (∀ i, b (j i) = d.source i) ∧ ∀ a ∉ range j, T (b a) = 0 := by
  classical
  obtain ⟨w, b, hw, hb⟩ := d.orthonormal_source.toSubtypeRange.exists_hilbertBasis_extension
  let I := {n // d.coeff n ≠ 0}
  let j (i : I) : w := ⟨d.source i, hw (mem_range_self i)⟩
  refine ⟨w, b, j, fun i k h ↦ d.orthonormal_source.linearIndependent.injective
    (congrArg Subtype.val h), fun i ↦ congrFun hb (j i), fun a ha ↦ ?_⟩
  refine (d.hasSum_apply (b a)).unique ?_
  convert (hasSum_zero (β := I) (α := F)) using 1
  funext i
  rw [show d.source i = b (j i) from (congrFun hb (j i)).symm,
    b.orthonormal.inner_eq_zero (fun h ↦ ha ⟨i, h⟩)]
  simp

/-- In a basis extending the source singular vectors, the nonzero columns have
norms equal to the corresponding approximation numbers. -/
private theorem exists_basis_schattenNorm_eq_sqrt (T : hilbertSchmidtOperators E F) :
    ∃ (w : Set E) (b : HilbertBasis w ℂ E),
      schattenNorm T = Real.sqrt (∑' i, ‖T.val (b i)‖ ^ 2) := by
  classical
  obtain ⟨d⟩ := (isCompactOperator_iff_nonempty_singularExpansion T.val).mp T.property.1
  obtain ⟨w, b, j, hj, hb, hzero⟩ := d.exists_source_basis
  have hsupp : support (fun n ↦ (d.coeff n : ℝ) ^ 2) ⊆ {n | d.coeff n ≠ 0} := by
    intro n hn hz
    exact hn (by simp [hz])
  refine ⟨w, b, ?_⟩
  rw [schattenNorm, ← Real.sqrt_eq_rpow, ← hj.tsum_eq (fun a ha ↦ by
    by_contra hn
    exact ha (by simp [hzero a hn]))]
  simp only [Real.rpow_two, ← d.coeff_eq_approximationNumber, hb, d.apply_source, norm_smul, Complex.norm_real,
    Real.norm_of_nonneg (NNReal.coe_nonneg _), d.orthonormal_target.norm_eq_one, mul_one]
  exact congrArg Real.sqrt (tsum_subtype_eq_of_support_subset hsupp).symm

/-- Paper: Proposition C.3.6.4(2), p. 705. The canonical image of an algebraic
tensor has Hilbert-Schmidt norm equal to the norm from the tensor inner product
of (C.3.6.8). Thus the two norms induce the same topology. -/
theorem schattenNorm_tensorToFiniteRank_eq_hilbertTensorNorm (z : StrongDual ℂ E ⊗[ℂ] F) :
    schattenNorm ⟨tensorToFiniteRank z, tensorToFiniteRank_mem_schattenClass one_le_two z⟩ =
      ‖z‖ := by
  let T : hilbertSchmidtOperators E F :=
    ⟨tensorToFiniteRank z, tensorToFiniteRank_mem_schattenClass one_le_two z⟩
  obtain ⟨w, b, hb⟩ := exists_basis_schattenNorm_eq_sqrt T
  exact hb.trans (by rw [(hasSum_tensorColumn_norm_sq b z).tsum_eq, Real.sqrt_sq (norm_nonneg _)])

private theorem hilbertSchmidt_extension {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (L : X →L[ℂ] (E →L[ℂ] F))
    (hcols : ∀ {s : Set E} (b : HilbertBasis s ℂ E) (z : X),
      HasSum (fun i ↦ ‖L z (b i)‖ ^ 2) (‖z‖ ^ 2)) :
    ∃ e : Completion X →ₗ[ℂ] hilbertSchmidtOperators E F,
      (∀ w : X, (e w).val = L w) ∧ ∀ z, schattenNorm (e z) = ‖z‖ := by
  have henergy {w : Set E} (b : HilbertBasis w ℂ E) (z : Completion X) :
      HasSum (fun i ↦ ‖L.fromCompletion z (b i)‖ ^ 2) (‖z‖ ^ 2) := by
    let v (x : X) : lp (fun _ : w ↦ F) 2 := ⟨fun i ↦ L x (b i), memℓp_gen (by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using (hcols b x).summable)⟩
    let columns : X →ₗᵢ[ℂ] lp (fun _ : w ↦ F) 2 := {
      toFun := v
      map_add' := fun x y ↦ by ext i; simp [v]; rfl
      map_smul' := fun c x ↦ by ext i; simp [v]
      norm_map' := fun x ↦ by
        apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
        have h : HasSum (fun i ↦ ‖v x i‖ ^ 2) (‖v x‖ ^ 2) := by
          simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using lp.hasSum_norm (by norm_num) (v x)
        exact h.unique (hcols b x) }
    have heval (i : w) : columns.fromCompletion z i = L.fromCompletion z (b i) := by
      refine Completion.induction_on z (isClosed_eq
        ((lp.evalCLM ℂ _ 2 i).continuous.comp columns.fromCompletion.continuous)
        ((ContinuousLinearMap.apply ℂ F (b i)).continuous.comp L.fromCompletion.continuous)) ?_
      intro w
      rw [LinearIsometry.fromCompletion_apply_coe, ContinuousLinearMap.fromCompletion_apply_coe]
      rfl
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, heval, LinearIsometry.norm_map] using
      lp.hasSum_norm (p := 2) (by norm_num) (columns.fromCompletion z)
  have hmem (z : Completion X) : L.fromCompletion z ∈ hilbertSchmidtOperators E F := by
    obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ E
    exact (mem_hilbertSchmidtOperators_iff_summable_basis b _).mpr (henergy b z).summable
  let e := L.fromCompletion.toLinearMap.codRestrict (hilbertSchmidtOperators E F) hmem
  refine ⟨e, fun w ↦ L.fromCompletion_apply_coe w, fun z ↦ ?_⟩
  obtain ⟨w, b, hb⟩ := exists_basis_schattenNorm_eq_sqrt (e z)
  exact hb.trans ((congrArg Real.sqrt (henergy b z).tsum_eq).trans (Real.sqrt_sq (norm_nonneg z)))

/-- Paper: Proposition C.3.6.4(2), p. 705. The canonical map extends from
algebraic tensors to the Hilbert tensor completion as a linear isometry for
the Hilbert-Schmidt norm. -/
theorem exists_hilbertTensorCompletion_schattenIsometry :
    ∃ e : Completion (StrongDual ℂ E ⊗[ℂ] F) →ₗ[ℂ] hilbertSchmidtOperators E F,
      (∀ z : StrongDual ℂ E ⊗[ℂ] F, (e z).val = tensorToFiniteRank z) ∧
      ∀ z, schattenNorm (e z) = ‖z‖ := by
  have hbound (z : StrongDual ℂ E ⊗[ℂ] F) : ‖tensorToFiniteRank z‖ ≤ 1 * ‖z‖ := by
    let T : hilbertSchmidtOperators E F :=
      ⟨tensorToFiniteRank z, tensorToFiniteRank_mem_schattenClass one_le_two z⟩
    have hs : Summable (fun n ↦ approximationNumber T.val n ^ (2 : ℕ)) := by
      simpa only [← Real.rpow_two] using T.property.2
    rw [one_mul, ← schattenNorm_tensorToFiniteRank_eq_hilbertTensorNorm]
    change ‖T.val‖ ≤ (∑' n, approximationNumber T.val n ^ (2 : ℝ)) ^ (1 / (2 : ℝ))
    simp only [Real.rpow_two, ← Real.sqrt_eq_rpow]
    exact Real.le_sqrt_of_sq_le (by
      simpa only [approximationNumber_zero_eq_norm] using hs.le_tsum 0 (fun i _ ↦ sq_nonneg _))
  let L := LinearMap.mkContinuous (𝕜 := ℂ) (𝕜₂ := ℂ) (E := StrongDual ℂ E ⊗[ℂ] F) (F := E →L[ℂ] F)
    tensorToFiniteRank 1 hbound
  apply hilbertSchmidt_extension (E := E) (F := F) (X := StrongDual ℂ E ⊗[ℂ] F) L
  exact fun b w ↦ hasSum_tensorColumn_norm_sq b w

local notation "πS" => banachProjectiveSeminorm (X := StrongDual ℂ E) (Y := F)
local notation "πW" => WithLocalSeminorm πS
local notation "πP" => ProjectiveTensor (StrongDual ℂ E) F

private def SingularExpansion.diagonalTest {A : E →L[ℂ] F} (d : SingularExpansion A)
    (s : Finset {n // d.coeff n ≠ 0}) : (E →L[ℂ] F) →L[ℂ] ℂ :=
  ∑ i ∈ s, (innerSL ℂ (d.target i)).comp (ContinuousLinearMap.apply ℂ F (d.source i))

omit [CompleteSpace F] in
/-- The singular vectors give norm-one tests on elementary tensors by Bessel's inequality. -/
private theorem SingularExpansion.diagonalTest_rankOne_le {A : E →L[ℂ] F} (d : SingularExpansion A)
    (s : Finset {n // d.coeff n ≠ 0}) (φ : StrongDual ℂ E) (y : F) :
    ‖d.diagonalTest s (φ.smulRight y)‖ ≤ ‖φ‖ * ‖y‖ := by
  let x := (InnerProductSpace.toDual ℂ E).symm φ
  have hx (i) : ‖φ (d.source i)‖ = ‖⟪d.source i, x⟫_ℂ‖ := by
    rw [← InnerProductSpace.toDual_symm_apply, norm_inner_symm]
  calc
    ‖d.diagonalTest s (φ.smulRight y)‖ ≤ ∑ i ∈ s, ‖φ (d.source i)‖ * ‖⟪d.target i, y⟫_ℂ‖ := by
      simpa only [diagonalTest, sum_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
        ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_smul_right, norm_mul] using
        norm_sum_le s (fun i ↦ φ (d.source i) * ⟪d.target i, y⟫_ℂ)
    _ ≤ ‖φ‖ * ‖y‖ := by
      simp_rw [hx]
      refine (Real.sum_mul_le_sqrt_mul_sqrt s _ _).trans (mul_le_mul ?_ ?_ (Real.sqrt_nonneg _) (norm_nonneg _))
      · exact (Real.sqrt_le_iff.mpr ⟨norm_nonneg _, (d.orthonormal_source.sum_inner_products_le x).trans_eq
          (by rw [show ‖x‖ = ‖φ‖ from (InnerProductSpace.toDual ℂ E).symm.norm_map _])⟩)
      · exact Real.sqrt_le_iff.mpr ⟨norm_nonneg _, d.orthonormal_target.sum_inner_products_le y⟩

omit [CompleteSpace E] [CompleteSpace F] in
private theorem SingularExpansion.norm_diagonalTest_self {A : E →L[ℂ] F} (d : SingularExpansion A)
    (s : Finset {n // d.coeff n ≠ 0}) :
    ‖d.diagonalTest s A‖ = ∑ i ∈ s, (d.coeff i : ℝ) := by
  simp only [diagonalTest, sum_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    innerSL_apply_apply, d.apply_source, inner_smul_right, inner_self_eq_norm_sq_to_K, d.orthonormal_target.norm_eq_one,
    RCLike.ofReal_one, one_pow, mul_one, ← Complex.ofReal_sum, Complex.norm_real]
  exact Real.norm_of_nonneg (Finset.sum_nonneg fun i _ ↦ (d.coeff i).2)

omit [CompleteSpace E] [CompleteSpace F] in
/-- Every test bounded on rank-one maps by their cost is bounded by the projective seminorm. -/
private theorem test_tensorToFiniteRank_le (τ : (E →L[ℂ] F) →L[ℂ] ℂ)
    (hτ : ∀ (φ : StrongDual ℂ E) (y : F), ‖τ (φ.smulRight y)‖ ≤ ‖φ‖ * ‖y‖)
    (z : πW) : ‖τ (tensorToFiniteRank z)‖ ≤ ‖z‖ := by
  let f : (StrongDual ℂ E ⊗[ℂ] F) →ₗ[ℂ] ℂ := τ.toLinearMap.comp (tensorToFiniteRank (E := E) (F := F))
  let q : Seminorm ℂ (StrongDual ℂ E ⊗[ℂ] F) := (normSeminorm ℂ ℂ).comp f
  exact (seminorm_le_banachProjectiveSeminorm q zero_le_one (fun φ y ↦ (hτ φ y).trans_eq (one_mul _).symm) z).trans_eq
    (one_mul _)

/-- The singular expansion of an algebraic tensor is finite. In tensor coordinates it
attains the projective decomposition cost. -/
private theorem exists_finite_singularTensor (z : πW) :
    ∃ (d : SingularExpansion (tensorToFiniteRank z)) (s : Finset {n // d.coeff n ≠ 0}),
      z = ∑ i ∈ s, ((d.coeff i : ℝ) : ℂ) •
        (show πW from innerSL ℂ (d.source i) ⊗ₜ[ℂ] d.target i) ∧
      ‖z‖ = ∑ i ∈ s, (d.coeff i : ℝ) := by
  classical
  let A := tensorToFiniteRank (show StrongDual ℂ E ⊗[ℂ] F from z)
  have hfin (w : StrongDual ℂ E ⊗[ℂ] F) : FiniteDimensional ℂ (tensorToFiniteRank w).toLinearMap.range := by
    induction w using TensorProduct.inductionOn with
    | tmul φ y =>
      have := FiniteDimensional.span_of_finite ℂ (Set.finite_singleton y)
      exact Submodule.finiteDimensional_of_le (range_smulRight_le φ y)
    | add w v hw hv =>
      rw [map_add, ContinuousLinearMap.toLinearMap_add]
      exact Submodule.finiteDimensional_of_le (LinearMap.range_add_le _ _)
  have := hfin z
  obtain ⟨d⟩ := (isCompactOperator_iff_nonempty_singularExpansion A).mp
    (tensorToFiniteRank_mem_schattenClass one_le_two z).1
  let r := Module.finrank ℂ A.toLinearMap.range
  let s := (Finset.range r).subtype (fun n ↦ d.coeff n ≠ 0)
  have hall (i : {n // d.coeff n ≠ 0}) : i ∈ s := by
    apply Finset.mem_subtype.mpr
    apply Finset.mem_range.mpr
    by_contra! hi
    apply i.property
    apply NNReal.coe_injective
    rw [d.coeff_eq_approximationNumber, approximationNumber_eq_zero_of_rank_le A (by
      rw [← Module.finrank_eq_rank]; exact_mod_cast hi)]
    rfl
  let w (i : {n // d.coeff n ≠ 0}) : πW := innerSL ℂ (d.source i) ⊗ₜ[ℂ] d.target i
  have hrepr : z = ∑ i ∈ s, ((d.coeff i : ℝ) : ℂ) • w i := by
    let L : πW →ₗ[ℂ] (E →L[ℂ] F) := tensorToFiniteRank
    apply tensorToFiniteRank_injective (E := E) (F := F)
    change L z = L (∑ i ∈ s, ((d.coeff i : ℝ) : ℂ) • w i)
    rw [map_sum]
    simp only [map_smul]
    exact d.hasSum_opNorm.unique (hasSum_sum_of_ne_finset_zero (fun i hi ↦ (hi (hall i)).elim))
  refine ⟨d, s, hrepr, le_antisymm ?_ ?_⟩
  · refine (congrArg norm hrepr).le.trans ?_
    refine (norm_sum_le s _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
    simp only [norm_smul, Complex.norm_real, Real.norm_of_nonneg (NNReal.coe_nonneg _)]
    refine mul_le_of_le_one_right (d.coeff i).2 ?_
    exact (projectiveSeminorm_tmul_le _ _).trans_eq (by
      rw [innerSL_apply_norm, d.orthonormal_source.norm_eq_one, d.orthonormal_target.norm_eq_one, one_mul])
  · rw [← d.norm_diagonalTest_self s]
    exact test_tensorToFiniteRank_le _ (d.diagonalTest_rankOne_le s) z

private theorem projective_unitHull_eq_closedBall :
    (convexHull ℝ (image2 (fun (φ : StrongDual ℂ E) (y : F) ↦ (show πW from φ ⊗ₜ[ℂ] y))
      (Metric.closedBall 0 1) (Metric.closedBall 0 1))) = Metric.closedBall (0 : πW) 1 := by
  classical
  let U := image2 (fun (φ : StrongDual ℂ E) (y : F) ↦ (show πW from φ ⊗ₜ[ℂ] y))
    (Metric.closedBall 0 1) (Metric.closedBall 0 1)
  change convexHull ℝ U = _
  have hz : (0 : πW) ∈ convexHull ℝ U := subset_convexHull _ _ <|
    ⟨0, by simp, 0, by simp, TensorProduct.zero_tmul _ _⟩
  apply le_antisymm
  · refine convexHull_min ?_ (convex_closedBall _ _)
    rintro _ ⟨φ, hφ, y, hy, rfl⟩
    apply mem_closedBall_zero_iff.mpr
    exact (projectiveSeminorm_tmul_le φ y).trans ((mul_le_of_le_one_right (norm_nonneg φ)
      (mem_closedBall_zero_iff.mp hy)).trans (mem_closedBall_zero_iff.mp hφ))
  · intro z hz'
    obtain ⟨d, s, hrepr, hnorm⟩ := exists_finite_singularTensor z
    let w (i : {n // d.coeff n ≠ 0}) : πW := innerSL ℂ (d.source i) ⊗ₜ[ℂ] d.target i
    let c (i : {n // d.coeff n ≠ 0}) : ℝ := d.coeff i
    have hw (i) : w i ∈ convexHull ℝ U := subset_convexHull _ _ <| mem_image2_of_mem
      (mem_closedBall_zero_iff.mpr (by rw [innerSL_apply_norm, d.orthonormal_source.norm_eq_one]))
      (mem_closedBall_zero_iff.mpr (d.orthonormal_target.norm_eq_one i).le)
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simpa only [Finset.sum_empty] using hrepr ▸ hz
    have hc : 0 < ∑ i ∈ s, c i := Finset.sum_pos (fun i _ ↦ NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr i.2)) hs
    have hmem := (convex_convexHull ℝ U).centerMass_mem (t := s) (w := c) (z := w) (fun i _ ↦ (d.coeff i).2) hc (fun i _ ↦ hw i)
    have hscaled := (convex_convexHull ℝ U).smul_mem_of_zero_mem hz hmem
      ⟨hc.le, hnorm.ge.trans (mem_closedBall_zero_iff.mp hz')⟩
    rw [Finset.centerMass, smul_inv_smul₀ hc.ne'] at hscaled
    have hreal (i) : ((c i : ℝ) : ℂ) • w i = c i • w i := Complex.coe_smul _ _
    rw [hrepr]
    change (∑ i ∈ s, ((c i : ℝ) : ℂ) • w i) ∈ convexHull ℝ U
    simpa only [hreal] using hscaled

private def projectiveModelToOperator : Completion πW →L[ℂ] (E →L[ℂ] F) :=
  completedProjectiveTensorToOperators.comp fromProjectiveSeminorm.completion

private theorem projectiveModelToOperator_coe (w : πW) :
    projectiveModelToOperator (w : Completion πW) = tensorToFiniteRank w :=
  (congrArg completedProjectiveTensorToOperators
    (fromProjectiveSeminorm.completion_apply_coe w)).trans (completedProjectiveTensorToOperators_coe _)

private theorem test_projectiveModel_le (τ : (E →L[ℂ] F) →L[ℂ] ℂ)
    (hτ : ∀ (φ : StrongDual ℂ E) (y : F), ‖τ (φ.smulRight y)‖ ≤ ‖φ‖ * ‖y‖)
    (z : Completion πW) : ‖τ (projectiveModelToOperator z)‖ ≤ ‖z‖ := by
  refine Completion.induction_on z (isClosed_le (τ.continuous.comp projectiveModelToOperator.continuous).norm
    continuous_norm) fun w ↦ ?_
  rw [projectiveModelToOperator_coe, Completion.norm_coe]
  exact test_tensorToFiniteRank_le τ hτ w

private theorem projectiveModel_singular_sum (z : Completion πW) :
    ∃ d : SingularExpansion (projectiveModelToOperator z), HasSum (fun n ↦ (d.coeff n : ℝ)) ‖z‖ := by
  classical
  let K := projectiveModelToOperator (E := E) (F := F)
  have hcompact : IsCompactOperator (K z) := by
    refine Completion.induction_on z (isClosed_setOfPred_isCompactOperator.preimage K.continuous) fun w ↦ ?_
    exact (projectiveModelToOperator_coe w).symm ▸ (tensorToFiniteRank_mem_schattenClass one_le_two w).1
  obtain ⟨d⟩ := (isCompactOperator_iff_nonempty_singularExpansion (K z)).mp hcompact
  let I := {n // d.coeff n ≠ 0}
  let c (i : I) : ℝ := d.coeff i
  have hbound (s : Finset I) : ∑ i ∈ s, c i ≤ ‖z‖ := by
    rw [← d.norm_diagonalTest_self]
    exact test_projectiveModel_le _ (d.diagonalTest_rankOne_le s) z
  have hs : Summable c := summable_of_sum_le (fun i ↦ (d.coeff i).2) hbound
  have htest (τ : (E →L[ℂ] F) →L[ℂ] ℂ)
      (hτ : ∀ (φ : StrongDual ℂ E) (y : F), ‖τ (φ.smulRight y)‖ ≤ ‖φ‖ * ‖y‖) :
      ‖τ (K z)‖ ≤ ∑' i, c i := by
    apply le_of_tendsto' (τ.hasSum d.hasSum_opNorm).norm
    intro s
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun i _ ↦ ?_).trans
      (hs.sum_le_tsum s fun i _ ↦ (d.coeff i).2))
    simp only [map_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg (NNReal.coe_nonneg _)]
    apply mul_le_of_le_one_right (d.coeff i).2
    simpa [innerSL_apply_norm, d.orthonormal_source.norm_eq_one, d.orthonormal_target.norm_eq_one] using
      hτ (innerSL ℂ (d.source i)) (d.target i)
  -- Choose a norming finite test for each algebraic approximation to z.
  have hreverse (u : Completion πW) : ‖u‖ ≤ ‖u - z‖ + ∑' i, c i := by
    refine Completion.induction_on u (isClosed_le continuous_norm
      ((continuous_id.sub continuous_const).norm.add continuous_const)) fun w ↦ ?_
    obtain ⟨d', s, _, hw⟩ := exists_finite_singularTensor w
    let τ := d'.diagonalTest s
    have hτ := d'.diagonalTest_rankOne_le s
    have hval : τ (K w) = τ (K ((w : Completion πW) - z)) + τ (K z) := by simp
    rw [Completion.norm_coe, hw, ← d'.norm_diagonalTest_self]
    refine (congrArg (fun A ↦ ‖τ A‖) (projectiveModelToOperator_coe w).symm).le.trans ?_
    change ‖τ (K w)‖ ≤ _
    rw [hval]
    exact (norm_add_le _ _).trans (add_le_add (test_projectiveModel_le _ hτ _) (htest _ hτ))
  have heq : (∑' i, c i) = ‖z‖ := le_antisymm (hs.tsum_le_of_sum_le hbound) (by simpa using hreverse z)
  refine ⟨d, (hasSum_subtype_iff_of_support_subset (s := {n | d.coeff n ≠ 0}) ?_).mp (heq ▸ hs.hasSum)⟩
  intro n hn hz
  exact hn (by simp [hz])

private theorem exists_projectiveModel_preimage (T : traceClassOperators E F) :
    ∃ z : Completion πW, projectiveModelToOperator z = T.val := by
  obtain ⟨d⟩ := (isCompactOperator_iff_nonempty_singularExpansion T.val).mp T.property.1
  let I := {n // d.coeff n ≠ 0}
  let w (i : I) : πW := innerSL ℂ (d.source i) ⊗ₜ[ℂ] d.target i
  have hs : Summable (fun n ↦ (d.coeff n : ℝ)) := by
    simpa only [Real.rpow_one, d.coeff_eq_approximationNumber] using T.property.2
  have hseries : Summable (fun i : I ↦ ((d.coeff i : ℝ) : ℂ) • (w i : Completion πW)) := by
    refine (hs.subtype (fun n ↦ d.coeff n ≠ 0)).of_norm_bounded fun i ↦ ?_
    simp only [norm_smul, Complex.norm_real, Real.norm_of_nonneg (NNReal.coe_nonneg _), Completion.norm_coe]
    refine mul_le_of_le_one_right (d.coeff i).2 ?_
    exact (projectiveSeminorm_tmul_le _ _).trans_eq (by
      rw [innerSL_apply_norm, d.orthonormal_source.norm_eq_one, d.orthonormal_target.norm_eq_one, one_mul])
  obtain ⟨z, hz⟩ := hseries
  refine ⟨z, (projectiveModelToOperator.hasSum hz).unique ?_⟩
  apply d.hasSum_opNorm.congr_fun
  intro i
  rw [map_smul, projectiveModelToOperator_coe]
  rfl

/-- Paper: Proposition C.3.6.4(3), p. 705. The completed projective tensor map
is a linear isometry onto the trace-class operators. On algebraic tensors
the projective norm is the gauge of the absolutely convex hull of elementary
tensors from the two unit balls. These tensors are already closed under
scalars of modulus at most one.
Deviation: The norm on the existing projective completion is expressed as the
continuous extension of this gauge. -/
theorem exists_projectiveTensorCompletion_traceClassIsometry :
    let projectiveNorm : ProjectiveTensor (StrongDual ℂ E) F → ℝ :=
      gauge (convexHull ℝ (Set.image2 (TensorProduct.tmul ℂ)
        (Metric.closedBall (0 : StrongDual ℂ E) 1) (Metric.closedBall (0 : F) 1)))
    UniformContinuous projectiveNorm ∧
      ∃ e : Completion (ProjectiveTensor (StrongDual ℂ E) F) ≃ₗ[ℂ] traceClassOperators E F,
        (∀ z, (e z).val = completedProjectiveTensorToOperators z) ∧
        ∀ z, schattenNorm (e z) = Completion.extension projectiveNorm z := by
  intro projectiveNorm
  let i : πP →L[ℂ] πW := toProjectiveSeminorm
  let j : πW →L[ℂ] πP := fromProjectiveSeminorm
  let A := completedProjectiveTensorToOperators (E := E) (F := F)
  have hji (z : Completion πP) : j.completion (i.completion z) = z := by
    refine Completion.induction_on z (isClosed_eq (j.completion.continuous.comp i.completion.continuous)
      continuous_id) fun w ↦ ?_
    rw [i.completion_apply_coe, j.completion_apply_coe]
    rfl
  have hK (z : Completion πP) : projectiveModelToOperator (i.completion z) = A z :=
    congrArg A (hji z)
  let g : πP → ℝ := fun z ↦ ‖i z‖
  have hg : UniformContinuous g := uniformContinuous_norm.comp i.uniformContinuous
  have hext (z : Completion πP) : Completion.extension g z = ‖i.completion z‖ := by
    refine Completion.induction_on z (isClosed_eq Completion.continuous_extension
      i.completion.continuous.norm) fun w ↦ ?_
    rw [Completion.extension_coe hg, i.completion_apply_coe, Completion.norm_coe]
  have hgauge : projectiveNorm = g := by
    funext z
    change gauge (convexHull ℝ (image2 (fun (φ : StrongDual ℂ E) (y : F) ↦ (show πW from φ ⊗ₜ[ℂ] y))
      (Metric.closedBall 0 1) (Metric.closedBall 0 1))) (i z) = ‖i z‖
    rw [projective_unitHull_eq_closedBall, gauge_closedBall zero_le_one, div_one]
  rw [hgauge]
  have hsum (z : Completion πP) : HasSum (fun n ↦ approximationNumber (A z) n) ‖i.completion z‖ := by
    obtain ⟨d, hd⟩ := projectiveModel_singular_sum (i.completion z)
    simpa only [d.coeff_eq_approximationNumber, hK] using hd
  have hmem (z : Completion πP) : A z ∈ traceClassOperators E F := by
    obtain ⟨d, _⟩ := projectiveModel_singular_sum (i.completion z)
    refine ⟨hK z ▸ (isCompactOperator_iff_nonempty_singularExpansion _).mpr ⟨d⟩, ?_⟩
    simpa only [Real.rpow_one] using (hsum z).summable
  let f := A.toLinearMap.codRestrict (traceClassOperators E F) hmem
  have hf : Bijective f := by
    constructor
    · apply (injective_iff_map_eq_zero f).mpr
      intro z hz
      have hAz : A z = 0 := congrArg Subtype.val hz
      have hz' := hsum z
      rw [hAz] at hz'
      have hzero (n : ℕ) : approximationNumber (0 : E →L[ℂ] F) n = 0 :=
        approximationNumber_eq_zero_of_rank_le _ (by simp)
      have hi : i.completion z = 0 := norm_eq_zero.mp (hz'.unique (by simp [hzero]))
      rw [← hji z, hi, map_zero]
    · intro T
      obtain ⟨z, hz⟩ := exists_projectiveModel_preimage T
      exact ⟨j.completion z, Subtype.ext hz⟩
  refine ⟨hg, LinearEquiv.ofBijective f hf, fun z ↦ rfl, fun z ↦ ?_⟩
  change (∑' n, approximationNumber (A z) n ^ (1 : ℝ)) ^ (1 / (1 : ℝ)) = Completion.extension g z
  simpa only [Real.rpow_one, div_one, hext] using (hsum z).tsum_eq

section TraceClassLimits

/-- Trace-norm convergence of operators represented by algebraic Hilbert-space tensors
gives convergence of the tensors in the completed projective tensor product. -/
theorem exists_tendsto_projectiveTensor_of_traceNorm {ι : Type*} (l : Filter ι)
    (w : ι → StrongDual ℂ E ⊗[ℂ] F) (T : traceClassOperators E F)
    (S : ι → traceClassOperators E F) (hS : ∀ i, tensorToFiniteRank (w i) = (S i).val)
    (hc : Tendsto (fun i ↦ schattenNorm (S i - T)) l (𝓝 0)) :
    ∃ k : Completion πP, Tendsto (fun i ↦ ((show πP from w i) : Completion πP)) l (𝓝 k) := by
  let toW : πP →L[ℂ] πW := toProjectiveSeminorm
  let fromW : πW →L[ℂ] πP := fromProjectiveSeminorm
  let R (i) : Completion πW := ↑(toW (w i))
  let L := projectiveModelToOperator (E := E) (F := F)
  obtain ⟨k, hk⟩ := exists_projectiveModel_preimage T
  have hn (v : Completion πW) (S : traceClassOperators E F) (hS : L v = S.val) :
      ‖v‖ = schattenNorm S := by
    obtain ⟨d, hd⟩ := projectiveModel_singular_sum (E := E) (F := F) v
    change _ = (∑' n, approximationNumber S.val n ^ (1 : ℝ)) ^ (1 / (1 : ℝ))
    rw [← hS]
    simpa only [d.coeff_eq_approximationNumber, Real.rpow_one, div_one, L] using hd.tsum_eq.symm
  have hconv : Tendsto R l (𝓝 k) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    apply hc.congr
    intro i
    apply Eq.symm
    apply hn (R i - k) _
    change L (R i - k) = (S i).val - T.val
    rw [← hS i]
    rw [map_sub, show L (R i) = tensorToFiniteRank (w i) from projectiveModelToOperator_coe _,
      show L k = T.val from hk]
  refine ⟨fromW.completion k, (fromW.completion.continuous.continuousAt.tendsto.comp hconv).congr ?_⟩
  intro i
  exact (fromW.completion_apply_coe (toW (w i))).trans rfl

end TraceClassLimits

omit [CompleteSpace F] in
/-- Every functional on the dual of a Hilbert space is evaluation at a vector of the same
norm. -/
private theorem exists_injectiveTensorCompletion_compactOperatorIsometry_eval
    (Φ : StrongDual ℂ (StrongDual ℂ E)) :
    ∃ x : E, ‖x‖ = ‖Φ‖ ∧ ∀ φ : StrongDual ℂ E, Φ φ = φ x := by
  let R := (InnerProductSpace.toDual ℂ E).symm
  let ψ := (InnerProductSpace.toDual ℂ (StrongDual ℂ E)).symm Φ
  refine ⟨R ψ, ?_, fun φ ↦ ?_⟩
  · rw [LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map]
  · have hΦ : Φ = InnerProductSpace.toDual ℂ (StrongDual ℂ E) ψ :=
      ((InnerProductSpace.toDual ℂ (StrongDual ℂ E)).apply_symm_apply Φ).symm
    rw [hΦ, InnerProductSpace.toDual_apply_apply, strongDual_inner_eq,
      InnerProductSpace.toDual_symm_apply]

omit [CompleteSpace F] in
/-- On the dual of a Hilbert space, the injective norm of an algebraic tensor is the
operator norm of the associated finite-rank map. -/
private theorem exists_injectiveTensorCompletion_compactOperatorIsometry_norm
    (z : StrongDual ℂ E ⊗[ℂ] F) :
    injectiveTensorNorm (StrongDual ℂ E) F z = ‖tensorToFiniteRank z‖ := by
  have hcomp' (w : StrongDual ℂ E ⊗[ℂ] F) (x : E) :
      tensorDualOperator w (NormedSpace.inclusionInDoubleDual ℂ E x) = tensorToFiniteRank w x := by
    induction w using TensorProduct.inductionOn with
    | tmul φ y => rw [tensorDualOperator_tmul, NormedSpace.dual_def, tensorToFiniteRank_tmul]
    | add w v hw hv => rw [map_add, LinearMap.add_apply, hw, hv, map_add, add_apply]
  obtain ⟨T, hT, hnorm⟩ := injectiveTensorNorm_eq_opNorm (E := StrongDual ℂ E) (F := F) z
  have hcomp (x : E) : T (NormedSpace.inclusionInDoubleDual ℂ E x) = tensorToFiniteRank z x :=
    (LinearMap.congr_fun hT _).trans (hcomp' z x)
  rw [hnorm]
  apply le_antisymm
  · refine T.opNorm_le_bound (norm_nonneg _) fun Φ ↦ ?_
    obtain ⟨x, hx, hΦ⟩ := exists_injectiveTensorCompletion_compactOperatorIsometry_eval Φ
    have hΦx : Φ = NormedSpace.inclusionInDoubleDual ℂ E x := ContinuousLinearMap.ext hΦ
    calc ‖T Φ‖ = ‖tensorToFiniteRank z x‖ := by rw [hΦx, hcomp]
      _ ≤ ‖tensorToFiniteRank z‖ * ‖x‖ := (tensorToFiniteRank z).le_opNorm x
      _ = ‖tensorToFiniteRank z‖ * ‖Φ‖ := by rw [hx]
  · refine (tensorToFiniteRank z).opNorm_le_bound (norm_nonneg _) fun x ↦ ?_
    rw [← hcomp]
    exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left
      (NormedSpace.double_dual_bound ℂ E x) (norm_nonneg _))

/-- Paper: Proposition C.3.6.4(3), p. 705. The canonical map extends to the
injective tensor completion as a linear isometry onto the compact operators
with the operator norm.
Deviation: The norm on the existing injective completion is expressed as the
continuous extension of the unit-ball injective norm. -/
theorem exists_injectiveTensorCompletion_compactOperatorIsometry :
    let injectiveNorm : InjectiveTensor (StrongDual ℂ E) F → ℝ :=
      injectiveTensorNorm (StrongDual ℂ E) F
    UniformContinuous injectiveNorm ∧
      ∃ e : Completion (InjectiveTensor (StrongDual ℂ E) F) →L[ℂ] (E →L[ℂ] F),
        (∀ z : InjectiveTensor (StrongDual ℂ E) F, e z = tensorToFiniteRank z) ∧
        Set.range e = {T : E →L[ℂ] F | IsCompactOperator T} ∧
        ∀ z, ‖e z‖ = Completion.extension injectiveNorm z := by
  intro injectiveNorm
  let X := InjectiveTensor (StrongDual ℂ E) F
  have hW := injectiveTensorNorm_withSeminorms (E := StrongDual ℂ E) (F := F)
  let s : Seminorm ℂ X := injectiveTensorNorm (StrongDual ℂ E) F
  have hs : Continuous s := hW.continuous_seminorm ()
  have huc : UniformContinuous injectiveNorm :=
    Seminorm.uniformContinuous_of_continuousAt_zero (p := s) hs.continuousAt
  have hnorm (z : X) : injectiveNorm z = ‖tensorToFiniteRank z‖ :=
    exists_injectiveTensorCompletion_compactOperatorIsometry_norm z
  let l : X →ₗ[ℂ] (E →L[ℂ] F) := tensorToFiniteRank
  have hl : Continuous l :=
    (norm_withSeminorms ℂ (E →L[ℂ] F)).continuous_of_continuous_comp l fun _ ↦
      Seminorm.continuous_of_le hs fun z ↦ (hnorm z).ge
  let L : X →L[ℂ] (E →L[ℂ] F) := ⟨l, hl⟩
  -- The injective topology is induced by the operator norm.
  have hind : Topology.IsInducing L := by
    have h0 : 𝓝 (0 : X) = Filter.comap s (𝓝 0) := by
      simpa only [iInf_const] using (SeminormFamily.withSeminorms_iff_nhds_eq_iInf _).mp hW
    rw [IsTopologicalAddGroup.isInducing_iff_nhds_zero, h0,
      ← comap_norm_nhds_zero (E := E →L[ℂ] F), Filter.comap_comap]
    congr 1
    funext z
    exact hnorm z
  have hui : IsUniformInducing L := AddMonoidHom.isUniformInducing_of_isInducing hind
  let e := L.fromCompletion
  have he (z : X) : e z = tensorToFiniteRank z := L.fromCompletion_apply_coe z
  refine ⟨huc, e, he, ?_, fun z ↦ ?_⟩
  · ext T
    constructor
    · rintro ⟨z, rfl⟩
      refine Completion.induction_on z
        (isClosed_setOfPred_isCompactOperator.preimage e.continuous) fun w ↦ ?_
      change IsCompactOperator (e w)
      rw [he]
      exact (tensorToFiniteRank_mem_schattenClass one_le_two w).1
    · intro hT
      obtain ⟨d⟩ := (isCompactOperator_iff_nonempty_singularExpansion T).mp hT
      let v (t : Finset {n // d.coeff n ≠ 0}) : StrongDual ℂ E ⊗[ℂ] F :=
        ∑ i ∈ t, (((d.coeff i : ℝ) : ℂ) • innerSL ℂ (d.source i)) ⊗ₜ[ℂ] d.target i
      let w (t : Finset {n // d.coeff n ≠ 0}) : X := v t
      have hLw (t : Finset {n // d.coeff n ≠ 0}) : L (w t) = ∑ i ∈ t, ((d.coeff i : ℝ) : ℂ) •
          (innerSL ℂ (d.source i)).smulRight (d.target i) := by
        change tensorToFiniteRank (v t) = _
        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        ext x
        rw [tensorToFiniteRank_tmul]
        simp only [smul_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
          smul_eq_mul, smul_smul]
      have h0 : Tendsto (fun t : Finset {n // d.coeff n ≠ 0} ↦ ∑ i ∈ t, ((d.coeff i : ℝ) : ℂ) •
          (innerSL ℂ (d.source i)).smulRight (d.target i)) atTop (𝓝 T) := d.hasSum_opNorm
      have hlim : Tendsto (fun t ↦ L (w t)) atTop (𝓝 T) :=
        h0.congr fun t ↦ (hLw t).symm
      have hc : Cauchy (map w atTop) := by
        rw [← hui.cauchy_map_iff, Filter.map_map]
        exact hlim.cauchy_map
      obtain ⟨z, hz⟩ := CompleteSpace.complete (hc.map (Completion.uniformContinuous_coe X))
      have hz' : Tendsto (fun t ↦ (w t : Completion X)) atTop (𝓝 z) := by
        rw [Filter.map_map] at hz
        exact hz
      refine ⟨z, tendsto_nhds_unique ?_ hlim⟩
      exact ((e.continuous.tendsto z).comp hz').congr fun t ↦ he (w t)
  · refine Completion.induction_on z
      (isClosed_eq e.continuous.norm Completion.continuous_extension) fun w ↦ ?_
    rw [he, Completion.extension_coe huc]
    exact (hnorm w).symm

end TensorProducts

section SchattenConvergence

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {p : ℝ} {hp : 1 ≤ p}

-- TODO(paper-gap): The proof uses the false Lemma C.3.6.3(1) for the triangle
-- inequality and prints repeated factors in (C.3.6.13), (C.3.6.14) and (C.3.6.17).

omit [CompleteSpace E] [CompleteSpace F] in
private theorem approx_nonneg (T : E →L[ℂ] F) (n : ℕ) : 0 ≤ approximationNumber T n :=
  le_csInf ⟨_, 0, by simp, rfl⟩ (fun _ ⟨S, _, h⟩ ↦ h ▸ norm_nonneg _)

/-- Apply a bounded linear operation to every competing finite-rank approximant. -/
private theorem approximationNumber_map_le (L : (E →L[ℂ] F) →L[ℂ] (E →L[ℂ] F))
    (A : E →L[ℂ] F) {m n : ℕ}
    (hr : ∀ S : E →L[ℂ] F, S.toLinearMap.rank ≤ (m : Cardinal) →
      (L S).toLinearMap.rank ≤ (n : Cardinal)) :
    approximationNumber (L A) n ≤ ‖L‖ * approximationNumber A m := by
  refine le_mul_of_forall_lt₀ fun a ha b hb ↦ ?_
  obtain ⟨S, hS, herr⟩ := exists_approximation_of_lt hb
  calc
    approximationNumber (L A) n ≤ ‖L S - L A‖ :=
      csInf_le ⟨0, fun _ ⟨R, _, h⟩ ↦ h ▸ norm_nonneg _⟩ ⟨_, hr S hS, rfl⟩
    _ ≤ ‖L‖ * ‖S - A‖ := by rw [← map_sub]; exact L.le_opNorm _
    _ ≤ a * b := mul_le_mul ha.le herr.le (norm_nonneg _) ((norm_nonneg L).trans ha.le)

private def composeBoth (C : F →L[ℂ] F) (B : E →L[ℂ] E) :
    (E →L[ℂ] F) →L[ℂ] (E →L[ℂ] F) :=
  (ContinuousLinearMap.compL ℂ E F F C).comp ((ContinuousLinearMap.compL ℂ E E F).flip B)

omit [CompleteSpace E] [CompleteSpace F] in
private theorem norm_composeBoth_le (C : F →L[ℂ] F) (B : E →L[ℂ] E) :
    ‖composeBoth C B‖ ≤ ‖C‖ * ‖B‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun S ↦ ?_
  calc
    ‖C.comp (S.comp B)‖ ≤ ‖C‖ * (‖S‖ * ‖B‖) :=
      (C.opNorm_comp_le _).trans (mul_le_mul_of_nonneg_left (S.opNorm_comp_le _) (norm_nonneg _))
    _ = _ := by ring

omit [CompleteSpace E] [CompleteSpace F] in
private theorem rank_composeBoth_le (C : F →L[ℂ] F) (B : E →L[ℂ] E) (S : E →L[ℂ] F) :
    (composeBoth C B S).toLinearMap.rank ≤ S.toLinearMap.rank :=
  (LinearMap.rank_comp_le_right (S.comp B).toLinearMap C.toLinearMap).trans
    (LinearMap.rank_comp_le_left B.toLinearMap S.toLinearMap)

private theorem composeBoth_mem (C : F →L[ℂ] F) (B : E →L[ℂ] E) (A : schattenClass E F p hp) :
    composeBoth C B A.val ∈ schattenClass E F p hp := by
  let L := composeBoth C B
  refine ⟨(A.property.1.comp_clm B).clm_comp C, (A.property.2.mul_left (‖L‖ ^ p)).of_nonneg_of_le
    (fun n ↦ Real.rpow_nonneg (approx_nonneg _ _) _) (fun n ↦ ?_)⟩
  rw [← Real.mul_rpow (norm_nonneg L) (approx_nonneg A.val n)]
  exact Real.rpow_le_rpow (approx_nonneg _ _)
    (approximationNumber_map_le L A.val (fun S hS ↦ (rank_composeBoth_le C B S).trans hS))
    (zero_le_one.trans hp)

private theorem exists_opNorm_bound_of_pointwise (B : E →L[ℂ] E) (B' : ℕ → E →L[ℂ] E)
    (h : ∀ x, Tendsto (fun k ↦ B' k x) atTop (𝓝 (B x))) :
    ∃ M : ℝ≥0, ∀ k, ‖B' k‖ ≤ M := by
  obtain ⟨M, hM⟩ := banach_steinhaus (g := B') fun x ↦ by
    obtain ⟨m, hm⟩ := (Metric.isBounded_range_of_tendsto _ (h x)).exists_norm_le
    exact ⟨m, fun k ↦ hm _ (mem_range_self k)⟩
  exact ⟨⟨M, (norm_nonneg _).trans (hM 0)⟩, hM⟩

private theorem tendsto_schatten_series {ι : Type*} {l : Filter ι}
    (A : schattenClass E F p hp) (T : ι → E →L[ℂ] F) (hop : Tendsto T l (𝓝 0))
    (M : ℝ≥0) (hbound : ∀ i n, approximationNumber (T i) n ≤ M * approximationNumber A.val (n / 2)) :
    Tendsto (fun i ↦ (∑' n, approximationNumber (T i) n ^ p) ^ (1 / p)) l (𝓝 0) := by
  have hp' : 0 < p := zero_lt_one.trans_le hp
  have hterm (n : ℕ) : Tendsto (fun i ↦ approximationNumber (T i) n ^ p) l (𝓝 0) := by
    have hzero : approximationNumber (0 : E →L[ℂ] F) n = 0 :=
      approximationNumber_eq_zero_of_rank_le _ (by simp)
    have hlim := squeeze_zero (fun i ↦ approx_nonneg (T i) n)
      (fun i ↦ by simpa [hzero, abs_of_nonneg (approx_nonneg _ _)] using
        abs_approximationNumber_sub_le (T i) (0 : E →L[ℂ] F) n) (by simpa using hop.norm)
    simpa [Real.zero_rpow hp'.ne'] using hlim.rpow_const (Or.inr hp'.le)
  let major (n : ℕ) := (M : ℝ) ^ p * approximationNumber A.val (n / 2) ^ p
  have hmajor : Summable major := by
    have hs := A.property.2.mul_left ((M : ℝ) ^ p)
    apply Summable.even_add_odd
    · simpa [major] using hs
    · exact hs.congr fun n ↦ by simp [major, show (2 * n + 1) / 2 = n by omega]
  have hsum := tendsto_tsum_of_dominated_convergence hmajor hterm (Eventually.of_forall fun i n ↦ by
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (approx_nonneg _ _) _)]
    exact (Real.rpow_le_rpow (approx_nonneg _ _) (hbound i n) hp'.le).trans_eq
      (Real.mul_rpow M.2 (approx_nonneg _ _)))
  simpa only [tsum_zero, Real.zero_rpow (by positivity : (1 / p) ≠ 0)] using
    hsum.rpow_const (Or.inr (by positivity : 0 ≤ 1 / p))

omit [CompleteSpace E] [CompleteSpace F] in
private theorem rank_sub_le (S T : E →L[ℂ] F) :
    (S - T).toLinearMap.rank ≤ S.toLinearMap.rank + T.toLinearMap.rank := by
  rw [sub_eq_add_neg, ContinuousLinearMap.toLinearMap_add, ContinuousLinearMap.toLinearMap_neg]
  exact (LinearMap.rank_add_le S.toLinearMap (-T.toLinearMap)).trans_eq
    (congrArg (fun V : Submodule ℂ F ↦ S.toLinearMap.rank + Module.rank ℂ V) (LinearMap.range_neg T.toLinearMap))

/-- Uniformly bounded left factors and adjoints of right factors converge on
rank-one operators, hence on compact operators in operator norm. The difference
of two compositions sends a rank-n approximant to one of rank at most 2n. -/
private theorem tendsto_schattenNorm_composeBoth {ι : Type*} {l : Filter ι}
    (A : schattenClass E F p hp) (B' : ι → E →L[ℂ] E) (B : E →L[ℂ] E)
    (C' : ι → F →L[ℂ] F) (C : F →L[ℂ] F)
    (hB : ∀ x, Tendsto (fun i ↦ (B' i).adjoint x) l (𝓝 (B.adjoint x)))
    (hC : ∀ y, Tendsto (fun i ↦ C' i y) l (𝓝 (C y)))
    (b c : ℝ≥0) (hb : ∀ i, ‖B' i‖ ≤ b) (hc : ∀ i, ‖C' i‖ ≤ c) :
    Tendsto (fun i ↦ schattenNorm
      ((⟨composeBoth (C' i) (B' i) A.val, composeBoth_mem _ _ A⟩ : schattenClass E F p hp) -
        ⟨composeBoth C B A.val, composeBoth_mem _ _ A⟩)) l (𝓝 0) := by
  let D (i : ι) := composeBoth (C' i) (B' i) - composeBoth C B
  let M := c * b + ‖composeBoth C B‖₊
  have hD (i : ι) : ‖D i‖ ≤ M :=
    (norm_sub_le (composeBoth (C' i) (B' i)) (composeBoth C B)).trans (add_le_add_left ((norm_composeBoth_le _ _).trans
      (mul_le_mul (hc i) (hb i) (norm_nonneg _) c.2)) _)
  have heq : Equicontinuous (fun i S ↦ D i S) :=
    (LipschitzWith.uniformEquicontinuous _ M (fun i ↦
      (D i).lipschitzWith.weaken (by exact_mod_cast hD i))).equicontinuous
  have hclosed := heq.isClosed_setOfPred_tendsto (l := l) (continuous_const (y := (0 : E →L[ℂ] F)))
  obtain ⟨d⟩ := (isCompactOperator_iff_nonempty_singularExpansion A.val).mp A.property.1
  have hop : Tendsto (fun i ↦ D i A.val) l (𝓝 0) := by
    apply hclosed.mem_of_tendsto d.hasSum_opNorm
    refine Eventually.of_forall fun s ↦ ?_
    change Tendsto (fun i ↦ D i (∑ j ∈ s, _)) l (𝓝 0)
    simp only [map_sum, map_smul]
    rw [← Finset.sum_const_zero (s := s) (M := E →L[ℂ] F)]
    apply tendsto_finsetSum
    intro j _
    have h := ((ContinuousLinearMap.smulRightL ℂ E F).continuous₂.tendsto
      (innerSL ℂ (B.adjoint (d.source j)), C (d.target j))).comp
      ((((innerSL ℂ).continuous.tendsto _).comp (hB _)).prodMk_nhds (hC _))
    change Tendsto (fun i ↦ InnerProductSpace.rankOne ℂ (C' i (d.target j)) ((B' i).adjoint (d.source j)))
      l (𝓝 (InnerProductSpace.rankOne ℂ (C (d.target j)) (B.adjoint (d.source j)))) at h
    have hsub := h.sub (tendsto_const_nhds (x := InnerProductSpace.rankOne ℂ (C (d.target j)) (B.adjoint (d.source j))))
    change Tendsto (fun i ↦ ((d.coeff j : ℝ) : ℂ) • ((C' i).comp
      ((InnerProductSpace.rankOne ℂ (d.target j) (d.source j)).comp (B' i)) -
      C.comp ((InnerProductSpace.rankOne ℂ (d.target j) (d.source j)).comp B))) l (𝓝 0)
    simp only [InnerProductSpace.rankOne_comp, InnerProductSpace.comp_rankOne]
    simpa only [sub_self, smul_zero] using
      hsub.const_smul (((d.coeff j : ℝ) : ℂ))
  have hσ (i : ι) (n : ℕ) :
      approximationNumber (D i A.val) n ≤ M * approximationNumber A.val (n / 2) := by
    refine (approximationNumber_map_le (D i) A.val (fun S hS ↦ ?_)).trans
      (mul_le_mul_of_nonneg_right (hD i) (approx_nonneg _ _))
    have hr (C₀ : F →L[ℂ] F) (B₀ : E →L[ℂ] E) := (rank_composeBoth_le C₀ B₀ S).trans hS
    refine (rank_sub_le _ _).trans ((add_le_add (hr (C' i) (B' i)) (hr C B)).trans ?_)
    exact_mod_cast (show n / 2 + n / 2 ≤ n by omega)
  exact tendsto_schatten_series A _ hop M hσ

/-- Paper: Proposition C.3.6.5, p. 705. Left composition by a strongly convergent
sequence of operators converges in the Schatten norm for a fixed right factor in
the class. Each composition and its limit belong to the class.
Deviation: The independent left-composition assertion uses only the left sequence. -/
theorem tendsto_schattenNorm_comp_left (A : schattenClass E F p hp)
    (Cj : ℕ → F →L[ℂ] F) (C : F →L[ℂ] F)
    (hC : ∀ y, Tendsto (fun j ↦ Cj j y) atTop (𝓝 (C y))) :
    ∃ (hj : ∀ j, (Cj j).comp A.val ∈ schattenClass E F p hp)
      (hlim : C.comp A.val ∈ schattenClass E F p hp),
      Tendsto (fun j ↦ schattenNorm
        ((⟨(Cj j).comp A.val, hj j⟩ : schattenClass E F p hp) - ⟨C.comp A.val, hlim⟩))
        atTop (𝓝 0) := by
  let I := ContinuousLinearMap.id ℂ E
  obtain ⟨c, hc⟩ := exists_opNorm_bound_of_pointwise C Cj hC
  refine ⟨fun j ↦ by simpa [composeBoth, I] using composeBoth_mem (Cj j) I A,
    by simpa [composeBoth, I] using composeBoth_mem C I A, ?_⟩
  simpa [composeBoth, I] using tendsto_schattenNorm_composeBoth A (fun _ ↦ I) I Cj C
    (fun _ ↦ tendsto_const_nhds) hC ‖I‖₊ c (fun _ ↦ le_rfl) hc

private theorem adjoint_eq_of_pointwise_selfAdjoint (B : E →L[ℂ] E) (B' : ℕ → E →L[ℂ] E)
    (h : ∀ x, Tendsto (fun k ↦ B' k x) atTop (𝓝 (B x))) (hs : ∀ k, IsSelfAdjoint (B' k)) :
    B.adjoint = B := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  rw [B.adjoint_inner_left]
  exact tendsto_nhds_unique ((tendsto_const_nhds.inner (h y)).congr fun k ↦ by
    rw [← (B' k).adjoint_inner_left, (hs k).adjoint_eq]) ((h x).inner tendsto_const_nhds)

/-- Paper: Proposition C.3.6.5, p. 705. Right composition by a strongly
convergent sequence of self-adjoint operators converges in the Schatten norm
for a fixed left factor in the class. Each composition and its limit belong to the class.
Deviation: The independent right-composition assertion uses only the right sequence. -/
theorem tendsto_schattenNorm_comp_right (A : schattenClass E F p hp)
    (Bk : ℕ → E →L[ℂ] E) (B : E →L[ℂ] E)
    (hB : ∀ x, Tendsto (fun k ↦ Bk k x) atTop (𝓝 (B x)))
    (hself : ∀ k, IsSelfAdjoint (Bk k)) :
    ∃ (hk : ∀ k, A.val.comp (Bk k) ∈ schattenClass E F p hp)
      (hlim : A.val.comp B ∈ schattenClass E F p hp),
      Tendsto (fun k ↦ schattenNorm
        ((⟨A.val.comp (Bk k), hk k⟩ : schattenClass E F p hp) - ⟨A.val.comp B, hlim⟩))
        atTop (𝓝 0) := by
  let I := ContinuousLinearMap.id ℂ F
  obtain ⟨b, hb⟩ := exists_opNorm_bound_of_pointwise B Bk hB
  have hadj (x : E) : Tendsto (fun k ↦ (Bk k).adjoint x) atTop (𝓝 (B.adjoint x)) := by
    simpa only [(hself _).adjoint_eq, adjoint_eq_of_pointwise_selfAdjoint B Bk hB hself] using hB x
  refine ⟨fun k ↦ by simpa [composeBoth, I] using composeBoth_mem I (Bk k) A,
    by simpa [composeBoth, I] using composeBoth_mem I B A, ?_⟩
  simpa [composeBoth, I] using tendsto_schattenNorm_composeBoth A Bk B (fun _ ↦ I) I
    hadj (fun _ ↦ tendsto_const_nhds) b ‖I‖₊ hb (fun _ ↦ le_rfl)

/-- Paper: Proposition C.3.6.5, p. 705. Simultaneous left and right
composition converges in the Schatten norm as both indices tend to infinity.
The two operator sequences converge strongly and the right factors are self-adjoint. -/
theorem tendsto_schattenNorm_comp_both (A : schattenClass E F p hp)
    (Bk : ℕ → E →L[ℂ] E) (B : E →L[ℂ] E)
    (hB : ∀ x, Tendsto (fun k ↦ Bk k x) atTop (𝓝 (B x)))
    (hself : ∀ k, IsSelfAdjoint (Bk k))
    (Cj : ℕ → F →L[ℂ] F) (C : F →L[ℂ] F)
    (hC : ∀ y, Tendsto (fun j ↦ Cj j y) atTop (𝓝 (C y))) :
    ∃ (hjk : ∀ j k, (Cj j).comp (A.val.comp (Bk k)) ∈ schattenClass E F p hp)
      (hlim : C.comp (A.val.comp B) ∈ schattenClass E F p hp),
      Tendsto (fun jk : ℕ × ℕ ↦ schattenNorm
        ((⟨(Cj jk.1).comp (A.val.comp (Bk jk.2)), hjk jk.1 jk.2⟩ : schattenClass E F p hp) -
          ⟨C.comp (A.val.comp B), hlim⟩)) atTop (𝓝 0) := by
  obtain ⟨b, hb⟩ := exists_opNorm_bound_of_pointwise B Bk hB
  obtain ⟨c, hc⟩ := exists_opNorm_bound_of_pointwise C Cj hC
  refine ⟨fun j k ↦ composeBoth_mem (Cj j) (Bk k) A, composeBoth_mem C B A, ?_⟩
  apply tendsto_schattenNorm_composeBoth A (fun jk : ℕ × ℕ ↦ Bk jk.2) B (fun jk ↦ Cj jk.1) C
    _ _ b c (fun jk ↦ hb jk.2) (fun jk ↦ hc jk.1)
  · intro x
    simp only [(hself _).adjoint_eq, adjoint_eq_of_pointwise_selfAdjoint B Bk hB hself]
    exact (hB x).comp (prod_atTop_atTop_eq (α := ℕ) (β := ℕ) ▸ tendsto_snd)
  · exact fun y ↦ (hC y).comp (prod_atTop_atTop_eq (α := ℕ) (β := ℕ) ▸ tendsto_fst)

end SchattenConvergence

section TraceClassEndomorphisms

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

-- TODO(paper-gap): Remark C.3.6.6 refers to Proposition C.3.6.5(2) for
-- the cofinal finite subsets. They are introduced in Proposition C.3.5.1.

omit [CompleteSpace H] in
/-- The positive square root acts by c on an eigenvector of its square of eigenvalue c². -/
private theorem apply_eq_smul_of_sq_apply {S : H →L[ℂ] H} (hS : S.IsPositive)
    (x : H) {c : ℝ} (hc : 0 < c) (h : S (S x) = (c : ℂ) • ((c : ℂ) • x)) :
    S x = (c : ℂ) • x := by
  let v := S x - (c : ℂ) • x
  have hv : S v = -(c : ℂ) • v := by
    simp only [v, map_sub, map_smul, h, neg_smul, smul_sub]
    abel
  have hpos := hS.re_inner_nonneg_right v
  rw [hv, inner_smul_right, inner_self_eq_norm_sq_to_K] at hpos
  have hv0 : ‖v‖ = 0 := by
    simp only [RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_neg, ← Complex.ofReal_pow,
      ← Complex.ofReal_mul] at hpos
    change 0 ≤ -c * ‖v‖ ^ 2 at hpos
    by_contra hn
    nlinarith [sq_nonneg ‖v‖, mul_pos hc (sq_pos_of_ne_zero hn)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hv0)

/-- Paper: Remark C.3.6.6, p. 707. The Schatten norm at index one equals
the earlier trace norm on nuclear endomorphisms. This is the norm identification
used when specializing Proposition C.3.6.5 to the projection results. -/
theorem schattenNorm_one_eq_traceNorm (T : nuclearEndomorphisms H) :
    schattenNorm ⟨T.val, (mem_traceClassOperators_iff_isNuclearOperator T.val).2 T.property⟩ =
      traceNorm T := by
  classical
  let S := CFC.sqrt (T.val.adjoint * T.val)
  have hS := ContinuousLinearMap.nonneg_iff_isPositive.mp (CFC.sqrt_nonneg (T.val.adjoint * T.val))
  have hsq : S * S = T.val.adjoint * T.val := CFC.sqrt_mul_sqrt_self _ <|
    ContinuousLinearMap.nonneg_iff_isPositive.mpr T.val.isPositive_adjoint_comp_self
  obtain ⟨d⟩ := (isCompactOperator_iff_nonempty_singularExpansion T.val).mp
    (isCompactOperator_of_isNuclearOperator T.property)
  obtain ⟨w, b, j, hj, hb, hvanish⟩ := d.exists_source_basis
  let I := {n // d.coeff n ≠ 0}
  have hadj (i : I) : T.val.adjoint (d.target i) = ((d.coeff i : ℝ) : ℂ) • d.source i := by
    apply ext_inner_right ℂ
    intro x
    rw [T.val.adjoint_inner_left, inner_smul_left]
    have hs := (innerSL ℂ (d.target i)).hasSum (d.hasSum_apply x)
    change HasSum (fun k : I ↦ ⟪d.target i, _⟫_ℂ) ⟪d.target i, T.val x⟫_ℂ at hs
    rw [hs.unique (hasSum_single i (fun k hk ↦ by simp [inner_smul_right,
      d.orthonormal_target.inner_eq_zero hk.symm]))]
    simp [inner_smul_right, d.orthonormal_target.norm_eq_one]
  let diag (a : w) := (⟪b a, S (b a)⟫_ℂ).re
  have hdiag (i : I) : diag (j i) = (d.coeff i : ℝ) := by
    have heig : S (d.source i) = ((d.coeff i : ℝ) : ℂ) • d.source i := by
      apply apply_eq_smul_of_sq_apply hS _ (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr i.2))
      change (S * S) (d.source i) = _
      rw [hsq, mul_apply_eq_comp, d.apply_source, map_smul, hadj]
    change (⟪b (j i), S (b (j i))⟫_ℂ).re = _
    rw [hb, heig, inner_smul_right]
    simp [d.orthonormal_source.norm_eq_one]
  have hzero (a : w) (ha : a ∉ range j) : diag a = 0 := by
    have hs : S (b a) = 0 := by
      apply norm_eq_zero.mp
      rw [S.apply_norm_eq_sqrt_inner_adjoint_right, hS.isSelfAdjoint.adjoint_eq,
        ← ContinuousLinearMap.mul_def, hsq, mul_apply_eq_comp, hvanish a ha]
      simp
    simp [diag, hs]
  have hs : HasSum diag (traceNorm T) := hasSum_traceNorm_diagonal b T
  have hcoeff := ((hj.hasSum_iff hzero).mpr hs).congr_fun (fun i ↦ (hdiag i).symm)
  have hfull : HasSum (fun n ↦ (d.coeff n : ℝ)) (traceNorm T) :=
    (hasSum_subtype_iff_of_support_subset (s := {n | d.coeff n ≠ 0}) (by
      intro n hn hz; exact hn (by simp [hz]))).mp hcoeff
  simpa only [schattenNorm, Real.rpow_one, div_one, ← d.coeff_eq_approximationNumber] using hfull.tsum_eq

end TraceClassEndomorphisms

end RiemannMasullo
