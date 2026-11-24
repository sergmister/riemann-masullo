module

public import RiemannMasullo.AppA_AlgebraicNT.Sec3
public import RiemannMasullo.Ch02_AdelicTheta.Sec1
public import RiemannMasullo.ForMathlib.Topology.Algebra.InfiniteSum
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.LinearAlgebra.Countable
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace

/-!
# Global adelic theta functions

Masullo, §§2.2.1–2.2.3, pp. 74–86. The theta operator sums over nonzero field
elements, with the additive Tamagawa measure used for its Fourier identity.
-/

@[expose] public noncomputable section

open Bornology Filter Function MeasureTheory NumberField Set Topology
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo

section Lattice

/-- Paper: Equation (2.2.1.1), p. 75. The shell consists of vectors with
supremum norm in the half-open interval of width one starting at `r`. -/
def euclideanSupNormShell (N : ℕ) (r : ℝ) : Set (Fin N → ℝ) :=
  {x | ‖x‖ ∈ Ico r (r + 1)}

/-- Paper: Equation (2.2.1.1), p. 75. In dimension one the shell uses the
absolute value of the single coordinate, with the outer endpoint excluded. -/
theorem mem_euclideanSupNormShell_one (x r : ℝ) :
    (fun _ : Fin 1 ↦ x) ∈ euclideanSupNormShell 1 r ↔ r ≤ |x| ∧ |x| < r + 1 := by
  simp [euclideanSupNormShell, Real.norm_eq_abs]

/-- Paper: Lemma 2.2.1.1, p. 75. Each shell is bounded in the supremum norm. -/
theorem euclideanSupNormShell_bounded {N : ℕ} (_hN : 1 ≤ N) {r : ℝ} (_hr : 1 ≤ r) :
    IsBounded (euclideanSupNormShell N r) := by
  apply (Metric.isBounded_ball (x := (0 : Fin N → ℝ)) (r := r + 1)).subset
  intro x hx
  simpa only [Metric.mem_ball, dist_zero_right] using hx.2

/-- Paper: Lemma 2.2.1.1, p. 75. Each shell is measurable for completed
Lebesgue measure. -/
theorem euclideanSupNormShell_lebesgueMeasurable {N : ℕ} (_hN : 1 ≤ N) {r : ℝ}
    (_hr : 1 ≤ r) :
    NullMeasurableSet (euclideanSupNormShell N r) volume := by
  exact (measurableSet_Ico.preimage continuous_norm.measurable).nullMeasurableSet

/-- Disjoint balls centered on lattice points fit into a thicker shell. -/
private theorem shell_packing {N : ℕ}
    (Γ : Submodule ℤ (Fin N → ℝ)) [DiscreteTopology Γ] :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 ∧ ∀ r : ℝ, 2 ≤ r →
      let S := (Γ : Set (Fin N → ℝ)) ∩ euclideanSupNormShell N r
      S.Finite ∧ (S.ncard : ℝ) * (2 * d) ^ N ≤ (2 * (r + 1 + d)) ^ N - (2 * (r - d)) ^ N := by
  classical
  obtain ⟨ε, hε, hiso⟩ := Metric.isOpen_iff.mp (isOpen_discrete ({0} : Set Γ)) 0 (by simp)
  let d := min (ε / 2) 1
  have hd : 0 < d := lt_min (by linarith) zero_lt_one
  have hd1 : d ≤ 1 := min_le_right _ _
  have hdε : d + d ≤ ε := by
    have hle := min_le_left (ε / 2) (1 : ℝ)
    dsimp [d]
    linarith
  refine ⟨d, hd, hd1, ?_⟩
  intro r hr S
  have hb : Bornology.IsBounded (euclideanSupNormShell N r) := by
    apply (Metric.isBounded_ball (x := (0 : Fin N → ℝ)) (r := r + 1)).subset
    intro x hx
    simpa only [Metric.mem_ball, dist_zero_right] using hx.2
  have hclosed : IsClosed (Γ : Set (Fin N → ℝ)) := by
    change IsClosed (Γ.toAddSubgroup : Set (Fin N → ℝ))
    exact AddSubgroup.isClosed_of_discreteTopology
  have hfin : S.Finite := by
    simpa [S, inter_comm] using
      Metric.finite_isBounded_inter_isClosed (s := (Γ : Set (Fin N → ℝ)))
        DiscreteTopology.isDiscrete hb hclosed
  refine ⟨hfin, ?_⟩
  let := hfin.fintype
  -- Discreteness at zero gives the same separation for every pair of lattice points.
  let balls := fun x : S => Metric.ball x.val d
  have hdis : Pairwise (Disjoint on balls) := by
    intro x y hne
    apply Metric.ball_disjoint_ball
    apply hdε.trans
    by_contra! h
    let z : Γ := ⟨x.val - y.val, Γ.sub_mem x.property.1 y.property.1⟩
    have hz : z ∈ Metric.ball (0 : Γ) ε := by
      simpa [z, Metric.mem_ball, dist_eq_norm] using h
    have hz0 : z = 0 := hiso hz
    apply hne
    exact Subtype.ext (sub_eq_zero.mp (congrArg Subtype.val hz0))
  have hbvol (x : Fin N → ℝ) {t : ℝ} (ht : 0 < t) :
      volume.real (Metric.ball x t) = (2 * t) ^ N := by
    simp [measureReal_def, Real.volume_pi_ball _ ht, ENNReal.toReal_ofReal (by positivity : 0 ≤ (2 * t) ^ N)]
  have heq : volume.real (⋃ x, balls x) = (S.ncard : ℝ) * (2 * d) ^ N := by
    rw [measureReal_iUnion_fintype hdis (fun _ => Metric.isOpen_ball.measurableSet)
      (fun x => by dsimp [balls]; rw [Real.volume_pi_ball _ hd]; exact ENNReal.ofReal_ne_top)]
    simp only [balls, hbvol _ hd, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  have hi : 0 < r - d := by linarith
  have ho : 0 < r + 1 + d := by linarith
  let outer := Metric.ball (0 : Fin N → ℝ) (r + 1 + d)
  let inner := Metric.ball (0 : Fin N → ℝ) (r - d)
  have hout : volume outer ≠ ⊤ := by
    rw [show outer = _ from rfl, Real.volume_pi_ball _ ho]
    exact ENNReal.ofReal_ne_top
  have hio : inner ⊆ outer := Metric.ball_subset_ball (by linarith)
  have hsub : (⋃ x, balls x) ⊆ outer \ inner := by
    intro y hy
    obtain ⟨x, hx⟩ := mem_iUnion.mp hy
    have hdxy : dist y x.val < d := hx
    have hnorm := abs_norm_sub_norm_le y x.val
    rw [← dist_eq_norm] at hnorm
    obtain ⟨h₁, h₂⟩ := abs_le.mp hnorm
    obtain ⟨hrx₁, hrx₂⟩ : r ≤ ‖x.val‖ ∧ ‖x.val‖ < r + 1 := x.property.2
    simp only [outer, inner, Set.mem_sdiff, Metric.mem_ball, dist_zero_right, not_lt]
    constructor <;> linarith
  have hdiff : volume.real (outer \ inner) = volume.real outer - volume.real inner := by
    have := measureReal_inter_add_sdiff (μ := volume) (s := outer)
      (t := inner) Metric.isOpen_ball.measurableSet hout
    rw [inter_eq_right.mpr hio] at this
    linarith
  calc
    _ = volume.real (⋃ x, balls x) := heq.symm
    _ ≤ volume.real (outer \ inner) :=
      measureReal_mono hsub (measure_ne_top_of_subset sdiff_subset hout)
    _ = _ := by rw [hdiff, hbvol _ ho, hbvol _ hi]


/-- A shell of fixed width has volume of order at most the radius to the power N − 1. -/
private theorem shell_pow_diff_bound (N : ℕ) (hN : 1 ≤ N) (d : ℝ)
    (hd : 0 < d) (hd' : d ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 2 ≤ r →
      (2 * (r + 1 + d)) ^ N - (2 * (r - d)) ^ N ≤ C * r ^ (N - 1) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N from hN)
  refine ⟨(2 + 4 * d) * N * 4 ^ (N - 1), by positivity, ?_⟩
  intro r hr
  let a := 2 * (r + 1 + d)
  let b := 2 * (r - d)
  have hb : 0 ≤ b := by dsimp [b]; linarith
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have hba : b ≤ a := by dsimp [a, b]; linarith
  have hdiff : a - b = 2 + 4 * d := by dsimp [a, b]; ring
  have htop : a ≤ 4 * r := by dsimp [a]; linarith
  calc
    a ^ N - b ^ N ≤ |a ^ N - b ^ N| := le_abs_self _
    _ ≤ |a - b| * N * max |a| |b| ^ (N - 1) := abs_pow_sub_pow_le a b N
    _ = (2 + 4 * d) * N * a ^ (N - 1) := by
      rw [abs_of_nonneg (sub_nonneg.mpr hba), hdiff, abs_of_nonneg ha, abs_of_nonneg hb, max_eq_left hba]
    _ ≤ (2 + 4 * d) * N * (4 * r) ^ (N - 1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha htop _) (by positivity)
    _ = _ := by rw [mul_pow]; ring

/-- Paper: Lemma 2.2.1.1, p. 75. For large radii, the shell has finitely many
lattice points and their number is at most a constant times `r ^ (N - 1)`. -/
theorem euclideanSupNormShell_lattice_count {N : ℕ} (_hN : 1 ≤ N)
    (Γ : Submodule ℤ (Fin N → ℝ)) [DiscreteTopology Γ] [IsZLattice ℝ Γ] :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ r : ℝ in atTop,
      ((Γ : Set (Fin N → ℝ)) ∩ euclideanSupNormShell N r).Finite ∧
      (((Γ : Set (Fin N → ℝ)) ∩ euclideanSupNormShell N r).ncard : ℝ) ≤
        C * r ^ (N - 1) := by
  obtain ⟨d, hd, hd', hpack⟩ := shell_packing Γ
  obtain ⟨C, hC, hpow⟩ := shell_pow_diff_bound N _hN d hd hd'
  have hvol : 0 < (2 * d) ^ N := by positivity
  refine ⟨C / (2 * d) ^ N, div_pos hC hvol, ?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with r hr
  obtain ⟨hfinite, hbound⟩ := hpack r hr
  refine ⟨hfinite, ?_⟩
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ hvol).mpr (hbound.trans (hpow r hr))

-- TODO(paper-gap): Proposition 2.2.1.3, p. 76, excludes Γ ∩ K from the sum,
-- but the term with ξ = -x can remain. Take Γ = ℤ, K = {1}, x = 1 and ξ = -1.

end Lattice

section Adelic

variable {F : Type*} [Field F] [NumberField F]

local notation "𝕀[" F "]" => IdeleGroup (𝓞 F) F
local notation "C[" F "]" => IdeleClassGroup (𝓞 F) F
local notation "ℬ[" F "]" => SchwartzBruhat (Multiplicative 𝔸[F])
local notation "normℝ" => fun (g : C[F]) ↦ ((ideleClassNorm F g : ℝ≥0) : ℝ)
local notation "classOf" => QuotientGroup.mk (s := IdeleGroup.principalSubgroup (𝓞 F) F)
local notation "zeroAdele" => Multiplicative.ofAdd (0 : 𝔸[F])

/-- Paper: Lemma 2.2.2.1, p. 77. The average sums the Schwartz–Bruhat function
at the adeles `g * (ξ + x)` as `ξ` ranges over the nonzero field elements. -/
def adelicAverage (f : ℬ[F]) (g : 𝕀[F]) (x : 𝔸[F]) : ℂ :=
  ∑' ξ : Fˣ, f (Multiplicative.ofAdd (g.val * (algebraMap F 𝔸[F] (ξ : F) + x)))

section AdelicAverageSummable

open IsDedekindDomain

open Classical in
/-- A stage realization evaluates the stage function at the quotient coordinate on the open
subgroup and vanishes outside it. -/
private theorem schwartzBruhatStageRealization_apply_dite {G : Type*} [CommGroup G] [TopologicalSpace G] (a : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation a.quotient) (f : SchwartzBruhatStage e) (x : G) :
    schwartzBruhatStageRealization a e f x =
      if hx : x ∈ a.val.1 then
        f (Multiplicative.toAdd (e.equiv (QuotientGroup.mk ⟨x, hx⟩)))
      else 0 :=
  schwartzBruhatStageRealization_apply a e f x

/-- A weighted bound of an elementary Schwartz function controls its pointwise size times the
real and lattice monomials. -/
private theorem elementarySchwartz_monomial_bound {m n r : ℕ} {Fk : Type*} [AddCommGroup Fk]
    [TopologicalSpace Fk] [DiscreteTopology Fk] [Finite Fk]
    {f : ElementaryLieGroup m n r Fk → ℂ} (hf : f ∈ elementarySchwartzSubmodule m n r Fk)
    (β : Fin m → ℕ) (δ : Fin r → ℕ) (w : ElementaryLieGroup m n r Fk) :
    (∏ k, |w.1 k| ^ β k) * (∏ k, |(w.2.2.1 k : ℝ)| ^ δ k) * ‖f w‖ ≤
      (elementarySchwartzBound f (β, 0, 0, δ)).toReal := by
  obtain ⟨t, ht⟩ := elementaryCover_surjective (F := Fk) w.2.2.1 w.2.2.2 w.1 w.2.1
  have hfin := hf.2 (β, 0, 0, δ)
  have hle : ((‖((∏ k, (w.1 k : ℂ) ^ β k) * (∏ k, (w.2.2.1 k : ℂ) ^ δ k)) *
      elementaryPartial f 0 0 (w.1, t) w.2.2.1 w.2.2.2‖₊ : ENNReal)) ≤
      elementarySchwartzBound f (β, 0, 0, δ) :=
    le_iSup_of_le (w.1, t) (le_iSup_of_le w.2.2.1 (le_iSup_of_le w.2.2.2 le_rfl))
  rw [elementaryPartial_zero, ht] at hle
  have := (ENNReal.toReal_le_toReal ENNReal.coe_ne_top hfin.ne).mpr hle
  simp only [ENNReal.coe_toReal, coe_nnNorm, norm_mul, norm_prod, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, Complex.norm_intCast] at this
  convert this using 3

/-- An elementary Schwartz function decays faster than any power of the real and lattice
coordinates. -/
private theorem elementarySchwartz_decay {m n r : ℕ} {Fk : Type*} [AddCommGroup Fk]
    [TopologicalSpace Fk] [DiscreteTopology Fk] [Finite Fk]
    {f : ElementaryLieGroup m n r Fk → ℂ} (hf : f ∈ elementarySchwartzSubmodule m n r Fk)
    (N : ℕ) : ∃ C : ℝ, ∀ w : ElementaryLieGroup m n r Fk,
      ‖f w‖ * (1 + (∑ j, |w.1 j| + ∑ k, |(w.2.2.1 k : ℝ)|)) ^ N ≤ C := by
  classical
  let B : ElementarySchwartzIndex m n r → ℝ := fun i => (elementarySchwartzBound f i).toReal
  let c : ℝ := Fintype.card (Option (Fin m ⊕ Fin r))
  refine ⟨c ^ N * (B (0, 0, 0, 0) + ∑ j, B (Pi.single j (N + 1), 0, 0, 0) +
    ∑ k, B (0, 0, 0, Pi.single k (N + 1))), fun w => ?_⟩
  let g : Option (Fin m ⊕ Fin r) → ℝ := fun i => match i with
    | none => 1
    | some (Sum.inl j) => |w.1 j|
    | some (Sum.inr k) => |(w.2.2.1 k : ℝ)|
  have hg0 : ∀ i ∈ Finset.univ, 0 ≤ g i := by
    rintro (_ | _ | _) _ <;> simp [g]
  have hsum : ∑ i, g i = 1 + (∑ j, |w.1 j| + ∑ k, |(w.2.2.1 k : ℝ)|) := by
    simp [g, Fintype.sum_option, Fintype.sum_sum_type]
  have hS1 : 1 ≤ ∑ i, g i := by
    rw [hsum]; have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => abs_nonneg (w.1 j))
    have := Finset.sum_nonneg (fun k (_ : k ∈ Finset.univ) => abs_nonneg ((w.2.2.1 k : ℝ)))
    linarith
  have hc : 0 < c := by positivity
  have hpow := pow_sum_div_card_le_sum_pow hg0 N
  rw [Finset.card_univ] at hpow
  have hpow' : (∑ i, g i) ^ (N + 1) ≤ c ^ N * ∑ i, g i ^ (N + 1) := by
    rwa [div_le_iff₀' (by positivity)] at hpow
  have hmono : (∑ i, g i) ^ N ≤ (∑ i, g i) ^ (N + 1) :=
    pow_le_pow_right₀ hS1 (Nat.le_succ N)
  have hterm : ∀ i, g i ^ (N + 1) * ‖f w‖ ≤ (match i with
      | none => B (0, 0, 0, 0)
      | some (Sum.inl j) => B (Pi.single j (N + 1), 0, 0, 0)
      | some (Sum.inr k) => B (0, 0, 0, Pi.single k (N + 1))) := by
    rintro (_ | j | k)
    · show (1 : ℝ) ^ (N + 1) * ‖f w‖ ≤ B (0, 0, 0, 0)
      simpa using elementarySchwartz_monomial_bound hf 0 0 w
    · have := elementarySchwartz_monomial_bound hf (Pi.single j (N + 1)) 0 w
      rw [Finset.prod_eq_single j (fun k _ hk => by simp [hk]) (by simp)] at this
      simp only [Pi.single_eq_same, Pi.zero_apply, pow_zero, Finset.prod_const_one,
        mul_one] at this
      exact this
    · have := elementarySchwartz_monomial_bound hf 0 (Pi.single k (N + 1)) w
      rw [Finset.prod_eq_single k (fun k' _ hk => by simp [hk]) (by simp)] at this
      simp only [Pi.single_eq_same, Pi.zero_apply, pow_zero, Finset.prod_const_one,
        one_mul] at this
      exact this
  have hfw : 0 ≤ ‖f w‖ := norm_nonneg _
  rw [← hsum]
  calc ‖f w‖ * (∑ i, g i) ^ N ≤ ‖f w‖ * (c ^ N * ∑ i, g i ^ (N + 1)) :=
        mul_le_mul_of_nonneg_left (hmono.trans hpow') hfw
    _ = c ^ N * ∑ i, g i ^ (N + 1) * ‖f w‖ := by rw [← Finset.sum_mul]; ring
    _ ≤ c ^ N * ∑ i : Option (Fin m ⊕ Fin r), (match i with
      | none => B (0, 0, 0, 0)
      | some (Sum.inl j) => B (Pi.single j (N + 1), 0, 0, 0)
      | some (Sum.inr k) => B (0, 0, 0, Pi.single k (N + 1))) := by
        gcongr with i; exact hterm i
    _ = _ := by simp [Fintype.sum_option, Fintype.sum_sum_type, add_assoc]


/-- A compact set of finite adeles has bounded denominators: one nonzero integer multiplies it
into the integral adeles. -/
private theorem exists_mul_mem_adicCompletionIntegers_of_isCompact
    {Ω : Set (FiniteAdeleRing (𝓞 F) F)} (hΩ : IsCompact Ω) :
    ∃ b : 𝓞 F, b ≠ 0 ∧ ∀ x ∈ Ω, ∀ v : HeightOneSpectrum (𝓞 F),
      (algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) b * x) v ∈ v.adicCompletionIntegers F := by
  classical
  let V : {b : 𝓞 F // b ≠ 0} → Set (FiniteAdeleRing (𝓞 F) F) := fun b =>
    {x | ∀ v, (algebraMap (𝓞 F) _ b.1 * x) v ∈ v.adicCompletionIntegers F}
  have hO : IsOpen {y : FiniteAdeleRing (𝓞 F) F | ∀ v, y v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_mem (fun v : HeightOneSpectrum (𝓞 F) =>
      Valued.isOpen_integer (v.adicCompletion F))
  have hVo : ∀ b, IsOpen (V b) := fun b => hO.preimage (continuous_const.mul continuous_id)
  have hint (v : HeightOneSpectrum (𝓞 F)) (b : 𝓞 F) :
      algebraMap (𝓞 F) (v.adicCompletion F) b ∈ v.adicCompletionIntegers F :=
    HeightOneSpectrum.coe_mem_adicCompletionIntegers v b
  have hcov : Ω ⊆ ⋃ b, V b := by
    intro x _
    have hS : {v | x v ∉ v.adicCompletionIntegers F}.Finite := by
      exact Filter.eventually_cofinite.mp x.2
    choose c hc hcx using fun v : HeightOneSpectrum (𝓞 F) =>
      HeightOneSpectrum.adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v (x v)
    have hb : (∏ v ∈ hS.toFinset, c v) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun v _ => nonZeroDivisors.ne_zero (hc v)
    refine Set.mem_iUnion.mpr ⟨⟨∏ v ∈ hS.toFinset, c v, hb⟩, fun v => ?_⟩
    change algebraMap (𝓞 F) (v.adicCompletion F) (∏ v ∈ hS.toFinset, c v) * x v ∈
      v.adicCompletionIntegers F
    by_cases hv : v ∈ hS.toFinset
    · rw [← Finset.mul_prod_erase _ _ hv, map_mul, mul_comm, ← mul_assoc]
      exact mul_mem (hcx v) (hint v _)
    · have : x v ∈ v.adicCompletionIntegers F := by simpa using hv
      exact mul_mem (hint v _) this
  have hdir : Directed (· ⊆ ·) V := by
    intro b c
    refine ⟨⟨b.1 * c.1, mul_ne_zero b.2 c.2⟩, fun x hx v => ?_, fun x hx v => ?_⟩
    · change algebraMap (𝓞 F) (v.adicCompletion F) (b.1 * c.1) * x v ∈ v.adicCompletionIntegers F
      have := hx v
      change algebraMap (𝓞 F) (v.adicCompletion F) b.1 * x v ∈ v.adicCompletionIntegers F at this
      rw [map_mul, mul_comm (algebraMap _ _ b.1), mul_assoc]
      exact mul_mem (hint v _) this
    · change algebraMap (𝓞 F) (v.adicCompletion F) (b.1 * c.1) * x v ∈ v.adicCompletionIntegers F
      have := hx v
      change algebraMap (𝓞 F) (v.adicCompletion F) c.1 * x v ∈ v.adicCompletionIntegers F at this
      rw [map_mul, mul_assoc]
      exact mul_mem (hint v _) this
  have : Nonempty {b : 𝓞 F // b ≠ 0} := ⟨⟨1, one_ne_zero⟩⟩
  obtain ⟨b, hb⟩ := hΩ.elim_directed_cover V hVo hcov hdir
  exact ⟨b.1, b.2, fun x hx => hb hx⟩


/-- A field element that is integral at every finite place is an algebraic integer. -/
private theorem mem_integers_of_forall_mem_adicCompletionIntegers {ξ : F}
    (h : ∀ v : HeightOneSpectrum (𝓞 F),
      algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ v ∈ v.adicCompletionIntegers F) :
    ξ ∈ (algebraMap (𝓞 F) F).range := by
  refine HeightOneSpectrum.mem_integers_of_valuation_le_one F ξ fun v => ?_
  have := h v
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at this
  rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact this


omit [NumberField F] in
/-- The identification of the infinite adeles with the mixed space is continuous. -/
private theorem continuous_ringEquiv_mixedSpace :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  have h : ⇑(InfiniteAdeleRing.ringEquiv_mixedSpace F) = fun x =>
      ((fun (v : {w : InfinitePlace F // InfinitePlace.IsReal w}) =>
        InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
       (fun (v : {w : InfinitePlace F // InfinitePlace.IsComplex w}) =>
        InfinitePlace.Completion.extensionEmbedding v.1 (x v))) := by
    funext x; exact InfiniteAdeleRing.ringEquiv_mixedSpace_apply F x
  rw [h]
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp
      (continuous_apply (v.1))
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp
      (continuous_apply (v.1))

/-- A subgroup of the adeles with open annihilator has trivial archimedean coordinates, since the
characters `y ↦ exp(i t φ(y_∞))` tend to the trivial character as `t → 0`. -/
private theorem mixedSpace_eq_zero_of_isOpen_lcaAnnihilator
    {k : Subgroup (Multiplicative 𝔸[F])}
    (hk : IsOpen (lcaAnnihilator k : Set (PontryaginDual (Multiplicative 𝔸[F]))))
    {y : Multiplicative 𝔸[F]} (hy : y ∈ k) :
    InfiniteAdeleRing.ringEquiv_mixedSpace F (Multiplicative.toAdd y).1 = 0 := by
  set m : 𝔸[F] → mixedEmbedding.mixedSpace F :=
    fun z => InfiniteAdeleRing.ringEquiv_mixedSpace F z.1 with hm_def
  have hm : Continuous m := continuous_ringEquiv_mixedSpace.comp continuous_fst
  have hmadd : ∀ a b, m (a + b) = m a + m b := fun a b =>
    map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1
  have hm0 : m 0 = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  change m (Multiplicative.toAdd y) = 0
  by_contra hne
  obtain ⟨φ, hφ⟩ := SeparatingDual.exists_ne_zero (R := ℝ) hne
  set c := φ (m (Multiplicative.toAdd y)) with hc
  let χ : ℝ → PontryaginDual (Multiplicative 𝔸[F]) := fun t =>
    { toFun := fun z => Circle.exp (t * φ (m (Multiplicative.toAdd z)))
      map_one' := by simp [hm0]
      map_mul' := fun a b => by
        simp only [toAdd_mul, hmadd, map_add, mul_add, Circle.exp_add]
      continuous_toFun := by
        exact Circle.exp.continuous.comp (continuous_const.mul
          (φ.continuous.comp (hm.comp continuous_toAdd))) }
  have hχ : Continuous χ := by
    apply ContinuousMonoidHom.continuous_of_continuous_uncurry
    exact Circle.exp.continuous.comp (continuous_fst.mul
          (φ.continuous.comp (hm.comp (continuous_toAdd.comp continuous_snd))))
  have h0 : χ 0 ∈ lcaAnnihilator k := by
    have : χ 0 = 1 := by
      refine ContinuousMonoidHom.ext fun z => ?_
      change Circle.exp (0 * _) = 1
      rw [zero_mul, Circle.exp_zero]
    rw [this]; exact Subgroup.one_mem _
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp (hk.preimage hχ) 0 h0
  have hcpos : 0 < |c| := abs_pos.mpr hφ
  set t := min (δ / 2) (Real.pi / |c|) with ht
  have htpos : 0 < t := lt_min (by linarith) (div_pos Real.pi_pos hcpos)
  have htδ : t < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have htc : |t * c| ≤ Real.pi := by
    rw [abs_mul, abs_of_pos htpos]
    calc t * |c| ≤ (Real.pi / |c|) * |c| := by gcongr; exact min_le_right _ _
      _ = Real.pi := div_mul_cancel₀ _ hcpos.ne'
  have hmem : χ t ∈ lcaAnnihilator k := hball (by simpa [abs_of_pos htpos] using htδ)
  have h1 := DFunLike.congr_fun (MonoidHom.mem_ker.mp hmem) ⟨y, hy⟩
  change Circle.exp (t * c) = 1 at h1
  obtain ⟨n, hn⟩ := Circle.exp_eq_one.mp h1
  have htc0 : t * c ≠ 0 := mul_ne_zero htpos.ne' hφ
  have hn0 : n ≠ 0 := by rintro rfl; exact htc0 (by simpa using hn)
  have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hn0
  have : |t * c| = |(n : ℝ)| * (2 * Real.pi) := by
    rw [hn, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
  nlinarith [Real.pi_pos]


/-- The Euclidean norm is at most the sum of the absolute values of the coordinates. -/
private theorem euclideanSpace_norm_le_sum_abs {m : ℕ} (x : EuclideanSpace ℝ (Fin m)) :
    ‖x‖ ≤ ∑ j, |x j| := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_le_iff]
  refine ⟨Finset.sum_nonneg fun _ _ => abs_nonneg _, ?_⟩
  simp only [Real.norm_eq_abs]
  exact Finset.sum_sq_le_sq_sum_of_nonneg fun _ _ => abs_nonneg _

/-- A continuous additive map from an elementary group to a real normed space grows at most
linearly in the real and lattice coordinates. -/
private theorem elementary_additive_norm_le {m n r : ℕ} {Fk : Type*} [AddCommGroup Fk]
    [TopologicalSpace Fk] [CompactSpace Fk]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (P₀ : ElementaryLieGroup m n r Fk → V) (hP₀ : Continuous P₀)
    (hadd : ∀ w₁ w₂, P₀ (w₁ + w₂) = P₀ w₁ + P₀ w₂) :
    ∃ A B : ℝ, 0 ≤ A ∧ ∀ w : ElementaryLieGroup m n r Fk,
      ‖P₀ w‖ ≤ A * (∑ j, |w.1 j| + ∑ k, |(w.2.2.1 k : ℝ)|) + B := by
  classical
  let P : ElementaryLieGroup m n r Fk →+ V := AddMonoidHom.mk' P₀ hadd
  have hP : Continuous P := hP₀
  show ∃ A B : ℝ, 0 ≤ A ∧ ∀ w : ElementaryLieGroup m n r Fk,
      ‖P w‖ ≤ A * (∑ j, |w.1 j| + ∑ k, |(w.2.2.1 k : ℝ)|) + B
  -- the real coordinate
  let Pr : EuclideanSpace ℝ (Fin m) →+ V := P.comp (AddMonoidHom.inl _ _)
  have hPr : Continuous Pr := hP.comp (continuous_id.prodMk continuous_const)
  let L := Pr.toRealLinearMap hPr
  -- the compact coordinates
  let q : (Fin n → AddCircle (1 : ℝ)) × Fk → V := fun θb => P (0, θb.1, 0, θb.2)
  have hq : Continuous q := hP.comp (continuous_const.prodMk
    (continuous_fst.prodMk (continuous_const.prodMk continuous_snd)))
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hq.continuousOn
  -- the lattice coordinate
  let Pz : (Fin r → ℤ) →+ V :=
    P.comp ((AddMonoidHom.inr _ _).comp ((AddMonoidHom.inr _ _).comp (AddMonoidHom.inl _ _)))
  let A₂ : ℝ := ∑ k, ‖Pz (Pi.single k 1)‖
  have hA₂ : 0 ≤ A₂ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨‖L‖ + A₂, C, add_nonneg (norm_nonneg _) hA₂, fun w => ?_⟩
  have hw : w = (w.1, 0, 0, 0) + ((0, w.2.1, 0, w.2.2.2) + (0, 0, w.2.2.1, 0)) := by
    ext <;> simp
  have h1 : ‖P (w.1, 0, 0, 0)‖ ≤ ‖L‖ * ∑ j, |w.1 j| := by
    have : P (w.1, 0, 0, 0) = L w.1 := rfl
    rw [this]
    exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left
      (euclideanSpace_norm_le_sum_abs _) (norm_nonneg _))
  have h2 : ‖P (0, w.2.1, 0, w.2.2.2)‖ ≤ C := hC (w.2.1, w.2.2.2) (Set.mem_univ _)
  have h3 : ‖P (0, 0, w.2.2.1, 0)‖ ≤ A₂ * ∑ k, |(w.2.2.1 k : ℝ)| := by
    have : P (0, 0, w.2.2.1, 0) = Pz w.2.2.1 := rfl
    rw [this]
    have hdecomp : w.2.2.1 = ∑ k, (w.2.2.1 k) • (Pi.single k 1 : Fin r → ℤ) := by
      ext i; simp [Pi.single_apply]
    have hPz : Pz w.2.2.1 = ∑ k, (w.2.2.1 k) • Pz (Pi.single k 1) := by
      conv_lhs => rw [hdecomp]
      rw [map_sum]
      simp only [map_zsmul]
    rw [hPz]
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [norm_zsmul ℝ, Real.norm_eq_abs, mul_comm]
    have : ‖Pz (Pi.single k 1)‖ ≤ A₂ :=
      Finset.single_le_sum (f := fun k => ‖Pz (Pi.single k 1)‖) (fun _ _ => norm_nonneg _)
        (Finset.mem_univ k)
    exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
  have hsplit : P w = P (w.1, 0, 0, 0) + (P (0, w.2.1, 0, w.2.2.2) + P (0, 0, w.2.2.1, 0)) := by
    conv_lhs => rw [hw]
    rw [map_add, map_add]
  rw [hsplit]
  have hX : 0 ≤ ∑ j, |w.1 j| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hY : 0 ≤ ∑ k, |(w.2.2.1 k : ℝ)| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  calc ‖P (w.1, 0, 0, 0) + (P (0, w.2.1, 0, w.2.2.2) + P (0, 0, w.2.2.1, 0))‖
      ≤ ‖P (w.1, 0, 0, 0)‖ + (‖P (0, w.2.1, 0, w.2.2.2)‖ + ‖P (0, 0, w.2.2.1, 0)‖) :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
    _ ≤ ‖L‖ * ∑ j, |w.1 j| + (C + A₂ * ∑ k, |(w.2.2.1 k : ℝ)|) := by gcongr
    _ ≤ _ := by nlinarith [norm_nonneg L]

/-- The norm of a continuous additive projection factoring through an elementary
quotient grows at most linearly in the real and lattice coordinates. -/
private theorem presentation_additive_norm_bound {G V : Type*} [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient)
    (m : G →* Multiplicative V) (hm : Continuous m)
    (hker : ∀ u ∈ OrderDual.ofDual a.val.2, m u = 1) :
    ∃ A B : ℝ, 0 ≤ A ∧ ∀ (y : G) (hy : y ∈ a.val.1),
      ‖Multiplicative.toAdd (m y)‖ ≤
        A * (∑ j, |(Multiplicative.toAdd (e.equiv (QuotientGroup.mk ⟨y, hy⟩))).1 j| +
          ∑ k, |((Multiplicative.toAdd (e.equiv (QuotientGroup.mk ⟨y, hy⟩))).2.2.1 k : ℝ)|) +
          B := by
  let h0 := m.comp a.val.1.subtype
  let lift : a.quotient →* Multiplicative V :=
    QuotientGroup.lift _ h0 (fun u hu ↦ hker u (Subgroup.mem_comap.mp hu))
  have hh0 : Continuous h0 := hm.comp continuous_subtype_val
  have hlift : Continuous lift := (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr hh0
  have key : ∀ w₁ w₂ : ElementaryLieGroup e.realDim e.torusDim e.latticeRank
      e.finiteFactor, e.equiv.symm (Multiplicative.ofAdd (w₁ + w₂)) =
        e.equiv.symm (Multiplicative.ofAdd w₁) * e.equiv.symm (Multiplicative.ofAdd w₂) :=
    fun w₁ w₂ => e.equiv.symm.map_mul (Multiplicative.ofAdd w₁) (Multiplicative.ofAdd w₂)
  let P : ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor →
      V :=
    fun w => Multiplicative.toAdd (lift (e.equiv.symm (Multiplicative.ofAdd w)))
  have hPadd : ∀ w₁ w₂, P (w₁ + w₂) = P w₁ + P w₂ := (fun w₁ w₂ => by
        have h1 := key w₁ w₂
        have h2 := congrArg (fun z => Multiplicative.toAdd (lift z)) h1
        have h3 := map_mul lift (e.equiv.symm (Multiplicative.ofAdd w₁))
          (e.equiv.symm (Multiplicative.ofAdd w₂))
        have h4 := congrArg Multiplicative.toAdd h3
        exact (h2.trans h4).trans (toAdd_mul _ _))

  have hP : Continuous P := continuous_toAdd.comp (hlift.comp (e.equiv.symm.continuous.comp
    continuous_ofAdd))
  have H := elementary_additive_norm_le (m := e.realDim) (n := e.torusDim)
    (r := e.latticeRank) (Fk := e.finiteFactor) (V := V) P hP hPadd
  obtain ⟨A, B, hA, hAB⟩ := H
  refine ⟨A, B, hA, ?_⟩
  intro y hy
  have h1 := congrArg (fun z => Multiplicative.toAdd (lift z))
      (e.equiv.symm_apply_apply (QuotientGroup.mk ⟨y, hy⟩))
  have h2 : lift (QuotientGroup.mk ⟨y, hy⟩) = h0 ⟨y, hy⟩ := QuotientGroup.lift_mk _ _ _
  have hPy : P (Multiplicative.toAdd (e.equiv (QuotientGroup.mk ⟨y, hy⟩))) =
      Multiplicative.toAdd (m y) :=
    h1.trans (congrArg Multiplicative.toAdd h2)
  exact (le_of_eq (congrArg norm hPy.symm)).trans
    (hAB (Multiplicative.toAdd (e.equiv (QuotientGroup.mk ⟨y, hy⟩))))

open scoped Classical in
/-- On the open subgroup of a structural pair of the adeles, the archimedean coordinate is
controlled linearly by the real and lattice coordinates of any elementary presentation. -/
private theorem presentation_mixedSpace_bound
    (a : BruhatStructuralPair (Multiplicative 𝔸[F]))
    (e : ElementaryLCAPresentation a.quotient) :
    ∃ A B : ℝ, 0 ≤ A ∧ ∀ (y : Multiplicative 𝔸[F]) (hy : y ∈ a.val.1),
      ‖InfiniteAdeleRing.ringEquiv_mixedSpace F (Multiplicative.toAdd y).1‖ ≤
        A * (∑ j, |(Multiplicative.toAdd (e.equiv (QuotientGroup.mk ⟨y, hy⟩))).1 j| +
          ∑ k, |((Multiplicative.toAdd (e.equiv (QuotientGroup.mk ⟨y, hy⟩))).2.2.1 k : ℝ)|) +
          B := by
  have hgood := a.property.2.2.1
  let m : 𝔸[F] → mixedEmbedding.mixedSpace F :=
    fun z => InfiniteAdeleRing.ringEquiv_mixedSpace F z.1
  have hm : Continuous m := continuous_ringEquiv_mixedSpace.comp continuous_fst
  let φ : Multiplicative 𝔸[F] →* Multiplicative (mixedEmbedding.mixedSpace F) :=
    { toFun := fun x ↦ Multiplicative.ofAdd (m x.toAdd)
      map_one' := by
        change Multiplicative.ofAdd (InfiniteAdeleRing.ringEquiv_mixedSpace F 0) = 1
        rw [map_zero]
        rfl
      map_mul' x y := by
        change Multiplicative.ofAdd (InfiniteAdeleRing.ringEquiv_mixedSpace F
          (x.toAdd.1 + y.toAdd.1)) = _
        rw [map_add]
        rfl }
  exact presentation_additive_norm_bound a e φ
    (continuous_ofAdd.comp (hm.comp continuous_toAdd))
    (fun x hx ↦ congrArg Multiplicative.ofAdd
      (mixedSpace_eq_zero_of_isOpen_lcaAnnihilator hgood.2.1 hx))

/-- A compactly generated subgroup of the adeles has bounded denominators at the finite places. -/
private theorem exists_mul_mem_adicCompletionIntegers_of_compactlyGenerated
    {U : Subgroup (Multiplicative 𝔸[F])} (hU : IsCompactlyGeneratedGroup U) :
    ∃ b : 𝓞 F, b ≠ 0 ∧ ∀ y ∈ U, ∀ v : HeightOneSpectrum (𝓞 F),
      (algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) b * (Multiplicative.toAdd y).2) v ∈
        v.adicCompletionIntegers F := by
  obtain ⟨V, -, hVc, hVgen⟩ := hU
  have hc : Continuous fun u : U => (Multiplicative.toAdd u.val).2 :=
    continuous_snd.comp (continuous_toAdd.comp continuous_subtype_val)
  obtain ⟨b, hb, hbV⟩ := exists_mul_mem_adicCompletionIntegers_of_isCompact (hVc.image hc)
  suffices H : ∀ u ∈ Subgroup.closure V, ∀ v : HeightOneSpectrum (𝓞 F),
      (algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) b * (Multiplicative.toAdd u.val).2) v ∈
        v.adicCompletionIntegers F from
    ⟨b, hb, fun y hy => H ⟨y, hy⟩ (hVgen ▸ Subgroup.mem_top _)⟩
  intro u hmem
  induction hmem using Subgroup.closure_induction with
  | mem u hu => exact hbV _ ⟨u, hu, rfl⟩
  | one =>
    intro v
    change algebraMap (𝓞 F) (v.adicCompletion F) b * 0 ∈ v.adicCompletionIntegers F
    rw [mul_zero]; exact zero_mem _
  | mul u w _ _ hu hw =>
    intro v
    change algebraMap (𝓞 F) (v.adicCompletion F) b *
      ((Multiplicative.toAdd u.val).2 v + (Multiplicative.toAdd w.val).2 v) ∈
        v.adicCompletionIntegers F
    rw [mul_add]
    exact add_mem (hu v) (hw v)
  | inv u _ hu =>
    intro v
    change algebraMap (𝓞 F) (v.adicCompletion F) b * (-(Multiplicative.toAdd u.val).2 v) ∈
        v.adicCompletionIntegers F
    rw [mul_neg]
    exact neg_mem (hu v)

open scoped Classical in
/-- Inverse powers of the archimedean size are summable over the field elements whose multiples
by a fixed nonzero integer are integral, once the power exceeds the rank of the integer lattice. -/
private theorem summable_indicator_inv_one_add_norm_pow (b : 𝓞 F) (hb : b ≠ 0) (N : ℕ)
    (hN : Module.finrank ℤ (mixedEmbedding.integerLattice F) < N) :
    Summable ({ξ : Fˣ | algebraMap (𝓞 F) F b * (ξ : F) ∈ (algebraMap (𝓞 F) F).range}.indicator
      (fun ξ : Fˣ => ((1 + ‖mixedEmbedding F (ξ : F)‖) ^ N)⁻¹)) := by
  set S := {ξ : Fˣ | algebraMap (𝓞 F) F b * (ξ : F) ∈ (algebraMap (𝓞 F) F).range}
  rw [← summable_subtype_iff_indicator]
  let L := mixedEmbedding.integerLattice F
  have hmemL : ∀ ξ : S, mixedEmbedding F (algebraMap (𝓞 F) F b * (ξ.val : F)) ∈ L := by
    rintro ⟨ξ, c, hc⟩
    exact ⟨c, by simp [hc]⟩
  let ι : S → L := fun ξ => ⟨_, hmemL ξ⟩
  have hι : Function.Injective ι := by
    intro ξ₁ ξ₂ h
    have h1 := congrArg Subtype.val h
    have h2 := (mixedEmbedding_injective F) h1
    have hb' : algebraMap (𝓞 F) F b ≠ 0 := by
      simpa using hb
    exact Subtype.ext (Units.ext (mul_left_cancel₀ hb' h2))
  have hsum := (ZLattice.summable_norm_pow_inv L N hN).comp_injective hι
  have hbn : 0 < ‖mixedEmbedding F (algebraMap (𝓞 F) F b)‖ := by
    rw [norm_pos_iff, map_ne_zero_iff _ (mixedEmbedding_injective F)]
    simpa using hb
  refine (hsum.mul_left (‖mixedEmbedding F (algebraMap (𝓞 F) F b)‖ ^ N)).of_nonneg_of_le
    (fun _ => by simp only [Function.comp_apply]; positivity) (fun ξ => ?_)
  simp only [Function.comp_apply]
  have hξ0 : (ξ.val : F) ≠ 0 := ξ.val.ne_zero
  have hιpos : 0 < ‖ι ξ‖ := by
    change 0 < ‖mixedEmbedding F (algebraMap (𝓞 F) F b * (ξ.val : F))‖
    rw [norm_pos_iff, map_ne_zero_iff _ (mixedEmbedding_injective F)]
    exact mul_ne_zero (by simpa using hb) hξ0
  have hιle : ‖ι ξ‖ ≤ ‖mixedEmbedding F (algebraMap (𝓞 F) F b)‖ *
      (1 + ‖mixedEmbedding F (ξ.val : F)‖) := by
    change ‖mixedEmbedding F (algebraMap (𝓞 F) F b * (ξ.val : F))‖ ≤ _
    rw [map_mul]
    refine (norm_mul_le _ _).trans ?_
    gcongr
    linarith
  rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm, ← div_eq_mul_inv,
    div_le_iff₀ (by positivity), ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) hιle N


/-- A norm estimate for `a * b - c` in a normed ring. -/
private theorem norm_le_mul_add_of_eq {R : Type*} [NormedRing R] (a b c d : R) (h : d = a * b - c) :
    ‖d‖ ≤ ‖a‖ * ‖b‖ + ‖c‖ := by
  rw [h]
  exact (norm_sub_le _ _).trans (add_le_add (norm_mul_le _ _) le_rfl)

open scoped Classical in
/-- The archimedean size of `ξ` is controlled by that of `g * (ξ + x)` and the sizes of
`g⁻¹` and `x`. -/
private theorem norm_mixedEmbedding_le_of_adele (g : IdeleGroup (𝓞 F) F) (x : 𝔸[F]) (ξ : F) :
    ‖mixedEmbedding F ξ‖ ≤
      ‖InfiniteAdeleRing.ringEquiv_mixedSpace F ((g⁻¹ : IdeleGroup (𝓞 F) F) : 𝔸[F]).1‖ *
        ‖InfiniteAdeleRing.ringEquiv_mixedSpace F (g.val * (algebraMap F 𝔸[F] ξ + x)).1‖ +
      ‖InfiniteAdeleRing.ringEquiv_mixedSpace F x.1‖ := by
  set E := InfiniteAdeleRing.ringEquiv_mixedSpace F
  have hgi : ((g⁻¹ : IdeleGroup (𝓞 F) F) : 𝔸[F]).1 * (g : 𝔸[F]).1 = 1 := by
    have := congrArg Prod.fst (Units.inv_mul g)
    exact this
  have hξ : mixedEmbedding F ξ = E ((algebraMap F 𝔸[F] ξ).1) :=
    InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp F
  have h3 : ((g⁻¹ : IdeleGroup (𝓞 F) F) : 𝔸[F]).1 * (g.val * (algebraMap F 𝔸[F] ξ + x)).1 =
      (algebraMap F 𝔸[F] ξ).1 + x.1 := by
    change ((g⁻¹ : IdeleGroup (𝓞 F) F) : 𝔸[F]).1 * ((g : 𝔸[F]).1 *
      ((algebraMap F 𝔸[F] ξ).1 + x.1)) = _
    rw [← mul_assoc, hgi, one_mul]
  have hkey : mixedEmbedding F ξ =
      E ((g⁻¹ : IdeleGroup (𝓞 F) F) : 𝔸[F]).1 * E (g.val * (algebraMap F 𝔸[F] ξ + x)).1 -
        E x.1 := by
    rw [← map_mul E, h3, map_add E, hξ, add_sub_cancel_right]
  exact norm_le_mul_add_of_eq _ _ _ _ hkey

/-- Bounded denominators of `g * (ξ + x)`, `g⁻¹` and `x` give bounded denominators of `ξ`. -/
private theorem mul_mem_integers_of_adele {b₀ b₁ b₂ : 𝓞 F} (g : IdeleGroup (𝓞 F) F) (x : 𝔸[F]) (ξ : F)
    (h0 : ∀ v : HeightOneSpectrum (𝓞 F), (algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) b₀ *
      (g.val * (algebraMap F 𝔸[F] ξ + x)).2) v ∈ v.adicCompletionIntegers F)
    (h1 : ∀ v : HeightOneSpectrum (𝓞 F), (algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) b₁ *
      ((g⁻¹ : IdeleGroup (𝓞 F) F) : 𝔸[F]).2) v ∈ v.adicCompletionIntegers F)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 F), (algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) b₂ *
      x.2) v ∈ v.adicCompletionIntegers F) :
    algebraMap (𝓞 F) F (b₀ * b₁ * b₂) * ξ ∈ (algebraMap (𝓞 F) F).range := by
  refine HeightOneSpectrum.mem_integers_of_valuation_le_one F _ fun v => ?_
  rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation', ← HeightOneSpectrum.mem_adicCompletionIntegers]
  have hgi : ((g⁻¹ : IdeleGroup (𝓞 F) F) : 𝔸[F]).2 v * (g : 𝔸[F]).2 v = 1 := by
    have := congrArg (fun z : 𝔸[F] => z.2 v) (Units.inv_mul g)
    exact this
  have e0 := h0 v
  have e1 := h1 v
  have e2 := h2 v
  change ((algebraMap (𝓞 F) F b₀ : F) : v.adicCompletion F) *
    ((g : 𝔸[F]).2 v * ((ξ : v.adicCompletion F) + x.2 v)) ∈ v.adicCompletionIntegers F at e0
  change ((algebraMap (𝓞 F) F b₁ : F) : v.adicCompletion F) *
    ((g⁻¹ : IdeleGroup (𝓞 F) F) : 𝔸[F]).2 v ∈ v.adicCompletionIntegers F at e1
  change ((algebraMap (𝓞 F) F b₂ : F) : v.adicCompletion F) * x.2 v ∈
    v.adicCompletionIntegers F at e2
  have hint (c : 𝓞 F) : ((algebraMap (𝓞 F) F c : F) : v.adicCompletion F) ∈
      v.adicCompletionIntegers F :=
    HeightOneSpectrum.coe_mem_adicCompletionIntegers v c
  have hcoe : ((algebraMap (𝓞 F) F (b₀ * b₁ * b₂) * ξ : F) : v.adicCompletion F) =
      ((algebraMap (𝓞 F) F b₂ : F) : v.adicCompletion F) *
        ((((algebraMap (𝓞 F) F b₁ : F) : v.adicCompletion F) *
          ((g⁻¹ : IdeleGroup (𝓞 F) F) : 𝔸[F]).2 v) *
          (((algebraMap (𝓞 F) F b₀ : F) : v.adicCompletion F) *
            ((g : 𝔸[F]).2 v * ((ξ : v.adicCompletion F) + x.2 v)))) -
      ((algebraMap (𝓞 F) F (b₀ * b₁) : F) : v.adicCompletion F) *
        (((algebraMap (𝓞 F) F b₂ : F) : v.adicCompletion F) * x.2 v) := by
    simp only [map_mul, HeightOneSpectrum.adicCompletion.coe_mul]
    linear_combination (-(((algebraMap (𝓞 F) F b₀ : F) : v.adicCompletion F) *
      ((algebraMap (𝓞 F) F b₁ : F) : v.adicCompletion F) *
      ((algebraMap (𝓞 F) F b₂ : F) : v.adicCompletion F) *
      ((ξ : v.adicCompletion F) + x.2 v))) * hgi
  rw [hcoe]
  exact sub_mem (mul_mem (hint _) (mul_mem e1 e0)) (mul_mem (hint _) e2)

/-- Real inequality transferring decay from the elementary coordinates to the archimedean one. -/
private theorem real_decay_aux {S M X A B C : ℝ} {N : ℕ} (hS : 0 ≤ S) (hX : 0 ≤ X) (hA : 0 ≤ A)
    (hM0 : 0 ≤ M) (hM : M ≤ A * X + B) (hC : S * (1 + X) ^ N ≤ C) :
    S * (1 + M) ^ N ≤ (1 + A + max B 0) ^ N * max C 0 := by
  have hB : B ≤ max B 0 := le_max_left _ _
  have hB0 : 0 ≤ max B 0 := le_max_right _ _
  have h2 : 1 + M ≤ (1 + A + max B 0) * (1 + X) := by nlinarith
  calc S * (1 + M) ^ N ≤ S * ((1 + A + max B 0) * (1 + X)) ^ N := by gcongr
    _ = (1 + A + max B 0) ^ N * (S * (1 + X) ^ N) := by rw [mul_pow]; ring
    _ ≤ (1 + A + max B 0) ^ N * max C 0 := by gcongr; exact hC.trans (le_max_left _ _)

/-- Real inequality transferring decay from `g * (ξ + x)` to `ξ`. -/
private theorem real_decay_aux₂ {φ t μ A₁ A₂ C₀ : ℝ} {N : ℕ} (hφ : 0 ≤ φ) (ht : 0 ≤ t) (hμ : 0 ≤ μ)
    (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂) (hpt : φ * (1 + t) ^ N ≤ C₀) (hmξ : μ ≤ A₁ * t + A₂) :
    φ ≤ (1 + A₁ + A₂) ^ N * C₀ * ((1 + μ) ^ N)⁻¹ := by
  have h1 : 1 + μ ≤ (1 + A₁ + A₂) * (1 + t) := by nlinarith
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  calc φ * (1 + μ) ^ N ≤ φ * ((1 + A₁ + A₂) * (1 + t)) ^ N := by gcongr
    _ = (1 + A₁ + A₂) ^ N * (φ * (1 + t) ^ N) := by rw [mul_pow]; ring
    _ ≤ (1 + A₁ + A₂) ^ N * C₀ := by gcongr

open scoped Classical in
/-- A stage realization on the adeles decays faster than any power of the archimedean size. -/
private theorem realization_decay (a : BruhatStructuralPair (Multiplicative 𝔸[F]))
    (e : ElementaryLCAPresentation a.quotient) (s : SchwartzBruhatStage e) (N : ℕ) :
    ∃ C₀ : ℝ, ∀ y : Multiplicative 𝔸[F], y ∈ a.val.1 →
      ‖schwartzBruhatStageRealization a e s y‖ *
        (1 + ‖InfiniteAdeleRing.ringEquiv_mixedSpace F (Multiplicative.toAdd y).1‖) ^ N ≤ C₀ := by
  have HAB := presentation_mixedSpace_bound a e
  obtain ⟨A, B, hA, hAB⟩ := HAB
  have HC := elementarySchwartz_decay (m := e.realDim) (n := e.torusDim)
    (r := e.latticeRank) (Fk := e.finiteFactor)
    (f := (show elementarySchwartzSubmodule _ _ _ _ from s).val)
    (show elementarySchwartzSubmodule _ _ _ _ from s).2 N
  obtain ⟨C, hC⟩ := HC
  refine ⟨(1 + A + max B 0) ^ N * max C 0, fun y hy => ?_⟩
  rw [schwartzBruhatStageRealization_apply_dite, dite_eq_left hy]
  have hC' := hC (Multiplicative.toAdd (e.equiv (QuotientGroup.mk ⟨y, hy⟩)))
  exact real_decay_aux (norm_nonneg _)
    (add_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)
      (Finset.sum_nonneg fun _ _ => abs_nonneg _)) hA (norm_nonneg _) (hAB y hy) hC'

/-- A Schwartz–Bruhat stage decays in the norm of any continuous additive projection
that vanishes on the kernel of the stage quotient. -/
theorem schwartzBruhatStage_exists_norm_decay {G V : Type*} [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient)
    (s : SchwartzBruhatStage e) (m : G →* Multiplicative V) (hm : Continuous m)
    (hker : ∀ u ∈ OrderDual.ofDual a.val.2, m u = 1) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : G,
      ‖schwartzBruhatStageRealization a e s y‖ * ‖(m y).toAdd‖ ^ N ≤ C := by
  obtain ⟨A, B, hA, hAB⟩ := presentation_additive_norm_bound a e m hm hker
  let fs : elementarySchwartzSubmodule _ _ _ _ := s
  obtain ⟨C, hC⟩ := elementarySchwartz_decay fs.property N
  refine ⟨(1 + A + max B 0) ^ N * max C 0, by positivity, fun y ↦ ?_⟩
  rw [schwartzBruhatStageRealization_apply]
  split_ifs with hy
  · exact (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (le_add_of_nonneg_left zero_le_one) N)
      (norm_nonneg _)).trans (real_decay_aux (norm_nonneg _)
        (add_nonneg (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)
          (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)) hA (norm_nonneg _) (hAB y hy) (hC _))
  · simp only [norm_zero, zero_mul]
    positivity

open scoped Classical in
/-- The summands of the adelic average of a stage realization admit a summable majorant on a
compact set of ideles and adeles. -/
private theorem realization_exists_summable_bound (a : BruhatStructuralPair (Multiplicative 𝔸[F]))
    (e : ElementaryLCAPresentation a.quotient) (s : SchwartzBruhatStage e)
    (K : Set (IdeleGroup (𝓞 F) F × 𝔸[F])) (hK : IsCompact K) :
    ∃ u : Fˣ → ℝ, Summable u ∧ ∀ ξ : Fˣ, ∀ p ∈ K,
      ‖schwartzBruhatStageRealization a e s
        (Multiplicative.ofAdd (p.1.val * (algebraMap F 𝔸[F] (ξ : F) + p.2)))‖ ≤ u ξ := by
  have hNlt : Module.finrank ℤ (mixedEmbedding.integerLattice F) <
      Module.finrank ℤ (mixedEmbedding.integerLattice F) + 1 := Nat.lt_succ_self _
  have HC := realization_decay a e s (Module.finrank ℤ (mixedEmbedding.integerLattice F) + 1)
  obtain ⟨C₀, hpt⟩ := HC
  -- finite-place constraints
  have HU := exists_mul_mem_adicCompletionIntegers_of_compactlyGenerated a.property.2.1
  obtain ⟨b₀, hb₀, hU⟩ := HU
  have hc1 : Continuous fun p : IdeleGroup (𝓞 F) F × 𝔸[F] =>
      ((p.1⁻¹ : IdeleGroup (𝓞 F) F) : 𝔸[F]) :=
    Units.continuous_coe_inv.comp continuous_fst
  have H1 := exists_mul_mem_adicCompletionIntegers_of_isCompact
    (hK.image (continuous_snd.comp hc1))
  obtain ⟨b₁, hb₁, hK1⟩ := H1
  have H2 := exists_mul_mem_adicCompletionIntegers_of_isCompact
    (hK.image (continuous_snd.comp continuous_snd))
  obtain ⟨b₂, hb₂, hK2⟩ := H2
  -- archimedean constraints
  have HA1 := hK.exists_bound_of_continuousOn
    ((continuous_ringEquiv_mixedSpace.comp (continuous_fst.comp hc1)).continuousOn)
  obtain ⟨A₁, hA₁⟩ := HA1
  have HA2 := hK.exists_bound_of_continuousOn
    ((continuous_ringEquiv_mixedSpace.comp (continuous_fst.comp continuous_snd)).continuousOn)
  obtain ⟨A₂, hA₂⟩ := HA2
  have hb : b₀ * b₁ * b₂ ≠ 0 := mul_ne_zero (mul_ne_zero hb₀ hb₁) hb₂
  have hsum := summable_indicator_inv_one_add_norm_pow (b₀ * b₁ * b₂) hb _ hNlt
  refine ⟨_, hsum.mul_left ((1 + max A₁ 0 + max A₂ 0) ^
    (Module.finrank ℤ (mixedEmbedding.integerLattice F) + 1) * max C₀ 0), ?_⟩
  intro ξ p hp
  by_cases hy : Multiplicative.ofAdd (p.1.val * (algebraMap F 𝔸[F] (ξ : F) + p.2)) ∈ a.val.1
  · have hξS := mul_mem_integers_of_adele p.1 p.2 (ξ : F) (hU _ hy)
      (hK1 _ ⟨p, hp, rfl⟩) (hK2 _ ⟨p, hp, rfl⟩)
    have hmξ := norm_mixedEmbedding_le_of_adele p.1 p.2 (ξ : F)
    have e1 : ‖InfiniteAdeleRing.ringEquiv_mixedSpace F
        ((p.1⁻¹ : IdeleGroup (𝓞 F) F) : 𝔸[F]).1‖ ≤ max A₁ 0 :=
      (hA₁ p hp).trans (le_max_left _ _)
    have e2 : ‖InfiniteAdeleRing.ringEquiv_mixedSpace F p.2.1‖ ≤ max A₂ 0 :=
      (hA₂ p hp).trans (le_max_left _ _)
    have hmξ' := hmξ.trans (add_le_add (mul_le_mul_of_nonneg_right e1 (norm_nonneg _)) e2)
    have hpt' := (hpt _ hy).trans (le_max_left C₀ 0)
    have hfin := real_decay_aux₂ (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      (le_max_right A₁ 0) (le_max_right A₂ 0) hpt' hmξ'
    have hξS' : ξ ∈ {ξ : Fˣ | algebraMap (𝓞 F) F (b₀ * b₁ * b₂) * (ξ : F) ∈
        (algebraMap (𝓞 F) F).range} := hξS
    exact hfin.trans_eq (by simp only [Set.indicator_of_mem hξS'])
  · have h0 : schwartzBruhatStageRealization a e s
        (Multiplicative.ofAdd (p.1.val * (algebraMap F 𝔸[F] (ξ : F) + p.2))) = 0 := by
      rw [schwartzBruhatStageRealization_apply_dite, dite_eq_right hy]
    have h1 : ‖schwartzBruhatStageRealization a e s
        (Multiplicative.ofAdd (p.1.val * (algebraMap F 𝔸[F] (ξ : F) + p.2)))‖ = 0 := by
      rw [h0, norm_zero]
    exact h1.le.trans (mul_nonneg (by positivity)
      (Set.indicator_nonneg (fun _ _ => by positivity) _))

end AdelicAverageSummable

/-- Paper: Lemma 2.2.2.1, p. 77. The series of absolute values of the summands
in the adelic average converges uniformly on every compact set. -/
theorem adelicAverage_summableUniformlyOn (f : ℬ[F])
    (K : Set (𝕀[F] × 𝔸[F])) (hK : IsCompact K) :
    SummableUniformlyOn (fun (ξ : Fˣ) (p : 𝕀[F] × 𝔸[F]) ↦
      ‖f (Multiplicative.ofAdd (p.1.val * (algebraMap F 𝔸[F] (ξ : F) + p.2)))‖) K := by
  have key : ∃ u : Fˣ → ℝ, Summable u ∧ ∀ ξ : Fˣ, ∀ p ∈ K,
      ‖(show schwartzBruhatSubmodule (Multiplicative 𝔸[F]) from f).val
        (Multiplicative.ofAdd (p.1.val * (algebraMap F 𝔸[F] (ξ : F) + p.2)))‖ ≤ u ξ := by
    have hf := (show schwartzBruhatSubmodule (Multiplicative 𝔸[F]) from f).2
    have hzero : ∃ u : Fˣ → ℝ, Summable u ∧ ∀ ξ : Fˣ, ∀ p ∈ K,
        ‖(0 : Multiplicative 𝔸[F] → ℂ)
          (Multiplicative.ofAdd (p.1.val * (algebraMap F 𝔸[F] (ξ : F) + p.2)))‖ ≤ u ξ :=
      ⟨0, summable_zero, fun _ _ _ => by simp⟩
    have hadd : ∀ φ ψ : Multiplicative 𝔸[F] → ℂ,
        (∃ u : Fˣ → ℝ, Summable u ∧ ∀ ξ : Fˣ, ∀ p ∈ K,
          ‖φ (Multiplicative.ofAdd (p.1.val * (algebraMap F 𝔸[F] (ξ : F) + p.2)))‖ ≤ u ξ) →
        (∃ u : Fˣ → ℝ, Summable u ∧ ∀ ξ : Fˣ, ∀ p ∈ K,
          ‖ψ (Multiplicative.ofAdd (p.1.val * (algebraMap F 𝔸[F] (ξ : F) + p.2)))‖ ≤ u ξ) →
        (∃ u : Fˣ → ℝ, Summable u ∧ ∀ ξ : Fˣ, ∀ p ∈ K,
          ‖(φ + ψ) (Multiplicative.ofAdd (p.1.val * (algebraMap F 𝔸[F] (ξ : F) + p.2)))‖ ≤
            u ξ) := by
      rintro φ ψ ⟨u₁, hu₁, h₁⟩ ⟨u₂, hu₂, h₂⟩
      exact ⟨u₁ + u₂, hu₁.add hu₂, fun ξ p hp =>
        (norm_add_le _ _).trans (add_le_add (h₁ ξ p hp) (h₂ ξ p hp))⟩
    refine Submodule.iSup_induction _ (motive := fun φ => ∃ u : Fˣ → ℝ, Summable u ∧
      ∀ ξ : Fˣ, ∀ p ∈ K,
        ‖φ (Multiplicative.ofAdd (p.1.val * (algebraMap F 𝔸[F] (ξ : F) + p.2)))‖ ≤ u ξ)
      hf ?_ hzero hadd
    intro a φ hφ
    refine Submodule.iSup_induction _ (motive := fun φ => ∃ u : Fˣ → ℝ, Summable u ∧
      ∀ ξ : Fˣ, ∀ p ∈ K,
        ‖φ (Multiplicative.ofAdd (p.1.val * (algebraMap F 𝔸[F] (ξ : F) + p.2)))‖ ≤ u ξ)
      hφ ?_ hzero hadd
    intro e φ hφ
    obtain ⟨s, rfl⟩ := LinearMap.mem_range.mp hφ
    exact realization_exists_summable_bound a e s K hK
  obtain ⟨u, hu, hle⟩ := key
  exact summableUniformlyOn_of_ge hu fun ξ p hp => by rw [norm_norm]; exact hle ξ p hp

/-- Paper: Lemma 2.2.2.1, pp. 77–78. At a fixed idele and adele, the
realization of a single elementary Schwartz stage has an absolutely summable
series over the nonzero diagonal field elements.
Deviation: This isolates pointwise convergence on one stage of the defining submodule. -/
theorem adelicAverage_stage_summable_norm
    (a : BruhatStructuralPair (Multiplicative 𝔸[F])) (e : ElementaryLCAPresentation a.quotient)
    (s : SchwartzBruhatStage e) (g : 𝕀[F]) (x : 𝔸[F]) :
    Summable (fun ξ : Fˣ ↦
      ‖schwartzBruhatStageRealization a e s
        (Multiplicative.ofAdd (g.val * (algebraMap F 𝔸[F] (ξ : F) + x)))‖) := by
  let f : ℬ[F] := schwartzBruhatStageInclusion a e s
  have hK : IsCompact ({(g, x)} : Set (𝕀[F] × 𝔸[F])) := isCompact_singleton
  have h := adelicAverage_summableUniformlyOn (F := F) f _ hK
  simpa only [f, schwartzBruhatStageInclusion_apply] using h.summable (Set.mem_singleton (g, x))

/-- Paper: Lemma 2.2.2.1(1), p. 77. Adding the term at `ξ = 0` to the adelic
average gives the sum over all field elements. -/
theorem hasSum_adelicAverage_add_zeroTerm (f : ℬ[F]) (g : 𝕀[F]) (x : 𝔸[F]) :
    HasSum (fun ξ : F ↦ f (Multiplicative.ofAdd (g.val * (algebraMap F 𝔸[F] ξ + x))))
      (adelicAverage f g x + f (Multiplicative.ofAdd (g.val * x))) := by
  classical
  let point (ξ : F) := Multiplicative.ofAdd (g.val * (algebraMap F 𝔸[F] ξ + x))
  let S : Submodule ℂ (Multiplicative 𝔸[F] → ℂ) :=
    { carrier := {φ | Summable (fun ξ : Fˣ ↦ φ (point (ξ : F)))}
      zero_mem' := summable_zero
      add_mem' := fun hφ hψ ↦ hφ.add hψ
      smul_mem' := fun c _ hφ ↦ hφ.const_smul c }
  have hS : schwartzBruhatSubmodule (Multiplicative 𝔸[F]) ≤ S := by
    unfold schwartzBruhatSubmodule
    refine iSup_le fun a ↦ iSup_le fun e ↦ ?_
    rintro _ ⟨s, rfl⟩
    exact (adelicAverage_stage_summable_norm a e s g x).of_norm
  have hs : Summable (fun ξ : Fˣ ↦ f (point (ξ : F))) :=
    hS (show (f : Multiplicative 𝔸[F] → ℂ) ∈ schwartzBruhatSubmodule _ from
      (show schwartzBruhatSubmodule _ from f).property)
  let e : Fˣ ≃ {ξ : F // ξ ∉ ({0} : Finset F)} :=
    unitsEquivNeZero.trans (Equiv.subtypeEquivRight (fun _ ↦ by simp))
  have hne : HasSum (fun ξ : {ξ : F // ξ ∉ ({0} : Finset F)} ↦ f (point ξ.val))
      (adelicAverage f g x) := e.hasSum_iff.mp hs.hasSum
  simpa only [Finset.sum_singleton, point, map_zero, zero_add] using
    (Finset.hasSum_compl_iff (f := fun ξ : F ↦ f (point ξ)) {0}).mp hne

/-- Smoothness on the covering space gives continuity on each discrete fiber. -/
private theorem continuous_elementarySchwartz {m n r : ℕ} {Fk : Type*}
    [TopologicalSpace Fk] [DiscreteTopology Fk] (f : ElementarySchwartz m n r Fk) :
    Continuous f := by
  let q : EuclideanSpace ℝ (Fin n) → (Fin n → AddCircle (1 : ℝ)) :=
    fun t i ↦ (t i : AddCircle (1 : ℝ))
  have hq : IsOpenQuotientMap q :=
    (IsOpenQuotientMap.piMap (fun _ ↦ QuotientAddGroup.isOpenQuotientMap_mk)).comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ ℝ)).toHomeomorph.isOpenQuotientMap
  rw [← (Homeomorph.prodAssoc (EuclideanSpace ℝ (Fin m)) (Fin n → AddCircle (1 : ℝ))
    ((Fin r → ℤ) × Fk)).isOpenQuotientMap.continuous_comp_iff]
  refine continuous_prod_of_discrete_right.mpr fun ab ↦ ?_
  have hcover := (IsOpenQuotientMap.id (X := EuclideanSpace ℝ (Fin m))).prodMap hq
  rw [← hcover.continuous_comp_iff]
  let fs : elementarySchwartzSubmodule m n r Fk := f
  exact (fs.property.1 ab.1 ab.2).continuous

/-- The Schwartz–Bruhat submodule is spanned by continuous stage functions. -/
private theorem continuous_schwartzBruhat_apply {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] (f : SchwartzBruhat G) : Continuous f := by
  classical
  let fs : schwartzBruhatSubmodule G := f
  change Continuous fs.val
  refine Submodule.iSup_induction (motive := fun g : G → ℂ ↦ Continuous g) _
    fs.property (fun a g hg ↦ ?_) continuous_const (fun _ _ hg hh ↦ hg.add hh)
  refine Submodule.iSup_induction (motive := fun g : G → ℂ ↦ Continuous g) _ hg
    (fun e g ⟨s, hs⟩ ↦ ?_) continuous_const (fun _ _ hg hh ↦ hg.add hh)
  subst g
  let U : OpenSubgroup G := ⟨a.val.1, a.property.1⟩
  have hu : IsClopen (U : Set G) := U.isClopen
  have hcomp : Continuous (fun x : a.val.1 ↦
      s (Multiplicative.toAdd (e.equiv (QuotientGroup.mk x)))) :=
    (continuous_elementarySchwartz s).comp
      (continuous_toAdd.comp (e.equiv.continuous.comp QuotientGroup.continuous_mk))
  refine continuous_iff_continuousAt.mpr fun x ↦ ?_
  by_cases hx : x ∈ U
  · apply (U.isOpen.isOpenEmbedding_subtypeVal.continuousAt_iff
      (x := (⟨x, hx⟩ : U))).mp
    convert hcomp.continuousAt (x := ⟨x, hx⟩) using 1
    funext y
    exact (schwartzBruhatStageRealization_apply a e s y.val).trans (dite_eq_left y.property)
  · refine (continuousAt_const (y := (0 : ℂ))).congr ?_
    filter_upwards [hu.1.isOpen_compl.mem_nhds hx] with y hy
    exact ((schwartzBruhatStageRealization_apply a e s y).trans (dite_eq_right hy)).symm

/-- A Schwartz–Bruhat function is continuous in its argument. -/
theorem schwartzBruhat_continuous {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] (f : SchwartzBruhat G) : Continuous f :=
  continuous_schwartzBruhat_apply f

open scoped IsDedekindDomain.FiniteAdeleRing RestrictedProduct in
/-- Uniform absolute convergence on compact sets gives continuity of the adelic average. -/
private theorem adelicAverage_continuous_of_summableUniformlyOn (f : ℬ[F])
    (hsummable : ∀ K : Set (𝕀[F] × 𝔸[F]), IsCompact K →
      SummableUniformlyOn (fun (ξ : Fˣ) (p : 𝕀[F] × 𝔸[F]) ↦
        ‖f (Multiplicative.ofAdd (p.1.val * (algebraMap F 𝔸[F] (ξ : F) + p.2)))‖) K) :
    Continuous (uncurry (adelicAverage f)) := by
  let (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
      CompactSpace (v.adicCompletionIntegers F) := compactSpace_adicCompletionIntegers v
  let : Fact (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    ⟨fun _ ↦ Valued.isOpen_valuationSubring _⟩
  let : LocallyCompactSpace (𝔸[F]) := by
    change LocallyCompactSpace (InfiniteAdeleRing F ×
      (Πʳ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
        [v.adicCompletion F, v.adicCompletionIntegers F]))
    let (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
        LocallyCompactSpace (v.adicCompletion F) := locallyCompactSpace_adicCompletion v
    infer_instance
  let : LocallyCompactSpace (𝕀[F]) := (ideleGroup_topology F).2.1
  let term (ξ : Fˣ) (p : 𝕀[F] × 𝔸[F]) :=
    f (Multiplicative.ofAdd (p.1.val * (algebraMap F 𝔸[F] (ξ : F) + p.2)))
  have hterm (ξ : Fˣ) : Continuous (term ξ) :=
    (continuous_schwartzBruhat_apply f).comp (continuous_ofAdd.comp
      ((Units.continuous_val.comp continuous_fst).mul (continuous_const.add continuous_snd)))
  change Continuous (fun p ↦ ∑' ξ, term ξ p)
  have hsum : HasSumLocallyUniformly term (fun p ↦ ∑' ξ, term ξ p) := by
    apply hasSumLocallyUniformly_of_forall_compact
    intro K hK
    have habs : SummableUniformlyOn (fun ξ p ↦ ‖term ξ p‖) K :=
      hsummable K hK
    apply hasSumUniformlyOn_iff_tendstoUniformlyOn.mpr
    refine Metric.tendstoUniformlyOn_iff.mpr fun ε hε ↦ ?_
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp
      habs.hasSumUniformlyOn.tendstoUniformlyOn ε hε] with s hs p hp
    -- The norm of the complex tail is bounded by the real tail.
    have h := habs.summable hp
    have htail := norm_tsum_le_tsum_norm (h.subtype fun ξ ↦ ξ ∉ s)
    rw [dist_eq_norm, ← h.of_norm.sum_add_tsum_subtype_compl s, add_sub_cancel_left]
    apply htail.trans_lt
    have hn := hs p hp
    rw [dist_eq_norm, ← h.sum_add_tsum_subtype_compl s, add_sub_cancel_left,
      Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg (fun _ ↦ norm_nonneg _))] at hn
    exact hn
  exact TendstoLocallyUniformly.continuous hsum
    (Eventually.of_forall fun s ↦ continuous_finsetSum s fun ξ _ ↦ hterm ξ).frequently

/-- Paper: Lemma 2.2.2.1(1), p. 77. The adelic average is jointly continuous in
the idele and adele arguments. -/
theorem adelicAverage_continuous (f : ℬ[F]) :
    Continuous (uncurry (adelicAverage f)) :=
  adelicAverage_continuous_of_summableUniformlyOn f (adelicAverage_summableUniformlyOn f)

/-- Paper: Lemma 2.2.2.1(1), p. 77. The sum with the zero term included is
invariant under addition of a diagonal field element to the adele argument. -/
theorem adelicAverage_add_zeroTerm_add_principal (f : ℬ[F]) (g : 𝕀[F]) (x : 𝔸[F]) (a : F) :
    let y := algebraMap F 𝔸[F] a + x
    adelicAverage f g y + f (Multiplicative.ofAdd (g.val * y)) =
      adelicAverage f g x + f (Multiplicative.ofAdd (g.val * x)) := by
  dsimp only
  rw [← (hasSum_adelicAverage_add_zeroTerm f g (algebraMap F 𝔸[F] a + x)).tsum_eq,
    ← (hasSum_adelicAverage_add_zeroTerm f g x).tsum_eq]
  simpa only [Equiv.coe_addRight, map_add, add_assoc] using
    (Equiv.addRight a).tsum_eq
      (fun ξ : F ↦ f (Multiplicative.ofAdd (g.val * (algebraMap F 𝔸[F] ξ + x))))

/-- Paper: Lemma 2.2.2.1(2), p. 77. The adelic average at `x = 0` is continuous
as a function of the idele. -/
theorem adelicAverage_at_zero_continuous (f : ℬ[F]) :
    Continuous (fun g : 𝕀[F] ↦ adelicAverage f g 0) :=
  (adelicAverage_continuous f).comp (continuous_id.prodMk continuous_const)

/-- Paper: Lemma 2.2.2.1(2), p. 77. The adelic average at `x = 0` is invariant
under multiplication by principal ideles.
Deviation: Invariance is expressed as constancy on the fibers of the quotient map. -/
theorem adelicAverage_at_zero_factorsThrough (f : ℬ[F]) :
    FactorsThrough (fun g : 𝕀[F] ↦ adelicAverage f g 0) classOf := by
  intro a b hab
  obtain ⟨u, hu⟩ := QuotientGroup.eq.mp hab
  have hb : b = a * IdeleGroup.unitEmbedding (𝓞 F) F u :=
    inv_mul_eq_iff_eq_mul.mp hu.symm
  subst b
  simp only [adelicAverage, add_zero]
  rw [← (Equiv.mulRight u).tsum_eq
    (fun ξ : Fˣ ↦ f (Multiplicative.ofAdd (a.val * algebraMap F 𝔸[F] (ξ : F))))]
  apply tsum_congr
  intro ξ
  change f (Multiplicative.ofAdd (a.val * algebraMap F 𝔸[F] (↑(ξ * u) : F))) =
    f (Multiplicative.ofAdd ((a.val * algebraMap F 𝔸[F] (u : F)) *
      algebraMap F 𝔸[F] (ξ : F)))
  rw [Units.val_mul, map_mul (algebraMap F 𝔸[F]), ← mul_assoc, mul_right_comm a.val]

-- ERRATA I65: With the Archimedean component fixed at one over ℚ, the
-- p-component p^m and test function 1_Ẑ give contributing rationals in
-- p^(-m) ℤ. The full domain below gives a uniform bound on the denominators.

section ArchimedeanFractional

open IsDedekindDomain
open scoped Classical nonZeroDivisors

/-- A subgroup of the infinite adeles with open annihilator is trivial at the mixed-space
coordinate: the characters `y ↦ exp(i t φ(y))` tend to the trivial character as `t → 0`. -/
private theorem infinite_mixedSpace_eq_zero_of_isOpen_lcaAnnihilator
    {k : Subgroup (Multiplicative (InfiniteAdeleRing F))}
    (hk : IsOpen (lcaAnnihilator k :
      Set (PontryaginDual (Multiplicative (InfiniteAdeleRing F)))))
    {y : Multiplicative (InfiniteAdeleRing F)} (hy : y ∈ k) :
    InfiniteAdeleRing.ringEquiv_mixedSpace F (Multiplicative.toAdd y) = 0 := by
  set m : InfiniteAdeleRing F → mixedEmbedding.mixedSpace F :=
    fun z => InfiniteAdeleRing.ringEquiv_mixedSpace F z with hm_def
  have hm : Continuous m := continuous_ringEquiv_mixedSpace
  have hmadd : ∀ a b, m (a + b) = m a + m b := fun a b =>
    map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) a b
  have hm0 : m 0 = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  change m (Multiplicative.toAdd y) = 0
  by_contra hne
  obtain ⟨φ, hφ⟩ := SeparatingDual.exists_ne_zero (R := ℝ) hne
  set c := φ (m (Multiplicative.toAdd y)) with hc
  let χ : ℝ → PontryaginDual (Multiplicative (InfiniteAdeleRing F)) := fun t =>
    { toFun := fun z => Circle.exp (t * φ (m (Multiplicative.toAdd z)))
      map_one' := by simp [hm0]
      map_mul' := fun a b => by
        simp only [toAdd_mul, hmadd, map_add, mul_add, Circle.exp_add]
      continuous_toFun := by
        exact Circle.exp.continuous.comp (continuous_const.mul
          (φ.continuous.comp (hm.comp continuous_toAdd))) }
  have hχ : Continuous χ := by
    apply ContinuousMonoidHom.continuous_of_continuous_uncurry
    exact Circle.exp.continuous.comp (continuous_fst.mul
          (φ.continuous.comp (hm.comp (continuous_toAdd.comp continuous_snd))))
  have h0 : χ 0 ∈ lcaAnnihilator k := by
    have : χ 0 = 1 := by
      refine ContinuousMonoidHom.ext fun z => ?_
      change Circle.exp (0 * _) = 1
      rw [zero_mul, Circle.exp_zero]
    rw [this]; exact Subgroup.one_mem _
  have hopen :
      χ ⁻¹' (lcaAnnihilator k :
        Set (PontryaginDual (Multiplicative (InfiniteAdeleRing F)))) ∈ 𝓝 (0 : ℝ) :=
    IsOpen.mem_nhds (hk.preimage hχ) h0
  obtain ⟨l, u, hlu, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hopen
  have hll0 : l < 0 := (Set.mem_Ioo.mp hlu).1
  have h0u : 0 < u := (Set.mem_Ioo.mp hlu).2
  have hcpos : 0 < |c| := abs_pos.mpr hφ
  set t := min (min (-l) u * 2⁻¹) (Real.pi / |c|) with ht
  have hwpos : 0 < min (-l) u := lt_min (by linarith) h0u
  have htpos : 0 < t :=
    lt_min (mul_pos hwpos (by norm_num : (0:ℝ) < 2⁻¹)) (div_pos Real.pi_pos hcpos)
  have hmem : χ t ∈ lcaAnnihilator k := by
    refine hsub (Set.mem_Ioo.mpr ⟨lt_trans hll0 htpos, ?_⟩)
    calc t ≤ min (-l) u * 2⁻¹ := min_le_left _ _
      _ ≤ u * 2⁻¹ :=
        mul_le_mul_of_nonneg_right (min_le_right (-l) u) (by norm_num : (0:ℝ) ≤ 2⁻¹)
      _ < u := by
        calc u * 2⁻¹ < u * 1 := mul_lt_mul_of_pos_left two_inv_lt_one h0u
          _ = u := mul_one u
  have htc : |t * c| ≤ Real.pi := by
    rw [abs_mul, abs_of_pos htpos]
    calc t * |c| ≤ (Real.pi / |c|) * |c| := by gcongr; exact min_le_right _ _
      _ = Real.pi := div_mul_cancel₀ _ hcpos.ne'
  have : T2Space (Multiplicative (InfiniteAdeleRing F)) := by
    change T2Space (∀ w : InfinitePlace F, w.Completion)
    infer_instance
  have h1 := (mem_lcaAnnihilator_iff k (χ t)).mp hmem ⟨y, hy⟩
  change Circle.exp (t * c) = 1 at h1
  obtain ⟨n, hn⟩ := Circle.exp_eq_one.mp h1
  have htc0 : t * c ≠ 0 := mul_ne_zero htpos.ne' hφ
  have hn0 : n ≠ 0 := by rintro rfl; exact htc0 (by simpa using hn)
  have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hn0
  have heq : |t * c| = |(n : ℝ)| * (2 * Real.pi) := by
    rw [hn, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
  nlinarith [Real.pi_pos, heq]

/-- On the open subgroup of a structural pair of the infinite adeles, the mixed-space norm is
controlled linearly by the real and lattice coordinates of any elementary presentation. -/
private theorem infinite_presentation_mixedSpace_bound
    (a : BruhatStructuralPair (Multiplicative (InfiniteAdeleRing F)))
    (e : ElementaryLCAPresentation a.quotient) :
    ∃ A B : ℝ, 0 ≤ A ∧ ∀ (y : Multiplicative (InfiniteAdeleRing F)) (hy : y ∈ a.val.1),
      ‖InfiniteAdeleRing.ringEquiv_mixedSpace F (Multiplicative.toAdd y)‖ ≤
        A * (∑ j, |(Multiplicative.toAdd (e.equiv (QuotientGroup.mk ⟨y, hy⟩))).1 j| +
          ∑ k, |((Multiplicative.toAdd (e.equiv (QuotientGroup.mk ⟨y, hy⟩))).2.2.1 k : ℝ)|) +
          B := by
  have hgood := a.property.2.2.1
  let m : InfiniteAdeleRing F → mixedEmbedding.mixedSpace F :=
    fun z => InfiniteAdeleRing.ringEquiv_mixedSpace F z
  have hm : Continuous m := continuous_ringEquiv_mixedSpace
  let h0 : a.val.1 →* Multiplicative (mixedEmbedding.mixedSpace F) :=
    { toFun := fun u => Multiplicative.ofAdd (m (Multiplicative.toAdd u.val))
      map_one' := by
        show Multiplicative.ofAdd (InfiniteAdeleRing.ringEquiv_mixedSpace F 0) = 1
        rw [map_zero]; rfl
      map_mul' := fun u v => by
        show Multiplicative.ofAdd (InfiniteAdeleRing.ringEquiv_mixedSpace F
          ((Multiplicative.toAdd u.val) + (Multiplicative.toAdd v.val))) = _
        rw [map_add]; rfl }
  have hker : ∀ u ∈ (OrderDual.ofDual a.val.2).comap a.val.1.subtype, h0 u = 1 := fun u hu => by
    have := infinite_mixedSpace_eq_zero_of_isOpen_lcaAnnihilator hgood.2.1
      (Subgroup.mem_comap.mp hu)
    show Multiplicative.ofAdd (InfiniteAdeleRing.ringEquiv_mixedSpace F
      (Multiplicative.toAdd u.val)) = 1
    rw [Subgroup.coe_subtype] at this
    rw [this]; rfl
  let lift : a.quotient →* Multiplicative (mixedEmbedding.mixedSpace F) :=
    QuotientGroup.lift _ h0 hker
  have hh0 : Continuous h0 := continuous_ofAdd.comp (hm.comp (continuous_toAdd.comp
    continuous_subtype_val))
  have hlift : Continuous lift := (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr hh0
  have key : ∀ w₁ w₂ : ElementaryLieGroup e.realDim e.torusDim e.latticeRank
      e.finiteFactor, e.equiv.symm (Multiplicative.ofAdd (w₁ + w₂)) =
        e.equiv.symm (Multiplicative.ofAdd w₁) * e.equiv.symm (Multiplicative.ofAdd w₂) :=
    fun w₁ w₂ => e.equiv.symm.map_mul (Multiplicative.ofAdd w₁) (Multiplicative.ofAdd w₂)
  let P : ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor →
      mixedEmbedding.mixedSpace F :=
    fun w => Multiplicative.toAdd (lift (e.equiv.symm (Multiplicative.ofAdd w)))
  have hPadd : ∀ w₁ w₂, P (w₁ + w₂) = P w₁ + P w₂ := (fun w₁ w₂ => by
        have h1 := key w₁ w₂
        have h2 := congrArg (fun z => Multiplicative.toAdd (lift z)) h1
        have h3 := map_mul lift (e.equiv.symm (Multiplicative.ofAdd w₁))
          (e.equiv.symm (Multiplicative.ofAdd w₂))
        have h4 := congrArg Multiplicative.toAdd h3
        exact (h2.trans h4).trans (toAdd_mul _ _))
  have hP : Continuous P := continuous_toAdd.comp (hlift.comp (e.equiv.symm.continuous.comp
    continuous_ofAdd))
  have H := elementary_additive_norm_le (m := e.realDim) (n := e.torusDim)
    (r := e.latticeRank) (Fk := e.finiteFactor) (V := mixedEmbedding.mixedSpace F) P hP hPadd
  obtain ⟨A, B, hA, hAB⟩ := H
  refine ⟨A, B, hA, ?_⟩
  intro y hy
  have h1 := congrArg (fun z => Multiplicative.toAdd (lift z))
      (e.equiv.symm_apply_apply (QuotientGroup.mk ⟨y, hy⟩))
  have h2 : lift (QuotientGroup.mk ⟨y, hy⟩) = h0 ⟨y, hy⟩ := QuotientGroup.lift_mk _ _ _
  have h3 : Multiplicative.toAdd (h0 ⟨y, hy⟩) =
      InfiniteAdeleRing.ringEquiv_mixedSpace F (Multiplicative.toAdd y) := rfl
  have hPy : P (Multiplicative.toAdd (e.equiv (QuotientGroup.mk ⟨y, hy⟩))) =
      InfiniteAdeleRing.ringEquiv_mixedSpace F (Multiplicative.toAdd y) := by
    exact (h1.trans (congrArg Multiplicative.toAdd h2)).trans h3
  exact (le_of_eq (congrArg norm hPy.symm)).trans
    (hAB (Multiplicative.toAdd (e.equiv (QuotientGroup.mk ⟨y, hy⟩))))

/-- A stage realization on the infinite adeles decays faster than any power of the mixed-space
norm. -/
private theorem infinite_realization_decay
    (a : BruhatStructuralPair (Multiplicative (InfiniteAdeleRing F)))
    (e : ElementaryLCAPresentation a.quotient) (s : SchwartzBruhatStage e) (N : ℕ) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ y : Multiplicative (InfiniteAdeleRing F),
      ‖schwartzBruhatStageRealization a e s y‖ *
        (1 + ‖InfiniteAdeleRing.ringEquiv_mixedSpace F (Multiplicative.toAdd y)‖) ^ N ≤ C₀ := by
  obtain ⟨A, B, hA, hAB⟩ := infinite_presentation_mixedSpace_bound a e
  obtain ⟨C, hC⟩ := elementarySchwartz_decay (m := e.realDim) (n := e.torusDim)
    (r := e.latticeRank) (Fk := e.finiteFactor)
    (f := (show elementarySchwartzSubmodule _ _ _ _ from s).val)
    (show elementarySchwartzSubmodule _ _ _ _ from s).2 N
  refine ⟨(1 + A + max B 0) ^ N * max C 0, by positivity, fun y => ?_⟩
  by_cases hy : y ∈ a.val.1
  · rw [schwartzBruhatStageRealization_apply_dite, dite_eq_left hy]
    have hC' := hC (Multiplicative.toAdd (e.equiv (QuotientGroup.mk ⟨y, hy⟩)))
    exact real_decay_aux (norm_nonneg _)
      (add_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)
        (Finset.sum_nonneg fun _ _ => abs_nonneg _)) hA (norm_nonneg _) (hAB y hy) hC'
  · rw [schwartzBruhatStageRealization_apply_dite, dite_eq_right hy, norm_zero, zero_mul]
    positivity

/-- Membership in the inverse of the principal fractional ideal `(b)` is integrality of `b * ξ`. -/
private theorem mem_inv_spanSingleton_algebraMap {b0 : 𝓞 F} (hb0 : b0 ≠ 0) (ξ : F) :
    ξ ∈ FractionalIdeal.spanSingleton (𝓞 F)⁰ ((algebraMap (𝓞 F) F b0)⁻¹) ↔
      algebraMap (𝓞 F) F b0 * ξ ∈ (algebraMap (𝓞 F) F).range := by
  set β : F := algebraMap (𝓞 F) F b0
  have hβ : β ≠ 0 := by
    intro h
    exact hb0 ((IsFractionRing.injective (𝓞 F) F) (by simpa [β] using h))
  rw [FractionalIdeal.mem_spanSingleton]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    have hz' : algebraMap (𝓞 F) F z * β⁻¹ = ξ := by simpa [Algebra.smul_def] using hz
    calc algebraMap (𝓞 F) F z = (algebraMap (𝓞 F) F z * β⁻¹) * β := by
          rw [mul_assoc, inv_mul_cancel₀ hβ, mul_one]
      _ = ξ * β := by rw [hz']
      _ = algebraMap (𝓞 F) F b0 * ξ := by rw [mul_comm]
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    rw [Algebra.smul_def, hz, mul_assoc, mul_comm ξ β⁻¹, ← mul_assoc,
      mul_inv_cancel₀ hβ, one_mul]

/-- If `b` clears the denominator of `g⁻¹` at every finite place and `g * ξ` is integral there,
then `b * ξ` is an algebraic integer. -/
private theorem mul_algebraMap_mem_integers_of_idele (b0 : 𝓞 F) (g : 𝕀[F]) (ξ : F)
    (hg : ∀ v : HeightOneSpectrum (𝓞 F),
      (algebraMap (𝓞 F) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) b0 * (g⁻¹).val.2) v ∈
        v.adicCompletionIntegers F)
    (hξ : ∀ v : HeightOneSpectrum (𝓞 F),
      (g : 𝔸[F]).2 v * (ξ : v.adicCompletion F) ∈ v.adicCompletionIntegers F) :
    algebraMap (𝓞 F) F b0 * ξ ∈ (algebraMap (𝓞 F) F).range := by
  refine mem_integers_of_forall_mem_adicCompletionIntegers ?_
  intro v
  have hgv : (g⁻¹).val.2 v * (g : 𝔸[F]).2 v = 1 :=
    congrArg (fun z : 𝔸[F] => z.2 v) (Units.inv_mul g)
  have hB : ((algebraMap (𝓞 F) F b0 : F) : v.adicCompletion F) * (g⁻¹).val.2 v ∈
      v.adicCompletionIntegers F := hg v
  have hcoe : ((algebraMap (𝓞 F) F b0 * ξ : F) : v.adicCompletion F) =
      (((algebraMap (𝓞 F) F b0 : F) : v.adicCompletion F) * (g⁻¹).val.2 v) *
        ((g : 𝔸[F]).2 v * (ξ : v.adicCompletion F)) := by
    simp only [HeightOneSpectrum.adicCompletion.coe_mul]
    rw [← mul_one (((algebraMap (𝓞 F) F b0 : F) : v.adicCompletion F) *
      (ξ : v.adicCompletion F)), ← hgv]
    ring
  change ((algebraMap (𝓞 F) F b0 * ξ : F) : v.adicCompletion F) ∈ v.adicCompletionIntegers F
  rw [hcoe]
  exact mul_mem hB (hξ v)

set_option maxHeartbeats 1800000 in
/-- The norm of one infinite-adele stage, sampled on a fixed fractional ideal, is summable. -/
private theorem summable_infinite_realization_on_fractional
    (a : BruhatStructuralPair (Multiplicative (InfiniteAdeleRing F)))
    (e : ElementaryLCAPresentation a.quotient) (s : SchwartzBruhatStage e)
    {b0 : 𝓞 F} (hb0 : b0 ≠ 0) (z : (InfiniteAdeleRing F)ˣ) :
    Summable (fun ξ : {ξ : Fˣ // algebraMap (𝓞 F) F b0 * (ξ.val : F) ∈
        (algebraMap (𝓞 F) F).range} ↦
      ‖schwartzBruhatStageRealization a e s (Multiplicative.ofAdd
        (z.val * algebraMap F (InfiniteAdeleRing F) (ξ.val : F)))‖) := by
  let N := Module.finrank ℤ (mixedEmbedding.integerLattice F) + 1
  have hN : Module.finrank ℤ (mixedEmbedding.integerLattice F) < N := Nat.lt_succ_self _
  obtain ⟨C₀, hC₀0, hC₀⟩ := infinite_realization_decay a e s N
  let R := ‖InfiniteAdeleRing.ringEquiv_mixedSpace F (z⁻¹).val‖
  have hR0 : 0 ≤ R := norm_nonneg _
  let S := {ξ : Fˣ | algebraMap (𝓞 F) F b0 * (ξ : F) ∈ (algebraMap (𝓞 F) F).range}
  have hsumS : Summable (fun ξ : {ξ : Fˣ // ξ ∈ S} ↦
      ((1 + ‖mixedEmbedding F (ξ.val : F)‖) ^ N)⁻¹) :=
    (summable_subtype_iff_indicator (f := fun ξ : Fˣ ↦
      ((1 + ‖mixedEmbedding F (ξ : F)‖) ^ N)⁻¹) (s := S)).mpr
      (by simpa [S] using summable_indicator_inv_one_add_norm_pow b0 hb0 N hN)
  refine ((hsumS.mul_left ((1 + R) ^ N * C₀)).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun ξ => ?_))
  let y : Multiplicative (InfiniteAdeleRing F) :=
    Multiplicative.ofAdd (z.val * algebraMap F (InfiniteAdeleRing F) (ξ.val : F))
  have hdecay := hC₀ y
  have hmul_inv : mixedEmbedding F (ξ.val : F) =
      InfiniteAdeleRing.ringEquiv_mixedSpace F (z⁻¹).val *
        InfiniteAdeleRing.ringEquiv_mixedSpace F
          (z.val * algebraMap F (InfiniteAdeleRing F) (ξ.val : F)) := by
    rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
    have hinv : (z⁻¹).val * z.val = 1 := Units.inv_mul z
    calc InfiniteAdeleRing.ringEquiv_mixedSpace F
          (algebraMap F (InfiniteAdeleRing F) (ξ.val : F))
        = InfiniteAdeleRing.ringEquiv_mixedSpace F
            ((z⁻¹).val * z.val * algebraMap F (InfiniteAdeleRing F) (ξ.val : F)) := by
          rw [hinv, one_mul]
      _ = InfiniteAdeleRing.ringEquiv_mixedSpace F
            ((z⁻¹).val * (z.val * algebraMap F (InfiniteAdeleRing F) (ξ.val : F))) := by
          rw [mul_assoc]
      _ = InfiniteAdeleRing.ringEquiv_mixedSpace F (z⁻¹).val *
            InfiniteAdeleRing.ringEquiv_mixedSpace F
              (z.val * algebraMap F (InfiniteAdeleRing F) (ξ.val : F)) :=
          map_mul _ _ _
  set μ := ‖mixedEmbedding F (ξ.val : F)‖
  set t := ‖InfiniteAdeleRing.ringEquiv_mixedSpace F (Multiplicative.toAdd y)‖
  have hμ : μ ≤ R * t := by
    dsimp [μ, t, y, R]
    rw [hmul_inv]
    exact norm_mul_le _ _
  have ht0 : 0 ≤ t := by simpa only [t] using norm_nonneg _
  have hμ0 : 0 ≤ μ := by simpa only [μ] using norm_nonneg _
  have hlin : 1 + μ ≤ (1 + R) * (1 + t) := by nlinarith [hμ, ht0, hμ0, hR0]
  have hbase : 0 ≤ 1 + μ := by linarith [hμ0]
  have hpow : (1 + μ) ^ N ≤ ((1 + R) * (1 + t)) ^ N := pow_le_pow_left₀ hbase hlin N
  have hdecay' : ‖schwartzBruhatStageRealization a e s y‖ * (1 + t) ^ N ≤ C₀ := by
    simpa only [t, y] using hdecay
  have hbound : ‖schwartzBruhatStageRealization a e s y‖ * (1 + μ) ^ N ≤ (1 + R) ^ N * C₀ := by
    calc ‖schwartzBruhatStageRealization a e s y‖ * (1 + μ) ^ N
        ≤ ‖schwartzBruhatStageRealization a e s y‖ * ((1 + R) * (1 + t)) ^ N :=
          mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
      _ = (1 + R) ^ N * (‖schwartzBruhatStageRealization a e s y‖ * (1 + t) ^ N) := by
          rw [mul_pow]; ring
      _ ≤ (1 + R) ^ N * C₀ :=
          mul_le_mul_of_nonneg_left hdecay' (by positivity)
  have hpos : 0 < (1 + μ) ^ N := by
    have : 0 < 1 + μ := by linarith [hμ0]
    exact pow_pos this _
  have hineq : ‖schwartzBruhatStageRealization a e s y‖ ≤
      (1 + R) ^ N * C₀ * ((1 + μ) ^ N)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hpos]
    exact hbound
  dsimp only [y, μ]
  exact hineq

set_option maxHeartbeats 1800000 in
/-- Sampling a Schwartz–Bruhat function of the infinite adeles along a fractional ideal is
summable. -/
private theorem summable_schwartz_infinite_on_integrality
    (arch : SchwartzBruhat (Multiplicative (InfiniteAdeleRing F)))
    {b0 : 𝓞 F} (hb0 : b0 ≠ 0) (z : (InfiniteAdeleRing F)ˣ) :
    Summable (fun ξ : {ξ : Fˣ // algebraMap (𝓞 F) F b0 * (ξ.val : F) ∈
        (algebraMap (𝓞 F) F).range} ↦
      ‖arch (Multiplicative.ofAdd
        (z.val * algebraMap F (InfiniteAdeleRing F) (ξ.val : F)))‖) := by
  have hf := (show schwartzBruhatSubmodule (Multiplicative (InfiniteAdeleRing F)) from arch).2
  have hzero : Summable (fun ξ : {ξ : Fˣ // algebraMap (𝓞 F) F b0 * (ξ.val : F) ∈
      (algebraMap (𝓞 F) F).range} ↦
      ‖(0 : Multiplicative (InfiniteAdeleRing F) → ℂ) (Multiplicative.ofAdd
        (z.val * algebraMap F (InfiniteAdeleRing F) (ξ.val : F)))‖) := by
    simp
  have hadd (φ ψ : Multiplicative (InfiniteAdeleRing F) → ℂ)
      (hφ : Summable (fun ξ : {ξ : Fˣ // algebraMap (𝓞 F) F b0 * (ξ.val : F) ∈
        (algebraMap (𝓞 F) F).range} ↦ ‖φ (Multiplicative.ofAdd
          (z.val * algebraMap F (InfiniteAdeleRing F) (ξ.val : F)))‖))
      (hψ : Summable (fun ξ : {ξ : Fˣ // algebraMap (𝓞 F) F b0 * (ξ.val : F) ∈
        (algebraMap (𝓞 F) F).range} ↦ ‖ψ (Multiplicative.ofAdd
          (z.val * algebraMap F (InfiniteAdeleRing F) (ξ.val : F)))‖)) :
      Summable (fun ξ : {ξ : Fˣ // algebraMap (𝓞 F) F b0 * (ξ.val : F) ∈
        (algebraMap (𝓞 F) F).range} ↦ ‖(φ + ψ) (Multiplicative.ofAdd
          (z.val * algebraMap F (InfiniteAdeleRing F) (ξ.val : F)))‖) := by
    refine (hφ.add hψ).of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun ξ ↦
      norm_add_le _ _
  refine Submodule.iSup_induction _
    (motive := fun φ ↦ Summable (fun ξ : {ξ : Fˣ // algebraMap (𝓞 F) F b0 * (ξ.val : F) ∈
        (algebraMap (𝓞 F) F).range} ↦ ‖φ (Multiplicative.ofAdd
          (z.val * algebraMap F (InfiniteAdeleRing F) (ξ.val : F)))‖))
    hf ?_ hzero hadd
  intro a φ hφ
  refine Submodule.iSup_induction _
    (motive := fun φ ↦ Summable (fun ξ : {ξ : Fˣ // algebraMap (𝓞 F) F b0 * (ξ.val : F) ∈
        (algebraMap (𝓞 F) F).range} ↦ ‖φ (Multiplicative.ofAdd
          (z.val * algebraMap F (InfiniteAdeleRing F) (ξ.val : F)))‖))
    hφ ?_ hzero hadd
  intro e φ hφ
  obtain ⟨s, rfl⟩ := LinearMap.mem_range.mp hφ
  exact summable_infinite_realization_on_fractional a e s hb0 z

end ArchimedeanFractional

open scoped Pointwise nonZeroDivisors in
/-- Paper: Lemma 2.2.2.1(3), p. 78. For a product of an Archimedean Schwartz
function and local indicators as in (2.2.2.2), a single fractional ideal gives
the summable Archimedean upper bound (2.2.2.3).
Deviation: The whole idele varies over the canonical norm section times the
norm-one fundamental domain used in the proof. -/
theorem adelicAverage_at_zero_le_fractionalIdeal
    (b : Module.Basis (Fin (Units.rank F)) ℤ (Additive ((𝓞 F)ˣ ⧸ Units.torsion F)))
    (v₀ : InfinitePlace F) (σ : ℂ ≃ₐ[ℝ] ℂ)
    (r : CommRing.Pic (𝓞 F) → (ideleNorm F).ker) (hr₁ : r 1 = 1)
    (hr : ∀ c, ideleIdealClass F (r c).val = c)
    (f : ℬ[F]) (arch : SchwartzBruhat (Multiplicative (InfiniteAdeleRing F)))
    (K : (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) → Set (v.adicCompletion F))
    (hK : ∀ v, IsCompact (K v) ∧ IsOpen (K v) ∧
      K v ⊆ (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (hKcofinite : ∀ᶠ v in cofinite, K v = (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (hf : ∀ x : 𝔸[F], f (Multiplicative.ofAdd x) = arch (Multiplicative.ofAdd x.1) *
      Set.indicator {y : 𝔸ᶠ[F] | ∀ v, y v ∈ K v} (fun _ ↦ (1 : ℂ)) x.2) :
    ∃ I : FractionalIdeal (𝓞 F)⁰ F,
      ∀ g ∈ Set.range (canonicalIdeleNormSection F) *
          ((ideleNorm F).ker.subtype '' ideleFundamentalDomain F b v₀ σ r),
        let term := fun ξ : {ξ : Fˣ // (ξ : F) ∈ I} ↦
          ‖arch (Multiplicative.ofAdd (g.val.1 * algebraMap F (InfiniteAdeleRing F) (ξ.val : F)))‖
        Summable term ∧
          (∑' ξ : Fˣ, ‖f (Multiplicative.ofAdd (g.val * algebraMap F 𝔸[F] (ξ : F)))‖) ≤
            ∑' ξ, term ξ := by
  classical
  let E₁ := ideleFundamentalDomain F b v₀ σ r
  have hcompact : IsCompact (closure E₁) :=
    ideleFundamentalDomain_precompact F b v₀ σ r hr₁ hr
  let finInv : (ideleNorm F).ker → IsDedekindDomain.FiniteAdeleRing (𝓞 F) F :=
    fun x => ((x : 𝕀[F])⁻¹).val.2
  have hcont : Continuous finInv :=
    continuous_snd.comp (Units.continuous_val.comp
      (continuous_inv.comp continuous_subtype_val))
  obtain ⟨b0, hb0, hbΩ⟩ :=
    exists_mul_mem_adicCompletionIntegers_of_isCompact (hcompact.image hcont)
  refine ⟨FractionalIdeal.spanSingleton (𝓞 F)⁰ ((algebraMap (𝓞 F) F b0)⁻¹), ?_⟩
  intro g hg
  dsimp only
  obtain ⟨s, hs, u, hu, rfl⟩ := Set.mem_mul.mp hg
  obtain ⟨t, ht⟩ := hs
  obtain ⟨x, hx, hxu⟩ := hu
  rw [← ht, ← hxu]
  set g0 : 𝕀[F] := canonicalIdeleNormSection F t * (ideleNorm F).ker.subtype x with hg0def
  have hfin : (g0⁻¹).val.2 = ((x : 𝕀[F])⁻¹).val.2 := by
    have hsinv : ((canonicalIdeleNormSection F t)⁻¹).val.2 = 1 := by
      rw [← map_inv (canonicalIdeleNormSection F)]
      simpa using canonicalIdeleNormSection_finite F (t⁻¹)
    have hmul : (canonicalIdeleNormSection F t * (ideleNorm F).ker.subtype x)⁻¹ =
        ((ideleNorm F).ker.subtype x)⁻¹ * (canonicalIdeleNormSection F t)⁻¹ := by
      simp [mul_inv_rev]
    rw [hg0def, hmul, Units.val_mul, Prod.snd_mul, hsinv, mul_one]
    rfl
  have hint : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      (algebraMap (𝓞 F) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) b0 * (g0⁻¹).val.2) v ∈
        v.adicCompletionIntegers F := by
    intro v
    rw [hfin]
    exact hbΩ (((x : 𝕀[F])⁻¹).val.2) ⟨x, subset_closure hx, rfl⟩ v
  let z : (InfiniteAdeleRing F)ˣ := Units.map
    (RingHom.fst (InfiniteAdeleRing F) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)).toMonoidHom
    g0
  have hz : z.val = g0.val.1 := rfl
  have hsumS := summable_schwartz_infinite_on_integrality (F := F) arch hb0 z
  let termξ (ξ : Fˣ) : ℝ :=
    ‖arch (Multiplicative.ofAdd (z.val * algebraMap F (InfiniteAdeleRing F) (ξ : F)))‖
  have hmemξ (ξ : Fˣ) : (ξ : F) ∈ FractionalIdeal.spanSingleton (𝓞 F)⁰
      ((algebraMap (𝓞 F) F b0)⁻¹) ↔
      algebraMap (𝓞 F) F b0 * (ξ : F) ∈ (algebraMap (𝓞 F) F).range :=
    mem_inv_spanSingleton_algebraMap hb0 (ξ : F)
  have hIndS : Summable ({ξ : Fˣ | algebraMap (𝓞 F) F b0 * (ξ : F) ∈
      (algebraMap (𝓞 F) F).range}.indicator termξ) :=
    (summable_subtype_iff_indicator).mp hsumS
  have hIndI : Summable ({ξ : Fˣ | (ξ : F) ∈ FractionalIdeal.spanSingleton (𝓞 F)⁰
      ((algebraMap (𝓞 F) F b0)⁻¹)}.indicator termξ) := by
    refine hIndS.congr fun ξ ↦ ?_
    by_cases hξ : algebraMap (𝓞 F) F b0 * (ξ : F) ∈ (algebraMap (𝓞 F) F).range
    · have hI : ξ ∈ {ξ : Fˣ | (ξ : F) ∈ FractionalIdeal.spanSingleton (𝓞 F)⁰
          ((algebraMap (𝓞 F) F b0)⁻¹)} := (hmemξ ξ).2 hξ
      have hSξ : ξ ∈ {ξ : Fˣ | algebraMap (𝓞 F) F b0 * (ξ : F) ∈
          (algebraMap (𝓞 F) F).range} := hξ
      rw [Set.indicator_of_mem hSξ, Set.indicator_of_mem hI]
    · have hI : ξ ∉ {ξ : Fˣ | (ξ : F) ∈ FractionalIdeal.spanSingleton (𝓞 F)⁰
          ((algebraMap (𝓞 F) F b0)⁻¹)} := fun h ↦ hξ ((hmemξ ξ).1 h)
      have hSξ : ξ ∉ {ξ : Fˣ | algebraMap (𝓞 F) F b0 * (ξ : F) ∈
          (algebraMap (𝓞 F) F).range} := hξ
      rw [Set.indicator_of_notMem hSξ, Set.indicator_of_notMem hI]
  have hsumTerm : Summable (fun ξ : {ξ : Fˣ // (ξ : F) ∈
      FractionalIdeal.spanSingleton (𝓞 F)⁰ ((algebraMap (𝓞 F) F b0)⁻¹)} ↦ termξ ξ.val) :=
    (summable_subtype_iff_indicator).mpr hIndI
  refine ⟨?_, ?_⟩
  · rw [← hz]
    exact hsumTerm
  · let S : Set Fˣ := {ξ | (ξ : F) ∈ FractionalIdeal.spanSingleton (𝓞 F)⁰
      ((algebraMap (𝓞 F) F b0)⁻¹)}
    have hvanish : ∀ ξ : Fˣ, ξ ∉ S →
        ‖f (Multiplicative.ofAdd (g0.val * algebraMap F 𝔸[F] (ξ : F)))‖ = 0 := by
      intro ξ hξ
      have hnot : g0.val.2 * (algebraMap F 𝔸[F] (ξ : F)).2 ∉
          {y : 𝔸ᶠ[F] | ∀ v, y v ∈ K v} := by
        intro hy
        apply hξ
        change (ξ : F) ∈ FractionalIdeal.spanSingleton (𝓞 F)⁰ ((algebraMap (𝓞 F) F b0)⁻¹)
        rw [mem_inv_spanSingleton_algebraMap hb0]
        refine mul_algebraMap_mem_integers_of_idele b0 g0 (ξ : F) hint ?_
        intro v
        exact (hK v).2.2 (hy v)
      have hfξ := hf (g0.val * algebraMap F 𝔸[F] (ξ : F))
      rw [hfξ, Prod.snd_mul, Set.indicator_of_notMem hnot, mul_zero, norm_zero]
    have key : ∀ ξ : Fˣ,
        ‖f (Multiplicative.ofAdd (g0.val * algebraMap F 𝔸[F] (ξ : F)))‖ ≤
          ‖arch (Multiplicative.ofAdd (g0.val.1 * algebraMap F (InfiniteAdeleRing F)
            (ξ : F)))‖ := by
      intro ξ
      have hfξ := hf (g0.val * algebraMap F 𝔸[F] (ξ : F))
      have hexp2 : Prod.fst (g0.val * algebraMap F 𝔸[F] (ξ : F)) =
          g0.val.1 * (algebraMap F 𝔸[F] (ξ : F)).1 :=
        Prod.fst_mul g0.val (algebraMap F 𝔸[F] (ξ : F))
      have hexp : g0.val.1 * (algebraMap F 𝔸[F] (ξ : F)).1 =
          g0.val.1 * algebraMap F (InfiniteAdeleRing F) (ξ : F) := by
        rw [NumberField.AdeleRing.algebraMap_fst_def]
      rw [hfξ, norm_mul, hexp2, hexp]
      refine mul_le_of_le_one_right (norm_nonneg _) ?_
      by_cases hy : (g0.val * algebraMap F 𝔸[F] (ξ : F)).2 ∈
        {y : 𝔸ᶠ[F] | ∀ v, y v ∈ K v}
      · simp only [Set.indicator_of_mem hy, norm_one, le_refl]
      · rw [Set.indicator_of_notMem hy, norm_zero]
        exact zero_le_one
    have hintfun : (fun ξ : Fˣ ↦
        ‖f (Multiplicative.ofAdd (g0.val * algebraMap F 𝔸[F] (ξ : F)))‖) =
        S.indicator (fun ξ : Fˣ ↦
          ‖f (Multiplicative.ofAdd (g0.val * algebraMap F 𝔸[F] (ξ : F)))‖) := by
      funext ξ
      by_cases hξ : ξ ∈ S
      · simp [hξ]
      · simp [hξ, hvanish ξ hξ]
    have harchξ : ∀ ξ : Fˣ, termξ ξ = ‖arch (Multiplicative.ofAdd (g0.val.1 *
        algebraMap F (InfiniteAdeleRing F) (ξ : F)))‖ := fun ξ => by rw [← hz]
    have hIndG : Summable (S.indicator (fun ξ : Fˣ ↦
        ‖arch (Multiplicative.ofAdd (g0.val.1 * algebraMap F (InfiniteAdeleRing F)
          (ξ : F)))‖)) := by
      refine hIndI.congr fun ξ => ?_
      by_cases hξ : ξ ∈ S
      · rw [Set.indicator_of_mem hξ, Set.indicator_of_mem hξ, harchξ ξ]
      · rw [Set.indicator_of_notMem hξ, Set.indicator_of_notMem hξ]
    have hdom : ∀ ξ : Fˣ,
        S.indicator (fun ξ : Fˣ ↦
          ‖f (Multiplicative.ofAdd (g0.val * algebraMap F 𝔸[F] (ξ : F)))‖) ξ ≤
          S.indicator (fun ξ : Fˣ ↦
            ‖arch (Multiplicative.ofAdd (g0.val.1 * algebraMap F (InfiniteAdeleRing F)
              (ξ : F)))‖) ξ := by
      intro ξ
      by_cases hξ : ξ ∈ S
      · rw [Set.indicator_of_mem hξ, Set.indicator_of_mem hξ]
        exact key ξ
      · rw [Set.indicator_of_notMem hξ, Set.indicator_of_notMem hξ]
    have hsumIndF : Summable (S.indicator (fun ξ : Fˣ ↦
        ‖f (Multiplicative.ofAdd (g0.val * algebraMap F 𝔸[F] (ξ : F)))‖)) :=
      hIndG.of_nonneg_of_le
        (fun ξ => Set.indicator_nonneg (fun _ _ => norm_nonneg _) ξ) hdom
    calc (∑' ξ : Fˣ, ‖f (Multiplicative.ofAdd (g0.val * algebraMap F 𝔸[F] (ξ : F)))‖)
        = ∑' ξ : Fˣ, S.indicator (fun ξ : Fˣ ↦
            ‖f (Multiplicative.ofAdd (g0.val * algebraMap F 𝔸[F] (ξ : F)))‖) ξ :=
          congrArg (fun g : Fˣ → ℝ => ∑' ξ : Fˣ, g ξ) hintfun
      _ ≤ ∑' ξ : Fˣ, S.indicator (fun ξ : Fˣ ↦
            ‖arch (Multiplicative.ofAdd (g0.val.1 * algebraMap F (InfiniteAdeleRing F)
              (ξ : F)))‖) ξ := hsumIndF.tsum_le_tsum hdom hIndG
      _ = ∑' ξ : {ξ : Fˣ // ξ ∈ S}, ‖arch (Multiplicative.ofAdd (g0.val.1 *
            algebraMap F (InfiniteAdeleRing F) (ξ.val : F)))‖ := (tsum_subtype S _).symm

/-- Paper: Definition 2.2.3.1, p. 81. The global adelic theta function descends
the average at `x = 0` to a continuous function on the idele class group. -/
def adelicTheta (f : ℬ[F]) : C(C[F], ℂ) :=
  IsQuotientMap.lift (f := ⟨classOf, QuotientGroup.continuous_mk⟩)
    (QuotientGroup.isQuotientMap_mk (IdeleGroup.principalSubgroup (𝓞 F) F))
    ⟨fun g ↦ adelicAverage f g 0, adelicAverage_at_zero_continuous f⟩
    (adelicAverage_at_zero_factorsThrough f)

/-- Paper: Definition 2.2.3.1, p. 81. At the class of an idele, theta sums
the test function over its nonzero principal multiples. -/
theorem adelicTheta_mk (f : ℬ[F]) (g : 𝕀[F]) :
    adelicTheta f (classOf g) =
      ∑' ξ : Fˣ, f (Multiplicative.ofAdd (algebraMap F 𝔸[F] (ξ : F) * g.val)) := by
  calc
    adelicTheta f (classOf g) = adelicAverage f g 0 :=
      DFunLike.congr_fun (IsQuotientMap.lift_comp (f := ⟨classOf, QuotientGroup.continuous_mk⟩)
        (QuotientGroup.isQuotientMap_mk _) ⟨_, adelicAverage_at_zero_continuous f⟩
        (adelicAverage_at_zero_factorsThrough f)) g
    _ = _ := by simp only [adelicAverage, add_zero, mul_comm g.val]

/-- Paper: Definition 2.2.3.1, p. 82. Formation of the global adelic theta
function is complex linear. -/
theorem adelicTheta_isLinear : IsLinearMap ℂ (adelicTheta (F := F)) := by
  have htheta (f : ℬ[F]) (g : 𝕀[F]) : adelicTheta f (classOf g) = adelicAverage f g 0 :=
    DFunLike.congr_fun (IsQuotientMap.lift_comp (f := ⟨classOf, QuotientGroup.continuous_mk⟩)
      (QuotientGroup.isQuotientMap_mk _) ⟨_, adelicAverage_at_zero_continuous f⟩
      (adelicAverage_at_zero_factorsThrough f)) g
  have hs (f : ℬ[F]) (g : 𝕀[F]) :
      Summable (fun ξ : Fˣ ↦ f (Multiplicative.ofAdd (g.val * (algebraMap F 𝔸[F] (ξ : F) + 0)))) :=
    ((adelicAverage_summableUniformlyOn f {(g, 0)} isCompact_singleton).summable rfl).of_norm
  have hsurj : Surjective (classOf : 𝕀[F] → C[F]) := QuotientGroup.mk_surjective
  constructor
  · refine fun f h ↦ ContinuousMap.ext (hsurj.forall.mpr fun g ↦ ?_)
    simp only [ContinuousMap.add_apply, htheta]
    exact (hs f g).tsum_add (hs h g)
  · refine fun c f ↦ ContinuousMap.ext (hsurj.forall.mpr fun g ↦ ?_)
    simp only [ContinuousMap.smul_apply, htheta]
    exact tsum_mul_left

local instance : MeasurableSpace 𝔸[F] := borel _

/-- A topological group isomorphism carries a compact generating neighborhood to one. -/
private theorem isCompactlyGeneratedGroup_of_equiv {G H : Type*}
    [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
    (e : G ≃ₜ* H) (h : IsCompactlyGeneratedGroup G) : IsCompactlyGeneratedGroup H := by
  obtain ⟨U, hU, hK, hgen⟩ := h
  refine ⟨e '' U, ?_, hK.image e.continuous, ?_⟩
  · have hmap := e.toHomeomorph.map_nhds_eq 1
    rw [show e.toHomeomorph 1 = 1 from map_one e] at hmap
    rw [← hmap]
    exact Filter.mem_map.mpr (mem_of_superset hU (subset_preimage_image e U))
  · have hmap := MonoidHom.map_closure e.toMulEquiv.toMonoidHom U
    rw [hgen, Subgroup.map_top, MonoidHom.range_eq_top.mpr e.surjective] at hmap
    exact hmap.symm

/-- After transporting the structural pair and its coordinates, pullback is the
identity on the elementary Schwartz functions. -/
private theorem exists_schwartzBruhatStage_comp_equiv {G H : Type*}
    [CommGroup G] [CommGroup H] [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H] [T2Space G] [T2Space H]
    [LocallyCompactSpace G] [LocallyCompactSpace H]
    (e : G ≃ₜ* H) (a : BruhatStructuralPair H) (p : ElementaryLCAPresentation a.quotient) :
    ∃ (b : BruhatStructuralPair G) (q : ElementaryLCAPresentation b.quotient)
      (j : SchwartzBruhatStage p →L[ℂ] SchwartzBruhatStage q),
      ∀ f, schwartzBruhatStageRealization b q (j f) = schwartzBruhatStageRealization a p f ∘ e := by
  classical
  let J := a.val.1
  let K := OrderDual.ofDual a.val.2
  let J' := J.comap e.toMulEquiv.toMonoidHom
  let K' := K.comap e.toMulEquiv.toMonoidHom
  let eJ : J' ≃ₜ* J := ContinuousMulEquiv.mk'
    (e.toHomeomorph.subtype fun _ ↦ Iff.rfl)
    (fun x y ↦ Subtype.ext (map_mul e (x : G) (y : G)))
  -- Precomposition identifies the annihilators of the two kernels.
  let hom : G →ₜ* H := ⟨e.toMulEquiv.toMonoidHom, e.continuous⟩
  let inv : H →ₜ* G := ⟨e.symm.toMulEquiv.toMonoidHom, e.symm.continuous⟩
  let dual : PontryaginDual H ≃ₜ* PontryaginDual G :=
    { toFun := PontryaginDual.map hom
      invFun := PontryaginDual.map inv
      left_inv := fun χ ↦ PontryaginDual.ext fun y ↦ congrArg χ (e.apply_symm_apply y)
      right_inv := fun χ ↦ PontryaginDual.ext fun x ↦ congrArg χ (e.symm_apply_apply x)
      map_mul' := map_mul (PontryaginDual.map hom)
      continuous_toFun := (PontryaginDual.map hom).continuous
      continuous_invFun := (PontryaginDual.map inv).continuous }
  have hAnn (χ : PontryaginDual H) : χ ∈ lcaAnnihilator K ↔ dual χ ∈ lcaAnnihilator K' := by
    simp only [mem_lcaAnnihilator_iff]
    refine ⟨fun h x ↦ h ⟨e x, x.property⟩, fun h y ↦ ?_⟩
    have hy : e.symm y ∈ K' := by
      change e (e.symm y) ∈ K
      rw [e.apply_symm_apply]
      exact y.property
    have heval : χ (e (e.symm y)) = 1 := h ⟨e.symm y, hy⟩
    simpa using heval
  let eAnn : lcaAnnihilator K ≃ₜ* lcaAnnihilator K' := ContinuousMulEquiv.mk'
    (dual.toHomeomorph.subtype hAnn)
    (fun x y ↦ Subtype.ext (map_mul dual (x : PontryaginDual H) y))
  have hopen : IsOpen (lcaAnnihilator K' : Set (PontryaginDual G)) := by
    have heq : (lcaAnnihilator K' : Set (PontryaginDual G)) =
        dual.symm ⁻¹' (lcaAnnihilator K : Set (PontryaginDual H)) := by
      ext χ
      simpa using (hAnn (dual.symm χ)).symm
    rw [heq]
    exact a.property.2.2.1.2.1.preimage dual.symm.continuous
  let a' : BruhatStructuralPair G :=
    ⟨(J', OrderDual.toDual K'), a.property.1.preimage e.continuous,
      isCompactlyGeneratedGroup_of_equiv eJ.symm a.property.2.1,
      ⟨a.property.2.2.1.1.preimage e.continuous, hopen,
        isCompactlyGeneratedGroup_of_equiv eAnn a.property.2.2.1.2.2⟩,
      Subgroup.comap_mono a.property.2.2.2⟩
  -- The restricted isomorphism descends to the quotients, keeping the same coordinates.
  let N := K.comap J.subtype
  let N' := K'.comap J'.subtype
  have hN : N'.map eJ.toMulEquiv.toMonoidHom = N := by
    change N'.map (eJ.toMulEquiv : J' →* J) = N
    rw [Subgroup.map_equiv_eq_comap_symm eJ.toMulEquiv]
    ext y
    change e (e.symm y) ∈ K ↔ (y : H) ∈ K
    rw [e.apply_symm_apply]
  let q := QuotientGroup.congr N' N eJ.toMulEquiv hN
  let eQ : a'.quotient ≃ₜ* a.quotient :=
    ⟨q, (QuotientGroup.isQuotientMap_mk N').continuous_iff.mpr
      (QuotientGroup.continuous_mk.comp eJ.continuous),
      (QuotientGroup.isQuotientMap_mk N).continuous_iff.mpr
        (QuotientGroup.continuous_mk.comp eJ.symm.continuous)⟩
  let p' : ElementaryLCAPresentation a'.quotient :=
    { p with equiv := eQ.trans p.equiv }
  exact ⟨a', p', ContinuousLinearMap.id ℂ _, fun _ ↦ rfl⟩

/-- Pulling back a structural pair along a topological group isomorphism preserves its
elementary quotient and carries its realized Schwartz functions to the pulled-back stage. -/
private theorem schwartzBruhat_stage_comp_equiv {G H : Type*}
    [CommGroup G] [CommGroup H] [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H] [T2Space G] [T2Space H]
    [LocallyCompactSpace G] [LocallyCompactSpace H]
    (e : G ≃ₜ* H) (a : BruhatStructuralPair H) (p : ElementaryLCAPresentation a.quotient)
    (f : SchwartzBruhatStage p) :
    schwartzBruhatStageRealization a p f ∘ e ∈ schwartzBruhatSubmodule G := by
  obtain ⟨b, q, j, hj⟩ := exists_schwartzBruhatStage_comp_equiv e a p
  rw [← hj f]
  exact (schwartzBruhatStageInclusion b q (j f)).property

/-- Pullback along a topological group isomorphism preserves Schwartz–Bruhat membership. -/
private theorem schwartzBruhat_mem_comp_equiv {G H : Type*}
    [CommGroup G] [CommGroup H] [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H] [T2Space G] [T2Space H]
    [LocallyCompactSpace G] [LocallyCompactSpace H]
    (e : G ≃ₜ* H) {g : H → ℂ} (hg : g ∈ schwartzBruhatSubmodule H) :
    g ∘ e ∈ schwartzBruhatSubmodule G := by
  let pullback : (H → ℂ) →ₗ[ℂ] (G → ℂ) := LinearMap.funLeft ℂ ℂ e
  have hle : schwartzBruhatSubmodule H ≤ (schwartzBruhatSubmodule G).comap pullback := by
    unfold schwartzBruhatSubmodule
    refine iSup_le fun a ↦ iSup_le fun p ↦ ?_
    rintro _ ⟨f, rfl⟩
    exact schwartzBruhat_stage_comp_equiv e a p f
  exact hle hg

/-- Composition with a topological group isomorphism preserves the Schwartz–Bruhat
submodule. -/
theorem schwartzBruhatSubmodule_comp_continuousMulEquiv {G H : Type*}
    [CommGroup G] [CommGroup H] [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H] [T2Space G] [T2Space H]
    [LocallyCompactSpace G] [LocallyCompactSpace H]
    (e : G ≃ₜ* H) {g : H → ℂ} (hg : g ∈ schwartzBruhatSubmodule H) :
    g ∘ e ∈ schwartzBruhatSubmodule G :=
  schwartzBruhat_mem_comp_equiv e hg

/-- Pullback by a topological group isomorphism is continuous because its restriction
to every elementary stage factors continuously through a stage. -/
private theorem exists_schwartzBruhat_comp_equivCLM {G H : Type*}
    [CommGroup G] [CommGroup H] [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H] [T2Space G] [T2Space H]
    [LocallyCompactSpace G] [LocallyCompactSpace H] (e : G ≃ₜ* H) :
    ∃ T : SchwartzBruhat H →L[ℂ] SchwartzBruhat G, ∀ f x, T f x = f (e x) := by
  let L := (LinearMap.funLeft ℂ ℂ e).comp (schwartzBruhatSubmodule H).subtype
  let T : SchwartzBruhat H →ₗ[ℂ] SchwartzBruhat G :=
    L.codRestrict _ fun f ↦ schwartzBruhat_mem_comp_equiv e f.property
  refine ⟨⟨T, ?_⟩, fun _ _ ↦ rfl⟩
  refine (withGeneratingSeminorms_spec _ Subtype.val).continuous_of_continuous_comp T ?_
  rintro ⟨s, hs⟩
  refine (withGeneratingSeminorms_spec _ Subtype.val).continuous_seminorm ⟨s.comp T, ?_⟩
  intro a p
  obtain ⟨b, q, j, hj⟩ := exists_schwartzBruhatStage_comp_equiv e a p
  exact ((hs b q).comp j.continuous).congr fun f ↦ congrArg s (Subtype.ext (hj f))

open scoped RestrictedProduct in
/-- The adelic Fourier integral is the continuous linear Fourier transform on the
Pontryagin dual followed by pullback along the standard self-duality. -/
private theorem exists_adeleSchwartzFourierCLM :
    ∃ T : ℬ[F] →L[ℂ] ℬ[F], ∀ f y, T f y = tamagawaFourier (additiveTamagawaMeasure F)
      (adeleStandardCharacter F) (fun x ↦ f (Multiplicative.ofAdd x)) y.toAdd := by
  let G := Multiplicative 𝔸[F]
  let μ : Measure G := additiveTamagawaMeasure F
  let (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
      LocallyCompactSpace (v.adicCompletion F) := locallyCompactSpace_adicCompletion v
  let (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
      CompactSpace (v.adicCompletionIntegers F) := compactSpace_adicCompletionIntegers v
  let : Fact (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    ⟨fun _ ↦ Valued.isOpen_valuationSubring _⟩
  let : LocallyCompactSpace G := by
    change LocallyCompactSpace (InfiniteAdeleRing F ×
      (Πʳ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
        [v.adicCompletion F, v.adicCompletionIntegers F]))
    infer_instance
  let : T2Space G := by
    change T2Space (((v : InfinitePlace F) → v.Completion) ×
      (Πʳ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
        [v.adicCompletion F, v.adicCompletionIntegers F]))
    infer_instance
  let : BorelSpace G := ⟨rfl⟩
  have hμ := (additiveTamagawaMeasure_existsUnique F).exists.choose_spec
  let : μ.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := hμ.1.toIsFiniteMeasureOnCompacts
      toIsOpenPosMeasure := hμ.1.toIsOpenPosMeasure
      map_mul_left_eq_self := fun x ↦ hμ.1.map_add_left_eq_self x.toAdd }
  let : μ.Regular := hμ.2.1
  refine (additiveTamagawaMeasure_selfDual F).elim fun e he ↦ ?_
  refine (schwartzBruhat_fourier_equiv μ).elim fun Fourier hFourier ↦ ?_
  refine (exists_schwartzBruhat_comp_equivCLM e).elim fun P hP ↦ ?_
  refine ⟨P.comp Fourier.toContinuousLinearMap, fun f y ↦ ?_⟩
  calc
    P (Fourier f) y = Fourier f (e y) := hP _ _
    _ = lcaFourier μ f (e y) := (hFourier f).2 _
    _ = _ := (tamagawaFourier_eq_lcaFourier _ _ _ _ (e y) (fun x ↦ by
      rw [mul_comm x y.toAdd]
      exact he.1 y.toAdd x)).symm

/-- Paper: Lemma D.1.6.19(2), p. 773. The Fourier integral for the standard adelic
character and the additive Tamagawa measure gives a Schwartz–Bruhat function. This Fourier
stability is used in Theorem 2.2.3.2, p. 82. -/
theorem adeleSchwartzFourier_mem (f : ℬ[F]) :
    (fun y : Multiplicative 𝔸[F] ↦ tamagawaFourier (additiveTamagawaMeasure F)
      (adeleStandardCharacter F) (fun x ↦ f (Multiplicative.ofAdd x)) y.toAdd) ∈
      schwartzBruhatSubmodule (Multiplicative 𝔸[F]) := by
  refine (exists_adeleSchwartzFourierCLM (F := F)).elim fun T hT ↦ ?_
  exact Set.mem_of_eq_of_mem (funext (hT f)).symm (T f).property

/-- Paper: Theorem 2.2.3.2, p. 82. The Fourier transform in the theta identity
uses the trace character and the covolume-one measure of Appendix A. -/
def adeleSchwartzFourier (f : ℬ[F]) : ℬ[F] :=
  ⟨fun y ↦ tamagawaFourier (additiveTamagawaMeasure F) (adeleStandardCharacter F)
    (fun x ↦ f (Multiplicative.ofAdd x)) y.toAdd, adeleSchwartzFourier_mem f⟩

set_option maxSynthPendingDepth 8 in
/-- The product measurable structure on an elementary group agrees with its Borel
structure. -/
private theorem elementaryLieGroup_borelSpace {m n r : ℕ} {Fk : Type*}
    [TopologicalSpace Fk] [MeasurableSpace Fk] [BorelSpace Fk] :
    BorelSpace (ElementaryLieGroup m n r Fk) := by
  let : BorelSpace ((Fin r → ℤ) × Fk) := inferInstance
  let : BorelSpace ((Fin n → AddCircle (1 : ℝ)) × (Fin r → ℤ) × Fk) := inferInstance
  exact inferInstanceAs (BorelSpace (EuclideanSpace ℝ (Fin m) ×
    (Fin n → AddCircle (1 : ℝ)) × (Fin r → ℤ) × Fk))

set_option maxSynthPendingDepth 8 in
/-- Rapid decay in the real and lattice directions makes an elementary Schwartz function
integrable for any Haar measure on its elementary group. -/
private theorem elementarySchwartz_integrable {m n r : ℕ} {Fk : Type*} [AddCommGroup Fk]
    [TopologicalSpace Fk] [DiscreteTopology Fk] [Finite Fk] [MeasurableSpace Fk] [BorelSpace Fk]
    (f : ElementarySchwartz m n r Fk) (μ : Measure (ElementaryLieGroup m n r Fk))
    [μ.IsAddHaarMeasure] : Integrable f μ := by
  let : (Measure.count : Measure ℤ).IsAddHaarMeasure :=
    { lt_top_of_isCompact := fun _ hs ↦ Measure.count_apply_lt_top.mpr hs.finite_of_discrete
      open_pos := fun _ _ hs ↦ Measure.count_ne_zero hs }
  let : (Measure.count : Measure Fk).IsAddHaarMeasure :=
    { lt_top_of_isCompact := fun _ hs ↦ Measure.count_apply_lt_top.mpr hs.finite_of_discrete
      open_pos := fun _ _ hs ↦ Measure.count_ne_zero hs }
  let : MeasurableAdd ((Fin r → ℤ) × Fk) := inferInstance
  let : BorelSpace ((Fin r → ℤ) × Fk) := inferInstance
  let : BorelSpace ((Fin n → AddCircle (1 : ℝ)) × (Fin r → ℤ) × Fk) := inferInstance
  let : MeasurableAdd ((Fin n → AddCircle (1 : ℝ)) × (Fin r → ℤ) × Fk) :=
    ContinuousAdd.measurableAdd
  let νL : Measure ((Fin r → ℤ) × Fk) :=
    (Measure.pi fun _ : Fin r ↦ (Measure.count : Measure ℤ)).prod Measure.count
  let : νL.IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  let : SFinite νL := by dsimp [νL]; infer_instance
  let νT : Measure ((Fin n → AddCircle (1 : ℝ)) × (Fin r → ℤ) × Fk) := volume.prod νL
  let : νT.IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  let : SFinite νT := by dsimp [νT, νL]; infer_instance
  let ν : Measure (ElementaryLieGroup m n r Fk) := volume.prod νT
  let : BorelSpace (ElementaryLieGroup m n r Fk) := elementaryLieGroup_borelSpace
  let : ν.IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  rw [Measure.isAddLeftInvariant_eq_smul μ ν]
  apply Integrable.smul_measure_nnreal
  let A (x : EuclideanSpace ℝ (Fin m)) := (1 + ‖x‖) ^ (m + 1)
  let B (k : ℤ) := (1 + |(k : ℝ)|) ^ 2
  have hA : Integrable (fun x ↦ (A x)⁻¹) volume := by
    have hdim : (Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) : ℝ) < ((m + 1 : ℕ) : ℝ) := by
      simp
    convert integrable_one_add_norm (μ := volume) hdim using 1
    funext x
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
  have hB : Integrable (fun k ↦ (B k)⁻¹) Measure.count := by
    have hb (k : ℤ) : 0 ≤ (B k)⁻¹ := by dsimp [B]; positivity
    simp only [integrable_count_iff, Real.norm_eq_abs, abs_of_nonneg (hb _),
      summable_int_iff_summable_nat_and_neg, B, Int.cast_neg, Int.cast_natCast, abs_neg]
    have hn (j : ℕ) : |(j : ℝ)| = j := abs_of_nonneg (Nat.cast_nonneg j)
    simp only [hn]
    have hs : Summable (fun j : ℕ ↦ ((1 + (j : ℝ)) ^ 2)⁻¹) := by
      convert (Real.summable_one_div_nat_add_rpow 1 2).2 (by norm_num) using 1
      funext j
      rw [abs_of_nonneg (by positivity), add_comm (j : ℝ), one_div, ← Real.rpow_natCast]
      norm_num
    exact ⟨hs, hs⟩
  let D (w : ElementaryLieGroup m n r Fk) := A w.1 * ∏ k, B (w.2.2.1 k)
  obtain ⟨C, hC⟩ := elementarySchwartz_decay
    (show (f : ElementaryLieGroup m n r Fk → ℂ) ∈ elementarySchwartzSubmodule m n r Fk from
      (show elementarySchwartzSubmodule m n r Fk from f).property) (m + 1 + 2 * r)
  have hdom : Integrable (fun w ↦ C * (D w)⁻¹) ν := by
    have hπ := Integrable.fintype_prod (ι := Fin r) (fun _ ↦ hB)
    have hf : Integrable (fun _ : Fk ↦ (1 : ℝ)) (Measure.count : Measure Fk) := integrable_const _
    have ht : Integrable (fun _ : Fin n → AddCircle (1 : ℝ) ↦ (1 : ℝ)) volume :=
      integrable_const _
    convert (hA.mul_prod (ht.mul_prod (hπ.mul_prod hf))).const_mul C using 1
    funext w
    simp only [D, mul_inv_rev, one_mul, mul_one, Finset.prod_inv_distrib]
    ring
  refine hdom.mono' (continuous_elementarySchwartz f).aestronglyMeasurable
    (Eventually.of_forall fun w ↦ ?_)
  have hD : 0 < D w := by dsimp [D, A, B]; positivity
  let t := 1 + (∑ j, |w.1 j| + ∑ k, |(w.2.2.1 k : ℝ)|)
  have hreal : 1 + ‖w.1‖ ≤ t := by
    have := euclideanSpace_norm_le_sum_abs w.1
    dsimp [t]
    linarith [Finset.sum_nonneg (s := Finset.univ) fun k _ ↦ abs_nonneg (w.2.2.1 k : ℝ)]
  have hint (k : Fin r) : 1 + |(w.2.2.1 k : ℝ)| ≤ t := by
    have hk := Finset.single_le_sum
      (f := fun k ↦ |(w.2.2.1 k : ℝ)|) (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ k)
    dsimp [t]
    linarith [Finset.sum_nonneg (s := Finset.univ) fun j _ ↦ abs_nonneg (w.1 j)]
  have hDt : D w ≤ t ^ (m + 1 + 2 * r) := by
    calc
      D w ≤ t ^ (m + 1) * ∏ _ : Fin r, t ^ 2 := by
        unfold D A B
        exact mul_le_mul
          (pow_le_pow_left₀ (by positivity) hreal _)
          (Finset.prod_le_prod₀ (fun _ _ ↦ by positivity) fun k _ ↦
            pow_le_pow_left₀ (by positivity) (hint k) _)
          (by positivity)
          (pow_nonneg (le_trans (by positivity) hreal) _)
      _ = _ := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, ← pow_add]
  rw [← div_eq_mul_inv]
  exact (le_div_iff₀ hD).2 ((mul_le_mul_of_nonneg_left hDt (norm_nonneg (f w))).trans (hC w))

set_option maxSynthPendingDepth 8 in
open scoped Pointwise in
/-- A Schwartz–Bruhat stage is integrable after pullback along the quotient by its compact
kernel and extension by zero from its open subgroup. -/
private theorem schwartzBruhatStage_integrable {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (a : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation a.quotient) (f : SchwartzBruhatStage e) :
    Integrable (schwartzBruhatStageRealization a e f) μ := by
  let H := a.val.1
  let K := OrderDual.ofDual a.val.2
  let L := K.comap H.subtype
  have hH : IsOpen (H : Set G) := a.property.1
  have hK : IsCompact (L : Set H) := by
    let J := lcaAnnihilator K
    have hEval := (isClosedEmbedding_pontryaginDual_eval (G := G)).comp
      (H.isClosed_of_isOpen hH).isClosedEmbedding_subtypeVal
    have hpre : (L : Set H) = (pontryaginDual_eval ∘ (Subtype.val : H → G)) ⁻¹'
        (lcaAnnihilator J : Set (PontryaginDual (PontryaginDual G))) := by
      ext x
      change x.val ∈ K ↔ pontryaginDual_eval x.val ∈ lcaAnnihilator J
      rw [← lcaDualAnnihilator_annihilator K a.property.2.2.1.1]
      exact (mem_lcaDualAnnihilator_iff J x.val).trans
        (mem_lcaAnnihilator_iff J (pontryaginDual_eval x.val)).symm
    rw [hpre]
    exact hEval.isCompact_preimage (isCompact_lcaAnnihilator J a.property.2.2.1.2.1)
  let q := QuotientGroup.mk' L
  have hq : IsProperMap q := by
    refine isProperMap_iff_isClosedMap_and_compact_fibers.mpr
      ⟨QuotientGroup.continuous_mk, QuotientGroup.isClosedMap_coe hK, ?_⟩
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective L y
    change IsCompact (QuotientGroup.mk ⁻¹' {QuotientGroup.mk x})
    rw [← image_singleton, QuotientGroup.preimage_image_mk_eq_mul]
    exact isCompact_singleton.mul hK
  let E := ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor
  let : MeasurableSpace e.finiteFactor := borel _
  let : BorelSpace e.finiteFactor := ⟨rfl⟩
  let : BorelSpace E := elementaryLieGroup_borelSpace
  let : T2Space (Multiplicative E) := inferInstanceAs (T2Space (EuclideanSpace ℝ (Fin e.realDim) ×
    (Fin e.torusDim → AddCircle (1 : ℝ)) × (Fin e.latticeRank → ℤ) × e.finiteFactor))
  let p : H →* Multiplicative E := e.equiv.toMonoidHom.comp q
  have hp : IsProperMap p := e.equiv.toHomeomorph.isProperMap.comp hq
  let ν := μ.comap H.subtype
  let : ν.IsHaarMeasure :=
    Measure.IsHaarMeasure.comap (mH := ContinuousMul.measurableMul) μ (f := H.subtype)
      hH.isOpenEmbedding_subtypeVal
  let ρ := ν.map p
  have hρ : ρ.IsHaarMeasure := Measure.isHaarMeasure_map ν p hp.continuous
    (e.equiv.surjective.comp (QuotientGroup.mk'_surjective L))
    (isProperMap_iff_tendsto_cocompact.mp hp).2
  let ρ' : Measure E := ρ
  let : ρ'.IsAddHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := hρ.toIsFiniteMeasureOnCompacts
      toIsOpenPosMeasure := hρ.toIsOpenPosMeasure
      map_add_left_eq_self := fun x ↦ hρ.map_mul_left_eq_self (Multiplicative.ofAdd x) }
  have hf : Integrable f ρ' := elementarySchwartz_integrable f ρ'
  have hcomp : Integrable (fun x : H ↦ f (Multiplicative.toAdd (p x))) ν :=
    hf.comp_measurable hp.continuous.measurable
  apply IntegrableOn.integrable_of_forall_notMem_eq_zero (s := (H : Set G))
  · rw [integrableOn_iff_comap_subtypeVal hH.measurableSet]
    refine hcomp.congr (Eventually.of_forall fun x ↦ ?_)
    exact ((schwartzBruhatStageRealization_apply a e f x.val).trans
      (dite_eq_left x.property)).symm
  · intro x hx
    exact (schwartzBruhatStageRealization_apply a e f x).trans (dite_eq_right hx)

/-- Integrability is stable under the finite sums which generate the Schwartz–Bruhat submodule. -/
private theorem schwartzBruhat_integrable {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (f : SchwartzBruhat G) : Integrable f μ := by
  let fs : schwartzBruhatSubmodule G := f
  change Integrable fs.val μ
  refine Submodule.iSup_induction (motive := fun g : G → ℂ ↦ Integrable g μ) _
    fs.property (fun a g hg ↦ ?_) (integrable_zero _ _ _) (fun _ _ hg hh ↦ hg.add hh)
  exact Submodule.iSup_induction (motive := fun g : G → ℂ ↦ Integrable g μ) _ hg
    (fun e g ⟨s, hs⟩ ↦ hs ▸ schwartzBruhatStage_integrable μ a e s)
    (integrable_zero _ _ _) (fun _ _ hg hh ↦ hg.add hh)

open scoped IsDedekindDomain.FiniteAdeleRing RestrictedProduct in
/-- Paper: (D.1.1.4), p. 746. At zero the standard adelic character in the Fourier
integrand is trivial. The Schwartz–Bruhat function is integrable, and its Fourier transform
at zero equals its integral, as used in Theorem 2.2.3.2, p. 82. -/
theorem adeleSchwartzFourier_apply_zero (f : ℬ[F]) :
    Integrable (fun x ↦ f (Multiplicative.ofAdd x)) (additiveTamagawaMeasure F) ∧
    adeleSchwartzFourier f zeroAdele =
      ∫ x, f (Multiplicative.ofAdd x) ∂additiveTamagawaMeasure F := by
  refine ⟨?_, ?_⟩
  · let (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
        CompactSpace (v.adicCompletionIntegers F) := compactSpace_adicCompletionIntegers v
    let (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
        LocallyCompactSpace (v.adicCompletion F) := locallyCompactSpace_adicCompletion v
    let : Fact (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
        IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
      ⟨fun _ ↦ Valued.isOpen_valuationSubring _⟩
    let : LocallyCompactSpace (Multiplicative 𝔸[F]) := by
      change LocallyCompactSpace (InfiniteAdeleRing F ×
        (Πʳ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
          [v.adicCompletion F, v.adicCompletionIntegers F]))
      infer_instance
    let : T2Space (Multiplicative 𝔸[F]) := by
      change T2Space (((v : InfinitePlace F) → v.Completion) ×
        (Πʳ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
          [v.adicCompletion F, v.adicCompletionIntegers F]))
      infer_instance
    let : BorelSpace (Multiplicative 𝔸[F]) := ⟨rfl⟩
    let μ : Measure (Multiplicative 𝔸[F]) := additiveTamagawaMeasure F
    have hμ := (Classical.choose_spec (additiveTamagawaMeasure_existsUnique F).exists).1
    let : μ.IsHaarMeasure :=
      { toIsFiniteMeasureOnCompacts := hμ.toIsFiniteMeasureOnCompacts
        toIsOpenPosMeasure := hμ.toIsOpenPosMeasure
        map_mul_left_eq_self := fun x ↦ hμ.map_add_left_eq_self x.toAdd }
    exact schwartzBruhat_integrable μ f
  · change tamagawaFourier (additiveTamagawaMeasure F) (adeleStandardCharacter F)
      (fun x ↦ f (Multiplicative.ofAdd x)) 0 = _
    simp [tamagawaFourier, adeleStandardCharacter_zero]

section RiemannRoch

open scoped ENNReal RestrictedProduct

local notation "A[" F "]" => AddSubgroup.toSubgroup (AdeleRing.principalSubgroup (𝓞 F) F)

local instance : T2Space (Multiplicative 𝔸[F]) := by
  change T2Space (((v : InfinitePlace F) → v.Completion) ×
    (Πʳ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      [v.adicCompletion F, v.adicCompletionIntegers F]))
  infer_instance

local instance : LocallyCompactSpace (Multiplicative 𝔸[F]) := by
  let (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
      CompactSpace (v.adicCompletionIntegers F) := compactSpace_adicCompletionIntegers v
  let (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
      LocallyCompactSpace (v.adicCompletion F) := locallyCompactSpace_adicCompletion v
  let : Fact (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    ⟨fun _ ↦ Valued.isOpen_valuationSubring _⟩
  change LocallyCompactSpace (InfiniteAdeleRing F ×
    (Πʳ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      [v.adicCompletion F, v.adicCompletionIntegers F]))
  infer_instance

/-- The inverse image of the diagonal's annihilator under the adelic trace pairing
is the diagonal itself. -/
private theorem adelePrincipal_annihilator
    (e : Multiplicative 𝔸[F] ≃ₜ* PontryaginDual (Multiplicative 𝔸[F]))
    (he : ∀ x y : 𝔸[F], e (Multiplicative.ofAdd x) (Multiplicative.ofAdd y) =
      adeleStandardCharacter F (x * y)) :
    (lcaAnnihilator A[F]).comap e.toMonoidHom = A[F] := by
  let G := Multiplicative 𝔸[F]
  let H := A[F]
  let K := (lcaAnnihilator H).comap e.toMonoidHom
  let Q := G ⧸ H
  let q := QuotientGroup.mk' H
  obtain ⟨-, hH, -, -, -, hcompact, hhausdorff, hdiv, -, -⟩ := adele_additive_quotient.{_, 0} F
  let : CompactSpace Q := hcompact
  let : T2Space Q := hhausdorff
  have hHK : H ≤ K := by
    rintro _ ⟨a, rfl⟩
    apply (mem_lcaAnnihilator_iff H _).2
    rintro ⟨x, hx⟩
    obtain ⟨b, hb⟩ := hx
    replace hb : Multiplicative.ofAdd (algebraMap F 𝔸[F] b) = x := hb
    subst x
    change e (Multiplicative.ofAdd (algebraMap F 𝔸[F] a))
      (Multiplicative.ofAdd (algebraMap F 𝔸[F] b)) = 1
    rw [he, ← (algebraMap F 𝔸[F]).map_mul, adeleStandardCharacter_algebraMap]
  obtain ⟨d, -⟩ := lcaQuotientDual_equiv_annihilator H hH
  let : DiscreteTopology (lcaAnnihilator H) :=
    d.toHomeomorph.discreteTopology_iff.mp inferInstance
  let : DiscreteTopology K :=
    (e.toHomeomorph.subtype (p := fun x ↦ x ∈ K)
      (q := fun χ ↦ χ ∈ lcaAnnihilator H) (fun _ ↦ Iff.rfl)).discreteTopology_iff.mpr
      inferInstance
  -- Its image modulo the diagonal is closed and discrete in a compact group.
  let L := K.map q
  have hpre : (q : G → Q) ⁻¹' (L : Set Q) = K := by
    ext x
    refine ⟨?_, fun hx ↦ Subgroup.mem_map.mpr ⟨x, hx, rfl⟩⟩
    rintro ⟨y, hy, hyx⟩
    have h : y⁻¹ * x ∈ H := QuotientGroup.eq.mp hyx
    change x ∈ K
    simpa only [mul_inv_cancel_left] using K.mul_mem hy (hHK h)
  have hL : IsClosed (L : Set Q) := by
    apply (QuotientGroup.isQuotientMap_mk H).isCoinducing.isClosed_preimage.mp
    rw [show (QuotientGroup.mk : G → Q) = q from rfl, hpre]
    exact Subgroup.isClosed_of_discreteTopology
  have hU : IsOpen ({1} : Set K) := isOpen_discrete _
  obtain ⟨U, hUopen, hUeq⟩ := IsInducing.subtypeVal.isOpen_iff.mp hU
  let : DiscreteTopology L := by
    apply discreteTopology_of_isOpen_singleton_one
    refine IsInducing.subtypeVal.isOpen_iff.mpr
      ⟨(q : G → Q) '' U, QuotientGroup.isOpenMap_coe U hUopen, ?_⟩
    ext y
    constructor
    · rintro ⟨x, hx, hxy⟩
      have hxK : x ∈ K := by
        change x ∈ (K : Set G)
        rw [← hpre]
        change q x ∈ L
        exact hxy ▸ y.property
      have hx1 : (⟨x, hxK⟩ : K) ∈ ({1} : Set K) := by
        rw [← hUeq]
        exact hx
      have hx0 : x = 1 := congrArg Subtype.val (mem_singleton_iff.mp hx1)
      exact mem_singleton_iff.mpr (Subtype.ext (by simpa [hx0] using hxy.symm))
    · intro hy
      have h1 : (1 : G) ∈ U := by
        exact (Set.ext_iff.mp hUeq (1 : K)).mpr (mem_singleton 1)
      exact ⟨1, h1, by simp [mem_singleton_iff.mp hy]⟩
  -- This image is finite, and the additive quotient has no nontrivial torsion.
  let : CompactSpace L := isCompact_iff_compactSpace.mp hL.isCompact
  let : Finite L := finite_of_compact_of_discrete
  apply le_antisymm _ hHK
  intro x hx
  let y : L := ⟨q x, Subgroup.mem_map.mpr ⟨x, hx, rfl⟩⟩
  obtain ⟨n, hn, hyn⟩ := (isOfFinOrder_of_finite y).exists_pow_eq_one
  have hqn : q x ^ n = 1 := congrArg L.subtype hyn
  have hx1 : q x = 1 := (hdiv n hn).1 (hqn.trans (one_pow n).symm)
  exact (QuotientGroup.eq_one_iff x).mp hx1

/-- Probability Haar measure on a compact group corresponds to counting measure on its
countable dual. -/
private theorem compact_plancherel_count {Q : Type*} [CommGroup Q] [TopologicalSpace Q]
    [IsTopologicalGroup Q] [T2Space Q] [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]
    [Countable (PontryaginDual Q)] (μ : Measure Q) [μ.IsHaarMeasure]
    (hμ : μ univ = 1) :
    IsLCAPlancherelMeasure μ (@Measure.count (PontryaginDual Q) (borel _)) := by
  let : MeasurableSpace (PontryaginDual Q) := borel _
  let : BorelSpace (PontryaginDual Q) := ⟨rfl⟩
  let : IsProbabilityMeasure μ := ⟨hμ⟩
  obtain ⟨ν, hν, -⟩ := lcaPlancherelMeasure_existsUnique μ
  let : ν.IsHaarMeasure := hν.1
  have hFourier :
      lcaFourier μ (fun _ ↦ (1 : ℂ)) = ({1} : Set (PontryaginDual Q)).indicator (fun _ ↦ 1) := by
    ext χ
    by_cases hχ : χ = 1
    · subst χ
      simp [lcaFourier, PontryaginDual.one_apply, measureReal_def, hμ]
    · obtain ⟨a, ha⟩ : ∃ a : Q, χ a ≠ 1 := by
        by_contra! h
        exact hχ (PontryaginDual.ext (fun x ↦ (h x).trans (PontryaginDual.one_apply x).symm))
      let k : Q → ℂ := fun x ↦ star (χ x : ℂ)
      have htranslate : star (χ a : ℂ) * (∫ x, k x ∂μ) = ∫ x, k x ∂μ := by
        calc
          _ = ∫ x, star (χ a : ℂ) * k x ∂μ := (integral_const_mul _ _).symm
          _ = ∫ x, k (a * x) ∂μ := by
            simp only [k, map_mul, Circle.coe_mul, star_mul, mul_comm]
          _ = _ := integral_mul_left_eq_self k a
      have ha' : star (χ a : ℂ) ≠ 1 := by
        intro h
        apply ha
        apply Subtype.ext
        simpa using congrArg (star : ℂ → ℂ) h
      have hzero : (∫ x, k x ∂μ) = 0 :=
        (mul_eq_zero.mp (show (star (χ a : ℂ) - 1) * (∫ x, k x ∂μ) = 0 by
          rw [sub_mul, one_mul, htranslate, sub_self])).resolve_left (sub_ne_zero.mpr ha')
      simpa [lcaFourier, k, hχ] using hzero
  have hNorm := (hν.2.2 (fun _ ↦ (1 : ℂ)) (integrable_const _) (memLp_const _)).2
  rw [hFourier, eLpNorm_indicator_const (measurableSet_singleton _).nullMeasurableSet
    (by norm_num) (by simp), eLpNorm_const' _ (by norm_num) (by simp)] at hNorm
  have hr : 0 < (1 / (2 : ℝ≥0∞).toReal : ℝ) := by norm_num
  have hνone : ν {1} = 1 := by
    apply (ENNReal.strictMono_rpow_of_pos hr).injective
    simpa [hμ] using hNorm
  have hcount : ν = Measure.count := by
    apply Measure.ext_of_singleton
    intro χ
    rw [Measure.count_singleton, ← hνone, ← measure_preimage_mul ν χ {χ}]
    congr 1
    ext ψ
    simp
  exact hcount ▸ hν

/-- Paper: Theorem 2.2.3.2, p. 82. Fourier transformation changes adelic dilation
by an idele into inverse dilation and a factor equal to the reciprocal of its norm. -/
private theorem adeleSchwartzFourier_dilation (f : ℬ[F]) (g : 𝕀[F]) (y : 𝔸[F]) :
    tamagawaFourier (additiveTamagawaMeasure F) (adeleStandardCharacter F)
      (fun x ↦ f (Multiplicative.ofAdd (g.val * x))) y =
    (normℝ (classOf g))⁻¹ • adeleSchwartzFourier f (Multiplicative.ofAdd (g⁻¹.val * y)) := by
  let μ := additiveTamagawaMeasure F
  let : BorelSpace 𝔸[F] := ⟨rfl⟩
  let : μ.IsAddHaarMeasure := (additiveTamagawaMeasure_existsUnique F).exists.choose_spec.1
  let d := Homeomorph.smul (α := 𝔸[F]) g
  have hmap : μ.map d = (↑(ideleNorm F g⁻¹).val : ℝ≥0∞) • μ := by
    ext s hs
    rw [Measure.map_apply d.continuous.measurable hs]
    change μ ((fun x : 𝔸[F] ↦ g • x) ⁻¹' s) = (↑(ideleNorm F g⁻¹).val : ℝ≥0∞) * μ s
    rw [← inv_inv g, Set.preimage_smul_inv]
    exact adeleHaar_mul_image F μ g⁻¹ s hs
  let k (z : 𝔸[F]) := f (Multiplicative.ofAdd z) *
    star (adeleStandardCharacter F (z * (g⁻¹.val * y)) : ℂ)
  have hk (x : 𝔸[F]) : k (d x) = f (Multiplicative.ofAdd (g.val * x)) *
      star (adeleStandardCharacter F (x * y) : ℂ) := by
    have hg : g.val * g⁻¹.val = (1 : 𝔸[F]) := g.val_inv
    have hmul : (g.val * x) * (g⁻¹.val * y) = x * y := by
      rw [mul_mul_mul_comm, hg, one_mul]
    change f (Multiplicative.ofAdd (g.val * x)) *
      star (adeleStandardCharacter F ((g.val * x) * (g⁻¹.val * y)) : ℂ) = _
    rw [hmul]
  unfold tamagawaFourier
  simp_rw [← hk]
  change (∫ x, k (d.toMeasurableEquiv x) ∂μ) =
    (normℝ (classOf g))⁻¹ • (∫ z, k z ∂μ)
  rw [← integral_map_equiv, show (⇑d.toMeasurableEquiv : 𝔸[F] → 𝔸[F]) = d from rfl, hmap,
    integral_smul_measure]
  simp only [ENNReal.coe_toReal, map_inv, Units.val_inv_eq_inv_val, NNReal.coe_inv]
  rfl

open scoped IsDedekindDomain.FiniteAdeleRing in
set_option maxSynthPendingDepth 8 in
/-- Paper: Theorem 2.2.3.2, p. 82. Poisson summation over the diagonal field for the
covolume-one additive Tamagawa measure and the standard adelic character. -/
private theorem adeleSchwartz_poisson (f : ℬ[F]) :
    (∑' x : F, f (Multiplicative.ofAdd (algebraMap F 𝔸[F] x))) =
      ∑' x : F, adeleSchwartzFourier f (Multiplicative.ofAdd (algebraMap F 𝔸[F] x)) := by
  classical
  let G := Multiplicative 𝔸[F]
  let H := A[F]
  let Q := G ⧸ H
  let μ : Measure G := additiveTamagawaMeasure F
  let d : F → G := fun x ↦ Multiplicative.ofAdd (algebraMap F 𝔸[F] x)
  obtain ⟨hinj, hclosed, hdisc, -, -, hcompact, hhausdorff, -, -, -⟩ :=
    adele_additive_quotient.{_, 0} F
  let : CompactSpace Q := hcompact
  let : T2Space Q := hhausdorff
  let : DiscreteTopology H := isDiscrete_iff_discreteTopology.mp hdisc
  let : BorelSpace G := ⟨rfl⟩
  let : MeasurableSpace Q := borel _
  let : BorelSpace Q := ⟨rfl⟩
  let : MeasurableSpace (PontryaginDual Q) := borel _
  let : BorelSpace (PontryaginDual Q) := ⟨rfl⟩
  have hμ := (additiveTamagawaMeasure_existsUnique F).exists.choose_spec
  let : μ.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := hμ.1.toIsFiniteMeasureOnCompacts
      toIsOpenPosMeasure := hμ.1.toIsOpenPosMeasure
      map_mul_left_eq_self := fun x ↦ hμ.1.map_add_left_eq_self x.toAdd }
  let : μ.Regular := hμ.2.1
  let eH : F ≃ H := Equiv.ofBijective (fun x ↦ ⟨d x, ⟨x, rfl⟩⟩)
    ⟨fun _ _ h ↦ hinj (congrArg Subtype.val h),
      fun ⟨x, hx⟩ ↦ by obtain ⟨a, ha⟩ := hx; exact ⟨a, Subtype.ext ha⟩⟩
  let : Countable F := Countable.of_moduleFinite (R := ℚ)
  let : Countable H := Countable.of_equiv F eH
  let : (Measure.count : Measure H).IsHaarMeasure :=
    { lt_top_of_isCompact := fun _ hs ↦ Measure.count_apply_lt_top.mpr hs.finite_of_discrete
      open_pos := fun _ _ hs ↦ Measure.count_ne_zero hs }
  obtain ⟨e, he, -⟩ := additiveTamagawaMeasure_selfDual F
  have hAnn := adelePrincipal_annihilator e he
  obtain ⟨eQ, heQ⟩ := lcaQuotientDual_equiv_annihilator H hclosed
  let eA : H ≃ lcaAnnihilator H :=
    e.toEquiv.subtypeEquiv (p := fun x ↦ x ∈ H) (q := fun χ ↦ χ ∈ lcaAnnihilator H)
      (fun x ↦ by
        have hAnn' : (lcaAnnihilator H).comap e.toMonoidHom = H := hAnn
        exact (SetLike.ext_iff.mp hAnn' x).symm)
  let eDual : F ≃ PontryaginDual Q := (eH.trans eA).trans eQ.toEquiv.symm
  have hpull (x : F) :
      PontryaginDual.map (⟨QuotientGroup.mk' H, continuous_quotient_mk'⟩ : G →ₜ* Q)
        (eDual x) = e (d x) := by
    apply PontryaginDual.ext
    intro z
    change eDual x (QuotientGroup.mk z) = _
    rw [← heQ]
    change (eQ (eQ.symm (eA (eH x)))).val z = _
    rw [eQ.apply_symm_apply]
    rfl
  let : Countable (PontryaginDual Q) := Countable.of_equiv F eDual
  obtain ⟨ν, hν, hνmass⟩ := additiveTamagawaMeasure_quotientVolume F
  let : ν.IsHaarMeasure := hν.1
  have hνdual := compact_plancherel_count ν hνmass
  obtain ⟨-, hright, hPoisson⟩ := schwartzBruhat_poisson H μ Measure.count hclosed
    ν hν Measure.count hνdual f 1
  simp only [map_one, Circle.coe_one, mul_one] at hright hPoisson
  change schwartzBruhatCosetIntegral H Measure.count hclosed f (QuotientGroup.mk (1 : G)) =
    _ at hPoisson
  have hcoset := schwartzBruhatCosetIntegral_mk H Measure.count hclosed f (1 : G)
  have hsum := hcoset.symm.trans hPoisson
  rw [integral_countable hright,
    integral_countable ((lcaCosetIntegral_mem_schwartzBruhat H Measure.count hclosed f).1 1)]
    at hsum
  simp only [one_mul, count_real_singleton, one_smul] at hsum
  rw [← eH.tsum_eq, ← eDual.tsum_eq] at hsum
  refine hsum.trans (tsum_congr fun x ↦ ?_)
  rw [hpull x]
  symm
  change tamagawaFourier (additiveTamagawaMeasure F) (adeleStandardCharacter F)
    (fun z ↦ f (Multiplicative.ofAdd z)) (algebraMap F 𝔸[F] x) = lcaFourier μ f (e (d x))
  exact tamagawaFourier_eq_lcaFourier _ _ _ _ _
    (fun y ↦ by rw [he, mul_comm])

/-- Paper: Theorem 2.2.3.2, p. 82. Adelic Riemann–Roch relates theta at an idele
class to the Fourier-transformed theta at its inverse, including the two zero terms. -/
theorem adelicTheta_riemannRoch (f : ℬ[F]) (g : C[F]) :
    adelicTheta f g = (normℝ g)⁻¹ • adelicTheta (adeleSchwartzFourier f) g⁻¹ +
      (normℝ g)⁻¹ • adeleSchwartzFourier f zeroAdele - f zeroAdele := by
  induction g using QuotientGroup.induction_on with
  | _ g =>
    let G := Multiplicative 𝔸[F]
    let dil : G ≃ₜ* G :=
      { (Homeomorph.smul (α := 𝔸[F]) g) with
        map_mul' := fun x y ↦ mul_add g.val x.toAdd y.toAdd }
    let f' : ℬ[F] := ⟨(f : G → ℂ) ∘ dil,
      schwartzBruhat_mem_comp_equiv dil (show schwartzBruhatSubmodule G from f).property⟩
    have hFull (φ : ℬ[F]) (u : 𝕀[F]) :
        (∑' x : F, φ (Multiplicative.ofAdd (u.val * algebraMap F 𝔸[F] x))) =
          adelicTheta φ (classOf u) + φ zeroAdele := by
      simpa only [add_zero, mul_zero, zero_mul, adelicTheta_mk, adelicAverage, mul_comm u.val]
        using (hasSum_adelicAverage_add_zeroTerm φ u 0).tsum_eq
    have hPoisson := adeleSchwartz_poisson f'
    change (∑' x : F, f (Multiplicative.ofAdd (g.val * algebraMap F 𝔸[F] x))) =
      ∑' x : F, tamagawaFourier (additiveTamagawaMeasure F) (adeleStandardCharacter F)
        (fun z ↦ f (Multiplicative.ofAdd (g.val * z))) (algebraMap F 𝔸[F] x) at hPoisson
    simp_rw [adeleSchwartzFourier_dilation, tsum_const_smul'', hFull, smul_add] at hPoisson
    rw [← QuotientGroup.mk_inv]
    exact eq_sub_of_add_eq hPoisson

end RiemannRoch

/-- Every norm-one idele class has a representative in a single compact set of ideles. -/
private theorem exists_compact_idele_representatives :
    ∃ K : Set 𝕀[F], IsCompact K ∧ ∀ g ∈ (ideleClassNorm F).ker,
      ∃ k ∈ K, classOf k = g := by
  classical
  let : LocallyCompactSpace 𝕀[F] := (ideleGroup_topology F).2.1
  let : CompactSpace (ideleClassNorm F).ker := (ideleClassGroup_finiteness F).2.1
  have hCompact : IsCompact ((ideleClassNorm F).ker : Set C[F]) :=
    isCompact_iff_compactSpace.mpr inferInstance
  choose U hUc hU using fun k : 𝕀[F] => exists_compact_mem_nhds k
  let V (k : 𝕀[F]) := classOf '' interior (U k)
  have hVo (k : 𝕀[F]) : IsOpen (V k) :=
    QuotientGroup.isOpenMap_coe _ isOpen_interior
  have hCover : (↑(ideleClassNorm F).ker : Set C[F]) ⊆ ⋃ k, V k := by
    intro g _
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective g
    exact mem_iUnion.mpr ⟨k, mem_image_of_mem _ (mem_interior_iff_mem_nhds.mpr (hU k))⟩
  obtain ⟨s, hs⟩ := hCompact.elim_finite_subcover V hVo hCover
  refine ⟨⋃ k : s, U k, isCompact_iUnion (fun k => hUc k), fun g hg => ?_⟩
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hs hg)
  obtain ⟨hi', k, hk, rfl⟩ := mem_iUnion.mp hi
  exact ⟨k, mem_iUnion.mpr ⟨⟨i, hi'⟩, interior_subset hk⟩, rfl⟩

/-- The canonical norm section dilates the mixed archimedean space by the positive
root of order the field degree. -/
private theorem canonicalIdeleNormSection_smul_mixedSpace (t : ℝ≥0ˣ) (x : 𝔸[F]) :
    InfiniteAdeleRing.ringEquiv_mixedSpace F ((canonicalIdeleNormSection F t).val * x).1 =
      ((t.val : ℝ) ^ (Module.finrank ℚ F : ℝ)⁻¹) •
        InfiniteAdeleRing.ringEquiv_mixedSpace F x.1 := by
  let E := InfiniteAdeleRing.ringEquiv_mixedSpace F
  let r := (t.val : ℝ) ^ (Module.finrank ℚ F : ℝ)⁻¹
  have h : E (canonicalIdeleNormSection F t).val.1 =
      algebraMap ℝ (mixedEmbedding.mixedSpace F) r := by
    rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    apply Prod.ext
    · funext v
      apply Complex.ofReal_injective
      rw [InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]
      exact canonicalIdeleNormSection_infinite F t v.val
    · funext v
      exact canonicalIdeleNormSection_infinite F t v.val
  change E ((canonicalIdeleNormSection F t).val.1 * x.1) = r • E x.1
  rw [map_mul, h, Algebra.smul_def]

set_option maxHeartbeats 1800000 in
open scoped Classical in
open IsDedekindDomain in
/-- After multiplication by the requested power of the idelic norm, the summands of
a Schwartz stage have one summable majorant along all norm-section rays from a compact set. -/
private theorem realization_normSection_summable_bound
    (a : BruhatStructuralPair (Multiplicative 𝔸[F]))
    (e : ElementaryLCAPresentation a.quotient) (s : SchwartzBruhatStage e)
    (K : Set 𝕀[F]) (hK : IsCompact K) (N : ℕ) :
    ∃ u : Fˣ → ℝ, Summable u ∧ ∀ (ξ : Fˣ) (t : ℝ≥0ˣ), 1 ≤ (t.val : ℝ) →
      ∀ k ∈ K, ‖schwartzBruhatStageRealization a e s
        (Multiplicative.ofAdd ((canonicalIdeleNormSection F t * k).val *
          algebraMap F 𝔸[F] (ξ : F)))‖ * (t.val : ℝ) ^ N ≤ u ξ := by
  let E := InfiniteAdeleRing.ringEquiv_mixedSpace F
  let d := Module.finrank ℚ F
  let L := mixedEmbedding.integerLattice F
  let M := d * N + Module.finrank ℤ L + 1
  have HC := realization_decay (F := F) a e s M
  obtain ⟨C, hC⟩ := HC
  obtain ⟨b₀, hb₀, h₀⟩ :=
    exists_mul_mem_adicCompletionIntegers_of_compactlyGenerated a.property.2.1
  obtain ⟨b₁, hb₁, h₁⟩ := exists_mul_mem_adicCompletionIntegers_of_isCompact
    (hK.image (continuous_snd.comp Units.continuous_coe_inv))
  obtain ⟨A₀, hA₀⟩ := hK.exists_bound_of_continuousOn
    ((continuous_ringEquiv_mixedSpace.comp (continuous_fst.comp
      Units.continuous_coe_inv)).continuousOn)
  let A := max A₀ 0
  have hA : 0 ≤ A := le_max_right _ _
  let b := b₀ * b₁
  let B := ‖mixedEmbedding F (algebraMap (𝓞 F) F b)‖
  have hb : algebraMap (𝓞 F) F b ≠ 0 := by
    simpa [b] using mul_ne_zero hb₀ hb₁
  let S : Set Fˣ := {ξ | algebraMap (𝓞 F) F b * (ξ : F) ∈ (algebraMap (𝓞 F) F).range}
  let z (ξ : Fˣ) := mixedEmbedding F (algebraMap (𝓞 F) F b * (ξ : F))
  let i (ξ : S) : L := ⟨z ξ.val, by
    obtain ⟨c, hc⟩ := ξ.property
    exact ⟨c, by simp [z, hc]⟩⟩
  have hi : Injective i := by
    intro ξ η h
    exact Subtype.ext (Units.ext (mul_left_cancel₀ hb
      (mixedEmbedding_injective F (congrArg Subtype.val h))))
  have hsum : Summable (S.indicator fun ξ => (‖z ξ‖ ^ M)⁻¹) := by
    rw [← summable_subtype_iff_indicator]
    have hs := (ZLattice.summable_norm_pow_inv L M (by dsimp [M]; omega)).comp_injective hi
    change Summable (fun ξ : S => ‖z ξ.val‖⁻¹ ^ M) at hs
    simpa only [inv_pow, Function.comp_def] using hs
  let D := (A * B) ^ M * max C 0
  have hAB : 0 ≤ A * B := mul_nonneg hA (norm_nonneg _)
  have hD : 0 ≤ D := mul_nonneg (pow_nonneg hAB _) (le_max_right _ _)
  refine ⟨_, hsum.mul_left D, fun ξ t ht k hk => ?_⟩
  let x : 𝔸[F] := k.val * algebraMap F 𝔸[F] (ξ : F)
  let y : 𝔸[F] := (canonicalIdeleNormSection F t).val * x
  let r := (t.val : ℝ) ^ (d : ℝ)⁻¹
  change ‖schwartzBruhatStageRealization a e s
    (Multiplicative.ofAdd ((canonicalIdeleNormSection F t).val * k.val *
      algebraMap F 𝔸[F] (ξ : F)))‖ * (t.val : ℝ) ^ N ≤ _
  rw [mul_assoc]
  change ‖schwartzBruhatStageRealization a e s (Multiplicative.ofAdd y)‖ * (t.val : ℝ) ^ N ≤ _
  by_cases hy : Multiplicative.ofAdd y ∈ a.val.1
  · have hf : y.2 = x.2 := by
      change (canonicalIdeleNormSection F t).val.2 * x.2 = x.2
      rw [canonicalIdeleNormSection_finite, one_mul]
    have hξ : ξ ∈ S := by
      change algebraMap (𝓞 F) F (b₀ * b₁) * (ξ : F) ∈ (algebraMap (𝓞 F) F).range
      simpa only [mul_one] using
        (mul_mem_integers_of_adele (b₂ := 1) k 0 (ξ : F)
          (by
            intro v
            have h := h₀ _ hy v
            change (algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) b₀ * y.2) v ∈
              v.adicCompletionIntegers F at h
            rw [hf] at h
            simpa only [add_zero] using h)
          (h₁ _ ⟨k, hk, rfl⟩) (fun v => by
            change algebraMap (𝓞 F) (v.adicCompletion F) 1 * 0 ∈ v.adicCompletionIntegers F
            rw [mul_zero]
            exact zero_mem _))
    have hz : 0 < ‖z ξ‖ := by
      dsimp [z]
      rw [norm_pos_iff, map_ne_zero_iff _ (mixedEmbedding_injective F)]
      exact mul_ne_zero hb ξ.ne_zero
    have hr : 1 ≤ r := Real.one_le_rpow ht (by positivity)
    have hr0 : 0 ≤ r := zero_le_one.trans hr
    have hp : r ^ (d * N) = (t.val : ℝ) ^ N := by
      have hd : (d : ℝ) ≠ 0 := by exact_mod_cast (Module.finrank_pos (R := ℚ) (M := F)).ne'
      dsimp [r]
      rw [← Real.rpow_mul_natCast t.val.coe_nonneg, ← Real.rpow_natCast,
        Nat.cast_mul, ← mul_assoc, inv_mul_cancel₀ hd, one_mul]
    have hyNorm : ‖E y.1‖ = r * ‖E x.1‖ := by
      change ‖E ((canonicalIdeleNormSection F t).val * x).1‖ = _
      rw [canonicalIdeleNormSection_smul_mixedSpace, norm_smul,
        Real.norm_of_nonneg hr0]
    have hξNorm : ‖mixedEmbedding F (ξ : F)‖ ≤ A * ‖E x.1‖ := by
      have h := norm_mixedEmbedding_le_of_adele k 0 (ξ : F)
      rw [add_zero] at h
      have h' : ‖mixedEmbedding F (ξ : F)‖ ≤ ‖E (k⁻¹ : 𝕀[F]).val.1‖ * ‖E x.1‖ := by
        simpa only [E, x, Prod.fst_zero, map_zero, norm_zero, add_zero] using h
      exact h'.trans (mul_le_mul_of_nonneg_right ((hA₀ k hk).trans (le_max_left _ _))
        (norm_nonneg _))
    have hscale : r * ‖z ξ‖ ≤ (A * B) * (1 + ‖E y.1‖) := by
      have hzMul : ‖z ξ‖ ≤ B * ‖mixedEmbedding F (ξ : F)‖ := by
        dsimp [z, B]
        rw [map_mul]
        exact norm_mul_le _ _
      calc
        r * ‖z ξ‖ ≤ r * (B * (A * ‖E x.1‖)) :=
          mul_le_mul_of_nonneg_left
            (hzMul.trans (mul_le_mul_of_nonneg_left hξNorm (norm_nonneg _))) hr0
        _ = (A * B) * ‖E y.1‖ := by rw [hyNorm]; ac_rfl
        _ ≤ (A * B) * (1 + ‖E y.1‖) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) hAB
    let w := ‖schwartzBruhatStageRealization a e s (Multiplicative.ofAdd y)‖
    have hw : 0 ≤ w := norm_nonneg _
    have htPow : (t.val : ℝ) ^ N ≤ r ^ M :=
      hp ▸ pow_le_pow_right₀ hr (by dsimp [M]; omega)
    have hweighted : w * (t.val : ℝ) ^ N * ‖z ξ‖ ^ M ≤ D := calc
      _ ≤ w * r ^ M * ‖z ξ‖ ^ M :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htPow hw) (pow_nonneg hz.le _)
      _ = w * (r * ‖z ξ‖) ^ M := by rw [mul_pow, mul_assoc]
      _ ≤ w * ((A * B) * (1 + ‖E y.1‖)) ^ M :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg hr0 hz.le) hscale _) hw
      _ = (A * B) ^ M * (w * (1 + ‖E y.1‖) ^ M) := by rw [mul_pow]; ac_rfl
      _ ≤ D := mul_le_mul_of_nonneg_left ((hC _ hy).trans (le_max_left _ _)) (pow_nonneg hAB _)
    calc
      w * (t.val : ℝ) ^ N ≤ D / ‖z ξ‖ ^ M := (le_div_iff₀ (pow_pos hz _)).mpr hweighted
      _ = D * S.indicator (fun η => (‖z η‖ ^ M)⁻¹) ξ := by
        rw [indicator_of_mem hξ, div_eq_mul_inv]
  · rw [schwartzBruhatStageRealization_apply_dite, dite_eq_right hy, norm_zero, zero_mul]
    exact mul_nonneg hD (indicator_nonneg (fun _ _ => by positivity) _)

/-- Paper: Theorem 2.2.3.4(1), p. 83. Theta decays faster than any inverse
power of the idele class norm as that norm tends to infinity. -/
theorem adelicTheta_decay_large (f : ℬ[F]) (N : ℕ) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ g : C[F], T < normℝ g →
      ‖adelicTheta f g‖ ≤ C * ((normℝ g) ^ N)⁻¹ := by
  obtain ⟨K, hK, hRep⟩ := exists_compact_idele_representatives (F := F)
  let point (ξ : Fˣ) (t : ℝ≥0ˣ) (k : 𝕀[F]) :=
    Multiplicative.ofAdd ((canonicalIdeleNormSection F t * k).val * algebraMap F 𝔸[F] (ξ : F))
  let P (φ : Multiplicative 𝔸[F] → ℂ) := ∃ u : Fˣ → ℝ, Summable u ∧
    ∀ (ξ : Fˣ) (t : ℝ≥0ˣ), 1 ≤ (t.val : ℝ) → ∀ k ∈ K,
      ‖φ (point ξ t k)‖ * (t.val : ℝ) ^ N ≤ u ξ
  have hzero : P 0 := ⟨0, summable_zero, fun _ _ _ _ _ => by simp⟩
  have hadd (φ ψ : Multiplicative 𝔸[F] → ℂ) : P φ → P ψ → P (φ + ψ) := by
    rintro ⟨u, hu, hφ⟩ ⟨v, hv, hψ⟩
    refine ⟨u + v, hu.add hv, fun ξ t ht k hk => ?_⟩
    change ‖φ (point ξ t k) + ψ (point ξ t k)‖ * (t.val : ℝ) ^ N ≤ u ξ + v ξ
    calc
      _ ≤ (‖φ (point ξ t k)‖ + ‖ψ (point ξ t k)‖) * (t.val : ℝ) ^ N :=
        mul_le_mul_of_nonneg_right (norm_add_le _ _) (by positivity)
      _ ≤ _ := by rw [add_mul]; exact add_le_add (hφ ξ t ht k hk) (hψ ξ t ht k hk)
  have hP : P (show schwartzBruhatSubmodule (Multiplicative 𝔸[F]) from f).val := by
    refine Submodule.iSup_induction (motive := P) _ f.property ?_ hzero hadd
    intro a φ hφ
    refine Submodule.iSup_induction (motive := P) _ hφ ?_ hzero hadd
    intro e ψ hψ
    obtain ⟨s, rfl⟩ := LinearMap.mem_range.mp hψ
    exact realization_normSection_summable_bound a e s K hK N
  obtain ⟨u, hu, hbound⟩ := hP
  refine ⟨max (∑' ξ, u ξ) 1, 1, zero_lt_one.trans_le (le_max_right _ _), zero_lt_one, ?_⟩
  intro g hg
  let t := ideleClassNorm F g
  let a := canonicalIdeleNormSection F t
  let q := QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 F) F)
  have hn : ideleClassNorm F (q a) = t := canonicalIdeleNormSection_rightInverse F t
  have hker : (q a)⁻¹ * g ∈ (ideleClassNorm F).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hn]
    exact inv_mul_cancel t
  obtain ⟨k, hk, hq⟩ := hRep ((q a)⁻¹ * g) hker
  have hclass : q (a * k) = g := by
    rw [map_mul, show q k = (q a)⁻¹ * g from hq, mul_inv_cancel_left]
  have htheta : adelicTheta f g = ∑' ξ, f (point ξ t k) := by
    rw [← hclass]
    change adelicTheta f (classOf (a * k)) =
      ∑' ξ : Fˣ, f (Multiplicative.ofAdd ((a * k).val * algebraMap F 𝔸[F] (ξ : F)))
    rw [adelicTheta_mk]
    simp only [mul_comm (a * k).val]
  have hs : Summable (fun ξ => ‖f (point ξ t k)‖) := by
    simpa only [point, add_zero] using
      ((adelicAverage_summableUniformlyOn f {(a * k, 0)} isCompact_singleton).summable rfl)
  rw [htheta]
  apply (norm_tsum_le_tsum_norm hs).trans
  change (∑' ξ, ‖f (point ξ t k)‖) ≤ max (∑' ξ, u ξ) 1 * ((t.val : ℝ) ^ N)⁻¹
  have ht : 1 ≤ (t.val : ℝ) := hg.le
  rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos (zero_lt_one.trans_le ht) N)]
  rw [← tsum_mul_right]
  exact (Summable.tsum_le_tsum (fun ξ => hbound ξ t ht k hk)
    (hs.mul_right _) hu).trans (le_max_left _ _)

/-- A lattice sum of an inverse power of the scaled norm grows at most like the inverse
of the scale to the power of the rank, as the scale tends to zero. -/
private theorem zlattice_tsum_inv_one_add_mul_norm_pow_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L]
    (M : ℕ) (hM : Module.finrank ℤ L < M) :
    ∃ C : ℝ, 0 < C ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      Summable (fun x : L ↦ ((1 + ρ * ‖x‖) ^ M)⁻¹) ∧
      ∑' x : L, ((1 + ρ * ‖x‖) ^ M)⁻¹ ≤ C * (ρ ^ Module.finrank ℤ L)⁻¹ := by
  classical
  set d := Module.finrank ℤ L
  let b : Module.Basis (Fin d) ℤ L := Module.finBasis ℤ L
  let e := b.equivFun.symm
  have he (m : Fin d → ℤ) : e m = ∑ i, m i • b i := b.equivFun_symm_apply m
  let D : ℝ := ∑ i, ‖b i‖
  have hD : 0 ≤ D := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  let H (x : L) : ℝ := ((1 + ‖x‖) ^ M)⁻¹
  have hH (x : L) : 0 ≤ H x := by positivity
  have hHsum : Summable H := by
    refine Summable.of_norm_bounded_eventually (ZLattice.summable_norm_pow_inv L M hM) ?_
    filter_upwards [(Set.finite_singleton (0 : L)).compl_mem_cofinite] with x hx
    have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
    rw [Real.norm_of_nonneg (hH x), inv_pow]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hx0.le (by linarith) M)
  let S := ∑' x, H x
  have hS : 0 ≤ S := tsum_nonneg hH
  refine ⟨2 ^ d * (1 + D) ^ M * (S + 1), by positivity, fun ρ hρ hρ1 ↦ ?_⟩
  let n : ℕ := ⌈ρ⁻¹⌉₊
  have hρ' : 1 ≤ ρ⁻¹ := one_le_inv_iff₀.mpr ⟨hρ, hρ1⟩
  have hρn : 1 ≤ ρ * n := by
    rw [← div_le_iff₀' hρ, one_div]
    exact Nat.le_ceil _
  have hn : (n : ℝ) ≤ 2 * ρ⁻¹ := by
    have := Nat.ceil_lt_add_one (inv_nonneg.mpr hρ.le)
    linarith
  have hn0 : (0 : ℝ) < n := by
    have := Nat.le_ceil ρ⁻¹
    linarith
  have hnpos : (0 : ℤ) < n := by exact_mod_cast hn0
  let G (x : L) : ℝ := ((1 + ρ * ‖x‖) ^ M)⁻¹
  have hG (x : L) : 0 ≤ G x := by positivity
  let Q (m : Fin d → ℤ) : Fin d → ℤ := fun i ↦ m i / n
  let R (m : Fin d → ℤ) : Fin d → ℤ := fun i ↦ m i % n
  have hQR (m : Fin d → ℤ) : m = (n : ℤ) • Q m + R m := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Q, R]
    exact (Int.mul_ediv_add_emod (m i) n).symm
  have hR (m : Fin d → ℤ) (i : Fin d) : 0 ≤ R m i ∧ R m i < n :=
    ⟨Int.emod_nonneg _ hnpos.ne', Int.emod_lt_of_pos _ hnpos⟩
  -- Each term is bounded by the unscaled term at the quotient coordinate.
  have hpt (m : Fin d → ℤ) : G (e m) ≤ (1 + D) ^ M * H (e (Q m)) := by
    have hsplit : e m = (n : ℤ) • e (Q m) + e (R m) := by
      conv_lhs => rw [hQR m]
      rw [map_add, map_zsmul]
    have hRn : ‖e (R m)‖ ≤ n * D := by
      rw [he, Finset.mul_sum]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ (norm_zsmul_le _ _).trans ?_)
      rw [Int.norm_eq_abs]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      have := hR m i
      rw [abs_of_nonneg (by exact_mod_cast this.1)]
      exact_mod_cast this.2.le
    set X := ‖e (Q m)‖
    have hX : 0 ≤ X := norm_nonneg _
    have hlow : (n : ℝ) * X - n * D ≤ ‖e m‖ := by
      have h1 : ‖(n : ℤ) • e (Q m)‖ = n * X := by
        change ‖(n : ℤ) • ((e (Q m) : L) : E)‖ = _
        rw [← Int.cast_smul_eq_zsmul ℝ, norm_smul, Int.cast_natCast, Real.norm_of_nonneg hn0.le]
        rfl
      have h2 := norm_sub_le ((n : ℤ) • e (Q m) + e (R m)) (e (R m))
      rw [add_sub_cancel_right, h1] at h2
      rw [hsplit]
      linarith
    have hkey : 1 + X ≤ (1 + D) * (1 + ρ * ‖e m‖) := by
      have hm0 := norm_nonneg (e m)
      rcases le_total D X with hDX | hDX
      · have h3 : X - D ≤ ρ * ‖e m‖ := by
          have : ρ * (n * X - n * D) ≤ ρ * ‖e m‖ := mul_le_mul_of_nonneg_left hlow hρ.le
          nlinarith
        nlinarith
      · nlinarith [mul_nonneg hρ.le hm0]
    change ((1 + ρ * ‖e m‖) ^ M)⁻¹ ≤ (1 + D) ^ M * ((1 + X) ^ M)⁻¹
    have hpos : 0 < 1 + ρ * ‖e m‖ := by positivity
    calc ((1 + ρ * ‖e m‖) ^ M)⁻¹ = (1 + D) ^ M * (((1 + D) * (1 + ρ * ‖e m‖)) ^ M)⁻¹ := by
          rw [mul_pow, mul_inv, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
      _ ≤ (1 + D) ^ M * ((1 + X) ^ M)⁻¹ := by gcongr
  -- Each fibre of the quotient coordinate has at most `n ^ d` points.
  have hcard (s : Finset (Fin d → ℤ)) (q : Fin d → ℤ) :
      ((s.filter (fun m ↦ Q m = q)).card : ℝ) ≤ (n : ℝ) ^ d := by
    have h : (s.filter (fun m ↦ Q m = q)).card ≤
        (Fintype.piFinset fun _ : Fin d ↦ Finset.Ico (0 : ℤ) n).card := by
      refine Finset.card_le_card_of_injOn R (fun m _ ↦ ?_) (fun m hm m' hm' hRm ↦ ?_)
      · exact Fintype.mem_piFinset.mpr fun i ↦ Finset.mem_Ico.mpr (hR m i)
      · have hq : Q m = Q m' := (Finset.mem_filter.mp hm).2.trans (Finset.mem_filter.mp hm').2.symm
        rw [hQR m, hQR m', hq, hRm]
    rw [Fintype.card_piFinset, Finset.prod_const, Int.card_Ico, sub_zero, Int.toNat_natCast,
      Finset.card_univ, Fintype.card_fin] at h
    exact_mod_cast h
  have hfin (s : Finset (Fin d → ℤ)) : ∑ m ∈ s, G (e m) ≤ n ^ d * (1 + D) ^ M * S := by
    have hT (T : Finset (Fin d → ℤ)) : ∑ q ∈ T, H (e q) ≤ S := by
      have := (hHsum.comp_injective e.injective).sum_le_tsum T (fun _ _ ↦ hH _)
      exact this.trans_eq (e.toEquiv.tsum_eq H)
    calc ∑ m ∈ s, G (e m) = ∑ q ∈ s.image Q, ∑ m ∈ s with Q m = q, G (e m) :=
          (Finset.sum_fiberwise_of_maps_to (fun m hm ↦ Finset.mem_image_of_mem Q hm) _).symm
      _ ≤ ∑ q ∈ s.image Q, ∑ m ∈ s with Q m = q, (1 + D) ^ M * H (e q) := by
          refine Finset.sum_le_sum fun q _ ↦ Finset.sum_le_sum fun m hm ↦ ?_
          rw [← (Finset.mem_filter.mp hm).2]
          exact hpt m
      _ = ∑ q ∈ s.image Q, ((s.filter (fun m ↦ Q m = q)).card : ℝ) * ((1 + D) ^ M * H (e q)) := by
          simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ q ∈ s.image Q, (n : ℝ) ^ d * ((1 + D) ^ M * H (e q)) :=
          Finset.sum_le_sum fun q _ ↦ mul_le_mul_of_nonneg_right (hcard s q) (by positivity)
      _ = n ^ d * (1 + D) ^ M * ∑ q ∈ s.image Q, H (e q) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun q _ ↦ ?_
          ring
      _ ≤ n ^ d * (1 + D) ^ M * S := mul_le_mul_of_nonneg_left (hT _) (by positivity)
  have hsumG : Summable (G ∘ e) := summable_of_sum_le (fun _ ↦ hG _) hfin
  have htsumG : ∑' m, (G ∘ e) m ≤ n ^ d * (1 + D) ^ M * S := hsumG.tsum_le_of_sum_le hfin
  refine ⟨(e.toEquiv.summable_iff).mp hsumG, ?_⟩
  change ∑' x, G x ≤ _
  rw [← e.toEquiv.tsum_eq G]
  refine htsumG.trans ?_
  have hnd : (n : ℝ) ^ d ≤ 2 ^ d * (ρ ^ d)⁻¹ := by
    rw [← inv_pow, ← mul_pow]
    exact pow_le_pow_left₀ hn0.le hn d
  calc (n : ℝ) ^ d * (1 + D) ^ M * S ≤ 2 ^ d * (ρ ^ d)⁻¹ * (1 + D) ^ M * (S + 1) := by
        gcongr
        linarith
    _ = _ := by ring

set_option maxHeartbeats 4000000 in
open scoped Classical in
open IsDedekindDomain in
/-- Along the norm-section rays from a compact set, below norm one, the sampled
summands of a Schwartz stage have a sum of norms bounded by a constant times the
inverse norm. -/
private theorem realization_normSection_small_bound
    (a : BruhatStructuralPair (Multiplicative 𝔸[F]))
    (e : ElementaryLCAPresentation a.quotient) (s : SchwartzBruhatStage e)
    (K : Set 𝕀[F]) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ≥0ˣ, (t.val : ℝ) ≤ 1 → ∀ k ∈ K,
      Summable (fun ξ : Fˣ ↦ ‖schwartzBruhatStageRealization a e s
        (Multiplicative.ofAdd ((canonicalIdeleNormSection F t * k).val *
          algebraMap F 𝔸[F] (ξ : F)))‖) ∧
      ∑' ξ : Fˣ, ‖schwartzBruhatStageRealization a e s
        (Multiplicative.ofAdd ((canonicalIdeleNormSection F t * k).val *
          algebraMap F 𝔸[F] (ξ : F)))‖ ≤ C * (t.val : ℝ)⁻¹ := by
  let E := InfiniteAdeleRing.ringEquiv_mixedSpace F
  let d := Module.finrank ℚ F
  let L := mixedEmbedding.integerLattice F
  have hdL : Module.finrank ℤ L = d := by
    have := ZLattice.rank ℝ (E := mixedEmbedding.mixedSpace F) L
    rw [mixedEmbedding.finrank] at this
    exact this
  let M := d + 1
  have HL := zlattice_tsum_inv_one_add_mul_norm_pow_le L M (by omega)
  obtain ⟨CL, hCL, hlat⟩ := HL
  have HC := realization_decay (F := F) a e s M
  obtain ⟨C, hC⟩ := HC
  obtain ⟨b₀, hb₀, h₀⟩ :=
    exists_mul_mem_adicCompletionIntegers_of_compactlyGenerated a.property.2.1
  obtain ⟨b₁, hb₁, h₁⟩ := exists_mul_mem_adicCompletionIntegers_of_isCompact
    (hK.image (continuous_snd.comp Units.continuous_coe_inv))
  obtain ⟨A₀, hA₀⟩ := hK.exists_bound_of_continuousOn
    ((continuous_ringEquiv_mixedSpace.comp (continuous_fst.comp
      Units.continuous_coe_inv)).continuousOn)
  let A := max A₀ 1
  have hA : 1 ≤ A := le_max_right _ _
  let b := b₀ * b₁
  let B := max ‖mixedEmbedding F (algebraMap (𝓞 F) F b)‖ 1
  have hB : 1 ≤ B := le_max_right _ _
  have hb : algebraMap (𝓞 F) F b ≠ 0 := by
    simpa [b] using mul_ne_zero hb₀ hb₁
  let S : Set Fˣ := {ξ | algebraMap (𝓞 F) F b * (ξ : F) ∈ (algebraMap (𝓞 F) F).range}
  let z (ξ : Fˣ) := mixedEmbedding F (algebraMap (𝓞 F) F b * (ξ : F))
  let i (ξ : S) : L := ⟨z ξ.val, by
    obtain ⟨c, hc⟩ := ξ.property
    exact ⟨c, by simp [z, hc]⟩⟩
  have hi : Injective i := by
    intro ξ η h
    exact Subtype.ext (Units.ext (mul_left_cancel₀ hb
      (mixedEmbedding_injective F (congrArg Subtype.val h))))
  let C' := max C 1
  have hC' : 0 < C' := zero_lt_one.trans_le (le_max_right _ _)
  have hAB : 1 ≤ A * B := one_le_mul_of_one_le_of_one_le hA hB
  refine ⟨C' * (CL * (A * B) ^ d), mul_pos hC' (mul_pos hCL (pow_pos (by linarith) _)),
    fun t ht k hk => ?_⟩
  have ht0 : 0 < (t.val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt t)
  let r := (t.val : ℝ) ^ (d : ℝ)⁻¹
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast (Module.finrank_pos (R := ℚ) (M := F)).ne'
  have hr0 : 0 < r := Real.rpow_pos_of_pos ht0 _
  have hr1 : r ≤ 1 := Real.rpow_le_one ht0.le ht (inv_nonneg.mpr (Nat.cast_nonneg _))
  have hrd : r ^ d = (t.val : ℝ) := by
    dsimp [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le, inv_mul_cancel₀ hd, Real.rpow_one]
  let ρ := r / (A * B)
  have hAB0 : (0 : ℝ) < A * B := zero_lt_one.trans_le hAB
  have hρ0 : 0 < ρ := div_pos hr0 hAB0
  have hρ1 : ρ ≤ 1 := (div_le_one hAB0).mpr (hr1.trans hAB)
  have hL2 := hlat ρ hρ0 hρ1
  have hsumL := hL2.1
  have htsumL : ∑' x : L, ((1 + ρ * ‖x‖) ^ M)⁻¹ ≤ CL * (ρ ^ d)⁻¹ := hdL ▸ hL2.2
  have hnn (q : ℝ) (hq : 0 ≤ q) : 0 < 1 + ρ * q :=
    add_pos_of_pos_of_nonneg one_pos (mul_nonneg hρ0.le hq)
  let G (ξ : Fˣ) : ℝ := C' * ((1 + ρ * ‖z ξ‖) ^ M)⁻¹
  let u := S.indicator G
  have hu : Summable u := by
    rw [← summable_subtype_iff_indicator]
    have hs := (hsumL.comp_injective hi).mul_left C'
    exact hs
  have hu0 (ξ : Fˣ) : 0 ≤ u ξ := indicator_nonneg
    (fun η _ => mul_nonneg hC'.le (inv_nonneg.mpr (pow_pos (hnn _ (norm_nonneg _)) _).le)) _
  have htsum : ∑' ξ, u ξ ≤ C' * (CL * (ρ ^ d)⁻¹) := by
    calc ∑' ξ, u ξ = ∑' ξ : S, G ξ := (tsum_subtype S G).symm
      _ = C' * ∑' ξ : S, ((1 + ρ * ‖z ξ‖) ^ M)⁻¹ := tsum_mul_left
      _ ≤ C' * (CL * (ρ ^ d)⁻¹) := mul_le_mul_of_nonneg_left
          ((tsum_comp_le_tsum_of_inj hsumL
            (fun x => inv_nonneg.mpr (pow_pos (hnn _ (norm_nonneg _)) _).le) hi).trans htsumL)
          hC'.le
  have hpt (ξ : Fˣ) : ‖schwartzBruhatStageRealization a e s
      (Multiplicative.ofAdd ((canonicalIdeleNormSection F t * k).val *
        algebraMap F 𝔸[F] (ξ : F)))‖ ≤ u ξ := by
    let x : 𝔸[F] := k.val * algebraMap F 𝔸[F] (ξ : F)
    let y : 𝔸[F] := (canonicalIdeleNormSection F t).val * x
    have hyeq : (canonicalIdeleNormSection F t * k).val * algebraMap F 𝔸[F] (ξ : F) = y := by
      change (canonicalIdeleNormSection F t).val * k.val * algebraMap F 𝔸[F] (ξ : F) = _
      exact mul_assoc _ _ _
    calc ‖schwartzBruhatStageRealization a e s
          (Multiplicative.ofAdd ((canonicalIdeleNormSection F t * k).val *
            algebraMap F 𝔸[F] (ξ : F)))‖ =
          ‖schwartzBruhatStageRealization a e s (Multiplicative.ofAdd y)‖ :=
          congrArg (fun v ↦ ‖schwartzBruhatStageRealization a e s (Multiplicative.ofAdd v)‖) hyeq
      _ ≤ u ξ := ?_
    by_cases hy : Multiplicative.ofAdd y ∈ a.val.1
    · have hf : y.2 = x.2 := by
        change (canonicalIdeleNormSection F t).val.2 * x.2 = x.2
        rw [canonicalIdeleNormSection_finite, one_mul]
      have hξ : ξ ∈ S := by
        change algebraMap (𝓞 F) F (b₀ * b₁) * (ξ : F) ∈ (algebraMap (𝓞 F) F).range
        simpa only [mul_one] using
          (mul_mem_integers_of_adele (b₂ := 1) k 0 (ξ : F)
            (by
              intro v
              have h := h₀ _ hy v
              change (algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) b₀ * y.2) v ∈
                v.adicCompletionIntegers F at h
              rw [hf] at h
              simpa only [add_zero] using h)
            (h₁ _ ⟨k, hk, rfl⟩) (fun v => by
              change algebraMap (𝓞 F) (v.adicCompletion F) 1 * 0 ∈ v.adicCompletionIntegers F
              rw [mul_zero]
              exact zero_mem _))
      have hyNorm : ‖E y.1‖ = r * ‖E x.1‖ := by
        change ‖E ((canonicalIdeleNormSection F t).val * x).1‖ = _
        rw [canonicalIdeleNormSection_smul_mixedSpace, norm_smul,
          Real.norm_of_nonneg hr0.le]
      have hξNorm : ‖mixedEmbedding F (ξ : F)‖ ≤ A * ‖E x.1‖ := by
        have h := norm_mixedEmbedding_le_of_adele k 0 (ξ : F)
        rw [add_zero] at h
        have h' : ‖mixedEmbedding F (ξ : F)‖ ≤ ‖E (k⁻¹ : 𝕀[F]).val.1‖ * ‖E x.1‖ := by
          simpa only [E, x, Prod.fst_zero, map_zero, norm_zero, add_zero] using h
        exact h'.trans (mul_le_mul_of_nonneg_right ((hA₀ k hk).trans (le_max_left _ _))
          (norm_nonneg _))
      have hzMul : ‖z ξ‖ ≤ B * ‖mixedEmbedding F (ξ : F)‖ := by
        have h := norm_mul_le (mixedEmbedding F (algebraMap (𝓞 F) F b)) (mixedEmbedding F (ξ : F))
        rw [← map_mul] at h
        exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
      have hscale : ρ * ‖z ξ‖ ≤ ‖E y.1‖ := by
        calc ρ * ‖z ξ‖ ≤ ρ * (B * (A * ‖E x.1‖)) :=
              mul_le_mul_of_nonneg_left
                (hzMul.trans (mul_le_mul_of_nonneg_left hξNorm (zero_le_one.trans hB))) hρ0.le
          _ = r * ‖E x.1‖ := by
              change r / (A * B) * (B * (A * ‖E x.1‖)) = r * ‖E x.1‖
              field_simp
          _ = ‖E y.1‖ := hyNorm.symm
      let w := ‖schwartzBruhatStageRealization a e s (Multiplicative.ofAdd y)‖
      have hw : 0 ≤ w := norm_nonneg _
      have hdecay : w * (1 + ‖E y.1‖) ^ M ≤ C' := (hC _ hy).trans (le_max_left _ _)
      have hpos : 0 < (1 + ρ * ‖z ξ‖) ^ M := pow_pos (hnn _ (norm_nonneg _)) _
      have hmono : (1 + ρ * ‖z ξ‖) ^ M ≤ (1 + ‖E y.1‖) ^ M :=
        pow_le_pow_left₀ (hnn _ (norm_nonneg _)).le (by linarith) M
      have hwle : w * (1 + ρ * ‖z ξ‖) ^ M ≤ C' :=
        (mul_le_mul_of_nonneg_left hmono hw).trans hdecay
      calc w ≤ C' / (1 + ρ * ‖z ξ‖) ^ M := (le_div_iff₀ hpos).mpr hwle
        _ = G ξ := div_eq_mul_inv _ _
        _ = u ξ := (indicator_of_mem hξ G).symm
    · have h0 : schwartzBruhatStageRealization a e s (Multiplicative.ofAdd y) = 0 := by
        rw [schwartzBruhatStageRealization_apply_dite, dite_eq_right hy]
      exact (norm_eq_zero.mpr h0).le.trans (hu0 ξ)
  have hsum := hu.of_nonneg_of_le (fun _ => norm_nonneg _) hpt
  have hρd : (ρ ^ d)⁻¹ = (A * B) ^ d * (t.val : ℝ)⁻¹ := by
    change ((r / (A * B)) ^ d)⁻¹ = _
    rw [div_pow, inv_div, hrd, div_eq_mul_inv]
  refine ⟨hsum, (hsum.tsum_le_tsum hpt hu).trans (htsum.trans (le_of_eq ?_))⟩
  rw [hρd]
  ring

/-- Multiplying an idele by a principal idele permutes the terms of the absolute
theta series. -/
private theorem normSum_mul_principal (f : ℬ[F]) (x : 𝕀[F]) (η : Fˣ) :
    ∑' ξ : Fˣ, ‖f (Multiplicative.ofAdd ((x * IdeleGroup.unitEmbedding (𝓞 F) F η).val *
        algebraMap F 𝔸[F] (ξ : F)))‖ =
      ∑' ξ : Fˣ, ‖f (Multiplicative.ofAdd (x.val * algebraMap F 𝔸[F] (ξ : F)))‖ := by
  refine Eq.trans ?_ ((Equiv.mulLeft η).tsum_eq
    (fun ξ : Fˣ ↦ ‖f (Multiplicative.ofAdd (x.val * algebraMap F 𝔸[F] (ξ : F)))‖))
  refine tsum_congr fun ξ ↦ ?_
  simp only [Equiv.coe_mulLeft, Units.val_mul, map_mul, mul_assoc]
  rfl

/-- Paper: Theorem 2.2.3.4(1), p. 83. The series of absolute values of the theta
terms decays faster than any inverse power of the idelic norm as that norm tends to
infinity.
Deviation: The bound is for the series of absolute values, at every idele of norm at
least one. Theorem 3.2.2.1(1), p. 124, needs it for absolute convergence. -/
theorem adelicTheta_normSum_decay_large (f : ℬ[F]) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : 𝕀[F], 1 ≤ ((ideleNorm F g : ℝ≥0) : ℝ) →
      ∑' ξ : Fˣ, ‖f (Multiplicative.ofAdd (g.val * algebraMap F 𝔸[F] (ξ : F)))‖ ≤
        C * ((((ideleNorm F g : ℝ≥0) : ℝ)) ^ N)⁻¹ := by
  obtain ⟨K, hK, hRep⟩ := exists_compact_idele_representatives (F := F)
  let point (ξ : Fˣ) (t : ℝ≥0ˣ) (k : 𝕀[F]) :=
    Multiplicative.ofAdd ((canonicalIdeleNormSection F t * k).val * algebraMap F 𝔸[F] (ξ : F))
  let P (φ : Multiplicative 𝔸[F] → ℂ) := ∃ u : Fˣ → ℝ, Summable u ∧
    ∀ (ξ : Fˣ) (t : ℝ≥0ˣ), 1 ≤ (t.val : ℝ) → ∀ k ∈ K,
      ‖φ (point ξ t k)‖ * (t.val : ℝ) ^ N ≤ u ξ
  have hzero : P 0 := ⟨0, summable_zero, fun _ _ _ _ _ => by simp⟩
  have hadd (φ ψ : Multiplicative 𝔸[F] → ℂ) : P φ → P ψ → P (φ + ψ) := by
    rintro ⟨u, hu, hφ⟩ ⟨v, hv, hψ⟩
    refine ⟨u + v, hu.add hv, fun ξ t ht k hk => ?_⟩
    change ‖φ (point ξ t k) + ψ (point ξ t k)‖ * (t.val : ℝ) ^ N ≤ u ξ + v ξ
    calc
      _ ≤ (‖φ (point ξ t k)‖ + ‖ψ (point ξ t k)‖) * (t.val : ℝ) ^ N :=
        mul_le_mul_of_nonneg_right (norm_add_le _ _) (by positivity)
      _ ≤ _ := by rw [add_mul]; exact add_le_add (hφ ξ t ht k hk) (hψ ξ t ht k hk)
  have hP : P (show schwartzBruhatSubmodule (Multiplicative 𝔸[F]) from f).val := by
    refine Submodule.iSup_induction (motive := P) _ f.property ?_ hzero hadd
    intro a φ hφ
    refine Submodule.iSup_induction (motive := P) _ hφ ?_ hzero hadd
    intro e ψ hψ
    obtain ⟨s, rfl⟩ := LinearMap.mem_range.mp hψ
    exact realization_normSection_summable_bound a e s K hK N
  obtain ⟨u, hu, hbound⟩ := hP
  refine ⟨max (∑' ξ, u ξ) 1, zero_lt_one.trans_le (le_max_right _ _), ?_⟩
  intro g hg
  let t := ideleNorm F g
  let a := canonicalIdeleNormSection F t
  let q := QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 F) F)
  have hker : q (a⁻¹ * g) ∈ (ideleClassNorm F).ker := by
    change ideleNorm F (a⁻¹ * g) = 1
    rw [map_mul, map_inv, canonicalIdeleNormSection_rightInverse F t]
    exact inv_mul_cancel t
  obtain ⟨k, hk, hq⟩ := hRep (q (a⁻¹ * g)) hker
  obtain ⟨η, hη⟩ := QuotientGroup.eq.mp hq
  have hg' : g = a * k * IdeleGroup.unitEmbedding (𝓞 F) F η := by
    rw [hη]
    group
  have hs : Summable (fun ξ => ‖f (point ξ t k)‖) := by
    simpa only [point, add_zero] using
      ((adelicAverage_summableUniformlyOn f {(a * k, 0)} isCompact_singleton).summable rfl)
  have hsum : (∑' ξ : Fˣ, ‖f (Multiplicative.ofAdd (g.val * algebraMap F 𝔸[F] (ξ : F)))‖) =
      ∑' ξ, ‖f (point ξ t k)‖ := by
    conv_lhs => rw [hg']
    exact normSum_mul_principal f (a * k) η
  rw [hsum]
  change (∑' ξ, ‖f (point ξ t k)‖) ≤ max (∑' ξ, u ξ) 1 * ((t.val : ℝ) ^ N)⁻¹
  have ht : 1 ≤ (t.val : ℝ) := hg
  rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos (zero_lt_one.trans_le ht) N)]
  rw [← tsum_mul_right]
  exact (Summable.tsum_le_tsum (fun ξ => hbound ξ t ht k hk)
    (hs.mul_right _) hu).trans (le_max_left _ _)

/-- Paper: Theorem 2.2.3.4(2), p. 83. The series of absolute values of the theta
terms grows at most like the inverse of the idelic norm as that norm tends to zero.
Deviation: The paper bounds theta itself, through Poisson summation, and the proof of
Theorem 3.2.2.1(1), p. 126, uses an Euler product. Here the bound is for the series
of absolute values, which Poisson summation does not control, at every idele of norm at
most one. The proof counts the points of a fixed lattice in balls. -/
theorem adelicTheta_normSum_le_small (f : ℬ[F]) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : 𝕀[F], ((ideleNorm F g : ℝ≥0) : ℝ) ≤ 1 →
      ∑' ξ : Fˣ, ‖f (Multiplicative.ofAdd (g.val * algebraMap F 𝔸[F] (ξ : F)))‖ ≤
        C * (((ideleNorm F g : ℝ≥0) : ℝ))⁻¹ := by
  obtain ⟨K, hK, hRep⟩ := exists_compact_idele_representatives (F := F)
  let point (ξ : Fˣ) (t : ℝ≥0ˣ) (k : 𝕀[F]) :=
    Multiplicative.ofAdd ((canonicalIdeleNormSection F t * k).val * algebraMap F 𝔸[F] (ξ : F))
  let P (φ : Multiplicative 𝔸[F] → ℂ) := ∃ C : ℝ, 0 < C ∧
    ∀ t : ℝ≥0ˣ, (t.val : ℝ) ≤ 1 → ∀ k ∈ K,
      Summable (fun ξ ↦ ‖φ (point ξ t k)‖) ∧ ∑' ξ, ‖φ (point ξ t k)‖ ≤ C * (t.val : ℝ)⁻¹
  have hzero : P 0 := ⟨1, one_pos, fun t _ _ _ ↦ by
    simp only [Pi.zero_apply, norm_zero, tsum_zero]
    exact ⟨summable_zero, by positivity⟩⟩
  have hadd (φ ψ : Multiplicative 𝔸[F] → ℂ) : P φ → P ψ → P (φ + ψ) := by
    rintro ⟨C₁, hC₁, hφ⟩ ⟨C₂, hC₂, hψ⟩
    refine ⟨C₁ + C₂, add_pos hC₁ hC₂, fun t ht k hk ↦ ?_⟩
    obtain ⟨hs₁, hb₁⟩ := hφ t ht k hk
    obtain ⟨hs₂, hb₂⟩ := hψ t ht k hk
    have hle (ξ : Fˣ) : ‖(φ + ψ) (point ξ t k)‖ ≤ ‖φ (point ξ t k)‖ + ‖ψ (point ξ t k)‖ :=
      norm_add_le _ _
    have hs := (hs₁.add hs₂).of_nonneg_of_le (fun _ ↦ norm_nonneg _) hle
    refine ⟨hs, (hs.tsum_le_tsum hle (hs₁.add hs₂)).trans ?_⟩
    rw [hs₁.tsum_add hs₂, add_mul]
    exact add_le_add hb₁ hb₂
  have hP : P (show schwartzBruhatSubmodule (Multiplicative 𝔸[F]) from f).val := by
    refine Submodule.iSup_induction (motive := P) _ f.property ?_ hzero hadd
    intro a φ hφ
    refine Submodule.iSup_induction (motive := P) _ hφ ?_ hzero hadd
    intro e ψ hψ
    obtain ⟨s, rfl⟩ := LinearMap.mem_range.mp hψ
    exact realization_normSection_small_bound a e s K hK
  obtain ⟨C, hC, hbound⟩ := hP
  refine ⟨C, hC, fun g hg ↦ ?_⟩
  let t := ideleNorm F g
  let a := canonicalIdeleNormSection F t
  let q := QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 F) F)
  have hker : q (a⁻¹ * g) ∈ (ideleClassNorm F).ker := by
    change ideleNorm F (a⁻¹ * g) = 1
    rw [map_mul, map_inv, canonicalIdeleNormSection_rightInverse F t]
    exact inv_mul_cancel t
  obtain ⟨k, hk, hq⟩ := hRep (q (a⁻¹ * g)) hker
  obtain ⟨η, hη⟩ := QuotientGroup.eq.mp hq
  have hg' : g = a * k * IdeleGroup.unitEmbedding (𝓞 F) F η := by
    rw [hη]
    group
  have hsum : (∑' ξ : Fˣ, ‖f (Multiplicative.ofAdd (g.val * algebraMap F 𝔸[F] (ξ : F)))‖) =
      ∑' ξ, ‖f (point ξ t k)‖ := by
    conv_lhs => rw [hg']
    exact normSum_mul_principal f (a * k) η
  rw [hsum]
  exact (hbound t hg k hk).2

/-- Paper: Theorem 2.2.3.4(2), p. 83. After subtracting the explicit polar
terms, theta decays faster than any power of the norm as it tends to zero. -/
theorem adelicTheta_decay_small (f : ℬ[F]) (N : ℕ) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ g : C[F], normℝ g < T →
      ‖adelicTheta f g - (normℝ g)⁻¹ • adeleSchwartzFourier f zeroAdele + f zeroAdele‖ ≤
        C * (normℝ g) ^ N := by
  obtain ⟨C, T, hC, hT, hlarge⟩ := adelicTheta_decay_large (adeleSchwartzFourier f) (N + 1)
  refine ⟨C, T⁻¹, hC, inv_pos.mpr hT, ?_⟩
  intro g hg
  have hnorm : 0 < normℝ g :=
    NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero (ideleClassNorm F g)))
  have hinv : normℝ (g⁻¹) = (normℝ g)⁻¹ := by
    simp only [map_inv, Units.val_inv_eq_inv_val, NNReal.coe_inv]
  have hg' : T < normℝ (g⁻¹) := by
    rw [hinv]
    exact (lt_inv_comm₀ hnorm hT).mp hg
  have hbound : ‖adelicTheta (adeleSchwartzFourier f) g⁻¹‖ ≤ C * (normℝ g) ^ (N + 1) := by
    simpa only [hinv, inv_pow, inv_inv] using hlarge g⁻¹ hg'
  rw [adelicTheta_riemannRoch f g, sub_right_comm, sub_add_cancel, add_sub_cancel_right,
    norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hnorm.le)]
  calc
    _ ≤ (normℝ g)⁻¹ * (C * (normℝ g) ^ (N + 1)) :=
      mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hnorm.le)
    _ = C * ((normℝ g)⁻¹ * (normℝ g * (normℝ g) ^ N)) := by
      rw [pow_succ']
      ac_rfl
    _ = _ := by rw [inv_mul_cancel_left₀ hnorm.ne']

/-- Paper: Theorem 2.2.3.4(3), p. 83. If both zero terms vanish, theta
decays at both ends at every exponential rate in the absolute logarithmic norm. -/
theorem adelicTheta_decay_both (f : ℬ[F]) (hf : f zeroAdele = 0)
    (hFourier : adeleSchwartzFourier f zeroAdele = 0) (N : ℕ) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ g : C[F], T < |Real.log (normℝ g)| →
      ‖adelicTheta f g‖ ≤ C * Real.exp (-(N : ℝ) * |Real.log (normℝ g)|) := by
  obtain ⟨C₁, T₁, hC₁, hT₁, hlarge⟩ := adelicTheta_decay_large f N
  -- The extra power absorbs the norm factor in Riemann–Roch.
  obtain ⟨C₂, T₂, _, hT₂, hdual⟩ := adelicTheta_decay_large (adeleSchwartzFourier f) (N + 1)
  let T := max 1 (max (Real.log T₁) (Real.log T₂))
  refine ⟨max C₁ C₂, T, hC₁.trans_le (le_max_left _ _),
    zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro g hg
  have hpos : 0 < normℝ g := NNReal.coe_pos.mpr (Units.zero_lt _)
  let r := Real.exp |Real.log (normℝ g)|
  have hthreshold {t : ℝ} (ht : 0 < t) (hle : Real.log t ≤ T) : t < r := by
    exact (Real.exp_log ht) ▸ Real.exp_lt_exp.mpr (hle.trans_lt hg)
  have h₁ := hthreshold hT₁ ((le_max_left _ _).trans (le_max_right 1 _))
  have h₂ := hthreshold hT₂ ((le_max_right _ _).trans (le_max_right 1 _))
  rw [neg_mul, Real.exp_neg, Real.exp_nat_mul]
  change ‖adelicTheta f g‖ ≤ max C₁ C₂ * (r ^ N)⁻¹
  by_cases hlog : 0 ≤ Real.log (normℝ g)
  · have hr : r = normℝ g := by
      dsimp [r]
      rw [abs_of_nonneg hlog, Real.exp_log hpos]
    rw [hr] at h₁ ⊢
    exact (hlarge g h₁).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · have hr : r = (normℝ g)⁻¹ := by
      dsimp [r]
      rw [abs_of_neg (lt_of_not_ge hlog), Real.exp_neg, Real.exp_log hpos]
    have hinv : normℝ (g⁻¹) = r := by
      rw [hr]
      simp only [map_inv, Units.val_inv_eq_inv_val, NNReal.coe_inv]
    have hbound := hdual g⁻¹ (hinv.symm ▸ h₂)
    rw [hinv, ← div_eq_mul_inv, le_div_iff₀ (pow_pos (Real.exp_pos _) _)] at hbound
    have htheta : adelicTheta f g = r • adelicTheta (adeleSchwartzFourier f) g⁻¹ := by
      simpa only [hr, hf, hFourier, smul_zero, add_zero, sub_zero]
        using adelicTheta_riemannRoch f g
    rw [htheta, norm_smul, Real.norm_of_nonneg (Real.exp_nonneg _), ← div_eq_mul_inv,
      le_div_iff₀ (pow_pos (Real.exp_pos _) _)]
    calc
      _ = ‖adelicTheta (adeleSchwartzFourier f) g⁻¹‖ * r ^ (N + 1) := by rw [pow_succ']; ring
      _ ≤ C₂ := hbound
      _ ≤ max C₁ C₂ := le_max_right _ _

/-- The generating seminorms of a Schwartz–Bruhat space are the stagewise continuous ones. -/
private theorem schwartzBruhat_stageWithSeminorms (G : Type*) [CommGroup G] [TopologicalSpace G] :
    WithSeminorms (E := SchwartzBruhat G)
      (Subtype.val : {p : Seminorm ℂ (schwartzBruhatSubmodule G) //
        ∀ (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient),
          Continuous (p ∘ schwartzBruhatStageInclusion a e)} → _) :=
  withGeneratingSeminorms_spec _ _

/-- The norm of point evaluation is a continuous seminorm on the Schwartz–Bruhat space. -/
private theorem schwartzBruhat_evalNorm_continuous {G : Type*} [CommGroup G]
    [TopologicalSpace G] (x : G) : Continuous (fun f : SchwartzBruhat G ↦ ‖f x‖) := by
  classical
  let p : Seminorm ℂ (SchwartzBruhat G) :=
    (normSeminorm ℂ ℂ).comp ((LinearMap.proj x).comp (schwartzBruhatSubmodule G).subtype)
  refine (schwartzBruhat_stageWithSeminorms G).continuous_seminorm ⟨p, fun a e ↦ ?_⟩
  change Continuous (p.comp (schwartzBruhatStageInclusion a e))
  let q : Seminorm ℂ (SchwartzBruhatStage e) := elementarySchwartzSeminorm (0, 0, 0, 0)
  have hq : Continuous (fun f : SchwartzBruhatStage e ↦ q f) :=
    (elementarySchwartz_withSeminorms (m := e.realDim) (n := e.torusDim)
      (r := e.latticeRank) (F := e.finiteFactor)).continuous_seminorm (0, 0, 0, 0)
  refine Seminorm.continuous_of_le (q := q) hq fun f ↦ ?_
  change ‖schwartzBruhatStageRealization a e f x‖ ≤ _
  rw [schwartzBruhatStageRealization_apply]
  split_ifs with hx
  · change ‖f _‖ ≤ elementarySchwartzSeminorm (0, 0, 0, 0) f
    rw [elementarySchwartzSeminorm_zero]
    refine le_ciSup (f := fun y ↦ ‖f y‖) ?_ _
    refine ⟨(elementarySchwartzBound f.val (0, 0, 0, 0)).toReal, forall_mem_range.mpr fun y ↦ ?_⟩
    simpa only [Pi.zero_apply, pow_zero, Finset.prod_const_one, mul_one, one_mul]
      using elementarySchwartz_monomial_bound f.property 0 0 y
  · rw [norm_zero]
    exact apply_nonneg q f

set_option maxHeartbeats 1500000 in
/-- Weighted partial sums along norm-section rays are dominated by a continuous seminorm. -/
private theorem exists_adelicTheta_weighted_partialSum_seminorm
    (K : Set 𝕀[F]) (hK : IsCompact K) (hKne : K.Nonempty) (N : ℕ) :
    ∃ p : Seminorm ℂ ℬ[F], Continuous (fun f : ℬ[F] ↦ p f) ∧
      ∀ (f : ℬ[F]) (t : ℝ≥0ˣ), 1 ≤ (t.val : ℝ) → ∀ k ∈ K, ∀ S : Finset Fˣ,
        (∑ ξ ∈ S, ‖f (Multiplicative.ofAdd
          ((canonicalIdeleNormSection F t * k).val * algebraMap F 𝔸[F] (ξ : F)))‖ *
          (t.val : ℝ) ^ N) ≤ p f := by
  let T := {t : ℝ≥0ˣ // 1 ≤ (t.val : ℝ)}
  let point (t : T) (k : K) (ξ : Fˣ) :=
    Multiplicative.ofAdd ((canonicalIdeleNormSection F t.val * k.val).val *
      algebraMap F 𝔸[F] (ξ : F))
  let ev (x : Multiplicative 𝔸[F]) : Seminorm ℂ ℬ[F] :=
    (normSeminorm ℂ ℂ).comp ((LinearMap.proj x).comp (schwartzBruhatSubmodule _).subtype)
  let partialSum (i : T × K × Finset Fˣ) : Seminorm ℂ ℬ[F] :=
    i.1.val.val ^ N • ∑ ξ ∈ i.2.2, ev (point i.1 i.2.1 ξ)
  have hpartial (i : T × K × Finset Fˣ) (f : ℬ[F]) :
      partialSum i f = ∑ ξ ∈ i.2.2, ‖f (point i.1 i.2.1 ξ)‖ * (i.1.val.val : ℝ) ^ N := by
    have hsum : (∑ ξ ∈ i.2.2, ev (point i.1 i.2.1 ξ)) f =
        ∑ ξ ∈ i.2.2, ‖f (point i.1 i.2.1 ξ)‖ := by
      change FunLike.coeAddMonoidHom (Seminorm ℂ ℬ[F]) ℬ[F] ℝ
        (∑ ξ ∈ i.2.2, ev (point i.1 i.2.1 ξ)) f = _
      rw [map_sum, Finset.sum_apply]
      rfl
    dsimp only [partialSum]
    rw [smul_apply]
    change (↑(i.1.val.val ^ N) : ℝ) * (∑ ξ ∈ i.2.2, ev (point i.1 i.2.1 ξ)) f = _
    rw [hsum, NNReal.coe_pow, mul_comm, Finset.sum_mul]
  have hcont (i : T × K × Finset Fˣ) : Continuous (partialSum i) :=
    (Seminorm.continuous_finsetSum fun ξ _ ↦
      schwartzBruhat_evalNorm_continuous (point i.1 i.2.1 ξ)).const_smul _
  obtain ⟨k₀, hk₀⟩ := hKne
  have hbdd : BddAbove (range partialSum) := Seminorm.bddAbove_range_iff.mpr fun f ↦ by
    let P (φ : Multiplicative 𝔸[F] → ℂ) :=
      ∃ C : ℝ, ∀ i : T × K × Finset Fˣ,
        ∑ ξ ∈ i.2.2, ‖φ (point i.1 i.2.1 ξ)‖ * (i.1.val.val : ℝ) ^ N ≤ C
    have hzero : P 0 := ⟨0, fun _ ↦ by simp⟩
    have hadd (φ ψ : Multiplicative 𝔸[F] → ℂ) : P φ → P ψ → P (φ + ψ) := by
      rintro ⟨C, hC⟩ ⟨D, hD⟩
      refine ⟨C + D, fun i ↦ ?_⟩
      refine le_trans ?_ (add_le_add (hC i) (hD i))
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun ξ _ ↦ by
        rw [← add_mul]
        exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (by positivity)
    have hP : P f.val := by
      refine Submodule.iSup_induction (motive := P) _ f.property ?_ hzero hadd
      intro a φ hφ
      refine Submodule.iSup_induction (motive := P) _ hφ ?_ hzero hadd
      intro e ψ hψ
      obtain ⟨s, rfl⟩ := LinearMap.mem_range.mp hψ
      obtain ⟨u, hu, hbound⟩ := realization_normSection_summable_bound a e s K hK N
      have hnonneg (ξ : Fˣ) : 0 ≤ u ξ :=
        (by positivity : 0 ≤ ‖schwartzBruhatStageRealization a e s
          (point ⟨1, by simp⟩ ⟨k₀, hk₀⟩ ξ)‖ * ((1 : ℝ≥0ˣ).val : ℝ) ^ N).trans
          (hbound ξ 1 (by simp) k₀ hk₀)
      exact ⟨∑' ξ, u ξ, fun i ↦
        (Finset.sum_le_sum fun ξ _ ↦ hbound ξ i.1.val i.1.property i.2.1.val
          i.2.1.property).trans (hu.sum_le_tsum _ fun ξ _ ↦ hnonneg ξ)⟩
    obtain ⟨C, hC⟩ := hP
    exact ⟨C, forall_mem_range.mpr fun i ↦ (hpartial i f).trans_le (hC i)⟩
  -- Barrelledness upgrades the pointwise bound on partial sums to a continuous seminorm.
  let : BarrelledSpace ℂ ℬ[F] := (adeleSchwartz_montel (F := F)).2.1
  let p : Seminorm ℂ ℬ[F] := ⨆ i, partialSum i
  have hcoe : (⇑p : ℬ[F] → ℝ) = ⨆ i, ⇑(partialSum i) :=
    Seminorm.coe_iSup_eq (p := partialSum) hbdd
  have hp : Continuous (fun f : ℬ[F] ↦ p f) :=
    hcoe.symm ▸ Seminorm.continuous_iSup partialSum hcont hbdd
  refine ⟨p, hp, fun f t ht k hk S ↦ ?_⟩
  let i : T × K × Finset Fˣ := (⟨t, ht⟩, ⟨k, hk⟩, S)
  exact (hpartial i f).ge.trans ((le_ciSup hbdd i) f)

set_option maxHeartbeats 1000000 in
/-- Paper: Theorem 2.2.3.4(5), p. 83. The inverse-power bound at norm greater
than one has a constant uniform over a bounded set of adelic test functions. -/
theorem adelicTheta_decay_bounded_large_threshold_one (B : Set ℬ[F])
    (hB : IsVonNBounded ℂ B) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f ∈ B, ∀ g : C[F], 1 < normℝ g →
      ‖adelicTheta f g‖ ≤ C * ((normℝ g) ^ N)⁻¹ := by
  obtain ⟨K, hK, hRep⟩ := exists_compact_idele_representatives (F := F)
  have hKne : K.Nonempty := by
    obtain ⟨k, hk, _⟩ := hRep 1 ((ideleClassNorm F).ker.one_mem)
    exact ⟨k, hk⟩
  let weighted := exists_adelicTheta_weighted_partialSum_seminorm (F := F)
  obtain ⟨p, hp, hpartial⟩ := weighted K hK hKne N
  have hS := schwartzBruhat_stageWithSeminorms (Multiplicative 𝔸[F])
  have hpB : BddAbove (p '' B) :=
    (hS.isVonNBounded_iff_seminorm_bddAbove.mp hB)
      ⟨p, fun a e ↦ hp.comp (hS.continuous_of_continuous_comp
        (schwartzBruhatStageInclusion a e) fun i ↦ i.property a e)⟩
  obtain ⟨C, hC⟩ := hpB
  refine ⟨max C 1, zero_lt_one.trans_le (le_max_right _ _), fun f hf g hg ↦ ?_⟩
  let t := ideleClassNorm F g
  let a := canonicalIdeleNormSection F t
  let q := QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 F) F)
  have hn : ideleClassNorm F (q a) = t := canonicalIdeleNormSection_rightInverse F t
  have hker : (q a)⁻¹ * g ∈ (ideleClassNorm F).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hn]
    exact inv_mul_cancel t
  obtain ⟨k, hk, hq⟩ := hRep ((q a)⁻¹ * g) hker
  have hclass : q (a * k) = g := by
    rw [map_mul, show q k = (q a)⁻¹ * g from hq, mul_inv_cancel_left]
  let point (ξ : Fˣ) := Multiplicative.ofAdd ((a * k).val * algebraMap F 𝔸[F] (ξ : F))
  have hs : Summable (fun ξ ↦ ‖f (point ξ)‖) := by
    simpa only [point, add_zero] using
      ((adelicAverage_summableUniformlyOn f {(a * k, 0)} isCompact_singleton).summable rfl)
  have htheta : adelicTheta f g = ∑' ξ, f (point ξ) := by
    rw [← hclass]
    change adelicTheta f (classOf (a * k)) =
      ∑' ξ : Fˣ, f (Multiplicative.ofAdd ((a * k).val * algebraMap F 𝔸[F] (ξ : F)))
    rw [adelicTheta_mk]
    simp only [mul_comm (a * k).val]
  rw [htheta, ← div_eq_mul_inv, le_div_iff₀ (pow_pos (zero_lt_one.trans hg) _)]
  calc
    _ ≤ (∑' ξ, ‖f (point ξ)‖) * (normℝ g) ^ N :=
      mul_le_mul_of_nonneg_right (norm_tsum_le_tsum_norm hs) (by positivity)
    _ = ∑' ξ, ‖f (point ξ)‖ * (normℝ g) ^ N := tsum_mul_right.symm
    _ ≤ p f := (hs.mul_right _).tsum_le_of_sum_le (hpartial f t hg.le k hk)
    _ ≤ max C 1 := (hC (mem_image_of_mem _ hf)).trans (le_max_left _ _)

/-- Paper: Proof of Theorem 2.2.3.4(4), p. 85. The adelic Fourier transform sends
von Neumann bounded sets of Schwartz–Bruhat functions to bounded sets. -/
theorem adeleSchwartzFourier_image_isVonNBounded (B : Set ℬ[F])
    (hB : IsVonNBounded ℂ B) :
    IsVonNBounded ℂ ((adeleSchwartzFourier (F := F)) '' B) := by
  refine (exists_adeleSchwartzFourierCLM (F := F)).elim fun T hT ↦ ?_
  apply (hB.image T).subset
  exact Set.image_subset_iff.mpr fun f hf ↦ ⟨f, hf, Subtype.ext (funext (hT f))⟩

/-- Paper: Theorem 2.2.3.4(5), p. 83. The uniform estimates on a bounded set
hold with threshold one and a common constant. -/
theorem adelicTheta_decay_bounded_threshold_one (B : Set ℬ[F])
    (hB : IsVonNBounded ℂ B) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f ∈ B, ∀ g : C[F],
      (1 < normℝ g → ‖adelicTheta f g‖ ≤ C * ((normℝ g) ^ N)⁻¹) ∧
      (normℝ g < 1 →
        ‖adelicTheta f g - (normℝ g)⁻¹ • adeleSchwartzFourier f zeroAdele + f zeroAdele‖ ≤
          C * (normℝ g) ^ N) ∧
      (f zeroAdele = 0 → adeleSchwartzFourier f zeroAdele = 0 →
        Real.exp (-|Real.log (normℝ g)|) < 1 →
        ‖adelicTheta f g‖ ≤ C * Real.exp (-(N : ℝ) * |Real.log (normℝ g)|)) := by
  let large := adelicTheta_decay_bounded_large_threshold_one (F := F)
  obtain ⟨C₁, hC₁, hlarge⟩ := large B hB N
  let Fourier := adeleSchwartzFourier (F := F)
  let fourierBounded := adeleSchwartzFourier_image_isVonNBounded (F := F)
  obtain ⟨C₂, _, hdual⟩ := large (Fourier '' B) (fourierBounded B hB) (N + 1)
  refine ⟨max C₁ C₂, hC₁.trans_le (le_max_left _ _), ?_⟩
  intro f hf g
  have hpos : 0 < normℝ g := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hbig (hg : 1 < normℝ g) :
      ‖adelicTheta f g‖ ≤ max C₁ C₂ * ((normℝ g) ^ N)⁻¹ :=
    (hlarge f hf g hg).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hsmall (hg : normℝ g < 1) :
      ‖adelicTheta f g - (normℝ g)⁻¹ • adeleSchwartzFourier f zeroAdele + f zeroAdele‖ ≤
        max C₁ C₂ * (normℝ g) ^ N := by
    have hinv : normℝ (g⁻¹) = (normℝ g)⁻¹ := by
      simp only [map_inv, Units.val_inv_eq_inv_val, NNReal.coe_inv]
    have hg' : 1 < normℝ (g⁻¹) := by
      rw [hinv]
      exact one_lt_inv_iff₀.mpr ⟨hpos, hg⟩
    have hbound : ‖adelicTheta (adeleSchwartzFourier f) g⁻¹‖ ≤ C₂ * (normℝ g) ^ (N + 1) := by
      simpa only [Fourier, hinv, inv_pow, inv_inv] using hdual (Fourier f) ⟨f, hf, rfl⟩ g⁻¹ hg'
    rw [adelicTheta_riemannRoch f g, sub_right_comm, sub_add_cancel, add_sub_cancel_right,
      norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hpos.le)]
    calc
      _ ≤ (normℝ g)⁻¹ * (C₂ * (normℝ g) ^ (N + 1)) :=
        mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hpos.le)
      _ = C₂ * ((normℝ g)⁻¹ * (normℝ g * (normℝ g) ^ N)) := by rw [pow_succ']; ac_rfl
      _ ≤ _ := by
        rw [inv_mul_cancel_left₀ hpos.ne']
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hpos.le _)
  refine ⟨hbig, hsmall, fun hf₀ hF₀ hg ↦ ?_⟩
  rw [neg_mul, Real.exp_neg, Real.exp_nat_mul]
  rcases lt_trichotomy (normℝ g) 1 with hlt | heq | hgt
  · rw [abs_of_neg (Real.log_neg hpos hlt), Real.exp_neg, Real.exp_log hpos, inv_pow, inv_inv]
    simpa only [hf₀, hF₀, smul_zero, sub_zero, add_zero] using hsmall hlt
  · simp [heq] at hg
  · rw [abs_of_pos (Real.log_pos hgt), Real.exp_log hpos]
    exact hbig hgt

/-- Paper: Theorem 2.2.3.4(4), p. 83. The three decay estimates admit a common
constant and threshold uniform over a bounded set of Schwartz–Bruhat functions.
The two-sided estimate applies to members whose two zero terms vanish. -/
theorem adelicTheta_decay_bounded (B : Set ℬ[F]) (hB : IsVonNBounded ℂ B) (N : ℕ) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ f ∈ B, ∀ g : C[F],
      (T < normℝ g → ‖adelicTheta f g‖ ≤ C * ((normℝ g) ^ N)⁻¹) ∧
      (normℝ g < T →
        ‖adelicTheta f g - (normℝ g)⁻¹ • adeleSchwartzFourier f zeroAdele + f zeroAdele‖ ≤
          C * (normℝ g) ^ N) ∧
      (f zeroAdele = 0 → adeleSchwartzFourier f zeroAdele = 0 →
        Real.exp (-|Real.log (normℝ g)|) < T →
        ‖adelicTheta f g‖ ≤ C * Real.exp (-(N : ℝ) * |Real.log (normℝ g)|)) := by
  have hthreshold := adelicTheta_decay_bounded_threshold_one (F := F) B
  obtain ⟨C, hC, hbound⟩ := hthreshold hB N
  exact ⟨C, 1, hC, zero_lt_one, hbound⟩

end Adelic

end RiemannMasullo
