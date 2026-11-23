module

public import RiemannMasullo.Ch10_TraceSpectral.Sec2

import all RiemannMasullo.Ch03_IdelicZeta.Sec2
import RiemannMasullo.Ch10_TraceSpectral.Sec1
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Logic.Equiv.Nat

/-! # §10.2 assertions that are false as printed -/

@[expose] public noncomputable section

open MeasureTheory NumberField Set
open scoped NNReal

namespace RiemannMasullo

attribute [local instance] instIdeleClassMeasurableSpaceSec1

set_option quotPrecheck false

local notation "C𝔽(" F ")" => IdeleClassGroup (𝓞 F) F
local notation "C₁(" F ")" => (ideleClassNorm F).ker
local notation "shift(" b ", " t ")" => ((b : ℝ) : ℂ) + (t : ℂ) * Complex.I
local notation "order(" χ ", " z ")" =>
  (meromorphicOrderAt (continuedCompletedHeckeL χ) z).untop₀.toNat
local notation "weight(" F ", " α ", " s ")" =>
  ((ideleClassTamagawaMeasure F).withDensity fun g : C𝔽(F) ↦ ENNReal.ofReal
    (intervalSobolevDensity (-α) α s (Real.log ((ideleClassNorm F g).val : ℝ)))⁻¹)

local notation "lineWeight(" F ", " s ")" =>
  ((ideleClassTamagawaMeasure F).withDensity fun g : C𝔽(F) ↦ ENNReal.ofReal
    (intervalSobolevDensity 0 0 s (Real.log ((ideleClassNorm F g).val : ℝ)))⁻¹)
local notation "floorCut(" s ", " N ")" => min N (Nat.floor ((s - 1) / 2 + 1))
local notation "stripFloor(" α ", " s ", " b ", " N ")" =>
  (if b = -α ∨ b = α then floorCut(s, N) else if b ∈ Ioo (-α) α then N else 0)

/-- Paper: Theorem 10.2.1.1, p. 440. For the printed index set the jets
belong to the negative line space and, in any enumeration, are the
functional half of a Markushevich basis of the theta quotient. -/
def Printed.spectralLineMarkushevichBasis : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice χ →
    ∀ (a s : ℝ) (hs : 1 < s),
      let J := {j : PontryaginDual C₁(F) × ℝ × ℕ //
        j.2.2 < floorCut(s, order(χ j.1, shift(a, j.2.1)))}
      let η := fun j : J ↦ spectralZeroJet (χ j.val.1) 0 j.val.2.1 j.val.2.2
      let hI := le_rfl (a := (0 : ℝ))
      let hs₀ := le_of_lt (zero_lt_one.trans hs)
      let Q := spectralSobolevQuotient F a hI hs₀
      let D := spectralSobolevDualEmbedding F a hI hs₀
      Countable J ∧ ∃ (h : ∀ j, MemLp (η j) 2 (lineWeight(F, s)))
        (x : J → Q) (Λ : J → StrongDual ℂ Q), IsSpectralMarkushevichBasis x Λ ∧
        ∀ j, D (Λ j) = (h j).toLp (η j)

/-- Paper: Theorem 10.2.1.1 and (10.2.1.6), p. 440. The printed floor cutoff
makes each selected jet belong to the negative Sobolev space on the line. -/
def Printed.spectralLineJet_memLp : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice χ →
    ∀ (a s : ℝ), 1 < s → ∀ (ω : PontryaginDual C₁(F)) (t : ℝ) (k : ℕ),
    k < min (order(χ ω, shift(a, t))) (Nat.floor ((s - 1) / 2 + 1)) →
    MemLp (spectralZeroJet (χ ω) 0 t k) 2 (weight(F, 0, s))

/-- Paper: Theorem 10.2.1.1 and (10.2.1.6), p. 440. Take the splitting
field of X³−2, the trivial character, s = 3, and a+it a nontrivial zero of the
two-dimensional Artin factor. That factor occurs squared in the Dedekind
zeta function. The cutoff includes k = 1, whose squared norm has a 1/|x|
tail in the log norm coordinate x. -/
theorem Printed.spectralLineJet_memLp_false : ¬ Printed.spectralLineJet_memLp := by sorry

/-- Paper: Theorem 10.2.1.1, p. 440. The squared Artin factor of the
splitting field of X³−2 supplies a double zero. At s = 3 its first
derivative is among the printed jets and fails square integrability. -/
theorem Printed.spectralLineMarkushevichBasis_false :
    ¬ Printed.spectralLineMarkushevichBasis := by
  intro h
  apply Printed.spectralLineJet_memLp_false
  intro F _ _ χ hχ a s hs ω t k hk
  obtain ⟨hh, _⟩ := (h F χ hχ a s hs).2
  simpa only [neg_zero] using hh ⟨(ω, t, k), hk⟩

/-- Paper: Proposition 10.2.1.3, p. 443. The printed annulus statement uses
all derivative orders below the full zero multiplicity. -/
def Printed.spectralLineJet_annulus : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice χ →
    ∀ (a s : ℝ), 1 < s → ∃ C : ℝ, 0 < C ∧
    ∀ (ω : PontryaginDual C₁(F)) (t : ℝ) (k : ℕ),
      k < order(χ ω, shift(a, t)) →
      let η := spectralZeroJet (χ ω) 0 t k
      ∃ h : MemLp η 2 (weight(F, 0, s)), C⁻¹ ≤ ‖h.toLp η‖ ∧ ‖h.toLp η‖ ≤ C

/-- Paper: Proposition 10.2.1.3, p. 443. In the splitting field of X³−2
use the trivial character and a nontrivial zero of its squared two-dimensional
Artin factor. For s = 3 the printed full multiplicity includes k = 1 and the
squared norm diverges logarithmically. -/
theorem Printed.spectralLineJet_annulus_false : ¬ Printed.spectralLineJet_annulus := by
  intro hall
  apply Printed.spectralLineJet_memLp_false
  intro F _ _ χ hχ a s hs ω t k hk
  obtain ⟨_, _, h⟩ := hall F χ hχ a s hs
  exact (h ω t k (lt_of_lt_of_le hk (min_le_left _ _))).choose

/-- Paper: Proposition 10.2.1.3, p. 443. As printed, the a-line family
fails to be contained in an open ball of some positive radius. -/
def Printed.spectralLineJet_not_subset_ball : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice χ →
    ∀ (a s : ℝ), 1 < s → ∃ C : ℝ, 0 < C ∧
    ¬ (∀ (ω : PontryaginDual C₁(F)) (t : ℝ) (k : ℕ),
      k < order(χ ω, shift(a, t)) →
      ∃ h : MemLp (spectralZeroJet (χ ω) 0 t k) 2 (weight(F, 0, s)),
        ‖h.toLp (spectralZeroJet (χ ω) 0 t k)‖ < C⁻¹)

/-- Paper: Proposition 10.2.1.3, p. 443. Take F = ℚ, a = 2 and s = 2.
All the completed Hecke L-functions are zero-free on this line by the
absolutely convergent Euler products and the nonvanishing gamma factors.
The resulting empty family is contained in every open ball. -/
theorem Printed.spectralLineJet_not_subset_ball_false :
    ¬ Printed.spectralLineJet_not_subset_ball := by
  intro hall
  obtain ⟨χ, hχ⟩ := exists_spectralBasepointChoice ℚ
  obtain ⟨_, _, hn⟩ := hall ℚ χ hχ 2 2 (by norm_num)
  apply hn
  intro ω t k hk
  let z := shift((2 : ℝ), t)
  have hz : 1 < z.re := by norm_num [z]
  have hval : continuedCompletedHeckeL (χ ω) z ≠ 0 := by
    rw [show continuedCompletedHeckeL (χ ω) z = completedHeckeL (χ ω) ⟨z, hz⟩ from
      (continuedCompletedHeckeL_spec (χ ω)).2 ⟨z, hz⟩]
    exact mul_ne_zero (heckeGammaFactor_ne_zero_of_re_pos (χ ω) (zero_lt_one.trans hz))
      (finiteHeckeL_ne_zero_of_one_lt_re (χ ω) ⟨z, hz⟩)
  have horder := ((continuedCompletedHeckeL_spec (χ ω)).1 (mem_univ z)).meromorphicOrderAt_eq_zero_iff.mpr hval
  simp [z] at horder
  simp [horder] at hk

/-- Paper: Proposition 10.2.1.3, p. 443. One constant gives (10.2.1.12)
and the asserted noncontainment for the family with full multiplicities. -/
def Printed.spectralLineJet_annulus_and_noncontainment : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice χ →
    ∀ (a s : ℝ), 1 < s →
      let J := {j : PontryaginDual C₁(F) × ℝ × ℕ // j.2.2 < order(χ j.1, shift(a, j.2.1))}
      let η := fun j : J ↦ spectralZeroJet (χ j.val.1) 0 j.val.2.1 j.val.2.2
      ∃ C : ℝ, 0 < C ∧
        (∀ j, ∃ h : MemLp (η j) 2 (weight(F, 0, s)), C⁻¹ ≤ ‖h.toLp (η j)‖ ∧ ‖h.toLp (η j)‖ ≤ C) ∧
        ¬ (∀ j, ∃ h : MemLp (η j) 2 (weight(F, 0, s)), ‖h.toLp (η j)‖ < C⁻¹)

/-- Paper: Proposition 10.2.1.3, p. 443. For ℚ at a = 2 the zero
family is empty and hence lies in the open ball for every C > 0. -/
theorem Printed.spectralLineJet_annulus_and_noncontainment_false :
    ¬ Printed.spectralLineJet_annulus_and_noncontainment := by
  intro hall
  apply Printed.spectralLineJet_not_subset_ball_false
  intro F _ _ χ hχ a s hs
  obtain ⟨C, hC, _, hn⟩ := hall F χ hχ a s hs
  refine ⟨C, hC, fun h ↦ hn ?_⟩
  intro j
  exact h j.val.1 j.val.2.1 j.val.2.2 j.property

/-- Paper: Terminology 10.2.1.2(2), p. 444. The printed implication says
that the functionals paired with a regular Markushevich family are bounded. -/
def Printed.spectralRegular_dual_bounded : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (x : ℕ → E) (Λ : ℕ → StrongDual ℂ E),
    (∀ i, Λ i (x i) = 1) → (∀ i j, i ≠ j → Λ j (x i) = 0) →
    Dense (Submodule.span ℂ (range x) : Set E) →
    (∀ v : E, (∀ i, Λ i v = 0) → v = 0) → IsRegularSpectralFamily x →
    ∃ C : ℝ, ∀ n, ‖Λ n‖ ≤ C

/-- Let `b` be a Hilbert basis indexed by `ℕ ⊕ ℕ`. Put `x (inl n) = b (inl n)` and
`x (inr n) = b (inl n) + (n + 1)⁻¹ • b (inr n)`. Then `x` has a total biorthogonal family `Λ`
with `‖Λ (inr n)‖ ≥ n + 1`. -/
private theorem Printed.spectralRegular_dual_bounded_false_exists {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (b : HilbertBasis (ℕ ⊕ ℕ) ℂ E) :
    ∃ (x : ℕ ⊕ ℕ → E) (Λ : ℕ ⊕ ℕ → StrongDual ℂ E),
      (∀ i, Λ i (x i) = 1) ∧ (∀ i j, i ≠ j → Λ j (x i) = 0) ∧
      Dense (Submodule.span ℂ (Set.range x) : Set E) ∧
      (∀ v : E, (∀ i, Λ i v = 0) → v = 0) ∧ (∀ i, 1 ≤ ‖x i‖) ∧
      ∀ n : ℕ, (n : ℝ) + 1 ≤ ‖Λ (Sum.inr n)‖ := by
  classical
  have hb : ∀ i j, inner ℂ (b i) (b j) = if i = j then (1 : ℂ) else 0 :=
    orthonormal_iff_ite.mp b.orthonormal
  have hn1 : ∀ i, ‖b i‖ = 1 := b.orthonormal.1
  have hne : ∀ n : ℕ, ((n : ℂ) + 1) ≠ 0 := fun n => Nat.cast_add_one_ne_zero n
  refine ⟨Sum.elim (fun n => b (Sum.inl n))
      (fun n => b (Sum.inl n) + ((n : ℂ) + 1)⁻¹ • b (Sum.inr n)),
    Sum.elim
      (fun n => innerSL ℂ (b (Sum.inl n)) - ((n : ℂ) + 1) • innerSL ℂ (b (Sum.inr n)))
      (fun n => ((n : ℂ) + 1) • innerSL ℂ (b (Sum.inr n))), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro (n | n)
    · simp [hb, hn1, innerSL_apply_apply]
    · simp [hb, hn1, innerSL_apply_apply, inner_add_right, inner_smul_right, hne n]
  · rintro (n | n) (m | m) hij
    · have : m ≠ n := fun h => hij (by rw [h])
      simp [hb, innerSL_apply_apply, this]
    · simp [hb, innerSL_apply_apply]
    · by_cases hmn : m = n
      · subst hmn
        simp [hb, hn1, innerSL_apply_apply, inner_add_right, inner_smul_right, hne m]
      · simp [hb, innerSL_apply_apply, inner_add_right, inner_smul_right, hmn]
    · have : m ≠ n := fun h => hij (by rw [h])
      simp [hb, innerSL_apply_apply, inner_add_right, inner_smul_right, this]
  · rw [Submodule.dense_iff_topologicalClosure_eq_top, eq_top_iff, ← b.dense_span]
    refine Submodule.topologicalClosure_mono (Submodule.span_le.mpr ?_)
    rintro _ ⟨(n | n), rfl⟩
    · exact Submodule.subset_span ⟨Sum.inl n, rfl⟩
    · have hx : b (Sum.inr n) = ((n : ℂ) + 1) •
          ((b (Sum.inl n) + ((n : ℂ) + 1)⁻¹ • b (Sum.inr n)) - b (Sum.inl n)) := by
        rw [add_sub_cancel_left, smul_smul, mul_inv_cancel₀ (hne n), one_smul]
      rw [SetLike.mem_coe, hx]
      exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.subset_span ⟨Sum.inr n, rfl⟩)
        (Submodule.subset_span ⟨Sum.inl n, rfl⟩))
  · intro v hv
    have hr : ∀ n : ℕ, inner ℂ (b (Sum.inr n)) v = 0 := by
      intro n
      have := hv (Sum.inr n)
      simpa [innerSL_apply_apply, hne n] using this
    have hl : ∀ n : ℕ, inner ℂ (b (Sum.inl n)) v = 0 := by
      intro n
      have := hv (Sum.inl n)
      simpa [innerSL_apply_apply, hr n] using this
    have hall : ∀ k, b.repr v k = 0 := by
      rintro (n | n)
      · rw [b.repr_apply_apply, hl n]
      · rw [b.repr_apply_apply, hr n]
    have hs := b.hasSum_repr v
    simp only [hall, zero_smul] at hs
    exact hs.unique hasSum_zero
  · rintro (n | n)
    · simp [hn1]
    · have h1 : inner ℂ (b (Sum.inl n))
          (b (Sum.inl n) + ((n : ℂ) + 1)⁻¹ • b (Sum.inr n)) = 1 := by
        rw [inner_add_right, inner_smul_right, hb, hb]
        simp
      have h2 := norm_inner_le_norm (𝕜 := ℂ) (b (Sum.inl n))
        (b (Sum.inl n) + ((n : ℂ) + 1)⁻¹ • b (Sum.inr n))
      rw [h1, hn1, one_mul, norm_one] at h2
      simpa using h2
  · intro n
    have h := ContinuousLinearMap.le_opNorm (((n : ℂ) + 1) • innerSL ℂ (b (Sum.inr n)))
      (b (Sum.inr n))
    have hv : (((n : ℂ) + 1) • innerSL ℂ (b (Sum.inr n))) (b (Sum.inr n)) =
        ((n : ℕ) + 1 : ℕ) := by
      simp [hn1, innerSL_apply_apply]
    rw [hv, hn1, mul_one, Complex.norm_natCast] at h
    simpa using h

/-- Paper: Terminology 10.2.1.2(2), p. 444. In complex ℓ² take
x₂ₙ = e₂ₙ and x₂ₙ₊₁ = e₂ₙ + (n+1)⁻¹ e₂ₙ₊₁. If eⱼ* is coordinate evaluation,
the dual pair is e₂ₙ* − (n+1)e₂ₙ₊₁* and (n+1)e₂ₙ₊₁*. Both spans contain
the finite-support families, every x has norm at least one, and the dual
norms are unbounded. -/
theorem Printed.spectralRegular_dual_bounded_false :
    ¬ Printed.spectralRegular_dual_bounded := by
  intro h
  obtain ⟨x, Λ, h1, h2, h3, h4, h5, h6⟩ := Printed.spectralRegular_dual_bounded_false_exists
    (HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ (lp (fun _ : ℕ ⊕ ℕ => ℂ) 2)))
  let σ : ℕ ≃ ℕ ⊕ ℕ := Equiv.natSumNatEquivNat.symm
  obtain ⟨C, hC⟩ := h (lp (fun _ : ℕ ⊕ ℕ => ℂ) 2) (x ∘ σ) (Λ ∘ σ)
    (fun i => h1 (σ i)) (fun i j hij => h2 (σ i) (σ j) (σ.injective.ne hij))
    (by rwa [σ.surjective.range_comp])
    (fun v hv => h4 v (fun k => by simpa using hv (σ.symm k)))
    ⟨1, one_pos, fun i => h5 (σ i)⟩
  obtain ⟨n, hn⟩ := exists_nat_gt C
  have hCn := hC (σ.symm (Sum.inr n))
  simp only [Function.comp_apply, Equiv.apply_symm_apply] at hCn
  linarith [h6 n]

/-- Paper: Corollary 10.2.1.4, p. 444. The printed floor-indexed
line jets form a normalized basis in the image of the quotient dual. -/
def Printed.spectralLineMarkushevichBasis_normalized : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice χ →
    ∀ (a s : ℝ) (hs : 1 < s),
      let J := {j : PontryaginDual C₁(F) × ℝ × ℕ //
        j.2.2 < floorCut(s, order(χ j.1, shift(a, j.2.1)))}
      let η := fun j : J ↦ spectralZeroJet (χ j.val.1) 0 j.val.2.1 j.val.2.2
      let hI := le_rfl (a := (0 : ℝ))
      let hs₀ := le_of_lt (zero_lt_one.trans hs)
      let Q := spectralSobolevQuotient F a hI hs₀
      let D := spectralSobolevDualEmbedding F a hI hs₀
      Countable J ∧ ∃ (h : ∀ j, MemLp (η j) 2 (lineWeight(F, s)))
        (x : J → Q) (Λ : J → StrongDual ℂ Q), IsSpectralMarkushevichBasis x Λ ∧
        (∀ j, D (Λ j) = (h j).toLp (η j)) ∧ IsNormalizedSpectralFamily (fun j ↦ D (Λ j))

/-- Paper: Corollary 10.2.1.4, p. 444. The splitting-field example at
s = 3 includes a positive-order jet of infinite squared integral. -/
theorem Printed.spectralLineMarkushevichBasis_normalized_false :
    ¬ Printed.spectralLineMarkushevichBasis_normalized := by
  intro hall
  apply Printed.spectralLineMarkushevichBasis_false
  intro F _ _ χ hχ a s hs
  obtain ⟨hc, h, x, Λ, hb, hΛ, _⟩ := hall F χ hχ a s hs
  exact ⟨hc, h, x, Λ, hb, hΛ⟩

/-- Paper: Theorem 10.2.1.1 and Remark 10.2.1.5, pp. 440, 444. The
asserted basis and its claimed primal normalization together give a bounded
regular family biorthogonal to the prescribed jets. -/
def Printed.spectralLineMarkushevichBasis_primal_normalized : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice χ →
    ∀ (a s : ℝ) (hs : 1 < s),
      let J := {j : PontryaginDual C₁(F) × ℝ × ℕ //
        j.2.2 < floorCut(s, order(χ j.1, shift(a, j.2.1)))}
      let η := fun j : J ↦ spectralZeroJet (χ j.val.1) 0 j.val.2.1 j.val.2.2
      let hI := le_rfl (a := (0 : ℝ))
      let hs₀ := le_of_lt (zero_lt_one.trans hs)
      let Q := spectralSobolevQuotient F a hI hs₀
      let D := spectralSobolevDualEmbedding F a hI hs₀
      Countable J ∧ ∃ (h : ∀ j, MemLp (η j) 2 (lineWeight(F, s)))
        (x : J → Q) (Λ : J → StrongDual ℂ Q), IsSpectralMarkushevichBasis x Λ ∧
        (∀ j, D (Λ j) = (h j).toLp (η j)) ∧ IsNormalizedSpectralFamily x

/-- Paper: Remark 10.2.1.5, p. 444. Use the rational trivial component
at a = 1/2 and s = 2. For close simple zeta zeros the two evaluation
vectors approach one another in the dual norm. A vector pairing to one
with the first and zero with the second has norm at least the reciprocal
of their distance. The required primal bound fails. -/
theorem Printed.spectralLineMarkushevichBasis_primal_normalized_false :
    ¬ Printed.spectralLineMarkushevichBasis_primal_normalized := by
  intro hall
  apply Printed.spectralLineMarkushevichBasis_false
  intro F _ _ χ hχ a s hs
  obtain ⟨hc, h, x, Λ, hb, hΛ, _⟩ := hall F χ hχ a s hs
  exact ⟨hc, h, x, Λ, hb, hΛ⟩

/-- Paper: Theorem 10.2.2.1, p. 446. The jets indexed by the printed
interior and boundary multiplicities belong to the reciprocal strip space
and are the functionals of a Markushevich basis in any enumeration. -/
def Printed.spectralStripMarkushevichBasis : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice χ →
    ∀ (a α s : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s),
      let J := {j : PontryaginDual C₁(F) × ℝ × ℝ × ℕ //
        j.2.2.2 < stripFloor(α, s, j.2.1, order(χ j.1, shift(a + j.2.1, j.2.2.1)))}
      let η := fun j : J ↦ spectralZeroJet (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2
      let hI := (neg_nonpos.mpr hα).trans hα
      let Q := spectralSobolevQuotient F a hI hs
      let D := spectralSobolevDualEmbedding F a hI hs
      Countable J ∧ ∃ (h : ∀ j, MemLp (η j) 2 (weight(F, α, s)))
        (x : J → Q) (Λ : J → StrongDual ℂ Q), IsSpectralMarkushevichBasis x Λ ∧
        ∀ j, D (Λ j) = (h j).toLp (η j)

/-- Paper: Theorem 10.2.2.1, p. 446. On the singleton strip with s = 1
a Riemann zeta zero supplies a zeroth jet with divergent squared norm. -/
theorem Printed.spectralStripMarkushevichBasis_false :
    ¬ Printed.spectralStripMarkushevichBasis := by
  intro hall
  apply Printed.spectralLineJet_memLp_false
  intro F _ _ χ hχ a s hs ω t k hk
  let h := (hall F χ hχ a 0 s le_rfl (zero_lt_one.trans hs).le).2.choose
  exact h ⟨(ω, 0, t, k), by simpa using hk⟩

/-- Paper: Theorem 10.2.2.1 and (10.2.2.5)–(10.2.2.6), p. 446.
The printed floor cutoff on the boundary and the full cutoff in the interior
are asserted to produce elements of the reciprocal strip space. -/
def Printed.spectralStripJet_memLp : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice χ →
    ∀ (a α s : ℝ), 0 ≤ α → 0 ≤ s → ∀ (ω : PontryaginDual C₁(F)) (b t : ℝ) (k : ℕ),
    let N := order(χ ω, shift(a + b, t))
    ((b = -α ∨ b = α) ∧ k < min N (Nat.floor ((s - 1) / 2 + 1)) ∨
      b ∈ Ioo (-α) α ∧ k < N) →
    MemLp (spectralZeroJet (χ ω) b t k) 2 (weight(F, α, s))

/-- Paper: Theorem 10.2.2.1 and (10.2.2.5), p. 446. Take F = ℚ,
the trivial character, s = 1, α = b = 0 and a+it the first nontrivial
Riemann zeta zero with positive ordinate. The printed cutoff includes k = 0.
Its squared norm has a 1/|x| tail in log coordinates. -/
theorem Printed.spectralStripJet_memLp_false : ¬ Printed.spectralStripJet_memLp := by
  intro hall
  apply Printed.spectralLineJet_memLp_false
  intro F _ _ χ hχ a s hs ω t k hk
  apply hall F χ hχ a 0 s le_rfl (zero_lt_one.trans hs).le ω 0 t k
  exact Or.inl ⟨Or.inr rfl, by simpa using hk⟩

/-- Paper: Proposition 10.2.2.2, pp. 446–447. The annulus uses the
reciprocal strip norm and the final open ball uses the negative line norm.
The ordinate is required to occur on the a-line as printed in (2). The
displacement in the displayed family is constrained by the multiplicity
at a+b+it, using the two cases of the definition on the same page. -/
def Printed.spectralStripJet_annulus_and_noncontainment : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice χ →
    ∀ (a α s : ℝ), 0 ≤ α → 1 < s →
      let J := {j : PontryaginDual C₁(F) × ℝ × ℝ × ℕ //
        0 < order(χ j.1, shift(a, j.2.2.1)) ∧
        j.2.2.2 < stripFloor(α, s, j.2.1, order(χ j.1, shift(a + j.2.1, j.2.2.1)))}
      let η := fun j : J ↦ spectralZeroJet (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2
      ∃ C : ℝ, 0 < C ∧
        (∀ j, ∃ h : MemLp (η j) 2 (weight(F, α, s)), C⁻¹ ≤ ‖h.toLp (η j)‖ ∧ ‖h.toLp (η j)‖ ≤ C) ∧
        ¬ (∀ j, ∃ h : MemLp (η j) 2 (weight(F, 0, s)), ‖h.toLp (η j)‖ < C⁻¹)

/-- Paper: Proposition 10.2.2.2, pp. 446–447. In ℚ take a = 2, s = 2
and α = 0. The family is empty, so it is contained in every open ball. -/
theorem Printed.spectralStripJet_annulus_and_noncontainment_false :
    ¬ Printed.spectralStripJet_annulus_and_noncontainment := by
  intro hall
  obtain ⟨χ, hχ⟩ := exists_spectralBasepointChoice ℚ
  obtain ⟨_, _, _, hn⟩ := hall ℚ χ hχ 2 0 2 (by norm_num) (by norm_num)
  apply hn
  intro j
  have hj := j.property.1
  let z := shift((2 : ℝ), j.val.2.2.1)
  have hz : 1 < z.re := by norm_num [z]
  have hval : continuedCompletedHeckeL (χ j.val.1) z ≠ 0 := by
    rw [show continuedCompletedHeckeL (χ j.val.1) z = completedHeckeL (χ j.val.1) ⟨z, hz⟩ from
      (continuedCompletedHeckeL_spec (χ j.val.1)).2 ⟨z, hz⟩]
    exact mul_ne_zero (heckeGammaFactor_ne_zero_of_re_pos (χ j.val.1) (zero_lt_one.trans hz))
      (finiteHeckeL_ne_zero_of_one_lt_re (χ j.val.1) ⟨z, hz⟩)
  have horder := ((continuedCompletedHeckeL_spec (χ j.val.1)).1 (mem_univ z)).meromorphicOrderAt_eq_zero_iff.mpr hval
  simp [z] at horder
  simp [horder] at hj

/-- Paper: Proposition 10.2.2.2, p. 447. The asserted noncontainment in an
open ball is specialized to the allowed singleton interval, where the
repeated boundary reference and the stated ambient line norm both apply. -/
def Printed.spectralStripJet_not_subset_ball_singleton : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice χ →
    ∀ (a s : ℝ), 1 < s → ∃ C : ℝ, 0 < C ∧
    ¬ (∀ (ω : PontryaginDual C₁(F)) (t : ℝ) (k : ℕ),
      k < min (order(χ ω, shift(a, t))) (Nat.floor ((s - 1) / 2 + 1)) →
      ∃ h : MemLp (spectralZeroJet (χ ω) 0 t k) 2 (weight(F, 0, s)),
        ‖h.toLp (spectralZeroJet (χ ω) 0 t k)‖ < C⁻¹)

/-- Paper: Proposition 10.2.2.2, p. 447. Take F = ℚ, a = 2, s = 2 and
I = {0}. On that strip every Hecke L-function is zero-free, so the empty
family is contained in every open ball. -/
theorem Printed.spectralStripJet_not_subset_ball_singleton_false :
    ¬ Printed.spectralStripJet_not_subset_ball_singleton := by
  intro hall
  obtain ⟨χ, hχ⟩ := exists_spectralBasepointChoice ℚ
  obtain ⟨_, _, hn⟩ := hall ℚ χ hχ 2 2 (by norm_num)
  apply hn
  intro ω t k hk
  let z := shift((2 : ℝ), t)
  have hz : 1 < z.re := by norm_num [z]
  have hval : continuedCompletedHeckeL (χ ω) z ≠ 0 := by
    rw [show continuedCompletedHeckeL (χ ω) z = completedHeckeL (χ ω) ⟨z, hz⟩ from
      (continuedCompletedHeckeL_spec (χ ω)).2 ⟨z, hz⟩]
    exact mul_ne_zero (heckeGammaFactor_ne_zero_of_re_pos (χ ω) (zero_lt_one.trans hz))
      (finiteHeckeL_ne_zero_of_one_lt_re (χ ω) ⟨z, hz⟩)
  have horder := ((continuedCompletedHeckeL_spec (χ ω)).1 (mem_univ z)).meromorphicOrderAt_eq_zero_iff.mpr hval
  simp [z] at horder
  simp [horder] at hk

/-- Paper: Corollary 10.2.2.3, p. 447. The printed index requires an
ordinate from the a-line. The conclusion identifies the normalized family
in the reciprocal strip space and also locates the annihilator in the negative line space. -/
def Printed.spectralStripMarkushevichBasis_normalized : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice χ →
    ∀ (a α s : ℝ) (hα : 0 ≤ α) (hs : 1 < s),
      let J := {j : PontryaginDual C₁(F) × ℝ × ℝ × ℕ //
        0 < order(χ j.1, shift(a, j.2.2.1)) ∧
        j.2.2.2 < stripFloor(α, s, j.2.1, order(χ j.1, shift(a + j.2.1, j.2.2.1)))}
      let η := fun j : J ↦ spectralZeroJet (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2
      let hI := (neg_nonpos.mpr hα).trans hα
      let hs₀ := le_of_lt (zero_lt_one.trans hs)
      let Q := spectralSobolevQuotient F a hI hs₀
      let D := spectralSobolevDualEmbedding F a hI hs₀
      Countable J ∧ ∃ (h : ∀ j, MemLp (η j) 2 (weight(F, α, s)))
        (x : J → Q) (Λ : J → StrongDual ℂ Q), IsSpectralMarkushevichBasis x Λ ∧
        (∀ j, D (Λ j) = (h j).toLp (η j)) ∧ IsNormalizedSpectralFamily (fun j ↦ D (Λ j)) ∧
        (∀ L : StrongDual ℂ Q, ∃ v : Lp ℂ 2 (lineWeight(F, s)),
          (v : C𝔽(F) → ℂ) =ᵐ[ideleClassTamagawaMeasure F] (D L : C𝔽(F) → ℂ))

/-- Paper: Corollary 10.2.2.3, p. 447. For ℚ at a = α = s = 2 the
a-line has no zeros. A nontrivial critical-line Riemann zero with ordinate γ
supplies a nonzero quotient functional: the jet with b = -3/2 and t = γ
is strip-integrable in squared norm and vanishes on polar-free weighted theta
tests by the forward zeta integral factorization. An empty family cannot span
this dual. -/
theorem Printed.spectralStripMarkushevichBasis_normalized_false :
    ¬ Printed.spectralStripMarkushevichBasis_normalized := by
  intro hall
  apply Printed.spectralLineJet_memLp_false
  intro F _ _ χ hχ a s hs ω t k hk
  let h := (hall F χ hχ a 0 s le_rfl hs).2.choose
  exact h ⟨(ω, 0, t, k), Nat.zero_lt_of_lt (hk.trans_le (min_le_left _ _)), by simpa using hk⟩

/-- Paper: Theorem 10.2.1.1, proof after (10.2.1.7), p. 441.
As printed: the exponential-decay topology is generated by the seminorms
with weights exp(−m |log t|) on the Euler derivatives. In the library's
logarithmic coordinates the Euler derivative becomes the ordinary derivative.
See `existsUnique_spectralLineTestCompletion` and ERRATA F153. -/
def Printed.spectralLineTestTopology : Prop :=
  let E := PositiveRealExponentialDecay (Set.univ : Set ℝ)
  ∃ p : SeminormFamily ℂ E (ℕ × ℕ), WithSeminorms p ∧
    ∀ (m n : ℕ) (f : E), p (m, n) f =
      ⨆ x : ℝ, Real.exp (-(m : ℝ) * |x|) * ‖iteratedDeriv n f.val x‖

open scoped ContDiff in
/-- Paper: Theorem 10.2.1.1, proof after (10.2.1.7), p. 441.
In x = log t take a nonzero smooth bump h supported in (0, 1) and the
profiles fⱼ(x) = exp(−j/2) h(x − j). Every printed seminorm tends to zero,
since its weight is at most one. The genuine topology includes the zeroth
Schwartz seminorm after the exp(x) twist, which grows as exp(j/2). -/
theorem Printed.spectralLineTestTopology_false : ¬ Printed.spectralLineTestTopology := by
  rintro ⟨p, hp, hval⟩
  let E := PositiveRealExponentialDecay (univ : Set ℝ)
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  let h (x : ℝ) : ℂ := b x
  have hc : HasCompactSupport h := b.hasCompactSupport.comp_left Complex.ofReal_zero
  have hd : ContDiff ℝ ∞ h := Complex.ofRealCLM.contDiff.comp b.contDiff
  let u := hc.toSchwartzMap hd
  let f (t : ℝ) : E := ⟨fun x ↦ h (x - t),
    mem_logExponentialDecaySubmodule_of_hasCompactSupport univ
      (by
        have ht := hc.comp_homeomorph (Homeomorph.addRight (-t))
        change HasCompactSupport (fun x ↦ h (x + -t)) at ht
        simpa only [sub_eq_add_neg] using ht)
      (hd.comp (contDiff_id.sub contDiff_const))⟩
  have hb : Bornology.IsVonNBounded ℂ (range f) := by
    apply hp.isVonNBounded_iff_seminorm_bounded.mpr
    rintro ⟨m,n⟩
    let C := SchwartzMap.seminorm ℂ 0 n u
    refine ⟨C + 1, by positivity, ?_⟩
    rintro _ ⟨t, rfl⟩
    rw [hval]
    apply lt_of_le_of_lt (ciSup_le fun x ↦ ?_) (lt_add_one C)
    have hw : Real.exp (-(m : ℝ) * |x|) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg m)) (abs_nonneg _))
    change _ * ‖iteratedDeriv n (fun z ↦ h (z - t)) x‖ ≤ C
    rw [iteratedDeriv_comp_sub_const]
    apply (mul_le_of_le_one_left (norm_nonneg _) hw).trans
    rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ u n (x - t)
  obtain ⟨T, -, hT⟩ := positiveRealExponentialDecay_continuous_inclusion univ (mem_univ (0 : ℝ))
  obtain ⟨R, hR, hbound⟩ := (schwartz_withSeminorms ℂ ℝ ℂ).isVonNBounded_iff_seminorm_bounded.mp
    (hb.image T) (1, 0)
  have hlt := hbound (T (f R)) ⟨f R, ⟨R, rfl⟩, rfl⟩
  have hle := SchwartzMap.norm_pow_mul_le_seminorm ℂ (T (f R)) 1 R
  have hx : T (f R) R = 1 := by
    rw [hT]
    change (b (R - R) : ℂ) = 1
    rw [sub_self, b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)]
    rfl
  rw [hx, norm_one, mul_one, pow_one, Real.norm_eq_abs, abs_of_pos hR] at hle
  exact (not_lt_of_ge hle) hlt

section BandProjection

set_option maxSynthPendingDepth 3

attribute [local instance] instIdeleClassBorelSpaceSec1 instIdeleClassT2Sec1
  instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1 instIdeleClassHaarMeasureSec1

local instance instDualMeasurableSpaceSec2Printed (F : Type*) [Field F] [NumberField F] :
    MeasurableSpace (PontryaginDual C𝔽(F)) := borel _

/-- Paper: Theorem 10.2.1.1, proof following (10.2.1.10), p. 443.
As printed: each in-band jet is in the range of the continuous adjoint of
the quotient band projection. This is the inclusion of the claimed spanning
family in the adjoint range. The band uses the characters χ |·|ⁱˣ
specified on p. 442(3). See `spectralLineIsotype_bandProjections` and ERRATA F155. -/
def Printed.spectralLineIsotype_bandAdjoint_contains_jets : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (basepoint : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)),
    IsSpectralBasepointChoice basepoint →
    ∀ (ω : PontryaginDual C₁(F)) (a s : ℝ) (hs : 1 < s) (m : ℕ)
      (ν : Measure (PontryaginDual C𝔽(F))),
    let μ := ideleClassTamagawaMeasure F
    ∀ hν : IsLCAPlancherelMeasure μ ν,
      let χ := basepoint ω
      let hI := le_rfl (a := (0 : ℝ))
      let hs₀ := le_of_lt (zero_lt_one.trans hs)
      let normMap : C𝔽(F) →ₜ* ℝ≥0ˣ :=
        ⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩
      let E := actionIsotype ((hardySobolevTranslation μ normMap 0 0 s hI hs₀).comp
        (ideleClassNorm F).ker.subtype) ω
      let N := (globalThetaSobolev F a hI hs₀).comap E.subtype
      let Q := spectralSobolevIsotypeQuotient F a hI hs₀ ω
      let U := (lcaFourier_unitary μ ν hν).exists.choose
      let B : Set Q := {q | ∃ f : E, q = N.mkQ f ∧ ∃ u : Lp ℂ 2 μ,
        (u : C𝔽(F) → ℂ) =ᵐ[μ] (f.val : C𝔽(F) → ℂ) ∧
          ∀ᵐ ψ ∂ν, ψ ∉ modulatedFrequencyBand normMap χ (-(m : ℝ)) m → U u ψ = 0}
      ∀ P : Q →L[ℂ] Q, Set.range P = closure B →
        (∀ q y, y ∈ closure B → ‖q - P q‖ ≤ ‖q - y‖) →
        ∀ (t : ℝ) (k : ℕ), t ∈ Icc (-(m : ℝ)) m →
          k < floorCut(s, order(χ, shift(a, t))) →
          ∃ d : StrongDual ℂ Q, d ∈ Set.range (P.precomp ℂ) ∧
            ∀ f : E,
              let integrand := fun g ↦ f.val g * spectralZeroJet χ 0 t k g
              Integrable integrand μ ∧ d (N.mkQ f) = ∫ g, integrand g ∂μ

/-- Paper: Theorem 10.2.1.1, proof following (10.2.1.10), p. 443.
For F = ℚ and the trivial character, take a = 1/2, s = 2, m = 15, and
the zeroth evaluations at the zeta ordinates t = 14.1347… and u = 21.0220….
Both vanish on the weighted theta image by forward Mellin factorization.
The evaluation at u annihilates the band image, so it is in the kernel of
the adjoint. Its dual inner product with the evaluation at t is
Mπ exp(−|t − u|) ≠ 0, where M is the norm-one mass. This excludes the
evaluation at t from the adjoint range of the orthogonal projection. -/
theorem Printed.spectralLineIsotype_bandAdjoint_contains_jets_false :
    ¬ Printed.spectralLineIsotype_bandAdjoint_contains_jets := by sorry

end BandProjection

end RiemannMasullo
