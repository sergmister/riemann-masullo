module

public import RiemannMasullo.Research.StripNuclearity.NumberFieldDiagonal
public import RiemannMasullo.Research.StripNuclearity.Projective
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-! # Physical localization of traces at finite theta bands

A compact physical cutoff gives a nuclear convolution with trace zero when the test
vanishes at the identity. Monotone orthogonal projection onto a generating sequence
of theta bands then recovers the negative localized spectral trace. Exhausting the
physical support is a second limit. The last assertion selects cofinal bandwidths
along which the two limits are attained together.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing TensorProduct Topology

namespace RiemannMasullo.PhysicalBandTrace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]

/-- Left multiplication of a nuclear endomorphism by a bounded operator. -/
def leftProduct (A : H →L[ℂ] H) (T : nuclearEndomorphisms H) : nuclearEndomorphisms H :=
  ⟨A * T.val, mul_mem_nuclearEndomorphisms_left A T⟩

/-- Right multiplication of a nuclear endomorphism by a bounded operator. -/
def rightProduct (T : nuclearEndomorphisms H) (A : H →L[ℂ] H) : nuclearEndomorphisms H :=
  ⟨T.val * A, mul_mem_nuclearEndomorphisms_right A T⟩

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

/-- A uniformly bounded strongly null family kills a nuclear operator in trace norm. -/
private theorem traceNorm_left_null
    (Q : ι → H →L[ℂ] H) (hQ : ∀ x, Tendsto (fun R ↦ Q R x) atTop (𝓝 0))
    (hbound : ∀ R, ‖Q R‖ ≤ 2) (T : nuclearEndomorphisms H) :
    Tendsto (fun R ↦ traceNorm ⟨Q R * T.val, mul_mem_nuclearEndomorphisms_left (Q R) T⟩) atTop (𝓝 0) := by
  let product (R : ι) (A : nuclearEndomorphisms H) : nuclearEndomorphisms H :=
    ⟨Q R * A.val, mul_mem_nuclearEndomorphisms_left (Q R) A⟩
  let : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
  have hcore := (traceNorm_normedSpaceCore (H := H)).toCore
  have hnonneg (A : nuclearEndomorphisms H) : 0 ≤ traceNorm A := hcore.norm_nonneg A
  refine Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
  obtain ⟨z, hz⟩ := exists_tensorToFiniteRank_traceNorm_sub_lt T (by positivity : 0 < ε / 4)
  let F : nuclearEndomorphisms H :=
    ⟨tensorToFiniteRank z, tensorToFiniteRank_mem_nuclearEndomorphisms z⟩
  obtain ⟨_, hF⟩ := tendsto_traceNorm_mul_finiteRank Q hQ F.val (finiteDimensional_range_tensorToFiniteRank z)
  have hF' : Tendsto (fun R ↦ traceNorm (product R F)) atTop (𝓝 0) := hF
  filter_upwards [Metric.tendsto_nhds.mp hF' (ε / 2) (half_pos hε)] with R hR
  have hsplit : product R T = product R (T - F) + product R F := by
    apply Subtype.ext
    simp [product, mul_sub]
  have hle : traceNorm (product R (T - F)) ≤ 2 * traceNorm (T - F) :=
    (traceNorm_mul_left_le (Q R) (T - F)).trans
      (mul_le_mul_of_nonneg_right (hbound R) (hnonneg (T - F)))
  have htriangle : traceNorm (product R T) ≤
      traceNorm (product R (T - F)) + traceNorm (product R F) := by
    rw [hsplit]
    exact hcore.norm_triangle _ _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hnonneg (product R F))] at hR
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hnonneg (product R T))]
  change traceNorm (T - F) < ε / 4 at hz
  linarith

/-- Nuclear traces are continuous under bounded strong convergence of contractions. -/
theorem tendsto_trace_leftProduct (U : ι → H →L[ℂ] H) (V : H →L[ℂ] H)
    (hU : ∀ x, Tendsto (fun i ↦ U i x) atTop (𝓝 (V x)))
    (hU₁ : ∀ i, ‖U i‖ ≤ 1) (hV₁ : ‖V‖ ≤ 1) (T : nuclearEndomorphisms H) :
    Tendsto (fun i ↦ hilbertTrace (leftProduct (U i) T)) atTop
      (𝓝 (hilbertTrace (leftProduct V T))) := by
  let D (i : ι) := U i - V
  have hD (x : H) : Tendsto (fun i ↦ D i x) atTop (𝓝 0) := by
    simpa [D] using (hU x).sub (tendsto_const_nhds : Tendsto (fun _ : ι ↦ V x) atTop (𝓝 (V x)))
  have hD₁ (i : ι) : ‖D i‖ ≤ 2 := (norm_sub_le ..).trans (by linarith [hU₁ i])
  have hn := traceNorm_left_null D hD hD₁ T
  have ht : Tendsto (fun i ↦ ‖hilbertTrace (leftProduct (D i) T)‖) atTop (𝓝 0) :=
    squeeze_zero (fun _ ↦ norm_nonneg _) (fun i ↦ norm_hilbertTrace_le (leftProduct (D i) T)) hn
  obtain ⟨tr, htr⟩ := hilbertTrace_linear (H := H)
  have heq (i : ι) : hilbertTrace (leftProduct (U i) T) - hilbertTrace (leftProduct V T) =
      hilbertTrace (leftProduct (D i) T) := by
    have hd : leftProduct (D i) T = leftProduct (U i) T - leftProduct V T :=
      Subtype.ext (sub_mul ..)
    rw [hd, ← htr, ← htr, ← htr, map_sub]
  exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [heq] using ht)

/-- The trace of a nuclear operator after increasing band projections converges to
its trace after projection onto the closed span of the bands. -/
theorem tendsto_bandTrace (T : nuclearEndomorphisms H) (U : ι → Submodule ℂ H)
    [∀ i, (U i).HasOrthogonalProjection] (hu : Monotone U)
    (K : Submodule ℂ H) [K.HasOrthogonalProjection] (hK : (⨆ i, U i).topologicalClosure = K) :
    Tendsto (fun i ↦ hilbertTrace (rightProduct T (U i).starProjection)) atTop
      (𝓝 (hilbertTrace (rightProduct T K.starProjection))) := by
  let : CompleteSpace (⨆ i, U i).topologicalClosure :=
    (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have h (x : H) := Submodule.starProjection_tendsto_closure_iSup U hu x
  have hs (x : H) : Tendsto (fun i ↦ (U i).starProjection x) atTop (𝓝 (K.starProjection x)) := by
    simpa only [hK] using h x
  have hh := tendsto_trace_leftProduct (fun i ↦ (U i).starProjection) K.starProjection hs
    (fun i ↦ (U i).starProjection_norm_le) K.starProjection_norm_le T
  simpa only [leftProduct, rightProduct, spectralRestriction_cyclic] using hh

/-- If the full localized trace vanishes, the limit of its geometric band traces is
minus its trace after the complementary spectral projection. -/
theorem tendsto_bandTrace_neg_orthogonal (T : nuclearEndomorphisms H) (hT : hilbertTrace T = 0)
    (U : ι → Submodule ℂ H) [∀ i, (U i).HasOrthogonalProjection] (hu : Monotone U)
    (K : Submodule ℂ H) [K.HasOrthogonalProjection] (hK : (⨆ i, U i).topologicalClosure = K) :
    Tendsto (fun i ↦ hilbertTrace (rightProduct T (U i).starProjection)) atTop
      (𝓝 (-hilbertTrace (rightProduct T K.orthogonal.starProjection))) := by
  have hid : K.starProjection + K.orthogonal.starProjection = 1 := by
    ext x
    exact K.starProjection_add_starProjection_orthogonal x
  have hsplit : rightProduct T K.starProjection + rightProduct T K.orthogonal.starProjection = T := by
    apply Subtype.ext
    change T.val * K.starProjection + T.val * K.orthogonal.starProjection = T.val
    rw [← mul_add, hid, mul_one]
  obtain ⟨tr, htr⟩ := hilbertTrace_linear (H := H)
  have hneg : hilbertTrace (rightProduct T K.starProjection) =
      -hilbertTrace (rightProduct T K.orthogonal.starProjection) := by
    apply eq_neg_of_add_eq_zero_left
    rwa [← htr, ← htr, ← map_add, hsplit, htr]
  rw [← hneg]
  exact tendsto_bandTrace T U hu K hK

/-- An iterated limit admits bandwidth thresholds. Every selection above those
thresholds at the integer cutoff radii has the same limit. -/
theorem exists_bandThresholds {f : ℕ → ℝ → ℂ} {g : ℕ → ℂ} {v : ℂ}
    (hf : ∀ n, Tendsto (f n) atTop (𝓝 (g n))) (hg : Tendsto g atTop (𝓝 v)) :
    ∃ b : ℕ → ℝ, Tendsto b atTop atTop ∧
      ∀ B : ℕ → ℝ, (∀ᶠ n in atTop, b n ≤ B n) →
        Tendsto (fun n ↦ f n (B n)) atTop (𝓝 v) := by
  have h (n : ℕ) := eventually_atTop.1 <| Metric.tendsto_nhds.mp (hf n)
    (1 / ((n : ℝ) + 1)) (by positivity)
  choose c hc using h
  let b (n : ℕ) := max (n : ℝ) (c n)
  refine ⟨b, tendsto_atTop_mono (fun n ↦ le_max_left ..) tendsto_natCast_atTop_atTop, ?_⟩
  intro B hB
  have he : Tendsto (fun n ↦ f n (B n) - g n) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ tendsto_one_div_add_atTop_nhds_zero_nat
    filter_upwards [hB] with n hn
    simpa only [← dist_eq_norm] using (hc n (B n) ((le_max_right ..).trans hn)).le
  simpa only [sub_add_cancel, zero_add] using he.add hg

section ModulatedGroup

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G]

/-- The full trace of a truncated test action vanishes when its convolution kernel
vanishes at the identity of the modulated group. -/
private theorem cutoff_testAction_zero (μ : Measure G) [μ.IsHaarMeasure] (m : G →ₜ* ℝ≥0ˣ)
    (hm : IsModulation m) (hsur : Surjective m) (a b s : ℝ) (hab : a ≤ b) (hs : 0 ≤ s)
    (φ : BruhatCompactSupport G) (hφ : φ.val 1 = 0) {R ε : ℝ} {ρ : G → ℝ}
    (hρ : IsModulatedCutoff m R ε ρ) (hband : 0 < R⁻¹ + ε ∧ R⁻¹ + ε < R - ε) :
    let l := fun x : G ↦ Real.log ((m x).val : ℝ)
    let ν := μ.withDensity fun x ↦ ENNReal.ofReal (intervalSobolevDensity a b s (l x))
    let T := (modulatedCutoffOperator m ν hρ).comp (hardySobolevTestAction μ m a b s hab hs φ)
    ∃ h : IsNuclearOperator T, hilbertTrace (H := CompactIntervalSobolev μ l a b s) ⟨T, h⟩ = 0 := by
  intro l ν T
  have hφs := (mem_bruhatSmoothSubmodule_iff _).mp φ.property.1
  have hc := continuous_of_bruhatSmooth hφs
  have hb := hc.bounded_above_of_compact_support (show HasCompactSupport φ.val from φ.property.2)
  have hconv := hardySobolevConvolution_eq_testAction μ m a b s hab hs φ hc.aemeasurable hb
  obtain ⟨hn, -, ht⟩ := truncatedHardySobolevConvolution_trace μ m a b s hab hs φ.val
    hc.aemeasurable φ.property.2 hb hm hsur hφs hρ hband
  change ∃ h : IsNuclearOperator ((modulatedCutoffOperator m ν hρ).comp
    (hardySobolevTestAction μ m a b s hab hs φ)), hilbertTrace ⟨_, h⟩ = 0
  rw [← hconv]
  refine ⟨hn, ?_⟩
  simpa only [hφ, mul_zero, integral_zero] using ht

end ModulatedGroup

section Physical

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]
variable {α s : ℝ}

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" => (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "W" => CompactIntervalSobolev μ𝔽 (logIdeleClassNorm F) (-α) α s
local notation "ν" => (μ𝔽).withDensity fun g ↦
  ENNReal.ofReal (intervalSobolevDensity (-α) α s (logIdeleClassNorm F g))
local notation "M(" hρ ")" => modulatedCutoffOperator m𝔽 ν hρ
local notation "A(" hα ", " hs ", " φ ")" =>
  hardySobolevTestAction μ𝔽 m𝔽 (-α) α s (neg_le_self hα) hs φ
local notation "K(" hα ", " hs ")" => globalThetaSobolev F (1/2) (neg_le_self hα) hs
local notation "P(" hα ", " hs ")" => spectralProjection (F := F) (1/2) hα hs

/-- A physical cutoff of adelic convolution is nuclear and has zero trace when the test
vanishes at the identity. This includes tests supported at positive log norm. -/
theorem physicalCutoff_trace_zero (hα : 0 ≤ α) (hs : 0 ≤ s)
    (φ : BruhatCompactSupport C𝔽) (hφ : φ.val 1 = 0) {R ε : ℝ} {ρ : C𝔽 → ℝ}
    (hρ : IsModulatedCutoff m𝔽 R ε ρ) (hband : 0 < R⁻¹ + ε ∧ R⁻¹ + ε < R - ε) :
    ∃ h : IsNuclearOperator ((M(hρ)).comp (A(hα, hs, φ))), hilbertTrace (H := W) ⟨_, h⟩ = 0 := by
  have hm : IsModulation m𝔽 := ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
  have hsur : Surjective m𝔽 := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.2.2.2.1
  exact cutoff_testAction_zero μ𝔽 m𝔽 hm hsur (-α) α s (neg_le_self hα) hs φ hφ hρ hband

/-- Paper: §12.3, p. 514. For an increasing family generating the full theta
space in the actual strip, the localized band traces converge to the negative localized
spectral trace. Exhausting the physical cutoffs gives the negative trace of convolution
after the ambient spectral projection. At integer physical radii all sufficiently large
choices of bandwidth, with a threshold depending on the radius, give this same limit.

Deviation: The printed section contains only a heading and footnote. This independent
argument assumes that the closed band span equals the global theta space. It selects
bandwidths with thresholds that can depend on the physical radius. -/
theorem exists_physicalBandTrace (hα : 0 ≤ α) (hs : 1 < s)
    (φ : BruhatCompactSupport C𝔽) (hφ : φ.val 1 = 0)
    (U : ℝ → Submodule ℂ W) [∀ B, (U B).HasOrthogonalProjection] (hu : Monotone U)
    (hgen : (⨆ B, U B).topologicalClosure = K(hα, zero_le_one.trans hs.le))
    (ε : ℝ → ℝ) (ρ : ℝ → C𝔽 → ℝ)
    (hε : Tendsto (fun R ↦ ε R * R) atTop (𝓝 0))
    (hρ : ∀ᶠ R in atTop, IsModulatedCutoff m𝔽 R (ε R) (ρ R) ∧
      0 < R⁻¹ + ε R ∧ R⁻¹ + ε R < R - ε R) :
    let hs₀ := zero_le_one.trans hs.le
    let A := A(hα, hs₀, φ)
    let P := P(hα, hs₀)
    ∃ (hAP : IsNuclearOperator (A.comp P)) (T : ℝ → nuclearEndomorphisms W),
      (∀ R (hc : IsModulatedCutoff m𝔽 R (ε R) (ρ R)), 0 < R⁻¹ + ε R ∧ R⁻¹ + ε R < R - ε R →
        (T R).val = (M(hc)).comp A) ∧
      (∀ R, hilbertTrace (T R) = 0) ∧
      (∀ R, Tendsto (fun B ↦ hilbertTrace (rightProduct (T R) (U B).starProjection)) atTop
        (𝓝 (-hilbertTrace (rightProduct (T R) P)))) ∧
      Tendsto (fun R ↦ -hilbertTrace (rightProduct (T R) P)) atTop
        (𝓝 (-hilbertTrace (H := W) ⟨A.comp P, hAP⟩)) ∧
      ∃ b : ℕ → ℝ, Tendsto b atTop atTop ∧
        ∀ B : ℕ → ℝ, (∀ᶠ n in atTop, b n ≤ B n) →
          Tendsto (fun n : ℕ ↦ hilbertTrace (rightProduct (T (n : ℝ)) (U (B n)).starProjection)) atTop
            (𝓝 (-hilbertTrace (H := W) ⟨A.comp P, hAP⟩)) := by
  classical
  intro hs₀ A P
  let valid (R : ℝ) := IsModulatedCutoff m𝔽 R (ε R) (ρ R) ∧
    0 < R⁻¹ + ε R ∧ R⁻¹ + ε R < R - ε R
  let L (R : ℝ) : W →L[ℂ] W := if h : valid R then M(h.1) else 0
  have hfam : ∃ C : ℝ → W →L[ℂ] W, (∀ R, ‖C R‖ ≤ 1) ∧
      (∀ x, Tendsto (fun R ↦ C R x) atTop (𝓝 x)) ∧
      ∀ R (hc : IsModulatedCutoff m𝔽 R (ε R) (ρ R)), C R = M(hc) := by
    with_unfolding_all exact exists_stronglyConvergent_modulatedCutoffOperators C𝔽 m𝔽 ν ε ρ hε hρ
  obtain ⟨C, hc₁, hc_lim, hc_eq⟩ := hfam
  have hL₁ (R : ℝ) : ‖L R‖ ≤ 1 := by
    dsimp only [L]
    split_ifs with h
    · rw [← hc_eq R h.1]
      exact hc₁ R
    · simp
  have hL (x : W) : Tendsto (fun R ↦ L R x) atTop (𝓝 x) := by
    apply (hc_lim x).congr'
    filter_upwards [hρ] with R hR
    simp only [L, dite_eq_left (show valid R from hR), hc_eq R hR.1]
  have hT (R : ℝ) : ∃ h : IsNuclearOperator ((L R).comp A), hilbertTrace (H := W) ⟨_, h⟩ = 0 := by
    by_cases hv : valid R
    · simpa only [L, dite_eq_left hv] using physicalCutoff_trace_zero (F := F) hα hs₀ φ hφ hv.1 hv.2
    · simp only [L, dite_eq_right hv]
      refine ⟨(nuclearEndomorphisms W).zero_mem, ?_⟩
      obtain ⟨tr, htr⟩ := hilbertTrace_linear (H := W)
      change hilbertTrace (0 : nuclearEndomorphisms W) = 0
      rw [← htr, map_zero]
  let T (R : ℝ) : nuclearEndomorphisms W := ⟨(L R).comp A, (hT R).choose⟩
  have hAP : IsNuclearOperator (A.comp P) :=
    (StripNuclearity.exists_projectiveKernel_iff (F := F) hα hs₀ _).mp
      (StripNuclearity.exists_numberField_projectiveKernel_comp_spectralProjection (F := F) hα hs φ)
  let S : nuclearEndomorphisms W := ⟨A.comp P, hAP⟩
  have hinner (R : ℝ) := tendsto_bandTrace_neg_orthogonal (T R) (hT R).choose_spec U hu _ hgen
  have houter : Tendsto (fun R ↦ -hilbertTrace (rightProduct (T R) P)) atTop (𝓝 (-hilbertTrace S)) := by
    have hn := tendsto_trace_leftProduct L (1 : W →L[ℂ] W) hL hL₁ ContinuousLinearMap.norm_id_le S
    have h₁ : leftProduct 1 S = S := Subtype.ext (one_mul _)
    have hcomp (R : ℝ) : leftProduct (L R) S = rightProduct (T R) P := Subtype.ext rfl
    simpa only [h₁, hcomp] using hn.neg
  exact ⟨hAP, T, fun R hc hb ↦ by simp only [T, L, dite_eq_left (show valid R from ⟨hc, hb⟩)],
    fun R ↦ (hT R).choose_spec, hinner, houter,
    exists_bandThresholds (fun n ↦ hinner (n : ℝ)) (houter.comp tendsto_natCast_atTop_atTop)⟩

end Physical

end RiemannMasullo.PhysicalBandTrace
