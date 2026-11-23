module

public import RiemannMasullo.Research.StripNuclearity.IdeleEigenConvolution
public import RiemannMasullo.Research.StripNuclearity.LiftedKernel

/-!
# Projective kernel of rational spectral convolution

Every compact Bruhat test on the rational idele classes is a finite sum of
norm-one character tests. Each test acts by a lifted, compactly supported
smooth convolution on the logarithmic line. Summing the projective tensors
of these finitely many projected operators gives the witness required at
(12.5.1.4), p. 520, for the rational field.
-/

@[expose] public noncomputable section
open Function Filter MeasureTheory NumberField Set Topology
open scoped NNReal ContDiff

namespace RiemannMasullo.StripNuclearity

set_option quotPrecheck false

attribute [local instance] uniformContinuousConstSMul_of_continuousConstSMul
attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "Kℚ" => (ideleClassNorm ℚ).ker
local notation "μℚ" => ideleClassTamagawaMeasure ℚ
local notation "mℚ" => (⟨ideleClassNorm ℚ, (isProperMap_ideleClassNorm ℚ).continuous⟩ : Cℚ →ₜ* ℝ≥0ˣ)
local notation "logNorm" => (fun x : Cℚ ↦ Real.log ((ideleClassNorm ℚ x).val : ℝ))

private theorem finite_projected_test_kernel {I D E X : Type*} [AddCommMonoid D] [Module ℂ D]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [AddCommMonoid X] [Module ℂ X]
    (J : X →ₗ[ℂ] (E →L[ℂ] E)) (A : D →ₗ[ℂ] (E →L[ℂ] E)) (P : E →L[ℂ] E)
    (S : Finset I) (F : I → D) (h : ∀ i ∈ S, ∃ x, J x = (A (F i)).comp P) :
    ∃ x, J x = (A (∑ i ∈ S, F i)).comp P := by
  have he : (A (∑ i ∈ S, F i)).comp P = ∑ i ∈ S, (A (F i)).comp P := by
    ext v
    rw [map_sum]
    simp only [ContinuousLinearMap.comp_apply, sum_apply]
  rw [he]
  change _ ∈ J.range
  exact J.range.sum_mem h

private theorem kernel_of_radial_factor {E W X T : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
    (O : X → (W →L[ℂ] W)) (A P : W →L[ℂ] W)
    (compact smooth profile : T → Prop) (lift : (E →L[ℂ] W) → Prop)
    (acts : T → (E →L[ℂ] E) → Prop)
    (hf : ∃ (p : T) (L : E →L[ℂ] W), compact p ∧ smooth p ∧ profile p ∧ lift L ∧
      ∀ B, acts p B → A = (L.comp B).comp L.adjoint)
    (hb : ∀ p, compact p → smooth p → ∃ B, acts p B)
    (hk : ∀ L, lift L → ∀ p, compact p → smooth p → ∀ B, acts p B →
      ∃ K, O K = (L.comp (B.comp L.adjoint)).comp P) :
    ∃ K, O K = A.comp P := by
  obtain ⟨p,L,hc,hd,_,hL,hA⟩ := hf
  obtain ⟨B,hB⟩ := hb p hc hd
  rw [hA B hB]
  exact hk L hL p hc hd B hB

private theorem exists_scalar_action {a b s : ℝ} (hab : a ≤ b) (hs : 0 ≤ s)
    (p : ℝ → ℂ) (hc : HasCompactSupport p) (hd : ContDiff ℝ (∞) p) :
    let E := CompactIntervalSobolev volume id a b s
    ∃ B : E →L[ℂ] E, ∀ f, ∀ᵐ x ∂volume, B f x = ∫ t : ℝ, p t * f (x - t) := by
  obtain ⟨B,hB⟩ := exists_scalar_weighted_convolution a b s hab hs p hd.continuous hc
  exact ⟨B,fun f ↦ (hB f).mono fun _ hx ↦ hx.2⟩

section NumberFields

variable {F : Type*} [Field F] [NumberField F]
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" => (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "ℓ" => (fun x : C𝔽 ↦ Real.log ((ideleClassNorm F x).val : ℝ))

/-- At any number field, a single angular character test has a projective kernel after
spectral projection at center 1/2. -/
theorem exists_projectiveKernel_comp_spectralProjection_of_angular_test
    {α s : ℝ} (ha : 0 ≤ α) (hs : 1 < s) (ξ : PontryaginDual C₁) (φ : BruhatCompactSupport C𝔽)
    (hφ : ∀ (k : C₁) (x : C𝔽), φ.val (k.val⁻¹ * x) = (ξ k : ℂ) * φ.val x) :
    let hs₀ := zero_le_one.trans hs.le
    ∃ K, sobolevProjectiveKernelOperator (F := F) ha hs₀ K =
      (hardySobolevTestAction μ𝔽 m𝔽 (-α) α s (neg_le_self ha) hs₀ φ).comp
        (spectralProjection (F := F) (1/2) ha hs₀) := by
  intro hs₀
  let χ := (exists_spectralBasepointChoice F).choose
  have hχ := (exists_spectralBasepointChoice F).choose_spec
  have ht (k : C₁) (x : C𝔽) : φ.val (k.val⁻¹ * x) = (χ ξ k.val : ℂ) * φ.val x := by
    have hk : χ ξ k.val = ξ k := DFunLike.congr_fun (hχ ξ) k
    rw [hk, hφ]
  let E := CompactIntervalSobolev volume id (-α) α s
  let W := CompactIntervalSobolev μ𝔽 ℓ (-α) α s
  let rep (L : E →L[ℂ] W) := ∀ f, (L f : C𝔽 → ℂ) =ᵐ[μ𝔽] fun x ↦ (χ ξ x : ℂ)⁻¹ * f (ℓ x)
  let acts (p : ℝ → ℂ) (B : E →L[ℂ] E) := ∀ f, ∀ᵐ x ∂volume, B f x = ∫ t : ℝ, p t * f (x - t)
  let W' := CompactIntervalSobolev μ𝔽 ℓ (-α) α s true
  let X := UniformSpace.Completion (ProjectiveTensor W' W)
  let O : X → (W →L[ℂ] W) := sobolevProjectiveKernelOperator (F := F) ha hs₀
  exact kernel_of_radial_factor (E := E) (W := W) (T := ℝ → ℂ) O
    (hardySobolevTestAction μ𝔽 m𝔽 (-α) α s (neg_le_self ha) hs₀ φ)
    (spectralProjection (F := F) (1/2) ha hs₀)
    HasCompactSupport (ContDiff ℝ (∞)) (fun p ↦ ∀ x, φ.val x = (χ ξ x : ℂ)⁻¹ * p (ℓ x)) rep acts
    (exists_ideleClass_eigenkernel_factorization (χ ξ) φ ht (neg_le_self ha) hs₀)
    (exists_scalar_action (neg_le_self ha) hs₀)
    (exists_projectiveKernel_projected_radial_lift (F := F) χ hχ ξ ha hs)

private theorem exists_projectiveKernel_of_finite_angular_decomposition
    {α s : ℝ} (ha : 0 ≤ α) (hs : 1 < s) (φ : BruhatCompactSupport C𝔽)
    (hφ : ∃ (S : Finset (PontryaginDual C₁)) (D : PontryaginDual C₁ → BruhatCompactSupport C𝔽),
      (∑ ξ ∈ S, D ξ) = φ ∧ ∀ ξ ∈ S, ∀ (k : C₁) x, (D ξ).val (k.val⁻¹ * x) = (ξ k : ℂ) * (D ξ).val x) :
    let hs₀ := zero_le_one.trans hs.le
    ∃ K, sobolevProjectiveKernelOperator (F := F) ha hs₀ K =
      (hardySobolevTestAction μ𝔽 m𝔽 (-α) α s (neg_le_self ha) hs₀ φ).comp
        (spectralProjection (F := F) (1/2) ha hs₀) := by
  intro hs₀
  let W := CompactIntervalSobolev μ𝔽 ℓ (-α) α s
  let j := (sobolevProjectiveKernelOperator (F := F) ha hs₀).toLinearMap
  let A : BruhatCompactSupport C𝔽 →ₗ[ℂ] (W →L[ℂ] W) :=
    hardySobolevTestAction μ𝔽 m𝔽 (-α) α s (neg_le_self ha) hs₀
  let P := spectralProjection (F := F) (1/2) ha hs₀
  obtain ⟨S,D,hD,hcov⟩ := hφ
  change ∃ K, j K = (A φ).comp P
  rw [← hD]
  exact finite_projected_test_kernel j A P S D (fun ξ hξ ↦
    exists_projectiveKernel_comp_spectralProjection_of_angular_test (F := F) ha hs ξ (D ξ) (hcov ξ hξ))

end NumberFields

/-- At center 1/2, convolution by any compact Bruhat test after the spectral
projection on the rational idele classes admits a projective Sobolev kernel.
The width can be zero, and every Sobolev order strictly greater than one is allowed. -/
theorem exists_rat_projectiveKernel_comp_spectralProjection {α s : ℝ} (ha : 0 ≤ α) (hs : 1 < s)
    (φ : BruhatCompactSupport Cℚ) :
    let hs₀ := (zero_le_one.trans hs.le)
    ∃ K, sobolevProjectiveKernelOperator (F := ℚ) ha hs₀ K =
      (hardySobolevTestAction μℚ mℚ (-α) α s (neg_le_self ha) hs₀ φ).comp
        (spectralProjection (F := ℚ) (1/2) ha hs₀) :=
  exists_projectiveKernel_of_finite_angular_decomposition (F := ℚ) ha hs φ
    (ratBruhatCompactSupport_finite_angular_decomposition φ)

end RiemannMasullo.StripNuclearity
