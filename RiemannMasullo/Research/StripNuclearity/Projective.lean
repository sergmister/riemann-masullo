module

public import RiemannMasullo.Ch10_TraceSpectral.Sec4b
public import RiemannMasullo.Research.PositiveStrip.Solution
public import RiemannMasullo.Research.StripNuclearity.FiniteCutoffs

/-!
# Projective kernels for convolution after the spectral projection

The reciprocal-weight tensor condition in the geometric diagonal identity can
be tested by approximating the Hilbert adjoint using finite sets of strip jets.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set UniformSpace
open scoped Topology NNReal NumberField.AdeleRing TensorProduct

namespace RiemannMasullo.StripNuclearity

set_option quotPrecheck false
attribute [local instance] uniformContinuousConstSMul_of_continuousConstSMul

section Tensor

private theorem projective_transport_surjective {Y X E : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup E] [NormedSpace ℂ E] (e : Y ≃ₗᵢ[ℂ] X) :
    let f := e.symm.toContinuousLinearEquiv.toContinuousLinearMap
    let i : ProjectiveTensor X E →L[ℂ] ProjectiveTensor Y E :=
      ⟨projectiveTensorMap f.toLinearMap (LinearMap.id : E →ₗ[ℂ] E),
        projectiveTensorMap_continuous f (ContinuousLinearMap.id ℂ E)⟩
    Surjective i.completion := by
  intro f i
  exact completedProjectiveTensorMap_surjective f (ContinuousLinearMap.id ℂ E)
    e.symm.toHomeomorph.isQuotientMap Topology.IsQuotientMap.id

private theorem exists_transported_tensor_iff {X E : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (e : StrongDual ℂ E ≃ₗᵢ[ℂ] X) (A : E →L[ℂ] E) :
    let f := e.symm.toContinuousLinearEquiv.toContinuousLinearMap
    let i : ProjectiveTensor X E →L[ℂ] ProjectiveTensor (StrongDual ℂ E) E :=
      ⟨projectiveTensorMap f.toLinearMap (LinearMap.id : E →ₗ[ℂ] E),
        projectiveTensorMap_continuous f (ContinuousLinearMap.id ℂ E)⟩
    (∃ K, completedProjectiveTensorToOperators (i.completion K) = A) ↔ IsNuclearOperator A := by
  intro f i
  rw [isNuclearOperator_iff_isBanachNuclear, isBanachNuclear_iff_mem_range]
  constructor
  · rintro ⟨K, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨z, hz⟩
    obtain ⟨K, hK⟩ := projective_transport_surjective (E := E) e z
    exact ⟨K, (congrArg (completedProjectiveTensorToOperators (E := E) (F := E)) hK).trans hz⟩

end Tensor

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" =>
  (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "logNorm" => (fun g : C𝔽 ↦ Real.log ((ideleClassNorm F g).val : ℝ))
local notation "W(" α ", " s ")" => CompactIntervalSobolev μ𝔽 logNorm (-α) α s
local notation "W'(" α ", " s ")" => CompactIntervalSobolev μ𝔽 logNorm (-α) α s true
local notation "I(" ha ")" => (neg_nonpos.mpr ha |>.trans ha)
local notation "T(" ha ", " hs ")" =>
  (modulatedIntervalSobolev_dual m𝔽
    ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
    μ𝔽 _ _ _ (I(ha)) hs).exists.choose
local notation "u(" χ ", " ha ", " hs ", " j ")" =>
  (spectralStripJet_memLp χ ha hs j).toLp
    (spectralZeroJet (χ (j).val.1) (j).val.2.1 (j).val.2.2.1 (j).val.2.2.2)

/-- The projective reciprocal-weight kernel of §10.4.3 exists exactly when the
ambient endomorphism is nuclear. Sobolev duality transports the tensor itself. -/
theorem exists_projectiveKernel_iff {α s : ℝ} (ha : 0 ≤ α) (hs : 0 ≤ s)
    (A : W(α, s) →L[ℂ] W(α, s)) :
    (∃ K, sobolevProjectiveKernelOperator (F := F) ha hs K = A) ↔ IsNuclearOperator A :=
  exists_transported_tensor_iff (T(ha, hs)) A

/-- Finite-strip-jet multipliers on the ambient adjoint suffice for the
projective kernel used at p. 520. The cutoffs may keep complete height bands
and the error is measured on the actual weighted Sobolev space. -/
theorem exists_projectiveKernel_comp_spectralProjection_of_cutoffs
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    {a α s : ℝ} (ha : 0 ≤ α) (hs : 0 ≤ s) (A : W(α, s) →L[ℂ] W(α, s))
    (U : ℕ → W(α, s) →L[ℂ] W(α, s)) (K : ℕ → Finset (SpectralStripJetIndex χ a α s))
    (hK : Monotone K)
    (hv : ∀ n j, j ∉ K n → ∀ x, spectralSobolevPairing (F := F) (U n x) (u(χ, ha, hs, j)) = 0)
    (herr : Summable fun n : ℕ ↦ (((K (n + 1)).card : ℝ) + 1) *
      ‖(U n - ContinuousLinearMap.id ℂ (W(α, s))).comp A.adjoint‖) :
    ∃ k, sobolevProjectiveKernelOperator (F := F) ha hs k =
      A.comp (spectralProjection (F := F) a ha hs) := by
  let θ := globalThetaSobolev F a (I(ha)) hs
  let P := spectralProjection (F := F) a ha hs
  let Λ (j : SpectralStripJetIndex χ a α s) : StrongDual ℂ (W(α, s)) :=
    (T(ha, hs)).symm (u(χ, ha, hs, j))
  have ev (j : SpectralStripJetIndex χ a α s) (v : W(α, s)) :
      Λ j v = spectralSobolevPairing v (u(χ, ha, hs, j)) := by
    simpa only [Λ, LinearIsometryEquiv.apply_symm_apply] using
      (spectralSobolevPairing_dual (I(ha)) hs (Λ j) v).2
  have hz (v : W(α, s)) : v ∈ θ ↔ ∀ j, Λ j v = 0 := by
    simpa only [ev] using spectralStripJet_commonKernel_direct (a := a) χ hχ ha hs v
  apply (exists_projectiveKernel_iff ha hs _).mpr
  apply nuclear_comp_projection_of_moment_cutoffs A P (isSelfAdjoint_starProjection θ.orthogonal) Λ _ U K hK _ herr
  · rintro v ⟨x, rfl⟩ h
    let y : θ.orthogonal := ⟨P x, θ.orthogonal.starProjection_apply_mem x⟩
    exact congrArg Subtype.val ((Submodule.mem_left_iff_eq_zero_of_disjoint (x := y)
      θ.orthogonal_disjoint).mp ((hz _).mpr h))
  · intro n j hj x
    have hθ : U n x - P (U n x) ∈ θ := by
      rw [show U n x - P (U n x) = θ.starProjection (U n x) from
        sub_eq_of_eq_add (θ.starProjection_add_starProjection_orthogonal _).symm]
      exact θ.starProjection_apply_mem _
    have hdiff := (hz _).mp hθ j
    rw [map_sub, sub_eq_zero] at hdiff
    exact hdiff.symm.trans ((ev j _).trans (hv n j hj x))

/-- Every admissible output cutoff of convolution after the spectral projection
has a reciprocal-weight projective kernel. This follows from the ambient
cutoff convolution theorem even in the absence of global spectral nuclearity. -/
theorem exists_local_projectiveKernel (a : ℝ) {α s : ℝ} (ha : 0 ≤ α) (hs : 0 ≤ s)
    (φ : BruhatCompactSupport C𝔽) {R ε : ℝ} {ρ : C𝔽 → ℝ}
    (hρ : IsModulatedCutoff m𝔽 R ε ρ) (hband : 0 < R⁻¹+ε ∧ R⁻¹+ε < R-ε) :
    ∃ K, sobolevProjectiveKernelOperator (F := F) ha hs K =
      spectralRestriction a ha hs hρ φ :=
  (exists_projectiveKernel_iff ha hs _).mpr (spectralRestriction_nuclear a ha hs hρ hband φ)

end RiemannMasullo.StripNuclearity
