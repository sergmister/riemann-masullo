module

public import RiemannMasullo.Research.StripNuclearity.HeckeConvolution
public import RiemannMasullo.Research.StripNuclearity.ProjectionTransfer

/-!
# Projective kernels of projected inverse-character lifts
-/

@[expose] public noncomputable section
open Filter Function MeasureTheory NumberField Set
open scoped Topology NumberField.AdeleRing InnerProductSpace ContDiff

namespace RiemannMasullo.StripNuclearity

set_option quotPrecheck false
attribute [local instance] uniformContinuousConstSMul_of_continuousConstSMul

variable {F : Type*} [Field F] [NumberField F]
attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "logNorm" => (fun g : C𝔽 ↦ Real.log ((ideleClassNorm F g).val : ℝ))
local notation "W(" α ", " s ")" => CompactIntervalSobolev μ𝔽 logNorm (-α) α s
local notation "Ws(" α ", " s ")" => CompactIntervalSobolev volume id (-α) α s
/-- Bounded operators on both sides of a nuclear map preserve the summable
Banach expansion, also when the outer and inner Hilbert spaces differ. -/
private theorem nuclear_sandwich {E H : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : E →L[ℂ] E) (hA : IsNuclearOperator A) (B : H →L[ℂ] E) (C : E →L[ℂ] H) :
    IsNuclearOperator (C.comp (A.comp B)) := by
  obtain ⟨c,φ,y,hc,hφ,hy,hs⟩ := (isNuclearOperator_iff_isBanachNuclear A).mp hA
  have hpre : Continuous (fun v : E →L[ℂ] ℂ ↦ v.comp B) := continuous_id.clm_comp continuous_const
  refine (isNuclearOperator_iff_isBanachNuclear _).mpr
    ⟨c,fun n ↦ (φ n).comp B,C ∘ y,hc,
      (hpre.tendsto' 0 0 (ContinuousLinearMap.zero_comp B)).comp hφ,
      (C.continuous.tendsto' 0 0 (map_zero C)).comp hy,fun x ↦ ?_⟩
  change HasSum (fun n ↦ (c n * φ n (B x)) • C (y n)) (C (A (B x)))
  simpa only [map_smul] using C.hasSum (hs (B x))

private theorem nuclear_lift_of_projection_identity {E H : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (L : E →L[ℂ] H) (A Q : E →L[ℂ] E) (P : H →L[ℂ] H)
    (hN : IsNuclearOperator (A.comp Q))
    (hp : Q.comp (L.adjoint.comp P) = L.adjoint.comp P) :
    IsNuclearOperator ((L.comp (A.comp L.adjoint)).comp P) := by
  have he : (L.comp (A.comp L.adjoint)).comp P =
      L.comp ((A.comp Q).comp (L.adjoint.comp P)) := by
    simp only [ContinuousLinearMap.comp_assoc,hp]
  rw [he]
  exact nuclear_sandwich (A.comp Q) hN (L.adjoint.comp P) L

/-- Each inverse-character lift of a smooth compact radial convolution has an
actual reciprocal-weight projective kernel after the ambient spectral
projection. The Haar normalization in the moment pairing cancels in the null space. -/
theorem exists_projectiveKernel_projected_radial_lift
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    (ξ : PontryaginDual C₁) {α s : ℝ} (ha : 0 ≤ α) (hs : 1 < s)
    (L : Ws(α,s) →L[ℂ] W(α,s))
    (hL : ∀ f, (L f : C𝔽 → ℂ) =ᵐ[μ𝔽] fun x ↦ (χ ξ x : ℂ)⁻¹ * f (logNorm x))
    (κ : ℝ → ℂ) (hk : HasCompactSupport κ) (hd : ContDiff ℝ (∞) κ) (A : Ws(α,s) →L[ℂ] Ws(α,s))
    (hA : ∀ f, ∀ᵐ x ∂volume, A f x = ∫ t : ℝ, κ t * f (x-t)) :
    let hs₀ : 0 ≤ s := zero_le_one.trans hs.le
    let P := spectralProjection (F := F) (1/2) ha hs₀
    ∃ K, sobolevProjectiveKernelOperator (F := F) ha hs₀ K =
      (L.comp (A.comp L.adjoint)).comp P := by
  intro hs₀ P
  let data := exists_normalized_idele_log_haar_and_radial_lift (F := F) (χ ξ) α s
  let ν := data.choose
  let : ν.IsHaarMeasure := data.choose_spec.choose
  have hlog := data.choose_spec.choose_spec.1
  let scalar := exists_projected_hecke_convolution (F := F) (χ ξ) ha hs
  let j := scalar.choose
  let Λ := scalar.choose_spec.choose
  have hj := scalar.choose_spec.choose_spec.2.1
  have hΛ := scalar.choose_spec.choose_spec.2.2.1
  have hN := scalar.choose_spec.choose_spec.2.2.2
  let Q := (⨅ l, (Λ l).ker).orthogonal.starProjection
  have hp : Q.comp (L.adjoint.comp P) = L.adjoint.comp P :=
    radial_projector_comp_lift_adjoint_spectralProjection (F := F) χ hχ ξ ha hs L hL ν hlog j Λ hj hΛ
  exact (exists_projectiveKernel_iff (F := F) ha hs₀ ((L.comp (A.comp L.adjoint)).comp P)).mpr
    (nuclear_lift_of_projection_identity L A Q P (hN κ hk hd A hA) hp)

end RiemannMasullo.StripNuclearity
