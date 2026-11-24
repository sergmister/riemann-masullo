module

public import RiemannMasullo.Research.StripNuclearity.HeckeConvolution
public import RiemannMasullo.Research.StripNuclearity.ProjectionTransfer
public import RiemannMasullo.Research.StripNuclearity.TraceSandwich
public import RiemannMasullo.Research.StripNuclearity.TraceNormSum

/-!
# Trace-class summation of projected angular convolutions

The character lift has constant norm because its character multiplier has unit modulus.
The common-kernel synthesis of Chapter 10 transfers the scalar estimate to each angular
term of the ambient operator. An operator-norm realization of the Fourier expansion and
summability of the weighted radial costs then supply the projective kernel.
-/

@[expose] public noncomputable section

open Function MeasureTheory NumberField Set
open scoped Topology NumberField.AdeleRing ContDiff

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

/-- The operator norms of two character lifts agree for the fixed Tamagawa measure.
Taking norms of the representing functions removes both unitary characters. -/
theorem norm_radial_lift_eq {α s : ℝ} (χ ψ : PontryaginDual C𝔽)
    (L U : Ws(α,s) →L[ℂ] W(α,s))
    (hL : ∀ f, (L f : C𝔽 → ℂ) =ᵐ[μ𝔽] fun x ↦ (χ x : ℂ)⁻¹ * f (logNorm x))
    (hU : ∀ f, (U f : C𝔽 → ℂ) =ᵐ[μ𝔽] fun x ↦ (ψ x : ℂ)⁻¹ * f (logNorm x)) :
    ‖L‖ = ‖U‖ := by
  have he (f : Ws(α,s)) : ‖L f‖ = ‖U f‖ := by
    simp only [Lp.norm_def]
    apply congrArg ENNReal.toReal
    apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
    apply (withDensity_absolutelyContinuous μ𝔽 _).ae_eq
    filter_upwards [hL f,hU f] with x hx hy
    simp only [hx,hy,norm_mul,norm_inv,Circle.norm_coe,inv_one,one_mul]
  exact le_antisymm
    (L.opNorm_le_bound (norm_nonneg U) fun f ↦ (he f).le.trans (U.le_opNorm f))
    (U.opNorm_le_bound (norm_nonneg L) fun f ↦ (he f).symm.le.trans (L.le_opNorm f))

/-- Every inverse-character radial lift for fixed Hardy and Haar data has one and
the same norm. -/
private theorem exists_uniform_radial_lift_norm (α s : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (ψ : PontryaginDual C𝔽) (L : Ws(α,s) →L[ℂ] W(α,s)),
      (∀ f, (L f : C𝔽 → ℂ) =ᵐ[μ𝔽] fun x ↦ (ψ x : ℂ)⁻¹ * f (logNorm x)) → ‖L‖ = M := by
  let ref := exists_normalized_idele_log_haar_and_radial_lift (F := F) (1 : PontryaginDual C𝔽) α s
  let data := ref.choose_spec.choose_spec.2
  let U := data.choose
  exact ⟨‖U‖,norm_nonneg U,fun ψ L hL ↦ norm_radial_lift_eq ψ 1 L U hL data.choose_spec.2⟩

private theorem mul_cost_bound {a b t x y z : ℝ} (hab : a = b)
    (ht : t ≤ x*y*z) (hb : 0 ≤ b) : a*t ≤ b*x*y*z :=
  (congrArg (· * t) hab).le.trans
    ((mul_le_mul_of_nonneg_left ht hb).trans_eq (by ring))

/-- On one fixed strip, every inverse-character lift of a scalar convolution followed
by the ambient Chapter 10 projection satisfies the same support-dependent bound.
Its only variable factors are the admitted zero mass and the quadratic Fourier cost. -/
theorem projected_radial_lift_traceNorm_uniform
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    {α s : ℝ} (ha : 0 ≤ α) (hs : 1 < s) :
    let P := spectralProjection (F := F) (1/2) ha (show 0 ≤ s by linarith)
    ∃ C : {K : Set ℝ // IsCompact K} → ℝ, (∀ K, 0 ≤ C K) ∧
      ∀ (ξ : PontryaginDual C₁) (L : Ws(α,s) →L[ℂ] W(α,s)),
        (∀ f, (L f : C𝔽 → ℂ) =ᵐ[μ𝔽] fun x ↦ (χ ξ x : ℂ)⁻¹ * f (logNorm x)) →
        ∀ (K : {K : Set ℝ // IsCompact K}) (κ : ℝ → ℂ), tsupport κ ⊆ K.val →
          ContDiff ℝ (∞) κ → ∀ A : Ws(α,s) →L[ℂ] Ws(α,s),
            HasRadialConvolutionKernel α s κ A →
            ∃ h : IsNuclearOperator ((L.comp (A.comp L.adjoint)).comp P),
              traceNorm ⟨(L.comp (A.comp L.adjoint)).comp P,h⟩ ≤
                C K * (1+admittedHeckeDivisorMass (χ ξ) α s)^2 * radialQuadraticFourierCost κ := by
  intro P
  let normalization := exists_normalized_idele_log_haar_and_radial_lift (F := F) (1 : PontryaginDual C𝔽) α s
  let ν := normalization.choose
  let : ν.IsHaarMeasure := normalization.choose_spec.choose
  have hlog := normalization.choose_spec.choose_spec.1
  let bd := exists_uniform_radial_lift_norm (F := F) α s
  let M := bd.choose
  let scalar := exists_projected_hecke_convolution_uniform (F := F) ha hs
  let j := scalar.choose
  let C := scalar.choose_spec.choose
  have hj := scalar.choose_spec.choose_spec.2.1
  have hC := scalar.choose_spec.choose_spec.2.2.1
  have hu := scalar.choose_spec.choose_spec.2.2.2
  let c := M*(M*‖P‖)
  have hc : 0 ≤ c := mul_nonneg bd.choose_spec.1 (mul_nonneg bd.choose_spec.1 (norm_nonneg P))
  refine ⟨fun K ↦ c*C K,fun K ↦ mul_nonneg hc (hC K),?_⟩
  intro ξ L hL K κ hκ hsκ A hA
  let jets := hu (χ ξ)
  let Λ := jets.choose
  let Q := (⨅ l, (Λ l).ker).orthogonal.starProjection
  have hp : Q.comp (L.adjoint.comp P) = L.adjoint.comp P :=
    radial_projector_comp_lift_adjoint_spectralProjection (F := F) χ hχ ξ ha hs L hL ν hlog j Λ hj jets.choose_spec.1
  let estimate := jets.choose_spec.2 K κ hκ hsκ A hA
  let lifted := projected_traceNorm_sandwich_le L A Q P estimate.choose hp
  refine ⟨lifted.choose,lifted.choose_spec.trans ?_⟩
  have hnorm : ‖L‖ = M := bd.choose_spec.2 (χ ξ) L hL
  exact mul_cost_bound (b := c) (congrArg (fun r : ℝ ↦ r*(r*‖P‖)) hnorm) estimate.choose_spec hc

/-- An operator-norm angular expansion with absolutely summable weighted radial
Fourier costs represents an ambient projective kernel after spectral projection. -/
theorem exists_projectiveKernel_of_radial_lift_sum
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    {α s : ℝ} (ha : 0 ≤ α) (hs : 1 < s)
    (L : PontryaginDual C₁ → Ws(α,s) →L[ℂ] W(α,s))
    (hL : ∀ ξ f, (L ξ f : C𝔽 → ℂ) =ᵐ[μ𝔽] fun x ↦ (χ ξ x : ℂ)⁻¹ * f (logNorm x))
    (K : Set ℝ) (hK : IsCompact K) (p : PontryaginDual C₁ → ℝ → ℂ)
    (hp : ∀ ξ, tsupport (p ξ) ⊆ K ∧ ContDiff ℝ (∞) (p ξ))
    (A : PontryaginDual C₁ → Ws(α,s) →L[ℂ] Ws(α,s))
    (hA : ∀ ξ, HasRadialConvolutionKernel α s (p ξ) (A ξ))
    (T : W(α,s) →L[ℂ] W(α,s)) (hT : HasSum (fun ξ ↦ (L ξ).comp ((A ξ).comp (L ξ).adjoint)) T)
    (hcost : Summable (fun ξ ↦ (1+admittedHeckeDivisorMass (χ ξ) α s)^2 *
      radialQuadraticFourierCost (p ξ))) :
    let hs₀ : 0 ≤ s := zero_le_one.trans hs.le
    let P := spectralProjection (F := F) (1/2) ha hs₀
    ∃ k, sobolevProjectiveKernelOperator (F := F) ha hs₀ k = T.comp P := by
  intro hs₀ P
  let uniform := projected_radial_lift_traceNorm_uniform χ hχ ha hs
  let C := uniform.choose
  let J : {K : Set ℝ // IsCompact K} := ⟨K,hK⟩
  let data (ξ : PontryaginDual C₁) :=
    uniform.choose_spec.2 ξ (L ξ) (hL ξ) J (p ξ) (hp ξ).1 (hp ξ).2 (A ξ) (hA ξ)
  let S (ξ : PontryaginDual C₁) : nuclearEndomorphisms (W(α,s)) :=
    ⟨((L ξ).comp ((A ξ).comp (L ξ).adjoint)).comp P,(data ξ).choose⟩
  have hcomp : HasSum (fun ξ ↦ (S ξ).val) (T.comp P) :=
    ((ContinuousLinearMap.compL ℂ (W(α,s)) (W(α,s)) (W(α,s))).flip P).hasSum hT
  let c := fun ξ ↦ C J*((1+admittedHeckeDivisorMass (χ ξ) α s)^2*radialQuadraticFourierCost (p ξ))
  have hbound (ξ : PontryaginDual C₁) : traceNorm (S ξ) ≤ c ξ :=
    (data ξ).choose_spec.trans_eq (mul_assoc _ _ _)
  have result := traceNorm_le_of_hasSum S (T.comp P) hcomp c (hcost.mul_left _) hbound
  exact (exists_projectiveKernel_iff (F := F) ha hs₀ (T.comp P)).mpr result.choose

end RiemannMasullo.StripNuclearity
