module

public import RiemannMasullo.Research.StripNuclearity.AngularReconstruction
public import RiemannMasullo.Research.StripNuclearity.SumOrbitKernels
public import RiemannMasullo.Research.StripNuclearity.IdeleEigenConvolution
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-! # The ambient Hardy–Sobolev action as a sum of its angular convolutions

Probability Haar on the compact norm-one subgroup gives the coefficients.
The Haar normalization of the ambient group is carried by the Hilbert adjoint
of each radial lift.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set
open scoped NNReal ContDiff Topology

namespace RiemannMasullo.StripNuclearity

section SplitGroup

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m)
  (σ : ℝ≥0ˣ →ₜ* G) (hright : RightInverse σ m)

set_option quotPrecheck false
local notation "K" => m.toMonoidHom.ker
local notation "ell" => (fun x : G ↦ Real.log ((m x).val : ℝ))

include hm hright in
/-- Absolute angular reconstruction of a compact Bruhat convolution for a split modulation. -/
theorem normSection_hasSum_lifted_angular_convolutions (μK : Measure K) [μK.IsHaarMeasure]
    [IsProbabilityMeasure μK] [μK.WeaklyRegular]
    (χ : PontryaginDual K → PontryaginDual G) (hχ : ∀ ξ (k : K), χ ξ k.val = ξ k)
    (hr : ∀ ξ t, χ ξ (σ t) = 1) (φ : BruhatCompactSupport G)
    {a b s : ℝ} (hab : a ≤ b) (hs : 0 ≤ s) :
    let p (ξ : PontryaginDual K) (t : ℝ) :=
      ∫ k : K, φ.val (k.val * σ (radialExponential (Multiplicative.ofAdd t))) * (ξ k : ℂ) ∂μK
    let E := CompactIntervalSobolev volume id a b s
    let W := CompactIntervalSobolev μ ell a b s
    ∃ (L : PontryaginDual K → E →L[ℂ] W) (A : PontryaginDual K → E →L[ℂ] E),
      (∀ ξ f, (L ξ f : G → ℂ) =ᵐ[μ] fun x ↦ (χ ξ x : ℂ)⁻¹ * f (ell x)) ∧
      (∀ ξ f, ∀ᵐ x ∂volume, A ξ f x = ∫ t : ℝ, p ξ t * f (x-t)) ∧
      HasSum (fun ξ ↦ (L ξ).comp ((A ξ).comp (L ξ).adjoint)) (hardySobolevTestAction μ m a b s hab hs φ) := by
  classical
  intro p E W
  let : CompactSpace K := isCompact_iff_compactSpace.mp (IsModulation.isCompact_ker hm)
  let : SecondCountableTopology K := Topology.IsInducing.subtypeVal.secondCountableTopology
  let : SecondCountableTopology Circle := inferInstanceAs (SecondCountableTopology (Metric.sphere (0 : ℂ) 1))
  let : SecondCountableTopology (PontryaginDual K) :=
    (ContinuousMonoidHom.isEmbedding_toContinuousMap K Circle).secondCountableTopology
  let : Countable (PontryaginDual K) := countable_of_Lindelof_of_discrete
  obtain ⟨J, hJ, hp, hder⟩ := normSection_summable_angularProfile_derivatives m hm σ hright μK φ
  have hpc (ξ) : HasCompactSupport (p ξ) := hJ.of_isClosed_subset isClosed_closure (hp ξ).1
  let c (ξ : PontryaginDual K) := ∫ u : ℝ, ‖deriv (p ξ) u‖
  have hc : Summable c := by simpa [p, c, iteratedDeriv_one] using hder [] 1
  have hpos (ξ) : 0 ≤ c ξ := integral_nonneg fun _ ↦ norm_nonneg _
  have hbound (ξ) (t : ℝ) : ‖p ξ t‖ ≤ c ξ := norm_le_integral_norm_deriv_of_compact (hp ξ).2 (hpc ξ) t
  have hsum (x : G) := hasSum_normSection_angular_profiles m σ hright μK χ
    hχ hr φ.val
    (continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp φ.property.1)) p
    (fun _ _ ↦ rfl) (fun t ↦ hc.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun ξ ↦ hbound ξ t)) x
  obtain ⟨hvolume, hLift⟩ := exists_modulated_radial_lifts μ m hm.1
    hright.surjective a b s
  choose L hL using fun ξ ↦ hLift (χ ξ)
  choose A hA using fun ξ ↦ exists_scalar_weighted_convolution a b s hab hs (p ξ) (hp ξ).2.continuous (hpc ξ)
  have ha (ξ) (f : E) := (hA ξ f).mono fun _ hx ↦ hx.2
  refine ⟨L, A, hL, ha, ?_⟩
  let l := ell
  let e : ℝ≥0ˣ ≃ₜ ℝ := radialExponential.symm.toHomeomorph
  have hel (x : G) : e (m x) = l x := by
    obtain ⟨t, ht⟩ := radialExponential.surjective (m x)
    change (radialExponential.symm (m x)).toAdd = Real.log ((m x).val : ℝ)
    rw [← ht, ContinuousMulEquiv.symm_apply_apply]
    exact (Real.log_exp t.toAdd).symm
  have hl : Continuous l :=
    (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)).log
      (fun x ↦ by
        change ((m x).val : ℝ) ≠ 0
        exact_mod_cast (m x).ne_zero)
  let S := m ⁻¹' (e ⁻¹' J)
  have hS : IsCompact S := hm.1.isCompact_preimage (e.isCompact_preimage.mpr hJ)
  let q (ξ : PontryaginDual K) (x : G) := (χ ξ x : ℂ)⁻¹ * p ξ (l x)
  have hq (ξ) : Continuous (q ξ) := ((continuous_subtype_val.comp (χ ξ).continuous).inv₀
    (fun x ↦ Circle.coe_ne_zero _)).mul ((hp ξ).2.continuous.comp hl)
  have hqs (ξ) : tsupport (q ξ) ⊆ S := by
    apply closure_minimal _ hS.isClosed
    intro x hx
    change e (m x) ∈ J
    rw [hel]
    have hpx : p ξ (l x) ≠ 0 := by
      intro hz
      apply hx
      change (χ ξ x : ℂ)⁻¹ * p ξ (l x) = 0
      rw [hz, mul_zero]
    exact (hp ξ).1 (subset_tsupport (p ξ) hpx)
  have hqc (ξ) : HasCompactSupport (q ξ) := hS.of_isClosed_subset isClosed_closure (hqs ξ)
  let ρ := hardySobolevTranslation μ m a b s hab hs
  apply hasSum_orbit_operators_of_compact_support μ (fun x ↦ ρ x)
    (exists_hardySobolevTranslation μ m a b s hab hs).choose_spec.2 hS φ.val q c hc hpos hq hqs
    (fun ξ x ↦ by simpa [q] using hbound ξ (l x)) hsum
  · have hf := continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp φ.property.1)
    exact hardySobolev_eq_integral_translation_of_convolution μ m a b s hab hs
      (hf.integrable_of_hasCompactSupport φ.property.2) φ.property.2 _ (hardySobolevTestAction_apply μ m a b s hab hs φ)
  · intro ξ
    apply hardySobolev_eq_integral_translation_of_convolution μ m a b s hab hs
      ((hq ξ).integrable_of_hasCompactSupport (hqc ξ)) (hqc ξ)
    exact radial_adjoint_eq_convolution_ae μ m hvolume (χ ξ) (p ξ) (hp ξ).2.continuous (hpc ξ) a b s
      (L ξ) (hL ξ) (A ξ) (ha ξ)

end SplitGroup

variable {F : Type*} [Field F] [NumberField F]

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

set_option quotPrecheck false

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "K𝔽" => (ideleClassNorm F).ker
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" => (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "logNorm" => (fun x : C𝔽 ↦ Real.log ((ideleClassNorm F x).val : ℝ))
local notation "σ𝔽" => (⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩ :
  IdeleGroup (𝓞 F) F →ₜ* C𝔽).comp ⟨canonicalIdeleNormSection F, canonicalIdeleNormSection_continuous F⟩

/-- For any number field and compact Bruhat test, the angular convolution blocks
sum in operator norm to the actual ambient Hardy–Sobolev action. The radial lifts,
profiles and unweighted scalar convolutions use the canonical section. -/
theorem ideleClass_hasSum_lifted_angular_convolutions (μK : Measure K𝔽) [μK.IsHaarMeasure]
    [IsProbabilityMeasure μK] [μK.WeaklyRegular]
    (χ : PontryaginDual K𝔽 → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    (hr : ∀ ξ t, χ ξ (σ𝔽 t) = 1) (φ : BruhatCompactSupport C𝔽)
    {a b s : ℝ} (hab : a ≤ b) (hs : 0 ≤ s) :
    let p (ξ : PontryaginDual K𝔽) (t : ℝ) :=
      ∫ k : K𝔽, φ.val (k.val * σ𝔽 (radialExponential (Multiplicative.ofAdd t))) * (ξ k : ℂ) ∂μK
    let E := CompactIntervalSobolev volume id a b s
    let W := CompactIntervalSobolev μ𝔽 logNorm a b s
    ∃ (L : PontryaginDual K𝔽 → E →L[ℂ] W) (A : PontryaginDual K𝔽 → E →L[ℂ] E),
      (∀ ξ f, (L ξ f : C𝔽 → ℂ) =ᵐ[μ𝔽] fun x ↦ (χ ξ x : ℂ)⁻¹ * f (logNorm x)) ∧
      (∀ ξ f, ∀ᵐ x ∂volume, A ξ f x = ∫ t : ℝ, p ξ t * f (x-t)) ∧
      HasSum (fun ξ ↦ (L ξ).comp ((A ξ).comp (L ξ).adjoint)) (hardySobolevTestAction μ𝔽 m𝔽 a b s hab hs φ) := by
  exact normSection_hasSum_lifted_angular_convolutions μ𝔽 m𝔽
    ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ σ𝔽
    (canonicalIdeleNormSection_rightInverse F) μK χ (fun ξ k ↦ DFunLike.congr_fun (hχ ξ) k)
    hr φ hab hs

end RiemannMasullo.StripNuclearity
