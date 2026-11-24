module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4
public import RiemannMasullo.Research.TraceComparison.SLocalQuotient
import all RiemannMasullo.AppD_SchwartzBruhat.Sec1a

/-! # The uncut S-local action on the unit locus

Multiplying the scalar dilation kernel by the square root of the norm
gives ordinary multiplicative convolution. For compact support on the
unit locus the actual orbit sum commutes with this action.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped ENNReal NNReal NumberField.AdeleRing Pointwise
namespace RiemannMasullo

variable {F : Type*} [Field F] [NumberField F] {S : Finset (HeightOneSpectrum (𝓞 F))}
attribute [local instance] instSAdeleMeasurableSpaceSec1 instSIdeleLocallyCompactSec1
  instSIdeleSecondCountableSec1 instSIdeleQuotientMeasurableSpaceSec1 instSIdeleQuotientBorelSpaceSec1
  instSIdeleQuotientLocallyCompactSec1 instSIdeleQuotientT2Sec1

set_option quotPrecheck false
local notation "Aₛ" => SAdeleRing F S
local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "Jₛ" => SIdeleQuotient F S
local notation "Hₛ" => sProjectedDiagonal F S
local notation "qS" => QuotientGroup.mk' (sProjectedDiagonal F S)
local notation "μI" => sMultiplicativeTamagawaMeasure F S
local notation "μJ" => sLocalQuotientTamagawaMeasure F S
local notation "N(" x ")" => (((sIdeleNorm F S (x : Iₛ)).val : ℝ))
local notation "W(" x ")" => ((Real.sqrt N(x) : ℝ) : ℂ)
local instance dilationSIdeleT2 : T2Space Iₛ := (sIdeleGroup_description F S).2.1
local instance dilationSIdeleBorel : BorelSpace Iₛ := sIdeleGroup_borelSpace

private theorem sLocal_sqrt_norm_inv_mul (g x : Iₛ) : W(g⁻¹*x) = W(g)⁻¹ * W(x) := by
  have he : N(g⁻¹*x) = N(g)⁻¹ * N(x) := by simp
  rw [he, Real.sqrt_mul (inv_nonneg.mpr (NNReal.coe_nonneg _)), Real.sqrt_inv]
  push_cast
  rfl

/-- Paper: Step I, pp. 515–516, (12.4.1.7). On S-ideles the square-root
norm in the output converts the scalar additive dilation to multiplicative
convolution on the square-root-weighted input. -/
theorem sLocalTraceDilationKernel_weighted_eq_convolution (f : BruhatCompactSupport Iₛ)
    (b : Aₛ → ℂ) (x : Iₛ) :
    W(x) * sLocalTraceDilationKernel f b x.val =
      lcaConvolution μI f.val (fun y : Iₛ ↦ W(y) * b y.val) x := by
  rw [sLocalTraceDilationKernel, ← integral_const_mul, lcaConvolution]
  apply integral_congr_ae (.of_forall fun g ↦ ?_)
  rw [sLocal_sqrt_norm_inv_mul, Units.val_mul]
  ring

private theorem sLocalTrace_finite_convolution_orbits
    (f : BruhatCompactSupport Iₛ) (B : Iₛ → ℂ) (hB : HasCompactSupport B) (x : Iₛ) :
    ∃ T : Finset Hₛ, ∀ ξ ∉ T, ∀ g : Iₛ, f.val g * B (ξ.val * (g⁻¹ * x)) = 0 := by
  classical
  let : DiscreteTopology Hₛ := discreteTopology_sProjectedDiagonal
  let K := (tsupport B * tsupport f.val) * ({x⁻¹} : Set Iₛ)
  have hK : IsCompact K := (hB.mul f.property.2).mul isCompact_singleton
  have hcl : IsClosed (Hₛ : Set Iₛ) := isClosed_sProjectedDiagonal
  have hfin := (hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hK).finite_of_discrete
  let T := hfin.toFinset
  refine ⟨T, fun ξ hout g ↦ ?_⟩
  by_contra hn
  obtain ⟨hf, hb⟩ := mul_ne_zero_iff.mp hn
  apply hout
  apply hfin.mem_toFinset.mpr
  change ξ.val ∈ K
  exact ⟨_, ⟨_, subset_tsupport _ hb, _, subset_tsupport _ hf, rfl⟩,
    x⁻¹, mem_singleton _, by
      calc _ = ξ.val * ((g⁻¹*g)*(x*x⁻¹)) := by ac_rfl
           _ = _ := by simp⟩

/-- Paper: (12.4.1.4) and Step I, pp. 515–516. Periodizing the weighted
output of the actual additive dilation on S-ideles gives the quotient
convolution of the two periodizations. Compact support of the weighted
input on the unit group gives a finite set of translates for each output
class. This comparison precedes the additive Fourier and radial cutoffs. -/
theorem sLocalTraceDilationKernel_periodized_convolution (f : BruhatCompactSupport Iₛ)
    (b : Aₛ → ℂ) (B : Iₛ → ℂ) (hW : ∀ g, B g = W(g) * b g.val)
    (hB : Continuous B) (hc : HasCompactSupport B)
    (φ p : Jₛ → ℂ) (hp : Continuous p)
    (hφ : ∀ g : Iₛ, HasSum (fun ξ : Hₛ ↦ f.val (ξ.val*g)) (φ (qS g)))
    (hP : ∀ g : Iₛ, HasSum (fun ξ : Hₛ ↦ B (ξ.val*g)) (p (qS g))) (x : Iₛ) :
    HasSum (fun ξ : Hₛ ↦ W(ξ.val*x) * sLocalTraceDilationKernel f b (ξ.val*x).val)
      (lcaConvolution μJ φ p (qS x)) := by
  classical
  let : (μI).IsHaarMeasure := sMultiplicativeTamagawaMeasure_isHaarMeasure
  obtain ⟨T,hT⟩ := sLocalTrace_finite_convolution_orbits f B hc x
  let L (ξ : Hₛ) (g : Iₛ) := f.val g * B (ξ.val*(g⁻¹*x))
  have hL (ξ : Hₛ) : W(ξ.val*x) * sLocalTraceDilationKernel f b (ξ.val*x).val = ∫ g, L ξ g ∂μI := by
    rw [sLocalTraceDilationKernel_weighted_eq_convolution, lcaConvolution]
    apply integral_congr_ae (.of_forall fun g ↦ ?_)
    dsimp only [L]
    rw [hW, mul_left_comm g⁻¹ ξ.val x]
  have hI (ξ : Hₛ) : Integrable (L ξ) μI :=
    ((continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp f.property.1)).mul
      (hB.comp (continuous_const.mul (continuous_inv.mul continuous_const)))).integrable_of_hasCompactSupport
      f.property.2.mul_right
  simp_rw [hL]
  have hsum : HasSum (fun ξ : Hₛ ↦ ∫ g, L ξ g ∂μI) (∑ ξ ∈ T, ∫ g, L ξ g ∂μI) :=
    hasSum_sum_of_ne_finset_zero fun ξ hξ ↦ by
      simp only [L, hT ξ hξ, integral_zero]
  convert hsum using 1
  rw [← integral_finsetSum T (fun ξ _ ↦ hI ξ)]
  symm
  calc
    _ = ∫ g : Iₛ, f.val g * p (qS (g⁻¹*x)) ∂μI := by
      apply integral_congr_ae (.of_forall fun g ↦ ?_)
      have ht := ((hP (g⁻¹*x)).mul_left (f.val g)).tsum_eq
      rw [← ht, tsum_eq_sum (fun ξ hξ ↦ hT ξ hξ g)]
    _ = _ := by
      simpa only [map_mul, map_inv, lcaConvolution] using
        sLocalTraceLift_weighted_integral f φ hφ (fun y ↦ p (y⁻¹*qS x))
          (hp.comp (continuous_inv.mul continuous_const))

/-- A continuous compactly supported function on the S-ideles has a
continuous compactly supported S-unit periodization on the quotient. -/
theorem sLocalTrace_exists_compact_periodization (B : Iₛ → ℂ)
    (hB : Continuous B) (hc : HasCompactSupport B) :
    ∃ p : Jₛ → ℂ, Continuous p ∧ HasCompactSupport p ∧
      ∀ g : Iₛ, HasSum (fun ξ : Hₛ ↦ B (ξ.val*g)) (p (qS g)) := by
  classical
  let : DiscreteTopology Hₛ := discreteTopology_sProjectedDiagonal
  let : Countable Hₛ := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  let : (Measure.count : Measure Hₛ).IsHaarMeasure := count_isHaarMeasure_of_discreteTopology
  have hcl : IsClosed (Hₛ : Set Iₛ) := isClosed_sProjectedDiagonal
  have hreg := weilTest_average Hₛ hcl Measure.count hB hc
  refine ⟨_, hreg.1, hreg.2, fun g ↦ ?_⟩
  have hs : (support fun ξ : Hₛ ↦ B (g*ξ.val)).Finite :=
    (((Homeomorph.mulLeft g).isClosedEmbedding.comp hcl.isClosedEmbedding_subtypeVal).isCompact_preimage hc).finite_of_discrete.subset
      (fun ξ hξ ↦ subset_tsupport _ hξ)
  have hsum : Summable (fun ξ : Hₛ ↦ B (g*ξ.val)) := summable_of_hasFiniteSupport hs
  have hInt := integrable_count_iff.mpr hsum.norm
  change HasSum (fun ξ : Hₛ ↦ B (ξ.val*g)) (lcaCosetIntegral Hₛ Measure.count B (QuotientGroup.mk g))
  rw [lcaCosetIntegral_mk Hₛ Measure.count B g hInt]
  have he : (∫ ξ : Hₛ, B (g*ξ.val) ∂Measure.count) = ∑' ξ : Hₛ, B (g*ξ.val) := by
    simpa only [count_real_singleton, one_smul] using integral_countable hInt
  rw [he]
  simpa only [mul_comm g] using hsum.hasSum

/-- Paper: Step I, pp. 515–516. For every compact convolution test and
every additive input whose square-root-weighted restriction is continuous
and compactly supported on the units, both periodizations exist and their
quotient convolution is the periodization of the weighted additive output. -/
theorem sLocalTraceDilationKernel_compact_orbit_action (f : BruhatCompactSupport Iₛ)
    (b : Aₛ → ℂ) (B : Iₛ → ℂ) (hW : ∀ g, B g = W(g) * b g.val)
    (hB : Continuous B) (hc : HasCompactSupport B) :
    ∃ φ p : Jₛ → ℂ, Continuous φ ∧ HasCompactSupport φ ∧ Continuous p ∧ HasCompactSupport p ∧
      (∀ g : Iₛ, HasSum (fun ξ : Hₛ ↦ f.val (ξ.val*g)) (φ (qS g))) ∧
      (∀ g : Iₛ, HasSum (fun ξ : Hₛ ↦ B (ξ.val*g)) (p (qS g))) ∧
      ∀ x : Iₛ, HasSum (fun ξ : Hₛ ↦ W(ξ.val*x) * sLocalTraceDilationKernel f b (ξ.val*x).val)
        (lcaConvolution μJ φ p (qS x)) := by
  obtain ⟨φ,hφc,hφs,hφ⟩ := sLocalTrace_exists_compact_periodization f.val
    (continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp f.property.1)) f.property.2
  obtain ⟨p,hpc,hps,hp⟩ := sLocalTrace_exists_compact_periodization B hB hc
  exact ⟨φ,p,hφc,hφs,hpc,hps,hφ,hp,sLocalTraceDilationKernel_periodized_convolution f b B hW hB hc φ p hpc hφ hp⟩

local notation "testₛ" => SchwartzBruhat (Multiplicative Aₛ)
local notation "X(" b ", " y ")" => (b : testₛ) (Multiplicative.ofAdd (y : Aₛ))

/-- The actual Schwartz–Bruhat input restricted to S-ideles and multiplied
by the square root of the norm is continuous. -/
theorem sLocalTrace_weightedSchwartzRestriction_continuous (b : testₛ) :
    Continuous (fun g : Iₛ ↦ W(g) * X(b, g.val)) := by
  have h : Continuous (fun g : Iₛ ↦ sIdeleQuotientNorm F S (QuotientGroup.mk g)) :=
    (isProperMap_sIdeleQuotientNorm F S).continuous.comp continuous_quot_mk
  have hn : Continuous (fun g : Iₛ ↦ N(g)) := NNReal.continuous_coe.comp (Units.continuous_val.comp h)
  exact (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp hn)).mul
    ((schwartzBruhat_continuous b).comp (show Continuous (fun g : Iₛ ↦ Multiplicative.ofAdd g.val) from
      continuous_ofAdd.comp Units.continuous_val))

local notation "SchwartzOrbit(" f ", " b ", " hc ")" =>
  sLocalTraceDilationKernel_compact_orbit_action f (fun x ↦ X(b, x))
    (fun g : Iₛ ↦ W(g)*X(b, g.val)) (fun _ ↦ rfl) (sLocalTrace_weightedSchwartzRestriction_continuous b)
    (HasCompactSupport.mul_left hc)

/-- Paper: (12.4.1.4)–(12.4.1.7), pp. 515–516. For Schwartz–Bruhat inputs
whose restriction has compact support on the unit group, the uncut weighted
additive action descends to the convolution of the actual S-unit periodizations. -/
theorem sLocalTraceDilationKernel_schwartz_orbit_action (f : BruhatCompactSupport Iₛ) (b : testₛ)
    (hc : HasCompactSupport (fun g : Iₛ ↦ X(b, g.val))) :
    type_of% SchwartzOrbit(f, b, hc) :=
  SchwartzOrbit(f, b, hc)

end RiemannMasullo
