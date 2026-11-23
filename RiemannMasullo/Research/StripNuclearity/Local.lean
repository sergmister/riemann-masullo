module
public import RiemannMasullo.Research.StripNuclearity.ScalarKernel
public import RiemannMasullo.Research.StripNuclearity.Factor
public import RiemannMasullo.Research.StripNuclearity.RealMaskedKernel
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Compact localization of the weighted adjoint kernel
-/

@[expose] public noncomputable section
open Function Filter MeasureTheory Set
open scoped Topology ContDiff Convolution Pointwise FourierTransform

namespace RiemannMasullo.StripNuclearity

local notation "ν[" w "]" => (volume.withDensity fun x : ℝ ↦ ENNReal.ofReal ((w : ℝ → ℝ) x))
local notation "H[" w "]" => Lp ℂ 2 ν[w]

/-- When the source is compactly localized, a smooth weighted adjoint
convolution is nuclear. Finite propagation permits compact L² masks on
both sides of its conjugate reflected kernel. Fixing a common compact kernel
support gives a uniform multiple of the absolute ordinary Fourier mass. -/
theorem traceNorm_compactly_masked_adjoint_uniform {w : ℝ → ℝ} (hw : Continuous w) (hp : ∀ x, 0 < w x)
    {J : Set ℝ} (hJ : IsCompact J)
    (a : ℝ → ℝ) (ha : Continuous a) (hac : HasCompactSupport a)
    (M : H[w] →L[ℂ] H[w]) (hM : ∀ u, (M u : ℝ → ℂ) =ᵐ[volume] fun x ↦ (a x : ℂ)*u x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (κ : ℝ → ℂ), tsupport κ ⊆ J → ContDiff ℝ ∞ κ →
      ∀ (B : H[w] →L[ℂ] H[w]), HasWeightedAdjointKernel w κ B →
        ∃ h : IsNuclearOperator (B.comp M), traceNorm ⟨B.comp M,h⟩ ≤ C * ∫ u : ℝ, ‖𝓕 κ u‖ := by
  let ν := ν[w]
  let : IsLocallyFiniteMeasure ν := IsLocallyFiniteMeasure.withDensity_ofReal hw
  let S := tsupport a + J
  have hS : IsCompact S := hac.isCompact.add hJ
  let L (x : ℝ) := S.indicator (fun y ↦ (w y : ℂ)⁻¹) x
  let Q := fun x ↦ (a x : ℂ)
  have hi : Continuous (fun x ↦ (w x : ℂ)⁻¹) :=
    (Complex.continuous_ofReal.comp hw).inv₀ fun x ↦ Complex.ofReal_ne_zero.mpr (hp x).ne'
  have hlp : MemLp L 2 ν := by
    rw [show L = S.indicator (fun y ↦ (w y : ℂ)⁻¹) from rfl,
      memLp_indicator_iff_restrict hS.measurableSet.nullMeasurableSet]
    obtain ⟨C,hC⟩ := hS.exists_bound_of_continuousOn hi.continuousOn
    let : IsFiniteMeasure (ν.restrict S) := ⟨by simpa using hS.measure_lt_top⟩
    exact (memLp_top_of_bound hi.aestronglyMeasurable C ((ae_restrict_mem hS.measurableSet).mono hC)).mono_exponent le_top
  have hrp : MemLp Q 2 ν := (Complex.continuous_ofReal.comp ha).memLp_of_hasCompactSupport
    (hac.comp_left Complex.ofReal_zero)
  refine ⟨‖hrp.toLp Q‖ * ‖hlp.toLp L‖, by positivity, ?_⟩
  intro κ hK hs B hB
  have hc : HasCompactSupport κ := hJ.of_isClosed_subset isClosed_closure hK
  let ψ := hc.toSchwartzMap hs
  have hF : Integrable (𝓕 κ) := (𝓕 ψ).integrable
  obtain ⟨T,hT,hcost,hcore⟩ := exists_masked_scalar_kernel_traceNorm_le ν κ hs.continuous
    (hs.continuous.integrable_of_hasCompactSupport hc) hF L Q hlp hrp
  have hbase : volume ≪ ν := withDensity_absolutelyContinuous' hw.measurable.ennreal_ofReal.aemeasurable
    (.of_forall fun x ↦ (ENNReal.ofReal_pos.mpr (hp x)).ne')
  have he : B.comp M = T := by
    apply ContinuousLinearMap.ext
    intro u
    have hclosed : IsClosed {z : H[w] | B (M z) = T z} := isClosed_eq (B.continuous.comp M.continuous) T.continuous
    apply closure_minimal _ hclosed ((compact_weighted_dense hw hp) u)
    rintro f ⟨g,hfg,hgs,hgc⟩
    let af := fun y ↦ (a y : ℂ)*g y
    have hAf : (M f : ℝ → ℂ) =ᵐ[volume] af := (hM f).trans (hfg.mono fun y hy ↦ congrArg ((a y : ℂ)*·) hy)
    have hb := hB (M f) af ((Complex.continuous_ofReal.comp ha).mul hgc) hgs.mul_left hAf
    apply Lp.ext
    apply (withDensity_absolutelyContinuous volume _).ae_eq
    filter_upwards [hb,hbase.ae_eq (hcore f)] with x hb ht
    rw [hb,ht]
    rw [integral_withDensity_eq_integral_toReal_smul hw.measurable.ennreal_ofReal
      (.of_forall fun x ↦ ENNReal.ofReal_lt_top)]
    change (w x : ℂ)⁻¹*(∫ y : ℝ, ((w y : ℂ)*af y)*κ (x-y)) = _
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hfg] with y hy
    simp only [ENNReal.toReal_ofReal (hp y).le, Complex.real_smul, hy, af, Q, Complex.star_def,
      Complex.conj_ofReal]
    by_cases hxy : x ∈ S
    · rw [show L x = (w x : ℂ)⁻¹ from indicator_of_mem hxy _]
      ring
    · by_cases hya : a y = 0
      · rw [hya]
        simp
      · have hk : κ (x-y) = 0 := image_eq_zero_of_notMem_tsupport (fun hk ↦ hxy
          ⟨y,subset_tsupport _ hya,x-y,hK hk,by ring⟩)
        simp [hk]
  exact he ▸ ⟨hT,hcost⟩

/-- When the source is compactly localized, a smooth weighted adjoint
convolution is nuclear. Finite propagation permits compact L² masks on
both sides of its conjugate reflected kernel. -/
theorem nuclear_compactly_masked_adjoint {w : ℝ → ℝ} (hw : Continuous w) (hp : ∀ x, 0 < w x)
    (κ : ℝ → ℂ) (hc : HasCompactSupport κ) (hs : ContDiff ℝ ∞ κ)
    (B : H[w] →L[ℂ] H[w]) (hB : HasWeightedAdjointKernel w κ B)
    (a : ℝ → ℝ) (ha : Continuous a) (hac : HasCompactSupport a)
    (M : H[w] →L[ℂ] H[w]) (hM : ∀ u, (M u : ℝ → ℂ) =ᵐ[volume] fun x ↦ (a x : ℂ)*u x) :
    IsNuclearOperator (B.comp M) := by
  obtain ⟨_,_,h⟩ := traceNorm_compactly_masked_adjoint_uniform hw hp hc.isCompact a ha hac M hM
  obtain ⟨hB,_⟩ := h κ Subset.rfl hs B hB
  exact hB

end RiemannMasullo.StripNuclearity
