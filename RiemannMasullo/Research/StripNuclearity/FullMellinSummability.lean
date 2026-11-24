module

public import RiemannMasullo.Research.StripNuclearity.NumberFieldDiagonal
public import RiemannMasullo.Research.StripNuclearity.NormSectionCharacters
public import RiemannMasullo.Research.StripNuclearity.QuotientNuclear

/-! # Absolute convergence of the idelic zero sum

The trace of the nuclear quotient convolution at half-width one half contains
every positive completed divisor with its full multiplicity. This gives the
pointwise convergence used in Appendix B before evaluating the local terms.
-/

@[expose] public noncomputable section

open Function MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo.StripNuclearity

variable {F : Type*} [Field F] [NumberField F]

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 instSpectralQuotientPolynormableSec3

set_option quotPrecheck false
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "X" => PontryaginDual C₁
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" => (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "hm𝔽" => (⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ : IsModulation m𝔽)
local notation "D(" χ ")" => MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ
local notation "M(" φ ", " χ ", " w ")" =>
  modulatedFourierMellin m𝔽 univ hm𝔽 μ𝔽 (φ : BruhatCompactSupport C𝔽).val (ideleClassNormTwist (F := F) χ w)
local notation "height(" x ")" => ((((ideleClassNorm F x).val : ℝ) : ℂ))
local notation "chartZeros(" τ ")" =>
  {z : {χ : PontryaginDual C𝔽 // ∀ t : ℝ≥0ˣ, χ (τ t) = 1} × ℂ //
    0 < MeromorphicOn.divisor (explicitFormulaCompletedHeckeL z.1.val) univ z.2}

private theorem centered_full_divisor_summable (χ : X → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice χ) (φ : BruhatCompactSupport C𝔽) :
    let S := {z : X × ℂ | 0 < D(χ z.1) z.2}
    Summable (fun z : S ↦ ‖((D(χ z.val.1) z.val.2 : ℤ) : ℂ) * M(φ, χ z.val.1, z.val.2-1/2)‖) := by
  intro S
  have hi (z : S) : |z.val.2.re - 1/2| < 1/2 := by
    have h := heckePositiveDivisor_open_strip (χ z.val.1) z.property
    exact abs_lt.mpr ⟨by linarith [h.1], by linarith [h.2]⟩
  have hS (z : X × ℂ) : z ∈ S ↔ 0 < D(χ z.1) z.2 ∧ |z.2.re-1/2| ≤ 1/2 :=
    ⟨fun hz ↦ ⟨hz, (hi ⟨z,hz⟩).le⟩, And.left⟩
  let hα : (0 : ℝ) ≤ 1/2 := by norm_num
  let hs : (1 : ℝ) < 3 := Nat.one_lt_ofNat
  let hs₀ := zero_le_one.trans hs.le
  let hn := spectralConvolution_nuclear_of_projectiveKernel (F := F) (1/2) hα hs₀ φ
    (exists_numberField_projectiveKernel_comp_spectralProjection (F := F) hα hs φ)
  let T : nuclearEndomorphisms (spectralSobolevQuotient F (1/2) (neg_le_self hα) hs₀) := ⟨_, hn⟩
  let series := spectralStripConvolution_trace_of_commonKernel (F := F) (1/2) χ hχ hα hs φ
    (spectralStripJet_commonKernel_direct (F := F) (a := 1/2) χ hχ hα hs₀) T rfl
  exact (hasSum_heckeZeros_of_closedStripJetSum (α := 1/2) (s := 3) φ χ S hS hi
    series.1 series.2).1

private theorem exists_shifted_test (φ : BruhatCompactSupport C𝔽) (b : ℝ) :
    ∃ ψ : BruhatCompactSupport C𝔽, ∀ g, ψ.val g = height(g) ^ (b : ℂ) * φ.val g := by
  have hsurj : Surjective m𝔽 := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.2.2.2.1
  have hw : modulationWeight m𝔽 b φ.val ∈ schwartzBruhatSubmodule C𝔽 :=
    modulationWeight_mem_schwartzBruhat m𝔽 univ ⟨b, mem_univ _⟩
      ⟨φ.val, bruhatCompactSupport_le_modulatedExponentialDecay m𝔽 univ hm𝔽 hsurj φ.property⟩
  refine ⟨⟨_, (mem_bruhatSmoothSubmodule_iff _).2
    (schwartzBruhat_isBruhatSmooth (G := C𝔽) ⟨_, hw⟩), φ.property.2.mul_left⟩, ?_⟩
  intro g
  change ((((ideleClassNorm F g).val : ℝ) ^ b : ℝ) : ℂ) * φ.val g = _
  rw [Complex.ofReal_cpow (ideleClassNorm F g).val.coe_nonneg]

private theorem mellin_shift_factor (h p c z : ℂ) (a : ℝ) (hh : h ≠ 0) :
    (h ^ (((a+1/2 : ℝ) : ℂ)) * p) * (c * h ^ (z-1/2)) =
      p * (c * h ^ z) * h ^ (a : ℂ) := by
  have hadd : h ^ (((a+1/2 : ℝ) : ℂ)) * h ^ (z-1/2) = h ^ z * h ^ (a : ℂ) := by
    rw [← Complex.cpow_add _ _ hh, ← Complex.cpow_add _ _ hh]
    congr 1
    push_cast
    ring
  calc
    _ = (p * c) * (h ^ (((a+1/2 : ℝ) : ℂ)) * h ^ (z-1/2)) := by ring
    _ = _ := by rw [hadd]; ring

private theorem centered_mellin_shift (φ ψ : BruhatCompactSupport C𝔽) (a : ℝ)
    (hψ : ∀ x, ψ.val x = height(x) ^ (((a+1/2 : ℝ) : ℂ)) * φ.val x)
    (χ : PontryaginDual C𝔽) (ρ : ℂ) :
    M(ψ, χ, ρ-1/2) = ∫ x, φ.val x * (ideleClassNormTwist χ ρ) x * height(x) ^ (a : ℂ) ∂μ𝔽 := by
  simp only [modulatedFourierMellin, relativeVerticalStrip, preimage_univ, indicator_univ]
  refine integral_congr_ae (.of_forall fun x ↦ ?_)
  change ψ.val x * ((χ x : ℂ) * height(x) ^ (ρ-1/2)) =
    φ.val x * ((χ x : ℂ) * height(x) ^ ρ) * height(x) ^ (a : ℂ)
  rw [hψ]
  exact mellin_shift_factor _ _ _ _ _ (Complex.ofReal_ne_zero.mpr
    (NNReal.coe_pos.mpr (Units.zero_lt _)).ne')

/-- Paper: Lemma B.4.4.9, pp. 624–625. For any continuous norm section, every
subset of the completed Hecke zeros, every compact Bruhat test and every real
norm twist, the Mellin evaluations form an absolutely summable family.
Deviation: Each zero is counted with its multiplicity. Nuclearity of the
centered quotient convolution supplies convergence directly. Footnotes 25–26
on p. 624 identify the extra density control needed by the printed argument. -/
theorem summable_ideleClassMellin_completedHeckeZeros_of_projected_convolution
    (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (Z : Set (chartZeros(τ))) (φ : BruhatCompactSupport C𝔽) (a : ℝ) :
    Summable (fun z : Z ↦ ‖((MeromorphicOn.divisor (explicitFormulaCompletedHeckeL z.val.val.1.val)
      univ z.val.val.2 : ℤ) : ℂ) *
      (∫ x, φ.val x * (ideleClassNormTwist z.val.val.1.val z.val.val.2) x * height(x) ^ (a : ℂ) ∂μ𝔽)‖) := by
  obtain ⟨ψ, hψ⟩ := exists_shifted_test φ (a+1/2)
  let e := normSectionCharacterEquiv τ hτ
  let χ (ξ : X) := (e ξ).val
  let S := {p : X × ℂ | 0 < D(χ p.1) p.2}
  let j (z : Z) : S := ⟨(e.symm z.val.val.1, z.val.val.2), by
    change 0 < D((e (e.symm z.val.val.1)).val) z.val.val.2
    rw [e.apply_symm_apply]
    exact z.val.property⟩
  have hj : Injective j := by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext (e.symm.injective (congrArg (fun p : S ↦ p.val.1) he))
      (congrArg (fun p : S ↦ p.val.2) he)
  have h := centered_full_divisor_summable χ (isSpectralBasepointChoice_normSection τ hτ) ψ
  refine (h.comp_injective hj).congr fun z ↦ ?_
  change ‖((D((e (e.symm z.val.val.1)).val) z.val.val.2 : ℤ) : ℂ) *
    M(ψ, (e (e.symm z.val.val.1)).val, z.val.val.2-1/2)‖ = _
  rw [e.apply_symm_apply, centered_mellin_shift φ ψ a hψ]
  rfl

end RiemannMasullo.StripNuclearity
