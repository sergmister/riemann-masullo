module

public import RiemannMasullo.Research.StripNuclearity.OddTraceComparison
public import RiemannMasullo.AppB_AnalyticNT.Sec4b

/-! # The odd trace comparison with canonical place restrictions -/

@[expose] public noncomputable section

open Filter IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo.StripNuclearity

variable {F : Type*} [Field F] [NumberField F]

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 instFiniteCompletionUnitsLocallyCompactSec4b

set_option quotPrecheck false
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "ι(" w ")" => IdeleClassGroup.ofCompletion (𝓞 F) F w
local notation "arch(" w ")" => idelicExplicitFormula_infiniteTestMap (F := F) w
local notation "fin(" v ")" => idelicExplicitFormula_finiteTestMap (F := F) v

theorem oddTrace_complex_restriction_zero (φ : BruhatCompactSupport C𝔽)
    (w : InfinitePlace F) (h : ∀ᶠ u in 𝓝 (1 : w.Completionˣ), φ.val (ι(w) u) = 0) :
    ∀ᶠ u in 𝓝 (1 : w.Completionˣ), ((arch(w)).choose φ).val u = 0 :=
  h.mono fun u hu ↦ ((arch(w)).choose_spec φ u).trans hu

local notation "oddWithPlaces(" φ ", " hφ ", " ho ", " hn ", " hα ", " hs ", " U ", " hU ", " hm ")" =>
  integral_centeredStripDiagonal_eq_localResidual_of_inv_odd φ hφ ho hα hs U hU hm
    (fun w ↦ (arch(w)).choose φ) (fun v ↦ (fin(v)).choose φ)
    (fun w ↦ (arch(w)).choose_spec φ) (fun v ↦ (fin(v)).choose_spec φ)
    (fun w hw ↦ oddTrace_complex_restriction_zero φ w (hn w hw))

/-- Paper: Section 12.3, p. 514, and p. 520. The global geometric diagonal
of an inversion-odd test agrees at every positive width with the normalized
principal values of its actual place restrictions minus both polar moments.
The test vanishes on the norm-one group, and each complex restriction
vanishes near the identity. The latter condition is empty over a totally
real field. -/
theorem integral_odd_centeredStripDiagonal_eq_restricted_localResidual
    (φ : BruhatCompactSupport C𝔽) (hφ : ∀ g : C₁, φ.val g = 0) (ho : ∀ x, φ.val x⁻¹ = -φ.val x)
    (hn : ∀ w : InfinitePlace F, w.IsComplex → ∀ᶠ u in 𝓝 (1 : w.Completionˣ), φ.val (ι(w) u) = 0)
    {α s : ℝ} (hα : 0 < α) (hs : 3 ≤ s) (U : ℕ → Set C𝔽) (hU : IsDPrimeSequence μ𝔽 U)
    (hm : ∀ k, MeasurableSet (U k)) :
    type_of% oddWithPlaces(φ, hφ, ho, hn, hα, hs, U, hU, hm) :=
  oddWithPlaces(φ, hφ, ho, hn, hα, hs, U, hU, hm)

end RiemannMasullo.StripNuclearity
