module

public import RiemannMasullo.Research.TraceComparison.SLocalQuotient
public import RiemannMasullo.Research.StripNuclearity.QuotientTrace

/-! # The global strip diagonal evaluated on an S-local quotient

For a test invariant under the integral units outside S, the quotient
integral uses its own Tamagawa measure. Only the angular characters
trivial on those units contribute. No identification of additive and
multiplicative cutoff operators enters the formula.
-/

@[expose] public noncomputable section

open Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped ENNReal NNReal NumberField.AdeleRing

namespace RiemannMasullo.StripNuclearity

variable {F : Type*} [Field F] [NumberField F] {S : Finset (HeightOneSpectrum (𝓞 F))}

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1 instIdeleClassHaarMeasureSec1
  instSIdeleQuotientMeasurableSpaceSec1 instSIdeleQuotientBorelSpaceSec1 instSIdeleQuotientT2Sec1
  instSIdeleQuotientLocallyCompactSec1 instSIdeleQuotientSecondCountableSec1 instNormOneSIdeleQuotientMeasurableSpaceSec1

set_option quotPrecheck false
local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "Jₛ" => SIdeleQuotient F S
local notation "qF" => QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 F) F)
local notation "mS" => (⟨sIdeleQuotientNorm F S, (isProperMap_sIdeleQuotientNorm F S).continuous⟩ : Jₛ →ₜ* ℝ≥0ˣ)
local notation "vF" => (normOneIdeleClassTamagawaMeasure F) univ
local notation "vS" => (sLocalNormOneQuotientMeasure F S) univ
local notation "μF" => ideleClassTamagawaMeasure F
local notation "μS" => sLocalQuotientTamagawaMeasure F S
local notation "Q(" hp ")" => exists_sLocalTraceQuotient (F := F) (S := S) hp
local notation "B(" hp ", " φ ", " hout ")" => sLocalTraceQuotient_bruhat_descent
  (Q(hp)).choose (Q(hp)).choose_spec.1 (Q(hp)).choose_spec.2.1 (Q(hp)).choose_spec.2.2.1 φ hout

local notation "localJetSum(" hp ", " φ ", " hφ ", " hout ", " χ ", " hχ ", " hα ", " hs ", " U ", " hU ", " hm ")" =>
  hasSum_quotientMellin_neg_centeredStripDiagonalIntegral (Q(hp)).choose (Q(hp)).choose_spec.1
    mS (Q(hp)).choose_spec.2.2.1 μS (vF/vS)
    (sLocalTraceQuotient_map_tamagawa (Q(hp)).choose (Q(hp)).choose_spec.1.surjective (Q(hp)).choose_spec.2.2.1)
    φ hφ (B(hp, φ, hout)).exists.choose.val
    (continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp (B(hp, φ, hout)).exists.choose.property.1))
    (B(hp, φ, hout)).exists.choose_spec χ hχ hα hs U hU hm

/-- Paper: Section 12.3, p. 514, and the comparison on p. 520.
For trivial S-ideal class group, the negative global geometric diagonal of
an outside-unit-invariant test is the sum of the Mellin integrals of its
actual Bruhat descent, over the zero jets trivial on the forgotten units.
Each local integral is multiplied by the ratio of the global and S-local
norm-one volumes.
Deviation: The strip projection and its boundary weights are retained
in this S-local expression of the global integral. -/
theorem hasSum_sLocalJetMellin_neg_centeredStripDiagonalIntegral
    (hp : Subsingleton (CommRing.Pic ((S : Set V).integer F)))
    (φ : BruhatCompactSupport C𝔽) (hφ : ∀ g : C₁, φ.val g = 0)
    (hout : ∀ (u : outsideIntegralIdeleUnits F S) (x : C𝔽), φ.val (qF u.val * x) = φ.val x)
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    {α s : ℝ} (hα : 0 < α) (hs : 3 ≤ s) (U : ℕ → Set C𝔽) (hU : IsDPrimeSequence μF U)
    (hm : ∀ k, MeasurableSet (U k)) :
    type_of% localJetSum(hp, φ, hφ, hout, χ, hχ, hα, hs, U, hU, hm) :=
  localJetSum(hp, φ, hφ, hout, χ, hχ, hα, hs, U, hU, hm)

end RiemannMasullo.StripNuclearity
