module

public import RiemannMasullo.Ch12_TraceGeometric.Sec5
public import RiemannMasullo.Research.StripNuclearity.AngularOperatorSum
public import RiemannMasullo.Research.StripNuclearity.HeckeAngularFourierCost
public import RiemannMasullo.Research.StripNuclearity.OpenStripDiagonal
public import RiemannMasullo.Research.StripNuclearity.UniformLift

/-! # The geometric diagonal for every number field

Convolution after spectral projection admits a projective tensor kernel.
The geometric diagonal therefore has the spectral expansion of (12.5.1.4)
with the multiplicities prescribed by the ambient Sobolev space.
-/

@[expose] public noncomputable section

open Function MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing ContDiff Topology

namespace RiemannMasullo.StripNuclearity

variable {F : Type*} [Field F] [NumberField F]

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

set_option quotPrecheck false
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" => (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "σ𝔽" => (⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩ :
  IdeleGroup (𝓞 F) F →ₜ* C𝔽).comp ⟨canonicalIdeleNormSection F, canonicalIdeleNormSection_continuous F⟩
local notation "projectedKernel(" hα ", " hs₀ ", " φ ")" =>
  (∃ K, sobolevProjectiveKernelOperator (F := F) hα hs₀ K =
    (hardySobolevTestAction μ𝔽 m𝔽 _ _ _ (neg_le_self hα) hs₀ φ).comp
      (spectralProjection (F := F) (1/2) hα hs₀))

private theorem projectedKernel_with_angular_coordinates
    (μK : Measure C₁) [μK.IsHaarMeasure] [IsProbabilityMeasure μK] [μK.WeaklyRegular]
    (χ : PontryaginDual C₁ →* PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    (hr : ∀ ξ t, χ ξ (σ𝔽 t) = 1) {α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s)
    (φ : BruhatCompactSupport C𝔽) : projectedKernel(hα, zero_le_one.trans hs.le, φ) := by
  let p (ξ : PontryaginDual C₁) (t : ℝ) :=
    ∫ k : C₁, φ.val (k.val * σ𝔽 (radialExponential (Multiplicative.ofAdd t))) * (ξ k : ℂ) ∂μK
  let supp := ideleClass_summable_angularProfile_derivatives μK φ
  let operators := ideleClass_hasSum_lifted_angular_convolutions μK χ hχ hr φ
    (neg_le_self hα) (zero_le_one.trans hs.le)
  let data := operators.choose_spec.choose_spec
  exact exists_projectiveKernel_of_radial_lift_sum (F := F) χ hχ hα hs operators.choose data.1
    supp.choose supp.choose_spec.1 p supp.choose_spec.2.1 operators.choose_spec.choose data.2.1
    _ data.2.2 (summable_admittedHeckeDivisorMass_angular_fourierCost φ μK χ hχ α s)

/-- Paper: Theorem 10.4.3.5(3), equation (10.4.3.45), p. 473. Over every number
field, convolution by a compact Bruhat test after the ambient spectral projection
at center one half admits a projective Sobolev tensor kernel for every nonnegative
half-width and every Sobolev order strictly greater than one.
Deviation: This proves the existence of a tensor giving the operator used in
Definition 10.4.3.7 (pp. 473–474) by summing angular convolution operators.
Convergence of the particular finite-rank sums in (10.4.3.42)–(43) is a
separate assertion (ERRATA I334 and I339). -/
theorem exists_numberField_projectiveKernel_comp_spectralProjection {α s : ℝ}
    (hα : 0 ≤ α) (hs : 1 < s) (φ : BruhatCompactSupport C𝔽) :
    projectedKernel(hα, zero_le_one.trans hs.le, φ) := by
  let : CompactSpace C₁ := (ideleClassGroup_finiteness F).2.1
  let μK : Measure C₁ := Measure.haarMeasure ⊤
  let : IsProbabilityMeasure μK := ⟨Measure.haarMeasure_self⟩
  let chars := exists_spectralBasepointChoice_radially_trivial F
  exact projectedKernel_with_angular_coordinates μK chars.choose chars.choose_spec.1
    chars.choose_spec.2 hα hs φ

local notation "kernelWitness(" hα ", " hs ", " φ ")" =>
  exists_numberField_projectiveKernel_comp_spectralProjection (F := F) (le_of_lt hα)
    (lt_of_lt_of_le (Nat.one_lt_ofNat : (1 : ℝ) < 3) hs) φ
local notation "diagonalFormula(" φ ", " hφ ", " χ ", " hχ ", " hα ", " hs ", " U ", " hU ", " hm ")" =>
  hasSum_stripZeros_neg_integral_smoothenedDiagonal (F := F)
    φ hφ χ hχ hα hs (kernelWitness(hα, hs, φ)) U hU hm

/-- Paper: Equation (12.5.1.4), p. 520. For a compact Bruhat test vanishing on
the norm-one classes, the smoothened geometric diagonal is Haar-integrable. Its
negative integral is the absolutely convergent sum of the Mellin values at the
admitted Hecke zeros, with their multiplicities. This holds for every number field.
Deviation: Page 519 specifies the interior of the strip. A zero on either edge
also contributes its Sobolev jets of degrees `k` below its multiplicity and
satisfying `2*k+1<s` (ERRATA F152). On zero-free edges the two counts agree. -/
theorem hasSum_numberField_stripZeros_neg_integral_smoothenedDiagonal
    (φ : BruhatCompactSupport C𝔽) (hφ : ∀ g : C₁, φ.val g = 0)
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    {α s : ℝ} (hα : 0 < α) (hs : 3 ≤ s) (U : ℕ → Set C𝔽)
    (hU : IsDPrimeSequence μ𝔽 U) (hBorel : ∀ n, MeasurableSet (U n)) :
    type_of% diagonalFormula(φ, hφ, χ, hχ, hα, hs, U, hU, hBorel) :=
  diagonalFormula(φ, hφ, χ, hχ, hα, hs, U, hU, hBorel)

local notation "openFormula(" φ ", " hφ ", " χ ", " hχ ", " hα ", " hs ", " U ", " hU ", " hm ", " he ")" =>
  hasSum_openStripZeros_neg_integral_smoothenedDiagonal (F := F) (hone_lt_three := Nat.one_lt_ofNat)
    φ hφ χ hχ hα hs (kernelWitness(hα, hs, φ)) U hU hm he

/-- Paper: Equation (12.5.1.4), p. 520. When the strip edges contain no zeros,
the negative integral of the smoothened geometric diagonal equals the
absolutely convergent sum over the interior completed Hecke zeros on p. 519.
Each zero appears with its full multiplicity. -/
theorem hasSum_numberField_openStripZeros_neg_integral_smoothenedDiagonal
    (φ : BruhatCompactSupport C𝔽) (hφ : ∀ g : C₁, φ.val g = 0)
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    {α s : ℝ} (hα : 0 < α) (hs : 3 ≤ s) (U : ℕ → Set C𝔽)
    (hU : IsDPrimeSequence μ𝔽 U) (hm : ∀ n, MeasurableSet (U n))
    (he : ∀ (ξ : PontryaginDual C₁) (ρ : ℂ),
      0 < MeromorphicOn.divisor (continuedCompletedHeckeL (χ ξ)) univ ρ → |ρ.re - 1/2| ≠ α) :
    type_of% openFormula(φ, hφ, χ, hχ, hα, hs, U, hU, hm, he) :=
  openFormula(φ, hφ, χ, hχ, hα, hs, U, hU, hm, he)

local notation "allFormula(" φ ", " hφ ", " χ ", " hχ ", " hw ", " hs ", " U ", " hU ", " hm ")" =>
  hasSum_allHeckeZeros_neg_integral_smoothenedDiagonal (F := F) (hone_lt_three := Nat.one_lt_ofNat)
    φ hφ χ hχ hw hs
    (kernelWitness((lt_of_lt_of_le (half_pos (zero_lt_one : (0 : ℝ) < 1)) hw), hs, φ)) U hU hm

/-- Paper: Equation (12.5.1.4), p. 520, and Proposition 3.2.1.3, p. 123.
At every half-width at least one half, including equality, the signed geometric
diagonal equals the full Hecke zero sum for every number field. The real parts
of the positive completed divisors lie strictly between zero and one. -/
theorem hasSum_numberField_allHeckeZeros_neg_integral_smoothenedDiagonal
    (φ : BruhatCompactSupport C𝔽) (hφ : ∀ g : C₁, φ.val g = 0)
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    {α s : ℝ} (hw : 1/2 ≤ α) (hs : 3 ≤ s) (U : ℕ → Set C𝔽)
    (hU : IsDPrimeSequence μ𝔽 U) (hm : ∀ n, MeasurableSet (U n)) :
    type_of% allFormula(φ, hφ, χ, hχ, hw, hs, U, hU, hm) :=
  allFormula(φ, hφ, χ, hχ, hw, hs, U, hU, hm)

end RiemannMasullo.StripNuclearity
