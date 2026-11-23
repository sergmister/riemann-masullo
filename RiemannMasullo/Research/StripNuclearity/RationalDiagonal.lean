module

public import RiemannMasullo.Ch12_TraceGeometric.Sec5
public import RiemannMasullo.Research.StripNuclearity.RationalProjectiveKernel

/-!
# The smoothened geometric diagonal on the rational idele classes

The projective kernel for rational compact convolution after spectral projection
supplies the kernel in the geometric diagonal formula at p. 520. The spectral
sum runs over the closed strip centered at 1/2, with the Sobolev multiplicities
at its two edges.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo.StripNuclearity

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "Kℚ" => (ideleClassNorm ℚ).ker
local notation "μℚ" => ideleClassTamagawaMeasure ℚ

-- Retain the exact proposition of the general theorem, including its chosen
-- geometric kernel, after substituting the proved rational kernel witness.
local notation "rationalDiagonalFormula(" φ ", " hφ ", " χ ", " hχ ", " hα ", " hs ", " U ", " hU ", " hm ")" =>
  hasSum_stripZeros_neg_integral_smoothenedDiagonal (F := ℚ) (hone_lt_three := Nat.one_lt_ofNat)
    φ hφ χ hχ hα hs (exists_rat_projectiveKernel_comp_spectralProjection (le_of_lt hα)
      (lt_of_lt_of_le (Nat.one_lt_ofNat : (1 : ℝ) < 3) hs) φ) U hU hm

/-- Paper: (12.5.1.4), p. 520. For a rational compact Bruhat test vanishing on
the norm-one subgroup and a Borel differentiation sequence, the smoothened
geometric diagonal is Haar-integrable. Its negative integral equals an absolutely
convergent sum over triples `(ω,b,t)` with `−α ≤ b ≤ α` and positive zero order
of the completed Hecke function of `χ ω` at `1/2 + b + it`. The summand is the
admitted multiplicity times the Fourier–Mellin transform of the test at the twist
`b + it`. The width is positive and the Sobolev order is at least three.

Deviation: The spectral sum counts the closed strip. Each interior zero has its
full multiplicity. A zero of order `m` on either edge contributes the jet orders
`k < m` satisfying `2*k+1 < s`. -/
theorem hasSum_rat_stripZeros_neg_integral_smoothenedDiagonal
    (φ : BruhatCompactSupport Cℚ) (hφ : ∀ g : Kℚ, φ.val g = 0)
    (χ : PontryaginDual Kℚ → PontryaginDual Cℚ) (hχ : IsSpectralBasepointChoice χ)
    {α s : ℝ} (hα : 0 < α) (hs : 3 ≤ s) (U : ℕ → Set Cℚ)
    (hU : IsDPrimeSequence μℚ U) (hBorel : ∀ n, MeasurableSet (U n)) :
    type_of% rationalDiagonalFormula(φ, hφ, χ, hχ, hα, hs, U, hU, hBorel) :=
  rationalDiagonalFormula(φ, hφ, χ, hχ, hα, hs, U, hU, hBorel)

end RiemannMasullo.StripNuclearity
