module

public import RiemannMasullo.Research.TraceComparison.RationalDedekindNonvanishing
public import RiemannMasullo.Research.TraceComparison.RationalTranslatedDiagonal
import all RiemannMasullo.Research.StripNuclearity.RationalDiagonalDefect

/-! # The rational radial trace inside a fixed zeta strip

For the trivial character only the ordinary zeta zeros contribute. A verified
half-plane of nonvanishing therefore gives the full all-place Weil value as soon
as the open strip contains the closed zero band. All heights are included.
-/

@[expose] public noncomputable section

open MeasureTheory NumberField Set
open scoped ContDiff NNReal
open RiemannMasullo.External.Grh

namespace RiemannMasullo.StripNuclearity

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

set_option quotPrecheck false
local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "μℚ" => ideleClassTamagawaMeasure ℚ
local notation "Vℚ" => (((normOneIdeleClassTamagawaMeasure ℚ) univ).toReal : ℂ)
local notation "radial(" φ "," g ")" => (∀ x : Cℚ, (φ : BruhatCompactSupport Cℚ).val x =
  rationalCenteredLogProfile g (Real.log (((ideleClassNorm ℚ) x).val : ℝ)))
local notation "retains(" α "," s "," z ")" => spectralStripMultiplicity α s
  ((z : criticalStripZetaZeros).val.re-1/2) (zetaZeroOrder z) = zetaZeroOrder z

/-- Paper: Section 12.3, p. 514. Retaining the whole multiplicity of every ordinary
zeta zero makes the smoothed global diagonal of a rational radial test equal its
wide-strip value, including for tests supported on both sides of norm one. -/
theorem rational_radial_diagonal_eq_wide_of_retained_zeta
    (g : ℝ → ℂ) (h₀ : g 0 = 0) (φ : BruhatCompactSupport Cℚ) (hφ : radial(φ,g))
    {α s : ℝ} (hα : 0 < α) (hs : 3 ≤ s) (hret : ∀ z, retains(α,s,z))
    (U : ℕ → Set Cℚ) (hU : IsDPrimeSequence μℚ U) (hm : ∀ n, MeasurableSet (U n)) :
    centeredStripGeometricDiagonalIntegral φ hα hs U =
      centeredStripGeometricDiagonalIntegral φ (by norm_num : (0:ℝ)<1/2) hs U := by
  let chars := exists_spectralBasepointChoice_radially_trivial ℚ
  have h := (rational_radial_missingJets_hasSum_iff g φ hφ chars.choose chars.choose_spec.1 α s _).mp
    (hasSum_missingHeckeJets_centeredStripDiagonalIntegral_sub φ (rational_vanishes_on_kernel g h₀ φ hφ)
      chars.choose chars.choose_spec.1 hα hs (β:=1/2) le_rfl hs U U hU hm hU hm).2
  have hh := h.congr_fun (g := fun _ ↦ (0 : ℂ)) (fun z ↦ by
    simp only [hret z, Nat.sub_self, Nat.cast_zero, zero_mul, mul_zero])
  exact sub_eq_zero.mp (hh.unique (hasSum_zero ..))

/-- Paper: Theorem 12.5.1.1, pp. 519–520. In every strip of half-width larger than
3/8, the geometric diagonal for a rational radial test equals the sum of the real
and all finite Weil contributions less both polar Mellin moments.
Deviation: Uses the ordinary zeta seven-eighths nonvanishing theorem as a separate
input; the half-width 2/5 is a concrete admissible choice. -/
theorem rational_radial_diagonal_eq_weil_of_zeta_seven_eighths
    (hn : ∀ {z : ℂ}, (7/8:ℝ) < z.re → riemannZeta z ≠ 0)
    (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (h₀ : g 0 = 0)
    (φ : BruhatCompactSupport Cℚ) (hφ : radial(φ,g)) {α s : ℝ} (hα : 3/8 < α) (hs : 3 ≤ s)
    (U : ℕ → Set Cℚ) (hU : IsDPrimeSequence μℚ U) (hm : ∀ n, MeasurableSet (U n)) :
    centeredStripGeometricDiagonalIntegral φ (show 0 < α by linarith) hs U =
      Vℚ * (rationalWeilLocalValue g - compactLogMellin g 0 - compactLogMellin g 1) := by
  have hret (z : criticalStripZetaZeros) : retains(α,s,z) := by
    have hz := rational_centered_zero_band_of_riemannZeta_nonvanishing (7/8) (fun _ hh _ ↦ hn hh) z
    exact spectralStripMultiplicity_interior (abs_lt.mp (by linarith : |z.val.re-1/2| < α)) _ _
  rw [rational_radial_diagonal_eq_wide_of_retained_zeta g h₀ φ hφ (by linarith) hs hret U hU hm]
  exact (integral_rational_wide_diagonal_eq_weilLocal_sub_poles g hg hc h₀ φ hφ
    (α:=1/2) le_rfl hs U hU hm).2

/-- Paper: Theorem 12.5.1.1, pp. 519–520. Ordinary RH implies the actual all-place
comparison for rational radial tests at *every* positive width.
Deviation: RH supplies the arithmetic input separately from the manuscript. -/
theorem rational_radial_diagonal_eq_weil_of_riemannHypothesis (hrh : RiemannHypothesis)
    (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (h₀ : g 0 = 0)
    (φ : BruhatCompactSupport Cℚ) (hφ : radial(φ,g)) {α s : ℝ} (hα : 0 < α) (hs : 3 ≤ s)
    (U : ℕ → Set Cℚ) (hU : IsDPrimeSequence μℚ U) (hm : ∀ n, MeasurableSet (U n)) :
    centeredStripGeometricDiagonalIntegral φ hα hs U =
      Vℚ * (rationalWeilLocalValue g - compactLogMellin g 0 - compactLogMellin g 1) := by
  rw [rational_radial_diagonal_eq_wide_of_retained_zeta g h₀ φ hφ hα hs
    ((zeta_all_windows_retain_iff_riemannHypothesis s).mpr hrh α hα) U hU hm]
  exact (integral_rational_wide_diagonal_eq_weilLocal_sub_poles g hg hc h₀ φ hφ
    (α:=1/2) le_rfl hs U hU hm).2

end RiemannMasullo.StripNuclearity
