module

public import RiemannMasullo.Research.StripNuclearity.RationalFiniteShells
public import RiemannMasullo.Research.StripNuclearity.WindowComparison

/-! # The rational local formula at an arbitrary positive half-width

The omitted divisor multiplicities are the exact correction to the normalized
sum of the local distributions for a positive-log radial test. The proof
combines the independent rational contour formula with the spectral expansion
of the constructed geometric kernel.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped ContDiff NNReal NumberField.AdeleRing Topology
namespace RiemannMasullo.StripNuclearity

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

set_option quotPrecheck false
local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "μℚ" => ideleClassTamagawaMeasure ℚ
local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local instance windowFiniteUnitsLocallyCompact (v : V) : LocallyCompactSpace (v.adicCompletion ℚ)ˣ :=
  letI : ProperSpace (v.adicCompletion ℚ) := properSpace_adicCompletion v
  inferInstance
local notation "U∞" => ((w : InfinitePlace ℚ) → BruhatCompactSupport w.Completionˣ)
local notation "U𝔭" => ((v : V) → BruhatCompactSupport (v.adicCompletion ℚ)ˣ)
local notation "radial(" φ ", " g ")" => (∀ x : Cℚ, (φ : BruhatCompactSupport Cℚ).val x =
  rationalCenteredLogProfile g (Real.log (((ideleClassNorm ℚ) x).val : ℝ)))
local notation "archRep(" A ", " φ ")" => (∀ (w : InfinitePlace ℚ) (u : w.Completionˣ),
  ((A : U∞) w).val u = (φ : BruhatCompactSupport Cℚ).val (IdeleClassGroup.ofCompletion (𝓞 ℚ) ℚ w u))
local notation "finRep(" B ", " φ ")" => (∀ (v : V) (u : (v.adicCompletion ℚ)ˣ),
  ((B : U𝔭) v).val u = (φ : BruhatCompactSupport Cℚ).val (IdeleClassGroup.ofAdicCompletion (𝓞 ℚ) ℚ v u))
local notation "chars" => exists_spectralBasepointChoice_radially_trivial ℚ
local notation "vanish(" g ", " ha ", " hp ", " φ ", " hφ ")" =>
  rational_vanishes_on_kernel g (image_eq_zero_of_notMem_tsupport fun ht ↦ (not_le.mpr ha) ((hp) ht).1) φ hφ

/-- Replacing the reference diagonal by its evaluated local expression
preserves the absolute sum and recovers the corrected diagonal. -/
theorem rationalWindow_of_two_evaluations {ι : Type*} {f : ι → ℂ} {d w ℓ : ℂ}
    (hd : Summable (fun i ↦ ‖f i‖) ∧ HasSum f (d-w)) (hw : w = ℓ) :
    Summable (fun i ↦ ‖f i‖) ∧ HasSum f (d-ℓ) ∧ d = ℓ + ∑' i, f i := by
  subst ℓ
  exact ⟨hd.1, hd.2, by rw [hd.2.tsum_eq]; ring⟩

local notation "balance(" g ", " hg ", " hc ", " ha ", " hp ", " φ ", " hφ ", " A ", " B ", " hA ", "
    hB ", " hα ", " hs ", " U ", " hU ", " hm ")" =>
  rationalWindow_of_two_evaluations
    (hasSum_missingHeckeJets_centeredStripDiagonalIntegral_sub (F := ℚ) φ (vanish(g, ha, hp, φ, hφ))
      (chars).choose (chars).choose_spec.1 hα hs (β := 1/2) le_rfl hs U U hU hm hU hm)
    (integral_rational_positive_log_diagonal_eq_principalValues_sub_poles g hg hc ha hp φ hφ
      A B hA hB (α := 1/2) le_rfl hs U hU hm)

/-- Paper: Section 12.3, p. 514, and (12.5.1.2)–(12.5.1.4), pp. 519–520.
For every positive rational half-width the geometric diagonal is the
norm-one volume times the actual sum of the local principal values minus
the polar moments, plus the absolutely convergent Mellin sum over the
missing zero jets.
Deviation: The correction is retained even at strip edges. The local
evaluation uses the classical contour formula only at wide width. -/
theorem integral_rational_window_eq_principalValues_sub_poles_add_missingJets
    (g : ℝ → ℂ) (hg : ContDiff ℝ (∞) g) (hc : HasCompactSupport g)
    {a b : ℝ} (ha : 0 < a) (hp : tsupport g ⊆ Icc a b)
    (φ : BruhatCompactSupport Cℚ) (hφ : radial(φ, g)) (A : U∞) (B : U𝔭)
    (hA : archRep(A, φ)) (hB : finRep(B, φ))
    {α s : ℝ} (hα : 0 < α) (hs : 3 ≤ s) (U : ℕ → Set Cℚ)
    (hU : IsDPrimeSequence μℚ U) (hm : ∀ k, MeasurableSet (U k)) :
    type_of% balance(g, hg, hc, ha, hp, φ, hφ, A, B, hA, hB, hα, hs, U, hU, hm) :=
  balance(g, hg, hc, ha, hp, φ, hφ, A, B, hA, hB, hα, hs, U, hU, hm)

end RiemannMasullo.StripNuclearity
