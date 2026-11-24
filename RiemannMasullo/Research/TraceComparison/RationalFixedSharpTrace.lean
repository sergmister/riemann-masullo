module

public import RiemannMasullo.Research.TraceComparison.RationalZetaStrip
public import RiemannMasullo.Research.TraceComparison.RationalDirichletStrip
public import RiemannMasullo.Research.TraceComparison.SLocalAnnularCutoff
import RiemannMasullo.Research.TraceComparison.RationalComparisonData
import RiemannMasullo.Research.TraceComparison.RationalCutoffComparison
import RiemannMasullo.Research.TraceComparison.SLocalRadialLift
import RiemannMasullo.Research.TraceComparison.SLocalQuotient
import all RiemannMasullo.Research.TraceComparison.RationalAnnularLimits
import all RiemannMasullo.Research.StripNuclearity.RationalDiagonalDefect

/-! # Actual sharp S-local limits in a rational fixed strip -/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped ContDiff NNReal NumberField.AdeleRing Topology
open RiemannMasullo.External.Grh

namespace RiemannMasullo.StripNuclearity

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 instFiniteCompletionUnitsLocallyCompactSec4b
  instSAdeleMeasurableSpaceSec1 instSIdeleLocallyCompactSec1 instNormOneSIdeleQuotientMeasurableSpaceSec1
  instSIdeleSecondCountableSec1

set_option quotPrecheck false
local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "Kℚ" => (ideleClassNorm ℚ).ker
local notation "μℚ" => ideleClassTamagawaMeasure ℚ
local notation "Pr" => HeightOneSpectrum (𝓞 ℚ)
local notation "I(" S ")" => (SAdeleRing ℚ S)ˣ
local notation "Vℚ" => (((normOneIdeleClassTamagawaMeasure ℚ) univ).toReal : ℂ)
local notation "vS(" S ")" => (((sLocalNormOneQuotientMeasure ℚ S) univ).toReal : ℂ)
local notation "N(" x ")" => ((((ideleClassNorm ℚ (x : Cℚ)).val : ℝ)) : ℂ)
local notation "poles(" φ ")" => ((∫ x : Cℚ, (φ : BruhatCompactSupport Cℚ).val x * N(x)^(-1/2:ℂ) ∂μℚ) +
  (∫ x : Cℚ, (φ : BruhatCompactSupport Cℚ).val x * N(x)^(1/2:ℂ) ∂μℚ))
local instance fixedSharpSIdeleT2 (S : Finset Pr) : T2Space I(S) := (sIdeleGroup_description ℚ S).2.1

/-- Paper: Equation (12.4.1.24), p. 518. Convergence of the volume-adjusted sharp masses for every admissible
finite set containing T, every compact S-local lift of the test, and both polar terms. -/
def RationalSharpTraceLimit (T : Finset Pr) (φ : BruhatCompactSupport Cℚ) (value : ℂ) : Prop :=
  ∀ S : Finset Pr, T ⊆ S → Subsingleton (CommRing.Pic ((S : Set Pr).integer ℚ)) →
    (∀ v : Pr, differentIdeal ℤ (𝓞 ℚ) ≤ v.asIdeal → v ∈ S) →
    (∀ u : outsideIntegralIdeleUnits ℚ S, ∀ x : Cℚ, φ.val (QuotientGroup.mk u.val * x) = φ.val x) →
    ∀ B : BruhatCompactSupport I(S),
      (∀ x : I(S), HasSum (fun ξ : sProjectedDiagonal ℚ S ↦ B.val (ξ.val * x))
        (φ.val (QuotientGroup.mk (sIdeleInsertion ℚ S x)))) →
      Tendsto (fun R : ℝ ↦ Vℚ / vS(S) * (∑' ξ : sProjectedDiagonal ℚ S, sLocalTraceSharpMass B ξ R)
        - poles(φ)) atTop (𝓝 value)

private theorem rational_exists_sharp_limit_at_wide (τ : ℝ≥0ˣ →ₜ* Cℚ)
    (hτ : RightInverse τ (ideleClassNorm ℚ)) (φ : BruhatCompactSupport Cℚ) (hφ : ∀ x : Kℚ, φ.val x = 0) :
    ∃ T : Finset Pr, ∀ {s : ℝ} (hs : 3 ≤ s) (U : ℕ → Set Cℚ), IsDPrimeSequence μℚ U →
      (∀ n, MeasurableSet (U n)) → RationalSharpTraceLimit T φ
        (centeredStripGeometricDiagonalIntegral φ (by norm_num : (0:ℝ)<1/2) hs U) := by
  obtain ⟨T,hT⟩ := exists_finset_sharpMass_tendsto_diagonal_of_wide_or_inv_odd τ hτ φ hφ
  refine ⟨T, ?_⟩
  intro s hs U hU hm S hS hp hr ho B hB
  exact hT S hS hp hr ho B hB (α:=1/2) (by norm_num) hs U hU hm (Or.inl le_rfl)

/-- Paper: Section 12.3, p. 514, and (12.4.1.24), p. 518. For rational radial tests,
the sharp S-local trace converges to the actual global diagonal at every half-width
strictly greater than 3/8. The finite set may depend on the test.
Deviation: The input is the ordinary zeta seven-eighths theorem. -/
theorem rational_sharpMass_tendsto_of_zeta_seven_eighths
    (hn : ∀ {z : ℂ}, (7/8:ℝ) < z.re → riemannZeta z ≠ 0)
    (τ : ℝ≥0ˣ →ₜ* Cℚ) (hτ : RightInverse τ (ideleClassNorm ℚ))
    (g : ℝ → ℂ) (h₀ : g 0 = 0) (φ : BruhatCompactSupport Cℚ)
    (hφ : ∀ x : Cℚ, φ.val x = rationalCenteredLogProfile g (Real.log (((ideleClassNorm ℚ) x).val : ℝ))) :
    ∃ T : Finset Pr, ∀ {α s : ℝ} (hα : 3/8 < α) (hs : 3 ≤ s) (U : ℕ → Set Cℚ),
      IsDPrimeSequence μℚ U → (∀ n, MeasurableSet (U n)) →
      RationalSharpTraceLimit T φ (centeredStripGeometricDiagonalIntegral φ (show 0 < α by linarith) hs U) := by
  obtain ⟨T,hT⟩ := rational_exists_sharp_limit_at_wide τ hτ φ (rational_vanishes_on_kernel g h₀ φ hφ)
  refine ⟨T, ?_⟩
  intro α s hα hs U hU hm
  rw [rational_radial_diagonal_eq_wide_of_retained_zeta g h₀ φ hφ (by linarith) hs _ U hU hm]
  · exact hT hs U hU hm
  · intro z
    have hz := rational_centered_zero_band_of_riemannZeta_nonvanishing (7/8) (fun _ hh _ ↦ hn hh) z
    exact spectralStripMultiplicity_interior (abs_lt.mp (by linarith : |z.val.re-1/2| < α)) _ _

/-- Paper: Section 12.3, p. 514, and (12.4.1.24), p. 518. A right Dirichlet
zero-free half-plane gives the actual rational sharp trace comparison throughout
the open strips containing its reflected closed band.
Deviation: The zero-free half-plane is a separate input. -/
theorem rational_sharpMass_tendsto_of_dirichlet_band {σ : ℝ} (hσ : 1/2 ≤ σ)
    (hn : ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {z : ℂ},
      σ < z.re → ¬ (χ = 1 ∧ z = 1) → DirichletCharacter.LFunction χ z ≠ 0)
    (τ : ℝ≥0ˣ →ₜ* Cℚ) (hτ : RightInverse τ (ideleClassNorm ℚ)) (φ : BruhatCompactSupport Cℚ)
    (hφ : ∀ x : Kℚ, φ.val x = 0) :
    ∃ T : Finset Pr, ∀ {α s : ℝ} (hα : σ-1/2 < α) (hs : 3 ≤ s) (U : ℕ → Set Cℚ),
      IsDPrimeSequence μℚ U → (∀ n, MeasurableSet (U n)) →
      RationalSharpTraceLimit T φ (centeredStripGeometricDiagonalIntegral φ (show 0 < α by linarith) hs U) := by
  obtain ⟨T,hT⟩ := rational_exists_sharp_limit_at_wide τ hτ φ hφ
  refine ⟨T, ?_⟩
  intro α s hα hs U hU hm
  have hE := rational_isEmpty_exteriorZeros_of_dirichlet_band (by linarith : 0 ≤ σ) hn τ hτ hα
  rw [rational_diagonal_eq_wide_of_isEmpty_exterior τ hτ φ hφ (by linarith) hE hs hs U U hU hm hU hm]
  exact hT hs U hU hm

/-- Paper: Section 12.3, p. 514, and (12.4.1.24), p. 518. The same fixed-width
sharp comparison holds for every admissible rational test, including all angular
characters, under the Dirichlet seven-eighths nonvanishing theorem.
Deviation: The zero exclusion comes from outside the manuscript. -/
theorem rational_sharpMass_tendsto_of_dirichlet_seven_eighths
    (hn : ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {z : ℂ},
      (7/8:ℝ) < z.re → ¬ (χ = 1 ∧ z = 1) → DirichletCharacter.LFunction χ z ≠ 0)
    (τ : ℝ≥0ˣ →ₜ* Cℚ) (hτ : RightInverse τ (ideleClassNorm ℚ)) (φ : BruhatCompactSupport Cℚ)
    (hφ : ∀ x : Kℚ, φ.val x = 0) :
    ∃ T : Finset Pr, ∀ {α s : ℝ} (hα : 3/8 < α) (hs : 3 ≤ s) (U : ℕ → Set Cℚ),
      IsDPrimeSequence μℚ U → (∀ n, MeasurableSet (U n)) →
      RationalSharpTraceLimit T φ (centeredStripGeometricDiagonalIntegral φ (show 0 < α by linarith) hs U) := by
  obtain ⟨T,hT⟩ := rational_sharpMass_tendsto_of_dirichlet_band (by norm_num : (1/2:ℝ) ≤ 7/8) hn τ hτ φ hφ
  exact ⟨T,fun hα hs U hU hm ↦ hT (by linarith) hs U hU hm⟩

/-- Paper: Section 12.3, p. 514, and (12.4.1.4), p. 515. For any rational radial
test vanishing at norm one there exists an admissible finite set and a compact local
lift whose actual polar-corrected sharp trace converges to the global diagonal, with
the same lift for every half-width above 3/8.
Deviation: Uses seven-eighths nonvanishing for ordinary zeta and the §12.4 lift. -/
theorem exists_rational_sharpMass_comparison_of_zeta_seven_eighths
    (hn : ∀ {z : ℂ}, (7/8:ℝ) < z.re → riemannZeta z ≠ 0)
    (τ : ℝ≥0ˣ →ₜ* Cℚ) (hτ : RightInverse τ (ideleClassNorm ℚ))
    (g : ℝ → ℂ) (h₀ : g 0 = 0) (φ : BruhatCompactSupport Cℚ)
    (hφ : ∀ x : Cℚ, φ.val x = rationalCenteredLogProfile g (Real.log (((ideleClassNorm ℚ) x).val : ℝ))) :
    ∃ (S : Finset Pr) (B : BruhatCompactSupport I(S)),
      (∀ x : I(S), HasSum (fun ξ : sProjectedDiagonal ℚ S ↦ B.val (ξ.val * x))
        (φ.val (QuotientGroup.mk (sIdeleInsertion ℚ S x)))) ∧
      ∀ {α s : ℝ} (hα : 3/8 < α) (hs : 3 ≤ s) (U : ℕ → Set Cℚ),
        IsDPrimeSequence μℚ U → (∀ n, MeasurableSet (U n)) →
        Tendsto (fun R : ℝ ↦ Vℚ / vS(S) * (∑' ξ : sProjectedDiagonal ℚ S, sLocalTraceSharpMass B ξ R)
          - poles(φ)) atTop (𝓝 (centeredStripGeometricDiagonalIntegral φ (show 0 < α by linarith) hs U)) := by
  obtain ⟨T,hT⟩ := rational_sharpMass_tendsto_of_zeta_seven_eighths hn τ hτ g h₀ φ hφ
  obtain ⟨S,hS,hPic⟩ := (picard_uniformization ℚ T).1
  have hRam (v : Pr) (hv : differentIdeal ℤ (𝓞 ℚ) ≤ v.asIdeal) : v ∈ S := by
    exact (Finset.notMem_empty v (empty_rational_ramification v hv)).elim
  obtain ⟨π, -, hker, hnorm, -⟩ := exists_sLocalTraceQuotient (F:=ℚ) (S:=S) hPic
  have hout (u : outsideIntegralIdeleUnits ℚ S) (x : Cℚ) : φ.val (QuotientGroup.mk u.val * x) = φ.val x := by
    have hu : QuotientGroup.mk u.val ∈ π.toMonoidHom.ker := hker ▸ ⟨u.val,u.property,rfl⟩
    have he := (hnorm (QuotientGroup.mk u.val)).symm
    rw [show π (QuotientGroup.mk u.val) = 1 from hu, map_one] at he
    rw [hφ,hφ,map_mul,he,one_mul]
  obtain ⟨B,hB⟩ := exists_sLocalTraceLift (F:=ℚ) (S:=S) hPic φ hout
  exact ⟨S,B,hB,fun hα hs U hU hm ↦ hT hα hs U hU hm S hS hPic hRam hout B hB⟩

/-- Paper: Section 12.3, p. 514, and (12.5.1.4), p. 520. For every smooth compact
rational profile vanishing at zero, actual global and local test representatives and
a regular smoothing sequence exist. At half-width 2/5 and Sobolev order 3 their
sharp local trace tends to the global diagonal, which equals the full Weil value.
Deviation: The external zeta seven-eighths bound supplies the arithmetic input. -/
theorem exists_rational_two_fifths_trace_comparison
    (hn : ∀ {z : ℂ}, (7/8:ℝ) < z.re → riemannZeta z ≠ 0)
    (g : ℝ → ℂ) (hg : ContDiff ℝ (∞) g) (hc : HasCompactSupport g) (h₀ : g 0 = 0) :
    ∃ (φ : BruhatCompactSupport Cℚ) (U : ℕ → Set Cℚ) (S : Finset Pr) (B : BruhatCompactSupport I(S)),
      (∀ x : Cℚ, φ.val x = rationalCenteredLogProfile g (Real.log (((ideleClassNorm ℚ) x).val : ℝ))) ∧
      IsDPrimeSequence μℚ U ∧ (∀ n, MeasurableSet (U n)) ∧
      (∀ x : I(S), HasSum (fun ξ : sProjectedDiagonal ℚ S ↦ B.val (ξ.val * x))
        (φ.val (QuotientGroup.mk (sIdeleInsertion ℚ S x)))) ∧
      let d := centeredStripGeometricDiagonalIntegral φ (by norm_num : (0:ℝ) < 2/5) (le_refl (3:ℝ)) U
      Tendsto (fun R : ℝ ↦ Vℚ / vS(S) * (∑' ξ : sProjectedDiagonal ℚ S, sLocalTraceSharpMass B ξ R)
        - poles(φ)) atTop (𝓝 d) ∧
      d = Vℚ * (rationalWeilLocalValue g - compactLogMellin g 0 - compactLogMellin g 1) := by
  obtain ⟨φ,hφ⟩ := exists_rationalCenteredNormTest g hg hc
  obtain ⟨U,hU,hop⟩ := exists_rational_regular_diagonal_sequence
  have hm (n : ℕ) := (hop n).1.measurableSet
  let τ := (⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩ : IdeleGroup (𝓞 ℚ) ℚ →ₜ* Cℚ).comp
    ⟨canonicalIdeleNormSection ℚ, canonicalIdeleNormSection_continuous ℚ⟩
  obtain ⟨S,B,hB,hlim⟩ := exists_rational_sharpMass_comparison_of_zeta_seven_eighths hn
    τ (canonicalIdeleNormSection_rightInverse ℚ) g h₀ φ hφ
  have hr : (3/8:ℝ) < 2/5 := by norm_num
  exact ⟨φ,U,S,B,hφ,hU,hm,hB,hlim hr le_rfl U hU hm,
    rational_radial_diagonal_eq_weil_of_zeta_seven_eighths hn g hg hc h₀ φ hφ hr le_rfl U hU hm⟩

local notation "S₀" => (∅ : Finset Pr)

/-- Paper: Section 12.3, p. 514, and (12.5.1.4), p. 520. For a smooth profile
supported strictly between norms one and two, realize the two-fifths comparison
with the actual annular §12.4 orbital integral, a Borel fundamental domain, a
compact archimedean lift and a regular smoothing sequence.
Deviation: Uses the external zeta bound and the independent lower cutoff t⁻³. -/
theorem exists_rational_two_fifths_annular_trace_comparison
    (hn : ∀ {z : ℂ}, (7/8:ℝ) < z.re → riemannZeta z ≠ 0)
    (g : ℝ → ℂ) (hg : ContDiff ℝ (∞) g) (hc : HasCompactSupport g) {a b : ℝ}
    (ha : 0 < a) (hb : b < Real.log 2) (hI : tsupport g ⊆ Icc a b) :
    ∃ (φ : BruhatCompactSupport Cℚ) (U : ℕ → Set Cℚ) (B : BruhatCompactSupport I(S₀)) (D : Set I(S₀)),
      (∀ x : Cℚ, φ.val x = rationalCenteredLogProfile g (Real.log (((ideleClassNorm ℚ) x).val : ℝ))) ∧
      IsDPrimeSequence μℚ U ∧ (∀ n, MeasurableSet (U n)) ∧ MeasurableSet D ∧
      IsFundamentalDomain (sProjectedDiagonal ℚ S₀) D (sMultiplicativeTamagawaMeasure ℚ S₀) ∧
      (∀ x : I(S₀), HasSum (fun ξ : sProjectedDiagonal ℚ S₀ ↦ B.val (ξ.val * x))
        (φ.val (QuotientGroup.mk (sIdeleInsertion ℚ S₀ x)))) ∧
      let d := centeredStripGeometricDiagonalIntegral φ (by norm_num : (0:ℝ) < 2/5) (le_refl (3:ℝ)) U
      Tendsto (fun t : ℝ ↦ Vℚ / vS(S₀) * sLocalTraceAnnularOrbitSum B D (t*(t*t))⁻¹ t (t*t) -
        Vℚ * (compactLogMellin g 0 + compactLogMellin g 1)) atTop (𝓝 d) ∧
      d = Vℚ * (rationalWeilLocalValue g - compactLogMellin g 0 - compactLogMellin g 1) := by
  let := finite_rational_empty_sProjectedDiagonal
  obtain ⟨φ,hφ⟩ := exists_rationalCenteredNormTest g hg hc
  obtain ⟨D,U,hD,hfund,hU,hop⟩ := exists_rational_annular_geometric_comparison_data
  have hm (n : ℕ) := (hop n).1.measurableSet
  have hd : ContDiff ℝ (∞) (rationalCenteredLogProfile g) :=
    (Complex.contDiff_exp.comp (Complex.ofRealCLM.contDiff.div_const 2)).mul hg
  obtain ⟨B,-,hB⟩ := exists_sLocalTraceLift_radial_of_finite (F:=ℚ) (S:=S₀)
    (rationalCenteredLogProfile g) hd hc.mul_left φ hφ
  have h₀ : g 0 = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ (not_le.mpr ha) (hI h).1)
  have hthin := rational_radial_diagonal_eq_weil_of_zeta_seven_eighths hn g hg hc h₀ φ hφ
    (by norm_num : (3/8:ℝ) < 2/5) (le_refl (3:ℝ)) U hU hm
  have hwide := (integral_rational_wide_diagonal_eq_weilLocal_sub_poles g hg hc h₀ φ hφ
    (α:=1/2) le_rfl (le_refl (3:ℝ)) U hU hm).2
  refine ⟨φ,U,B,D,hφ,hU,hm,hD,hfund,hB,?_,hthin⟩
  rw [hthin.trans hwide.symm]
  simpa only [Complex.ofReal_div] using rational_annularTrace_tendsto_wide_geometric_diagonal g hg hc
    ha hb hI (α:=1/2) le_rfl (le_refl (3:ℝ)) φ hφ B hB D hfund U hU hm

end RiemannMasullo.StripNuclearity
