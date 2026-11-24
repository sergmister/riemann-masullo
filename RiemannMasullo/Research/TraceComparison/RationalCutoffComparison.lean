module

public import RiemannMasullo.Research.TraceComparison.RationalAnnularLimits
public import RiemannMasullo.Research.TraceComparison.GeometricWidthContinuity
public import RiemannMasullo.Research.TraceComparison.RationalComparisonData
public import RiemannMasullo.Research.StripNuclearity.RationalRealAnnihilator

/-! # Comparing the global strip diagonal with an actual rational S-local cutoff

On local-null tests in a prime-free interval the annular cutoff has zero
limit. Equality of that limit with the global integral therefore tests
exactly the missing arithmetic statement.
-/

@[expose] public noncomputable section

open Filter IsDedekindDomain MeasureTheory NumberField Set
open scoped ContDiff NNReal NumberField.AdeleRing Pointwise Topology
open RiemannMasullo.StripNuclearity RiemannMasullo.External.Grh
namespace RiemannMasullo

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 instSAdeleMeasurableSpaceSec1 instSIdeleLocallyCompactSec1
  instNormOneSIdeleQuotientMeasurableSpaceSec1 instSIdeleSecondCountableSec1

set_option quotPrecheck false
local notation "S₀" => (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))
local notation "I₀" => (SAdeleRing ℚ S₀)ˣ
local notation "H₀" => sProjectedDiagonal ℚ S₀
local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "μF" => ideleClassTamagawaMeasure ℚ
local notation "μI" => sMultiplicativeTamagawaMeasure ℚ S₀
local notation "vF" => ((normOneIdeleClassTamagawaMeasure ℚ) univ).toReal
local notation "vS" => ((sLocalNormOneQuotientMeasure ℚ S₀) univ).toReal
local notation "radial(" φ "," g ")" =>
  ∀ x : Cℚ, (φ : BruhatCompactSupport Cℚ).val x = rationalCenteredLogProfile g (Real.log (((ideleClassNorm ℚ) x).val : ℝ))
local notation "lifts(" B "," φ ")" => ∀ x : I₀, HasSum (fun ξ : H₀ ↦ (B : BruhatCompactSupport I₀).val (ξ.val*x))
  ((φ : BruhatCompactSupport Cℚ).val (QuotientGroup.mk (sIdeleInsertion ℚ S₀ x)))
local notation "localTrace(" B "," D "," t ")" => (((vF / vS : ℝ) : ℂ) *
  sLocalTraceAnnularOrbitSum (B : BruhatCompactSupport I₀) D ((t:ℝ)*(t*t))⁻¹ t (t*t))
local notation "diagonal(" φ "," hα "," hs "," U ")" =>
  (∫ x : Cℚ, dSequenceKernelSmoothening μF U
    (globalStripGeometricKernel (F := ℚ) (1/2) (hα).le
      (lt_of_lt_of_le (b := (3 : ℝ)) Nat.one_lt_ofNat hs) φ
      (exists_numberField_projectiveKernel_comp_spectralProjection (F := ℚ) (le_of_lt hα)
        (lt_of_lt_of_le (b := (3 : ℝ)) Nat.one_lt_ofNat hs) φ)) (x,x) ∂μF)
local instance joinedCutoffT2 : T2Space I₀ := (sIdeleGroup_description ℚ S₀).2.1

/-- Both geometric choices in the rational trace comparison exist. The local
domain is Borel and the global smoothing neighborhoods are symmetric,
relatively compact and open. -/
theorem exists_rational_annular_geometric_comparison_data :
    ∃ (D : Set I₀) (U : ℕ → Set Cℚ), MeasurableSet D ∧ IsFundamentalDomain H₀ D μI ∧
      IsDPrimeSequence μF U ∧ ∀ n, IsOpen (U n) ∧ IsCompact (closure (U n)) ∧ (U n)⁻¹ = U n := by
  let := finite_rational_empty_sProjectedDiagonal
  let : BorelSpace I₀ := sIdeleGroup_borelSpace
  obtain ⟨D,hD,hd⟩ := exists_borel_finite_subgroup_domain H₀ μI
  obtain ⟨U,hU,hu⟩ := exists_rational_regular_diagonal_sequence
  exact ⟨D,U,hD,hd,hU,hu⟩

local notation "polar(" g ")" => ((vF : ℂ) * (compactLogMellin g 0 + compactLogMellin g 1))

/-- Paper: Section 12.3, p. 514, and equations (12.5.1.2)–(12.5.1.4),
pp. 519–520. For rational tests at norms between one and two, the actual
annular S-local cutoff trace with its polar terms subtracted tends to the
actual projected global diagonal at every half-width at least one half.
Deviation: The wide-strip evaluation uses the classical rational contour
formula. The independent lower cutoff has radius t⁻³. -/
theorem rational_annularTrace_tendsto_wide_geometric_diagonal (g : ℝ → ℂ)
    (hg : ContDiff ℝ (∞) g) (hc : HasCompactSupport g) {a b α s : ℝ}
    (ha : 0 < a) (hb : b < Real.log 2) (hI : tsupport g ⊆ Icc a b) (hw : 1/2 ≤ α) (hs : 3 ≤ s)
    (φ : BruhatCompactSupport Cℚ) (hφ : radial(φ,g)) (B : BruhatCompactSupport I₀) (hB : lifts(B,φ))
    (D : Set I₀) (hD : IsFundamentalDomain H₀ D μI)
    (U : ℕ → Set Cℚ) (hU : IsDPrimeSequence μF U) (hm : ∀ n, MeasurableSet (U n)) :
    Tendsto (fun t : ℝ ↦ localTrace(B,D,t) - polar(g)) atTop
      (𝓝 diagonal(φ,(half_pos (zero_lt_one : (0:ℝ)<1)).trans_le hw,hs,U)) := by
  let J := ∫ x in Ioi (0:ℝ), g x / (1-Complex.exp (-2*(x:ℂ)))
  have h₀ : g 0 = 0 := image_eq_zero_of_notMem_tsupport fun ht ↦ (not_le.mpr ha) (hI ht).1
  have hglobal := (integral_rational_wide_diagonal_eq_weilLocal_sub_poles
    g hg hc h₀ φ hφ hw hs U hU hm).2
  rw [rationalWeilLocalValue_eq_primeFree_realIntegral g hg hc ha hb hI] at hglobal
  let G := (sIdeleQuotientNorm ℚ S₀).ker
  let : CompactSpace G := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm ℚ S₀).isCompact_preimage (isCompact_singleton (x:=1)))
  let M := sLocalNormOneQuotientMeasure ℚ S₀
  let : M.IsHaarMeasure := (sLocalNormOneQuotientMeasure_normProduct (F:=ℚ) (S:=S₀)).1
  have hv : (vS : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ENNReal.toReal_ne_zero.mpr
    ⟨isOpen_univ.measure_ne_zero M univ_nonempty, measure_ne_top M univ⟩)
  have hlocal := ((rational_annularTrace_two_limits_of_radial g hg.continuous ha hI φ hφ B hB D hD).2.const_mul
    (((vF/vS : ℝ) : ℂ))).sub_const polar(g)
  have he : (((vF/vS : ℝ) : ℂ) * ((vS : ℂ) * J) - polar(g)) =
      (vF : ℂ) * (J - compactLogMellin g 0 - compactLogMellin g 1) := by
    rw [Complex.ofReal_div, ← mul_assoc, div_mul_cancel₀ _ hv]
    ring
  rwa [hglobal, ← he]

/-- With narrow positive half-widths tending to one half, the difference
between the actual global strip integral and the polar-corrected additive
annular trace tends to zero. This holds for every rational prime-free radial
profile and every way of sending the cutoff radius to infinity. -/
theorem rational_annularTrace_geometric_diff_tendsto_zero_at_half (g : ℝ → ℂ)
    (hg : ContDiff ℝ (∞) g) (hc : HasCompactSupport g) {a b : ℝ}
    (ha : 0 < a) (hb : b < Real.log 2) (hI : tsupport g ⊆ Icc a b)
    (φ : BruhatCompactSupport Cℚ) (hφ : radial(φ,g)) (B : BruhatCompactSupport I₀) (hB : lifts(B,φ))
    (D : Set I₀) (hD : IsFundamentalDomain H₀ D μI)
    {T : Type*} {l : Filter T} (α s R : T → ℝ) (hα : ∀ t, 0 < α t) (hs : ∀ t, 3 ≤ s t)
    (hlim : Tendsto α l (𝓝 (1/2))) (hR : Tendsto R l atTop)
    (U : ℕ → Set Cℚ) (hU : IsDPrimeSequence μF U) (hm : ∀ n, MeasurableSet (U n)) :
    Tendsto (fun t ↦ centeredStripGeometricDiagonalIntegral φ (hα t) (hs t) U -
      (localTrace(B,D,R t) - polar(g))) l (𝓝 0) := by
  have h₀ : g 0 = 0 := image_eq_zero_of_notMem_tsupport fun ht ↦ (not_le.mpr ha) (hI ht).1
  have hz := rational_vanishes_on_kernel g h₀ φ hφ
  have hglobal := tendsto_centeredStripDiagonalIntegral_at_half φ hz α s hα hs hlim
    (σ:=3) le_rfl (fun _ ↦ U) U (fun _ ↦ hU) (fun _ ↦ hm) hU hm
  have hlocal : Tendsto (fun t ↦ localTrace(B,D,R t) - polar(g)) l
      (𝓝 (centeredStripGeometricDiagonalIntegral φ (half_pos (zero_lt_one : (0:ℝ)<1)) (s:=3) le_rfl U)) :=
    (rational_annularTrace_tendsto_wide_geometric_diagonal g hg hc ha hb hI
      (α:=1/2) le_rfl (s:=3) le_rfl φ hφ B hB D hD U hU hm).comp hR
  simpa only [sub_self] using hglobal.sub hlocal

/-- On the real-place annihilating family, the normalized actual annular
S-local trace tends to zero for every compact Bruhat lift. -/
theorem rational_annularTrace_realAnnihilator_tendsto_zero (f : ℝ → ℂ)
    (hf : ContDiff ℝ (∞) f) (hc : HasCompactSupport f) {a b : ℝ} (ha : 0 < a) (hI : tsupport f ⊆ Icc a b)
    (φ : BruhatCompactSupport Cℚ) (hφ : radial(φ,boundedRealAnnihilator f))
    (B : BruhatCompactSupport I₀) (hB : lifts(B,φ)) (D : Set I₀) (hD : IsFundamentalDomain H₀ D μI) :
    Tendsto (fun t : ℝ ↦ localTrace(B,D,t)) atTop (𝓝 0) := by
  obtain ⟨hd, -,hs⟩ := boundedRealAnnihilator_regularity f hf hc
  have h := (rational_annularTrace_two_limits_of_radial (boundedRealAnnihilator f) hd.continuous
    ha (hs.trans hI) φ hφ B hB D hD).2.const_mul (((vF/vS : ℝ) : ℂ))
  simpa only [boundedRealAnnihilator_realIntegral f hf hc ha hI, mul_zero] using h

/-- Paper: Section 12.3, p. 514, and the comparison used on p. 520. On a fixed
rational prime-free interval, agreement between the actual global geometric
diagonal and the limit of the actual S-local sharp annular kernel for all
positive half-widths and all real-place annihilating tests is equivalent to
ordinary RH. The sole arithmetic input is a sublinear dyadic count of the
omitted zeros at each width. All physical tests and S-unit lifts exist.
Deviation: Uses lower spatial radius t⁻³, upper spatial radius t and Fourier
radius t², with both polar terms zero on this family. -/
theorem rational_allWidths_annular_geometric_comparison_iff_riemannHypothesis
    {a b s : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < Real.log 2) (hs : 3 ≤ s)
    (hcount : ∀ α : ℝ, 0 < α → RationalOmittedZeroDyadicBound α s)
    (D : Set I₀) (hD : IsFundamentalDomain H₀ D μI)
    (U : ℕ → Set Cℚ) (hU : IsDPrimeSequence μF U) (hm : ∀ n, MeasurableSet (U n)) :
    (∀ α (hα : 0 < α) (f : ℝ → ℂ), ContDiff ℝ (∞) f → HasCompactSupport f → tsupport f ⊆ Icc a b →
      ∀ φ : BruhatCompactSupport Cℚ, radial(φ,boundedRealAnnihilator f) →
      ∀ B : BruhatCompactSupport I₀, lifts(B,φ) →
        Tendsto (fun t : ℝ ↦ localTrace(B,D,t)) atTop (𝓝 diagonal(φ,hα,hs,U))) ↔ RiemannHypothesis := by
  let := finite_rational_empty_sProjectedDiagonal
  have criterion := rational_allWidths_realAnnihilator_diagonal_zero_iff_riemannHypothesis_of_dyadicCount
    ha hab hb hs hcount U hU hm
  constructor
  · intro h
    apply criterion.mp
    intro α hα f hf hc hI φ hφ
    obtain ⟨hg,hgc,-⟩ := boundedRealAnnihilator_regularity f hf hc
    have hd : ContDiff ℝ (∞) (rationalCenteredLogProfile (boundedRealAnnihilator f)) :=
      (Complex.contDiff_exp.comp (Complex.ofRealCLM.contDiff.div_const 2)).mul hg
    obtain ⟨B, -, hB⟩ := exists_sLocalTraceLift_radial_of_finite (F:=ℚ) (S:=S₀) _ hd hgc.mul_left φ hφ
    exact tendsto_nhds_unique (h α hα f hf hc hI φ hφ B hB)
      (rational_annularTrace_realAnnihilator_tendsto_zero f hf hc ha hI φ hφ B hB D hD)
  · intro rh α hα f hf hc hI φ hφ B hB
    have he : diagonal(φ,hα,hs,U) = 0 := criterion.mpr rh α hα f hf hc hI φ hφ
    rw [he]
    exact rational_annularTrace_realAnnihilator_tendsto_zero f hf hc ha hI φ hφ B hB D hD


/-- Paper: Section 12.3, p. 514, and (12.5.1.4), p. 520. For a rational
prime-free radial test, continuity in the half-width of its actual projected
diagonal suffices to compare it with the polar-corrected annular local
trace at every positive half-width. Conversely, comparison at every width
implies continuity.
Deviation: The reference value is calibrated by the wide rational contour
formula, and the annular cutoff uses lower radius t⁻³. -/
theorem rational_continuous_diagonal_iff_annular_comparison (g : ℝ → ℂ)
    (hg : ContDiff ℝ (∞) g) (hc : HasCompactSupport g) {a b s : ℝ}
    (ha : 0 < a) (hb : b < Real.log 2) (hI : tsupport g ⊆ Icc a b) (hs : 3 ≤ s)
    (φ : BruhatCompactSupport Cℚ) (hφ : radial(φ,g)) (B : BruhatCompactSupport I₀) (hB : lifts(B,φ))
    (D : Set I₀) (hD : IsFundamentalDomain H₀ D μI)
    (U : ℕ → Set Cℚ) (hU : IsDPrimeSequence μF U) (hm : ∀ n, MeasurableSet (U n)) :
    let d (α : Ioi (0 : ℝ)) := centeredStripGeometricDiagonalIntegral φ α.property hs U
    Continuous d ↔ ∀ α, Tendsto (fun t : ℝ ↦ localTrace(B,D,t) - polar(g)) atTop (𝓝 (d α)) := by
  intro d
  let half : Ioi (0:ℝ) := ⟨1/2, half_pos zero_lt_one⟩
  have h₀ : g 0 = 0 := image_eq_zero_of_notMem_tsupport fun ht ↦ (not_le.mpr ha) (hI ht).1
  have crit : Continuous d ↔ ∀ α, d α = d half :=
    continuous_centeredStripDiagonalIntegral_iff_eq_wide φ (rational_vanishes_on_kernel g h₀ φ hφ)
      hs (fun _ ↦ U) (fun _ ↦ hU) (fun _ ↦ hm)
  have hw : Tendsto (fun t : ℝ ↦ localTrace(B,D,t) - polar(g)) atTop (𝓝 (d half)) :=
    rational_annularTrace_tendsto_wide_geometric_diagonal g hg hc ha hb hI (α:=1/2) le_rfl hs φ hφ B hB D hD U hU hm
  constructor
  · intro h α
    rw [crit.mp h α]
    exact hw
  · intro h
    exact crit.mpr fun α ↦ tendsto_nhds_unique (h α) hw

end RiemannMasullo
