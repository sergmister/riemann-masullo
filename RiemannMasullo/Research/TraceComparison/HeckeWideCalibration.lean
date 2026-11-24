module

public import RiemannMasullo.Research.TraceComparison.GeometricWidthContinuity
public import RiemannMasullo.Research.StripNuclearity.NumberFieldExplicitFormula
import RiemannMasullo.Research.StripNuclearity.NormSectionCharacters
import RiemannMasullo.Research.StripNuclearity.OddTraceComparison

/-! # The wide projected diagonal and the all-place Weil distributions

For wide strips, the scalar idelic explicit formula calibrates the smoothed
global diagonal against the sharp S-local orbital masses of §12.4. At every
positive width, the joint limit of their difference gives exactly the exterior
Hecke zero sum of the missing comparison on pp. 514 and 520.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo.StripNuclearity

variable {F : Type*} [Field F] [NumberField F]

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 instFiniteCompletionUnitsLocallyCompactSec4b

set_option quotPrecheck false
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "K" => (ideleClassNorm F).ker
local notation "μ" => ideleClassTamagawaMeasure F
local notation "V" => (((normOneIdeleClassTamagawaMeasure F) univ).toReal : ℂ)
local notation "m𝔽" => (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "hm" => (⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ : IsModulation m𝔽)
local notation "height(" x ")" => ((((ideleClassNorm F x).val : ℝ) : ℂ))
local notation "M(" φ "," χ "," w ")" => modulatedFourierMellin m𝔽 univ hm μ
  (φ : BruhatCompactSupport C𝔽).val (ideleClassNormTwist (F:=F) χ w)
local notation "D(" χ ")" => MeromorphicOn.divisor (continuedCompletedHeckeL (F:=F) χ) univ
local notation "chart(" τ ")" => {η : PontryaginDual C𝔽 // ∀ t : ℝ≥0ˣ, η (τ t) = 1}
local notation "archTests" => (w : InfinitePlace F) → BruhatCompactSupport w.Completionˣ
local notation "primeTests" => (v : HeightOneSpectrum (𝓞 F)) → BruhatCompactSupport (v.adicCompletion F)ˣ
local notation "arch(" w ")" => IdeleClassGroup.ofCompletion (𝓞 F) F w
local notation "prime(" v ")" => IdeleClassGroup.ofAdicCompletion (𝓞 F) F v
local notation "finiteScale(" v ")" => ((Real.log ((v : HeightOneSpectrum (𝓞 F)).asIdeal.absNorm : ℝ) /
  (finiteLocalMultiplicativeTamagawaMeasure F v ((HeightOneSpectrum.adicCompletionIntegers F v).units :
    Set _)).toReal : ℝ) : ℂ)
local notation "polar(" φ ")" => ((∫ x : C𝔽, (φ : BruhatCompactSupport C𝔽).val x * height(x)^(-1/2:ℂ) ∂μ) +
  (∫ x : C𝔽, (φ : BruhatCompactSupport C𝔽).val x * height(x)^(1/2:ℂ) ∂μ))
local notation "localValue(" I "," P ")" => ((∑ w : InfinitePlace F, infiniteConnesWeilPrincipalValue w (I w)) +
  ∑' v : HeightOneSpectrum (𝓞 F), finiteScale(v) * finiteConnesWeilPrincipalValue v 1 (P v))

private theorem wide_classVolume_ne_zero : (V : ℂ) ≠ 0 := by
  let ν := normOneIdeleClassTamagawaMeasure F
  let : CompactSpace K := (ideleClassGroup_finiteness F).2.1
  let : ν.IsHaarMeasure := (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  exact Complex.ofReal_ne_zero.mpr (ENNReal.toReal_ne_zero.mpr
    ⟨isOpen_univ.measure_ne_zero ν univ_nonempty, measure_ne_top ν univ⟩)

private theorem wide_mellin_integral (φ : BruhatCompactSupport C𝔽) (χ : PontryaginDual C𝔽) (z : ℂ) :
    M(φ,χ,z-1/2) = ∫ x : C𝔽, φ.val x * (ideleClassNormTwist χ z) x * height(x)^(-1/2:ℂ) ∂μ := by
  simp only [modulatedFourierMellin, relativeVerticalStrip, preimage_univ, indicator_univ]
  apply integral_congr_ae (.of_forall fun x ↦ ?_)
  have hn : height(x) ≠ 0 := Complex.ofReal_ne_zero.mpr (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
  change φ.val x * ((χ x : ℂ) * height(x)^(z-1/2)) =
    φ.val x * ((χ x : ℂ) * height(x)^z) * height(x)^(-1/2:ℂ)
  rw [neg_div, sub_eq_add_neg, Complex.cpow_add _ _ hn]
  ring

/-- Paper: Theorem 12.5.1.1, pp. 519–520. When the half-width is at least
one half, the actual smoothed global diagonal equals the global norm-one
Tamagawa volume times the sum of the all-place Weil distributions, less both
polar integrals.
Deviation: Nuclear projected convolution supplies the absolute convergence
in the classical scalar Weil formula used for this calibration. -/
theorem wide_centeredStripDiagonalIntegral_eq_weilLocal_sub_poles
    (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (φ : BruhatCompactSupport C𝔽) (hφ : ∀ g : K, φ.val g = 0)
    {α s : ℝ} (ha : 1/2 ≤ α) (hs : 3 ≤ s) (U : ℕ → Set C𝔽)
    (hU : IsDPrimeSequence μ U) (hM : ∀ n, MeasurableSet (U n))
    (I : archTests) (hI : ∀ w u, (I w).val u = φ.val (arch(w) u))
    (P : primeTests) (hP : ∀ v u, (P v).val u = φ.val (prime(v) u)) :
    centeredStripGeometricDiagonalIntegral φ ((half_pos zero_lt_one).trans_le ha) hs U =
      V * localValue(I,P) - polar(φ) := by
  have hweil := idelicExplicitFormula_pointwise_of_projected_convolution τ hτ φ I hI P hP
  let e := normSectionCharacterEquiv τ hτ
  let χ (ξ : PontryaginDual K) := (e ξ).val
  let Z := {p : PontryaginDual K × ℂ // 0 < D(χ p.1) p.2}
  let W := {p : chart(τ) × ℂ // 0 < D(p.1.val) p.2}
  let E : Z ≃ W := {
    toFun := fun z ↦ ⟨(e z.val.1, z.val.2), z.property⟩
    invFun := fun z ↦ ⟨(e.symm z.val.1, z.val.2), by
      change 0 < D((e (e.symm z.val.1)).val) z.val.2
      rw [e.apply_symm_apply]
      exact z.property⟩
    left_inv := fun z ↦ by apply Subtype.ext; exact Prod.ext (e.symm_apply_apply _) rfl
    right_inv := fun z ↦ by apply Subtype.ext; exact Prod.ext (e.apply_symm_apply _) rfl }
  let aSum := ∑ w : InfinitePlace F, infiniteConnesWeilPrincipalValue w (I w)
  let pSum := ∑' v : HeightOneSpectrum (𝓞 F), finiteScale(v) * finiteConnesWeilPrincipalValue v 1 (P v)
  let d := centeredStripGeometricDiagonalIntegral φ ((half_pos zero_lt_one).trans_le ha) hs U
  have hG : HasSum (fun z : Z ↦ (D(χ z.val.1) z.val.2 : ℂ) * M(φ,χ z.val.1,z.val.2-1/2)) (-d) :=
    (hasSum_numberField_allHeckeZeros_neg_integral_smoothenedDiagonal φ hφ χ
      (isSpectralBasepointChoice_normSection τ hτ) ha hs U hU hM).2.2
  have hL := E.hasSum_iff.mpr (hweil.mul_left (V : ℂ))
  have h : HasSum (fun z : Z ↦ (D(χ z.val.1) z.val.2 : ℂ) * M(φ,χ z.val.1,z.val.2-1/2))
      (V * (polar(φ)/V-aSum-pSum)) := by
    apply hL.congr_fun
    intro z
    rw [wide_mellin_integral]
    change _ * _ = V * ((_ / V) * _)
    rw [← mul_assoc, mul_comm V (_ / V), div_mul_cancel₀ _ wide_classVolume_ne_zero]
    rfl
  have eq : -d = V * (polar(φ)/V-aSum-pSum) := hG.unique h
  change d = V * (aSum + pSum) - polar(φ)
  have hn := wide_classVolume_ne_zero (F:=F)
  rw [mul_sub, mul_sub, mul_comm V (polar(φ)/V), div_mul_cancel₀ _ hn] at eq
  linear_combination -eq

local notation "Pr" => HeightOneSpectrum (𝓞 F)
local notation "Idele(" S ")" => (SAdeleRing F S)ˣ
local notation "vS(" S ")" => (((sLocalNormOneQuotientMeasure F S) univ).toReal : ℂ)
local notation "cut(" B "," S "," R ")" =>
  (V / vS(S) * ∑' ξ : sProjectedDiagonal F S, sLocalTraceSharpMass B ξ R)

attribute [local instance] instSAdeleMeasurableSpaceSec1 instSIdeleLocallyCompactSec1
  instNormOneSIdeleQuotientMeasurableSpaceSec1 instSIdeleSecondCountableSec1

local instance wideSIdeleT2 (S : Finset Pr) : T2Space Idele(S) := (sIdeleGroup_description F S).2.1

/-- Paper: Section 12.3, p. 514, (12.4.1.24), p. 518, and (12.5.1.4), p. 520.
For any number field and test vanishing on norm-one classes, there is a finite
set of finite places outside which the local contributions vanish. For every larger
admissible set S and actual compact S-unit lift, the volume-adjusted sum of
the sharp S-local orbital masses, less both polar integrals, tends to the
actual smoothed global diagonal at every half-width at least one half.
For inversion-odd tests the two traces agree in this limit at every positive
width, by reflection in the Hecke functional equation.
Deviation: Uses the literal sharp masses of §12.4 and the classical wide
Weil formula. The Hilbert-space Paley–Wiener cutoff is a further comparison. -/
theorem exists_finset_sharpMass_tendsto_diagonal_of_wide_or_inv_odd
    (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (φ : BruhatCompactSupport C𝔽) (hφ : ∀ g : K, φ.val g = 0) :
    ∃ T : Finset Pr, ∀ (S : Finset Pr), T ⊆ S →
      Subsingleton (CommRing.Pic ((S : Set Pr).integer F)) →
      (∀ v : Pr, differentIdeal ℤ (𝓞 F) ≤ v.asIdeal → v ∈ S) →
      (∀ (u : outsideIntegralIdeleUnits F S) (x : C𝔽), φ.val (QuotientGroup.mk u.val * x) = φ.val x) →
      ∀ B : BruhatCompactSupport Idele(S),
        (∀ x : Idele(S), HasSum (fun ξ : sProjectedDiagonal F S ↦ B.val (ξ.val * x))
          (φ.val (QuotientGroup.mk (sIdeleInsertion F S x)))) →
        ∀ {α s : ℝ} (ha : 0 < α) (hs : 3 ≤ s) (U : ℕ → Set C𝔽),
          IsDPrimeSequence μ U → (∀ n, MeasurableSet (U n)) →
          (1/2 ≤ α ∨ ∀ x, φ.val x⁻¹ = -φ.val x) →
          Tendsto (fun R : ℝ ↦ cut(B,S,R) - polar(φ)) atTop
            (𝓝 (centeredStripGeometricDiagonalIntegral φ ha hs U)) := by
  classical
  choose RF hRF using fun v : Pr ↦ idelicExplicitFormula_finiteTestMap (F:=F) v
  let P (v : Pr) := RF v φ
  have hP (v : Pr) (x : (v.adicCompletion F)ˣ) : (P v).val x = φ.val (prime(v) x) := hRF v φ x
  let Q (v : Pr) := finiteConnesWeilPrincipalValue v 1 (P v)
  have hQ : {v : Pr | Q v ≠ 0}.Finite := idelicExplicitFormula_finite_support φ P hP
  refine ⟨hQ.toFinset, ?_⟩
  intro S hS hp hr hout B hB α s ha hs U hU hM hwidth
  let placeTerm (v : Pr) := finiteScale(v) * Q v
  have hsum : (∑' v : Pr, placeTerm v) = ∑ v : S, placeTerm v.val := by
    calc
      _ = ∑ v ∈ S, placeTerm v := tsum_eq_sum (fun v hv ↦ by
        have hz : Q v = 0 := by
          by_contra hz
          exact hv (hS (hQ.mem_toFinset.mpr hz))
        simp [placeTerm, hz])
      _ = _ := (Finset.sum_coe_sort S placeTerm).symm
  obtain ⟨I, b, M, hI, hb, hseries, hlim⟩ := sLocalTraceSharpMass_asymptotic φ hp hr hout B hB
  have he (v : S) : b v = P v.val := by
    apply Subtype.ext
    funext x
    exact (hb v x).trans (hP v.val x).symm
  have hvalue : centeredStripGeometricDiagonalIntegral φ ha hs U = V * localValue(I,P) - polar(φ) := by
    rcases hwidth with hwide | hodd
    · exact wide_centeredStripDiagonalIntegral_eq_weilLocal_sub_poles τ hτ φ hφ hwide hs U hU hM I hI P hP
    · have hhalf := wide_centeredStripDiagonalIntegral_eq_weilLocal_sub_poles τ hτ φ hφ
        (α:=1/2) le_rfl hs U hU hM I hI P hP
      have hzero := integral_centeredStripDiagonal_of_inv_odd φ hφ hodd (half_pos zero_lt_one) hs U hU hM
      exact (integral_centeredStripDiagonal_of_inv_odd φ hφ hodd ha hs U hU hM).trans (hzero.symm.trans hhalf)
  have h1 : φ.val 1 = 0 := by simpa using hφ (1 : K)
  simp only [h1, mul_zero, zero_mul, sub_zero, he] at hlim
  let G := (sIdeleQuotientNorm F S).ker
  let : CompactSpace G := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage (isCompact_singleton (x := 1)))
  let ν := sLocalNormOneQuotientMeasure F S
  let : ν.IsHaarMeasure := (sLocalNormOneQuotientMeasure_normProduct (F:=F) (S:=S)).1
  have hv : vS(S) ≠ 0 := Complex.ofReal_ne_zero.mpr (ENNReal.toReal_ne_zero.mpr
    ⟨isOpen_univ.measure_ne_zero ν univ_nonempty, measure_ne_top ν univ⟩)
  let c := (∑ w : InfinitePlace F, infiniteConnesWeilPrincipalValue w (I w)) +
    ∑ v : S, finiteScale(v.val) * Q v.val
  change Tendsto M atTop (𝓝 (vS(S) * c)) at hlim
  have hscaled := (hlim.const_mul (V/vS(S))).sub_const polar(φ)
  rw [← mul_assoc, div_mul_cancel₀ _ hv] at hscaled
  rw [hvalue]
  change Tendsto _ _ (𝓝 (V * ((∑ w : InfinitePlace F, infiniteConnesWeilPrincipalValue w (I w)) +
    ∑' v : Pr, finiteScale(v) * Q v) - polar(φ)))
  rw [hsum]
  apply hscaled.congr'
  filter_upwards [hseries] with R hR
  rw [hR.tsum_eq]

local notation "pos" => Ioi (0 : ℝ)
local notation "extZeros(" τ "," r ")" =>
  {p : chart(τ) × ℂ // 0 < D(p.1.val) p.2 ∧ r ≤ |p.2.re - 1/2|}
local notation "zeroTerm(" φ "," z ")" =>
  ((D((z).val.1.val) (z).val.2 : ℤ) : ℂ) * M(φ,(z).val.1.val,(z).val.2-1/2)

/-- Paper: Section 12.3, p. 514, (12.4.1.24), p. 518, and (12.5.1.4), p. 520.
The joint limit of the global diagonal minus the polar-corrected sharp S-local
trace equals the exterior Hecke zero sum, including full orders on both edges.
The global half-width approaches the target from below and the local cutoff
tends to infinity independently. The discrepancy tends to zero at every target
half-width at least one half, and at every positive width for an inversion-odd test.
Deviation: This identifies the missing comparison for the sharp cutoff. Its
vanishing at arbitrary narrower widths requires an independent argument. -/
theorem exists_finset_sharpMass_geometric_leftLimit_exteriorZeros
    (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (φ : BruhatCompactSupport C𝔽) (hφ : ∀ g : K, φ.val g = 0) :
    ∃ T : Finset Pr, ∀ (S : Finset Pr), T ⊆ S →
      Subsingleton (CommRing.Pic ((S : Set Pr).integer F)) →
      (∀ v : Pr, differentIdeal ℤ (𝓞 F) ≤ v.asIdeal → v ∈ S) →
      (∀ (u : outsideIntegralIdeleUnits F S) (x : C𝔽),
        φ.val (QuotientGroup.mk u.val * x) = φ.val x) →
      ∀ B : BruhatCompactSupport Idele(S),
        (∀ x : Idele(S), HasSum (fun ξ : sProjectedDiagonal F S ↦ B.val (ξ.val * x))
          (φ.val (QuotientGroup.mk (sIdeleInsertion F S x)))) →
        ∀ {s : ℝ} (hs : 3 ≤ s) (U : pos → ℕ → Set C𝔽), (∀ t, IsDPrimeSequence μ (U t)) →
          (∀ t n, MeasurableSet (U t n)) → ∀ r : pos,
          ∃ E : ℂ, HasSum (fun z : extZeros(τ,r.val) ↦ zeroTerm(φ,z)) E ∧
            Tendsto (fun p : pos × ℝ ↦ centeredStripGeometricDiagonalIntegral φ p.1.property hs (U p.1) -
              (cut(B,S,p.2) - polar(φ))) ((𝓝[<] r) ×ˢ (atTop : Filter ℝ)) (𝓝 E) ∧
            ((1/2 ≤ r.val ∨ ∀ x, φ.val x⁻¹ = -φ.val x) → E = 0) := by
  obtain ⟨T, hT⟩ := exists_finset_sharpMass_tendsto_diagonal_of_wide_or_inv_odd τ hτ φ hφ
  refine ⟨T, ?_⟩
  intro S hS hp hr hout B hB s hs U hU hM r
  let half : pos := ⟨1/2, half_pos zero_lt_one⟩
  obtain ⟨L, hL, hExt⟩ :=
    exists_leftLimit_centeredStripDiagonalIntegral_exteriorZeros τ hτ φ hφ hs U hU hM r
  have hlocal := hT S hS hp hr hout B hB half.property hs (U half) (hU half) (hM half) (Or.inl le_rfl)
  refine ⟨_, hExt, (hL.comp tendsto_fst).sub (hlocal.comp tendsto_snd), ?_⟩
  rintro (hwide | hodd)
  · exact hExt.unique (traceFormula_exteriorZeros_of_half_le τ φ hwide)
  · apply hExt.unique
    exact traceFormula_exteriorZeros_of_continuous_centeredStripDiagonalIntegral τ hτ φ hφ hs U hU hM
      (continuous_const.congr (fun t ↦
        (integral_centeredStripDiagonal_of_inv_odd φ hφ hodd t.property hs (U t) (hU t) (hM t)).symm)) r

end RiemannMasullo.StripNuclearity
