module

public import RiemannMasullo.Research.StripNuclearity.WindowComparison
public import RiemannMasullo.Research.StripNuclearity.LocalInversion
import RiemannMasullo.Ch03_IdelicZeta.Sec2

/-! # The global and local traces on inversion-odd tests

The functional equation pairs completed divisors with equal strip
multiplicities. For inversion-odd tests the geometric diagonal and the
sum of the polar terms vanish. The normalized local distributions have
the same symmetry.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo.StripNuclearity

variable {F : Type*} [Field F] [NumberField F]

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

set_option quotPrecheck false
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "X" => PontryaginDual C₁
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" => (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "hm𝔽" => (⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ : IsModulation m𝔽)
local notation "D(" χ ")" => MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ
local notation "zeros(" χ ")" => {z : X × ℂ // 0 < D(χ z.1) z.2}
local notation "M(" φ ", " χ ", " s ")" =>
  modulatedFourierMellin m𝔽 univ hm𝔽 μ𝔽 (φ : BruhatCompactSupport C𝔽).val (ideleClassNormTwist (F := F) χ s)
local notation "kept(" χ ", " α ", " s ", " z ")" =>
  spectralStripMultiplicity α s ((z).val.2.re - 1/2) (D(χ (z).val.1) (z).val.2).toNat

private theorem divisor_functionalEquation (χ : PontryaginDual C𝔽) (z : ℂ) :
    D(χ⁻¹) (1-z) = D(χ) z := by
  obtain ⟨hL, hl⟩ := continuedCompletedHeckeL_spec χ
  obtain ⟨hD, hd⟩ := continuedCompletedHeckeL_spec χ⁻¹
  obtain ⟨ε, hε, hne, hfe⟩ := completedHeckeL_continuation_functionalEquation χ _ _ hL hl hD hd
  have he : meromorphicOrderAt (fun s ↦ continuedCompletedHeckeL χ⁻¹ (1-s)) z =
      meromorphicOrderAt (continuedCompletedHeckeL χ⁻¹) (1-z) := by
    simpa [Function.comp_def] using meromorphicOrderAt_comp_of_deriv_ne_zero
      (f := continuedCompletedHeckeL χ⁻¹) (show AnalyticAt ℂ (fun s : ℂ ↦ 1-s) z by fun_prop)
      (show deriv (fun s : ℂ ↦ 1-s) z ≠ 0 by simp)
  rw [show (fun s ↦ continuedCompletedHeckeL χ⁻¹ (1-s)) = ε * continuedCompletedHeckeL χ from funext hfe,
    meromorphicOrderAt_mul_of_ne_zero (hε.analyticAt z) (hne z)] at he
  rw [MeromorphicOn.divisor_apply hD.meromorphicOn (mem_univ _),
    MeromorphicOn.divisor_apply hL.meromorphicOn (mem_univ _), ← he]

private theorem inv_mellin (φ : BruhatCompactSupport C𝔽) (hφ : ∀ x, φ.val x⁻¹ = -φ.val x)
    (χ : PontryaginDual C𝔽) (w : ℂ) : M(φ, χ⁻¹, -w) = -M(φ, χ, w) := by
  have hinv (g : C𝔽) : ideleClassNormTwist χ⁻¹ (-w) g = ideleClassNormTwist χ w g⁻¹ := by
    change (((χ⁻¹ g : Circle)) : ℂ) * ((((ideleClassNorm F g : ℝ≥0) : ℝ)) : ℂ) ^ (-w) =
      ((χ g⁻¹ : Circle) : ℂ) * ((((ideleClassNorm F g⁻¹ : ℝ≥0) : ℝ)) : ℂ) ^ w
    have hp : 0 < ((ideleClassNorm F g : ℝ≥0) : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
    have harg : (((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg hp.le]
      exact Real.pi_ne_zero.symm
    rw [map_inv χ g, map_inv (ideleClassNorm F) g, Units.val_inv_eq_inv_val, NNReal.coe_inv,
      Complex.ofReal_inv, Complex.inv_cpow _ _ harg, Complex.cpow_neg]
    rfl
  have hM (c : QuasiCharacter C𝔽) :
      modulatedFourierMellin m𝔽 univ hm𝔽 μ𝔽 φ.val c = ∫ g, φ.val g * c g ∂μ𝔽 := by
    unfold modulatedFourierMellin
    rw [Set.indicator_of_mem (by simp [relativeVerticalStrip])]
  rw [hM, hM, ← integral_inv_eq_self _ μ𝔽, ← integral_neg]
  apply integral_congr_ae
  filter_upwards with x
  rw [hφ, hinv, inv_inv, neg_mul]

private theorem multiplicity_reflect (α s b : ℝ) (m : ℕ) :
    spectralStripMultiplicity α s (-b) m = spectralStripMultiplicity α s b m := by
  unfold spectralStripMultiplicity
  have hi : (-α < -b ∧ -b < α) ↔ -α < b ∧ b < α := by constructor <;> rintro ⟨h,k⟩ <;> constructor <;> linarith
  have he : (-b = -α ∨ -b = α) ↔ b = -α ∨ b = α := by
    constructor <;> rintro (h | h) <;> first | left; linarith | right; linarith
  simp only [hi, he]

/-- A completed divisor and its functional-equation partner have opposite
Mellin contributions for an inversion-odd test, including the Sobolev edge weights. -/
theorem odd_keptHeckeZeroSum_eq_zero (φ : BruhatCompactSupport C𝔽) (hφ : ∀ x, φ.val x⁻¹ = -φ.val x)
    (χ : X →* PontryaginDual C𝔽) (α s : ℝ) {d : ℂ}
    (hs : HasSum (fun z : zeros(χ) ↦ (kept(χ, α, s, z) : ℂ) * M(φ, χ z.val.1, z.val.2-1/2)) (-d)) :
    d = 0 := by
  let invZ (z : zeros(χ)) : zeros(χ) :=
    ⟨(z.val.1⁻¹,1-z.val.2), by simpa only [map_inv, divisor_functionalEquation] using z.property⟩
  have hi : Involutive invZ := fun z ↦ Subtype.ext (Prod.ext (inv_inv _) (sub_sub_cancel _ _))
  let e := hi.toPerm invZ
  let term (z : zeros(χ)) := (kept(χ, α, s, z) : ℂ) * M(φ, χ z.val.1, z.val.2-1/2)
  have he (z : zeros(χ)) : term (e z) = -term z := by
    have hb : (1-z.val.2).re - 1/2 = -(z.val.2.re-1/2) := by rw [Complex.sub_re, Complex.one_re]; ring
    have hw : (1-z.val.2)-1/2 = -(z.val.2-1/2) := by ring
    change (spectralStripMultiplicity α s ((1-z.val.2).re-1/2) (D(χ z.val.1⁻¹) (1-z.val.2)).toNat : ℂ) *
      M(φ, χ z.val.1⁻¹, (1-z.val.2)-1/2) = _
    rw [map_inv, divisor_functionalEquation, hb, multiplicity_reflect, hw, inv_mellin φ hφ, mul_neg]
  have h := (show HasSum term (-d) from hs)
  have h₂ : HasSum (fun z ↦ term (e z)) (-d) := e.hasSum_iff.mpr h
  simp only [he] at h₂
  have hp := h.neg.unique h₂
  linear_combination hp / 2

local notation "chars" => (exists_spectralBasepointChoice_radially_trivial F)
local notation "oddDiagonal(" φ ", " hφ ", " ho ", " α ", " s ", " hα ", " hs ", " U ", " hU ", " hm ")" =>
  odd_keptHeckeZeroSum_eq_zero φ ho (chars).choose α s
    (hasSum_keptHeckeZeros_neg_centeredStripDiagonalIntegral (F := F) φ hφ (chars).choose (chars).choose_spec.1 hα hs U hU hm)

/-- Paper: Section 12.3, p. 514, and (12.5.1.4), p. 520. For every number field
and every positive width, the actual geometric diagonal of an inversion-odd
compact Bruhat test vanishing on the norm-one subgroup has integral zero. -/
theorem integral_centeredStripDiagonal_of_inv_odd
    (φ : BruhatCompactSupport C𝔽) (hφ : ∀ g : C₁, φ.val g = 0) (ho : ∀ x, φ.val x⁻¹ = -φ.val x)
    {α s : ℝ} (hα : 0 < α) (hs : 3 ≤ s) (U : ℕ → Set C𝔽)
    (hU : IsDPrimeSequence μ𝔽 U) (hm : ∀ n, MeasurableSet (U n)) :
    type_of% oddDiagonal(φ, hφ, ho, α, s, hα, hs, U, hU, hm) :=
  oddDiagonal(φ, hφ, ho, α, s, hα, hs, U, hU, hm)

/-- The two polar Mellin moments cancel for an inversion-odd test. -/
theorem polarMellin_sum_of_inv_odd (φ : BruhatCompactSupport C𝔽) (ho : ∀ x, φ.val x⁻¹ = -φ.val x) :
    M(φ, 1, 1/2) + M(φ, 1, -(1/2)) = 0 := by
  have h := inv_mellin φ ho 1 (1/2)
  rw [inv_one] at h
  rw [h, add_neg_cancel]

attribute [local instance] instFiniteCompletionUnitsLocallyCompactSec4b

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "atArch(" w ")" => IdeleClassGroup.ofCompletion (𝓞 F) F w
local notation "atFinite(" v ")" => IdeleClassGroup.ofAdicCompletion (𝓞 F) F v
local notation "archTests" => ((w : InfinitePlace F) → BruhatCompactSupport w.Completionˣ)
local notation "finiteTests" => ((v : V) → BruhatCompactSupport (v.adicCompletion F)ˣ)
local notation "classVolume" => (((normOneIdeleClassTamagawaMeasure F) univ).toReal : ℂ)
local notation "finiteTerm(" b ", " v ")" =>
  ((Real.log ((v : V).asIdeal.absNorm : ℝ) /
    (finiteLocalMultiplicativeTamagawaMeasure F v
      ((HeightOneSpectrum.adicCompletionIntegers F v).units : Set _)).toReal : ℝ) : ℂ) *
      finiteConnesWeilPrincipalValue v 1 (b v)

/-- Evaluate the corrected local expression of p. 520 on an inversion-odd test.
At the complex places the restriction is assumed zero near one. The finite
terms vanish individually and hence form a summable family. -/
theorem localTraceResidual_of_inv_odd (φ : BruhatCompactSupport C𝔽)
    (ho : ∀ x, φ.val x⁻¹ = -φ.val x) (a : archTests) (b : finiteTests)
    (ha : ∀ w u, (a w).val u = φ.val (atArch(w) u))
    (hb : ∀ v u, (b v).val u = φ.val (atFinite(v) u))
    (hn : ∀ w : InfinitePlace F, w.IsComplex → ∀ᶠ u in 𝓝 1, (a w).val u = 0) :
    Summable (fun v : V ↦ finiteTerm(b, v)) ∧
      classVolume * ((∑ w : InfinitePlace F, infiniteConnesWeilPrincipalValue w (a w)) +
        ∑' v : V, finiteTerm(b, v)) - M(φ, 1, 1/2) - M(φ, 1, -(1/2)) = 0 := by
  have hfin (v : V) : finiteConnesWeilPrincipalValue v 1 (b v) = 0 :=
    finiteWeilPrincipalValue_of_inv_odd v (b v) fun u ↦ by rw [hb, map_inv, ho, hb]
  have harch (w : InfinitePlace F) : infiniteConnesWeilPrincipalValue w (a w) = 0 :=
    infiniteWeilPrincipalValue_of_inv_odd w (a w) (fun u ↦ by rw [ha, map_inv, ho, ha]) (hn w)
  have hp := polarMellin_sum_of_inv_odd φ ho
  simp only [hfin, harch, mul_zero, summable_zero, Finset.sum_const_zero, tsum_zero,
    add_zero, zero_sub, true_and]
  linear_combination -hp

/-- Two vanishing traces give the local comparison with its two polar terms. -/
theorem odd_diagonal_local_agreement {d r : ℂ} {f : V → ℂ}
    (hd : d = 0) (hr : Summable f ∧ r = 0) : Summable f ∧ d = r :=
  ⟨hr.1, hd.trans hr.2.symm⟩

local notation "compareOdd(" φ ", " hφ ", " ho ", " hα ", " hs ", " U ", " hU ", " hm ", "
    a ", " b ", " ha ", " hb ", " hn ")" =>
  odd_diagonal_local_agreement
    (integral_centeredStripDiagonal_of_inv_odd (F := F) φ hφ ho hα hs U hU hm)
    (localTraceResidual_of_inv_odd φ ho a b ha hb hn)

/-- Paper: Section 12.3, p. 514, and the comparison on p. 520.
For every number field and every positive half-width, the actual geometric
diagonal equals the normalized local Weil expression minus both polar Mellin
terms for inversion-odd tests vanishing on the norm-one subgroup. The complex
place restrictions must vanish in a neighborhood of the identity.
Deviation: The local terms use the Fourier-defined principal values, the
normalized complex absolute value, and the finite-place Haar conversion. -/
theorem integral_centeredStripDiagonal_eq_localResidual_of_inv_odd
    (φ : BruhatCompactSupport C𝔽) (hφ : ∀ g : C₁, φ.val g = 0) (ho : ∀ x, φ.val x⁻¹ = -φ.val x)
    {α s : ℝ} (hα : 0 < α) (hs : 3 ≤ s) (U : ℕ → Set C𝔽) (hU : IsDPrimeSequence μ𝔽 U)
    (hm : ∀ n, MeasurableSet (U n)) (a : archTests) (b : finiteTests)
    (ha : ∀ w u, (a w).val u = φ.val (atArch(w) u))
    (hb : ∀ v u, (b v).val u = φ.val (atFinite(v) u))
    (hn : ∀ w : InfinitePlace F, w.IsComplex → ∀ᶠ u in 𝓝 1, (a w).val u = 0) :
    type_of% compareOdd(φ, hφ, ho, hα, hs, U, hU, hm, a, b, ha, hb, hn) :=
  compareOdd(φ, hφ, ho, hα, hs, U, hU, hm, a, b, ha, hb, hn)

end RiemannMasullo.StripNuclearity
