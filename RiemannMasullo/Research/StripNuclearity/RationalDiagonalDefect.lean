module

public import RiemannMasullo.Research.StripNuclearity.NumberFieldDiagonal
public import RiemannMasullo.External.Grh.Theorems.RationalExplicitFormula
import RiemannMasullo.Ch01_Introduction.Sec4
import RiemannMasullo.Ch13_ZerosHecke.Targets

/-! # The projected rational diagonal and the classical explicit formula

Section 12.3, p. 514, leaves the comparison of the global and local traces
open. On any rational radial test and any centered half-width at least one
half, the independent contour formula for Riemann's zeta function evaluates
the global diagonal. The prime-power and real terms use Lebesgue log coordinates.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set
open scoped ContDiff FourierTransform NNReal Topology
open RiemannMasullo.External.Grh

namespace RiemannMasullo.StripNuclearity

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

set_option quotPrecheck false
local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "C₁" => (ideleClassNorm ℚ).ker
local notation "X" => PontryaginDual C₁
local notation "Uℚ" => PontryaginDual Cℚ
local notation "μℚ" => ideleClassTamagawaMeasure ℚ
local notation "Vℚ" => (((normOneIdeleClassTamagawaMeasure ℚ) univ).toReal : ℂ)
local notation "mℚ" => (⟨ideleClassNorm ℚ, (isProperMap_ideleClassNorm ℚ).continuous⟩ : Cℚ →ₜ* ℝ≥0ˣ)
local notation "hmℚ" => (⟨isProperMap_ideleClassNorm ℚ, ideleClassNorm_ne_one (F := ℚ)⟩ : IsModulation mℚ)
local notation "N(" x ")" => (((ideleClassNorm ℚ) (x : Cℚ)).val : ℝ)
local notation "M(" φ ", " ψ ", " w ")" =>
  modulatedFourierMellin mℚ univ hmℚ μℚ (φ : BruhatCompactSupport Cℚ).val (ideleClassNormTwist (F := ℚ) ψ w)
local notation "D(" ψ ")" => MeromorphicOn.divisor (continuedCompletedHeckeL (F := ℚ) ψ) univ
local notation "Lℚ" => continuedCompletedHeckeL (F := ℚ) (1 : Uℚ)

/-- The inverse shift turns an ordinary, unshifted compact Mellin profile
into the log profile of the idèle-class test at spectral center one half. -/
def rationalCenteredLogProfile (g : ℝ → ℂ) (t : ℝ) : ℂ :=
  Complex.exp ((t : ℂ) / 2) * g t

/-- Every smooth compact log profile gives an actual radial Bruhat test. -/
theorem exists_rationalCenteredNormTest (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) :
    ∃ φ : BruhatCompactSupport Cℚ, ∀ x, φ.val x = rationalCenteredLogProfile g (Real.log N(x)) := by
  apply exists_normTest (F := ℚ)
  · exact (Complex.contDiff_exp.comp ((Complex.ofRealCLM.contDiff).div_const 2)).mul hg
  · exact hc.mul_left

/-- The Mellin transform on the trivial rational component is the ordinary
compact log-Mellin transform with the norm-one Tamagawa volume. -/
theorem rationalCenteredNormTest_mellin (g : ℝ → ℂ) (φ : BruhatCompactSupport Cℚ)
    (hφ : ∀ x, φ.val x = rationalCenteredLogProfile g (Real.log N(x))) (w : ℂ) :
    M(φ, 1, w - 1 / 2) = Vℚ * compactLogMellin g w := by
  let A (t : ℝ) := rationalCenteredLogProfile g (Real.log t)
  have ha : ∀ x, φ.val x = introTraceTest 1 A x := by
    intro x
    simpa [introTraceTest, A] using hφ x
  have he := (introTraceTest_mellin (F := ℚ) 1 A φ ha (w - 1/2)).2
  simp only [modulatedFourierMellin, relativeVerticalStrip, preimage_univ, indicator_univ]
  rw [he]
  congr 1
  rw [introTraceMellin, mellin, ← integral_comp_exp, compactLogMellin]
  apply integral_congr_ae
  filter_upwards with x
  rw [Complex.real_smul, smul_eq_mul,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos x).ne'),
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp, Complex.ofReal_exp]
  simp only [A, rationalCenteredLogProfile, Real.log_exp]
  rw [show w * (x : ℂ) = x + x * (w - 1 / 2 - 1) + x / 2 by ring, Complex.exp_add, Complex.exp_add]
  ring

private theorem rational_radial_mellin_other (g : ℝ → ℂ) (φ : BruhatCompactSupport Cℚ)
    (hφ : ∀ x, φ.val x = rationalCenteredLogProfile g (Real.log N(x)))
    (χ : X →* Uℚ) (hχ : IsSpectralBasepointChoice χ) {ξ : X} (hn : ξ ≠ 1) (w : ℂ) :
    M(φ, χ ξ, w) = 0 := by
  obtain ⟨u, hu⟩ : ∃ u : C₁, ξ u ≠ 1 := by
    by_contra! h
    exact hn (ContinuousMonoidHom.ext h)
  have hc : ((χ ξ) u.val : ℂ) ≠ 1 := by
    rw [show χ ξ u.val = ξ u from DFunLike.congr_fun (hχ ξ) u]
    exact fun h ↦ hu (Subtype.ext h)
  let f (x : Cℚ) := φ.val x * ideleClassNormTwist (χ ξ) w x
  have tr (x : Cℚ) : f (u.val * x) = ((χ ξ) u.val : ℂ) * f x := by
    have hn : ideleClassNorm ℚ u.val = 1 := u.property
    have hp : φ.val (u.val*x) = φ.val x := by rw [hφ,hφ,map_mul,hn,one_mul]
    change φ.val _ * _ = _ * (φ.val x * _)
    rw [hp, map_mul]
    change _ * ((χ ξ u.val : ℂ) * (N(u.val) : ℂ) ^ w * _) = _
    simp only [hn]
    simp
    ring
  let I := ∫ x, f x ∂μℚ
  have hI : I = ((χ ξ) u.val : ℂ) * I := by
    rw [← integral_const_mul]
    exact (integral_mul_left_eq_self (μ := μℚ) f u.val).symm.trans (integral_congr_ae (.of_forall tr))
  simp only [modulatedFourierMellin, relativeVerticalStrip, preimage_univ, indicator_univ]
  exact (mul_eq_zero.mp (by linear_combination -hI : (((χ ξ) u.val : ℂ) - 1) * I = 0)).resolve_left
    (sub_ne_zero.mpr hc)

private theorem rational_zeta_order (z : ℂ) (hz : 0 < z.re) :
    meromorphicOrderAt riemannZeta z = meromorphicOrderAt Lℚ z :=
  meromorphicOrderAt_finiteHeckeL_continuation (1 : Uℚ)
    (by simpa only [DirichletCharacter.LFunction_modOne_eq] using
      meromorphic_dirichletLFunction (1 : DirichletCharacter ℂ 1))
    (fun s ↦ by rw [finiteHeckeL_one_eq_dedekindZeta, dedekindZeta_rat_eq_riemannZeta s.property]) hz

/-- At a classical nontrivial zeta zero, the multiplicity of the rational
trivial Hecke character agrees with the analytic zeta multiplicity. -/
theorem rational_heckeDivisor_at_zetaZero (r : criticalStripZetaZeros) :
    D(1) r.val = (zetaZeroOrder r : ℤ) := by
  obtain ⟨_, hp, h1⟩ := mem_criticalStripZetaZeros.mp r.property
  have hn : r.val ≠ 1 := fun he ↦ by simp [he] at h1
  have ha := analyticOn_riemannZeta r.val hn
  rw [MeromorphicOn.divisor_apply (continuedCompletedHeckeL_spec (1 : Uℚ)).1.meromorphicOn
    (mem_univ _), ← rational_zeta_order _ hp, ha.meromorphicOrderAt_eq, ← zetaZeroOrder_cast_eq]
  simp

private theorem rational_zeta_of_heckeDivisor {z : ℂ} (h : 0 < D(1) z) : z ∈ criticalStripZetaZeros := by
  obtain ⟨hp, h1⟩ := heckePositiveDivisor_open_strip (1 : Uℚ) h
  refine mem_criticalStripZetaZeros.mpr ⟨?_, hp, h1⟩
  by_contra hn
  have ha := analyticOn_riemannZeta z (show z ≠ 1 from fun he ↦ by simp [he] at h1)
  rw [MeromorphicOn.divisor_apply (continuedCompletedHeckeL_spec (1 : Uℚ)).1.meromorphicOn
    (mem_univ _), ← rational_zeta_order _ hp, ha.meromorphicOrderAt_eq, ha.analyticOrderAt_eq_zero.mpr hn] at h
  simp at h

local notation "radial(" φ ", " g ")" =>
  (∀ x : Cℚ, (φ : BruhatCompactSupport Cℚ).val x = rationalCenteredLogProfile g (Real.log N(x)))
local notation "term(" φ ", " χ ", " z ")" =>
  ((D(χ (z).val.1) (z).val.2 : ℤ) : ℂ) * M(φ, χ (z).val.1, (z).val.2 - 1/2)
local notation "Z(" χ ")" => {z : X × ℂ // 0 < D(χ z.1) z.2}

/-- The classical real-place integral and finite prime-power terms for a test
vanishing on the norm-one idèle classes. Its argument is the unshifted Mellin
profile, so the two finite-place weights are 1 and 1/n. -/
def rationalWeilLocalValue (g : ℝ → ℂ) : ℂ :=
  (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) *
    (g (Real.log n) + g (-Real.log n) / (n : ℂ))) +
  ∫ x in Ioi (0 : ℝ), (g x + Complex.exp (-(x : ℂ)) * g (-x)) /
    (1 - Complex.exp (-2 * (x : ℂ)))

private theorem rational_full_zeroSum (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (h₀ : g 0 = 0) :
    HasSum (fun ρ : criticalStripZetaZeros ↦ (zetaZeroOrder ρ : ℂ) * compactLogMellin g ρ.val)
      (compactLogMellin g 0 + compactLogMellin g 1 - rationalWeilLocalValue g) := by
  obtain ⟨_, _, hsum, heq⟩ := completedZeta_explicit_formula hg hc
  have h := hsum.of_norm.hasSum
  convert h using 1
  simp only [h₀, mul_zero, zero_mul, zero_sub] at heq
  have hneg (x : ℝ) : (-g x - Complex.exp (-(x : ℂ)) * g (-x)) /
      (1 - Complex.exp (-2 * (x : ℂ))) =
      -((g x + Complex.exp (-(x : ℂ)) * g (-x)) / (1 - Complex.exp (-2 * (x : ℂ)))) := by ring
  simp_rw [hneg] at heq
  rw [integral_neg] at heq
  unfold rationalWeilLocalValue
  linear_combination heq

/-- The zeros of the trivial rational component give the whole spectral sum
of a radial test. All other Fourier components vanish by Haar invariance. -/
theorem rational_radial_zeroSum (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (h₀ : g 0 = 0) (φ : BruhatCompactSupport Cℚ)
    (hφ : radial(φ, g)) (χ : X →* Uℚ) (hχ : IsSpectralBasepointChoice χ) :
    HasSum (fun z : Z(χ) ↦ term(φ, χ, z))
      (Vℚ * (compactLogMellin g 0 + compactLogMellin g 1 - rationalWeilLocalValue g)) := by
  classical
  let ι (r : criticalStripZetaZeros) : Z(χ) := ⟨(1,r.val), by
    simp only [map_one, rational_heckeDivisor_at_zetaZero]
    exact_mod_cast zetaZeroOrder_pos r⟩
  have hi : Injective ι := fun r t h ↦ Subtype.ext (congrArg (fun z : Z(χ) ↦ z.val.2) h)
  let f (z : Z(χ)) := term(φ, χ, z)
  apply (hi.hasSum_iff (f := f) (fun z hz ↦ ?_)).mp
  · apply ((rational_full_zeroSum g hg hc h₀).mul_left Vℚ).congr_fun
    intro r
    change ((D(χ 1) r.val : ℤ) : ℂ) * M(φ, χ 1, r.val - 1/2) = _
    rw [map_one, rational_heckeDivisor_at_zetaZero, rationalCenteredNormTest_mellin g φ hφ]
    push_cast
    ring
  · have hn : z.val.1 ≠ 1 := by
      intro h
      have hd := z.property
      rw [h,map_one] at hd
      exact hz ⟨⟨z.val.2,rational_zeta_of_heckeDivisor hd⟩, Subtype.ext (Prod.ext h.symm rfl)⟩
    change _ * M(φ, χ z.val.1, z.val.2 - 1/2) = 0
    rw [rational_radial_mellin_other g φ hφ χ hχ hn, mul_zero]

private theorem rational_diagonal_sign {d v a b c : ℂ} (h : -d = v * (a + b - c)) :
    d = v * (c - a - b) := by linear_combination -h

/-- A centered radial profile vanishing at log norm zero kills the norm-one classes. -/
theorem rational_vanishes_on_kernel (g : ℝ → ℂ) (h₀ : g 0 = 0)
    (φ : BruhatCompactSupport Cℚ) (hφ : radial(φ, g)) (u : C₁) : φ.val u = 0 := by
  rw [hφ, show ideleClassNorm ℚ u.val = 1 from u.property]
  simp [rationalCenteredLogProfile, h₀]

/-- A spectral series with a pole-minus-local value evaluates the corresponding diagonal. -/
theorem rational_compare_diagonal {Y ι : Type*} [MeasurableSpace Y] {μ : Measure Y}
    {d : Y → ℂ} {f : ι → ℂ} {v a b c : ℂ}
    (h : Integrable d μ ∧ Summable (fun i ↦ ‖f i‖) ∧ HasSum f (-∫ y, d y ∂μ))
    (h' : HasSum f (v * (a+b-c))) : Integrable d μ ∧ (∫ y, d y ∂μ) = v*(c-a-b) :=
  ⟨h.1, rational_diagonal_sign (h.2.2.unique h')⟩

local notation "charsℚ" => (exists_spectralBasepointChoice_radially_trivial ℚ)
local notation "calibrate(" g ", " hg ", " hc ", " h₀ ", " φ ", " hφ ", " hw ", " hs ", " U ", " hU ", " hm ")" =>
  rational_compare_diagonal
    (hasSum_numberField_allHeckeZeros_neg_integral_smoothenedDiagonal (F := ℚ) φ
      (rational_vanishes_on_kernel g h₀ φ hφ) (charsℚ).choose (charsℚ).choose_spec.1 hw hs U hU hm)
    (rational_radial_zeroSum g hg hc h₀ φ hφ (charsℚ).choose (charsℚ).choose_spec.1)

/-- Paper: Equations (12.5.1.1)–(12.5.1.4), pp. 519–520. The actual wide
projected diagonal of a smooth compact rational radial test equals the
classical real and finite contributions minus its two polar Mellin moments,
with the norm-one Tamagawa volume. The contour calculation is independent
of the idelic explicit-formula theorem and the omitted-zero assertion. -/
theorem integral_rational_wide_diagonal_eq_weilLocal_sub_poles
    (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (h₀ : g 0 = 0)
    (φ : BruhatCompactSupport Cℚ) (hφ : radial(φ, g)) {α s : ℝ} (hw : 1 / 2 ≤ α) (hs : 3 ≤ s)
    (U : ℕ → Set Cℚ) (hU : IsDPrimeSequence μℚ U) (hm : ∀ n, MeasurableSet (U n)) :
    type_of% calibrate(g, hg, hc, h₀, φ, hφ, hw, hs, U, hU, hm) :=
  calibrate(g, hg, hc, h₀, φ, hφ, hw, hs, U, hU, hm)

end RiemannMasullo.StripNuclearity
