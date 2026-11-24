module

public import RiemannMasullo.Research.TraceComparison.GeometricWidthLimit
public import RiemannMasullo.Research.StripNuclearity.RationalZeroWindow
import all RiemannMasullo.Research.StripNuclearity.RationalZeroWindow
import all RiemannMasullo.Research.StripNuclearity.RationalDiagonalDefect

/-! # Growth of rational geometric diagonals under log translations

For a fixed compact profile, the growing translate has one exponential for
each ordinary zeta zero. Normalization at the edge of the classical critical
strip gives decay, even when the geometric half-width varies with the translate.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set
open scoped ContDiff NNReal Topology
open RiemannMasullo.External.Grh

namespace RiemannMasullo.StripNuclearity

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

set_option quotPrecheck false
local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "Kℚ" => (ideleClassNorm ℚ).ker
local notation "μℚ" => ideleClassTamagawaMeasure ℚ
local notation "Vℚ" => (((normOneIdeleClassTamagawaMeasure ℚ) univ).toReal : ℂ)
local notation "logN(" x ")" => Real.log (((ideleClassNorm ℚ) (x : Cℚ)).val : ℝ)
local notation "phys(" g "," y "," x ")" => rationalCenteredLogProfile g (logN(x) - y)
local notation "ord(" ψ ")" => MeromorphicOn.divisor (continuedCompletedHeckeL (F:=ℚ) ψ) univ
local notation "kept(" α "," s "," z ")" => spectralStripMultiplicity α s
  ((z : criticalStripZetaZeros).val.re - 1/2) (zetaZeroOrder z)
local notation "coeff(" g "," m "," z ")" =>
  (Vℚ * ((m : ℕ) : ℂ) * compactLogMellin g (z : criticalStripZetaZeros).val)

private def translatedUnshiftedProfile (g : ℝ → ℂ) (y x : ℝ) : ℂ :=
  Complex.exp (-(y : ℂ)/2) * g (x-y)

private theorem centered_translated_profile (g : ℝ → ℂ) (y x : ℝ) :
    rationalCenteredLogProfile (translatedUnshiftedProfile g y) x =
      rationalCenteredLogProfile g (x-y) := by
  simp only [rationalCenteredLogProfile, translatedUnshiftedProfile, Complex.ofReal_sub,
    ← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- Translating the physical log profile leaves it a compact Bruhat test on the rational idèle classes. -/
theorem exists_rational_translated_normTests (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    ∃ φ : ℝ → BruhatCompactSupport Cℚ, ∀ y x, (φ y).val x = phys(g,y,x) := by
  have h (y : ℝ) := exists_rationalCenteredNormTest (translatedUnshiftedProfile g y)
    (contDiff_const.mul (hg.comp (contDiff_id.sub contDiff_const)))
    ((hc.comp_homeomorph (Homeomorph.subRight y)).mul_left)
  choose φ hφ using h
  exact ⟨φ, fun y x ↦ (hφ y x).trans (centered_translated_profile g y _)⟩

private theorem compactLogMellin_translated_profile (g : ℝ → ℂ) (y : ℝ) (z : criticalStripZetaZeros) :
    compactLogMellin (translatedUnshiftedProfile g y) z.val =
      compactLogMellin g z.val * Complex.exp (shiftedZetaZero z * y) := by
  have h : compactLogMellin (translatedUnshiftedProfile g y) z.val =
      Complex.exp (-(y : ℂ)/2) * compactLogMellin (fun x ↦ g (x-y)) z.val := by
    unfold compactLogMellin translatedUnshiftedProfile
    rw [← integral_const_mul]
    exact integral_congr_ae (.of_forall (fun x ↦ mul_assoc _ _ _))
  rw [h, compactLogMellin_translate, mul_left_comm, ← Complex.exp_add]
  congr 2
  unfold shiftedZetaZero
  ring

/-- Paper: Equations (12.5.1.1)–(12.5.1.4), pp. 519–520. Translating a physical radial test
by y in log norm multiplies each ordinary zero contribution to its geometric diagonal
by exp((ρ − 1/2)y). The sign and norm-one volume are those of the actual global trace. -/
theorem hasSum_translatedZeta_neg_diagonal (g : ℝ → ℂ) (y : ℝ) (hzero : g (-y) = 0)
    (φ : BruhatCompactSupport Cℚ) (hφ : ∀ x, φ.val x = phys(g,y,x))
    {α s : ℝ} (hα : 0 < α) (hs : 3 ≤ s) (U : ℕ → Set Cℚ) (hU : IsDPrimeSequence μℚ U)
    (hM : ∀ n, MeasurableSet (U n)) :
    HasSum (fun z : criticalStripZetaZeros ↦ coeff(g,kept(α,s,z),z) * Complex.exp (shiftedZetaZero z * y))
      (-centeredStripGeometricDiagonalIntegral φ hα hs U) := by
  let k := translatedUnshiftedProfile g y
  have hk (x : Cℚ) : φ.val x = rationalCenteredLogProfile k (logN(x)) :=
    (hφ x).trans (centered_translated_profile g y _).symm
  have hk0 : k 0 = 0 := by simp [k, translatedUnshiftedProfile, hzero]
  let χ := (exists_spectralBasepointChoice_radially_trivial ℚ).choose
  have hχ : IsSpectralBasepointChoice χ := (exists_spectralBasepointChoice_radially_trivial ℚ).choose_spec.1
  let Z := {p : PontryaginDual Kℚ × ℂ // 0 < ord(χ p.1) p.2}
  let i (z : criticalStripZetaZeros) : Z := ⟨(1,z.val), by
    simp only [map_one, rational_heckeDivisor_at_zetaZero]
    exact_mod_cast zetaZeroOrder_pos z⟩
  have hi : Injective i := fun z z' h ↦ Subtype.ext (congrArg (fun p : Z ↦ p.val.2) h)
  have h := hasSum_keptHeckeZeros_neg_centeredStripDiagonalIntegral φ (rational_vanishes_on_kernel k hk0 φ hk)
    χ hχ hα hs U hU hM
  have hout (p : Z) (hp : p ∉ range i) : p.val.1 ≠ 1 := by
    intro h1
    have hD := p.property
    rw [h1, map_one] at hD
    exact hp ⟨⟨p.val.2, rational_zeta_of_heckeDivisor hD⟩, Subtype.ext (Prod.ext h1.symm rfl)⟩
  have hsum := (hi.hasSum_iff (f:=_) (fun p hp ↦ by
    rw [rational_radial_mellin_other k φ hk χ hχ (hout p hp), mul_zero])).mpr h
  apply hsum.congr_fun
  intro z
  dsimp only [i, comp_apply]
  rw [map_one, rational_heckeDivisor_at_zetaZero, Int.toNat_natCast, rationalCenteredNormTest_mellin k φ hk,
    compactLogMellin_translated_profile]
  ring

/-- A summable family of coefficients at the shifted ordinary zeros contributes
o(exp(y/2)) on positive log translates. The individual coefficients may vary
arbitrarily with y inside a single summable majorant. -/
theorem tendsto_normalized_zeta_exponentials (b : criticalStripZetaZeros → ℝ) (hb : Summable b)
    (k : ℝ → criticalStripZetaZeros → ℂ) (hk : ∀ y z, ‖k y z‖ ≤ b z) :
    Tendsto (fun y : ℝ ↦ Complex.exp (-(y : ℂ)/2) *
      ∑' z, k y z * Complex.exp (shiftedZetaZero z * y)) atTop (𝓝 0) := by
  let t (y : ℝ) (z : criticalStripZetaZeros) := k y z * Complex.exp ((shiftedZetaZero z - 1/2) * y)
  have hnorm (y : ℝ) (z : criticalStripZetaZeros) : ‖t y z‖ = ‖k y z‖ * Real.exp (((shiftedZetaZero z).re - 1/2) * y) := by
    simp [t, Complex.norm_exp, Complex.mul_re]
  have hlt (z : criticalStripZetaZeros) : (shiftedZetaZero z).re - 1/2 < 0 :=
    sub_neg.mpr ((le_abs_self _).trans_lt (abs_re_shiftedZetaZero_lt z))
  have h : Tendsto (fun y ↦ ∑' z, t y z) atTop (𝓝 (∑' _ : criticalStripZetaZeros, (0 : ℂ))) := by
    apply tendsto_tsum_of_dominated_convergence hb
    · intro z
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      apply squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _)
        (Eventually.of_forall fun y ↦ (hnorm y z).le.trans (mul_le_mul_of_nonneg_right (hk y z) (Real.exp_pos _).le))
      simpa only [Function.comp_apply, id_eq, mul_zero] using (Real.tendsto_exp_atBot.comp
        (tendsto_id.const_mul_atTop_of_neg (hlt z))).const_mul (b z)
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy z
      rw [hnorm]
      exact (mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (hlt z).le hy))).trans (hk y z)
  rw [tsum_zero] at h
  apply h.congr
  intro y
  rw [← tsum_mul_left]
  apply tsum_congr
  intro z
  have he : (shiftedZetaZero z - 1/2) * (y : ℂ) = (-(y : ℂ)/2) + shiftedZetaZero z*y := by ring
  simp only [t, he, Complex.exp_add]
  ring

private theorem translated_kept_le (α s : ℝ) (z : criticalStripZetaZeros) :
    kept(α,s,z) ≤ zetaZeroOrder z := by
  unfold spectralStripMultiplicity spectralBoundaryMultiplicity
  split_ifs <;> first | exact le_rfl | exact min_le_left _ _ | exact Nat.zero_le _

/-- Paper: Section 12.3, p. 514, and (12.5.1.4), p. 520. For every compact smooth
profile on the positive log half-line, its translated global diagonal divided by exp(y/2)
tends to zero. The half-width, Sobolev order and admissible smoothing sequence may
all depend on the translate.
Deviation: This endpoint estimate uses the classical open critical strip. It supplies
no fixed power saving at a smaller exponent. -/
theorem tendsto_normalized_translated_rational_diagonal (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (hzero : ∀ t ≤ 0, g t = 0)
    (φ : ℝ → BruhatCompactSupport Cℚ) (hφ : ∀ y x, (φ y).val x = phys(g,y,x))
    (α s : ℝ → ℝ) (hα : ∀ y, 0 < α y) (hs : ∀ y, 3 ≤ s y) (U : ℝ → ℕ → Set Cℚ)
    (hU : ∀ y, IsDPrimeSequence μℚ (U y)) (hM : ∀ y n, MeasurableSet (U y n)) :
    Tendsto (fun y : ℝ ↦ Complex.exp (-(y : ℂ)/2) *
      centeredStripGeometricDiagonalIntegral (φ y) (hα y) (hs y) (U y)) atTop (𝓝 0) := by
  let b (z : criticalStripZetaZeros) := ‖Vℚ‖ * ‖(zetaZeroOrder z : ℂ) * compactLogMellin g z.val‖
  let k (y : ℝ) (z : criticalStripZetaZeros) := coeff(g,kept(α y,s y,z),z)
  have hb : Summable b := ((completedZeta_explicit_formula hg hc).2.2.1).mul_left _
  have hk (y : ℝ) (z : criticalStripZetaZeros) : ‖k y z‖ ≤ b z := by
    simp only [k, b, mul_assoc, norm_mul, Complex.norm_natCast]
    gcongr
    exact_mod_cast translated_kept_le (α y) (s y) z
  have h := (tendsto_normalized_zeta_exponentials b hb k hk).neg
  rw [neg_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with y hy
  rw [(hasSum_translatedZeta_neg_diagonal g y (hzero (-y) (neg_nonpos.mpr hy)) (φ y) (hφ y)
    (hα y) (hs y) (U y) (hU y) (hM y)).tsum_eq]
  ring

/-- Almost every real exponential tilt of one prescribed compact profile has a nonzero
log-Mellin transform at every ordinary zeta zero. A nonzero total integral suffices.
The conclusion holds simultaneously for the countable family of zero locations. -/
theorem ae_real_tilt_mellin_ne_zero_at_all_zeta_zeros (g : ℝ → ℂ) (hg : Continuous g)
    (hc : HasCompactSupport g) (h0 : compactLogMellin g 0 ≠ 0) :
    ∀ᵐ b : ℝ, ∀ z : criticalStripZetaZeros, compactLogMellin g (z.val + (b : ℂ)) ≠ 0 := by
  let Z := {w : ℂ | compactLogMellin g w = 0}
  have hA : AnalyticOnNhd ℂ (compactLogMellin g) univ := fun z _ ↦ analyticAt_compactLogMellin hg hc z
  have hcod : Zᶜ ∈ codiscrete ℂ := by
    simpa only [Z, preimage_compl, preimage_singleton] using hA.preimage_zero_mem_codiscrete h0
  have hcount := (HereditarilyLindelofSpace.isLindelof Z).countable_of_isDiscrete
    (compl_mem_codiscrete_iff.mp hcod).2
  apply ae_all_iff.mpr
  intro z
  have hinj : Injective (fun b : ℝ ↦ z.val + (b : ℂ)) := fun _ _ e ↦ Complex.ofReal_injective (add_left_cancel e)
  rw [ae_iff]
  simpa [Z, Set.preimage] using (hcount.preimage hinj).measure_zero (volume : Measure ℝ)

end RiemannMasullo.StripNuclearity
