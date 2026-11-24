module

public import RiemannMasullo.AppB_AnalyticNT.Sec6
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import RiemannMasullo.AppB_AnalyticNT.Sec4b
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Gamma.Digamma

/-! # Estimates for the Hecke zero mass

A difference of logarithmic derivatives at two real points detects the
reciprocal-square mass of zeros in the critical strip. The comparison below
keeps the partial-fraction identity as an explicit hypothesis. The bounds
on the finite Euler series and the digamma function are unconditional.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped Topology

namespace RiemannMasullo.StripNuclearity

private theorem reciprocal_real_lower {x y : ℝ} (h₁ : 1 ≤ x) (h₂ : x ≤ 2) :
    1 / (2 * (1 + y ^ 2)) ≤ x / (x ^ 2 + y ^ 2) := by
  have hx : 0 < x := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg hx.le (sub_nonneg.mpr h₂),
    mul_nonneg (by linarith : 0 ≤ 2 * x - 1) (sq_nonneg y)]

/-- In the closed critical strip the real part of the paired Cauchy kernels
at two and minus one dominates a reciprocal-square height weight. -/
theorem heckeZeroWeight_le_reciprocalPair (z : ℂ) (h₀ : 0 ≤ z.re) (h₁ : z.re ≤ 1) :
    1 / (1 + |z.im|) ^ 2 ≤ (((2 : ℂ) - z)⁻¹ + (1 + z)⁻¹).re := by
  have hleft := reciprocal_real_lower (x := 2 - z.re) (y := z.im) (by linarith) (by linarith)
  have hright := reciprocal_real_lower (x := 1 + z.re) (y := z.im) (by linarith) (by linarith)
  have hheight : 1 / (1 + |z.im|) ^ 2 ≤ 1 / (1 + z.im ^ 2) := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [sq_abs z.im, abs_nonneg z.im]
  apply hheight.trans
  rw [Complex.add_re, Complex.inv_re, Complex.inv_re, Complex.normSq_apply,
    Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.add_re, Complex.sub_im, Complex.add_im,
    show (2 : ℂ).re = 2 by norm_num, Complex.one_re, show (2 : ℂ).im = 0 by norm_num, Complex.one_im, zero_sub,
    zero_add, ← sq, neg_sq]
  calc
    1 / (1 + z.im ^ 2) = 1 / (2 * (1 + z.im ^ 2)) + 1 / (2 * (1 + z.im ^ 2)) := by
      field_simp [show 1 + z.im ^ 2 ≠ 0 by positivity] <;> ring
    _ ≤ _ := add_le_add hleft hright

/-- A partial-fraction formula for the difference of logarithmic derivatives at
two and minus one bounds the full positive zero mass, with multiplicity. -/
theorem heckeZeroMass_le_of_hasSum_reciprocalPair {ι : Type*} (z : ι → ℂ) (m : ι → ℕ)
    (hstrip : ∀ i, 0 < m i → 0 ≤ (z i).re ∧ (z i).re ≤ 1) {value : ℂ}
    (hs : HasSum (fun i ↦ (m i : ℂ) * (((2 : ℂ) - z i)⁻¹ + (1 + z i)⁻¹)) value) :
    Summable (fun i ↦ (m i : ℝ) / (1 + |(z i).im|) ^ 2) ∧
      (∑' i, (m i : ℝ) / (1 + |(z i).im|) ^ 2) ≤ value.re := by
  have h := Complex.hasSum_re hs
  have hb (i : ι) : (m i : ℝ) / (1 + |(z i).im|) ^ 2 ≤
      ((m i : ℂ) * (((2 : ℂ) - z i)⁻¹ + (1 + z i)⁻¹)).re := by
    rcases Nat.eq_zero_or_pos (m i) with hm | hm
    · simp [hm]
    simpa [Complex.mul_re, div_eq_mul_inv] using
      mul_le_mul_of_nonneg_left (heckeZeroWeight_le_reciprocalPair (z i)
        (hstrip i hm).1 (hstrip i hm).2) (show 0 ≤ (m i : ℝ) by positivity)
  have hw := h.summable.of_nonneg_of_le (fun i ↦ by positivity) hb
  exact ⟨hw, h.tsum_eq ▸ hw.tsum_le_tsum hb h.summable⟩

variable {F : Type*} [Field F] [NumberField F]

private theorem unitary_idealWeight_bound
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (I : Ideal (𝓞 F)) :
    ‖heckeIdealVonMangoldt (ideleClassNormTwist χ 0) I‖ ≤ Real.log I.absNorm := by
  classical
  by_cases h : ∃ v : HeightOneSpectrum (𝓞 F), ∃ k : ℕ, 0 < k ∧ I = v.asIdeal ^ k
  · obtain ⟨v, k, hk, rfl⟩ := h
    have hq : (1 : ℝ) ≤ v.asIdeal.absNorm := by
      exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm v).le
    rw [heckeIdealVonMangoldt, heckeIdealValue_prime_pow _ v hk, idealVonMangoldt_prime_pow v hk,
      norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.log_nonneg hq), map_pow, Nat.cast_pow]
    split_ifs <;> simp only [norm_pow, norm_ideleClassNormTwist_zero_localValue, one_pow, one_mul,
      norm_zero, zero_mul]
    · exact Real.log_le_log (zero_lt_one.trans_le hq) (le_self_pow₀ hq hk.ne')
    · exact Real.log_nonneg (one_le_pow₀ hq)
  · simp [heckeIdealVonMangoldt, idealVonMangoldt, h, Real.log_natCast_nonneg]

/-- Paper: Equation (B.6.1.12), p. 638. The absolutely convergent ideal
Dirichlet series gives one bound for the finite logarithmic derivatives of
all unitary Hecke characters of a fixed field throughout Re(s) ≥ 2. -/
theorem exists_uniform_finiteHeckeL_logDeriv_bound (F : Type*) [Field F] [NumberField F] :
    ∃ C : ℝ, ∀ (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (L : ℂ → ℂ)
      (_hL : MeromorphicNFOn L univ)
      (_hSeries : ∀ s : Complex.re ⁻¹' Ioi (1 : ℝ), L s = finiteHeckeL χ s)
      (z : ℂ), 2 ≤ z.re → ‖logDeriv L z‖ ≤ C := by
  let M (I : {I : Ideal (𝓞 F) // I ≠ ⊥}) := (I.val.absNorm : ℝ) ^ (-(3/2 : ℝ)) / (1/2)
  have hM : Summable M :=
    ((summable_absNorm_rpow F (by norm_num : 1 < (3/2 : ℝ))).subtype (fun I ↦ I ≠ ⊥)).div_const _
  refine ⟨∑' I, M I, fun χ L hL hSeries z hz ↦ ?_⟩
  have hz' : 1 < z.re := by linarith
  have hS := (finiteHeckeL_logDeriv_hasSum_ideals χ L hL hSeries ⟨z, hz'⟩).2.2
  rw [← hS.tsum_eq]
  apply tsum_of_norm_bounded hM.hasSum
  intro I
  let q : ℝ := I.val.absNorm
  have hq : 0 < q := by
    dsimp [q]
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr I.property)
  have hq₁ : 1 ≤ q := by
    dsimp [q]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr I.property)
  change ‖-heckeIdealVonMangoldt _ I.val / (q : ℂ) ^ z‖ ≤ _
  rw [norm_div, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hq]
  calc
    _ ≤ (q ^ (1/2 : ℝ) / (1/2)) / q ^ z.re := by
      exact div_le_div_of_nonneg_right ((unitary_idealWeight_bound χ I.val).trans
        (Real.log_le_rpow_div hq.le (by norm_num : 0 < (1/2 : ℝ)))) (Real.rpow_nonneg hq.le _)
    _ = q ^ ((1/2 : ℝ) - z.re) / (1/2) := by rw [div_right_comm, Real.rpow_sub hq]
    _ ≤ M I := by
      exact div_le_div_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hq₁
        (show (1/2 : ℝ) - z.re ≤ -(3/2 : ℝ) by linarith)) (by norm_num)

/-- The Gauss integral gives a linear bound on the entire half-plane Re(z) ≥ 1
with a single constant. This permits both the archimedean angular and spectral
parameters of a Hecke character to vary. -/
theorem exists_uniform_digamma_bound :
    ∃ C ≥ (0 : ℝ), ∀ (u v : ℝ), 1 ≤ u →
      ‖Complex.digamma ((u : ℂ) + (v : ℂ) * Complex.I)‖ ≤ C * (1 + u + |v|) := by
  let K (x : ℝ) := (1 + x) * Real.exp (-x)
  have hExp := integrableOn_exp_mul_Ioi (show (-1 : ℝ) < 0 by norm_num) 0
  have hxExp : IntegrableOn (fun x : ℝ ↦ x * Real.exp (-x)) (Ioi 0) := by
    simpa using (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1)
      (by norm_num) one_pos (by norm_num : (0 : ℝ) < 1))
  have hK : IntegrableOn K (Ioi 0) := by
    simpa only [K, Pi.add_def, add_mul, one_mul, neg_one_mul] using hExp.add hxExp
  let A := ∫ x in Ioi (0 : ℝ), K x
  have ha : 0 ≤ A := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
    exact mul_nonneg (by linarith [show 0 < x from hx]) (Real.exp_pos _).le
  let D := ‖Complex.digamma 1‖
  have hd : 0 ≤ D := norm_nonneg _
  refine ⟨A + D, by positivity, fun u v hu ↦ ?_⟩
  let w : ℂ := (u : ℂ) + (v : ℂ) * Complex.I
  have hw : 0 < (w / (1 : ℂ)).re := by simpa [w] using (zero_lt_one.trans_le hu)
  have hG := (integral_gaussDigammaDifferenceKernel (d := 1) (w := w) one_pos (by simpa using hw)).2
  simp only [Complex.ofReal_one, div_one] at hG
  have hb : ‖∫ x in Ioi (0 : ℝ), gaussDigammaDifferenceKernel 1 w x‖ ≤
      (|1 - u| + |v|) * A := by
    rw [← integral_const_mul]
    refine norm_integral_le_of_norm_le (hK.const_mul _) ?_
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
    simpa [K, w, min_eq_left hu] using
      (norm_gaussDigammaDifferenceKernel_le (d := 1) (u := u) (v := v) one_pos (show 0 < x from hx))
  change ‖Complex.digamma w‖ ≤ _
  calc
    _ ≤ ‖Complex.digamma w - Complex.digamma 1‖ + D :=
      (norm_le_insert' (Complex.digamma w) (Complex.digamma 1)).trans_eq (add_comm _ _)
    _ ≤ (|1 - u| + |v|) * A + D := by rw [← hG]; exact add_le_add hb (le_refl D)
    _ ≤ _ := by
      rw [abs_of_nonpos (by linarith : 1 - u ≤ 0)]
      nlinarith [mul_nonneg hd (show 0 ≤ u + |v| by linarith [abs_nonneg v])]

end RiemannMasullo.StripNuclearity
