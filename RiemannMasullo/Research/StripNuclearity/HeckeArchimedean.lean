module

public import RiemannMasullo.Research.StripNuclearity.HeckeZeroMass
public import RiemannMasullo.Ch06_LocalGlobal.Sec3

/-! # Uniform right-hand bounds for the completed Hecke logarithmic derivative

The bound records the local radial parameters and the real parity or complex
angular order from the gamma factors. The constant depends only on the field.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain NumberField Set
open scoped Topology

namespace RiemannMasullo.StripNuclearity

variable {F : Type*} [Field F] [NumberField F]
local notation "U" => PontryaginDual (IdeleClassGroup (𝓞 F) F)

/-- Paper: Equations (3.2.1.4)–(3.2.1.5), p. 123. The shift of the
real or complex gamma factor includes both the radial exponent and the local
parity or half angular order, with the normalized complex absolute value. -/
def heckeArchimedeanShift (χ : U) (v : InfinitePlace F) : ℂ :=
  open Classical in
  if hv : v.IsReal then
    let a := (realHeckeCharacter_parameters χ v hv).exists.choose
    a.1 + (a.2.val : ℂ)
  else
    let a := (complexHeckeCharacter_parameters χ v
      (InfinitePlace.not_isReal_iff_isComplex.mp hv)).exists.choose
    a.1 + (a.2.natAbs : ℂ) / 2

theorem heckeArchimedeanShift_re_nonneg (χ : U) (v : InfinitePlace F) :
    0 ≤ (heckeArchimedeanShift χ v).re := by
  unfold heckeArchimedeanShift
  split_ifs with hv
  · simp only [Complex.add_re, (realHeckeCharacter_parameters χ v hv).exists.choose_spec.1,
      Complex.natCast_re, zero_add]
    positivity
  · have hc := InfinitePlace.not_isReal_iff_isComplex.mp hv
    simp only [Complex.add_re, (complexHeckeCharacter_parameters χ v hc).exists.choose_spec.1,
      Complex.div_ofNat_re, Complex.natCast_re, zero_add]
    positivity

private def gammaModel (c d : ℝ) (b s : ℂ) : ℂ :=
  Complex.exp (-(Real.log c : ℂ) * ((s + b) / (d : ℂ))) * Complex.Gamma ((s + b) / (d : ℂ))

private theorem gammaModel_at_two (c d : ℝ) (hd : 1 ≤ d) (hd' : d ≤ 2) :
    ∃ K ≥ (0 : ℝ), ∀ b : ℂ, 0 ≤ b.re →
      gammaModel c d b 2 ≠ 0 ∧ DifferentiableAt ℂ (gammaModel c d b) 2 ∧
        ‖logDeriv (gammaModel c d b) 2‖ ≤ K * (1 + b.re + |b.im|) := by
  obtain ⟨C, hC, hD⟩ := exists_uniform_digamma_bound
  refine ⟨3 * C + |Real.log c|, by positivity, fun b hb ↦ ?_⟩
  let z (s : ℂ) := (s + b) / (d : ℂ)
  let E (s : ℂ) := Complex.exp (-(Real.log c : ℂ) * z s)
  have hd₀ : 0 < d := zero_lt_one.trans_le hd
  have hzre : (z 2).re = (2 + b.re) / d := by simp [z, Complex.div_ofReal_re]
  have hzim : (z 2).im = b.im / d := by simp [z, Complex.div_ofReal_im]
  have hz₁ : 1 ≤ (z 2).re := by rw [hzre, le_div_iff₀ hd₀]; linarith
  have hz₀ : 0 < (z 2).re := zero_lt_one.trans_le hz₁
  have hz : HasDerivAt z (1 / (d : ℂ)) 2 := ((hasDerivAt_id' (2 : ℂ)).add_const b).div_const _
  have hE := (hz.const_mul (-(Real.log c : ℂ))).cexp
  have hG := (Complex.hasDerivAt_Gamma_of_re_pos hz₀).differentiableAt
  have hN : E 2 ≠ 0 := Complex.exp_ne_zero _
  have hGN := Complex.Gamma_ne_zero_of_re_pos hz₀
  refine ⟨mul_ne_zero hN hGN, hE.differentiableAt.mul (hG.comp 2 hz.differentiableAt), ?_⟩
  have hlog : logDeriv (gammaModel c d b) 2 =
      (Complex.digamma (z 2) - (Real.log c : ℂ)) / (d : ℂ) := by
    change logDeriv (fun s ↦ E s * Complex.Gamma (z s)) 2 = _
    rw [logDeriv_fun_mul (f := E) (g := fun s ↦ Complex.Gamma (z s)) 2 hN hGN
      hE.differentiableAt (hG.comp 2 hz.differentiableAt),
      hz.logDeriv_Gamma (fun m h ↦ by
        have he := congrArg Complex.re h
        simp at he
        linarith [show (0 : ℝ) ≤ m by positivity])]
    rw [logDeriv_apply, show deriv E 2 = E 2 * (-(Real.log c : ℂ) * (1 / (d : ℂ))) from hE.deriv,
      mul_div_cancel_left₀ _ hN]
    ring
  have he := hD (z 2).re (z 2).im hz₁
  rw [Complex.re_add_im, hzre, hzim, abs_div, abs_of_pos hd₀] at he
  have hR : (2 + b.re) / d ≤ 2 + b.re := div_le_self (by linarith) hd
  have hI : |b.im| / d ≤ |b.im| := div_le_self (abs_nonneg _) hd
  rw [hlog, norm_div, Complex.norm_real, Real.norm_of_nonneg hd₀.le]
  refine (div_le_self (norm_nonneg _) hd).trans ((norm_sub_le _ _).trans ?_)
  rw [Complex.norm_real, Real.norm_eq_abs]
  have hb' := mul_le_mul_of_nonneg_left (show 1 + (2 + b.re) / d + |b.im| / d ≤
      3 * (1 + b.re + |b.im|) by linarith [abs_nonneg b.im]) hC
  nlinarith [mul_nonneg (abs_nonneg (Real.log c)) (add_nonneg hb (abs_nonneg b.im))]

private theorem gammaModel_real (b : ℂ) :
    (fun s ↦ Complex.Gammaℝ (s + b)) = gammaModel Real.pi 2 b := by
  funext s
  rw [Complex.Gammaℝ_def, gammaModel, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero),
    ← Complex.ofReal_log Real.pi_pos.le]
  push_cast
  ring_nf

private theorem gammaModel_complex (b : ℂ) :
    (fun s ↦ Complex.Gammaℂ (s + b) / 2) = gammaModel (2 * Real.pi) 1 b := by
  funext s
  simp only [Complex.Gammaℂ_def, gammaModel, Complex.ofReal_one, div_one]
  have hn : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  rw [Complex.cpow_def_of_ne_zero hn,
    show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_log (by positivity : 0 ≤ 2 * Real.pi)]
  ring_nf

/-- A common bound for the archimedean logarithmic derivative at two, with
the dependence on all the archimedean character parameters displayed. -/
theorem exists_heckeGammaFactor_uniform_logDeriv_two (F : Type*) [Field F] [NumberField F] :
    ∃ C ≥ (0 : ℝ), ∀ χ : PontryaginDual (IdeleClassGroup (𝓞 F) F),
      ‖logDeriv (heckeGammaFactor χ) 2‖ ≤ C *
        (∑ v : InfinitePlace F, (1 + (heckeArchimedeanShift χ v).re + |(heckeArchimedeanShift χ v).im|)) := by
  classical
  obtain ⟨R, hR, hr⟩ := gammaModel_at_two Real.pi 2 (by norm_num) le_rfl
  obtain ⟨S, hS, hc⟩ := gammaModel_at_two (2 * Real.pi) 1 le_rfl (by norm_num)
  let C := max R S
  refine ⟨C, hR.trans (le_max_left _ _), fun χ ↦ ?_⟩
  let b := heckeArchimedeanShift χ
  let G (v : InfinitePlace F) (s : ℂ) :=
    if v.IsReal then Complex.Gammaℝ (s + b v) else Complex.Gammaℂ (s + b v) / 2
  have hG (v : InfinitePlace F) : G v 2 ≠ 0 ∧ DifferentiableAt ℂ (G v) 2 ∧
      ‖logDeriv (G v) 2‖ ≤ C * (1 + (b v).re + |(b v).im|) := by
    have hb := heckeArchimedeanShift_re_nonneg χ v
    have hsize : 0 ≤ 1 + (b v).re + |(b v).im| := by dsimp [b]; positivity
    by_cases hv : v.IsReal
    · have hg : G v = gammaModel Real.pi 2 (b v) := by simpa [G, hv] using gammaModel_real (b v)
      rw [hg]
      obtain ⟨hn, hd, h⟩ := hr (b v) hb
      exact ⟨hn, hd, h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hsize)⟩
    · have hg : G v = gammaModel (2 * Real.pi) 1 (b v) := by simpa [G, hv] using gammaModel_complex (b v)
      rw [hg]
      obtain ⟨hn, hd, h⟩ := hc (b v) hb
      exact ⟨hn, hd, h.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hsize)⟩
  have hprod : heckeGammaFactor χ = fun s ↦ ∏ v, G v s := by
    funext s
    apply Finset.prod_congr rfl
    intro v _
    by_cases hv : v.IsReal <;> simp [G, b, heckeArchimedeanShift, hv, add_assoc]
  rw [hprod, logDeriv_fun_prod (fun v _ ↦ (hG v).1) (fun v _ ↦ (hG v).2.1), Finset.mul_sum]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun v _ ↦ (hG v).2.2)

/-- The logarithmic derivative of the actual completed Hecke continuation at
two has a bound uniform in the character, with only linear growth in the sum
of its local archimedean parameters. -/
theorem exists_continuedCompletedHeckeL_uniform_logDeriv_two (F : Type*) [Field F] [NumberField F] :
    ∃ C ≥ (0 : ℝ), ∀ χ : PontryaginDual (IdeleClassGroup (𝓞 F) F),
      ‖logDeriv (continuedCompletedHeckeL χ) 2‖ ≤ C *
        (1 + ∑ v : InfinitePlace F, (1 + (heckeArchimedeanShift χ v).re + |(heckeArchimedeanShift χ v).im|)) := by
  obtain ⟨B, hB⟩ := exists_uniform_finiteHeckeL_logDeriv_bound F
  obtain ⟨A, hA, hG⟩ := exists_heckeGammaFactor_uniform_logDeriv_two F
  refine ⟨max A B, hA.trans (le_max_left _ _), fun χ ↦ ?_⟩
  obtain ⟨L, hL, hSeries⟩ := finiteHeckeL_exists_continuation χ
  have hz : 1 < (2 : ℂ).re := by norm_num
  have hη := (finiteHeckeL_logDeriv_hasSum_ideals χ L hL hSeries ⟨2, hz⟩)
  have heq : continuedCompletedHeckeL χ =ᶠ[𝓝 (2 : ℂ)] fun z ↦ heckeGammaFactor χ z * L z := by
    filter_upwards [Complex.continuous_re.continuousAt.eventually (lt_mem_nhds hz)] with z hz'
    rw [(continuedCompletedHeckeL_spec χ).2 ⟨z, hz'⟩, completedHeckeL, hSeries ⟨z, hz'⟩, finiteHeckeL]
  rw [(logDeriv_congr_nhds heq).eq_of_nhds,
    logDeriv_fun_mul _ (heckeGammaFactor_ne_zero_of_re_pos χ (zero_lt_one.trans hz)) hη.2.1
      (differentiableAt_heckeGammaFactor_of_re_pos χ (zero_lt_one.trans hz)) hη.1.differentiableAt]
  have hb := hB χ L hL hSeries 2 (by norm_num)
  have hpart (v : InfinitePlace F) : 0 ≤ 1 + (heckeArchimedeanShift χ v).re + |(heckeArchimedeanShift χ v).im| :=
    add_nonneg (add_nonneg zero_le_one (heckeArchimedeanShift_re_nonneg χ v)) (abs_nonneg _)
  refine (norm_add_le _ _).trans ((add_le_add (hG χ) hb).trans ?_)
  rw [mul_add, mul_one]
  rw [add_comm (max A B)]
  exact add_le_add (mul_le_mul_of_nonneg_right (le_max_left A B)
    (Finset.sum_nonneg fun v _ ↦ hpart v)) (le_max_right A B)

end RiemannMasullo.StripNuclearity
