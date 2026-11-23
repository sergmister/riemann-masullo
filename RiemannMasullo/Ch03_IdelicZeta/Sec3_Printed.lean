module

public import RiemannMasullo.Ch03_IdelicZeta.Sec3
import all RiemannMasullo.Ch03_IdelicZeta.Sec3b
import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Gamma.VerticalStripRatio

/-! # Chapter 3.3: the printed vertical-line estimate for the correcting factor -/

@[expose] public noncomputable section

namespace RiemannMasullo

open Filter NumberField IsDedekindDomain Topology
open scoped Asymptotics

/-- Paper: Proposition 3.3.1.5(3), (3.3.1.11), p. 132. As printed: on each fixed
vertical line of positive real part σ, the kth complex derivative of the S-local
correcting factor in any unitary norm-twist chart is big-O of
`|τ|^(σ - 1/2) |log |τ||^k` as `|τ| → ∞`. The finite set parameter lists the finite
places of S. `sLocalRhoFactor_iteratedDeriv_analyticOn` records (3.3.1.10).
See ERRATA F16. -/
def Printed.sLocalRhoFactor_iteratedDeriv_isBigO : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (χ : PontryaginDual (SIdeleQuotient F S)) (k : ℕ) (σ : ℝ), 0 < σ →
    let circleToComplex : Circle →ₜ* ℂ := ⟨Circle.coeHom, continuous_subtype_val⟩
    let ρ := fun z : ℂ ↦ sLocalRhoFactor (F := F) (S := S)
      (quasiCharacterNormTwist (G := SIdeleQuotient F S) (sIdeleQuotientNorm F S)
        (isProperMap_sIdeleQuotientNorm F S).continuous (circleToComplex.comp χ) z)
    (fun t : ℝ ↦ iteratedDeriv k ρ ((σ : ℂ) + (t : ℂ) * Complex.I))
      =O[comap (fun t : ℝ ↦ |t|) atTop]
        (fun t : ℝ ↦ |t| ^ (σ - 1 / 2) * |Real.log (|t|)| ^ k)

/-- At a complex place, the local factor of a bare norm power in the critical strip
is the ratio of complex gamma factors. -/
private theorem P4641_tate {F : Type*} [Field F] [NumberField F] (w : InfinitePlace F)
    (hw : w.IsComplex) (s : ℂ) (hs : s.re ∈ Set.Ioo (0 : ℝ) 1) :
    infiniteLocalTateFactor w (sLocalInfiniteRestriction (S := ∅) w
      (quasiCharacterNormTwist (sIdeleQuotientNorm F ∅) (isProperMap_sIdeleQuotientNorm F ∅).continuous
        ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp 1) s)) =
      Complex.Gammaℂ s / Complex.Gammaℂ (1 - s) := by
  obtain ⟨η, ha, -⟩ := sLocalInfinite_charts (S := ∅) (1 : PontryaginDual (SIdeleQuotient F ∅)) w
  have hval (g : w.Completionˣ) := sLocalInfiniteRestriction_normTwist (S := ∅) w s g
  have hshape : ∀ x : ℂˣ, (sLocalInfiniteRestriction (S := ∅) w
      (quasiCharacterNormTwist (sIdeleQuotientNorm F ∅) (isProperMap_sIdeleQuotientNorm F ∅).continuous
        ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp 1) s))
        (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm.toMonoidHom x) =
      ((‖(x : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ s * ((x : ℂ) / (‖(x : ℂ)‖ : ℂ)) ^ (0 : ℤ) := by
    intro x
    have hn : ‖((InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm (x : ℂ) : w.Completion)‖ =
        ‖(x : ℂ)‖ :=
      (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).symm.isometry.norm_map_of_map_zero
        (map_zero (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm) (x : ℂ)
    refine (hval _).trans ?_
    simp [InfinitePlace.mult, InfinitePlace.not_isReal_iff_isComplex.mpr hw, hn]
  replace hshape := fun x ↦ (DFunLike.congr_fun (ha s) _).symm.trans (hshape x)
  refine (congrArg (infiniteLocalTateFactor w) (ha s)).trans ?_
  have hr := complexTate_ratio_strip w hw η s hs
  have h1 := complexEuler_of_shape w hw _ s 0 hshape
  have h2 := complexEuler_of_shape w hw _ (1 - s) (-0) (complexDual_shape w hw _ s 0 hshape)
  simp only at hr
  rw [hr, h1.1, h1.2, h2.1]
  simp only [Int.natAbs_zero, pow_zero, one_mul, Nat.cast_zero, zero_div, add_zero, neg_zero]
  exact div_div_div_cancel_right₀ two_ne_zero _ _

/-- Lower bound for the modulus of the complex gamma ratio on a vertical line. -/
private theorem P4641_lower (σ : ℝ) (hσ : σ ∈ Set.Icc (0 : ℝ) 1) :
    ∃ A : ℝ, 0 < A ∧ ∀ t : ℝ, 1 ≤ |t| →
      A * |t| ^ (2 * σ - 1) ≤
        ‖Complex.Gammaℂ ((σ : ℂ) + (t : ℂ) * Complex.I) /
          Complex.Gammaℂ (1 - ((σ : ℂ) + (t : ℂ) * Complex.I))‖ := by
  obtain ⟨C, hC, hb⟩ := norm_Gamma_div_le_rpow_on_strip (le_refl (1 : ℝ))
  set P := (2 * Real.pi) ^ (-σ)
  set Q := (2 * Real.pi) ^ (-(1 - σ))
  have hP : 0 < P := by positivity
  have hQ : 0 < Q := by positivity
  refine ⟨P / (Q * C), by positivity, fun t ht ↦ ?_⟩
  have h1 := hb (1 - σ) σ t (by rw [abs_le]; constructor <;> linarith [hσ.1, hσ.2])
    (by rw [abs_le]; constructor <;> linarith [hσ.1, hσ.2]) ht
  have he1 : (σ : ℂ) + (t : ℂ) * Complex.I = ⟨σ, t⟩ := by apply Complex.ext <;> simp
  have he2 : 1 - ((σ : ℂ) + (t : ℂ) * Complex.I) = (starRingEnd ℂ) ⟨1 - σ, t⟩ := by
    apply Complex.ext <;> simp
  have hne (x : ℝ) : Complex.Gamma ⟨x, t⟩ ≠ 0 := by
    rw [ne_eq, Complex.Gamma_eq_zero_iff]
    rintro ⟨m, hm⟩
    have h : t = 0 := by simpa using congrArg Complex.im hm
    rw [h, abs_zero] at ht
    norm_num at ht
  have ht0 : 0 < |t| := zero_lt_one.trans_le ht
  have hpos1 : 0 < ‖Complex.Gamma ⟨σ, t⟩‖ := norm_pos_iff.mpr (hne σ)
  have hpos2 : 0 < ‖Complex.Gamma ⟨1 - σ, t⟩‖ := norm_pos_iff.mpr (hne (1 - σ))
  have hG (z : ℂ) : ‖Complex.Gammaℂ z‖ = 2 * (2 * Real.pi) ^ (-z.re) * ‖Complex.Gamma z‖ := by
    have h2 : (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
    rw [Complex.Gammaℂ_def, norm_mul, norm_mul, h2,
      Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    simp
  rw [norm_div, hG, hG, he2, Complex.Gamma_conj, Complex.norm_conj, ← he2, he1]
  have hre : (1 - (Complex.mk σ t)).re = 1 - σ := by simp
  rw [hre]
  change P / (Q * C) * |t| ^ (2 * σ - 1) ≤ 2 * P * ‖Complex.Gamma ⟨σ, t⟩‖ /
    (2 * Q * ‖Complex.Gamma ⟨1 - σ, t⟩‖)
  rw [norm_div, div_le_iff₀ hpos1] at h1
  have hTT : |t| ^ (2 * σ - 1) * |t| ^ (1 - σ - σ) = 1 := by
    rw [← Real.rpow_add ht0]; norm_num [show 2 * σ - 1 + (1 - σ - σ) = 0 by ring]
  have key : |t| ^ (2 * σ - 1) * ‖Complex.Gamma ⟨1 - σ, t⟩‖ ≤ C * ‖Complex.Gamma ⟨σ, t⟩‖ := by
    have := mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg ht0.le (2 * σ - 1))
    calc _ ≤ _ := this
      _ = C * ‖Complex.Gamma ⟨σ, t⟩‖ * (|t| ^ (2 * σ - 1) * |t| ^ (1 - σ - σ)) := by ring
      _ = _ := by rw [hTT, mul_one]
  rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have := mul_le_mul_of_nonneg_left key (by positivity : (0 : ℝ) ≤ 2 * P * Q)
  nlinarith

/-- Paper: Proposition 3.3.1.5(3), (3.3.1.11), p. 132. Take F = ℚ(i), S consisting
of the complex place, the trivial character, k = 0 and σ = 1. The factor is
`(2π)^(1 - 2s) Γ(s) / Γ(1 - s)`, of modulus `|τ| / (2π)` for nonzero τ by the
Gamma recurrence and conjugation. The printed bound would give `O(|τ|^(1/2))`. -/
theorem Printed.sLocalRhoFactor_iteratedDeriv_isBigO_false :
    ¬ Printed.sLocalRhoFactor_iteratedDeriv_isBigO := by
  intro h
  haveI : NeZero (4 : ℕ) := ⟨by norm_num⟩
  haveI : IsCyclotomicExtension {4} ℚ (CyclotomicField 4 ℚ) := by
    convert CyclotomicField.isCyclotomicExtension 4 ℚ; exact Subsingleton.elim _ _
  have hcx : ∀ w : InfinitePlace (CyclotomicField 4 ℚ), w.IsComplex := fun w ↦
    (IsCyclotomicExtension.Rat.isTotallyComplex (n := 4) (CyclotomicField 4 ℚ) (by norm_num)).isComplex w
  have hb := h (CyclotomicField 4 ℚ) ∅ 1 0 (3 / 4) (by norm_num)
  simp only [iteratedDeriv_zero, pow_zero, mul_one] at hb
  obtain ⟨c, hc⟩ := hb.bound
  obtain ⟨A, hA, hlow⟩ := P4641_lower (3 / 4) (by norm_num)
  set n := Fintype.card (InfinitePlace (CyclotomicField 4 ℚ))
  have hn : 1 ≤ n := Fintype.card_pos
  have hρ : ∀ t : ℝ, sLocalRhoFactor (F := CyclotomicField 4 ℚ) (S := ∅)
      (quasiCharacterNormTwist (sIdeleQuotientNorm (CyclotomicField 4 ℚ) ∅)
        (isProperMap_sIdeleQuotientNorm (CyclotomicField 4 ℚ) ∅).continuous
        ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp 1)
        (((3 / 4 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) =
      (Complex.Gammaℂ (((3 / 4 : ℝ) : ℂ) + (t : ℂ) * Complex.I) /
        Complex.Gammaℂ (1 - (((3 / 4 : ℝ) : ℂ) + (t : ℂ) * Complex.I))) ^ n := by
    intro t
    have hs : (((3 / 4 : ℝ) : ℂ) + (t : ℂ) * Complex.I).re ∈ Set.Ioo (0 : ℝ) 1 := by
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, mul_zero, mul_one, sub_self, add_zero]
      norm_num
    rw [sLocalRhoFactor_archimedean, Finset.prod_congr rfl (fun w _ ↦ P4641_tate w (hcx w) _ hs),
      Finset.prod_const, Finset.card_univ]
  have hev := Filter.eventually_comap.mp hc
  have h2 : ∀ᶠ b : ℝ in atTop, (|c| + 1) / A < b ^ (1 / 4 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num)).eventually_gt_atTop _
  obtain ⟨b, hb1, hb2, hb3⟩ := (hev.and (h2.and (eventually_ge_atTop 1))).exists
  have hab : |b| = b := abs_of_nonneg (by linarith)
  have hup := (congrArg norm (hρ b)).symm.trans_le (hb1 b hab)
  rw [norm_pow, hab, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    show (3 / 4 : ℝ) - 1 / 2 = 1 / 4 by norm_num] at hup
  have hl := hlow b (by rw [hab]; exact hb3)
  rw [hab, show 2 * (3 / 4 : ℝ) - 1 = 1 / 4 + 1 / 4 by norm_num,
    Real.rpow_add (by linarith)] at hl
  set X := ‖Complex.Gammaℂ (((3 / 4 : ℝ) : ℂ) + (b : ℂ) * Complex.I) /
        Complex.Gammaℂ (1 - (((3 / 4 : ℝ) : ℂ) + (b : ℂ) * Complex.I))‖ with hX
  set u := b ^ (1 / 4 : ℝ) with hu
  have hu1 : 1 ≤ u := Real.one_le_rpow hb3 (by norm_num)
  rw [div_lt_iff₀ hA] at hb2
  have hc1 : 0 ≤ |c| := abs_nonneg c
  have hX1 : 1 ≤ X := by nlinarith
  have hXn : X ≤ X ^ n := le_self_pow₀ hX1 (by omega)
  have hcu : c * u ≤ |c| * u := mul_le_mul_of_nonneg_right (le_abs_self c) (by linarith)
  nlinarith


end RiemannMasullo
