module

public import RiemannMasullo.Ch09_HardySobolev.Sec2
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
The radial resolvent inverts its second-order differential numerator on compactly supported smooth tests.
-/

@[expose] public noncomputable section
open Function MeasureTheory Set

namespace RiemannMasullo.StripNuclearity

/-- Differentiation of a compactly supported radial profile multiplies its
bilateral Mellin transform by the negative spectral variable. -/
private theorem mellin_log_derivative (p p' : ℝ → ℂ) (hp : ∀ x, HasDerivAt p (p' x) x)
    (hc : Continuous p') (h₁ : HasCompactSupport p) (h₂ : HasCompactSupport p') (z : ℂ) :
    mellin (fun t ↦ p' (Real.log t)) z = -z * mellin (fun t ↦ p (Real.log t)) z := by
  let v (x : ℝ) := Complex.exp (z * x)
  let v' (x : ℝ) := z * v x
  have hv (x : ℝ) : HasDerivAt v (v' x) x := by
    simpa [v,v',mul_comm] using ((Complex.ofRealCLM.hasDerivAt (x := x)).const_mul z).cexp
  have hvC : Continuous v := continuous_iff_continuousAt.mpr fun x ↦ (hv x).continuousAt
  have hpC : Continuous p := continuous_iff_continuousAt.mpr fun x ↦ (hp x).continuousAt
  have hparts := integral_mul_deriv_eq_deriv_mul_of_integrable (u := p) (v := v)
    (u' := p') (v' := v') (fun x _ ↦ hp x) (fun x _ ↦ hv x)
    ((hpC.mul (continuous_const.mul hvC)).integrable_of_hasCompactSupport h₁.mul_right)
    ((hc.mul hvC).integrable_of_hasCompactSupport h₂.mul_right)
    ((hpC.mul hvC).integrable_of_hasCompactSupport h₁.mul_right)
  have hmul : (∫ x : ℝ, p x * v' x) = z * ∫ x : ℝ, p x * v x := by
    rw [← integral_const_mul]
    exact integral_congr_ae (.of_forall (fun x ↦ by dsimp [v']; ring))
  rw [hmul] at hparts
  rw [mellin_logProfile, mellin_logProfile, neg_mul]
  simpa [v] using (congrArg (fun x : ℂ ↦ -x) hparts).symm

/-- The two-sided resolvent inverts the second-order differential operator
on compact radial profiles, with the normalization of the project's Mellin
transform. -/
theorem mellin_compact_resolvent_numerator (c : ℝ) (p p' p'' : ℝ → ℂ)
    (hp : ∀ x, HasDerivAt p (p' x) x) (hp' : ∀ x, HasDerivAt p' (p'' x) x)
    (hc : Continuous p'') (h₀ : HasCompactSupport p) (h₁ : HasCompactSupport p')
    (h₂ : HasCompactSupport p'') (z : ℂ) :
    mellin (fun t ↦ (c : ℂ)^2 * p (Real.log t) - p'' (Real.log t)) z =
      ((c : ℂ)^2 - z^2) * mellin (fun t ↦ p (Real.log t)) z := by
  let v (x : ℝ) := Complex.exp (z * x)
  have hv : Continuous v := by dsimp [v]; fun_prop
  have hpC : Continuous p := continuous_iff_continuousAt.mpr fun x ↦ (hp x).continuousAt
  have hpC' : Continuous p' := continuous_iff_continuousAt.mpr fun x ↦ (hp' x).continuousAt
  have hD := mellin_log_derivative p p' hp hpC' h₀ h₁ z
  have hD' := mellin_log_derivative p' p'' hp' hc h₁ h₂ z
  rw [hD] at hD'
  have hlin : mellin (fun t ↦ (c : ℂ)^2 * p (Real.log t) - p'' (Real.log t)) z =
      (c : ℂ)^2 * mellin (fun t ↦ p (Real.log t)) z - mellin (fun t ↦ p'' (Real.log t)) z := by
    rw [mellin_logProfile (fun x ↦ (c : ℂ)^2 * p x - p'' x), mellin_logProfile p, mellin_logProfile p'']
    have h_int : Integrable (fun x ↦ p x * v x) volume := (hpC.mul hv).integrable_of_hasCompactSupport h₀.mul_right
    have h_int' : Integrable (fun x ↦ p'' x * v x) volume := (hc.mul hv).integrable_of_hasCompactSupport h₂.mul_right
    calc
      _ = ∫ x : ℝ, ((c : ℂ)^2 * (p x * v x) - p'' x * v x) :=
        integral_congr_ae (.of_forall fun x ↦ by dsimp [v]; ring)
      _ = _ := by rw [integral_sub (h_int.const_mul _) h_int', integral_const_mul]
  rw [hlin,hD']
  ring

/-- On compact radial tests the Sobolev resolvent sends the second-order
numerator back to the original profile in the weighted Hilbert space. -/
theorem resolvent_inverts_compact_test {I : Set ℝ} (ho : IsOpen I) (hi : OrdConnected I)
    (hne : I.Nonempty) {c : ℝ} (hno : ∀ z : ℂ, z.re ∈ I → (c : ℂ)^2 - z^2 ≠ 0)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (j : PositiveRealExponentialDecay I →L[ℂ] E) (R : E →L[ℂ] E)
    (hr : ∀ p, ∃ q : PositiveRealExponentialDecay I, R (j p) = j q ∧
      ∀ z, z.re ∈ I → mellin (fun t ↦ q.val (Real.log t)) z =
        ((c : ℂ)^2-z^2)⁻¹ * mellin (fun t ↦ p.val (Real.log t)) z)
    (p u : PositiveRealExponentialDecay I) (p' p'' : ℝ → ℂ)
    (hp : ∀ x, HasDerivAt p.val (p' x) x) (hp' : ∀ x, HasDerivAt p' (p'' x) x)
    (hc : Continuous p'') (h₀ : HasCompactSupport p.val) (h₁ : HasCompactSupport p')
    (h₂ : HasCompactSupport p'') (hu : ∀ x, u.val x = (c : ℂ)^2 * p.val x - p'' x) :
    R (j u) = j p := by
  obtain ⟨q,hq,hm⟩ := hr u
  rw [hq]
  apply congrArg j
  let M := positiveRealFourierMellin I ho hi hne
  apply M.injective
  apply Subtype.ext
  funext z
  by_cases hz : z.re ∈ I
  · rw [show (M q).val z = _ from positiveRealFourierMellin_apply I ho hi hne q z hz,
        show (M p).val z = _ from positiveRealFourierMellin_apply I ho hi hne p z hz, hm z hz]
    simp only [hu, mellin_compact_resolvent_numerator c p.val p' p'' hp hp' hc h₀ h₁ h₂ z,
      inv_mul_cancel_left₀ (hno z hz)]
  · rw [(M q).property.1 hz, (M p).property.1 hz]

/-- On each half-line the inverse Sobolev density is the exponential of a smooth
log-weight. The first two derivatives are bounded multiples of the density,
uniformly on the whole half-line. -/
theorem weight_log_derivatives (b s : ℝ) :
    let v := fun x : ℝ ↦ Real.exp (-b*x - (s/2)*Real.log (1+x^2))
    let p := fun x : ℝ ↦ -b-s*x/(1+x^2)
    let q := fun x : ℝ ↦ (p x)^2-s*(1-x^2)/(1+x^2)^2
    (∀ x, HasDerivAt v (p x*v x) x) ∧
      (∀ x, HasDerivAt (fun y ↦ p y*v y) (q x*v x) x) ∧
      (∀ x, |p x| ≤ |b|+|s|) ∧
      ∀ x, |q x| ≤ (|b|+|s|)^2+|s| := by
  intro v p q
  have hden (x : ℝ) : 0 < 1+x^2 := by positivity
  have hden' (x : ℝ) : HasDerivAt (fun y : ℝ ↦ 1+y^2) (2*x) x := by
    simpa using ((hasDerivAt_id x).pow 2).const_add 1
  have hp (x : ℝ) : HasDerivAt p (-s*(1-x^2)/(1+x^2)^2) x := by
    have h := (hasDerivAt_const x (-b)).sub
      (((hasDerivAt_id x).const_mul s).div (hden' x) (hden x).ne')
    convert h using 1 <;> first | rfl | (dsimp [p,id]; ring)
  have hv (x : ℝ) : HasDerivAt v (p x*v x) x := by
    have h := (((hasDerivAt_id x).const_mul (-b)).sub
      (((hden' x).log (hden x).ne').const_mul (s/2))).exp
    convert h using 1 <;> first | rfl | (dsimp [v,p,id]; ring)
  have hx (x : ℝ) : |x| ≤ 1+x^2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (x-1),sq_nonneg (x+1)]
  have hpB (x : ℝ) : |p x| ≤ |b|+|s| := by
    calc
      |p x| ≤ |-b|+|s*x/(1+x^2)| := abs_sub _ _
      _ ≤ _ := by
        rw [abs_neg, abs_div, abs_mul, abs_of_pos (hden x)]
        apply add_le_add_right
        exact (div_le_iff₀ (hden x)).mpr (mul_le_mul_of_nonneg_left (hx x) (abs_nonneg s))
  refine ⟨hv, ?_, hpB, ?_⟩
  · intro x
    convert (hp x).mul (hv x) using 1
    dsimp [q]
    ring
  · intro x
    have hrat : |1-x^2| ≤ (1+x^2)^2 := by
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg x, sq_nonneg (x^2), sq_nonneg (x^2+1)]
    calc
      |q x| ≤ |(p x)^2|+|s*(1-x^2)/(1+x^2)^2| := abs_sub _ _
      _ ≤ _ := by
        rw [abs_pow,abs_div,abs_mul, show |(1+x^2)^2| = (1+x^2)^2 from abs_of_nonneg (sq_nonneg _)]
        apply add_le_add (pow_le_pow_left₀ (abs_nonneg _) (hpB x) _)
        exact (div_le_iff₀ (sq_pos_of_pos (hden x))).mpr
          (mul_le_mul_of_nonneg_left hrat (abs_nonneg s))

/-- The two log-weight branches from the derivative estimate coincide with the
actual reciprocal Sobolev weight on their respective half-lines. -/
theorem reciprocal_interval_weight_branches {α : ℝ} (ha : 0 ≤ α) (s x : ℝ) :
    (intervalSobolevDensity (-α) α s x)⁻¹ =
      Real.exp ((if 0 ≤ x then -2*α else 2*α)*x -(s/2)*Real.log (1+x^2)) := by
  have hpos : 0 < 1+x^2 := by positivity
  rw [intervalSobolevDensity, Real.rpow_def_of_pos hpos]
  by_cases hx : 0 ≤ x
  · rw [ite_eq_left hx, max_eq_right (Real.exp_le_exp.mpr (by nlinarith [mul_nonneg ha hx]))]
    rw [mul_inv, ← Real.exp_neg, ← Real.exp_neg, ← Real.exp_add]
    congr 1
    ring
  · rw [ite_eq_right hx, max_eq_left (Real.exp_le_exp.mpr (by nlinarith [mul_nonpos_of_nonneg_of_nonpos ha (le_of_not_ge hx)]))]
    rw [mul_inv, ← Real.exp_neg, ← Real.exp_neg, ← Real.exp_add]
    congr 1
    ring

end RiemannMasullo.StripNuclearity
