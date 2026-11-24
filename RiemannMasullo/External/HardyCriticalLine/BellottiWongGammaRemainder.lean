/-
Copyright 2026 ArtiFish26. Released under the Apache-2.0 license.
Ported from artifish26/riemann-hypothesis-lean at e9b20c778b19b5bba2e9a8e14a9bb4ca0afad850,
RiemannHypothesisProject/RiemannVonMangoldt/BellottiWongGammaRemainder.lean.
Selected dependencies of Hardy's theorem, renamed the namespace, and adapted to Mathlib v4.36.0.
See MODIFICATIONS.md for file-specific changes.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial

@[expose] public section

open MeasureTheory

namespace HardyCriticalLine

noncomputable section

/-- The Binet kernel whose Laplace transform controls the complex digamma remainder. -/
def bennettGammaBinetKernel (t : Real) : Complex :=
  (1 / 2 : Complex) - 1 / (t : Complex) +
    1 / (Complex.exp (t : Complex) - 1)

/-- The exact derivative of Binet's kernel on the positive axis. -/
def bennettGammaBinetKernelDeriv (t : Real) : Complex :=
  1 / (t : Complex) ^ 2 -
    Complex.exp (t : Complex) / (Complex.exp (t : Complex) - 1) ^ 2

/-- Binet's kernel has the expected derivative away from the origin. -/
theorem hasDerivAt_bennettGammaBinetKernel {t : Real} (ht : 0 < t) :
    HasDerivAt bennettGammaBinetKernel (bennettGammaBinetKernelDeriv t) t := by
  have ht0 : (t : Complex) ≠ 0 := by exact_mod_cast ht.ne'
  have hden : Complex.exp (t : Complex) - 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    have hre' : Real.exp t - 1 = 0 := by
      simpa [Complex.exp_ofReal_re] using hre
    nlinarith [Real.add_one_lt_exp ht.ne']
  have hinv : HasDerivAt (fun x : Real => 1 / (x : Complex))
      (-(1 : Complex) / (t : Complex) ^ 2) t := by
    simpa only [Function.comp_apply, one_div, neg_div] using!
      (hasDerivAt_inv ht0).comp_ofReal
  have hexp : HasDerivAt (fun x : Real => Complex.exp (x : Complex))
      (Complex.exp (t : Complex)) t :=
    (Complex.hasDerivAt_exp (t : Complex)).comp_ofReal
  have hdenInv : HasDerivAt
      (fun x : Real => 1 / (Complex.exp (x : Complex) - 1))
      (-(Complex.exp (t : Complex)) /
        (Complex.exp (t : Complex) - 1) ^ 2) t := by
    simpa only [Function.comp_apply, one_div] using!
      ((Complex.hasDerivAt_exp (t : Complex)).sub_const 1).inv hden |>.comp_ofReal
  convert ((hasDerivAt_const t (1 / 2 : Complex)).sub hinv).add hdenInv using 1
  all_goals first
    | rfl
    | (simp only [bennettGammaBinetKernelDeriv, one_div,
        sub_eq_add_neg]; ring)

/-- The Binet kernel is real on the positive integration axis. -/
theorem bennettGammaBinetKernel_eq_ofReal (t : Real) :
    bennettGammaBinetKernel t =
      ((1 / 2 : Real) - 1 / t + 1 / (Real.exp t - 1) : Real) := by
  simp [bennettGammaBinetKernel, ← Complex.ofReal_exp]

/-- The Binet-kernel cancellation gives a uniform compact bound near zero. -/
theorem norm_bennettGammaBinetKernel_le_one_half {t : Real}
    (ht_pos : 0 < t) (ht_one : t <= 1) :
    ‖bennettGammaBinetKernel t‖ <= 1 / 2 := by
  rw [bennettGammaBinetKernel_eq_ofReal, Complex.norm_real]
  have ht_abs : |t| <= 1 := by
    rw [abs_of_pos ht_pos]
    exact ht_one
  have hexp_error := Real.abs_exp_sub_one_sub_id_le ht_abs
  have hden_lower : t <= Real.exp t - 1 := by
    nlinarith [Real.add_one_le_exp t]
  have hden_pos : 0 < Real.exp t - 1 := lt_of_lt_of_le ht_pos hden_lower
  have hden_upper : Real.exp t - 1 <= t + t ^ 2 := by
    have := (abs_le.mp hexp_error).2
    nlinarith
  have hrecip_upper : 1 / (Real.exp t - 1) <= 1 / t :=
    one_div_le_one_div_of_le ht_pos hden_lower
  have hcompact_pos : 0 < t + t ^ 2 := by positivity
  have hrecip_lower : 1 / (t + t ^ 2) <= 1 / (Real.exp t - 1) :=
    one_div_le_one_div_of_le hden_pos hden_upper
  apply abs_le.mpr
  constructor
  · have hbaseline :
        -(1 / 2 : Real) <= 1 / 2 - 1 / t + 1 / (t + t ^ 2) := by
      have hone_pos : 0 < 1 + t := by linarith
      field_simp [ht_pos.ne', hone_pos.ne']
      nlinarith [sq_nonneg t]
    linarith
  · linarith

/-- Binet-kernel cancellation gives the sharp elementary bound on the positive axis. -/
theorem norm_bennettGammaBinetKernel_le_one_half_of_pos {t : Real}
    (ht_pos : 0 < t) : ‖bennettGammaBinetKernel t‖ <= 1 / 2 := by
  by_cases ht_one : t <= 1
  · exact norm_bennettGammaBinetKernel_le_one_half ht_pos ht_one
  · rw [bennettGammaBinetKernel_eq_ofReal, Complex.norm_real]
    have ht_ge_one : 1 <= t := le_of_lt (lt_of_not_ge ht_one)
    have hinv_nonneg : 0 <= 1 / t := by positivity
    have hinv_le_one : 1 / t <= 1 := by
      rw [div_le_iff₀ ht_pos]
      linarith
    have hden_lower : t <= Real.exp t - 1 := by
      nlinarith [Real.add_one_le_exp t]
    have hden_pos : 0 < Real.exp t - 1 := lt_of_lt_of_le ht_pos hden_lower
    have htail_nonneg : 0 <= 1 / (Real.exp t - 1) := by positivity
    have htail_le : 1 / (Real.exp t - 1) <= 1 / t :=
      one_div_le_one_div_of_le ht_pos hden_lower
    apply abs_le.mpr
    constructor <;> linarith

/-- The Binet kernel is continuous away from the origin. -/
theorem continuousOn_bennettGammaBinetKernel :
    ContinuousOn bennettGammaBinetKernel (Set.Ioi 0) := by
  intro t ht
  exact (hasDerivAt_bennettGammaBinetKernel ht).continuousAt.continuousWithinAt

end

end HardyCriticalLine
