/-
Copyright 2026 ArtiFish26. Released under the Apache-2.0 license.
Ported from artifish26/riemann-hypothesis-lean at e9b20c778b19b5bba2e9a8e14a9bb4ca0afad850,
RiemannHypothesisProject/Hardy/HardyFunctionNormalization.lean.
Replaced the ξ quotient with Mathlib's hardyZ, preserving the sign of the upstream function.
The parametrization is from RiemannHypothesisProject/SpectralModel.lean at the same revision.
See MODIFICATIONS.md for file-specific changes.
-/
module

public import Mathlib.NumberTheory.LSeries.HardyZ

@[expose] public section

open Complex

namespace HardyCriticalLine

noncomputable section

/-- The point at height `t` on the critical line. -/
def criticalLinePoint (t : ℝ) : ℂ := 1 / 2 + (t : ℂ) * I

theorem continuous_criticalLinePoint : Continuous criticalLinePoint := by
  unfold criticalLinePoint
  fun_prop

/-- Upstream's ξ normalization gives the negative of Mathlib's Hardy function. -/
def hardyFunctionReal (t : ℝ) : ℝ := -hardyZ t

/-- The complex presentation used in the oscillatory integral. -/
def hardyFunction (t : ℝ) : ℂ := hardyFunctionReal t

theorem ofReal_hardyFunctionReal_eq (t : ℝ) : (hardyFunctionReal t : ℂ) = hardyFunction t := rfl

theorem continuous_hardyFunctionReal : Continuous hardyFunctionReal := continuous_hardyZ.neg

theorem continuous_hardyFunction : Continuous hardyFunction :=
  continuous_ofReal.comp continuous_hardyFunctionReal

theorem abs_hardyFunctionReal (t : ℝ) :
    |hardyFunctionReal t| = ‖riemannZeta (criticalLinePoint t)‖ := by
  simpa only [hardyFunctionReal, abs_neg, criticalLinePoint] using abs_hardyZ t

theorem hardyFunctionReal_eq_zero_iff (t : ℝ) :
    hardyFunctionReal t = 0 ↔ riemannZeta (criticalLinePoint t) = 0 := by
  simpa only [hardyFunctionReal, neg_eq_zero, criticalLinePoint] using hardyZ_eq_zero_iff t

/-- The negative unit phase in the ξ normalization. -/
def hardyPhaseFactor (t : ℝ) : ℂ :=
  -(Gammaℝ (criticalLinePoint t) / ‖Gammaℝ (criticalLinePoint t)‖)

theorem norm_hardyPhaseFactor (t : ℝ) : ‖hardyPhaseFactor t‖ = 1 := by
  have h : Gammaℝ (criticalLinePoint t) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by simp [criticalLinePoint])
  simp [hardyPhaseFactor, h]

theorem hardyFunction_eq_factor_unit_mul_riemannZeta (t : ℝ) :
    hardyFunction t = hardyPhaseFactor t * riemannZeta (criticalLinePoint t) := by
  have hg : Gammaℝ (criticalLinePoint t) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by simp [criticalLinePoint])
  have hs : criticalLinePoint t ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num [criticalLinePoint] at this
  rw [hardyFunction, hardyFunctionReal, ofReal_neg, ofReal_hardyZ,
    riemannZeta_def_of_ne_zero hs, hardyPhaseFactor]
  change -(completedRiemannZeta (criticalLinePoint t) / (‖Gammaℝ (criticalLinePoint t)‖ : ℂ)) = _
  field_simp

end

end HardyCriticalLine
