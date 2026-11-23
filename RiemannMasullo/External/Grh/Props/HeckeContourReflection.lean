/-
Vendored from thatnealpatel/grh at e55aab27b744bfb62a4aaa57ea9f13818aad1055,
Proofs/Props/HeckeContourReflection.lean, lines 26–49.
Copyright (c) 2026 Neal Patel. MIT License (see LICENSE in the Grh directory).
Changes are listed in MODIFICATIONS.md.
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.LinearCombination

/-! # Reflection of the completed logarithmic derivative -/

open Complex Filter
open scoped Topology

namespace RiemannMasullo.External.Grh

/-- Corrected (B.4.2.3) at an ordinary nonzero point. The constant `κ`
is `log A` once the arithmetic formula for the epsilon factor is proved. -/
public theorem completed_logDeriv_reflection {F G : ℂ → ℂ} {C κ z : ℂ}
    (hC : C ≠ 0) (hF : DifferentiableAt ℂ F z) (hG : DifferentiableAt ℂ G (1 - z)) (hz : F z ≠ 0)
    (hFE : (fun s ↦ G (1 - s)) =ᶠ[𝓝 z]
      (fun s ↦ (C * exp (κ * (s - 1 / 2))) * F s)) :
    logDeriv F z = -logDeriv G (1 - z) - κ := by
  let E (s : ℂ) := C * exp (κ * (s - 1 / 2))
  have hE : HasDerivAt E (E z * κ) z := by
    convert ((((hasDerivAt_id z).sub_const (1 / 2)).const_mul κ).cexp.const_mul C) using 1
    · rfl
    · simp [E, mul_assoc]
  have hG' : HasDerivAt (fun s : ℂ ↦ 1 - s) (-1) z :=
    (hasDerivAt_id z).const_sub (1 : ℂ)
  have hE₀ : E z ≠ 0 := mul_ne_zero hC (exp_ne_zero _)
  have hlogE : logDeriv E z = κ := by
    rw [logDeriv_apply, hE.deriv, mul_div_cancel_left₀ _ hE₀]
  have hleft : logDeriv (fun s ↦ G (1 - s)) z = -logDeriv G (1 - z) := by
    rw [logDeriv_fun_comp (f := G) (g := fun s : ℂ ↦ 1 - s) hG hG'.differentiableAt,
      hG'.deriv, mul_neg_one]
  have h := (logDeriv_congr_nhds hFE).eq_of_nhds
  change logDeriv (fun s ↦ G (1 - s)) z = logDeriv (fun s ↦ E s * F s) z at h
  rw [hleft, logDeriv_fun_mul z hE₀ hz hE.differentiableAt hF, hlogE] at h
  linear_combination -h

end RiemannMasullo.External.Grh
