/-
Copyright 2026 ArtiFish26. Released under the Apache-2.0 license.
Ported from artifish26/riemann-hypothesis-lean at e9b20c778b19b5bba2e9a8e14a9bb4ca0afad850,
RiemannHypothesisProject/RiemannVonMangoldt/BellottiWongElementaryTaylor.lean.
Selected dependencies of Hardy's theorem, renamed the namespace, and adapted to Mathlib v4.36.0.
See MODIFICATIONS.md for file-specific changes.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

@[expose] public section

namespace HardyCriticalLine

noncomputable section

private def arctanUpperGap (x : Real) : Real :=
  x - x ^ 3 / 3 + x ^ 5 / 5 - Real.arctan x

private theorem hasDerivAt_arctanUpperGap (x : Real) :
    HasDerivAt arctanUpperGap (x ^ 6 / (1 + x ^ 2)) x := by
  unfold arctanUpperGap
  convert
    (((hasDerivAt_id x).sub ((hasDerivAt_pow 3 x).div_const 3)).add
      ((hasDerivAt_pow 5 x).div_const 5)).sub
        (Real.hasDerivAt_arctan x) using 1
  · rfl
  · norm_num
    field_simp
    ring

private theorem arctanUpperGap_monotone : Monotone arctanUpperGap :=
  monotone_of_hasDerivAt_nonneg hasDerivAt_arctanUpperGap (fun x => by positivity)

/-- The quintic upper alternating bound for arctangent on the nonnegative axis. -/
theorem arctan_quintic_upper {x : Real} (hx : 0 <= x) :
    Real.arctan x <= x - x ^ 3 / 3 + x ^ 5 / 5 := by
  have h := arctanUpperGap_monotone hx
  simpa [arctanUpperGap] using h

end

end HardyCriticalLine
