/-
Copyright 2026 ArtiFish26. Released under the Apache-2.0 license.
Ported from artifish26/riemann-hypothesis-lean at e9b20c778b19b5bba2e9a8e14a9bb4ca0afad850,
RiemannHypothesisProject/RiemannVonMangoldt/Binet/GaussDigammaHolomorphic.lean.
Selected dependencies of Hardy's theorem, renamed the namespace, and adapted to Mathlib v4.36.0.
See MODIFICATIONS.md for file-specific changes.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma

@[expose] public section

open Filter Set Topology

namespace HardyCriticalLine

noncomputable section

/-- The complex digamma function is analytic at every point of the right
half-plane. -/
theorem analyticAt_digamma_of_re_pos {z : Complex} (hz : 0 < z.re) :
    AnalyticAt Complex Complex.digamma z := by
  have hGammaDiff : DifferentiableAt Complex Complex.Gamma z :=
    Complex.differentiableAt_Gamma z (fun m => by
      intro h
      have hre := congrArg Complex.re h
      simp only [Complex.neg_re, Complex.natCast_re] at hre
      have hm : (0 : Real) ≤ m := Nat.cast_nonneg m
      linarith)
  have hGammaAnalytic : AnalyticAt Complex Complex.Gamma z :=
    (Meromorphic.Gamma z).analyticAt hGammaDiff.continuousAt
  have hquotient := hGammaAnalytic.deriv.div hGammaAnalytic
    (Complex.Gamma_ne_zero_of_re_pos hz)
  simpa [Complex.digamma_def, logDeriv] using hquotient

end

end HardyCriticalLine
