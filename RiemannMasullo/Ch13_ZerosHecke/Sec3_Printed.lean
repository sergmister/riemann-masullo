module

public import RiemannMasullo.Ch13_ZerosHecke.Sec3
import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.AppB_AnalyticNT.Sec4b

/-! # Printed claims about the capped critical-line trace

The codimension and trace identity in Theorem 13.3.1.1 are distinct claims.
Nothing imports this file.
-/

@[expose] public noncomputable section

open Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 instFiniteCompletionUnitsLocallyCompactSec4b

local notation "C[" F "]" => IdeleClassGroup (𝓞 F) F
local notation "D[" F "]" => BruhatCompactSupport C[F]

/-- Paper: Theorem 13.3.1.1, p. 522. The common test subspace for all the
character jets in (13.3.1.2) is claimed to have codimension `[F : ℚ]`. -/
def Printed.criticalTraceTestCodimension : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (τ : ℝ≥0ˣ →ₜ* C[F]),
    RightInverse τ (ideleClassNorm F) →
    Module.rank ℂ (D[F] ⧸ criticalTraceTestSubmodule τ) = (Module.finrank ℚ F : Cardinal)

/-- Paper: Theorem 13.3.1.1, p. 522. Take `F = ℚ`, the section with positive real
component and finite components one, and identify the norm-one classes with
`ℤ̂ˣ`. Let `ω` be the nontrivial character of `(ℤ/4ℤ)ˣ`, pulled back along the
projection from `ℤ̂ˣ`. For a smooth compactly supported bump `b` with integral
one, the tests `b(log t)` and `b(log t) · conj (ω(k))` on `(t,k)` have, respectively,
moment pairs `(1,0)` and `(0,1)` for the trivial character and `ω`, by Haar
orthogonality. The common kernel therefore has codimension at least two. -/
theorem Printed.criticalTraceTestCodimension_false : ¬ Printed.criticalTraceTestCodimension :=
  by
  intro h
  let q : (AdeleRing (𝓞 ℚ) ℚ)ˣ →ₜ* C[ℚ] := ⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩
  let τ : ℝ≥0ˣ →ₜ* C[ℚ] := q.comp
    ⟨canonicalIdeleNormSection ℚ, canonicalIdeleNormSection_continuous ℚ⟩
  have hτ : RightInverse τ (ideleClassNorm ℚ) := canonicalIdeleNormSection_rightInverse ℚ
  have hrank := criticalTraceTestSubmodule_rat_codimension_ge_two τ hτ
  rw [h ℚ τ hτ, Module.finrank_self] at hrank
  norm_num at hrank

local notation "ord[" F "](" χ ", " s ")" =>
  MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ s
local notation "mellinAt[" F "](" φ ", " χ ", " s ")" =>
  (∫ g : C[F], (φ : D[F]).val g * ideleClassNormTwist (F := F) χ s g ∂ideleClassTamagawaMeasure F)

/-- Paper: Theorem 13.3.1.1, (13.3.1.3)–(13.3.1.5), p. 522. The capped
critical-line sum and the printed polar and local terms are claimed to converge
to the same continuous linear functional on the space satisfying (13.3.1.2). -/
def Printed.criticalTraceFormula : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (τ : ℝ≥0ˣ →ₜ* C[F]),
    RightInverse τ (ideleClassNorm F) →
    let A := criticalTraceTestSubmodule (F := F) τ
    let zeros := {z : {χ : PontryaginDual C[F] // ∀ t, χ (τ t) = 1} × ℂ //
      0 < ord[F](z.1.val, z.2) ∧ z.2.re = 1 / 2}
    ∃ L : A →L[ℂ] ℂ, ∀ φ : A,
      HasSum (fun z : zeros ↦
        (criticalTraceMultiplicity (F := F) z.val.1.val z.val.2 z.property.1 : ℂ) *
          mellinAt[F](φ.val, z.val.1.val, z.val.2 - 1 / 2)) (L φ) ∧
      ∃ (a : (w : InfinitePlace F) → BruhatCompactSupport w.Completionˣ)
        (b : (v : HeightOneSpectrum (𝓞 F)) → BruhatCompactSupport (v.adicCompletion F)ˣ),
        (∀ w u, (a w).val u = φ.val.val (IdeleClassGroup.ofCompletion (𝓞 F) F w u)) ∧
        (∀ v u, (b v).val u = φ.val.val (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u)) ∧
        HasSum (fun v : HeightOneSpectrum (𝓞 F) ↦ (Real.log (v.asIdeal.absNorm : ℝ) : ℂ) *
          finiteConnesWeilPrincipalValue (F := F) v 1 (b v))
          (mellinAt[F](φ.val, 1, -1 / 2) + mellinAt[F](φ.val, 1, 1 / 2) -
            (∑ w : InfinitePlace F, infiniteConnesWeilPrincipalValue w (a w)) - L φ)

/-- Paper: Theorem 13.3.1.1, (13.3.1.3)–(13.3.1.5), p. 522. Take
`F = ℚ(i)` and the test `φ_X(g) = f(log |g|_F − X)`, where `f = b''` and
`b(u) = exp(−1 / (u(1 − u)))` for `0 < u < 1`, extended by zero. Both radial
moments vanish by integration by parts, and all nontrivial norm-one characters
vanish by orthogonality. On the critical line translation multiplies each
Mellin value by a phase, so absolute convergence bounds the capped zero sum
uniformly in `X`. Write `J = ∫ f(u) exp(u/2) du > 0`. The polar sum is
`(π/4) J exp(X/2) + O(exp(−X/2))` by the norm-one Tamagawa volume. The
archimedean term is `O(exp(−X/2))`. On each finite shell of norm `qᵐ > 1`, the
term in (13.3.1.5) before the minus sign is `log(q) · q^(−m/2) · f(m log q − X)`
times the integer-unit mass. That mass is one off the prime above two, whose
contribution is `O(exp(−X/2))`. The prime ideal theorem and partial summation
give `J exp(X/2) + o(exp(X/2))` for the finite sum. Thus the printed right side
grows in magnitude like `(1 − π/4) J exp(X/2)` for large `X`. -/
theorem Printed.criticalTraceFormula_false : ¬ Printed.criticalTraceFormula := by sorry

end RiemannMasullo
