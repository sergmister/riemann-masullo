module

public import RiemannMasullo.Ch11_ShellStructure.Sec2a
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import RiemannMasullo.Ch10_TraceSpectral.Sec1

/-! # §11.2: the printed intersection of principal-value kernels -/

@[expose] public noncomputable section

open IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

local notation "C𝔽(" F ")" => IdeleClassGroup (𝓞 F) F
local notation "m𝔽(" F ")" =>
  (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽(F) →ₜ* ℝ≥0ˣ)
local notation "logNorm(" F ")" => (fun g : C𝔽(F) ↦ Real.log ((ideleClassNorm F g).val : ℝ))

/-- Paper: Proof of Proposition 11.2.0.1(2), p. 485. As printed: On each norm-one
isotype the range of the completed 0-line principal value is the common kernel
of the Mellin evaluations and derivatives through order |S₀| − 1 at every zero
of the reciprocal partial Euler product. `OrbitalJetIndex` uses the individual
multiplicities and `globalThetaSobolevPrincipalValue_range_closure` compares
closures. See ERRATA F163. -/
def Printed.globalThetaSobolevPrincipalValue_range_eq_jetKernels : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
    (χ : PontryaginDual C𝔽(F)) (s : ℝ) (hs : 0 ≤ s), 2 * (S₀.card : ℝ) ≤ s →
    let μ := ideleClassTamagawaMeasure F
    let hI := le_rfl (a := (0 : ℝ))
    let W := CompactIntervalSobolev μ logNorm(F) 0 0 s
    let H := globalThetaSobolev F 0 hI hs
    let P := globalThetaSobolevPrincipalValue F S₀ 0 hs
    let K := (ideleClassNorm F).ker
    let ω := χ.comp (⟨K.subtype, continuous_subtype_val⟩ : K →ₜ* C𝔽(F))
    let Wω := actionIsotype ((hardySobolevTranslation μ m𝔽(F) 0 0 s hI hs).comp K.subtype) ω
    ∀ u : Wω,
      (∃ f : H, (f : W) ∈ Wω ∧ (P f : W) = u.val) ↔
        ∀ (ε : ℂ), reciprocalPartialHeckeEulerProduct χ S₀ ε = 0 →
          ∀ j : ℕ, j < S₀.card →
            (∫ g, u.val g * ideleClassNormTwist χ ε g * (logNorm(F) g : ℂ) ^ j ∂μ) = 0

/-- Paper: Proof of Proposition 11.2.0.1(2), p. 485. Take ℚ, the trivial character,
the places over 2 and 3, and degree 4. The zero ε = 2πi/log 2 of the product
(1 − 2⁻ᶻ)(1 − 3⁻ᶻ) is simple, since log 3/log 2 is irrational. Use a nonzero
nonnegative smooth bump in the log norm multiplied by exp(−εx), so its Mellin
transform H has H(ε) ≠ 0. The profile belongs to the completed trivial isotype
by zero-line density. The principal-value image has Mellin derivative
P′(ε)H(ε) ≠ 0, whereas the printed intersection requires order one to vanish. -/
theorem Printed.globalThetaSobolevPrincipalValue_range_eq_jetKernels_false :
    ¬ Printed.globalThetaSobolevPrincipalValue_range_eq_jetKernels := by
  sorry

end RiemannMasullo
