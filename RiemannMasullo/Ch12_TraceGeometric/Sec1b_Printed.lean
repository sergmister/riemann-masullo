module

public import RiemannMasullo.Ch12_TraceGeometric.Sec1b
import RiemannMasullo.Ch10_TraceSpectral.Sec1

/-! # The weighted spectral kernel in Remark 12.1.1.4 -/

@[expose] public noncomputable section

open MeasureTheory NumberField
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

attribute [local instance] uniformContinuousConstSMul_of_continuousConstSMul

local notation "C𝔽(" F ")" => IdeleClassGroup (𝓞 F) F
local notation "μ(" F ")" => ideleClassTamagawaMeasure F
local notation "logNorm(" F ")" => (fun g : C𝔽(F) ↦ Real.log ((ideleClassNorm F g).val : ℝ))
local notation "w(" F ", " s ")" => (fun g : C𝔽(F) ↦ intervalSobolevDensity (-(0 : ℝ)) 0 s (logNorm(F) g))
local notation "ν(" F ", " s ")" => ((μ(F)).withDensity fun g ↦ ENNReal.ofReal (w(F, s) g))
local notation "hs₁(" hs ")" => (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 3) hs)

/-- Paper: Remark 12.1.1.4, p. 503. For a test vanishing at the identity,
the global spectral kernel of Definition 10.4.3.2 divided by its input weight is
claimed to fail square integrability against the product of the two positive
Sobolev measures. The print writes `k^spec_{φ,a,s}(x,y)`, without a tilde, and
does not say which variable carries the weight; it is the input variable, as
in (10.4.3.30). -/
def Printed.globalLineSpectralKernel_weighted_not_memLp : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (a s : ℝ), 0 < a → ∀ hs : 3 ≤ s,
    ∀ (φ : BruhatCompactSupport C𝔽(F)), φ.val 1 = 0 →
      ¬ MemLp (fun p : C𝔽(F) × C𝔽(F) ↦
          ((w(F, s) p.2)⁻¹ : ℝ) • (globalLineSpectralKernel (F := F) a hs₁(hs) φ : _ → ℂ) p) 2
        ((ν(F, s)).prod (ν(F, s)))

/-- Paper: Remark 12.1.1.4, p. 503. Take the zero test over the rationals
with twist one and Sobolev degree four. Theorem 10.4.3.4(2) makes the weighted
spectral kernel the Hilbert–Schmidt kernel of spectral projection after
convolution, so it is square integrable. For the zero test that operator is
zero and its kernel has squared norm zero. -/
theorem Printed.globalLineSpectralKernel_weighted_not_memLp_false :
    ¬ Printed.globalLineSpectralKernel_weighted_not_memLp := by
  intro h
  let φ : BruhatCompactSupport C𝔽(ℚ) := 0
  have hs : (3 : ℝ) ≤ 4 := by norm_num
  exact h ℚ 1 4 zero_lt_one hs φ rfl
    (globalLineSpectralKernel_weighted_memLp (F := ℚ) 1 hs φ zero_lt_one)

end RiemannMasullo
