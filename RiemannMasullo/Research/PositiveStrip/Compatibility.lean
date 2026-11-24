module
public import RiemannMasullo.Research.PositiveStrip.Chart
public import RiemannMasullo.Research.PositiveStrip.SingleGenerator
import all RiemannMasullo.Ch09_HardySobolev.Sec2

@[expose] public noncomputable section
open Filter Function MeasureTheory NumberField Set
open scoped Topology NNReal NumberField.AdeleRing
namespace RiemannMasullo.StripDual
set_option quotPrecheck false
variable {F : Type*} [Field F] [NumberField F]
attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" => (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "logNorm" => (fun g : C𝔽 ↦ Real.log ((ideleClassNorm F g).val : ℝ))
local notation "W(" l ", " r ", " s ")" => CompactIntervalSobolev μ𝔽 logNorm l r s
local notation "hm𝔽" => (⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ : IsModulation m𝔽)
local notation "hms𝔽" => (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.2.2.2.1

/-- Agreement of radial profiles on Lebesgue measure transports to their
inverse-character lifts for the Tamagawa measure. -/
theorem radial_rep {α s : ℝ} (ψ : PontryaginDual C𝔽)
    (L : SE α s →L[ℂ] W(-α,α,s))
    (hL : ∀ f, (L f : C𝔽 → ℂ) =ᵐ[μ𝔽] fun x ↦ (ψ x : ℂ)⁻¹ * f (logNorm x))
    (f : SE α s) (q : ℝ → ℂ) (hq : (f : ℝ → ℂ) =ᵐ[volume] q) :
    (L f : C𝔽 → ℂ) =ᵐ[μ𝔽] fun x ↦ ((ψ⁻¹ x : Circle) : ℂ) * q (logNorm x) := by
  let ν := canonicalModulatedHaar m𝔽 hm𝔽
  let : ν.IsHaarMeasure := (existsUnique_canonicalModulatedHaar m𝔽 hm𝔽).exists.choose_spec.1
  have hv := (sobolev_log_preserving m𝔽 hm𝔽 hms𝔽).quasiMeasurePreserving.ae_eq_comp hq
  have ht := (Measure.absolutelyContinuous_isHaarMeasure μ𝔽 ν).ae_eq hv
  filter_upwards [hL f,ht] with x hx hy
  rw [hx]
  change (ψ x : ℂ)⁻¹ * f (logNorm x) = (((ψ x)⁻¹ : Circle) : ℂ) * q (logNorm x)
  rw [Circle.coe_inv]
  exact congrArg ((ψ x : ℂ)⁻¹ * ·) hy

/-- The cutoffs preserve membership of every generator times every entire test
in the geometric theta space. The cutoff can be moved onto the test, after
which its inverse Mellin transform supplies the radial convolution kernel. -/
theorem cutoff_generator_mem {α s a r : ℝ} (ha : 0 ≤ α) (hs : 0 ≤ s) (hr : α+s/2 < r)
    (ψ : PontryaginDual C𝔽) (e : Tests →ₗ[ℂ] SE α s)
    (L : SE α s →L[ℂ] W(-α,α,s))
    (hL : ∀ f, (L f : C𝔽 → ℂ) =ᵐ[μ𝔽] fun x ↦ (ψ x : ℂ)⁻¹ * f (logNorm x))
    (U : SE α s →L[ℂ] SE α s) (b : ℂ → ℂ)
    (hU : ∀ H : Tests, ∃ q : PositiveRealExponentialDecay (Ioo (-r) r),
      (U (e H) : ℝ → ℂ) =ᵐ[volume] q.val ∧ ∀ z, z.re ∈ Ioo (-r) r →
        mellin (fun t ↦ q.val (Real.log t)) z = b z * H.val z)
    (f : adelePolarSubspace F) (H Q : Tests)
    (hQ : ∀ z, Q.val z = globalThetaMellinIntegral f.val (ideleClassNormTwist ψ ((a:ℂ)+z)) * H.val z) :
    L (U (e Q)) ∈ globalThetaSobolev F a (neg_le_self ha) hs := by
  have h0 : 0 ∈ Ioo (-r) r := ⟨by linarith,by linarith⟩
  obtain ⟨p,-,hp⟩ := hU H
  obtain ⟨q,hq,hqM⟩ := hU Q
  apply stripTheta_generator_product_mem h0 α s a ha hs
    (show -(α+s/2) ∈ Ioo (-r) r from ⟨by linarith,by linarith⟩)
    (show α+s/2 ∈ Ioo (-r) r from ⟨by linarith,hr⟩)
    ψ f p _ q (radial_rep ψ L hL _ q.val hq)
  intro t
  have hz : ((t:ℂ)*Complex.I).re ∈ Ioo (-r) r := by simpa using h0
  rw [hqM _ hz, hp _ hz, hQ]
  ring

end RiemannMasullo.StripDual
