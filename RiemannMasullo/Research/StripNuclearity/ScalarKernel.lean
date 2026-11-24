module

public import RiemannMasullo.Ch09_HardySobolev.Sec3
public import RiemannMasullo.Research.StripNuclearity.RadialConvolution
public import RiemannMasullo.Research.StripNuclearity.CompactYoung

/-!
# Compactly supported convolution on additive radial coordinates

The multiplicative form of Chapter 9 transports along the ordinary exponential
isomorphism to the additive real convolution on the scalar weighted space.
-/

@[expose] public noncomputable section

open Function Filter MeasureTheory Set
open scoped Topology NNReal ContDiff Convolution
namespace RiemannMasullo.StripNuclearity

private abbrev radialHaar : Measure (Multiplicative ℝ) := (volume : Measure ℝ)

private instance : radialHaar.IsHaarMeasure := by
  let : IsFiniteMeasureOnCompacts radialHaar := inferInstanceAs (IsFiniteMeasureOnCompacts (volume : Measure ℝ))
  let : Measure.IsOpenPosMeasure radialHaar := inferInstanceAs (Measure.IsOpenPosMeasure (volume : Measure ℝ))
  let : radialHaar.IsMulLeftInvariant :=
    ⟨fun t ↦ (measurePreserving_add_left (volume : Measure ℝ) t.toAdd).map_eq⟩
  constructor

/-- The exponential group isomorphism from logarithmic real coordinates to
positive multiplicative units. -/
def radialExponential : Multiplicative ℝ ≃ₜ* ℝ≥0ˣ :=
  { Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm with
    map_mul' := fun x y ↦ by
      apply Units.ext
      apply NNReal.eq
      exact Real.exp_add x.toAdd y.toAdd }

private def radialExp : Multiplicative ℝ ≃ₜ* ℝ≥0ˣ := radialExponential

/-- The underlying real value of the logarithmic-coordinate exponential. -/
@[simp] theorem radialExponential_val (t : ℝ) :
    ((radialExponential (Multiplicative.ofAdd t)).val : ℝ) = Real.exp t := rfl

private def radialModule : Multiplicative ℝ →ₜ* ℝ≥0ˣ := ⟨radialExp,radialExp.continuous⟩

/-- Ordinary additive convolution by a continuous compactly supported kernel
acts boundedly on the actual radial weighted Hilbert space. -/
theorem exists_scalar_weighted_convolution (a b s : ℝ) (hab : a ≤ b) (hs : 0 ≤ s)
    (κ : ℝ → ℂ) (hc : Continuous κ) (hk : HasCompactSupport κ) :
    let E := CompactIntervalSobolev volume id a b s
    ∃ A : E →L[ℂ] E, ∀ f, ∀ᵐ x ∂volume,
      Integrable (fun t : ℝ ↦ κ t * f (x-t)) volume ∧
        A f x = ∫ t : ℝ, κ t * f (x-t) := by
  intro E
  let μ := radialHaar
  let m := radialModule
  let ℓ (x : Multiplicative ℝ) := Real.log ((m x).val : ℝ)
  have hlog : ℓ = (id : ℝ → ℝ) := funext fun x ↦ Real.log_exp x
  have hb : ∃ C : ℝ, ∀ x, ‖κ x‖ ≤ C := hc.bounded_above_of_compact_support hk
  let A := hardySobolevConvolution μ m a b s hab hs κ hc.aemeasurable hk hb
  let Acts (l : Multiplicative ℝ → ℝ) : Prop :=
    let X := CompactIntervalSobolev μ l a b s
    ∃ B : X →L[ℂ] X, ∀ f, ∀ᵐ x ∂μ,
      Integrable (fun t : Multiplicative ℝ ↦ κ t.toAdd * f (t⁻¹*x)) μ ∧
        B f x = ∫ t : Multiplicative ℝ, κ t.toAdd * f (t⁻¹*x) ∂μ
  have hA : Acts ℓ :=
    ⟨A, fun f ↦ hardySobolevConvolution_apply μ m a b s hab hs κ hc.aemeasurable hk hb f⟩
  obtain ⟨B,hB⟩ := (congrArg Acts hlog).mp hA
  refine ⟨B, fun f ↦ ?_⟩
  have hh := hB f
  change ∀ᵐ (x : ℝ) ∂volume, Integrable (fun t : ℝ ↦ κ t * f (-t+x)) volume ∧
    B f (Multiplicative.ofAdd x) = ∫ t : ℝ, κ t * f (-t+x) at hh
  filter_upwards [hh] with x hx
  simp only [sub_eq_neg_add]
  convert hx using 1
  rfl

/-- On a fixed compact set in the real logarithmic coordinate, every smooth
kernel acts on the weighted Sobolev space with operator norm at most a common
constant times its ordinary L¹ norm. An a.e. convolution formula suffices
to identify the operator. -/
theorem scalar_convolution_uniform_on_compact (a b s : ℝ) (hab : a ≤ b) (hs : 0 ≤ s)
    {J : Set ℝ} (hJ : IsCompact J) :
    let E := CompactIntervalSobolev volume id a b s
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (κ : ℝ → ℂ), tsupport κ ⊆ J → ContDiff ℝ ∞ κ →
      ∀ A : E →L[ℂ] E, (∀ u, ∀ᵐ x ∂volume, A u x = ∫ y : ℝ, κ y*u (x-y)) →
        ‖A‖ ≤ C * ∫ y : ℝ, ‖κ y‖ := by
  intro E
  let μ := radialHaar
  let m := radialModule
  let ℓ (g : Multiplicative ℝ) := Real.log ((m g).val : ℝ)
  have hlog : ℓ = (id : ℝ → ℝ) := funext fun g ↦ Real.log_exp g
  let acts (l : Multiplicative ℝ → ℝ) : Prop :=
    let H := CompactIntervalSobolev μ l a b s
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (κ : ℝ → ℂ), tsupport κ ⊆ J → ContDiff ℝ ∞ κ →
      ∀ A : H →L[ℂ] H, (∀ u, ∀ᵐ (x : ℝ) ∂volume, A u (Multiplicative.ofAdd x) =
        ∫ y : ℝ, κ y*u (Multiplicative.ofAdd (x-y))) →
        ‖A‖ ≤ C * ∫ y : ℝ, ‖κ y‖
  suffices h : acts ℓ from (congrArg acts hlog).mp h
  let ρ := hardySobolevTranslation μ m a b s hab hs
  have hρ := (exists_hardySobolevTranslation μ m a b s hab hs).choose_spec.2
  obtain ⟨C,hC,h⟩ := norm_bruhatRegularizedAction_le_on_compact μ ρ hρ (J := J) hJ
  refine ⟨C,hC,fun κ hK hsm A hA ↦ ?_⟩
  let φ : BruhatCompactSupport (Multiplicative ℝ) := ⟨κ,(mem_bruhatCompactSupportSubmodule_real_iff _).mpr
    ⟨hsm,hJ.of_isClosed_subset isClosed_closure hK⟩⟩
  apply A.opNorm_le_bound (mul_nonneg hC (integral_nonneg fun _ ↦ norm_nonneg _))
  intro u
  have he : A u = hardySobolevTestAction μ m a b s hab hs φ u := by
    apply Lp.ext
    apply (withDensity_absolutelyContinuous μ _).ae_eq
    have htest := hardySobolevTestAction_apply μ m a b s hab hs φ u
    filter_upwards [hA u,htest] with x hx hy
    change A u x = _ at hx
    rw [hy,hx]
    change (∫ y : ℝ, κ y*u (x.toAdd-y)) = ∫ y : ℝ, κ y*u (-y+x.toAdd)
    simp only [sub_eq_neg_add]
  rw [he]
  exact h φ hK u

/-- A smooth compactly supported real convolution kernel with two L² masks
is trace class on the weighted measure. The masks may be fixed independently
of the convolution symbol. -/
theorem exists_nuclear_masked_scalar_kernel (ν : Measure ℝ) [SigmaFinite ν]
    (κ : ℝ → ℂ) (hκ : HasCompactSupport κ) (hs : ContDiff ℝ ∞ κ)
    (l r : ℝ → ℂ) (hl : MemLp l 2 ν) (hr : MemLp r 2 ν) :
    ∃ (T : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν), IsNuclearOperator T ∧
      ∀ u, ∀ᵐ (x : ℝ) ∂ν, T u x = ∫ y : ℝ, l x*κ (x-y)*star (r y)*u y ∂ν := by
  have hm : IsModulation radialModule := by
    refine ⟨radialExp.toHomeomorph.isProperMap,Multiplicative.ofAdd (1 : ℝ),?_⟩
    intro h
    have he := congrArg (fun t : ℝ≥0ˣ ↦ Real.log (t.val : ℝ)) h
    change Real.log (Real.exp 1) = Real.log 1 at he
    simp at he
  have hσ : @SigmaFinite (Multiplicative ℝ) inferInstance ν := inferInstanceAs (SigmaFinite (ν : Measure ℝ))
  have hκs : IsBruhatSmooth (G := Multiplicative ℝ) (fun x ↦ κ x.toAdd) :=
    (isBruhatSmooth_real_iff _).mpr hs
  obtain ⟨T,hT,happly,-⟩ := @masked_bruhat_convolution_nuclear (Multiplicative ℝ) _ _ _ _ _ _ _ _
    radialHaar _ radialModule hm radialExp.surjective (fun x ↦ κ x.toAdd) hκ hκs ν hσ l r hl hr
  refine ⟨T,hT,fun u ↦ ?_⟩
  have ht := happly u
  filter_upwards [ht] with x hx
  convert hx using 1
  rfl

end RiemannMasullo.StripNuclearity
