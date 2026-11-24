module
public import RiemannMasullo.Research.PositiveStrip.Evaluation
public import RiemannMasullo.Ch10_TraceSpectral.Sec2
import all RiemannMasullo.Ch10_TraceSpectral.Sec2

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set
open scoped Topology
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false

variable {F : Type*} [Field F] [NumberField F]

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" =>
  (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "logNorm" => (fun g : C𝔽 ↦ Real.log ((ideleClassNorm F g).val : ℝ))
local notation "W(" l ", " r ", " s ")" => CompactIntervalSobolev μ𝔽 logNorm l r s
local notation "hm𝔽" => (⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ :
  IsModulation m𝔽)
local notation "Ws(" α ", " s ")" => CompactIntervalSobolev volume id (-α) α s
local notation "stripJet(" χ ", " j ")" =>
  spectralZeroJet (χ (j).val.1) (j).val.2.1 (j).val.2.2.1 (j).val.2.2.2
local notation "uJet(" χ ", " hα ", " hs ", " j ")" =>
  (spectralStripJet_memLp χ hα hs j).toLp (stripJet(χ, j))
open scoped Classical

/-- An admitted jet on an inverse Hecke-character component agrees with its
bounded scalar Mellin derivative on the entire radial Sobolev space. The
Tamagawa/canonical Haar factor is explicit. All other angular components vanish. -/
theorem spectralStripJet_pairing_radial_eval
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ) (ω : PontryaginDual C₁)
    {a α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (j : SpectralStripJetIndex χ a α s)
    (K : Ws(α, s) →L[ℂ] W(-α, α, s))
    (hK : ∀ f, (K f : C𝔽 → ℂ) =ᵐ[μ𝔽] fun x ↦ (χ ω x : ℂ)⁻¹ * f (logNorm x))
    (ν : Measure C𝔽) [ν.IsHaarMeasure] (hlog : MeasurePreserving logNorm ν volume)
    (Λ : Ws(α, s) →L[ℂ] ℂ)
    (hΛ : ∀ (p : PositiveRealExponentialDecay univ) (f : Ws(α, s)),
      (f : ℝ → ℂ) =ᵐ[volume] p.val →
        Λ f = iteratedDeriv j.val.2.2.2 (mellin (fun t ↦ p.val (Real.log t))) ((j.val.2.1 : ℂ) + (j.val.2.2.1 : ℂ) * Complex.I)) :
    ∀ f, spectralSobolevPairing (K f) (uJet(χ, hα, hs, j)) =
      if j.val.1 = ω then ((Measure.haarScalarFactor μ𝔽 ν : ℝ) : ℂ) *
        Λ f else 0 := by
  let c : ℂ := ((Measure.haarScalarFactor μ𝔽 ν : ℝ) : ℂ)
  let T := (modulatedIntervalSobolev_dual m𝔽 hm𝔽 μ𝔽 (-α) α s (neg_le_self hα) hs).exists.choose
  let u := uJet(χ, hα, hs, j)
  let e := T.symm u
  have he (y : W(-α, α, s)) : spectralSobolevPairing y u = e y :=
    ((spectralSobolevPairing_dual (neg_le_self hα) hs e y).2.trans
      (congrArg (spectralSobolevPairing y) (T.apply_symm_apply u))).symm
  have hc : Continuous fun f : Ws(α, s) ↦ spectralSobolevPairing (K f) u := by
    simp only [he]
    exact e.continuous.comp K.continuous
  have hright : Continuous (fun f : Ws(α, s) ↦ if j.val.1 = ω then c * Λ f else 0) := by
    by_cases h : j.val.1 = ω
    · simp only [ite_eq_left h]
      fun_prop
    · simp only [ite_eq_right h]
      exact continuous_const
  obtain ⟨P, -, hd, hP⟩ := scalarIntervalSobolev_dense (-α) α s (neg_le_self hα) hs univ
    isOpen_univ ordConnected_univ (subset_univ _)
  intro f
  change spectralSobolevPairing (K f) u = if j.val.1 = ω then c * Λ f else 0
  refine hd.induction_on f (isClosed_eq hc hright) (fun p ↦ ?_)
  have ht := hlog.quasiMeasurePreserving.ae_eq_comp (hP p)
  have hp : (K (P p) : C𝔽 → ℂ) =ᵐ[μ𝔽] fun x ↦ (χ ω x : ℂ)⁻¹ * p.val (logNorm x) := by
    refine (hK _).trans ?_
    apply (Measure.absolutelyContinuous_isHaarMeasure μ𝔽 ν).ae_eq
    filter_upwards [ht] with x hx using congrArg ((χ ω x : ℂ)⁻¹ * ·) hx
  change spectralSobolevPairing (K (P p)) (uJet(χ, hα, hs, j)) = _
  rw [stripTail_profile_pairing χ hχ ω hα hs isOpen_univ (subset_univ _) ν
    hlog p (K (P p)) hp j, hΛ p (P p) (hP p)]

end RiemannMasullo

namespace RiemannMasullo.SharpStripEval

/-- For a zero of multiplicity `N`, the exact strip index is equivalent to a
derivative below `N` extending continuously to the scalar Sobolev space. -/
theorem lt_spectralStripMultiplicity_iff_bounded_eval (α s : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s)
    (N k : ℕ) (z : ℂ) :
    k < spectralStripMultiplicity α s z.re N ↔ k < N ∧
      ∃ Λ : CompactIntervalSobolev volume id (-α) α s →L[ℂ] ℂ,
        ∀ (f : PositiveRealExponentialDecay univ) (u : CompactIntervalSobolev volume id (-α) α s),
          (u : ℝ → ℂ) =ᵐ[volume] f.val →
          Λ u = iteratedDeriv k (mellin (fun t ↦ f.val (Real.log t))) z := by
  rw [scalarIntervalSobolev_eval_iff α s hα hs k z]
  have he : (z.re = -α ∨ z.re = α) ↔ |z.re| = α := by
    rcases le_total 0 z.re with hz | hz
    · rw [abs_of_nonneg hz]
      constructor
      · rintro (h | h) <;> linarith
      · exact Or.inr
    · rw [abs_of_nonpos hz]
      constructor
      · rintro (h | h) <;> linarith
      · exact fun h ↦ Or.inl (by linarith)
  by_cases hi : |z.re| < α
  · rw [spectralStripMultiplicity_interior (abs_lt.mp hi) s N]
    simp [hi]
  · by_cases hedge : |z.re| = α
    · rw [spectralStripMultiplicity_boundary hα (he.mpr hedge) s N, lt_spectralBoundaryMultiplicity]
      simp only [hedge, lt_self_iff_false, false_or, true_and]
      exact and_congr_right fun _ ↦ by constructor <;> intro h <;> linarith
    · have hni : ¬ (-α < z.re ∧ z.re < α) := fun h ↦ hi (abs_lt.mpr h)
      have hne : ¬ (z.re = -α ∨ z.re = α) := fun h ↦ hedge (he.mp h)
      simp [spectralStripMultiplicity, hni, hne, hi, hedge]

end RiemannMasullo.SharpStripEval
