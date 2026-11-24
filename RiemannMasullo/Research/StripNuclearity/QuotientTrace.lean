module

public import RiemannMasullo.Research.StripNuclearity.WindowComparison
import RiemannMasullo.Ch03_IdelicZeta.Sec2

/-! # The spectral trace of a test pulled back from a norm-preserving quotient

A character nontrivial on a quotient fiber has zero Mellin coefficient. Every
surviving character descends continuously, and the quotient integral acquires
the scalar from the pushforward of Haar measure.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set
open scoped ENNReal NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo.StripNuclearity

variable {F : Type*} [Field F] [NumberField F]

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

set_option quotPrecheck false
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "X" => PontryaginDual C₁
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" => (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "hm𝔽" => (⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ : IsModulation m𝔽)
local notation "D(" χ ")" => MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ
local notation "zeros(" χ ")" => {z : X × ℂ // 0 < D(χ z.1) z.2}
local notation "M(" φ ", " χ ", " s ")" =>
  modulatedFourierMellin m𝔽 univ hm𝔽 μ𝔽 (φ : BruhatCompactSupport C𝔽).val (ideleClassNormTwist (F := F) χ s)
local notation "kept(" χ ", " α ", " s ", " z ")" =>
  spectralStripMultiplicity α s ((z).val.2.re - 1/2) (D(χ (z).val.1) (z).val.2).toNat

variable {J : Type*} [CommGroup J] [TopologicalSpace J] [IsTopologicalGroup J]

/-- A character trivial on the kernel descends along an open quotient map. -/
theorem traceQuotient_character (π : C𝔽 →ₜ* J) (hπ : IsOpenQuotientMap π)
    (ψ : PontryaginDual C𝔽) (h : π.toMonoidHom.ker ≤ ψ.toMonoidHom.ker) :
    ∃! η : PontryaginDual J, ∀ x, η (π x) = ψ x := by
  obtain ⟨i,hi⟩ := hπ.surjective.hasRightInverse
  let η := π.toMonoidHom.liftOfRightInverseAux i hi ψ.toMonoidHom h
  have hs (x : C𝔽) : η (π x) = ψ x := MonoidHom.liftOfRightInverseAux_comp_apply ..
  refine ⟨⟨η, hπ.continuous_comp_iff.mp (ψ.continuous.congr (fun x ↦ (hs x).symm))⟩, hs, ?_⟩
  intro η' he
  apply ContinuousMonoidHom.ext
  intro y
  obtain ⟨x,rfl⟩ := hπ.surjective y
  exact (he x).trans (hs x).symm

private theorem mellin_vanishes_off_quotient (π : C𝔽 →ₜ* J) (n : J →ₜ* ℝ≥0ˣ)
    (hn : ∀ x, n (π x) = ideleClassNorm F x) (φ : BruhatCompactSupport C𝔽) (b : J → ℂ)
    (hb : ∀ x, b (π x) = φ.val x) (ψ : PontryaginDual C𝔽) (w : ℂ)
    (he : ¬ π.toMonoidHom.ker ≤ ψ.toMonoidHom.ker) :
    M(φ, ψ, w) = 0 := by
  obtain ⟨u,hu,hψ⟩ := Set.not_subset.mp he
  have hpu : π u = 1 := hu
  have hnu : ideleClassNorm F u = 1 := by rw [← hn, hpu, map_one]
  have hχ : (ψ u : ℂ) ≠ 1 := fun h ↦ hψ (Subtype.ext h)
  let f (x : C𝔽) := φ.val x * ideleClassNormTwist ψ w x
  have tr (x : C𝔽) : f (u*x) = (ψ u : ℂ) * f x := by
    have ht : φ.val (u*x) = φ.val x := by rw [← hb, map_mul, hpu, one_mul, hb]
    change φ.val _ * _ = _ * (φ.val x * _)
    rw [ht, map_mul]
    change _ * ((ψ u : ℂ) * (((ideleClassNorm F u).val : ℝ) : ℂ) ^ w * _) = _
    simp only [hnu, Units.val_one, NNReal.coe_one, Complex.ofReal_one, Complex.one_cpow, mul_one]
    ring
  let I := ∫ x, f x ∂μ𝔽
  have hI : I = (ψ u : ℂ) * I := by
    rw [← integral_const_mul]
    exact (integral_mul_left_eq_self (μ := μ𝔽) f u).symm.trans (integral_congr_ae (.of_forall tr))
  simp only [modulatedFourierMellin, relativeVerticalStrip, preimage_univ, indicator_univ]
  exact (mul_eq_zero.mp (by linear_combination -hI : ((ψ u : ℂ) - 1) * I = 0)).resolve_left
    (sub_ne_zero.mpr hχ)

local notation "visible(" π ", " χ ")" => {z : zeros(χ) // (π).toMonoidHom.ker ≤ (χ z.val.1).toMonoidHom.ker}

variable [MeasurableSpace J] [BorelSpace J]

/-- Reindex a global jet sum by the fiber-trivial characters and evaluate
each of their Mellin coefficients on the quotient with its own Haar measure. -/
theorem hasSum_quotientMellin_of_keptJetSum (π : C𝔽 →ₜ* J) (hπ : IsOpenQuotientMap π)
    (n : J →ₜ* ℝ≥0ˣ) (hn : ∀ x, n (π x) = ideleClassNorm F x)
    (μ : Measure J) (c : ℝ≥0∞) (hμ : (μ𝔽).map π = c • μ)
    (φ : BruhatCompactSupport C𝔽) (b : J → ℂ) (hc : Continuous b) (hb : ∀ x, b (π x) = φ.val x)
    (χ : X → PontryaginDual C𝔽) (α s : ℝ) {r : ℂ}
    (ht : HasSum (fun z : zeros(χ) ↦ (kept(χ, α, s, z) : ℂ) * M(φ, χ z.val.1, z.val.2-1/2)) r) :
    ∃ η : visible(π, χ) → PontryaginDual J,
      (∀ z x, η z (π x) = χ z.val.val.1 x) ∧
      HasSum (fun z : visible(π, χ) ↦ (kept(χ, α, s, z.val) : ℂ) *
        (c.toReal • ∫ j, b j * ((η z j : ℂ) * (((n j).val : ℝ) : ℂ) ^ (z.val.val.2-1/2)) ∂μ)) r := by
  classical
  choose η hη using fun z : visible(π, χ) ↦ (traceQuotient_character π hπ (χ z.val.val.1) z.property).exists
  refine ⟨η, hη, ?_⟩
  let term (z : zeros(χ)) := (kept(χ, α, s, z) : ℂ) * M(φ, χ z.val.1, z.val.2-1/2)
  have hp : support term ⊆ {z : zeros(χ) | π.toMonoidHom.ker ≤ (χ z.val.1).toMonoidHom.ker} := by
    intro z hz
    by_contra h
    exact hz (by dsimp only [term]; rw [mellin_vanishes_off_quotient π n hn φ b hb _ _ h, mul_zero])
  apply ((hasSum_subtype_iff_of_support_subset hp).mpr ht).congr_fun
  intro z
  apply congrArg ((kept(χ, α, s, z.val) : ℂ) * ·)
  let w := z.val.val.2-1/2
  let g (j : J) := b j * ((η z j : ℂ) * (((n j).val : ℝ) : ℂ) ^ w)
  have hpN : Continuous (fun j : J ↦ (((n j).val : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp (Units.continuous_val.comp n.continuous))
  have hg : Continuous g := hc.mul ((continuous_subtype_val.comp (η z).continuous).mul
    (hpN.cpow continuous_const fun j ↦ Complex.ofReal_mem_slitPlane.mpr (NNReal.coe_pos.mpr (Units.zero_lt _))))
  have ht' (x : C𝔽) : φ.val x * ideleClassNormTwist (χ z.val.val.1) w x = g (π x) := by
    change φ.val x * ((χ z.val.val.1 x : ℂ) * (((ideleClassNorm F x).val : ℝ) : ℂ) ^ w) = _
    simp only [g, hb, hn, hη]
  simp only [modulatedFourierMellin, relativeVerticalStrip, preimage_univ, indicator_univ]
  change c.toReal • (∫ j, g j ∂μ) = ∫ x, φ.val x * ideleClassNormTwist (χ z.val.val.1) w x ∂μ𝔽
  simp_rw [ht']
  have hm : Measurable (π : C𝔽 → J) := π.continuous.measurable
  rw [← integral_map hm.aemeasurable hg.aestronglyMeasurable, hμ, integral_smul_measure]

local notation "quotientTrace(" π ", " hπ ", " n ", " hn ", " μ ", " c ", " hμ ", " φ ", " hφ ", " b ", "
    hc ", " hb ", " χ ", " hχ ", " α ", " s ", " hα ", " hs ", " U ", " hU ", " hm ")" =>
  hasSum_quotientMellin_of_keptJetSum π hπ n hn μ c hμ φ b hc hb χ α s
    (hasSum_keptHeckeZeros_neg_centeredStripDiagonalIntegral (F := F) φ hφ χ hχ hα hs U hU hm)

/-- Paper: Section 12.3, p. 514, and (12.5.1.4), p. 520.
For a test pulled back from a norm-preserving open quotient, the negative
geometric diagonal integral is a Mellin sum on that quotient. The characters
are exactly the ones trivial on the kernel, and the scalar is the Haar
pushforward factor. The quotient retains the original strip multiplicities.
Deviation: This evaluates the spectral expansion under descent. Identifying
it with the S-local cutoff operator is the remaining comparison. -/
theorem hasSum_quotientMellin_neg_centeredStripDiagonalIntegral
    (π : C𝔽 →ₜ* J) (hπ : IsOpenQuotientMap π) (n : J →ₜ* ℝ≥0ˣ)
    (hn : ∀ x, n (π x) = ideleClassNorm F x) (μ : Measure J) (c : ℝ≥0∞)
    (hμ : (μ𝔽).map π = c • μ) (φ : BruhatCompactSupport C𝔽) (hφ : ∀ g : C₁, φ.val g = 0)
    (b : J → ℂ) (hc : Continuous b) (hb : ∀ x, b (π x) = φ.val x)
    (χ : X → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    {α s : ℝ} (hα : 0 < α) (hs : 3 ≤ s) (U : ℕ → Set C𝔽)
    (hU : IsDPrimeSequence μ𝔽 U) (hm : ∀ k, MeasurableSet (U k)) :
    type_of% quotientTrace(π, hπ, n, hn, μ, c, hμ, φ, hφ, b, hc, hb, χ, hχ, α, s, hα, hs, U, hU, hm) :=
  quotientTrace(π, hπ, n, hn, μ, c, hμ, φ, hφ, b, hc, hb, χ, hχ, α, s, hα, hs, U, hU, hm)

end RiemannMasullo.StripNuclearity
