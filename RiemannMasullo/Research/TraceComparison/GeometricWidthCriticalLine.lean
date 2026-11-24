module

public import RiemannMasullo.Research.TraceComparison.GeometricWidthContinuity
import RiemannMasullo.Ch01_Introduction.Sec4

/-! # The one-sided geometric comparison and the Hecke critical line

The geometric condition is imposed on scalar diagonal integrals of physical
tests. Exterior-zero detection supplies the converse at each width and
norm-twist transport passes from normalized to arbitrary characters.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo.StripNuclearity

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" =>
  (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "hm𝔽" => (⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ :
  IsModulation m𝔽)
local notation "M(" φ ", " c ")" =>
  modulatedFourierMellin m𝔽 univ hm𝔽 μ𝔽 (φ : BruhatCompactSupport C𝔽).val c
local notation "twist(" χ ", " s ")" => ideleClassNormTwist (F := F) χ s
local notation "ord(" χ ", " s ")" =>
  MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ s
local notation "zeroTerm(" φ ", " z ")" =>
  ((ord((z).val.1.val, (z).val.2) : ℤ) : ℂ) * M(φ, twist((z).val.1.val, (z).val.2 - 1 / 2))
local notation "exteriorZeros(" τ ", " α ")" =>
  {z : {χ : PontryaginDual C𝔽 // ∀ t : ℝ≥0ˣ, χ (τ t) = 1} × ℂ //
    0 < ord(z.1.val, z.2) ∧ α ≤ |z.2.re - 1 / 2|}

/-- Paper: Theorem 12.5.1.1, pp. 519–520, and §1.4.5, pp. 29–30. For a fixed norm section over any number field, all-width cancellation for
the normalized characters is equivalent to the critical-line assertion for
every unitary Hecke character of the field. -/
private theorem all_exterior_iff_criticalLine
    (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F)) :
    (∀ (α : ℝ), 0 < α → ∀ φ : BruhatCompactSupport C𝔽, (∀ g : C₁, φ.val g = 0) →
      HasSum (fun z : exteriorZeros(τ, α) ↦ zeroTerm(φ, z)) 0) ↔
    ∀ (χ : PontryaginDual C𝔽) (s : ℂ), 0 < s.re → s.re < 1 →
        0 < meromorphicOrderAt (continuedCompletedHeckeL χ) s → s.re = 1 / 2 := by
  classical
  have hpos (χ : PontryaginDual C𝔽) (s : ℂ) :
      0 < ord(χ, s) ↔ 0 < meromorphicOrderAt (continuedCompletedHeckeL χ) s := by
    have hL := (continuedCompletedHeckeL_spec χ).1.meromorphicOn
    have h₂ : meromorphicOrderAt (continuedCompletedHeckeL χ) 2 ≠ ⊤ := by
      intro ht
      have hp : 0 < meromorphicOrderAt (continuedCompletedHeckeL χ) 2 := by rw [ht]; simp
      have h : (2 : ℂ).re < 1 := completedHeckeL_continuation_zeros χ _
        (continuedCompletedHeckeL_spec χ).1 (continuedCompletedHeckeL_spec χ).2 (by norm_num) hp
      norm_num at h
    have hfin := hL.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
      (mem_univ (2 : ℂ)) (mem_univ s) h₂
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hfin
    rw [MeromorphicOn.divisor_apply hL (mem_univ _), ← hn, WithTop.untop₀_coe]
    exact_mod_cast (Iff.rfl : (0 < n) ↔ 0 < n)
  constructor
  · intro h
    apply (introTrace_all_continuations_iff_critical_line τ hτ).mp
    intro χ hχ a ha
    apply (introTrace_normalized_continuation_iff_no_right_zeros τ hτ χ hχ a ha.le).mpr
    intro s hs hp
    have he := (hasSum_exteriorZeros_iff_isEmpty τ hτ a).mp (h a ha)
    exact he.false ⟨⟨⟨χ, hχ⟩, s⟩, (hpos χ s).mpr hp,
      (show a ≤ s.re - 1 / 2 by linarith).trans (le_abs_self _)⟩
  · intro h α hα
    apply (hasSum_exteriorZeros_iff_isEmpty τ hτ α).mpr
    constructor
    rintro ⟨⟨χ, s⟩, hp, hdist⟩
    have hw := heckePositiveDivisor_open_strip χ.val hp
    have hline := h χ.val s hw.1 hw.2 ((hpos χ.val s).mp hp)
    change α ≤ |s.re - 1 / 2| at hdist
    rw [hline, sub_self, abs_zero] at hdist
    exact hα.not_ge hdist


/-- Paper: Theorem 12.5.1.1, pp. 519–520, and §1.4.5, pp. 29–30. Over a
number field with admissible smoothing neighborhoods, the projected
geometric diagonals approach their wide value from the left at
every positive half-width for all tests vanishing on the norm-one classes
if and only if all unitary Hecke zeros in the critical strip lie on its
center line.
Deviation: This isolates a one-sided scalar geometric limit. Neither the
narrow explicit formula nor a zero-density bound is assumed in the proof
of the equivalence. -/
theorem all_leftLimits_centeredStripDiagonalIntegral_iff_heckeCriticalLine
    (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F)) {s : ℝ} (hs : 3 ≤ s)
    (U : Ioi (0:ℝ) → ℕ → Set C𝔽) (hU : ∀ t, IsDPrimeSequence μ𝔽 (U t))
    (hM : ∀ t n, MeasurableSet (U t n)) :
    (∀ (φ : BruhatCompactSupport C𝔽), (∀ g : C₁, φ.val g = 0) →
      ∀ r : Ioi (0:ℝ),
        Tendsto (fun t : Ioi (0:ℝ) ↦ centeredStripGeometricDiagonalIntegral φ t.property hs (U t))
          (𝓝[<] r) (𝓝 (centeredStripGeometricDiagonalIntegral φ (half_pos zero_lt_one) hs
            (U ⟨1/2, half_pos zero_lt_one⟩)))) ↔
      ∀ (χ : PontryaginDual C𝔽) (z : ℂ), 0 < z.re → z.re < 1 →
        0 < meromorphicOrderAt (continuedCompletedHeckeL χ) z → z.re = 1 / 2 := by
  rw [← all_exterior_iff_criticalLine τ hτ]
  constructor
  · intro h α hα φ hφ
    exact (exteriorZeros_iff_leftLimit_centeredStripDiagonalIntegral_eq_wide τ hτ φ hφ hs U hU hM
      ⟨α,hα⟩).mpr (h φ hφ ⟨α,hα⟩)
  · intro h φ hφ r
    exact (exteriorZeros_iff_leftLimit_centeredStripDiagonalIntegral_eq_wide τ hτ φ hφ hs U hU hM
      r).mp (h r.val r.property φ hφ)

end RiemannMasullo.StripNuclearity
