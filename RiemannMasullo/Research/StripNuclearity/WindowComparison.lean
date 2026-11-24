module

public import RiemannMasullo.Research.StripNuclearity.NumberFieldDiagonal

/-!
# The change of the geometric diagonal with the strip width

The local expression on p. 520 does not depend on the half-width. Comparing the
actual diagonal at two widths isolates the spectral correction that a local
comparison must account for, including any missing jets at the boundary.
-/

@[expose] public noncomputable section

open Function MeasureTheory NumberField Set
open scoped NumberField.AdeleRing NNReal

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
local notation "M(" φ ", " χ ", " z ")" =>
  modulatedFourierMellin m𝔽 univ hm𝔽 μ𝔽 (φ : BruhatCompactSupport C𝔽).val
    (ideleClassNormTwist (F := F) (χ (z).val.1) ((z).val.2 - 1/2))
local notation "mult(" χ ", " z ")" => (D(χ (z).val.1) (z).val.2).toNat
local notation "kept(" χ ", " α ", " s ", " z ")" =>
  spectralStripMultiplicity α s ((z).val.2.re - 1/2) mult(χ, z)

local notation "point(" b ", " t ")" => ((b : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I
local notation "closedPoints(" χ ", " α ")" =>
  {z : X × ℝ × ℝ // z.2.1 ∈ Icc (-α) α ∧
    0 < meromorphicOrderAt (continuedCompletedHeckeL (χ z.1)) (point(1/2+z.2.1,z.2.2))}
local notation "closedTerm(" φ ", " χ ", " α ", " s ", " j ")" =>
  ((spectralStripMultiplicity α s (j).val.2.1
    (meromorphicOrderAt (continuedCompletedHeckeL (χ (j).val.1))
      (point(1/2+(j).val.2.1,(j).val.2.2))).untop₀.toNat : ℕ) : ℂ) *
    modulatedFourierMellin m𝔽 univ hm𝔽 μ𝔽 (φ : BruhatCompactSupport C𝔽).val
      (ideleClassNormTwist (χ (j).val.1) (point((j).val.2.1,(j).val.2.2)))

private theorem kept_le (α s b : ℝ) (n : ℕ) : spectralStripMultiplicity α s b n ≤ n := by
  unfold spectralStripMultiplicity spectralBoundaryMultiplicity
  split_ifs <;> first | exact le_rfl | exact min_le_left _ _ | exact Nat.zero_le _

private theorem kept_eq_zero_outside {α b : ℝ} (hα : 0 ≤ α) (hb : ¬ |b| ≤ α) (s : ℝ) (n : ℕ) :
    spectralStripMultiplicity α s b n = 0 := by
  unfold spectralStripMultiplicity
  have hi : ¬ (-α < b ∧ b < α) := fun h ↦ hb (abs_le.mpr ⟨h.1.le, h.2.le⟩)
  have he : ¬ (b = -α ∨ b = α) := by
    intro h
    apply hb
    rcases h with h | h <;> rw [h] <;> simp only [abs_neg, abs_of_nonneg hα, le_refl]
  simp [hi, he]

private theorem centered_point (w : ℂ) :
    ((1/2 + (w.re - 1/2) : ℝ) : ℂ) + (w.im : ℂ) * Complex.I = w := by
  apply Complex.ext <;> simp

private theorem shifted_point (w : ℂ) :
    ((w.re - 1/2 : ℝ) : ℂ) + (w.im : ℂ) * Complex.I = w - 1/2 := by
  apply Complex.ext <;> simp

/-- Reindex the closed jet sum on all completed divisors by extending its multiplicity by zero. -/
theorem keptHeckeZeroSum_of_closedJetSum (φ : BruhatCompactSupport C𝔽)
    (χ : X → PontryaginDual C𝔽) {α s : ℝ} (hα : 0 < α) {r : ℂ}
    (h : HasSum (fun j : closedPoints(χ, α) ↦ closedTerm(φ, χ, α, s, j)) r) :
    HasSum (fun z : zeros(χ) ↦ (kept(χ, α, s, z) : ℂ) * M(φ, χ, z)) r := by
  let S := {z : X × ℂ | 0 < D(χ z.1) z.2 ∧ |z.2.re - 1/2| ≤ α}
  let C := {z : zeros(χ) | |z.val.2.re - 1/2| ≤ α}
  let e : C ≃ S :=
    ⟨fun z ↦ ⟨z.val.val, z.val.property, z.property⟩,
     fun z ↦ ⟨⟨z.val, z.property.1⟩, z.property.2⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩
  let j := heckeZeroCoordinatesEquiv χ S (fun _ ↦ Iff.rfl)
  let f (z : zeros(χ)) := (kept(χ, α, s, z) : ℂ) * M(φ, χ, z)
  have hsupport : Function.support f ⊆ C := by
    intro z hz
    by_contra hout
    apply hz
    change (kept(χ, α, s, z) : ℂ) * M(φ, χ, z) = 0
    rw [kept_eq_zero_outside hα.le (show ¬ |z.val.2.re - 1/2| ≤ α from hout), Nat.cast_zero, zero_mul]
  apply (hasSum_subtype_iff_of_support_subset hsupport).mp
  apply ((e.trans j).hasSum_iff.mpr h).congr_fun
  intro z
  have hd := MeromorphicOn.divisor_apply (continuedCompletedHeckeL_spec (χ z.val.val.1)).1.meromorphicOn
    (mem_univ z.val.val.2)
  change _ = ((spectralStripMultiplicity α s (z.val.val.2.re - 1/2)
    (meromorphicOrderAt (continuedCompletedHeckeL (χ z.val.val.1))
      (((1/2+(z.val.val.2.re-1/2) : ℝ) : ℂ) + (z.val.val.2.im : ℂ)*Complex.I)).untop₀.toNat : ℕ) : ℂ) *
        modulatedFourierMellin m𝔽 univ hm𝔽 μ𝔽 φ.val (ideleClassNormTwist (χ z.val.val.1)
          (((z.val.val.2.re-1/2 : ℝ) : ℂ) + (z.val.val.2.im : ℂ)*Complex.I))
  rw [centered_point, shifted_point, ← hd]
  rfl

local notation "thin(" φ ", " hφ ", " χ ", " hχ ", " hα ", " hs ", " U ", " hU ", " hm ")" =>
  (hasSum_numberField_stripZeros_neg_integral_smoothenedDiagonal (F := F) φ hφ χ hχ hα hs U hU hm).2.2
local notation "keptSum(" φ ", " hφ ", " χ ", " hχ ", " hα ", " hs ", " U ", " hU ", " hm ")" =>
  keptHeckeZeroSum_of_closedJetSum φ χ hα (thin(φ, hφ, χ, hχ, hα, hs, U, hU, hm))

/-- Paper: Equations (10.2.2.5)–(10.2.2.6), p. 446, and (12.5.1.4), p. 520.
The negative integral of the actual smoothened diagonal is the Mellin sum on
all completed Hecke zeros with the strip multiplicity extended by zero. -/
theorem hasSum_keptHeckeZeros_neg_centeredStripDiagonalIntegral
    (φ : BruhatCompactSupport C𝔽) (hφ : ∀ g : C₁, φ.val g = 0)
    (χ : X → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    {α s : ℝ} (hα : 0 < α) (hs : 3 ≤ s) (U : ℕ → Set C𝔽)
    (hU : IsDPrimeSequence μ𝔽 U) (hm : ∀ n, MeasurableSet (U n)) :
    type_of% keptSum(φ, hφ, χ, hχ, hα, hs, U, hU, hm) :=
  keptSum(φ, hφ, χ, hχ, hα, hs, U, hU, hm)

/-- Subtract two absolutely convergent trace expansions on their common zero index. -/
theorem missingHeckeJetSum_of_two_traces (φ : BruhatCompactSupport C𝔽)
    (χ : X → PontryaginDual C𝔽) (α s : ℝ) {narrow wide : ℂ}
    (ha : HasSum (fun z : zeros(χ) ↦ (kept(χ, α, s, z) : ℂ) * M(φ, χ, z)) (-narrow))
    (hf : Summable (fun z : zeros(χ) ↦ ‖((D(χ z.val.1) z.val.2 : ℤ) : ℂ) * M(φ, χ, z)‖) ∧
      HasSum (fun z : zeros(χ) ↦ ((D(χ z.val.1) z.val.2 : ℤ) : ℂ) * M(φ, χ, z)) (-wide)) :
    let defect (z : zeros(χ)) := ((mult(χ, z) - kept(χ, α, s, z) : ℕ) : ℂ) * M(φ, χ, z)
    Summable (fun z ↦ ‖defect z‖) ∧ HasSum defect (narrow - wide) := by
  intro defect
  let full (z : zeros(χ)) := ((D(χ z.val.1) z.val.2 : ℤ) : ℂ) * M(φ, χ, z)
  let admitted (z : zeros(χ)) := (kept(χ, α, s, z) : ℂ) * M(φ, χ, z)
  have hfull (z : zeros(χ)) : (mult(χ, z) : ℂ) = (D(χ z.val.1) z.val.2 : ℂ) := by
    exact_mod_cast Int.toNat_of_nonneg z.property.le
  have hsub (z : zeros(χ)) : defect z = full z - admitted z := by
    dsimp only [defect, full, admitted]
    rw [Nat.cast_sub (kept_le ..), sub_mul, hfull]
  constructor
  · refine (show Summable (fun z ↦ ‖full z‖) from hf.1).of_nonneg_of_le
      (fun _ ↦ norm_nonneg _) (fun z ↦ ?_)
    dsimp only [defect, full]
    rw [← hfull, norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le _ _) (norm_nonneg _)
  · have h : HasSum (fun z ↦ full z - admitted z) (-wide - -narrow) := hf.2.sub ha
    simpa only [sub_neg_eq_add, neg_add_eq_sub] using h.congr_fun hsub

local notation "wideSum(" φ ", " hφ ", " χ ", " hχ ", " hβ ", " ht ", " V ", " hV ", " hm ")" =>
  (hasSum_numberField_allHeckeZeros_neg_integral_smoothenedDiagonal (F := F) φ hφ χ hχ hβ ht V hV hm).2
local notation "difference(" φ ", " hφ ", " χ ", " hχ ", " α ", " s ", " hα ", " hs ", " hβ ", " ht ", "
    U ", " V ", " hU ", " hmU ", " hV ", " hmV ")" =>
  missingHeckeJetSum_of_two_traces φ χ α s (keptSum(φ, hφ, χ, hχ, hα, hs, U, hU, hmU))
    (wideSum(φ, hφ, χ, hχ, hβ, ht, V, hV, hmV))

/-- Paper: Section 12.3, p. 514, and (12.5.1.4), p. 520.
Deviation: The difference of the actual geometric diagonal and a wide-strip
diagonal is the absolutely convergent Mellin sum over missing multiplicities.
A strictly exterior zero contributes its full order. At an edge only the
unrepresented jet orders contribute. The two smoothing sequences and
Sobolev orders can be chosen independently. -/
theorem hasSum_missingHeckeJets_centeredStripDiagonalIntegral_sub
    (φ : BruhatCompactSupport C𝔽) (hφ : ∀ g : C₁, φ.val g = 0)
    (χ : X → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    {α s β t : ℝ} (hα : 0 < α) (hs : 3 ≤ s) (hβ : 1/2 ≤ β) (ht : 3 ≤ t)
    (U V : ℕ → Set C𝔽) (hU : IsDPrimeSequence μ𝔽 U) (hmU : ∀ n, MeasurableSet (U n))
    (hV : IsDPrimeSequence μ𝔽 V) (hmV : ∀ n, MeasurableSet (V n)) :
    type_of% difference(φ, hφ, χ, hχ, α, s, hα, hs, hβ, ht, U, V, hU, hmU, hV, hmV) :=
  difference(φ, hφ, χ, hχ, α, s, hα, hs, hβ, ht, U, V, hU, hmU, hV, hmV)

end RiemannMasullo.StripNuclearity
