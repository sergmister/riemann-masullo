module

public import RiemannMasullo.Ch12_TraceGeometric.Sec5
public import RiemannMasullo.Research.StripNuclearity.HeckePairedDivisor

/-!
# The smoothened diagonal and the open-strip zero sum

Page 519 specifies the interior of the relative strip. Equation (12.5.1.4) on p. 520
evaluates the diagonal for a closed symmetric interval. With zero-free edges, the
closed-strip theorem yields the printed open-strip sum with full multiplicities.
At half-width at least one-half the sum includes every positive completed divisor.
-/

@[expose] public noncomputable section

open MeasureTheory NumberField Set
open scoped NumberField.AdeleRing NNReal

namespace RiemannMasullo.StripNuclearity

set_option quotPrecheck false

variable {F : Type*} [Field F] [NumberField F]

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "X" => PontryaginDual C₁
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" => (⟨ideleClassNorm F,(isProperMap_ideleClassNorm F).continuous⟩ : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "hm𝔽" => (⟨isProperMap_ideleClassNorm F,ideleClassNorm_ne_one (F := F)⟩ : IsModulation m𝔽)
local notation "D(" χ ")" => MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ
local notation "M(" φ ", " χ ", " w ")" =>
  modulatedFourierMellin m𝔽 univ hm𝔽 μ𝔽 (φ : BruhatCompactSupport C𝔽).val (ideleClassNormTwist (F := F) χ w)
local notation "point(" b ", " t ")" => ((b : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I
variable {hone_lt_three : (1 : ℝ) < 3}
local notation "hs₁(" hs ")" => (lt_of_lt_of_le hone_lt_three hs)
local notation "hs₀(" hs ")" => (le_of_lt (zero_lt_one.trans hs₁(hs)))
local notation "widePos(" h ")" => (lt_of_lt_of_le (half_pos (zero_lt_one : (0 : ℝ) < 1)) h)
local notation "rangeProof(" hα ")" => (neg_nonpos.mpr hα |>.trans hα)
local notation "tensorExists(" hα ", " hs ", " φ ")" =>
  (∃ K, sobolevProjectiveKernelOperator (F := F) hα hs₀(hs) K =
    (hardySobolevTestAction μ𝔽 m𝔽 _ _ _ (rangeProof(hα)) hs₀(hs) φ).comp
      (spectralProjection (F := F) (1 / 2) hα hs₀(hs)))
local notation "diagonal(" hα ", " hs ", " φ ", " hK ", " U ")" =>
  (fun x : C𝔽 ↦ dSequenceKernelSmoothening μ𝔽 U
    (globalStripGeometricKernel (F := F) (1 / 2) hα hs₁(hs) φ hK) (x,x))
local notation "closedPoints(" χ ", " α ")" =>
  {z : X × ℝ × ℝ // z.2.1 ∈ Icc (-α) α ∧
    0 < meromorphicOrderAt (continuedCompletedHeckeL (χ z.1)) (point(1/2+z.2.1,z.2.2))}
local notation "closedTerm(" φ ", " χ ", " α ", " s ", " z ")" =>
  ((spectralStripMultiplicity α s (z).val.2.1
    (meromorphicOrderAt (continuedCompletedHeckeL (χ (z).val.1)) (point(1/2+(z).val.2.1,(z).val.2.2))).untop₀.toNat : ℕ) : ℂ) *
    M(φ, χ (z).val.1, point((z).val.2.1,(z).val.2.2))
local notation "fullTerm(" φ ", " χ ", " z ")" =>
  ((D(χ (z).val.1) (z).val.2 : ℤ) : ℂ) * M(φ, χ (z).val.1, (z).val.2-1/2)
local notation "sumStatement(" S ", " χ ", " φ ", " g ")" =>
  (let term (z : S) := fullTerm(φ, χ, z)
   Integrable g μ𝔽 ∧ Summable (fun z ↦ ‖term z‖) ∧ HasSum term (-(∫ x, g x ∂μ𝔽)))

private theorem divisor_pos_iff_order_pos (η : PontryaginDual C𝔽) (w : ℂ) :
    0 < D(η) w ↔ 0 < meromorphicOrderAt (continuedCompletedHeckeL η) w := by
  obtain ⟨hL,heq⟩ := continuedCompletedHeckeL_spec η
  have ht : meromorphicOrderAt (continuedCompletedHeckeL η) 2 ≠ ⊤ := by
    intro h
    have hp : 0 < meromorphicOrderAt (continuedCompletedHeckeL η) 2 := by
      rw [h]; exact WithTop.coe_lt_top (0 : ℤ)
    have hbad := completedHeckeL_continuation_zeros η _ hL heq (by norm_num : 0 < (2 : ℂ).re) hp
    norm_num at hbad
  obtain ⟨n,hn⟩ := WithTop.ne_top_iff_exists.mp
    (hL.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ _) (mem_univ w) ht)
  rw [MeromorphicOn.divisor_apply hL.meromorphicOn (mem_univ w),← hn,WithTop.untop₀_coe]
  exact WithTop.coe_lt_coe.symm

private theorem centered_point (w : ℂ) : point(1/2+(w.re-1/2),w.im) = w := by
  apply Complex.ext <;> simp

private theorem shifted_point (w : ℂ) : point(w.re-1/2,w.im) = w-1/2 := by
  apply Complex.ext <;> simp

/-- Index the closed-strip jet points by their angular character and actual complex
Hecke zero. Its ordinate is unchanged and its real coordinate is centered at one-half. -/
def heckeZeroCoordinatesEquiv (χ : X → PontryaginDual C𝔽) {α : ℝ} (S : Set (X × ℂ))
    (hS : ∀ z, z ∈ S ↔ 0 < D(χ z.1) z.2 ∧ |z.2.re-1/2| ≤ α) :
    S ≃ closedPoints(χ, α) := by
  let coordinates : X × ℂ ≃ X × ℝ × ℝ :=
    { toFun := fun z ↦ (z.1,z.2.re-1/2,z.2.im)
      invFun := fun z ↦ (z.1,⟨1/2+z.2.1,z.2.2⟩)
      left_inv := fun _ ↦ Prod.ext rfl (Complex.ext (by dsimp; ring) rfl)
      right_inv := fun _ ↦ Prod.ext rfl (Prod.ext (by dsimp; ring) rfl) }
  exact coordinates.subtypeEquiv fun z ↦ by
    change z ∈ S ↔ z.2.re-1/2 ∈ Icc (-α) α ∧
      0 < meromorphicOrderAt (continuedCompletedHeckeL (χ z.1)) (point(1/2+(z.2.re-1/2),z.2.im))
    rw [centered_point,← divisor_pos_iff_order_pos,hS,abs_le]
    exact and_comm

/-- For an interior zero, the trace summand in logarithmic coordinates equals its
full divisor multiplicity times the Mellin transform at the positive twist `ρ−1/2`. -/
theorem heckeZeroCoordinatesEquiv_mellinTerm (φ : BruhatCompactSupport C𝔽) (χ : X → PontryaginDual C𝔽)
    {α s : ℝ} (S : Set (X × ℂ)) (hS : ∀ z, z ∈ S ↔ 0 < D(χ z.1) z.2 ∧ |z.2.re-1/2| ≤ α)
    (z : S) (hz : |z.val.2.re-1/2| < α) :
    let j := heckeZeroCoordinatesEquiv χ S hS z
    closedTerm(φ, χ, α, s, j) = fullTerm(φ, χ, z) := by
  intro j
  have hd := MeromorphicOn.divisor_apply (continuedCompletedHeckeL_spec (χ z.val.1)).1.meromorphicOn (mem_univ z.val.2)
  have hc : (((D(χ z.val.1) z.val.2).toNat : ℕ) : ℂ) = (D(χ z.val.1) z.val.2 : ℂ) := by
    exact_mod_cast Int.toNat_of_nonneg ((hS z.val).mp z.property).1.le
  change ((spectralStripMultiplicity α s (z.val.2.re-1/2)
    (meromorphicOrderAt (continuedCompletedHeckeL (χ z.val.1)) (point(1/2+(z.val.2.re-1/2),z.val.2.im))).untop₀.toNat : ℕ) : ℂ) *
      M(φ, χ z.val.1, point(z.val.2.re-1/2,z.val.2.im)) = _
  rw [centered_point,shifted_point,spectralStripMultiplicity_interior (abs_lt.mp hz),← hd,hc]

/-- Reindex an absolutely convergent jet trace whenever all its zeros lie in the
interior. The sum value is arbitrary, so this also applies directly to a quotient trace. -/
theorem hasSum_heckeZeros_of_closedStripJetSum (φ : BruhatCompactSupport C𝔽) (χ : X → PontryaginDual C𝔽)
    {α s : ℝ} (S : Set (X × ℂ)) (hS : ∀ z, z ∈ S ↔ 0 < D(χ z.1) z.2 ∧ |z.2.re-1/2| ≤ α)
    (hint : ∀ z : S, |z.val.2.re-1/2| < α) {r : ℂ}
    (habs : Summable (fun j : closedPoints(χ, α) ↦ ‖closedTerm(φ, χ, α, s, j)‖))
    (hsum : HasSum (fun j : closedPoints(χ, α) ↦ closedTerm(φ, χ, α, s, j)) r) :
    Summable (fun z : S ↦ ‖fullTerm(φ, χ, z)‖) ∧ HasSum (fun z : S ↦ fullTerm(φ, χ, z)) r := by
  let e := heckeZeroCoordinatesEquiv χ S hS
  have ht (z : S) := heckeZeroCoordinatesEquiv_mellinTerm (s := s) φ χ S hS z (hint z)
  exact ⟨(e.summable_iff.mpr habs).congr (fun z ↦ congrArg norm (ht z)),
    (e.hasSum_iff.mpr hsum).congr_fun (fun z ↦ (ht z).symm)⟩

private theorem hasSum_diagonal_of_zeroSet (φ : BruhatCompactSupport C𝔽)
    (hφ : ∀ g : C₁, φ.val g = 0) (χ : X → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    {α s : ℝ} (hα : 0 < α) (hs : 3 ≤ s) (hK : tensorExists(hα.le, hs, φ))
    (U : ℕ → Set C𝔽) (hU : IsDPrimeSequence μ𝔽 U) (hm : ∀ n, MeasurableSet (U n))
    (S : Set (X × ℂ))
    (hS : ∀ z, z ∈ S ↔ 0 < D(χ z.1) z.2 ∧ |z.2.re-1/2| ≤ α)
    (hint : ∀ z : S, |z.val.2.re-1/2| < α) :
    sumStatement(S, χ, φ, diagonal(hα.le, hs, φ, hK, U)) := by
  intro term
  let g := diagonal(hα.le, hs, φ, hK, U)
  let v (j : closedPoints(χ, α)) := closedTerm(φ, χ, α, s, j)
  have h : Integrable g μ𝔽 ∧ Summable (fun j ↦ ‖v j‖) ∧ HasSum v (-(∫ x, g x ∂μ𝔽)) :=
    hasSum_stripZeros_neg_integral_smoothenedDiagonal (F := F) (hone_lt_three := hone_lt_three)
      φ hφ χ hχ hα hs hK U hU hm
  exact ⟨h.1,hasSum_heckeZeros_of_closedStripJetSum (α := α) (s := s) (r := -(∫ x, g x ∂μ𝔽))
    φ χ S hS hint h.2.1 h.2.2⟩

/-- Paper: (12.5.1.4), p. 520. If the two edges have no positive Hecke divisors,
the negative Haar integral of the smoothened geometric diagonal is the absolutely
convergent open-strip sum of the test's Mellin values, with full zero multiplicity.
The Mellin twist at a zero `ρ` is `ρ − 1/2` as on p. 519. -/
theorem hasSum_openStripZeros_neg_integral_smoothenedDiagonal (φ : BruhatCompactSupport C𝔽)
    (hφ : ∀ g : C₁, φ.val g = 0) (χ : X → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    {α s : ℝ} (hα : 0 < α) (hs : 3 ≤ s) (hK : tensorExists(hα.le, hs, φ))
    (U : ℕ → Set C𝔽) (hU : IsDPrimeSequence μ𝔽 U) (hm : ∀ n, MeasurableSet (U n))
    (hedge : ∀ (ω : X) (ρ : ℂ), 0 < D(χ ω) ρ → |ρ.re-1/2| ≠ α) :
    let S := {z : X × ℂ | 0 < D(χ z.1) z.2 ∧ |z.2.re-1/2| < α}
    sumStatement(S, χ, φ, diagonal(hα.le, hs, φ, hK, U)) := by
  intro S
  have hS (z : X × ℂ) : z ∈ S ↔ 0 < D(χ z.1) z.2 ∧ |z.2.re-1/2| ≤ α :=
    and_congr_right fun hz ↦ ⟨LT.lt.le,fun h ↦ lt_of_le_of_ne h (hedge _ _ hz)⟩
  exact hasSum_diagonal_of_zeroSet (F := F) (hone_lt_three := hone_lt_three)
    φ hφ χ hχ hα hs hK U hU hm S hS (fun z ↦ z.property.2)

/-- Paper: (12.5.1.4), p. 520. At half-width at least one-half, the same diagonal
equals the negative sum over every positive divisor of every completed Hecke function.
The functional equation and the nonvanishing on `Re ρ ≥ 1` place all these zeros
strictly inside the critical strip. -/
theorem hasSum_allHeckeZeros_neg_integral_smoothenedDiagonal (φ : BruhatCompactSupport C𝔽)
    (hφ : ∀ g : C₁, φ.val g = 0) (χ : X → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    {α s : ℝ} (hwide : 1/2 ≤ α) (hs : 3 ≤ s) :
    let hα : 0 < α := widePos(hwide)
    ∀ (hK : tensorExists(hα.le, hs, φ)) (U : ℕ → Set C𝔽), IsDPrimeSequence μ𝔽 U →
      (∀ n, MeasurableSet (U n)) →
      let S := {z : X × ℂ | 0 < D(χ z.1) z.2}
      sumStatement(S, χ, φ, diagonal(hα.le, hs, φ, hK, U)) := by
  intro hα hK U hU hm S
  have hi (z : S) : |z.val.2.re-1/2| < α := by
    have h := heckePositiveDivisor_open_strip (χ z.val.1) z.property
    exact (abs_lt.mpr ⟨by linarith [h.1],by linarith [h.2]⟩ : |z.val.2.re-1/2| < 1/2).trans_le hwide
  have hS (z : X × ℂ) : z ∈ S ↔ 0 < D(χ z.1) z.2 ∧ |z.2.re-1/2| ≤ α :=
    ⟨fun hz ↦ ⟨hz,(hi ⟨z,hz⟩).le⟩,And.left⟩
  exact hasSum_diagonal_of_zeroSet (F := F) (hone_lt_three := hone_lt_three)
    φ hφ χ hχ hα hs hK U hU hm S hS hi

end RiemannMasullo.StripNuclearity
