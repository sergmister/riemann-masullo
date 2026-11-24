module

public import RiemannMasullo.Research.StripNuclearity.WindowComparison
import Mathlib.Analysis.Normed.Group.Tannery

/-! # The global projected integral as the strip approaches full width

The actual projected diagonals converge from inside the wide strip. The
Sobolev order can vary because the boundary multiplicity never exceeds the
order of the zero.
-/

@[expose] public noncomputable section

open Filter MeasureTheory NumberField Set
open scoped NumberField.AdeleRing NNReal Topology

namespace RiemannMasullo.StripNuclearity

private theorem missing_tsum_tendsto_zero {ι T : Type*} {l : Filter T} {r : ℝ}
    (β : ι → ℝ) (hβ : ∀ i, |β i| < r) (m : ι → ℕ) (v : ι → ℂ)
    (hV : Summable (fun i ↦ ‖(m i : ℂ) * v i‖))
    (α s : T → ℝ) (hα : Tendsto α l (𝓝 r)) :
    Tendsto (fun t ↦ ∑' i, ((m i - spectralStripMultiplicity (α t) (s t) (β i) (m i) : ℕ) : ℂ) * v i)
      l (𝓝 0) := by
  let term (t : T) (i : ι) := ((m i - spectralStripMultiplicity (α t) (s t) (β i) (m i) : ℕ) : ℂ) * v i
  have hpt (i : ι) : Tendsto (fun t ↦ term t i) l (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hα.eventually (Ioi_mem_nhds (hβ i))] with t ht
    simp only [term, spectralStripMultiplicity_interior (abs_lt.mp (show |β i| < α t from ht)),
      Nat.sub_self, Nat.cast_zero, zero_mul]
  have hb (t : T) (i : ι) : ‖term t i‖ ≤ ‖(m i : ℂ) * v i‖ := by
    simp only [term, norm_mul, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le _ _) (norm_nonneg _)
  simpa only [tsum_zero] using (tendsto_tsum_of_dominated_convergence hV hpt (.of_forall hb))

private theorem tendsto_of_difference {T : Type*} {l : Filter T} {d : T → ℂ} {c : ℂ}
    (h : Tendsto (fun t ↦ d t - c) l (𝓝 0)) : Tendsto d l (𝓝 c) := by
  simpa only [sub_add_cancel, zero_add] using h.add_const c

variable {F : Type*} [Field F] [NumberField F]

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

set_option quotPrecheck false
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "μ" => ideleClassTamagawaMeasure F
local notation "m𝔽" => (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "hm" => (⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ : IsModulation m𝔽)
local notation "divisor(" χ ")" => MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ
/-- Paper: Equation (12.5.1.4), p. 520. The global smoothed diagonal integral
at center one half, using the projective kernel of the projected test action. -/
def centeredStripGeometricDiagonalIntegral (φ : BruhatCompactSupport C𝔽)
    {α s : ℝ} (hα : 0 < α) (hs : 3 ≤ s) (U : ℕ → Set C𝔽) : ℂ :=
  ∫ x : C𝔽, dSequenceKernelSmoothening μ U
    (globalStripGeometricKernel (F := F) (1/2) hα.le
      (lt_of_lt_of_le (b := (3 : ℝ)) Nat.one_lt_ofNat hs) φ
      (exists_numberField_projectiveKernel_comp_spectralProjection (F := F) (le_of_lt hα)
        (lt_of_lt_of_le (b := (3 : ℝ)) Nat.one_lt_ofNat hs) φ)) (x,x) ∂μ
local notation "diagonal(" φ "," hα "," hs "," U ")" => centeredStripGeometricDiagonalIntegral φ hα hs U

/-- Paper: Equation (12.5.1.4), p. 520. As the positive half-width tends to one
half, the actual global smoothed diagonal integral tends to its full-width
value for every number field. The Sobolev orders may vary above three and
each width may use its own regular smoothing sequence. The test vanishes on
the norm-one classes.
Deviation: This is convergence towards full width, including from smaller
widths. Equality at a fixed smaller width is the additional conclusion
sought in §12.3. -/
theorem tendsto_centeredStripDiagonalIntegral_at_half (φ : BruhatCompactSupport C𝔽)
    (hφ : ∀ g : C₁, φ.val g = 0) {T : Type*} {l : Filter T}
    (α s : T → ℝ) (hα : ∀ t, 0 < α t) (hs : ∀ t, 3 ≤ s t) (hlim : Tendsto α l (𝓝 (1/2)))
    {σ : ℝ} (hσ : 3 ≤ σ) (U : T → ℕ → Set C𝔽) (V : ℕ → Set C𝔽)
    (hU : ∀ t, IsDPrimeSequence μ (U t)) (hmU : ∀ t n, MeasurableSet (U t n))
    (hV : IsDPrimeSequence μ V) (hmV : ∀ n, MeasurableSet (V n)) :
    Tendsto (fun t ↦ diagonal(φ,hα t,hs t,U t)) l (𝓝 diagonal(φ,half_pos (zero_lt_one : (0:ℝ)<1),hσ,V)) := by
  let full := diagonal(φ,half_pos (zero_lt_one : (0:ℝ)<1),hσ,V)
  let narrow (t : T) := diagonal(φ,hα t,hs t,U t)
  change Tendsto narrow l (𝓝 full)
  let chars := exists_spectralBasepointChoice_radially_trivial F
  let χ := chars.choose
  let Z := {z : PontryaginDual C₁ × ℂ // 0 < divisor(χ z.1) z.2}
  let β (z : Z) := z.val.2.re - 1/2
  let m (z : Z) := (divisor(χ z.val.1) z.val.2).toNat
  let v (z : Z) := modulatedFourierMellin m𝔽 univ hm μ φ.val
    (ideleClassNormTwist (χ z.val.1) (z.val.2 - 1/2))
  have hi (z : Z) : |β z| < 1/2 := by
    obtain ⟨h₀,h₁⟩ := heckePositiveDivisor_open_strip (χ z.val.1) z.property
    exact abs_lt.mpr ⟨by dsimp [β]; linarith, by dsimp [β]; linarith⟩
  have hf := (hasSum_numberField_allHeckeZeros_neg_integral_smoothenedDiagonal (F:=F)
    φ hφ χ chars.choose_spec.1 (α:=1/2) le_rfl hσ V hV hmV).2.1
  have hw : Summable (fun z : Z ↦ ‖(m z : ℂ) * v z‖) := by
    apply hf.congr
    intro z
    have e : (m z : ℂ) = (divisor(χ z.val.1) z.val.2 : ℂ) := by
      exact_mod_cast Int.toNat_of_nonneg z.property.le
    rw [e]
  have ht := missing_tsum_tendsto_zero β hi m v hw α s hlim
  have hd (t : T) : (∑' z : Z, ((m z - spectralStripMultiplicity (α t) (s t) (β z) (m z) : ℕ) : ℂ) * v z) =
      narrow t - full := (hasSum_missingHeckeJets_centeredStripDiagonalIntegral_sub (F:=F)
    φ hφ χ chars.choose_spec.1 (hα t) (hs t) (β:=1/2) le_rfl hσ (U t) V (hU t) (hmU t) hV hmV).2.tsum_eq
  exact tendsto_of_difference (d:=narrow) (c:=full) (ht.congr hd)

end RiemannMasullo.StripNuclearity
