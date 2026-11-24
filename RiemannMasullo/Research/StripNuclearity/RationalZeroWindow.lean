module

public import RiemannMasullo.Research.StripNuclearity.RationalWindow
import all RiemannMasullo.Research.StripNuclearity.RationalDiagonalDefect
import all RiemannMasullo.Ch12_TraceGeometric.Sec5

/-! # The zero correction on the rational radial component

On radial tests the complete missing-jet correction is supported on the
ordinary nontrivial zeros of the Riemann zeta function.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped ContDiff NNReal NumberField.AdeleRing Topology
open RiemannMasullo.External.Grh

namespace RiemannMasullo.StripNuclearity

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

set_option quotPrecheck false
local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "C₁" => (ideleClassNorm ℚ).ker
local notation "X" => PontryaginDual C₁
local notation "Uℚ" => PontryaginDual Cℚ
local notation "μℚ" => ideleClassTamagawaMeasure ℚ
local notation "Vℚ" => (((normOneIdeleClassTamagawaMeasure ℚ) univ).toReal : ℂ)
local notation "mℚ" => (⟨ideleClassNorm ℚ, (isProperMap_ideleClassNorm ℚ).continuous⟩ : Cℚ →ₜ* ℝ≥0ˣ)
local notation "hmℚ" => (⟨isProperMap_ideleClassNorm ℚ, ideleClassNorm_ne_one (F := ℚ)⟩ : IsModulation mℚ)
local notation "M(" φ ", " ψ ", " w ")" =>
  modulatedFourierMellin mℚ univ hmℚ μℚ (φ : BruhatCompactSupport Cℚ).val (ideleClassNormTwist (F := ℚ) ψ w)
local notation "D(" ψ ")" => MeromorphicOn.divisor (continuedCompletedHeckeL (F := ℚ) ψ) univ
local notation "Z(" χ ")" => {z : X × ℂ // 0 < D(χ z.1) z.2}
local notation "radial(" φ ", " g ")" => (∀ x : Cℚ, (φ : BruhatCompactSupport Cℚ).val x =
  rationalCenteredLogProfile g (Real.log (((ideleClassNorm ℚ) x).val : ℝ)))
local notation "missing(" α ", " s ", " z ", " m ")" =>
  ((m : ℕ) - spectralStripMultiplicity α s ((z : ℂ).re - 1/2) m : ℕ)
local notation "hTerm(" φ ", " χ ", " α ", " s ", " z ")" =>
  ((missing(α, s, (z).val.2, (D(χ (z).val.1) (z).val.2).toNat) : ℕ) : ℂ) * M(φ, χ (z).val.1, (z).val.2-1/2)
local notation "zTerm(" g ", " α ", " s ", " z ")" =>
  ((missing(α, s, (z : criticalStripZetaZeros).val, zetaZeroOrder z) : ℕ) : ℂ) *
    compactLogMellin g (z : criticalStripZetaZeros).val

/-- For a centered rational radial test the missing-jet sum is exactly the
norm-one Tamagawa volume times the corresponding sum over ordinary zeta
zeros, including the Sobolev losses at either strip edge. -/
theorem rational_radial_missingJets_hasSum_iff (g : ℝ → ℂ)
    (φ : BruhatCompactSupport Cℚ) (hφ : radial(φ, g)) (χ : X →* Uℚ)
    (hχ : IsSpectralBasepointChoice χ) (α s : ℝ) (v : ℂ) :
    HasSum (fun z : Z(χ) ↦ hTerm(φ, χ, α, s, z)) v ↔
      HasSum (fun z : criticalStripZetaZeros ↦ Vℚ * zTerm(g, α, s, z)) v := by
  classical
  let ι (r : criticalStripZetaZeros) : Z(χ) := ⟨(1,r.val), by
    simp only [map_one, rational_heckeDivisor_at_zetaZero]
    exact_mod_cast zetaZeroOrder_pos r⟩
  have hi : Injective ι := fun r t h ↦ Subtype.ext (congrArg (fun z : Z(χ) ↦ z.val.2) h)
  let f (z : Z(χ)) := hTerm(φ, χ, α, s, z)
  have hout (z : Z(χ)) (hz : z ∉ range ι) : f z = 0 := by
    have hn : z.val.1 ≠ 1 := by
      intro h
      have hd := z.property
      rw [h, map_one] at hd
      exact hz ⟨⟨z.val.2, rational_zeta_of_heckeDivisor hd⟩, Subtype.ext (Prod.ext h.symm rfl)⟩
    change _ * M(φ, χ z.val.1, z.val.2 - 1/2) = 0
    rw [rational_radial_mellin_other g φ hφ χ hχ hn, mul_zero]
  have hterm (z : criticalStripZetaZeros) : f (ι z) = Vℚ * zTerm(g, α, s, z) := by
    dsimp only [f, ι]
    rw [map_one, rational_heckeDivisor_at_zetaZero, Int.toNat_natCast, rationalCenteredNormTest_mellin g φ hφ]
    ring
  exact (hi.hasSum_iff (f := f) hout).symm.trans
    ⟨fun h ↦ h.congr_fun (fun z ↦ (hterm z).symm), fun h ↦ h.congr_fun hterm⟩

private theorem compactLogMellin_translate (H : ℝ → ℂ) (y : ℝ) (w : ℂ) :
    compactLogMellin (fun x ↦ H (x-y)) w = compactLogMellin H w * Complex.exp (w*y) := by
  let f (u : ℝ) := H u * Complex.exp (w*u) * Complex.exp (w*y)
  calc
    _ = ∫ x : ℝ, f (x-y) := by
      apply integral_congr_ae (.of_forall fun x ↦ ?_)
      have he : w * (x : ℂ) = w * ((x-y : ℝ) : ℂ) + w*y := by push_cast; ring
      dsimp only [f]
      rw [he, Complex.exp_add, mul_assoc]
    _ = ∫ u : ℝ, f u := integral_sub_right_eq_self f y
    _ = _ := integral_mul_const _ _

/-- Translated smooth radial profiles supported beyond any fixed log norm
determine every individual coefficient of an ordinary zeta-zero distribution. -/
theorem zetaZeroCoeff_eq_zero_of_positive_log (R : ℝ) (c : criticalStripZetaZeros → ℂ)
    (hT : ∀ (g : ℝ → ℂ), ContDiff ℝ (∞) g → HasCompactSupport g →
      ∀ {a b : ℝ}, R < a → tsupport g ⊆ Icc a b →
        HasSum (fun z : criticalStripZetaZeros ↦ c z * compactLogMellin g z.val) 0)
    (z₀ : criticalStripZetaZeros) : c z₀ = 0 := by
  let β : ContDiffBump (R+1) := ⟨1/4, 1/2, by norm_num, by norm_num⟩
  let H (t : ℝ) := (β t : ℂ) * Complex.exp (-(z₀.val * t))
  have hd : ContDiff ℝ (∞) H := (Complex.ofRealCLM.contDiff.comp β.contDiff).mul
    (Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff).neg)
  have hc : HasCompactSupport H := (β.hasCompactSupport.comp_left Complex.ofReal_zero).mul_right
  let B (r : criticalStripZetaZeros) := c r * compactLogMellin H r.val
  have hsum (y : ℝ) (hy : 0 ≤ y) : HasSum (fun r ↦ B r * Complex.exp (shiftedZetaZero r * y)) 0 := by
    let g (x : ℝ) := H (x-y)
    have hs : tsupport g ⊆ Icc (R+1/2+y) (R+3/2+y) := by
      apply closure_minimal _ isClosed_Icc
      intro x hx
      have hdist : dist (x-y) (R+1) < 1/2 := by
        apply lt_of_not_ge
        intro ht
        exact hx (show g x = 0 by simp [g, H, β.zero_of_le_dist ht])
      rw [Real.dist_eq,abs_lt] at hdist
      exact ⟨by linarith, by linarith⟩
    have h := (hT g (hd.comp (contDiff_id.sub contDiff_const))
      (hc.comp_homeomorph (Homeomorph.subRight y)) (by linarith) hs).mul_right (Complex.exp (-(y:ℂ)/2))
    rw [zero_mul] at h
    apply h.congr_fun
    intro z
    dsimp only [B, g]
    have he : shiftedZetaZero z * y = z.val * y + (-(y:ℂ)/2) := by unfold shiftedZetaZero; ring
    rw [compactLogMellin_translate, he, Complex.exp_add]
    ring
  have hdisc (z : ℂ) : ∀ᶠ u in 𝓝[≠] z, u ∉ range shiftedZetaZero := by
    filter_upwards [grh_zeros_discrete (1 : Uℚ) z] with u hu
    rintro ⟨r,rfl⟩
    apply hu
    change 0 < D(1) ((r.val-1/2)+1/2)
    rw [sub_add_cancel, rational_heckeDivisor_at_zetaZero]
    exact_mod_cast zetaZeroOrder_pos r
  have hB : Summable B := by simpa using (hsum 0 le_rfl).summable
  have h0 := eq_zero_of_hasSum_exp_eq_zero shiftedZetaZero B shiftedZetaZero_injective hdisc
    (fun r ↦ ((le_abs_self _).trans (abs_re_shiftedZetaZero_lt r).le)) hB hsum z₀
  have he : compactLogMellin H z₀.val = ((∫ t, β t : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    exact integral_congr_ae (.of_forall fun t ↦ grh_bump_mul_exp _ _)
  exact (mul_eq_zero.mp h0).resolve_right (he ▸ Complex.ofReal_ne_zero.mpr β.integral_pos.ne')

local notation "profiles(" R ")" => {g : ℝ → ℂ // ContDiff ℝ (∞) g ∧ HasCompactSupport g ∧
  ∃ a b : ℝ, R < a ∧ tsupport g ⊆ Icc a b}
local notation "retains(" α ", " s ", " z ")" =>
  spectralStripMultiplicity α s ((z : criticalStripZetaZeros).val.re - 1/2) (zetaZeroOrder z) = zetaZeroOrder z

/-- For rational radial profiles beyond any fixed log norm, a local formula
with the missing-zeta-jet expansion is exact for every test if and only if
the strip retains the full order of each nontrivial zeta zero. -/
theorem rationalPositiveWindow_equality_iff (R α s : ℝ) {d e : profiles(R) → ℂ}
    (h : ∀ p : profiles(R), HasSum (fun z : criticalStripZetaZeros ↦ Vℚ * zTerm(p.val, α, s, z)) (d p-e p)) :
    (∀ p, d p = e p) ↔ ∀ z : criticalStripZetaZeros, retains(α, s, z) := by
  constructor
  · intro he z
    let c (r : criticalStripZetaZeros) := Vℚ * (missing(α, s, r.val, zetaZeroOrder r) : ℂ)
    have hz := zetaZeroCoeff_eq_zero_of_positive_log R c (fun g hg hc a b ha hs ↦ by
      let p : profiles(R) := ⟨g, hg, hc, a, b, ha, hs⟩
      simpa only [c, p, mul_assoc, he p, sub_self] using h p) z
    have hm := (mul_eq_zero.mp hz).resolve_left (grh_classVolume_ne_zero (F := ℚ))
    refine le_antisymm ?_ (Nat.sub_eq_zero_iff_le.mp (Nat.cast_eq_zero.mp hm))
    unfold spectralStripMultiplicity spectralBoundaryMultiplicity
    split_ifs <;> first | exact le_rfl | exact min_le_left _ _ | exact Nat.zero_le _
  · intro hz p
    apply sub_eq_zero.mp
    apply (h p).unique
    simpa only [hz, Nat.sub_self, Nat.cast_zero, zero_mul, mul_zero] using
      (hasSum_zero (α := ℂ) (β := criticalStripZetaZeros))

local notation "physical(" p ")" =>
  exists_rationalCenteredNormTest (p).val (p).property.1 (p).property.2.1
local notation "restrictions(" p ")" =>
  exists_rational_radial_place_tests (p).val (p).property.1 (p).property.2.1
    (physical(p)).choose (physical(p)).choose_spec
local notation "chars" => exists_spectralBasepointChoice_radially_trivial ℚ
local notation "profileBalance(" p ", " hR ", " hα ", " hs ", " U ", " hU ", " hm ")" =>
  (rational_radial_missingJets_hasSum_iff (p).val (physical(p)).choose (physical(p)).choose_spec
    (chars).choose (chars).choose_spec.1 _ _ _).mp
    (integral_rational_window_eq_principalValues_sub_poles_add_missingJets
      (p).val (p).property.1 (p).property.2.1 (lt_of_le_of_lt hR ((p).property.2.2.choose_spec.choose_spec.1))
      ((p).property.2.2.choose_spec.choose_spec.2)
      (physical(p)).choose (physical(p)).choose_spec (restrictions(p)).choose (restrictions(p)).choose_spec.choose
      (restrictions(p)).choose_spec.choose_spec.1 (restrictions(p)).choose_spec.choose_spec.2
      hα hs U hU hm).2.1

local notation "windowCriterion(" R ", " α ", " s ", " hR ", " hα ", " hs ", " U ", " hU ", " hm ")" =>
  rationalPositiveWindow_equality_iff R α s
    (fun p : profiles(R) ↦ profileBalance(p, hR, hα, hs, U, hU, hm))

/-- Paper: Section 12.3, p. 514, and (12.5.1.2)–(12.5.1.4), pp. 519–520.
For the *actual* rational diagonal and the normalized principal values minus
both polar moments, agreement on all smooth radial profiles beyond any fixed
nonnegative log norm is equivalent to retaining the full order of every
nontrivial zeta zero at this width. Each profile and its place restrictions
are realized as compact Bruhat functions. -/
theorem rational_positiveLog_geometric_local_comparison_iff
    {R α s : ℝ} (hR : 0 ≤ R) (hα : 0 < α) (hs : 3 ≤ s)
    (U : ℕ → Set Cℚ) (hU : IsDPrimeSequence μℚ U) (hm : ∀ k, MeasurableSet (U k)) :
    type_of% windowCriterion(R, α, s, hR, hα, hs, U, hU, hm) :=
  windowCriterion(R, α, s, hR, hα, hs, U, hU, hm)

/-- Retaining every ordinary zeta zero with full multiplicity at all
positive half-widths is precisely the ordinary Riemann hypothesis. -/
theorem zeta_all_windows_retain_iff_riemannHypothesis (s : ℝ) :
    (∀ α : ℝ, 0 < α → ∀ z : criticalStripZetaZeros, retains(α, s, z)) ↔ RiemannHypothesis := by
  constructor
  · intro h z hz htriv _h1
    have hp : 0 < z.re := lt_of_not_ge (fun hn ↦ htriv ((riemannZeta_eq_zero_iff_of_re_nonpos hn).mp hz))
    have hlt : z.re < 1 := lt_of_not_ge (fun hn ↦ riemannZeta_ne_zero_of_one_le_re hn hz)
    let r : criticalStripZetaZeros := ⟨z, mem_criticalStripZetaZeros.mpr ⟨hz, hp, hlt⟩⟩
    by_contra hn
    have hb : 0 < |z.re-1/2| := abs_pos.mpr (sub_ne_zero.mpr hn)
    let α := |z.re-1/2| / 2
    have hα : 0 < α := half_pos hb
    have hout : α < |z.re-1/2| := by dsimp [α]; linarith
    have hinner : ¬ (-α < z.re-1/2 ∧ z.re-1/2 < α) := fun he ↦ (not_lt.mpr hout.le) (abs_lt.mpr he)
    have hedge : ¬ (z.re-1/2 = -α ∨ z.re-1/2 = α) := by
      rintro (he|he) <;> rw [he] at hout <;> simp [abs_of_pos hα] at hout
    have he := h α hα r
    change spectralStripMultiplicity α s (z.re-1/2) _ = _ at he
    simp only [spectralStripMultiplicity, ite_eq_right hinner, ite_eq_right hedge] at he
    exact (zetaZeroOrder_pos r).ne' he.symm
  · intro rh α ha r
    obtain ⟨hr, hp, hlt⟩ := mem_criticalStripZetaZeros.mp r.property
    have htriv : ¬ ∃ n : ℕ, r.val = -2 * (n+1) := by
      rintro ⟨n, he⟩
      rw [he] at hp
      norm_num [Complex.mul_re] at hp
      linarith [Nat.cast_nonneg (α := ℝ) n]
    have h1 : r.val ≠ 1 := fun h ↦ by simp [h] at hlt
    rw [rh r.val hr htriv h1, sub_self]
    exact ite_eq_left ⟨neg_lt_zero.mpr ha, ha⟩

/-- Pass from the individual half-width comparisons to the ordinary Riemann hypothesis. -/
theorem rationalWindow_all_iff (s : ℝ) {P : (α : ℝ) → 0 < α → Prop}
    (h : ∀ α (ha : 0 < α), P α ha ↔ ∀ z : criticalStripZetaZeros, retains(α, s, z)) :
    (∀ α (ha : 0 < α), P α ha) ↔ RiemannHypothesis :=
  (forall_congr' fun α ↦ forall_congr' fun ha ↦ h α ha).trans (zeta_all_windows_retain_iff_riemannHypothesis s)

local notation "allWidths(" s ", " hR ", " hs ", " U ", " hU ", " hm ")" =>
  rationalWindow_all_iff s (fun α (ha : 0 < α) ↦
    rational_positiveLog_geometric_local_comparison_iff hR ha hs U hU hm)

/-- Paper: Section 12.3, p. 514, and p. 520. For the rational field, the
uncorrected comparison between the actual geometric diagonal and the actual
normalized local sum minus both polar moments, at every positive half-width,
is equivalent to the ordinary Riemann hypothesis even on smooth radial tests
supported above any prescribed nonnegative log norm. Compact support may
vary with the test. -/
theorem rational_allWidths_positiveLog_geometric_local_comparison_iff_riemannHypothesis
    {R s : ℝ} (hR : 0 ≤ R) (hs : 3 ≤ s)
    (U : ℕ → Set Cℚ) (hU : IsDPrimeSequence μℚ U) (hm : ∀ k, MeasurableSet (U k)) :
    type_of% allWidths(s, hR, hs, U, hU, hm) :=
  allWidths(s, hR, hs, U, hU, hm)

end RiemannMasullo.StripNuclearity
