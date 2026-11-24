module

public import RiemannMasullo.Research.TraceComparison.GeometricWidthLimit
import RiemannMasullo.Research.StripNuclearity.NormSectionCharacters
import Mathlib.Analysis.Normed.Group.Tannery

/-! # Continuity in the strip half-width

The two one-sided limits of the global geometric diagonal retain or omit every
jet on the boundary. Absolute convergence allows their difference to be grouped
by the distance of a zero from the critical line.
-/

@[expose] public noncomputable section

open Filter MeasureTheory NumberField Set
open scoped NumberField.AdeleRing NNReal Topology

namespace RiemannMasullo.StripNuclearity

section WidthSum

variable {ι : Type*} (β : ι → ℝ) (m : ι → ℕ) (v : ι → ℂ)

private def stripMomentSum (s : ℝ) (r : ℝ) : ℂ :=
  ∑' i, (spectralStripMultiplicity r s (β i) (m i) : ℂ) * v i

private theorem stripMultiplicity_zero_outside {r b : ℝ} (hr : 0 ≤ r) (h : r < |b|)
    (s : ℝ) (n : ℕ) : spectralStripMultiplicity r s b n = 0 := by
  have hi : ¬ (-r < b ∧ b < r) := fun hx ↦ (not_lt_of_ge h.le) (abs_lt.mpr hx)
  have he : ¬ (b = -r ∨ b = r) := by
    rintro (rfl | rfl) <;> simp [abs_of_nonneg hr] at h
  simp [spectralStripMultiplicity, hi, he]

private theorem stripMomentSum_tendsto {l : Filter ℝ} {s : ℝ}
    (hv : Summable (fun i ↦ ‖(m i : ℂ) * v i‖)) (p : ι → Prop) [DecidablePred p]
    (hpos : ∀ᶠ x in l, 0 ≤ x)
    (hin : ∀ i, p i → ∀ᶠ x in l, |β i| < x)
    (hout : ∀ i, ¬p i → ∀ᶠ x in l, x < |β i|) :
    Tendsto (stripMomentSum β m v s) l (𝓝 (∑' i, if p i then (m i : ℂ) * v i else 0)) := by
  apply tendsto_tsum_of_dominated_convergence hv
  · intro i
    by_cases h : p i
    · simp only [ite_eq_left h]
      apply tendsto_const_nhds.congr'
      filter_upwards [hin i h] with x hx
      rw [spectralStripMultiplicity_interior (abs_lt.mp hx)]
    · simp only [ite_eq_right h]
      apply tendsto_const_nhds.congr'
      filter_upwards [hpos, hout i h] with x hx hxi
      rw [stripMultiplicity_zero_outside hx hxi, Nat.cast_zero, zero_mul]
  · apply Filter.Eventually.of_forall
    intro x i
    have h : spectralStripMultiplicity x s (β i) (m i) ≤ m i := by
      unfold spectralStripMultiplicity spectralBoundaryMultiplicity
      split_ifs <;> first | exact le_rfl | exact min_le_left _ _ | exact Nat.zero_le _
    simp only [norm_mul, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast h) (norm_nonneg _)

private theorem stripMomentSum_oneSided {r s : ℝ} (hr : 0 < r)
    (hv : Summable (fun i ↦ ‖(m i : ℂ) * v i‖)) :
    Tendsto (stripMomentSum β m v s) (𝓝[<] r)
        (𝓝 (∑' i, if |β i| < r then (m i : ℂ) * v i else 0)) ∧
    Tendsto (stripMomentSum β m v s) (𝓝[>] r)
        (𝓝 (∑' i, if |β i| ≤ r then (m i : ℂ) * v i else 0)) := by
  constructor
  · apply stripMomentSum_tendsto β m v hv (fun i ↦ |β i| < r)
    · exact ((eventually_gt_nhds hr).filter_mono nhdsWithin_le_nhds).mono fun _ h ↦ h.le
    · exact fun _ h ↦ (eventually_gt_nhds h).filter_mono nhdsWithin_le_nhds
    · intro i hi
      filter_upwards [self_mem_nhdsWithin (s := Iio r)] with x hx using hx.trans_le (le_of_not_gt hi)
  · apply stripMomentSum_tendsto β m v hv (fun i ↦ |β i| ≤ r)
    · exact ((eventually_gt_nhds hr).filter_mono nhdsWithin_le_nhds).mono fun _ h ↦ h.le
    · intro i hi
      filter_upwards [self_mem_nhdsWithin (s := Ioi r)] with x hx using lt_of_le_of_lt hi hx
    · exact fun _ h ↦ (eventually_lt_nhds (lt_of_not_ge h)).filter_mono nhdsWithin_le_nhds

private theorem stripMomentSum_eq_full_of_continuous {s : ℝ}
    (hv : Summable (fun i ↦ ‖(m i : ℂ) * v i‖))
    (hc : ContinuousOn (stripMomentSum β m v s) (Ioi 0)) {a : ℝ} (ha : 0 < a) :
    stripMomentSum β m v s a = ∑' i, (m i : ℂ) * v i := by
  classical
  let d (i : ι) := |β i|
  let V (i : ι) := (m i : ℂ) * v i
  have hV : Summable V := hv.of_norm
  have piece (p : ι → Prop) [DecidablePred p] : Summable (fun i ↦ if p i then V i else 0) := by
    exact (hV.indicator {i | p i}).congr (fun i ↦ by simp [Set.indicator_apply])
  have side (r : ℝ) (hr : 0 < r) :
      (∑' i, if d i < r then V i else 0) = stripMomentSum β m v s r ∧
      (∑' i, if d i ≤ r then V i else 0) = stripMomentSum β m v s r := by
    have ht := (hc r (show r ∈ Ioi 0 from hr)).continuousAt (isOpen_Ioi.mem_nhds hr)
    have sides := stripMomentSum_oneSided β m v hr hv (s:=s)
    exact ⟨tendsto_nhds_unique sides.1 (ht.tendsto.mono_left nhdsWithin_le_nhds),
      tendsto_nhds_unique sides.2 (ht.tendsto.mono_left nhdsWithin_le_nhds)⟩
  have edge (r : ℝ) (hr : 0 < r) : ∑' i : d ⁻¹' {r}, V i.val = 0 := by
    have he (i : ι) : (if d i ≤ r then V i else 0) - (if d i < r then V i else 0) =
        (d ⁻¹' {r}).indicator V i := by
      rcases lt_trichotomy (d i) r with h | h | h
      · simp [h, h.le, h.ne]
      · simp [h]
      · simp [h.not_ge, h.not_gt, h.ne']
    rw [tsum_subtype, ← tsum_congr he, (piece (fun i ↦ d i ≤ r)).tsum_sub (piece (fun i ↦ d i < r)),
      (side r hr).1, (side r hr).2, sub_self]
  have outside := (piece (fun i ↦ a < d i)).hasSum.tsum_fiberwise d
  have fiber (r : ℝ) : (∑' i : d ⁻¹' {r}, if a < d i.val then V i.val else 0) = 0 := by
    by_cases h : a < r
    · rw [← edge r (ha.trans h)]
      exact tsum_congr fun i ↦ ite_eq_left (show a < d i.val by rwa [show d i.val = r from i.property])
    · have he (i : d ⁻¹' {r}) : ¬ a < d i.val := by rwa [show d i.val = r from i.property]
      simp [he]
  have hz : (∑' i, if a < d i then V i else 0) = 0 := by
    simpa only [fiber, tsum_zero] using outside.tsum_eq.symm
  have he (i : ι) : (if d i ≤ a then V i else 0) + (if a < d i then V i else 0) = V i := by
    by_cases h : d i ≤ a
    · simp [h, not_lt.mpr h]
    · simp [h, lt_of_not_ge h]
  rw [← (side a ha).2]
  calc
    _ = (∑' i, if d i ≤ a then V i else 0) + (∑' i, if a < d i then V i else 0) := by rw [hz, add_zero]
    _ = ∑' i, ((if d i ≤ a then V i else 0) + (if a < d i then V i else 0)) :=
      ((piece (fun i ↦ d i ≤ a)).tsum_add (piece (fun i ↦ a < d i))).symm
    _ = _ := tsum_congr he

end WidthSum


section ActualDiagonal

variable {F : Type*} [Field F] [NumberField F]

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

set_option quotPrecheck false
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "μ" => ideleClassTamagawaMeasure F
local notation "pos" => Ioi (0:ℝ)
local notation "m𝔽" => (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "hm" => (⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ : IsModulation m𝔽)
local notation "divisor(" χ ")" => MeromorphicOn.divisor (continuedCompletedHeckeL (F:=F) χ) univ

/-- Paper: Section 12.3, p. 514, and (12.5.1.4), p. 520. For a fixed physical
test and Sobolev order, continuity of the actual smoothed global diagonal
on the positive half-widths is equivalent to agreement at every positive
half-width with its full-width value. Each width may use its own smoothing
sequence. The argument applies to every number field.
Deviation: This gives a sufficient geometric regularity condition. The
continuity hypothesis at interior widths is an additional assertion. -/
theorem continuous_centeredStripDiagonalIntegral_iff_eq_wide
    (φ : BruhatCompactSupport C𝔽) (hφ : ∀ g : C₁, φ.val g = 0)
    {s : ℝ} (hs : 3 ≤ s) (U : pos → ℕ → Set C𝔽)
    (hU : ∀ a, IsDPrimeSequence μ (U a)) (hM : ∀ a n, MeasurableSet (U a n)) :
    let d (a : pos) := centeredStripGeometricDiagonalIntegral φ a.property hs (U a)
    let half : pos := ⟨1/2, half_pos zero_lt_one⟩
    Continuous d ↔ ∀ a, d a = d half := by
  intro d half
  constructor
  · intro hc
    let chars := exists_spectralBasepointChoice_radially_trivial F
    let χ := chars.choose
    let Z := {z : PontryaginDual C₁ × ℂ // 0 < divisor(χ z.1) z.2}
    let β (z : Z) := z.val.2.re - 1/2
    let m (z : Z) := (divisor(χ z.val.1) z.val.2).toNat
    let v (z : Z) := modulatedFourierMellin m𝔽 univ hm μ φ.val
      (ideleClassNormTwist (χ z.val.1) (z.val.2 - 1/2))
    have hf := (hasSum_numberField_allHeckeZeros_neg_integral_smoothenedDiagonal (F:=F)
      φ hφ χ chars.choose_spec.1 (α:=1/2) le_rfl hs (U half) (hU half) (hM half)).2.1
    have hv : Summable (fun z : Z ↦ ‖(m z : ℂ) * v z‖) := by
      apply hf.congr
      intro z
      have e : (m z : ℂ) = (divisor(χ z.val.1) z.val.2 : ℂ) := by
        exact_mod_cast Int.toNat_of_nonneg z.property.le
      rw [e]
    have he (a : pos) : stripMomentSum β m v s a.val = - d a :=
      (hasSum_keptHeckeZeros_neg_centeredStripDiagonalIntegral (F:=F) φ hφ χ chars.choose_spec.1
        a.property hs (U a) (hU a) (hM a)).tsum_eq
    have hcont : ContinuousOn (stripMomentSum β m v s) pos := by
      apply continuousOn_iff_continuous_domRestrict.mpr
      exact hc.neg.congr (fun a ↦ (he a).symm)
    intro a
    have eq := (stripMomentSum_eq_full_of_continuous β m v hv hcont a.property).trans
      (stripMomentSum_eq_full_of_continuous β m v hv hcont half.property).symm
    exact neg_injective ((he a).symm.trans (eq.trans (he half)))
  · intro he
    exact continuous_const.congr (fun a ↦ (he a).symm)


local notation "chart(" τ ")" => {η : PontryaginDual C𝔽 // ∀ t : ℝ≥0ˣ, η (τ t) = 1}
local notation "extZeros(" τ "," r ")" =>
  {p : chart(τ) × ℂ // 0 < divisor(p.1.val) p.2 ∧ r ≤ |p.2.re - 1/2|}
local notation "zeroTerm(" φ "," p ")" =>
  ((divisor((p).val.1.val) (p).val.2 : ℤ) : ℂ) * modulatedFourierMellin m𝔽 univ hm μ
    (φ : BruhatCompactSupport C𝔽).val (ideleClassNormTwist (F:=F) (p).val.1.val ((p).val.2 - 1/2))

/-- Paper: Section 12.3, p. 514, and Theorem 12.5.1.1, pp. 519–520.
For any norm section and one physical test, the global diagonal has a
left limit at each positive half-width. Its excess over the wide diagonal
is exactly the exterior Hecke zero sum of the open strip in Chapter 12.
Every zero on either edge contributes its full multiplicity.
Deviation: Taking the limit from smaller widths removes the finite-order
edge convention of the Hilbert-space trace without a hypothesis on zeros. -/
theorem exists_leftLimit_centeredStripDiagonalIntegral_exteriorZeros
    (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : Function.RightInverse τ (ideleClassNorm F))
    (φ : BruhatCompactSupport C𝔽) (hφ : ∀ g : C₁, φ.val g = 0) {s : ℝ} (hs : 3 ≤ s)
    (U : pos → ℕ → Set C𝔽) (hU : ∀ t, IsDPrimeSequence μ (U t)) (hM : ∀ t n, MeasurableSet (U t n))
    (r : pos) :
    let d (t : pos) := centeredStripGeometricDiagonalIntegral φ t.property hs (U t)
    let half : pos := ⟨1/2, half_pos zero_lt_one⟩
    ∃ L : ℂ, Tendsto d (𝓝[<] r) (𝓝 L) ∧ HasSum (fun z : extZeros(τ,r.val) ↦ zeroTerm(φ,z)) (L-d half) := by
  classical
  intro d half
  let e := normSectionCharacterEquiv τ hτ
  let χ (ξ : PontryaginDual C₁) := (e ξ).val
  have hχ : IsSpectralBasepointChoice χ := isSpectralBasepointChoice_normSection τ hτ
  let Z := {p : PontryaginDual C₁ × ℂ // 0 < divisor(χ p.1) p.2}
  let β (z : Z) := z.val.2.re - 1/2
  let m (z : Z) := (divisor(χ z.val.1) z.val.2).toNat
  let v (z : Z) := modulatedFourierMellin m𝔽 univ hm μ φ.val
    (ideleClassNormTwist (χ z.val.1) (z.val.2 - 1/2))
  let V (z : Z) := (m z : ℂ) * v z
  have castM (z : Z) : (m z : ℂ) = (divisor(χ z.val.1) z.val.2 : ℂ) := by
    exact_mod_cast Int.toNat_of_nonneg z.property.le
  have full := (hasSum_numberField_allHeckeZeros_neg_integral_smoothenedDiagonal (F:=F)
    φ hφ χ hχ (α:=1/2) le_rfl hs (U half) (hU half) (hM half)).2
  have hv : Summable (fun z : Z ↦ ‖(m z : ℂ)*v z‖) :=
    full.1.congr (fun z ↦ by rw [castM])
  have hfull : HasSum V (-d half) := full.2.congr_fun (fun z ↦ by dsimp only [V]; rw [castM])
  let I : Set Z := {z | |β z| < r.val}
  let J := ∑' z : I, V z.val
  have hI : HasSum (V ∘ ((↑) : I → Z)) J := (hfull.summable.subtype (fun z ↦ z ∈ I)).hasSum
  have hJ : (∑' z : Z, if |β z| < r.val then (m z : ℂ)*v z else 0) = J := by
    dsimp only [J]
    rw [tsum_subtype]
    exact tsum_congr (fun z ↦ by simp [I, V, Set.indicator_apply])
  have hsub : Tendsto ((↑) : pos → ℝ) (𝓝[<] r) (𝓝[<] r.val) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨continuous_subtype_val.continuousAt.tendsto.mono_left nhdsWithin_le_nhds, self_mem_nhdsWithin⟩
  have hlim := ((stripMomentSum_oneSided β m v r.property hv (s:=s)).1.comp hsub).neg
  rw [hJ] at hlim
  refine ⟨-J, hlim.congr' (.of_forall fun t ↦ ?_), ?_⟩
  · have he : stripMomentSum β m v s t.val = -d t :=
      (hasSum_keptHeckeZeros_neg_centeredStripDiagonalIntegral (F:=F) φ hφ χ hχ
        t.property hs (U t) (hU t) (hM t)).tsum_eq
    exact (congrArg Neg.neg he).trans (neg_neg _)
  · let E : ↥(Iᶜ) ≃ extZeros(τ,r.val) := {
      toFun := fun z ↦ ⟨(e z.val.val.1, z.val.val.2), z.val.property, le_of_not_gt z.property⟩
      invFun := fun z ↦ ⟨⟨(e.symm z.val.1, z.val.2), by
        change 0 < divisor((e (e.symm z.val.1)).val) z.val.2
        rw [e.apply_symm_apply]
        exact z.property.1⟩, not_lt.mpr z.property.2⟩
      left_inv := fun z ↦ by apply Subtype.ext; apply Subtype.ext; exact Prod.ext (e.symm_apply_apply _) rfl
      right_inv := fun z ↦ by apply Subtype.ext; exact Prod.ext (e.apply_symm_apply _) rfl }
    have hrest := hI.hasSum_iff_compl.mp hfull
    have hsign : -d half - J = -J - d half := by ring
    rw [← hsign]
    apply E.hasSum_iff.mp
    apply hrest.congr_fun
    intro z
    change (divisor(χ z.val.val.1) z.val.val.2 : ℂ) * v z.val = (m z.val : ℂ) * v z.val
    rw [castM]

/-- Paper: Theorem 12.5.1.1, pp. 519–520. For one norm section, test and
positive half-width, the exact conclusion of the exterior-zero gap holds
if and only if the actual global geometric diagonal approaches the wide
value from smaller half-widths. This includes both strip edges.
Deviation: This identifies the geometric limit still needed at p. 520. -/
theorem exteriorZeros_iff_leftLimit_centeredStripDiagonalIntegral_eq_wide
    (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : Function.RightInverse τ (ideleClassNorm F))
    (φ : BruhatCompactSupport C𝔽) (hφ : ∀ g : C₁, φ.val g = 0) {s : ℝ} (hs : 3 ≤ s)
    (U : pos → ℕ → Set C𝔽) (hU : ∀ t, IsDPrimeSequence μ (U t)) (hM : ∀ t n, MeasurableSet (U t n))
    (r : pos) :
    let d (t : pos) := centeredStripGeometricDiagonalIntegral φ t.property hs (U t)
    let half : pos := ⟨1/2, half_pos zero_lt_one⟩
    HasSum (fun z : extZeros(τ,r.val) ↦ zeroTerm(φ,z)) 0 ↔ Tendsto d (𝓝[<] r) (𝓝 (d half)) := by
  intro d half
  obtain ⟨L,hL,hExt⟩ := exists_leftLimit_centeredStripDiagonalIntegral_exteriorZeros τ hτ φ hφ hs U hU hM r
  change HasSum _ (L - d half) at hExt
  constructor
  · intro h
    have e : L = d half := sub_eq_zero.mp (hExt.unique h)
    exact e ▸ hL
  · intro h
    have e : L = d half := tendsto_nhds_unique hL h
    simpa only [e, sub_self] using hExt

/-- Paper: Theorem 12.5.1.1, pp. 519–520. Continuity in the positive half-width
of the global projected diagonal for one physical test implies the exterior
cancellation required in Chapter 12 for that test at every width.
Deviation: The width-continuity hypothesis is the independent geometric step. -/
theorem traceFormula_exteriorZeros_of_continuous_centeredStripDiagonalIntegral
    (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : Function.RightInverse τ (ideleClassNorm F))
    (φ : BruhatCompactSupport C𝔽) (hφ : ∀ g : C₁, φ.val g = 0) {s : ℝ} (hs : 3 ≤ s)
    (U : pos → ℕ → Set C𝔽) (hU : ∀ t, IsDPrimeSequence μ (U t)) (hM : ∀ t n, MeasurableSet (U t n))
    (hc : Continuous fun t : pos ↦ centeredStripGeometricDiagonalIntegral φ t.property hs (U t))
    (r : pos) : HasSum (fun z : extZeros(τ,r.val) ↦ zeroTerm(φ,z)) 0 := by
  apply (exteriorZeros_iff_leftLimit_centeredStripDiagonalIntegral_eq_wide τ hτ φ hφ hs U hU hM r).mpr
  have eq := (continuous_centeredStripDiagonalIntegral_iff_eq_wide φ hφ hs U hU hM).mp hc
  exact tendsto_const_nhds.congr' (.of_forall fun t ↦ (eq t).symm)

end ActualDiagonal

end RiemannMasullo.StripNuclearity
