module

public import RiemannMasullo.Research.StripNuclearity.BoundedMellinSeparation
public import RiemannMasullo.Research.StripNuclearity.RationalZeroWindow
public import RiemannMasullo.Research.StripNuclearity.RationalPrimeFreeDiagonal

/-! # The rational trace comparison on a fixed bounded interval of log norms

A nontrivial zeta zero contributes to the missing-jet distribution only when the
strip omits its full multiplicity or some of its boundary jets. The reciprocal
summability used for bounded-interval separation concerns this smaller set. -/

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
local notation "μℚ" => ideleClassTamagawaMeasure ℚ
local notation "Vℚ" => (((normOneIdeleClassTamagawaMeasure ℚ) univ).toReal : ℂ)
local notation "kept(" α "," s "," r ")" =>
  spectralStripMultiplicity α s ((r : criticalStripZetaZeros).val.re - 1 / 2) (zetaZeroOrder r)
local notation "missing(" α "," s "," r ")" => (zetaZeroOrder r - kept(α,s,r) : ℕ)
local notation "profiles(" a "," b ")" =>
  {g : ℝ → ℂ // ContDiff ℝ (∞) g ∧ HasCompactSupport g ∧ tsupport g ⊆ Icc a b}
local notation "term(" g "," α "," s "," z ")" =>
  Vℚ * ((missing(α,s,z) : ℂ) * compactLogMellin g (z : criticalStripZetaZeros).val)

/-- The ordinary zeta zeros whose full jet multiplicity is absent at this width,
including zeros with partially retained boundary multiplicity. -/
def rationalWindowOmittedZeros (α s : ℝ) : Set criticalStripZetaZeros :=
  {z | 0 < missing(α,s,z)}

/-- The rational norm-one idèle class group has strictly positive finite Tamagawa mass. -/
theorem rationalNormOneTamagawaVolume_ne_zero : Vℚ ≠ 0 := by
  let K := (ideleClassNorm ℚ).ker
  let μ := normOneIdeleClassTamagawaMeasure ℚ
  let : CompactSpace K := (ideleClassGroup_finiteness ℚ).2.1
  let : μ.IsHaarMeasure := (multiplicativeTamagawaMeasures_existsUnique ℚ).exists.choose_spec.2.2.2.1
  exact Complex.ofReal_ne_zero.mpr (ENNReal.toReal_ne_zero.mpr
    ⟨isOpen_univ.measure_ne_zero μ univ_nonempty, measure_ne_top μ univ⟩)

/-- Translating the ordinates by a fixed real number preserves reciprocal summability. -/
theorem summable_reciprocal_shift {ι : Type*} (t : ι → ℝ)
    (h : Summable (fun i ↦ 1 / (1 + |t i|))) (x : ℝ) :
    Summable (fun i ↦ 1 / (1 + |t i - x|)) := by
  apply (h.mul_left (1 + |x|)).of_nonneg_of_le (fun i ↦ by positivity)
  intro i
  have ht : |t i| ≤ |t i - x| + |x| := by
    simpa only [sub_add_cancel] using abs_add_le (t i - x) x
  rw [← mul_div_assoc, mul_one]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [mul_nonneg (abs_nonneg x) (abs_nonneg (t i - x))]

/-- Restricting a rational missing-jet Mellin sum to the ordinary zeros with
positive omitted multiplicity preserves its sum. -/
theorem rationalWindow_omitted_hasSum_iff (g : ℝ → ℂ) (α s : ℝ) (v : ℂ) :
    HasSum (fun i : rationalWindowOmittedZeros α s ↦
      (Vℚ * (missing(α,s,i.val) : ℂ)) * compactLogMellin g i.val.val) v ↔
    HasSum (fun z : criticalStripZetaZeros ↦ term(g,α,s,z)) v := by
  have h : HasSum (fun i : rationalWindowOmittedZeros α s ↦ term(g,α,s,i.val)) v ↔
      HasSum (fun z : criticalStripZetaZeros ↦ term(g,α,s,z)) v := by
    apply Subtype.val_injective.hasSum_iff (g := (Subtype.val : rationalWindowOmittedZeros α s → _))
      (f := fun z : criticalStripZetaZeros ↦ term(g,α,s,z))
    intro z hz
    have hn : missing(α,s,z) = 0 := by
      by_contra! hn
      exact hz ⟨⟨z, Nat.pos_of_ne_zero hn⟩, rfl⟩
    simp only [hn, Nat.cast_zero, zero_mul, mul_zero]
  simpa only [mul_assoc] using h

/-- On a fixed bounded logarithmic interval, vanishing of the rational missing-jet
correction for every test is equivalent to retention of every ordinary zero with its
full multiplicity. Reciprocal ordinates are required to be summable only over zeros
with a positive missing coefficient. -/
theorem rationalBoundedWindow_equality_iff {a b α s : ℝ} (hab : a < b)
    (hu : Summable (fun r : rationalWindowOmittedZeros α s ↦ 1 / (1 + |r.val.val.im|)))
    {d e : profiles(a,b) → ℂ}
    (h : ∀ p : profiles(a,b), HasSum (fun z : criticalStripZetaZeros ↦ term(p.val,α,s,z)) (d p - e p)) :
    (∀ p, d p = e p) ↔ ∀ r : criticalStripZetaZeros, kept(α,s,r) = zetaZeroOrder r := by
  constructor
  · intro he r
    have hupper : kept(α,s,r) ≤ zetaZeroOrder r := by
      unfold spectralStripMultiplicity spectralBoundaryMultiplicity
      split_ifs <;> first | exact le_rfl | exact min_le_left _ _ | exact Nat.zero_le _
    apply le_antisymm hupper
    by_contra! hlt
    have hp : 0 < missing(α,s,r) := Nat.sub_pos_of_lt hlt
    let c (i : rationalWindowOmittedZeros α s) := Vℚ * (missing(α,s,i.val) : ℂ)
    let index (i : rationalWindowOmittedZeros α s) := i.val.val
    have hz (i : rationalWindowOmittedZeros α s) : (index i).re ∈ Icc (0 : ℝ) 1 := by
      obtain ⟨_, hx, hy⟩ := mem_criticalStripZetaZeros.mp i.val.property
      exact ⟨hx.le, hy.le⟩
    have hrec : Summable (fun j : rationalWindowOmittedZeros α s ↦
        1 / (1 + |(index j - r.val).im|)) := by
      simpa only [index, Complex.sub_im] using
        summable_reciprocal_shift (fun i : rationalWindowOmittedZeros α s ↦ i.val.val.im) hu r.val.im
    have h₀ := boundedWindow_mellin_coeff_eq_zero index (fun _ _ h ↦ Subtype.ext (Subtype.ext h))
      hz c ⟨r,hp⟩ hrec hab (fun g hg hc hgI ↦ by
      let p : profiles(a,b) := ⟨g, hg, hc, hgI⟩
      have hsum : HasSum (fun z : criticalStripZetaZeros ↦ term(g,α,s,z)) 0 := by
        simpa only [p, he p, sub_self] using h p
      have hc₀ := (rationalWindow_omitted_hasSum_iff g α s 0).mpr hsum
      exact ⟨hc₀.summable.norm, hc₀⟩)
    exact (mul_ne_zero rationalNormOneTamagawaVolume_ne_zero (Nat.cast_ne_zero.mpr hp.ne')) h₀
  · intro hr p
    apply sub_eq_zero.mp
    apply (h p).unique
    simpa only [hr, Nat.sub_self, Nat.cast_zero, zero_mul, mul_zero] using
      (hasSum_zero (α := ℂ) (β := criticalStripZetaZeros))

local notation "physical(" p ")" =>
  exists_rationalCenteredNormTest (p).val (p).property.1 (p).property.2.1
local notation "restrictions(" p ")" =>
  exists_rational_radial_place_tests (p).val (p).property.1 (p).property.2.1
    (physical(p)).choose (physical(p)).choose_spec
local notation "chars" => exists_spectralBasepointChoice_radially_trivial ℚ
local notation "balance(" p "," ha "," hα "," hs "," U "," hU "," hm ")" =>
  (rational_radial_missingJets_hasSum_iff (p).val (physical(p)).choose (physical(p)).choose_spec
    (chars).choose (chars).choose_spec.1 _ _ _).mp
    (integral_rational_window_eq_principalValues_sub_poles_add_missingJets
      (p).val (p).property.1 (p).property.2.1 ha (p).property.2.2
      (physical(p)).choose (physical(p)).choose_spec (restrictions(p)).choose (restrictions(p)).choose_spec.choose
      (restrictions(p)).choose_spec.choose_spec.1 (restrictions(p)).choose_spec.choose_spec.2
      hα hs U hU hm).2.1

local notation "criterion(" a "," b "," ha "," hab "," hα "," hs "," hu "," U "," hU "," hm ")" =>
  rationalBoundedWindow_equality_iff hab hu
    (fun p : profiles(a,b) ↦ balance(p,ha,hα,hs,U,hU,hm))

/-- Paper: §12.3, p. 514 and (12.5.1.2)–(12.5.1.4), pp. 519–520. At a given positive
width, the actual rational geometric diagonal agrees with the normalized local principal
values minus both poles on every smooth radial test supported in this single compact
logarithmic interval if and only if the strip represents every ordinary zeta zero with
full multiplicity, provided the omitted ordinates satisfy the stated reciprocal sum. -/
theorem rational_boundedLog_geometric_local_comparison_iff
    {a b α s : ℝ} (ha : 0 < a) (hab : a < b) (hα : 0 < α) (hs : 3 ≤ s)
    (hu : Summable (fun r : rationalWindowOmittedZeros α s ↦ 1 / (1 + |r.val.val.im|)))
    (U : ℕ → Set Cℚ) (hU : IsDPrimeSequence μℚ U) (hm : ∀ k, MeasurableSet (U k)) :
    type_of% criterion(a,b,ha,hab,hα,hs,hu,U,hU,hm) := criterion(a,b,ha,hab,hα,hs,hu,U,hU,hm)

local notation "allWidths(" ha "," hab "," hs "," hu "," U "," hU "," hm ")" =>
  rationalWindow_all_iff _ (fun α hα ↦
    rational_boundedLog_geometric_local_comparison_iff ha hab hα hs (hu α hα) U hU hm)

/-- Paper: §12.3, p. 514 and p. 520. Under reciprocal summability of the omitted
ordinary zeros at each positive width, the global–local comparison on one fixed
positive bounded logarithmic interval, for every positive width, is equivalent to the
ordinary Riemann hypothesis. The test interval is independent of the width. -/
theorem rational_allWidths_boundedLog_geometric_local_comparison_iff_riemannHypothesis
    {a b s : ℝ} (ha : 0 < a) (hab : a < b) (hs : 3 ≤ s)
    (hu : ∀ α : ℝ, 0 < α →
      Summable (fun r : rationalWindowOmittedZeros α s ↦ 1 / (1 + |r.val.val.im|)))
    (U : ℕ → Set Cℚ) (hU : IsDPrimeSequence μℚ U) (hm : ∀ k, MeasurableSet (U k)) :
    type_of% allWidths(ha,hab,hs,hu,U,hU,hm) := allWidths(ha,hab,hs,hu,U,hU,hm)

/-- For a smooth rational radial profile supported at norms strictly between one
and two, the local side of the explicit formula is the single real gamma integral. -/
theorem rationalWeilLocalValue_eq_primeFree_realIntegral (g : ℝ → ℂ)
    (hg : ContDiff ℝ (∞) g) (hc : HasCompactSupport g) {a b : ℝ}
    (ha : 0 < a) (hb : b < Real.log 2) (hgI : tsupport g ⊆ Icc a b) :
    rationalWeilLocalValue g = ∫ x in Ioi (0 : ℝ), g x / (1 - Complex.exp (-2 * (x : ℂ))) := by
  obtain ⟨φ, hφ⟩ := exists_rationalCenteredNormTest g hg hc
  obtain ⟨A, _, hA, _⟩ := exists_rational_prime_free_place_tests g hg hc ha hb hgI φ hφ
  have h := rationalWeilLocalValue_eq_principalValues g hg.continuous ha hb hgI φ hφ A (fun _ ↦ 0)
    hA (fun v u ↦ (rational_finite_prime_free_restriction ha hb hgI φ hφ v u).symm)
  simp only [map_zero, mul_zero, tsum_zero, add_zero, Fintype.sum_subsingleton _ Rat.infinitePlace] at h
  apply h.trans
  apply rational_real_principalValue_positive_log_profile g hg.continuous ha hgI
  intro u
  rw [hA, hφ, ideleClassNorm_ofCompletion, Rat.isReal_infinitePlace.mult_eq_one, pow_one]
  rfl

local notation "primeFreeValue(" p "," ha "," hb ")" =>
  (rational_prime_free_places_sub_global_poles (p).val (p).property.1.continuous ha hb (p).property.2.2
    (physical(p)).choose (physical(p)).choose_spec (restrictions(p)).choose (restrictions(p)).choose_spec.choose
    (restrictions(p)).choose_spec.choose_spec.1 (restrictions(p)).choose_spec.choose_spec.2).symm.trans
    (congrArg (fun l : ℂ ↦ Vℚ * (l - compactLogMellin (p).val 0 - compactLogMellin (p).val 1))
      (rationalWeilLocalValue_eq_primeFree_realIntegral
        (p).val (p).property.1 (p).property.2.1 ha hb (p).property.2.2))

local notation "realBalance(" p "," ha "," hb "," hα "," hs "," U "," hU "," hm ")" =>
  (rationalWindow_of_two_evaluations
    ⟨(balance(p,ha,hα,hs,U,hU,hm)).summable.norm, balance(p,ha,hα,hs,U,hU,hm)⟩
    (primeFreeValue(p,ha,hb))).2.1

local notation "radialTest(" g "," hg "," hc "," hgI ")" =>
  (⟨g, hg, hc, hgI⟩ : profiles(_,_))

/-- Paper: §12.3, p. 514 and p. 520. For a centered rational radial profile on a
prime-free interval, the missing ordinary zero jets sum absolutely to the smoothed
diagonal minus the norm-one Tamagawa mass times the real gamma integral with both
scalar polar moments subtracted. -/
theorem rational_primeFree_boundedLog_missingJets_hasSum (g : ℝ → ℂ)
    (hg : ContDiff ℝ (∞) g) (hc : HasCompactSupport g) {a b α s : ℝ}
    (ha : 0 < a) (hb : b < Real.log 2) (hgI : tsupport g ⊆ Icc a b) (hα : 0 < α) (hs : 3 ≤ s)
    (U : ℕ → Set Cℚ) (hU : IsDPrimeSequence μℚ U) (hm : ∀ k, MeasurableSet (U k)) :
    type_of% realBalance(radialTest(g,hg,hc,hgI),ha,hb,hα,hs,U,hU,hm) :=
  realBalance(radialTest(g,hg,hc,hgI),ha,hb,hα,hs,U,hU,hm)

local notation "realCriterion(" a "," b "," ha "," hb "," hab "," hα "," hs "," hu "," U "," hU "," hm ")" =>
  rationalBoundedWindow_equality_iff hab hu (fun p : profiles(a,b) ↦
    rational_primeFree_boundedLog_missingJets_hasSum p.val p.property.1 p.property.2.1
      ha hb p.property.2.2 hα hs U hU hm)

/-- Paper: §12.3, p. 514 and (12.5.1.2)–(12.5.1.4), pp. 519–520. On one prime-free
logarithmic interval, the rational smoothed geometric diagonal equals the norm-one
volume times the real gamma integral minus the two Mellin moments (inside the volume
factor), for every radial test, exactly when all ordinary zeta multiplicities are
retained. The separation hypothesis is reciprocal summability over the omitted zeros. -/
theorem rational_primeFree_boundedLog_geometric_real_comparison_iff
    {a b α s : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < Real.log 2) (hα : 0 < α) (hs : 3 ≤ s)
    (hu : Summable (fun r : rationalWindowOmittedZeros α s ↦ 1 / (1 + |r.val.val.im|)))
    (U : ℕ → Set Cℚ) (hU : IsDPrimeSequence μℚ U) (hm : ∀ k, MeasurableSet (U k)) :
    type_of% realCriterion(a,b,ha,hb,hab,hα,hs,hu,U,hU,hm) :=
  realCriterion(a,b,ha,hb,hab,hα,hs,hu,U,hU,hm)

local notation "allReal(" ha "," hab "," hb "," hs "," hu "," U "," hU "," hm ")" =>
  rationalWindow_all_iff _ (fun α hα ↦
    rational_primeFree_boundedLog_geometric_real_comparison_iff ha hab hb hα hs (hu α hα) U hU hm)

/-- Paper: §12.3, p. 514 and p. 520. Under reciprocal summability of the omitted zeros
at each positive width, agreement on a single fixed prime-free interval with the real
gamma integral and the two Mellin moments, at every positive width, is equivalent to
the ordinary Riemann hypothesis. -/
theorem rational_allWidths_primeFree_boundedLog_geometric_real_comparison_iff_riemannHypothesis
    {a b s : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < Real.log 2) (hs : 3 ≤ s)
    (hu : ∀ α : ℝ, 0 < α →
      Summable (fun r : rationalWindowOmittedZeros α s ↦ 1 / (1 + |r.val.val.im|)))
    (U : ℕ → Set Cℚ) (hU : IsDPrimeSequence μℚ U) (hm : ∀ k, MeasurableSet (U k)) :
    type_of% allReal(ha,hab,hb,hs,hu,U,hU,hm) := allReal(ha,hab,hb,hs,hu,U,hU,hm)

end RiemannMasullo.StripNuclearity
