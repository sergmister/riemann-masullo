module

public import RiemannMasullo.Research.StripNuclearity.BoundedRealSeparation
public import RiemannMasullo.Research.StripNuclearity.RationalOmittedZeroDensity

/-! # A bare rational geometric diagonal criterion on one prime-free interval

For the real-place annihilating family all local terms and both polar
moments vanish. The remaining integral of the actual projected geometric
kernel therefore equals the omitted zeta-jet sum. Bounded-interval
separation gives an equivalence with ordinary RH when applied at every
positive strip width under the indicated reciprocal-summability condition.
-/

@[expose] public noncomputable section

open Function MeasureTheory NumberField Set
open scoped ContDiff NumberField.AdeleRing Topology
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
  spectralStripMultiplicity α s ((r : criticalStripZetaZeros).val.re-1/2) (zetaZeroOrder r)
local notation "missing(" α "," s "," r ")" => (zetaZeroOrder r - kept(α,s,r) : ℕ)
local notation "c(" α "," s "," r ")" => (Vℚ * (missing(α,s,(r).val) : ℂ))
local notation "radial(" φ "," g ")" => ∀ x : Cℚ, (φ : BruhatCompactSupport Cℚ).val x =
  rationalCenteredLogProfile g (Real.log (((ideleClassNorm ℚ) x).val : ℝ))
local notation "strong(" hs ")" => (lt_of_lt_of_le (Nat.one_lt_ofNat : (1 : ℝ) < 3) hs)
local notation "diagonal(" φ "," hα "," hs "," U ")" =>
  (∫ x : Cℚ, (fun y : Cℚ ↦ dSequenceKernelSmoothening μℚ U
    (globalStripGeometricKernel (F := ℚ) (1/2) (hα).le
      (lt_of_lt_of_le (b := (3 : ℝ)) Nat.one_lt_ofNat hs) φ
      (exists_numberField_projectiveKernel_comp_spectralProjection (F := ℚ) (le_of_lt hα) strong(hs) φ))
    (y,y)) x ∂μℚ)

private theorem hasSum_without_local_terms {ι : Type*} {T : ι → ℂ} {d w v A p q : ℂ}
    (h : HasSum T (d - w)) (hw : v * (A - p - q) = w) (hA : A = 0) (hp : p = 0)
    (hq : q = 0) : HasSum T d := by
  simpa only [← hw, hA, hp, hq, sub_zero, mul_zero] using h

/-- Paper: §12.3, p. 514, and (12.5.1.4), p. 520. On the real-place
annihilating family the sum over genuinely omitted zeta zeros equals the
actual smoothened rational geometric diagonal integral, at every positive
half-width and every Sobolev order at least three.
Deviation: This test family makes the local terms and both poles vanish.
Boundary multiplicity is the strict Sobolev truncation. -/
theorem rational_realAnnihilator_missingJets_hasSum (f : ℝ → ℂ) (hf : ContDiff ℝ (∞) f)
    (hc : HasCompactSupport f) {a b α s : ℝ} (ha : 0 < a) (hb : b < Real.log 2)
    (hI : tsupport f ⊆ Icc a b) (φ : BruhatCompactSupport Cℚ) (hφ : radial(φ,boundedRealAnnihilator f))
    (hα : 0 < α) (hs : 3 ≤ s) (U : ℕ → Set Cℚ) (hU : IsDPrimeSequence μℚ U)
    (hm : ∀ n, MeasurableSet (U n)) :
    HasSum (fun i : rationalWindowOmittedZeros α s ↦
      c(α,s,i) * compactLogMellin (boundedRealAnnihilator f) i.val.val) diagonal(φ,hα,hs,U) := by
  let g := boundedRealAnnihilator f
  change HasSum (fun i : rationalWindowOmittedZeros α s ↦ c(α,s,i) * compactLogMellin g i.val.val) _
  obtain ⟨hg, hcg, hsupp⟩ := boundedRealAnnihilator_regularity f hf hc
  have hI' : tsupport g ⊆ Icc a b := hsupp.trans hI
  obtain ⟨A, B, hA, hB⟩ := exists_rational_radial_place_tests g hg hcg φ hφ
  let chars := exists_spectralBasepointChoice_radially_trivial ℚ
  have hsum := (rational_radial_missingJets_hasSum_iff g φ hφ chars.choose chars.choose_spec.1 α s _).mp
    (integral_rational_window_eq_principalValues_sub_poles_add_missingJets
      g hg hcg ha hI' φ hφ A B hA hB hα hs U hU hm).2.1
  have hlocal := rational_prime_free_places_sub_global_poles g hg.continuous ha hb hI' φ hφ A B hA hB
  have hz := (rationalWeilLocalValue_eq_primeFree_realIntegral g hg hcg ha hb hI').trans
    (boundedRealAnnihilator_realIntegral f hf hc ha hI)
  have hp := boundedRealAnnihilator_polarMoments f hf hc
  have hbare := hasSum_without_local_terms hsum hlocal hz hp.1 hp.2
  exact (rationalWindow_omitted_hasSum_iff g α s _).mpr hbare

local notation "vanishes(" a "," b "," hα "," hs "," U ")" =>
  ∀ (f : ℝ → ℂ), ContDiff ℝ (∞) f → HasCompactSupport f → tsupport f ⊆ Icc a b →
    ∀ φ : BruhatCompactSupport Cℚ, radial(φ,boundedRealAnnihilator f) → diagonal(φ,hα,hs,U) = 0

/-- For a fixed width, the bare geometric diagonal vanishes on every member
of the annihilating family in one prime-free interval precisely when the
whole multiplicity of every ordinary zero is represented. Reciprocal
summability concerns only the omitted zero ordinates. -/
theorem rational_realAnnihilator_diagonal_zero_iff {a b α s : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b < Real.log 2) (hα : 0 < α) (hs : 3 ≤ s)
    (hu : Summable (fun i : rationalWindowOmittedZeros α s ↦ 1 / (1+|i.val.val.im|)))
    (U : ℕ → Set Cℚ) (hU : IsDPrimeSequence μℚ U) (hm : ∀ n, MeasurableSet (U n)) :
    (vanishes(a,b,hα,hs,U)) ↔ ∀ r : criticalStripZetaZeros, kept(α,s,r) = zetaZeroOrder r := by
  constructor
  · intro h r
    have hle : kept(α,s,r) ≤ zetaZeroOrder r := by
      unfold spectralStripMultiplicity spectralBoundaryMultiplicity
      split_ifs <;> first | exact le_rfl | exact min_le_left _ _ | exact Nat.zero_le _
    apply le_antisymm hle
    by_contra! hlt
    have hp : 0 < missing(α,s,r) := Nat.sub_pos_of_lt hlt
    let index (i : rationalWindowOmittedZeros α s) := i.val.val
    let coeff (i : rationalWindowOmittedZeros α s) := c(α,s,i)
    have hi : Function.Injective index := fun _ _ e ↦ Subtype.ext (Subtype.ext e)
    have hre (i : rationalWindowOmittedZeros α s) : (index i).re ∈ Ioo (0 : ℝ) 1 :=
      (mem_criticalStripZetaZeros.mp i.val.property).2
    have hrec : Summable (fun j : rationalWindowOmittedZeros α s ↦ 1/(1+|(index j-r.val).im|)) := by
      simpa only [index, Complex.sub_im] using
        summable_reciprocal_shift (fun i : rationalWindowOmittedZeros α s ↦ i.val.val.im) hu r.val.im
    have hcoeff := boundedWindow_realAnnihilator_coeff_eq_zero index hi hre coeff ⟨r,hp⟩ hrec hab
    apply (mul_ne_zero rationalNormOneTamagawaVolume_ne_zero (Nat.cast_ne_zero.mpr hp.ne'))
    apply hcoeff
    · intro f hf hc hI
      have hS := rational_primeFree_boundedLog_missingJets_hasSum f hf hc ha hb hI hα hs U hU hm
      exact ((rationalWindow_omitted_hasSum_iff f α s _).mpr hS).summable.norm
    · intro f hf hc hI
      obtain ⟨hd,hcg,-⟩ := boundedRealAnnihilator_regularity f hf hc
      obtain ⟨φ,hφ⟩ := exists_rationalCenteredNormTest _ hd hcg
      have hS := rational_realAnnihilator_missingJets_hasSum f hf hc ha hb hI φ hφ hα hs U hU hm
      rwa [h f hf hc hI φ hφ] at hS
  · intro h f hf hc hI φ hφ
    apply (rational_realAnnihilator_missingJets_hasSum f hf hc ha hb hI φ hφ hα hs U hU hm).unique
    have hzero : (fun i : rationalWindowOmittedZeros α s ↦
        c(α,s,i) * compactLogMellin (boundedRealAnnihilator f) i.val.val) = 0 := by
      funext i
      simp only [h i.val, Nat.sub_self, Nat.cast_zero, mul_zero, zero_mul, Pi.zero_apply]
    rw [hzero]
    exact hasSum_zero

/-- Paper: §12.3, p. 514, and (12.5.1.4), p. 520. Fix a nondegenerate log
interval strictly inside (0, log 2) and one Sobolev order at least three.
Vanishing of the actual rational projected geometric diagonal on the
annihilating family, for every positive half-width, is equivalent to ordinary
RH under reciprocal summability of each omitted zero set.
Deviation: The family has zero real principal value, zero finite-place
restrictions and zero polar moments. The equivalence is a test of the missing
operator comparison. -/
theorem rational_allWidths_realAnnihilator_diagonal_zero_iff_riemannHypothesis
    {a b s : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < Real.log 2) (hs : 3 ≤ s)
    (hu : ∀ α : ℝ, 0 < α → Summable (fun i : rationalWindowOmittedZeros α s ↦
      1/(1+|i.val.val.im|)))
    (U : ℕ → Set Cℚ) (hU : IsDPrimeSequence μℚ U) (hm : ∀ n, MeasurableSet (U n)) :
    (∀ α (hα : 0 < α), vanishes(a,b,hα,hs,U)) ↔ RiemannHypothesis :=
  rationalWindow_all_iff s fun α hα ↦ rational_realAnnihilator_diagonal_zero_iff
    ha hab hb hα hs (hu α hα) U hU hm

/-- A subquadratic dyadic counting bound at every positive width supplies the
reciprocal summability for the bare-diagonal criterion on a single interval. -/
theorem rational_allWidths_realAnnihilator_diagonal_zero_iff_riemannHypothesis_of_dyadicCount
    {a b s : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < Real.log 2) (hs : 3 ≤ s)
    (hcount : ∀ α : ℝ, 0 < α → RationalOmittedZeroDyadicBound α s)
    (U : ℕ → Set Cℚ) (hU : IsDPrimeSequence μℚ U) (hm : ∀ n, MeasurableSet (U n)) :
    (∀ α (hα : 0 < α), vanishes(a,b,hα,hs,U)) ↔ RiemannHypothesis :=
  rational_allWidths_realAnnihilator_diagonal_zero_iff_riemannHypothesis ha hab hb hs
    (fun α hα ↦ (hcount α hα).summable_reciprocal) U hU hm

end RiemannMasullo.StripNuclearity
