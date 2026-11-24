module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4
import RiemannMasullo.Research.TraceComparison.SLocalAnnularCutoff
import RiemannMasullo.Ch03_IdelicZeta.Sec1
import RiemannMasullo.ForMathlib.MeasureTheory.Measure.Haar.Units
import Mathlib.Topology.Algebra.IsOpenUnits
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.NumberTheory.NumberField.Discriminant.Different

/-! # Smooth upper cutoffs in the actual S-local trace kernel -/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped BigOperators ContDiff ENNReal NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

private theorem moving_threshold_fubini {X : Type*} [MeasurableSpace X] (μ : Measure X) [SFinite μ]
    (m : X → ℝ) (hm : Measurable m) (b : X → ℂ) (r : ℝ → ℝ) (hr : Measurable r)
    (ψ : ℝ → ℂ) (hψ : Integrable ψ) (B : ℝ) (hb : Integrable ({x | m x ≤ B}.indicator b) μ)
    (hB : ∀ u, ψ u ≠ 0 → r u ≤ B) :
    let φ (x : X) := (∫ u : ℝ, {u | m x ≤ r u}.indicator ψ u) * b x
    let a (u : ℝ) := ψ u * ∫ x, {x | m x ≤ r u}.indicator b x ∂μ
    Integrable φ μ ∧ Integrable a ∧ ∫ x, φ x ∂μ = ∫ u, a u := by
  intro φ a
  let E : Set (ℝ × X) := {p | m p.2 ≤ r p.1}
  let J := E.indicator (fun p : ℝ × X ↦ ψ p.1 * ({x | m x ≤ B}.indicator b) p.2)
  have hJ : Integrable J (volume.prod μ) :=
    (hψ.mul_prod hb).indicator (measurableSet_le (hm.comp measurable_snd) (hr.comp measurable_fst))
  have h₁ (u : ℝ) (x : X) : J (u,x) = ψ u * {x | m x ≤ r u}.indicator b x := by
    by_cases hx : m x ≤ r u
    · by_cases hu : ψ u = 0
      · simp [J,E,hx,hu]
      · have hle := hx.trans (hB u hu)
        simp [J,E,hx,hle]
    · simp [J,E,hx]
  have h₂ (u : ℝ) (x : X) : J (u,x) = {u | m x ≤ r u}.indicator ψ u * b x := by
    rw [h₁]
    by_cases hx : m x ≤ r u <;> simp [hx]
  have hx (x : X) : ∫ u, J (u,x) = φ x := by simp_rw [h₂,integral_mul_const]; rfl
  have hu (u : ℝ) : ∫ x, J (u,x) ∂μ = a u := by simp_rw [h₁,integral_const_mul]; rfl
  refine ⟨hJ.integral_prod_right.congr (.of_forall hx),
    hJ.integral_prod_left.congr (.of_forall hu), ?_⟩
  simpa only [hx,hu] using (integral_integral_swap (f := fun u x ↦ J (u,x)) hJ).symm

variable {F : Type*} [Field F] [NumberField F] {S : Finset (HeightOneSpectrum (𝓞 F))}
attribute [local instance] instSAdeleMeasurableSpaceSec1 instSIdeleLocallyCompactSec1
  instIdeleClassMeasurableSpaceSec1 instNormOneSIdeleQuotientMeasurableSpaceSec1
  instFiniteCompletionUnitsLocallyCompactSec4b instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1

set_option quotPrecheck false
local notation "Aₛ" => SAdeleRing F S
local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "Hₛ" => sProjectedDiagonal F S
local notation "μI" => sMultiplicativeTamagawaMeasure F S
local notation "ν" => sAdditiveTamagawaMeasure F S
local notation "νI" => (ν).comap (Units.val : Iₛ → Aₛ)
local notation "N(" x ")" => (((sIdeleNorm F S (x : Iₛ)).val : ℝ))
local notation "slab(" L ")" => {x : Iₛ | N(x) ≤ (L : ℝ)}
local notation "band(" L ")" => sLocalPWProductRegion (F := F) S L
local notation "oneOn(" B ")" => (B : Set _).indicator (fun _ ↦ (1 : ℂ))
local instance smoothUpperSIdeleT2 : T2Space Iₛ := (sIdeleGroup_description F S).2.1
local instance smoothUpperSIdeleBorel : BorelSpace Iₛ := sIdeleGroup_borelSpace

private theorem smooth_upper_sFinite : SFinite (νI) := by
  let : BorelSpace Aₛ := sAdeleRing_borelSpace
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let (w : InfinitePlace F) : MeasurableSpace w.Completion := borel _
  let (v : S) : MeasurableSpace (v.val.adicCompletion F) := borel _
  let (w : InfinitePlace F) : BorelSpace w.Completion := ⟨rfl⟩
  let (v : S) : BorelSpace (v.val.adicCompletion F) := ⟨rfl⟩
  let (w : InfinitePlace F) : (infiniteLocalAdditiveTamagawaMeasure F w).IsAddHaarMeasure := by
    by_cases h : w.IsReal
    · rw [infiniteLocalAdditiveTamagawaMeasure, dite_eq_left h]
      exact (InfinitePlace.Completion.ringEquivRealOfIsReal h).symm.toAddEquiv.isAddHaarMeasure_map volume
        (InfinitePlace.Completion.isometryEquivRealOfIsReal h).symm.continuous
        (InfinitePlace.Completion.isometryEquivRealOfIsReal h).continuous
    · let hw := InfinitePlace.not_isReal_iff_isComplex.mp h
      rw [infiniteLocalAdditiveTamagawaMeasure, dite_eq_right h]
      let : (2 • (volume : Measure ℂ)).IsAddHaarMeasure := by
        rw [show 2 • (volume : Measure ℂ) = (2 : ℝ≥0∞) • volume by simp [two_smul]]
        exact Measure.IsAddHaarMeasure.smul (μ := (volume : Measure ℂ)) (by norm_num) (by simp)
      exact (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm.toAddEquiv.isAddHaarMeasure_map _
        (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).symm.continuous
        (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).continuous
  let (v : S) : (finiteLocalAdditiveTamagawaMeasure F v.val).IsAddHaarMeasure :=
    finiteLocalAdditiveTamagawaMeasure_isAddHaar F v.val
  let : (Measure.pi (infiniteLocalAdditiveTamagawaMeasure F)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  let : (Measure.pi (fun v : S ↦ finiteLocalAdditiveTamagawaMeasure F v.val)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  let : (ν).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  let : SecondCountableTopology Aₛ := inferInstanceAs (SecondCountableTopology
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : SecondCountableTopology Iₛ := (sIdeleGroup_description F S).1.secondCountableTopology
  have ho : Topology.IsOpenEmbedding (Units.val : Iₛ → Aₛ) := IsOpenUnits.isOpenEmbedding_unitsVal
    (M := ((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F))
  let : IsFiniteMeasureOnCompacts (νI) := .comap' _ Units.continuous_val ho.measurableEmbedding
  infer_instance

/-- Average the sharp upper radius against a weight on its logarithmic displacement. -/
def sLocalTraceSmoothUpperCutoff (ψ : ℝ → ℂ) (L ε : ℝ) (x : Iₛ) : ℂ :=
  ∫ u : ℝ, {u | N(x) ≤ L * Real.exp (ε*u)}.indicator ψ u

/-- A smooth compact weight produces a genuinely smooth log-norm profile for
every positive transition width. It is the upper tail of the weight evaluated
at the rescaled displacement of log norm from the cutoff center. -/
theorem sLocalTraceSmoothUpperCutoff_smooth_logProfile
    (ψ : ℝ → ℂ) (hψ : ContDiff ℝ (∞) ψ) (hc : HasCompactSupport ψ)
    {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε) :
    ∃ G : ℝ → ℂ, ContDiff ℝ (∞) G ∧ (∀ t, G t = ∫ u in Ici ((t - Real.log L)/ε), ψ u) ∧
      ∀ x : Iₛ, sLocalTraceSmoothUpperCutoff ψ L ε x = G (Real.log N(x)) := by
  let P (t : ℝ) := ∫ u in (0 : ℝ)..t, ψ u
  have hp (t : ℝ) : HasDerivAt P (ψ t) t := (hψ.continuous.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hder : deriv P = ψ := funext fun t ↦ (hp t).deriv
  have hP : ContDiff ℝ (∞) P := contDiff_infty_iff_deriv.mpr
    ⟨fun t ↦ (hp t).differentiableAt, hder ▸ hψ⟩
  let H (y : ℝ) := ∫ u in Ici y, ψ u
  have hI : Integrable ψ := hψ.continuous.integrable_of_hasCompactSupport hc
  have hH : ContDiff ℝ (∞) H := by
    have he : H = (fun y ↦ (∫ u in Ici (0 : ℝ), ψ u) - P y) := by
      funext y
      have he := intervalIntegral.integral_Ici_sub_Ici' (a := (0 : ℝ)) (b := y) hI.integrableOn hI.integrableOn
      dsimp only [H,P]
      linear_combination -he
    rw [he]
    exact contDiff_const.sub hP
  refine ⟨fun t ↦ H ((t - Real.log L)/ε), hH.comp ((contDiff_id.sub contDiff_const).div_const ε),
    fun _ ↦ rfl, fun x ↦ ?_⟩
  have hx : 0 < N(x) := NNReal.coe_pos.mpr (Units.zero_lt _)
  have heq : {u : ℝ | N(x) ≤ L * Real.exp (ε*u)} = Ici ((Real.log N(x) - Real.log L)/ε) := by
    ext u
    change _ ≤ _ ↔ _ ≤ u
    rw [← Real.log_le_log_iff hx (mul_pos hL (Real.exp_pos _)), Real.log_mul hL.ne' (Real.exp_pos _).ne',
      Real.log_exp, div_le_iff₀ hε, mul_comm u ε]
    constructor <;> intro h <;> linarith
  rw [sLocalTraceSmoothUpperCutoff,heq,integral_indicator measurableSet_Ici]

/-- A nonnegative unit-integral smooth weight on the required displacement
interval exists. Its complex-valued embedding can be used in the orbital integral. -/
theorem exists_sLocalTraceSmoothUpperWeight :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ (∞) ψ ∧ HasCompactSupport ψ ∧
      tsupport ψ ⊆ Icc (-1) 1 ∧ (∀ u, 0 ≤ ψ u) ∧ ∫ u, ψ u = 1 := by
  let b : ContDiffBump (0 : ℝ) := ⟨1/4,1/2,by norm_num,by norm_num⟩
  refine ⟨b.normed volume,b.contDiff_normed,b.hasCompactSupport_normed,?_,b.nonneg_normed,b.integral_normed⟩
  rw [b.tsupport_normed_eq]
  intro x hx
  have h : |x| ≤ 1/2 := by simpa only [b,Metric.mem_closedBall,Real.dist_eq,sub_zero] using hx
  exact abs_le.mp (h.trans (by norm_num))

/-- For a nonnegative real weight of total mass one, every value of the
one-sided spatial symbol is a real number between zero and one. -/
theorem sLocalTraceSmoothUpperCutoff_unitInterval (ψ : ℝ → ℝ) (hψ : Integrable ψ)
    (hp : ∀ u, 0 ≤ ψ u) (h₁ : ∫ u, ψ u = 1) (L ε : ℝ) (x : Iₛ) :
    ∃ t : ℝ, t ∈ Icc (0 : ℝ) 1 ∧ sLocalTraceSmoothUpperCutoff (fun u ↦ (ψ u : ℂ)) L ε x = t := by
  let E := {u : ℝ | N(x) ≤ L * Real.exp (ε*u)}
  have hm : MeasurableSet E := measurableSet_le measurable_const (by fun_prop)
  refine ⟨∫ u in E, ψ u, ⟨setIntegral_nonneg hm (fun u _ ↦ hp u),
    (setIntegral_le_integral hψ (.of_forall hp)).trans h₁.le⟩, ?_⟩
  change (∫ u, E.indicator (fun u ↦ (ψ u : ℂ)) u) = _
  rw [integral_indicator hm,integral_complex_ofReal]

/-- The normalized smoothed upper cutoff is exactly one below the lower edge
of the multiplicative band and zero above its upper edge. -/
theorem sLocalTraceSmoothUpperCutoff_transition
    (ψ : ℝ → ℂ) (hs : tsupport ψ ⊆ Icc (-1) 1) (h₁ : ∫ u, ψ u = 1)
    {L : ℝ} (hL : 0 < L) (ε : ℝ) (x : Iₛ) :
    (N(x) ≤ L * Real.exp (-|ε|) → sLocalTraceSmoothUpperCutoff ψ L ε x = 1) ∧
    (L * Real.exp |ε| < N(x) → sLocalTraceSmoothUpperCutoff ψ L ε x = 0) := by
  let E := {u : ℝ | N(x) ≤ L * Real.exp (ε*u)}
  have hb (u : ℝ) (hu : ψ u ≠ 0) : |ε*u| ≤ |ε| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (abs_le.mpr (hs (subset_tsupport ψ (mem_support.mpr hu))))
  constructor
  · intro h
    apply Eq.trans _ h₁
    refine integral_congr_ae (.of_forall fun u ↦ ?_)
    change E.indicator ψ u = ψ u
    by_cases hu : ψ u = 0
    · exact indicator_apply_eq_self.mpr fun _ ↦ hu
    · exact indicator_of_mem (s := E)
        (h.trans (mul_le_mul_of_nonneg_left (Real.exp_monotone (abs_le.mp (hb u hu)).1) hL.le)) ψ
  · intro h
    change (∫ u : ℝ, E.indicator ψ u) = 0
    rw [← show (∫ _ : ℝ, (0 : ℂ)) = 0 by simp]
    refine integral_congr_ae (.of_forall fun u ↦ ?_)
    by_cases hu : ψ u = 0
    · exact (indicator_apply_eq_self.mpr fun _ ↦ hu).trans hu
    · exact indicator_of_notMem (s := E) (not_le.mpr ((mul_le_mul_of_nonneg_left
        (Real.exp_monotone (abs_le.mp (hb u hu)).2) hL.le).trans_lt h)) ψ

/-- Paper: Step II, pp. 517–518. In the actual cutoff kernel with sharp frequency
radius, a compactly weighted average of upper spatial cutoffs integrates on an
S-unit fundamental domain to the identical average of the evaluated sharp masses.
Deviation: This selects an explicit family of one-sided spatial cutoffs. -/
theorem sLocalTraceSmoothUpperCutoff_orbit_integral
    (f : BruhatCompactSupport Iₛ) (ξ : Hₛ) (D : Set Iₛ) (hD : IsFundamentalDomain Hₛ D μI)
    (ψ : ℝ → ℂ) (hψ : Integrable ψ) (hs : tsupport ψ ⊆ Icc (-1) 1)
    {L L' : ℝ} (hL : 0 < L) (hL' : 0 < L') (ε : ℝ) :
    let k (x : Iₛ) := sLocalTraceCutoffKernel f (sLocalTraceSmoothUpperCutoff ψ L ε)
      oneOn(band(L')) (ξ.val*x) x.val
    let a (u : ℝ) := ψ u * sLocalTraceSharpMass f ξ ((L * Real.exp (ε*u))*L')
    IntegrableOn k D νI ∧ Integrable a ∧ ∫ x in D, k x ∂νI = ∫ u, a u := by
  intro k a
  let := smooth_upper_sFinite (F := F) (S := S)
  let m (x : Iₛ) := N(x)
  let b (x : Iₛ) := sLocalTraceCutoffKernel f (fun _ ↦ 1) oneOn(band(L')) (ξ.val*x) x.val
  have hξ : (QuotientGroup.mk ξ.val : SIdeleQuotient F S) = 1 := (QuotientGroup.eq_one_iff _).mpr ξ.property
  have hnξ : sIdeleNorm F S ξ.val = 1 := (congrArg (sIdeleQuotientNorm F S) hξ).trans (map_one _)
  have hmx (x : Iₛ) : N(ξ.val*x) = m x := by simp only [m, map_mul, hnξ, one_mul]
  have hm : Measurable m := by
    have h := (isProperMap_sIdeleQuotientNorm F S).continuous.comp
      (QuotientGroup.continuous_mk (N := sProjectedDiagonal F S))
    exact (NNReal.continuous_coe.comp (Units.continuous_val.comp h)).measurable
  have hsharp (r : ℝ) (hr : 0 < r) :
      IntegrableOn ({x | m x ≤ r}.indicator b) D νI ∧
      (∫ x in D, {x | m x ≤ r}.indicator b x ∂νI) = sLocalTraceSharpMass f ξ (r * L') := by
    obtain ⟨hi,he⟩ := sLocalTraceSharpMass_eq_integral f ξ D hD r L' hr hL'
    let E := {x : Iₛ | m x ≤ r}
    have hE : MeasurableSet E := measurableSet_le hm measurable_const
    have heq (x : Iₛ) : sLocalTraceCutoffKernel f oneOn(slab(r)) oneOn(band(L')) (ξ.val*x) x.val =
        E.indicator b x := by
      change (if N(ξ.val*x) ≤ r then (1 : ℂ) else 0) * _ = _
      rw [hmx]
      by_cases hx : m x ≤ r <;> simp [E,hx,b,sLocalTraceCutoffKernel]
    simp_rw [heq] at hi he
    have hid : E.indicator (E.indicator b) = E.indicator b := by rw [indicator_indicator, inter_self]
    constructor
    · rw [← hid, integrableOn_indicator_iff hE.nullMeasurableSet, inter_comm]
      exact hi
    · rw [← hid, setIntegral_indicator hE]
      exact he
  let r (u : ℝ) := L * Real.exp (ε*u)
  let B := L * Real.exp |ε|
  have hb : 0 < B := mul_pos hL (Real.exp_pos _)
  have hdom (u : ℝ) (hu : ψ u ≠ 0) : r u ≤ B := by
    have hv := hs (subset_tsupport ψ (mem_support.mpr hu))
    apply mul_le_mul_of_nonneg_left _ hL.le
    apply Real.exp_monotone
    exact (le_abs_self _).trans (by rw [abs_mul]; exact
      (mul_le_of_le_one_right (abs_nonneg _) (abs_le.mpr hv)))
  obtain ⟨hk,hi,he⟩ := moving_threshold_fubini ((νI).restrict D) m hm b r (by dsimp [r]; fun_prop)
    ψ hψ B (hsharp B hb).1 hdom
  have hx (x : Iₛ) : k x = (∫ u : ℝ, {u | m x ≤ r u}.indicator ψ u) * b x := by
    simp only [k,b,sLocalTraceCutoffKernel,sLocalTraceSmoothUpperCutoff,hmx,r,one_mul]
  have hu (u : ℝ) : ψ u * (∫ x in D, {x | m x ≤ r u}.indicator b x ∂νI) = a u := by
    rw [(hsharp (r u) (mul_pos hL (Real.exp_pos _))).2]
  exact ⟨hk.congr (.of_forall fun x ↦ (hx x).symm), hi.congr (.of_forall hu), by
    simpa only [← hx, hu] using he⟩

/-- The sum of the integrated skew diagonals of the actual kernel with an averaged
upper spatial cutoff and a sharp frequency cutoff. -/
def sLocalTraceSmoothUpperOrbitSum (f : BruhatCompactSupport Iₛ) (D : Set Iₛ)
    (ψ : ℝ → ℂ) (L L' ε : ℝ) : ℂ :=
  ∑' ξ : Hₛ, ∫ x in D, sLocalTraceCutoffKernel f (sLocalTraceSmoothUpperCutoff ψ L ε)
    oneOn(band(L')) (ξ.val*x) x.val ∂νI

/-- For finite projected S-units the integrated sum is the weighted average of the
sum of sharp masses at the corresponding product radii. -/
theorem sLocalTraceSmoothUpperOrbitSum_eq_integral [Finite Hₛ]
    (f : BruhatCompactSupport Iₛ) (D : Set Iₛ) (hD : IsFundamentalDomain Hₛ D μI)
    (ψ : ℝ → ℂ) (hψ : Integrable ψ) (hs : tsupport ψ ⊆ Icc (-1) 1)
    {L L' : ℝ} (hL : 0 < L) (hL' : 0 < L') (ε : ℝ) :
    let a (u : ℝ) := ψ u * ∑' ξ : Hₛ, sLocalTraceSharpMass f ξ ((L*L') * Real.exp (ε*u))
    Integrable a ∧ sLocalTraceSmoothUpperOrbitSum f D ψ L L' ε = ∫ u, a u := by
  intro a
  let := Fintype.ofFinite Hₛ
  let b (ξ : Hₛ) (u : ℝ) := ψ u * sLocalTraceSharpMass f ξ ((L*Real.exp (ε*u))*L')
  have h (ξ : Hₛ) := sLocalTraceSmoothUpperCutoff_orbit_integral f ξ D hD ψ hψ hs hL hL' ε
  have hb (ξ : Hₛ) : Integrable (b ξ) := (h ξ).2.1
  have he (u : ℝ) : ∑ ξ, b ξ u = a u := by
    simp only [a,b,tsum_fintype,Finset.mul_sum,mul_right_comm L (Real.exp (ε*u)) L']
  refine ⟨(integrable_finsetSum Finset.univ fun ξ _ ↦ hb ξ).congr (.of_forall he), ?_⟩
  calc
    _ = ∑ ξ, ∫ u, b ξ u := by
      rw [sLocalTraceSmoothUpperOrbitSum,tsum_fintype]
      exact Finset.sum_congr rfl fun ξ _ ↦ (h ξ).2.2
    _ = ∫ u, ∑ ξ, b ξ u := (integral_finsetSum _ fun ξ _ ↦ hb ξ).symm
    _ = _ := integral_congr_ae (.of_forall he)

private theorem weighted_log_radius_tendsto {T : Type*} {l : Filter T} [l.IsCountablyGenerated]
    (ψ : ℝ → ℂ) (hψ : Integrable ψ) (hs : tsupport ψ ⊆ Icc (-1) 1) (h₁ : ∫ u, ψ u = 1)
    (M : ℝ → ℂ) {C : ℂ} (hC : Tendsto M atTop (𝓝 C))
    (R ε : T → ℝ) (hR : Tendsto R l atTop) {A : ℝ} (hε : ∀ᶠ t in l, |ε t| ≤ A)
    (hi : ∀ᶠ t in l, Integrable (fun u ↦ ψ u * M (R t * Real.exp (ε t*u)))) :
    Tendsto (fun t ↦ ∫ u, ψ u * M (R t * Real.exp (ε t*u))) l (𝓝 C) := by
  have hlow (t : T) (ht : |ε t| ≤ A) (htR : 0 ≤ R t) (u : ℝ) (hu : ψ u ≠ 0) :
      R t * Real.exp (-A) ≤ R t * Real.exp (ε t*u) := by
    have hu₁ := abs_le.mpr (hs (subset_tsupport ψ (mem_support.mpr hu)))
    have hav : |ε t*u| ≤ A := by
      rw [abs_mul]
      exact (mul_le_of_le_one_right (abs_nonneg _) hu₁).trans ht
    exact mul_le_mul_of_nonneg_left (Real.exp_monotone (abs_le.mp hav).1) htR
  have hR' := hR.atTop_mul_const (Real.exp_pos (-A))
  have hB := (Metric.tendsto_nhds.mp hC 1 one_pos).mono fun R h ↦
    norm_le_norm_add_const_of_dist_le h.le
  obtain ⟨B,hB⟩ := eventually_atTop.mp hB
  have h := tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := l)
    (F := fun t u ↦ ψ u * M (R t * Real.exp (ε t*u))) (f := fun u ↦ ψ u * C)
    (fun u ↦ ‖ψ u‖ * (‖C‖+1)) (hi.mono fun _ ht ↦ ht.aestronglyMeasurable) ?_
    (hψ.norm.mul_const _) ?_
  · simpa only [integral_mul_const,h₁,one_mul] using h
  · filter_upwards [hε,hR.eventually_ge_atTop 0,hR'.eventually_ge_atTop B] with t ht htR htB
    exact .of_forall fun u ↦ by
      by_cases hu : ψ u = 0
      · simp [hu]
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hB _ (htB.trans (hlow t ht htR u hu))) (norm_nonneg _)
  · exact .of_forall fun u ↦ by
      by_cases hu : ψ u = 0
      · simpa only [hu, zero_mul] using (tendsto_const_nhds (x := (0 : ℂ)) (f := l))
      · apply tendsto_const_nhds.mul
        apply hC.comp
        refine tendsto_atTop_mono' _ ?_ hR'
        filter_upwards [hε,hR.eventually_ge_atTop 0] with t ht htR
        exact hlow t ht htR u hu

/-- For finite projected S-units, a normalized spatial smoothing preserves any
finite limit of the sharp sum. It suffices for its log-transition width to stay
bounded while the product of the spatial and frequency radii tends to infinity. -/
theorem sLocalTraceSmoothUpperOrbitSum_tendsto [Finite Hₛ]
    (f : BruhatCompactSupport Iₛ) (D : Set Iₛ) (hD : IsFundamentalDomain Hₛ D μI)
    (ψ : ℝ → ℂ) (hψ : Integrable ψ) (hs : tsupport ψ ⊆ Icc (-1) 1) (h₁ : ∫ u, ψ u = 1)
    {C : ℂ} (hC : Tendsto (fun R : ℝ ↦ ∑' ξ : Hₛ, sLocalTraceSharpMass f ξ R) atTop (𝓝 C))
    {T : Type*} {l : Filter T} [l.IsCountablyGenerated]
    (L L' ε : T → ℝ) (hL : ∀ᶠ t in l, 0 < L t) (hL' : ∀ᶠ t in l, 0 < L' t)
    (hR : Tendsto (fun t ↦ L t*L' t) l atTop) {A : ℝ} (hε : ∀ᶠ t in l, |ε t| ≤ A) :
    Tendsto (fun t ↦ sLocalTraceSmoothUpperOrbitSum f D ψ (L t) (L' t) (ε t)) l (𝓝 C) := by
  have he := (hL.and hL').mono fun t ht ↦
    sLocalTraceSmoothUpperOrbitSum_eq_integral f D hD ψ hψ hs ht.1 ht.2 (ε t)
  exact (weighted_log_radius_tendsto ψ hψ hs h₁ _ hC _ _ hR hε (he.mono fun _ h ↦ h.1)).congr'
    (he.mono fun _ h ↦ h.2.symm)

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "vS" => ((sLocalNormOneQuotientMeasure F S) univ).toReal
local notation "arch(" w ")" => IdeleClassGroup.ofCompletion (𝓞 F) F w
local notation "fin(" v ")" => IdeleClassGroup.ofAdicCompletion (𝓞 F) F v
local notation "finVol(" v ")" => ((finiteLocalMultiplicativeTamagawaMeasure F v)
  (HeightOneSpectrum.adicCompletionIntegers F v).units).toReal
local notation "pv(" a "," b ")" => ((∑ w : InfinitePlace F, infiniteConnesWeilPrincipalValue w (a w)) +
  ∑ v : S, ((Real.log (v.val.asIdeal.absNorm : ℝ) / finVol(v.val) : ℝ) : ℂ) *
    finiteConnesWeilPrincipalValue v.val 1 (b v))

/-- Paper: Step II, pp. 517–519. For a global test vanishing at the identity and
a finite projected S-unit group, the actual smooth upper spatial cutoff against
a sharp Fourier band gives the local principal-value limit. This holds along
every path with diverging product radius and bounded log-transition width.
Deviation: This treats the explicit one-sided spatial cutoff, without a lower
spatial radius. -/
theorem sLocalTraceSmoothUpperOrbitSum_local_limit [Finite Hₛ]
    (φ : BruhatCompactSupport C𝔽) (hφ : φ.val 1 = 0)
    (hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F)))
    (hRam : ∀ v : V, differentIdeal ℤ (𝓞 F) ≤ v.asIdeal → v ∈ S)
    (hout : ∀ (u : outsideIntegralIdeleUnits F S) (x : C𝔽), φ.val (QuotientGroup.mk u.val*x) = φ.val x)
    (f : BruhatCompactSupport Iₛ) (hLift : ∀ x : Iₛ, HasSum (fun ξ : Hₛ ↦ f.val (ξ.val*x))
      (φ.val (QuotientGroup.mk (sIdeleInsertion F S x))))
    (D : Set Iₛ) (hD : IsFundamentalDomain Hₛ D μI)
    (ψ : ℝ → ℂ) (hd : ContDiff ℝ (∞) ψ) (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ Icc (-1) 1)
    (h₁ : ∫ u, ψ u = 1)
    {T : Type*} {l : Filter T} [l.IsCountablyGenerated]
    (L L' ε : T → ℝ) (hL : ∀ᶠ t in l, 0 < L t) (hL' : ∀ᶠ t in l, 0 < L' t)
    (hR : Tendsto (fun t ↦ L t*L' t) l atTop) {A : ℝ} (hε : ∀ᶠ t in l, |ε t| ≤ A) :
    ∃ (a : (w : InfinitePlace F) → BruhatCompactSupport w.Completionˣ)
      (b : (v : S) → BruhatCompactSupport (v.val.adicCompletion F)ˣ),
      (∀ w u, (a w).val u = φ.val (arch(w) u)) ∧ (∀ (v : S) u, (b v).val u = φ.val (fin(v.val) u)) ∧
      Tendsto (fun t ↦ sLocalTraceSmoothUpperOrbitSum f D ψ (L t) (L' t) (ε t)) l (𝓝 ((vS : ℂ) * pv(a,b))) := by
  obtain ⟨a,b,M,ha,hb,hM,hlim⟩ := sLocalTraceSharpMass_asymptotic φ hPic hRam hout f hLift
  simp only [hφ,mul_zero,zero_mul,sub_zero] at hlim
  have he := hlim.congr' (hM.mono fun _ h ↦ h.tsum_eq.symm)
  exact ⟨a,b,ha,hb,sLocalTraceSmoothUpperOrbitSum_tendsto f D hD ψ
    (hd.continuous.integrable_of_hasCompactSupport hc) hs h₁ he L L' ε hL hL' hR hε⟩

end RiemannMasullo

namespace RiemannMasullo

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped BigOperators ContDiff ENNReal NNReal NumberField.AdeleRing Topology

private theorem spatial_frequency_fubini {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (s : X → ℂ) (hs : Integrable s μ) (K : X × Y → ℂ) (hK : Measurable K) (C : ℝ)
    (hC : ∀ z, ‖K z‖ ≤ C) (m : Y → ℝ) (hm : Measurable m)
    (hfinite : ∀ r : ℝ, ν {y | m y ≤ r} ≠ ⊤)
    (r : ℝ → ℝ) (hr : Measurable r) (ψ : ℝ → ℂ) (hψ : Integrable ψ)
    (B : ℝ) (hB : ∀ u, ψ u ≠ 0 → r u ≤ B) :
    let a (x : X) := s x * ∫ y, (∫ v, {v | m y ≤ r v}.indicator ψ v) * K (x,y) ∂ν
    let b (v : ℝ) := ψ v * ∫ x, s x *
      (∫ y, {y | m y ≤ r v}.indicator (fun _ ↦ (1 : ℂ)) y * K (x,y) ∂ν) ∂μ
    Integrable a μ ∧ Integrable b ∧ ∫ x, a x ∂μ = ∫ v, b v := by
  intro a b
  let E (R : ℝ) := {y : Y | m y ≤ R}
  let U (R : ℝ) := {z : X × Y | m z.2 ≤ R}
  let k (z : X × Y) := s z.1 * K z
  let w (y : Y) := ∫ v, {v | m y ≤ r v}.indicator ψ v
  have hmE (R : ℝ) : MeasurableSet (E R) := measurableSet_le hm measurable_const
  have hcut (R : ℝ) : Integrable ((U R).indicator k) (μ.prod ν) := by
    let e := (E R).indicator (fun _ ↦ (1 : ℂ))
    have he : Integrable e ν := (integrable_indicator_iff (hmE R)).mpr
      (integrableOn_const (hfinite R))
    have hk := (hs.mul_prod he).smul_bdd C hK.aestronglyMeasurable (.of_forall hC)
    apply hk.congr (.of_forall fun z ↦ ?_)
    change s z.1 * e z.2 * K z = (U R).indicator k z
    by_cases hz : m z.2 ≤ R <;> simp [e,E,U,k,hz]
  obtain ⟨h₁,h₂,h₃⟩ := moving_threshold_fubini (μ.prod ν) (fun z : X × Y ↦ m z.2)
    (hm.comp measurable_snd) k r hr ψ hψ B (hcut B) hB
  have hx (x : X) : (∫ y, w y * k (x,y) ∂ν) = a x := by
    rw [show a x = s x * ∫ y, w y * K (x,y) ∂ν from rfl, ← integral_const_mul]
    exact integral_congr_ae (.of_forall fun y ↦ mul_left_comm _ _ _)
  have hv (v : ℝ) : ψ v * (∫ z, (U (r v)).indicator k z ∂μ.prod ν) = b v := by
    rw [integral_prod _ (hcut (r v))]
    apply congrArg (ψ v * ·)
    refine integral_congr_ae (.of_forall fun x ↦ ?_)
    change _ = s x * ∫ y, (E (r v)).indicator (fun _ ↦ (1 : ℂ)) y * K (x,y) ∂ν
    rw [← integral_const_mul]
    refine integral_congr_ae (.of_forall fun y ↦ ?_)
    by_cases hy : m y ≤ r v <;> simp [E,U,k,hy]
  have hI : Integrable (fun z : X × Y ↦ w z.2 * k z) (μ.prod ν) := h₁
  refine ⟨hI.integral_prod_left.congr (.of_forall hx), h₂.congr (.of_forall hv), ?_⟩
  calc
    _ = ∫ x, ∫ y, w y * k (x,y) ∂ν ∂μ := integral_congr_ae (.of_forall fun x ↦ (hx x).symm)
    _ = ∫ z, w z.2 * k z ∂μ.prod ν := (integral_prod _ hI).symm
    _ = _ := h₃.trans (integral_congr_ae (.of_forall hv))

section RationalFrequency

set_option quotPrecheck false
local notation "S₀" => (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))
local notation "A₀" => SAdeleRing ℚ S₀
local notation "I₀" => (SAdeleRing ℚ S₀)ˣ
local notation "H₀" => sProjectedDiagonal ℚ S₀
local notation "μ₀" => sMultiplicativeTamagawaMeasure ℚ S₀
local notation "ν₀" => sAdditiveTamagawaMeasure ℚ S₀
local notation "νᵤ" => (ν₀).comap (Units.val : I₀ → A₀)
local notation "wℝ" => Rat.infinitePlace
local notation "size(" y ")" => ‖(y : A₀).1 wℝ‖
local notation "B₀(" r ")" => sLocalPWProductRegion (F := ℚ) S₀ r
local notation "unitSlab(" r ")" => {x : I₀ | size(x.val) ≤ (r : ℝ)}
local notation "N₀(" x ")" => (((sIdeleNorm ℚ S₀ (x : I₀)).val : ℝ))
local notation "oneS(" B ")" => (B : Set _).indicator (fun _ ↦ (1 : ℂ))

attribute [local instance] instSAdeleMeasurableSpaceSec1 instSIdeleLocallyCompactSec1
  instFiniteCompletionUnitsLocallyCompactSec4b smoothUpperSIdeleT2 smoothUpperSIdeleBorel
local instance ratDoubleSBorel : BorelSpace A₀ := sAdeleRing_borelSpace
local instance ratDoubleCountable : SecondCountableTopology A₀ := by
  let j := InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace
  let e : A₀ ≃ₜ ℝ := ((Homeomorph.prodUnique _ _).trans
    (Homeomorph.piUnique fun v : InfinitePlace ℚ ↦ v.Completion)).trans j.toHomeomorph
  exact e.isEmbedding.secondCountableTopology

private theorem rationalFrequency_band (r : ℝ) : B₀(r) = {y : A₀ | size(y) ≤ r} := by
  ext y
  simp only [sLocalPWProductRegion, Fintype.prod_subsingleton _ wℝ,
    Rat.isReal_infinitePlace.mult_eq_one,pow_one, Fintype.prod_empty, mul_one]

private theorem rationalFrequency_unit_norm (x : I₀) : N₀(x) = size(x.val) := by
  simp [sIdeleNorm]
  rfl

private theorem rationalFrequency_compact_band (r : ℝ) :
    IsCompact {y : A₀ | size(y) ≤ r} := by
  let j := InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace
  let e : A₀ ≃ₜ Rat.infinitePlace.Completion := (Homeomorph.prodUnique _ _).trans (Homeomorph.piUnique fun v : InfinitePlace ℚ ↦ v.Completion)
  let : ProperSpace Rat.infinitePlace.Completion := LipschitzWith.properSpace
    j.toHomeomorph.isProperMap j.isometry.lipschitzWith
  have h := e.isProperMap.isCompact_preimage (isCompact_closedBall (0 : Rat.infinitePlace.Completion) r)
  have he : e ⁻¹' (Metric.closedBall (0 : Rat.infinitePlace.Completion) r) = {y : A₀ | size(y) ≤ r} := by
    ext y
    change dist (e y) 0 ≤ r ↔ _
    rw [dist_zero_right]
    rfl
  exact he ▸ h

private theorem rationalFrequency_addHaar : (ν₀).IsAddHaarMeasure := by
  let (w : InfinitePlace ℚ) : MeasurableSpace w.Completion := borel _
  let (v : S₀) : MeasurableSpace (v.val.adicCompletion ℚ) := borel _
  let (w : InfinitePlace ℚ) : BorelSpace w.Completion := ⟨rfl⟩
  let (v : S₀) : BorelSpace (v.val.adicCompletion ℚ) := ⟨rfl⟩
  let (w : InfinitePlace ℚ) : (infiniteLocalAdditiveTamagawaMeasure ℚ w).IsAddHaarMeasure := by
    obtain rfl := Subsingleton.elim w wℝ
    rw [infiniteLocalAdditiveTamagawaMeasure, dite_eq_left Rat.isReal_infinitePlace]
    exact (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).symm.toAddEquiv.isAddHaarMeasure_map
      volume (InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace).symm.continuous
      (InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace).continuous
  let (w : InfinitePlace ℚ) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let (v : S₀) : ProperSpace (v.val.adicCompletion ℚ) := properSpace_adicCompletion v.val
  let (v : S₀) : (finiteLocalAdditiveTamagawaMeasure ℚ v.val).IsAddHaarMeasure :=
    finiteLocalAdditiveTamagawaMeasure_isAddHaar ℚ v.val
  let : (Measure.pi (infiniteLocalAdditiveTamagawaMeasure ℚ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  let : (Measure.pi (fun v : S₀ ↦ finiteLocalAdditiveTamagawaMeasure ℚ v.val)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  exact Measure.prod.instIsAddHaarMeasure _ _

private theorem rationalFrequency_spatial_band (r : ℝ) : νᵤ (unitSlab(r)) ≠ ⊤ := by
  let := rationalFrequency_addHaar
  have ho : Topology.IsOpenEmbedding (Units.val : I₀ → A₀) := IsOpenUnits.isOpenEmbedding_unitsVal
    (M := ((w : InfinitePlace ℚ) → w.Completion) × ((v : S₀) → v.val.adicCompletion ℚ))
  rw [ho.measurableEmbedding.comap_apply]
  exact ((measure_mono (by rintro _ ⟨x,hx,rfl⟩; exact hx :
    Units.val '' unitSlab(r) ⊆ {y : A₀ | size(y) ≤ r})).trans_lt
    (rationalFrequency_compact_band r).measure_lt_top).ne

private def rationalSkewPhase (f : BruhatCompactSupport I₀) (ξ : H₀) (z : I₀ × A₀) : ℂ :=
  sLocalTraceDilationKernel f (fun y ↦ (sAdeleStandardCharacter ℚ S₀ ((y - z.1.val) * z.2) : ℂ))
    (ξ.val*z.1).val

private theorem rationalSkewPhase_bounds (f : BruhatCompactSupport I₀) (ξ : H₀) :
    Continuous (rationalSkewPhase f ξ) ∧ ∃ C : ℝ, ∀ z, ‖rationalSkewPhase f ξ z‖ ≤ C := by
  let := rationalFrequency_addHaar
  let : SecondCountableTopology I₀ := (sIdeleGroup_description ℚ S₀).1.secondCountableTopology
  let w (g : I₀) := f.val g / (Real.sqrt N₀(g) : ℂ)
  have hw : Integrable w μ₀ := (sLocalTraceDilationKernel_apply_zero f 0).1
  obtain ⟨e,he,_⟩ := sAdditiveTamagawaMeasure_selfDual ℚ S₀
  let χ := e (Multiplicative.ofAdd (1 : A₀))
  have he (z : A₀) : χ (Multiplicative.ofAdd z) = sAdeleStandardCharacter ℚ S₀ z := by
    simpa only [one_mul] using he 1 z
  have hc : Continuous fun z : A₀ ↦ (sAdeleStandardCharacter ℚ S₀ z : ℂ) := by
    simp_rw [← he]; exact continuous_subtype_val.comp ((map_continuous χ).comp continuous_ofAdd)
  let p (z : I₀ × A₀) (g : I₀) := (sAdeleStandardCharacter ℚ S₀
    (((g⁻¹).val * (ξ.val*z.1).val - z.1.val) * z.2) : ℂ)
  have hpc (z : I₀ × A₀) : Continuous (p z) := by
    apply hc.comp
    fun_prop
  have hpz (g : I₀) : Continuous fun z ↦ p z g := by
    apply hc.comp
    fun_prop
  have hb (z : I₀ × A₀) (g : I₀) : ‖w g * p z g‖ ≤ ‖w g‖ := by simp only [p,norm_mul,Circle.norm_coe,mul_one,le_refl]
  constructor
  · apply continuous_of_dominated (bound := fun g ↦ ‖w g‖)
      (fun z ↦ hw.aestronglyMeasurable.mul (hpc z).aestronglyMeasurable) (fun z ↦ .of_forall (hb z)) hw.norm
      (.of_forall fun g ↦ (hpz g).const_mul _)
  · exact ⟨∫ g, ‖w g‖ ∂μ₀, fun z ↦ norm_integral_le_of_norm_le hw.norm (.of_forall (hb z))⟩

/-- A compactly weighted average of rational, real-place sharp upper frequency
bands, in the actual additive adelic frequency variable. -/
def rationalSLocalSmoothFrequency (ψ : ℝ → ℂ) (L η : ℝ) (y : A₀) : ℂ :=
  ∫ v : ℝ, {v | size(y) ≤ L * Real.exp (η*v)}.indicator ψ v

/-- A nonnegative normalized weight gives a real-valued frequency cutoff
between zero and one at every rational real-place frequency. -/
theorem rationalSLocalSmoothFrequency_unitInterval (θ : ℝ → ℝ) (hθ : Integrable θ)
    (hp : ∀ v, 0 ≤ θ v) (h₁ : ∫ v, θ v = 1) (L η : ℝ) (y : A₀) :
    ∃ t : ℝ, t ∈ Icc (0 : ℝ) 1 ∧ rationalSLocalSmoothFrequency (fun v ↦ (θ v : ℂ)) L η y = t := by
  let E := {v : ℝ | size(y) ≤ L * Real.exp (η*v)}
  have hm : MeasurableSet E := measurableSet_le measurable_const (by fun_prop)
  refine ⟨∫ v in E, θ v, ⟨setIntegral_nonneg hm (fun v _ ↦ hp v),
    (setIntegral_le_integral hθ (.of_forall hp)).trans h₁.le⟩, ?_⟩
  change (∫ v, E.indicator (fun v ↦ (θ v : ℂ)) v) = _
  rw [integral_indicator hm, integral_complex_ofReal]

/-- In the canonical real coordinate the additive frequency symbol is a smooth
compactly supported function. It is identically one on an interval about zero,
including the point where the absolute value is not differentiable. -/
theorem rationalSLocalSmoothFrequency_smooth_realProfile
    (θ : ℝ → ℂ) (hd : ContDiff ℝ (∞) θ) (hc : HasCompactSupport θ)
    (hs : tsupport θ ⊆ Icc (-1) 1) (h₁ : ∫ v, θ v = 1) {L η : ℝ} (hL : 0 < L) (hη : 0 < η) :
    ∃ G : ℝ → ℂ, ContDiff ℝ (∞) G ∧ tsupport G ⊆ Icc (-(L*Real.exp |η|)) (L*Real.exp |η|) ∧
      (∀ t, |t| ≤ L*Real.exp (-|η|) → G t = 1) ∧
      ∀ y : A₀, rationalSLocalSmoothFrequency θ L η y =
        G (InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace (y.1 wℝ)) := by
  let G (t : ℝ) := ∫ v : ℝ, {v | |t| ≤ L * Real.exp (η*v)}.indicator θ v
  let δ := L*Real.exp (-|η|)
  have hδ : 0 < δ := mul_pos hL (Real.exp_pos _)
  have hdisp (v : ℝ) (hv : θ v ≠ 0) : |η*v| ≤ |η| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (abs_le.mpr (hs (subset_tsupport θ (mem_support.mpr hv))))
  have hlo (t : ℝ) (ht : |t| ≤ δ) : G t = 1 := by
    rw [← h₁]
    apply integral_congr_ae (.of_forall fun v ↦ ?_)
    by_cases hv : θ v = 0
    · simp only [Set.indicator_apply, hv, ite_self]
    · exact indicator_of_mem (ht.trans (mul_le_mul_of_nonneg_left
        (Real.exp_monotone (abs_le.mp (hdisp v hv)).1) hL.le)) θ
  obtain ⟨H,hH,heH,_⟩ := sLocalTraceSmoothUpperCutoff_smooth_logProfile (F := ℚ) (S := S₀) θ hd hc hL hη
  have hne (t : ℝ) (ht : t ≠ 0) : G t = H (Real.log |t|) := by
    have hpre : {v : ℝ | |t| ≤ L * Real.exp (η*v)} = Ici ((Real.log |t| - Real.log L)/η) := by
      ext v
      change _ ≤ _ ↔ _ ≤ v
      rw [← Real.log_le_log_iff (abs_pos.mpr ht) (mul_pos hL (Real.exp_pos _)),
        Real.log_mul hL.ne' (Real.exp_pos _).ne', Real.log_exp, div_le_iff₀ hη, mul_comm v η]
      constructor <;> intro h <;> linarith
    rw [heH]
    dsimp only [G]
    rw [hpre,integral_indicator measurableSet_Ici]
  refine ⟨G,contDiff_iff_contDiffAt.mpr (fun t ↦ ?_),closure_minimal ?_ isClosed_Icc,hlo,fun y ↦ ?_⟩
  · by_cases ht : t = 0
    · subst t
      refine (contDiffAt_const (c := (1 : ℂ))).congr_of_eventuallyEq ?_
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with u hu
      exact hlo u (le_of_lt (by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using hu))
    · exact (hH.contDiffAt.comp t ((Real.contDiffAt_log.mpr (abs_ne_zero.mpr ht)).comp t
        (contDiffAt_abs ht))).congr_of_eventuallyEq ((eventually_ne_nhds ht).mono fun u hu ↦ hne u hu)
  · intro t ht
    apply abs_le.mp
    by_contra! hn
    apply ht
    apply integral_eq_zero_of_ae (.of_forall fun v ↦ ?_)
    change {v : ℝ | |t| ≤ L * Real.exp (η*v)}.indicator θ v = 0
    by_cases hv : θ v = 0
    · simp only [Set.indicator_apply, hv, ite_self]
    · apply indicator_of_notMem
      exact not_le.mpr ((mul_le_mul_of_nonneg_left (Real.exp_monotone (abs_le.mp (hdisp v hv)).2) hL.le).trans_lt hn)
  · let j := InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace
    have hy : |j (y.1 wℝ)| = size(y) := by
      rw [← Real.norm_eq_abs, j.isometry.norm_map_of_map_zero
        (map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace))]
    change _ = ∫ v : ℝ, {v | |j (y.1 wℝ)| ≤ L*Real.exp (η*v)}.indicator θ v
    rw [hy]
    rfl

/-- Paper: Step II, pp. 517–518. Over the rational field with no finite place, smoothing
both upper radii in the actual S-local cutoff kernel averages the evaluated sharp mass
over both product radii. The averaging measures are the indicated test weights on log
displacements.
Deviation: This chooses explicit one-sided smooth cutoffs in space and frequency. -/
theorem rationalSLocalSmoothFrequency_orbit_integral
    (f : BruhatCompactSupport I₀) (ξ : H₀) (D : Set I₀) (hD : IsFundamentalDomain H₀ D μ₀)
    (ψ θ : ℝ → ℂ) (hd : ContDiff ℝ (∞) ψ) (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ Icc (-1) 1)
    (h₁ : ∫ u, ψ u = 1) (hθ : Integrable θ) (ht : tsupport θ ⊆ Icc (-1) 1)
    {L L' ε : ℝ} (hL : 0 < L) (hL' : 0 < L') (hε : 0 < ε) (η : ℝ) :
    let k (x : I₀) := sLocalTraceCutoffKernel f (sLocalTraceSmoothUpperCutoff ψ L ε)
      (rationalSLocalSmoothFrequency θ L' η) (ξ.val*x) x.val
    let a (v : ℝ) := θ v * ∫ u, ψ u * sLocalTraceSharpMass f ξ
      ((L * Real.exp (ε*u)) * (L' * Real.exp (η*v)))
    IntegrableOn k D νᵤ ∧ Integrable a ∧ ∫ x in D, k x ∂νᵤ = ∫ v, a v := by
  intro k a
  let := rationalFrequency_addHaar
  let := smooth_upper_sFinite (F := ℚ) (S := S₀)
  let : LocallyCompactSpace A₀ := inferInstanceAs (LocallyCompactSpace
    (((w : InfinitePlace ℚ) → w.Completion) × ((v : S₀) → v.val.adicCompletion ℚ)))
  let s (x : I₀) := sLocalTraceSmoothUpperCutoff ψ L ε (ξ.val*x)
  let r (v : ℝ) := L' * Real.exp (η*v)
  have hmod (x : I₀) : N₀(ξ.val*x) = size(x.val) := by
    have hξ : (QuotientGroup.mk ξ.val : SIdeleQuotient ℚ S₀) = 1 := (QuotientGroup.eq_one_iff _).mpr ξ.property
    have hn : sIdeleNorm ℚ S₀ ξ.val = 1 := (congrArg (sIdeleQuotientNorm ℚ S₀) hξ).trans (map_one _)
    rw [map_mul,hn,one_mul,rationalFrequency_unit_norm]
  have hψ : Integrable ψ := hd.continuous.integrable_of_hasCompactSupport hc
  obtain ⟨G,hG,_,heG⟩ := sLocalTraceSmoothUpperCutoff_smooth_logProfile (F := ℚ) (S := S₀) ψ hd hc hL hε
  have hsize : Continuous fun y : A₀ ↦ size(y) := ((continuous_apply wℝ).comp continuous_fst).norm
  have hme : Measurable fun x : I₀ ↦ size(x.val) := (hsize.comp Units.continuous_val).measurable
  have hS : Measurable s := by
    have he (x : I₀) : s x = G (Real.log size(x.val)) := by rw [← hmod x]; exact heG _
    simp_rw [show s = fun x : I₀ ↦ G (Real.log size(x.val)) from funext he]
    exact hG.continuous.measurable.comp (Real.measurable_log.comp hme)
  have hiS : Integrable s ((νᵤ).restrict D) := by
    let R := L * Real.exp |ε|
    let M := ∫ u, ‖ψ u‖
    have hmeR : MeasurableSet unitSlab(R) := measurableSet_le hme measurable_const
    have hfR : (νᵤ).restrict D (unitSlab(R)) ≠ ⊤ :=
      ((Measure.restrict_apply_le D _).trans_lt (lt_top_iff_ne_top.mpr (rationalFrequency_spatial_band R))).ne
    have hiR : Integrable ((unitSlab(R)).indicator (fun _ ↦ M)) ((νᵤ).restrict D) :=
      (integrable_indicator_iff hmeR).mpr (integrableOn_const hfR)
    apply hiR.mono' hS.aestronglyMeasurable (.of_forall fun x ↦ ?_)
    by_cases hx : x ∈ unitSlab(R)
    · rw [indicator_of_mem hx]
      apply norm_integral_le_of_norm_le hψ.norm (.of_forall fun u ↦ ?_)
      exact norm_indicator_le_norm_self ψ u
    · have hlt : L * Real.exp |ε| < N₀(ξ.val*x) := by rw [hmod]; exact lt_of_not_ge hx
      rw [indicator_of_notMem hx, show s x = 0 from
        (sLocalTraceSmoothUpperCutoff_transition ψ hs h₁ hL ε (ξ.val*x)).2 hlt, norm_zero]
  obtain ⟨hK,C,hC⟩ := rationalSkewPhase_bounds f ξ
  have hFF := spatial_frequency_fubini ((νᵤ).restrict D) ν₀ s hiS (rationalSkewPhase f ξ) hK.measurable C hC
    (fun y : A₀ ↦ size(y)) hsize.measurable (fun R ↦ (rationalFrequency_compact_band R).measure_lt_top.ne)
    r (by dsimp [r]; fun_prop) θ hθ (L' * Real.exp |η|) (fun v hv ↦ by
      apply mul_le_mul_of_nonneg_left _ hL'.le
      apply Real.exp_monotone
      apply (le_abs_self _).trans
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (abs_le.mpr (ht (subset_tsupport θ (mem_support.mpr hv)))))
  have hv (v : ℝ) : θ v * (∫ x in D, s x *
      (∫ y : A₀, oneS({y : A₀ | size(y) ≤ r v}) y * rationalSkewPhase f ξ (x,y) ∂ν₀) ∂νᵤ) = a v := by
    rw [← rationalFrequency_band (r v)]
    apply congrArg (θ v * ·)
    exact (sLocalTraceSmoothUpperCutoff_orbit_integral f ξ D hD ψ hψ hs hL
      (mul_pos hL' (Real.exp_pos (η*v))) ε).2.2
  exact ⟨hFF.1, hFF.2.1.congr (.of_forall hv), hFF.2.2.trans (integral_congr_ae (.of_forall hv))⟩

/-- The orbital sum for the two explicit upper symbols, integrated in the
actual additive measure pulled back to the unit group. -/
def rationalSLocalSmoothDoubleOrbitSum (f : BruhatCompactSupport I₀) (D : Set I₀)
    (ψ θ : ℝ → ℂ) (L L' ε η : ℝ) : ℂ :=
  ∑' ξ : H₀, ∫ x in D, sLocalTraceCutoffKernel f (sLocalTraceSmoothUpperCutoff ψ L ε)
    (rationalSLocalSmoothFrequency θ L' η) (ξ.val*x) x.val ∂νᵤ

/-- After summing the rational projected units, frequency smoothing averages
the spatially smoothed trace evaluated at displaced frequency radii. -/
theorem rationalSLocalSmoothDoubleOrbitSum_eq_integral
    (f : BruhatCompactSupport I₀) (D : Set I₀) (hD : IsFundamentalDomain H₀ D μ₀)
    (ψ θ : ℝ → ℂ) (hd : ContDiff ℝ (∞) ψ) (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ Icc (-1) 1)
    (h₁ : ∫ u, ψ u = 1) (hθ : Integrable θ) (ht : tsupport θ ⊆ Icc (-1) 1)
    {L L' ε : ℝ} (hL : 0 < L) (hL' : 0 < L') (hε : 0 < ε) (η : ℝ) :
    let a (v : ℝ) := θ v * sLocalTraceSmoothUpperOrbitSum f D ψ L (L' * Real.exp (η*v)) ε
    Integrable a ∧ rationalSLocalSmoothDoubleOrbitSum f D ψ θ L L' ε η = ∫ v, a v := by
  intro a
  let := finite_rational_empty_sProjectedDiagonal
  let := Fintype.ofFinite H₀
  let b (ξ : H₀) (v : ℝ) := θ v * ∫ u, ψ u * sLocalTraceSharpMass f ξ
    ((L * Real.exp (ε*u)) * (L' * Real.exp (η*v)))
  have h (ξ : H₀) := rationalSLocalSmoothFrequency_orbit_integral f ξ D hD ψ θ hd hc hs h₁ hθ ht hL hL' hε η
  have hb (ξ : H₀) : Integrable (b ξ) := (h ξ).2.1
  have he (v : ℝ) : ∑ ξ, b ξ v = a v := by
    simp only [a,b,sLocalTraceSmoothUpperOrbitSum,tsum_fintype,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ξ _
    apply congrArg (θ v * ·)
    exact (sLocalTraceSmoothUpperCutoff_orbit_integral f ξ D hD ψ
      (hd.continuous.integrable_of_hasCompactSupport hc) hs hL (mul_pos hL' (Real.exp_pos _)) ε).2.2.symm
  refine ⟨(integrable_finsetSum Finset.univ fun ξ _ ↦ hb ξ).congr (.of_forall he), ?_⟩
  calc
    _ = ∑ ξ, ∫ v, b ξ v := by
      rw [rationalSLocalSmoothDoubleOrbitSum,tsum_fintype]
      exact Finset.sum_congr rfl fun ξ _ ↦ (h ξ).2.2
    _ = ∫ v, ∑ ξ, b ξ v := (integral_finsetSum _ fun ξ _ ↦ hb ξ).symm
    _ = _ := integral_congr_ae (.of_forall he)

private theorem integral_weighted_family_tendsto {T : Type*} {l : Filter T} [l.IsCountablyGenerated]
    (θ : ℝ → ℂ) (hθ : Integrable θ) (ht : tsupport θ ⊆ Icc (-1) 1) (h₁ : ∫ v, θ v = 1)
    (P : T → ℝ → ℂ) {C : ℂ} (hP : ∀ v : T → ℝ, (∀ t, |v t| ≤ 1) →
      Tendsto (fun t ↦ P t (v t)) l (𝓝 C))
    (hi : ∀ᶠ t in l, Integrable fun v ↦ θ v * P t v) :
    Tendsto (fun t ↦ ∫ v, θ v * P t v) l (𝓝 C) := by
  classical
  let bad (t : T) := ∃ v : ℝ, |v| ≤ 1 ∧ ‖C‖+1 < ‖P t v‖
  let p (t : T) := if h : bad t then h.choose else 0
  have hp (t : T) : |p t| ≤ 1 := by
    dsimp only [p]
    split_ifs with h
    · exact h.choose_spec.1
    · norm_num
  have hB := (Metric.tendsto_nhds.mp (hP p hp) 1 one_pos).mono fun t h ↦
    norm_le_norm_add_const_of_dist_le h.le
  have hu : ∀ᶠ t in l, ∀ v : ℝ, |v| ≤ 1 → ‖P t v‖ ≤ ‖C‖+1 := by
    filter_upwards [hB] with t h v hv
    by_contra! hn
    have hb : bad t := ⟨v,hv,hn⟩
    rw [show p t = hb.choose from dite_eq_left hb] at h
    exact hb.choose_spec.2.not_ge h
  have h := tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := l)
    (F := fun t v ↦ θ v * P t v) (f := fun v ↦ θ v * C) (fun v ↦ ‖θ v‖*(‖C‖+1))
    (hi.mono fun _ hh ↦ hh.aestronglyMeasurable) ?_ (hθ.norm.mul_const _) ?_
  · simpa only [integral_mul_const,h₁,one_mul] using h
  · filter_upwards [hu] with t h
    exact .of_forall fun v ↦ by
      by_cases hv : θ v = 0
      · simp [hv]
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (h v (abs_le.mpr (ht (subset_tsupport θ (mem_support.mpr hv))))) (norm_nonneg _)
  · exact .of_forall fun v ↦ by
      by_cases hv : θ v = 0
      · simpa only [hv,zero_mul] using (tendsto_const_nhds (x := (0 : ℂ)) (f := l))
      · exact tendsto_const_nhds.mul (hP (fun _ ↦ v) fun _ ↦ abs_le.mpr (ht (subset_tsupport θ (mem_support.mpr hv))))

/-- A finite sharp-mass limit is preserved by simultaneous normalized smoothing
of the two upper cutoffs. Both logarithmic widths can vary along the path and
stay bounded, while the product of the two radii tends to infinity. -/
theorem rationalSLocalSmoothDoubleOrbitSum_tendsto
    (f : BruhatCompactSupport I₀) (D : Set I₀) (hD : IsFundamentalDomain H₀ D μ₀)
    (ψ θ : ℝ → ℂ) (hd : ContDiff ℝ (∞) ψ) (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ Icc (-1) 1)
    (h₁ : ∫ u, ψ u = 1) (hθ : Integrable θ) (ht : tsupport θ ⊆ Icc (-1) 1) (h₂ : ∫ v, θ v = 1)
    {C : ℂ} (hC : Tendsto (fun R : ℝ ↦ ∑' ξ : H₀, sLocalTraceSharpMass f ξ R) atTop (𝓝 C))
    {T : Type*} {l : Filter T} [l.IsCountablyGenerated]
    (L L' ε η : T → ℝ) (hL : ∀ᶠ t in l, 0 < L t) (hL' : ∀ᶠ t in l, 0 < L' t)
    (hR : Tendsto (fun t ↦ L t*L' t) l atTop) (he : ∀ᶠ t in l, 0 < ε t)
    {A B : ℝ} (hε : ∀ᶠ t in l, |ε t| ≤ A) (hη : ∀ᶠ t in l, |η t| ≤ B) :
    Tendsto (fun t ↦ rationalSLocalSmoothDoubleOrbitSum f D ψ θ (L t) (L' t) (ε t) (η t)) l (𝓝 C) := by
  let := finite_rational_empty_sProjectedDiagonal
  let P (t : T) (v : ℝ) := sLocalTraceSmoothUpperOrbitSum f D ψ (L t) (L' t*Real.exp (η t*v)) (ε t)
  have hP (v : T → ℝ) (hv : ∀ t, |v t| ≤ 1) : Tendsto (fun t ↦ P t (v t)) l (𝓝 C) := by
    apply sLocalTraceSmoothUpperOrbitSum_tendsto f D hD ψ (hd.continuous.integrable_of_hasCompactSupport hc)
      hs h₁ hC L (fun t ↦ L' t * Real.exp (η t*v t)) ε hL
      (hL'.mono fun t ht ↦ mul_pos ht (Real.exp_pos _)) _ hε
    apply tendsto_atTop_mono' _ _ (hR.atTop_mul_const (Real.exp_pos (-B)))
    filter_upwards [hη, hR.eventually_ge_atTop 0] with t hηt ht
    have hw : |η t*v t| ≤ B := by
      rw [abs_mul]
      exact (mul_le_of_le_one_right (abs_nonneg _) (hv t)).trans hηt
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (Real.exp_monotone (abs_le.mp hw).1) ht
  have H := (hL.and (hL'.and he)).mono fun t h ↦ rationalSLocalSmoothDoubleOrbitSum_eq_integral
    f D hD ψ θ hd hc hs h₁ hθ ht h.1 h.2.1 h.2.2 (η t)
  exact (integral_weighted_family_tendsto θ hθ ht h₂ P hP (H.mono fun _ h ↦ h.1)).congr'
    (H.mono fun _ h ↦ h.2.symm)

local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "v₀" => ((sLocalNormOneQuotientMeasure ℚ S₀) univ).toReal

attribute [local instance] instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1
  instIdeleClassMeasurableSpaceSec1 instNormOneSIdeleQuotientMeasurableSpaceSec1

/-- Paper: Step II, pp. 517–519. For a rational test vanishing at the identity
and descending through the outside integral units, the doubly smoothed actual
orbital integral tends to the real-place principal value times the norm-one
quotient volume. The cutoffs may have independent bounded logarithmic widths.
Deviation: This compares two explicit upper symbols with the sharp S-local
integral. The Hilbert-space Paley–Wiener projection on p. 514 is a separate
operator. -/
theorem rationalSLocalSmoothDoubleOrbitSum_local_limit
    (φ : BruhatCompactSupport Cℚ) (hφ : φ.val 1 = 0)
    (hout : ∀ (u : outsideIntegralIdeleUnits ℚ S₀) (x : Cℚ),
      φ.val (QuotientGroup.mk u.val*x) = φ.val x)
    (f : BruhatCompactSupport I₀) (hLift : ∀ x : I₀, HasSum (fun ξ : H₀ ↦ f.val (ξ.val*x))
      (φ.val (QuotientGroup.mk (sIdeleInsertion ℚ S₀ x))))
    (D : Set I₀) (hD : IsFundamentalDomain H₀ D μ₀)
    (ψ θ : ℝ → ℂ) (hd : ContDiff ℝ (∞) ψ) (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ Icc (-1) 1)
    (h₁ : ∫ u, ψ u = 1) (hθ : Integrable θ) (ht : tsupport θ ⊆ Icc (-1) 1) (h₂ : ∫ v, θ v = 1)
    {T : Type*} {l : Filter T} [l.IsCountablyGenerated]
    (L L' ε η : T → ℝ) (hL : ∀ᶠ t in l, 0 < L t) (hL' : ∀ᶠ t in l, 0 < L' t)
    (hR : Tendsto (fun t ↦ L t*L' t) l atTop) (he : ∀ᶠ t in l, 0 < ε t)
    {A B : ℝ} (hε : ∀ᶠ t in l, |ε t| ≤ A) (hη : ∀ᶠ t in l, |η t| ≤ B) :
    ∃ a : BruhatCompactSupport Rat.infinitePlace.Completionˣ,
      (∀ u, a.val u = φ.val (IdeleClassGroup.ofCompletion (𝓞 ℚ) ℚ wℝ u)) ∧
      Tendsto (fun t ↦ rationalSLocalSmoothDoubleOrbitSum f D ψ θ (L t) (L' t) (ε t) (η t)) l
        (𝓝 ((v₀ : ℂ) * infiniteConnesWeilPrincipalValue wℝ a)) := by
  have hPic : Subsingleton (CommRing.Pic ((S₀ : Set (HeightOneSpectrum (𝓞 ℚ))).integer ℚ)) := by
    rw [Finset.coe_empty, integer_empty]
    let e := (Algebra.botEquivOfInjective (IsFractionRing.injective (𝓞 ℚ) ℚ)).toRingEquiv
    let i := Rat.ringOfIntegersEquiv.symm.trans e.symm
    let := IsPrincipalIdealRing.of_surjective i i.surjective
    infer_instance
  have hRam (v : HeightOneSpectrum (𝓞 ℚ)) (h : differentIdeal ℤ (𝓞 ℚ) ≤ v.asIdeal) : v ∈ S₀ := by
    have hd : differentIdeal ℤ (𝓞 ℚ) = ⊤ := by
      rw [← Ideal.absNorm_eq_one_iff, NumberField.absNorm_differentIdeal ℚ (𝓞 ℚ), NumberField.discr_rat]
      rfl
    exact (v.isPrime.ne_top (top_unique (hd ▸ h))).elim
  obtain ⟨a,b,M,ha,_,hM,hlim⟩ := sLocalTraceSharpMass_asymptotic φ hPic hRam hout f hLift
  simp only [hφ,mul_zero,zero_mul,sub_zero,Fintype.sum_empty,add_zero,Fintype.sum_subsingleton _ wℝ] at hlim
  exact ⟨a wℝ,ha wℝ,rationalSLocalSmoothDoubleOrbitSum_tendsto f D hD ψ θ hd hc hs h₁ hθ ht h₂
    (hlim.congr' (hM.mono fun _ h ↦ h.tsum_eq.symm)) L L' ε η hL hL' hR he hε hη⟩

end RationalFrequency
end RiemannMasullo
