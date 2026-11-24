module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4
import all RiemannMasullo.Ch12_TraceGeometric.Sec4

/-! # An independent lower spatial cutoff in the S-local trace

The lower radius in the footnote on p. 514 couples to the upper Fourier
radius. An annular spatial cutoff subtracts an entire second sharp orbital
mass. This makes the relative rate of the two cutoffs relevant.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped ENNReal NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

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
local instance annularSIdeleT2 : T2Space Iₛ := (sIdeleGroup_description F S).2.1
local instance annularSIdeleBorel : BorelSpace Iₛ := sIdeleGroup_borelSpace

private theorem upper_cutoff_on_domain (f : BruhatCompactSupport Iₛ) (ξ : Hₛ)
    (D : Set Iₛ) (hD : IsFundamentalDomain Hₛ D μI) {L L' : ℝ} (hL : 0 < L) (hL' : 0 < L') :
    let k := fun x : Iₛ ↦ sLocalTraceCutoffKernel f oneOn(slab(L)) oneOn(band(L')) (ξ.val*x) x.val
    IntegrableOn k D νI ∧ ∫ x in D, k x ∂νI = sLocalTraceSharpMass f ξ (L*L') := by
  intro k
  obtain ⟨hi, he⟩ := sLocalTraceSharpMass_eq_integral f ξ D hD L L' hL hL'
  have hμ : MeasurableSet slab(L) := measurableSet_le
    ((NNReal.continuous_coe.comp (Units.continuous_val.comp sLocalTrace_sIdeleNorm_continuous)).measurable)
    measurable_const
  have hk : (slab(L)).indicator k = k := by
    funext x
    by_cases hx : x ∈ slab(L)
    · exact indicator_of_mem hx _
    · rw [indicator_of_notMem hx]
      have hn : ξ.val * x ∉ slab(L) := by
        change ¬ N(ξ.val * x) ≤ L
        rw [map_mul, sLocalTrace_unit_norm ξ, one_mul]
        exact hx
      simp only [k,sLocalTraceCutoffKernel,indicator_of_notMem hn,zero_mul]
  constructor
  · rw [←hk, integrableOn_indicator_iff hμ.nullMeasurableSet, inter_comm]
    exact hi
  · rw [←hk, setIntegral_indicator hμ]
    exact he

/-- Paper: Section 12.4, footnote 2 on p. 514 and (12.4.1.23), p. 518.
With an independent positive lower spatial radius, the integral of the actual
annular sharp kernel on an S-unit fundamental domain is the difference of
the two one-sided sharp orbital masses. The frequency radius multiplies
both spatial radii.
Deviation: This computes the two-sided sharp version suggested by the footnote. -/
theorem sLocalTraceAnnularCutoff_eq_difference (f : BruhatCompactSupport Iₛ) (ξ : Hₛ)
    (D : Set Iₛ) (hD : IsFundamentalDomain Hₛ D μI) {l L L' : ℝ}
    (hl : 0 < l) (hlL : l ≤ L) (hL' : 0 < L') :
    let k := fun x : Iₛ ↦ sLocalTraceCutoffKernel f oneOn(slab(L) \ slab(l)) oneOn(band(L')) (ξ.val*x) x.val
    IntegrableOn k D νI ∧ ∫ x in D, k x ∂νI =
      sLocalTraceSharpMass f ξ (L*L') - sLocalTraceSharpMass f ξ (l*L') := by
  intro k
  let u (r : ℝ) (x : Iₛ) := sLocalTraceCutoffKernel f oneOn(slab(r)) oneOn(band(L')) (ξ.val*x) x.val
  obtain ⟨hU,eU⟩ := upper_cutoff_on_domain f ξ D hD (hl.trans_le hlL) hL'
  obtain ⟨hB,eB⟩ := upper_cutoff_on_domain f ξ D hD hl hL'
  have hk : k = (fun x ↦ u L x - u l x) := by
    funext x
    have hsub : slab(l) ⊆ slab(L) := fun _ hx ↦ hx.trans hlL
    by_cases hs : ξ.val*x ∈ slab(l)
    · simp [k,u,sLocalTraceCutoffKernel,hs,hsub hs]
    · by_cases hb : ξ.val*x ∈ slab(L) <;> simp [k,u,sLocalTraceCutoffKernel,hs,hb]
  rw [hk]
  exact ⟨hU.sub hB, (integral_sub hU hB).trans (congrArg₂ (·-·) eU eB)⟩

private theorem lower_log_mass {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (g : X → ℂ) (m : X → ℝ) (hm : Measurable m) (hmpos : ∀ᵐ x ∂μ, 0 < m x)
    (hg : Integrable g μ) (hw : Integrable (fun x ↦ g x * (Real.log (m x) : ℂ)) μ) :
    Tendsto (fun R : ℝ ↦ ∫ x in {x | m x ≤ R}, g x *
      ((Real.log R - Real.log (m x) : ℝ) : ℂ) ∂μ) (𝓝[>] 0) (𝓝 0) := by
  classical
  let t (R : ℝ) := {x : X | m x ≤ R}
  have ht (R : ℝ) : MeasurableSet (t R) := measurableSet_le hm measurable_const
  let k (R : ℝ) (x : X) := g x * ((Real.log R - Real.log (m x) : ℝ) : ℂ)
  have hk (R : ℝ) : Integrable (k R) μ := by
    simp only [k, Complex.ofReal_sub, mul_sub]
    exact (hg.mul_const (Real.log R : ℂ)).sub hw
  have htend := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := 𝓝[>] (0:ℝ))
    (F := fun R ↦ (t R).indicator (k R)) (f := fun _ ↦ (0 : ℂ))
    (fun x ↦ ‖g x * (Real.log (m x) : ℂ)‖)
    (.of_forall fun R ↦ ((hk R).indicator (ht R)).aestronglyMeasurable) ?_ hw.norm ?_
  · simpa only [integral_indicator (ht _), integral_zero] using htend
  · filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (zero_lt_one : (0:ℝ)<1))] with R hR
    change R < 1 at hR
    filter_upwards [hmpos] with x hx
    by_cases he : x ∈ t R
    · have hle : m x ≤ R := he
      have hl := Real.log_le_log hx hle
      have hlR := Real.log_nonpos (hx.trans_le hle).le hR.le
      rw [indicator_of_mem he]
      simp only [k, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr hl), abs_of_nonpos (hl.trans hlR)]
      gcongr
      linarith
    · rw [indicator_of_notMem he, norm_zero]
      exact norm_nonneg _
  · filter_upwards [hmpos] with x hx
    apply tendsto_const_nhds.congr'
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hx)] with R hR
    change R < m x at hR
    exact (indicator_of_notMem (not_le.mpr hR : x ∉ t R) _).symm

/-- A single omitted lower orbital mass tends to zero if its positive
radius tends to zero. The Fourier logarithmic moment gives an integrable
majorant. This handles the lower endpoint proposed on p. 514. -/
theorem sLocalTraceSharpMass_tendsto_zero_at_small_radius (f : BruhatCompactSupport Iₛ) (ξ : Hₛ) :
    Tendsto (sLocalTraceSharpMass f ξ) (𝓝[>] 0) (𝓝 0) := by
  let : BorelSpace Aₛ := sAdeleRing_borelSpace
  let m (x : Aₛ) := (∏ w : InfinitePlace F, ‖x.1 w‖ ^ w.mult) * ∏ v : S, ‖x.2 v‖
  have hm : Continuous m :=
    (continuous_finsetProd _ fun w _ ↦
      (((continuous_apply w).comp continuous_fst).norm.pow _)).mul
      (continuous_finsetProd _ fun v _ ↦ ((continuous_apply v).comp continuous_snd).norm)
  have hfull : ∀ᵐ x ∂ν, x ∈ range (Units.val : Iₛ → Aₛ) :=
    (measure_eq_zero_iff_ae_notMem.mp sLocalTrace_nonunits_null).mono fun _ h ↦ not_not.mp h
  have hp : ∀ᵐ x ∂ν, 0 < m x := by
    filter_upwards [hfull] with x hx
    obtain ⟨u,rfl⟩ := hx
    have he : m u.val = N(u) := by simp [m,sIdeleNorm,Units.coe_prod]
    exact he ▸ NNReal.coe_pos.mpr (Units.zero_lt _)
  have h := lower_log_mass ν _ m hm.measurable hp
    (sLocalTraceEta_fourier_integrable f ξ) (sLocalTrace_fourier_log_integrable f ξ)
  have heq (R : ℝ) : (ν).restrict (band(R) ∩ range (Units.val : Iₛ → Aₛ)) =
      (ν).restrict (band(R)) := by
    rw [← Measure.restrict_restrict (show MeasurableSet (band(R)) from (isClosed_le hm continuous_const).measurableSet),
      Measure.restrict_eq_self_of_ae_mem hfull]
  have hr (R : ℝ) : band(R) = {x : Aₛ | m x ≤ R} := rfl
  have ht := h.const_mul (((sLocalNormOneQuotientMeasure F S) univ).toReal : ℂ)
  rw [mul_zero] at ht
  exact ht.congr (fun R ↦ by rw [sLocalTraceSharpMass, heq R, hr R])

/-- Over the rationals with no finite places in S, the projected S-units
form a finite group. Its source is the unit group of the rational integers. -/
theorem finite_rational_empty_sProjectedDiagonal :
    Finite (sProjectedDiagonal ℚ (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))) := by
  let S₀ : Finset (HeightOneSpectrum (𝓞 ℚ)) := ∅
  have hfin : Finite ((S₀ : Set (HeightOneSpectrum (𝓞 ℚ))).integer ℚ)ˣ := by
    dsimp only [S₀]
    rw [Finset.coe_empty, integer_empty]
    let e := (Algebra.botEquivOfInjective (IsFractionRing.injective (𝓞 ℚ) ℚ)).toRingEquiv
    exact Finite.of_injective (Units.mapEquiv (e.trans Rat.ringOfIntegersEquiv).toMulEquiv)
      (Units.mapEquiv (e.trans Rat.ringOfIntegersEquiv).toMulEquiv).injective
  let := hfin
  change Finite (sProjectedDiagonal ℚ S₀)
  rw [sProjectedDiagonal, MonoidHom.map_range]
  exact Finite.of_surjective _ (sUnitEmbedding ℚ S₀).rangeRestrict_surjective

/-- A finite S-unit sum of sharp masses has zero small-radius limit. In
particular this applies to the real-place calculation over the rationals. -/
theorem sLocalTraceSharpMass_tsum_tendsto_zero_at_small_radius [Finite Hₛ]
    (f : BruhatCompactSupport Iₛ) :
    Tendsto (fun R : ℝ ↦ ∑' ξ : Hₛ, sLocalTraceSharpMass f ξ R) (𝓝[>] 0) (𝓝 0) := by
  classical
  let := Fintype.ofFinite Hₛ
  simpa only [tsum_fintype, Finset.sum_const_zero] using
    (tendsto_finsetSum Finset.univ (fun (ξ : Hₛ) _ ↦ sLocalTraceSharpMass_tendsto_zero_at_small_radius f ξ))

/-- The orbit sum of the actual sharp annular diagonal on a fundamental domain,
in the order in which the sharp mass sums the S-unit orbits. -/
def sLocalTraceAnnularOrbitSum (f : BruhatCompactSupport Iₛ) (D : Set Iₛ)
    (l L L' : ℝ) : ℂ :=
  ∑' ξ : Hₛ, ∫ x in D, sLocalTraceCutoffKernel f oneOn(slab(L) \ slab(l)) oneOn(band(L')) (ξ.val*x) x.val ∂νI

/-- If both one-sided orbital sums converge, subtraction identifies the
annular cutoff exactly. The orbit group may be infinite. -/
theorem sLocalTraceAnnularOrbitSum_eq_sub (f : BruhatCompactSupport Iₛ)
    (D : Set Iₛ) (hD : IsFundamentalDomain Hₛ D μI) {l L L' : ℝ}
    (hl : 0 < l) (hlL : l ≤ L) (hL' : 0 < L')
    (hU : Summable (fun ξ : Hₛ ↦ sLocalTraceSharpMass f ξ (L*L')))
    (hB : Summable (fun ξ : Hₛ ↦ sLocalTraceSharpMass f ξ (l*L'))) :
    sLocalTraceAnnularOrbitSum f D l L L' = (∑' ξ : Hₛ, sLocalTraceSharpMass f ξ (L*L')) -
      ∑' ξ : Hₛ, sLocalTraceSharpMass f ξ (l*L') := by
  unfold sLocalTraceAnnularOrbitSum
  exact (tsum_congr (fun ξ ↦ (sLocalTraceAnnularCutoff_eq_difference f ξ D hD hl hlL hL').2)).trans
    (hU.tsum_sub hB)

/-- For finite S-units, two choices of the lower spatial radius give distinct
limits whenever the one-sided sharp local trace has a nonzero finite limit.
Both use spatial upper radius t and Fourier radius t². With lower radius 1/t
the limit is zero, and with lower radius 1/t³ it is the full one-sided limit. -/
theorem sLocalTraceAnnularOrbitSum_two_rates [Finite Hₛ] (f : BruhatCompactSupport Iₛ)
    (D : Set Iₛ) (hD : IsFundamentalDomain Hₛ D μI) {C : ℂ}
    (hC : Tendsto (fun R : ℝ ↦ ∑' ξ : Hₛ, sLocalTraceSharpMass f ξ R) atTop (𝓝 C)) :
    Tendsto (fun t : ℝ ↦ sLocalTraceAnnularOrbitSum f D t⁻¹ t (t*t)) atTop (𝓝 0) ∧
      Tendsto (fun t : ℝ ↦ sLocalTraceAnnularOrbitSum f D (t*(t*t))⁻¹ t (t*t)) atTop (𝓝 C) := by
  let := Fintype.ofFinite Hₛ
  let M (r : ℝ) := ∑' ξ : Hₛ, sLocalTraceSharpMass f ξ r
  have hprod : Tendsto (fun t : ℝ ↦ t*(t*t)) atTop atTop :=
    tendsto_id.atTop_mul_atTop₀ (tendsto_id.atTop_mul_atTop₀ tendsto_id)
  have hA : Tendsto (fun t : ℝ ↦ M (t*(t*t))) atTop (𝓝 C) := hC.comp hprod
  have hB : Tendsto (fun t : ℝ ↦ M t⁻¹) atTop (𝓝 0) :=
    (sLocalTraceSharpMass_tsum_tendsto_zero_at_small_radius f).comp tendsto_inv_atTop_nhdsGT_zero
  have e (t l : ℝ) (ht : 1 ≤ t) (hl : 0 < l) (hlt : l ≤ t) :
      sLocalTraceAnnularOrbitSum f D l t (t*t) = M (t*(t*t)) - M (l*(t*t)) :=
    sLocalTraceAnnularOrbitSum_eq_sub f D hD hl hlt (mul_pos (zero_lt_one.trans_le ht) (zero_lt_one.trans_le ht))
      (hasSum_fintype _).summable (hasSum_fintype _).summable
  constructor
  · have h := hA.sub hC
    rw [sub_self] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
    have hpos := zero_lt_one.trans_le ht
    rw [e _ _ ht (inv_pos.mpr hpos) ((inv_le_one_of_one_le₀ ht).trans ht)]
    congr 2
    field_simp
  · have h := hA.sub hB
    rw [sub_zero] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
    have hpos := zero_lt_one.trans_le ht
    have h1 : 1 ≤ t*(t*t) := one_le_mul_of_one_le_of_one_le ht (one_le_mul_of_one_le_of_one_le ht ht)
    rw [e _ _ ht (by positivity) ((inv_le_one_of_one_le₀ h1).trans ht)]
    congr 2
    field_simp

section LocalLimits

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "vS" => ((sLocalNormOneQuotientMeasure F S) univ).toReal
local notation "arch(" w ")" => IdeleClassGroup.ofCompletion (𝓞 F) F w
local notation "fin(" v ")" => IdeleClassGroup.ofAdicCompletion (𝓞 F) F v
local notation "finVol(" v ")" =>
  ((finiteLocalMultiplicativeTamagawaMeasure F v) ((v : V).adicCompletionIntegers F).units).toReal
local notation "pv(" a "," b ")" => ((∑ w : InfinitePlace F, infiniteConnesWeilPrincipalValue w (a w)) +
  ∑ v : S, ((Real.log (v.val.asIdeal.absNorm : ℝ) / finVol(v.val) : ℝ) : ℂ) *
    finiteConnesWeilPrincipalValue v.val 1 (b v))

/-- Paper: Theorem 12.4.1.1 and footnote 2, p. 514. For a finite S-unit group
and an actual lift of a test vanishing at the identity, the two annular
sharp cutoff paths have limits zero and the norm-one volume times the
normalized local principal values. The unscaled local term can thus depend
on the relative growth of the lower and Fourier cutoff parameters.
Deviation: The footnote asks to study the independently varying lower cutoff. -/
theorem sLocalTraceAnnularOrbitSum_two_local_limits [Finite Hₛ] (φ : BruhatCompactSupport C𝔽)
    (hφ : φ.val 1 = 0) (hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F)))
    (hRam : ∀ v : V, differentIdeal ℤ (𝓞 F) ≤ v.asIdeal → v ∈ S)
    (hout : ∀ (u : outsideIntegralIdeleUnits F S) (x : C𝔽), φ.val (QuotientGroup.mk u.val*x) = φ.val x)
    (f : BruhatCompactSupport Iₛ) (hLift : ∀ x : Iₛ, HasSum (fun ξ : Hₛ ↦ f.val (ξ.val*x))
      (φ.val (QuotientGroup.mk (sIdeleInsertion F S x))))
    (D : Set Iₛ) (hD : IsFundamentalDomain Hₛ D μI) :
    ∃ (a : (w : InfinitePlace F) → BruhatCompactSupport w.Completionˣ)
      (b : (v : S) → BruhatCompactSupport (v.val.adicCompletion F)ˣ),
      (∀ w u, (a w).val u = φ.val (arch(w) u)) ∧ (∀ (v : S) u, (b v).val u = φ.val (fin(v.val) u)) ∧
      Tendsto (fun t : ℝ ↦ sLocalTraceAnnularOrbitSum f D t⁻¹ t (t*t)) atTop (𝓝 0) ∧
      Tendsto (fun t : ℝ ↦ sLocalTraceAnnularOrbitSum f D (t*(t*t))⁻¹ t (t*t)) atTop
        (𝓝 ((vS : ℂ) * pv(a,b))) := by
  obtain ⟨a,b,M,ha,hb,hs,h₀⟩ := sLocalTraceSharpMass_asymptotic φ hPic hRam hout f hLift
  simp only [hφ,mul_zero,zero_mul,sub_zero] at h₀
  have h := h₀.congr' (hs.mono (fun _ hsum ↦ hsum.tsum_eq.symm))
  exact ⟨a,b,ha,hb,sLocalTraceAnnularOrbitSum_two_rates f D hD h⟩

end LocalLimits
end RiemannMasullo
