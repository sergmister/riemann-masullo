module

public import RiemannMasullo.Ch12_TraceGeometric.Sec1a
public import RiemannMasullo.Ch10_TraceSpectral.Sec4b
import RiemannMasullo.Ch10_TraceSpectral.Sec1
import all RiemannMasullo.AppD_SchwartzBruhat.Sec3b
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Topology.UrysohnsLemma
import RiemannMasullo.ForMathlib.MeasureTheory.Function.L2Space

/-!
# Localization along the global diagonal

Masullo, Theorem 12.1.1.3 and Remark 12.1.1.4, pp. 502–504. The product averages
use Haar measure and a chosen Borel D′-sequence on the idele class group. The
operators whose traces are computed act on the weighted Sobolev space.

The kernels are those of Definition 10.4.3.2, the case `I = {0}`, which in Lean
are `globalLineSpectralKernel` and `globalLineGeometricKernel`: they belong to
spectral projection after convolution, `P^spec_a ∘ A(φ)`, the operator of
(12.1.1.21). The strip kernels of Definition 10.4.3.7 belong to convolution after
projection and are not used here.
-/

@[expose] public noncomputable section

open Filter MeasureTheory NumberField Set Topology
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false
set_option maxHeartbeats 900000

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" =>
  (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "logNorm" => (fun g : C𝔽 ↦ Real.log ((ideleClassNorm F g).val : ℝ))
local notation "W(" s ")" => CompactIntervalSobolev μ𝔽 logNorm (-(0 : ℝ)) 0 s
local notation "hline" => (le_refl (0 : ℝ))
local notation "hbase" => ((neg_nonpos.mpr hline).trans hline)
local notation "hs₀(" hs ")" => (le_trans (by norm_num : (0 : ℝ) ≤ 3) hs)
local notation "hs₁(" hs ")" => (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 3) hs)
local notation "convKernel(" φ ")" =>
  (fun p : C𝔽 × C𝔽 ↦ (φ : BruhatCompactSupport C𝔽).val (p.1 * p.2⁻¹))
local notation "innerBand(" Λ ", " ε ")" => (0 < Λ⁻¹ + ε ∧ Λ⁻¹ + ε < Λ - ε)

-- TODO(paper-gap): The printed standard sequence on the idele class group
-- need not shrink to the identity. Use a Borel D′-sequence as in §12.1a.
variable {U : ℕ → Set (IdeleClassGroup (𝓞 F) F)}
  (hU : IsDPrimeSequence (ideleClassTamagawaMeasure F) U) (hBorel : ∀ n, MeasurableSet (U n))

local notation "regular(" k ")" =>
  dSequenceRegularSet ((μ𝔽).prod μ𝔽) (fun n ↦ U n ×ˢ U n) k
local notation "diagonal(" k ")" => (fun x ↦ dSequenceKernelSmoothening μ𝔽 U k (x, x))

include hU hBorel

omit hU hBorel in
open scoped Pointwise ENNReal in
/-- The convolution kernel is eventually integrable on the averaging neighborhoods,
and its averages on the diagonal converge to the test value at the identity. -/
theorem diagonal_mem_convolutionKernelRegularSet_averages
    {F : Type*} [Field F] [NumberField F]
    {U : ℕ → Set (IdeleClassGroup (𝓞 F) F)}
    (hU : IsDPrimeSequence (ideleClassTamagawaMeasure F) U)
    (hBorel : ∀ n, MeasurableSet (U n))
    (φ : BruhatCompactSupport (IdeleClassGroup (𝓞 F) F))
    (x : IdeleClassGroup (𝓞 F) F) :
    (∀ᶠ n in atTop, IntegrableOn
      (fun p : (IdeleClassGroup (𝓞 F) F) × (IdeleClassGroup (𝓞 F) F) ↦ φ.val (p.1 * p.2⁻¹))
      ((x, x) • (U n ×ˢ U n))
      ((ideleClassTamagawaMeasure F).prod (ideleClassTamagawaMeasure F))) ∧
      Tendsto (fun n ↦ dSequenceAverage
        ((ideleClassTamagawaMeasure F).prod (ideleClassTamagawaMeasure F)) (U n ×ˢ U n)
        (fun p : (IdeleClassGroup (𝓞 F) F) × (IdeleClassGroup (𝓞 F) F) ↦ φ.val (p.1 * p.2⁻¹))
        (x, x)) atTop (𝓝 (φ.val 1)) := by
  let G := IdeleClassGroup (𝓞 F) F
  let μ : Measure G := ideleClassTamagawaMeasure F
  let f : G × G → ℂ := fun p ↦ φ.val (p.1 * p.2⁻¹)
  have hc : Continuous φ.val :=
    schwartzBruhat_continuous
      (⟨φ.val, bruhatCompactSupport_mem_schwartz φ.property⟩ : SchwartzBruhat G)
  have hg : Continuous f := hc.comp (continuous_fst.mul continuous_snd.inv)
  have rectSeq [m : MeasurableSpace (G × G)] (hm : m = borel _)
      (η : Measure (G × G)) [η.IsHaarMeasure]
      (hrect : ∀ v w : Set G, MeasurableSet v → MeasurableSet w →
        η (v ×ˢ w) = μ v * μ w) :
      IsDPrimeSequence η (fun n ↦ U n ×ˢ U n) := by
    subst m
    exact IsDPrimeSequence.prod hrect hU hU
  have hseq : IsDPrimeSequence (μ.prod μ) (fun n ↦ U n ×ˢ U n) :=
    rectSeq BorelSpace.measurable_eq _ (fun v w _ _ ↦ Measure.prod_prod v w)
  have hshrink {W : Set (G × G)} (hW : W ∈ 𝓝 (x, x)) :
      ∀ᶠ n in atTop, (x, x) • (U n ×ˢ U n) ⊆ W := by
    have hpre : (fun y : G × G ↦ (x, x) * y) ⁻¹' W ∈ 𝓝 1 :=
      (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds (by simpa using hW)
    obtain ⟨N, hN⟩ := hseq.2 _ hpre
    filter_upwards [eventually_ge_atTop N] with n hn
    exact Set.smul_set_subset_iff.mpr fun _ hy ↦ hN (hseq.1.2.1 hn hy)
  obtain ⟨W, hW, hiW⟩ := hg.locallyIntegrable (μ := μ.prod μ) (x, x)
  have hint : ∀ᶠ n in atTop,
      IntegrableOn f ((x, x) • (U n ×ˢ U n)) (μ.prod μ) :=
    (hshrink hW).mono fun _ hn ↦ hiW.mono_set hn
  refine ⟨hint, ?_⟩
  have hvalue : f (x, x) = φ.val 1 := congrArg φ.val (mul_inv_cancel x)
  rw [← hvalue]
  refine Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
  have hnear : f ⁻¹' Metric.ball (f (x, x)) (ε / 2) ∈
      𝓝 (x, x) :=
    hg.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ (half_pos hε))
  filter_upwards [hshrink hnear, hint] with n hn hi
  let S := (x, x) • (U n ×ˢ U n)
  have hzero : (μ.prod μ) S ≠ 0 := by
    simpa only [S, measure_smul] using (hseq.1.1 n).2.2.1.ne'
  have hfin : (μ.prod μ) S ≠ ∞ := by
    simpa only [S, measure_smul] using (hseq.1.1 n).2.2.2.ne
  have havg : (⨍ y in S, f y - f (x, x) ∂(μ.prod μ)) =
      dSequenceAverage (μ.prod μ) (U n ×ˢ U n) f (x, x) -
        f (x, x) := by
    change (⨍ y in S, f y - f (x, x) ∂(μ.prod μ)) =
      (⨍ y in S, f y ∂(μ.prod μ)) - f (x, x)
    rw [setAverage_fun_sub hi (integrableOn_const (C := f (x, x)) hfin),
      setAverage_const hzero hfin]
  rw [dist_eq_norm, ← ENNReal.ofReal_lt_ofReal_iff hε, ofReal_norm, ← havg]
  calc
    ‖⨍ y in S, f y - f (x, x) ∂(μ.prod μ)‖ₑ ≤
        ⨍⁻ y in S, ‖f y - f (x, x)‖ₑ ∂(μ.prod μ) := by
      rw [setAverage_eq', setLAverage_eq']
      exact eNorm_integral_le_lintegral_eNorm _
    _ ≤ ⨍⁻ _ in S, ENNReal.ofReal (ε / 2) ∂(μ.prod μ) := by
      rw [setLAverage_eq', setLAverage_eq']
      apply lintegral_mono_ae
      have hS := (ae_restrict_mem (μ := μ.prod μ)
        (((hBorel n).prod (hBorel n)).const_smul (x, x))).filter_mono
        (Measure.ae_smul_measure_le ((μ.prod μ) S)⁻¹)
      filter_upwards [hS] with y hy
      have hy' : dist (f y) (f (x, x)) < ε / 2 := hn hy
      rw [← ofReal_norm, ← dist_eq_norm]
      exact ENNReal.ofReal_le_ofReal hy'.le
    _ < ENNReal.ofReal ε := by
      rw [setLAverage_const hzero hfin, ENNReal.ofReal_lt_ofReal_iff hε]
      exact half_lt_self hε

/-- Paper: Theorem 12.1.1.3(1), p. 502. The diagonal points of the convolution
kernel are regular for the Haar product averages.
Deviation: A valid Borel D′-sequence is explicit throughout. -/
theorem diagonal_mem_convolutionKernelRegularSet (φ : BruhatCompactSupport C𝔽) (x : C𝔽) :
    (x, x) ∈ regular(convKernel(φ)) := by
  exact ⟨φ.val 1, (diagonal_mem_convolutionKernelRegularSet_averages hU hBorel φ x).2⟩

omit hU hBorel in
private theorem isNuclearOperator_adjoint_sec1b {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (T : H →L[ℂ] H) (hT : IsNuclearOperator T) :
    IsNuclearOperator T.adjoint := by
  have hTc : T ∈ traceClassOperators H H := (mem_traceClassOperators_iff_isNuclearOperator T).mpr hT
  refine (mem_traceClassOperators_iff_isNuclearOperator T.adjoint).mp ?_
  change IsCompactOperator T.adjoint ∧ Summable (fun n ↦ approximationNumber T.adjoint n ^ (1 : ℝ))
  refine ⟨isCompactOperator_adjoint_of_compact T hTc.1, ?_⟩
  have happ (n : ℕ) : approximationNumber T.adjoint n = approximationNumber T n := by
    by_cases hn : (n : Cardinal) < Module.rank ℂ H
    · exact (approximationNumber_adjoint T hTc.1 n hn).symm
    · have hle : Module.rank ℂ H ≤ (n : Cardinal) := le_of_not_gt hn
      have hzero (A : H →L[ℂ] H) : approximationNumber A n = 0 := by
        unfold approximationNumber
        refine le_antisymm ?_ (Real.sInf_nonneg ?_)
        · refine csInf_le ⟨0, ?_⟩ ?_
          · rintro _ ⟨S, _, rfl⟩; exact norm_nonneg _
          · exact ⟨A, (Submodule.rank_le _).trans hle, by simp⟩
        · rintro _ ⟨S, _, rfl⟩; exact norm_nonneg _
      rw [hzero T.adjoint, hzero T]
  exact hTc.2.congr fun n ↦ by rw [happ n]

omit hU hBorel in
open scoped ComplexConjugate InnerProductSpace in
private theorem integralKernelOperator_adjoint_sec1b {X : Type*}
    [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    (ν : Measure X) [IsFiniteMeasureOnCompacts ν] [Measure.InnerRegular ν]
    (a : Lp ℂ 2 (ν.prod ν)) :
    ∃ c : Lp ℂ 2 (ν.prod ν), (c : X × X → ℂ) =ᵐ[ν.prod ν] (fun p ↦ conj (a p.swap)) ∧
      (integralKernelOperator ν c).val = (integralKernelOperator ν a).val.adjoint := by
  let swap := Measure.measurePreserving_swap (μ := ν) (ν := ν)
  have ha := (Lp.memLp a).comp_measurePreserving swap
  have hc : MemLp (fun p : X × X ↦ conj (a p.swap)) 2 (ν.prod ν) :=
    ha.congr_norm (Complex.continuous_conj.comp_aestronglyMeasurable ha.aestronglyMeasurable)
      (Eventually.of_forall fun p : X × X ↦ (Complex.norm_conj (a p.swap)).symm)
  let c := hc.toLp (fun p : X × X ↦ conj (a p.swap))
  refine ⟨c, hc.coeFn_toLp, ?_⟩
  apply ContinuousLinearMap.ext
  intro g
  apply ext_inner_right ℂ
  intro f
  rw [ContinuousLinearMap.adjoint_inner_left]
  simp only [L2.inner_def, RCLike.inner_apply]
  let F' (p : X × X) := conj (g p.1) * (a p * f p.2)
  obtain ⟨K, hK, -⟩ := L2.exists_outerProduct f g
  have hF : Integrable F' (ν.prod ν) := by
    refine ((Lp.memLp a).integrable_mul ((Lp.memLp K).comp_measurePreserving swap)).congr ?_
    filter_upwards [swap.quasiMeasurePreserving.ae hK] with p hp
    change a p * K p.swap = F' p
    rw [hp, RCLike.inner_apply]
    dsimp [F']
    ring
  calc
    _ = ∫ y, ∫ x, F' (x, y) ∂ν ∂ν := by
      apply integral_congr_ae
      filter_upwards [integralKernelOperator_apply ν c g,
        Measure.ae_ae_of_ae_prod hc.coeFn_toLp] with y hy hcy
      have hconj : conj (∫ x, c (y, x) * g x ∂ν) =
          ∫ x, conj (c (y, x) * g x) ∂ν :=
        (Complex.conjCLE.toContinuousLinearMap.integral_comp_comm hy.1).symm
      rw [hy.2, hconj, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [hcy] with x hx
      rw [hx, map_mul, Complex.conj_conj]
      dsimp [F']
      ring
    _ = ∫ x, ∫ y, F' (x, y) ∂ν ∂ν :=
      (integral_prod_symm F' hF).symm.trans (integral_prod F' hF)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [integralKernelOperator_apply ν a f] with x hx
      rw [hx.2, mul_comm, ← integral_const_mul]

omit hU hBorel in
open scoped ComplexConjugate Pointwise in
private theorem dSequenceAverage_conj_swap_diagonal {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]
    (V : ℕ → Set G) (ψ : G × G → ℂ) (x : G) (n : ℕ) :
    dSequenceAverage (μ.prod μ) (V n ×ˢ V n) (fun p ↦ conj (ψ p.swap)) (x, x) =
      conj (dSequenceAverage (μ.prod μ) (V n ×ˢ V n) ψ (x, x)) := by
  let S : Set G := x • V n
  have hprod_set : (x, x) • (V n ×ˢ V n) = S ×ˢ S := by
    ext ⟨u, v⟩
    simp only [S, mem_smul_set, mem_prod]
    constructor
    · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, h⟩
      rcases Prod.mk.inj h with ⟨rfl, rfl⟩
      exact ⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩
    · rintro ⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩
      exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩
  have hrestrict : (μ.prod μ).restrict (S ×ˢ S) = (μ.restrict S).prod (μ.restrict S) :=
    (Measure.prod_restrict S S).symm
  have hswap : ∫ p in S ×ˢ S, ψ p.swap ∂(μ.prod μ) = ∫ p in S ×ˢ S, ψ p ∂(μ.prod μ) := by
    rw [hrestrict]
    exact (Measure.measurePreserving_swap (μ := μ.restrict S) (ν := μ.restrict S)).integral_comp
      MeasurableEquiv.prodComm.measurableEmbedding ψ
  unfold dSequenceAverage
  rw [hprod_set, setAverage_eq, setAverage_eq, integral_conj, hswap]
  simp [Complex.real_smul]

omit hU hBorel in
open scoped ComplexConjugate Pointwise in
private theorem dSequenceKernelSmoothening_conj_swap_diagonal {G : Type*} [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]
    (V : ℕ → Set G) (ψ : G × G → ℂ) (x : G) :
    dSequenceKernelSmoothening μ V (fun p ↦ conj (ψ p.swap)) (x, x) =
      conj (dSequenceKernelSmoothening μ V ψ (x, x)) := by
  have havg (n : ℕ) := dSequenceAverage_conj_swap_diagonal (μ := μ) V ψ x n
  by_cases hreg : (x, x) ∈ dSequenceRegularSet (μ.prod μ) (fun n ↦ V n ×ˢ V n) ψ
  · obtain ⟨v, hv⟩ := hreg
    have hreg0 : (x, x) ∈ dSequenceRegularSet (μ.prod μ) (fun n ↦ V n ×ˢ V n) ψ := ⟨v, hv⟩
    have hv' : Tendsto
        (fun n ↦ dSequenceAverage (μ.prod μ) (V n ×ˢ V n) (fun p ↦ conj (ψ p.swap)) (x, x))
        atTop (𝓝 (conj v)) := by
      simpa only [havg, Function.comp_def] using (Complex.continuous_conj.tendsto v).comp hv
    have hreg' : (x, x) ∈ dSequenceRegularSet (μ.prod μ) (fun n ↦ V n ×ˢ V n)
        (fun p ↦ conj (ψ p.swap)) := ⟨conj v, hv'⟩
    simp only [dSequenceKernelSmoothening, dSequenceSmootheningOrZero, dite_eq_left hreg',
      dSequenceSmoothening, dite_eq_left hreg0, hv'.limUnder_eq, hv.limUnder_eq]
  · have hreg' : (x, x) ∉ dSequenceRegularSet (μ.prod μ) (fun n ↦ V n ×ˢ V n)
        (fun p ↦ conj (ψ p.swap)) := by
      rintro ⟨v, hv⟩
      apply hreg
      refine ⟨conj v, ?_⟩
      have hback := (Complex.continuous_conj.tendsto v).comp hv
      simpa only [Function.comp_def, havg, Complex.conj_conj] using hback
    simp only [dSequenceKernelSmoothening, dSequenceSmootheningOrZero, dite_eq_right hreg',
      dite_eq_right hreg, map_zero]

omit hU hBorel in
open scoped ComplexConjugate ENNReal Pointwise in
theorem dSequenceKernelSmoothening_mul_continuous_snd_diagonal {G : Type*} [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    {μ ν : Measure G} [μ.IsHaarMeasure] [IsFiniteMeasureOnCompacts ν] [ν.InnerRegular]
    {V : ℕ → Set G} (hV : IsDPrimeSequence μ V) (hVBorel : ∀ n, MeasurableSet (V n))
    {f : G → ℝ≥0} (hf : Continuous f) (hf_pos : ∀ x, 0 < f x)
    (hν : ν = μ.withDensity (fun x ↦ ↑(f x)))
    {k : Lp ℂ 2 (ν.prod ν)} {κ : G × G → ℂ} (hκ : κ =ᵐ[ν.prod ν] k)
    (hT : IsNuclearOperator (integralKernelOperator ν k).val)
    (g : G → ℂ) (hg : Continuous g) :
    ∀ᵐ x ∂μ,
      (x, x) ∈ dSequenceRegularSet (μ.prod μ) (fun n ↦ V n ×ˢ V n) (fun p ↦ g p.2 * κ p) ∧
        dSequenceKernelSmoothening μ V (fun p ↦ g p.2 * κ p) (x, x) =
          g x * dSequenceKernelSmoothening μ V κ (x, x) := by
  obtain ⟨kAdj, hkAdj_ae, hkAdj_op⟩ := integralKernelOperator_adjoint_sec1b ν k
  let κAdj : G × G → ℂ := fun p ↦ conj (κ p.swap)
  have hκAdj : κAdj =ᵐ[ν.prod ν] kAdj := by
    have hswap := (Measure.measurePreserving_swap (μ := ν) (ν := ν)).quasiMeasurePreserving.ae hκ
    filter_upwards [hswap, hkAdj_ae] with p hp hka
    exact (congrArg conj hp).trans hka.symm
  have hTAdj : IsNuclearOperator (integralKernelOperator ν kAdj).val :=
    (congrArg (fun L : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν ↦ IsNuclearOperator L) hkAdj_op).mpr
      (isNuclearOperator_adjoint_sec1b _ hT)
  have hloc (m : ℕ) :
      ∀ᵐ x ∂μ, x ∈ compactCovering G m →
        (x, x) ∈ dSequenceRegularSet (μ.prod μ) (fun n ↦ V n ×ˢ V n) (fun p ↦ g p.2 * κ p) ∧
          dSequenceKernelSmoothening μ V (fun p ↦ g p.2 * κ p) (x, x) =
            g x * dSequenceKernelSmoothening μ V κ (x, x) := by
    obtain ⟨L, hLc, hsubL⟩ := exists_compact_superset (isCompact_compactCovering G m)
    obtain ⟨χ, hχ1, _, hχc, _⟩ :=
      exists_continuous_one_zero_of_isCompact hLc isClosed_empty (disjoint_empty L)
    let ρ : G → ℂ := fun y ↦ conj (((χ y : ℝ) : ℂ) * g y)
    have hρ : Continuous ρ :=
      Complex.continuous_conj.comp ((Complex.continuous_ofReal.comp χ.continuous).mul hg)
    have hρc : HasCompactSupport ρ := by
      refine HasCompactSupport.of_support_subset_isCompact hχc fun y hy ↦ ?_
      apply subset_tsupport χ
      intro h0
      apply hy
      simp [ρ, h0]
    obtain ⟨C, hC⟩ := hρ.bounded_above_of_compact_support hρc
    have hρ_mem : MemLp ρ ⊤ ν :=
      memLp_top_of_bound (hρ.aestronglyMeasurable (μ := ν)) C (Eventually.of_forall hC)
    let ρLp : Lp ℂ ⊤ ν := hρ_mem.toLp ρ
    obtain ⟨Kρ, hKρ_op, hKρ_ae, _⟩ :=
      integralKernelOperator_mul_dSequenceKernelSmoothening hκAdj hV hVBorel hf hf_pos hν hTAdj ρLp
    have hKρ_rep : (fun p : G × G ↦ ρ p.1 * κAdj p) =ᵐ[ν.prod ν] Kρ := by
      filter_upwards [hKρ_ae, Measure.quasiMeasurePreserving_fst.ae hρ_mem.coeFn_toLp] with p h1 h2
      rw [h1, h2]
    have hKρ_nuc : IsNuclearOperator (integralKernelOperator ν Kρ).val :=
      (congrArg (fun L : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν ↦ IsNuclearOperator L) hKρ_op).mpr
        (mul_mem_nuclearEndomorphisms_left _ ⟨_, hTAdj⟩)
    have hae_reg :=
      ae_diagonal_mem_dSequenceRegularSet hKρ_rep hV hVBorel hf hf_pos hν hKρ_nuc
    have hae_val :=
      dSequenceKernelSmoothening_mul_continuous_diagonal hκAdj hV hVBorel hf hf_pos hν hTAdj ρ hρ hρc
    filter_upwards [hae_reg, hae_val] with x hxreg hxval hxK
    have hx_int : x ∈ interior L := hsubL hxK
    have hpre : (fun y : G ↦ x * y) ⁻¹' interior L ∈ 𝓝 (1 : G) :=
      (continuous_const_mul x).continuousAt.preimage_mem_nhds
        (by simpa only [mul_one] using isOpen_interior.mem_nhds hx_int)
    obtain ⟨N, hN⟩ := hV.2 _ hpre
    have hsub_ev : ∀ᶠ n in atTop, x • V n ⊆ interior L := by
      filter_upwards [eventually_ge_atTop N] with n hn
      exact Set.smul_set_subset_iff.mpr fun _ hy ↦ hN (hV.1.2.1 hn hy)
    have havg_eq : ∀ᶠ n in atTop,
        dSequenceAverage (μ.prod μ) (V n ×ˢ V n) (fun p ↦ ρ p.1 * κAdj p) (x, x) =
          conj (dSequenceAverage (μ.prod μ) (V n ×ˢ V n) (fun p ↦ g p.2 * κ p) (x, x)) := by
      filter_upwards [hsub_ev] with n hn
      have hmeasS : MeasurableSet ((x, x) • (V n ×ˢ V n)) :=
        ((hVBorel n).prod (hVBorel n)).const_smul (x, x)
      have hcongr : dSequenceAverage (μ.prod μ) (V n ×ˢ V n) (fun p ↦ ρ p.1 * κAdj p) (x, x) =
          dSequenceAverage (μ.prod μ) (V n ×ˢ V n)
            (fun p ↦ conj ((fun q : G × G ↦ g q.2 * κ q) p.swap)) (x, x) := by
        unfold dSequenceAverage
        rw [setAverage_eq, setAverage_eq]
        refine congrArg _ (setIntegral_congr_fun hmeasS fun p hp ↦ ?_)
        rcases hp with ⟨⟨u, v⟩, ⟨hu, _⟩, rfl⟩
        have hxu : x * u ∈ L := interior_subset (hn ⟨u, hu, rfl⟩)
        have hχu : χ (x * u) = 1 := hχ1 hxu
        change ρ (x * u) * κAdj (x * u, x * v) = conj (g (x * u) * κ (x * v, x * u))
        have hρu : ρ (x * u) = conj (g (x * u)) := by
          simp only [ρ, hχu, Complex.ofReal_one, one_mul]
        rw [hρu]
        exact (map_mul (starRingEnd ℂ) (g (x * u)) (κ (x * v, x * u))).symm
      exact hcongr.trans (dSequenceAverage_conj_swap_diagonal (μ := μ) V (fun q ↦ g q.2 * κ q) x n)
    obtain ⟨v, hv⟩ := hxreg
    have hreg0 : (x, x) ∈ dSequenceRegularSet (μ.prod μ) (fun n ↦ V n ×ˢ V n)
        (fun p ↦ ρ p.1 * κAdj p) := ⟨v, hv⟩
    have hv_eq : v = ρ x * dSequenceKernelSmoothening μ V κAdj (x, x) := by
      have h1 : dSequenceKernelSmoothening μ V (fun p ↦ ρ p.1 * κAdj p) (x, x) = v := by
        simpa only [dSequenceKernelSmoothening, dSequenceSmootheningOrZero, dite_eq_left hreg0,
          dSequenceSmoothening] using hv.limUnder_eq
      exact h1.symm.trans hxval
    have hχx : χ x = 1 := hχ1 (interior_subset hx_int)
    have hlim_conj : Tendsto
        (fun n ↦ conj (dSequenceAverage (μ.prod μ) (V n ×ˢ V n) (fun p ↦ g p.2 * κ p) (x, x)))
        atTop (𝓝 v) := hv.congr' havg_eq
    have hlim : Tendsto
        (fun n ↦ dSequenceAverage (μ.prod μ) (V n ×ˢ V n) (fun p ↦ g p.2 * κ p) (x, x))
        atTop (𝓝 (g x * dSequenceKernelSmoothening μ V κ (x, x))) := by
      have hback := (Complex.continuous_conj.tendsto v).comp hlim_conj
      have htarget : conj v = g x * dSequenceKernelSmoothening μ V κ (x, x) := by
        rw [hv_eq, dSequenceKernelSmoothening_conj_swap_diagonal (μ := μ) V κ x]
        simp only [ρ, hχx, Complex.ofReal_one, one_mul, map_mul, Complex.conj_conj]
      simpa only [Function.comp_def, Complex.conj_conj, htarget] using hback
    have hreg_out :
        (x, x) ∈ dSequenceRegularSet (μ.prod μ) (fun n ↦ V n ×ˢ V n) (fun p ↦ g p.2 * κ p) :=
      ⟨_, hlim⟩
    refine ⟨hreg_out, ?_⟩
    simpa only [dSequenceKernelSmoothening, dSequenceSmootheningOrZero, dite_eq_left hreg_out,
      dSequenceSmoothening] using hlim.limUnder_eq
  filter_upwards [ae_all_iff.2 hloc] with x hx
  have hxU : x ∈ ⋃ m : ℕ, compactCovering G m := by
    rw [iUnion_compactCovering G]
    trivial
  obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hxU
  exact hx m hm

omit hU hBorel in
open scoped ENNReal in
private theorem locallyIntegrable_of_weighted_memLp_prod_sec1b {G : Type*} [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    {μ ν : Measure G} [μ.IsHaarMeasure] [IsFiniteMeasureOnCompacts ν]
    {f : G → ℝ≥0} {k : Lp ℂ 2 (ν.prod ν)} {κ : G × G → ℂ}
    (hκ : κ =ᵐ[ν.prod ν] k) (hf : Continuous f) (hf_pos : ∀ x, 0 < f x)
    (hν : ν = μ.withDensity (fun x ↦ ↑(f x))) :
    LocallyIntegrable κ (μ.prod μ) := by
  let w (p : G × G) := f p.1 * f p.2
  have hw : Continuous w := (hf.comp continuous_fst).mul (hf.comp continuous_snd)
  have hwpos (p : G × G) : 0 < (w p : ℝ) := by
    exact_mod_cast mul_pos (hf_pos p.1) (hf_pos p.2)
  have hprod : ν.prod ν = (μ.prod μ).withDensity (fun p ↦ (w p : ENNReal)) := by
    rw [hν]
    have hm : Measurable (fun x ↦ (f x : ENNReal)) := (ENNReal.continuous_coe.comp hf).measurable
    simpa only [w, ENNReal.coe_mul] using (prod_withDensity (μ := μ) (ν := μ) hm hm)
  have hloc := ((Lp.memLp k).locallyIntegrable one_le_two).congr hκ.symm
  have hweighted : LocallyIntegrable (fun p ↦ (w p : ℝ) • κ p) (μ.prod μ) := by
    apply locallyIntegrable_iff.mpr
    intro K hK
    have hi := hloc.integrableOn_isCompact hK
    rw [IntegrableOn, hprod, restrict_withDensity hK.measurableSet] at hi
    exact (integrable_withDensity_iff_integrable_smul hw.measurable).mp hi
  have hinv : Continuous (fun p ↦ (w p : ℝ)⁻¹) :=
    (NNReal.continuous_coe.comp hw).inv₀ (fun p ↦ (hwpos p).ne')
  refine (hweighted.continuous_smul hinv).congr (Filter.Eventually.of_forall fun p ↦ ?_)
  simp only [smul_smul, inv_mul_cancel₀ (hwpos p).ne', one_smul]

omit hU hBorel in
private theorem integralKernelOperator_surjective_sec1b {X : Type*}
    [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    (ν : Measure X) [IsFiniteMeasureOnCompacts ν] [Measure.InnerRegular ν]
    (A : hilbertSchmidtOperators (Lp ℂ 2 ν) (Lp ℂ 2 ν)) :
    ∃ K : Lp ℂ 2 (ν.prod ν), integralKernelOperator ν K = A := by
  let swap := Measure.measurePreserving_swap (μ := ν) (ν := ν)
  let e := (hilbertSchmidtOperators_equiv_Lp_prod ν ν).choose
  refine ⟨Lp.compMeasurePreserving Prod.swap swap (e.symm A), ?_⟩
  unfold integralKernelOperator
  have hinv : Lp.compMeasurePreserving Prod.swap swap
      (Lp.compMeasurePreserving Prod.swap swap (e.symm A)) = e.symm A := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_compMeasurePreserving
        (Lp.compMeasurePreserving Prod.swap swap (e.symm A)) swap,
      swap.quasiMeasurePreserving.ae (Lp.coeFn_compMeasurePreserving (e.symm A) swap)] with p h1 h2
    rw [h1, Function.comp_apply, h2, Function.comp_apply, Prod.swap_swap]
  rw [hinv]
  exact e.apply_symm_apply A

omit hU hBorel in
private theorem clm_comp_mul_eq_sec1b {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {M₁ M₂ P A T : E →L[ℂ] E} (hM : M₁ = M₂) (hT : T = P.comp A) :
    (M₁.comp P).comp A = M₂ * T := by
  subst hM hT
  ext x
  rfl

section GlobalKernels

variable (a : ℝ) {s : ℝ} (hs : 3 ≤ s)
  (φ : BruhatCompactSupport (IdeleClassGroup (𝓞 F) F))

local notation "Tspec" => (spectralProjection (F := F) a hline hs₀(hs)).comp
  (hardySobolevTestAction μ𝔽 m𝔽 _ _ _ hbase hs₀(hs) φ)
local notation "Tgeom(" hρ ")" => geometricTruncatedConvolution (F := F) a hline hs₀(hs) hρ φ

local notation "kspec" =>
  (globalLineSpectralKernel (F := F) a hs₁(hs) φ : C𝔽 × C𝔽 → ℂ)
local notation "kgeom" => globalLineGeometricKernel (F := F) a hs₁(hs) φ

-- TODO(paper-gap): On p. 503 the proof applies the weighted L² trace theorem
-- to the Haar kernels directly. The actual Hilbert-Schmidt representatives
-- in Theorem 10.4.3.4 carry the reciprocal input weight. Its effect on the
-- diagonal smoothening must be justified for Haar-almost every center.

omit hU hBorel in
private theorem continuous_logNorm_sec1b :
    Continuous (fun g : C𝔽 ↦ logNorm g) :=
  ((NNReal.continuous_coe.comp (Units.continuous_val.comp
    (isProperMap_ideleClassNorm F).continuous))).log fun _ ↦
      ne_of_gt (NNReal.coe_pos.mpr (Units.zero_lt _))

omit hU hBorel in
private theorem continuous_wline_sec1b (s : ℝ) :
    Continuous (fun g : C𝔽 ↦ intervalSobolevDensity (-(0 : ℝ)) 0 s (logNorm g)) := by
  have hw : Continuous (intervalSobolevDensity (-(0 : ℝ)) 0 s) := by
    unfold intervalSobolevDensity
    refine Continuous.mul (by fun_prop) (Continuous.rpow_const (by fun_prop) fun _ ↦ Or.inl ?_)
    positivity
  exact hw.comp (continuous_logNorm_sec1b (F := F))

omit hU hBorel in
private theorem pos_wline_sec1b (s : ℝ) (g : C𝔽) :
    0 < intervalSobolevDensity (-(0 : ℝ)) 0 s (logNorm g) := by
  unfold intervalSobolevDensity
  have h1 : 0 < max (Real.exp (2 * -(0 : ℝ) * logNorm g)) (Real.exp (2 * 0 * logNorm g)) := by
    simp
  have h2 : 0 < (1 + (logNorm g) ^ 2) ^ (s / 2) := by positivity
  exact mul_pos h1 h2

open scoped ENNReal in
private theorem globalLineSpectralKernel_diagonal_setup (_ha : 0 < a) :
    let w : C𝔽 → ℝ := fun g ↦ intervalSobolevDensity (-(0 : ℝ)) 0 s (logNorm g)
    let κHS : C𝔽 × C𝔽 → ℂ := fun p ↦ ((w p.2)⁻¹ : ℝ) • kspec p
    LocallyIntegrable kspec ((μ𝔽).prod μ𝔽) ∧
      (∀ᵐ x ∂μ𝔽, (x, x) ∈ regular(kspec) ∧
        diagonal(kspec) x = (w x : ℂ) * diagonal(κHS) x) := by
  intro w κHS
  let ν : Measure C𝔽 := (μ𝔽).withDensity (fun g ↦ ENNReal.ofReal (w g))
  have hw_cont : Continuous w := continuous_wline_sec1b (F := F) s
  have hw_pos : ∀ g : C𝔽, 0 < w g := pos_wline_sec1b (F := F) s
  let fNN : C𝔽 → ℝ≥0 := fun g ↦ ⟨w g, (hw_pos g).le⟩
  have hf_cont : Continuous fNN := hw_cont.subtype_mk _
  have hf_pos : ∀ g : C𝔽, 0 < fNN g := hw_pos
  have hν : ν = (μ𝔽).withDensity (fun g ↦ (fNN g : ENNReal)) :=
    congrArg (μ𝔽).withDensity (funext fun g ↦ ENNReal.ofReal_eq_coe_nnreal (hw_pos g).le)
  let : IsLocallyFiniteMeasure ν := sobolevKernelWeight_locallyFinite (F := F) 0 s
  obtain ⟨hT, -, -⟩ := spectralProjection_convolution_trace (F := F) a hline hs₀(hs) hs φ
  have hHS := spectralLineKernel_hilbertSchmidt (F := F) a hs₁(hs) φ _ha
  obtain ⟨hk, hk_op⟩ := hHS
  have hκHS : κHS =ᵐ[ν.prod ν] hk.toLp κHS := hk.coeFn_toLp.symm
  have hT_HS : IsNuclearOperator (integralKernelOperator ν (hk.toLp κHS)).val :=
    (congrArg (fun L : W(s) →L[ℂ] W(s) ↦ IsNuclearOperator L) hk_op).mpr hT
  have hmul_eq : (fun p : C𝔽 × C𝔽 ↦ (w p.2 : ℂ) * κHS p) = kspec := by
    funext p
    simp only [κHS, Complex.real_smul, Complex.ofReal_inv]
    exact mul_inv_cancel_left₀ (Complex.ofReal_ne_zero.mpr (hw_pos p.2).ne') _
  have hloc_HS : LocallyIntegrable κHS ((μ𝔽).prod μ𝔽) :=
    locallyIntegrable_of_weighted_memLp_prod_sec1b hκHS hf_cont hf_pos hν
  have hloc_spec : LocallyIntegrable kspec ((μ𝔽).prod μ𝔽) := by
    rw [← hmul_eq]
    have hcont2 : Continuous (fun p : C𝔽 × C𝔽 ↦ (w p.2 : ℂ)) :=
      Complex.continuous_ofReal.comp (hw_cont.comp continuous_snd)
    simpa only [smul_eq_mul] using hloc_HS.continuous_smul hcont2
  have hae := dSequenceKernelSmoothening_mul_continuous_snd_diagonal hU hBorel hf_cont hf_pos hν
    hκHS hT_HS (fun x ↦ (w x : ℂ)) (Complex.continuous_ofReal.comp hw_cont)
  rw [hmul_eq] at hae
  exact ⟨hloc_spec, hae⟩

open scoped Pointwise in
private theorem ae_diagonal_globalLineGeometricKernel_eq_sub (_ha : 0 < a) :
    ∀ᵐ x ∂μ𝔽, (x, x) ∈ regular(kgeom) ∧ diagonal(kgeom) x = φ.val 1 - diagonal(kspec) x := by
  obtain ⟨hloc_spec, hae_spec⟩ :=
    globalLineSpectralKernel_diagonal_setup hU hBorel a hs φ _ha
  have rectSeq [m : MeasurableSpace (C𝔽 × C𝔽)] (hm : m = borel _)
      (η : Measure (C𝔽 × C𝔽)) [η.IsHaarMeasure]
      (hrect : ∀ v w : Set C𝔽, MeasurableSet v → MeasurableSet w →
        η (v ×ˢ w) = (μ𝔽) v * (μ𝔽) w) :
      IsDPrimeSequence η (fun n ↦ U n ×ˢ U n) := by
    subst m
    exact IsDPrimeSequence.prod hrect hU hU
  have hseq : IsDPrimeSequence ((μ𝔽).prod μ𝔽) (fun n ↦ U n ×ˢ U n) :=
    rectSeq BorelSpace.measurable_eq _ (fun v w _ _ ↦ Measure.prod_prod v w)
  filter_upwards [hae_spec] with x ⟨hxreg, _⟩
  obtain ⟨hconv_int, hconv_lim⟩ := diagonal_mem_convolutionKernelRegularSet_averages hU hBorel φ x
  obtain ⟨W, hW, hiW⟩ := hloc_spec (x, x)
  have hpre : (fun y : C𝔽 × C𝔽 ↦ (x, x) * y) ⁻¹' W ∈ 𝓝 (1 : C𝔽 × C𝔽) :=
    (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds (by simpa using hW)
  obtain ⟨N, hN⟩ := hseq.2 _ hpre
  have hspec_int : ∀ᶠ n in atTop, IntegrableOn kspec ((x, x) • (U n ×ˢ U n)) ((μ𝔽).prod μ𝔽) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    exact hiW.mono_set (Set.smul_set_subset_iff.mpr fun _ hy ↦ hN (hseq.1.2.1 hn hy))
  obtain ⟨v, hv⟩ := hxreg
  have hreg0 : (x, x) ∈ regular(kspec) := ⟨v, hv⟩
  have hv_eq : dSequenceKernelSmoothening μ𝔽 U kspec (x, x) = v := by
    simpa only [dSequenceKernelSmoothening, dSequenceSmootheningOrZero, dite_eq_left hreg0,
      dSequenceSmoothening] using hv.limUnder_eq
  have hsub_avg : ∀ᶠ n in atTop,
      dSequenceAverage ((μ𝔽).prod μ𝔽) (U n ×ˢ U n) kgeom (x, x) =
        dSequenceAverage ((μ𝔽).prod μ𝔽) (U n ×ˢ U n) convKernel(φ) (x, x) -
          dSequenceAverage ((μ𝔽).prod μ𝔽) (U n ×ˢ U n) kspec (x, x) := by
    filter_upwards [hconv_int, hspec_int] with n h1 h2
    exact setAverage_fun_sub h1 h2
  have hlim : Tendsto (fun n ↦ dSequenceAverage ((μ𝔽).prod μ𝔽) (U n ×ˢ U n) kgeom (x, x))
      atTop (𝓝 (φ.val 1 - v)) :=
    (hconv_lim.sub hv).congr' (hsub_avg.mono fun _ h ↦ h.symm)
  have hreg_g : (x, x) ∈ regular(kgeom) := ⟨φ.val 1 - v, hlim⟩
  refine ⟨hreg_g, ?_⟩
  change dSequenceKernelSmoothening μ𝔽 U kgeom (x, x) =
    φ.val 1 - dSequenceKernelSmoothening μ𝔽 U kspec (x, x)
  rw [hv_eq]
  simpa only [dSequenceKernelSmoothening, dSequenceSmootheningOrZero, dite_eq_left hreg_g,
    dSequenceSmoothening] using hlim.limUnder_eq

/-- Paper: Theorem 12.1.1.3(1), p. 502. The diagonal of the global spectral
kernel is regular for Haar-almost every center.
Deviation: The kernel is the mixed-weight class of Definition 10.4.3.2 in Lean,
whose Haar integral gives spectral projection after convolution. Regularity does
not depend on the representative of that class. -/
theorem ae_diagonal_mem_globalLineSpectralKernelRegularSet (_ha : 0 < a) :
    ∀ᵐ x ∂μ𝔽, (x, x) ∈ regular(kspec) := by
  obtain ⟨-, hae⟩ := globalLineSpectralKernel_diagonal_setup hU hBorel a hs φ _ha
  exact hae.mono fun _ h ↦ h.1

/-- Paper: Theorem 12.1.1.3(1), p. 502. The diagonal of the global geometric
kernel is regular for Haar-almost every center. -/
theorem ae_diagonal_mem_globalLineGeometricKernelRegularSet (_ha : 0 < a) :
    ∀ᵐ x ∂μ𝔽, (x, x) ∈ regular(kgeom) := by
  exact (ae_diagonal_globalLineGeometricKernel_eq_sub hU hBorel a hs φ _ha).mono fun _ h ↦ h.1

/-- Paper: Theorem 12.1.1.3(2), p. 502. In (12.1.1.20), geometric
truncation after convolution is trace class. Its trace is the Haar integral
of the cutoff times the smoothened geometric diagonal.
Deviation: The cutoff is any real cutoff of Definition 9.3.3.1, smooth or not,
as Theorem 12.1.1.2(2) allows bounded symbols; this is the form the limit
(12.1.1.22) and the sharp band of Remark 12.1.1.4 use. Absolute integrability
of the trace integrand is explicit. -/
theorem geometricTruncatedConvolution_trace_eq_integral_globalDiagonal (_ha : 0 < a)
    {Λ ε : ℝ} {ρ : C𝔽 → ℝ} (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) (_hband : innerBand(Λ, ε)) :
    let T := Tgeom(hρ)
    ∃ hT : IsNuclearOperator T,
      Integrable (fun x ↦ (ρ x : ℂ) * diagonal(kgeom) x) μ𝔽 ∧
      hilbertTrace (H := W(s)) ⟨T, hT⟩ =
        ∫ x, (ρ x : ℂ) * diagonal(kgeom) x ∂μ𝔽 := by
  intro T
  let w : C𝔽 → ℝ := fun g ↦ intervalSobolevDensity (-(0 : ℝ)) 0 s (logNorm g)
  let ν : Measure C𝔽 := (μ𝔽).withDensity (fun g ↦ ENNReal.ofReal (w g))
  let κHS : C𝔽 × C𝔽 → ℂ := fun p ↦ ((w p.2)⁻¹ : ℝ) • kspec p
  have hw_cont : Continuous w := continuous_wline_sec1b (F := F) s
  have hw_pos : ∀ g : C𝔽, 0 < w g := pos_wline_sec1b (F := F) s
  let fNN : C𝔽 → ℝ≥0 := fun g ↦ ⟨w g, (hw_pos g).le⟩
  have hf_cont : Continuous fNN := hw_cont.subtype_mk _
  have hf_pos : ∀ g : C𝔽, 0 < fNN g := hw_pos
  have hν : ν = (μ𝔽).withDensity (fun g ↦ (fNN g : ENNReal)) :=
    congrArg (μ𝔽).withDensity (funext fun g ↦ ENNReal.ofReal_eq_coe_nnreal (hw_pos g).le)
  let : IsLocallyFiniteMeasure ν := sobolevKernelWeight_locallyFinite (F := F) 0 s
  obtain ⟨hTspec, hquot, -⟩ := spectralProjection_convolution_trace (F := F) a hline hs₀(hs) hs φ
  obtain ⟨hTfull, hTgeom, hTspec_trunc, hsplit⟩ :=
    truncatedConvolution_trace_split (F := F) a hline hs₀(hs) hρ _hband φ hquot
  have hφs : IsBruhatSmooth φ.val := (mem_bruhatSmoothSubmodule_iff _).mp φ.property.1
  have hφc : Continuous φ.val :=
    schwartzBruhat_continuous
      (⟨φ.val, bruhatCompactSupport_mem_schwartz φ.property⟩ : SchwartzBruhat C𝔽)
  have hφb := hφc.bounded_above_of_compact_support (show HasCompactSupport φ.val from φ.property.2)
  have hm : IsModulation m𝔽 := ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
  have hsur : Function.Surjective m𝔽 := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.2.2.2.1
  obtain ⟨hTconv, hint1, htr1⟩ := truncatedHardySobolevConvolution_trace μ𝔽 m𝔽 (-(0 : ℝ)) 0 s hbase
    hs₀(hs) φ.val hφc.aemeasurable φ.property.2 hφb hm hsur hφs hρ _hband
  have hconv_eq :=
    hardySobolevConvolution_eq_testAction μ𝔽 m𝔽 (-(0 : ℝ)) 0 s hbase hs₀(hs) φ hφc.aemeasurable hφb
  have htr_full :
      hilbertTrace (H := W(s))
        ⟨(modulatedCutoffOperator m𝔽 ν hρ).comp
          (hardySobolevTestAction μ𝔽 m𝔽 _ _ _ hbase hs₀(hs) φ), hTfull⟩ =
        ∫ x, (ρ x : ℂ) * φ.val 1 ∂μ𝔽 := by
    have hsub : (⟨(modulatedCutoffOperator m𝔽 ν hρ).comp
          (hardySobolevTestAction μ𝔽 m𝔽 _ _ _ hbase hs₀(hs) φ), hTfull⟩ :
          nuclearEndomorphisms (W(s))) =
        ⟨(modulatedCutoffOperator m𝔽 ν hρ).comp
          (hardySobolevConvolution μ𝔽 m𝔽 (-(0 : ℝ)) 0 s hbase hs₀(hs) φ.val
            hφc.aemeasurable φ.property.2 hφb), hTconv⟩ :=
      Subtype.ext (congrArg (modulatedCutoffOperator m𝔽 ν hρ).comp hconv_eq.symm)
    exact (congrArg (hilbertTrace (H := W(s))) hsub).trans htr1
  obtain ⟨hk, hk_op⟩ := spectralLineKernel_hilbertSchmidt (F := F) a hs₁(hs) φ _ha
  obtain ⟨-, hae_spec⟩ :=
    globalLineSpectralKernel_diagonal_setup hU hBorel a hs φ _ha
  have hκHS : κHS =ᵐ[ν.prod ν] hk.toLp κHS := hk.coeFn_toLp.symm
  have hT_HS : IsNuclearOperator (integralKernelOperator ν (hk.toLp κHS)).val :=
    (congrArg (fun L : W(s) →L[ℂ] W(s) ↦ IsNuclearOperator L) hk_op).mpr hTspec
  have hρ_mem : MemLp (fun x : C𝔽 ↦ (ρ x : ℂ)) ⊤ ν :=
    memLp_top_of_bound (Complex.measurable_ofReal.comp hρ.measurable).aestronglyMeasurable 1
      (Eventually.of_forall fun x ↦ by simpa [Real.norm_eq_abs] using hρ.abs_le_one x)
  let ρLp : Lp ℂ ⊤ ν := hρ_mem.toLp (fun x : C𝔽 ↦ (ρ x : ℂ))
  have hMρ_eq :
      modulatedCutoffOperator m𝔽 ν hρ = (ContinuousLinearMap.mul ℂ ℂ).holderL ν ⊤ 2 2 ρLp := by
    ext1 u
    apply Lp.ext
    have hM : ⇑(((ContinuousLinearMap.mul ℂ ℂ).holderL ν ⊤ 2 2 ρLp) u) =ᵐ[ν]
        fun x ↦ ρLp x * u x :=
      (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2) ρLp u
    filter_upwards [modulatedCutoffOperator_apply m𝔽 ν hρ u, hM, hρ_mem.coeFn_toLp] with x h1 h2 h3
    rw [h1, h2, h3]
  obtain ⟨hint_HS, htr_HS⟩ :=
    integral_mul_dSequenceKernelSmoothening_diagonal hκHS hU hBorel hf_cont hf_pos hν hT_HS ρLp
  have hμ_ac : μ𝔽 ≪ ν := by
    rw [hν]
    exact withDensity_absolutelyContinuous' hf_cont.measurable.coe_nnreal_ennreal.aemeasurable
      (Eventually.of_forall fun x ↦ by simpa using (hf_pos x).ne')
  have hpt_spec :
      (fun x ↦ fNN x • ((ρLp : C𝔽 → ℂ) x * diagonal(κHS) x)) =ᵐ[μ𝔽]
        fun x ↦ (ρ x : ℂ) * diagonal(kspec) x := by
    filter_upwards [hμ_ac.ae_le hρ_mem.coeFn_toLp, hae_spec] with x hρx hspecx
    rw [hρx, hspecx.2]
    change (w x : ℝ) • ((ρ x : ℂ) * diagonal(κHS) x) = (ρ x : ℂ) * ((w x : ℂ) * diagonal(κHS) x)
    rw [Complex.real_smul]
    ring
  have hint2 : Integrable (fun x ↦ (ρ x : ℂ) * diagonal(kspec) x) μ𝔽 := by
    have hint_HS' : Integrable (fun x ↦ (ρLp : C𝔽 → ℂ) x * diagonal(κHS) x)
        ((μ𝔽).withDensity (fun g ↦ (fNN g : ENNReal))) :=
      (congrArg (fun σ ↦ Integrable (fun x ↦ (ρLp : C𝔽 → ℂ) x * diagonal(κHS) x) σ) hν).mp hint_HS
    exact ((integrable_withDensity_iff_integrable_smul hf_cont.measurable).mp hint_HS').congr
      hpt_spec
  have htr2 :
      hilbertTrace (H := W(s)) ⟨spectralTruncatedConvolution (F := F) a hline hs₀(hs) hρ φ,
        hTspec_trunc⟩ = ∫ x, (ρ x : ℂ) * diagonal(kspec) x ∂μ𝔽 := by
    have hsub : (⟨spectralTruncatedConvolution (F := F) a hline hs₀(hs) hρ φ, hTspec_trunc⟩ :
          nuclearEndomorphisms (W(s))) =
        ⟨(ContinuousLinearMap.mul ℂ ℂ).holderL ν ⊤ 2 2 ρLp *
            (integralKernelOperator ν (hk.toLp κHS)).val,
          mul_mem_nuclearEndomorphisms_left _ ⟨_, hT_HS⟩⟩ := by
      apply Subtype.ext
      unfold spectralTruncatedConvolution spectralTruncation
      exact clm_comp_mul_eq_sec1b hMρ_eq hk_op
    calc
      hilbertTrace (H := W(s)) ⟨spectralTruncatedConvolution (F := F) a hline hs₀(hs) hρ φ,
          hTspec_trunc⟩ =
          ∫ x, (ρLp : C𝔽 → ℂ) x * diagonal(κHS) x ∂ν :=
        (congrArg (hilbertTrace (H := W(s))) hsub).trans htr_HS.symm
      _ = ∫ x, (ρLp : C𝔽 → ℂ) x * diagonal(κHS) x ∂((μ𝔽).withDensity (fun g ↦ (fNN g : ENNReal))) :=
        congrArg (fun σ ↦ ∫ x, (ρLp : C𝔽 → ℂ) x * diagonal(κHS) x ∂σ) hν
      _ = ∫ x, fNN x • ((ρLp : C𝔽 → ℂ) x * diagonal(κHS) x) ∂μ𝔽 :=
        integral_withDensity_eq_integral_smul hf_cont.measurable
          (fun x ↦ (ρLp : C𝔽 → ℂ) x * diagonal(κHS) x)
      _ = ∫ x, (ρ x : ℂ) * diagonal(kspec) x ∂μ𝔽 := integral_congr_ae hpt_spec
  have hpt_geom :
      (fun x ↦ (ρ x : ℂ) * diagonal(kgeom) x) =ᵐ[μ𝔽]
        fun x ↦ (ρ x : ℂ) * φ.val 1 - (ρ x : ℂ) * diagonal(kspec) x := by
    filter_upwards [ae_diagonal_globalLineGeometricKernel_eq_sub hU hBorel a hs φ _ha] with x hx
    rw [hx.2, mul_sub]
  refine ⟨hTgeom, (hint1.sub hint2).congr hpt_geom.symm, ?_⟩
  calc
    hilbertTrace (H := W(s)) ⟨T, hTgeom⟩ =
        hilbertTrace (H := W(s)) ⟨(modulatedCutoffOperator m𝔽 ν hρ).comp
          (hardySobolevTestAction μ𝔽 m𝔽 _ _ _ hbase hs₀(hs) φ), hTfull⟩ -
        hilbertTrace (H := W(s)) ⟨spectralTruncatedConvolution (F := F) a hline hs₀(hs) hρ φ,
          hTspec_trunc⟩ := eq_sub_of_add_eq hsplit.symm
    _ = (∫ x, (ρ x : ℂ) * φ.val 1 ∂μ𝔽) - ∫ x, (ρ x : ℂ) * diagonal(kspec) x ∂μ𝔽 :=
        congrArg₂ (· - ·) htr_full htr2
    _ = ∫ x, ((ρ x : ℂ) * φ.val 1 - (ρ x : ℂ) * diagonal(kspec) x) ∂μ𝔽 :=
        (integral_sub hint1 hint2).symm
    _ = ∫ x, (ρ x : ℂ) * diagonal(kgeom) x ∂μ𝔽 :=
        integral_congr_ae hpt_geom.symm

/-- Paper: Theorem 12.1.1.3(2), p. 503. In (12.1.1.21), spectral
projection after convolution is trace class. Its trace is the Haar integral
of the smoothened spectral diagonal.
Deviation: Absolute integrability of the smoothened diagonal is explicit. -/
theorem spectralProjection_convolution_trace_eq_integral_globalDiagonal (_ha : 0 < a) :
    let T := Tspec
    ∃ hT : IsNuclearOperator T,
      Integrable diagonal(kspec) μ𝔽 ∧
      hilbertTrace (H := W(s)) ⟨T, hT⟩ = ∫ x, diagonal(kspec) x ∂μ𝔽 := by
  intro T
  let w : C𝔽 → ℝ := fun g ↦ intervalSobolevDensity (-(0 : ℝ)) 0 s (logNorm g)
  let ν : Measure C𝔽 := (μ𝔽).withDensity (fun g ↦ ENNReal.ofReal (w g))
  let κHS : C𝔽 × C𝔽 → ℂ := fun p ↦ ((w p.2)⁻¹ : ℝ) • kspec p
  have hw_cont : Continuous w := continuous_wline_sec1b (F := F) s
  have hw_pos : ∀ g : C𝔽, 0 < w g := pos_wline_sec1b (F := F) s
  let fNN : C𝔽 → ℝ≥0 := fun g ↦ ⟨w g, (hw_pos g).le⟩
  have hf_cont : Continuous fNN := hw_cont.subtype_mk _
  have hf_pos : ∀ g : C𝔽, 0 < fNN g := hw_pos
  have hν : ν = (μ𝔽).withDensity (fun g ↦ (fNN g : ENNReal)) :=
    congrArg (μ𝔽).withDensity (funext fun g ↦ ENNReal.ofReal_eq_coe_nnreal (hw_pos g).le)
  let : IsLocallyFiniteMeasure ν := sobolevKernelWeight_locallyFinite (F := F) 0 s
  obtain ⟨hT, -, -⟩ := spectralProjection_convolution_trace (F := F) a hline hs₀(hs) hs φ
  obtain ⟨hk, hk_op⟩ := spectralLineKernel_hilbertSchmidt (F := F) a hs₁(hs) φ _ha
  obtain ⟨-, hae_spec⟩ :=
    globalLineSpectralKernel_diagonal_setup hU hBorel a hs φ _ha
  have hκHS : κHS =ᵐ[ν.prod ν] hk.toLp κHS := hk.coeFn_toLp.symm
  have hT_HS : IsNuclearOperator (integralKernelOperator ν (hk.toLp κHS)).val :=
    (congrArg (fun L : W(s) →L[ℂ] W(s) ↦ IsNuclearOperator L) hk_op).mpr hT
  obtain ⟨hint_HS, htr_HS⟩ :=
    integral_dSequenceKernelSmoothening_diagonal hκHS hU hBorel hf_cont hf_pos hν hT_HS
  have hpt : (fun x ↦ fNN x • diagonal(κHS) x) =ᵐ[μ𝔽] diagonal(kspec) := by
    filter_upwards [hae_spec] with x hx
    rw [hx.2]
    change (w x : ℝ) • diagonal(κHS) x = (w x : ℂ) * diagonal(κHS) x
    rw [Complex.real_smul]
  refine ⟨hT, ?_, ?_⟩
  · rw [hν, integrable_withDensity_iff_integrable_smul hf_cont.measurable] at hint_HS
    exact hint_HS.congr hpt
  · have hsub : (⟨T, hT⟩ : nuclearEndomorphisms (W(s))) =
        ⟨(integralKernelOperator ν (hk.toLp κHS)).val, hT_HS⟩ := Subtype.ext hk_op.symm
    calc
      hilbertTrace (H := W(s)) ⟨T, hT⟩ = ∫ x, diagonal(κHS) x ∂ν :=
        (congrArg (hilbertTrace (H := W(s))) hsub).trans htr_HS.symm
      _ = ∫ x, fNN x • diagonal(κHS) x ∂μ𝔽 := by
        rw [hν, integral_withDensity_eq_integral_smul hf_cont.measurable]
      _ = ∫ x, diagonal(kspec) x ∂μ𝔽 := integral_congr_ae hpt

-- TODO(paper-gap): The citation of Theorem 10.4.3.1(4) for integrability
-- points to an enumeration condition. Theorem 10.4.3.4(4), cited in the
-- following remark for the same assertion, has no part (4).

omit hU hBorel in
open scoped Pointwise in
/-- When the convolution part has zero diagonal average, the geometric and spectral
smoothenings are opposite, including at irregular points where both are defined to be zero. -/
private theorem integrable_globalLineGeometricKernel_diagonal_eq_neg_spectral
    {F : Type*} [Field F] [NumberField F]
    {U : ℕ → Set (IdeleClassGroup (𝓞 F) F)}
    (hU : IsDPrimeSequence (ideleClassTamagawaMeasure F) U)
    (hBorel : ∀ n, MeasurableSet (U n))
    (a : ℝ) {s : ℝ} (hs : 3 ≤ s)
    (φ : BruhatCompactSupport (IdeleClassGroup (𝓞 F) F))
    (hφ : φ.val 1 = 0) (x : IdeleClassGroup (𝓞 F) F) :
    dSequenceKernelSmoothening (ideleClassTamagawaMeasure F) U
      (globalLineGeometricKernel (F := F) a hs₁(hs) φ) (x, x) =
      -dSequenceKernelSmoothening (ideleClassTamagawaMeasure F) U
        (globalLineSpectralKernel (F := F) a hs₁(hs) φ :
          (IdeleClassGroup (𝓞 F) F) × (IdeleClassGroup (𝓞 F) F) → ℂ) (x, x) := by
  classical
  let G := IdeleClassGroup (𝓞 F) F
  let μ : Measure (G × G) :=
    (ideleClassTamagawaMeasure F).prod (ideleClassTamagawaMeasure F)
  let V : ℕ → Set (G × G) := fun n ↦ U n ×ˢ U n
  let f : G × G → ℂ := fun y ↦ φ.val (y.1 * y.2⁻¹)
  let g : G × G → ℂ := globalLineSpectralKernel (F := F) a hs₁(hs) φ
  let p : G × G := (x, x)
  change dSequenceSmootheningOrZero μ V (fun y ↦ f y - g y) p =
    -dSequenceSmootheningOrZero μ V g p
  obtain ⟨hf, hlim⟩ := diagonal_mem_convolutionKernelRegularSet_averages hU hBorel φ x
  change ∀ᶠ n in atTop, IntegrableOn f (p • V n) μ at hf
  change Tendsto (fun n ↦ dSequenceAverage μ (V n) f p) atTop (𝓝 (φ.val 1)) at hlim
  rw [hφ] at hlim
  have hsum : Tendsto (fun n ↦
      dSequenceAverage μ (V n) (fun y ↦ f y - g y) p +
        dSequenceAverage μ (V n) g p) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (by simpa only [norm_zero] using hlim.norm)
    filter_upwards [hf] with n hn
    by_cases hg : IntegrableOn g (p • V n) μ
    · change ‖(⨍ y in p • V n, f y - g y ∂μ) +
          (⨍ y in p • V n, g y ∂μ)‖ ≤ ‖⨍ y in p • V n, f y ∂μ‖
      rw [setAverage_fun_sub hn hg, sub_add_cancel]
    · -- If the spectral integral is undefined, both totalized averages vanish.
      have hfg : ¬ IntegrableOn (fun y ↦ f y - g y) (p • V n) μ := by
        intro h
        apply hg
        simpa only [Pi.sub_def, sub_sub_cancel] using hn.sub h
      have hzero : dSequenceAverage μ (V n) g p = 0 := by
        rw [dSequenceAverage, setAverage_eq, integral_undef hg, smul_zero]
      have hsubzero : dSequenceAverage μ (V n) (fun y ↦ f y - g y) p = 0 := by
        rw [dSequenceAverage, setAverage_eq, integral_undef hfg, smul_zero]
      rw [hzero, hsubzero, zero_add, norm_zero]
      exact norm_nonneg _
  by_cases hg : p ∈ dSequenceRegularSet μ V g
  · obtain ⟨v, hv⟩ := hg
    have hgreg : p ∈ dSequenceRegularSet μ V g := ⟨v, hv⟩
    have hsub : Tendsto (fun n ↦ dSequenceAverage μ (V n) (fun y ↦ f y - g y) p)
        atTop (𝓝 (-v)) := by
      simpa only [add_sub_cancel_right, zero_sub] using hsum.sub hv
    have hreg : p ∈ dSequenceRegularSet μ V (fun y ↦ f y - g y) := ⟨-v, hsub⟩
    simp only [dSequenceSmootheningOrZero, dite_eq_left hreg, dite_eq_left hgreg,
      dSequenceSmoothening, hsub.limUnder_eq, hv.limUnder_eq]
  · have hreg : p ∉ dSequenceRegularSet μ V (fun y ↦ f y - g y) := by
      rintro ⟨v, hv⟩
      apply hg
      refine ⟨-v, ?_⟩
      simpa only [add_sub_cancel_left, zero_sub] using hsum.sub hv
    simp only [dSequenceSmootheningOrZero, dite_eq_right hreg, dite_eq_right hg, neg_zero]

/-- Paper: Theorem 12.1.1.3(3), p. 503. When the test vanishes at the
identity, the smoothened geometric diagonal is absolutely Haar integrable. -/
theorem integrable_globalLineGeometricKernel_diagonal (_ha : 0 < a) (_hφ : φ.val 1 = 0) :
    Integrable diagonal(kgeom) μ𝔽 := by
  obtain ⟨_, hi, _⟩ :=
    spectralProjection_convolution_trace_eq_integral_globalDiagonal hU hBorel a hs φ _ha
  have heq : diagonal(kgeom) = fun x ↦ -diagonal(kspec) x := by
    funext x
    exact integrable_globalLineGeometricKernel_diagonal_eq_neg_spectral hU hBorel a hs φ _hφ x
  rw [heq]
  exact hi.neg

private theorem tendsto_integral_cutoff_globalLineGeometricKernel_diagonal_aux (_ha : 0 < a)
    (_hφ : φ.val 1 = 0) {ι : Type*} {l : Filter ι} (Λ ε : ι → ℝ) (ρ : ι → C𝔽 → ℝ)
    (_hΛ : Tendsto Λ l atTop) (_hε : Tendsto (fun i ↦ ε i * Λ i) l (𝓝 0))
    (_hρ : ∀ᶠ i in l, IsModulatedCutoff m𝔽 (Λ i) (ε i) (ρ i) ∧ innerBand(Λ i, ε i)) :
    Tendsto (fun i ↦ ∫ x, (ρ i x : ℂ) * diagonal(kgeom) x ∂μ𝔽) l
      (𝓝 (∫ x, diagonal(kgeom) x ∂μ𝔽)) := by
  let D : C𝔽 → ℂ := diagonal(kgeom)
  have hD : Integrable D μ𝔽 :=
    integrable_globalLineGeometricKernel_diagonal hU hBorel a hs φ _ha _hφ
  let K (N : ℕ) : Set C𝔽 :=
    (fun x : C𝔽 ↦ ((m𝔽 x).val : ℝ)) ⁻¹' Icc (N : ℝ)⁻¹ (N : ℝ)
  have hm_cont : Continuous (fun x : C𝔽 ↦ ((m𝔽 x).val : ℝ)) :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous)
  have hKm (N : ℕ) : MeasurableSet (K N) := measurableSet_Icc.preimage hm_cont.measurable
  have htail : Tendsto (fun N : ℕ ↦ ∫ x, (K N)ᶜ.indicator (fun x ↦ ‖D x‖) x ∂μ𝔽)
      atTop (𝓝 0) := by
    have h0 : (∫ _ : C𝔽, (0 : ℝ) ∂μ𝔽) = 0 := integral_zero _ _
    rw [← h0]
    apply tendsto_integral_of_dominated_convergence (fun x ↦ ‖D x‖)
    · exact fun N ↦ hD.norm.aestronglyMeasurable.indicator (hKm N).compl
    · exact hD.norm
    · intro N
      refine Eventually.of_forall fun x ↦ ?_
      by_cases hx : x ∈ (K N)ᶜ
      · simp [Set.indicator_of_mem hx]
      · simp [Set.indicator_of_notMem hx]
    · refine Eventually.of_forall fun x ↦ ?_
      have hx : 0 < ((m𝔽 x).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
      obtain ⟨N₀, hN₀⟩ := exists_nat_gt (max ((m𝔽 x).val : ℝ) ((m𝔽 x).val : ℝ)⁻¹)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop (max N₀ 1)] with N hN
      have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast le_trans (le_max_right N₀ 1) hN
      have hNgt : max ((m𝔽 x).val : ℝ) ((m𝔽 x).val : ℝ)⁻¹ < (N : ℝ) :=
        hN₀.trans_le (by exact_mod_cast le_trans (le_max_left N₀ 1) hN)
      have hhi : ((m𝔽 x).val : ℝ) ≤ (N : ℝ) := (le_max_left _ _).trans hNgt.le
      have hlo : (N : ℝ)⁻¹ ≤ ((m𝔽 x).val : ℝ) := by
        have h1 : ((m𝔽 x).val : ℝ)⁻¹ ≤ (N : ℝ) := (le_max_right _ _).trans hNgt.le
        have hpos : (0 : ℝ) < (N : ℝ) := by linarith
        rw [inv_le_comm₀ hpos hx]
        exact h1
      have hxK : x ∈ K N := ⟨hlo, hhi⟩
      simp [Set.indicator_of_notMem (show x ∉ (K N)ᶜ from not_not.mpr hxK)]
  rw [Metric.tendsto_nhds]
  intro δ hδ
  have htail_ev : ∀ᶠ N : ℕ in atTop, ∫ x, (K N)ᶜ.indicator (fun x ↦ ‖D x‖) x ∂μ𝔽 < δ :=
    htail.eventually (Iio_mem_nhds hδ)
  obtain ⟨N, hN1, hNδ⟩ := (eventually_ge_atTop 1 |>.and htail_ev).exists
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hinvΛ : Tendsto (fun i ↦ (Λ i)⁻¹) l (𝓝 0) :=
    (tendsto_inv_atTop_zero (𝕜 := ℝ)).comp _hΛ
  have hε0 : Tendsto ε l (𝓝 0) := by
    have hmul : Tendsto (fun i ↦ (ε i * Λ i) * (Λ i)⁻¹) l (𝓝 (0 * 0)) := _hε.mul hinvΛ
    rw [mul_zero] at hmul
    refine hmul.congr' ?_
    filter_upwards [_hΛ.eventually (eventually_ge_atTop (1 : ℝ))] with i hΛ1
    have hne : Λ i ≠ 0 := by linarith
    field_simp
  have hlow : ∀ᶠ i in l, (Λ i)⁻¹ + ε i ≤ (N : ℝ)⁻¹ := by
    have hsum : Tendsto (fun i ↦ (Λ i)⁻¹ + ε i) l (𝓝 0) := by
      simpa only [add_zero] using hinvΛ.add hε0
    exact hsum.eventually (Iic_mem_nhds (inv_pos.mpr hNpos))
  have hhigh : ∀ᶠ i in l, (N : ℝ) ≤ Λ i - ε i := by
    filter_upwards [_hΛ.eventually (eventually_ge_atTop ((N : ℝ) + 1)),
      hε0.eventually (Iic_mem_nhds (zero_lt_one : (0 : ℝ) < 1))] with i h1 h2
    linarith
  filter_upwards [_hρ, hlow, hhigh] with i ⟨hcut, _⟩ hlo hhi
  have hρ_int : Integrable (fun x ↦ (ρ i x : ℂ) * D x) μ𝔽 := by
    refine hD.norm.mono'
      ((Complex.measurable_ofReal.comp hcut.measurable).aestronglyMeasurable.mul
        hD.aestronglyMeasurable) (Eventually.of_forall fun x ↦ ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right (hcut.abs_le_one x) (norm_nonneg _)).trans_eq (one_mul _)
  rw [dist_eq_norm, ← integral_sub hρ_int hD]
  have hsub_eq : (fun x ↦ (ρ i x : ℂ) * D x - D x) = fun x ↦ ((ρ i x - 1 : ℝ) : ℂ) * D x := by
    funext x
    push_cast
    ring
  rw [hsub_eq]
  have hnorm_le : ‖∫ x, ((ρ i x - 1 : ℝ) : ℂ) * D x ∂μ𝔽‖ ≤
      ∫ x, ‖((ρ i x - 1 : ℝ) : ℂ) * D x‖ ∂μ𝔽 := norm_integral_le_integral_norm _
  have hind_int : Integrable (fun x ↦ (K N)ᶜ.indicator (fun x ↦ ‖D x‖) x) μ𝔽 :=
    hD.norm.indicator (hKm N).compl
  have hpt_le : ∀ x : C𝔽,
      ‖((ρ i x - 1 : ℝ) : ℂ) * D x‖ ≤ (K N)ᶜ.indicator (fun x ↦ ‖D x‖) x := by
    intro x
    by_cases hx : x ∈ K N
    · have h1 : ρ i x = 1 := hcut.eq_one ⟨hlo.trans hx.1, hx.2.trans hhi⟩
      simp [h1, Set.indicator_of_notMem (show x ∉ (K N)ᶜ from not_not.mpr hx)]
    · have hx' : x ∈ (K N)ᶜ := hx
      rw [Set.indicator_of_mem hx', norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have h0 : 0 ≤ ρ i x := hcut.nonneg x
      have h1 : ρ i x ≤ 1 := (abs_le.mp (hcut.abs_le_one x)).2
      have habs : |ρ i x - 1| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
      exact (mul_le_mul_of_nonneg_right habs (norm_nonneg _)).trans_eq (one_mul _)
  have hnorm_int : Integrable (fun x ↦ ‖((ρ i x - 1 : ℝ) : ℂ) * D x‖) μ𝔽 :=
    (hρ_int.sub hD).norm.congr (Eventually.of_forall fun x ↦ congrArg norm (congrFun hsub_eq x))
  exact hnorm_le.trans_lt ((integral_mono hnorm_int hind_int hpt_le).trans_lt hNδ)

/-- Paper: Theorem 12.1.1.3(3), p. 503. In (12.1.1.22), as the radius
tends to infinity and the width times the radius tends to zero, the
geometric truncation traces tend to the Haar mass of the smoothened diagonal.
Deviation: A filter represents the joint limit, with real cutoffs and their
traces specified eventually. The same limit holds for the sharp band in
Remark 12.1.1.4. -/
theorem geometricTruncatedConvolution_trace_tendsto_integral_globalDiagonal (_ha : 0 < a)
    (_hφ : φ.val 1 = 0) {ι : Type*} {l : Filter ι} (Λ ε : ι → ℝ) (ρ : ι → C𝔽 → ℝ)
    (_hΛ : Tendsto Λ l atTop) (_hε : Tendsto (fun i ↦ ε i * Λ i) l (𝓝 0))
    (_hρ : ∀ᶠ i in l, IsModulatedCutoff m𝔽 (Λ i) (ε i) (ρ i) ∧ innerBand(Λ i, ε i)) :
    ∃ traces : ι → ℂ,
      (∀ᶠ i in l, ∃ hcut : IsModulatedCutoff m𝔽 (Λ i) (ε i) (ρ i),
        let T := Tgeom(hcut)
        ∃ hT : IsNuclearOperator T, traces i = hilbertTrace (H := W(s)) ⟨T, hT⟩) ∧
      Tendsto traces l (𝓝 (∫ x, diagonal(kgeom) x ∂μ𝔽)) := by
  refine ⟨fun i ↦ ∫ x, (ρ i x : ℂ) * diagonal(kgeom) x ∂μ𝔽, ?_,
    tendsto_integral_cutoff_globalLineGeometricKernel_diagonal_aux hU hBorel a hs φ _ha _hφ Λ ε ρ
      _hΛ _hε _hρ⟩
  filter_upwards [_hρ] with i ⟨hcut, hband⟩
  obtain ⟨hT, -, htr⟩ :=
    geometricTruncatedConvolution_trace_eq_integral_globalDiagonal hU hBorel a hs φ _ha hcut hband
  exact ⟨hcut, hT, htr.symm⟩

/-- Paper: (12.1.1.23), p. 503. If the test vanishes at the identity, the
smoothened geometric diagonal is the negative of the spectral diagonal.
The smoothening uses the zero extension from Definition 12.1.1.1. -/
theorem globalLineGeometricKernel_diagonal_eq_neg_spectral (_hφ : φ.val 1 = 0) (x : C𝔽) :
    diagonal(kgeom) x = -diagonal(kspec) x := by
  exact integrable_globalLineGeometricKernel_diagonal_eq_neg_spectral hU hBorel a hs φ _hφ x

/-- Paper: (12.1.1.24), p. 503. If the test vanishes at the identity, the
cutoff integrals of the smoothened geometric diagonal converge to its full Haar integral.
Deviation: A filter expresses the joint limit for the radius and width. The
plateau estimate also applies to the two-sided absolute cutoff of Remark 12.1.1.4. -/
theorem tendsto_integral_cutoff_globalLineGeometricKernel_diagonal (_ha : 0 < a)
    (_hφ : φ.val 1 = 0) {ι : Type*} {l : Filter ι} (Λ ε : ι → ℝ) (ρ : ι → C𝔽 → ℝ)
    (_hΛ : Tendsto Λ l atTop) (_hε : Tendsto (fun i ↦ ε i * Λ i) l (𝓝 0))
    (_hρ : ∀ᶠ i in l, IsModulatedCutoff m𝔽 (Λ i) (ε i) (ρ i) ∧ innerBand(Λ i, ε i)) :
    Tendsto (fun i ↦ ∫ x, (ρ i x : ℂ) * diagonal(kgeom) x ∂μ𝔽) l
      (𝓝 (∫ x, diagonal(kgeom) x ∂μ𝔽)) :=
  tendsto_integral_cutoff_globalLineGeometricKernel_diagonal_aux hU hBorel a hs φ _ha _hφ Λ ε ρ
    _hΛ _hε _hρ

-- TODO(paper-gap): The end of the proof cites (10.4.3.31) as its conclusion.
-- The intended conclusion is (12.1.1.22). The geometric kernel formula is
-- (10.4.3.31), while (10.4.3.32) starts a computation of the kernel action.

/-- Paper: Remark 12.1.1.4, pp. 503–504. For a test vanishing at the identity,
the sharp and smooth cutoff masses of the geometric diagonal differ by a
quantity tending to zero in the joint limit of (12.1.1.22). -/
theorem tendsto_absolute_sub_smooth_globalLineGeometricKernel_diagonal (_ha : 0 < a)
    (_hφ : φ.val 1 = 0)
    {ι : Type*} {l : Filter ι} (Λ ε : ι → ℝ) (ρ : ι → C𝔽 → ℝ)
    (_hΛ : Tendsto Λ l atTop) (_hε : Tendsto (fun i ↦ ε i * Λ i) l (𝓝 0))
    (_hρ : ∀ᶠ i in l, IsSmoothModulatedCutoff m𝔽 (Λ i) (ε i) (ρ i) ∧ innerBand(Λ i, ε i)) :
    Tendsto (fun i ↦ (∫ x, (modulatedAbsoluteCutoff m𝔽 (Icc (Λ i)⁻¹ (Λ i)) x : ℂ) *
        diagonal(kgeom) x ∂μ𝔽) - ∫ x, (ρ i x : ℂ) * diagonal(kgeom) x ∂μ𝔽) l (𝓝 0) := by
  let D : C𝔽 → ℂ := diagonal(kgeom)
  have hD : Integrable D μ𝔽 :=
    integrable_globalLineGeometricKernel_diagonal hU hBorel a hs φ _ha _hφ
  have hsharp :
      Tendsto (fun R : ℝ ↦ ∫ x,
        (modulatedAbsoluteCutoff m𝔽 (Icc R⁻¹ R) x : ℂ) * D x ∂μ𝔽)
        atTop (𝓝 (∫ x, D x ∂μ𝔽)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun x ↦ ‖D x‖)
    · exact .of_forall fun R ↦
        ((modulatedAbsoluteCutoff_measurable_bounded m𝔽 (Icc R⁻¹ R)
          measurableSet_Icc).1.complex_ofReal.aestronglyMeasurable).mul
            hD.aestronglyMeasurable
    · refine .of_forall fun R ↦ .of_forall fun x ↦ ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_right
        ((modulatedAbsoluteCutoff_measurable_bounded m𝔽 (Icc R⁻¹ R)
          measurableSet_Icc).2 x) (norm_nonneg _)).trans_eq (one_mul _)
    · exact hD.norm
    · refine .of_forall fun x ↦ ?_
      have hx : 0 < ((m𝔽 x).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
      have hlo : ∀ᶠ R : ℝ in atTop, R⁻¹ ≤ ((m𝔽 x).val : ℝ) :=
        (tendsto_inv_atTop_zero (𝕜 := ℝ)).eventually (eventually_le_nhds hx)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hlo, eventually_ge_atTop ((m𝔽 x).val : ℝ)] with R hl hr
      simp [modulatedAbsoluteCutoff, show ((m𝔽 x).val : ℝ) ∈ Icc R⁻¹ R from ⟨hl, hr⟩]
  have hsmooth := tendsto_integral_cutoff_globalLineGeometricKernel_diagonal
    hU hBorel a hs φ _ha _hφ Λ ε ρ _hΛ _hε
    (_hρ.mono fun _ h ↦ ⟨h.1.1, h.2⟩)
  simpa only [D, Function.comp_def, sub_self] using (hsharp.comp _hΛ).sub hsmooth

local notation "wline" =>
  (fun g : C𝔽 ↦ intervalSobolevDensity (-(0 : ℝ)) 0 s (logNorm g))
local notation "νline" => ((μ𝔽).withDensity (fun g ↦ ENNReal.ofReal (wline g)))

omit hU hBorel in
/-- Paper: Remark 12.1.1.4, p. 503. The spectral kernel divided by its input
weight is square integrable for the positive Sobolev measure in both variables.
Deviation: The remark asserts the opposite; the square integrability is
Theorem 10.4.3.4(2). The kernel of `P^geom_a ∘ A(φ)`, which the remark is
about, is `k^geom`; see `globalLineGeometricKernel_weighted_not_memLp`. -/
theorem globalLineSpectralKernel_weighted_memLp (ha : 0 < a) :
    MemLp (fun p : C𝔽 × C𝔽 ↦ ((wline p.2)⁻¹ : ℝ) • kspec p) 2 ((νline).prod νline) :=
  (spectralLineKernel_hilbertSchmidt (F := F) a hs₁(hs) φ ha).1

omit hU hBorel in
open scoped Pointwise in
private theorem ideleClassTamagawaMeasure_univ_eq_top :
    (μ𝔽) Set.univ = ⊤ := by
  obtain ⟨W, hW_comp, hW_nhds⟩ := exists_compact_mem_nhds (1 : C𝔽)
  have hW_pos : 0 < (μ𝔽) W := by
    obtain ⟨O, hOW, hOopen, h1O⟩ := mem_nhds_iff.mp hW_nhds
    exact (hOopen.measure_pos (μ𝔽) ⟨1, h1O⟩).trans_le (measure_mono hOW)
  have hlog_cont : Continuous (fun g : C𝔽 ↦ logNorm g) := continuous_logNorm_sec1b (F := F)
  obtain ⟨B, hB⟩ := hW_comp.exists_bound_of_continuousOn hlog_cont.continuousOn
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 1 (mem_of_mem_nhds hW_nhds))
  let r : ℝ≥0ˣ := Units.mk0 ⟨Real.exp (2 * B + 1), (Real.exp_pos _).le⟩
    (ne_of_gt (show (0 : ℝ≥0) < ⟨Real.exp (2 * B + 1), (Real.exp_pos _).le⟩ from Real.exp_pos _))
  have hsur : Function.Surjective (ideleClassNorm F) :=
    (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.2.2.2.1
  obtain ⟨g, hg⟩ := hsur r
  have hlog_g : logNorm g = 2 * B + 1 := by
    dsimp only
    rw [hg]
    exact Real.log_exp (2 * B + 1)
  have hlog_mul (x y : C𝔽) : logNorm (x * y) = logNorm x + logNorm y := by
    dsimp only
    rw [map_mul, Units.val_mul, NNReal.coe_mul]
    exact Real.log_mul (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
      (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
  have hlog_pow (n : ℕ) : logNorm (g ^ n) = (n : ℝ) * (2 * B + 1) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, hlog_mul, ih, hlog_g, Nat.cast_succ]
      ring
  let A : ℕ → Set C𝔽 := fun n ↦ (g ^ n) • W
  have hA_meas (n : ℕ) : MeasurableSet (A n) := hW_comp.isClosed.measurableSet.const_smul (g ^ n)
  have hA_disj : Pairwise fun m n ↦ Disjoint (A m) (A n) := by
    intro m n hmn
    rw [Set.disjoint_left]
    rintro x ⟨u, hu, rfl⟩ ⟨v, hv, hEq⟩
    have huB : |logNorm u| ≤ B := by simpa [Real.norm_eq_abs] using hB u hu
    have hvB : |logNorm v| ≤ B := by simpa [Real.norm_eq_abs] using hB v hv
    have hlog_eq : (m : ℝ) * (2 * B + 1) + logNorm u = (n : ℝ) * (2 * B + 1) + logNorm v := by
      have h1 := congrArg (fun z : C𝔽 ↦ logNorm z) hEq
      change logNorm (g ^ n * v) = logNorm (g ^ m * u) at h1
      rw [hlog_mul, hlog_mul, hlog_pow, hlog_pow] at h1
      exact h1.symm
    have hdiff : |(m : ℝ) - (n : ℝ)| * (2 * B + 1) ≤ 2 * B := by
      have hstep : ((m : ℝ) - (n : ℝ)) * (2 * B + 1) = logNorm v - logNorm u := by linarith
      have habs : |((m : ℝ) - (n : ℝ)) * (2 * B + 1)| = |logNorm v - logNorm u| :=
        congrArg abs hstep
      rw [abs_mul, abs_of_pos (by linarith : 0 < 2 * B + 1)] at habs
      have htri : |logNorm v - logNorm u| ≤ |logNorm v| + |logNorm u| := abs_sub _ _
      linarith
    have hge1 : (1 : ℝ) ≤ |(m : ℝ) - (n : ℝ)| := by
      rcases lt_or_gt_of_ne hmn with hlt | hgt
      · have : (m : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hlt
        rw [abs_of_neg (by linarith)]
        linarith
      · have : (n : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hgt
        rw [abs_of_pos (by linarith)]
        linarith
    nlinarith
  have hsum : (∑' n : ℕ, (μ𝔽) (A n)) ≤ (μ𝔽) Set.univ := by
    rw [← measure_iUnion hA_disj hA_meas]
    exact measure_mono (Set.subset_univ _)
  have hconst : (∑' n : ℕ, (μ𝔽) (A n)) = ⊤ := by
    simp only [A, measure_smul]
    exact ENNReal.tsum_const_eq_top_of_ne_zero hW_pos.ne'
  rw [hconst] at hsum
  exact top_unique hsum

omit hU hBorel in
private theorem not_memLp_weighted_convolution_kernel (hs' : 0 ≤ s) (_hne : φ ≠ 0) :
    ¬ MemLp (fun p : C𝔽 × C𝔽 ↦ ((wline p.2)⁻¹ : ℝ) • convKernel(φ) p) 2 ((νline).prod νline) := by
  intro hmem
  have hex : ∃ u₀ : C𝔽, φ.val u₀ ≠ 0 := by
    by_contra hall
    push Not at hall
    apply _hne
    exact Subtype.ext (funext hall)
  obtain ⟨u₀, hu₀⟩ := hex
  have hφc : Continuous φ.val :=
    schwartzBruhat_continuous
      (⟨φ.val, bruhatCompactSupport_mem_schwartz φ.property⟩ : SchwartzBruhat C𝔽)
  have hlog_cont : Continuous (fun g : C𝔽 ↦ logNorm g) := continuous_logNorm_sec1b (F := F)
  have hw_cont : Continuous wline := continuous_wline_sec1b (F := F) s
  have hw_pos : ∀ g : C𝔽, 0 < wline g := pos_wline_sec1b (F := F) s
  let c : ℝ := ‖φ.val u₀‖ / 2
  have hc_pos : 0 < c := half_pos (norm_pos_iff.mpr hu₀)
  let M : ℝ := |logNorm u₀| + 1
  have hM_pos : 0 < M := by positivity
  let V : Set C𝔽 := {u : C𝔽 | c < ‖φ.val u‖ ∧ |logNorm u| < M}
  have hV_open : IsOpen V :=
    (isOpen_lt continuous_const hφc.norm).inter (isOpen_lt hlog_cont.abs continuous_const)
  have hu₀V : u₀ ∈ V := ⟨by simp [c, norm_pos_iff.mpr hu₀], by simp [M]⟩
  have hV_pos : 0 < (μ𝔽) V := hV_open.measure_pos (μ𝔽) ⟨u₀, hu₀V⟩
  have hlog_mul (x y : C𝔽) : logNorm (x * y) = logNorm x + logNorm y := by
    dsimp only
    rw [map_mul, Units.val_mul, NNReal.coe_mul]
    exact Real.log_mul (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
      (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
  have hw_eq (g : C𝔽) : wline g = (1 + (logNorm g) ^ 2) ^ (s / 2) := by
    simp [intervalSobolevDensity]
  let C : ℝ := (2 + 2 * M ^ 2) ^ (s / 2)
  have hC_pos : 0 < C := by positivity
  let δ : ℝ := C⁻¹ * c ^ 2
  have hδ_pos : 0 < δ := by positivity
  have hw_ratio (u y : C𝔽) (hu : u ∈ V) : C⁻¹ * wline y ≤ wline (u * y) := by
    rw [inv_mul_le_iff₀ hC_pos, hw_eq y, hw_eq (u * y), hlog_mul u y]
    have hbase_le : 1 + (logNorm y) ^ 2 ≤ (2 + 2 * M ^ 2) * (1 + (logNorm u + logNorm y) ^ 2) := by
      have ha : |logNorm u| ≤ M := hu.2.le
      have ha2 : (logNorm u) ^ 2 ≤ M ^ 2 := by nlinarith [abs_le.mp ha]
      nlinarith [sq_nonneg (2 * logNorm u + logNorm y), sq_nonneg (logNorm u + logNorm y),
        sq_nonneg M]
    have hs2 : 0 ≤ s / 2 := by linarith
    have hpow := Real.rpow_le_rpow (by positivity) hbase_le hs2
    rwa [Real.mul_rpow (by positivity) (by positivity)] at hpow
  let f : C𝔽 × C𝔽 → ℂ := fun p ↦ ((wline p.2)⁻¹ : ℝ) • convKernel(φ) p
  have hlt : ∫⁻ p, ENNReal.ofReal (‖f p‖ ^ 2) ∂((νline).prod νline) < ⊤ := by
    have hsq : Integrable (fun p : C𝔽 × C𝔽 ↦ ‖f p‖ ^ 2) ((νline).prod νline) :=
      (memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).mp hmem
    have hfin := hsq.hasFiniteIntegral
    have heq : (fun p : C𝔽 × C𝔽 ↦ ‖‖f p‖ ^ 2‖ₑ) = fun p ↦ ENNReal.ofReal (‖f p‖ ^ 2) := by
      funext p
      rw [← ofReal_norm, Real.norm_of_nonneg (sq_nonneg _)]
    rw [HasFiniteIntegral, heq] at hfin
    exact hfin
  have hwm : Measurable (fun g : C𝔽 ↦ ENNReal.ofReal (wline g)) :=
    (ENNReal.continuous_ofReal.comp hw_cont).measurable
  have hwm_prod : Measurable (fun p : C𝔽 × C𝔽 ↦
      ENNReal.ofReal (wline p.1) * ENNReal.ofReal (wline p.2)) :=
    (hwm.comp measurable_fst).mul (hwm.comp measurable_snd)
  have hprod : (νline).prod νline =
      ((μ𝔽).prod μ𝔽).withDensity (fun p ↦ ENNReal.ofReal (wline p.1) * ENNReal.ofReal (wline p.2)) :=
    prod_withDensity hwm hwm
  have hf_meas : Measurable (fun p : C𝔽 × C𝔽 ↦ ENNReal.ofReal (‖f p‖ ^ 2)) := by
    have hfc : Continuous f :=
      (hw_cont.comp continuous_snd).inv₀ (fun p ↦ (hw_pos p.2).ne') |>.smul
        (hφc.comp (continuous_fst.mul continuous_snd.inv))
    exact (ENNReal.continuous_ofReal.comp (hfc.norm.pow 2)).measurable
  have hlower : ∫⁻ p, ENNReal.ofReal (‖f p‖ ^ 2) ∂((νline).prod νline) = ⊤ := by
    rw [hprod, lintegral_withDensity_eq_lintegral_mul ((μ𝔽).prod μ𝔽) hwm_prod hf_meas]
    have hmeas_int : Measurable (fun p : C𝔽 × C𝔽 ↦
        (ENNReal.ofReal (wline p.1) * ENNReal.ofReal (wline p.2)) * ENNReal.ofReal (‖f p‖ ^ 2)) :=
      hwm_prod.mul hf_meas
    change ∫⁻ p, (ENNReal.ofReal (wline p.1) * ENNReal.ofReal (wline p.2)) *
        ENNReal.ofReal (‖f p‖ ^ 2) ∂((μ𝔽).prod μ𝔽) = ⊤
    rw [lintegral_prod_symm _ hmeas_int.aemeasurable]
    have hrow (y : C𝔽) :
        ENNReal.ofReal δ * (μ𝔽) V ≤
          ∫⁻ x, (ENNReal.ofReal (wline x) * ENNReal.ofReal (wline y)) *
            ENNReal.ofReal (‖f (x, y)‖ ^ 2) ∂μ𝔽 := by
      have hshift := lintegral_mul_right_eq_self (μ := μ𝔽)
        (fun x ↦ (ENNReal.ofReal (wline x) * ENNReal.ofReal (wline y)) *
          ENNReal.ofReal (‖f (x, y)‖ ^ 2)) y
      rw [← hshift]
      calc
        ENNReal.ofReal δ * (μ𝔽) V = ∫⁻ _ in V, ENNReal.ofReal δ ∂μ𝔽 := by
          rw [setLIntegral_const]
        _ ≤ ∫⁻ u in V, (ENNReal.ofReal (wline (u * y)) * ENNReal.ofReal (wline y)) *
            ENNReal.ofReal (‖f (u * y, y)‖ ^ 2) ∂μ𝔽 := by
          refine setLIntegral_mono' hV_open.measurableSet fun u hu ↦ ?_
          have hnorm_f : ‖f (u * y, y)‖ = (wline y)⁻¹ * ‖φ.val u‖ := by
            simp only [f, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (hw_pos y),
              mul_inv_cancel_right]
          rw [hnorm_f, ← ENNReal.ofReal_mul (hw_pos _).le,
            ← ENNReal.ofReal_mul (mul_nonneg (hw_pos _).le (hw_pos _).le)]
          refine ENNReal.ofReal_le_ofReal ?_
          have hwy : wline y ≠ 0 := (hw_pos y).ne'
          have hrhs : wline (u * y) * wline y * ((wline y)⁻¹ * ‖φ.val u‖) ^ 2 =
              (wline (u * y) / wline y) * ‖φ.val u‖ ^ 2 := by
            field_simp
          rw [hrhs]
          have h1 : C⁻¹ ≤ wline (u * y) / wline y :=
            (le_div_iff₀ (hw_pos y)).mpr (hw_ratio u y hu)
          have h2 : c ^ 2 ≤ ‖φ.val u‖ ^ 2 :=
            pow_le_pow_left₀ hc_pos.le hu.1.le 2
          exact mul_le_mul h1 h2 (sq_nonneg c) (div_nonneg (hw_pos _).le (hw_pos _).le)
        _ ≤ ∫⁻ u, (ENNReal.ofReal (wline (u * y)) * ENNReal.ofReal (wline y)) *
            ENNReal.ofReal (‖f (u * y, y)‖ ^ 2) ∂μ𝔽 := setLIntegral_le_lintegral V _
    have htot : (ENNReal.ofReal δ * (μ𝔽) V) * (μ𝔽) Set.univ ≤
        ∫⁻ y, ∫⁻ x, (ENNReal.ofReal (wline x) * ENNReal.ofReal (wline y)) *
          ENNReal.ofReal (‖f (x, y)‖ ^ 2) ∂μ𝔽 ∂μ𝔽 := by
      calc
        (ENNReal.ofReal δ * (μ𝔽) V) * (μ𝔽) Set.univ =
            ∫⁻ _ : C𝔽, ENNReal.ofReal δ * (μ𝔽) V ∂μ𝔽 := (lintegral_const _).symm
        _ ≤ _ := lintegral_mono hrow
    have hinf : (ENNReal.ofReal δ * (μ𝔽) V) * (μ𝔽) Set.univ = ⊤ := by
      rw [ideleClassTamagawaMeasure_univ_eq_top (F := F)]
      exact ENNReal.mul_top (mul_ne_zero (ENNReal.ofReal_pos.mpr hδ_pos).ne' hV_pos.ne')
    rw [hinf] at htot
    exact top_unique htot
  rw [hlower] at hlt
  exact lt_irrefl ⊤ hlt

omit hU hBorel in
/-- Paper: Remark 12.1.1.4, p. 503. For a nonzero test vanishing at the identity,
the geometric kernel divided by its input weight is not square integrable for
the positive Sobolev measure in both variables.
Deviation: The print writes `k^spec` here, for which the claim is false
(`Sec1b_Printed.lean`); the kernel of `P^geom_a ∘ A(φ)` is `k^geom`. The zero
test must be excluded. -/
theorem globalLineGeometricKernel_weighted_not_memLp
    (_ha : 0 < a) (_hφ : φ.val 1 = 0) (_hne : φ ≠ 0) :
    ¬ MemLp (fun p : C𝔽 × C𝔽 ↦ ((wline p.2)⁻¹ : ℝ) • kgeom p) 2 ((νline).prod νline) := by
  intro hgeom
  have hspec := globalLineSpectralKernel_weighted_memLp a hs φ _ha
  have hconv : MemLp (fun p : C𝔽 × C𝔽 ↦ ((wline p.2)⁻¹ : ℝ) • convKernel(φ) p) 2
      ((νline).prod νline) := by
    refine (hgeom.add hspec).ae_eq (Eventually.of_forall fun p ↦ ?_)
    simp only [Pi.add_apply, globalLineGeometricKernel, smul_sub, sub_add_cancel]
  exact not_memLp_weighted_convolution_kernel (φ := φ) hs₀(hs) _hne hconv

omit hU hBorel in
open scoped ComplexConjugate InnerProductSpace in
/-- Paper: Remark 12.1.1.4, p. 503. Convolution by a nonzero test is not
Hilbert–Schmidt on the weighted Sobolev space, hence not nuclear.
Deviation: The zero test must be excluded. -/
theorem hardySobolevTestAction_not_hilbertSchmidt (_hne : φ ≠ 0) :
    hardySobolevTestAction μ𝔽 m𝔽 _ _ _ hbase hs₀(hs) φ ∉
      hilbertSchmidtOperators (W(s)) (W(s)) := by
  intro hHS
  have hw_cont : Continuous wline := continuous_wline_sec1b (F := F) s
  have hw_pos : ∀ g : C𝔽, 0 < wline g := pos_wline_sec1b (F := F) s
  let fNN : C𝔽 → ℝ≥0 := fun g ↦ ⟨wline g, (hw_pos g).le⟩
  have hf_cont : Continuous fNN := hw_cont.subtype_mk _
  have hν : νline = (μ𝔽).withDensity (fun g ↦ (fNN g : ENNReal)) :=
    congrArg (μ𝔽).withDensity (funext fun g ↦ ENNReal.ofReal_eq_coe_nnreal (hw_pos g).le)
  let : IsLocallyFiniteMeasure νline := sobolevKernelWeight_locallyFinite (F := F) 0 s
  obtain ⟨K, hK_eq⟩ := integralKernelOperator_surjective_sec1b νline
    ⟨hardySobolevTestAction μ𝔽 m𝔽 _ _ _ hbase hs₀(hs) φ, hHS⟩
  have hK_op : (integralKernelOperator νline K).val =
      hardySobolevTestAction μ𝔽 m𝔽 _ _ _ hbase hs₀(hs) φ := congrArg Subtype.val hK_eq
  let f : C𝔽 × C𝔽 → ℂ := fun p ↦ ((wline p.2)⁻¹ : ℝ) • convKernel(φ) p
  have hφc : Continuous φ.val :=
    schwartzBruhat_continuous
      (⟨φ.val, bruhatCompactSupport_mem_schwartz φ.property⟩ : SchwartzBruhat C𝔽)
  have hfc : Continuous f :=
    (hw_cont.comp continuous_snd).inv₀ (fun p ↦ (hw_pos p.2).ne') |>.smul
      (hφc.comp (continuous_fst.mul continuous_snd.inv))
  have hν_ac : νline ≪ μ𝔽 := withDensity_absolutelyContinuous _ _
  have hrow_eq (u : Lp ℂ 2 νline) :
      ∀ᵐ x ∂νline, ∫ y, K (x, y) * u y ∂νline = ∫ y, f (x, y) * u y ∂νline := by
    filter_upwards [integralKernelOperator_apply νline K u,
      hν_ac.ae_le (hardySobolevTestAction_apply μ𝔽 m𝔽 _ _ _ hbase hs₀(hs) φ u)] with x hx hact
    have h1 : (integralKernelOperator νline K).val u x =
        (hardySobolevTestAction μ𝔽 m𝔽 _ _ _ hbase hs₀(hs) φ u) x :=
      congrArg (fun A : W(s) →L[ℂ] W(s) ↦ (A u : C𝔽 → ℂ) x) hK_op
    rw [← hx.2, h1, hact]
    unfold lcaConvolution
    have hwd : ∫ y, f (x, y) * (u : C𝔽 → ℂ) y ∂νline =
        ∫ y, fNN y • (f (x, y) * (u : C𝔽 → ℂ) y) ∂μ𝔽 :=
      (congrArg (fun σ ↦ ∫ y, f (x, y) * (u : C𝔽 → ℂ) y ∂σ) hν).trans
        (integral_withDensity_eq_integral_smul hf_cont.measurable
          (fun y ↦ f (x, y) * (u : C𝔽 → ℂ) y))
    rw [hwd]
    have hsimp : (fun y : C𝔽 ↦ fNN y • (f (x, y) * u y)) = fun y ↦ φ.val (x * y⁻¹) * u y := by
      funext y
      change (wline y : ℝ) • ((((wline y)⁻¹ : ℝ) • φ.val (x * y⁻¹)) * u y) = φ.val (x * y⁻¹) * u y
      rw [smul_mul_assoc, smul_smul, mul_inv_cancel₀ (hw_pos y).ne', one_smul]
    rw [hsimp, ← integral_inv_eq_self (fun t ↦ φ.val t * u (t⁻¹ * x)) (μ𝔽)]
    have hinv_simp : (fun t : C𝔽 ↦ φ.val t⁻¹ * u (t⁻¹⁻¹ * x)) =
        fun t ↦ φ.val (x * (t * x)⁻¹) * u (t * x) := by
      funext t
      rw [inv_inv, mul_inv, mul_comm t⁻¹ x⁻¹, ← mul_assoc, mul_inv_cancel, one_mul]
    rw [hinv_simp]
    exact integral_mul_right_eq_self (fun y ↦ φ.val (x * y⁻¹) * u y) x
  let : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
  have : SecondCountableTopology (Lp ℂ 2 νline) := Lp.SecondCountableTopology
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq (Lp ℂ 2 νline)
  have hKrow : ∀ᵐ x ∂νline, MemLp (fun y ↦ K (x, y)) 2 νline := by
    have hKsq := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable K)).mp (Lp.memLp K)
    filter_upwards [hKsq.prod_right_ae] with x hx
    exact (memLp_two_iff_integrable_sq_norm
      ((Lp.stronglyMeasurable K).comp_measurable measurable_prodMk_left).aestronglyMeasurable).mpr hx
  have hfrow (x : C𝔽) : MemLp (fun y ↦ f (x, y)) 2 νline := by
    have hcont : Continuous (fun y ↦ f (x, y)) := hfc.comp (continuous_const.prodMk continuous_id)
    have hsupp : HasCompactSupport (fun y ↦ f (x, y)) := by
      have hK_comp : IsCompact ((fun t : C𝔽 ↦ x * t⁻¹) '' tsupport φ.val) :=
        φ.property.2.image (continuous_const.mul continuous_inv)
      refine HasCompactSupport.of_support_subset_isCompact hK_comp fun y hy ↦ ?_
      refine ⟨x * y⁻¹, ?_, ?_⟩
      · apply subset_tsupport φ.val
        intro h0
        apply hy
        simp [f, h0]
      · dsimp only
        rw [mul_inv, inv_inv, ← mul_assoc, mul_inv_cancel, one_mul]
    have hsq_cont : Continuous (fun y ↦ ‖f (x, y)‖ ^ 2) := hcont.norm.pow 2
    have hsq_supp : HasCompactSupport (fun y ↦ ‖f (x, y)‖ ^ 2) :=
      hsupp.comp_left (g := fun z : ℂ ↦ ‖z‖ ^ 2) (by simp)
    exact (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).mpr
      (hsq_cont.integrable_of_hasCompactSupport hsq_supp)
  have hae_ae : ∀ᵐ x ∂νline, (fun y ↦ K (x, y)) =ᵐ[νline] fun y ↦ f (x, y) := by
    filter_upwards [hKrow, ae_all_iff.2 fun n ↦ hrow_eq (u n)] with x hKx hux
    have hdiff : MemLp (fun y ↦ conj (K (x, y) - f (x, y))) 2 νline := by
      have hsub := hKx.sub (hfrow x)
      exact hsub.congr_norm
        (Complex.continuous_conj.comp_aestronglyMeasurable hsub.aestronglyMeasurable)
        (Eventually.of_forall fun y ↦ (Complex.norm_conj _).symm)
    let v : Lp ℂ 2 νline := hdiff.toLp (fun y ↦ conj (K (x, y) - f (x, y)))
    have hinner_u (n : ℕ) : ⟪v, u n⟫_ℂ = 0 := by
      rw [L2.inner_def]
      have h1 : (fun y ↦ ⟪v y, u n y⟫_ℂ) =ᵐ[νline] fun y ↦ K (x, y) * u n y - f (x, y) * u n y := by
        filter_upwards [hdiff.coeFn_toLp] with y hy
        rw [hy, RCLike.inner_apply, Complex.conj_conj]
        ring
      have hi1 : Integrable (fun y ↦ K (x, y) * u n y) νline :=
        hKx.integrable_mul (Lp.memLp (u n))
      have hi2 : Integrable (fun y ↦ f (x, y) * u n y) νline :=
        (hfrow x).integrable_mul (Lp.memLp (u n))
      rw [integral_congr_ae h1, integral_sub hi1 hi2, hux n, sub_self]
    have hinner_all (w : Lp ℂ 2 νline) : ⟪v, w⟫_ℂ = 0 := by
      have hfun : (fun z : Lp ℂ 2 νline ↦ ⟪v, z⟫_ℂ) = fun _ ↦ 0 :=
        hu.equalizer (continuous_const.inner continuous_id) continuous_const (funext hinner_u)
      exact congrFun hfun w
    have hv0 : v = 0 := inner_self_eq_zero.mp (hinner_all v)
    have hv_zero : (v : C𝔽 → ℂ) =ᵐ[νline] 0 := by
      rw [hv0]
      exact Lp.coeFn_zero ℂ 2 νline
    filter_upwards [hdiff.coeFn_toLp, hv_zero] with y h1 h2
    have h0 : conj (K (x, y) - f (x, y)) = 0 := h1.symm.trans h2
    have h0' : K (x, y) - f (x, y) = 0 := by
      simpa only [Complex.conj_conj, map_zero] using congrArg conj h0
    exact sub_eq_zero.mp h0'
  have hKf : (K : C𝔽 × C𝔽 → ℂ) =ᵐ[(νline).prod νline] f := by
    have hmeas : MeasurableSet {p : C𝔽 × C𝔽 | K p = f p} :=
      measurableSet_eq_fun (Lp.stronglyMeasurable K).measurable hfc.measurable
    exact (Measure.ae_prod_iff_ae_ae hmeas).mpr hae_ae
  exact not_memLp_weighted_convolution_kernel (φ := φ) hs₀(hs) _hne ((Lp.memLp K).ae_eq hKf)

omit hU hBorel in
/-- Paper: Remark 12.1.1.4, pp. 503–504. For a nonzero test vanishing at the
identity, untruncated geometric convolution fails to be Hilbert–Schmidt.
Deviation: The obstruction comes from the full convolution kernel, and the
zero test must be excluded. -/
theorem geometricProjection_convolution_not_hilbertSchmidt
    (_ha : 0 < a) (_hφ : φ.val 1 = 0) (_hne : φ ≠ 0) :
    (geometricProjection (F := F) a hline hs₀(hs)).comp
      (hardySobolevTestAction μ𝔽 m𝔽 _ _ _ hbase hs₀(hs) φ) ∉
        hilbertSchmidtOperators (W(s)) (W(s)) := by
  let A : W(s) →L[ℂ] W(s) := hardySobolevTestAction μ𝔽 m𝔽 (-(0 : ℝ)) 0 s hbase hs₀(hs) φ
  let M := globalThetaSobolev F a (α := -(0 : ℝ)) (β := 0) hbase hs₀(hs)
  have hspec : Tspec ∈ hilbertSchmidtOperators (W(s)) (W(s)) := by
    let : IsLocallyFiniteMeasure νline := sobolevKernelWeight_locallyFinite (F := F) 0 s
    let K : C𝔽 × C𝔽 → ℂ := fun p ↦ (wline p.2)⁻¹ • kspec p
    have hK := spectralLineKernel_hilbertSchmidt (F := F) a hs₁(hs) φ _ha
    let T := integralKernelOperator νline (hK.choose.toLp K)
    have he : T.val = Tspec := hK.choose_spec
    have hmem : T.val ∈ hilbertSchmidtOperators (W(s)) (W(s)) := T.property
    exact (congrArg (fun L : W(s) →L[ℂ] W(s) ↦ L ∈ hilbertSchmidtOperators (W(s)) (W(s))) he).mp hmem
  intro hgeom
  have hsum : M.starProjection.comp A + M.orthogonal.starProjection.comp A = A := by
    ext1 u
    exact M.starProjection_add_starProjection_orthogonal (A u)
  refine (hardySobolevTestAction_not_hilbertSchmidt (F := F) (hs := hs) (φ := φ) _hne :
    A ∉ hilbertSchmidtOperators (W(s)) (W(s))) ?_
  exact Eq.subst (motive := fun B ↦ B ∈ hilbertSchmidtOperators (W(s)) (W(s))) hsum
    ((hilbertSchmidtOperators (W(s)) (W(s))).add_mem hgeom hspec)

-- TODO(later): needs §12.5. The proof of Theorem 12.5.1.1, p. 520, integrates the
-- smoothened strip kernel of Definition 10.4.3.7 along the diagonal. The paper
-- states (12.1.1.21)–(12.1.1.23) for the line kernels only.

end GlobalKernels

end RiemannMasullo
