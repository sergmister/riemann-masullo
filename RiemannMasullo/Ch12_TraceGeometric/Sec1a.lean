module

public import RiemannMasullo.AppA_AlgebraicNT.Sec5b
public import RiemannMasullo.AppC_LCTVS.Sec3b
public import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec1
public import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import RiemannMasullo.ForMathlib.MeasureTheory.Function.L2Space

/-!
# Smoothenings along the diagonal

Masullo, §12.1.1, pp. 498–501, through Theorem 12.1.1.2.
Regular points are those of `dSequenceRegularSet` from Appendix A.5.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set Topology
open scoped ComplexConjugate ENNReal NNReal

namespace RiemannMasullo

section Smoothening

variable {G : Type*} [CommGroup G] [MeasurableSpace G]

/-- Paper: Definition 12.1.1.1, p. 498. The smoothening is the limit of the
translated Haar averages at every regular point and zero elsewhere. The paper
applies this formula to locally Haar-integrable functions and Borel D′-sequences. -/
def dSequenceSmootheningOrZero (μ : Measure G) (U : ℕ → Set G) (φ : G → ℂ) (x : G) : ℂ :=
  open Classical in
  if hx : x ∈ dSequenceRegularSet μ U φ then dSequenceSmoothening μ U φ ⟨x, hx⟩ else 0

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- Paper: Definition 12.1.1.1, p. 498. A constant function smoothens to the same
constant at every point. -/
theorem dSequenceSmootheningOrZero_const [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    {U : ℕ → Set G} (hU : IsDPrimeSequence μ U) (c : ℂ) :
    dSequenceSmootheningOrZero μ U (fun _ ↦ c) = fun _ ↦ c := by
  funext x
  have havg (n : ℕ) : dSequenceAverage μ (U n) (fun _ ↦ c) x = c := by
    obtain ⟨_, _, hpos, hfin⟩ := hU.1.1 n
    unfold dSequenceAverage
    apply setAverage_const <;> rw [measure_smul]
    · exact hpos.ne'
    · exact hfin.ne
  have hlim : Tendsto (fun n ↦ dSequenceAverage μ (U n) (fun _ ↦ c) x) atTop (𝓝 c) := by
    simpa only [havg] using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ c) atTop (𝓝 c))
  have hx : x ∈ dSequenceRegularSet μ U (fun _ ↦ c) := ⟨c, hlim⟩
  simpa only [dSequenceSmootheningOrZero, dite_eq_left hx, dSequenceSmoothening] using hlim.limUnder_eq

-- TODO(paper-gap): The Euclidean example on p. 498 needs positive radii tending to zero.

/-- Paper: §12.1.1, p. 499. Smoothen a kernel using the sequence of product
sets and product Haar measure. -/
def dSequenceKernelSmoothening (μ : Measure G) (U : ℕ → Set G) (k : G × G → ℂ) :
    G × G → ℂ :=
  dSequenceSmootheningOrZero (μ.prod μ) (fun n ↦ U n ×ˢ U n) k

/-- Paper: §12.1.1, p. 499. A constant kernel is unchanged by product smoothening. -/
theorem dSequenceKernelSmoothening_const [T2Space G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] {U : ℕ → Set G} (hU : IsDPrimeSequence μ U) (c : ℂ) :
    dSequenceKernelSmoothening μ U (fun _ ↦ c) = fun _ ↦ c := by
  funext p
  have havg (n : ℕ) :
      dSequenceAverage (μ.prod μ) (U n ×ˢ U n) (fun _ ↦ c) p = c := by
    obtain ⟨_, _, hpos, hfin⟩ := hU.1.1 n
    unfold dSequenceAverage
    apply setAverage_const <;> rw [measure_smul, Measure.prod_prod]
    · exact mul_ne_zero hpos.ne' hpos.ne'
    · exact ENNReal.mul_ne_top hfin.ne hfin.ne
  have hlim : Tendsto
      (fun n ↦ dSequenceAverage (μ.prod μ) (U n ×ˢ U n) (fun _ ↦ c) p) atTop (𝓝 c) := by
    simpa only [havg] using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ c) atTop (𝓝 c))
  have hp : p ∈ dSequenceRegularSet (μ.prod μ) (fun n ↦ U n ×ˢ U n) (fun _ ↦ c) := ⟨c, hlim⟩
  simpa only [dSequenceKernelSmoothening, dSequenceSmootheningOrZero, dite_eq_left hp,
    dSequenceSmoothening] using hlim.limUnder_eq

end Smoothening

private theorem isDPrimeSequence_prod_self {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]
    {U : ℕ → Set G} (hU : IsDPrimeSequence μ U) :
    IsDPrimeSequence (μ.prod μ) (fun n ↦ U n ×ˢ U n) := by
  have rectSeq [m : MeasurableSpace (G × G)] (hm : m = borel _)
      (η : Measure (G × G)) [η.IsHaarMeasure]
      (hrect : ∀ s t : Set G, MeasurableSet s → MeasurableSet t → η (s ×ˢ t) = μ s * μ t) :
      IsDPrimeSequence η (fun n ↦ U n ×ˢ U n) := by
    subst m
    exact IsDPrimeSequence.prod hrect hU hU
  exact rectSeq BorelSpace.measurable_eq _ (fun s t _ _ ↦ Measure.prod_prod s t)

private theorem locallyIntegrable_of_weighted_memLp_prod {G : Type*} [CommGroup G]
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
  have hprod : ν.prod ν = (μ.prod μ).withDensity (fun p ↦ (w p : ℝ≥0∞)) := by
    rw [hν]
    have hm : Measurable (fun x ↦ (f x : ℝ≥0∞)) := (ENNReal.continuous_coe.comp hf).measurable
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

private theorem dSequenceKernelSmoothening_ae_eq_haar {G : Type*} [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    {μ : Measure G} [μ.IsHaarMeasure] {U : ℕ → Set G} (hU : IsDPrimeSequence μ U)
    {κ : G × G → ℂ} (hhaar : LocallyIntegrable κ (μ.prod μ)) :
    dSequenceKernelSmoothening μ U κ =ᵐ[μ.prod μ] κ := by
  filter_upwards [ae_tendsto_dSequenceAverage (isDPrimeSequence_prod_self hU) hhaar] with p hp
  have hreg : p ∈ dSequenceRegularSet (μ.prod μ) (fun n ↦ U n ×ˢ U n) κ := ⟨κ p, hp⟩
  simpa only [dSequenceKernelSmoothening, dSequenceSmootheningOrZero, dite_eq_left hreg,
    dSequenceSmoothening] using hp.limUnder_eq

open scoped Pointwise in
private theorem ae_tendsto_setAverage_hilbert {G H : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]
    {U : ℕ → Set G} (hU : IsDPrimeSequence μ U)
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    {Φ : G → H} (hΦm : AEStronglyMeasurable Φ μ)
    (hΦ2 : LocallyIntegrable (fun x ↦ ‖Φ x‖ ^ 2) μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n ↦ ⨍ y in x • U n, Φ y ∂μ) atTop (𝓝 (Φ x)) := by
  obtain ⟨v, hv⟩ := TopologicalSpace.exists_dense_seq H
  have hΦ_loc : LocallyIntegrable Φ μ := by
    rw [locallyIntegrable_iff]
    intro K hK
    refine ((hΦ2.integrableOn_isCompact hK).add
      (integrableOn_const (C := (1 : ℝ)) hK.measure_lt_top.ne)).mono'
      hΦm.restrict (Eventually.of_forall fun y ↦ ?_)
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (‖Φ y‖ - 1), norm_nonneg (Φ y)]
  have hloc_sub (w : H) : LocallyIntegrable (fun y ↦ ‖Φ y - w‖ ^ 2) μ := by
    rw [locallyIntegrable_iff]
    intro K hK
    refine (((hΦ2.integrableOn_isCompact hK).const_mul 2).add
      (integrableOn_const (C := 2 * ‖w‖ ^ 2) hK.measure_lt_top.ne)).mono'
      ((hΦm.sub aestronglyMeasurable_const).norm.pow 2).restrict
      (Eventually.of_forall fun y ↦ ?_)
    simp only [Pi.add_apply]
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have htri : ‖Φ y - w‖ ≤ ‖Φ y‖ + ‖w‖ := norm_sub_le (Φ y) w
    nlinarith [sq_nonneg (‖Φ y‖ - ‖w‖), norm_nonneg (Φ y - w), norm_nonneg (Φ y), norm_nonneg w]
  have hloc_subC (m : ℕ) : LocallyIntegrable (fun y ↦ ((‖Φ y - v m‖ ^ 2 : ℝ) : ℂ)) μ := by
    rw [locallyIntegrable_iff]
    intro K hK
    exact Complex.ofRealCLM.integrable_comp ((hloc_sub (v m)).integrableOn_isCompact hK)
  have havgC (m : ℕ) (x : G) (n : ℕ) :
      dSequenceAverage μ (U n) (fun y ↦ ((‖Φ y - v m‖ ^ 2 : ℝ) : ℂ)) x =
        ((⨍ y in x • U n, ‖Φ y - v m‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    have hint : ∫ y in x • U n, ((‖Φ y - v m‖ ^ 2 : ℝ) : ℂ) ∂μ =
        ↑(∫ y in x • U n, ‖Φ y - v m‖ ^ 2 ∂μ) := integral_ofReal
    rw [dSequenceAverage, setAverage_eq, setAverage_eq, hint, Complex.real_smul, smul_eq_mul,
      Complex.ofReal_mul]
  have hae : ∀ᵐ x ∂μ, ∀ m : ℕ,
      Tendsto (fun n ↦ ⨍ y in x • U n, ‖Φ y - v m‖ ^ 2 ∂μ) atTop (𝓝 (‖Φ x - v m‖ ^ 2)) := by
    refine ae_all_iff.2 fun m ↦ ?_
    filter_upwards [ae_tendsto_dSequenceAverage hU (hloc_subC m)] with x hx
    have hre := (Complex.reCLM.continuous.tendsto _).comp hx
    simpa only [Function.comp_def, havgC, Complex.reCLM_apply, Complex.ofReal_re] using hre
  filter_upwards [hae] with x hx
  obtain ⟨K, hK, hKnhds⟩ := exists_compact_mem_nhds x
  have hpre : (fun y : G ↦ x * y) ⁻¹' K ∈ 𝓝 (1 : G) :=
    (continuous_const_mul x).continuousAt.preimage_mem_nhds (by simpa only [mul_one] using hKnhds)
  obtain ⟨N₀, hN₀⟩ := hU.2 _ hpre
  have hsub (n : ℕ) (hn : N₀ ≤ n) : x • U n ⊆ K := by
    rintro _ ⟨y, hy, rfl⟩
    exact hN₀ (hU.1.2.1 hn hy)
  have hμne0 (n : ℕ) : μ (x • U n) ≠ 0 := by
    rw [measure_smul]
    exact (hU.1.1 n).2.2.1.ne'
  have hμne_top (n : ℕ) : μ (x • U n) ≠ ∞ := by
    rw [measure_smul]
    exact (hU.1.1 n).2.2.2.ne
  have hμpos (n : ℕ) : 0 < μ.real (x • U n) := ENNReal.toReal_pos (hμne0 n) (hμne_top n)
  have hsq : Tendsto (fun n ↦ ⨍ y in x • U n, ‖Φ y - Φ x‖ ^ 2 ∂μ) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨m, hm⟩ := hv.exists_dist_lt (Φ x) (Real.sqrt_pos.mpr (by positivity : 0 < ε / 5))
    rw [dist_eq_norm] at hm
    have hm2 : ‖Φ x - v m‖ ^ 2 < ε / 5 := by
      have hsq_lt := pow_lt_pow_left₀ hm (norm_nonneg _) (by decide : 2 ≠ 0)
      rwa [Real.sq_sqrt (by positivity)] at hsq_lt
    have hrhs : Tendsto (fun n ↦ 2 * (⨍ y in x • U n, ‖Φ y - v m‖ ^ 2 ∂μ) + 2 * ‖Φ x - v m‖ ^ 2)
        atTop (𝓝 (2 * ‖Φ x - v m‖ ^ 2 + 2 * ‖Φ x - v m‖ ^ 2)) :=
      ((hx m).const_mul 2).add tendsto_const_nhds
    have hev : ∀ᶠ n in atTop,
        2 * (⨍ y in x • U n, ‖Φ y - v m‖ ^ 2 ∂μ) + 2 * ‖Φ x - v m‖ ^ 2 < ε :=
      hrhs.eventually (Iio_mem_nhds (by linarith))
    filter_upwards [hev, eventually_ge_atTop N₀] with n hn hn₀
    have hle : ⨍ y in x • U n, ‖Φ y - Φ x‖ ^ 2 ∂μ ≤
        2 * (⨍ y in x • U n, ‖Φ y - v m‖ ^ 2 ∂μ) + 2 * ‖Φ x - v m‖ ^ 2 := by
      have hi1 := ((hloc_sub (Φ x)).integrableOn_isCompact hK).mono_set (hsub n hn₀)
      have hi2 := ((hloc_sub (v m)).integrableOn_isCompact hK).mono_set (hsub n hn₀)
      have hic := integrableOn_const (μ := μ) (s := x • U n) (C := 2 * ‖Φ x - v m‖ ^ 2) (hμne_top n)
      have hpt : ∀ y, ‖Φ y - Φ x‖ ^ 2 ≤ 2 * ‖Φ y - v m‖ ^ 2 + 2 * ‖Φ x - v m‖ ^ 2 := by
        intro y
        have htri : ‖Φ y - Φ x‖ ≤ ‖Φ y - v m‖ + ‖Φ x - v m‖ := by
          have hd := dist_triangle (Φ y) (v m) (Φ x)
          rw [dist_eq_norm, dist_eq_norm, dist_eq_norm, norm_sub_rev (v m) (Φ x)] at hd
          exact hd
        nlinarith [sq_nonneg (‖Φ y - v m‖ - ‖Φ x - v m‖), norm_nonneg (Φ y - Φ x),
          norm_nonneg (Φ y - v m), norm_nonneg (Φ x - v m)]
      have hint : ∫ y in x • U n, ‖Φ y - Φ x‖ ^ 2 ∂μ ≤
          ∫ y in x • U n, (2 * ‖Φ y - v m‖ ^ 2 + 2 * ‖Φ x - v m‖ ^ 2) ∂μ :=
        integral_mono hi1 ((hi2.const_mul 2).add hic) hpt
      rw [integral_add (hi2.const_mul 2) hic, integral_const_mul, integral_const,
        measureReal_restrict_apply_univ, smul_eq_mul] at hint
      simp only [setAverage_eq, smul_eq_mul]
      have hpos := hμpos n
      have hinv_pos : 0 < (μ.real (x • U n))⁻¹ := inv_pos.mpr hpos
      have hmul := mul_le_mul_of_nonneg_left hint hinv_pos.le
      rw [mul_add, ← mul_assoc, mul_comm (μ.real (x • U n))⁻¹ 2, mul_assoc 2,
        ← mul_assoc (μ.real (x • U n))⁻¹, inv_mul_cancel₀ hpos.ne', one_mul] at hmul
      exact hmul
    have hnn : 0 ≤ ⨍ y in x • U n, ‖Φ y - Φ x‖ ^ 2 ∂μ :=
      average_nonneg fun _ ↦ sq_nonneg _
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
    exact hle.trans_lt hn
  rw [Metric.tendsto_nhds]
  intro ε hε
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := half_pos hε
  have hsq_small : ∀ᶠ n in atTop, (⨍ y in x • U n, ‖Φ y - Φ x‖ ^ 2 ∂μ) / (4 * δ) < δ :=
    (hsq.div_const (4 * δ)).eventually (Iio_mem_nhds (by simpa [zero_div] using hδ))
  filter_upwards [hsq_small, eventually_ge_atTop N₀] with n hn hn₀
  have hΦn : IntegrableOn Φ (x • U n) μ := (hΦ_loc.integrableOn_isCompact hK).mono_set (hsub n hn₀)
  have hΦ2n : IntegrableOn (fun y ↦ ‖Φ y - Φ x‖ ^ 2) (x • U n) μ :=
    ((hloc_sub (Φ x)).integrableOn_isCompact hK).mono_set (hsub n hn₀)
  have hcn : IntegrableOn (fun _ : G ↦ Φ x) (x • U n) μ := integrableOn_const (hμne_top n)
  have hdiff : (⨍ y in x • U n, Φ y ∂μ) - Φ x = ⨍ y in x • U n, (Φ y - Φ x) ∂μ := by
    have hpos := hμpos n
    simp only [setAverage_eq]
    rw [integral_sub hΦn hcn, integral_const, measureReal_restrict_apply_univ, smul_sub, smul_smul,
      inv_mul_cancel₀ hpos.ne', one_smul]
  have hnorm_le : ‖(⨍ y in x • U n, Φ y ∂μ) - Φ x‖ ≤
      δ + (⨍ y in x • U n, ‖Φ y - Φ x‖ ^ 2 ∂μ) / (4 * δ) := by
    have hpos := hμpos n
    have hinv_nn : 0 ≤ (μ.real (x • U n))⁻¹ := inv_nonneg.mpr hpos.le
    rw [hdiff, setAverage_eq, norm_smul, Real.norm_of_nonneg hinv_nn]
    have hpt : ∀ y, ‖Φ y - Φ x‖ ≤ δ + ‖Φ y - Φ x‖ ^ 2 / (4 * δ) := by
      intro y
      have h4δ : 0 < 4 * δ := by positivity
      rw [← sub_nonneg]
      have hcalc : δ + ‖Φ y - Φ x‖ ^ 2 / (4 * δ) - ‖Φ y - Φ x‖ =
          (‖Φ y - Φ x‖ - 2 * δ) ^ 2 / (4 * δ) := by
        field_simp [h4δ.ne']
        ring
      rw [hcalc]
      positivity
    have hint : ∫ y in x • U n, ‖Φ y - Φ x‖ ∂μ ≤
        ∫ y in x • U n, (δ + ‖Φ y - Φ x‖ ^ 2 / (4 * δ)) ∂μ :=
      integral_mono (hΦn.sub hcn).norm
        ((integrableOn_const (hμne_top n)).add (hΦ2n.div_const (4 * δ))) hpt
    rw [integral_add (integrableOn_const (hμne_top n)) (hΦ2n.div_const (4 * δ)),
      integral_const, measureReal_restrict_apply_univ, integral_div, smul_eq_mul] at hint
    calc
      (μ.real (x • U n))⁻¹ * ‖∫ y in x • U n, (Φ y - Φ x) ∂μ‖
        ≤ (μ.real (x • U n))⁻¹ * ∫ y in x • U n, ‖Φ y - Φ x‖ ∂μ :=
          mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) hinv_nn
      _ ≤ (μ.real (x • U n))⁻¹ *
            (μ.real (x • U n) * δ + (∫ y in x • U n, ‖Φ y - Φ x‖ ^ 2 ∂μ) / (4 * δ)) :=
          mul_le_mul_of_nonneg_left hint hinv_nn
      _ = δ + (⨍ y in x • U n, ‖Φ y - Φ x‖ ^ 2 ∂μ) / (4 * δ) := by
          simp only [setAverage_eq, smul_eq_mul]
          rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul, mul_div_assoc]
  rw [dist_eq_norm]
  have hlt : δ + (⨍ y in x • U n, ‖Φ y - Φ x‖ ^ 2 ∂μ) / (4 * δ) < ε := by
    dsimp only [δ] at hn ⊢
    linarith
  exact hnorm_le.trans_lt hlt

open scoped Pointwise in
private theorem ae_tendsto_dSequenceAverage_diagonal_inner {G H : Type*} [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    {μ : Measure G} [μ.IsHaarMeasure] {U : ℕ → Set G} (hU : IsDPrimeSequence μ U)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {Φ Ψ : G → H} (hΦm : AEStronglyMeasurable Φ μ) (hΦ2 : LocallyIntegrable (fun x ↦ ‖Φ x‖ ^ 2) μ)
    (hΨm : AEStronglyMeasurable Ψ μ) (hΨ2 : LocallyIntegrable (fun x ↦ ‖Ψ x‖ ^ 2) μ)
    {κ : G × G → ℂ} (hκ : κ =ᵐ[μ.prod μ] fun p ↦ inner ℂ (Φ p.1) (Ψ p.2)) :
    ∀ᵐ x ∂μ, Tendsto (fun n ↦ dSequenceAverage (μ.prod μ) (U n ×ˢ U n) κ (x, x)) atTop
      (𝓝 (inner ℂ (Φ x) (Ψ x))) := by
  have hΦ_loc : LocallyIntegrable Φ μ := by
    rw [locallyIntegrable_iff]
    intro K hK
    refine ((hΦ2.integrableOn_isCompact hK).add
      (integrableOn_const (C := (1 : ℝ)) hK.measure_lt_top.ne)).mono'
      hΦm.restrict (Eventually.of_forall fun y ↦ ?_)
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (‖Φ y‖ - 1), norm_nonneg (Φ y)]
  have hΨ_loc : LocallyIntegrable Ψ μ := by
    rw [locallyIntegrable_iff]
    intro K hK
    refine ((hΨ2.integrableOn_isCompact hK).add
      (integrableOn_const (C := (1 : ℝ)) hK.measure_lt_top.ne)).mono'
      hΨm.restrict (Eventually.of_forall fun y ↦ ?_)
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (‖Ψ y‖ - 1), norm_nonneg (Ψ y)]
  let B : H →L[ℝ] H →L[ℝ] ℂ :=
    LinearMap.mkContinuous₂
      { toFun := fun u ↦
          { toFun := fun v ↦ inner ℂ u v
            map_add' := fun v₁ v₂ ↦ inner_add_right u v₁ v₂
            map_smul' := fun r v ↦ by
              change inner ℂ u (r • v) = r • inner ℂ u v
              rw [← Complex.coe_smul, inner_smul_right, Complex.real_smul] }
        map_add' := fun u₁ u₂ ↦ by ext v; exact inner_add_left u₁ u₂ v
        map_smul' := fun r u ↦ by
          ext v
          change inner ℂ (r • u) v = r • inner ℂ u v
          rw [← Complex.coe_smul, inner_smul_left, Complex.conj_ofReal, Complex.real_smul] }
      1 (fun u v ↦ by rw [one_mul]; exact norm_inner_le_norm u v)
  filter_upwards [ae_tendsto_setAverage_hilbert hU hΦm hΦ2,
    ae_tendsto_setAverage_hilbert hU hΨm hΨ2] with x hxΦ hxΨ
  obtain ⟨K, hK, hKnhds⟩ := exists_compact_mem_nhds x
  have hpre : (fun y : G ↦ x * y) ⁻¹' K ∈ 𝓝 (1 : G) :=
    (continuous_const_mul x).continuousAt.preimage_mem_nhds (by simpa only [mul_one] using hKnhds)
  obtain ⟨N₀, hN₀⟩ := hU.2 _ hpre
  refine (hxΦ.inner hxΨ).congr' ?_
  filter_upwards [eventually_ge_atTop N₀] with n hn
  have hsub : x • U n ⊆ K := by
    rintro _ ⟨y, hy, rfl⟩
    exact hN₀ (hU.1.2.1 hn hy)
  have hΦn : IntegrableOn Φ (x • U n) μ := (hΦ_loc.integrableOn_isCompact hK).mono_set hsub
  have hΨn : IntegrableOn Ψ (x • U n) μ := (hΨ_loc.integrableOn_isCompact hK).mono_set hsub
  have hsmul_prod : (x, x) • (U n ×ˢ U n) = (x • U n) ×ˢ (x • U n) := by
    ext ⟨a, b⟩
    simp only [Set.mem_smul_set, Set.mem_prod, Prod.exists]
    constructor
    · rintro ⟨u, v, ⟨hu, hv⟩, h⟩
      rcases Prod.mk.inj h with ⟨rfl, rfl⟩
      exact ⟨⟨u, hu, rfl⟩, ⟨v, hv, rfl⟩⟩
    · rintro ⟨⟨u, hu, rfl⟩, ⟨v, hv, rfl⟩⟩
      exact ⟨u, v, ⟨hu, hv⟩, rfl⟩
  have hprod_real : (μ.prod μ).real ((x • U n) ×ˢ (x • U n)) =
      μ.real (x • U n) * μ.real (x • U n) := by
    simp only [measureReal_def, Measure.prod_prod, ENNReal.toReal_mul]
  symm
  calc
    dSequenceAverage (μ.prod μ) (U n ×ˢ U n) κ (x, x)
      = ⨍ p in (x • U n) ×ˢ (x • U n), κ p ∂(μ.prod μ) := by
          rw [dSequenceAverage, hsmul_prod]
    _ = ⨍ p in (x • U n) ×ˢ (x • U n), inner ℂ (Φ p.1) (Ψ p.2) ∂(μ.prod μ) :=
          average_congr (ae_restrict_of_ae hκ)
    _ = ((μ.prod μ).real ((x • U n) ×ˢ (x • U n)))⁻¹ •
          ∫ p in (x • U n) ×ˢ (x • U n), B (Φ p.1) (Ψ p.2) ∂(μ.prod μ) := by
          rw [setAverage_eq]
          rfl
    _ = ((μ.real (x • U n))⁻¹ * (μ.real (x • U n))⁻¹) •
          B (∫ y₁ in x • U n, Φ y₁ ∂μ) (∫ y₂ in x • U n, Ψ y₂ ∂μ) := by
          rw [hprod_real, mul_inv, ← Measure.prod_restrict (x • U n) (x • U n),
            integral_prod_bilin B hΦn hΨn]
    _ = inner ℂ (⨍ y₁ in x • U n, Φ y₁ ∂μ) (⨍ y₂ in x • U n, Ψ y₂ ∂μ) := by
          simp only [setAverage_eq, mul_smul]
          change (μ.real (x • U n))⁻¹ • (μ.real (x • U n))⁻¹ • B _ _ =
            B ((μ.real (x • U n))⁻¹ • _) ((μ.real (x • U n))⁻¹ • _)
          rw [map_smul, map_smul, smul_apply]

private theorem exists_row_hilbert_map {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] {μ ν : Measure G} [μ.IsHaarMeasure]
    [IsFiniteMeasureOnCompacts ν] [ν.InnerRegular] {f : G → ℝ≥0}
    (hf : Continuous f) (hf_pos : ∀ x, 0 < f x) (hν : ν = μ.withDensity (fun x ↦ ↑(f x)))
    (a : Lp ℂ 2 (ν.prod ν)) :
    ∃ Φ : G → Lp ℂ 2 ν,
      AEStronglyMeasurable Φ μ ∧
      LocallyIntegrable (fun x ↦ ‖Φ x‖ ^ 2) μ ∧
      ∀ᵐ x ∂μ, (Φ x : G → ℂ) =ᵐ[ν] fun z ↦ conj (a (x, z)) := by
  classical
  have hac_μν : μ ≪ ν :=
    hν ▸ withDensity_absolutelyContinuous' hf.measurable.coe_nnreal_ennreal.aemeasurable
      (Eventually.of_forall fun x ↦ by simpa using (hf_pos x).ne')
  have ha2 := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable a)).mp (Lp.memLp a)
  have hrow : ∀ᵐ x ∂μ, MemLp (fun z ↦ conj (a (x, z))) 2 ν := by
    filter_upwards [hac_μν.ae_le ha2.prod_right_ae] with x hx
    exact (memLp_two_iff_integrable_sq_norm
      (Complex.continuous_conj.comp_stronglyMeasurable
        ((Lp.stronglyMeasurable a).comp_measurable
          (measurable_const.prodMk measurable_id))).aestronglyMeasurable).mpr
      (by simpa only [Function.comp_apply, id_eq, Complex.norm_conj] using hx)
  let Φ (x : G) : Lp ℂ 2 ν :=
    if h : MemLp (fun z ↦ conj (a (x, z))) 2 ν then h.toLp _ else 0
  have hΦae : ∀ᵐ x ∂μ, (Φ x : G → ℂ) =ᵐ[ν] fun z ↦ conj (a (x, z)) := by
    filter_upwards [hrow] with x hx
    simp only [Φ, dite_eq_left hx]
    exact hx.coeFn_toLp
  have hnorm_loc : LocallyIntegrable (fun x ↦ ‖Φ x‖ ^ 2) μ := by
    let E (x : G) : ℝ := ∫ z, ‖a (x, z)‖ ^ 2 ∂ν
    have hE_int : Integrable E ν := ha2.integral_prod_left
    rw [hν, integrable_withDensity_iff_integrable_smul hf.measurable] at hE_int
    have hinv : Continuous (fun x ↦ (f x : ℝ)⁻¹) :=
      (NNReal.continuous_coe.comp hf).inv₀ (fun x ↦ NNReal.coe_ne_zero.mpr (hf_pos x).ne')
    have hE_loc : LocallyIntegrable E μ := by
      refine (hE_int.locallyIntegrable.continuous_smul hinv).congr (Eventually.of_forall fun x ↦ ?_)
      have hx0 : (f x : ℝ) ≠ 0 := by exact_mod_cast (hf_pos x).ne'
      simp only [NNReal.smul_def, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hx0, one_mul]
    refine hE_loc.congr ?_
    filter_upwards [hΦae] with x hx
    rw [← L2.integral_sq_norm (𝕜 := ℂ) (Φ x)]
    apply integral_congr_ae
    filter_upwards [hx] with z hz
    rw [hz, Complex.norm_conj]
  have hΦm : AEStronglyMeasurable Φ μ := by
    let : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
    let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
    have : SecondCountableTopology (Lp ℂ 2 ν) := Lp.SecondCountableTopology
    obtain ⟨ι, e, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := Lp ℂ 2 ν)
    have : Countable ι := by
      refine Pairwise.countable_of_isOpen_disjoint (s := fun i ↦ Metric.ball (e i) (1 / 2))
        ?_ (fun _ ↦ Metric.isOpen_ball) (fun i ↦ ⟨e i, Metric.mem_ball_self (by norm_num)⟩)
      intro i j hij
      apply Metric.ball_disjoint_ball
      have hd : dist (e i) (e j) ^ 2 = 2 := by
        rw [dist_eq_norm, norm_sub_sq (𝕜 := ℂ), e.orthonormal.norm_eq_one i,
          e.orthonormal.norm_eq_one j, e.orthonormal.inner_eq_zero hij]
        norm_num
      nlinarith [dist_nonneg (x := e i) (y := e j)]
    rcases isEmpty_or_nonempty ι with hι | hι
    · have h0 : Φ = fun _ ↦ 0 := by
        funext x
        simpa only [tsum_empty] using (e.hasSum_repr (Φ x)).tsum_eq.symm
      rw [h0]
      exact aestronglyMeasurable_const
    · obtain ⟨g, hg⟩ := exists_surjective_nat ι
      let s (n : ℕ) : Finset ι := (Finset.range n).image g
      have hs : Tendsto s atTop atTop := by
        rw [tendsto_atTop_atTop]
        intro A
        choose k hk using hg
        refine ⟨(A.image k).sup id + 1, fun n hn i hi ↦ Finset.mem_image.mpr ⟨k i, ?_, hk i⟩⟩
        rw [Finset.mem_range]
        exact Nat.lt_of_le_of_lt (Finset.le_sup (f := id) (Finset.mem_image_of_mem k hi))
          (Nat.lt_of_succ_le hn)
      have hcoord (i : ι) : AEStronglyMeasurable (fun x ↦ inner ℂ (e i) (Φ x)) μ := by
        have hsm : StronglyMeasurable (fun p : G × G ↦ conj (a p) * conj (e i p.2)) :=
          (Complex.continuous_conj.comp_stronglyMeasurable (Lp.stronglyMeasurable a)).mul
            (Complex.continuous_conj.comp_stronglyMeasurable
              ((Lp.stronglyMeasurable (e i)).comp_measurable measurable_snd))
        refine (hsm.integral_prod_right' (ν := ν)).aestronglyMeasurable.congr ?_
        filter_upwards [hΦae] with x hx
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [hx] with z hz
        rw [RCLike.inner_apply, hz]
      refine aestronglyMeasurable_of_tendsto_ae atTop
        (f := fun n x ↦ ∑ i ∈ s n, inner ℂ (e i) (Φ x) • e i) ?_ ?_
      · intro n
        refine Finset.aestronglyMeasurable_fun_sum (s n) fun i _ ↦
          (hcoord i).smul aestronglyMeasurable_const
      · refine Eventually.of_forall fun x ↦ ?_
        have hsum := (e.hasSum_repr (Φ x)).comp hs
        simpa only [Function.comp_def, e.repr_apply_apply] using hsum
  exact ⟨Φ, hΦm, hnorm_loc, hΦae⟩

private theorem exists_diagonal_smoothening_factorization {G : Type*} [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    {μ ν : Measure G} [μ.IsHaarMeasure] [IsFiniteMeasureOnCompacts ν] [ν.InnerRegular]
    {f : G → ℝ≥0} {k : Lp ℂ 2 (ν.prod ν)} {κ : G × G → ℂ}
    (hκ : κ =ᵐ[ν.prod ν] k) (hf : Continuous f) (hf_pos : ∀ x, 0 < f x)
    (hν : ν = μ.withDensity (fun x ↦ ↑(f x)))
    (hT : IsNuclearOperator (integralKernelOperator ν k).val) :
    ∃ Φ Ψ : G → Lp ℂ 2 ν,
      AEStronglyMeasurable Φ μ ∧ LocallyIntegrable (fun x ↦ ‖Φ x‖ ^ 2) μ ∧
      AEStronglyMeasurable Ψ μ ∧ LocallyIntegrable (fun x ↦ ‖Ψ x‖ ^ 2) μ ∧
      (κ =ᵐ[μ.prod μ] fun p ↦ inner ℂ (Φ p.1) (Ψ p.2)) ∧
      Integrable (fun x ↦ inner ℂ (Φ x) (Ψ x)) ν ∧
      hilbertTrace ⟨(integralKernelOperator ν k).val, hT⟩ = ∫ x, inner ℂ (Φ x) (Ψ x) ∂ν := by
  obtain ⟨a, b, -, hconv, -, hdiagL1, htrace⟩ := exists_integralKernel_smoothening ν k hT
  have hac_μν : μ ≪ ν :=
    hν ▸ withDensity_absolutelyContinuous' hf.measurable.coe_nnreal_ennreal.aemeasurable
      (Eventually.of_forall fun x ↦ by simpa using (hf_pos x).ne')
  have hac_νμ : ν ≪ μ := hν ▸ withDensity_absolutelyContinuous _ _
  have hac_prod : μ.prod μ ≪ ν.prod ν := hac_μν.prod hac_μν
  obtain ⟨Φ, hΦm, hΦ2, hΦae⟩ := exists_row_hilbert_map hf hf_pos hν a
  have hbswap := (Lp.memLp b).comp_measurePreserving (Measure.measurePreserving_swap (μ := ν) (ν := ν))
  have hb'mem : MemLp (fun p : G × G ↦ conj (b p.swap)) 2 (ν.prod ν) :=
    hbswap.congr_norm (Complex.continuous_conj.comp_aestronglyMeasurable hbswap.aestronglyMeasurable)
      (Eventually.of_forall fun p ↦ (Complex.norm_conj (b p.swap)).symm)
  let b' := hb'mem.toLp (fun p : G × G ↦ conj (b p.swap))
  obtain ⟨Ψ, hΨm, hΨ2, hΨae⟩ := exists_row_hilbert_map hf hf_pos hν b'
  have hΨb : ∀ᵐ y ∂μ, (Ψ y : G → ℂ) =ᵐ[ν] fun z ↦ b (z, y) := by
    filter_upwards [hΨae, hac_μν.ae_le (Measure.ae_ae_of_ae_prod hb'mem.coeFn_toLp)] with y hy hb'y
    filter_upwards [hy, hb'y] with z hz₁ hz₂
    rw [hz₁, hz₂, Complex.conj_conj]
    rfl
  have hinner_pt : ∀ᵐ p ∂(μ.prod μ), inner ℂ (Φ p.1) (Ψ p.2) = ∫ z, a (p.1, z) * b (z, p.2) ∂ν := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hΦae,
      Measure.quasiMeasurePreserving_snd.ae hΨb] with p hp₁ hp₂
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hp₁, hp₂] with z hz₁ hz₂
    rw [RCLike.inner_apply, hz₁, hz₂, Complex.conj_conj, mul_comm]
  have hκ_eq : κ =ᵐ[μ.prod μ] fun p ↦ inner ℂ (Φ p.1) (Ψ p.2) := by
    filter_upwards [hac_prod.ae_le hκ, hac_prod.ae_le hconv, hinner_pt] with p h1 h2 h3
    rw [h1, ← h2.2, h3]
  have hdiag_eq : (fun x ↦ ∫ z, a (x, z) * b (z, x) ∂ν) =ᵐ[ν] fun x ↦ inner ℂ (Φ x) (Ψ x) := by
    filter_upwards [hac_νμ.ae_le hΦae, hac_νμ.ae_le hΨb] with x hx₁ hx₂
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hx₁, hx₂] with z hz₁ hz₂
    rw [RCLike.inner_apply, hz₁, hz₂, Complex.conj_conj, mul_comm]
  exact ⟨Φ, Ψ, hΦm, hΦ2, hΨm, hΨ2, hκ_eq, hdiagL1.congr hdiag_eq,
    htrace.trans (integral_congr_ae hdiag_eq)⟩

section DiagonalTrace

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  {μ ν : Measure G} [μ.IsHaarMeasure] [IsFiniteMeasureOnCompacts ν] [ν.InnerRegular]
  {U : ℕ → Set G} {f : G → ℝ≥0} {k : Lp ℂ 2 (ν.prod ν)}
  {κ : G × G → ℂ} (hκ : κ =ᵐ[ν.prod ν] k)
  (hU : IsDPrimeSequence μ U) (hBorel : ∀ n, MeasurableSet (U n))
  (hf : Continuous f) (hf_pos : ∀ x, 0 < f x) (hν : ν = μ.withDensity (fun x ↦ ↑(f x)))
  (hT : IsNuclearOperator (integralKernelOperator ν k).val)

include hU hBorel hf hf_pos hν hT hκ

/-- Paper: Theorem 12.1.1.2, p. 499. For Haar-almost every `x`, the product
averages of the chosen kernel representative converge at `(x, x)`. -/
theorem ae_diagonal_mem_dSequenceRegularSet :
    ∀ᵐ x ∂μ, (x, x) ∈ dSequenceRegularSet (μ.prod μ) (fun n ↦ U n ×ˢ U n) κ := by
  let : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
  have : SecondCountableTopology (Lp ℂ 2 ν) := Lp.SecondCountableTopology
  obtain ⟨Φ, Ψ, hΦm, hΦ2, hΨm, hΨ2, hκ_eq, -, -⟩ :=
    exists_diagonal_smoothening_factorization hκ hf hf_pos hν hT
  filter_upwards [ae_tendsto_dSequenceAverage_diagonal_inner hU hΦm hΦ2 hΨm hΨ2 hκ_eq] with x hx
  exact ⟨inner ℂ (Φ x) (Ψ x), hx⟩

/-- Paper: Theorem 12.1.1.2(1), p. 499. The smoothened function represents the
same Hilbert-Schmidt kernel in the weighted product measure. -/
theorem dSequenceKernelSmoothening_ae_eq :
    dSequenceKernelSmoothening μ U κ =ᵐ[ν.prod ν] (k : G × G → ℂ) := by
  let w (p : G × G) := f p.1 * f p.2
  have hw : Continuous w := (hf.comp continuous_fst).mul (hf.comp continuous_snd)
  have hwpos (p : G × G) : 0 < (w p : ℝ) := by
    exact_mod_cast mul_pos (hf_pos p.1) (hf_pos p.2)
  have hprod : ν.prod ν = (μ.prod μ).withDensity (fun p ↦ (w p : ℝ≥0∞)) := by
    rw [hν]
    have hm : Measurable (fun x ↦ (f x : ℝ≥0∞)) := (ENNReal.continuous_coe.comp hf).measurable
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
  have hhaar : LocallyIntegrable κ (μ.prod μ) := by
    refine (hweighted.continuous_smul hinv).congr (Filter.Eventually.of_forall fun p ↦ ?_)
    simp only [smul_smul, inv_mul_cancel₀ (hwpos p).ne', one_smul]
  -- The product-sequence theorem uses the Borel measurable structure on the product.
  have rectSeq [m : MeasurableSpace (G × G)] (hm : m = borel _)
      (η : Measure (G × G)) [η.IsHaarMeasure]
      (hrect : ∀ s t : Set G, MeasurableSet s → MeasurableSet t → η (s ×ˢ t) = μ s * μ t) :
      IsDPrimeSequence η (fun n ↦ U n ×ˢ U n) := by
    subst m
    exact IsDPrimeSequence.prod hrect hU hU
  have hseq : IsDPrimeSequence (μ.prod μ) (fun n ↦ U n ×ˢ U n) :=
    rectSeq BorelSpace.measurable_eq _ (fun s t _ _ ↦ Measure.prod_prod s t)
  have hac : ν.prod ν ≪ μ.prod μ := hprod ▸ withDensity_absolutelyContinuous _ _
  refine Filter.EventuallyEq.trans ?_ hκ
  filter_upwards [hac.ae_le (ae_tendsto_dSequenceAverage hseq hhaar)] with p hp
  have hreg : p ∈ dSequenceRegularSet (μ.prod μ) (fun n ↦ U n ×ˢ U n) κ := ⟨κ p, hp⟩
  simpa only [dSequenceKernelSmoothening, dSequenceSmootheningOrZero, dite_eq_left hreg,
    dSequenceSmoothening] using hp.limUnder_eq

-- TODO(paper-gap): The proof on p. 500 uses projections onto individual eigenspaces
-- as if they exhausted the operator. Cumulative spectral projections are needed.
-- The reduction to positive operators also requires a common full-measure set of
-- diagonal regularity, where linearity of the limit applies.
/-- Paper: Theorem 12.1.1.2(1), p. 499. The smoothened diagonal is absolutely
integrable for the weighted measure, and its integral equals the nuclear trace. -/
theorem integral_dSequenceKernelSmoothening_diagonal :
    Integrable (fun x ↦ dSequenceKernelSmoothening μ U κ (x, x)) ν ∧
      (∫ x, dSequenceKernelSmoothening μ U κ (x, x) ∂ν) =
        hilbertTrace ⟨(integralKernelOperator ν k).val, hT⟩ := by
  let : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
  have : SecondCountableTopology (Lp ℂ 2 ν) := Lp.SecondCountableTopology
  obtain ⟨Φ, Ψ, hΦm, hΦ2, hΨm, hΨ2, hκ_eq, hint, htrace⟩ :=
    exists_diagonal_smoothening_factorization hκ hf hf_pos hν hT
  have hac_νμ : ν ≪ μ := hν ▸ withDensity_absolutelyContinuous _ _
  have hdiag : (fun x ↦ inner ℂ (Φ x) (Ψ x)) =ᵐ[ν]
      fun x ↦ dSequenceKernelSmoothening μ U κ (x, x) := by
    filter_upwards [hac_νμ.ae_le
      (ae_tendsto_dSequenceAverage_diagonal_inner hU hΦm hΦ2 hΨm hΨ2 hκ_eq)] with x hx
    have hreg : (x, x) ∈ dSequenceRegularSet (μ.prod μ) (fun n ↦ U n ×ˢ U n) κ := ⟨_, hx⟩
    have hpt : dSequenceKernelSmoothening μ U κ (x, x) = inner ℂ (Φ x) (Ψ x) := by
      simpa only [dSequenceKernelSmoothening, dSequenceSmootheningOrZero, dite_eq_left hreg,
        dSequenceSmoothening] using hx.limUnder_eq
    exact hpt.symm
  exact ⟨hint.congr hdiag, (integral_congr_ae hdiag.symm).trans htrace.symm⟩

-- TODO(paper-gap): The proof on p. 501 uses Corollary A.5.4.3 at all regular
-- points. See the rank-one counterexample in Sec1a_Printed.
/-- Paper: Theorem 12.1.1.2(2), p. 499. A compactly supported continuous
multiplier commutes with kernel smoothening almost everywhere for product Haar measure.
Deviation: The printed pointwise identity is restricted to product-almost-everywhere
equality. -/
theorem dSequenceKernelSmoothening_mul_continuous (ρ : G → ℂ)
    (hρ : Continuous ρ) (hρc : HasCompactSupport ρ) :
    let kρ := fun p : G × G ↦ ρ p.1 * κ p
    dSequenceKernelSmoothening μ U kρ =ᵐ[μ.prod μ]
      (fun p ↦ ρ p.1 * dSequenceKernelSmoothening μ U κ p) := by
  have _ := hρc
  have hhaar := locallyIntegrable_of_weighted_memLp_prod hκ hf hf_pos hν
  have hhaar_ρ : LocallyIntegrable (fun p : G × G ↦ ρ p.1 * κ p) (μ.prod μ) := by
    simpa only [Function.comp_apply, smul_eq_mul] using hhaar.continuous_smul (hρ.comp continuous_fst)
  filter_upwards [dSequenceKernelSmoothening_ae_eq_haar hU hhaar,
    dSequenceKernelSmoothening_ae_eq_haar hU hhaar_ρ] with p hp hpρ
  rw [hpρ, hp]

/-- Paper: Theorem 12.1.1.2(2), p. 499. Along the diagonal, a compactly
supported continuous multiplier commutes with kernel smoothening for Haar-almost every center.
Deviation: The printed pointwise identity is restricted to almost-everywhere equality
in the Haar measure on the diagonal. -/
theorem dSequenceKernelSmoothening_mul_continuous_diagonal (ρ : G → ℂ)
    (hρ : Continuous ρ) (hρc : HasCompactSupport ρ) :
    let kρ := fun p : G × G ↦ ρ p.1 * κ p
    ∀ᵐ x ∂μ, dSequenceKernelSmoothening μ U kρ (x, x) =
      ρ x * dSequenceKernelSmoothening μ U κ (x, x) := by
  have _ := hρc
  let : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
  have : SecondCountableTopology (Lp ℂ 2 ν) := Lp.SecondCountableTopology
  obtain ⟨Φ, Ψ, hΦm, hΦ2, hΨm, hΨ2, hκ_eq, -, -⟩ :=
    exists_diagonal_smoothening_factorization hκ hf hf_pos hν hT
  let Φρ (x : G) : Lp ℂ 2 ν := conj (ρ x) • Φ x
  have hΦρm : AEStronglyMeasurable Φρ μ :=
    (Complex.continuous_conj.comp hρ).aestronglyMeasurable.smul hΦm
  have hΦρ2 : LocallyIntegrable (fun x ↦ ‖Φρ x‖ ^ 2) μ := by
    have hcont : Continuous (fun x ↦ ‖ρ x‖ ^ 2) := hρ.norm.pow 2
    refine (hΦ2.continuous_smul hcont).congr (Eventually.of_forall fun x ↦ ?_)
    simp only [Φρ, smul_eq_mul, norm_smul, Complex.norm_conj, mul_pow]
  have hkρ_eq : (fun p : G × G ↦ ρ p.1 * κ p) =ᵐ[μ.prod μ] fun p ↦ inner ℂ (Φρ p.1) (Ψ p.2) := by
    filter_upwards [hκ_eq] with p hp
    simp only [Φρ, inner_smul_left, Complex.conj_conj, hp]
  filter_upwards [ae_tendsto_dSequenceAverage_diagonal_inner hU hΦm hΦ2 hΨm hΨ2 hκ_eq,
    ae_tendsto_dSequenceAverage_diagonal_inner hU hΦρm hΦρ2 hΨm hΨ2 hkρ_eq] with x hx hxρ
  have hreg : (x, x) ∈ dSequenceRegularSet (μ.prod μ) (fun n ↦ U n ×ˢ U n) κ := ⟨_, hx⟩
  have hregρ : (x, x) ∈ dSequenceRegularSet (μ.prod μ) (fun n ↦ U n ×ˢ U n)
      (fun p : G × G ↦ ρ p.1 * κ p) := ⟨_, hxρ⟩
  have h1 : dSequenceKernelSmoothening μ U κ (x, x) = inner ℂ (Φ x) (Ψ x) := by
    simpa only [dSequenceKernelSmoothening, dSequenceSmootheningOrZero, dite_eq_left hreg,
      dSequenceSmoothening] using hx.limUnder_eq
  have h2 : dSequenceKernelSmoothening μ U (fun p : G × G ↦ ρ p.1 * κ p) (x, x) =
      inner ℂ (Φρ x) (Ψ x) := by
    simpa only [dSequenceKernelSmoothening, dSequenceSmootheningOrZero, dite_eq_left hregρ,
      dSequenceSmoothening] using hxρ.limUnder_eq
  rw [h2, h1]
  simp only [Φρ, inner_smul_left, Complex.conj_conj]

/-- Paper: Theorem 12.1.1.2(2), p. 499. Multiplying either representative by
the bounded symbol in the target variable gives a kernel of the composed
operator. The multiplier is pointwise multiplication on L² classes. -/
theorem integralKernelOperator_mul_dSequenceKernelSmoothening (ρ : Lp ℂ ∞ ν) :
    let Mρ := (ContinuousLinearMap.mul ℂ ℂ).holderL ν ∞ 2 2 ρ
    ∃ K : Lp ℂ 2 (ν.prod ν),
      (integralKernelOperator ν K).val = Mρ * (integralKernelOperator ν k).val ∧
        (K : G × G → ℂ) =ᵐ[ν.prod ν] (fun p ↦ ρ p.1 * κ p) ∧
        (K : G × G → ℂ) =ᵐ[ν.prod ν] (fun p ↦ ρ p.1 * dSequenceKernelSmoothening μ U κ p) :=
  by
  intro Mρ
  let a : G × G → ℂ := fun p ↦ ρ p.1
  have ha : MemLp a ∞ (ν.prod ν) := by
    have hmρ := Lp.aestronglyMeasurable ρ
    have hm : AEStronglyMeasurable a (ν.prod ν) := hmρ.comp_fst
    rw [memLp_iff, eLpNorm_exponent_top hm, eLpNormEssSup_lt_top_iff_isBoundedUnder]
    have hb := (Lp.memLp ρ).eLpNorm_lt_top
    rw [eLpNorm_exponent_top hmρ, eLpNormEssSup_lt_top_iff_isBoundedUnder] at hb
    obtain ⟨C, hC⟩ := hb
    exact ⟨C, Measure.quasiMeasurePreserving_fst.ae hC⟩
  let b : G × G → ℂ := fun p ↦ a p * k p
  have hb : MemLp b 2 (ν.prod ν) := ha.mul (Lp.memLp k)
  let K := hb.toLp b
  have hK : (K : G × G → ℂ) =ᵐ[ν.prod ν] b := hb.coeFn_toLp
  refine ⟨K, ?_, ?_, ?_⟩
  · ext1 g
    apply Lp.ext
    have hM : ⇑(Mρ ((integralKernelOperator ν k).val g)) =ᵐ[ν]
        fun x ↦ ρ x * ((integralKernelOperator ν k).val g) x :=
      (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2) ρ _
    filter_upwards [integralKernelOperator_apply ν K g, integralKernelOperator_apply ν k g,
      Measure.ae_ae_of_ae_prod hK, hM] with x hx hx' hrow hmult
    change (integralKernelOperator ν K).val g x = Mρ ((integralKernelOperator ν k).val g) x
    rw [hx.2, hmult, hx'.2, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hrow] with y hy
    exact (congrArg (· * g y) hy).trans (mul_assoc _ _ _)
  · filter_upwards [hK, hκ] with p hp hrep
    exact hp.trans (congrArg (ρ p.1 * ·) hrep.symm)
  · filter_upwards [hK, dSequenceKernelSmoothening_ae_eq hκ hU hBorel hf hf_pos hν hT]
      with p hp hs
    exact hp.trans (congrArg (ρ p.1 * ·) hs.symm)

/-- Paper: Theorem 12.1.1.2(2), p. 499. The weighted integral of the
smoothened diagonal against an essentially bounded symbol equals the trace
of the operator followed by multiplication by that symbol. -/
theorem integral_mul_dSequenceKernelSmoothening_diagonal (ρ : Lp ℂ ∞ ν) :
    let Mρ := (ContinuousLinearMap.mul ℂ ℂ).holderL ν ∞ 2 2 ρ
    let T : nuclearEndomorphisms (Lp ℂ 2 ν) := ⟨(integralKernelOperator ν k).val, hT⟩
    Integrable (fun x ↦ ρ x * dSequenceKernelSmoothening μ U κ (x, x)) ν ∧
      (∫ x, ρ x * dSequenceKernelSmoothening μ U κ (x, x) ∂ν) =
        hilbertTrace ⟨Mρ * T.val, mul_mem_nuclearEndomorphisms_left Mρ T⟩ := by sorry

section FiniteRank

variable (ks : ℕ → Lp ℂ 2 (ν.prod ν)) (κs : ℕ → G × G → ℂ)
  (hκs : ∀ n, κs n =ᵐ[ν.prod ν] ks n)
  (hrank : ∀ n, FiniteDimensional ℂ (integralKernelOperator ν (ks n)).val.toLinearMap.range)
  (hSn : ∀ n, IsNuclearOperator (integralKernelOperator ν (ks n)).val)
  (hS1 : Tendsto (fun n ↦ traceNorm
    ((⟨(integralKernelOperator ν (ks n)).val, hSn n⟩ : nuclearEndomorphisms (Lp ℂ 2 ν)) -
      ⟨(integralKernelOperator ν k).val, hT⟩)) atTop (𝓝 0))
  (hS2 : Tendsto (fun n ↦ schattenNorm
    (integralKernelOperator ν (ks n) - integralKernelOperator ν k)) atTop (𝓝 0))

include hκs hrank hS1 hS2

/-- Paper: Theorem 12.1.1.2(3), p. 499. Under trace-norm and Hilbert-Schmidt
convergence of the finite-rank operators, their kernels converge in weighted
product L². The smoothenings represent the same sequence and limit there. -/
theorem tendsto_dSequenceKernelSmoothening_L2 :
    Tendsto ks atTop (𝓝 k) ∧
      (∀ n, dSequenceKernelSmoothening μ U (κs n) =ᵐ[ν.prod ν] (ks n : G × G → ℂ)) ∧
      dSequenceKernelSmoothening μ U κ =ᵐ[ν.prod ν] (k : G × G → ℂ) := by
  refine ⟨tendsto_iff_norm_sub_tendsto_zero.mpr ?_, fun n ↦
    dSequenceKernelSmoothening_ae_eq (hκs n) hU hBorel hf hf_pos hν (hSn n),
    dSequenceKernelSmoothening_ae_eq hκ hU hBorel hf hf_pos hν hT⟩
  let swap := Lp.compMeasurePreservingₗ (E := ℂ) (p := 2) ℂ Prod.swap
    (Measure.measurePreserving_swap (μ := ν) (ν := ν))
  let A := (hilbertSchmidtOperators_equiv_Lp_prod ν ν).choose.toLinearMap.comp swap
  have hsub (n : ℕ) :
      integralKernelOperator ν (ks n - k) = integralKernelOperator ν (ks n) - integralKernelOperator ν k :=
    map_sub A (ks n) k
  simpa only [← hsub, schattenNorm_integralKernelOperator] using hS2

/-- Paper: Theorem 12.1.1.2(3), p. 499. The smoothened diagonals converge
weakly in weighted L¹, expressed by testing against all weighted L∞ classes. -/
theorem tendsto_dSequenceKernelSmoothening_diagonal_weak :
    let ds := fun n x ↦ dSequenceKernelSmoothening μ U (κs n) (x, x)
    let d := fun x ↦ dSequenceKernelSmoothening μ U κ (x, x)
    (∀ n, Integrable (ds n) ν) ∧ Integrable d ν ∧
      ∀ ρ : Lp ℂ ∞ ν, Tendsto (fun n ↦ ∫ x, ρ x * ds n x ∂ν) atTop
        (𝓝 (∫ x, ρ x * d x ∂ν)) := by
  refine ⟨fun n ↦ (integral_dSequenceKernelSmoothening_diagonal
    (hκs n) hU hBorel hf hf_pos hν (hSn n)).1,
    (integral_dSequenceKernelSmoothening_diagonal hκ hU hBorel hf hf_pos hν hT).1, ?_⟩
  intro ρ
  let M := (ContinuousLinearMap.mul ℂ ℂ).holderL ν ∞ 2 2 ρ
  let left (A : nuclearEndomorphisms (Lp ℂ 2 ν)) : nuclearEndomorphisms (Lp ℂ 2 ν) :=
    ⟨M * A.val, mul_mem_nuclearEndomorphisms_left M A⟩
  let Ts (n : ℕ) : nuclearEndomorphisms (Lp ℂ 2 ν) := ⟨(integralKernelOperator ν (ks n)).val, hSn n⟩
  let T : nuclearEndomorphisms (Lp ℂ 2 ν) := ⟨(integralKernelOperator ν k).val, hT⟩
  have hleft (n : ℕ) : left (Ts n) - left T = left (Ts n - T) := Subtype.ext (mul_sub ..).symm
  obtain ⟨tr, htr⟩ := hilbertTrace_linear (H := Lp ℂ 2 ν)
  have hlim : Tendsto (fun n ↦ hilbertTrace (left (Ts n))) atTop (𝓝 (hilbertTrace (left T))) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp only [← htr, ← map_sub, hleft]
    simp only [htr]
    apply squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦
      (norm_hilbertTrace_le _).trans (traceNorm_mul_left_le M (Ts n - T)))
    simpa only [mul_zero] using hS1.const_mul ‖M‖
  have hn (n : ℕ) := (integral_mul_dSequenceKernelSmoothening_diagonal
    (hκs n) hU hBorel hf hf_pos hν (hSn n) ρ).2
  have h := (integral_mul_dSequenceKernelSmoothening_diagonal hκ hU hBorel hf hf_pos hν hT ρ).2
  simpa only [hn, h] using hlim

end FiniteRank

end DiagonalTrace

section Basis

variable {G : Type*} [MeasurableSpace G]

/-- Paper: (12.1.1.4)–(12.1.1.5), p. 499. The bilinear pairing between the
weighted and reciprocal-weighted L² spaces integrates their product against Haar measure. -/
def weightedL2Duality (μ : Measure G) {ν νdual : Measure G} {f : G → ℝ≥0}
    (_hf : Measurable f) (_hf_pos : ∀ x, 0 < f x)
    (_hν : ν = μ.withDensity (fun x ↦ ↑(f x)))
    (_hνdual : νdual = μ.withDensity (fun x ↦ ↑((f x)⁻¹)))
    (u : Lp ℂ 2 ν) (v : Lp ℂ 2 νdual) : ℂ :=
  ∫ x, u x * v x ∂μ

/-- Paper: (12.1.1.5), p. 499. At unit weight the bilinear pairing with a
complex conjugate gives the squared L² norm. -/
theorem weightedL2Duality_conj (μ : Measure G) (u v : Lp ℂ 2 μ)
    (hv : (v : G → ℂ) =ᵐ[μ] fun x ↦ conj (u x)) :
    weightedL2Duality μ (f := fun _ ↦ 1) measurable_const (fun _ ↦ zero_lt_one)
      (by simp) (by simp) u v = (‖u‖ ^ 2 : ℝ) := by
  calc
    _ = ∫ x, inner ℂ (u x) (u x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hv] with x hx
      rw [hx, RCLike.inner_apply]
    _ = inner ℂ u u := (L2.inner_def u u).symm
    _ = _ := by simp [inner_self_eq_norm_sq_to_K]

private theorem weightedL2Duality_equiv_absCont (μ : Measure G) {g : G → ℝ≥0}
    (hg : Measurable g) (hpos : ∀ x, 0 < g x) :
    μ ≪ μ.withDensity (fun x ↦ (g x : ℝ≥0∞)) :=
  withDensity_absolutelyContinuous' hg.coe_nnreal_ennreal.aemeasurable
    (Filter.Eventually.of_forall fun x ↦ by simpa using (hpos x).ne')

private theorem weightedL2Duality_equiv_rep (μ : Measure G) {g : G → ℝ≥0}
    (hg : Measurable g) (hpos : ∀ x, 0 < g x)
    {ν₁ ν₂ : Measure G} (h₁ : ν₁ = μ.withDensity (fun x ↦ (g x : ℝ≥0∞)))
    (h₂ : ν₂ = μ.withDensity (fun x ↦ (((g x)⁻¹ : ℝ≥0) : ℝ≥0∞))) (v : Lp ℂ 2 ν₂) :
    ∃ W : Lp ℂ 2 ν₁,
      (W : G → ℂ) =ᵐ[μ] (fun x ↦ conj (v x) / (g x : ℂ)) ∧
      ∀ u : Lp ℂ 2 ν₁,
        Integrable (fun x ↦ u x * v x) μ ∧ ∫ x, u x * v x ∂μ = inner ℂ W u := by
  subst h₁ h₂
  have hgi : Measurable fun x ↦ (g x)⁻¹ := hg.inv
  have hac1 := weightedL2Duality_equiv_absCont μ hg hpos
  let w : G → ℂ := fun x ↦ conj (v x) / (g x : ℂ)
  have hwm : StronglyMeasurable w :=
    (Complex.continuous_conj.comp_stronglyMeasurable (Lp.stronglyMeasurable v)).div
      (Complex.measurable_ofReal.comp (measurable_coe_nnreal_real.comp hg)).stronglyMeasurable
  have hmem : MemLp w 2 (μ.withDensity (fun x ↦ (g x : ℝ≥0∞))) := by
    rw [memLp_two_iff_integrable_sq_norm hwm.aestronglyMeasurable,
      integrable_withDensity_iff_integrable_smul hg]
    have hv2 := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable v)).mp (Lp.memLp v)
    rw [integrable_withDensity_iff_integrable_smul hgi] at hv2
    refine hv2.congr (Filter.Eventually.of_forall fun x ↦ ?_)
    have hx := (hpos x).ne'
    simp only [w, NNReal.smul_def, smul_eq_mul, norm_div, Complex.norm_conj, NNReal.coe_inv,
      Complex.norm_real, Real.norm_eq_abs, NNReal.abs_eq]
    field_simp
  refine ⟨hmem.toLp w, hac1.ae_le hmem.coeFn_toLp, fun u ↦ ?_⟩
  have hpt : (fun x ↦ g x • inner ℂ ((hmem.toLp w) x) (u x)) =ᵐ[μ] fun x ↦ u x * v x := by
    filter_upwards [hac1.ae_le hmem.coeFn_toLp] with x hx
    rw [hx]
    have hx0 : (g x : ℂ) ≠ 0 := by exact_mod_cast (hpos x).ne'
    simp only [w, NNReal.smul_def, RCLike.inner_apply, map_div₀, Complex.conj_conj,
      Complex.conj_ofReal, Complex.real_smul]
    field_simp
  have hint := L2.integrable_inner (𝕜 := ℂ) (hmem.toLp w) u
  rw [integrable_withDensity_iff_integrable_smul hg] at hint
  refine ⟨hint.congr hpt, ?_⟩
  rw [L2.inner_def, integral_withDensity_eq_integral_smul hg]
  exact (integral_congr_ae hpt).symm

/-- Paper: (12.1.1.4)–(12.1.1.5), p. 499. Each continuous linear functional on
the weighted L² space has a unique representing vector for the reciprocal weight.
Deviation: The isometry implicit in the pairing is explicit here so it can
supply the dual basis and the transpose used in part (4). -/
theorem weightedL2Duality_equiv (μ : Measure G) {ν νdual : Measure G} {f : G → ℝ≥0}
    (hf : Measurable f) (hf_pos : ∀ x, 0 < f x)
    (hν : ν = μ.withDensity (fun x ↦ ↑(f x)))
    (hνdual : νdual = μ.withDensity (fun x ↦ ↑((f x)⁻¹))) :
    ∃! J : StrongDual ℂ (Lp ℂ 2 ν) ≃ₗᵢ[ℂ] Lp ℂ 2 νdual, ∀ ℓ u,
      Integrable (fun x ↦ u x * J ℓ x) μ ∧
        weightedL2Duality μ hf hf_pos hν hνdual u (J ℓ) = ℓ u := by
  have hfi_pos : ∀ x, 0 < (f x)⁻¹ := fun x ↦ inv_pos.mpr (hf_pos x)
  have hfi : Measurable fun x ↦ (f x)⁻¹ := hf.inv
  choose M hMae hM using weightedL2Duality_equiv_rep μ hf hf_pos hν hνdual
  subst hν hνdual
  have hac2 := weightedL2Duality_equiv_absCont μ hfi hfi_pos
  have hνac := withDensity_absolutelyContinuous μ (fun x ↦ (f x : ℝ≥0∞))
  have hnorm : ∀ v, ‖M v‖ = ‖v‖ := by
    intro v
    have h1 : inner ℂ (M v) (M v) = inner ℂ v v := by
      rw [← (hM v (M v)).2, L2.inner_def, integral_withDensity_eq_integral_smul hfi]
      refine integral_congr_ae ?_
      filter_upwards [hMae v] with x hx
      rw [hx]
      have hx0 : (f x : ℂ) ≠ 0 := by exact_mod_cast (hf_pos x).ne'
      simp only [NNReal.smul_def, RCLike.inner_apply, NNReal.coe_inv, Complex.real_smul,
        Complex.ofReal_inv]
      field_simp
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h1
    have h3 : ‖M v‖ ^ 2 = ‖v‖ ^ 2 := by exact_mod_cast h1
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h3
  let R : Lp ℂ 2 (μ.withDensity fun x ↦ ↑((f x)⁻¹)) →ₗ[ℂ]
      StrongDual ℂ (Lp ℂ 2 (μ.withDensity fun x ↦ ↑(f x))) :=
    { toFun := fun v ↦ InnerProductSpace.toDual ℂ _ (M v)
      map_add' := fun v₁ v₂ ↦ by
        ext u
        rw [add_apply]
        simp only [InnerProductSpace.toDual_apply_apply]
        rw [← (hM _ u).2, ← (hM v₁ u).2, ← (hM v₂ u).2, ← integral_add (hM v₁ u).1 (hM v₂ u).1]
        refine integral_congr_ae ?_
        filter_upwards [hac2.ae_le (Lp.coeFn_add v₁ v₂)] with x hx
        rw [hx, Pi.add_apply, mul_add]
      map_smul' := fun c v ↦ by
        ext u
        rw [RingHom.id_apply, smul_apply]
        simp only [InnerProductSpace.toDual_apply_apply]
        rw [← (hM _ u).2, ← (hM v u).2, smul_eq_mul, ← integral_const_mul]
        refine integral_congr_ae ?_
        filter_upwards [hac2.ae_le (Lp.coeFn_smul c v)] with x hx
        rw [hx, Pi.smul_apply, smul_eq_mul]
        ring }
  have hR : ∀ v u, R v u = ∫ x, u x * v x ∂μ := fun v u ↦ (hM v u).2.symm
  let Ri : Lp ℂ 2 (μ.withDensity fun x ↦ ↑((f x)⁻¹)) →ₗᵢ[ℂ]
      StrongDual ℂ (Lp ℂ 2 (μ.withDensity fun x ↦ ↑(f x))) :=
    { toLinearMap := R
      norm_map' := fun v ↦ by
        change ‖InnerProductSpace.toDual ℂ _ (M v)‖ = ‖v‖
        rw [LinearIsometryEquiv.norm_map, hnorm] }
  have hsurj : Function.Surjective Ri := by
    intro ℓ
    let y := (InnerProductSpace.toDual ℂ _).symm ℓ
    obtain ⟨V, hVae, -⟩ := weightedL2Duality_equiv_rep μ (g := fun x ↦ (f x)⁻¹) hfi hfi_pos rfl (by simp) y
    refine ⟨V, ?_⟩
    have hMV : M V = y := by
      refine Lp.ext (hνac.ae_le ?_)
      filter_upwards [hMae V, hVae] with x h1 h2
      rw [h1, h2]
      have hx0 : (f x : ℂ) ≠ 0 := by exact_mod_cast (hf_pos x).ne'
      simp only [map_div₀, Complex.conj_conj, NNReal.coe_inv, Complex.ofReal_inv, map_inv₀,
        Complex.conj_ofReal]
      field_simp
    change InnerProductSpace.toDual ℂ _ (M V) = ℓ
    rw [hMV, LinearIsometryEquiv.apply_symm_apply]
  let J := (LinearIsometryEquiv.ofSurjective Ri hsurj).symm
  have hJ : ∀ ℓ, Ri (J ℓ) = ℓ := fun ℓ ↦
    (LinearIsometryEquiv.ofSurjective Ri hsurj).apply_symm_apply ℓ
  refine ⟨J, fun ℓ u ↦ ⟨(hM _ u).1, ?_⟩, fun J' hJ' ↦ ?_⟩
  · change ∫ x, u x * J ℓ x ∂μ = ℓ u
    rw [← hR]
    exact DFunLike.congr_fun (hJ ℓ) u
  · refine LinearIsometryEquiv.ext fun ℓ ↦ Ri.injective ?_
    rw [hJ ℓ]
    ext u
    change R (J' ℓ) u = ℓ u
    exact (hR _ _).trans (hJ' ℓ u).2

/-- Paper: (12.1.1.6), p. 499. The partial kernel is the sum through index
`N` of the basis vector in the target variable times the transposed dual
vector divided by the weight in the source variable. -/
def schauderKernelPartialSum {ν νdual : Measure G} (f : G → ℝ≥0)
    (φ : ℕ → Lp ℂ 2 ν) (θ : ℕ → Lp ℂ 2 νdual) (transpose : Lp ℂ 2 νdual →L[ℂ] Lp ℂ 2 νdual)
    (N : ℕ) (p : G × G) : ℂ :=
  ∑ m ∈ Finset.range (N + 1), (transpose (θ m) p.2 / (f p.2 : ℂ)) * φ m p.1

/-- Paper: (12.1.1.6), p. 499. The zeroth partial kernel consists of the
first basis term with its reciprocal weight in the source variable. -/
theorem schauderKernelPartialSum_zero {ν νdual : Measure G} (f : G → ℝ≥0)
    (φ : ℕ → Lp ℂ 2 ν) (θ : ℕ → Lp ℂ 2 νdual) (transpose : Lp ℂ 2 νdual →L[ℂ] Lp ℂ 2 νdual)
    (x y : G) :
    schauderKernelPartialSum f φ θ transpose 0 (x, y) =
      (transpose (θ 0) y / (f y : ℂ)) * φ 0 x := by
  simp [schauderKernelPartialSum]

end Basis

section SchauderApproximation

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  {μ ν : Measure G} [μ.IsHaarMeasure] [IsFiniteMeasureOnCompacts ν] [ν.InnerRegular]
  {U : ℕ → Set G} {f : G → ℝ≥0} {k : Lp ℂ 2 (ν.prod ν)}
  {κ : G × G → ℂ} (hκ : κ =ᵐ[ν.prod ν] k)
  (hU : IsDPrimeSequence μ U) (hBorel : ∀ n, MeasurableSet (U n))
  (hf : Continuous f) (hf_pos : ∀ x, 0 < f x) (hν : ν = μ.withDensity (fun x ↦ ↑(f x)))
  (hT : IsNuclearOperator (integralKernelOperator ν k).val)

variable {νdual : Measure G} (hνdual : νdual = μ.withDensity (fun x ↦ ↑((f x)⁻¹)))
  (b : _root_.SchauderBasis ℂ (Lp ℂ 2 ν)) (θ : ℕ → Lp ℂ 2 νdual)
  (transpose : Lp ℂ 2 νdual →L[ℂ] Lp ℂ 2 νdual)
  (hsimple : ∃ C : ℝ, ∀ N, ‖b.proj (N + 1)‖ ≤ C)
  (hnormalized : RiemannMasullo.SchauderBasis.IsNormalized (fun n ↦ b n))
  (hθ : ∀ (m : ℕ) (u : Lp ℂ 2 ν),
    weightedL2Duality μ hf.measurable hf_pos hν hνdual u (θ m) = b.coord m u)
  (htranspose : ∀ (u : Lp ℂ 2 ν) (v : Lp ℂ 2 νdual),
    weightedL2Duality μ hf.measurable hf_pos hν hνdual ((integralKernelOperator ν k).val u) v =
    weightedL2Duality μ hf.measurable hf_pos hν hνdual u (transpose v))

include hU hBorel hf hf_pos hν hT hκ hνdual hsimple hnormalized hθ htranspose

/-- Paper: Theorem 12.1.1.2(4), p. 499. The partial kernels constructed
from the simple, normalized Schauder basis converge in weighted product L².
The product smoothenings represent the same L² classes and limit.
Deviation: Simplicity is stated as uniform operator-norm boundedness of the
partial projections, equivalent to strong boundedness here. -/
theorem tendsto_schauderKernelPartialSum_L2 :
    let ks := schauderKernelPartialSum f (fun n ↦ b n) θ transpose
    ∃ hk : ∀ N, MemLp (ks N) 2 (ν.prod ν),
      Tendsto (fun N ↦ (hk N).toLp (ks N)) atTop (𝓝 k) ∧
        (∀ N, dSequenceKernelSmoothening μ U (ks N) =ᵐ[ν.prod ν] ks N) ∧
        dSequenceKernelSmoothening μ U κ =ᵐ[ν.prod ν] (k : G × G → ℂ) := by
  intro ks
  choose W hWae hW using fun m ↦
    weightedL2Duality_equiv_rep μ hf.measurable hf_pos hν hνdual (transpose (θ m))
  choose Km hKm _ using fun m ↦ L2.exists_outerProduct (b m) (W m)
  have hνac : ν ≪ μ := hν ▸ withDensity_absolutelyContinuous _ _
  have hKm_term (m : ℕ) :
      (Km m : G × G → ℂ) =ᵐ[ν.prod ν] fun p ↦ (transpose (θ m) p.2 / (f p.2 : ℂ)) * b m p.1 := by
    filter_upwards [hKm m, Measure.quasiMeasurePreserving_snd.ae (hνac.ae_le (hWae m))] with p hp hWp
    rw [hp, RCLike.inner_apply, hWp, map_div₀, Complex.conj_conj, Complex.conj_ofReal, mul_comm]
  let KS (N : ℕ) : Lp ℂ 2 (ν.prod ν) := ∑ m ∈ Finset.range (N + 1), Km m
  have hKS_ae (N : ℕ) : (KS N : G × G → ℂ) =ᵐ[ν.prod ν] ks N := by
    have hsum : ∀ n : ℕ, ((∑ m ∈ Finset.range n, Km m : Lp ℂ 2 (ν.prod ν)) : G × G → ℂ) =ᵐ[ν.prod ν]
        fun p ↦ ∑ m ∈ Finset.range n, (transpose (θ m) p.2 / (f p.2 : ℂ)) * b m p.1 := by
      intro n
      induction n with
      | zero =>
        simp only [Finset.range_zero, Finset.sum_empty]
        exact (Lp.coeFn_zero ℂ 2 (ν.prod ν)).trans (Eventually.of_forall fun _ ↦ rfl)
      | succ n ih =>
        rw [Finset.sum_range_succ]
        filter_upwards [Lp.coeFn_add (∑ m ∈ Finset.range n, Km m) (Km n), ih, hKm_term n]
          with p hadd hprev hlast
        rw [hadd, Pi.add_apply, hprev, hlast, Finset.sum_range_succ]
    exact hsum (N + 1)
  have hk (N : ℕ) : MemLp (ks N) 2 (ν.prod ν) := (Lp.memLp (KS N)).ae_eq (hKS_ae N)
  have htoLp (N : ℕ) : (hk N).toLp (ks N) = KS N :=
    Lp.ext ((hk N).coeFn_toLp.trans (hKS_ae N).symm)
  have hKm_op (m : ℕ) (u : Lp ℂ 2 ν) :
      (integralKernelOperator ν (Km m)).val u =
        b.coord m ((integralKernelOperator ν k).val u) • b m := by
    apply Lp.ext
    have hcoord : inner ℂ (W m) u = b.coord m ((integralKernelOperator ν k).val u) := by
      rw [← (hW m u).2]
      exact (htranspose u (θ m)).symm.trans (hθ m _)
    filter_upwards [integralKernelOperator_apply ν (Km m) u, Measure.ae_ae_of_ae_prod (hKm m),
      Lp.coeFn_smul (b.coord m ((integralKernelOperator ν k).val u)) (b m)] with x hx hxy hsmul
    have hrow : (fun y ↦ Km m (x, y) * u y) =ᵐ[ν] fun y ↦ b m x * inner ℂ (W m y) (u y) := by
      filter_upwards [hxy] with y hy
      rw [hy, RCLike.inner_apply, RCLike.inner_apply]
      ring
    rw [hx.2, integral_congr_ae hrow, integral_const_mul, ← L2.inner_def, hcoord, hsmul,
      Pi.smul_apply, smul_eq_mul, mul_comm]
  let swap := Lp.compMeasurePreservingₗ (E := ℂ) (p := 2) ℂ Prod.swap
    (Measure.measurePreserving_swap (μ := ν) (ν := ν))
  let A := (hilbertSchmidtOperators_equiv_Lp_prod ν ν).choose.toLinearMap.comp swap
  have hKS_op (N : ℕ) :
      (integralKernelOperator ν (KS N)).val = (b.proj (N + 1)).comp (integralKernelOperator ν k).val := by
    ext1 u
    have hmap : integralKernelOperator ν (KS N) =
        ∑ m ∈ Finset.range (N + 1), integralKernelOperator ν (Km m) :=
      map_sum A Km (Finset.range (N + 1))
    rw [hmap, Submodule.coe_sum]
    simp only [FunLike.coe_sum, Finset.sum_apply, hKm_op,
      ContinuousLinearMap.comp_apply, _root_.SchauderBasis.proj_apply]
  obtain ⟨hj, hlim, hconv⟩ := tendsto_schattenNorm_comp_left
    (integralKernelOperator ν k) (fun N ↦ b.proj (N + 1)) (ContinuousLinearMap.id ℂ (Lp ℂ 2 ν))
    (fun y ↦ (b.tendsto_proj y).comp (tendsto_add_atTop_nat 1))
  have hKS_tendsto : Tendsto KS atTop (𝓝 k) := by
    refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
    refine hconv.congr fun N ↦ ?_
    have h1 : (⟨(b.proj (N + 1)).comp (integralKernelOperator ν k).val, hj N⟩ :
        hilbertSchmidtOperators (Lp ℂ 2 ν) (Lp ℂ 2 ν)) = integralKernelOperator ν (KS N) :=
      Subtype.ext (hKS_op N).symm
    have h2 : (⟨(ContinuousLinearMap.id ℂ (Lp ℂ 2 ν)).comp (integralKernelOperator ν k).val, hlim⟩ :
        hilbertSchmidtOperators (Lp ℂ 2 ν) (Lp ℂ 2 ν)) = integralKernelOperator ν k :=
      Subtype.ext (ContinuousLinearMap.id_comp _)
    have hsub : integralKernelOperator ν (KS N - k) =
        integralKernelOperator ν (KS N) - integralKernelOperator ν k :=
      map_sub A (KS N) k
    rw [h1, h2, ← hsub]
    exact schattenNorm_integralKernelOperator ν (KS N - k)
  refine ⟨hk, by simpa only [htoLp] using hKS_tendsto, fun N ↦ ?_,
    dSequenceKernelSmoothening_ae_eq hκ hU hBorel hf hf_pos hν hT⟩
  have hhaarN := locallyIntegrable_of_weighted_memLp_prod (hk N).coeFn_toLp.symm hf hf_pos hν
  exact (hνac.prod hνac).ae_le (dSequenceKernelSmoothening_ae_eq_haar hU hhaarN)

/-- Paper: Theorem 12.1.1.2(4), p. 499. The diagonals of the smoothened
partial kernels from the Schauder basis converge weakly in weighted L¹. -/
theorem tendsto_schauderKernelPartialSum_diagonal_weak :
    let ks := schauderKernelPartialSum f (fun n ↦ b n) θ transpose
    let ds := fun N x ↦ dSequenceKernelSmoothening μ U (ks N) (x, x)
    let d := fun x ↦ dSequenceKernelSmoothening μ U κ (x, x)
    (∀ N, Integrable (ds N) ν) ∧ Integrable d ν ∧
      ∀ ρ : Lp ℂ ∞ ν, Tendsto (fun N ↦ ∫ x, ρ x * ds N x ∂ν) atTop
        (𝓝 (∫ x, ρ x * d x ∂ν)) := by sorry

end SchauderApproximation

end RiemannMasullo
