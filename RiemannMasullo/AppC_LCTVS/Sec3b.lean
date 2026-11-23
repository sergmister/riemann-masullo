module

public import RiemannMasullo.AppC_LCTVS.Sec3a_part2
import RiemannMasullo.ForMathlib.Analysis.Normed.Lp.lpSpace
import RiemannMasullo.ForMathlib.MeasureTheory.Function.L2Space
import RiemannMasullo.ForMathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Integral kernels

Masullo, Appendix C, §C.3.7, pp. 707–708.
-/

@[expose] public noncomputable section

open Filter MeasureTheory TopologicalSpace
open scoped ComplexConjugate ENNReal InnerProductSpace Topology

namespace RiemannMasullo

variable {X : Type*}
  [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ] [Measure.InnerRegular μ]

-- TODO(paper-gap): The diagonal need not be product-null as asserted on p. 707.
-- For a one-point space with unit point mass, the diagonal has product measure one.

/-- Paper: (C.3.7.1), p. 708. A square-integrable kernel defines a Hilbert-Schmidt
endomorphism of L².
Deviation: The kernel is an L² class. The correspondence from (C.3.6.5)–(C.3.6.6)
uses source-first coordinates, so the operator is obtained by swapping the coordinates. -/
def integralKernelOperator (k : Lp ℂ 2 (μ.prod μ)) :
    hilbertSchmidtOperators (Lp ℂ 2 μ) (Lp ℂ 2 μ) :=
  (hilbertSchmidtOperators_equiv_Lp_prod μ μ).choose
    (Lp.compMeasurePreserving Prod.swap (Measure.measurePreserving_swap (μ := μ) (ν := μ)) k)

/-- Paper: (C.3.7.1), p. 708. The operator acts by integrating the product of the
kernel and the input function in the source variable.
Deviation: The integral is required to be defined and to give the operator value
almost everywhere in the target variable. -/
theorem integralKernelOperator_apply (k : Lp ℂ 2 (μ.prod μ)) (f : Lp ℂ 2 μ) :
    ∀ᵐ x ∂μ, Integrable (fun y ↦ k (x, y) * f y) μ ∧
      (integralKernelOperator μ k).val f x = ∫ y, k (x, y) * f y ∂μ := by
  let hswap := Measure.measurePreserving_swap (μ := μ) (ν := μ)
  let swapped := Lp.compMeasurePreserving Prod.swap hswap k
  have hkernel : ∀ᵐ p ∂(μ.prod μ), swapped p.swap = k p :=
    hswap.quasiMeasurePreserving.ae (Lp.coeFn_compMeasurePreserving k hswap)
  filter_upwards [Measure.ae_ae_of_ae_prod hkernel,
    (hilbertSchmidtOperators_equiv_Lp_prod μ μ).choose_spec.2 swapped f] with x hx happly
  have hmul : (fun y ↦ swapped (y, x) * f y) =ᵐ[μ] fun y ↦ k (x, y) * f y := by
    filter_upwards [hx] with y hy
    exact congrArg (· * f y) hy
  exact ⟨happly.1.congr hmul, happly.2.trans (integral_congr_ae hmul)⟩

/-- Paper: Theorem C.3.7.1(1), p. 708. The Hilbert-Schmidt norm of the integral
operator is the L² norm of the kernel. -/
theorem schattenNorm_integralKernelOperator (k : Lp ℂ 2 (μ.prod μ)) :
    schattenNorm (integralKernelOperator μ k) = ‖k‖ := by
  unfold integralKernelOperator
  rw [(hilbertSchmidtOperators_equiv_Lp_prod μ μ).choose_spec.1]
  exact Lp.norm_compMeasurePreserving k (Measure.measurePreserving_swap (μ := μ) (ν := μ))

/-- The kernel correspondence is continuous in operator norm. -/
private theorem norm_integralKernelOperator_le (k : Lp ℂ 2 (μ.prod μ)) :
    ‖(integralKernelOperator μ k).val‖ ≤ ‖k‖ := by
  let A := integralKernelOperator μ k
  have hA : IsCompactOperator A.val ∧ Summable (fun n ↦ approximationNumber A.val n ^ (2 : ℝ)) :=
    A.property
  have hbound := hA.2.le_tsum 0 (fun n _ ↦ by rw [Real.rpow_two]; positivity)
  rw [approximationNumber_zero_eq_opNorm A.val hA.1, Real.rpow_two] at hbound
  rw [← schattenNorm_integralKernelOperator μ k]
  change ‖A.val‖ ≤ (∑' n, approximationNumber A.val n ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_sq (norm_nonneg A.val)]
  exact Real.sqrt_le_sqrt hbound

/-- The integral operator of an outer-product kernel is the corresponding rank-one map. -/
private theorem integralKernelOperator_outerProduct {K : Lp ℂ 2 (μ.prod μ)}
    {u v : Lp ℂ 2 μ} (hK : (K : X × X → ℂ) =ᵐ[μ.prod μ]
      fun p ↦ ⟪v p.2, u p.1⟫_ℂ) :
    (integralKernelOperator μ K).val = (innerSL ℂ v).smulRight u := by
  ext f : 1
  apply Lp.ext
  filter_upwards [integralKernelOperator_apply μ K f, Measure.ae_ae_of_ae_prod hK,
    Lp.coeFn_smul ⟪v, f⟫_ℂ u] with x hx hxy hsmul
  have h : (fun y ↦ K (x, y) * f y) =ᵐ[μ] fun y ↦ u x * ⟪v y, f y⟫_ℂ := by
    filter_upwards [hxy] with y hy
    rw [show K (x, y) = ⟪v y, u x⟫_ℂ from hy, RCLike.inner_apply, RCLike.inner_apply]
    ring
  change (integralKernelOperator μ K).val f x = (⟪v, f⟫_ℂ • u : Lp ℂ 2 μ) x
  rw [hx.2, integral_congr_ae h, integral_const_mul, hsmul]
  change u x * (∫ y, ⟪v y, f y⟫_ℂ ∂μ) = ⟪v, f⟫_ℂ * u x
  rw [L2.inner_def, mul_comm]

/-- Divide the summable coefficients of a nuclear presentation between its vectors and
Riesz representatives, giving two square-summable families. -/
private theorem NuclearPresentation.exists_squareSummable {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {T : H →L[ℂ] H} (r : NuclearPresentation T) :
    ∃ u v : ℕ → H, (Summable fun n ↦ ‖u n‖ ^ 2) ∧ (Summable fun n ↦ ‖v n‖ ^ 2) ∧
      ∀ f, HasSum (fun n ↦ ⟪v n, f⟫_ℂ • u n) (T f) := by
  obtain ⟨C, hC, hφ⟩ :=
    ((NormedSpace.equicontinuous_tfae r.functional).out 1 7).mp r.equicontinuous
  obtain ⟨D, hD⟩ := ((NormedSpace.isVonNBounded_iff ℂ).mp r.isBanachDisc.bounded).exists_norm_le
  let d (n : ℕ) : ℝ := Real.sqrt ‖r.coeff n‖
  let c (n : ℕ) : ℂ := r.coeff n / (d n : ℂ)
  have hd (n : ℕ) : ‖(d n : ℂ)‖ = d n := by simp [d, Real.sqrt_nonneg]
  have hdsq (n : ℕ) : d n ^ 2 = ‖r.coeff n‖ := Real.sq_sqrt (norm_nonneg _)
  have hcoeff (n : ℕ) : c n * (d n : ℂ) = r.coeff n := by
    by_cases hr : r.coeff n = 0
    · simp [c, hr]
    · exact div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr
        (Real.sqrt_pos.2 (norm_pos_iff.mpr hr)).ne')
  have hc (n : ℕ) : ‖c n‖ = d n := by
    rw [show ‖c n‖ = ‖r.coeff n‖ / d n from (norm_div _ _).trans (by rw [hd]), ← hdsq]
    by_cases hn : d n = 0
    · simp [hn]
    · rw [pow_two, mul_div_cancel_right₀ _ hn]
  let u (n : ℕ) : H := c n • (r.vector n : H)
  let v (n : ℕ) : H := (d n : ℂ) • (InnerProductSpace.toDual ℂ H).symm (r.functional n)
  have hvinner (n : ℕ) (f : H) : ⟪v n, f⟫_ℂ = (d n : ℂ) * r.functional n f := by
    rw [show v n = (d n : ℂ) • (InnerProductSpace.toDual ℂ H).symm (r.functional n) from rfl,
      inner_smul_left, InnerProductSpace.toDual_symm_apply]
    have hreal : (starRingEnd ℂ) (d n : ℂ) = (d n : ℂ) := by
      apply Complex.ext <;> simp
    rw [hreal]
  refine ⟨u, v, ?_, ?_, ?_⟩
  · apply (r.summable_coeff.mul_left (D ^ 2)).of_nonneg_of_le (fun _ ↦ sq_nonneg _)
    intro n
    rw [show ‖u n‖ = d n * ‖(r.vector n : H)‖ by rw [norm_smul, hc], mul_pow, hdsq, mul_comm]
    gcongr
    exact hD _ (r.vector_mem n)
  · apply (r.summable_coeff.mul_left (C ^ 2)).of_nonneg_of_le (fun _ ↦ sq_nonneg _)
    intro n
    rw [show ‖v n‖ = d n * ‖r.functional n‖ by
      rw [norm_smul, hd, LinearIsometryEquiv.norm_map], mul_pow, hdsq, mul_comm]
    gcongr
    exact hφ n
  · intro f
    refine (r.hasSum f).congr_fun fun n ↦ ?_
    rw [hvinner, show u n = c n • (r.vector n : H) from rfl, smul_smul,
      mul_right_comm, mul_comm (↑(d n) : ℂ) (c n), hcoeff]

/-- The trace of a square-summable rank-one expansion is the sum of the pairings
of its vectors. Absolute convergence permits exchanging the two sums. -/
private theorem hilbertTrace_eq_tsum_inner_of_rankOne_series {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (T : nuclearEndomorphisms H)
    {u v : ℕ → H} (hu : Summable fun n ↦ ‖u n‖ ^ 2) (hv : Summable fun n ↦ ‖v n‖ ^ 2)
    (hT : ∀ f, HasSum (fun n ↦ ⟪v n, f⟫_ℂ • u n) (T.val f)) :
    hilbertTrace T = ∑' n, ⟪v n, u n⟫_ℂ := by
  let b := (exists_hilbertBasis (𝕜 := ℂ) (E := H)).choose_spec.choose
  let d (n : ℕ) i := ⟪v n, b i⟫_ℂ * ⟪b i, u n⟫_ℂ
  have hrow (n : ℕ) : HasSum (d n) ⟪v n, u n⟫_ℂ := by
    have h := (innerSL ℂ (v n)).hasSum (b.hasSum_repr (u n))
    simp only [map_smul, smul_eq_mul, b.repr_apply_apply, innerSL_apply_apply] at h
    exact h.congr_fun fun i ↦ mul_comm _ _
  have hcol (i : _) : HasSum (fun n ↦ d n i) ⟪b i, T.val (b i)⟫_ℂ := by
    simpa only [d, innerSL_apply_apply, inner_smul_right] using (innerSL ℂ (b i)).hasSum (hT (b i))
  have hholder : (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal := by
    rw [ENNReal.toReal_ofNat, Real.holderConjugate_iff]
    norm_num
  have hnorm (n : ℕ) : (Summable fun i ↦ ‖d n i‖) ∧ ∑' i, ‖d n i‖ ≤ ‖v n‖ * ‖u n‖ := by
    simpa only [d, norm_mul, norm_inner_symm (v n), ← b.repr_apply_apply,
      LinearIsometryEquiv.norm_map] using lp.tsum_mul_le_mul_norm hholder (b.repr (v n)) (b.repr (u n))
  have habs : Summable fun p : ℕ × _ ↦ ‖d p.1 p.2‖ := by
    apply (summable_prod_of_nonneg (fun _ ↦ norm_nonneg _)).2
    refine ⟨fun n ↦ (hnorm n).1, ((hu.add hv).div_const 2).of_nonneg_of_le
      (fun n ↦ tsum_nonneg fun i ↦ norm_nonneg (d n i)) fun n ↦ (hnorm n).2.trans ?_⟩
    exact (le_div_iff₀ (by norm_num)).2 (by
      linarith only [two_mul_le_add_sq ‖v n‖ ‖u n‖])
  change (∑' i, ⟪b i, T.val (b i)⟫_ℂ) = _
  calc
    _ = ∑' i, ∑' n, d n i := tsum_congr fun i ↦ (hcol i).tsum_eq.symm
    _ = ∑' n, ∑' i, d n i := habs.of_norm.tsum_comm
    _ = _ := tsum_congr fun n ↦ (hrow n).tsum_eq

/-- A square-summable rank-one expansion represents the original kernel almost everywhere
by pairing the two families of coordinates in ℓ². -/
private theorem ae_eq_inner_of_rankOne_series {K : Lp ℂ 2 (μ.prod μ)}
    {u v : ℕ → Lp ℂ 2 μ} (hu : Summable fun n ↦ ‖u n‖ ^ 2)
    (hv : Summable fun n ↦ ‖v n‖ ^ 2)
    (hT : ∀ f, HasSum (fun n ↦ ⟪v n, f⟫_ℂ • u n) ((integralKernelOperator μ K).val f))
    {a b : X → lp (fun _ : ℕ ↦ ℂ) 2} (ha : ∀ᵐ x ∂μ, ∀ n, a x n = u n x)
    (hb : ∀ᵐ x ∂μ, ∀ n, b x n = v n x) :
    (K : X × X → ℂ) =ᵐ[μ.prod μ] fun p ↦ ⟪b p.2, a p.1⟫_ℂ := by
  let swap : Lp ℂ 2 (μ.prod μ) →ₗᵢ[ℂ] Lp ℂ 2 (μ.prod μ) :=
    Lp.compMeasurePreservingₗᵢ ℂ Prod.swap Measure.measurePreserving_swap
  let e := (hilbertSchmidtOperators_equiv_Lp_prod μ μ).choose
  let L := (hilbertSchmidtOperators (Lp ℂ 2 μ) (Lp ℂ 2 μ)).subtype.comp
    (e.toLinearMap.comp swap.toLinearMap)
  let A := L.mkContinuous 1 (by
    intro k
    change ‖(integralKernelOperator μ k).val‖ ≤ 1 * ‖k‖
    rw [one_mul]
    exact norm_integralKernelOperator_le μ k)
  have hinj : Function.Injective A :=
    Subtype.val_injective.comp (e.injective.comp swap.injective)
  choose Kn hKn hnorm using fun n ↦ L2.exists_outerProduct (u n) (v n)
  have hsum : Summable fun n ↦ ‖Kn n‖ := by
    apply ((hu.add hv).div_const 2).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    intro n
    rw [hnorm]
    exact (le_div_iff₀ (by norm_num)).2 (by
      linarith only [two_mul_le_add_sq ‖u n‖ ‖v n‖])
  have hKnT : ∀ f, A (∑' n, Kn n) f = A K f := by
    intro f
    have hs := (ContinuousLinearMap.apply ℂ _ f).hasSum
      (A.hasSum hsum.of_norm.hasSum)
    have hterm (n : ℕ) : A (Kn n) f = ⟪v n, f⟫_ℂ • u n :=
      DFunLike.congr_fun (integralKernelOperator_outerProduct μ (hKn n)) f
    exact (hs.congr_fun fun n ↦ (hterm n).symm).unique (hT f)
  have heq : (∑' n, Kn n) = K := hinj (ContinuousLinearMap.ext hKnT)
  have hsumAE := Lp.hasSum_coeFn_tsum (tsum_eNorm_ne_top_iff_summable_norm.mpr hsum)
  rw [heq] at hsumAE
  filter_upwards [hsumAE, ae_all_iff.2 hKn, Measure.quasiMeasurePreserving_fst.ae ha,
    Measure.quasiMeasurePreserving_snd.ae hb] with p hp hterms hpa hpb
  refine hp.unique ((lp.hasSum_inner (b p.2) (a p.1)).congr_fun fun n ↦ ?_)
  rw [hterms n, hpa n, hpb n]

/-- Paper: Theorem C.3.7.1(2)(a), p. 708. If a square-integrable kernel is jointly
continuous at almost every diagonal point and its operator is nuclear, the diagonal
is integrable and its integral is the trace.
Deviation: The continuity and diagonal evaluation use a specified representative
of the L² kernel class. -/
theorem hilbertTrace_integralKernelOperator_of_ae_continuous {k : X × X → ℂ}
    (hk : MemLp k 2 (μ.prod μ))
    (hT : IsNuclearOperator (integralKernelOperator μ (hk.toLp k)).val)
    (hcont : ∀ᵐ x ∂μ, ContinuousAt k (x, x)) :
    Integrable (fun x ↦ k (x, x)) μ ∧
      hilbertTrace ⟨(integralKernelOperator μ (hk.toLp k)).val, hT⟩ =
        ∫ x, k (x, x) ∂μ := by
  let T := (integralKernelOperator μ (hk.toLp k)).val
  obtain ⟨r⟩ := (isNuclearOperator_iff_nonempty_presentation T).mp hT
  obtain ⟨u, v, hu, hv, hseries⟩ := r.exists_squareSummable
  obtain ⟨a, ha, ha'⟩ := L2.exists_memLp_coordinates u hu
  obtain ⟨b, hb, hb'⟩ := L2.exists_memLp_coordinates v hv
  let : SeparableSpace (lp (fun _ : ℕ ↦ ℂ) 2) := lp.separableSpace (by simp)
  let : MeasurableSpace (lp (fun _ : ℕ ↦ ℂ) 2) := borel _
  have : BorelSpace (lp (fun _ : ℕ ↦ ℂ) 2) := ⟨rfl⟩
  have hkernel := hk.coeFn_toLp.symm.trans (ae_eq_inner_of_rankOne_series μ hu hv hseries ha' hb')
  have hdiag := ae_diagonal_eq_of_ae_eq_comp_prod ha.aestronglyMeasurable.aemeasurable
    hb.aestronglyMeasurable.aemeasurable (continuous_snd.inner continuous_fst) hkernel hcont
  have hinner : Integrable (fun x ↦ ⟪b x, a x⟫_ℂ) μ := by
    apply (L2.integrable_inner (𝕜 := ℂ) (hb.toLp b) (ha.toLp a)).congr
    filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with x hx hy
    rw [hx, hy]
  refine ⟨hinner.congr hdiag.symm, ?_⟩
  rw [integral_congr_ae hdiag, hilbertTrace_eq_tsum_inner_of_rankOne_series _ hu hv hseries]
  have hInt (n : ℕ) : Integrable (fun x ↦ ⟪v n x, u n x⟫_ℂ) μ := L2.integrable_inner _ _
  have hNormSum : Summable fun n ↦ ∫ x, ‖⟪v n x, u n x⟫_ℂ‖ ∂μ := by
    have hbound : Summable fun n ↦ (‖u n‖ ^ 2 + ‖v n‖ ^ 2) / 2 := (hu.add hv).div_const 2
    apply hbound.of_nonneg_of_le (fun n ↦ integral_nonneg fun _ ↦ norm_nonneg _)
    intro n
    rw [← L2.integral_sq_norm (𝕜 := ℂ) (u n), ← L2.integral_sq_norm (𝕜 := ℂ) (v n),
      ← integral_add ((Lp.memLp (u n)).integrable_norm_pow (by decide : 2 ≠ 0))
        ((Lp.memLp (v n)).integrable_norm_pow (by decide : 2 ≠ 0)),
      ← integral_div]
    apply integral_mono (hInt n).norm
      ((((Lp.memLp (u n)).integrable_norm_pow (by decide : 2 ≠ 0)).add
        ((Lp.memLp (v n)).integrable_norm_pow (by decide : 2 ≠ 0))).div_const _)
    intro x
    apply (norm_inner_le_norm _ _).trans
    change ‖v n x‖ * ‖u n x‖ ≤ (‖u n x‖ ^ 2 + ‖v n x‖ ^ 2) / 2
    nlinarith [sq_nonneg (‖u n x‖ - ‖v n x‖)]
  have hsum := hasSum_integral_of_summable_integral_norm hInt hNormSum
  have hsumDiag : (fun x ↦ ∑' n, ⟪v n x, u n x⟫_ℂ) =ᵐ[μ] fun x ↦ ⟪b x, a x⟫_ℂ := by
    filter_upwards [ha', hb'] with x hx hy
    simpa only [hx, hy] using (lp.hasSum_inner (b x) (a x)).tsum_eq
  rw [integral_congr_ae hsumDiag] at hsum
  simpa only [L2.inner_def] using hsum.tsum_eq

omit [T2Space X] [BorelSpace X] [Measure.InnerRegular μ] in
/-- The rows of a square-integrable kernel are square-integrable almost everywhere. -/
private theorem ae_memLp_integralKernel_row (a : Lp ℂ 2 (μ.prod μ)) :
    ∀ᵐ x ∂μ, MemLp (fun z ↦ a (x, z)) 2 μ := by
  have h := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable a)).mp (Lp.memLp a)
  filter_upwards [h.prod_right_ae] with x hx
  exact (memLp_two_iff_integrable_sq_norm
    ((Lp.stronglyMeasurable a).comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable).mpr hx

omit [T2Space X] [BorelSpace X] [Measure.InnerRegular μ] in
/-- The columns of a square-integrable kernel are square-integrable almost everywhere. -/
private theorem ae_memLp_integralKernel_column (b : Lp ℂ 2 (μ.prod μ)) :
    ∀ᵐ y ∂μ, MemLp (fun z ↦ b (z, y)) 2 μ := by
  have h := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable b)).mp (Lp.memLp b)
  filter_upwards [h.prod_left_ae] with y hy
  exact (memLp_two_iff_integrable_sq_norm
    ((Lp.stronglyMeasurable b).comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable).mpr hy

/-- The kernel-to-operator correspondence in target-first coordinates is bijective. -/
theorem bijective_integralKernelOperator : Function.Bijective (integralKernelOperator μ) := by
  let hswap := Measure.measurePreserving_swap (μ := μ) (ν := μ)
  let swap := Lp.compMeasurePreserving (E := ℂ) (p := 2) Prod.swap hswap
  have hswap_inv : Function.Involutive swap := by
    intro a
    apply Lp.ext
    filter_upwards [Lp.coeFn_compMeasurePreserving (swap a) hswap,
      hswap.quasiMeasurePreserving.ae (Lp.coeFn_compMeasurePreserving a hswap)] with p h₁ h₂
    exact h₁.trans h₂
  exact (hilbertSchmidtOperators_equiv_Lp_prod μ μ).choose.bijective.comp hswap_inv.bijective

omit [T2Space X] [BorelSpace X] [Measure.InnerRegular μ] in
/-- Integrating a product of two square-integrable kernels over their shared variable
gives a square-integrable kernel, and the section products are integrable almost everywhere. -/
private theorem memLp_integralKernel_convolution (a b : Lp ℂ 2 (μ.prod μ)) :
    MemLp (fun p : X × X ↦ ∫ z, a (p.1, z) * b (z, p.2) ∂μ) 2 (μ.prod μ) ∧
      ∀ᵐ p ∂(μ.prod μ), Integrable (fun z ↦ a (p.1, z) * b (z, p.2)) μ := by
  have hrows := (Measure.quasiMeasurePreserving_fst (ν := μ)).ae
    (ae_memLp_integralKernel_row μ a)
  have hcols := (Measure.quasiMeasurePreserving_snd (μ := μ)).ae
    (ae_memLp_integralKernel_column μ b)
  have hmeas : StronglyMeasurable
      (fun q : (X × X) × X ↦ a (q.1.1, q.2) * b (q.2, q.1.2)) :=
    ((Lp.stronglyMeasurable a).comp_measurable
      (measurable_fst.fst.prodMk measurable_snd)).mul
      ((Lp.stronglyMeasurable b).comp_measurable
        (measurable_snd.prodMk measurable_fst.snd))
  let rowEnergy (x : X) := ∫ z, ‖a (x, z)‖ ^ 2 ∂μ
  let colEnergy (y : X) := ∫ z, ‖b (z, y)‖ ^ 2 ∂μ
  have ha : Integrable rowEnergy μ :=
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable a)).mp
      (Lp.memLp a)).integral_prod_left
  have hb : Integrable colEnergy μ :=
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable b)).mp
      (Lp.memLp b)).integral_prod_right
  refine ⟨(memLp_two_iff_integrable_sq_norm
    hmeas.integral_prod_right'.aestronglyMeasurable).mpr ?_, ?_⟩
  · refine (ha.mul_prod hb).mono' (hmeas.integral_prod_right'.norm.pow 2).aestronglyMeasurable ?_
    filter_upwards [hrows, hcols] with p hp hq
    have hle : ‖∫ z, a (p.1, z) * b (z, p.2) ∂μ‖ ≤
        Real.sqrt (rowEnergy p.1) * Real.sqrt (colEnergy p.2) := by
      calc
        _ ≤ ∫ z, ‖a (p.1, z) * b (z, p.2)‖ ∂μ := norm_integral_le_integral_norm _
        _ ≤ _ := by
          simpa [rowEnergy, colEnergy, norm_mul, Real.sqrt_eq_rpow] using
            integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
              (by simpa using hp) (by simpa using hq)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    calc
      _ ≤ (Real.sqrt (rowEnergy p.1) * Real.sqrt (colEnergy p.2)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hle 2
      _ = rowEnergy p.1 * colEnergy p.2 := by
        rw [mul_pow, Real.sq_sqrt (integral_nonneg fun _ ↦ sq_nonneg _),
          Real.sq_sqrt (integral_nonneg fun _ ↦ sq_nonneg _)]
  · filter_upwards [hrows, hcols] with p hp hq
    exact hp.integrable_mul hq

/-- The integral operator of a convolution of square-integrable kernels is the
composition of their integral operators. -/
private theorem integralKernelOperator_convolution (a b : Lp ℂ 2 (μ.prod μ))
    (hc : MemLp (fun p : X × X ↦ ∫ z, a (p.1, z) * b (z, p.2) ∂μ) 2 (μ.prod μ)) :
    (integralKernelOperator μ (hc.toLp _)).val =
      (integralKernelOperator μ a).val.comp (integralKernelOperator μ b).val := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  let g := (integralKernelOperator μ b).val f
  have hconv := Measure.ae_ae_of_ae_prod hc.coeFn_toLp
  filter_upwards [integralKernelOperator_apply μ (hc.toLp _) f,
    integralKernelOperator_apply μ a g, ae_memLp_integralKernel_row μ a, hconv] with x hx ha hrow hxy
  let integrand (p : X × X) := a (x, p.1) * b p * f p.2
  have hrowSq := (memLp_two_iff_integrable_sq_norm hrow.aestronglyMeasurable).mp hrow
  have hfSq := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  have hbSq := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable b)).mp (Lp.memLp b)
  have hmeas : StronglyMeasurable integrand :=
    (((Lp.stronglyMeasurable a).comp_measurable (measurable_const.prodMk measurable_fst)).mul
      (Lp.stronglyMeasurable b)).mul ((Lp.stronglyMeasurable f).comp_measurable measurable_snd)
  have hint : Integrable integrand (μ.prod μ) := by
    refine (((hrowSq.mul_prod hfSq).add hbSq).const_mul (1 / 2 : ℝ)).mono'
      hmeas.aestronglyMeasurable ?_
    filter_upwards with p
    dsimp [integrand]
    simp only [norm_mul]
    nlinarith [sq_nonneg (‖a (x, p.1)‖ * ‖f p.2‖ - ‖b p‖)]
  calc
    _ = ∫ y, (hc.toLp _ : Lp ℂ 2 (μ.prod μ)) (x, y) * f y ∂μ := hx.2
    _ = ∫ y, ∫ z, integrand (z, y) ∂μ ∂μ := by
      apply integral_congr_ae
      filter_upwards [hxy] with y hy
      rw [hy, ← integral_mul_const]
    _ = ∫ z, ∫ y, integrand (z, y) ∂μ ∂μ :=
      (integral_prod_symm integrand hint).symm.trans (integral_prod integrand hint)
    _ = ∫ z, a (x, z) * g z ∂μ := by
      apply integral_congr_ae
      filter_upwards [integralKernelOperator_apply μ b f] with z hz
      rw [hz.2, ← integral_const_mul]
      simp only [integrand, mul_assoc]
    _ = _ := ha.2.symm

omit [T2Space X] [BorelSpace X] [Measure.InnerRegular μ] in
/-- The product of two square-integrable kernels with reversed arguments in the
second kernel is integrable on the product space. -/
private theorem integrable_integralKernel_mul_swap (a b : Lp ℂ 2 (μ.prod μ)) :
    Integrable (fun p : X × X ↦ a p * b p.swap) (μ.prod μ) := by
  have hb := (Lp.memLp b).comp_measurePreserving (Measure.measurePreserving_swap (μ := μ) (ν := μ))
  exact (Lp.memLp a).integrable_mul hb

/-- A nuclear endomorphism of a complex Hilbert space factors into two Hilbert-Schmidt
endomorphisms by taking a fourth root of its Gram operator. -/
theorem exists_hilbertSchmidt_factorization
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) (hT : IsNuclearOperator T) :
    ∃ A B : hilbertSchmidtOperators H H, T = A.val.comp B.val := by
  let S := CFC.sqrt (T.adjoint * T)
  let B := CFC.sqrt S
  have hS : S * S = T.adjoint * T :=
    CFC.sqrt_mul_sqrt_self _ (ContinuousLinearMap.nonneg_iff_isPositive.mpr
      T.isPositive_adjoint_comp_self)
  have hB : B * B = S := CFC.sqrt_mul_sqrt_self _ (CFC.sqrt_nonneg _)
  have hadjS : S.adjoint = S :=
    IsSelfAdjoint.star_eq (IsSelfAdjoint.of_nonneg (show 0 ≤ S from CFC.sqrt_nonneg _))
  have hadjB : B.adjoint = B :=
    IsSelfAdjoint.star_eq (IsSelfAdjoint.of_nonneg (show 0 ≤ B from CFC.sqrt_nonneg _))
  have hnorm (x : H) : ‖T x‖ ≤ ‖S x‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    have heq : ⟪T x, T x⟫_ℂ = ⟪S x, S x⟫_ℂ := calc
      _ = ⟪x, (T.adjoint * T) x⟫_ℂ := (ContinuousLinearMap.adjoint_inner_right T x (T x)).symm
      _ = ⟪x, (S * S) x⟫_ℂ := by rw [hS]
      _ = _ := by
        simpa only [hadjS, mul_apply_eq_comp] using
          ContinuousLinearMap.adjoint_inner_right S x (S x)
    exact le_of_eq (by simpa only [inner_self_eq_norm_sq] using congrArg (RCLike.re (K := ℂ)) heq)
  -- Extend the map S x ↦ T x to the closure of the range of S, then project onto it.
  obtain ⟨U, hU, hUS⟩ : ∃ U : H →L[ℂ] H, ‖U‖ ≤ 1 ∧ U * S = T := by
    let V := S.toLinearMap.range.topologicalClosure
    let i : H →ₗ[ℂ] V := S.toLinearMap.codRestrict V
      (fun x ↦ S.toLinearMap.range.le_topologicalClosure ⟨x, rfl⟩)
    have hi : DenseRange i := by
      have hincl : DenseRange (Set.inclusion S.toLinearMap.range.le_topologicalClosure) :=
        (denseRange_inclusion_iff _).2 subset_rfl
      exact hincl.comp (show Function.Surjective S.toLinearMap.rangeRestrict from
        fun ⟨x, y, hy⟩ ↦ ⟨y, Subtype.ext hy⟩).denseRange
        (continuous_inclusion _)
    let j := T.toLinearMap.extendOfNorm i
    have hbound (x : H) : ‖T.toLinearMap x‖ ≤ 1 * ‖i x‖ := by
      simpa [i] using hnorm x
    have hj : ‖j‖ ≤ 1 := LinearMap.opNorm_extendOfNorm_le hi zero_le_one hbound
    have hj_apply (x : H) : j (i x) = T x :=
      LinearMap.extendOfNorm_eq hi ⟨1, hbound⟩ x
    let U := j.comp V.orthogonalProjectionOnto
    refine ⟨U, (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_, ?_⟩
    · simpa only [mul_one] using
        mul_le_mul hj V.orthogonalProjectionOnto_norm_le
          (norm_nonneg V.orthogonalProjectionOnto) zero_le_one
    · ext x
      change j (V.orthogonalProjectionOnto (S x)) = T x
      exact (congrArg j (V.orthogonalProjectionOnto_mem_subspace_eq_self (i x))).trans (hj_apply x)
  obtain ⟨ι, b, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  have hb_sum : Summable (fun i ↦ ‖B (b i)‖ ^ 2) := by
    refine ((isNuclearOperator_iff_summable_traceNorm_diagonal b T).mp hT).congr fun i ↦ ?_
    change (⟪b i, S (b i)⟫_ℂ).re = _
    rw [← hB]
    have heq : ⟪b i, (B * B) (b i)⟫_ℂ = ⟪B (b i), B (b i)⟫_ℂ := by
      simpa only [hadjB, mul_apply_eq_comp] using
        ContinuousLinearMap.adjoint_inner_right B (b i) (B (b i))
    rw [heq]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) _
  have ha_sum : Summable (fun i ↦ ‖(U * B) (b i)‖ ^ 2) := by
    refine hb_sum.of_nonneg_of_le (fun _ ↦ sq_nonneg _) fun i ↦ ?_
    apply pow_le_pow_left₀ (norm_nonneg _) _ 2
    exact (U.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) hU)
  refine ⟨⟨U * B, (mem_hilbertSchmidtOperators_iff_summable_basis b _).mpr ha_sum⟩,
    ⟨B, (mem_hilbertSchmidtOperators_iff_summable_basis b _).mpr hb_sum⟩, ?_⟩
  change T = (U * B) * B
  rw [mul_assoc, hB, hUS]

/-- The adjoint integral operator has the conjugate kernel with its arguments reversed. -/
private theorem integralKernelOperator_adjoint (a : Lp ℂ 2 (μ.prod μ)) :
    ∃ c : Lp ℂ 2 (μ.prod μ), (c : X × X → ℂ) =ᵐ[μ.prod μ] (fun p ↦ conj (a p.swap)) ∧
      (integralKernelOperator μ c).val = (integralKernelOperator μ a).val.adjoint := by
  let swap := Measure.measurePreserving_swap (μ := μ) (ν := μ)
  have ha := (Lp.memLp a).comp_measurePreserving swap
  have hc : MemLp (fun p : X × X ↦ conj (a p.swap)) 2 (μ.prod μ) :=
    ha.congr_norm (Complex.continuous_conj.comp_aestronglyMeasurable
      ha.aestronglyMeasurable)
      (Eventually.of_forall fun p : X × X ↦ (Complex.norm_conj (a p.swap)).symm)
  let c := hc.toLp (fun p : X × X ↦ conj (a p.swap))
  refine ⟨c, hc.coeFn_toLp, ?_⟩
  apply ContinuousLinearMap.ext
  intro g
  apply ext_inner_right ℂ
  intro f
  -- Pair the two operators with arbitrary vectors and exchange the two integrations.
  rw [ContinuousLinearMap.adjoint_inner_left]
  simp only [L2.inner_def, RCLike.inner_apply]
  let F (p : X × X) := conj (g p.1) * (a p * f p.2)
  obtain ⟨K, hK, -⟩ := L2.exists_outerProduct f g
  have hF : Integrable F (μ.prod μ) := by
    refine ((Lp.memLp a).integrable_mul ((Lp.memLp K).comp_measurePreserving swap)).congr ?_
    filter_upwards [swap.quasiMeasurePreserving.ae hK] with p hp
    change a p * K p.swap = F p
    rw [hp, RCLike.inner_apply]
    dsimp [F]
    ring
  calc
    _ = ∫ y, ∫ x, F (x, y) ∂μ ∂μ := by
      apply integral_congr_ae
      filter_upwards [integralKernelOperator_apply μ c g,
        Measure.ae_ae_of_ae_prod hc.coeFn_toLp] with y hy hcy
      have hconj : conj (∫ x, c (y, x) * g x ∂μ) =
          ∫ x, conj (c (y, x) * g x) ∂μ :=
        (Complex.conjCLE.toContinuousLinearMap.integral_comp_comm hy.1).symm
      rw [hy.2, hconj, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [hcy] with x hx
      rw [hx, map_mul, Complex.conj_conj]
      dsimp [F]
      ring
    _ = ∫ x, ∫ y, F (x, y) ∂μ ∂μ :=
      (integral_prod_symm F hF).symm.trans (integral_prod F hF)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [integralKernelOperator_apply μ a f] with x hx
      rw [hx.2, mul_comm, ← integral_const_mul]

omit [T2Space X] [BorelSpace X] [Measure.InnerRegular μ] in
/-- The conjugate of almost every row gives an L² vector whose inner product with
an input vector computes the kernel integral. -/
private theorem ae_exists_integralKernel_row (a : Lp ℂ 2 (μ.prod μ)) :
    ∀ᵐ x ∂μ, ∃ u : Lp ℂ 2 μ, (u : X → ℂ) =ᵐ[μ] (fun y ↦ conj (a (x, y))) ∧
      ∀ f : Lp ℂ 2 μ, ⟪u, f⟫_ℂ = ∫ y, a (x, y) * f y ∂μ := by
  filter_upwards [ae_memLp_integralKernel_row μ a] with x hx
  have hu := hx.congr_norm (Complex.continuous_conj.comp_aestronglyMeasurable
    hx.aestronglyMeasurable) (Eventually.of_forall fun y ↦ (Complex.norm_conj (a (x, y))).symm)
  refine ⟨hu.toLp _, hu.coeFn_toLp, fun f ↦ ?_⟩
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hu.coeFn_toLp] with y hy
  rw [RCLike.inner_apply, hy, Complex.conj_conj, mul_comm]

/-- Paper: Theorem C.3.7.1(2)(b), p. 708. The trace of a nuclear composite of
two integral operators with square-integrable kernels is the product-space integral
of the first kernel times the second kernel with its variables reversed.
Deviation: The diagonal integral is written as a single product-space integral by Fubini. -/
theorem hilbertTrace_integralKernelOperator_comp (a b : Lp ℂ 2 (μ.prod μ))
    (h : IsNuclearOperator
      ((integralKernelOperator μ a).val.comp (integralKernelOperator μ b).val)) :
    hilbertTrace ⟨(integralKernelOperator μ a).val.comp (integralKernelOperator μ b).val, h⟩ =
      ∫ p : X × X, a p * b p.swap ∂(μ.prod μ) := by
  obtain ⟨c, hc, hadj⟩ := integralKernelOperator_adjoint μ a
  let B := (integralKernelOperator μ b).val
  let C := (integralKernelOperator μ c).val
  let e := (exists_hilbertBasis (𝕜 := ℂ) (E := Lp ℂ 2 μ)).choose_spec.choose
  -- Countability lets us apply the section formula simultaneously to every basis vector.
  let : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
  have : Countable (exists_hilbertBasis (𝕜 := ℂ) (E := Lp ℂ 2 μ)).choose := by
    refine Pairwise.countable_of_isOpen_disjoint (s := fun i ↦ Metric.ball (e i) (1 / 2))
      ?_ (fun _ ↦ Metric.isOpen_ball) (fun i ↦ ⟨e i, Metric.mem_ball_self (by norm_num)⟩)
    intro i j hij
    apply Metric.ball_disjoint_ball
    have hd : dist (e i) (e j) ^ 2 = 2 := by
      rw [dist_eq_norm, norm_sub_sq (𝕜 := ℂ), e.orthonormal.norm_eq_one i,
        e.orthonormal.norm_eq_one j, e.orthonormal.inner_eq_zero hij]
      norm_num
    nlinarith [dist_nonneg (x := e i) (y := e j)]
  have hB := (mem_hilbertSchmidtOperators_iff_summable_basis e B).mp
    (integralKernelOperator μ b).property
  have hC := (mem_hilbertSchmidtOperators_iff_summable_basis e C).mp
    (integralKernelOperator μ c).property
  let d i (x : X) := ⟪C (e i) x, B (e i) x⟫_ℂ
  have hInt (i : _) : Integrable (d i) μ := L2.integrable_inner _ _
  have hNorm : Summable fun i ↦ ∫ x, ‖d i x‖ ∂μ := by
    refine ((hB.add hC).div_const 2).of_nonneg_of_le
      (fun _ ↦ integral_nonneg fun _ ↦ norm_nonneg _) fun i ↦ ?_
    have hbound := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
      (by simpa using Lp.memLp (B (e i))) (by simpa using Lp.memLp (C (e i)))
    simp only [← Real.sqrt_eq_rpow, Real.rpow_two, L2.integral_sq_norm (𝕜 := ℂ),
      Real.sqrt_sq (norm_nonneg _)] at hbound
    simp only [d, RCLike.inner_apply, norm_mul, Complex.norm_conj]
    exact hbound.trans ((le_div_iff₀ (by norm_num)).2 (by
      linarith only [two_mul_le_add_sq ‖B (e i)‖ ‖C (e i)‖]))
  have hdiag : (fun x ↦ ∑' i, d i x) =ᵐ[μ] (fun x ↦ ∫ y, b (x, y) * a (y, x) ∂μ) := by
    filter_upwards [ae_exists_integralKernel_row μ b, ae_exists_integralKernel_row μ c,
      Measure.ae_ae_of_ae_prod hc,
      ae_all_iff.2 fun i ↦ integralKernelOperator_apply μ b (e i),
      ae_all_iff.2 fun i ↦ integralKernelOperator_apply μ c (e i)] with
      x hbx hcx hswap hBe hCe
    obtain ⟨u, hu, hu_inner⟩ := hbx
    obtain ⟨v, hv, hv_inner⟩ := hcx
    calc
      _ = ⟪u, v⟫_ℂ := by
        refine ((e.hasSum_inner_mul_inner u v).congr_fun fun i ↦ ?_).tsum_eq
        have hBi : B (e i) x = ⟪u, e i⟫_ℂ := (hBe i).2.trans (hu_inner (e i)).symm
        have hCi : C (e i) x = ⟪v, e i⟫_ℂ := (hCe i).2.trans (hv_inner (e i)).symm
        rw [show d i x = ⟪C (e i) x, B (e i) x⟫_ℂ from rfl, RCLike.inner_apply,
          hBi, hCi, inner_conj_symm]
      _ = _ := by
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [hu, hv, hswap] with y hyu hyv hcy
        rw [RCLike.inner_apply, hyu, hyv, hcy, Complex.conj_conj, Complex.conj_conj, mul_comm]
        rfl
  change (∑' i, ⟪e i, (integralKernelOperator μ a).val (B (e i))⟫_ℂ) = _
  calc
    _ = ∑' i, ⟪C (e i), B (e i)⟫_ℂ := tsum_congr fun i ↦ by
      rw [← ContinuousLinearMap.adjoint_inner_left, ← hadj]
    _ = ∫ x, ∑' i, d i x ∂μ := by
      simpa only [d, L2.inner_def] using (hasSum_integral_of_summable_integral_norm hInt hNorm).tsum_eq
    _ = ∫ p : X × X, b p * a p.swap ∂(μ.prod μ) :=
      (integral_congr_ae hdiag).trans (integral_prod _ (integrable_integralKernel_mul_swap μ b a)).symm
    _ = _ := by
      simpa only [Prod.swap_swap, mul_comm] using
        (integral_prod_swap (μ := μ) (ν := μ) (fun p : X × X ↦ a p * b p.swap))

/-- Paper: Theorem C.3.7.1(2)(b), p. 708. A nuclear integral operator has
Hilbert-Schmidt factors whose kernel convolution represents the original kernel.
The convolution is defined almost everywhere on the diagonal, where it is
integrable and computes the trace.
Deviation: The smoothening is expressed by the factor-kernel convolution
described on pp. 707–708. -/
theorem exists_integralKernel_smoothening (k : Lp ℂ 2 (μ.prod μ))
    (hT : IsNuclearOperator (integralKernelOperator μ k).val) :
    ∃ a b : Lp ℂ 2 (μ.prod μ),
      (integralKernelOperator μ k).val =
        (integralKernelOperator μ a).val.comp (integralKernelOperator μ b).val ∧
      let integrand (p : X × X) (z : X) := a (p.1, z) * b (z, p.2)
      let smoothened (p : X × X) := ∫ z, integrand p z ∂μ
      (∀ᵐ p ∂(μ.prod μ), Integrable (integrand p) μ ∧ smoothened p = k p) ∧
        (∀ᵐ x ∂μ, Integrable (integrand (x, x)) μ) ∧
        Integrable (fun x ↦ smoothened (x, x)) μ ∧
        hilbertTrace ⟨(integralKernelOperator μ k).val, hT⟩ =
          ∫ x, smoothened (x, x) ∂μ := by
  obtain ⟨A, B, hcomp⟩ :=
    exists_hilbertSchmidt_factorization (integralKernelOperator μ k).val hT
  obtain ⟨a, rfl⟩ := (bijective_integralKernelOperator μ).surjective A
  obtain ⟨b, rfl⟩ := (bijective_integralKernelOperator μ).surjective B
  obtain ⟨hc, hint⟩ := memLp_integralKernel_convolution μ a b
  have hkernel : hc.toLp _ = k := by
    apply (bijective_integralKernelOperator μ).injective
    exact Subtype.ext ((integralKernelOperator_convolution μ a b hc).trans hcomp.symm)
  have hdiag := integrable_integralKernel_mul_swap μ a b
  refine ⟨a, b, hcomp, ?_, hdiag.prod_right_ae, hdiag.integral_prod_left, ?_⟩
  · have hcoe := hc.coeFn_toLp
    rw [hkernel] at hcoe
    filter_upwards [hint, hcoe] with p h₁ h₂
    exact ⟨h₁, h₂.symm⟩
  · have hnuc : IsNuclearOperator
        ((integralKernelOperator μ a).val.comp (integralKernelOperator μ b).val) := hcomp ▸ hT
    have htrace : (⟨(integralKernelOperator μ k).val, hT⟩ : nuclearEndomorphisms (Lp ℂ 2 μ)) =
        ⟨(integralKernelOperator μ a).val.comp (integralKernelOperator μ b).val, hnuc⟩ :=
      Subtype.ext hcomp
    rw [htrace, hilbertTrace_integralKernelOperator_comp]
    exact integral_prod _ hdiag

end RiemannMasullo
