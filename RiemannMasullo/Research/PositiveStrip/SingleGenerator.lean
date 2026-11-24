module
public import RiemannMasullo.ForMathlib.Analysis.Complex.StripReciprocal
public import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Tactic
public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Analysis.Meromorphic.NormalForm
public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.Harmonic.Poisson
public import Mathlib.Analysis.Complex.Harmonic.MeanValue
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Topology.UniformSpace.CompactConvergence
public import RiemannMasullo.Ch10_TraceSpectral.Sec2
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
import all RiemannMasullo.Ch10_TraceSpectral.Sec2
import all RiemannMasullo.Ch09_HardySobolev.Sec2
import all RiemannMasullo.Ch09_HardySobolev.Sec3
import all RiemannMasullo.Ch10_TraceSpectral.Sec1

section

open Filter Function Metric Set
open scoped BigOperators ComplexConjugate Topology

@[expose] public noncomputable section
namespace RiemannMasullo
open MeasureTheory MeromorphicOn Real


private theorem synthesis_finite_sum_le_finsum_of_nonneg {α : Type*} (f : α → ℝ)
    (hf : (support f).Finite) (hn : 0 ≤ f) (S : Finset α) :
    ∑ x ∈ S, f x ≤ ∑ᶠ x, f x := by
  classical
  have hsub : support f ⊆ ↑(S ∪ hf.toFinset) := fun x hx ↦
    Finset.mem_union_right _ (hf.mem_toFinset.mpr hx)
  rw [finsum_eq_sum_of_support_subset _ hsub]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun x _ _ ↦ hn x)

/-- The weighted sum of the logarithmic distances of any finite collection of
zeros from the boundary is bounded by the central deficit in Jensen's formula. -/
theorem synthesis_disk_divisor_finite_log_sum_le {g : ℂ → ℂ} {M : ℝ} (hM : 1 ≤ M)
    (hg : AnalyticOnNhd ℂ g (ball 0 1)) (hg₀ : g 0 ≠ 0)
    (hb : ∀ z ∈ ball 0 1, ‖g z‖ ≤ M) (S : Finset ℂ) :
    ∑ z ∈ S, (divisor g (ball 0 1) z : ℝ) * log ‖z‖⁻¹ ≤ log M - log ‖g 0‖ := by
  classical
  let d := divisor g (ball 0 1)
  have hc (z : ℂ) : ContinuousAt (fun r : ℝ ↦ log (r * ‖z‖⁻¹)) 1 := by
    by_cases hz : z = 0
    · simp [hz, continuousAt_const]
    · exact (continuousAt_id.mul continuousAt_const).log (by simp [hz])
  have hlim : Tendsto (fun r : ℝ ↦ ∑ z ∈ S, (d z : ℝ) * log (r * ‖z‖⁻¹))
      (𝓝[<] 1) (𝓝 (∑ z ∈ S, (d z : ℝ) * log ‖z‖⁻¹)) := by
    apply tendsto_finsetSum
    intro z hz
    exact tendsto_const_nhds.mul (by simpa only [one_mul] using ((hc z).tendsto.mono_left nhdsWithin_le_nhds))
  apply le_of_tendsto hlim
  have hS : ∀ᶠ r : ℝ in 𝓝[<] 1, ∀ z ∈ S, z ∈ ball (0 : ℂ) 1 → ‖z‖ ≤ r := by
    apply (eventually_all_finset S).mpr
    intro z hz
    by_cases h : z ∈ ball (0 : ℂ) 1
    · have hn : ‖z‖ < 1 := by simpa [mem_ball] using h
      exact (((eventually_gt_nhds hn).filter_mono nhdsWithin_le_nhds)).mono fun r hr _ ↦ hr.le
    · exact .of_forall fun _ hz ↦ (h hz).elim
  filter_upwards [hS, self_mem_nhdsWithin, (eventually_gt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds]
    with r hrS hr₁ hr₀
  have hr : r < 1 := hr₁
  let D := divisor g (closedBall 0 |r|)
  let J (z : ℂ) := (D z : ℝ) * log (r * ‖z‖⁻¹)
  have hA : AnalyticOnNhd ℂ g (closedBall 0 |r|) := hg.mono
    (closedBall_subset_ball (by rwa [abs_of_pos hr₀]))
  have hJ (z : ℂ) : 0 ≤ J z := by
    by_cases hz : z = 0
    · simp [J, hz]
    by_cases hR : z ∈ closedBall (0 : ℂ) |r|
    · apply mul_nonneg (by exact_mod_cast hA.divisor_nonneg z)
      apply log_nonneg
      rw [← div_eq_mul_inv, one_le_div (norm_pos_iff.mpr hz)]
      simpa [mem_closedBall, abs_of_pos hr₀] using hR
    · simp [J, D.apply_eq_zero_of_notMem hR]
  have hfin : (support J).Finite :=
    (D.finiteSupport (isCompact_closedBall ..)).subset (fun z h ↦ by
      change D z ≠ 0
      intro hz
      exact h (by simp [J, hz]))
  have hav : circleAverage (fun x ↦ log ‖g x‖) 0 r ≤ log M := by
    apply circleAverage_mono_on_of_le_circle
    · exact (hA.mono sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm
    · intro z hz
      obtain h | h := eq_zero_or_norm_pos (g z)
      · simpa [h] using log_nonneg hM
      · exact log_le_log h (hb z (closedBall_subset_ball (by rwa [abs_of_pos hr₀] : |r| < 1) (sphere_subset_closedBall hz)))
  have hj := hA.circleAverage_log_norm hg₀
  calc
    ∑ z ∈ S, (d z : ℝ) * log (r * ‖z‖⁻¹) ≤ ∑ z ∈ S, J z := by
      refine Finset.sum_le_sum fun z hz ↦ ?_
      by_cases h : z ∈ ball (0 : ℂ) 1
      · have hR : z ∈ closedBall (0 : ℂ) |r| := by simpa [mem_closedBall, abs_of_pos hr₀] using hrS z hz h
        exact le_of_eq (congrArg (fun n : ℤ ↦ (n : ℝ) * log (r * ‖z‖⁻¹))
          ((hg.divisor_apply h).trans (hA.divisor_apply hR).symm))
      · simpa [d.apply_eq_zero_of_notMem h] using hJ z
    _ ≤ ∑ᶠ z, J z := synthesis_finite_sum_le_finsum_of_nonneg J hfin hJ S
    _ ≤ log M - log ‖g 0‖ := by
      have he : circleAverage (fun x ↦ log ‖g x‖) 0 r = (∑ᶠ z, J z) + log ‖g 0‖ := by
        simpa only [J, D, zero_sub, norm_neg] using hj
      linarith

/-- The divisor of a nonzero bounded analytic function on the unit disk
satisfies the Blaschke condition, including the multiplicity of every zero. -/
theorem synthesis_disk_divisor_summable_one_sub_norm {g : ℂ → ℂ} {M : ℝ}
    (hg : AnalyticOnNhd ℂ g (ball 0 1)) (hg₀ : g 0 ≠ 0)
    (hb : ∀ z ∈ ball 0 1, ‖g z‖ ≤ M) :
    Summable fun z : ℂ ↦ (divisor g (ball 0 1) z : ℝ) * (1 - ‖z‖) := by
  let d := divisor g (ball 0 1)
  have hd (z : ℂ) : 0 ≤ (d z : ℝ) := by exact_mod_cast hg.divisor_nonneg z
  apply summable_of_sum_le (c := log (max 1 M) - log ‖g 0‖)
  · intro z
    by_cases hz : z ∈ ball (0 : ℂ) 1
    · have hn : ‖z‖ < 1 := by simpa [mem_ball] using hz
      exact mul_nonneg (hd z) (sub_nonneg.mpr hn.le)
    · simp [(divisor g (ball 0 1)).apply_eq_zero_of_notMem hz]
  · intro S
    refine le_trans (Finset.sum_le_sum fun z _ ↦ ?_) (synthesis_disk_divisor_finite_log_sum_le (le_max_left 1 M) hg hg₀
      (fun z hz ↦ (hb z hz).trans (le_max_right _ _)) S)
    by_cases hz : z = 0
    · subst z
      rw [hg.divisor_apply (by simp), (hg 0 (by simp)).analyticOrderAt_eq_zero.mpr hg₀]
      simp
    · apply mul_le_mul_of_nonneg_left _ (hd z)
      simpa using one_sub_inv_le_log_of_pos (inv_pos.mpr (norm_pos_iff.mpr hz))



end RiemannMasullo

namespace DiskTails
open Complex MeromorphicOn

/-- Rotation carrying a nonzero zero to its positive radius. -/
def rotation (a : ℂ) := conj a / (‖a‖ : ℂ)

private theorem rotation_norm {a : ℂ} (ha : a ≠ 0) : ‖rotation a‖ = 1 := by
  simp [rotation, norm_ne_zero_iff.mpr ha]

private theorem rotation_mul {a : ℂ} (ha : a ≠ 0) : rotation a * a = ‖a‖ := by
  rw [rotation, div_mul_eq_mul_div, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr ha)]

/-- A disk factor normalized to have the positive value ‖a‖ at zero. -/
def factor (a z : ℂ) : ℂ :=
  ((‖a‖ : ℂ) - rotation a * z) / (1 - (‖a‖ : ℂ) * (rotation a * z))

private theorem den_ne {a z : ℂ} (ha : a ≠ 0) (ha' : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    1 - (‖a‖ : ℂ) * (rotation a * z) ≠ 0 := by
  apply sub_ne_zero.mpr
  intro h
  have hn : ‖(‖a‖ : ℂ) * (rotation a * z)‖ < 1 := by
    simp only [norm_mul, rotation_norm ha, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_norm]
    nlinarith [mul_nonneg (sub_nonneg.mpr ha'.le) (norm_nonneg z)]
  simp only [← h, norm_one, lt_self_iff_false] at hn

private theorem factor_contracts {a z : ℂ} (ha : a ≠ 0) (ha' : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    ‖factor a z‖ ≤ 1 := by
  let r := ‖a‖
  let w := rotation a * z
  have hw : ‖w‖ < 1 := by simpa [w, norm_mul, rotation_norm ha] using hz
  have hr : r ^ 2 ≤ 1 := by nlinarith [norm_nonneg a, sq_nonneg (1 - r), mul_nonneg (sub_nonneg.mpr ha'.le) (add_nonneg (show 0 ≤ r from norm_nonneg a) zero_le_one)]
  have hw' : ‖w‖ ^ 2 ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hw.le) (add_nonneg (norm_nonneg w) zero_le_one)]
  have hsq : ‖1 - (r : ℂ) * w‖ ^ 2 - ‖(r : ℂ) - w‖ ^ 2 = (1-r^2)*(1-‖w‖^2) := by
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  change ‖((r : ℂ) - w) / (1 - (r : ℂ) * w)‖ ≤ 1
  rw [norm_div, div_le_one (norm_pos_iff.mpr (den_ne ha ha' hz))]
  nlinarith [norm_nonneg ((r : ℂ) - w), norm_nonneg (1 - (r : ℂ) * w),
    mul_nonneg (sub_nonneg.mpr hr) (sub_nonneg.mpr hw')]

private theorem factor_close {a z : ℂ} {R : ℝ} (ha : a ≠ 0) (ha' : ‖a‖ < 1)
    (hz : ‖z‖ ≤ R) (hR : R < 1) :
    ‖factor a z - 1‖ ≤ (1 + R) / (1 - R) * (1 - ‖a‖) := by
  let r := ‖a‖
  let w := rotation a * z
  have hw : ‖w‖ ≤ R := by simpa [w, norm_mul, rotation_norm ha] using hz
  have hr : 0 ≤ r := norm_nonneg a
  have hr1 : r ≤ 1 := ha'.le
  have hd : 1 - (r : ℂ) * w ≠ 0 := den_ne ha ha' (hz.trans_lt hR)
  have hdn : 1 - R ≤ ‖1 - (r : ℂ)*w‖ := by
    have h := norm_sub_norm_le (1 : ℂ) ((r : ℂ)*w)
    rw [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr] at h
    nlinarith [mul_nonneg (sub_nonneg.mpr hr1) (norm_nonneg w)]
  have hnum : ‖1 + w‖ ≤ 1 + R := (norm_add_le _ _).trans (by simpa using hw)
  have hid : factor a z - 1 = ((r : ℂ)-1) * (1+w) / (1 - (r : ℂ)*w) := by
    change ((r : ℂ)-w)/(1-(r : ℂ)*w)-1 = _
    field_simp
    ring
  have hrnorm : ‖(r : ℂ) - 1‖ = 1-r := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hr1)]
    ring
  rw [hid, norm_div, norm_mul, hrnorm]
  have hne := sub_pos.mpr hR
  calc
    _ ≤ (1-r) * (1+R) / (1-R) := by
      gcongr
      exact mul_nonneg (sub_nonneg.mpr hr1) (by linarith [norm_nonneg z])
    _ = _ := by ring

private theorem factor_analytic {a : ℂ} (ha : a ≠ 0) (ha' : ‖a‖ < 1) :
    AnalyticOnNhd ℂ (factor a) (ball 0 1) := by
  intro z hz
  have hw : AnalyticAt ℂ (fun u : ℂ ↦ rotation a * u) z := analyticAt_const.mul analyticAt_id
  exact (analyticAt_const.sub hw).div (analyticAt_const.sub (analyticAt_const.mul hw))
    (den_ne ha ha' (mem_ball_zero_iff.mp hz))

private theorem norm_mul_sub_one (x y : ℂ) (hx : ‖x‖ ≤ 1) :
    ‖x*y-1‖ ≤ ‖x-1‖ + ‖y-1‖ := by
  calc
    _ = ‖(x-1) + x*(y-1)‖ := by congr 1; ring
    _ ≤ _ := (norm_add_le _ _).trans (by rw [norm_mul]; nlinarith [mul_nonneg (sub_nonneg.mpr hx) (norm_nonneg (y-1))])

private theorem norm_pow_sub_one (x : ℂ) (hx : ‖x‖ ≤ 1) (m : ℕ) :
    ‖x^m-1‖ ≤ m * ‖x-1‖ := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ']
    exact (norm_mul_sub_one _ _ hx).trans (by push_cast; linarith)

private theorem norm_prod_sub_one {ι : Type*} (f : ι → ℂ) (h : ∀ i, ‖f i‖ ≤ 1) (S : Finset ι) :
    ‖∏ i ∈ S, f i - 1‖ ≤ ∑ i ∈ S, ‖f i - 1‖ := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact (norm_mul_sub_one _ _ (h i)).trans (add_le_add le_rfl ih)

private theorem product_uniform {ι : Type*} (a : ι → ℂ) (m : ι → ℕ)
    (ha : ∀ i, a i ≠ 0) (ha' : ∀ i, ‖a i‖ < 1)
    (hs : Summable (fun i ↦ (m i : ℝ) * (1 - ‖a i‖))) :
    HasProdLocallyUniformlyOn (fun i z ↦ factor (a i) z ^ m i)
      (fun z ↦ ∏' i, factor (a i) z ^ m i) (ball 0 1) := by
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_ball
  intro K hK hKc
  obtain h | h := K.eq_empty_or_nonempty
  · subst K
    rw [hasProdUniformlyOn_iff_tendstoUniformlyOn]
    exact tendstoUniformlyOn_empty
  obtain ⟨x, hx, hmax⟩ := hKc.exists_isMaxOn h (continuous_norm.continuousOn)
  let R := ‖x‖
  have hR : R < 1 := mem_ball_zero_iff.mp (hK hx)
  let C := (1 + R) / (1 - R)
  let f (i : ι) (z : ℂ) := factor (a i) z ^ m i - 1
  have hf (i) (z) (hz : z ∈ K) : ‖f i z‖ ≤ C * ((m i : ℝ) * (1 - ‖a i‖)) := by
    apply (norm_pow_sub_one _ (factor_contracts (ha i) (ha' i) (mem_ball_zero_iff.mp (hK hz))) _).trans
    calc
      _ ≤ (m i : ℝ) * (C * (1 - ‖a i‖)) := mul_le_mul_of_nonneg_left
        (factor_close (ha i) (ha' i) (hmax hz) hR) (Nat.cast_nonneg _)
      _ = _ := by ring
  have hcts (i) : ContinuousOn (f i) K :=
    (((factor_analytic (ha i) (ha' i)).continuousOn.mono hK).pow _).sub continuousOn_const
  simpa only [f, add_sub_cancel, add_sub_cancel_left, add_sub_cancel_right, add_sub_assoc, add_comm (1 : ℂ), sub_add_cancel] using
    (Summable.hasProdUniformlyOn_one_add hKc (hs.mul_left C) (.of_forall hf) hcts)

private theorem product_analytic {ι : Type*} (a : ι → ℂ) (m : ι → ℕ)
    (ha : ∀ i, a i ≠ 0) (ha' : ∀ i, ‖a i‖ < 1)
    (hs : Summable (fun i ↦ (m i : ℝ) * (1 - ‖a i‖))) :
    AnalyticOnNhd ℂ (fun z ↦ ∏' i, factor (a i) z ^ m i) (ball 0 1) := by
  have h := product_uniform a m ha ha' hs
  apply DifferentiableOn.analyticOnNhd _ isOpen_ball
  apply TendstoLocallyUniformlyOn.differentiableOn h _ isOpen_ball
  exact .of_forall fun S ↦ DifferentiableOn.fun_finsetProd fun i _ ↦
    ((factor_analytic (ha i) (ha' i)).differentiableOn).pow _

private theorem product_bound {ι : Type*} (a : ι → ℂ) (m : ι → ℕ)
    (ha : ∀ i, a i ≠ 0) (ha' : ∀ i, ‖a i‖ < 1)
    (hs : Summable (fun i ↦ (m i : ℝ) * (1 - ‖a i‖))) (z : ℂ) (hz : ‖z‖ < 1) :
    ‖∏' i, factor (a i) z ^ m i‖ ≤ 1 ∧
    ‖(∏' i, factor (a i) z ^ m i) - 1‖ ≤
      ((1 + ‖z‖)/(1 - ‖z‖)) * ∑' i, (m i : ℝ) * (1 - ‖a i‖) := by
  let C := (1 + ‖z‖)/(1 - ‖z‖)
  have hp := (product_uniform a m ha ha' hs).hasProd (mem_ball_zero_iff.mpr hz)
  have h1 (i) : ‖factor (a i) z ^ m i‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (factor_contracts (ha i) (ha' i) hz)
  constructor
  · apply le_of_tendsto' hp.norm
    intro S
    rw [norm_prod]
    exact Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _) fun i _ ↦ h1 i
  · apply le_of_tendsto' (hp.sub tendsto_const_nhds).norm
    intro S
    apply (norm_prod_sub_one _ h1 S).trans
    calc
      _ ≤ ∑ i ∈ S, C * ((m i : ℝ) * (1 - ‖a i‖)) := by
        apply Finset.sum_le_sum
        intro i _
        apply (norm_pow_sub_one _ (factor_contracts (ha i) (ha' i) hz) _).trans
        calc
          _ ≤ (m i : ℝ) * (C * (1 - ‖a i‖)) := mul_le_mul_of_nonneg_left
            (factor_close (ha i) (ha' i) le_rfl hz) (Nat.cast_nonneg _)
          _ = _ := by ring
      _ = C * ∑ i ∈ S, (m i : ℝ) * (1 - ‖a i‖) := (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (hs.sum_le_tsum S (fun i _ ↦ mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (ha' i).le)))
        (div_nonneg (by positivity) (sub_nonneg.mpr hz.le))

private theorem product_divisible {ι : Type*} (a : ι → ℂ) (m : ι → ℕ)
    (ha : ∀ i, a i ≠ 0) (ha' : ∀ i, ‖a i‖ < 1)
    (hs : Summable (fun i ↦ (m i : ℝ) * (1 - ‖a i‖))) (i : ι) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G (a i) ∧
      (fun z ↦ ∏' j, factor (a j) z ^ m j) =ᶠ[𝓝 (a i)]
        fun z ↦ (z - a i) ^ m i * G z := by
  classical
  let n (j : ι) := if j = i then 0 else m j
  have hs' : Summable (fun j ↦ (n j : ℝ) * (1 - ‖a j‖)) := by
    apply Summable.of_nonneg_of_le (fun j ↦ mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (ha' j).le)) _ hs
    intro j
    by_cases h : j = i
    · simp only [n, ite_eq_left h, Nat.cast_zero, zero_mul]
      exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (ha' j).le)
    · simp [n, h]
  let D (z : ℂ) := 1 - (‖a i‖ : ℂ) * (rotation (a i) * z)
  let V (z : ℂ) := -rotation (a i)/D z
  let U (z : ℂ) := ∏' j, factor (a j) z ^ n j
  have hai : a i ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr (ha' i)
  have hD : AnalyticAt ℂ D (a i) :=
    analyticAt_const.sub (analyticAt_const.mul (analyticAt_const.mul analyticAt_id))
  have hV : AnalyticAt ℂ V (a i) :=
    analyticAt_const.div hD (den_ne (ha i) (ha' i) (ha' i))
  have hU : AnalyticAt ℂ U (a i) := product_analytic a n ha ha' hs' _ hai
  refine ⟨fun z ↦ V z ^ m i * U z, (hV.pow _).mul hU, ?_⟩
  filter_upwards [isOpen_ball.mem_nhds hai] with z hz
  have hu : Function.update (fun j ↦ factor (a j) z ^ m j) i 1 =
      fun j ↦ factor (a j) z ^ n j := by
    funext j
    by_cases h : j = i <;> simp [h, n, Function.update_of_ne]
  have hconv : Multipliable (Function.update (fun j ↦ factor (a j) z ^ m j) i 1) := by
    rw [hu]
    exact ((product_uniform a n ha ha' hs').hasProd hz).multipliable
  rw [Multipliable.tprod_eq_mul_tprod_ite' i hconv]
  have htail : (∏' j, if j = i then 1 else factor (a j) z ^ m j) = U z := by
    apply tprod_congr
    intro j
    by_cases h : j = i <;> simp [n, h]
  have hfac : factor (a i) z = (z - a i) * V z := by
    have hn : ((‖a i‖ : ℂ) - rotation (a i) * z) = (z - a i) * (-rotation (a i)) := by
      rw [← rotation_mul (ha i)]
      ring
    change ((‖a i‖ : ℂ) - rotation (a i) * z)/D z = (z-a i)*(-rotation (a i)/D z)
    rw [hn, mul_div_assoc]
  rw [htail, hfac, mul_pow, mul_assoc]

/-- Any divisor satisfying the Blaschke condition has contractive holomorphic
tail factors on the disk. The tails tend pointwise to one and have all
prescribed zero multiplicities outside a finite set. -/
theorem exists_holomorphic_disk_tails {ι : Type*} (a : ι → ℂ) (m : ι → ℕ)
    (ha : ∀ i, a i ≠ 0) (ha' : ∀ i, ‖a i‖ < 1)
    (hs : Summable (fun i ↦ (m i : ℝ) * (1 - ‖a i‖))) :
    ∃ B : Finset ι → ℂ → ℂ,
      (∀ S, AnalyticOnNhd ℂ (B S) (ball 0 1)) ∧
      (∀ S z, ‖z‖ < 1 → ‖B S z‖ ≤ 1) ∧
      (∀ z, ‖z‖ < 1 → Tendsto (fun S ↦ B S z) atTop (𝓝 1)) ∧
      ∀ (S : Finset ι) (i : ι), i ∉ S →
        ∃ G : ℂ → ℂ, AnalyticAt ℂ G (a i) ∧
          B S =ᶠ[𝓝 (a i)] fun z ↦ (z - a i) ^ m i * G z := by
  classical
  let ar (S : Finset ι) (j : {j // j ∉ S}) := a j.val
  let mult (S : Finset ι) (j : {j // j ∉ S}) := m j.val
  let tail (S : Finset ι) (z : ℂ) := ∏' j : {j // j ∉ S}, factor (ar S j) z ^ mult S j
  have hn (S : Finset ι) (j) : ar S j ≠ 0 := ha j.val
  have hlt (S : Finset ι) (j) : ‖ar S j‖ < 1 := ha' j.val
  have hconv (S : Finset ι) : Summable (fun j ↦ (mult S j : ℝ) * (1-‖ar S j‖)) := hs.subtype _
  have hA (S : Finset ι) : AnalyticOnNhd ℂ (tail S) (ball 0 1) :=
    product_analytic (ar S) (mult S) (hn S) (hlt S) (hconv S)
  have hbound (S : Finset ι) (z : ℂ) (hz : ‖z‖ < 1) := product_bound
    (ar S) (mult S) (hn S) (hlt S) (hconv S) z hz
  refine ⟨tail, hA, fun S z hz ↦ (hbound S z hz).1, ?_, ?_⟩
  · intro z hz
    let C := (1+‖z‖)/(1-‖z‖)
    let u (i : ι) := (m i : ℝ) * (1-‖a i‖)
    have hmajor (S : Finset ι) : ‖tail S z - 1‖ ≤ C * ∑' j : {x // x ∉ S}, u j.val :=
      (hbound S z hz).2
    have hlim : Tendsto (fun S : Finset ι ↦ C * ∑' j : {x // x ∉ S}, u j.val) atTop (𝓝 0) := by
      simpa only [mul_zero] using (tendsto_tsum_compl_atTop_zero u).const_mul C
    exact tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero (fun S ↦ norm_nonneg _) hmajor hlim)
  · intro S i hi
    let j : {x // x ∉ S} := ⟨i, hi⟩
    exact product_divisible (ar S) (mult S) (hn S) (hlt S) (hconv S) j

/-- A continuous finite inner multiplier with modulus one on the unit circle
preserves the supremum bound of an analytic function on the open disk. -/
theorem disk_inner_multiplier_bound (P F : ℂ → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hP : ContinuousOn P (closedBall 0 1))
    (hboundary : ∀ w ∈ sphere (0 : ℂ) 1, ‖P w‖ = 1)
    (hF : AnalyticOnNhd ℂ F (ball 0 1))
    (hb : ∀ w ∈ ball (0:ℂ) 1, ‖P w * F w‖ ≤ M) (w : ℂ) (hw : w ∈ ball 0 1) :
    ‖F w‖ ≤ M := by
  by_contra! h
  have hn := hM.trans_lt h
  obtain ⟨m,hm,h1⟩ := exists_between ((div_lt_one hn).mpr h)
  have hmpos := (div_nonneg hM hn.le).trans_lt hm
  let K := {z ∈ closedBall (0:ℂ) 1 | ‖P z‖ ≤ m}
  have hK : IsClosed K := hP.norm.preimage_isClosed_of_isClosed isClosed_closedBall isClosed_Iic
  have hsub : K ⊆ ball 0 1 := by
    intro z hz
    have hzball : ‖z‖ ≤ 1 := by simpa [mem_closedBall] using hz.1
    refine mem_ball_zero_iff.mpr (lt_of_le_of_ne hzball ?_)
    intro hz'
    have he := hboundary z (by simpa [mem_sphere] using hz')
    have hp := hz.2
    linarith
  obtain ⟨R,hR,hRsub⟩ := exists_lt_subset_ball hK hsub
  obtain ⟨r,hl,hr⟩ := exists_between (max_lt hR (mem_ball_zero_iff.mp hw))
  have hRr := (le_max_left R ‖w‖).trans_lt hl
  have hwr := (le_max_right R ‖w‖).trans_lt hl
  have hc : ‖F w‖ ≤ M/m := by
    apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
      (hF.differentiableOn.diffContOnCl_ball (closedBall_subset_ball hr))
    · intro z hz
      have hs := frontier_ball_subset_sphere hz
      have hzr : ‖z‖ = r := by simpa [mem_sphere] using hs
      have hzi := mem_ball_zero_iff.mpr (hzr.trans_lt hr)
      have hzm : m ≤ ‖P z‖ := by
        by_contra! hlt
        have hzK : z ∈ K := ⟨ball_subset_closedBall hzi,hlt.le⟩
        have := mem_ball_zero_iff.mp (hRsub hzK)
        linarith
      have hp := hb z hzi
      rw [norm_mul] at hp
      exact (le_div_iff₀ hmpos).mpr (by nlinarith [mul_le_mul_of_nonneg_right hzm (norm_nonneg (F z))])
    · exact subset_closure (mem_ball_zero_iff.mpr hwr)
  have hlow := (div_lt_iff₀ hn).mp hm
  have hupp := (le_div_iff₀ hmpos).mp hc
  linarith

private theorem factor_den_closed {a z : ℂ} (ha : a ≠ 0) (ha' : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    1 - (‖a‖ : ℂ)*(rotation a*z) ≠ 0 := by
  apply sub_ne_zero.mpr
  intro h
  have hp : ‖(‖a‖ : ℂ)*(rotation a*z)‖ < 1 := by
    rw [norm_mul,norm_mul,rotation_norm ha,one_mul,Complex.norm_real,Real.norm_eq_abs,abs_norm]
    exact (mul_le_of_le_one_right (norm_nonneg a) hz).trans_lt ha'
  simp [← h] at hp

private theorem factor_continuousOn_closed {a : ℂ} (ha : a ≠ 0) (ha' : ‖a‖ < 1) :
    ContinuousOn (factor a) (closedBall 0 1) := by
  intro z hz
  let V (w : ℂ) := rotation a*w
  have hV : ContinuousAt V z := continuousAt_const.mul continuousAt_id
  exact ((continuousAt_const.sub hV).div (continuousAt_const.sub (continuousAt_const.mul hV))
    (factor_den_closed ha ha' (by simpa [mem_closedBall] using hz))).continuousWithinAt

private theorem factor_boundary {a z : ℂ} (ha : a ≠ 0) (ha' : ‖a‖ < 1) (hz : ‖z‖ = 1) :
    ‖factor a z‖ = 1 := by
  let r := ‖a‖
  let w := rotation a*z
  have hw : ‖w‖ = 1 := by simp [w,rotation_norm ha,hz]
  have hsq : ‖1-(r:ℂ)*w‖^2-‖(r:ℂ)-w‖^2 = (1-r^2)*(1-‖w‖^2) := by
    simp only [← Complex.normSq_eq_norm_sq,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,
      Complex.mul_re,Complex.mul_im,Complex.one_re,Complex.one_im,Complex.ofReal_re,Complex.ofReal_im]
    ring
  have he : ‖(r:ℂ)-w‖ = ‖1-(r:ℂ)*w‖ := by
    rw [hw] at hsq
    nlinarith [norm_nonneg ((r:ℂ)-w),norm_nonneg (1-(r:ℂ)*w)]
  have hd := norm_ne_zero_iff.mpr (factor_den_closed ha ha' hz.le)
  change ‖((r:ℂ)-w)/(1-(r:ℂ)*w)‖ = 1
  rw [norm_div,he,div_self hd]


/-- Full normalized product with the specified zero multiplicities. -/
def diskBlaschkeProduct {ι : Type*} (a : ι → ℂ) (m : ι → ℕ) (z : ℂ) : ℂ :=
  ∏' i, factor (a i) z ^ m i

/-- Normalized product of a finite set of blocks of the divisor. -/
def diskBlaschkeFinite {ι : Type*} (a : ι → ℂ) (m : ι → ℕ) (S : Finset ι) (z : ℂ) : ℂ :=
  ∏ i ∈ S, factor (a i) z ^ m i

/-- Normalized product with the given finite set of zero blocks omitted. -/
def diskBlaschkeTail {ι : Type*} (a : ι → ℂ) (m : ι → ℕ) (S : Finset ι) (z : ℂ) : ℂ :=
  diskBlaschkeProduct (fun i : {j // j ∉ S} ↦ a i.val) (fun i ↦ m i.val) z

private def factorUnit (a z : ℂ) := -rotation a / (1-(‖a‖:ℂ)*(rotation a*z))

private theorem factor_unit_decomposition {a : ℂ} (ha : a ≠ 0) (z : ℂ) :
    factor a z = (z-a)*factorUnit a z := by
  have hh : ((‖a‖:ℂ)-rotation a*z) = (z-a)*(-rotation a) := by rw [←rotation_mul ha]; ring
  unfold factor factorUnit
  rw [hh,mul_div_assoc]

private theorem factor_unit_ne {a z : ℂ} (ha : a ≠ 0) (ha' : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    factorUnit a z ≠ 0 := by
  apply div_ne_zero _ (den_ne ha ha' hz)
  intro hh
  have := rotation_norm ha
  simp [neg_eq_zero.mp hh] at this

private theorem factor_unit_analytic {a z : ℂ} (ha : a ≠ 0) (ha' : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    AnalyticAt ℂ (factorUnit a) z :=
  analyticAt_const.div (analyticAt_const.sub (analyticAt_const.mul (analyticAt_const.mul analyticAt_id)))
    (den_ne ha ha' hz)

/-- The product is nonzero away from its specified positive-multiplicity roots. -/
theorem diskBlaschkeProduct_ne_zero {ι : Type*} (a : ι → ℂ) (m : ι → ℕ)
    (ha : ∀ i, a i ≠ 0) (ha' : ∀ i, ‖a i‖ < 1)
    (hs : Summable (fun i ↦ (m i : ℝ)*(1-‖a i‖))) {z : ℂ} (hz : ‖z‖ < 1)
    (hmiss : ∀ i, m i ≠ 0 → z ≠ a i) : diskBlaschkeProduct a m z ≠ 0 := by
  let u (i : ι) := factor (a i) z ^ m i - 1
  have he (i : ι) : 1+u i = factor (a i) z ^ m i := by dsimp [u]; ring
  have hn (i : ι) : 1 + u i ≠ 0 := by
    rw [he]
    by_cases hm : m i = 0
    · simp [hm]
    · rw [factor_unit_decomposition (ha i)]
      exact pow_ne_zero _ (mul_ne_zero (sub_ne_zero.mpr (hmiss i hm)) (factor_unit_ne (ha i) (ha' i) hz))
  let C := (1+‖z‖)/(1-‖z‖)
  have hsum : Summable fun i ↦ ‖u i‖ := by
    apply Summable.of_nonneg_of_le (fun i ↦ norm_nonneg _) _ (hs.mul_left C)
    intro i
    apply (norm_pow_sub_one _ (factor_contracts (ha i) (ha' i) hz) _).trans
    calc
      _ ≤ (m i : ℝ)*(C*(1-‖a i‖)) := mul_le_mul_of_nonneg_left (factor_close (ha i) (ha' i) le_rfl hz) (Nat.cast_nonneg _)
      _ = _ := by ring
  simpa only [he,diskBlaschkeProduct] using tprod_one_add_ne_zero_of_summable hn hsum

private theorem product_split {ι : Type*} (a : ι → ℂ) (m : ι → ℕ) (S : Finset ι)
    (ha : ∀ i, a i ≠ 0) (ha' : ∀ i, ‖a i‖ < 1)
    (hs : Summable (fun i ↦ (m i : ℝ)*(1-‖a i‖))) (z : ℂ) (hz : z ∈ ball 0 1) :
    diskBlaschkeFinite a m S z * diskBlaschkeTail a m S z = diskBlaschkeProduct a m z := by
  let F (i : ι) := factor (a i) z ^ m i
  have hin : Multipliable (fun i : {j // j ∈ S} ↦ F i.val) := (hasProd_fintype _).multipliable
  have hout : Multipliable (fun i : {j // j ∉ S} ↦ F i.val) :=
    ((product_uniform (fun i : {j // j ∉ S} ↦ a i.val) (fun i ↦ m i.val)
      (fun i ↦ ha i.val) (fun i ↦ ha' i.val) (hs.subtype _)).hasProd hz).multipliable
  have h := Multipliable.tprod_mul_tprod_compl (s := (S : Set ι)) (f := F) hin hout
  rw [Finset.tprod_subtype' S F] at h
  exact h

/-- The product has exactly the specified multiplicity at every marked point,
including zero multiplicities. -/
theorem diskBlaschkeProduct_order {ι : Type*} (a : ι → ℂ) (m : ι → ℕ)
    (hinj : Injective a) (ha : ∀ i, a i ≠ 0) (ha' : ∀ i, ‖a i‖ < 1)
    (hs : Summable (fun i ↦ (m i : ℝ)*(1-‖a i‖))) (i : ι) :
    analyticOrderAt (diskBlaschkeProduct a m) (a i) = m i := by
  classical
  let S : Finset ι := {i}
  let U := diskBlaschkeTail a m S
  have hmem := mem_ball_zero_iff.mpr (ha' i)
  have hA : AnalyticAt ℂ (diskBlaschkeProduct a m) (a i) := product_analytic a m ha ha' hs _ hmem
  have hU : AnalyticAt ℂ U (a i) :=
    product_analytic (fun j : {j // j ∉ S} ↦ a j.val) (fun j ↦ m j.val)
      (fun j ↦ ha j.val) (fun j ↦ ha' j.val) (hs.subtype _) _ hmem
  have hune : U (a i) ≠ 0 := by
    apply diskBlaschkeProduct_ne_zero (fun j : {j // j ∉ S} ↦ a j.val) (fun j ↦ m j.val)
      (fun j ↦ ha j.val) (fun j ↦ ha' j.val) (hs.subtype _) (ha' i)
    intro j _ h
    exact j.property (by simpa [S] using (hinj h).symm)
  refine hA.analyticOrderAt_eq_natCast.mpr ⟨fun z ↦ factorUnit (a i) z ^ m i * U z,
    ((factor_unit_analytic (ha i) (ha' i) (ha' i)).pow _).mul hU,
    mul_ne_zero (pow_ne_zero _ (factor_unit_ne (ha i) (ha' i) (ha' i))) hune, ?_⟩
  filter_upwards [isOpen_ball.mem_nhds hmem] with z hz
  have he := (product_split a m S ha ha' hs z hz).symm
  simpa only [U,S,diskBlaschkeFinite,Finset.prod_singleton,factor_unit_decomposition (ha i),
    mul_pow,mul_assoc,smul_eq_mul] using he


/-- Removing all and exactly the zeros, counted with their finite analytic
orders, yields a holomorphic zero-free quotient, including at the removed roots. -/
theorem exists_analytic_zero_free_quotient {U : Set ℂ} (g B : ℂ → ℂ)
    (hg : AnalyticOnNhd ℂ g U) (hB : AnalyticOnNhd ℂ B U)
    (ho : ∀ z ∈ U, ∃ n : ℕ, analyticOrderAt g z = n ∧ analyticOrderAt B z = n) :
    ∃ Q : ℂ → ℂ, AnalyticOnNhd ℂ Q U ∧ (∀ z ∈ U, Q z ≠ 0) ∧
      ∀ z ∈ U, B z * Q z = g z := by
  let Q := toMeromorphicNFOn (g/B) U
  have hm : MeromorphicOn (g/B) U := hg.meromorphicOn.div hB.meromorphicOn
  have hnormal : MeromorphicNFOn Q U := meromorphicNFOn_toMeromorphicNFOn _ _
  have horders (z : ℂ) (hz : z ∈ U) : meromorphicOrderAt Q z = 0 ∧ meromorphicOrderAt B z ≠ ⊤ := by
    obtain ⟨n,hg₀,hB₀⟩ := ho z hz
    have hgb : meromorphicOrderAt B z = ((n:ℤ) : WithTop ℤ) := by rw [(hB z hz).meromorphicOrderAt_eq,hB₀]; simp
    have hgg : meromorphicOrderAt g z = ((n:ℤ) : WithTop ℤ) := by rw [(hg z hz).meromorphicOrderAt_eq,hg₀]; simp
    refine ⟨?_,by simp [hgb]⟩
    change meromorphicOrderAt (toMeromorphicNFOn (g/B) U) z = 0
    rw [meromorphicOrderAt_toMeromorphicNFOn hm hz,meromorphicOrderAt_div (hg z hz).meromorphicAt
      (hB z hz).meromorphicAt,hgg,hgb]
    simp
  have hQ : AnalyticOnNhd ℂ Q U := fun z hz ↦ (hnormal hz).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    (le_of_eq (horders z hz).1.symm)
  refine ⟨Q,hQ,fun z hz ↦ (hnormal hz).meromorphicOrderAt_eq_zero_iff.mp (horders z hz).1,?_⟩
  intro z hz
  have hbn := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hB z hz).meromorphicAt).mp (horders z hz).2
  have hev : (fun u ↦ B u * Q u) =ᶠ[𝓝[≠] z] g := by
    filter_upwards [hm.toMeromorphicNFOn_eq_self_on_nhdsNE hz,hbn] with u hq hu
    change Q u = g u/B u at hq
    rw [hq,mul_div_cancel₀ _ hu]
  have ht := (((hB z hz).continuousAt.mul (hQ z hz).continuousAt).tendsto.mono_left
    (nhdsWithin_le_nhds (s := {z}ᶜ))).congr' hev
  exact tendsto_nhds_unique ht ((hg z hz).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)


theorem diskBlaschkeTail_tendsto {ι : Type*} (a : ι → ℂ) (m : ι → ℕ)
    (ha : ∀ i, a i ≠ 0) (ha' : ∀ i, ‖a i‖ < 1)
    (hs : Summable (fun i ↦ (m i : ℝ)*(1-‖a i‖))) {z : ℂ} (hz : ‖z‖ < 1) :
    Tendsto (fun S ↦ diskBlaschkeTail a m S z) atTop (𝓝 1) := by
  let C := (1+‖z‖)/(1-‖z‖)
  let u (i : ι) := (m i : ℝ)*(1-‖a i‖)
  have hmajor (S : Finset ι) : ‖diskBlaschkeTail a m S z - 1‖ ≤ C * ∑' j : {x // x ∉ S}, u j.val :=
    (product_bound (fun j : {x // x ∉ S} ↦ a j.val) (fun j ↦ m j.val) (fun j ↦ ha _) (fun j ↦ ha' _)
      (hs.subtype _) z hz).2
  have hlim : Tendsto (fun S : Finset ι ↦ C * ∑' j : {x // x ∉ S}, u j.val) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_tsum_compl_atTop_zero u).const_mul C
  exact tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero (fun S ↦ norm_nonneg _) hmajor hlim)

private theorem bound_of_blaschke_mul {ι : Type*} (a : ι → ℂ) (m : ι → ℕ)
    (ha : ∀ i, a i ≠ 0) (ha' : ∀ i, ‖a i‖ < 1)
    (hs : Summable (fun i ↦ (m i : ℝ)*(1-‖a i‖))) (Q : ℂ → ℂ)
    (hQ : AnalyticOnNhd ℂ Q (ball 0 1)) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ z ∈ ball (0 : ℂ) 1, ‖diskBlaschkeProduct a m z * Q z‖ ≤ M) :
    ∀ z ∈ ball (0:ℂ) 1, ‖Q z‖ ≤ M := by
  intro z hz
  have hlim : Tendsto (fun S ↦ diskBlaschkeTail a m S z * Q z) atTop (𝓝 (Q z)) := by
    simpa using (diskBlaschkeTail_tendsto a m ha ha' hs (mem_ball_zero_iff.mp hz)).mul_const (Q z)
  apply le_of_tendsto' hlim.norm
  intro S
  let P := diskBlaschkeFinite a m S
  let T := diskBlaschkeTail a m S
  have hP : ContinuousOn P (closedBall 0 1) :=
    continuousOn_finsetProd S (fun i _ ↦ (factor_continuousOn_closed (ha i) (ha' i)).pow _)
  have hPb (w : ℂ) (hw : w ∈ sphere 0 1) : ‖P w‖ = 1 := by
    have hwn : ‖w‖ = 1 := by simpa [mem_sphere] using hw
    change ‖∏ i ∈ S, factor (a i) w ^ m i‖ = 1
    rw [norm_prod]
    apply Finset.prod_eq_one
    intro i _
    rw [norm_pow,factor_boundary (ha i) (ha' i) hwn,one_pow]
  have hT : AnalyticOnNhd ℂ T (ball 0 1) :=
    product_analytic (fun i : {j // j ∉ S} ↦ a i.val) (fun i ↦ m i.val)
      (fun i ↦ ha _) (fun i ↦ ha' _) (hs.subtype _)
  apply disk_inner_multiplier_bound P (fun w ↦ T w * Q w) M hM hP hPb (hT.mul hQ) _ z hz
  intro w hw
  change ‖diskBlaschkeFinite a m S w * (diskBlaschkeTail a m S w * Q w)‖ ≤ M
  rw [←mul_assoc,product_split a m S ha ha' hs w hw]
  exact hb w hw

/-- A bounded analytic function on the unit disk factors as the full normalized
Blaschke product of its zeros with multiplicity times a bounded zero-free analytic
function. The analytic factor satisfies the same supremum bound as the original. -/
theorem exists_bounded_analytic_blaschke_quotient {ι : Type*} (a : ι → ℂ) (m : ι → ℕ)
    (hinj : Injective a) (ha : ∀ i, a i ≠ 0) (ha' : ∀ i, ‖a i‖ < 1)
    (hs : Summable (fun i ↦ (m i : ℝ)*(1-‖a i‖))) (g : ℂ → ℂ)
    (hg : AnalyticOnNhd ℂ g (ball 0 1)) (horder : ∀ i, analyticOrderAt g (a i) = m i)
    (hroots : ∀ z ∈ ball (0:ℂ) 1, g z = 0 → ∃ i, a i = z)
    (M : ℝ) (hb : ∀ z ∈ ball (0 : ℂ) 1, ‖g z‖ ≤ M) :
    ∃ Q : ℂ → ℂ, AnalyticOnNhd ℂ Q (ball 0 1) ∧ (∀ z ∈ ball (0:ℂ) 1, Q z ≠ 0) ∧
      (∀ z ∈ ball (0:ℂ) 1, ‖Q z‖ ≤ M) ∧
      ∀ z ∈ ball (0:ℂ) 1, diskBlaschkeProduct a m z * Q z = g z := by
  have hB : AnalyticOnNhd ℂ (diskBlaschkeProduct a m) (ball 0 1) := product_analytic a m ha ha' hs
  have horders (z : ℂ) (hz : z ∈ ball 0 1) :
      ∃ n : ℕ, analyticOrderAt g z = n ∧ analyticOrderAt (diskBlaschkeProduct a m) z = n := by
    by_cases h : ∃ i, a i = z
    · obtain ⟨i,rfl⟩ := h
      exact ⟨m i,horder i,diskBlaschkeProduct_order a m hinj ha ha' hs i⟩
    · have hg' : g z ≠ 0 := fun hh ↦ h (hroots z hz hh)
      have hB' := diskBlaschkeProduct_ne_zero a m ha ha' hs (mem_ball_zero_iff.mp hz)
        (fun i _ hi ↦ h ⟨i,hi.symm⟩)
      exact ⟨0,(hg z hz).analyticOrderAt_eq_zero.mpr hg',(hB z hz).analyticOrderAt_eq_zero.mpr hB'⟩
  obtain ⟨Q,hQ,hn,heq⟩ := exists_analytic_zero_free_quotient g (diskBlaschkeProduct a m) hg hB horders
  refine ⟨Q,hQ,hn,bound_of_blaschke_mul a m ha ha' hs Q hQ M ((norm_nonneg (g 0)).trans (hb _ (by simp))) ?_,heq⟩
  exact fun z hz ↦ (heq z hz) ▸ hb z hz


/-- The full normalized Blaschke product indexed by the actual zero set and
with the intrinsic analytic multiplicities of g. -/
def diskBlaschkeZeroProduct (g : ℂ → ℂ) : ℂ → ℂ :=
  diskBlaschkeProduct (fun i : {z : ℂ // z ∈ ball 0 1 ∧ g z = 0} ↦ i.val)
    (fun i ↦ analyticOrderNatAt g i.val)

/-- Canonical zero factorization from the bounded analytic function alone.
The full product uses the actual zero set and intrinsic orders; Jensen's formula
supplies the Blaschke condition automatically. -/
theorem exists_canonical_disk_factorization (g : ℂ → ℂ) (hg : AnalyticOnNhd ℂ g (ball 0 1))
    (h₀ : g 0 ≠ 0) (M : ℝ) (hb : ∀ z ∈ ball (0:ℂ) 1, ‖g z‖ ≤ M) :
    ∃ Q : ℂ → ℂ, AnalyticOnNhd ℂ Q (ball 0 1) ∧ (∀ z ∈ ball (0:ℂ) 1, Q z ≠ 0) ∧
      (∀ z ∈ ball (0:ℂ) 1, ‖Q z‖ ≤ M) ∧
      ∀ z ∈ ball (0:ℂ) 1, diskBlaschkeZeroProduct g z * Q z = g z := by
  let Z := {z : ℂ // z ∈ ball 0 1 ∧ g z = 0}
  let a (i : Z) : ℂ := i.val
  let m (i : Z) := analyticOrderNatAt g i.val
  have ha (i : Z) : a i ≠ 0 := by
    intro he
    have hzero : g (a i) = 0 := i.property.2
    exact h₀ (he ▸ hzero)
  have ha' (i : Z) : ‖a i‖ < 1 := mem_ball_zero_iff.mp i.property.1
  have h0ord : analyticOrderAt g 0 ≠ ⊤ := by rw [(hg 0 (by simp)).analyticOrderAt_eq_zero.mpr h₀]; simp
  have ho (i : Z) : analyticOrderAt g (a i) = m i :=
    (Nat.cast_analyticOrderNatAt (hg.analyticOrderAt_ne_top_of_isPreconnected (convex_ball (0:ℂ) 1).isPreconnected
      (by simp) i.property.1 h0ord)).symm
  have hs : Summable (fun i ↦ (m i : ℝ)*(1-‖a i‖)) := by
    have hsum := (RiemannMasullo.synthesis_disk_divisor_summable_one_sub_norm hg h₀ hb).subtype
      (fun z ↦ z ∈ ball (0:ℂ) 1 ∧ g z = 0)
    apply hsum.congr
    intro i
    change (divisor g (ball 0 1) i.val : ℝ) * (1-‖i.val‖) = _
    rw [hg.divisor_apply i.property.1,show analyticOrderAt g i.val = (m i : ℕ∞) from ho i]
    simp [a]
  exact exists_bounded_analytic_blaschke_quotient a m Subtype.val_injective ha ha' hs g hg ho
    (fun z hz hzero ↦ ⟨⟨z,hz,hzero⟩,rfl⟩) M hb


private theorem exists_analytic_quotient_of_order_le {U : Set ℂ} (f P : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f U) (hP : AnalyticOnNhd ℂ P U)
    (hord : ∀ z ∈ U, ∃ n : ℕ, analyticOrderAt P z = n ∧ ↑n ≤ analyticOrderAt f z) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F U ∧ ∀ z ∈ U, P z * F z = f z := by
  let F := toMeromorphicNFOn (f/P) U
  have hm : MeromorphicOn (f/P) U := hf.meromorphicOn.div hP.meromorphicOn
  have hnormal : MeromorphicNFOn F U := meromorphicNFOn_toMeromorphicNFOn _ _
  have horders (z : ℂ) (hz : z ∈ U) : 0 ≤ meromorphicOrderAt F z ∧ meromorphicOrderAt P z ≠ ⊤ := by
    obtain ⟨n,hP₀,hf₀⟩ := hord z hz
    have hp : meromorphicOrderAt P z = ((n:ℤ) : WithTop ℤ) := by rw [(hP z hz).meromorphicOrderAt_eq,hP₀]; simp
    refine ⟨?_,by simp [hp]⟩
    change 0 ≤ meromorphicOrderAt (toMeromorphicNFOn (f/P) U) z
    rw [meromorphicOrderAt_toMeromorphicNFOn hm hz,meromorphicOrderAt_div (hf z hz).meromorphicAt
      (hP z hz).meromorphicAt,hp,(hf z hz).meromorphicOrderAt_eq]
    cases he : analyticOrderAt f z with
    | top => simp
    | coe j =>
      rw [he] at hf₀
      have hle : n ≤ j := by exact_mod_cast hf₀
      exact WithTop.coe_le_coe.mpr (show (0 : ℤ) ≤ (j:ℤ)-(n:ℤ) by omega)
  have hF : AnalyticOnNhd ℂ F U := fun z hz ↦ (hnormal hz).meromorphicOrderAt_nonneg_iff_analyticAt.mp (horders z hz).1
  refine ⟨F,hF,?_⟩
  intro z hz
  have hpn := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hP z hz).meromorphicAt).mp (horders z hz).2
  have hev : (fun u ↦ P u * F u) =ᶠ[𝓝[≠] z] f := by
    filter_upwards [hm.toMeromorphicNFOn_eq_self_on_nhdsNE hz,hpn] with u hq hu
    change F u = f u/P u at hq
    rw [hq,mul_div_cancel₀ _ hu]
  have ht := (((hP z hz).continuousAt.mul (hF z hz).continuousAt).tendsto.mono_left
    (nhdsWithin_le_nhds (s := {z}ᶜ))).congr' hev
  exact tendsto_nhds_unique ht ((hf z hz).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)

/-- Division by the finite Blaschke product of a prescribed set of roots of a
bounded analytic test preserves its bound. Only those finite vanishing jets are required. -/
theorem exists_bounded_finite_blaschke_quotient {ι : Type*} (a : ι → ℂ) (m : ι → ℕ) (S : Finset ι)
    (hinj : Injective a) (ha : ∀ i, a i ≠ 0) (ha' : ∀ i, ‖a i‖ < 1)
    (H : ℂ → ℂ) (hH : AnalyticOnNhd ℂ H (ball 0 1))
    (hv : ∀ i ∈ S, (m i : ℕ∞) ≤ analyticOrderAt H (a i))
    (M : ℝ) (hb : ∀ z ∈ ball (0:ℂ) 1, ‖H z‖ ≤ M) :
    ∃ N : ℂ → ℂ, AnalyticOnNhd ℂ N (ball 0 1) ∧ (∀ z ∈ ball (0:ℂ) 1, ‖N z‖ ≤ M) ∧
      ∀ z ∈ ball (0:ℂ) 1, diskBlaschkeFinite a m S z * N z = H z := by
  let P := diskBlaschkeFinite a m S
  let a' (j : {i // i ∈ S}) := a j.val
  let m' (j : {i // i ∈ S}) := m j.val
  have hinj' : Injective a' := hinj.comp Subtype.val_injective
  have hsa : Summable (fun j ↦ (m' j : ℝ)*(1-‖a' j‖)) := (hasSum_fintype _).summable
  have he : diskBlaschkeProduct a' m' = P := by
    ext z
    exact Finset.tprod_subtype S (fun i ↦ factor (a i) z ^ m i)
  have hP : AnalyticOnNhd ℂ P (ball 0 1) := he ▸
    (product_analytic a' m' (fun j ↦ ha _) (fun j ↦ ha' _) hsa : AnalyticOnNhd ℂ (diskBlaschkeProduct a' m') _)
  have horders (z : ℂ) (hz : z ∈ ball 0 1) : ∃ n : ℕ, analyticOrderAt P z = n ∧ ↑n ≤ analyticOrderAt H z := by
    by_cases h : ∃ j, a' j = z
    · obtain ⟨j,rfl⟩ := h
      refine ⟨m' j,?_,hv _ j.property⟩
      rw [←he]
      exact diskBlaschkeProduct_order a' m' hinj' (fun j ↦ ha _) (fun j ↦ ha' _) hsa j
    · refine ⟨0,(hP _ hz).analyticOrderAt_eq_zero.mpr ?_,by simp⟩
      rw [←he]
      exact diskBlaschkeProduct_ne_zero a' m' (fun j ↦ ha _) (fun j ↦ ha' _) hsa
        (mem_ball_zero_iff.mp hz) (fun j _ hj ↦ h ⟨j,hj.symm⟩)
  obtain ⟨N,hN,hprod⟩ := exists_analytic_quotient_of_order_le H P hH hP horders
  refine ⟨N,hN,?_,hprod⟩
  have hPc : ContinuousOn P (closedBall 0 1) :=
    continuousOn_finsetProd S (fun i _ ↦ (factor_continuousOn_closed (ha i) (ha' i)).pow _)
  have hPs (w : ℂ) (hw : w ∈ sphere 0 1) : ‖P w‖ = 1 := by
    have hwn : ‖w‖ = 1 := by simpa [mem_sphere] using hw
    change ‖∏ i ∈ S, factor (a i) w ^ m i‖ = 1
    rw [norm_prod]
    apply Finset.prod_eq_one
    exact fun i _ ↦ by rw [norm_pow,factor_boundary (ha i) (ha' i) hwn,one_pow]
  exact disk_inner_multiplier_bound P N M ((norm_nonneg (H 0)).trans (hb 0 (by simp))) hPc hPs hN
    (fun z hz ↦ (hprod z hz) ▸ hb z hz)


/-- Given a finite set of tested zeros, the missing-zero tail times the test
is the original function times a bounded analytic numerator over a bounded
zero-free analytic denominator. The identity holds at the zeros as well. -/
theorem exists_tail_test_quotient {ι : Type*} (a : ι → ℂ) (m : ι → ℕ)
    (hinj : Injective a) (ha : ∀ i, a i ≠ 0) (ha' : ∀ i, ‖a i‖ < 1)
    (hs : Summable (fun i ↦ (m i : ℝ)*(1-‖a i‖))) (g : ℂ → ℂ)
    (hg : AnalyticOnNhd ℂ g (ball 0 1)) (horder : ∀ i, analyticOrderAt g (a i) = m i)
    (hroots : ∀ z ∈ ball (0:ℂ) 1, g z = 0 → ∃ i, a i = z)
    (M : ℝ) (hb : ∀ z ∈ ball (0:ℂ) 1, ‖g z‖ ≤ M) :
    ∃ Q : ℂ → ℂ, AnalyticOnNhd ℂ Q (ball 0 1) ∧ (∀ z ∈ ball (0:ℂ) 1, Q z ≠ 0) ∧
      (∀ z ∈ ball (0:ℂ) 1, ‖Q z‖ ≤ M) ∧
      ∀ (S : Finset ι) (H : ℂ → ℂ), AnalyticOnNhd ℂ H (ball 0 1) →
      (∀ i ∈ S, (m i : ℕ∞) ≤ analyticOrderAt H (a i)) →
      ∀ L : ℝ, (∀ z ∈ ball (0:ℂ) 1, ‖H z‖ ≤ L) →
        ∃ N : ℂ → ℂ, AnalyticOnNhd ℂ N (ball 0 1) ∧ (∀ z ∈ ball (0:ℂ) 1, ‖N z‖ ≤ L) ∧
        ∀ z ∈ ball (0:ℂ) 1, diskBlaschkeTail a m S z * H z = g z * (N z / Q z) := by
  obtain ⟨Q,hQ,hne,hbQ,hgQ⟩ := exists_bounded_analytic_blaschke_quotient a m hinj ha ha' hs g hg
    horder hroots M hb
  refine ⟨Q,hQ,hne,hbQ,?_⟩
  intro S H hH hHv L hL
  obtain ⟨N,hN,hbN,heN⟩ := exists_bounded_finite_blaschke_quotient a m S hinj ha ha' H hH hHv L hL
  refine ⟨N,hN,hbN,?_⟩
  intro z hz
  rw [←heN z hz,←hgQ z hz,←product_split a m S ha ha' hs z hz]
  field_simp [hne z hz]


end DiskTails
end
end

section
@[expose] public noncomputable section
open Filter Function InnerProductSpace MeasureTheory Metric Real Set
open scoped Topology
namespace RiemannMasullo
/-- The strip-to-disk and disk-to-strip maps use the half-width π/(2k).
The center may have arbitrary imaginary part. -/
def synthesis_stripBlaschkeToDisk (w₀ : ℂ) (k : ℝ) (w : ℂ) : ℂ :=
  let u := Complex.exp ((k : ℂ) * (Complex.I * (w - w₀)))
  (u - 1) / (u + 1)

def synthesis_stripBlaschkeFromDisk (w₀ : ℂ) (k : ℝ) (z : ℂ) : ℂ :=
  w₀ + ((k⁻¹ : ℝ) : ℂ) * (-Complex.I * Complex.log ((1 + z) / (1 - z)))

private theorem synthesis_diskCayley_re_pos {z : ℂ} (hz : ‖z‖ < 1) :
    0 < ((1 + z) / (1 - z)).re := by
  have hn : 1 - z ≠ 0 := sub_ne_zero.mpr (fun h ↦ by simp [← h] at hz)
  have H := congrFun (poissonKernel_eq_re_herglotzRieszKernel (c := 0) (w := z)) (1 : ℂ)
  have he : ((1 + z) / (1 - z)).re = (1 - ‖z‖^2) / ‖1 - z‖^2 := by
    simpa [poissonKernel_def, herglotzRieszKernel_def] using H.symm
  rw [he]
  exact div_pos (by nlinarith [sq_lt_sq₀ (norm_nonneg z) (by norm_num : 0 ≤ (1:ℝ)) |>.mpr hz]) (pow_pos (norm_pos_iff.mpr hn) _)

private theorem synthesis_diskInverseCayley_mem {u : ℂ} (hu : 0 < u.re) :
    ‖(u - 1) / (u + 1)‖ < 1 := by
  have hn : u + 1 ≠ 0 := fun h ↦ by
    have he := congrArg Complex.re h
    simp at he
    linarith
  rw [norm_div, div_lt_one (norm_pos_iff.mpr hn)]
  apply (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, sub_zero, add_zero]
  linarith

private theorem synthesis_stripBlaschke_phase {w₀ w : ℂ} {k : ℝ} (hk : 0 < k)
    (hw : |w.re - w₀.re| < (π / 2) / k) :
    |((k : ℂ) * (Complex.I * (w - w₀))).im| < π / 2 := by
  rw [Complex.im_ofReal_mul, Complex.I_mul_im, Complex.sub_re, abs_mul, abs_of_pos hk]
  simpa only [mul_comm k _] using (lt_div_iff₀ hk).mp hw

theorem synthesis_stripBlaschkeToDisk_mem {w₀ w : ℂ} {k : ℝ} (hk : 0 < k)
    (hw : |w.re - w₀.re| < (π / 2) / k) : synthesis_stripBlaschkeToDisk w₀ k w ∈ ball 0 1 := by
  have ht := synthesis_stripBlaschke_phase hk hw
  have hpos : 0 < (Complex.exp ((k : ℂ) * (Complex.I * (w - w₀)))).re := by
    rw [Complex.exp_re]
    exact mul_pos (exp_pos _) (cos_pos_of_mem_Ioo (abs_lt.mp ht))
  simpa [synthesis_stripBlaschkeToDisk, mem_ball] using synthesis_diskInverseCayley_mem hpos

theorem synthesis_stripBlaschkeFromDisk_mem {z w₀ : ℂ} {k : ℝ} (hk : 0 < k) (hz : z ∈ ball 0 1) :
    |(synthesis_stripBlaschkeFromDisk w₀ k z).re - w₀.re| < (π / 2) / k := by
  have h := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (synthesis_diskCayley_re_pos (z := z) (by simpa [mem_ball] using hz)))
  have he : (synthesis_stripBlaschkeFromDisk w₀ k z).re - w₀.re = k⁻¹ * Complex.arg ((1 + z)/(1 - z)) := by
    simp [synthesis_stripBlaschkeFromDisk, Complex.mul_re, Complex.log_im]
  rw [he, abs_mul, abs_inv, abs_of_pos hk, show (π / 2) / k = k⁻¹ * (π / 2) from div_eq_inv_mul ..]
  exact mul_lt_mul_of_pos_left h (inv_pos.mpr hk)

private theorem synthesis_stripBlaschke_cancel (k : ℝ) (hk : 0 < k) :
    ((k⁻¹ : ℝ) : ℂ) * (-Complex.I) * ((k : ℂ) * Complex.I) = 1 := by
  rw [Complex.ofReal_inv]
  field_simp [show (k : ℂ) ≠ 0 by exact_mod_cast hk.ne']
  simp

theorem synthesis_stripBlaschkeFromDisk_toDisk {w₀ w : ℂ} {k : ℝ} (hk : 0 < k)
    (hw : |w.re - w₀.re| < (π / 2) / k) :
    synthesis_stripBlaschkeFromDisk w₀ k (synthesis_stripBlaschkeToDisk w₀ k w) = w := by
  let t := (k : ℂ) * (Complex.I * (w - w₀))
  let u := Complex.exp t
  have ht : |t.im| < π / 2 := synthesis_stripBlaschke_phase hk hw
  have hpos : 0 < u.re := by
    change 0 < (Complex.exp t).re
    rw [Complex.exp_re]
    exact mul_pos (exp_pos _) (cos_pos_of_mem_Ioo (abs_lt.mp ht))
  have hn : u + 1 ≠ 0 := fun h ↦ by
    have h' := congrArg Complex.re h
    simp at h'
    linarith
  have hz := synthesis_diskInverseCayley_mem hpos
  have hz' : 1 - (u - 1)/(u + 1) ≠ 0 := sub_ne_zero.mpr fun h ↦ by simp [← h] at hz
  have hC : (1 + (u - 1)/(u + 1)) / (1 - (u - 1)/(u + 1)) = u := by field_simp; ring
  have hlog : Complex.log u = t := Complex.log_exp (by linarith [(abs_lt.mp ht).1, pi_pos]) (by linarith [(abs_lt.mp ht).2, pi_pos])
  change w₀ + _ * (-Complex.I * Complex.log ((1 + (u - 1)/(u + 1)) / (1 - (u - 1)/(u + 1)))) = w
  rw [hC,hlog]
  change w₀ + ((k⁻¹ : ℝ) : ℂ) * (-Complex.I * ((k : ℂ) * (Complex.I * (w - w₀)))) = w
  rw [← mul_assoc, ← mul_assoc, ← mul_assoc, show ((k⁻¹ : ℝ) : ℂ) * -Complex.I * (k : ℂ) * Complex.I = 1 by
    simpa only [mul_assoc] using synthesis_stripBlaschke_cancel k hk]
  ring

theorem synthesis_stripBlaschkeToDisk_fromDisk {w₀ z : ℂ} {k : ℝ} (hk : 0 < k) (hz : z ∈ ball 0 1) :
    synthesis_stripBlaschkeToDisk w₀ k (synthesis_stripBlaschkeFromDisk w₀ k z) = z := by
  let u := (1 + z)/(1 - z)
  have hzn : ‖z‖ < 1 := by simpa [mem_ball] using hz
  have hpos : 0 < u.re := synthesis_diskCayley_re_pos hzn
  have hn : u ≠ 0 := fun h ↦ by simp [h] at hpos
  have hu : u + 1 ≠ 0 := fun h ↦ by
    have h' := congrArg Complex.re h
    simp at h'
    linarith
  have hz' : 1 - z ≠ 0 := sub_ne_zero.mpr fun h ↦ by simp [← h] at hzn
  have hC : (u - 1)/(u + 1) = z := by dsimp [u] at *; field_simp; ring
  have hphase : (k : ℂ) * (Complex.I * (synthesis_stripBlaschkeFromDisk w₀ k z - w₀)) = Complex.log u := by
    change (k : ℂ) * (Complex.I * (w₀ + ((k⁻¹ : ℝ):ℂ) * (-Complex.I * Complex.log u) - w₀)) = Complex.log u
    rw [add_sub_cancel_left]
    calc
      _ = (((k⁻¹ : ℝ):ℂ) * -Complex.I * ((k : ℂ) * Complex.I)) * Complex.log u := by ring
      _ = _ := by rw [synthesis_stripBlaschke_cancel k hk,one_mul]
  simpa only [synthesis_stripBlaschkeToDisk, hphase, Complex.exp_log hn] using hC

theorem synthesis_stripBlaschkeFromDisk_analytic_deriv {z w₀ : ℂ} {k : ℝ} (hk : 0 < k) (hz : z ∈ ball 0 1) :
    AnalyticAt ℂ (synthesis_stripBlaschkeFromDisk w₀ k) z ∧ deriv (synthesis_stripBlaschkeFromDisk w₀ k) z ≠ 0 := by
  have hzn : ‖z‖ < 1 := by simpa [mem_ball] using hz
  have hden : 1 - z ≠ 0 := sub_ne_zero.mpr fun h ↦ by simp [← h] at hzn
  have hpos := synthesis_diskCayley_re_pos hzn
  let u (v : ℂ) := (1 + v)/(1 - v)
  have hu : AnalyticAt ℂ u z := (analyticAt_const.add analyticAt_id).div (analyticAt_const.sub analyticAt_id) hden
  have hslit : u z ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl hpos)
  have hnum : u z ≠ 0 := fun h ↦ by change 0 < (u z).re at hpos; simp [h] at hpos
  refine ⟨analyticAt_const.add (analyticAt_const.mul (analyticAt_const.mul (hu.clog hslit))), ?_⟩
  have hdu : HasDerivAt u (2/(1-z)^2) z := by
    convert (((hasDerivAt_const z 1).add (hasDerivAt_id z)).div ((hasDerivAt_const z 1).sub (hasDerivAt_id z)) hden) using 1
    · rfl
    · simp
      ring
  have h := (((Complex.hasDerivAt_log hslit).comp z hdu).const_mul (-Complex.I)).const_mul ((k⁻¹ : ℝ):ℂ)
  have hd := (h.const_add w₀).deriv
  change deriv (fun v ↦ w₀ + ((k⁻¹ : ℝ):ℂ) * (-Complex.I * Complex.log (u v))) z ≠ 0
  simp only [Function.comp_apply] at hd
  rw [hd]
  exact mul_ne_zero (by exact_mod_cast (inv_ne_zero hk.ne')) (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero)
    (mul_ne_zero (inv_ne_zero hnum) (div_ne_zero two_ne_zero (pow_ne_zero _ hden))))

/-- A positive harmonic function on the unit disk grows at most like the
reciprocal Euclidean distance to the disk boundary. -/
theorem stripReciprocal_disk_harnack (H : ℂ → ℝ) (hH : HarmonicOnNhd H (ball 0 1))
    (hn : ∀ z ∈ ball (0:ℂ) 1, 0 ≤ H z) {z : ℂ} (hz : z ∈ ball 0 1) :
    H z ≤ (4 / (1 - ‖z‖)) * H 0 := by
  let R := (1 + ‖z‖)/2
  have hz' : ‖z‖ < 1 := by simpa [mem_ball] using hz
  have hR : ‖z‖ < R := by dsimp [R]; linarith
  have hR' : R < 1 := by dsimp [R]; linarith
  have hR₀ : 0 < R := (norm_nonneg _).trans_lt hR
  have hzR : z ∈ ball (0 : ℂ) R := by simpa [mem_ball] using hR
  have hrH : HarmonicOnNhd H (closedBall 0 R) := hH.mono (closedBall_subset_ball hR')
  have hC : ContinuousOn H (sphere 0 |R|) := by
    rw [abs_of_pos hR₀]
    exact hrH.continuousOn.mono sphere_subset_closedBall
  let K := Complex.re ∘ herglotzRieszKernel 0 z
  let c := (R + ‖z‖)/(R - ‖z‖)
  have hK : ContinuousOn K (sphere 0 |R|) := by
    apply Complex.continuous_re.comp_continuousOn
    apply continuousOn_herglotzRieszKernel_sphere
    simpa [mem_sphere, abs_of_pos hR₀] using hR.ne
  have hav : circleAverage (K • H) 0 R ≤ circleAverage (c • H) 0 R := by
    apply circleAverage_mono (hK.smul hC).circleIntegrable' (continuousOn_const.smul hC).circleIntegrable'
    intro x hx
    have hx' : x ∈ sphere 0 R := by simpa [abs_of_pos hR₀] using hx
    have hk : K x ≤ c := by simpa [K, c, herglotzRieszKernel_def] using re_herglotzRieszKernel_le hx' hzR
    exact mul_le_mul_of_nonneg_right hk (hn x (sphere_subset_ball hR' hx'))
  have hcc : c ≤ 4/(1 - ‖z‖) := by
    rw [div_le_div_iff₀ (sub_pos.mpr hR) (sub_pos.mpr hz')]
    dsimp [R]
    nlinarith [sq_nonneg (1 - ‖z‖)]
  calc
    H z = _ := (hrH.circleAverage_re_herglotzRieszKernel_smul hzR).symm
    _ ≤ _ := hav
    _ = c * H 0 := by
      rw [circleAverage_smul, InnerProductSpace.HarmonicOnNhd.circleAverage_eq (by simpa [abs_of_pos hR₀] using hrH)]; rfl
    _ ≤ _ := mul_le_mul_of_nonneg_right hcc (hn _ (by simp))

private theorem stripReciprocal_cayley_gap {u : ℂ} (hu : 0 < u.re) :
    (1 - ‖(u - 1)/(u + 1)‖)⁻¹ ≤ (‖u‖ + 1)^2/(2*u.re) := by
  have hu' := synthesis_diskInverseCayley_mem hu
  have hd : u + 1 ≠ 0 := fun h ↦ by have hh := congrArg Complex.re h; simp at hh; linarith
  have hD := norm_pos_iff.mpr hd
  have hsq : ‖u+1‖^2 - ‖u-1‖^2 = 4*u.re := by
    rw [← Complex.normSq_eq_norm_sq,← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.sub_re, Complex.add_im, Complex.sub_im,
      Complex.one_re, Complex.one_im, sub_zero, add_zero]
    ring
  have hp : ‖u+1‖ ≤ ‖u‖+1 := by simpa using norm_add_le u 1
  have hm : ‖u-1‖ ≤ ‖u‖+1 := by simpa using norm_sub_le u 1
  have hdiff : 0 < ‖u+1‖ - ‖u-1‖ := by
    rw [norm_div, div_lt_one hD] at hu'
    linarith
  have hquot : (1 - ‖(u - 1)/(u + 1)‖)⁻¹ = ‖u+1‖ * (‖u+1‖+‖u-1‖)/(4*u.re) := by
    rw [norm_div, show 1 - ‖u-1‖/‖u+1‖ = (‖u+1‖-‖u-1‖)/‖u+1‖ by field_simp, inv_div]
    rw [div_eq_div_iff hdiff.ne' (mul_pos (by norm_num) hu).ne']
    nlinarith [congrArg (‖u+1‖ * ·) hsq]
  rw [hquot, div_le_div_iff₀ (mul_pos (by norm_num) hu) (mul_pos (by norm_num) hu)]
  have hprod : ‖u+1‖ * (‖u+1‖ + ‖u-1‖) ≤ (‖u‖+1) * ((‖u‖+1)+(‖u‖+1)) :=
    mul_le_mul hp (add_le_add hp hm) (add_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)
  nlinarith [mul_le_mul_of_nonneg_right hprod hu.le]

/-- The conformal disk boundary is approached at exponential rate k along each
fixed narrower vertical strip. The lower angular margin enters only as a constant. -/
theorem stripReciprocal_chart_gap (A k d : ℝ) (hk : 0 < k) (hd : 0 ≤ d) (hkd : k*d < π/2)
    (w : ℂ) (hw : |w.re - A| ≤ d) :
    (1 - ‖synthesis_stripBlaschkeToDisk (A : ℂ) k w‖)⁻¹ ≤
      (2 / Real.cos (k*d)) * Real.exp (k*|w.im|) := by
  let t : ℂ := (k : ℂ) * (Complex.I * (w - (A : ℂ)))
  let u := Complex.exp t
  let x := Real.exp (-k*w.im)
  let E := Real.exp (k * |w.im|)
  let b := Real.cos (k*d)
  have hpos : 0 < b := cos_pos_of_mem_Ioo ⟨by linarith [mul_nonneg hk.le hd,pi_pos],hkd⟩
  have hre : t.re = -k*w.im := by simp [t]
  have him : t.im = k*(w.re - A) := by simp [t]
  have hθ : b ≤ Real.cos t.im := by
    rw [← Real.cos_abs t.im]
    apply cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [pi_pos])
    rw [him,abs_mul,abs_of_pos hk]
    exact mul_le_mul_of_nonneg_left hw hk.le
  have hxn : ‖u‖ = x := by simp [u, Complex.norm_exp, hre, x]
  have hure : u.re = x * Real.cos t.im := by simp only [u,Complex.exp_re,hre,x]
  have hx : 0 < x := exp_pos _
  have hu : 0 < u.re := hure ▸ mul_pos hx (hpos.trans_le hθ)
  have h₁e : 1 ≤ E := Real.one_le_exp_iff.mpr (mul_nonneg hk.le (abs_nonneg _))
  have hxe : x ≤ E := by
    apply exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left (neg_le_abs w.im) hk.le]
  have hxi : x⁻¹ ≤ E := by
    dsimp [x]
    rw [← Real.exp_neg]
    apply exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left (le_abs_self w.im) hk.le]
  calc
    _ ≤ (‖u‖+1)^2/(2*u.re) := stripReciprocal_cayley_gap hu
    _ ≤ (x+1)^2/(2*(x*b)) := by
      rw [hxn,hure]
      exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by gcongr)
    _ = (x+2+x⁻¹)/(2*b) := by field_simp; ring
    _ ≤ (4*E)/(2*b) := by gcongr; linarith
    _ = (2 / b)*E := by ring


private theorem stripReciprocal_real_cos (z : ℂ) :
    (Complex.cos z).re = Real.cos z.re * Real.cosh z.im := by
  rw [Complex.cos_eq]
  simp [Complex.mul_re, Complex.cos_ofReal_re]

theorem stripReciprocalCutoff_norm (a c ε : ℝ) (w : ℂ) :
    ‖stripReciprocalCutoff a c ε w‖ =
      Real.exp (-ε * (Real.cos (c*(w.re-a)) * Real.cosh (c*w.im))) := by
  simp [stripReciprocalCutoff,Complex.norm_exp,stripReciprocal_real_cos]

theorem stripReciprocal_iteratedDeriv_estimate {f : ℂ → ℂ} {a r δ q C : ℝ}
    (hδ : 0 < δ) (hq : 0 ≤ q) (hC : 0 ≤ C)
    (hf : AnalyticOnNhd ℂ f {z : ℂ | |z.re-a| ≤ r+δ})
    (hbound : ∀ z : ℂ, |z.re-a| ≤ r+δ → ‖f z‖ ≤ C*Real.exp (-q*|z.im|))
    (n : ℕ) (w : ℂ) (hw : |w.re-a| ≤ r) :
    ‖iteratedDeriv n f w‖ ≤ ((n.factorial : ℝ)*C*Real.exp (q*δ)/δ^n)*Real.exp (-q*|w.im|) := by
  have hstrip : closedBall w δ ⊆ {z : ℂ | |z.re-a| ≤ r+δ} := by
    intro z hz
    have hdist := (Complex.abs_re_le_norm (z-w)).trans (mem_closedBall_iff_norm.mp hz)
    simp only [Complex.sub_re] at hdist
    change |z.re-a| ≤ r+δ
    rw [show z.re-a = (z.re-w.re)+(w.re-a) by ring]
    linarith [abs_add_le (z.re-w.re) (w.re-a)]
  have hcircle (z : ℂ) (hz : z ∈ sphere w δ) : ‖f z‖ ≤ C*Real.exp (q*δ)*Real.exp (-q*|w.im|) := by
    have hdist := (Complex.abs_im_le_norm (z-w)).trans_eq (mem_sphere_iff_norm.mp hz)
    simp only [Complex.sub_im] at hdist
    have him : |w.im| ≤ |z.im|+δ := by
      have hh := abs_sub z.im (z.im-w.im)
      rw [sub_sub_cancel] at hh
      linarith
    apply (hbound z (hstrip (sphere_subset_closedBall hz))).trans
    rw [mul_assoc,←Real.exp_add]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left him hq])) hC
  apply (Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hδ
    (hf.differentiableOn.diffContOnCl_ball hstrip) hcircle).trans_eq
  ring

end RiemannMasullo
end
end
@[expose] public noncomputable section
open Filter Function MeasureTheory Metric Set
open scoped Topology ENNReal SchwartzMap
namespace RiemannMasullo
/-- A uniformly rapidly decaying analytic function on an open vertical strip
gives a Schwartz–Bergman element with its original values throughout that strip. -/
theorem stripBergman_of_exponential_bound (l r : ℝ) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (Complex.re ⁻¹' Ioo l r)) (C : ℝ) (_hC : 0 ≤ C)
    (hb : ∀ z : ℂ, z.re ∈ Ioo l r → ‖f z‖ ≤ C*Real.exp (-|z.im|)) :
    ∃ F : SchwartzBergman (Ioo l r), ∀ z : ℂ, z.re ∈ Ioo l r → F.val z = f z := by
  let U := Complex.re ⁻¹' Ioo l r
  refine ⟨⟨U.indicator f,fun z hz ↦ indicator_of_notMem hz _,?_,?_⟩, fun z hz ↦ indicator_of_mem (show z ∈ U from hz) _⟩
  · exact hf.differentiableOn.congr (fun z hz ↦ indicator_of_mem hz _)
  · intro a b _hab hab N
    let D := max |a| |b|
    refine ⟨(N.factorial : ℝ)*Real.exp D*C,?_⟩
    rintro _ ⟨z,hz,rfl⟩
    have hz' : z.re ∈ Icc a b := hz
    have hvr : |z.re| ≤ D := abs_le_max_abs_abs hz'.1 hz'.2
    have hnorm : ‖z‖ ≤ D+|z.im| := (Complex.norm_le_abs_re_add_abs_im z).trans (by linarith)
    have hfac := (div_le_iff₀ (show 0 < (N.factorial : ℝ) by positivity)).mp
      (Real.pow_div_factorial_le_exp ‖z‖ (norm_nonneg z) N)
    have hpow : ‖z‖^N ≤ ((N.factorial : ℝ)*Real.exp D)*Real.exp |z.im| := by
      rw [mul_assoc,←Real.exp_add,mul_comm]
      exact hfac.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hnorm) (by positivity))
    change ‖z^N*U.indicator f z‖ ≤ _
    rw [indicator_of_mem (show z ∈ U from hab hz') _,norm_mul,norm_pow]
    calc
      _ ≤ (((N.factorial : ℝ)*Real.exp D)*Real.exp |z.im|) * (C*Real.exp (-|z.im|)) :=
        mul_le_mul hpow (hb _ (hab hz')) (norm_nonneg _) (by positivity)
      _ = _ := by rw [Real.exp_neg]; field_simp

/-- A bounded analytic multiplier preserves the Schwartz–Bergman test space
on a smaller strip on which the test function is defined. -/
theorem stripBergman_bounded_mul {I J : Set ℝ} (h : J ⊆ I)
    (f : SchwartzBergman I) (P : ℂ → ℂ)
    (hP : AnalyticOnNhd ℂ P (Complex.re ⁻¹' J)) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ z : ℂ, z.re ∈ J → ‖P z‖ ≤ C) :
    ∃ F : SchwartzBergman J, ∀ z : ℂ, z.re ∈ J → F.val z = P z * f.val z := by
  let U := Complex.re ⁻¹' J
  let g (z : ℂ) := P z*f.val z
  refine ⟨⟨U.indicator g,fun z hz ↦ indicator_of_notMem hz _,?_,?_⟩,fun z hz ↦ indicator_of_mem (show z ∈ U from hz) _⟩
  · exact (hP.differentiableOn.mul (f.property.2.1.mono (preimage_mono h))).congr (fun z hz ↦ indicator_of_mem hz _)
  · intro a b hab habJ N
    obtain ⟨D,hD⟩ := f.property.2.2 a b hab (habJ.trans h) N
    refine ⟨C*D,?_⟩
    rintro _ ⟨z,hz,rfl⟩
    have hzm := habJ hz
    change ‖z^N*U.indicator g z‖ ≤ _
    rw [indicator_of_mem (show z ∈ U from hzm) _]
    change ‖z^N*(P z*f.val z)‖ ≤ _
    rw [mul_left_comm,norm_mul]
    exact mul_le_mul (hb z hzm) (hD ⟨z,hz,rfl⟩) (norm_nonneg _) hC


/-- A pointwise-convergent, uniformly bounded family of multipliers multiplies a
fixed Schwartz–Bergman test convergently in the full strip test topology. -/
theorem stripBergman_tendsto_of_dominated {I : Set ℝ} (Y : SchwartzBergman I)
    (F : ℕ → SchwartzBergman I) (C : ℝ) (_hC : 0 ≤ C)
    (hdom : ∀ n (z : ℂ), z.re ∈ I → ‖(F n).val z-Y.val z‖ ≤ C*‖Y.val z‖)
    (hcv : ∀ z : ℂ, z.re ∈ I → Tendsto (fun n ↦ (F n).val z) atTop (𝓝 (Y.val z))) :
    Tendsto F atTop (𝓝 Y) := by
  let P : I × ℕ → Seminorm ℂ (SchwartzBergman I) := fun i ↦ Seminorm.of
    (fun f : schwartzBergmanSubmodule I ↦ (eLpNorm (weightedVerticalTrace i.1 i.2 f.val) 2 volume).toReal)
    (schwartzBergman_l2_seminorm I i).1 (schwartzBergman_l2_seminorm I i).2
  have hP : WithSeminorms P := withGeneratingSeminorms_spec (schwartzBergmanSubmodule I) _
  apply (hP.tendsto_nhds F Y).mpr
  rintro ⟨a,N⟩ ε hε
  let z (t : ℝ) := (a.val:ℂ)+(t:ℂ)*Complex.I
  have hz (t : ℝ) : (z t).re ∈ I := by simp [z]
  let u (t : ℝ) := weightedVerticalTrace a.val N Y.val t
  let d (n : ℕ) (t : ℝ) := weightedVerticalTrace a.val N (F n-Y).val t
  have hu : MemLp u 2 volume := schwartzBergman_trace_memLp I a 2 (by norm_num) (by norm_num) N Y
  have hd (n : ℕ) : MemLp (d n) 2 volume := schwartzBergman_trace_memLp I a 2 (by norm_num) (by norm_num) N (F n-Y)
  have hdlim (t : ℝ) : Tendsto (fun n ↦ d n t) atTop (𝓝 0) := by
    have h := ((hcv _ (hz t)).sub_const (Y.val (z t))).const_mul ((z t)^N)
    change Tendsto (fun n ↦ z t ^ N*((F n).val (z t)-Y.val (z t))) atTop (𝓝 0)
    simpa only [sub_self,mul_zero] using h
  have hdb (n : ℕ) (t : ℝ) : ‖d n t‖ ≤ C*‖u t‖ := by
    change ‖z t ^ N*((F n).val (z t)-Y.val (z t))‖ ≤ C*‖(z t)^N*Y.val (z t)‖
    rw [norm_mul,norm_mul,mul_left_comm C]
    exact mul_le_mul_of_nonneg_left (hdom n _ (hz t)) (norm_nonneg _)
  have hint : Integrable (fun t ↦ C^2*‖u t‖^2) volume :=
    (hu.integrable_norm_pow (by norm_num : 2 ≠ 0)).const_mul _
  have hsq : Tendsto (fun n ↦ ∫ t, ‖d n t‖^2) atTop (𝓝 0) := by
    have hh := tendsto_integral_of_dominated_convergence (μ := (volume : Measure ℝ))
      (F := fun n t ↦ ‖d n t‖^2) (f := fun _ ↦ (0:ℝ)) (fun t ↦ C^2*‖u t‖^2)
      (fun n ↦ (hd n).aestronglyMeasurable.norm.pow 2) hint
      (fun n ↦ .of_forall fun t ↦ by
        rw [Real.norm_of_nonneg (sq_nonneg _),←mul_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (hdb n t) 2)
      (.of_forall fun t ↦ by simpa using (hdlim t).norm.pow 2)
    simpa using hh
  have heq (n : ℕ) : P (a,N) (F n - Y) = (∫ t, ‖d n t‖ ^ 2) ^ ((2:ℝ)⁻¹) := by
    change (eLpNorm (d n) 2 volume).toReal = _
    rw [toReal_eLpNorm,lpNorm_eq_integral_norm_rpow_toReal
      (by norm_num : (2:ℝ≥0∞) ≠ 0) (by norm_num) (hd n).aestronglyMeasurable]
    simp
  have hpow : Tendsto (fun n ↦ P (a,N) (F n-Y)) atTop (𝓝 0) := by
    simp_rw [heq]
    simpa using (hsq.rpow_const (Or.inr (by norm_num : 0 ≤ (2:ℝ)⁻¹)))
  exact (tendsto_order.mp hpow).2 ε hε


/-- Inside an arbitrary buffered strip, the tail times an entire test is the
Mellin transform of an exponential test approximated in the full test topology
by multiples of the chosen generator. The multipliers themselves are actual
inverse-Mellin exponential tests on the same buffered strip. -/
theorem stripBergman_regularized_mellin_division (A k c r : ℝ)
    (hk : 0 < k) (hkc : k < c) (hr : 0 < r) (hwide : k*(|0-A|+r) < Real.pi/2)
    (hcr : c*r < Real.pi/2) (G T Q N : ℂ → ℂ) (H : SchwartzBergman (univ : Set ℝ))
    (hT : AnalyticOnNhd ℂ T {w : ℂ | |w.re-A| < (Real.pi/2)/k})
    (hQ : AnalyticOnNhd ℂ Q {w : ℂ | |w.re-A| < (Real.pi/2)/k})
    (hN : AnalyticOnNhd ℂ N {w : ℂ | |w.re-A| < (Real.pi/2)/k})
    (hQn : ∀ z : ℂ, |z.re-A| < (Real.pi/2)/k → Q z ≠ 0)
    (M L : ℝ) (hL : 0 ≤ L)
    (htb : ∀ z : ℂ, |z.re-A| < (Real.pi/2)/k → ‖T z‖ ≤ 1)
    (hqb : ∀ z : ℂ, |z.re-A| < (Real.pi/2)/k → ‖Q z‖ ≤ M)
    (hnb : ∀ z : ℂ, |z.re-A| < (Real.pi/2)/k → ‖N z‖ ≤ L)
    (heq : ∀ z : ℂ, |z.re-A| < (Real.pi/2)/k → T z*H.val z = G z * (N z/Q z)) :
    let J := Ioo (-r) r
    ∃ y : PositiveRealExponentialDecay J,
      (∀ z : ℂ, z.re ∈ J → mellin (fun x ↦ y.val (Real.log x)) z = T z*H.val z) ∧
      ∃ k' v : ℕ → PositiveRealExponentialDecay J, Tendsto v atTop (𝓝 y) ∧
        ∀ n (z : ℂ), z.re ∈ J → mellin (fun x ↦ (v n).val (Real.log x)) z =
          G z * mellin (fun x ↦ (k' n).val (Real.log x)) z := by
  intro J
  let U := {w : ℂ | |w.re-A| < (Real.pi/2)/k}
  have hsub : Complex.re ⁻¹' J ⊆ U := by
    intro z hz
    have hj : |z.re| < r := abs_lt.mpr hz
    have hb : |z.re-A| ≤ |z.re|+|0-A| := by simpa using abs_sub z.re A
    apply (lt_div_iff₀ hk).mpr
    nlinarith [mul_le_mul_of_nonneg_left hb hk.le,mul_lt_mul_of_pos_left hj hk]
  have hrad (z : ℂ) (hz : z.re ∈ J) : |z.re-0| ≤ r := by simpa using (abs_lt.mpr hz).le
  have hc := hk.trans hkc
  let e (n : ℕ) : ℝ := 1/(n+1)
  have he (n : ℕ) : 0 < e n := by dsimp [e]; positivity
  let V (n : ℕ) := stripReciprocalCutoff 0 c (e n)
  have hV (n : ℕ) : AnalyticOnNhd ℂ (V n) (Complex.re ⁻¹' J) := fun z _ ↦ stripReciprocalCutoff_analytic ..
  have hVb (n : ℕ) (z : ℂ) (hz : z.re ∈ J) : ‖V n z‖ ≤ 1 :=
    stripReciprocalCutoff_norm_le_one 0 c r (e n) hc hr.le hcr (he n).le z (hrad z hz)
  obtain ⟨Y,hY⟩ := stripBergman_bounded_mul (J := J) (subset_univ _) H T (hT.mono hsub) 1 zero_le_one
    (fun z hz ↦ htb z (hsub hz))
  choose VY hVY using fun n ↦ stripBergman_bounded_mul (J := J) subset_rfl Y (V n) (hV n) 1 zero_le_one (hVb n)
  have hconv : Tendsto VY atTop (𝓝 Y) := by
    apply stripBergman_tendsto_of_dominated Y VY 2 (by norm_num)
    · intro n z hz
      rw [hVY n z hz,←sub_one_mul,norm_mul]
      exact mul_le_mul_of_nonneg_right ((norm_sub_le _ _).trans (by rw [norm_one]; linarith [hVb n z hz])) (norm_nonneg _)
    · intro z hz
      have ht := (stripReciprocalCutoff_tendsto_compact 0 c {z} isCompact_singleton).tendsto_at (mem_singleton z)
      have hn : Tendsto (fun n ↦ V n z) atTop (𝓝 1) := ht.comp tendsto_one_div_add_atTop_nhds_zero_nat
      simp_rw [hVY _ z hz]
      simpa using hn.mul_const (Y.val z)
  have hK (n : ℕ) : ∃ K : SchwartzBergman J, ∀ z : ℂ, z.re ∈ J → K.val z = (V n z/Q z)*N z := by
    obtain ⟨C,hC,hb⟩ := stripReciprocal_regularized_decay A 0 k c r (e n) hk hkc hr.le hwide hcr (he n)
      Q hQ hQn M hqb 1 zero_le_one
    refine stripBergman_of_exponential_bound (-r) r _ ((stripReciprocal_regularized_analytic A 0 k c (e n) Q hQ hQn
      |>.mono hsub).mul (hN.mono hsub)) (C*L) (mul_nonneg hC.le hL) ?_
    intro z hz
    rw [norm_mul]
    have h₁ := hb z (hrad z hz)
    calc
      _ ≤ (C*Real.exp (-1*|z.im|))*L := mul_le_mul h₁ (hnb z (hsub hz)) (norm_nonneg _) (by positivity)
      _ = _ := by rw [neg_one_mul]; ring
  choose K hK' using hK
  have hne : J.Nonempty := nonempty_Ioo.mpr (by linarith)
  let M' := positiveRealFourierMellin J isOpen_Ioo (ordConnected_Ioo) hne
  have hM' (F : SchwartzBergman J) (z : ℂ) (hz : z.re ∈ J) :
      mellin (fun x ↦ (M'.symm F).val (Real.log x)) z = F.val z := by
    rw [←positiveRealFourierMellin_apply J isOpen_Ioo (ordConnected_Ioo) hne _ z hz]
    exact congrArg (fun v : SchwartzBergman J ↦ v.val z) (M'.apply_symm_apply F)
  refine ⟨M'.symm Y,fun z hz ↦ (hM' _ _ hz).trans (hY z hz),fun n ↦ M'.symm (K n),
    fun n ↦ M'.symm (VY n),(M'.symm.continuous.tendsto Y).comp hconv,?_⟩
  intro n z hz
  rw [hM' _ _ hz,hM' _ _ hz,hVY n z hz,hY z hz,heq z (hsub hz),hK' n z hz]
  ring


private theorem synthesis_stripBlaschkeToDisk_analytic {w₀ w : ℂ} {k : ℝ} (hk : 0 < k)
    (hw : |w.re - w₀.re| < (Real.pi / 2) / k) : AnalyticAt ℂ (synthesis_stripBlaschkeToDisk w₀ k) w := by
  let E (z : ℂ) := Complex.exp ((k : ℂ) * (Complex.I * (z - w₀)))
  have hE : AnalyticAt ℂ E w :=
    (analyticAt_const.mul (analyticAt_const.mul (analyticAt_id.sub analyticAt_const))).cexp
  have hr : 0 < (E w).re := by
    rw [show (E w).re = _ from Complex.exp_re _]
    exact mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo (abs_lt.mp (synthesis_stripBlaschke_phase hk hw)))
  exact (hE.sub analyticAt_const).div (hE.add analyticAt_const) (fun h ↦ by
    have he := congrArg Complex.re h
    change (E w + 1).re = 0 at he
    simp only [Complex.add_re, Complex.one_re] at he
    linarith)

/-- The normalized complementary tail of the actual zeros of one strip generator
takes any entire test killing the finitely many excluded multiplicities to the
closure, in the exponential test topology, of products by that generator. -/
theorem stripBergman_single_generator_finite_jets (A k c r : ℝ)
    (hk : 0 < k) (hkc : k < c) (hr : 0 < r) (hwide : k*(|0-A|+r) < Real.pi/2)
    (hcr : c*r < Real.pi/2) (G : ℂ → ℂ)
    (hG : AnalyticOnNhd ℂ G {w : ℂ | |w.re-A| < (Real.pi/2)/k})
    (hG₀ : G (A:ℂ) ≠ 0) (M : ℝ) (hb : ∀ z : ℂ, |z.re-A| < (Real.pi/2)/k → ‖G z‖ ≤ M) :
    let D := synthesis_stripBlaschkeFromDisk (A:ℂ) k
    let B := synthesis_stripBlaschkeToDisk (A:ℂ) k
    let Z := {z : ℂ // z ∈ ball 0 1 ∧ G (D z) = 0}
    let a (i : Z) := i.val
    let m (i : Z) := analyticOrderNatAt G (D i.val)
    let J := Ioo (-r) r
    ∀ (S : Finset Z) (H : SchwartzBergman (univ : Set ℝ)),
      (∀ i ∈ S, (m i : ℕ∞) ≤ analyticOrderAt H.val (D i.val)) →
      ∃ y : PositiveRealExponentialDecay J,
        (∀ z : ℂ, z.re ∈ J → mellin (fun x ↦ y.val (Real.log x)) z = DiskTails.diskBlaschkeTail a m S (B z)*H.val z) ∧
        ∃ K v : ℕ → PositiveRealExponentialDecay J, Tendsto v atTop (𝓝 y) ∧
          ∀ n (z : ℂ), z.re ∈ J → mellin (fun x ↦ (v n).val (Real.log x)) z =
            G z*mellin (fun x ↦ (K n).val (Real.log x)) z := by
  intro D B Z a m J S H hHjets
  let U := {w : ℂ | |w.re-A| < (Real.pi/2)/k}
  let Gd := G ∘ D
  let Hd := H.val ∘ D
  have hD (z : ℂ) (hz : z ∈ ball 0 1) : D z ∈ U := synthesis_stripBlaschkeFromDisk_mem hk hz
  have hB (z : ℂ) (hz : z ∈ U) : B z ∈ ball 0 1 := synthesis_stripBlaschkeToDisk_mem hk hz
  have hBa (z : ℂ) (hz : z ∈ U) : AnalyticAt ℂ B z := synthesis_stripBlaschkeToDisk_analytic hk hz
  have hlog (z : ℂ) (hz : z ∈ U) : D (B z) = z := synthesis_stripBlaschkeFromDisk_toDisk hk hz
  have hGd : AnalyticOnNhd ℂ Gd (ball 0 1) := fun z hz ↦ (hG _ (hD z hz)).comp (synthesis_stripBlaschkeFromDisk_analytic_deriv hk hz).1
  have hHent : AnalyticOnNhd ℂ H.val univ :=
    (show DifferentiableOn ℂ H.val univ by simpa only [preimage_univ] using H.property.2.1).analyticOnNhd isOpen_univ
  have hHd : AnalyticOnNhd ℂ Hd (ball 0 1) := fun z hz ↦ (hHent _ (mem_univ _)).comp (synthesis_stripBlaschkeFromDisk_analytic_deriv hk hz).1
  have h₀ : Gd 0 ≠ 0 := by simpa [Gd,D,synthesis_stripBlaschkeFromDisk] using hG₀
  have ha (i : Z) : a i ≠ 0 := by
    intro ha
    have hi : Gd (a i) = 0 := i.property.2
    exact h₀ (ha ▸ hi)
  have ha' (i : Z) : ‖a i‖ < 1 := mem_ball_zero_iff.mp i.property.1
  have hcnt (i : Z) : analyticOrderAt Gd (a i) = m i := by
    have h := synthesis_stripBlaschkeFromDisk_analytic_deriv (w₀ := (A:ℂ)) hk i.property.1
    have hc : analyticOrderAt Gd (a i) = analyticOrderAt G (D i.val) := analyticOrderAt_comp_of_deriv_ne_zero h.1 h.2
    have hfin := hGd.analyticOrderAt_ne_top_of_isPreconnected (convex_ball (0:ℂ) 1).isPreconnected
      (x := 0) (by simp) i.property.1 (by rw [(hGd 0 (by simp)).analyticOrderAt_eq_zero.mpr h₀]; simp)
    exact hc.trans (Nat.cast_analyticOrderNatAt (hc ▸ hfin)).symm
  have hsum : Summable (fun i ↦ (m i : ℝ)*(1-‖a i‖)) := by
    have h := (synthesis_disk_divisor_summable_one_sub_norm hGd h₀ (fun z hz ↦ hb _ (hD z hz))).subtype
      (fun z ↦ z ∈ ball (0:ℂ) 1 ∧ G (D z) = 0)
    apply h.congr
    intro i
    change (MeromorphicOn.divisor Gd (ball 0 1) i.val : ℝ)*(1-‖i.val‖) = _
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hGd i.property.1,show analyticOrderAt Gd i.val = m i from hcnt i]
    simp [a]
  obtain ⟨Q,hQ,hn,hQb,hdiv⟩ := DiskTails.exists_tail_test_quotient a m Subtype.val_injective ha ha'
    hsum Gd hGd hcnt (fun z hz he ↦ ⟨⟨z,hz,he⟩,rfl⟩) M (fun z hz ↦ hb _ (hD z hz))
  let R := (Real.pi/2)/k
  have hR : 0 < R := by dsimp [R]; positivity
  obtain ⟨L,hLb⟩ := H.property.2.2 (A-R) (A+R) (by linarith) (subset_univ _) 0
  have hHdBound (z : ℂ) (hz : z ∈ ball 0 1) : ‖Hd z‖ ≤ L := by
    have hz' : |(D z).re-A| < R := hD z hz
    have hwin : (D z).re ∈ Icc (A-R) (A+R) := ⟨by linarith [(abs_lt.mp hz').1],by linarith [(abs_lt.mp hz').2]⟩
    simpa [Hd] using hLb ⟨D z,hwin,rfl⟩
  have hj (i) (hi : i ∈ S) : (m i : ℕ∞) ≤ analyticOrderAt Hd (a i) := by
    have h := synthesis_stripBlaschkeFromDisk_analytic_deriv (w₀ := (A:ℂ)) hk i.property.1
    change _ ≤ analyticOrderAt (H.val ∘ D) i.val
    rw [analyticOrderAt_comp_of_deriv_ne_zero h.1 h.2]
    exact hHjets i hi
  obtain ⟨N,hN,hNb,hrel⟩ := hdiv S Hd hHd hj L hHdBound
  let T := DiskTails.diskBlaschkeTail a m S
  have hTa : AnalyticOnNhd ℂ T (ball 0 1) := DiskTails.product_analytic
    (fun i : {j // j ∉ S} ↦ a i.val) (fun i ↦ m i.val) (fun i ↦ ha _) (fun i ↦ ha' _) (hsum.subtype _)
  have hTb (z : ℂ) (hz : z ∈ ball 0 1) : ‖T z‖ ≤ 1 := (DiskTails.product_bound
    (fun i : {j // j ∉ S} ↦ a i.val) (fun i ↦ m i.val) (fun i ↦ ha _) (fun i ↦ ha' _)
    (hsum.subtype _) z (mem_ball_zero_iff.mp hz)).1
  apply stripBergman_regularized_mellin_division A k c r hk hkc hr hwide hcr G (T ∘ B) (Q ∘ B) (N ∘ B) H
    (fun z hz ↦ (hTa _ (hB z hz)).comp (hBa z hz)) (fun z hz ↦ (hQ _ (hB z hz)).comp (hBa z hz))
    (fun z hz ↦ (hN _ (hB z hz)).comp (hBa z hz)) (fun z hz ↦ hn _ (hB z hz))
    M L ((norm_nonneg _).trans (hHdBound 0 (by simp))) (fun z hz ↦ hTb _ (hB z hz))
    (fun z hz ↦ hQb _ (hB z hz)) (fun z hz ↦ hNb _ (hB z hz))
  intro z hz
  simpa only [T,Hd,Gd,Function.comp_apply,hlog z hz] using hrel _ (hB z hz)


end RiemannMasullo

end

@[expose] public noncomputable section


open Filter Function MeasureTheory NumberField Set
open scoped Topology
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false

variable {F : Type*} [Field F] [NumberField F]

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" =>
  (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "logNorm" => (fun g : C𝔽 ↦ Real.log ((ideleClassNorm F g).val : ℝ))
local notation "W(" l ", " r ", " s ")" => CompactIntervalSobolev μ𝔽 logNorm l r s
local notation "W'(" l ", " r ", " s ")" => CompactIntervalSobolev μ𝔽 logNorm l r s true
local notation "Θ(" a ", " hI ", " hs ")" => globalThetaSobolev F a hI hs
local notation "ρ(" l ", " r ", " s ", " hI ", " hs ")" =>
  (hardySobolevTranslation μ𝔽 m𝔽 l r s hI hs).comp (ideleClassNorm F).ker.subtype
local notation "Wω(" hI ", " hs ", " ω ")" => actionIsotype (ρ(_, _, _, hI, hs)) ω
local notation "restriction" =>
  (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁ →ₜ* C𝔽)

local notation "hm𝔽" => (⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ :
  IsModulation m𝔽)
local notation "hms𝔽" => (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.2.2.2.1


open scoped SchwartzMap
local notation "nuTheta" => canonicalModulatedHaar m𝔽 hm𝔽
local notation "rad(" χ ", " u ")" => (fun x : C𝔽 ↦ ((χ⁻¹ x : Circle) : ℂ) * u (logNorm x))
local instance thetaStripCanonicalHaar : (nuTheta : Measure C𝔽).IsHaarMeasure :=
  (existsUnique_canonicalModulatedHaar m𝔽 hm𝔽).exists.choose_spec.1

/-- The polynomial factor in the translation bound is absorbed by the available
extra width. This gives a weighted L¹ norm for every inverse Mellin kernel. -/
theorem stripTheta_radial_weight_integrable (J : Set ℝ) (α s : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s)
    (hzero : 0 ∈ J) (hneg : -(α+s/2) ∈ J) (hpos : α+s/2 ∈ J)
    (p : PositiveRealExponentialDecay J) :
    Integrable (fun t : ℝ ↦ ‖p.val t‖*(max (Real.exp (-α*t)) (Real.exp (α*t))*(1+|t|)^(s/2))) volume := by
  let b := α+s/2
  let P := logExponentialDecayTwist J ⟨b,hpos⟩ p
  let N := logExponentialDecayTwist J ⟨-b,hneg⟩ p
  have hpn (t : ℝ) : ‖P t‖ = Real.exp (b*t)*‖p.val t‖ := by
    rw [show P t = _ from logExponentialDecayTwist_apply J ⟨b,hpos⟩ p t,norm_mul]
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  have hnn (t : ℝ) : ‖N t‖ = Real.exp (-b*t)*‖p.val t‖ := by
    rw [show N t = _ from logExponentialDecayTwist_apply J ⟨-b,hneg⟩ p t,norm_mul]
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  have hcont : Continuous p.val := by
    refine (logExponentialDecayTwist J ⟨0,hzero⟩ p).continuous.congr ?_
    intro x
    simpa using logExponentialDecayTwist_apply J ⟨0,hzero⟩ p x
  have hm : Continuous (fun t : ℝ ↦ ‖p.val t‖*(max (Real.exp (-α*t)) (Real.exp (α*t))*(1+|t|)^(s/2))) := by
    have hpow : Continuous (fun t : ℝ ↦ (1+|t|)^(s/2)) := (continuous_const.add continuous_id.abs).rpow_const
      (fun t : ℝ ↦ Or.inl (ne_of_gt (by positivity : 0 < 1+|t|)))
    exact hcont.norm.mul (((Real.continuous_exp.comp (continuous_const.mul continuous_id)).max
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))).mul hpow)
  apply (P.integrable.norm.add N.integrable.norm).mono' hm.aestronglyMeasurable
  filter_upwards with t
  have ht : 0 < 1+|t| := by positivity
  have hL : Real.log (1+|t|) ≤ |t| := by linarith [Real.log_le_sub_one_of_pos ht]
  have hpow : (1+|t|)^(s/2) ≤ Real.exp ((s/2)*|t|) := by
    rw [Real.rpow_def_of_pos ht,Real.exp_le_exp]
    nlinarith [mul_le_mul_of_nonneg_right hL (show 0 ≤ s/2 by positivity)]
  have hmax : max (Real.exp (-α*t)) (Real.exp (α*t)) ≤ Real.exp (α*|t|) :=
    max_le (Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left (neg_le_abs t) hα]))
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_abs_self t) hα))
  have hm : max (Real.exp (-α*t)) (Real.exp (α*t))*(1+|t|)^(s/2) ≤ Real.exp (b*|t|) := by
    calc
      _ ≤ Real.exp (α*|t|)*Real.exp ((s/2)*|t|) := mul_le_mul hmax hpow (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le
      _ = _ := by rw [←Real.exp_add]; congr 1; dsimp [b]; ring
  rw [Real.norm_of_nonneg (by positivity),Pi.add_apply,hpn,hnn]
  apply (mul_le_mul_of_nonneg_left hm (norm_nonneg _)).trans
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht]
    nlinarith [mul_nonneg (Real.exp_pos (-b*t)).le (norm_nonneg (p.val t))]
  · rw [abs_of_nonpos ht,show b*(-t) = -b*t by ring]
    nlinarith [mul_nonneg (Real.exp_pos (b*t)).le (norm_nonneg (p.val t))]


private theorem stripTheta_log_integrable {E : Type*} [NormedAddCommGroup E] {p : ℝ → E}
    (hp : Integrable p volume) : Integrable (fun x : C𝔽 ↦ p (logNorm x)) μ𝔽 := by
  have hl := sobolev_log_preserving m𝔽 hm𝔽 hms𝔽
  have h : Integrable (fun x : C𝔽 ↦ p (logNorm x)) nuTheta := hl.integrable_comp_of_integrable hp
  rw [Measure.isMulLeftInvariant_eq_smul μ𝔽 nuTheta]
  exact h.smul_measure_nnreal

private theorem stripTheta_radial_continuous {J : Set ℝ} (h0 : 0 ∈ J) (χ : PontryaginDual C𝔽)
    (p : PositiveRealExponentialDecay J) : Continuous rad(χ, p.val) := by
  have hc : Continuous p.val := by
    refine (logExponentialDecayTwist J ⟨0,h0⟩ p).continuous.congr ?_
    intro x
    simpa using logExponentialDecayTwist_apply J ⟨0,h0⟩ p x
  have hg : Continuous logNorm := (NNReal.continuous_coe.comp (Units.continuous_val.comp
    (m𝔽).continuous)).log fun x ↦ NNReal.coe_ne_zero.2 (m𝔽 x).ne_zero
  exact (continuous_subtype_val.comp χ⁻¹.continuous).mul (hc.comp hg)

private theorem stripTheta_radial_integrable {J : Set ℝ} (h0 : 0 ∈ J) (χ : PontryaginDual C𝔽)
    (p : PositiveRealExponentialDecay J) : Integrable rad(χ, p.val) μ𝔽 := by
  have hi : Integrable p.val volume := (logExponentialDecayTwist J ⟨0,h0⟩ p).integrable.congr
    (.of_forall fun x ↦ by simpa using logExponentialDecayTwist_apply J ⟨0,h0⟩ p x)
  apply (stripTheta_log_integrable (F := F) hi.norm).mono' (stripTheta_radial_continuous h0 χ p).aestronglyMeasurable
  exact .of_forall fun x ↦ by simp only [norm_mul,Circle.norm_coe,one_mul]; exact le_rfl

private theorem stripTheta_bounded_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (c q : ℂ) (hc : ‖c‖ = 1) (T : E →L[ℂ] E) (C : ℝ) (hT : ‖T‖ ≤ C) (u : E) :
    ‖(c*q) • T u‖ ≤ ‖q‖*C*‖u‖ := by
  rw [norm_smul,norm_mul,hc,one_mul,mul_assoc]
  exact mul_le_mul_of_nonneg_left ((T.le_opNorm u).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg u))) (norm_nonneg _)

private theorem stripTheta_radial_orbit_integrable {J : Set ℝ} (h0 : 0 ∈ J) (α s : ℝ)
    (hα : 0 ≤ α) (hs : 0 ≤ s) (hneg : -(α+s/2) ∈ J) (hpos : α+s/2 ∈ J)
    (χ : PontryaginDual C𝔽) (p : PositiveRealExponentialDecay J) (u : W(-α, α, s)) :
    let τ := hardySobolevTranslation μ𝔽 m𝔽 (-α) α s (neg_le_self hα) hs
    Integrable (fun g ↦ rad(χ, p.val) g • τ g u) μ𝔽 := by
  intro τ
  have hweight := stripTheta_log_integrable (F := F) (stripTheta_radial_weight_integrable J α s hα hs h0 hneg hpos p)
  have ht : Continuous (fun g ↦ τ g u) :=
    (exists_hardySobolevTranslation μ𝔽 m𝔽 (-α) α s (neg_le_self hα) hs).choose_spec.2.comp (Continuous.prodMk_left u)
  apply (hweight.mul_const ‖u‖).mono' ((stripTheta_radial_continuous h0 χ p).smul ht).aestronglyMeasurable
  refine .of_forall fun g ↦ ?_
  exact stripTheta_bounded_smul (χ⁻¹ g : ℂ) (p.val (logNorm g)) (Circle.norm_coe _)
    (τ g) _ (norm_hardySobolevTranslation_le μ𝔽 m𝔽 (-α) α s (neg_le_self hα) hs g) u


private theorem stripTheta_orbit_integral (a b s : ℝ) (hab : a ≤ b) (hs : 0 ≤ s)
    {φ : C𝔽 → ℂ} (hi : Integrable φ μ𝔽) (u : W(a, b, s))
    (horb : Integrable (fun g ↦ φ g • hardySobolevTranslation μ𝔽 m𝔽 a b s hab hs g u) μ𝔽) :
    let τ := hardySobolevTranslation μ𝔽 m𝔽 a b s hab hs
    ∀ᵐ x ∂μ𝔽, Integrable (fun g ↦ φ g * u (g⁻¹ * x)) μ𝔽 ∧
      (∫ g, φ g • τ g u ∂μ𝔽) x = lcaConvolution μ𝔽 φ u x := by
  intro τ
  let d (x : C𝔽) := ENNReal.ofReal (intervalSobolevDensity a b s (logNorm x))
  let ν := (μ𝔽).withDensity d
  have hν : ν ≪ μ𝔽 := withDensity_absolutelyContinuous μ𝔽 d
  have hd : Measurable d := by
    have hlog : Measurable (fun x : C𝔽 ↦ Real.log ((m𝔽 x).val : ℝ)) := Real.measurable_log.comp
      (NNReal.continuous_coe.comp (Units.continuous_val.comp (m𝔽).continuous)).measurable
    have hD : Measurable (intervalSobolevDensity a b s) := by unfold intervalSobolevDensity; fun_prop
    exact (hD.comp hlog).ennreal_ofReal
  have hμ : μ𝔽 ≪ ν := withDensity_absolutelyContinuous' hd.aemeasurable
    (.of_forall fun x ↦ (ENNReal.ofReal_pos.mpr (mul_pos (lt_max_of_lt_left (Real.exp_pos _))
      (Real.rpow_pos_of_pos (by positivity) _))).ne')
  have : SigmaFinite ν := MeasureTheory.SigmaFinite.withDensity_ofReal _
  have hmeas : AEStronglyMeasurable (fun p : C𝔽 × C𝔽 ↦ φ p.1 * u (p.1⁻¹ * p.2)) ((μ𝔽).prod ν) :=
    hi.1.comp_fst.mul ((Lp.stronglyMeasurable u).comp_measurable
      (measurable_fst.inv.mul measurable_snd)).aestronglyMeasurable
  apply hμ.ae_le
  apply integral_L2_representative horb hmeas
  refine .of_forall fun g ↦ ?_
  filter_upwards [Lp.coeFn_smul (φ g) (τ g u),
    hν.ae_le (hardySobolevTranslation_apply μ𝔽 m𝔽 a b s hab hs g u)] with x hx hy
  rw [hx, Pi.smul_apply, hy, smul_eq_mul]



/-- The physical radial lift is continuous into the Tamagawa weighted strip space. -/
theorem stripTheta_test_lift (χ : PontryaginDual C𝔽) (l r s : ℝ)
    (hlr : l ≤ r) (hs : 0 ≤ s) (J : Set ℝ) (hJ : IsOpen J) (hint : OrdConnected J)
    (hsub : Icc l r ⊆ J) :
    ∃ R : PositiveRealExponentialDecay J →L[ℂ] W(l, r, s),
      ∀ p, (R p : C𝔽 → ℂ) =ᵐ[μ𝔽] rad(χ, p.val) := by
  let E := globalThetaAmbient_equiv_canonical (F := F) hm𝔽 l r s
  let B := E.choose
  let L := exists_modulatedIntervalSobolev_characterLogPullback m𝔽 hm𝔽 hms𝔽 χ⁻¹ l r s
  let T := B.symm.toContinuousLinearMap.comp L.choose
  let j := scalarIntervalSobolev_dense l r s hlr hs J hJ hint hsub
  refine ⟨T.comp j.choose,fun p ↦ ?_⟩
  have hE := (E.choose_spec (T (j.choose p))).1.symm
  have hB : B (T (j.choose p)) = L.choose (j.choose p) := B.apply_symm_apply _
  have hb : (B (T (j.choose p)) : C𝔽 → ℂ) =ᵐ[μ𝔽] (L.choose (j.choose p) : C𝔽 → ℂ) :=
    .of_forall fun g ↦ congrArg (fun v : ModulatedIntervalSobolev m𝔽 hm𝔽 l r s ↦ v g) hB
  have hj := (sobolev_log_preserving m𝔽 hm𝔽 hms𝔽).quasiMeasurePreserving.ae_eq_comp (j.choose_spec.2.2 p)
  have heq := (Measure.absolutelyContinuous_isHaarMeasure μ𝔽 nuTheta).ae_eq (L.choose_spec.1 (j.choose p))
  have heq' := (Measure.absolutelyContinuous_isHaarMeasure μ𝔽 nuTheta).ae_eq hj
  apply hE.trans (hb.trans (heq.trans ?_))
  filter_upwards [heq'] with x hx
  exact congrArg (fun z : ℂ ↦ (χ⁻¹ x : ℂ)*z) hx

private theorem stripTheta_radial_schwartz {J : Set ℝ} (h0 : 0 ∈ J) (χ : PontryaginDual C𝔽)
    (p : PositiveRealExponentialDecay J) :
    ∃ θ : SchwartzBruhat C𝔽, ∀ x, θ x = rad(χ, p.val) x := by
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  obtain ⟨S,hS⟩ := schwartzBruhat_realCoordinate_equiv positiveRealLogEquiv
  obtain ⟨L,hL,-⟩ := exists_modulatedSchwartz_isotypeLift m𝔽 hm𝔽 hms𝔽 χ
  let f := logExponentialDecayTwist J ⟨0,h0⟩ p
  refine ⟨L (S f),fun x ↦ ?_⟩
  rw [hL,hS,positiveRealLogEquiv_apply]
  congr 1
  change f (logNorm x) = p.val (logNorm x)
  simpa [f] using logExponentialDecayTwist_apply J ⟨0,h0⟩ p (logNorm x)

private theorem stripTheta_scalar_fourier {J : Set ℝ} (h0 : 0 ∈ J) (χ : PontryaginDual C𝔽) (γ : ℝ → PontryaginDual C𝔽)
    (hγ : ∀ t x, γ t x = (χ x)⁻¹ * Circle.exp (-t * logNorm x))
    (f : PositiveRealExponentialDecay J) (t : ℝ) :
    lcaFourier μ𝔽 rad(χ, f.val) (γ t) =
      ((Measure.haarScalarFactor μ𝔽 nuTheta : ℝ) : ℂ) *
        mellin (fun x ↦ f.val (Real.log x)) ((t : ℂ) * Complex.I) := by
  let ν := nuTheta
  let : ν.IsHaarMeasure := (existsUnique_canonicalModulatedHaar m𝔽 hm𝔽).exists.choose_spec.1
  have hfun (x : C𝔽) : rad(χ, f.val) x * star (γ t x : ℂ) =
      f.val (logNorm x) * Complex.exp (((t:ℂ)*Complex.I) * (logNorm x : ℂ)) := by
    have hψ : γ t x = (χ x * Circle.exp (t * logNorm x))⁻¹ := by rw [hγ,neg_mul,Circle.exp_neg,mul_inv]
    have hph : star (γ t x : ℂ) = (χ x : ℂ) * Complex.exp (((t * logNorm x : ℝ) : ℂ)*Complex.I) := by
      rw [hψ,Circle.coe_inv_eq_conj, ← Complex.star_def,star_star,Circle.coe_mul,Circle.coe_exp]
    change (((χ x)⁻¹ : Circle) : ℂ) * f.val (logNorm x) * star (γ t x : ℂ) = _
    rw [hph,Circle.coe_inv,Complex.ofReal_mul,show (t:ℂ)*(logNorm x : ℂ)*Complex.I = (t:ℂ)*Complex.I*(logNorm x : ℂ) by ring]
    field_simp [Circle.coe_ne_zero]
  have hprofile := (integral_congr_ae (.of_forall hfun) : lcaFourier μ𝔽 rad(χ, f.val) (γ t) = _)
  refine hprofile.trans ?_
  rw [mellin_logProfile]
  conv_lhs => rw [Measure.isMulLeftInvariant_eq_smul μ𝔽 ν,integral_smul_nnreal_measure]
  rw [NNReal.smul_def, Complex.real_smul]
  congr 1
  have hl := sobolev_log_preserving m𝔽 hm𝔽 hms𝔽
  have hc : Continuous f.val := by
    refine (logExponentialDecayTwist J ⟨0,h0⟩ f).continuous.congr ?_
    intro x
    simpa using logExponentialDecayTwist_apply J ⟨0,h0⟩ f x
  let q (x : ℝ) := f.val x * Complex.exp (((t:ℂ)*Complex.I)*(x:ℂ))
  have hq : Continuous q := hc.mul (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
  exact (integral_map hl.measurable.aemeasurable (f := q) hq.aestronglyMeasurable).symm.trans
    (congrArg (fun η : Measure ℝ ↦ ∫ x, q x ∂η) hl.map_eq)

private theorem stripTheta_radial_symbols {J : Set ℝ} (h0 : 0 ∈ J) (χ : PontryaginDual C𝔽) :
    ∃ γ : ℝ → PontryaginDual C𝔽,
      (∀ t x, γ t x = (χ x)⁻¹ * Circle.exp (-t * logNorm x)) ∧
      ∀ p : PositiveRealExponentialDecay J,
        (∀ t, lcaFourier μ𝔽 rad(χ, p.val) (γ t) = ((Measure.haarScalarFactor μ𝔽 nuTheta : ℝ) : ℂ) *
          mellin (fun x ↦ p.val (Real.log x)) ((t : ℂ) * Complex.I)) ∧
        ∀ ψ, ψ ∉ range γ → lcaFourier μ𝔽 rad(χ, p.val) ψ = 0 := by
  obtain ⟨P,γ,hγ,-,hoff,-,honto⟩ := exists_schwartzBruhat_mellinFrequencyChart m𝔽 hm𝔽 hms𝔽 μ𝔽 χ
  refine ⟨γ,hγ,fun p ↦ ⟨stripTheta_scalar_fourier h0 χ γ hγ p,fun ψ hψ ↦ ?_⟩⟩
  obtain ⟨v,hv⟩ := stripTheta_radial_schwartz h0 χ p
  have huv (k : C₁) (x : C𝔽) : v (k.val⁻¹*x) = (χ k.val : ℂ)*v x :=
    (hv _).trans ((lineProfile_radial_homogeneous χ p.val k x).trans (congrArg ((χ k.val : ℂ)*·) (hv x).symm))
  obtain ⟨q,hq⟩ := honto v huv
  have heq : (P q : C𝔽 → ℂ) = rad(χ, p.val) := funext fun x ↦ (congrArg (fun v : SchwartzBruhat C𝔽 ↦ v x) hq).trans (hv x)
  rw [←heq]
  exact hoff q ψ hψ


/-- Weighted closed theta spaces are stable under the actual Bochner integrals
of radial exponential kernels with enough room for the translation norm. -/
theorem stripTheta_radial_orbit_mem {J : Set ℝ} (h0 : 0 ∈ J) (α s a : ℝ)
    (hα : 0 ≤ α) (hs : 0 ≤ s) (hneg : -(α+s/2) ∈ J) (hpos : α+s/2 ∈ J)
    (χ : PontryaginDual C𝔽) (p : PositiveRealExponentialDecay J) (u : W(-α, α, s))
    (hu : u ∈ Θ(a, neg_le_self hα, hs)) :
    let τ := hardySobolevTranslation μ𝔽 m𝔽 (-α) α s (neg_le_self hα) hs
    (∫ g, rad(χ, p.val) g • τ g u ∂μ𝔽) ∈ Θ(a, neg_le_self hα, hs) := by
  intro τ
  let K := Θ(a, neg_le_self hα, hs)
  obtain ⟨ρ,hρ,-,-⟩ := exists_globalThetaSobolevAction (F := F) a (neg_le_self hα) hs
  have hτ (g : C𝔽) : ∀ v ∈ K, τ g v ∈ K := fun v hv ↦ (hρ g ⟨v,hv⟩) ▸ (ρ g ⟨v,hv⟩).property
  exact lineProfile_pettis_mem_closed μ𝔽 K (Submodule.isClosed_topologicalClosure _) τ hτ hu
    (Integrable.hasPettisIntegral (stripTheta_radial_orbit_integrable h0 α s hα hs hneg hpos χ p u))

private theorem stripTheta_eq_of_fourier {l r s : ℝ} (u v : W(l, r, s)) (hu : Integrable (u : C𝔽 → ℂ) μ𝔽)
    (hv : Integrable (v : C𝔽 → ℂ) μ𝔽) (h : ∀ ψ, lcaFourier μ𝔽 u ψ = lcaFourier μ𝔽 v ψ) : u = v := by
  let H := lcaFourier_L1 μ𝔽
  let f : Lp ℂ 1 μ𝔽 := hu.toL1 u
  let g : Lp ℂ 1 μ𝔽 := hv.toL1 v
  have hf : (f : C𝔽 → ℂ) =ᵐ[μ𝔽] (u : C𝔽 → ℂ) := hu.coeFn_toL1
  have hg : (g : C𝔽 → ℂ) =ᵐ[μ𝔽] (v : C𝔽 → ℂ) := hv.coeFn_toL1
  have hfg : H.choose f = H.choose g := by
    apply ZeroAtInftyContinuousMap.ext
    intro ψ
    rw [H.choose_spec.1 f ψ, H.choose_spec.1 g ψ]
    exact (integral_congr_ae (hf.mul EventuallyEq.rfl)).trans
      ((h ψ).trans (integral_congr_ae (hg.symm.mul EventuallyEq.rfl)))
  have hfg' : f = g := H.choose_spec.2.1 hfg
  have hrep : (f : C𝔽 → ℂ) =ᵐ[μ𝔽] (g : C𝔽 → ℂ) := by rw [hfg']
  exact Lp.ext ((withDensity_absolutelyContinuous μ𝔽 _).ae_eq (hf.symm.trans (hrep.trans hg)))

/-- A Mellin product by the centered transform of any adelic polar-free test
is the Fourier transform of its radial convolution in the closed theta space. -/
theorem stripTheta_generator_product_mem {J : Set ℝ} (h0 : 0 ∈ J) (α s a : ℝ)
    (hα : 0 ≤ α) (hs : 0 ≤ s) (hneg : -(α+s/2) ∈ J) (hpos : α+s/2 ∈ J)
    (χ : PontryaginDual C𝔽) (f : adelePolarSubspace F) (p : PositiveRealExponentialDecay J)
    (v : W(-α, α, s)) (w : PositiveRealExponentialDecay J) (hv : (v : C𝔽 → ℂ) =ᵐ[μ𝔽] rad(χ, w.val))
    (hprod : ∀ t : ℝ, mellin (fun x ↦ w.val (Real.log x)) ((t:ℂ)*Complex.I) =
      globalThetaMellinIntegral f.val (ideleClassNormTwist χ ((a:ℂ)+(t:ℂ)*Complex.I)) *
        mellin (fun x ↦ p.val (Real.log x)) ((t:ℂ)*Complex.I)) :
    v ∈ Θ(a, neg_le_self hα, hs) := by
  let E := (existsUnique_globalThetaSobolevEmbedding (F := F) a (-α) α s (neg_le_self hα) hs).exists.choose
  let u := E (Submodule.Quotient.mk f)
  let τ := hardySobolevTranslation μ𝔽 m𝔽 (-α) α s (neg_le_self hα) hs
  let φ := rad(χ, p.val)
  let z := ∫ g, φ g • τ g u ∂μ𝔽
  have hu := (existsUnique_globalThetaSobolevEmbedding (F := F) a (-α) α s (neg_le_self hα) hs).exists.choose_spec.2 f
  obtain ⟨γ,hγ,hFT⟩ := stripTheta_radial_symbols h0 χ
  have hG := lineProfile_weightedTheta χ a γ hγ f
  have huI : Integrable (u : C𝔽 → ℂ) μ𝔽 := hG.1.congr hu.symm
  have huF (t : ℝ) : lcaFourier μ𝔽 u (γ t) =
      globalThetaMellinIntegral f.val (ideleClassNormTwist χ ((a:ℂ)+(t:ℂ)*Complex.I)) :=
    (integral_congr_ae (hu.mul EventuallyEq.rfl)).trans (hG.2 t)
  have hφ : Integrable φ μ𝔽 := stripTheta_radial_integrable h0 χ p
  have horb := stripTheta_radial_orbit_integrable h0 α s hα hs hneg hpos χ p u
  have hz : (z : C𝔽 → ℂ) =ᵐ[μ𝔽] lcaConvolution μ𝔽 φ u :=
    (stripTheta_orbit_integral (-α) α s (neg_le_self hα) hs hφ u horb).mono fun _ h ↦ h.2
  have hzi := (lcaConvolution_integrable μ𝔽 hφ huI).2.1.congr hz.symm
  have hvi := (stripTheta_radial_integrable h0 χ w).congr hv.symm
  have hconv := lcaFourier_convolution μ𝔽 hφ huI
  have heq : z = v := by
    apply stripTheta_eq_of_fourier (F := F) (l := -α) (r := α) (s := s) z v hzi hvi
    intro ψ
    refine (integral_congr_ae (hz.mul EventuallyEq.rfl)).trans ((congrFun hconv ψ).trans ?_)
    refine Eq.trans (b := lcaFourier μ𝔽 rad(χ, w.val) ψ) ?_ (integral_congr_ae (hv.symm.mul EventuallyEq.rfl))
    change lcaFourier μ𝔽 rad(χ, p.val) ψ*lcaFourier μ𝔽 u ψ = _
    by_cases hψ : ψ ∈ range γ
    · obtain ⟨t,rfl⟩ := hψ
      rw [(hFT p).1,huF,(hFT w).1,hprod]
      ring
    · rw [(hFT p).2 _ hψ,zero_mul,(hFT w).2 _ hψ]
  rw [←heq]
  exact stripTheta_radial_orbit_mem h0 α s a hα hs hneg hpos χ p u
    (Submodule.le_topologicalClosure _ (LinearMap.mem_range_self E.toLinearMap _))



open Real
/-- Absolute convergence at the two real endpoints bounds a polar-free theta
Mellin transform uniformly throughout the closed vertical strip between them. -/
theorem globalThetaMellinIntegral_bounded_closedStrip (χ : PontryaginDual C𝔽)
    (f : adelePolarSubspace F) (l r : ℝ) :
    ∃ M : ℝ, ∀ w : ℂ, l ≤ w.re → w.re ≤ r →
      ‖globalThetaMellinIntegral f.val (ideleClassNormTwist χ w)‖ ≤ M := by
  obtain ⟨hf, hf'⟩ := (mem_adelePolarSubspace f.val).mp f.property
  let A (w : ℂ) (x : C𝔽) := adelicTheta f.val x * ideleClassNormTwist χ w x
  let ν := μ𝔽
  have hi (w : ℂ) : Integrable (A w) ν := globalThetaMellinIntegral_integrable_of_vanishing f.val hf hf' _
  refine ⟨∫ x, ‖A l x‖ + ‖A r x‖ ∂ν,fun w hl hr ↦ ?_⟩
  change ‖∫ x, A w x ∂ν‖ ≤ _
  refine (norm_integral_le_integral_norm _).trans (integral_mono (hi w).norm ((hi l).norm.add (hi r).norm) ?_)
  intro x
  let t : ℝ := ((ideleClassNorm F x).val : ℝ)
  have ht : 0 < t := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hA (z : ℂ) : ‖A z x‖ = ‖adelicTheta f.val x‖ * t^z.re := by
    change ‖adelicTheta f.val x * ((χ x : ℂ) * ((t : ℂ)^z))‖ = _
    rw [norm_mul, norm_mul, Circle.norm_coe, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht]
  change ‖A w x‖ ≤ ‖A l x‖ + ‖A r x‖
  rw [hA,hA,hA, Complex.ofReal_re, Complex.ofReal_re, ← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  by_cases h : 1 ≤ t
  · exact (rpow_le_rpow_of_exponent_le h hr).trans (le_add_of_nonneg_left (rpow_nonneg ht.le _))
  · exact (rpow_le_rpow_of_exponent_ge ht (le_of_not_ge h) hl).trans (le_add_of_nonneg_right (rpow_nonneg ht.le _))


open Metric Real

/-- Some polar-free theta test has a transform nonzero at absolute real coordinate two. -/
theorem exists_stripTheta_generator_nonzero (χ : PontryaginDual C𝔽) :
    ∃ f : adelePolarSubspace F, globalThetaMellinIntegral f.val (ideleClassNormTwist χ 2) ≠ 0 := by
  have h₂ : meromorphicOrderAt (continuedCompletedHeckeL χ) (2:ℂ) ≤ 0 := by
    by_contra! h
    have hbad := completedHeckeL_continuation_zeros χ _ (continuedCompletedHeckeL_spec χ).1
      (continuedCompletedHeckeL_spec χ).2 (by norm_num : 0 < (2:ℂ).re) h
    norm_num at hbad
  obtain ⟨f,hf⟩ := (isLeast_globalThetaMellinIntegral_orders χ (2:ℂ)).1
  obtain ⟨h₀,h₁⟩ := (mem_adelePolarSubspace f.val).mp f.property
  have hG := globalThetaMellinIntegral_entire_of_vanishing f.val h₀ h₁ χ
  exact ⟨f,(hG.analyticAt _).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp (hf.trans (max_eq_left h₂))⟩

/-- Mellin values on the strip determine every logarithmic test profile. -/
theorem stripTheta_mellin_ext {J : Set ℝ} (hJ : IsOpen J) (hi : OrdConnected J) (hn : J.Nonempty)
    (p q : PositiveRealExponentialDecay J)
    (hpq : ∀ z : ℂ, z.re ∈ J → mellin (fun t ↦ p.val (Real.log t)) z = mellin (fun t ↦ q.val (Real.log t)) z) :
    p = q := by
  let M := positiveRealFourierMellin J hJ hi hn
  apply M.injective
  apply Subtype.ext
  funext z
  by_cases hz : z.re ∈ J
  · exact (positiveRealFourierMellin_apply J hJ hi hn p z hz).trans ((hpq z hz).trans
      (positiveRealFourierMellin_apply J hJ hi hn q z hz).symm)
  · exact ((M p).property.1 hz).trans ((M q).property.1 hz).symm

/-- For one polar-free generator, a normalized Blaschke tail of its full divisor
times any entire rapidly decreasing test killing the complementary finite jets
has a radial lift in the closed global theta Sobolev space. -/
theorem stripTheta_full_divisor_finite_jet_mem (χ : PontryaginDual C𝔽) (f : adelePolarSubspace F)
    (α s a A k c r : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s) (hr : α+s/2 < r)
    (hk : 0 < k) (hkc : k < c) (hwide : k*(|0-A|+r) < Real.pi/2) (hcr : c*r < Real.pi/2)
    (h₀ : globalThetaMellinIntegral f.val (ideleClassNormTwist χ ((a:ℂ)+(A:ℂ))) ≠ 0) :
    let G (z : ℂ) := globalThetaMellinIntegral f.val (ideleClassNormTwist χ ((a:ℂ)+z))
    let D := synthesis_stripBlaschkeFromDisk (A:ℂ) k
    let B := synthesis_stripBlaschkeToDisk (A:ℂ) k
    let Z := {z : ℂ // z ∈ ball 0 1 ∧ G (D z) = 0}
    let m (i : Z) := analyticOrderNatAt G (D i.val)
    let J := Ioo (-r) r
    ∀ (S : Finset Z) (H : SchwartzBergman (univ : Set ℝ)),
      (∀ i ∈ S, (m i : ℕ∞) ≤ analyticOrderAt H.val (D i.val)) →
      ∃ y : PositiveRealExponentialDecay J,
        (∀ z : ℂ, z.re ∈ J → mellin (fun x ↦ y.val (Real.log x)) z =
          DiskTails.diskBlaschkeTail (fun i : Z ↦ i.val) m S (B z)*H.val z) ∧
        (∃ v : W(-α, α, s), (v : C𝔽 → ℂ) =ᵐ[μ𝔽] rad(χ, y.val) ∧ v ∈ Θ(a, neg_le_self hα, hs)) ∧
        ∀ (q : PositiveRealExponentialDecay J) (v : W(-α, α, s)),
          (∀ z : ℂ, z.re ∈ J → mellin (fun x ↦ q.val (Real.log x)) z =
            DiskTails.diskBlaschkeTail (fun i : Z ↦ i.val) m S (B z)*H.val z) →
          (v : C𝔽 → ℂ) =ᵐ[μ𝔽] rad(χ, q.val) → v ∈ Θ(a, neg_le_self hα, hs) := by
  intro G D B Z m J S H hmem
  obtain ⟨h₁,h₂⟩ := (mem_adelePolarSubspace f.val).mp f.property
  have hent := globalThetaMellinIntegral_entire_of_vanishing f.val h₁ h₂ χ
  have hGa (z : ℂ) : AnalyticAt ℂ G z :=
    (hent.analyticAt _).comp (analyticAt_const.add analyticAt_id)
  let R := (Real.pi/2)/k
  obtain ⟨M,hM⟩ := globalThetaMellinIntegral_bounded_closedStrip χ f (a+A-R) (a+A+R)
  have hb (z : ℂ) (hz : |z.re-A| < R) : ‖G z‖ ≤ M := by
    apply hM
    · rw [Complex.add_re,Complex.ofReal_re]
      linarith [(abs_lt.mp hz).1]
    · rw [Complex.add_re,Complex.ofReal_re]
      linarith [(abs_lt.mp hz).2]
  have hr' : 0 < r := by linarith
  obtain ⟨y,hy,K,v,hvy,hv⟩ := stripBergman_single_generator_finite_jets A k c r hk hkc hr' hwide hcr G
    (fun z _ ↦ hGa z) h₀ M hb S H hmem
  have hsub : Icc (-α) α ⊆ J := fun t ht ↦ ⟨by linarith [ht.1],by linarith [ht.2]⟩
  obtain ⟨L,hL⟩ := stripTheta_test_lift χ (-α) α s (neg_le_self hα) hs J isOpen_Ioo ordConnected_Ioo hsub
  have hzero : 0 ∈ J := ⟨by linarith,hr'⟩
  have hneg : -(α+s/2) ∈ J := ⟨by linarith,by linarith⟩
  have hpos : α+s/2 ∈ J := ⟨by linarith,hr⟩
  have hn (n : ℕ) : L (v n) ∈ Θ(a, neg_le_self hα, hs) := by
    apply stripTheta_generator_product_mem hzero α s a hα hs hneg hpos χ f (K n) _ (v n) (hL _)
    intro t
    apply hv n
    simpa using hr'
  have hclosed : IsClosed (Θ(a, neg_le_self hα, hs) : Set W(-α, α, s)) := Submodule.isClosed_topologicalClosure _
  have hym : L y ∈ Θ(a, neg_le_self hα, hs) :=
    hclosed.mem_of_tendsto ((L.continuous.tendsto y).comp hvy) (.of_forall hn)
  refine ⟨y,hy,⟨L y,hL y,hym⟩,fun q u hq hu ↦ ?_⟩
  have hqy : q = y := stripTheta_mellin_ext isOpen_Ioo ordConnected_Ioo ⟨0,hzero⟩ q y
    (fun z hz ↦ (hq z hz).trans (hy z hz).symm)
  subst q
  have heq : u = L y := Lp.ext ((withDensity_absolutelyContinuous μ𝔽 _).ae_eq (hu.trans (hL y).symm))
  exact heq ▸ hym


/-- Every entire rapidly decreasing Mellin multiplier times any polar-free theta
generator has its inverse Mellin profile in the closed theta space on every
finite Sobolev strip, with its actual inverse-character lift. -/
theorem stripTheta_entire_generator_product_mem (χ : PontryaginDual C𝔽) (f : adelePolarSubspace F)
    (α s a : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s) (H : SchwartzBergman (univ : Set ℝ)) :
    let G (z : ℂ) := globalThetaMellinIntegral f.val (ideleClassNormTwist χ ((a:ℂ)+z))
    ∃ y : PositiveRealExponentialDecay univ, (∀ z : ℂ, mellin (fun x ↦ y.val (Real.log x)) z = G z*H.val z) ∧
      ∃ v : W(-α, α, s), (v : C𝔽 → ℂ) =ᵐ[μ𝔽] rad(χ, y.val) ∧ v ∈ Θ(a, neg_le_self hα, hs) := by
  intro G
  obtain ⟨h₁,h₂⟩ := (mem_adelePolarSubspace f.val).mp f.property
  have hd : Differentiable ℂ G := (globalThetaMellinIntegral_entire_of_vanishing f.val h₁ h₂ χ).comp
    ((differentiable_const (a:ℂ)).add differentiable_id)
  let Q : SchwartzBergman (univ : Set ℝ) := ⟨fun z ↦ G z*H.val z,by
    refine ⟨fun z hz ↦ (hz (mem_univ _)).elim,hd.differentiableOn.mul H.property.2.1,?_⟩
    intro l r hlr hsub n
    obtain ⟨M,hM⟩ := globalThetaMellinIntegral_bounded_closedStrip χ f (a+l) (a+r)
    obtain ⟨C,hC⟩ := H.property.2.2 l r hlr hsub n
    have hM₀ : 0 ≤ M := (norm_nonneg _).trans (hM ((a+l:ℝ):ℂ) (by simp) (by simpa using hlr))
    refine ⟨M*C,?_⟩
    rintro _ ⟨z,hz,rfl⟩
    have hG : ‖G z‖ ≤ M := hM _ (by simpa only [Complex.add_re,Complex.ofReal_re,add_le_add_iff_left] using hz.1)
      (by simpa only [Complex.add_re,Complex.ofReal_re,add_le_add_iff_left] using hz.2)
    change ‖z^n*(G z*H.val z)‖ ≤ M*C
    rw [show z^n*(G z*H.val z) = G z*(z^n*H.val z) by ring,norm_mul]
    exact mul_le_mul hG (hC ⟨z,hz,rfl⟩) (norm_nonneg _) hM₀⟩
  let M := positiveRealFourierMellin univ isOpen_univ ordConnected_univ univ_nonempty
  have hi (P : SchwartzBergman (univ : Set ℝ)) (z : ℂ) :
      mellin (fun x ↦ (M.symm P).val (Real.log x)) z = P.val z :=
    (positiveRealFourierMellin_apply univ isOpen_univ ordConnected_univ univ_nonempty (M.symm P) z (mem_univ _)).symm.trans
      (congrArg (fun U : SchwartzBergman (univ : Set ℝ) ↦ U.val z) (M.apply_symm_apply P))
  let y := M.symm Q
  obtain ⟨L,hL⟩ := stripTheta_test_lift χ (-α) α s (neg_le_self hα) hs univ isOpen_univ ordConnected_univ (subset_univ _)
  refine ⟨y,hi Q, L y,hL y,?_⟩
  apply stripTheta_generator_product_mem (mem_univ _) α s a hα hs (mem_univ _) (mem_univ _) χ f (M.symm H) _ y (hL _)
  intro t
  rw [hi H]
  exact hi Q _


end RiemannMasullo
