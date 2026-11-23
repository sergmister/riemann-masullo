module

import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.MellinInversion
import RiemannMasullo.ForMathlib.Analysis.Complex.PhragmenLindelof
import RiemannMasullo.ForMathlib.Analysis.Distribution.SchwartzSpace.ChangeVariables
import RiemannMasullo.ForMathlib.Topology.Algebra.Module.OpenMapping
public import RiemannMasullo.AppD_SchwartzBruhat.Sec2b
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RealDeriv
import RiemannMasullo.ForMathlib.Analysis.Complex.VerticalCauchyIntegral
public import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import RiemannMasullo.ForMathlib.Analysis.Distribution.SchwartzSpace.Montel
import Mathlib.Analysis.PSeries
import RiemannMasullo.ForMathlib.Analysis.Distribution.SchwartzSpace.Grid
import RiemannMasullo.ForMathlib.Analysis.Normed.Module.CompactInterpolation
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Algebra.IsUniformGroup.DiscreteSubgroup
public import RiemannMasullo.ForMathlib.Analysis.Distribution.ContDiffMapSupportedIn
import RiemannMasullo.ForMathlib.Analysis.MellinTransform
import RiemannMasullo.AppC_LCTVS.Sec2a
import RiemannMasullo.Ch02_AdelicTheta.Sec1
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.HahnBanach
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.StrongBidual
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.StrongDual

/-!
# Schwartz–Bergman spaces and Schwartz–Bruhat functions with exponential decay

Masullo, Appendix D, §§D.3.1–D.3.3.
-/

@[expose] public noncomputable section

namespace RiemannMasullo

open Bornology Filter Function MeasureTheory Set Topology TopologicalSpace UniformSpace
open scoped ContDiff NNReal ENNReal SchwartzMap TensorProduct

section Bergman

/-- Paper: Lemma D.3.1.1, p. 797. Bounds for one polynomial weight on every
interior strip persist after taking any number of complex derivatives. -/
theorem verticalStrip_weighted_iteratedDeriv_bounded (a b : ℝ) (hab : a < b)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (Complex.re ⁻¹' Ioo a b)) (N : ℕ)
    (h : ∀ c d : ℝ, a < c → c < d → d < b →
      BddAbove ((fun z : ℂ ↦ ‖z ^ N * f z‖) '' (Complex.re ⁻¹' Ioo c d)))
    (k : ℕ) (c d : ℝ) (hac : a < c) (hcd : c < d) (hdb : d < b) :
    BddAbove ((fun z : ℂ ↦ ‖z ^ N * iteratedDeriv k f z‖) '' (Complex.re ⁻¹' Ioo c d)) := by
  let r := min (c - a) (b - d) / 2
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have ha : a < c - r := by
    dsimp [r]
    linarith [min_le_left (c - a) (b - d)]
  have hb : d + r < b := by
    dsimp [r]
    linarith [min_le_right (c - a) (b - d)]
  obtain ⟨M, hM⟩ := h (c - r) (d + r) ha (by linarith) hb
  let B := 2 ^ N * max M 0
  refine ⟨k.factorial * B / (r / 4) ^ k, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  change c < z.re ∧ z.re < d at hz
  -- Choose a circle on which the weight at the center is controlled by the boundary weight.
  obtain ⟨R, hRlo, hRhi, hweight⟩ : ∃ R : ℝ, r / 4 ≤ R ∧ R ≤ r ∧
      ∀ w ∈ Metric.sphere z R, ‖z‖ ≤ 2 * ‖w‖ := by
    by_cases hsmall : ‖z‖ ≤ r / 2
    · refine ⟨r, by linarith, le_rfl, ?_⟩
      intro w hw
      have hd := dist_le_norm_add_norm w z
      rw [Metric.mem_sphere.mp hw] at hd
      linarith [norm_nonneg w]
    · refine ⟨r / 4, le_rfl, by linarith, ?_⟩
      intro w hw
      have hd := norm_sub_norm_le z w
      rw [← dist_eq_norm, dist_comm, Metric.mem_sphere.mp hw] at hd
      linarith
  have hstrip {w : ℂ} (hw : w ∈ Metric.closedBall z R) :
      w ∈ Complex.re ⁻¹' Ioo (c - r) (d + r) := by
    have hd := (Complex.abs_re_le_norm (w - z)).trans (mem_closedBall_iff_norm.mp hw)
    rw [Complex.sub_re, abs_le] at hd
    exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have hdiff := (hf.const_mul (z ^ N)).diffContOnCl_ball (c := z) (R := R)
    (fun w hw ↦ Ioo_subset_Ioo ha.le hb.le (hstrip hw))
  have hcircle (w : ℂ) (hw : w ∈ Metric.sphere z R) : ‖z ^ N * f w‖ ≤ B := by
    have hwM := hM (mem_image_of_mem _ (hstrip (Metric.sphere_subset_closedBall hw)))
    calc
      ‖z ^ N * f w‖ = ‖z‖ ^ N * ‖f w‖ := by rw [norm_mul, norm_pow]
      _ ≤ (2 * ‖w‖) ^ N * ‖f w‖ := by
        gcongr
        exact hweight w hw
      _ = 2 ^ N * ‖w ^ N * f w‖ := by rw [mul_pow, norm_mul, norm_pow, mul_assoc]
      _ ≤ B := by
        dsimp [B]
        gcongr
        exact hwM.trans (le_max_left _ _)
  have hest := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k
    (by linarith : 0 < R) hdiff hcircle
  rw [iteratedDeriv_const_mul_field] at hest
  apply hest.trans
  exact div_le_div_of_nonneg_left (by dsimp [B]; positivity) (by positivity)
    (pow_le_pow_left₀ (by positivity) hRlo k)

-- TODO(paper-gap): The proof's displayed denominator in (D.3.1.2) uses
-- σ + Re(z), although the real part of σ + iT - z is σ - Re(z).

/-- Paper: Definition D.3.1.3, p. 800. The strip conditions are closed under
the vector space operations. -/
theorem schwartzBergman_closure (I : Set ℝ) :
    let P (f : ℂ → ℂ) :=
      EqOn f 0 (Complex.re ⁻¹' I)ᶜ ∧ DifferentiableOn ℂ f (Complex.re ⁻¹' I) ∧
      ∀ (a b : ℝ), a ≤ b → Icc a b ⊆ I → ∀ N : ℕ,
        BddAbove ((fun z : ℂ ↦ ‖z ^ N * f z‖) '' (Complex.re ⁻¹' Icc a b))
    P 0 ∧ (∀ {f g}, P f → P g → P (f + g)) ∧ (∀ c : ℂ, ∀ {f}, P f → P (c • f)) := by
  dsimp only
  refine ⟨⟨eqOn_refl _ _, differentiableOn_const 0, ?_⟩, ?_, ?_⟩
  · intro a b _ _ N
    exact ⟨0, by rintro _ ⟨z, _, rfl⟩; simp⟩
  · rintro f g ⟨hf, df, bf⟩ ⟨hg, dg, bg⟩
    refine ⟨fun z hz ↦ ?_, df.add dg, ?_⟩
    · simp [Pi.add_apply, hf hz, hg hz]
    · intro a b hab hI N
      obtain ⟨A, hA⟩ := bf a b hab hI N
      obtain ⟨B, hB⟩ := bg a b hab hI N
      refine ⟨A + B, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      change ‖z ^ N * (f z + g z)‖ ≤ _
      rw [mul_add]
      exact (norm_add_le _ _).trans (add_le_add (hA ⟨z, hz, rfl⟩) (hB ⟨z, hz, rfl⟩))
  · rintro c f ⟨hf, df, bf⟩
    refine ⟨fun z hz ↦ ?_, df.const_mul c, ?_⟩
    · simp [Pi.smul_apply, hf hz]
    · intro a b hab hI N
      obtain ⟨A, hA⟩ := bf a b hab hI N
      refine ⟨‖c‖ * A, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      change ‖z ^ N * (c * f z)‖ ≤ _
      rw [mul_left_comm, norm_mul]
      exact mul_le_mul_of_nonneg_left (hA ⟨z, hz, rfl⟩) (norm_nonneg _)

/-- Paper: Definition D.3.1.3, p. 800. These are the holomorphic functions
with rapid decay on every bounded-width strip whose real closure is contained in the interval.
Deviation: Functions are extended by zero outside their strip to give a common carrier.
Bounds are tested on closed substrips, which is equivalent on an open interval. -/
def schwartzBergmanSubmodule (I : Set ℝ) : Submodule ℂ (ℂ → ℂ) where
  carrier := {f | EqOn f 0 (Complex.re ⁻¹' I)ᶜ ∧ DifferentiableOn ℂ f (Complex.re ⁻¹' I) ∧
    ∀ (a b : ℝ), a ≤ b → Icc a b ⊆ I → ∀ N : ℕ,
      BddAbove ((fun z : ℂ ↦ ‖z ^ N * f z‖) '' (Complex.re ⁻¹' Icc a b))}
  zero_mem' := (schwartzBergman_closure I).1
  add_mem' := (schwartzBergman_closure I).2.1
  smul_mem' := (schwartzBergman_closure I).2.2

/-- Paper: Definition D.3.1.3, p. 800. The Gaussian restricted to a strip
gives a nonzero example whenever the strip is nonempty.
Deviation: Sanity check in the zero-extension representation. -/
theorem gaussian_mem_schwartzBergmanSubmodule (I : Set ℝ) (hI : IsOpen I) :
    (Complex.re ⁻¹' I).indicator (fun z : ℂ ↦ Complex.exp (z ^ 2)) ∈
      schwartzBergmanSubmodule I := by
  refine ⟨fun z hz ↦ indicator_of_notMem hz _, ?_, ?_⟩
  · have h : Differentiable ℂ (fun z : ℂ ↦ Complex.exp (z ^ 2)) := by fun_prop
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    apply (h z).congr_of_eventuallyEq
    filter_upwards [(hI.preimage Complex.continuous_re).mem_nhds hz] with w hw
    exact indicator_of_mem hw _
  · intro a b _ hab N
    let M := max |a| |b|
    refine ⟨N.factorial * Real.exp (1 + 2 * M ^ 2), ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    have hstrip : z.re ∈ Icc a b := hz
    have hM : |z.re| ≤ M := abs_le_max_abs_abs hstrip.1 hstrip.2
    have hsq : z.re ^ 2 ≤ M ^ 2 := by
      simpa using pow_le_pow_left₀ (abs_nonneg _) hM 2
    have hweight : ‖z‖ ^ N ≤ N.factorial * Real.exp ‖z‖ := by
      have h := (div_le_iff₀ (show 0 < (N.factorial : ℝ) by positivity)).mp
        (Real.pow_div_factorial_le_exp ‖z‖ (norm_nonneg z) N)
      simpa [mul_comm] using h
    change ‖z ^ N * (Complex.re ⁻¹' I).indicator _ z‖ ≤ _
    rw [indicator_of_mem (show z ∈ Complex.re ⁻¹' I from hab hstrip), norm_mul, norm_pow, Complex.norm_exp]
    calc
      _ ≤ (N.factorial * Real.exp ‖z‖) * Real.exp (z ^ 2).re :=
        mul_le_mul_of_nonneg_right hweight (Real.exp_pos _).le
      _ = N.factorial * Real.exp (‖z‖ + (z ^ 2).re) := by rw [Real.exp_add, mul_assoc]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
        rw [pow_two, Complex.mul_re]
        nlinarith [Complex.sq_norm_sub_sq_re z, sq_nonneg (‖z‖ - 1 / 2)]

/-- Paper: (D.3.1.7), p. 799. Evaluate the polynomially weighted function on the
vertical line with real part a. -/
def weightedVerticalTrace (a : ℝ) (N : ℕ) (f : ℂ → ℂ) (x : ℝ) : ℂ :=
  let z : ℂ := (a : ℂ) + (x : ℂ) * Complex.I
  z ^ N * f z

/-- Paper: (D.3.1.7), p. 799. At zero height, the trace evaluates the weighted
function on the real axis. -/
theorem weightedVerticalTrace_zero_height (a : ℝ) (N : ℕ) (f : ℂ → ℂ) :
    weightedVerticalTrace a N f 0 = (a : ℂ) ^ N * f a := by
  simp [weightedVerticalTrace]

/-- Paper: Lemma D.3.1.2, p. 799. Each polynomially weighted trace belongs to
the indicated Lᵖ space.
Deviation: The single-line bounds also give this for an endpoint when the
carrier is used with a closed interval. -/
theorem schwartzBergman_trace_memLp (I : Set ℝ) (a : I)
    (p : ℝ≥0∞) (hp : 1 < p) (hp' : p < ⊤) (N : ℕ) (f : schwartzBergmanSubmodule I) :
    MemLp (weightedVerticalTrace a N f.val) p volume := by
  let z (x : ℝ) : ℂ := (a.val : ℂ) + x * Complex.I
  have hz (x : ℝ) : (z x).re = a := by simp [z]
  have hc : Continuous z := by
    dsimp [z]
    fun_prop
  have hf : Continuous (f.val ∘ z) :=
    f.property.2.1.continuousOn.comp_continuous hc fun x ↦ by
      simp [mem_preimage, hz]
  have bound (k : ℕ) : ∃ C : ℝ, ∀ x, ‖z x ^ k * f.val (z x)‖ ≤ C := by
    obtain ⟨C, hC⟩ := f.property.2.2 a a le_rfl (by simp) k
    exact ⟨C, fun x ↦ hC ⟨z x, by simp [mem_preimage, hz], rfl⟩⟩
  obtain ⟨A, hA⟩ := bound N
  obtain ⟨B, hB⟩ := bound (N + 1)
  have hmodel : MemLp (fun x : ℝ ↦ (1 + ‖x‖)⁻¹) p volume := by
    apply (integrable_norm_rpow_iff (by fun_prop) (zero_lt_one.trans hp).ne' hp'.ne).mp
    have hdim : 1 < p.toReal := by
      simpa using (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp'.ne).2 hp
    have hnorm (x : ℝ) : ‖(1 + ‖x‖)⁻¹‖ = (1 + ‖x‖)⁻¹ := Real.norm_of_nonneg (by positivity)
    simpa only [hnorm, Real.rpow_neg_eq_inv_rpow] using
      (integrable_one_add_norm (μ := (volume : Measure ℝ)) (r := p.toReal) (by simpa using hdim))
  apply hmodel.of_le_mul (c := A + B) ((hc.pow N).mul hf).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  change ‖z x ^ N * f.val (z x)‖ ≤ (A + B) * ‖(1 + ‖x‖)⁻¹‖
  rw [Real.norm_of_nonneg (by positivity), ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  rw [mul_add, mul_one]
  apply add_le_add (hA x)
  have hx : ‖x‖ ≤ ‖z x‖ := by simpa [Real.norm_eq_abs, z] using Complex.abs_im_le_norm (z x)
  calc
    ‖z x ^ N * f.val (z x)‖ * ‖x‖ ≤ ‖z x ^ N * f.val (z x)‖ * ‖z x‖ :=
      mul_le_mul_of_nonneg_left hx (norm_nonneg _)
    _ = ‖z x ^ (N + 1) * f.val (z x)‖ := by
      rw [← norm_mul, pow_succ, mul_right_comm]
    _ ≤ B := hB x

/-- Paper: Definition D.3.1.3, p. 800. The weighted L² norm on one line
satisfies the seminorm laws. -/
theorem schwartzBergman_l2_seminorm (I : Set ℝ) (i : I × ℕ) :
    let q (f : schwartzBergmanSubmodule I) :=
      (eLpNorm (weightedVerticalTrace i.1 i.2 f.val) 2 volume).toReal
    (∀ f g, q (f + g) ≤ q f + q g) ∧ (∀ (c : ℂ) f, q (c • f) = ‖c‖ * q f) := by
  let T (f : schwartzBergmanSubmodule I) := weightedVerticalTrace i.1 i.2 f.val
  have hT (f : schwartzBergmanSubmodule I) : MemLp (T f) 2 volume :=
    schwartzBergman_trace_memLp I i.1 2 (by norm_num) (by norm_num) i.2 f
  constructor
  · intro f g
    have hadd : T (f + g) = T f + T g := by
      funext x
      simp [T, weightedVerticalTrace, mul_add]
    change lpNorm (T (f + g)) 2 volume ≤ lpNorm (T f) 2 volume + lpNorm (T g) 2 volume
    rw [hadd]
    exact lpNorm_add_le (hT f) (by norm_num)
  · intro c f
    have hsmul : T (c • f) = c • T f := by
      funext x
      simp [T, weightedVerticalTrace, smul_eq_mul, mul_left_comm]
    change lpNorm (T (c • f)) 2 volume = ‖c‖ * lpNorm (T f) 2 volume
    rw [hsmul]
    exact lpNorm_const_smul c (T f) volume

-- TODO(paper-gap): Definition D.3.1.3 specifies positive rational abscissae
-- even for intervals contained in the negative half-line. Lemma D.3.1.2
-- instead uses real abscissae tending to both ends of the interval.

/-- Paper: Definition D.3.1.3, p. 800. Equip the Schwartz–Bergman
submodule with the topology of weighted L² convergence on interior vertical lines.
Deviation: Use all lines and p = 2 to make the choice-independent topology canonical.
Lemma D.3.1.2 identifies this with each of the paper's countable families. -/
abbrev SchwartzBergman (I : Set ℝ) :=
  WithGeneratingSeminorms (schwartzBergmanSubmodule I)
    (fun i : I × ℕ ↦ Seminorm.of
      (fun f : schwartzBergmanSubmodule I ↦
        (eLpNorm (weightedVerticalTrace i.1 i.2 f.val) 2 volume).toReal)
      (schwartzBergman_l2_seminorm I i).1 (schwartzBergman_l2_seminorm I i).2)

section VerticalTraces

local notation "linePoint" => (fun (x y : ℝ) ↦ (x : ℂ) + y * Complex.I)

private theorem exists_bracketing_lines {I : Set ℝ} (hI : IsOpen I) (a : I) :
    ∃ l r : I, (l : ℝ) < a ∧ (a : ℝ) < r := by
  obtain ⟨u, v, hav, huv⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hI.mem_nhds a.property)
  obtain ⟨l, hul, hla⟩ := exists_between hav.1
  obtain ⟨r, har, hrv⟩ := exists_between hav.2
  exact ⟨⟨l, huv ⟨hul, hla.trans hav.2⟩⟩, ⟨r, huv ⟨hav.1.trans har, hrv⟩⟩, hla, har⟩

/-- Weighted values inside the strip are bounded by the two boundary trace norms. -/
private theorem bergman_interior_lp_bound {I : Set ℝ} (hI : IsOpen I) (hInt : OrdConnected I)
    (l r : I) (p q : ℝ≥0∞) [ENNReal.HolderTriple p q 1]
    (hp : 1 < p) (hp' : p < ⊤) (hq : 1 < q) (hq' : q < ⊤) {δ : ℝ} (hδ : 0 < δ) :
    ∃ D ≥ (0 : ℝ), ∀ (k : ℕ) (f : schwartzBergmanSubmodule I) (z : ℂ),
      (l : ℝ) + δ ≤ z.re → z.re ≤ (r : ℝ) - δ →
        ‖z ^ k * f.val z‖ ≤ D * (lpNorm (weightedVerticalTrace l k f.val) p volume +
          lpNorm (weightedVerticalTrace r k f.val) p volume) := by
  obtain ⟨C, hC, hkernel⟩ := verticalCauchy_lpBound p q hq hq' hδ
  refine ⟨C / (2 * Real.pi), by positivity, ?_⟩
  intro k f z hl hr
  have hlz : (l : ℝ) < z.re := by linarith
  have hzr : z.re < (r : ℝ) := by linarith
  obtain ⟨a, _, hal, _⟩ := exists_bracketing_lines hI l
  obtain ⟨_, b, _, hrb⟩ := exists_bracketing_lines hI r
  let F (w : ℂ) := w ^ k * f.val w
  have hF : DifferentiableOn ℂ F (Complex.re ⁻¹' Ioo (a : ℝ) (b : ℝ)) :=
    (differentiableOn_id.pow k).mul (f.property.2.1.mono
      (preimage_mono (Ioo_subset_Icc_self.trans (hInt.out a.property b.property))))
  obtain ⟨M, hM⟩ := f.property.2.2 l r (hlz.trans hzr).le (hInt.out l.property r.property) (k+1)
  have hdec : ∀ᶠ y : ℝ in comap abs atTop, ∀ x ∈ Icc (l : ℝ) r, ‖F (linePoint x y)‖ ≤ max M 0 / |y| := by
    have ht : Tendsto (abs : ℝ → ℝ) (comap abs atTop) atTop := tendsto_comap
    filter_upwards [ht.eventually (eventually_gt_atTop 0)] with y hy
    intro x hx
    let w := linePoint x y
    have hw : w ∈ Complex.re ⁻¹' Icc (l : ℝ) r := by simpa [w] using hx
    have him : |y| ≤ ‖w‖ := by simpa [w] using Complex.abs_im_le_norm w
    apply (le_div_iff₀ hy).mpr
    calc ‖F w‖ * |y| ≤ ‖F w‖ * ‖w‖ := mul_le_mul_of_nonneg_left him (norm_nonneg _)
      _ = ‖w ^ (k+1) * f.val w‖ := by simp only [F, pow_succ, ← norm_mul]; congr 1; ring
      _ ≤ max M 0 := (hM ⟨w, hw, rfl⟩).trans (le_max_left _ _)
  have hL := hkernel (σ := (l : ℝ)) (z := z) (by rw [abs_of_neg (sub_neg.mpr hlz)]; linarith)
    (schwartzBergman_trace_memLp I l p hp hp' k f)
  have hR := hkernel (σ := (r : ℝ)) (z := z) (by rw [abs_of_pos (sub_pos.mpr hzr)]; linarith)
    (schwartzBergman_trace_memLp I r p hp hp' k f)
  have eq := verticalCauchyIntegral_sub_eq hF hal hrb ⟨hlz,hzr⟩ (le_max_right M 0) hdec hL.1 hR.1
  have hb := (norm_sub_le _ _).trans (add_le_add hR.2 hL.2)
  have hb' := (congrArg norm eq.symm).le.trans hb
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le] at hb'
  norm_num at hb'
  change ‖F z‖ ≤ _
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (show 0 < 2 * Real.pi by positivity)).mpr
  calc ‖F z‖ * (2 * Real.pi) ≤ C * lpNorm (weightedVerticalTrace r k f.val) p volume +
        C * lpNorm (weightedVerticalTrace l k f.val) p volume := by simpa only [mul_comm ‖F z‖] using hb'
    _ = _ := by ring

/-- Differentiating a holomorphic function along a vertical trace introduces a factor of i. -/
private theorem hasDerivAt_vertical_iterate {I : Set ℝ} (hI : IsOpen I) (a : I)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (Complex.re ⁻¹' I)) (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ Complex.I ^ n * iteratedDeriv n f (linePoint a y))
      (Complex.I ^ (n+1) * iteratedDeriv (n+1) f (linePoint a x)) x := by
  have hU := hI.preimage Complex.continuous_re
  have han : ∀ m, AnalyticOnNhd ℂ (iteratedDeriv m f) (Complex.re ⁻¹' I) := by
    intro m
    induction m with
    | zero => simpa using hf.analyticOnNhd hU
    | succ m ih => rw [iteratedDeriv_succ]; exact fun z hz ↦ (ih z hz).deriv
  have hd := (han n _ (show linePoint a x ∈ Complex.re ⁻¹' I by simp)).differentiableAt.hasDerivAt
  have hline : HasDerivAt (fun w : ℂ ↦ (a.val : ℂ) + w * Complex.I) Complex.I (x : ℂ) := by
    simpa using (((hasDerivAt_id (x : ℂ)).mul_const Complex.I).const_add (a.val : ℂ))
  have h := ((hd.comp (x : ℂ) hline).comp_ofReal).const_mul (Complex.I ^ n)
  simpa only [Function.comp_apply, iteratedDeriv_succ, pow_succ, mul_left_comm,
    mul_assoc, mul_comm (deriv _ _)] using h

private theorem iteratedDeriv_vertical {I : Set ℝ} (hI : IsOpen I) (a : I)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (Complex.re ⁻¹' I)) (n : ℕ) :
    iteratedDeriv n (fun y : ℝ ↦ f (linePoint a y)) =
      fun y ↦ Complex.I ^ n * iteratedDeriv n f (linePoint a y) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    exact (hasDerivAt_vertical_iterate hI a hf n x).deriv

/-- Both neighboring trace norms control each Schwartz seminorm on the intermediate line. -/
private theorem bergman_line_lp_bound {I : Set ℝ} (hI : IsOpen I) (hInt : OrdConnected I)
    (l a r : I) (hl : (l : ℝ) < a) (hr : (a : ℝ) < r)
    (p q : ℝ≥0∞) [ENNReal.HolderTriple p q 1] (hp : 1 < p) (hp' : p < ⊤)
    (hq : 1 < q) (hq' : q < ⊤) (k n : ℕ) :
    ∃ C ≥ (0 : ℝ), ∀ (f : schwartzBergmanSubmodule I) (y : ℝ),
      |y| ^ k * ‖iteratedDeriv n (fun u : ℝ ↦ f.val (linePoint a u)) y‖ ≤
        C * (lpNorm (weightedVerticalTrace l k f.val) p volume +
          lpNorm (weightedVerticalTrace r k f.val) p volume) := by
  let d := min ((a : ℝ) - l) ((r : ℝ) - a) / 2
  have hd : 0 < d := by dsimp [d]; positivity
  have hl' : (l : ℝ) + 2 * d ≤ a := by dsimp [d]; linarith [min_le_left ((a : ℝ) - l) ((r : ℝ) - a)]
  have hr' : (a : ℝ) + 2 * d ≤ r := by dsimp [d]; linarith [min_le_right ((a : ℝ) - l) ((r : ℝ) - a)]
  obtain ⟨D, hD, hbound⟩ := bergman_interior_lp_bound hI hInt l r p q hp hp' hq hq' hd
  refine ⟨n.factorial * (2 ^ k * D) / (d/4)^n, by positivity, ?_⟩
  intro f y
  let z := linePoint a y
  have hre : z.re = a := by simp [z]
  let Q := lpNorm (weightedVerticalTrace l k f.val) p volume + lpNorm (weightedVerticalTrace r k f.val) p volume
  have hQ : 0 ≤ Q := add_nonneg lpNorm_nonneg lpNorm_nonneg
  obtain ⟨R, hRlo, hRhi, hweight⟩ : ∃ R : ℝ, d/4 ≤ R ∧ R ≤ d ∧
      ∀ w ∈ Metric.sphere z R, ‖z‖ ≤ 2 * ‖w‖ := by
    by_cases hz : ‖z‖ ≤ d/2
    · refine ⟨d, by linarith, le_rfl, ?_⟩
      intro w hw
      have ht := dist_le_norm_add_norm w z
      rw [Metric.mem_sphere.mp hw] at ht
      linarith
    · refine ⟨d/4, le_rfl, by linarith, ?_⟩
      intro w hw
      have ht := norm_sub_norm_le z w
      rw [← dist_eq_norm, dist_comm, Metric.mem_sphere.mp hw] at ht
      linarith
  have hstrip {w : ℂ} (hw : w ∈ Metric.closedBall z R) :
      (l : ℝ) + d ≤ w.re ∧ w.re ≤ (r : ℝ) - d := by
    have h := (Complex.abs_re_le_norm (w-z)).trans (mem_closedBall_iff_norm.mp hw)
    rw [Complex.sub_re, hre, abs_le] at h
    constructor <;> linarith [h.1, h.2]
  have hdiff := (f.property.2.1.const_mul (z ^ k)).diffContOnCl_ball (c := z) (R := R)
    (fun w hw ↦ hInt.out l.property r.property ⟨by linarith [(hstrip hw).1], by linarith [(hstrip hw).2]⟩)
  have hcircle (w : ℂ) (hw : w ∈ Metric.sphere z R) : ‖z ^ k * f.val w‖ ≤ 2 ^ k * (D * Q) := by
    have hs := hstrip (Metric.sphere_subset_closedBall hw)
    calc ‖z ^ k * f.val w‖ = ‖z‖ ^ k * ‖f.val w‖ := by rw [norm_mul, norm_pow]
      _ ≤ (2 * ‖w‖)^k * ‖f.val w‖ := by gcongr; exact hweight w hw
      _ = 2 ^ k * ‖w ^ k * f.val w‖ := by rw [mul_pow, norm_mul, norm_pow, mul_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hbound k f w hs.1 hs.2) (by positivity)
  have hest := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n (by linarith : 0 < R) hdiff hcircle
  rw [iteratedDeriv_const_mul_field, norm_mul, norm_pow] at hest
  rw [iteratedDeriv_vertical hI a f.property.2.1, norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul]
  calc |y| ^ k * ‖iteratedDeriv n f.val z‖ ≤ ‖z‖ ^ k * ‖iteratedDeriv n f.val z‖ := by
        gcongr
        simpa [z] using Complex.abs_im_le_norm z
    _ ≤ _ := hest
    _ ≤ n.factorial * (2 ^ k * (D * Q)) / (d/4)^n := div_le_div_of_nonneg_left
      (by positivity) (by positivity) (pow_le_pow_left₀ (by positivity) hRlo n)
    _ = _ := by dsimp only [Q]; ring

/-- Paper: Lemma D.3.1.2, p. 799. Restriction to a vertical line as a real Schwartz function. -/
private def bergmanLine {I : Set ℝ} (hI : IsOpen I) (hInt : OrdConnected I)
    (a : I) : SchwartzBergman I →ₗ[ℂ] 𝓢(ℝ, ℂ) where
  toFun f := {
    toFun := fun x ↦ f.val (linePoint a x)
    smooth' := by
      apply contDiff_of_differentiable_iteratedDeriv
      intro n _ x
      rw [iteratedDeriv_vertical hI a f.property.2.1]
      exact (hasDerivAt_vertical_iterate hI a f.property.2.1 n x).differentiableAt
    decay' := by
      intro k n
      obtain ⟨l, r, hl, hr⟩ := exists_bracketing_lines hI a
      obtain ⟨C, _, h⟩ := bergman_line_lp_bound hI hInt l a r hl hr 2 2
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) k n
      exact ⟨_, fun x ↦ by simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] using h f x⟩ }
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

/-- Multiply a Schwartz function by the vertical polynomial weight and include it in Lᵖ. -/
private def weightedSchwartzLp (a : ℝ) (k : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    𝓢(ℝ, ℂ) →L[ℂ] Lp ℂ p (volume : Measure ℝ) :=
  (SchwartzMap.toLpCLM ℂ ℂ p volume).comp (SchwartzMap.smulLeftCLM ℂ fun y : ℝ ↦ (linePoint a y)^k)

/-- Paper: (D.3.1.7), p. 799. The weighted Lᵖ norm of the trace on a single line. -/
private def bergmanLpSeminorm {I : Set ℝ} (hI : IsOpen I) (hInt : OrdConnected I)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (a : I) (k : ℕ) : Seminorm ℂ (SchwartzBergman I) :=
  (normSeminorm ℂ _).comp ((weightedSchwartzLp a k p).toLinearMap.comp (bergmanLine hI hInt a))

private theorem bergmanLpSeminorm_apply {I : Set ℝ} (hI : IsOpen I) (hInt : OrdConnected I)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (a : I) (k : ℕ) (f : SchwartzBergman I) :
    bergmanLpSeminorm hI hInt p a k f = lpNorm (weightedVerticalTrace a k f.val) p volume := by
  change ‖((SchwartzMap.smulLeftCLM ℂ (fun y : ℝ ↦ (linePoint a y)^k)) (bergmanLine hI hInt a f)).toLp p volume‖ = _
  rw [SchwartzMap.norm_toLp, toReal_eLpNorm]
  congr 1
  have hg : (fun y : ℝ ↦ (linePoint a y) ^ k).HasTemperateGrowth := by fun_prop
  rw [SchwartzMap.smulLeftCLM_apply hg]
  rfl

private theorem bergman_with_l2 {I : Set ℝ} (hI : IsOpen I) (hInt : OrdConnected I) :
    WithSeminorms (fun i : I × ℕ ↦ bergmanLpSeminorm hI hInt 2 i.1 i.2) := by
  let P : I × ℕ → Seminorm ℂ (SchwartzBergman I) := fun i ↦ Seminorm.of
      (fun f : schwartzBergmanSubmodule I ↦ (eLpNorm (weightedVerticalTrace i.1 i.2 f.val) 2 volume).toReal)
      (schwartzBergman_l2_seminorm I i).1 (schwartzBergman_l2_seminorm I i).2
  have heq : (fun i : I × ℕ ↦ bergmanLpSeminorm hI hInt 2 i.1 i.2) = P := by
    funext i
    ext f
    exact bergmanLpSeminorm_apply hI hInt 2 i.1 i.2 f
  rw [heq]
  exact withGeneratingSeminorms_spec (schwartzBergmanSubmodule I) P

private theorem continuous_bergmanLine_of_bracketing {I : Set ℝ} (hI : IsOpen I) (hInt : OrdConnected I)
    (a l r : I) (hl : (l : ℝ) < a) (hr : (a : ℝ) < r)
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [ENNReal.HolderTriple p q 1]
    (hp : 1 < p) (hp' : p < ⊤) (hq : 1 < q) (hq' : q < ⊤)
    [t : TopologicalSpace (SchwartzBergman I)] [IsTopologicalAddGroup (SchwartzBergman I)]
    (hL : ∀ k, Continuous (bergmanLpSeminorm hI hInt p l k))
    (hR : ∀ k, Continuous (bergmanLpSeminorm hI hInt p r k)) :
    Continuous (bergmanLine hI hInt a) := by
  apply (schwartz_withSeminorms ℂ ℝ ℂ).continuous_of_continuous_comp
  rintro ⟨k,n⟩
  obtain ⟨C, hC, hb⟩ := bergman_line_lp_bound hI hInt l a r hl hr p q hp hp' hq hq' k n
  let c : ℝ≥0 := ⟨C,hC⟩
  apply Seminorm.continuous_of_le (q := c • (bergmanLpSeminorm hI hInt p l k + bergmanLpSeminorm hI hInt p r k))
    (((hL k).add (hR k)).const_smul c)
  intro f
  change SchwartzMap.seminorm ℂ k n (bergmanLine hI hInt a f) ≤
    C * (bergmanLpSeminorm hI hInt p l k f + bergmanLpSeminorm hI hInt p r k f)
  rw [bergmanLpSeminorm_apply, bergmanLpSeminorm_apply]
  apply SchwartzMap.seminorm_le_bound' _ _ _ _ (mul_nonneg hC (add_nonneg lpNorm_nonneg lpNorm_nonneg))
  exact hb f

private theorem continuous_bergmanLine {I : Set ℝ} (hI : IsOpen I) (hInt : OrdConnected I)
    (a : I) : Continuous (bergmanLine hI hInt a) := by
  obtain ⟨l, r, hl, hr⟩ := exists_bracketing_lines hI a
  have hc := (bergman_with_l2 hI hInt).continuous_seminorm
  exact continuous_bergmanLine_of_bracketing hI hInt a l r hl hr 2 2 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (fun k ↦ hc (l,k)) (fun k ↦ hc (r,k))

private theorem le_topology_withSeminorms {E ι : Type*} [AddCommGroup E] [Module ℂ E]
    [t : TopologicalSpace E] [IsTopologicalAddGroup E] {u : TopologicalSpace E}
    {P : ι → Seminorm ℂ E} (hP : WithSeminorms (topology := u) P)
    (hc : ∀ i, Continuous[t, _] (P i)) : t ≤ u :=
  continuous_id_iff_le.mp (@WithSeminorms.continuous_of_continuous_comp ℂ ℂ E E ι
    _ _ _ _ _ _ (RingHom.id ℂ) _ P t _ u hP (LinearMap.id (R := ℂ)) hc)

private theorem bergman_embedding {I : Set ℝ} (hI : IsOpen I) (hInt : OrdConnected I) :
    IsEmbedding (fun (f : SchwartzBergman I) (a : I) ↦ bergmanLine hI hInt a f) := by
  let T := LinearMap.pi (bergmanLine hI hInt)
  change IsEmbedding T
  have hcont : Continuous T := continuous_pi (continuous_bergmanLine hI hInt)
  refine ⟨⟨le_antisymm (continuous_iff_le_induced.mp hcont) ?_⟩, ?_⟩
  · let t := TopologicalSpace.induced T inferInstance
    have hT : Continuous[t, _] T := continuous_induced_dom
    have hprod := withSeminorms_pi fun _ : I ↦ schwartz_withSeminorms ℂ ℝ ℂ
    have hsource := bergman_with_l2 hI hInt
    let : TopologicalSpace (SchwartzBergman I) := t
    let : IsTopologicalAddGroup (SchwartzBergman I) := (T.withSeminorms_induced hprod).isTopologicalAddGroup
    apply le_topology_withSeminorms (t := t) hsource
    rintro ⟨a,k⟩
    exact ((weightedSchwartzLp a k 2).continuous.comp ((continuous_apply a).comp hT)).norm
  · intro f g h
    apply Subtype.ext
    funext z
    by_cases hz : z.re ∈ I
    · have eq := congrArg (fun v : 𝓢(ℝ, ℂ) ↦ v z.im) (congrFun h ⟨z.re, hz⟩)
      change f.val (linePoint z.re z.im) = g.val (linePoint z.re z.im) at eq
      simpa only [Complex.re_add_im] using eq
    · exact (f.property.1 hz).trans (g.property.1 hz).symm

end VerticalTraces

/-- Paper: Lemma D.3.1.2, p. 799. Weighted Lᵖ norms on a sequence of lines
reaching both ends of the interval generate the Schwartz–Bergman topology.
Deviation: The endpoint condition is expressed by bracketing every real point of I. -/
theorem schwartzBergman_lp_generates (I : Set ℝ) (hI : IsOpen I) (hInt : OrdConnected I)
    (hne : I.Nonempty) (a : ℕ → I)
    (ha : ∀ x : I, (∃ n, (a n : ℝ) < x) ∧ ∃ n, (x : ℝ) < a n)
    (p : ℝ≥0∞) (hp : 1 < p) (hp' : p < ⊤) :
    GeneratesLpSeminorms volume p
      (fun (i : ℕ × ℕ) (f : SchwartzBergman I) ↦ weightedVerticalTrace (a i.1) i.2 f.val) := by
  let : Fact (1 ≤ p) := ⟨hp.le⟩
  let q := ENNReal.conjExponent p
  have hq : 1 < q := (ENNReal.HolderConjugate.lt_top_iff_one_lt p q).mp hp'
  have hq' : q < ⊤ := (ENNReal.HolderConjugate.lt_top_iff_one_lt q p).mpr hp
  let P : SeminormFamily ℂ (SchwartzBergman I) (ℕ × ℕ) := fun i ↦ bergmanLpSeminorm hI hInt p (a i.1) i.2
  have hmem (i : ℕ × ℕ) (f : SchwartzBergman I) := schwartzBergman_trace_memLp I (a i.1) p hp hp' i.2 f
  refine ⟨hmem, P, ?_, ?_⟩
  · have hc (i : ℕ × ℕ) : Continuous (P i) :=
      ((weightedSchwartzLp (a i.1) i.2 p).continuous.comp (continuous_bergmanLine hI hInt (a i.1))).norm
    let t : TopologicalSpace (SchwartzBergman I) := inferInstance
    let u := P.moduleFilterBasis.topology
    have hP : WithSeminorms (topology := u) P := ⟨rfl⟩
    refine WithSeminorms.mk (topology := t) ?_
    change t = u
    apply le_antisymm
    · exact le_topology_withSeminorms (t := t) hP hc
    · have h2 := bergman_with_l2 hI hInt
      let : TopologicalSpace (SchwartzBergman I) := u
      let : IsTopologicalAddGroup (SchwartzBergman I) := hP.isTopologicalAddGroup
      apply le_topology_withSeminorms (t := u) h2
      rintro ⟨s,k⟩
      obtain ⟨⟨j,hj⟩, m, hm⟩ := ha s
      have hs := continuous_bergmanLine_of_bracketing (t := u) hI hInt s (a j) (a m) hj hm p q
        hp hp' hq hq' (fun k ↦ hP.continuous_seminorm (j,k)) (fun k ↦ hP.continuous_seminorm (m,k))
      exact ((weightedSchwartzLp s k 2).continuous.comp hs).norm
  · intro i f
    dsimp only [P]
    rw [bergmanLpSeminorm_apply, ← toReal_eLpNorm, ENNReal.ofReal_toReal (hmem i f).eLpNorm_ne_top]

/-- Paper: Lemma D.3.1.2, p. 799. The topology also comes from taking the
Schwartz restriction to each vertical line. -/
theorem schwartzBergman_schwartzLine_topology (I : Set ℝ) (hI : IsOpen I)
    (hInt : OrdConnected I) (hne : I.Nonempty) :
    ∃ T : SchwartzBergman I → (I → 𝓢(ℝ, ℂ)),
      (∀ f (a : I) x, T f a x = weightedVerticalTrace a 0 f.val x) ∧ IsEmbedding T :=
  by
    refine ⟨fun f a ↦ bergmanLine hI hInt a f, ?_, bergman_embedding hI hInt⟩
    intro f a x
    simp only [weightedVerticalTrace, pow_zero, one_mul]
    rfl

/-- Paper: Lemma D.3.1.2, p. 799. The Schwartz–Bergman space is separable. -/
theorem schwartzBergman_separable (I : Set ℝ) (hI : IsOpen I) (hInt : OrdConnected I)
    (hne : I.Nonempty) : SeparableSpace (SchwartzBergman I) := by
  let : Nonempty I := hne.to_subtype
  obtain ⟨a,ha⟩ := TopologicalSpace.exists_dense_seq I
  have hbr (x : I) : (∃ n, (a n : ℝ) < x) ∧ ∃ n, (x : ℝ) < a n := by
    obtain ⟨l,r,hl,hr⟩ := exists_bracketing_lines hI x
    exact ⟨ha.exists_mem_open isOpen_Iio ⟨l,hl⟩, ha.exists_mem_open isOpen_Ioi ⟨r,hr⟩⟩
  obtain ⟨_, P, hP, hval⟩ := schwartzBergman_lp_generates I hI hInt hne a hbr 2 (by norm_num) (by norm_num)
  let L (i : ℕ × ℕ) := (weightedSchwartzLp (a i.1) i.2 2).toLinearMap.comp (bergmanLine hI hInt (a i.1))
  let T := LinearMap.pi L
  have heq (i : ℕ × ℕ) : P i = (normSeminorm ℂ _).comp (L i) := by
    ext f
    change P i f = bergmanLpSeminorm hI hInt 2 (a i.1) i.2 f
    rw [bergmanLpSeminorm_apply, ← toReal_eLpNorm]
    exact (ENNReal.toReal_ofReal (apply_nonneg (P i) f)).symm.trans (congrArg ENNReal.toReal (hval i f))
  have hprod := withSeminorms_pi fun _ : ℕ × ℕ ↦ norm_withSeminorms ℂ (Lp ℂ 2 (volume : Measure ℝ))
  have hi : IsInducing T := by
    constructor
    refine hP.topologicalSpace_eq_iInf.trans ?_
    refine Eq.trans ?_ (WithSeminorms.topologicalSpace_eq_iInf (t := TopologicalSpace.induced T inferInstance)
      (T.withSeminorms_induced hprod)).symm
    rw [iInf_sigma]
    congr 1
    funext i
    rw [heq, iInf_unique]
    rfl
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  have := hi.secondCountableTopology
  infer_instance

end Bergman

section PositiveReal

/-- Paper: Definition D.3.2.1, p. 801. A real Schwartz map is viewed as a
function by the linear forgetful map. -/
def realSchwartzCoe : 𝓢(ℝ, ℂ) →ₗ[ℂ] (ℝ → ℂ) where
  toFun f := f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Paper: Definition D.3.2.1, p. 801. Forgetting the Schwartz properties
retains the values of the function. -/
theorem realSchwartzCoe_apply (f : 𝓢(ℝ, ℂ)) (x : ℝ) : realSchwartzCoe f x = f x := rfl

/-- Paper: Definition D.3.2.1, p. 801. In logarithmic coordinates, weighting
by tᵃ amounts to multiplying by exp(ax). -/
def logExponentialWeight (a : ℝ) : (ℝ → ℂ) →ₗ[ℂ] (ℝ → ℂ) :=
  LinearMap.mulLeft ℂ (fun x : ℝ ↦ (Real.exp (a * x) : ℂ))

/-- Paper: Definition D.3.2.1, p. 801. The weight at exponent zero does not
change the function. -/
theorem logExponentialWeight_zero (f : ℝ → ℂ) : logExponentialWeight 0 f = f := by
  ext x
  simp [logExponentialWeight, LinearMap.mulLeft]

/-- Paper: Definition D.3.2.1, p. 801. A logarithmic profile belongs to the
decay submodule if each weighted profile is a real-line Schwartz function.
Deviation: The carrier is in the logarithmic coordinate x = log t. -/
def logExponentialDecaySubmodule (I : Set ℝ) : Submodule ℂ (ℝ → ℂ) :=
  ⨅ a : I, realSchwartzCoe.range.comap (logExponentialWeight a)

/-- A compactly supported smooth profile has Schwartz decay after every real exponential twist. -/
theorem mem_logExponentialDecaySubmodule_of_hasCompactSupport (I : Set ℝ) {f : ℝ → ℂ}
    (hs : HasCompactSupport f) (hf : ContDiff ℝ ∞ f) : f ∈ logExponentialDecaySubmodule I := by
  apply (Submodule.mem_iInf _).2
  intro a
  let w (x : ℝ) : ℂ := Real.exp ((a : ℝ) * x)
  have hw : ContDiff ℝ ∞ w :=
    Complex.ofRealCLM.contDiff.comp ((contDiff_const.mul contDiff_id).exp)
  exact ⟨(hs.mul_left (f := w)).toSchwartzMap (hw.mul hf), rfl⟩

/-- Paper: Definition D.3.2.1, p. 801. The multiplier Tₐ is the weighted
profile, bundled as a Schwartz map. -/
theorem logExponentialDecay_weight_mem_range (I : Set ℝ)
    (a : I) (f : logExponentialDecaySubmodule I) :
    logExponentialWeight a f.val ∈ realSchwartzCoe.range := by
  exact (Submodule.mem_iInf _).mp f.property a

/-- Paper: (D.3.2.1), p. 801. This is the linear multiplier to the space
of Schwartz functions in logarithmic coordinates. -/
def logExponentialDecayTwist (I : Set ℝ) (a : I) : logExponentialDecaySubmodule I →ₗ[ℂ] 𝓢(ℝ, ℂ) :=
  (LinearEquiv.ofInjective realSchwartzCoe DFunLike.coe_injective).symm.toLinearMap.comp
    (((logExponentialWeight a).comp (logExponentialDecaySubmodule I).subtype).codRestrict
      realSchwartzCoe.range (logExponentialDecay_weight_mem_range I a))

/-- Paper: (D.3.2.1), p. 801. The bundled multiplier evaluates to
exp(ax) times the original logarithmic profile. -/
theorem logExponentialDecayTwist_apply (I : Set ℝ) (a : I)
    (f : logExponentialDecaySubmodule I) (x : ℝ) :
    logExponentialDecayTwist I a f x = (Real.exp ((a : ℝ) * x) : ℂ) * f.val x := by
  exact congrFun (LinearEquiv.ofInjective_symm_apply realSchwartzCoe
    (h := DFunLike.coe_injective)
    ⟨logExponentialWeight a f.val, logExponentialDecay_weight_mem_range I a f⟩) x

/-- Paper: Definition D.3.2.1, p. 801. The topology is induced by
all weighted Schwartz profiles, using the usual seminorms on the real Schwartz space.
Deviation: Positive real functions are represented by their logarithmic profiles. -/
abbrev PositiveRealExponentialDecay (I : Set ℝ) :=
  WithGeneratingSeminorms (logExponentialDecaySubmodule I)
    (fun i : I × ℕ × ℕ ↦
      (SchwartzMap.seminorm ℂ i.2.1 i.2.2).comp (logExponentialDecayTwist I i.1))

/-- Paper: Definition D.3.2.1, p. 801. The family of weighted profiles embeds
the decay space in a product of real Schwartz spaces. -/
theorem positiveRealExponentialDecay_isEmbedding (I : Set ℝ) (hne : I.Nonempty) :
    IsEmbedding (fun (f : PositiveRealExponentialDecay I) (a : I) ↦
      logExponentialDecayTwist I a f) := by
  let T : PositiveRealExponentialDecay I →ₗ[ℂ] (I → 𝓢(ℝ, ℂ)) :=
    LinearMap.pi (logExponentialDecayTwist I)
  have hp := withSeminorms_pi fun _ : I ↦ schwartz_withSeminorms ℂ ℝ ℂ
  have hsource := withGeneratingSeminorms_spec (logExponentialDecaySubmodule I)
    (fun i : I × ℕ × ℕ ↦
      (SchwartzMap.seminorm ℂ i.2.1 i.2.2).comp (logExponentialDecayTwist I i.1))
  change IsEmbedding T
  constructor
  · constructor
    refine hsource.topologicalSpace_eq_iInf.trans ?_
    refine Eq.trans ?_ (WithSeminorms.topologicalSpace_eq_iInf
      (t := TopologicalSpace.induced T inferInstance) (T.withSeminorms_induced hp)).symm
    rw [iInf_sigma, iInf_prod]
    rfl
  · intro f g h
    obtain ⟨a, ha⟩ := hne
    apply Subtype.ext
    funext x
    have hx := congrArg (fun F : 𝓢(ℝ, ℂ) ↦ F x) (congrFun h ⟨a, ha⟩)
    change logExponentialDecayTwist I ⟨a, ha⟩ f x = logExponentialDecayTwist I ⟨a, ha⟩ g x at hx
    rw [logExponentialDecayTwist_apply I ⟨a, ha⟩ f x,
      logExponentialDecayTwist_apply I ⟨a, ha⟩ g x] at hx
    exact mul_left_cancel₀ (by exact_mod_cast (Real.exp_pos (a * x)).ne') hx

variable (I : Set ℝ)

local notation "E" => PositiveRealExponentialDecay I
local notation "D" => StrongDual ℂ E

open scoped BoundedContinuousFunction

open scoped Distributions in
/-- A smooth test function supported in a fixed compact set includes continuously into the
space of profiles with Schwartz decay under every prescribed exponential weight. -/
def supportedToLogDecayCLM (I : Set ℝ) (hI : I.Nonempty) (K : Compacts ℝ) :
    𝓓_{K}(ℝ, ℂ) →L[ℂ] PositiveRealExponentialDecay I := by
  let J : 𝓓_{K}(ℝ, ℂ) →ₗ[ℂ] PositiveRealExponentialDecay I :=
    { toFun f := ⟨(f : ℝ → ℂ), mem_logExponentialDecaySubmodule_of_hasCompactSupport I
        f.hasCompactSupport f.contDiff⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  refine ⟨J, (positiveRealExponentialDecay_isEmbedding I hI).isInducing.continuous_iff.mpr ?_⟩
  apply continuous_pi
  intro a
  let w (x : ℝ) : ℂ := Real.exp ((a : ℝ) * x)
  have hw : ContDiff ℝ ∞ w :=
    Complex.ofRealCLM.contDiff.comp ((contDiff_const.mul contDiff_id).exp)
  let M : 𝓓_{K}(ℝ, ℂ) →L[ℂ] 𝓓_{K}(ℝ, ℂ) :=
    ContDiffMapSupportedIn.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) hw
  convert ((supportedToSchwartzCLM ℂ K).comp M).continuous using 1
  funext f
  ext x
  change logExponentialDecayTwist I a (show logExponentialDecaySubmodule I from J f) x = f x * w x
  rw [logExponentialDecayTwist_apply I a _ x]
  exact mul_comm _ _

/-- Paper: Lemma D.3.2.3(1), p. 802. The image in the product is closed because the
compatibility equations between weighted profiles are closed pointwise conditions. -/
private theorem isClosed_range_logExponentialDecayTwist (I : Set ℝ) (a : I) :
    IsClosed (range (fun (f : PositiveRealExponentialDecay I) (b : I) ↦
      logExponentialDecayTwist I b f)) := by
  let w (b : I) (x : ℝ) : ℂ := Real.exp ((b : ℝ) * x)
  have hw (b : I) (x : ℝ) : w b x ≠ 0 := by
    dsimp [w]
    exact_mod_cast (Real.exp_pos ((b : ℝ) * x)).ne'
  have heval (b : I) (x : ℝ) : Continuous (fun g : I → 𝓢(ℝ, ℂ) ↦ g b x) :=
    (continuous_eval_const (F := ℝ →ᵇ ℂ) x).comp
      ((SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ).continuous.comp (continuous_apply b))
  have hrange : range (fun (f : PositiveRealExponentialDecay I) (b : I) ↦
      logExponentialDecayTwist I b f) =
      ⋂ (b : I) (x : ℝ), {g : I → 𝓢(ℝ, ℂ) | w a x * g b x = w b x * g a x} := by
    ext g
    simp only [mem_iInter, mem_ofPred_eq, mem_range]
    constructor
    · rintro ⟨f, rfl⟩ b x
      rw [logExponentialDecayTwist_apply I b f x, logExponentialDecayTwist_apply I a f x]
      exact mul_left_comm _ _ _
    · intro hg
      let f (x : ℝ) := g a x / w a x
      have hmatch (b : I) (x : ℝ) : w b x * f x = g b x := by
        rw [show w b x * f x = (w b x * g a x) / w a x by simp [f, mul_div_assoc]]
        exact (div_eq_iff (hw a x)).mpr ((hg b x).symm.trans (mul_comm _ _))
      have hf : f ∈ logExponentialDecaySubmodule I := by
        apply (Submodule.mem_iInf _).mpr
        intro b
        exact ⟨g b, funext fun x ↦ (hmatch b x).symm⟩
      refine ⟨⟨f, hf⟩, ?_⟩
      funext b
      ext x
      rw [logExponentialDecayTwist_apply]
      exact hmatch b x
  rw [hrange]
  exact isClosed_iInter fun b ↦ isClosed_iInter fun x ↦
    isClosed_eq (continuous_const.mul (heval b x)) (continuous_const.mul (heval a x))

/-- Paper: Lemma D.3.2.3(1), p. 802. The closed embedding into the product of complete
Schwartz spaces gives completeness for the additive uniformity. -/
private theorem positiveRealExponentialDecay_complete (I : Set ℝ) (hne : I.Nonempty) :
    CompleteSpace (PositiveRealExponentialDecay I) := by
  have : CompleteSpace 𝓢(ℝ, ℂ) := completeSpace_schwartzMap
  let T : PositiveRealExponentialDecay I →ₗ[ℂ] (I → 𝓢(ℝ, ℂ)) :=
    LinearMap.pi (logExponentialDecayTwist I)
  have hT : IsUniformInducing T := AddMonoidHom.isUniformInducing_of_isInducing
    (f := T.toAddMonoidHom) (positiveRealExponentialDecay_isEmbedding I hne).isInducing
  obtain ⟨a, ha⟩ := hne
  exact (completeSpace_iff_isComplete_range hT).mpr
    (isClosed_range_logExponentialDecayTwist I ⟨a, ha⟩).isComplete

/-- A finite sum of Schwartz seminorms controlling the derivatives of an exponential twist
on the half-line where that exponential is at most one. -/
private def exponentialTwistBound (t : ℝ) (k n : ℕ) : Seminorm ℂ 𝓢(ℝ, ℂ) :=
  ∑ i ∈ Finset.range (n + 1),
    ((n.choose i : ℝ≥0) * ‖t‖₊ ^ i) • SchwartzMap.seminorm ℂ k (n - i)

private theorem exponentialTwistBound_continuous (t : ℝ) (k n : ℕ) :
    Continuous (exponentialTwistBound t k n) := by
  apply Seminorm.continuous_finsetSum
  intro i _
  exact ((schwartz_withSeminorms ℂ ℝ ℂ).continuous_seminorm (k, n - i)).const_smul _

/-- Leibniz's formula bounds the weighted derivative wherever the exponential is at most one. -/
private theorem weighted_deriv_exp_smul_le (t x : ℝ) (hx : t * x ≤ 0) (k n : ℕ) (g : 𝓢(ℝ, ℂ)) :
    |x| ^ k * ‖iteratedDeriv n ((fun y ↦ Real.exp (t * y)) • ⇑g) x‖ ≤
      exponentialTwistBound t k n g := by
  have hexp : ContDiff ℝ n (fun y : ℝ ↦ Real.exp (t * y)) := by fun_prop
  have hderiv := iteratedDerivWithin_smul (Set.mem_univ x) uniqueDiffOn_univ
    hexp.contDiffAt.contDiffWithinAt (g.smooth n).contDiffAt.contDiffWithinAt
  simp only [iteratedDerivWithin_univ, iteratedDeriv_exp_const_mul] at hderiv
  rw [hderiv]
  refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (pow_nonneg (abs_nonneg x) k)).trans ?_
  rw [Finset.mul_sum]
  simp only [exponentialTwistBound, FunLike.coe_sum, Finset.sum_apply, smul_apply, NNReal.smul_def,
    NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_pow, coe_nnNorm, smul_eq_mul]
  apply Finset.sum_le_sum
  intro i hi
  rw [RCLike.norm_nsmul (K := ℝ), nsmul_eq_mul, norm_smul, norm_mul,
    Real.norm_of_nonneg (Real.exp_pos _).le, norm_pow]
  have h := g.le_seminorm' ℂ k (n - i) x
  have hcoeff : 0 ≤ (n.choose i : ℝ) * ‖t‖ ^ i := by positivity
  calc
    _ = ((n.choose i : ℝ) * ‖t‖ ^ i) * (Real.exp (t * x) *
        (|x| ^ k * ‖iteratedDeriv (n - i) g x‖)) := by ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hcoeff
      exact (mul_le_of_le_one_left (by positivity) (Real.exp_le_one_iff.mpr hx)).trans h

/-- Paper: Lemma D.3.2.3(1), p. 802. On each half-line the corresponding endpoint
controls the Schwartz seminorm of every intermediate twist. -/
private theorem exponentialTwist_seminorm_le {I : Set ℝ} (a b c : I) (hba : b ≤ a) (hac : a ≤ c)
    (k n : ℕ) (f : logExponentialDecaySubmodule I) :
    SchwartzMap.seminorm ℂ k n (logExponentialDecayTwist I a f) ≤
      exponentialTwistBound (a - b : ℝ) k n (logExponentialDecayTwist I b f) +
      exponentialTwistBound (a - c : ℝ) k n (logExponentialDecayTwist I c f) := by
  have changeWeight (d : I) : ⇑(logExponentialDecayTwist I a f) =
      (fun x ↦ Real.exp (((a : ℝ) - d) * x)) • ⇑(logExponentialDecayTwist I d f) := by
    funext x
    change _ = Real.exp (((a : ℝ) - d) * x) • logExponentialDecayTwist I d f x
    rw [Complex.real_smul, logExponentialDecayTwist_apply,
      logExponentialDecayTwist_apply, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
    congr 3
    ring
  apply SchwartzMap.seminorm_le_bound' ℂ k n _ (add_nonneg (apply_nonneg _ _) (apply_nonneg _ _))
  intro x
  rcases le_total x 0 with hx | hx
  · rw [changeWeight b]
    exact (weighted_deriv_exp_smul_le _ _ (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hba) hx)
      k n _).trans (le_add_of_nonneg_right (apply_nonneg _ _))
  · rw [changeWeight c]
    exact (weighted_deriv_exp_smul_le _ _ (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hac) hx)
      k n _).trans (le_add_of_nonneg_left (apply_nonneg _ _))

/-- Paper: Lemma D.3.2.3(1), p. 802. Two countable sequences of exponents bracket
every exponent of the interval and suffice to generate the topology. -/
private theorem exponentialDecay_metrizable (I : Set ℝ) (hInt : OrdConnected I) (hne : I.Nonempty) :
    MetrizableSpace (PositiveRealExponentialDecay I) := by
  have : Nonempty I := hne.to_subtype
  obtain ⟨lo, -, hlo⟩ := exists_seq_antitone_tendsto_atTop_atBot I
  obtain ⟨hi, -, hhi⟩ := exists_seq_monotone_tendsto_atTop_atTop I
  let d : ℕ ⊕ ℕ → I := Sum.elim lo hi
  let p (i : I × ℕ × ℕ) :=
    (SchwartzMap.seminorm ℂ i.2.1 i.2.2).comp (logExponentialDecayTwist I i.1)
  let q (j : (ℕ ⊕ ℕ) × ℕ × ℕ) := p (d j.1, j.2)
  let X := WithGeneratingSeminorms (logExponentialDecaySubmodule I) q
  let Y := PositiveRealExponentialDecay I
  have hp := withGeneratingSeminorms_spec (logExponentialDecaySubmodule I) p
  have hq := withGeneratingSeminorms_spec (logExponentialDecaySubmodule I) q
  let T (a : I) : X →ₗ[ℂ] 𝓢(ℝ, ℂ) := logExponentialDecayTwist I a
  have hc (j : ℕ ⊕ ℕ) : Continuous (T (d j)) := by
    apply (schwartz_withSeminorms ℂ ℝ ℂ).continuous_of_continuous_comp
    intro i
    exact hq.continuous_seminorm (j, i)
  let toFull : X →ₗ[ℂ] Y := LinearMap.id
  have hfull : Continuous toFull := by
    apply hp.continuous_of_continuous_comp
    rintro ⟨a, k, n⟩
    obtain ⟨l, hl⟩ := (hlo.eventually (eventually_le_atBot a)).exists
    obtain ⟨r, hr⟩ := (hhi.eventually (eventually_ge_atTop a)).exists
    let B := ((exponentialTwistBound (a - lo l : ℝ) k n).comp (T (lo l))) +
      ((exponentialTwistBound (a - hi r : ℝ) k n).comp (T (hi r)))
    have hB : Continuous B :=
      ((exponentialTwistBound_continuous _ _ _).comp (hc (.inl l))).add
        ((exponentialTwistBound_continuous _ _ _).comp (hc (.inr r)))
    exact Seminorm.continuous_of_le hB (fun f ↦ exponentialTwist_seminorm_le a _ _ hl hr k n f)
  let toCountable : Y →ₗ[ℂ] X := LinearMap.id
  have hcountable : Continuous toCountable := by
    apply hq.continuous_of_continuous_comp
    intro j
    exact hp.continuous_seminorm (d j.1, j.2)
  let e : Y ≃ₜ X := ⟨Equiv.refl _, hcountable, hfull⟩
  have : FirstCountableTopology X := hq.firstCountableTopology
  have : FirstCountableTopology Y := e.isInducing.firstCountableTopology
  have : (uniformity Y).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  have : T2Space Y := (positiveRealExponentialDecay_isEmbedding I hne).t2Space
  exact UniformSpace.metrizableSpace

/-- Paper: Lemma D.3.2.3(1), p. 801. The positive-real decay space is Fréchet. -/
theorem positiveRealExponentialDecay_frechet (hInt : OrdConnected I) (hne : I.Nonempty) :
    IsFrechetTVS E := by
  exact ⟨inferInstance, inferInstance, exponentialDecay_metrizable I hInt hne,
    positiveRealExponentialDecay_complete I hne⟩

/-- A topologically embedded linear subspace inherits nuclearity through the
continuous linear equivalence with its range. -/
private theorem isNuclearTVS_of_linearEmbedding.{v, u} {X Y : Type u}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [PolynormableSpace ℂ X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    (f : X →ₗ[ℂ] Y) (hf : IsEmbedding f) (hY : IsNuclearTVS.{v, u} Y) :
    IsNuclearTVS.{v, u} X := by
  let := hY.1
  let := hY.2.1
  have hn := isNuclearTVS_submodule hY f.range
  let e := LinearEquiv.ofInjective f hf.injective
  have he : IsInducing e := IsInducing.subtypeVal.of_comp_iff.mp hf.isInducing
  let h := e.toEquiv.toHomeomorphOfIsInducing he
  let L : X ≃L[ℂ] f.range := ⟨e, h.continuous, h.continuous_symm⟩
  have : T2Space X := hf.t2Space
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro F _ _ _ _ _
  let cmp := (hn.2.2 F inferInstance inferInstance inferInstance inferInstance
    inferInstance).homeomorph
  let idF := ContinuousLinearMap.id ℂ F
  have hroundtrip (z : X ⊗[ℂ] F) :
      L.symm.toLinearMap.rTensor F (L.toLinearMap.rTensor F z) = z := by
    rw [← LinearMap.rTensor_comp_apply, show L.symm.toLinearMap.comp L.toLinearMap =
      LinearMap.id from LinearMap.ext L.symm_apply_apply, LinearMap.rTensor_id_apply]
  have hforward : Continuous (show ProjectiveTensor X F → InjectiveTensor X F from id) :=
    ((injectiveTensorMap_continuous L.symm.toContinuousLinearMap idF).comp
      (cmp.continuous.comp (projectiveTensorMap_continuous L.toContinuousLinearMap idF))).congr
      hroundtrip
  have hcmp : Continuous (show InjectiveTensor f.range F → ProjectiveTensor f.range F from id) :=
    cmp.continuous_symm.congr fun z ↦ cmp.apply_symm_apply z
  have hback : Continuous (show InjectiveTensor X F → ProjectiveTensor X F from id) :=
    ((projectiveTensorMap_continuous L.symm.toContinuousLinearMap idF).comp
      (hcmp.comp (injectiveTensorMap_continuous L.toContinuousLinearMap idF))).congr hroundtrip
  exact (⟨Equiv.refl (X ⊗[ℂ] F), hforward, hback⟩ :
    ProjectiveTensor X F ≃ₜ InjectiveTensor X F).isHomeomorph

-- The nuclearity argument uses only nonemptiness of the exponent set.
set_option linter.unusedVariables false in
/-- Paper: Lemma D.3.2.3(1), p. 801. The positive-real decay space is nuclear. -/
theorem positiveRealExponentialDecay_nuclear (hInt : OrdConnected I) (hne : I.Nonempty) :
    IsNuclearTVS E := by
  let e : EuclideanSpace ℝ (Fin 1) ≃L[ℝ] ℝ := PiLp.equivOfUnique 2 ℝ _
  let S := schwartzChangeVariable ℂ (F := ℂ) e
  have : PolynormableSpace ℂ 𝓢(ℝ, ℂ) := (schwartz_withSeminorms ℂ ℝ ℂ).toPolynormableSpace
  have hS : IsNuclearTVS 𝓢(ℝ, ℂ) :=
    isNuclearTVS_of_linearEmbedding S.toLinearMap S.toHomeomorph.isEmbedding
      (euclideanSchwartz_nuclear 1)
  let T : E →ₗ[ℂ] (I → 𝓢(ℝ, ℂ)) := LinearMap.pi (logExponentialDecayTwist I)
  exact isNuclearTVS_of_linearEmbedding T (positiveRealExponentialDecay_isEmbedding I hne)
    (isNuclearTVS_pi fun _ : I ↦ hS)

/-- Paper: Lemma D.3.2.3(1), p. 801. The positive-real decay space has the
Montel property and is barrelled. -/
theorem positiveRealExponentialDecay_montel (hInt : OrdConnected I) (hne : I.Nonempty) :
    BarrelledSpace ℂ E ∧ MontelSpace ℂ E := by
  have : MetrizableSpace E := exponentialDecay_metrizable I hInt hne
  have : CompleteSpace E := positiveRealExponentialDecay_complete I hne
  have : (uniformity E).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  have : MontelSpace ℂ 𝓢(ℝ, ℂ) := schwartzMap_real_montel
  refine ⟨inferInstance, ⟨fun S hclosed hS ↦ ?_⟩⟩
  let T : E →ₗ[ℂ] (I → 𝓢(ℝ, ℂ)) := LinearMap.pi (logExponentialDecayTwist I)
  have hT : IsEmbedding T := positiveRealExponentialDecay_isEmbedding I hne
  have hu := AddMonoidHom.isUniformInducing_of_isInducing (f := T.toAddMonoidHom) hT.isInducing
  let K (a : I) := closure (logExponentialDecayTwist I a '' S)
  have hK (a : I) : IsCompact (K a) := by
    let L : E →L[ℂ] 𝓢(ℝ, ℂ) := ⟨logExponentialDecayTwist I a, (continuous_apply a).comp hT.continuous⟩
    exact MontelSpace.isCompact_of_isClosed_of_isVonNBounded ℂ isClosed_closure (hS.image L).closure
  apply TotallyBounded.isCompact_of_isClosed _ hclosed
  apply (totallyBounded_image_iff hu).mp
  apply (isCompact_univ_pi hK).totallyBounded.subset
  rintro _ ⟨f, hf, rfl⟩ a _
  exact subset_closure (mem_image_of_mem _ hf)

/-- Paper: Lemma D.3.2.3(2), p. 801. The strong dual is complete. -/
theorem positiveRealExponentialDecay_strongDual_complete (hInt : OrdConnected I) (hne : I.Nonempty) :
    CompleteSpace D := by
  obtain ⟨_, _, hmetric, _⟩ := positiveRealExponentialDecay_frechet I hInt hne
  infer_instance

section StrongDualNuclearity

/-! We use the local Banach integral criterion directly. For a bounded set of profiles, its
closure is compact by the Montel property. Interpolating jets on a grid gives rank O(n³)
approximations on this compact set. The sixth-power rescaled errors form another bounded set,
so passing to a stronger seminorm on the dual makes the transposed errors O(n⁻⁶) in operator
norm. The rank-weighted norms of the successive differences are therefore summable. -/

open Module

open scoped Pointwise in
/-- A finite-rank map into a space of dimension d costs at most d times its
operator norm in the injective-tensor bound for its evaluation form. -/
private theorem finite_rank_evaluation_bound {X Y : Type*} [NormedAddCommGroup X]
    [NormedSpace ℂ X] [NormedAddCommGroup Y] [NormedSpace ℂ Y] (T : X →L[ℂ] Y)
    (V : Submodule ℂ Y) [FiniteDimensional ℂ V] (hV : ∀ x, T x ∈ V)
    (L : X ⊗[ℂ] StrongDual ℂ Y →ₗ[ℂ] ℂ) (hL : ∀ x φ, L (x ⊗ₜ[ℂ] φ) = φ (T x))
    (z : X ⊗[ℂ] StrongDual ℂ Y) : ‖L z‖ ≤ finrank ℂ V * ‖T‖ * injectiveTensorNorm _ _ z := by
  classical
  let S := Metric.closedBall (0 : V) 1
  have hS : S ∈ 𝓝 0 := Metric.closedBall_mem_nhds 0 one_pos
  have hspan : Submodule.span ℂ S = ⊤ := by
    refine top_unique fun x _ ↦ ?_
    obtain ⟨c, hc⟩ : ∃ c : ℂ, x ∈ c • S := by
      simpa using (absorbent_nhds_zero (𝕜 := ℂ) hS x).exists
    obtain ⟨y, hy, rfl⟩ := hc
    exact Submodule.smul_mem _ _ (Submodule.subset_span hy)
  obtain ⟨b, hb, hc⟩ := exists_basis_compact_coord_le (isCompact_closedBall (0 : V) 1) hspan
  let φ (i) := (b.coord i).toContinuousLinearMap.comp (T.codRestrict V hV)
  have hφ (i) : ‖φ i‖ ≤ ‖T‖ := by
    have hcoord : ‖(b.coord i).toContinuousLinearMap‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_le_of_unit_norm zero_le_one (fun x hx ↦ hc i x
        (mem_closedBall_zero_iff.mpr hx.le))
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    exact ((b.coord i).toContinuousLinearMap.le_opNorm _).trans
      ((mul_le_of_le_one_left (norm_nonneg _) hcoord).trans (T.le_opNorm x))
  have hb' (i) : ‖(b i : Y)‖ ≤ 1 := mem_closedBall_zero_iff.mp (hb i)
  have heq (w : X ⊗[ℂ] StrongDual ℂ Y) : L w = ∑ i, tensorDualOperator w (φ i) (b i) := by
    induction w using TensorProduct.inductionOn with
    | tmul x ψ =>
      rw [hL]
      have hh := congrArg (fun v : V ↦ ψ v.val) (b.sum_repr ((T.codRestrict V hV) x))
      change ψ (↑(∑ i, _ • b i) : Y) = ψ (T x) at hh
      simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, map_sum, map_smul, smul_eq_mul] at hh
      simpa [φ, tensorDualOperator_tmul, Basis.coord_apply] using hh.symm
    | add u v hu hv => simp [hu, hv, Finset.sum_add_distrib]
  obtain ⟨A, hA, hε⟩ := injectiveTensorNorm_eq_opNorm z
  rw [heq, hε]
  apply (norm_sum_le _ _).trans
  apply le_trans (Finset.sum_le_sum (g := fun _ ↦ ‖A‖ * ‖T‖) ?_) (by simp; ring_nf; rfl)
  intro i _
  change ‖(tensorDualOperator z (φ i)) (b i)‖ ≤ _
  rw [← hA]
  exact ((A (φ i)).unit_le_opNorm _ (hb' i)).trans ((A.le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (hφ i) (norm_nonneg _)))

/-- Norm-convergent finite-rank approximations with summable rank-weighted
increments give an integral evaluation form. -/
private theorem integral_evaluation_of_approximants {X Y : Type*} [NormedAddCommGroup X]
    [NormedSpace ℂ X] [NormedAddCommGroup Y] [NormedSpace ℂ Y] (T : X →L[ℂ] Y)
    (S : ℕ → X →L[ℂ] Y) (h0 : S 0 = 0) (hT : Tendsto S atTop (𝓝 T))
    (V : ℕ → Submodule ℂ Y) [∀ n, FiniteDimensional ℂ (V n)]
    (hV : ∀ n x, (S (n+1) - S n) x ∈ V n)
    (hs : Summable fun n ↦ (finrank ℂ (V n) : ℝ) * ‖S (n+1) - S n‖) :
    IsIntegralBilinearForm (fun x (φ : StrongDual ℂ Y) ↦ φ (T x)) := by
  let F := StrongDual ℂ Y
  let L (A : X →L[ℂ] Y) : X ⊗[ℂ] F →ₗ[ℂ] ℂ := TensorProduct.lift
    (LinearMap.mk₂ ℂ (fun x (φ : F) ↦ φ (A x))
      (by intros; simp) (by intros; simp) (by intros; rfl) (by intros; rfl))
  have hsub (A B : X →L[ℂ] Y) : L (A - B) = L A - L B := by ext x φ; simp [L]
  have hzero : L 0 = 0 := by ext x φ; simp [L]
  have hc (z : X ⊗[ℂ] F) : Continuous (fun A ↦ L A z) := by
    induction z using TensorProduct.inductionOn with
    | tmul x φ => exact φ.continuous.comp (ContinuousLinearMap.apply ℂ Y x).continuous
    | add z w hz hw => simp only [map_add]; exact hz.add hw
  let ε := injectiveTensorNorm X F
  let t (n : ℕ) : ℝ := (finrank ℂ (V n) : ℝ) * ‖S (n + 1) - S n‖
  let C : ℝ≥0 := ⟨∑' n, t n, tsum_nonneg (fun n ↦ by dsimp only [t]; positivity)⟩
  have hbound (z : X ⊗[ℂ] F) : ‖L T z‖ ≤ C * ε z := by
    apply le_of_tendsto (((hc z).tendsto T).comp hT).norm
    apply Eventually.of_forall
    intro n
    have heq := Finset.sum_range_sub (fun k ↦ L (S k) z) n
    rw [h0, hzero, LinearMap.zero_apply, sub_zero] at heq
    change ‖L (S n) z‖ ≤ _
    rw [← heq]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ k ∈ Finset.range n, t k * ε z := by
        apply Finset.sum_le_sum
        intro k _
        have hh := finite_rank_evaluation_bound _ (V k) (hV k) (L (S (k+1) - S k))
          (fun _ _ ↦ rfl) z
        rwa [hsub, LinearMap.sub_apply] at hh
      _ = (∑ k ∈ Finset.range n, t k) * ε z := Finset.sum_mul .. |>.symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (hs.sum_le_tsum _ (fun k _ ↦ by dsimp [t]; positivity))
        (apply_nonneg _ _)
  let : PolynormableSpace ℂ X := (norm_withSeminorms ℂ X).toPolynormableSpace
  let : PolynormableSpace ℂ F := (norm_withSeminorms ℂ F).toPolynormableSpace
  let hI := withGeneratingSeminorms_spec (X ⊗[ℂ] F)
    (fun UV : {U : Set X // U ∈ 𝓝 0} × {V : Set F // V ∈ 𝓝 0} ↦
      injectiveTensorSeminorm UV.1 UV.2)
  have hε : Continuous (show InjectiveTensor X F → ℝ from ε) := hI.continuous_seminorm
    (⟨Metric.closedBall 0 1, Metric.closedBall_mem_nhds 0 one_pos⟩,
     ⟨Metric.closedBall 0 1, Metric.closedBall_mem_nhds 0 one_pos⟩)
  let L' : InjectiveTensor X F →ₗ[ℂ] ℂ := L T
  have hL : Continuous L' := (norm_withSeminorms ℂ ℂ).continuous_of_continuous_comp L' fun _ ↦
    Seminorm.continuous_of_le (q := C • ε) (hε.const_smul C) hbound
  exact ⟨⟨L', hL⟩, fun _ _ ↦ rfl⟩

/-- Cubic rank growth and sixth-order error decay suffice for summability of the
rank-weighted increments. -/
private theorem integral_evaluation_of_cubic_approximation {X Y : Type*} [NormedAddCommGroup X]
    [NormedSpace ℂ X] [NormedAddCommGroup Y] [NormedSpace ℂ Y] (T : X →L[ℂ] Y)
    (S : ℕ → X →L[ℂ] Y) (V : ℕ → Submodule ℂ Y) [∀ n, FiniteDimensional ℂ (V n)]
    (hV : ∀ n x, S n x ∈ V n) (hd : ∀ n, finrank ℂ (V n) ≤ (2*n^2+1)*n)
    (K : ℝ) (hK : 0 ≤ K) (herr : ∀ n, ‖T - S n‖ ≤ K / ((n : ℝ) + 1)^6) :
    IsIntegralBilinearForm (fun x (φ : StrongDual ℂ Y) ↦ φ (T x)) := by
  let W (n : ℕ) := V (n+1) ⊔ V n
  have : ∀ n, FiniteDimensional ℂ (W n) := fun n ↦ (V (n+1)).finiteDimensional_sup _
  apply integral_evaluation_of_approximants T S _ _ W
  · intro n x
    exact Submodule.sub_mem _ (Submodule.mem_sup_left (hV (n+1) x))
      (Submodule.mem_sup_right (hV n x))
  · have hs : Summable (fun n : ℕ ↦ (((n : ℝ) + 1)^3)⁻¹) := by
      simpa only [Function.comp_def, Nat.cast_succ] using
        (Real.summable_nat_pow_inv.mpr (by decide : 1 < 3)).comp_injective Nat.succ_injective
    apply (hs.mul_left (12*K)).of_nonneg_of_le (fun _ ↦ by positivity)
    intro n
    let a : ℝ := n + 1
    have ha : (1 : ℝ) ≤ a := by dsimp [a]; linarith [Nat.cast_nonneg (α := ℝ) n]
    have ha₀ : 0 < a := by linarith
    have hdim : (finrank ℂ (W n) : ℝ) ≤ 6 * a^3 := by
      have h₁ := ((V (n+1)).finrank_add_le_finrank_add_finrank (V n)).trans
        (add_le_add (hd (n+1)) (hd n))
      have h₂ : (finrank ℂ (W n) : ℝ) ≤ (2*a^2+1)*a + (2*(n:ℝ)^2+1)*n := by dsimp only [W, a]; exact_mod_cast h₁
      have hn : (n : ℝ) ≤ a := by dsimp [a]; linarith
      have h₃ : (2*(n:ℝ)^2+1)*n ≤ (2*a^2+1)*a := by gcongr
      have h₄ : a ≤ a^3 := by simpa using pow_le_pow_right₀ ha (show 1 ≤ 3 by decide)
      linarith
    have hnorm : ‖S (n+1) - S n‖ ≤ 2 * (K / a^6) := by
      have hn₁ : K / (((n+1 : ℕ) : ℝ) + 1)^6 ≤ K / a^6 := by
        gcongr; dsimp [a]; push_cast; linarith
      calc
        _ ≤ ‖S (n+1) - T‖ + ‖T - S n‖ := by
          simpa only [← dist_eq_norm] using dist_triangle (S (n+1)) T (S n)
        _ ≤ K / a^6 + K / a^6 := add_le_add
          ((norm_sub_rev ..).trans_le ((herr (n+1)).trans hn₁)) (herr n)
        _ = _ := (two_mul _).symm
    calc
      _ ≤ (6*a^3) * (2 * (K / a^6)) := mul_le_mul hdim hnorm (norm_nonneg _) (by positivity)
      _ = _ := by change _ = (12*K) * (a^3)⁻¹; field_simp; ring
  · have hz : finrank ℂ (V 0) = 0 := Nat.eq_zero_of_le_zero (by simpa using hd 0)
    have hbot := Submodule.finrank_eq_zero.mp hz
    ext x
    exact (show S 0 x ∈ (⊥ : Submodule ℂ Y) from hbot ▸ hV 0 x)
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 6
    have h' := h.const_mul K
    simp only [zero_pow (by decide : 6 ≠ 0), mul_zero, one_div, inv_pow] at h'
    apply squeeze_zero (fun _ ↦ norm_nonneg _) _ h'
    intro n
    rw [norm_sub_rev]
    simpa [div_eq_mul_inv] using herr n

/-- Transposing finite interpolation on a test set approximates the local
Banach comparison of the strong dual in operator norm. -/
private theorem dual_local_integral_of_interpolation {X : Type*} [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] (p q : Seminorm ℂ (StrongDual ℂ X)) (hqp : q ≤ p)
    {B : Set X} (K : ℝ) (hK : 0 ≤ K) (hq : ∀ (f : StrongDual ℂ X) (r : ℝ), 0 ≤ r →
      (∀ x ∈ B, ‖f x‖ ≤ r) → q f ≤ K * r)
    (d : ℕ → ℕ) (b : ∀ n, Fin (d n) → B) (c : ∀ n, Fin (d n) → StrongDual ℂ X)
    (hd : ∀ n, d n ≤ (2*n^2+1)*n) (hb : ∀ (f : StrongDual ℂ X) (x : B), ‖f x‖ ≤ p f)
    (hr : ∀ (f : StrongDual ℂ X) (n : ℕ) (x : B),
      ‖f (x.val - ∑ i, c n i x.val • (b n i).val)‖ ≤ p f / ((n : ℝ) + 1)^6) :
    IsIntegralBilinearForm (fun (v : LocalBanach p) (φ : StrongDual ℂ (LocalBanach q)) ↦
      φ (localBanachMap p q hqp v)) := by
  classical
  let j : StrongDual ℂ X →ₗ[ℂ] LocalBanach q := Completion.toComplL.toLinearMap.comp
    (show StrongDual ℂ X →ₗ[ℂ] WithLocalSeminorm q from LinearMap.id)
  let u (x : B) : WithLocalSeminorm p →L[ℂ] ℂ :=
    (show WithLocalSeminorm p →ₗ[ℂ] ℂ from (ContinuousLinearMap.coeLM ℂ).flip x.val).mkContinuous
      1 (fun f ↦ by rw [one_mul]; exact hb f x)
  let S (n : ℕ) : LocalBanach p →L[ℂ] LocalBanach q :=
    ∑ i, (u (b n i)).fromCompletion.smulRight (j (c n i))
  let V (n : ℕ) := Submodule.span ℂ (range fun i ↦ j (c n i))
  have : ∀ n, FiniteDimensional ℂ (V n) := fun n ↦ FiniteDimensional.span_of_finite ℂ (finite_range _)
  refine integral_evaluation_of_cubic_approximation _ S V ?_ ?_ K hK ?_
  · intro n x
    rw [show S n x = ∑ i, (u (b n i)).fromCompletion x • j (c n i) by simp [S]]
    exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _
      (Submodule.subset_span (mem_range_self i))
  · intro n
    exact (finrank_range_le_card (R := ℂ) (fun i ↦ j (c n i))).trans (by simpa using hd n)
  · intro n
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro x
    induction x using Completion.induction_on with
    | hp => exact isClosed_le (by fun_prop) (by fun_prop)
    | ih x =>
      let f : StrongDual ℂ X := x
      let g : StrongDual ℂ X := f - ∑ i, f (b n i) • c n i
      have heq : (localBanachMap p q hqp - S n) (x : LocalBanach p) = j g := by
        rw [sub_apply, localBanachMap_coe]
        change j f - S n (x : LocalBanach p) = j (f - ∑ i, f (b n i) • c n i)
        simp only [map_sub, map_sum, map_smul, S, sum_apply,
          ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.fromCompletion_apply_coe]
        rfl
      have hg : q g ≤ K * (p f / ((n : ℝ) + 1)^6) := by
        apply hq _ _ (div_nonneg (apply_nonneg _ _) (by positivity))
        intro y hy
        have hh := hr f n ⟨y, hy⟩
        simpa [g, sum_apply, smul_eq_mul, mul_comm] using hh
      rw [heq, show ‖j g‖ = q g from localBanach_norm_coe q g, localBanach_norm_coe]
      exact hg.trans_eq (by ring)

/-- Changing exponential weight preserves the vanishing of a jet. -/
private theorem decay_twist_jet_zero {I : Set ℝ} (a b : I) (f : PositiveRealExponentialDecay I)
    (y : ℝ) (j : ℕ) (h : ∀ m ≤ j, iteratedDeriv m (logExponentialDecayTwist I a f) y = 0) :
    iteratedDeriv j (logExponentialDecayTwist I b f) y = 0 := by
  let w (x : ℝ) := Real.exp (((b : ℝ) - a) * x)
  have hw : ContDiff ℝ j w := by dsimp [w]; fun_prop
  have he : ⇑(logExponentialDecayTwist I b f) = w • ⇑(logExponentialDecayTwist I a f) := by
    funext x
    change _ = w x • logExponentialDecayTwist I a f x
    rw [Complex.real_smul, logExponentialDecayTwist_apply I b f, logExponentialDecayTwist_apply I a f,
      ← mul_assoc, ← Complex.ofReal_mul]
    simp only [w, ← Real.exp_add, sub_mul, sub_add_cancel]
  have hh := iteratedDerivWithin_smul (mem_univ y) uniqueDiffOn_univ hw.contDiffAt.contDiffWithinAt
    ((logExponentialDecayTwist I a f).smooth j).contDiffAt.contDiffWithinAt
  simp only [iteratedDerivWithin_univ] at hh
  rw [he, hh]
  exact Finset.sum_eq_zero fun i _ ↦ by rw [h _ (Nat.sub_le ..)]; simp

/-- Each jet observation is a continuous linear functional of the profile. -/
private theorem exists_decay_jet {I : Set ℝ} (a : I) (y : ℝ) (j : ℕ) :
    ∃ u : StrongDual ℂ (PositiveRealExponentialDecay I),
      ∀ f, u f = iteratedDeriv j (logExponentialDecayTwist I a f) y := by
  let T : PositiveRealExponentialDecay I →L[ℂ] 𝓢(ℝ, ℂ) := ⟨logExponentialDecayTwist I a,
    (continuous_apply a).comp (positiveRealExponentialDecay_isEmbedding I ⟨a, a.property⟩).continuous⟩
  suffices H : ∃ u : StrongDual ℂ 𝓢(ℝ, ℂ), ∀ g, u g = iteratedDeriv j g y by
    obtain ⟨u, hu⟩ := H
    exact ⟨u.comp T, fun f ↦ hu (T f)⟩
  induction j with
  | zero => exact ⟨(BoundedContinuousFunction.evalCLM ℂ y).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ), fun _ ↦ rfl⟩
  | succ j ih =>
    obtain ⟨u, hu⟩ := ih
    exact ⟨u.comp (SchwartzMap.derivCLM ℂ ℂ), fun g ↦ (hu _).trans (by rw [iteratedDeriv_succ']; rfl)⟩

/-- On a compact set of profiles, interpolating its observed jets gives finite-rank
operators of cubic rank whose errors, multiplied by the sixth power of the stage,
still range over a bounded set. -/
private theorem decay_compact_approximants {I : Set ℝ} (a : I)
    {B : Set (PositiveRealExponentialDecay I)} (hB : IsCompact B) :
    ∃ (d : ℕ → ℕ) (b : ∀ n, Fin (d n) → B) (c : ∀ n, Fin (d n) → StrongDual ℂ
      (PositiveRealExponentialDecay I)),
      (∀ n, d n ≤ (2 * n ^ 2 + 1) * n) ∧
      IsVonNBounded ℂ (range fun z : ℕ × B ↦ (((z.1 : ℂ) + 1) ^ 6) •
        (z.2.val - ∑ i, c z.1 i z.2.val • (b z.1 i).val)) := by
  classical
  let X := PositiveRealExponentialDecay I
  let idx (n : ℕ) := Fin (2 * n ^ 2 + 1) × Fin n
  choose u hu using exists_decay_jet a
  let J (n : ℕ) : X →L[ℂ] (idx n → ℂ) := ContinuousLinearMap.pi
    fun i ↦ u ((i.1.val : ℝ) / n - n) i.2.val
  choose d b v hd hv hj using fun n ↦ exists_compact_interpolant hB (J n)
  let c (n : ℕ) (i : Fin (d n)) := (v n i).comp (J n)
  have hrank (n : ℕ) : d n ≤ (2 * n ^ 2 + 1) * n := by
    simpa [idx, finrank_pi] using hd n
  refine ⟨d, b, c, hrank, ?_⟩
  let R (n : ℕ) (f : X) : X := f - ∑ i, c n i f • (b n i).val
  have hjR (n : ℕ) (f : B) : J n (R n f.val) = 0 := by
    simp only [R, map_sub, map_sum, map_smul, sub_eq_zero]
    exact (hj n f f.property).symm
  let p (i : I × ℕ × ℕ) : Seminorm ℂ X := (SchwartzMap.seminorm ℂ i.2.1 i.2.2).comp
    (logExponentialDecayTwist I i.1)
  have hp : WithSeminorms («E» := X) p := withGeneratingSeminorms_spec (logExponentialDecaySubmodule I) _
  have hBb : IsVonNBounded ℂ B := hB.isVonNBounded (𝕜 := ℂ)
  choose M hm hM using hp.isVonNBounded_iff_seminorm_bounded.mp hBb
  have hrough (s : I × ℕ × ℕ) (n : ℕ) (f : B) :
      p s (R n f.val) ≤ (1 + (d n : ℝ)) * M s := by
    apply (map_sub_le_add (p s) _ _).trans
    rw [add_mul, one_mul]
    apply add_le_add (hM s f f.property).le
    apply (Finset.le_sum_of_subadditive (p s) (map_zero _).le (map_add_le_add _) _ _).trans
    apply le_trans (Finset.sum_le_sum (g := fun _ ↦ M s) ?_) (by simp)
    intro i _
    rw [map_smul_eq_mul]
    exact (mul_le_of_le_one_left (apply_nonneg _ _) (hv n i f f.property)).trans
      (hM s _ (b n i).property).le
  apply hp.isVonNBounded_iff_seminorm_bounded.mpr
  rintro ⟨w, k, l⟩
  let L := l + (9 + k) + 1
  let A := M (w, 0, l + (9 + k)) + M (w, 9 + k, l)
  let C := ((L : ℝ) + 1) ^ 6 * ((1 + ((2 * (L : ℝ) ^ 2 + 1) * L)) * M (w, k, l))
  have hC : 0 ≤ C := by have := hm (w,k,l); dsimp [C]; positivity
  have hA : 0 ≤ A := add_nonneg (hm _).le (hm _).le
  refine ⟨C + 256 * A + 1, by positivity, ?_⟩
  rintro _ ⟨⟨n, f⟩, rfl⟩
  change p (w, k, l) ((((n : ℂ) + 1) ^ 6) • R n f.val) < _
  rw [map_smul_eq_mul, norm_pow, show ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 by
    exact_mod_cast Complex.norm_natCast (n + 1)]
  have hd' : (d n : ℝ) ≤ (2 * (n : ℝ) ^ 2 + 1) * n := by exact_mod_cast hrank n
  by_cases hn : n < L
  · have hn' : (n : ℝ) ≤ L := by exact_mod_cast hn.le
    have hle : ((n : ℝ) + 1) ^ 6 * p (w, k, l) (R n f.val) ≤ C := by
      dsimp only [C]
      gcongr
      exact (hrough _ n f).trans (mul_le_mul_of_nonneg_right
        (add_le_add le_rfl (hd'.trans (by gcongr))) (hm _).le)
    linarith
  · have hn' : 0 < n := by dsimp [L] at hn; omega
    have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn'
    let g := logExponentialDecayTwist I w (R n f.val)
    have hg := schwartz_grid_estimate g n k l 9 hn' (by dsimp [L] at hn; omega) (by
      intro i j hj'
      apply decay_twist_jet_zero a w
      intro t ht
      have h := congrFun (hjR n f) (i, ⟨t, by omega⟩)
      exact (hu _ _ _).symm.trans h)
    change (n : ℝ) ^ 9 * p (w, k, l) (R n f.val) ≤ p (w, 0, l + (9 + k)) (R n f.val) +
      p (w, 9 + k, l) (R n f.val) at hg
    have hd'' : 1 + (d n : ℝ) ≤ 4 * (n : ℝ) ^ 3 := by
      have hcub : (n : ℝ) ≤ (n : ℝ)^3 := by simpa using pow_le_pow_right₀ h1 (show 1 ≤ 3 by decide)
      linarith
    have hh : (n : ℝ) ^ 9 * p (w,k,l) (R n f.val) ≤ 4 * (n : ℝ) ^ 3 * A :=
      hg.trans <| (add_le_add (hrough _ _ _) (hrough _ _ _)).trans (by
        rw [← mul_add]; exact mul_le_mul_of_nonneg_right hd'' hA)
    have hh' : (n : ℝ) ^ 6 * p (w,k,l) (R n f.val) ≤ 4 * A := by
      apply le_of_mul_le_mul_left (a := (n : ℝ) ^ 3) _ (by positivity)
      convert hh using 1 <;> ring
    have hh'' : ((n : ℝ) + 1) ^ 6 ≤ 64 * (n : ℝ) ^ 6 := by
      have h := pow_le_pow_left₀ (by positivity : 0 ≤ (n : ℝ) + 1)
        (show (n : ℝ) + 1 ≤ 2 * n by linarith) 6
      norm_num [mul_pow] at h; exact h
    linarith [mul_le_mul_of_nonneg_right hh'' (apply_nonneg (p (w,k,l)) (R n f.val)),
      mul_assoc (64 : ℝ) ((n : ℝ)^6) (p (w,k,l) (R n f.val))]

/-- Paper: Lemma D.3.2.3(2), p. 801. The strong dual is nuclear. -/
theorem positiveRealExponentialDecay_strongDual_nuclear (hInt : OrdConnected I) (hne : I.Nonempty) :
    IsNuclearTVS D := by
  classical
  obtain ⟨w, hw⟩ := hne
  let a : I := ⟨w, hw⟩
  have : T2Space E := (positiveRealExponentialDecay_isEmbedding I ⟨w, hw⟩).t2Space
  have : MontelSpace ℂ E := (positiveRealExponentialDecay_montel I hInt ⟨w, hw⟩).2
  let tests : Set (Set E) := {s | IsVonNBounded ℂ s}
  have : PolynormableSpace ℂ D := (uniformConvergenceCLM_withSeminorms tests
    (fun _ h ↦ h) (by simp [tests, sUnion_isVonNBounded_eq_univ]) _
    (norm_withSeminorms ℂ ℂ)).toPolynormableSpace
  have : ContinuousSMul ℝ D := MulAction.continuousSMul_compHom
    (f := (algebraMap ℝ ℂ).toMonoidHom) Complex.continuous_ofReal
  apply (isNuclearTVS_iff_localBanach_integral D).mpr
  intro U hU bU cU
  let q := gaugeSeminorm bU cU (absorbent_nhds_zero hU)
  obtain ⟨⟨B₀, W⟩, ⟨hB₀, hW⟩, hWU⟩ := ContinuousLinearMap.hasBasis_nhds_zero.mem_iff.mp hU
  obtain ⟨ε, hε, hεW⟩ := Metric.mem_nhds_iff.mp hW
  let B := closure B₀
  have hB : IsCompact B := MontelSpace.isCompact_of_isClosed_of_isVonNBounded ℂ
    isClosed_closure hB₀.closure
  have hq (f : D) (r : ℝ) (hr : 0 ≤ r) (hf : ∀ x ∈ B, ‖f x‖ ≤ r) : q f ≤ ε⁻¹ * r := by
    apply le_of_forall_gt_imp_ge_of_dense
    intro t ht
    have ht₀ : 0 < t := (mul_nonneg (inv_nonneg.mpr hε.le) hr).trans_lt ht
    have ht' : r < t * ε := by rwa [← div_eq_inv_mul, div_lt_iff₀ hε] at ht
    have hmem : (t : ℂ)⁻¹ • f ∈ U := by
      apply hWU
      intro x hx
      apply hεW
      rw [Metric.mem_ball, dist_zero_right, smul_apply, norm_smul, norm_inv,
        Complex.norm_real, Real.norm_of_nonneg ht₀.le, inv_mul_lt_iff₀ ht₀]
      exact (hf x (subset_closure hx)).trans_lt ht'
    have hle : q ((t : ℂ)⁻¹ • f) ≤ 1 := gauge_le_one_of_mem hmem
    rwa [map_smul_eq_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg ht₀.le,
      inv_mul_le_iff₀ ht₀, mul_one] at hle
  obtain ⟨d, b, c, hd, hz⟩ := decay_compact_approximants a hB
  let err (n : ℕ) (x : B) : E := x.val - ∑ i, c n i x.val • (b n i).val
  let A := B ∪ range (fun z : ℕ × B ↦ (((z.1 : ℂ) + 1)^6) • err z.1 z.2)
  have hA : IsVonNBounded ℂ A := hB₀.closure.union hz
  have hpol : ∀ᶠ f : D in 𝓝 0, MapsTo f A (Metric.ball 0 1) :=
    ContinuousLinearMap.eventually_nhds_zero_mapsTo hA (Metric.ball_mem_nhds 0 one_pos)
  obtain ⟨p, hp, hball⟩ := (PolynormableSpace.hasBasis_zero_ball ℂ D).mem_iff.mp (inter_mem hU hpol)
  let V := p.ball 0 1
  have hV : V ∈ 𝓝 0 := p.ball_mem_nhds hp one_pos
  have bV := p.balanced_ball_zero 1
  have cV := p.convex_ball 0 1
  have hVU : V ⊆ U := fun _ hx ↦ (hball hx).1
  have hpg : gaugeSeminorm bV cV (absorbent_nhds_zero hV) = p :=
    DFunLike.coe_injective (p.restrictScalars ℝ).gauge_ball
  have hbound (f : D) (x : E) (hx : x ∈ A) : ‖f x‖ ≤ p f := by
    apply le_of_forall_gt_imp_ge_of_dense
    intro t ht
    have ht₀ := (apply_nonneg p f).trans_lt ht
    have hmem : (t : ℂ)⁻¹ • f ∈ V := by
      rwa [Seminorm.mem_ball_zero, map_smul_eq_mul, norm_inv, Complex.norm_real,
        Real.norm_of_nonneg ht₀.le, inv_mul_lt_iff₀ ht₀, mul_one]
    have hh := (hball hmem).2 hx
    rw [Metric.mem_ball, dist_zero_right, smul_apply, norm_smul, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg ht₀.le, inv_mul_lt_iff₀ ht₀, mul_one] at hh
    exact hh.le
  refine ⟨V, hV, bV, cV, hVU, ?_⟩
  dsimp only
  apply dual_local_integral_of_interpolation _ q _ ε⁻¹ (inv_nonneg.mpr hε.le) hq d b c hd
  · intro f x
    rw [hpg]
    exact hbound f x (Or.inl x.property)
  · intro f n x
    rw [hpg, le_div_iff₀ (by positivity)]
    have hh := hbound f _ (Or.inr (mem_range_self (n, x)))
    simpa only [map_smul, norm_smul, norm_pow, show ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 by
      exact_mod_cast Complex.norm_natCast (n + 1), mul_comm] using hh

end StrongDualNuclearity

open scoped ComplexOrder in
/-- Paper: Lemma D.3.2.3(2), p. 801. The strong dual has the Montel
property and is barrelled. -/
theorem positiveRealExponentialDecay_strongDual_montel (hInt : OrdConnected I) (hne : I.Nonempty) :
    BarrelledSpace ℂ D ∧ MontelSpace ℂ D := by
  obtain ⟨hbarrel, hmontel⟩ := positiveRealExponentialDecay_montel I hInt hne
  let : T2Space E := (positiveRealExponentialDecay_isEmbedding I hne).t2Space
  refine ⟨⟨fun p hp ↦ ?_⟩, montelSpace_strongDual⟩
  let U := p.closedBall 0 1
  let A := (topDualPairing ℂ E).polar U
  -- The polar of the absorbing unit ball is pointwise bounded.
  have hA : IsVonNBounded ℂ A := by
    apply (isVonNBounded_iff_dual_image A).mpr
    intro φ
    obtain ⟨c, hc⟩ := (p.absorbent_closedBall_zero one_pos φ).exists
    refine isBounded_iff_forall_norm_le.mpr ⟨‖c‖, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨ψ, hψ, hφ⟩ := hc (mem_singleton φ)
    rw [← hφ]
    change ‖(c • ψ) x‖ ≤ ‖c‖
    rw [smul_apply, norm_smul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hx ψ hψ)
  refine Seminorm.continuous' (r := 1) ?_
  have hU : IsClosed U := by
    rw [show U = {φ | p φ ≤ 1} from p.closedBall_zero_eq]
    exact hp.isClosed_preimage 1
  let : Module ℝ D := Module.restrictScalars ℝ ℂ D
  let : IsScalarTower ℝ ℂ D := IsScalarTower.restrictScalars ℝ ℂ D
  let S : Set (Set E) := {s | IsVonNBounded ℂ s}
  let : PolynormableSpace ℂ D :=
    uniformConvergenceCLM_polynormable (F := ℂ) S (fun _ hs ↦ hs)
      (by rw [show ⋃₀ S = univ from sUnion_isVonNBounded_eq_univ, Submodule.span_univ]; simp)
  have haU : AbsConvex ℂ U := ⟨p.balanced_closedBall_zero 1,
    convex_RCLike_iff_convex_real.mpr (p.convex_closedBall 0 1)⟩
  have hzU : 0 ∈ U := p.mem_closedBall_zero.mpr (by simp)
  -- Any separating functional would be evaluation at a point of the polar.
  filter_upwards [ContinuousLinearMap.eventually_nhds_zero_mapsTo (σ := RingHom.id ℂ) hA
    (Metric.ball_mem_nhds (0 : ℂ) one_pos)] with φ hφ
  by_contra hnot
  obtain ⟨l, hl, hlt⟩ := exists_dual_norm_le_one_lt_of_notMem hU haU hzU hnot
  obtain ⟨x, rfl⟩ := surjective_strongBidual_eval l
  have hx : x ∈ A := fun ψ hψ ↦ hl ψ hψ
  exact (not_lt_of_ge (mem_ball_zero_iff.mp (hφ hx)).le) hlt

/-- Paper: Lemma D.3.2.3(3), p. 801. If zero lies in I, the zero-weight
profile is a continuous linear inclusion into the ordinary Schwartz space. -/
theorem positiveRealExponentialDecay_continuous_inclusion (h0 : 0 ∈ I) :
    ∃ T : E →L[ℂ] 𝓢(ℝ, ℂ), Injective T ∧ ∀ f x, T f x = f.val x := by
  let a : I := ⟨0, h0⟩
  have hc := (continuous_apply a).comp (positiveRealExponentialDecay_isEmbedding I ⟨0, h0⟩).continuous
  let T : E →L[ℂ] 𝓢(ℝ, ℂ) := ⟨logExponentialDecayTwist I a, hc⟩
  have hT (f : E) (x : ℝ) : T f x = f.val x := by
    change logExponentialDecayTwist I a f x = _
    rw [logExponentialDecayTwist_apply I a f x]
    simp [a]
  refine ⟨T, ?_, hT⟩
  intro f g h
  apply Subtype.ext
  funext x
  rw [← hT f x, ← hT g x, h]

-- TODO(prerequisite): Lemma D.3.2.3(4–6) needs the three independently defined
-- subspaces from §B.2.1.1, Definition B.2.1.1.

/-- Paper: Proposition D.3.2.5, p. 802. On the strip, the positive-real Mellin
integral converges absolutely. The profile is pulled back by the real logarithm. -/
theorem positiveRealExponentialDecay_mellinConvergent (f : E) (s : ℂ) (hs : s.re ∈ I) :
    MellinConvergent (fun t ↦ f.val (Real.log t)) s := by
  apply mellinConvergent_of_integrable_logWeight
  have h : Integrable (fun x : ℝ ↦ logExponentialDecayTwist I ⟨s.re, hs⟩ f x) volume :=
    (logExponentialDecayTwist I ⟨s.re, hs⟩ f).integrable
  exact h.congr (Eventually.of_forall fun x ↦ logExponentialDecayTwist_apply I ⟨s.re, hs⟩ f x)

section MellinIsomorphism

open scoped Asymptotics FourierTransform

local notation "linePoint" => (fun (a y : ℝ) ↦ (a : ℂ) + y * Complex.I)
local notation "profile" => (fun (f : ℝ → ℂ) (t : ℝ) ↦ f (Real.log t))

/-- The Fourier argument corresponding to a unit of imaginary Mellin height. -/
private def fourierFrequencyScale :=
  (LinearEquiv.smulOfNeZero ℝ ℝ (2 * Real.pi)⁻¹
    (inv_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero))).toContinuousLinearEquiv

/-- Paper: Proposition D.3.2.5, p. 802. Reflection, Fourier transform, and rescaling
turn an exponential twist into its vertical Mellin trace. -/
private def mellinLineEquiv : 𝓢(ℝ, ℂ) ≃L[ℂ] 𝓢(ℝ, ℂ) :=
  (schwartzChangeVariable ℂ (LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ).toContinuousLinearEquiv).trans
    ((FourierTransform.fourierCLE ℂ 𝓢(ℝ, ℂ)).trans (schwartzChangeVariable ℂ fourierFrequencyScale))

private theorem mellinLineEquiv_twist {I : Set ℝ} (a : I) (f : logExponentialDecaySubmodule I) (y : ℝ) :
    mellinLineEquiv (logExponentialDecayTwist I a f) y = mellin (profile f.val) (linePoint a y) := by
  let g := logExponentialDecayTwist I a f
  let r := schwartzChangeVariable ℂ (LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ).toContinuousLinearEquiv g
  change (𝓕 r) ((2 * Real.pi)⁻¹ * y) = _
  rw [SchwartzMap.fourier_coe, mellin_eq_fourier]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im,
    neg_zero, add_zero, Complex.add_im, Complex.mul_I_im, zero_add, Real.log_exp, div_eq_inv_mul]
  apply congrArg (fun h : ℝ → ℂ ↦ 𝓕 h ((2 * Real.pi)⁻¹ * y))
  funext x
  change logExponentialDecayTwist I a f (-x) = _
  rw [logExponentialDecayTwist_apply I a f (-x)]
  simp only [Complex.real_smul, mul_neg, neg_mul]

private theorem mellinLineEquiv_symm_apply {F : ℂ → ℂ} (a : ℝ) (g : 𝓢(ℝ, ℂ))
    (hg : ∀ y, g y = F (linePoint a y)) (x : ℝ) :
    mellinLineEquiv.symm g x = (Real.exp (a * x) : ℂ) * mellinInv a F (Real.exp x) := by
  let r := (schwartzChangeVariable ℂ fourierFrequencyScale).symm g
  change (𝓕⁻ r) (-x) = _
  rw [SchwartzMap.fourierInv_coe, mellinInv_eq_fourierInv a F (Real.exp_pos x), Real.log_exp]
  have eq : ⇑r = (fun y : ℝ ↦ F (a + 2 * (Real.pi : ℂ) * y * Complex.I)) := by
    funext y
    change g (((2 * Real.pi)⁻¹)⁻¹ * y) = _
    rw [inv_inv, hg]
    push_cast
    rfl
  rw [eq, smul_eq_mul, ← mul_assoc]
  have hpow : ((Real.exp x : ℝ) : ℂ) ^ (-(a : ℂ)) = (Real.exp (-(a * x)) : ℂ) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos x).ne'),
      ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [hpow, ← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, Complex.ofReal_one, one_mul]

private theorem mellinProfile_differentiable {I : Set ℝ} (hI : IsOpen I)
    (f : logExponentialDecaySubmodule I) : DifferentiableOn ℂ (mellin (profile f.val)) (Complex.re ⁻¹' I) := by
  intro z hz
  let a : I := ⟨z.re, hz⟩
  have cont : Continuous f.val := by
    have eq : f.val = (fun u : ℝ ↦ (Real.exp (-((a : ℝ) * u)) : ℂ) * logExponentialDecayTwist I a f u) := by
      funext x
      rw [logExponentialDecayTwist_apply I a f x, ← mul_assoc, ← Complex.ofReal_mul,
        ← Real.exp_add, neg_add_cancel, Real.exp_zero, Complex.ofReal_one, one_mul]
    rw [eq]
    exact (by fun_prop : Continuous (fun u : ℝ ↦ (Real.exp (-((a : ℝ) * u)) : ℂ))).mul
      (logExponentialDecayTwist I a f).continuous
  obtain ⟨l, r, hl, hr⟩ := exists_bracketing_lines hI a
  have hloc : LocallyIntegrableOn (profile f.val) (Ioi 0) volume :=
    (cont.comp_continuousOn (Real.continuousOn_log.mono (fun x hx ↦ ne_of_gt hx))).locallyIntegrableOn measurableSet_Ioi
  have bound (c : I) {L : Filter ℝ} (hL : ∀ᶠ t in L, 0 < t) :
      profile f.val =O[L] (fun t : ℝ ↦ t ^ (-(c : ℝ))) := by
    let g := logExponentialDecayTwist I c f
    apply Asymptotics.IsBigO.of_bound (SchwartzMap.seminorm ℂ 0 0 g)
    filter_upwards [hL] with t ht
    rw [Real.norm_of_nonneg (Real.rpow_nonneg ht.le _), Real.rpow_neg ht.le, ← div_eq_mul_inv,
      le_div_iff₀ (Real.rpow_pos_of_pos ht _), Real.rpow_def_of_pos ht, mul_comm (Real.log t)]
    simpa only [g, logExponentialDecayTwist_apply, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le, mul_comm] using g.norm_le_seminorm ℂ (Real.log t)
  exact (mellin_differentiableAt_of_isBigO_rpow hloc (bound r (eventually_gt_atTop 0)) hr
    (bound l self_mem_nhdsWithin) hl).differentiableWithinAt

private theorem mellinProfile_strip_bound {I : Set ℝ} (l r : I) (f : logExponentialDecaySubmodule I) :
    ∃ C : ℝ, ∀ z : ℂ, z.re ∈ Icc (l : ℝ) r → ‖mellin (profile f.val) z‖ ≤ C := by
  let G (a : I) := logExponentialDecayTwist I a f
  let B (x : ℝ) := ‖G l (-x)‖ + ‖G r (-x)‖
  have hi (a : I) : Integrable (fun x : ℝ ↦ ‖G a (-x)‖) :=
    ((Measure.measurePreserving_neg (volume : Measure ℝ)).integrable_comp
      ((G a).integrable (μ := volume)).norm.aestronglyMeasurable).2 (G a).integrable.norm
  refine ⟨∫ x, B x, fun z hz ↦ ?_⟩
  rw [mellin_eq_fourier]
  apply (Real.norm_fourier_le_integral_norm _ _).trans
  apply integral_mono_of_nonneg (.of_forall fun _ ↦ norm_nonneg _) ((hi l).add (hi r))
  filter_upwards with x
  change ‖Real.exp (-z.re * x) • f.val (Real.log (Real.exp (-x)))‖ ≤ ‖G l (-x)‖ + ‖G r (-x)‖
  simp only [G, logExponentialDecayTwist_apply, norm_mul, Complex.norm_real, norm_smul, Real.log_exp,
    Real.norm_of_nonneg (Real.exp_pos _).le, mul_neg, ← neg_mul]
  rcases le_total x 0 with hx | hx
  · apply le_add_of_nonneg_of_le (by positivity)
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right (neg_le_neg hz.2) hx)) (norm_nonneg _)
  · apply le_add_of_le_of_nonneg _ (by positivity)
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hz.1) hx)) (norm_nonneg _)

private theorem mellinProfile_weighted_edge {I : Set ℝ} (a : I) (k : ℕ) (f : logExponentialDecaySubmodule I) :
    ∃ C : ℝ, ∀ z : ℂ, z.re = a → ‖z ^ k * mellin (profile f.val) z‖ ≤ C := by
  let g := mellinLineEquiv (logExponentialDecayTwist I a f)
  let w := fun y : ℝ ↦ (linePoint a y)^k
  have hw : w.HasTemperateGrowth := by dsimp [w]; fun_prop
  let h := SchwartzMap.smulLeftCLM ℂ w g
  refine ⟨SchwartzMap.seminorm ℂ 0 0 h, fun z hz ↦ ?_⟩
  have heq : linePoint a z.im = z := hz ▸ Complex.re_add_im z
  have hval : h z.im = z ^ k * mellin (profile f.val) z := by
    change SchwartzMap.smulLeftCLM ℂ w g z.im = _
    rw [SchwartzMap.smulLeftCLM_apply_apply hw]
    change (linePoint a z.im)^k * mellinLineEquiv (logExponentialDecayTwist I a f) z.im = _
    rw [mellinLineEquiv_twist, heq]
  rw [← hval]
  exact h.norm_le_seminorm ℂ _

private theorem mellinProfile_mem_bergman {I : Set ℝ} (hI : IsOpen I)
    (f : logExponentialDecaySubmodule I) :
    (Complex.re ⁻¹' I).indicator (mellin (profile f.val)) ∈ schwartzBergmanSubmodule I := by
  let F := mellin (profile f.val)
  have hf := mellinProfile_differentiable hI f
  refine ⟨fun z hz ↦ indicator_of_notMem hz _, ?_, ?_⟩
  · exact hf.congr fun z hz ↦ indicator_of_mem hz _
  intro l r hlr hsub k
  let a : I := ⟨l, hsub (left_mem_Icc.mpr hlr)⟩
  let b : I := ⟨r, hsub (right_mem_Icc.mpr hlr)⟩
  obtain ⟨A, hA⟩ := mellinProfile_weighted_edge a k f
  obtain ⟨B, hB⟩ := mellinProfile_weighted_edge b k f
  refine ⟨max A B, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  change ‖z ^ k * (Complex.re ⁻¹' I).indicator F z‖ ≤ _
  rw [indicator_of_mem (show z ∈ Complex.re ⁻¹' I from hsub hz)]
  rcases hlr.eq_or_lt with heq | hlt
  · exact (hA z (show z.re = l by linarith [hz.1, hz.2])).trans (le_max_left _ _)
  have hd : DiffContOnCl ℂ F (Complex.re ⁻¹' Ioo l r) := by
    refine ⟨hf.mono (preimage_mono (Ioo_subset_Icc_self.trans hsub)), ?_⟩
    rw [Complex.closure_preimage_re, closure_Ioo hlt.ne]
    exact hf.continuousOn.mono (preimage_mono hsub)
  obtain ⟨M, hM⟩ := mellinProfile_strip_bound a b f
  exact norm_pow_mul_le_on_verticalStrip hlt hd hM k
    (fun w hw ↦ (hA w hw).trans (le_max_left _ _)) (fun w hw ↦ (hB w hw).trans (le_max_right _ _)) z hz

/-- Moving the inverse contour between two lines preserves its value at every positive argument. -/
private theorem bergmanInv_shift_lt {I : Set ℝ} (hI : IsOpen I) (hInt : OrdConnected I)
    (F : SchwartzBergman I) (a b : I) (hab : (a : ℝ) < b) (u : ℝ) :
    mellinInv a F.val (Real.exp u) = mellinInv b F.val (Real.exp u) := by
  let z : ℂ := ((a : ℝ) + (b : ℝ)) / 2
  have haz : (a : ℝ) < z.re := by dsimp [z]; simp; linarith
  have hzb : z.re < (b : ℝ) := by dsimp [z]; simp; linarith
  let phase (w : ℂ) := Complex.exp (-(w * u))
  let K (w : ℂ) := phase w * F.val w
  let G (w : ℂ) := (w - z) * K w
  have hphase (w : ℂ) : ‖phase w‖ = Real.exp (-w.re * u) := by simp [phase, Complex.norm_exp, Complex.mul_re]
  have hpow (w : ℂ) : ((Real.exp u : ℝ) : ℂ) ^ (-w) = phase w := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos u).ne'),
      ← Complex.ofReal_log (Real.exp_pos u).le, Real.log_exp]
    dsimp [phase]
    ring_nf
  have line (s : I) : Integrable (fun y ↦ K (linePoint s y)) := by
    obtain ⟨T, hT, _⟩ := schwartzBergman_schwartzLine_topology I hI hInt ⟨s, s.property⟩
    have heq (y : ℝ) : T F s y = F.val (linePoint s y) := by simpa [weightedVerticalTrace] using hT F s y
    have htrace : Integrable (fun y : ℝ ↦ F.val (linePoint s y)) :=
      (T F s).integrable.congr (.of_forall heq)
    have hc : Continuous (fun y : ℝ ↦ phase (linePoint s y)) := by dsimp [phase]; fun_prop
    have hb (y : ℝ) : ‖phase (linePoint s y)‖ ≤ Real.exp (-(s : ℝ) * u) := by rw [hphase]; simp
    exact htrace.bdd_mul hc.aestronglyMeasurable (.of_forall hb)
  have eqline (s : I) (hs : (s : ℝ) ≠ z.re) (y : ℝ) : G (linePoint s y) / (linePoint s y - z) = K (linePoint s y) := by
    have hne : linePoint s y ≠ z := fun he ↦ hs (by simpa using congrArg Complex.re he)
    dsimp only [G]
    field_simp [sub_ne_zero.mpr hne]
  obtain ⟨l, _, hla, _⟩ := exists_bracketing_lines hI a
  obtain ⟨_, r, _, hbr⟩ := exists_bracketing_lines hI b
  have hG : DifferentiableOn ℂ G (Complex.re ⁻¹' Ioo (l : ℝ) r) :=
    (differentiable_id.sub_const z).differentiableOn.mul ((by dsimp [phase]; fun_prop : Differentiable ℂ phase).differentiableOn.mul
      (F.property.2.1.mono (preimage_mono (Ioo_subset_Icc_self.trans (hInt.out l.property r.property)))))
  obtain ⟨A,hA⟩ := F.property.2.2 a b hab.le (hInt.out a.property b.property) 1
  obtain ⟨B,hB⟩ := F.property.2.2 a b hab.le (hInt.out a.property b.property) 2
  obtain ⟨P,hP⟩ := (isCompact_Icc (a := (a : ℝ)) (b := (b : ℝ))).bddAbove_image
    (f := fun s : ℝ ↦ Real.exp (-s * u)) (by fun_prop)
  let C := max P 0 * (max B 0 + ‖z‖ * max A 0)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hdec : ∀ᶠ y : ℝ in comap abs atTop, ∀ s ∈ Icc (a : ℝ) b, ‖G (linePoint s y)‖ ≤ C / |y| := by
    have ht : Tendsto (abs : ℝ → ℝ) (comap abs atTop) atTop := tendsto_comap
    filter_upwards [ht.eventually (eventually_gt_atTop 0)] with y hy s hs
    let w := linePoint s y
    have hw : w ∈ Complex.re ⁻¹' Icc (a : ℝ) b := by simpa [w] using hs
    have him : |y| ≤ ‖w‖ := by simpa [w] using Complex.abs_im_le_norm w
    have ha := hA (mem_image_of_mem _ hw)
    have hb := hB (mem_image_of_mem _ hw)
    simp only [pow_one, norm_mul, norm_pow] at ha hb
    have hp : ‖phase w‖ ≤ max P 0 := (hphase w).le.trans
      ((hP (mem_image_of_mem _ hw)).trans (le_max_left _ _))
    apply (le_div_iff₀ hy).mpr
    calc ‖G w‖ * |y| = ‖phase w‖ * (‖w-z‖ * |y| * ‖F.val w‖) := by simp only [G,K,norm_mul]; ring
      _ ≤ max P 0 * ((‖w‖ + ‖z‖) * ‖w‖ * ‖F.val w‖) := by gcongr; exact norm_sub_le _ _
      _ ≤ C := by
        apply mul_le_mul_of_nonneg_left _ (le_max_right P 0)
        calc _ = ‖w‖ ^ 2 * ‖F.val w‖ + ‖z‖ * (‖w‖ * ‖F.val w‖) := by ring
          _ ≤ _ := add_le_add (hb.trans (le_max_left _ _))
            (mul_le_mul_of_nonneg_left (ha.trans (le_max_left _ _)) (norm_nonneg _))
  have h := verticalCauchyIntegral_sub_eq hG hla hbr ⟨haz,hzb⟩ hC hdec
    (by simpa only [Complex.VerticalIntegrable, eqline a haz.ne] using line a)
    (by simpa only [Complex.VerticalIntegrable, eqline b hzb.ne'] using line b)
  simp only [eqline b hzb.ne', eqline a haz.ne] at h
  have hi : (∫ y : ℝ, K (linePoint b y)) = ∫ y : ℝ, K (linePoint a y) :=
    sub_eq_zero.mp (by simpa [G] using h)
  simp only [mellinInv, hpow, smul_eq_mul]
  exact congrArg (fun v : ℂ ↦ (1 / (2 * Real.pi) : ℝ) • v) hi.symm

private theorem bergmanInv_shift {I : Set ℝ} (hI : IsOpen I) (hInt : OrdConnected I)
    (F : SchwartzBergman I) (a b : I) (u : ℝ) :
    mellinInv a F.val (Real.exp u) = mellinInv b F.val (Real.exp u) := by
  rcases lt_trichotomy (a : ℝ) (b : ℝ) with h | h | h
  · exact bergmanInv_shift_lt hI hInt F a b h u
  · rw [h]
  · exact (bergmanInv_shift_lt hI hInt F b a h u).symm

/-- The Mellin transform of a logarithmic profile, extended by zero outside the strip. -/
private def stripMellinLinear {I : Set ℝ} (hI : IsOpen I) : PositiveRealExponentialDecay I →ₗ[ℂ] SchwartzBergman I := by
  let B (f : PositiveRealExponentialDecay I) : SchwartzBergman I :=
    ⟨(Complex.re ⁻¹' I).indicator (mellin (profile f.val)), mellinProfile_mem_bergman hI f⟩
  let L (a : I) : PositiveRealExponentialDecay I →ₗ[ℂ] 𝓢(ℝ, ℂ) :=
    mellinLineEquiv.toLinearMap.comp (logExponentialDecayTwist I a)
  have hv (f : PositiveRealExponentialDecay I) (z : ℂ) (hz : z.re ∈ I) :
      (B f).val z = L ⟨z.re, hz⟩ f z.im := by
    change (Complex.re ⁻¹' I).indicator _ z = mellinLineEquiv (logExponentialDecayTwist I _ f) z.im
    rw [indicator_of_mem (show z ∈ Complex.re ⁻¹' I from hz), mellinLineEquiv_twist ⟨z.re, hz⟩ f z.im]
    simp [Complex.re_add_im]
  refine ⟨⟨B, ?_⟩, ?_⟩
  · intro f g
    apply Subtype.ext
    funext z
    change (B (f+g)).val z = (B f).val z + (B g).val z
    by_cases hz : z.re ∈ I
    · rw [hv _ _ hz, hv f _ hz, hv g _ hz, map_add]; rfl
    · simp [B, indicator_of_notMem (show z ∉ Complex.re ⁻¹' I from hz)]
  · intro c f
    apply Subtype.ext
    funext z
    change (B (c • f)).val z = c • (B f).val z
    by_cases hz : z.re ∈ I
    · rw [hv _ _ hz, hv f _ hz, map_smul]; rfl
    · simp [B, indicator_of_notMem (show z ∉ Complex.re ⁻¹' I from hz)]

private theorem stripMellinLinear_apply {I : Set ℝ} (hI : IsOpen I)
    (f : PositiveRealExponentialDecay I) (s : ℂ) (hs : s.re ∈ I) :
    (stripMellinLinear hI f).val s = mellin (profile f.val) s :=
  indicator_of_mem (show s ∈ Complex.re ⁻¹' I from hs) _

/-- Paper: Proposition D.3.2.5, p. 802. The Mellin integral induces a unique
continuous linear equivalence with the Schwartz–Bergman space on the strip. -/
theorem existsUnique_positiveRealFourierMellin (hOpen : IsOpen I) (hInt : OrdConnected I)
    (hne : I.Nonempty) :
    ∃! M : E ≃L[ℂ] SchwartzBergman I, ∀ (f : E) (s : ℂ), s.re ∈ I →
      (M f).val s = mellin (fun t ↦ f.val (Real.log t)) s := by
  let M := stripMellinLinear hOpen
  let U := mellinLineEquiv
  obtain ⟨T, hval, hT⟩ := schwartzBergman_schwartzLine_topology I hOpen hInt hne
  have hline (F : SchwartzBergman I) (a : I) (y : ℝ) : T F a y = F.val (linePoint a y) := by
    simpa only [weightedVerticalTrace, pow_zero, one_mul] using hval F a y
  have hcomm (f : PositiveRealExponentialDecay I) (a : I) : T (M f) a = U (logExponentialDecayTwist I a f) := by
    ext y
    rw [hline, show (M f).val (linePoint a y) = _ from stripMellinLinear_apply hOpen f _ (by simp)]
    exact (mellinLineEquiv_twist a f y).symm
  have hE := positiveRealExponentialDecay_isEmbedding I hne
  have inj : Injective M := by
    intro f g h
    apply hE.injective
    funext a
    apply U.injective
    rw [← hcomm, ← hcomm, h]
  have surj : Surjective M := by
    intro F
    obtain ⟨c,hc⟩ := hne
    let f (u : ℝ) := mellinInv c F.val (Real.exp u)
    have htw (a : I) (u : ℝ) : U.symm (T F a) u = (Real.exp ((a : ℝ) * u) : ℂ) * f u := by
      rw [mellinLineEquiv_symm_apply a (T F a) (hline F a)]
      exact congrArg (_ * ·) (bergmanInv_shift hOpen hInt F a ⟨c,hc⟩ u)
    have hf : f ∈ logExponentialDecaySubmodule I := by
      apply (Submodule.mem_iInf _).mpr
      intro a
      exact ⟨U.symm (T F a), funext (htw a)⟩
    let g : PositiveRealExponentialDecay I := ⟨f,hf⟩
    have hg (a : I) : logExponentialDecayTwist I a g = U.symm (T F a) := by
      ext u
      exact (logExponentialDecayTwist_apply I a g u).trans (htw a u).symm
    refine ⟨g, hT.injective ?_⟩
    funext a
    rw [hcomm, hg, U.apply_symm_apply]
  let e := LinearEquiv.ofBijective M ⟨inj,surj⟩
  let A : PositiveRealExponentialDecay I ≃L[ℂ] SchwartzBergman I := {
    toLinearEquiv := e
    continuous_toFun := by
      apply hT.continuous_iff.mpr
      apply continuous_pi
      intro a
      exact (U.continuous.comp ((continuous_apply a).comp hE.continuous)).congr fun f ↦ (hcomm f a).symm
    continuous_invFun := by
      apply hE.continuous_iff.mpr
      apply continuous_pi
      intro a
      apply (U.symm.continuous.comp ((continuous_apply a).comp hT.continuous)).congr
      intro F
      change U.symm (T F a) = logExponentialDecayTwist I a (e.symm F)
      apply U.injective
      rw [U.apply_symm_apply, ← hcomm]
      exact congrArg (fun G ↦ T G a) (e.apply_symm_apply F).symm }
  refine ⟨A, stripMellinLinear_apply hOpen, ?_⟩
  intro A' hA'
  apply ContinuousLinearEquiv.ext
  funext f
  apply hT.injective
  funext a
  ext y
  rw [hline, hline, hA' f _ (by simp)]
  exact (stripMellinLinear_apply hOpen f _ (by simp)).symm

end MellinIsomorphism

/-- Paper: Definition D.3.2.6, p. 803. The Fourier–Mellin transform is
the continuous linear equivalence furnished by the Mellin integral. -/
def positiveRealFourierMellin (hOpen : IsOpen I) (hInt : OrdConnected I) (hne : I.Nonempty) :
    E ≃L[ℂ] SchwartzBergman I :=
  Classical.choose (existsUnique_positiveRealFourierMellin I hOpen hInt hne).exists

/-- Paper: Lemma D.3.1.2, p. 799. The Schwartz–Bergman space is Fréchet. -/
theorem schwartzBergman_frechet (I : Set ℝ) (hI : IsOpen I) (hInt : OrdConnected I)
    (hne : I.Nonempty) : IsFrechetTVS (SchwartzBergman I) := by
  let M := positiveRealFourierMellin I hI hInt hne
  obtain ⟨_, _, hmetr, hcomp⟩ := positiveRealExponentialDecay_frechet I hInt hne
  have : MetrizableSpace (PositiveRealExponentialDecay I) := hmetr
  refine ⟨inferInstance, inferInstance, M.symm.toHomeomorph.isEmbedding.metrizableSpace, ?_⟩
  exact (M.isUniformEmbedding.isUniformInducing.completeSpace_congr M.surjective).mp hcomp

/-- Paper: Definition D.3.2.6, p. 803. Evaluation of the Fourier–Mellin
transform on the strip gives the absolutely convergent Mellin integral. -/
theorem positiveRealFourierMellin_apply (hOpen : IsOpen I) (hInt : OrdConnected I)
    (hne : I.Nonempty) (f : E) (s : ℂ) (hs : s.re ∈ I) :
    (positiveRealFourierMellin I hOpen hInt hne f).val s =
      mellin (fun t ↦ f.val (Real.log t)) s := by
  exact Classical.choose_spec (existsUnique_positiveRealFourierMellin I hOpen hInt hne).exists f s hs

/-- Paper: (D.3.2.3–4), p. 803. In logarithmic coordinates the weighted
L² norm is the norm of this exponentially and polynomially weighted derivative. -/
def exponentialDecayL2Integrand (a b : ℝ) (m : ℕ) (f : PositiveRealExponentialDecay univ)
    (x : ℝ) : ℂ :=
  ((Real.exp (a * |x|) * |x| ^ b : ℝ) : ℂ) * iteratedDeriv m f.val x

/-- Paper: (D.3.2.3–4), p. 803. At b = 0 the logarithmic power disappears,
leaving the pure exponential weight. -/
theorem exponentialDecayL2Integrand_zero_log (a : ℝ) (m : ℕ)
    (f : PositiveRealExponentialDecay univ) (x : ℝ) :
    exponentialDecayL2Integrand a 0 m f x =
      (Real.exp (a * |x|) : ℂ) * iteratedDeriv m f.val x := by
  simp [exponentialDecayL2Integrand]

private def decayTwistCLM (c : ℝ) : PositiveRealExponentialDecay univ →L[ℂ] 𝓢(ℝ, ℂ) :=
  ⟨logExponentialDecayTwist univ ⟨c, mem_univ c⟩,
    (continuous_apply (⟨c, mem_univ c⟩ : (univ : Set ℝ))).comp
      (positiveRealExponentialDecay_isEmbedding univ univ_nonempty).continuous⟩

private theorem decayProfile_smooth (f : PositiveRealExponentialDecay univ) : ContDiff ℝ ∞ f.val := by
  have h : ⇑(decayTwistCLM 0 f) = f.val := by
    funext x
    change logExponentialDecayTwist univ ⟨0, _⟩ f x = _
    simpa only [Subtype.coe_mk, zero_mul, Real.exp_zero, Complex.ofReal_one, one_mul] using
      logExponentialDecayTwist_apply univ ⟨0, mem_univ (0 : ℝ)⟩ f x
  rw [← h]
  exact (decayTwistCLM 0 f).smooth _

/-- Differentiate the profile before applying the exponential twist. -/
private def decayWeightedDeriv (c : ℝ) (m : ℕ) : PositiveRealExponentialDecay univ →L[ℂ] 𝓢(ℝ, ℂ) :=
  ((SchwartzMap.derivCLM ℂ ℂ - (c : ℂ) • ContinuousLinearMap.id ℂ _) ^ m).comp (decayTwistCLM c)

private theorem decayWeightedDeriv_apply (c : ℝ) (m : ℕ) (f : PositiveRealExponentialDecay univ) :
    ⇑(decayWeightedDeriv c m f) =
      fun x : ℝ ↦ (Real.exp (c * x) : ℂ) * iteratedDeriv m f.val x := by
  induction m with
  | zero =>
    funext x
    exact logExponentialDecayTwist_apply univ ⟨c, mem_univ c⟩ f x
  | succ m ih =>
    funext x
    simp only [decayWeightedDeriv, pow_succ', ContinuousLinearMap.comp_apply] at ih ⊢
    change deriv (⇑(decayWeightedDeriv c m f)) x - c * decayWeightedDeriv c m f x = _
    change ⇑(decayWeightedDeriv c m f) = _ at ih
    rw [ih, iteratedDeriv_succ]
    have he : HasDerivAt (fun x : ℝ ↦ (Real.exp (c * x) : ℂ)) ((c * Real.exp (c * x) : ℝ) : ℂ) x := by
      apply HasDerivAt.ofReal_comp
      simpa [mul_comm] using ((hasDerivAt_id x).const_mul c).exp
    have hd := ((decayProfile_smooth f).differentiable_iteratedDeriv m
      (by exact_mod_cast ENat.natCast_lt_top m)) x
    rw [(he.fun_mul hd.hasDerivAt).deriv]
    push_cast
    ring

/-- The polynomially weighted exponential envelope belongs to L² on both half-lines. -/
private theorem memLp_decayEnvelope (s b : ℝ) (hs : 0 < s) (hb : 0 ≤ b) :
    MemLp (fun x : ℝ ↦ |x| ^ b * Real.exp (-s * |x|)) 2 volume := by
  have hcont : Continuous (fun x : ℝ ↦ |x| ^ b * Real.exp (-s * |x|)) :=
    ((Real.continuous_rpow_const hb).comp continuous_abs).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_abs))
  apply (integrable_norm_rpow_iff hcont.aestronglyMeasurable (by norm_num) (by norm_num)).mp
  have hpos : IntegrableOn
      (fun x : ℝ ↦ ‖|x| ^ b * Real.exp (-s * |x|)‖ ^ (2 : ℝ≥0∞).toReal) (Ioi 0) := by
    refine (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (b := 2 * s) (s := b * 2)
      (by linarith) (by norm_num) (by positivity)).congr_fun (fun x hx ↦ ?_) measurableSet_Ioi
    change 0 < x at hx
    dsimp only
    rw [abs_of_pos hx, Real.norm_of_nonneg (by positivity), ENNReal.toReal_ofNat,
      Real.rpow_two, mul_pow, Real.rpow_one, ← Real.rpow_mul_natCast hx.le, ← Real.exp_nat_mul]
    push_cast
    ring_nf
  rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ), integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  refine ⟨?_, hpos⟩
  rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding]
  simpa [Function.comp_def, neg_preimage] using hpos

private def decayL2ProfileMap (a b : ℝ) (m : ℕ) : PositiveRealExponentialDecay univ →ₗ[ℂ] (ℝ → ℂ) :=
  (LinearMap.mulLeft ℂ fun x : ℝ ↦ ((Real.exp (a * |x|) * |x| ^ b : ℝ) : ℂ)).comp
    (realSchwartzCoe.comp (decayWeightedDeriv 0 m).toLinearMap)

private theorem decayL2ProfileMap_apply (a b : ℝ) (m : ℕ) (f : PositiveRealExponentialDecay univ)
    (x : ℝ) :
    decayL2ProfileMap a b m f x = exponentialDecayL2Integrand a b m f x := by
  change _ * (decayWeightedDeriv 0 m f x) = _
  rw [congrFun (decayWeightedDeriv_apply 0 m f) x]
  simp [exponentialDecayL2Integrand]

/-- Paper: Lemma D.3.2.7(1), p. 803. Each weighted derivative is in L² and its
L² norm defines a continuous seminorm. The choice b = 0 includes (D.3.2.3). -/
theorem exponentialDecayL2_continuous_seminorm (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (m : ℕ) :
    let w := exponentialDecayL2Integrand a b m
    (∀ f, MemLp (w f) 2 volume) ∧
      ∃ p : Seminorm ℂ (PositiveRealExponentialDecay univ), Continuous p ∧
        ∀ f, ENNReal.ofReal (p f) = eLpNorm (w f) 2 volume := by
  let T := decayL2ProfileMap a b m
  have hT (f : PositiveRealExponentialDecay univ) : T f = exponentialDecayL2Integrand a b m f :=
    funext (decayL2ProfileMap_apply a b m f)
  let H (x : ℝ) := |x| ^ b * Real.exp (-a * |x|)
  have hH : MemLp H 2 volume := memLp_decayEnvelope a b ha hb
  let q (c : ℝ) := (SchwartzMap.seminorm ℂ 0 0).comp (decayWeightedDeriv c m).toLinearMap
  let Q := q (2 * a) + q (-(2 * a))
  have hc (c : ℝ) : Continuous (q c) :=
    ((schwartz_withSeminorms ℂ ℝ ℂ).continuous_seminorm (0, 0)).comp
      (decayWeightedDeriv c m).continuous
  have hQ : Continuous Q := (hc _).add (hc _)
  have hmeas (f : PositiveRealExponentialDecay univ) : AEStronglyMeasurable (T f) volume := by
    rw [hT]
    apply Continuous.aestronglyMeasurable
    exact (Complex.continuous_ofReal.comp
      ((Real.continuous_exp.comp (continuous_const.mul continuous_abs)).mul
        ((Real.continuous_rpow_const hb).comp continuous_abs))).mul
      ((decayProfile_smooth f).continuous_iteratedDeriv m (by exact_mod_cast (le_top : (m : ℕ∞) ≤ ⊤)))
  have hbound (f : PositiveRealExponentialDecay univ) : ∀ᵐ x ∂volume, ‖T f x‖ ≤ Q f * ‖H x‖ := by
    apply Eventually.of_forall
    intro x
    have hside (c : ℝ) (hx : c * x = (2 * a) * |x|) : ‖T f x‖ ≤ q c f * ‖H x‖ := by
      have he : Real.exp (a * |x|) = Real.exp (c * x) * Real.exp (-a * |x|) := by
        rw [← Real.exp_add, hx]
        congr 1
        ring
      have h := (decayWeightedDeriv c m f).norm_le_seminorm ℂ x
      change ‖decayWeightedDeriv c m f x‖ ≤ q c f at h
      calc
        ‖T f x‖ = ‖decayWeightedDeriv c m f x‖ * ‖H x‖ := by
          rw [hT, congrFun (decayWeightedDeriv_apply c m f) x]
          simp only [exponentialDecayL2Integrand, H, norm_mul, Complex.norm_real,
            Real.norm_of_nonneg (Real.exp_pos _).le,
            Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg x) b), he]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_right h (norm_nonneg _)
    rcases le_total 0 x with hx | hx
    · exact (hside (2 * a) (by rw [abs_of_nonneg hx])).trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (apply_nonneg _ _)) (norm_nonneg _))
    · exact (hside (-(2 * a)) (by rw [abs_of_nonpos hx]; ring)).trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (apply_nonneg _ _)) (norm_nonneg _))
  have hm (f : PositiveRealExponentialDecay univ) : MemLp (T f) 2 volume :=
    hH.of_le_mul (hmeas f) (hbound f)
  let L : PositiveRealExponentialDecay univ →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
    { toFun := fun f ↦ (hm f).toLp (T f)
      map_add' := fun f g ↦ by simp only [map_add]; rfl
      map_smul' := fun c f ↦ by simp only [map_smul]; rfl }
  let p := (normSeminorm ℂ _).comp L
  have hp (f : PositiveRealExponentialDecay univ) : p f = (eLpNorm (T f) 2 volume).toReal :=
    Lp.norm_toLp _ (hm f)
  refine ⟨fun f ↦ hT f ▸ hm f, p, ?_, fun f ↦ ?_⟩
  · let C := (eLpNorm H 2 volume).toNNReal
    apply Seminorm.continuous_of_le (q := C • Q) (hQ.const_smul C)
    intro f
    rw [hp]
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hH.eLpNorm_ne_top)
      (eLpNorm_le_mul_eLpNorm_of_ae_le_mul (hmeas f) (hbound f) 2)
    change _ ≤ (eLpNorm H 2 volume).toReal * Q f
    simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (apply_nonneg Q f), mul_comm] using h
  · rw [hp, hT f, ENNReal.ofReal_toReal]
    exact (hT f ▸ hm f).eLpNorm_ne_top

/-- Integrating on the ray away from zero bounds a weighted derivative by the weighted
L² norm of the next derivative, with one unit of spare exponential decay. -/
private theorem decay_exp_mul_norm_le (a b : ℝ) (hb : 0 ≤ b) (hab : b + 1 ≤ a)
    (m : ℕ) (f : PositiveRealExponentialDecay univ)
    (hW : MemLp (exponentialDecayL2Integrand a 0 (m + 1) f) 2 volume) (x : ℝ) :
    Real.exp (b * |x|) * ‖iteratedDeriv m f.val x‖ ≤
      lpNorm (fun y : ℝ ↦ Real.exp (-|y|)) 2 volume *
        lpNorm (exponentialDecayL2Integrand a 0 (m + 1) f) 2 volume := by
  let H (y : ℝ) := Real.exp (-|y|)
  let W := exponentialDecayL2Integrand a 0 (m + 1) f
  let g := decayWeightedDeriv 0 m f
  let d := decayWeightedDeriv 0 (m + 1) f
  have hprofile (n : ℕ) : ⇑(decayWeightedDeriv 0 n f) = iteratedDeriv n f.val := by
    simpa using decayWeightedDeriv_apply 0 n f
  have hd (y : ℝ) : HasDerivAt g (d y) y := by
    simpa only [g, d, hprofile, iteratedDeriv_succ] using g.hasDerivAt y
  have hH : MemLp H 2 volume := by
    simpa [H] using memLp_decayEnvelope 1 0 one_pos le_rfl
  let V : ℝ → ℝ := H • (fun y ↦ ‖W y‖)
  have hV : Integrable V volume := memLp_one_iff_integrable.mp (hH.smul (r := 1) hW.norm)
  have hVval (y : ℝ) : V y = H y * ‖W y‖ := rfl
  have hVnonneg (y : ℝ) : 0 ≤ V y := by
    rw [hVval]
    exact mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
  have htail (s : Set ℝ) (hs : MeasurableSet s) (habs : ∀ y ∈ s, |x| ≤ |y|)
      (hg : ‖g x‖ ≤ ∫ y in s, ‖d y‖) :
      Real.exp (b * |x|) * ‖g x‖ ≤ ∫ y, V y := by
    calc
      _ ≤ Real.exp (b * |x|) * ∫ y in s, ‖d y‖ :=
        mul_le_mul_of_nonneg_left hg (Real.exp_pos _).le
      _ = ∫ y in s, Real.exp (b * |x|) * ‖d y‖ := (integral_const_mul ..).symm
      _ ≤ ∫ y in s, V y := by
        apply setIntegral_mono_on (d.integrable.norm.const_mul _).integrableOn
          hV.integrableOn hs
        intro y hy
        rw [hVval, show W y = exponentialDecayL2Integrand a 0 (m + 1) f y from rfl,
          exponentialDecayL2Integrand_zero_log, norm_mul, Complex.norm_real,
          Real.norm_of_nonneg (Real.exp_pos _).le, ← hprofile (m + 1)]
        rw [← mul_assoc]
        change _ ≤ (Real.exp (-|y|) * Real.exp (a * |y|)) * ‖d y‖
        rw [← Real.exp_add]
        apply mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
        calc
          b * |x| ≤ b * |y| := mul_le_mul_of_nonneg_left (habs y hy) hb
          _ ≤ -|y| + a * |y| := by
            linarith [mul_le_mul_of_nonneg_right hab (abs_nonneg y)]
      _ ≤ ∫ y, V y := setIntegral_le_integral hV (Eventually.of_forall hVnonneg)
  have hx : Real.exp (b * |x|) * ‖g x‖ ≤ ∫ y, V y := by
    rcases le_total 0 x with hx | hx
    · apply htail (Ioi x) measurableSet_Ioi
      · intro y hy
        have hxy := (mem_Ioi.mp hy).le
        rwa [abs_of_nonneg hx, abs_of_nonneg (hx.trans hxy)]
      · have h := integral_Ioi_of_hasDerivAt_of_tendsto' (a := x) (fun y _ ↦ hd y)
          d.integrable.integrableOn (g.tendsto_cocompact.mono_left atTop_le_cocompact)
        simpa [h] using norm_integral_le_integral_norm (μ := volume.restrict (Ioi x)) d
    · apply htail (Iic x) measurableSet_Iic
      · intro y hy
        have hxy := mem_Iic.mp hy
        rw [abs_of_nonpos hx, abs_of_nonpos (hxy.trans hx)]
        exact neg_le_neg hxy
      · have h := integral_Iic_of_hasDerivAt_of_tendsto' (a := x) (fun y _ ↦ hd y)
          d.integrable.integrableOn (g.tendsto_cocompact.mono_left atBot_le_cocompact)
        simpa [h] using norm_integral_le_integral_norm (μ := volume.restrict (Iic x)) d
  rw [show g x = iteratedDeriv m f.val x from congrFun (hprofile m) x] at hx
  apply hx.trans
  have h : eLpNorm V 1 volume ≤ eLpNorm H 2 volume * eLpNorm (fun y ↦ ‖W y‖) 2 volume :=
    eLpNorm_smul_le_mul_eLpNorm (r := 1) hH.aestronglyMeasurable
    hW.norm.aestronglyMeasurable
  have hbound := ENNReal.toReal_mono
    (ENNReal.mul_ne_top hH.eLpNorm_ne_top hW.norm.eLpNorm_ne_top) h
  have hnorm (y : ℝ) : ‖V y‖ = V y := Real.norm_of_nonneg (hVnonneg y)
  simpa only [ENNReal.toReal_mul, eLpNorm_norm _ hW.aestronglyMeasurable, toReal_eLpNorm,
    lpNorm_one_eq_integral_norm hV.aestronglyMeasurable, hnorm] using hbound

/-- Paper: Lemma D.3.2.7(2), p. 803. Exponential weights on an unbounded sequence
of positive exponents generate the topology. -/
theorem exponentialDecayL2_generates (a : ℕ → ℝ) (ha : ∀ n, 0 < a n)
    (hunbounded : ¬ BddAbove (range a)) :
    GeneratesLpSeminorms volume 2
      (fun (i : ℕ × ℕ) ↦ exponentialDecayL2Integrand (a i.1) 0 i.2) := by
  classical
  have h (i : ℕ × ℕ) :=
    exponentialDecayL2_continuous_seminorm (a i.1) 0 (ha i.1) le_rfl i.2
  choose P hPc hPval using fun i ↦ (h i).2
  refine ⟨fun i ↦ (h i).1, P, ?_, hPval⟩
  let t : TopologicalSpace (PositiveRealExponentialDecay univ) := inferInstance
  let u := (SeminormFamily.moduleFilterBasis P).topology
  have hP : WithSeminorms (topology := u) P := ⟨rfl⟩
  refine WithSeminorms.mk (topology := t) ?_
  change t = u
  apply le_antisymm
  · exact le_topology_withSeminorms (t := t) hP hPc
  have hsource := withGeneratingSeminorms_spec (logExponentialDecaySubmodule univ)
    (fun i : ↥(univ : Set ℝ) × ℕ × ℕ ↦
      (SchwartzMap.seminorm ℂ i.2.1 i.2.2).comp (logExponentialDecayTwist univ i.1))
  let : TopologicalSpace (PositiveRealExponentialDecay univ) := u
  let : IsTopologicalAddGroup (PositiveRealExponentialDecay univ) := hP.isTopologicalAddGroup
  apply le_topology_withSeminorms (t := u) hsource
  rintro ⟨c, k, n⟩
  obtain ⟨_, ⟨i, rfl⟩, hi⟩ := not_bddAbove_iff.mp hunbounded (|(c : ℝ)| + 1 + 1)
  let C : ℝ≥0 := ⟨lpNorm (fun y : ℝ ↦ Real.exp (-|y|)) 2 volume, lpNorm_nonneg⟩
  let coeff (j : ℕ) : ℝ≥0 := (n.choose j : ℝ≥0) * ‖(c : ℝ)‖₊ ^ j
  let Q := ((k.factorial : ℝ≥0) * C) •
    ∑ j ∈ Finset.range (n + 1), coeff j • P (i, n - j + 1)
  have hQ : Continuous Q :=
    (Seminorm.continuous_finsetSum fun j _ ↦
      (hP.continuous_seminorm (i, n - j + 1)).const_smul (coeff j)).const_smul _
  apply Seminorm.continuous_of_le hQ
  intro f
  change SchwartzMap.seminorm ℂ k n (logExponentialDecayTwist univ c f) ≤ Q f
  apply SchwartzMap.seminorm_le_bound' ℂ k n _ (apply_nonneg Q f)
  intro x
  have htwist : ⇑(logExponentialDecayTwist univ c f) =
      (fun y ↦ Real.exp ((c : ℝ) * y)) • f.val := by
    funext y
    exact (logExponentialDecayTwist_apply univ c f y).trans Complex.real_smul.symm
  have hexp : ContDiff ℝ n (fun y ↦ Real.exp ((c : ℝ) * y)) := by fun_prop
  have hderiv := iteratedDerivWithin_smul (mem_univ x) uniqueDiffOn_univ
    hexp.contDiffAt.contDiffWithinAt
    (((decayProfile_smooth f).of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))).contDiffAt.contDiffWithinAt)
  simp only [iteratedDerivWithin_univ, iteratedDeriv_exp_const_mul] at hderiv
  rw [htwist, hderiv]
  refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (pow_nonneg (abs_nonneg x) k)).trans ?_
  have hweight : |x| ^ k * Real.exp ((c : ℝ) * x) ≤
      k.factorial * Real.exp ((|(c : ℝ)| + 1) * |x|) := by
    have hpow := (div_le_iff₀ (show 0 < (k.factorial : ℝ) by positivity)).mp
      (Real.pow_div_factorial_le_exp |x| (abs_nonneg x) k)
    have hcx : (c : ℝ) * x ≤ |(c : ℝ)| * |x| := by
      simpa only [abs_mul] using le_abs_self ((c : ℝ) * x)
    calc
      _ ≤ (Real.exp |x| * k.factorial) * Real.exp (|(c : ℝ)| * |x|) :=
        mul_le_mul hpow (Real.exp_le_exp.mpr hcx) (Real.exp_pos _).le (by positivity)
      _ = _ := by rw [add_mul, one_mul, Real.exp_add]; ring
  simp only [Q, smul_apply, NNReal.smul_def, NNReal.coe_mul, NNReal.coe_natCast, smul_eq_mul,
    FunLike.coe_sum, Finset.sum_apply, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  rw [RCLike.norm_nsmul (K := ℝ), nsmul_eq_mul, norm_smul, norm_mul,
    Real.norm_of_nonneg (Real.exp_pos _).le, norm_pow]
  have hj := decay_exp_mul_norm_le (a i) (|(c : ℝ)| + 1) (by positivity) hi.le
    (n - j) f ((h (i, n - j + 1)).1 f) x
  have hval : lpNorm (exponentialDecayL2Integrand (a i) 0 (n - j + 1) f) 2 volume =
      P (i, n - j + 1) f := by
    rw [← toReal_eLpNorm, ← hPval (i, n - j + 1) f, ENNReal.toReal_ofReal (apply_nonneg _ _)]
  rw [hval] at hj
  change _ ≤ (C : ℝ) * P (i, n - j + 1) f at hj
  simp only [coeff, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_pow, coe_nnNorm]
  calc
    _ = ((n.choose j : ℝ) * ‖(c : ℝ)‖ ^ j) *
        ((|x| ^ k * Real.exp ((c : ℝ) * x)) * ‖iteratedDeriv (n - j) f.val x‖) := by ring
    _ ≤ ((n.choose j : ℝ) * ‖(c : ℝ)‖ ^ j) *
        (k.factorial * (Real.exp ((|(c : ℝ)| + 1) * |x|) *
          ‖iteratedDeriv (n - j) f.val x‖)) := by
      rw [← mul_assoc (k.factorial : ℝ)]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hweight (norm_nonneg _))
        (by positivity)
    _ ≤ ((n.choose j : ℝ) * ‖(c : ℝ)‖ ^ j) *
        (k.factorial * ((C : ℝ) * P (i, n - j + 1) f)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hj (by positivity)) (by positivity)
    _ = _ := by ring

private theorem lpNorm_le_mul_lpNorm {u g : ℝ → ℂ} {c : ℝ}
    (hc : 0 ≤ c) (hu : AEStronglyMeasurable u volume) (hg : MemLp g 2 volume)
    (h : ∀ x, ‖u x‖ ≤ c * ‖g x‖) :
    lpNorm u 2 volume ≤ c * lpNorm g 2 volume := by
  have hle := eLpNorm_le_mul_eLpNorm_of_ae_le_mul hu (Eventually.of_forall h) 2
  have htop : ENNReal.ofReal c * eLpNorm g 2 volume ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hg.eLpNorm_ne_top
  calc lpNorm u 2 volume
      = (eLpNorm u 2 volume).toReal := rfl
    _ ≤ (ENNReal.ofReal c * eLpNorm g 2 volume).toReal := ENNReal.toReal_mono htop hle
    _ = c * lpNorm g 2 volume := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc, toReal_eLpNorm]

private theorem lpNorm_sq_eq_integral_norm_sq (φ : 𝓢(ℝ, ℂ)) :
    ∫ y : ℝ, ‖φ y‖ ^ 2 = (lpNorm (φ : ℝ → ℂ) 2 volume) ^ 2 := by
  have hm : AEStronglyMeasurable (φ : ℝ → ℂ) volume := φ.continuous.aestronglyMeasurable
  have hpow : (fun y : ℝ ↦ ‖φ y‖ ^ (2 : ℝ)) = fun y ↦ ‖φ y‖ ^ 2 := by
    funext y
    exact Real.rpow_natCast ‖φ y‖ 2
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num) hm]
  simp only [ENNReal.toReal_ofNat]
  rw [hpow]
  have hexp : ((2 : ℝ) ⁻¹) = (1 / 2 : ℝ) := by norm_num
  rw [hexp, ← Real.sqrt_eq_rpow, Real.sq_sqrt (integral_nonneg fun _ ↦ by positivity)]

/-- A Schwartz function on the line is pointwise bounded by the L² norms of itself and its derivative. -/
private theorem schwartz_norm_le_lpNorm_add_deriv (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    ‖ψ x‖ ≤ lpNorm (ψ : ℝ → ℂ) 2 volume +
      lpNorm (SchwartzMap.derivCLM ℂ ℂ ψ : ℝ → ℂ) 2 volume := by
  let d : ℝ → ℂ := SchwartzMap.derivCLM ℂ ℂ ψ
  let F : ℝ → ℝ := fun t ↦ ‖ψ t‖ ^ 2
  let F' : ℝ → ℝ := fun t ↦ 2 * inner ℝ (ψ t) (d t)
  have hd (y : ℝ) : d y = deriv (ψ : ℝ → ℂ) y := by
    simp [d]
  have hF (y : ℝ) : HasDerivAt F (F' y) y := by
    simpa [F, F', hd y] using (SchwartzMap.hasDerivAt ψ y).norm_sq
  have hsqψ : Integrable (fun y : ℝ ↦ ‖ψ y‖ ^ 2) volume := by
    have h := (ψ.memLp 2 volume).integrable_norm_rpow (by norm_num) (by norm_num)
    have hfun : (fun y : ℝ ↦ ‖ψ y‖ ^ (2 : ℝ≥0∞).toReal) = fun y ↦ ‖ψ y‖ ^ 2 := by
      funext y
      simp only [ENNReal.toReal_ofNat]
      exact Real.rpow_natCast ‖ψ y‖ 2
    simpa [hfun] using h
  have hsqd : Integrable (fun y : ℝ ↦ ‖d y‖ ^ 2) volume := by
    have h := ((SchwartzMap.derivCLM ℂ ℂ ψ).memLp 2 volume).integrable_norm_rpow
      (by norm_num) (by norm_num)
    rw [show (fun y : ℝ ↦ ‖d y‖ ^ 2) =
        fun y ↦ ‖(SchwartzMap.derivCLM ℂ ℂ ψ) y‖ ^ (2 : ℝ≥0∞).toReal by
      funext y
      simp only [ENNReal.toReal_ofNat, d]
      exact (Real.rpow_natCast ‖d y‖ 2).symm]
    exact h
  have hsumsq : Integrable (fun y : ℝ ↦ ‖ψ y‖ ^ 2 + ‖d y‖ ^ 2) volume := hsqψ.add hsqd
  have hcs (y : ℝ) : |inner ℝ (ψ y) (d y)| ≤ ‖ψ y‖ * ‖d y‖ :=
    abs_real_inner_le_norm (ψ y) (d y)
  have hdom (y : ℝ) : ‖F' y‖ ≤ ‖ψ y‖ ^ 2 + ‖d y‖ ^ 2 := by
    have hyoung : 2 * ‖ψ y‖ * ‖d y‖ ≤ ‖ψ y‖ ^ 2 + ‖d y‖ ^ 2 := by
      nlinarith [sq_nonneg (‖ψ y‖ - ‖d y‖)]
    calc ‖F' y‖ = |2 * inner ℝ (ψ y) (d y)| := by simp [F', Real.norm_eq_abs]
      _ = 2 * |inner ℝ (ψ y) (d y)| := by rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      _ ≤ 2 * (‖ψ y‖ * ‖d y‖) := mul_le_mul_of_nonneg_left (hcs y) (by norm_num)
      _ ≤ ‖ψ y‖ ^ 2 + ‖d y‖ ^ 2 := by simpa [mul_assoc] using hyoung
  have hFmeas : AEStronglyMeasurable F' volume := by
    apply Continuous.aestronglyMeasurable
    have hcψ : Continuous (fun t : ℝ ↦ (ψ t : ℂ)) := ψ.continuous
    have hcd : Continuous d := (SchwartzMap.derivCLM ℂ ℂ ψ).continuous
    exact continuous_const.mul (continuous_inner.comp (hcψ.prodMk hcd))
  have hF'int : Integrable F' volume :=
    hsumsq.mono' hFmeas (Eventually.of_forall hdom)
  have hlim : Tendsto F atTop (𝓝 0) :=
    tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (a := x) (f := F) (f' := F')
      (fun y _ ↦ hF y) hF'int.integrableOn hsqψ.integrableOn
  have heq : ∫ y in Ioi x, F' y = - F x := by
    simpa using integral_Ioi_of_hasDerivAt_of_tendsto' (a := x) (f := F) (f' := F') (m := 0)
      (fun y _ ↦ hF y) hF'int.integrableOn hlim
  have hpoint (y : ℝ) : - F' y ≤ ‖ψ y‖ ^ 2 + ‖d y‖ ^ 2 :=
    (neg_le_abs _).trans (by simpa [Real.norm_eq_abs] using hdom y)
  have htail : ∫ y in Ioi x, - F' y ≤ ∫ y in Ioi x, ‖ψ y‖ ^ 2 + ‖d y‖ ^ 2 :=
    setIntegral_mono hF'int.neg.integrableOn hsumsq.integrableOn hpoint
  have hfull : ∫ y in Ioi x, ‖ψ y‖ ^ 2 + ‖d y‖ ^ 2 ≤ ∫ y, ‖ψ y‖ ^ 2 + ‖d y‖ ^ 2 := by
    have hnonneg : 0 ≤ᵐ[volume] (fun y : ℝ ↦ ‖ψ y‖ ^ 2 + ‖d y‖ ^ 2) :=
      Eventually.of_forall fun y ↦ add_nonneg (sq_nonneg _) (sq_nonneg _)
    simpa using integral_mono_measure (Measure.restrict_le_self (s := Ioi x))
      hnonneg hsumsq
  have hsqx : ‖ψ x‖ ^ 2 ≤ (lpNorm (ψ : ℝ → ℂ) 2 volume) ^ 2 +
      (lpNorm (d : ℝ → ℂ) 2 volume) ^ 2 := by
    calc ‖ψ x‖ ^ 2 = - ∫ y in Ioi x, F' y := by rw [heq, neg_neg]
      _ = ∫ y in Ioi x, - F' y := (integral_neg _).symm
      _ ≤ ∫ y in Ioi x, ‖ψ y‖ ^ 2 + ‖d y‖ ^ 2 := htail
      _ ≤ ∫ y, ‖ψ y‖ ^ 2 + ‖d y‖ ^ 2 := hfull
      _ = (lpNorm (ψ : ℝ → ℂ) 2 volume) ^ 2 +
            (lpNorm (d : ℝ → ℂ) 2 volume) ^ 2 := by
          rw [integral_add hsqψ hsqd, lpNorm_sq_eq_integral_norm_sq ψ,
            lpNorm_sq_eq_integral_norm_sq (SchwartzMap.derivCLM ℂ ℂ ψ)]
  have hsqrt : ‖ψ x‖ ≤ Real.sqrt ((lpNorm (ψ : ℝ → ℂ) 2 volume) ^ 2 +
      (lpNorm (d : ℝ → ℂ) 2 volume) ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg _)]
    exact Real.sqrt_le_sqrt hsqx
  refine hsqrt.trans ?_
  have ha0 : 0 ≤ lpNorm (ψ : ℝ → ℂ) 2 volume := lpNorm_nonneg
  have hb0 : 0 ≤ lpNorm (d : ℝ → ℂ) 2 volume := lpNorm_nonneg
  rw [← Real.sqrt_sq (add_nonneg ha0 hb0)]
  refine Real.sqrt_le_sqrt ?_
  nlinarith

private theorem iteratedDeriv_expWeight (c : ℝ) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun y : ℝ ↦ (Real.exp (c * y) : ℂ)) x =
      (c : ℂ) ^ n * (Real.exp (c * x) : ℂ) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have hfun : iteratedDeriv n (fun y : ℝ ↦ (Real.exp (c * y) : ℂ)) =
        fun y ↦ (c : ℂ) ^ n * (Real.exp (c * y) : ℂ) := by
      funext y
      exact ih y
    rw [hfun]
    have hexp : HasDerivAt (fun y : ℝ ↦ (Real.exp (c * y) : ℂ))
        ((c : ℂ) * (Real.exp (c * x) : ℂ)) x := by
      have h := HasDerivAt.ofReal_comp (((hasDerivAt_id x).const_mul c).exp)
      simpa [mul_comm] using h
    have h := (hexp.const_mul ((c : ℂ) ^ n)).deriv
    simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using h

private theorem deriv_decayWeightedDeriv (c : ℝ) (j : ℕ)
    (f : PositiveRealExponentialDecay univ) (x : ℝ) :
    deriv (decayWeightedDeriv c j f) x =
      (c : ℂ) * decayWeightedDeriv c j f x + decayWeightedDeriv c (j + 1) f x := by
  have hexp : HasDerivAt (fun y : ℝ ↦ (Real.exp (c * y) : ℂ))
      ((c : ℂ) * (Real.exp (c * x) : ℂ)) x := by
    have h := HasDerivAt.ofReal_comp (((hasDerivAt_id x).const_mul c).exp)
    simpa [mul_comm] using h
  have hprofile : HasDerivAt (iteratedDeriv j f.val) (iteratedDeriv (j + 1) f.val x) x := by
    have hd := ((decayProfile_smooth f).differentiable_iteratedDeriv j
      (by exact_mod_cast ENat.natCast_lt_top j)) x
    simpa [iteratedDeriv_succ] using hd.hasDerivAt
  have hmul := (hexp.mul hprofile).deriv
  rw [decayWeightedDeriv_apply c (j + 1) f, decayWeightedDeriv_apply c j f]
  convert hmul using 1; ring

private theorem hasDerivAt_complexOfReal_pow (n : ℕ) (y : ℝ) :
    HasDerivAt (fun t : ℝ ↦ (t : ℂ) ^ n) ((n : ℂ) * (y : ℂ) ^ (n - 1)) y := by
  induction n with
  | zero => simpa using hasDerivAt_const y (1 : ℂ)
  | succ n ih =>
    have hid : HasDerivAt (fun t : ℝ ↦ (t : ℂ)) (1 : ℂ) y := by
      simpa using HasDerivAt.ofReal_comp (hasDerivAt_id y)
    have hmul := ih.mul hid
    have hfun : ((fun t : ℝ ↦ (t : ℂ) ^ n) * fun t : ℝ ↦ (t : ℂ)) =
        fun t : ℝ ↦ (t : ℂ) ^ (n + 1) := by
      funext t
      simp [pow_succ, mul_comm]
    rw [hfun] at hmul
    refine hmul.congr_deriv ?_
    by_cases hn : n = 0
    · simp [hn]
    · have hpow : (y : ℂ) ^ (n - 1) * (y : ℂ) = (y : ℂ) ^ n := by
        rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)]
      calc (n : ℂ) * (y : ℂ) ^ (n - 1) * (y : ℂ) + (y : ℂ) ^ n * 1
          = (n : ℂ) * ((y : ℂ) ^ (n - 1) * (y : ℂ)) + (y : ℂ) ^ n := by ring
        _ = (n : ℂ) * (y : ℂ) ^ n + (y : ℂ) ^ n := by rw [hpow]
        _ = ((n : ℂ) + 1) * (y : ℂ) ^ n := by ring
        _ = (↑(n + 1) : ℂ) * (y : ℂ) ^ (n + 1 - 1) := by
            simp [Nat.cast_add]

private theorem norm_exponentialDecayL2Integrand (a b : ℝ) (m : ℕ)
    (f : PositiveRealExponentialDecay univ) (x : ℝ) :
    ‖exponentialDecayL2Integrand a b m f x‖ =
      Real.exp (a * |x|) * |x| ^ b * ‖iteratedDeriv m f.val x‖ := by
  simp only [exponentialDecayL2Integrand, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (abs_nonneg x) b))]

private theorem expMul_profile_sup_le (a0 c : ℝ) (hc : |c| < a0) (k j : ℕ)
    (f : PositiveRealExponentialDecay univ) (x : ℝ) :
    |x| ^ k * Real.exp (c * x) * ‖iteratedDeriv j f.val x‖ ≤
      (1 + |c|) * lpNorm (exponentialDecayL2Integrand a0 (k : ℝ) j f) 2 volume +
        (k : ℝ) * lpNorm (exponentialDecayL2Integrand a0 ((k - 1 : ℕ) : ℝ) j f) 2 volume +
        lpNorm (exponentialDecayL2Integrand a0 (k : ℝ) (j + 1) f) 2 volume := by
  have ha0 : 0 < a0 := lt_of_le_of_lt (abs_nonneg c) hc
  let g := decayWeightedDeriv c j f
  let g1 := decayWeightedDeriv c (j + 1) f
  have hgrowth (b : ℕ) : (fun y : ℝ ↦ (y : ℂ) ^ b).HasTemperateGrowth :=
    (Complex.ofRealCLM.hasTemperateGrowth).pow b
  let weighted (b : ℕ) (g0 : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
    SchwartzMap.smulLeftCLM ℂ (fun y : ℝ ↦ (y : ℂ) ^ b) g0
  have hweighted (b : ℕ) (g0 : 𝓢(ℝ, ℂ)) (y : ℝ) :
      weighted b g0 y = (y : ℂ) ^ b * g0 y := by
    rw [SchwartzMap.smulLeftCLM_apply_apply (hgrowth b)]
    simp [smul_eq_mul]
  have hgx (y : ℝ) : ‖g y‖ = Real.exp (c * y) * ‖iteratedDeriv j f.val y‖ := by
    rw [congrFun (decayWeightedDeriv_apply c j f) y, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le]
  have hg1x (y : ℝ) : ‖g1 y‖ = Real.exp (c * y) * ‖iteratedDeriv (j + 1) f.val y‖ := by
    rw [congrFun (decayWeightedDeriv_apply c (j + 1) f) y, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le]
  have hcx (y : ℝ) : Real.exp (c * y) ≤ Real.exp (a0 * |y|) := by
    refine Real.exp_le_exp.mpr ?_
    calc c * y ≤ |c * y| := le_abs_self _
      _ = |c| * |y| := abs_mul _ _
      _ ≤ a0 * |y| := mul_le_mul_of_nonneg_right hc.le (abs_nonneg _)
  have hmem (b m : ℕ) : MemLp (exponentialDecayL2Integrand a0 (b : ℝ) m f) 2 volume :=
    (exponentialDecayL2_continuous_seminorm a0 (b : ℝ) ha0 (Nat.cast_nonneg b) m).1 f
  have hweight_lp (b m : ℕ) (g0 : 𝓢(ℝ, ℂ))
      (hg0 : ∀ y, ‖g0 y‖ = Real.exp (c * y) * ‖iteratedDeriv m f.val y‖) :
      lpNorm (weighted b g0 : ℝ → ℂ) 2 volume ≤
        lpNorm (exponentialDecayL2Integrand a0 (b : ℝ) m f) 2 volume := by
    have hpoint (y : ℝ) :
        ‖weighted b g0 y‖ ≤ ‖exponentialDecayL2Integrand a0 (b : ℝ) m f y‖ := by
      rw [hweighted, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, hg0,
        norm_exponentialDecayL2Integrand a0 (b : ℝ) m f y,
        Real.rpow_natCast |y| b]
      calc |y| ^ b * (Real.exp (c * y) * ‖iteratedDeriv m f.val y‖)
          = Real.exp (c * y) * (|y| ^ b * ‖iteratedDeriv m f.val y‖) := by ring
        _ ≤ Real.exp (a0 * |y|) * (|y| ^ b * ‖iteratedDeriv m f.val y‖) := by
            exact mul_le_mul_of_nonneg_right (hcx y) (mul_nonneg (by positivity) (norm_nonneg _))
        _ = Real.exp (a0 * |y|) * |y| ^ b * ‖iteratedDeriv m f.val y‖ := by ring
    simpa using lpNorm_le_mul_lpNorm (c := 1) (by positivity)
      (weighted b g0).continuous.aestronglyMeasurable (hmem b m)
      (fun y ↦ by rw [one_mul]; exact hpoint y)
  let ψ := weighted k g
  have hleft : |x| ^ k * Real.exp (c * x) * ‖iteratedDeriv j f.val x‖ = ‖ψ x‖ := by
    rw [hweighted, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, hgx]
    ring
  have hderiv (y : ℝ) : deriv (ψ : ℝ → ℂ) y =
      (k : ℂ) * (y : ℂ) ^ (k - 1) * g y + (y : ℂ) ^ k * deriv (g : ℝ → ℂ) y := by
    have hpow := hasDerivAt_complexOfReal_pow k y
    have hmul := (hpow.mul (SchwartzMap.hasDerivAt g y)).deriv
    have hfun : (fun t : ℝ ↦ (t : ℂ) ^ k * g t) = ψ := by
      funext t
      exact (hweighted k g t).symm
    rw [← hfun]
    exact hmul
  have hderivg (y : ℝ) : deriv (g : ℝ → ℂ) y = (c : ℂ) * g y + g1 y :=
    deriv_decayWeightedDeriv c j f y
  let low := weighted (k - 1) g
  let nxt := weighted k g1
  have hsplit : (SchwartzMap.derivCLM ℂ ℂ ψ : ℝ → ℂ) =
      ((k : ℂ) • (low : ℝ → ℂ)) + (((c : ℂ) • (ψ : ℝ → ℂ)) + (nxt : ℝ → ℂ)) := by
    funext y
    rw [SchwartzMap.derivCLM_apply (𝕜 := ℂ) (F := ℂ), hderiv y, hderivg y]
    have hlowy : low y = (y : ℂ) ^ (k - 1) * g y := hweighted (k - 1) g y
    have hψy : ψ y = (y : ℂ) ^ k * g y := hweighted k g y
    have hny : nxt y = (y : ℂ) ^ k * g1 y := hweighted k g1 y
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hlowy, hψy, hny, mul_add,
      mul_assoc, mul_left_comm]
  have hderlp : lpNorm (SchwartzMap.derivCLM ℂ ℂ ψ : ℝ → ℂ) 2 volume ≤
      (k : ℝ) * lpNorm (low : ℝ → ℂ) 2 volume +
        (|c| * lpNorm (ψ : ℝ → ℂ) 2 volume + lpNorm (nxt : ℝ → ℂ) 2 volume) := by
    rw [hsplit]
    have hm1 : MemLp ((k : ℂ) • (low : ℝ → ℂ)) 2 volume :=
      (low.memLp 2 volume).const_smul (k : ℂ)
    have hm2 : MemLp ((c : ℂ) • (ψ : ℝ → ℂ)) 2 volume :=
      (ψ.memLp 2 volume).const_smul (c : ℂ)
    have hm3 : MemLp (nxt : ℝ → ℂ) 2 volume := nxt.memLp 2 volume
    calc lpNorm (((k : ℂ) • (low : ℝ → ℂ)) + (((c : ℂ) • (ψ : ℝ → ℂ)) + (nxt : ℝ → ℂ))) 2 volume
        ≤ lpNorm ((k : ℂ) • (low : ℝ → ℂ)) 2 volume +
            lpNorm (((c : ℂ) • (ψ : ℝ → ℂ)) + (nxt : ℝ → ℂ)) 2 volume :=
          lpNorm_add_le hm1 (by norm_num)
      _ ≤ lpNorm ((k : ℂ) • (low : ℝ → ℂ)) 2 volume +
            (lpNorm ((c : ℂ) • (ψ : ℝ → ℂ)) 2 volume + lpNorm (nxt : ℝ → ℂ) 2 volume) := by
          gcongr
          exact lpNorm_add_le hm2 (by norm_num)
      _ = (k : ℝ) * lpNorm (low : ℝ → ℂ) 2 volume +
            (|c| * lpNorm (ψ : ℝ → ℂ) 2 volume + lpNorm (nxt : ℝ → ℂ) 2 volume) := by
          rw [lpNorm_const_smul, lpNorm_const_smul]
          simp
  have hlow := hweight_lp (k - 1) j g hgx
  have hψlp := hweight_lp k j g hgx
  have hnxt := hweight_lp k (j + 1) g1 hg1x
  calc |x| ^ k * Real.exp (c * x) * ‖iteratedDeriv j f.val x‖
      = ‖ψ x‖ := hleft
    _ ≤ lpNorm (ψ : ℝ → ℂ) 2 volume +
          lpNorm (SchwartzMap.derivCLM ℂ ℂ ψ : ℝ → ℂ) 2 volume :=
        schwartz_norm_le_lpNorm_add_deriv ψ x
    _ ≤ lpNorm (exponentialDecayL2Integrand a0 (k : ℝ) j f) 2 volume +
          ((k : ℝ) * lpNorm (low : ℝ → ℂ) 2 volume +
            (|c| * lpNorm (ψ : ℝ → ℂ) 2 volume + lpNorm (nxt : ℝ → ℂ) 2 volume)) := by
        gcongr
      _ ≤ lpNorm (exponentialDecayL2Integrand a0 (k : ℝ) j f) 2 volume +
          ((k : ℝ) * lpNorm (exponentialDecayL2Integrand a0 ((k - 1 : ℕ) : ℝ) j f) 2 volume +
            (|c| * lpNorm (exponentialDecayL2Integrand a0 (k : ℝ) j f) 2 volume +
              lpNorm (exponentialDecayL2Integrand a0 (k : ℝ) (j + 1) f) 2 volume)) := by
        gcongr
    _ = (1 + |c|) * lpNorm (exponentialDecayL2Integrand a0 (k : ℝ) j f) 2 volume +
          (k : ℝ) * lpNorm (exponentialDecayL2Integrand a0 ((k - 1 : ℕ) : ℝ) j f) 2 volume +
          lpNorm (exponentialDecayL2Integrand a0 (k : ℝ) (j + 1) f) 2 volume := by
        ring

private theorem twist_seminorm_le (a0 c : ℝ) (hc : |c| < a0) (k n : ℕ)
    (f : PositiveRealExponentialDecay univ) :
    SchwartzMap.seminorm ℂ k n (logExponentialDecayTwist univ ⟨c, mem_univ c⟩ f) ≤
      (k + |c| + 2) * (1 + |c|) ^ n *
        ∑ b ∈ Finset.range (k + 1), ∑ m ∈ Finset.range (n + 2),
          lpNorm (exponentialDecayL2Integrand a0 (b : ℝ) m f) 2 volume := by
  let S := ∑ b ∈ Finset.range (k + 1), ∑ m ∈ Finset.range (n + 2),
    lpNorm (exponentialDecayL2Integrand a0 (b : ℝ) m f) 2 volume
  have hS0 : 0 ≤ S := by
    refine Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ ?_
    exact lpNorm_nonneg
  have hterm (b m : ℕ) (hb : b ≤ k) (hm : m ≤ n + 1) :
      lpNorm (exponentialDecayL2Integrand a0 (b : ℝ) m f) 2 volume ≤ S := by
    have hb' : b ∈ Finset.range (k + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hb)
    have hm' : m ∈ Finset.range (n + 2) := Finset.mem_range.mpr (Nat.lt_succ_of_le hm)
    have hnonneg : ∀ m' ∈ Finset.range (n + 2),
        0 ≤ lpNorm (exponentialDecayL2Integrand a0 (b : ℝ) m' f) 2 volume := by
      intro _ _; exact lpNorm_nonneg
    calc lpNorm (exponentialDecayL2Integrand a0 (b : ℝ) m f) 2 volume
        ≤ ∑ m' ∈ Finset.range (n + 2),
            lpNorm (exponentialDecayL2Integrand a0 (b : ℝ) m' f) 2 volume :=
          Finset.single_le_sum hnonneg hm'
      _ ≤ S := by
        have houter : ∀ b' ∈ Finset.range (k + 1), 0 ≤
            ∑ m' ∈ Finset.range (n + 2),
              lpNorm (exponentialDecayL2Integrand a0 (b' : ℝ) m' f) 2 volume := by
          intro b' hb'
          refine Finset.sum_nonneg fun m' hm' ↦ ?_
          exact lpNorm_nonneg
        exact Finset.single_le_sum houter hb'
  have hbound (j : ℕ) (hj : j ≤ n) :
      (1 + |c|) * lpNorm (exponentialDecayL2Integrand a0 (k : ℝ) j f) 2 volume +
        (k : ℝ) * lpNorm (exponentialDecayL2Integrand a0 ((k - 1 : ℕ) : ℝ) j f) 2 volume +
        lpNorm (exponentialDecayL2Integrand a0 (k : ℝ) (j + 1) f) 2 volume ≤
      (k + |c| + 2) * S := by
    have h1 := hterm k j le_rfl (hj.trans (Nat.le_succ n))
    have h2 := hterm (k - 1) j (Nat.sub_le _ _) (hj.trans (Nat.le_succ n))
    have h3 := hterm k (j + 1) le_rfl (Nat.succ_le_succ hj)
    have hc0 : 0 ≤ |c| := abs_nonneg c
    calc (1 + |c|) * lpNorm (exponentialDecayL2Integrand a0 (k : ℝ) j f) 2 volume +
          (k : ℝ) * lpNorm (exponentialDecayL2Integrand a0 ((k - 1 : ℕ) : ℝ) j f) 2 volume +
          lpNorm (exponentialDecayL2Integrand a0 (k : ℝ) (j + 1) f) 2 volume
        ≤ (1 + |c|) * S + (k : ℝ) * S + S := by
          refine add_le_add (add_le_add ?_ ?_) h3
          · exact mul_le_mul_of_nonneg_left h1 (by positivity)
          · exact mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg k)
      _ = (k + |c| + 2) * S := by ring
  let T : ℝ → ℂ := fun y ↦ (Real.exp (c * y) : ℂ) * f.val y
  have hT : (logExponentialDecayTwist univ ⟨c, mem_univ c⟩ f : ℝ → ℂ) = T := by
    funext y
    exact logExponentialDecayTwist_apply univ ⟨c, mem_univ c⟩ f y
  have hu : ContDiff ℝ ⊤ (fun y : ℝ ↦ (Real.exp (c * y) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((contDiff_const.mul contDiff_id).exp)
  have hformula (x : ℝ) : iteratedDeriv n T x =
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℂ) *
        ((c : ℂ) ^ i * (Real.exp (c * x) : ℂ)) * iteratedDeriv (n - i) f.val x := by
    have hmul := iteratedDeriv_mul
      ((hu.of_le (show (n : ℕ∞ω) ≤ ⊤ from le_top)).contDiffAt (x := x))
      (((decayProfile_smooth f).of_le
        (show (n : ℕ∞ω) ≤ (⊤ : ℕ∞) from by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))).contDiffAt
        (x := x))
    have hfun : ((fun y : ℝ ↦ (Real.exp (c * y) : ℂ)) * f.val) = T := by
      funext y
      rfl
    rw [hfun] at hmul
    rw [hmul]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [iteratedDeriv_expWeight]
  have hpoint (x : ℝ) : |x| ^ k * ‖iteratedDeriv n
      (logExponentialDecayTwist univ ⟨c, mem_univ c⟩ f) x‖ ≤
      (k + |c| + 2) * (1 + |c|) ^ n * S := by
    rw [hT]
    rw [hformula]
    calc |x| ^ k * ‖∑ i ∈ Finset.range (n + 1), (n.choose i : ℂ) *
          ((c : ℂ) ^ i * (Real.exp (c * x) : ℂ)) * iteratedDeriv (n - i) f.val x‖
        ≤ |x| ^ k * ∑ i ∈ Finset.range (n + 1), ‖(n.choose i : ℂ) *
            ((c : ℂ) ^ i * (Real.exp (c * x) : ℂ)) * iteratedDeriv (n - i) f.val x‖ := by
          gcongr
          exact norm_sum_le _ _
      _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * |c| ^ i *
            (|x| ^ k * Real.exp (c * x) * ‖iteratedDeriv (n - i) f.val x‖) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [norm_mul, norm_mul, norm_mul, Complex.norm_natCast, norm_pow,
            Complex.norm_real, Real.norm_eq_abs, Complex.norm_real,
            Real.norm_of_nonneg (Real.exp_pos _).le]
          ring
      _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * |c| ^ i * ((k + |c| + 2) * S) := by
          refine Finset.sum_le_sum fun i hi ↦ ?_
          have hi' : n - i ≤ n := Nat.sub_le _ _
          have hineq := (expMul_profile_sup_le a0 c hc k (n - i) f x).trans
            (hbound (n - i) hi')
          exact mul_le_mul_of_nonneg_left hineq (by positivity)
      _ = (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * |c| ^ i) * ((k + |c| + 2) * S) := by
          rw [← Finset.sum_mul]
      _ = (1 + |c|) ^ n * ((k + |c| + 2) * S) := by
          have hbin : ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * |c| ^ i =
              (1 + |c|) ^ n := by
            rw [add_comm (1 : ℝ) |c|, add_pow]
            exact Finset.sum_congr rfl fun i _ ↦ by simp [one_pow, mul_one, mul_comm]
          rw [hbin]
      _ = (k + |c| + 2) * (1 + |c|) ^ n * S := by ring
  refine SchwartzMap.seminorm_le_bound' ℂ k n _ ?_ hpoint
  positivity

private theorem seminorm_double_sum_apply {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (p : ι → κ → Seminorm ℂ (PositiveRealExponentialDecay univ)) (s : Finset ι) (t : Finset κ)
    (f : PositiveRealExponentialDecay univ) :
    (∑ i ∈ s, ∑ j ∈ t, p i j) f = ∑ i ∈ s, ∑ j ∈ t, (p i j) f := by
  let E0 := PositiveRealExponentialDecay univ
  let phi : Seminorm ℂ E0 →+ (E0 → ℝ) := FunLike.coeAddMonoidHom (Seminorm ℂ E0) E0 ℝ
  change (phi (∑ i ∈ s, ∑ j ∈ t, p i j)) f = _
  rw [map_sum phi (fun i => ∑ j ∈ t, p i j) s]
  have heval : (∑ i ∈ s, phi (∑ j ∈ t, p i j)) f =
      (Pi.evalAddMonoidHom (fun _ : E0 => ℝ) f) (∑ i ∈ s, phi (∑ j ∈ t, p i j)) := rfl
  rw [heval, map_sum (Pi.evalAddMonoidHom (fun _ : E0 => ℝ) f)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_sum phi (fun j => p i j) t]
  rw [map_sum (Pi.evalAddMonoidHom (fun _ : E0 => ℝ) f)]
  rfl

/-- Paper: Lemma D.3.2.7(3), p. 803. The same topology is generated by including
all nonnegative integer logarithmic weights. -/
theorem exponentialDecayL2_log_generates (a : ℕ → ℝ) (ha : ∀ n, 0 < a n)
    (hunbounded : ¬ BddAbove (range a)) :
    GeneratesLpSeminorms volume 2
      (fun (i : ℕ × ℕ × ℕ) ↦ exponentialDecayL2Integrand (a i.1) i.2.1 i.2.2) := by
  have hmem (i : ℕ × ℕ × ℕ) (f : PositiveRealExponentialDecay univ) :
      MemLp (exponentialDecayL2Integrand (a i.1) (i.2.1 : ℝ) i.2.2 f) 2 volume :=
    (exponentialDecayL2_continuous_seminorm (a i.1) (i.2.1 : ℝ) (ha i.1)
      (Nat.cast_nonneg _) i.2.2).1 f
  let P : SeminormFamily ℂ (PositiveRealExponentialDecay univ) (ℕ × ℕ × ℕ) := fun i ↦
    Classical.choose (exponentialDecayL2_continuous_seminorm (a i.1) (i.2.1 : ℝ) (ha i.1)
      (Nat.cast_nonneg _) i.2.2).2
  have hPspec (i : ℕ × ℕ × ℕ) := Classical.choose_spec
    (exponentialDecayL2_continuous_seminorm (a i.1) (i.2.1 : ℝ) (ha i.1)
      (Nat.cast_nonneg _) i.2.2).2
  have hPcont (i : ℕ × ℕ × ℕ) : Continuous (P i) := (hPspec i).1
  have hPval (i : ℕ × ℕ × ℕ) (f : PositiveRealExponentialDecay univ) :
      ENNReal.ofReal (P i f) =
        eLpNorm (exponentialDecayL2Integrand (a i.1) (i.2.1 : ℝ) i.2.2 f) 2 volume :=
    (hPspec i).2 f
  have hPeq (i : ℕ × ℕ × ℕ) (f : PositiveRealExponentialDecay univ) :
      P i f = lpNorm (exponentialDecayL2Integrand (a i.1) (i.2.1 : ℝ) i.2.2 f) 2 volume := by
    rw [← ENNReal.toReal_ofReal (apply_nonneg (P i) f), hPval i f, toReal_eLpNorm]
  refine ⟨hmem, P, ?_, hPval⟩
  let t : TopologicalSpace (PositiveRealExponentialDecay univ) := inferInstance
  let u := P.moduleFilterBasis.topology
  have hPu : WithSeminorms (topology := u) P := ⟨rfl⟩
  refine WithSeminorms.mk (topology := t) ?_
  change t = u
  apply le_antisymm
  · exact le_topology_withSeminorms (t := t) hPu hPcont
  · let I0 : Set ℝ := univ
    let Q := fun (i : I0 × ℕ × ℕ) ↦
      (SchwartzMap.seminorm ℂ i.2.1 i.2.2).comp (logExponentialDecayTwist I0 i.1)
    have hQ := withGeneratingSeminorms_spec (logExponentialDecaySubmodule (univ : Set ℝ)) Q
    let : TopologicalSpace (PositiveRealExponentialDecay univ) := u
    let : IsTopologicalAddGroup (PositiveRealExponentialDecay univ) := hPu.isTopologicalAddGroup
    apply le_topology_withSeminorms (t := u) hQ
    rintro ⟨⟨c, hc⟩, k, n⟩
    obtain ⟨_, ⟨n0, rfl⟩, hn0⟩ :=
      (not_bddAbove_iff.mp (show ¬ BddAbove (range a) by assumption)) |c|
    let C : ℝ≥0 := ⟨(k + |c| + 2) * (1 + |c|) ^ n, by positivity⟩
    let S : Seminorm ℂ (PositiveRealExponentialDecay univ) :=
      ∑ b ∈ Finset.range (k + 1), ∑ m ∈ Finset.range (n + 2), P (n0, b, m)
    have hScont : Continuous (S : PositiveRealExponentialDecay univ → ℝ) := by
      dsimp [S]
      refine Seminorm.continuous_finsetSum ?_
      intro b hb
      refine Seminorm.continuous_finsetSum ?_
      intro m hm
      exact hPu.continuous_seminorm (n0, b, m)
    apply Seminorm.continuous_of_le (q := C • S) (hScont.const_smul C)
    refine (Seminorm.le_def).2 ?_
    intro f
    rw [Seminorm.comp_apply]
    change (SchwartzMap.seminorm ℂ k n) (logExponentialDecayTwist I0 ⟨c, hc⟩ f) ≤
      (C : ℝ) * S f
    have hsum : S f = ∑ b ∈ Finset.range (k + 1), ∑ m ∈ Finset.range (n + 2),
        P (n0, b, m) f := by
      simpa [S] using seminorm_double_sum_apply (fun b m => P (n0, b, m))
        (Finset.range (k + 1)) (Finset.range (n + 2)) f
    have htwist := twist_seminorm_le (a n0) c hn0 k n f
    rw [hsum]
    refine le_trans (by convert htwist using 1) ?_
    have hlp : ∑ b ∈ Finset.range (k + 1), ∑ m ∈ Finset.range (n + 2),
        lpNorm (exponentialDecayL2Integrand (a n0) (b : ℝ) m f) 2 volume =
        ∑ b ∈ Finset.range (k + 1), ∑ m ∈ Finset.range (n + 2), P (n0, b, m) f := by
      refine Finset.sum_congr rfl fun b _ ↦ Finset.sum_congr rfl fun m _ ↦ ?_
      exact (hPeq (n0, b, m) f).symm
    rw [hlp]
    have hC : (C : ℝ) = ((k : ℝ) + |c| + 2) * (1 + |c|) ^ n := by
      simp only [C]
      exact Subtype.coe_mk _ _
    rw [hC]

end PositiveReal

section Modulated

variable {G : Type*} [CommGroup G] [TopologicalSpace G]
variable (m : G →ₜ* ℝ≥0ˣ) (I : Set ℝ)

/-- Paper: Definition D.3.3.1, p. 804. Multiply a function by the real power
of the modulation at each point. -/
def modulationWeight (a : ℝ) : (G → ℂ) →ₗ[ℂ] (G → ℂ) :=
  LinearMap.mulLeft ℂ (fun g : G ↦ (((m g).val : ℝ) ^ a : ℝ))

/-- Paper: Definition D.3.3.1, p. 804. Weighting at exponent zero is
the identity. -/
theorem modulationWeight_zero (f : G → ℂ) : modulationWeight m 0 f = f := by
  ext g
  simp [modulationWeight]

/-- Paper: Definition D.3.3.1, p. 804. All real twists with exponents in I
must lie in the Schwartz–Bruhat submodule.
Forward, backward and two-sided exponential decay use `Ici 0`, `Iic 0` and `univ`.
Deviation: Continuity follows from any one twist when I is nonempty. -/
def modulatedExponentialDecaySubmodule : Submodule ℂ (G → ℂ) :=
  ⨅ a : I, (schwartzBruhatSubmodule G).comap (modulationWeight m a)

/-- Paper: Definition D.3.3.1, p. 804. The exponent set containing only zero
recovers the ordinary Schwartz–Bruhat functions. -/
theorem modulatedExponentialDecaySubmodule_singleton_zero :
    modulatedExponentialDecaySubmodule m {0} = schwartzBruhatSubmodule G := by
  ext f
  simp only [modulatedExponentialDecaySubmodule, Submodule.mem_iInf, Submodule.mem_comap]
  constructor
  · intro h
    simpa [modulationWeight_zero] using h ⟨0, rfl⟩
  · rintro hf ⟨a, ha⟩
    obtain rfl : a = 0 := ha
    simpa [modulationWeight_zero] using hf

/-- Paper: (D.3.3.2), p. 805. The given exponent supplies the corresponding
Schwartz–Bruhat membership. -/
theorem modulationWeight_mem_schwartzBruhat (a : I) (f : modulatedExponentialDecaySubmodule m I) :
    modulationWeight m a f.val ∈ schwartzBruhatSubmodule G :=
  Submodule.mem_comap.1 (Submodule.mem_iInf _ |>.1 f.2 a)

/-- Paper: (D.3.3.2), p. 805. The linear map Tₐ sends a function in the decay
submodule to its weighted Schwartz–Bruhat function. -/
def modulatedExponentialDecayTwist (a : I) :
    modulatedExponentialDecaySubmodule m I →ₗ[ℂ] SchwartzBruhat G :=
  ((modulationWeight m a).comp (modulatedExponentialDecaySubmodule m I).subtype).codRestrict
    (schwartzBruhatSubmodule G) (modulationWeight_mem_schwartzBruhat m I a)

/-- Paper: (D.3.3.2), p. 805. The bundled twist evaluates to the pointwise
product with the power of the modulation. -/
theorem modulatedExponentialDecayTwist_apply (a : I) (f : modulatedExponentialDecaySubmodule m I)
    (g : G) :
    modulatedExponentialDecayTwist m I a f g = ((((m g).val : ℝ) ^ (a : ℝ) : ℝ) : ℂ) * f.val g :=
  rfl

variable [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]

/-- Paper: Definition D.3.3.1, p. 804. Inverse left translation preserves
the decay submodule. -/
theorem modulatedExponentialDecaySubmodule_translate (hm : IsModulation m) (hms : Surjective m)
    (g : G) (f : modulatedExponentialDecaySubmodule m I) :
    (fun x : G ↦ f.val (g⁻¹ * x)) ∈ modulatedExponentialDecaySubmodule m I := by
  let translate : (G → ℂ) →ₗ[ℂ] (G → ℂ) :=
    LinearMap.pi fun x ↦ LinearMap.proj (g⁻¹ * x)
  have htranslate : schwartzBruhatSubmodule G ≤ (schwartzBruhatSubmodule G).comap translate := by
    intro f hf
    exact schwartzBruhat_translate_mem g ⟨f, hf⟩
  refine (Submodule.mem_iInf _).2 fun a ↦ Submodule.mem_comap.2 ?_
  let weight (x : G) : ℂ := (((m x).val : ℝ) ^ (a : ℝ) : ℝ)
  have hweight (x : G) : weight x = weight g * weight (g⁻¹ * x) := by
    have hx : (m x).val = (m g).val * (m (g⁻¹ * x)).val := by
      rw [← Units.val_mul, ← map_mul, mul_inv_cancel_left]
    unfold weight
    rw [hx, NNReal.coe_mul, Real.mul_rpow (NNReal.coe_nonneg _) (NNReal.coe_nonneg _),
      Complex.ofReal_mul]
  have htwist : modulationWeight m a (fun x ↦ f.val (g⁻¹ * x)) =
      weight g • translate (modulationWeight m a f.val) := by
    funext x
    change weight x * f.val (g⁻¹ * x) = weight g * (weight (g⁻¹ * x) * f.val (g⁻¹ * x))
    rw [hweight, mul_assoc]
  rw [htwist]
  exact (schwartzBruhatSubmodule G).smul_mem _ (htranslate (modulationWeight_mem_schwartzBruhat m I a f))

/-- An iterated derivative may be evaluated after transporting its order along an equality. -/
private theorem iteratedFDeriv_cast_len {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (P : X → Y) (x : X) {n k : ℕ} (h : n = k)
    (w : Fin n → X) :
    iteratedFDeriv ℝ n P x w = iteratedFDeriv ℝ k P x (w ∘ Fin.cast h.symm) := by
  subst h; rfl

/-- Differentiating along a list ending in `v` is differentiating `∂ᵥP` along the rest. -/
private theorem iteratedFDeriv_list_concat {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {P : X → ℂ} (hP : ContDiff ℝ ∞ P) (L : List X) (v x : X) :
    iteratedFDeriv ℝ (L ++ [v]).length P x (L ++ [v]).get =
      iteratedFDeriv ℝ L.length (fun y ↦ fderiv ℝ P y v) x L.get := by
  rw [iteratedFDeriv_cast_len P x (by simp : (L ++ [v]).length = L.length + 1),
    iteratedFDeriv_succ_apply_right,
    iteratedFDeriv_clm_apply_const_apply (hP.fderiv_right (m := ∞) le_rfl) (mod_cast le_top)]
  congr 2
  · funext i
    simp [Fin.init, List.getElem_append_left]
  · simp [List.getElem_append_right]

/-- Leibniz bound along an ordered list of directions: the derivative of `ψ * P` is
controlled by the derivatives of `P` along the sublists of the list. -/
private theorem norm_iteratedFDeriv_list_mul_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (L : List X) : ∀ (ψ P : X → ℂ), ContDiff ℝ ∞ ψ → ContDiff ℝ ∞ P → ∀ (x : X) (C : ℝ),
      (∀ k ≤ L.length, ‖iteratedFDeriv ℝ k ψ x‖ ≤ C) →
      ‖iteratedFDeriv ℝ L.length (fun y ↦ ψ y * P y) x L.get‖ ≤
        C * (L.map fun v ↦ 1 + ‖v‖).prod *
          (L.sublists.map fun L' ↦ ‖iteratedFDeriv ℝ L'.length P x L'.get‖).sum := by
  induction L using List.reverseRecOn with
  | nil =>
    intro ψ P _ _ x C hC
    have h0 := hC 0 le_rfl
    rw [norm_iteratedFDeriv_zero] at h0
    simp only [List.length_nil, iteratedFDeriv_zero_apply, List.map_nil, List.prod_nil, mul_one,
      List.sublists_nil, norm_mul]
    simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      List.length_nil, iteratedFDeriv_zero_apply] using
      mul_le_mul_of_nonneg_right h0 (norm_nonneg (P x))
  | append_singleton L v ih =>
    intro ψ P hψ hP x C hC
    rw [iteratedFDeriv_list_concat (hψ.mul hP)]
    have hfd : (fun y ↦ fderiv ℝ (fun y ↦ ψ y * P y) y v) =
        fun y ↦ fderiv ℝ ψ y v * P y + ψ y * fderiv ℝ P y v := by
      funext y
      rw [fderiv_fun_mul ((hψ.differentiable (by simp)) y) ((hP.differentiable (by simp)) y)]
      simp only [add_apply, smul_apply, smul_eq_mul]
      ring
    have hψv : ContDiff ℝ ∞ (fun y ↦ fderiv ℝ ψ y v) :=
      (hψ.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const
    have hPv : ContDiff ℝ ∞ (fun y ↦ fderiv ℝ P y v) :=
      (hP.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const
    have hadd : iteratedFDeriv ℝ L.length
        (fun y ↦ fderiv ℝ ψ y v * P y + ψ y * fderiv ℝ P y v) x =
        iteratedFDeriv ℝ L.length (fun y ↦ fderiv ℝ ψ y v * P y) x +
          iteratedFDeriv ℝ L.length (fun y ↦ ψ y * fderiv ℝ P y v) x :=
      iteratedFDeriv_add_apply ((hψv.mul hP).contDiffAt.of_le (mod_cast le_top))
        ((hψ.mul hPv).contDiffAt.of_le (mod_cast le_top))
    rw [hfd, hadd]
    rw [add_apply]
    have hC1 : ∀ k ≤ L.length, ‖iteratedFDeriv ℝ k (fun y ↦ fderiv ℝ ψ y v) x‖ ≤ ‖v‖ * C := by
      intro k hk
      calc _ ≤ ‖v‖ * ‖iteratedFDeriv ℝ k (fderiv ℝ ψ) x‖ :=
            norm_iteratedFDeriv_clm_apply_const
              (hψ.fderiv_right (m := ∞) le_rfl).contDiffAt (mod_cast le_top)
        _ ≤ ‖v‖ * C := by
          rw [norm_iteratedFDeriv_fderiv]
          exact mul_le_mul_of_nonneg_left (hC (k + 1) (by simp; omega)) (norm_nonneg _)
    have hC2 : ∀ k ≤ L.length, ‖iteratedFDeriv ℝ k ψ x‖ ≤ C :=
      fun k hk ↦ hC k (by simp; omega)
    have h1 := ih _ P hψv hP x _ hC1
    have h2 := ih ψ _ hψ hPv x C hC2
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 (Nat.zero_le _))
    set Pr := (L.map fun v ↦ 1 + ‖v‖).prod
    have hPr : 0 ≤ Pr := List.prod_nonneg (by simp; intro a _; positivity)
    set S₁ := (L.sublists.map fun L' ↦ ‖iteratedFDeriv ℝ L'.length P x L'.get‖).sum
    set S₂ := (L.sublists.map fun L' ↦
      ‖iteratedFDeriv ℝ L'.length (fun y ↦ fderiv ℝ P y v) x L'.get‖).sum
    have hS₁ : 0 ≤ S₁ := List.sum_nonneg (by simp)
    have hS₂ : 0 ≤ S₂ := List.sum_nonneg (by simp)
    have hS : (((L ++ [v]).sublists).map fun L' ↦ ‖iteratedFDeriv ℝ L'.length P x L'.get‖).sum =
        S₁ + S₂ := by
      rw [List.sublists_concat, List.map_append, List.sum_append, List.map_map]
      congr 1
      congr 1
      apply List.map_congr_left
      intro L' _
      simp only [Function.comp_apply]
      rw [iteratedFDeriv_list_concat hP]
    rw [hS, List.map_append, List.prod_append]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ ‖v‖ * C * Pr * S₁ + C * Pr * S₂ := add_le_add h1 h2
      _ ≤ C * (Pr * (1 + ‖v‖)) * (S₁ + S₂) := by
        have : 0 ≤ C * Pr := mul_nonneg hC0 hPr
        nlinarith [mul_nonneg this hS₁, mul_nonneg this hS₂, mul_nonneg (mul_nonneg this hS₂) (norm_nonneg v),
          mul_nonneg (mul_nonneg this hS₁) (norm_nonneg v)]

/-- A sublist of a concatenation of constant blocks is again such a concatenation. -/
private theorem sublist_flatten_ofFn_replicate {X : Type*} :
    ∀ {k : ℕ} (u : Fin k → X) (β : Fin k → ℕ) {L' : List X},
      List.Sublist L' (List.ofFn fun i ↦ List.replicate (β i) (u i)).flatten →
        ∃ β' : Fin k → ℕ, L' = (List.ofFn fun i ↦ List.replicate (β' i) (u i)).flatten := by
  intro k
  induction k with
  | zero =>
    intro u β L' h
    refine ⟨β, ?_⟩
    simpa using h
  | succ k ih =>
    intro u β L' h
    rw [List.ofFn_succ, List.flatten_cons, List.sublist_append_iff] at h
    obtain ⟨r₁, r₂, rfl, h₁, h₂⟩ := h
    obtain ⟨j, -, rfl⟩ := List.sublist_replicate_iff.mp h₁
    obtain ⟨β'', rfl⟩ := ih (fun i ↦ u i.succ) (fun i ↦ β i.succ) h₂
    refine ⟨Fin.cons j β'', ?_⟩
    rw [List.ofFn_succ, List.flatten_cons]
    simp

/-- Derivatives of a function of an affine real functional. -/
private theorem norm_iteratedFDeriv_comp_affine_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ) (ℓ : X →L[ℝ] ℝ) (c : ℝ) (k : ℕ) (x : X) :
    ‖iteratedFDeriv ℝ k (fun y ↦ φ (ℓ y + c)) x‖ ≤ ‖iteratedFDeriv ℝ k φ (ℓ x + c)‖ * ‖ℓ‖ ^ k := by
  have hc : ContDiff ℝ ∞ (fun t ↦ φ (t + c)) := hφ.comp (contDiff_id.add contDiff_const)
  have h := ℓ.iteratedFDeriv_comp_right hc x (i := k) (mod_cast le_top)
  have h' : (fun y ↦ φ (ℓ y + c)) = (fun t ↦ φ (t + c)) ∘ ℓ := rfl
  rw [h', h, iteratedFDeriv_comp_add_right]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  simp

/-- Multiplying an elementary Schwartz function by `φ ∘ Λ` keeps it Schwartz, when `Λ` is
affine on each fibre of the cover and `φ` has bounded derivatives of all orders. -/
private theorem elementarySchwartz_mul_affine_mem {m n r : ℕ} {F : Type*} [AddCommGroup F]
    [TopologicalSpace F] [DiscreteTopology F] [Finite F]
    {s : ElementaryLieGroup m n r F → ℂ} (hs : s ∈ elementarySchwartzSubmodule m n r F)
    (Λ : ElementaryLieGroup m n r F → ℝ)
    (ℓ : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hΛ : ∀ xt a b, Λ (elementaryCover xt a b) = ℓ xt + Λ (elementaryCover 0 a b))
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ) (hφb : ∀ k, ∃ C, ∀ t, ‖iteratedFDeriv ℝ k φ t‖ ≤ C) :
    (fun y ↦ φ (Λ y) * s y) ∈ elementarySchwartzSubmodule m n r F := by
  classical
  let X := EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
  have hpull (a : Fin r → ℤ) (b : F) :
      (fun xt ↦ φ (Λ (elementaryCover xt a b)) * s (elementaryCover xt a b)) =
        fun xt ↦ φ (ℓ xt + Λ (elementaryCover 0 a b)) * s (elementaryCover xt a b) := by
    funext xt
    rw [hΛ]
  have hψ (c : ℝ) : ContDiff ℝ ∞ (fun xt : X ↦ φ (ℓ xt + c)) :=
    hφ.comp (ℓ.contDiff.add contDiff_const)
  refine ⟨fun a b ↦ ?_, fun i ↦ ?_⟩
  · change ContDiff ℝ ∞ (fun xt ↦ φ (Λ (elementaryCover xt a b)) * s (elementaryCover xt a b))
    rw [hpull]
    exact (hψ _).mul (hs.1 a b)
  obtain ⟨α, β, γ, δ⟩ := i
  let D (β : Fin m → ℕ) (γ : Fin n → ℕ) : List X :=
    (List.ofFn (fun i : Fin m ↦ List.replicate (β i)
      ((EuclideanSpace.single i 1 : EuclideanSpace ℝ (Fin m)), (0 : EuclideanSpace ℝ (Fin n))))).flatten ++
    (List.ofFn (fun i : Fin n ↦ List.replicate (γ i)
      ((0 : EuclideanSpace ℝ (Fin m)), (EuclideanSpace.single i 1 : EuclideanSpace ℝ (Fin n))))).flatten
  have hpartial (f : ElementaryLieGroup m n r F → ℂ) (β : Fin m → ℕ) (γ : Fin n → ℕ) (xt : X)
      (a : Fin r → ℤ) (b : F) : elementaryPartial f β γ xt a b =
        iteratedFDeriv ℝ (D β γ).length (fun v ↦ f (elementaryCover v a b)) xt (D β γ).get := rfl
  have hsub (L' : List X) (h : List.Sublist L' (D β γ)) : ∃ β' γ', L' = D β' γ' := by
    obtain ⟨r₁, r₂, rfl, h₁, h₂⟩ := List.sublist_append_iff.mp h
    obtain ⟨β', rfl⟩ := sublist_flatten_ofFn_replicate _ _ h₁
    obtain ⟨γ', rfl⟩ := sublist_flatten_ofFn_replicate _ _ h₂
    exact ⟨β', γ', rfl⟩
  let mono (xt : X) (a : Fin r → ℤ) : ℂ :=
    (∏ k, (xt.1 k : ℂ) ^ α k) * (∏ k, (a k : ℂ) ^ δ k)
  let T (L' : List X) : ℝ≥0∞ := ⨆ (xt : X) (a : Fin r → ℤ) (b : F),
    (‖mono xt a * iteratedFDeriv ℝ L'.length (fun v ↦ s (elementaryCover v a b)) xt L'.get‖₊ : ℝ≥0∞)
  have hT (L' : List X) (h : L' ∈ (D β γ).sublists) : T L' < ⊤ := by
    obtain ⟨β', γ', rfl⟩ := hsub L' (List.mem_sublists.mp h)
    exact hs.2 (α, β', γ', δ)
  have hTle (L' : List X) (h : L' ∈ (D β γ).sublists) (xt : X) (a : Fin r → ℤ) (b : F) :
      ‖mono xt a * iteratedFDeriv ℝ L'.length (fun v ↦ s (elementaryCover v a b)) xt L'.get‖ ≤
        (T L').toReal := by
    have := ENNReal.toReal_mono (hT L' h).ne
      (le_iSup_of_le xt (le_iSup_of_le a (le_iSup_of_le b le_rfl)) :
        (‖mono xt a * iteratedFDeriv ℝ L'.length (fun v ↦ s (elementaryCover v a b)) xt L'.get‖₊ :
          ℝ≥0∞) ≤ T L')
    simpa using this
  let N := (D β γ).length
  choose B hB using hφb
  let Cψ : ℝ := ∑ k ∈ Finset.range (N + 1), B k * ‖ℓ‖ ^ k
  have hB0 (k : ℕ) : 0 ≤ B k := (norm_nonneg _).trans (hB k 0)
  have hCψ (c : ℝ) (xt : X) : ∀ k ≤ N, ‖iteratedFDeriv ℝ k (fun xt : X ↦ φ (ℓ xt + c)) xt‖ ≤ Cψ := by
    intro k hk
    calc _ ≤ ‖iteratedFDeriv ℝ k φ (ℓ xt + c)‖ * ‖ℓ‖ ^ k :=
          norm_iteratedFDeriv_comp_affine_le hφ ℓ c k xt
      _ ≤ B k * ‖ℓ‖ ^ k := mul_le_mul_of_nonneg_right (hB k _) (by positivity)
      _ ≤ Cψ := Finset.single_le_sum (f := fun k ↦ B k * ‖ℓ‖ ^ k)
          (fun j _ ↦ mul_nonneg (hB0 j) (by positivity)) (Finset.mem_range.mpr (by omega))
  let Pr := ((D β γ).map fun v ↦ 1 + ‖v‖).prod
  have hPr : 0 ≤ Pr := List.prod_nonneg (by simp; intro a _; positivity)
  have hCψ0 : 0 ≤ Cψ := Finset.sum_nonneg fun j _ ↦ mul_nonneg (hB0 j) (by positivity)
  let K := Cψ * Pr * ((D β γ).sublists.map fun L' ↦ (T L').toReal).sum
  refine lt_of_le_of_lt (?_ : _ ≤ ENNReal.ofReal K) ENNReal.ofReal_lt_top
  refine iSup_le fun xt ↦ iSup_le fun a ↦ iSup_le fun b ↦ ?_
  rw [← ENNReal.ofReal_coe_nnreal, coe_nnNorm]
  apply ENNReal.ofReal_le_ofReal
  change ‖mono xt a * elementaryPartial (fun y ↦ φ (Λ y) * s y) β γ xt a b‖ ≤ K
  rw [hpartial]
  change ‖mono xt a * iteratedFDeriv ℝ (D β γ).length
    (fun xt ↦ φ (Λ (elementaryCover xt a b)) * s (elementaryCover xt a b)) xt (D β γ).get‖ ≤ K
  rw [hpull, norm_mul]
  have hL := norm_iteratedFDeriv_list_mul_le (D β γ) _ _ (hψ (Λ (elementaryCover 0 a b))) (hs.1 a b)
    xt Cψ (hCψ _ xt)
  calc _ ≤ ‖mono xt a‖ * (Cψ * Pr * ((D β γ).sublists.map fun L' ↦
        ‖iteratedFDeriv ℝ L'.length (fun v ↦ s (elementaryCover v a b)) xt L'.get‖).sum) :=
        mul_le_mul_of_nonneg_left hL (norm_nonneg _)
    _ = Cψ * Pr * ((D β γ).sublists.map fun L' ↦
        ‖mono xt a * iteratedFDeriv ℝ L'.length (fun v ↦ s (elementaryCover v a b)) xt L'.get‖).sum := by
        rw [mul_left_comm, ← List.sum_map_mul_left]
        simp only [norm_mul]
    _ ≤ K := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hCψ0 hPr)
        exact List.sum_le_sum fun L' h ↦ hTle L' h xt a b

/-- Real derivatives of the restriction to the real line of a function holomorphic near it. -/
private theorem iteratedDeriv_comp_ofReal_of_differentiableOn {h : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hR : ∀ t : ℝ, (t : ℂ) ∈ U) (hh : DifferentiableOn ℂ h U) (k : ℕ) :
    iteratedDeriv k (fun t : ℝ ↦ h t) = fun t : ℝ ↦ iteratedDeriv k h t := by
  have han : ∀ j, AnalyticOnNhd ℂ (iteratedDeriv j h) U := by
    intro j
    induction j with
    | zero => simpa using hh.analyticOnNhd hU
    | succ j ih => rw [iteratedDeriv_succ]; exact fun z hz ↦ (ih z hz).deriv
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    rw [iteratedDeriv_succ]
    exact ((han k t (hR t)).differentiableAt.hasDerivAt.comp_ofReal).deriv

/-- The weight `(e^{-αt} + e^{βt})⁻¹` is smooth with bounded derivatives of all orders,
by Cauchy estimates on a horizontal strip. -/
private theorem twoSidedExpWeight_bounds_of_nonneg {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    ContDiff ℝ ∞ (fun t : ℝ ↦ (((Real.exp (-α * t) + Real.exp (β * t))⁻¹ : ℝ) : ℂ)) ∧
      ∀ k, ∃ C, ∀ t, ‖iteratedFDeriv ℝ k
        (fun t : ℝ ↦ (((Real.exp (-α * t) + Real.exp (β * t))⁻¹ : ℝ) : ℂ)) t‖ ≤ C := by
  have hpos (t : ℝ) : 0 < Real.exp (-α * t) + Real.exp (β * t) := by positivity
  refine ⟨?_, fun k ↦ ?_⟩
  · have h1 : ContDiff ℝ ∞ (fun t : ℝ ↦ Real.exp (-α * t)) :=
      Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
    have h2 : ContDiff ℝ ∞ (fun t : ℝ ↦ Real.exp (β * t)) :=
      Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
    exact Complex.ofRealCLM.contDiff.comp ((h1.add h2).inv fun t ↦ (hpos t).ne')
  set δ := 1 / (α + β + 1) with hδdef
  have hδ : 0 < δ := by positivity
  let h : ℂ → ℂ := fun z ↦ (Complex.exp (-α * z) + Complex.exp (β * z))⁻¹
  let U : Set ℂ := Complex.im ⁻¹' Ioo (-δ) δ
  have hU : IsOpen U := isOpen_Ioo.preimage Complex.continuous_im
  have hcos (c : ℝ) (hc : |c| ≤ 1) : 1 / 2 ≤ Real.cos c := by
    have h1 := Real.one_sub_sq_div_two_le_cos (x := c)
    have h2 : c ^ 2 ≤ 1 := by
      rw [← sq_abs]; nlinarith [abs_nonneg c]
    linarith
  have hre (z : ℂ) (hz : |z.im| ≤ δ) :
      1 / 2 ≤ (Complex.exp (-α * z) + Complex.exp (β * z)).re := by
    rw [Complex.add_re, Complex.exp_re, Complex.exp_re]
    have e1 : (-(α : ℂ) * z).re = -α * z.re := by simp
    have e2 : (-(α : ℂ) * z).im = -α * z.im := by simp
    have e3 : ((β : ℂ) * z).re = β * z.re := by simp
    have e4 : ((β : ℂ) * z).im = β * z.im := by simp
    rw [e1, e2, e3, e4]
    have hαδ : α * δ ≤ 1 := by
      rw [hδdef, mul_one_div, div_le_one (by positivity)]; linarith
    have hβδ : β * δ ≤ 1 := by
      rw [hδdef, mul_one_div, div_le_one (by positivity)]; linarith
    have c1 : 1 / 2 ≤ Real.cos (-α * z.im) := hcos _ (by
      rw [abs_mul, abs_neg, abs_of_nonneg hα]
      exact (mul_le_mul_of_nonneg_left hz hα).trans hαδ)
    have c2 : 1 / 2 ≤ Real.cos (β * z.im) := hcos _ (by
      rw [abs_mul, abs_of_nonneg hβ]
      exact (mul_le_mul_of_nonneg_left hz hβ).trans hβδ)
    have hsum : 1 ≤ Real.exp (-α * z.re) + Real.exp (β * z.re) := by
      rcases le_total 0 z.re with h0 | h0
      · have := Real.one_le_exp (show 0 ≤ β * z.re by positivity)
        linarith [Real.exp_pos (-α * z.re)]
      · have := Real.one_le_exp (mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hα) h0)
        linarith [Real.exp_pos (β * z.re)]
    nlinarith [Real.exp_pos (-α * z.re), Real.exp_pos (β * z.re)]
  have hne (z : ℂ) (hz : |z.im| ≤ δ) : Complex.exp (-α * z) + Complex.exp (β * z) ≠ 0 := by
    intro h0
    have := hre z hz
    rw [h0, Complex.zero_re] at this
    linarith
  have hbound (z : ℂ) (hz : |z.im| ≤ δ) : ‖h z‖ ≤ 2 := by
    have h1 := (hre z hz).trans (Complex.re_le_norm _)
    simp only [h, norm_inv]
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have hh : DifferentiableOn ℂ h U := by
    intro z hz
    have hz' : |z.im| ≤ δ := (abs_lt.mpr hz).le
    apply DifferentiableAt.differentiableWithinAt
    exact (((differentiableAt_const _).mul differentiableAt_id).cexp.add
      ((differentiableAt_const _).mul differentiableAt_id).cexp).inv (hne z hz')
  have hφ : (fun t : ℝ ↦ (((Real.exp (-α * t) + Real.exp (β * t))⁻¹ : ℝ) : ℂ)) =
      fun t : ℝ ↦ h t := by
    funext t
    simp only [h]
    push_cast
    rfl
  refine ⟨k.factorial * 2 / (δ / 2) ^ k, fun t ↦ ?_⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hφ,
    iteratedDeriv_comp_ofReal_of_differentiableOn hU (fun t ↦ by simp [U, hδ]) hh]
  have hsub : Metric.closedBall (t : ℂ) (δ / 2) ⊆ U := by
    intro z hz
    have h1 := (Complex.abs_im_le_norm (z - t)).trans (mem_closedBall_iff_norm.mp hz)
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at h1
    exact abs_lt.mp (by linarith)
  refine Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k (by positivity)
    (hh.diffContOnCl_ball hsub) fun z hz ↦ hbound z ?_
  have h1 := (Complex.abs_im_le_norm (z - t)).trans (mem_sphere_iff_norm.mp hz).le
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at h1
  linarith

/-- The two-sided exponential weight has bounded derivatives for positive exponents. -/
private theorem twoSidedExpWeight_bounds {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ContDiff ℝ ∞ (fun t : ℝ ↦ (((Real.exp (-α * t) + Real.exp (β * t))⁻¹ : ℝ) : ℂ)) ∧
      ∀ k, ∃ C, ∀ t, ‖iteratedFDeriv ℝ k
        (fun t : ℝ ↦ (((Real.exp (-α * t) + Real.exp (β * t))⁻¹ : ℝ) : ℂ)) t‖ ≤ C :=
  twoSidedExpWeight_bounds_of_nonneg hα.le hβ.le

/-- A good subgroup is compact, being closed in its double annihilator. -/
private theorem isCompact_of_isBruhatGoodSubgroup_aux (k : Subgroup G) (hk : IsBruhatGoodSubgroup k) :
    IsCompact (k : Set G) := by
  have hCompact := isCompact_lcaAnnihilator (lcaAnnihilator k) hk.2.1
  have hD : IsCompact (lcaDualAnnihilator (lcaAnnihilator k) : Set G) := by
    convert (isClosedEmbedding_pontryaginDual_eval (G := G)).isCompact_preimage hCompact using 1
    ext x
    exact (mem_lcaDualAnnihilator_iff _ x).trans
      (mem_lcaAnnihilator_iff _ (pontryaginDual_eval x)).symm
  refine hD.of_isClosed_subset hk.1 fun x hx ↦ ?_
  rw [SetLike.mem_coe, mem_lcaDualAnnihilator_iff]
  intro χ
  exact (mem_lcaAnnihilator_iff k χ.val).mp χ.2 ⟨x, hx⟩

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
/-- The modulation is trivial on each compact subgroup. -/
private theorem compactSubgroup_le_ker_aux (k : Subgroup G) (hk : IsCompact (k : Set G)) :
    k ≤ m.toMonoidHom.ker := by
  obtain ⟨y, hy, hmax⟩ := hk.exists_isMaxOn ⟨1, k.one_mem⟩
    (Units.continuous_val.comp m.continuous).continuousOn
  have bound (x : G) (hx : x ∈ k) : (m x).val ≤ 1 := by
    apply (mul_le_iff_le_one_right (Units.zero_lt (m y))).mp
    have h : (m (y * x)).val ≤ (m y).val := hmax (k.mul_mem hy hx)
    simpa only [map_mul, Units.val_mul] using h
  intro x hx
  apply Units.ext
  exact le_antisymm (bound x hx) (by simpa using bound x⁻¹ (k.inv_mem hx))

/-- Multiplying a stage realization by a function of `log m` with bounded derivatives
is again the realization of a stage function on the same structural pair. -/
private theorem stage_mul_logModulation (a : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation a.quotient) (s : SchwartzBruhatStage e)
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ) (hφb : ∀ k, ∃ C, ∀ t, ‖iteratedFDeriv ℝ k φ t‖ ≤ C) :
    ∃ s' : SchwartzBruhatStage e, schwartzBruhatStageRealization a e s' =
      fun g ↦ φ (Real.log ((m g : ℝ≥0) : ℝ)) * schwartzBruhatStageRealization a e s g := by
  classical
  let N := (OrderDual.ofDual a.val.2).comap a.val.1.subtype
  have hN : N ≤ (m.toMonoidHom.comp a.val.1.subtype).ker := by
    intro x hx
    have := compactSubgroup_le_ker_aux m _ (isCompact_of_isBruhatGoodSubgroup_aux _ a.property.2.2.1) hx
    simpa using this
  let mbar : a.quotient →* ℝ≥0ˣ := QuotientGroup.lift N (m.toMonoidHom.comp a.val.1.subtype) hN
  have hmbar : Continuous mbar :=
    continuous_coinduced_dom.2 (m.continuous.comp continuous_subtype_val)
  let Λ : ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor → ℝ :=
    fun y ↦ Real.log ((mbar (e.equiv.symm (Multiplicative.ofAdd y)) : ℝ≥0) : ℝ)
  have hΛpos (y) : ((mbar (e.equiv.symm (Multiplicative.ofAdd y)) : ℝ≥0) : ℝ) ≠ 0 := by
    have := Units.ne_zero (mbar (e.equiv.symm (Multiplicative.ofAdd y)))
    exact_mod_cast this
  have hΛadd (y z) : Λ (y + z) = Λ y + Λ z := by
    simp only [Λ]
    rw [← Real.log_mul (hΛpos y) (hΛpos z)]
    congr 1
    rw [ofAdd_add, map_mul, map_mul, Units.val_mul, NNReal.coe_mul]
  have hΛcont : Continuous Λ := by
    refine Continuous.log ?_ hΛpos
    exact NNReal.continuous_coe.comp (Units.continuous_val.comp (hmbar.comp
      (e.equiv.symm.continuous.comp continuous_ofAdd)))
  have hcover_add (xt : EuclideanSpace ℝ (Fin e.realDim) × EuclideanSpace ℝ (Fin e.torusDim)) (u : Fin e.latticeRank → ℤ) (b : e.finiteFactor) :
      (elementaryCover xt u b : ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor) =
        elementaryCover xt 0 0 + elementaryCover 0 u b := by
    simp only [elementaryCover]
    refine Prod.ext (by simp) (Prod.ext (funext fun i ↦ by simp) (Prod.ext (by simp) (by simp)))
  have hcover_add' (xt xt' : EuclideanSpace ℝ (Fin e.realDim) × EuclideanSpace ℝ (Fin e.torusDim)) :
      (elementaryCover (xt + xt') 0 0 :
        ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor) =
        elementaryCover xt 0 0 + elementaryCover xt' 0 0 := by
    simp only [elementaryCover]
    exact Prod.ext rfl (Prod.ext (funext fun i ↦ rfl) (Prod.ext (by simp) (by simp)))
  have hcover_zero : (elementaryCover (0 : EuclideanSpace ℝ (Fin e.realDim) × EuclideanSpace ℝ (Fin e.torusDim)) 0 0 :
      ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor) = 0 := by
    simp only [elementaryCover]
    refine Prod.ext (by simp) (Prod.ext (funext fun i ↦ by simp) (Prod.ext (by simp) (by simp)))
  have hcover_cont : Continuous (fun xt : EuclideanSpace ℝ (Fin e.realDim) × EuclideanSpace ℝ (Fin e.torusDim) ↦ (elementaryCover xt 0 0 :
      ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor)) := by
    unfold elementaryCover
    fun_prop
  have hΛ0 : Λ 0 = 0 := by
    have := hΛadd 0 0
    simp only [add_zero] at this
    linarith
  let ℓ₀ : EuclideanSpace ℝ (Fin e.realDim) × EuclideanSpace ℝ (Fin e.torusDim) →+ ℝ :=
    { toFun := fun xt ↦ Λ (elementaryCover xt 0 0)
      map_zero' := by simp only [hcover_zero, hΛ0]
      map_add' := fun xt xt' ↦ by simp only [hcover_add', hΛadd] }
  let ℓ : EuclideanSpace ℝ (Fin e.realDim) × EuclideanSpace ℝ (Fin e.torusDim) →L[ℝ] ℝ := ℓ₀.toRealLinearMap (hΛcont.comp hcover_cont)
  have hΛ (xt : EuclideanSpace ℝ (Fin e.realDim) × EuclideanSpace ℝ (Fin e.torusDim)) (u : Fin e.latticeRank → ℤ) (b : e.finiteFactor) :
      Λ (elementaryCover xt u b) = ℓ xt + Λ (elementaryCover 0 u b) := by
    rw [hcover_add, hΛadd]
    rfl
  have hs' := elementarySchwartz_mul_affine_mem
    (show elementarySchwartzSubmodule _ _ _ _ from s).property Λ ℓ hΛ hφ hφb
  refine ⟨(show SchwartzBruhatStage e from (⟨_, hs'⟩ : elementarySchwartzSubmodule _ _ _ _)), ?_⟩
  funext g
  rw [schwartzBruhatStageRealization_apply, schwartzBruhatStageRealization_apply]
  split_ifs with hg
  · change φ (Λ _) * _ = _
    congr 2
    simp only [Λ, ofAdd_toAdd, ContinuousMulEquiv.symm_apply_apply]
    rfl
  · simp

/-- Schwartz–Bruhat functions are stable under multiplication by `φ (log m)` when `φ`
is smooth with bounded derivatives of all orders. -/
private theorem logModulation_mul_mem_schwartzBruhat {φ : ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (hφb : ∀ k, ∃ C, ∀ t, ‖iteratedFDeriv ℝ k φ t‖ ≤ C) {F : G → ℂ}
    (hF : F ∈ schwartzBruhatSubmodule G) :
    (fun g ↦ φ (Real.log ((m g : ℝ≥0) : ℝ)) * F g) ∈ schwartzBruhatSubmodule G := by
  let M : (G → ℂ) →ₗ[ℂ] (G → ℂ) :=
    LinearMap.mulLeft ℂ (fun g ↦ φ (Real.log ((m g : ℝ≥0) : ℝ)))
  have hle : schwartzBruhatSubmodule G ≤ (schwartzBruhatSubmodule G).comap M := by
    refine iSup_le fun a ↦ iSup_le fun e ↦ ?_
    rintro _ ⟨s, rfl⟩
    obtain ⟨s', hs'⟩ := stage_mul_logModulation m a e s hφ hφb
    rw [Submodule.mem_comap]
    have : M (schwartzBruhatStageRealization a e s) = schwartzBruhatStageRealization a e s' := by
      rw [hs']
      rfl
    rw [this]
    exact Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem e ⟨s', rfl⟩)
  exact hle hF

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
/-- An intermediate twist is the sum of the endpoint twists times a function of `log m`. -/
private theorem modulationWeight_between_eq (f : G → ℂ) (a c b : ℝ) :
    modulationWeight m c f = fun g ↦
      (((Real.exp (-(c - a) * Real.log ((m g).val : ℝ)) +
        Real.exp ((b - c) * Real.log ((m g).val : ℝ)))⁻¹ : ℝ) : ℂ) *
        (modulationWeight m a f + modulationWeight m b f) g := by
  funext g
  simp only [modulationWeight, LinearMap.mulLeft_apply, Pi.add_apply, Pi.mul_apply]
  have hr : 0 < ((m g : ℝ≥0) : ℝ) := by
    have := Units.ne_zero (m g)
    positivity
  set r : ℝ := ((m g : ℝ≥0) : ℝ)
  have key : r ^ c = (Real.exp (-(c - a) * Real.log r) + Real.exp ((b - c) * Real.log r))⁻¹ *
      (r ^ a + r ^ b) := by
    rw [Real.rpow_def_of_pos hr, Real.rpow_def_of_pos hr, Real.rpow_def_of_pos hr,
      eq_inv_mul_iff_mul_eq₀ (by positivity), add_mul, ← Real.exp_add, ← Real.exp_add]
    congr 2 <;> ring
  rw [key]
  push_cast
  ring

/-- Paper: Lemma D.3.3.2, p. 804. If two exponent twists are Schwartz–Bruhat,
every intermediate exponent twist is Schwartz–Bruhat as well. -/
theorem modulationWeight_mem_schwartzBruhat_between (hm : IsModulation m) (hms : Surjective m)
    (f : G → ℂ) (a c b : ℝ) (hac : a < c) (hcb : c < b)
    (ha : modulationWeight m a f ∈ schwartzBruhatSubmodule G)
    (hb : modulationWeight m b f ∈ schwartzBruhatSubmodule G) :
    modulationWeight m c f ∈ schwartzBruhatSubmodule G := by
  obtain ⟨hφ, hφb⟩ := twoSidedExpWeight_bounds (sub_pos.mpr hac) (sub_pos.mpr hcb)
  rw [modulationWeight_between_eq m f a c b]
  exact logModulation_mul_mem_schwartzBruhat m hφ hφb (add_mem ha hb)

-- TODO(paper-gap): The finite-generation wording in Definition D.3.3.3
-- refers to the annihilator in the dual of the norm-one subgroup. In
-- the full dual the opening compact-generation condition applies.
local notation "GoodCompact" => {k : Subgroup G // IsCompact (k : Set G) ∧
  IsCompactlyGeneratedGroup (lcaAnnihilator k)}

/-- Paper: Definition D.3.3.3, p. 805. The modulation is trivial on each
compact subgroup because the positive-real group has no nontrivial compact subgroup. -/
theorem compactSubgroup_le_modulation_ker (k : Subgroup G) (hk : IsCompact (k : Set G)) :
    k ≤ m.toMonoidHom.ker := by
  obtain ⟨y, hy, hmax⟩ := hk.exists_isMaxOn ⟨1, k.one_mem⟩
    (Units.continuous_val.comp m.continuous).continuousOn
  have bound (x : G) (hx : x ∈ k) : (m x).val ≤ 1 := by
    apply (mul_le_iff_le_one_right (Units.zero_lt (m y))).mp
    have h : (m (y * x)).val ≤ (m y).val := hmax (k.mul_mem hy hx)
    simpa only [map_mul, Units.val_mul] using h
  intro x hx
  apply Units.ext
  exact le_antisymm (bound x hx) (by simpa using bound x⁻¹ (k.inv_mem hx))

/-- Paper: Definition D.3.3.3, p. 805. The homomorphism induced by the
modulation on a compact-subgroup quotient is continuous. -/
theorem continuous_quotientModulation (k : Subgroup G) (hk : IsCompact (k : Set G)) :
    Continuous (QuotientGroup.lift k m.toMonoidHom (compactSubgroup_le_modulation_ker m k hk)) :=
  continuous_coinduced_dom.2 m.continuous

/-- Paper: Definition D.3.3.3, p. 805. Use the descended modulation to form
the projective system on the quotient by a compact subgroup. -/
def quotientModulation (k : Subgroup G) (hk : IsCompact (k : Set G)) : (G ⧸ k) →ₜ* ℝ≥0ˣ where
  toMonoidHom := QuotientGroup.lift k m.toMonoidHom (compactSubgroup_le_modulation_ker m k hk)
  continuous_toFun := continuous_quotientModulation m k hk

/-- Paper: Definition D.3.3.3, p. 805. The descended modulation agrees with
the original one on each coset representative. -/
theorem quotientModulation_apply (k : Subgroup G) (hk : IsCompact (k : Set G)) (g : G) :
    quotientModulation m k hk (g : G ⧸ k) = m g := rfl

/-- Paper: Definition D.3.3.3, p. 805. The stage S_I(k,G) carries the topology
induced by the Schwartz–Bruhat twists on G/k.
Deviation: The k-invariant functions are represented on the quotient.

This is a `def` with its own instances, not an `abbrev`, so that instance terms over it do
not spell out its seminorm family (#5398). -/
def ModulatedExponentialDecayStage (k : GoodCompact) :=
  WithGeneratingSeminorms
    (modulatedExponentialDecaySubmodule (quotientModulation m k.val k.property.1) I)
    (fun i : I × {p : Seminorm ℂ (SchwartzBruhat (G ⧸ k.val)) // Continuous p} ↦
      i.2.val.comp
        (modulatedExponentialDecayTwist (quotientModulation m k.val k.property.1) I i.1))

namespace ModulatedExponentialDecayStage

instance instAddCommGroup (k : GoodCompact) :
    AddCommGroup (ModulatedExponentialDecayStage m I k) :=
  inferInstanceAs (AddCommGroup (WithGeneratingSeminorms
    (modulatedExponentialDecaySubmodule (quotientModulation m k.val k.property.1) I) _))

instance instModule (k : GoodCompact) :
    Module ℂ (ModulatedExponentialDecayStage m I k) :=
  inferInstanceAs (Module ℂ (WithGeneratingSeminorms
    (modulatedExponentialDecaySubmodule (quotientModulation m k.val k.property.1) I) _))

instance instTopologicalSpace (k : GoodCompact) :
    TopologicalSpace (ModulatedExponentialDecayStage m I k) :=
  inferInstanceAs (TopologicalSpace (WithGeneratingSeminorms
    (modulatedExponentialDecaySubmodule (quotientModulation m k.val k.property.1) I) _))

instance instPolynormableSpace (k : GoodCompact) :
    PolynormableSpace ℂ (ModulatedExponentialDecayStage m I k) :=
  inferInstanceAs (PolynormableSpace ℂ (WithGeneratingSeminorms
    (modulatedExponentialDecaySubmodule (quotientModulation m k.val k.property.1) I) _))

instance instIsTopologicalAddGroup (k : GoodCompact) :
    IsTopologicalAddGroup (ModulatedExponentialDecayStage m I k) :=
  inferInstanceAs (IsTopologicalAddGroup (WithGeneratingSeminorms
    (modulatedExponentialDecaySubmodule (quotientModulation m k.val k.property.1) I) _))

instance instUniformSpace (k : GoodCompact) :
    UniformSpace (ModulatedExponentialDecayStage m I k) :=
  inferInstanceAs (UniformSpace (WithGeneratingSeminorms
    (modulatedExponentialDecaySubmodule (quotientModulation m k.val k.property.1) I) _))

instance instIsUniformAddGroup (k : GoodCompact) :
    IsUniformAddGroup (ModulatedExponentialDecayStage m I k) :=
  inferInstanceAs (IsUniformAddGroup (WithGeneratingSeminorms
    (modulatedExponentialDecaySubmodule (quotientModulation m k.val k.property.1) I) _))

/-- The topology of a stage is generated by the Schwartz–Bruhat seminorms of its twists. -/
theorem withSeminorms (k : GoodCompact) :
    WithSeminorms (E := ModulatedExponentialDecayStage m I k)
      (fun i : I × {p : Seminorm ℂ (SchwartzBruhat (G ⧸ k.val)) // Continuous p} ↦
        (i.2.val.comp (modulatedExponentialDecayTwist
          (quotientModulation m k.val k.property.1) I i.1) :
            Seminorm ℂ (ModulatedExponentialDecayStage m I k))) :=
  withGeneratingSeminorms_spec _ _

end ModulatedExponentialDecayStage

/-- The inverse image of a good subgroup of a compact quotient is good. -/
private theorem isBruhatGoodSubgroup_comap_compactQuotient (k : Subgroup G)
    (hk : IsCompact (k : Set G)) (J : Subgroup (G ⧸ k)) (hJ : IsBruhatGoodSubgroup J) :
    IsBruhatGoodSubgroup (J.comap (QuotientGroup.mk' k)) := by
  let q := QuotientGroup.mk' k
  let L := J.comap q
  let : IsClosed (k : Set G) := hk.isClosed
  obtain ⟨e, he⟩ := lcaQuotientDual_equiv_annihilator k hk.isClosed
  have hkL : k ≤ L := fun x hx ↦ by
    change (x : G ⧸ k) ∈ J
    rw [(QuotientGroup.eq_one_iff x).2 hx]
    exact J.one_mem
  have hAnn : lcaAnnihilator L ≤ lcaAnnihilator k := fun χ hχ ↦
    (mem_lcaAnnihilator_iff k χ).mpr fun x ↦
      (mem_lcaAnnihilator_iff L χ).mp hχ ⟨x, hkL x.property⟩
  let A := (lcaAnnihilator L).subgroupOf (lcaAnnihilator k)
  have hA : A.comap e.toMulEquiv.toMonoidHom = lcaAnnihilator J := by
    ext χ
    change (e χ).val ∈ lcaAnnihilator L ↔ χ ∈ lcaAnnihilator J
    rw [mem_lcaAnnihilator_iff, mem_lcaAnnihilator_iff]
    simp_rw [he]
    constructor
    · intro h x
      obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective x.val
      simpa only [hy] using h ⟨y, show (y : G ⧸ k) ∈ J from hy.symm ▸ x.property⟩
    · exact fun h x ↦ h ⟨q x, x.property⟩
  have hOpenA : IsOpen (A : Set (lcaAnnihilator k)) := by
    apply e.toHomeomorph.isOpen_preimage.mp
    change IsOpen ((A.comap e.toMulEquiv.toMonoidHom : Subgroup _) : Set (PontryaginDual (G ⧸ k)))
    rw [hA]
    exact hJ.2.1
  refine ⟨hJ.1.preimage QuotientGroup.continuous_mk, ?_, ?_⟩
  · have hImage : Subtype.val '' (A : Set (lcaAnnihilator k)) = (lcaAnnihilator L : Set _) := by
      ext χ
      exact ⟨fun ⟨x, hx, hEq⟩ ↦ hEq ▸ hx, fun h ↦ ⟨⟨χ, hAnn h⟩, h, rfl⟩⟩
    rw [← hImage]
    exact (isOpen_lcaAnnihilator k hk).isOpenEmbedding_subtypeVal.isOpenMap _ hOpenA
  · let B := A.comap e.toMulEquiv.toMonoidHom
    let d : B →* A := (e.toMulEquiv.toMonoidHom.comp B.subtype).codRestrict A (·.property)
    have hd : IsOpenQuotientMap d :=
      e.toHomeomorph.isOpenQuotientMap.restrictPreimage (A : Set (lcaAnnihilator k))
    let D := (MulEquiv.ofBijective d
      ⟨fun x y h ↦ Subtype.ext (e.injective (congrArg Subtype.val h)), hd.surjective⟩
      ).toContinuousMulEquiv (fun _ ↦ hd.isQuotientMap.isOpen_preimage)
    have hGenB : IsCompactlyGeneratedGroup B := by
      change IsCompactlyGeneratedGroup (A.comap e.toMulEquiv.toMonoidHom)
      rw [hA]
      exact hJ.2.2
    exact isCompactlyGeneratedGroup_of_continuousMulEquiv
      (D.trans (Subgroup.subgroupOfContinuousMulEquivOfLe hAnn)) hGenB

/-- Pulling back a structural pair across a compact quotient preserves its elementary quotient. -/
private theorem bruhatStructuralPair_lift_compactQuotient (k : Subgroup G)
    (hk : IsCompact (k : Set G)) (a : BruhatStructuralPair (G ⧸ k)) :
    ∃ (b : BruhatStructuralPair G) (v : b.quotient ≃ₜ* a.quotient)
      (hb : ∀ g : G, g ∈ b.val.1 ↔ (g : G ⧸ k) ∈ a.val.1),
      ∀ (g : G) (hg : g ∈ b.val.1),
        v (QuotientGroup.mk ⟨g, hg⟩) = QuotientGroup.mk ⟨(g : G ⧸ k), (hb g).mp hg⟩ := by
  let q := QuotientGroup.mk' k
  let H := a.val.1.comap q
  let J := OrderDual.ofDual a.val.2
  let L := J.comap q
  have hq : IsOpenQuotientMap q := QuotientGroup.isOpenQuotientMap_mk
  have hqProper : IsProperMap q := by
    refine isProperMap_iff_isClosedMap_and_compact_fibers.mpr
      ⟨hq.continuous, QuotientGroup.isClosedMap_coe hk, ?_⟩
    intro y
    obtain ⟨x, rfl⟩ := hq.surjective y
    change IsCompact (QuotientGroup.mk ⁻¹' {QuotientGroup.mk x} : Set G)
    rw [← Set.image_singleton, QuotientGroup.preimage_image_mk_eq_mul, Set.singleton_mul]
    exact hk.image (continuous_const.mul continuous_id)
  let p : H →* a.val.1 := (q.comp H.subtype).codRestrict a.val.1 (·.property)
  have hp : IsOpenQuotientMap p := hq.restrictPreimage (a.val.1 : Set (G ⧸ k))
  have hpProper : IsProperMap p := hqProper.restrictPreimage (a.val.1 : Set (G ⧸ k))
  have hGen : IsCompactlyGeneratedGroup H := by
    obtain ⟨U, hU, hUc, hUgen⟩ := a.property.2.1
    refine ⟨p ⁻¹' U, hp.continuous.continuousAt.preimage_mem_nhds (by simpa only [map_one]),
      hpProper.isCompact_preimage hUc, eq_top_iff.mpr ?_⟩
    let C := Subgroup.closure (p ⁻¹' U)
    have hImage : C.map p = ⊤ := by
      rw [MonoidHom.map_closure, Set.image_preimage_eq _ hp.surjective, hUgen]
    intro x _
    obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp (hImage ▸ Subgroup.mem_top (p x))
    have hker : y⁻¹ * x ∈ C := by
      apply Subgroup.subset_closure
      change p (y⁻¹ * x) ∈ U
      rw [map_mul, map_inv, hxy, inv_mul_cancel]
      exact mem_of_mem_nhds hU
    simpa only [mul_inv_cancel_left] using C.mul_mem hy hker
  let b : BruhatStructuralPair G := ⟨(H, OrderDual.toDual L),
    a.property.1.preimage hq.continuous, hGen,
    isBruhatGoodSubgroup_comap_compactQuotient k hk J a.property.2.2.1,
    Subgroup.comap_mono a.property.2.2.2⟩
  let r : H →* a.quotient := (QuotientGroup.mk' _).comp p
  have hr : IsOpenQuotientMap r := QuotientGroup.isOpenQuotientMap_mk.comp hp
  have hKer : L.comap H.subtype = r.ker := by
    ext x
    exact (a.quotient_mk_eq_one (p x)).symm
  let w : b.quotient ≃* a.quotient :=
    (QuotientGroup.quotientMulEquivOfEq hKer).trans
      (QuotientGroup.quotientKerEquivOfSurjective r hr.surjective)
  have hw (x : H) : w (QuotientGroup.mk x) = r x := rfl
  let v := w.toContinuousMulEquiv fun s ↦ by
    change IsOpen (w ⁻¹' s : Set (H ⧸ L.comap H.subtype)) ↔ IsOpen s
    rw [← (QuotientGroup.isQuotientMap_mk (L.comap H.subtype)).isOpen_preimage]
    exact hr.isQuotientMap.isOpen_preimage
  exact ⟨b, v, fun _ ↦ Iff.rfl, fun g hg ↦ hw ⟨g, hg⟩⟩

/-- Pullback by the quotient map of a compact subgroup preserves Schwartz–Bruhat membership. -/
private theorem schwartzBruhatSubmodule_compactQuotient_pullback_mem (k : Subgroup G)
    (hk : IsCompact (k : Set G)) {f : (G ⧸ k) → ℂ} (hf : f ∈ schwartzBruhatSubmodule (G ⧸ k)) :
    (fun g : G ↦ f (g : G ⧸ k)) ∈ schwartzBruhatSubmodule G := by
  let P : ((G ⧸ k) → ℂ) →ₗ[ℂ] (G → ℂ) :=
    LinearMap.pi fun g : G ↦ LinearMap.proj (g : G ⧸ k)
  change P f ∈ schwartzBruhatSubmodule G
  suffices hP : (schwartzBruhatSubmodule (G ⧸ k)).map P ≤ schwartzBruhatSubmodule G by
    exact hP (Submodule.mem_map_of_mem hf)
  unfold schwartzBruhatSubmodule
  simp only [Submodule.map_iSup]
  refine iSup_le fun a ↦ iSup_le fun e ↦ ?_
  rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
  obtain ⟨b, v, hb, hv⟩ := bruhatStructuralPair_lift_compactQuotient k hk a
  let e' : ElementaryLCAPresentation b.quotient := { e with equiv := v.trans e.equiv }
  refine Submodule.mem_iSup_of_mem b (Submodule.mem_iSup_of_mem e' ⟨s, ?_⟩)
  funext g
  change schwartzBruhatStageRealization b e' s g =
    schwartzBruhatStageRealization a e s (g : G ⧸ k)
  by_cases hg : g ∈ b.val.1
  · have hqg := (hb g).mp hg
    calc
      _ = s (e'.equiv (QuotientGroup.mk ⟨g, hg⟩)).toAdd :=
        (schwartzBruhatStageRealization_apply b e' s g).trans (dite_eq_left hg)
      _ = s (e.equiv (QuotientGroup.mk ⟨(g : G ⧸ k), hqg⟩)).toAdd :=
        congrArg (fun x : a.quotient ↦ s (e.equiv x).toAdd) (hv g hg)
      _ = _ := ((schwartzBruhatStageRealization_apply a e s (g : G ⧸ k)).trans
        (dite_eq_left hqg)).symm
  · have hqg := mt (hb g).mpr hg
    exact ((schwartzBruhatStageRealization_apply b e' s g).trans (dite_eq_right hg)).trans
      (((schwartzBruhatStageRealization_apply a e s (g : G ⧸ k)).trans
        (dite_eq_right hqg)).symm)

/-- Paper: Definition D.3.3.3, p. 805. Pulling a stage profile back along
the quotient map lands in the ambient decay submodule. -/
theorem modulatedExponentialDecayStage_pullback_mem (k : GoodCompact)
    (f : ModulatedExponentialDecayStage m I k) :
    (fun g : G ↦ f.val (g : G ⧸ k.val)) ∈ modulatedExponentialDecaySubmodule m I := by
  refine (Submodule.mem_iInf _).mpr fun a ↦ Submodule.mem_comap.mpr ?_
  exact schwartzBruhatSubmodule_compactQuotient_pullback_mem k.val k.property.1
    (modulationWeight_mem_schwartzBruhat (quotientModulation m k.val k.property.1) I a f)

/-- Paper: (D.3.3.1), p. 805. The canonical stage map is pullback from G/k. -/
def modulatedExponentialDecayStageInclusion (k : GoodCompact) :
    ModulatedExponentialDecayStage m I k →ₗ[ℂ] modulatedExponentialDecaySubmodule m I :=
  ((LinearMap.pi fun g : G ↦ LinearMap.proj (g : G ⧸ k.val)).comp
    (modulatedExponentialDecaySubmodule (quotientModulation m k.val k.property.1) I).subtype
  ).codRestrict (modulatedExponentialDecaySubmodule m I)
    (modulatedExponentialDecayStage_pullback_mem m I k)

/-- Paper: (D.3.3.1), p. 805. A stage maps bijectively onto the k-invariant
functions in the ambient decay submodule. -/
theorem modulatedExponentialDecayStageInclusion_range (k : GoodCompact) :
    Injective (modulatedExponentialDecayStageInclusion m I k) ∧
      ∀ f : modulatedExponentialDecaySubmodule m I,
        f ∈ (modulatedExponentialDecayStageInclusion m I k).range ↔
          ∀ (g : G) (u : k.val), f.val (g * u.val) = f.val g := by
  constructor
  · intro f f' h
    apply Subtype.ext
    funext q
    exact QuotientGroup.induction_on q fun g ↦
      congrArg (fun F : modulatedExponentialDecaySubmodule m I ↦ F.val g) h
  intro f
  constructor
  · rintro ⟨F, rfl⟩ g u
    exact congrArg F.val (QuotientGroup.mk_mul_of_mem g u.property)
  · intro hf
    let fbar : (G ⧸ k.val) → ℂ := fun q ↦ f.val q.out
    have hbar (g : G) : fbar (g : G ⧸ k.val) = f.val g := by
      obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul k.val g
      exact (congrArg f.val hu).trans (hf g u)
    refine ⟨⟨fbar, ?_⟩, Subtype.ext (funext hbar)⟩
    let : MeasurableSpace G := borel G
    let : BorelSpace G := ⟨rfl⟩
    let : CompactSpace k.val := isCompact_iff_compactSpace.mp k.property.1
    let μ : Measure k.val := Measure.haarMeasure ⊤
    let : IsProbabilityMeasure μ := ⟨Measure.haarMeasure_self⟩
    refine (Submodule.mem_iInf _).2 fun a ↦ Submodule.mem_comap.2 ?_
    let F := modulatedExponentialDecayTwist m I a f
    let W := modulationWeight (quotientModulation m k.val k.property.1) a fbar
    change W ∈ schwartzBruhatSubmodule (G ⧸ k.val)
    have hW (g : G) : W (g : G ⧸ k.val) = F g := by
      exact congrArg (fun z : ℂ ↦ ((((m g).val : ℝ) ^ (a : ℝ) : ℝ) : ℂ) * z) (hbar g)
    have haverage : W = lcaCosetIntegral k.val μ F := by
      funext q
      have hconst (u : k.val) : F (q.out * u.val) = W q :=
        (hW (q.out * u.val)).symm.trans
          (congrArg W ((QuotientGroup.mk_mul_of_mem q.out u.property).trans (Quotient.out_eq' q)))
      rw [lcaCosetIntegral, funext hconst, integral_const, probReal_univ, one_smul]
    rw [haverage]
    exact (lcaCosetIntegral_mem_schwartzBruhat k.val μ k.property.1.isClosed F).2

/-- Paper: Definition D.3.3.3, p. 805. The topology of S_I(G) is the final
locally convex topology for the inclusions of the compact-subgroup stages.

This is a `def` with its own instances, not an `abbrev`, so that instance terms over it do
not spell out its seminorm family (#5398). -/
def ModulatedExponentialDecay :=
  WithGeneratingSeminorms (modulatedExponentialDecaySubmodule m I)
    (Subtype.val : {p : Seminorm ℂ (modulatedExponentialDecaySubmodule m I) //
      ∀ k : GoodCompact, Continuous (p ∘ modulatedExponentialDecayStageInclusion m I k)} → _)

namespace ModulatedExponentialDecay

instance instAddCommGroup : AddCommGroup (ModulatedExponentialDecay m I) :=
  inferInstanceAs (AddCommGroup (WithGeneratingSeminorms
    (modulatedExponentialDecaySubmodule m I) _))

instance instModule : Module ℂ (ModulatedExponentialDecay m I) :=
  inferInstanceAs (Module ℂ (WithGeneratingSeminorms
    (modulatedExponentialDecaySubmodule m I) _))

instance instTopologicalSpace : TopologicalSpace (ModulatedExponentialDecay m I) :=
  inferInstanceAs (TopologicalSpace (WithGeneratingSeminorms
    (modulatedExponentialDecaySubmodule m I) _))

instance instPolynormableSpace : PolynormableSpace ℂ (ModulatedExponentialDecay m I) :=
  inferInstanceAs (PolynormableSpace ℂ (WithGeneratingSeminorms
    (modulatedExponentialDecaySubmodule m I) _))

instance instIsTopologicalAddGroup : IsTopologicalAddGroup (ModulatedExponentialDecay m I) :=
  inferInstanceAs (IsTopologicalAddGroup (WithGeneratingSeminorms
    (modulatedExponentialDecaySubmodule m I) _))

instance instUniformSpace : UniformSpace (ModulatedExponentialDecay m I) :=
  inferInstanceAs (UniformSpace (WithGeneratingSeminorms
    (modulatedExponentialDecaySubmodule m I) _))

instance instIsUniformAddGroup : IsUniformAddGroup (ModulatedExponentialDecay m I) :=
  inferInstanceAs (IsUniformAddGroup (WithGeneratingSeminorms
    (modulatedExponentialDecaySubmodule m I) _))

end ModulatedExponentialDecay

-- Retain the modulation and interval hypotheses in the existing signature.
set_option linter.unusedVariables false in
/-- Paper: Definition D.3.3.3, p. 805. The stage inclusions exhaust the
underlying space. -/
theorem modulatedExponentialDecay_exists_stage (hm : IsModulation m) (hms : Surjective m)
    (hInt : OrdConnected I) (hne : I.Nonempty) :
    ∀ f : ModulatedExponentialDecay m I, ∃ k : GoodCompact,
      f ∈ (modulatedExponentialDecayStageInclusion m I k).range := by
  intro f
  obtain ⟨a, ha⟩ := hne
  let F : G → ℂ := modulationWeight m a f.val
  have hmem : F ∈ schwartzBruhatSubmodule G :=
    modulationWeight_mem_schwartzBruhat m I ⟨a, ha⟩ f
  have hstage : ∃ (p : BruhatStructuralPair G) (e : ElementaryLCAPresentation p.quotient)
      (s : SchwartzBruhatStage e), schwartzBruhatStageRealization p e s = F :=
    (mem_schwartzBruhatSubmodule_iff F).mp hmem
  rcases hstage with ⟨p, e, s, hs⟩
  let k := OrderDual.ofDual p.val.2
  have hInv (g u : G) (hu : u ∈ k) : F (g * u) = F g := by
    have hu' : u ∈ p.val.1 := p.property.2.2.2 hu
    rw [← hs, schwartzBruhatStageRealization_apply, schwartzBruhatStageRealization_apply]
    by_cases hg : g ∈ p.val.1
    · rw [dite_eq_left (p.val.1.mul_mem hg hu'), dite_eq_left hg]
      let v : p.val.1 := ⟨u, hu'⟩
      have hv : v ∈ k.comap p.val.1.subtype := hu
      have hq : (QuotientGroup.mk ((⟨g, hg⟩ : p.val.1) * v) : p.quotient) =
          QuotientGroup.mk ⟨g, hg⟩ := QuotientGroup.mk_mul_of_mem _ hv
      exact congrArg (fun x : p.quotient ↦ s (e.equiv x).toAdd) hq
    · rw [dite_eq_right (fun h ↦ hg ((p.val.1.mul_mem_cancel_right hu').mp h)), dite_eq_right hg]
  have hk : IsCompact (k : Set G) := isCompact_of_isBruhatGoodSubgroup_aux k p.property.2.2.1
  let K : GoodCompact := ⟨k, hk, p.property.2.2.1.2.2⟩
  refine ⟨K, ((modulatedExponentialDecayStageInclusion_range m I K).2 f).mpr ?_⟩
  intro g u
  -- The twist has the same nonzero weight at both points.
  have hmu : m u.val = 1 := compactSubgroup_le_modulation_ker m k hk u.property
  have hF := hInv g u.val u.property
  change (((m (g * u.val)).val : ℝ) ^ a : ℝ) * f.val (g * u.val) =
    (((m g).val : ℝ) ^ a : ℝ) * f.val g at hF
  rw [map_mul, hmu, mul_one] at hF
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr
    (Real.rpow_pos_of_pos (NNReal.coe_pos.mpr (Units.zero_lt (m g))) a).ne') hF

end Modulated

section IdentityModulation

open scoped BoundedContinuousFunction

/-- The elementary Schwartz space with one real factor and trivial remaining
factors is the usual Schwartz space on that real factor. -/
private theorem elementarySchwartz_line_equiv :
    ∃ e : 𝓢(EuclideanSpace ℝ (Fin 1), ℂ) ≃L[ℂ] ElementarySchwartz 1 0 0 PUnit,
      ∀ f x, e f x = f x.1 := by
  let E := EuclideanSpace ℝ (Fin 1)
  let X := 𝓢(E, ℂ)
  let Y := ElementarySchwartz 1 0 0 PUnit
  let L : X →ₗ[ℂ] Y :=
    { toFun := fun f ↦ ⟨fun x ↦ f x.1, (elementarySchwartzSubmodule_real_iff _).mpr ⟨f, rfl⟩⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hL (f : X) (x : ElementaryLieGroup 1 0 0 PUnit) : L f x = f x.1 := rfl
  have hbij : Bijective L := by
    constructor
    · intro f g h
      ext x
      exact congrArg (fun s : Y ↦ s (x, 0, 0, 0)) h
    · intro g
      let f (x : E) := g (x, 0, 0, 0)
      have heq : (fun x : ElementaryLieGroup 1 0 0 PUnit ↦ f x.1) = g.val := by
        funext x
        exact congrArg g (Prod.ext rfl (Subsingleton.elim _ _))
      have hmem := (elementarySchwartzSubmodule_real_iff f).mp (heq ▸ g.property)
      obtain ⟨s, hs⟩ := hmem
      refine ⟨s, Subtype.ext ?_⟩
      change (fun x : ElementaryLieGroup 1 0 0 PUnit ↦ s x.1) = g.val
      rw [← heq]
      exact congrArg (fun u : E → ℂ ↦ fun x : ElementaryLieGroup 1 0 0 PUnit ↦ u x.1) hs
  have hX : IsFrechetTVS X := euclideanSchwartz_frechet 1
  have : BarrelledSpace ℂ X := isFrechetTVS_barrelled hX
  have hc : Continuous L := by
    apply continuous_toElementarySchwartz_of_eval
    intro g
    exact ⟨(BoundedContinuousFunction.evalCLM ℂ g.1).comp (SchwartzMap.toBoundedContinuousFunctionCLM ℂ E ℂ),
      fun _ ↦ rfl⟩
  obtain ⟨hTX, -, hMX, hCX⟩ := hX
  obtain ⟨hTY, -, hMY, hCY⟩ := elementarySchwartz_isFrechet (m := 1) (n := 0) (r := 0) (F := PUnit)
  let : UniformSpace X := IsTopologicalAddGroup.rightUniformSpace X
  let : UniformSpace Y := IsTopologicalAddGroup.rightUniformSpace Y
  have : IsUniformAddGroup X := isUniformAddGroup_of_addCommGroup
  have : IsUniformAddGroup Y := isUniformAddGroup_of_addCommGroup
  have : CompleteSpace X := hCX
  have : CompleteSpace Y := hCY
  have : (uniformity Y).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_zero Y]
    infer_instance
  have : BaireSpace Y := BaireSpace.of_completelyPseudoMetrizable
  let A : X →L[ℂ] Y := ⟨L, hc⟩
  have hopen : IsOpenMap A := by
    apply isOpenMap_of_not_isMeagre_range A
    change ¬ IsMeagre (range L)
    rw [hbij.surjective.range_eq]
    exact not_isMeagre_of_isOpen isOpen_univ univ_nonempty
  let e := LinearEquiv.ofBijective L hbij
  refine ⟨{ e with continuous_toFun := hc, continuous_invFun := ?_ }, hL⟩
  exact e.toEquiv.continuous_symm_iff.mpr hopen

/-- A largest Bruhat structural pair realizes every Schwartz–Bruhat function. -/
private theorem schwartzBruhat_maxStage_surjective {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (a : BruhatStructuralPair G) (ha : ∀ b, b ≤ a) (e : ElementaryLCAPresentation a.quotient) :
    Surjective (schwartzBruhatStageInclusion a e) := by
  intro f
  obtain ⟨b, e', s, hs⟩ := (mem_schwartzBruhatSubmodule_iff f.val).mp f.property
  exact (schwartzBruhatStage_transition (G := G) (a := b) (b := a) (ha b) e' e).elim
    fun j hj ↦ ⟨j s, Subtype.ext ((hj.1 s).trans hs)⟩

/-- A real coordinate gives a maximal structural pair with a one-dimensional
elementary presentation. -/
private theorem realCoordinate_bruhatPresentation {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (c : G ≃ₜ* Multiplicative ℝ) (line : EuclideanSpace ℝ (Fin 1) ≃L[ℝ] ℝ) :
    ∃ a : BruhatStructuralPair G, (∀ b, b ≤ a) ∧
      ∃ (hm : ∀ x : G, x ∈ a.val.1)
        (w : a.quotient ≃ₜ* Multiplicative (ElementaryLieGroup 1 0 0 PUnit)),
        ∀ x : G, line (w (QuotientGroup.mk ⟨x, hm x⟩)).toAdd.1 = (c x).toAdd := by
  have : ConnectedSpace (Multiplicative ℝ) := inferInstanceAs (ConnectedSpace ℝ)
  have : ConnectedSpace G := c.symm.surjective.connectedSpace c.symm.continuous
  let chart : EuclideanSpace ℝ (Fin 1) ≃ₜ G := line.toHomeomorph.trans c.symm.toHomeomorph
  have hgood : IsBruhatGoodSubgroup (⊥ : Subgroup G) :=
    isBruhatGoodSubgroup_bot_iff.mpr ⟨1, ⟨chart.chartedSpace⟩⟩
  let H : Subgroup G := ⊤
  let i : G ≃ₜ* H :=
    ⟨Subgroup.topEquiv.symm, continuous_id.subtype_mk _, continuous_subtype_val⟩
  have htop : IsOpen (H : Set G) := isOpen_univ
  let : ConnectedSpace H := i.surjective.connectedSpace i.continuous
  let : LocallyCompactSpace H := htop.isOpenEmbedding_subtypeVal.locallyCompactSpace
  have hgen : IsCompactlyGeneratedGroup H := by
    obtain ⟨U, hUc, hU⟩ := exists_compact_mem_nhds (1 : H)
    have hOpen : IsOpen (Subgroup.closure U : Set H) :=
      Subgroup.isOpen_of_mem_nhds _ (mem_of_superset hU Subgroup.subset_closure)
    exact ⟨U, hU, hUc, SetLike.coe_injective
      ((OpenSubgroup.isClopen ⟨Subgroup.closure U, hOpen⟩).eq_univ ⟨1, Subgroup.one_mem _⟩)⟩
  let a : BruhatStructuralPair G := ⟨(H, OrderDual.toDual ⊥), htop, hgen, hgood, bot_le⟩
  have hmem (x : G) : x ∈ a.val.1 := Subgroup.mem_top x
  let p := (QuotientGroup.mk' _ : H →* a.quotient).comp i.toMulEquiv.toMonoidHom
  have hp : IsOpenQuotientMap p :=
    QuotientGroup.isOpenQuotientMap_mk.comp i.toHomeomorph.isOpenQuotientMap
  have hinj : Injective p := (MonoidHom.ker_eq_bot_iff p).mp (le_antisymm (fun x hx ↦ by
    change (QuotientGroup.mk (i x) : a.quotient) = 1 at hx
    exact (a.quotient_mk_eq_one (i x)).mp hx) bot_le)
  let q := (MulEquiv.ofBijective p ⟨hinj, hp.surjective⟩).toContinuousMulEquiv
    (fun _ ↦ hp.isQuotientMap.isOpen_preimage)
  let : Unique ((Fin 0 → AddCircle (1 : ℝ)) × (Fin 0 → ℤ) × PUnit) := uniqueOfSubsingleton 0
  let w : Multiplicative (ElementaryLieGroup 1 0 0 PUnit) ≃ₜ* Multiplicative ℝ :=
    ContinuousMulEquiv.mk' ((Homeomorph.prodUnique _ _).trans line.toHomeomorph)
      (fun x y ↦ line.map_add x.toAdd.1 y.toAdd.1)
  have ha (b : BruhatStructuralPair G) : b ≤ a := by
    change b.val.1 ≤ ⊤ ∧ (⊥ : Subgroup G) ≤ OrderDual.ofDual b.val.2
    exact ⟨le_top, bot_le⟩
  refine ⟨a, ha, hmem, q.symm.trans (c.trans w.symm), fun x ↦ ?_⟩
  change (w (w.symm (c (q.symm (q x))))).toAdd = _
  rw [q.symm_apply_apply, w.apply_symm_apply]

/-- In real coordinates, the Schwartz–Bruhat space of the real group carries the
usual real-line Schwartz topology. -/
private theorem schwartzBruhat_realCoordinate_equiv {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (c : G ≃ₜ* Multiplicative ℝ) :
    ∃ e : 𝓢(ℝ, ℂ) ≃L[ℂ] SchwartzBruhat G,
      ∀ f x, e f x = f (c x).toAdd := by
  have : SecondCountableTopology (Multiplicative ℝ) := inferInstanceAs (SecondCountableTopology ℝ)
  have : SecondCountableTopology G := c.toHomeomorph.isEmbedding.secondCountableTopology
  let line := (EuclideanSpace.equiv (Fin 1) ℝ).trans (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ)
  refine (realCoordinate_bruhatPresentation (G := G) c line).elim fun a hp ↦ ?_
  refine hp.2.elim fun hm hm' ↦ hm'.elim fun w hw ↦ ?_
  have ha := hp.1
  let e : ElementaryLCAPresentation a.quotient := ⟨1, 0, 0, PUnit, w⟩
  let J : SchwartzBruhatStage e →ₗ[ℂ] SchwartzBruhat G := schwartzBruhatStageInclusion a e
  have hJ : IsEmbedding J := schwartzBruhatStage_isEmbedding a e
  have hs : Surjective J := schwartzBruhat_maxStage_surjective a ha e
  let A := LinearEquiv.ofBijective J ⟨hJ.injective, hs⟩
  let B := ContinuousLinearEquiv.ofIsHomeomorph A
    (isHomeomorph_iff_isEmbedding_surjective.mpr ⟨hJ, hs⟩)
  refine elementarySchwartz_line_equiv.elim fun T hT ↦ ?_
  let L := (schwartzChangeVariable ℂ line).trans (T.trans B)
  refine ⟨L, fun f x ↦ ?_⟩
  change (show SchwartzBruhat G from
    schwartzBruhatStageInclusion a e (T (schwartzChangeVariable ℂ line f))) x = _
  rw [schwartzBruhatStageInclusion_apply, schwartzBruhatStageRealization_apply,
    dite_eq_left (hm x), hT]
  exact congrArg f (hw x)

private def positiveRealLogEquiv : ℝ≥0ˣ ≃ₜ* Multiplicative ℝ := by
  let e : ℝ≥0ˣ ≃ₜ Multiplicative ℝ :=
    (Nonneg.unitsHomeomorphPos ℝ).trans Real.expOrderIso.symm.toHomeomorph
  have he (t : ℝ≥0ˣ) : (e t).toAdd = Real.log (t.val : ℝ) :=
    (Real.log_of_pos (NNReal.coe_pos.mpr (Units.zero_lt t))).symm
  refine ContinuousMulEquiv.mk' e fun s t ↦ ?_
  change (e (s * t)).toAdd = (e s).toAdd + (e t).toAdd
  rw [he, he, he, Units.val_mul, NNReal.coe_mul,
    Real.log_mul (NNReal.coe_pos.mpr (Units.zero_lt s)).ne'
      (NNReal.coe_pos.mpr (Units.zero_lt t)).ne']

private theorem positiveRealLogEquiv_apply (t : ℝ≥0ˣ) :
    (positiveRealLogEquiv t).toAdd = Real.log (t.val : ℝ) :=
  (Real.log_of_pos (NNReal.coe_pos.mpr (Units.zero_lt t))).symm

local notation "IdModulation" => ContinuousMonoidHom.id ℝ≥0ˣ
local notation "PositiveRealStageIndex" => {k : Subgroup ℝ≥0ˣ // IsCompact (k : Set ℝ≥0ˣ) ∧
  IsCompactlyGeneratedGroup (lcaAnnihilator k)}

private theorem positiveRealCompact_eq_bot (k : PositiveRealStageIndex) : k.val = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro x hx
  exact Subgroup.mem_bot.mpr (compactSubgroup_le_modulation_ker IdModulation k.val k.property.1 hx)

private def positiveRealStageEquiv (k : PositiveRealStageIndex) : (ℝ≥0ˣ ⧸ k.val) ≃ₜ* ℝ≥0ˣ := by
  let e := (QuotientGroup.quotientMulEquivOfEq (positiveRealCompact_eq_bot k)).trans
    QuotientGroup.quotientBot
  apply e.toContinuousMulEquiv
  intro s
  exact (QuotientGroup.isQuotientMap_mk k.val).isOpen_preimage.symm

private theorem positiveRealStageEquiv_mk (k : PositiveRealStageIndex) (t : ℝ≥0ˣ) :
    positiveRealStageEquiv k (t : ℝ≥0ˣ ⧸ k.val) = t := rfl

private theorem nonempty_positiveRealStage (I : Set ℝ) (hInt : OrdConnected I)
    (hne : I.Nonempty) : Nonempty PositiveRealStageIndex := by
  have hm : IsModulation IdModulation := ⟨isProperMap_id, ⟨(Units.mk0 2 (by norm_num) : ℝ≥0ˣ), by
    intro h
    have := congrArg (fun t : ℝ≥0ˣ ↦ (t.val : ℝ)) h
    norm_num at this⟩⟩
  obtain ⟨k, _⟩ := modulatedExponentialDecay_exists_stage IdModulation I hm surjective_id hInt hne 0
  exact ⟨k⟩

/-- The real exponential weight is precisely the power weight in positive-real coordinates. -/
private theorem identityWeight_log (a : ℝ) (t : ℝ≥0ˣ) :
    (t.val : ℝ) ^ a = Real.exp (a * (positiveRealLogEquiv t).toAdd) := by
  rw [positiveRealLogEquiv_apply, Real.rpow_def_of_pos (NNReal.coe_pos.mpr (Units.zero_lt t)),
    mul_comm]

/-- The power weight in a positive-real coordinate agrees with the
exponential weight in its logarithmic coordinate. -/
private theorem logWeight_comp {G : Type*} [CommGroup G] [TopologicalSpace G]
    (n : G →ₜ* ℝ≥0ˣ) (d : G ≃ₜ* ℝ≥0ˣ) (hd : ∀ x, n x = d x)
    (a : ℝ) (f : ℝ → ℂ) (x : G) :
    modulationWeight n a (fun t ↦ f (positiveRealLogEquiv (d t)).toAdd) x =
      logExponentialWeight a f (positiveRealLogEquiv (d x)).toAdd := by
  change ((((n x).val : ℝ) ^ a : ℝ) : ℂ) * _ =
    (Real.exp (a * (positiveRealLogEquiv (d x)).toAdd) : ℂ) * _
  rw [hd x, identityWeight_log]

/-- Pullback by a real coordinate carries the Schwartz condition for each
logarithmic twist to the corresponding modulation twist, in both directions. -/
private theorem logDecay_mem_iff {G : Type*} [CommGroup G] [TopologicalSpace G]
    (n : G →ₜ* ℝ≥0ˣ) (d : G ≃ₜ* ℝ≥0ˣ) (hd : ∀ x, n x = d x) (I : Set ℝ)
    (S : 𝓢(ℝ, ℂ) ≃L[ℂ] SchwartzBruhat G)
    (hS : ∀ f x, S f x = f (positiveRealLogEquiv (d x)).toAdd) (f : ℝ → ℂ) :
    f ∈ logExponentialDecaySubmodule I ↔
      (fun x ↦ f (positiveRealLogEquiv (d x)).toAdd) ∈ modulatedExponentialDecaySubmodule n I := by
  let c := d.trans positiveRealLogEquiv
  let g (x : G) := f (c x).toAdd
  change f ∈ logExponentialDecaySubmodule I ↔ g ∈ modulatedExponentialDecaySubmodule n I
  simp only [logExponentialDecaySubmodule, modulatedExponentialDecaySubmodule,
    Submodule.mem_iInf, Submodule.mem_comap]
  constructor
  · intro hf a
    obtain ⟨s, hs⟩ := hf a
    have hw : modulationWeight n a g = (S s).val := by
      funext x
      change modulationWeight n a g x = S s x
      exact (logWeight_comp n d hd a f x).trans
        ((congrFun hs (c x).toAdd).symm.trans (hS s x).symm)
    exact hw.symm ▸ (S s).property
  · intro hg a
    let F : SchwartzBruhat G := ⟨modulationWeight n a g, hg a⟩
    let s := S.symm F
    refine ⟨s, funext fun y ↦ ?_⟩
    let x := c.symm (Multiplicative.ofAdd y)
    have hx : (c x).toAdd = y := congrArg Multiplicative.toAdd (c.apply_symm_apply _)
    change s y = logExponentialWeight a f y
    calc
      s y = s (c x).toAdd := congrArg s hx.symm
      _ = S s x := (hS s x).symm
      _ = F x := congrArg (fun z : SchwartzBruhat G ↦ z x) (S.apply_symm_apply F)
      _ = logExponentialWeight a f (c x).toAdd := logWeight_comp n d hd a f x
      _ = _ := congrArg (logExponentialWeight a f) hx

/-- Pullback by the logarithmic coordinate identifies the decay submodules
and intertwines their twists. -/
private theorem positiveRealDecay_linear_equiv {G : Type*} [CommGroup G] [TopologicalSpace G]
    (n : G →ₜ* ℝ≥0ˣ) (d : G ≃ₜ* ℝ≥0ˣ) (hd : ∀ x, n x = d x) (I : Set ℝ)
    (S : 𝓢(ℝ, ℂ) ≃L[ℂ] SchwartzBruhat G)
    (hS : ∀ f x, S f x = f (positiveRealLogEquiv (d x)).toAdd) :
    ∃ e : logExponentialDecaySubmodule I ≃ₗ[ℂ] modulatedExponentialDecaySubmodule n I,
      (∀ f x, (e f).val x = f.val (positiveRealLogEquiv (d x)).toAdd) ∧
      (∀ a f, modulatedExponentialDecayTwist n I a (e f) = S (logExponentialDecayTwist I a f)) := by
  let c := d.trans positiveRealLogEquiv
  have hmem (f : ℝ → ℂ) : f ∈ logExponentialDecaySubmodule I ↔
      (fun x ↦ f (c x).toAdd) ∈ modulatedExponentialDecaySubmodule n I :=
    logDecay_mem_iff n d hd I S hS f
  let inv (g : modulatedExponentialDecaySubmodule n I) (y : ℝ) :=
    g.val (c.symm (Multiplicative.ofAdd y))
  have hinv (g : modulatedExponentialDecaySubmodule n I) : inv g ∈ logExponentialDecaySubmodule I :=
    (hmem (inv g)).mpr (show (fun x ↦ inv g (c x).toAdd) ∈ modulatedExponentialDecaySubmodule n I from by
      have hv : (fun x ↦ inv g (c x).toAdd) = g.val :=
        funext fun x ↦ congrArg g.val (c.symm_apply_apply x)
      exact hv.symm ▸ g.property)
  let e : logExponentialDecaySubmodule I ≃ₗ[ℂ] modulatedExponentialDecaySubmodule n I :=
    { toFun := fun f ↦ ⟨fun x ↦ f.val (c x).toAdd, (hmem f.val).mp f.property⟩
      invFun := fun g ↦ ⟨inv g, hinv g⟩
      left_inv := fun f ↦ Subtype.ext (funext fun y ↦ congrArg (fun z : Multiplicative ℝ ↦ f.val z.toAdd)
        (c.apply_symm_apply (Multiplicative.ofAdd y)))
      right_inv := fun g ↦ Subtype.ext (funext fun x ↦ congrArg g.val (c.symm_apply_apply x))
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  refine ⟨e, fun _ _ ↦ rfl, fun a f ↦ Subtype.ext (funext fun x ↦ ?_)⟩
  change modulationWeight n a (fun x ↦ f.val (c x).toAdd) x = S (logExponentialDecayTwist I a f) x
  calc
    _ = logExponentialWeight a f.val (c x).toAdd := logWeight_comp n d hd a f.val x
    _ = logExponentialDecayTwist I a f (c x).toAdd :=
      (logExponentialDecayTwist_apply I a f (c x).toAdd).symm
    _ = _ := (hS _ x).symm

/-- Intertwining the coordinate maps of two projective topologies lifts a
linear equivalence to a continuous linear equivalence. -/
private def projectiveEquivOfTwists
    {ι X Y V W : Type*}
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup V] [AddCommGroup W]
    [Module ℂ X] [Module ℂ Y] [Module ℂ V] [Module ℂ W]
    [TopologicalSpace X] [TopologicalSpace V] [TopologicalSpace W]
    [IsTopologicalAddGroup X] [PolynormableSpace ℂ W]
    (U : ι → X →ₗ[ℂ] V) (T : ι → Y →ₗ[ℂ] W)
    (hU : IsInducing (fun (x : X) a ↦ U a x))
    (L : X ≃ₗ[ℂ] Y) (S : V ≃L[ℂ] W) (hL : ∀ a x, T a (L x) = S (U a x)) :
    let p := fun i : ι × {q : Seminorm ℂ W // Continuous q} ↦ i.2.val.comp (T i.1)
    X ≃L[ℂ] WithGeneratingSeminorms Y p := by
  let p := fun i : ι × {q : Seminorm ℂ W // Continuous q} ↦ i.2.val.comp (T i.1)
  let F := WithGeneratingSeminorms Y p
  let e : X ≃ₗ[ℂ] F := L
  have hproj := withGeneratingSeminorms_spec Y p
  let B (a : ι) : F →ₗ[ℂ] W := T a
  have hT (a : ι) : Continuous (B a) :=
    (PolynormableSpace.withSeminorms ℂ W).continuous_of_continuous_comp (B a)
      fun q ↦ hproj.continuous_seminorm (a, q)
  have he : Continuous e := by
    apply hproj.continuous_of_continuous_comp e.toLinearMap
    rintro ⟨a, q⟩
    have hcoord : Continuous (U a) := (continuous_apply a).comp hU.continuous
    have hEq : ((p (a, q)).comp e.toLinearMap : X → ℝ) = q.val ∘ S ∘ U a :=
      funext fun x ↦ congrArg q.val (hL a x)
    exact hEq.symm ▸ q.property.comp (S.continuous.comp hcoord)
  refine { e with continuous_toFun := he, continuous_invFun := ?_ }
  apply hU.continuous_iff.mpr
  apply continuous_pi
  intro a
  have hEq : (fun y : F ↦ U a (e.symm y)) = S.symm ∘ B a := by
    funext y
    apply S.injective
    exact (hL a (L.symm y)).symm.trans
      ((congrArg (T a) (L.apply_symm_apply y)).trans (S.apply_symm_apply (T a y)).symm)
  change Continuous (fun y : F ↦ U a (e.symm y))
  exact hEq.symm ▸ S.symm.continuous.comp (hT a)

/-- Exponential decay in a positive-real coordinate is the projective condition
on the real logarithmic profile. -/
private theorem positiveRealDecay_projective_equiv {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (d : G ≃ₜ* ℝ≥0ˣ) (n : G →ₜ* ℝ≥0ˣ) (hd : ∀ x, n x = d x)
    (I : Set ℝ) (hne : I.Nonempty) :
    let p := fun i : I × {q : Seminorm ℂ (SchwartzBruhat G) // Continuous q} ↦
      i.2.val.comp (modulatedExponentialDecayTwist n I i.1)
    ∃ e : PositiveRealExponentialDecay I ≃L[ℂ]
        WithGeneratingSeminorms (modulatedExponentialDecaySubmodule n I) p,
      ∀ f x, (e f).val x = f.val (positiveRealLogEquiv (d x)).toAdd := by
  refine (schwartzBruhat_realCoordinate_equiv (G := G) (d.trans positiveRealLogEquiv)).elim
    fun S hS ↦ ?_
  refine (positiveRealDecay_linear_equiv n d hd I S hS).elim fun L hL ↦ ?_
  have hU := (positiveRealExponentialDecay_isEmbedding I hne).isInducing
  let e := projectiveEquivOfTwists (X := PositiveRealExponentialDecay I)
    (fun a ↦ logExponentialDecayTwist I a) (modulatedExponentialDecayTwist n I)
    hU L S hL.2
  exact ⟨e, hL.1⟩

/-- A bijective inclusion from the sole stage of a locally convex limit is a
continuous linear equivalence for the final topology. -/
private theorem singleStage_final_equiv
    {κ : Type*} [Subsingleton κ] {X : κ → Type*} {Y : Type*}
    [∀ k, AddCommGroup (X k)] [∀ k, Module ℂ (X k)] [∀ k, TopologicalSpace (X k)]
    [∀ k, IsTopologicalAddGroup (X k)] [∀ k, PolynormableSpace ℂ (X k)]
    [AddCommGroup Y] [Module ℂ Y]
    (J : ∀ k, X k →ₗ[ℂ] Y) (k₀ : κ) (hj : Bijective (J k₀)) :
    let p := (Subtype.val : {q : Seminorm ℂ Y // ∀ k, Continuous (q ∘ J k)} → _)
    ∃ e : X k₀ ≃L[ℂ] WithGeneratingSeminorms Y p, ∀ x, e x = J k₀ x := by
  let p := (Subtype.val : {q : Seminorm ℂ Y // ∀ k, Continuous (q ∘ J k)} → _)
  let F := WithGeneratingSeminorms Y p
  let L : X k₀ →ₗ[ℂ] F := J k₀
  let e := LinearEquiv.ofBijective L hj
  have hF := withGeneratingSeminorms_spec Y p
  refine ⟨{ e with continuous_toFun := ?_, continuous_invFun := ?_ }, fun _ ↦ rfl⟩
  · exact hF.continuous_of_continuous_comp L fun q ↦ q.property k₀
  · apply (PolynormableSpace.withSeminorms ℂ (X k₀)).continuous_of_continuous_comp e.symm.toLinearMap
    intro q
    have hcomp : (fun x : X k₀ ↦ q.val (e.symm (e x))) = q.val :=
      funext fun x ↦ congrArg q.val (e.symm_apply_apply x)
    have hbase : Continuous (q.val.comp e.symm.toLinearMap ∘ J k₀) := by
      change Continuous (fun x : X k₀ ↦ q.val (e.symm (e x)))
      exact Eq.mpr (congrArg (fun f : X k₀ → ℝ ↦ Continuous f) hcomp) q.property
    let q' : {q : Seminorm ℂ Y // ∀ k, Continuous (q ∘ J k)} :=
      ⟨q.val.comp e.symm.toLinearMap, fun k ↦
        Eq.mp (congrArg (fun i ↦ Continuous (q.val.comp e.symm.toLinearMap ∘ J i))
          (Subsingleton.elim k₀ k)) hbase⟩
    exact hF.continuous_seminorm q'

/-- Paper: Example D.3.3.4, p. 805. For the identity modulation, the inductive
space agrees with the positive-real projective space in logarithmic coordinates. -/
theorem identityModulationExponentialDecay_equiv (I : Set ℝ) (hInt : OrdConnected I)
    (hne : I.Nonempty) :
    ∃ e : PositiveRealExponentialDecay I ≃L[ℂ]
        ModulatedExponentialDecay (ContinuousMonoidHom.id ℝ≥0ˣ) I,
      ∀ (f : PositiveRealExponentialDecay I) (t : ℝ≥0ˣ),
        (e f).val t = f.val (Real.log (t.val : ℝ)) := by
  refine (nonempty_positiveRealStage I hInt hne).elim fun k ↦ ?_
  let : IsClosed (k.val : Set ℝ≥0ˣ) := k.property.1.isClosed
  let n := quotientModulation IdModulation k.val k.property.1
  have hn (x : ℝ≥0ˣ ⧸ k.val) : n x = positiveRealStageEquiv k x := by
    refine QuotientGroup.induction_on x fun t ↦ ?_
    exact (positiveRealStageEquiv_mk k t).symm
  refine (positiveRealDecay_projective_equiv
    (G := ℝ≥0ˣ ⧸ k.val) (positiveRealStageEquiv k) n hn I hne).elim fun E hE ↦ ?_
  let J := modulatedExponentialDecayStageInclusion IdModulation I
  let : Subsingleton PositiveRealStageIndex := ⟨fun k₁ k₂ ↦ Subtype.ext
    ((positiveRealCompact_eq_bot k₁).trans (positiveRealCompact_eq_bot k₂).symm)⟩
  have hJ := modulatedExponentialDecayStageInclusion_range IdModulation I k
  have hj : Bijective (J k) :=
    ⟨hJ.1, fun f ↦ (hJ.2 f).mpr fun g u ↦ by
      have hu : u.val = 1 := Subgroup.mem_bot.mp (positiveRealCompact_eq_bot k ▸ u.property)
      exact congrArg f.val ((congrArg (g * ·) hu).trans (mul_one g))⟩
  refine (singleStage_final_equiv
    (X := ModulatedExponentialDecayStage IdModulation I) (Y := modulatedExponentialDecaySubmodule IdModulation I)
    J k hj).elim fun B hB ↦ ?_
  refine ⟨E.trans B, fun f t ↦ ?_⟩
  change (B (E f)).val t = _
  refine (congrArg (fun u : modulatedExponentialDecaySubmodule IdModulation I ↦ u.val t) (hB (E f))).trans ?_
  change (E f).val (t : ℝ≥0ˣ ⧸ k.val) = _
  exact (hE f _).trans (congrArg f.val ((congrArg (fun u ↦ (positiveRealLogEquiv u).toAdd)
    (positiveRealStageEquiv_mk k t)).trans (positiveRealLogEquiv_apply t)))

end IdentityModulation

section ModulatedExamples

variable {G : Type*} [CommGroup G] [TopologicalSpace G]
  [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
variable (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m) (hms : Surjective m)

local notation "GoodCompact" => {k : Subgroup G // IsCompact (k : Set G) ∧
  IsCompactlyGeneratedGroup (lcaAnnihilator k)}

section WeightTranslation

variable (I : Set ℝ)

/-- Paper: (D.3.3.2), p. 805. The topology of a decay stage is induced by the
joint map to the product of its Schwartz–Bruhat twists. -/
private theorem modulatedDecayStage_twists_isInducing (k : GoodCompact) :
    IsInducing (fun (f : ModulatedExponentialDecayStage m I k) (a : I) ↦
      modulatedExponentialDecayTwist (quotientModulation m k.val k.property.1) I a f) := by
  let T : ModulatedExponentialDecayStage m I k →ₗ[ℂ] (I → SchwartzBruhat (G ⧸ k.val)) :=
    LinearMap.pi (modulatedExponentialDecayTwist (quotientModulation m k.val k.property.1) I)
  change IsInducing T
  have hPi := withSeminorms_pi
    (fun _ : I ↦ PolynormableSpace.withSeminorms ℂ (SchwartzBruhat (G ⧸ k.val)))
  have hInduced := WithSeminorms.topologicalSpace_eq_iInf (t := induced T inferInstance)
    (T.withSeminorms_induced hPi)
  refine ⟨(ModulatedExponentialDecayStage.withSeminorms m I k).topologicalSpace_eq_iInf.trans
    (Eq.trans ?_ hInduced.symm)⟩
  exact (Equiv.sigmaEquivProd I _).symm.iInf_congr (fun _ ↦ rfl)

/-- Translating the exponent set by the negative of a weight exponent makes
multiplication by that weight a continuous linear equivalence. -/
private theorem modulatedDecay_weightTranslation (a : ℝ) :
    ∃ e : ModulatedExponentialDecay m I ≃L[ℂ]
        ModulatedExponentialDecay m ((fun b : ℝ ↦ b - a) '' I),
      ∀ f, (e f).val = modulationWeight m a f.val := by
  have weight_add {A : Type _} [CommGroup A] [TopologicalSpace A]
      (n : A →ₜ* ℝ≥0ˣ) (b c : ℝ) (f : A → ℂ) :
      modulationWeight n b (modulationWeight n c f) = modulationWeight n (b + c) f := by
    funext x
    have hx : 0 < ((n x).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt (n x))
    simp only [modulationWeight, LinearMap.mulLeft_apply, Pi.mul_apply,
      Real.rpow_add hx, Complex.ofReal_mul, mul_assoc]
  let shift {A : Type _} [CommGroup A] [TopologicalSpace A]
      (n : A →ₜ* ℝ≥0ˣ) (S T : Set ℝ) (c : ℝ) (h : ∀ b ∈ T, b + c ∈ S) :
      modulatedExponentialDecaySubmodule n S →ₗ[ℂ] modulatedExponentialDecaySubmodule n T :=
    ((modulationWeight n c).comp (modulatedExponentialDecaySubmodule n S).subtype).codRestrict
      (modulatedExponentialDecaySubmodule n T) (by
        intro f
        refine (Submodule.mem_iInf _).mpr fun b ↦ Submodule.mem_comap.mpr ?_
        change modulationWeight n b (modulationWeight n c f.val) ∈ schwartzBruhatSubmodule A
        rw [weight_add]
        exact modulationWeight_mem_schwartzBruhat n S ⟨b + c, h b b.property⟩ f)
  let continuousShift (S T : Set ℝ) (c : ℝ) (h : ∀ b ∈ T, b + c ∈ S) :
      ModulatedExponentialDecay m S →L[ℂ] ModulatedExponentialDecay m T := by
    let F : ModulatedExponentialDecay m S →ₗ[ℂ] ModulatedExponentialDecay m T := shift m S T c h
    refine ⟨F, ?_⟩
    change Continuous F
    let FinalSeminorms (U : Set ℝ) := {q : Seminorm ℂ (modulatedExponentialDecaySubmodule m U) //
      ∀ k : GoodCompact, Continuous (q ∘ modulatedExponentialDecayStageInclusion m U k)}
    have generating (U : Set ℝ) :=
      withGeneratingSeminorms_spec _ (Subtype.val : FinalSeminorms U → _)
    refine (generating T).continuous_of_continuous_comp F fun p ↦ ?_
    let q : Seminorm ℂ (ModulatedExponentialDecay m S) := p.val.comp F
    change Continuous q
    have hq (k : GoodCompact) : Continuous (q ∘ modulatedExponentialDecayStageInclusion m S k) := by
      let n := quotientModulation m k.val k.property.1
      let stageShift : ModulatedExponentialDecayStage m S k →ₗ[ℂ]
          ModulatedExponentialDecayStage m T k := shift n S T c h
      have hstage : Continuous stageShift := by
        apply (modulatedDecayStage_twists_isInducing m T k).continuous_iff.mpr
        apply continuous_pi
        intro b
        let d : S := ⟨b + c, h b b.property⟩
        have htwist : Continuous (fun f : ModulatedExponentialDecayStage m S k ↦
            modulatedExponentialDecayTwist n S d f) :=
          (continuous_apply d).comp (modulatedDecayStage_twists_isInducing m S k).continuous
        exact htwist.congr fun f ↦ Subtype.ext (weight_add n b c f.val).symm
      exact ((p.property k).comp hstage).congr fun f ↦ congrArg p.val (Subtype.ext rfl)
    exact (generating S).continuous_seminorm (⟨q, hq⟩ : FinalSeminorms S)
  let J := (fun b : ℝ ↦ b - a) '' I
  have hforward : ∀ b ∈ J, b + a ∈ I := by
    rintro b ⟨d, hd, rfl⟩
    simpa only [sub_add_cancel] using hd
  have hbackward : ∀ b ∈ I, b + -a ∈ J := by
    intro b hb
    exact ⟨b, hb, sub_eq_add_neg b a⟩
  let forward : ModulatedExponentialDecay m I →L[ℂ] ModulatedExponentialDecay m J := continuousShift I J a hforward
  let backward : ModulatedExponentialDecay m J →L[ℂ] ModulatedExponentialDecay m I := continuousShift J I (-a) hbackward
  have hleft : LeftInverse backward forward := by
    intro f
    apply Subtype.ext
    change modulationWeight m (-a) (modulationWeight m a f.val) = f.val
    rw [weight_add, neg_add_cancel, modulationWeight_zero]
  have hright : RightInverse backward forward := by
    intro f
    apply Subtype.ext
    change modulationWeight m a (modulationWeight m (-a) f.val) = f.val
    rw [weight_add, add_neg_cancel, modulationWeight_zero]
  exact ⟨ContinuousLinearEquiv.equivOfInverse forward backward hleft hright, fun _ ↦ rfl⟩

end WeightTranslation

include hm hms

set_option linter.unusedSectionVars false in
/-- Paper: Example D.3.3.5, p. 805. Weighting by the difference of exponents
identifies the two singleton decay spaces.
Deviation: This includes the ordinary Schwartz–Bruhat case at exponent zero
via the continuous equivalence in the next declaration. -/
theorem modulatedExponentialDecay_singleton_equiv (a b : ℝ) :
    ∃ e : ModulatedExponentialDecay m {a} ≃L[ℂ] ModulatedExponentialDecay m {b},
      ∀ f, (e f).val = modulationWeight m (a - b) f.val := by
  have hset : (fun x : ℝ ↦ x - (a - b)) '' ({a} : Set ℝ) = {b} :=
    Set.image_singleton.trans (congrArg (fun x : ℝ ↦ ({x} : Set ℝ)) (sub_sub_cancel a b))
  let P (J : Set ℝ) :=
    ∃ e : ModulatedExponentialDecay m {a} ≃L[ℂ] ModulatedExponentialDecay m J,
      ∀ f, (e f).val = modulationWeight m (a - b) f.val
  have h : P ((fun x : ℝ ↦ x - (a - b)) '' ({a} : Set ℝ)) :=
    modulatedDecay_weightTranslation m {a} (a - b)
  exact @Eq.ndrec (Set ℝ) ((fun x : ℝ ↦ x - (a - b)) '' ({a} : Set ℝ))
    P h ({b} : Set ℝ) hset

omit hm hms in
/-- Pullback from a compact quotient is continuous because it lifts each
structural stage with the same elementary coordinates. -/
private theorem continuous_schwartzBruhat_compactQuotient_pullback
    (k : Subgroup G) (hk : IsCompact (k : Set G)) :
    ∃ P : SchwartzBruhat (G ⧸ k) →L[ℂ] SchwartzBruhat G,
      ∀ f g, P f g = f (g : G ⧸ k) := by
  let P : SchwartzBruhat (G ⧸ k) →ₗ[ℂ] SchwartzBruhat G :=
    ((LinearMap.pi fun g : G ↦ LinearMap.proj (g : G ⧸ k)).comp
      (schwartzBruhatSubmodule (G ⧸ k)).subtype).codRestrict (schwartzBruhatSubmodule G)
        (fun f ↦ schwartzBruhatSubmodule_compactQuotient_pullback_mem k hk f.property)
  refine ⟨⟨P, ?_⟩, fun _ _ ↦ rfl⟩
  apply (withGeneratingSeminorms_spec (schwartzBruhatSubmodule G) Subtype.val)
    |>.continuous_of_continuous_comp P
  intro p
  let q := p.val.comp P
  refine (withGeneratingSeminorms_spec (schwartzBruhatSubmodule (G ⧸ k)) Subtype.val)
    |>.continuous_seminorm ⟨q, ?_⟩
  intro b e
  obtain ⟨c, v, hc, hv⟩ := bruhatStructuralPair_lift_compactQuotient k hk b
  let e' : ElementaryLCAPresentation c.quotient := { e with equiv := v.trans e.equiv }
  have hstage (s : SchwartzBruhatStage e) :
      schwartzBruhatStageInclusion c e' s = P (schwartzBruhatStageInclusion b e s) := by
    apply Subtype.ext
    funext g
    change schwartzBruhatStageRealization c e' s g =
      schwartzBruhatStageRealization b e s (g : G ⧸ k)
    by_cases hg : g ∈ c.val.1
    · have hqg := (hc g).mp hg
      calc
        _ = s (e'.equiv (QuotientGroup.mk ⟨g, hg⟩)).toAdd :=
          (schwartzBruhatStageRealization_apply c e' s g).trans (dite_eq_left hg)
        _ = s (e.equiv (QuotientGroup.mk ⟨(g : G ⧸ k), hqg⟩)).toAdd :=
          congrArg (fun x : b.quotient ↦ s (e.equiv x).toAdd) (hv g hg)
        _ = _ := ((schwartzBruhatStageRealization_apply b e s (g : G ⧸ k)).trans
          (dite_eq_left hqg)).symm
    · have hqg := mt (hc g).mpr hg
      exact ((schwartzBruhatStageRealization_apply c e' s g).trans (dite_eq_right hg)).trans
        (((schwartzBruhatStageRealization_apply b e s (g : G ⧸ k)).trans (dite_eq_right hqg)).symm)
  exact (p.property c e').congr fun s ↦ congrArg p.val (hstage s)

omit hm hms in
/-- The singleton twist is a linear bijection, with inverse weighting at
the opposite exponent. -/
private theorem modulatedExponentialDecayTwist_singleton_bijective {A : Type*} [CommGroup A] [TopologicalSpace A]
    (n : A →ₜ* ℝ≥0ˣ) (a : ℝ) :
    Bijective (modulatedExponentialDecayTwist n {a} ⟨a, rfl⟩) := by
  have cancel (b : ℝ) (f : A → ℂ) :
      modulationWeight n b (modulationWeight n (-b) f) = f := by
    funext x
    have hx : 0 < ((n x).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt (n x))
    simp only [modulationWeight, LinearMap.mulLeft_apply, Pi.mul_apply, ← mul_assoc,
      ← Complex.ofReal_mul, ← Real.rpow_add hx, add_neg_cancel, Real.rpow_zero,
      Complex.ofReal_one, one_mul]
  constructor
  · intro f g h
    apply Subtype.ext
    have h' : modulationWeight n a f.val = modulationWeight n a g.val := congrArg Subtype.val h
    have hinv (u : A → ℂ) : modulationWeight n (-a) (modulationWeight n a u) = u := by
      simpa only [neg_neg] using cancel (-a) u
    exact (hinv f.val).symm.trans ((congrArg (modulationWeight n (-a)) h').trans (hinv g.val))
  · intro f
    let g := modulationWeight n (-a) (f : A → ℂ)
    have hg : g ∈ modulatedExponentialDecaySubmodule n {a} := by
      refine (Submodule.mem_iInf _).mpr ?_
      intro b
      apply Submodule.mem_comap.mpr
      change modulationWeight n (b : ℝ) (modulationWeight n (-a) f.val) ∈ schwartzBruhatSubmodule A
      rw [mem_singleton_iff.mp b.property, cancel]
      exact f.property
    exact ⟨⟨g, hg⟩, Subtype.ext (cancel a f.val)⟩

omit hm hms in
/-- A structural stage descends continuously to the quotient by its compact
subgroup, where normalized Haar averaging recovers the descended function. -/
private theorem schwartzBruhatStage_compactQuotient_descent (b : BruhatStructuralPair G)
    (d : ElementaryLCAPresentation b.quotient) :
    let k := OrderDual.ofDual b.val.2
    ∃ P : SchwartzBruhatStage d →L[ℂ] SchwartzBruhat (G ⧸ k),
      ∀ s (g : G), P s (g : G ⧸ k) = schwartzBruhatStageRealization b d s g := by
  let k := OrderDual.ofDual b.val.2
  have hk : IsCompact (k : Set G) :=
    isCompact_of_isBruhatGoodSubgroup_aux k b.property.2.2.1
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let : CompactSpace k := isCompact_iff_compactSpace.mp hk
  let μ : Measure k := Measure.haarMeasure ⊤
  let : IsProbabilityMeasure μ := ⟨Measure.haarMeasure_self⟩
  have hint (c : ℂ) : (∫ _u : k, c ∂μ) = c :=
    (integral_const c).trans <|
      (congrArg (fun r : ℝ ↦ r • c) (probReal_univ (μ := μ))).trans (one_smul ℝ c)
  have havg := schwartzBruhatCosetIntegral_continuousLinear k μ hk.isClosed
  let P : SchwartzBruhat G →L[ℂ] SchwartzBruhat (G ⧸ k) := havg.choose
  have hP (f : SchwartzBruhat G) : P f = schwartzBruhatCosetIntegral k μ
      hk.isClosed f := havg.choose_spec f
  let F : SchwartzBruhatStage d →ₗ[ℂ] SchwartzBruhat G := schwartzBruhatStageInclusion b d
  have hF : Continuous F := by
    apply (withGeneratingSeminorms_spec (schwartzBruhatSubmodule G) Subtype.val)
      |>.continuous_of_continuous_comp F
    exact fun r ↦ r.property b d
  refine ⟨P.comp ⟨F, hF⟩, fun s g ↦ ?_⟩
  change P (F s) (g : G ⧸ k) = F s g
  calc
    _ = schwartzBruhatCosetIntegral k μ hk.isClosed (F s) (g : G ⧸ k) :=
      congrArg (fun f : SchwartzBruhat (G ⧸ k) ↦ f (g : G ⧸ k)) (hP (F s))
    _ = ∫ u : k, F s (g * u.val) ∂μ :=
      schwartzBruhatCosetIntegral_mk k μ hk.isClosed (F s) g
    _ = F s g := by
      have hconst (u : k) : F s (g * u.val) = F s g := by
        have hu : u.val ∈ b.val.1 := b.property.2.2.2 u.property
        change schwartzBruhatStageRealization b d s (g * u.val) =
          schwartzBruhatStageRealization b d s g
        by_cases hg : g ∈ b.val.1
        · have hgu := b.val.1.mul_mem hg hu
          let v : b.val.1 := ⟨u.val, hu⟩
          have hv : v ∈ k.comap b.val.1.subtype := u.property
          have heq : (QuotientGroup.mk ((⟨g, hg⟩ : b.val.1) * v) : b.quotient) =
              QuotientGroup.mk ⟨g, hg⟩ := QuotientGroup.mk_mul_of_mem _ hv
          exact ((schwartzBruhatStageRealization_apply b d s (g * u.val)).trans
            (dite_eq_left hgu)).trans
            ((congrArg (fun x : b.quotient ↦ s (d.equiv x).toAdd) heq).trans
              (((schwartzBruhatStageRealization_apply b d s g).trans (dite_eq_left hg)).symm))
        · have hgu : g * u.val ∉ b.val.1 :=
            fun hh ↦ hg ((b.val.1.mul_mem_cancel_right hu).mp hh)
          exact ((schwartzBruhatStageRealization_apply b d s (g * u.val)).trans
            (dite_eq_right hgu)).trans
            (((schwartzBruhatStageRealization_apply b d s g).trans (dite_eq_right hg)).symm)
      calc
        _ = ∫ _u : k, F s g ∂μ :=
          congrArg (fun u : k → ℂ ↦ ∫ v, u v ∂μ) (funext hconst)
        _ = F s g := hint (F s g)

set_option linter.unusedSectionVars false in
/-- Paper: Example D.3.3.5, p. 805. Weighting by the given exponent identifies
the singleton decay space with the ordinary Schwartz–Bruhat space. -/
theorem modulatedExponentialDecay_singleton_schwartz (a : ℝ) :
    ∃ e : ModulatedExponentialDecay m {a} ≃L[ℂ] SchwartzBruhat G,
      ∀ f, (e f : G → ℂ) = modulationWeight m a f.val := by
  let E := ModulatedExponentialDecay m {a}
  let S (k : GoodCompact) := ModulatedExponentialDecayStage m {a} k
  let q (k : GoodCompact) := quotientModulation m k.val k.property.1
  let a₀ : ({a} : Set ℝ) := ⟨a, rfl⟩
  let e : E ≃ₗ[ℂ] SchwartzBruhat G :=
    LinearEquiv.ofBijective _ (modulatedExponentialDecayTwist_singleton_bijective m a)
  let eₖ (k : GoodCompact) : S k ≃ₗ[ℂ] SchwartzBruhat (G ⧸ k.val) :=
    LinearEquiv.ofBijective _ (modulatedExponentialDecayTwist_singleton_bijective (q k) a)
  let j (k : GoodCompact) : S k →ₗ[ℂ] E := modulatedExponentialDecayStageInclusion m {a} k
  have he (k : GoodCompact) (f : S k) (g : G) :
      e (j k f) g = eₖ k f (g : G ⧸ k.val) := rfl
  let Q (k : GoodCompact) :=
    {p : Seminorm ℂ (SchwartzBruhat (G ⧸ k.val)) // Continuous p}
  let stageFamily (k : GoodCompact) (i : ({a} : Set ℝ) × Q k) :
      Seminorm ℂ (modulatedExponentialDecaySubmodule (q k) {a}) :=
    i.2.val.comp (modulatedExponentialDecayTwist (q k) {a} i.1)
  have hS (k : GoodCompact) :=
    withGeneratingSeminorms_spec (modulatedExponentialDecaySubmodule (q k) {a}) (stageFamily k)
  have hstage (k : GoodCompact) : Continuous (eₖ k) := by
    refine (PolynormableSpace.withSeminorms ℂ (SchwartzBruhat (G ⧸ k.val)))
      |>.continuous_of_continuous_comp (eₖ k).toLinearMap fun p ↦ ?_
    exact (hS k).continuous_seminorm (a₀, p)
  have hstageInv (k : GoodCompact) : Continuous (eₖ k).symm := by
    refine (hS k).continuous_of_continuous_comp (eₖ k).symm.toLinearMap ?_
    rintro ⟨b, p⟩
    have hb : b = a₀ := Subsingleton.elim _ _
    subst b
    change Continuous (fun f : SchwartzBruhat (G ⧸ k.val) ↦ p.val (eₖ k ((eₖ k).symm f)))
    have heq (f : SchwartzBruhat (G ⧸ k.val)) :
        p.val f = p.val (eₖ k ((eₖ k).symm f)) :=
      congrArg (fun g : SchwartzBruhat (G ⧸ k.val) ↦ p.val g) ((eₖ k).apply_symm_apply f).symm
    exact p.property.congr heq
  let FinalSeminorms := {p : Seminorm ℂ (modulatedExponentialDecaySubmodule m {a}) //
    ∀ k : GoodCompact, Continuous (p ∘ j k)}
  have hE := withGeneratingSeminorms_spec _ (Subtype.val : FinalSeminorms → _)
  have hfwdStage (k : GoodCompact) : Continuous (fun f : S k ↦ e (j k f)) := by
    have hh := continuous_schwartzBruhat_compactQuotient_pullback k.val k.property.1
    let P : SchwartzBruhat (G ⧸ k.val) →L[ℂ] SchwartzBruhat G := hh.choose
    have hP (u : SchwartzBruhat (G ⧸ k.val)) (g : G) :
        P u g = u (g : G ⧸ k.val) := hh.choose_spec u g
    have hc : Continuous (fun f : S k ↦ P (eₖ k f)) := P.continuous.comp (hstage k)
    have heq : (fun f : S k ↦ P (eₖ k f)) = (fun f : S k ↦ e (j k f)) := by
      funext f
      apply Subtype.ext
      funext g
      exact (hP (eₖ k f) g).trans (he k f g).symm
    exact Eq.mp (congrArg (fun u : S k → SchwartzBruhat G ↦ Continuous u) heq) hc
  have hfwd : Continuous (fun f : E ↦ e f) := by
    have hTarget := PolynormableSpace.withSeminorms ℂ (SchwartzBruhat G)
    refine hTarget.continuous_of_continuous_comp e.toLinearMap ?_
    intro p
    let r : Seminorm ℂ E := p.val.comp e.toLinearMap
    change Continuous r
    have hr (k : GoodCompact) : Continuous (fun f : S k ↦ r (j k f)) :=
      p.property.comp (hfwdStage k)
    exact hE.continuous_seminorm (⟨r, hr⟩ : FinalSeminorms)
  have hbwdStage (b : BruhatStructuralPair G) (d : ElementaryLCAPresentation b.quotient) :
      Continuous (fun f : SchwartzBruhatStage d ↦ e.symm (schwartzBruhatStageInclusion b d f)) := by
    have hd := schwartzBruhatStage_compactQuotient_descent b d
    let k₀ := OrderDual.ofDual b.val.2
    let k : GoodCompact := ⟨k₀, isCompact_of_isBruhatGoodSubgroup_aux k₀ b.property.2.2.1,
      b.property.2.2.1.2.2⟩
    let P : SchwartzBruhatStage d →L[ℂ] SchwartzBruhat (G ⧸ k₀) := hd.choose
    have hP (s : SchwartzBruhatStage d) (g : G) :
        P s (g : G ⧸ k₀) = schwartzBruhatStageRealization b d s g := hd.choose_spec s g
    let F : SchwartzBruhatStage d →ₗ[ℂ] SchwartzBruhat G := schwartzBruhatStageInclusion b d
    have hfactor (s : SchwartzBruhatStage d) : j k ((eₖ k).symm (P s)) = e.symm (F s) := by
      apply e.injective
      apply Subtype.ext
      funext g
      change e (j k ((eₖ k).symm (P s))) g = e (e.symm (F s)) g
      calc
        _ = eₖ k ((eₖ k).symm (P s)) (g : G ⧸ k.val) := he k _ g
        _ = P s (g : G ⧸ k.val) :=
          congrArg (fun f : SchwartzBruhat (G ⧸ k.val) ↦ f (g : G ⧸ k.val))
            ((eₖ k).apply_symm_apply (P s))
        _ = F s g := hP s g
        _ = _ := congrArg (fun f : SchwartzBruhat G ↦ f g) (e.apply_symm_apply (F s)).symm
    have hj : Continuous (j k) :=
      hE.continuous_of_continuous_comp (j k) (fun p ↦ p.property k)
    have hc : Continuous (fun s : SchwartzBruhatStage d ↦ j k ((eₖ k).symm (P s))) :=
      hj.comp ((hstageInv k).comp P.continuous)
    exact Eq.mp (congrArg (fun u : SchwartzBruhatStage d → E ↦ Continuous u)
      (funext hfactor)) hc
  let SchwartzSeminorms := {p : Seminorm ℂ (schwartzBruhatSubmodule G) //
    ∀ (b : BruhatStructuralPair G) (d : ElementaryLCAPresentation b.quotient),
      Continuous (p ∘ schwartzBruhatStageInclusion b d)}
  have hB := withGeneratingSeminorms_spec _ (Subtype.val : SchwartzSeminorms → _)
  have hbwd : Continuous (fun f : SchwartzBruhat G ↦ e.symm f) := by
    refine hE.continuous_of_continuous_comp e.symm.toLinearMap ?_
    intro p
    let r : Seminorm ℂ (SchwartzBruhat G) := p.val.comp e.symm.toLinearMap
    change Continuous r
    have hr (b : BruhatStructuralPair G) (d : ElementaryLCAPresentation b.quotient) :
        Continuous (fun f : SchwartzBruhatStage d ↦ r (schwartzBruhatStageInclusion b d f)) :=
      (hE.continuous_seminorm p).comp (hbwdStage b d)
    exact hB.continuous_seminorm (⟨r, hr⟩ : SchwartzSeminorms)

  let e' : E ≃L[ℂ] SchwartzBruhat G := ⟨e, hfwd, hbwd⟩
  refine ⟨e', ?_⟩
  intro f
  change (e f : G → ℂ) = modulationWeight m a f.val
  rfl

omit hm hms [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
/-- Evaluation on an elementary stage is bounded by the zeroth Schwartz seminorm. -/
private theorem elementarySchwartz_eval_continuousLinear {d t r : ℕ} {F : Type*}
    [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
    (x : ElementaryLieGroup d t r F) :
    ∃ L : ElementarySchwartz d t r F →L[ℂ] ℂ, ∀ f, L f = f x := by
  let L : ElementarySchwartz d t r F →ₗ[ℂ] ℂ :=
    (LinearMap.proj x).comp (elementarySchwartzSubmodule d t r F).subtype
  refine ⟨⟨L, (norm_withSeminorms ℂ ℂ).continuous_of_continuous_comp L fun _ ↦ ?_⟩, fun _ ↦ rfl⟩
  let i : ElementarySchwartzIndex d t r := (0, 0, 0, 0)
  apply Seminorm.continuous_of_le («E» := ElementarySchwartz d t r F)
    (q := elementarySchwartzSeminorm i)
    (elementarySchwartz_withSeminorms.continuous_seminorm i)
  intro f
  change (‖f.val x‖₊ : ENNReal).toReal ≤ (elementarySchwartzBound f.val i).toReal
  apply ENNReal.toReal_mono (f.property.2 i).ne
  rw [show i = (0, 0, 0, 0) from rfl, elementarySchwartzBound_zero]
  exact le_iSup (fun y ↦ (‖f.val y‖₊ : ENNReal)) x

omit hm hms [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
/-- Evaluation on Schwartz–Bruhat functions is continuous by the stage seminorms. -/
private theorem continuous_schwartzBruhat_eval_forEndpoints (x : G) :
    Continuous (fun f : SchwartzBruhat G ↦ f x) := by
  let L : SchwartzBruhat G →ₗ[ℂ] ℂ :=
    (LinearMap.proj x).comp (schwartzBruhatSubmodule G).subtype
  let p := (normSeminorm ℂ ℂ).comp L
  apply (norm_withSeminorms ℂ ℂ).continuous_of_continuous_comp L
  intro _
  change Continuous p
  refine (withGeneratingSeminorms_spec _ _).continuous_seminorm
    (⟨p, fun a e ↦ ?_⟩ : {p : Seminorm ℂ (schwartzBruhatSubmodule G) //
      ∀ (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient),
        Continuous (p ∘ schwartzBruhatStageInclusion a e)})
  classical
  let _ := e.finiteGroup
  let _ := e.finiteTopology
  let _ := e.finiteDiscrete
  let _ := e.finiteFintype
  by_cases hx : x ∈ a.val.1
  · obtain ⟨E, hE⟩ := elementarySchwartz_eval_continuousLinear
      (e.equiv (QuotientGroup.mk ⟨x, hx⟩)).toAdd
    exact E.continuous.norm.congr fun f ↦ by
      change ‖E f‖ = ‖schwartzBruhatStageRealization a e f x‖
      rw [hE, schwartzBruhatStageRealization_apply, dite_eq_left hx]
  · exact continuous_const.congr fun f ↦ by
      change (0 : ℝ) = ‖schwartzBruhatStageRealization a e f x‖
      rw [schwartzBruhatStageRealization_apply, dite_eq_right hx, norm_zero]

omit hm hms in
/-- A smooth multiplier of `log m` with bounded derivatives acts continuously
on Schwartz–Bruhat functions, by applying it on each elementary stage. -/
private theorem logModulation_mul_schwartzBruhat_continuousLinear {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hφb : ∀ j, ∃ C, ∀ t, ‖iteratedFDeriv ℝ j φ t‖ ≤ C) :
    ∃ M : SchwartzBruhat G →L[ℂ] SchwartzBruhat G,
      ∀ f x, M f x = φ (Real.log ((m x).val : ℝ)) * f x := by
  classical
  let w (x : G) := φ (Real.log ((m x).val : ℝ))
  let L : SchwartzBruhat G →ₗ[ℂ] SchwartzBruhat G :=
    ((LinearMap.mulLeft ℂ w).comp (schwartzBruhatSubmodule G).subtype).codRestrict
      (schwartzBruhatSubmodule G) (fun f ↦ logModulation_mul_mem_schwartzBruhat m hφ hφb f.property)
  refine ⟨⟨L, ?_⟩, fun _ _ ↦ rfl⟩
  let FinalSeminorms := {p : Seminorm ℂ (schwartzBruhatSubmodule G) //
    ∀ (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient),
      Continuous (p ∘ schwartzBruhatStageInclusion a e)}
  have generating := withGeneratingSeminorms_spec _ (Subtype.val : FinalSeminorms → _)
  apply generating.continuous_of_continuous_comp L
  intro p
  refine generating.continuous_seminorm (⟨p.val.comp L, fun a e ↦ ?_⟩ : FinalSeminorms)
  let _ := e.finiteGroup
  let _ := e.finiteTopology
  let _ := e.finiteDiscrete
  let _ := e.finiteFintype
  let X := SchwartzBruhatStage e
  let Y := ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor
  let R := schwartzBruhatStageRealization a e
  -- Each elementary coordinate can be evaluated at a representative in the open subgroup.
  have hrep (y : Y) : ∃ x : a.val.1, (e.equiv (QuotientGroup.mk x)).toAdd = y := by
    obtain ⟨q, hq⟩ := e.equiv.surjective (Multiplicative.ofAdd y)
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨x, congrArg Multiplicative.toAdd hq⟩
  choose x hx using hrep
  have heval (f : X) (y : Y) : R f (x y).val = f y := by
    rw [schwartzBruhatStageRealization_apply, dite_eq_left (x y).property, hx]
  choose s hs using fun f : X ↦ stage_mul_logModulation m a e f hφ hφb
  have hmul (f : X) (y : Y) : s f y = w (x y).val * f y := by
    calc
      _ = R (s f) (x y).val := (heval (s f) y).symm
      _ = w (x y).val * R f (x y).val := congrFun (hs f) _
      _ = _ := congrArg (w (x y).val * ·) (heval f y)
  let A : X →ₗ[ℂ] X :=
    { toFun := s
      map_add' := fun f g ↦ Subtype.ext (funext fun y ↦ by
        change s (f + g) y = s f y + s g y
        rw [hmul, hmul, hmul]
        exact mul_add _ _ _)
      map_smul' := fun c f ↦ Subtype.ext (funext fun y ↦ by
        change s (c • f) y = c * s f y
        rw [hmul, hmul]
        exact mul_left_comm _ _ _) }
  let _ : BarrelledSpace ℂ X := elementarySchwartz_barrelled
  let _ : ContinuousSMul ℂ X := elementarySchwartz_withSeminorms.continuousSMul
  have hA : Continuous A := by
    apply continuous_toElementarySchwartz_of_eval
    intro y
    obtain ⟨E, hE⟩ := elementarySchwartz_eval_continuousLinear y
    exact ⟨w (x y).val • E, fun f ↦ by
      change w (x y).val * E f = s f y
      rw [hE, hmul]⟩
  exact ((p.property a e).comp hA).congr fun f ↦ congrArg p.val (Subtype.ext (hs f))

omit hm hms in
/-- Every twist in a closed interval is recovered continuously from the two endpoint twists. -/
private theorem modulationWeight_between_continuous (a c b : ℝ) (hac : a ≤ c) (hcb : c ≤ b) :
    ∃ F : SchwartzBruhat G × SchwartzBruhat G →L[ℂ] SchwartzBruhat G,
      ∀ (f : G → ℂ) (p : SchwartzBruhat G × SchwartzBruhat G),
        p.1.val = modulationWeight m a f → p.2.val = modulationWeight m b f →
        (F p).val = modulationWeight m c f := by
  let φ (t : ℝ) : ℂ :=
    ((Real.exp (-(c - a) * t) + Real.exp ((b - c) * t))⁻¹ : ℝ)
  have hφ : ContDiff ℝ ∞ φ ∧ ∀ j, ∃ C, ∀ t, ‖iteratedFDeriv ℝ j φ t‖ ≤ C :=
    twoSidedExpWeight_bounds_of_nonneg (sub_nonneg.mpr hac) (sub_nonneg.mpr hcb)
  have hmul := logModulation_mul_schwartzBruhat_continuousLinear m hφ.1 hφ.2
  let M := hmul.choose
  have hM := hmul.choose_spec
  let fst := ContinuousLinearMap.fst ℂ (SchwartzBruhat G) (SchwartzBruhat G)
  let snd := ContinuousLinearMap.snd ℂ (SchwartzBruhat G) (SchwartzBruhat G)
  refine ⟨M.comp (fst + snd), ?_⟩
  intro f p ha hb
  change (M (p.1 + p.2)).val = modulationWeight m c f
  funext x
  have hsum : (p.1 + p.2).val = modulationWeight m a f + modulationWeight m b f :=
    congrArg₂ (fun u v : G → ℂ ↦ u + v) ha hb
  calc
    _ = φ (Real.log ((m x).val : ℝ)) * (p.1 + p.2).val x := hM (p.1 + p.2) x
    _ = φ (Real.log ((m x).val : ℝ)) * (modulationWeight m a f + modulationWeight m b f) x :=
      congrArg (fun g : G → ℂ ↦ φ (Real.log ((m x).val : ℝ)) * g x) hsum
    _ = _ := (congrFun (modulationWeight_between_eq m f a c b) x).symm

-- Keep the modulation hypotheses in the existing signature.
set_option linter.unusedSectionVars false in
/-- Paper: Example D.3.3.5, p. 805. The diagonal map from a stage over a
compact interval to the two endpoint stages is a closed topological embedding. -/
theorem modulatedExponentialDecayStage_endpoints_closedEmbedding (k : GoodCompact)
    (a b : ℝ) (hab : a ≤ b) :
    ∃ T : ModulatedExponentialDecayStage m (Icc a b) k →L[ℂ]
        ModulatedExponentialDecayStage m {a} k × ModulatedExponentialDecayStage m {b} k,
      IsClosedEmbedding T ∧ ∀ f, (T f).1.val = f.val ∧ (T f).2.val = f.val := by
  let Q := G ⧸ k.val
  let n := quotientModulation m k.val k.property.1
  let _ : IsClosed (k.val : Set G) := k.property.1.isClosed
  let X (J : Set ℝ) := ModulatedExponentialDecayStage m J k
  let twist (J : Set ℝ) (c : J) : X J →L[ℂ] SchwartzBruhat Q :=
    ⟨modulatedExponentialDecayTwist n J c,
      (continuous_apply c).comp (modulatedDecayStage_twists_isInducing m J k).continuous⟩
  let restrict (J K : Set ℝ) (h : K ⊆ J) : X J →L[ℂ] X K := by
    let R : X J →ₗ[ℂ] X K :=
      (modulatedExponentialDecaySubmodule n J).subtype.codRestrict
        (modulatedExponentialDecaySubmodule n K) fun f ↦
          (Submodule.mem_iInf _).mpr fun c ↦ Submodule.mem_comap.mpr
            (modulationWeight_mem_schwartzBruhat n J ⟨c, h c.property⟩ f)
    refine ⟨R, (modulatedDecayStage_twists_isInducing m K k).continuous_iff.mpr ?_⟩
    exact continuous_pi fun c ↦ (twist J ⟨c, h c.property⟩).continuous
  let T : X (Icc a b) →L[ℂ] X {a} × X {b} :=
    (restrict _ _ (singleton_subset_iff.mpr (left_mem_Icc.mpr hab))).prod
      (restrict _ _ (singleton_subset_iff.mpr (right_mem_Icc.mpr hab)))
  let A : X {a} →L[ℂ] SchwartzBruhat Q := twist {a} ⟨a, rfl⟩
  let B : X {b} →L[ℂ] SchwartzBruhat Q := twist {b} ⟨b, rfl⟩
  let endpoints : X {a} × X {b} →L[ℂ] SchwartzBruhat Q × SchwartzBruhat Q :=
    (A.comp (ContinuousLinearMap.fst ℂ _ _)).prod (B.comp (ContinuousLinearMap.snd ℂ _ _))
  have hfactor (c : Icc a b) :
      ∃ F : X {a} × X {b} →L[ℂ] SchwartzBruhat Q,
        ∀ p, p.1.val = p.2.val → (F p).val = modulationWeight n c p.1.val := by
    have hW := modulationWeight_between_continuous n a c b
      c.property.1 c.property.2
    exact ⟨hW.choose.comp endpoints, fun p h ↦ hW.choose_spec p.1.val (A p.1, B p.2) rfl
      (congrArg (modulationWeight n b) h.symm)⟩
  let F (c : Icc a b) := (hfactor c).choose
  have hFT (c : Icc a b) := (hfactor c).choose_spec
  have hT : IsInducing T := by
    let U (p : X {a} × X {b}) (c : Icc a b) := F c p
    have hU : Continuous U := continuous_pi fun c ↦ (F c).continuous
    have hcomp : U ∘ (T : X (Icc a b) → X {a} × X {b}) =
        fun f c ↦ modulatedExponentialDecayTwist n (Icc a b) c f := by
      funext f c
      exact Subtype.ext (hFT c (T f) rfl)
    refine IsInducing.of_comp (f := T) (g := U) T.continuous hU ?_
    exact (congrArg (fun g : X (Icc a b) → (Icc a b → SchwartzBruhat Q) ↦ IsInducing g)
      hcomp).mpr (modulatedDecayStage_twists_isInducing m (Icc a b) k)
  have heval (d : ℝ) (x : Q) : Continuous (fun f : X {d} ↦ f.val x) := by
    let w : ℂ := (((n x).val : ℝ) ^ d : ℝ)
    have hw : w ≠ 0 := Complex.ofReal_ne_zero.mpr
      (Real.rpow_pos_of_pos (NNReal.coe_pos.mpr (Units.zero_lt (n x))) d).ne'
    have h := (continuous_schwartzBruhat_eval_forEndpoints x).comp (twist {d} ⟨d, rfl⟩).continuous
    exact ((continuous_const (y := w⁻¹)).mul h).congr fun f ↦ by
      change w⁻¹ * (w * f.val x) = f.val x
      rw [← mul_assoc, inv_mul_cancel₀ hw, one_mul]
  have hrange : range T = ⋂ x : Q, {p : X {a} × X {b} | p.1.val x = p.2.val x} := by
    refine Set.ext fun p ↦ ⟨?_, ?_⟩
    · intro hp
      refine mem_iInter.mpr fun x ↦ ?_
      refine Exists.elim hp fun f hf ↦ ?_
      exact (congrArg (fun q : X {a} × X {b} ↦ q.1.val x = q.2.val x) hf).mp rfl
    · intro hp
      have heq : p.1.val = p.2.val := funext fun x ↦ mem_iInter.mp hp x
      have hf : p.1.val ∈ modulatedExponentialDecaySubmodule n (Icc a b) := by
        refine (Submodule.mem_iInf _).mpr fun c ↦ Submodule.mem_comap.mpr ?_
        exact (congrArg (fun g : Q → ℂ ↦ g ∈ schwartzBruhatSubmodule Q) (hFT c p heq)).mp
          (F c p).property
      exact ⟨⟨p.1.val, hf⟩, Prod.ext (Subtype.ext rfl) (Subtype.ext heq)⟩
  have hinj : Injective T := fun _ _ h ↦
    Subtype.ext (congrArg (fun p : X {a} × X {b} ↦ p.1.val) h)
  have hclosed : IsClosed (⋂ x : Q, {p : X {a} × X {b} | p.1.val x = p.2.val x}) := by
    have hfst : Continuous (Prod.fst : X {a} × X {b} → X {a}) := continuous_fst
    have hsnd : Continuous (Prod.snd : X {a} × X {b} → X {b}) := continuous_snd
    exact isClosed_iInter fun x ↦ isClosed_eq ((heval a x).comp hfst) ((heval b x).comp hsnd)
  have hclosedRange : IsClosed (range T) :=
    (congrArg (fun s : Set (X {a} × X {b}) ↦ IsClosed s) hrange).mpr hclosed
  exact ⟨T, ⟨⟨hT, hinj⟩, hclosedRange⟩, fun _ ↦ ⟨rfl, rfl⟩⟩

/-- A proper surjective modulation pulls a compact generating neighborhood back to one. -/
private theorem compactlyGenerated_of_surjective_modulation : IsCompactlyGeneratedGroup G := by
  have : ConnectedSpace (Multiplicative ℝ) := inferInstanceAs (ConnectedSpace ℝ)
  have : ConnectedSpace ℝ≥0ˣ := positiveRealLogEquiv.symm.toHomeomorph.surjective.connectedSpace
    positiveRealLogEquiv.symm.continuous
  obtain ⟨U, hUc, hU⟩ := exists_compact_mem_nhds (1 : ℝ≥0ˣ)
  have hopen : IsOpen (Subgroup.closure U : Set ℝ≥0ˣ) :=
    Subgroup.isOpen_of_mem_nhds _ (mem_of_superset hU Subgroup.subset_closure)
  have hgen : Subgroup.closure U = ⊤ := SetLike.coe_injective
    ((OpenSubgroup.isClopen ⟨Subgroup.closure U, hopen⟩).eq_univ ⟨1, Subgroup.one_mem _⟩)
  have hpre : m ⁻¹' U ∈ 𝓝 (1 : G) :=
    m.continuous.continuousAt.preimage_mem_nhds (show U ∈ 𝓝 (m 1) by rwa [map_one])
  refine ⟨m ⁻¹' U, hpre, hm.1.isCompact_preimage hUc, ?_⟩
  have hker : m.toMonoidHom.ker ≤ Subgroup.closure (m ⁻¹' U) := by
    intro g hg
    apply Subgroup.subset_closure
    change m g ∈ U
    rw [show m g = 1 from hg]
    exact mem_of_mem_nhds hU
  rw [← Subgroup.comap_map_eq_self hker, MonoidHom.map_closure]
  change Subgroup.comap m.toMonoidHom (Subgroup.closure (m '' (m ⁻¹' U))) = ⊤
  rw [hms.image_preimage, hgen, Subgroup.comap_top]

/-- The Schwartz–Bruhat space of an elementary compact quotient is metrizable via
the Schwartz space of its largest structural pair. -/
private theorem modulatedDecayStage_schwartzBruhat_metrizable (k : GoodCompact) :
    MetrizableSpace (SchwartzBruhat (G ⧸ k.val)) := by
  let Q := G ⧸ k.val
  let _ : IsClosed (k.val : Set G) := k.property.1.isClosed
  have hgen : IsCompactlyGeneratedGroup Q :=
    isCompactlyGeneratedGroup_quotient (compactlyGenerated_of_surjective_modulation m hm hms)
      k.val k.property.1.isClosed
  let d : PontryaginDual (G ⧸ k.val) ≃ₜ* lcaAnnihilator k.val :=
    (lcaQuotientDual_equiv_annihilator k.val k.property.1.isClosed).choose
  have hdual : IsCompactlyGeneratedGroup (PontryaginDual (G ⧸ k.val)) :=
    isCompactlyGeneratedGroup_of_continuousMulEquiv d.symm k.property.2
  have hlocal : IsLocallyEuclidean (G ⧸ k.val) :=
    isLocallyEuclidean_of_isCompactlyGeneratedGroup_dual hdual
  let e := Classical.choice ((lca_elementary_iff (G := Q)).mp ⟨hgen, hlocal⟩)
  let _ := e.finiteGroup
  let _ := e.finiteTopology
  let _ := e.finiteDiscrete
  let _ := e.finiteFintype
  have : SecondCountableTopology Q := e.equiv.toHomeomorph.isEmbedding.secondCountableTopology
  let top : (⊤ : Subgroup Q) ≃ₜ* Q :=
    { Subgroup.topEquiv with
      continuous_toFun := continuous_subtype_val
      continuous_invFun := continuous_id.subtype_mk _ }
  let a : BruhatStructuralPair Q := ⟨(⊤, OrderDual.toDual ⊥), isOpen_univ,
    isCompactlyGeneratedGroup_of_continuousMulEquiv top.symm hgen,
    isBruhatGoodSubgroup_bot_iff.mpr hlocal, bot_le⟩
  let p := Classical.choice a.elementary
  have ha (b : BruhatStructuralPair Q) : b ≤ a := by
    change b.val.1 ≤ ⊤ ∧ (⊥ : Subgroup Q) ≤ OrderDual.ofDual b.val.2
    exact ⟨le_top, bot_le⟩
  let J : SchwartzBruhatStage p →ₗ[ℂ] SchwartzBruhat Q := schwartzBruhatStageInclusion a p
  have hJ : IsEmbedding J := schwartzBruhatStage_isEmbedding a p
  have hsurj : Surjective J := schwartzBruhat_maxStage_surjective a ha p
  let E : SchwartzBruhatStage p ≃ₜ SchwartzBruhat Q :=
    (Equiv.ofBijective J ⟨hJ.injective, hsurj⟩).toHomeomorphOfIsInducing hJ.isInducing
  let _ := p.finiteGroup
  let _ := p.finiteTopology
  let _ := p.finiteDiscrete
  let _ := p.finiteFintype
  have hF : IsFrechetTVS (SchwartzBruhatStage p) :=
    elementarySchwartz_isFrechet (m := p.realDim) (n := p.torusDim) (r := p.latticeRank)
      (F := p.finiteFactor)
  let _ : MetrizableSpace (SchwartzBruhatStage p) := hF.choose_spec.2.1
  exact E.symm.isEmbedding.metrizableSpace

omit hm hms in
/-- A countable bracketing family of exponents embeds a decay stage as the closed
space of compatible Schwartz–Bruhat twists. -/
private theorem modulatedDecayStage_countable_closedEmbedding (I : Set ℝ) (hInt : OrdConnected I)
    (hne : I.Nonempty) (k : GoodCompact) :
    ∃ T : ModulatedExponentialDecayStage m I k →ₗ[ℂ] (ℕ ⊕ ℕ → SchwartzBruhat (G ⧸ k.val)),
      IsClosedEmbedding T := by
  let Q := G ⧸ k.val
  let _ : IsClosed (k.val : Set G) := k.property.1.isClosed
  let n := quotientModulation m k.val k.property.1
  let X := ModulatedExponentialDecayStage m I k
  let S := SchwartzBruhat Q
  let J := ℕ ⊕ ℕ
  let Y := J → S
  have : Nonempty I := hne.to_subtype
  let _ : OrderTopology I := orderTopology_of_ordConnected (ht := hInt)
  let lo := (exists_seq_antitone_tendsto_atTop_atBot I).choose
  let hi := (exists_seq_monotone_tendsto_atTop_atTop I).choose
  have hlo : Tendsto lo atTop atBot := (exists_seq_antitone_tendsto_atTop_atBot I).choose_spec.2
  have hhi : Tendsto hi atTop atTop := (exists_seq_monotone_tendsto_atTop_atTop I).choose_spec.2
  let d : J → I := Sum.elim lo hi
  let T : X →ₗ[ℂ] Y := LinearMap.pi fun j ↦ modulatedExponentialDecayTwist n I (d j)
  have hfactor (a : I) : ∃ F : Y →L[ℂ] S, ∀ (g : Y) (f : Q → ℂ),
      (∀ j, (g j).val = modulationWeight n (d j) f) →
        (F g).val = modulationWeight n a f := by
    let left := (hlo.eventually (eventually_le_atBot a)).exists
    let right := (hhi.eventually (eventually_ge_atTop a)).exists
    let l := left.choose
    let r := right.choose
    let interpolate := modulationWeight_between_continuous n (lo l) a (hi r)
      left.choose_spec right.choose_spec
    let F := interpolate.choose
    have hF := interpolate.choose_spec
    let L : Y →L[ℂ] S := ContinuousLinearMap.proj (R := ℂ) (Sum.inl l)
    let R : Y →L[ℂ] S := ContinuousLinearMap.proj (R := ℂ) (Sum.inr r)
    exact ⟨F.comp (L.prod R), fun g f hg ↦ hF f (L g, R g) (hg (.inl l)) (hg (.inr r))⟩
  let F (a : I) : Y →L[ℂ] S := (hfactor a).choose
  have hF (a : I) := (hfactor a).choose_spec
  let V (f : X) (a : I) : S := modulatedExponentialDecayTwist n I a f
  have hall : IsInducing V := modulatedDecayStage_twists_isInducing m I k
  have hT : IsInducing T := by
    have hcont : Continuous T := continuous_pi fun j ↦
      (continuous_apply (d j)).comp hall.continuous
    let U (g : Y) (a : I) : S := F a g
    have hU : Continuous U := continuous_pi fun a ↦ (F a).continuous
    have hcomp : U ∘ (T : X → Y) = V := by
      funext f a
      exact Subtype.ext (hF a (T f) f.val fun _ ↦ rfl)
    have hUV : IsInducing (U ∘ (T : X → Y)) :=
      (congrArg (fun g : X → (I → S) ↦ IsInducing g) hcomp).mpr hall
    exact IsInducing.of_comp (f := (T : X → Y)) (g := U) hcont hU hUV
  let w (a : I) (x : Q) : ℂ := (((n x).val : ℝ) ^ (a : ℝ) : ℝ)
  have hw (a : I) (x : Q) : w a x ≠ 0 := Complex.ofReal_ne_zero.mpr
    (Real.rpow_pos_of_pos (NNReal.coe_pos.mpr (Units.zero_lt (n x))) _).ne'
  let unweight (j : J) (g : Y) (x : Q) : ℂ := g j x / w (d j) x
  have hunw (j : J) (f : X) (x : Q) : unweight j (T f) x = f.val x := by
    change w (d j) x * f.val x / w (d j) x = f.val x
    exact (div_eq_iff (hw (d j) x)).mpr (mul_comm _ _)
  let j₀ : J := .inl 0
  have hinj : Injective T := by
    intro f g h
    exact Subtype.ext (funext fun x ↦
      (hunw j₀ f x).symm.trans ((congrArg (fun z ↦ unweight j₀ z x) h).trans (hunw j₀ g x)))
  have hrange : range T = ⋂ (j : J) (x : Q), {g : Y | unweight j g x = unweight j₀ g x} := by
    refine Set.ext fun g ↦ ⟨?_, ?_⟩
    · rintro ⟨f, rfl⟩
      exact mem_iInter.mpr fun j ↦ mem_iInter.mpr fun x ↦
        (hunw j f x).trans (hunw j₀ f x).symm
    · intro hg
      let f := unweight j₀ g
      have hmatch (j : J) : (g j).val = modulationWeight n (d j) f := by
        funext x
        have hx : unweight j g x = f x := mem_iInter.mp (mem_iInter.mp hg j) x
        change g j x = w (d j) x * f x
        exact ((div_eq_iff (hw (d j) x)).mp hx).trans (mul_comm _ _)
      have hf : f ∈ modulatedExponentialDecaySubmodule n I := by
        refine (Submodule.mem_iInf _).mpr fun a ↦ Submodule.mem_comap.mpr ?_
        have heq := hF a g f hmatch
        exact (congrArg (fun u : Q → ℂ ↦ u ∈ schwartzBruhatSubmodule Q) heq).mp
          (F a g).property
      refine ⟨⟨f, hf⟩, ?_⟩
      funext j
      apply Subtype.ext
      exact (hmatch j).symm
  have heval (x : Q) : Continuous (fun s : S ↦ s x) :=
    continuous_schwartzBruhat_eval_forEndpoints x
  have hproj (j : J) : Continuous (fun g : Y ↦ g j) := continuous_apply j
  have hc (j : J) (x : Q) : Continuous (fun g : Y ↦ unweight j g x) :=
    ((heval x).comp (hproj j)).div_const (w (d j) x)
  have hclosed : IsClosed (⋂ (j : J) (x : Q), {g : Y | unweight j g x = unweight j₀ g x}) :=
    isClosed_iInter fun j ↦ isClosed_iInter fun x ↦ isClosed_eq (hc j x) (hc j₀ x)
  have hclosedRange : IsClosed (range T) :=
    (congrArg (fun s : Set Y ↦ IsClosed s) hrange).mpr hclosed
  exact ⟨T, ⟨⟨hT, hinj⟩, hclosedRange⟩⟩

omit hm hms in
/-- A closed linear embedding into a countable product of complete metrizable
additive uniform spaces gives a Fréchet space. -/
private theorem isFrechetTVS_of_closedLinearEmbedding_pi {ι X S : Type*} [Countable ι]
    [AddCommGroup X] [Module ℂ X] [UniformSpace X] [IsUniformAddGroup X]
    [PolynormableSpace ℂ X] [AddCommGroup S] [Module ℂ S] [UniformSpace S]
    [IsUniformAddGroup S] (hS : CompleteSpace S) (hM : MetrizableSpace S)
    (T : X →ₗ[ℂ] (ι → S)) (hT : IsClosedEmbedding T) : IsFrechetTVS X := by
  let _ : CompleteSpace S := hS
  let _ : MetrizableSpace S := hM
  have : (uniformity S).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  have : MetrizableSpace (ι → S) := UniformSpace.metrizableSpace
  have hU : IsUniformInducing T :=
    AddMonoidHom.isUniformInducing_of_isInducing (f := T.toAddMonoidHom) hT.isInducing
  refine ⟨inferInstance, inferInstance, hT.isEmbedding.metrizableSpace, ?_⟩
  rw [IsUniformAddGroup.rightUniformSpace_eq (G := X)]
  exact hU.completeSpace hT.isClosed_range.isComplete

/-- Paper: Example D.3.3.5, p. 805. For a nonempty interval, each stage is Fréchet. -/
theorem modulatedExponentialDecayStage_frechet (I : Set ℝ) (hInt : OrdConnected I)
    (hne : I.Nonempty) (k : GoodCompact) :
    IsFrechetTVS (ModulatedExponentialDecayStage m I k) := by
  let _ : IsClosed (k.val : Set G) := k.property.1.isClosed
  let X := ModulatedExponentialDecayStage m I k
  let S := SchwartzBruhat (G ⧸ k.val)
  have hS : CompleteSpace S := schwartzBruhat_complete
  have hM : MetrizableSpace S := modulatedDecayStage_schwartzBruhat_metrizable m hm hms k
  have h := modulatedDecayStage_countable_closedEmbedding m I hInt hne k
  exact isFrechetTVS_of_closedLinearEmbedding_pi (X := X) (S := S) hS hM h.choose h.choose_spec

omit hms in
/-- The quotient underlying a decay stage is second countable. Properness gives
σ-compactness, and compact generation of the dual gives Euclidean charts. -/
private theorem modulatedDecayStage_quotient_secondCountable (k : GoodCompact) :
    SecondCountableTopology (G ⧸ k.val) := by
  let Q := G ⧸ k.val
  let : IsClosed (k.val : Set G) := k.property.1.isClosed
  have : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  have : SigmaCompactSpace G :=
    ⟨⟨fun j ↦ m ⁻¹' compactCovering ℝ≥0ˣ j,
      fun j ↦ hm.1.isCompact_preimage (isCompact_compactCovering _ j), by
        rw [← preimage_iUnion, iUnion_compactCovering, preimage_univ]⟩⟩
  let q : G → Q := QuotientGroup.mk
  have hq : Surjective q := QuotientGroup.mk_surjective
  have : SigmaCompactSpace Q :=
    isSigmaCompact_univ_iff.mp (hq.range_eq ▸
      isSigmaCompact_range (show Continuous q from QuotientGroup.continuous_mk))
  obtain ⟨e, _⟩ := lcaQuotientDual_equiv_annihilator (G := G) k.val k.property.1.isClosed
  have hDual : IsCompactlyGeneratedGroup (PontryaginDual Q) :=
    isCompactlyGeneratedGroup_of_continuousMulEquiv e.symm k.property.2
  obtain ⟨d, ⟨charts⟩⟩ := isLocallyEuclidean_of_isCompactlyGeneratedGroup_dual (G := Q) hDual
  let : ChartedSpace (EuclideanSpace ℝ (Fin d)) Q := charts
  exact ChartedSpace.secondCountable_of_sigmaCompact (EuclideanSpace ℝ (Fin d)) Q

-- The proof uses properness of the modulation and nonemptiness of the exponent set.
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
/-- Paper: Example D.3.3.5, p. 805. For a nonempty interval, each stage is nuclear. -/
theorem modulatedExponentialDecayStage_nuclear (I : Set ℝ) (hInt : OrdConnected I)
    (hne : I.Nonempty) (k : GoodCompact) :
    IsNuclearTVS (ModulatedExponentialDecayStage m I k) := by
  let Q := G ⧸ k.val
  let n := quotientModulation m k.val k.property.1
  let : IsClosed (k.val : Set G) := k.property.1.isClosed
  have : SecondCountableTopology Q := modulatedDecayStage_quotient_secondCountable m hm k
  let T : ModulatedExponentialDecayStage m I k →ₗ[ℂ] (I → SchwartzBruhat Q) :=
    LinearMap.pi (modulatedExponentialDecayTwist n I)
  have hT : IsEmbedding T := by
    refine ⟨modulatedDecayStage_twists_isInducing m I k, ?_⟩
    let a : I := ⟨hne.choose, hne.choose_spec⟩
    intro f g h
    apply Subtype.ext
    funext x
    have hx := congrArg (fun p : I → SchwartzBruhat Q ↦ p a x) h
    let w : ℂ := (((n x).val : ℝ) ^ (a : ℝ) : ℝ)
    have hw : w ≠ 0 := Complex.ofReal_ne_zero.mpr
      (Real.rpow_pos_of_pos (NNReal.coe_pos.mpr (Units.zero_lt (n x))) (a : ℝ)).ne'
    exact mul_left_cancel₀ hw (show w * f.val x = w * g.val x from hx)
  exact isNuclearTVS_of_linearEmbedding T hT
    (isNuclearTVS_pi fun _ : I ↦ schwartzBruhat_nuclear (G := Q))

omit hm hms in
/-- A first-countable Schwartz space is separable. For each continuous seminorm a
totally bounded zero-neighborhood spans the space, so the space is separable for that
seminorm, and countably many seminorm balls form a basis at zero. -/
private theorem separableSpace_of_isSchwartzTVS_firstCountable {E : Type*} [AddCommGroup E]
    [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E] [FirstCountableTopology E]
    (hE : IsSchwartzTVS E) : SeparableSpace E := by
  let _ : PolynormableSpace ℂ E := hE.1
  have hsep (p : Seminorm ℂ E) (hp : Continuous p) : SeparableSpace (WithLocalSeminorm p) := by
    obtain ⟨V, hV, htot⟩ := hE.2 p hp
    let W : Set (WithLocalSeminorm p) := V
    have hW : TotallyBounded W := htot
    have hAbs : Absorbent ℂ W := by
      change Absorbent ℂ V
      exact absorbent_nhds_zero (𝕜 := ℂ) hV
    have hspan : Submodule.span ℂ W = ⊤ :=
      (hAbs.mono (Submodule.subset_span (R := ℂ))).submodule_eq_top
    have hS := hW.isSeparable.span (R := ℂ)
    rw [hspan, Submodule.top_coe] at hS
    exact isSeparable_univ_iff.mp hS
  obtain ⟨q, hq, hbasis⟩ :=
    (PolynormableSpace.hasBasis_zero_ball ℂ E).exists_antitone_subbasis
  have (n : ℕ) : SeparableSpace (WithLocalSeminorm (q n)) := hsep (q n) (hq n)
  choose u hu using fun n ↦ exists_dense_seq (WithLocalSeminorm (q n))
  refine ⟨⟨⋃ n, range (u n), countable_iUnion fun n ↦ countable_range _, fun x ↦ ?_⟩⟩
  refine mem_closure_iff_nhds.mpr fun t ht ↦ ?_
  rw [← map_add_left_nhds_zero x, Filter.mem_map] at ht
  obtain ⟨n, -, hn⟩ := hbasis.toHasBasis.mem_iff.mp ht
  let y : WithLocalSeminorm (q n) := x
  obtain ⟨j, hj⟩ := (hu n).exists_mem_open (s := Metric.ball y 1) Metric.isOpen_ball
    ⟨y, Metric.mem_ball_self one_pos⟩
  let v : E := u n j
  refine ⟨v, ?_, mem_iUnion.mpr ⟨n, mem_range_self j⟩⟩
  have hmem : v - x ∈ (q n).ball 0 1 := by
    rw [Seminorm.mem_ball_zero]
    rw [Metric.mem_ball, dist_eq_norm] at hj
    exact hj
  simpa using hn hmem

omit hm hms in
/-- A decay stage is separable once the quotient is second countable, its
Schwartz–Bruhat space is metrizable, and the stage embeds in a countable power of it. -/
private theorem modulatedDecayStage_separable_of_embedding (I : Set ℝ) (k : GoodCompact)
    (hQ : SecondCountableTopology (G ⧸ k.val))
    (hM : MetrizableSpace (SchwartzBruhat (G ⧸ k.val)))
    (hE : ∃ T : ModulatedExponentialDecayStage m I k →ₗ[ℂ] (ℕ ⊕ ℕ → SchwartzBruhat (G ⧸ k.val)),
      IsClosedEmbedding T) :
    SeparableSpace (ModulatedExponentialDecayStage m I k) := by
  let Q := G ⧸ k.val
  let _ : IsClosed (k.val : Set G) := k.property.1.isClosed
  let S := SchwartzBruhat Q
  have : SecondCountableTopology Q := hQ
  have : MetrizableSpace S := hM
  have hN : IsNuclearTVS.{0} S := schwartzBruhat_nuclear
  have : SeparableSpace S :=
    separableSpace_of_isSchwartzTVS_firstCountable (isSchwartzTVS_of_isNuclearTVS hN)
  have : SecondCountableTopology (univ : Set S) :=
    (isSeparable_univ_iff.mpr ‹SeparableSpace S›).secondCountableTopology
  have : SecondCountableTopology S :=
    (Homeomorph.Set.univ S).symm.isEmbedding.secondCountableTopology
  obtain ⟨T, hT⟩ := hE
  have := hT.isEmbedding.secondCountableTopology
  infer_instance

/-- Paper: Example D.3.3.5, p. 805. For a nonempty interval, each stage is separable. -/
theorem modulatedExponentialDecayStage_separable (I : Set ℝ) (hInt : OrdConnected I)
    (hne : I.Nonempty) (k : GoodCompact) :
    SeparableSpace (ModulatedExponentialDecayStage m I k) :=
  modulatedDecayStage_separable_of_embedding m I k
    (modulatedDecayStage_quotient_secondCountable m hm k)
    (modulatedDecayStage_schwartzBruhat_metrizable m hm hms k)
    (modulatedDecayStage_countable_closedEmbedding m I hInt hne k)

end ModulatedExamples

-- The remaining part starts with the transition maps at the end of Example
-- D.3.3.5, p. 805.
-- TODO(paper-gap): Proposition D.3.3.10(3) misses included endpoints when
-- J only accumulates at them. On [0,1], translates of a fixed smooth bump
-- centered at n and scaled by exp(-n) are bounded at every a < 1, while the
-- a = 1 twists have an unbounded first polynomial Schwartz seminorm.
-- TODO(paper-gap): In Theorem D.3.3.13 the tensor formula requires the
-- Haar measures on the group and compact factor to be chosen compatibly.

end RiemannMasullo
