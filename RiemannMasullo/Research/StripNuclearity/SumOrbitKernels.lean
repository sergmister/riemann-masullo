module

public import RiemannMasullo.Ch09_HardySobolev.Sec3
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Summing kernels of a continuous representation on a fixed compact set -/

@[expose] public noncomputable section

open Filter Function MeasureTheory Set
open scoped Topology

namespace RiemannMasullo.StripNuclearity

/-- If kernels reconstruct a test pointwise on a common compact support and
have a summable sequence of uniform bounds, their orbit integrals reconstruct
the test action in operator norm. Only joint continuity of the action is needed. -/
theorem hasSum_orbit_operators_of_compact_support
    {G E ι : Type*} [TopologicalSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] [Countable ι]
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (ρ : G → E →L[ℂ] E)
    (hρ : Continuous (fun q : G × E ↦ ρ q.1 q.2))
    {J : Set G} (hJ : IsCompact J) (f : G → ℂ) (q : ι → G → ℂ) (c : ι → ℝ)
    (hc : Summable c) (hpos : ∀ i, 0 ≤ c i) (hq : ∀ i, Continuous (q i))
    (hsupp : ∀ i, tsupport (q i) ⊆ J) (hbound : ∀ i x, ‖q i x‖ ≤ c i)
    (hsum : ∀ x, HasSum (fun i ↦ q i x) (f x))
    (T : E →L[ℂ] E) (B : ι → E →L[ℂ] E)
    (hT : ∀ u, T u = ∫ x, f x • ρ x u ∂μ)
    (hB : ∀ i u, B i u = ∫ x, q i x • ρ x u ∂μ) :
    HasSum B T := by
  classical
  obtain ⟨M, hM⟩ := banach_steinhaus (g := fun x : J ↦ ρ x.val) fun u ↦ by
    obtain ⟨M, hM⟩ := hJ.exists_bound_of_continuousOn (hρ.comp (Continuous.prodMk_left u)).continuousOn
    exact ⟨M, fun x ↦ hM x.val x.property⟩
  let C := max M 0
  have hC : 0 ≤ C := le_max_right _ _
  let V := μ.real J
  have hV : 0 ≤ V := measureReal_nonneg
  let H (i : ι) (u : E) (x : G) := q i x • ρ x u
  have hvan (i : ι) (u : E) {x : G} (hx : x ∉ J) : H i u x = 0 := by
    simp [H, image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hsupp i h))]
  have hi (i : ι) (u : E) : Integrable (H i u) μ := by
    have hcont := (hq i).smul (hρ.comp (Continuous.prodMk_left u))
    apply hcont.integrable_of_hasCompactSupport
    apply hJ.of_isClosed_subset isClosed_closure
    exact closure_minimal (fun x hx ↦ by_contra fun h ↦ hx (hvan i u h)) hJ.isClosed
  have hb (i : ι) (u : E) : (∫ x, ‖H i u x‖ ∂μ) ≤ c i * (C * V) * ‖u‖ := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := J)
      (f := fun x ↦ ‖H i u x‖) (fun x hx ↦ by rw [hvan i u hx, norm_zero])]
    calc
      _ ≤ ∫ _ in J, c i * (C * ‖u‖) ∂μ := by
        apply setIntegral_mono_on (hi i u).norm.integrableOn (integrableOn_const hJ.measure_lt_top.ne) hJ.measurableSet
        intro x hx
        rw [show ‖H i u x‖ = ‖q i x‖ * ‖ρ x u‖ from norm_smul _ _]
        exact mul_le_mul (hbound i x) (((ρ x).le_opNorm u).trans
          (mul_le_mul_of_nonneg_right ((hM ⟨x,hx⟩).trans (le_max_left _ _)) (norm_nonneg _)))
          (norm_nonneg _) (hpos i)
      _ = _ := by rw [setIntegral_const]; change V * _ = _; ring
  have hsumB : Summable B := .of_norm_bounded (hc.mul_right (C*V)) fun i ↦ by
    apply (B i).opNorm_le_bound (by positivity [hpos i])
    intro u
    rw [hB]
    exact (norm_integral_le_integral_norm _).trans (hb i u)
  have heq : ∑' i, B i = T := by
    ext u : 1
    let ev := ContinuousLinearMap.apply ℂ E u
    have he := (ev.hasSum hsumB.hasSum).tsum_eq
    change (∑' i, B i u) = (∑' i, B i) u at he
    rw [← he, hT]
    have hint := hasSum_integral_of_summable_integral_norm (fun i ↦ hi i u)
      ((hc.mul_right ((C*V)*‖u‖)).of_nonneg_of_le
        (fun i ↦ integral_nonneg (fun _ ↦ norm_nonneg _)) (fun i ↦ (hb i u).trans_eq (mul_assoc ..)))
    rw [show (fun i ↦ B i u) = (fun i ↦ ∫ x, H i u x ∂μ) from funext (fun i ↦ hB i u), hint.tsum_eq]
    exact integral_congr_ae (.of_forall fun x ↦ ((hsum x).smul_const (ρ x u)).tsum_eq)
  exact heq ▸ hsumB.hasSum

end RiemannMasullo.StripNuclearity
