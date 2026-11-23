module

public import RiemannMasullo.Ch09_HardySobolev.Sec3
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

/-!
# A common operator bound for compactly supported convolution kernels
-/

@[expose] public noncomputable section
open MeasureTheory Set Function
open scoped Topology

namespace RiemannMasullo.StripNuclearity

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The integrated operator of a jointly continuous representation has norm
bounded by a common constant times the L¹ norm on each fixed compact support. -/
theorem norm_bruhatRegularizedAction_le_on_compact (μ : Measure G) [μ.IsHaarMeasure]
    (ρ : G →* (E →L[ℂ] E)) (hρ : Continuous (fun p : G × E ↦ ρ p.1 p.2))
    {J : Set G} (hJ : IsCompact J) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : BruhatCompactSupport G, tsupport φ.val ⊆ J →
      ∀ u : E, ‖bruhatRegularizedAction μ ρ hρ φ u‖ ≤ (C * ∫ g, ‖φ.val g‖ ∂μ) * ‖u‖ := by
  obtain ⟨C,hC⟩ := banach_steinhaus (g := fun g : J ↦ ρ g.val) fun u ↦ by
    obtain ⟨c,hc⟩ := hJ.exists_bound_of_continuousOn (hρ.comp (Continuous.prodMk_left u)).continuousOn
    exact ⟨c,fun g ↦ hc g.val g.property⟩
  let c := max C 0
  have hc : 0 ≤ c := le_max_right _ _
  refine ⟨c,hc,fun φ hφ ↦ ?_⟩
  have hf : Continuous φ.val := continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).1 φ.property.1)
  have hi : Integrable φ.val μ := hf.integrable_of_hasCompactSupport φ.property.2
  intro u
  let F := fun g ↦ φ.val g • ρ g u
  have hFC : Continuous F := hf.smul (hρ.comp (Continuous.prodMk_left u))
  have hFi : Integrable F μ := hFC.integrable_of_hasCompactSupport
    (hJ.of_isClosed_subset isClosed_closure (closure_minimal (fun g hg ↦ hφ (subset_tsupport _ fun h ↦
      hg (by simp only [F,h,zero_smul]))) hJ.isClosed))
  have hP := (bruhatRegularizedAction_apply μ ρ hρ φ u).unique (Integrable.hasPettisIntegral hFi)
  have hbound (g : G) : ‖F g‖ ≤ ‖φ.val g‖ * (c * ‖u‖) := by
    change ‖φ.val g • ρ g u‖ ≤ _
    rw [norm_smul]
    by_cases hg : φ.val g = 0
    · simp [hg]
    · refine mul_le_mul_of_nonneg_left ((ρ g).le_opNorm u |>.trans ?_) (norm_nonneg _)
      exact mul_le_mul_of_nonneg_right ((hC ⟨g,hφ (subset_tsupport _ hg)⟩).trans (le_max_left _ _)) (norm_nonneg _)
  rw [hP]
  apply (norm_integral_le_integral_norm F).trans
  refine (integral_mono hFi.norm (hi.norm.mul_const (c*‖u‖)) hbound).trans_eq ?_
  rw [integral_mul_const]
  ring

end RiemannMasullo.StripNuclearity
