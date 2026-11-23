module

public import RiemannMasullo.AppC_LCTVS.Sec5a
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # Appendix C.5.1: the printed Lipschitz claim for a weakly differentiable map -/

@[expose] public noncomputable section

namespace RiemannMasullo

open Bornology

universe u

/-- Paper: Lemma C.5.1.13(1), p. 726. As printed: for a weakly continuously
differentiable map on an open subset of kᵈ, where k is ℝ or ℂ and d ≥ 1, one
bounded set contains all the normalized increments in (C.5.1.19) for distances
at most one. This is the Lipschitz clause. The continuity consequence is
`WeaklyContDiffOn.continuousOn`. See ERRATA F229. -/
def Printed.weaklyContDiffOn_lipschitz : Prop :=
  let over (k : Type) [RCLike k] [NormedAlgebra k ℂ] : Prop :=
    ∀ d : ℕ, 1 ≤ d →
      ∀ (E : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
        [PolynormableSpace ℂ E] [T2Space E],
        let W := EuclideanSpace k (Fin d)
        ∀ (Ω : Set W), IsOpen Ω → ∀ (f : W → E), WeaklyContDiffOn k f Ω →
          ∃ B : Set E, IsVonNBounded ℂ B ∧
            ∀ x' ∈ Ω, ∀ x ∈ Ω, x' ≠ x → ‖x' - x‖ ≤ 1 →
              ((‖x' - x‖⁻¹ : ℝ) : ℂ) • (f x' - f x) ∈ B
  over ℝ ∧ over ℂ

/-- The map x ↦ x² from ℝ (as `EuclideanSpace ℝ (Fin 1)`) to ℂ, lifted to any universe,
is weakly continuously differentiable on the whole line. -/
private theorem weaklyContDiffOn_lipschitz_false_sq :
    WeaklyContDiffOn ℝ (fun x : EuclideanSpace ℝ (Fin 1) ↦
      (ULift.up (((x 0 : ℝ) : ℂ) ^ 2) : ULift.{u} ℂ)) Set.univ := by
  rw [weaklyContDiffOn_iff_scalar isOpen_univ]
  intro φ
  have h1 : ContDiff ℝ 1 (fun x : EuclideanSpace ℝ (Fin 1) ↦ ((x 0 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)).contDiff
  have h2 : ContDiff ℝ 1 (fun x : EuclideanSpace ℝ (Fin 1) ↦
      (ULift.up (((x 0 : ℝ) : ℂ) ^ 2) : ULift.{u} ℂ)) :=
    ((ContinuousLinearEquiv.ulift (R₁ := ℝ) (M₁ := ℂ)).symm.contDiff.comp (h1.pow 2))
  exact ((φ.restrictScalars ℝ).contDiff.comp h2).contDiffOn

/-- Paper: Lemma C.5.1.13(1), p. 726. Take k = ℝ, d = 1, Ω = ℝ, E = ℂ,
and f(x) = x². Its weak differential is the jointly continuous map
(x, v) ↦ 2xv under the identification of ℂ with its weak completion.
The normalized increments for x' = x + 1 are 2x + 1, an unbounded set. -/
theorem Printed.weaklyContDiffOn_lipschitz_false :
    ¬ Printed.weaklyContDiffOn_lipschitz := by
  intro h
  obtain ⟨B, hB, hinc⟩ := h.1 1 le_rfl (ULift ℂ) Set.univ isOpen_univ _
    weaklyContDiffOn_lipschitz_false_sq
  obtain ⟨R, hR⟩ := ((NormedSpace.isVonNBounded_iff ℂ).1 hB).exists_norm_le
  set t : ℝ := max R 0
  let x : EuclideanSpace ℝ (Fin 1) := WithLp.toLp 2 (fun _ ↦ t)
  let x' : EuclideanSpace ℝ (Fin 1) := WithLp.toLp 2 (fun _ ↦ t + 1)
  have hd : x' - x = WithLp.toLp 2 (fun _ ↦ (1 : ℝ)) := by
    rw [← WithLp.toLp_sub]; congr 1; funext; simp
  have hn : ‖x' - x‖ = 1 := by rw [hd, EuclideanSpace.norm_eq]; simp
  have hne : x' ≠ x := by
    intro h; rw [h, sub_self, norm_zero] at hn; exact zero_ne_one hn
  have hmem := hR _ (hinc x' trivial x trivial hne hn.le)
  rw [hn, inv_one, Complex.ofReal_one, one_smul] at hmem
  have hsq : ‖(ULift.up (((x' 0 : ℝ) : ℂ) ^ 2) : ULift ℂ) - ULift.up (((x 0 : ℝ) : ℂ) ^ 2)‖
      = 2 * t + 1 := by
    change ‖((t + 1 : ℝ) : ℂ) ^ 2 - ((t : ℝ) : ℂ) ^ 2‖ = _
    have h2 : ((t + 1 : ℝ) : ℂ) ^ 2 - ((t : ℝ) : ℂ) ^ 2 = ((2 * t + 1 : ℝ) : ℂ) := by
      push_cast; ring
    rw [h2, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hR' : R ≤ t := le_max_left _ _
  have ht0 : 0 ≤ t := le_max_right _ _
  rw [hsq] at hmem
  linarith

end RiemannMasullo
