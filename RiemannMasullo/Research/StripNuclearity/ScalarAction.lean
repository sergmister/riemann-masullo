module

public import RiemannMasullo.Research.PositiveStrip.Multiplier

/-!
# Quantitative composition of radial Sobolev multipliers

The full scalar Hardy–Sobolev norm controls the error of a contractive cutoff
after a smoothing multiplier by the sup norm of the product of their symbols
on a slightly wider strip.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory Set
open scoped Topology

namespace RiemannMasullo.StripNuclearity

/-- Contractive holomorphic Mellin symbols on the open strip above `I`. -/
def ContractiveStripSymbol (I : Set ℝ) (b : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ b (Complex.re ⁻¹' I) ∧ ∀ z, z.re ∈ I → ‖b z‖ ≤ 1

/-- The scalar Hardy–Sobolev action of any two contractive strip symbols
satisfies an operator-norm estimate for the cutoff error after the second
multiplier. The constant is common to the full contractive family. -/
theorem exists_scalar_multiplier_action {I : Set ℝ} (hI : IsOpen I) (hi : OrdConnected I)
    (h0 : 0 ∈ I) {α s β : ℝ} (ha : 0 ≤ α) (hs : 0 ≤ s) (hβ : 2*α+s < 2*β)
    (hp : β ∈ I) (hm : -β ∈ I) (hsub : Icc (-α) α ⊆ I) :
    let E := CompactIntervalSobolev volume id (-α) α s
    let S := {b : ℂ → ℂ // ContractiveStripSymbol I b}
    ∃ (j : PositiveRealExponentialDecay I →L[ℂ] E) (U : S → E →L[ℂ] E) (C : ℝ),
      0 ≤ C ∧ DenseRange j ∧ (∀ p, (j p : ℝ → ℂ) =ᵐ[volume] p.val) ∧
      (∀ b, ‖U b‖ ≤ C) ∧
      (∀ b p, ∃ q : PositiveRealExponentialDecay I, U b (j p) = j q ∧
        ∀ z, z.re ∈ I → mellin (fun t ↦ q.val (Real.log t)) z =
          b.val z * mellin (fun t ↦ p.val (Real.log t)) z) ∧
      ∀ (b r : S) (ε : ℝ), 0 < ε → (∀ z, z.re ∈ I → ‖(b.val z - 1) * r.val z‖ ≤ ε) →
        ‖(U b - ContinuousLinearMap.id ℂ E).comp (U r)‖ ≤ C * ε := by
  intro E S
  let one : S := ⟨fun _ ↦ 1, differentiableOn_const _, fun z _ ↦ by simp⟩
  have hl (z : ℂ) : Tendsto (fun f : S ↦ f.val z) (pure one) (𝓝 1) := by
    exact tendsto_pure_nhds _ _
  obtain ⟨j, U, C, -, hd, hj, hU, -, ht⟩ := StripMultiplier.exists_sobolev_mellin_multiplier_family
    hI hi h0 ha hs hβ hp hm hsub (pure one) (fun f : S ↦ f.val)
    (fun f ↦ f.property.1) (fun f ↦ f.property.2) (fun z _ ↦ hl z)
  refine ⟨j, U, C, (norm_nonneg _).trans (hU one), hd, hj, hU, fun b p ↦ ht p b, ?_⟩
  intro b r ε hε hb
  let g (z : ℂ) := ((ε : ℂ)⁻¹) * ((b.val z - 1) * r.val z)
  have hg : ContractiveStripSymbol I g := by
    refine ⟨(differentiableOn_const _).mul ((b.property.1.sub (differentiableOn_const _)).mul r.property.1), ?_⟩
    intro z hz
    dsimp [g]
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε, inv_mul_eq_div]
    exact (div_le_one hε).mpr (hb z hz)
  let d : S := ⟨g, hg⟩
  have hEq : (U b - ContinuousLinearMap.id ℂ E).comp (U r) = (ε : ℂ) • U d := by
    apply DFunLike.coe_injective
    apply hd.equalizer ((U b - ContinuousLinearMap.id ℂ E).comp (U r)).continuous
      ((ε : ℂ) • U d).continuous
    funext p
    change U b (U r (j p)) - U r (j p) = (ε : ℂ) • U d (j p)
    obtain ⟨q, hq, hR⟩ := ht p r
    obtain ⟨v, hv, hB⟩ := ht q b
    obtain ⟨w, hw, hD⟩ := ht p d
    rw [hq, hv, hw, ← j.map_sub, ← j.map_smul]
    apply congrArg j
    let M := positiveRealFourierMellin I hI hi ⟨0,h0⟩
    apply M.injective
    rw [map_sub, map_smul]
    apply Subtype.ext
    funext z
    change (M v).val z - (M q).val z = (ε : ℂ) * (M w).val z
    by_cases hz : z.re ∈ I
    · have hrw (u : PositiveRealExponentialDecay I) := positiveRealFourierMellin_apply I hI hi ⟨0,h0⟩ u z hz
      change (M _).val _ - (M _).val _ = _ * (M _).val _
      rw [hrw, hrw, hrw, hB z hz, hR z hz, hD z hz]
      dsimp [d, g]
      field_simp [Complex.ofReal_ne_zero.mpr hε.ne']
    · rw [(M v).property.1 hz, (M q).property.1 hz, (M w).property.1 hz]
      simp
  rw [hEq, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε, mul_comm]
  exact mul_le_mul_of_nonneg_right (hU d) hε.le

end RiemannMasullo.StripNuclearity
