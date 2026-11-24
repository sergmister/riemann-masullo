module

public import RiemannMasullo.Ch10_TraceSpectral.Sec4a
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # Restricting a closed space to a physical window

A window restriction retains its ambient norm through the product with its adjoint.
A continuous moment which vanishes on all global lifts gives a lower bound for their
norm whenever the observed profiles carry a nonzero moment.
-/

@[expose] public noncomputable section

open Filter Topology

namespace RiemannMasullo

variable {H : Type*} [NormedAddCommGroup H]

section Moment

variable [NormedSpace ℂ H]

/-- The observed part of an annihilated moment is bounded by the norm of its tail
functional times the full norm of the lift. -/
theorem windowMoment_norm_le (L : H →L[ℂ] ℂ) (E : H →L[ℂ] H) {u : H}
    (hu : L u = 0) : ‖L (E u)‖ ≤ ‖L.comp (1 - E)‖ * ‖u‖ := by
  have h : (L.comp (1 - E)) u = -(L (E u)) := by simp [hu]
  calc ‖L (E u)‖ = ‖(L.comp (1 - E)) u‖ := by rw [h, norm_neg]
       _ ≤ _ := (L.comp (1 - E)).le_opNorm u

/-- Global lifts in the kernel of a moment must escape every norm bound if their
restrictions approximate a profile with nonzero moment and the tail dual norms vanish. -/
theorem tendsto_norm_lift_atTop_of_windowMoment (L : H →L[ℂ] ℂ)
    (E : ℕ → H →L[ℂ] H) (u : ℕ → H) {g : H} (hg : L g ≠ 0)
    (hu : ∀ j, L (u j) = 0) (hprofile : Tendsto (fun j ↦ E j (u j)) atTop (𝓝 g))
    (htail : Tendsto (fun j ↦ ‖L.comp (1 - E j)‖) atTop (𝓝 0)) :
    Tendsto (fun j ↦ ‖u j‖) atTop atTop := by
  have hpos := norm_pos_iff.mpr hg
  have hm := ((L.continuous.tendsto g).comp hprofile).norm
  apply tendsto_atTop.2
  intro b
  have hb : 0 < max b 1 := zero_lt_one.trans_le (le_max_right _ _)
  filter_upwards [hm.eventually_const_lt (half_lt_self hpos),
    htail.eventually_lt_const (div_pos (half_pos hpos) hb)] with j hj hk
  by_contra! hj'
  have hbound := mul_le_mul_of_nonneg_left
    (hj'.le.trans (le_max_left b 1)) (norm_nonneg (L.comp (1 - E j)))
  have hlow := windowMoment_norm_le L (E j) (hu j)
  have hsmall := (lt_div_iff₀ hb).mp hk
  change ‖L g‖ / 2 < ‖L (E j (u j))‖ at hj
  linarith

end Moment

section Hilbert

variable [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Restriction of a closed subspace to a self-adjoint window, followed on the
right by its adjoint, gives the windowed global orthogonal projection. -/
theorem windowRestriction_comp_adjoint (G : Submodule ℂ H) [CompleteSpace G]
    (E : H →L[ℂ] H) (hE : E.adjoint = E) :
    (E.comp G.subtypeL).comp (E.comp G.subtypeL).adjoint =
      E.comp (G.starProjection.comp E) := by
  rw [ContinuousLinearMap.adjoint_comp, G.adjoint_subtypeL, hE]
  rfl

/-- If a nuclear operator has both its input and output in a physical window,
its trace after the global geometric projection can be computed with the product
of the window restriction and its adjoint. -/
theorem hilbertTrace_windowRestriction (T : nuclearEndomorphisms H) (G : Submodule ℂ H)
    [CompleteSpace G] (E : H →L[ℂ] H) (hE : E.adjoint = E)
    (hleft : E * T.val = T.val) (hright : T.val * E = T.val) :
    let J := E.comp G.subtypeL
    hilbertTrace ⟨T.val * G.starProjection, mul_mem_nuclearEndomorphisms_right _ T⟩ =
      hilbertTrace ⟨T.val * (J.comp J.adjoint), mul_mem_nuclearEndomorphisms_right _ T⟩ := by
  intro J
  let S : nuclearEndomorphisms H :=
    ⟨T.val * G.starProjection, mul_mem_nuclearEndomorphisms_right _ T⟩
  calc
    _ = hilbertTrace ⟨E * S.val, mul_mem_nuclearEndomorphisms_left _ S⟩ := by
      apply congrArg hilbertTrace
      apply Subtype.ext
      change T.val * G.starProjection = E * (T.val * G.starProjection)
      rw [← mul_assoc, hleft]
    _ = hilbertTrace ⟨S.val * E, mul_mem_nuclearEndomorphisms_right _ S⟩ :=
      spectralRestriction_cyclic E S
    _ = _ := by
      apply congrArg hilbertTrace
      apply Subtype.ext
      dsimp only [J]
      rw [windowRestriction_comp_adjoint G E hE]
      change T.val * G.starProjection * E = T.val * (E * (G.starProjection * E))
      rw [← mul_assoc T.val E, hright, mul_assoc]

/-- If a global projection fixes a nonzero vector, its compression by exhausting
contractive windows has norm tending to one. Applied to the orthogonal complement
of the theta space, this measures the error in using the full window projector. -/
theorem tendsto_norm_compressed_starProjection (V : Submodule ℂ H) [CompleteSpace V]
    (E : ℕ → H →L[ℂ] H) (hE : ∀ j, ‖E j‖ ≤ 1)
    (hstrong : ∀ x, Tendsto (fun j ↦ E j x) atTop (𝓝 x))
    {v : H} (hv : v ∈ V) (hv₀ : v ≠ 0) :
    Tendsto (fun j ↦ ‖(E j).comp (V.starProjection.comp (E j))‖) atTop (𝓝 1) := by
  let P := V.starProjection
  let C := fun j ↦ (E j).comp (P.comp (E j))
  have hfix : P v = v := V.starProjection_eq_self_iff.mpr hv
  have hfull : Tendsto (fun j ↦ P (E j v)) atTop (𝓝 v) := by
    have h := (P.continuous.tendsto v).comp (hstrong v)
    rwa [hfix] at h
  have hstep (j : ℕ) : ‖C j v - E j v‖ ≤ ‖P (E j v) - v‖ := by
    change ‖E j (P (E j v)) - E j v‖ ≤ _
    rw [← map_sub]
    exact ((E j).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (hE j))
  have hCv : Tendsto (fun j ↦ C j v) atTop (𝓝 v) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun _ ↦ norm_nonneg _)
      (fun j ↦ (norm_sub_le_norm_sub_add_norm_sub (C j v) (E j v) v).trans (add_le_add (hstep j) le_rfl))
    simpa using (tendsto_iff_norm_sub_tendsto_zero.mp hfull).add
      (tendsto_iff_norm_sub_tendsto_zero.mp (hstrong v))
  have hpos := norm_pos_iff.mpr hv₀
  have hratio : Tendsto (fun j ↦ ‖C j v‖ / ‖v‖) atTop (𝓝 1) := by
    simpa [hpos.ne'] using hCv.norm.div_const ‖v‖
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hratio tendsto_const_nhds
  · intro j
    exact (div_le_iff₀ hpos).mpr ((C j).le_opNorm v)
  · intro j
    have hp : ‖P.comp (E j)‖ ≤ 1 := (P.opNorm_comp_le _).trans
      ((mul_le_of_le_one_left (norm_nonneg _) V.starProjection_norm_le).trans (hE j))
    exact ((E j).opNorm_comp_le _).trans
      ((mul_le_of_le_one_left (norm_nonneg _) (hE j)).trans hp)

/-- If a larger sieved band contains the first N Euler differences of a smaller
band, then the part of the smaller band missed by its projection has operator norm
at most the Nth translation power. This estimates a one-sided projection error. -/
theorem norm_sieved_band_projection_error_le (T : H →L[ℂ] H) (N : ℕ)
    (U V : Submodule ℂ H) [CompleteSpace U] [CompleteSpace V]
    (hsieve : ∀ u ∈ U, ∀ j < N, (1 - T) ((T ^ j) u) ∈ V) :
    ‖(1 - V.starProjection).comp U.starProjection‖ ≤ ‖T ^ N‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  let u := U.starProjection x
  have hu : u ∈ U := U.starProjection_apply_mem x
  have hm : u - (T ^ N) u ∈ V := by
    have heq := DFunLike.congr_fun (mul_neg_geom_sum T N) u
    change (1 - T) ((∑ i ∈ Finset.range N, T ^ i) u) = u - (T ^ N) u at heq
    rw [← heq, sum_apply, map_sum]
    exact V.sum_mem fun j hj ↦ hsieve u hu j (Finset.mem_range.mp hj)
  let R := 1 - V.starProjection
  have hz : R (u - (T ^ N) u) = 0 := by
    change (u - (T ^ N) u) - V.starProjection (u - (T ^ N) u) = 0
    rw [V.starProjection_eq_self_iff.mpr hm, sub_self]
  have heq : R u = R ((T ^ N) u) := sub_eq_zero.mp (map_sub R u _ ▸ hz)
  have hR : ‖R‖ ≤ 1 := by
    change ‖1 - V.starProjection‖ ≤ 1
    rw [← V.starProjection_orthogonal']
    exact Vᗮ.starProjection_norm_le
  change ‖R u‖ ≤ _
  rw [heq]
  exact ((R.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) hR)).trans
    (((T ^ N).le_opNorm u).trans (mul_le_mul_of_nonneg_left
      (U.norm_starProjection_apply_le x) (norm_nonneg _)))

end Hilbert

end RiemannMasullo
