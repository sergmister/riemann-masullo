module
public import RiemannMasullo.Research.StripNuclearity.Local
public import RiemannMasullo.Research.StripNuclearity.TraceResolventSplit
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Projected trace class for smooth compact radial convolutions
-/

@[expose] public noncomputable section
open Function Filter MeasureTheory Set
open scoped Topology ContDiff Convolution ComplexConjugate FourierTransform

namespace RiemannMasullo.StripNuclearity

local notation "ν[" w "]" => (volume.withDensity fun x : ℝ ↦ ENNReal.ofReal ((w : ℝ → ℝ) x))
local notation "H[" w "]" => Lp ℂ 2 ν[w]

/-- A compactly supported smooth radial convolution inherits trace class on
the spectral subspace from the projected two-sided Mellin resolvent. Its
weighted adjoint is resolved on the two tails, and the remaining compact
piece is nuclear by absolute Fourier inversion. The bound is uniform for
all kernels with support in a fixed compact set and every projection. -/
theorem projected_weighted_convolution_traceNorm_uniform {α s : ℝ} (hα : 0 ≤ α)
    {I : Set ℝ} (ho : IsOpen I) (hi : OrdConnected I) (hne : I.Nonempty) (c : ℝ)
    (hno : ∀ z : ℂ, z.re ∈ I → (c : ℂ)^2-z^2 ≠ 0)
    {J : Set ℝ} (hJ : IsCompact J) :
    let w := intervalSobolevDensity (-α) α s
    ∀ (j : PositiveRealExponentialDecay I →L[ℂ] H[w]) (R : H[w] →L[ℂ] H[w])
      (_ : ∀ p, (j p : ℝ → ℂ) =ᵐ[volume] p.val)
      (_ : ∀ p, ∃ q : PositiveRealExponentialDecay I, R (j p) = j q ∧
        ∀ z, z.re ∈ I → mellin (fun t ↦ q.val (Real.log t)) z =
          ((c : ℂ)^2-z^2)⁻¹ * mellin (fun t ↦ p.val (Real.log t)) z),
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (κ : ℝ → ℂ), tsupport κ ⊆ J → ContDiff ℝ ∞ κ →
        ∀ (P B₀ B₁ B₂ : H[w] →L[ℂ] H[w]) (hR : IsNuclearOperator (R.adjoint.comp P)),
          HasWeightedAdjointKernel w κ B₀ → HasWeightedAdjointKernel w (deriv κ) B₁ →
          HasWeightedAdjointKernel w (deriv (deriv κ)) B₂ →
          ∃ hn : IsNuclearOperator (B₀.adjoint.comp P), traceNorm ⟨B₀.adjoint.comp P,hn⟩ ≤
            C * ((∫ u : ℝ, ‖𝓕 κ u‖)*‖P‖ + (‖B₀‖+‖B₁‖+‖B₂‖)*traceNorm ⟨R.adjoint.comp P,hR⟩) := by
  intro w j R hj hr
  have hw : Continuous w := by
    unfold w intervalSobolevDensity
    refine Continuous.mul (by fun_prop) (Continuous.rpow_const (by fun_prop) fun x ↦ Or.inl ?_)
    positivity
  have hp (x : ℝ) : 0 < w x := by
    exact mul_pos (lt_max_of_lt_left (Real.exp_pos _)) (Real.rpow_pos_of_pos (by positivity) _)
  obtain ⟨K,hJK⟩ := hJ.exists_bound_of_continuousOn (f := id) continuous_id.continuousOn
  let T := max K 0 + 1
  have ht : 0 < T := by dsimp [T]; positivity
  have hrad {t : ℝ} (h : t ∈ J) : |t| < T := by
    have hv : |t| ≤ K := by simpa [Real.norm_eq_abs] using hJK t h
    dsimp [T]
    linarith [le_max_left K 0]
  let ap (x : ℝ) := Real.smoothTransition (x-T)
  let am (x : ℝ) := Real.smoothTransition (-x-T)
  let a0 (x : ℝ) := 1-ap x-am x
  have hpc : Continuous ap := Real.smoothTransition.continuous.comp (continuous_id.sub continuous_const)
  have hmc : Continuous am := Real.smoothTransition.continuous.comp (continuous_neg.sub continuous_const)
  have h0c : Continuous a0 := (continuous_const.sub hpc).sub hmc
  have h0s : HasCompactSupport a0 := by
    apply HasCompactSupport.intro (isCompact_Icc (a := -T-1) (b := T+1))
    intro x hx
    have hor : x < -T-1 ∨ T+1 < x := by
      by_contra! h
      exact hx ⟨h.1,h.2⟩
    rcases hor with h | h
    · simp [a0,ap,am,Real.smoothTransition.zero_of_nonpos (by linarith : x-T ≤ 0),
        Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ -x-T)]
    · simp [a0,ap,am,Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ x-T),
        Real.smoothTransition.zero_of_nonpos (by linarith : -x-T ≤ 0)]
  have h1 (x : ℝ) : |Real.smoothTransition x| ≤ 1 :=
    (abs_of_nonneg (Real.smoothTransition.nonneg x)).trans_le (Real.smoothTransition.le_one x)
  obtain ⟨Mp,hMp⟩ := exists_weight_multiplier hw hp ap hpc.measurable ⟨1,fun _ ↦ h1 _⟩
  obtain ⟨Mm,hMm⟩ := exists_weight_multiplier hw hp am hmc.measurable ⟨1,fun _ ↦ h1 _⟩
  let M0 := ContinuousLinearMap.id ℂ (H[w]) - Mp - Mm
  have hm0 (u : H[w]) : (M0 u : ℝ → ℂ) =ᵐ[volume] fun x ↦ (a0 x : ℂ)*u x := by
    have hbase : volume ≪ ν[w] := withDensity_absolutelyContinuous' hw.measurable.ennreal_ofReal.aemeasurable
      (.of_forall fun x ↦ (ENNReal.ofReal_pos.mpr (hp x)).ne')
    change ((u - Mp u - Mm u : H[w]) : ℝ → ℂ) =ᵐ[volume] _
    filter_upwards [hbase.ae_eq (Lp.coeFn_sub (u-Mp u) (Mm u)),hbase.ae_eq (Lp.coeFn_sub u (Mp u)),
      hMp u,hMm u] with x hsub hsub' hm hM
    simp only [hsub,Pi.sub_apply,hsub',hm,hM,a0,Complex.ofReal_sub,Complex.ofReal_one]
    ring
  obtain ⟨C₀,hC₀,hlocal⟩ := traceNorm_compactly_masked_adjoint_uniform hw hp hJ a0 h0c h0s M0 hm0
  obtain ⟨Cp,hCp,hposAux⟩ := exists_masked_resolvent_factor_uniform ho hi hne hno hw hp j R hj hr
    (2*α) s ap hpc Mp hMp
  obtain ⟨Cm,hCm,hnegAux⟩ := exists_masked_resolvent_factor_uniform ho hi hne hno hw hp j R hj hr
    (-2*α) s am hmc Mm hMm
  let C := max C₀ (Cp+Cm)
  refine ⟨C,hC₀.trans (le_max_left _ _),?_⟩
  intro κ hK hs P B₀ B₁ B₂ hN hB₀ hB₁ hB₂
  have hc : HasCompactSupport κ := hJ.of_isClosed_subset isClosed_closure hK
  obtain ⟨h0N,h0cost⟩ := hlocal κ hK hs B₀ hB₀
  have hpos (x y : ℝ) (hy : ap y ≠ 0) (hts : x-y ∈ tsupport κ) :
      (w x)⁻¹ = Real.exp (-(2*α)*x-(s/2)*Real.log (1+x^2)) := by
    have hy' : 0 < y-T := lt_of_not_ge (fun h ↦ hy (Real.smoothTransition.zero_of_nonpos h))
    have hx : 0 ≤ x := by linarith [(abs_lt.mp (hrad (hK hts))).1]
    simpa only [ite_eq_left hx,neg_mul] using reciprocal_interval_weight_branches hα s x
  have hneg (x y : ℝ) (hy : am y ≠ 0) (hts : x-y ∈ tsupport κ) :
      (w x)⁻¹ = Real.exp (-(-2*α)*x-(s/2)*Real.log (1+x^2)) := by
    have hy' : 0 < -y-T := lt_of_not_ge (fun h ↦ hy (Real.smoothTransition.zero_of_nonpos h))
    have hx : ¬ 0 ≤ x := by linarith [(abs_lt.mp (hrad (hK hts))).2]
    simpa only [ite_eq_right hx,neg_mul,neg_neg] using reciprocal_interval_weight_branches hα s x
  obtain ⟨Dp,hDp,hDpn⟩ := hposAux κ hc hs B₀ B₁ B₂ hB₀ hB₁ hB₂ hpos
  obtain ⟨Dm,hDm,hDmn⟩ := hnegAux κ hc hs B₀ B₁ B₂ hB₀ hB₁ hB₂ hneg
  have hsum : B₀ = B₀.comp M0 + R.comp Dp + R.comp Dm := by
    rw [hDp,hDm]
    apply ContinuousLinearMap.ext
    intro u
    change B₀ u = B₀ (u - Mp u - Mm u) + B₀ (Mp u) + B₀ (Mm u)
    simp only [map_sub]
    abel
  have he : B₀.adjoint.comp P = (B₀.comp M0).adjoint.comp P + Dp.adjoint.comp (R.adjoint.comp P) +
      Dm.adjoint.comp (R.adjoint.comp P) := by
    conv_lhs => rw [hsum]
    simp only [map_add,ContinuousLinearMap.add_comp,ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.comp_assoc]
  obtain ⟨hn,hcost⟩ := traceNorm_resolvent_split_le _ (B₀.comp M0) R P Dp Dm he h0N hN
  refine ⟨hn,hcost.trans ?_⟩
  let S := ‖B₀‖+‖B₁‖+‖B₂‖
  let N := traceNorm (⟨R.adjoint.comp P,hN⟩ : nuclearEndomorphisms (H[w]))
  let F := ∫ u : ℝ, ‖𝓕 κ u‖
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hF : 0 ≤ F := integral_nonneg fun _ ↦ norm_nonneg _
  have hNpos : 0 ≤ N := by
    let : Norm (nuclearEndomorphisms (H[w])) := ⟨traceNorm⟩
    exact (traceNorm_normedSpaceCore (H := H[w])).norm_nonneg ⟨_,hN⟩
  have hD : ‖Dp‖+‖Dm‖ ≤ C*S := by
    calc _ ≤ Cp*S+Cm*S := add_le_add hDpn hDmn
      _ = (Cp+Cm)*S := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hS
  have hU : traceNorm ⟨B₀.comp M0,h0N⟩ ≤ C*F :=
    h0cost.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hF)
  change ‖P‖*traceNorm ⟨B₀.comp M0,h0N⟩ + (‖Dp‖+‖Dm‖)*N ≤ C*(F*‖P‖+S*N)
  calc _ ≤ ‖P‖*(C*F)+(C*S)*N :=
      add_le_add (mul_le_mul_of_nonneg_left hU (norm_nonneg _)) (mul_le_mul_of_nonneg_right hD hNpos)
    _ = _ := by ring

/-- A compactly supported smooth radial convolution inherits trace class on
the spectral subspace from the projected two-sided Mellin resolvent. Its
weighted adjoint is resolved on the two tails, and the remaining compact
piece is nuclear by absolute Fourier inversion. -/
theorem nuclear_weighted_convolution_of_projected_resolvent {α s : ℝ} (hα : 0 ≤ α)
    {I : Set ℝ} (ho : IsOpen I) (hi : OrdConnected I) (hne : I.Nonempty) (c : ℝ)
    (hno : ∀ z : ℂ, z.re ∈ I → (c : ℂ)^2-z^2 ≠ 0)
    (κ : ℝ → ℂ) (hc : HasCompactSupport κ) (hs : ContDiff ℝ ∞ κ) :
    let w := intervalSobolevDensity (-α) α s
    ∀ (j : PositiveRealExponentialDecay I →L[ℂ] H[w]) (R P B₀ B₁ B₂ : H[w] →L[ℂ] H[w])
      (_ : ∀ p, (j p : ℝ → ℂ) =ᵐ[volume] p.val)
      (_ : ∀ p, ∃ q : PositiveRealExponentialDecay I, R (j p) = j q ∧
        ∀ z, z.re ∈ I → mellin (fun t ↦ q.val (Real.log t)) z =
          ((c : ℂ)^2-z^2)⁻¹ * mellin (fun t ↦ p.val (Real.log t)) z)
      (_ : IsNuclearOperator (R.adjoint.comp P))
      (_ : HasWeightedAdjointKernel w κ B₀)
      (_ : HasWeightedAdjointKernel w (deriv κ) B₁)
      (_ : HasWeightedAdjointKernel w (deriv (deriv κ)) B₂),
      IsNuclearOperator (B₀.adjoint.comp P) := by
  intro w j R P B₀ B₁ B₂ hj hr hN hB₀ hB₁ hB₂
  obtain ⟨_,_,h⟩ := projected_weighted_convolution_traceNorm_uniform hα ho hi hne c hno hc.isCompact j R hj hr
  obtain ⟨hn,_⟩ := h κ Subset.rfl hs P B₀ B₁ B₂ hN hB₀ hB₁ hB₂
  exact hn

end RiemannMasullo.StripNuclearity
