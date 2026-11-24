module
public import RiemannMasullo.Research.PositiveStrip.Multiplier
public import RiemannMasullo.Research.PositiveStrip.FiniteDual
import all RiemannMasullo.Research.PositiveStrip.Multiplier
import all RiemannMasullo.Research.PositiveStrip.FiniteDual
public import RiemannMasullo.Ch10_TraceSpectral.Sec2

@[expose] public noncomputable section
open Filter Function MeasureTheory Set
open scoped Topology
namespace RiemannMasullo.StripDual

abbrev SE (α s : ℝ) := CompactIntervalSobolev volume id (-α) α s
def ME := positiveRealFourierMellin (univ : Set ℝ) isOpen_univ ordConnected_univ univ_nonempty

private def restrictProfile (J : Set ℝ) (p : PositiveRealExponentialDecay univ) : PositiveRealExponentialDecay J :=
  ⟨p.val, (Submodule.mem_iInf _).mpr fun a ↦ (Submodule.mem_iInf _).mp p.property ⟨a.val,mem_univ _⟩⟩

private theorem inverseSymbol (H : Tests) (z : ℂ) :
    mellin (fun t ↦ (ME.symm H).val (Real.log t)) z = H.val z := by
  rw [← positiveRealFourierMellin_apply univ isOpen_univ ordConnected_univ univ_nonempty (ME.symm H) z (mem_univ _)]
  exact congrArg (fun K : SchwartzBergman univ ↦ K.val z) (ME.apply_symm_apply H)

private theorem eqProfile {I : Set ℝ} (hI : IsOpen I) (hi : OrdConnected I) (hne : I.Nonempty)
    (p q : PositiveRealExponentialDecay I)
    (h : ∀ z, z.re ∈ I → mellin (fun t ↦ p.val (Real.log t)) z = mellin (fun t ↦ q.val (Real.log t)) z) :
    p = q := by
  let M := positiveRealFourierMellin I hI hi hne
  apply M.injective
  apply Subtype.ext
  funext z
  by_cases hz : z.re ∈ I
  · exact (positiveRealFourierMellin_apply I hI hi hne p z hz).trans ((h z hz).trans
      (positiveRealFourierMellin_apply I hI hi hne q z hz).symm)
  · exact ((M p).property.1 hz).trans ((M q).property.1 hz).symm

theorem exists_chart {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) :
    ∃ e : Tests →ₗ[ℂ] SE α s, DenseRange e ∧
      ∀ H, (e H : ℝ → ℂ) =ᵐ[volume] (ME.symm H).val := by
  obtain ⟨j,-,hd,hr⟩ := scalarIntervalSobolev_dense (-α) α s (by linarith) hs univ isOpen_univ ordConnected_univ (subset_univ _)
  let e : Tests →ₗ[ℂ] SE α s := j.toLinearMap.comp ME.symm.toLinearMap
  exact ⟨e, hd.comp ME.symm.surjective.denseRange j.continuous, fun H ↦ hr _⟩

private theorem chart_restriction {α s : ℝ} (J : Set ℝ) (e : Tests →ₗ[ℂ] SE α s)
    (he : ∀ H, (e H : ℝ → ℂ) =ᵐ[volume] (ME.symm H).val)
    (j : PositiveRealExponentialDecay J →L[ℂ] SE α s) (hj : ∀ q, (j q : ℝ → ℂ) =ᵐ[volume] q.val) (H : Tests) :
    e H = j (restrictProfile J (ME.symm H)) := by
  apply Lp.ext
  exact (withDensity_absolutelyContinuous _ _).ae_le ((he H).trans (hj (restrictProfile J (ME.symm H))).symm)

theorem chart_multiplier_action {α s β r : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (hβ : 2*α+s < 2*β) (hβr : β < r)
    (e : Tests →ₗ[ℂ] SE α s) (he : ∀ H, (e H : ℝ → ℂ) =ᵐ[volume] (ME.symm H).val) :
    ∀ H : Tests, ∃ U : SE α s →L[ℂ] SE α s, ∀ p, U (e p) = e (timesTest H p) := by
  let J := Ioo (-r) r
  have hr : 0 < r := by linarith
  have h0 : 0 ∈ J := ⟨by linarith,hr⟩
  have hp : β ∈ J := ⟨by linarith,hβr⟩
  have hm : -β ∈ J := ⟨by linarith,by linarith⟩
  have hsub : Icc (-α) α ⊆ J := fun x ⟨hl,hu⟩ ↦ ⟨by linarith, by linarith⟩
  obtain ⟨j,-,hd,hj⟩ := scalarIntervalSobolev_dense (-α) α s (by linarith) hs J isOpen_Ioo ordConnected_Ioo hsub
  obtain ⟨C,hC,extend⟩ := StripMultiplier.scalar_sobolev_multiplier_extension h0 hα hs hβ hp hm j hd hj
  have contract (H : Tests) (hbounded : ∀ z, z.re ∈ J → ‖H.val z‖ ≤ 1) :
      ∃ U : SE α s →L[ℂ] SE α s, ∀ p, U (e p) = e (timesTest H p) := by
    have hdiff : DifferentiableOn ℂ H.val (Complex.re ⁻¹' J) := H.property.2.1.mono (fun _ _ ↦ trivial)
    let T := StripMultiplier.multiplyTest isOpen_Ioo ordConnected_Ioo ⟨0,h0⟩ H.val hdiff hbounded
    obtain ⟨U,-,hU⟩ := extend T (fun v p ↦ by
      apply StripMultiplier.line_contraction
      intro t
      rw [StripMultiplier.multiplyTest_mellin isOpen_Ioo ordConnected_Ioo ⟨0,h0⟩ H.val hdiff hbounded p ⟨v,t⟩ v.property, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hbounded _ v.property))
    refine ⟨U,fun p ↦ ?_⟩
    rw [chart_restriction J e he j hj p, hU, chart_restriction J e he j hj (timesTest H p)]
    apply congrArg j
    apply eqProfile isOpen_Ioo ordConnected_Ioo ⟨0,h0⟩
    intro z hz
    rw [StripMultiplier.multiplyTest_mellin isOpen_Ioo ordConnected_Ioo ⟨0,h0⟩ H.val hdiff hbounded _ z hz]
    change H.val z * mellin (fun t ↦ (ME.symm p).val (Real.log t)) z =
      mellin (fun t ↦ (ME.symm (timesTest H p)).val (Real.log t)) z
    rw [inverseSymbol, inverseSymbol]
    rfl
  intro H
  obtain ⟨M,hM⟩ := H.property.2.2 (-r) r (by linarith) (subset_univ _) 0
  let A := max M 1
  have hA : 0 < A := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let h : Tests := (A:ℂ)⁻¹ • H
  have hb (z : ℂ) (hz : z.re ∈ J) : ‖h.val z‖ ≤ 1 := by
    change ‖(A:ℂ)⁻¹ * H.val z‖ ≤ 1
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hA, inv_mul_eq_div]
    apply (div_le_one hA).mpr
    have hz' : z ∈ Complex.re ⁻¹' Icc (-r) r := ⟨hz.1.le,hz.2.le⟩
    exact (by simpa using hM ⟨z,hz',rfl⟩ : ‖H.val z‖ ≤ M).trans (le_max_left _ _)
  obtain ⟨U,hU⟩ := contract h hb
  refine ⟨(A:ℂ) • U, fun p ↦ ?_⟩
  rw [smul_apply, hU, ← e.map_smul]
  apply congrArg e
  apply Subtype.ext
  funext z
  change (A:ℂ) * (((A:ℂ)⁻¹ * H.val z) * p.val z) = H.val z * p.val z
  rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hA.ne'), one_mul]

theorem chart_tail_action {α s β r : ℝ} (ha : 0 ≤ α) (hs : 0 ≤ s) (hβ : 2*α+s < 2*β) (hβr : β < r)
    (e : Tests →ₗ[ℂ] SE α s) (he : ∀ H, (e H : ℝ → ℂ) =ᵐ[volume] (ME.symm H).val)
    {ι : Type*} (l : Filter ι) [l.IsCountablyGenerated] (b : ι → ℂ → ℂ)
    (hb : ∀ n, DifferentiableOn ℂ (b n) (Complex.re ⁻¹' Ioo (-r) r))
    (hc : ∀ n z, z.re ∈ Ioo (-r) r → ‖b n z‖ ≤ 1)
    (hl : ∀ z, z.re ∈ Ioo (-r) r → Tendsto (fun n ↦ b n z) l (𝓝 1)) :
    ∃ U : ι → SE α s →L[ℂ] SE α s, (∀ y, Tendsto (fun n ↦ U n y) l (𝓝 y)) ∧
      ∀ n H, ∃ q : PositiveRealExponentialDecay (Ioo (-r) r), (U n (e H) : ℝ → ℂ) =ᵐ[volume] q.val ∧
        ∀ z, z.re ∈ Ioo (-r) r → mellin (fun t ↦ q.val (Real.log t)) z = b n z * H.val z := by
  let J := Ioo (-r) r
  have h0 : 0 ∈ J := ⟨by linarith, by linarith⟩
  obtain ⟨j,U,-,-,-,hj,-,hlim,hU⟩ := StripMultiplier.exists_sobolev_mellin_multiplier_family
    isOpen_Ioo ordConnected_Ioo h0 ha hs hβ (⟨by linarith,hβr⟩ : β ∈ J) (⟨by linarith,by linarith⟩ : -β ∈ J)
    (fun x ⟨hx,hy⟩ ↦ ⟨by linarith,by linarith⟩) l b hb hc hl
  refine ⟨U,hlim,fun n H ↦ ?_⟩
  obtain ⟨q,hq,hm⟩ := hU (restrictProfile J (ME.symm H)) n
  refine ⟨q, ?_, fun z hz ↦ (hm z hz).trans (congrArg (b n z * ·) (inverseSymbol H z))⟩
  rw [chart_restriction J e he j hj, hq]
  exact hj q

end RiemannMasullo.StripDual
