module

public import RiemannMasullo.Research.StripNuclearity.AdjointIntegral
public import RiemannMasullo.Research.StripNuclearity.RadialConvolution
import Mathlib.Analysis.Normed.Lp.SmoothApprox

/-!
# A resolvent factor for weighted adjoint convolution on each radial tail
-/

@[expose] public noncomputable section
open Function Filter MeasureTheory Set
open scoped Topology ContDiff Convolution

namespace RiemannMasullo.StripNuclearity

local notation "ν[" w "]" => (volume.withDensity fun x : ℝ ↦ ENNReal.ofReal ((w : ℝ → ℝ) x))
local notation "H[" w "]" => Lp ℂ 2 ν[w]

/-- An operator has the physical weighted-adjoint kernel on compact continuous
profiles. Its convolution symbol is already conjugated and reflected. -/
def HasWeightedAdjointKernel (w : ℝ → ℝ) (k : ℝ → ℂ) (B : H[w] →L[ℂ] H[w]) : Prop :=
  ∀ (u : H[w]) (g : ℝ → ℂ), Continuous g → HasCompactSupport g → (u : ℝ → ℂ) =ᵐ[volume] g →
    (B u : ℝ → ℂ) =ᵐ[volume] fun x ↦ (w x : ℂ)⁻¹ *
      (((fun y : ℝ ↦ (w y : ℂ)*g y) ⋆[ContinuousLinearMap.mul ℝ ℂ,volume] k) x)

/-- Bounded measurable pointwise multiplication on a positive weighted L²
space, with representatives viewed in Lebesgue measure. -/
theorem exists_weight_multiplier {w : ℝ → ℝ} (hw : Continuous w) (hp : ∀ x, 0 < w x)
    (a : ℝ → ℝ) (hma : Measurable a) (hb : ∃ C : ℝ, ∀ x, |a x| ≤ C) :
    ∃ T : H[w] →L[ℂ] H[w], ∀ u, (T u : ℝ → ℂ) =ᵐ[volume] fun x ↦ (a x : ℂ)*u x := by
  obtain ⟨C,hC⟩ := hb
  let f := fun x ↦ (a x : ℂ)
  have hf : MemLp f ⊤ ν[w] := memLp_top_of_bound
    (Complex.measurable_ofReal.comp hma).aestronglyMeasurable C
    (.of_forall fun x ↦ by simpa [f, Real.norm_eq_abs] using hC x)
  let L := ContinuousLinearMap.mul ℂ ℂ
  let T := L.holderL ν[w] ⊤ 2 2 (hf.toLp f)
  have hbase : volume ≪ ν[w] := withDensity_absolutelyContinuous' hw.measurable.ennreal_ofReal.aemeasurable
    (.of_forall fun x ↦ (ENNReal.ofReal_pos.mpr (hp x)).ne')
  refine ⟨T,fun u ↦ hbase.ae_eq ?_⟩
  exact (L.coeFn_holder (r := 2) (hf.toLp f) u).trans (hf.coeFn_toLp.mono fun x hx ↦ congrArg (·*u x) hx)

/-- Compact continuous profiles are dense for the weighted Hilbert norm. -/
theorem compact_weighted_dense {w : ℝ → ℝ} (hw : Continuous w) (hp : ∀ x, 0 < w x) :
    Dense {u : H[w] | ∃ g : ℝ → ℂ, (u : ℝ → ℂ) =ᵐ[volume] g ∧ HasCompactSupport g ∧ Continuous g} := by
  let : IsLocallyFiniteMeasure ν[w] := IsLocallyFiniteMeasure.withDensity_ofReal hw
  have hbase : volume ≪ ν[w] := withDensity_absolutelyContinuous' hw.measurable.ennreal_ofReal.aemeasurable
    (.of_forall fun x ↦ (ENNReal.ofReal_pos.mpr (hp x)).ne')
  apply (Lp.dense_hasCompactSupport_contDiff (F := ℂ) (μ := ν[w]) (p := 2) (by norm_num)).mono
  rintro u ⟨g,hu,hs,hc⟩
  exact ⟨g,hbase.ae_eq hu,hs,hc.continuous⟩

/-- Away from the corner of the weight, a bounded operator with the weighted
adjoint convolution kernel factors through the Mellin resolvent. The source
mask ensures that convolution by the kernel and its two derivatives sees
only the indicated smooth branch of the output weight. The factor norm is
bounded linearly in the three convolution operator norms, with the same
constant for every kernel at the chosen mask. -/
theorem exists_masked_resolvent_factor_uniform {I : Set ℝ} (ho : IsOpen I) (hi : OrdConnected I)
    (hne : I.Nonempty) {c : ℝ} (hno : ∀ z : ℂ, z.re ∈ I → (c : ℂ)^2-z^2 ≠ 0)
    {w : ℝ → ℝ} (hw : Continuous w) (hp : ∀ x, 0 < w x)
    (j : PositiveRealExponentialDecay I →L[ℂ] H[w]) (R : H[w] →L[ℂ] H[w])
    (hj : ∀ p, (j p : ℝ → ℂ) =ᵐ[volume] p.val)
    (hr : ∀ p, ∃ q : PositiveRealExponentialDecay I, R (j p) = j q ∧
      ∀ z, z.re ∈ I → mellin (fun t ↦ q.val (Real.log t)) z =
        ((c : ℂ)^2-z^2)⁻¹ * mellin (fun t ↦ p.val (Real.log t)) z)
    (b s : ℝ) (a : ℝ → ℝ) (ha : Continuous a) (M : H[w] →L[ℂ] H[w])
    (hM : ∀ u, (M u : ℝ → ℂ) =ᵐ[volume] fun x ↦ (a x : ℂ)*u x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (κ : ℝ → ℂ) (_ : HasCompactSupport κ) (_ : ContDiff ℝ ∞ κ)
      (B₀ B₁ B₂ : H[w] →L[ℂ] H[w]) (_ : HasWeightedAdjointKernel w κ B₀)
      (_ : HasWeightedAdjointKernel w (deriv κ) B₁)
      (_ : HasWeightedAdjointKernel w (deriv (deriv κ)) B₂)
      (_ : ∀ x y, a y ≠ 0 → x-y ∈ tsupport κ →
        (w x)⁻¹ = Real.exp (-b*x-(s/2)*Real.log (1+x^2))),
      ∃ D : H[w] →L[ℂ] H[w], R.comp D = B₀.comp M ∧ ‖D‖ ≤ C * (‖B₀‖ + ‖B₁‖ + ‖B₂‖) := by
  let v := fun x : ℝ ↦ Real.exp (-b*x-(s/2)*Real.log (1+x^2))
  let p := fun x : ℝ ↦ -b-s*x/(1+x^2)
  let q := fun x : ℝ ↦ (p x)^2-s*(1-x^2)/(1+x^2)^2
  have hCoef := weight_log_derivatives b s
  have hd (x : ℝ) : 1+x^2 ≠ 0 := by positivity
  have hpC : Continuous p := by dsimp [p]; fun_prop (disch := apply hd)
  have hqC : Continuous q := by dsimp [q]; fun_prop (disch := intros; positivity)
  have hqB : ∃ C : ℝ, ∀ x, |c^2-q x| ≤ C := ⟨|c^2|+(|b|+|s|)^2+|s|, fun x ↦
    (abs_sub _ _).trans (by linarith [(hCoef.2.2.2 x : |q x| ≤ _)])⟩
  obtain ⟨Q,hQ⟩ := exists_weight_multiplier hw hp (fun x ↦ c^2-q x)
    (continuous_const.sub hqC).measurable hqB
  obtain ⟨P,hP⟩ := exists_weight_multiplier hw hp p hpC.measurable ⟨_,hCoef.2.2.1⟩
  let C := (‖Q‖ + 2*‖P‖ + 1) * ‖M‖
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro κ hc hs B₀ B₁ B₂ hB₀ hB₁ hB₂ hside
  let D := (Q.comp B₀ - (2 : ℂ) • (P.comp B₁) - B₂).comp M
  have hnorm : ‖D‖ ≤ C * (‖B₀‖ + ‖B₁‖ + ‖B₂‖) := by
    let S := ‖B₀‖ + ‖B₁‖ + ‖B₂‖
    have h0 : ‖B₀‖ ≤ S := by dsimp [S]; linarith [norm_nonneg B₁,norm_nonneg B₂]
    have h1 : ‖B₁‖ ≤ S := by dsimp [S]; linarith [norm_nonneg B₀,norm_nonneg B₂]
    have h2 : ‖B₂‖ ≤ S := by dsimp [S]; linarith [norm_nonneg B₀,norm_nonneg B₁]
    have hQ0 : ‖Q.comp B₀‖ ≤ ‖Q‖ * S :=
      (Q.opNorm_comp_le B₀).trans (mul_le_mul_of_nonneg_left h0 (norm_nonneg _))
    have hP1 : ‖(2 : ℂ) • P.comp B₁‖ ≤ 2*(‖P‖ * S) := by
      rw [norm_smul,Complex.norm_ofNat]
      exact mul_le_mul_of_nonneg_left ((P.opNorm_comp_le B₁).trans
        (mul_le_mul_of_nonneg_left h1 (norm_nonneg _))) (by norm_num)
    calc ‖D‖ ≤ ‖Q.comp B₀ - (2 : ℂ) • P.comp B₁ - B₂‖ * ‖M‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ((‖Q‖*S + 2*(‖P‖*S)) + S) * ‖M‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add hQ0 hP1)) h2)
      _ = _ := by dsimp [C,S]; ring
  refine ⟨D,?_,hnorm⟩
  apply ContinuousLinearMap.ext
  intro u
  have closed : IsClosed {v : H[w] | R (D v) = B₀ (M v)} :=
    isClosed_eq (R.continuous.comp D.continuous) (B₀.continuous.comp M.continuous)
  apply closure_minimal _ closed ((compact_weighted_dense hw hp) u)
  rintro f ⟨g,hfg,hgs,hgc⟩
  let af := fun y ↦ (a y : ℂ)*g y
  let G := fun y ↦ (w y : ℂ)*af y
  let L := ContinuousLinearMap.mul ℝ ℂ
  let F (k : ℝ → ℂ) := G ⋆[L,volume] k
  have hAf : (M f : ℝ → ℂ) =ᵐ[volume] af := (hM f).trans (hfg.mono fun y hy ↦ congrArg ((a y : ℂ)*·) hy)
  have hafC : Continuous af := (Complex.continuous_ofReal.comp ha).mul hgc
  have hafS : HasCompactSupport af := hgs.mul_left
  have hGC : Continuous G := (Complex.continuous_ofReal.comp hw).mul hafC
  have hGS : HasCompactSupport G := hafS.mul_left
  have heq (k : ℝ → ℂ) (hk : tsupport k ⊆ tsupport κ) (x : ℝ) :
      (w x : ℂ)⁻¹ * F k x = (v x : ℂ)*F k x := by
    by_cases he : (w x)⁻¹ = v x
    · rw [← Complex.ofReal_inv,he]
    · have hz : F k x = 0 := by
        apply integral_eq_zero_of_ae
        apply ae_of_all
        intro y
        change G y*k (x-y) = 0
        by_cases hgy : a y = 0
        · simp [G,af,hgy]
        · apply mul_eq_zero_of_right
          exact image_eq_zero_of_notMem_tsupport fun h ↦ he (hside _ _ hgy (hk h))
      rw [hz,mul_zero,mul_zero]
  have B0 := (hB₀ (M f) af hafC hafS hAf).trans (.of_forall (heq κ Subset.rfl))
  have B1 := (hB₁ (M f) af hafC hafS hAf).trans (.of_forall (heq (deriv κ) tsupport_deriv_subset))
  have B2 := (hB₂ (M f) af hafC hafS hAf).trans (.of_forall
    (heq (deriv (deriv κ)) (tsupport_deriv_subset.trans tsupport_deriv_subset)))
  obtain ⟨t,d,ht,hdN,hRd⟩ := weighted_convolution_resolvent_numerator ho hi hne hno j R hr b s
    G κ hGS hGC.locallyIntegrable hc hs
  have hBc : B₀ (M f) = j t := by
    apply Lp.ext
    apply (withDensity_absolutelyContinuous volume _).ae_eq
    filter_upwards [B0,hj t] with x h0 htj
    rw [htj,ht]
    exact h0
  have hdformula (x : ℝ) : d.val x =
      ((c : ℂ)^2 - (q x : ℂ)) * ((v x : ℂ) * F κ x) -
        2 * (p x : ℂ) * ((v x : ℂ) * F (deriv κ) x) -
        (v x : ℂ) * F (deriv (deriv κ)) x := hdN x
  have hDc : D f = j d := by
    apply Lp.ext
    have hν := withDensity_absolutelyContinuous volume (fun x ↦ ENNReal.ofReal (w x))
    change (Q (B₀ (M f)) - (2 : ℂ) • P (B₁ (M f)) - B₂ (M f) : H[w]) =ᵐ[ν[w]] _
    filter_upwards [Lp.coeFn_sub (Q (B₀ (M f)) - (2 : ℂ) • P (B₁ (M f))) (B₂ (M f)),
      Lp.coeFn_sub (Q (B₀ (M f))) ((2 : ℂ) • P (B₁ (M f))),
      Lp.coeFn_smul (2 : ℂ) (P (B₁ (M f))),hν.ae_eq (hQ (B₀ (M f))),
      hν.ae_eq (hP (B₁ (M f))),hν.ae_eq B0,hν.ae_eq B1,hν.ae_eq B2,hν.ae_eq (hj d)] with
      x hsub hsub' hsm hqx hpx h0 h1 h2 hdx
    simp only [hsub,Pi.sub_apply,hsub',hsm,Pi.smul_apply,smul_eq_mul,hqx,hpx,h0,h1,h2,hdx,hdformula,
      Complex.ofReal_sub,Complex.ofReal_pow]
    ring
  change R (D f) = B₀ (M f)
  rw [hDc,hBc,hRd]

/-- Away from the corner of the weight, a bounded operator with the weighted
adjoint convolution kernel factors through the Mellin resolvent. The source
mask ensures that convolution by the kernel and its two derivatives sees
only the indicated smooth branch of the output weight. -/
theorem exists_masked_resolvent_factor {I : Set ℝ} (ho : IsOpen I) (hi : OrdConnected I)
    (hne : I.Nonempty) {c : ℝ} (hno : ∀ z : ℂ, z.re ∈ I → (c : ℂ)^2-z^2 ≠ 0)
    {w : ℝ → ℝ} (hw : Continuous w) (hp : ∀ x, 0 < w x)
    (j : PositiveRealExponentialDecay I →L[ℂ] H[w]) (R : H[w] →L[ℂ] H[w])
    (hj : ∀ p, (j p : ℝ → ℂ) =ᵐ[volume] p.val)
    (hr : ∀ p, ∃ q : PositiveRealExponentialDecay I, R (j p) = j q ∧
      ∀ z, z.re ∈ I → mellin (fun t ↦ q.val (Real.log t)) z =
        ((c : ℂ)^2-z^2)⁻¹ * mellin (fun t ↦ p.val (Real.log t)) z)
    (κ : ℝ → ℂ) (hc : HasCompactSupport κ) (hs : ContDiff ℝ ∞ κ)
    (B₀ B₁ B₂ : H[w] →L[ℂ] H[w])
    (hB₀ : HasWeightedAdjointKernel w κ B₀)
    (hB₁ : HasWeightedAdjointKernel w (deriv κ) B₁)
    (hB₂ : HasWeightedAdjointKernel w (deriv (deriv κ)) B₂)
    (b s : ℝ) (a : ℝ → ℝ) (ha : Continuous a) (M : H[w] →L[ℂ] H[w])
    (hM : ∀ u, (M u : ℝ → ℂ) =ᵐ[volume] fun x ↦ (a x : ℂ)*u x)
    (hside : ∀ x y, a y ≠ 0 → x-y ∈ tsupport κ →
      (w x)⁻¹ = Real.exp (-b*x-(s/2)*Real.log (1+x^2))) :
    ∃ D : H[w] →L[ℂ] H[w], R.comp D = B₀.comp M := by

  obtain ⟨_,_,h⟩ := exists_masked_resolvent_factor_uniform ho hi hne hno hw hp j R hj hr b s a ha M hM
  obtain ⟨D,hD,_⟩ := h κ hc hs B₀ B₁ B₂ hB₀ hB₁ hB₂ hside
  exact ⟨D,hD⟩

end RiemannMasullo.StripNuclearity
