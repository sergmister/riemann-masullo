module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.CompactGroup
public import RiemannMasullo.Research.StripNuclearity.IdeleAngularProfiles

/-! # Reconstruction from the positive angular coefficients

On the compact norm-one group a positive character in the coefficient gives
an inverse character in the reconstructed test. Probability Haar fixes the
normalization of both the series and the action.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set
open scoped ContDiff FourierTransform InnerProductSpace NNReal Topology

namespace RiemannMasullo.StripNuclearity

/-- An absolutely summable sequence of angular coefficients reconstructs its
continuous function uniformly on a compact abelian group with probability Haar. -/
theorem hasSum_inverse_characters_of_summable_coefficients {K : Type*}
    [CommGroup K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [T2Space K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    [μ.WeaklyRegular] (f : C(K, ℂ)) (p : PontryaginDual K → ℂ)
    (hp : ∀ ξ, p ξ = ∫ k, (ξ k : ℂ) * f k ∂μ) (hs : Summable (fun ξ ↦ ‖p ξ‖)) :
    HasSum (fun ξ ↦ p ξ • (⟨fun k ↦ star (ξ k : ℂ), by fun_prop⟩ : C(K, ℂ))) f := by
  classical
  let v (ξ : PontryaginDual K) : C(K, ℂ) := ⟨fun k ↦ star (ξ k : ℂ), by fun_prop⟩
  let term (ξ : PontryaginDual K) := p ξ • v ξ
  have hterm : Summable term := .of_norm_bounded hs fun ξ ↦ by
    have hv : ‖v ξ‖ ≤ 1 := (ContinuousMap.norm_le _ zero_le_one).mpr (fun k ↦ by simp [v])
    exact (norm_smul_le (p ξ) (v ξ)).trans (mul_le_of_le_one_right (norm_nonneg _) hv)
  let g := ∑' ξ, term ξ
  let T := ContinuousMap.toLp (E := ℂ) 2 μ ℂ
  let L (η : PontryaginDual K) := (innerSL ℂ (T (v η))).comp T
  have hL (η : PontryaginDual K) (h : C(K, ℂ)) :
      L η h = ∫ k, (η k : ℂ) * h k ∂μ := by
    change ⟪T (v η), T h⟫_ℂ = _
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(v η).coeFn_toLp (p := 2) (𝕜 := ℂ) μ, h.coeFn_toLp (p := 2) (𝕜 := ℂ) μ] with k hx hy
    change ⟪T (v η) k, T h k⟫_ℂ = _
    rw [hx, hy]
    simp [v, mul_comm]
  have hcoeff (η ξ : PontryaginDual K) :
      L η (term ξ) = if ξ = η then p η else 0 := by
    rw [show L η (term ξ) = p ξ * L η (v ξ) from (L η).map_smul (p ξ) (v ξ), hL]
    have ho := integral_character_pair μ ξ η
    simp only [mul_comm (η _ : ℂ), v, ContinuousMap.coe_mk] at *
    rw [ho]
    split_ifs with h <;> simp_all
  have hg (η : PontryaginDual K) : L η g = p η := by
    have h := (L η).hasSum hterm.hasSum
    simp only [hcoeff] at h
    exact h.unique (hasSum_ite_eq η (p η))
  have hd : (fun k ↦ (g - f) k) =ᵐ[μ] (0 : K → ℂ) := by
    apply ae_eq_zero_of_character_integral_eq_zero μ ((g-f).memLp (p := 2) μ ℂ)
    intro η
    have he := hL η⁻¹ (g - f)
    have hm : L η⁻¹ (g - f) = 0 := by rw [map_sub, hg, hL, hp, sub_self]
    simpa only [show ∀ k, (η⁻¹ k : ℂ) = star (η k : ℂ) from fun k ↦ Circle.coe_inv_eq_conj (η k)]
      using he.symm.trans hm
  have he := Measure.eq_of_ae_eq hd (g-f).continuous continuous_zero
  have heq : g = f := sub_eq_zero.mp (ContinuousMap.ext (congrFun he))
  exact heq ▸ hterm.hasSum

/-- For a split group, inverse characters times the positive radial profiles
reconstruct the original test at each group element. -/
theorem hasSum_normSection_angular_profiles {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] (m : G →ₜ* ℝ≥0ˣ) (σ : ℝ≥0ˣ →ₜ* G) (hσ : RightInverse σ m)
    [CompactSpace m.toMonoidHom.ker] [T2Space m.toMonoidHom.ker]
    [MeasurableSpace m.toMonoidHom.ker] [BorelSpace m.toMonoidHom.ker]
    (μ : Measure m.toMonoidHom.ker) [μ.IsHaarMeasure] [IsProbabilityMeasure μ] [μ.WeaklyRegular]
    (χ : PontryaginDual m.toMonoidHom.ker → PontryaginDual G)
    (hk : ∀ ξ (k : m.toMonoidHom.ker), χ ξ k.val = ξ k) (hr : ∀ ξ u, χ ξ (σ u) = 1)
    (φ : G → ℂ) (hφ : Continuous φ) (p : PontryaginDual m.toMonoidHom.ker → ℝ → ℂ)
    (hp : ∀ ξ t, p ξ t = ∫ k : m.toMonoidHom.ker,
      φ (k.val * σ (radialExponential (Multiplicative.ofAdd t))) * (ξ k : ℂ) ∂μ)
    (hs : ∀ t, Summable (fun ξ ↦ ‖p ξ t‖)) (x : G) :
    HasSum (fun ξ ↦ (χ ξ x : ℂ)⁻¹ * p ξ (Real.log ((m x).val : ℝ))) (φ x) := by
  let u := m x
  let t := Real.log (u.val : ℝ)
  have hu : radialExponential (Multiplicative.ofAdd t) = u := by
    apply Units.ext
    apply NNReal.coe_injective
    exact Real.exp_log (by exact_mod_cast Units.zero_lt u)
  let k : m.toMonoidHom.ker := ⟨x / σ u, by
    change m (x / σ u) = 1
    rw [map_div, hσ, div_self']⟩
  have hd : k.val * σ u = x := div_mul_cancel x (σ u)
  have hχ (ξ) : χ ξ x = ξ k := by
    rw [← hd, map_mul, hk, hr, mul_one]
  let f : C(m.toMonoidHom.ker, ℂ) := ⟨fun k ↦ φ (k.val * σ u), hφ.comp (continuous_subtype_val.mul continuous_const)⟩
  have hcoeff (ξ) : p ξ t = ∫ j, (ξ j : ℂ) * f j ∂μ := by
    rw [hp, hu]
    exact integral_congr_ae (.of_forall fun _ ↦ mul_comm _ _)
  have h := hasSum_inverse_characters_of_summable_coefficients μ f (fun ξ ↦ p ξ t) hcoeff (hs t)
  have he := (ContinuousMap.evalCLM ℂ k).hasSum h
  change HasSum (fun ξ ↦ p ξ t * star (ξ k : ℂ)) (φ (k.val * σ u)) at he
  have hsξ (ξ : PontryaginDual m.toMonoidHom.ker) : star (ξ k : ℂ) = (ξ k : ℂ)⁻¹ :=
    (Circle.coe_inv_eq_conj _).symm.trans (Circle.coe_inv _)
  simpa only [hχ, hd, hsξ, mul_comm (p _ _), t, u] using he

/-- The variation of a smooth compact real profile dominates each of its values. -/
theorem norm_le_integral_norm_deriv_of_compact {p : ℝ → ℂ}
    (hp : ContDiff ℝ ∞ p) (hc : HasCompactSupport p) (t : ℝ) :
    ‖p t‖ ≤ ∫ u : ℝ, ‖deriv p u‖ := by
  obtain ⟨b, hb⟩ := hc.bddBelow
  let a := min t b - 1
  have hat : a ≤ t := by dsimp [a]; linarith [min_le_left t b]
  have hab : a < b := by dsimp [a]; linarith [min_le_right t b]
  have ha : p a = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hab.not_ge (hb h))
  have hdc := (contDiff_infty_iff_deriv.mp hp).2.continuous
  have hi : Integrable (deriv p) volume := hdc.integrable_of_hasCompactSupport (hc.of_isClosed_subset isClosed_closure tsupport_deriv_subset)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := a) (b := t)
    (fun u _ ↦ (hp.differentiable (by simp) u).hasDerivAt) hi.intervalIntegrable
  rw [ha, sub_zero] at he
  rw [← he]
  apply (intervalIntegral.norm_integral_le_integral_norm hat).trans
  rw [intervalIntegral.integral_of_le hat]
  exact setIntegral_le_integral hi.norm (.of_forall fun _ ↦ norm_nonneg _)

end RiemannMasullo.StripNuclearity
