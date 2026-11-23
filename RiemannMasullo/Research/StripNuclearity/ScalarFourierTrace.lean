module
public import RiemannMasullo.Research.StripNuclearity.Smoothing
public import RiemannMasullo.Research.StripNuclearity.RadialFourierCost

/-!
# Quantitative smoothing after a radial Mellin resolvent
-/

@[expose] public noncomputable section
open Function MeasureTheory NumberField Set
open scoped Topology ContDiff Convolution ComplexConjugate NumberField.AdeleRing FourierTransform

namespace RiemannMasullo.StripNuclearity

private def reflectConj (k : ℝ → ℂ) (x : ℝ) := conj (k (-x))

private theorem reflectConj_contDiff {k : ℝ → ℂ} (hk : ContDiff ℝ (∞) k) :
    ContDiff ℝ (∞) (reflectConj k) := Complex.conjCLE.contDiff.comp (hk.comp contDiff_neg)

private theorem reflectConj_compact {k : ℝ → ℂ} (hk : HasCompactSupport k) :
    HasCompactSupport (reflectConj k) := by
  have h : HasCompactSupport (fun x : ℝ ↦ k (-x)) := hk.comp_homeomorph (Homeomorph.neg ℝ)
  exact h.comp_left (show conj (0 : ℂ) = 0 from map_zero _)

private theorem reflectConj_involution (k : ℝ → ℂ) : reflectConj (reflectConj k) = k := by
  funext x
  simp [reflectConj]

private theorem reflectConj_support_interval {p : ℝ → ℂ} {T : ℝ}
    (h : tsupport p ⊆ Icc (-T) T) : tsupport (reflectConj p) ⊆ Icc (-T) T := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  have hy : p (-x) ≠ 0 := fun hz ↦ hx (by simp [reflectConj,hz])
  have hb := h (subset_tsupport p hy)
  obtain ⟨hl,hr⟩ := hb
  exact ⟨by linarith,by linarith⟩

private theorem integral_norm_reflectConj (p : ℝ → ℂ) :
    (∫ t : ℝ, ‖reflectConj p t‖) = ∫ t : ℝ, ‖p t‖ := by
  simpa only [reflectConj,Complex.norm_conj] using (integral_neg_eq_self (fun t : ℝ ↦ ‖p t‖) (volume : Measure ℝ))

private theorem fourier_reflectConj (p : ℝ → ℂ) (u : ℝ) : 𝓕 (reflectConj p) u = conj (𝓕 p u) := by
  rw [Real.fourier_real_eq (reflectConj p),Real.fourier_real_eq p,← integral_conj]
  let h := fun t : ℝ ↦ (Real.fourierChar (-(t*u)) : ℂ) * reflectConj p t
  apply ((integral_neg_eq_self h (volume : Measure ℝ)).symm).trans
  apply integral_congr_ae
  refine .of_forall fun t ↦ ?_
  change (Real.fourierChar (-((-t)*u)) : ℂ)*conj (p (- -t)) =
    conj ((Real.fourierChar (-(t*u)) : ℂ)*p t)
  simp only [neg_mul,neg_neg,map_mul,Real.fourierChar.map_neg_eq_inv,Circle.coe_inv_eq_conj,Complex.conj_conj]

/-- Absolute ordinary Fourier mass with the quadratic radial-frequency weight. -/
def radialQuadraticFourierCost (p : ℝ → ℂ) := ∫ u : ℝ, (1+u^2)*‖𝓕 p u‖

/-- The quadratic Fourier cost is nonnegative. -/
theorem radialQuadraticFourierCost_nonneg (p : ℝ → ℂ) : 0 ≤ radialQuadraticFourierCost p :=
  integral_nonneg fun _ ↦ mul_nonneg (by positivity) (norm_nonneg _)

private theorem profile_cost_bounds {J : Set ℝ} (hJ : IsCompact J) {p : ℝ → ℂ}
    (hsm : ContDiff ℝ (∞) p) (hsupp : tsupport p ⊆ J) :
    (∫ u : ℝ, ‖𝓕 p u‖) ≤ radialQuadraticFourierCost p ∧
    ∀ j : ℕ, j ≤ 2 → (∫ t : ℝ, ‖iteratedDeriv j p t‖) ≤
      (volume.real J * (2*Real.pi)^j) * radialQuadraticFourierCost p := by
  have hc : HasCompactSupport p := hJ.of_isClosed_subset isClosed_closure hsupp
  let ψ := hc.toSchwartzMap hsm
  have hu (n : ℕ) : Integrable (fun u : ℝ ↦ |u|^n * ‖𝓕 p u‖) := by
    have hψ := (𝓕 ψ).integrable_pow_mul volume n
    have he : (ψ : ℝ → ℂ) = p := rfl
    simpa only [Real.norm_eq_abs,SchwartzMap.fourier_coe,he] using hψ
  have hF : Integrable (fun u : ℝ ↦ ‖𝓕 p u‖) := by simpa using hu 0
  have hW : Integrable (fun u : ℝ ↦ (1+u^2) * ‖𝓕 p u‖) := by
    apply (hF.add (hu 2)).congr
    exact .of_forall fun u ↦ by simp [add_mul,sq_abs]
  have hm (j : ℕ) (hj : j ≤ 2) :
      (∫ u : ℝ, |u|^j * ‖𝓕 p u‖) ≤ radialQuadraticFourierCost p := by
    apply integral_mono (hu j) hW
    intro u
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    interval_cases j
    · simpa using sq_nonneg u
    · simp only [pow_one]
      nlinarith [sq_nonneg (|u|-1/2),sq_abs u]
    · simp [sq_abs]
  refine ⟨by simpa using hm 0 (by norm_num),fun j hj ↦ ?_⟩
  exact (integral_norm_iteratedDeriv_le_fourier_moment hJ p hsm hsupp j).trans
    (mul_le_mul_of_nonneg_left (hm j hj) (by positivity))

private theorem scalar_convolution_operators_with_reflection {α s : ℝ} (ha : 0 ≤ α) (hs : 0 ≤ s)
    (k : ℝ → ℂ) (hk : HasCompactSupport k) (hkc : ContDiff ℝ (∞) k) :
    let θ := intervalSobolevDensity (-α) α s
    let E := CompactIntervalSobolev volume id (-α) α s
    ∃ B : E →L[ℂ] E, (∀ v, ∀ᵐ x ∂volume, B v x = ∫ t : ℝ, reflectConj k t*v (x-t)) ∧
      HasWeightedAdjointKernel θ k B.adjoint := by
  intro θ E
  have hw : Continuous θ := by
    unfold θ intervalSobolevDensity
    refine Continuous.mul (by fun_prop) (Continuous.rpow_const (by fun_prop) fun x ↦ Or.inl ?_)
    positivity
  have hp (x : ℝ) : 0 < θ x := mul_pos (lt_max_of_lt_left (Real.exp_pos _))
    (Real.rpow_pos_of_pos (by positivity) _)
  obtain ⟨A,hA⟩ := exists_scalar_weighted_convolution (-α) α s (by linarith) hs
    (reflectConj k) (reflectConj_contDiff hkc).continuous (reflectConj_compact hk)
  refine ⟨A,fun v ↦ (hA v).mono fun _ h ↦ h.2,?_⟩
  intro u g hgc hgs hu
  have he := weighted_convolution_adjoint_compact hw hp (reflectConj k) (reflectConj_contDiff hkc).continuous
    (reflectConj_compact hk) A (fun v ↦ (hA v).mono fun _ h ↦ h.2) u g hgc hgs hu
  simpa only [show (fun t ↦ conj (reflectConj k (-t))) = k from reflectConj_involution k] using he

/-- A compact radial convolution after any projection controlled by the
two-sided Mellin resolvent. The constant is independent of both the kernel
and the projection, on a fixed compact set of logarithmic displacements. -/
theorem scalar_projected_convolution_traceNorm_le {α s : ℝ} (ha : 0 ≤ α) (hs : 0 ≤ s)
    {I : Set ℝ} (ho : IsOpen I) (hi : OrdConnected I) (hne : I.Nonempty) (c : ℝ)
    (hno : ∀ z : ℂ, z.re ∈ I → (c : ℂ)^2-z^2 ≠ 0) {J : Set ℝ} (hJ : IsCompact J) :
    let E := CompactIntervalSobolev volume id (-α) α s
    ∀ (j : PositiveRealExponentialDecay I →L[ℂ] E) (R : E →L[ℂ] E)
      (_ : ∀ v, (j v : ℝ → ℂ) =ᵐ[volume] v.val)
      (_ : ∀ p, ∃ q : PositiveRealExponentialDecay I, R (j p) = j q ∧
        ∀ z, z.re ∈ I → mellin (fun t ↦ q.val (Real.log t)) z =
          ((c : ℂ)^2-z^2)⁻¹ * mellin (fun t ↦ p.val (Real.log t)) z),
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : ℝ → ℂ), tsupport p ⊆ J → ContDiff ℝ (∞) p →
        ∀ (A P : E →L[ℂ] E) (hN : IsNuclearOperator (R.adjoint.comp P)),
          (∀ u, ∀ᵐ x ∂volume, A u x = ∫ t : ℝ, p t*u (x-t)) →
          ∃ hn : IsNuclearOperator (A.comp P), traceNorm ⟨A.comp P,hn⟩ ≤
            C * radialQuadraticFourierCost p * (‖P‖ + traceNorm ⟨R.adjoint.comp P,hN⟩) := by
  intro E j R hj hr
  obtain ⟨T,hT⟩ := hJ.exists_bound_of_continuousOn (f := id) continuous_id.continuousOn
  let K := Icc (-T) T
  have hK : IsCompact K := isCompact_Icc
  have hJK : J ⊆ K := fun x hx ↦ abs_le.mp (by simpa [Real.norm_eq_abs] using hT x hx)
  let L (i : ℕ) := volume.real K * (2*Real.pi)^i
  have hL (i : ℕ) : 0 ≤ L i := by dsimp [L]; positivity
  obtain ⟨Y,hY,hYoung⟩ := scalar_convolution_uniform_on_compact (-α) α s (by linarith) hs hK
  obtain ⟨C,hC,hS⟩ := projected_weighted_convolution_traceNorm_uniform ha ho hi hne c hno hK j R hj hr
  let D := Y*(L 0+L 1+L 2)
  let M := max 1 D
  refine ⟨C*M,mul_nonneg hC (zero_le_one.trans (le_max_left _ _)),?_⟩
  intro p hp hsm A P hN hA
  let θ := intervalSobolevDensity (-α) α s
  have hθ : Continuous θ := by
    unfold θ intervalSobolevDensity
    refine Continuous.mul (by fun_prop) (Continuous.rpow_const (by fun_prop) fun x ↦ Or.inl ?_)
    positivity
  have hθp (x : ℝ) : 0 < θ x := mul_pos (lt_max_of_lt_left (Real.exp_pos _))
    (Real.rpow_pos_of_pos (by positivity) _)
  let k := reflectConj p
  have hpK := hp.trans hJK
  have hkK : tsupport k ⊆ K := reflectConj_support_interval hpK
  have hkc : HasCompactSupport k := hK.of_isClosed_subset isClosed_closure hkK
  have hpC : HasCompactSupport p := hK.of_isClosed_subset isClosed_closure hpK
  have hkd : ContDiff ℝ (∞) k := reflectConj_contDiff hsm
  have hk' := (contDiff_infty_iff_deriv.mp hkd).2
  have hk'' := (contDiff_infty_iff_deriv.mp hk').2
  have hB₀ : HasWeightedAdjointKernel θ k A.adjoint :=
    weighted_convolution_adjoint_compact hθ hθp p hsm.continuous hpC A hA
  have hq : radialQuadraticFourierCost k = radialQuadraticFourierCost p := by
    simp only [radialQuadraticFourierCost,k,fourier_reflectConj,Complex.norm_conj]
  let Q := radialQuadraticFourierCost p
  have hQ : 0 ≤ Q := radialQuadraticFourierCost_nonneg p
  obtain ⟨hF,hphys⟩ := profile_cost_bounds hK hkd hkK
  rw [hq] at hF hphys
  have hcore (u : ℝ → ℂ) (hu : tsupport u ⊆ K) (hud : ContDiff ℝ (∞) u) :
      ∃ B : E →L[ℂ] E, HasWeightedAdjointKernel θ u B ∧ ‖B‖ ≤ Y * ∫ t : ℝ, ‖u t‖ := by
    have hcs : HasCompactSupport u := hK.of_isClosed_subset isClosed_closure hu
    obtain ⟨B,hB,hBrep⟩ := scalar_convolution_operators_with_reflection ha hs u hcs hud
    refine ⟨B.adjoint,hBrep,?_⟩
    rw [ContinuousLinearMap.adjoint.norm_map]
    simpa only [integral_norm_reflectConj] using hYoung (reflectConj u) (reflectConj_support_interval hu)
      (reflectConj_contDiff hud) B hB
  obtain ⟨B₁,hB₁,hn₁⟩ := hcore (deriv k) (tsupport_deriv_subset.trans hkK) hk'
  obtain ⟨B₂,hB₂,hn₂⟩ := hcore (deriv (deriv k)) (tsupport_deriv_subset.trans (tsupport_deriv_subset.trans hkK)) hk''
  have hn₀ : ‖A.adjoint‖ ≤ Y * (L 0 * Q) := by
    rw [ContinuousLinearMap.adjoint.norm_map]
    apply (hYoung p hpK hsm A hA).trans
    apply mul_le_mul_of_nonneg_left _ hY
    simpa only [iteratedDeriv_zero,k,integral_norm_reflectConj] using hphys 0 (by omega)
  have h1 : (∫ t : ℝ, ‖deriv k t‖) ≤ L 1 * Q := by simpa only [iteratedDeriv_one] using hphys 1 (by omega)
  have h2 : (∫ t : ℝ, ‖deriv (deriv k) t‖) ≤ L 2 * Q := by
    simpa only [show 2=1+1 by rfl,iteratedDeriv_succ,iteratedDeriv_zero] using hphys 2 (by omega)
  have hsum : ‖A.adjoint‖+‖B₁‖+‖B₂‖ ≤ D * Q := by
    calc _ ≤ Y*(L 0*Q) + Y*(L 1*Q) + Y*(L 2*Q) :=
        add_le_add (add_le_add hn₀ (hn₁.trans (mul_le_mul_of_nonneg_left h1 hY)))
          (hn₂.trans (mul_le_mul_of_nonneg_left h2 hY))
      _ = _ := by dsimp [D]; ring
  have hpair := hS k hkK hkd P A.adjoint B₁ B₂ hN hB₀ hB₁ hB₂
  simp only [ContinuousLinearMap.adjoint_adjoint] at hpair
  obtain ⟨hn,hcost⟩ := hpair
  refine ⟨hn,hcost.trans ?_⟩
  let N := traceNorm (⟨R.adjoint.comp P,hN⟩ : nuclearEndomorphisms E)
  have hNpos : 0 ≤ N := by
    let : Norm (nuclearEndomorphisms E) := ⟨traceNorm⟩
    exact (traceNorm_normedSpaceCore (H := E)).norm_nonneg ⟨_,hN⟩
  have hmQ : Q ≤ M*Q := le_mul_of_one_le_left hQ (le_max_left _ _)
  have hdQ : D*Q ≤ M*Q := mul_le_mul_of_nonneg_right (le_max_right _ _) hQ
  calc _ ≤ C*((M*Q)*‖P‖+(M*Q)*N) :=
      mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_right (hF.trans hmQ) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (hsum.trans hdQ) hNpos)) hC
    _ = _ := by dsimp [N,Q]; ring

end RiemannMasullo.StripNuclearity
