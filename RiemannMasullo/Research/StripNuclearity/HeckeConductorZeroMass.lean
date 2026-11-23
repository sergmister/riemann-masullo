module

public import RiemannMasullo.Research.StripNuclearity.HeckeJensen
public import RiemannMasullo.Research.StripNuclearity.HeckeLeftGamma
public import RiemannMasullo.AppB_AnalyticNT.Sec4b

/-! # Conductor dependence of the reciprocal-square Hecke zero mass

For a nontrivial character of the norm-one idele classes, Jensen's inequality
bounds the zero mass by a constant of the field times the logarithms of the
finite conductor and the archimedean parameters. Zeros are counted with
their multiplicities throughout the critical strip.
-/

@[expose] public noncomputable section

open IsDedekindDomain NumberField Set

namespace RiemannMasullo.StripNuclearity

variable {F : Type*} [Field F] [NumberField F]
local notation "U" => PontryaginDual (IdeleClassGroup (𝓞 F) F)

/-- The absolute discriminant and each finite conductor factor have norm at least one. -/
theorem heckeLogDiscriminantConductor_nonneg (χ : U) : 0 ≤ heckeLogDiscriminantConductor χ := by
  unfold heckeLogDiscriminantConductor
  refine add_nonneg (Real.log_nonneg ?_) (finsum_nonneg fun v ↦ mul_nonneg (Real.log_nonneg ?_) (by positivity))
  · exact_mod_cast Int.natAbs_pos.mpr (NumberField.discr_ne_zero F)
  · exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm v).le

/-- For each number field the dual pair of finite Hecke functions satisfies a common
left-edge estimate with its actual conductor and archimedean shifts as parameters. -/
theorem exists_uniform_finiteHecke_pair_left_bound (F : Type*) [Field F] [NumberField F] :
    ∃ E : ℝ, 1 ≤ E ∧ ∀ (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (s : ℂ),
      s.re = -(3/2 : ℝ) →
        ‖(continuedCompletedHeckeL χ s / heckeGammaFactor χ s) *
          (continuedCompletedHeckeL χ⁻¹ s / heckeGammaFactor χ⁻¹ s)‖ ≤
        Real.exp (4 * heckeLogDiscriminantConductor χ) * E ^ 2 *
          (6 + ∑ v : InfinitePlace F, ‖heckeArchimedeanShift χ v‖) ^ (8 * Fintype.card (InfinitePlace F)) *
          (1 + |s.im|) ^ (8 * Fintype.card (InfinitePlace F)) := by
  obtain ⟨E, hE, he⟩ := exists_uniform_finiteHeckeL_right_bounds F
  refine ⟨E, hE, fun χ s hs ↦ ?_⟩
  obtain ⟨c, _, hc⟩ := completedHeckeL_functionalEquation_conductorScale χ _ _
    (continuedCompletedHeckeL_spec χ).1 (continuedCompletedHeckeL_spec χ).2
    (continuedCompletedHeckeL_spec χ⁻¹).1 (continuedCompletedHeckeL_spec χ⁻¹).2
  exact finiteHecke_pair_left_le_of_functionalEquation χ _ c hc E (zero_le_one.trans hE)
    (fun ψ w hw ↦ (he ψ w (by rw [hw]; norm_num)).2) s hs

/-- For every character nontrivial on the norm-one idele classes, the positive
completed Hecke divisor, counted with reciprocal-square height weights, has mass
bounded by a field constant times one plus its log discriminant–conductor and
the logarithm of its archimedean shifts. This is a quantitative Jensen estimate
for the projected convolution used in Equation (12.5.1.4), p. 520. -/
theorem exists_uniform_heckeZeroMass_conductor_bound (F : Type*) [Field F] [NumberField F] :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)),
      χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1 →
      let mass := fun z : ℂ ↦ ((MeromorphicOn.divisor (continuedCompletedHeckeL χ) univ z).toNat : ℝ) /
        (1 + |z.im|) ^ 2
      Summable mass ∧ ∑' z, mass z ≤ K * (1 + |heckeLogDiscriminantConductor χ| +
        Real.log (6 + ∑ v : InfinitePlace F, ‖heckeArchimedeanShift χ v‖)) := by
  obtain ⟨E, hE, he⟩ := exists_uniform_finiteHecke_pair_left_bound F
  obtain ⟨K, hK, hmass⟩ := exists_uniform_heckeZeroMass_of_paired_left_bound F
  let d := 8 * Fintype.card (InfinitePlace F)
  let B := 5 + 2 * Real.log E + 2 * (d : ℝ)
  have hlogE := Real.log_nonneg hE
  have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨K * B, mul_nonneg hK hB, fun χ hχ ↦ ?_⟩
  let κ := heckeLogDiscriminantConductor χ
  let J := ∑ v : InfinitePlace F, ‖heckeArchimedeanShift χ v‖
  let A := Real.exp (4 * κ) * E ^ 2 * (6 + J) ^ d
  have hκ : 0 ≤ κ := heckeLogDiscriminantConductor_nonneg χ
  have hJ : 0 ≤ J := Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _)
  have hJ₁ : 1 ≤ 6 + J := by linarith
  have hE₀ := zero_lt_one.trans_le hE
  have hJ₀ := zero_lt_one.trans_le hJ₁
  have hA : 1 ≤ A := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (Real.one_le_exp_iff.mpr (by positivity)) (one_le_pow₀ hE))
    (one_le_pow₀ hJ₁)
  have hlog : Real.log A = 4 * κ + 2 * Real.log E + (d : ℝ) * Real.log (6 + J) := by
    dsimp only [A]
    rw [Real.log_mul (mul_pos (Real.exp_pos _) (sq_pos_of_pos hE₀)).ne' (pow_pos hJ₀ d).ne',
      Real.log_mul (Real.exp_pos _).ne' (sq_pos_of_pos hE₀).ne', Real.log_exp, Real.log_pow, Real.log_pow]
    norm_num
  obtain ⟨hs, h⟩ := hmass χ hχ d A hA (he χ)
  refine ⟨hs, h.trans ?_⟩
  let Y := 1 + |κ| + Real.log (6 + J)
  have hZ := Real.log_nonneg hJ₁
  have hY : 1 ≤ Y := by dsimp only [Y]; linarith [abs_nonneg κ]
  have hκY : κ ≤ Y := by dsimp only [Y]; linarith [le_abs_self κ]
  have hZY : Real.log (6 + J) ≤ Y := by dsimp only [Y]; linarith [abs_nonneg κ]
  change K * (1 + Real.log A + (d : ℝ)) ≤ K * B * Y
  rw [hlog, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hK
  dsimp only [B]
  nlinarith [mul_le_mul_of_nonneg_left hY hlogE, mul_le_mul_of_nonneg_left hY hd,
    mul_le_mul_of_nonneg_left hZY hd]

end RiemannMasullo.StripNuclearity
