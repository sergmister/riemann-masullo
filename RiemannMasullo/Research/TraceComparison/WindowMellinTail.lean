module

public import RiemannMasullo.Ch09_HardySobolev.Sec2
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # The upper log-norm tail of a Mellin moment -/

@[expose] public noncomputable section

open Filter MeasureTheory Set

namespace RiemannMasullo

/-- On a positive-width interval, the dual mass of the upper tail decays at least as
fast as the reciprocal exponential times the reciprocal logarithmic Sobolev factor. -/
theorem integral_inv_intervalSobolevDensity_upperTail_le {α s R : ℝ}
    (hα : 0 < α) (hs : 0 ≤ s) (hR : 0 ≤ R) :
    (∫ t in Ioi R, (intervalSobolevDensity (-α) α s t)⁻¹) ≤
      ((1 + R ^ 2) ^ (s / 2))⁻¹ * (Real.exp (-(2 * α) * R) / (2 * α)) := by
  let c := ((1 + R ^ 2) ^ (s / 2))⁻¹
  have ha : -(2 * α) < 0 := by linarith
  have mono (t : ℝ) (ht : R < t) :
      (intervalSobolevDensity (-α) α s t)⁻¹ ≤ c * Real.exp (-(2 * α) * t) := by
    have ht₀ := hR.trans ht.le
    have hbase : 1 + R ^ 2 ≤ 1 + t ^ 2 := by gcongr
    have hw := Real.rpow_le_rpow (by positivity) hbase (by positivity : 0 ≤ s / 2)
    have hweights : ((1 + t ^ 2) ^ (s / 2))⁻¹ ≤ c :=
      inv_anti₀ (by positivity) hw
    rw [intervalSobolevDensity, max_eq_right (Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hα.le ht₀])),
      mul_inv_rev, ← Real.exp_neg, neg_mul]
    exact mul_le_mul_of_nonneg_right hweights (Real.exp_pos _).le
  calc
    _ ≤ ∫ t in Ioi R, c * Real.exp (-(2 * α) * t) := by
      apply integral_mono_of_nonneg
      · exact ae_of_all _ fun t ↦ by unfold intervalSobolevDensity; positivity
      · exact (integrableOn_exp_mul_Ioi ha R).const_mul c
      · exact ae_restrict_of_forall_mem measurableSet_Ioi fun t ht ↦ mono t ht
    _ = _ := by rw [integral_const_mul, integral_exp_mul_Ioi ha]; simp [c]

/-- A unit-modulus Mellin character pairs with a function on a window with norm at
most the product of the weighted L² energy and the inverse-weight mass, both square
rooted. The measure can already be restricted to a one-sided or two-sided tail. -/
theorem norm_integral_unitMoment_le_weighted_energy {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f u : X → ℂ) (w : X → ℝ) (hw : ∀ x, 0 < w x)
    (hu : ∀ x, ‖u x‖ = 1)
    (hf : MemLp (fun x ↦ ‖f x‖ * Real.sqrt (w x)) 2 μ)
    (hi : MemLp (fun x ↦ (Real.sqrt (w x))⁻¹) 2 μ) :
    ‖∫ x, f x * u x ∂μ‖ ≤
      Real.sqrt (∫ x, ‖f x‖ ^ 2 * w x ∂μ) * Real.sqrt (∫ x, (w x)⁻¹ ∂μ) := by
  let A := fun x ↦ ‖f x‖ * Real.sqrt (w x)
  let B := fun x ↦ (Real.sqrt (w x))⁻¹
  have hA (x : X) : 0 ≤ A x := mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
  have hB (x : X) : 0 ≤ B x := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hprod (x : X) : ‖f x * u x‖ = A x * B x := by
    simp [A, B, hu, (Real.sqrt_pos.mpr (hw x)).ne']
  have hsqA (x : X) : A x ^ (2 : ℝ) = ‖f x‖ ^ 2 * w x := by
    dsimp only [A]
    rw [Real.rpow_two, mul_pow, Real.sq_sqrt (hw x).le]
  have hsqB (x : X) : B x ^ (2 : ℝ) = (w x)⁻¹ := by
    dsimp only [B]
    rw [Real.rpow_two, inv_pow, Real.sq_sqrt (hw x).le]
  calc
    _ ≤ ∫ x, ‖f x * u x‖ ∂μ := norm_integral_le_integral_norm _
    _ = ∫ x, A x * B x ∂μ := integral_congr_ae (ae_of_all _ hprod)
    _ ≤ _ := by
      have H := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) Real.HolderConjugate.two_two
        (ae_of_all _ hA) (ae_of_all _ hB) (by simpa using hf) (by simpa using hi)
      simpa only [hsqA, hsqB, ← Real.sqrt_eq_rpow] using H

end RiemannMasullo
