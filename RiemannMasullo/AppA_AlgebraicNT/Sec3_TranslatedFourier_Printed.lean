module

public import RiemannMasullo.AppA_AlgebraicNT.Sec3

/-! # Appendix A.3: the printed Fourier formula for a translated p-adic ball -/

@[expose] public noncomputable section

namespace RiemannMasullo

open MeasureTheory Set

local instance printedSec3TranslatedFourierPadicMeasurableSpace (p : ℕ) [Fact p.Prime] :
    MeasurableSpace ℚ_[p] := borel _

/-- Paper: Example A.3.1.6, (A.3.1.5), p. 557.
As printed: for every prime, integer scale, translation and frequency, the transform of the
translated ball indicator equals the scaled unit-ball transform at the shifted frequency and
the scaled reciprocal-ball indicator times the positive character at `a * x`. The inverse of
`padicStandardCharacter` gives the paper's character, and `tamagawaFourier` conjugates it as on
p. 558. The zero-translation specialization is `padicTamagawaFourier_scaledIntegers`.
See ERRATA F217. -/
def Printed.padicTamagawaFourier_translatedScaledIntegers : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℤ) (a x : ℚ_[p]),
    let integers := Metric.closedBall (0 : ℚ_[p]) 1
    let f₀ := integers.indicator (fun _ ↦ (1 : ℂ))
    let f := ((fun t : ℚ_[p] ↦ a + (p : ℚ_[p]) ^ n * t) '' integers).indicator
      (fun _ ↦ (1 : ℂ))
    let ψ := fun t : ℚ_[p] ↦ (padicStandardCharacter p t)⁻¹
    let transform := tamagawaFourier (padicTamagawaMeasure p) ψ
    let scale := ((p : ℝ) ^ (-n) : ℂ)
    transform f x = scale * transform f₀ ((p : ℚ_[p]) ^ n * (x - a)) ∧
      transform f x = scale * (ψ (a * x) : ℂ) *
        (((fun t : ℚ_[p] ↦ (p : ℚ_[p]) ^ (-n) * t) '' integers).indicator (fun _ ↦ 1)) x

/-- Paper: Example A.3.1.6, (A.3.1.5), p. 557.
Take `p = 3`, `n = 0` and `a = 1/3` in `ℚ_[3]`. At `x = 0` the transform is the mass
one of the translated unit ball. The shifted unit-ball transform is zero at `-1/3`.
At `x = 1` the transform is `exp(-2πi/3)`, since the character is constant on the coset,
and the printed phase gives `exp(2πi/3)`. -/
theorem Printed.padicTamagawaFourier_translatedScaledIntegers_false :
    ¬ Printed.padicTamagawaFourier_translatedScaledIntegers := by
  intro h
  have h1 := (h 3 0 (1 / 3) 0).1
  simp only [] at h1
  have : BorelSpace ℚ_[3] := ⟨rfl⟩
  set μ := padicTamagawaMeasure 3
  have : μ.IsAddHaarMeasure :=
    (Classical.choose_spec (padicTamagawaMeasure_existsUnique 3).exists).1
  have hball : μ (Metric.closedBall (0 : ℚ_[3]) 1) = 1 :=
    (Classical.choose_spec (padicTamagawaMeasure_existsUnique 3).exists).2.2
  have hχ0 : padicStandardCharacter 3 0 = 1 := by
    simpa using padicStandardCharacter_div_pow 3 0 0
  -- left side: the mass of the translated ball
  have hS : (fun t : ℚ_[3] ↦ 1 / 3 + ((3 : ℕ) : ℚ_[3]) ^ (0 : ℤ) * t) '' Metric.closedBall 0 1 =
      (fun t ↦ -(1 / 3) + t) ⁻¹' Metric.closedBall 0 1 := by
    simp only [zpow_zero, one_mul]
    rw [image_add_left]
  have hSm : MeasurableSet ((fun t : ℚ_[3] ↦ -(1 / 3) + t) ⁻¹' Metric.closedBall 0 1) :=
    (measurableSet_closedBall).preimage (measurable_const_add _)
  have hL : tamagawaFourier μ (fun t ↦ (padicStandardCharacter 3 t)⁻¹)
      (((fun t : ℚ_[3] ↦ 1 / 3 + ((3 : ℕ) : ℚ_[3]) ^ (0 : ℤ) * t) '' Metric.closedBall 0 1).indicator
        (fun _ ↦ (1 : ℂ))) 0 = 1 := by
    unfold tamagawaFourier
    simp only [mul_zero, hχ0, inv_one, Circle.coe_one, star_one, mul_one]
    rw [hS, integral_indicator_const _ hSm, measureReal_def, measure_preimage_add, hball]
    simp
  -- right side: the unit-ball transform at -1/3
  have hR : tamagawaFourier μ (fun t ↦ (padicStandardCharacter 3 t)⁻¹)
      ((Metric.closedBall (0 : ℚ_[3]) 1).indicator (fun _ ↦ (1 : ℂ)))
      (((3 : ℕ) : ℚ_[3]) ^ (0 : ℤ) * (0 - 1 / 3)) = 0 := by
    have hlib := congrFun (padicTamagawaFourier_scaledIntegers 3 0) (-(1 / 3))
    have hnot : (-(1 / 3) : ℚ_[3]) ∉ Metric.closedBall (0 : ℚ_[3]) 1 := by
      intro hm
      rw [Metric.mem_closedBall, dist_zero_right, norm_neg, norm_div, norm_one] at hm
      have h3 : ‖(3 : ℚ_[3])‖ = 3⁻¹ := by exact_mod_cast Padic.norm_p (p := 3)
      rw [h3] at hm
      norm_num at hm
    simp only [zpow_zero, one_mul, neg_zero, image_id', Pi.smul_apply,
      indicator_of_notMem hnot, smul_zero] at hlib
    unfold tamagawaFourier at hlib ⊢
    simp only [zpow_zero, one_mul, zero_sub]
    have hconj := congrArg (starRingEnd ℂ) hlib
    rw [← integral_conj, map_zero] at hconj
    rw [← hconj]
    congr 1
    funext t
    rw [Circle.coe_inv_eq_conj]
    by_cases ht : t ∈ Metric.closedBall (0 : ℚ_[3]) 1 <;> simp [ht]
  rw [hL, hR] at h1
  norm_num at h1

end RiemannMasullo
