module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-! # Integrating Schwartz functions against weights of polynomial growth -/

@[expose] public section

open MeasureTheory Set
open scoped SchwartzMap

namespace RiemannMasullo

/-- Integration against a weight `L` with `‖L‖ / (1 + ‖t‖) ^ k` integrable is a continuous
linear functional on Schwartz functions. -/
theorem SchwartzMap.exists_strongDual_integral_mul {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    (μ : Measure V) (L : V → ℂ) (hL : AEStronglyMeasurable L μ) (k : ℕ)
    (hk : Integrable (fun t ↦ ‖L t‖ / (1 + ‖t‖) ^ k) μ) :
    ∃ Λ : StrongDual ℂ 𝓢(V, ℂ), ∀ g : 𝓢(V, ℂ),
      Integrable (fun t ↦ L t * g t) μ ∧ Λ g = ∫ t, L t * g t ∂μ := by
  let S : 𝓢(V, ℂ) → ℝ := fun g ↦
    (Finset.Iic (k, 0)).sup (fun m ↦ SchwartzMap.seminorm ℂ m.1 m.2) g
  have hpt (g : 𝓢(V, ℂ)) (t : V) :
      ‖L t * g t‖ ≤ 2 ^ k * S g * (‖L t‖ / (1 + ‖t‖) ^ k) := by
    have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k, 0))
      (le_refl k) (le_refl 0) g t
    rw [norm_iteratedFDeriv_zero] at h
    have hpos : 0 < (1 + ‖t‖) ^ k := by positivity
    have hg : ‖g t‖ ≤ 2 ^ k * S g / (1 + ‖t‖) ^ k := by
      rw [le_div_iff₀ hpos, mul_comm]; exact h
    calc ‖L t * g t‖ = ‖L t‖ * ‖g t‖ := norm_mul _ _
      _ ≤ ‖L t‖ * (2 ^ k * S g / (1 + ‖t‖) ^ k) :=
          mul_le_mul_of_nonneg_left hg (norm_nonneg _)
      _ = _ := by ring
  have hint (g : 𝓢(V, ℂ)) : Integrable (fun t ↦ L t * g t) μ :=
    (hk.const_mul (2 ^ k * S g)).mono' (hL.mul g.continuous.aestronglyMeasurable)
      (ae_of_all _ (hpt g))
  refine ⟨SchwartzMap.mkCLMtoNormedSpace (fun g ↦ ∫ t, L t * g t ∂μ)
    (fun g h ↦ by simp only [add_apply, mul_add]; exact integral_add (hint g) (hint h))
    (fun c g ↦ by
      simp only [smul_apply, smul_eq_mul, RingHom.id_apply, mul_left_comm _ c]
      exact integral_const_mul c _)
    ⟨Finset.Iic (k, 0), 2 ^ k * ∫ t, ‖L t‖ / (1 + ‖t‖) ^ k ∂μ,
      by positivity, fun g ↦ ?_⟩, fun g ↦ ⟨hint g, rfl⟩⟩
  calc ‖∫ t, L t * g t ∂μ‖ ≤ ∫ t, 2 ^ k * S g * (‖L t‖ / (1 + ‖t‖) ^ k) ∂μ :=
        norm_integral_le_of_norm_le (hk.const_mul _) (ae_of_all _ (hpt g))
    _ = _ := by rw [integral_const_mul]; change _ = _ * S g; ring

/-- On a finite-dimensional real normed space of positive dimension, `|log ‖t‖|` is integrable
against `(1 + ‖t‖) ^ -(d + 2)` for any additive Haar measure. -/
theorem integrable_abs_log_norm_div_one_add_norm_pow {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]
    (hd : 1 ≤ Module.finrank ℝ V) :
    Integrable (fun t : V ↦ |Real.log ‖t‖| / (1 + ‖t‖) ^ (Module.finrank ℝ V + 2)) μ := by
  set d := Module.finrank ℝ V
  have hmeas : AEStronglyMeasurable
      (fun t : V ↦ |Real.log ‖t‖| / (1 + ‖t‖) ^ (d + 2)) μ := by
    apply Measurable.aestronglyMeasurable
    exact (continuous_abs.measurable.comp measurable_norm.log).div (by fun_prop)
  have hden (t : V) : 1 ≤ (1 + ‖t‖) ^ (d + 2) :=
    one_le_pow₀ (by linarith [norm_nonneg t])
  have h1 : IntegrableOn (fun t : V ↦ |Real.log ‖t‖| / (1 + ‖t‖) ^ (d + 2))
      (Metric.ball 0 1) μ := by
    refine integrableOn_ball_of_norm_le_rpow (C := 2) (α := 1 / 2) hd
      (by have : (1 : ℝ) ≤ d := by exact_mod_cast hd
          linarith) (ae_restrict_of_forall_mem measurableSet_ball fun t ht ↦ ?_) hmeas
    rw [mem_ball_zero_iff] at ht
    rw [Real.norm_of_nonneg (by positivity)]
    rcases (norm_nonneg t).eq_or_lt with h0 | h0
    · rw [← h0, Real.log_zero, abs_zero, zero_div, Real.zero_rpow (by norm_num)]
      norm_num
    · have hl := Real.abs_log_mul_self_rpow_lt ‖t‖ (1 / 2) h0 ht.le (by norm_num)
      have hp : 0 < ‖t‖ ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos h0 _
      rw [abs_mul, abs_of_pos hp, ← lt_div_iff₀ hp] at hl
      rw [Real.rpow_neg h0.le, ← div_eq_mul_inv]
      calc |Real.log ‖t‖| / (1 + ‖t‖) ^ (d + 2) ≤ |Real.log ‖t‖| :=
            div_le_self (abs_nonneg _) (hden t)
        _ ≤ 2 / ‖t‖ ^ (1 / 2 : ℝ) := by norm_num at hl ⊢; exact hl.le
  have h2 : IntegrableOn (fun t : V ↦ |Real.log ‖t‖| / (1 + ‖t‖) ^ (d + 2))
      (Metric.ball 0 1)ᶜ μ := by
    refine ((integrable_one_add_norm (μ := μ) (r := (d + 1 : ℝ))
      (by linarith)).integrableOn).mono' hmeas.restrict
      (ae_restrict_of_forall_mem measurableSet_ball.compl fun t ht ↦ ?_)
    rw [mem_compl_iff, mem_ball_zero_iff, not_lt] at ht
    have hpos : 0 < 1 + ‖t‖ := by positivity
    rw [Real.norm_of_nonneg (by positivity), Real.rpow_neg hpos.le,
      div_le_iff₀ (by positivity), abs_of_nonneg (Real.log_nonneg ht)]
    have : (1 + ‖t‖) ^ (d + 2) = (1 + ‖t‖) ^ ((d + 1 : ℕ) : ℝ) * (1 + ‖t‖) := by
      rw [Real.rpow_natCast]; ring
    rw [this, ← mul_assoc, show ((d + 1 : ℕ) : ℝ) = (d : ℝ) + 1 by push_cast; ring, inv_mul_cancel₀ (by positivity), one_mul]
    linarith [Real.log_le_self (norm_nonneg t)]
  have := h1.union h2
  rwa [union_compl_self, integrableOn_univ] at this

end RiemannMasullo
