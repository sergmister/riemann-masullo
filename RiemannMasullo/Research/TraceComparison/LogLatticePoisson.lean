module

public import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.PSeries

/-! # Poisson summation on a logarithmic lattice

With Mathlib's Fourier character, the frequency lattice dual to `Lℤ`
is `(1/L)ℤ`. On taking `L = log p`, samples of a positive-log profile
correspond to the positive powers of `p`.
-/

@[expose] public noncomputable section

open Filter MeasureTheory
open scoped FourierTransform SchwartzMap

namespace RiemannMasullo

/-- Fourier samples at spacing `1/L` sum to `L` times the physical samples at spacing `L`. -/
theorem hasSum_fourier_logLattice (f : 𝓢(ℝ, ℂ)) {L : ℝ} (hL : 0 < L) :
    HasSum (fun k : ℤ ↦ 𝓕 f ((k : ℝ) / L)) ((L : ℂ) * ∑' m : ℤ, f ((m : ℝ) * L)) := by
  let e : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 L hL.ne')
  let g := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e f
  have hg (x : ℝ) : g x = f (x * L) := rfl
  have hFourier (u : ℝ) : 𝓕 g u = L⁻¹ • 𝓕 f (u / L) := by
    simp only [SchwartzMap.fourier_coe, Real.fourier_real_eq]
    have hphase (x : ℝ) : x * L * (u / L) = x * u := by field_simp
    simpa only [hg, hphase, abs_of_pos (inv_pos.mpr hL)] using
      Measure.integral_comp_mul_right (fun x : ℝ ↦ 𝐞 (-(x * (u / L))) • f x) L
  have hs : Summable (fun k : ℤ ↦ 𝓕 g (k : ℝ)) :=
    summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
      (((𝓕 g).isBigO_cocompact_rpow (-2)).comp_tendsto Int.tendsto_coe_cofinite)
  have hunit := g.tsum_eq_tsum_fourier 0
  simp at hunit
  have h := (hunit.symm ▸ hs.hasSum).const_smul L
  simpa only [hFourier, Complex.real_smul, smul_eq_mul, Complex.ofReal_inv,
    mul_inv_cancel_left₀ (Complex.ofReal_ne_zero.mpr hL.ne'), hg] using h

/-- A profile supported on positive logarithms sees only positive physical samples. -/
theorem hasSum_fourier_logLattice_of_support_pos (f : 𝓢(ℝ, ℂ)) {L : ℝ} (hL : 0 < L)
    (hf : Function.support f ⊆ Set.Ioi 0) :
    HasSum (fun k : ℤ ↦ 𝓕 f ((k : ℝ) / L))
      ((L : ℂ) * ∑' m : ℕ, f (((m : ℝ) + 1) * L)) := by
  have hi : Function.Injective (fun m : ℕ ↦ (m : ℤ) + 1) := by
    intro m n h
    change (m : ℤ) + 1 = (n : ℤ) + 1 at h
    omega
  have hsum := hi.tsum_eq (f := fun k : ℤ ↦ f ((k : ℝ) * L)) (by
    intro k hk
    have hk₀ : 0 < (k : ℝ) * L := hf hk
    have hk₁ : 0 < k := by exact_mod_cast (pos_of_mul_pos_left hk₀ hL.le)
    refine ⟨k.toNat - 1, ?_⟩
    change ((k.toNat - 1 : ℕ) : ℤ) + 1 = k
    omega)
  rw [show (∑' m : ℕ, f (((m : ℝ) + 1) * L)) = ∑' k : ℤ, f ((k : ℝ) * L) by
    simpa using hsum]
  exact hasSum_fourier_logLattice f hL

/-- If the support lies between zero and the first positive sample, the frequency sum vanishes. -/
theorem hasSum_fourier_logLattice_zero_of_support_Ioo (f : 𝓢(ℝ, ℂ)) {L : ℝ} (hL : 0 < L)
    (hf : Function.support f ⊆ Set.Ioo 0 L) :
    HasSum (fun k : ℤ ↦ 𝓕 f ((k : ℝ) / L)) 0 := by
  have hz (m : ℕ) : f (((m : ℝ) + 1) * L) = 0 := by
    by_contra hn
    exact (hf hn).2.not_ge (le_mul_of_one_le_left hL.le (by linarith [Nat.cast_nonneg (α := ℝ) m]))
  simpa only [hz, tsum_zero, mul_zero] using
    hasSum_fourier_logLattice_of_support_pos f hL (fun _ hx ↦ (hf hx).1)

end RiemannMasullo
