module

public import RiemannMasullo.Ch10_TraceSpectral.Sec2
public import RiemannMasullo.Ch13_ZerosHecke.Targets
public import RiemannMasullo.External.Grh.Lemmas.ShiftedZetaZeros
import Mathlib.Analysis.Normed.Module.Connected

/-! # A zero-free half-plane for the rational Dedekind continuation

The continuation formulation of the Cureton–Thorner theorem uses Mathlib's Dedekind
Dirichlet series on its convergence half-plane. Analytic uniqueness identifies the
continuation for the rational field with Mathlib's Riemann zeta function away from its
pole. The functional equation then bounds both sides of the centered strip.
-/

public section

open Filter NumberField Set
open scoped Topology
open RiemannMasullo.External.Grh

namespace RiemannMasullo.StripNuclearity

/-- An analytic continuation of the rational Dedekind zeta series away from its pole
agrees with the Riemann zeta function there. Only the Dirichlet-series identity on
`1 < Re s` enters the comparison. -/
theorem rational_dedekindContinuation_eq_riemannZeta (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f ({1}ᶜ : Set ℂ))
    (hag : ∀ z : ℂ, 1 < z.re → f z = dedekindZeta ℚ z) :
    EqOn f riemannZeta ({1}ᶜ : Set ℂ) := by
  have htwo : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by norm_num
  apply (hf.analyticOnNhd isOpen_compl_singleton).eqOn_of_preconnected_of_eventuallyEq
    (differentiableOn_riemannZeta.analyticOnNhd isOpen_compl_singleton)
    (isConnected_compl_singleton_of_one_lt_rank (by simp [Complex.rank_real_complex]) 1).isPreconnected htwo
  have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hopen.mem_nhds (show (2 : ℂ) ∈ {z : ℂ | 1 < z.re} by norm_num)] with z hz
  exact (hag z hz).trans (dedekindZeta_rat_eq_riemannZeta hz)

/-- A right zero-free half-plane for Riemann zeta bounds both sides of the centered critical
strip, at every height, by reflection across the critical line. Both closed boundary lines
may still contain zeros. -/
theorem rational_centered_zero_band_of_riemannZeta_nonvanishing (σ : ℝ)
    (hn : ∀ z : ℂ, σ < z.re → z ≠ 1 → riemannZeta z ≠ 0) (ρ : criticalStripZetaZeros) :
    |ρ.val.re - 1/2| ≤ σ - 1/2 := by
  have hζ {z : ℂ} (hs : z ≠ 1) (hz : riemannZeta z = 0) : z.re ≤ σ := by
    apply le_of_not_gt
    intro hh
    exact hn z hh hs hz
  obtain ⟨hz, hpos, hlt⟩ := mem_criticalStripZetaZeros.mp ρ.property
  have h₁ : ρ.val ≠ 1 := fun h ↦ (ne_of_lt hlt) (by rw [h]; simp)
  have h₀ : ρ.val ≠ 0 := fun h ↦ (ne_of_gt hpos) (by rw [h]; simp)
  have href : riemannZeta (1 - ρ.val) = 0 := by
    rw [riemannZeta_one_sub _ h₁, hz, mul_zero]
    intro n he
    rw [he] at hpos
    exact (not_lt_of_ge (Nat.cast_nonneg n : (0 : ℝ) ≤ n)) (by simpa using hpos)
  have hleft := hζ (z := 1 - ρ.val) (fun he ↦ h₀ (by linear_combination -he)) href
  have hright := hζ h₁ hz
  simp only [Complex.sub_re, Complex.one_re] at hleft
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The precise rational-field conclusion of the Cureton–Thorner continuation theorem
gives a centered, closed band for all nontrivial Riemann zeta zeros. Their exponent
`σ = 31/32` yields half-width `15/32`. No bound on the height of a zero occurs. -/
theorem rational_centered_zero_band_of_dedekindContinuation (σ : ℝ)
    (h : ∃ f : ℂ → ℂ, DifferentiableOn ℂ f ({1}ᶜ : Set ℂ) ∧
      (∀ z : ℂ, 1 < z.re → f z = dedekindZeta ℚ z) ∧
      ∀ z : ℂ, σ < z.re → z ≠ 1 → f z ≠ 0) (ρ : criticalStripZetaZeros) :
    |ρ.val.re - 1/2| ≤ σ - 1/2 := by
  obtain ⟨f, hf, hag, hn⟩ := h
  apply rational_centered_zero_band_of_riemannZeta_nonvanishing σ _ ρ
  intro z hz h1
  rw [← rational_dedekindContinuation_eq_riemannZeta f hf hag h1]
  exact hn z hz h1

/-- The exact rational specialization of the published `31/32` Dedekind theorem
retains the entire order of every nontrivial zeta zero in the centered strip of
half-width `31/64 < 1/2`, for every Sobolev parameter. Its edges lie strictly
outside the closed `15/32` band. See
[Cureton–Thorner, Theorem 1.1](https://hexagonmath.org/2610.00200v2) and the
[pinned Lean solution](https://github.com/AxiomMath/DedekindZetaZeroFree/blob/09afbb4ce6570c1615d58509dc197fc9f0956b7d/Solution/DedekindZetaSolution.lean#L9-L12). -/
theorem rational_full_strip_multiplicity_of_dedekind_thirty_one_over_thirty_two
    (h : ∃ f : ℂ → ℂ, DifferentiableOn ℂ f ({1}ᶜ : Set ℂ) ∧
      (∀ z : ℂ, 1 < z.re → f z = dedekindZeta ℚ z) ∧
      ∀ z : ℂ, 31/32 < z.re → z ≠ 1 → f z ≠ 0)
    (ρ : criticalStripZetaZeros) (s : ℝ) (N : ℕ) :
    spectralStripMultiplicity (31/64) s (ρ.val.re - 1/2) N = N := by
  have hb := (abs_le.mp (rational_centered_zero_band_of_dedekindContinuation (31/32) h ρ))
  exact spectralStripMultiplicity_interior ⟨by linarith [hb.1], by linarith [hb.2]⟩ s N

end RiemannMasullo.StripNuclearity
