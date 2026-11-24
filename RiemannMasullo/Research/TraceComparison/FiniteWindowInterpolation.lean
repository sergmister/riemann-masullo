module

public import RiemannMasullo.Research.TraceComparison.LogLatticePoisson
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Interpolating a finite-band rational theta profile on a physical window

In the reciprocal spatial coordinate the Poisson formula is a weighted sum of integer
dilations of the Fourier test. After normalizing its nonzero first coefficient, the
remaining dilations have scale at least two. On a window separated from zero a finite
recursion inverts this sum. A further dilation enforces the vanishing polar integral.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff FourierTransform SchwartzMap

namespace RiemannMasullo.StripNuclearity

/-- The normalized finite dilation sum in the reciprocal norm variable. -/
def windowDilationSum (D : Finset ℕ) (c : ℕ → ℂ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  f x + ∑ n ∈ D, c n * f (n * x)

private def windowInverse (D : Finset ℕ) (c : ℕ → ℂ) (g : ℝ → ℂ) : ℕ → ℝ → ℂ
  | 0 => 0
  | k + 1 => fun x ↦ g x - ∑ n ∈ D, c n * windowInverse D c g k (n * x)

private theorem dilation_scale_ge (D : Finset ℕ) (hD : ∀ n ∈ D, 2 ≤ n)
    {n : ℕ} (hn : n ∈ D) {y : ℝ} (hy : 0 ≤ y) : y ≤ (n : ℝ) * y := by
  have h : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by have := hD n hn; omega)
  exact le_mul_of_one_le_left hy h

private theorem windowInverse_stable (D : Finset ℕ) (c : ℕ → ℂ) (g : ℝ → ℂ)
    (hD : ∀ n ∈ D, 2 ≤ n) (B : ℝ) (hg : ∀ x, B ≤ |x| → g x = 0) (k : ℕ)
    {x : ℝ} (hx : 0 ≤ x) (hcut : B ≤ 2 ^ k * x) :
    windowInverse D c g (k+1) x = windowInverse D c g k x := by
  induction k generalizing x with
  | zero => simp [windowInverse, hg x (by simpa [abs_of_nonneg hx] using hcut)]
  | succ k ih =>
    simp only [windowInverse]
    apply congrArg (g x - ·)
    apply Finset.sum_congr rfl
    intro n hn
    apply congrArg (c n * ·)
    apply ih (mul_nonneg (Nat.cast_nonneg _) hx)
    have h : (2 : ℝ) ≤ n := by exact_mod_cast hD n hn
    calc B ≤ 2 ^ (k + 1) * x := hcut
         _ = 2 ^ k * (2 * x) := by ring
         _ ≤ 2 ^ k * (n * x) := by gcongr

private structure WindowTest (B : ℝ) (f : ℝ → ℂ) : Prop where
  smooth : ContDiff ℝ ∞ f
  even : ∀ x, f (-x) = f x
  origin : f 0 = 0
  outside : ∀ x, B ≤ |x| → f x = 0

private theorem windowInverse_test (D : Finset ℕ) (c : ℕ → ℂ) (g : ℝ → ℂ)
    (hD : ∀ n ∈ D, 2 ≤ n) (B : ℝ) (hg : WindowTest B g) (k : ℕ) :
    WindowTest B (windowInverse D c g k) := by
  induction k with
  | zero => exact ⟨contDiff_const, fun _ ↦ rfl, rfl, fun _ _ ↦ rfl⟩
  | succ k ih =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · dsimp only [windowInverse]
      apply hg.smooth.sub
      apply ContDiff.sum
      intro n _
      have H := ih.smooth
      fun_prop
    · intro x
      simp [windowInverse, hg.even, mul_neg, ih.even]
    · simp [windowInverse, hg.origin, ih.origin]
    · intro x hx
      dsimp only [windowInverse]
      rw [hg.outside x hx]
      suffices h : (∑ n ∈ D, c n * windowInverse D c g k (n * x)) = 0 by simp [h]
      apply Finset.sum_eq_zero
      intro n hn
      have hnx : B ≤ |(n : ℝ) * x| := by
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
        exact hx.trans (dilation_scale_ge D hD hn (abs_nonneg x))
      rw [ih.outside _ hnx, mul_zero]

private theorem windowTest_compact {B : ℝ} {f : ℝ → ℂ} (hf : WindowTest B f) :
    HasCompactSupport f := by
  apply HasCompactSupport.intro (K := Icc (-B) B) isCompact_Icc
  intro x hx
  apply hf.outside
  by_contra! h
  exact hx ⟨(abs_lt.mp h).1.le, (abs_lt.mp h).2.le⟩

/-- A smooth, even band profile vanishing at zero can be interpolated on the entire
window x ≥ a by a normalized finite dilation sum. The interpolating test stays in
the same band, vanishes at zero and has integral exactly zero. -/
theorem exists_polarFree_windowDilation_interpolant (D : Finset ℕ) (c : ℕ → ℂ)
    (hD : ∀ n ∈ D, 2 ≤ n) {a B : ℝ} (ha : 0 < a) (hB : 0 < B)
    (g : ℝ → ℂ) (hsmooth : ContDiff ℝ ∞ g) (heven : ∀ x, g (-x) = g x)
    (hzero : g 0 = 0) (hband : ∀ x, B ≤ |x| → g x = 0) :
    ∃ f : ℝ → ℂ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ (∀ x, f (-x) = f x) ∧
      f 0 = 0 ∧ (∀ x, B ≤ |x| → f x = 0) ∧ (∫ x : ℝ, f x) = 0 ∧
      ∀ x, a ≤ x → windowDilationSum D c f x = g x := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (B/a) (by norm_num : (1 : ℝ) < 2)
  let u := windowInverse D c g k
  have hu : WindowTest B u := windowInverse_test D c g hD B ⟨hsmooth, heven, hzero, hband⟩ k
  have heq (x : ℝ) (hx : a ≤ x) : windowDilationSum D c u x = g x := by
    have hst := windowInverse_stable D c g hD B hband k (ha.le.trans hx)
      (((div_lt_iff₀ ha).mp hk).le.trans (mul_le_mul_of_nonneg_left hx (by positivity)))
    change g x - (∑ n ∈ D, c n * u (n * x)) = u x at hst
    exact (eq_sub_iff_add_eq.mp hst.symm)
  let r : ℝ := 1 + B/a
  have hr : 1 ≤ r := le_add_of_nonneg_right (div_nonneg hB.le ha.le)
  have hr₀ : 0 < r := zero_lt_one.trans_le hr
  have hra : B ≤ r * a := by dsimp [r]; rw [add_mul, div_mul_cancel₀ _ ha.ne']; linarith
  let f := fun x : ℝ ↦ u x - r • u (r * x)
  have hf : WindowTest B f := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · have H := hu.smooth
      dsimp only [f]
      fun_prop
    · intro x
      simp [f, mul_neg, hu.even]
    · simp [f, hu.origin]
    · intro x hx
      have hrx : B ≤ |r*x| := by
        rw [abs_mul, abs_of_pos hr₀]
        exact hx.trans (le_mul_of_one_le_left (abs_nonneg _) hr)
      simp [f, hu.outside x hx, hu.outside _ hrx]
  refine ⟨f, hf.smooth, windowTest_compact hf, hf.even, hf.origin, hf.outside, ?_, ?_⟩
  · have hi : Integrable u volume := hu.smooth.continuous.integrable_of_hasCompactSupport (windowTest_compact hu)
    have hi' : Integrable (fun x : ℝ ↦ u (r*x)) := (integrable_comp_mul_left_iff _ hr₀.ne').2 hi
    rw [show (∫ x : ℝ, f x) = _ from integral_sub hi (hi'.smul r), integral_smul,
      Measure.integral_comp_mul_left, abs_of_pos (inv_pos.mpr hr₀), smul_smul,
      mul_inv_cancel₀ hr₀.ne', one_smul, sub_self]
  · have agrees (x : ℝ) (hx : a ≤ x) : f x = u x := by
      have hrx : B ≤ |r*x| := by
        rw [abs_of_nonneg (mul_nonneg hr₀.le (ha.le.trans hx))]
        exact hra.trans (mul_le_mul_of_nonneg_left hx hr₀.le)
      have hz := hu.outside (r*x) hrx
      simp [f, hz]
    intro x hx
    rw [← heq x hx]
    unfold windowDilationSum
    rw [agrees x hx]
    apply congrArg (u x + ·)
    apply Finset.sum_congr rfl
    exact fun n hn ↦ congrArg (c n * ·) (agrees _ (hx.trans
      (dilation_scale_ge D hD hn (ha.le.trans hx))))


/-- On the reciprocal window ξ ≥ a, an actual even Schwartz theta sum over the
integers interpolates the prescribed band profile. The physical test vanishes at
zero, and its Fourier transform vanishes at zero and outside the chosen band.
The spatial norm is x = 1/ξ. -/
theorem exists_rational_theta_window_interpolant {a B : ℝ} (ha : 0 < a) (hB : 0 < B)
    (g : ℝ → ℂ) (hsmooth : ContDiff ℝ ∞ g) (heven : ∀ x, g (-x) = g x)
    (hzero : g 0 = 0) (hband : ∀ x, B ≤ |x| → g x = 0) :
    ∃ f : 𝓢(ℝ, ℂ), (∀ x, f (-x) = f x) ∧ f 0 = 0 ∧ (𝓕 f) 0 = 0 ∧
      (∀ x, B ≤ |x| → (𝓕 f) x = 0) ∧
      ∀ ξ, a ≤ ξ → HasSum (fun n : ℤ ↦ f ((n : ℝ) / ξ)) ((ξ : ℂ) * (2 * g ξ)) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (B/a)
  let D := Finset.Icc 2 N
  have hD (n : ℕ) (hn : n ∈ D) : 2 ≤ n := (Finset.mem_Icc.mp hn).1
  obtain ⟨h, hsm, hc, he, h0, hlim, hI, hinv⟩ :=
    exists_polarFree_windowDilation_interpolant D (fun _ ↦ 1) hD ha hB g hsmooth heven hzero hband
  let H : 𝓢(ℝ, ℂ) := hc.toSchwartzMap hsm
  have hH (t : ℝ) : H t = h t := rfl
  let f := 𝓕⁻ H
  have hF : 𝓕 f = H := FourierTransform.fourier_fourierInv_eq _
  have hneg : (fun x : ℝ ↦ H (-x)) = H := funext he
  have hself : f = 𝓕 H := by
    ext x
    rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_comp_neg, hneg, SchwartzMap.fourier_coe]
  refine ⟨f, ?_, ?_, hF ▸ h0, ?_, ?_⟩
  · intro x
    change (𝓕 H) (- -x) = f x
    rw [neg_neg, hself]
  · rw [hself, SchwartzMap.fourier_coe, Real.fourier_real_eq]
    simpa [H] using hI
  · rw [hF]
    exact hlim
  · intro ξ hξ
    have hpos := ha.trans_le hξ
    let v : ℕ → ℂ := fun n ↦ h (n * ξ)
    have hv (n : ℕ) (hn : n ∉ insert 1 D) : v n = 0 := by
      by_cases hn0 : n = 0
      · simp [v, hn0, h0]
      have hn1 : n ≠ 1 := fun e ↦ hn (e ▸ Finset.mem_insert_self 1 D)
      have hn2 : 2 ≤ n := by omega
      have hnN : N < n := by
        by_contra! hnN
        exact hn (Finset.mem_insert_of_mem (Finset.mem_Icc.mpr ⟨hn2, hnN⟩))
      apply hlim
      rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hpos.le)]
      calc B ≤ (N : ℝ) * a := ((div_lt_iff₀ ha).mp hN).le
           _ ≤ n * ξ := by gcongr
    have hsum : (∑' n : ℕ, v n) = g ξ := by
      rw [tsum_eq_sum hv, Finset.sum_insert (show 1 ∉ D by simp [D])]
      simpa [v, windowDilationSum] using hinv ξ hξ
    have hpossum : HasSum (fun n : ℕ+ ↦ v n.val) (g ξ) := by
      apply hasSum_pnat_iff.mpr
      have hfull : Summable v := summable_of_ne_finset_zero hv
      have hnat : HasSum v (g ξ) := hsum ▸ hfull.hasSum
      have hv0 : v 0 = 0 := by simp [v, h0]
      simpa only [hv0, add_zero] using hnat
    have hZ : Summable (fun n : ℤ ↦ H (n * ξ)) := by
      simpa only [hF, div_inv_eq_mul] using
        (hasSum_fourier_logLattice f (inv_pos.mpr hpos)).summable
    have hsym : Function.Even (fun n : ℤ ↦ H (n * ξ)) := by
      intro n
      change H (((-n : ℤ) : ℝ) * ξ) = H ((n : ℝ) * ξ)
      simpa only [Int.cast_neg, neg_mul, hH] using he ((n : ℝ) * ξ)
    have hZsum : (∑' n : ℤ, H (n * ξ)) = 2 * g ξ := by
      rw [tsum_int_eq_zero_add_two_mul_tsum_pnat hsym hZ]
      simp only [Int.cast_zero, zero_mul, Int.cast_natCast, hH, h0, zero_add, nsmul_eq_mul, Nat.cast_ofNat]
      change 2 * (∑' n : ℕ+, v n.val) = 2 * g ξ
      rw [hpossum.tsum_eq]
    rw [hself, ← hZsum]
    exact hasSum_fourier_logLattice H hpos

end RiemannMasullo.StripNuclearity
