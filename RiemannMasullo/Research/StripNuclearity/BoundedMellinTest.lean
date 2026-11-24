module

public import RiemannMasullo.External.Grh.Lemmas.CompactLogMellin
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Group.Integral

/-! # Finite Mellin filters on a bounded log interval

Differentiating a compactly supported profile multiplies its Mellin transform
by the negative of the complex argument. A weighted translation gives a
two-term exponential multiplier. These two operations prescribe finite sets
of zeros and keep explicit control of the support of the test.
-/

@[expose] public noncomputable section

open Function MeasureTheory Set
open scoped ContDiff Topology
open RiemannMasullo.External.Grh

namespace RiemannMasullo.StripNuclearity

private theorem mellin_linear (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g)
    (hcf : HasCompactSupport f) (hcg : HasCompactSupport g) (c d z : ℂ) :
    compactLogMellin (fun x ↦ c * f x + d * g x) z =
      c * compactLogMellin f z + d * compactLogMellin g z := by
  have hE : Continuous (fun x : ℝ ↦ Complex.exp (z * x)) := by fun_prop
  have hi : Integrable (fun x : ℝ ↦ f x * Complex.exp (z*x)) :=
    (hf.mul hE).integrable_of_hasCompactSupport hcf.mul_right
  have hj : Integrable (fun x : ℝ ↦ g x * Complex.exp (z*x)) :=
    (hg.mul hE).integrable_of_hasCompactSupport hcg.mul_right
  simp only [compactLogMellin, add_mul, mul_assoc]
  rw [integral_add (hi.const_mul c) (hj.const_mul d), integral_const_mul, integral_const_mul]

private theorem mellin_translate (f : ℝ → ℂ) (y : ℝ) (z : ℂ) :
    compactLogMellin (fun t ↦ f (t-y)) z = compactLogMellin f z * Complex.exp (z*y) := by
  let H (t : ℝ) := f t * Complex.exp (z*t) * Complex.exp (z*y)
  calc
    _ = ∫ t : ℝ, H (t-y) := by
      apply integral_congr_ae (.of_forall fun t ↦ ?_)
      have he : z * (t : ℂ) = z * ((t-y : ℝ) : ℂ) + z*y := by push_cast; ring
      dsimp only [H]
      rw [he, Complex.exp_add, mul_assoc]
    _ = ∫ t : ℝ, H t := integral_sub_right_eq_self H y
    _ = _ := integral_mul_const _ _

/-- A compact smooth profile in any nondegenerate closed interval separates the
target exponent from any finite set of other exponents. The derivative
operators preserve its support. -/
theorem exists_compactLogMellin_vanishing_on_finset (z₀ : ℂ) (T : Finset ℂ) (hT : z₀ ∉ T)
    {a b : ℝ} (hab : a < b) :
    ∃ g : ℝ → ℂ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ tsupport g ⊆ Icc a b ∧
      compactLogMellin g z₀ ≠ 0 ∧ ∀ z ∈ T, compactLogMellin g z = 0 := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    let β : ContDiffBump ((a+b)/2) := ⟨(b-a)/8, (b-a)/4, by linarith, by linarith⟩
    let g (x : ℝ) := (β x : ℂ) * Complex.exp (-(z₀*x))
    have hd : ContDiff ℝ ∞ g := (Complex.ofRealCLM.contDiff.comp β.contDiff).mul
      (Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff).neg)
    refine ⟨g, hd, (β.hasCompactSupport.comp_left Complex.ofReal_zero).mul_right, ?_, ?_, by simp⟩
    · refine closure_minimal (fun x hx ↦ ?_) isClosed_Icc
      have hdist : dist x ((a+b)/2) < (b-a)/4 := by
        by_contra! h
        exact hx (by simp [g, β.zero_of_le_dist h])
      rw [Real.dist_eq, abs_lt] at hdist
      exact ⟨by linarith [hdist.1], by linarith [hdist.2]⟩
    · have hM : compactLogMellin g z₀ = ((∫ t, β t : ℝ) : ℂ) := by
        rw [← integral_complex_ofReal]
        apply integral_congr_ae (.of_forall fun x ↦ ?_)
        simp only [g, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
      exact hM ▸ Complex.ofReal_ne_zero.mpr β.integral_pos.ne'
  | @insert w T hw ih =>
    obtain ⟨g, hg, hc, hs, hn, hvan⟩ := ih (fun h ↦ hT (Finset.mem_insert_of_mem h))
    have hd : ContDiff ℝ ∞ (deriv g) := hg.deriv'
    let f := fun x ↦ (1 : ℂ) * deriv g x + w * g x
    have hM (z : ℂ) : compactLogMellin f z = (w-z) * compactLogMellin g z := by
      have hder := compactLogMellin_iteratedDeriv hg hc z 1
      simp only [iteratedDeriv_one, pow_one] at hder
      rw [show compactLogMellin f z = _ from
        mellin_linear (deriv g) g hd.continuous hg.continuous hc.deriv hc 1 w z, hder]
      ring
    refine ⟨f, (contDiff_const.mul hd).add (contDiff_const.mul hg),
      hc.deriv.mul_left.add hc.mul_left, ?_, ?_, ?_⟩
    · refine closure_minimal (fun x hx ↦ ?_) isClosed_Icc
      by_contra h
      have hout : x ∉ tsupport g := fun hx ↦ h (hs hx)
      exact hx (by simp [f, image_eq_zero_of_notMem_tsupport hout,
        image_eq_zero_of_notMem_tsupport (fun hx ↦ hout (tsupport_deriv_subset hx))])
    · rw [hM]
      exact mul_ne_zero (sub_ne_zero.mpr (fun e ↦ hT (e ▸ Finset.mem_insert_self _ _))) hn
    · intro z hz
      rw [hM]
      rcases Finset.mem_insert.mp hz with rfl | h
      · simp
      · rw [hvan z h, mul_zero]

/-- A finite product of two-point exponential factors is the Mellin multiplier
of a compact smooth profile. Nonnegative shifts increase only the right end
of the given support interval, by at most their sum. -/
theorem exists_compactLogMellin_finite_filter {ι : Type*} (T : Finset ι) (h : ι → ℝ)
    (p : ι → ℂ) (z₀ : ℂ) (g : ℝ → ℂ) {a b : ℝ}
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (hs : tsupport g ⊆ Icc a b)
    (hh : ∀ i ∈ T, 0 ≤ h i) :
    ∃ f : ℝ → ℂ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      tsupport f ⊆ Icc a (b + ∑ i ∈ T, h i) ∧ ∀ z, compactLogMellin f z =
        compactLogMellin g z * ∏ i ∈ T, (p i + (1-p i) * Complex.exp ((z-z₀)*(h i : ℂ))) := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨g, hg, hc, by simpa using hs, by simp⟩
  | @insert i T hi ih =>
    obtain ⟨f, hd, hcf, hsf, hMf⟩ := ih (fun j hj ↦ hh j (Finset.mem_insert_of_mem hj))
    let t := h i
    let d := (1-p i) * Complex.exp (-(z₀*t))
    let u (x : ℝ) := f (x-t)
    let k (x : ℝ) := p i * f x + d * u x
    have hdu : ContDiff ℝ ∞ u := hd.comp (contDiff_id.sub contDiff_const)
    have hcu : HasCompactSupport u := hcf.comp_homeomorph (Homeomorph.subRight t)
    have ht : 0 ≤ t := hh i (Finset.mem_insert_self _ _)
    refine ⟨k, (contDiff_const.mul hd).add (contDiff_const.mul hdu), hcf.mul_left.add hcu.mul_left, ?_, ?_⟩
    · rw [Finset.sum_insert hi]
      refine closure_minimal (fun x hx ↦ ?_) isClosed_Icc
      by_contra hout
      have hOld : x ∉ tsupport f := fun hx ↦ hout ⟨(hsf hx).1, by linarith [(hsf hx).2]⟩
      have hNew : x - t ∉ tsupport f := fun hx ↦ hout
        ⟨by linarith [(hsf hx).1], by linarith [(hsf hx).2]⟩
      exact hx (by simp [k, u, image_eq_zero_of_notMem_tsupport hOld, image_eq_zero_of_notMem_tsupport hNew])
    · intro z
      have he : Complex.exp (-(z₀*t)) * Complex.exp (z*t) = Complex.exp ((z-z₀)*t) := by
        rw [← Complex.exp_add]
        congr 1
        ring
      rw [show compactLogMellin k z = _ from
        mellin_linear f u hd.continuous hdu.continuous hcf hcu (p i) d z,
        show compactLogMellin u z = _ from mellin_translate f t z, hMf, Finset.prod_insert hi]
      dsimp only [d]
      linear_combination (1-p i) * compactLogMellin g z *
        (∏ j ∈ T, (p j + (1-p j) * Complex.exp ((z-z₀)*(h j : ℂ)))) * he

end RiemannMasullo.StripNuclearity
