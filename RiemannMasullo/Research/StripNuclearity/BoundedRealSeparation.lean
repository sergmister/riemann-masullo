module

public import RiemannMasullo.Research.StripNuclearity.BoundedRealAnnihilator
public import RiemannMasullo.Research.StripNuclearity.BoundedMellinSeparation
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-! # Mellin separation using only the real-place annihilator

The two polynomially weighted transforms of a test on the original strip
and its translate by minus two form a single distribution on disjoint
strips. Their ordinates coincide. Testing this distribution on any log
interval separates the coefficient at each original frequency.
-/

@[expose] public noncomputable section

open Function MeasureTheory Set
open scoped ContDiff Topology
open RiemannMasullo.External.Grh

namespace RiemannMasullo.StripNuclearity

private theorem mellin_exp_neg_two (g : ℝ → ℂ) (z : ℂ) :
    compactLogMellin (fun t : ℝ ↦ Complex.exp (-2*(t : ℂ)) * g t) z = compactLogMellin g (z-2) := by
  apply integral_congr_ae (.of_forall fun t ↦ ?_)
  have he : (z-2)*(t : ℂ) = -2*t + z*t := by ring
  rw [he, Complex.exp_add]
  ring

private theorem boundedRealAnnihilatorSymbol_ne_zero {z : ℂ} (hz : z.re ∈ Ioo (0 : ℝ) 1) :
    boundedRealAnnihilatorSymbol z ≠ 0 := by
  have hn : z ≠ 0 := fun h ↦ (by simpa only [h, Complex.zero_re, lt_self_iff_false] using hz.1 : False)
  have h₂ : z + 2 ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    norm_num [Complex.add_re] at he
    linarith [hz.1]
  have hsub : z - 1 ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    norm_num [Complex.sub_re] at he
    linarith [hz.2]
  have hadd : z + 1 ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    norm_num [Complex.add_re] at he
    linarith [hz.1]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hn h₂) hsub) hadd

/-- A distribution with frequencies in the open critical strip and
reciprocal-summable ordinates can be tested exclusively against the image of
the real-place annihilator in any fixed log interval of positive length.
Vanishing on all these tests forces the given coefficient to vanish. -/
theorem boundedWindow_realAnnihilator_coeff_eq_zero {ι : Type*} (z : ι → ℂ) (hi : Injective z)
    (hz : ∀ i, (z i).re ∈ Ioo (0 : ℝ) 1) (c : ι → ℂ) (i₀ : ι)
    (hu : Summable (fun j ↦ 1/(1+|(z j-z i₀).im|))) {a b : ℝ} (hab : a < b)
    (habs : ∀ (f : ℝ → ℂ), ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ Icc a b →
      Summable (fun j ↦ ‖c j * compactLogMellin f (z j)‖))
    (hvan : ∀ (f : ℝ → ℂ), ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ Icc a b →
      HasSum (fun j ↦ c j * compactLogMellin (boundedRealAnnihilator f) (z j)) 0) :
    c i₀ = 0 := by
  let w : ι ⊕ ι → ℂ := Sum.elim z (fun i ↦ z i - 2)
  let P := boundedRealAnnihilatorSymbol
  let d : ι ⊕ ι → ℂ := Sum.elim (fun i ↦ c i * P (z i)) (fun i ↦ -(c i * P (z i-2)))
  have horig (i j : ι) : z i ≠ z j - 2 := by
    intro h
    have he := congrArg Complex.re h
    norm_num [Complex.sub_re] at he
    linarith [(hz i).1, (hz j).2]
  have hinj : Injective w := by
    rintro (i|i) (j|j) h
    · exact congrArg Sum.inl (hi h)
    · exact False.elim (horig i j h)
    · exact False.elim (horig j i h.symm)
    · exact congrArg Sum.inr (hi (sub_left_inj.mp h))
  have hre (i : ι ⊕ ι) : (w i - w (.inl i₀)).re ≤ 1 := by
    rcases i with i|i
    · change (z i - z i₀).re ≤ 1
      rw [Complex.sub_re]
      linarith [(hz i).2, (hz i₀).1]
    · change (z i - 2 - z i₀).re ≤ 1
      simp only [Complex.sub_re, show (2 : ℂ).re = 2 by norm_num]
      linarith [(hz i).2, (hz i₀).1]
  have hrecip : Summable (fun j : ι ⊕ ι ↦ 1/(1+|(w j-w (.inl i₀)).im|)) := by
    apply Summable.sum _ hu
    simpa only [comp_def,w, Sum.elim_inl, Sum.elim_inr, Complex.sub_im, show (2 : ℂ).im = 0 by norm_num, sub_zero] using hu
  have hsep := boundedWindow_mellin_coeff_eq_zero_of_re_sub_le_one w hinj d (.inl i₀) hre hrecip hab
  apply (mul_eq_zero.mp (show c i₀ * P (z i₀) = 0 from hsep ?_)).resolve_right
    (boundedRealAnnihilatorSymbol_ne_zero (hz i₀))
  intro f hf hc hs
  let g := boundedRealDifferential f
  let v := fun t : ℝ ↦ Complex.exp (-2 * (t : ℂ)) * g t
  obtain ⟨hd, hcg, hsg, hm⟩ := boundedRealDifferential_spec f hf hc
  have hvd : ContDiff ℝ ∞ v := (Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff)).mul hd
  have hvc : HasCompactSupport v := hcg.mul_left
  have hvs : tsupport v ⊆ Icc a b := tsupport_mul_subset_right.trans (hsg.trans hs)
  let terms (j : ι ⊕ ι) := d j * compactLogMellin f (w j)
  have hleft (i : ι) : terms (.inl i) = c i * compactLogMellin g (z i) := by
    change c i * boundedRealAnnihilatorSymbol (z i) * compactLogMellin f (z i) = _
    rw [show compactLogMellin g (z i) = _ from hm (z i)]
    ring
  have hright (i : ι) : terms (.inr i) = -(c i * compactLogMellin v (z i)) := by
    change -(c i * boundedRealAnnihilatorSymbol (z i-2)) * compactLogMellin f (z i-2) = -(c i * compactLogMellin (fun t : ℝ ↦ Complex.exp (-2*(t:ℂ)) * g t) (z i))
    rw [mellin_exp_neg_two, show compactLogMellin g (z i-2) = _ from hm (z i-2)]
    ring
  have hA : Summable (fun i ↦ ‖terms (.inl i)‖) := by
    simpa only [hleft] using habs g hd hcg (hsg.trans hs)
  have hB : Summable (fun i ↦ ‖terms (.inr i)‖) := by
    simpa only [hright, norm_neg] using habs v hvd hvc hvs
  refine ⟨Summable.sum (fun j ↦ ‖terms j‖) hA hB, ?_⟩
  have htotal : HasSum (fun i ↦ terms (.inl i) + terms (.inr i)) 0 := by
    apply (hvan f hf hc hs).congr_fun
    intro i
    rw [compactLogMellin_boundedRealAnnihilator f hf hc]
    dsimp only [terms, d, w, P, Sum.elim_inl, Sum.elim_inr]
    ring
  have hl : HasSum (terms ∘ Sum.inl) (∑' i, terms (.inl i)) := hA.of_norm.hasSum
  have hr : HasSum (terms ∘ Sum.inr) (∑' i, terms (.inr i)) := hB.of_norm.hasSum
  have he := (hl.add hr).unique htotal
  exact he ▸ hl.sum hr

end RiemannMasullo.StripNuclearity
