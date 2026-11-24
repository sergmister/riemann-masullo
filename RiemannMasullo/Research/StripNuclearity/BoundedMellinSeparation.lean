module

public import RiemannMasullo.Research.StripNuclearity.BoundedMellinTest
public import RiemannMasullo.Research.StripNuclearity.BoundedMellinWeights

/-! # Separation inside a bounded log-norm interval

When reciprocal ordinates are summable, a fixed open interval of
positive length has enough smooth tests to identify each Mellin coefficient.
The translation shifts can be made arbitrarily small in total.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory Set
open scoped BigOperators ContDiff Topology
open RiemannMasullo.External.Grh
namespace RiemannMasullo.StripNuclearity

/-- A Mellin distribution of bounded real frequencies and reciprocal-summable
ordinates is determined by smooth test profiles within any interval of positive
length. The summability assumption concerns the frequencies in this distribution,
which will be the missing zero multiplicities in the application. -/
theorem boundedWindow_mellin_coeff_eq_zero_of_re_sub_le_one {ι : Type*} (z : ι → ℂ) (hi : Injective z)
    (c : ι → ℂ) (i₀ : ι) (hz : ∀ i, (z i - z i₀).re ≤ 1)
    (hu : Summable (fun j ↦ 1/(1+|(z j-z i₀).im|))) {a b : ℝ} (hab : a < b)
    (hvan : ∀ (f : ℝ → ℂ), ContDiff ℝ (∞) f → HasCompactSupport f → tsupport f ⊆ Icc a b →
      Summable (fun j ↦ ‖c j * compactLogMellin f (z j)‖) ∧ HasSum (fun j ↦ c j * compactLogMellin f (z j)) 0) :
    c i₀ = 0 := by
  classical
  let m := (a+b)/2
  have ham : a < m := by dsimp [m]; linarith
  have hmb : m < b := by dsimp [m]; linarith
  let u (j : ι) := (z j-z i₀).im
  obtain ⟨E,hE,hsE⟩ := exists_small_mellin_shift_tail u hu (b-m) (sub_pos.mpr hmb)
  have hmiss : z i₀ ∉ (E.erase i₀).image z := by
    rintro h
    obtain ⟨i,hiE,he⟩ := Finset.mem_image.mp h
    exact (Finset.ne_of_mem_erase hiE) (hi he)
  obtain ⟨g,hg,hc,hS,h₀,hkill⟩ := exists_compactLogMellin_vanishing_on_finset (z i₀)
    ((E.erase i₀).image z) hmiss ham
  let h (j : ι) := Real.pi / |u j|
  choose P hP hP' hZ using fun j : {j // j ∉ E} ↦ exists_positive_mellin_killing_weight
    (z j.val - z i₀) (hE _ j.property)
  let p (j : ι) : ℝ := if hj : j ∉ E then P ⟨j,hj⟩ else 1
  let k (j : ι) (w : ℂ) := (p j : ℂ) + (1-(p j : ℂ)) * Complex.exp ((w - z i₀)*(h j))
  have hkill' (j : ι) (hj : j ∉ E) : k j (z j) = 0 := by
    simpa only [k, p, dif_pos hj, h, u] using hZ ⟨j,hj⟩
  have hnorm (i j : ι) (hj : j ∉ E) : ‖k j (z i)‖ ≤ Real.exp (h j) := by
    simpa only [k,p,dif_pos hj] using norm_mellin_two_point_le (z i-z i₀) (hz i)
      (show 0 ≤ h j by dsimp [h]; positivity) (hP ⟨j,hj⟩) (hP' ⟨j,hj⟩)
  let A (i : ι) := c i * compactLogMellin g (z i)
  have hsA : Summable (fun i ↦ ‖A i‖) := (hvan g hg hc (hS.trans (Icc_subset_Icc_right hmb.le))).1
  have hA : A i₀ = 0 := by
    apply coeff_eq_zero_of_bounded_finite_filters i₀ A hsA (Real.exp (b-m))
    intro T
    let D := T.filter fun j ↦ j ∉ E
    have hd {j} (hj : j ∈ D) : j ∉ E := (Finset.mem_filter.mp hj).2
    have hlen : (∑ j ∈ D, h j) ≤ b-m := hsE D (fun _ hj ↦ hd hj)
    obtain ⟨f,hfc,hfcc,hfs,hf⟩ := exists_compactLogMellin_finite_filter D h (fun j ↦ (p j : ℂ))
      (z i₀) g hg hc hS (fun j _ ↦ by dsimp [h]; positivity)
    refine ⟨fun i ↦ ∏ j ∈ D, k j (z i), ?_, ?_, ?_, ?_⟩
    · simp [k]
    · intro i hTi hne
      by_cases he : i ∈ E
      · have he' := hkill (z i) (Finset.mem_image_of_mem _ (Finset.mem_erase.mpr ⟨hne,he⟩))
        simp [A,he']
      · exact mul_eq_zero_of_right _ (Finset.prod_eq_zero (s := D) (f := fun j ↦ k j (z i))
          (Finset.mem_filter.mpr ⟨hTi,he⟩) (hkill' i he))
    · intro i
      calc
        _ = ∏ j ∈ D, ‖k j (z i)‖ := norm_prod _ _
        _ ≤ ∏ j ∈ D, Real.exp (h j) := Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _)
          (fun j hj ↦ hnorm i j (hd hj))
        _ = Real.exp (∑ j ∈ D, h j) := (Real.exp_sum _ _).symm
        _ ≤ _ := Real.exp_le_exp.mpr hlen
    · apply (hvan f hfc hfcc (hfs.trans (Icc_subset_Icc_right (by linarith)))).2.congr_fun
      intro i
      rw [hf]
      dsimp only [A,k]
      ring
  exact (mul_eq_zero.mp hA).resolve_right h₀

/-- Fixed-interval uniqueness applied to frequencies in the closed critical strip. -/
theorem boundedWindow_mellin_coeff_eq_zero {ι : Type*} (z : ι → ℂ) (hi : Injective z)
    (hz : ∀ i, (z i).re ∈ Icc (0 : ℝ) 1) (c : ι → ℂ) (i₀ : ι)
    (hu : Summable (fun j ↦ 1/(1+|(z j-z i₀).im|))) {a b : ℝ} (hab : a < b)
    (hvan : ∀ (f : ℝ → ℂ), ContDiff ℝ (∞) f → HasCompactSupport f → tsupport f ⊆ Icc a b →
      Summable (fun j ↦ ‖c j * compactLogMellin f (z j)‖) ∧ HasSum (fun j ↦ c j * compactLogMellin f (z j)) 0) :
    c i₀ = 0 :=
  boundedWindow_mellin_coeff_eq_zero_of_re_sub_le_one z hi c i₀
    (fun i ↦ by rw [Complex.sub_re]; linarith [(hz i).2, (hz i₀).1]) hu hab hvan

end RiemannMasullo.StripNuclearity
