module

public import RiemannMasullo.Research.TraceComparison.FiniteEulerRecovery
public import RiemannMasullo.AppC_LCTVS.Sec3a
public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # The zero-frequency coordinate of a half-twisted rational prime sieve

In log norm the relevant row has weight exp(-t/2). A half-twisted positive
translation leaves its value unchanged. On a finite band a row with that value
must pay for the norm decay of each translated global profile.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped NNReal

namespace RiemannMasullo.StripNuclearity

/-- The zero-frequency Mellin coordinate at the lower pole after the central half twist. -/
def rationalLowerPoleRow (F : ℝ → ℂ) : ℂ :=
  ∫ t : ℝ, (Real.exp (-t / 2) : ℂ) * F t

/-- Translation in log norm with the half twist preserves the lower-pole row.
Consequently a first-prime Euler difference has zero coordinate for integrable profiles. -/
theorem rationalLowerPoleRow_halfTranslation (F : ℝ → ℂ) (l : ℝ) :
    rationalLowerPoleRow (fun t ↦ (Real.exp (-l / 2) : ℂ) * F (t + l)) =
      rationalLowerPoleRow F := by
  let g := fun t : ℝ ↦ (Real.exp (-t / 2) : ℂ) * F t
  calc
    _ = ∫ t : ℝ, g (t + l) := by
      apply integral_congr_ae
      filter_upwards with t
      dsimp only [g]
      rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
      congr 3
      ring
    _ = _ := integral_add_right_eq_self g l

/-- Convolution by a translation-invariant kernel multiplies this coordinate by
the same coordinate of the kernel whenever both weighted inputs are integrable. -/
theorem rationalLowerPoleRow_convolution (k F : ℝ → ℂ)
    (hk : Integrable (fun t : ℝ ↦ (Real.exp (-t / 2) : ℂ) * k t))
    (hF : Integrable (fun t : ℝ ↦ (Real.exp (-t / 2) : ℂ) * F t)) :
    rationalLowerPoleRow (fun t ↦ ∫ r : ℝ, k r * F (t - r)) =
      rationalLowerPoleRow k * rationalLowerPoleRow F := by
  let w := fun t : ℝ ↦ (Real.exp (-t / 2) : ℂ)
  let M := ContinuousLinearMap.mul ℂ ℂ
  have hw (t r : ℝ) : w t = w r * w (t - r) := by
    dsimp only [w]
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  calc
    _ = ∫ t, convolution (fun r ↦ w r * k r) (fun r ↦ w r * F r) M volume t := by
      apply integral_congr_ae
      filter_upwards with t
      change w t * (∫ r, k r * F (t - r)) = ∫ r, (w r * k r) * (w (t - r) * F (t - r))
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with r
      rw [hw t r]
      ring
    _ = _ := integral_convolution M hk hF

/-- At the critical half-width and larger, with Sobolev order greater than one,
the squared dual weight of the lower-pole evaluation is integrable on the full line. -/
theorem integrable_rationalLowerPole_dualDensity {α s : ℝ} (hα : 1 / 2 ≤ α) (hs : 1 < s) :
    Integrable (fun t : ℝ ↦ Real.exp (-t) / intervalSobolevDensity (-α) α s t) := by
  have hdim : (Module.finrank ℝ ℝ : ℝ) < s := by simpa using hs
  refine (integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) hdim).mono' ?_
    (ae_of_all _ fun t ↦ ?_)
  · apply Measurable.aestronglyMeasurable
    unfold intervalSobolevDensity
    fun_prop
  · let M := max (Real.exp (2 * -α * t)) (Real.exp (2 * α * t))
    have hm : 0 < M := (Real.exp_pos _).trans_le (le_max_right _ _)
    have hl : Real.exp (-t) ≤ M := by
      rcases le_total t 0 with ht | ht
      · apply le_trans _ (le_max_left _ _)
        apply Real.exp_le_exp.mpr
        nlinarith [mul_nonneg (show 0 ≤ 2 * α - 1 by linarith) (neg_nonneg.mpr ht)]
      · apply le_trans _ (le_max_right _ _)
        apply Real.exp_le_exp.mpr
        nlinarith [mul_nonneg (show 0 ≤ α by linarith) ht]
    have hw : 0 < 1 + t ^ 2 := by positivity
    change ‖Real.exp (-t) / (M * (1 + t ^ 2) ^ (s/2))‖ ≤ _
    rw [Real.norm_of_nonneg (by positivity), Real.norm_eq_abs, sq_abs, neg_div,
      Real.rpow_neg hw.le]
    calc _ = (Real.exp (-t) / M) * ((1 + t ^ 2) ^ (s/2))⁻¹ := by ring
         _ ≤ _ := mul_le_of_le_one_left (by positivity) ((div_le_one hm).mpr hl)

/-- Every fixed finite Fourier-band lower support cutoff makes the dual mass
finite, including on narrower positive-width strips. -/
theorem integrableOn_rationalLowerPole_dualDensity (α s R : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s) :
    IntegrableOn (fun t : ℝ ↦ Real.exp (-t) / intervalSobolevDensity (-α) α s t) (Ici R) := by
  let d := fun t : ℝ ↦ intervalSobolevDensity (-α) α s t
  have hd (t : ℝ) : 0 < d t := by dsimp [d, intervalSobolevDensity]; positivity
  have hdc : Continuous d := by dsimp [d, intervalSobolevDensity]; fun_prop (disch := positivity)
  let f := fun t : ℝ ↦ Real.exp (-t) / d t
  have hfc : Continuous f := by
    exact (Real.continuous_exp.comp continuous_neg).div hdc (fun t ↦ (hd t).ne')
  have hcmp (t : ℝ) (ht : 0 ≤ t) : 1 ≤ d t := by
    apply one_le_mul_of_one_le_of_one_le
    · exact le_trans (Real.one_le_exp (by positivity : 0 ≤ 2 * α * t)) (le_max_right _ _)
    · exact Real.one_le_rpow (by nlinarith [sq_nonneg t]) (by positivity)
  have hpos : IntegrableOn f (Ioi 0) := by
    apply (integrableOn_exp_mul_Ioi (a := -1) (by norm_num) 0).mono'
      hfc.measurable.aestronglyMeasurable
    apply ae_restrict_of_forall_mem measurableSet_Ioi
    intro t ht
    simp only [neg_one_mul, Real.norm_eq_abs, f, abs_of_nonneg (div_nonneg (Real.exp_pos _).le (hd _).le)]
    exact div_le_self (Real.exp_pos _).le (hcmp _ ht.le)
  have hc : IntegrableOn f (Icc (min R 0) 0) volume := hfc.integrableOn_Icc
  exact (hc.union hpos).mono_set (by
    intro t ht
    rcases le_or_gt t 0 with h | h
    · exact Or.inl ⟨(min_le_left R 0).trans ht, h⟩
    · exact Or.inr h)

section RankOne

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A one-dimensional quotient picked out by an equivariant row contributes its
scalar eigenvalue to the trace. Choosing the normalized Riesz vector makes the
rank-one projection the orthogonal difference of the two nested spaces. -/
theorem hilbertTrace_normalizedRow (L : H →L[ℂ] ℂ) (w : H) (hw : L w = 1)
    (A : H →L[ℂ] H) (c : ℂ) (hA : L (A w) = c * L w) :
    ∃ h : IsNuclearOperator (A.comp (L.smulRight w)),
      hilbertTrace ⟨A.comp (L.smulRight w), h⟩ = c := by
  have he : A.comp (L.smulRight w) = L.smulRight (A w) := by
    ext x
    simp
  have hn := smulRight_mem_nuclearEndomorphisms L (A w)
  refine ⟨he ▸ hn, ?_⟩
  calc
    _ = hilbertTrace ⟨L.smulRight (A w), hn⟩ := congrArg hilbertTrace (Subtype.ext he)
    _ = L (A w) := hilbertTrace_smulRight L (A w)
    _ = c := by rw [hA, hw, mul_one]

/-- A strongly exhausting physical cutoff preserves the limiting trace of the
rank-one contribution, even when the cutoff itself does not preserve the subspace. -/
theorem tendsto_hilbertTrace_normalizedRow (L : H →L[ℂ] ℂ) {v : H} {c : ℂ}
    (hv : L v = c) (M : ℕ → H →L[ℂ] H)
    (hM : Filter.Tendsto (fun j ↦ M j v) Filter.atTop (nhds v)) :
    Filter.Tendsto (fun j ↦ hilbertTrace
      ⟨L.smulRight (M j v), smulRight_mem_nuclearEndomorphisms L (M j v)⟩)
      Filter.atTop (nhds c) := by
  have h := (L.continuous.tendsto v).comp hM
  simpa only [hilbertTrace_smulRight, hv, Function.comp_def] using h

end RankOne

section Norm

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]

variable (μ : Measure G) [μ.IsHaarMeasure] (m : G →ₜ* ℝ≥0ˣ)

set_option quotPrecheck false
local notation "t(" p ")" => Real.log ((m p).val : ℝ)
local notation "W" => (fun a b s ↦ CompactIntervalSobolev μ (fun g ↦ t(g)) a b s)

/-- Any continuous coordinate on a finite band that has a prescribed value on
an N-fold half-twisted prime translation satisfies this norm lower bound.
The row is only required to be bounded on the band containing that translate. -/
theorem finiteBand_row_value_le (a b s : ℝ) (hab : a ≤ b) (hs : 0 ≤ s)
    (p : G) (hp : 0 < t(p)) (N : ℕ) (u : W a b s) (V : Submodule ℂ (W a b s))
    (hmem : ((finiteEulerTranslation μ m a b s hab hs p) ^ N) u ∈ V) (L : V →L[ℂ] ℂ) :
    ‖L ⟨_, hmem⟩‖ ≤ ‖L‖ *
      (Real.exp (-(a + 1 / 2) * (N * t(p))) * (1 + N * t(p)) ^ (s / 2)) * ‖u‖ := by
  let T := finiteEulerTranslation μ m a b s hab hs p
  calc
    _ ≤ ‖L‖ * ‖(T ^ N) u‖ := L.le_opNorm ⟨_, hmem⟩
    _ ≤ ‖L‖ * (‖T ^ N‖ * ‖u‖) :=
      mul_le_mul_of_nonneg_left ((T ^ N).le_opNorm u) (norm_nonneg _)
    _ ≤ _ := by
      rw [← mul_assoc]
      gcongr
      exact norm_finiteEulerTranslation_pow_le μ m a b s hab hs p hp N

end Norm

end RiemannMasullo.StripNuclearity
