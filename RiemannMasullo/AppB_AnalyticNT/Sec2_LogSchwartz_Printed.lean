module

public import RiemannMasullo.AppB_AnalyticNT.Sec2
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! # Appendix B.2: printed assertions about growth and decay in logarithmic coordinates -/

@[expose] public noncomputable section

namespace RiemannMasullo

open Filter Set
open scoped Asymptotics SchwartzMap

/-- Paper: Remark B.2.1.2, p. 593.
As printed: for a Schwartz logarithmic profile, the condition that every derivative is
`O(exp(-x))` as `x` tends to positive infinity suffices for forward semi-exponential decay.
This is the false direction of the printed correspondence. The equivalence with all Schwartz
weights is `forwardSemiExponentialDecay_iff_weighted_schwartz`. See ERRATA F224. -/
def Printed.forwardSemiExponentialDecay_of_single_rate : Prop :=
  ∀ f : 𝓢(ℝ, ℂ),
    (∀ j : ℕ, (iteratedDeriv j (f : ℝ → ℂ)) =O[atTop] fun x ↦ Real.exp (-x)) →
    ForwardSemiExponentialDecay f

/-- A Schwartz exponential cutoff, with a zero left tail and exact exponential right tail. -/
private theorem forwardSemiExponentialDecay_of_single_rate_cutoff :
    ∃ f : SchwartzMap ℝ ℂ, (∀ x : ℝ, 0 ≤ x → f x = (Real.exp (-x) : ℂ)) ∧ (∀ x : ℝ, x ≤ -1 → f x = 0) := by
  let g (x : ℝ) := Real.smoothTransition (x + 1) * Real.exp (-x)
  have hs : ContDiff ℝ (↑(⊤ : ℕ∞)) g := (Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)).mul
    (Real.contDiff_exp.comp contDiff_id.neg)
  have hpos (x : ℝ) (hx : 0 ≤ x) : g x = Real.exp (-x) := by
    simp [g, Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ x + 1)]
  have hneg (x : ℝ) (hx : x ≤ -1) : g x = 0 := by
    simp [g, Real.smoothTransition.zero_of_nonpos (by linarith : x + 1 ≤ 0)]
  have hd (n : ℕ) : iteratedDeriv n (fun x : ℝ ↦ Real.exp (-x)) =
      fun x : ℝ ↦ (-1 : ℝ) ^ n * Real.exp (-x) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      have d := ((hasDerivAt_id x).neg.exp.const_mul ((-1 : ℝ) ^ n)).deriv
      simpa [pow_succ, mul_assoc] using d
  let f : SchwartzMap ℝ ℝ :=
    { toFun := g, smooth' := hs
      decay' := by
        intro k n
        let w (x : ℝ) := ‖x‖ ^ k * ‖iteratedDeriv n g x‖
        have hw : Continuous w := (continuous_norm.pow _).mul
          (hs.continuous_iteratedDeriv n (by simp)).norm
        obtain ⟨M, hM⟩ := (isCompact_Icc (α := ℝ) (a := -1) (b := 0)).bddAbove_image hw.continuousOn
        refine ⟨max 0 (max M k.factorial), fun x ↦ ?_⟩
        rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
        rcases lt_or_ge x (-1) with hx | hx
        · have h : g =ᶠ[nhds x] fun _ ↦ (0 : ℝ) :=
            (gt_mem_nhds hx).mono fun y hy ↦ hneg y hy.le
          rw [(h.iteratedDeriv n).eq_of_nhds]
          simp
        rcases le_or_gt x 0 with hx' | hx'
        · exact (hM ⟨x, ⟨hx, hx'⟩, rfl⟩).trans ((le_max_left _ _).trans (le_max_right _ _))
        · have h : g =ᶠ[nhds x] fun y ↦ Real.exp (-y) :=
            (lt_mem_nhds hx').mono fun y hy ↦ hpos y hy.le
          rw [(h.iteratedDeriv n).eq_of_nhds, hd]
          simp only [Real.norm_eq_abs, abs_of_pos hx', Real.exp_neg, ← div_eq_mul_inv]
          apply le_trans _ ((le_max_right _ _).trans (le_max_right _ _))
          rw [abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_of_pos (Real.exp_pos _), mul_one_div]
          apply (div_le_iff₀ (Real.exp_pos _)).mpr
          exact (div_le_iff₀ (Nat.cast_pos.mpr (Nat.factorial_pos _))).mp
            (Real.pow_div_factorial_le_exp x hx'.le k) |>.trans_eq (mul_comm _ _) }
  exact ⟨f.postcompCLM Complex.ofRealCLM, (fun x hx ↦ congrArg Complex.ofReal (hpos x hx)), fun x hx ↦ by
    change (g x : ℂ) = 0
    rw [hneg x hx, Complex.ofReal_zero]⟩


/-- Paper: Remark B.2.1.2, p. 593.
Use the smooth cutoff `χ(t) = Real.smoothTransition (t - 1)`, zero for `t ≤ 1` and one
for `t ≥ 2`.
The logarithmic profile of `φ(t) = χ(t)/t` is Schwartz. For `x ≥ log 2` its `j`-th
derivative is `(-1)^j exp(-x)`, and the zeroth derivative fails the rate `exp(-2x)`. -/
theorem Printed.forwardSemiExponentialDecay_of_single_rate_false :
    ¬ Printed.forwardSemiExponentialDecay_of_single_rate := by
  obtain ⟨f, hf, hz⟩ := forwardSemiExponentialDecay_of_single_rate_cutoff
  let E : ℝ → ℂ := fun x ↦ (Real.exp (-x) : ℂ)
  have hd (j : ℕ) : iteratedDeriv j E = fun x ↦ (↑((-1 : ℝ) ^ j * Real.exp (-x)) : ℂ) := by
    induction j with
    | zero => simp [E]
    | succ j ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      simpa [pow_succ, mul_assoc, mul_neg] using
        (((hasDerivAt_id x).neg.exp.const_mul ((-1 : ℝ) ^ j)).ofReal_comp.deriv)
  have he (j : ℕ) : iteratedDeriv j (f : ℝ → ℂ) =ᶠ[atTop] iteratedDeriv j E := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    apply Filter.EventuallyEq.iteratedDeriv_eq j
    filter_upwards [lt_mem_nhds hx] with y hy
    exact hf y hy.le
  have hb (j : ℕ) : iteratedDeriv j (f : ℝ → ℂ) =O[atTop] fun x ↦ Real.exp (-x) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [he j] with x hx
    rw [hx, hd]
    simp only [Complex.norm_real, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_of_nonneg (Real.exp_pos _).le, le_refl]
  intro h
  have hh := (h f hb) 0 2 (by norm_num)
  rw [iteratedDeriv_zero] at hh
  have hr : (fun x : ℝ ↦ Real.exp (-x)) =O[atTop] fun x ↦ Real.exp (-2 * x) := by
    have hn := hh.norm_left
    apply hn.congr' _ Filter.EventuallyEq.rfl
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    rw [hf x hx, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  have hbounded := Real.isBigO_exp_comp_exp_comp.mp hr
  have hfun : (fun x : ℝ ↦ -x) - (fun x : ℝ ↦ -2 * x) = fun x ↦ x := by funext x; dsimp; ring
  rw [hfun] at hbounded
  exact (Filter.not_isBoundedUnder_of_tendsto_atTop tendsto_id) hbounded

/-- Paper: Remark B.2.1.3, p. 593.
As printed: if a complex-valued function on the positive reals has at most polynomial
growth in the logarithmic coordinate, then for every natural exponent `N` it admits a bound
`C_N |log t|^N` for all positive `t`. This is the false direction of the identification with
the usual polynomial growth condition on the real line. See ERRATA F224. -/
def Printed.logPolynomialGrowth_bound_for_every_exponent : Prop :=
  ∀ f : Ioi (0 : ℝ) → ℂ,
    (∃ (M : ℕ) (C : ℝ), 0 < C ∧ ∀ t : Ioi (0 : ℝ),
      ‖f t‖ ≤ C * (1 + |Real.log t.val|) ^ M) →
    ∀ N : ℕ, ∃ C > (0 : ℝ), ∀ t : Ioi (0 : ℝ), ‖f t‖ ≤ C * |Real.log t.val| ^ N

/-- Paper: Remark B.2.1.3, p. 593.
Take the constant function `1`, with degree zero and constant one in the usual polynomial
growth bound. The printed bound with `N = 1` at `t = 1` would give `1 ≤ 0`. -/
theorem Printed.logPolynomialGrowth_bound_for_every_exponent_false :
    ¬ Printed.logPolynomialGrowth_bound_for_every_exponent := by
  intro h
  obtain ⟨C, _, hC⟩ := h (fun _ ↦ 1) ⟨0, 1, zero_lt_one, by simp⟩ 1
  have hbad := hC ⟨1, zero_lt_one⟩
  norm_num at hbad

/-- Paper: Lemma B.2.1.4(1), p. 593.
As printed: every Schwartz profile on the positive reals with backward semi-exponential decay
has a Schwartz zero extension to the real line. The smoothness assertion is
`contDiff_zeroExtension_of_backwardSemiExponentialDecay`. The stronger decay hypothesis
in part (3) gives `exists_schwartz_zeroExtension_of_exponentialDecay`. See ERRATA F224. -/
def Printed.exists_schwartz_zeroExtension_of_backwardSemiExponentialDecay : Prop :=
  ∀ f : 𝓢(ℝ, ℂ), BackwardSemiExponentialDecay f →
    ∃ g : 𝓢(ℝ, ℂ), (g : ℝ → ℂ) = (Ioi (0 : ℝ)).indicator (fun t ↦ f (Real.log t))

/-- Paper: Lemma B.2.1.4(1), p. 593.
Take the logarithmic profile `f(x) = χ(exp x) exp(-x)`, with `χ(t) = Real.smoothTransition (t - 1)`.
It vanishes for `x ≤ 0` and is Schwartz in `x`. Its zero extension in the `t` coordinate
equals `1/t` for `t ≥ 2`, so the weight `t²` makes it unbounded. -/
theorem Printed.exists_schwartz_zeroExtension_of_backwardSemiExponentialDecay_false :
    ¬ Printed.exists_schwartz_zeroExtension_of_backwardSemiExponentialDecay := by
  obtain ⟨f, hf, hz⟩ := forwardSemiExponentialDecay_of_single_rate_cutoff
  have hb : BackwardSemiExponentialDecay f := by
    intro j A hA
    apply Asymptotics.IsBigO.of_bound 0
    filter_upwards [eventually_lt_atBot (-1 : ℝ)] with x hx
    have he : (f : ℝ → ℂ) =ᶠ[nhds x] (0 : ℝ → ℂ) := by
      filter_upwards [gt_mem_nhds hx] with y hy
      exact hz y hy.le
    rw [he.iteratedDeriv_eq j]
    simp
  intro h
  obtain ⟨g, hg⟩ := h f hb
  obtain ⟨C, hC, hbound⟩ := g.decay 2 0
  let t := C + 1
  have ht : 0 < t := by dsimp [t]; linarith
  have ht1 : 1 ≤ t := by dsimp [t]; linarith
  have hgt : g t = (t⁻¹ : ℝ) := by
    rw [show g t = ((Ioi (0 : ℝ)).indicator (fun u ↦ f (Real.log u))) t from congrFun hg t]
    rw [indicator_of_mem ht, hf _ (Real.log_nonneg ht1), Real.exp_neg, Real.exp_log ht]
  have hh := hbound t
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_zero, hgt] at hh
  simp only [Real.norm_eq_abs, Complex.norm_real, abs_inv, abs_of_pos ht] at hh
  have heq : t ^ 2 * t⁻¹ = t := by field_simp
  rw [heq] at hh
  dsimp [t] at hh
  linarith

end RiemannMasullo
