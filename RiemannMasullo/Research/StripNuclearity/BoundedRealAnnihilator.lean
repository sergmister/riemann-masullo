module

public import RiemannMasullo.Research.StripNuclearity.RationalPrimeFreeDiagonal
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support

/-! # Compact log profiles annihilating the rational real place

On positive log support the normalized rational real principal value has
kernel `1/(1−exp(−2t))`. Multiplication by its denominator reduces the real
term to an ordinary integral. A fourth-order differential operator then kills
that integral and both polar Mellin moments. This construction is an original
test of the comparison in §12.3.
-/

@[expose] public noncomputable section

open Function MeasureTheory NumberField Set
open scoped ContDiff Topology
open RiemannMasullo.External.Grh

namespace RiemannMasullo.StripNuclearity

/-- The Mellin polynomial with roots at both polar exponents and their shifts
by minus two. Its zero at the origin also kills the ordinary integral. -/
def boundedRealAnnihilatorSymbol (z : ℂ) : ℂ := z * (z+2) * (z-1) * (z+1)

/-- The differential operator whose Mellin action is multiplication by the
complex argument plus a prescribed scalar. -/
def mellinDifferentialFactor (c : ℂ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  c * f x - deriv f x

private theorem mellinDifferentialFactor_spec (c : ℂ) (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    let k := mellinDifferentialFactor c f
    ContDiff ℝ ∞ k ∧ HasCompactSupport k ∧ tsupport k ⊆ tsupport f ∧
      ∀ z, compactLogMellin k z = (z+c) * compactLogMellin f z := by
  intro k
  have hd : ContDiff ℝ ∞ (deriv f) := hf.deriv'
  refine ⟨(contDiff_const.mul hf).sub hd, hc.mul_left.sub hc.deriv, ?_, ?_⟩
  · refine closure_minimal (fun x hx ↦ ?_) isClosed_closure
    by_contra hout
    exact hx (by simp [k, mellinDifferentialFactor, image_eq_zero_of_notMem_tsupport hout,
      image_eq_zero_of_notMem_tsupport (fun hx ↦ hout (tsupport_deriv_subset hx))])
  · intro z
    have he : Continuous fun x : ℝ ↦ Complex.exp (z*x) := by fun_prop
    have hi : Integrable (fun x : ℝ ↦ f x * Complex.exp (z*x)) :=
      (hf.continuous.mul he).integrable_of_hasCompactSupport hc.mul_right
    have hj : Integrable (fun x : ℝ ↦ deriv f x * Complex.exp (z*x)) :=
      (hd.continuous.mul he).integrable_of_hasCompactSupport hc.deriv.mul_right
    have hder : compactLogMellin (deriv f) z = -z * compactLogMellin f z := by
      simpa only [iteratedDeriv_one, pow_one] using compactLogMellin_iteratedDeriv hf hc z 1
    change (∫ x : ℝ, (c * f x-deriv f x) * Complex.exp (z*x)) = _
    simp_rw [sub_mul, mul_assoc]
    rw [integral_sub (hi.const_mul c) hj, integral_const_mul]
    change c * compactLogMellin f z - compactLogMellin (deriv f) z = _
    rw [hder]
    ring

/-- The fourth-order constant-coefficient operator used before multiplying
by the real-place denominator. -/
def boundedRealDifferential (f : ℝ → ℂ) : ℝ → ℂ :=
  mellinDifferentialFactor 0 (mellinDifferentialFactor 2
    (mellinDifferentialFactor (-1) (mellinDifferentialFactor 1 f)))

/-- The differential operator preserves the support and realizes its quartic
Mellin multiplier at every complex argument. -/
theorem boundedRealDifferential_spec (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) :
    let k := boundedRealDifferential f
    ContDiff ℝ ∞ k ∧ HasCompactSupport k ∧ tsupport k ⊆ tsupport f ∧
      ∀ z, compactLogMellin k z = boundedRealAnnihilatorSymbol z * compactLogMellin f z := by
  obtain ⟨hd₁, hc₁, hs₁, hm₁⟩ := mellinDifferentialFactor_spec 1 f hf hc
  obtain ⟨hd₂, hc₂, hs₂, hm₂⟩ := mellinDifferentialFactor_spec (-1) _ hd₁ hc₁
  obtain ⟨hd₃, hc₃, hs₃, hm₃⟩ := mellinDifferentialFactor_spec 2 _ hd₂ hc₂
  obtain ⟨hd₄, hc₄, hs₄, hm₄⟩ := mellinDifferentialFactor_spec 0 _ hd₃ hc₃
  refine ⟨hd₄, hc₄, ((hs₄.trans hs₃).trans hs₂).trans hs₁, fun z ↦ ?_⟩
  dsimp only [boundedRealDifferential]
  rw [hm₄, hm₃, hm₂, hm₁]
  unfold boundedRealAnnihilatorSymbol
  ring

/-- A test obtained by applying the polynomial in the negative derivative
and multiplying by the denominator of the positive-log real-place kernel. -/
def boundedRealAnnihilator (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (1 - Complex.exp (-2 * (x : ℂ))) * boundedRealDifferential f x

/-- The real-place annihilator preserves smoothness and compact support, with
no enlargement of the log support. -/
theorem boundedRealAnnihilator_regularity (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) :
    ContDiff ℝ ∞ (boundedRealAnnihilator f) ∧ HasCompactSupport (boundedRealAnnihilator f) ∧
      tsupport (boundedRealAnnihilator f) ⊆ tsupport f := by
  obtain ⟨hd, hck, hs, -⟩ := boundedRealDifferential_spec f hf hc
  have he : ContDiff ℝ ∞ (fun x : ℝ ↦ 1 - Complex.exp (-2*(x : ℂ))) :=
    contDiff_const.sub (Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff))
  exact ⟨he.mul hd, hck.mul_left, tsupport_mul_subset_right.trans hs⟩

/-- The exact Mellin transform of the real-place annihilator is a difference
of polynomial multiples at the original point and the point shifted by two. -/
theorem compactLogMellin_boundedRealAnnihilator (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (z : ℂ) :
    compactLogMellin (boundedRealAnnihilator f) z =
      boundedRealAnnihilatorSymbol z * compactLogMellin f z -
        boundedRealAnnihilatorSymbol (z-2) * compactLogMellin f (z-2) := by
  obtain ⟨hd, hck, -, hm⟩ := boundedRealDifferential_spec f hf hc
  let k := boundedRealDifferential f
  have hi (w : ℂ) : Integrable (fun x : ℝ ↦ k x * Complex.exp (w*x)) :=
    (hd.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport hck.mul_right
  calc
    _ = ∫ x : ℝ, k x * Complex.exp (z*x) - k x * Complex.exp ((z-2)*x) := by
      apply integral_congr_ae (.of_forall fun x ↦ ?_)
      have he : (z-2)*(x : ℂ) = -2*x + z*x := by ring
      rw [he, Complex.exp_add]
      change ((1-Complex.exp (-2*(x : ℂ)))* k x) * _ = _
      ring
    _ = compactLogMellin k z - compactLogMellin k (z-2) := integral_sub (hi z) (hi (z-2))
    _ = _ := by rw [show compactLogMellin k z = _ from hm z, show compactLogMellin k (z-2) = _ from hm (z-2)]

/-- Both global polar moments vanish on these profiles. -/
theorem boundedRealAnnihilator_polarMoments (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) :
    compactLogMellin (boundedRealAnnihilator f) 0 = 0 ∧ compactLogMellin (boundedRealAnnihilator f) 1 = 0 := by
  constructor <;> rw [compactLogMellin_boundedRealAnnihilator f hf hc] <;>
    norm_num [boundedRealAnnihilatorSymbol]

/-- On positive log support the ordinary real-coordinate principal-value
integral of the constructed profile vanishes. -/
theorem boundedRealAnnihilator_realIntegral (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) {a b : ℝ} (ha : 0 < a) (hs : tsupport f ⊆ Icc a b) :
    (∫ x in Ioi (0 : ℝ), boundedRealAnnihilator f x / (1 - Complex.exp (-2*(x : ℂ)))) = 0 := by
  let k := boundedRealDifferential f
  obtain ⟨-, -, hks, hm⟩ := boundedRealDifferential_spec f hf hc
  have hz : compactLogMellin k 0 = 0 := by simpa [boundedRealAnnihilatorSymbol] using hm 0
  calc
    _ = ∫ x in Ioi (0 : ℝ), k x := by
      apply setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
      have hx₀ : 0 < x := hx
      have he : Complex.exp (-2 * (x : ℂ)) = (Real.exp (-2*x) : ℂ) := by
        rw [Complex.ofReal_exp]; congr 1; push_cast; ring
      have hn : (1 : ℂ) - Complex.exp (-2*(x : ℂ)) ≠ 0 := by
        rw [he]
        exact_mod_cast (sub_ne_zero.mpr (Real.exp_lt_one_iff.mpr (by linarith : -2*x < 0)).ne')
      exact mul_div_cancel_left₀ (k x) hn
    _ = ∫ x, k x := setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦
      image_eq_zero_of_notMem_tsupport fun h ↦ hx (ha.trans_le ((hks.trans hs) h).1)
    _ = 0 := by simpa only [compactLogMellin, zero_mul, Complex.exp_zero, mul_one] using hz

/-- Paper: Equations (12.5.1.2)–(12.5.1.4), pp. 519–520. The literal rational
real-place principal value vanishes for every centered Bruhat representative
of the annihilating radial profile.
Deviation: This specific differential family is an original test of the
claimed local comparison. Its real-place vanishing already holds throughout
positive log support. -/
theorem infiniteConnesWeilPrincipalValue_boundedRealAnnihilator (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) {a b : ℝ}
    (ha : 0 < a) (hs : tsupport f ⊆ Icc a b) (A : BruhatCompactSupport Rat.infinitePlace.Completionˣ)
    (hA : ∀ u, A.val u = rationalCenteredLogProfile (boundedRealAnnihilator f) (Real.log ‖u.val‖)) :
    infiniteConnesWeilPrincipalValue Rat.infinitePlace A = 0 := by
  obtain ⟨hd, -, hts⟩ := boundedRealAnnihilator_regularity f hf hc
  rw [rational_real_principalValue_positive_log_profile _ hd.continuous ha (hts.trans hs) A hA]
  exact boundedRealAnnihilator_realIntegral f hf hc ha hs

end RiemannMasullo.StripNuclearity
