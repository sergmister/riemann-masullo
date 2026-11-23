module

public import RiemannMasullo.Ch13_ZerosHecke.Sec3
public import RiemannMasullo.AppB_AnalyticNT.Sec6
import RiemannMasullo.External.TauCeti.Analysis.Complex.Conformal.Montel.Basic
import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.AppB_AnalyticNT.Sec4b

import all RiemannMasullo.Ch07_SchauderBasesZeta.Sec5
import all RiemannMasullo.Ch03_IdelicZeta.Sec2
import all RiemannMasullo.AppD_SchwartzBruhat.Sec3b

/-! # From the trace formula to GRH

Masullo, §1.4, pp. 27–31, repeated in §§1.8.4–1.8.5. The introductory trace
identity recurs as Theorem 12.5.1.1. The centered version is `traceFormula`.
The page 28 display uses an uncentered zero window. Its literal form is
`Printed.introTrace_globalTrace` in the companion file. The passage from the
trace identity to the zero-free region requires limits of the trace terms.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 instNormOneIdeleClassMeasurableSec4b

variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "U𝔽" => PontryaginDual C𝔽
local notation "D𝔽" => BruhatCompactSupport C𝔽
local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "q(" v ")" => ((v : V).asIdeal.absNorm : ℝ)
local notation "N(" g ")" => (((ideleClassNorm F) (g : C𝔽)).val : ℝ)
local notation "right(" a ")" => (Complex.re ⁻¹' Ioi (a : ℝ))
local notation "τVolume" => (((normOneIdeleClassTamagawaMeasure F) univ).toReal : ℂ)
local notation "finiteL(" χ ")" => (finiteHeckeL_exists_continuation (F := F) χ).choose
local notation "zeroOrder(" χ ", " s ")" =>
  MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ s
local notation "windowZeros(" χ ", " a ")" =>
  {s : ℂ // 0 < zeroOrder(χ, s) ∧ |s.re - 1 / 2| < (a : ℝ)}

-- TODO(paper-gap): The “Finish!” footnotes on p. 27 belong to §§1.3.3–1.3.4.
-- The deduction here inherits the unfinished kernel comparisons in those subsections.
-- The centered window in §1.8.4, p. 53, agrees with the shift in §1.4.3.

section CharacterTrace

/-- Paper: §1.4.1, p. 28. A radial profile gives a test of norm-one weight
conjugate to the character by multiplication by that conjugate on the idele classes.
Deviation: The conjugate is required by the stated weight and by the zero Mellin
pairing. The product in the prose of §§1.4.2–1.4.3 uses the character itself. -/
def introTraceTest (χ : U𝔽) (h : ℝ → ℂ) (g : C𝔽) : ℂ :=
  (star (χ g : ℂ)) * h (N(g))

/-- Paper: §1.4.1, p. 28. Right translation by a norm-one class multiplies the
test by the conjugate character value on that class. -/
theorem introTraceTest_mul_normOne (χ : U𝔽) (h : ℝ → ℂ)
    (g : C𝔽) (u : (ideleClassNorm F).ker) :
    introTraceTest χ h (g * u.val) = star (χ u.val : ℂ) * introTraceTest χ h g := by
  have hu : ideleClassNorm F u.val = 1 := u.property
  simp only [introTraceTest, map_mul, hu, mul_one, Circle.coe_mul, star_mul]
  ac_rfl

/-- Paper: §1.4.1, p. 28. Mathlib's Mellin moment of the radial profile uses the
positive norm coordinate with Haar density `dt/t`. -/
def introTraceMellin (h : ℝ → ℂ) (s : ℂ) : ℂ :=
  mellin h s

/-- Paper: §1.4.1, p. 28. In the selected isotype the global Mellin integral
exists and is the radial moment times the norm-one Tamagawa volume. -/
theorem introTraceTest_mellin (χ : U𝔽) (h : ℝ → ℂ) (φ : D𝔽)
    (_hφ : ∀ g, φ.val g = introTraceTest χ h g) (s : ℂ) :
    let f := fun g : C𝔽 ↦ φ.val g * ideleClassNormTwist χ s g
    Integrable f (ideleClassTamagawaMeasure F) ∧
      (∫ g, f g ∂ideleClassTamagawaMeasure F) = τVolume * introTraceMellin h s := by
  let W (g : C𝔽) := φ.val g * ideleClassNormTwist χ s g
  have hc : Continuous φ.val := schwartzBruhat_continuous
    (⟨φ.val, bruhatCompactSupport_mem_schwartz φ.property⟩ : SchwartzBruhat C𝔽)
  have hW : Continuous W := hc.mul (ideleClassNormTwist χ s).continuous
  refine ⟨hW.integrable_of_hasCompactSupport
    (show HasCompactSupport φ.val from φ.property.2).mul_right, ?_⟩
  have hrad (g : C𝔽) : W g = h (N(g)) * (N(g) : ℂ) ^ s := by
    change φ.val g * ((χ g : ℂ) * (N(g) : ℂ) ^ s) = _
    rw [_hφ, introTraceTest]
    have hu : star (χ g : ℂ) * (χ g : ℂ) = 1 := by simp [← Circle.coe_inv_eq_conj]
    linear_combination h (N(g)) * (N(g) : ℂ) ^ s * hu
  let E : ℝ ≃ₜ ℝ≥0ˣ := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
  let σ (x : ℝ) : C𝔽 := QuotientGroup.mk (canonicalIdeleNormSection F (E x))
  have hσ : Continuous σ :=
    continuous_quotient_mk'.comp ((canonicalIdeleNormSection_continuous F).comp E.continuous)
  have hnorm (x : ℝ) : N(σ x) = Real.exp x :=
    congrArg (fun t : ℝ≥0ˣ ↦ (t.val : ℝ)) (canonicalIdeleNormSection_rightInverse F (E x))
  let l (g : C𝔽) := Real.log (N(g))
  have hl : Measurable l := Real.measurable_log.comp
    ((NNReal.continuous_coe.comp Units.continuous_val).comp
      (isProperMap_ideleClassNorm F).continuous).measurable
  have hsec (g : C𝔽) : W (σ (l g)) = W g := by
    have he : Real.exp (l g) = N(g) := Real.exp_log (Units.zero_lt (ideleClassNorm F g))
    rw [hrad, hrad, hnorm, he]
  have hmellin : (∫ x : ℝ, W (σ x)) = introTraceMellin h s := by
    rw [introTraceMellin, mellin, ← integral_comp_exp]
    refine integral_congr_ae (.of_forall fun x ↦ ?_)
    beta_reduce
    rw [hrad, hnorm, Complex.real_smul, smul_eq_mul]
    have he : (Real.exp x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos x).ne'
    rw [show (s : ℂ) = (s - 1) + 1 by ring, Complex.cpow_add _ _ he,
      Complex.cpow_one, add_sub_cancel_right]
    ring
  change (∫ g, W g ∂ideleClassTamagawaMeasure F) = _
  calc
    _ = ∫ x, W (σ x) ∂(ideleClassTamagawaMeasure F).map l := by
      rw [integral_map (f := fun x ↦ W (σ x)) hl.aemeasurable (hW.comp hσ).aestronglyMeasurable]
      exact integral_congr_ae (.of_forall fun g ↦ (hsec g).symm)
    _ = _ := by
      rw [show (ideleClassTamagawaMeasure F).map l = _ from classTamagawa_map_log_norm (F := F),
        integral_smul_nnreal_measure, hmellin]
      rfl

local notation "archClass(" w ")" => IdeleClassGroup.ofCompletion (𝓞 F) F w
local notation "archIntegrand(" χ ", " h ", " w ")" =>
  (fun u : (w : InfinitePlace F).Completionˣ ↦
    introTraceTest χ h (archClass(w) u) * (Real.sqrt (‖u.val‖ ^ InfinitePlace.mult w) : ℂ) /
      ((‖1 - u.val‖ ^ InfinitePlace.mult w : ℝ) : ℂ))

open Classical in
/-- Paper: §1.4.1, p. 28. The archimedean term is the ordinary local integral
on tests vanishing at norm one.
Deviation: As in the corrected `traceFormula`, the denominator uses the normalized
local absolute value of `1 - u`, and the weight is the square root of the
normalized norm of `u`. The displayed real denominator uses the positive sign
even for the negative branch. The displayed complex denominator is unsquared. -/
def introTraceArchimedean (χ : U𝔽) (h : ℝ → ℂ) (w : InfinitePlace F) : ℂ :=
  (if w.IsReal then (1 / 2 : ℂ) else 1 / (2 * (Real.pi : ℂ))) *
    ∫ u, archIntegrand(χ, h, w) u ∂infiniteLocalMultiplicativeTamagawaMeasure F w

/-- Paper: §1.4.1, p. 28. At a real place this integral is the local
Connes–Weil term of a compactly supported Bruhat test vanishing at norm one. -/
theorem introTraceArchimedean_eq_realPrincipalValue (χ : U𝔽) (h : ℝ → ℂ)
    (_hh : h 1 = 0) (w : InfinitePlace F) (_hw : w.IsReal)
    (φ : BruhatCompactSupport w.Completionˣ)
    (_hφ : ∀ u, φ.val u = introTraceTest χ h (archClass(w) u)) :
    Integrable archIntegrand(χ, h, w) (infiniteLocalMultiplicativeTamagawaMeasure F w) ∧
      introTraceArchimedean χ h w = infiniteConnesWeilPrincipalValue w φ := by sorry

open Classical in
/-- Paper: §1.4.1, p. 28. The finite term at a place is a sum over the positive
and negative prime-power shells.
Deviation: Averaging over local integer units annihilates ramified characters.
At unramified places the uniformizer value uses the library's Euler convention. -/
def introTracePrimePower (χ : U𝔽) (h : ℝ → ℂ) (v : V) (k : ℕ) : ℂ :=
  let c := ideleClassNormTwist χ 0
  let m := k + 1
  if c.IsUnramifiedAt v then
    (Real.log q(v) : ℂ) *
      (c.localValue v ^ m * h (q(v) ^ m) + star (c.localValue v) ^ m * h ((q(v) ^ m)⁻¹)) /
      (q(v) : ℂ) ^ ((m : ℂ) / 2)
  else 0

/-- Paper: §1.4.1, p. 28. The two shells of exponent one for the trivial
character have coefficient `log(q)/sqrt(q)`. -/
theorem introTracePrimePower_one_first (h : ℝ → ℂ) (v : V) :
    introTracePrimePower (1 : U𝔽) h v 0 =
      (Real.log q(v) : ℂ) * (h q(v) + h (q(v)⁻¹)) / (q(v) : ℂ) ^ (1 / 2 : ℂ) := by
  classical
  have htriv : ideleClassNormTwist (1 : U𝔽) 0 = 1 := by
    ext1 g
    change (1 : ℂ) * _ ^ (0 : ℂ) = 1
    simp
  have hunit (u : (v.adicCompletion F)ˣ) :
      (1 : HeckeCharacter (𝓞 F) F).restrict v u = 1 := by
    rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
    rfl
  have hur : (1 : HeckeCharacter (𝓞 F) F).IsUnramifiedAt v :=
    HeckeCharacter.isUnramifiedAt_iff.mpr fun x ↦
      hunit (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom x)
  let val : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
  let u := Units.mk0 (val.exists_isUniformizer_of_isCyclic_of_nontrivial.choose : v.adicCompletion F)
    val.exists_isUniformizer_of_isCyclic_of_nontrivial.choose_spec.ne_zero
  have hv : (1 : HeckeCharacter (𝓞 F) F).localValue v = 1 := hunit u
  simp [introTracePrimePower, htriv, hur, hv]

/-- Paper: §1.4.1, p. 28. The spectral side sums the full zero orders in the
selected character and the open window centered at one half. -/
def introTraceSpectralSum (χ : U𝔽) (h : ℝ → ℂ) (a : ℝ) : ℂ :=
  ∑' ρ : windowZeros(χ, a), (zeroOrder(χ, ρ.val) : ℂ) * introTraceMellin h (ρ.val - 1 / 2)

/-- Paper: §1.4.1, p. 28. A window containing exactly one zero gives its
multiplicity times the radial Mellin moment at that zero's shifted parameter. -/
theorem introTraceSpectralSum_eq_single (χ : U𝔽) (h : ℝ → ℂ) (a : ℝ) (ρ : ℂ)
    (_hρ : 0 < zeroOrder(χ, ρ) ∧ |ρ.re - 1 / 2| < a)
    (_honly : ∀ w : windowZeros(χ, a), w.val = ρ) :
    introTraceSpectralSum χ h a =
      (zeroOrder(χ, ρ) : ℂ) * introTraceMellin h (ρ - 1 / 2) := by
  let w : windowZeros(χ, a) := ⟨ρ, _hρ⟩
  unfold introTraceSpectralSum
  exact tsum_eq_single w fun v hv ↦ (hv (Subtype.ext (_honly v))).elim

open Classical in
/-- Paper: §1.4.1, p. 28. In a single isotype, the local terms equal the
polar moments minus the zero sum. The polar moments occur in the trivial isotype.
Deviation: The character is represented by its extension trivial on the chosen
norm section. The window is centered as in §1.8.4. The identity specializes
the corrected `traceFormula`, using normalized local kernels and unit averages.
The common Tamagawa volume cancels against the Mellin disintegration factor.
The arbitrary window still depends on `traceFormula_exteriorZeros`. -/
theorem introTrace_characterTrace (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (_hτ : RightInverse τ (ideleClassNorm F)) (χ : U𝔽) (_hχ : ∀ t, χ (τ t) = 1)
    (h : ℝ → ℂ) (_hh : h 1 = 0) (φ : D𝔽)
    (_hφ : ∀ g, φ.val g = introTraceTest χ h g) (a : ℝ) (_ha : 0 < a) :
    (∀ w : InfinitePlace F,
      Integrable archIntegrand(χ, h, w) (infiniteLocalMultiplicativeTamagawaMeasure F w)) ∧
    Summable (fun p : V × ℕ ↦ introTracePrimePower χ h p.1 p.2) ∧
    HasSum (fun ρ : windowZeros(χ, a) ↦
      (zeroOrder(χ, ρ.val) : ℂ) * introTraceMellin h (ρ.val - 1 / 2))
      ((if χ = 1 then introTraceMellin h (1 / 2) + introTraceMellin h (-1 / 2) else 0) -
        (∑ w : InfinitePlace F, introTraceArchimedean χ h w) -
        ∑' p : V × ℕ, introTracePrimePower χ h p.1 p.2) := by sorry

end CharacterTrace

section Tests

/-- Paper: §1.4.2, p. 28. The radial power is zero below one, one half at
one, and the inverse complex power above one.
Deviation: The radial profile is extended by zero to the nonpositive real axis
for additive convolution. -/
def introTracePower (z : ℂ) (t : ℝ) : ℂ :=
  if 1 < t then (t : ℂ) ^ (-z) else if t = 1 then 1 / 2 else 0

/-- Paper: §1.4.2, p. 28. On the positive side at parameter two the profile
has value one quarter at two and value one half at the jump. -/
theorem introTracePower_two :
    introTracePower 2 2 = 1 / 4 ∧ introTracePower 2 1 = 1 / 2 := by
  refine ⟨?_, by simp [introTracePower]⟩
  simp only [introTracePower, show (1 : ℝ) < 2 by norm_num, ↓reduceIte, Complex.cpow_neg]
  norm_num

/-- Paper: §1.4.2, p. 28. The radial power is smooth on the two real
intervals separated by its jump at one. -/
theorem introTracePower_contDiffOn (z : ℂ) :
    ContDiffOn ℝ ⊤ (introTracePower z) ({1}ᶜ : Set ℝ) := by
  intro x hx
  refine ContDiffAt.contDiffWithinAt ?_
  rcases lt_or_gt_of_ne (show x ≠ 1 from hx) with h | h
  · have : introTracePower z =ᶠ[nhds x] fun _ ↦ 0 := by
      filter_upwards [eventually_lt_nhds h] with t ht
      simp [introTracePower, ht.not_gt, ht.ne]
    exact contDiffAt_const.congr_of_eventuallyEq this
  · have : introTracePower z =ᶠ[nhds x]
        fun t : ℝ ↦ Complex.exp ((Real.log t : ℂ) * (-z)) := by
      filter_upwards [eventually_gt_nhds h] with t ht
      have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (by linarith)
      simp only [introTracePower, ht, ↓reduceIte, Complex.cpow_def_of_ne_zero ht0,
        Complex.ofReal_log (by linarith : (0 : ℝ) ≤ t)]
    refine ContDiffAt.congr_of_eventuallyEq ?_ this
    have hlog : ContDiffAt ℝ ⊤ Real.log x := Real.contDiffAt_log.2 (by linarith)
    exact Complex.contDiff_exp.contDiffAt.comp x
      ((Complex.ofRealCLM.contDiff.contDiffAt.comp x hlog).mul contDiffAt_const)

/-- Paper: §1.4.2, p. 28. The limiting power depends holomorphically
on the complex parameter at each fixed radial coordinate. -/
theorem introTracePower_differentiable (t : ℝ) :
    Differentiable ℂ (fun z ↦ introTracePower z t) := by
  by_cases ht : 1 < t
  · simp only [introTracePower, ite_eq_left ht]
    exact differentiable_neg.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr (by linarith)))
  · simp only [introTracePower, ite_eq_right ht]
    exact differentiable_const _

/-- Paper: §1.4.2, pp. 28–29. The cutoffs increase pointwise to the indicator
of `(1, ∞)` and the mollifiers have nonnegative unit mass and shrinking support.
Deviation: The paper leaves the mollifier and convolution unspecified. This
uses ordinary additive convolution in the coordinate `t` with Lebesgue measure
and encodes the cofinal approximation by sequences. -/
def IsIntroTraceApproximation (h ρ : ℕ → ℝ → ℝ) : Prop :=
  (∀ n, ContDiff ℝ ⊤ (h n) ∧ HasCompactSupport (h n) ∧
    tsupport (h n) ⊆ Ioi 1 ∧ ∀ t, h n t ∈ Icc 0 1) ∧
  Monotone h ∧ (∀ t > 1, Tendsto (fun n ↦ h n t) atTop (𝓝 1)) ∧
  ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
    ∀ n, 0 < ε n ∧ ContDiff ℝ ⊤ (ρ n) ∧ (∀ t, 0 ≤ ρ n t) ∧
      tsupport (ρ n) ⊆ Icc (-ε n) (ε n) ∧ (∫ t, ρ n t) = 1

/-- Paper: §1.4.2, pp. 28–29. Smooth bump cutoffs and ordinary mollifiers
give an approximation sequence with the stated support and convergence. -/
theorem exists_introTraceApproximation :
    ∃ h ρ, IsIntroTraceApproximation h ρ := by sorry

/-- Paper: §1.4.2, p. 28. The approximant is the cutoff times the mollified
radial power in the norm coordinate. -/
def introTraceApprox (h ρ : ℝ → ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  (h t : ℂ) * ∫ u : ℝ, (ρ u : ℂ) * introTracePower z (t - u)

/-- Paper: §1.4.2, pp. 28–29. The approximants are supported strictly
above norm one and agree with the limiting power at each fixed norm other
than one in the limit.
Deviation: The support statement uses topological support, so each individual
cutoff vanishes in an open neighborhood of one. -/
theorem introTraceApprox_support (h ρ : ℕ → ℝ → ℝ)
    (_hA : IsIntroTraceApproximation h ρ) (n : ℕ) (z : ℂ) :
    tsupport (introTraceApprox (h n) (ρ n) z) ⊆ Ioi 1 := by
  refine (closure_mono (s := Function.support (introTraceApprox (h n) (ρ n) z))
    (t := Function.support (h n)) ?_).trans (_hA.1 n).2.2.1
  intro t ht he
  exact ht (by simp [introTraceApprox, he])

/-- Paper: §1.4.2, p. 29. Every fixed positive norm other than one has
the printed pointwise limit. -/
theorem introTraceApprox_tendsto (h ρ : ℕ → ℝ → ℝ)
    (_hA : IsIntroTraceApproximation h ρ) (z : ℂ) (t : ℝ) (_ht : 0 < t) (_ht₁ : t ≠ 1) :
    Tendsto (fun n ↦ introTraceApprox (h n) (ρ n) z t) atTop (𝓝 (introTracePower z t)) := by
  obtain ⟨hh, -, hhlim, ε, hε, hρ⟩ := _hA
  rcases lt_or_gt_of_ne _ht₁ with ht | ht
  · have hzero (n : ℕ) : h n t = 0 := by
      by_contra hn
      exact (not_lt.mpr ht.le) ((hh n).2.2.1 (subset_tsupport _ hn))
    simp [introTraceApprox, hzero, introTracePower, ht.not_gt, ht.ne]
  · have hcont : ContinuousAt (introTracePower z) t := by
      apply (Complex.continuousAt_ofReal_cpow_const t (-z) (Or.inr _ht.ne')).congr_of_eventuallyEq
      filter_upwards [lt_mem_nhds ht] with x hx
      simp [introTracePower, hx]
    have hmeas : Measurable (introTracePower z) :=
      Measurable.ite measurableSet_Ioi (by fun_prop)
        (Measurable.ite (measurableSet_singleton 1) measurable_const measurable_const)
    have hsmall : Tendsto (fun n ↦ support (ρ n)) atTop (𝓝 0).smallSets := by
      rw [Metric.nhds_basis_ball.smallSets.tendsto_right_iff]
      intro r hr
      filter_upwards [hε.eventually_lt_const hr] with n hn
      intro x hx
      have hmem := (hρ n).2.2.2.1 (subset_tsupport _ hx)
      simpa only [Metric.mem_ball, Real.dist_0_eq_abs, abs_lt] using
        (show -r < x ∧ x < r from ⟨lt_of_lt_of_le (neg_lt_neg hn) hmem.1, hmem.2.trans_lt hn⟩)
    have hconv := convolution_tendsto_right (μ := volume)
      (g := fun _ : ℕ ↦ introTracePower z) (k := fun _ ↦ t)
      (Eventually.of_forall fun n ↦ (hρ n).2.2.1)
      (Eventually.of_forall fun n ↦ (hρ n).2.2.2.2) hsmall
      (Eventually.of_forall fun _ ↦ hmeas.aestronglyMeasurable)
      (hcont.tendsto.comp tendsto_snd) tendsto_const_nhds
    have hcut := Complex.continuous_ofReal.continuousAt.tendsto.comp (hhlim t ht)
    simpa only [introTraceApprox, convolution, ContinuousLinearMap.lsmul_apply,
      Complex.real_smul, Complex.ofReal_one, one_mul, Function.comp_def] using hcut.mul hconv

/-- Paper: §1.4.2, pp. 28–29. At any fixed norm, the mollified cutoff
depends holomorphically on the complex parameter. -/
theorem introTraceApprox_differentiable (h ρ : ℕ → ℝ → ℝ)
    (_hA : IsIntroTraceApproximation h ρ) (n : ℕ) (t : ℝ) :
    Differentiable ℂ (fun z ↦ introTraceApprox (h n) (ρ n) z t) := by
  obtain ⟨-, -, -, ε, -, hε⟩ := _hA
  obtain ⟨-, hρc, -, hρs, -⟩ := hε n
  have hρint : Integrable (ρ n) := hρc.continuous.integrable_of_hasCompactSupport
    (isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hρs)
  have hρm : Measurable fun u ↦ (ρ n u : ℂ) :=
    Complex.measurable_ofReal.comp hρc.continuous.measurable
  have hPm : ∀ z : ℂ, Measurable (introTracePower z) := fun z ↦
    Measurable.ite measurableSet_Ioi (by fun_prop)
      (Measurable.ite (measurableSet_singleton 1) measurable_const measurable_const)
  have hu : ∀ u, ρ n u ≠ 0 → t - u ≤ t + ε n := fun u hu ↦ by
    have := hρs (subset_tsupport _ hu)
    linarith [this.1]
  intro z₀
  set K : ℝ := |z₀.re| + 1
  set C : ℝ := |Real.log (t + ε n)| * |t + ε n| ^ K
  set M : ℝ := max 1 (|t + ε n| ^ K)
  have hpow : ∀ u, ∀ z ∈ Metric.ball z₀ 1, ρ n u ≠ 0 → 1 < t - u →
      (t - u) ^ (-z.re) ≤ |t + ε n| ^ K := by
    intro u z hz hρ h1
    have hz' : |z.re - z₀.re| < 1 :=
      (Complex.abs_re_le_norm (z - z₀)).trans_lt (by simpa [dist_eq_norm] using hz)
    calc (t - u) ^ (-z.re) ≤ (t - u) ^ K := Real.rpow_le_rpow_of_exponent_le h1.le
          (by linarith [(abs_lt.1 hz').1, neg_abs_le z₀.re])
      _ ≤ |t + ε n| ^ K := Real.rpow_le_rpow (by linarith)
          ((hu u hρ).trans (le_abs_self _)) (by positivity)
  have hF_int : Integrable (fun u ↦ (ρ n u : ℂ) * introTracePower z₀ (t - u)) := by
    refine Integrable.mono' (hρint.norm.mul_const M)
      (hρm.mul ((hPm z₀).comp (measurable_const.sub measurable_id))).aestronglyMeasurable
      (Eventually.of_forall fun u ↦ ?_)
    by_cases hρ : ρ n u = 0
    · simp [hρ]
    rw [norm_mul, Complex.norm_real]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    unfold introTracePower
    split_ifs with h1 h2
    · rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith), Complex.neg_re]
      exact (hpow u z₀ (Metric.mem_ball_self one_pos) hρ h1).trans (le_max_right _ _)
    · exact le_trans (by norm_num) (le_max_left _ _)
    · simpa using (zero_le_one.trans (le_max_left _ _) : (0 : ℝ) ≤ M)
  have hF'_meas : AEStronglyMeasurable (fun u : ℝ ↦ (ρ n u : ℂ) *
      if 1 < t - u then ((t - u : ℝ) : ℂ) ^ (-z₀) * Complex.log ((t - u : ℝ) : ℂ) * (-1)
      else 0) volume :=
    (hρm.mul (Measurable.ite (measurableSet_lt measurable_const
      (measurable_const.sub measurable_id)) (by fun_prop) measurable_const)).aestronglyMeasurable
  have h_bound : ∀ᵐ u ∂volume, ∀ z ∈ Metric.ball z₀ 1, ‖(ρ n u : ℂ) *
      (if 1 < t - u then ((t - u : ℝ) : ℂ) ^ (-z) * Complex.log ((t - u : ℝ) : ℂ) * (-1)
        else 0)‖ ≤ ‖ρ n u‖ * C := by
    refine Eventually.of_forall fun u z hz ↦ ?_
    rw [norm_mul, Complex.norm_real]
    by_cases hρ : ρ n u = 0
    · simp [hρ]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    split_ifs with h1
    · have hc : 0 < t - u := by linarith
      rw [norm_mul, norm_mul, norm_neg, norm_one, mul_one,
        Complex.norm_cpow_eq_rpow_re_of_pos hc, Complex.neg_re, ← Complex.ofReal_log hc.le,
        Complex.norm_real, Real.norm_eq_abs, mul_comm]
      refine mul_le_mul ?_ (hpow u z hz hρ h1) (by positivity) (abs_nonneg _)
      rw [abs_of_nonneg (Real.log_nonneg h1.le)]
      exact (Real.log_le_log hc (hu u hρ)).trans (le_abs_self _)
    · simp only [norm_zero]
      positivity
  have h_diff : ∀ᵐ u ∂volume, ∀ z ∈ Metric.ball z₀ 1,
      HasDerivAt (fun z ↦ (ρ n u : ℂ) * introTracePower z (t - u)) ((ρ n u : ℂ) *
        (if 1 < t - u then ((t - u : ℝ) : ℂ) ^ (-z) * Complex.log ((t - u : ℝ) : ℂ) * (-1)
          else 0)) z := by
    refine Eventually.of_forall fun u z _ ↦ ?_
    split_ifs with h1
    · have hfun : (fun z ↦ (ρ n u : ℂ) * introTracePower z (t - u)) =
          fun z ↦ (ρ n u : ℂ) * ((t - u : ℝ) : ℂ) ^ (-z) := by
        funext z
        simp [introTracePower, h1]
      rw [hfun]
      exact ((hasDerivAt_neg z).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.2 (by linarith)))).const_mul _
    · have hfun : (fun z ↦ (ρ n u : ℂ) * introTracePower z (t - u)) =
          fun _ ↦ (ρ n u : ℂ) * introTracePower 0 (t - u) := by
        funext z
        simp [introTracePower, h1]
      rw [hfun]
      exact (hasDerivAt_const z _).const_mul _
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds z₀ one_pos)
    (Eventually.of_forall fun z ↦ (hρm.mul
      ((hPm z).comp (measurable_const.sub measurable_id))).aestronglyMeasurable)
    hF_int hF'_meas h_bound (hρint.norm.mul_const C) h_diff
  exact (differentiableAt_const _).mul key.2.differentiableAt

/-- Paper: §1.4.2, pp. 28–29. After twisting by the conjugate character
the approximant is a compactly supported Bruhat test on the idele classes. -/
theorem introTraceApprox_exists_bruhat (χ : U𝔽) (h ρ : ℕ → ℝ → ℝ)
    (_hA : IsIntroTraceApproximation h ρ) (n : ℕ) (z : ℂ) :
    ∃ φ : D𝔽, ∀ g, φ.val g = introTraceTest χ (introTraceApprox (h n) (ρ n) z) g := by sorry

/-- Paper: §1.4.2, pp. 28–29. The twisted approximant satisfies the second
standing hypothesis of the trace identity, vanishing at every norm-one class. -/
theorem introTraceApprox_zero_on_normOne (χ : U𝔽) (h ρ : ℕ → ℝ → ℝ)
    (_hA : IsIntroTraceApproximation h ρ) (n : ℕ) (z : ℂ) :
    ∀ g : (ideleClassNorm F).ker,
      introTraceTest χ (introTraceApprox (h n) (ρ n) z) g.val = 0 := by
  intro g
  have hzero : introTraceApprox (h n) (ρ n) z 1 = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    exact fun ht ↦ lt_irrefl (1 : ℝ) (introTraceApprox_support h ρ _hA n z ht)
  have hg : ideleClassNorm F g.val = 1 := g.property
  simp [introTraceTest, hg, hzero]

private theorem introTraceApprox_mellin_tendsto_power_measurable (z : ℂ) :
    Measurable (introTracePower z) :=
  Measurable.ite measurableSet_Ioi (by fun_prop)
    (Measurable.ite (measurableSet_singleton 1) measurable_const measurable_const)

private theorem introTraceApprox_mellin_tendsto_power_bound {a t x : ℝ} {z : ℂ}
    (ht : 1 < t) (hx : |x - t| ≤ 1) (hz : a ≤ z.re) :
    ‖introTracePower z x‖ ≤ ((1 / 2 : ℝ) ^ (-a) + 2 ^ (-a)) * t ^ (-a) := by
  -- On the nonzero branch, the shifted radius lies between t/2 and 2t.
  have hb (hx1 : 1 ≤ x) :
      x ^ (-a) ≤ ((1 / 2 : ℝ) ^ (-a) + 2 ^ (-a)) * t ^ (-a) := by
    obtain ⟨hl, hu⟩ := abs_le.mp hx
    rcases le_total 0 a with ha | ha
    · calc
        x ^ (-a) ≤ ((1 / 2) * t) ^ (-a) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
        _ = (1 / 2 : ℝ) ^ (-a) * t ^ (-a) := Real.mul_rpow (by norm_num) (by linarith)
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) (by positivity)
    · calc
        x ^ (-a) ≤ (2 * t) ^ (-a) :=
          Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
        _ = (2 : ℝ) ^ (-a) * t ^ (-a) := Real.mul_rpow (by norm_num) (by linarith)
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity)) (by positivity)
  unfold introTracePower
  split_ifs with h h'
  · rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith), Complex.neg_re]
    exact (Real.rpow_le_rpow_of_exponent_le h.le (neg_le_neg hz)).trans (hb h.le)
  · subst x
    exact le_trans (by norm_num : ‖(1 / 2 : ℂ)‖ ≤ (1 : ℝ) ^ (-a)) (hb le_rfl)
  · rw [norm_zero]
    positivity

private theorem introTraceApprox_mellin_tendsto_radial {h ρ : ℕ → ℝ → ℝ}
    (hA : IsIntroTraceApproximation h ρ) (z : ℂ) {t : ℝ} (ht : 1 < t) :
    Tendsto (fun p : ℕ × ℂ ↦ introTraceApprox (h p.1) (ρ p.1) p.2 t)
      (atTop ×ˢ 𝓝 z) (𝓝 (introTracePower z t)) := by
  obtain ⟨_, _, hlim, ε, hε, hρ⟩ := hA
  have hsmall : Tendsto (fun n ↦ support (ρ n)) atTop (𝓝 0).smallSets := by
    rw [Metric.nhds_basis_ball.smallSets.tendsto_right_iff]
    intro r hr
    filter_upwards [hε.eventually_lt_const hr] with n hn
    intro x hx
    have hm := (hρ n).2.2.2.1 (subset_tsupport _ hx)
    simpa only [Metric.mem_ball, Real.dist_0_eq_abs, abs_lt] using
      (show -r < x ∧ x < r from ⟨by linarith [hm.1], by linarith [hm.2]⟩)
  let l : Filter (ℕ × ℂ) := atTop ×ˢ 𝓝 z
  have hcont : Tendsto (fun p : (ℕ × ℂ) × ℝ ↦ introTracePower p.1.2 p.2)
      (l ×ˢ 𝓝 t) (𝓝 (introTracePower z t)) := by
    have hx : Tendsto (fun p : (ℕ × ℂ) × ℝ ↦ (p.2 : ℂ)) (l ×ˢ 𝓝 t) (𝓝 (t : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp tendsto_snd
    have hz : Tendsto (fun p : (ℕ × ℂ) × ℝ ↦ -p.1.2) (l ×ˢ 𝓝 t) (𝓝 (-z)) :=
      (tendsto_snd.comp tendsto_fst).neg
    simp only [introTracePower, ht, ↓reduceIte]
    apply (hx.cpow hz (Complex.ofReal_mem_slitPlane.mpr (by linarith))).congr'
    filter_upwards [tendsto_snd.eventually (lt_mem_nhds ht)] with p hp
    simp [hp]
  have hconv := convolution_tendsto_right (μ := volume)
    (φ := fun p : ℕ × ℂ ↦ ρ p.1) (g := fun p : ℕ × ℂ ↦ introTracePower p.2)
    (k := fun _ ↦ t) (l := l)
    (Eventually.of_forall fun p ↦ (hρ p.1).2.2.1)
    (Eventually.of_forall fun p ↦ (hρ p.1).2.2.2.2) (hsmall.comp tendsto_fst)
    (Eventually.of_forall fun p ↦ (introTraceApprox_mellin_tendsto_power_measurable p.2).aestronglyMeasurable)
    hcont tendsto_const_nhds
  have hcut := Complex.continuous_ofReal.continuousAt.tendsto.comp ((hlim t ht).comp
    (show Tendsto Prod.fst l atTop from tendsto_fst))
  simpa only [introTraceApprox, convolution, ContinuousLinearMap.lsmul_apply,
    Complex.real_smul, Complex.ofReal_one, one_mul, Function.comp_def] using hcut.mul hconv

private theorem introTraceApprox_mellin_tendsto_cutoff_bound {h ρ : ℕ → ℝ → ℝ}
    (hA : IsIntroTraceApproximation h ρ) (a : ℝ) :
    ∀ᶠ n in atTop, ∀ (z : ℂ) (t : ℝ), a ≤ z.re → 1 < t →
      ‖introTraceApprox (h n) (ρ n) z t‖ ≤ ((1 / 2 : ℝ) ^ (-a) + 2 ^ (-a)) * t ^ (-a) := by
  obtain ⟨hh, _, _, ε, hε, hρ⟩ := hA
  filter_upwards [hε.eventually_le_const (zero_lt_one : (0 : ℝ) < 1)] with n hn
  intro z t hz ht
  let B := ((1 / 2 : ℝ) ^ (-a) + 2 ^ (-a)) * t ^ (-a)
  obtain ⟨_, hsm, hpos, hs, hm⟩ := hρ n
  have hi : Integrable (ρ n) volume := hsm.continuous.integrable_of_hasCompactSupport
    (isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hs)
  have hbound : ‖∫ u : ℝ, (ρ n u : ℂ) * introTracePower z (t - u)‖ ≤ B := by
    calc
      _ ≤ ∫ u, ρ n u * B := norm_integral_le_of_norm_le (hi.mul_const B) (by
        apply Eventually.of_forall
        intro u
        by_cases hu : ρ n u = 0
        · simp [hu]
        obtain ⟨hl, hr⟩ := hs (subset_tsupport _ hu)
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hpos u)]
        apply mul_le_mul_of_nonneg_left _ (hpos u)
        exact introTraceApprox_mellin_tendsto_power_bound ht (abs_le.mpr ⟨by linarith, by linarith⟩) hz)
      _ = B := by rw [integral_mul_const, hm, one_mul]
  rw [introTraceApprox, norm_mul, Complex.norm_real, Real.norm_of_nonneg ((hh n).2.2.2 t).1]
  exact mul_le_of_le_one_left (norm_nonneg _) ((hh n).2.2.2 t).2 |>.trans hbound

private theorem introTraceApprox_mellin_tendsto_integral {ι : Type} {l : Filter ι}
    [l.IsCountablyGenerated] {f : ι → ℝ → ℂ} {g : ℝ → ℂ} (s : ℂ) {a C : ℝ}
    (ha : s.re < a) (hf : ∀ i, Measurable (f i))
    (hzero : ∀ i t, t < 1 → f i t = 0)
    (hbound : ∀ᶠ i in l, ∀ t, 1 < t → ‖f i t‖ ≤ C * t ^ (-a))
    (hlim : ∀ t, t ≠ 1 → Tendsto (fun i ↦ f i t) l (𝓝 (g t))) :
    Tendsto (fun i ↦ introTraceMellin (f i) s) l (𝓝 (introTraceMellin g s)) := by
  -- The Mellin weight lowers the decay exponent to s.re - 1 - a < -1.
  let B := (Ioi (1 : ℝ)).indicator (fun t : ℝ ↦ C * t ^ (s.re - 1 - a))
  have hi : Integrable B volume := (integrable_indicator_iff measurableSet_Ioi).2
    ((integrableOn_Ioi_rpow_of_lt (by linarith : s.re - 1 - a < -1) zero_lt_one).const_mul C)
  apply tendsto_integral_filter_of_dominated_convergence B _ _ hi.integrableOn _
  · exact Eventually.of_forall fun i ↦
      ((by fun_prop : Measurable (fun t : ℝ ↦ (t : ℂ) ^ (s - 1))).smul (hf i)).aestronglyMeasurable
  · filter_upwards [hbound] with i hbi
    filter_upwards [Measure.ae_ne _ (1 : ℝ)] with t hne
    rcases lt_or_gt_of_ne hne with ht | ht
    · simp [B, hzero i t ht, ht.not_gt, Set.indicator_of_notMem]
    · rw [show B t = C * t ^ (s.re - 1 - a) from indicator_of_mem ht _, smul_eq_mul,
          norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
      simp only [Complex.sub_re, Complex.one_re]
      calc
        _ ≤ t ^ (s.re - 1) * (C * t ^ (-a)) :=
          mul_le_mul_of_nonneg_left (hbi t ht) (by positivity)
        _ = C * t ^ (s.re - 1 - a) := by
          rw [sub_eq_add_neg (s.re - 1), Real.rpow_add (by linarith : 0 < t)]
          ring
  · filter_upwards [Measure.ae_ne _ (1 : ℝ)] with t ht
    exact (tendsto_const_nhds (x := (t : ℂ) ^ (s - 1))).smul (hlim t ht)

/-- Paper: §§1.4.2–1.4.3, pp. 28–29. For a fixed Mellin exponent `s`,
the approximant moments converge locally uniformly on `Re z > Re s`
to the Mellin integral of the limiting radial power. -/
theorem introTraceApprox_mellin_tendsto (h ρ : ℕ → ℝ → ℝ)
    (_hA : IsIntroTraceApproximation h ρ) (s : ℂ) :
    TendstoLocallyUniformlyOn
      (fun n z ↦ introTraceMellin (introTraceApprox (h n) (ρ n) z) s)
      (fun z ↦ introTraceMellin (introTracePower z) s) atTop right(s.re) := by
  apply (isOpen_Ioi.preimage Complex.continuous_re).tendstoLocallyUniformlyOn_iff_forall_tendsto.2
  intro z hz
  obtain ⟨a, hsa, haz⟩ := exists_between (show s.re < z.re from hz)
  let l : Filter (ℕ × ℂ) := atTop ×ˢ 𝓝 z
  let C := (1 / 2 : ℝ) ^ (-a) + 2 ^ (-a)
  have hnear : ∀ᶠ p : ℕ × ℂ in l, a ≤ p.2.re :=
    (Complex.continuous_re.continuousAt.tendsto.comp tendsto_snd).eventually (le_mem_nhds haz)
  have hpow : Tendsto (fun p : ℕ × ℂ ↦ introTraceMellin (introTracePower p.2) s) l
      (𝓝 (introTraceMellin (introTracePower z) s)) := by
    apply introTraceApprox_mellin_tendsto_integral (a := a) (C := C) s hsa
    · exact fun p ↦ introTraceApprox_mellin_tendsto_power_measurable p.2
    · intro p t ht
      simp [introTracePower, ht.not_gt, ht.ne]
    · filter_upwards [hnear] with p hp
      intro t ht
      exact introTraceApprox_mellin_tendsto_power_bound ht (by simp) hp
    · intro t _
      exact (introTracePower_differentiable t).continuous.continuousAt.tendsto.comp tendsto_snd
  have hzero (n : ℕ) (t : ℝ) (ht : t < 1) : h n t = 0 := by
    by_contra hn
    exact ht.asymm ((_hA.1 n).2.2.1 (subset_tsupport _ hn))
  have happ : Tendsto (fun p : ℕ × ℂ ↦ introTraceMellin (introTraceApprox (h p.1) (ρ p.1) p.2) s) l
      (𝓝 (introTraceMellin (introTracePower z) s)) := by
    apply introTraceApprox_mellin_tendsto_integral (a := a) (C := C) s hsa
    · intro p
      obtain ⟨ε, _, hρ⟩ := _hA.2.2.2
      have hm := (introTraceApprox_mellin_tendsto_power_measurable p.2).comp
        (measurable_fst.sub measurable_snd : Measurable fun q : ℝ × ℝ ↦ q.1 - q.2)
      have hk : Measurable (fun q : ℝ × ℝ ↦ (ρ p.1 q.2 : ℂ)) :=
        Complex.measurable_ofReal.comp ((hρ p.1).2.1.continuous.measurable.comp measurable_snd)
      exact (Complex.measurable_ofReal.comp (_hA.1 p.1).1.continuous.measurable).mul
        ((hk.mul hm).stronglyMeasurable.integral_prod_right'.measurable)
    · intro p t ht
      simp [introTraceApprox, hzero p.1 t ht]
    · filter_upwards [hnear, (show Tendsto Prod.fst l atTop from tendsto_fst).eventually
          (introTraceApprox_mellin_tendsto_cutoff_bound _hA a)] with p hp hb
      exact fun t ht ↦ hb p.2 t hp ht
    · intro t ht
      rcases lt_or_gt_of_ne ht with hlt | hgt
      · simp [introTraceApprox, hzero _ _ hlt, introTracePower, hlt.not_gt, hlt.ne]
      · exact introTraceApprox_mellin_tendsto_radial _hA z hgt
  exact (hpow.prodMk_nhds happ).mono_right (nhds_le_uniformity _)

/-- Paper: §§1.4.2, 1.4.5, pp. 28–29. The Mellin transform of the limiting
radial power exists on the convergence half-plane and equals `1 / (z - s)`. -/
theorem introTracePower_mellin (z s : ℂ) (_hs : s.re < z.re) :
    IntegrableOn (fun t : ℝ ↦ introTracePower z t * (t : ℂ) ^ (s - 1)) (Ioi 0) ∧
      introTraceMellin (introTracePower z) s = 1 / (z - s) := by
  let a := -z + (s - 1)
  have ha : a.re < -1 := by
    change -z.re + (s.re - 1) < -1
    linarith
  have he : (fun t : ℝ ↦ introTracePower z t * (t : ℂ) ^ (s - 1)) =ᵐ[volume]
      (Ioi (1 : ℝ)).indicator (fun t : ℝ ↦ (t : ℂ) ^ a) := by
    filter_upwards [Measure.ae_ne volume (1 : ℝ)] with t ht
    by_cases hgt : 1 < t
    · rw [indicator_of_mem hgt, introTracePower, ite_eq_left hgt]
      exact (Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (zero_lt_one.trans hgt).ne')).symm
    · simp [introTracePower, ht, hgt]
  have hsub : Ioi (1 : ℝ) ⊆ Ioi 0 := Ioi_subset_Ioi zero_le_one
  have hI : IntegrableOn ((Ioi (1 : ℝ)).indicator (fun t : ℝ ↦ (t : ℂ) ^ a)) (Ioi 0) := by
    rw [integrableOn_indicator_iff measurableSet_Ioi.nullMeasurableSet, inter_eq_left.mpr hsub]
    exact integrableOn_Ioi_cpow_of_lt ha zero_lt_one
  refine ⟨hI.congr (ae_restrict_of_ae he.symm), ?_⟩
  unfold introTraceMellin mellin
  simp_rw [smul_eq_mul, mul_comm _ (introTracePower z _)]
  rw [integral_congr_ae (ae_restrict_of_ae he), setIntegral_indicator measurableSet_Ioi,
    inter_eq_right.mpr hsub, integral_Ioi_cpow_of_lt ha zero_lt_one]
  rw [show a + 1 = -(z - s) by dsimp [a]; ring]
  simp only [Complex.ofReal_one, Complex.one_cpow, neg_div_neg_eq]

end Tests

section Limits

local notation "approx(" h ", " ρ ", " n ", " z ")" => introTraceApprox (h n) (ρ n) z
local notation "archSum(" χ ", " h ")" =>
  (∑ w : InfinitePlace F, introTraceArchimedean χ h w)
local notation "primeSum(" χ ", " h ")" =>
  (∑' p : V × ℕ, introTracePrimePower χ h p.1 p.2)

/-- Paper: §1.4.3, p. 29. Each fixed-cutoff archimedean integral is entire
in the parameter.
Deviation: The archimedean kernels use the corrected trace formula. -/
theorem introTraceApprox_archimedean_differentiable (χ : U𝔽) (h ρ : ℕ → ℝ → ℝ)
    (_hA : IsIntroTraceApproximation h ρ) (n : ℕ) (w : InfinitePlace F) :
    Differentiable ℂ (fun z ↦ introTraceArchimedean χ approx(h, ρ, n, z) w) := by sorry

/-- At the real place of ℚ, a lower integral against the local multiplicative Tamagawa measure
is the Lebesgue integral with density `|t|⁻¹` in the real coordinate. -/
private theorem introTraceApprox_rat_archimedean_tendsto_atTop_lintegral
    (Φ : ℝ → ENNReal) (hΦ : Measurable Φ) :
    ∫⁻ u, Φ (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
        (u : Rat.infinitePlace.Completion))
        ∂infiniteLocalMultiplicativeTamagawaMeasure ℚ Rat.infinitePlace =
      ∫⁻ t, Φ t * ENNReal.ofReal |t|⁻¹ := by
  let v := Rat.infinitePlace
  have h : v.IsReal := Rat.isReal_infinitePlace
  let : MeasurableSpace v.Completion := instMeasurableSpaceCompletion_riemannMasullo ℚ v
  let : BorelSpace v.Completion := ⟨rfl⟩
  let : BorelSpace v.Completionˣ := borelSpace_units_of_continuousInv₀ _
  let e := (InfinitePlace.Completion.isometryEquivRealOfIsReal h).toHomeomorph.toMeasurableEquiv
  have hval := (IsOpenUnits.isOpenEmbedding_unitsVal (M := v.Completion)).measurableEmbedding
  have hd : Measurable (fun x : v.Completion ↦ (↑(‖x‖₊ ^ v.mult) : ENNReal)⁻¹) :=
    (measurable_coe_nnreal_ennreal.comp (measurable_nnnorm.pow_const _)).inv
  let g : v.Completion → ENNReal := fun x ↦ Φ (InfinitePlace.Completion.ringEquivRealOfIsReal h x)
  have hg : Measurable g := hΦ.comp e.measurable
  have hee (t : ℝ) : InfinitePlace.Completion.ringEquivRealOfIsReal h (e.symm t) = t :=
    e.apply_symm_apply t
  have key := hval.lintegral_map (μ := ((infiniteLocalAdditiveTamagawaMeasure ℚ v).withDensity
    (fun x ↦ (↑(‖x‖₊ ^ v.mult) : ENNReal)⁻¹)).comap Units.val) g
  rw [hval.map_comap, setLIntegral_withDensity_eq_setLIntegral_mul _ hd hg
    hval.measurableSet_range] at key
  unfold infiniteLocalMultiplicativeTamagawaMeasure
  refine key.symm.trans ?_
  rw [infiniteLocalAdditiveTamagawaMeasure, dite_eq_left h]
  change (∫⁻ x in range Units.val, _ ∂volume.map e.symm) = _
  rw [e.symm.restrict_map, e.symm.measurableEmbedding.lintegral_map]
  have he0 : e.symm 0 = 0 := map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal h).symm
  have hrange : e.symm ⁻¹' range (Units.val : v.Completionˣ → v.Completion) = {0}ᶜ := by
    ext t
    simp only [mem_preimage, mem_range, mem_compl_iff, mem_singleton_iff]
    constructor
    · rintro ⟨x, hx⟩ rfl
      exact x.ne_zero (hx.trans he0)
    · intro ht
      exact ⟨Units.mk0 (e.symm t) fun h0 ↦ ht (e.symm.injective (h0.trans he0.symm)), rfl⟩
  have hnorm (t : ℝ) : ‖e.symm t‖ = ‖t‖ :=
    (InfinitePlace.Completion.isometryEquivRealOfIsReal h).symm.isometry.norm_map_of_map_zero
      (map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal h).symm) t
  rw [hrange]
  conv_rhs => rw [← restrict_compl_singleton (μ := volume) (0 : ℝ)]
  refine setLIntegral_congr_fun (measurableSet_singleton (0 : ℝ)).compl fun t ht ↦ ?_
  have ht0 : t ≠ 0 := ht
  change (↑(‖e.symm t‖₊ ^ v.mult) : ENNReal)⁻¹ * g (e.symm t) = _
  simp only [g]
  rw [hee, h.mult_eq_one, pow_one, ← ENNReal.ofReal_coe_nnreal, coe_nnNorm, hnorm,
    Real.norm_eq_abs, mul_comm, ENNReal.ofReal_inv_of_pos (abs_pos.mpr ht0)]

/-- Paper: §1.4.3, p. 29. For the trivial rational character at parameter two,
the real-place term goes to positive infinity as the cutoffs are removed.
Deviation: This replaces the printed uniform bound. It also applies to the
corrected trace formula, since the positive real branch has the same kernel. -/
theorem introTraceApprox_rat_archimedean_tendsto_atTop (h ρ : ℕ → ℝ → ℝ)
    (_hA : IsIntroTraceApproximation h ρ) :
    Tendsto (fun n ↦ (∑ w : InfinitePlace ℚ,
      introTraceArchimedean (F := ℚ) 1 approx(h, ρ, n, (2 : ℂ)) w).re) atTop atTop := by
  classical
  obtain ⟨hh, -, hhlim, ε, hε, hρ⟩ := _hA
  have hw : Rat.infinitePlace.IsReal := Rat.isReal_infinitePlace
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  -- The limiting profile at parameter two is real.
  let p : ℝ → ℝ := fun x ↦ if 1 < x then x ^ (-2 : ℝ) else if x = 1 then 1 / 2 else 0
  have hp0 (x : ℝ) : 0 ≤ p x := by
    simp only [p]; split_ifs with h1 <;> first | positivity | norm_num
  have hp1 (x : ℝ) : p x ≤ 1 := by
    simp only [p]; split_ifs with h1
    · exact Real.rpow_le_one_of_one_le_of_nonpos h1.le (by norm_num)
    · norm_num
    · norm_num
  have hpm : Measurable p :=
    Measurable.ite measurableSet_Ioi (by fun_prop)
      (Measurable.ite (measurableSet_singleton 1) measurable_const measurable_const)
  have hpow (x : ℝ) : introTracePower 2 x = (p x : ℂ) := by
    simp only [introTracePower, p]
    split_ifs with h1 h2
    · rw [Complex.ofReal_cpow (zero_lt_one.trans h1).le]; push_cast; rfl
    · push_cast; rfl
    · simp
  -- The real approximants.
  let b : ℕ → ℝ → ℝ := fun n t ↦ h n t * ∫ u, ρ n u * p (t - u)
  have happrox (n : ℕ) (t : ℝ) : introTraceApprox (h n) (ρ n) 2 t = (b n t : ℂ) := by
    simp only [introTraceApprox, hpow, b, Complex.ofReal_mul]
    congr 1
    rw [← integral_complex_ofReal]
    simp only [Complex.ofReal_mul]
  have hρint (n : ℕ) : Integrable (ρ n) volume := (hρ n).2.1.continuous.integrable_of_hasCompactSupport
    (isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (hρ n).2.2.2.1)
  have hint (n : ℕ) (t : ℝ) : Integrable (fun u ↦ ρ n u * p (t - u)) volume :=
    (hρint n).mono (((hρ n).2.1.continuous.measurable.mul
      (hpm.comp (measurable_const.sub measurable_id))).aestronglyMeasurable)
      (Eventually.of_forall fun u ↦ by
        rw [norm_mul, Real.norm_of_nonneg (hp0 _)]
        exact mul_le_of_le_one_right (norm_nonneg _) (hp1 _))
  have hI0 (n : ℕ) (t : ℝ) : 0 ≤ ∫ u, ρ n u * p (t - u) :=
    integral_nonneg fun u ↦ mul_nonneg ((hρ n).2.2.1 u) (hp0 _)
  have hb0 (n : ℕ) (t : ℝ) : 0 ≤ b n t := mul_nonneg ((hh n).2.2.2 t).1 (hI0 n t)
  have hb1 (n : ℕ) (t : ℝ) : b n t ≤ 1 := by
    have hI : ∫ u, ρ n u * p (t - u) ≤ 1 := by
      rw [← (hρ n).2.2.2.2]
      exact integral_mono (hint n t) (hρint n) fun u ↦
        mul_le_of_le_one_right ((hρ n).2.2.1 u) (hp1 _)
    exact mul_le_one₀ ((hh n).2.2.2 t).2 (hI0 n t) hI
  have hbm (n : ℕ) : Measurable (b n) := by
    have hk : Measurable (fun q : ℝ × ℝ ↦ ρ n q.2 * p (q.1 - q.2)) :=
      ((hρ n).2.1.continuous.measurable.comp measurable_snd).mul
        (hpm.comp (measurable_fst.sub measurable_snd))
    exact (hh n).1.continuous.measurable.mul hk.stronglyMeasurable.integral_prod_right'.measurable
  have hbsupp (n : ℕ) (t : ℝ) (hbt : b n t ≠ 0) : t ∈ tsupport (h n) :=
    subset_tsupport _ (left_ne_zero_of_mul hbt)
  have hblow (n : ℕ) (t : ℝ) (hεn : ε n ≤ 1) (ht1 : 1 + ε n < t) (ht2 : t < 2) :
      h n t / 9 ≤ b n t := by
    have hI : (1 / 9 : ℝ) ≤ ∫ u, ρ n u * p (t - u) := by
      calc (1 / 9 : ℝ) = ∫ u, ρ n u * (1 / 9) := by rw [integral_mul_const, (hρ n).2.2.2.2, one_mul]
        _ ≤ _ := integral_mono ((hρint n).mul_const _) (hint n t) fun u ↦ by
          by_cases hu : ρ n u = 0
          · simp [hu]
          obtain ⟨hl, hr⟩ := (hρ n).2.2.2.1 (subset_tsupport _ hu)
          refine mul_le_mul_of_nonneg_left ?_ ((hρ n).2.2.1 u)
          have hgt : 1 < t - u := by linarith
          have hlt : t - u ≤ 3 := by linarith
          simp only [p, if_pos hgt]
          rw [Real.rpow_neg (by linarith), Real.rpow_two, show (1 / 9 : ℝ) = (3 ^ 2)⁻¹ by norm_num]
          exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by linarith) hlt 2)
    calc h n t / 9 = h n t * (1 / 9) := by ring
      _ ≤ b n t := mul_le_mul_of_nonneg_left hI ((hh n).2.2.2 t).1
  -- The integrand in the real coordinate.
  let Φ : ℕ → ℝ → ℝ := fun n t ↦ b n |t| * √|t| / |1 - t|
  have hΦ0 (n : ℕ) (t : ℝ) : 0 ≤ Φ n t := by
    simp only [Φ]; have := hb0 n |t|; positivity
  have hΦm (n : ℕ) : Measurable (Φ n) :=
    (((hbm n).comp continuous_abs.measurable).mul (Real.continuous_sqrt.measurable.comp continuous_abs.measurable)).div
      (continuous_abs.measurable.comp (measurable_const.sub measurable_id))
  let X : ℕ → ENNReal := fun n ↦ ∫⁻ t, ENNReal.ofReal (Φ n t) * ENNReal.ofReal |t|⁻¹
  have hnorm (x : Rat.infinitePlace.Completion) : ‖x‖ = |e x| :=
    ((InfinitePlace.Completion.isometryEquivRealOfIsReal hw).isometry.norm_map_of_map_zero
      (map_zero e) x).symm.trans (Real.norm_eq_abs _)
  -- The real part of the archimedean term is half of `X n`.
  have hre (n : ℕ) : (∑ w : InfinitePlace ℚ,
      introTraceArchimedean (F := ℚ) 1 approx(h, ρ, n, (2 : ℂ)) w).re = (X n).toReal / 2 := by
    rw [Fintype.sum_subsingleton _ Rat.infinitePlace, introTraceArchimedean, if_pos hw]
    have hpt (u : Rat.infinitePlace.Completionˣ) :
        introTraceTest (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)) approx(h, ρ, n, (2 : ℂ))
            (IdeleClassGroup.ofCompletion (𝓞 ℚ) ℚ Rat.infinitePlace u) *
            (Real.sqrt (‖u.val‖ ^ InfinitePlace.mult Rat.infinitePlace) : ℂ) /
            ((‖1 - u.val‖ ^ InfinitePlace.mult Rat.infinitePlace : ℝ) : ℂ) =
          ((Φ n (e u) : ℝ) : ℂ) := by
      have hN : (((ideleClassNorm ℚ) (IdeleClassGroup.ofCompletion (𝓞 ℚ) ℚ Rat.infinitePlace u)).val : ℝ) =
          ‖(u : Rat.infinitePlace.Completion)‖ := by
        rw [ideleClassNorm_ofCompletion, hw.mult_eq_one, pow_one]
        rfl
      simp only [introTraceTest, PontryaginDual.one_apply, Circle.coe_one, star_one, one_mul,
        hw.mult_eq_one, pow_one, hN, happrox, Φ]
      rw [hnorm, hnorm, map_sub, map_one]
      push_cast
      rfl
    let : MeasurableSpace Rat.infinitePlace.Completion :=
      instMeasurableSpaceCompletion_riemannMasullo ℚ Rat.infinitePlace
    let : BorelSpace Rat.infinitePlace.Completion := ⟨rfl⟩
    let : BorelSpace Rat.infinitePlace.Completionˣ := borelSpace_units_of_continuousInv₀ _
    simp_rw [hpt]
    rw [integral_complex_ofReal]
    have hmeas : Measurable fun u : Rat.infinitePlace.Completionˣ ↦ Φ n (e u) :=
      (hΦm n).comp ((InfinitePlace.Completion.isometryEquivRealOfIsReal hw).continuous.measurable.comp
        Units.continuous_val.measurable)
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun u ↦ hΦ0 n _)
      hmeas.aestronglyMeasurable,
      introTraceApprox_rat_archimedean_tendsto_atTop_lintegral (fun t ↦ ENNReal.ofReal (Φ n t))
        (ENNReal.measurable_ofReal.comp (hΦm n))]
    simp only [one_div, Complex.re_mul_ofReal, Complex.inv_re, Complex.normSq_ofNat]
    norm_num
    ring
  -- Each `X n` is finite: the cutoff is supported in a compact subset of `(1, ∞)`.
  have hfin (n : ℕ) : X n ≠ ⊤ := by
    have hK : IsCompact (tsupport (h n)) := (hh n).2.1
    have hsub : tsupport (h n) ⊆ Ioi 1 := (hh n).2.2.1
    obtain ⟨c, hc1, hc⟩ : ∃ c, 1 < c ∧ ∀ x ∈ tsupport (h n), c ≤ x := by
      rcases (tsupport (h n)).eq_empty_or_nonempty with he | hne
      · exact ⟨2, by norm_num, by simp [he]⟩
      · obtain ⟨c, hcK, hcmin⟩ := hK.exists_isMinOn hne continuousOn_id
        exact ⟨c, hsub hcK, fun x hx ↦ hcmin hx⟩
    obtain ⟨R, hR⟩ := hK.bddAbove
    let M : ℝ := √R / (c - 1) * c⁻¹
    have hle (t : ℝ) : ENNReal.ofReal (Φ n t) * ENNReal.ofReal |t|⁻¹ ≤
        (Icc (-R) R).indicator (fun _ ↦ ENNReal.ofReal M) t := by
      by_cases hz : b n |t| = 0
      · simp [Φ, hz]
      have hmem := hbsupp n |t| hz
      have hct : c ≤ |t| := hc _ hmem
      have hRt : |t| ≤ R := hR hmem
      rw [indicator_of_mem (abs_le.mp hRt), ← ENNReal.ofReal_mul (hΦ0 n t)]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1t : c - 1 ≤ |1 - t| := by
        have := abs_sub_abs_le_abs_sub t 1
        rw [abs_one, abs_sub_comm] at this
        linarith
      have hc0 : 0 < c - 1 := by linarith
      have htpos : 0 < |t| := by linarith
      have hb := hb1 n |t|
      have hb' := hb0 n |t|
      simp only [Φ, M]
      calc b n |t| * √|t| / |1 - t| * |t|⁻¹ ≤ 1 * √R / (c - 1) * c⁻¹ := by
            gcongr
        _ = √R / (c - 1) * c⁻¹ := by rw [one_mul]
    refine ne_top_of_le_ne_top ?_ (lintegral_mono hle)
    rw [lintegral_indicator measurableSet_Icc, setLIntegral_const, Real.volume_Icc]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  -- The lower bounds `K n` and Fatou's lemma.
  let K : ℕ → ℝ → ENNReal := fun n ↦
    (Ioo (1 + ε n) 2).indicator fun t ↦ ENNReal.ofReal (h n t / (18 * (t - 1)))
  have hKm (n : ℕ) : Measurable (K n) :=
    (ENNReal.measurable_ofReal.comp ((hh n).1.continuous.measurable.div
      (measurable_const.mul (measurable_id.sub measurable_const)))).indicator measurableSet_Ioo
  have hKle : ∀ᶠ n in atTop, ∀ t, K n t ≤ ENNReal.ofReal (Φ n t) * ENNReal.ofReal |t|⁻¹ := by
    filter_upwards [hε.eventually_le_const (zero_lt_one : (0 : ℝ) < 1)] with n hn t
    simp only [K]
    by_cases ht : t ∈ Ioo (1 + ε n) 2
    · rw [indicator_of_mem ht, ← ENNReal.ofReal_mul (hΦ0 n t)]
      refine ENNReal.ofReal_le_ofReal ?_
      obtain ⟨ht1, ht2⟩ := ht
      have hεpos := (hρ n).1
      have htpos : 0 < t := by linarith
      have ht1' : 0 < t - 1 := by linarith
      have hbt := hblow n t hn ht1 ht2
      have hs0 : 0 < √t := Real.sqrt_pos.mpr htpos
      have hs2 : √t ≤ 2 := by
        calc √t ≤ √4 := Real.sqrt_le_sqrt (by linarith)
          _ = 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      have hst : √t * t⁻¹ = (√t)⁻¹ := by
        calc √t * t⁻¹ = √t * (√t * √t)⁻¹ := by rw [Real.mul_self_sqrt htpos.le]
          _ = (√t)⁻¹ := by field_simp
      have hsq : 1 / 2 ≤ √t * t⁻¹ := by
        rw [hst, one_div]
        exact inv_anti₀ hs0 hs2
      simp only [Φ]
      rw [abs_of_pos htpos, abs_sub_comm, abs_of_pos ht1']
      have hh0 : 0 ≤ h n t / 9 := div_nonneg ((hh n).2.2.2 t).1 (by norm_num)
      calc h n t / (18 * (t - 1)) = (h n t / 9) * (1 / 2) / (t - 1) := by field_simp; ring
        _ ≤ b n t * (√t * t⁻¹) / (t - 1) :=
          div_le_div_of_nonneg_right (mul_le_mul hbt hsq (by norm_num) (hb0 n t)) ht1'.le
        _ = b n t * √t / (t - 1) * t⁻¹ := by ring
    · rw [indicator_of_notMem ht]
      exact bot_le
  have hliminf : ∀ t, (Ioo 1 2).indicator (fun t ↦ ENNReal.ofReal (1 / (18 * (t - 1)))) t ≤
      liminf (fun n ↦ K n t) atTop := by
    intro t
    by_cases ht : t ∈ Ioo 1 2
    · rw [indicator_of_mem ht]
      have hev : ∀ᶠ n in atTop, K n t = ENNReal.ofReal (h n t / (18 * (t - 1))) := by
        filter_upwards [hε.eventually (gt_mem_nhds (sub_pos.mpr ht.1))] with n hn
        simp only [K]
        exact indicator_of_mem (show t ∈ Ioo (1 + ε n) 2 from ⟨by linarith, ht.2⟩) _
      have hlim : Tendsto (fun n ↦ K n t) atTop (𝓝 (ENNReal.ofReal (1 / (18 * (t - 1))))) :=
        (ENNReal.tendsto_ofReal ((hhlim t ht.1).div_const _)).congr' (hev.mono fun n hn ↦ hn.symm)
      exact hlim.liminf_eq.ge
    · rw [indicator_of_notMem ht]
      exact bot_le
  have hdiv : ∫⁻ t, (Ioo 1 2).indicator (fun t ↦ ENNReal.ofReal (1 / (18 * (t - 1)))) t = ⊤ := by
    rw [lintegral_indicator measurableSet_Ioo]
    by_contra hne
    have hi : IntegrableOn (fun t : ℝ ↦ 1 / (18 * (t - 1))) (Ioo (1 : ℝ) 2) := by
      have := integrable_toReal_of_lintegral_ne_top (μ := volume.restrict (Ioo (1 : ℝ) 2))
        (ENNReal.measurable_ofReal.comp (measurable_const.div
          (measurable_const.mul (measurable_id.sub measurable_const)))).aemeasurable hne
      refine this.congr ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun t ht ↦ ?_))
      have : 0 ≤ 1 / (18 * (t - 1)) := by have := ht.1; positivity
      exact ENNReal.toReal_ofReal this
    have hii : IntervalIntegrable (fun t : ℝ ↦ (t - 1)⁻¹) volume 1 2 := by
      rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)]
      refine IntegrableOn.congr_fun (Integrable.const_mul hi 18) (fun t ht ↦ ?_) measurableSet_Ioo
      have : t - 1 ≠ 0 := by have := ht.1; linarith
      field_simp
    rw [intervalIntegrable_sub_inv_iff] at hii
    rcases hii with h12 | h1
    · norm_num at h12
    · exact h1 (by simp)
  have hX : liminf X atTop = ⊤ := by
    refine top_le_iff.mp ?_
    calc (⊤ : ENNReal) = ∫⁻ t, (Ioo 1 2).indicator (fun t ↦ ENNReal.ofReal (1 / (18 * (t - 1)))) t :=
          hdiv.symm
      _ ≤ ∫⁻ t, liminf (fun n ↦ K n t) atTop := lintegral_mono hliminf
      _ ≤ liminf (fun n ↦ ∫⁻ t, K n t) atTop := lintegral_liminf_le hKm
      _ ≤ liminf X atTop := liminf_le_liminf (hKle.mono fun n hn ↦ lintegral_mono hn)
  -- Conclusion.
  simp_rw [hre]
  refine tendsto_atTop.mpr fun M ↦ ?_
  have hlt : ENNReal.ofReal (2 * max M 0) < liminf X atTop := by rw [hX]; exact ENNReal.ofReal_lt_top
  filter_upwards [eventually_lt_of_lt_liminf hlt] with n hn
  have := (ENNReal.ofReal_lt_iff_lt_toReal (by positivity) (hfin n)).mp hn
  have := le_max_left M 0
  linarith

/-- Paper: §1.4.3, p. 29. A common subsequence of the two archimedean sums
has holomorphic limits on the interior of the compact set if the stated
uniform bounds hold.
Deviation: The bounds are hypotheses of the Montel implication. The real-place
bound fails for the rational trivial character. -/
theorem introTrace_montel_of_bounded (K : Set ℂ) (_hK : IsCompact K)
    (A B : ℕ → ℂ → ℂ) (_hA : ∀ n, DifferentiableOn ℂ (A n) (interior K))
    (_hB : ∀ n, DifferentiableOn ℂ (B n) (interior K))
    (_hbound : ∃ C : ℝ, 0 < C ∧ ∀ n z, z ∈ K → ‖A n z‖ ≤ C ∧ ‖B n z‖ ≤ C) :
    ∃ (k : ℕ → ℕ) (L₁ L₂ : ℂ → ℂ), StrictMono k ∧
      TendstoLocallyUniformlyOn (A ∘ k) L₁ atTop (interior K) ∧
      TendstoLocallyUniformlyOn (B ∘ k) L₂ atTop (interior K) ∧
      AnalyticOnNhd ℂ L₁ (interior K) ∧ AnalyticOnNhd ℂ L₂ (interior K) := by
  rcases _hbound with ⟨C, _, hC⟩
  have hdiff : ∀ n, DifferentiableOn ℂ (fun z ↦ (A n z, B n z)) (interior K) :=
    fun n ↦ (_hA n).prodMk (_hB n)
  have hbounded : External.TauCeti.IsLocallyBoundedOn
      (fun n z ↦ (A n z, B n z)) (interior K) :=
    External.TauCeti.isLocallyBoundedOn_of_forall_norm_le fun n z hz ↦
      norm_prod_le_iff.mpr (hC n z (interior_subset hz))
  obtain ⟨k, L, hk, hL, hconv⟩ := External.TauCeti.montel isOpen_interior hdiff hbounded
  exact ⟨k, Prod.fst ∘ L, Prod.snd ∘ L, hk,
    uniformContinuous_fst.comp_tendstoLocallyUniformlyOn hconv,
    uniformContinuous_snd.comp_tendstoLocallyUniformlyOn hconv,
    hL.fst.analyticOnNhd isOpen_interior, hL.snd.analyticOnNhd isOpen_interior⟩

-- TODO(paper-gap): Pointwise convergence of the individual Mellin terms
-- leaves the infinite zero sum uncontrolled. At the trivial rational character and
-- a window containing the full divisor the zero sum itself diverges at z = 2.

/-- Paper: §1.4.3, p. 29. At each fixed cutoff the zero sum converges at every
parameter. This gives the totalized spectral sum its intended value in every chart. -/
theorem introTraceApprox_spectral_summable (χ : U𝔽) (h ρ : ℕ → ℝ → ℝ)
    (_hA : IsIntroTraceApproximation h ρ) (n : ℕ) (a : ℝ) (_ha : 0 < a) (z : ℂ) :
    Summable (fun r : windowZeros(χ, a) ↦
      (zeroOrder(χ, r.val) : ℂ) * introTraceMellin approx(h, ρ, n, z) (r.val - 1 / 2)) := by sorry

/-- Paper: §1.4.3, p. 29. Each fixed-cutoff zero sum is entire in the
test parameter.
Deviation: The sum uses full zero orders and the corrected centered window.
Passing to a holomorphic limit needs a further estimate on the zero sum. -/
theorem introTraceApprox_spectral_differentiable (χ : U𝔽) (h ρ : ℕ → ℝ → ℝ)
    (_hA : IsIntroTraceApproximation h ρ) (n : ℕ) (a : ℝ) (_ha : 0 < a) :
    Differentiable ℂ (fun z ↦ introTraceSpectralSum χ approx(h, ρ, n, z) a) := by sorry

/-- At parameter two the radial approximant is real and nonnegative. -/
private theorem introTraceApprox_rat_spectral_tendsto_atBot_profile (h ρ : ℕ → ℝ → ℝ)
    (hA : IsIntroTraceApproximation h ρ) (n : ℕ) :
    ∃ g : ℝ → ℝ, (∀ t, 0 ≤ g t) ∧ approx(h, ρ, n, (2 : ℂ)) = fun t ↦ (g t : ℂ) := by
  let P (x : ℝ) : ℝ := if 1 < x then (x ^ 2)⁻¹ else if x = 1 then 1 / 2 else 0
  have hP (x : ℝ) : introTracePower 2 x = (P x : ℂ) := by
    unfold introTracePower P
    split_ifs <;> norm_num [Complex.cpow_neg]
  obtain ⟨ε, _, hρ⟩ := hA.2.2.2
  refine ⟨fun t ↦ h n t * ∫ u, ρ n u * P (t - u), fun t ↦ ?_, ?_⟩
  · apply mul_nonneg ((hA.1 n).2.2.2 t).1
    apply integral_nonneg
    intro u
    apply mul_nonneg ((hρ n).2.2.1 u)
    unfold P
    split_ifs <;> positivity
  · funext t
    simp only [introTraceApprox, hP, ← Complex.ofReal_mul, integral_complex_ofReal]

/-- With a nonnegative real radial profile the real part of each trivial-character
prime-power contribution is nonnegative. -/
private theorem introTraceApprox_rat_spectral_tendsto_atBot_prime_nonneg (g : ℝ → ℝ)
    (hg : ∀ t, 0 ≤ g t) (v : HeightOneSpectrum (𝓞 ℚ)) (k : ℕ) :
    0 ≤ (introTracePrimePower (F := ℚ) 1 (fun t ↦ (g t : ℂ)) v k).re := by
  classical
  have htriv : ideleClassNormTwist (F := ℚ) 1 0 = 1 := by
    ext1 x
    change (1 : ℂ) * _ ^ (0 : ℂ) = 1
    simp
  have hunit (u : (v.adicCompletion ℚ)ˣ) :
      (1 : HeckeCharacter (𝓞 ℚ) ℚ).restrict v u = 1 := by
    rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
    rfl
  let val : Valuation (v.adicCompletion ℚ) (WithZero (Multiplicative ℤ)) := Valued.v
  have hv : (1 : HeckeCharacter (𝓞 ℚ) ℚ).localValue v = 1 :=
    hunit (Units.mk0 _ val.exists_isUniformizer_of_isCyclic_of_nontrivial.choose_spec.ne_zero)
  let q : ℝ := v.asIdeal.absNorm
  have hq : 1 ≤ q := by
    dsimp only [q]
    exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm v).le
  have hden : (q : ℂ) ^ (((k + 1 : ℕ) : ℂ) / 2) = ((q ^ ((k + 1 : ℝ) / 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (zero_le_one.trans hq)]
    push_cast
    rfl
  simp only [introTracePrimePower, htriv]
  split_ifs
  · simp only [hv, one_pow, star_one, one_mul]
    change 0 ≤ ((Real.log q : ℂ) * ((g (q ^ (k + 1)) : ℂ) + (g ((q ^ (k + 1))⁻¹) : ℂ)) /
      (q : ℂ) ^ (((k + 1 : ℕ) : ℂ) / 2)).re
    rw [hden, ← Complex.ofReal_add, ← Complex.ofReal_mul, ← Complex.ofReal_div, Complex.ofReal_re]
    exact div_nonneg (mul_nonneg (Real.log_nonneg hq) (add_nonneg (hg _) (hg _)))
      (Real.rpow_nonneg (zero_le_one.trans hq) _)
  · exact le_rfl

/-- Paper: §1.4.3, p. 29. For the trivial rational character, the zero
sum in the window of half-width one has real part tending to minus infinity
at parameter two.
Deviation: This replaces the claimed separate holomorphic spectral limit.
The full explicit formula suffices for this window because it contains all zeros. -/
theorem introTraceApprox_rat_spectral_tendsto_atBot (h ρ : ℕ → ℝ → ℝ)
    (_hA : IsIntroTraceApproximation h ρ) :
    Tendsto (fun n ↦ (introTraceSpectralSum (F := ℚ) 1 approx(h, ρ, n, (2 : ℂ)) 1).re)
      atTop atBot := by
  classical
  let a (n : ℕ) := approx(h, ρ, n, (2 : ℂ))
  let M (n : ℕ) := introTraceMellin (a n) (1 / 2) + introTraceMellin (a n) (-1 / 2)
  let A (n : ℕ) := ∑ w : InfinitePlace ℚ, introTraceArchimedean (F := ℚ) 1 (a n) w
  let m := (introTraceMellin (introTracePower 2) (1 / 2) +
    introTraceMellin (introTracePower 2) (-1 / 2)).re
  have hM := ((introTraceApprox_mellin_tendsto h ρ _hA (1 / 2)).tendsto_at
    (a := (2 : ℂ)) (by norm_num)).add
    ((introTraceApprox_mellin_tendsto h ρ _hA (-1 / 2)).tendsto_at (a := (2 : ℂ)) (by norm_num))
  have hbound := ((Complex.continuous_re.tendsto _).comp hM).eventually
    (eventually_lt_nhds (lt_add_one m))
  have hArch := introTraceApprox_rat_archimedean_tendsto_atTop h ρ _hA
  let τ : ℝ≥0ˣ →ₜ* IdeleClassGroup (𝓞 ℚ) ℚ :=
    ⟨(QuotientGroup.mk' _).comp (canonicalIdeleNormSection ℚ),
      continuous_quotient_mk'.comp (canonicalIdeleNormSection_continuous _)⟩
  apply tendsto_atBot.2
  intro b
  filter_upwards [hbound, (tendsto_atTop.1 hArch) (m + 1 - b)] with n hn hAn
  obtain ⟨φ, hφ⟩ := introTraceApprox_exists_bruhat (F := ℚ) 1 h ρ _hA n 2
  have hzero : a n 1 = 0 := image_eq_zero_of_notMem_tsupport
    (fun ht ↦ lt_irrefl _ (introTraceApprox_support h ρ _hA n 2 ht))
  have ht := introTrace_characterTrace τ (canonicalIdeleNormSection_rightInverse ℚ) 1
    (fun _ ↦ rfl) (a n) hzero φ hφ 1 one_pos
  have he := ht.2.2.tsum_eq
  simp only at he
  change introTraceSpectralSum (F := ℚ) 1 (a n) 1 = M n - A n -
    ∑' p : HeightOneSpectrum (𝓞 ℚ) × ℕ, introTracePrimePower (F := ℚ) 1 (a n) p.1 p.2 at he
  change (introTraceSpectralSum (F := ℚ) 1 (a n) 1).re ≤ b
  rw [he, Complex.sub_re, Complex.sub_re, Complex.re_tsum ht.2.1]
  obtain ⟨g, hg, hag⟩ := introTraceApprox_rat_spectral_tendsto_atBot_profile h ρ _hA n
  have hp : 0 ≤ ∑' p : HeightOneSpectrum (𝓞 ℚ) × ℕ,
      (introTracePrimePower (F := ℚ) 1 (a n) p.1 p.2).re := by
    rw [show a n = _ from hag]
    exact tsum_nonneg fun p ↦ introTraceApprox_rat_spectral_tendsto_atBot_prime_nonneg g hg p.1 p.2
  change (M n).re < _ at hn
  change _ ≤ (A n).re at hAn
  linarith

/-- Paper: §1.4.4, p. 29. The negative prime-power norms lie below one,
where every cutoff test vanishes. -/
theorem introTraceApprox_primePower_inv_zero (h ρ : ℕ → ℝ → ℝ)
    (_hA : IsIntroTraceApproximation h ρ) (n : ℕ) (z : ℂ) (v : V) (m : ℕ) (_hm : 0 < m) :
    approx(h, ρ, n, z) ((q(v) ^ m)⁻¹) = 0 := by
  have hq : 1 ≤ q(v) := by exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm v).le
  have hle : (q(v) ^ m)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hq)
  apply image_eq_zero_of_notMem_tsupport
  exact fun ht ↦ hle.not_gt (introTraceApprox_support h ρ _hA n z ht)

/-- Paper: §1.4.4, p. 29. The finite terms converge locally uniformly to
the negative logarithmic derivative of the finite Hecke L-function.
Deviation: The sign is negative by differentiation of the Euler product,
as in `finiteHeckeL_logDeriv_hasSum_ideals`. The same argument works on
`Re z > 1/2`, the absolute-convergence region for `s = z + 1/2`.
The local coefficients include the unit averaging in the corrected trace formula. -/
theorem introTraceApprox_primeSum_tendsto (χ : U𝔽) (h ρ : ℕ → ℝ → ℝ)
    (_hA : IsIntroTraceApproximation h ρ) :
    TendstoLocallyUniformlyOn (fun n z ↦ primeSum(χ, approx(h, ρ, n, z)))
      (fun z ↦ -logDeriv finiteL(χ) (z + 1 / 2)) atTop right(1 / 2) := by sorry

open Classical in
/-- Paper: §1.4.5, pp. 29–30. If the archimedean and zero terms together
converge on the common half-plane to the restriction of a holomorphic
function on the right of the window, that function extends the regularized
shifted logarithmic derivative.
Deviation: The two polar moments are added to the logarithmic derivative
because the finite sum tends to its negative. The character is normalized
on the norm section so the poles have the printed coordinates. The corrected
trace formula gives the identity at each cutoff with the centered zero window
and normalized local terms. Neither separate Montel limit in the sketch
supplies the hypothesis on the combined terms. -/
theorem introTrace_logDeriv_extension_of_limit (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (_hτ : RightInverse τ (ideleClassNorm F)) (χ : U𝔽) (_hχ : ∀ t, χ (τ t) = 1)
    (a : ℝ) (_ha : 0 < a) (h ρ : ℕ → ℝ → ℝ) (_hA : IsIntroTraceApproximation h ρ)
    (H : ℂ → ℂ) (_hH : AnalyticOnNhd ℂ H right(a))
    (_hlim : TendstoLocallyUniformlyOn
      (fun n z ↦ archSum(χ, approx(h, ρ, n, z)) + introTraceSpectralSum χ approx(h, ρ, n, z) a)
      H atTop right(max a 1)) :
    EqOn H (fun z ↦ logDeriv finiteL(χ) (z + 1 / 2) +
      if χ = 1 then 1 / (z + 1 / 2) + 1 / (z - 1 / 2) else 0) right(max a 1) := by
  classical
  intro z hz
  have hz₁ : 1 < z.re := (le_max_right a 1).trans_lt hz
  have hp : (1 / 2 : ℂ).re < z.re := by norm_num; linarith
  have hm : (-1 / 2 : ℂ).re < z.re := by norm_num; linarith
  have hprime := (introTraceApprox_primeSum_tendsto χ h ρ _hA).tendsto_at
    (a := z) (show 1 / 2 < z.re by linarith)
  let P (n : ℕ) := if χ = 1 then introTraceMellin approx(h, ρ, n, z) (1 / 2) +
    introTraceMellin approx(h, ρ, n, z) (-1 / 2) else 0
  have he (n : ℕ) : archSum(χ, approx(h, ρ, n, z)) +
      introTraceSpectralSum χ approx(h, ρ, n, z) a = P n - primeSum(χ, approx(h, ρ, n, z)) := by
    obtain ⟨φ, hφ⟩ := introTraceApprox_exists_bruhat χ h ρ _hA n z
    have hzero : approx(h, ρ, n, z) 1 = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hu ↦ lt_irrefl _ (introTraceApprox_support h ρ _hA n z hu))
    have hsum := (introTrace_characterTrace τ _hτ χ _hχ _ hzero φ hφ a _ha).2.2.tsum_eq
    change introTraceSpectralSum χ approx(h, ρ, n, z) a =
      P n - archSum(χ, approx(h, ρ, n, z)) - primeSum(χ, approx(h, ρ, n, z)) at hsum
    rw [hsum]
    ring
  have hpolar : Tendsto P atTop
      (𝓝 (if χ = 1 then 1 / (z + 1 / 2) + 1 / (z - 1 / 2) else 0)) := by
    by_cases htriv : χ = 1
    · simp only [P, ite_eq_left htriv]
      have h₁ := (introTraceApprox_mellin_tendsto h ρ _hA (1 / 2)).tendsto_at hp
      have h₂ := (introTraceApprox_mellin_tendsto h ρ _hA (-1 / 2)).tendsto_at hm
      rw [(introTracePower_mellin z _ hp).2] at h₁
      rw [(introTracePower_mellin z _ hm).2] at h₂
      simpa [sub_neg_eq_add, neg_div, add_comm] using h₁.add h₂
    · simp [P, htriv]
  have hlim := _hlim.tendsto_at hz
  simp_rw [he] at hlim
  simpa only [sub_neg_eq_add, add_comm] using tendsto_nhds_unique hlim (hpolar.sub hprime)

-- TODO(paper-gap): The reference to §5.1 on p. 29 (also p. 55) supplies no
-- continuation argument. The corrected cutoff identity does not itself bound
-- the separate terms or provide the holomorphic limit of their sum.

/-- Paper: §1.4.5, pp. 29–30. In each normalized chart a holomorphic function
on the right of the window agrees on the common half-plane with the limit of
the combined archimedean and spectral terms for a cofinal family of tests.
Gap: The separate limits on p. 29 diverge for the trivial rational character.
The paper gives no extension of the combined value across the overlap.
Deviation: Only the restriction of the extension to the overlap must be a
cutoff limit. One cofinal family for each chart and width suffices. -/
theorem introTrace_combined_limit_extension (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (_hτ : RightInverse τ (ideleClassNorm F)) (χ : U𝔽) (_hχ : ∀ t, χ (τ t) = 1)
    (a : ℝ) (_ha : 0 < a) :
    ∃ (h ρ : ℕ → ℝ → ℝ) (H : ℂ → ℂ), IsIntroTraceApproximation h ρ ∧
      AnalyticOnNhd ℂ H right(a) ∧ TendstoLocallyUniformlyOn
        (fun n z ↦ archSum(χ, approx(h, ρ, n, z)) + introTraceSpectralSum χ approx(h, ρ, n, z) a)
        H atTop right(max a 1) := by sorry

open Classical in
/-- Paper: §1.4.5, p. 30. Continuation from every positive half-width gives
holomorphy of the shifted logarithmic derivative throughout the right half-plane
except for the possible shifted pole in the trivial character.
Deviation: The regularizing term has the sign dictated by the corrected Euler
sum. Meromorphic continuation on the overlap is used before concluding
holomorphy of the pointwise logarithmic derivative away from the pole. -/
theorem introTrace_logDeriv_analytic_of_extensions (χ : U𝔽)
    (_h : ∀ a : ℝ, 0 < a → ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H right(a) ∧
      EqOn H (fun z ↦ logDeriv finiteL(χ) (z + 1 / 2) +
        if χ = 1 then 1 / (z + 1 / 2) + 1 / (z - 1 / 2) else 0) right(max a 1)) :
    AnalyticOnNhd ℂ (fun z ↦ logDeriv finiteL(χ) (z + 1 / 2))
      {z : ℂ | 0 < z.re ∧ (χ ≠ 1 ∨ z ≠ 1 / 2)} := by
  let L := finiteL(χ)
  have hL : MeromorphicNFOn L univ := (finiteHeckeL_exists_continuation χ).choose_spec.1
  have hfinite (w : ℂ) : meromorphicOrderAt L w ≠ ⊤ := by
    apply hL.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
      isPreconnected_univ (x := 2) (mem_univ _) (mem_univ w)
    have htwo : L 2 ≠ 0 := by
      rw [show L 2 = finiteHeckeL χ ⟨2, by norm_num⟩ from
        (finiteHeckeL_exists_continuation χ).choose_spec.2 ⟨2, by norm_num⟩]
      exact finiteHeckeL_ne_zero_of_one_lt_re χ ⟨2, by norm_num⟩
    rw [(hL (mem_univ (2 : ℂ))).meromorphicOrderAt_eq_zero_iff.mpr htwo]
    exact WithTop.zero_ne_top
  intro z hz
  obtain ⟨H, hH, hEq⟩ := _h (z.re / 2) (half_pos hz.1)
  let R : ℂ → ℂ := fun w ↦
    if χ = 1 then 1 / (w + 1 / 2) + 1 / (w - 1 / 2) else 0
  let D : ℂ → ℂ := fun w ↦ logDeriv L (w + 1 / 2)
  have hD : Meromorphic D := by
    intro w
    exact meromorphicAt_comp_add_const_iff_meromorphicAt.mpr
      (hL (mem_univ (w + 1 / 2))).meromorphicAt.logDeriv
  have hR : Meromorphic R := by
    intro w
    dsimp only [R]
    split_ifs <;> fun_prop
  let A := H - R
  have hA : MeromorphicOn A right(z.re / 2) :=
    hH.meromorphicOn.sub (fun w _ ↦ hR w)
  -- Continue equality of punctured germs, without assuming regularity at zeros or poles.
  let q : ℂ := (max (z.re / 2) 1 + 1 : ℝ)
  have hq : max (z.re / 2) 1 < q.re := by simp [q]
  have hbase : meromorphicOrderAt (D - A) q = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    have hnear : ∀ᶠ w : ℂ in 𝓝 q, max (z.re / 2) 1 < w.re :=
      Complex.continuous_re.continuousAt.eventually (eventually_gt_nhds hq)
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds] with w hw
    have he : H w = D w + R w := hEq hw
    change D w - (H w - R w) = 0
    rw [he]
    ring
  have hzhalf : z ∈ right(z.re / 2) := by change z.re / 2 < z.re; linarith [hz.1]
  have hqhalf : q ∈ right(z.re / 2) := (le_max_left _ _).trans_lt hq
  have hDm : MeromorphicOn D right(z.re / 2) := fun w _ ↦ hD w
  have horder := (hDm.sub hA).meromorphicOrderAt_eq_top_of_isPreconnected
    (convex_halfSpace_re_gt _).isPreconnected hqhalf hzhalf hbase
  have hnear : D =ᶠ[𝓝[≠] z] A :=
    (meromorphicOrderAt_eq_top_iff.mp horder).mono fun w hw ↦ sub_eq_zero.mp hw
  have hRz : AnalyticAt ℂ R z := by
    dsimp only [R]
    split_ifs with hχ
    · have hp : z + 1 / 2 ≠ 0 := by
        intro hzero
        have hre := congrArg Complex.re hzero
        norm_num at hre
        linarith [hz.1]
      have hm : z - 1 / 2 ≠ 0 := sub_ne_zero.mpr (hz.2.resolve_left (not_not.mpr hχ))
      have hpa : AnalyticAt ℂ (fun w : ℂ ↦ w + 1 / 2) z := by fun_prop
      have hma : AnalyticAt ℂ (fun w : ℂ ↦ w - 1 / 2) z := by fun_prop
      exact (analyticAt_const.div hpa hp).add (analyticAt_const.div hma hm)
    · exact analyticAt_const
  have hnonneg : 0 ≤ meromorphicOrderAt D z := by
    rw [meromorphicOrderAt_congr hnear]
    exact ((hH z hzhalf).sub hRz).meromorphicOrderAt_nonneg
  change 0 ≤ meromorphicOrderAt (logDeriv L ∘ (· + (1 / 2 : ℂ))) z at hnonneg
  rw [meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt] at hnonneg
  -- A zero or pole of L would give its logarithmic derivative a simple pole.
  have hzero : meromorphicOrderAt L (z + 1 / 2) = 0 := by
    by_contra hzero
    rw [meromorphicOrderAt_logDeriv_eq_neg_one hzero (hfinite _)] at hnonneg
    exact (by decide : ¬ (0 : WithTop ℤ) ≤ -1) hnonneg
  have hnormal := hL (mem_univ (z + 1 / 2))
  have ha := hnormal.meromorphicOrderAt_nonneg_iff_analyticAt.mp (le_of_eq hzero.symm)
  exact (ha.deriv.div ha (hnormal.meromorphicOrderAt_eq_zero_iff.mp hzero)).comp
    (f := fun w : ℂ ↦ w + 1 / 2) (x := z) (by fun_prop)

/-- Paper: §1.4.5, p. 30. A holomorphic shifted logarithmic derivative
excludes finite Hecke zeros to the right of one half. The exceptional point
for the trivial character is a pole of the finite L-function. -/
theorem introTrace_finiteL_no_right_zeros (χ : U𝔽)
    (_h : AnalyticOnNhd ℂ (fun z ↦ logDeriv finiteL(χ) (z + 1 / 2))
      {z : ℂ | 0 < z.re ∧ (χ ≠ 1 ∨ z ≠ 1 / 2)}) (s : ℂ) (_hs : 1 / 2 < s.re) :
    meromorphicOrderAt finiteL(χ) s ≤ 0 := by
  let L := finiteL(χ)
  have hL := (finiteHeckeL_exists_continuation χ).choose_spec
  have hr (z : ℂ) (hz : 1 ≤ z.re) : meromorphicOrderAt L z ≤ 0 := by
    obtain ⟨A, hA, h⟩ := finiteHeckeL_zeroFreeRegion
    obtain ⟨B, hB, hzero⟩ := h F χ
    have hl : 0 ≤ Real.log (B * (|z.im| + 3)) := Real.log_nonneg (by
      have := mul_nonneg (show 0 ≤ B by linarith) (abs_nonneg z.im)
      nlinarith)
    exact hzero L hL.1 hL.2 z ((sub_le_self _ (div_nonneg hA.le
      (mul_nonneg (by positivity) hl))).trans hz)
  by_cases he : s = 1
  · exact hr s (by simp [he])
  have hne : meromorphicOrderAt L s ≠ ⊤ := hL.1.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (mem_univ (2 : ℂ)) (mem_univ s)
    ((hr 2 (by norm_num)).trans_lt (show (0 : WithTop ℤ) < ⊤ by simp)).ne
  have hs : 0 < (s - 1 / 2).re := by
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
    linarith
  have hx : s - 1 / 2 ≠ 1 / 2 := fun h ↦ he (by linear_combination h)
  have han := (_h (s - 1 / 2) ⟨hs, Or.inr hx⟩).comp (f := fun z : ℂ ↦ z - 1 / 2)
    (analyticAt_id.sub analyticAt_const)
  have ha : AnalyticAt ℂ (logDeriv L) s := by simpa [Function.comp_def, L] using han
  by_contra! hp
  have hn := ha.meromorphicOrderAt_nonneg
  rw [meromorphicOrderAt_logDeriv_eq_neg_one hp.ne' hne] at hn
  have hi : (0 : ℤ) ≤ -1 := WithTop.coe_le_coe.mp hn
  omega

/-- Paper: §1.4.5, p. 30. Right-hand nonvanishing for the finite continuations
in the section-normalized characters implies right-hand nonvanishing for every
completed continuation. Imaginary norm twists translate the exponent, and the
gamma factors are regular and nonzero in the positive half-plane. -/
theorem introTrace_completedL_no_right_zeros (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (_hτ : RightInverse τ (ideleClassNorm F))
    (_h : ∀ (ψ : U𝔽), (∀ t, ψ (τ t) = 1) →
      ∀ s : ℂ, 1 / 2 < s.re → meromorphicOrderAt finiteL(ψ) s ≤ 0)
    (χ : U𝔽) (s : ℂ) (_hs : 1 / 2 < s.re) :
    meromorphicOrderAt (continuedCompletedHeckeL χ) s ≤ 0 := by
  let n : C𝔽 →ₜ* ℝ≥0ˣ := ⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩
  let j : Circle →ₜ* ℂ := ⟨Circle.coeHom, continuous_subtype_val⟩
  obtain ⟨a, ⟨ha, hpower⟩, -⟩ :=
    existsUnique_unitaryComplexPower (j.comp (χ.comp τ)) (fun t ↦ Circle.norm_coe _)
  let η : U𝔽 := χ.comp (τ.comp n)
  let ψ : U𝔽 := χ / η
  have hnorm (t : ℝ≥0ˣ) : ψ (τ t) = 1 := by
    change χ (τ t) / χ (τ (ideleClassNorm F (τ t))) = 1
    rw [_hτ t, div_self']
  have htwist : ideleClassNormTwist ψ 0 = ideleClassNormTwist χ (-a) := by
    ext1 g
    change ((χ g : ℂ) / (χ (τ (ideleClassNorm F g)) : ℂ)) *
      (N(g) : ℂ) ^ (0 : ℂ) = (χ g : ℂ) * (N(g) : ℂ) ^ (-a)
    rw [Complex.cpow_zero, mul_one, Complex.cpow_neg, div_eq_mul_inv]
    exact congrArg (fun w : ℂ ↦ (χ g : ℂ) * w⁻¹) (hpower (ideleClassNorm F g))
  let G (z : ℂ) := (heckeGammaFactor χ z)⁻¹
  let L := continuedCompletedHeckeL χ
  let H (z : ℂ) := finiteL(ψ) (z + a)
  have hG : Differentiable ℂ G := differentiable_inv_heckeGammaFactor χ
  have hL := continuedCompletedHeckeL_spec χ
  have hF := (finiteHeckeL_exists_continuation ψ).choose_spec
  have hH : MeromorphicOn H univ := fun z _ ↦
    ((hF.1 (mem_univ (z + a))).meromorphicAt).comp_analyticAt (g := fun w : ℂ ↦ w + a) (by fun_prop)
  have hGL : MeromorphicOn (fun z ↦ G z * L z) univ :=
    fun z hz ↦ (hG.analyticAt z).meromorphicAt.mul (hL.1 hz).meromorphicAt
  have hEq (z : ℂ) (hz : 1 < z.re) : H z = G z * L z := by
    have hw : 1 < (z + a).re := by rwa [Complex.add_re, ha, add_zero]
    let w : {z : ℂ // 1 < z.re} := ⟨z, hz⟩
    have ht : finiteHeckeL ψ ⟨z + a, hw⟩ = finiteHeckeL χ w := by
      simpa [w, add_assoc] using
        finiteHeckeL_imaginary_twist χ ψ (-a) (by simp [ha]) htwist ⟨z + a, hw⟩
    calc
      H z = finiteHeckeL ψ ⟨z + a, hw⟩ := hF.2 ⟨z + a, hw⟩
      _ = finiteHeckeL χ w := ht
      _ = G z * completedHeckeL χ w :=
        (inv_mul_cancel_left₀ (heckeGammaFactor_ne_zero_of_re_pos χ (zero_lt_one.trans hz)) _).symm
      _ = G z * L z := congrArg (G z * ·) (hL.2 w).symm
  have hnear : ∀ᶠ z in 𝓝 (2 : ℂ), 1 < z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  have htop : meromorphicOrderAt (H - fun z ↦ G z * L z) 2 = ⊤ :=
    meromorphicOrderAt_eq_top_iff.mpr (eventuallyEq_iff_sub.mp
      ((hnear.mono hEq).filter_mono nhdsWithin_le_nhds))
  have ho := (hH.sub hGL).meromorphicOrderAt_eq_top_of_isPreconnected
    isPreconnected_univ (mem_univ (2 : ℂ)) (mem_univ s) htop
  have hlocal : H =ᶠ[𝓝[≠] s] (fun z ↦ G z * L z) :=
    eventuallyEq_iff_sub.mpr (meromorphicOrderAt_eq_top_iff.mp ho)
  have hord : meromorphicOrderAt H s = meromorphicOrderAt L s := by
    rw [meromorphicOrderAt_congr hlocal]
    exact meromorphicOrderAt_mul_of_ne_zero (hG.analyticAt s)
      (inv_ne_zero (heckeGammaFactor_ne_zero_of_re_pos χ (by linarith)))
  change meromorphicOrderAt L s ≤ 0
  rw [← hord]
  change meromorphicOrderAt (fun z ↦ finiteL(ψ) (z + a)) s ≤ 0
  rw [meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt]
  exact _h ψ hnorm (s + a) (by rwa [Complex.add_re, ha, add_zero])

/-- Paper: §1.4.5, p. 30. The completed functional equation reflects the
zero-free region for the inverse character to the left of one half for the
original character. -/
theorem introTrace_completedL_no_left_zeros (χ : U𝔽)
    (_h : ∀ s : ℂ, 1 / 2 < s.re → meromorphicOrderAt (continuedCompletedHeckeL χ⁻¹) s ≤ 0)
    (s : ℂ) (_hs : s.re < 1 / 2) :
    meromorphicOrderAt (continuedCompletedHeckeL χ) s ≤ 0 := by
  obtain ⟨ε, hε, hne, he⟩ := completedHeckeL_continuation_functionalEquation χ
    (continuedCompletedHeckeL χ) (continuedCompletedHeckeL χ⁻¹)
    (continuedCompletedHeckeL_spec χ).1 (continuedCompletedHeckeL_spec χ).2
    (continuedCompletedHeckeL_spec χ⁻¹).1 (continuedCompletedHeckeL_spec χ⁻¹).2
  let r (z : ℂ) := 1 - z
  have hr : HasDerivAt r (-1) s := by simpa [r] using (hasDerivAt_id s).const_sub 1
  have e : continuedCompletedHeckeL χ⁻¹ ∘ r = fun z ↦ ε z * continuedCompletedHeckeL χ z :=
    funext he
  have ho := meromorphicOrderAt_comp_of_deriv_ne_zero (f := continuedCompletedHeckeL χ⁻¹)
    (show AnalyticAt ℂ r s by dsimp [r]; fun_prop) (hr.deriv.trans_ne (by norm_num))
  rw [e] at ho
  change meromorphicOrderAt (ε * continuedCompletedHeckeL χ) s = _ at ho
  rw [meromorphicOrderAt_mul_of_ne_zero (hε.analyticAt s) (hne s)] at ho
  exact ho.trans_le (_h (r s) (by change 1 / 2 < 1 - s.re; linarith))

end Limits

-- TODO(paper-gap): In §1.4.6, p. 30, continuity in the Bruhat test topology alone
-- cannot extend the identity from tests supported away from norm one. In the radial
-- log coordinate, first-derivative evaluation at zero annihilates every such test
-- but takes value one on x times a bump equal to one near zero. A bound in a weaker
-- topology, or control of the distributions supported at norm one, is needed.
-- Under GRH the full zero set of idelicExplicitFormula lies in every centered
-- open window of positive width, for all compactly supported Bruhat tests.
-- Section 1.4.2 fixes the profile as t^(-z) with midpoint value at t = 1.
-- For a convolution square the value at the identity is the squared L² norm.

section Boundary

local notation "outside(" χ ", " S ")" =>
  toMeromorphicNFOn (fun s ↦ reciprocalPartialHeckeEulerProduct χ S s * finiteL(χ) s) univ
local notation "outsideMass(" S ")" =>
  (∏ᶠ v : {v : V // v ∉ S},
    (((finiteLocalMultiplicativeTamagawaMeasure F v.val)
      (v.val.adicCompletionIntegers F).units).toReal : ℂ))

/-- Paper: §1.4.7, p. 30. Extension by the integer tests outside `S`
multiplies the local Mellin transform by the outside Euler product and
the product of the outside local integer-unit masses.
Section 1.1.4 (p. 12) defines the local character for χ unramified outside S.
Deviation: For the finite S in §1.4.7 retain the outside unit masses. If S contains
the different as on p. 25, their product is one. This is the meromorphic comparison in
`weilIdentity_unramifiedOutside_meromorphic`, with the normalized outside
Euler product of §6.3. The masses depend on the Haar convention. -/
theorem introTrace_transition_mellin (S : Finset V) (χ : U𝔽)
    (hχ : ideleClassNormTwist χ 0 ∈ unramifiedOutside F S)
    (f : SchwartzBruhat (Multiplicative (SAdeleRing F S))) :
    let c := sIdeleRestriction F S ⟨ideleClassNormTwist χ 0, hχ⟩
    let twist := quasiCharacterNormTwist (G := SIdeleQuotient F S) (sIdeleQuotientNorm F S)
      (isProperMap_sIdeleQuotientNorm F S).continuous c
    (fun s ↦ globalIdelicZFunction (sAdeleSchwartzToGlobal F S f) (ideleClassNormTwist χ s))
      =ᶠ[codiscrete ℂ] (fun s ↦
        outsideMass(S) * sLocalIdelicZFunction f (twist s) * heckeEulerProductOutside S χ hχ s) :=
  by
  let L := finiteL(χ)
  obtain ⟨hL, hs⟩ := (finiteHeckeL_exists_continuation χ).choose_spec
  have hraw := weilIdentity_unramifiedOutside_meromorphic (F := F) S f χ hχ L hL
    (fun z hz ↦ hs ⟨z, hz⟩)
  have hm : MeromorphicOn (fun z ↦ reciprocalPartialHeckeEulerProduct χ S z * L z) univ :=
    fun z hz ↦ ((strongCoprimalityJetMatrix_det_ne_zero_euler χ S).1 z).meromorphicAt.mul
      (hL hz).meromorphicAt
  have he : (fun z ↦ reciprocalPartialHeckeEulerProduct χ S z * L z)
      =ᶠ[codiscrete ℂ] heckeEulerProductOutside S χ hχ := by
    rw [heckeEulerProductOutside_eq_finite S χ hχ L hL hs]
    simpa only [Filter.codiscrete] using toMeromorphicNFOn_eqOn_codiscrete hm
  filter_upwards [hraw, he] with z htrans heuler
  rw [htrans, ← heuler]
  simp only [reciprocalPartialHeckeEulerProduct, mul_assoc]

-- On theta classes this is the representative formula for sLocalThetaToGlobal_mk,
-- globalThetaMellin_mk and sLocalThetaMellin_mk from §§5.1–5.2.

/-- Paper: §1.4.7, pp. 30–31. The finite Hecke L-function has no zero on
the line of real part one.
Deviation: Meromorphic order allows the pole of a pure norm character on
this line. A normal-form point value at a pole would be zero in Lean. -/
theorem introTrace_finiteL_no_zeros_one_line (χ : U𝔽) (t : ℝ) :
    meromorphicOrderAt finiteL(χ) ⟨1, t⟩ ≤ 0 := by
  obtain ⟨A, hA, h⟩ := finiteHeckeL_zeroFreeRegion
  obtain ⟨B, hB, hzero⟩ := h F χ
  have hlog : 0 ≤ Real.log (B * (|t| + 3)) := Real.log_nonneg (by
    have hBt : 0 ≤ B * |t| := mul_nonneg (by linarith) (abs_nonneg t)
    nlinarith)
  apply hzero _ (finiteHeckeL_exists_continuation χ).choose_spec.1
    (finiteHeckeL_exists_continuation χ).choose_spec.2
  change 1 - A / ((Module.finrank ℚ F : ℝ) ^ 4 * Real.log (B * (|t| + 3))) ≤ 1
  exact sub_le_self _ (div_nonneg hA.le (mul_nonneg (by positivity) hlog))

/-- Paper: §1.4.7, pp. 30–31. The outside Euler product has no zero on the
line of real part one, so its reciprocal is holomorphic there.
Deviation: Multiplying by inverse local Euler factors creates no zeros
on this line. The reciprocal at a pole is interpreted in normal form. -/
theorem introTrace_outside_inv_analytic_one_line (χ : U𝔽) (S : Finset V) (t : ℝ) :
    AnalyticAt ℂ (fun s ↦ (outside(χ, S) s)⁻¹) ⟨1, t⟩ := by
  let L := finiteL(χ)
  let z : ℂ := ⟨1, t⟩
  obtain ⟨ha, hn⟩ := strongCoprimalityJetMatrix_det_ne_zero_euler χ S
  have hm : MeromorphicOn (fun w ↦ reciprocalPartialHeckeEulerProduct χ S w * L w) univ :=
    fun w hw ↦ (ha w).meromorphicAt.mul ((finiteHeckeL_exists_continuation χ).choose_spec.1 hw).meromorphicAt
  have hnf := meromorphicNFOn_toMeromorphicNFOn (fun w ↦ reciprocalPartialHeckeEulerProduct χ S w * L w) univ
  apply (hnf (mem_univ z)).inv.meromorphicOrderAt_nonneg_iff_analyticAt.mp
  rw [meromorphicOrderAt_inv, meromorphicOrderAt_toMeromorphicNFOn hm (mem_univ z)]
  change 0 ≤ -meromorphicOrderAt (reciprocalPartialHeckeEulerProduct χ S * L) z
  rw [meromorphicOrderAt_mul_of_ne_zero (ha z) (hn z (by norm_num [z]))]
  have hle : meromorphicOrderAt L z ≤ 0 := introTrace_finiteL_no_zeros_one_line χ t
  cases he : meromorphicOrderAt L z with
  | top => simp [he] at hle
  | coe k =>
    rw [he] at hle
    have hk : k ≤ 0 := by exact_mod_cast hle
    exact_mod_cast neg_nonneg.mpr hk

/-- Paper: §1.4.7, p. 31. Multiplication by the reciprocal of the outside
Euler product undoes the transition multiplier as a meromorphic identity.
Deviation: The reciprocal includes the measure normalization. Cancellation
holds on punctured neighborhoods, including at poles on the boundary. -/
theorem introTrace_transition_mellin_inv (S : Finset V) (χ : U𝔽)
    (hχ : ideleClassNormTwist χ 0 ∈ unramifiedOutside F S)
    (f : SchwartzBruhat (Multiplicative (SAdeleRing F S))) (t : ℝ) :
    let c := sIdeleRestriction F S ⟨ideleClassNormTwist χ 0, hχ⟩
    let twist := quasiCharacterNormTwist (G := SIdeleQuotient F S) (sIdeleQuotientNorm F S)
      (isProperMap_sIdeleQuotientNorm F S).continuous c
    (fun s ↦ (outsideMass(S) * heckeEulerProductOutside S χ hχ s)⁻¹ *
      globalIdelicZFunction (sAdeleSchwartzToGlobal F S f) (ideleClassNormTwist χ s))
      =ᶠ[𝓝[≠] (⟨1, t⟩ : ℂ)] (fun s ↦ sLocalIdelicZFunction f (twist s)) := by sorry

/-- Paper: §1.4.7, p. 31. The continued product recovers the local Mellin value
on the boundary after normalization at its removable singularities.
Deviation: At a pole of the outside factor the two separate normal-form point
values give zero when multiplied. The product is normalized as a whole. -/
theorem introTrace_transition_mellin_inv_boundaryValue (S : Finset V) (χ : U𝔽)
    (hχ : ideleClassNormTwist χ 0 ∈ unramifiedOutside F S)
    (f : SchwartzBruhat (Multiplicative (SAdeleRing F S))) (t : ℝ) :
    let c := sIdeleRestriction F S ⟨ideleClassNormTwist χ 0, hχ⟩
    let twist := quasiCharacterNormTwist (G := SIdeleQuotient F S) (sIdeleQuotientNorm F S)
      (isProperMap_sIdeleQuotientNorm F S).continuous c
    toMeromorphicNFOn (fun s ↦ (outsideMass(S) * heckeEulerProductOutside S χ hχ s)⁻¹ *
      globalIdelicZFunction (sAdeleSchwartzToGlobal F S f) (ideleClassNormTwist χ s)) univ ⟨1, t⟩ =
        sLocalIdelicZFunction f (twist ⟨1, t⟩) := by sorry

-- The first and third growth inputs on p. 31 are already stated as
-- finiteHeckeL_continuation_isBigO_rpow and finiteHeckeL_inv_isBigO_oneLine.

/-- Paper: §1.4.7, p. 31. On both tails there are horizontal edges of
growing contour boxes on which the reciprocal finite L-function is regular,
nonzero, and polynomially bounded uniformly along the edge.
Deviation: The real parts range over the fixed width of the boxes in the
preceding sentence. The polynomial bounds concern large absolute heights. -/
theorem introTrace_finiteL_inv_horizontal_growth (χ : U𝔽) (a b : ℝ) (_hab : a < b) :
    ∃ (T : ℤ → ℝ) (C : ℝ) (m : ℕ), 0 < C ∧ Tendsto T atTop atTop ∧ Tendsto T atBot atBot ∧
      ∀ k : ℤ, ∀ σ ∈ Icc a b,
        meromorphicOrderAt finiteL(χ) ⟨σ, T k⟩ = 0 ∧
          ‖(finiteL(χ) ⟨σ, T k⟩)⁻¹‖ ≤ C * (1 + |T k|) ^ m := by sorry

end Boundary

-- Section 1.4.8, p. 31. The full multiplicity in the open strip and the capped
-- edge multiplicity are spectralStripMultiplicity_interior and
-- spectralStripMultiplicity_boundary. The strict test for jet k is 2*k + 1 < s,
-- by lt_spectralBoundaryMultiplicity and scalarIntervalSobolev_eval_boundary_iff.
-- TODO(paper-gap): §§1.4.8–1.4.9, p. 31. Continuity of the surviving evaluations
-- does not compare the fixed geometric distribution across widths. The missing
-- orbital comparison is recorded by traceFormula_exteriorZeros in Chapter 12.

/-- Paper: §1.4.5, p. 30. For every number field and every unitary character
of its idele class group, a zero of the continued completed Hecke L-function
in the open critical strip has real part one half. The paper gives no
numbered statement for this claim. Theorem 13.3.1.2 is a title. The deduction
below depends on the missing extension in §1.4.5.
Deviation: Positive meromorphic order expresses a zero of the continuation
and distinguishes zeros from poles. -/
theorem heckeL_zero_re_eq_half (χ : U𝔽) (s : ℂ) (_hs₀ : 0 < s.re) (_hs₁ : s.re < 1)
    (_hzero : 0 < meromorphicOrderAt (continuedCompletedHeckeL χ) s) :
    s.re = 1 / 2 := by
  classical
  let q : (AdeleRing (𝓞 F) F)ˣ →ₜ* C𝔽 := ⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩
  let τ : ℝ≥0ˣ →ₜ* C𝔽 := q.comp
    ⟨canonicalIdeleNormSection F, canonicalIdeleNormSection_continuous F⟩
  have hτ : RightInverse τ (ideleClassNorm F) := canonicalIdeleNormSection_rightInverse F
  have hr (ψ : U𝔽) (w : ℂ) (hw : 1 / 2 < w.re) :
      meromorphicOrderAt (continuedCompletedHeckeL ψ) w ≤ 0 := by
    refine introTrace_completedL_no_right_zeros τ hτ ?_ ψ w hw
    intro η hη
    refine introTrace_finiteL_no_right_zeros η (introTrace_logDeriv_analytic_of_extensions η ?_)
    intro a ha
    obtain ⟨h, ρ, H, hA, hH, hlim⟩ := introTrace_combined_limit_extension τ hτ η hη a ha
    exact ⟨H, hH, introTrace_logDeriv_extension_of_limit τ hτ η hη a ha h ρ hA H hH hlim⟩
  apply le_antisymm
  · exact le_of_not_gt fun h ↦ _hzero.not_ge (hr χ s h)
  · exact le_of_not_gt fun h ↦ _hzero.not_ge
      (introTrace_completedL_no_left_zeros χ (hr χ⁻¹) s h)

end RiemannMasullo
