module

import Mathlib.Topology.Algebra.IsOpenUnits
public import RiemannMasullo.Research.StripNuclearity.RationalDiagonalDefect
import RiemannMasullo.Research.StripNuclearity.ScalarKernel
import RiemannMasullo.ForMathlib.Analysis.Normed.Field.ProperSpace

/-! # The actual rational place terms below the first prime

For a smooth profile with log support between zero and log two, every finite
local pullback vanishes. At the real place the positive and negative
multiplicative branches give the classical real term in the contour formula.
This direct coordinate comparison evaluates the global geometric diagonal.
-/

@[expose] public noncomputable section
open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped ContDiff NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo.StripNuclearity

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

set_option quotPrecheck false
local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "N(" x ")" => (((ideleClassNorm ℚ) (x : Cℚ)).val : ℝ)
local notation "wℝ" => Rat.infinitePlace
local notation "Kℝ" => Rat.infinitePlace.Completion
local notation "μℝ" => infiniteLocalMultiplicativeTamagawaMeasure ℚ Rat.infinitePlace
local notation "xℝ" => InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace

/-- Real-coordinate expression for the multiplicative Tamagawa integral at the
real place of the rationals. -/
private theorem rational_real_mul_integral (f : ℝ → ℂ) :
    (∫ u : Kℝˣ, f (xℝ u.val) ∂μℝ) = ∫ t : ℝ, (|t|⁻¹ : ℝ) • f t := by
  let w := Rat.infinitePlace
  have hw : w.IsReal := Rat.isReal_infinitePlace
  let : MeasurableSpace w.Completion := instMeasurableSpaceCompletion_riemannMasullo ℚ w
  let : BorelSpace w.Completion := ⟨rfl⟩
  let : BorelSpace w.Completionˣ := borelSpace_units_of_continuousInv₀ _
  let e := (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).toHomeomorph.toMeasurableEquiv
  have hv := (IsOpenUnits.isOpenEmbedding_unitsVal (M := w.Completion)).measurableEmbedding
  let d (y : w.Completion) : ENNReal := (↑(‖y‖₊ ^ w.mult) : ENNReal)⁻¹
  have hd : Measurable d := (measurable_coe_nnreal_ennreal.comp (measurable_nnNorm.pow_const _)).inv
  change (∫ u : w.Completionˣ, f (e u.val) ∂((infiniteLocalAdditiveTamagawaMeasure ℚ w).withDensity d).comap Units.val) = _
  rw [← hv.integral_map (g := fun y ↦ f (e y)), hv.map_comap,
    setIntegral_withDensity_eq_setIntegral_toReal_smul hd ?_ _ hv.measurableSet_range,
    infiniteLocalAdditiveTamagawaMeasure, dite_eq_left hw]
  · change (∫ y in range Units.val, _ ∂volume.map e.symm) = _
    rw [e.symm.restrict_map, e.symm.measurableEmbedding.integral_map]
    have he0 : e.symm 0 = 0 := map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm
    have hr : e.symm ⁻¹' range (Units.val : w.Completionˣ → w.Completion) = {0}ᶜ := by
      ext t
      simp only [mem_preimage, mem_range, mem_compl_iff, mem_singleton_iff]
      constructor
      · rintro ⟨u, hu⟩ rfl
        exact u.ne_zero (hu.trans he0)
      · intro ht
        exact ⟨Units.mk0 (e.symm t) fun hy ↦ ht (e.symm.injective (hy.trans he0.symm)), rfl⟩
    rw [hr, restrict_compl_singleton]
    apply integral_congr_ae (.of_forall fun t ↦ ?_)
    have hn := (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.isometry.norm_map_of_map_zero
      (map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm) t
    simp only [d, hw.mult_eq_one, pow_one, ENNReal.toReal_inv, ENNReal.coe_toReal, coe_nnNorm,
      e.apply_symm_apply]
    exact congrArg (fun t : ℝ ↦ t⁻¹ • f _) (hn.trans (Real.norm_eq_abs _))
  · refine ae_restrict_of_forall_mem hv.measurableSet_range fun y ⟨u, hu⟩ ↦ ?_
    simp only [d, hw.mult_eq_one, pow_one]
    exact ENNReal.inv_lt_top.mpr (by simp [← hu])

private theorem sqrt_profile (v : ℝ) (hv : 0 < v) :
    Complex.exp ((Real.log v : ℂ) / 2) = (Real.sqrt v : ℂ) := by
  rw [show ((Real.log v : ℂ) / 2) = ((Real.log v / 2 : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_exp, Real.exp_half, Real.exp_log hv]

private theorem rational_real_PV_coordinates (g : ℝ → ℂ) (g₀ : g 0 = 0)
    (φ : BruhatCompactSupport Kℝˣ)
    (hφ : ∀ u, φ.val u = Complex.exp ((Real.log ‖u.val‖ : ℂ) / 2) * g (Real.log ‖u.val‖)) :
    infiniteConnesWeilPrincipalValue wℝ φ =
      (1 / 2 : ℂ) * ∫ y : ℝ, g (Real.log |y|) / (|1 - y| : ℝ) := by
  have h₁ : φ.val 1 = 0 := by simp [hφ, g₀]
  rw [realConnesWeilPrincipalValue_of_apply_one_zero wℝ Rat.isReal_infinitePlace φ h₁]
  congr 1
  let F (t : ℝ) := ((|t| : ℝ) : ℂ) * g (Real.log |t|) / (|1 - t| : ℝ)
  have hnorm (y : Kℝ) : |xℝ y| = ‖y‖ := (Real.norm_eq_abs _).symm.trans
    ((InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace).isometry.norm_map_of_map_zero
      (map_zero xℝ) y)
  have hker (u : Kℝˣ) : φ.val u * (Real.sqrt ‖u.val‖ : ℂ) / (‖1 - u.val‖ : ℂ) = F (xℝ u.val) := by
    have hden : |1 - xℝ u.val| = ‖1 - u.val‖ := by simpa only [map_sub, map_one] using hnorm (1 - u.val)
    rw [hφ, sqrt_profile _ (norm_pos_iff.mpr u.ne_zero)]
    simp only [F, hnorm, hden]
    congr 1
    have hsq : (Real.sqrt ‖u.val‖ : ℂ) * (Real.sqrt ‖u.val‖ : ℂ) = (‖u.val‖ : ℂ) := by
      exact_mod_cast Real.mul_self_sqrt (norm_nonneg u.val)
    rw [← hsq]
    ring
  rw [integral_congr_ae (.of_forall hker), rational_real_mul_integral]
  apply integral_congr_ae (.of_forall fun t ↦ ?_)
  by_cases h : t = 0
  · simp [F,h,g₀]
  · have ht : ((|t| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (abs_ne_zero.mpr h)
    simp [Complex.real_smul, F, ht, mul_div_assoc]

/-- A compact smooth log-norm profile gives a compact Bruhat test on the units
of any proper normed field. -/
theorem exists_normedField_logNorm_test {K : Type*} [NormedField K] [ProperSpace K]
    (G : ℝ → ℂ) (hg : ContDiff ℝ (∞) G) (hc : HasCompactSupport G) :
    ∃ u : BruhatCompactSupport Kˣ, ∀ x, u.val x = G (Real.log ‖x.val‖) := by
  let n := (Units.map nnNormHom.toMonoidHom : Kˣ →* ℝ≥0ˣ)
  have hn : IsProperMap n := by simpa only [pow_one] using isProperMap_units_nnNorm_pow (K := K) 1 one_ne_zero
  let L := (radialExponential.symm : ℝ≥0ˣ →ₜ* Multiplicative ℝ).comp ⟨n,hn.continuous⟩
  have hL : IsProperMap L := radialExponential.symm.toHomeomorph.isProperMap.comp hn
  obtain ⟨u,hu⟩ := exists_bruhatCompactSupport_of_proper_realHom L hL G hg hc
  refine ⟨u,fun x ↦ (hu x).trans (congrArg G ?_)⟩
  change (radialExponential.symm (n x)).toAdd = Real.log ((n x).val : ℝ)
  obtain ⟨t,ht⟩ := radialExponential.surjective (n x)
  rw [← ht,ContinuousMulEquiv.symm_apply_apply]
  exact (Real.log_exp t.toAdd).symm

/-- A norm radial test has an actual compact Bruhat restriction to the real place. -/
theorem exists_rational_archimedean_norm_test (G : ℝ → ℂ) (hg : ContDiff ℝ (∞) G)
    (hc : HasCompactSupport G) : ∃ u : BruhatCompactSupport Kℝˣ, ∀ x, u.val x = G (Real.log ‖x.val‖) := by
  let e := (InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace).symm
  let : ProperSpace Kℝ := e.isometry.antilipschitzWith.properSpace e.continuous e.surjective
  exact exists_normedField_logNorm_test G hg hc

/-- A uniformizer has norm equal to the reciprocal of an integer at least two,
so there is no nonarchimedean unit whose norm is strictly between one and two. -/
theorem finite_place_norm_notMem_one_two {F : Type*} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (u : (v.adicCompletion F)ˣ) : ‖u.val‖ ∉ Ioo (1 : ℝ) 2 := by
  let k : ℤ := WithZero.log (Valued.v u.val)
  let q : ℝ := v.asIdeal.absNorm
  have hn : 2 ≤ v.asIdeal.absNorm := NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hq : 2 ≤ q := by
    change (2 : ℝ) ≤ (v.asIdeal.absNorm : ℝ)
    exact_mod_cast hn
  have h : ‖u.val‖ = q ^ k := by
    rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ (Valued.v.ne_zero_iff.mpr u.ne_zero)]
    simp [k,q]
  rw [h]
  intro ⟨hl,hr⟩
  by_cases hk : k ≤ 0
  · exact hl.not_ge (zpow_le_one_of_nonpos₀ (by linarith) hk)
  · have hk' : (1 : ℤ) ≤ k := by omega
    have hpow := zpow_le_zpow_right₀ (a:=q) (by linarith : 1 ≤ q) hk'
    rw [zpow_one] at hpow
    exact hr.not_ge (hq.trans hpow)

/-- On a log-norm window strictly inside (0,log 2), every finite-place
restriction is the zero compact Bruhat test. -/
theorem rational_finite_prime_free_restriction {g : ℝ → ℂ} {a b : ℝ} (ha : 0 < a) (hb : b < Real.log 2)
    (hs : tsupport g ⊆ Icc a b) (φ : BruhatCompactSupport Cℚ)
    (hφ : ∀ x, φ.val x = Complex.exp ((Real.log N(x) : ℂ) / 2) * g (Real.log N(x)))
    (v : HeightOneSpectrum (𝓞 ℚ)) (u : (v.adicCompletion ℚ)ˣ) :
    φ.val (IdeleClassGroup.ofAdicCompletion (𝓞 ℚ) ℚ v u) = 0 := by
  rw [hφ,ideleClassNorm_ofAdicCompletion]
  change Complex.exp _ * g (Real.log ‖u.val‖) = 0
  apply mul_eq_zero_of_right
  apply image_eq_zero_of_notMem_tsupport
  intro ht
  have hn : 0 < ‖u.val‖ := norm_pos_iff.mpr u.ne_zero
  exact finite_place_norm_notMem_one_two v u
    ⟨(Real.log_pos_iff hn.le).mp (ha.trans_le (hs ht).1),
    (Real.log_lt_log_iff hn (by norm_num : (0 : ℝ) < 2)).mp ((hs ht).2.trans_lt hb)⟩


section RealLogCoordinate

open Real

private theorem log_kernel_integrable (g : ℝ → ℂ) (hg : Continuous g) {a b : ℝ} (ha : 0 < a)
    (hs : tsupport g ⊆ Icc a b) :
    Integrable (fun y : ℝ ↦ g (log |y|) / (|1 - y| : ℝ)) := by
  have hx0 : g 0 = 0 := image_eq_zero_of_notMem_tsupport (fun ht ↦ (not_le.mpr ha) (hs ht).1)
  have hvan (y : ℝ) (hy : |y| < exp a) : g (log |y|) = 0 := by
    by_cases h : y = 0
    · simpa [h] using hx0
    · apply image_eq_zero_of_notMem_tsupport
      exact fun ht ↦ (not_le.mpr ((log_lt_iff_lt_exp (abs_pos.mpr h)).mpr hy)) (hs ht).1
  let f (y : ℝ) := g (log |y|) / (|1 - y| : ℝ)
  have hf : Continuous f := continuous_iff_continuousAt.mpr fun y ↦ by
    by_cases h : |y| < exp a
    · apply (continuousAt_const (y := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds h] with z hz
      simp only [f, hvan z hz, zero_div]
    · have h0 : y ≠ 0 := fun he ↦ h (by simp [he, exp_pos])
      have h1 : 1 - y ≠ 0 := fun he ↦ h (by rw [← sub_eq_zero.mp he, abs_one]; exact one_lt_exp_iff.mpr ha)
      exact (hg.continuousAt.comp (continuous_abs.continuousAt.log (abs_ne_zero.mpr h0))).div
        (Complex.continuous_ofReal.continuousAt.comp (continuous_abs.continuousAt.comp
          (continuous_const.sub continuous_id).continuousAt)) (by exact_mod_cast abs_ne_zero.mpr h1)
  have hc : HasCompactSupport f := HasCompactSupport.intro (isCompact_Icc (a := -(exp b)) (b := exp b))
    fun y hy ↦ by
      have h : exp b < |y| := not_le.mp (fun h ↦ hy (abs_le.mp h))
      have h' : |y| > 0 := (exp_pos b).trans h
      have hnot : log |y| ∉ tsupport g := fun ht ↦ (not_le.mpr ((lt_log_iff_exp_lt h').mpr h)) (hs ht).2
      simp only [f,image_eq_zero_of_notMem_tsupport hnot,zero_div]
  exact hf.integrable_of_hasCompactSupport hc

private theorem real_log_kernel (g : ℝ → ℂ) (hg : Continuous g) {a b : ℝ} (ha : 0 < a)
    (hs : tsupport g ⊆ Icc a b) :
    (1 / 2 : ℂ) * (∫ y : ℝ, g (log |y|) / (|1 - y| : ℝ)) =
      ∫ x in Ioi (0 : ℝ), g x / (1 - Complex.exp (-2 * (x : ℂ))) := by
  let f (y : ℝ) := g (log |y|) / (|1 - y| : ℝ)
  have hi : Integrable f := log_kernel_integrable g hg ha hs
  have hi' : Integrable (fun y ↦ f (-y)) := hi.comp_neg
  have heq : (∫ t, f t) = ∫ t in Ioi (0 : ℝ), f t + f (-t) := by
    rw [integral_add hi.integrableOn hi'.integrableOn, integral_comp_neg_Ioi, neg_zero]
    simpa only [compl_Ioi] using (integral_add_compl (s := Ioi (0 : ℝ)) measurableSet_Ioi hi).symm
  change (1 / 2 : ℂ)*(∫y,f y) = _
  rw [heq, ← integral_comp_exp, ← integral_const_mul]
  have vanish {x : ℝ} (hx : x ≤ 0) : g x = 0 :=
    image_eq_zero_of_notMem_tsupport fun hx' ↦ (not_le.mpr (hx.trans_lt ha)) (hs hx').1
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi (0 : ℝ))
    (f := fun x : ℝ ↦ (1 / 2 : ℂ) * (exp x • (f (exp x) + f (-(exp x))))) (fun x hx ↦ by
      have h : x ≤ 0 := not_lt.mp hx
      simp [f, log_exp, vanish h])]
  apply setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
  have hxpos : 0 < x := hx
  have h1 : 1 < exp x := one_lt_exp_iff.mpr hxpos
  simp only [f, abs_of_pos (exp_pos _), abs_neg, log_exp, sub_neg_eq_add,
    abs_of_neg (sub_neg.mpr h1), abs_of_pos (show 0 < 1 + exp x by positivity), neg_sub,
    Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_add]
  have e₂ : Complex.exp (-2 * (x : ℂ)) = ((exp x : ℝ) : ℂ)⁻¹^2 := by
    rw [show -2 * (x : ℂ) = -(x : ℂ) + -x by ring,Complex.exp_add, Complex.exp_neg, ← Complex.ofReal_exp]
    ring
  rw [e₂]
  have hn : ((exp x : ℝ):ℂ) ≠ 0 := by exact_mod_cast (exp_pos x).ne'
  have hm : ((exp x : ℝ):ℂ)-1 ≠ 0 := by exact_mod_cast (sub_ne_zero.mpr h1.ne')
  have hp : 1+((exp x : ℝ):ℂ) ≠ 0 := by exact_mod_cast (show (0 : ℝ)<1 + exp x by positivity).ne'
  have hpow : ((exp x : ℝ):ℂ)^2-1 ≠ 0 := by
    rw [show ((exp x : ℝ):ℂ)^2-1 = (((exp x : ℝ):ℂ)-1)*(1+(exp x : ℝ)) by ring]
    exact mul_ne_zero hm hp
  field_simp
  ring

end RealLogCoordinate

/-- The real-place principal value of a positive-log rational radial profile
is the classical real gamma integral. No upper bound on its norm is needed. -/
theorem rational_real_principalValue_positive_log_profile (g : ℝ → ℂ) (hg : Continuous g)
    {a b : ℝ} (ha : 0 < a) (hs : tsupport g ⊆ Icc a b)
    (φ : BruhatCompactSupport Kℝˣ)
    (hφ : ∀ u, φ.val u = rationalCenteredLogProfile g (Real.log ‖u.val‖)) :
    infiniteConnesWeilPrincipalValue wℝ φ =
      ∫ x in Ioi (0 : ℝ), g x / (1 - Complex.exp (-2 * (x : ℂ))) :=
  (rational_real_PV_coordinates g
    (image_eq_zero_of_notMem_tsupport fun ht ↦ (not_le.mpr ha) (hs ht).1) φ hφ).trans
    (real_log_kernel g hg ha hs)

private theorem rational_prime_free_value (g : ℝ → ℂ) {a b : ℝ} (ha : 0 < a)
    (hb : b < Real.log 2) (hs : tsupport g ⊆ Icc a b) :
    rationalWeilLocalValue g = ∫ x in Ioi (0 : ℝ), g x / (1-Complex.exp (-2 * (x : ℂ))) := by
  have hn {x : ℝ} (hx : x ≤ 0) : g x = 0 :=
    image_eq_zero_of_notMem_tsupport fun ht ↦ (not_le.mpr (hx.trans_lt ha)) (hs ht).1
  unfold rationalWeilLocalValue
  have hp (n : ℕ) : (ArithmeticFunction.vonMangoldt n : ℂ) *
      (g (Real.log n) + g (-Real.log n) / (n : ℂ)) = 0 := by
    by_cases h : n < 2
    · interval_cases n <;> simp [hn (le_refl _)]
    · have h2 : (2:ℝ) ≤ n := by exact_mod_cast (le_of_not_gt h)
      have hlog : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) h2
      have h₁ : g (Real.log n) = 0 :=
        image_eq_zero_of_notMem_tsupport fun ht ↦ (not_le.mpr (hb.trans_le hlog)) (hs ht).2
      have h₂ : 0 ≤ Real.log n := (Real.log_pos (by norm_num : (1 : ℝ)<2)).le.trans hlog
      simp only [h₁, hn (neg_nonpos.mpr h₂), zero_div, add_zero, mul_zero]
  rw [(tsum_congr hp).trans tsum_zero,zero_add]
  apply setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
  simp only [hn (neg_nonpos.mpr (le_of_lt hx)), mul_zero, add_zero]

local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation "U∞" => ((w : InfinitePlace ℚ) → BruhatCompactSupport w.Completionˣ)
local instance ratFiniteUnitsLocallyCompact (v : V) : LocallyCompactSpace (v.adicCompletion ℚ)ˣ :=
  letI : ProperSpace (v.adicCompletion ℚ) := properSpace_adicCompletion v
  inferInstance
local notation "U𝔭" => ((v : V) → BruhatCompactSupport (v.adicCompletion ℚ)ˣ)
local notation "infClass(" w ")" => IdeleClassGroup.ofCompletion (𝓞 ℚ) ℚ w
local notation "finClass(" v ")" => IdeleClassGroup.ofAdicCompletion (𝓞 ℚ) ℚ v
local notation "finTerm(" v ", " B ")" =>
  ((Real.log ((v : V).asIdeal.absNorm : ℝ) / ((finiteLocalMultiplicativeTamagawaMeasure ℚ v)
    ((HeightOneSpectrum.adicCompletionIntegers ℚ v).units : Set _)).toReal : ℝ) : ℂ) *
    finiteConnesWeilPrincipalValue v 1 B
local notation "radial(" φ ", " g ")" =>
  (∀ x : Cℚ, (φ : BruhatCompactSupport Cℚ).val x = rationalCenteredLogProfile g (Real.log N(x)))
local notation "archRep(" A ", " φ ")" =>
  (∀ (w : InfinitePlace ℚ) (u : w.Completionˣ), ((A : U∞) w).val u = (φ : BruhatCompactSupport Cℚ).val (infClass(w) u))
local notation "finRep(" B ", " φ ")" =>
  (∀ (v : V) (u : (v.adicCompletion ℚ)ˣ), ((B : U𝔭) v).val u = (φ : BruhatCompactSupport Cℚ).val (finClass(v) u))
local notation "places(" A ", " B ")" =>
  ((∑ w : InfinitePlace ℚ, infiniteConnesWeilPrincipalValue w ((A : U∞) w)) + ∑' v : V, finTerm(v,(B : U𝔭) v))

/-- At rational norm strictly between one and two, a smooth radial test has
compact Bruhat restrictions at all places. The finite restrictions are zero. -/
theorem exists_rational_prime_free_place_tests (g : ℝ → ℂ) (hg : ContDiff ℝ (∞) g)
    (hc : HasCompactSupport g) {a b : ℝ} (ha : 0 < a) (hb : b < Real.log 2)
    (hs : tsupport g ⊆ Icc a b) (φ : BruhatCompactSupport Cℚ) (hφ : radial(φ, g)) :
    ∃ (A : U∞) (B : U𝔭), archRep(A, φ) ∧ finRep(B, φ) := by
  obtain ⟨u, hu⟩ := exists_rational_archimedean_norm_test (rationalCenteredLogProfile g)
    ((Complex.contDiff_exp.comp ((Complex.ofRealCLM.contDiff).div_const 2)).mul hg) hc.mul_left
  have hr (w : InfinitePlace ℚ) : ∃ u : BruhatCompactSupport w.Completionˣ, ∀ x, u.val x = φ.val (infClass(w) x) := by
    obtain rfl := Subsingleton.elim w wℝ
    refine ⟨u, fun x ↦ ?_⟩
    rw [hu, hφ, ideleClassNorm_ofCompletion, Rat.isReal_infinitePlace.mult_eq_one, pow_one]
    rfl
  choose A hA using hr
  exact ⟨A, (fun _ ↦ 0), hA, fun v x ↦ (rational_finite_prime_free_restriction ha hb hs φ hφ v x).symm⟩

/-- Paper: Equations (12.5.1.2)–(12.5.1.3), pp. 519–520. For a rational
radial test with norm in a compact subinterval of (1,2), the real principal
value is exactly the classical gamma contribution and the finite-place
principal-value series vanishes at every place. -/
theorem rationalWeilLocalValue_eq_principalValues (g : ℝ → ℂ) (hg : Continuous g)
    {a b : ℝ} (ha : 0 < a) (hb : b < Real.log 2) (hs : tsupport g ⊆ Icc a b)
    (φ : BruhatCompactSupport Cℚ) (hφ : radial(φ, g)) (A : U∞) (B : U𝔭)
    (hA : archRep(A, φ)) (hB : finRep(B, φ)) : rationalWeilLocalValue g = places(A, B) := by
  have h₀ : g 0 = 0 := image_eq_zero_of_notMem_tsupport fun ht ↦ (not_le.mpr ha) (hs ht).1
  have hzero (v : V) : B v = 0 := by
    apply Subtype.ext
    exact funext fun u ↦ (hB v u).trans (rational_finite_prime_free_restriction ha hb hs φ hφ v u)
  have hp (v : V) : finTerm(v,B v) = 0 := by rw [hzero,map_zero,mul_zero]
  rw [(tsum_congr hp).trans tsum_zero, add_zero, Fintype.sum_subsingleton _ wℝ,
    rational_prime_free_value g ha hb hs,
    rational_real_PV_coordinates g h₀ (A wℝ) (fun u ↦ ?_), real_log_kernel g hg ha hs]
  rw [hA, hφ, ideleClassNorm_ofCompletion, Rat.isReal_infinitePlace.mult_eq_one, pow_one]
  rfl

local notation "Vℚ" => (((normOneIdeleClassTamagawaMeasure ℚ) univ).toReal : ℂ)
local notation "μℚ" => ideleClassTamagawaMeasure ℚ
local notation "mℚ" => (⟨ideleClassNorm ℚ, (isProperMap_ideleClassNorm ℚ).continuous⟩ : Cℚ →ₜ* ℝ≥0ˣ)
local notation "pole(" φ ", " b ")" =>
  modulatedFourierMellin mℚ univ
    (⟨isProperMap_ideleClassNorm ℚ, ideleClassNorm_ne_one (F := ℚ)⟩ : IsModulation mℚ)
    μℚ (φ : BruhatCompactSupport Cℚ).val (ideleClassNormTwist (F := ℚ) 1 b)

open RiemannMasullo.External.Grh in
/-- On the prime-free window the numerical pole corrections are the two
global Mellin moments of the original test under Tamagawa Haar measure. -/
theorem rational_prime_free_places_sub_global_poles (g : ℝ → ℂ) (hg : Continuous g)
    {a b : ℝ} (ha : 0 < a) (hb : b < Real.log 2) (hs : tsupport g ⊆ Icc a b)
    (φ : BruhatCompactSupport Cℚ) (hφ : radial(φ, g)) (A : U∞) (B : U𝔭)
    (hA : archRep(A, φ)) (hB : finRep(B, φ)) :
    Vℚ * (rationalWeilLocalValue g - compactLogMellin g 0 - compactLogMellin g 1) =
      Vℚ * places(A, B) - pole(φ, -(1/2)) - pole(φ, 1/2) := by
  have hm : pole(φ,-(1/2)) = Vℚ * compactLogMellin g 0 := by
    simpa only [zero_sub] using rationalCenteredNormTest_mellin g φ hφ 0
  have hp : pole(φ,1/2) = Vℚ * compactLogMellin g 1 := by
    simpa only [show (1 : ℂ) - 1/2 = 1/2 by norm_num] using rationalCenteredNormTest_mellin g φ hφ 1
  rw [rationalWeilLocalValue_eq_principalValues g hg ha hb hs φ hφ A B hA hB, hm, hp]
  ring

local notation "compareActual(" g ", " hg ", " hc ", " ha ", " hb ", " hsupp ", " φ ", " hφ ", " A ", " B ", " hA ", " hB ", " hw ", " hs ", " U ", " hU ", " hm ")" =>
  (integral_rational_wide_diagonal_eq_weilLocal_sub_poles g hg hc
    (image_eq_zero_of_notMem_tsupport fun ht ↦ (not_le.mpr ha) ((hsupp) ht).1)
    φ hφ hw hs U hU hm).2.trans
    (rational_prime_free_places_sub_global_poles g (hg).continuous ha hb hsupp φ hφ A B hA hB)

/-- Paper: Equations (12.5.1.2)–(12.5.1.4), pp. 519–520. For rational
radial tests of norm in a compact subinterval of (1,2), the actual smoothened
wide geometric diagonal is the Tamagawa norm-one volume times the sum of the
normalized local principal values, minus the two global polar Mellin moments.
The half-width may be exactly one half and the Sobolev order at least three.
Deviation: The calculation uses the independent classical zeta contour formula.
It requires no passage from an S-local cutoff trace. -/
theorem integral_rational_prime_free_diagonal_eq_principalValues_sub_poles
    (g : ℝ → ℂ) (hg : ContDiff ℝ (∞) g) (hc : HasCompactSupport g)
    {a b : ℝ} (ha : 0 < a) (hb : b < Real.log 2) (hsupp : tsupport g ⊆ Icc a b)
    (φ : BruhatCompactSupport Cℚ) (hφ : radial(φ, g)) (A : U∞) (B : U𝔭)
    (hA : archRep(A, φ)) (hB : finRep(B, φ))
    {α s : ℝ} (hw : 1/2 ≤ α) (hs : 3 ≤ s) (U : ℕ → Set Cℚ)
    (hU : IsDPrimeSequence μℚ U) (hm : ∀ n, MeasurableSet (U n)) :
    type_of% compareActual(g, hg, hc, ha, hb, hsupp, φ, hφ, A, B, hA, hB, hw, hs, U, hU, hm) :=
  compareActual(g, hg, hc, ha, hb, hsupp, φ, hφ, A, B, hA, hB, hw, hs, U, hU, hm)

end RiemannMasullo.StripNuclearity
