module

public import RiemannMasullo.Research.StripNuclearity.RationalFiniteShells
public import RiemannMasullo.Research.TraceComparison.GeometricWidthLimit
import RiemannMasullo.Research.StripNuclearity.RationalBoundedWindow
import Mathlib.Data.Nat.Prime.Infinite

/-! # Rational place values for translates in log norm

The physical idèle-class test has profile `G (log N x - y)`. The shift by
one half in the Mellin convention is included throughout. We test the
dependence of the finite-place set in §12.5 on the support of this test.
-/

@[expose] public noncomputable section
set_option quotPrecheck false
open Classical Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped ContDiff NNReal NumberField.AdeleRing Topology
namespace RiemannMasullo.StripNuclearity

local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation "q(" v ")" => ((v : V).asIdeal.absNorm : ℝ)
local notation "K(" v ")" => ((v : V).adicCompletion ℚ)
local instance translatedLocalCompact (v : V) : LocallyCompactSpace K(v)ˣ :=
  letI : ProperSpace K(v) := properSpace_adicCompletion v
  inferInstance
local instance translatedMeasurable (v : V) : MeasurableSpace K(v)ˣ := borel _
local instance translatedBorel (v : V) : BorelSpace K(v)ˣ := ⟨rfl⟩
attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "N(" x ")" => (((ideleClassNorm ℚ) (x : Cℚ)).val : ℝ)
local notation "finTerm(" v ", " B ")" =>
  ((Real.log q(v) / ((finiteLocalMultiplicativeTamagawaMeasure ℚ v)
    ((HeightOneSpectrum.adicCompletionIntegers ℚ v).units : Set _)).toReal : ℝ) : ℂ) *
    finiteConnesWeilPrincipalValue v 1 B

/-- The unshifted Mellin profile representing the physical translate by `y` in log norm. -/
def rationalTranslatedMellinProfile (G : ℝ → ℂ) (y t : ℝ) : ℂ :=
  (Real.exp (-t / 2) : ℂ) * G (t - y)

theorem rationalCenteredLogProfile_translated (G : ℝ → ℂ) (y t : ℝ) :
    rationalCenteredLogProfile (rationalTranslatedMellinProfile G y) t = G (t - y) := by
  rw [rationalCenteredLogProfile, rationalTranslatedMellinProfile,
    show (t : ℂ) / 2 = ((t / 2 : ℝ) : ℂ) by push_cast; rfl, ← Complex.ofReal_exp,
    ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  rw [show t / 2 + -t / 2 = 0 by ring, Real.exp_zero, Complex.ofReal_one, one_mul]

private theorem translated_support {G : ℝ → ℂ} {R : ℝ} (hR : tsupport G ⊆ Icc (-R) R)
    (y : ℝ) : tsupport (rationalTranslatedMellinProfile G y) ⊆ Icc (y - R) (y + R) := by
  refine closure_minimal (fun t ht ↦ ?_) isClosed_Icc
  have h : G (t-y) ≠ 0 := fun hz ↦ ht (by simp [rationalTranslatedMellinProfile, hz])
  obtain ⟨hl,hr⟩ := hR (subset_tsupport G h)
  constructor <;> linarith

private theorem translated_vanishes {G : ℝ → ℂ} {R y t : ℝ} (hR : tsupport G ⊆ Icc (-R) R)
    (hy : R < y) (ht : t ≤ 0) : rationalTranslatedMellinProfile G y t = 0 :=
  image_eq_zero_of_notMem_tsupport fun h ↦ by
    have := (translated_support hR y h).1
    linarith

private theorem translated_smooth {G : ℝ → ℂ} (hg : ContDiff ℝ (∞) G) (y : ℝ) :
    ContDiff ℝ (∞) (rationalTranslatedMellinProfile G y) :=
  (Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp (contDiff_id.neg.div_const 2))).mul
    (hg.comp (contDiff_id.sub contDiff_const))

/-- For every physical translation there are actual compact Bruhat representatives
on the idèle classes and at every place, all with their literal pullback values. -/
theorem exists_rational_translated_place_tests (G : ℝ → ℂ) (hG : ContDiff ℝ (∞) G)
    {R : ℝ} (hR : tsupport G ⊆ Icc (-R) R) (y : ℝ) :
    ∃ (φ : BruhatCompactSupport Cℚ) (A : BruhatCompactSupport Rat.infinitePlace.Completionˣ)
      (B : (v : V) → BruhatCompactSupport K(v)ˣ),
      (∀ x : Cℚ, φ.val x = G (Real.log N(x)-y)) ∧
      (∀ u, A.val u = φ.val (IdeleClassGroup.ofCompletion (𝓞 ℚ) ℚ Rat.infinitePlace u)) ∧
      (∀ v u, (B v).val u = φ.val (IdeleClassGroup.ofAdicCompletion (𝓞 ℚ) ℚ v u)) := by
  let g := rationalTranslatedMellinProfile G y
  have hc : HasCompactSupport g := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (translated_support hR _)
  obtain ⟨φ,hφ⟩ := exists_rationalCenteredNormTest g (translated_smooth hG y) hc
  obtain ⟨A,B,hA,hB⟩ := exists_rational_radial_place_tests g (translated_smooth hG y) hc φ hφ
  exact ⟨φ,A Rat.infinitePlace,B,fun x ↦ (hφ x).trans (rationalCenteredLogProfile_translated G _ _),hA _,hB⟩

private theorem exp_neg_half_log {q : ℝ} (hq : 0 < q) :
    Real.exp (-Real.log q / 2) = (Real.sqrt q)⁻¹ := by
  rw [neg_div, Real.exp_neg, Real.exp_half, Real.exp_log hq]

/-- Paper: p. 520. On the translate centered at the residue norm of a prime,
only its first shell contributes if the center exceeds the support radius.
The normalized coefficient for the physical test is positive log(q)/√q. -/
theorem rational_translated_prime_principalValue (v : V) (G : ℝ → ℂ) {R : ℝ}
    (hR : tsupport G ⊆ Icc (-R) R) (hqR : R < Real.log q(v))
    (B : BruhatCompactSupport K(v)ˣ)
    (hB : ∀ u, B.val u = G (Real.log ‖u.val‖ - Real.log q(v))) :
    finTerm(v, B) = ((Real.log q(v) / Real.sqrt q(v) : ℝ) : ℂ) * G 0 := by
  let L := Real.log q(v)
  have hq : 1 < q(v) := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hL : 0 < L := Real.log_pos hq
  have H := hasSum_finite_principalValue_positive_radial v (rationalTranslatedMellinProfile G L)
    (fun _ ht ↦ translated_vanishes hR hqR ht) B
    (fun u ↦ (hB u).trans (rationalCenteredLogProfile_translated G L _).symm)
  rw [← H.tsum_eq, tsum_eq_single 0]
  · simp only [Nat.zero_add, pow_one, rationalTranslatedMellinProfile, L, sub_self]
    rw [exp_neg_half_log (zero_lt_one.trans hq), Complex.ofReal_div, Complex.ofReal_inv, div_eq_mul_inv, mul_assoc]
  · intro k hk
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
    have hz : G (Real.log (q(v)^(k+1)) - L) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hm
      have hu := (hR hm).2
      rw [Real.log_pow, Nat.cast_add, Nat.cast_one] at hu
      change ((k : ℝ) + 1) * L - L ≤ R at hu
      have := mul_le_mul_of_nonneg_right hk' hL.le
      change R < L at hqR
      nlinarith
    simp only [rationalTranslatedMellinProfile,hz,mul_zero]

/-- Paper: p. 520. After any prescribed height there is a translate of a fixed
smooth pulse and a prime outside a prescribed finite set where the normalized
principal value is nonzero. The printed support inequalities fail for this
same idèle-class test and finite set. -/
theorem exists_rational_translated_prime_outside (G : ℝ → ℂ) (hG : ContDiff ℝ (∞) G)
    {R : ℝ} (hR : tsupport G ⊆ Icc (-R) R) (h₀ : G 0 ≠ 0) (S : Finset V) (Y : ℝ) :
    ∃ (v : V) (φ : BruhatCompactSupport Cℚ) (B : BruhatCompactSupport K(v)ˣ),
      v ∉ S ∧ Y < Real.log q(v) ∧
      (∀ x : Cℚ, φ.val x = G (Real.log N(x) - Real.log q(v))) ∧
      (∀ u : K(v)ˣ, B.val u = φ.val (IdeleClassGroup.ofAdicCompletion (𝓞 ℚ) ℚ v u)) ∧
      finTerm(v, B) = ((Real.log q(v) / Real.sqrt q(v) : ℝ) : ℂ) * G 0 ∧ finTerm(v, B) ≠ 0 ∧
      ¬ ∃ T : ℝ, 1 < T ∧ (∀ x ∈ tsupport φ.val, N(x) ∈ Ioo T⁻¹ T) ∧
        ∀ w : V, w ∉ S → T < q(w) := by
  let e : V ≃ Nat.Primes := Rat.HeightOneSpectrum.primesEquiv
  obtain ⟨n,hn⟩ := exists_nat_gt (max (Real.exp (max R Y)) ((S.sup (fun v : V ↦ v.asIdeal.absNorm) : ℕ) : ℝ))
  obtain ⟨p,hnp,hp⟩ := Nat.exists_infinite_primes n
  let v := e.symm ⟨p,hp⟩
  have hv : v.asIdeal.absNorm = p := (NumberFieldKB.Chebotarev.RatIdele.absNorm_asIdeal v).trans
    (congrArg Subtype.val (e.apply_symm_apply ⟨p,hp⟩))
  have hpR : (n : ℝ) ≤ p := by exact_mod_cast hnp
  have hvS : v ∉ S := by
    intro h
    have hh := Finset.le_sup (f := fun w : V ↦ w.asIdeal.absNorm) h
    rw [hv] at hh
    have := ((le_max_right _ _).trans_lt hn).trans_le hpR
    exact (not_lt.mpr (by exact_mod_cast hh)) this
  have hq : 1 < q(v) := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hlog : max R Y < Real.log q(v) := by
    apply (Real.lt_log_iff_exp_lt (zero_lt_one.trans hq)).mpr
    rw [hv]
    exact ((le_max_left _ _).trans_lt hn).trans_le hpR
  obtain ⟨φ,_,B,hx,_,hB⟩ := exists_rational_translated_place_tests G hG hR (Real.log q(v))
  have H := rational_translated_prime_principalValue v G hR ((le_max_left _ _).trans_lt hlog) (B v)
    (fun u ↦ by rw [hB, hx, ideleClassNorm_ofAdicCompletion]; rfl)
  refine ⟨v,φ,B v,hvS,(le_max_right _ _).trans_lt hlog,hx,hB v,H,?_,?_⟩
  · rw [H]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (div_pos (Real.log_pos hq) (Real.sqrt_pos.mpr (zero_lt_one.trans hq))).ne') h₀
  · rintro ⟨T,_,hT,hout⟩
    let qu := Units.mk0 (v.asIdeal.absNorm : ℝ≥0) (by exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm v).pos.ne')
    let x : Cℚ := QuotientGroup.mk' _ (canonicalIdeleNormSection ℚ qu)
    have hnrm : ideleClassNorm ℚ x = qu := canonicalIdeleNormSection_rightInverse ℚ qu
    have hnrm' : N(x) = q(v) := by rw [hnrm]; rfl
    have hnz : φ.val x ≠ 0 := by simpa only [hx, hnrm',sub_self] using h₀
    have hlt := (hT x (subset_tsupport _ hnz)).2
    rw [hnrm'] at hlt
    exact (not_lt.mpr hlt.le) (hout v hvS)

open RiemannMasullo.External.Grh

/-- The smoothed rational prime-power sum for the physical translate, after subtracting
the main term from the upper Mellin pole. -/
def rationalTranslatedPrimeError (G : ℝ → ℂ) (y : ℝ) : ℂ :=
  (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * G (Real.log n - y)) -
    (Real.exp (y / 2) : ℂ) * compactLogMellin G (1/2)

/-- The remaining real-place integral after cancellation against the lower Mellin pole. -/
def rationalTranslatedRealRemainder (G : ℝ → ℂ) (y : ℝ) : ℂ :=
  ∫ t : ℝ, ((Real.exp (-5*t/2) / (1 - Real.exp (-2*t)) : ℝ) : ℂ) * G (t-y)

private theorem translated_remainder_majorant (G : ℝ → ℂ) {R y : ℝ}
    (hR : tsupport G ⊆ Icc (-R) R) (hy : R + 1 ≤ y) (t : ℝ) :
    ‖((Real.exp (-5*t/2) / (1 - Real.exp (-2*t)) : ℝ) : ℂ) * G (t-y)‖ ≤
      ((Real.exp (5*R/2) / (1 - Real.exp (-2))) * Real.exp (-5*y/2)) * ‖G (t-y)‖ := by
  by_cases h : G (t-y) = 0
  · simp [h]
  have hl := (hR (subset_tsupport G h)).1
  have ht : 1 ≤ t := by linarith
  have hden : 0 < 1 - Real.exp (-2) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
  have hd : 1 - Real.exp (-2) ≤ 1 - Real.exp (-2*t) := by
    apply sub_le_sub_left
    exact Real.exp_le_exp.mpr (by linarith)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (div_nonneg (Real.exp_pos _).le (hden.le.trans hd))]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  have he : Real.exp (-5*t/2) ≤ Real.exp (5*R/2) * Real.exp (-5*y/2) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  calc
    _ ≤ (Real.exp (5*R/2) * Real.exp (-5*y/2)) / (1 - Real.exp (-2)) :=
      div_le_div₀ (by positivity) he hden hd
    _ = _ := by ring

/-- The remainder in the real principal value is uniformly at most a constant depending
only on the profile and its support radius times exp(−5y/2). -/
theorem rationalTranslatedRealRemainder_norm (G : ℝ → ℂ) (hG : Continuous G) {R y : ℝ}
    (hR : tsupport G ⊆ Icc (-R) R) (hy : R + 1 ≤ y) :
    ‖rationalTranslatedRealRemainder G y‖ ≤
      ((Real.exp (5*R/2) / (1 - Real.exp (-2))) * (∫ u, ‖G u‖)) * Real.exp (-5*y/2) := by
  have hc : HasCompactSupport G := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hR
  have hi := (hG.integrable_of_hasCompactSupport (μ := volume) hc).norm.comp_sub_right y
  refine (norm_integral_le_of_norm_le (hi.const_mul _) (.of_forall (translated_remainder_majorant G hR hy))).trans_eq ?_
  rw [integral_const_mul, integral_sub_right_eq_self (fun u ↦ ‖G u‖)]
  ring

private theorem translated_upper_pole (G : ℝ → ℂ) (y : ℝ) :
    compactLogMellin (rationalTranslatedMellinProfile G y) 1 =
      (Real.exp (y/2) : ℂ) * compactLogMellin G (1/2) := by
  let H (u : ℝ) := (Real.exp (y/2) : ℂ) * (G u * Complex.exp ((1/2 : ℂ)*u))
  calc
    _ = ∫ t : ℝ, H (t-y) := by
      apply integral_congr_ae (.of_forall fun t ↦ ?_)
      change ((Real.exp (-t/2) : ℂ) * G (t-y)) * Complex.exp (1*(t:ℂ)) = _
      simp only [H, one_mul, Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat,
        Complex.ofReal_sub]
      calc
        _ = G (t-y) * Complex.exp (-((t:ℂ))/2 + t) := by rw [Complex.exp_add]; ring
        _ = G (t-y) * Complex.exp ((y:ℂ)/2 + 1/2*((t:ℂ)-y)) := by congr 2; ring
        _ = _ := by rw [Complex.exp_add]; ring
    _ = ∫ t : ℝ, H t := integral_sub_right_eq_self H y
    _ = _ := integral_const_mul _ _

private theorem translated_gamma_integral (G : ℝ → ℂ) (hG : ContDiff ℝ (∞) G)
    {R y : ℝ} (hR : tsupport G ⊆ Icc (-R) R) (hy : R + 1 ≤ y) :
    let g := rationalTranslatedMellinProfile G y
    (∫ t in Ioi (0:ℝ), g t / (1 - Complex.exp (-2*(t:ℂ)))) =
      (∫ t, g t) + rationalTranslatedRealRemainder G y := by
  let g := rationalTranslatedMellinProfile G y
  have hy' : R < y := by linarith
  have hn (t : ℝ) (ht : t ≤ 0) : g t = 0 := translated_vanishes hR hy' ht
  let E (t : ℝ) := ((Real.exp (-5*t/2) / (1 - Real.exp (-2*t)) : ℝ) : ℂ) * G (t-y)
  have hc : HasCompactSupport g := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (translated_support hR _)
  have hgint : Integrable g := (translated_smooth hG y).continuous.integrable_of_hasCompactSupport hc
  have hGc : HasCompactSupport G := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hR
  have hGr := (hG.continuous.integrable_of_hasCompactSupport (μ:=volume) hGc).norm.comp_sub_right y
  have hE : Integrable E := (hGr.const_mul _).mono' (by
    apply Measurable.aestronglyMeasurable
    dsimp only [E]
    have hGm := hG.continuous.measurable
    fun_prop) (.of_forall (translated_remainder_majorant G hR hy))
  calc
    _ = ∫ t : ℝ, g t / (1 - Complex.exp (-2*(t:ℂ))) := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro t ht
      change g t / (1 - Complex.exp (-2 * (t:ℂ))) = 0
      rw [hn _ (not_lt.mp ht), zero_div]
    _ = ∫ t, g t + E t := by
      apply integral_congr_ae (.of_forall fun t ↦ ?_)
      by_cases hz : G (t-y) = 0
      · simp [g,rationalTranslatedMellinProfile,E,hz]
      have hl := (hR (subset_tsupport G hz)).1
      have ht : 1 ≤ t := by linarith
      have hd : (1 : ℂ) - (Real.exp (-2*t) : ℂ) ≠ 0 := by
        exact_mod_cast (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith : -2*t < 0))).ne'
      have he : Real.exp (-5*t/2) = Real.exp (-t/2) * Real.exp (-2*t) := by
        rw [← Real.exp_add]; congr 1; ring
      have hex : Complex.exp (-2 * (t:ℂ)) = (Real.exp (-2*t) : ℂ) := by push_cast; rfl
      simp only [g,rationalTranslatedMellinProfile,E,he,hex,Complex.ofReal_div,
        Complex.ofReal_mul,Complex.ofReal_sub,Complex.ofReal_one]
      have H (u v z : ℂ) (hv : 1-v ≠ 0) : u*z/(1-v) = u*z + u*v/(1-v)*z := by
        field_simp [hv]
        ring
      exact H _ _ _ hd
    _ = _ := integral_add hgint hE

private theorem translated_weil_sub_poles (G : ℝ → ℂ) (hG : ContDiff ℝ (∞) G)
    {R y : ℝ} (hR : tsupport G ⊆ Icc (-R) R) (hy : R + 1 ≤ y) :
    let g := rationalTranslatedMellinProfile G y
    rationalWeilLocalValue g - compactLogMellin g 0 - compactLogMellin g 1 =
      rationalTranslatedPrimeError G y + rationalTranslatedRealRemainder G y := by
  let g := rationalTranslatedMellinProfile G y
  have hy' : R < y := by linarith
  have hn (t : ℝ) (ht : t ≤ 0) : g t = 0 := translated_vanishes hR hy' ht
  have hp (n : ℕ) : (ArithmeticFunction.vonMangoldt n : ℂ) *
      (g (Real.log n) + g (-Real.log n) / (n : ℂ)) =
      ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * G (Real.log n-y) := by
    rw [hn _ (neg_nonpos.mpr (Real.log_natCast_nonneg _)), zero_div, add_zero]
    obtain rfl | h := Nat.eq_zero_or_pos n
    · simp [g, rationalTranslatedMellinProfile]
    · dsimp only [g,rationalTranslatedMellinProfile]
      rw [exp_neg_half_log (by exact_mod_cast h), Complex.ofReal_div, Complex.ofReal_inv, div_eq_mul_inv, mul_assoc]
  have hreal :
      (∫ t in Ioi (0:ℝ), (g t + Complex.exp (-(t:ℂ)) * g (-t)) / (1 - Complex.exp (-2 * (t:ℂ)))) =
      (∫ t, g t) + rationalTranslatedRealRemainder G y := by
    refine Eq.trans ?_ (translated_gamma_integral G hG hR hy)
    apply setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
    rw [hn _ (neg_nonpos.mpr ht.le),mul_zero,add_zero]
  change rationalWeilLocalValue g - compactLogMellin g 0 - compactLogMellin g 1 = _
  rw [rationalWeilLocalValue,tsum_congr hp,hreal,translated_upper_pole]
  simp only [compactLogMellin,zero_mul,Complex.exp_zero,mul_one,rationalTranslatedPrimeError,
    rationalTranslatedRealRemainder]
  ring

local notation "μℚ" => ideleClassTamagawaMeasure ℚ
local notation "Vℚ" => (((normOneIdeleClassTamagawaMeasure ℚ) univ).toReal : ℂ)

/-- Paper: Equations (12.5.1.2)–(12.5.1.4), pp. 519–520. For the physical translate
of any smooth compact rational radial test sufficiently far in positive log norm,
the actual wide geometric diagonal is the norm-one Tamagawa volume times the
smoothed prime error plus the remaining real-place integral.
Deviation: The rational calibration uses the classical zeta explicit formula. -/
theorem rational_wide_diagonal_translated_prime_error (G : ℝ → ℂ) (hG : ContDiff ℝ (∞) G)
    {R y : ℝ} (hR : tsupport G ⊆ Icc (-R) R) (hy : R + 1 ≤ y)
    (φ : BruhatCompactSupport Cℚ) (hφ : ∀ x : Cℚ, φ.val x = G (Real.log N(x) - y))
    {α s : ℝ} (hw : 1/2 ≤ α) (hs : 3 ≤ s) (U : ℕ → Set Cℚ)
    (hU : IsDPrimeSequence μℚ U) (hm : ∀ n, MeasurableSet (U n)) :
    centeredStripGeometricDiagonalIntegral φ ((half_pos zero_lt_one).trans_le hw) hs U =
      Vℚ * (rationalTranslatedPrimeError G y + rationalTranslatedRealRemainder G y) := by
  let g := rationalTranslatedMellinProfile G y
  have hc : HasCompactSupport g := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (translated_support hR _)
  have hd := integral_rational_wide_diagonal_eq_weilLocal_sub_poles g (translated_smooth hG y) hc
    (translated_vanishes hR (by linarith : R < y) le_rfl) φ
    (fun x ↦ (hφ x).trans (rationalCenteredLogProfile_translated G _ _).symm) hw hs U hU hm
  exact hd.2.trans (congrArg (Vℚ * ·) (translated_weil_sub_poles G hG hR hy))

/-- Uniform error estimate comparing the actual wide rational diagonal and the
translated smoothed prime error. The constant is independent of the translation,
strip width, Sobolev order, and smoothing sequence. -/
theorem norm_rational_wide_diagonal_sub_translated_prime_error (G : ℝ → ℂ) (hG : ContDiff ℝ (∞) G)
    {R y : ℝ} (hR : tsupport G ⊆ Icc (-R) R) (hy : R + 1 ≤ y)
    (φ : BruhatCompactSupport Cℚ) (hφ : ∀ x : Cℚ, φ.val x = G (Real.log N(x) - y))
    {α s : ℝ} (hw : 1/2 ≤ α) (hs : 3 ≤ s) (U : ℕ → Set Cℚ)
    (hU : IsDPrimeSequence μℚ U) (hm : ∀ n, MeasurableSet (U n)) :
    ‖centeredStripGeometricDiagonalIntegral φ ((half_pos zero_lt_one).trans_le hw) hs U -
        Vℚ * rationalTranslatedPrimeError G y‖ ≤
      (‖Vℚ‖ * (Real.exp (5*R/2) / (1 - Real.exp (-2))) * (∫ u, ‖G u‖)) * Real.exp (-5*y/2) := by
  rw [rational_wide_diagonal_translated_prime_error G hG hR hy φ hφ hw hs U hU hm,
    mul_add, add_sub_cancel_left, norm_mul]
  exact (mul_le_mul_of_nonneg_left (rationalTranslatedRealRemainder_norm G hG.continuous hR hy)
    (norm_nonneg _)).trans_eq (by ring)

private theorem translated_one_place_bound (v : V) (G : ℝ → ℂ) (hG : Continuous G)
    {R : ℝ} (hR : tsupport G ⊆ Icc (-R) R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, R < y → ∀ B : BruhatCompactSupport K(v)ˣ,
      (∀ u, B.val u = G (Real.log ‖u.val‖ - y)) → ‖finTerm(v, B)‖ ≤ C * Real.exp (-y/2) := by
  let L := Real.log q(v)
  have hL : 0 < L := Real.log_pos (by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v)
  obtain ⟨M,hM⟩ := exists_nat_ge (2*R/L)
  have hM' := (div_le_iff₀ hL).mp hM
  have hc : HasCompactSupport G := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hR
  obtain ⟨B₀,hB₀⟩ := hc.exists_bound_of_continuous hG
  have hpos : 0 ≤ B₀ := (norm_nonneg _).trans (hB₀ 0)
  let D := L * Real.exp (R/2) * B₀
  have hD : 0 ≤ D := mul_nonneg (mul_nonneg hL.le (Real.exp_pos _).le) hpos
  refine ⟨((2*M+1:ℕ):ℝ)*D, mul_nonneg (Nat.cast_nonneg _) hD, ?_⟩
  intro y hy B hB
  let t (k : ℕ) : ℝ := ((k:ℝ)+1)*L
  let f (k : ℕ) : ℂ := (L : ℂ) * rationalTranslatedMellinProfile G y (t k)
  have hS : HasSum f (finTerm(v, B)) := by
    refine (hasSum_finite_principalValue_positive_radial v (rationalTranslatedMellinProfile G y)
      (fun _ ht ↦ translated_vanishes hR hy ht) B
      (fun u ↦ (hB u).trans (rationalCenteredLogProfile_translated G y _).symm)).congr_fun ?_
    intro k
    simp only [Real.log_pow, Nat.cast_add,Nat.cast_one,f,t,L]
  have hbound (k : ℕ) : ‖f k‖ ≤ D*Real.exp (-y/2) := by
    by_cases h : G (t k-y) = 0
    · simp only [f,rationalTranslatedMellinProfile,h,mul_zero,norm_zero]
      positivity
    have ht := (hR (subset_tsupport G h)).1
    have he : Real.exp (-t k/2) ≤ Real.exp (R/2)*Real.exp (-y/2) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith)
    simp only [f,rationalTranslatedMellinProfile,norm_mul,Complex.norm_real,
      Real.norm_of_nonneg hL.le,Real.norm_of_nonneg (Real.exp_pos _).le]
    calc
      _ ≤ L * ((Real.exp (R/2) * Real.exp (-y/2)) * B₀) :=
        mul_le_mul_of_nonneg_left (mul_le_mul he (hB₀ _) (norm_nonneg _) (by positivity)) hL.le
      _ = _ := by dsimp only [D]; ring
  rw [← hS.tsum_eq]
  by_cases H : ∃ k, G (t k-y) ≠ 0
  · obtain ⟨k,hk⟩ := H
    let I := Finset.Icc (k-M) (k+M)
    have hdist (i j : ℕ) (hi : G (t i -y) ≠ 0) (hj : G (t j-y) ≠ 0) : i ≤ j+M := by
      by_contra! h
      have hl := (hR (subset_tsupport G hj)).1
      have hr := (hR (subset_tsupport G hi)).2
      have hc' : ((j + M : ℕ) : ℝ) < i := by exact_mod_cast h
      have hh := mul_lt_mul_of_pos_right hc' hL
      rw [Nat.cast_add] at hh
      dsimp only [t] at hl hr
      nlinarith
    have hcard : I.card ≤ 2*M+1 := by dsimp only [I]; rw [Nat.card_Icc]; omega
    rw [tsum_eq_sum (s := I) (fun i hi ↦ by
      have hz : G (t i-y) = 0 := by
        by_contra hn
        exact hi (Finset.mem_Icc.mpr ⟨by have := hdist k i hk hn; omega,hdist i k hn hk⟩)
      simp [f,rationalTranslatedMellinProfile,hz])]
    calc
      _ ≤ ∑ _i ∈ I, D * Real.exp (-y/2) := norm_sum_le_of_le _ (fun i _ ↦ hbound i)
      _ = (I.card : ℝ) * (D * Real.exp (-y/2)) := by simp
      _ ≤ ((2*M+1:ℕ):ℝ) * (D * Real.exp (-y/2)) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
      _ = _ := by ring
  · push Not at H
    simp only [f,rationalTranslatedMellinProfile,H,mul_zero,tsum_zero,norm_zero]
    positivity

/-- For each fixed finite set of rational places, the sum of the normalized finite
principal values of a physically translated compact pulse is O(exp(−y/2)).
Each prime contributes only boundedly many powers in a fixed-length log window. -/
theorem rational_translated_finite_places_bound (G : ℝ → ℂ) (hG : Continuous G)
    {R : ℝ} (hR : tsupport G ⊆ Icc (-R) R) (S : Finset V) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, R < y →
      ∀ B : (v : V) → BruhatCompactSupport K(v)ˣ,
      (∀ v ∈ S, ∀ u, (B v).val u = G (Real.log ‖u.val‖ - y)) →
      ‖∑ v ∈ S, finTerm(v, B v)‖ ≤ C * Real.exp (-y/2) := by
  choose C hpos hC using fun v : V ↦ translated_one_place_bound v G hG hR
  refine ⟨∑ v ∈ S, C v,Finset.sum_nonneg (fun v _ ↦ hpos v),?_⟩
  intro y hy B hB
  rw [Finset.sum_mul]
  exact norm_sum_le_of_le _ (fun v hv ↦ hC v y hy (B v) (hB v hv))

local notation "wℝ" => Rat.infinitePlace
local notation "mℚ" => (⟨ideleClassNorm ℚ, (isProperMap_ideleClassNorm ℚ).continuous⟩ : Cℚ →ₜ* ℝ≥0ˣ)
local notation "pole(" φ ", " b ")" =>
  modulatedFourierMellin mℚ univ
    (⟨isProperMap_ideleClassNorm ℚ, ideleClassNorm_ne_one (F := ℚ)⟩ : IsModulation mℚ)
    μℚ (φ : BruhatCompactSupport Cℚ).val (ideleClassNormTwist (F := ℚ) 1 b)

/-- Paper: pp. 519–520. For a fixed finite set of rational places, the actual
normalized place values less both global poles equal the negative upper polar
main term up to O(exp(−y/2)). A nonnegative pulse with positive upper moment
therefore has a fixed-set value of order exp(y/2).
Deviation: The fixed-set asymptotic is taken in the physical translation. The
paper chooses its finite set after the test. -/
theorem rational_translated_fixed_places_sub_poles (G : ℝ → ℂ) (hG : ContDiff ℝ (∞) G)
    {R : ℝ} (hR₀ : 0 ≤ R) (hR : tsupport G ⊆ Icc (-R) R) (S : Finset V) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, R+1 ≤ y →
      ∀ (φ : BruhatCompactSupport Cℚ) (A : BruhatCompactSupport Rat.infinitePlace.Completionˣ)
        (B : (v : V) → BruhatCompactSupport K(v)ˣ),
      (∀ x : Cℚ, φ.val x = G (Real.log N(x) - y)) →
      (∀ u, A.val u = φ.val (IdeleClassGroup.ofCompletion (𝓞 ℚ) ℚ wℝ u)) →
      (∀ v ∈ S, ∀ u, (B v).val u = φ.val (IdeleClassGroup.ofAdicCompletion (𝓞 ℚ) ℚ v u)) →
      ‖(Vℚ * (infiniteConnesWeilPrincipalValue wℝ A + ∑ v ∈ S, finTerm(v, B v)) -
          pole(φ, -(1/2)) - pole(φ, 1/2)) + Vℚ * ((Real.exp (y/2) : ℂ) * compactLogMellin G (1/2))‖ ≤
        C * Real.exp (-y/2) := by
  obtain ⟨C,hC,hplace⟩ := rational_translated_finite_places_bound G hG.continuous hR S
  let Carch := (Real.exp (5*R/2) / (1 - Real.exp (-2))) * (∫ u, ‖G u‖)
  have hden : 0 < 1-Real.exp (-2) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
  have hCarch : 0 ≤ Carch := mul_nonneg (div_nonneg (Real.exp_pos _).le hden.le) (integral_nonneg (fun _ ↦ norm_nonneg _))
  refine ⟨‖Vℚ‖ * (Carch + C),mul_nonneg (norm_nonneg _) (add_nonneg hCarch hC), ?_⟩
  intro y hy φ A B hφ hA hB
  let g := rationalTranslatedMellinProfile G y
  have hφ' (x : Cℚ) : φ.val x = rationalCenteredLogProfile g (Real.log N(x)) :=
    (hφ x).trans (rationalCenteredLogProfile_translated G _ _).symm
  have hreal (u : Rat.infinitePlace.Completionˣ) : A.val u = rationalCenteredLogProfile g (Real.log ‖u.val‖) := by
    rw [hA,hφ',ideleClassNorm_ofCompletion,Rat.isReal_infinitePlace.mult_eq_one,pow_one]
    rfl
  have hP := hplace y (by linarith) B (fun v hv u ↦ by
    rw [hB v hv, hφ, ideleClassNorm_ofAdicCompletion]; rfl)
  have hl : pole(φ,-(1/2)) = Vℚ * compactLogMellin g 0 := by
    simpa only [zero_sub] using rationalCenteredNormTest_mellin g φ hφ' 0
  have hu : pole(φ,1/2) = Vℚ * ((Real.exp (y/2) : ℂ) * compactLogMellin G (1/2)) := by
    rw [← translated_upper_pole]
    simpa only [show (1 : ℂ)-1/2 = 1/2 by norm_num] using rationalCenteredNormTest_mellin g φ hφ' 1
  have harch : infiniteConnesWeilPrincipalValue wℝ A = compactLogMellin g 0 + rationalTranslatedRealRemainder G y := by
    rw [rational_real_principalValue_positive_log_profile g (translated_smooth hG y).continuous
      (by linarith : 0 < y-R) (translated_support hR y) A hreal, translated_gamma_integral G hG hR hy]
    simp [compactLogMellin,g]
  rw [harch,hl,hu]
  have halg (v a b c d : ℂ) : v*(a+b+c)-v*a-v*d+v*d = v*(b+c) := by ring
  rw [halg,norm_mul]
  have hE : ‖rationalTranslatedRealRemainder G y‖ ≤ Carch * Real.exp (-y/2) :=
    (rationalTranslatedRealRemainder_norm G hG.continuous hR hy).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hCarch)
  calc
    _ ≤ ‖Vℚ‖ * (Carch*Real.exp (-y/2) + C*Real.exp (-y/2)) :=
      mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add hE hP)) (norm_nonneg _)
    _ = _ := by ring

private theorem exponential_pole_dominates (C K Y : ℝ) {α m : ℝ} (hα : α < 1/2) (hm : 0 < m) :
    ∃ y : ℝ, Y ≤ y ∧ C*Real.exp (-y/2) + K*Real.exp (α*y) < m*Real.exp (y/2) := by
  have hlim : Tendsto (fun y : ℝ ↦ C*Real.exp (-y) + K*Real.exp ((α-1/2)*y)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply,id_eq,mul_zero,add_zero] using
      (tendsto_const_nhds.mul Real.tendsto_exp_neg_atTop_nhds_zero).add
        (tendsto_const_nhds.mul (Real.tendsto_exp_atBot.comp
          (tendsto_id.const_mul_atTop_of_neg (sub_neg.mpr hα))))
  obtain ⟨y, hy,h⟩ := ((eventually_ge_atTop Y).and (hlim.eventually_lt_const hm)).exists
  refine ⟨y,hy,?_⟩
  have h₁ : Real.exp (-y)*Real.exp (y/2) = Real.exp (-y/2) := by rw [← Real.exp_add]; congr 1; ring
  have h₂ : Real.exp ((α-1/2)*y)*Real.exp (y/2) = Real.exp (α*y) := by rw [← Real.exp_add]; congr 1; ring
  have hh := mul_lt_mul_of_pos_right h (Real.exp_pos (y/2))
  rwa [add_mul,mul_assoc,mul_assoc,h₁,h₂] at hh

private theorem nonnegative_profile_upper_moment (G : ℝ → ℝ) (hG : Continuous G)
    (hc : HasCompactSupport G) (hn : 0 ≤ G) (h₀ : 0 < G 0) :
    compactLogMellin (fun t ↦ (G t : ℂ)) (1/2) ≠ 0 := by
  let H (t : ℝ) := G t * Real.exp (t/2)
  have hH : Continuous H := hG.mul (Real.continuous_exp.comp (continuous_id.div_const 2))
  have hm : 0 < ∫ t, H t := integral_pos_of_integrable_nonneg_ne_zero hH
    (hH.integrable_of_hasCompactSupport hc.mul_right)
    (fun t ↦ mul_nonneg (hn t) (Real.exp_pos _).le) (x:=0) (mul_pos h₀ (Real.exp_pos _)).ne'
  have he : compactLogMellin (fun t ↦ (G t : ℂ)) (1/2) = ((∫ t, H t : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    apply integral_congr_ae (.of_forall fun t ↦ ?_)
    dsimp only [H]
    rw [Complex.ofReal_mul,Complex.ofReal_exp,Complex.ofReal_div,Complex.ofReal_ofNat]
    congr 2
    ring
  exact he ▸ Complex.ofReal_ne_zero.mpr hm.ne'

/-- Paper: p. 520. For every fixed finite set of places and every exponent below
one half, arbitrarily high translates of a prescribed nonnegative pulse exceed
every proposed constant times exp(αy) in the pole-corrected fixed-place value.
Deviation: This concerns the fixed-set local expression. The full place sum includes
new primes along these translates. -/
theorem rational_translated_fixed_places_exceeds_sub_half_power
    (G : ℝ → ℝ) (hG : ContDiff ℝ (∞) G) {R : ℝ} (hR₀ : 0 ≤ R) (hR : tsupport G ⊆ Icc (-R) R)
    (hn : 0 ≤ G) (h₀ : 0 < G 0) (S : Finset V) {α : ℝ} (hα : α < 1/2) (K Y : ℝ) :
    ∃ (y : ℝ) (φ : BruhatCompactSupport Cℚ) (A : BruhatCompactSupport Rat.infinitePlace.Completionˣ)
      (B : (v : V) → BruhatCompactSupport K(v)ˣ),
      Y ≤ y ∧ (∀ x : Cℚ, φ.val x = (G (Real.log N(x)-y) : ℂ)) ∧
      (∀ u, A.val u = φ.val (IdeleClassGroup.ofCompletion (𝓞 ℚ) ℚ wℝ u)) ∧
      (∀ v u, (B v).val u = φ.val (IdeleClassGroup.ofAdicCompletion (𝓞 ℚ) ℚ v u)) ∧
      K*Real.exp (α*y) <
        ‖Vℚ * (infiniteConnesWeilPrincipalValue wℝ A + ∑ v ∈ S, finTerm(v, B v)) -
          pole(φ, -(1/2)) - pole(φ, 1/2)‖ := by
  let H (t : ℝ) := (G t : ℂ)
  have hH : ContDiff ℝ (∞) H := Complex.ofRealCLM.contDiff.comp hG
  have hHR : tsupport H ⊆ Icc (-R) R := by
    apply closure_minimal _ isClosed_Icc
    intro t ht
    exact hR (subset_tsupport G (fun h ↦ ht (by simp [H,h])))
  have hGc : HasCompactSupport G := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hR
  let m := Vℚ * compactLogMellin H (1/2)
  have hm : m ≠ 0 := mul_ne_zero rationalNormOneTamagawaVolume_ne_zero (nonnegative_profile_upper_moment G hG.continuous hGc hn h₀)
  obtain ⟨C,_,hC⟩ := rational_translated_fixed_places_sub_poles H hH hR₀ hHR S
  obtain ⟨y,hy,hp⟩ := exponential_pole_dominates C K (max Y (R+1)) hα (norm_pos_iff.mpr hm)
  obtain ⟨φ,A,B,hφ,hA,hB⟩ := exists_rational_translated_place_tests H hH hHR y
  refine ⟨y,φ,A,B,(le_max_left _ _).trans hy,hφ,hA,hB,?_⟩
  let d := Vℚ * (infiniteConnesWeilPrincipalValue wℝ A + ∑ v ∈ S, finTerm(v, B v)) -
          pole(φ, -(1/2)) - pole(φ, 1/2)
  have hd := hC y ((le_max_right _ _).trans hy) φ A B hφ hA (fun v _ ↦ hB v)
  have hid : Vℚ * ((Real.exp (y/2):ℂ) * compactLogMellin H (1/2)) = m * (Real.exp (y/2):ℂ) := by dsimp [m]; ring
  change ‖d + _‖ ≤ _ at hd
  rw [hid] at hd
  have htri : ‖m‖ * Real.exp (y/2) ≤ C*Real.exp (-y/2) + ‖d‖ := calc
    _ = ‖d + m*(Real.exp (y/2):ℂ) - d‖ := by
      rw [add_sub_cancel_left,norm_mul m (Real.exp (y/2):ℂ),Complex.norm_real (Real.exp (y/2)),
        Real.norm_of_nonneg (Real.exp_pos _).le]
    _ ≤ _ := (norm_sub_le _ _).trans (add_le_add hd le_rfl)
  change K*Real.exp (α*y) < ‖d‖
  linarith

end RiemannMasullo.StripNuclearity
