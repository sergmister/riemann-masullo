module

public import RiemannMasullo.AppB_AnalyticNT.Sec1
public import RiemannMasullo.ForMathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Basic
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.NumberTheory.LSeries.WienerIkehara
import all RiemannMasullo.Ch03_IdelicZeta.Sec2
import RiemannMasullo.ForMathlib.Analysis.Complex.LandauLemma
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Pow.Complex
import RiemannMasullo.ForMathlib.NumberTheory.EulerProduct.Basic
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.HeckeLFunction

/-!
# Classical zero-free regions for Hecke L-functions

Masullo, §B.6, pp. 636–643. The finite Hecke L-function is represented by a
meromorphic continuation in normal form, as in §B.1.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped Asymptotics Topology

namespace RiemannMasullo

variable {F : Type*} [Field F] [NumberField F]

local notation "U[" F "]" => PontryaginDual (IdeleClassGroup (𝓞 F) F)
local notation "𝒳[" F "]" => HeckeCharacter (𝓞 F) F
local notation "halfPlane" => Complex.re ⁻¹' Ioi (1 : ℝ)
local notation "atHeight" => comap (abs ∘ Complex.im) atTop
local notation "atAbsTop" => comap (abs : ℝ → ℝ) atTop

/-- Paper: §B.6.1.2, p. 636. The value at a nonzero integral ideal is the
product of local uniformizer values with the ideal's prime exponents. At a
ramified prime the local value used in this product is zero.
Deviation: The value at the zero ideal is set to zero. -/
def heckeIdealValue (χ : 𝒳[F]) (I : Ideal (𝓞 F)) : ℂ :=
  open Classical in
  if I = ⊥ then 0 else
    ∏ᶠ v : HeightOneSpectrum (𝓞 F),
      (if χ.IsUnramifiedAt v then χ.localValue v else 0) ^ multiplicity v.asIdeal I

open Classical in
/-- Paper: §B.6.1.2, p. 636. The value on a positive power of a prime ideal
is the corresponding power of the local value, or zero at a ramified prime. -/
theorem heckeIdealValue_prime_pow (χ : 𝒳[F]) (v : HeightOneSpectrum (𝓞 F))
    {k : ℕ} (hk : 0 < k) :
    heckeIdealValue χ (v.asIdeal ^ k) =
      if χ.IsUnramifiedAt v then χ.localValue v ^ k else 0 := by
  have hne : v.asIdeal ^ k ≠ ⊥ := pow_ne_zero _ v.ne_bot
  unfold heckeIdealValue
  rw [ite_eq_right hne, finprod_eq_single _ v, multiplicity_pow_self_of_prime v.prime]
  · split_ifs <;> simp [hk.ne']
  · intro w hw
    rw [multiplicity_eq_zero_of_not_dvd fun hd ↦ hw (HeightOneSpectrum.eq_of_dvd_pow hd), pow_zero]

/-- Paper: Equation (B.6.1.2), p. 636. To the right of one, the series indexed
by nonzero integral ideals converges absolutely to the finite Hecke L-function. -/
theorem finiteHeckeL_hasSum_ideals (χ : U[F]) (s : halfPlane) :
    HasSum (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} ↦
      heckeIdealValue (ideleClassNormTwist χ 0) I.val / (I.val.absNorm : ℂ) ^ (s : ℂ))
      (finiteHeckeL χ s) := by
  classical
  let a (v : HeightOneSpectrum (𝓞 F)) : ℂ :=
    if (ideleClassNormTwist χ 0).IsUnramifiedAt v then
      (ideleClassNormTwist χ 0).localValue v else 0
  let factor (I : Ideal (𝓞 F)) (v : HeightOneSpectrum (𝓞 F)) :=
    a v ^ multiplicity v.asIdeal I
  let value := heckeIdealValue (ideleClassNormTwist χ 0)
  have hzero : value 0 = 0 := by simp [value, heckeIdealValue]
  have hvalue {I : Ideal (𝓞 F)} (hI : I ≠ 0) : value I = ∏ᶠ v, factor I v := by
    have hI' : I ≠ ⊥ := by simpa only [Ideal.zero_eq_bot] using hI
    simp only [value, heckeIdealValue, ite_eq_right hI', factor, a]
  have hsupport (I : Ideal (𝓞 F)) : (factor I).HasFiniteMulSupport :=
    UniqueFactorizationMonoid.hasFiniteMulSupport_fun_pow_multiplicity a
      HeightOneSpectrum.asIdeal_injective HeightOneSpectrum.irreducible
  let c : Ideal (𝓞 F) →*₀ ℂ :=
    { toFun := value
      map_zero' := hzero
      map_one' := by
        rw [hvalue one_ne_zero]
        exact finprod_eq_one_of_forall_eq_one fun v ↦ by simp only [factor, multiplicity_one_right, pow_zero]
      map_mul' := by
        intro I J
        by_cases hI : I = 0
        · simp only [hI, zero_mul, hzero]
        by_cases hJ : J = 0
        · simp only [hJ, mul_zero, hzero]
        rw [hvalue (mul_ne_zero hI hJ), hvalue hI, hvalue hJ,
          ← finprod_mul_distrib (hsupport I) (hsupport J)]
        apply finprod_congr
        intro v
        simp only [factor, multiplicity_mul v.prime
          (FiniteMultiplicity.of_prime_left v.prime (mul_ne_zero hI hJ)), pow_add] }
  have hd (v w : HeightOneSpectrum (𝓞 F)) (h : v.asIdeal ∣ w.asIdeal) : v = w :=
    HeightOneSpectrum.ext (w.isMaximal.eq_of_le v.isPrime.ne_top (Ideal.dvd_iff_le.mp h)).symm
  have hcPrime (v : HeightOneSpectrum (𝓞 F)) : c v.asIdeal = a v := by
    change value v.asIdeal = _
    rw [hvalue v.prime.ne_zero, finprod_eq_single _ v]
    · simp only [factor, multiplicity_self (FiniteMultiplicity.of_prime_left v.prime v.prime.ne_zero),
        pow_one]
    · intro w hw
      simp only [factor, multiplicity_eq_zero_of_not_dvd (fun h ↦ hw (hd w v h)), pow_zero]
  have ha (v : HeightOneSpectrum (𝓞 F)) : ‖a v‖ ≤ 1 := by
    by_cases h : (ideleClassNormTwist χ 0).IsUnramifiedAt v <;>
      simp [a, h, norm_ideleClassNormTwist_zero_localValue]
  have hc (I : Ideal (𝓞 F)) : ‖c I‖ ≤ 1 := by
    by_cases hI : I = 0
    · rw [hI, map_zero, norm_zero]
      exact zero_le_one
    change ‖value I‖ ≤ 1
    rw [hvalue hI, finprod_eq_prod _ (hsupport I), norm_prod]
    exact Finset.prod_le_one₀ (fun v _ ↦ norm_nonneg _) fun v _ ↦ by
      simp only [factor, norm_pow]
      exact pow_le_one₀ (norm_nonneg _) (ha v)
  let term : Ideal (𝓞 F) →*₀ ℂ :=
    { toFun := fun I ↦ c I * ((I.absNorm : ℝ) : ℂ) ^ (-(s : ℂ))
      map_zero' := by rw [map_zero c, zero_mul]
      map_one' := by rw [map_one c, map_one, Nat.cast_one, Complex.ofReal_one,
        Complex.one_cpow, mul_one]
      map_mul' := by
        intro I J
        rw [map_mul c, map_mul, Nat.cast_mul, Complex.ofReal_mul,
          Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg I.absNorm) (Nat.cast_nonneg J.absNorm)]
        ring }
  have hr : 1 < (s : ℂ).re := s.property
  have hbound (I : Ideal (𝓞 F)) : ‖term I‖ ≤ (I.absNorm : ℝ) ^ (-(s : ℂ).re) := by
    by_cases hI : I = 0
    · rw [hI, map_zero, norm_zero]
      positivity
    have hN : (0 : ℝ) < I.absNorm := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (by simpa only [Ideal.zero_eq_bot] using hI))
    change ‖c I * ((I.absNorm : ℝ) : ℂ) ^ (-(s : ℂ))‖ ≤ _
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hN, Complex.neg_re]
    exact mul_le_of_le_one_left (Real.rpow_nonneg hN.le _) (hc I)
  have hsum : Summable (fun I ↦ ‖term I‖) :=
    (summable_absNorm_rpow F hr).of_nonneg_of_le (fun _ ↦ norm_nonneg _) hbound
  have hprod := hasProd_eulerFactors_of_summable
    (fun v : HeightOneSpectrum (𝓞 F) ↦ v.asIdeal) (fun v ↦ v.prime) hd
    (fun I hI h1 ↦ by
      obtain ⟨J, hJ, hIJ⟩ := I.exists_le_maximal (by simpa only [Ideal.one_eq_top] using h1)
      exact ⟨⟨J, hJ.isPrime, fun h ↦ hI (le_bot_iff.mp (h ▸ hIJ))⟩, Ideal.dvd_iff_le.mpr hIJ⟩)
    term hsum (fun v ↦ by
      have hv : 1 < (v.asIdeal.absNorm : ℝ) := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
      have hlt := (hbound v.asIdeal).trans_lt
        (Real.rpow_lt_one_of_one_lt_of_neg hv (by linarith : -(s : ℂ).re < 0))
      exact fun h ↦ (ne_of_lt hlt) (by rw [h, norm_one]))
  have hlocal (v : HeightOneSpectrum (𝓞 F)) :
      finiteHeckeEulerFactor χ v s = (1 - term v.asIdeal)⁻¹ := by
    change _ = (1 - c v.asIdeal * ((v.asIdeal.absNorm : ℝ) : ℂ) ^ (-(s : ℂ)))⁻¹
    rw [hcPrime, Complex.ofReal_natCast]
    by_cases h : (ideleClassNormTwist χ 0).IsUnramifiedAt v <;> simp [finiteHeckeEulerFactor, a, h]
  have hEq : (∑' I, term I) = finiteHeckeL χ s :=
    (hprod.congr_fun hlocal).unique (finiteHeckeL_hasProd χ s)
  have hsupport' : Function.support (term : Ideal (𝓞 F) → ℂ) ⊆ {I | I ≠ ⊥} := by
    intro I hI hBot
    exact hI ((show I = 0 by simpa only [Ideal.zero_eq_bot] using hBot) ▸ term.map_zero)
  refine ((hasSum_subtype_iff_of_support_subset hsupport').mpr
    (hEq ▸ hsum.of_norm.hasSum)).congr_fun fun I ↦ ?_
  change value I.val / (I.val.absNorm : ℂ) ^ (s : ℂ) =
    value I.val * ((I.val.absNorm : ℝ) : ℂ) ^ (-(s : ℂ))
  rw [Complex.ofReal_natCast, Complex.cpow_neg, div_eq_mul_inv]

/-- Paper: Equation (B.6.1.3), p. 636. The summatory function adds the values
at nonzero integral ideals of norm at most `x`. -/
def heckeIdealSummatory (χ : 𝒳[F]) (x : ℝ) : ℂ :=
  ∑ᶠ I : {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ (I.absNorm : ℝ) ≤ x}, heckeIdealValue χ I.val

/-- Paper: Equation (B.6.1.3), p. 636. At `x = 1` only the unit ideal contributes. -/
theorem heckeIdealSummatory_one (χ : 𝒳[F]) : heckeIdealSummatory χ 1 = 1 := by
  have hmem : ∀ I : Ideal (𝓞 F), I ≠ ⊥ ∧ (I.absNorm : ℝ) ≤ 1 ↔ I = ⊤ := fun I ↦ by
    constructor
    · rintro ⟨h0, h1⟩
      have h1' : Ideal.absNorm I ≤ 1 := by exact_mod_cast h1
      have h0' : Ideal.absNorm I ≠ 0 := fun h ↦ h0 (Ideal.absNorm_eq_zero_iff.mp h)
      exact Ideal.absNorm_eq_one_iff.mp (by omega)
    · rintro rfl
      exact ⟨top_ne_bot, by simp⟩
  let : Unique {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ (I.absNorm : ℝ) ≤ 1} :=
    { default := ⟨⊤, (hmem ⊤).mpr rfl⟩
      uniq := fun I ↦ Subtype.ext ((hmem I.val).mp I.2) }
  unfold heckeIdealSummatory
  rw [finsum_unique]
  show heckeIdealValue χ ⊤ = 1
  unfold heckeIdealValue
  rw [ite_eq_right top_ne_bot]
  refine finprod_eq_one_of_forall_eq_one fun w ↦ ?_
  rw [← Ideal.one_eq_top, multiplicity_one_right, pow_zero]

/-- Paper: Equation (B.6.1.4), p. 636. The coefficient at `x` sums the
values at nonzero integral ideals of norm exactly `x`. The sum is zero if
there are no such ideals. -/
def heckeNormCoefficient (χ : 𝒳[F]) (x : ℝ) : ℂ :=
  ∑ᶠ I : {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ (I.absNorm : ℝ) = x}, heckeIdealValue χ I.val

/-- Paper: Equation (B.6.1.4), p. 636. At natural numbers the coefficients
agree with the coefficients of Mathlib's formal Euler product. -/
theorem heckeNormCoefficient_natCast (χ : 𝒳[F]) (m : ℕ) :
    heckeNormCoefficient χ (m : ℝ) = χ.LFunction m := by
  classical
  let a (v : HeightOneSpectrum (𝓞 F)) : ℂ :=
    if χ.IsUnramifiedAt v then χ.localValue v else 0
  let factor (I : Ideal (𝓞 F)) (v : HeightOneSpectrum (𝓞 F)) :=
    a v ^ multiplicity v.asIdeal I
  let value := heckeIdealValue χ
  have hzero : value 0 = 0 := by simp [value, heckeIdealValue]
  have hvalue {I : Ideal (𝓞 F)} (hI : I ≠ 0) : value I = ∏ᶠ v, factor I v := by
    have hI' : I ≠ ⊥ := by simpa only [Ideal.zero_eq_bot] using hI
    simp only [value, heckeIdealValue, ite_eq_right hI', factor, a]
  have hsupport (I : Ideal (𝓞 F)) : (factor I).HasFiniteMulSupport :=
    UniqueFactorizationMonoid.hasFiniteMulSupport_fun_pow_multiplicity a
      HeightOneSpectrum.asIdeal_injective HeightOneSpectrum.irreducible
  let c : Ideal (𝓞 F) →*₀ ℂ :=
    { toFun := value
      map_zero' := hzero
      map_one' := by
        rw [hvalue one_ne_zero]
        exact finprod_eq_one_of_forall_eq_one fun v ↦ by
          simp only [factor, multiplicity_one_right, pow_zero]
      map_mul' := by
        intro I J
        by_cases hI : I = 0
        · simp only [hI, zero_mul, hzero]
        by_cases hJ : J = 0
        · simp only [hJ, mul_zero, hzero]
        rw [hvalue (mul_ne_zero hI hJ), hvalue hI, hvalue hJ,
          ← finprod_mul_distrib (hsupport I) (hsupport J)]
        apply finprod_congr
        intro v
        simp only [factor, multiplicity_mul v.prime
          (FiniteMultiplicity.of_prime_left v.prime (mul_ne_zero hI hJ)), pow_add] }
  have hd (v w : HeightOneSpectrum (𝓞 F)) (h : v.asIdeal ∣ w.asIdeal) : v = w :=
    HeightOneSpectrum.ext (w.isMaximal.eq_of_le v.isPrime.ne_top (Ideal.dvd_iff_le.mp h)).symm
  have hcPrime (v : HeightOneSpectrum (𝓞 F)) : c v.asIdeal = a v := by
    change value v.asIdeal = _
    rw [hvalue v.prime.ne_zero, finprod_eq_single _ v]
    · simp only [factor,
        multiplicity_self (FiniteMultiplicity.of_prime_left v.prime v.prime.ne_zero), pow_one]
    · intro w hw
      simp only [factor, multiplicity_eq_zero_of_not_dvd (fun h ↦ hw (hd w v h)), pow_zero]
  have hN (v : HeightOneSpectrum (𝓞 F)) : 1 < v.asIdeal.absNorm :=
    NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hE (v : HeightOneSpectrum (𝓞 F)) : χ.localEulerFactor v =
      ArithmeticFunction.ofPowerSeries v.asIdeal.absNorm (PowerSeries.mk fun k ↦ a v ^ k) := by
    rw [HeckeCharacter.localEulerFactor, card_residueField_adicCompletion,
      hecke_localPowerSeries_eq_mk]
  have hEpow (v : HeightOneSpectrum (𝓞 F)) (k : ℕ) :
      χ.localEulerFactor v (v.asIdeal.absNorm ^ k) = a v ^ k := by
    rw [hE, ArithmeticFunction.ofPowerSeries_apply_pow (hN v), PowerSeries.coeff_mk]
  have hEne (v : HeightOneSpectrum (𝓞 F)) (d : ℕ) (h : χ.localEulerFactor v d ≠ 0) :
      v.asIdeal.absNorm ^ Nat.log v.asIdeal.absNorm d = d := by
    by_contra hk
    apply h
    rw [hE, ArithmeticFunction.ofPowerSeries_apply (hN v), Function.extend_apply']
    · rfl
    rintro ⟨k, rfl⟩
    exact hk (by rw [Nat.log_pow (hN v)])
  let U (S : Finset (HeightOneSpectrum (𝓞 F))) (n : ℕ) : Finset (Ideal (𝓞 F)) :=
    (Ring.HasFiniteQuotients.finite_absNorm_eq n).toFinset.filter fun I ↦ ∀ v, v.asIdeal ∣ I → v ∈ S
  have hmemU {S : Finset (HeightOneSpectrum (𝓞 F))} {n : ℕ} {I : Ideal (𝓞 F)} :
      I ∈ U S n ↔ I.absNorm = n ∧ ∀ v, v.asIdeal ∣ I → v ∈ S := by
    simp [U]
  have key (S : Finset (HeightOneSpectrum (𝓞 F))) (n : ℕ) :
      (∏ v ∈ S, χ.localEulerFactor v) n = ∑ I ∈ U S n, c I := by
    induction S using Finset.induction_on generalizing n with
    | empty =>
      have hU (I : Ideal (𝓞 F)) (hI : I ∈ U ∅ n) : I = ⊥ ∨ I = ⊤ := by
        by_contra! h
        obtain ⟨J, hJ, hIJ⟩ := I.exists_le_maximal h.2
        have hv := (hmemU.mp hI).2 ⟨J, hJ.isPrime, fun hJ0 ↦ h.1 (le_bot_iff.mp (hJ0 ▸ hIJ))⟩
          (Ideal.dvd_iff_le.mpr hIJ)
        simp at hv
      rw [Finset.prod_empty]
      by_cases hn : n = 1
      · subst hn
        rw [ArithmeticFunction.one_one,
          Finset.sum_eq_single_of_mem ⊤ (hmemU.mpr ⟨Ideal.absNorm_top, by
          intro v hv
          exact absurd (Ideal.dvd_iff_le.mp hv) (fun h ↦ v.isPrime.ne_top (top_le_iff.mp h))⟩)]
        · rw [← Ideal.one_eq_top, map_one]
        · intro I hI hIt
          rcases hU I hI with rfl | rfl
          · rw [← Ideal.zero_eq_bot, _root_.map_zero]
          · exact absurd rfl hIt
      · rw [ArithmeticFunction.one_apply_ne hn]
        refine (Finset.sum_eq_zero fun I hI ↦ ?_).symm
        rcases hU I hI with rfl | rfl
        · rw [← Ideal.zero_eq_bot, _root_.map_zero]
        · exact absurd ((hmemU.mp hI).1.symm.trans Ideal.absNorm_top) hn
    | insert w S hw ih =>
      have hw0 : w.asIdeal ≠ 0 := w.prime.ne_zero
      rw [Finset.prod_insert hw, ArithmeticFunction.mul_apply]
      simp_rw [ih, Finset.mul_sum]
      rw [Finset.sum_sigma']
      refine Finset.sum_bij_ne_zero
        (fun p _ _ ↦ w.asIdeal ^ Nat.log w.asIdeal.absNorm p.1.1 * p.2) ?_ ?_ ?_ ?_
      · rintro ⟨⟨d, e⟩, J⟩ hp hne
        rw [Finset.mem_sigma, Nat.mem_divisorsAntidiagonal, hmemU] at hp
        have hk := hEne w d (left_ne_zero_of_mul hne)
        refine hmemU.mpr ⟨?_, fun v hv ↦ ?_⟩
        · rw [map_mul, map_pow, hk, hp.2.1, hp.1.1]
        · rcases v.prime.dvd_or_dvd hv with h | h
          · exact Finset.mem_insert.mpr (Or.inl (hd v w (v.prime.dvd_of_dvd_pow h)))
          · exact Finset.mem_insert_of_mem (hp.2.2 v h)
      · have hmult (k : ℕ) (J : Ideal (𝓞 F)) (hJ : J ≠ 0) (hwJ : ¬ w.asIdeal ∣ J) :
            multiplicity w.asIdeal (w.asIdeal ^ k * J) = k := by
          rw [multiplicity_mul w.prime (FiniteMultiplicity.of_prime_left w.prime
            (mul_ne_zero (pow_ne_zero _ hw0) hJ)), multiplicity_pow_self_of_prime w.prime,
            multiplicity_eq_zero_of_not_dvd hwJ, add_zero]
        rintro ⟨⟨d, e⟩, J⟩ hp hne ⟨⟨d', e'⟩, J'⟩ hp' hne' heq
        rw [Finset.mem_sigma, Nat.mem_divisorsAntidiagonal, hmemU] at hp hp'
        have hJ : J ≠ 0 := fun h ↦ hne (by rw [h, _root_.map_zero, mul_zero])
        have hJ' : J' ≠ 0 := fun h ↦ hne' (by rw [h, _root_.map_zero, mul_zero])
        have hwJ : ¬ w.asIdeal ∣ J := fun h ↦ hw (hp.2.2 w h)
        have hwJ' : ¬ w.asIdeal ∣ J' := fun h ↦ hw (hp'.2.2 w h)
        dsimp only at heq
        have hkk := (hmult _ J hJ hwJ).symm.trans ((congrArg _ heq).trans (hmult _ J' hJ' hwJ'))
        have hJJ : J = J' := mul_left_cancel₀ (pow_ne_zero _ hw0) (hkk ▸ heq)
        have hdd : d = d' := by
          rw [← hEne w d (left_ne_zero_of_mul hne), ← hEne w d' (left_ne_zero_of_mul hne'), hkk]
        have hee : e = e' := hp.2.1.symm.trans (hJJ ▸ hp'.2.1)
        subst hJJ hdd hee
        rfl
      · intro I hI hcI
        rw [hmemU] at hI
        have hI0 : I ≠ 0 := fun h ↦ hcI (by rw [h, _root_.map_zero])
        obtain ⟨k, J, hwJ, rfl⟩ := WfDvdMonoid.max_power_factor hI0 w.irreducible
        refine ⟨⟨(w.asIdeal.absNorm ^ k, J.absNorm), J⟩, ?_, ?_, ?_⟩
        · rw [Finset.mem_sigma, Nat.mem_divisorsAntidiagonal, hmemU]
          refine ⟨⟨by rw [← hI.1, map_mul, map_pow], ?_⟩, rfl, fun v hv ↦ ?_⟩
          · rw [← hI.1, Ne, Ideal.absNorm_eq_zero_iff, ← Ideal.zero_eq_bot]
            exact hI0
          · rcases Finset.mem_insert.mp (hI.2 v (dvd_mul_of_dvd_right hv _)) with rfl | h
            · exact absurd hv hwJ
            · exact h
        · rw [map_mul, map_pow, hcPrime] at hcI
          rwa [hEpow]
        · dsimp only
          rw [Nat.log_pow (hN w)]
      · rintro ⟨⟨d, e⟩, J⟩ hp hne
        dsimp only
        rw [map_mul, map_pow, hcPrime, ← hEpow, hEne w d (left_ne_zero_of_mul hne)]
  rcases eq_or_ne m 0 with rfl | hm
  · rw [ArithmeticFunction.map_zero, heckeNormCoefficient]
    have : IsEmpty {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ (I.absNorm : ℝ) = ((0 : ℕ) : ℝ)} :=
      ⟨fun I ↦ I.2.1 (Ideal.absNorm_eq_zero_iff.mp (by exact_mod_cast I.2.2))⟩
    exact finsum_of_isEmpty _
  obtain ⟨S, hS, hSm⟩ := ((heckeLocalEulerFactor_eventually_prod_eq χ m).and
    (eventually_ge_atTop ((Ring.HasFiniteQuotients.finite_absNorm_le m).preimage
      HeightOneSpectrum.asIdeal_injective.injOn).toFinset)).exists
  rw [← hS, key S m]
  have hset : {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (I.absNorm : ℝ) = m} = ↑(U S m) := by
    ext I
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, hmemU]
    constructor
    · rintro ⟨-, hIm⟩
      have hIm' : I.absNorm = m := by exact_mod_cast hIm
      refine ⟨hIm', fun v hv ↦ hSm ?_⟩
      rw [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_ofPred_eq, ← hIm']
      exact Nat.le_of_dvd (Nat.pos_of_ne_zero (hIm' ▸ hm)) (map_dvd Ideal.absNorm hv)
    · rintro ⟨hIm, -⟩
      exact ⟨fun h ↦ hm (by rw [← hIm, h, Ideal.absNorm_bot]), by exact_mod_cast hIm⟩
  change ∑ᶠ I : ↥{I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (I.absNorm : ℝ) = m}, value I = _
  rw [hset, finsum_set_coe_eq_finsum_mem, finsum_mem_coe_finset]
  rfl

/-- Paper: Equation (B.6.1.5), p. 637. Grouping the terms by their integral
norm gives the absolutely convergent Dirichlet series with coefficients `aₘ`. -/
theorem finiteHeckeL_hasSum_normCoefficients (χ : U[F]) (s : halfPlane) :
    LSeriesHasSum (fun m : ℕ ↦ heckeNormCoefficient (ideleClassNormTwist χ 0) (m : ℝ))
      (s : ℂ) (finiteHeckeL χ s) := by
  let normIndex (I : {I : Ideal (𝓞 F) // I ≠ ⊥}) : ℕ := I.val.absNorm
  let value := heckeIdealValue (ideleClassNormTwist χ 0)
  have hs : (s : ℂ) ≠ 0 := by
    intro h
    have hr : 1 < (s : ℂ).re := s.property
    norm_num [h] at hr
  refine ((finiteHeckeL_hasSum_ideals χ s).tsum_fiberwise normIndex).congr_fun ?_
  intro n
  symm
  rw [LSeries.term_of_ne_zero' hs]
  let normFiber : Set (Ideal (𝓞 F)) := {I | I ≠ ⊥ ∧ (I.absNorm : ℝ) = (n : ℝ)}
  let e : (normIndex ⁻¹' ({n} : Set ℕ) : Set {I : Ideal (𝓞 F) // I ≠ ⊥}) ≃ normFiber :=
    { toFun := fun I ↦ ⟨I.val.val, I.val.property,
        by exact_mod_cast (show I.val.val.absNorm = n from I.property)⟩
      invFun := fun I ↦ ⟨⟨I.val, I.property.1⟩, by
        change I.val.absNorm = n
        exact_mod_cast I.property.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have hnorm (I : normFiber) : I.val.absNorm = n := by exact_mod_cast I.property.2
  rw [← e.symm.tsum_eq]
  change (∑' I : normFiber, value I.val / (I.val.absNorm : ℂ) ^ (s : ℂ)) =
    heckeNormCoefficient (ideleClassNormTwist χ 0) (n : ℝ) / (n : ℂ) ^ (s : ℂ)
  let : Finite normFiber :=
    ((Ring.HasFiniteQuotients.finite_absNorm_eq n).subset
      (show normFiber ⊆ {I | I.absNorm = n} from fun I hI ↦ hnorm ⟨I, hI⟩)).to_subtype
  simp_rw [hnorm, tsum_div_const, tsum_eq_finsum (Set.toFinite _)]
  rfl

/-- Paper: Equation (B.6.1.6), p. 637. For each positive `ε`, the summatory
function is bounded by a constant times `x^(1 + ε)`, uniformly in unitary characters. -/
theorem heckeIdealSummatory_bound (F : Type*) [Field F] [NumberField F] {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop, ∀ χ : U[F],
      ‖heckeIdealSummatory (ideleClassNormTwist χ 0) x‖ ≤ C * x ^ (1 + ε) := by
  classical
  have hvalue (χ : U[F]) {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) :
      ‖heckeIdealValue (ideleClassNormTwist χ 0) I‖ ≤ 1 := by
    rw [heckeIdealValue, ite_eq_right hI]
    refine finprod_induction (fun z : ℂ ↦ ‖z‖ ≤ 1) (by simp) (fun _ w hz hw ↦ ?_) (fun v ↦ ?_)
    · rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg w) hz).trans hw
    · rw [norm_pow]
      apply pow_le_one₀ (norm_nonneg _)
      split_ifs <;> simp [norm_ideleClassNormTwist_zero_localValue]
  obtain ⟨B, hB⟩ := (NumberField.Ideal.tendsto_norm_le_div_atTop F).isBoundedUnder_le.eventually_le
  have hC : 0 < max 1 B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨max 1 B, hC, ?_⟩
  filter_upwards [hB, eventually_ge_atTop (1 : ℝ)] with x hcount hx
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  let ideals := {I : Ideal (𝓞 F) | (I.absNorm : ℝ) ≤ x}
  let nonzeroIdeals := {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (I.absNorm : ℝ) ≤ x}
  have hfinite : ideals.Finite := by
    simp only [ideals, ← Nat.le_floor_iff hxpos.le]
    exact Ring.HasFiniteQuotients.finite_absNorm_le _
  have hsub : nonzeroIdeals ⊆ ideals := fun _ hI ↦ hI.2
  let : Fintype nonzeroIdeals := (hfinite.subset hsub).fintype
  intro χ
  calc
    ‖heckeIdealSummatory (ideleClassNormTwist χ 0) x‖ ≤ ∑ _ : nonzeroIdeals, (1 : ℝ) := by
      change ‖∑ᶠ I : nonzeroIdeals, heckeIdealValue (ideleClassNormTwist χ 0) I.1‖ ≤ _
      rw [finsum_eq_sum_of_fintype]
      exact norm_sum_le_of_le _ fun I _ ↦ hvalue χ I.2.1
    _ = (nonzeroIdeals.ncard : ℝ) := by simp
    _ ≤ (ideals.ncard : ℝ) := by exact_mod_cast Set.ncard_le_ncard hsub hfinite
    _ ≤ max 1 B * x := (div_le_iff₀ hxpos).mp (hcount.trans (le_max_right 1 B))
    _ ≤ max 1 B * x ^ (1 + ε) := mul_le_mul_of_nonneg_left
      (Real.self_le_rpow_of_one_le hx (le_add_of_nonneg_right hε.le)) hC.le

-- TODO(paper-gap): Equation (B.6.1.7) multiplies the norm-one class volume by an
-- extra inverse square root of the discriminant under the normalization in §A.3.

/-- A unitary character trivial on the norm-one subgroup is a unique imaginary power of
the norm. -/
private theorem heckeIdealSummatory_tendsto_of_trivial_on_normOne_existsUnique (χ : U[F])
    (hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1) :
    ∃! t : ℝ, ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * (t : ℂ)) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ⟨σ, hσ, hnorm⟩, _⟩ := ideleGroup_quotient.{_, 0} F
  let c : NNRealˣ →ₜ* ℂ := (ideleClassNormTwist χ 0).comp ⟨σ, hσ⟩
  have hunit (g : IdeleClassGroup (𝓞 F) F) : ideleClassNormTwist χ 0 g = (χ g : ℂ) := by
    change (χ g : ℂ) * _ ^ (0 : ℂ) = _
    simp
  obtain ⟨z, ⟨hzre, hz⟩, huniq⟩ :=
    existsUnique_unitaryComplexPower c (fun u ↦ by
      change ‖ideleClassNormTwist χ 0 (σ u)‖ = 1
      rw [hunit, Circle.norm_coe])
  have hparam : -Complex.I * ((-z.im : ℝ) : ℂ) = z := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, hzre]
  refine ⟨-z.im, ?_, ?_⟩
  · change ideleClassNormTwist χ 0 =
      ideleClassNormTwist (1 : U[F]) (-Complex.I * ((-z.im : ℝ) : ℂ))
    rw [hparam]
    ext1 g
    let u := ideleClassNorm F g
    have hk : g / σ u ∈ (ideleClassNorm F).ker := MonoidHom.mem_ker.mpr (by
      rw [map_div, hnorm u, div_self'])
    have hkχ : χ (g / σ u) = 1 :=
      DFunLike.congr_fun hχ (⟨g / σ u, hk⟩ : (ideleClassNorm F).ker)
    have he : ideleClassNormTwist χ 0 (g / σ u) = 1 := by rw [hunit, hkχ, Circle.coe_one]
    calc
      ideleClassNormTwist χ 0 g = ideleClassNormTwist χ 0 (g / σ u) * c u := by
        change ideleClassNormTwist χ 0 g =
          ideleClassNormTwist χ 0 (g / σ u) * ideleClassNormTwist χ 0 (σ u)
        rw [← map_mul, div_mul_cancel]
      _ = ideleClassNormTwist (1 : U[F]) z g := by
        change ideleClassNormTwist χ 0 (g / σ u) * c u =
          1 * (((ideleClassNorm F g : NNReal) : ℝ) : ℂ) ^ z
        rw [he, hz u]
  · intro t ht
    have he : -Complex.I * (t : ℂ) = z := huniq _ ⟨by simp [Complex.mul_re], fun u ↦ by
      change ideleClassNormTwist χ 0 (σ u) = _
      rw [ht]
      change (1 : ℂ) * (((ideleClassNorm F (σ u) : NNReal) : ℝ) : ℂ) ^ (-Complex.I * (t : ℂ)) = _
      rw [one_mul, hnorm u]⟩
    apply neg_eq_iff_eq_neg.mp
    simpa [Complex.mul_im] using congrArg Complex.im he

/-- Undoing the imaginary norm twist of such a character gives the trivial character. -/
private theorem heckeIdealSummatory_tendsto_of_trivial_on_normOne_eq_one (χ : U[F]) (t₀ : ℝ)
    (ht : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀))
    (g : IdeleClassGroup (𝓞 F) F) : ideleClassNormTwist χ (Complex.I * t₀) g = 1 := by
  have h := DFunLike.congr_fun ht g
  change (χ g : ℂ) * (((ideleClassNorm F g : NNReal) : ℝ) : ℂ) ^ (0 : ℂ) =
    1 * (((ideleClassNorm F g : NNReal) : ℝ) : ℂ) ^ (-Complex.I * t₀) at h
  change (χ g : ℂ) * (((ideleClassNorm F g : NNReal) : ℝ) : ℂ) ^ (Complex.I * t₀) = 1
  have hne : (((ideleClassNorm F g : NNReal) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ideleClassNorm F g).ne_zero
  rw [Complex.cpow_zero, mul_one, one_mul] at h
  rw [h, ← Complex.cpow_add _ _ hne, neg_mul, neg_add_cancel, Complex.cpow_zero]

/-- A character that is identically one has value one at every nonzero ideal. -/
private theorem heckeIdealSummatory_tendsto_of_trivial_on_normOne_value (χ : 𝒳[F])
    (hχ : ∀ g, χ g = 1) {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) : heckeIdealValue χ I = 1 := by
  classical
  have hres : ∀ v : HeightOneSpectrum (𝓞 F), ∀ x : v.adicCompletion F, x ≠ 0 →
      χ.restrict v x = 1 := fun v x hx ↦ by
    have hu : IsUnit x := isUnit_iff_ne_zero.mpr hx
    rw [← hu.unit_spec, HeckeCharacter.restrict_apply]
    simp [hχ, hx]
  have hun : ∀ v : HeightOneSpectrum (𝓞 F), χ.IsUnramifiedAt v := fun v ↦
    HeckeCharacter.isUnramifiedAt_iff.mpr fun x ↦ hres v _ (by simp)
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F), χ.localValue v = 1 := fun v ↦ by
    rw [HeckeCharacter.localValue]
    apply hres
    exact (Valued.v.exists_isUniformizer_of_isCyclic_of_nontrivial).choose_spec.ne_zero
  unfold heckeIdealValue
  rw [ite_eq_right hI]
  exact finprod_eq_one_of_forall_eq_one fun v ↦ by simp [hun v, hloc v]

/-- Paper: Lemma B.6.1.2(1), p. 637. For a unitary character trivial on
norm-one classes, undoing its imaginary norm twist gives the ideal-counting
limit at the residue of Dedekind zeta.
Deviation: Uses Mathlib's `dedekindZeta_residue`, the class volume in §A.3,
with the extra printed inverse square root of the discriminant removed. -/
theorem heckeIdealSummatory_tendsto_of_trivial_on_normOne (χ : U[F])
    (hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1) :
    (∃! t₀ : ℝ, ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀)) ∧
      ∀ t₀ : ℝ, ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀) →
        Tendsto (fun x : ℝ ↦ heckeIdealSummatory (ideleClassNormTwist χ (Complex.I * t₀)) x / x)
          atTop (𝓝 (dedekindZeta_residue F : ℂ)) := by
  refine ⟨heckeIdealSummatory_tendsto_of_trivial_on_normOne_existsUnique χ hχ, fun t₀ ht ↦ ?_⟩
  have hval {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) :
      heckeIdealValue (ideleClassNormTwist χ (Complex.I * t₀)) I = 1 :=
    heckeIdealSummatory_tendsto_of_trivial_on_normOne_value _
      (heckeIdealSummatory_tendsto_of_trivial_on_normOne_eq_one χ t₀ ht) hI
  have hlim := (Complex.continuous_ofReal.tendsto _).comp (Ideal.tendsto_norm_le_div_atTop₀ F)
  rw [← dedekindZeta_residue_def] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with x hx
  rw [Function.comp_apply, Complex.ofReal_div, Complex.ofReal_natCast]
  congr 1
  let e : {I : nonZeroDivisors (Ideal (𝓞 F)) // Ideal.absNorm (I : Ideal (𝓞 F)) ≤ x} ≃
      {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ (I.absNorm : ℝ) ≤ x} :=
    { toFun := fun I ↦ ⟨I.1.1, by simpa using mem_nonZeroDivisors_iff_ne_zero.mp I.1.2, I.2⟩
      invFun := fun I ↦ ⟨⟨I.1, mem_nonZeroDivisors_iff_ne_zero.mpr (by simpa using I.2.1)⟩, I.2.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have hfin : {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (I.absNorm : ℝ) ≤ x}.Finite :=
    (Ring.HasFiniteQuotients.finite_absNorm_le (S := 𝓞 F) ⌊x⌋₊).subset
      fun I hI ↦ Nat.le_floor hI.2
  have : Finite {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ (I.absNorm : ℝ) ≤ x} := hfin.to_subtype
  have : Fintype {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ (I.absNorm : ℝ) ≤ x} := Fintype.ofFinite _
  unfold heckeIdealSummatory
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, finsum_eq_sum_of_fintype, Finset.sum_congr rfl fun I _ ↦ hval I.2.1, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one]

/-- Conjugating the coefficients of a Dirichlet series conjugates its sum at the
conjugate point. -/
private theorem heckeIdealSummatory_tendsto_zero_of_nontrivial_on_normOne_conj (f : ℕ → ℂ)
    (s a : ℂ) (h : LSeriesHasSum f ((starRingEnd ℂ) s) a) :
    LSeriesHasSum (fun n ↦ (starRingEnd ℂ) (f n)) s ((starRingEnd ℂ) a) := by
  have h' := h.star
  unfold LSeriesHasSum
  convert h' using 1
  · funext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    change _ = (starRingEnd ℂ) _
    rw [map_div₀, ← Complex.conj_cpow _ _ (by rw [Complex.natCast_arg]; positivity),
      Complex.conj_natCast]
  · rfl

/-- The summatory function groups by integral norm. -/
private theorem heckeIdealSummatory_tendsto_zero_of_nontrivial_on_normOne_sum (χ : 𝒳[F])
    (x : ℝ) (hx : 0 ≤ x) :
    heckeIdealSummatory χ x = ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, heckeNormCoefficient χ n := by
  classical
  have hfin : {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (I.absNorm : ℝ) ≤ x}.Finite :=
    (Ring.HasFiniteQuotients.finite_absNorm_le (S := 𝓞 F) ⌊x⌋₊).subset
      fun I hI ↦ Nat.le_floor hI.2
  let T := hfin.toFinset
  have hfib (n : ℕ) (hn : n ∈ Finset.Icc 0 ⌊x⌋₊) :
      heckeNormCoefficient χ n = ∑ I ∈ T with I.absNorm = n, heckeIdealValue χ I := by
    have hset : {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (I.absNorm : ℝ) = n} =
        ↑(T.filter fun I ↦ I.absNorm = n) := by
      ext I
      simp only [Set.mem_ofPred_eq, Finset.coe_filter, T, Set.Finite.mem_toFinset]
      constructor
      · rintro ⟨h0, h1⟩
        have h1' : I.absNorm = n := by exact_mod_cast h1
        refine ⟨⟨h0, ?_⟩, h1'⟩
        rw [h1]
        exact (Nat.le_floor_iff hx).mp (Finset.mem_Icc.mp hn).2
      · rintro ⟨⟨h0, -⟩, h1⟩
        exact ⟨h0, by exact_mod_cast h1⟩
    unfold heckeNormCoefficient
    change ∑ᶠ I : ↥{I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (I.absNorm : ℝ) = n}, heckeIdealValue χ I = _
    rw [hset, finsum_set_coe_eq_finsum_mem, finsum_mem_coe_finset]
  unfold heckeIdealSummatory
  change ∑ᶠ I : ↥{I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (I.absNorm : ℝ) ≤ x}, heckeIdealValue χ I = _
  rw [finsum_set_coe_eq_finsum_mem, finsum_mem_eq_finite_toFinset_sum _ hfin,
    Finset.sum_congr rfl hfib]
  refine (Finset.sum_fiberwise_of_maps_to (fun I hI ↦ ?_) _).symm
  simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hI
  exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, Nat.le_floor hI.2⟩


/-- The norm-one-twisted trivial character has coefficient equal to the number of
nonzero ideals of the given norm. -/
private theorem heckeIdealSummatory_tendsto_zero_of_nontrivial_on_normOne_one (n : ℕ) :
    heckeNormCoefficient (ideleClassNormTwist (1 : U[F]) 0) n =
      ((Nat.card {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ (I.absNorm : ℝ) = n} : ℝ) : ℂ) := by
  classical
  have hone (g : IdeleClassGroup (𝓞 F) F) : ideleClassNormTwist (1 : U[F]) 0 g = 1 := by
    change ((1 : U[F]) g : ℂ) * _ ^ (0 : ℂ) = 1
    simp
  have : Finite {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ (I.absNorm : ℝ) = n} :=
    ((Ring.HasFiniteQuotients.finite_absNorm_eq (S := 𝓞 F) n).subset
      (show {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (I.absNorm : ℝ) = n} ⊆ {I | I.absNorm = n} from
        fun I hI ↦ by exact_mod_cast hI.2)).to_subtype
  have : Fintype {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ (I.absNorm : ℝ) = n} := Fintype.ofFinite _
  unfold heckeNormCoefficient
  rw [finsum_eq_sum_of_fintype, Finset.sum_congr rfl fun I _ ↦
    heckeIdealSummatory_tendsto_of_trivial_on_normOne_value _ hone I.2.1, Finset.sum_const,
    Finset.card_univ, Nat.card_eq_fintype_card, nsmul_eq_mul, mul_one]
  norm_cast

/-- Each coefficient of a unitary character is bounded by the number of ideals of that norm. -/
private theorem heckeIdealSummatory_tendsto_zero_of_nontrivial_on_normOne_norm_le (χ : U[F])
    (n : ℕ) : ‖heckeNormCoefficient (ideleClassNormTwist χ 0) n‖ ≤
      (Nat.card {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ (I.absNorm : ℝ) = n} : ℝ) := by
  classical
  have hvalue {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) :
      ‖heckeIdealValue (ideleClassNormTwist χ 0) I‖ ≤ 1 := by
    rw [heckeIdealValue, ite_eq_right hI]
    refine finprod_induction (fun z : ℂ ↦ ‖z‖ ≤ 1) (by simp) (fun _ w hz hw ↦ ?_) (fun v ↦ ?_)
    · rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg w) hz).trans hw
    · rw [norm_pow]
      apply pow_le_one₀ (norm_nonneg _)
      split_ifs <;> simp [norm_ideleClassNormTwist_zero_localValue]
  have : Finite {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ (I.absNorm : ℝ) = n} :=
    ((Ring.HasFiniteQuotients.finite_absNorm_eq (S := 𝓞 F) n).subset
      (show {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (I.absNorm : ℝ) = n} ⊆ {I | I.absNorm = n} from
        fun I hI ↦ by exact_mod_cast hI.2)).to_subtype
  have : Fintype {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ (I.absNorm : ℝ) = n} := Fintype.ofFinite _
  unfold heckeNormCoefficient
  rw [finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card]
  refine (norm_sum_le_of_le _ fun I _ ↦ hvalue I.2.1).trans ?_
  simp

/-- The ideal counts have a linear summatory bound. -/
private theorem heckeIdealSummatory_tendsto_zero_of_nontrivial_on_normOne_bound :
    ∃ C : ℝ, ∀ n : ℕ, ∑ i ∈ Finset.range n,
      (Nat.card {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ (I.absNorm : ℝ) = i} : ℝ) ≤ C * n := by
  set N : ℕ → ℝ := fun i ↦ (Nat.card {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ (I.absNorm : ℝ) = i} : ℝ)
    with hN
  set S : ℕ → ℝ := fun n ↦ ∑ i ∈ Finset.Icc 0 n, N i with hS
  have hN0 (i : ℕ) : 0 ≤ N i := Nat.cast_nonneg _
  have h1 : (1 : U[F]).toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1 := by
    ext; rfl
  have hlim := (heckeIdealSummatory_tendsto_of_trivial_on_normOne (1 : U[F]) h1).2 0 (by simp)
  have e : Complex.I * ((0 : ℝ) : ℂ) = 0 := by simp
  rw [e] at hlim
  have hR : Tendsto (fun n : ℕ ↦ S n / n) atTop (𝓝 (dedekindZeta_residue F)) := by
    have := ((Complex.continuous_re.tendsto _).comp hlim).comp tendsto_natCast_atTop_atTop
    refine this.congr fun n ↦ ?_
    simp only [Function.comp_apply]
    rw [heckeIdealSummatory_tendsto_zero_of_nontrivial_on_normOne_sum _ _ (Nat.cast_nonneg n),
      Nat.floor_natCast]
    simp_rw [heckeIdealSummatory_tendsto_zero_of_nontrivial_on_normOne_one]
    rw [← Complex.ofReal_sum, ← Complex.ofReal_div, Complex.ofReal_re]
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1
    (hR.eventually (gt_mem_nhds (lt_add_one (dedekindZeta_residue F))))
  have hres := dedekindZeta_residue_pos F
  have hSmono {m n : ℕ} (h : m ≤ n) : S m ≤ S n :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl h)
      fun i _ _ ↦ hN0 i
  have hS0 (n : ℕ) : 0 ≤ S n := Finset.sum_nonneg fun i _ ↦ hN0 i
  refine ⟨dedekindZeta_residue F + 1 + S n₀, fun n ↦ ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hle : ∑ i ∈ Finset.range n, N i ≤ S n :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (fun i hi ↦ Finset.mem_Icc.mpr ⟨Nat.zero_le _, (Finset.mem_range.mp hi).le⟩)
      fun i _ _ ↦ hN0 i
  refine hle.trans ?_
  rcases le_or_gt n₀ n with h | h
  · have := hn₀ n h
    rw [div_lt_iff₀ (by linarith)] at this
    nlinarith [hS0 n₀]
  · have := hSmono h.le
    nlinarith [hS0 n₀]

/-- On the right half-plane the ideal-count Dirichlet series has the sum given by the
finite Dedekind zeta function. -/
private theorem heckeIdealSummatory_tendsto_zero_of_nontrivial_on_normOne_hasSum_one
    (s : ℂ) (hs : 1 < s.re) :
    LSeriesHasSum (fun n : ℕ ↦
      ((Nat.card {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ (I.absNorm : ℝ) = n} : ℝ) : ℂ)) s
      (finiteHeckeL (1 : U[F]) ⟨s, hs⟩) := by
  have := finiteHeckeL_hasSum_normCoefficients (1 : U[F]) ⟨s, hs⟩
  simp_rw [heckeIdealSummatory_tendsto_zero_of_nontrivial_on_normOne_one] at this
  exact this

/-- The ideal-count Dirichlet series minus a real multiple of `1 / (s - 1)` extends
continuously to the closed half-plane `1 ≤ re s`. -/
private theorem heckeIdealSummatory_tendsto_zero_of_nontrivial_on_normOne_zeta :
    ∃ c : ℝ, ∃ G : ℂ → ℂ, ContinuousOn G {s | 1 ≤ s.re} ∧
      EqOn G (fun s ↦ LSeries (fun n : ℕ ↦
        ((Nat.card {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ (I.absNorm : ℝ) = n} : ℝ) : ℂ)) s -
          c / (s - 1)) {s | 1 < s.re} := by
  set a : ℕ → ℂ := fun n ↦
    ((Nat.card {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ (I.absNorm : ℝ) = n} : ℝ) : ℂ) with ha
  obtain ⟨Λ, hΛ, hEq⟩ := completedHeckeL_exists_continuation (1 : U[F])
  have h1 : (1 : U[F]).toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1 := by
    ext; rfl
  obtain ⟨t, ⟨ht, -, hord, han⟩, -⟩ :=
    completedHeckeL_continuation_simplePoles (1 : U[F]) Λ hΛ hEq h1
  have ht0 : t = 0 := by
    have := congrArg Complex.im (trivial_normTwist_injective (F := F) ht)
    simpa using this.symm
  subst ht0
  have hord' : meromorphicOrderAt Λ 1 = -1 := by simpa using hord
  let γ : ℂ → ℂ := fun s ↦ (heckeGammaFactor (1 : U[F]) s)⁻¹
  have hγ : Differentiable ℂ γ := differentiable_inv_heckeGammaFactor _
  have hLS (s : ℂ) (hs : 1 < s.re) : γ s * Λ s = LSeries a s := by
    have hne := heckeGammaFactor_ne_zero_of_re_pos (1 : U[F]) (s := s) (by linarith)
    rw [hEq ⟨s, hs⟩,
      (heckeIdealSummatory_tendsto_zero_of_nontrivial_on_normOne_hasSum_one s hs).LSeries_eq]
    change γ s * (heckeGammaFactor (1 : U[F]) s * finiteHeckeL (1 : U[F]) ⟨s, hs⟩) = _
    rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  have hreal (s : ℂ) (hs : 1 < s.re) (hsr : s.im = 0) : (LSeries a s).im = 0 := by
    have hc : (starRingEnd ℂ) s = s := Complex.conj_eq_iff_im.mpr hsr
    have hsum (s' : ℂ) (hs' : 1 < s'.re) : LSeriesHasSum a s' (LSeries a s') :=
      (heckeIdealSummatory_tendsto_zero_of_nontrivial_on_normOne_hasSum_one (F := F) s'
        hs').LSeriesSummable.LSeriesHasSum
    have h₂ := heckeIdealSummatory_tendsto_zero_of_nontrivial_on_normOne_conj a s _
      (hsum _ (by rwa [Complex.conj_re]))
    have hfa : (fun n ↦ (starRingEnd ℂ) (a n)) = a := funext fun n ↦ Complex.conj_ofReal _
    rw [hc, hfa] at h₂
    rw [← Complex.conj_eq_iff_im]
    exact HasSum.unique h₂ (hsum s hs)
  obtain ⟨g, hg, -, hgeq⟩ :=
    (meromorphicOrderAt_eq_int_iff (hΛ (mem_univ 1)).meromorphicAt).1 hord'
  let h : ℂ → ℂ := fun s ↦ γ s * g s
  have hh : DifferentiableAt ℂ h 1 := (hγ 1).mul hg.differentiableAt
  have hnear : ∀ᶠ z in 𝓝[≠] (1 : ℂ), γ z * Λ z = (z - 1)⁻¹ * h z := by
    filter_upwards [hgeq] with z hz
    simp only [zpow_neg, zpow_one, smul_eq_mul] at hz
    rw [hz]
    ring
  have hh1 : (h 1).im = 0 := by
    have hto : Tendsto (fun σ : ℝ ↦ (σ : ℂ)) (𝓝[>] 1) (𝓝[≠] (1 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · exact (Complex.continuous_ofReal.tendsto' 1 1 (by simp)).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with σ hσ
        exact fun h' ↦ (ne_of_gt (Set.mem_Ioi.mp hσ))
          (by exact_mod_cast (Set.mem_singleton_iff.mp h'))
    have hlim : Tendsto (fun σ : ℝ ↦ (h σ).im) (𝓝[>] 1) (𝓝 (h 1).im) :=
      (Complex.continuous_im.tendsto _).comp
        ((hh.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).comp hto)
    refine tendsto_nhds_unique hlim (tendsto_const_nhds.congr' ?_)
    filter_upwards [hto.eventually hnear, self_mem_nhdsWithin] with σ hσ hσ1
    have hσ1' : (1 : ℝ) < σ := hσ1
    have hre : 1 < (σ : ℂ).re := by simpa using hσ1'
    have hne : (σ : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hσ1'.ne')
    have : h σ = ((σ : ℂ) - 1) * LSeries a σ := by
      rw [← hLS _ hre, hσ, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
    rw [this, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.im_ofReal_mul,
      hreal _ hre (by simp), mul_zero]
  set c : ℝ := (h 1).re with hc
  have hcc : (c : ℂ) = h 1 := Complex.ext (by simp [hc]) (by simp [hh1])
  let G : ℂ → ℂ := Function.update (fun s ↦ γ s * Λ s - c / (s - 1)) 1 (deriv h 1)
  refine ⟨c, G, fun s hs ↦ ?_, fun s hs ↦ ?_⟩
  · apply ContinuousAt.continuousWithinAt
    by_cases hs1 : s = 1
    · subst hs1
      have hev : G =ᶠ[𝓝 1] dslope h 1 := by
        filter_upwards [eventually_nhdsWithin_iff.mp hnear] with z hz
        by_cases hz1 : z = 1
        · subst hz1
          simp only [G, Function.update_self, dslope_same]
        · have hne : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
          simp only [G, Function.update_of_ne hz1]
          rw [hz hz1, dslope_of_ne _ hz1, slope_def_field, hcc]
          field_simp
      exact (continuousAt_dslope_same.mpr hh).congr hev.symm
    · have hs0 : s ≠ 0 := by
        rintro rfl
        norm_num at hs
      have hΛs : ContinuousAt Λ s := (han s (by simp [hs0, hs1])).continuousAt
      have hcont : ContinuousAt (fun s ↦ γ s * Λ s - c / (s - 1)) s :=
        ((hγ s).continuousAt.mul hΛs).sub
          (continuousAt_const.div (continuousAt_id.sub continuousAt_const)
            (sub_ne_zero.mpr hs1))
      refine hcont.congr ?_
      filter_upwards [eventually_ne_nhds hs1] with z hz
      simp [G, Function.update_of_ne hz]
  · have hs1 : s ≠ 1 := by
      rintro rfl
      simp at hs
    simp only [G, Function.update_of_ne hs1]
    rw [hLS s hs]

/-- If the character is nontrivial on norm-one classes, the Dirichlet series of its
coefficients has an entire continuation. -/
private theorem heckeIdealSummatory_tendsto_zero_of_nontrivial_on_normOne_entire (χ : U[F])
    (hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1) :
    ∃ M : ℂ → ℂ, Differentiable ℂ M ∧ ∀ s : ℂ, 1 < s.re →
      LSeriesHasSum (fun n : ℕ ↦ heckeNormCoefficient (ideleClassNormTwist χ 0) n) s (M s) := by
  obtain ⟨Λ, hΛ, hEq⟩ := completedHeckeL_exists_continuation χ
  have hd := completedHeckeL_continuation_entire χ Λ hΛ hEq hχ
  refine ⟨fun s ↦ (heckeGammaFactor χ s)⁻¹ * Λ s,
    (differentiable_inv_heckeGammaFactor χ).mul hd, fun s hs ↦ ?_⟩
  have hne := heckeGammaFactor_ne_zero_of_re_pos χ (s := s) (by linarith)
  convert finiteHeckeL_hasSum_normCoefficients χ ⟨s, hs⟩ using 1
  change (heckeGammaFactor χ s)⁻¹ * Λ s = _
  rw [show Λ s = completedHeckeL χ ⟨s, hs⟩ from hEq ⟨s, hs⟩]
  change _ * (heckeGammaFactor χ s * finiteHeckeL χ ⟨s, hs⟩) = _
  rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]

/-- Paper: Lemma B.6.1.2(2), p. 637. If the character is nontrivial on norm-one
classes, its summatory function divided by `x` tends to zero. -/
theorem heckeIdealSummatory_tendsto_zero_of_nontrivial_on_normOne (χ : U[F])
    (hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1) :
    Tendsto (fun x : ℝ ↦ heckeIdealSummatory (ideleClassNormTwist χ 0) x / x) atTop (𝓝 0) := by
  set N : ℕ → ℝ := fun n ↦ (Nat.card {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ (I.absNorm : ℝ) = n} : ℝ)
    with hN
  set a : ℕ → ℂ := fun n ↦ heckeNormCoefficient (ideleClassNormTwist χ 0) n with ha
  have hN0 (n : ℕ) : 0 ≤ N n := Nat.cast_nonneg _
  have haN (n : ℕ) : ‖a n‖ ≤ N n :=
    heckeIdealSummatory_tendsto_zero_of_nontrivial_on_normOne_norm_le χ n
  obtain ⟨C, hC⟩ := heckeIdealSummatory_tendsto_zero_of_nontrivial_on_normOne_bound (F := F)
  obtain ⟨c, G, hG, hGeq⟩ := heckeIdealSummatory_tendsto_zero_of_nontrivial_on_normOne_zeta (F := F)
  obtain ⟨M, hM, hMsum⟩ :=
    heckeIdealSummatory_tendsto_zero_of_nontrivial_on_normOne_entire χ hχ
  have hNsum (s : ℂ) (hs : 1 < s.re) :
      LSeriesHasSum (fun n ↦ (N n : ℂ)) s (LSeries (fun n ↦ (N n : ℂ)) s) :=
    (heckeIdealSummatory_tendsto_zero_of_nontrivial_on_normOne_hasSum_one (F := F) s
      hs).LSeriesSummable.LSeriesHasSum
  have hWI (u : ℕ → ℝ) (H : ℂ → ℂ) (hu : 0 ≤ u) (hu2 : ∀ n, u n ≤ 2 * N n)
      (hH : ContinuousOn H {s | 1 ≤ s.re})
      (hsum : ∀ s : ℂ, 1 < s.re →
        LSeriesHasSum (fun n ↦ (u n : ℂ)) s (LSeries (fun n ↦ (N n : ℂ)) s + H s)) :
      Tendsto (fun x : ℝ ↦ (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, u n) / x) atTop (𝓝 c) := by
    refine WienerIkehara.tendsto_sum_div (C := 2 * C) (G := fun s ↦ G s + H s)
      (fun n ↦ ?_) (hG.add hH) (fun s hs ↦ ?_) hu
    · calc ∑ i ∈ Finset.range n, u i ≤ ∑ i ∈ Finset.range n, 2 * N i :=
            Finset.sum_le_sum fun i _ ↦ hu2 i
        _ = 2 * ∑ i ∈ Finset.range n, N i := by rw [Finset.mul_sum]
        _ ≤ 2 * (C * n) := by linarith [hC n]
        _ = 2 * C * n := by ring
    · simp only
      rw [hGeq hs, (hsum s hs).LSeries_eq]
      ring
  have hT0 := hWI N 0 (fun n ↦ hN0 n) (fun n ↦ by linarith [hN0 n]) continuousOn_const
    fun s hs ↦ by simpa using hNsum s hs
  have hconj (s : ℂ) (hs : 1 < s.re) :
      LSeriesHasSum (fun n ↦ (starRingEnd ℂ) (a n)) s ((starRingEnd ℂ) (M ((starRingEnd ℂ) s))) :=
    heckeIdealSummatory_tendsto_zero_of_nontrivial_on_normOne_conj a s _
      (hMsum _ (by rwa [Complex.conj_re]))
  have hMc : Continuous fun s ↦ (starRingEnd ℂ) (M ((starRingEnd ℂ) s)) :=
    Complex.continuous_conj.comp (hM.continuous.comp Complex.continuous_conj)
  have hT1 := hWI (fun n ↦ N n + (a n).re) (fun s ↦ (M s + (starRingEnd ℂ) (M ((starRingEnd ℂ) s))) / 2)
    (fun n ↦ by
      have h1 := abs_le.mp (Complex.abs_re_le_norm (a n))
      have h2 := haN n
      simp only [Pi.zero_apply]
      linarith [h1.1])
    (fun n ↦ by linarith [Complex.re_le_norm (a n), haN n])
    ((hM.continuous.add hMc).div_const 2).continuousOn
    fun s hs ↦ by
      have := (hNsum s hs).add (((hMsum s hs).add (hconj s hs)).smul (1 / 2 : ℂ))
      convert this using 1
      · funext n
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        push_cast
        rw [Complex.re_eq_add_conj]
        ring
      · ring
  have hT2 := hWI (fun n ↦ N n + (a n).im)
    (fun s ↦ (M s - (starRingEnd ℂ) (M ((starRingEnd ℂ) s))) / (2 * Complex.I))
    (fun n ↦ by
      have h1 := abs_le.mp (Complex.abs_im_le_norm (a n))
      have h2 := haN n
      simp only [Pi.zero_apply]
      linarith [h1.1])
    (fun n ↦ by linarith [Complex.im_le_norm (a n), haN n])
    ((hM.continuous.sub hMc).div_const _).continuousOn
    fun s hs ↦ by
      have := (hNsum s hs).add (((hMsum s hs).sub (hconj s hs)).smul (1 / (2 * Complex.I)))
      convert this using 1
      · funext n
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        push_cast
        rw [Complex.im_eq_sub_conj]
        ring
      · ring
  have hdiff (u : ℕ → ℝ) (hu : Tendsto (fun x : ℝ ↦ (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (N n + u n)) / x)
      atTop (𝓝 c)) : Tendsto (fun x : ℝ ↦ (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, u n) / x) atTop (𝓝 0) := by
    have := hu.sub hT0
    rw [sub_self] at this
    refine this.congr fun x ↦ ?_
    rw [Finset.sum_add_distrib]
    ring
  have hre := hdiff _ hT1
  have him := hdiff _ hT2
  have hlim := ((Complex.continuous_ofReal.tendsto 0).comp hre).add
    (((Complex.continuous_ofReal.tendsto 0).comp him).mul_const Complex.I)
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with x hx
  rw [heckeIdealSummatory_tendsto_zero_of_nontrivial_on_normOne_sum _ x hx]
  have hsplit : ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, heckeNormCoefficient (ideleClassNormTwist χ 0) n =
      ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, ((a n).re : ℂ) + (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, ((a n).im : ℂ)) *
        Complex.I := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ ↦ (Complex.re_add_im _).symm
  simp only [Function.comp_apply]
  push_cast
  rw [hsplit]
  ring

/-- Paper: Theorem B.6.1.3, p. 637. The logarithmic derivative is bounded by
a squared logarithm for large absolute heights, uniformly over the narrower
region defined by `α * η`. The Dedekind zeta continuation is the one for the
trivial character. For fixed field, character and `α`, the implied constant
works for every admissible width. Its height threshold may depend on the width.
Deviation: The width is represented by a real function restricted to `t ≥ 0`.
Decreasing is expressed as nonincreasing, and the logarithm uses absolute height.
Eventual analyticity and nonvanishing make the logarithmic derivative well-defined. -/
theorem finiteHeckeL_logDeriv_isBigO_of_zeroFree (χ : U[F]) (L Z : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (hZ : MeromorphicNFOn Z univ) (hZSeries : ∀ s : halfPlane, Z s = dedekindZeta F s)
    (α : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1)
    (hα : ∀ z : ℂ, 0 < ‖z - 1‖ → ‖z - 1‖ < α → meromorphicOrderAt Z z ≤ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ → ℝ,
      MapsTo η (Ici 0) (Ioc 0 (1 / 2)) →
      DifferentiableOn ℝ η (Ici 0) → AntitoneOn η (Ici 0) →
      Tendsto (derivWithin η (Ici 0)) atTop (𝓝 0) →
      ((fun t ↦ (η t)⁻¹) =O[atTop] Real.log) →
      (∀ s : ℂ, 1 - η |s.im| < s.re → meromorphicOrderAt L s ≤ 0) →
      let l := atHeight ⊓ 𝓟 {s : ℂ | 1 - α * η |s.im| ≤ s.re}
      (∀ᶠ s in l, AnalyticAt ℂ L s ∧ L s ≠ 0) ∧
        Asymptotics.IsBigOWith C l (logDeriv L) (fun s ↦ (Real.log |s.im|) ^ 2) := by
  sorry

/-- Paper: Equation (B.6.1.13), p. 638. The ideal von Mangoldt function is
`log (N p)` on positive powers of a nonzero prime ideal `p` and zero elsewhere. -/
def idealVonMangoldt (I : Ideal (𝓞 F)) : ℝ :=
  open Classical in
  if h : ∃ v : HeightOneSpectrum (𝓞 F), ∃ k : ℕ, 0 < k ∧ I = v.asIdeal ^ k then
    Real.log (h.choose.asIdeal.absNorm : ℝ)
  else 0

/-- Paper: Equation (B.6.1.13), p. 638. The value at a positive prime-ideal
power is the logarithm of the prime's norm, independently of the exponent. -/
theorem idealVonMangoldt_prime_pow (v : HeightOneSpectrum (𝓞 F)) {k : ℕ} (hk : 0 < k) :
    idealVonMangoldt (v.asIdeal ^ k) = Real.log (v.asIdeal.absNorm : ℝ) := by
  have h : ∃ w : HeightOneSpectrum (𝓞 F), ∃ j : ℕ, 0 < j ∧ v.asIdeal ^ k = w.asIdeal ^ j :=
    ⟨v, k, hk, rfl⟩
  unfold idealVonMangoldt
  split_ifs with h'
  · obtain ⟨hj, hw⟩ := h'.choose_spec.choose_spec
    rw [HeightOneSpectrum.eq_of_dvd_pow ((dvd_pow_self _ hj.ne').trans hw.symm.dvd)]
  · exact absurd h h'

/-- Paper: §B.6.1.2, p. 638. The twisted von Mangoldt value is the product
of the ideal character value and the ideal von Mangoldt weight. -/
def heckeIdealVonMangoldt (χ : 𝒳[F]) (I : Ideal (𝓞 F)) : ℂ :=
  heckeIdealValue χ I * (idealVonMangoldt I : ℂ)

/-- Paper: §B.6.1.2, p. 638. At a positive power of an unramified prime, the
twisted weight is the character power times the logarithm of the prime norm. -/
theorem heckeIdealVonMangoldt_prime_pow (χ : 𝒳[F]) (v : HeightOneSpectrum (𝓞 F))
    (hv : χ.IsUnramifiedAt v) {k : ℕ} (hk : 0 < k) :
    heckeIdealVonMangoldt χ (v.asIdeal ^ k) =
      χ.localValue v ^ k * (Real.log (v.asIdeal.absNorm : ℝ) : ℂ) := by
  classical
  rw [heckeIdealVonMangoldt, heckeIdealValue_prime_pow χ v hk, ite_eq_left hv,
    idealVonMangoldt_prime_pow v hk]

/-- A positive prime power has twisted weight of norm at most the logarithm of its norm.
The weight vanishes on all other ideals. -/
private theorem finiteHeckeL_logDeriv_hasSum_ideals_weight (χ : U[F])
    (I : Ideal (𝓞 F)) :
    ‖heckeIdealVonMangoldt (ideleClassNormTwist χ 0) I‖ ≤ Real.log I.absNorm := by
  classical
  by_cases h : ∃ v : HeightOneSpectrum (𝓞 F), ∃ k : ℕ, 0 < k ∧ I = v.asIdeal ^ k
  · obtain ⟨v, k, hk, rfl⟩ := h
    have hq : (1 : ℝ) ≤ v.asIdeal.absNorm := by
      exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm v).le
    rw [heckeIdealVonMangoldt, heckeIdealValue_prime_pow _ v hk, idealVonMangoldt_prime_pow v hk,
      norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.log_nonneg hq), map_pow, Nat.cast_pow]
    split_ifs <;> simp only [norm_pow, norm_ideleClassNormTwist_zero_localValue, one_pow, one_mul,
      norm_zero, zero_mul]
    · exact Real.log_le_log (zero_lt_one.trans_le hq) (le_self_pow₀ hq hk.ne')
    · exact Real.log_nonneg (one_le_pow₀ hq)
  · simp [heckeIdealVonMangoldt, idealVonMangoldt, h, Real.log_natCast_nonneg]

/-- The logarithmic weight is absorbed by the difference between two exponents greater than one. -/
private theorem finiteHeckeL_logDeriv_hasSum_ideals_summable (χ : U[F]) (s : halfPlane) :
    Summable (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} ↦
      -heckeIdealVonMangoldt (ideleClassNormTwist χ 0) I.val / (I.val.absNorm : ℂ) ^ (s : ℂ)) := by
  obtain ⟨r, hr, hrs⟩ := exists_between (show 1 < (s : ℂ).re from s.property)
  let ε := (s : ℂ).re - r
  have hε : 0 < ε := sub_pos.mpr hrs
  have hs := ((summable_absNorm_rpow F hr).subtype (fun I ↦ I ≠ ⊥)).div_const ε
  apply hs.of_norm_bounded
  intro I
  let q : ℝ := I.val.absNorm
  have hq : 0 < q := by
    dsimp [q]
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr I.property)
  change ‖-heckeIdealVonMangoldt _ I.val / (q : ℂ) ^ (s : ℂ)‖ ≤ q ^ (-r) / ε
  rw [norm_div, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hq]
  calc
    _ ≤ (q ^ ε / ε) / q ^ (s : ℂ).re := by
      apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg hq.le _)
      exact (finiteHeckeL_logDeriv_hasSum_ideals_weight χ I.val).trans
        (Real.log_le_rpow_div hq.le hε)
    _ = q ^ (-r) / ε := by
      rw [div_right_comm, ← Real.rpow_sub hq]
      congr 2
      dsimp [ε]
      ring

/-- At one finite place, the logarithmic derivative sums the weights of its positive powers. -/
private theorem finiteHeckeL_logDeriv_hasSum_ideals_local (χ : U[F])
    (v : HeightOneSpectrum (𝓞 F)) (s : halfPlane) :
    DifferentiableAt ℂ (finiteHeckeEulerFactor χ v) s ∧ finiteHeckeEulerFactor χ v s ≠ 0 ∧
      HasSum (fun k : ℕ ↦ -heckeIdealVonMangoldt (ideleClassNormTwist χ 0) (v.asIdeal ^ (k + 1)) /
        ((v.asIdeal ^ (k + 1)).absNorm : ℂ) ^ (s : ℂ)) (logDeriv (finiteHeckeEulerFactor χ v) s) := by
  classical
  let ψ := ideleClassNormTwist χ 0
  let a := if ψ.IsUnramifiedAt v then ψ.localValue v else 0
  let q := v.asIdeal.absNorm
  let z (w : ℂ) := a * (q : ℂ) ^ (-w)
  have hq : (1 : ℝ) < q := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hq₀ : (q : ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans hq).ne'
  have ha : ‖a‖ ≤ 1 := by
    by_cases h : ψ.IsUnramifiedAt v <;> simp [a, h, ψ, norm_ideleClassNormTwist_zero_localValue]
  have hz : ‖z s‖ < 1 := by
    change ‖a * ((q : ℝ) : ℂ) ^ (-(s : ℂ))‖ < 1
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hq), Complex.neg_re]
    exact (mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _) ha).trans_lt
      (Real.rpow_lt_one_of_one_lt_of_neg hq (neg_lt_zero.mpr (zero_lt_one.trans s.property)))
  have hden : 1 - z s ≠ 0 := fun h ↦ hz.ne (by rw [← sub_eq_zero.mp h, norm_one])
  have hfactor : finiteHeckeEulerFactor χ v = fun w ↦ (1 - z w)⁻¹ := by
    funext w
    by_cases h : (ideleClassNormTwist χ 0).IsUnramifiedAt v <;>
      simp [finiteHeckeEulerFactor, z, a, q, ψ, h]
  rw [hfactor]
  have dz := ((hasDerivAt_id (s : ℂ)).neg.const_cpow (Or.inl hq₀)).const_mul a
  change HasDerivAt z _ (s : ℂ) at dz
  have df := (dz.const_sub 1).inv hden
  change HasDerivAt (fun w ↦ (1 - z w)⁻¹) _ (s : ℂ) at df
  refine ⟨df.differentiableAt, inv_ne_zero hden, ?_⟩
  have hlog : logDeriv (fun w ↦ (1 - z w)⁻¹) s =
      (-Complex.log q * z s) * (1 - z s)⁻¹ := by
    rw [logDeriv_apply, df.deriv]
    change _ / (1 - z s)⁻¹ = _
    field_simp [hden]
    dsimp [z]
    ring
  rw [hlog]
  apply ((hasSum_geometric_of_norm_lt_one hz).mul_left (-Complex.log q * z s)).congr_fun
  intro k
  have hv : heckeIdealValue ψ (v.asIdeal ^ (k + 1)) = a ^ (k + 1) := by
    rw [heckeIdealValue_prime_pow _ v (Nat.succ_pos k)]
    by_cases h : ψ.IsUnramifiedAt v <;> simp [a, h]
  rw [heckeIdealVonMangoldt, hv, idealVonMangoldt_prime_pow v (Nat.succ_pos k),
    map_pow, Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul,
    Complex.natCast_log]
  change -(a ^ (k + 1) * Complex.log q) / ((q : ℂ) ^ (s : ℂ)) ^ (k + 1) =
    (-Complex.log q * z s) * z s ^ k
  rw [mul_assoc (-Complex.log q), ← pow_succ',
    show z s = a * ((q : ℂ) ^ (s : ℂ))⁻¹ by simp [z, Complex.cpow_neg],
    mul_pow, inv_pow, div_eq_mul_inv]
  ring

/-- On the right half-plane, the logarithmic derivatives of the local Euler factors sum
to the logarithmic derivative of the continuation. -/
private theorem finiteHeckeL_logDeriv_hasSum_ideals_places (χ : U[F]) (L : ℂ → ℂ)
    (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s) (s : halfPlane) :
    L s ≠ 0 ∧ HasSum (fun v ↦ logDeriv (finiteHeckeEulerFactor χ v) s) (logDeriv L s) := by
  have hlocal := finiteHeckeL_logDeriv_hasSum_ideals_local χ
  have hn : L s ≠ 0 := by
    rw [hSeries s]
    exact finiteHeckeL_ne_zero_of_one_lt_re χ s
  refine ⟨hn, ?_⟩
  obtain ⟨r, hr, hrs⟩ := exists_between (show 1 < (s : ℂ).re from s.property)
  let D := Complex.re ⁻¹' Ioi r
  have hD : IsOpen D := isOpen_Ioi.preimage Complex.continuous_re
  have hconv := (finiteHeckeEulerProduct_tendstoUniformlyOn_halfPlane χ hr).mono
    (show D ⊆ {w : ℂ | r ≤ w.re} from fun w (hw : r < w.re) ↦ show r ≤ w.re from hw.le)
  have hconvL := hconv.congr_right
    (show EqOn _ L D from fun w hw ↦ (hSeries ⟨w, hr.trans hw⟩).symm)
  have hd (v : HeightOneSpectrum (𝓞 F)) : DifferentiableOn ℂ (finiteHeckeEulerFactor χ v) D :=
    fun w hw ↦ (hlocal v ⟨w, hr.trans hw⟩).1.differentiableWithinAt
  apply (Complex.logDeriv_tendsto hD hrs hconvL.tendstoLocallyUniformlyOn
    (.of_forall fun S ↦ DifferentiableOn.fun_finsetProd fun v _ ↦ hd v) hn).congr
  intro S
  exact logDeriv_fun_prod (fun v _ ↦ (hlocal v s).2.1) (fun v _ ↦ (hlocal v s).1)

/-- Paper: Equation (B.6.1.12), p. 638. To the right of one, the negative of
the Dirichlet series weighted by the ideal von Mangoldt function converges
absolutely to the logarithmic derivative of the finite Hecke L-function. -/
theorem finiteHeckeL_logDeriv_hasSum_ideals (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (s : halfPlane) :
    AnalyticAt ℂ L (s : ℂ) ∧ L s ≠ 0 ∧
      HasSum (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} ↦
        -heckeIdealVonMangoldt (ideleClassNormTwist χ 0) I.val /
          (I.val.absNorm : ℂ) ^ (s : ℂ)) (logDeriv L s) := by
  obtain ⟨hne, hplaces⟩ := finiteHeckeL_logDeriv_hasSum_ideals_places χ L hSeries s
  have hNF := hL (mem_univ (s : ℂ))
  refine ⟨hNF.meromorphicOrderAt_nonneg_iff_analyticAt.mp
    (hNF.meromorphicOrderAt_eq_zero_iff.mpr hne).ge, hne, ?_⟩
  let P (p : HeightOneSpectrum (𝓞 F) × ℕ) : {I : Ideal (𝓞 F) // I ≠ ⊥} :=
    ⟨p.1.asIdeal ^ (p.2 + 1), pow_ne_zero _ p.1.ne_bot⟩
  have hP : Injective P := by
    rintro ⟨v, k⟩ ⟨w, j⟩ he
    have heq : v.asIdeal ^ (k + 1) = w.asIdeal ^ (j + 1) := congrArg Subtype.val he
    obtain rfl := HeightOneSpectrum.eq_of_dvd_pow ((dvd_pow_self _ k.succ_ne_zero).trans heq.dvd)
    exact Prod.ext rfl (Nat.succ.inj (pow_injective_of_not_isUnit v.prime.not_isUnit v.ne_bot heq))
  let f (I : {I : Ideal (𝓞 F) // I ≠ ⊥}) :=
    -heckeIdealVonMangoldt (ideleClassNormTwist χ 0) I.val / (I.val.absNorm : ℂ) ^ (s : ℂ)
  have hout (I) (hI : I ∉ range P) : f I = 0 := by
    have h : ¬ ∃ v : HeightOneSpectrum (𝓞 F), ∃ k : ℕ, 0 < k ∧ I.val = v.asIdeal ^ k := by
      rintro ⟨v, _ | k, hk, he⟩
      · exact hk.false
      · exact hI ⟨(v, k), Subtype.ext he.symm⟩
    simp [f, heckeIdealVonMangoldt, idealVonMangoldt, h]
  have hsum : Summable (f ∘ P) :=
    (finiteHeckeL_logDeriv_hasSum_ideals_summable χ s).comp_injective hP
  have hvalue := hsum.hasSum.prod_fiberwise fun v ↦
    (finiteHeckeL_logDeriv_hasSum_ideals_local χ v s).2.2
  exact (hP.hasSum_iff hout).mp (hvalue.unique hplaces ▸ hsum.hasSum)

/-- Paper: Equation (B.6.1.14), p. 638. The coefficient `Aₘ` sums the
character-weighted von Mangoldt values over nonzero ideals of norm `m`.
Deviation: The empty sum at `m = 0` is also defined. -/
def heckeLogDerivCoefficient (χ : 𝒳[F]) (m : ℕ) : ℂ :=
  ∑ᶠ I : {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = m}, heckeIdealVonMangoldt χ I.val

/-- Over `ℚ`, the ideal von Mangoldt function at the ideal generated by `n` is `Λ n`. -/
private theorem idealVonMangoldt_ratSpan (n : ℕ) :
    idealVonMangoldt (Ideal.span {(n : 𝓞 ℚ)}) = ArithmeticFunction.vonMangoldt n := by
  by_cases hn : IsPrimePow n
  · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hn
    let v : HeightOneSpectrum (𝓞 ℚ) :=
      { asIdeal := Ideal.span {(p : 𝓞 ℚ)}
        isPrime := (Ideal.span_singleton_prime (RatRingOfIntegers.natCast_ne_zero hp.ne_zero)).mpr
          (RatRingOfIntegers.prime_natCast_iff.mpr hp)
        ne_bot := by
          rw [Ne, Ideal.span_singleton_eq_bot]
          exact RatRingOfIntegers.natCast_ne_zero hp.ne_zero }
    have hv : Ideal.span {((p ^ k : ℕ) : 𝓞 ℚ)} = v.asIdeal ^ k := by
      simp [v, Ideal.span_singleton_pow]
    rw [hv, idealVonMangoldt_prime_pow v hk, ArithmeticFunction.vonMangoldt_apply_pow hk.ne',
      ArithmeticFunction.vonMangoldt_apply_prime hp]
    show Real.log ((Ideal.absNorm (Ideal.span {(p : 𝓞 ℚ)}) : ℕ) : ℝ) = _
    rw [RatRingOfIntegers.absNorm_span_natCast]
  · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right hn, idealVonMangoldt, dite_eq_right]
    rintro ⟨v, k, hk, hvk⟩
    apply hn
    obtain ⟨p, hp⟩ := RatRingOfIntegers.exists_eq_span_natCast v.asIdeal
    have hp0 : p ≠ 0 := by
      rintro rfl
      exact v.ne_bot (by simpa using hp)
    have hprime : Nat.Prime p := RatRingOfIntegers.prime_natCast_iff.mp
      ((Ideal.span_singleton_prime (RatRingOfIntegers.natCast_ne_zero hp0)).mp (hp ▸ v.isPrime))
    have hpow : Ideal.span {(n : 𝓞 ℚ)} = Ideal.span {((p ^ k : ℕ) : 𝓞 ℚ)} := by
      rw [hvk, hp, Ideal.span_singleton_pow]
      simp
    have := congrArg Ideal.absNorm hpow
    rw [RatRingOfIntegers.absNorm_span_natCast, RatRingOfIntegers.absNorm_span_natCast] at this
    exact this ▸ (isPrimePow_nat_iff _).mpr ⟨p, k, hprime, hk, rfl⟩

/-- A character that is identically one has value one at every nonzero ideal. -/
private theorem heckeIdealValue_of_forall_eq_one (χ : 𝒳[F]) (hχ : ∀ g, χ g = 1)
    {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) : heckeIdealValue χ I = 1 := by
  classical
  have hres : ∀ v : HeightOneSpectrum (𝓞 F), ∀ x : v.adicCompletion F, x ≠ 0 →
      χ.restrict v x = 1 := fun v x hx ↦ by
    have hu : IsUnit x := isUnit_iff_ne_zero.mpr hx
    rw [← hu.unit_spec, HeckeCharacter.restrict_apply]
    simp [hχ, hx]
  have hun : ∀ v : HeightOneSpectrum (𝓞 F), χ.IsUnramifiedAt v := fun v ↦
    HeckeCharacter.isUnramifiedAt_iff.mpr fun x ↦ hres v _ (by simp)
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F), χ.localValue v = 1 := fun v ↦ by
    rw [HeckeCharacter.localValue]
    apply hres
    exact (Valued.v.exists_isUniformizer_of_isCyclic_of_nontrivial).choose_spec.ne_zero
  unfold heckeIdealValue
  rw [ite_eq_right hI]
  exact finprod_eq_one_of_forall_eq_one fun v ↦ by simp [hun v, hloc v]

/-- Paper: Equation (B.6.1.14), p. 638. Over the rationals with trivial
character these coefficients recover the classical von Mangoldt function. -/
theorem heckeLogDerivCoefficient_trivial_rat (m : ℕ) :
    heckeLogDerivCoefficient (ideleClassNormTwist (1 : U[ℚ]) 0) m =
      (ArithmeticFunction.vonMangoldt m : ℂ) := by
  have hχ : ∀ g, ideleClassNormTwist (1 : U[ℚ]) 0 g = 1 := fun g ↦ by
    simp only [ideleClassNormTwist, Complex.cpow_zero]
    change ((1 : U[ℚ]) g : ℂ) * 1 = 1
    simp
  unfold heckeLogDerivCoefficient
  rcases eq_or_ne m 0 with rfl | hm
  · have : IsEmpty {I : Ideal (𝓞 ℚ) // I ≠ ⊥ ∧ I.absNorm = 0} :=
      ⟨fun I ↦ I.2.1 (Ideal.absNorm_eq_zero_iff.mp I.2.2)⟩
    rw [finsum_of_isEmpty]
    simp
  · have hmem : ∀ I : Ideal (𝓞 ℚ), I ≠ ⊥ ∧ I.absNorm = m ↔ I = Ideal.span {(m : 𝓞 ℚ)} :=
      fun I ↦ by
        constructor
        · rintro ⟨-, h⟩
          obtain ⟨n, rfl⟩ := RatRingOfIntegers.exists_eq_span_natCast I
          rw [RatRingOfIntegers.absNorm_span_natCast] at h
          rw [h]
        · rintro rfl
          refine ⟨?_, RatRingOfIntegers.absNorm_span_natCast m⟩
          rw [Ne, Ideal.span_singleton_eq_bot]
          exact RatRingOfIntegers.natCast_ne_zero hm
    let : Unique {I : Ideal (𝓞 ℚ) // I ≠ ⊥ ∧ I.absNorm = m} :=
      { default := ⟨_, (hmem _).mpr rfl⟩
        uniq := fun I ↦ Subtype.ext ((hmem I.val).mp I.2) }
    rw [finsum_unique]
    show heckeIdealVonMangoldt _ (Ideal.span {(m : 𝓞 ℚ)}) = _
    rw [heckeIdealVonMangoldt, heckeIdealValue_of_forall_eq_one _ hχ ((hmem _).mpr rfl).1,
      idealVonMangoldt_ratSpan, one_mul]

/-- A unitary character twisted by the trivial norm power has values of norm at most one,
so the twisted von Mangoldt weight is bounded by the ideal von Mangoldt weight. -/
private theorem heckeLogDerivCoefficient_bound_norm_le (χ : U[F]) (I : Ideal (𝓞 F)) :
    ‖heckeIdealVonMangoldt (ideleClassNormTwist χ 0) I‖ ≤ idealVonMangoldt I := by
  classical
  have hΛ : 0 ≤ idealVonMangoldt I := by
    unfold idealVonMangoldt
    split_ifs
    exacts [Real.log_natCast_nonneg _, le_rfl]
  have hval : ‖heckeIdealValue (ideleClassNormTwist χ 0) I‖ ≤ 1 := by
    unfold heckeIdealValue
    split_ifs
    · simp
    · refine finprod_induction (fun z : ℂ ↦ ‖z‖ ≤ 1) (by simp)
        (fun x y hx hy ↦ (norm_mul_le x y).trans (by nlinarith [norm_nonneg x, norm_nonneg y]))
        fun v ↦ ?_
      rw [norm_pow]
      refine pow_le_one₀ (norm_nonneg _) ?_
      split_ifs
      · exact (norm_ideleClassNormTwist_zero_localValue χ v).le
      · simp
  rw [heckeIdealVonMangoldt, norm_mul, Complex.norm_real, Real.norm_of_nonneg hΛ]
  exact mul_le_of_le_one_left hΛ hval

/-- A nonzero prime ideal lies over a rational prime `q`, and its norm is a positive
power of `q`. -/
private theorem heckeLogDerivCoefficient_bound_liesOver (v : HeightOneSpectrum (𝓞 F)) :
    ∃ q f : ℕ, q.Prime ∧ 0 < f ∧ v.asIdeal.LiesOver (Ideal.span {(q : ℤ)}) ∧
      v.asIdeal.absNorm = q ^ f := by
  have : NeZero v.asIdeal := ⟨v.ne_bot⟩
  set q := Ideal.absNorm (v.asIdeal.under ℤ)
  have hl : v.asIdeal.LiesOver (Ideal.span {(q : ℤ)}) := Int.liesOver_span_absNorm _
  refine ⟨q, v.asIdeal.inertiaDeg ℤ, Nat.absNorm_under_prime v.asIdeal,
    Ideal.inertiaDeg_pos _ _, hl, ?_⟩
  rw [← Ideal.natAbs_pow_inertiaDeg (q : ℤ) v.asIdeal, Int.natAbs_natCast]

/-- At most `[F : ℚ]` positive prime-ideal powers have a given norm `m ≥ 2`, and each
has von Mangoldt weight at most `log m`. -/
private theorem heckeLogDerivCoefficient_bound_finsum_le {m : ℕ} (hm : 2 ≤ m) :
    ∑ᶠ I : {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = m}, idealVonMangoldt I.val ≤
      Module.finrank ℚ F * Real.log m := by
  classical
  set p := m.minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have : Fact p.Prime := ⟨hp⟩
  set P : Ideal ℤ := Ideal.span {(p : ℤ)}
  have hfin : {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ I.absNorm = m}.Finite :=
    (Ring.HasFiniteQuotients.finite_absNorm_eq (S := 𝓞 F) m).subset fun _ h ↦ h.2
  have : Finite {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = m} := hfin.to_subtype
  have : Fintype {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = m} := Fintype.ofFinite _
  have : Fintype (P.primesOver (𝓞 F)) := (primesOver_finite P (𝓞 F)).fintype
  -- The ideals with nonzero weight are positive powers of primes over `p`.
  have hpow : ∀ I : {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = m}, idealVonMangoldt I.val ≠ 0 →
      ∃ v : HeightOneSpectrum (𝓞 F), ∃ k, 0 < k ∧ I.val = v.asIdeal ^ k := by
    intro I hI
    by_contra h
    exact hI (by rw [idealVonMangoldt, dite_eq_right_iff.mpr fun h' ↦ absurd h' h])
  have hover : ∀ (v : HeightOneSpectrum (𝓞 F)) (k : ℕ), 0 < k →
      (v.asIdeal ^ k).absNorm = m → v.asIdeal ∈ P.primesOver (𝓞 F) := by
    intro v k hk hvk
    obtain ⟨q, f, hq, hf, hlies, hnorm⟩ := heckeLogDerivCoefficient_bound_liesOver v
    rw [map_pow, hnorm, ← pow_mul] at hvk
    have hqp : q = p := by
      have h : m.minFac = q := by rw [← hvk, hq.pow_minFac (Nat.mul_ne_zero hf.ne' hk.ne')]
      exact h.symm
    subst hqp
    exact ⟨v.isPrime, hlies⟩
  have hle : ∀ (v : HeightOneSpectrum (𝓞 F)) (k : ℕ), 0 < k →
      (v.asIdeal ^ k).absNorm = m → Real.log (v.asIdeal.absNorm : ℝ) ≤ Real.log m := by
    intro v k hk hvk
    have h0 : 0 < v.asIdeal.absNorm :=
      Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)
    refine Real.log_le_log (by exact_mod_cast h0) ?_
    rw [← hvk, map_pow]
    exact_mod_cast Nat.le_self_pow hk.ne' _
  -- Weighted ideals inject into the primes over `p` through their radicals.
  set s := Finset.univ.filter fun I : {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = m} ↦
    idealVonMangoldt I.val ≠ 0
  have hrad : ∀ I ∈ s, ∃ v : HeightOneSpectrum (𝓞 F), ∃ k, 0 < k ∧ I.val = v.asIdeal ^ k ∧
      I.val.radical = v.asIdeal := by
    intro I hI
    obtain ⟨v, k, hk, hI'⟩ := hpow I (Finset.mem_filter.mp hI).2
    exact ⟨v, k, hk, hI', by rw [hI', Ideal.radical_pow v.asIdeal hk.ne', v.isPrime.radical]⟩
  have hcard : s.card ≤ Fintype.card (P.primesOver (𝓞 F)) := by
    rw [← Fintype.card_coe s]
    refine Fintype.card_le_of_injective (fun I ↦ ⟨I.1.1.radical, ?_⟩) ?_
    · obtain ⟨v, k, hk, hI, hr⟩ := hrad I.1 I.2
      rw [hr]
      exact hover v k hk (hI ▸ I.1.2.2)
    · rintro ⟨I, hI⟩ ⟨J, hJ⟩ hIJ
      obtain ⟨v, k, hk, hI', hrI⟩ := hrad I hI
      obtain ⟨w, j, hj, hJ', hrJ⟩ := hrad J hJ
      have hvw : v.asIdeal = w.asIdeal := by
        have := congrArg Subtype.val hIJ
        simp only at this
        rw [← hrI, ← hrJ, this]
      have h2 : 2 ≤ v.asIdeal.absNorm := by
        have h0 := Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot
        have h1 : v.asIdeal.absNorm ≠ 1 := by
          rw [Ne, Ideal.absNorm_eq_one_iff]
          exact v.isPrime.ne_top
        omega
      have hkj : k = j := by
        have hI2 := I.2.2
        have hJ2 := J.2.2
        rw [hI', map_pow] at hI2
        rw [hJ', ← hvw, map_pow] at hJ2
        exact Nat.pow_right_injective h2 (hI2.trans hJ2.symm)
      have : I = J := Subtype.ext (by rw [hI', hJ', hvw, hkj])
      subst this
      rfl
  have hprimes : Fintype.card (P.primesOver (𝓞 F)) ≤ Module.finrank ℚ F := by
    rw [← RingOfIntegers.rank, ← Ideal.sum_ramification_inertia_eq_finrank P (𝓞 F),
      Fintype.card_eq_sum_ones]
    refine Finset.sum_le_sum fun q _ ↦ ?_
    have : q.1.IsPrime := q.2.1
    have : q.1.LiesOver P := q.2.2
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero
      (Ideal.ramificationIdx_pos ℤ q.1).ne' (Ideal.inertiaDeg_pos q.1 ℤ).ne')
  rw [finsum_eq_sum_of_fintype, ← Finset.sum_filter_ne_zero]
  have hlogm : 0 ≤ Real.log m := Real.log_natCast_nonneg m
  calc ∑ I ∈ s, idealVonMangoldt I.val ≤ ∑ _I ∈ s, Real.log m := by
        refine Finset.sum_le_sum fun I hI ↦ ?_
        obtain ⟨v, k, hk, hI', -⟩ := hrad I hI
        rw [hI', idealVonMangoldt_prime_pow v hk]
        exact hle v k hk (hI' ▸ I.2.2)
    _ = s.card * Real.log m := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ Module.finrank ℚ F * Real.log m := by
        gcongr
        exact_mod_cast hcard.trans hprimes

/-- Paper: Lemma B.6.1.4, p. 638. The logarithmic-derivative coefficients are
bounded by a constant times `log m`, with the constant depending only on the field degree. -/
theorem heckeLogDerivCoefficient_bound (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (F : Type*) [Field F] [NumberField F], Module.finrank ℚ F = d →
        ∀ᶠ m : ℕ in atTop, ∀ χ : U[F],
          ‖heckeLogDerivCoefficient (ideleClassNormTwist χ 0) m‖ ≤ C * Real.log (m : ℝ) := by
  refine ⟨d + 1, by positivity, fun F _ _ hd ↦ ?_⟩
  subst hd
  filter_upwards [eventually_ge_atTop 2] with m hm χ
  classical
  have hfin : {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ I.absNorm = m}.Finite :=
    (Ring.HasFiniteQuotients.finite_absNorm_eq (S := 𝓞 F) m).subset fun _ h ↦ h.2
  have : Finite {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = m} := hfin.to_subtype
  have : Fintype {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = m} := Fintype.ofFinite _
  have hsum := heckeLogDerivCoefficient_bound_finsum_le (F := F) hm
  rw [finsum_eq_sum_of_fintype] at hsum
  unfold heckeLogDerivCoefficient
  rw [finsum_eq_sum_of_fintype]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun I _ ↦
    heckeLogDerivCoefficient_bound_norm_le χ I.val).trans (hsum.trans ?_))
  gcongr
  linarith

-- TODO(paper-gap): In (B.6.1.16) a pure norm twist can have a pole in Ω.
-- Restrict the logarithm to heights above the pole. After (B.6.1.19) the
-- summand must retain the power m in N(p)^(m * (1 + αη(T))).
-- TODO(paper-gap): Substituting the radii from (B.6.1.18) into the first
-- coefficient in (B.6.1.20) gives 4(1 + 3α) / ((1 - α)^2 η(T)).

/-- Paper: Corollary B.6.1.5, p. 639. On the line `Re(s) = 1`, the logarithmic
derivative is bounded by a squared logarithm as the absolute height grows.
Deviation: The logarithm uses absolute height. Eventual analyticity and
nonvanishing make the logarithmic derivative well-defined. -/
theorem finiteHeckeL_logDeriv_isBigO_oneLine (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s) :
    (∀ᶠ t : ℝ in atAbsTop, AnalyticAt ℂ L ⟨1, t⟩ ∧ L ⟨1, t⟩ ≠ 0) ∧
      (fun t : ℝ ↦ logDeriv L ⟨1, t⟩) =O[atAbsTop] (fun t ↦ (Real.log |t|) ^ 2) := by
  sorry

open Complex in
/-- The inequality for the three Euler factors with a common radius and a unit phase. -/
private theorem finiteHeckeL_inv_isBigO_oneLine_one_le_norm_eulerFactor_product {r : ℝ} (hr : 0 ≤ r) (hr₁ : r < 1) {z : ℂ} (hz : ‖z‖ = 1) :
    1 ≤ ‖(1 - (r : ℂ))⁻¹ ^ 3 * (1 - (r : ℂ) * z)⁻¹ ^ 4 *
      (1 - (r : ℂ) * z ^ 2)⁻¹‖ := by
  have h₀ : ‖(r : ℂ)‖ < 1 := by rw [Complex.norm_of_nonneg hr]; exact hr₁
  have h₁ : ‖(r : ℂ) * z‖ < 1 := by simpa [norm_mul, hz] using h₀
  have h₂ : ‖(r : ℂ) * z ^ 2‖ < 1 := by simpa [norm_mul, norm_pow, hz] using h₀
  have hinv {w : ℂ} (hw : ‖w‖ < 1) : (1 - w)⁻¹ = exp (-log (1 - w)) := by
    rw [exp_neg, exp_log (fun h ↦ hw.ne (by rw [← sub_eq_zero.mp h, norm_one]))]
  rw [hinv h₀, hinv h₁, hinv h₂, ← exp_nat_mul, ← exp_nat_mul, ← exp_add, ← exp_add,
    norm_exp, Real.one_le_exp_iff]
  simp only [add_re, mul_re, re_ofNat, im_ofNat, Nat.cast_ofNat, zero_mul, sub_zero]
  rw [← ((hasSum_re (hasSum_taylorSeries_neg_log h₀)).mul_left 3 |>.add
    ((hasSum_re (hasSum_taylorSeries_neg_log h₁)).mul_left 4) |>.add
    (hasSum_re (hasSum_taylorSeries_neg_log h₂))).tsum_eq]
  apply tsum_nonneg
  intro n
  simp only [mul_pow, ← ofReal_pow, div_natCast_re, ofReal_re, mul_re, ofReal_im, zero_mul,
    sub_zero, ← mul_div_assoc, ← add_div]
  apply div_nonneg _ (Nat.cast_nonneg _)
  have hnorm : ‖z ^ n‖ = 1 := by rw [norm_pow, hz, one_pow]
  have him := sq_norm_sub_sq_re (z ^ n)
  rw [hnorm, one_pow] at him
  rw [← pow_mul, Nat.mul_comm 2 n, pow_mul, pow_two (z ^ n), mul_re]
  have hident :
      3 * r ^ n + 4 * (r ^ n * (z ^ n).re) + r ^ n *
        ((z ^ n).re * (z ^ n).re - (z ^ n).im * (z ^ n).im) =
      2 * r ^ n * ((z ^ n).re + 1) ^ 2 := by
    rw [← sq ((z ^ n).im), ← him]
    ring
  rw [hident]
  positivity

/-- The de la Vallée Poussin Euler-product inequality for the trivial character, a unitary
character, and its square at ordinates in the ratio zero, one, and two. -/
private theorem finiteHeckeL_inv_isBigO_oneLine_norm_finiteHeckeL_product_ge_one (χ : U[F]) {x : ℝ} (hx : 1 < x)
    (a : ℂ) (ha : a.re = 0) :
    1 ≤ ‖(ideleClassNormTwist (1 : U[F]) 0).LSeries (x : ℂ) ^ 3 * (ideleClassNormTwist χ 0).LSeries ((x : ℂ) + a) ^ 4 *
      (ideleClassNormTwist (χ ^ 2) 0).LSeries ((x : ℂ) + 2 * a)‖ := by
  classical
  have h₂a : (2 * a).re = 0 := by simp [Complex.mul_re, ha]
  let s₀ : halfPlane := ⟨(x : ℂ), hx⟩
  let s₁ : halfPlane := ⟨(x : ℂ) + a, by simpa [mem_preimage, Complex.add_re, ha]⟩
  let s₂ : halfPlane := ⟨(x : ℂ) + 2 * a, by simpa [mem_preimage, Complex.add_re, h₂a]⟩
  have hp := (((finiteHeckeL_hasProd (1 : U[F]) s₀).pow 3).mul
    ((finiteHeckeL_hasProd χ s₁).pow 4)).mul (finiteHeckeL_hasProd (χ ^ 2) s₂)
  apply ge_of_tendsto' hp.norm
  intro T
  simp only [norm_prod]
  refine Finset.one_le_prod₀ fun v _ ↦ ?_
  change 1 ≤ ‖finiteHeckeEulerFactor (1 : U[F]) v x ^ 3 *
    finiteHeckeEulerFactor χ v ((x : ℂ) + a) ^ 4 *
    finiteHeckeEulerFactor (χ ^ 2) v ((x : ℂ) + 2 * a)‖
  have hres (ψ : U[F]) (u : (v.adicCompletion F)ˣ) :
      (ideleClassNormTwist ψ 0).restrict v (u : v.adicCompletion F) =
        (ψ (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u) : ℂ) := by
    rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
    change (ψ _ : ℂ) * _ ^ (0 : ℂ) = _
    rw [Complex.cpow_zero, mul_one]
  have hres_one (u : (v.adicCompletion F)ˣ) :
      (ideleClassNormTwist (1 : U[F]) 0).restrict v (u : v.adicCompletion F) = 1 := by
    rw [hres, PontryaginDual.one_apply, Circle.coe_one]
  have hres_sq (u : (v.adicCompletion F)ˣ) :
      (ideleClassNormTwist (χ ^ 2) 0).restrict v (u : v.adicCompletion F) =
        ((ideleClassNormTwist χ 0).restrict v (u : v.adicCompletion F)) ^ 2 := by
    rw [hres, hres]
    rfl
  have hu₀ : (ideleClassNormTwist (1 : U[F]) 0).IsUnramifiedAt v := HeckeCharacter.isUnramifiedAt_iff.mpr
    fun u ↦ hres_one (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u)
  have hu₂ (hu : (ideleClassNormTwist χ 0).IsUnramifiedAt v) : (ideleClassNormTwist (χ ^ 2) 0).IsUnramifiedAt v :=
    HeckeCharacter.isUnramifiedAt_iff.mpr fun u ↦ by
      rw [show (ideleClassNormTwist (χ ^ 2) 0).restrict v u = ((ideleClassNormTwist χ 0).restrict v u) ^ 2 from
        hres_sq (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u),
        hu.restrict_apply_unit_eq_one, one_pow]
  let val : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
  let u := Units.mk0 (val.exists_isUniformizer_of_isCyclic_of_nontrivial.choose : v.adicCompletion F)
    val.exists_isUniformizer_of_isCyclic_of_nontrivial.choose_spec.ne_zero
  have hv₀ : (ideleClassNormTwist (1 : U[F]) 0).localValue v = 1 := hres_one u
  have hv₂ : (ideleClassNormTwist (χ ^ 2) 0).localValue v = ((ideleClassNormTwist χ 0).localValue v) ^ 2 := hres_sq u
  let q : ℝ := v.asIdeal.absNorm
  have hq : 1 < q := by
    dsimp only [q]
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hq₀ := zero_lt_one.trans hq
  have hqC : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq₀.ne'
  let r := q ^ (-x)
  have hr : 0 ≤ r := Real.rpow_nonneg hq₀.le _
  have hr₁ : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith)
  let z (ψ : U[F]) (b : ℂ) := (ideleClassNormTwist ψ 0).localValue v * (q : ℂ) ^ (-b)
  have hz (ψ : U[F]) (b : ℂ) (hb : b.re = 0) : ‖z ψ b‖ = 1 := by
    simp [z, norm_ideleClassNormTwist_zero_localValue,
      Complex.norm_cpow_eq_rpow_re_of_pos hq₀, Complex.neg_re, hb]
  have hphase (ψ : U[F]) (b : ℂ) :
      (ideleClassNormTwist ψ 0).localValue v * (v.asIdeal.absNorm : ℂ) ^ (-((x : ℂ) + b)) =
        (r : ℂ) * z ψ b := by
    change (ideleClassNormTwist ψ 0).localValue v * (q : ℂ) ^ (-((x : ℂ) + b)) = _
    rw [neg_add, Complex.cpow_add _ _ hqC, ← Complex.ofReal_neg,
      ← Complex.ofReal_cpow hq₀.le]
    exact mul_left_comm ..
  have hsq : z (χ ^ 2) (2 * a) = z χ a ^ 2 := by
    simp only [z, hv₂, mul_pow, neg_mul_eq_mul_neg]
    rw [show (2 : ℂ) = (↑(2 : ℕ) : ℂ) by norm_num, Complex.cpow_nat_mul]
  rw [finiteHeckeEulerFactor, ite_eq_left hu₀, hv₀, one_mul]
  change 1 ≤ ‖(1 - (q : ℂ) ^ (-(x : ℂ)))⁻¹ ^ 3 * _ * _‖
  rw [← Complex.ofReal_neg, ← Complex.ofReal_cpow hq₀.le]
  by_cases hu : (ideleClassNormTwist χ 0).IsUnramifiedAt v
  · rw [finiteHeckeEulerFactor, ite_eq_left hu, finiteHeckeEulerFactor, ite_eq_left (hu₂ hu),
      hphase χ a, hphase (χ ^ 2) (2 * a), hsq]
    exact finiteHeckeL_inv_isBigO_oneLine_one_le_norm_eulerFactor_product hr hr₁ (hz χ a ha)
  · rw [finiteHeckeEulerFactor, ite_eq_right hu, one_pow, mul_one, finiteHeckeEulerFactor]
    have hrnorm : ‖(1 : ℂ) - (r : ℂ)‖ = 1 - r := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_of_nonneg (sub_nonneg.mpr hr₁.le)]
    split_ifs
    · rw [hphase (χ ^ 2) (2 * a)]
      let w := (r : ℂ) * z (χ ^ 2) (2 * a)
      change 1 ≤ ‖(1 - (r : ℂ))⁻¹ ^ 3 * (1 - w)⁻¹‖
      have hw : ‖w‖ = r := by
        rw [show ‖w‖ = ‖(r : ℂ)‖ * ‖z (χ ^ 2) (2 * a)‖ from norm_mul _ _,
          hz _ _ h₂a, Complex.norm_of_nonneg hr, mul_one]
      have hpos : 0 < ‖(1 : ℂ) - w‖ := norm_pos_iff.mpr fun h ↦
        hr₁.ne (by rw [← hw, ← sub_eq_zero.mp h, norm_one])
      rw [norm_mul, norm_pow, norm_inv, norm_inv, hrnorm, inv_pow, ← mul_inv,
        one_le_inv₀ (mul_pos (pow_pos (sub_pos.mpr hr₁) 3) hpos)]
      have hle : ‖(1 : ℂ) - w‖ ≤ 1 + r := by
        simpa only [hw, norm_one] using norm_sub_le (1 : ℂ) w
      calc
        (1 - r) ^ 3 * ‖(1 : ℂ) - w‖ ≤ (1 - r) ^ 3 * (1 + r) :=
          mul_le_mul_of_nonneg_left hle (pow_nonneg (sub_nonneg.mpr hr₁.le) _)
        _ = (1 - r) ^ 2 * (1 - r ^ 2) := by ring
        _ ≤ (1 - r) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg r]) (sq_nonneg _)
        _ ≤ 1 := by
          rw [mul_one]
          exact pow_le_one₀ (sub_nonneg.mpr hr₁.le) (by linarith)
    · rw [mul_one, norm_pow, norm_inv, hrnorm, inv_pow,
        one_le_inv₀ (pow_pos (sub_pos.mpr hr₁) 3)]
      exact pow_le_one₀ (sub_nonneg.mpr hr₁.le) (by linarith)

/-- Euler product inequality in the exact variables used in the bound. -/
private theorem finiteHeckeL_inv_isBigO_oneLine_euler (χ : U[F]) (L : ℂ → ℂ)
    (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    {x : ℝ} (hx : 1 < x) (t : ℝ) :
    1 ≤ ‖dedekindZeta F x‖ ^ 3 * ‖L ⟨x,t⟩‖ ^ 4 *
      ‖finiteHeckeL (χ ^ 2) ⟨⟨x,2*t⟩,hx⟩‖ := by
  let a : ℂ := ⟨0,t⟩
  have h := finiteHeckeL_inv_isBigO_oneLine_norm_finiteHeckeL_product_ge_one χ hx a rfl
  have h1 : (x : ℂ) + a = ⟨x,t⟩ := by apply Complex.ext <;> simp [a]
  have h2 : (x : ℂ) + 2 * a = ⟨x,2*t⟩ := by apply Complex.ext <;> simp [a, Complex.mul_re, Complex.mul_im]
  have hζ := completedHeckeL_one_eq_dedekindZeta (F := F) (⟨x,hx⟩ : halfPlane)
  change heckeGammaFactor (1 : U[F]) x * _ = _ at hζ
  rw [← heckeGammaFactor_one] at hζ
  have hz := mul_left_cancel₀ (heckeGammaFactor_ne_zero_of_re_pos (1 : U[F]) (zero_lt_one.trans hx)) hζ
  rw [h1, h2, norm_mul, norm_mul, norm_pow, norm_pow] at h
  rw [hSeries ⟨⟨x,t⟩,hx⟩]
  simpa only [finiteHeckeL, hz] using h

private theorem finiteHeckeL_inv_isBigO_oneLine_scalar {V B X L Q : ℝ} (hV : 3 ≤ V) (hB : 0 ≤ B) (hX : 0 ≤ X) (hQ : 0 ≤ Q)
    (hzeta : B ≤ V ^ 13) (hsq : Q ≤ V) (hdiff : X ≤ L + (V ^ 11)⁻¹)
    (hprod : 1 ≤ B ^ 3 * X ^ 4 * Q) : (V ^ 11)⁻¹ ≤ L := by
  by_contra! hbad
  have hpos : 0 < V := by linarith
  have ht : X ≤ 2 / V ^ 11 := by rw [div_eq_mul_inv]; linarith
  have h := calc
    1 ≤ B ^ 3 * X ^ 4 * Q := hprod
    _ ≤ (V ^ 13) ^ 3 * (2 / V ^ 11) ^ 4 * V := by gcongr
    _ = 16 / V ^ 4 := by field_simp; ring
  have hh : 3 ^ 4 ≤ V ^ 4 := by gcongr
  have := (le_div_iff₀ (pow_pos hpos 4)).mp h
  norm_num at hh
  linarith

/-- A local version of the strip bounds sufficient for the reciprocal estimate. -/
private theorem finiteHeckeL_inv_isBigO_oneLine_reciprocal_of_bounds (χ : U[F]) (L : ℂ → ℂ)
    (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (m : ℕ) (hm : m ≠ 0)
    (ha : ∀ᶠ t : ℝ in atAbsTop, AnalyticAt ℂ L ⟨1,t⟩)
    (h₁ : ∀ᶠ t : ℝ in atAbsTop, ∀ d ∈ Ioc (0:ℝ) 1,
      ‖L ⟨1 + d,t⟩ - L ⟨1,t⟩‖ ≤ |t| ^ m * d)
    (h₂ : ∀ᶠ t : ℝ in atAbsTop, ∀ d ∈ Ioc (0:ℝ) 1, ∀ hd : 1 < 1+d,
      ‖finiteHeckeL (χ ^ 2) ⟨⟨1+d,2*t⟩,hd⟩‖ ≤ |t| ^ m) :
    (∀ᶠ t : ℝ in atAbsTop, AnalyticAt ℂ L ⟨1,t⟩ ∧ L ⟨1,t⟩ ≠ 0) ∧
      ∃ N : ℕ, 0 < N ∧ (fun t : ℝ ↦ (L ⟨1,t⟩)⁻¹) =O[atAbsTop] (fun t ↦ |t| ^ N) := by
  let V (t : ℝ) := |t| ^ m
  let d (t : ℝ) := (V t ^ 12)⁻¹
  have hV : Tendsto V atAbsTop atTop :=
    (tendsto_pow_atTop (α := ℝ) hm).comp tendsto_comap
  have hd : Tendsto d atAbsTop (𝓝 (0:ℝ)) :=
    tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (α := ℝ) (by decide : 12 ≠ 0)).comp hV)
  have hx : Tendsto (fun t ↦ 1+d t) atAbsTop (𝓝[>] (1:ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨by simpa using hd.const_add 1, ?_⟩
    filter_upwards [hV.eventually_gt_atTop 0] with t ht
    change 1 < 1 + (V t ^ 12)⁻¹
    exact lt_add_of_pos_right _ (inv_pos.mpr (pow_pos ht 12))
  obtain ⟨C,hC⟩ := ((NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT F).norm.comp hx).isBoundedUnder_le.eventually_le
  have hbound : ∀ᶠ t : ℝ in atAbsTop, (V t ^ 11)⁻¹ ≤ ‖L ⟨1,t⟩‖ := by
    filter_upwards [hC, hV.eventually_ge_atTop C, hV.eventually_ge_atTop 3,
      hd.eventually_le_const zero_lt_one, h₁, h₂] with t hζ hCV hv hdle hdiff hsq
    have hv' : 0 < V t := by linarith
    have hdt : 0 < d t := inv_pos.mpr (pow_pos hv' 12)
    have hxt : 1 < 1 + d t := lt_add_of_pos_right _ hdt
    have hz : d t * ‖dedekindZeta F (1 + d t : ℝ)‖ ≤ C := by
      simpa [Function.comp_def, norm_mul, Real.norm_of_nonneg hdt.le] using hζ
    apply finiteHeckeL_inv_isBigO_oneLine_scalar hv (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) _ (hsq (d t) ⟨hdt,hdle⟩ hxt) _
      (finiteHeckeL_inv_isBigO_oneLine_euler χ L hSeries hxt t)
    · have hvBound : ‖dedekindZeta F (1 + d t : ℝ)‖ ≤ V t / d t :=
        (le_div_iff₀ hdt).mpr (by simpa only [mul_comm (d t)] using hz.trans hCV)
      exact hvBound.trans_eq (show V t / d t = V t ^ 13 by dsimp only [d]; rw [div_inv_eq_mul, pow_succ (V t) 12, mul_comm])
    · calc
        _ ≤ ‖L ⟨1,t⟩‖ + ‖L ⟨1+d t,t⟩ - L ⟨1,t⟩‖ := by
          linarith [norm_sub_norm_le (L ⟨1+d t,t⟩) (L ⟨1,t⟩)]
        _ ≤ ‖L ⟨1,t⟩‖ + V t * d t := add_le_add_right (hdiff _ ⟨hdt,hdle⟩) _
        _ = _ := by dsimp [d]; field_simp
  refine ⟨?_, m*11, Nat.mul_pos (Nat.pos_of_ne_zero hm) (by decide), Asymptotics.IsBigO.of_bound 1 ?_⟩
  · filter_upwards [ha, hbound, hV.eventually_gt_atTop 0] with t ht hb hv
    exact ⟨ht, norm_pos_iff.mp ((inv_pos.mpr (pow_pos hv 11)).trans_le hb)⟩
  · filter_upwards [hbound, hV.eventually_gt_atTop 0] with t ht hv
    rw [norm_inv, Real.norm_of_nonneg (pow_nonneg (abs_nonneg _) _), one_mul, pow_mul]
    exact (inv_le_comm₀ ((inv_pos.mpr (pow_pos hv 11)).trans_le ht) (pow_pos hv 11)).mpr ht


private theorem finiteHeckeL_inv_isBigO_oneLine_strip_bound_nat (G : ℂ → ℂ) (a b M : ℝ)
    (hO : G =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc a b)] fun s ↦ |s.im| ^ M) :
    ∃ n : ℕ, ∃ T : ℝ, ∀ z : ℂ, z.re ∈ Icc a b → T ≤ |z.im| → ‖G z‖ ≤ |z.im| ^ n := by
  obtain ⟨n,hn⟩ := exists_nat_gt M
  obtain ⟨c,hc⟩ := Asymptotics.isBigO_iff.mp hO
  simp only [eventually_inf_principal, eventually_comap, eventually_atTop] at hc
  obtain ⟨T,hT⟩ := hc
  refine ⟨n+1, max T (max 1 c), fun z hz htz ↦ ?_⟩
  have hz₁ : 1 ≤ |z.im| := (le_max_left 1 c).trans ((le_max_right ..).trans htz)
  have hzc : c ≤ |z.im| := (le_max_right 1 c).trans ((le_max_right ..).trans htz)
  have h := hT |z.im| ((le_max_left ..).trans htz) z rfl hz
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)] at h
  calc
    ‖G z‖ ≤ c * |z.im| ^ M := h
    _ ≤ |z.im| * |z.im| ^ M := by gcongr
    _ ≤ |z.im| * |z.im| ^ (n:ℝ) := by gcongr
    _ = _ := by rw [Real.rpow_natCast, pow_succ, mul_comm]

private theorem finiteHeckeL_inv_isBigO_oneLine_analytic_and_deriv_strip (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    {n : ℕ} {T : ℝ} (hT : ∀ z : ℂ, z.re ∈ Icc (-1:ℝ) 4 → T ≤ |z.im| → ‖L z‖ ≤ |z.im| ^ n)
    (t : ℝ) (ht : max 2 (T + 2) ≤ |t|) {σ : ℝ} (hσ : σ ∈ Icc (1:ℝ) 2) :
    AnalyticAt ℂ L ⟨σ,t⟩ ∧ ‖deriv L ⟨σ,t⟩‖ ≤ (2*|t|)^n := by
  let s : ℂ := ⟨σ,t⟩
  have him := (le_max_left 2 (T+2)).trans ht
  have hlarge := (le_max_right 2 (T+2)).trans ht
  have hDisk {w : ℂ} (hw : w ∈ Metric.closedBall s 1) :
      w.re ∈ Ioo (-1:ℝ) 4 ∧ T < |w.im| ∧ |w.im| ≤ 2 * |t| := by
    have dist := mem_closedBall_iff_norm.mp hw
    have hre := (Complex.abs_re_le_norm (w - s)).trans dist
    have him' := (Complex.abs_im_le_norm (w - s)).trans dist
    change |w.re - σ| ≤ 1 at hre
    change |w.im - t| ≤ 1 at him'
    rw [abs_le] at hre
    refine ⟨⟨by linarith [hre.1,hσ.1], by linarith [hre.2,hσ.2]⟩, ?_, ?_⟩
    · linarith [(abs_sub_abs_le_abs_sub t w.im).trans (by simpa [abs_sub_comm] using him')]
    · linarith [(abs_sub_abs_le_abs_sub w.im t).trans him']
  have han {w : ℂ} (hw : w ∈ Metric.closedBall s 1) : AnalyticAt ℂ L w := by
    obtain ⟨hRe,hLo,hHi⟩ := hDisk hw
    apply (hL (mem_univ w)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    by_contra! hp
    have hre := (isOpen_Ioo.preimage Complex.continuous_re).mem_nhds hRe
    have him := (isOpen_Ioo.preimage Complex.continuous_im.abs).mem_nhds
      (show w ∈ (fun z : ℂ ↦ |z.im|) ⁻¹' Ioo T (|w.im|+1) from ⟨hLo, by linarith⟩)
    have hb : ∀ᶠ z in 𝓝 w, ‖L z‖ ≤ (|w.im|+1)^n := by
      filter_upwards [hre,him] with z hz h'z
      exact (hT z (Ioo_subset_Icc_self hz) h'z.1.le).trans (pow_le_pow_left₀ (abs_nonneg _) h'z.2.le _)
    have hp' := (tendsto_norm_cobounded_atTop.comp (tendsto_cobounded_of_meromorphicOrderAt_neg hp)).eventually_gt_atTop ((|w.im|+1)^n)
    obtain ⟨_,h,h'⟩ := ((hb.filter_mono nhdsWithin_le_nhds).and hp').exists
    exact h'.not_ge h
  refine ⟨han (Metric.mem_closedBall_self zero_le_one), ?_⟩
  have hDiff : DiffContOnCl ℂ L (Metric.ball s 1) :=
    (show DifferentiableOn ℂ L (Metric.closedBall s 1) from fun w hw ↦
      (han hw).differentiableAt.differentiableWithinAt).diffContOnCl_ball subset_rfl
  have hCircle : ∀ w ∈ Metric.sphere s 1, ‖L w‖ ≤ (2 * |t|)^n := by
    intro w hw
    obtain ⟨hRe,hLo,hHi⟩ := hDisk (Metric.sphere_subset_closedBall hw)
    exact (hT w (Ioo_subset_Icc_self hRe) hLo.le).trans (pow_le_pow_left₀ (abs_nonneg _) hHi _)
  simpa only [div_one] using Complex.norm_deriv_le_of_forall_mem_sphere_norm_le zero_lt_one hDiff hCircle

/-- Reduction to polynomial *upper* bounds. No log derivative or zero-free region is needed. -/
private theorem finiteHeckeL_inv_isBigO_oneLine_reciprocal_of_strip_growth (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (hG : ∃ M : ℝ, L =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc (-1:ℝ) 4)] fun s ↦ |s.im| ^ M)
    (hG₂ : ∃ n : ℕ, ∃ T : ℝ, ∀ z : halfPlane, (z:ℂ).re ≤ 2 → T ≤ |(z:ℂ).im| →
      ‖finiteHeckeL (χ^2) z‖ ≤ |(z:ℂ).im| ^ n) :
    (∀ᶠ t : ℝ in atAbsTop, AnalyticAt ℂ L ⟨1,t⟩ ∧ L ⟨1,t⟩ ≠ 0) ∧
      ∃ N : ℕ, 0 < N ∧ (fun t : ℝ ↦ (L ⟨1,t⟩)⁻¹) =O[atAbsTop] (fun t ↦ |t| ^ N) := by
  obtain ⟨M,hM⟩ := hG
  obtain ⟨n,T,hT⟩ := finiteHeckeL_inv_isBigO_oneLine_strip_bound_nat L _ _ _ hM
  obtain ⟨k,T₂,hT₂⟩ := hG₂
  let m := 2 * (n+k) + 1
  have hb {x : ℝ} (hx : 2 ≤ x) {j : ℕ} (hj : j ≤ n + k) : (2 * x) ^ j ≤ x ^ m := by
    have hx₁ : 1 ≤ x := by linarith
    calc
      (2*x) ^ j ≤ (x*x) ^ j := by gcongr
      _ = x ^ (2*j) := by rw [← sq, pow_mul]
      _ ≤ x ^ m := pow_le_pow_right₀ hx₁ (by dsimp [m]; omega)
  have hlim : Tendsto abs atAbsTop atTop := tendsto_comap
  have hev := hlim.eventually_ge_atTop (max 2 (T+2))
  apply finiteHeckeL_inv_isBigO_oneLine_reciprocal_of_bounds χ L hSeries m (Nat.succ_ne_zero _)
  · filter_upwards [hev] with t ht
    exact (finiteHeckeL_inv_isBigO_oneLine_analytic_and_deriv_strip L hL hT t ht ⟨le_rfl,one_le_two⟩).1
  · filter_upwards [hev] with t ht
    have hs (σ : ℝ) (hσ : σ ∈ Icc (1:ℝ) 2) := finiteHeckeL_inv_isBigO_oneLine_analytic_and_deriv_strip L hL hT t ht hσ
    have hd (σ : ℝ) (hσ : σ ∈ Icc (1:ℝ) 2) : HasDerivAt (fun u : ℝ ↦ L ⟨u,t⟩) (deriv L ⟨σ,t⟩) σ := by
      have he (u : ℝ) : (u:ℂ) + ⟨0,t⟩ = ⟨u,t⟩ := by apply Complex.ext <;> simp
      have hd := ((hs σ hσ).1.differentiableAt.hasDerivAt.comp_of_eq (x := (σ:ℂ))
        ((hasDerivAt_id (σ:ℂ)).add_const (⟨0,t⟩:ℂ)) (he σ).symm).comp_ofReal
      simpa only [he,mul_one,id_eq,Function.comp_def] using hd
    intro d hd'
    have hu : 1+d ∈ Icc (1:ℝ) 2 := ⟨by linarith [hd'.1], by linarith [hd'.2]⟩
    have h := norm_image_sub_le_of_norm_deriv_le_segment' (a := 1) (b := 2)
      (fun σ hσ ↦ (hd σ hσ).hasDerivWithinAt)
      (fun σ hσ ↦ (hs σ (Ico_subset_Icc_self hσ)).2.trans (hb ((le_max_left ..).trans ht) (by omega))) _ hu
    simpa using h
  · filter_upwards [hev, hlim.eventually_ge_atTop T₂] with t ht ht₂
    intro d hd hd'
    have h := hT₂ (⟨⟨1+d,2*t⟩,hd'⟩ : halfPlane) (by change 1+d ≤ 2; linarith [hd.2])
      (by change T₂ ≤ |2*t|; rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]; linarith [abs_nonneg t])
    change _ ≤ |2*t| ^ k at h
    rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] at h
    exact h.trans (hb ((le_max_left ..).trans ht) (by omega))


/-- Paper: Theorem B.6.1.6, p. 640. The reciprocal of the finite Hecke
L-function grows at most polynomially on `Re(s) = 1` at large absolute heights.
Deviation: Eventual analyticity and nonvanishing make the reciprocal well-defined. -/
theorem finiteHeckeL_inv_isBigO_oneLine (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s) :
    (∀ᶠ t : ℝ in atAbsTop, AnalyticAt ℂ L ⟨1, t⟩ ∧ L ⟨1, t⟩ ≠ 0) ∧
      ∃ N : ℕ, 0 < N ∧ (fun t : ℝ ↦ (L ⟨1, t⟩)⁻¹) =O[atAbsTop] (fun t ↦ |t| ^ N) := by
  apply finiteHeckeL_inv_isBigO_oneLine_reciprocal_of_strip_growth χ L hL hSeries
  · obtain ⟨M,_,hM⟩ := finiteHeckeL_continuation_isBigO_rpow χ L hL hSeries (-1) 4 (by norm_num)
    exact ⟨M,hM⟩
  · obtain ⟨G,hG,hAgree⟩ := finiteHeckeL_exists_continuation (χ^2)
    obtain ⟨M,_,hM⟩ := finiteHeckeL_continuation_isBigO_rpow (χ^2) G hG hAgree 1 2 one_lt_two
    obtain ⟨n,T,hT⟩ := finiteHeckeL_inv_isBigO_oneLine_strip_bound_nat G _ _ _ hM
    exact ⟨n,T,fun z hz ht ↦ hAgree z ▸ hT z ⟨z.2.le,hz⟩ ht⟩

-- TODO(paper-gap): Equation (B.6.1.23) uses the finite L-factors. Its χ²
-- argument has height 2t, which (B.6.1.28) must retain.
-- TODO(paper-gap): The upper bound in (B.6.1.28) uses the critical-strip exponent
-- for σ > 1, where that exponent can be negative and the Euler factors need not decay.

/-- A continuation of the completed L-function with the same order as `L` on `Re s > 0`. -/
private theorem finiteHeckeL_zeroFreeRegion_completed (F : Type*) [Field F] [NumberField F]
    (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s) :
    ∃ Λ : ℂ → ℂ, MeromorphicNFOn Λ univ ∧ (∀ s : halfPlane, Λ s = completedHeckeL χ s) ∧
      ∀ s : ℂ, 0 < s.re → meromorphicOrderAt Λ s = meromorphicOrderAt L s := by
  have hΓ (s : ℂ) (hs : 0 < s.re) : AnalyticAt ℂ (heckeGammaFactor χ) s :=
    DifferentiableOn.analyticAt (s := Complex.re ⁻¹' Ioi 0)
      (fun w hw ↦ (differentiableAt_heckeGammaFactor_of_re_pos χ hw).differentiableWithinAt)
      ((isOpen_Ioi.preimage Complex.continuous_re).mem_nhds hs)
  let M : ℂ → ℂ := fun w ↦ heckeGammaFactor χ w * L w
  have hM : MeromorphicOn M univ := fun x _ ↦
    (meromorphic_heckeGammaFactor χ x).mul (hL (mem_univ x)).meromorphicAt
  refine ⟨toMeromorphicNFOn M univ, meromorphicNFOn_toMeromorphicNFOn _ _, fun s ↦ ?_,
    fun s hs ↦ ?_⟩
  · have hs : 0 < (s : ℂ).re := zero_lt_one.trans s.property
    have hMan : AnalyticAt ℂ M s :=
      (hΓ s hs).mul (finiteHeckeL_logDeriv_hasSum_ideals χ L hL hSeries s).1
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hM (mem_univ _),
      toMeromorphicNFAt_eq_self.mpr hMan.meromorphicNFAt]
    simp [M, hSeries s, completedHeckeL, finiteHeckeL]
  · rw [meromorphicOrderAt_toMeromorphicNFOn hM (mem_univ _)]
    exact meromorphicOrderAt_mul_of_ne_zero (hΓ s hs) (heckeGammaFactor_ne_zero_of_re_pos χ hs)

/-- No zero on or to the right of `Re s = 1`. -/
private theorem finiteHeckeL_zeroFreeRegion_order_nonpos (F : Type*) [Field F] [NumberField F]
    (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (s : ℂ) (hs : 1 ≤ s.re) : meromorphicOrderAt L s ≤ 0 := by
  obtain ⟨Λ, hΛ, hΛs, hord⟩ := finiteHeckeL_zeroFreeRegion_completed F χ L hL hSeries
  by_contra! h
  rw [← hord s (by linarith)] at h
  exact (completedHeckeL_continuation_zeros χ Λ hΛ hΛs (by linarith) h).not_ge hs

/-- On `Re s > 0` the continuation has at most one pole, and it is simple. -/
private theorem finiteHeckeL_zeroFreeRegion_poles (F : Type*) [Field F] [NumberField F]
    (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s) :
    ∃ p : ℂ, ∀ s : ℂ, 0 < s.re →
      (-1 ≤ meromorphicOrderAt L s) ∧ (s ≠ p → AnalyticAt ℂ L s) := by
  obtain ⟨Λ, hΛ, hΛs, hord⟩ := finiteHeckeL_zeroFreeRegion_completed F χ L hL hSeries
  have hgood (p : ℂ) (hΛp : -1 ≤ meromorphicOrderAt Λ p)
      (han : ∀ s, 0 < s.re → s ≠ p → AnalyticAt ℂ Λ s) :
      ∀ s : ℂ, 0 < s.re → (-1 ≤ meromorphicOrderAt L s) ∧ (s ≠ p → AnalyticAt ℂ L s) := by
    intro s hs
    by_cases hsp : s = p
    · subst hsp
      exact ⟨hord s hs ▸ hΛp, fun h ↦ (h rfl).elim⟩
    · have h0 : 0 ≤ meromorphicOrderAt L s := hord s hs ▸ (han s hs hsp).meromorphicOrderAt_nonneg
      exact ⟨le_trans (by decide) h0,
        fun _ ↦ (hL (mem_univ s)).meromorphicOrderAt_nonneg_iff_analyticAt.mp h0⟩
  by_cases hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1
  · obtain ⟨t, ⟨-, -, h1, han⟩, -⟩ := completedHeckeL_continuation_simplePoles χ Λ hΛ hΛs hχ
    refine ⟨1 + Complex.I * t, hgood _ h1.ge fun s hs hsp ↦ han s ?_⟩
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    refine ⟨fun h ↦ ?_, hsp⟩
    rw [h] at hs
    simp at hs
  · have hD := completedHeckeL_continuation_entire χ Λ hΛ hΛs hχ
    exact ⟨0, hgood 0 (le_trans (by decide) (hD.analyticAt 0).meromorphicOrderAt_nonneg)
      fun s _ _ ↦ hD.analyticAt s⟩

/-- Comparison of Euler products with Dedekind zeta at a real point to the left. -/
private theorem finiteHeckeL_zeroFreeRegion_euler (F : Type*) [Field F] [NumberField F]
    (ψ : U[F]) (s : halfPlane) {y : ℝ} (hy : 1 < y) (hys : y ≤ (s : ℂ).re) :
    ‖finiteHeckeL ψ s‖ ≤ ‖dedekindZeta F y‖ ∧
      1 ≤ ‖finiteHeckeL ψ s‖ * ‖dedekindZeta F y‖ := by
  classical
  have hZ := dedekindZeta_hasProd F (s := (y : ℂ)) (by simpa using hy)
  have hP := finiteHeckeL_hasProd ψ s
  have hfac (v : HeightOneSpectrum (𝓞 F)) :
      ‖finiteHeckeEulerFactor ψ v s‖ ≤ ‖(1 - (v.asIdeal.absNorm : ℂ) ^ (-(y : ℂ)))⁻¹‖ ∧
        1 ≤ ‖finiteHeckeEulerFactor ψ v s‖ * ‖(1 - (v.asIdeal.absNorm : ℂ) ^ (-(y : ℂ)))⁻¹‖ := by
    let q : ℝ := v.asIdeal.absNorm
    have hq : 1 < q := by
      dsimp only [q]
      exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
    have hq₀ : 0 < q := zero_lt_one.trans hq
    let r : ℝ := q ^ (-y)
    have hr : 0 ≤ r := Real.rpow_nonneg hq₀.le _
    have hr₁ : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith)
    have hZr : (v.asIdeal.absNorm : ℂ) ^ (-(y : ℂ)) = (r : ℂ) := by
      change ((q : ℝ) : ℂ) ^ (-(y : ℂ)) = _
      rw [← Complex.ofReal_neg, ← Complex.ofReal_cpow hq₀.le]
    have hZn : ‖(1 - (v.asIdeal.absNorm : ℂ) ^ (-(y : ℂ)))⁻¹‖ = (1 - r)⁻¹ := by
      rw [hZr, norm_inv, ← Complex.ofReal_one, ← Complex.ofReal_sub,
        Complex.norm_of_nonneg (sub_nonneg.mpr hr₁.le)]
    rw [hZn]
    have h1r : 0 < 1 - r := sub_pos.mpr hr₁
    have hge : 1 ≤ (1 - r)⁻¹ := (one_le_inv₀ h1r).mpr (by linarith)
    unfold finiteHeckeEulerFactor
    split_ifs with hu
    · let w : ℂ := (ideleClassNormTwist ψ 0).localValue v * (v.asIdeal.absNorm : ℂ) ^ (-(s : ℂ))
      have hw : ‖w‖ ≤ r := by
        change ‖_ * ((q : ℝ) : ℂ) ^ (-(s : ℂ))‖ ≤ _
        rw [norm_mul, norm_ideleClassNormTwist_zero_localValue, one_mul,
          Complex.norm_cpow_eq_rpow_re_of_pos hq₀, Complex.neg_re]
        exact Real.rpow_le_rpow_of_exponent_le hq.le (by linarith)
      have hlo : 1 - r ≤ ‖1 - w‖ := by
        have := norm_sub_norm_le (1 : ℂ) w
        rw [norm_one] at this
        linarith
      have hhi : ‖1 - w‖ ≤ 1 + r := (norm_sub_le _ _).trans (by rw [norm_one]; linarith)
      have hpos : 0 < ‖1 - w‖ := h1r.trans_le hlo
      change ‖(1 - w)⁻¹‖ ≤ _ ∧ 1 ≤ ‖(1 - w)⁻¹‖ * _
      rw [norm_inv]
      refine ⟨inv_anti₀ h1r hlo, ?_⟩
      rw [← mul_inv, one_le_inv₀ (mul_pos hpos h1r)]
      calc ‖1 - w‖ * (1 - r) ≤ (1 + r) * (1 - r) := by gcongr
        _ ≤ 1 := by nlinarith
    · simp only [norm_one, one_mul]
      exact ⟨hge, hge⟩
  constructor
  · apply le_of_tendsto_of_tendsto' hP.norm hZ.norm
    intro T
    simp only [norm_prod]
    gcongr with v
    exact (hfac v).1
  · apply ge_of_tendsto' (hP.norm.mul hZ.norm)
    intro T
    simp only [norm_prod, ← Finset.prod_mul_distrib]
    exact Finset.one_le_prod₀ fun v _ ↦ (hfac v).2

/-- `-1 ≤ x < 0` in `WithTop ℤ` forces `x = -1`. -/
private theorem finiteHeckeL_zeroFreeRegion_eq_neg_one (x : WithTop ℤ) (h₁ : -1 ≤ x) (h₂ : x < 0) :
    x = -1 := by
  induction x using WithTop.recTopCoe with
  | top => exact absurd h₂ (by simp)
  | coe n =>
    have h₁' : (-1 : ℤ) ≤ n := WithTop.coe_le_coe.mp h₁
    have h₂' : n < 0 := WithTop.coe_lt_coe.mp h₂
    have : n = -1 := by omega
    rw [this]
    rfl

/-- A polynomial bound with exponent `d / 4 + 2` on the strip `1/2 ≤ Re s ≤ 5/2` at large
heights, obtained by convexity of the growth order. -/
private theorem finiteHeckeL_zeroFreeRegion_growth (F : Type*) [Field F] [NumberField F]
    (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s) :
    ∃ C T : ℝ, 0 < C ∧ 1 ≤ T ∧ ∀ u : ℂ, u.re ∈ Icc (1 / 2 : ℝ) (5 / 2) → T ≤ |u.im| →
      ‖L u‖ ≤ C * |u.im| ^ ((Module.finrank ℚ F : ℝ) / 4 + 2) := by
  set d : ℝ := (Module.finrank ℚ F : ℝ) with hd
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  obtain ⟨p, hp⟩ := finiteHeckeL_zeroFreeRegion_poles F χ L hL hSeries
  have hf : MeromorphicNFOn L (Complex.re ⁻¹' Ioi (1 / 4 : ℝ)) := fun x _ ↦ hL (mem_univ x)
  have hFinite : {s : ℂ | (1 / 4 : ℝ) < s.re ∧ meromorphicOrderAt L s < 0}.Finite := by
    apply (finite_singleton p).subset
    rintro s ⟨hs, hneg⟩
    by_contra hsp
    have := ((hp s (by linarith)).2 hsp).meromorphicOrderAt_nonneg
    exact hneg.not_ge this
  have hSimple : ∀ s : ℂ, (1 / 4 : ℝ) < s.re → meromorphicOrderAt L s < 0 →
      meromorphicOrderAt L s = -1 := fun s hs hneg ↦
    finiteHeckeL_zeroFreeRegion_eq_neg_one _ (hp s (by linarith)).1 hneg
  -- bound to the right of `Re s = 1`
  have hRight (s : ℂ) (y : ℝ) (hy : 1 < y) (hys : y ≤ s.re) : ‖L s‖ ≤ ‖dedekindZeta F y‖ := by
    have hs : s ∈ halfPlane := show 1 < s.re by linarith
    rw [show L s = finiteHeckeL χ ⟨s, hs⟩ from hSeries ⟨s, hs⟩]
    exact (finiteHeckeL_zeroFreeRegion_euler F χ ⟨s, hs⟩ hy hys).1
  have hHeight : Tendsto (fun z : ℂ ↦ |z.im|) atHeight atTop := tendsto_comap
  have hGrowth : ∃ ξ : ℝ, 0 < ξ ∧
      L =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Ioi (1 / 4 : ℝ))] fun s ↦ |s.im| ^ ξ := by
    obtain ⟨M, hM, hO⟩ := finiteHeckeL_continuation_isBigO_rpow χ L hL hSeries (1 / 4) 3
      (by norm_num)
    refine ⟨M, hM, ?_⟩
    have hO' : L =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Ici 3)] fun s ↦ |s.im| ^ M := by
      refine Asymptotics.IsBigO.of_bound ‖dedekindZeta F 3‖ ?_
      rw [eventually_inf_principal]
      filter_upwards [hHeight.eventually_ge_atTop 1] with s hs hs3
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      calc ‖L s‖ ≤ ‖dedekindZeta F 3‖ := hRight s 3 (by norm_num) hs3
        _ ≤ ‖dedekindZeta F 3‖ * |s.im| ^ M :=
          le_mul_of_one_le_right (norm_nonneg _) (Real.one_le_rpow hs hM.le)
    refine (hO.sup hO').mono ?_
    rw [← inf_sup_left, sup_principal, ← preimage_union]
    refine inf_le_inf_left _ (principal_mono.mpr (preimage_mono fun x (hx : 1 / 4 < x) ↦ ?_))
    rcases le_or_gt x 3 with h | h
    · exact Or.inl ⟨hx.le, h⟩
    · exact Or.inr (show 3 ≤ x from h.le)
  have hO := isBigO_verticalGrowthOrder_add hf hFinite hSimple hGrowth (1 / 2) (5 / 2)
    (by norm_num) (by norm_num) 1 one_pos
  -- the growth order is at most `d / 4 + 1` on the strip
  have hμ (σ : ℝ) (hσ : σ ∈ Icc (1 / 2 : ℝ) (5 / 2)) :
      (verticalGrowthOrder L σ).toReal ≤ d / 4 + 1 := by
    rcases le_or_gt σ 1 with h1 | h1
    · obtain ⟨C, -, hC⟩ := finiteHeckeL_continuation_convexity_bound χ L hL hSeries
      have hline := (hC 1 one_pos).isBigO.mono (inf_le_inf_left _ (principal_mono.mpr
        (preimage_mono (show ({σ} : Set ℝ) ⊆ Icc 0 1 from
          singleton_subset_iff.mpr ⟨by linarith [hσ.1], h1⟩))))
      have hline' : L =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' {σ})]
          fun s ↦ |s.im| ^ (d * ((1 - σ) / 2) + 1) := by
        refine hline.congr' EventuallyEq.rfl ?_
        rw [EventuallyEq, eventually_inf_principal]
        exact Eventually.of_forall fun s (hs : s.re = σ) ↦ by rw [hs]
      refine (verticalGrowthOrder_toReal_le_of_isBigO (by nlinarith [hσ.1]) hline').trans ?_
      nlinarith [hσ.1]
    · have hline : L =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' {σ})] fun s ↦ |s.im| ^ (0 : ℝ) := by
        refine Asymptotics.IsBigO.of_bound ‖dedekindZeta F σ‖ ?_
        rw [eventually_inf_principal]
        refine Eventually.of_forall fun s (hs : s.re = σ) ↦ ?_
        rw [Real.rpow_zero, norm_one, mul_one]
        exact hRight s σ h1 hs.ge
      exact (verticalGrowthOrder_toReal_le_of_isBigO le_rfl hline).trans (by positivity)
  obtain ⟨C, hC, hC'⟩ := Asymptotics.isBigO_iff'.mp hO
  rw [eventually_inf_principal, eventually_comap, eventually_atTop] at hC'
  obtain ⟨T, hT⟩ := hC'
  refine ⟨C, max T 1, hC, le_max_right _ _, fun u hu huT ↦ ?_⟩
  have h1 : 1 ≤ |u.im| := (le_max_right _ _).trans huT
  have h := hT |u.im| ((le_max_left _ _).trans huT) u rfl hu
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)] at h
  refine h.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le h1 ?_) hC.le)
  linarith [hμ u.re hu]

/-- The trivial character is unramified with local value one, and the local value of `χ ^ 2`
is the square of that of `χ`. -/
private theorem finiteHeckeL_zeroFreeRegion_local (F : Type*) [Field F] [NumberField F]
    (χ : U[F]) (v : HeightOneSpectrum (𝓞 F)) :
    (ideleClassNormTwist (1 : U[F]) 0).IsUnramifiedAt v ∧
      (ideleClassNormTwist (1 : U[F]) 0).localValue v = 1 ∧
      ((ideleClassNormTwist χ 0).IsUnramifiedAt v →
        (ideleClassNormTwist (χ ^ 2) 0).IsUnramifiedAt v) ∧
      (ideleClassNormTwist (χ ^ 2) 0).localValue v =
        ((ideleClassNormTwist χ 0).localValue v) ^ 2 := by
  have hres (ψ : U[F]) (u : (v.adicCompletion F)ˣ) :
      (ideleClassNormTwist ψ 0).restrict v (u : v.adicCompletion F) =
        (ψ (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u) : ℂ) := by
    rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
    change (ψ _ : ℂ) * _ ^ (0 : ℂ) = _
    rw [Complex.cpow_zero, mul_one]
  have hres_one (u : (v.adicCompletion F)ˣ) :
      (ideleClassNormTwist (1 : U[F]) 0).restrict v (u : v.adicCompletion F) = 1 := by
    rw [hres, PontryaginDual.one_apply, Circle.coe_one]
  have hres_sq (u : (v.adicCompletion F)ˣ) :
      (ideleClassNormTwist (χ ^ 2) 0).restrict v (u : v.adicCompletion F) =
        ((ideleClassNormTwist χ 0).restrict v (u : v.adicCompletion F)) ^ 2 := by
    rw [hres, hres]
    rfl
  let val : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
  let u := Units.mk0 (val.exists_isUniformizer_of_isCyclic_of_nontrivial.choose : v.adicCompletion F)
    val.exists_isUniformizer_of_isCyclic_of_nontrivial.choose_spec.ne_zero
  refine ⟨HeckeCharacter.isUnramifiedAt_iff.mpr fun u ↦
      hres_one (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u), hres_one u,
    fun hu ↦ HeckeCharacter.isUnramifiedAt_iff.mpr fun u ↦ ?_, hres_sq u⟩
  rw [show (ideleClassNormTwist (χ ^ 2) 0).restrict v u =
      ((ideleClassNormTwist χ 0).restrict v u) ^ 2 from
    hres_sq (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u),
    hu.restrict_apply_unit_eq_one, one_pow]

/-- The elementary inequality `3 + 4 cos θ + cos 2θ ≥ 0`, with a possibly ramified phase. -/
private theorem finiteHeckeL_zeroFreeRegion_trig (x : ℝ) (hx : 0 ≤ x) (a a₂ e : ℂ)
    (he : ‖e‖ = 1) (h : (‖a‖ = 1 ∧ a₂ = a ^ 2) ∨ (a = 0 ∧ ‖a₂‖ ≤ 1)) :
    0 ≤ 3 * x + 4 * ((x : ℂ) * (a * e)).re + ((x : ℂ) * (a₂ * e ^ 2)).re := by
  rcases h with ⟨ha, rfl⟩ | ⟨rfl, ha₂⟩
  · obtain ⟨w, hw⟩ : ∃ w, w = a * e := ⟨_, rfl⟩
    have hw1 : ‖w‖ = 1 := by rw [hw, norm_mul, ha, he, one_mul]
    have hsq : w.re * w.re + w.im * w.im = 1 := by
      rw [← Complex.normSq_apply, ← Complex.sq_norm, hw1, one_pow]
    have h2 : a ^ 2 * e ^ 2 = w ^ 2 := by rw [hw, mul_pow]
    rw [h2, ← hw, Complex.re_ofReal_mul, Complex.re_ofReal_mul, sq, Complex.mul_re]
    nlinarith [mul_nonneg hx (sq_nonneg (1 + w.re))]
  · have hn : ‖(x : ℂ) * (a₂ * e ^ 2)‖ ≤ x := by
      rw [norm_mul, norm_mul, norm_pow, he, one_pow, mul_one, Complex.norm_of_nonneg hx]
      exact mul_le_of_le_one_right hx ha₂
    have := (abs_le.mp ((Complex.abs_re_le_norm _).trans hn)).1
    simp only [zero_mul, mul_zero, Complex.zero_re]
    linarith

/-- The termwise de la Vallée Poussin inequality for the ideal series of `-L'/L`. -/
private theorem finiteHeckeL_zeroFreeRegion_term (F : Type*) [Field F] [NumberField F]
    (χ : U[F]) (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (σ γ : ℝ) :
    (3 * (-heckeIdealVonMangoldt (ideleClassNormTwist (1 : U[F]) 0) I /
        (I.absNorm : ℂ) ^ (σ : ℂ)) +
      4 * (-heckeIdealVonMangoldt (ideleClassNormTwist χ 0) I /
        (I.absNorm : ℂ) ^ (⟨σ, γ⟩ : ℂ)) +
      -heckeIdealVonMangoldt (ideleClassNormTwist (χ ^ 2) 0) I /
        (I.absNorm : ℂ) ^ (⟨σ, 2 * γ⟩ : ℂ)).re ≤ 0 := by
  classical
  by_cases h : ∃ v : HeightOneSpectrum (𝓞 F), ∃ k : ℕ, 0 < k ∧ I = v.asIdeal ^ k
  · obtain ⟨v, k, hk, rfl⟩ := h
    obtain ⟨hu₀, hv₀, hu₂, hv₂⟩ := finiteHeckeL_zeroFreeRegion_local F χ v
    set N : ℕ := (v.asIdeal ^ k).absNorm with hNdef
    have hN : 0 < N := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
    have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    set lam : ℝ := Real.log (v.asIdeal.absNorm : ℝ)
    have hlam : 0 ≤ lam := Real.log_natCast_nonneg _
    have hc (ψ : U[F]) : heckeIdealVonMangoldt (ideleClassNormTwist ψ 0) (v.asIdeal ^ k) =
        (if (ideleClassNormTwist ψ 0).IsUnramifiedAt v then
          (ideleClassNormTwist ψ 0).localValue v ^ k else 0) * (lam : ℂ) := by
      rw [heckeIdealVonMangoldt, heckeIdealValue_prime_pow _ v hk, idealVonMangoldt_prime_pow v hk]
    set x : ℝ := (N : ℝ) ^ (-σ)
    have hx : 0 ≤ x := Real.rpow_nonneg (Nat.cast_nonneg _) _
    set e : ℂ := (N : ℂ) ^ (-((γ : ℂ) * Complex.I))
    have he : ‖e‖ = 1 := by
      rw [Complex.norm_natCast_cpow_of_pos hN]
      simp
    have hpow (τ : ℝ) : ((N : ℂ) ^ (⟨σ, τ⟩ : ℂ))⁻¹ =
        (x : ℂ) * (N : ℂ) ^ (-((τ : ℂ) * Complex.I)) := by
      have hsplit : (⟨σ, τ⟩ : ℂ) = (σ : ℂ) + (τ : ℂ) * Complex.I := by
        apply Complex.ext <;> simp
      rw [hsplit, Complex.cpow_add _ _ hNC, mul_inv, Complex.cpow_neg]
      congr 1
      rw [← Complex.cpow_neg, show (N : ℂ) = ((N : ℝ) : ℂ) by norm_cast, ← Complex.ofReal_neg,
        ← Complex.ofReal_cpow (Nat.cast_nonneg _)]
    have h0 : ((N : ℂ) ^ (σ : ℂ))⁻¹ = (x : ℂ) := by
      have := hpow 0
      rw [show (⟨σ, 0⟩ : ℂ) = (σ : ℂ) from rfl] at this
      simpa using this
    have h1 : ((N : ℂ) ^ (⟨σ, γ⟩ : ℂ))⁻¹ = (x : ℂ) * e := hpow γ
    have h2 : ((N : ℂ) ^ (⟨σ, 2 * γ⟩ : ℂ))⁻¹ = (x : ℂ) * e ^ 2 := by
      rw [hpow, ← Complex.cpow_nat_mul]
      congr 2
      push_cast
      ring
    simp only [div_eq_mul_inv, h0, h1, h2, hc, hv₀, one_pow, ite_eq_left hu₀]
    set a : ℂ := if (ideleClassNormTwist χ 0).IsUnramifiedAt v then
      (ideleClassNormTwist χ 0).localValue v ^ k else 0
    set a₂ : ℂ := if (ideleClassNormTwist (χ ^ 2) 0).IsUnramifiedAt v then
      (ideleClassNormTwist (χ ^ 2) 0).localValue v ^ k else 0
    have hcase : (‖a‖ = 1 ∧ a₂ = a ^ 2) ∨ (a = 0 ∧ ‖a₂‖ ≤ 1) := by
      by_cases hu : (ideleClassNormTwist χ 0).IsUnramifiedAt v
      · left
        simp only [a, a₂, ite_eq_left hu, ite_eq_left (hu₂ hu), hv₂, norm_pow,
          norm_ideleClassNormTwist_zero_localValue, one_pow, true_and]
        ring
      · right
        refine ⟨ite_eq_right hu, ?_⟩
        simp only [a₂]
        split_ifs
        · rw [norm_pow, norm_ideleClassNormTwist_zero_localValue, one_pow]
        · simp
    have key := finiteHeckeL_zeroFreeRegion_trig x hx a a₂ e he hcase
    have hexp : 3 * (-(1 * (lam : ℂ)) * (x : ℂ)) + 4 * (-(a * (lam : ℂ)) * ((x : ℂ) * e)) +
        -(a₂ * (lam : ℂ)) * ((x : ℂ) * e ^ 2) =
        -((lam : ℂ) * (3 * (x : ℂ) + 4 * ((x : ℂ) * (a * e)) + (x : ℂ) * (a₂ * e ^ 2))) := by
      ring
    rw [hexp, Complex.neg_re, Complex.re_ofReal_mul, neg_nonpos]
    apply mul_nonneg hlam
    simpa [Complex.add_re, Complex.mul_re] using key
  · simp [heckeIdealVonMangoldt, idealVonMangoldt, h]

/-- The de la Vallée Poussin inequality for logarithmic derivatives:
`Re (3 L₀'/L₀(σ) + 4 L'/L(σ + iγ) + L₂'/L₂(σ + 2iγ)) ≤ 0` for `σ > 1`. -/
private theorem finiteHeckeL_zeroFreeRegion_three_four_one (F : Type*) [Field F] [NumberField F]
    (χ : U[F]) (L L₀ L₂ : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (hL₀ : MeromorphicNFOn L₀ univ) (hS₀ : ∀ s : halfPlane, L₀ s = finiteHeckeL (1 : U[F]) s)
    (hL₂ : MeromorphicNFOn L₂ univ) (hS₂ : ∀ s : halfPlane, L₂ s = finiteHeckeL (χ ^ 2) s)
    (σ : ℝ) (hσ : 1 < σ) (γ : ℝ) :
    0 ≤ 3 * -(logDeriv L₀ σ).re + 4 * -(logDeriv L ⟨σ, γ⟩).re +
      -(logDeriv L₂ ⟨σ, 2 * γ⟩).re := by

  let s₀ : halfPlane := ⟨(σ : ℂ), show 1 < (σ : ℂ).re by simpa using hσ⟩
  let s₁ : halfPlane := ⟨⟨σ, γ⟩, show 1 < σ from hσ⟩
  let s₂ : halfPlane := ⟨⟨σ, 2 * γ⟩, show 1 < σ from hσ⟩
  have h₀ := (finiteHeckeL_logDeriv_hasSum_ideals (1 : U[F]) L₀ hL₀ hS₀ s₀).2.2
  have h₁ := (finiteHeckeL_logDeriv_hasSum_ideals χ L hL hSeries s₁).2.2
  have h₂ := (finiteHeckeL_logDeriv_hasSum_ideals (χ ^ 2) L₂ hL₂ hS₂ s₂).2.2
  have H := Complex.hasSum_re (((h₀.mul_left 3).add (h₁.mul_left 4)).add h₂)
  have hle : (3 * logDeriv L₀ (s₀ : ℂ) + 4 * logDeriv L (s₁ : ℂ) +
      logDeriv L₂ (s₂ : ℂ)).re ≤ 0 := H.nonpos fun I ↦ by
    have := finiteHeckeL_zeroFreeRegion_term F χ I.1 I.2 σ γ
    exact this
  simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul,
    sub_zero] at hle
  change 0 ≤ 3 * -(logDeriv L₀ (s₀ : ℂ)).re + 4 * -(logDeriv L (s₁ : ℂ)).re +
    -(logDeriv L₂ (s₂ : ℂ)).re
  linarith

/-- Near `s = 1` from the right, `-Re L₀'/L₀(σ) ≤ 1/(σ - 1) + C` for the trivial character:
the pole at one is at most simple. -/
private theorem finiteHeckeL_zeroFreeRegion_zeta (F : Type*) [Field F] [NumberField F]
    (L₀ : ℂ → ℂ)
    (hL₀ : MeromorphicNFOn L₀ univ) (hS₀ : ∀ s : halfPlane, L₀ s = finiteHeckeL (1 : U[F]) s) :
    ∃ η C : ℝ, 0 < η ∧ ∀ σ : ℝ, 1 < σ → σ ≤ 1 + η →
      -(logDeriv L₀ σ).re ≤ 1 / (σ - 1) + C := by
  obtain ⟨p, hp⟩ := finiteHeckeL_zeroFreeRegion_poles F 1 L₀ hL₀ hS₀
  have hge := (hp 1 (by simp)).1
  have hreal : Tendsto (fun r : ℝ ↦ (r : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa using (Complex.continuous_ofReal.continuousAt (x := (1 : ℝ))).tendsto.mono_left
        nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      simpa using (show 1 < r from hr).ne'
  have hne (r : ℝ) (hr : 1 < r) : L₀ r ≠ 0 :=
    (finiteHeckeL_logDeriv_hasSum_ideals (1 : U[F]) L₀ hL₀ hS₀
      ⟨(r : ℂ), show 1 < (r : ℂ).re by simpa using hr⟩).2.1
  have htop : meromorphicOrderAt L₀ 1 ≠ ⊤ := by
    intro h
    obtain ⟨r, hr, hr1⟩ := ((hreal.eventually (meromorphicOrderAt_eq_top_iff.mp h)).and
      self_mem_nhdsWithin).exists
    exact hne r hr1 hr
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp htop
  have hm1 : -1 ≤ m := by
    rw [← hm] at hge
    exact WithTop.coe_le_coe.mp hge
  obtain ⟨g, hg, hg1, hEq⟩ := (meromorphicOrderAt_eq_int_iff (hL₀ (mem_univ 1)).meromorphicAt).mp
    hm.symm
  have hcont : ContinuousAt (logDeriv g) 1 :=
    hg.deriv.continuousAt.div hg.continuousAt hg1
  have hbound : ∀ᶠ z in 𝓝 (1 : ℂ), ‖logDeriv g z‖ ≤ ‖logDeriv g 1‖ + 1 := by
    filter_upwards [hcont.norm.eventually (gt_mem_nhds (lt_add_one ‖logDeriv g 1‖))] with z hz
    exact hz.le
  have hlog := logDeriv_congr_nhdsNE hEq
  have hev : ∀ᶠ z in 𝓝[≠] (1 : ℂ),
      logDeriv L₀ z = (m : ℂ) / (z - 1) + logDeriv g z ∧
        ‖logDeriv g z‖ ≤ ‖logDeriv g 1‖ + 1 := by
    filter_upwards [hlog, nhdsWithin_le_nhds hbound, nhdsWithin_le_nhds hg.eventually_analyticAt,
      nhdsWithin_le_nhds (hg.continuousAt.eventually_ne hg1), self_mem_nhdsWithin]
      with z hz hb han hgz hz1
    refine ⟨?_, hb⟩
    have hz1' : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
    have hd : DifferentiableAt ℂ (fun w : ℂ ↦ w - 1) z := differentiableAt_id.sub_const 1
    rw [hz, show (fun w : ℂ ↦ (w - 1) ^ m • g w) = (fun w ↦ (w - 1) ^ m) * g from rfl,
      logDeriv_mul (f := fun w : ℂ ↦ (w - 1) ^ m) z (zpow_ne_zero _ hz1') hgz
      (hd.zpow (Or.inl hz1')) han.differentiableAt, logDeriv_fun_zpow hd]
    congr 1
    rw [logDeriv_apply, deriv_sub_const, deriv_id'']
    field_simp
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp (hreal.eventually hev)
  refine ⟨u - 1, ‖logDeriv g 1‖ + 1, by linarith [hu.out], fun σ hσ hσu ↦ ?_⟩
  obtain ⟨h1, h2⟩ := hsub ⟨hσ, by linarith⟩
  rw [h1, Complex.add_re]
  have hre : ((m : ℂ) / ((σ : ℂ) - 1)).re = m / (σ - 1) := by
    rw [show (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) by push_cast; ring, show (m : ℂ) = ((m : ℝ) : ℂ) by
      norm_cast, ← Complex.ofReal_div, Complex.ofReal_re]
  rw [hre]
  have hσ1 : 0 < σ - 1 := by linarith
  have hm' : -(m : ℝ) / (σ - 1) ≤ 1 / (σ - 1) := by
    apply div_le_div_of_nonneg_right _ hσ1.le
    have : (-1 : ℝ) ≤ m := by exact_mod_cast hm1
    linarith
  have := (abs_le.mp ((Complex.abs_re_le_norm _).trans h2)).1
  rw [neg_div] at hm'
  linarith

/-- Landau's lemma on the disc of radius one about `c`, with the radii `1/2 < 3/4 < 7/8 < 1`,
an upper bound `M` on the disc and a lower bound `δ` at the centre. -/
private theorem finiteHeckeL_zeroFreeRegion_landau (f : ℂ → ℂ) (c z : ℂ) (M δ : ℝ) (hδ : 0 < δ)
    (hf : ∀ u ∈ Metric.closedBall c 1, AnalyticAt ℂ f u)
    (hM : ∀ u ∈ Metric.closedBall c 1, ‖f u‖ ≤ M) (hc : δ ≤ ‖f c‖)
    (hz : z ∈ Metric.closedBall c (1 / 2)) (hfz : f z ≠ 0)
    (hS : ∀ ρ ∈ Metric.closedBall c (3 / 4), f ρ = 0 → ρ.re ≤ z.re) :
    -(logDeriv f z).re ≤
        landauConstant (1 / 2) (3 / 4) (7 / 8) 1 * Real.log (max (M / δ) 2) ∧
      ∀ ρ₀ ∈ Metric.closedBall c (3 / 4), f ρ₀ = 0 →
        -(logDeriv f z).re ≤ -(1 / (z - ρ₀)).re +
          landauConstant (1 / 2) (3 / 4) (7 / 8) 1 * Real.log (max (M / δ) 2) := by
  have hB : 1 < max (M / δ) 2 := lt_of_lt_of_le one_lt_two (le_max_right _ _)
  have hfc : f c ≠ 0 := norm_pos_iff.mp (hδ.trans_le hc)
  have hbound : ∀ u ∈ Metric.closedBall c 1, ‖f u / f c‖ ≤ max (M / δ) 2 := by
    intro u hu
    rw [norm_div]
    refine le_trans ?_ (le_max_left _ _)
    calc ‖f u‖ / ‖f c‖ ≤ ‖f u‖ / δ := div_le_div_of_nonneg_left (norm_nonneg _) hδ hc
      _ ≤ M / δ := div_le_div_of_nonneg_right (hM u hu) hδ.le
  exact ⟨landau_neg_re_logDeriv_le_of_forall_re_le hB (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hf hfc hbound hz hfz hS,
    fun ρ₀ hρ₀ hfρ₀ ↦ landau_neg_re_logDeriv_le_of_zero hB (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hf hfc hbound hz hfz hS hρ₀ hfρ₀⟩

/-- `log max(C Z g^E, 2) ≤ log max(C Z, 2) + E log g` for `g ≥ 1`. -/
private theorem finiteHeckeL_zeroFreeRegion_log_le (x E g : ℝ) (hE : 0 ≤ E)
    (hg : 1 ≤ g) :
    Real.log (max (x * g ^ E) 2) ≤ Real.log (max x 2) + E * Real.log g := by
  have hgE : 1 ≤ g ^ E := Real.one_le_rpow hg hE
  have hm : 0 < max x 2 := lt_of_lt_of_le two_pos (le_max_right _ _)
  calc Real.log (max (x * g ^ E) 2) ≤ Real.log (max x 2 * g ^ E) := by
        apply Real.log_le_log (lt_of_lt_of_le two_pos (le_max_right _ _))
        apply max_le
        · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
        · exact (le_max_right x 2).trans (le_mul_of_one_le_right hm.le hgE)
    _ = Real.log (max x 2) + E * Real.log g := by
        rw [Real.log_mul hm.ne' (by positivity), Real.log_rpow (by linarith)]

/-- The final inequality of de la Vallée Poussin's argument. -/
private theorem finiteHeckeL_zeroFreeRegion_final (M Lg σ β : ℝ) (hM : 0 < M) (hLg : 0 < Lg)
    (hσ : σ = 1 + 1 / (2 * M) / Lg) (hβ : 1 - 1 / (15 * M) / Lg ≤ β) (hβ1 : β < 1)
    (h : 0 ≤ 3 / (σ - 1) - 4 / (σ - β) + M * Lg) : False := by
  have hx : 0 < σ - β := by
    rw [hσ]
    have : 0 < 1 / (2 * M) / Lg := by positivity
    linarith
  have hx' : σ - β ≤ 17 / (30 * M * Lg) := by
    have : 1 / (2 * M) / Lg + 1 / (15 * M) / Lg = 17 / (30 * M * Lg) := by
      field_simp
      ring
    rw [hσ]
    linarith
  have h3 : 3 / (σ - 1) = 6 * M * Lg := by
    rw [hσ]
    field_simp
    ring
  have h4 : 120 * M * Lg / 17 ≤ 4 / (σ - β) := by
    rw [le_div_iff₀ hx]
    calc 120 * M * Lg / 17 * (σ - β) ≤ 120 * M * Lg / 17 * (17 / (30 * M * Lg)) :=
          mul_le_mul_of_nonneg_left hx' (by positivity)
      _ = 4 := by field_simp; ring
  have : 0 < M * Lg := by positivity
  nlinarith

/-- Geometry of the discs: a point of `closedBall ⟨3/2, τ⟩ 1` has real part in `[1/2, 5/2]`
and imaginary part within one of `τ`. -/
private theorem finiteHeckeL_zeroFreeRegion_disc (τ : ℝ) (u : ℂ)
    (hu : u ∈ Metric.closedBall (⟨3 / 2, τ⟩ : ℂ) 1) :
    u.re ∈ Icc (1 / 2 : ℝ) (5 / 2) ∧ |u.im - τ| ≤ 1 := by
  have h := mem_closedBall_iff_norm.mp hu
  have hre := (Complex.abs_re_le_norm _).trans h
  have him := (Complex.abs_im_le_norm _).trans h
  simp only [Complex.sub_re, Complex.sub_im] at hre him
  rw [abs_le] at hre
  exact ⟨⟨by linarith [hre.1], by linarith [hre.2]⟩, him⟩

/-- A real point `⟨x, τ⟩` lies in `closedBall ⟨3/2, τ⟩ r` when `|x - 3/2| ≤ r`. -/
private theorem finiteHeckeL_zeroFreeRegion_mem_ball (τ x r : ℝ) (h : |x - 3 / 2| ≤ r) :
    (⟨x, τ⟩ : ℂ) ∈ Metric.closedBall (⟨3 / 2, τ⟩ : ℂ) r := by
  rw [mem_closedBall_iff_norm]
  have : (⟨x, τ⟩ : ℂ) - ⟨3 / 2, τ⟩ = ((x - 3 / 2 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  rwa [this, Complex.norm_real, Real.norm_eq_abs]

/-- At a point with `Re s ≥ 1` where `L` is analytic, `L` does not vanish. -/
private theorem finiteHeckeL_zeroFreeRegion_ne_zero (F : Type*) [Field F] [NumberField F]
    (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (x : ℂ) (hx : 1 ≤ x.re) (han : AnalyticAt ℂ L x) : L x ≠ 0 :=
  (hL (mem_univ x)).meromorphicOrderAt_eq_zero_iff.mp (le_antisymm
    (finiteHeckeL_zeroFreeRegion_order_nonpos F χ L hL hSeries x hx) han.meromorphicOrderAt_nonneg)

/-- At large heights, zeros of `L` satisfy `β < 1 - c / (d log |γ|)` with an absolute `c`. -/
private theorem finiteHeckeL_zeroFreeRegion_eventual (F : Type*) [Field F] [NumberField F]
    (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s) :
    ∃ T₀ : ℝ, 3 ≤ T₀ ∧ ∀ ρ : ℂ, T₀ ≤ |ρ.im| → 0 < meromorphicOrderAt L ρ →
      ρ.re < 1 - 1 / (15 * (30 * landauConstant (1 / 2) (3 / 4) (7 / 8) 1 + 1)) /
        ((Module.finrank ℚ F : ℝ) * Real.log |ρ.im|) := by
  set K := landauConstant (1 / 2) (3 / 4) (7 / 8) 1 with hKdef
  have hK : 0 < K := landauConstant_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  set M := 30 * K + 1 with hMdef
  have hM : 0 < M := by positivity
  set d : ℝ := (Module.finrank ℚ F : ℝ) with hd
  have hd1 : 1 ≤ d := by
    rw [hd]
    exact_mod_cast Module.finrank_pos
  obtain ⟨L₀, hL₀, hS₀⟩ := finiteHeckeL_exists_continuation (1 : U[F])
  obtain ⟨L₂, hL₂, hS₂⟩ := finiteHeckeL_exists_continuation (χ ^ 2)
  obtain ⟨η, C₀, hη, hzeta⟩ := finiteHeckeL_zeroFreeRegion_zeta F L₀ hL₀ hS₀
  obtain ⟨p, hp⟩ := finiteHeckeL_zeroFreeRegion_poles F χ L hL hSeries
  obtain ⟨p₂, hp₂⟩ := finiteHeckeL_zeroFreeRegion_poles F (χ ^ 2) L₂ hL₂ hS₂
  obtain ⟨C₁, T₁, hC₁, hT₁, hgr₁⟩ := finiteHeckeL_zeroFreeRegion_growth F χ L hL hSeries
  obtain ⟨C₂, T₂, hC₂, hT₂, hgr₂⟩ := finiteHeckeL_zeroFreeRegion_growth F (χ ^ 2) L₂ hL₂ hS₂
  set Z := ‖dedekindZeta F ((3 / 2 : ℝ) : ℂ)‖ with hZdef
  set E : ℝ := d / 4 + 2 with hE
  have hE0 : 0 ≤ E := by positivity
  have hEd : E ≤ 3 * d := by rw [hE]; linarith
  -- lower bound at the centres
  have hlow (ψ : U[F]) (G : ℂ → ℂ) (hG : ∀ s : halfPlane, G s = finiteHeckeL ψ s) (τ : ℝ) :
      0 < Z ∧ 1 / Z ≤ ‖G ⟨3 / 2, τ⟩‖ := by
    have hs : (⟨3 / 2, τ⟩ : ℂ) ∈ halfPlane := show (1 : ℝ) < 3 / 2 by norm_num
    have h := (finiteHeckeL_zeroFreeRegion_euler F ψ ⟨_, hs⟩ (y := 3 / 2) (by norm_num)
      le_rfl).2
    rw [← hG ⟨_, hs⟩, ← hZdef] at h
    have hZ : 0 < Z := by
      rcases (show (0 : ℝ) ≤ Z from norm_nonneg _).lt_or_eq with hZ | hZ
      · exact hZ
      · rw [← hZ, mul_zero] at h
        linarith
    exact ⟨hZ, (div_le_iff₀ hZ).mpr (by simpa using h)⟩
  have hZ : 0 < Z := (hlow 1 L₀ hS₀ 0).1
  set c₁ := Real.log (max (C₁ * Z) 2) with hc₁
  set c₂ := Real.log (max (C₂ * Z) 2) with hc₂
  set Cst := 3 * C₀ + 4 * K * c₁ + K * c₂ with hCst
  refine ⟨max (max 3 (Real.exp 4)) (max (max (T₁ + 1) (T₂ + 1))
    (max (max (|p.im| + 2) (|p₂.im| + 2)) (max (Real.exp Cst) (Real.exp (1 / η))))),
    le_max_of_le_left (le_max_left _ _), ?_⟩
  rintro ⟨β, γ⟩ hγ hord
  simp only [max_le_iff] at hγ
  obtain ⟨⟨hγ3, hγ4⟩, ⟨hγT₁, hγT₂⟩, ⟨hγp, hγp₂⟩, hγC, hγη⟩ := hγ
  change 3 ≤ |γ| at hγ3
  change Real.exp 4 ≤ |γ| at hγ4
  change T₁ + 1 ≤ |γ| at hγT₁
  change T₂ + 1 ≤ |γ| at hγT₂
  change |p.im| + 2 ≤ |γ| at hγp
  change |p₂.im| + 2 ≤ |γ| at hγp₂
  change Real.exp Cst ≤ |γ| at hγC
  change Real.exp (1 / η) ≤ |γ| at hγη
  change β < 1 - 1 / (15 * M) / (d * Real.log |γ|)
  have hγ0 : 0 < |γ| := by linarith
  have hlog4 : 4 ≤ Real.log |γ| := (Real.le_log_iff_exp_le hγ0).mpr hγ4
  have hlogC : Cst ≤ Real.log |γ| := (Real.le_log_iff_exp_le hγ0).mpr hγC
  have hlogη : 1 / η ≤ Real.log |γ| := (Real.le_log_iff_exp_le hγ0).mpr hγη
  set Lg := d * Real.log |γ| with hLg
  have hLg4 : 4 ≤ Lg := by rw [hLg]; nlinarith
  have hLg0 : 0 < Lg := by linarith
  by_contra! hβ
  -- the zero lies left of one
  have hβ1 : β < 1 := by
    by_contra! h
    exact (finiteHeckeL_zeroFreeRegion_order_nonpos F χ L hL hSeries ⟨β, γ⟩ h).not_gt hord
  have ha : 1 / (2 * M) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hc : 1 / (15 * M) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  have hβ34 : 3 / 4 ≤ β := by
    have : 1 / (15 * M) / Lg ≤ 1 / 4 := by
      rw [div_le_iff₀ hLg0]; linarith
    linarith
  set σ := 1 + 1 / (2 * M) / Lg with hσ
  have hσ1 : 1 < σ := by
    have : 0 < 1 / (2 * M) / Lg := by positivity
    linarith
  have hσ2 : σ ≤ 2 := by
    have : 1 / (2 * M) / Lg ≤ 1 := by
      rw [div_le_iff₀ hLg0]; linarith
    linarith
  have hση : σ ≤ 1 + η := by
    have : 1 / (2 * M) / Lg ≤ η := by
      rw [div_le_iff₀ hLg0]
      have h1 : 1 ≤ η * Real.log |γ| := by
        rw [div_le_iff₀ hη] at hlogη; linarith
      nlinarith
    linarith
  -- the three bounds
  have h341 := finiteHeckeL_zeroFreeRegion_three_four_one F χ L L₀ L₂ hL hSeries hL₀ hS₀ hL₂ hS₂
    σ hσ1 γ
  have hX₀ := hzeta σ hσ1 hση
  have hγsq : 3 * |γ| ≤ |γ| ^ 2 := by
    rw [sq]; exact mul_le_mul_of_nonneg_right hγ3 (abs_nonneg γ)
  have hγ2 : |γ| + 1 ≤ |γ| ^ 2 := by linarith
  have hγ2' : 2 * |γ| + 1 ≤ |γ| ^ 2 := by linarith
  have hdisc₁ : ∀ u ∈ Metric.closedBall (⟨3 / 2, γ⟩ : ℂ) 1,
      AnalyticAt ℂ L u ∧ ‖L u‖ ≤ C₁ * (|γ| ^ 2) ^ E := by
    intro u hu
    obtain ⟨hre, him⟩ := finiteHeckeL_zeroFreeRegion_disc γ u hu
    have hlo : |γ| - 1 ≤ |u.im| := by
      have := abs_sub_abs_le_abs_sub γ u.im
      rw [abs_sub_comm] at this
      linarith
    have hhi : |u.im| ≤ |γ| + 1 := by
      have := abs_sub_abs_le_abs_sub u.im γ
      linarith
    refine ⟨(hp u (by linarith [hre.1])).2 fun h ↦ ?_, ?_⟩
    · rw [h] at hlo
      linarith
    · refine (hgr₁ u hre (by linarith)).trans (mul_le_mul_of_nonneg_left ?_ hC₁.le)
      exact Real.rpow_le_rpow (abs_nonneg _) (by linarith) hE0
  have hdisc₂ : ∀ u ∈ Metric.closedBall (⟨3 / 2, 2 * γ⟩ : ℂ) 1,
      AnalyticAt ℂ L₂ u ∧ ‖L₂ u‖ ≤ C₂ * (|γ| ^ 2) ^ E := by
    intro u hu
    obtain ⟨hre, him⟩ := finiteHeckeL_zeroFreeRegion_disc (2 * γ) u hu
    have h2γ : |2 * γ| = 2 * |γ| := by rw [abs_mul, abs_two]
    have hlo : 2 * |γ| - 1 ≤ |u.im| := by
      have := abs_sub_abs_le_abs_sub (2 * γ) u.im
      rw [abs_sub_comm] at this
      linarith
    have hhi : |u.im| ≤ 2 * |γ| + 1 := by
      have := abs_sub_abs_le_abs_sub u.im (2 * γ)
      linarith
    refine ⟨(hp₂ u (by linarith [hre.1])).2 fun h ↦ ?_, ?_⟩
    · rw [h] at hlo
      linarith
    · refine (hgr₂ u hre (by linarith)).trans (mul_le_mul_of_nonneg_left ?_ hC₂.le)
      exact Real.rpow_le_rpow (abs_nonneg _) (by linarith) hE0
  obtain ⟨-, hlow₁⟩ := hlow χ L hSeries γ
  obtain ⟨-, hlow₂⟩ := hlow (χ ^ 2) L₂ hS₂ (2 * γ)
  have hz₁ : (⟨σ, γ⟩ : ℂ) ∈ Metric.closedBall (⟨3 / 2, γ⟩ : ℂ) (1 / 2) :=
    finiteHeckeL_zeroFreeRegion_mem_ball γ σ (1 / 2) (by rw [abs_le]; constructor <;> linarith)
  have hz₂ : (⟨σ, 2 * γ⟩ : ℂ) ∈ Metric.closedBall (⟨3 / 2, 2 * γ⟩ : ℂ) (1 / 2) :=
    finiteHeckeL_zeroFreeRegion_mem_ball (2 * γ) σ (1 / 2)
      (by rw [abs_le]; constructor <;> linarith)
  have hρ₁ : (⟨β, γ⟩ : ℂ) ∈ Metric.closedBall (⟨3 / 2, γ⟩ : ℂ) (3 / 4) :=
    finiteHeckeL_zeroFreeRegion_mem_ball γ β (3 / 4) (by rw [abs_le]; constructor <;> linarith)
  have h34 (c : ℂ) : Metric.closedBall c (3 / 4) ⊆ Metric.closedBall c 1 :=
    Metric.closedBall_subset_closedBall (by norm_num)
  have hLz : L ⟨σ, γ⟩ ≠ 0 :=
    (finiteHeckeL_logDeriv_hasSum_ideals χ L hL hSeries ⟨⟨σ, γ⟩, hσ1⟩).2.1
  have hLz₂ : L₂ ⟨σ, 2 * γ⟩ ≠ 0 :=
    (finiteHeckeL_logDeriv_hasSum_ideals (χ ^ 2) L₂ hL₂ hS₂ ⟨⟨σ, 2 * γ⟩, hσ1⟩).2.1
  have hLρ : L ⟨β, γ⟩ = 0 := by
    by_contra h
    exact hord.ne' ((hL (mem_univ _)).meromorphicOrderAt_eq_zero_iff.mpr h)
  have hS₁ : ∀ ρ' ∈ Metric.closedBall (⟨3 / 2, γ⟩ : ℂ) (3 / 4), L ρ' = 0 →
      ρ'.re ≤ (⟨σ, γ⟩ : ℂ).re := by
    intro ρ' hρ' h0
    by_contra! hlt
    exact finiteHeckeL_zeroFreeRegion_ne_zero F χ L hL hSeries ρ'
      (by change σ < ρ'.re at hlt; linarith) (hdisc₁ ρ' (h34 _ hρ')).1 h0
  have hS₂' : ∀ ρ' ∈ Metric.closedBall (⟨3 / 2, 2 * γ⟩ : ℂ) (3 / 4), L₂ ρ' = 0 →
      ρ'.re ≤ (⟨σ, 2 * γ⟩ : ℂ).re := by
    intro ρ' hρ' h0
    by_contra! hlt
    exact finiteHeckeL_zeroFreeRegion_ne_zero F (χ ^ 2) L₂ hL₂ hS₂ ρ'
      (by change σ < ρ'.re at hlt; linarith) (hdisc₂ ρ' (h34 _ hρ')).1 h0
  have hX₁ := (finiteHeckeL_zeroFreeRegion_landau L _ _ (C₁ * (|γ| ^ 2) ^ E) (1 / Z)
    (by positivity) (fun u hu ↦ (hdisc₁ u hu).1) (fun u hu ↦ (hdisc₁ u hu).2) hlow₁ hz₁ hLz
    hS₁).2 _ hρ₁ hLρ
  have hX₂ := (finiteHeckeL_zeroFreeRegion_landau L₂ _ _ (C₂ * (|γ| ^ 2) ^ E) (1 / Z)
    (by positivity) (fun u hu ↦ (hdisc₂ u hu).1) (fun u hu ↦ (hdisc₂ u hu).2) hlow₂ hz₂ hLz₂
    hS₂').1
  have hre : (1 / ((⟨σ, γ⟩ : ℂ) - ⟨β, γ⟩)).re = 1 / (σ - β) := by
    have : (⟨σ, γ⟩ : ℂ) - ⟨β, γ⟩ = ((σ - β : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [this, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
  rw [hre] at hX₁
  rw [← hKdef] at hX₁ hX₂
  have hg1 : 1 ≤ |γ| ^ 2 := by linarith
  have hlogsq : Real.log (|γ| ^ 2) = 2 * Real.log |γ| := by
    rw [Real.log_pow]; norm_num
  have hB (C : ℝ) : Real.log (max (C * (|γ| ^ 2) ^ E / (1 / Z)) 2) ≤
      Real.log (max (C * Z) 2) + E * (2 * Real.log |γ|) := by
    rw [div_div_eq_mul_div, div_one, mul_right_comm, ← hlogsq]
    exact finiteHeckeL_zeroFreeRegion_log_le (C * Z) E (|γ| ^ 2) hE0 hg1
  have hB₁ := mul_le_mul_of_nonneg_left (hB C₁) hK.le
  have hB₂ := mul_le_mul_of_nonneg_left (hB C₂) hK.le
  rw [← hc₁] at hB₁
  rw [← hc₂] at hB₂
  have hlg0 : 0 ≤ Real.log |γ| := by linarith
  have hKE : 10 * K * (E * Real.log |γ|) ≤ 30 * K * (d * Real.log |γ|) := by
    have := mul_le_mul_of_nonneg_left hEd (by positivity : 0 ≤ 10 * K * Real.log |γ|)
    linarith
  have hdlg : Real.log |γ| ≤ d * Real.log |γ| := le_mul_of_one_le_left hlg0 hd1
  have hmain : 0 ≤ 3 / (σ - 1) - 4 / (σ - β) + M * Lg := by
    rw [hMdef, hLg]
    have e2 : K * (c₁ + E * (2 * Real.log |γ|)) = K * c₁ + 2 * (K * (E * Real.log |γ|)) := by
      ring
    have e3 : K * (c₂ + E * (2 * Real.log |γ|)) = K * c₂ + 2 * (K * (E * Real.log |γ|)) := by
      ring
    have e4 : (30 * K + 1) * (d * Real.log |γ|) = 30 * K * (d * Real.log |γ|) +
      d * Real.log |γ| := by ring
    have e5 : 10 * K * (E * Real.log |γ|) = 10 * (K * (E * Real.log |γ|)) := by ring
    have e6 : 3 / (σ - 1) - 4 / (σ - β) = 3 * (1 / (σ - 1)) + 4 * -(1 / (σ - β)) := by ring
    rw [e2] at hB₁
    rw [e3] at hB₂
    rw [e4, e6]
    rw [e5] at hKE
    have hCst' : Cst = 3 * C₀ + 4 * (K * c₁) + K * c₂ := by rw [hCst]; ring
    linarith only [h341, hX₀, hX₁, hX₂, hB₁, hB₂, hKE, hdlg, hlogC, hCst']
  exact finiteHeckeL_zeroFreeRegion_final M Lg σ β hM hLg0 hσ hβ hβ1 hmain

/-- Two continuations in normal form agreeing on `Re s > 1` are equal. -/
private theorem finiteHeckeL_zeroFreeRegion_unique {U V : ℂ → ℂ} (hU : MeromorphicNFOn U univ)
    (hV : MeromorphicNFOn V univ) (h : ∀ z : ℂ, 1 < z.re → U z = V z) : U = V := by
  let b : ℂ := (2 : ℝ)
  have hb : ∀ᶠ z : ℂ in 𝓝 b, 1 < z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num [b])
  have ho : meromorphicOrderAt (U - V) b = ⊤ :=
    meromorphicOrderAt_eq_top_iff.mpr ((hb.filter_mono nhdsWithin_le_nhds).mono
      fun z hz ↦ sub_eq_zero.mpr (h z hz))
  funext z
  have hz := (hU.meromorphicOn.sub hV.meromorphicOn).meromorphicOrderAt_eq_top_of_isPreconnected
    isPreconnected_univ (mem_univ b) (mem_univ z) ho
  exact (((hU (mem_univ z)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
    (hV (mem_univ z))).mp (eventuallyEq_iff_sub.mpr
      (meromorphicOrderAt_eq_top_iff.mp hz))).eq_of_nhds

/-- Below a fixed height, a strip to the left of `Re s = 1` is free of zeros. -/
private theorem finiteHeckeL_zeroFreeRegion_low (F : Type*) [Field F] [NumberField F]
    (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (T : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℂ, |s.im| ≤ T → 1 - δ ≤ s.re → meromorphicOrderAt L s ≤ 0 := by
  have hnear (x : ℂ) (hx : meromorphicOrderAt L x ≤ 0) :
      ∀ᶠ w in 𝓝 x, meromorphicOrderAt L w ≤ 0 := by
    have hM := (hL (mem_univ x)).meromorphicAt
    have hne := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hM).mp
      (ne_top_of_le_ne_top (by simp) hx)
    have hev : ∀ᶠ w in 𝓝[≠] x, meromorphicOrderAt L w ≤ 0 := by
      filter_upwards [hne, hM.eventually_analyticAt] with w hw han
      exact ((hL (mem_univ w)).meromorphicOrderAt_eq_zero_iff.mpr hw).le
    filter_upwards [eventually_nhdsWithin_iff.mp hev] with w hw
    by_cases hwx : w = x
    · rw [hwx]; exact hx
    · exact hw hwx
  let K := (fun τ : ℝ ↦ (⟨1, τ⟩ : ℂ)) '' Icc (-T) T
  have hc : Continuous (fun τ : ℝ ↦ (⟨1, τ⟩ : ℂ)) := by
    have : (fun τ : ℝ ↦ (⟨1, τ⟩ : ℂ)) = fun τ : ℝ ↦ (1 : ℂ) + (τ : ℂ) * Complex.I := by
      funext τ
      apply Complex.ext <;> simp
    rw [this]
    fun_prop
  have hK : IsCompact K := isCompact_Icc.image hc
  have hKt : K ⊆ {w | ∀ᶠ z in 𝓝 w, meromorphicOrderAt L z ≤ 0} := by
    rintro _ ⟨τ, -, rfl⟩
    exact hnear _ (finiteHeckeL_zeroFreeRegion_order_nonpos F χ L hL hSeries _ le_rfl)
  obtain ⟨δ, hδ, hsub⟩ := hK.exists_thickening_subset_open isOpen_setOfPred_eventually_nhds hKt
  refine ⟨δ / 2, half_pos hδ, fun s hs hre ↦ ?_⟩
  by_cases h1 : 1 ≤ s.re
  · exact finiteHeckeL_zeroFreeRegion_order_nonpos F χ L hL hSeries s h1
  rw [not_le] at h1
  have hmem : s ∈ Metric.thickening δ K := by
    rw [Metric.mem_thickening_iff]
    refine ⟨⟨1, s.im⟩, ⟨s.im, abs_le.mp hs, rfl⟩, ?_⟩
    rw [Complex.dist_eq]
    have : s - ⟨1, s.im⟩ = ((s.re - 1 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
    linarith
  exact (hsub hmem).self_of_nhds

/-- Paper: Proposition B.6.1.1, p. 636. An absolute constant gives a
zero-free region for each finite Hecke L-function, with a scale depending on
the field and character. Meromorphic order distinguishes poles from zeros.
Deviation: The scale is chosen greater than `1/3` so the logarithm in the
denominator is positive at every height. It is an existential scale and may be
enlarged to exclude an exceptional zero. The separate real-zero clause is false. -/
theorem finiteHeckeL_zeroFreeRegion :
    ∃ A : ℝ, 0 < A ∧
      ∀ (F : Type*) [Field F] [NumberField F] (χ : U[F]),
        ∃ B : ℝ, 1 / 3 < B ∧
          ∀ (L : ℂ → ℂ), MeromorphicNFOn L univ →
            (∀ s : halfPlane, L s = finiteHeckeL χ s) →
            ∀ s : ℂ, 1 - A / ((Module.finrank ℚ F : ℝ) ^ 4 *
              Real.log (B * (|s.im| + 3))) ≤ s.re → meromorphicOrderAt L s ≤ 0 := by
  have hK : 0 < landauConstant (1 / 2) (3 / 4) (7 / 8) 1 :=
    landauConstant_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨1 / (15 * (30 * landauConstant (1 / 2) (3 / 4) (7 / 8) 1 + 1)), by positivity,
    fun F _ _ χ ↦ ?_⟩
  set A := 1 / (15 * (30 * landauConstant (1 / 2) (3 / 4) (7 / 8) 1 + 1)) with hA
  have hA0 : 0 < A := by positivity
  set d : ℝ := (Module.finrank ℚ F : ℝ) with hd
  have hd1 : 1 ≤ d := by
    rw [hd]
    exact_mod_cast Module.finrank_pos
  have hd4 : d ≤ d ^ 4 := by
    calc d = d ^ 1 := (pow_one d).symm
      _ ≤ d ^ 4 := pow_le_pow_right₀ hd1 (by norm_num)
  obtain ⟨L₁, hL₁, hS₁⟩ := finiteHeckeL_exists_continuation χ
  obtain ⟨T₀, hT₀, hev⟩ := finiteHeckeL_zeroFreeRegion_eventual F χ L₁ hL₁ hS₁
  obtain ⟨δ, hδ, hlow⟩ := finiteHeckeL_zeroFreeRegion_low F χ L₁ hL₁ hS₁ T₀
  set B := max 1 (Real.exp (A / δ)) with hB
  have hB1 : 1 ≤ B := le_max_left _ _
  refine ⟨B, by linarith, fun L hL hSeries s hs ↦ ?_⟩
  have hLL : L = L₁ := finiteHeckeL_zeroFreeRegion_unique hL hL₁ fun z hz ↦ by
    rw [hSeries ⟨z, hz⟩, hS₁ ⟨z, hz⟩]
  subst hLL
  have hB3 : B ≤ B * (|s.im| + 3) := le_mul_of_one_le_right (by linarith) (by linarith [abs_nonneg s.im])
  have hlogpos : 0 < Real.log (B * (|s.im| + 3)) :=
    Real.log_pos (by nlinarith [abs_nonneg s.im])
  by_cases ht : |s.im| ≤ T₀
  · apply hlow s ht
    have hlogB : A / δ ≤ Real.log (B * (|s.im| + 3)) := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      exact (le_max_right _ _).trans hB3
    have : A / (d ^ 4 * Real.log (B * (|s.im| + 3))) ≤ δ := by
      rw [div_le_iff₀ (by positivity)]
      rw [div_le_iff₀ hδ] at hlogB
      nlinarith
    linarith
  · rw [not_le] at ht
    by_contra hpos
    rw [not_le] at hpos
    have h := hev s ht.le hpos
    have hlogt : 0 < Real.log |s.im| := Real.log_pos (by linarith)
    have hle : d * Real.log |s.im| ≤ d ^ 4 * Real.log (B * (|s.im| + 3)) := by
      apply mul_le_mul hd4 _ hlogt.le (by positivity)
      exact Real.log_le_log (by linarith) (by nlinarith [abs_nonneg s.im])
    have : A / (d ^ 4 * Real.log (B * (|s.im| + 3))) ≤ A / (d * Real.log |s.im|) :=
      div_le_div_of_nonneg_left hA0.le (by positivity) hle
    rw [← hA] at h
    linarith

-- TODO(paper-gap): The paragraph after (B.6.1.1) identifies two different conductors.
-- A pure imaginary norm twist preserves the finite conductor but changes the
-- archimedean parameter. No conductor-uniform exceptional-zero assertion is made here.
-- TODO(paper-gap): The real-zero clause of Proposition B.6.1.1 is false on [1/2, 1].
-- If ζ(1/2 + iγ) = 0 with γ ≠ 0, the nonquadratic norm character |·|^(iγ)
-- over ℚ has finite L-function ζ(s + iγ), which vanishes at the real point 1/2.
-- The square of this character has finite L-function ζ(s + 2iγ), with a pole.

section OutsideEulerProduct

variable (χ : U[F]) (L : ℂ → ℂ) (S : Finset (HeightOneSpectrum (𝓞 F)))
variable (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)

-- TODO(later): needs §6.3 to compare with the S-local quotient in (6.3.1.6).
-- Compare as meromorphic germs, or after normalizing the quotient at removable
-- singularities. The factors agree via sLocalHeckeL_eq_partialEulerProduct on
-- descended characters. The finite-factor expression already occurs in §3.4.
local notation "Loutside" => (fun s : ℂ ↦ (∏ v ∈ S, (finiteHeckeEulerFactor χ v s)⁻¹) * L s)

include hL hSeries

/-- Paper: Theorem B.6.1.7, p. 641. The polynomial lower bound holds on a
closed unit interval outside a measurable set of length `1 / B`, with the
large-height threshold independent of `B > 1`.
Deviation: The finite set records only finite places. All archimedean factors
have already been removed from `L`. -/
theorem finiteHeckeL_outside_horizontal_lower_bound_off_small_set :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ T : ℝ in atTop, ∀ B : ℝ, 1 < B →
      ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Icc T (T + 1) ∧
        volume E = ENNReal.ofReal (1 / B) ∧
        ∀ t ∈ Icc T (T + 1) \ E, ∀ σ ∈ Icc (-1 : ℝ) 2,
          T ^ (-(A * B)) < ‖Loutside ⟨σ, t⟩‖ := by
  sorry

/-- Paper: Theorem B.6.1.7, p. 641. Each sufficiently high open unit interval
contains a height at which the Euler product outside `S` has a polynomial
lower bound on the whole horizontal segment from real part `-1` to `2`.
Deviation: The finite set records only finite places. All archimedean factors
have already been removed from `L`. -/
theorem finiteHeckeL_outside_exists_horizontal_lower_bound :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ T : ℝ in atTop, ∃ t ∈ Ioo T (T + 1),
      ∀ σ ∈ Icc (-1 : ℝ) 2, |t| ^ (-A) < ‖Loutside ⟨σ, t⟩‖ := by
  obtain ⟨A, hA, hev⟩ :=
    finiteHeckeL_outside_horizontal_lower_bound_off_small_set χ L S hL hSeries
  refine ⟨A * 2, by positivity, ?_⟩
  filter_upwards [hev, eventually_ge_atTop (1 : ℝ)] with T hT hT1
  obtain ⟨E, -, -, hEvol, hE⟩ := hT 2 one_lt_two
  have hne : (Ioo T (T + 1) \ E).Nonempty := by
    by_contra h
    have hsub : Ioo T (T + 1) ⊆ E := fun x hx ↦ by
      by_contra hxE
      exact h ⟨x, hx, hxE⟩
    have h1 := measure_mono (μ := volume) hsub
    rw [Real.volume_Ioo, hEvol] at h1
    have h2 := (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp h1
    norm_num at h2
  obtain ⟨t, ht, htE⟩ := hne
  refine ⟨t, ht, fun σ hσ ↦ lt_of_le_of_lt ?_ (hE t ⟨Ioo_subset_Icc_self ht, htE⟩ σ hσ)⟩
  rw [abs_of_pos (by linarith [ht.1])]
  exact Real.rpow_le_rpow_of_nonpos (by linarith) ht.1.le (by nlinarith)

-- TODO(paper-gap): The exponent in (B.6.1.38) must account for the left edge
-- of the strip. The basepoint for the integration in (B.6.1.43) is log Loutside(2 + it).

-- TODO(paper-gap): Footnote 29 asks for details in the proof of Corollary B.6.1.8
-- that pass from horizontal lower bounds to bounds for reciprocal derivatives.
-- At the selected heights use Cauchy's estimates on a wider fixed strip for
-- derivatives of Loutside, then differentiate Loutside * (1 / Loutside) = 1.

/-- Paper: Corollary B.6.1.8, p. 643. For each derivative order there is a
nondecreasing sequence of heights tending to infinity in absolute value and
growing at most linearly in the index. The derivative of the reciprocal Euler
product is bounded by a fixed power of the height on every selected segment.
Deviation: The finite set records only finite places. All archimedean factors
have already been removed from `L`. The supremum is expressed pointwise, and
analyticity ensures the iterated derivatives are defined on the segments. The
unit intervals of Theorem B.6.1.7, reflected for the conjugate character on the
negative tail, give heights within one of the index for the application of §B.3. -/
theorem finiteHeckeL_outside_inv_iteratedDeriv_horizontal_bound (m : ℕ) :
    let l := comap (abs : ℤ → ℤ) atTop
    ∃ (A β : ℝ) (T : ℤ → ℝ), 0 < A ∧ 0 < β ∧ Monotone T ∧
      Tendsto (abs ∘ T) l atTop ∧ (T =O[l] fun k ↦ |(k : ℝ)|) ∧
      (∀ᶠ k : ℤ in l, |T k - (k : ℝ)| ≤ 1) ∧
      ∀ k : ℤ, ∀ σ ∈ Icc (-1 : ℝ) 2,
        AnalyticAt ℂ (fun s ↦ (Loutside s)⁻¹) ⟨σ, T k⟩ ∧
          ‖iteratedDeriv m (fun s ↦ (Loutside s)⁻¹) ⟨σ, T k⟩‖ ≤ A * |T k| ^ β := by
  sorry

end OutsideEulerProduct

end RiemannMasullo
