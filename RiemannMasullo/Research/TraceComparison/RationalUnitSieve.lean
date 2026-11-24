module
public import RiemannMasullo.Research.TraceComparison.RationalThetaSpan
import RiemannMasullo.Research.TraceComparison.PoissonCompensation
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Ideal.Basic

/-! # The two polar evaluations of a singly unit-sieved rational test -/

public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped FourierTransform NumberField.AdeleRing NNReal SchwartzMap
namespace RiemannMasullo.StripNuclearity

set_option quotPrecheck false
local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ
local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation "L(" v ")" => HeightOneSpectrum.adicCompletion ℚ v
local notation "O(" v ")" => HeightOneSpectrum.adicCompletionIntegers ℚ v
local notation "𝟎ₐ" => Multiplicative.ofAdd (0 : 𝔸)
local notation "realCoord" => InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
local notation "std" => ratStandardAdelicTest
local notation "ins(" v ", " π ")" => IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v π

/-- Subtracting the proper subball at one finite place of a standard real test
replaces its integer indicator there by the unit indicator when π is a uniformizer. -/
def ratFiniteUnitSieve (v : V) (π : L(v)ˣ) (f : SchwartzMap ℝ ℂ) :
    SchwartzBruhat (Multiplicative 𝔸) := std f - schwartzBruhatUnitTranslate ins(v, π) (std f)

private theorem rat_local_shrunk_ball (v : V) (π : L(v)ˣ)
    (hπ : Valued.v.IsUniformizer (π : L(v))) (x : L(v)) :
    π.inv * x ∈ O(v) ↔ Valued.v x < 1 := by
  let ν := (Valued.v : Valuation L(v) (WithZero (Multiplicative ℤ)))
  have hv : ν (π : L(v)) = WithZero.exp (-1 : ℤ) := hπ.trans
    (congrArg Units.val (Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (v.valuedAdicCompletion_surjective ℚ)))
  change ν ((↑π⁻¹ : L(v)) * x) ≤ 1 ↔ ν x < 1
  rw [map_mul, Units.val_inv_eq_inv_val, map_inv₀, hv, ← WithZero.exp_neg, neg_neg]
  rcases eq_or_ne (ν x) 0 with h | h
  · simp [h]
  rw [← WithZero.exp_log h, ← WithZero.exp_add, WithZero.exp_le_one_iff, WithZero.exp_lt_one_iff]
  omega

private theorem integral_except (v : V) (x : 𝔸) :
    (∀ w : V, x.2 w ∈ O(w)) ↔
      (∀ w : V, w ≠ v → x.2 w ∈ O(w)) ∧ Valued.v (x.2 v) ≤ 1 :=
  ⟨fun h ↦ ⟨fun w _ ↦ h w, h v⟩, fun ⟨h, hv⟩ w ↦ by
    by_cases hw : w = v
    · subst w
      exact hv
    · exact h w hw⟩

private theorem sifted_integrality (v : V) (π : L(v)ˣ) (hπ : Valued.v.IsUniformizer (π : L(v)))
    (x : 𝔸) :
    (∀ w : V, ((ins(v, π)⁻¹ : 𝔸ˣ).val * x).2 w ∈ O(w)) ↔
      (∀ w : V, w ≠ v → x.2 w ∈ O(w)) ∧ Valued.v (x.2 v) < 1 := by
  classical
  have eh (w : V) (hw : w ≠ v) : ((ins(v, π)⁻¹ : 𝔸ˣ).val * x).2 w = x.2 w := by
    change Pi.mulSingle v π.inv w * x.2 w = _
    rw [Pi.mulSingle_eq_of_ne hw, one_mul]
  have ev : ((ins(v, π)⁻¹ : 𝔸ˣ).val * x).2 v = π.inv * x.2 v := by
    change Pi.mulSingle v π.inv v * x.2 v = _
    rw [Pi.mulSingle_eq_same]
  constructor
  · intro h
    refine ⟨fun w hw ↦ (eh w hw) ▸ h w, ?_⟩
    exact (rat_local_shrunk_ball v π hπ _).mp (ev ▸ h v)
  · rintro ⟨h, hv⟩ w
    by_cases hw : w = v
    · subst w
      rw [ev]
      exact (rat_local_shrunk_ball v π hπ _).mpr hv
    · rw [eh w hw]
      exact h w hw

open Classical in
private theorem shell_difference {Γ : Type*} [LinearOrder Γ] (p : Prop) (x r : Γ) (z : ℂ)
    (dle : Decidable (p ∧ x ≤ r)) (dlt : Decidable (p ∧ x < r)) (deq : Decidable (p ∧ x = r)) :
    (@ite ℂ (p ∧ x ≤ r) dle z 0) - (@ite ℂ (p ∧ x < r) dlt z 0) =
      (@ite ℂ (p ∧ x = r) deq z 0) := by
  by_cases hp : p
  · rcases lt_trichotomy x r with h | h | h
    · simp [hp, h, h.le, h.ne]
    · simp [hp, h]
    · simp [hp, h.not_gt, h.not_ge, h.ne']
  · simp [hp]

open Classical in
/-- The masked test equals the real input on the product of the unit shell at v with
the integer balls elsewhere. At v, having valuation one means being an integer unit. -/
theorem ratFiniteUnitSieve_apply (v : V) (π : L(v)ˣ) (hπ : Valued.v.IsUniformizer (π : L(v)))
    (f : SchwartzMap ℝ ℂ) (x : 𝔸) :
    ratFiniteUnitSieve v π f (Multiplicative.ofAdd x) =
      if (∀ w : V, w ≠ v → x.2 w ∈ O(w)) ∧ Valued.v (x.2 v) = 1 then
        f (realCoord (x.1 Rat.infinitePlace)) else 0 := by
  change std f (Multiplicative.ofAdd x) - std f (Multiplicative.ofAdd ((ins(v, π)⁻¹ : 𝔸ˣ).val * x)) = _
  rw [ratStandardAdelicTest_apply, ratStandardAdelicTest_apply, sifted_integrality v π hπ,
    integral_except v x]
  have ha : ((ins(v, π)⁻¹ : 𝔸ˣ).val * x).1 Rat.infinitePlace = x.1 Rat.infinitePlace := by
    change 1 * (x.1 Rat.infinitePlace) = _
    rw [one_mul]
  rw [ha]
  exact shell_difference (∀ w : V, w ≠ v → x.2 w ∈ O(w)) (Valued.v (x.2 v)) 1
    (f (realCoord (x.1 Rat.infinitePlace))) _ _ _

/-- The actual two adelic polar evaluations for a single unit mask. Its Fourier value
uses the additive Haar mass of the unit shell, namely 1−1/Nv. -/
theorem ratFiniteUnitSieve_polarValues (v : V) (π : L(v)ˣ) (hπ : Valued.v.IsUniformizer (π : L(v)))
    (f : SchwartzMap ℝ ℂ) :
    adelePolarValues (ratFiniteUnitSieve v π f) =
      (0, (1 - (v.asIdeal.absNorm : ℂ)⁻¹) * 𝓕 f 0) := by
  have h0 : schwartzBruhatUnitTranslate ins(v, π) (std f) 𝟎ₐ = std f 𝟎ₐ := by
    rw [schwartzBruhatUnitTranslate_apply, mul_zero]
  have hn : ((ideleClassNorm ℚ (QuotientGroup.mk ins(v, π))).val : ℝ) = (v.asIdeal.absNorm : ℝ)⁻¹ := by
    change ((ideleClassNorm ℚ (IdeleClassGroup.ofAdicCompletion (𝓞 ℚ) ℚ v π)).val : ℝ) = _
    rw [ideleClassNorm_ofAdicCompletion]
    exact norm_uniformizer_adicCompletion v _ hπ
  rw [ratFiniteUnitSieve, map_sub, adelePolarValues_apply, adelePolarValues_apply,
    h0, adeleUnitTranslate_fourier_zero, hn, ratStandardAdelicTest_fourier_zero]
  apply Prod.ext
  · exact sub_self _
  · change 𝓕 f 0 - ((v.asIdeal.absNorm : ℝ)⁻¹ : ℝ) • 𝓕 f 0 = _
    rw [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast]
    ring

/-- After imposing the unit indicator at one rational finite place, the real test
is adelically polar-free exactly when its ordinary Fourier transform vanishes at zero. -/
theorem ratFiniteUnitSieve_polar_iff (v : V) (π : L(v)ˣ) (hπ : Valued.v.IsUniformizer (π : L(v)))
    (f : SchwartzMap ℝ ℂ) :
    ratFiniteUnitSieve v π f ∈ adelePolarSubspace ℚ ↔ 𝓕 f 0 = 0 := by
  change adelePolarValues (ratFiniteUnitSieve v π f) = 0 ↔ _
  have hn : (1 : ℝ) < v.asIdeal.absNorm := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hne : (1 - (v.asIdeal.absNorm : ℂ)⁻¹) ≠ 0 := by
    have h := (inv_lt_one_of_one_lt₀ hn).ne
    have hr := Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr h.symm)
    simpa only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_inv, Complex.ofReal_natCast] using hr
  rw [ratFiniteUnitSieve_polarValues v π hπ, Prod.mk_eq_zero]
  simp [hne]

private theorem ratPrimePlace_absNorm (p : Nat.Primes) :
    (Rat.HeightOneSpectrum.primesEquiv.symm p : V).asIdeal.absNorm = p.val := by
  let v : V := Rat.HeightOneSpectrum.primesEquiv.symm p
  let e := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)
  have hg : Rat.HeightOneSpectrum.natGenerator v = p.val := congrArg Subtype.val
    (Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply p)
  have he := Rat.HeightOneSpectrum.span_natGenerator v
  rw [hg] at he
  have hi : v.asIdeal = Ideal.span {(p.val : 𝓞 ℚ)} := by
    apply (Ideal.relIsoOfBijective (f := e.toRingHom) e.bijective).symm.injective
    change Ideal.map e _ = Ideal.map e _
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
    exact he.symm
  change v.asIdeal.absNorm = p.val
  rw [hi, Ideal.absNorm_span_natCast, RingOfIntegers.rank]
  simp

/-- For each ordinary rational prime there is an idelic unit-supported test with
the specified two polar values for every real input, including p=2 with multiplier 1/2. -/
theorem exists_ratPrimeUnitSieve_polarValues (p : Nat.Primes) :
    let v : V := Rat.HeightOneSpectrum.primesEquiv.symm p
    ∃ π : L(v)ˣ, Valued.v.IsUniformizer (π : L(v)) ∧ ∀ f : SchwartzMap ℝ ℂ,
      adelePolarValues (ratFiniteUnitSieve v π f) = (0, (1 - (p.val : ℂ)⁻¹) * 𝓕 f 0) := by
  let v : V := Rat.HeightOneSpectrum.primesEquiv.symm p
  let ν := (Valued.v : Valuation L(v) (WithZero (Multiplicative ℤ)))
  obtain ⟨a, ha⟩ := ν.exists_isUniformizer_of_isCyclic_of_nontrivial
  refine ⟨Units.mk0 a ha.ne_zero, ha, fun f ↦ ?_⟩
  rw [ratFiniteUnitSieve_polarValues _ _ ha, ratPrimePlace_absNorm]

end RiemannMasullo.StripNuclearity
