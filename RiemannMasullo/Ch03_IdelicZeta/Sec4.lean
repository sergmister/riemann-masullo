module

public import RiemannMasullo.Ch03_IdelicZeta.Sec3b
public import RiemannMasullo.AppC_LCTVS.Sec5b
public import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Pow.Complex
import all RiemannMasullo.Ch03_IdelicZeta.Sec3
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace
import RiemannMasullo.ForMathlib.Analysis.MellinTransform.Holomorphic
import RiemannMasullo.ForMathlib.Analysis.MellinTransform.Gaussian
import all RiemannMasullo.Ch03_IdelicZeta.Sec3b
import all RiemannMasullo.AppC_LCTVS.Sec2a_part2
import all RiemannMasullo.AppC_LCTVS.Sec2b
import all RiemannMasullo.Ch03_IdelicZeta.Sec2
import all RiemannMasullo.AppC_LCTVS.Sec5b
import all RiemannMasullo.AppA_AlgebraicNT.Sec3
import all RiemannMasullo.Ch02_AdelicTheta.Sec2a
import all RiemannMasullo.Ch02_AdelicTheta.Sec2b
import all RiemannMasullo.AppD_SchwartzBruhat.Sec2b
import Mathlib.Topology.Homeomorph.Lemmas
import RiemannMasullo.ForMathlib.Analysis.Distribution.SchwartzSpace.Gaussian
import Mathlib.Topology.LocallyConstant.Algebra
import RiemannMasullo.ForMathlib.MeasureTheory.Integral.LocallyConstant
import Mathlib.Analysis.Complex.Convex
import RiemannMasullo.ForMathlib.MeasureTheory.Integral.ProdPi
import RiemannMasullo.ForMathlib.Analysis.Normed.Field.ProperSpace
import Mathlib.Topology.Algebra.IsOpenUnits
import RiemannMasullo.ForMathlib.MeasureTheory.Group.Arithmetic

/-!
# Eigendistributions and Weil's identity

Masullo, §3.4, pp. 141–153. Page 154 is blank. The zeta integrals use the
Tamagawa measures from Appendix A. The local factorization recalled in
Notation 3.4.1.1 is `heckeCharacter_eq_prod_restrictions` from §3.1.
-/

@[expose] public noncomputable section

open Bornology Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing Topology UniformConvergenceCLM

namespace RiemannMasullo

set_option quotPrecheck false

variable {F : Type*} [Field F] [NumberField F]

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "C₁" => (ideleClassNorm F).ker
local notation "C_F" => IdeleClassGroup (𝓞 F) F
local notation "X" => HeckeCharacter (𝓞 F) F
local notation "I_F" => IdeleGroup (𝓞 F) F
local notation "ℬ(" K ")" => SchwartzBruhat (Multiplicative K)
local notation "classOf" => QuotientGroup.mk (s := IdeleGroup.principalSubgroup (𝓞 F) F)
local notation "normℝ" => fun (g : C_F) ↦ ((ideleClassNorm F g : ℝ≥0) : ℝ)
local notation "circleToComplex" => (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ)
local notation "finiteNorm(" v ")" =>
  (Units.map nnNormHom.toMonoidHom : (HeightOneSpectrum.adicCompletion F v)ˣ →* ℝ≥0ˣ)
local notation "infiniteNorm(" w ")" =>
  ((Units.map nnNormHom.toMonoidHom) ^ InfinitePlace.mult w : (InfinitePlace.Completion w)ˣ →* ℝ≥0ˣ)

section UnramifiedIdentity

local notation "AArch" => SAdeleRing F (∅ : Finset V)
local notation "μArch" => sMultiplicativeTamagawaMeasure F (∅ : Finset V)
local notation "μv" => finiteLocalMultiplicativeTamagawaMeasure F
local notation "valuation(" v ")" =>
  (Valued.v : Valuation (HeightOneSpectrum.adicCompletion F v) (WithZero (Multiplicative ℤ)))
local notation "positive" => (relativeRightHalfPlane (G := C_F) (ideleClassNorm F)
  (isProperMap_ideleClassNorm F) (ideleClassNorm_ne_one (F := F)) 0 : Set X)

-- Named, because an anonymous instance gets the same generated name in every file that declares
-- it, and two such files can then not be imported together.
local instance instMeasurableSpaceUnitsAdicCompletionSec4 (v : V) :
    MeasurableSpace (v.adicCompletion F)ˣ := borel _

/-- Paper: Equation (3.4.1.2), p. 143. The archimedean integral uses the
restriction of the quasi-character along insertion of the archimedean ideles. -/
def weilArchimedeanIntegral (fArch : ℬ(AArch)) (c : X) : ℂ :=
  ∫ g : AArchˣ, fArch (Multiplicative.ofAdd g.val) *
    c (classOf (sIdeleInsertion F ∅ g)) ∂μArch

/-- Paper: Equation (3.4.1.2), p. 143. The integral at the bare norm is the
integral of the test function weighted by the archimedean module. -/
theorem weilArchimedeanIntegral_norm (fArch : ℬ(AArch)) :
    weilArchimedeanIntegral fArch (ideleClassNormTwist 1 1) =
      ∫ g : AArchˣ, fArch (Multiplicative.ofAdd g.val) *
        (((sIdeleNorm F ∅ g : ℝ≥0) : ℝ) : ℂ) ∂μArch := by
  unfold weilArchimedeanIntegral
  congr with g
  rw [ideleClassNormTwist_one_one]
  change _ * (((ideleNorm F (sIdeleInsertion F ∅ g) : ℝ≥0) : ℝ) : ℂ) = _
  rw [ideleNorm_sIdeleInsertion]

/-- Paper: Theorem 3.4.1.1, p. 143. The archimedean integrand is absolutely
integrable at each quasi-character of positive abscissa. -/
theorem weilArchimedeanIntegral_integrable (fArch : ℬ(AArch)) (c : X) (hc : c ∈ positive) :
    Integrable (fun g : AArchˣ ↦ fArch (Multiplicative.ofAdd g.val) *
      c (classOf (sIdeleInsertion F ∅ g))) μArch := by
  obtain ⟨-, -, -, -, -, hC₂, hClc, -⟩ := ideleGroup_quotient.{_, 0} F
  let σ := quasiCharacterAbscissa (ideleClassNorm F) (isProperMap_ideleClassNorm F)
    (ideleClassNorm_ne_one (F := F)) c
  have hσ : 0 < σ := hc
  -- Compare with the S-local integrand for the norm twist of exponent σ and S = ∅.
  let c₀ : QuasiCharacter (SIdeleQuotient F ∅) :=
    quasiCharacterNormTwist (sIdeleQuotientNorm F ∅)
      (isProperMap_sIdeleQuotientNorm F ∅).continuous ((circleToComplex).comp 1) σ
  have hc₀ := sLocalIdelicZetaIntegral_integrable fArch c₀ ⟨1, σ, by simpa using hσ, rfl⟩
  have hnorm (g : AArchˣ) : ‖c (classOf (sIdeleInsertion F ∅ g))‖ =
      ‖c₀ (QuotientGroup.mk g)‖ := by
    rw [norm_quasiCharacter_eq_rpow_abscissa (ideleClassNorm F) (isProperMap_ideleClassNorm F)
      (ideleClassNorm_ne_one (F := F)) c]
    change (((ideleNorm F (sIdeleInsertion F ∅ g) : ℝ≥0ˣ) : ℝ≥0) : ℝ) ^ σ =
      ‖((1 : Circle) : ℂ) * ((((sIdeleQuotientNorm F ∅ (QuotientGroup.mk g) : ℝ≥0ˣ) :
        ℝ≥0) : ℝ) : ℂ) ^ (σ : ℂ)‖
    rw [ideleNorm_sIdeleInsertion, sIdeleQuotientNorm_mk, Circle.coe_one, one_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos (NNReal.coe_pos.mpr (Units.zero_lt _)),
      Complex.ofReal_re]
  -- The σ-algebras of §3.3.1 on the archimedean ideles.
  let (w : InfinitePlace F) : MeasurableSpace w.Completion := borel _
  let (v : V) : MeasurableSpace (v.adicCompletion F) := borel _
  let : MeasurableSpace (InfiniteAdeleRing F) :=
    inferInstanceAs (MeasurableSpace ((w : InfinitePlace F) → w.Completion))
  let : MeasurableSpace AArch := inferInstanceAs (MeasurableSpace
    (InfiniteAdeleRing F × ((v : (∅ : Finset V)) → v.val.adicCompletion F)))
  let : BorelSpace AArchˣ := sIdeleGroup_borelSpace
  have hf : Continuous fun g : AArchˣ ↦ fArch (Multiplicative.ofAdd g.val) :=
    (schwartzBruhat_continuous (G := Multiplicative AArch) fArch).comp
      (continuous_ofAdd.comp Units.continuous_val)
  have hcc : Continuous fun g : AArchˣ ↦ c (classOf (sIdeleInsertion F ∅ g)) :=
    c.continuous.comp (QuotientGroup.continuous_mk.comp
      (isClosedEmbedding_sIdeleInsertion F ∅).continuous)
  refine hc₀.norm.mono' (hf.mul hcc).aestronglyMeasurable (ae_of_all _ fun g ↦ ?_)
  rw [norm_mul, norm_mul, hnorm]

open Classical in
/-- Paper: Equations (3.4.1.3)–(3.4.1.4), p. 143. At an unramified place,
subtract the test function pulled back by inverse uniformizer multiplication
before integrating. At a ramified place, integrate the original test function. -/
def weilModifiedFiniteIntegral (v : V) (π : (v.adicCompletion F)ˣ)
    (f : v.adicCompletion F → ℂ) (c : X) : ℂ :=
  localIdelicZetaIntegral (μv v)
    (if c.IsUnramifiedAt v then fun x ↦ f x - f ((↑π⁻¹ : v.adicCompletion F) * x) else f)
    (finitePlaceRestriction F v c)

open Classical in
/-- Paper: Theorem 3.4.1.1, pp. 143–144. The finite-place integrals of the
modified compact-open indicators are absolutely convergent at positive abscissa. -/
theorem weilModifiedFiniteIntegral_integrable (v : V) (π : (v.adicCompletion F)ˣ)
    (hπ : (valuation(v)).IsUniformizer π.val) (K : Set (v.adicCompletion F))
    (hK : IsCompact K) (hKo : IsOpen K) (c : X) (hc : c ∈ positive) :
    let f := K.indicator (fun _ ↦ (1 : ℂ))
    let test := if c.IsUnramifiedAt v then fun x ↦ f x - f ((↑π⁻¹ : v.adicCompletion F) * x)
      else f
    Integrable (fun g : (v.adicCompletion F)ˣ ↦ test g.val * finitePlaceRestriction F v c g)
      (μv v) := by
  intro f test
  let L := v.adicCompletion F
  have : BorelSpace Lˣ := ⟨rfl⟩
  -- The character has modulus a positive power of the local norm.
  obtain ⟨-, -, -, -, -, hC₂, hClc, -⟩ := ideleGroup_quotient.{_, 0} F
  let σ := quasiCharacterAbscissa (ideleClassNorm F) (isProperMap_ideleClassNorm F)
    (ideleClassNorm_ne_one (F := F)) c
  have hσ : 0 < σ := hc
  have hnorm (g : Lˣ) : ‖finitePlaceRestriction F v c g‖ = ‖(g : L)‖ ^ σ := by
    change ‖c (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v g)‖ = _
    rw [norm_quasiCharacter_eq_rpow_abscissa (ideleClassNorm F) (isProperMap_ideleClassNorm F)
      (ideleClassNorm_ne_one (F := F)) c]
    change (((ideleClassNorm F (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v g) : ℝ≥0ˣ) : ℝ≥0) : ℝ) ^
      σ = _
    rw [ideleClassNorm_ofAdicCompletion]
    rfl
  -- The test function is bounded by two and vanishes outside a ball.
  obtain ⟨R₀, hR₀⟩ := hK.exists_bound_of_continuousOn continuous_norm.continuousOn
  let R := max R₀ (‖(π : L)‖ * R₀)
  have hsupp (x : L) (hx : test x ≠ 0) : ‖x‖ ≤ R := by
    have hcases : x ∈ K ∨ (↑π⁻¹ : L) * x ∈ K := by
      by_contra h
      push Not at h
      apply hx
      by_cases hu : c.IsUnramifiedAt v
      · simp only [test, f, hu, ite_true]
        rw [indicator_of_notMem h.1, indicator_of_notMem h.2, sub_self]
      · simp only [test, f, hu, ite_false]
        rw [indicator_of_notMem h.1]
    rcases hcases with h | h
    · exact (by simpa using hR₀ x h : ‖x‖ ≤ R₀).trans (le_max_left _ _)
    · have h' : ‖(↑π⁻¹ : L) * x‖ ≤ R₀ := by simpa using hR₀ _ h
      have hx : x = (π : L) * ((↑π⁻¹ : L) * x) := by
        rw [← mul_assoc, Units.mul_inv, one_mul]
      refine le_trans ?_ (le_max_right _ _)
      rw [hx, norm_mul]
      exact mul_le_mul_of_nonneg_left h' (norm_nonneg _)
  have hbound (x : L) : ‖test x‖ ≤ 2 := by
    have h1 (y : L) : ‖f y‖ ≤ 1 := by
      by_cases hy : y ∈ K <;> simp [f, hy]
    by_cases hu : c.IsUnramifiedAt v
    · simp only [test, hu, ite_true]
      exact (norm_sub_le _ _).trans (by linarith [h1 x, h1 ((↑π⁻¹ : L) * x)])
    · simp only [test, hu, ite_false]
      linarith [h1 x]
  -- Measurability: the test function is a difference of indicators of open sets of units.
  have hmeasf (a : L) : Measurable fun g : Lˣ ↦ f (a * g.val) := by
    have hopen : IsOpen {g : Lˣ | a * g.val ∈ K} :=
      hKo.preimage ((continuous_const.mul Units.continuous_val))
    have heq : (fun g : Lˣ ↦ f (a * g.val)) = {g : Lˣ | a * g.val ∈ K}.indicator 1 := by
      funext g
      by_cases hg : a * g.val ∈ K <;> simp [f, hg]
    rw [heq]
    exact measurable_one.indicator hopen.measurableSet
  have hmeas : Measurable fun g : Lˣ ↦ test g.val := by
    by_cases hu : c.IsUnramifiedAt v
    · simp only [test, hu, ite_true]
      have h1 := hmeasf 1
      simp only [one_mul] at h1
      exact h1.sub (hmeasf _)
    · simp only [test, hu, ite_false]
      have h1 := hmeasf 1
      simpa only [one_mul] using h1
  -- Dominate by the truncated norm power.
  have hb := finiteLocalTamagawa_integrable_norm_rpow v hσ R
  refine (hb.2.const_mul 2).mono'
    (hmeas.aestronglyMeasurable.mul (finitePlaceRestriction F v c).continuous.aestronglyMeasurable)
    (ae_of_all _ fun g ↦ ?_)
  rw [norm_mul, hnorm]
  by_cases hg : test (g : L) = 0
  · rw [hg, norm_zero, zero_mul]
    exact mul_nonneg zero_le_two (Set.indicator_nonneg (fun _ _ ↦ by positivity) _)
  · rw [indicator_of_mem (show g ∈ {u : Lˣ | ‖(u : L)‖ ≤ R} from hsupp _ hg)]
    exact mul_le_mul_of_nonneg_right (hbound _) (by positivity)

private theorem integerRing_difference_eq_integerUnits (v : V) (π : (v.adicCompletion F)ˣ)
    (hπ : (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).IsUniformizer π.val) :
    (fun x : v.adicCompletion F ↦
      ((v.adicCompletionIntegers F) : Set (v.adicCompletion F)).indicator (fun _ ↦ (1 : ℂ)) x -
        ((v.adicCompletionIntegers F) : Set (v.adicCompletion F)).indicator (fun _ ↦ (1 : ℂ)) ((↑π⁻¹ : v.adicCompletion F) * x)) =
      (Units.val '' ((v.adicCompletionIntegers F)).units).indicator (fun _ ↦ (1 : ℂ)) := by
  classical
  let K := v.adicCompletion F
  let O : Set K := v.adicCompletionIntegers F
  let U : Set Kˣ := (v.adicCompletionIntegers F).units
  let val := (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)))
  -- The uniformizer has valuation `exp (-1)`, the largest value below one.
  have hval : val (π : K) = WithZero.exp (-1 : ℤ) := hπ.trans
    (congrArg Units.val (Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (v.valuedAdicCompletion_surjective F)))
  have hlt (y : WithZero (Multiplicative ℤ)) (hy : y < 1) : y ≤ WithZero.exp (-1) := by
    rcases eq_or_ne y 0 with rfl | h0
    · exact zero_le
    rw [← WithZero.exp_log h0] at hy ⊢
    rw [WithZero.exp_lt_one_iff] at hy
    rw [WithZero.exp_le_exp]
    omega
  have hmemO (x : K) : x ∈ O ↔ val x ≤ 1 := HeightOneSpectrum.mem_adicCompletionIntegers _ _ _
  have hmemU (x : K) : x ∈ Units.val '' U ↔ val x = 1 := by
    constructor
    · rintro ⟨g, hg, rfl⟩
      have h1 : val (g : K) ≤ 1 := (hmemO _).mp hg.1
      have h2 : val ((g⁻¹ : Kˣ) : K) ≤ 1 := (hmemO _).mp hg.2
      rw [Units.val_inv_eq_inv_val, map_inv₀] at h2
      have hg0 : val (g : K) ≠ 0 := (Valuation.ne_zero_iff _).mpr g.ne_zero
      exact le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.mpr hg0)).mp h2)
    · intro hx
      have hx0 : x ≠ 0 := by
        intro h
        rw [h, map_zero] at hx
        exact zero_ne_one hx
      refine ⟨Units.mk0 x hx0, ⟨(hmemO _).mpr hx.le, (hmemO _).mpr ?_⟩, rfl⟩
      simp only [Units.coeHom_apply, Units.val_inv_eq_inv_val, Units.val_mk0, map_inv₀, hx,
        inv_one, le_refl]
  have hπinv (x : K) : val ((↑π⁻¹ : K) * x) = WithZero.exp 1 * val x := by
    rw [map_mul, Units.val_inv_eq_inv_val, map_inv₀, hval, ← WithZero.exp_neg, neg_neg]
  -- The modified integer-ring indicator is the indicator of the integer units.
  have htest : (fun x : K ↦ O.indicator (fun _ ↦ (1 : ℂ)) x -
      O.indicator (fun _ ↦ (1 : ℂ)) ((↑π⁻¹ : K) * x)) =
        (Units.val '' U).indicator (fun _ ↦ 1) := by
    funext x
    have he1 : (1 : WithZero (Multiplicative ℤ)) < WithZero.exp 1 := by simp
    rcases lt_trichotomy (val x) 1 with h | h | h
    · have hx : x ∈ O := (hmemO x).mpr h.le
      have hx' : (↑π⁻¹ : K) * x ∈ O := by
        rw [hmemO, hπinv]
        calc WithZero.exp 1 * val x ≤ WithZero.exp 1 * WithZero.exp (-1) := by
              gcongr
              exact hlt _ h
          _ = 1 := by rw [← WithZero.exp_add]; simp
      have hU : x ∉ Units.val '' U := fun hU ↦ h.ne ((hmemU x).mp hU)
      rw [indicator_of_mem hx, indicator_of_mem hx', indicator_of_notMem hU, sub_self]
    · have hx : x ∈ O := (hmemO x).mpr h.le
      have hx' : (↑π⁻¹ : K) * x ∉ O := by
        rw [hmemO, hπinv, h, mul_one, not_le]
        exact he1
      have hU : x ∈ Units.val '' U := (hmemU x).mpr h
      rw [indicator_of_mem hx, indicator_of_notMem hx', indicator_of_mem hU, sub_zero]
    · have hx : x ∉ O := by rw [hmemO, not_le]; exact h
      have hx' : (↑π⁻¹ : K) * x ∉ O := by
        rw [hmemO, hπinv, not_le]
        calc (1 : WithZero (Multiplicative ℤ)) = 1 * 1 := (mul_one 1).symm
          _ < WithZero.exp 1 * val x := mul_lt_mul'' he1 h zero_le zero_le
      have hU : x ∉ Units.val '' U := fun hU ↦ h.ne' ((hmemU x).mp hU)
      rw [indicator_of_notMem hx, indicator_of_notMem hx', indicator_of_notMem hU, sub_zero]
  exact htest

/-- Paper: Theorem 3.4.1.1, p. 144. At an unramified place the modified
integer-ring indicator integrates to the Tamagawa mass of the integer units. -/
theorem weilModifiedFiniteIntegral_integerRing (v : V) (π : (v.adicCompletion F)ˣ)
    (hπ : (valuation(v)).IsUniformizer π.val) (c : X)
    (hc : c.IsUnramifiedAt v) :
    weilModifiedFiniteIntegral v π
        ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ ↦ 1)) c =
      ((μv v) (v.adicCompletionIntegers F).units).toReal := by
  let K := v.adicCompletion F
  let O : Set K := v.adicCompletionIntegers F
  let U : Set Kˣ := (v.adicCompletionIntegers F).units
  have hmemO (x : K) : x ∈ O ↔ (valuation(v)) x ≤ 1 :=
    HeightOneSpectrum.mem_adicCompletionIntegers _ _ _
  have htest := integerRing_difference_eq_integerUnits v π hπ
  -- The integer units are a compact open set on which the character is trivial.
  have : BorelSpace Kˣ := ⟨rfl⟩
  have hUo : IsOpen U := Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)
  have hUc : IsCompact U := by
    have : ProperSpace K := properSpace_adicCompletion v
    apply Submonoid.units_isCompact
    change IsCompact (v.adicCompletionIntegers F : Set K)
    convert isCompact_closedBall (0 : K) 1 using 1
    ext x
    simp only [SetLike.mem_coe, Metric.mem_closedBall, dist_zero_right,
      Valued.toNormedField.norm_le_one_iff]
    exact hmemO x
  have : (μv v).IsHaarMeasure := finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure (F := F) v
  have hcU (g : Kˣ) (hg : g ∈ U) : finitePlaceRestriction F v c g = 1 := by
    let x := (v.adicCompletionIntegers F).toSubmonoid.unitsEquivUnitsType ⟨g, hg⟩
    have h := HeckeCharacter.isUnramifiedAt_iff.mp hc x
    simp only [HeckeCharacter.restrict, x] at h
    have hxg : (((v.adicCompletionIntegers F).unitsEquivUnitsType ⟨g, hg⟩ :
        v.adicCompletionIntegers F) : K) = (g : K) := rfl
    rw [hxg, MulChar.ofUnitHom_coe, MonoidHom.comp_apply, MonoidHom.coe_toHomUnits] at h
    exact h
  unfold weilModifiedFiniteIntegral
  simp only [hc, ↓reduceIte]
  rw [htest]
  exact localIdelicZetaIntegral_indicator (μv v) _ U hUo.measurableSet hUc.measure_ne_top hcU

/-- Paper: Equation (3.4.1.1), p. 143. The modified zeta function is the
archimedean integral times the product of the modified finite integrals. -/
def weilModifiedZeta (fArch : ℬ(AArch)) (K : (v : V) → Set (v.adicCompletion F))
    (uniformizer : (v : V) → (v.adicCompletion F)ˣ) (c : X) : ℂ :=
  weilArchimedeanIntegral fArch c *
    (∏' v : V, weilModifiedFiniteIntegral v (uniformizer v) ((K v).indicator (fun _ ↦ 1)) c)

/-- Paper: Theorem 3.4.1.1, pp. 143–144. When the character is unramified
at every finite place and every local test is the integer-ring indicator,
the finite product contributes the product of integer-unit masses. -/
theorem weilModifiedZeta_integerRings (fArch : ℬ(AArch))
    (K : (v : V) → Set (v.adicCompletion F))
    (uniformizer : (v : V) → (v.adicCompletion F)ˣ)
    (hπ : ∀ v : V, (valuation(v)).IsUniformizer (uniformizer v).val)
    (hK : ∀ v : V, K v = v.adicCompletionIntegers F) (c : X)
    (hc : ∀ v, c.IsUnramifiedAt v) :
    weilModifiedZeta fArch K uniformizer c = weilArchimedeanIntegral fArch c *
      ∏ᶠ v : V, (((μv v) (v.adicCompletionIntegers F).units).toReal : ℂ) := by
  have hfactor (v : V) :
      weilModifiedFiniteIntegral v (uniformizer v) ((K v).indicator (fun _ ↦ 1)) c =
        (((μv v) (v.adicCompletionIntegers F).units).toReal : ℂ) := by
    rw [hK v]
    exact weilModifiedFiniteIntegral_integerRing v _ (hπ v) c (hc v)
  unfold weilModifiedZeta
  rw [tprod_congr hfactor]
  congr 1
  refine tprod_eq_finprod ((finiteLocalTamagawaMass_finite (F := F)).subset fun v hv h ↦ hv ?_)
  change ((((μv v) (v.adicCompletionIntegers F).units).toReal : ℝ) : ℂ) = 1
  rw [finiteLocalMultiplicativeTamagawaMeasure_integerUnits, h, ENNReal.toReal_one,
    Complex.ofReal_one]

private theorem weilModifiedFiniteIntegral_eventually_one
    (K : (v : V) → Set (v.adicCompletion F))
    (uniformizer : (v : V) → (v.adicCompletion F)ˣ)
    (hπ : ∀ v : V, (valuation(v)).IsUniformizer (uniformizer v).val)
    (hK : ∀ᶠ v in cofinite, K v = v.adicCompletionIntegers F)
    (L : Set X) (hL : IsCompact L) :
    ∀ᶠ v in cofinite, ∀ c ∈ L,
      weilModifiedFiniteIntegral v (uniformizer v) ((K v).indicator (fun _ ↦ 1)) c = 1 := by
  classical
  obtain ⟨t, ht⟩ := hL.elim_finite_subcover (fun S : Finset V ↦ (unramifiedOutside F S : Set X))
    (fun S ↦ (unramifiedOutside F S).isOpen) (by rw [iUnion_unramifiedOutside]; exact subset_univ L)
  have hmass : ∀ᶠ v : V in cofinite, (μv v) (v.adicCompletionIntegers F).units = 1 := by
    simpa only [finiteLocalMultiplicativeTamagawaMeasure_integerUnits, eventually_cofinite]
      using finiteLocalTamagawaMass_finite F
  filter_upwards [hK, hmass, (t.biUnion id).finite_toSet.compl_mem_cofinite] with v hv hm hv₀ c hc
  obtain ⟨S, hSt, hcS⟩ := mem_iUnion₂.mp (ht hc)
  have hvS : v ∉ S := fun h ↦ hv₀ (Finset.mem_biUnion.mpr ⟨S, hSt, h⟩)
  rw [hv, weilModifiedFiniteIntegral_integerRing v _ (hπ v) c (hcS v hvS), hm]
  simp

/-- Paper: Theorem 3.4.1.1, p. 143. The finite-place factors of the modified
zeta product differ from one by an absolutely summable family. -/
theorem weilModifiedZeta_summable
    (K : (v : V) → Set (v.adicCompletion F))
    (uniformizer : (v : V) → (v.adicCompletion F)ˣ)
    (hπ : ∀ v : V, (valuation(v)).IsUniformizer (uniformizer v).val)
    (hKc : ∀ v : V, IsCompact (K v)) (hKo : ∀ v : V, IsOpen (K v))
    (hK : ∀ᶠ v in cofinite, K v = v.adicCompletionIntegers F) (c : X) (hc : c ∈ positive) :
    Summable (fun v : V ↦
      ‖weilModifiedFiniteIntegral v (uniformizer v) ((K v).indicator (fun _ ↦ 1)) c - 1‖) := by
  have h := weilModifiedFiniteIntegral_eventually_one K uniformizer hπ hK {c} isCompact_singleton
  apply summable_of_hasFiniteSupport
  apply eventually_cofinite.mp
  filter_upwards [h] with v hv
  simp [hv c (mem_singleton c)]

/-- Paper: Theorem 3.4.1.1, p. 143. The net of partial modified products
converges uniformly on compact sets of quasi-characters of positive abscissa. -/
theorem weilModifiedZeta_tendstoUniformlyOn (fArch : ℬ(AArch))
    (K : (v : V) → Set (v.adicCompletion F))
    (uniformizer : (v : V) → (v.adicCompletion F)ˣ)
    (hπ : ∀ v : V, (valuation(v)).IsUniformizer (uniformizer v).val)
    (hKc : ∀ v : V, IsCompact (K v)) (hKo : ∀ v : V, IsOpen (K v))
    (hK : ∀ᶠ v in cofinite, K v = v.adicCompletionIntegers F)
    (L : Set X) (hL : IsCompact L) (hLpos : L ⊆ positive) :
    TendstoUniformlyOn (fun S : Finset V ↦ fun c ↦
      weilArchimedeanIntegral fArch c *
        ∏ v ∈ S, weilModifiedFiniteIntegral v (uniformizer v) ((K v).indicator (fun _ ↦ 1)) c)
      (weilModifiedZeta fArch K uniformizer) atTop L := by
  classical
  have h := eventually_cofinite.mp (weilModifiedFiniteIntegral_eventually_one K uniformizer hπ hK L hL)
  intro U hU
  filter_upwards [eventually_ge_atTop h.toFinset] with S hS c hc
  have htail (v : V) (hv : v ∉ S) :
      weilModifiedFiniteIntegral v (uniformizer v) ((K v).indicator (fun _ ↦ 1)) c = 1 := by
    have hv' : v ∉ h.toFinset := fun hmem ↦ hv (hS hmem)
    simp only [Finite.mem_toFinset, mem_setOf_eq, not_not] at hv'
    exact hv' c hc
  rw [weilModifiedZeta, tprod_eq_prod htail]
  exact refl_mem_uniformity hU

private theorem ideleClassNormTwist_abscissa (χ : PontryaginDual C_F) (s : ℂ) :
    quasiCharacterAbscissa (ideleClassNorm F) (isProperMap_ideleClassNorm F)
      (ideleClassNorm_ne_one (F := F)) (ideleClassNormTwist χ s) = s.re :=
  quasiCharacterAbscissa_of_unitary_twist _ _ _ _ χ s (fun _ ↦ rfl)

private theorem ideleClassNormTwist_unramified_iff (χ : PontryaginDual C_F) (s : ℂ) (v : V) :
    (ideleClassNormTwist χ s).IsUnramifiedAt v ↔ (ideleClassNormTwist χ 0).IsUnramifiedAt v := by
  simp only [HeckeCharacter.isUnramifiedAt_iff]
  apply forall_congr'
  intro u
  let g := Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u
  have hn : ‖(g : v.adicCompletion F)‖ = 1 := Valued.toNormedField.norm_eq_one_iff.mpr
    (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp
      (show g ∈ (v.adicCompletionIntegers F).units from ⟨u.val.property, u.inv.property⟩))
  have he (z : ℂ) : (ideleClassNormTwist χ z).restrict v g =
      (χ (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v g) : ℂ) := by
    rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
    change _ * (((ideleClassNorm F (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v g) : ℝ≥0) : ℝ) : ℂ) ^ z = _
    rw [ideleClassNorm_ofAdicCompletion]
    change _ * (‖(g : v.adicCompletion F)‖ : ℂ) ^ z = _
    rw [hn, Complex.ofReal_one, Complex.one_cpow, mul_one]
    rfl
  change (ideleClassNormTwist χ s).restrict v g = 1 ↔ (ideleClassNormTwist χ 0).restrict v g = 1
  rw [he, he]

section

private theorem analyticOnNhd_integral_normTwist {G : Type*} [TopologicalSpace G]
    [MeasurableSpace G] [OpensMeasurableSpace G] (μ : Measure G) (f : G → ℂ)
    (ι : G → C_F) (hι : Continuous ι) (χ : PontryaginDual C_F)
    (hint : ∀ s : ℂ, 0 < s.re → Integrable (fun g ↦ f g * ideleClassNormTwist χ s (ι g)) μ) :
    AnalyticOnNhd ℂ (fun s ↦ ∫ g, f g * ideleClassNormTwist χ s (ι g) ∂μ) (Complex.re ⁻¹' Ioi 0) := by
  let n (g : G) : ℝ := normℝ (ι g)
  have hn : Measurable n := (NNReal.continuous_coe.comp (Units.continuous_val.comp
    ((isProperMap_ideleClassNorm F).continuous.comp hι))).measurable
  have h (s : ℂ) (g : G) : f g * ideleClassNormTwist χ s (ι g) =
      (f g * (χ (ι g) : ℂ)) * (n g : ℂ) ^ s := (mul_assoc _ _ _).symm
  simp_rw [h] at hint ⊢
  exact analyticOnNhd_integral_mul_cpow_of_integrable μ _ n hn (fun _ ↦ NNReal.coe_pos.mpr (Units.zero_lt _))
    isOpen_Ioi hint

end

/-- Paper: Theorem 3.4.1.1, p. 143. The modified zeta product is holomorphic
on the positive half-plane in each unitary norm-twist coordinate. -/
theorem weilModifiedZeta_analyticOn (fArch : ℬ(AArch))
    (K : (v : V) → Set (v.adicCompletion F))
    (uniformizer : (v : V) → (v.adicCompletion F)ˣ)
    (hπ : ∀ v : V, (valuation(v)).IsUniformizer (uniformizer v).val)
    (hKc : ∀ v : V, IsCompact (K v)) (hKo : ∀ v : V, IsOpen (K v))
    (hK : ∀ᶠ v in cofinite, K v = v.adicCompletionIntegers F) (χ : PontryaginDual C_F) :
    AnalyticOnNhd ℂ (fun s ↦ weilModifiedZeta fArch K uniformizer (ideleClassNormTwist χ s))
      (Complex.re ⁻¹' Ioi 0) := by
  classical
  let c := ideleClassNormTwist χ
  have hpos (z : ℂ) (hz : 0 < z.re) : c z ∈ positive := by
    change 0 < quasiCharacterAbscissa _ _ _ _
    rwa [ideleClassNormTwist_abscissa]
  have hArch : AnalyticOnNhd ℂ (fun z ↦ weilArchimedeanIntegral fArch (c z)) (Complex.re ⁻¹' Ioi 0) := by
    letI := (fun {m} (_ : @Measure AArchˣ m) ↦ m) μArch
    let : BorelSpace AArchˣ := sIdeleGroup_borelSpace
    apply analyticOnNhd_integral_normTwist μArch (fun g : AArchˣ ↦ fArch (Multiplicative.ofAdd g.val))
      (fun g ↦ classOf (sIdeleInsertion F ∅ g)) (continuous_quotient_mk'.comp
        (isClosedEmbedding_sIdeleInsertion F ∅).continuous) χ
    exact fun z hz ↦ weilArchimedeanIntegral_integrable fArch (c z) (hpos z hz)
  let factor (v : V) (z : ℂ) := weilModifiedFiniteIntegral v (uniformizer v)
    ((K v).indicator (fun _ ↦ 1)) (c z)
  have hfactor (v : V) : AnalyticOnNhd ℂ (factor v) (Complex.re ⁻¹' Ioi 0) := by
    let : BorelSpace (v.adicCompletion F)ˣ := ⟨rfl⟩
    let f := (K v).indicator (fun _ ↦ (1 : ℂ))
    let test := if (c 0).IsUnramifiedAt v then fun x ↦ f x - f ((↑(uniformizer v)⁻¹ : v.adicCompletion F) * x)
      else f
    have he (z : ℂ) : factor v z = ∫ g : (v.adicCompletion F)ˣ, test g.val *
        c z (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v g) ∂μv v := by
      simp only [factor, weilModifiedFiniteIntegral, c, ideleClassNormTwist_unramified_iff χ z, test, f]
      rfl
    change AnalyticOnNhd ℂ (fun z ↦ factor v z) _
    simp_rw [he]
    apply analyticOnNhd_integral_normTwist _ _ _ (continuous_ideleClass_ofAdicCompletion F v) χ
    intro z hz
    have h := weilModifiedFiniteIntegral_integrable v (uniformizer v) (hπ v) (K v)
      (hKc v) (hKo v) (c z) (hpos z hz)
    simp only [c, ideleClassNormTwist_unramified_iff χ z] at h
    exact h
  obtain ⟨T, hT⟩ : ∃ T : Finset V, c 0 ∈ unramifiedOutside F T :=
    mem_iUnion.mp ((iUnion_unramifiedOutside F).symm ▸ mem_univ (c 0))
  have htail : ∀ᶠ v : V in cofinite, ∀ z, factor v z = 1 := by
    have hm : ∀ᶠ v : V in cofinite, (μv v) (v.adicCompletionIntegers F).units = 1 := by
      simpa only [finiteLocalMultiplicativeTamagawaMeasure_integerUnits, eventually_cofinite]
        using finiteLocalTamagawaMass_finite F
    filter_upwards [hK, hm, T.finite_toSet.compl_mem_cofinite] with v hv hm hvT z
    have hu := (ideleClassNormTwist_unramified_iff χ z v).mpr (hT v hvT)
    simp only [factor, c, hv, weilModifiedFiniteIntegral_integerRing v _ (hπ v) _ hu, hm, ENNReal.toReal_one,
      Complex.ofReal_one]
  let S := (eventually_cofinite.mp htail).toFinset
  have he (z : ℂ) : weilModifiedZeta fArch K uniformizer (c z) =
      weilArchimedeanIntegral fArch (c z) * ∏ v ∈ S, factor v z := by
    apply congrArg (_ * ·)
    exact tprod_eq_prod fun v hv ↦ (by simpa [S] using hv : ∀ t, factor v t = 1) z
  change AnalyticOnNhd ℂ (fun z ↦ weilModifiedZeta fArch K uniformizer (c z)) _
  simp_rw [he]
  exact hArch.mul (S.analyticOnNhd_fun_prod fun v _ ↦ hfactor v)

section

private def quasiCharacterPhase {G : Type*} [Group G] [TopologicalSpace G]
    (d : QuasiCharacter G) : PontryaginDual G := by
  have hn (x : G) : (‖d x‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr ((Group.isUnit x).map d).ne_zero)
  exact
    { toFun x := ⟨d x / (‖d x‖ : ℂ), mem_sphere_zero_iff_norm.mpr (by
        rw [norm_div, Complex.norm_of_nonneg (norm_nonneg _), div_self (by exact_mod_cast hn x)])⟩
      map_one' := Subtype.ext (by simp)
      map_mul' x y := Subtype.ext (by
        change d (x * y) / (‖d (x * y)‖ : ℂ) =
          (d x / ↑‖d x‖) * (d y / ↑‖d y‖)
        rw [map_mul, norm_mul, Complex.ofReal_mul, div_mul_div_comm])
      continuous_toFun := (d.continuous.div (Complex.continuous_ofReal.comp d.continuous.norm)
        hn).subtype_mk _ }

end

/-- Paper: Proof of Theorem 3.4.1.1, p. 144. For a character of positive abscissa
unramified at every finite place, the archimedean integral equals the continued
S-idelic Z-function with no finite places. -/
theorem weilArchimedeanIntegral_eq_sLocal (fArch : ℬ(AArch)) (c : X)
    (hc : c ∈ unramifiedOutside F ∅) (hpos : c ∈ positive) :
    weilArchimedeanIntegral fArch c =
      sLocalIdelicZFunction fArch (sIdeleRestriction F ∅ ⟨c, hc⟩) := by
  let d := sIdeleRestriction F ∅ ⟨c, hc⟩
  let a := quasiCharacterAbscissa (ideleClassNorm F) (isProperMap_ideleClassNorm F)
    (ideleClassNorm_ne_one (F := F)) c
  have hInt : weilArchimedeanIntegral fArch c = sLocalIdelicZetaIntegral fArch d := by
    unfold weilArchimedeanIntegral sLocalIdelicZetaIntegral
    congr 1
  refine hInt.trans (sLocalIdelicZFunction_eq_integral fArch (x := d) ?_).symm
  refine ⟨quasiCharacterPhase d, (a : ℂ), hpos, ContinuousMonoidHom.ext fun x ↦ ?_⟩
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  let y : C_F := classOf (sIdeleInsertion F ∅ g)
  let : T2Space C_F := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.1
  let : LocallyCompactSpace C_F := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.1
  have hnorm := norm_quasiCharacter_eq_rpow_abscissa (ideleClassNorm F)
    (isProperMap_ideleClassNorm F) (ideleClassNorm_ne_one (F := F)) c y
  change c y = c y / (‖c y‖ : ℂ) * (((sIdeleNorm F ∅ g : ℝ≥0) : ℝ) : ℂ) ^ (a : ℂ)
  rw [← ideleNorm_sIdeleInsertion, ← Complex.ofReal_cpow (by positivity)]
  change c y = c y / (‖c y‖ : ℂ) * (((normℝ y) ^ a : ℝ) : ℂ)
  rw [← hnorm, div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr ((Group.isUnit y).map c).ne_zero))]

-- TODO(paper-gap): Equations (3.4.1.5)–(3.4.1.6) omit the outside integer-unit masses.
-- In (3.4.1.6) the ramified finite Euler factors are one, and the continuation
-- on the positive half-plane can have a pole. Footnote 3 asks for the product comparison.

section

local notation "ArchUnits" => (w : InfinitePlace F) → w.Completionˣ
local notation "FinUnits(" S ")" => (v : (S : Finset V)) → (v.val.adicCompletion F)ˣ
local notation "μ∞" => infiniteLocalMultiplicativeTamagawaMeasure F

local instance (w : InfinitePlace F) : MeasurableSpace w.Completion := borel _

private def sUnitsOfCoordinates (S : Finset V) : (ArchUnits × FinUnits(S)) ≃ₜ (SAdeleRing F S)ˣ :=
  ((ContinuousMulEquiv.piUnits (M := fun w : InfinitePlace F ↦ w.Completion)).symm.toHomeomorph.prodCongr
    (ContinuousMulEquiv.piUnits (M := fun v : S ↦ v.val.adicCompletion F)).symm.toHomeomorph).trans
    (ContinuousMulEquiv.prodUnits (InfiniteAdeleRing F) ((v : S) → v.val.adicCompletion F)).symm.toHomeomorph

private theorem integral_sUnitsOfCoordinates (S : Finset V) (H : (SAdeleRing F S)ˣ → ℂ) :
    (∫ g, H g ∂sMultiplicativeTamagawaMeasure F S) =
      ∫ p, H (sUnitsOfCoordinates S p)
        ∂(Measure.pi μ∞).prod (Measure.pi fun v : S ↦ μv v.val) := by
  let := (fun {m} (_ : @Measure (SAdeleRing F S)ˣ m) ↦ m) (sMultiplicativeTamagawaMeasure F S)
  let : BorelSpace (SAdeleRing F S)ˣ := sIdeleGroup_borelSpace
  let (w : InfinitePlace F) : BorelSpace w.Completion := ⟨rfl⟩
  let (w : InfinitePlace F) : BorelSpace w.Completionˣ := borelSpace_units_of_continuousInv₀ _
  let (v : S) : BorelSpace (v.val.adicCompletion F)ˣ := ⟨rfl⟩
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let (w : InfinitePlace F) : SecondCountableTopology w.Completionˣ := Units.isEmbedding_val₀.secondCountableTopology
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (v : S) : SecondCountableTopology (v.val.adicCompletion F)ˣ := Units.isEmbedding_val₀.secondCountableTopology
  exact integral_map_equiv (sUnitsOfCoordinates S).toMeasurableEquiv H

private theorem sIdeleInsertion_coordinates (S : Finset V) (c : X) (p : ArchUnits × FinUnits(S)) :
    c (classOf (sIdeleInsertion F S (sUnitsOfCoordinates S p))) =
      c (classOf (sIdeleInsertion F ∅ (sUnitsOfCoordinates ∅ (p.1, 1)))) *
        ∏ v : S, finitePlaceRestriction F v.val c (p.2 v) := by
  classical
  let d : I_F →* ℂ := c.toMonoidHom.comp (QuotientGroup.mk' _)
  change d (sIdeleInsertion F S _) = d (sIdeleInsertion F ∅ _) * _
  simp only [sIdeleInsertion, MonoidHom.mul_apply, MonoidHom.finsetProd_apply, MonoidHom.comp_apply,
    map_mul, map_prod, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
  rfl

private theorem sLocalIntegral_arch_mul_prod (S : Finset V) (fS : ℬ(SAdeleRing F S))
    (fArch : ℬ(AArch)) (f : (v : S) → v.val.adicCompletion F → ℂ)
    (hf : ∀ x : SAdeleRing F S, fS (Multiplicative.ofAdd x) = fArch (Multiplicative.ofAdd (x.1, 0)) *
      ∏ v, f v (x.2 v)) (c : X) (hc : c ∈ unramifiedOutside F S) :
    sLocalIdelicZetaIntegral fS (sIdeleRestriction F S ⟨c, hc⟩) =
      weilArchimedeanIntegral fArch c *
        ∏ v : S, localIdelicZetaIntegral (μv v.val) (f v) (finitePlaceRestriction F v.val c) := by
  classical
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let (w : InfinitePlace F) : SecondCountableTopology w.Completionˣ := Units.isEmbedding_val₀.secondCountableTopology
  let (w : InfinitePlace F) : LocallyCompactSpace w.Completionˣ :=
    (IsOpenUnits.isOpenEmbedding_unitsVal (M := w.Completion)).locallyCompactSpace
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (v : S) : SecondCountableTopology (v.val.adicCompletion F)ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let (v : S) : LocallyCompactSpace (v.val.adicCompletion F)ˣ :=
    (IsOpenUnits.isOpenEmbedding_unitsVal (M := v.val.adicCompletion F)).locallyCompactSpace
  let (w : InfinitePlace F) : (μ∞ w).IsHaarMeasure := infiniteLocalMultiplicativeTamagawaMeasure_haar F w
  let (v : S) : (μv v.val).IsHaarMeasure := finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure v.val
  let (w : InfinitePlace F) : BorelSpace w.Completion := ⟨rfl⟩
  let (w : InfinitePlace F) : BorelSpace w.Completionˣ := borelSpace_units_of_continuousInv₀ _
  let (v : V) : BorelSpace (v.adicCompletion F)ˣ := ⟨rfl⟩
  let (w : InfinitePlace F) : SigmaFinite (μ∞ w) := inferInstance
  let (v : S) : SigmaFinite (μv v.val) := inferInstance
  let (v : (∅ : Finset V)) : SigmaFinite (μv v.val) := isEmptyElim v
  let a (p : ArchUnits) := let g := sUnitsOfCoordinates ∅ (p, 1)
    fArch (Multiplicative.ofAdd g.val) * c (classOf (sIdeleInsertion F ∅ g))
  let b (v : S) (u : (v.val.adicCompletion F)ˣ) := f v u.val * finitePlaceRestriction F v.val c u
  have ha : weilArchimedeanIntegral fArch c = ∫ p, a p ∂Measure.pi μ∞ := by
    rw [weilArchimedeanIntegral, integral_sUnitsOfCoordinates]
    calc _ = ∫ p : ArchUnits × FinUnits(∅), a p.1 * (1 : ℂ)
              ∂(Measure.pi μ∞).prod (Measure.pi fun v : (∅ : Finset V) ↦ μv v.val) := by
                apply integral_congr_ae
                filter_upwards with p
                rw [mul_one]
                obtain ⟨x, y⟩ := p
                rw [Subsingleton.elim y 1]
      _ = _ := by
        rw [integral_prod_mul (μ := Measure.pi μ∞) (ν := Measure.pi fun v : (∅ : Finset V) ↦ μv v.val)
          a (fun _ ↦ (1 : ℂ))]
        simp [measureReal_def]
  rw [sLocalIdelicZetaIntegral, integral_sUnitsOfCoordinates, ha]
  calc _ = ∫ p : ArchUnits × FinUnits(S), a p.1 * ∏ v, b v (p.2 v)
            ∂(Measure.pi μ∞).prod (Measure.pi fun v : S ↦ μv v.val) := by
              apply integral_congr_ae
              filter_upwards with p
              rw [sIdeleRestriction_mk, sIdeleInsertion_coordinates, hf]
              simp only [a, b, Finset.prod_mul_distrib]
              have he : ((sUnitsOfCoordinates S p).val.1, (0 : (v : (∅ : Finset V)) → v.val.adicCompletion F)) =
                  (sUnitsOfCoordinates ∅ (p.1, 1)).val := Prod.ext rfl (Subsingleton.elim _ _)
              rw [he]
              ac_rfl
    _ = _ := by
      rw [integral_prod_mul (μ := Measure.pi μ∞) (ν := Measure.pi fun v : S ↦ μv v.val) a
        (fun p ↦ ∏ v, b v (p v)), integral_fintype_prod_eq_prod b]
      rfl

end

open Classical in
/-- Paper: Equation (3.4.1.5), p. 143. The modified product factors through the
S₀-idelic integral over the archimedean and ramified places, with modified factors at
the remaining exceptional places in S.
Deviation: The Tamagawa masses of the integer units outside S are included. The finite
sets S₀ and S index only finite places, since all archimedean places are implicit. -/
theorem weilModifiedZeta_eq_sLocal (S₀ S : Finset V) (hS : S₀ ⊆ S)
    (fArch : ℬ(AArch)) (fS₀ : ℬ(SAdeleRing F S₀))
    (K : (v : V) → Set (v.adicCompletion F))
    (uniformizer : (v : V) → (v.adicCompletion F)ˣ)
    (hπ : ∀ v : V, (valuation(v)).IsUniformizer (uniformizer v).val)
    (hKc : ∀ v : V, IsCompact (K v)) (hKo : ∀ v : V, IsOpen (K v))
    (hK : ∀ v ∉ S, K v = v.adicCompletionIntegers F)
    (hfS₀ : ∀ x : SAdeleRing F S₀, fS₀ (Multiplicative.ofAdd x) =
      fArch (Multiplicative.ofAdd (x.1, 0)) *
        ∏ v : S₀, (K v.val).indicator (fun _ ↦ (1 : ℂ)) (x.2 v))
    (c : X) (hc : c ∈ positive) (hc₀ : c ∈ unramifiedOutside F S₀)
    (hram : ∀ v ∈ S₀, ¬ c.IsUnramifiedAt v) :
    weilModifiedZeta fArch K uniformizer c =
      (∏ᶠ v : {v : V // v ∉ S}, (((μv v.val) (v.val.adicCompletionIntegers F).units).toReal : ℂ)) *
        sLocalIdelicZetaIntegral fS₀ (sIdeleRestriction F S₀ ⟨c, hc₀⟩) *
        ∏ v ∈ S \ S₀,
          weilModifiedFiniteIntegral v (uniformizer v) ((K v).indicator (fun _ ↦ 1)) c := by
  classical
  let f (v : V) := (K v).indicator (fun _ ↦ (1 : ℂ))
  let E (v : V) := weilModifiedFiniteIntegral v (uniformizer v) (f v) c
  let M (v : V) : ℂ := ((μv v) (v.adicCompletionIntegers F).units).toReal
  have he (v : V) (hv : v ∉ S) : E v = M v := by
    dsimp only [E, f]
    rw [hK v hv]
    exact weilModifiedFiniteIntegral_integerRing v _ (hπ v) c (hc₀ v (fun h ↦ hv (hS h)))
  have hm : M.HasFiniteMulSupport := by
    apply eventually_cofinite.mp
    have hmass : ∀ᶠ v : V in cofinite, (μv v) (v.adicCompletionIntegers F).units = 1 := by
      simpa only [finiteLocalMultiplicativeTamagawaMeasure_integerUnits, eventually_cofinite]
        using finiteLocalTamagawaMass_finite F
    filter_upwards [hmass] with v hv
    simp [M, hv]
  let C := (S : Set V)ᶜ
  have hMC : (fun v : C ↦ M v.val).HasFiniteMulSupport :=
    hm.preimage Subtype.val_injective.injOn
  have htail : HasProd (fun v : C ↦ E v.val) (∏ᶠ v : C, M v.val) := by
    rw [← tprod_eq_finprod (L := SummationFilter.unconditional _) hMC]
    exact (multipliable_of_hasFiniteMulSupport hMC).hasProd.congr_fun fun v ↦ he v v.property
  have hprod : ∏' v, E v = (∏ v ∈ S, E v) * ∏ᶠ v : C, M v.val :=
    ((S.hasProd E).mul_compl htail).tprod_eq
  have hlocal := sLocalIntegral_arch_mul_prod S₀ fS₀ fArch (fun v ↦ f v.val) hfS₀ c hc₀
  have hramE (v : S₀) : localIdelicZetaIntegral (μv v.val) (f v.val) (finitePlaceRestriction F v.val c) =
      E v.val := by simp only [E, weilModifiedFiniteIntegral, hram v.val v.property, ite_false]
  simp_rw [hramE] at hlocal
  rw [← Finset.prod_subtype S₀ (fun _ ↦ Iff.rfl) E] at hlocal
  change weilArchimedeanIntegral fArch c * (∏' v, E v) =
    (∏ᶠ v : C, M v.val) * sLocalIdelicZetaIntegral fS₀ _ * ∏ v ∈ S \ S₀, E v
  rw [hprod, ← Finset.prod_sdiff hS, hlocal]
  ring

private theorem weilModifiedFiniteIntegral_eq_inv_euler_mul (v : V) (π : (v.adicCompletion F)ˣ)
    (hπ : (valuation(v)).IsUniformizer π.val) (K : Set (v.adicCompletion F))
    (hK : IsCompact K) (hKo : IsOpen K) (χ : PontryaginDual C_F) (s : ℂ) (hs : 1 < s.re) :
    let c := ideleClassNormTwist χ s
    let f := K.indicator (fun _ ↦ (1 : ℂ))
    weilModifiedFiniteIntegral v π f c =
      (finiteHeckeEulerFactor χ v s)⁻¹ * localIdelicZetaIntegral (μv v) f (finitePlaceRestriction F v c) := by
  classical
  let c := ideleClassNormTwist χ s
  let d := finitePlaceRestriction F v c
  let f := K.indicator (fun _ ↦ (1 : ℂ))
  change weilModifiedFiniteIntegral v π f c = _ * localIdelicZetaIntegral _ f d
  by_cases hu : c.IsUnramifiedAt v
  · have hu₀ := (ideleClassNormTwist_unramified_iff χ s v).mp hu
    rw [finiteHeckeEulerFactor_inv_uniformizer χ v π hπ hu₀ hs]
    have hf : ∃ k : ℬ(v.adicCompletion F), ∀ x, k (Multiplicative.ofAdd x) = f x := by
      apply (mem_finitePlaceSchwartz_iff F v f).2
      refine ⟨(LocallyConstant.charFn ℂ ⟨hK.isClosed, hKo⟩).isLocallyConstant, ?_⟩
      exact hK.of_isClosed_subset isClosed_closure (closure_minimal support_indicator_subset hK.isClosed)
    obtain ⟨k, hk⟩ := hf
    let χv := χ.comp ⟨IdeleClassGroup.ofAdicCompletion (𝓞 F) F v, continuous_ideleClass_ofAdicCompletion F v⟩
    let m := finiteNorm(v)
    have hd (g : (v.adicCompletion F)ˣ) : d g =
        quasiCharacterNormTwist m (continuous_finiteLocalModule v) ((circleToComplex).comp χv) s g := by
      change _ * (((ideleClassNorm F (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v g) : ℝ≥0) : ℝ) : ℂ) ^ s = _
      rw [ideleClassNorm_ofAdicCompletion]
      rfl
    let : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
    let : SecondCountableTopology (v.adicCompletion F)ˣ := Units.isEmbedding_val₀.secondCountableTopology
    let := finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure v
    let : BorelSpace (v.adicCompletion F)ˣ := ⟨rfl⟩
    let b (g : (v.adicCompletion F)ˣ) := f g.val * d g
    have hb : Integrable b (μv v) := by
      apply (finiteLocalIdelicZetaIntegral_integrable v k χv (s := s) (zero_lt_one.trans hs)).congr
      filter_upwards with g
      rw [← hd, hk]
    have ht (g : (v.adicCompletion F)ˣ) :
        f ((↑π⁻¹ : v.adicCompletion F) * g.val) * d g = d π * b (π⁻¹ * g) := by
      simp only [b, Units.val_mul, map_mul]
      have hi : d π * d π⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
      linear_combination -(f ((↑π⁻¹ : v.adicCompletion F) * g.val) * d g) * hi
    have hshift : Integrable (fun g ↦ d π * b (π⁻¹ * g)) (μv v) :=
      ((measurePreserving_mul_left (μv v) π⁻¹).integrable_comp_of_integrable hb).const_mul _
    unfold weilModifiedFiniteIntegral localIdelicZetaIntegral
    simp only [hu, ite_true, sub_mul]
    simp_rw [show ∀ g, f ((↑π⁻¹ : v.adicCompletion F) * g.val) * finitePlaceRestriction F v c g =
      d π * b (π⁻¹ * g) from ht]
    rw [integral_sub hb hshift, integral_const_mul, integral_mul_left_eq_self]
    rw [one_mul]
  · have hu₀ : ¬ (ideleClassNormTwist χ 0).IsUnramifiedAt v := fun h ↦ hu ((ideleClassNormTwist_unramified_iff χ s v).mpr h)
    simp only [weilModifiedFiniteIntegral, hu, ite_false, finiteHeckeEulerFactor, hu₀, inv_one, one_mul]
    rfl

private theorem finiteHeckeEulerFactor_ne_zero_of_one_lt (χ : PontryaginDual C_F) (v : V) (z : ℂ) (hz : 1 < z.re) :
    finiteHeckeEulerFactor χ v z ≠ 0 := by
  classical
  have hq : 1 < (v.asIdeal.absNorm : ℝ) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hlt : ‖(ideleClassNormTwist χ 0).localValue v * (v.asIdeal.absNorm : ℂ) ^ (-z)‖ < 1 := by
    rw [norm_mul, norm_ideleClassNormTwist_zero_localValue, one_mul,
      ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hq)]
    exact Real.rpow_lt_one_of_one_lt_of_neg hq (by simp only [Complex.neg_re]; linarith)
  unfold finiteHeckeEulerFactor
  split_ifs
  · exact inv_ne_zero (sub_ne_zero.mpr fun h ↦ (ne_of_lt hlt) (h ▸ norm_one))
  · exact one_ne_zero

section

open scoped Classical
local notation "ArchUnits" => (w : InfinitePlace F) → w.Completionˣ
local notation "FinUnits(" S ")" => (v : (S : Finset V)) → (v.val.adicCompletion F)ˣ
local notation "μ∞" => infiniteLocalMultiplicativeTamagawaMeasure F
local notation "O(" v ")" => (HeightOneSpectrum.adicCompletionIntegers F v)
local notation "archAt" => fun w : InfinitePlace F ↦ Units.map
  ((Pi.evalRingHom InfinitePlace.Completion w).comp (RingHom.fst (InfiniteAdeleRing F)
    (FiniteAdeleRing (𝓞 F) F))).toMonoidHom
local notation "finiteAt" => fun v : V ↦ Units.map
  ((RestrictedProduct.evalRingHom (fun w : V ↦ w.adicCompletion F) v).comp
    (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))).toMonoidHom

private local instance : MeasurableSpace I_F := borel _
private local instance : BorelSpace I_F := ⟨rfl⟩
private local instance (w : InfinitePlace F) : MeasurableSpace w.Completion := borel _
private local instance (w : InfinitePlace F) : BorelSpace w.Completion := ⟨rfl⟩
private local instance (w : InfinitePlace F) : BorelSpace w.Completionˣ := borelSpace_units_of_continuousInv₀ _
private local instance (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
  (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
private local instance (w : InfinitePlace F) : SecondCountableTopology w.Completionˣ :=
  Units.isEmbedding_val₀.secondCountableTopology
private local instance (w : InfinitePlace F) : LocallyCompactSpace w.Completionˣ :=
  (IsOpenUnits.isOpenEmbedding_unitsVal (M := w.Completion)).locallyCompactSpace
private local instance (v : V) : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
private local instance (v : V) : BorelSpace (v.adicCompletion F)ˣ := ⟨rfl⟩
private local instance (v : V) : SecondCountableTopology (v.adicCompletion F)ˣ :=
  Units.isEmbedding_val₀.secondCountableTopology
private local instance (v : V) : LocallyCompactSpace (v.adicCompletion F)ˣ :=
  (IsOpenUnits.isOpenEmbedding_unitsVal (M := v.adicCompletion F)).locallyCompactSpace
private local instance (w : InfinitePlace F) : (μ∞ w).IsHaarMeasure := infiniteLocalMultiplicativeTamagawaMeasure_haar F w
private local instance (v : V) : (μv v).IsHaarMeasure := finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure v
private local instance : Countable V :=
  Countable.of_preimage_singleton (f := fun v : V ↦ v.asIdeal.absNorm) fun n ↦
    (Ring.HasFiniteQuotients.finite_absNorm_heightOneSpectrum_le (S := 𝓞 F) n).countable.mono
      fun v (hv : v.asIdeal.absNorm = n) ↦ hv.le

private def outsideUnitIdeles (S : Finset V) : Set I_F :=
  {g | ∀ v ∉ S, (finiteAt) v g ∈ (O(v)).units}

private def idelicCoordinates (S : Finset V) (g : I_F) : ArchUnits × FinUnits(S) :=
  (fun w ↦ (archAt) w g, fun v ↦ (finiteAt) v.val g)

private theorem continuous_finiteAt (v : V) : Continuous ((finiteAt) v) :=
  ((RestrictedProduct.continuous_eval v).comp continuous_snd).units_map _

private theorem continuous_idelicCoordinates (S : Finset V) : Continuous (idelicCoordinates S (F := F)) :=
  (continuous_pi fun w ↦ ((continuous_apply w).comp continuous_fst).units_map _).prodMk
    (continuous_pi fun v ↦ continuous_finiteAt v.val)

private theorem measurableSet_outsideUnitIdeles (S : Finset V) : MeasurableSet (outsideUnitIdeles (F := F) S) := by
  simp only [outsideUnitIdeles, ofPred_forall]
  apply MeasurableSet.iInter
  intro v
  apply MeasurableSet.iInter
  intro _
  have hc : Continuous (fun g : I_F ↦ (finiteAt) v g) := continuous_finiteAt v
  exact hc.measurable (Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)).measurableSet

/-- Once the selected places contain the finite different, projection of the
restricted global measure is exactly the product of the selected local measures. -/
private theorem map_outsideUnitIdeles (S : Finset V) (hS : ∀ v ∉ S, (μv v) (O(v)).units = 1) :
    ((multiplicativeTamagawaMeasure F).restrict (outsideUnitIdeles S)).map (idelicCoordinates S) =
      (Measure.pi μ∞).prod (Measure.pi fun v : S ↦ μv v.val) := by
  symm
  apply Measure.prod_pi_eq
  intro B U hB hU
  rw [Measure.map_apply (continuous_idelicCoordinates S).measurable ((MeasurableSet.univ_pi hB).prod
    (MeasurableSet.univ_pi hU)), Measure.restrict_apply ((continuous_idelicCoordinates S).measurable
      ((MeasurableSet.univ_pi hB).prod (MeasurableSet.univ_pi hU)))]
  have ht := multiplicativeTamagawaMeasure_restrictedProduct F S B hB U hU
  have he : (idelicCoordinates S) ⁻¹' (univ.pi B ×ˢ univ.pi U) ∩ outsideUnitIdeles S =
      {g : I_F | (∀ w, (archAt) w g ∈ B w) ∧ (∀ v : S, (finiteAt) v.val g ∈ U v) ∧
        ∀ v ∉ S, (finiteAt) v g ∈ (O(v)).units} := by
    ext g
    simp only [mem_inter_iff, mem_preimage, mem_prod, mem_univ_pi, outsideUnitIdeles, mem_ofPred_eq,
      idelicCoordinates, and_assoc]
  rw [he, ht]
  suffices (∏ᶠ v : {v : V // v ∉ S}, (μv v.val) (O(v.val)).units) = 1 by
    simp only [finiteLocalMultiplicativeTamagawaMeasure_integerUnits] at this
    rw [this, mul_one]
  exact finprod_eq_one_of_forall_eq_one fun v ↦ hS v.val v.property

private def sCoordinateIntegrand (S : Finset V) (fS : ℬ(SAdeleRing F S)) (c : X)
    (p : ArchUnits × FinUnits(S)) : ℂ :=
  fS (Multiplicative.ofAdd (sUnitsOfCoordinates S p).val) *
    ((∏ w, infinitePlaceRestriction F w c (p.1 w)) * ∏ v : S, finitePlaceRestriction F v.val c (p.2 v))

private theorem continuous_sCoordinateIntegrand (S : Finset V) (fS : ℬ(SAdeleRing F S)) (c : X) :
    Continuous (sCoordinateIntegrand S fS c) :=
  ((schwartzBruhat_continuous fS).comp (continuous_ofAdd.comp (Units.continuous_val.comp
    (sUnitsOfCoordinates S).continuous))).mul
    ((continuous_finsetProd _ fun w _ ↦ (infinitePlaceRestriction F w c).continuous.comp
      ((continuous_apply w).comp continuous_fst)).mul
    (continuous_finsetProd _ fun v _ ↦ (finitePlaceRestriction F v.val c).continuous.comp
      ((continuous_apply v).comp continuous_snd)))

private theorem sLocalIntegral_eq_coordinates (S : Finset V) (fS : ℬ(SAdeleRing F S)) (c : X)
    (hc : c ∈ unramifiedOutside F S) :
    sLocalIdelicZetaIntegral fS (sIdeleRestriction F S ⟨c, hc⟩) =
      ∫ p, sCoordinateIntegrand S fS c p ∂(Measure.pi μ∞).prod (Measure.pi fun v : S ↦ μv v.val) := by
  rw [sLocalIdelicZetaIntegral, integral_sUnitsOfCoordinates]
  apply integral_congr_ae
  filter_upwards with p
  rw [sIdeleRestriction_mk]
  apply congrArg (_ * ·)
  let d : I_F →* ℂ := c.toMonoidHom.comp (QuotientGroup.mk' _)
  change d (sIdeleInsertion F S _) = _
  simp only [sIdeleInsertion, MonoidHom.mul_apply, MonoidHom.finsetProd_apply, MonoidHom.comp_apply,
    map_mul, map_prod]
  rfl

private theorem sLocalIntegral_pureTensor (S : Finset V) (fS : ℬ(SAdeleRing F S))
    (a : (w : InfinitePlace F) → ℬ(w.Completion)) (b : (v : V) → ℬ(v.adicCompletion F))
    (hf : ∀ x : SAdeleRing F S, fS (Multiplicative.ofAdd x) =
      (∏ w, a w (Multiplicative.ofAdd (x.1 w))) * ∏ v : S, b v.val (Multiplicative.ofAdd (x.2 v)))
    (c : X) (hc : c ∈ unramifiedOutside F S) :
    sLocalIdelicZetaIntegral fS (sIdeleRestriction F S ⟨c, hc⟩) =
      (∏ w, localIdelicZetaIntegral (μ∞ w) (fun y ↦ a w (Multiplicative.ofAdd y)) (infinitePlaceRestriction F w c)) *
      ∏ v : S, localIdelicZetaIntegral (μv v.val) (fun y ↦ b v.val (Multiplicative.ofAdd y)) (finitePlaceRestriction F v.val c) := by
  classical
  let A (w : InfinitePlace F) (g : w.Completionˣ) := a w (Multiplicative.ofAdd g.val) * infinitePlaceRestriction F w c g
  let B (v : S) (g : (v.val.adicCompletion F)ˣ) := b v.val (Multiplicative.ofAdd g.val) * finitePlaceRestriction F v.val c g
  rw [sLocalIntegral_eq_coordinates S fS c hc]
  calc _ = ∫ p : ArchUnits × FinUnits(S), (∏ w, A w (p.1 w)) * ∏ v, B v (p.2 v)
      ∂(Measure.pi μ∞).prod (Measure.pi fun v : S ↦ μv v.val) := by
        apply integral_congr_ae
        filter_upwards with p
        rw [sCoordinateIntegrand, hf]
        simp only [A, B, Finset.prod_mul_distrib]
        ac_rfl
    _ = _ := by
      rw [integral_prod_mul (μ := Measure.pi μ∞) (ν := Measure.pi fun v : S ↦ μv v.val)
        (fun p ↦ ∏ w, A w (p w)) (fun p ↦ ∏ v, B v (p v)), integral_fintype_prod_eq_prod A, integral_fintype_prod_eq_prod B]
      rfl

private theorem setIntegral_outsideUnitIdeles (S T : Finset V) (hST : Disjoint S T)
    (hM : ∀ v ∉ S ∪ T, (μv v) (O(v)).units = 1)
    (fS : ℬ(SAdeleRing F S)) (c : X) (hc : c ∈ unramifiedOutside F S) :
    (∫ g in outsideUnitIdeles (S ∪ T), sAdeleSchwartzToGlobal F S fS (Multiplicative.ofAdd g.val) *
      c (classOf g) ∂multiplicativeTamagawaMeasure F) =
        sLocalIdelicZetaIntegral fS (sIdeleRestriction F S ⟨c, hc⟩) *
          ∏ v : T, localIdelicZetaIntegral (μv v.val)
            ((O(v.val) : Set (v.val.adicCompletion F)).indicator (fun _ ↦ 1))
            (finitePlaceRestriction F v.val c) := by
  let R := S ∪ T
  let i (v : S) : R := ⟨v, Finset.mem_union_left _ v.property⟩
  let j (v : T) : R := ⟨v, Finset.mem_union_right _ v.property⟩
  let K (v : V) := (O(v) : Set (v.adicCompletion F)).indicator (fun _ ↦ (1 : ℂ))
  let b (v : T) (u : (v.val.adicCompletion F)ˣ) := K v.val u.val * finitePlaceRestriction F v.val c u
  let Φ (p : ArchUnits × FinUnits(R)) := sCoordinateIntegrand S fS c (p.1, fun v ↦ p.2 (i v)) *
    ∏ v : T, b v (p.2 (j v))
  have hΦ : Continuous Φ := by
    apply ((continuous_sCoordinateIntegrand S fS c).comp (continuous_fst.prodMk
      (continuous_pi fun v ↦ (continuous_apply (i v)).comp continuous_snd))).mul
    apply continuous_finsetProd
    intro v _
    have hO : IsClopen (O(v.val) : Set (v.val.adicCompletion F)) :=
      ⟨Valued.isClosed_valuationSubring _, Valued.isOpen_valuationSubring _⟩
    have hK : Continuous (K v.val) := (LocallyConstant.charFn ℂ hO).continuous
    exact ((hK.comp Units.continuous_val).mul (finitePlaceRestriction F v.val c).continuous).comp
      ((continuous_apply (j v)).comp continuous_snd)
  have he (g : I_F) (hg : g ∈ outsideUnitIdeles R) :
      sAdeleSchwartzToGlobal F S fS (Multiplicative.ofAdd g.val) * c (classOf g) =
        Φ (idelicCoordinates R g) := by
    let L (v : V) := finitePlaceRestriction F v c ((finiteAt) v g)
    let A := ∏ w, infinitePlaceRestriction F w c ((archAt) w g)
    have hL (v : V) (hv : v ∉ R) : L v = 1 :=
      (mem_unramifiedOutside_iff F S c).mp hc v (fun h ↦ hv (Finset.mem_union_left _ h))
        ((O(v)).unitsEquivUnitsType ⟨(finiteAt) v g, hg v hv⟩)
    have hd := (heckeCharacter_eq_prod_restrictions F c g).2
    change c (classOf g) = A * ∏ᶠ v, L v at hd
    rw [finprod_eq_prod_of_mulSupport_subset (s := R) _ (mulSupport_subset_iff'.mpr hL),
      Finset.prod_union hST, Finset.prod_subtype S (fun _ ↦ Iff.rfl), Finset.prod_subtype T (fun _ ↦ Iff.rfl)] at hd
    refine (congrArg₂ (· * ·) (sAdeleSchwartzToGlobal_apply F S fS g.val) hd).trans ?_
    let a := fS (Multiplicative.ofAdd (adeleProjection F S g.val))
    change (if _ then a else 0) * (A * _) =
      a * (A * ∏ v : S, L v.val) * ∏ v : T, K v.val (g.val.2 v.val) * L v.val
    rw [Finset.prod_mul_distrib]
    by_cases hint : ∀ v ∉ S, g.val.2 v ∈ O(v)
    · have ht : ∏ v : T, K v.val (g.val.2 v.val) = 1 := Finset.prod_eq_one fun v _ ↦
        indicator_of_mem (hint v.val (Finset.disjoint_left.mp hST · v.property)) _
      rw [ite_eq_left hint, ht, one_mul]
      ring
    · have hT : ∃ v : T, g.val.2 v.val ∉ O(v.val) := by
        obtain ⟨v, hv, hx⟩ := not_forall.mp hint |>.imp fun v h ↦ not_imp.mp h
        by_cases h : v ∈ T
        · exact ⟨⟨v, h⟩, hx⟩
        · exact (hx (hg v (Finset.notMem_union.mpr ⟨hv, h⟩)).1).elim
      obtain ⟨v, hv⟩ := hT
      have hzero : (∏ w : T, K w.val (g.val.2 w.val)) = 0 := Finset.prod_eq_zero (Finset.mem_univ v) (indicator_of_notMem hv _)
      rw [ite_eq_right hint, hzero]
      simp
  calc
    _ = ∫ g in outsideUnitIdeles R, Φ (idelicCoordinates R g) ∂multiplicativeTamagawaMeasure F :=
      setIntegral_congr_fun (measurableSet_outsideUnitIdeles R) he
    _ = ∫ p, Φ p ∂(Measure.pi μ∞).prod (Measure.pi fun v : R ↦ μv v.val) := by
      have hm := integral_map (μ := (multiplicativeTamagawaMeasure F).restrict (outsideUnitIdeles R))
        (continuous_idelicCoordinates R).measurable.aemeasurable (f := Φ) hΦ.aestronglyMeasurable
      exact hm.symm.trans (congrArg (fun ν ↦ ∫ p, Φ p ∂ν) (map_outsideUnitIdeles R hM))
    _ = _ := by
      have hφ (a : ArchUnits) (x : FinUnits(S)) (y : FinUnits(T)) :
          Φ (a, MeasurableEquiv.piFinsetUnion (fun v : V ↦ (v.adicCompletion F)ˣ) hST (x, y)) = sCoordinateIntegrand S fS c (a, x) *
            ∏ v : T, b v (y v) := by
        dsimp only [Φ, i, j]
        simp only [MeasurableEquiv.piFinsetUnion_left _ hST (Subtype.property _),
          MeasurableEquiv.piFinsetUnion_right _ hST (Subtype.property _)]
      exact (integral_prod_piFinsetUnion (Measure.pi μ∞) μv hST (sCoordinateIntegrand S fS c) b Φ hφ).trans
        (congrArg (· * _) (sLocalIntegral_eq_coordinates S fS c hc).symm)

private theorem localIntegerRingIntegral_eq_mass_mul_euler (v : V) (χ : PontryaginDual C_F)
    (s : ℂ) (hs : 1 < s.re) (hu : (ideleClassNormTwist χ s).IsUnramifiedAt v) :
    localIdelicZetaIntegral (μv v) ((O(v) : Set (v.adicCompletion F)).indicator fun _ ↦ 1)
      (finitePlaceRestriction F v (ideleClassNormTwist χ s)) =
      ((μv v) (O(v)).units).toReal * finiteHeckeEulerFactor χ v s := by
  obtain ⟨π, hπ⟩ := (valuation(v)).exists_isUniformizer_of_isCyclic_of_nontrivial
  let u := Units.mk0 (π : v.adicCompletion F) hπ.ne_zero
  have hK : IsCompact (O(v) : Set (v.adicCompletion F)) := isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v)
  have he := weilModifiedFiniteIntegral_eq_inv_euler_mul v u hπ _ hK (Valued.isOpen_valuationSubring _) χ s hs
  dsimp only at he
  rw [weilModifiedFiniteIntegral_integerRing v u hπ _ hu] at he
  rw [he]
  field_simp [finiteHeckeEulerFactor_ne_zero_of_one_lt χ v s hs]

/-- Paper: Equation (3.4.1.6), p. 143, in the form used on p. 231. The zeta integral
of a test extended from S is its S-idelic zeta integral times the outside Euler product.
Deviation: The Tamagawa masses of the integer units outside S are included. This is the
absolute-convergence form of the identity, with an arbitrary S-adelic test function. -/
theorem weilIdentity_unramifiedOutside (S : Finset V) (fS : ℬ(SAdeleRing F S))
    (χ : PontryaginDual C_F) (s : ℂ) (hs : 1 < s.re)
    (hc : ideleClassNormTwist χ s ∈ unramifiedOutside F S) :
    globalIdelicZetaIntegral (sAdeleSchwartzToGlobal F S fS) (ideleClassNormTwist χ s) =
      (∏ᶠ v : {v : V // v ∉ S},
          (((μv v.val) (v.val.adicCompletionIntegers F).units).toReal : ℂ)) *
        sLocalIdelicZetaIntegral fS (sIdeleRestriction F S ⟨ideleClassNormTwist χ s, hc⟩) *
        ∏' v : {v : V // v ∉ S}, finiteHeckeEulerFactor χ v.val s := by
  classical
  let c := ideleClassNormTwist χ s
  let I := {v : V // v ∉ S}
  let places (t : Finset I) := t.map (Function.Embedding.subtype _)
  have hdis (t : Finset I) : Disjoint S (places t) := by
    refine Finset.disjoint_left.mpr fun v hv ht ↦ ?_
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp ht
    exact j.property hv
  let U (t : Finset I) := outsideUnitIdeles (S ∪ places t)
  have hU : (⋃ t, U t) = univ := by
    apply eq_univ_of_forall
    intro g
    have he : ∀ᶠ v : V in cofinite, g.val.2 v ∈ O(v) ∧ g.inv.2 v ∈ O(v) :=
      g.val.2.property.and g.inv.2.property
    let T := (eventually_cofinite.mp he).toFinset
    let t := T.subtype (fun v ↦ v ∉ S)
    apply mem_iUnion.mpr
    refine ⟨t, fun v hv ↦ ?_⟩
    have hvS : v ∉ S := fun h ↦ hv (Finset.mem_union_left _ h)
    have hvT : v ∉ T := fun h ↦ hv (Finset.mem_union_right _
      (Finset.mem_map.mpr ⟨⟨v, hvS⟩, Finset.mem_subtype.mpr h, rfl⟩))
    have h : g.val.2 v ∈ O(v) ∧ g.inv.2 v ∈ O(v) := by simpa [T] using hvT
    exact h
  let H (g : I_F) := sAdeleSchwartzToGlobal F S fS (Multiplicative.ofAdd g.val) * c (classOf g)
  let μ := multiplicativeTamagawaMeasure F
  have hint : Integrable H μ := globalIdelicZetaIntegral_integrable (sAdeleSchwartzToGlobal F S fS) c
    (hs.trans_eq (ideleClassNormTwist_abscissa χ s).symm)
  have hmono : Monotone U := by
    intro t t' ht g hg v hv
    exact hg v (fun h ↦ hv ((Finset.union_subset_union_right (s := S) (Finset.map_subset_map.mpr ht)) h))
  have hlim := tendsto_setIntegral_of_monotone (μ := μ) (s := U) (f := H)
    (fun t ↦ measurableSet_outsideUnitIdeles _) hmono hint.integrableOn
  have hlim' : Tendsto (fun t ↦ ∫ g in U t, H g ∂μ) atTop (𝓝 (∫ g, H g ∂μ)) := by
    simpa only [hU, setIntegral_univ] using hlim
  let M (v : V) : ℂ := ((μv v) (O(v)).units).toReal
  let E (v : V) := finiteHeckeEulerFactor χ v s
  let Z := sLocalIdelicZetaIntegral fS (sIdeleRestriction F S ⟨c, hc⟩)
  have hm : ∀ᶠ v : V in cofinite, (μv v) (O(v)).units = 1 := by
    simpa only [finiteLocalMultiplicativeTamagawaMeasure_integerUnits, eventually_cofinite] using finiteLocalTamagawaMass_finite F
  let D := (eventually_cofinite.mp hm).toFinset
  have heq : (fun t : Finset I ↦ ∫ g in U t, H g ∂μ) =ᶠ[atTop] fun t ↦ Z * ∏ v ∈ t, M v.val * E v.val := by
    filter_upwards [eventually_ge_atTop (D.subtype (fun v ↦ v ∉ S))] with t ht
    have hM (v : V) (hv : v ∉ S ∪ places t) : (μv v) (O(v)).units = 1 := by
      have hvS : v ∉ S := fun h ↦ hv (Finset.mem_union_left _ h)
      have : v ∉ D := fun h ↦ hv (Finset.mem_union_right _
        (Finset.mem_map.mpr ⟨⟨v, hvS⟩, ht (Finset.mem_subtype.mpr h), rfl⟩))
      simpa [D] using this
    refine (setIntegral_outsideUnitIdeles S (places t) (hdis t) hM fS c hc).trans ?_
    apply congrArg (Z * ·)
    calc _ = ∏ v : places t, M v.val * E v.val := Finset.prod_congr rfl fun v _ ↦
                localIntegerRingIntegral_eq_mass_mul_euler v.val χ s hs
                  (hc v.val fun h ↦ Finset.disjoint_left.mp (hdis t) h v.property)
      _ = _ := by rw [← Finset.prod_subtype (places t) (fun _ ↦ Iff.rfl) (fun v ↦ M v * E v), Finset.prod_map]; rfl
  have hms : M.HasFiniteMulSupport := eventually_cofinite.mp (hm.mono fun v hv ↦ by simp [M, hv])
  have hmi := hms.preimage (f := fun j : I ↦ j.val) Subtype.val_injective.injOn
  have hmp : HasProd (fun v : I ↦ M v.val) (∏ᶠ v : I, M v.val) := by
    rw [← tprod_eq_finprod (L := SummationFilter.unconditional _) hmi]
    exact (multipliable_of_hasFiniteMulSupport hmi).hasProd
  have hep : Multipliable (fun v : I ↦ E v.val) := by
    let C := (S : Set V)ᶜ
    have hp := (finiteHeckeL_hasProd χ ⟨s, hs⟩).congr_cofinite₀ (s := S) (g := C.mulIndicator E)
      (fun v _ ↦ finiteHeckeEulerFactor_ne_zero_of_one_lt χ v s hs)
      (fun v hv ↦ (mulIndicator_of_mem hv E).symm)
    exact (hasProd_subtype_iff_mulIndicator.mpr hp).multipliable
  have h := tendsto_nhds_unique (hlim'.congr' heq) (tendsto_const_nhds.mul (hmp.mul hep.hasProd))
  change globalIdelicZetaIntegral (sAdeleSchwartzToGlobal F S fS) c = (∏ᶠ v : I, M v.val) * Z * ∏' v : I, E v.val
  exact h.trans (by ring)

end

private theorem tprod_finiteHeckeEulerFactor_outside (χ : PontryaginDual C_F) (S : Finset V)
    (z : ℂ) (hz : 1 < z.re) :
    ∏' v : {v : V // v ∉ S}, finiteHeckeEulerFactor χ v.val z =
      (∏ v ∈ S, (finiteHeckeEulerFactor χ v z)⁻¹) * finiteHeckeL χ ⟨z, hz⟩ := by
  classical
  let E (v : V) := finiteHeckeEulerFactor χ v z
  let C : Set V := {v | v ∉ S}
  have hprod := (finiteHeckeL_hasProd χ ⟨z, hz⟩).congr_cofinite₀ (s := S) (g := C.mulIndicator E)
    (fun v _ ↦ finiteHeckeEulerFactor_ne_zero_of_one_lt χ v z hz) (fun v hv ↦ (mulIndicator_of_mem hv E).symm)
  have ht : (∏' v : C, E v.val) = _ := (hasProd_subtype_iff_mulIndicator.mpr hprod).tprod_eq
  have hS : ∏ v ∈ S, C.mulIndicator E v = 1 :=
    Finset.prod_eq_one fun v hv ↦ mulIndicator_of_notMem (show v ∉ C from not_not_intro hv) _
  change (∏' v : C, E v.val) = (∏ v ∈ S, (E v)⁻¹) * _
  rw [ht, hS, one_div, Finset.prod_inv_distrib, mul_comm]

private theorem meromorphic_eq_of_eq_on_right (U : Set ℂ) (hU : IsPreconnected U) (h₂ : 2 ∈ U)
    {f g : ℂ → ℂ} (hf : MeromorphicOn f U) (hg : MeromorphicOn g U)
    (h : ∀ z : ℂ, 1 < z.re → f z = g z) : f =ᶠ[codiscreteWithin U] g := by
  have hnear : ∀ᶠ z in 𝓝 (2 : ℂ), 1 < z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  have he : meromorphicOrderAt (f - g) 2 = ⊤ := meromorphicOrderAt_eq_top_iff.mpr
    ((hnear.filter_mono nhdsWithin_le_nhds).mono fun z hz ↦ sub_eq_zero.mpr (h z hz))
  apply eventuallyEq_codiscreteWithin_iff_forall_eventually_nhdsNE.mpr
  intro z hz
  have hz' := (hf.sub hg).meromorphicOrderAt_eq_top_of_isPreconnected hU h₂ hz he
  exact (meromorphicOrderAt_eq_top_iff.mp hz').mono fun w hw _ ↦ sub_eq_zero.mp hw

/-- Paper: Equation (3.4.1.6), pp. 143–144, as applied on p. 231. For a test extended
from S, the global Z-function is the S-local Z-function times the continued outside
Euler product and the outside integer-unit masses.
Deviation: The continuation is expressed away from a discrete set of exponents. -/
theorem weilIdentity_unramifiedOutside_meromorphic (S : Finset V) (fS : ℬ(SAdeleRing F S))
    (χ : PontryaginDual C_F) (hc : ideleClassNormTwist χ 0 ∈ unramifiedOutside F S)
    (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (hLf : ∀ (s : ℂ) (hs : 1 < s.re), L s = finiteHeckeL χ ⟨s, hs⟩) :
    let cS := sIdeleRestriction F S ⟨ideleClassNormTwist χ 0, hc⟩
    let twistS := quasiCharacterNormTwist (G := SIdeleQuotient F S) (sIdeleQuotientNorm F S)
      (isProperMap_sIdeleQuotientNorm F S).continuous cS
    (fun s ↦ globalIdelicZFunction (sAdeleSchwartzToGlobal F S fS) (ideleClassNormTwist χ s))
      =ᶠ[codiscrete ℂ] (fun s ↦
        (∏ᶠ v : {v : V // v ∉ S}, (((μv v.val) (v.val.adicCompletionIntegers F).units).toReal : ℂ)) *
          sLocalIdelicZFunction fS (twistS s) * (∏ v ∈ S, (finiteHeckeEulerFactor χ v s)⁻¹) * L s) := by
  classical
  let cS := sIdeleRestriction F S ⟨ideleClassNormTwist χ 0, hc⟩
  let m := sIdeleQuotientNorm F S
  let hm := (isProperMap_sIdeleQuotientNorm F S).continuous
  let ψ := quasiCharacterPhase cS
  have hnorm (x : SIdeleQuotient F S) : ‖cS x‖ = 1 := by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    change ‖(χ (classOf (sIdeleInsertion F S g)) : ℂ) * _ ^ (0 : ℂ)‖ = 1
    simp
  have hbase : cS = (circleToComplex).comp ψ := by
    ext1 x
    change cS x = cS x / (‖cS x‖ : ℂ)
    rw [hnorm, Complex.ofReal_one, div_one]
  have hu (z : ℂ) : ideleClassNormTwist χ z ∈ unramifiedOutside F S := fun v hv ↦
    (ideleClassNormTwist_unramified_iff χ z v).mpr (hc v hv)
  have htwist (z : ℂ) : sIdeleRestriction F S ⟨ideleClassNormTwist χ z, hu z⟩ =
      quasiCharacterNormTwist m hm cS z := by
    ext1 x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    rw [sIdeleRestriction_mk]
    let y : C_F := classOf (sIdeleInsertion F S g)
    change (χ y : ℂ) * (normℝ y : ℂ) ^ z =
      ((χ y : ℂ) * (normℝ y : ℂ) ^ (0 : ℂ)) * (((m (QuotientGroup.mk g) : ℝ≥0) : ℝ) : ℂ) ^ z
    simp only [Complex.cpow_zero, mul_one, m, sIdeleQuotientNorm_mk, ← ideleNorm_sIdeleInsertion]
    rfl
  let A := ∏ᶠ v : {v : V // v ∉ S}, (((μv v.val) (v.val.adicCompletionIntegers F).units).toReal : ℂ)
  let Z (z : ℂ) := sLocalIdelicZFunction fS (quasiCharacterNormTwist m hm cS z)
  have hZ : MeromorphicOn Z univ := by
    dsimp only [Z]
    rw [hbase]
    exact (sLocalIdelicZFunction_meromorphic fS ψ).meromorphicOn
  have hE (v : V) : Differentiable ℂ (fun z ↦ (finiteHeckeEulerFactor χ v z)⁻¹) := by
    unfold finiteHeckeEulerFactor
    split_ifs
    · simp only [inv_inv]
      have hq : (v.asIdeal.absNorm : ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans
        (HeightOneSpectrum.one_lt_absNorm v)).ne'
      fun_prop (disch := simp [hq])
    · exact differentiable_const _
  change _ =ᶠ[codiscreteWithin (univ : Set ℂ)] (fun z ↦ A * Z z * _ * L z)
  apply meromorphic_eq_of_eq_on_right _ isPreconnected_univ (mem_univ _)
    (globalIdelicZFunction_meromorphic _ χ).meromorphicOn
  · intro z hz
    have he : AnalyticAt ℂ (fun t ↦ ∏ v ∈ S, (finiteHeckeEulerFactor χ v t)⁻¹) z :=
      S.analyticAt_fun_prod fun v _ ↦ (hE v).analyticAt _
    exact (((MeromorphicAt.const A z).mul (hZ z hz)).mul he.meromorphicAt).mul (hL hz).meromorphicAt
  · intro z hz
    have hpos := hz.trans_eq (ideleClassNormTwist_abscissa χ z).symm
    rw [globalIdelicZFunction_eq_integral _ hpos, weilIdentity_unramifiedOutside S fS χ z hz (hu z),
      tprod_finiteHeckeEulerFactor_outside χ S z hz, hLf z hz]
    have he : Z z = sLocalIdelicZetaIntegral fS (sIdeleRestriction F S ⟨_, hu z⟩) := by
      rw [htwist]
      exact sLocalIdelicZFunction_eq_integral fS ⟨ψ, z, zero_lt_one.trans hz, by rw [hbase]⟩
    rw [he, mul_assoc (A * _)]

/-- Paper: Equation (3.4.1.6), p. 143. For a pure tensor the zeta integral is the
modified zeta product times the finite Hecke L-function on the absolute-convergence half-plane.
Deviation: The modified product already contains the outside Tamagawa masses. The
finite Hecke L-function has Euler factor one at every ramified place, as in §3.2. -/
theorem weilIdentity_modifiedZeta (f : ℬ(𝔸[F])) (fArch : ℬ(AArch))
    (K : (v : V) → Set (v.adicCompletion F))
    (uniformizer : (v : V) → (v.adicCompletion F)ˣ)
    (hπ : ∀ v : V, (valuation(v)).IsUniformizer (uniformizer v).val)
    (hKc : ∀ v : V, IsCompact (K v)) (hKo : ∀ v : V, IsOpen (K v))
    (hK : ∀ᶠ v in cofinite, K v = v.adicCompletionIntegers F)
    (hf : ∀ x : 𝔸[F], f (Multiplicative.ofAdd x) =
      fArch (Multiplicative.ofAdd (adeleProjection F ∅ x)) *
        ∏ᶠ v : V, (K v).indicator (fun _ ↦ (1 : ℂ)) (x.2 v))
    (χ : PontryaginDual C_F) (s : ℂ) (hs : 1 < s.re) :
    globalIdelicZetaIntegral f (ideleClassNormTwist χ s) =
      weilModifiedZeta fArch K uniformizer (ideleClassNormTwist χ s) *
        finiteHeckeL χ ⟨s, hs⟩ := by
  classical
  let c := ideleClassNormTwist χ s
  let k (v : V) := (K v).indicator (fun _ ↦ (1 : ℂ))
  let E (v : V) := weilModifiedFiniteIntegral v (uniformizer v) (k v) c
  let Z (v : V) := localIdelicZetaIntegral (μv v) (k v) (finitePlaceRestriction F v c)
  obtain ⟨T, fT, hT⟩ := sAdeleSchwartzToGlobal_exhaustive F f
  obtain ⟨R, hR⟩ : ∃ R : Finset V, c ∈ unramifiedOutside F R :=
    mem_iUnion.mp ((iUnion_unramifiedOutside F).symm ▸ mem_univ c)
  have hm : ∀ᶠ v : V in cofinite, (μv v) (v.adicCompletionIntegers F).units = 1 := by
    simpa only [finiteLocalMultiplicativeTamagawaMeasure_integerUnits, eventually_cofinite]
      using finiteLocalTamagawaMass_finite F
  let B := (eventually_cofinite.mp (hK.and hm)).toFinset
  let S := T ∪ (R ∪ B)
  have hTS : T ⊆ S := Finset.subset_union_left
  have hc : c ∈ unramifiedOutside F S := fun v hv ↦ hR v (fun h ↦ hv
    (Finset.mem_union_right _ (Finset.mem_union_left _ h)))
  have htail (v : V) (hv : v ∉ S) : K v = v.adicCompletionIntegers F ∧
      (μv v) (v.adicCompletionIntegers F).units = 1 := by
    have hb : v ∉ B := fun h ↦ hv (Finset.mem_union_right _ (Finset.mem_union_right _ h))
    simpa [B] using hb
  let fS := sAdeleSchwartzTransition F hTS fT
  have hglob : sAdeleSchwartzToGlobal F S fS = f :=
    (LinearMap.congr_fun (sAdeleSchwartzToGlobal_comp F hTS) fT).trans hT
  have hfS (x : SAdeleRing F S) : fS (Multiplicative.ofAdd x) =
      fArch (Multiplicative.ofAdd (x.1, 0)) * ∏ v : S, k v.val (x.2 v) := by
    let y (v : V) : v.adicCompletion F := if h : v ∈ S then x.2 ⟨v, h⟩ else 0
    have hy (v : V) (hv : v ∉ S) : y v ∈ v.adicCompletionIntegers F := by simp [y, hv]
    let a : 𝔸[F] := (x.1, ⟨y, S.eventually_cofinite_notMem.mono (fun v hv ↦ hy v hv)⟩)
    have hp : adeleProjection F S a = x := Prod.ext rfl (funext fun v ↦ dite_eq_left v.property)
    have hp₀ : adeleProjection F ∅ a = (x.1, 0) := Prod.ext rfl (Subsingleton.elim _ _)
    have ht := sAdeleSchwartzToGlobal_apply F S fS a
    have ha (v : V) (hv : v ∉ S) : a.2 v ∈ v.adicCompletionIntegers F := hy v hv
    rw [hglob, ite_eq_left ha, hp, hf, hp₀] at ht
    rw [← ht]
    apply congrArg (_ * ·)
    change (∏ᶠ v, k v (y v)) = _
    rw [finprod_eq_prod_of_mulSupport_subset (s := S) _ (mulSupport_subset_iff'.mpr fun v hv ↦ ?_),
      Finset.prod_subtype S (fun _ ↦ Iff.rfl)]
    · exact Finset.prod_congr rfl fun v _ ↦ congrArg (k v.val) (dite_eq_left v.property)
    · simp only [k, (htail v hv).1, indicator_of_mem (hy v hv)]
  have hlocal := sLocalIntegral_arch_mul_prod S fS fArch (fun v ↦ k v.val) hfS c hc
  change sLocalIdelicZetaIntegral fS (sIdeleRestriction F S ⟨c, hc⟩) =
    weilArchimedeanIntegral fArch c * ∏ v : S, Z v.val at hlocal
  rw [← Finset.prod_subtype S (fun _ ↦ Iff.rfl)] at hlocal
  have hmass : (∏ᶠ v : {v : V // v ∉ S},
      (((μv v.val) (v.val.adicCompletionIntegers F).units).toReal : ℂ)) = 1 := by
    apply finprod_eq_one_of_forall_eq_one
    intro v
    simp [(htail v.val v.property).2]
  have hmod : weilModifiedZeta fArch K uniformizer c = weilArchimedeanIntegral fArch c * ∏ v ∈ S, E v := by
    apply congrArg (_ * ·)
    apply tprod_eq_prod
    intro v hv
    simp only [(htail v hv).1, weilModifiedFiniteIntegral_integerRing v _ (hπ v) c (hc v hv),
      (htail v hv).2, ENNReal.toReal_one, Complex.ofReal_one]
  have he (v : V) : E v = (finiteHeckeEulerFactor χ v s)⁻¹ * Z v :=
    weilModifiedFiniteIntegral_eq_inv_euler_mul v _ (hπ v) (K v) (hKc v) (hKo v) χ s hs
  change globalIdelicZetaIntegral f c = weilModifiedZeta fArch K uniformizer c * _
  calc globalIdelicZetaIntegral f c = globalIdelicZetaIntegral (sAdeleSchwartzToGlobal F S fS) c :=
        congrArg (globalIdelicZetaIntegral · c) hglob.symm
    _ = _ := ?_
  rw [weilIdentity_unramifiedOutside S fS χ s hs hc, hmass, one_mul, hlocal, hmod,
    tprod_finiteHeckeEulerFactor_outside χ S s hs]
  simp_rw [he]
  rw [Finset.prod_mul_distrib]
  ring

/-- Paper: Equation (3.4.1.6), pp. 143–144. The pure-tensor identity extends to the
positive half-plane for the continued zeta function and finite Hecke L-function.
Deviation: The same normalization as in `weilIdentity_modifiedZeta` is used. The
continuation is meromorphic, with equality expressed off a discrete set. -/
theorem weilIdentity_modifiedZeta_meromorphic (f : ℬ(𝔸[F])) (fArch : ℬ(AArch))
    (K : (v : V) → Set (v.adicCompletion F))
    (uniformizer : (v : V) → (v.adicCompletion F)ˣ)
    (hπ : ∀ v : V, (valuation(v)).IsUniformizer (uniformizer v).val)
    (hKc : ∀ v : V, IsCompact (K v)) (hKo : ∀ v : V, IsOpen (K v))
    (hK : ∀ᶠ v in cofinite, K v = v.adicCompletionIntegers F)
    (hf : ∀ x : 𝔸[F], f (Multiplicative.ofAdd x) =
      fArch (Multiplicative.ofAdd (adeleProjection F ∅ x)) *
        ∏ᶠ v : V, (K v).indicator (fun _ ↦ (1 : ℂ)) (x.2 v))
    (χ : PontryaginDual C_F) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (hLf : ∀ (s : ℂ) (hs : 1 < s.re), L s = finiteHeckeL χ ⟨s, hs⟩) :
    (fun s ↦ globalIdelicZFunction f (ideleClassNormTwist χ s)) =ᶠ[
        codiscreteWithin (Complex.re ⁻¹' Ioi 0)]
      (fun s ↦ weilModifiedZeta fArch K uniformizer (ideleClassNormTwist χ s) * L s) := by
  let U := Complex.re ⁻¹' Ioi (0 : ℝ)
  apply meromorphic_eq_of_eq_on_right U (convex_halfSpace_re_gt 0).isPreconnected
    (by change 0 < (2 : ℂ).re; norm_num)
  · exact fun z _ ↦ (globalIdelicZFunction_meromorphic f χ (mem_univ z)).meromorphicAt
  · exact fun z hz ↦ (weilModifiedZeta_analyticOn fArch K uniformizer hπ hKc hKo hK χ z hz).meromorphicAt.mul
      (hL (mem_univ z)).meromorphicAt
  · intro z hz
    have hc := hz.trans_eq (ideleClassNormTwist_abscissa χ z).symm
    rw [globalIdelicZFunction_eq_integral f hc, hLf z hz]
    exact weilIdentity_modifiedZeta f fArch K uniformizer hπ hKc hKo hK hf χ z hz

end UnramifiedIdentity

section Applications

-- TODO(paper-gap): Proposition 3.4.2.1 asserts Lebesgue integrability on the
-- relative one-line. The standard test function over ℚ gives absolute divergence.

open Classical in
/-- Paper: Equation (3.4.2.6), p. 146. For the trivial norm-one character
the cutoff is the indicator of norm at most one. For other characters it vanishes. -/
def thetaPolarCutoff (ω : PontryaginDual C₁) (g : C_F) : ℂ :=
  if ω = 1 ∧ normℝ g ≤ 1 then 1 else 0

/-- Paper: Equation (3.4.2.6), p. 146. The trivial-character cutoff equals
one at the identity class. -/
theorem thetaPolarCutoff_one : thetaPolarCutoff (1 : PontryaginDual C₁) 1 = 1 := by
  simp [thetaPolarCutoff]

/-- Paper: Theorem 3.4.2.2(1), p. 146. At large norm homogeneous theta
decays to every inverse power, uniformly over a bounded set of test functions.
This restates the large-norm bound in `homogeneousAdelicTheta_decay_bounded`. -/
theorem weilTheta_decay_large (ω : PontryaginDual C₁)
    (B : Set ℬ(𝔸[F])) (hB : IsVonNBounded ℂ B) (N : ℕ) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ f ∈ B, ∀ g : C_F, T < normℝ g →
      ‖homogeneousAdelicTheta ω f g‖ ≤ C * ((normℝ g) ^ N)⁻¹ := by
  obtain ⟨C, T, hC, -, h⟩ := homogeneousAdelicTheta_decay_bounded ω B hB N
  refine ⟨C, Real.exp T, hC, Real.exp_pos T, fun f hf g hg ↦ (h f hf g).1 ?_⟩
  have hpos : (0 : ℝ) < normℝ g := (Real.exp_pos T).trans hg
  exact (Real.lt_log_iff_exp_lt hpos).2 hg

-- TODO(paper-gap): Equation (3.4.2.4) drops the norm-one class volume
-- included in Theorem 2.2.5.4 and in Equations (3.4.2.9)–(3.4.2.10).

/-- Paper: Theorem 3.4.2.2(2), p. 146. At small norm homogeneous theta
minus the cutoff polar term decays to every power, uniformly over bounded sets.
Deviation: The polar coefficient includes the norm-one Tamagawa volume as in
Equation (3.4.2.10) and `homogeneousAdelicTheta_decay_bounded`. -/
theorem weilTheta_decay_small (ω : PontryaginDual C₁)
    (B : Set ℬ(𝔸[F])) (hB : IsVonNBounded ℂ B) (N : ℕ) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ f ∈ B, ∀ g : C_F, normℝ g < T →
      let zeroAdele := Multiplicative.ofAdd (0 : 𝔸[F])
      let polar := (normℝ g)⁻¹ • adeleSchwartzFourier f zeroAdele - f zeroAdele
      ‖homogeneousAdelicTheta ω f g -
        (normOneIdeleClassTamagawaMeasure F univ).toReal • (thetaPolarCutoff ω g * polar)‖ ≤
        C * (normℝ g) ^ N := by
  obtain ⟨C, T, hC, hT, h⟩ := homogeneousAdelicTheta_decay_bounded ω B hB N
  refine ⟨C, Real.exp (-T), hC, Real.exp_pos _, fun f hf g hg ↦ ?_⟩
  have hp : 0 < normℝ g := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hlog : Real.log (normℝ g) < -T := (Real.log_lt_iff_lt_exp hp).2 hg
  have hg₁ : normℝ g ≤ 1 := hg.le.trans (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hT.le))
  have hsmall := (h f hf g).2.1 (by linarith)
  by_cases hω : ω = 1 <;>
    simpa [thetaPolarCutoff, homogeneousAdelicTheta_polarTerm, hω, hg₁] using hsmall

/-- Paper: Theorem 3.4.2.2(2), p. 146. For norm at most one, the volume-scaled
cutoff polar term equals the polar term of Theorem 2.2.5.4. -/
theorem thetaPolarCutoff_polarTerm (ω : PontryaginDual C₁) (f : ℬ(𝔸[F])) (g : C_F)
    (hg : normℝ g ≤ 1) :
    (normOneIdeleClassTamagawaMeasure F univ).toReal •
        (thetaPolarCutoff ω g *
          ((normℝ g)⁻¹ • adeleSchwartzFourier f (Multiplicative.ofAdd (0 : 𝔸[F])) -
            f (Multiplicative.ofAdd (0 : 𝔸[F])))) =
      homogeneousAdelicTheta_polarTerm ω f g := by
  unfold thetaPolarCutoff homogeneousAdelicTheta_polarTerm
  by_cases hω : ω = 1
  · rw [ite_eq_left ⟨hω, hg⟩, ite_eq_left hω, one_mul]
  · rw [ite_eq_right fun h ↦ hω h.1, ite_eq_right hω, zero_mul, smul_zero]

-- TODO(paper-gap): Equation (3.4.2.7) counts each modified finite factor
-- twice. The line below it also divides by the local Euler denominator,
-- while the definition (3.4.1.3) multiplies by that denominator.
-- TODO(paper-gap): Remarks 3.4.2.3–3.4.2.4 assert attainment of maxima on
-- arbitrary bounded sets. The compact closure gives a bound. The small-norm
-- estimate (3.4.2.17) also omits the polar subtraction for the full theta sum.

end Applications

section Eigendistributions

variable {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

local notation "isEigen(" c "," T ")" =>
  (∀ g : Rˣ, ∀ f : ℬ(R), (T) (schwartzBruhatUnitTranslate g f) = (c) g * (T) f)

/-- Paper: Definition 3.4.3.1, p. 151. The weight condition is preserved
by zero, addition and complex scalar multiplication. -/
theorem schwartzBruhatEigen_submodule (c : QuasiCharacter Rˣ) :
    isEigen(c, (0 : StrongDual ℂ ℬ(R))) ∧
      (∀ T U : StrongDual ℂ ℬ(R), isEigen(c, T) → isEigen(c, U) → isEigen(c, T + U)) ∧
      (∀ (a : ℂ) (T : StrongDual ℂ ℬ(R)), isEigen(c, T) → isEigen(c, a • T)) := by
  refine ⟨fun g f ↦ by simp, fun T U hT hU g f ↦ ?_, fun a T hT g f ↦ ?_⟩
  · simp only [ContinuousLinearMap.add_apply, hT g f, hU g f, mul_add]
  · simp only [ContinuousLinearMap.smul_apply, hT g f, smul_eq_mul]
    ring

-- TODO(paper-gap): The right-translation gloss in Definition 3.4.3.1 reverses
-- the action of (2.1.2.2) and the weight condition recalled in Definition 5.5.1.1.

/-- Paper: Definition 3.4.3.1(1)–(2), p. 151. The eigendistributions are the
continuous functionals that take translation by a unit to multiplication by its weight.
Deviation: The action on test functions is `ρ(g, f)(x) = f(g⁻¹x)`, as in
Equation (2.1.2.2) and Definition 5.5.1.1. -/
def schwartzBruhatEigendistributions (c : QuasiCharacter Rˣ) : Submodule ℂ (StrongDual ℂ ℬ(R)) where
  carrier := {T | isEigen(c, T)}
  zero_mem' := (schwartzBruhatEigen_submodule c).1
  add_mem' := (schwartzBruhatEigen_submodule c).2.1 _ _
  smul_mem' a := (schwartzBruhatEigen_submodule c).2.2 a _

/-- Point evaluation on the Schwartz–Bruhat space is continuous because its
absolute value pulls back to a continuous seminorm on every elementary stage.
Copied from the private `continuous_schwartzBruhat_eval` in
`AppD_SchwartzBruhat/Sec2b.lean`, used here for the point evaluation. -/
private theorem continuous_schwartzBruhat_eval' {G : Type*} [CommGroup G] [TopologicalSpace G]
    (x : G) : Continuous (fun f : SchwartzBruhat G ↦ f x) := by
  classical
  let L : SchwartzBruhat G →ₗ[ℂ] ℂ := (LinearMap.proj x).comp (schwartzBruhatSubmodule G).subtype
  let p := (normSeminorm ℂ ℂ).comp L
  have hp : ∀ (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient),
      Continuous (p ∘ schwartzBruhatStageInclusion a e) := by
    intro a e
    let q := (normSeminorm ℂ ℂ).comp (L.comp (schwartzBruhatStageInclusion a e))
    change Continuous q
    let p₀ : Seminorm ℂ (SchwartzBruhatStage e) := elementarySchwartzSeminorm (0, 0, 0, 0)
    have hp₀ : Continuous p₀ :=
      (withGeneratingSeminorms_spec _ _).continuous_seminorm (0, 0, 0, 0)
    apply Seminorm.continuous_of_le hp₀
    intro f
    change ‖schwartzBruhatStageRealization a e f x‖ ≤ p₀ f
    let := e.finiteGroup
    have he := schwartzBruhatStageRealization_apply a e f x
    by_cases hx : x ∈ a.val.1
    · rw [dite_eq_left hx] at he
      rw [he]
      let y := Multiplicative.toAdd (e.equiv (QuotientGroup.mk ⟨x, hx⟩))
      change (‖f y‖₊ : ENNReal).toReal ≤ (elementarySchwartzBound f.val (0, 0, 0, 0)).toReal
      have hb : (‖f y‖₊ : ENNReal) ≤ elementarySchwartzBound f.val (0, 0, 0, 0) :=
        (le_iSup (fun g ↦ (‖f.val g‖₊ : ENNReal)) y).trans_eq
          (elementarySchwartzBound_zero f.val).symm
      exact ENNReal.toReal_mono (f.property.2 (0, 0, 0, 0)).ne hb
    · rw [dite_eq_right hx] at he
      exact ((congrArg norm he).trans (norm_zero (E := ℂ))).le.trans (apply_nonneg p₀ f)
  let i : {q : Seminorm ℂ (schwartzBruhatSubmodule G) //
      ∀ (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient),
        Continuous (q ∘ schwartzBruhatStageInclusion a e)} := ⟨p, hp⟩
  exact (norm_withSeminorms ℂ ℂ).continuous_of_continuous_comp L fun _ ↦
    (withGeneratingSeminorms_spec _ Subtype.val).continuous_seminorm i

/-- Paper: Definition 3.4.3.1(1)–(2), p. 151. Evaluation at zero belongs
to the weight-one subspace, since unit multiplication fixes zero. -/
theorem schwartzBruhatEigendistributions_zeroEval :
    ∃ T : StrongDual ℂ ℬ(R), T ∈ schwartzBruhatEigendistributions (1 : QuasiCharacter Rˣ) ∧
      ∀ f : ℬ(R), T f = f (Multiplicative.ofAdd 0) := by
  let L : ℬ(R) →ₗ[ℂ] ℂ :=
    (LinearMap.proj (Multiplicative.ofAdd 0)).comp (schwartzBruhatSubmodule _).subtype
  refine ⟨⟨L, continuous_schwartzBruhat_eval' _⟩, fun g f ↦ ?_, fun f ↦ rfl⟩
  change schwartzBruhatUnitTranslate g f (Multiplicative.ofAdd 0) = _ * f (Multiplicative.ofAdd 0)
  rw [schwartzBruhatUnitTranslate_apply, mul_zero]
  exact (one_mul _).symm

/-- Paper: Definition 3.4.3.1(1)–(2), p. 151. The weight subspace is
closed in the strong topology of the continuous dual. -/
theorem schwartzBruhatEigendistributions_isClosed (c : QuasiCharacter Rˣ) :
    IsClosed (schwartzBruhatEigendistributions c : Set (StrongDual ℂ ℬ(R))) := by
  have h : (schwartzBruhatEigendistributions c : Set (StrongDual ℂ ℬ(R))) =
      ⋂ (g : Rˣ) (f : ℬ(R)), {T | T (schwartzBruhatUnitTranslate g f) = c g * T f} := by
    ext T
    simp only [Set.mem_iInter]
    rfl
  -- Rewriting with `h` takes minutes, so transport closedness along it instead.
  exact (congrArg (fun s : Set (StrongDual ℂ ℬ(R)) ↦ IsClosed s) h).mpr
    (isClosed_iInter fun g ↦ isClosed_iInter fun f ↦
      isClosed_eq (continuous_eval_const _) ((continuous_eval_const f).const_mul _))

end Eigendistributions

/-- Paper: Definition 3.4.3.1(2), p. 151. The global weight subspace uses the
pullback of the quasi-character from the idele classes to the ideles. -/
def adelicEigendistributions (c : X) : Submodule ℂ (StrongDual ℂ ℬ(𝔸[F])) :=
  schwartzBruhatEigendistributions
    (c.comp ⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩ : QuasiCharacter I_F)

/-- Paper: Definition 3.4.3.1(2), p. 151. At global weight one,
evaluation at the zero adele is an eigendistribution. -/
theorem adelicEigendistributions_zeroEval :
    ∃ T : StrongDual ℂ ℬ(𝔸[F]), T ∈ adelicEigendistributions (1 : X) ∧
      ∀ f : ℬ(𝔸[F]), T f = f (Multiplicative.ofAdd 0) := by
  have h1 : ((1 : X).comp ⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩ :
      QuasiCharacter I_F) = 1 := ContinuousMonoidHom.ext fun _ ↦ rfl
  have h2 : adelicEigendistributions (1 : X) =
      schwartzBruhatEigendistributions (1 : QuasiCharacter 𝔸[F]ˣ) :=
    congrArg schwartzBruhatEigendistributions h1
  -- Destructuring the existential with `obtain` unfolds the membership and takes minutes.
  exact (show ∃ T : StrongDual ℂ ℬ(𝔸[F]),
      T ∈ schwartzBruhatEigendistributions (1 : QuasiCharacter 𝔸[F]ˣ) ∧
        ∀ f : ℬ(𝔸[F]), T f = f (Multiplicative.ofAdd 0) from
    schwartzBruhatEigendistributions_zeroEval).imp
    fun T hT ↦ ⟨(congrArg (T ∈ ·) h2).mpr hT.1, hT.2⟩

section Gaussians

local notation "realCoord(" h ")" => InfinitePlace.Completion.ringEquivRealOfIsReal h
local notation "complexCoord(" h ")" => InfinitePlace.Completion.ringEquivComplexOfIsComplex h

-- TODO(paper-gap): The complex monomials in (3.4.3.5)–(3.4.3.6) have the same
-- angular weight as the character, so their local zeta integrals vanish at nonzero weight.

open Classical in
/-- Paper: Definition 3.4.3.2(1)–(2), p. 152. The local real Gaussian is
even or odd according to the character on signs. The complex Gaussian
has angular exponent opposite to the character.
Deviation: The monomials in (3.4.3.5)–(3.4.3.6) are conjugated so that the
angular factors cancel in the local zeta integral. -/
def infiniteStandardGaussianValue (w : InfinitePlace F)
    (χ : PontryaginDual w.Completionˣ) (x : w.Completion) : ℂ :=
  if h : w.IsReal then
    let y := realCoord(h) x
    let parity := if χ (-1) = 1 then (1 : ℝ) else y
    (parity * Real.exp (-Real.pi * y ^ 2) : ℝ)
  else
    let e := complexCoord(InfinitePlace.not_isReal_iff_isComplex.mp h)
    let c : ℂˣ →ₜ* ℂ :=
      (circleToComplex).comp (χ.comp ⟨Units.map e.symm.toMonoidHom,
        (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
          (InfinitePlace.not_isReal_iff_isComplex.mp h)).symm.continuous.units_map _⟩)
    let m := (existsUnique_complexUnits_character_parameters c
      (fun _ ↦ Circle.norm_coe _)).exists.choose.2
    let z := e x
    let monomial := if 0 ≤ m then (star z) ^ m.natAbs else z ^ m.natAbs
    monomial * Complex.exp (-2 * (Real.pi : ℂ) * z * star z) / (2 * (Real.pi : ℂ))

section
private theorem schwartzBruhat_mem_of_schwartz_coordinates {A E : Type*} [AddCommGroup A]
    [TopologicalSpace A] [IsTopologicalAddGroup A] [T2Space A] [LocallyCompactSpace A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (e : A ≃+ E) (he : Continuous e) (he' : Continuous e.symm) (s : SchwartzMap E ℂ) :
    (fun x : Multiplicative A ↦ s (e x.toAdd)) ∈ schwartzBruhatSubmodule (Multiplicative A) := by
  let L : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  let v : Multiplicative A ≃ₜ* Multiplicative _ :=
    { toMulEquiv := (e.trans L.toLinearEquiv.toAddEquiv).toMultiplicative
      continuous_toFun := L.continuous.comp he
      continuous_invFun := he'.comp L.symm.continuous }
  let : T2Space (Multiplicative A) := v.toHomeomorph.isEmbedding.t2Space
  let : LocallyCompactSpace (Multiplicative A) := ‹LocallyCompactSpace A›
  apply (mem_schwartzBruhatSubmodule_euclidean_iff v _).mpr
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm s, fun x ↦ ?_⟩
  change s (L.symm (L _)) = _
  rw [L.symm_apply_apply]
  rfl
end

/-- Paper: Definition 3.4.3.2(1)–(2), p. 152. The real and complex
Gaussian formulas give Schwartz–Bruhat test functions on the completion. -/
theorem infiniteStandardGaussian_mem (w : InfinitePlace F) (χ : PontryaginDual w.Completionˣ) :
    (fun x : Multiplicative w.Completion ↦ infiniteStandardGaussianValue w χ x.toAdd) ∈
      schwartzBruhatSubmodule (Multiplicative w.Completion) := by
  classical
  by_cases h : w.IsReal
  · let e := realCoord(h)
    let p (t : ℝ) := if χ (-1) = 1 then (1 : ℝ) else t
    have hp : p.HasTemperateGrowth := by
      by_cases hχ : χ (-1) = 1 <;> simp only [p, hχ, ↓reduceIte] <;> fun_prop
    let g := (SchwartzMap.smulLeftCLM ℝ p (SchwartzMap.gaussian Real.pi Real.pi_pos)).postcompCLM
      Complex.ofRealCLM
    have hg := schwartzBruhat_mem_of_schwartz_coordinates e.toAddEquiv
      (InfinitePlace.Completion.isometryEquivRealOfIsReal h).continuous
      (InfinitePlace.Completion.isometryEquivRealOfIsReal h).symm.continuous g
    convert hg using 1
    ext x
    simp only [g, SchwartzMap.postcompCLM_apply, Complex.ofRealCLM_apply, SchwartzMap.smulLeftCLM_apply_apply hp,
      SchwartzMap.gaussian_apply, smul_eq_mul, Real.norm_eq_abs, sq_abs, infiniteStandardGaussianValue, h, dite_true]
    rfl
  · let hw := InfinitePlace.not_isReal_iff_isComplex.mp h
    let e := complexCoord(hw)
    let c : ℂˣ →ₜ* ℂ := (circleToComplex).comp (χ.comp ⟨Units.map e.symm.toMonoidHom,
      (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).symm.continuous.units_map _⟩)
    let m := (existsUnique_complexUnits_character_parameters c (fun _ ↦ Circle.norm_coe _)).exists.choose.2
    let p (z : ℂ) := if 0 ≤ m then (star z) ^ m.natAbs else z ^ m.natAbs
    have hp : p.HasTemperateGrowth := by
      by_cases hm : 0 ≤ m
      · simp only [p, hm, ite_true]
        change (fun z : ℂ ↦ Complex.conjCLE.toContinuousLinearMap z ^ m.natAbs).HasTemperateGrowth
        fun_prop
      · simp only [p, hm, ite_false]
        fun_prop
    let a := 2 * Real.pi
    let b : SchwartzMap ℂ ℂ := (SchwartzMap.gaussian a (by positivity : 0 < 2 * Real.pi)).postcompCLM Complex.ofRealCLM
    let g := ((2 * (Real.pi : ℂ))⁻¹) • (SchwartzMap.smulLeftCLM ℂ p b)
    have hg := schwartzBruhat_mem_of_schwartz_coordinates e.toAddEquiv
      (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).continuous
      (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).symm.continuous g
    convert hg using 1
    ext x
    simp only [infiniteStandardGaussianValue, h, dite_false]
    change p (e x.toAdd) * Complex.exp (-2 * (Real.pi : ℂ) * e x.toAdd * star (e x.toAdd)) / _ = _
    let z := e x.toAdd
    change p z * Complex.exp (-2 * (Real.pi : ℂ) * z * star z) / _ = g z
    have he : -2 * (Real.pi : ℂ) * z * star z = ((-a * ‖z‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_assoc, show z * star z = (‖z‖ : ℂ) ^ 2 from Complex.mul_conj' z]
      dsimp only [a]
      push_cast
      ring
    simp only [g, b, smul_apply, smul_eq_mul, SchwartzMap.smulLeftCLM_apply_apply hp,
      SchwartzMap.postcompCLM_apply, Complex.ofRealCLM_apply, SchwartzMap.gaussian_apply, he, Complex.ofReal_exp]
    ring

/-- Paper: Definition 3.4.3.2(1)–(2), p. 152. The standard infinite-place
test function is the Gaussian of the sign or angular weight.
Deviation: The complex Gaussian uses the conjugated monomials of `infiniteStandardGaussianValue`. -/
def infiniteStandardGaussian (w : InfinitePlace F) (χ : PontryaginDual w.Completionˣ) :
    ℬ(w.Completion) :=
  ⟨fun x ↦ infiniteStandardGaussianValue w χ x.toAdd, infiniteStandardGaussian_mem w χ⟩

/-- The angular exponent of the trivial unitary character of the complex units is zero. -/
theorem complexUnits_character_parameter_snd_trivial (c : ℂˣ →ₜ* ℂ) (hc : ∀ x, ‖c x‖ = 1)
    (h1 : ∀ x, c x = 1) :
    (existsUnique_complexUnits_character_parameters c hc).exists.choose.2 = 0 := by
  have h := (existsUnique_complexUnits_character_parameters c hc).unique
    (existsUnique_complexUnits_character_parameters c hc).exists.choose_spec
    (show ((0 : ℂ), (0 : ℤ)).1.re = 0 ∧ _ from ⟨by simp, fun x ↦ by simp [h1]⟩)
  exact congrArg Prod.snd h

open Classical in
/-- Paper: Equations (3.4.3.3) and (3.4.3.5), p. 152. At zero and weight
one, the real Gaussian equals one and the complex Gaussian equals one over two pi. -/
theorem infiniteStandardGaussian_trivial_zero (w : InfinitePlace F) :
    infiniteStandardGaussian w 1 (Multiplicative.ofAdd 0) =
      if w.IsReal then 1 else (2 * (Real.pi : ℂ))⁻¹ := by
  by_cases h : w.IsReal
  · simp [infiniteStandardGaussian, infiniteStandardGaussianValue, h]
  · simp only [infiniteStandardGaussian, infiniteStandardGaussianValue, h, dite_false,
      ite_false]
    rw [complexUnits_character_parameter_snd_trivial]
    · simp
    · intro x
      refine (congrArg norm (?_ : _ = (1 : ℂ))).trans (norm_one (α := ℂ))
      rfl
    · intro x
      rfl

local notation "integerUnits(" v ")" => ((HeightOneSpectrum.adicCompletionIntegers F v).units)
local notation "unramified(" v "," c ")" => (∀ u ∈ integerUnits(v), c u = (1 : ℂ))

open Classical in
/-- Paper: Definition 3.4.3.2(3), p. 152. The finite Gaussian is the
integer-ring indicator for unramified weights. For ramified weights it
is the inverse quasi-character on the integer units, extended by zero. -/
def finiteStandardGaussianValue (v : V) (c : QuasiCharacter (v.adicCompletion F)ˣ)
    (x : v.adicCompletion F) : ℂ :=
  if unramified(v, c) then
    (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ ↦ 1) x
  else
    (Units.val '' integerUnits(v)).indicator
      (fun y ↦ if hy : y ≠ 0 then (c (Units.mk0 y hy))⁻¹ else 0) x

/-- A complex number all of whose powers lie within `r < 1` of one is one. Otherwise the real
parts of the geometric sums `∑ n < N, z ^ n` would grow linearly in `N`, while the sums
themselves, equal to `(z ^ N - 1) / (z - 1)`, stay bounded. -/
private theorem eq_one_of_forall_norm_pow_sub_one_le {z : ℂ} {r : ℝ} (hr : r < 1)
    (h : ∀ n : ℕ, ‖z ^ n - 1‖ ≤ r) : z = 1 := by
  by_contra hz
  have hz1 : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  have hpos : 0 < (1 - r) * ‖z - 1‖ := mul_pos (sub_pos.mpr hr) hz1
  obtain ⟨N, hN⟩ := exists_nat_gt (r / ((1 - r) * ‖z - 1‖))
  rw [div_lt_iff₀ hpos] at hN
  have hre : (N : ℝ) * (1 - r) ≤ (∑ n ∈ Finset.range N, z ^ n).re := by
    rw [Complex.re_sum]
    have hle : ∀ n ∈ Finset.range N, 1 - r ≤ (z ^ n).re := fun n _ ↦ by
      have h1 := (abs_le.mp ((Complex.abs_re_le_norm (z ^ n - 1)).trans (h n))).1
      rw [Complex.sub_re, Complex.one_re] at h1
      linarith
    simpa using Finset.card_nsmul_le_sum _ _ _ hle
  have hbound : (∑ n ∈ Finset.range N, z ^ n).re * ‖z - 1‖ ≤ r :=
    calc _ ≤ ‖∑ n ∈ Finset.range N, z ^ n‖ * ‖z - 1‖ :=
          mul_le_mul_of_nonneg_right (Complex.re_le_norm _) hz1.le
      _ = ‖z ^ N - 1‖ := by rw [← norm_mul, geom_sum_mul]
      _ ≤ r := h N
  nlinarith [mul_le_mul_of_nonneg_right hre hz1.le]

/-- A continuous character of the units of a nonarchimedean normed field is trivial near one.
If `‖t - 1‖ < δ ≤ 1`, every power of `t` also lies within `δ` of one, so all powers of the
character value stay near one in `ℂ`, which forces the value to be one. -/
private theorem exists_forall_norm_sub_one_lt_map_eq_one {K : Type*} [NormedField K]
    [IsUltrametricDist K] (c : Kˣ →ₜ* ℂ) :
    ∃ δ > 0, δ ≤ 1 ∧ ∀ t : Kˣ, ‖(t : K) - 1‖ < δ → c t = 1 := by
  have hc : Tendsto c (nhds 1) (nhds 1) := by
    simpa only [map_one] using (map_continuous c).tendsto 1
  have hU := hc (Metric.ball_mem_nhds (1 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2))
  rw [Units.isEmbedding_val₀.nhds_eq_comap, mem_map, mem_comap] at hU
  obtain ⟨s, hs, hsU⟩ := hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hs
  refine ⟨min ε 1, lt_min hε one_pos, min_le_right _ _, fun t ht ↦ ?_⟩
  have ht1' : ‖(t : K) - 1‖ < 1 := ht.trans_le (min_le_right _ _)
  have ht1 : ‖(t : K)‖ = 1 := by
    have hne : ‖(1 : K)‖ ≠ ‖(t : K) - 1‖ := by rw [norm_one]; exact ht1'.ne'
    have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne
    rwa [add_sub_cancel, norm_one, max_eq_left ht1'.le] at this
  have hpow (n : ℕ) : ‖((t ^ n : Kˣ) : K) - 1‖ < min ε 1 := by
    induction n with
    | zero => simpa using lt_min hε one_pos
    | succ n ih =>
      rw [Units.val_pow_eq_pow_val] at ih ⊢
      have he : (t : K) ^ (n + 1) - 1 = (t : K) ^ n * ((t : K) - 1) + ((t : K) ^ n - 1) := by
        ring
      rw [he]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ih)
      rwa [norm_mul, norm_pow, ht1, one_pow, one_mul]
  refine eq_one_of_forall_norm_pow_sub_one_le (r := 1 / 2) (by norm_num) fun n ↦ ?_
  have hmem : ((t ^ n : Kˣ) : K) ∈ s := hball (by
    rw [Metric.mem_ball, dist_eq_norm, Units.val_one]
    exact (hpow n).trans_le (min_le_left _ _))
  have hlt := Metric.mem_ball.mp (hsU hmem)
  rw [dist_eq_norm, map_pow] at hlt
  exact hlt.le

/-- An element of a finite completion is the image of an integral unit exactly when its norm
is one. -/
private theorem mem_integerUnits_iff_norm_eq_one (v : V) (x : v.adicCompletion F) :
    x ∈ Units.val '' integerUnits(v) ↔ ‖x‖ = 1 := by
  have he1 : (Ideal.absNorm v.asIdeal : ℝ≥0) ≠ 1 :=
    (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v).ne'
  rw [NumberField.FinitePlace.norm_def, NNReal.coe_eq_one,
    WithZeroMulInt.toNNReal_eq_one_iff _ _ he1]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp ha
  · intro hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hx
    exact ⟨Units.mk0 x hx0,
      HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mpr hx, rfl⟩

/-- Paper: Definition 3.4.3.2(3), p. 152. Both finite Gaussian formulas
give Schwartz–Bruhat test functions on the completion. -/
theorem finiteStandardGaussian_mem (v : V) (c : QuasiCharacter (v.adicCompletion F)ˣ) :
    (fun x : Multiplicative (v.adicCompletion F) ↦ finiteStandardGaussianValue v c x.toAdd) ∈
      schwartzBruhatSubmodule (Multiplicative (v.adicCompletion F)) := by
  -- At a finite place, Schwartz–Bruhat means locally constant with compact support.
  classical
  set O : Set (v.adicCompletion F) := ↑(v.adicCompletionIntegers F) with hO
  have hOc : IsCompact O :=
    isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers (K := F) v)
  have hOo : IsOpen O := Valued.isOpen_valuationSubring _
  have hOcl : IsClosed O := Valued.isClosed_valuationSubring _
  have hlc : IsLocallyConstant (finiteStandardGaussianValue v c) ∧
      HasCompactSupport (finiteStandardGaussianValue v c) := by
    by_cases hu : unramified(v, c)
    · -- Unramified: the indicator of the compact open integer ring.
      have hf : finiteStandardGaussianValue v c = O.indicator (fun _ ↦ 1) := by
        funext x
        unfold finiteStandardGaussianValue
        rw [ite_eq_left hu]
      rw [hf]
      refine ⟨(IsLocallyConstant.iff_exists_open _).mpr fun x ↦ ?_,
        HasCompactSupport.intro hOc fun x hx ↦ indicator_of_notMem hx _⟩
      by_cases hx : x ∈ O
      · exact ⟨O, hOo, hx, fun y hy ↦ by rw [indicator_of_mem hy, indicator_of_mem hx]⟩
      · exact ⟨Oᶜ, hOcl.isOpen_compl, hx, fun y hy ↦ by
          rw [indicator_of_notMem hy, indicator_of_notMem hx]⟩
    · -- Ramified: the inverse character on the integral units, which form the unit sphere.
      set U₀ : Set (v.adicCompletion F) := Units.val '' integerUnits(v) with hU₀
      have hU₀O : U₀ ⊆ O := by
        rintro _ ⟨a, ha, rfl⟩
        exact (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp ha).le
      have hf : finiteStandardGaussianValue v c = U₀.indicator
          (fun y ↦ if hy : y ≠ 0 then (c (Units.mk0 y hy))⁻¹ else 0) := by
        funext x
        unfold finiteStandardGaussianValue
        rw [ite_eq_right hu]
      rw [hf]
      refine ⟨(IsLocallyConstant.iff_exists_open _).mpr fun x ↦ ?_,
        HasCompactSupport.intro hOc fun x hx ↦ indicator_of_notMem (fun h ↦ hx (hU₀O h)) _⟩
      by_cases hx : x ∈ U₀
      · obtain ⟨δ, hδ, hδ1, hδc⟩ := exists_forall_norm_sub_one_lt_map_eq_one c
        have hx1 : ‖x‖ = 1 := (mem_integerUnits_iff_norm_eq_one v x).mp hx
        have hx0 : x ≠ 0 := by
          rintro rfl
          simp at hx1
        refine ⟨Metric.ball x δ, Metric.isOpen_ball, Metric.mem_ball_self hδ, fun y hy ↦ ?_⟩
        rw [Metric.mem_ball, dist_eq_norm] at hy
        have hy1 : ‖y‖ = 1 := by
          have hne : ‖x‖ ≠ ‖y - x‖ := by rw [hx1]; exact (hy.trans_le hδ1).ne'
          have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne
          rwa [add_sub_cancel, hx1, max_eq_left (hy.trans_le hδ1).le] at this
        have hy0 : y ≠ 0 := by
          rintro rfl
          simp at hy1
        have hyU : y ∈ U₀ := (mem_integerUnits_iff_norm_eq_one v y).mpr hy1
        rw [indicator_of_mem hyU, indicator_of_mem hx, dite_eq_left hy0, dite_eq_left hx0]
        have ht : Units.mk0 y hy0 = Units.mk0 x hx0 * Units.mk0 (y / x) (div_ne_zero hy0 hx0) :=
          Units.ext (by simp [mul_div_cancel₀ _ hx0])
        have hsmall : ‖((Units.mk0 (y / x) (div_ne_zero hy0 hx0) : (v.adicCompletion F)ˣ) :
            v.adicCompletion F) - 1‖ < δ := by
          rw [Units.val_mk0, show y / x - 1 = (y - x) / x by field_simp, norm_div, hx1, div_one]
          exact hy
        rw [ht, map_mul, hδc _ hsmall, mul_one]
      · refine ⟨U₀ᶜ, ?_, hx, fun y hy ↦ by rw [indicator_of_notMem hy, indicator_of_notMem hx]⟩
        have hsphere : U₀ = Metric.sphere 0 1 := by
          ext y
          rw [mem_sphere_zero_iff_norm]
          exact mem_integerUnits_iff_norm_eq_one v y
        rw [hsphere]
        exact Metric.isClosed_sphere.isOpen_compl
  obtain ⟨g, hg⟩ := (mem_finitePlaceSchwartz_iff F v (finiteStandardGaussianValue v c)).mpr hlc
  have heq : (fun x : Multiplicative (v.adicCompletion F) ↦
      finiteStandardGaussianValue v c x.toAdd) = (g : Multiplicative (v.adicCompletion F) → ℂ) :=
    funext fun x ↦ (hg x.toAdd).symm
  rw [heq]
  exact g.property

/-- Paper: Definition 3.4.3.2(3), p. 152. The finite-place standard
Gaussian is the bundled test function given by the local indicator formula. -/
def finiteStandardGaussian (v : V) (c : QuasiCharacter (v.adicCompletion F)ˣ) :
    ℬ(v.adicCompletion F) :=
  ⟨fun x ↦ finiteStandardGaussianValue v c x.toAdd, finiteStandardGaussian_mem v c⟩

/-- Paper: Equations (3.4.3.7)–(3.4.3.8), p. 152. On an integer unit,
the local Gaussian takes the reciprocal of the character value. -/
theorem finiteStandardGaussian_integerUnit (v : V) (c : QuasiCharacter (v.adicCompletion F)ˣ)
    (u : (v.adicCompletion F)ˣ) (hu : u ∈ integerUnits(v)) :
    finiteStandardGaussian v c (Multiplicative.ofAdd u.val) = (c u)⁻¹ := by
  classical
  change finiteStandardGaussianValue v c u.val = (c u)⁻¹
  unfold finiteStandardGaussianValue
  split_ifs with hc
  · rw [indicator_of_mem (show u.val ∈ (v.adicCompletionIntegers F : Set _) from hu.1),
      hc u hu, inv_one]
  · rw [indicator_of_mem (mem_image_of_mem _ hu)]
    simp [u.ne_zero]

local notation "infiniteUnitaryRestriction(" χ "," w ")" =>
  ((χ).comp ⟨IdeleClassGroup.ofCompletion (𝓞 F) F w, continuous_ideleClass_ofCompletion F w⟩)

local notation "globalGaussianTest(" χ ")" => fun x : Multiplicative 𝔸[F] ↦
  (∏ w : InfinitePlace F,
    infiniteStandardGaussian w (infiniteUnitaryRestriction(χ,w))
      (Multiplicative.ofAdd (x.toAdd.1 w))) *
    ∏ᶠ v : V, finiteStandardGaussian v (finitePlaceRestriction F v (ideleClassNormTwist (χ) 0))
      (Multiplicative.ofAdd (x.toAdd.2 v))

open scoped TensorProduct

section
/-- The product of finitely many local tests belongs to the Schwartz–Bruhat space
of the product group. -/
private theorem schwartzBruhat_pi_test {ι : Type*} [Fintype ι] (G : ι → Type*)
    [∀ i, CommGroup (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)]
    [∀ i, T2Space (G i)] [∀ i, LocallyCompactSpace (G i)] [∀ i, SecondCountableTopology (G i)]
    (f : ∀ i, SchwartzBruhat (G i)) : ∃ g : SchwartzBruhat (∀ i, G i),
      ∀ x, g x = ∏ i, f i (x i) := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl _ =>
    let : CompactSpace (∀ i, G i) := Finite.compactSpace
    obtain ⟨g, hg⟩ := compact_schwartzBruhat_one (H := (i : ι) → G i)
    exact ⟨g, fun x ↦ (hg x).trans (by simp)⟩
  | inr hi =>
    obtain ⟨i⟩ := hi
    let J := {j : ι // j ≠ i}
    obtain ⟨g, hg⟩ := schwartzBruhat_pi_test (ι := J) (fun j ↦ G j.val) (fun j ↦ f j.val)
    let e : ((j : ι) → G j) ≃ₜ* (G i × ((j : J) → G j.val)) :=
      { Homeomorph.piSplitAt i G with map_mul' := fun _ _ ↦ rfl }
    obtain ⟨t, ht⟩ := schwartzBruhat_kernel_equiv (G := G i) (H := (j : J) → G j.val)
    let q := t (UniformSpace.Completion.coe' (α := InductiveTensor (SchwartzBruhat (G i))
      (SchwartzBruhat ((j : J) → G j.val))) ((f i) ⊗ₜ[ℂ] g))
    refine ⟨⟨q.val ∘ e, schwartzBruhat_mem_comp_equiv e q.property⟩, fun x ↦ ?_⟩
    change q (x i, fun j ↦ x j.val) = _
    rw [show q (x i, fun j ↦ x j.val) = _ from ht (f i) g _ _, hg, Fintype.prod_eq_mul_prod_compl i]
    exact congrArg (_ * ·) (Finset.prod_subtype _ (fun j ↦ by simp) (fun j ↦ f j (x j))).symm
termination_by Fintype.card ι
decreasing_by
  classical
  exact Fintype.card_subtype_lt (x := i) (not_not_intro rfl)
end

/-- Paper: Equation (3.4.3.9), p. 152. The restricted product of local
Gaussians is Schwartz–Bruhat on the adeles. -/
theorem adelicStandardGaussian_mem (χ : PontryaginDual C_F) :
    globalGaussianTest(χ) ∈ schwartzBruhatSubmodule (Multiplicative 𝔸[F]) := by
  classical
  let c := ideleClassNormTwist χ 0
  let a (w : InfinitePlace F) := infiniteStandardGaussian w (infiniteUnitaryRestriction(χ,w))
  let g (v : V) := finiteStandardGaussian v (finitePlaceRestriction F v c)
  obtain ⟨S, hS⟩ : ∃ S : Finset V, c ∈ unramifiedOutside F S :=
    mem_iUnion.mp ((iUnion_unramifiedOutside F).symm ▸ mem_univ c)
  have htail (v : V) (hv : v ∉ S) (x : v.adicCompletion F) :
      g v (Multiplicative.ofAdd x) =
        (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ ↦ (1 : ℂ)) x := by
    have hu (u : (v.adicCompletion F)ˣ) (hu : u ∈ integerUnits(v)) : finitePlaceRestriction F v c u = 1 :=
      (mem_unramifiedOutside_iff F S c).mp hS v hv ((v.adicCompletionIntegers F).unitsEquivUnitsType ⟨u, hu⟩)
    exact ite_eq_left hu
  let G (w : InfinitePlace F) := Multiplicative w.Completion
  let (w : InfinitePlace F) : T2Space (G w) := (inferInstance : T2Space w.Completion)
  let (w : InfinitePlace F) : LocallyCompactSpace (G w) := (inferInstance : LocallyCompactSpace w.Completion)
  let (w : InfinitePlace F) : SecondCountableTopology (G w) :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  obtain ⟨a₀, ha⟩ := schwartzBruhat_pi_test G a
  let e : Multiplicative (InfiniteAdeleRing F) ≃ₜ* ((w : InfinitePlace F) → G w) :=
    { toFun := fun x w ↦ Multiplicative.ofAdd (x.toAdd w)
      invFun := fun x ↦ Multiplicative.ofAdd (fun w ↦ (x w).toAdd)
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl
      continuous_toFun := continuous_id
      continuous_invFun := continuous_id }
  let : T2Space (Multiplicative (InfiniteAdeleRing F)) := e.toHomeomorph.isEmbedding.t2Space
  let : LocallyCompactSpace (Multiplicative (InfiniteAdeleRing F)) := e.toHomeomorph.isOpenEmbedding.locallyCompactSpace
  let arch : ℬ(InfiniteAdeleRing F) := ⟨a₀.val ∘ e, schwartzBruhat_mem_comp_equiv e a₀.property⟩
  obtain ⟨t, ht⟩ := sAdeleSchwartz_inductiveTensor_equiv F S
  let fS := t (arch ⊗ₜ[ℂ] (⨂ₜ[ℂ] v : S, g v.val))
  let h := sAdeleSchwartzToGlobal F S fS
  suffices he : globalGaussianTest(χ) = h.val by rw [he]; exact h.property
  funext x
  let b (v : V) := g v (Multiplicative.ofAdd (x.toAdd.2 v))
  have hb : b.HasFiniteMulSupport := by
    apply eventually_cofinite.mp
    filter_upwards [S.eventually_cofinite_notMem, x.toAdd.2.property] with v hv hx
    exact (htail v hv _).trans (indicator_of_mem hx _)
  rw [show h.val x = _ from sAdeleSchwartzToGlobal_apply F S fS x.toAdd]
  by_cases hx : ∀ v : V, v ∉ S → x.toAdd.2 v ∈ v.adicCompletionIntegers F
  · rw [ite_eq_left hx, show fS (Multiplicative.ofAdd _) = _ from ht arch (fun v ↦ g v.val) _]
    change _ * (∏ᶠ v, b v) = a₀ _ * ∏ v : S, b v.val
    have hav := ha (e (Multiplicative.ofAdd x.toAdd.1))
    change a₀ (e (Multiplicative.ofAdd x.toAdd.1)) = _ at hav
    apply congrArg₂ (· * ·) hav.symm
    rw [finprod_eq_prod_of_mulSupport_subset (s := S) b
      (mulSupport_subset_iff'.mpr fun v hv ↦ (htail v hv _).trans (indicator_of_mem (hx v hv) _)),
      Finset.prod_subtype S (fun _ ↦ Iff.rfl)]
  · rw [ite_eq_right hx]
    push Not at hx
    obtain ⟨v, hv, hx⟩ := hx
    change _ * (∏ᶠ v, b v) = 0
    rw [finprod_eq_zero b v ((htail v hv _).trans (indicator_of_notMem hx _)) hb, mul_zero]

/-- Paper: Equation (3.4.3.9), p. 152. The adelic Gaussian is the pointwise
restricted product of the indicated local Gaussians.
Deviation: The component is specified by a unitary representative, and the complex
factors use the conjugated monomials of `infiniteStandardGaussianValue`. -/
def adelicStandardGaussian (χ : PontryaginDual C_F) : ℬ(𝔸[F]) :=
  ⟨globalGaussianTest(χ), adelicStandardGaussian_mem χ⟩

/-- Paper: Equation (3.4.3.9), p. 152. The trivial-character Gaussian
at the zero adele has one factor of one over two pi per complex place. -/
theorem adelicStandardGaussian_trivial_zero :
    adelicStandardGaussian (1 : PontryaginDual C_F) (Multiplicative.ofAdd 0) =
      (2 * (Real.pi : ℂ))⁻¹ ^ InfinitePlace.nrComplexPlaces F := by
  classical
  have hInf (w : InfinitePlace F) :
      ((1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)).comp
        ⟨IdeleClassGroup.ofCompletion (𝓞 F) F w, continuous_ideleClass_ofCompletion F w⟩) = 1 :=
    ContinuousMonoidHom.ext fun _ ↦ rfl
  have hFin (v : HeightOneSpectrum (𝓞 F)) :
      finiteStandardGaussian v (finitePlaceRestriction F v (ideleClassNormTwist 1 0))
        (Multiplicative.ofAdd 0) = 1 := by
    have hc : ∀ u, finitePlaceRestriction F v (ideleClassNormTwist 1 0) u = 1 := fun u ↦ by
      change (((1 : PontryaginDual (IdeleClassGroup (𝓞 F) F))
        (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u) : Circle) : ℂ) *
        (((ideleClassNorm F (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u) : NNReal) : ℝ) : ℂ) ^
          (0 : ℂ) = 1
      simp
    change finiteStandardGaussianValue v _ 0 = 1
    simp [finiteStandardGaussianValue, hc]
  change (∏ w : InfinitePlace F,
      infiniteStandardGaussian w _ (Multiplicative.ofAdd ((0 : 𝔸[F]).1 w))) *
    ∏ᶠ v : HeightOneSpectrum (𝓞 F),
      finiteStandardGaussian v _ (Multiplicative.ofAdd ((0 : 𝔸[F]).2 v)) = _
  simp only [hInf]
  have h2 (v : HeightOneSpectrum (𝓞 F)) : (0 : 𝔸[F]).2 v = 0 := rfl
  have hI (w : InfinitePlace F) :
      infiniteStandardGaussian w 1 (Multiplicative.ofAdd ((0 : 𝔸[F]).1 w)) =
        if w.IsReal then (1 : ℂ) else (2 * (Real.pi : ℂ))⁻¹ :=
    infiniteStandardGaussian_trivial_zero w
  simp only [h2, hFin, finprod_one, mul_one]
  refine (Finset.prod_congr rfl fun w _ ↦ hI w).trans ?_
  rw [InfinitePlace.prod_eq_prod_mul_prod]
  have hR : ∀ w : {w : InfinitePlace F // w.IsReal},
      (if w.1.IsReal then (1 : ℂ) else (2 * (Real.pi : ℂ))⁻¹) = 1 :=
    fun w ↦ ite_eq_left_iff.mpr fun h ↦ absurd w.2 h
  have hC : ∀ w : {w : InfinitePlace F // w.IsComplex},
      (if w.1.IsReal then (1 : ℂ) else (2 * (Real.pi : ℂ))⁻¹) = (2 * (Real.pi : ℂ))⁻¹ :=
    fun w ↦ ite_eq_right_iff.mpr fun h ↦ absurd h (InfinitePlace.not_isReal_iff_isComplex.mpr w.2)
  simp only [hR, hC, Finset.prod_const_one, Finset.prod_const, Finset.card_univ, one_mul]

/-- Unitary characters of the complex units that agree on the unit circle have the same
angular exponent. -/
private theorem complexUnits_character_parameter_snd_congr (c d : ℂˣ →ₜ* ℂ)
    (hc : ∀ x, ‖c x‖ = 1) (hd : ∀ x, ‖d x‖ = 1)
    (h : ∀ x : ℂˣ, ‖(x : ℂ)‖ = 1 → c x = d x) :
    (existsUnique_complexUnits_character_parameters c hc).exists.choose.2 =
      (existsUnique_complexUnits_character_parameters d hd).exists.choose.2 := by
  have hP := (existsUnique_complexUnits_character_parameters c hc).exists
  have hQ := (existsUnique_complexUnits_character_parameters d hd).exists
  change hP.choose.2 = hQ.choose.2
  have key (x : ℂˣ) : ((x : ℂ) / (‖(x : ℂ)‖ : ℂ)) ^ hP.choose.2 =
      ((x : ℂ) / (‖(x : ℂ)‖ : ℂ)) ^ hQ.choose.2 := by
    have hr : ‖(x : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr x.ne_zero
    let u : ℂˣ := Units.mk0 ((x : ℂ) / (‖(x : ℂ)‖ : ℂ))
      (div_ne_zero x.ne_zero (Complex.ofReal_ne_zero.mpr hr))
    have hu : ‖(u : ℂ)‖ = 1 := by
      change ‖(x : ℂ) / (‖(x : ℂ)‖ : ℂ)‖ = 1
      rw [norm_div, Complex.norm_of_nonneg (norm_nonneg _), div_self hr]
    have h1 := hP.choose_spec.2 u
    have h2 := hQ.choose_spec.2 u
    rw [hu, one_pow, Complex.ofReal_one, Complex.one_cpow, one_mul, div_one] at h1 h2
    exact h1.symm.trans ((h u hu).trans h2)
  have hpair := (existsUnique_complexUnits_character_parameters c hc).unique hP.choose_spec
    (show (hP.choose.1, hQ.choose.2).1.re = 0 ∧ _ from
      ⟨hP.choose_spec.1, fun x ↦ by rw [hP.choose_spec.2 x, key x]⟩)
  exact (congrArg Prod.snd hpair :)

/-- Paper: Definition 3.4.3.2, p. 152. The adelic Gaussian depends only on
the restriction of the unitary representative to the norm-one classes. -/
theorem adelicStandardGaussian_eq_of_restriction (χ ψ : PontryaginDual C_F)
    (h : normOneRestriction (G := C_F) (ideleClassNorm F) (ideleClassNormTwist χ 0) =
      normOneRestriction (G := C_F) (ideleClassNorm F) (ideleClassNormTwist ψ 0)) :
    adelicStandardGaussian χ = adelicStandardGaussian ψ := by
  classical
  have hk : ∀ g : C_F, ideleClassNorm F g = 1 → χ g = ψ g := fun g hg ↦ by
    have hg' := DFunLike.congr_fun h ⟨g, hg⟩
    change (χ g : ℂ) * (((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ (0 : ℂ) =
      (ψ g : ℂ) * (((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ (0 : ℂ) at hg'
    rw [Complex.cpow_zero, mul_one, mul_one] at hg'
    exact Circle.coe_injective hg'
  have hN (w : InfinitePlace F) (y : w.Completionˣ) (hy : ‖(y : w.Completion)‖ = 1) :
      χ (IdeleClassGroup.ofCompletion (𝓞 F) F w y) =
        ψ (IdeleClassGroup.ofCompletion (𝓞 F) F w y) :=
    hk _ (by
      rw [ideleClassNorm_ofCompletion, show Units.map nnNormHom.toMonoidHom y = 1 from
        Units.ext (NNReal.coe_injective hy), one_pow])
  have hInf (w : InfinitePlace F) (x : w.Completion) :
      infiniteStandardGaussianValue w (infiniteUnitaryRestriction(χ,w)) x =
        infiniteStandardGaussianValue w (infiniteUnitaryRestriction(ψ,w)) x := by
    unfold infiniteStandardGaussianValue
    by_cases hw : w.IsReal
    · simp only [dite_eq_left hw]
      congr 4
      exact hN w (-1) (by rw [Units.val_neg, Units.val_one, norm_neg, norm_one])
    · have hc := InfinitePlace.not_isReal_iff_isComplex.mp hw
      have hm := complexUnits_character_parameter_snd_congr
        ((circleToComplex).comp ((infiniteUnitaryRestriction(χ,w)).comp
          ⟨Units.map complexCoord(hc).symm.toMonoidHom,
            (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
              hc).symm.continuous.units_map _⟩))
        ((circleToComplex).comp ((infiniteUnitaryRestriction(ψ,w)).comp
          ⟨Units.map complexCoord(hc).symm.toMonoidHom,
            (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
              hc).symm.continuous.units_map _⟩))
        (fun _ ↦ Circle.norm_coe _) (fun _ ↦ Circle.norm_coe _)
        (fun x hx ↦ congrArg (fun z : Circle ↦ (z : ℂ))
          (hN w (Units.map complexCoord(hc).symm.toMonoidHom x)
            (((InfinitePlace.Completion.isometryEquivComplexOfIsComplex
              hc).symm.isometry.norm_map_of_map_zero
                (map_zero complexCoord(hc).symm) (x : ℂ)).trans hx)))
      simp only [dite_eq_right hw, hm]
  have hFin (v : V) (x : v.adicCompletion F) :
      finiteStandardGaussianValue v (finitePlaceRestriction F v (ideleClassNormTwist χ 0)) x =
        finiteStandardGaussianValue v
          (finitePlaceRestriction F v (ideleClassNormTwist ψ 0)) x := by
    have hu : ∀ u ∈ integerUnits(v), finitePlaceRestriction F v (ideleClassNormTwist χ 0) u =
        finitePlaceRestriction F v (ideleClassNormTwist ψ 0) u := fun u hu ↦
      DFunLike.congr_fun h ⟨IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u, by
        change ideleClassNorm F _ = 1
        rw [ideleClassNorm_ofAdicCompletion]
        exact Units.ext (NNReal.coe_injective (Valued.toNormedField.norm_eq_one_iff.mpr
          (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp hu)))⟩
    have h1 : unramified(v, finitePlaceRestriction F v (ideleClassNormTwist χ 0)) ↔
        unramified(v, finitePlaceRestriction F v (ideleClassNormTwist ψ 0)) :=
      forall₂_congr fun u hu' ↦ by rw [hu u hu']
    rw [finiteStandardGaussianValue, finiteStandardGaussianValue]
    by_cases h0 : unramified(v, finitePlaceRestriction F v (ideleClassNormTwist χ 0))
    · rw [ite_eq_left h0, ite_eq_left (h1.mp h0)]
    · rw [ite_eq_right h0, ite_eq_right (mt h1.mpr h0)]
      by_cases hx : x ∈ Units.val '' (integerUnits(v) : Set (v.adicCompletion F)ˣ)
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
        obtain ⟨u, hu', rfl⟩ := hx
        rw [dite_eq_left u.ne_zero, dite_eq_left u.ne_zero, Units.mk0_val, hu u hu']
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
  apply Subtype.ext
  funext x
  exact congrArg₂ (· * ·) (Finset.prod_congr rfl fun w _ ↦ hInf w _)
    (finprod_congr fun v ↦ hFin v _)

-- TODO(paper-gap): Even with the corrected complex Gaussians, the Tamagawa
-- zeta integral has an extra factor of |d_F|^(-1/2) relative to the Euler product of §3.2.

/-- Paper: Paragraph after Equation (3.4.3.9), p. 152.
The completed function with the Gaussian normalization is the continued
global zeta function of the standard Gaussian on the chosen component.
Deviation: This uses the corrected complex Gaussian and the Tamagawa measures.
The comparison with the completed Euler product of §3.2 includes the factor `|d_F|^(-1/2)`. -/
def gaussianCompletedHeckeL (χ : PontryaginDual C_F) (s : ℂ) : ℂ :=
  globalIdelicZFunction (adelicStandardGaussian χ) (ideleClassNormTwist χ s)

/-- Paper: Paragraph after Equation (3.4.3.9), p. 152.
In the half-plane of absolute convergence, the Gaussian normalization
is the global zeta integral of the Gaussian. -/
theorem gaussianCompletedHeckeL_eq_integral (χ : PontryaginDual C_F) (s : ℂ)
    (hs : 1 < s.re) :
    gaussianCompletedHeckeL χ s =
      globalIdelicZetaIntegral (adelicStandardGaussian χ) (ideleClassNormTwist χ s) := by
  refine globalIdelicZFunction_eq_integral (adelicStandardGaussian χ) ?_
  change 1 < quasiCharacterAbscissa (ideleClassNorm F) (isProperMap_ideleClassNorm F)
    (ideleClassNorm_ne_one (F := F)) (ideleClassNormTwist χ s)
  rwa [quasiCharacterAbscissa_ideleClassNormTwist]

section
local notation "μ∞" => infiniteLocalMultiplicativeTamagawaMeasure F
local notation "λ∞" => infiniteLocalAdditiveTamagawaMeasure F
private local instance (w : InfinitePlace F) : MeasurableSpace w.Completion := borel _
private local instance (w : InfinitePlace F) : BorelSpace w.Completion := ⟨rfl⟩
private local instance (w : InfinitePlace F) : BorelSpace w.Completionˣ := borelSpace_units_of_continuousInv₀ _

private theorem integral_infiniteLocal_radial (w : InfinitePlace F) (H : ℝ → ℂ)
    (hzero : (λ∞ w) {0} = 0) :
    (∫ g : w.Completionˣ, H ‖g.val‖ ∂μ∞ w) =
      ∫ x : w.Completion, (‖x‖ ^ w.mult)⁻¹ • H ‖x‖ ∂λ∞ w := by
  let ρ (x : w.Completion) := (↑(‖x‖₊ ^ w.mult) : ENNReal)⁻¹
  have hρ : Measurable ρ := by fun_prop
  have hn : ∀ᵐ x : w.Completion ∂λ∞ w, x ≠ 0 := by simpa only [ae_iff, not_not, ofPred_eq_eq_singleton] using hzero
  have hval := (IsOpenUnits.isOpenEmbedding_unitsVal (M := w.Completion)).measurableEmbedding
  have hfull : ∀ᵐ x ∂(λ∞ w).withDensity ρ, x ∈ range (Units.val : w.Completionˣ → w.Completion) :=
    (hn.mono fun x hx ↦ (isUnit_iff_ne_zero.mpr hx : IsUnit x)).filter_mono (withDensity_absolutelyContinuous _ _).ae_le
  change (∫ g : w.Completionˣ, (fun x : w.Completion ↦ H ‖x‖) g.val ∂((λ∞ w).withDensity ρ).comap Units.val) = _
  rw [← hval.integral_map (fun x : w.Completion ↦ H ‖x‖), hval.map_comap, Measure.restrict_eq_self_of_ae_mem hfull,
    integral_withDensity_eq_integral_toReal_smul hρ (hn.mono fun x hx ↦ ?_)]
  · simp [ρ]
  · exact ENNReal.inv_lt_top.mpr (by exact_mod_cast pow_pos (show 0 < ‖x‖₊ from pos_iff_ne_zero.mpr (nnNorm_ne_zero_iff.mpr hx)) w.mult)

private theorem infiniteLocal_real_gaussian_integral (w : InfinitePlace F) (hw : w.IsReal) (t : ℂ) (ht : 0 < t.re) :
    (∫ g : w.Completionˣ, (‖g.val‖ : ℂ) ^ t * (Real.exp (-Real.pi * ‖g.val‖ ^ 2) : ℂ) ∂μ∞ w) =
      Complex.Gammaℝ t := by
  let e := (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).toHomeomorph.toMeasurableEquiv
  have hμ : λ∞ w = (volume : Measure ℝ).map e.symm := by
    simp only [infiniteLocalAdditiveTamagawaMeasure, hw, dite_true]
    rfl
  have hzero : (λ∞ w) {0} = 0 := by
    rw [hμ, e.symm.map_apply]
    rw [show e.symm ⁻¹' ({0} : Set w.Completion) = ({0} : Set ℝ) from
      Set.ext fun x ↦ (map_eq_zero (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm)]
    exact measure_singleton _
  let f (r : ℝ) := (r : ℂ) ^ t * (Real.exp (-Real.pi * r ^ 2) : ℂ)
  have hn (y : ℝ) : ‖e.symm y‖ = |y| := by
    exact (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.isometry.norm_map_of_map_zero
      (map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm) y
  change (∫ g : w.Completionˣ, f ‖g.val‖ ∂μ∞ w) = _
  rw [integral_infiniteLocal_radial w f hzero, hμ, integral_map_equiv, hw.mult_eq_one]
  simp_rw [hn, pow_one]
  rw [integral_comp_abs_complex (fun r ↦ r⁻¹ • f r)]
  have he : (∫ r in Ioi (0 : ℝ), r⁻¹ • f r) =
      mellin (fun r : ℝ ↦ (Real.exp (-Real.pi * r ^ 2) : ℂ)) t := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
    simp [f, Complex.real_smul, Complex.cpow_sub _ _ hr', div_eq_mul_inv, mul_left_comm, mul_assoc]
  rw [he, mellin_gaussian Real.pi_pos ht, Complex.Gammaℝ_def]
  rw [neg_div]
  ring

private theorem infiniteLocal_complex_gaussian_integral (w : InfinitePlace F) (hw : w.IsComplex) (t : ℂ)
    (ht : 0 < t.re) :
    (∫ g : w.Completionˣ, (‖g.val‖ : ℂ) ^ (2 * t) * (Real.exp (-(2 * Real.pi) * ‖g.val‖ ^ 2) : ℂ) /
      (2 * (Real.pi : ℂ)) ∂μ∞ w) = Complex.Gammaℂ t / 2 := by
  let e := (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).toHomeomorph.toMeasurableEquiv
  have hμ : λ∞ w = (2 • (volume : Measure ℂ)).map e.symm := by
    simp only [infiniteLocalAdditiveTamagawaMeasure, InfinitePlace.not_isReal_iff_isComplex.mpr hw, dite_false]
    rfl
  have hzero : (λ∞ w) {0} = 0 := by
    rw [hμ, e.symm.map_apply]
    rw [show e.symm ⁻¹' ({0} : Set w.Completion) = ({0} : Set ℂ) from
      Set.ext fun x ↦ (map_eq_zero (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm)]
    simp
  let f (r : ℝ) := (r : ℂ) ^ (2 * t) * (Real.exp (-(2 * Real.pi) * r ^ 2) : ℂ) / (2 * (Real.pi : ℂ))
  have hn (y : ℂ) : ‖e.symm y‖ = ‖y‖ := by
    exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).symm.isometry.norm_map_of_map_zero
      (map_zero (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm) y
  change (∫ g : w.Completionˣ, f ‖g.val‖ ∂μ∞ w) = _
  rw [integral_infiniteLocal_radial w f hzero, hμ, integral_map_equiv, hw.mult_eq_two]
  simp_rw [hn]
  rw [show (2 • (volume : Measure ℂ)) = (2 : ENNReal) • volume from by simp [two_smul], integral_smul_measure,
    Complex.integral_radial (fun r ↦ (r ^ 2)⁻¹ • f r)]
  have he : (∫ r in Ioi (0 : ℝ), (r : ℂ) * ((r ^ 2)⁻¹ • f r)) =
      mellin (fun r : ℝ ↦ (Real.exp (-(2 * Real.pi) * r ^ 2) : ℂ)) (2 * t) / (2 * (Real.pi : ℂ)) := by
    rw [mellin, ← integral_div]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
    simp only [f, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_pow, smul_eq_mul,
      Complex.cpow_sub _ _ hr', Complex.cpow_one]
    field_simp
  rw [he, mellin_gaussian (by positivity : 0 < 2 * Real.pi) (by simpa using ht : 0 < (2 * t).re),
    Complex.Gammaℂ_def, show (2 * t) / 2 = t by ring]
  simp only [Complex.real_smul, ENNReal.toReal_ofNat, Complex.ofReal_ofNat, Complex.ofReal_mul]
  field_simp [Real.pi_ne_zero]

end

section
open scoped Classical
local notation "μ∞" => infiniteLocalMultiplicativeTamagawaMeasure F
private local instance (w : InfinitePlace F) : MeasurableSpace w.Completion := borel _

private theorem infinitePlaceRestriction_twist_apply (w : InfinitePlace F) (χ : PontryaginDual C_F)
    (z : ℂ) (g : w.Completionˣ) : infinitePlaceRestriction F w (ideleClassNormTwist χ z) g =
    (infiniteUnitaryRestriction(χ,w) g : ℂ) * ((‖g.val‖ ^ w.mult : ℝ) : ℂ) ^ z := by
  change _ * (((ideleClassNorm F (IdeleClassGroup.ofCompletion (𝓞 F) F w g) : ℝ≥0) : ℝ) : ℂ) ^ z = _
  rw [ideleClassNorm_ofCompletion, Units.val_pow_eq_pow_val, NNReal.coe_pow]
  rfl

private theorem gaussian_angular_cancel (z : ℂ) (hz : z ≠ 0) (m : ℤ) :
    (if 0 ≤ m then (star z) ^ m.natAbs else z ^ m.natAbs) * (z / (‖z‖ : ℂ)) ^ m =
      (‖z‖ : ℂ) ^ m.natAbs := by
  have hr : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
  cases m with
  | ofNat n =>
    change (star z) ^ n * (z / (‖z‖ : ℂ)) ^ (n : ℤ) = (‖z‖ : ℂ) ^ n
    rw [zpow_natCast, ← mul_pow]
    congr 1
    rw [← mul_div_assoc, show star z * z = (‖z‖ : ℂ) ^ 2 from Complex.conj_mul' z]
    field_simp
  | negSucc n =>
    simp only [Int.negSucc_not_nonneg, ite_false, Int.natAbs_negSucc, zpow_negSucc, ← inv_pow, ← mul_pow]
    congr 1
    field_simp

private theorem infiniteGaussian_real_factor (w : InfinitePlace F) (hw : w.IsReal) (χ : PontryaginDual C_F)
    (s : ℂ) (hs : 0 < s.re) :
    (∫ g : w.Completionˣ, infiniteStandardGaussian w (infiniteUnitaryRestriction(χ,w)) (Multiplicative.ofAdd g.val) *
      infinitePlaceRestriction F w (ideleClassNormTwist χ s) g ∂μ∞ w) =
        let p := (realHeckeCharacter_parameters χ w hw).exists.choose
        Complex.Gammaℝ (s + p.1 + (p.2.val : ℂ)) := by
  let p := (realHeckeCharacter_parameters χ w hw).exists.choose
  have hp := (realHeckeCharacter_parameters χ w hw).exists.choose_spec
  let η := infiniteUnitaryRestriction(χ,w)
  let e := realCoord(hw)
  have hn (g : w.Completion) : |e g| = ‖g‖ :=
    (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).isometry.norm_map_of_map_zero (map_zero e) g
  have hchar (g : w.Completionˣ) : (η g : ℂ) =
      (‖g.val‖ : ℂ) ^ p.1 * (if 0 < e g.val then 1 else (-1 : ℂ)) ^ p.2.val := by
    let u := Units.map e.toMonoidHom g
    have he : Units.map e.symm.toMonoidHom u = g := Units.ext (e.symm_apply_apply g.val)
    have h := hp.2 u
    rw [he, infinitePlaceRestriction_twist_apply, Complex.cpow_zero, mul_one] at h
    exact h.trans (by rw [show ‖u.val‖ = ‖g.val‖ from hn g.val]; rfl)
  have hsign : (η (-1) : ℂ) = (-1 : ℂ) ^ p.2.val := by
    simpa [e, show ¬ (1 : ℝ) < 0 by norm_num] using hchar (-1)
  let t := s + p.1 + (p.2.val : ℂ)
  have ht : 0 < t.re := by
    have hr : p.1.re = 0 := hp.1
    simpa only [t, Complex.add_re, hr, add_zero, Complex.natCast_re] using
      add_pos_of_pos_of_nonneg hs (Nat.cast_nonneg p.2.val)
  refine (integral_congr_ae ?_).trans (infiniteLocal_real_gaussian_integral w hw t ht)
  filter_upwards with g
  change infiniteStandardGaussianValue w η g.val * _ = _
  simp only [infiniteStandardGaussianValue, hw, dite_true, Complex.ofReal_mul]
  rw [infinitePlaceRestriction_twist_apply, hw.mult_eq_one, pow_one]
  change _ * ((η g : ℂ) * _) = _
  rw [hchar]
  have hr : (‖g.val‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr g.ne_zero)
  have hbase : ((if η (-1) = 1 then (1 : ℝ) else e g.val) : ℂ) *
      (if 0 < e g.val then 1 else (-1 : ℂ)) ^ p.2.val = (‖g.val‖ : ℂ) ^ p.2.val := by
    have hk : p.2 = 0 ∨ p.2 = 1 := by omega
    rcases hk with h | h
    · have hχ : η (-1) = 1 := Circle.coe_injective (by simpa [h] using hsign)
      simp [hχ, h]
    · have hχ : η (-1) ≠ 1 := fun hχ ↦ by norm_num [hχ, h] at hsign
      simp only [hχ, ite_false, h, Fin.isValue, Fin.val_one, pow_one]
      rw [← hn]
      split_ifs with h
      · rw [mul_one, abs_of_pos h]
      · rw [mul_neg_one, abs_of_nonpos (le_of_not_gt h), Complex.ofReal_neg]

  have hsq : e g.val ^ 2 = ‖g.val‖ ^ 2 := by rw [← hn, sq_abs]
  change (↑(if η (-1) = 1 then (1 : ℝ) else e g.val) : ℂ) * (Real.exp (-Real.pi * (e g.val)^2) : ℂ) * _ = _
  rw [hsq]
  simp only [t, Complex.cpow_add _ _ hr, Complex.cpow_natCast, apply_ite Complex.ofReal]
  linear_combination ((Real.exp (-Real.pi * ‖g.val‖ ^ 2) : ℂ) * (‖g.val‖ : ℂ) ^ p.1 * (‖g.val‖ : ℂ) ^ s) * hbase

private theorem infiniteGaussian_complex_factor (w : InfinitePlace F) (hw : w.IsComplex) (χ : PontryaginDual C_F)
    (s : ℂ) (hs : 0 < s.re) :
    (∫ g : w.Completionˣ, infiniteStandardGaussian w (infiniteUnitaryRestriction(χ,w)) (Multiplicative.ofAdd g.val) *
      infinitePlaceRestriction F w (ideleClassNormTwist χ s) g ∂μ∞ w) =
        let p := (complexHeckeCharacter_parameters χ w hw).exists.choose
        Complex.Gammaℂ (s + p.1 + (p.2.natAbs : ℂ) / 2) / 2 := by
  let p := (complexHeckeCharacter_parameters χ w hw).exists.choose
  have hp := (complexHeckeCharacter_parameters χ w hw).exists.choose_spec
  let η := infiniteUnitaryRestriction(χ,w)
  let e := complexCoord(hw)
  let c : ℂˣ →ₜ* ℂ := (circleToComplex).comp (η.comp ⟨Units.map e.symm.toMonoidHom,
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).symm.continuous.units_map _⟩)
  let hU (x : ℂˣ) : ‖c x‖ = 1 := Circle.norm_coe _
  have hex := existsUnique_complexUnits_character_parameters c hU
  have heq : hex.exists.choose = p := by
    apply hex.unique hex.exists.choose_spec
    refine ⟨hp.1, fun x ↦ ?_⟩
    have h := hp.2 x
    rw [infinitePlaceRestriction_twist_apply, Complex.cpow_zero, mul_one] at h
    exact h
  have hn (g : w.Completion) : ‖e g‖ = ‖g‖ :=
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).isometry.norm_map_of_map_zero (map_zero e) g
  have hchar (g : w.Completionˣ) : (η g : ℂ) =
      ((‖g.val‖ ^ 2 : ℝ) : ℂ) ^ p.1 * (e g.val / (‖g.val‖ : ℂ)) ^ p.2 := by
    let u := Units.map e.toMonoidHom g
    have h := hex.exists.choose_spec.2 u
    rw [heq] at h
    change (η (Units.map e.symm.toMonoidHom u) : ℂ) = _ at h
    rw [show Units.map e.symm.toMonoidHom u = g from Units.ext (e.symm_apply_apply g.val)] at h
    exact h.trans (by rw [show ‖u.val‖ = ‖g.val‖ from hn g.val]; rfl)
  let t := s + p.1 + (p.2.natAbs : ℂ) / 2
  have ht : 0 < t.re := by
    have hr : p.1.re = 0 := hp.1
    simp [t, Complex.add_re, hr]
    positivity
  refine (integral_congr_ae ?_).trans (infiniteLocal_complex_gaussian_integral w hw t ht)
  filter_upwards with g
  change infiniteStandardGaussianValue w η g.val * _ = _
  simp only [infiniteStandardGaussianValue, InfinitePlace.not_isReal_iff_isComplex.mpr hw, dite_false]
  change ((if 0 ≤ hex.exists.choose.2 then (star (e g.val)) ^ hex.exists.choose.2.natAbs
    else (e g.val) ^ hex.exists.choose.2.natAbs) * Complex.exp _ / _) * _ = _
  rw [heq, infinitePlaceRestriction_twist_apply, hw.mult_eq_two]
  change _ * ((η g : ℂ) * _) = _
  rw [hchar]
  have hangle := gaussian_angular_cancel (e g.val) ((map_ne_zero e).mpr g.ne_zero) p.2
  rw [hn] at hangle
  have hsq : e g.val * star (e g.val) = (‖g.val‖ : ℂ) ^ 2 := by rw [← hn]; exact Complex.mul_conj' _
  have he : -2 * (Real.pi : ℂ) * e g.val * star (e g.val) = ((-(2 * Real.pi) * ‖g.val‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_assoc, hsq]; push_cast; ring
  change _ * Complex.exp (-2 * (Real.pi : ℂ) * e g.val * star (e g.val)) / _ * _ = _
  rw [he, ← Complex.ofReal_exp]
  have hr : (‖g.val‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr g.ne_zero)
  have hpow (b : ℂ) : ((‖g.val‖ ^ 2 : ℝ) : ℂ) ^ b = (‖g.val‖ : ℂ) ^ (2 * b) := by
    simpa using (Complex.cpow_mul_ofReal_nonneg (norm_nonneg g.val) 2 b).symm
  rw [hpow, hpow, show 2 * t = 2 * s + 2 * p.1 + (p.2.natAbs : ℂ) by dsimp [t]; ring]
  simp only [Complex.cpow_add _ _ hr, Complex.cpow_natCast]
  linear_combination ((Real.exp (-(2 * Real.pi) * ‖g.val‖ ^ 2) : ℂ) / (2 * (Real.pi : ℂ)) *
    (‖g.val‖ : ℂ) ^ (2*p.1) * (‖g.val‖ : ℂ) ^ (2*s)) * hangle

end

section
local notation "μ∞" => infiniteLocalMultiplicativeTamagawaMeasure F
local notation "μv" => finiteLocalMultiplicativeTamagawaMeasure F
local notation "O(" v ")" => (HeightOneSpectrum.adicCompletionIntegers F v)
attribute [local instance] instMeasurableSpaceUnitsAdicCompletionSec4
private local instance (v : V) : BorelSpace (v.adicCompletion F)ˣ := ⟨rfl⟩
private local instance (w : InfinitePlace F) : MeasurableSpace w.Completion := borel _

private theorem sAdeleSchwartz_pureTensor_of_global (S : Finset V) (fS : ℬ(SAdeleRing F S))
    (a : (w : InfinitePlace F) → ℬ(w.Completion)) (b : (v : V) → ℬ(v.adicCompletion F))
    (hb : ∀ v ∉ S, b v (Multiplicative.ofAdd 0) = 1)
    (hf : ∀ x : 𝔸[F], sAdeleSchwartzToGlobal F S fS (Multiplicative.ofAdd x) =
      (∏ w, a w (Multiplicative.ofAdd (x.1 w))) * ∏ᶠ v, b v (Multiplicative.ofAdd (x.2 v)))
    (x : SAdeleRing F S) : fS (Multiplicative.ofAdd x) =
      (∏ w, a w (Multiplicative.ofAdd (x.1 w))) * ∏ v : S, b v.val (Multiplicative.ofAdd (x.2 v)) := by
  classical
  let y (v : V) : v.adicCompletion F := if h : v ∈ S then x.2 ⟨v, h⟩ else 0
  have hy (v : V) (hv : v ∉ S) : y v ∈ v.adicCompletionIntegers F := by simp [y, hv]
  let z : 𝔸[F] := (x.1, ⟨y, S.eventually_cofinite_notMem.mono (fun v hv ↦ hy v hv)⟩)
  have hp : adeleProjection F S z = x := Prod.ext rfl (funext fun v ↦ dite_eq_left v.property)
  have hinside : ∀ v ∉ S, z.2 v ∈ v.adicCompletionIntegers F := hy
  have ht := ((sAdeleSchwartzToGlobal_apply F S fS z).trans (ite_eq_left hinside)).trans
    (congrArg (fun t ↦ fS (Multiplicative.ofAdd t)) hp)
  refine (ht.symm.trans (hf z)).trans (congrArg (_ * ·) ?_)
  change (∏ᶠ v, b v (Multiplicative.ofAdd (y v))) = _
  rw [finprod_eq_prod_of_mulSupport_subset (s := S) _ (mulSupport_subset_iff'.mpr fun v hv ↦ ?_),
    Finset.prod_subtype S (fun _ ↦ Iff.rfl)]
  · exact Finset.prod_congr rfl fun v _ ↦ congrArg (fun z ↦ b v.val (Multiplicative.ofAdd z)) (dite_eq_left v.property)
  · exact (congrArg (fun z ↦ b v (Multiplicative.ofAdd z)) (show y v = 0 from dite_eq_right hv)).trans (hb v hv)

private theorem unramifiedAt_iff_restriction (c : X) (v : V) :
    c.IsUnramifiedAt v ↔ unramified(v, (finitePlaceRestriction F v c)) := by
  rw [HeckeCharacter.isUnramifiedAt_iff]
  constructor
  · intro h g hg
    have ht := h ((O(v)).unitsEquivUnitsType ⟨g, hg⟩)
    change c.restrict v g.val = 1 at ht
    rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe] at ht
    exact ht
  · intro h u
    change c.restrict v (Units.map (O(v)).subtype.toMonoidHom u).val = 1
    rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
    exact h (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u) ⟨u.val.property, u.inv.property⟩

private theorem finitePlaceRestriction_twist_unit (χ : PontryaginDual C_F) (v : V)
    (g : (v.adicCompletion F)ˣ) (hg : g ∈ integerUnits(v)) (z : ℂ) :
    finitePlaceRestriction F v (ideleClassNormTwist χ z) g =
      (χ (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v g) : ℂ) := by
  change _ * (((ideleClassNorm F (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v g) : ℝ≥0) : ℝ) : ℂ) ^ z = _
  rw [ideleClassNorm_ofAdicCompletion]
  change _ * (‖(g : v.adicCompletion F)‖ : ℂ) ^ z = _
  rw [Valued.toNormedField.norm_eq_one_iff.mpr
    (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp hg),
    Complex.ofReal_one, Complex.one_cpow, mul_one]
  rfl

private theorem finiteGaussian_factor (v : V) (χ : PontryaginDual C_F) (s : ℂ) (hs : 1 < s.re) :
    let c₀ := finitePlaceRestriction F v (ideleClassNormTwist χ 0)
    let c := finitePlaceRestriction F v (ideleClassNormTwist χ s)
    localIdelicZetaIntegral (μv v) (fun y ↦ finiteStandardGaussian v c₀ (Multiplicative.ofAdd y)) c =
      ((μv v) integerUnits(v)).toReal * finiteHeckeEulerFactor χ v s := by
  classical
  let c₀ := finitePlaceRestriction F v (ideleClassNormTwist χ 0)
  let c := finitePlaceRestriction F v (ideleClassNormTwist χ s)
  by_cases hu : (ideleClassNormTwist χ 0).IsUnramifiedAt v
  · have hU := (unramifiedAt_iff_restriction _ _).mp hu
    have he (y : v.adicCompletion F) : finiteStandardGaussian v c₀ (Multiplicative.ofAdd y) =
        (O(v) : Set (v.adicCompletion F)).indicator (fun _ ↦ (1 : ℂ)) y := ite_eq_left hU
    exact (congrArg (fun f ↦ localIdelicZetaIntegral (μv v) f c) (funext he)).trans
      (localIntegerRingIntegral_eq_mass_mul_euler v χ s hs ((ideleClassNormTwist_unramified_iff χ s v).mpr hu))
  · have hU := mt (unramifiedAt_iff_restriction _ _).mpr hu
    have he (g : (v.adicCompletion F)ˣ) : finiteStandardGaussian v c₀ (Multiplicative.ofAdd g.val) * c g =
        (integerUnits(v) : Set (v.adicCompletion F)ˣ).indicator (fun _ ↦ (1 : ℂ)) g := by
      by_cases hg : g ∈ integerUnits(v)
      · rw [finiteStandardGaussian_integerUnit v c₀ g hg, indicator_of_mem hg]
        have ht : c g = c₀ g := (finitePlaceRestriction_twist_unit χ v g hg s).trans (finitePlaceRestriction_twist_unit χ v g hg 0).symm
        rw [ht, inv_mul_cancel₀ ((Group.isUnit g).map c₀).ne_zero]
      · have hv : g.val ∉ Units.val '' integerUnits(v) := by
          rintro ⟨u, hu, he⟩
          exact hg (Units.ext he ▸ hu)
        change finiteStandardGaussianValue v c₀ g.val * _ = _
        rw [finiteStandardGaussianValue, ite_eq_right hU, indicator_of_notMem hv, zero_mul, indicator_of_notMem hg]
    change (∫ g : (v.adicCompletion F)ˣ, finiteStandardGaussian v c₀ (Multiplicative.ofAdd g.val) * c g ∂μv v) = _
    simp_rw [he]
    have hopen : IsOpen (integerUnits(v) : Set (v.adicCompletion F)ˣ) := Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)
    rw [integral_indicator hopen.measurableSet, setIntegral_const]
    simp [measureReal_def, finiteHeckeEulerFactor, hu]


private theorem finiteGaussian_mass_prod (S : Finset V) (hm : ∀ v ∉ S, (μv v) integerUnits(v) = 1) :
    (∏ v ∈ S, (((μv v) integerUnits(v)).toReal : ℂ)) = ((Real.sqrt |(NumberField.discr F : ℝ)|)⁻¹ : ℝ) := by
  have hprod := finiteLocalTamagawaMass_finprod F
  have hm' : (∏ᶠ v : V, (μv v) integerUnits(v)) = _ :=
    finprod_eq_finsetProd_of_mulSupport_subset _ (mulSupport_subset_iff'.mpr hm)
  simp_rw [finiteLocalMultiplicativeTamagawaMeasure_integerUnits] at hm'
  rw [← Complex.ofReal_prod, ← ENNReal.toReal_prod]
  simp_rw [finiteLocalMultiplicativeTamagawaMeasure_integerUnits]
  rw [← hm', hprod, ENNReal.toReal_inv, ENNReal.toReal_ofReal (Real.sqrt_nonneg _), Nat.cast_natAbs, Int.cast_abs]


/-- Paper: Paragraph after Equation (3.4.3.9), p. 152. In the half-plane of
absolute convergence the Gaussian zeta function gives the completed Euler product of §3.2
scaled by the product of the finite integer-unit Tamagawa masses.
Deviation: The scale is the inverse square root of the absolute discriminant. -/
theorem gaussianCompletedHeckeL_eq_completedHeckeL (χ : PontryaginDual C_F) (s : ℂ)
    (hs : 1 < s.re) :
    gaussianCompletedHeckeL χ s =
      ((Real.sqrt |(NumberField.discr F : ℝ)|)⁻¹ : ℝ) * completedHeckeL χ ⟨s, hs⟩ := by
  classical
  let a (w : InfinitePlace F) := infiniteStandardGaussian w (infiniteUnitaryRestriction(χ,w))
  let b (v : V) := finiteStandardGaussian v (finitePlaceRestriction F v (ideleClassNormTwist χ 0))
  let c := ideleClassNormTwist χ s
  let M (v : V) := (μv v) integerUnits(v)
  obtain ⟨T, fT, hT⟩ := sAdeleSchwartzToGlobal_exhaustive F (adelicStandardGaussian χ)
  obtain ⟨R, hR⟩ : ∃ R : Finset V, c ∈ unramifiedOutside F R :=
    mem_iUnion.mp ((iUnion_unramifiedOutside F).symm ▸ mem_univ c)
  have hm : ∀ᶠ v : V in cofinite, M v = 1 := by
    simpa only [M, finiteLocalMultiplicativeTamagawaMeasure_integerUnits, eventually_cofinite] using finiteLocalTamagawaMass_finite F
  let S := T ∪ (R ∪ (eventually_cofinite.mp hm).toFinset)
  have hc : c ∈ unramifiedOutside F S := fun v hv ↦ hR v (fun h ↦ hv (Finset.mem_union_right _ (Finset.mem_union_left _ h)))
  have hM (v : V) (hv : v ∉ S) : M v = 1 := by
    by_contra hh
    exact hv (Finset.mem_union_right _ (Finset.mem_union_right _ ((eventually_cofinite.mp hm).mem_toFinset.mpr hh)))
  let fS := sAdeleSchwartzTransition F (show T ⊆ S from Finset.subset_union_left) fT
  have hglob : sAdeleSchwartzToGlobal F S fS = adelicStandardGaussian χ :=
    (LinearMap.congr_fun (sAdeleSchwartzToGlobal_comp F (show T ⊆ S from Finset.subset_union_left)) fT).trans hT
  have hb (v : V) (hv : v ∉ S) : b v (Multiplicative.ofAdd 0) = 1 := by
    have hU := (unramifiedAt_iff_restriction _ v).mp ((ideleClassNormTwist_unramified_iff χ s v).mp (hc v hv))
    exact (ite_eq_left hU).trans (indicator_of_mem (O(v)).zero_mem _)
  have hf := sAdeleSchwartz_pureTensor_of_global S fS a b hb (fun x ↦ by rw [hglob]; rfl)
  have hlocal := sLocalIntegral_pureTensor S fS a b hf c hc
  have hA : (∏ w, localIdelicZetaIntegral (μ∞ w) (fun y ↦ a w (Multiplicative.ofAdd y))
      (infinitePlaceRestriction F w c)) = heckeGammaFactor χ s := by
    apply Finset.prod_congr rfl
    intro w _
    split_ifs with hw
    · exact infiniteGaussian_real_factor w hw χ s (zero_lt_one.trans hs)
    · exact infiniteGaussian_complex_factor w (InfinitePlace.not_isReal_iff_isComplex.mp hw) χ s (zero_lt_one.trans hs)
  have hB (v : V) : localIdelicZetaIntegral (μv v) (fun y ↦ b v (Multiplicative.ofAdd y))
      (finitePlaceRestriction F v c) = (M v).toReal * finiteHeckeEulerFactor χ v s := finiteGaussian_factor v χ s hs
  rw [hA] at hlocal
  simp_rw [hB] at hlocal
  have hprod : _ = ∏ v : S, ((M v.val).toReal : ℂ) * finiteHeckeEulerFactor χ v.val s := Finset.prod_subtype S (fun _ ↦ Iff.rfl) (fun v : V ↦ ((M v).toReal : ℂ) * finiteHeckeEulerFactor χ v s)
  rw [← hprod, Finset.prod_mul_distrib, finiteGaussian_mass_prod S hM] at hlocal
  have hout : (∏ᶠ v : {v : V // v ∉ S}, ((M v.val).toReal : ℂ)) = 1 :=
    finprod_eq_one_of_forall_eq_one fun v ↦ by rw [hM v.val v.property, ENNReal.toReal_one, Complex.ofReal_one]
  have hne : (∏ v ∈ S, finiteHeckeEulerFactor χ v s) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun v _ ↦ finiteHeckeEulerFactor_ne_zero_of_one_lt χ v s hs
  rw [gaussianCompletedHeckeL_eq_integral χ s hs, ← hglob, weilIdentity_unramifiedOutside S fS χ s hs hc,
    hout, one_mul, hlocal, tprod_finiteHeckeEulerFactor_outside χ S s hs, Finset.prod_inv_distrib]
  change _ = _ * (heckeGammaFactor χ s * finiteHeckeL χ ⟨s, hs⟩)
  field_simp

end


-- TODO(paper-gap): At a finite place (3.4.3.13) needs the Tamagawa mass of the
-- integer units with the normalized tests in (3.4.3.10)–(3.4.3.11).

section
local notation "O(" v ")" => HeightOneSpectrum.adicCompletionIntegers F v
local notation "μ(" v ")" => finiteLocalMultiplicativeTamagawaMeasure F v
local notation "fn(" f ")" => fun y ↦ (f) (Multiplicative.ofAdd y)
attribute [local instance] instMeasurableSpaceUnitsAdicCompletionSec4

private theorem finiteTest_regular (v : V) (f : ℬ(v.adicCompletion F)) :
    IsLocallyConstant (fn(f) : v.adicCompletion F → ℂ) ∧ HasCompactSupport (fn(f) : v.adicCompletion F → ℂ) :=
  (mem_finitePlaceSchwartz_iff F v _).mp ⟨f, fun _ ↦ rfl⟩

private theorem finiteTest_unitSupport (v : V) (f : ℬ(v.adicCompletion F)) (hf : f (Multiplicative.ofAdd 0) = 0) :
    HasCompactSupport (fun g : (v.adicCompletion F)ˣ ↦ f (Multiplicative.ofAdd g.val)) := by
  let h : v.adicCompletion F → ℂ := fn(f)
  have hl := (finiteTest_regular v f).1
  have hc : IsCompact (support h) := by
    have hclosed : IsClosed (support h) := by
      change IsClosed (h ⁻¹' ({0} : Set ℂ)ᶜ)
      exact (hl.isClopen_fiber 0).compl.isClosed
    exact hclosed.closure_eq ▸ (finiteTest_regular v f).2
  have hunit : support h ⊆ range (Units.val : (v.adicCompletion F)ˣ → v.adicCompletion F) := by
    intro x hx
    exact isUnit_iff_ne_zero.mpr fun he ↦ hx (he ▸ hf)
  have he : IsCompact ((Units.val : (v.adicCompletion F)ˣ → v.adicCompletion F) ⁻¹' support h) := by
    apply Units.isEmbedding_val₀.isCompact_iff.mpr
    rwa [image_preimage_eq_of_subset hunit]
  exact he.closure

private theorem locallyConstant_unitTranslate {K : Type*} [NormedField K] [ProperSpace K]
    {k : K → ℂ} (hl : IsLocallyConstant k) (hc : HasCompactSupport k)
    (hU : ∀ᶠ g : Kˣ in 𝓝 1, ‖(↑g⁻¹ : K)‖ = 1) :
    IsLocallyConstant (fun g : Kˣ ↦ fun x : K ↦ k ((↑g⁻¹ : K) * x)) := by
  obtain ⟨R, hR⟩ := hc.exists_bound_of_continuousOn continuous_norm.continuousOn
  let C := Metric.closedBall (0 : K) R
  have hs (x : K) (hx : x ∉ C) : k x = 0 := by
    apply notMem_support.mp
    intro he
    exact hx (by simpa [C] using hR x (subset_tsupport k he))
  let good := {p : (K)ˣ × K | k ((↑p.1⁻¹ : K) * p.2) = k p.2}
  have ho : IsOpen good := by
    have h1 := hl.comp_continuous (show Continuous (fun p : (K)ˣ × K ↦ (↑p.1⁻¹ : K) * p.2) by fun_prop)
    convert (h1.comp₂ (hl.comp_continuous continuous_snd) (· - ·)).isOpen_fiber 0 using 1
    ext p
    exact sub_eq_zero.symm
  have hsub : {(1 : (K)ˣ)} ×ˢ C ⊆ good := by
    rintro ⟨g,x⟩ ⟨rfl, hx⟩
    simp [good]
  obtain ⟨N, W, hN, _, h1, hC, hNW⟩ := generalized_tube_lemma isCompact_singleton (isCompact_closedBall _ _) ho hsub
  have near : ∀ᶠ g : (K)ˣ in 𝓝 1, ∀ x, k ((↑g⁻¹ : K) * x) = k x := by
    filter_upwards [hN.mem_nhds (h1 (mem_singleton _)), hU] with g hg hu x
    by_cases hx : x ∈ C
    · exact hNW (show (g, x) ∈ N ×ˢ W from ⟨hg, hC hx⟩)
    · rw [hs x hx, hs _ (fun hh ↦ hx (by simpa only [C, Metric.mem_closedBall, dist_zero_right, norm_mul, hu, one_mul] using hh))]
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro g
  have ht : Tendsto (fun u : (K)ˣ ↦ g⁻¹ * u) (𝓝 g) (𝓝 1) := by
    have hh : Tendsto (fun u : (K)ˣ ↦ g⁻¹ * u) (𝓝 g) (𝓝 (g⁻¹ * g)) := (continuous_const_mul _).continuousAt
    simpa only [inv_mul_cancel] using hh
  filter_upwards [ht.eventually near] with u hu
  funext x
  have h := hu ((↑g⁻¹ : K) * x)
  simpa only [mul_inv_rev, inv_inv, Units.val_mul, mul_assoc, Units.mul_inv_cancel_left] using h

private theorem finiteTest_translate_locallyConstant (v : V) (f : ℬ(v.adicCompletion F)) :
    IsLocallyConstant (fun g : (v.adicCompletion F)ˣ ↦ schwartzBruhatUnitTranslate g f) := by
  let : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
  have hU : IsOpen ((O(v)).units : Set (v.adicCompletion F)ˣ) := Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)
  have hnear : ∀ᶠ g : (v.adicCompletion F)ˣ in 𝓝 1, g ∈ (O(v)).units := hU.mem_nhds (O(v)).units.one_mem
  have hl := locallyConstant_unitTranslate (finiteTest_regular v f).1 (finiteTest_regular v f).2
    (hnear.mono fun g hg ↦ Valued.toNormedField.norm_eq_one_iff.mpr
      (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp ((O(v)).units.inv_mem hg)))
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro g
  exact (hl.eventually_eq g).mono fun u hu ↦ Subtype.ext (funext fun x ↦ congrFun hu x.toAdd)

private theorem finiteTest_convolution (v : V) (f h : ℬ(v.adicCompletion F)) (hf : f (Multiplicative.ofAdd 0) = 0) :
    ∃ y : ℬ(v.adicCompletion F), ∀ L : ℬ(v.adicCompletion F) →ₗ[ℂ] ℂ,
      L y = ∫ g : (v.adicCompletion F)ˣ, f (Multiplicative.ofAdd g.val) * L (schwartzBruhatUnitTranslate g h) ∂μ(v) := by
  let : BorelSpace (v.adicCompletion F)ˣ := ⟨rfl⟩
  let : (μ(v)).IsHaarMeasure := finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure v
  let A (g : (v.adicCompletion F)ˣ) := f (Multiplicative.ofAdd g.val) • schwartzBruhatUnitTranslate g h
  have hl : IsLocallyConstant A := ((finiteTest_regular v f).1.comp_continuous Units.continuous_val).comp₂
    (finiteTest_translate_locallyConstant v h) (· • ·)
  have hc : HasCompactSupport A := HasCompactSupport.of_support_subset_isCompact (finiteTest_unitSupport v f hf) (fun g hg ↦
    subset_tsupport _ (show f (Multiplicative.ofAdd g.val) ≠ 0 from fun h0 ↦ hg (show A g = 0 by simp [A, h0])))
  exact (exists_algebraic_integral_of_locallyConstant (μ(v)) A hl hc).imp fun y hy L ↦
    (hy L).trans (integral_congr_ae (ae_of_all _ fun g ↦ L.map_smul _ _))

private theorem integral_swap_div {G : Type*} [CommGroup G] [MeasurableSpace G] [MeasurableMul G] [MeasurableInv G]
    (μ : Measure G) [μ.IsInvInvariant] [μ.IsMulLeftInvariant] (a b : G → ℂ) (u : G) :
    (∫ g, a g * b (u / g) ∂μ) = ∫ g, b g * a (u / g) ∂μ := by
  let k (g : G) := a g * b (u / g)
  refine (integral_div_left_eq_self k μ u).symm.trans (integral_congr_ae (ae_of_all _ fun g ↦ ?_))
  change a (u / g) * b (u / (u / g)) = _
  rw [div_div_cancel, mul_comm]

private theorem finiteTest_integral_swap (v : V) (f h : ℬ(v.adicCompletion F))
    (hf : f (Multiplicative.ofAdd 0) = 0) (hh : h (Multiplicative.ofAdd 0) = 0) (x : v.adicCompletion F) :
    (∫ g : (v.adicCompletion F)ˣ, f (Multiplicative.ofAdd g.val) * h (Multiplicative.ofAdd ((↑g⁻¹ : v.adicCompletion F) * x)) ∂μ(v)) =
      ∫ g : (v.adicCompletion F)ˣ, h (Multiplicative.ofAdd g.val) * f (Multiplicative.ofAdd ((↑g⁻¹ : v.adicCompletion F) * x)) ∂μ(v) := by
  let : BorelSpace (v.adicCompletion F)ˣ := ⟨rfl⟩
  let : (μ(v)).IsHaarMeasure := finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure v
  let : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
  let : LocallyCompactSpace (v.adicCompletion F)ˣ := (IsOpenUnits.isOpenEmbedding_unitsVal (M := v.adicCompletion F)).locallyCompactSpace
  let : (μ(v)).IsInvInvariant := by
    constructor
    unfold finiteLocalMultiplicativeTamagawaMeasure
    rw [Measure.inv_def, Measure.map_smul, Measure.map_inv_eq_self]
    exact measurable_inv.aemeasurable
  by_cases hx : x = 0
  · simp only [hx, mul_zero, hh, hf, integral_zero]
  · let u := Units.mk0 x hx
    have swap (g : (v.adicCompletion F)ˣ) : (↑g⁻¹ : v.adicCompletion F) * x = (u / g).val := mul_comm _ _
    simp_rw [swap]
    exact integral_swap_div (μ(v)) (fun g ↦ f (Multiplicative.ofAdd g.val)) (fun g ↦ h (Multiplicative.ofAdd g.val)) u

open scoped Classical
local notation "J(" v ")" => finiteStandardGaussian v (1 : QuasiCharacter (HeightOneSpectrum.adicCompletion F v)ˣ)
local notation "m(" v ")" => (((finiteLocalMultiplicativeTamagawaMeasure F v) (O(v)).units).toReal : ℂ)
local notation "ft(" χ "," v "," z ")" => quasiCharacterNormTwist (finiteNorm(v)) (continuous_finiteLocalModule v) ((circleToComplex).comp (χ)) z

private theorem integerGaussian_apply (v : V) (x : v.adicCompletion F) :
    J(v) (Multiplicative.ofAdd x) = (O(v) : Set (v.adicCompletion F)).indicator (fun _ ↦ (1 : ℂ)) x :=
  ite_eq_left (fun _ _ ↦ rfl)

private theorem integerGaussian_zero (v : V) : J(v) (Multiplicative.ofAdd 0) = 1 :=
  (integerGaussian_apply v 0).trans (indicator_of_mem (O(v)).zero_mem _)

private def removeFiniteConstant (v : V) : ℬ(v.adicCompletion F) →ₗ[ℂ] ℬ(v.adicCompletion F) :=
  LinearMap.id - (LinearMap.proj (Multiplicative.ofAdd 0) |>.comp (schwartzBruhatSubmodule _).subtype).smulRight (J(v))

private theorem removeFiniteConstant_zero (v : V) (f : ℬ(v.adicCompletion F)) :
    removeFiniteConstant v f (Multiplicative.ofAdd 0) = 0 := by
  change f (Multiplicative.ofAdd 0) - f (Multiplicative.ofAdd 0) * J(v) (Multiplicative.ofAdd 0) = 0
  rw [integerGaussian_zero, mul_one, sub_self]

private theorem truncatedFiniteZeta_integrable (v : V) (f : ℬ(v.adicCompletion F)) (c : QuasiCharacter (v.adicCompletion F)ˣ) :
    Integrable (fun g : (v.adicCompletion F)ˣ ↦ removeFiniteConstant v f (Multiplicative.ofAdd g.val) * c g) (μ(v)) := by
  let : BorelSpace (v.adicCompletion F)ˣ := ⟨rfl⟩
  let : (μ(v)).IsHaarMeasure := finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure v
  have hl := (finiteTest_regular v (removeFiniteConstant v f)).1.comp_continuous Units.continuous_val
  exact (hl.continuous.mul c.continuous).integrable_of_hasCompactSupport
    ((finiteTest_unitSupport v _ (removeFiniteConstant_zero v f)).mul_right (f' := (c : (v.adicCompletion F)ˣ → ℂ)))

private def truncatedFiniteZeta (v : V) (c : QuasiCharacter (v.adicCompletion F)ˣ) :
    ℬ(v.adicCompletion F) →ₗ[ℂ] ℂ where
  toFun f := localIdelicZetaIntegral (μ(v)) fn(removeFiniteConstant v f) c
  map_add' f h := by
    refine (integral_congr_ae (ae_of_all _ fun g ↦ ?_)).trans
      (integral_add (truncatedFiniteZeta_integrable v f c) (truncatedFiniteZeta_integrable v h c))
    exact (congrArg (fun k : ℬ(v.adicCompletion F) ↦ k (Multiplicative.ofAdd g.val) * c g)
      ((removeFiniteConstant v).map_add f h)).trans (add_mul _ _ _)
  map_smul' t f := by
    refine (integral_congr_ae (ae_of_all _ fun g ↦ ?_)).trans (integral_const_mul t _)
    exact (congrArg (fun k : ℬ(v.adicCompletion F) ↦ k (Multiplicative.ofAdd g.val) * c g)
      ((removeFiniteConstant v).map_smul t f)).trans (mul_assoc _ _ _)

private theorem truncatedFiniteZeta_analytic (v : V) (χ : PontryaginDual (v.adicCompletion F)ˣ) (f : ℬ(v.adicCompletion F)) :
    AnalyticOnNhd ℂ (fun z ↦ truncatedFiniteZeta v (ft(χ,v,z)) f) univ := by
  let k (g : (v.adicCompletion F)ˣ) := removeFiniteConstant v f (Multiplicative.ofAdd g.val) * (χ g : ℂ)
  let n (g : (v.adicCompletion F)ˣ) := ‖g.val‖
  let : BorelSpace (v.adicCompletion F)ˣ := ⟨rfl⟩
  have hI (z : ℂ) : Integrable (fun g ↦ k g * (n g : ℂ) ^ z) (μ(v)) := by
    apply (truncatedFiniteZeta_integrable v f (ft(χ,v,z))).congr
    filter_upwards with g
    exact (mul_assoc _ _ _).symm
  have h := analyticOnNhd_integral_mul_cpow_of_integrable (μ(v)) k n (continuous_norm.comp Units.continuous_val).measurable
    (fun g ↦ norm_pos_iff.mpr g.ne_zero) isOpen_univ (fun z _ ↦ hI z)
  have he (z : ℂ) : truncatedFiniteZeta v (ft(χ,v,z)) f = ∫ g, k g * (n g : ℂ) ^ z ∂μ(v) :=
    integral_congr_ae (ae_of_all _ fun _ ↦ (mul_assoc _ _ _).symm)
  rw [funext he]
  exact h

private def finiteEulerUniformizer (v : V) : (v.adicCompletion F)ˣ :=
  let h := (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
  Units.mk0 h.choose h.choose_spec.ne_zero

private theorem finiteEulerUniformizer_spec (v : V) :
    (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).IsUniformizer (finiteEulerUniformizer v).val :=
  (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial.choose_spec

private def finiteEulerDenominator (v : V) (c : QuasiCharacter (v.adicCompletion F)ˣ) : ℂ :=
  open Classical in
  if ∀ g ∈ (O(v)).units, c g = 1 then 1 - c (finiteEulerUniformizer v) else 1

private theorem finiteTwist_unit (v : V) (χ : PontryaginDual (v.adicCompletion F)ˣ) (z : ℂ)
    (g : (v.adicCompletion F)ˣ) (hg : g ∈ (O(v)).units) : ft(χ,v,z) g = (χ g : ℂ) := by
  change _ * (‖g.val‖ : ℂ) ^ z = _
  rw [Valued.toNormedField.norm_eq_one_iff.mpr
    (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp hg), Complex.ofReal_one, Complex.one_cpow, mul_one]
  rfl

private theorem finiteEulerDenominator_eq_inv (v : V) (c : QuasiCharacter (v.adicCompletion F)ˣ) :
    finiteEulerDenominator v c = (finiteLocalEulerFactor v c)⁻¹ := by
  classical
  let U := (O(v)).units
  have he : (∀ g ∈ U, c g = 1) ↔ ∀ u : (O(v))ˣ, c (Units.map (O(v)).subtype.toMonoidHom u) = 1 :=
    ⟨fun h u ↦ h _ ⟨u.val.property, u.inv.property⟩,
     fun h g hg ↦ h ((O(v)).unitsEquivUnitsType ⟨g,hg⟩)⟩
  by_cases h : ∀ g ∈ (O(v)).units, c g = 1
  · rw [finiteEulerDenominator, ite_eq_left h, finiteLocalEulerFactor, ite_eq_left (he.mp h), inv_inv]
    rfl
  · rw [finiteEulerDenominator, ite_eq_right h, finiteLocalEulerFactor, ite_eq_right (fun h' ↦ h (he.mpr h')), inv_one]


private theorem finiteEulerDenominator_analytic (v : V) (χ : PontryaginDual (v.adicCompletion F)ˣ) :
    AnalyticOnNhd ℂ (fun z ↦ finiteEulerDenominator v (ft(χ,v,z))) univ := by
  classical
  have hU (z : ℂ) : (∀ g ∈ (O(v)).units, ft(χ,v,z) g = 1) ↔ ∀ g ∈ (O(v)).units, (χ g : ℂ) = 1 :=
    forall_congr' fun g ↦ forall_congr' fun hg ↦ by rw [finiteTwist_unit v χ z g hg]
  simp only [finiteEulerDenominator, hU]
  split_ifs
  · let π := finiteEulerUniformizer v
    have hn : (‖π.val‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr π.ne_zero)
    change AnalyticOnNhd ℂ (fun z : ℂ ↦ 1 - (χ π : ℂ) * (‖π.val‖ : ℂ) ^ z) univ
    apply DifferentiableOn.analyticOnNhd _ isOpen_univ
    fun_prop (disch := simp [hn])
  · exact analyticOnNhd_const

private def finiteTestDual (v : V) (L : ℬ(v.adicCompletion F) →ₗ[ℂ] ℂ) : StrongDual ℂ ℬ(v.adicCompletion F) :=
  ⟨L, (congrArg (fun t ↦ @Continuous ℬ(v.adicCompletion F) ℂ t _ (fun f ↦ L f))
    (finitePlaceSchwartz_finestTopology F v)).mpr (continuous_of_finestLocallyConvex ℬ(v.adicCompletion F) L)⟩

private def finiteAdjustedLinear (v : V) (χ : PontryaginDual (v.adicCompletion F)ˣ) (z : ℂ) :
    ℬ(v.adicCompletion F) →ₗ[ℂ] ℂ :=
  let ev : ℬ(v.adicCompletion F) →ₗ[ℂ] ℂ :=
    (LinearMap.proj (Multiplicative.ofAdd (0 : v.adicCompletion F))).comp
      (schwartzBruhatSubmodule (Multiplicative (v.adicCompletion F))).subtype
  let A : ℂ := if ∀ g ∈ (O(v)).units, (χ g : ℂ) = 1 then 1 else 0
  let B : ℂ := finiteEulerDenominator v (ft(χ,v,z)) / m(v)
  A • ev + B • truncatedFiniteZeta v (ft(χ,v,z))

private def finiteAdjustedDistribution (v : V) (χ : PontryaginDual (v.adicCompletion F)ˣ) (z : ℂ) :
    StrongDual ℂ ℬ(v.adicCompletion F) :=
  finiteTestDual v (finiteAdjustedLinear v χ z)

private theorem finiteAdjustedDistribution_apply (v : V) (χ : PontryaginDual (v.adicCompletion F)ˣ) (z : ℂ)
    (f : ℬ(v.adicCompletion F)) :
    finiteAdjustedDistribution v χ z f =
      (if ∀ g ∈ (O(v)).units, (χ g : ℂ) = 1 then (1 : ℂ) else 0) * f (Multiplicative.ofAdd 0) +
        finiteEulerDenominator v (ft(χ,v,z)) / m(v) * truncatedFiniteZeta v (ft(χ,v,z)) f := rfl

private theorem finiteAdjustedDistribution_analytic (v : V) (χ : PontryaginDual (v.adicCompletion F)ˣ)
    (f : ℬ(v.adicCompletion F)) : AnalyticOnNhd ℂ (fun z ↦ finiteAdjustedDistribution v χ z f) univ := by
  let t : ℂ := (if ∀ g ∈ (O(v)).units, (χ g : ℂ) = 1 then (1 : ℂ) else 0) * f (Multiplicative.ofAdd 0)
  let d (z : ℂ) := finiteEulerDenominator v (ft(χ,v,z))
  let I (z : ℂ) := truncatedFiniteZeta v (ft(χ,v,z)) f
  have he (z : ℂ) : finiteAdjustedDistribution v χ z f = t + d z * (m(v))⁻¹ * I z :=
    (finiteAdjustedDistribution_apply v χ z f).trans (congrArg (fun q ↦ t + q * I z) (div_eq_mul_inv _ _))
  exact (congrArg (fun q : ℂ → ℂ ↦ AnalyticOnNhd ℂ q univ) (funext he)).mpr
    (analyticOnNhd_const.add (((finiteEulerDenominator_analytic v χ).mul analyticOnNhd_const).mul
      (truncatedFiniteZeta_analytic v χ f)))

private theorem sbDual_holomorphic_of_analytic_eval {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    (D : ℂ → StrongDual ℂ (SchwartzBruhat G)) (h : ∀ f, AnalyticOnNhd ℂ (fun z ↦ D z f) univ) :
    VectorHolomorphicOn D univ := by
  let E := StrongDual ℂ (SchwartzBruhat G)
  have : PolynormableSpace ℂ E := (schwartzBruhat_strongDual_nuclear.{0,_} (G := G)).2.1
  let : @CompleteSpace E (IsTopologicalAddGroup.rightUniformSpace E) := by
    rw [@IsUniformAddGroup.rightUniformSpace_eq E (inferInstance : UniformSpace E) _ _]
    exact schwartzBruhat_strongDual_complete
  apply WeaklyHolomorphicOn.vectorHolomorphicOn isOpen_univ isConnected_univ
  intro L
  refine (schwartzBruhat_reflexive (G := G)).elim fun e he ↦ ?_
  let f := e.symm L
  have hf (z : ℂ) : L (D z) = D z f :=
    (congrArg (fun M : StrongDual ℂ E ↦ M (D z)) (e.apply_symm_apply L).symm).trans (he f (D z))
  exact (congrArg (fun q : ℂ → ℂ ↦ DifferentiableOn ℂ q univ) (funext hf)).mpr ((h f).differentiableOn)

private theorem finiteAdjustedDistribution_holomorphic (v : V) (χ : PontryaginDual (v.adicCompletion F)ˣ) :
    VectorHolomorphicOn (finiteAdjustedDistribution v χ) univ := by
  let : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
  let : SecondCountableTopology (Multiplicative (v.adicCompletion F)) :=
    (inferInstance : SecondCountableTopology (v.adicCompletion F))
  let : LocallyCompactSpace (Multiplicative (v.adicCompletion F)) :=
    (inferInstance : LocallyCompactSpace (v.adicCompletion F))
  exact sbDual_holomorphic_of_analytic_eval (G := Multiplicative (v.adicCompletion F)) (finiteAdjustedDistribution v χ) (finiteAdjustedDistribution_analytic v χ)

private theorem finiteEulerMass_ne_zero (v : V) : m(v) ≠ 0 := by
  rw [finiteLocalMultiplicativeTamagawaMeasure_integerUnits, ENNReal.toReal_inv, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
  exact Complex.ofReal_ne_zero.mpr (inv_ne_zero (Real.sqrt_ne_zero'.mpr (pow_pos (Nat.cast_pos.mpr (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v))) _)))

private theorem integerGaussian_unitTranslate (v : V) (u : (v.adicCompletion F)ˣ)
    (hu : u ∈ (O(v)).units) : schwartzBruhatUnitTranslate u J(v) = J(v) := by
  apply Subtype.ext
  funext x
  change J(v) (Multiplicative.ofAdd ((↑u⁻¹ : v.adicCompletion F) * x.toAdd)) = J(v) (Multiplicative.ofAdd x.toAdd)
  refine (integerGaussian_apply v _).trans (Eq.trans ?_ (integerGaussian_apply v x.toAdd).symm)
  by_cases hx : x.toAdd ∈ O(v)
  · exact (indicator_of_mem ((O(v)).toSubring.mul_mem hu.2 hx) _).trans (indicator_of_mem hx (fun _ ↦ (1 : ℂ))).symm
  · have hx' : (↑u⁻¹ : v.adicCompletion F) * x.toAdd ∉ O(v) := fun h ↦ hx
        (by
          have hp : u.val * ((↑u⁻¹ : v.adicCompletion F) * x.toAdd) ∈ O(v) := (O(v)).toSubring.mul_mem hu.1 h
          rwa [Units.mul_inv_cancel_left] at hp)
    exact (indicator_of_notMem hx' _).trans (indicator_of_notMem hx (fun _ ↦ (1 : ℂ))).symm

private theorem zero_of_eq_scalar_mul {a x : ℂ} (ha : a ≠ 1) (h : x = a * x) : x = 0 := by
  have hm : (1 - a) * x = 0 := by rw [sub_mul, one_mul, ← h, sub_self]
  exact (mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr ha.symm)

private theorem finiteEigen_integerGaussian_zero (v : V) (c : QuasiCharacter (v.adicCompletion F)ˣ)
    (T : ℬ(v.adicCompletion F) → ℂ)
    (hT : ∀ (u : (v.adicCompletion F)ˣ) (f : ℬ(v.adicCompletion F)), T (schwartzBruhatUnitTranslate u f) = c u * T f)
    (hr : ¬∀ u ∈ (O(v)).units, c u = 1) : T J(v) = 0 := by
  classical
  have hn : ∃ u : (v.adicCompletion F)ˣ, ¬(u ∈ (O(v)).units → c u = 1) := not_forall.mp hr
  refine hn.elim fun u h ↦ ?_
  have hu : u ∈ (O(v)).units := (Classical.not_imp.mp h).1
  have hc : c u ≠ 1 := (Classical.not_imp.mp h).2
  have he : T J(v) = c u * T J(v) :=
    (congrArg T (integerGaussian_unitTranslate v u hu).symm).trans (hT u J(v))
  exact zero_of_eq_scalar_mul hc he

private theorem finiteTest_integral_eq_mass (v : V) (c : QuasiCharacter (v.adicCompletion F)ˣ)
    (k : ℬ(v.adicCompletion F)) (h : ∀ u : (v.adicCompletion F)ˣ, k (Multiplicative.ofAdd u.val) * c u =
      ((O(v)).units : Set (v.adicCompletion F)ˣ).indicator (fun _ ↦ (1 : ℂ)) u) :
    localIdelicZetaIntegral (μ(v)) fn(k) c = m(v) := by
  let : BorelSpace (v.adicCompletion F)ˣ := ⟨rfl⟩
  have hopen : IsOpen ((O(v)).units : Set (v.adicCompletion F)ˣ) := Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)
  refine (integral_congr_ae (ae_of_all _ h)).trans ?_
  rw [integral_indicator hopen.measurableSet, setIntegral_const]
  simp [measureReal_def]

private theorem unramifiedShell_integral (v : V) (c : QuasiCharacter (v.adicCompletion F)ˣ)
    (hu : ∀ u ∈ (O(v)).units, c u = 1) :
    localIdelicZetaIntegral (μ(v)) fn(J(v) - schwartzBruhatUnitTranslate (finiteEulerUniformizer v) J(v)) c = m(v) := by
  let π := finiteEulerUniformizer v
  let U := (O(v)).units
  have hk (x : v.adicCompletion F) :
      (J(v) - schwartzBruhatUnitTranslate π J(v) : ℬ(v.adicCompletion F)) (Multiplicative.ofAdd x) =
        (Units.val '' U).indicator (fun _ ↦ (1 : ℂ)) x := by
    change J(v) (Multiplicative.ofAdd x) - J(v) (Multiplicative.ofAdd ((↑π⁻¹ : v.adicCompletion F) * x)) = _
    exact (congrArg₂ (· - ·) (integerGaussian_apply v _) (integerGaussian_apply v _)).trans
      (congrFun (integerRing_difference_eq_integerUnits v π (finiteEulerUniformizer_spec v)) x)
  apply finiteTest_integral_eq_mass v c _
  intro u
  by_cases h : u ∈ U
  · exact (congrArg₂ (· * ·) ((hk _).trans (indicator_of_mem (mem_image_of_mem _ h) _)) (hu u h)).trans
      ((one_mul _).trans (indicator_of_mem h (fun _ ↦ (1 : ℂ))).symm)
  · have hv : u.val ∉ Units.val '' U := fun ⟨j, hj, he⟩ ↦ h ((congrArg (· ∈ U) (Units.ext he)).mp hj)
    exact (congrArg (· * c u) ((hk _).trans (indicator_of_notMem hv _))).trans
      ((zero_mul _).trans (indicator_of_notMem h _).symm)

private theorem ramifiedGaussian_integral (v : V) (c : QuasiCharacter (v.adicCompletion F)ˣ)
    (hu : ¬∀ u ∈ (O(v)).units, c u = 1) : localIdelicZetaIntegral (μ(v)) fn(finiteStandardGaussian v c) c = m(v) := by
  let U := (O(v)).units
  apply finiteTest_integral_eq_mass v c _
  intro u
  by_cases h : u ∈ U
  · exact (congrArg (· * c u) (finiteStandardGaussian_integerUnit v c u h)).trans
      ((inv_mul_cancel₀ ((Group.isUnit u).map c).ne_zero).trans (indicator_of_mem h (fun _ ↦ (1 : ℂ))).symm)
  · have hv : u.val ∉ Units.val '' U := fun ⟨j, hj, he⟩ ↦ h ((congrArg (· ∈ U) (Units.ext he)).mp hj)
    have he : finiteStandardGaussian v c (Multiplicative.ofAdd u.val) = 0 :=
      (ite_eq_right hu).trans (indicator_of_notMem hv _)
    exact (congrArg (· * c u) he).trans ((zero_mul _).trans (indicator_of_notMem h _).symm)

private theorem finiteEigen_shell (v : V) (c : QuasiCharacter (v.adicCompletion F)ˣ)
    (T : ℬ(v.adicCompletion F) → ℂ)
    (hsub : ∀ f h, T (f - h) = T f - T h)
    (hT : ∀ (u : (v.adicCompletion F)ˣ) (f : ℬ(v.adicCompletion F)), T (schwartzBruhatUnitTranslate u f) = c u * T f) :
    let G := finiteStandardGaussian v c
    let θ : ℂ := if ∀ u ∈ (O(v)).units, c u = 1 then 1 else 0
    ∃ h : ℬ(v.adicCompletion F), h (Multiplicative.ofAdd 0) = 0 ∧
      localIdelicZetaIntegral (μ(v)) fn(h) c = m(v) ∧
      T h = finiteEulerDenominator v c * T G ∧ T J(v) = θ * T G := by
  classical
  intro G θ
  let π := finiteEulerUniformizer v
  by_cases hu : ∀ u ∈ (O(v)).units, c u = 1
  · have hG : G = J(v) := Subtype.ext (funext fun x ↦ (ite_eq_left hu).trans (integerGaussian_apply v x.toAdd).symm)
    let k := J(v) - schwartzBruhatUnitTranslate π J(v)
    have h0 : k (Multiplicative.ofAdd 0) = 0 :=
      sub_eq_zero.mpr (congrArg (fun z ↦ J(v) (Multiplicative.ofAdd z)) (mul_zero (↑π⁻¹ : v.adicCompletion F)).symm)
    have hd : finiteEulerDenominator v c = 1 - c π := ite_eq_left hu
    have hv : θ = 1 := ite_eq_left hu
    have eG := congrArg T hG
    have e : T k = (1 - c π) * T J(v) :=
      (hsub _ _).trans ((congrArg (T J(v) - ·) (hT π J(v))).trans (by rw [sub_mul, one_mul]))
    exact ⟨k, h0, unramifiedShell_integral v c hu, e.trans (congrArg₂ (· * ·) hd.symm eG.symm),
      eG.symm.trans ((one_mul (T G)).symm.trans (congrArg (· * T G) hv.symm))⟩
  · have hz : (0 : v.adicCompletion F) ∉ Units.val '' (O(v)).units := fun ⟨g, _, hg⟩ ↦ g.ne_zero hg
    have hg : G (Multiplicative.ofAdd 0) = 0 := (ite_eq_right hu).trans (indicator_of_notMem hz _)
    have h0 := finiteEigen_integerGaussian_zero v c T hT hu
    have hd : finiteEulerDenominator v c = 1 := ite_eq_right hu
    have hv : θ = 0 := ite_eq_right hu
    exact ⟨G, hg, ramifiedGaussian_integral v c hu, ((congrArg (· * T G) hd).trans (one_mul _)).symm,
      h0.trans ((congrArg (· * T G) hv).trans (zero_mul _)).symm⟩

private theorem finiteGaussian_chart_const (v : V) (χ : PontryaginDual (v.adicCompletion F)ˣ) (z : ℂ) :
    finiteStandardGaussian v (ft(χ,v,z)) = finiteStandardGaussian v (ft(χ,v,0)) := by
  let c (t : ℂ) := ft(χ,v,t)
  have he (g : (v.adicCompletion F)ˣ) (hg : g ∈ (O(v)).units) : c z g = c 0 g :=
    (finiteTwist_unit v χ z g hg).trans (finiteTwist_unit v χ 0 g hg).symm
  have hu : (∀ g ∈ (O(v)).units, c z g = 1) ↔ ∀ g ∈ (O(v)).units, c 0 g = 1 :=
    forall_congr' fun g ↦ forall_congr' fun hg ↦ by rw [he g hg]
  apply Subtype.ext
  funext x
  by_cases hx : x.toAdd ∈ Units.val '' (O(v)).units
  · obtain ⟨g, hg, hx⟩ := hx
    change finiteStandardGaussian v (c z) (Multiplicative.ofAdd x.toAdd) = finiteStandardGaussian v (c 0) (Multiplicative.ofAdd x.toAdd)
    rw [← hx, finiteStandardGaussian_integerUnit v _ g hg, finiteStandardGaussian_integerUnit v _ g hg, he g hg]
  · change finiteStandardGaussianValue v (c z) x.toAdd = finiteStandardGaussianValue v (c 0) x.toAdd
    simp only [finiteStandardGaussianValue, hu, indicator_of_notMem hx]

private theorem finite_adjustment_of_cross {x g t I m d θ : ℂ} (hm : m ≠ 0)
    (h : I * (d * g) = m * (x - t * (θ * g))) : x = (θ * t + d / m * I) * g := by
  field_simp [hm]
  linear_combination -h

private def FiniteGaussianEvaluation : Prop :=
  ∀ (v : V) (χ : PontryaginDual (v.adicCompletion F)ˣ) (z : ℂ)
    (T : ℬ(v.adicCompletion F) →ₗ[ℂ] ℂ) (hT : ∀ (u : (v.adicCompletion F)ˣ) (k : ℬ(v.adicCompletion F)),
      T (schwartzBruhatUnitTranslate u k) = ft(χ,v,z) u * T k) (f : ℬ(v.adicCompletion F)),
    T f = finiteAdjustedDistribution v χ z f * T (finiteStandardGaussian v (ft(χ,v,z)))

private theorem finiteEigen_apply_eq : FiniteGaussianEvaluation (F := F) := by
  intro v χ z T hT f
  classical
  let c := ft(χ,v,z)
  let θ := if ∀ u ∈ (O(v)).units, (χ u : ℂ) = 1 then (1 : ℂ) else 0
  let G := finiteStandardGaussian v c
  let t := f (Multiplicative.ofAdd 0)
  have hu : (∀ u ∈ (O(v)).units, c u = 1) ↔ ∀ u ∈ (O(v)).units, (χ u : ℂ) = 1 :=
    forall_congr' fun u ↦ forall_congr' fun hu ↦ by rw [show c u = _ from finiteTwist_unit v χ z u hu]
  let L : ℬ(v.adicCompletion F) → ℂ := T.toFun
  have hs (f h : ℬ(v.adicCompletion F)) : L (f - h) = L f - L h := T.map_sub f h
  let f₀ := removeFiniteConstant v f
  have hf₀ : f₀ (Multiplicative.ofAdd 0) = 0 := removeFiniteConstant_zero v f
  have he := finiteEigen_shell v c L hs hT
  refine he.elim fun r h ↦ ?_
  have hR : L r = finiteEulerDenominator v c * L G := h.2.2.1
  have hθ : (if ∀ u ∈ (O(v)).units, c u = 1 then (1 : ℂ) else 0) = θ := if_congr hu rfl rfl
  have hJ : L J(v) = θ * L G := h.2.2.2.trans (congrArg (· * L G) hθ)
  have hsub : L (removeFiniteConstant v f) = L f - t * (θ * L G) :=
    (T.map_sub f (t • J(v))).trans (congrArg (L f - ·) ((T.map_smul t J(v)).trans (congrArg (t * ·) hJ)))
  have cross (k l : ℬ(v.adicCompletion F)) (hk : k (Multiplicative.ofAdd 0) = 0) (hl : l (Multiplicative.ofAdd 0) = 0) :
      localIdelicZetaIntegral (μ(v)) fn(k) c * L l = localIdelicZetaIntegral (μ(v)) fn(l) c * L k := by
    let ev (x : Multiplicative (v.adicCompletion F)) : ℬ(v.adicCompletion F) →ₗ[ℂ] ℂ :=
      (LinearMap.proj x).comp (schwartzBruhatSubmodule _).subtype
    refine (finiteTest_convolution v k l hk).elim fun a ha ↦ ?_
    refine (finiteTest_convolution v l k hl).elim fun b hb ↦ ?_
    have he (x : Multiplicative (v.adicCompletion F)) : a x = b x :=
      (ha (ev x)).trans ((finiteTest_integral_swap v k l hk hl x.toAdd).trans (hb (ev x)).symm)
    have hab : a = b := Subtype.ext (funext he)
    have hI (k l : ℬ(v.adicCompletion F)) :
        (∫ g : (v.adicCompletion F)ˣ, k (Multiplicative.ofAdd g.val) * T (schwartzBruhatUnitTranslate g l) ∂μ(v))
          = localIdelicZetaIntegral (μ(v)) fn(k) c * T l := by
      refine (integral_congr_ae (ae_of_all _ fun g ↦ ?_)).trans (integral_mul_const (T l)
        (fun g : (v.adicCompletion F)ˣ ↦ k (Multiplicative.ofAdd g.val) * c g))
      exact (congrArg (k (Multiplicative.ofAdd g.val) * ·) (hT g l)).trans (mul_assoc _ _ _).symm
    exact ((ha T).trans (hI k l)).symm.trans ((congrArg T hab).trans ((hb T).trans (hI l k)))
  have hx := cross f₀ r hf₀ h.1
  let I := truncatedFiniteZeta v c f
  have hc : I * (finiteEulerDenominator v c * L G) = m(v) * (L f - t * (θ * L G)) :=
    (congrArg (I * ·) hR.symm).trans (hx.trans (congrArg₂ (· * ·) h.2.1 hsub))
  exact (finite_adjustment_of_cross (finiteEulerMass_ne_zero v) hc).trans
    (congrArg (· * L G) (finiteAdjustedDistribution_apply v χ z f).symm)

private def finiteIntegralOnRight (v : V) (χ : PontryaginDual (v.adicCompletion F)ˣ) (z : ℂ) (hz : 0 < z.re) :
    StrongDual ℂ ℬ(v.adicCompletion F) := by
  let c := ft(χ,v,z)
  let L : ℬ(v.adicCompletion F) →ₗ[ℂ] ℂ :=
    { toFun := fun f ↦ localIdelicZetaIntegral (μ(v)) fn(f) c
      map_add' f h := by
        refine (integral_congr_ae (ae_of_all _ fun g ↦ ?_)).trans (integral_add
          (finiteLocalIdelicZetaIntegral_integrable v f χ hz) (finiteLocalIdelicZetaIntegral_integrable v h χ hz))
        exact add_mul _ _ _
      map_smul' t f := by
        refine (integral_congr_ae (ae_of_all _ fun g ↦ ?_)).trans (integral_const_mul t _)
        exact mul_assoc _ _ _ }
  exact finiteTestDual v L

private theorem finiteIntegralOnRight_eigen (v : V) (χ : PontryaginDual (v.adicCompletion F)ˣ) (z : ℂ) (hz : 0 < z.re) :
    finiteIntegralOnRight v χ z hz ∈ schwartzBruhatEigendistributions (ft(χ,v,z)) := by
  let c := ft(χ,v,z)
  let : BorelSpace (v.adicCompletion F)ˣ := ⟨rfl⟩
  let : (μ(v)).IsHaarMeasure := finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure v
  intro g f
  let b (u : (v.adicCompletion F)ˣ) := f (Multiplicative.ofAdd u.val) * c u
  change (∫ u : (v.adicCompletion F)ˣ,
    f (Multiplicative.ofAdd ((↑g⁻¹ : v.adicCompletion F) * u.val)) * c u ∂μ(v)) = c g * ∫ u, b u ∂μ(v)
  have he (u : (v.adicCompletion F)ˣ) : c g * c (g⁻¹ * u) = c u :=
    (c.map_mul g (g⁻¹ * u)).symm.trans (congrArg c (mul_inv_cancel_left g u))
  have e (u : (v.adicCompletion F)ˣ) : f (Multiplicative.ofAdd ((↑g⁻¹ : v.adicCompletion F) * u.val)) * c u =
      c g * b (g⁻¹ * u) :=
    (congrArg (f (Multiplicative.ofAdd (g⁻¹ * u).val) * ·) (he u).symm).trans (mul_left_comm _ _ _)
  exact (integral_congr_ae (ae_of_all _ e)).trans
    ((integral_const_mul (c g) _).trans (congrArg (c g * ·) (integral_mul_left_eq_self (μ := μ(v)) b (g⁻¹))))

private def FiniteGaussianOnRight : Prop :=
  ∀ (v : V) (χ : PontryaginDual (v.adicCompletion F)ˣ)
    (z : ℂ) (_hz : 0 < z.re),
    let c := ft(χ,v,z)
    let D := finiteAdjustedDistribution v χ z
    D ∈ schwartzBruhatEigendistributions c ∧ D (finiteStandardGaussian v c) = 1 ∧
      ∀ f : ℬ(v.adicCompletion F), localIdelicZetaIntegral (μ(v)) fn(f) c = m(v) * finiteLocalEulerFactor v c * D f

private theorem finiteAdjusted_on_right : FiniteGaussianOnRight (F := F) := by
  intro v χ z hz
  have cls := finiteEigen_apply_eq (F := F)
  let c := ft(χ,v,z)
  let D := finiteAdjustedDistribution v χ z
  let G := finiteStandardGaussian v c
  let I := finiteIntegralOnRight v χ z hz
  let d := finiteEulerDenominator v c
  have hi : I ∈ schwartzBruhatEigendistributions c := finiteIntegralOnRight_eigen v χ z hz
  let L : ℬ(v.adicCompletion F) → ℂ := I.toLinearMap.toFun
  have hs (f h : ℬ(v.adicCompletion F)) : L (f-h) = L f - L h := I.map_sub f h
  have hi' (u : (v.adicCompletion F)ˣ) (f : ℬ(v.adicCompletion F)) : L (schwartzBruhatUnitTranslate u f) = c u * L f := hi u f
  have eval (f : ℬ(v.adicCompletion F)) : I f = D f * I G := cls v χ z I.toLinearMap hi' f
  have shell := finiteEigen_shell v c L hs hi'
  refine shell.elim fun r h ↦ ?_
  have hm : m(v) = d * I G := h.2.1.symm.trans h.2.2.1
  have hprod : d * I G ≠ 0 := hm.symm.trans_ne (finiteEulerMass_ne_zero v)
  have hd := (mul_ne_zero_iff.mp hprod).1
  have hG := (mul_ne_zero_iff.mp hprod).2
  have hscale : I G = m(v) * finiteLocalEulerFactor v c := by
    calc I G = d⁻¹ * (d * I G) := (inv_mul_cancel_left₀ hd _).symm
         _ = m(v) * finiteLocalEulerFactor v c := by
           rw [← hm, mul_comm, show d⁻¹ = _ from (congrArg Inv.inv (finiteEulerDenominator_eq_inv v c)).trans (inv_inv _)]
  refine ⟨fun g f ↦ mul_right_cancel₀ hG ?_, mul_right_cancel₀ hG ((eval G).symm.trans (one_mul _).symm), fun f ↦ ?_⟩
  · exact (eval _).symm.trans ((hi g f).trans ((congrArg (c g * ·) (eval f)).trans (mul_assoc _ _ _).symm))
  · exact (eval f).trans ((mul_comm _ _).trans (congrArg (· * D f) hscale))

private theorem finiteEulerDenominator_ne_zero (v : V) (c : QuasiCharacter (v.adicCompletion F)ˣ) (hc : c ≠ 1) :
    finiteEulerDenominator v c ≠ 0 := by
  classical
  let π := finiteEulerUniformizer v
  let ι := Units.map (O(v)).subtype.toMonoidHom
  by_cases hU : ∀ u ∈ (O(v)).units, c u = 1
  · rw [finiteEulerDenominator, ite_eq_left hU]
    intro he
    have hπ : c π = 1 := (sub_eq_zero.mp he).symm
    obtain ⟨e, hep, heι⟩ := finitePlace_unitDecomposition v π
      (norm_uniformizer_adicCompletion v _ (finiteEulerUniformizer_spec v))
    apply hc
    ext u
    have hdec : u = π ^ (e u).1.toAdd * ι (e u).2 := by
      apply e.injective
      rw [map_mul, map_zpow, hep, heι]
      refine Prod.ext ?_ (by simp)
      change (e u).1.toAdd = (e u).1.toAdd * 1 + 0
      simp
    have hunit : ι (e u).2 ∈ (O(v)).units := ⟨(e u).2.val.property, (e u).2.inv.property⟩
    exact (congrArg c hdec).trans (by rw [map_mul, map_zpow, hπ, one_zpow, hU _ hunit, one_mul]; rfl)
  · rw [finiteEulerDenominator, ite_eq_right hU]
    exact one_ne_zero

private theorem entire_eq_of_eq_on_right {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f univ)
    (hg : AnalyticOnNhd ℂ g univ) (h : ∀ z : ℂ, 0 < z.re → f z = g z) (s : ℂ) : f s = g s := by
  have hnear : ∀ᶠ z : ℂ in 𝓝[≠] 2, 0 < z.re :=
    (Complex.continuous_re.continuousAt.eventually (lt_mem_nhds (by norm_num : 0 < (2 : ℂ).re))).filter_mono nhdsWithin_le_nhds
  exact hf.eqOn_of_preconnected_of_frequently_eq hg isPreconnected_univ (mem_univ 2)
    (hnear.mono h).frequently (mem_univ s)

private theorem finiteTwist_eval_analytic (v : V) (χ : PontryaginDual (v.adicCompletion F)ˣ) (g : (v.adicCompletion F)ˣ) :
    AnalyticOnNhd ℂ (fun z : ℂ ↦ ft(χ,v,z) g) univ := by
  change AnalyticOnNhd ℂ (fun z : ℂ ↦ (χ g : ℂ) * (‖g.val‖ : ℂ) ^ z) univ
  have hn : (‖g.val‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr g.ne_zero)
  apply DifferentiableOn.analyticOnNhd _ isOpen_univ
  fun_prop (disch := simp [hn])

private theorem finiteAdjusted_matches_zeta (v : V) (χ : PontryaginDual (v.adicCompletion F)ˣ)
    (s : ℂ) (hs : ft(χ,v,s) ≠ 1) (f : ℬ(v.adicCompletion F)) :
    finiteLocalIdelicZFunction v f (ft(χ,v,s)) = m(v) * finiteLocalEulerFactor v (ft(χ,v,s)) *
      finiteAdjustedDistribution v χ s f := by
  have right := finiteAdjusted_on_right (F := F)
  let Z (z : ℂ) := finiteLocalIdelicZFunction v f (ft(χ,v,z))
  let d (z : ℂ) := finiteEulerDenominator v (ft(χ,v,z))
  let ev (z : ℂ) := finiteAdjustedDistribution v χ z f
  let R (z : ℂ) := m(v) * (d z)⁻¹ * ev z
  have hZ : MeromorphicNFOn Z univ := ((finiteLocalIdelicZFunction_existsUnique v f).exists.choose_spec χ).1
  have hd : AnalyticOnNhd ℂ d univ := finiteEulerDenominator_analytic v χ
  have hev : AnalyticOnNhd ℂ ev univ := finiteAdjustedDistribution_analytic v χ f
  have hR : MeromorphicOn R univ := fun z hz ↦
    ((MeromorphicAt.const m(v) z).mul (hd z hz).meromorphicAt.inv).mul (hev z hz).meromorphicAt
  have factor (z : ℂ) : (d z)⁻¹ = finiteLocalEulerFactor v (ft(χ,v,z)) :=
    (congrArg Inv.inv (finiteEulerDenominator_eq_inv v _)).trans (inv_inv _)
  have he := meromorphic_eq_of_eq_on_right univ isPreconnected_univ (mem_univ _)
    hZ.meromorphicOn hR (fun z hz ↦ (finiteLocalIdelicZFunction_eq_integral v f χ (zero_lt_one.trans hz)).trans
      (((right v χ z (zero_lt_one.trans hz)).2.2 f).trans (congrArg (fun y ↦ m(v) * y * ev z) (factor z).symm)))
  have hnear : Z =ᶠ[𝓝[≠] s] R :=
    ((eventuallyEq_codiscreteWithin_iff_forall_eventually_nhdsNE.mp he) s (mem_univ s)).mono fun z h ↦ h (mem_univ z)
  have hRs : AnalyticAt ℂ R s :=
    (analyticAt_const.mul ((hd s (mem_univ s)).inv (finiteEulerDenominator_ne_zero v _ hs))).mul (hev s (mem_univ s))
  exact ((((hZ (mem_univ s)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds hRs.meromorphicNFAt).mp hnear).eq_of_nhds).trans
    (congrArg (fun y ↦ m(v) * y * ev s) (factor s))

end

/-- Paper: Theorem 3.4.3.3(1), p. 153. The holomorphic family at a finite place
is normalized on the integer-ring indicator in the unramified case and on the inverse
character supported on the integer units in the ramified case. Scaling by the Euler
factor and the unit mass gives the zeta function away from the trivial quasi-character.
Deviation: Equation (3.4.3.13) includes the integer-unit Tamagawa mass. -/
theorem finiteEigendistribution_normalized (v : V) (χ : PontryaginDual (v.adicCompletion F)ˣ) :
    let twist := quasiCharacterNormTwist (finiteNorm(v)) (continuous_finiteLocalModule v)
      ((circleToComplex).comp χ)
    ∃ D : ℂ → StrongDual ℂ ℬ(v.adicCompletion F), VectorHolomorphicOn D univ ∧
      (∀ s : ℂ, ∀ T : StrongDual ℂ ℬ(v.adicCompletion F),
        T = D s ↔ T ∈ schwartzBruhatEigendistributions (twist s) ∧
          T (finiteStandardGaussian v (twist s)) = 1) ∧
      ∀ s : ℂ, twist s ≠ 1 → ∀ f : ℬ(v.adicCompletion F),
        finiteLocalIdelicZFunction v f (twist s) =
          ((finiteLocalMultiplicativeTamagawaMeasure F v) integerUnits(v)).toReal *
            finiteLocalEulerFactor v (twist s) * D s f := by
  classical
  intro twist
  have right := finiteAdjusted_on_right (F := F)
  have cls := finiteEigen_apply_eq (F := F)
  let D := finiteAdjustedDistribution v χ
  refine ⟨D, finiteAdjustedDistribution_holomorphic v χ, ?_, fun s hs f ↦ finiteAdjusted_matches_zeta v χ s hs f⟩
  intro s T
  let G := finiteStandardGaussian v (twist 0)
  have norm (t : ℂ) (ht : 0 < t.re) : D t G = 1 :=
    (congrArg (D t) (finiteGaussian_chart_const v χ t).symm).trans (right v χ t ht).2.1
  have normAll : D s (finiteStandardGaussian v (twist s)) = 1 :=
    (congrArg (D s) (finiteGaussian_chart_const v χ s)).trans
      (entire_eq_of_eq_on_right (finiteAdjustedDistribution_analytic v χ G) analyticOnNhd_const norm s)
  constructor
  · rintro rfl
    refine ⟨fun g f ↦ ?_, normAll⟩
    exact entire_eq_of_eq_on_right (finiteAdjustedDistribution_analytic v χ (schwartzBruhatUnitTranslate g f))
      ((finiteTwist_eval_analytic v χ g).mul (finiteAdjustedDistribution_analytic v χ f))
      (fun t ht ↦ (right v χ t ht).1 g f) s
  · rintro ⟨he, hG⟩
    apply ContinuousLinearMap.ext
    intro f
    exact (cls v χ s T.toLinearMap (fun u k ↦ he u k) f).trans ((congrArg (D s f * ·) hG).trans (mul_one _))

section

private theorem exists_unitary_normTwist {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] (m : G →* ℝ≥0ˣ)
    (hm : IsProperMap m) (hne : ∃ g, m g ≠ 1) (c : QuasiCharacter G) :
    ∃ (χ : PontryaginDual G) (s : ℂ), quasiCharacterNormTwist m hm.continuous
      ((circleToComplex).comp χ) s = c := by
  let a := quasiCharacterAbscissa m hm hne c
  refine ⟨quasiCharacterPhase c, (a : ℂ), ContinuousMonoidHom.ext fun g ↦ ?_⟩
  change c g / (‖c g‖ : ℂ) * (((m g : ℝ≥0) : ℝ) : ℂ) ^ (a : ℂ) = c g
  rw [← Complex.ofReal_cpow (by positivity), ← norm_quasiCharacter_eq_rpow_abscissa m hm hne c,
    div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr ((Group.isUnit g).map c).ne_zero))]

private theorem rank_one_of_unique_normalization {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (W : Submodule ℂ (StrongDual ℂ E)) (f : E) (D : StrongDual ℂ E)
    (h : ∀ T : StrongDual ℂ E, T = D ↔ T ∈ W ∧ T f = 1) : Module.rank ℂ W = 1 := by
  have hD := (h D).mp rfl
  apply (rank_submodule_eq_one_iff W).mpr
  refine ⟨D, hD.1, fun h0 ↦ ?_, ?_⟩
  · simpa [h0] using hD.2
  · intro T hT
    let B := T + (1 - T f) • D
    have hB : B = D := (h B).mpr ⟨W.add_mem hT (W.smul_mem _ hD.1), by simp [B, hD.2]⟩
    apply Submodule.mem_span_singleton.mpr
    refine ⟨T f, ?_⟩
    change T + (1 - T f) • D = D at hB
    rw [sub_smul, one_smul] at hB
    calc T f • D = D - (D - (T f) • D) := by abel
         _ = T := eq_sub_of_add_eq hB |>.symm

end

/-- Paper: Theorem 3.4.3.3(1), pp. 152–153. At a finite place each
quasi-character has a one-dimensional eigendistribution space. -/
theorem finiteEigendistributions_rank (v : V) (c : QuasiCharacter (v.adicCompletion F)ˣ) :
    Module.rank ℂ (schwartzBruhatEigendistributions c) = 1 := by
  let : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
  have hp : IsProperMap (finiteNorm(v)) := by
    simpa only [pow_one] using (isProperMap_units_nnNorm_pow (K := v.adicCompletion F) 1 one_ne_zero)
  have hne : ∃ g, finiteNorm(v) g ≠ 1 := by
    let val : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
    obtain ⟨π, hπ⟩ := val.exists_isUniformizer_of_isCyclic_of_nontrivial
    let u := Units.mk0 (π : v.adicCompletion F) hπ.ne_zero
    refine ⟨u, fun he ↦ hπ.val_lt_one.ne ?_⟩
    apply Valued.toNormedField.norm_eq_one_iff.mp
    exact congrArg (fun t : ℝ≥0ˣ ↦ ((t : ℝ≥0) : ℝ)) he
  have hx : ∃ (χ : PontryaginDual (v.adicCompletion F)ˣ) (s : ℂ), quasiCharacterNormTwist (finiteNorm(v)) hp.continuous ((circleToComplex).comp χ) s = c := exists_unitary_normTwist (finiteNorm(v)) hp hne c
  refine hx.elim fun χ hχ ↦ hχ.elim fun s hs ↦ ?_
  exact (congrArg (fun d : QuasiCharacter (v.adicCompletion F)ˣ ↦ Module.rank ℂ (schwartzBruhatEigendistributions d)) hs.symm).trans
    (rank_one_of_unique_normalization _ _ ((finiteEigendistribution_normalized v χ).choose s)
      ((finiteEigendistribution_normalized v χ).choose_spec.2.1 s))

section InfiniteEigendistributionHelpers

open Bornology Filter Function MeasureTheory Set
open scoped NNReal Topology ContDiff ENNReal

private theorem abs_exp_sub_sum_le (t : ℝ) (M : ℕ) :
    ‖Real.exp t - ∑ k ∈ Finset.range M, t ^ k / (k.factorial : ℝ)‖ ≤
      |t| ^ M / (M.factorial : ℝ) * Real.exp |t| := by
  have hsum : HasSum (fun n : ℕ ↦ t ^ n / (n.factorial : ℝ)) (Real.exp t) := by
    simpa [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div, div_eq_mul_inv] using
      (NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) t)
  have hsplit := (hasSum_nat_add_iff' M).mpr hsum
  have hdiff : Real.exp t - ∑ k ∈ Finset.range M, t ^ k / (k.factorial : ℝ) =
      ∑' n : ℕ, t ^ (n + M) / ((n + M).factorial : ℝ) :=
    hsplit.tsum_eq.symm
  rw [hdiff]
  have hsum_abs : HasSum (fun n : ℕ ↦ |t| ^ n / (n.factorial : ℝ)) (Real.exp |t|) := by
    simpa [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div, div_eq_mul_inv] using
      (NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) |t|)
  have hdom : Summable (fun n : ℕ ↦ |t| ^ M / (M.factorial : ℝ) * (|t| ^ n / (n.factorial : ℝ))) :=
    hsum_abs.summable.mul_left _
  have hbound (n : ℕ) : ‖t ^ (n + M) / ((n + M).factorial : ℝ)‖ ≤
      |t| ^ M / (M.factorial : ℝ) * (|t| ^ n / (n.factorial : ℝ)) := by
    rw [Real.norm_eq_abs, abs_div, abs_pow, Nat.abs_cast]
    have hfac : (M.factorial : ℝ) * (n.factorial : ℝ) ≤ ((n + M).factorial : ℝ) := by
      have hmul : M.factorial * n.factorial ≤ (n + M).factorial := by
        calc
          M.factorial * n.factorial = 1 * (n.factorial * M.factorial) := by ring
          _ ≤ (n + M).choose M * n.factorial * M.factorial := by
            rw [mul_assoc]
            gcongr
            exact Nat.choose_pos (Nat.le_add_left M n)
          _ = (n + M).factorial := Nat.add_choose_mul_factorial_mul_factorial n M
      exact_mod_cast hmul
    rw [pow_add, mul_comm (|t| ^ n) (|t| ^ M), div_mul_div_comm]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hfac
  have hbound' (n : ℕ) : ‖‖t ^ (n + M) / ((n + M).factorial : ℝ)‖‖ ≤
      |t| ^ M / (M.factorial : ℝ) * (|t| ^ n / (n.factorial : ℝ)) := by
    simpa only [norm_norm] using hbound n
  calc
    ‖∑' n : ℕ, t ^ (n + M) / ((n + M).factorial : ℝ)‖ ≤
        ∑' n : ℕ, ‖t ^ (n + M) / ((n + M).factorial : ℝ)‖ :=
      norm_tsum_le_tsum_norm (hdom.of_norm_bounded hbound')
    _ ≤ ∑' n : ℕ, |t| ^ M / (M.factorial : ℝ) * (|t| ^ n / (n.factorial : ℝ)) :=
      (hdom.of_norm_bounded hbound').tsum_le_tsum hbound hdom
    _ = |t| ^ M / (M.factorial : ℝ) * Real.exp |t| := by
      rw [tsum_mul_left, hsum_abs.tsum_eq]

private theorem realSchwartzBruhat_surjective (w : InfinitePlace F) (hw : w.IsReal) :
    ∃ Φ : SchwartzMap ℝ ℂ →L[ℂ] SchwartzBruhat (Multiplicative w.Completion),
      Surjective Φ ∧
        ∀ (f : SchwartzMap ℝ ℂ) (x : w.Completion),
          Φ f (Multiplicative.ofAdd x) = f (InfinitePlace.Completion.ringEquivRealOfIsReal hw x) := by
  obtain ⟨E, hE⟩ := realSchwartzBruhat_equiv
  let j := InfinitePlace.Completion.isometryEquivRealOfIsReal hw
  let er : Multiplicative ℝ ≃ₜ* Multiplicative w.Completion :=
    { toMulEquiv := (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toAddEquiv.toMultiplicative
      continuous_toFun := j.symm.continuous
      continuous_invFun := j.continuous }
  obtain ⟨P, hP⟩ := exists_schwartzBruhat_comp_equivCLM er.symm
  obtain ⟨Q, hQ⟩ := exists_schwartzBruhat_comp_equivCLM er
  refine ⟨P.comp E.toContinuousLinearMap, fun g ↦ ?_, fun f x ↦ ?_⟩
  · refine ⟨E.symm (Q g), Subtype.ext (funext fun x ↦ ?_)⟩
    change P (E (E.symm (Q g))) x = g x
    rw [E.apply_symm_apply, hP, hQ, er.apply_symm_apply]
  · change P (E f) (Multiplicative.ofAdd x) = _
    rw [hP]
    exact hE f _

private theorem local_euclideanSchwartzMonomialPartial_eq {m : ℕ} (α β : Fin m → ℕ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ) (x : EuclideanSpace ℝ (Fin m)) :
    let directions := (List.finRange m).flatMap fun j ↦ List.replicate (β j) j
    euclideanSchwartzMonomialPartial α β f x =
      (∏ i, (x i : ℂ) ^ α i) *
        iteratedFDeriv ℝ directions.length f x
          (fun j ↦ EuclideanSpace.single (directions.get j) 1) := by
  intro directions
  unfold euclideanSchwartzMonomialPartial elementaryPartial
  congr 1
  let L : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 0) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
    ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin 0))
  let d : List (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 0)) :=
    (List.ofFn fun i : Fin m ↦ List.replicate (β i) (EuclideanSpace.single i 1, 0)).flatten
  let cd : List (EuclideanSpace ℝ (Fin m)) := directions.map (fun j ↦ EuclideanSpace.single j 1)
  have hzero : (List.ofFn fun i : Fin 0 ↦ List.replicate ((0 : Fin 0 → ℕ) i)
      ((0 : EuclideanSpace ℝ (Fin m)), EuclideanSpace.single i (1 : ℝ))).flatten = [] := rfl
  have hdirs : d ++ (List.ofFn fun i : Fin 0 ↦ List.replicate ((0 : Fin 0 → ℕ) i)
      ((0 : EuclideanSpace ℝ (Fin m)), EuclideanSpace.single i (1 : ℝ))).flatten = d := by
    rw [hzero, List.append_nil]
  have hfn : (fun v : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 0) ↦
      f (elementaryCover v (0 : Fin 0 → ℤ) PUnit.unit).1) =
      (f : EuclideanSpace ℝ (Fin m) → ℂ) ∘ L := rfl
  dsimp only
  rw [hdirs, hfn, L.iteratedFDeriv_comp_right (f.smooth ⊤) _ (by simp)]
  change iteratedFDeriv ℝ d.length f x (fun i ↦ L (d.get i)) = _
  have hd : d.map L = cd := by
    simp only [d, cd, directions, List.ofFn_eq_map]
    induction List.finRange m with
    | nil => simp
    | cons a l ih =>
      rw [List.map_cons, List.flatten_cons, List.map_append, List.flatMap_cons, List.map_append,
        ih]
      simp only [List.map_replicate, L]
      rfl
  have hcd_eq : iteratedFDeriv ℝ cd.length f x cd.get =
      iteratedFDeriv ℝ directions.length f x (fun j ↦ EuclideanSpace.single (directions.get j) 1) := by
    have hcd_get : cd.get =
        fun j : Fin cd.length ↦ EuclideanSpace.single (directions.get (j.cast (List.length_map _))) 1 := by
      funext j
      simp [cd, List.get_eq_getElem]
    rw [hcd_get]
    have hcast' {n k : ℕ} (h : n = k) (v : Fin k → EuclideanSpace ℝ (Fin m)) :
        iteratedFDeriv ℝ n f x (fun i ↦ v (i.cast h)) = iteratedFDeriv ℝ k f x v := by
      subst n
      rfl
    exact hcast' (List.length_map _) (fun j ↦ EuclideanSpace.single (directions.get j) 1)
  rw [← hcd_eq, ← hd]
  have hg : (d.map L).get = fun i ↦ L (d.get (i.cast (List.length_map L))) := by
    funext i
    simp [List.get_eq_getElem]
  rw [hg]
  have hcast {n k : ℕ} (h : n = k) (v : Fin k → EuclideanSpace ℝ (Fin m)) :
      iteratedFDeriv ℝ n f x (fun i ↦ v (i.cast h)) = iteratedFDeriv ℝ k f x v := by
    subst n
    rfl
  exact (hcast (List.length_map L) (fun i ↦ L (d.get i))).symm

private theorem complexSchwartzBruhat_surjective (w : InfinitePlace F) (hw : w.IsComplex) :
    ∃ Φ : SchwartzMap ℂ ℂ →L[ℂ] SchwartzBruhat (Multiplicative w.Completion),
      Surjective Φ ∧
        ∀ (f : SchwartzMap ℂ ℂ) (x : w.Completion),
          Φ f (Multiplicative.ofAdd x) = f (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw x) := by
  classical
  let m := Module.finrank ℝ ℂ
  let E := EuclideanSpace ℝ (Fin m)
  let L : ℂ ≃L[ℝ] E := ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  let C1 : SchwartzMap ℂ ℂ →L[ℂ] SchwartzMap E ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm
  let P := ElementaryLieGroup m 0 0 PUnit.{1}
  let D := (Fin 0 → AddCircle (1 : ℝ)) × (Fin 0 → ℤ) × PUnit.{1}
  let : Unique D := uniqueOfSubsingleton 0
  let p : Multiplicative E ≃ₜ* Multiplicative P :=
    { toMulEquiv := (AddEquiv.prodUnique (M := E) (N := D)).symm.toMultiplicative
      continuous_toFun := (continuous_id.prodMk continuous_const :
        Continuous (fun x : E ↦ (x, (default : D))))
      continuous_invFun := (continuous_fst : Continuous (Prod.fst : E × D → E)) }
  let e : ElementaryLCAPresentation (Multiplicative E) :=
    { realDim := m, torusDim := 0, latticeRank := 0, finiteFactor := PUnit.{1}, equiv := p }
  have hA := (lca_elementary_iff (G := Multiplicative E)).mpr ⟨e⟩
  let i : (⊤ : Subgroup (Multiplicative E)) ≃ₜ* Multiplicative E :=
    { Subgroup.topEquiv with
      continuous_toFun := continuous_subtype_val
      continuous_invFun := continuous_id.subtype_mk _ }
  let a : BruhatStructuralPair (Multiplicative E) := ⟨(⊤, OrderDual.toDual ⊥), by simp,
    isCompactlyGeneratedGroup_of_continuousMulEquiv i.symm hA.1,
    isBruhatGoodSubgroup_bot_iff.mpr hA.2, bot_le⟩
  let q₀ : Multiplicative E →* a.quotient := (QuotientGroup.mk' _).comp i.symm.toMulEquiv.toMonoidHom
  have hq₀ : IsOpenQuotientMap q₀ :=
    QuotientGroup.isOpenQuotientMap_mk.comp i.symm.toHomeomorph.isOpenQuotientMap
  have hinj : Injective q₀ := (MonoidHom.ker_eq_bot_iff q₀).mp (eq_bot_iff.mpr fun x hx ↦
    (a.quotient_mk_eq_one (i.symm x)).mp hx)
  let q := (MulEquiv.ofBijective q₀ ⟨hinj, hq₀.surjective⟩).toContinuousMulEquiv
    (fun _ ↦ hq₀.isQuotientMap.isOpen_preimage)
  let e₀ : ElementaryLCAPresentation a.quotient :=
    { realDim := m, torusDim := 0, latticeRank := 0, finiteFactor := PUnit.{1},
      finiteGroup := e.finiteGroup, finiteFintype := e.finiteFintype,
      finiteTopology := e.finiteTopology, finiteDiscrete := e.finiteDiscrete,
      equiv := q.symm.trans e.equiv }
  let A_lin : SchwartzMap E ℂ →ₗ[ℂ] ElementarySchwartz m 0 0 PUnit.{1} :=
    { toFun := fun f ↦ ⟨fun y ↦ f y.1, (elementarySchwartzSubmodule_real_iff _).mpr ⟨f, rfl⟩⟩
      map_add' := fun _ _ ↦ Subtype.ext rfl
      map_smul' := fun _ _ ↦ Subtype.ext rfl }
  have hA_cont : Continuous A_lin := by
    apply (withGeneratingSeminorms_spec _ _).continuous_of_continuous_comp A_lin
    intro idx
    let directions := (List.finRange m).flatMap fun j ↦ List.replicate (idx.2.1 j) j
    let q_semi : Seminorm ℂ (SchwartzMap E ℂ) :=
      SchwartzMap.seminorm ℂ (∑ k, idx.1 k) directions.length
    have hq_cont : Continuous q_semi :=
      (schwartz_withSeminorms ℂ E ℂ).continuous_seminorm (∑ k, idx.1 k, directions.length)
    refine Seminorm.continuous_of_le (p := (elementarySchwartzSeminorm idx).comp A_lin)
      (q := q_semi) hq_cont fun f ↦ ?_
    change (elementarySchwartzBound (A_lin f).val idx).toReal ≤ q_semi f
    rw [← ENNReal.ofReal_le_ofReal_iff (apply_nonneg q_semi f),
      ENNReal.ofReal_toReal ((A_lin f).property.2 idx).ne]
    refine iSup_le fun xt ↦ iSup_le fun aa ↦ iSup_le fun bb ↦ ?_
    obtain ⟨x, t⟩ := xt
    obtain rfl : t = 0 := Subsingleton.elim _ _
    obtain rfl : aa = 0 := Subsingleton.elim _ _
    cases bb
    have hpow0 : (∏ k : Fin 0, ((0 : Fin 0 → ℤ) k : ℂ) ^ idx.2.2.2 k) = 1 := by simp
    have hpart : elementaryPartial (A_lin f).val idx.2.1 idx.2.2.1 (x, 0) 0 PUnit.unit =
        elementaryPartial (fun g : ElementaryLieGroup m 0 0 PUnit.{1} ↦ f g.1) idx.2.1 0 (x, 0) 0 PUnit.unit := by
      have hz : idx.2.2.1 = 0 := Subsingleton.elim _ _
      rw [hz]
      rfl
    change (‖(∏ k : Fin m, (x k : ℂ) ^ idx.1 k) *
      (∏ k : Fin 0, ((0 : Fin 0 → ℤ) k : ℂ) ^ idx.2.2.2 k) *
      elementaryPartial (A_lin f).val idx.2.1 idx.2.2.1 (x, 0) 0 PUnit.unit‖₊ : ℝ≥0∞) ≤
      ENNReal.ofReal (q_semi f)
    rw [hpow0, mul_one, hpart]
    have hmp := local_euclideanSchwartzMonomialPartial_eq idx.1 idx.2.1 f x
    change (‖euclideanSchwartzMonomialPartial idx.1 idx.2.1 f x‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal (q_semi f)
    rw [hmp, ← ENNReal.ofReal_coe_nnreal]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [coe_nnNorm]
    have hnorm : ‖(∏ i, (x i : ℂ) ^ idx.1 i) *
        iteratedFDeriv ℝ directions.length f x (fun j ↦ EuclideanSpace.single (directions.get j) 1)‖ ≤
        ‖x‖ ^ (∑ k, idx.1 k) * ‖iteratedFDeriv ℝ directions.length f x‖ := by
      rw [norm_mul]
      refine mul_le_mul ?_ ?_ (norm_nonneg _) (by positivity)
      · rw [norm_prod]
        calc
          ∏ i, ‖(x i : ℂ) ^ idx.1 i‖ = ∏ i, ‖x i‖ ^ idx.1 i := by
            refine Finset.prod_congr rfl fun i _ ↦ ?_
            simp [Complex.norm_real]
          _ ≤ ∏ i, ‖x‖ ^ idx.1 i := by
            gcongr with i
            exact PiLp.norm_apply_le x i
          _ = ‖x‖ ^ (∑ k, idx.1 k) := by rw [Finset.prod_pow_eq_pow_sum]
      · refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
        have hunit : (∏ j : Fin directions.length, ‖EuclideanSpace.single (directions.get j) (1 : ℝ)‖) = 1 := by
          refine Finset.prod_eq_one fun j _ ↦ ?_
          rw [PiLp.norm_single, norm_one]
        rw [hunit, mul_one]
    exact hnorm.trans (SchwartzMap.le_seminorm ℂ (∑ k, idx.1 k) directions.length f x)
  let A_clm : SchwartzMap E ℂ →L[ℂ] SchwartzBruhatStage e₀ := ⟨A_lin, hA_cont⟩
  let J_clm : SchwartzBruhatStage e₀ →L[ℂ] SchwartzBruhat (Multiplicative E) :=
    ⟨schwartzBruhatStageInclusion a e₀,
      (withGeneratingSeminorms_spec _ Subtype.val).continuous_of_continuous_comp
        (schwartzBruhatStageInclusion a e₀) fun p ↦ p.2 a e₀⟩
  let j := InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw
  let ec : Multiplicative E ≃ₜ* Multiplicative w.Completion :=
    { toMulEquiv := ((L.symm.toLinearEquiv.toAddEquiv).trans
        (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm.toAddEquiv).toMultiplicative
      continuous_toFun := j.symm.continuous.comp L.symm.continuous
      continuous_invFun := L.continuous.comp j.continuous }
  obtain ⟨P_clm, hP⟩ := exists_schwartzBruhat_comp_equivCLM ec.symm
  let Φ : SchwartzMap ℂ ℂ →L[ℂ] SchwartzBruhat (Multiplicative w.Completion) :=
    P_clm.comp (J_clm.comp (A_clm.comp C1))
  have hq_inv : ∀ z, ((e₀.equiv (q z)).toAdd).1 = z.toAdd := fun z ↦ by
    change ((e.equiv (q.symm (q z))).toAdd).1 = _
    rw [q.symm_apply_apply]
    rfl
  refine ⟨Φ, ?_, ?_⟩
  · intro g
    let : T2Space (Multiplicative w.Completion) := ec.symm.toHomeomorph.isEmbedding.t2Space
    let g₀ : Multiplicative E → ℂ := fun x ↦ g (ec x)
    have hg₀ : g₀ ∈ schwartzBruhatSubmodule (Multiplicative E) :=
      schwartzBruhat_mem_comp_equiv ec g.property
    obtain ⟨s, hs⟩ := (mem_schwartzBruhatSubmodule_euclidean_iff
      (ContinuousMulEquiv.refl (Multiplicative E)) g₀).mp hg₀
    refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L s, Subtype.ext (funext fun x ↦ ?_)⟩
    change P_clm (J_clm (A_clm (C1 (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L s)))) x = g x
    rw [hP]
    change (schwartzBruhatStageInclusion a e₀ (A_clm (C1 _))).val (ec.symm x) = g x
    rw [schwartzBruhatStageInclusion_apply, schwartzBruhatStageRealization_apply,
      dite_eq_left (Subgroup.mem_top _)]
    change s (L (L.symm ((e₀.equiv (q (ec.symm x))).toAdd.1))) = g x
    rw [L.apply_symm_apply, hq_inv]
    exact (hs (ec.symm x)).trans (congrArg g (ec.apply_symm_apply x))
  · intro f x
    change P_clm (J_clm (A_clm (C1 f))) (Multiplicative.ofAdd x) = _
    rw [hP]
    change (schwartzBruhatStageInclusion a e₀ (A_clm (C1 f))).val (ec.symm (Multiplicative.ofAdd x)) = _
    rw [schwartzBruhatStageInclusion_apply, schwartzBruhatStageRealization_apply,
      dite_eq_left (Subgroup.mem_top _)]
    change f (L.symm ((e₀.equiv (q (ec.symm (Multiplicative.ofAdd x)))).toAdd.1)) = _
    rw [hq_inv]
    change f (L.symm (L (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw x))) = _
    rw [L.symm_apply_apply]

section Step2

private lemma one_add_pow_le {t : ℝ} (ht : 0 ≤ t) (m : ℕ) :
    (1 + t) ^ m ≤ 2 ^ m * (1 + t ^ m) := by
  rcases le_total t 1 with h1 | h1
  · calc
      (1 + t) ^ m ≤ 2 ^ m := pow_le_pow_left₀ (by positivity) (by linarith) m
      _ ≤ 2 ^ m * (1 + t ^ m) := le_mul_of_one_le_right (by positivity) (by linarith [pow_nonneg ht m])
  · calc
      (1 + t) ^ m ≤ (2 * t) ^ m := pow_le_pow_left₀ (by positivity) (by linarith) m
      _ = 2 ^ m * t ^ m := mul_pow 2 t m
      _ ≤ 2 ^ m * (1 + t ^ m) := by gcongr; linarith

private lemma iteratedDeriv_exp_neg_mul (h : ℝ) (k : ℕ) (u : ℝ) :
    iteratedDeriv k (fun y : ℝ ↦ Real.exp (-h * y)) u = (-h) ^ k * Real.exp (-h * u) := by
  induction k generalizing u with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ']
    have hderiv : deriv (fun y : ℝ ↦ Real.exp (-h * y)) =
        fun y : ℝ ↦ (-h) * Real.exp (-h * y) := by
      ext y
      have hd : HasDerivAt (fun y : ℝ ↦ Real.exp (-h * y)) (Real.exp (-h * y) * (-h)) y := by
        simpa using ((hasDerivAt_id y).const_mul (-h)).exp
      rw [hd.deriv, mul_comm]
    rw [hderiv, iteratedDeriv_const_mul_field, ih]
    ring

private lemma abs_exp_sub_one_le_of_nonpos {t : ℝ} (ht : t ≤ 0) :
    |Real.exp t - 1| ≤ |t| := by
  have h1 : Real.exp t ≤ 1 := Real.exp_le_one_iff.mpr ht
  have h2 : t + 1 ≤ Real.exp t := Real.add_one_le_exp t
  rw [abs_of_nonpos (sub_nonpos.mpr h1), abs_of_nonpos ht]
  linarith

private lemma abs_exp_sub_one_sub_id_le_of_nonpos {t : ℝ} (ht : t ≤ 0) :
    |Real.exp t - (1 + t)| ≤ t ^ 2 / 2 := by
  let g : ℝ → ℝ := fun y ↦ Real.exp y - (1 + y + y ^ 2 / 2)
  have hderiv : ∀ y : ℝ, HasDerivAt g (Real.exp y - 1 - y) y := fun y ↦ by
    have hsq : HasDerivAt (fun y : ℝ ↦ y ^ 2 / 2) y y := by
      simpa using (hasDerivAt_pow 2 y).div_const 2
    have hg : HasDerivAt (fun y : ℝ ↦ Real.exp y - (1 + y + y ^ 2 / 2))
        (Real.exp y - (0 + 1 + y)) y :=
      (Real.hasDerivAt_exp y).fun_sub
        (((hasDerivAt_const y (1 : ℝ)).fun_add (hasDerivAt_id y)).fun_add hsq)
    convert hg using 1
    ring
  have hmono : MonotoneOn g (Iic 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Iic 0)
      (fun y _ ↦ (hderiv y).continuousAt.continuousWithinAt)
      (fun y _ ↦ (hderiv y).differentiableAt.differentiableWithinAt) fun y _ ↦ ?_
    rw [(hderiv y).deriv]
    linarith [Real.add_one_le_exp y]
  have hgt : g t ≤ g 0 := hmono ht (mem_Iic.mpr le_rfl) ht
  have hg0 : g 0 = 0 := by simp [g]
  have hnonneg : 0 ≤ Real.exp t - (1 + t) := by linarith [Real.add_one_le_exp t]
  rw [abs_of_nonneg hnonneg]
  dsimp only [g] at hgt hg0
  linarith

private lemma gauss_diff_quot_bound {h : ℝ} (hh0 : 0 < h) (hh1 : h ≤ 1) (i : ℕ)
    {u : ℝ} (hu : 0 ≤ u) :
    ‖iteratedDeriv i (fun y : ℝ ↦ (Real.exp (-h * y) - 1) / h + y) u‖ ≤ h * (1 + u) ^ 2 := by
  let fh : ℝ → ℝ := fun y ↦ (Real.exp (-h * y) - 1) / h + y
  have hd1 : deriv fh = fun y ↦ 1 - Real.exp (-h * y) := by
    ext y
    have hid : HasDerivAt (fun x : ℝ ↦ x) 1 y := hasDerivAt_id y
    have h1 : HasDerivAt (fun y : ℝ ↦ Real.exp (-h * y)) (Real.exp (-h * y) * (-h)) y := by
      simpa using (hid.const_mul (-h)).exp
    have hd := ((h1.sub_const 1).div_const h).fun_add hid
    change deriv (fun y : ℝ ↦ (Real.exp (-h * y) - 1) / h + y) y = _
    rw [hd.deriv]
    field_simp [hh0.ne']
    ring
  match i with
  | 0 =>
    rw [iteratedDeriv_zero, Real.norm_eq_abs]
    have heq : (Real.exp (-h * u) - 1) / h + u = h⁻¹ * (Real.exp (-h * u) - (1 + (-h * u))) := by
      field_simp [hh0.ne']
      ring
    rw [heq, abs_mul, abs_inv, abs_of_pos hh0]
    have hnonpos : -h * u ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hh0.le) hu
    have hexp := abs_exp_sub_one_sub_id_le_of_nonpos hnonpos
    calc
      h⁻¹ * |Real.exp (-h * u) - (1 + (-h * u))|
          ≤ h⁻¹ * ((-h * u) ^ 2 / 2) := by gcongr
      _ = h * u ^ 2 / 2 := by field_simp [hh0.ne']
      _ ≤ h * (1 + u) ^ 2 := by
          have hu2 : u ^ 2 ≤ (1 + u) ^ 2 := pow_le_pow_left₀ hu (by linarith) 2
          nlinarith [hh0]
  | 1 =>
    rw [iteratedDeriv_one, hd1, Real.norm_eq_abs, abs_sub_comm]
    have hnonpos : -h * u ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hh0.le) hu
    have hexp := abs_exp_sub_one_le_of_nonpos hnonpos
    calc
      |Real.exp (-h * u) - 1| ≤ |-h * u| := hexp
      _ = h * u := by rw [abs_mul, abs_neg, abs_of_pos hh0, abs_of_nonneg hu]
      _ ≤ h * (1 + u) ^ 2 := by
          gcongr
          nlinarith
  | k + 2 =>
    rw [iteratedDeriv_succ', hd1, iteratedDeriv_succ']
    have hd2 : deriv (fun y : ℝ ↦ 1 - Real.exp (-h * y)) =
        fun y : ℝ ↦ h * Real.exp (-h * y) := by
      ext y
      have hd : HasDerivAt (fun y : ℝ ↦ 1 - Real.exp (-h * y)) (0 - Real.exp (-h * y) * (-h)) y := by
        simpa using (hasDerivAt_const y (1 : ℝ)).fun_sub (((hasDerivAt_id y).const_mul (-h)).exp)
      rw [hd.deriv]
      ring
    rw [hd2, iteratedDeriv_const_mul_field, iteratedDeriv_exp_neg_mul, Real.norm_eq_abs,
      abs_mul, abs_mul, abs_of_pos hh0, abs_pow, abs_neg, abs_of_pos hh0,
      abs_of_pos (Real.exp_pos _)]
    have hexp1 : Real.exp (-h * u) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have hpow1 : h ^ k ≤ 1 := pow_le_one₀ hh0.le hh1
    have hu1 : 1 ≤ (1 + u) ^ 2 := by nlinarith
    calc
      h * (h ^ k * Real.exp (-h * u)) ≤ h * (1 * 1) := by gcongr
      _ = h := by ring
      _ ≤ h * (1 + u) ^ 2 := le_mul_of_one_le_right hh0.le hu1

private theorem gauss_deriv_tendsto {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (b : ℝ) (hb : 0 < b) :
    Tendsto (fun h : ℝ ↦ if hh : 0 < h then
      (h⁻¹ : ℂ) • ((SchwartzMap.gaussian (b + h) (by linarith) -
        SchwartzMap.gaussian b hb).postcompCLM Complex.ofRealCLM) +
      SchwartzMap.smulLeftCLM ℂ (fun x : E ↦ (‖x‖ ^ 2 : ℂ))
        ((SchwartzMap.gaussian b hb).postcompCLM Complex.ofRealCLM)
      else 0) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  let gR : SchwartzMap E ℝ := SchwartzMap.gaussian b hb
  have hns : (fun x : E ↦ ‖x‖ ^ 2).HasTemperateGrowth :=
    Function.hasTemperateGrowth_norm_sq E
  let normSqR : SchwartzMap E ℝ →L[ℝ] SchwartzMap E ℝ :=
    SchwartzMap.smulLeftCLM ℝ (fun x : E ↦ ‖x‖ ^ 2)
  let F : ℝ → SchwartzMap E ℝ := fun h ↦ if hh : 0 < h then
    h⁻¹ • (SchwartzMap.gaussian (b + h) (by linarith) - gR) + normSqR gR else 0
  have hF_tendsto : Tendsto F (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    rw [(schwartz_withSeminorms ℝ E ℝ).tendsto_nhds _ 0]
    intro ⟨k, n⟩ ε hε
    simp only [sub_zero]
    -- Show SchwartzMap.seminorm ℝ k n (F h) ≤ h * C for h ∈ Ioo 0 1
    obtain ⟨j, C₀, hC₀⟩ := hns.norm_iteratedFDeriv_le_uniform n
    let D₀ : ℝ := max C₀ 0 + 1
    have hD₀ : 1 ≤ D₀ := by simp only [D₀, le_add_iff_nonneg_left]; exact le_max_right C₀ 0
    have hgauss_bd : ∀ (m i : ℕ), ∃ M : ℝ, 0 ≤ M ∧ ∀ x : E,
        (1 + ‖x‖) ^ m * ‖iteratedFDeriv ℝ i gR x‖ ≤ M := fun m i ↦ by
      let M := 2 ^ m * (SchwartzMap.seminorm ℝ 0 i gR + SchwartzMap.seminorm ℝ m i gR)
      refine ⟨M, by positivity, fun x ↦ ?_⟩
      calc
        (1 + ‖x‖) ^ m * ‖iteratedFDeriv ℝ i gR x‖
            ≤ 2 ^ m * (1 + ‖x‖ ^ m) * ‖iteratedFDeriv ℝ i gR x‖ := by
          gcongr
          exact one_add_pow_le (norm_nonneg x) m
        _ = 2 ^ m * (‖x‖ ^ 0 * ‖iteratedFDeriv ℝ i gR x‖ +
            ‖x‖ ^ m * ‖iteratedFDeriv ℝ i gR x‖) := by ring
        _ ≤ M := by
          dsimp only [M]
          gcongr
          · simpa using SchwartzMap.le_seminorm ℝ 0 i gR x
          · exact SchwartzMap.le_seminorm ℝ m i gR x
    choose M_fn hM_nn hM_bd using hgauss_bd
    let C : ℝ := ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
      ((n - i).factorial * D₀ ^ (n - i)) * (4 * M_fn (k + 4 + j * (n - i)) i)
    have hC_nn : 0 ≤ C := Finset.sum_nonneg fun i _ ↦ by
      have := hM_nn (k + 4 + j * (n - i)) i
      positivity
    have hbd_ev : ∀ᶠ h in nhdsWithin 0 (Ioi 0), SchwartzMap.seminorm ℝ k n (F h) ≤ h * C := by
      have hIoo : Ioo (0 : ℝ) 1 ∈ nhdsWithin (0 : ℝ) (Ioi 0) :=
        Ioo_mem_nhdsGT one_pos
      filter_upwards [hIoo] with h hh
      rcases hh with ⟨hh0, hh1⟩
      refine SchwartzMap.seminorm_le_bound ℝ k n (F h) (mul_nonneg hh0.le hC_nn) fun x ↦ ?_
      let fh : ℝ → ℝ := fun y ↦ (Real.exp (-h * y) - 1) / h + y
      have hfh_smooth : ContDiff ℝ (∞) fh := by
        have h1 : ContDiff ℝ (∞) (fun y : ℝ ↦ (Real.exp (-h * y) - 1) / h) :=
          (((Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).sub contDiff_const).div_const h)
        exact h1.add contDiff_id
      have hFun : ((F h : SchwartzMap E ℝ) : E → ℝ) =
          fun y ↦ gR y * fh (‖y‖ ^ 2) := by
        ext y
        simp only [F, dite_eq_left hh0, add_apply, smul_apply,
          sub_apply, normSqR, SchwartzMap.smulLeftCLM_apply_apply hns, gR,
          SchwartzMap.gaussian_apply, smul_eq_mul, fh]
        have hadd : -(b + h) * ‖y‖ ^ 2 = -b * ‖y‖ ^ 2 + -h * ‖y‖ ^ 2 := by ring
        rw [hadd, Real.exp_add]
        field_simp [hh0.ne']
      rw [hFun]
      have hleib := norm_iteratedFDeriv_mul_le (gR.smooth ⊤)
        (hfh_smooth.comp (hns.1.of_le (by simp))) x (n := n) (by simp)
      have hleib' : ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y ↦ gR y * fh (‖y‖ ^ 2)) x‖ ≤
          ‖x‖ ^ k * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i gR x‖ *
            ‖iteratedFDeriv ℝ (n - i) (fh ∘ fun y : E ↦ ‖y‖ ^ 2) x‖ :=
        mul_le_mul_of_nonneg_left hleib (by positivity)
      calc
        ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y ↦ gR y * fh (‖y‖ ^ 2)) x‖
            ≤ ‖x‖ ^ k * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
              ‖iteratedFDeriv ℝ i gR x‖ * ‖iteratedFDeriv ℝ (n - i) (fh ∘ fun y : E ↦ ‖y‖ ^ 2) x‖ :=
          hleib'
        _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
            (‖x‖ ^ k * ‖iteratedFDeriv ℝ i gR x‖ * ‖iteratedFDeriv ℝ (n - i) (fh ∘ fun y : E ↦ ‖y‖ ^ 2) x‖) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ ↦ by ring
        _ ≤ h * C := by
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun i hi ↦ ?_
          have hin : n - i ≤ n := Nat.sub_le n i
          have hcomp := norm_iteratedFDeriv_comp_le (𝕜 := ℝ) (n := n - i) (N := ∞)
            hfh_smooth (hns.1.of_le (by simp)) (by simp) x
            (C := h * (1 + ‖x‖ ^ 2) ^ 2) (D := D₀ * (1 + ‖x‖) ^ j)
            (fun r hr ↦ by
              rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
              exact gauss_diff_quot_bound hh0 hh1.le r (sq_nonneg ‖x‖))
            (fun r hr1 hrn ↦ by
              have hc : ‖iteratedFDeriv ℝ r (fun y : E ↦ ‖y‖ ^ 2) x‖ ≤ C₀ * (1 + ‖x‖) ^ j :=
                hC₀.2 r (hrn.trans hin) x
              have hc' : C₀ * (1 + ‖x‖) ^ j ≤ D₀ * (1 + ‖x‖) ^ j := by
                gcongr
                linarith [le_max_left C₀ 0]
              have hd1 : 1 ≤ D₀ * (1 + ‖x‖) ^ j := by
                have h1 : 1 ≤ (1 + ‖x‖) ^ j := one_le_pow₀ (by linarith [norm_nonneg x])
                exact one_le_mul_of_one_le_of_one_le hD₀ h1
              exact (hc.trans hc').trans (le_self_pow₀ hd1 (by omega)))
          have hxsq : (1 + ‖x‖ ^ 2) ^ 2 ≤ 4 * (1 + ‖x‖) ^ 4 := by
            have h1 : 1 + ‖x‖ ^ 2 ≤ 2 * (1 + ‖x‖) ^ 2 := by nlinarith [norm_nonneg x]
            calc
              (1 + ‖x‖ ^ 2) ^ 2 ≤ (2 * (1 + ‖x‖) ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
              _ = 4 * (1 + ‖x‖) ^ 4 := by ring
          have hxk : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k := pow_le_pow_left₀ (norm_nonneg x) (by linarith) k
          have hterm : ‖x‖ ^ k * ‖iteratedFDeriv ℝ i gR x‖ *
              ‖iteratedFDeriv ℝ (n - i) (fh ∘ fun y : E ↦ ‖y‖ ^ 2) x‖ ≤
              h * (((n - i).factorial * D₀ ^ (n - i)) * (4 * M_fn (k + 4 + j * (n - i)) i)) := by
            calc
              ‖x‖ ^ k * ‖iteratedFDeriv ℝ i gR x‖ *
                  ‖iteratedFDeriv ℝ (n - i) (fh ∘ fun y : E ↦ ‖y‖ ^ 2) x‖
                  ≤ (1 + ‖x‖) ^ k * ‖iteratedFDeriv ℝ i gR x‖ *
                    (((n - i).factorial : ℝ) * (h * (1 + ‖x‖ ^ 2) ^ 2) * (D₀ * (1 + ‖x‖) ^ j) ^ (n - i)) := by
                  gcongr
              _ ≤ (1 + ‖x‖) ^ k * ‖iteratedFDeriv ℝ i gR x‖ *
                    (((n - i).factorial : ℝ) * (h * (4 * (1 + ‖x‖) ^ 4)) * (D₀ * (1 + ‖x‖) ^ j) ^ (n - i)) := by
                  gcongr
              _ = h * (((n - i).factorial * D₀ ^ (n - i)) *
                    (4 * ((1 + ‖x‖) ^ (k + 4 + j * (n - i)) * ‖iteratedFDeriv ℝ i gR x‖))) := by
                  rw [mul_pow, ← pow_mul, pow_add, pow_add]
                  ring
              _ ≤ h * (((n - i).factorial * D₀ ^ (n - i)) * (4 * M_fn (k + 4 + j * (n - i)) i)) := by
                  gcongr
                  exact hM_bd (k + 4 + j * (n - i)) i x
          calc
            (n.choose i : ℝ) *
                (‖x‖ ^ k * ‖iteratedFDeriv ℝ i gR x‖ *
                  ‖iteratedFDeriv ℝ (n - i) (fh ∘ fun y : E ↦ ‖y‖ ^ 2) x‖)
                ≤ (n.choose i : ℝ) * (h * (((n - i).factorial * D₀ ^ (n - i)) *
                  (4 * M_fn (k + 4 + j * (n - i)) i))) := by gcongr
            _ = h * ((n.choose i : ℝ) * ((n - i).factorial * D₀ ^ (n - i)) *
                (4 * M_fn (k + 4 + j * (n - i)) i)) := by ring
    have hzero : Tendsto (fun h : ℝ ↦ h * C) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
      simpa using (continuous_id.mul_const C).tendsto 0 |>.mono_left nhdsWithin_le_nhds
    filter_upwards [hbd_ev, hzero.eventually (Iio_mem_nhds hε)] with h h1 h2
    exact lt_of_le_of_lt h1 h2
  let P_clm := SchwartzMap.postcompCLM Complex.ofRealCLM (E := E) (𝕜 := ℝ)
  have hP := P_clm.continuous.tendsto 0 |>.comp hF_tendsto
  rw [map_zero] at hP
  refine hP.congr fun h ↦ ?_
  by_cases hh : 0 < h
  · simp only [Function.comp_apply, F, dite_eq_left hh, map_add, map_smul, map_sub, P_clm]
    ext x
    have hnsC : (fun x : E ↦ (‖x‖ ^ 2 : ℂ)).HasTemperateGrowth := by
      simpa [Function.comp_def] using Complex.hasTemperateGrowth_ofReal.comp hns
    simp only [add_apply, smul_apply, SchwartzMap.postcompCLM_apply, Complex.ofRealCLM_apply,
      sub_apply, normSqR, SchwartzMap.smulLeftCLM_apply_apply hns, smul_eq_mul, Complex.real_smul,
      gR, SchwartzMap.gaussian_apply]
    change _ = _ + (SchwartzMap.smulLeftCLM ℂ (fun x : E ↦ (‖x‖ ^ 2 : ℂ))
      ((SchwartzMap.gaussian b hb).postcompCLM Complex.ofRealCLM)) x
    rw [SchwartzMap.smulLeftCLM_apply_apply hnsC]
    simp only [SchwartzMap.postcompCLM_apply, Complex.ofRealCLM_apply, SchwartzMap.gaussian_apply,
      smul_eq_mul]
    push_cast
    rfl
  · simp [F, hh]

private theorem schwartzDual_normSq_pow_mul_gauss_eq_zero {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (T : StrongDual ℂ (SchwartzMap E ℂ))
    {P : E → ℂ} (hP : P.HasTemperateGrowth)
    (hvan : ∀ (b : ℝ) (hb : 0 < b),
      T (SchwartzMap.smulLeftCLM ℂ P ((SchwartzMap.gaussian b hb).postcompCLM Complex.ofRealCLM)) = 0)
    (j : ℕ) (b : ℝ) (hb : 0 < b) :
    T (SchwartzMap.smulLeftCLM ℂ (fun x : E ↦ (‖x‖ ^ 2 : ℂ) ^ j * P x)
      ((SchwartzMap.gaussian b hb).postcompCLM Complex.ofRealCLM)) = 0 := by
  have hnsC : (fun x : E ↦ (‖x‖ ^ 2 : ℂ)).HasTemperateGrowth := by
    simpa [Function.comp_def] using
      Complex.hasTemperateGrowth_ofReal.comp (Function.hasTemperateGrowth_norm_sq E)
  induction j generalizing b with
  | zero =>
    simpa using hvan b hb
  | succ j ih =>
    let Q : E → ℂ := fun x : E ↦ (‖x‖ ^ 2 : ℂ) ^ j * P x
    have hQ : Q.HasTemperateGrowth := (hnsC.pow j).mul hP
    let MQ : SchwartzMap E ℂ →L[ℂ] SchwartzMap E ℂ := SchwartzMap.smulLeftCLM ℂ Q
    have hlim : Tendsto (fun h : ℝ ↦ T (MQ (if hh : 0 < h then
        (h⁻¹ : ℂ) • ((SchwartzMap.gaussian (b + h) (by linarith) -
          SchwartzMap.gaussian b hb).postcompCLM Complex.ofRealCLM) +
        SchwartzMap.smulLeftCLM ℂ (fun x : E ↦ (‖x‖ ^ 2 : ℂ))
          ((SchwartzMap.gaussian b hb).postcompCLM Complex.ofRealCLM)
        else 0))) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
      have hc : Continuous (fun f : SchwartzMap E ℂ ↦ T (MQ f)) :=
        T.continuous.comp MQ.continuous
      simpa [map_zero, Function.comp_def] using (hc.tendsto 0).comp (gauss_deriv_tendsto b hb)
    have hconst : Tendsto (fun _ : ℝ ↦
        T (SchwartzMap.smulLeftCLM ℂ (fun x : E ↦ (‖x‖ ^ 2 : ℂ) ^ (j + 1) * P x)
          ((SchwartzMap.gaussian b hb).postcompCLM Complex.ofRealCLM)))
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
      refine hlim.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
      have h1 : T (MQ ((SchwartzMap.gaussian (b + h) (by linarith)).postcompCLM Complex.ofRealCLM)) = 0 :=
        ih (b + h) (by linarith)
      have h2 : T (MQ ((SchwartzMap.gaussian b hb).postcompCLM Complex.ofRealCLM)) = 0 :=
        ih b hb
      simp only [dite_eq_left hh, map_add, map_smul, map_sub, h1, h2, sub_zero, smul_zero, zero_add]
      congr 1
      ext x
      have hQ_succ : (fun x : E ↦ (‖x‖ ^ 2 : ℂ) ^ (j + 1) * P x).HasTemperateGrowth :=
        (hnsC.pow (j + 1)).mul hP
      rw [SchwartzMap.smulLeftCLM_apply_apply hQ, SchwartzMap.smulLeftCLM_apply_apply hnsC,
        SchwartzMap.smulLeftCLM_apply_apply hQ_succ]
      simp only [Q, smul_eq_mul, pow_succ]
      ring
    exact tendsto_nhds_unique tendsto_const_nhds hconst

end Step2

section Step3a

private lemma exp_tail_deriv (N i : ℕ) :
    iteratedDeriv i (fun u : ℝ ↦ Real.exp u - ∑ k ∈ Finset.range N, u ^ k / (k.factorial : ℝ)) =
      fun u : ℝ ↦ Real.exp u - ∑ k ∈ Finset.range (N - i), u ^ k / (k.factorial : ℝ) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [iteratedDeriv_succ, ih]
    cases hM : N - i with
    | zero =>
      ext u
      simp [show N - (i + 1) = 0 by omega]
    | succ M =>
      ext u
      have hsum : HasDerivAt (fun y : ℝ ↦ ∑ k ∈ Finset.range (M + 1), y ^ k / (k.factorial : ℝ))
          (∑ k ∈ Finset.range M, u ^ k / (k.factorial : ℝ)) u := by
        have hd : ∀ k ∈ Finset.range (M + 1),
            HasDerivAt (fun y : ℝ ↦ y ^ k / (k.factorial : ℝ))
              (if k = 0 then 0 else u ^ (k - 1) / ((k - 1).factorial : ℝ)) u := by
          intro k _
          cases k with
          | zero => simp [hasDerivAt_const]
          | succ m =>
            simp only [Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]
            have h1 := (hasDerivAt_pow (m + 1) u).div_const (((m + 1).factorial : ℝ))
            convert h1 using 1
            rw [Nat.factorial_succ]
            push_cast
            field_simp [Nat.factorial_ne_zero m]
        convert HasDerivAt.fun_sum hd using 1
        rw [Finset.sum_range_succ']
        simp
      have hd_sub := (Real.hasDerivAt_exp u).fun_sub hsum
      have hsub : N - (i + 1) = M := by omega
      simpa [hsub] using hd_sub.deriv

private noncomputable def gaussianPolyC (c : ℝ) (m : ℕ) : ℝ :=
  2 ^ m * (1 + (1 + (m.factorial : ℝ) / c ^ m))

private lemma gaussianPolyC_nonneg {c : ℝ} (hc : 0 < c) (m : ℕ) : 0 ≤ gaussianPolyC c m := by
  unfold gaussianPolyC; positivity

private lemma gaussian_poly_bound (c : ℝ) (hc : 0 < c) (m : ℕ) :
    ∀ t : ℝ, 0 ≤ t → (1 + t) ^ m * Real.exp (-c * t ^ 2) ≤ gaussianPolyC c m := by
  have hexp : ∀ r : ℝ, 0 ≤ r → r ^ m * Real.exp (-c * r ^ 2) ≤ 1 + (m.factorial : ℝ) / c ^ m := by
    intro r hr
    rcases le_total r 1 with h1 | h1
    · calc
        r ^ m * Real.exp (-c * r ^ 2) ≤ 1 * 1 := by
          gcongr
          · exact pow_le_one₀ hr h1
          · exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg r])
        _ = 1 := mul_one 1
        _ ≤ 1 + (m.factorial : ℝ) / c ^ m := le_add_of_nonneg_right (by positivity)
    · have hp := Real.pow_div_factorial_le_exp (c * r ^ 2) (by positivity) m
      have hr2 : r ^ m ≤ r ^ (2 * m) := pow_le_pow_right₀ h1 (by omega)
      calc
        r ^ m * Real.exp (-c * r ^ 2) ≤ r ^ (2 * m) * Real.exp (-c * r ^ 2) := by gcongr
        _ = ((c * r ^ 2) ^ m / (m.factorial : ℝ)) * ((m.factorial : ℝ) / c ^ m) * Real.exp (-c * r ^ 2) := by
          rw [mul_pow, ← pow_mul, mul_comm 2 m]
          field_simp [hc.ne', Nat.factorial_ne_zero m]
        _ ≤ Real.exp (c * r ^ 2) * ((m.factorial : ℝ) / c ^ m) * Real.exp (-c * r ^ 2) := by gcongr
        _ = (m.factorial : ℝ) / c ^ m := by
          rw [mul_right_comm, ← Real.exp_add]
          simp
        _ ≤ 1 + (m.factorial : ℝ) / c ^ m := le_add_of_nonneg_left zero_le_one
  intro t ht
  unfold gaussianPolyC
  calc
    (1 + t) ^ m * Real.exp (-c * t ^ 2) ≤ 2 ^ m * (1 + t ^ m) * Real.exp (-c * t ^ 2) := by
      gcongr; exact one_add_pow_le ht m
    _ = 2 ^ m * (1 * Real.exp (-c * t ^ 2) + t ^ m * Real.exp (-c * t ^ 2)) := by ring
    _ ≤ 2 ^ m * (1 * 1 + (1 + (m.factorial : ℝ) / c ^ m)) := by
      gcongr
      · exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg t])
      · exact hexp t ht
    _ = 2 ^ m * (1 + (1 + (m.factorial : ℝ) / c ^ m)) := by ring

private lemma pow_div_factorial_mul_exp_neg_sq_le (A c : ℝ) (hA : 0 ≤ A) (hc : 0 < c)
    (M : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (A * t) ^ M / (M.factorial : ℝ) * Real.exp (-c * t ^ 2) ≤
      (1 + t) * max A 1 * ((max A 1 ^ 2 / c) ^ (M / 2) / ((M / 2).factorial : ℝ)) := by
  let p := M / 2
  let r := M % 2
  have hM : M = 2 * p + r := by omega
  have hr : r ≤ 1 := Nat.lt_succ_iff.mp (Nat.mod_lt M two_pos)
  have hfac_p : p.factorial * p.factorial ≤ (2 * p).factorial := by
    calc
      p.factorial * p.factorial = 1 * (p.factorial * p.factorial) := by ring
      _ ≤ (2 * p).choose p * (p.factorial * p.factorial) := by
        gcongr; exact Nat.choose_pos (by omega)
      _ = (2 * p).factorial := by
        have h := Nat.add_choose_mul_factorial_mul_factorial p p
        rw [two_mul, ← mul_assoc]
        exact h
  have hfac : p.factorial * p.factorial ≤ M.factorial :=
    hfac_p.trans (Nat.factorial_le (by omega))
  have hfac_real : (p.factorial : ℝ) * (p.factorial : ℝ) ≤ (M.factorial : ℝ) := by
    exact_mod_cast hfac
  have ht_r : t ^ r ≤ 1 + t := by
    interval_cases r
    · simp; linarith
    · simp
  have hA_M : A ^ M ≤ max A 1 ^ (2 * p + 1) := by
    calc
      A ^ M ≤ max A 1 ^ M := pow_le_pow_left₀ hA (le_max_left A 1) M
      _ ≤ max A 1 ^ (2 * p + 1) := pow_le_pow_right₀ (le_max_right A 1) (by omega)
  have hexp_p := Real.pow_div_factorial_le_exp (c * t ^ 2) (by positivity) p
  calc
    (A * t) ^ M / (M.factorial : ℝ) * Real.exp (-c * t ^ 2)
        = A ^ M * (t ^ r * t ^ (2 * p)) / (M.factorial : ℝ) * Real.exp (-c * t ^ 2) := by
      rw [mul_pow, hM, pow_add]; ring
    _ ≤ max A 1 ^ (2 * p + 1) * ((1 + t) * t ^ (2 * p)) /
          ((p.factorial : ℝ) * (p.factorial : ℝ)) * Real.exp (-c * t ^ 2) := by
      gcongr
    _ = (1 + t) * max A 1 * ((max A 1 ^ 2 / c) ^ p / (p.factorial : ℝ)) *
          (((c * t ^ 2) ^ p / (p.factorial : ℝ)) * Real.exp (-c * t ^ 2)) := by
      rw [pow_succ, mul_pow, div_pow]
      have hp2 : t ^ (2 * p) = (t ^ 2) ^ p := by rw [← pow_mul, mul_comm]
      have hA2 : max A 1 ^ (2 * p) = (max A 1 ^ 2) ^ p := by rw [← pow_mul]
      rw [hp2, hA2]
      field_simp [hc.ne', Nat.factorial_ne_zero p]
    _ ≤ (1 + t) * max A 1 * ((max A 1 ^ 2 / c) ^ p / (p.factorial : ℝ)) *
          (Real.exp (c * t ^ 2) * Real.exp (-c * t ^ 2)) := by gcongr
    _ = (1 + t) * max A 1 * ((max A 1 ^ 2 / c) ^ (M / 2) / ((M / 2).factorial : ℝ)) := by
      rw [← Real.exp_add]
      simp [p]

private lemma gauss_taylor_pointwise_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (b : ℝ) (hb : 0 < b) (y : E)
    (k n N i j : ℕ) (C₀ D₀ : ℝ) (hD₀ : 1 ≤ D₀)
    (hC₀ : ∀ r ≤ n, ∀ x : E, ‖iteratedFDeriv ℝ r (fun z : E ↦ ‖z‖ ^ 2) x‖ ≤ C₀ * (1 + ‖x‖) ^ j)
    (hD_bd : b * max C₀ 0 + 1 ≤ D₀)
    (hin : i ≤ n) (hN : n ≤ N) (x : E) :
    let L : E →L[ℝ] ℝ := (2 * b) • innerSL ℝ y
    let RN : ℝ → ℝ := fun u ↦ Real.exp u - ∑ m ∈ Finset.range N, u ^ m / (m.factorial : ℝ)
    let c : ℝ := b / 4
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ i (fun z : E ↦ Real.exp (-b * ‖z‖ ^ 2)) x‖ *
        ‖iteratedFDeriv ℝ (n - i) (RN ∘ L) x‖ ≤
      (i.factorial * D₀ ^ i * max ‖L‖ 1 ^ (2 * n) * Real.exp (‖L‖ ^ 2 / (8 * c)) * max ‖L‖ 1 *
        gaussianPolyC c (k + 1 + j * i + n)) *
      ((max ‖L‖ 1 ^ 2 / c) ^ ((N - n) / 2) / (((N - n) / 2).factorial : ℝ)) := by
  intro L RN c
  have hc : 0 < c := by positivity
  have hns : (fun z : E ↦ ‖z‖ ^ 2).HasTemperateGrowth :=
    Function.hasTemperateGrowth_norm_sq E
  have hRN_smooth : ContDiff ℝ (∞) RN :=
    Real.contDiff_exp.sub (ContDiff.sum fun m _ ↦ (contDiff_id.pow m).div_const _)
  have hcomp_exp : ‖iteratedFDeriv ℝ i (fun z : E ↦ Real.exp (-b * ‖z‖ ^ 2)) x‖ ≤
      i.factorial * Real.exp (-b * ‖x‖ ^ 2) * (D₀ * (1 + ‖x‖) ^ j) ^ i := by
    refine norm_iteratedFDeriv_comp_le (𝕜 := ℝ) (n := i) (N := ∞)
      Real.contDiff_exp (contDiff_const.mul (hns.1.of_le (by simp))) (by simp) x
      (C := Real.exp (-b * ‖x‖ ^ 2)) (D := D₀ * (1 + ‖x‖) ^ j)
      (fun r _ ↦ by
        rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate,
          Real.iter_deriv_exp, Real.norm_of_nonneg (Real.exp_pos _).le])
      (fun r hr1 hri ↦ ?_)
    have hsmul : iteratedFDeriv ℝ r (fun z : E ↦ (-b) * ‖z‖ ^ 2) x =
        (-b) • iteratedFDeriv ℝ r (fun z : E ↦ ‖z‖ ^ 2) x := by
      change iteratedFDeriv ℝ r ((-b) • fun z : E ↦ ‖z‖ ^ 2) x = _
      rw [iteratedFDeriv_const_smul_apply (hns.1.of_le (by simp) |>.contDiffAt)]
    have hnr : ‖iteratedFDeriv ℝ r (fun z : E ↦ (-b) * ‖z‖ ^ 2) x‖ ≤ D₀ * (1 + ‖x‖) ^ j := by
      rw [hsmul, norm_smul, norm_neg, Real.norm_of_nonneg hb.le]
      have hc0 := hC₀ r (hri.trans hin) x
      have h1 : b * ‖iteratedFDeriv ℝ r (fun z : E ↦ ‖z‖ ^ 2) x‖ ≤ b * (C₀ * (1 + ‖x‖) ^ j) :=
        mul_le_mul_of_nonneg_left hc0 hb.le
      have h2 : b * (C₀ * (1 + ‖x‖) ^ j) ≤ b * (max C₀ 0 * (1 + ‖x‖) ^ j) := by
        gcongr; exact le_max_left C₀ 0
      have h3 : b * (max C₀ 0 * (1 + ‖x‖) ^ j) ≤ (b * max C₀ 0 + 1) * (1 + ‖x‖) ^ j := by
        have : 0 ≤ (1 + ‖x‖) ^ j := by positivity
        nlinarith
      exact h1.trans (h2.trans (h3.trans (mul_le_mul_of_nonneg_right hD_bd (by positivity))))
    have hd1 : 1 ≤ D₀ * (1 + ‖x‖) ^ j :=
      one_le_mul_of_one_le_of_one_le hD₀ (one_le_pow₀ (by linarith [norm_nonneg x]))
    exact hnr.trans (le_self_pow₀ hd1 (by omega))
  have hcomp_RN : ‖iteratedFDeriv ℝ (n - i) (RN ∘ L) x‖ ≤
      (|L x| ^ (N - (n - i)) / ((N - (n - i)).factorial : ℝ) * Real.exp |L x|) *
        ‖L‖ ^ (n - i) := by
    rw [L.iteratedFDeriv_comp_right hRN_smooth x (by simp)]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    simp only [Finset.prod_const, Finset.card_fin]
    gcongr
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, exp_tail_deriv N (n - i), Real.norm_eq_abs]
    exact abs_exp_sub_sum_le (L x) (N - (n - i))
  have hLx : |L x| ≤ ‖L‖ * ‖x‖ := L.le_opNorm x
  have hRN_exp : N - (n - i) = (N - n) + i := by omega
  have hfac_n : ((N - n).factorial : ℝ) ≤ ((N - (n - i)).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega : N - n ≤ N - (n - i))
  have hL_pow : ‖L‖ ^ i * ‖L‖ ^ (n - i) ≤ max ‖L‖ 1 ^ (2 * n) := by
    calc
      ‖L‖ ^ i * ‖L‖ ^ (n - i) = ‖L‖ ^ n := by rw [← pow_add, Nat.add_sub_of_le hin]
      _ ≤ max ‖L‖ 1 ^ n := pow_le_pow_left₀ (norm_nonneg L) (le_max_left _ _) n
      _ ≤ max ‖L‖ 1 ^ (2 * n) := pow_le_pow_right₀ (le_max_right _ _) (by omega)
  have hquad : Real.exp (-b * ‖x‖ ^ 2) * Real.exp |L x| ≤
      Real.exp (‖L‖ ^ 2 / (8 * c)) * (Real.exp (-c * ‖x‖ ^ 2) * Real.exp (-c * ‖x‖ ^ 2)) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
    have hsq_ge : 0 ≤ 2 * c * (‖x‖ - ‖L‖ / (4 * c)) ^ 2 := by positivity
    have hlin : ‖L‖ * ‖x‖ - 2 * c * ‖x‖ ^ 2 ≤ ‖L‖ ^ 2 / (8 * c) := by
      have hident : 2 * c * (‖x‖ - ‖L‖ / (4 * c)) ^ 2 =
          2 * c * ‖x‖ ^ 2 - ‖L‖ * ‖x‖ + ‖L‖ ^ 2 / (8 * c) := by
        field_simp [hc.ne']; ring
      linarith
    have hb_c : b = 4 * c := by ring
    rw [hb_c]
    linarith [hLx, hlin]
  have hx_i : ‖x‖ ^ i ≤ (1 + ‖x‖) ^ n :=
    (pow_le_pow_left₀ (norm_nonneg x) (by linarith) i).trans
      (pow_le_pow_right₀ (by linarith [norm_nonneg x]) hin)
  have hRN_le2 : ‖iteratedFDeriv ℝ (n - i) (RN ∘ L) x‖ ≤
      (‖L‖ ^ i * ‖L‖ ^ (n - i)) * (1 + ‖x‖) ^ n * Real.exp |L x| *
        ((‖L‖ * ‖x‖) ^ (N - n) / ((N - n).factorial : ℝ)) := by
    have hLpow : |L x| ^ (N - (n - i)) ≤ (‖L‖ * ‖x‖) ^ (N - n) * (‖L‖ ^ i * ‖x‖ ^ i) := by
      calc
        |L x| ^ (N - (n - i)) ≤ (‖L‖ * ‖x‖) ^ (N - (n - i)) :=
          pow_le_pow_left₀ (abs_nonneg _) hLx _
        _ = (‖L‖ * ‖x‖) ^ (N - n) * (‖L‖ ^ i * ‖x‖ ^ i) := by
          rw [hRN_exp, pow_add, mul_pow, mul_pow]
    have hLpow' : |L x| ^ (N - (n - i)) ≤ (‖L‖ * ‖x‖) ^ (N - n) * (‖L‖ ^ i * (1 + ‖x‖) ^ n) :=
      hLpow.trans (by gcongr)
    calc
      ‖iteratedFDeriv ℝ (n - i) (RN ∘ L) x‖
          ≤ (|L x| ^ (N - (n - i)) / ((N - (n - i)).factorial : ℝ) * Real.exp |L x|) *
            ‖L‖ ^ (n - i) := hcomp_RN
      _ ≤ (((‖L‖ * ‖x‖) ^ (N - n) * (‖L‖ ^ i * (1 + ‖x‖) ^ n)) / ((N - n).factorial : ℝ) *
            Real.exp |L x|) * ‖L‖ ^ (n - i) := by gcongr
      _ = (‖L‖ ^ i * ‖L‖ ^ (n - i)) * (1 + ‖x‖) ^ n * Real.exp |L x| *
            ((‖L‖ * ‖x‖) ^ (N - n) / ((N - n).factorial : ℝ)) := by ring
  have hxk : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k := pow_le_pow_left₀ (norm_nonneg x) (by linarith) k
  have htail := pow_div_factorial_mul_exp_neg_sq_le ‖L‖ c (norm_nonneg L) hc (N - n)
    ‖x‖ (norm_nonneg x)
  have hpoly := gaussian_poly_bound c hc (k + 1 + j * i + n) ‖x‖ (norm_nonneg x)
  have hprod1 : ‖x‖ ^ k * ‖iteratedFDeriv ℝ i (fun z : E ↦ Real.exp (-b * ‖z‖ ^ 2)) x‖ *
      ‖iteratedFDeriv ℝ (n - i) (RN ∘ L) x‖ ≤
      (1 + ‖x‖) ^ k * (i.factorial * Real.exp (-b * ‖x‖ ^ 2) * (D₀ * (1 + ‖x‖) ^ j) ^ i) *
        ((‖L‖ ^ i * ‖L‖ ^ (n - i)) * (1 + ‖x‖) ^ n * Real.exp |L x| *
          ((‖L‖ * ‖x‖) ^ (N - n) / ((N - n).factorial : ℝ))) :=
    mul_le_mul (mul_le_mul hxk hcomp_exp (norm_nonneg _) (by positivity))
      hRN_le2 (norm_nonneg _) (by positivity)
  have hrearr1 : (1 + ‖x‖) ^ k * (i.factorial * Real.exp (-b * ‖x‖ ^ 2) * (D₀ * (1 + ‖x‖) ^ j) ^ i) *
      ((‖L‖ ^ i * ‖L‖ ^ (n - i)) * (1 + ‖x‖) ^ n * Real.exp |L x| *
        ((‖L‖ * ‖x‖) ^ (N - n) / ((N - n).factorial : ℝ))) =
      (i.factorial * D₀ ^ i * (‖L‖ ^ i * ‖L‖ ^ (n - i))) *
        (1 + ‖x‖) ^ (k + j * i + n) * (Real.exp (-b * ‖x‖ ^ 2) * Real.exp |L x|) *
        ((‖L‖ * ‖x‖) ^ (N - n) / ((N - n).factorial : ℝ)) := by
    rw [mul_pow, ← pow_mul, pow_add, pow_add]
    ring
  have hquad_mul : (i.factorial * D₀ ^ i * (‖L‖ ^ i * ‖L‖ ^ (n - i))) *
      (1 + ‖x‖) ^ (k + j * i + n) * (Real.exp (-b * ‖x‖ ^ 2) * Real.exp |L x|) *
      ((‖L‖ * ‖x‖) ^ (N - n) / ((N - n).factorial : ℝ)) ≤
      (i.factorial * D₀ ^ i * max ‖L‖ 1 ^ (2 * n) * Real.exp (‖L‖ ^ 2 / (8 * c))) *
        ((1 + ‖x‖) ^ (k + j * i + n) * Real.exp (-c * ‖x‖ ^ 2)) *
        ((‖L‖ * ‖x‖) ^ (N - n) / ((N - n).factorial : ℝ) * Real.exp (-c * ‖x‖ ^ 2)) := by
    calc
      _ ≤ (i.factorial * D₀ ^ i * max ‖L‖ 1 ^ (2 * n)) *
            (1 + ‖x‖) ^ (k + j * i + n) *
            (Real.exp (‖L‖ ^ 2 / (8 * c)) * (Real.exp (-c * ‖x‖ ^ 2) * Real.exp (-c * ‖x‖ ^ 2))) *
            ((‖L‖ * ‖x‖) ^ (N - n) / ((N - n).factorial : ℝ)) := by gcongr
      _ = _ := by ring
  have htail_mul : (i.factorial * D₀ ^ i * max ‖L‖ 1 ^ (2 * n) * Real.exp (‖L‖ ^ 2 / (8 * c))) *
      ((1 + ‖x‖) ^ (k + j * i + n) * Real.exp (-c * ‖x‖ ^ 2)) *
      ((‖L‖ * ‖x‖) ^ (N - n) / ((N - n).factorial : ℝ) * Real.exp (-c * ‖x‖ ^ 2)) ≤
      (i.factorial * D₀ ^ i * max ‖L‖ 1 ^ (2 * n) * Real.exp (‖L‖ ^ 2 / (8 * c)) * max ‖L‖ 1 *
        gaussianPolyC c (k + 1 + j * i + n)) *
      ((max ‖L‖ 1 ^ 2 / c) ^ ((N - n) / 2) / (((N - n) / 2).factorial : ℝ)) := by
    have h2a : (i.factorial * D₀ ^ i * max ‖L‖ 1 ^ (2 * n) * Real.exp (‖L‖ ^ 2 / (8 * c))) *
        ((1 + ‖x‖) ^ (k + j * i + n) * Real.exp (-c * ‖x‖ ^ 2)) *
        ((‖L‖ * ‖x‖) ^ (N - n) / ((N - n).factorial : ℝ) * Real.exp (-c * ‖x‖ ^ 2)) ≤
        (i.factorial * D₀ ^ i * max ‖L‖ 1 ^ (2 * n) * Real.exp (‖L‖ ^ 2 / (8 * c))) *
        ((1 + ‖x‖) ^ (k + j * i + n) * Real.exp (-c * ‖x‖ ^ 2)) *
        ((1 + ‖x‖) * max ‖L‖ 1 * ((max ‖L‖ 1 ^ 2 / c) ^ ((N - n) / 2) /
          (((N - n) / 2).factorial : ℝ))) :=
      mul_le_mul_of_nonneg_left htail (by positivity)
    have h2b : (i.factorial * D₀ ^ i * max ‖L‖ 1 ^ (2 * n) * Real.exp (‖L‖ ^ 2 / (8 * c))) *
        ((1 + ‖x‖) ^ (k + j * i + n) * Real.exp (-c * ‖x‖ ^ 2)) *
        ((1 + ‖x‖) * max ‖L‖ 1 * ((max ‖L‖ 1 ^ 2 / c) ^ ((N - n) / 2) /
          (((N - n) / 2).factorial : ℝ))) =
        (i.factorial * D₀ ^ i * max ‖L‖ 1 ^ (2 * n) * Real.exp (‖L‖ ^ 2 / (8 * c)) * max ‖L‖ 1) *
          ((1 + ‖x‖) ^ (k + 1 + j * i + n) * Real.exp (-c * ‖x‖ ^ 2)) *
          ((max ‖L‖ 1 ^ 2 / c) ^ ((N - n) / 2) / (((N - n) / 2).factorial : ℝ)) := by
      rw [show k + 1 + j * i + n = (k + j * i + n) + 1 by ring, pow_succ]
      ring
    calc
      _ ≤ _ := h2a
      _ = _ := h2b
      _ ≤ _ := by gcongr
  exact hprod1.trans ((hrearr1 ▸ hquad_mul).trans htail_mul)

private theorem gauss_taylor_tendsto {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (b : ℝ) (hb : 0 < b) (y : E) :
    Tendsto (fun N : ℕ ↦ ∑ m ∈ Finset.range N,
      (((2 * b : ℂ) ^ m / (m.factorial : ℂ)) •
        SchwartzMap.smulLeftCLM ℂ (fun x : E ↦ ((inner ℝ x y : ℝ) : ℂ) ^ m)
          ((SchwartzMap.gaussian b hb).postcompCLM Complex.ofRealCLM)))
      atTop
      (nhds ((Real.exp (b * ‖y‖ ^ 2) : ℂ) •
        (((SchwartzMap.gaussian b hb).postcompCLM Complex.ofRealCLM).compSubConstCLM ℂ y))) := by
  have hinner_tg : (fun x : E ↦ inner ℝ x y).HasTemperateGrowth := by
    convert (innerSL ℝ y).hasTemperateGrowth using 1
    ext x
    exact real_inner_comm y x
  let F : ℕ → SchwartzMap E ℝ := fun N ↦
    Real.exp (b * ‖y‖ ^ 2) • ((SchwartzMap.gaussian b hb).compSubConstCLM ℝ y) -
      ∑ m ∈ Finset.range N, ((2 * b) ^ m / (m.factorial : ℝ)) •
        SchwartzMap.smulLeftCLM ℝ (fun x : E ↦ (inner ℝ x y) ^ m) (SchwartzMap.gaussian b hb)
  have hF : Tendsto F atTop (nhds 0) := by
    rw [(schwartz_withSeminorms ℝ E ℝ).tendsto_nhds _ 0]
    intro ⟨k, n⟩ ε hε
    simp only [sub_zero]
    have hns : (fun x : E ↦ ‖x‖ ^ 2).HasTemperateGrowth :=
      Function.hasTemperateGrowth_norm_sq E
    obtain ⟨j, C₀, hC₀⟩ := hns.norm_iteratedFDeriv_le_uniform n
    let D₀ : ℝ := b * max C₀ 0 + 1
    have hD₀ : 1 ≤ D₀ := by simp only [D₀, le_add_iff_nonneg_left]; positivity
    let L : E →L[ℝ] ℝ := (2 * b) • innerSL ℝ y
    have hL_apply : ∀ x : E, L x = 2 * b * inner ℝ x y := fun x ↦ by
      simp [L, real_inner_comm]
    let c : ℝ := b / 4
    have hc : 0 < c := by positivity
    let B : ℝ := ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
      (i.factorial * D₀ ^ i * max ‖L‖ 1 ^ (2 * n) *
        Real.exp (‖L‖ ^ 2 / (8 * c)) * max ‖L‖ 1 *
        gaussianPolyC c (k + 1 + j * i + n))
    have hbd : ∀ N : ℕ, n ≤ N → SchwartzMap.seminorm ℝ k n (F N) ≤
        B * ((max ‖L‖ 1 ^ 2 / c) ^ ((N - n) / 2) / (((N - n) / 2).factorial : ℝ)) := by
      intro N hN
      have hB : 0 ≤ B := Finset.sum_nonneg fun i _ ↦ by
        have := gaussianPolyC_nonneg hc (k + 1 + j * i + n)
        positivity
      refine SchwartzMap.seminorm_le_bound ℝ k n (F N) (by positivity) fun x ↦ ?_
      let RN : ℝ → ℝ := fun u ↦ Real.exp u - ∑ m ∈ Finset.range N, u ^ m / (m.factorial : ℝ)
      have hRN_smooth : ContDiff ℝ (∞) RN :=
        Real.contDiff_exp.sub (ContDiff.sum fun m _ ↦ (contDiff_id.pow m).div_const _)
      have hpowR : ∀ m, (fun z : E ↦ inner ℝ z y ^ m).HasTemperateGrowth :=
        fun m ↦ hinner_tg.pow m
      have hFun : ((F N : SchwartzMap E ℝ) : E → ℝ) =
          fun z ↦ Real.exp (-b * ‖z‖ ^ 2) * RN (L z) := by
        ext z
        simp only [F, sub_apply, smul_apply, SchwartzMap.compSubConstCLM_apply,
          SchwartzMap.gaussian_apply, sum_apply, smul_eq_mul, RN, hL_apply]
        have hsq : ‖z - y‖ ^ 2 = ‖z‖ ^ 2 - 2 * inner ℝ z y + ‖y‖ ^ 2 := norm_sub_sq_real z y
        rw [hsq]
        have hexp : b * ‖y‖ ^ 2 + -b * (‖z‖ ^ 2 - 2 * inner ℝ z y + ‖y‖ ^ 2) =
            -b * ‖z‖ ^ 2 + 2 * b * inner ℝ z y := by ring
        rw [← Real.exp_add, hexp, Real.exp_add, mul_sub]
        congr 1
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ ↦ ?_
        rw [SchwartzMap.smulLeftCLM_apply_apply (hpowR m), SchwartzMap.gaussian_apply,
          smul_eq_mul, mul_pow]
        ring
      rw [hFun]
      have hgauss_smooth : ContDiff ℝ (∞) (fun z : E ↦ Real.exp (-b * ‖z‖ ^ 2)) :=
        Real.contDiff_exp.comp (contDiff_const.mul (hns.1.of_le (by simp)))
      have hleib := norm_iteratedFDeriv_mul_le hgauss_smooth
        (hRN_smooth.comp L.contDiff) x (n := n) (by simp)
      have hleib' : ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun z ↦ Real.exp (-b * ‖z‖ ^ 2) * RN (L z)) x‖ ≤
          ‖x‖ ^ k * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i (fun z : E ↦ Real.exp (-b * ‖z‖ ^ 2)) x‖ *
            ‖iteratedFDeriv ℝ (n - i) (RN ∘ L) x‖ :=
        mul_le_mul_of_nonneg_left hleib (by positivity)
      calc
        ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun z ↦ Real.exp (-b * ‖z‖ ^ 2) * RN (L z)) x‖
            ≤ ‖x‖ ^ k * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
              ‖iteratedFDeriv ℝ i (fun z : E ↦ Real.exp (-b * ‖z‖ ^ 2)) x‖ *
              ‖iteratedFDeriv ℝ (n - i) (RN ∘ L) x‖ := hleib'
        _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
            (‖x‖ ^ k * ‖iteratedFDeriv ℝ i (fun z : E ↦ Real.exp (-b * ‖z‖ ^ 2)) x‖ *
              ‖iteratedFDeriv ℝ (n - i) (RN ∘ L) x‖) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ ↦ by ring
        _ ≤ B * ((max ‖L‖ 1 ^ 2 / c) ^ ((N - n) / 2) / (((N - n) / 2).factorial : ℝ)) := by
          rw [Finset.sum_mul]
          refine Finset.sum_le_sum fun i hi ↦ ?_
          have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          have hpt := gauss_taylor_pointwise_le b hb y k n N i j C₀ D₀ hD₀ hC₀.2 le_rfl hin hN x
          calc
            (n.choose i : ℝ) *
                (‖x‖ ^ k * ‖iteratedFDeriv ℝ i (fun z : E ↦ Real.exp (-b * ‖z‖ ^ 2)) x‖ *
                  ‖iteratedFDeriv ℝ (n - i) (RN ∘ L) x‖)
                ≤ (n.choose i : ℝ) *
                    ((i.factorial * D₀ ^ i * max ‖L‖ 1 ^ (2 * n) * Real.exp (‖L‖ ^ 2 / (8 * c)) *
                      max ‖L‖ 1 * gaussianPolyC c (k + 1 + j * i + n)) *
                    ((max ‖L‖ 1 ^ 2 / c) ^ ((N - n) / 2) / (((N - n) / 2).factorial : ℝ))) :=
                  mul_le_mul_of_nonneg_left hpt (Nat.cast_nonneg _)
            _ = _ := by ring
    have hpow_lim : Tendsto (fun N : ℕ ↦
        B * ((max ‖L‖ 1 ^ 2 / c) ^ ((N - n) / 2) / (((N - n) / 2).factorial : ℝ)))
        atTop (nhds 0) := by
      have hdiv : Tendsto (fun N : ℕ ↦ (N - n) / 2) atTop atTop :=
        tendsto_atTop_atTop.mpr fun K ↦ ⟨2 * K + n, fun N hN ↦ by omega⟩
      have hsum_exp := (NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ)
        (max ‖L‖ 1 ^ 2 / c)).summable.tendsto_atTop_zero
      have hpow0 : Tendsto (fun p : ℕ ↦
          (max ‖L‖ 1 ^ 2 / c) ^ p / (p.factorial : ℝ)) atTop (nhds 0) := by
        simpa [div_eq_mul_inv, mul_comm] using hsum_exp
      simpa using (hpow0.comp hdiv).const_mul B
    filter_upwards [eventually_atTop.mpr ⟨n, hbd⟩, hpow_lim.eventually (Iio_mem_nhds hε)] with
      N hN1 hN2
    exact lt_of_le_of_lt hN1 hN2
  let P_clm := SchwartzMap.postcompCLM Complex.ofRealCLM (E := E) (𝕜 := ℝ)
  have hP := P_clm.continuous.tendsto 0 |>.comp hF
  rw [map_zero] at hP
  have hsub : Tendsto (fun N : ℕ ↦
      ((Real.exp (b * ‖y‖ ^ 2) : ℂ) •
        (((SchwartzMap.gaussian b hb).postcompCLM Complex.ofRealCLM).compSubConstCLM ℂ y)) -
      ∑ m ∈ Finset.range N,
        (((2 * b : ℂ) ^ m / (m.factorial : ℂ)) •
          SchwartzMap.smulLeftCLM ℂ (fun x : E ↦ ((inner ℝ x y : ℝ) : ℂ) ^ m)
            ((SchwartzMap.gaussian b hb).postcompCLM Complex.ofRealCLM)))
      atTop (nhds 0) := by
    refine hP.congr fun N ↦ ?_
    ext x
    have hpowR : ∀ m, (fun z : E ↦ inner ℝ z y ^ m).HasTemperateGrowth := fun m ↦ hinner_tg.pow m
    have hpowC : ∀ m, (fun z : E ↦ ((inner ℝ z y : ℝ) : ℂ) ^ m).HasTemperateGrowth :=
      fun m ↦ (Complex.hasTemperateGrowth_ofReal.comp hinner_tg).pow m
    simp only [Function.comp_apply, P_clm, SchwartzMap.postcompCLM_apply, Complex.ofRealCLM_apply,
      F, sub_apply, smul_apply, SchwartzMap.compSubConstCLM_apply, SchwartzMap.gaussian_apply,
      sum_apply, smul_eq_mul, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_sum,
      Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast, Complex.ofReal_exp]
    congr 1
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    rw [SchwartzMap.smulLeftCLM_apply_apply (hpowR m),
      SchwartzMap.smulLeftCLM_apply_apply (hpowC m)]
    simp only [SchwartzMap.postcompCLM_apply, Complex.ofRealCLM_apply, SchwartzMap.gaussian_apply,
      smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_pow]
    push_cast
    rfl
  have hneg : Tendsto (fun N : ℕ ↦
      (∑ m ∈ Finset.range N,
        (((2 * b : ℂ) ^ m / (m.factorial : ℂ)) •
          SchwartzMap.smulLeftCLM ℂ (fun x : E ↦ ((inner ℝ x y : ℝ) : ℂ) ^ m)
            ((SchwartzMap.gaussian b hb).postcompCLM Complex.ofRealCLM))) -
      ((Real.exp (b * ‖y‖ ^ 2) : ℂ) •
        (((SchwartzMap.gaussian b hb).postcompCLM Complex.ofRealCLM).compSubConstCLM ℂ y)))
      atTop (nhds 0) := by
    simpa [neg_sub] using hsub.neg
  exact tendsto_sub_nhds_zero_iff.mp hneg

private theorem schwartzDual_translate_gauss_eq_zero {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (T : StrongDual ℂ (SchwartzMap E ℂ))
    (b : ℝ) (hb : 0 < b) (y : E)
    (hm : ∀ m : ℕ, T (SchwartzMap.smulLeftCLM ℂ (fun x : E ↦ ((inner ℝ x y : ℝ) : ℂ) ^ m)
      ((SchwartzMap.gaussian b hb).postcompCLM Complex.ofRealCLM)) = 0) :
    T (((SchwartzMap.gaussian b hb).postcompCLM Complex.ofRealCLM).compSubConstCLM ℂ y) = 0 := by
  have hlim := (T.continuous.tendsto _).comp (gauss_taylor_tendsto b hb y)
  have hzero : Tendsto (fun _ : ℕ ↦ (0 : ℂ)) atTop
      (nhds (T ((Real.exp (b * ‖y‖ ^ 2) : ℂ) •
        (((SchwartzMap.gaussian b hb).postcompCLM Complex.ofRealCLM).compSubConstCLM ℂ y)))) := by
    refine hlim.congr fun N ↦ ?_
    simp only [Function.comp_apply, map_sum, map_smul, hm, smul_zero, Finset.sum_const_zero]
  have hmul : (Real.exp (b * ‖y‖ ^ 2) : ℂ) *
      T (((SchwartzMap.gaussian b hb).postcompCLM Complex.ofRealCLM).compSubConstCLM ℂ y) = 0 := by
    simpa [map_smul, smul_eq_mul] using (tendsto_nhds_unique tendsto_const_nhds hzero).symm
  have hexp_ne : (Real.exp (b * ‖y‖ ^ 2) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  exact (mul_eq_zero.mp hmul).resolve_left hexp_ne

end Step3a

section Step3b

private lemma schwartzMap_one_add_norm_pow_mul_integrable {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure]
    (f : SchwartzMap E ℂ) (k : ℕ) :
    Integrable (fun y : E ↦ (1 + ‖y‖) ^ k * ‖f y‖) volume := by
  have h1 : Integrable (fun y : E ↦ 2 ^ k * (‖y‖ ^ 0 * ‖f y‖ + ‖y‖ ^ k * ‖f y‖)) volume :=
    ((f.integrable_pow_mul volume 0).add (f.integrable_pow_mul volume k)).const_mul (2 ^ k)
  refine h1.mono ?_ (Eventually.of_forall fun y ↦ ?_)
  · exact ((continuous_const.add continuous_norm).pow k |>.mul f.continuous.norm).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    calc
      (1 + ‖y‖) ^ k * ‖f y‖ ≤ 2 ^ k * (1 + ‖y‖ ^ k) * ‖f y‖ := by
        gcongr; exact one_add_pow_le (norm_nonneg y) k
      _ = 2 ^ k * (‖y‖ ^ 0 * ‖f y‖ + ‖y‖ ^ k * ‖f y‖) := by ring

private lemma schwartzConvSet_integrable {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure]
    (S : Set E) (f g : SchwartzMap E ℂ) (n : ℕ) (x : E) :
    Integrable (fun y : E ↦ f y • iteratedFDeriv ℝ n g (x - y)) (volume.restrict S) := by
  have hcont : Continuous (fun y : E ↦ f y • iteratedFDeriv ℝ n g (x - y)) :=
    f.continuous.smul (((g.smooth ⊤).continuous_iteratedFDeriv (mod_cast le_top)).comp
      (continuous_const.sub continuous_id))
  refine Integrable.mono (f.integrable.norm.mul_const (SchwartzMap.seminorm ℂ 0 n g)).integrableOn
    hcont.aestronglyMeasurable (Eventually.of_forall fun y ↦ ?_)
  rw [norm_smul, Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (apply_nonneg _ _))]
  gcongr
  simpa using SchwartzMap.le_seminorm ℂ 0 n g (x - y)

private lemma schwartzConvSet_hasFDerivAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure]
    (S : Set E) (f g : SchwartzMap E ℂ) (n : ℕ) (x : E) :
    let CL := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) ↦ E) ℂ
    HasFDerivAt (fun z : E ↦ ∫ y in S, f y • iteratedFDeriv ℝ n g (z - y))
      (CL.toContinuousLinearEquiv.toContinuousLinearMap
        (∫ y in S, f y • iteratedFDeriv ℝ (n + 1) g (x - y))) x := by
  intro CL
  let F : E → E → ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ E) ℂ :=
    fun z y ↦ f y • iteratedFDeriv ℝ n g (z - y)
  let F' : E → E → E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ E) ℂ :=
    fun z y ↦ f y • CL (iteratedFDeriv ℝ (n + 1) g (z - y))
  have hdiff := hasFDerivAt_integral_of_dominated_of_fderiv_le (F := F) (F' := F') univ_mem
    (Eventually.of_forall fun z ↦ (f.continuous.smul (((g.smooth ⊤).continuous_iteratedFDeriv
      (mod_cast le_top)).comp (continuous_const.sub continuous_id))).aestronglyMeasurable)
    (schwartzConvSet_integrable S f g n x)
    ((f.continuous.smul (CL.continuous.comp (((g.smooth ⊤).continuous_iteratedFDeriv
      (mod_cast le_top)).comp (continuous_const.sub continuous_id)))).aestronglyMeasurable)
    (Eventually.of_forall fun y z _ ↦ by
      simp only [F', norm_smul, LinearIsometryEquiv.norm_map]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      simpa using SchwartzMap.le_seminorm ℂ 0 (n + 1) g (z - y))
    ((f.integrable.norm.mul_const (SchwartzMap.seminorm ℂ 0 (n + 1) g)).integrableOn)
    (Eventually.of_forall fun y z _ ↦ by
      have hg1 : HasFDerivAt (fun w : E ↦ iteratedFDeriv ℝ n g (w - y))
          (CL (iteratedFDeriv ℝ (n + 1) g (z - y))) z := by
        have hd := ((g.smooth (n + 1 : ℕ)).differentiable_iteratedFDeriv (m := n)
          (by norm_cast; omega) (z - y)).hasFDerivAt
        have hsub : HasFDerivAt (fun w : E ↦ w - y) (ContinuousLinearMap.id ℝ E) z :=
          (hasFDerivAt_id z).sub_const y
        have hcomp := hd.comp z hsub
        rw [ContinuousLinearMap.comp_id] at hcomp
        refine hcomp.congr_fderiv ?_
        ext u v
        simp [CL, iteratedFDeriv_succ_apply_left]
      exact hg1.const_smul (f y))
  have hint' : Integrable (fun y : E ↦ f y • iteratedFDeriv ℝ (n + 1) g (x - y))
      (volume.restrict S) := schwartzConvSet_integrable S f g (n + 1) x
  have heq : (∫ y in S, F' x y) =
      CL.toContinuousLinearEquiv.toContinuousLinearMap
        (∫ y in S, f y • iteratedFDeriv ℝ (n + 1) g (x - y)) := by
    rw [← CL.toContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm hint']
    refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
    ext u v
    simp [F', CL]
  rwa [← heq]

private lemma schwartzConvSet_iteratedFDeriv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure]
    (S : Set E) (f g : SchwartzMap E ℂ) (n : ℕ) :
    ∀ x : E, iteratedFDeriv ℝ n (fun z : E ↦ ∫ y in S, f y * g (z - y)) x =
      ∫ y in S, f y • iteratedFDeriv ℝ n g (x - y) := by
  induction n with
  | zero =>
    intro x
    let C0 := (continuousMultilinearCurryFin0 ℝ E ℂ).symm.toContinuousLinearEquiv.toContinuousLinearMap
    have hint : Integrable (fun y : E ↦ f y * g (x - y)) (volume.restrict S) := by
      refine Integrable.mono (f.integrable.norm.mul_const (SchwartzMap.seminorm ℂ 0 0 g)).integrableOn
        (f.continuous.mul (g.continuous.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
        (Eventually.of_forall fun y ↦ ?_)
      simp only [norm_mul, Real.norm_of_nonneg (norm_nonneg _),
        Real.norm_of_nonneg (apply_nonneg _ _)]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      simpa using SchwartzMap.le_seminorm ℂ 0 0 g (x - y)
    change C0 (∫ y in S, f y * g (x - y)) = ∫ y in S, f y • C0 (g (x - y))
    rw [← C0.integral_comp_comm hint]
    refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
    ext v
    simp [C0, smul_eq_mul]
  | succ n ih =>
    intro x
    let CL := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) ↦ E) ℂ
    have hEq : iteratedFDeriv ℝ n (fun z : E ↦ ∫ y in S, f y * g (z - y)) =
        fun z : E ↦ ∫ y in S, f y • iteratedFDeriv ℝ n g (z - y) := funext ih
    have hdiff := schwartzConvSet_hasFDerivAt S f g n x
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, hEq, hdiff.fderiv]
    exact CL.symm_apply_apply _

private noncomputable def schwartzConvSet {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure]
    (S : Set E) (f g : SchwartzMap E ℂ) : SchwartzMap E ℂ where
  toFun := fun x ↦ ∫ y in S, f y * g (x - y)
  smooth' := by
    refine contDiff_of_differentiable_iteratedFDeriv fun m _ ↦ fun x ↦ ?_
    have hEq : iteratedFDeriv ℝ m (fun z : E ↦ ∫ y in S, f y * g (z - y)) =
        fun z : E ↦ ∫ y in S, f y • iteratedFDeriv ℝ m g (z - y) :=
      funext (schwartzConvSet_iteratedFDeriv S f g m)
    rw [hEq]
    exact (schwartzConvSet_hasFDerivAt S f g m x).differentiableAt
  decay' k n := by
    let Cg := 2 ^ k * (SchwartzMap.seminorm ℂ 0 n g + SchwartzMap.seminorm ℂ k n g)
    let C := Cg * ∫ y in S, (1 + ‖y‖) ^ k * ‖f y‖
    refine ⟨C, fun x ↦ ?_⟩
    rw [schwartzConvSet_iteratedFDeriv S f g n x]
    have hbd1 : ‖∫ y in S, f y • iteratedFDeriv ℝ n g (x - y)‖ ≤
        ∫ y in S, ‖f y‖ * ‖iteratedFDeriv ℝ n g (x - y)‖ := by
      refine (norm_integral_le_integral_norm _).trans_eq ?_
      simp [norm_smul]
    have hint : Integrable (fun y : E ↦ Cg * ((1 + ‖y‖) ^ k * ‖f y‖)) (volume.restrict S) :=
      ((schwartzMap_one_add_norm_pow_mul_integrable f k).const_mul Cg).integrableOn
    have hint_lhs : Integrable (fun y : E ↦ ‖x‖ ^ k * (‖f y‖ * ‖iteratedFDeriv ℝ n g (x - y)‖))
        (volume.restrict S) := by
      refine ((schwartzConvSet_integrable S f g n x).norm.const_mul (‖x‖ ^ k)).congr
        (Eventually.of_forall fun y ↦ ?_)
      simp [norm_smul]
    have hpt : ∀ y : E, ‖x‖ ^ k * (‖f y‖ * ‖iteratedFDeriv ℝ n g (x - y)‖) ≤
        Cg * ((1 + ‖y‖) ^ k * ‖f y‖) := fun y ↦ by
      have hx1 : 1 + ‖x‖ ≤ (1 + ‖x - y‖) * (1 + ‖y‖) := by
        have htri : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := norm_le_norm_sub_add x y
        nlinarith [norm_nonneg (x - y), norm_nonneg y]
      have hxk : ‖x‖ ^ k ≤ (1 + ‖x - y‖) ^ k * (1 + ‖y‖) ^ k :=
        (pow_le_pow_left₀ (norm_nonneg x) (by linarith) k).trans
          ((pow_le_pow_left₀ (by positivity) hx1 k).trans_eq (mul_pow _ _ _))
      have hg_bd : (1 + ‖x - y‖) ^ k * ‖iteratedFDeriv ℝ n g (x - y)‖ ≤ Cg := by
        calc
          (1 + ‖x - y‖) ^ k * ‖iteratedFDeriv ℝ n g (x - y)‖
              ≤ 2 ^ k * (1 + ‖x - y‖ ^ k) * ‖iteratedFDeriv ℝ n g (x - y)‖ := by
            gcongr; exact one_add_pow_le (norm_nonneg (x - y)) k
          _ = 2 ^ k * (‖x - y‖ ^ 0 * ‖iteratedFDeriv ℝ n g (x - y)‖ +
              ‖x - y‖ ^ k * ‖iteratedFDeriv ℝ n g (x - y)‖) := by ring
          _ ≤ Cg := by
            dsimp only [Cg]
            gcongr
            · simpa using SchwartzMap.le_seminorm ℂ 0 n g (x - y)
            · exact SchwartzMap.le_seminorm ℂ k n g (x - y)
      calc
        ‖x‖ ^ k * (‖f y‖ * ‖iteratedFDeriv ℝ n g (x - y)‖)
            ≤ (1 + ‖x - y‖) ^ k * (1 + ‖y‖) ^ k * (‖f y‖ * ‖iteratedFDeriv ℝ n g (x - y)‖) := by
          gcongr
        _ = ((1 + ‖x - y‖) ^ k * ‖iteratedFDeriv ℝ n g (x - y)‖) * ((1 + ‖y‖) ^ k * ‖f y‖) := by
          ring
        _ ≤ Cg * ((1 + ‖y‖) ^ k * ‖f y‖) := by gcongr
    calc
      ‖x‖ ^ k * ‖∫ y in S, f y • iteratedFDeriv ℝ n g (x - y)‖
          ≤ ‖x‖ ^ k * ∫ y in S, ‖f y‖ * ‖iteratedFDeriv ℝ n g (x - y)‖ := by gcongr
      _ = ∫ y in S, ‖x‖ ^ k * (‖f y‖ * ‖iteratedFDeriv ℝ n g (x - y)‖) := by
        rw [← integral_const_mul]
      _ ≤ ∫ y in S, Cg * ((1 + ‖y‖) ^ k * ‖f y‖) := integral_mono hint_lhs hint hpt
      _ = C := integral_const_mul Cg _

private lemma schwartzConvSet_apply {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure]
    (S : Set E) (f g : SchwartzMap E ℂ) (x : E) :
    schwartzConvSet S f g x = ∫ y in S, f y * g (x - y) := rfl

private lemma schwartzConvSet_seminorm_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure]
    (S : Set E) (f g : SchwartzMap E ℂ) (k n : ℕ) :
    SchwartzMap.seminorm ℂ k n (schwartzConvSet S f g) ≤
      2 ^ k * (SchwartzMap.seminorm ℂ 0 n g + SchwartzMap.seminorm ℂ k n g) *
        ∫ y in S, (1 + ‖y‖) ^ k * ‖f y‖ := by
  let Cg := 2 ^ k * (SchwartzMap.seminorm ℂ 0 n g + SchwartzMap.seminorm ℂ k n g)
  let C := Cg * ∫ y in S, (1 + ‖y‖) ^ k * ‖f y‖
  have hC : 0 ≤ C := mul_nonneg (by positivity) (integral_nonneg fun _ ↦ by positivity)
  refine SchwartzMap.seminorm_le_bound ℂ k n (schwartzConvSet S f g) hC fun x ↦ ?_
  change ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun z : E ↦ ∫ y in S, f y * g (z - y)) x‖ ≤ C
  rw [schwartzConvSet_iteratedFDeriv S f g n x]
  have hbd1 : ‖∫ y in S, f y • iteratedFDeriv ℝ n g (x - y)‖ ≤
      ∫ y in S, ‖f y‖ * ‖iteratedFDeriv ℝ n g (x - y)‖ := by
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    simp [norm_smul]
  have hint : Integrable (fun y : E ↦ Cg * ((1 + ‖y‖) ^ k * ‖f y‖)) (volume.restrict S) :=
    ((schwartzMap_one_add_norm_pow_mul_integrable f k).const_mul Cg).integrableOn
  have hint_lhs : Integrable (fun y : E ↦ ‖x‖ ^ k * (‖f y‖ * ‖iteratedFDeriv ℝ n g (x - y)‖))
      (volume.restrict S) := by
    refine ((schwartzConvSet_integrable S f g n x).norm.const_mul (‖x‖ ^ k)).congr
      (Eventually.of_forall fun y ↦ ?_)
    simp [norm_smul]
  have hpt : ∀ y : E, ‖x‖ ^ k * (‖f y‖ * ‖iteratedFDeriv ℝ n g (x - y)‖) ≤
      Cg * ((1 + ‖y‖) ^ k * ‖f y‖) := fun y ↦ by
    have hx1 : 1 + ‖x‖ ≤ (1 + ‖x - y‖) * (1 + ‖y‖) := by
      have htri : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := norm_le_norm_sub_add x y
      nlinarith [norm_nonneg (x - y), norm_nonneg y]
    have hxk : ‖x‖ ^ k ≤ (1 + ‖x - y‖) ^ k * (1 + ‖y‖) ^ k :=
      (pow_le_pow_left₀ (norm_nonneg x) (by linarith) k).trans
        ((pow_le_pow_left₀ (by positivity) hx1 k).trans_eq (mul_pow _ _ _))
    have hg_bd : (1 + ‖x - y‖) ^ k * ‖iteratedFDeriv ℝ n g (x - y)‖ ≤ Cg := by
      calc
        (1 + ‖x - y‖) ^ k * ‖iteratedFDeriv ℝ n g (x - y)‖
            ≤ 2 ^ k * (1 + ‖x - y‖ ^ k) * ‖iteratedFDeriv ℝ n g (x - y)‖ := by
          gcongr; exact one_add_pow_le (norm_nonneg (x - y)) k
        _ = 2 ^ k * (‖x - y‖ ^ 0 * ‖iteratedFDeriv ℝ n g (x - y)‖ +
            ‖x - y‖ ^ k * ‖iteratedFDeriv ℝ n g (x - y)‖) := by ring
        _ ≤ Cg := by
          dsimp only [Cg]
          gcongr
          · simpa using SchwartzMap.le_seminorm ℂ 0 n g (x - y)
          · exact SchwartzMap.le_seminorm ℂ k n g (x - y)
    calc
      ‖x‖ ^ k * (‖f y‖ * ‖iteratedFDeriv ℝ n g (x - y)‖)
          ≤ (1 + ‖x - y‖) ^ k * (1 + ‖y‖) ^ k * (‖f y‖ * ‖iteratedFDeriv ℝ n g (x - y)‖) := by
        gcongr
      _ = ((1 + ‖x - y‖) ^ k * ‖iteratedFDeriv ℝ n g (x - y)‖) * ((1 + ‖y‖) ^ k * ‖f y‖) := by
        ring
      _ ≤ Cg * ((1 + ‖y‖) ^ k * ‖f y‖) := by gcongr
  calc
    ‖x‖ ^ k * ‖∫ y in S, f y • iteratedFDeriv ℝ n g (x - y)‖
        ≤ ‖x‖ ^ k * ∫ y in S, ‖f y‖ * ‖iteratedFDeriv ℝ n g (x - y)‖ := by gcongr
    _ = ∫ y in S, ‖x‖ ^ k * (‖f y‖ * ‖iteratedFDeriv ℝ n g (x - y)‖) := by
      rw [← integral_const_mul]
    _ ≤ ∫ y in S, Cg * ((1 + ‖y‖) ^ k * ‖f y‖) := integral_mono hint_lhs hint hpt
    _ = C := integral_const_mul Cg _

private lemma schwartzConvSet_univ_comm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure]
    (f g : SchwartzMap E ℂ) :
    schwartzConvSet Set.univ f g = schwartzConvSet Set.univ g f := by
  ext x
  simp only [schwartzConvSet_apply, Measure.restrict_univ]
  have hsub := integral_sub_left_eq_self (fun y : E ↦ f y * g (x - y)) volume x
  rw [← hsub]
  refine integral_congr_ae (Eventually.of_forall fun u ↦ ?_)
  simp [sub_sub_cancel, mul_comm]

private lemma schwartzConvSet_compl_eq_sub {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure]
    {S : Set E} (hS : MeasurableSet S) (f g : SchwartzMap E ℂ) :
    schwartzConvSet Set.univ f g - schwartzConvSet S f g = schwartzConvSet Sᶜ f g := by
  ext x
  simp only [sub_apply, schwartzConvSet_apply, Measure.restrict_univ]
  have hint : Integrable (fun y : E ↦ f y * g (x - y)) volume := by
    refine Integrable.mono (f.integrable.norm.mul_const (SchwartzMap.seminorm ℂ 0 0 g))
      (f.continuous.mul (g.continuous.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
      (Eventually.of_forall fun y ↦ ?_)
    simp only [norm_mul, Real.norm_of_nonneg (norm_nonneg _),
      Real.norm_of_nonneg (apply_nonneg _ _)]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    simpa using SchwartzMap.le_seminorm ℂ 0 0 g (x - y)
  rw [← integral_add_compl hS hint]
  ring

private theorem schwartzDual_eq_zero_of_ball_approx {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure]
    (T : StrongDual ℂ (SchwartzMap E ℂ))
    (hvan : ∀ (b : ℝ) (hb : 0 < b) (y : E),
      T (((SchwartzMap.gaussian b hb).postcompCLM Complex.ofRealCLM).compSubConstCLM ℂ y) = 0)
    (f : SchwartzMap E ℂ) (b : ℝ) (hb : 0 < b) (R : ℝ) (hR : 0 ≤ R)
    (s : Finset (ℕ × ℕ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ h : SchwartzMap E ℂ, T h = 0 ∧
      ∀ p ∈ s, SchwartzMap.seminorm ℂ p.1 p.2
        (schwartzConvSet (Metric.closedBall 0 R) f ((SchwartzMap.gaussian b hb).postcompCLM Complex.ofRealCLM) - h) < ε := by
  let g : SchwartzMap E ℂ := (SchwartzMap.gaussian b hb).postcompCLM Complex.ofRealCLM
  have hf1 : 0 ≤ ∫ y in Metric.closedBall (0 : E) R, ‖f y‖ :=
    integral_nonneg fun _ ↦ norm_nonneg _
  let M : ℝ := (∑ p ∈ s,
    2 ^ p.1 * (1 + R + 1) ^ p.1 * (SchwartzMap.seminorm ℂ 0 (p.2 + 1) g + SchwartzMap.seminorm ℂ p.1 (p.2 + 1) g)) + 1
  have hM : 0 < M := by positivity
  let I₀ : ℝ := (∫ y in Metric.closedBall (0 : E) R, ‖f y‖) + 1
  have hI₀ : 0 < I₀ := lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_left hf1)
  let δ : ℝ := min 1 (ε / (2 * M * I₀))
  have hδ : 0 < δ := lt_min one_pos (by positivity)
  have hcov : Metric.closedBall (0 : E) R ⊆ ⋃ y ∈ Metric.closedBall (0 : E) R, Metric.ball y δ :=
    fun y hy ↦ Set.mem_biUnion hy (Metric.mem_ball_self hδ)
  obtain ⟨t, ht⟩ := (isCompact_closedBall (0 : E) R).elim_finite_subcover_image
    (fun y _ ↦ Metric.isOpen_ball) hcov
  let t₀ : Finset E := ht.2.1.toFinset
  let N : ℕ := t₀.card
  let l : Fin N → E := fun j ↦ (t₀.equivFin.symm j).1
  let B : ℕ → Set E := fun j ↦
    if hj : j < N then Metric.closedBall (0 : E) R ∩ Metric.ball (l ⟨j, hj⟩) δ else ∅
  have hB_meas : ∀ j : ℕ, MeasurableSet (B j) := fun j ↦ by
    by_cases hj : j < N
    · simp only [B, dite_eq_left hj]
      exact measurableSet_closedBall.inter measurableSet_ball
    · simp [B, hj]
  let A : ℕ → Set E := disjointed B
  let A_fin : Fin N → Set E := fun j ↦ A j.1
  have hA_meas : ∀ j : Fin N, MeasurableSet (A_fin j) := fun j ↦
    MeasurableSet.disjointed hB_meas j.1
  have hA_disj : Pairwise (Disjoint on A_fin) := fun i j hij ↦
    disjoint_disjointed B (Fin.val_ne_of_ne hij)
  have hA_union : (⋃ j : Fin N, A_fin j) = Metric.closedBall (0 : E) R := by
    have hsub_empty : ∀ m : ℕ, ¬ m < N → A m = ∅ := fun m hm ↦ by
      rw [← Set.subset_empty_iff]
      refine (disjointed_subset B m).trans ?_
      simp [B, hm]
    have hU : (⋃ j : Fin N, A_fin j) = ⋃ m : ℕ, A m := by
      refine Set.Subset.antisymm (Set.iUnion_subset fun j ↦ Set.subset_iUnion A j.1)
        (Set.iUnion_subset fun m ↦ ?_)
      by_cases hm : m < N
      · exact Set.subset_iUnion A_fin ⟨m, hm⟩
      · simp [hsub_empty m hm]
    rw [hU, iUnion_disjointed]
    refine Set.Subset.antisymm (Set.iUnion_subset fun m ↦ by
      by_cases hm : m < N
      · simp only [B, dite_eq_left hm]; exact Set.inter_subset_left
      · simp [B, hm]) fun y hy ↦ ?_
    have hy' := ht.2.2 hy
    simp only [Set.mem_iUnion, exists_prop] at hy'
    obtain ⟨y₀, hy₀, hyb⟩ := hy'
    let j := t₀.equivFin ⟨y₀, ht.2.1.mem_toFinset.mpr hy₀⟩
    refine Set.mem_iUnion.mpr ⟨j.1, ?_⟩
    dsimp only [B]
    rw [dite_eq_left j.isLt]
    refine ⟨hy, ?_⟩
    simpa [l, j] using hyb
  let c : Fin N → ℂ := fun j ↦ ∫ y in A_fin j, f y
  let h : SchwartzMap E ℂ := ∑ j : Fin N, c j • g.compSubConstCLM ℂ (l j)
  refine ⟨h, ?_, fun p hp ↦ ?_⟩
  · simp only [h, map_sum, map_smul]
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    rw [hvan b hb (l j), smul_zero]
  · have hk_le : 2 ^ p.1 * (1 + R + 1) ^ p.1 *
        (SchwartzMap.seminorm ℂ 0 (p.2 + 1) g + SchwartzMap.seminorm ℂ p.1 (p.2 + 1) g) ≤ M :=
      (Finset.single_le_sum (f := fun q : ℕ × ℕ ↦ 2 ^ q.1 * (1 + R + 1) ^ q.1 *
        (SchwartzMap.seminorm ℂ 0 (q.2 + 1) g + SchwartzMap.seminorm ℂ q.1 (q.2 + 1) g))
        (fun _ _ ↦ by positivity) hp).trans (by linarith)
    refine (SchwartzMap.seminorm_le_bound ℂ p.1 p.2 _
      (M := (∫ y in Metric.closedBall (0 : E) R, ‖f y‖) * (M * δ))
      (mul_nonneg hf1 (by positivity)) fun x ↦ ?_).trans_lt ?_
    · have hdiff_deriv : iteratedFDeriv ℝ p.2 (⇑(schwartzConvSet (Metric.closedBall 0 R) f g - h)) x =
          ∑ j : Fin N, ∫ y in A_fin j, f y • (iteratedFDeriv ℝ p.2 g (x - y) - iteratedFDeriv ℝ p.2 g (x - l j)) := by
        have hsub : iteratedFDeriv ℝ p.2 (⇑(schwartzConvSet (Metric.closedBall 0 R) f g - h)) x =
            iteratedFDeriv ℝ p.2 (⇑(schwartzConvSet (Metric.closedBall 0 R) f g)) x -
              iteratedFDeriv ℝ p.2 (⇑h) x :=
          iteratedFDeriv_sub_apply ((schwartzConvSet _ _ _).smooth p.2 |>.contDiffAt)
            (h.smooth p.2 |>.contDiffAt)
        rw [hsub]
        rw [show (⇑(schwartzConvSet (Metric.closedBall 0 R) f g)) =
            fun z ↦ ∫ y in Metric.closedBall 0 R, f y * g (z - y) from rfl]
        rw [schwartzConvSet_iteratedFDeriv (Metric.closedBall 0 R) f g p.2 x]
        have hh_deriv : iteratedFDeriv ℝ p.2 (⇑h) x =
            ∑ j : Fin N, c j • iteratedFDeriv ℝ p.2 g (x - l j) := by
          have hsum_d : iteratedFDeriv ℝ p.2 (fun z : E ↦ ∑ j : Fin N, c j • g.compSubConstCLM ℂ (l j) z) x =
              ∑ j : Fin N, iteratedFDeriv ℝ p.2 (fun z : E ↦ c j • g (z - l j)) x := by
            rw [iteratedFDeriv_sum (fun j _ ↦ ((g.compSubConstCLM ℂ (l j)).smooth p.2).const_smul (c j))]
            rw [Finset.sum_apply]
            rfl
          have hpt_d : ∀ j : Fin N, iteratedFDeriv ℝ p.2 (fun z : E ↦ c j • g (z - l j)) x =
              c j • iteratedFDeriv ℝ p.2 g (x - l j) := fun j ↦ by
            have hg_sub : ContDiff ℝ p.2 (fun z : E ↦ g (z - l j)) :=
              (g.smooth p.2).comp (contDiff_id.sub contDiff_const)
            rw [show (fun z : E ↦ c j • g (z - l j)) = (c j • fun z : E ↦ g (z - l j)) from rfl,
              iteratedFDeriv_const_smul_apply (hg_sub.contDiffAt (x := x))]
            congr 1
            simpa [sub_eq_add_neg] using iteratedFDeriv_comp_add_right (f := ⇑g) p.2 (-l j) x
          calc
            iteratedFDeriv ℝ p.2 (⇑h) x = iteratedFDeriv ℝ p.2 (fun z : E ↦ ∑ j : Fin N, c j • g.compSubConstCLM ℂ (l j) z) x := by
              congr 1; ext z; simp [h]
            _ = ∑ j : Fin N, iteratedFDeriv ℝ p.2 (fun z : E ↦ c j • g (z - l j)) x := hsum_d
            _ = ∑ j : Fin N, c j • iteratedFDeriv ℝ p.2 g (x - l j) := Finset.sum_congr rfl fun j _ ↦ hpt_d j
        rw [hh_deriv, ← hA_union]
        have hint_A : Integrable (fun y : E ↦ f y • iteratedFDeriv ℝ p.2 g (x - y))
            (volume.restrict (⋃ j : Fin N, A_fin j)) := by
          rw [hA_union]; exact schwartzConvSet_integrable _ f g p.2 x
        rw [integral_iUnion hA_meas hA_disj hint_A, tsum_fintype, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        have hint1 : Integrable (fun y : E ↦ f y • iteratedFDeriv ℝ p.2 g (x - y)) (volume.restrict (A_fin j)) :=
          schwartzConvSet_integrable (A_fin j) f g p.2 x
        have hint2 : Integrable (fun y : E ↦ f y • iteratedFDeriv ℝ p.2 g (x - l j)) (volume.restrict (A_fin j)) :=
          f.integrable.integrableOn.smul_const _
        rw [← integral_smul_const (iteratedFDeriv ℝ p.2 g (x - l j)) (f := fun y ↦ f y) (μ := volume.restrict (A_fin j))]
        rw [← integral_sub hint1 hint2]
        refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
        exact (smul_sub _ _ _).symm
      rw [hdiff_deriv]
      have hterm : ∀ j : Fin N, ∀ y ∈ A_fin j,
          ‖x‖ ^ p.1 * ‖f y • (iteratedFDeriv ℝ p.2 g (x - y) - iteratedFDeriv ℝ p.2 g (x - l j))‖ ≤
            ‖f y‖ * (M * δ) := fun j y hy ↦ by
        have hyB : y ∈ B j.1 := disjointed_subset B j.1 hy
        simp only [B, dite_eq_left j.isLt] at hyB
        have hy_R : ‖y‖ ≤ R := by simpa [dist_eq_norm] using hyB.1
        have hy_δ : ‖y - l j‖ < δ := by simpa [dist_eq_norm] using hyB.2
        have hδ1 : δ ≤ 1 := min_le_left _ _
        let Cg := 2 ^ p.1 * (1 + R + 1) ^ p.1 *
          (SchwartzMap.seminorm ℂ 0 (p.2 + 1) g + SchwartzMap.seminorm ℂ p.1 (p.2 + 1) g)
        have hmvt : ‖iteratedFDeriv ℝ p.2 g (x - y) - iteratedFDeriv ℝ p.2 g (x - l j)‖ ≤
            Cg / (1 + ‖x‖) ^ p.1 * ‖(x - y) - (x - l j)‖ := by
          have hy_in : x - y ∈ Metric.ball (x - y) 1 := Metric.mem_ball_self one_pos
          have hly_in : x - l j ∈ Metric.ball (x - y) 1 := by
            rw [Metric.mem_ball, dist_eq_norm]
            have heq : (x - l j) - (x - y) = y - l j := by abel
            rw [heq]
            exact hy_δ.trans_le hδ1
          refine (convex_ball (x - y) 1).norm_image_sub_le_of_norm_fderivWithin_le
            (fun z _ ↦ ((g.smooth (p.2 + 1 : ℕ)).differentiable_iteratedFDeriv (m := p.2)
              (by exact_mod_cast Nat.lt_succ_self p.2) z).differentiableWithinAt)
            (fun z hz ↦ ?_) hly_in hy_in
          rw [((g.smooth (p.2 + 1 : ℕ)).differentiable_iteratedFDeriv (m := p.2)
            (by exact_mod_cast Nat.lt_succ_self p.2) z).fderivWithin
            (Metric.isOpen_ball.uniqueDiffWithinAt hz)]
          rw [Metric.mem_ball, dist_eq_norm] at hz
          have hx_z : 1 + ‖x‖ ≤ (1 + R + 1) * (1 + ‖z‖) := by
            have h1 : ‖x‖ ≤ ‖z‖ + ‖y‖ + ‖z - (x - y)‖ := by
              calc
                ‖x‖ = ‖z - (z - (x - y)) + y‖ := by congr 1; abel
                _ ≤ ‖z - (z - (x - y))‖ + ‖y‖ := norm_add_le _ _
                _ ≤ (‖z‖ + ‖z - (x - y)‖) + ‖y‖ := by gcongr; exact norm_sub_le _ _
                _ = ‖z‖ + ‖y‖ + ‖z - (x - y)‖ := by ring
            have h2 : 1 + ‖x‖ ≤ 1 + ‖z‖ + R + 1 := by linarith
            nlinarith [norm_nonneg z]
          have hpow_xz : (1 + ‖x‖) ^ p.1 ≤ (1 + R + 1) ^ p.1 * (1 + ‖z‖) ^ p.1 :=
            (pow_le_pow_left₀ (by positivity) hx_z p.1).trans_eq (mul_pow _ _ _)
          have hfderiv_eq : ‖fderiv ℝ (iteratedFDeriv ℝ p.2 g) z‖ =
              ‖iteratedFDeriv ℝ (p.2 + 1) g z‖ := by
            let CL := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (p.2 + 1) ↦ E) ℂ
            have hcl : CL.symm (fderiv ℝ (iteratedFDeriv ℝ p.2 g) z) = iteratedFDeriv ℝ (p.2 + 1) g z := by
              ext v; simp [CL, iteratedFDeriv_succ_apply_left]
            rw [← hcl, LinearIsometryEquiv.norm_map]
          rw [hfderiv_eq, le_div_iff₀ (by positivity)]
          calc
            ‖iteratedFDeriv ℝ (p.2 + 1) g z‖ * (1 + ‖x‖) ^ p.1
                ≤ ‖iteratedFDeriv ℝ (p.2 + 1) g z‖ * ((1 + R + 1) ^ p.1 * (1 + ‖z‖) ^ p.1) := by
              gcongr
            _ ≤ ‖iteratedFDeriv ℝ (p.2 + 1) g z‖ * ((1 + R + 1) ^ p.1 * (2 ^ p.1 * (1 + ‖z‖ ^ p.1))) := by
              gcongr; exact one_add_pow_le (norm_nonneg z) p.1
            _ = 2 ^ p.1 * (1 + R + 1) ^ p.1 *
                (‖z‖ ^ 0 * ‖iteratedFDeriv ℝ (p.2 + 1) g z‖ + ‖z‖ ^ p.1 * ‖iteratedFDeriv ℝ (p.2 + 1) g z‖) := by
              ring
            _ ≤ Cg := by
              dsimp only [Cg]
              gcongr
              · simpa using SchwartzMap.le_seminorm ℂ 0 (p.2 + 1) g z
              · exact SchwartzMap.le_seminorm ℂ p.1 (p.2 + 1) g z
        have heq_diff : ‖(x - y) - (x - l j)‖ = ‖y - l j‖ := by
          rw [show (x - y) - (x - l j) = -(y - l j) by abel, norm_neg]
        have hxk_le : ‖x‖ ^ p.1 ≤ (1 + ‖x‖) ^ p.1 := pow_le_pow_left₀ (norm_nonneg x) (by linarith) p.1
        rw [norm_smul]
        calc
          ‖x‖ ^ p.1 * (‖f y‖ * ‖iteratedFDeriv ℝ p.2 g (x - y) - iteratedFDeriv ℝ p.2 g (x - l j)‖)
              = ‖f y‖ * (‖x‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 g (x - y) - iteratedFDeriv ℝ p.2 g (x - l j)‖) := by
            ring
          _ ≤ ‖f y‖ * ((1 + ‖x‖) ^ p.1 * (Cg / (1 + ‖x‖) ^ p.1 * ‖(x - y) - (x - l j)‖)) := by
            gcongr
          _ = ‖f y‖ * (Cg * ‖y - l j‖) := by
            rw [heq_diff]; field_simp [(by positivity : (1 + ‖x‖) ^ p.1 ≠ 0)]
          _ ≤ ‖f y‖ * (M * δ) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul hk_le hy_δ.le (norm_nonneg _) (by positivity)) (norm_nonneg _)
      calc
        ‖x‖ ^ p.1 * ‖∑ j : Fin N, ∫ y in A_fin j, f y • (iteratedFDeriv ℝ p.2 g (x - y) - iteratedFDeriv ℝ p.2 g (x - l j))‖
            ≤ ‖x‖ ^ p.1 * ∑ j : Fin N, ‖∫ y in A_fin j, f y • (iteratedFDeriv ℝ p.2 g (x - y) - iteratedFDeriv ℝ p.2 g (x - l j))‖ := by
          gcongr; exact norm_sum_le _ _
        _ ≤ ∑ j : Fin N, ‖x‖ ^ p.1 * ∫ y in A_fin j, ‖f y • (iteratedFDeriv ℝ p.2 g (x - y) - iteratedFDeriv ℝ p.2 g (x - l j))‖ := by
          rw [Finset.mul_sum]
          gcongr with j
          exact norm_integral_le_integral_norm _
        _ = ∑ j : Fin N, ∫ y in A_fin j, ‖x‖ ^ p.1 * ‖f y • (iteratedFDeriv ℝ p.2 g (x - y) - iteratedFDeriv ℝ p.2 g (x - l j))‖ := by
          refine Finset.sum_congr rfl fun j _ ↦ (integral_const_mul _ _).symm
        _ ≤ ∑ j : Fin N, ∫ y in A_fin j, ‖f y‖ * (M * δ) := by
          refine Finset.sum_le_sum fun j _ ↦ integral_mono_ae ?_ (f.integrable.norm.mul_const _ |>.integrableOn) ?_
          · have hint1 : Integrable (fun y : E ↦ f y • iteratedFDeriv ℝ p.2 g (x - y)) (volume.restrict (A_fin j)) :=
              schwartzConvSet_integrable (A_fin j) f g p.2 x
            have hint2 : Integrable (fun y : E ↦ f y • iteratedFDeriv ℝ p.2 g (x - l j)) (volume.restrict (A_fin j)) :=
              f.integrable.integrableOn.smul_const _
            refine ((hint1.sub hint2).norm.const_mul (‖x‖ ^ p.1)).congr (Eventually.of_forall fun y ↦ ?_)
            simp [smul_sub]
          · exact (ae_restrict_iff' (hA_meas j)).mpr (Eventually.of_forall fun y hy ↦ hterm j y hy)
        _ = (∫ y in Metric.closedBall (0 : E) R, ‖f y‖ * (M * δ)) := by
          have hint_U : Integrable (fun y : E ↦ ‖f y‖ * (M * δ)) (volume.restrict (⋃ j : Fin N, A_fin j)) := by
            rw [hA_union]; exact f.integrable.norm.mul_const _ |>.integrableOn
          have hUnion := integral_iUnion hA_meas hA_disj hint_U
          rw [hA_union] at hUnion
          rw [hUnion, tsum_fintype]
        _ = (∫ y in Metric.closedBall (0 : E) R, ‖f y‖) * (M * δ) := integral_mul_const _ _
    · calc
        (∫ y in Metric.closedBall (0 : E) R, ‖f y‖) * (M * δ)
            ≤ I₀ * (M * (ε / (2 * M * I₀))) := by
          gcongr
          · linarith [hf1]
          · exact min_le_right _ _
        _ = ε / 2 := by
          field_simp [hM.ne', hI₀.ne']
        _ < ε := half_lt_self hε

private lemma schwartzConvSet_tail_tendsto {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure]
    (f g : SchwartzMap E ℂ) (k n : ℕ) :
    Tendsto (fun R : ℝ ↦ SchwartzMap.seminorm ℂ k n
      (schwartzConvSet (Metric.closedBall 0 R)ᶜ f g)) atTop (nhds 0) := by
  let Cg := 2 ^ k * (SchwartzMap.seminorm ℂ 0 n g + SchwartzMap.seminorm ℂ k n g)
  let h : E → ℝ := fun y ↦ (1 + ‖y‖) ^ k * ‖f y‖
  have hh_int : Integrable h volume := schwartzMap_one_add_norm_pow_mul_integrable f k
  have hlim_int : Tendsto (fun R : ℝ ↦ ∫ y : E, (Metric.closedBall (0 : E) R)ᶜ.indicator h y)
      atTop (nhds 0) := by
    have hzero : ∫ y : E, (0 : ℝ) = 0 := integral_zero _ _
    rw [← hzero]
    refine tendsto_integral_filter_of_dominated_convergence (bound := h) ?_ ?_ hh_int ?_
    · refine Eventually.of_forall fun R ↦ ?_
      exact hh_int.aestronglyMeasurable.indicator measurableSet_closedBall.compl
    · refine Eventually.of_forall fun R ↦ Eventually.of_forall fun y ↦ ?_
      rw [Real.norm_of_nonneg (Set.indicator_nonneg (fun _ _ ↦ by positivity) _)]
      by_cases hy : y ∈ (Metric.closedBall (0 : E) R)ᶜ <;> simp [hy]; positivity
    · refine Eventually.of_forall fun y ↦ ?_
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioi_mem_atTop ‖y‖] with R hR
      have hy : y ∈ Metric.closedBall (0 : E) R := by simpa [dist_eq_norm] using hR.le
      simp [hy]
  have hlim_mul : Tendsto (fun R : ℝ ↦ Cg * ∫ y : E, (Metric.closedBall (0 : E) R)ᶜ.indicator h y)
      atTop (nhds 0) := by
    simpa using hlim_int.const_mul Cg
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim_mul
    (Eventually.of_forall fun _ ↦ apply_nonneg _ _) (Eventually.of_forall fun R ↦ ?_)
  refine (schwartzConvSet_seminorm_le (Metric.closedBall 0 R)ᶜ f g k n).trans_eq ?_
  congr 1
  exact (integral_indicator measurableSet_closedBall.compl).symm

private lemma schwartzConv_gauss_tendsto {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure] (f : SchwartzMap E ℂ) :
    let I₁ : ℝ := ∫ u : E, Real.exp (-‖u‖ ^ 2)
    ∀ (k n : ℕ) (ε : ℝ), 0 < ε → ∃ B : ℝ, 1 ≤ B ∧
      ∀ (b : ℝ) (hb : 0 < b), B ≤ b →
        let Ib : ℝ := (Real.sqrt b ^ Module.finrank ℝ E)⁻¹ * I₁
        SchwartzMap.seminorm ℂ k n
          ((Ib⁻¹ : ℂ) • schwartzConvSet Set.univ f ((SchwartzMap.gaussian b hb).postcompCLM Complex.ofRealCLM) - f) < ε := by
  intro I₁ k n ε hε
  have hI₁_int : Integrable (fun u : E ↦ Real.exp (-‖u‖ ^ 2)) volume :=
    ((SchwartzMap.gaussian (E := E) 1 one_pos).integrable (μ := volume)).congr
      (Eventually.of_forall fun u ↦ by simp [SchwartzMap.gaussian_apply])
  have hI₁_pos : 0 < I₁ := by
    refine integral_pos_of_integrable_nonneg_ne_zero
      (Real.continuous_exp.comp (continuous_neg.comp (continuous_norm.pow 2)))
      hI₁_int (fun u ↦ (Real.exp_pos _).le) (x := (0 : E)) (by simp)
  let Cf1 : ℝ := 4 ^ k * (SchwartzMap.seminorm ℂ 0 (n + 1) f + SchwartzMap.seminorm ℂ k (n + 1) f)
  let Cf0 : ℝ := 2 ^ k * (SchwartzMap.seminorm ℂ 0 n f + SchwartzMap.seminorm ℂ k n f)
  let r : ℝ := min (1 / 2) (ε / (4 * (Cf1 + 1)))
  have hr_pos : 0 < r := lt_min (by norm_num) (div_pos hε (by positivity))
  have hr_half : r ≤ 1 / 2 := min_le_left _ _
  have hIpoly_int : Integrable (fun u : E ↦ (1 + ‖u‖) ^ k * Real.exp (-(1 / 2 : ℝ) * ‖u‖ ^ 2)) volume := by
    have hpoly : Integrable (fun u : E ↦ 2 ^ k * ((‖u‖ ^ 0 + ‖u‖ ^ k) * Real.exp (-(1 / 2 : ℝ) * ‖u‖ ^ 2))) volume := by
      have hg0 : Integrable (fun u : E ↦ ‖u‖ ^ 0 * Real.exp (-(1 / 2 : ℝ) * ‖u‖ ^ 2)) volume := by
        simpa [SchwartzMap.gaussian_apply] using
          ((SchwartzMap.gaussian (E := E) (1 / 2) (by norm_num)).integrable_pow_mul volume 0)
      have hgk : Integrable (fun u : E ↦ ‖u‖ ^ k * Real.exp (-(1 / 2 : ℝ) * ‖u‖ ^ 2)) volume := by
        simpa [SchwartzMap.gaussian_apply] using
          ((SchwartzMap.gaussian (E := E) (1 / 2) (by norm_num)).integrable_pow_mul volume k)
      simpa [add_mul] using (hg0.add hgk).const_mul (2 ^ k)
    refine hpoly.mono ?_ (Eventually.of_forall fun u ↦ ?_)
    · exact ((continuous_const.add continuous_norm).pow k |>.mul
        (Real.continuous_exp.comp (continuous_const.mul (continuous_norm.pow 2)))).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
      calc
        (1 + ‖u‖) ^ k * Real.exp (-(1 / 2 : ℝ) * ‖u‖ ^ 2)
            ≤ (2 ^ k * (1 + ‖u‖ ^ k)) * Real.exp (-(1 / 2 : ℝ) * ‖u‖ ^ 2) := by
          gcongr; exact one_add_pow_le (norm_nonneg u) k
        _ = 2 ^ k * ((‖u‖ ^ 0 + ‖u‖ ^ k) * Real.exp (-(1 / 2 : ℝ) * ‖u‖ ^ 2)) := by
          simp only [pow_zero]; ring
  let Ipoly : ℝ := ∫ u : E, (1 + ‖u‖) ^ k * Real.exp (-(1 / 2 : ℝ) * ‖u‖ ^ 2)
  have hIpoly_nn : 0 ≤ Ipoly := integral_nonneg fun _ ↦ by positivity
  let d := Module.finrank ℝ E
  let A_const : ℝ := I₁⁻¹ * (2 * (Cf0 + 1) * (Ipoly + 1))
  have hA_nn : 0 ≤ A_const := by positivity
  let c₀ : ℝ := r ^ 2 / 2
  have hc₀ : 0 < c₀ := by positivity
  have hlim_b : Tendsto (fun b : ℝ ↦ A_const * (b + 1) ^ d * Real.exp (-c₀ * b)) atTop (nhds 0) := by
    have hbd_b : ∀ b : ℝ, 1 ≤ b → A_const * (b + 1) ^ d * Real.exp (-c₀ * b) ≤
        A_const * 2 ^ d * (((d + 1).factorial : ℝ) / c₀ ^ (d + 1)) / b := fun b hb1 ↦ by
      have hp := Real.pow_div_factorial_le_exp (c₀ * b) (by positivity) (d + 1)
      have hexp_inv : Real.exp (-c₀ * b) ≤ ((d + 1).factorial : ℝ) / (c₀ ^ (d + 1) * b ^ (d + 1)) := by
        rw [le_div_iff₀ (by positivity)]
        calc
          Real.exp (-c₀ * b) * (c₀ ^ (d + 1) * b ^ (d + 1))
              ≤ Real.exp (-c₀ * b) * (Real.exp (c₀ * b) * ((d + 1).factorial : ℝ)) := by
            rw [div_le_iff₀ (by positivity), mul_pow] at hp
            exact mul_le_mul_of_nonneg_left hp (Real.exp_pos _).le
          _ = ((d + 1).factorial : ℝ) := by
            rw [← mul_assoc, ← Real.exp_add]
            simp
      have hb_add : (b + 1) ^ d ≤ 2 ^ d * b ^ d := by
        calc
          (b + 1) ^ d ≤ (2 * b) ^ d := pow_le_pow_left₀ (by positivity) (by linarith) d
          _ = 2 ^ d * b ^ d := mul_pow 2 b d
      have hb_ne : b ≠ 0 := by linarith
      calc
        A_const * (b + 1) ^ d * Real.exp (-c₀ * b)
            ≤ A_const * (2 ^ d * b ^ d) * (((d + 1).factorial : ℝ) / (c₀ ^ (d + 1) * b ^ (d + 1))) := by
          gcongr
        _ = A_const * 2 ^ d * (((d + 1).factorial : ℝ) / c₀ ^ (d + 1)) / b := by
          rw [pow_succ b d]
          field_simp [hb_ne]
    have hb_inv : Tendsto (fun b : ℝ ↦ A_const * 2 ^ d * (((d + 1).factorial : ℝ) / c₀ ^ (d + 1)) / b)
        atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hb_inv
      ((eventually_ge_atTop (1 : ℝ)).mono fun b _ ↦ by positivity)
      ((eventually_ge_atTop (1 : ℝ)).mono fun b hb1 ↦ hbd_b b hb1)
  obtain ⟨B₀, hB₀⟩ := eventually_atTop.mp (hlim_b.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < ε / 2)))
  refine ⟨max 1 B₀, le_max_left _ _, fun b hb hbB ↦ ?_⟩
  have hb1 : 1 ≤ b := (le_max_left 1 B₀).trans hbB
  have hbB₀ : B₀ ≤ b := (le_max_right 1 B₀).trans hbB
  let Ib : ℝ := (Real.sqrt b ^ d)⁻¹ * I₁
  have hIb_eq : ∫ u : E, Real.exp (-b * ‖u‖ ^ 2) = Ib := by
    have hsc := Measure.integral_comp_smul_of_nonneg (μ := volume)
      (fun u : E ↦ Real.exp (-‖u‖ ^ 2)) (Real.sqrt b) (hR := Real.sqrt_nonneg b)
    have hfun : (fun u : E ↦ Real.exp (-‖Real.sqrt b • u‖ ^ 2)) =
        fun u : E ↦ Real.exp (-b * ‖u‖ ^ 2) := by
      ext u
      rw [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg b), mul_pow, Real.sq_sqrt hb.le]
      ring_nf
    rw [← hfun]
    simpa [Ib, d, smul_eq_mul] using hsc
  have hIb_pos : 0 < Ib := mul_pos (inv_pos.mpr (pow_pos (Real.sqrt_pos.mpr hb) d)) hI₁_pos
  let g : SchwartzMap E ℂ := (SchwartzMap.gaussian b hb).postcompCLM Complex.ofRealCLM
  have hg_intR : Integrable (fun u : E ↦ Real.exp (-b * ‖u‖ ^ 2)) volume :=
    ((SchwartzMap.gaussian (E := E) b hb).integrable (μ := volume)).congr
      (Eventually.of_forall fun u ↦ by simp [SchwartzMap.gaussian_apply])
  have hbound_eps : Cf1 * r + A_const * (b + 1) ^ d * Real.exp (-c₀ * b) < ε := by
    have h1 : Cf1 * r ≤ ε / 4 := by
      calc
        Cf1 * r ≤ (Cf1 + 1) * (ε / (4 * (Cf1 + 1))) := by
          gcongr
          · linarith
          · exact min_le_right _ _
        _ = ε / 4 := by field_simp [(by positivity : Cf1 + 1 ≠ 0)]
    have h2 : A_const * (b + 1) ^ d * Real.exp (-c₀ * b) < ε / 2 := hB₀ b hbB₀
    linarith
  refine (SchwartzMap.seminorm_le_bound ℂ k n _
    (M := Cf1 * r + A_const * (b + 1) ^ d * Real.exp (-c₀ * b))
    (by positivity) fun x ↦ ?_).trans_lt hbound_eps
  have hcomm : schwartzConvSet Set.univ f g = schwartzConvSet Set.univ g f :=
    schwartzConvSet_univ_comm f g
  have hdiff_deriv : iteratedFDeriv ℝ n (⇑((Ib⁻¹ : ℂ) • schwartzConvSet Set.univ f g - f)) x =
      (Ib⁻¹ : ℂ) • ∫ u : E, g u • (iteratedFDeriv ℝ n f (x - u) - iteratedFDeriv ℝ n f x) := by
    have hsub : iteratedFDeriv ℝ n (⇑((Ib⁻¹ : ℂ) • schwartzConvSet Set.univ f g - f)) x =
        (Ib⁻¹ : ℂ) • iteratedFDeriv ℝ n (⇑(schwartzConvSet Set.univ g f)) x -
          iteratedFDeriv ℝ n (⇑f) x := by
      rw [hcomm]
      have h1 := iteratedFDeriv_sub_apply
        (((Ib⁻¹ : ℂ) • schwartzConvSet Set.univ g f).smooth n |>.contDiffAt (x := x))
        (f.smooth n |>.contDiffAt (x := x))
      have h2 : iteratedFDeriv ℝ n (⇑((Ib⁻¹ : ℂ) • schwartzConvSet Set.univ g f)) x =
          (Ib⁻¹ : ℂ) • iteratedFDeriv ℝ n (⇑(schwartzConvSet Set.univ g f)) x :=
        iteratedFDeriv_const_smul_apply ((schwartzConvSet Set.univ g f).smooth n |>.contDiffAt)
      exact h1.trans (by rw [h2])
    rw [hsub, show (⇑(schwartzConvSet Set.univ g f)) = fun z ↦ ∫ u in Set.univ, g u * f (z - u) from rfl,
      schwartzConvSet_iteratedFDeriv Set.univ g f n x, Measure.restrict_univ]
    have hconst_int : ∫ u : E, g u • iteratedFDeriv ℝ n f x = (Ib : ℂ) • iteratedFDeriv ℝ n f x := by
      rw [integral_smul_const]
      congr 1
      have hcoe : (fun u : E ↦ g u) = fun u : E ↦ Complex.ofRealCLM (Real.exp (-b * ‖u‖ ^ 2)) := by
        ext u; simp [g, SchwartzMap.gaussian_apply]
      rw [hcoe, Complex.ofRealCLM.integral_comp_comm hg_intR, Complex.ofRealCLM_apply, hIb_eq]
    have hsm1 : Integrable (fun u : E ↦ g u • iteratedFDeriv ℝ n f (x - u)) volume := by
      simpa only [Measure.restrict_univ] using schwartzConvSet_integrable Set.univ g f n x
    have hsm2 : Integrable (fun u : E ↦ g u • iteratedFDeriv ℝ n f x) volume :=
      g.integrable.smul_const _
    calc
      ((Ib⁻¹ : ℂ) • ∫ y : E, g y • iteratedFDeriv ℝ n f (x - y)) - iteratedFDeriv ℝ n f x
          = ((Ib⁻¹ : ℂ) • ∫ y : E, g y • iteratedFDeriv ℝ n f (x - y)) -
              ((Ib⁻¹ : ℂ) • ∫ y : E, g y • iteratedFDeriv ℝ n f x) := by
            rw [hconst_int, smul_smul, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hIb_pos.ne'),
              one_smul]
      _ = (Ib⁻¹ : ℂ) • ∫ u : E, g u • (iteratedFDeriv ℝ n f (x - u) - iteratedFDeriv ℝ n f x) := by
            rw [← smul_sub, ← integral_sub hsm1 hsm2]
            refine congrArg ((Ib⁻¹ : ℂ) • ·) (integral_congr_ae (Eventually.of_forall fun u ↦ ?_))
            exact (smul_sub _ _ _).symm
  rw [hdiff_deriv, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hIb_pos.le]
  have hpt : ∀ u : E, ‖x‖ ^ k * (Real.exp (-b * ‖u‖ ^ 2) *
      ‖iteratedFDeriv ℝ n f (x - u) - iteratedFDeriv ℝ n f x‖) ≤
      (Cf1 * r) * Real.exp (-b * ‖u‖ ^ 2) +
        (2 * (Cf0 + 1) * Real.exp (-c₀ * b)) * ((1 + ‖u‖) ^ k * Real.exp (-(1 / 2 : ℝ) * ‖u‖ ^ 2)) := by
    intro u
    by_cases hu : ‖u‖ ≤ r
    · have hu_lt : ‖u‖ < 1 := hu.trans_lt (hr_half.trans_lt (by norm_num))
      have hmvt : ‖iteratedFDeriv ℝ n f (x - u) - iteratedFDeriv ℝ n f x‖ ≤
          Cf1 / (1 + ‖x‖) ^ k * ‖(x - u) - x‖ := by
        have hx_in : x ∈ Metric.ball x 1 := Metric.mem_ball_self one_pos
        have hxu_in : x - u ∈ Metric.ball x 1 := by
          rw [Metric.mem_ball, dist_eq_norm]
          simpa using hu_lt
        refine (convex_ball x 1).norm_image_sub_le_of_norm_fderivWithin_le
          (fun z _ ↦ ((f.smooth (n + 1 : ℕ)).differentiable_iteratedFDeriv (m := n)
            (by exact_mod_cast Nat.lt_succ_self n) z).differentiableWithinAt)
          (fun z hz ↦ ?_) hx_in hxu_in
        rw [((f.smooth (n + 1 : ℕ)).differentiable_iteratedFDeriv (m := n)
          (by exact_mod_cast Nat.lt_succ_self n) z).fderivWithin
          (Metric.isOpen_ball.uniqueDiffWithinAt hz)]
        rw [Metric.mem_ball, dist_eq_norm] at hz
        have hxz : 1 + ‖x‖ ≤ 2 * (1 + ‖z‖) := by
          have : ‖x‖ ≤ ‖z‖ + ‖z - x‖ := by
            calc
              ‖x‖ = ‖z - (z - x)‖ := by rw [sub_sub_cancel]
              _ ≤ ‖z‖ + ‖z - x‖ := norm_sub_le z (z - x)
          have h1 : ‖z - x‖ < 1 := hz
          linarith [norm_nonneg z]
        have hfderiv_eq : ‖fderiv ℝ (iteratedFDeriv ℝ n f) z‖ = ‖iteratedFDeriv ℝ (n + 1) f z‖ := by
          let CL := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) ↦ E) ℂ
          have hcl : CL.symm (fderiv ℝ (iteratedFDeriv ℝ n f) z) = iteratedFDeriv ℝ (n + 1) f z := by
            ext v; simp [CL, iteratedFDeriv_succ_apply_left]
          rw [← hcl, LinearIsometryEquiv.norm_map]
        rw [hfderiv_eq, le_div_iff₀ (by positivity)]
        calc
          ‖iteratedFDeriv ℝ (n + 1) f z‖ * (1 + ‖x‖) ^ k
              ≤ ‖iteratedFDeriv ℝ (n + 1) f z‖ * (2 ^ k * (1 + ‖z‖) ^ k) := by
            gcongr; exact (pow_le_pow_left₀ (by positivity) hxz k).trans_eq (mul_pow _ _ _)
          _ ≤ ‖iteratedFDeriv ℝ (n + 1) f z‖ * (2 ^ k * (2 ^ k * (1 + ‖z‖ ^ k))) := by
            gcongr; exact one_add_pow_le (norm_nonneg z) k
          _ = 4 ^ k * (‖z‖ ^ 0 * ‖iteratedFDeriv ℝ (n + 1) f z‖ + ‖z‖ ^ k * ‖iteratedFDeriv ℝ (n + 1) f z‖) := by
            rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]
            ring
          _ ≤ Cf1 := by
            dsimp only [Cf1]
            gcongr
            · simpa using SchwartzMap.le_seminorm ℂ 0 (n + 1) f z
            · exact SchwartzMap.le_seminorm ℂ k (n + 1) f z
      have hdiff_xu : ‖(x - u) - x‖ = ‖u‖ := by simp
      have hxk : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k := pow_le_pow_left₀ (norm_nonneg x) (by linarith) k
      have hfirst : ‖x‖ ^ k * (Real.exp (-b * ‖u‖ ^ 2) * ‖iteratedFDeriv ℝ n f (x - u) - iteratedFDeriv ℝ n f x‖) ≤
          (Cf1 * r) * Real.exp (-b * ‖u‖ ^ 2) := by
        calc
          ‖x‖ ^ k * (Real.exp (-b * ‖u‖ ^ 2) * ‖iteratedFDeriv ℝ n f (x - u) - iteratedFDeriv ℝ n f x‖)
              = Real.exp (-b * ‖u‖ ^ 2) * (‖x‖ ^ k * ‖iteratedFDeriv ℝ n f (x - u) - iteratedFDeriv ℝ n f x‖) := by
            ring
          _ ≤ Real.exp (-b * ‖u‖ ^ 2) * ((1 + ‖x‖) ^ k * (Cf1 / (1 + ‖x‖) ^ k * ‖(x - u) - x‖)) := by
            gcongr
          _ = Real.exp (-b * ‖u‖ ^ 2) * (Cf1 * ‖u‖) := by
            rw [hdiff_xu]; field_simp [(by positivity : (1 + ‖x‖) ^ k ≠ 0)]
          _ ≤ (Cf1 * r) * Real.exp (-b * ‖u‖ ^ 2) := by
            rw [mul_comm (Real.exp _)]
            gcongr
      exact hfirst.trans (le_add_of_nonneg_right (by positivity))
    · have hu_gt : r < ‖u‖ := lt_of_not_ge hu
      have hx_u : 1 + ‖x‖ ≤ (1 + ‖x - u‖) * (1 + ‖u‖) := by
        have htri : ‖x‖ ≤ ‖x - u‖ + ‖u‖ := norm_le_norm_sub_add x u
        nlinarith [norm_nonneg (x - u), norm_nonneg u]
      have hxk_u : ‖x‖ ^ k ≤ (1 + ‖x - u‖) ^ k * (1 + ‖u‖) ^ k :=
        (pow_le_pow_left₀ (norm_nonneg x) (by linarith) k).trans
          ((pow_le_pow_left₀ (by positivity) hx_u k).trans_eq (mul_pow _ _ _))
      have hfxu : (1 + ‖x - u‖) ^ k * ‖iteratedFDeriv ℝ n f (x - u)‖ ≤ Cf0 := by
        calc
          (1 + ‖x - u‖) ^ k * ‖iteratedFDeriv ℝ n f (x - u)‖
              ≤ 2 ^ k * (1 + ‖x - u‖ ^ k) * ‖iteratedFDeriv ℝ n f (x - u)‖ := by
            gcongr; exact one_add_pow_le (norm_nonneg (x - u)) k
          _ = 2 ^ k * (‖x - u‖ ^ 0 * ‖iteratedFDeriv ℝ n f (x - u)‖ +
              ‖x - u‖ ^ k * ‖iteratedFDeriv ℝ n f (x - u)‖) := by ring
          _ ≤ Cf0 := by
            dsimp only [Cf0]
            gcongr
            · simpa using SchwartzMap.le_seminorm ℂ 0 n f (x - u)
            · exact SchwartzMap.le_seminorm ℂ k n f (x - u)
      have hfx : ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ Cf0 := by
        calc
          ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ Cf0 / 2 ^ k := by
            have h1 := SchwartzMap.le_seminorm ℂ k n f x
            calc
              ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ SchwartzMap.seminorm ℂ k n f := h1
              _ ≤ SchwartzMap.seminorm ℂ 0 n f + SchwartzMap.seminorm ℂ k n f :=
                le_add_of_nonneg_left (apply_nonneg _ _)
              _ = Cf0 / 2 ^ k := by
                dsimp only [Cf0]
                have h2ne : (2 : ℝ) ^ k ≠ 0 := by positivity
                field_simp [h2ne]
          _ ≤ Cf0 := by
            dsimp only [Cf0]
            have hpow : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
            have hnon : 0 ≤ SchwartzMap.seminorm ℂ 0 n f + SchwartzMap.seminorm ℂ k n f := by
              have := apply_nonneg (SchwartzMap.seminorm ℂ 0 n) f
              have := apply_nonneg (SchwartzMap.seminorm ℂ k n) f
              linarith
            calc
              2 ^ k * (SchwartzMap.seminorm ℂ 0 n f + SchwartzMap.seminorm ℂ k n f) / 2 ^ k
                  = SchwartzMap.seminorm ℂ 0 n f + SchwartzMap.seminorm ℂ k n f := by
                field_simp [(by positivity : (2 : ℝ) ^ k ≠ 0)]
              _ ≤ 2 ^ k * (SchwartzMap.seminorm ℂ 0 n f + SchwartzMap.seminorm ℂ k n f) :=
                le_mul_of_one_le_left hnon hpow
      have hsub_bd : ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f (x - u) - iteratedFDeriv ℝ n f x‖ ≤
          2 * Cf0 * (1 + ‖u‖) ^ k := by
        have htri : ‖iteratedFDeriv ℝ n f (x - u) - iteratedFDeriv ℝ n f x‖ ≤
            ‖iteratedFDeriv ℝ n f (x - u)‖ + ‖iteratedFDeriv ℝ n f x‖ := norm_sub_le _ _
        have h1 : ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f (x - u)‖ ≤ Cf0 * (1 + ‖u‖) ^ k := by
          calc
            ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f (x - u)‖
                ≤ (1 + ‖x - u‖) ^ k * (1 + ‖u‖) ^ k * ‖iteratedFDeriv ℝ n f (x - u)‖ := by gcongr
            _ = ((1 + ‖x - u‖) ^ k * ‖iteratedFDeriv ℝ n f (x - u)‖) * (1 + ‖u‖) ^ k := by ring
            _ ≤ Cf0 * (1 + ‖u‖) ^ k := by gcongr
        have h2 : ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ Cf0 * (1 + ‖u‖) ^ k :=
          hfx.trans (le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by linarith [norm_nonneg u])))
        calc
          ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f (x - u) - iteratedFDeriv ℝ n f x‖
              ≤ ‖x‖ ^ k * (‖iteratedFDeriv ℝ n f (x - u)‖ + ‖iteratedFDeriv ℝ n f x‖) := by gcongr
          _ = ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f (x - u)‖ + ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ := by ring
          _ ≤ Cf0 * (1 + ‖u‖) ^ k + Cf0 * (1 + ‖u‖) ^ k := add_le_add h1 h2
          _ = 2 * Cf0 * (1 + ‖u‖) ^ k := by ring
      have hexp_split : Real.exp (-b * ‖u‖ ^ 2) ≤
          Real.exp (-c₀ * b) * Real.exp (-(1 / 2 : ℝ) * ‖u‖ ^ 2) := by
        rw [← Real.exp_add, Real.exp_le_exp]
        have hr2 : r ^ 2 ≤ ‖u‖ ^ 2 := pow_le_pow_left₀ hr_pos.le hu_gt.le 2
        have hbu : -(b / 2) * ‖u‖ ^ 2 ≤ -(1 / 2 : ℝ) * ‖u‖ ^ 2 := by
          have hb2 : (1 / 2 : ℝ) ≤ b / 2 := by linarith
          calc
            -(b / 2) * ‖u‖ ^ 2 = -((b / 2) * ‖u‖ ^ 2) := by ring
            _ ≤ -((1 / 2 : ℝ) * ‖u‖ ^ 2) := neg_le_neg (mul_le_mul_of_nonneg_right hb2 (sq_nonneg _))
            _ = -(1 / 2 : ℝ) * ‖u‖ ^ 2 := by ring
        have hbr : -(b / 2) * ‖u‖ ^ 2 ≤ -c₀ * b := by
          calc
            -(b / 2) * ‖u‖ ^ 2 = -((b / 2) * ‖u‖ ^ 2) := by ring
            _ ≤ -((b / 2) * r ^ 2) := neg_le_neg (mul_le_mul_of_nonneg_left hr2 (by positivity))
            _ = -c₀ * b := by dsimp only [c₀]; ring
        calc
          -b * ‖u‖ ^ 2 = -(b / 2) * ‖u‖ ^ 2 + -(b / 2) * ‖u‖ ^ 2 := by ring
          _ ≤ -c₀ * b + -(1 / 2 : ℝ) * ‖u‖ ^ 2 := add_le_add hbr hbu
      have hsecond : ‖x‖ ^ k * (Real.exp (-b * ‖u‖ ^ 2) * ‖iteratedFDeriv ℝ n f (x - u) - iteratedFDeriv ℝ n f x‖) ≤
          (2 * (Cf0 + 1) * Real.exp (-c₀ * b)) * ((1 + ‖u‖) ^ k * Real.exp (-(1 / 2 : ℝ) * ‖u‖ ^ 2)) := by
        calc
          ‖x‖ ^ k * (Real.exp (-b * ‖u‖ ^ 2) * ‖iteratedFDeriv ℝ n f (x - u) - iteratedFDeriv ℝ n f x‖)
              = Real.exp (-b * ‖u‖ ^ 2) * (‖x‖ ^ k * ‖iteratedFDeriv ℝ n f (x - u) - iteratedFDeriv ℝ n f x‖) := by
            ring
          _ ≤ (Real.exp (-c₀ * b) * Real.exp (-(1 / 2 : ℝ) * ‖u‖ ^ 2)) * (2 * Cf0 * (1 + ‖u‖) ^ k) := by
            gcongr
          _ ≤ (2 * (Cf0 + 1) * Real.exp (-c₀ * b)) * ((1 + ‖u‖) ^ k * Real.exp (-(1 / 2 : ℝ) * ‖u‖ ^ 2)) := by
            have : (Cf0 : ℝ) ≤ Cf0 + 1 := le_add_of_nonneg_right zero_le_one
            calc
              Real.exp (-c₀ * b) * Real.exp (-(1 / 2 : ℝ) * ‖u‖ ^ 2) * (2 * Cf0 * (1 + ‖u‖) ^ k)
                  ≤ Real.exp (-c₀ * b) * Real.exp (-(1 / 2 : ℝ) * ‖u‖ ^ 2) * (2 * (Cf0 + 1) * (1 + ‖u‖) ^ k) := by
                gcongr
              _ = _ := by ring
      exact hsecond.trans (le_add_of_nonneg_left (by positivity))
  have hint_lhs : Integrable (fun u : E ↦ ‖x‖ ^ k * (Real.exp (-b * ‖u‖ ^ 2) *
      ‖iteratedFDeriv ℝ n f (x - u) - iteratedFDeriv ℝ n f x‖)) volume := by
    have hsub_int : Integrable (fun u : E ↦ g u • (iteratedFDeriv ℝ n f (x - u) - iteratedFDeriv ℝ n f x)) volume := by
      have h1 : Integrable (fun u : E ↦ g u • iteratedFDeriv ℝ n f (x - u)) volume := by
        simpa only [Measure.restrict_univ] using schwartzConvSet_integrable Set.univ g f n x
      have h2 : Integrable (fun u : E ↦ g u • iteratedFDeriv ℝ n f x) volume :=
        g.integrable.smul_const _
      refine (h1.sub h2).congr (Eventually.of_forall fun u ↦ ?_)
      simp [smul_sub]
    refine (hsub_int.norm.const_mul (‖x‖ ^ k)).congr (Eventually.of_forall fun u ↦ ?_)
    simp only [g, SchwartzMap.postcompCLM_apply, Complex.ofRealCLM_apply, SchwartzMap.gaussian_apply,
      norm_smul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  have hint_rhs : Integrable (fun u : E ↦ (Cf1 * r) * Real.exp (-b * ‖u‖ ^ 2) +
      (2 * (Cf0 + 1) * Real.exp (-c₀ * b)) * ((1 + ‖u‖) ^ k * Real.exp (-(1 / 2 : ℝ) * ‖u‖ ^ 2))) volume :=
    (hg_intR.const_mul _).add (hIpoly_int.const_mul _)
  have hsqrt_le : Real.sqrt b ^ d ≤ (b + 1) ^ d := by
    refine pow_le_pow_left₀ (Real.sqrt_nonneg b) ?_ d
    nlinarith [Real.sqrt_nonneg b, Real.sq_sqrt hb.le]
  calc
    ‖x‖ ^ k * (Ib⁻¹ * ‖∫ u : E, g u • (iteratedFDeriv ℝ n f (x - u) - iteratedFDeriv ℝ n f x)‖)
        ≤ Ib⁻¹ * (‖x‖ ^ k * ∫ u : E, ‖g u • (iteratedFDeriv ℝ n f (x - u) - iteratedFDeriv ℝ n f x)‖) := by
      rw [mul_left_comm]
      gcongr
      exact norm_integral_le_integral_norm _
    _ = Ib⁻¹ * ∫ u : E, ‖x‖ ^ k * (Real.exp (-b * ‖u‖ ^ 2) *
          ‖iteratedFDeriv ℝ n f (x - u) - iteratedFDeriv ℝ n f x‖) := by
      congr 1
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun u ↦ ?_)
      simp only [g, SchwartzMap.postcompCLM_apply, Complex.ofRealCLM_apply, SchwartzMap.gaussian_apply,
        norm_smul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    _ ≤ Ib⁻¹ * ∫ u : E, ((Cf1 * r) * Real.exp (-b * ‖u‖ ^ 2) +
          (2 * (Cf0 + 1) * Real.exp (-c₀ * b)) * ((1 + ‖u‖) ^ k * Real.exp (-(1 / 2 : ℝ) * ‖u‖ ^ 2))) :=
      mul_le_mul_of_nonneg_left (integral_mono hint_lhs hint_rhs hpt) (inv_nonneg.mpr hIb_pos.le)
    _ = Ib⁻¹ * ((Cf1 * r) * Ib + (2 * (Cf0 + 1) * Real.exp (-c₀ * b)) * Ipoly) := by
      rw [integral_add (hg_intR.const_mul _) (hIpoly_int.const_mul _),
        integral_const_mul, integral_const_mul, hIb_eq]
    _ = Cf1 * r + (Real.sqrt b ^ d * I₁⁻¹) * (2 * (Cf0 + 1) * Real.exp (-c₀ * b) * Ipoly) := by
      have hIb_inv : Ib⁻¹ = Real.sqrt b ^ d * I₁⁻¹ := by
        dsimp only [Ib]
        rw [mul_inv, inv_inv]
      calc
        Ib⁻¹ * ((Cf1 * r) * Ib + (2 * (Cf0 + 1) * Real.exp (-c₀ * b)) * Ipoly)
            = (Ib⁻¹ * Ib) * (Cf1 * r) + Ib⁻¹ * (2 * (Cf0 + 1) * Real.exp (-c₀ * b) * Ipoly) := by
          ring
        _ = Cf1 * r + (Real.sqrt b ^ d * I₁⁻¹) * (2 * (Cf0 + 1) * Real.exp (-c₀ * b) * Ipoly) := by
          rw [inv_mul_cancel₀ hIb_pos.ne', one_mul, hIb_inv]
    _ ≤ Cf1 * r + A_const * (b + 1) ^ d * Real.exp (-c₀ * b) := by
      refine add_le_add le_rfl ?_
      calc
        Real.sqrt b ^ d * I₁⁻¹ * (2 * (Cf0 + 1) * Real.exp (-c₀ * b) * Ipoly)
            ≤ (b + 1) ^ d * I₁⁻¹ * (2 * (Cf0 + 1) * Real.exp (-c₀ * b) * (Ipoly + 1)) := by
          gcongr
          linarith
        _ = A_const * (b + 1) ^ d * Real.exp (-c₀ * b) := by
          dsimp only [A_const]; ring

private theorem schwartzDual_eq_zero_of_translate_gauss {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure]
    (T : StrongDual ℂ (SchwartzMap E ℂ))
    (hvan : ∀ (b : ℝ) (hb : 0 < b) (y : E),
      T (((SchwartzMap.gaussian b hb).postcompCLM Complex.ofRealCLM).compSubConstCLM ℂ y) = 0) :
    T = 0 := by
  ext f
  rw [zero_apply]
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ E ℂ)
    ((normSeminorm ℂ ℂ).comp T.toLinearMap) T.continuous.norm
  rw [← norm_eq_zero]
  refine le_antisymm ?_ (norm_nonneg _)
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  rw [zero_add]
  let δ' : ℝ := ε / ((C : ℝ) + 1)
  have hδ' : 0 < δ' := by positivity
  let I₁ : ℝ := ∫ u : E, Real.exp (-‖u‖ ^ 2)
  have hB_each : ∀ p ∈ s, ∃ B : ℝ, 1 ≤ B ∧
      ∀ (b : ℝ) (hb : 0 < b), B ≤ b →
        let Ib : ℝ := (Real.sqrt b ^ Module.finrank ℝ E)⁻¹ * I₁
        SchwartzMap.seminorm ℂ p.1 p.2
          ((Ib⁻¹ : ℂ) • schwartzConvSet Set.univ f ((SchwartzMap.gaussian b hb).postcompCLM Complex.ofRealCLM) - f) <
            δ' / 3 :=
    fun p _ ↦ schwartzConv_gauss_tendsto f p.1 p.2 (δ' / 3) (by positivity)
  choose B_fn hB1 hB_bd using fun p : s ↦ hB_each p.1 p.2
  let b : ℝ := 1 + ∑ p : s, B_fn p
  have hb1 : 1 ≤ b := by
    have hnn : 0 ≤ ∑ p : s, B_fn p := Finset.sum_nonneg fun p _ ↦ le_trans zero_le_one (hB1 p)
    linarith
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one hb1
  have hb_ge : ∀ p : s, B_fn p ≤ b := fun p ↦ by
    have hnn : 0 ≤ ∑ q : s, B_fn q := Finset.sum_nonneg fun q _ ↦ le_trans zero_le_one (hB1 q)
    have hle : B_fn p ≤ ∑ q : s, B_fn q :=
      Finset.single_le_sum (fun q _ ↦ le_trans zero_le_one (hB1 q)) (Finset.mem_univ p)
    linarith
  let Ib : ℝ := (Real.sqrt b ^ Module.finrank ℝ E)⁻¹ * I₁
  have hI₁_int : Integrable (fun u : E ↦ Real.exp (-‖u‖ ^ 2)) volume :=
    ((SchwartzMap.gaussian (E := E) 1 one_pos).integrable (μ := volume)).congr
      (Eventually.of_forall fun u ↦ by simp [SchwartzMap.gaussian_apply])
  have hI₁_pos : 0 < I₁ := by
    refine integral_pos_of_integrable_nonneg_ne_zero
      (Real.continuous_exp.comp (continuous_neg.comp (continuous_norm.pow 2)))
      hI₁_int (fun u ↦ (Real.exp_pos _).le) (x := (0 : E)) (by simp)
  have hIb_pos : 0 < Ib := mul_pos (inv_pos.mpr (pow_pos (Real.sqrt_pos.mpr hb) _)) hI₁_pos
  let g : SchwartzMap E ℂ := (SchwartzMap.gaussian b hb).postcompCLM Complex.ofRealCLM
  let η : ℝ := δ' / (3 * (Ib⁻¹ + 1))
  have hη : 0 < η := by positivity
  have hR_each : ∀ p : s, ∃ R₀ : ℝ, 0 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      SchwartzMap.seminorm ℂ p.1.1 p.1.2 (schwartzConvSet (Metric.closedBall 0 R)ᶜ f g) < η :=
    fun p ↦ by
      obtain ⟨R₀, hR₀⟩ := eventually_atTop.mp
        ((schwartzConvSet_tail_tendsto f g p.1.1 p.1.2).eventually (Iio_mem_nhds hη))
      exact ⟨max R₀ 0, le_max_right _ _, fun R hR ↦ hR₀ R ((le_max_left R₀ 0).trans hR)⟩
  choose R_fn hR0 hR_bd using hR_each
  let R : ℝ := ∑ p : s, R_fn p
  have hR : 0 ≤ R := Finset.sum_nonneg fun p _ ↦ hR0 p
  have hR_ge : ∀ p : s, R_fn p ≤ R := fun p ↦
    Finset.single_le_sum (fun q _ ↦ hR0 q) (Finset.mem_univ p)
  obtain ⟨h₀, hh₀_van, hh₀_bd⟩ := schwartzDual_eq_zero_of_ball_approx T hvan f b hb R hR s η hη
  let h : SchwartzMap E ℂ := (Ib⁻¹ : ℂ) • h₀
  have hT_h : T h = 0 := by simp [h, map_smul, hh₀_van]
  have h_sup : (s.sup (schwartzSeminormFamily ℂ E ℂ)) (f - h) ≤ δ' := by
    rw [Seminorm.finset_sup_apply, ← Real.coe_toNNReal δ' hδ'.le, NNReal.coe_le_coe]
    refine Finset.sup_le fun p hp ↦ ?_
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal δ' hδ'.le]
    let conv : SchwartzMap E ℂ := (Ib⁻¹ : ℂ) • schwartzConvSet Set.univ f g
    let trunc : SchwartzMap E ℂ := (Ib⁻¹ : ℂ) • schwartzConvSet (Metric.closedBall 0 R) f g
    have hsplit : f - h = (f - conv) + (conv - trunc) + (trunc - h) := by abel
    have h1 : SchwartzMap.seminorm ℂ p.1 p.2 (f - conv) < δ' / 3 := by
      rw [← map_neg_eq_map (SchwartzMap.seminorm ℂ p.1 p.2) (f - conv), neg_sub]
      exact hB_bd ⟨p, hp⟩ b hb (hb_ge ⟨p, hp⟩)
    have h2 : SchwartzMap.seminorm ℂ p.1 p.2 (conv - trunc) ≤ δ' / 3 := by
      have heq : conv - trunc = (Ib⁻¹ : ℂ) • schwartzConvSet (Metric.closedBall 0 R)ᶜ f g := by
        rw [← smul_sub, schwartzConvSet_compl_eq_sub measurableSet_closedBall]
      rw [heq, map_smul_eq_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hIb_pos.le]
      have hbd := (hR_bd ⟨p, hp⟩ R (hR_ge ⟨p, hp⟩)).le
      calc
        Ib⁻¹ * SchwartzMap.seminorm ℂ p.1 p.2 (schwartzConvSet (Metric.closedBall 0 R)ᶜ f g)
            ≤ (Ib⁻¹ + 1) * (δ' / (3 * (Ib⁻¹ + 1))) := by gcongr; linarith
        _ = δ' / 3 := by field_simp [(by positivity : Ib⁻¹ + 1 ≠ 0)]
    have h3 : SchwartzMap.seminorm ℂ p.1 p.2 (trunc - h) ≤ δ' / 3 := by
      have heq : trunc - h =
          (Ib⁻¹ : ℂ) • (schwartzConvSet (Metric.closedBall 0 R) f g - h₀) := by
        simp [trunc, h, smul_sub]
      rw [heq, map_smul_eq_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hIb_pos.le]
      have hbd := (hh₀_bd p hp).le
      calc
        Ib⁻¹ * SchwartzMap.seminorm ℂ p.1 p.2 (schwartzConvSet (Metric.closedBall 0 R) f g - h₀)
            ≤ (Ib⁻¹ + 1) * (δ' / (3 * (Ib⁻¹ + 1))) := by gcongr; linarith
        _ = δ' / 3 := by field_simp [(by positivity : Ib⁻¹ + 1 ≠ 0)]
    change SchwartzMap.seminorm ℂ p.1 p.2 (f - h) ≤ δ'
    calc
      SchwartzMap.seminorm ℂ p.1 p.2 (f - h)
          ≤ SchwartzMap.seminorm ℂ p.1 p.2 (f - conv) +
              SchwartzMap.seminorm ℂ p.1 p.2 (conv - trunc) +
              SchwartzMap.seminorm ℂ p.1 p.2 (trunc - h) := by
        rw [hsplit]
        refine (map_add_le_add _ _ _).trans ?_
        gcongr
        exact map_add_le_add _ _ _
      _ ≤ δ' / 3 + δ' / 3 + δ' / 3 := by linarith
      _ = δ' := by ring
  calc
    ‖T f‖ = ‖T (f - h)‖ := by rw [map_sub, hT_h, sub_zero]
    _ ≤ (C : ℝ) * (s.sup (schwartzSeminormFamily ℂ E ℂ)) (f - h) := hC (f - h)
    _ ≤ (C : ℝ) * δ' := mul_le_mul_of_nonneg_left h_sup C.coe_nonneg
    _ ≤ ε := by
      dsimp only [δ']
      calc
        (C : ℝ) * (ε / ((C : ℝ) + 1)) ≤ ((C : ℝ) + 1) * (ε / ((C : ℝ) + 1)) := by
          gcongr; linarith
        _ = ε := by field_simp [(by positivity : (C : ℝ) + 1 ≠ 0)]

end Step3b

section Step3c

private def unitScaleInvCLE {K : Type*} [NormedField K] [NormedAlgebra ℝ K] (g : Kˣ) : K ≃L[ℝ] K :=
  { toFun := fun x ↦ (g⁻¹ : K) * x
    map_add' := fun x y ↦ mul_add _ x y
    map_smul' := fun r x ↦ by
      simp only [RingHom.id_apply, Algebra.smul_def]
      ring
    invFun := fun x ↦ (g : K) * x
    left_inv := fun x ↦ by simp
    right_inv := fun x ↦ by simp
    continuous_toFun := continuous_const.mul continuous_id
    continuous_invFun := continuous_const.mul continuous_id }

@[simp]
private lemma unitScaleInvCLE_apply {K : Type*} [NormedField K] [NormedAlgebra ℝ K]
    (g : Kˣ) (x : K) : unitScaleInvCLE g x = (g⁻¹ : K) * x := rfl

private lemma infiniteNorm_ofReal_unit (w : InfinitePlace F) (hw : w.IsReal) (g : ℝˣ) :
    (((Units.map nnNormHom.toMonoidHom ^ InfinitePlace.mult w : w.Completionˣ →* ℝ≥0ˣ)
      (Units.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toMonoidHom g) : ℝ≥0) : ℝ) =
      ‖(g : ℝ)‖ := by
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  have hn : ‖e.symm (g : ℝ)‖ = ‖(g : ℝ)‖ :=
    (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.isometry.norm_map_of_map_zero
      (map_zero e.symm) (g : ℝ)
  simp [InfinitePlace.mult, hw, hn, e]

private lemma infiniteNorm_ofComplex_unit (w : InfinitePlace F) (hc : w.IsComplex) (g : ℂˣ) :
    (((Units.map nnNormHom.toMonoidHom ^ InfinitePlace.mult w : w.Completionˣ →* ℝ≥0ˣ)
      (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex hc).symm.toMonoidHom g) : ℝ≥0) : ℝ) =
      ‖(g : ℂ)‖ ^ 2 := by
  let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hc
  have hn : ‖e.symm (g : ℂ)‖ = ‖(g : ℂ)‖ :=
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc).symm.isometry.norm_map_of_map_zero
      (map_zero e.symm) (g : ℂ)
  simp [InfinitePlace.mult, InfinitePlace.not_isReal_iff_isComplex.mpr hc, hn, e]

private lemma real_inner_mul_left_eq (x y : ℝ) : (inner ℝ x y : ℂ) = (y : ℂ) * (x : ℂ) := by
  rw [RCLike.inner_apply]
  simp [mul_comm]

private lemma complex_inner_eq_add_conj (z y : ℂ) :
    (inner ℝ z y : ℂ) = (z * starRingEnd ℂ y + starRingEnd ℂ z * y) / 2 := by
  apply Complex.ext <;> simp [Complex.inner, Complex.mul_re, Complex.mul_im] <;> ring

private theorem infiniteEigendistribution_eq_zero_of_gaussian_proof (w : InfinitePlace F)
    (χ : PontryaginDual w.Completionˣ) (s : ℂ)
    (T : StrongDual ℂ (SchwartzBruhat (Multiplicative w.Completion)))
    (hT : T ∈ schwartzBruhatEigendistributions
      (quasiCharacterNormTwist (Units.map nnNormHom.toMonoidHom ^ InfinitePlace.mult w)
        (continuous_infiniteLocalModule w)
        ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ) s))
    (hG : T (infiniteStandardGaussian w χ) = 0) : T = 0 := by
  classical
  let mInf : w.Completionˣ →* ℝ≥0ˣ := Units.map nnNormHom.toMonoidHom ^ InfinitePlace.mult w
  let cToC : Circle →ₜ* ℂ := ⟨Circle.coeHom, continuous_subtype_val⟩
  let c : QuasiCharacter w.Completionˣ :=
    quasiCharacterNormTwist mInf (continuous_infiniteLocalModule w) (cToC.comp χ) s
  have hT_eig : ∀ (u : w.Completionˣ) (f : SchwartzBruhat (Multiplicative w.Completion)),
      T (schwartzBruhatUnitTranslate u f) = c u * T f := hT
  by_cases hw : w.IsReal
  · obtain ⟨Φ, hΦ_surj, hΦ_apply⟩ := realSchwartzBruhat_surjective w hw
    let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
    let T' : StrongDual ℂ (SchwartzMap ℝ ℂ) := T.comp Φ
    have hΦ_trans : ∀ (g : ℝˣ) (f : SchwartzMap ℝ ℂ),
        Φ (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (unitScaleInvCLE g) f) =
          schwartzBruhatUnitTranslate (Units.map e.symm.toMonoidHom g) (Φ f) := by
      intro g f
      refine Subtype.ext (funext fun y ↦ ?_)
      obtain ⟨x, rfl⟩ : ∃ x : w.Completion, Multiplicative.ofAdd x = y := ⟨y.toAdd, rfl⟩
      rw [hΦ_apply, schwartzBruhatUnitTranslate_apply, hΦ_apply]
      have harg : e ((↑(Units.map e.symm.toMonoidHom g)⁻¹ : w.Completion) * x) = (g⁻¹ : ℝ) * e x := by
        calc
          e ((↑(Units.map e.symm.toMonoidHom g)⁻¹ : w.Completion) * x)
              = e (e.symm (g⁻¹ : ℝ) * x) := by simp [e]
          _ = (g⁻¹ : ℝ) * e x := by rw [map_mul, e.apply_symm_apply]
      rw [harg]
      rfl
    have hT'_eig : ∀ (g : ℝˣ) (f : SchwartzMap ℝ ℂ),
        T' (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (unitScaleInvCLE g) f) =
          c (Units.map e.symm.toMonoidHom g) * T' f := by
      intro g f
      simp only [T', ContinuousLinearMap.comp_apply, hΦ_trans]
      exact hT_eig _ _
    have hpoly_temp : ∀ m : ℕ, (fun x : ℝ ↦ (x : ℂ) ^ m).HasTemperateGrowth := fun m ↦ by
      have h1 : (fun x : ℝ ↦ (x : ℂ)).HasTemperateGrowth := Complex.hasTemperateGrowth_ofReal
      exact h1.pow m
    let p₀ : ℕ := if χ (-1) = 1 then 0 else 1
    have hp₀_van : T' (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ) ^ p₀)
        ((SchwartzMap.gaussian Real.pi Real.pi_pos).postcompCLM Complex.ofRealCLM)) = 0 := by
      have hgauss_eq : infiniteStandardGaussian w χ =
          Φ (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ) ^ p₀)
            ((SchwartzMap.gaussian Real.pi Real.pi_pos).postcompCLM Complex.ofRealCLM)) := by
        refine Subtype.ext (funext fun y ↦ ?_)
        obtain ⟨x, rfl⟩ : ∃ x : w.Completion, Multiplicative.ofAdd x = y := ⟨y.toAdd, rfl⟩
        rw [hΦ_apply, SchwartzMap.smulLeftCLM_apply_apply (hpoly_temp p₀)]
        change infiniteStandardGaussianValue w χ x = _
        simp only [infiniteStandardGaussianValue, hw, ↓reduceDIte, SchwartzMap.postcompCLM_apply,
          Complex.ofRealCLM_apply, SchwartzMap.gaussian_apply, smul_eq_mul, Real.norm_eq_abs, sq_abs]
        by_cases h1 : χ (-1) = 1
        · simp [p₀, h1]
        · simp [p₀, h1]
      have hG' : T' (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ) ^ p₀)
            ((SchwartzMap.gaussian Real.pi Real.pi_pos).postcompCLM Complex.ofRealCLM)) =
          T (infiniteStandardGaussian w χ) := by
        simp only [T', ContinuousLinearMap.comp_apply, ← hgauss_eq]
      rw [hG', hG]
    have hneg_c : c (Units.map e.symm.toMonoidHom (-1 : ℝˣ)) = (cToC (χ (-1)) : ℂ) := by
      have hmap : Units.map e.symm.toMonoidHom (-1 : ℝˣ) = (-1 : w.Completionˣ) := by
        ext; simp
      have hnorm1 : ((mInf (-1 : w.Completionˣ) : ℝ≥0) : ℝ) = 1 := by
        rw [← hmap, infiniteNorm_ofReal_unit w hw (-1)]
        simp
      change ((cToC (χ (Units.map e.symm.toMonoidHom (-1 : ℝˣ))) : ℂ)) *
        (((mInf (Units.map e.symm.toMonoidHom (-1 : ℝˣ)) : ℝ≥0) : ℝ) : ℂ) ^ s = _
      rw [hmap, hnorm1]
      simp
    have hparity_both : ∀ q : Fin 2,
        T' (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ) ^ (q : ℕ))
          ((SchwartzMap.gaussian Real.pi Real.pi_pos).postcompCLM Complex.ofRealCLM)) = 0 := by
      intro q
      let gq := SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ) ^ (q : ℕ))
        ((SchwartzMap.gaussian Real.pi Real.pi_pos).postcompCLM Complex.ofRealCLM)
      have hneg_gq : SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (unitScaleInvCLE (-1 : ℝˣ)) gq =
          ((-1 : ℂ) ^ (q : ℕ)) • gq := by
        ext x
        simp [gq, SchwartzMap.smulLeftCLM_apply_apply (hpoly_temp (q : ℕ)),
          SchwartzMap.gaussian_apply, neg_mul, Real.norm_eq_abs, sq_abs]
        ring
      have heq_eig : ((-1 : ℂ) ^ (q : ℕ)) * T' gq = (cToC (χ (-1)) : ℂ) * T' gq := by
        calc
          ((-1 : ℂ) ^ (q : ℕ)) * T' gq = T' (((-1 : ℂ) ^ (q : ℕ)) • gq) := by rw [map_smul, smul_eq_mul]
          _ = T' (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (unitScaleInvCLE (-1 : ℝˣ)) gq) := by
            rw [hneg_gq]
          _ = c (Units.map e.symm.toMonoidHom (-1 : ℝˣ)) * T' gq := hT'_eig (-1) gq
          _ = (cToC (χ (-1)) : ℂ) * T' gq := by rw [hneg_c]
      by_cases h1 : χ (-1) = 1
      · fin_cases q
        · simpa [p₀, h1] using hp₀_van
        · have hsub : (-1 : ℂ) * T' gq = 1 * T' gq := by simpa [h1] using heq_eig
          have htwo : (2 : ℂ) * T' gq = 0 := by linear_combination -hsub
          exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
      · fin_cases q
        · have hχ_sq : (cToC (χ (-1)) : ℂ) ^ 2 = 1 := by
            calc
              (cToC (χ (-1)) : ℂ) ^ 2 = (cToC (χ ((-1 : w.Completionˣ) ^ 2)) : ℂ) := by
                rw [← map_pow, ← map_pow]
              _ = 1 := by simp
          have hχ_ne : (cToC (χ (-1)) : ℂ) ≠ 1 := by
            intro h
            exact h1 (Circle.coe_injective h)
          have hχ_neg1 : (cToC (χ (-1)) : ℂ) = -1 :=
            (sq_eq_one_iff.mp hχ_sq).resolve_left hχ_ne
          have hsub : (1 : ℂ) * T' gq = (-1 : ℂ) * T' gq := by simpa [hχ_neg1] using heq_eig
          have htwo : (2 : ℂ) * T' gq = 0 := by linear_combination hsub
          exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
        · simpa [p₀, h1] using hp₀_van
    have hparity_all_b : ∀ (q : Fin 2) (b : ℝ) (hb : 0 < b),
        T' (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ) ^ (q : ℕ))
          ((SchwartzMap.gaussian b hb).postcompCLM Complex.ofRealCLM)) = 0 := by
      intro q b hb
      let r : ℝ := Real.sqrt (Real.pi / b)
      have hr : 0 < r := Real.sqrt_pos.mpr (div_pos Real.pi_pos hb)
      let g : ℝˣ := Units.mk0 r hr.ne'
      have hscale : SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (unitScaleInvCLE g)
            (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ) ^ (q : ℕ))
              ((SchwartzMap.gaussian Real.pi Real.pi_pos).postcompCLM Complex.ofRealCLM)) =
          ((r⁻¹ : ℂ) ^ (q : ℕ)) • SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ) ^ (q : ℕ))
            ((SchwartzMap.gaussian b hb).postcompCLM Complex.ofRealCLM) := by
        ext x
        simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
          unitScaleInvCLE_apply, smul_apply, SchwartzMap.smulLeftCLM_apply_apply (hpoly_temp (q : ℕ)),
          SchwartzMap.postcompCLM_apply, Complex.ofRealCLM_apply, SchwartzMap.gaussian_apply,
          smul_eq_mul]
        have hr_sq : -Real.pi * (r⁻¹ * x) ^ 2 = -b * x ^ 2 := by
          have hr2 : r ^ 2 = Real.pi / b := Real.sq_sqrt (div_pos Real.pi_pos hb).le
          calc
            -Real.pi * (r⁻¹ * x) ^ 2 = -Real.pi * (r ^ 2)⁻¹ * x ^ 2 := by ring
            _ = -Real.pi * (Real.pi / b)⁻¹ * x ^ 2 := by rw [hr2]
            _ = -b * x ^ 2 := by field_simp [Real.pi_ne_zero, hb.ne']
        have hnorm_sq : ‖(g⁻¹ : ℝ) * x‖ ^ 2 = (r⁻¹ * x) ^ 2 := by
          rw [Real.norm_eq_abs, sq_abs]
          rfl
        have hnorm_x : -b * ‖x‖ ^ 2 = -b * x ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
        rw [hnorm_sq, hr_sq, ← hnorm_x, show ((g⁻¹ : ℝ) : ℝ) = r⁻¹ from rfl, Complex.ofReal_mul, mul_pow,
          Complex.ofReal_inv]
        ring
      have hvan_scaled : ((r⁻¹ : ℂ) ^ (q : ℕ)) *
          T' (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ) ^ (q : ℕ))
            ((SchwartzMap.gaussian b hb).postcompCLM Complex.ofRealCLM)) = 0 := by
        calc
          ((r⁻¹ : ℂ) ^ (q : ℕ)) *
              T' (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ) ^ (q : ℕ))
                ((SchwartzMap.gaussian b hb).postcompCLM Complex.ofRealCLM))
              = T' (((r⁻¹ : ℂ) ^ (q : ℕ)) • SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ) ^ (q : ℕ))
                  ((SchwartzMap.gaussian b hb).postcompCLM Complex.ofRealCLM)) := by
                rw [map_smul, smul_eq_mul]
          _ = T' (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (unitScaleInvCLE g)
                  (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ) ^ (q : ℕ))
                    ((SchwartzMap.gaussian Real.pi Real.pi_pos).postcompCLM Complex.ofRealCLM))) := by
                rw [hscale]
          _ = c (Units.map e.symm.toMonoidHom g) *
                T' (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ) ^ (q : ℕ))
                  ((SchwartzMap.gaussian Real.pi Real.pi_pos).postcompCLM Complex.ofRealCLM)) :=
                hT'_eig g _
          _ = 0 := by rw [hparity_both q, mul_zero]
      exact (mul_eq_zero.mp hvan_scaled).resolve_left (pow_ne_zero _ (inv_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne')))
    have hmono_all : ∀ (m : ℕ) (b : ℝ) (hb : 0 < b),
        T' (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ) ^ m)
          ((SchwartzMap.gaussian b hb).postcompCLM Complex.ofRealCLM)) = 0 := by
      intro m b hb
      let j := m / 2
      let q : Fin 2 := ⟨m % 2, Nat.mod_lt m (by norm_num)⟩
      have hdecomp : (fun x : ℝ ↦ (x : ℂ) ^ m) =
          fun x : ℝ ↦ (‖x‖ ^ 2 : ℂ) ^ j * (x : ℂ) ^ (q : ℕ) := by
        ext x
        have hm_eq : m = 2 * j + (q : ℕ) := (Nat.div_add_mod m 2).symm
        calc
          (x : ℂ) ^ m = (x : ℂ) ^ (2 * j + (q : ℕ)) := by rw [hm_eq]
          _ = ((x : ℂ) ^ 2) ^ j * (x : ℂ) ^ (q : ℕ) := by rw [pow_add, pow_mul]
          _ = (‖x‖ ^ 2 : ℂ) ^ j * (x : ℂ) ^ (q : ℕ) := by
            conv_rhs => rw [Real.norm_eq_abs, ← Complex.ofReal_pow, sq_abs, Complex.ofReal_pow]
      rw [hdecomp]
      exact schwartzDual_normSq_pow_mul_gauss_eq_zero T' (hpoly_temp (q : ℕ))
        (hparity_all_b q) j b hb
    have htrans_van : ∀ (b : ℝ) (hb : 0 < b) (y : ℝ),
        T' (((SchwartzMap.gaussian b hb).postcompCLM Complex.ofRealCLM).compSubConstCLM ℂ y) = 0 := by
      intro b hb y
      refine schwartzDual_translate_gauss_eq_zero T' b hb y fun m ↦ ?_
      have hfun : (fun x : ℝ ↦ ((inner ℝ x y : ℝ) : ℂ) ^ m) = fun x : ℝ ↦ (y : ℂ) ^ m * (x : ℂ) ^ m := by
        ext x; rw [real_inner_mul_left_eq, mul_pow]
      have hinner : SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ ((inner ℝ x y : ℝ) : ℂ) ^ m)
            ((SchwartzMap.gaussian b hb).postcompCLM Complex.ofRealCLM) =
          ((y : ℂ) ^ m) • SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ) ^ m)
            ((SchwartzMap.gaussian b hb).postcompCLM Complex.ofRealCLM) := by
        ext x
        have htemp : (fun x : ℝ ↦ ((inner ℝ x y : ℝ) : ℂ) ^ m).HasTemperateGrowth := by
          rw [hfun]; exact (Function.HasTemperateGrowth.const _).mul (hpoly_temp m)
        rw [smul_apply, SchwartzMap.smulLeftCLM_apply_apply htemp,
          SchwartzMap.smulLeftCLM_apply_apply (hpoly_temp m), congrFun hfun x]
        simp [smul_eq_mul, mul_assoc]
      rw [hinner, map_smul, hmono_all m b hb, smul_zero]
    have hT'_zero : T' = 0 := schwartzDual_eq_zero_of_translate_gauss T' htrans_van
    ext f
    obtain ⟨g, rfl⟩ := hΦ_surj f
    exact congrArg (fun S : StrongDual ℂ (SchwartzMap ℝ ℂ) ↦ S g) hT'_zero
  · have hc : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hw
    obtain ⟨Φ, hΦ_surj, hΦ_apply⟩ := complexSchwartzBruhat_surjective w hc
    let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hc
    let T' : StrongDual ℂ (SchwartzMap ℂ ℂ) := T.comp Φ
    have hΦ_trans : ∀ (g : ℂˣ) (f : SchwartzMap ℂ ℂ),
        Φ (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (unitScaleInvCLE g) f) =
          schwartzBruhatUnitTranslate (Units.map e.symm.toMonoidHom g) (Φ f) := by
      intro g f
      refine Subtype.ext (funext fun y ↦ ?_)
      obtain ⟨x, rfl⟩ : ∃ x : w.Completion, Multiplicative.ofAdd x = y := ⟨y.toAdd, rfl⟩
      rw [hΦ_apply, schwartzBruhatUnitTranslate_apply, hΦ_apply]
      have harg : e ((↑(Units.map e.symm.toMonoidHom g)⁻¹ : w.Completion) * x) = (g⁻¹ : ℂ) * e x := by
        calc
          e ((↑(Units.map e.symm.toMonoidHom g)⁻¹ : w.Completion) * x)
              = e (e.symm (g⁻¹ : ℂ) * x) := by simp [e]
          _ = (g⁻¹ : ℂ) * e x := by rw [map_mul, e.apply_symm_apply]
      rw [harg]
      rfl
    have hT'_eig : ∀ (g : ℂˣ) (f : SchwartzMap ℂ ℂ),
        T' (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (unitScaleInvCLE g) f) =
          c (Units.map e.symm.toMonoidHom g) * T' f := by
      intro g f
      simp only [T', ContinuousLinearMap.comp_apply, hΦ_trans]
      exact hT_eig _ _
    let monom : ℕ → ℕ → ℂ → ℂ := fun p q z ↦ z ^ p * (starRingEnd ℂ z) ^ q
    have hmonom_temp : ∀ p q : ℕ, (monom p q).HasTemperateGrowth := fun p q ↦ by
      have hid : (fun z : ℂ ↦ z).HasTemperateGrowth := (ContinuousLinearMap.id ℝ ℂ).hasTemperateGrowth
      have hconj : (fun z : ℂ ↦ starRingEnd ℂ z).HasTemperateGrowth :=
        (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.hasTemperateGrowth
      exact (hid.pow p).mul (hconj.pow q)
    let jIso := InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc
    let i_unit : ℂˣ →ₜ* w.Completionˣ :=
      ⟨Units.map e.symm.toMonoidHom, jIso.symm.continuous.units_map _⟩
    let c₀ : ℂˣ →ₜ* ℂ := cToC.comp (χ.comp i_unit)
    have hc₀_norm : ∀ x : ℂˣ, ‖c₀ x‖ = 1 := fun x ↦ Circle.norm_coe _
    have hpair := existsUnique_complexUnits_character_parameters c₀ hc₀_norm
    let t : ℂ := hpair.exists.choose.1
    let m : ℤ := hpair.exists.choose.2
    have hbase : ∀ x : ℂˣ, c₀ x = ((‖(x : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ t * ((x : ℂ) / (‖(x : ℂ)‖ : ℂ)) ^ m :=
      hpair.exists.choose_spec.2
    let p₀ : ℕ := if 0 ≤ m then 0 else m.natAbs
    let q₀ : ℕ := if 0 ≤ m then m.natAbs else 0
    have hp₀q₀_van : T' (SchwartzMap.smulLeftCLM ℂ (monom p₀ q₀)
        ((SchwartzMap.gaussian (2 * Real.pi) (by positivity)).postcompCLM Complex.ofRealCLM)) = 0 := by
      have hgauss_eq : infiniteStandardGaussian w χ =
          ((2 * (Real.pi : ℂ))⁻¹) • Φ (SchwartzMap.smulLeftCLM ℂ (monom p₀ q₀)
            ((SchwartzMap.gaussian (2 * Real.pi) (by positivity)).postcompCLM Complex.ofRealCLM)) := by
        refine Subtype.ext (funext fun y ↦ ?_)
        obtain ⟨x, rfl⟩ : ∃ x : w.Completion, Multiplicative.ofAdd x = y := ⟨y.toAdd, rfl⟩
        change infiniteStandardGaussianValue w χ x =
          ((2 * (Real.pi : ℂ))⁻¹) * Φ (SchwartzMap.smulLeftCLM ℂ (monom p₀ q₀)
            ((SchwartzMap.gaussian (2 * Real.pi) (by positivity)).postcompCLM Complex.ofRealCLM))
            (Multiplicative.ofAdd x)
        rw [hΦ_apply, SchwartzMap.smulLeftCLM_apply_apply (hmonom_temp p₀ q₀)]
        simp only [infiniteStandardGaussianValue, hw, ↓reduceDIte, SchwartzMap.postcompCLM_apply,
          Complex.ofRealCLM_apply, SchwartzMap.gaussian_apply, smul_eq_mul]
        have hexp_eq : Complex.exp (-2 * ↑Real.pi * e x * star (e x)) =
            (Real.exp (-(2 * Real.pi) * ‖e x‖ ^ 2) : ℂ) := by
          rw [Complex.ofReal_exp]
          congr 1
          have hmul_conj : e x * star (e x) = ((‖e x‖ : ℝ) : ℂ) ^ 2 := Complex.mul_conj' (e x)
          calc
            -2 * (Real.pi : ℂ) * e x * star (e x)
                = -(2 * (Real.pi : ℂ)) * (e x * star (e x)) := by ring
            _ = -(2 * (Real.pi : ℂ)) * ((‖e x‖ : ℝ) : ℂ) ^ 2 := by rw [hmul_conj]
            _ = ((-(2 * Real.pi) * ‖e x‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
        have hmon_eq : (if 0 ≤ m then star (e x) ^ m.natAbs else e x ^ m.natAbs) = monom p₀ q₀ (e x) := by
          by_cases hm0 : 0 ≤ m
          · simp [monom, p₀, q₀, hm0]
          · simp [monom, p₀, q₀, hm0]
        change (if 0 ≤ m then star (e x) ^ m.natAbs else e x ^ m.natAbs) *
            Complex.exp (-2 * ↑Real.pi * e x * star (e x)) / (2 * ↑Real.pi) = _
        rw [hmon_eq, hexp_eq]
        ring
      have hG' : ((2 * (Real.pi : ℂ))⁻¹) *
          T' (SchwartzMap.smulLeftCLM ℂ (monom p₀ q₀)
            ((SchwartzMap.gaussian (2 * Real.pi) (by positivity)).postcompCLM Complex.ofRealCLM)) = 0 := by
        simpa [T', hgauss_eq, map_smul, smul_eq_mul] using hG
      exact (mul_eq_zero.mp hG').resolve_left (inv_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
    have hp₀q₀_all_b : ∀ (b : ℝ) (hb : 0 < b),
        T' (SchwartzMap.smulLeftCLM ℂ (monom p₀ q₀)
          ((SchwartzMap.gaussian b hb).postcompCLM Complex.ofRealCLM)) = 0 := by
      intro b hb
      let ρ : ℝ := Real.sqrt (2 * Real.pi / b)
      have hρ : 0 < ρ := Real.sqrt_pos.mpr (div_pos (by positivity) hb)
      let g : ℂˣ := Units.mk0 (ρ : ℂ) (Complex.ofReal_ne_zero.mpr hρ.ne')
      have hscale : SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (unitScaleInvCLE g)
            (SchwartzMap.smulLeftCLM ℂ (monom p₀ q₀)
              ((SchwartzMap.gaussian (2 * Real.pi) (by positivity)).postcompCLM Complex.ofRealCLM)) =
          ((ρ⁻¹ : ℂ) ^ (p₀ + q₀)) • SchwartzMap.smulLeftCLM ℂ (monom p₀ q₀)
            ((SchwartzMap.gaussian b hb).postcompCLM Complex.ofRealCLM) := by
        ext z
        simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
          unitScaleInvCLE_apply, smul_apply, SchwartzMap.smulLeftCLM_apply_apply (hmonom_temp p₀ q₀),
          SchwartzMap.postcompCLM_apply, Complex.ofRealCLM_apply, SchwartzMap.gaussian_apply,
          smul_eq_mul]
        have hg_inv : (g⁻¹ : ℂ) = (ρ⁻¹ : ℂ) := by simp [g]
        have hnorm_sc : ‖(g⁻¹ : ℂ) * z‖ ^ 2 = ρ⁻¹ ^ 2 * ‖z‖ ^ 2 := by
          rw [hg_inv, norm_mul, norm_inv, Complex.norm_real,
            Real.norm_of_nonneg hρ.le, mul_pow]
        have hexp_sc : -(2 * Real.pi) * ‖(g⁻¹ : ℂ) * z‖ ^ 2 = -b * ‖z‖ ^ 2 := by
          have hρ2 : ρ ^ 2 = 2 * Real.pi / b := Real.sq_sqrt (div_pos (by positivity) hb).le
          rw [hnorm_sc]
          calc
            -(2 * Real.pi) * (ρ⁻¹ ^ 2 * ‖z‖ ^ 2) = -(2 * Real.pi) * (ρ ^ 2)⁻¹ * ‖z‖ ^ 2 := by ring
            _ = -(2 * Real.pi) * (2 * Real.pi / b)⁻¹ * ‖z‖ ^ 2 := by rw [hρ2]
            _ = -b * ‖z‖ ^ 2 := by field_simp [Real.pi_ne_zero, hb.ne']
        have hmon_sc : monom p₀ q₀ ((g⁻¹ : ℂ) * z) = (ρ⁻¹ : ℂ) ^ (p₀ + q₀) * monom p₀ q₀ z := by
          rw [hg_inv]
          simp only [monom, map_mul, map_inv₀, Complex.conj_ofReal, mul_pow, pow_add]
          ring
        rw [hexp_sc, hmon_sc]
        ring
      have hmul : ((ρ⁻¹ : ℂ) ^ (p₀ + q₀)) *
          T' (SchwartzMap.smulLeftCLM ℂ (monom p₀ q₀)
            ((SchwartzMap.gaussian b hb).postcompCLM Complex.ofRealCLM)) = 0 := by
        calc
          ((ρ⁻¹ : ℂ) ^ (p₀ + q₀)) *
              T' (SchwartzMap.smulLeftCLM ℂ (monom p₀ q₀)
                ((SchwartzMap.gaussian b hb).postcompCLM Complex.ofRealCLM))
              = T' (((ρ⁻¹ : ℂ) ^ (p₀ + q₀)) • SchwartzMap.smulLeftCLM ℂ (monom p₀ q₀)
                  ((SchwartzMap.gaussian b hb).postcompCLM Complex.ofRealCLM)) := by
                rw [map_smul, smul_eq_mul]
          _ = T' (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (unitScaleInvCLE g)
                  (SchwartzMap.smulLeftCLM ℂ (monom p₀ q₀)
                    ((SchwartzMap.gaussian (2 * Real.pi) (by positivity)).postcompCLM Complex.ofRealCLM))) := by
                rw [hscale]
          _ = c (Units.map e.symm.toMonoidHom g) *
                T' (SchwartzMap.smulLeftCLM ℂ (monom p₀ q₀)
                  ((SchwartzMap.gaussian (2 * Real.pi) (by positivity)).postcompCLM Complex.ofRealCLM)) :=
                hT'_eig g _
          _ = 0 := by rw [hp₀q₀_van, mul_zero]
      exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero _ (inv_ne_zero (Complex.ofReal_ne_zero.mpr hρ.ne')))
    have hdiag_van : ∀ (j : ℕ) (b : ℝ) (hb : 0 < b),
        T' (SchwartzMap.smulLeftCLM ℂ (monom (p₀ + j) (q₀ + j))
          ((SchwartzMap.gaussian b hb).postcompCLM Complex.ofRealCLM)) = 0 := by
      intro j b hb
      have hdecomp : monom (p₀ + j) (q₀ + j) = fun z : ℂ ↦ (‖z‖ ^ 2 : ℂ) ^ j * monom p₀ q₀ z := by
        ext z
        have hmconj : (‖z‖ ^ 2 : ℂ) = z * starRingEnd ℂ z := (Complex.mul_conj' z).symm
        simp only [monom, hmconj, mul_pow, pow_add]
        ring
      rw [hdecomp]
      exact schwartzDual_normSq_pow_mul_gauss_eq_zero T' (hmonom_temp p₀ q₀) hp₀q₀_all_b j b hb
    have hmonom_all : ∀ (p q : ℕ) (b : ℝ) (hb : 0 < b),
        T' (SchwartzMap.smulLeftCLM ℂ (monom p q)
          ((SchwartzMap.gaussian b hb).postcompCLM Complex.ofRealCLM)) = 0 := by
      intro p q b hb
      by_cases hdiff : (q : ℤ) - p = m
      · by_cases hm0 : 0 ≤ m
        · have hp0 : p₀ = 0 := by simp [p₀, hm0]
          have hq0 : q₀ = m.natAbs := by simp [q₀, hm0]
          rw [show monom p q = monom (p₀ + p) (q₀ + p) by congr 1 <;> omega]
          exact hdiag_van p b hb
        · have hp0 : p₀ = m.natAbs := by simp [p₀, hm0]
          have hq0 : q₀ = 0 := by simp [q₀, hm0]
          rw [show monom p q = monom (p₀ + q) (q₀ + q) by congr 1 <;> omega]
          exact hdiag_van q b hb
      · let d : ℤ := (q : ℤ) - p - m
        have hd : d ≠ 0 := sub_ne_zero.mpr hdiff
        let θ : ℝ := Real.pi / ((d.natAbs : ℝ) + 1)
        have hθ_pos : 0 < θ := div_pos Real.pi_pos (by positivity)
        let u0 : ℂ := Complex.exp ((θ : ℂ) * Complex.I)
        have hu0_ne : u0 ≠ 0 := Complex.exp_ne_zero _
        let u : ℂˣ := Units.mk0 u0 hu0_ne
        have hu0_norm : ‖u0‖ = 1 := by simp [u0, Complex.norm_exp_ofReal_mul_I]
        have hu0_conj : starRingEnd ℂ u0 = u0⁻¹ := by
          have hmul : u0 * starRingEnd ℂ u0 = 1 := by
            rw [Complex.mul_conj' u0, hu0_norm]
            norm_num
          exact (inv_eq_of_mul_eq_one_right hmul).symm
        have hu0_inv_conj : starRingEnd ℂ (u0⁻¹) = u0 := by
          rw [map_inv₀, hu0_conj, inv_inv]
        let Fpq := SchwartzMap.smulLeftCLM ℂ (monom p q)
          ((SchwartzMap.gaussian b hb).postcompCLM Complex.ofRealCLM)
        have hrot_F : SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (unitScaleInvCLE u) Fpq =
            (u0 ^ ((q : ℤ) - p)) • Fpq := by
          ext z
          simp only [Fpq, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
            unitScaleInvCLE_apply, smul_apply, SchwartzMap.smulLeftCLM_apply_apply (hmonom_temp p q),
            SchwartzMap.postcompCLM_apply, Complex.ofRealCLM_apply, SchwartzMap.gaussian_apply,
            smul_eq_mul]
          have hu_val : (u⁻¹ : ℂ) = u0⁻¹ := rfl
          have hnorm_rot : ‖(u⁻¹ : ℂ) * z‖ = ‖z‖ := by
            rw [hu_val, norm_mul, norm_inv, hu0_norm, inv_one, one_mul]
          have hpow_rot : monom p q ((u⁻¹ : ℂ) * z) = u0 ^ ((q : ℤ) - p) * monom p q z := by
            rw [hu_val]
            simp only [monom, map_mul, hu0_inv_conj, mul_pow]
            rw [zpow_sub₀ hu0_ne, zpow_natCast, zpow_natCast, inv_pow]
            field_simp [hu0_ne]
          rw [hnorm_rot, hpow_rot]
          ring
        have hc_u : c (Units.map e.symm.toMonoidHom u) = u0 ^ m := by
          change c₀ u * (((mInf (Units.map e.symm.toMonoidHom u) : ℝ≥0) : ℝ) : ℂ) ^ s = _
          have hnorm_u : ((mInf (Units.map e.symm.toMonoidHom u) : ℝ≥0) : ℝ) = 1 := by
            rw [infiniteNorm_ofComplex_unit w hc u]
            simp [u, hu0_norm]
          rw [hnorm_u, Complex.ofReal_one, Complex.one_cpow, mul_one, hbase u]
          have hu_n : ‖(u : ℂ)‖ = 1 := hu0_norm
          rw [hu_n]
          simp [u]
        have heq_mul : (u0 ^ ((q : ℤ) - p) - u0 ^ m) * T' Fpq = 0 := by
          have h1 : u0 ^ ((q : ℤ) - p) * T' Fpq = u0 ^ m * T' Fpq := by
            calc
              u0 ^ ((q : ℤ) - p) * T' Fpq = T' ((u0 ^ ((q : ℤ) - p)) • Fpq) := by
                rw [map_smul, smul_eq_mul]
              _ = T' (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (unitScaleInvCLE u) Fpq) := by
                rw [hrot_F]
              _ = c (Units.map e.symm.toMonoidHom u) * T' Fpq := hT'_eig u Fpq
              _ = u0 ^ m * T' Fpq := by rw [hc_u]
          linear_combination h1
        have hdiff_ne : u0 ^ ((q : ℤ) - p) - u0 ^ m ≠ 0 := by
          intro hzero
          have hdiv1 : u0 ^ d = 1 := by
            have heq : u0 ^ ((q : ℤ) - p) = u0 ^ m := sub_eq_zero.mp hzero
            dsimp only [d]
            rw [zpow_sub₀ hu0_ne, heq, div_self (zpow_ne_zero m hu0_ne)]
          have hexp_d : Complex.exp (((d : ℝ) * θ : ℝ) * Complex.I) = 1 := by
            calc
              Complex.exp (((d : ℝ) * θ : ℝ) * Complex.I)
                  = Complex.exp ((d : ℂ) * ((θ : ℂ) * Complex.I)) := by push_cast; ring_nf
              _ = (Complex.exp ((θ : ℂ) * Complex.I)) ^ d := Complex.exp_int_mul _ d
              _ = u0 ^ d := rfl
              _ = 1 := hdiv1
          obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp hexp_d
          have hk_im : (d : ℝ) * θ = k * (2 * Real.pi) := by
            have := congrArg Complex.im hk
            simpa [Complex.mul_im] using this
          have hk_ne : k ≠ 0 := by
            rintro rfl
            simp only [Int.cast_zero, zero_mul, mul_eq_zero] at hk_im
            rcases hk_im with hd0 | hθ0
            · exact hd (Int.cast_eq_zero.mp hd0)
            · exact hθ_pos.ne' hθ0
          have hk_abs : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk_ne
          have hbd1 : 2 * Real.pi ≤ |(d : ℝ) * θ| := by
            rw [hk_im, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
            nlinarith [Real.pi_pos]
          have hbd2 : |(d : ℝ) * θ| < Real.pi := by
            rw [abs_mul, abs_of_pos hθ_pos]
            have hd_abs : |(d : ℝ)| = (d.natAbs : ℝ) := by
              rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
            rw [hd_abs]
            dsimp only [θ]
            calc
              (d.natAbs : ℝ) * (Real.pi / ((d.natAbs : ℝ) + 1))
                  = Real.pi * ((d.natAbs : ℝ) / ((d.natAbs : ℝ) + 1)) := by ring
              _ < Real.pi * 1 := by
                gcongr
                rw [div_lt_one (by positivity)]
                linarith
              _ = Real.pi := mul_one _
          linarith [Real.pi_pos]
        exact (mul_eq_zero.mp heq_mul).resolve_left hdiff_ne
    have htrans_van : ∀ (b : ℝ) (hb : 0 < b) (y : ℂ),
        T' (((SchwartzMap.gaussian b hb).postcompCLM Complex.ofRealCLM).compSubConstCLM ℂ y) = 0 := by
      intro b hb y
      refine schwartzDual_translate_gauss_eq_zero T' b hb y fun m ↦ ?_
      let g : SchwartzMap ℂ ℂ := (SchwartzMap.gaussian b hb).postcompCLM Complex.ofRealCLM
      have htemp_in : (fun z : ℂ ↦ ((inner ℝ z y : ℝ) : ℂ) ^ m).HasTemperateGrowth := by
        have hlin : (fun z : ℂ ↦ ((inner ℝ z y : ℝ) : ℂ)) =
            fun z : ℂ ↦ (starRingEnd ℂ y / 2) * z + (y / 2) * starRingEnd ℂ z := by
          ext z
          rw [complex_inner_eq_add_conj]
          ring
        have h1 : (fun z : ℂ ↦ (starRingEnd ℂ y / 2) * z + (y / 2) * starRingEnd ℂ z).HasTemperateGrowth := by
          exact ((Function.HasTemperateGrowth.const _).mul
              (ContinuousLinearMap.id ℝ ℂ).hasTemperateGrowth).add
            ((Function.HasTemperateGrowth.const _).mul
              (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.hasTemperateGrowth)
        rw [show (fun z : ℂ ↦ ((inner ℝ z y : ℝ) : ℂ) ^ m) =
            (fun z : ℂ ↦ ((starRingEnd ℂ y / 2) * z + (y / 2) * starRingEnd ℂ z) ^ m) from
            funext fun z ↦ congrArg (· ^ m) (congrFun hlin z)]
        exact h1.pow m
      have hsum : SchwartzMap.smulLeftCLM ℂ (fun z : ℂ ↦ ((inner ℝ z y : ℝ) : ℂ) ^ m) g =
          ∑ i ∈ Finset.range (m + 1),
            ((m.choose i : ℂ) * (starRingEnd ℂ y / 2) ^ i * (y / 2) ^ (m - i)) •
              SchwartzMap.smulLeftCLM ℂ (monom i (m - i)) g := by
        ext z
        rw [SchwartzMap.smulLeftCLM_apply_apply htemp_in, sum_apply]
        simp only [smul_apply, SchwartzMap.smulLeftCLM_apply_apply (hmonom_temp _ _),
          smul_eq_mul]
        rw [complex_inner_eq_add_conj,
          show (z * starRingEnd ℂ y + starRingEnd ℂ z * y) / 2 =
            z * (starRingEnd ℂ y / 2) + starRingEnd ℂ z * (y / 2) by ring,
          add_pow, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        simp only [monom, mul_pow]
        ring
      rw [hsum, map_sum]
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      rw [map_smul, hmonom_all i (m - i) b hb, smul_zero]
    have hT'_zero : T' = 0 := schwartzDual_eq_zero_of_translate_gauss T' htrans_van
    ext f
    obtain ⟨g, rfl⟩ := hΦ_surj f
    exact congrArg (fun S : StrongDual ℂ (SchwartzMap ℂ ℂ) ↦ S g) hT'_zero

end Step3c

end InfiniteEigendistributionHelpers

/-- Paper: Theorem 3.4.3.3(1), p. 153. At an infinite place, an eigendistribution of
weight `χ‖·‖^s` (in the norm-twist chart of the unitary character `χ`) that vanishes on the
standard Gaussian of `χ` is zero. This is the uniqueness half of the one-dimensionality of the
eigendistribution space, combined with the fact that its generator does not vanish on the
Gaussian (Weil, Kudla Thm. 3.4). -/
theorem infiniteEigendistribution_eq_zero_of_gaussian (w : InfinitePlace F)
    (χ : PontryaginDual w.Completionˣ) (s : ℂ) (T : StrongDual ℂ ℬ(w.Completion))
    (hT : T ∈ schwartzBruhatEigendistributions (quasiCharacterNormTwist (infiniteNorm(w))
      (continuous_infiniteLocalModule w) ((circleToComplex).comp χ) s))
    (hG : T (infiniteStandardGaussian w χ) = 0) : T = 0 := by
  exact infiniteEigendistribution_eq_zero_of_gaussian_proof w χ s T hT hG

/-- Abstract form of the entire family: a meromorphic family of distributions whose scalar
poles are at most simple and lie in the zero set of an entire function `h` becomes entire after
multiplication by `h`, and the product is a family of continuous functionals by
`distribution_of_local_clearings`. -/
private theorem infiniteEigendistribution_entire_family_assembly {E : Type*} [AddCommGroup E]
    [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℂ E] [BarrelledSpace ℂ E]
    (hol : ∀ {U : Set ℂ}, IsOpen U → ∀ Z : ℂ → StrongDual ℂ E,
      (∀ f, DifferentiableOn ℂ (fun z ↦ Z z f) U) → VectorHolomorphicOn Z U)
    (Zc : E → ℂ → ℂ) (hNF : ∀ f, MeromorphicNFOn (Zc f) univ)
    (D : ℂ → StrongDual ℂ E) (P : Set ℂ) (hD : IsVectorMeromorphicOn D univ P)
    (hDZ : ∀ s ∉ P, ∀ f, D s f = Zc f s)
    (h L : ℂ → ℂ) (hh : AnalyticOnNhd ℂ h univ) (hh0 : ∃ s, h s ≠ 0)
    (hL : ∀ s, h s ≠ 0 → L s * h s = 1)
    (h1 : ∀ f s, (-1 : WithTop ℤ) ≤ meromorphicOrderAt (Zc f) s)
    (h2 : ∀ f s, meromorphicOrderAt (Zc f) s < 0 → h s = 0) :
    ∃ Ent : ℂ → StrongDual ℂ E, (∀ f, AnalyticOnNhd ℂ (fun s ↦ Ent s f) univ) ∧
      ∀ᶠ s : ℂ in codiscrete ℂ, ∀ f, Zc f s = L s * Ent s f := by
  classical
  obtain ⟨-, -, hopen, hhol, hloc⟩ := hD
  let ev (f : E) : StrongDual ℂ E →L[ℂ] ℂ :=
    ⟨⟨⟨fun T ↦ T f, fun _ _ ↦ rfl⟩, fun _ _ ↦ rfl⟩, continuous_eval_const f⟩
  have hev (G : ℂ → StrongDual ℂ E) (U : Set ℂ) (hV : IsOpen U) (hG : VectorHolomorphicOn G U)
      (f : E) (t : ℂ) (ht : t ∈ U) : AnalyticAt ℂ (fun z ↦ G z f) t := by
    have hd : DifferentiableOn ℂ (fun z ↦ G z f) U := fun z hz ↦ by
      have hGz := ((hG z hz).differentiableAt (hV.mem_nhds hz)).hasFDerivAt
      have hj : HasFDerivAt ((ev f) ∘ G) ((ev f).comp (fderiv ℂ G z)) z := by
        apply HasFDerivAt.of_isLittleOTVS
        simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, map_sub]
          using (ev f).isBigOTVS_comp.trans_isLittleOTVS hGz.isLittleOTVS
      exact hj.differentiableAt.differentiableWithinAt
    exact hd.analyticAt (hV.mem_nhds ht)
  have hmer (f : E) : MeromorphicOn (h * Zc f) univ := fun s _ ↦
    (hh s trivial).meromorphicAt.mul ((hNF f).meromorphicOn s trivial)
  have hord (f : E) (s : ℂ) : 0 ≤ meromorphicOrderAt (h * Zc f) s := by
    rw [meromorphicOrderAt_mul (hh s trivial).meromorphicAt ((hNF f).meromorphicOn s trivial)]
    by_cases hz : meromorphicOrderAt (Zc f) s < 0
    · have hs0 := h2 f s hz
      have hz1 : meromorphicOrderAt (Zc f) s = -1 := by
        refine le_antisymm ?_ (h1 f s)
        revert hz
        induction meromorphicOrderAt (Zc f) s with
        | top => simp
        | coe m =>
          intro hm
          have : m < 0 := by exact_mod_cast hm
          show (m : WithTop ℤ) ≤ ((-1 : ℤ) : WithTop ℤ)
          exact WithTop.coe_le_coe.mpr (by omega)
      have ha : analyticOrderAt h s ≠ 0 := by
        rw [Ne, (hh s trivial).analyticOrderAt_eq_zero, not_not]
        exact hs0
      rw [hz1, (hh s trivial).meromorphicOrderAt_eq]
      revert ha
      induction analyticOrderAt h s with
      | top => simp
      | coe n =>
        intro hn
        have hn' : n ≠ 0 := fun h0 ↦ hn (by simp [h0])
        simp only [ENat.map_natCast]
        show ((0 : ℤ) : WithTop ℤ) ≤ ((n : ℤ) : WithTop ℤ) + ((-1 : ℤ) : WithTop ℤ)
        rw [← WithTop.coe_add]
        exact WithTop.coe_le_coe.mpr (by omega)
    · push Not at hz
      exact add_nonneg (hh s trivial).meromorphicOrderAt_nonneg hz
  let T (f : E) : ℂ → ℂ := toMeromorphicNFOn (h * Zc f) univ
  have hTnf (f : E) : MeromorphicNFOn (T f) univ := meromorphicNFOn_toMeromorphicNFOn _ _
  have hTan (f : E) (s : ℂ) : AnalyticAt ℂ (T f) s := by
    apply (hTnf f (mem_univ s)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    rw [meromorphicOrderAt_toMeromorphicNFOn (hmer f) (mem_univ s)]
    exact hord f s
  have hTeq (f : E) (t : ℂ) : T f =ᶠ[𝓝[≠] t] (h * Zc f) :=
    (hmer f).toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ t)
  have hclear : ∀ s : ℂ, ∃ (n : ℕ) (U : Set ℂ) (A : ℂ → StrongDual ℂ E),
      IsOpen U ∧ s ∈ U ∧ ∀ f t, t ∈ U → AnalyticAt ℂ (fun z ↦ A z f) t ∧
        (fun z ↦ (z - s) ^ n * T f z) =ᶠ[𝓝[≠] t] fun z ↦ A z f := by
    intro s
    by_cases hs : s ∈ P
    · obtain ⟨n, r, g, hr, hsub, hg, hgeq⟩ := hloc s hs
      refine ⟨n, Metric.ball s r, fun z ↦ h z • g z, Metric.isOpen_ball, Metric.mem_ball_self hr,
        fun f t ht ↦ ⟨(hh t trivial).mul (hev g _ Metric.isOpen_ball hg f t ht), ?_⟩⟩
      have hball : ∀ᶠ z in 𝓝[≠] t, z ∈ Metric.ball s r :=
        eventually_nhdsWithin_of_eventually_nhds (Metric.isOpen_ball.mem_nhds ht)
      have hne : ∀ᶠ z in 𝓝[≠] t, z ≠ s := by
        by_cases hts : t = s
        · subst hts
          exact self_mem_nhdsWithin
        · exact eventually_nhdsWithin_of_eventually_nhds (isOpen_ne.mem_nhds hts)
      filter_upwards [hTeq f t, hball, hne] with z hz hzb hzs
      have hzP : z ∈ univ \ P := hsub ⟨hzb, hzs⟩
      have hgz : g z f = (z - s) ^ n * Zc f z := by
        rw [hgeq ⟨hzb, hzs⟩]
        change (z - s) ^ n * D z f = _
        rw [hDZ z hzP.2]
      change (z - s) ^ n * T f z = h z * g z f
      rw [hz, hgz, Pi.mul_apply]
      ring
    · refine ⟨0, univ \ P, fun z ↦ h z • D z, hopen, ⟨mem_univ s, hs⟩,
        fun f t ht ↦ ⟨(hh t trivial).mul (hev D _ hopen hhol f t ht), ?_⟩⟩
      filter_upwards [hTeq f t, eventually_nhdsWithin_of_eventually_nhds (hopen.mem_nhds ht)]
        with z hz hzP
      change (z - s) ^ 0 * T f z = h z * D z f
      rw [hz, hDZ z hzP.2, pow_zero, one_mul, Pi.mul_apply]
  obtain ⟨Ent, -, hEnt⟩ := distribution_of_local_clearings hol T hTnf hclear
  have hEntT (f : E) (s : ℂ) : Ent s f = T f s := by
    refine hEnt s ?_ f
    rintro ⟨g, hg⟩
    have := hord g s
    rw [← meromorphicOrderAt_toMeromorphicNFOn (hmer g) (mem_univ s)] at this
    exact absurd hg (not_lt.mpr this)
  refine ⟨Ent, fun f s _ ↦ (hTan f s).congr (Eventually.of_forall fun z ↦ (hEntT f z).symm), ?_⟩
  obtain ⟨s₀, hs₀⟩ := hh0
  have hcod : ∀ᶠ s in codiscrete ℂ, h s ≠ 0 :=
    (hh.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_univ).resolve_left
      fun h0 ↦ hs₀ (h0 (mem_univ s₀))
  filter_upwards [hcod] with s hs f
  have hZs : AnalyticAt ℂ (Zc f) s := by
    apply (hNF f (mem_univ s)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    exact not_lt.mp fun hlt ↦ hs (h2 f s hlt)
  have hprod : AnalyticAt ℂ (h * Zc f) s := (hh s trivial).mul hZs
  have hval : T f s = h s * Zc f s := by
    have he := ((hTan f s).meromorphicNFAt.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
      hprod.meromorphicNFAt).mp (hTeq f s)
    exact he.eq_of_nhds
  rw [hEntT, hval, ← mul_assoc, hL s hs, one_mul]

/-- Moving a purely imaginary exponent `t` from the chart parameter into the unitary
character: the chart of `χ` at `s` is the chart of another unitary character at `s + t`. -/
private theorem infiniteEigendistribution_entire_family_shift (w : InfinitePlace F)
    (χ : PontryaginDual w.Completionˣ) (t : ℂ) (ht : t.re = 0) :
    ∃ χ₀ : PontryaginDual w.Completionˣ,
      (∀ g, (χ₀ g : ℂ) = quasiCharacterNormTwist (infiniteNorm(w)) (continuous_infiniteLocalModule w)
        ((circleToComplex).comp χ) (-t) g) ∧
      ∀ s, quasiCharacterNormTwist (infiniteNorm(w)) (continuous_infiniteLocalModule w)
          ((circleToComplex).comp χ) s =
        quasiCharacterNormTwist (infiniteNorm(w)) (continuous_infiniteLocalModule w)
          ((circleToComplex).comp χ₀) (s + t) := by
  let d := quasiCharacterNormTwist (infiniteNorm(w)) (continuous_infiniteLocalModule w)
    ((circleToComplex).comp χ) (-t)
  have hN (g : w.Completionˣ) : (0 : ℝ) < (((infiniteNorm(w) g : ℝ≥0) : ℝ)) :=
    NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))
  have hd (g : w.Completionˣ) : ‖d g‖ = 1 := by
    change ‖(χ g : ℂ) * ((((infiniteNorm(w) g : ℝ≥0) : ℝ) : ℂ)) ^ (-t)‖ = 1
    rw [norm_mul, Circle.norm_coe, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hN g),
      Complex.neg_re, ht, neg_zero, Real.rpow_zero]
  let χ₀ : PontryaginDual w.Completionˣ :=
    { toFun := fun g ↦ ⟨d g, mem_sphere_zero_iff_norm.mpr (hd g)⟩
      map_one' := Subtype.ext d.map_one
      map_mul' x y := Subtype.ext (d.map_mul x y)
      continuous_toFun := d.continuous.subtype_mk _ }
  refine ⟨χ₀, fun g ↦ rfl, fun s ↦ ContinuousMonoidHom.ext fun g ↦ ?_⟩
  have hN0 : ((((infiniteNorm(w) g : ℝ≥0) : ℝ) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr (hN g).ne'
  change (χ g : ℂ) * ((((infiniteNorm(w) g : ℝ≥0) : ℝ) : ℂ)) ^ s =
    ((χ g : ℂ) * ((((infiniteNorm(w) g : ℝ≥0) : ℝ) : ℂ)) ^ (-t)) *
      ((((infiniteNorm(w) g : ℝ≥0) : ℝ) : ℂ)) ^ (s + t)
  rw [mul_assoc, ← Complex.cpow_add _ _ hN0, neg_add_cancel_comm_assoc]

/-- An extended integer that is at least `-1` and negative is `-1`. -/
private theorem infiniteEigendistribution_entire_family_neg_one {x : WithTop ℤ}
    (h1 : (-1 : WithTop ℤ) ≤ x) (h2 : x < 0) : x = -1 := by
  refine le_antisymm ?_ h1
  revert h2
  induction x with
  | top => simp
  | coe m =>
    intro hm
    have : m < 0 := by exact_mod_cast hm
    show (m : WithTop ℤ) ≤ ((-1 : ℤ) : WithTop ℤ)
    exact WithTop.coe_le_coe.mpr (by omega)

/-- At a real place: the reciprocal Euler factor is entire and not identically zero, the
zeta function has at most simple poles, and they lie among the zeros of the reciprocal Euler
factor. -/
private theorem infiniteEigendistribution_entire_family_real (w : InfinitePlace F)
    (hw : w.IsReal) (χ : PontryaginDual w.Completionˣ) :
    let twist := quasiCharacterNormTwist (infiniteNorm(w)) (continuous_infiniteLocalModule w)
      ((circleToComplex).comp χ)
    AnalyticOnNhd ℂ (fun s ↦ (infiniteLocalEulerFactor w (twist s))⁻¹) univ ∧
      (∃ s, (infiniteLocalEulerFactor w (twist s))⁻¹ ≠ 0) ∧
      (∀ f s, (-1 : WithTop ℤ) ≤ meromorphicOrderAt (infiniteLocalIdelicZFunction w f ∘ twist) s) ∧
      (∀ f s, meromorphicOrderAt (infiniteLocalIdelicZFunction w f ∘ twist) s < 0 →
        (infiniteLocalEulerFactor w (twist s))⁻¹ = 0) := by
  intro twist
  obtain ⟨t, a, ht, hχ⟩ := realPlaceUnitary_shape w hw χ
  obtain ⟨χ₀, hg₀, hχ₀⟩ := infiniteEigendistribution_entire_family_shift w χ t ht
  have hs0 := realChart_shape w hw χ t a hχ (-t)
  simp only [neg_add_cancel] at hs0
  have hL (s : ℂ) : infiniteLocalEulerFactor w (twist s) = Complex.Gammaℝ (s + t + (a.val : ℂ)) := by
    have hp := (realLocalEulerParameters w hw (twist s)).unique
      (realLocalEulerParameters w hw (twist s)).exists.choose_spec (y₂ := (s + t, a))
      (realChart_shape w hw χ t a hχ s)
    simp only [infiniteLocalEulerFactor, hw, dite_true]
    rw [hp]
  have hcomp (f : ℬ(w.Completion)) : infiniteLocalIdelicZFunction w f ∘ twist =
      (infiniteLocalIdelicZFunction w f ∘ quasiCharacterNormTwist (infiniteNorm(w))
        (continuous_infiniteLocalModule w) ((circleToComplex).comp χ₀)) ∘ (· + t) :=
    funext fun s ↦ congrArg (infiniteLocalIdelicZFunction w f) (hχ₀ s)
  refine ⟨fun s _ ↦ ?_, ⟨1 - t - (a.val : ℂ), ?_⟩, fun f s ↦ ?_, fun f s hlt ↦ ?_⟩
  · simp only [hL]
    exact (Complex.differentiable_Gammaℝ_inv.comp
      ((differentiable_id.add_const t).add_const _)).analyticAt s
  · rw [hL, show 1 - t - (a.val : ℂ) + t + (a.val : ℂ) = 1 by ring]
    exact inv_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num))
  · rw [hcomp, meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt]
    exact (infiniteLocalIdelicZFunction_real_poles w hw χ₀ a (fun x ↦ (hg₀ _).trans (hs0 x)) (s + t)).1 f
  · rw [hcomp, meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt] at hlt
    have hP := infiniteLocalIdelicZFunction_real_poles w hw χ₀ a (fun x ↦ (hg₀ _).trans (hs0 x)) (s + t)
    obtain ⟨k, hk⟩ := hP.2.mp
      ⟨f, infiniteEigendistribution_entire_family_neg_one (hP.1 f) hlt⟩
    rw [hL, inv_eq_zero, Complex.Gammaℝ_eq_zero_iff]
    refine ⟨k, ?_⟩
    push_cast at hk
    linear_combination hk

/-- At a complex place: the reciprocal Euler factor is entire and not identically zero, the
zeta function has at most simple poles, and they lie among the zeros of the reciprocal Euler
factor. -/
private theorem infiniteEigendistribution_entire_family_complex (w : InfinitePlace F)
    (hw : w.IsComplex) (χ : PontryaginDual w.Completionˣ) :
    let twist := quasiCharacterNormTwist (infiniteNorm(w)) (continuous_infiniteLocalModule w)
      ((circleToComplex).comp χ)
    AnalyticOnNhd ℂ (fun s ↦ (infiniteLocalEulerFactor w (twist s))⁻¹) univ ∧
      (∃ s, (infiniteLocalEulerFactor w (twist s))⁻¹ ≠ 0) ∧
      (∀ f s, (-1 : WithTop ℤ) ≤ meromorphicOrderAt (infiniteLocalIdelicZFunction w f ∘ twist) s) ∧
      (∀ f s, meromorphicOrderAt (infiniteLocalIdelicZFunction w f ∘ twist) s < 0 →
        (infiniteLocalEulerFactor w (twist s))⁻¹ = 0) := by
  intro twist
  have hnr : ¬ w.IsReal := InfinitePlace.not_isReal_iff_isComplex.mpr hw
  obtain ⟨t, r, ht, hχ⟩ := complexPlaceUnitary_shape w hw χ
  obtain ⟨χ₀, hg₀, hχ₀⟩ := infiniteEigendistribution_entire_family_shift w χ t ht
  have hs0 := complexChart_shape w hw χ t r hχ (-t)
  simp only [neg_add_cancel] at hs0
  have hL (s : ℂ) : infiniteLocalEulerFactor w (twist s) =
      Complex.Gammaℂ (s + t + (r.natAbs : ℂ) / 2) / 2 := by
    have hp := (complexLocalEulerParameters w hw (twist s)).unique
      (complexLocalEulerParameters w hw (twist s)).exists.choose_spec (y₂ := (s + t, r))
      (complexChart_shape w hw χ t r hχ s)
    simp only [infiniteLocalEulerFactor, hnr, dite_false]
    rw [hp]
  have hcomp (f : ℬ(w.Completion)) : infiniteLocalIdelicZFunction w f ∘ twist =
      (infiniteLocalIdelicZFunction w f ∘ quasiCharacterNormTwist (infiniteNorm(w))
        (continuous_infiniteLocalModule w) ((circleToComplex).comp χ₀)) ∘ (· + t) :=
    funext fun s ↦ congrArg (infiniteLocalIdelicZFunction w f) (hχ₀ s)
  refine ⟨fun s _ ↦ ?_, ⟨1 - t - (r.natAbs : ℂ) / 2, ?_⟩, fun f s ↦ ?_, fun f s hlt ↦ ?_⟩
  · simp only [hL, inv_div]
    exact ((Complex.differentiable_Gammaℂ_inv.comp
      ((differentiable_id.add_const t).add_const _)).const_mul (2 : ℂ)).analyticAt s
  · rw [hL, show 1 - t - (r.natAbs : ℂ) / 2 + t + (r.natAbs : ℂ) / 2 = 1 by ring]
    refine inv_ne_zero (div_ne_zero ?_ two_ne_zero)
    have hpi : (2 * (Real.pi : ℂ)) ≠ 0 :=
      mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    simp [Complex.Gammaℂ_def, hpi]
  · rw [hcomp, meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt]
    exact (infiniteLocalIdelicZFunction_complex_poles w hw χ₀ r (fun x ↦ (hg₀ _).trans (hs0 x)) (s + t)).1 f
  · rw [hcomp, meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt] at hlt
    have hP := infiniteLocalIdelicZFunction_complex_poles w hw χ₀ r (fun x ↦ (hg₀ _).trans (hs0 x)) (s + t)
    obtain ⟨m, hm⟩ := hP.2.mp
      ⟨f, infiniteEigendistribution_entire_family_neg_one (hP.1 f) hlt⟩
    rw [hL, show s + t + (r.natAbs : ℂ) / 2 = -(m : ℂ) by linear_combination hm,
      Complex.Gammaℂ_def, Complex.Gamma_neg_nat_eq_zero]
    simp

/-- Paper: Theorem 3.4.3.3(1), (3.4.3.13), p. 153, with Lemma 3.3.2.1, p. 138. At an
infinite place the quotient of the local zeta function by the local Euler factor extends to an
entire family of distributions: there is `E : ℂ → StrongDual` with `s ↦ E s f` entire for every
test function `f`, such that off a discrete set of exponents `s` (the same for all `f`) the
meromorphic Z-function at `χ‖·‖^s` equals the Euler factor times `E s f`. -/
theorem infiniteEigendistribution_entire_family (w : InfinitePlace F)
    (χ : PontryaginDual w.Completionˣ) :
    let twist := quasiCharacterNormTwist (infiniteNorm(w)) (continuous_infiniteLocalModule w)
      ((circleToComplex).comp χ)
    ∃ E : ℂ → StrongDual ℂ ℬ(w.Completion), (∀ f, AnalyticOnNhd ℂ (fun s ↦ E s f) univ) ∧
      ∀ᶠ s : ℂ in codiscrete ℂ, ∀ f : ℬ(w.Completion),
        infiniteLocalIdelicZFunction w f (twist s) = infiniteLocalEulerFactor w (twist s) * E s f := by
  intro twist
  have hi := InfinitePlace.Completion.isometry_extensionEmbedding w
  let : ProperSpace w.Completion :=
    LipschitzWith.properSpace hi.isClosedEmbedding.isProperMap hi.lipschitzWith
  let : SecondCountableTopology (Multiplicative w.Completion) :=
    (hi.isEmbedding.secondCountableTopology : SecondCountableTopology w.Completion)
  let : LocallyCompactSpace (Multiplicative w.Completion) :=
    (inferInstance : LocallyCompactSpace w.Completion)
  have : BarrelledSpace ℂ (ℬ(w.Completion)) := schwartzBruhat_barrelled
  obtain ⟨D, hD, hDZ⟩ := infiniteLocalIdelicZFunction_distribution w χ
  have hpoles : AnalyticOnNhd ℂ (fun s ↦ (infiniteLocalEulerFactor w (twist s))⁻¹) univ ∧
      (∃ s, (infiniteLocalEulerFactor w (twist s))⁻¹ ≠ 0) ∧
      (∀ f s, (-1 : WithTop ℤ) ≤ meromorphicOrderAt (infiniteLocalIdelicZFunction w f ∘ twist) s) ∧
      (∀ f s, meromorphicOrderAt (infiniteLocalIdelicZFunction w f ∘ twist) s < 0 →
        (infiniteLocalEulerFactor w (twist s))⁻¹ = 0) := by
    by_cases hw : w.IsReal
    · exact infiniteEigendistribution_entire_family_real w hw χ
    · exact infiniteEigendistribution_entire_family_complex w
        (InfinitePlace.not_isReal_iff_isComplex.mp hw) χ
  obtain ⟨hh, hh0, h1, h2⟩ := hpoles
  exact infiniteEigendistribution_entire_family_assembly
    (fun hU Z hZ ↦ schwartzDistribution_holomorphic (G := Multiplicative w.Completion) hU Z hZ)
    (fun f ↦ infiniteLocalIdelicZFunction w f ∘ twist)
    (fun f ↦ ((infiniteLocalIdelicZFunction_existsUnique w f).exists.choose_spec χ).1)
    D _ hD hDZ _ (fun s ↦ infiniteLocalEulerFactor w (twist s)) hh hh0
    (fun s hs ↦ mul_inv_cancel₀ fun h0 ↦ hs (by rw [h0, inv_zero])) h1 h2

private theorem infiniteLocalIdelicZFunction_standardGaussian_real (w : InfinitePlace F)
    (hw : w.IsReal) (χ : PontryaginDual w.Completionˣ) (s : ℂ) (hs : 0 < s.re) :
    infiniteLocalIdelicZFunction w (infiniteStandardGaussian w χ)
        (quasiCharacterNormTwist (infiniteNorm(w)) (continuous_infiniteLocalModule w)
          ((circleToComplex).comp χ) s) =
      infiniteLocalEulerFactor w (quasiCharacterNormTwist (infiniteNorm(w))
        (continuous_infiniteLocalModule w) ((circleToComplex).comp χ) s) := by
  classical
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  let c := quasiCharacterNormTwist (infiniteNorm(w)) (continuous_infiniteLocalModule w)
    ((circleToComplex).comp χ) s
  obtain ⟨t, a, ht, hχ⟩ := realPlaceUnitary_shape w hw χ
  have hc := realChart_shape w hw χ t a hχ s
  have hz : 0 < (s + t).re := by rw [Complex.add_re, ht, add_zero]; exact hs
  have hE : infiniteLocalEulerFactor w c = Complex.Gammaℝ (s + t + (a.val : ℂ)) := by
    have hp := (realLocalEulerParameters w hw c).unique
      (realLocalEulerParameters w hw c).exists.choose_spec (y₂ := (s + t, a)) hc
    simp only [infiniteLocalEulerFactor, hw, dite_true]
    rw [hp]
  have hm1 : ((χ (-1) : Circle) : ℂ) = (-1 : ℂ) ^ a.val := by
    have h := hχ (-1)
    have hu : Units.map e.symm.toMonoidHom (-1 : ℝˣ) = -1 := Units.ext (by simp [e])
    rw [hu] at h
    change ((χ (-1) : Circle) : ℂ) = _ at h
    rw [h]
    norm_num
  obtain ⟨g, hg⟩ := realModelSchwartz w hw (infiniteStandardGaussian w χ)
  have hgv (x : ℝ) : g x =
      (((if χ (-1) = 1 then (1 : ℝ) else x) * Real.exp (-Real.pi * x ^ 2) : ℝ) : ℂ) := by
    rw [hg x]
    simp only [infiniteStandardGaussian, infiniteStandardGaussianValue, hw, dite_true]
    change (((if χ (-1) = 1 then (1 : ℝ) else e (e.symm x)) *
      Real.exp (-Real.pi * (e (e.symm x)) ^ 2) : ℝ) : ℂ) = _
    rw [e.apply_symm_apply]
  rw [infiniteLocalIdelicZFunction_eq_integral w _ χ (show s ∈ Complex.re ⁻¹' Ioi 0 from hs)]
  have he : (fun x : w.Completion ↦ infiniteStandardGaussian w χ (Multiplicative.ofAdd x)) =
      fun x ↦ g (e x) := by
    funext x
    simpa only [e, RingEquiv.symm_apply_apply] using (hg (e x)).symm
  rw [he, realIntegral_shape w hw g c (s + t) a hc hz, hE]
  have hgauss := mellin_gaussian Real.pi_pos hz
  obtain rfl | rfl : a = 0 ∨ a = 1 := by fin_cases a <;> simp
  · have h1 : χ (-1) = 1 := by
      apply Circle.coe_injective
      simpa using hm1
    have hfun : (fun x : ℝ ↦ g x + (-1 : ℂ) ^ (0 : Fin 2).val * g (-x)) =
        fun x : ℝ ↦ (2 : ℂ) • (Real.exp (-Real.pi * x ^ 2) : ℂ) := by
      funext x
      simp only [hgv, h1, ite_true, one_mul, neg_sq, Fin.val_zero, pow_zero, smul_eq_mul]
      ring
    rw [hfun, mellin_const_smul, hgauss, Complex.Gammaℝ_def]
    simp only [Fin.val_zero, Nat.cast_zero, add_zero, smul_eq_mul, neg_div]
    ring
  · have h1 : χ (-1) ≠ 1 := by
      intro h
      rw [h] at hm1
      norm_num at hm1
    have hfun : (fun x : ℝ ↦ g x + (-1 : ℂ) ^ (1 : Fin 2).val * g (-x)) =
        fun x : ℝ ↦ (x : ℂ) ^ (1 : ℂ) • ((2 : ℂ) • (Real.exp (-Real.pi * x ^ 2) : ℂ)) := by
      funext x
      simp only [hgv, h1, ite_false, neg_sq, Fin.val_one, pow_one, smul_eq_mul, Complex.cpow_one]
      push_cast
      ring
    have hz1 : 0 < (s + t + 1).re := by simp only [Complex.add_re, Complex.one_re]; linarith
    rw [hfun, mellin_cpow_smul, mellin_const_smul, mellin_gaussian Real.pi_pos hz1,
      Complex.Gammaℝ_def]
    simp only [Fin.val_one, Nat.cast_one, smul_eq_mul, neg_div]
    ring

private theorem infiniteLocalIdelicZFunction_standardGaussian_angular (r : ℤ) (u θ : ℝ) :
    Complex.exp ((r : ℂ) * (θ : ℂ) * Complex.I) *
      ((if 0 ≤ r then star ((u : ℂ) * Complex.exp (((1 : ℤ) : ℂ) * (θ : ℂ) * Complex.I)) ^ r.natAbs
        else ((u : ℂ) * Complex.exp (((1 : ℤ) : ℂ) * (θ : ℂ) * Complex.I)) ^ r.natAbs) *
        Complex.exp (-2 * (Real.pi : ℂ) * ((u : ℂ) * Complex.exp (((1 : ℤ) : ℂ) * (θ : ℂ) * Complex.I)) *
          star ((u : ℂ) * Complex.exp (((1 : ℤ) : ℂ) * (θ : ℂ) * Complex.I))) / (2 * (Real.pi : ℂ))) =
      (u : ℂ) ^ r.natAbs * (Real.exp (-(2 * Real.pi) * u ^ 2) : ℂ) / (2 * (Real.pi : ℂ)) := by
  set E := Complex.exp ((θ : ℂ) * Complex.I) with hEdef
  have hE1 : ((1 : ℤ) : ℂ) * (θ : ℂ) * Complex.I = (θ : ℂ) * Complex.I := by push_cast; ring
  have hstar : star E = Complex.exp (-((θ : ℂ) * Complex.I)) := by
    rw [hEdef, Complex.star_def, ← Complex.exp_conj]
    congr 1
    simp [Complex.conj_ofReal]
  have hEE : E * star E = 1 := by
    rw [hstar, hEdef, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hsq : (u : ℂ) * E * star ((u : ℂ) * E) = ((u ^ 2 : ℝ) : ℂ) := by
    rw [star_mul', Complex.star_def, Complex.conj_ofReal]
    calc (u : ℂ) * E * ((u : ℂ) * star E) = (u : ℂ) ^ 2 * (E * star E) := by ring
      _ = _ := by rw [hEE]; push_cast; ring
  have hexp : Complex.exp (-2 * (Real.pi : ℂ) * ((u : ℂ) * E) * star ((u : ℂ) * E)) =
      (Real.exp (-(2 * Real.pi) * u ^ 2) : ℂ) := by
    rw [mul_assoc (-2 * (Real.pi : ℂ)), hsq, Complex.ofReal_exp]
    push_cast
    ring_nf
  rw [hE1, ← hEdef, hexp]
  rcases Int.eq_nat_or_neg r with ⟨n, rfl | rfl⟩
  · have hr : Complex.exp (((n : ℤ) : ℂ) * (θ : ℂ) * Complex.I) = E ^ n := by
      rw [hEdef, ← Complex.exp_nat_mul]
      push_cast
      ring_nf
    rw [hr, ite_eq_left (Int.natCast_nonneg n), Int.natAbs_natCast, star_mul', Complex.star_def,
      Complex.conj_ofReal, mul_pow]
    calc E ^ n * ((u : ℂ) ^ n * star E ^ n * (Real.exp (-(2 * Real.pi) * u ^ 2) : ℂ) /
          (2 * (Real.pi : ℂ))) =
        (E * star E) ^ n * ((u : ℂ) ^ n * (Real.exp (-(2 * Real.pi) * u ^ 2) : ℂ) /
          (2 * (Real.pi : ℂ))) := by rw [mul_pow]; ring
      _ = _ := by rw [hEE, one_pow, one_mul]
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have hr : Complex.exp (((-(n : ℤ)) : ℤ) * (θ : ℂ) * Complex.I) = star E ^ n := by
      rw [hstar, ← Complex.exp_nat_mul]
      push_cast
      ring_nf
    have hneg : ¬ (0 ≤ -(n : ℤ)) := by omega
    rw [hr, ite_eq_right hneg, Int.natAbs_neg, Int.natAbs_natCast, mul_pow]
    calc star E ^ n * ((u : ℂ) ^ n * E ^ n * (Real.exp (-(2 * Real.pi) * u ^ 2) : ℂ) /
          (2 * (Real.pi : ℂ))) =
        (E * star E) ^ n * ((u : ℂ) ^ n * (Real.exp (-(2 * Real.pi) * u ^ 2) : ℂ) /
          (2 * (Real.pi : ℂ))) := by rw [mul_pow]; ring
      _ = _ := by rw [hEE, one_pow, one_mul]

private theorem infiniteLocalIdelicZFunction_standardGaussian_complex (w : InfinitePlace F)
    (hw : w.IsComplex) (χ : PontryaginDual w.Completionˣ) (s : ℂ) (hs : 0 < s.re) :
    infiniteLocalIdelicZFunction w (infiniteStandardGaussian w χ)
        (quasiCharacterNormTwist (infiniteNorm(w)) (continuous_infiniteLocalModule w)
          ((circleToComplex).comp χ) s) =
      infiniteLocalEulerFactor w (quasiCharacterNormTwist (infiniteNorm(w))
        (continuous_infiniteLocalModule w) ((circleToComplex).comp χ) s) := by
  have hnr : ¬ w.IsReal := InfinitePlace.not_isReal_iff_isComplex.mpr hw
  let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
  let c := quasiCharacterNormTwist (infiniteNorm(w)) (continuous_infiniteLocalModule w)
    ((circleToComplex).comp χ) s
  obtain ⟨t, r, ht, hχ⟩ := complexPlaceUnitary_shape w hw χ
  have hc := complexChart_shape w hw χ t r hχ s
  have hz : 0 < (s + t).re := by rw [Complex.add_re, ht, add_zero]; exact hs
  have hE : infiniteLocalEulerFactor w c = Complex.Gammaℂ (s + t + (r.natAbs : ℂ) / 2) / 2 := by
    have hp := (complexLocalEulerParameters w hw c).unique
      (complexLocalEulerParameters w hw c).exists.choose_spec (y₂ := (s + t, r)) hc
    simp only [infiniteLocalEulerFactor, hnr, dite_false]
    rw [hp]
  have hm (c' : ℂˣ →ₜ* ℂ) (hc' : ∀ x, ‖c' x‖ = 1)
      (hcc : ∀ x, c' x = ((circleToComplex).comp χ) (Units.map e.symm.toMonoidHom x)) :
      (existsUnique_complexUnits_character_parameters c' hc').exists.choose.2 = r := by
    have h := (existsUnique_complexUnits_character_parameters c' hc').unique
      (existsUnique_complexUnits_character_parameters c' hc').exists.choose_spec
      (y₂ := (t, r)) ⟨ht, fun x ↦ (hcc x).trans (hχ x)⟩
    rw [h]
  obtain ⟨g, hg⟩ := complexModelSchwartz w hw (infiniteStandardGaussian w χ)
  have hgv (x : ℂ) : g x = (if 0 ≤ r then (star x) ^ r.natAbs else x ^ r.natAbs) *
      Complex.exp (-2 * (Real.pi : ℂ) * x * star x) / (2 * (Real.pi : ℂ)) := by
    rw [congrFun hg x]
    simp only [infiniteStandardGaussian, infiniteStandardGaussianValue, hnr, dite_false]
    rw [hm]
    · change (if 0 ≤ r then (star (e (e.symm x))) ^ r.natAbs else (e (e.symm x)) ^ r.natAbs) *
        Complex.exp (-2 * (Real.pi : ℂ) * e (e.symm x) * star (e (e.symm x))) /
          (2 * (Real.pi : ℂ)) = _
      rw [e.apply_symm_apply]
    · intro x
      exact Circle.norm_coe _
    · intro x
      rfl
  rw [infiniteLocalIdelicZFunction_eq_integral w _ χ (show s ∈ Complex.re ⁻¹' Ioi 0 from hs)]
  have he : (fun x : w.Completion ↦ infiniteStandardGaussian w χ (Multiplicative.ofAdd x)) =
      fun x ↦ g (e x) := by
    funext x
    simpa only [e, RingEquiv.symm_apply_apply] using (congrFun hg (e x)).symm
  rw [he, complexIntegral_shape w hw g c (s + t) r hc hz, hE]
  have hprof : angularProfile g r = fun u : ℝ ↦
      (u : ℂ) ^ ((r.natAbs : ℕ) : ℂ) • (Real.exp (-(2 * Real.pi) * u ^ 2) : ℂ) := by
    funext u
    have hpt (θ : ℝ) : angularWeight r θ * g ((u : ℂ) * angularWeight 1 θ) =
        (u : ℂ) ^ r.natAbs * (Real.exp (-(2 * Real.pi) * u ^ 2) : ℂ) / (2 * (Real.pi : ℂ)) := by
      rw [hgv]
      exact infiniteLocalIdelicZFunction_standardGaussian_angular r u θ
    simp only [angularProfile, hpt, setIntegral_const, Complex.cpow_natCast, smul_eq_mul,
      Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
    rw [Complex.real_smul]
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    push_cast
    field_simp
    ring
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hv : 0 < (2 * (s + t) + ((r.natAbs : ℕ) : ℂ)).re := by
    simp only [Complex.add_re, Complex.mul_re, Complex.natCast_re]
    norm_num
    positivity
  rw [hprof, mellin_cpow_smul, mellin_gaussian h2pi hv, Complex.Gammaℂ_def]
  have hw2 : (2 * (s + t) + ((r.natAbs : ℕ) : ℂ)) / 2 = s + t + (r.natAbs : ℂ) / 2 := by ring
  rw [hw2]
  push_cast
  ring

/-- Paper: Definition 3.4.3.2 and the line after (3.4.3.9), p. 152. On the half-plane
`0 < re s`, the local zeta function of the standard Gaussian of `χ` at `χ‖·‖^s` is the local
Euler factor (the real or complex gamma factor).
Deviation: The complex Gaussian uses the conjugated monomial of `infiniteStandardGaussianValue`. -/
theorem infiniteLocalIdelicZFunction_standardGaussian (w : InfinitePlace F)
    (χ : PontryaginDual w.Completionˣ) (s : ℂ) (hs : 0 < s.re) :
    let twist := quasiCharacterNormTwist (infiniteNorm(w)) (continuous_infiniteLocalModule w)
      ((circleToComplex).comp χ)
    infiniteLocalIdelicZFunction w (infiniteStandardGaussian w χ) (twist s) =
      infiniteLocalEulerFactor w (twist s) := by
  by_cases hw : w.IsReal
  · exact infiniteLocalIdelicZFunction_standardGaussian_real w hw χ s hs
  · exact infiniteLocalIdelicZFunction_standardGaussian_complex w
      (InfinitePlace.not_isReal_iff_isComplex.mp hw) χ s hs

/-- Paper: Definition 3.4.3.1, p. 151, for the local zeta integral (3.3.2.1), p. 137. On the
half-plane `0 < re s`, translating the test function by a unit `g` (`f ↦ f(g⁻¹ ·)`)
multiplies the local zeta function at `c = χ‖·‖^s` by `c g`: by invariance of the
multiplicative Haar measure. -/
theorem infiniteLocalIdelicZFunction_unitTranslate (w : InfinitePlace F)
    (χ : PontryaginDual w.Completionˣ) (g : w.Completionˣ) (f : ℬ(w.Completion)) (s : ℂ)
    (hs : 0 < s.re) :
    let twist := quasiCharacterNormTwist (infiniteNorm(w)) (continuous_infiniteLocalModule w)
      ((circleToComplex).comp χ)
    infiniteLocalIdelicZFunction w (schwartzBruhatUnitTranslate g f) (twist s) =
      twist s g * infiniteLocalIdelicZFunction w f (twist s) := by
  intro twist
  let : MeasurableSpace w.Completion := borel _
  let : BorelSpace w.Completion := ⟨rfl⟩
  let : BorelSpace w.Completionˣ := borelSpace_units_of_continuousInv₀ _
  let : (infiniteLocalMultiplicativeTamagawaMeasure F w).IsHaarMeasure :=
    infiniteLocalMultiplicativeTamagawaMeasure_haar F w
  have hs' : s ∈ Complex.re ⁻¹' Ioi (0 : ℝ) := hs
  have e1 := infiniteLocalIdelicZFunction_eq_integral w (schwartzBruhatUnitTranslate g f) χ hs'
  have e2 := infiniteLocalIdelicZFunction_eq_integral w f χ hs'
  refine e1.trans (Eq.trans ?_ (congrArg (twist s g * ·) e2.symm))
  let c := twist s
  let b (u : w.Completionˣ) := f (Multiplicative.ofAdd u.val) * c u
  change (∫ u : w.Completionˣ, f (Multiplicative.ofAdd ((↑g⁻¹ : w.Completion) * u.val)) * c u
    ∂(infiniteLocalMultiplicativeTamagawaMeasure F w)) =
      c g * ∫ u, b u ∂(infiniteLocalMultiplicativeTamagawaMeasure F w)
  have he (u : w.Completionˣ) : c g * c (g⁻¹ * u) = c u :=
    (c.map_mul g (g⁻¹ * u)).symm.trans (congrArg c (mul_inv_cancel_left g u))
  have e (u : w.Completionˣ) : f (Multiplicative.ofAdd ((↑g⁻¹ : w.Completion) * u.val)) * c u =
      c g * b (g⁻¹ * u) :=
    (congrArg (f (Multiplicative.ofAdd (g⁻¹ * u).val) * ·) (he u).symm).trans (mul_left_comm _ _ _)
  exact (integral_congr_ae (ae_of_all _ e)).trans
    ((integral_const_mul (c g) _).trans (congrArg (c g * ·)
      (integral_mul_left_eq_self (μ := infiniteLocalMultiplicativeTamagawaMeasure F w) b (g⁻¹))))

/-- Paper: Equation (3.3.1.25), p. 134. On the half-plane `0 < re s` the infinite local
Euler factor at `χ‖·‖^s` does not vanish: it is a gamma factor evaluated at a point of
positive real part. -/
theorem infiniteLocalEulerFactor_twist_ne_zero (w : InfinitePlace F)
    (χ : PontryaginDual w.Completionˣ) (s : ℂ) (hs : 0 < s.re) :
    infiniteLocalEulerFactor w (quasiCharacterNormTwist (infiniteNorm(w))
      (continuous_infiniteLocalModule w) ((circleToComplex).comp χ) s) ≠ 0 := by
  let c := quasiCharacterNormTwist (infiniteNorm(w)) (continuous_infiniteLocalModule w)
    ((circleToComplex).comp χ) s
  have hval (g : w.Completionˣ) : c g = (χ g : ℂ) * ((((infiniteNorm(w) g : ℝ≥0) : ℝ)) : ℂ) ^ s := rfl
  have hnorm (g : w.Completionˣ) : ‖c g‖ = (((infiniteNorm(w) g : ℝ≥0) : ℝ)) ^ s.re := by
    have hpos : (0 : ℝ) < (((infiniteNorm(w) g : ℝ≥0) : ℝ)) :=
      NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))
    rw [hval, norm_mul, Circle.norm_coe, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos]
  have key (b t : ℝ) (hb : 1 < b) (h : b ^ s.re = b ^ t) : 0 < t := by
    have h1 : b ^ (0 : ℝ) < b ^ t := by rw [Real.rpow_zero, ← h]; exact Real.one_lt_rpow hb hs
    exact (Real.rpow_lt_rpow_left_iff hb).mp h1
  by_cases hw : w.IsReal
  · simp only [infiniteLocalEulerFactor, hw, ↓reduceDIte]
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    have hp := (realLocalEulerParameters w hw c).exists.choose_spec
    let x : ℝˣ := Units.mk0 2 two_ne_zero
    have hn : ‖((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm (x : ℝ) : w.Completion)‖ =
        ‖(x : ℝ)‖ :=
      (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.isometry.norm_map_of_map_zero
        (map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm) (x : ℝ)
    have hm : (((infiniteNorm(w) (Units.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toMonoidHom x) : ℝ≥0) : ℝ)) =
        ‖(x : ℝ)‖ := by
      simp [InfinitePlace.mult, hw, hn]
    have h0 := hp x
    have hx0 : (0 : ℝ) < (x : ℝ) := by norm_num [x]
    rw [if_pos hx0, one_pow, mul_one] at h0
    have h1 := congrArg norm h0
    rw [hnorm, hm, Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos_iff.mpr x.ne_zero)] at h1
    have hx1 : 1 < ‖(x : ℝ)‖ := by norm_num [x]
    have hre := key _ _ hx1 h1
    rw [Complex.add_re, Complex.natCast_re]
    positivity
  · have hc : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hw
    simp only [infiniteLocalEulerFactor, hw, ↓reduceDIte]
    refine div_ne_zero ?_ two_ne_zero
    have hp := (complexLocalEulerParameters w hc c).exists.choose_spec
    let x : ℂˣ := Units.mk0 2 two_ne_zero
    have hn : ‖((InfinitePlace.Completion.ringEquivComplexOfIsComplex hc).symm (x : ℂ) : w.Completion)‖ =
        ‖(x : ℂ)‖ :=
      (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc).symm.isometry.norm_map_of_map_zero
        (map_zero (InfinitePlace.Completion.ringEquivComplexOfIsComplex hc).symm) (x : ℂ)
    have hm : (((infiniteNorm(w) (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex hc).symm.toMonoidHom x) : ℝ≥0) : ℝ)) =
        ‖(x : ℂ)‖ ^ 2 := by
      simp [InfinitePlace.mult, hw, hn]
    have h0 := hp x
    have hx2 : (x : ℂ) / (‖(x : ℂ)‖ : ℂ) = 1 := by norm_num [x]
    rw [hx2, one_zpow, mul_one] at h0
    have h1 := congrArg norm h0
    rw [hnorm, hm, Complex.norm_cpow_eq_rpow_re_of_pos (pow_pos (norm_pos_iff.mpr x.ne_zero) 2)] at h1
    have hx1 : 1 < ‖(x : ℂ)‖ ^ 2 := by norm_num [x]
    have hre := key _ _ hx1 h1
    have hre' : 0 < ((complexLocalEulerParameters w hc c).exists.choose.1 +
        ((complexLocalEulerParameters w hc c).exists.choose.2.natAbs : ℂ) / 2).re := by
      rw [Complex.add_re, Complex.div_ofNat_re, Complex.natCast_re]
      positivity
    rw [Complex.Gammaℂ_def]
    refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Complex.Gamma_ne_zero_of_re_pos hre')
    have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    exact fun h ↦ hpi ((Complex.cpow_eq_zero_iff _ _).mp h).1

private theorem infiniteTwist_eval_analytic (w : InfinitePlace F) (χ : PontryaginDual w.Completionˣ)
    (g : w.Completionˣ) :
    AnalyticOnNhd ℂ (fun z : ℂ ↦ quasiCharacterNormTwist (infiniteNorm(w))
      (continuous_infiniteLocalModule w) ((circleToComplex).comp χ) z g) univ := by
  change AnalyticOnNhd ℂ (fun z : ℂ ↦ (χ g : ℂ) *
    ((((infiniteNorm(w) g : ℝ≥0) : ℝ) : ℂ)) ^ z) univ
  have hn : ((((infiniteNorm(w) g : ℝ≥0) : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (Units.ne_zero _))
  apply DifferentiableOn.analyticOnNhd _ isOpen_univ
  fun_prop (disch := simp [hn])

private theorem frequently_good_near_two {P : ℂ → Prop} (hP : ∀ᶠ s : ℂ in codiscrete ℂ, P s) :
    ∃ᶠ z : ℂ in 𝓝[≠] 2, P z ∧ 0 < z.re := by
  have hnear : ∀ᶠ z : ℂ in 𝓝[≠] 2, 0 < z.re :=
    (Complex.continuous_re.continuousAt.eventually (lt_mem_nhds (by norm_num : 0 < (2 : ℂ).re))).filter_mono
      nhdsWithin_le_nhds
  have hP2 : ∀ᶠ z : ℂ in 𝓝[≠] 2, P z := hP.filter_mono (nhdsNE_le_codiscrete 2)
  exact (hP2.and hnear).frequently

private theorem entire_eq_of_frequently {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f univ)
    (hg : AnalyticOnNhd ℂ g univ) (h : ∃ᶠ z : ℂ in 𝓝[≠] 2, f z = g z) (s : ℂ) : f s = g s :=
  hf.eqOn_of_preconnected_of_frequently_eq hg isPreconnected_univ (mem_univ 2) h (mem_univ s)

private theorem infiniteFamily_holomorphic (w : InfinitePlace F)
    (E : ℂ → StrongDual ℂ ℬ(w.Completion)) (hE : ∀ f, AnalyticOnNhd ℂ (fun s ↦ E s f) univ) :
    VectorHolomorphicOn E univ := by
  have hi := InfinitePlace.Completion.isometry_extensionEmbedding w
  let : ProperSpace w.Completion := LipschitzWith.properSpace hi.isClosedEmbedding.isProperMap hi.lipschitzWith
  let : SecondCountableTopology (Multiplicative w.Completion) :=
    (hi.isEmbedding.secondCountableTopology : SecondCountableTopology w.Completion)
  let : LocallyCompactSpace (Multiplicative w.Completion) :=
    (inferInstance : LocallyCompactSpace w.Completion)
  exact sbDual_holomorphic_of_analytic_eval (G := Multiplicative w.Completion) E hE

private theorem infiniteFamily_gaussian (w : InfinitePlace F) (χ : PontryaginDual w.Completionˣ)
    (E : ℂ → StrongDual ℂ ℬ(w.Completion)) (hE : ∀ f, AnalyticOnNhd ℂ (fun s ↦ E s f) univ)
    (hZ : ∀ᶠ s : ℂ in codiscrete ℂ, ∀ f : ℬ(w.Completion),
      infiniteLocalIdelicZFunction w f (quasiCharacterNormTwist (infiniteNorm(w))
        (continuous_infiniteLocalModule w) ((circleToComplex).comp χ) s) =
      infiniteLocalEulerFactor w (quasiCharacterNormTwist (infiniteNorm(w))
        (continuous_infiniteLocalModule w) ((circleToComplex).comp χ) s) * E s f) (s : ℂ) :
    E s (infiniteStandardGaussian w χ) = 1 := by
  refine entire_eq_of_frequently (hE _) analyticOnNhd_const ((frequently_good_near_two hZ).mono ?_) s
  intro z hz
  have h1 := hz.1 (infiniteStandardGaussian w χ)
  have h2 := infiniteLocalIdelicZFunction_standardGaussian w χ z hz.2
  have hL := infiniteLocalEulerFactor_twist_ne_zero w χ z hz.2
  exact mul_left_cancel₀ hL (h1.symm.trans (h2.trans (mul_one _).symm))

private theorem iff_of_normalized_generator {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (W : Submodule ℂ (StrongDual ℂ E)) (x : E) (D : StrongDual ℂ E)
    (huniq : ∀ T ∈ W, T x = 0 → T = 0) (hmem : D ∈ W) (hD : D x = 1) (T : StrongDual ℂ E) :
    T = D ↔ T ∈ W ∧ T x = 1 := by
  constructor
  · rintro rfl
    exact ⟨hmem, hD⟩
  · rintro ⟨hT, hTx⟩
    have h0 : (T - D) x = 0 := by
      rw [ContinuousLinearMap.sub_apply, hTx, hD, sub_self]
    exact sub_eq_zero.mp (huniq _ (W.sub_mem hT hmem) h0)

private theorem eq_mul_of_codiscrete_of_right {A B c L Z₁ Z₂ : ℂ → ℂ} (hA : AnalyticOnNhd ℂ A univ)
    (hB : AnalyticOnNhd ℂ B univ) (hc : AnalyticOnNhd ℂ c univ)
    (hZ : ∀ᶠ s : ℂ in codiscrete ℂ, Z₁ s = L s * A s ∧ Z₂ s = L s * B s)
    (hL : ∀ s : ℂ, 0 < s.re → L s ≠ 0) (h₃ : ∀ s : ℂ, 0 < s.re → Z₁ s = c s * Z₂ s) (s : ℂ) :
    A s = c s * B s := by
  refine entire_eq_of_frequently hA (hc.mul hB) ((frequently_good_near_two hZ).mono fun z hz ↦ ?_) s
  refine mul_left_cancel₀ (hL z hz.2) ?_
  rw [← hz.1.1, h₃ z hz.2, hz.1.2]
  ring

private theorem infiniteFamily_eigen (w : InfinitePlace F) (χ : PontryaginDual w.Completionˣ)
    (E : ℂ → StrongDual ℂ ℬ(w.Completion)) (hE : ∀ f, AnalyticOnNhd ℂ (fun s ↦ E s f) univ)
    (hZ : ∀ᶠ s : ℂ in codiscrete ℂ, ∀ f : ℬ(w.Completion),
      infiniteLocalIdelicZFunction w f ((quasiCharacterNormTwist (infiniteNorm(w)) (continuous_infiniteLocalModule w) ((circleToComplex).comp χ)) s) = infiniteLocalEulerFactor w ((quasiCharacterNormTwist (infiniteNorm(w)) (continuous_infiniteLocalModule w) ((circleToComplex).comp χ)) s) * E s f)
    (g : w.Completionˣ) (f : ℬ(w.Completion)) (s : ℂ) :
    E s (schwartzBruhatUnitTranslate g f) = (quasiCharacterNormTwist (infiniteNorm(w)) (continuous_infiniteLocalModule w) ((circleToComplex).comp χ)) s g * E s f :=
  eq_mul_of_codiscrete_of_right (A := fun s ↦ E s (schwartzBruhatUnitTranslate g f))
    (B := fun s ↦ E s f) (c := fun s ↦ (quasiCharacterNormTwist (infiniteNorm(w)) (continuous_infiniteLocalModule w) ((circleToComplex).comp χ)) s g) (L := fun s ↦ infiniteLocalEulerFactor w ((quasiCharacterNormTwist (infiniteNorm(w)) (continuous_infiniteLocalModule w) ((circleToComplex).comp χ)) s))
    (Z₁ := fun s ↦ infiniteLocalIdelicZFunction w (schwartzBruhatUnitTranslate g f) ((quasiCharacterNormTwist (infiniteNorm(w)) (continuous_infiniteLocalModule w) ((circleToComplex).comp χ)) s))
    (Z₂ := fun s ↦ infiniteLocalIdelicZFunction w f ((quasiCharacterNormTwist (infiniteNorm(w)) (continuous_infiniteLocalModule w) ((circleToComplex).comp χ)) s))
    (hE _) (hE f) (infiniteTwist_eval_analytic w χ g) (hZ.mono fun _ h ↦ ⟨h _, h f⟩)
    (fun s hs ↦ infiniteLocalEulerFactor_twist_ne_zero w χ s hs)
    (fun s hs ↦ infiniteLocalIdelicZFunction_unitTranslate w χ g f s hs) s

private theorem infiniteFamily_mem (w : InfinitePlace F) (χ : PontryaginDual w.Completionˣ)
    (E : ℂ → StrongDual ℂ ℬ(w.Completion)) (hE : ∀ f, AnalyticOnNhd ℂ (fun s ↦ E s f) univ)
    (hZ : ∀ᶠ s : ℂ in codiscrete ℂ, ∀ f : ℬ(w.Completion),
      infiniteLocalIdelicZFunction w f ((quasiCharacterNormTwist (infiniteNorm(w)) (continuous_infiniteLocalModule w) ((circleToComplex).comp χ)) s) = infiniteLocalEulerFactor w ((quasiCharacterNormTwist (infiniteNorm(w)) (continuous_infiniteLocalModule w) ((circleToComplex).comp χ)) s) * E s f)
    (s : ℂ) :
    E s ∈ schwartzBruhatEigendistributions ((quasiCharacterNormTwist (infiniteNorm(w)) (continuous_infiniteLocalModule w) ((circleToComplex).comp χ)) s) :=
  fun g f ↦ infiniteFamily_eigen w χ E hE hZ g f s

private theorem normalized_assembly {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (W : ℂ → Submodule ℂ (StrongDual ℂ E)) (x : E) (A Hol Q : (ℂ → StrongDual ℂ E) → Prop)
    (hex : ∃ D, A D ∧ Q D) (hHol : ∀ D, A D → Hol D)
    (hmem : ∀ D, A D → Q D → ∀ s, D s ∈ W s) (hone : ∀ D, A D → Q D → ∀ s, D s x = 1)
    (huniq : ∀ s, ∀ T ∈ W s, T x = 0 → T = 0) :
    ∃ D, Hol D ∧ (∀ s T, T = D s ↔ T ∈ W s ∧ T x = 1) ∧ Q D := by
  obtain ⟨D, hA, hQ⟩ := hex
  exact ⟨D, hHol D hA, fun s T ↦ iff_of_normalized_generator (W s) x (D s) (huniq s)
    (hmem D hA hQ s) (hone D hA hQ s) T, hQ⟩

/-- Paper: Theorem 3.4.3.3(1), p. 153. At an infinite place the normalized
eigendistribution evaluates to one on the Gaussian and varies holomorphically.
Multiplication by the Euler factor recovers the local zeta function.
Deviation: The complex Gaussian uses the corrected angular weight, and the meromorphic
identity (3.4.3.13) is expressed off a discrete set of exponents. -/
theorem infiniteEigendistribution_normalized (w : InfinitePlace F)
    (χ : PontryaginDual w.Completionˣ) :
    let twist := quasiCharacterNormTwist (infiniteNorm(w)) (continuous_infiniteLocalModule w)
      ((circleToComplex).comp χ)
    ∃ D : ℂ → StrongDual ℂ ℬ(w.Completion), VectorHolomorphicOn D univ ∧
      (∀ s : ℂ, ∀ T : StrongDual ℂ ℬ(w.Completion),
        T = D s ↔ T ∈ schwartzBruhatEigendistributions (twist s) ∧
          T (infiniteStandardGaussian w χ) = 1) ∧
      ∀ᶠ s : ℂ in codiscrete ℂ, ∀ f : ℬ(w.Completion),
        infiniteLocalIdelicZFunction w f (twist s) =
          infiniteLocalEulerFactor w (twist s) * D s f := by
  intro twist
  exact normalized_assembly (fun s ↦ schwartzBruhatEigendistributions (twist s))
    (infiniteStandardGaussian w χ) (fun E ↦ ∀ f, AnalyticOnNhd ℂ (fun s ↦ E s f) univ)
    (fun D ↦ VectorHolomorphicOn D univ)
    (fun D ↦ ∀ᶠ s : ℂ in codiscrete ℂ, ∀ f : ℬ(w.Completion),
      infiniteLocalIdelicZFunction w f (twist s) = infiniteLocalEulerFactor w (twist s) * D s f)
    (infiniteEigendistribution_entire_family w χ) (fun D hD ↦ infiniteFamily_holomorphic w D hD)
    (fun D hD hZ s ↦ infiniteFamily_mem w χ D hD hZ s)
    (fun D hD hZ s ↦ infiniteFamily_gaussian w χ D hD hZ s)
    (fun s T hT h ↦ infiniteEigendistribution_eq_zero_of_gaussian w χ s T hT h)

/-- Paper: Theorem 3.4.3.3(1), pp. 152–153. At an infinite place each
quasi-character has a one-dimensional eigendistribution space. -/
theorem infiniteEigendistributions_rank (w : InfinitePlace F) (c : QuasiCharacter w.Completionˣ) :
    Module.rank ℂ (schwartzBruhatEigendistributions c) = 1 := by
  have hi := InfinitePlace.Completion.isometry_extensionEmbedding w
  let : ProperSpace w.Completion := LipschitzWith.properSpace hi.isClosedEmbedding.isProperMap hi.lipschitzWith
  have hp : IsProperMap (infiniteNorm(w)) := isProperMap_units_nnNorm_pow w.mult w.mult_ne_zero
  have hne : ∃ g, infiniteNorm(w) g ≠ 1 := by
    have htwo : 1 < ‖(2 : w.Completion)‖ := by
      rw [← hi.norm_map_of_map_zero (map_zero _) (2 : w.Completion), map_ofNat]
      norm_num
    let u := Units.mk0 (2 : w.Completion) (by rintro h; rw [h, norm_zero] at htwo; linarith)
    refine ⟨u, fun he ↦ ?_⟩
    exact (one_lt_pow₀ htwo w.mult_ne_zero).ne' (congrArg (fun t : ℝ≥0ˣ ↦ ((t : ℝ≥0) : ℝ)) he)
  have hx : ∃ (χ : PontryaginDual (w.Completion)ˣ) (s : ℂ), quasiCharacterNormTwist (infiniteNorm(w)) hp.continuous ((circleToComplex).comp χ) s = c := exists_unitary_normTwist (infiniteNorm(w)) hp hne c
  refine hx.elim fun χ hχ ↦ hχ.elim fun s hs ↦ ?_
  exact (congrArg (fun d : QuasiCharacter (w.Completion)ˣ ↦ Module.rank ℂ (schwartzBruhatEigendistributions d)) hs.symm).trans
    (rank_one_of_unique_normalization _ _ ((infiniteEigendistribution_normalized w χ).choose s)
      ((infiniteEigendistribution_normalized w χ).choose_spec.2.1 s))


section
open scoped Classical
local notation "χ∞(" χ "," w ")" => infiniteUnitaryRestriction(χ,w)
local notation "χv(" χ "," v ")" => ((χ).comp ⟨IdeleClassGroup.ofAdicCompletion (𝓞 F) F v, continuous_ideleClass_ofAdicCompletion F v⟩)
local notation "arc(" χ "," w "," z ")" => quasiCharacterNormTwist (infiniteNorm(w)) (continuous_infiniteLocalModule w) ((circleToComplex).comp χ∞(χ,w)) z
local notation "fin(" χ "," v "," z ")" => quasiCharacterNormTwist (finiteNorm(v)) (continuous_finiteLocalModule v) ((circleToComplex).comp χv(χ,v)) z
local notation "μ∞" => infiniteLocalMultiplicativeTamagawaMeasure F
local notation "μv" => finiteLocalMultiplicativeTamagawaMeasure F
attribute [local instance] instMeasurableSpaceUnitsAdicCompletionSec4
private local instance (w : InfinitePlace F) : MeasurableSpace w.Completion := borel _

private theorem infinitePlaceRestriction_eq_twist (χ : PontryaginDual C_F) (w : InfinitePlace F) (z : ℂ) :
    infinitePlaceRestriction F w (ideleClassNormTwist χ z) = arc(χ,w,z) :=
  ContinuousMonoidHom.ext fun g ↦ infinitePlaceRestriction_twist_apply w χ z g

private theorem finitePlaceRestriction_eq_twist (χ : PontryaginDual C_F) (v : V) (z : ℂ) :
    finitePlaceRestriction F v (ideleClassNormTwist χ z) = fin(χ,v,z) := by
  ext g
  change _ * (((ideleClassNorm F (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v g) : ℝ≥0) : ℝ) : ℂ) ^ z = _
  rw [ideleClassNorm_ofAdicCompletion]
  rfl

private theorem finiteGaussian_twist_eq (χ : PontryaginDual C_F) (v : V) (z : ℂ) :
    finiteStandardGaussian v (finitePlaceRestriction F v (ideleClassNormTwist χ z)) =
      finiteStandardGaussian v (finitePlaceRestriction F v (ideleClassNormTwist χ 0)) := by
  let c (t : ℂ) := finitePlaceRestriction F v (ideleClassNormTwist χ t)
  have he (g : (v.adicCompletion F)ˣ) (hg : g ∈ integerUnits(v)) : c z g = c 0 g :=
    (finitePlaceRestriction_twist_unit χ v g hg z).trans (finitePlaceRestriction_twist_unit χ v g hg 0).symm
  have hu : unramified(v, (c z)) ↔ unramified(v, (c 0)) :=
    forall_congr' fun g ↦ forall_congr' fun hg ↦ by rw [he g hg]
  apply Subtype.ext
  funext x
  by_cases hx : x.toAdd ∈ Units.val '' integerUnits(v)
  · obtain ⟨g, hg, hx⟩ := hx
    change finiteStandardGaussian v (c z) (Multiplicative.ofAdd x.toAdd) = finiteStandardGaussian v (c 0) (Multiplicative.ofAdd x.toAdd)
    rw [← hx, finiteStandardGaussian_integerUnit v _ g hg, finiteStandardGaussian_integerUnit v _ g hg, he g hg]
  · change finiteStandardGaussianValue v (c z) x.toAdd = finiteStandardGaussianValue v (c 0) x.toAdd
    simp only [finiteStandardGaussianValue, hu, indicator_of_notMem hx]

private theorem finite_twist_ne_one (χ : PontryaginDual C_F) (v : V) {z : ℂ} (hz : 0 < z.re) :
    fin(χ,v,z) ≠ 1 := by
  let val : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
  obtain ⟨π, hπ⟩ := val.exists_isUniformizer_of_isCyclic_of_nontrivial
  let g := Units.mk0 (π : v.adicCompletion F) hπ.ne_zero
  have hlt : ‖g.val‖ < 1 := Valued.toNormedField.norm_lt_one_iff.mpr hπ.val_lt_one
  have hpos : 0 < ‖g.val‖ := norm_pos_iff.mpr g.ne_zero
  intro he
  have hh := congrArg (fun d : QuasiCharacter (v.adicCompletion F)ˣ ↦ ‖d g‖) he
  change ‖(χv(χ,v) g : ℂ) * (‖g.val‖ : ℂ) ^ z‖ = ‖(1 : ℂ)‖ at hh
  rw [norm_one, norm_mul, Circle.norm_coe, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos] at hh
  exact (Real.rpow_lt_one hpos.le hlt hz).ne hh

private theorem analytic_eval_normalized {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [ContinuousSMul ℂ E] {D : ℂ → StrongDual ℂ E} (hD : VectorHolomorphicOn D univ) (f : E) :
    AnalyticOnNhd ℂ (fun z ↦ D z f) univ := by
  let e : StrongDual ℂ E →L[ℂ] ℂ := ContinuousLinearMap.applyₗ ℂ (RingHom.id ℂ) f
  exact (vectorHolomorphicOn_weaklyHolomorphic isOpen_univ hD e).analyticOnNhd isOpen_univ

local notation "DA(" χ "," w ")" => (infiniteEigendistribution_normalized w χ∞(χ,w)).choose
local notation "DB(" χ "," v ")" => (finiteEigendistribution_normalized v χv(χ,v)).choose
local notation "a₀(" χ "," w ")" => infiniteStandardGaussian w χ∞(χ,w)
local notation "b₀(" χ "," v ")" => finiteStandardGaussian v (finitePlaceRestriction F v (ideleClassNormTwist χ 0))
local notation "ZA(" χ "," w "," z "," a ")" => localIdelicZetaIntegral (μ∞ w) (fun y ↦ (a) (Multiplicative.ofAdd y)) (infinitePlaceRestriction F w (ideleClassNormTwist χ z))
local notation "ZB(" χ "," v "," z "," b ")" => localIdelicZetaIntegral (μv v) (fun y ↦ (b) (Multiplicative.ofAdd y)) (finitePlaceRestriction F v (ideleClassNormTwist χ z))

private theorem infiniteIntegral_normalized_ratio (χ : PontryaginDual C_F) (w : InfinitePlace F) :
    ∀ᶠ z : ℂ in 𝓝[≠] 2, ∀ f : ℬ(w.Completion), ZA(χ,w,z,f) = ZA(χ,w,z,a₀(χ,w)) * DA(χ,w) z f := by
  let G := a₀(χ,w)
  have hnear : ∀ᶠ z : ℂ in 𝓝[≠] 2, 0 < z.re :=
    (Complex.continuous_re.continuousAt.eventually (lt_mem_nhds (by norm_num : 0 < (2 : ℂ).re))).filter_mono nhdsWithin_le_nhds
  have hZ : ∀ᶠ z : ℂ in 𝓝[≠] 2, ∀ f : ℬ(w.Completion),
      infiniteLocalIdelicZFunction w f (arc(χ,w,z)) = infiniteLocalEulerFactor w (arc(χ,w,z)) * DA(χ,w) z f :=
    eventually_codiscrete_iff_forall_eventually_nhdsNE.mp (infiniteEigendistribution_normalized w χ∞(χ,w)).choose_spec.2.2 2
  refine (hnear.and hZ).mono fun z hh f ↦ ?_
  have hG : DA(χ,w) z G = 1 := (((infiniteEigendistribution_normalized w χ∞(χ,w)).choose_spec.2.1 z _).mp rfl).2
  have he (k : ℬ(w.Completion)) : ZA(χ,w,z,k) = infiniteLocalEulerFactor w (arc(χ,w,z)) * DA(χ,w) z k :=
    (congrArg (localIdelicZetaIntegral (μ∞ w) (fun y ↦ k (Multiplicative.ofAdd y)))
      (infinitePlaceRestriction_eq_twist χ w z)).trans
      ((infiniteLocalIdelicZFunction_eq_integral w k χ∞(χ,w) hh.1).symm.trans (hh.2 k))
  have heG := (he G).trans ((congrArg (_ * ·) hG).trans (mul_one _))
  exact (he f).trans (congrArg (· * _) heG.symm)

private theorem finiteIntegral_normalized_ratio (χ : PontryaginDual C_F) (v : V) {z : ℂ} (hz : 0 < z.re)
    (f : ℬ(v.adicCompletion F)) : ZB(χ,v,z,f) = ZB(χ,v,z,b₀(χ,v)) * DB(χ,v) z f := by
  let G := b₀(χ,v)
  have heG : finiteStandardGaussian v (fin(χ,v,z)) = G :=
    (congrArg (finiteStandardGaussian v) (finitePlaceRestriction_eq_twist χ v z).symm).trans (finiteGaussian_twist_eq χ v z)
  have hG : DB(χ,v) z G = 1 := (congrArg (DB(χ,v) z) heG.symm).trans
    ((((finiteEigendistribution_normalized v χv(χ,v)).choose_spec.2.1 z _).mp rfl).2)
  let factor := (((μv v) integerUnits(v)).toReal : ℂ) * finiteLocalEulerFactor v (fin(χ,v,z))
  have he (k : ℬ(v.adicCompletion F)) : ZB(χ,v,z,k) = factor * DB(χ,v) z k :=
    (congrArg (localIdelicZetaIntegral (μv v) (fun y ↦ k (Multiplicative.ofAdd y)))
      (finitePlaceRestriction_eq_twist χ v z)).trans
      ((finiteLocalIdelicZFunction_eq_integral v k χv(χ,v) hz).symm.trans
        ((finiteEigendistribution_normalized v χv(χ,v)).choose_spec.2.2 z (finite_twist_ne_one χ v hz) k))
  exact (he f).trans (congrArg (· * _) ((he G).trans ((congrArg (factor * ·) hG).trans (mul_one _))).symm)

private theorem prod_mul_of_eq_mul {ι : Type*} [Fintype ι] (a b d : ι → ℂ) (h : ∀ i, a i = b i * d i) :
    (∏ i, a i) = (∏ i, b i) * ∏ i, d i :=
  (Finset.prod_congr rfl (fun i _ ↦ h i)).trans Finset.prod_mul_distrib

private theorem globalIntegral_tensor_ratio (χ : PontryaginDual C_F) (z : ℂ) (hz : 1 < z.re)
    (S : Finset V) (hc : ideleClassNormTwist χ z ∈ unramifiedOutside F S)
    (fS gS : ℬ(SAdeleRing F S)) (a : (w : InfinitePlace F) → ℬ(w.Completion)) (b : (v : V) → ℬ(v.adicCompletion F))
    (hf : ∀ x : SAdeleRing F S, fS (Multiplicative.ofAdd x) =
      (∏ w, a w (Multiplicative.ofAdd (x.1 w))) * ∏ v : S, b v.val (Multiplicative.ofAdd (x.2 v)))
    (hg : ∀ x : SAdeleRing F S, gS (Multiplicative.ofAdd x) =
      (∏ w, a₀(χ,w) (Multiplicative.ofAdd (x.1 w))) * ∏ v : S, b₀(χ,v.val) (Multiplicative.ofAdd (x.2 v)))
    (hA : ∀ w, ZA(χ,w,z,a w) = ZA(χ,w,z,a₀(χ,w)) * DA(χ,w) z (a w)) :
    globalIdelicZetaIntegral (sAdeleSchwartzToGlobal F S fS) (ideleClassNormTwist χ z) =
      globalIdelicZetaIntegral (sAdeleSchwartzToGlobal F S gS) (ideleClassNormTwist χ z) *
        ((∏ w, DA(χ,w) z (a w)) * ∏ v : S, DB(χ,v.val) z (b v.val)) := by
  let c := ideleClassNormTwist χ z
  let P := (∏ᶠ v : {v : V // v ∉ S}, (((μv v.val) integerUnits(v.val)).toReal : ℂ))
  let Q := ∏' v : {v : V // v ∉ S}, finiteHeckeEulerFactor χ v.val z
  let A := ∏ w, ZA(χ,w,z,a₀(χ,w))
  let B := ∏ v : S, ZB(χ,v.val,z,b₀(χ,v.val))
  let X₁ := ∏ w, DA(χ,w) z (a w)
  let X₂ := ∏ v : S, DB(χ,v.val) z (b v.val)
  have hA' : (∏ w, ZA(χ,w,z,a w)) = A * X₁ :=
    prod_mul_of_eq_mul (fun w ↦ ZA(χ,w,z,a w)) (fun w ↦ ZA(χ,w,z,a₀(χ,w))) (fun w ↦ DA(χ,w) z (a w)) hA
  have hB' : (∏ v : S, ZB(χ,v.val,z,b v.val)) = B * X₂ :=
    prod_mul_of_eq_mul (fun v : S ↦ ZB(χ,v.val,z,b v.val)) (fun v : S ↦ ZB(χ,v.val,z,b₀(χ,v.val)))
      (fun v : S ↦ DB(χ,v.val) z (b v.val)) (fun v ↦ finiteIntegral_normalized_ratio χ v.val (zero_lt_one.trans hz) (b v.val))
  have hF := (sLocalIntegral_pureTensor S fS a b hf c hc).trans (congrArg₂ (· * ·) hA' hB')
  have hG := sLocalIntegral_pureTensor S gS (fun w ↦ a₀(χ,w)) (fun v ↦ b₀(χ,v)) hg c hc
  have eF := (weilIdentity_unramifiedOutside S fS χ z hz hc).trans (congrArg (fun t ↦ P * t * Q) hF)
  have eG := (weilIdentity_unramifiedOutside S gS χ z hz hc).trans (congrArg (fun t ↦ P * t * Q) hG)
  refine eF.trans (Eq.trans ?_ (congrArg (· * (X₁ * X₂)) eG.symm))
  change P * (A * X₁ * (B * X₂)) * Q = P * (A * B) * Q * (X₁ * X₂)
  ring

private theorem exists_pair_in_stage {ι E : Type*} {B : Finset ι → Type*}
    (ιS : ∀ S, B S → E) (cover : ∀ x, ∃ S y, ιS S y = x)
    (grow : ∀ {S T : Finset ι}, S ⊆ T → ∀ y, ∃ z, ιS T z = ιS S y)
    (f g : E) (R : Finset ι) :
    ∃ S : Finset ι, R ⊆ S ∧ ∃ a b, ιS S a = f ∧ ιS S b = g := by
  classical
  obtain ⟨P, p, hp⟩ := cover f
  obtain ⟨Q, q, hq⟩ := cover g
  let S := R ∪ (P ∪ Q)
  have hP : P ⊆ S := fun _ h ↦ Finset.mem_union_right R (Finset.mem_union_left Q h)
  have hQ : Q ⊆ S := fun _ h ↦ Finset.mem_union_right R (Finset.mem_union_right P h)
  obtain ⟨a, ha⟩ := grow hP p
  obtain ⟨b, hb⟩ := grow hQ q
  exact ⟨S, Finset.subset_union_left, a, b, ha.trans hp, hb.trans hq⟩

private theorem exists_pair_sAdeleStage (f g : ℬ(𝔸[F])) (R : Finset V) :
    ∃ S : Finset V, R ⊆ S ∧ ∃ (fS gS : ℬ(SAdeleRing F S)),
      sAdeleSchwartzToGlobal F S fS = f ∧ sAdeleSchwartzToGlobal F S gS = g := by
  apply exists_pair_in_stage (B := fun S : Finset V ↦ ℬ(SAdeleRing F S))
    (fun S x ↦ sAdeleSchwartzToGlobal F S x) (sAdeleSchwartzToGlobal_exhaustive F)
  intro P Q h y
  exact ⟨sAdeleSchwartzTransition F h y, LinearMap.congr_fun (sAdeleSchwartzToGlobal_comp F h) y⟩

private theorem exists_normalized_stage (χ : PontryaginDual C_F) (s : ℂ)
    (f : ℬ(𝔸[F])) (b : (v : V) → ℬ(v.adicCompletion F))
    (htail : ∀ᶠ v in cofinite, b v = finiteStandardGaussian v (finitePlaceRestriction F v (ideleClassNormTwist χ s))) :
    ∃ S : Finset V, (∀ z : ℂ, ideleClassNormTwist χ z ∈ unramifiedOutside F S) ∧
      (∀ v ∉ S, b v = finiteStandardGaussian v (finitePlaceRestriction F v (ideleClassNormTwist χ s))) ∧
      ∃ (fS gS : ℬ(SAdeleRing F S)), sAdeleSchwartzToGlobal F S fS = f ∧
        sAdeleSchwartzToGlobal F S gS = adelicStandardGaussian χ := by
  classical
  have hcov : ∃ R : Finset V, ideleClassNormTwist χ 0 ∈ unramifiedOutside F R :=
    mem_iUnion.mp (eq_univ_iff_forall.mp (iUnion_unramifiedOutside F) (ideleClassNormTwist χ 0))
  refine hcov.elim fun R hR ↦ ?_
  let p (v : V) := b v = finiteStandardGaussian v (finitePlaceRestriction F v (ideleClassNormTwist χ s))
  have hfinite : {v : V | ¬p v}.Finite := eventually_cofinite.mp (show ∀ᶠ v in cofinite, p v from htail)
  let U := hfinite.toFinset
  refine (exists_pair_sAdeleStage (F := F) f (adelicStandardGaussian χ) (R ∪ U)).elim fun S hstage ↦ ?_
  have hRS : R ∪ U ⊆ S := hstage.1
  refine ⟨S, fun z v hv ↦ (ideleClassNormTwist_unramified_iff χ z v).mpr
    (hR v fun h ↦ hv (hRS (Finset.mem_union_left U h))), ?_, hstage.2⟩
  intro v hv
  by_contra hn
  exact hv (hRS (Finset.mem_union_right R (hfinite.mem_toFinset.mpr hn)))

private theorem all_infiniteIntegral_normalized_ratio (χ : PontryaginDual C_F) : ∀ᶠ z : ℂ in 𝓝[≠] 2, ∀ w : InfinitePlace F, ∀ k : ℬ(w.Completion),
      ZA(χ,w,z,k) = ZA(χ,w,z,a₀(χ,w)) * DA(χ,w) z k :=
    (eventually_all (ι := InfinitePlace F) (l := 𝓝[≠] (2 : ℂ))
      (p := fun w z ↦ ∀ k : ℬ(w.Completion), ZA(χ,w,z,k) = ZA(χ,w,z,a₀(χ,w)) * DA(χ,w) z k)).mpr
      (infiniteIntegral_normalized_ratio χ)

section
open scoped TensorProduct
attribute [local instance] uniformContinuousConstSMul_of_continuousConstSMul

section
private local instance : MeasurableSpace I_F := borel _
private local instance : BorelSpace I_F := ⟨rfl⟩

private def globalIntegralDual (χ : PontryaginDual C_F) (z : ℂ) (hz : 1 < z.re) : StrongDual ℂ ℬ(𝔸[F]) := by
  let c := ideleClassNormTwist χ z
  have hc : 1 < quasiCharacterAbscissa (ideleClassNorm F) (isProperMap_ideleClassNorm F)
      (ideleClassNorm_ne_one (F := F)) c := hz.trans_eq (ideleClassNormTwist_abscissa χ z).symm
  let I : ℬ(𝔸[F]) →ₗ[ℂ] ℂ :=
    { toFun := fun f ↦ globalIdelicZetaIntegral f c
      map_add' := fun f k ↦ (integral_congr_ae (ae_of_all _ (fun g : I_F ↦
        add_mul (f (Multiplicative.ofAdd g.val)) (k (Multiplicative.ofAdd g.val)) (c (classOf g))))).trans
        (integral_add (globalIdelicZetaIntegral_integrable f c hc) (globalIdelicZetaIntegral_integrable k c hc))
      map_smul' := fun t f ↦ (integral_congr_ae (ae_of_all _ (fun g : I_F ↦
        mul_assoc t (f (Multiplicative.ofAdd g.val)) (c (classOf g))))).trans
        (integral_const_mul t (fun g : I_F ↦ f (Multiplicative.ofAdd g.val) * c (classOf g))) }
  exact ⟨I, continuous_globalIdelicZetaIntegral c hc⟩

private theorem globalIntegralDual_eigen (χ : PontryaginDual C_F) (z : ℂ) (hz : 1 < z.re) :
    globalIntegralDual χ z hz ∈ adelicEigendistributions (ideleClassNormTwist χ z) := by
  let c := ideleClassNormTwist χ z
  let d : QuasiCharacter I_F := c.comp ⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩
  let : (multiplicativeTamagawaMeasure F).IsHaarMeasure := (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.1
  intro g f
  let b (u : I_F) := f (Multiplicative.ofAdd u.val) * d u
  change (∫ u : I_F, f (Multiplicative.ofAdd ((↑g⁻¹ : 𝔸[F]) * u.val)) * d u ∂multiplicativeTamagawaMeasure F) =
    d g * ∫ u, b u ∂multiplicativeTamagawaMeasure F
  have he (u : I_F) : d g * d (g⁻¹ * u) = d u :=
    (d.map_mul g (g⁻¹ * u)).symm.trans (congrArg d (mul_inv_cancel_left g u))
  have e (u : I_F) : f (Multiplicative.ofAdd ((↑g⁻¹ : 𝔸[F]) * u.val)) * d u = d g * b (g⁻¹ * u) :=
    (congrArg (f (Multiplicative.ofAdd (g⁻¹ * u).val) * ·) (he u).symm).trans (mul_left_comm _ _ _)
  exact (integral_congr_ae (ae_of_all _ e)).trans
    ((integral_const_mul (d g) _).trans (congrArg (d g * ·) (integral_mul_left_eq_self b (g⁻¹))))

end

private theorem vectorHolomorphicOn_bilinear {E H P : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    [AddCommGroup H] [Module ℂ H] [TopologicalSpace H] [IsTopologicalAddGroup H] [ContinuousSMul ℂ H]
    [AddCommGroup P] [Module ℂ P] [TopologicalSpace P] [IsTopologicalAddGroup P] [ContinuousSMul ℂ P]
    (B : E →ₗ[ℂ] H →ₗ[ℂ] P) (hB : Continuous (fun p : E × H ↦ B p.1 p.2))
    {f : ℂ → E} {g : ℂ → H} (hf : VectorHolomorphicOn f univ) (hg : VectorHolomorphicOn g univ) :
    VectorHolomorphicOn (fun z ↦ B (f z) (g z)) univ := by
  apply (vectorHolomorphicOn_iff_tendsto isOpen_univ _).mpr
  intro z hz
  obtain ⟨v, hv⟩ := (vectorHolomorphicOn_iff_tendsto isOpen_univ f).mp hf z hz
  obtain ⟨w, hw⟩ := (vectorHolomorphicOn_iff_tendsto isOpen_univ g).mp hg z hz
  have hc : Tendsto g (𝓝[≠] z) (𝓝 (g z)) :=
    ((hg.continuousOn.continuousAt (univ_mem : univ ∈ 𝓝 z))).tendsto.mono_left nhdsWithin_le_nhds
  have h1 := (hB.tendsto (v, g z)).comp (hv.prodMk_nhds hc)
  have h2 := (hB.tendsto (f z, w)).comp (tendsto_const_nhds.prodMk_nhds hw)
  refine ⟨B v (g z) + B (f z) w, (h1.add h2).congr fun t ↦ ?_⟩
  change B ((t - z)⁻¹ • (f t - f z)) (g t) + B (f z) ((t - z)⁻¹ • (g t - g z)) = _
  rw [B.map_smul, LinearMap.smul_apply, map_smul, ← smul_add, B.map_sub, LinearMap.sub_apply, map_sub]
  congr 1
  abel

private theorem vectorHolomorphicOn_postcomp {E P : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    [AddCommGroup P] [Module ℂ P] [TopologicalSpace P] [IsTopologicalAddGroup P] [ContinuousSMul ℂ P]
    (L : E →L[ℂ] P) {f : ℂ → E} (hf : VectorHolomorphicOn f univ) :
    VectorHolomorphicOn (fun z ↦ L (f z)) univ :=
  fun z hz ↦ ⟨_, (hf.hasDerivAt_comp isOpen_univ L ⟨z, hz⟩).hasFDerivAt.hasFDerivWithinAt⟩

private local instance {W : Type*} [AddCommGroup W] [Module ℂ W] {ι : Type*}
    (p : SeminormFamily ℂ W ι) : ContinuousSMul ℂ (WithGeneratingSeminorms W p) :=
  (withGeneratingSeminorms_spec W p).continuousSMul

private theorem holomorphic_projectiveTensor {A B : Type*}
    [AddCommGroup A] [Module ℂ A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [ContinuousSMul ℂ A] [PolynormableSpace ℂ A]
    [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] [IsTopologicalAddGroup B]
    [ContinuousSMul ℂ B] [PolynormableSpace ℂ B]
    {Z : Type*} [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z] [IsTopologicalAddGroup Z] [ContinuousSMul ℂ Z]
    (e : UniformSpace.Completion (ProjectiveTensor A B) ≃L[ℂ] Z)
    (a : ℂ → A) (b : ℂ → B) (ha : VectorHolomorphicOn a univ) (hb : VectorHolomorphicOn b univ) :
    VectorHolomorphicOn (fun z ↦ e (UniformSpace.Completion.coe' (α := ProjectiveTensor A B) (a z ⊗ₜ[ℂ] b z))) univ := by
  let Q := ProjectiveTensor A B
  let tm : A →ₗ[ℂ] B →ₗ[ℂ] Q := TensorProduct.mk ℂ A B
  have htm : Continuous (fun p : A × B ↦ tm p.1 p.2) := continuous_projectiveTensor_tmul
  have ht := vectorHolomorphicOn_bilinear tm htm ha hb
  let j : Q →L[ℂ] UniformSpace.Completion Q := UniformSpace.Completion.toComplL
  let L : Q →L[ℂ] Z := e.toContinuousLinearMap.comp j
  exact vectorHolomorphicOn_postcomp L ht

private theorem schwartzBruhat_dual_tensor_family {G H : Type*}
    [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] [LocallyCompactSpace H] [SecondCountableTopology H]
    (D : ℂ → StrongDual ℂ (SchwartzBruhat G)) (E : ℂ → StrongDual ℂ (SchwartzBruhat H))
    (hD : VectorHolomorphicOn D univ) (hE : VectorHolomorphicOn E univ) :
    ∃ P : ℂ → StrongDual ℂ (SchwartzBruhat (G × H)), VectorHolomorphicOn P univ ∧
      ∀ (z : ℂ) (a : SchwartzBruhat G) (b : SchwartzBruhat H) (f : SchwartzBruhat (G × H)),
        (∀ x y, f (x, y) = a x * b y) → P z f = D z a * E z b := by
  have hA : PolynormableSpace ℂ (StrongDual ℂ (SchwartzBruhat G)) := (schwartzBruhat_strongDual_nuclear.{0,_} (G := G)).2.1
  have hB : PolynormableSpace ℂ (StrongDual ℂ (SchwartzBruhat H)) := (schwartzBruhat_strongDual_nuclear.{0,_} (G := H)).2.1
  refine (schwartzBruhat_kernel_equiv (G := G) (H := H)).elim fun k hk ↦ ?_
  refine (schwartzBruhat_strongDual_kernel_equiv k hk).elim fun e he ↦ ?_
  have hol := holomorphic_projectiveTensor e D E hD hE
  refine ⟨_, hol, fun z a b f hf ↦ ?_⟩
  let q := k (UniformSpace.Completion.coe' (α := InductiveTensor (SchwartzBruhat G) (SchwartzBruhat H)) (a ⊗ₜ[ℂ] b))
  have eq : f = q := Subtype.ext (funext fun x ↦ (hf x.1 x.2).trans (hk a b x.1 x.2).symm)
  rw [eq]
  with_reducible exact he (D z) (E z) a b

private theorem strongDual_ext_inductiveTensor {A B : Type*}
    [AddCommGroup A] [Module ℂ A] [TopologicalSpace A]
    [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] {Z : Type*} [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z]
    (e : UniformSpace.Completion (InductiveTensor A B) ≃L[ℂ] Z)
    (P Q : StrongDual ℂ Z)
    (h : ∀ (a : A) (b : B), P (e (UniformSpace.Completion.coe' (α := InductiveTensor A B) (a ⊗ₜ[ℂ] b))) =
      Q (e (UniformSpace.Completion.coe' (α := InductiveTensor A B) (a ⊗ₜ[ℂ] b)))) : P = Q := by
  let U := InductiveTensor A B
  let j : U →L[ℂ] UniformSpace.Completion U := UniformSpace.Completion.toComplL
  let f : A ⊗[ℂ] B →ₗ[ℂ] Z := e.toLinearEquiv.toLinearMap.comp j.toLinearMap
  have heq : P.toLinearMap.comp f = Q.toLinearMap.comp f := TensorProduct.ext' h
  have eq (z : UniformSpace.Completion U) : P (e z) = Q (e z) :=
    UniformSpace.Completion.ext' (P.continuous.comp e.continuous) (Q.continuous.comp e.continuous)
      (fun w ↦ LinearMap.congr_fun heq w) z
  exact ContinuousLinearMap.ext (e.surjective.forall.mpr eq)

private theorem schwartzBruhat_dual_ext_products {G H : Type*}
    [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] [LocallyCompactSpace H] [SecondCountableTopology H]
    (P Q : StrongDual ℂ (SchwartzBruhat (G × H)))
    (h : ∀ (a : SchwartzBruhat G) (b : SchwartzBruhat H) (f : SchwartzBruhat (G × H)),
        (∀ x y, f (x,y) = a x * b y) → P f = Q f) : P = Q := by
  refine (schwartzBruhat_kernel_equiv (G := G) (H := H)).elim fun e he ↦ ?_
  with_reducible apply strongDual_ext_inductiveTensor e P Q
  intro a b
  with_reducible exact h a b _ (he a b)

private theorem inductiveTensor_fix_left {A B : Type*}
    [AddCommGroup A] [Module ℂ A] [TopologicalSpace A] [PolynormableSpace ℂ A] [T2Space A]
    [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] [PolynormableSpace ℂ B] [T2Space B]
    {Z : Type*} [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z]
    (e : UniformSpace.Completion (InductiveTensor A B) ≃L[ℂ] Z) (a : A) :
    ∃ j : B →L[ℂ] Z, ∀ b, j b = e (UniformSpace.Completion.coe' (α := InductiveTensor A B) (a ⊗ₜ[ℂ] b)) := by
  let U := InductiveTensor A B
  let t : B →L[ℂ] U := ⟨TensorProduct.mk ℂ A B a,
    ((continuous_inductiveTensor_iff (LinearMap.id : U →ₗ[ℂ] U)).mp continuous_id).1 a⟩
  let c : U →L[ℂ] UniformSpace.Completion U := UniformSpace.Completion.toComplL
  exact ⟨e.toContinuousLinearMap.comp (c.comp t), fun _ ↦ rfl⟩

private theorem exists_schwartzBruhat_product_right {G H : Type*}
    [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] [LocallyCompactSpace H] [SecondCountableTopology H]
    (a : SchwartzBruhat G) : ∃ j : SchwartzBruhat H →L[ℂ] SchwartzBruhat (G × H),
      ∀ (b : SchwartzBruhat H) x y, j b (x,y) = a x * b y := by
  have : T2Space (SchwartzBruhat G) := schwartzBruhat_t2
  have : T2Space (SchwartzBruhat H) := schwartzBruhat_t2
  let U := InductiveTensor (SchwartzBruhat G) (SchwartzBruhat H)
  refine (schwartzBruhat_kernel_equiv (G := G) (H := H)).elim fun e he ↦ ?_
  with_reducible refine (inductiveTensor_fix_left e a).elim fun j hj ↦ ?_
  with_reducible exact ⟨j, fun b x y ↦ (congrArg (fun f : SchwartzBruhat (G × H) ↦ f (x,y)) (hj b)).trans (he a b x y)⟩

private def HasProductDual {ι : Type*} [Fintype ι] (G : ι → Type*)
    [∀ i, CommGroup (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)]
    [∀ i, T2Space (G i)] [∀ i, LocallyCompactSpace (G i)] [∀ i, SecondCountableTopology (G i)]
    (D : ∀ i, ℂ → StrongDual ℂ (SchwartzBruhat (G i))) : Prop :=
    ∃ P : ℂ → StrongDual ℂ (SchwartzBruhat ((i : ι) → G i)), VectorHolomorphicOn P univ ∧
      ∀ (z : ℂ) (a : ∀ i, SchwartzBruhat (G i)) (f : SchwartzBruhat ((i : ι) → G i)),
        (∀ x, f x = ∏ i, a i (x i)) → P z f = ∏ i, D i z (a i)

private theorem prod_at_index {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) (f : ι → ℂ) :
    ∏ j, f j = f i * ∏ j : {j // j ≠ i}, f j.val := by
  rw [Fintype.prod_eq_mul_prod_compl i]
  exact congrArg (_ * ·) (Finset.prod_subtype _ (fun _ ↦ by simp) f)

private theorem vectorHolomorphicOn_const' {T : Type*} [AddCommGroup T] [Module ℂ T]
    [TopologicalSpace T] [IsTopologicalAddGroup T] [ContinuousSMul ℂ T] (k : T) :
    VectorHolomorphicOn (fun _ : ℂ ↦ k) univ := by
  apply (vectorHolomorphicOn_iff_tendsto isOpen_univ _).mpr
  intro z _
  exact ⟨0, by simpa only [sub_self, smul_zero] using (tendsto_const_nhds (x := (0 : T)) : Tendsto (fun _ : ℂ ↦ (0 : T)) (𝓝[≠] z) (𝓝 0))⟩

private theorem productDual_empty {ι : Type*} [Fintype ι] (G : ι → Type*)
    [∀ i, CommGroup (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)]
    [∀ i, T2Space (G i)] [∀ i, LocallyCompactSpace (G i)] [∀ i, SecondCountableTopology (G i)]
    (D : ∀ i, ℂ → StrongDual ℂ (SchwartzBruhat (G i))) [IsEmpty ι] : HasProductDual G D := by
  unfold HasProductDual
  let ev : SchwartzBruhat ((i : ι) → G i) →ₗ[ℂ] ℂ := (LinearMap.proj 1).comp (schwartzBruhatSubmodule _).subtype
  let L : StrongDual ℂ (SchwartzBruhat ((i : ι) → G i)) := ⟨ev, continuous_schwartzBruhat_eval' 1⟩
  refine ⟨fun _ ↦ L, vectorHolomorphicOn_const' L, fun z a f hf ↦ ?_⟩
  change f 1 = ∏ j, D j z (a j)
  exact (hf 1).trans (by simp)

private theorem productDual_step {ι : Type*} [Fintype ι] (G : ι → Type*)
    [∀ i, CommGroup (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)]
    [∀ i, T2Space (G i)] [∀ i, LocallyCompactSpace (G i)] [∀ i, SecondCountableTopology (G i)]
    (D : ∀ i, ℂ → StrongDual ℂ (SchwartzBruhat (G i))) (hD : ∀ i, VectorHolomorphicOn (D i) univ) [DecidableEq ι] (i : ι)
    (ih : HasProductDual (ι := {j : ι // j ≠ i}) (fun j ↦ G j.val) (fun j ↦ D j.val)) : HasProductDual G D := by
  unfold HasProductDual
  classical
  let J := {j : ι // j ≠ i}
  refine ih.elim fun P hPev ↦ ?_
  have hP := hPev.1
  have hev := hPev.2
  let e : ((j : ι) → G j) ≃ₜ* (G i × ((j : J) → G j.val)) :=
    { Homeomorph.piSplitAt i G with map_mul' := fun _ _ ↦ rfl }
  with_reducible refine (schwartzBruhat_dual_tensor_family (D i) P (hD i) hP).elim fun P₂ h₂ ↦ ?_
  refine (exists_schwartzBruhat_comp_equivCLM e.symm).elim fun u hu ↦ ?_
  let L : StrongDual ℂ (SchwartzBruhat (G i × ((j : J) → G j.val))) →L[ℂ] StrongDual ℂ (SchwartzBruhat ((j : ι) → G j)) := by with_reducible exact u.precomp ℂ
  with_reducible refine ⟨fun z ↦ L (P₂ z), vectorHolomorphicOn_postcomp L h₂.1, fun z a f hf ↦ ?_⟩
  with_reducible refine (schwartzBruhat_pi_test (ι := J) (fun j ↦ G j.val) (fun j ↦ a j.val)).elim fun b hb ↦ ?_
  have hp (x : G i) (y : (j : J) → G j.val) : u f (x,y) = a i x * b y := by
    have hx : e (e.symm (x,y)) = (x,y) := e.apply_symm_apply _
    have hx₁ : e.symm (x,y) i = x := congrArg Prod.fst hx
    have hx₂ (j : J) : e.symm (x,y) j.val = y j := congrFun (congrArg Prod.snd hx) j
    refine (hu f (x,y)).trans ((hf (e.symm (x,y))).trans ?_)
    rw [prod_at_index i, hx₁, hb]
    exact congrArg (_ * ·) (Finset.prod_congr rfl fun j _ ↦ congrArg (a j.val) (hx₂ j))
  have h₁ := h₂.2 z (a i) b (u f) hp
  have hrest := hev z (fun j ↦ a j.val) b hb
  exact h₁.trans ((congrArg (D i z (a i) * ·) hrest).trans (prod_at_index i (fun j ↦ D j z (a j))).symm)

private def DetectPureProducts {ι : Type*} [Fintype ι] (G : ι → Type*)
    [∀ i, CommGroup (G i)] [∀ i, TopologicalSpace (G i)] : Prop :=
  ∀ P Q : StrongDual ℂ (SchwartzBruhat ((i : ι) → G i)),
    (∀ (a : ∀ i, SchwartzBruhat (G i)) (f : SchwartzBruhat ((i : ι) → G i)),
      (∀ x, f x = ∏ i, a i (x i)) → P f = Q f) → P = Q

private theorem detectPureProducts_empty {ι : Type*} [Fintype ι] [IsEmpty ι] (G : ι → Type*)
    [∀ i, CommGroup (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)] [∀ i, T2Space (G i)]
    [∀ i, LocallyCompactSpace (G i)] [∀ i, SecondCountableTopology (G i)] : DetectPureProducts G := by
  intro P Q h
  let : CompactSpace ((i : ι) → G i) := Finite.compactSpace
  refine (compact_schwartzBruhat_one (H := (i : ι) → G i)).elim fun oneTest ho ↦ ?_
  have eq := h (fun i ↦ isEmptyElim i) oneTest (fun x ↦ (ho x).trans (by simp))
  apply ContinuousLinearMap.ext
  intro f
  have he : f = f 1 • oneTest := Subtype.ext (funext fun x ↦ (congrArg (fun t ↦ f t) (Subsingleton.elim x 1)).trans
    ((mul_one (f 1)).symm.trans (congrArg (f 1 * ·) (ho x).symm)))
  exact (congrArg P he).trans ((P.map_smul (f 1) oneTest).trans ((congrArg (f 1 * ·) eq).trans
    ((Q.map_smul (f 1) oneTest).symm.trans (congrArg Q he.symm))))

private theorem detectPureProducts_step {ι : Type*} [Fintype ι] [DecidableEq ι] (G : ι → Type*)
    [∀ i, CommGroup (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)] [∀ i, T2Space (G i)]
    [∀ i, LocallyCompactSpace (G i)] [∀ i, SecondCountableTopology (G i)] (i : ι)
    (ih : DetectPureProducts (ι := {j : ι // j ≠ i}) (fun j ↦ G j.val)) : DetectPureProducts G := by
  intro P Q hall
  let J := {j : ι // j ≠ i}
  let e : ((j : ι) → G j) ≃ₜ* (G i × ((j : J) → G j.val)) :=
    { Homeomorph.piSplitAt i G with map_mul' := fun _ _ ↦ rfl }
  with_reducible refine (schwartzBruhat_congr e).elim fun k hk ↦ ?_
  let A := SchwartzBruhat (G i × ((j : J) → G j.val))
  let U := P.comp k.symm.toContinuousLinearMap
  let W := Q.comp k.symm.toContinuousLinearMap
  have hp (f : A) (x : (j : ι) → G j) : k.symm f x = f (e x) :=
    (hk (k.symm f) x).symm.trans (congrArg (fun q : A ↦ q (e x)) (k.apply_symm_apply f))
  have hUW : U = W := by
    with_reducible apply schwartzBruhat_dual_ext_products U W
    intro a b f hf
    with_reducible refine (exists_schwartzBruhat_product_right (H := (j : J) → G j.val) a).elim fun ins hh ↦ ?_
    have heq : U.comp ins = W.comp ins := by
      apply ih
      intro c g hg
      let t := Equiv.piSplitAt i (fun j ↦ SchwartzBruhat (G j))
      let d := t.symm (a,c)
      have hed : t d = (a,c) := t.apply_symm_apply _
      have hd₁ : d i = a := congrArg Prod.fst hed
      have hd₂ (j : J) (x : G j.val) : d j.val x = c j x :=
        congrArg (fun k : SchwartzBruhat (G j.val) ↦ k x) (congrFun (congrArg Prod.snd hed) j)
      have hlocal (x : (j : ι) → G j) : k.symm (ins g) x = ∏ j, d j (x j) := by
        rw [hp, hh, hg, prod_at_index i]
        exact congrArg₂ (· * ·) (congrArg (fun k : SchwartzBruhat (G i) ↦ k (x i)) hd₁).symm (Finset.prod_congr rfl fun j _ ↦ (hd₂ j (x j.val)).symm)
      exact hall d _ hlocal
    have hfg : f = ins b := Subtype.ext (funext fun x ↦ (hf x.1 x.2).trans (hh b x.1 x.2).symm)
    exact (congrArg U hfg).trans ((DFunLike.congr_fun heq b).trans (congrArg W hfg.symm))
  exact ContinuousLinearMap.ext fun f ↦ (congrArg P (k.symm_apply_apply f).symm).trans
    ((DFunLike.congr_fun hUW (k f)).trans (congrArg Q (k.symm_apply_apply f)))

private theorem schwartzBruhat_pi_families {ι : Type*} [Fintype ι] (G : ι → Type*)
    [∀ i, CommGroup (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)]
    [∀ i, T2Space (G i)] [∀ i, LocallyCompactSpace (G i)] [∀ i, SecondCountableTopology (G i)]
    (D : ∀ i, ℂ → StrongDual ℂ (SchwartzBruhat (G i))) (hD : ∀ i, VectorHolomorphicOn (D i) univ) :
    HasProductDual G D ∧ DetectPureProducts G := by
  classical
  rcases isEmpty_or_nonempty ι with hempty | hn
  · exact ⟨productDual_empty G D, detectPureProducts_empty G⟩
  · obtain ⟨i⟩ := hn
    let J := {j : ι // j ≠ i}
    have ih := schwartzBruhat_pi_families (ι := J) (fun j ↦ G j.val) (fun j ↦ D j.val) (fun j ↦ hD j.val)
    exact ⟨productDual_step G D hD i ih.1, detectPureProducts_step G i ih.2⟩
termination_by Fintype.card ι
decreasing_by
  classical
  exact Fintype.card_subtype_lt (x := i) (not_not_intro rfl)

private abbrev stageCoordinateGroup (S : Finset V) : InfinitePlace F ⊕ S → Type _ :=
  Sum.elim (fun w : InfinitePlace F ↦ Multiplicative w.Completion) (fun v : S ↦ Multiplicative (v.val.adicCompletion F))

private local instance coordCommGroup (S : Finset V) (i : InfinitePlace F ⊕ S) : CommGroup (stageCoordinateGroup S i) := by
  cases i with
  | inl w => exact (inferInstance : CommGroup (Multiplicative w.Completion))
  | inr v => exact (inferInstance : CommGroup (Multiplicative (v.val.adicCompletion F)))
private local instance coordTopology (S : Finset V) (i : InfinitePlace F ⊕ S) : TopologicalSpace (stageCoordinateGroup S i) := by
  cases i with
  | inl w => exact (inferInstance : TopologicalSpace (Multiplicative w.Completion))
  | inr v => exact (inferInstance : TopologicalSpace (Multiplicative (v.val.adicCompletion F)))
private local instance coordTopGroup (S : Finset V) (i : InfinitePlace F ⊕ S) : IsTopologicalGroup (stageCoordinateGroup S i) := by
  cases i with
  | inl w => exact (inferInstance : IsTopologicalGroup (Multiplicative w.Completion))
  | inr v => exact (inferInstance : IsTopologicalGroup (Multiplicative (v.val.adicCompletion F)))
private local instance coordT2 (S : Finset V) (i : InfinitePlace F ⊕ S) : T2Space (stageCoordinateGroup S i) := by
  cases i with
  | inl w => exact (inferInstance : T2Space w.Completion)
  | inr v => exact (inferInstance : T2Space (v.val.adicCompletion F))
private local instance coordLCH (S : Finset V) (i : InfinitePlace F ⊕ S) : LocallyCompactSpace (stageCoordinateGroup S i) := by
  cases i with
  | inl w => exact (inferInstance : LocallyCompactSpace w.Completion)
  | inr v =>
    let : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
    exact (inferInstance : LocallyCompactSpace (v.val.adicCompletion F))
private local instance coordSC (S : Finset V) (i : InfinitePlace F ⊕ S) : SecondCountableTopology (stageCoordinateGroup S i) := by
  cases i with
  | inl w => exact (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  | inr v =>
    let : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
    exact (inferInstance : SecondCountableTopology (v.val.adicCompletion F))

private def sAdeleToProduct (S : Finset V) : Multiplicative (SAdeleRing F S) ≃ₜ*
    ((i : InfinitePlace F ⊕ S) → stageCoordinateGroup S i) where
  toFun x := fun i ↦ match i with
    | .inl w => Multiplicative.ofAdd (x.toAdd.1 w)
    | .inr v => Multiplicative.ofAdd (x.toAdd.2 v)
  invFun y := Multiplicative.ofAdd ((fun w ↦ (y (.inl w)).toAdd), (fun v ↦ (y (.inr v)).toAdd))
  left_inv _ := rfl
  right_inv y := funext fun i ↦ by cases i <;> rfl
  map_mul' _ _ := funext fun i ↦ by cases i <;> rfl
  continuous_toFun := continuous_pi fun i ↦ by
    cases i with
    | inl w => exact (continuous_apply w).comp continuous_fst
    | inr v => exact (continuous_apply v).comp continuous_snd
  continuous_invFun := (continuous_pi fun w ↦ continuous_apply (Sum.inl w)).prodMk
    (continuous_pi fun v ↦ continuous_apply (Sum.inr v))

private def stageLocalDual (χ : PontryaginDual C_F) (S : Finset V) :
    (i : InfinitePlace F ⊕ S) → ℂ → StrongDual ℂ (SchwartzBruhat (stageCoordinateGroup S i))
  | .inl w => DA(χ,w)
  | .inr v => DB(χ,v.val)

private theorem stageLocalDual_hol (χ : PontryaginDual C_F) (S : Finset V) (i : InfinitePlace F ⊕ S) :
    VectorHolomorphicOn (stageLocalDual χ S i) univ := by
  cases i with
  | inl w => exact (infiniteEigendistribution_normalized w χ∞(χ,w)).choose_spec.1
  | inr v => exact (finiteEigendistribution_normalized v.val χv(χ,v.val)).choose_spec.1

private def stagePure (S : Finset V) (a : ∀ i, SchwartzBruhat (stageCoordinateGroup S i))
    (f : ℬ(SAdeleRing F S)) : Prop :=
  ∀ x : Multiplicative (SAdeleRing F S), f x = ∏ i, a i (sAdeleToProduct S x i)

private theorem stageProducts (χ : PontryaginDual C_F) (S : Finset V) :
    (∃ P : ℂ → StrongDual ℂ ℬ(SAdeleRing F S), VectorHolomorphicOn P univ ∧
      ∀ z a f, stagePure S a f → P z f = ∏ i, stageLocalDual χ S i z (a i)) ∧
    (∀ U W : StrongDual ℂ ℬ(SAdeleRing F S), (∀ a f, stagePure S a f → U f = W f) → U = W) := by
  let G := stageCoordinateGroup S
  let e := sAdeleToProduct S
  let : LocallyCompactSpace (Multiplicative (SAdeleRing F S)) := e.toHomeomorph.isOpenEmbedding.locallyCompactSpace
  let : T2Space (Multiplicative (SAdeleRing F S)) := e.toHomeomorph.isEmbedding.t2Space
  with_reducible refine (schwartzBruhat_congr e).elim fun k hk ↦ ?_
  have hall := schwartzBruhat_pi_families G (stageLocalDual χ S) (stageLocalDual_hol χ S)
  refine hall.1.elim fun P h ↦ ?_
  let L : StrongDual ℂ (SchwartzBruhat ((i : InfinitePlace F ⊕ S) → G i)) →L[ℂ] StrongDual ℂ ℬ(SAdeleRing F S) := by
    with_reducible exact k.toContinuousLinearMap.precomp ℂ
  constructor
  · refine ⟨fun z ↦ L (P z), vectorHolomorphicOn_postcomp L h.1, fun z a f hf ↦ ?_⟩
    change P z (k f) = _
    apply h.2 z a (k f)
    exact e.surjective.forall.mpr fun x ↦ (hk f x).trans (hf x)
  · intro U W he
    let U' := U.comp k.symm.toContinuousLinearMap
    let W' := W.comp k.symm.toContinuousLinearMap
    have eq : U' = W' := by
      apply hall.2
      intro a f hf
      apply he a (k.symm f)
      intro x
      exact (hk (k.symm f) x).symm.trans ((congrArg (fun q ↦ q (e x)) (show (k (k.symm f) : ((i : InfinitePlace F ⊕ S) → G i) → ℂ) = f from congrArg Subtype.val (k.apply_symm_apply f))).trans (hf (e x)))
    exact ContinuousLinearMap.ext fun f ↦ (congrArg U (k.symm_apply_apply f).symm).trans
      ((DFunLike.congr_fun eq (k f)).trans (congrArg W (k.symm_apply_apply f)))

private theorem normalizedGaussian_ne_zero (χ : PontryaginDual C_F) (z : ℂ) (hz : 1 < z.re) :
    gaussianCompletedHeckeL χ z ≠ 0 := by
  rw [gaussianCompletedHeckeL_eq_completedHeckeL χ z hz]
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (inv_ne_zero (Real.sqrt_ne_zero'.mpr
    (abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero F))))) (mul_ne_zero
    (heckeGammaFactor_ne_zero_of_re_pos χ (zero_lt_one.trans hz)) (finiteHeckeL_ne_zero_of_one_lt_re χ ⟨z,hz⟩))

private def globalIntegralQuotient (χ : PontryaginDual C_F) (z : ℂ) : StrongDual ℂ ℬ(𝔸[F]) :=
  if hz : 1 < z.re then (gaussianCompletedHeckeL χ z)⁻¹ • globalIntegralDual χ z hz else 0

private theorem globalIntegralQuotient_apply (χ : PontryaginDual C_F) (z : ℂ) (hz : 1 < z.re) (f : ℬ(𝔸[F])) :
    globalIntegralQuotient χ z f = (gaussianCompletedHeckeL χ z)⁻¹ * globalIdelicZetaIntegral f (ideleClassNormTwist χ z) :=
  congrArg (fun T : StrongDual ℂ ℬ(𝔸[F]) ↦ T f) (dite_eq_left hz)

private theorem stageGerm (χ : PontryaginDual C_F) (S : Finset V)
    (hout : ∀ z : ℂ, ideleClassNormTwist χ z ∈ unramifiedOutside F S)
    (gS : ℬ(SAdeleRing F S)) (hG : sAdeleSchwartzToGlobal F S gS = adelicStandardGaussian χ) :
    ∃ D : ℂ → StrongDual ℂ ℬ(SAdeleRing F S), (∀ f, AnalyticOnNhd ℂ (fun z ↦ D z f) univ) ∧
      ∀ f, (fun z ↦ D z f) =ᶠ[𝓝[≠] (2 : ℂ)] (fun z ↦ globalIntegralQuotient χ z (sAdeleSchwartzToGlobal F S f)) := by
  have hS := stageProducts χ S
  refine hS.1.elim fun P hh ↦ ?_
  refine ⟨P, fun f ↦ analytic_eval_normalized hh.1 f, fun f ↦ ?_⟩
  have hnear : ∀ᶠ z : ℂ in 𝓝[≠] 2, 1 < z.re := (Complex.continuous_re.continuousAt.eventually
    (lt_mem_nhds (by norm_num : 1 < (2 : ℂ).re))).filter_mono nhdsWithin_le_nhds
  refine (hnear.and (all_infiniteIntegral_normalized_ratio χ)).mono fun z h ↦ ?_
  let Vₛ : ℬ(SAdeleRing F S) →L[ℂ] ℬ(𝔸[F]) := ⟨sAdeleSchwartzToGlobal F S, (sAdeleSchwartzToGlobal_isEmbedding F S).continuous⟩
  let Q := (globalIntegralQuotient χ z).comp Vₛ
  have hzero (v : V) (hv : v ∉ S) : b₀(χ,v) (Multiplicative.ofAdd 0) = 1 := by
    have hu := (unramifiedAt_iff_restriction _ v).mp (hout 0 v hv)
    exact (ite_eq_left hu).trans (indicator_of_mem (v.adicCompletionIntegers F).zero_mem _)
  have hGauss := sAdeleSchwartz_pureTensor_of_global S gS (fun w ↦ a₀(χ,w)) (fun v ↦ b₀(χ,v)) hzero
    (fun x ↦ by rw [hG]; rfl)
  have eq : P z = Q := by
    apply hS.2
    intro a k hk
    let b (v : V) : ℬ(v.adicCompletion F) := if hv : v ∈ S then a (.inr ⟨v,hv⟩) else b₀(χ,v)
    have hb (v : S) : b v.val = a (.inr v) := dite_eq_left v.property
    have hf (x : SAdeleRing F S) : k (Multiplicative.ofAdd x) =
        (∏ w, a (.inl w) (Multiplicative.ofAdd (x.1 w))) * ∏ v : S, b v.val (Multiplicative.ofAdd (x.2 v)) := by
      refine (hk (Multiplicative.ofAdd x)).trans ((Fintype.prod_sum_type _).trans ?_)
      exact congrArg (_ * ·) (Finset.prod_congr rfl fun v _ ↦ (congrArg (fun u : ℬ(v.val.adicCompletion F) ↦ u (Multiplicative.ofAdd (x.2 v))) (hb v)).symm)
    have hprod := globalIntegral_tensor_ratio χ z h.1 S (hout z) k gS (fun w ↦ a (.inl w)) b hf hGauss
      (fun w ↦ h.2 w (a (.inl w)))
    let A := ∏ i, stageLocalDual χ S i z (a i)
    have hs : A = (∏ w, DA(χ,w) z (a (.inl w))) * ∏ v : S, DB(χ,v.val) z (b v.val) :=
      (Fintype.prod_sum_type _).trans (congrArg (_ * ·) (Finset.prod_congr rfl fun v _ ↦ congrArg
        (DB(χ,v.val) z) (hb v).symm))
    have hGz : globalIdelicZetaIntegral (sAdeleSchwartzToGlobal F S gS) (ideleClassNormTwist χ z) =
        gaussianCompletedHeckeL χ z := (congrArg (fun f ↦ globalIdelicZetaIntegral f (ideleClassNormTwist χ z)) hG).trans
          (gaussianCompletedHeckeL_eq_integral χ z h.1).symm
    have hmul := hprod.trans (congrArg₂ (· * ·) hGz hs.symm)
    exact (hh.2 z a k hk).trans (((inv_mul_cancel_left₀ (normalizedGaussian_ne_zero χ z h.1) A).symm.trans
      (congrArg ((gaussianCompletedHeckeL χ z)⁻¹ * ·) hmul.symm)).trans (globalIntegralQuotient_apply χ z h.1 _).symm)
  exact DFunLike.congr_fun eq f

private theorem strongDual_of_stage_germs {κ E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    {P : κ → Type*} [∀ i, AddCommGroup (P i)] [∀ i, Module ℂ (P i)] [∀ i, TopologicalSpace (P i)]
    (j : ∀ i, P i →ₗ[ℂ] E) (cover : ∀ f : E, ∃ i, f ∈ LinearMap.range (j i))
    (finalTopology : ∀ L : E →ₗ[ℂ] ℂ, (∀ i, Continuous (L ∘ j i)) → Continuous L)
    (Z : ℂ → E →ₗ[ℂ] ℂ) (D : ∀ i, ℂ → StrongDual ℂ (P i))
    (hol : ∀ i f, AnalyticOnNhd ℂ (fun z ↦ D i z f) univ)
    (germ : ∀ i f, (fun z ↦ D i z f) =ᶠ[𝓝[≠] (2 : ℂ)] (fun z ↦ Z z (j i f))) :
    ∃ T : ℂ → StrongDual ℂ E, (∀ f, AnalyticOnNhd ℂ (fun z ↦ T z f) univ) ∧
      (∀ z i f, T z (j i f) = D i z f) ∧
      ∀ f, (fun z ↦ T z f) =ᶠ[𝓝[≠] (2 : ℂ)] (fun z ↦ Z z f) := by
  classical
  have chooseRep (f : E) : ∃ i, ∃ x : P i, j i x = f := cover f
  choose i x hx using chooseRep
  let ev (f : E) (z : ℂ) := D (i f) z (x f)
  have hg (f : E) : ev f =ᶠ[𝓝[≠] (2 : ℂ)] (fun z ↦ Z z f) :=
    (germ (i f) (x f)).mono fun z he ↦ he.trans (congrArg (Z z) (hx f))
  have eqOfGerm {a b : ℂ → ℂ} (ha : AnalyticOnNhd ℂ a univ) (hb : AnalyticOnNhd ℂ b univ)
      (h : a =ᶠ[𝓝[≠] (2 : ℂ)] b) (z : ℂ) : a z = b z :=
    ha.eqOn_of_preconnected_of_frequently_eq hb isPreconnected_univ (mem_univ 2) h.frequently (mem_univ z)
  have hev (f : E) : AnalyticOnNhd ℂ (ev f) univ := hol _ _
  have stage (z : ℂ) (k : κ) (y : P k) : ev (j k y) z = D k z y :=
    eqOfGerm (hev _) (hol k y) ((hg _).trans (germ k y).symm) z
  let lin (z : ℂ) : E →ₗ[ℂ] ℂ :=
    { toFun := fun f ↦ ev f z
      map_add' := fun f k ↦ eqOfGerm (hev (f+k)) ((hev f).add (hev k))
        (((hg (f+k)).trans (.of_forall fun w ↦ (Z w).map_add f k)).trans ((hg f).add (hg k)).symm) z
      map_smul' := fun a f ↦ eqOfGerm (hev (a • f)) (analyticOnNhd_const.mul (hev f))
        (((hg (a • f)).trans (.of_forall fun w ↦ (Z w).map_smul a f)).trans ((hg f).fun_comp (a * ·)).symm) z }
  let T (z : ℂ) : StrongDual ℂ E := ⟨lin z, finalTopology (lin z) fun k ↦
    (D k z).continuous.congr fun f ↦ (stage z k f).symm⟩
  exact ⟨T, hev, stage, hg⟩

private theorem globalFamily_germ (χ : PontryaginDual C_F) :
    ∃ D : ℂ → StrongDual ℂ ℬ(𝔸[F]), (∀ f, AnalyticOnNhd ℂ (fun z ↦ D z f) univ) ∧
      ∀ f, (fun z ↦ D z f) =ᶠ[𝓝[≠] (2 : ℂ)] (fun z ↦ globalIntegralQuotient χ z f) := by
  classical
  have covered := exists_normalized_stage χ 0 (adelicStandardGaussian χ) (fun v ↦ b₀(χ,v)) (.of_forall fun _ ↦ rfl)
  refine covered.elim fun R hR ↦ ?_
  refine hR.2.2.elim fun _ h ↦ h.elim fun g hg ↦ ?_
  have stage (S : Finset V) : ∃ P : ℂ → StrongDual ℂ ℬ(SAdeleRing F S),
      (∀ f, AnalyticOnNhd ℂ (fun z ↦ P z f) univ) ∧ ∀ f,
      (fun z ↦ P z f) =ᶠ[𝓝[≠] (2 : ℂ)] (fun z ↦ globalIntegralQuotient χ z (sAdeleSchwartzToGlobal F S f)) := by
    let U := R ∪ S
    have hRU : R ⊆ U := Finset.subset_union_left
    have hSU : S ⊆ U := Finset.subset_union_right
    let inc : ℬ(SAdeleRing F S) →L[ℂ] ℬ(SAdeleRing F U) :=
      ⟨sAdeleSchwartzTransition F hSU, (sAdeleSchwartzTransition_isEmbedding F hSU).continuous⟩
    have hU (z : ℂ) : ideleClassNormTwist χ z ∈ unramifiedOutside F U := fun v hv ↦ hR.1 z v (fun hh ↦ hv (hRU hh))
    have hin := (LinearMap.congr_fun (sAdeleSchwartzToGlobal_comp F hRU) g).trans hg.2
    refine (stageGerm χ U hU _ hin).elim fun D hh ↦ ?_
    refine ⟨fun z ↦ (D z).comp inc, fun f ↦ hh.1 (inc f), fun f ↦ ?_⟩
    exact (hh.2 (inc f)).mono fun z he ↦ he.trans (congrArg (globalIntegralQuotient χ z) (LinearMap.congr_fun (sAdeleSchwartzToGlobal_comp F hSU) f))
  choose P hP using stage
  have cts (L : ℬ(𝔸[F]) →ₗ[ℂ] ℂ) (hc : ∀ S, Continuous (L ∘ sAdeleSchwartzToGlobal F S)) : Continuous L := by
    exact (congrArg (fun t ↦ @Continuous ℬ(𝔸[F]) ℂ t _ L) (sAdeleSchwartzToGlobal_finalTopology F)).mpr
      (continuous_of_locallyConvexFinalTopology (sAdeleSchwartzToGlobal F) L hc)
  refine (strongDual_of_stage_germs (sAdeleSchwartzToGlobal F) (sAdeleSchwartzToGlobal_exhaustive F) cts
    (fun z ↦ (globalIntegralQuotient χ z).toLinearMap) P (fun i ↦ (hP i).1) (fun i ↦ (hP i).2)).elim fun T h ↦ ?_
  exact ⟨T,h.1,h.2.2⟩


private theorem globalTwist_eval_analytic (χ : PontryaginDual C_F) (g : I_F) :
    AnalyticOnNhd ℂ (fun z ↦ ideleClassNormTwist χ z (classOf g)) univ := by
  let n := ((ideleClassNorm F (classOf g) : ℝ≥0) : ℝ)
  have hn : (n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (ideleClassNorm F (classOf g)).ne_zero)
  change AnalyticOnNhd ℂ (fun z : ℂ ↦ (χ (classOf g) : ℂ) * (n : ℂ) ^ z) univ
  apply DifferentiableOn.analyticOnNhd _ isOpen_univ
  fun_prop (disch := simp [hn])

private theorem eventually_one_lt_re_at_two : ∀ᶠ z : ℂ in 𝓝[≠] 2, 1 < z.re := (Complex.continuous_re.continuousAt.eventually
    (lt_mem_nhds (by norm_num : 1 < (2 : ℂ).re))).filter_mono nhdsWithin_le_nhds

private theorem globalFamily_normalized (χ : PontryaginDual C_F)
    (D : ℂ → StrongDual ℂ ℬ(𝔸[F])) (hD : ∀ f, AnalyticOnNhd ℂ (fun z ↦ D z f) univ)
    (hQ : ∀ f, (fun z ↦ D z f) =ᶠ[𝓝[≠] (2 : ℂ)] (fun z ↦ globalIntegralQuotient χ z f)) :
    ∀ s, D s (adelicStandardGaussian χ) = 1 := by
  intro s
  apply (hD (adelicStandardGaussian χ)).eqOn_of_preconnected_of_frequently_eq analyticOnNhd_const
    isPreconnected_univ (mem_univ 2) _ (mem_univ s)
  apply Filter.Eventually.frequently
  filter_upwards [eventually_one_lt_re_at_two, hQ (adelicStandardGaussian χ)] with z hz he
  exact he.trans ((globalIntegralQuotient_apply χ z hz _).trans
    ((congrArg ((gaussianCompletedHeckeL χ z)⁻¹ * ·) (gaussianCompletedHeckeL_eq_integral χ z hz).symm).trans
    (inv_mul_cancel₀ (normalizedGaussian_ne_zero χ z hz))))

private theorem globalFamily_matches_zeta (χ : PontryaginDual C_F)
    (D : ℂ → StrongDual ℂ ℬ(𝔸[F])) (hD : ∀ f, AnalyticOnNhd ℂ (fun z ↦ D z f) univ)
    (hQ : ∀ f, (fun z ↦ D z f) =ᶠ[𝓝[≠] (2 : ℂ)] (fun z ↦ globalIntegralQuotient χ z f)) :
    ∀ s, ideleClassNormTwist χ s ≠ 1 → ideleClassNormTwist χ s ≠ ideleClassNormTwist (1 : PontryaginDual C_F) 1 →
      ∀ f, globalIdelicZFunction f (ideleClassNormTwist χ s) = gaussianCompletedHeckeL χ s * D s f := by
  intro s hs hn f
  let Z (w : ℂ) := globalIdelicZFunction f (ideleClassNormTwist χ w)
  let L := gaussianCompletedHeckeL χ
  let A (w : ℂ) := D w f
  have hz : MeromorphicNFOn Z univ := globalIdelicZFunction_meromorphic f χ
  have hl : MeromorphicNFOn L univ := globalIdelicZFunction_meromorphic _ χ
  have ha := hD f
  have hla : MeromorphicOn (L * A) univ := hl.meromorphicOn.mul (fun w hw ↦ (ha w hw).meromorphicAt)
  have heq : Z =ᶠ[𝓝[≠] (2 : ℂ)] L * A := by
    filter_upwards [eventually_one_lt_re_at_two, hQ f] with w hw h
    have hab : 1 < quasiCharacterAbscissa (ideleClassNorm F) (isProperMap_ideleClassNorm F)
        (ideleClassNorm_ne_one (F := F)) (ideleClassNormTwist χ w) := hw.trans_eq (ideleClassNormTwist_abscissa χ w).symm
    exact (globalIdelicZFunction_eq_integral f hab).trans ((mul_inv_cancel_left₀ (normalizedGaussian_ne_zero χ w hw) _).symm.trans
      (congrArg (L w * ·) ((globalIntegralQuotient_apply χ w hw f).symm.trans h.symm)))
  have ho : meromorphicOrderAt (Z - L * A) 2 = ⊤ := meromorphicOrderAt_eq_top_iff.mpr (heq.mono fun w hw ↦ sub_eq_zero.mpr hw)
  have hs' := (hz.meromorphicOn.sub hla).meromorphicOrderAt_eq_top_of_isPreconnected
    isPreconnected_univ (mem_univ (2 : ℂ)) (mem_univ s) ho
  have hpun : Z =ᶠ[𝓝[≠] s] L * A := (meromorphicOrderAt_eq_top_iff.mp hs').mono fun w hw ↦ sub_eq_zero.mp hw
  have hreg : AnalyticAt ℂ L s := (globalIdelicZFunction_poles (adelicStandardGaussian χ) χ).1 s ⟨hs,hn⟩
  exact (((hz (mem_univ s)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
    (hreg.mul (ha s (mem_univ s))).meromorphicNFAt).mp hpun).eq_of_nhds

private theorem globalIntegralQuotient_eigen (χ : PontryaginDual C_F) (z : ℂ) (hz : 1 < z.re) :
    globalIntegralQuotient χ z ∈ adelicEigendistributions (ideleClassNormTwist χ z) :=
  (congrArg (fun T : StrongDual ℂ ℬ(𝔸[F]) ↦ T ∈ adelicEigendistributions (ideleClassNormTwist χ z))
    (show globalIntegralQuotient χ z = (gaussianCompletedHeckeL χ z)⁻¹ • globalIntegralDual χ z hz from dite_eq_left hz)).mpr
    ((adelicEigendistributions (ideleClassNormTwist χ z)).smul_mem _ (globalIntegralDual_eigen χ z hz))

private theorem globalFamily_eigen (χ : PontryaginDual C_F)
    (D : ℂ → StrongDual ℂ ℬ(𝔸[F])) (hD : ∀ f, AnalyticOnNhd ℂ (fun z ↦ D z f) univ)
    (hQ : ∀ f, (fun z ↦ D z f) =ᶠ[𝓝[≠] (2 : ℂ)] (fun z ↦ globalIntegralQuotient χ z f)) :
    ∀ s, D s ∈ adelicEigendistributions (ideleClassNormTwist χ s) := by
  intro s g f
  let d (w : ℂ) := ideleClassNormTwist χ w (classOf g)
  let A (w : ℂ) := D w (schwartzBruhatUnitTranslate g f)
  let B (w : ℂ) := d w * D w f
  have ha : AnalyticOnNhd ℂ A univ := hD _
  have hb : AnalyticOnNhd ℂ B univ := (globalTwist_eval_analytic χ g).mul (hD f)
  have eq : A =ᶠ[𝓝[≠] (2 : ℂ)] B := by
    refine (eventually_one_lt_re_at_two.and ((hQ (schwartzBruhatUnitTranslate g f)).and (hQ f))).mono fun z h ↦ ?_
    exact h.2.1.trans ((globalIntegralQuotient_eigen χ z h.1 g f).trans (congrArg (d z * ·) h.2.2.symm))
  exact ha.eqOn_of_preconnected_of_frequently_eq hb isPreconnected_univ (mem_univ 2) eq.frequently (mem_univ s)

open scoped RestrictedProduct in
private theorem adelic_dual_holomorphic (D : ℂ → StrongDual ℂ ℬ(𝔸[F]))
    (h : ∀ f, AnalyticOnNhd ℂ (fun z ↦ D z f) univ) : VectorHolomorphicOn D univ := by
  let := ratAdele_secondCountable
  let u := (exists_adeleTrace_dualCoordinates F).choose
  let : SecondCountableTopology (Multiplicative 𝔸[F]) := u.symm.toHomeomorph.isEmbedding.secondCountableTopology
  let : LocallyCompactSpace (Multiplicative 𝔸[F]) := adele_locallyCompact F
  let : T2Space (Multiplicative 𝔸[F]) := by
    change T2Space (((v : InfinitePlace F) → v.Completion) ×
      (Πʳ v : V, [v.adicCompletion F, v.adicCompletionIntegers F]))
    infer_instance
  exact sbDual_holomorphic_of_analytic_eval D h

private theorem inductiveTensor_fix_right {A B : Type*}
    [AddCommGroup A] [Module ℂ A] [TopologicalSpace A] [PolynormableSpace ℂ A] [T2Space A]
    [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] [PolynormableSpace ℂ B] [T2Space B]
    {Z : Type*} [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z]
    (e : UniformSpace.Completion (InductiveTensor A B) ≃L[ℂ] Z) (b : B) :
    ∃ j : A →L[ℂ] Z, ∀ a, j a = e (UniformSpace.Completion.coe' (α := InductiveTensor A B) (a ⊗ₜ[ℂ] b)) := by
  let U := InductiveTensor A B
  let t : A →L[ℂ] U := ⟨(TensorProduct.mk ℂ A B).flip b,
    ((continuous_inductiveTensor_iff (LinearMap.id : U →ₗ[ℂ] U)).mp continuous_id).2 b⟩
  let c : U →L[ℂ] UniformSpace.Completion U := UniformSpace.Completion.toComplL
  exact ⟨e.toContinuousLinearMap.comp (c.comp t), fun _ ↦ rfl⟩

private theorem exists_schwartzBruhat_product_left {G H : Type*}
    [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] [LocallyCompactSpace H] [SecondCountableTopology H]
    (b : SchwartzBruhat H) : ∃ j : SchwartzBruhat G →L[ℂ] SchwartzBruhat (G × H),
      ∀ (a : SchwartzBruhat G) x y, j a (x,y) = a x * b y := by
  have : T2Space (SchwartzBruhat G) := schwartzBruhat_t2
  have : T2Space (SchwartzBruhat H) := schwartzBruhat_t2
  let U := InductiveTensor (SchwartzBruhat G) (SchwartzBruhat H)
  refine (schwartzBruhat_kernel_equiv (G := G) (H := H)).elim fun e he ↦ ?_
  with_reducible refine (inductiveTensor_fix_right e b).elim fun j hj ↦ ?_
  with_reducible exact ⟨j, fun a x y ↦ (congrArg (fun f : SchwartzBruhat (G × H) ↦ f (x,y)) (hj a)).trans (he a b x y)⟩

private theorem insertLocalTest {ι : Type*} [Fintype ι] [DecidableEq ι] (G : ι → Type*)
    [∀ i, CommGroup (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)]
    [∀ i, T2Space (G i)] [∀ i, LocallyCompactSpace (G i)] [∀ i, SecondCountableTopology (G i)]
    (i : ι) (a : ∀ j, SchwartzBruhat (G j)) :
    ∃ j : SchwartzBruhat (G i) →L[ℂ] SchwartzBruhat ((i : ι) → G i),
      ∀ k x, j k x = k (x i) * ∏ l : {l : ι // l ≠ i}, a l.val (x l.val) := by
  let J := {l : ι // l ≠ i}
  let e : ((l : ι) → G l) ≃ₜ* (G i × ((l : J) → G l.val)) :=
    { Homeomorph.piSplitAt i G with map_mul' := fun _ _ ↦ rfl }
  with_reducible refine (schwartzBruhat_pi_test (ι := J) (fun j ↦ G j.val) (fun j ↦ a j.val)).elim fun b hb ↦ ?_
  with_reducible refine (exists_schwartzBruhat_product_left (G := G i) b).elim fun t ht ↦ ?_
  with_reducible refine (exists_schwartzBruhat_comp_equivCLM e).elim fun u hu ↦ ?_
  refine ⟨u.comp t, fun k x ↦ ?_⟩
  exact (hu (t k) x).trans ((ht k (x i) (fun l ↦ x l.val)).trans (congrArg (_ * ·) (hb _)))

private theorem scalar_of_coordinate_factors {ι : Type*} [Fintype ι] [DecidableEq ι] {E : ι → Type*}
    (T : (∀ i, E i) → ℂ) (D : ∀ i, E i → ℂ) (b : ∀ i, E i)
    (h : ∀ (i : ι) (a : ∀ j, E j), T a = D i (a i) * T (Function.update a i (b i)))
    (a : ∀ i, E i) : T a = (∏ i, D i (a i)) * T b := by
  let w (s : Finset ι) : ∀ j, E j := fun j ↦ if j ∈ s then a j else b j
  have eq (s : Finset ι) : T (w s) = (∏ i ∈ s, D i (a i)) * T b := by
    induction s using Finset.induction_on with
    | empty => simp [w]
    | @insert i s hi ih =>
      have he : Function.update (w (insert i s)) i (b i) = w s := by
        funext j
        by_cases hj : j = i
        · subst j; simp [w, hi]
        · simp [w, hj]
      rw [h i (w (insert i s)), he, ih, Finset.prod_insert hi, mul_assoc]
      simp [w]
  simpa [w] using eq Finset.univ

private theorem sAdeleToGlobal_translate (S : Finset V) (g : (SAdeleRing F S)ˣ) (f : ℬ(SAdeleRing F S)) :
    sAdeleSchwartzToGlobal F S (schwartzBruhatUnitTranslate g f) =
      schwartzBruhatUnitTranslate (sIdeleInsertion F S g) (sAdeleSchwartzToGlobal F S f) := by
  classical
  let u := (sIdeleInsertion F S g)⁻¹
  have he : sIdeleInsertion F S g⁻¹ = u := map_inv _ _
  have hc := sIdeleInsertion_apply F S g⁻¹
  rw [he] at hc
  apply Subtype.ext
  funext x
  let y := x.toAdd
  change sAdeleSchwartzToGlobal F S (schwartzBruhatUnitTranslate g f) (Multiplicative.ofAdd y) =
    sAdeleSchwartzToGlobal F S f (Multiplicative.ofAdd (u.val * y))
  have outside : (∀ v ∉ S, (u.val * y).2 v ∈ v.adicCompletionIntegers F) ↔
      ∀ v ∉ S, y.2 v ∈ v.adicCompletionIntegers F :=
    forall_congr' fun v ↦ forall_congr' fun hv ↦ by change (u.val.2 v * y.2 v ∈ _) ↔ _; rw [hc.2.2 v hv, one_mul]
  have proj : adeleProjection F S (u.val * y) = g.inv * adeleProjection F S y :=
    Prod.ext (congrArg (· * y.1) hc.1) (funext fun v ↦ congrArg (· * y.2 v.val) (hc.2.1 v))
  have ht := sAdeleSchwartzToGlobal_apply F S (schwartzBruhatUnitTranslate g f) y
  have hs := sAdeleSchwartzToGlobal_apply F S f (u.val * y)
  refine ht.trans (Eq.trans ?_ hs.symm)
  exact if_congr outside.symm (congrArg (fun t ↦ f (Multiplicative.ofAdd t)) proj.symm) rfl

local notation "au(" S "," w "," x ")" => (ContinuousMulEquiv.prodUnits (InfiniteAdeleRing F) ((p : S) → HeightOneSpectrum.adicCompletion F p.val)).symm (ContinuousMulEquiv.piUnits.symm (@Pi.mulSingle _ _ _ (Classical.decEq _) w x), 1)
local notation "fu(" S "," v "," x ")" => (ContinuousMulEquiv.prodUnits (InfiniteAdeleRing F) ((p : S) → HeightOneSpectrum.adicCompletion F p.val)).symm (1, ContinuousMulEquiv.piUnits.symm (@Pi.mulSingle _ _ _ (Classical.decEq _) v x))


private abbrev stageUnits (S : Finset V) : (InfinitePlace F ⊕ ↥S) → Type _ :=
  Sum.elim (fun w : InfinitePlace F ↦ w.Completionˣ) (fun v : S ↦ (v.val.adicCompletion F)ˣ)

private def stageUnit (S : Finset V) : ∀ i : (InfinitePlace F ⊕ ↥S), stageUnits S i → (SAdeleRing F S)ˣ
  | .inl w, u => au(S,w,u)
  | .inr v, u => fu(S,v,u)

private def stageLocalTranslate (S : Finset V) : ∀ i : (InfinitePlace F ⊕ ↥S), stageUnits S i →
    SchwartzBruhat (stageCoordinateGroup S i) → SchwartzBruhat (stageCoordinateGroup S i)
  | .inl w, u, f => schwartzBruhatUnitTranslate (R := w.Completion) u f
  | .inr v, u, f => schwartzBruhatUnitTranslate (R := v.val.adicCompletion F) u f

private def stageGaussian (χ : PontryaginDual C_F) (S : Finset V) :
    ∀ i : (InfinitePlace F ⊕ ↥S), SchwartzBruhat (stageCoordinateGroup S i)
  | .inl w => a₀(χ,w)
  | .inr v => b₀(χ,v.val)

private theorem stageTranslate_same (S : Finset V) (i : (InfinitePlace F ⊕ ↥S)) (u : stageUnits S i)
    (k : SchwartzBruhat (stageCoordinateGroup S i)) (x : SAdeleRing F S) :
    stageLocalTranslate S i u k (sAdeleToProduct S (Multiplicative.ofAdd x) i) =
      k (sAdeleToProduct S (Multiplicative.ofAdd ((stageUnit S i u).inv * x)) i) := by
  let : DecidableEq S := Classical.decEq _
  cases i with
  | inl w =>
    change w.Completionˣ at u
    change k (Multiplicative.ofAdd ((u.inv : w.Completion) * x.1 w)) =
      k (Multiplicative.ofAdd (((Pi.mulSingle (M := (fun p : InfinitePlace F ↦ p.Completionˣ)) w u w).inv : w.Completion) * x.1 w))
    rw [Pi.mulSingle_eq_same]
  | inr v =>
    change (v.val.adicCompletion F)ˣ at u
    change k (Multiplicative.ofAdd ((u.inv : v.val.adicCompletion F) * x.2 v)) =
      k (Multiplicative.ofAdd (((Pi.mulSingle (M := (fun p : S ↦ (p.val.adicCompletion F)ˣ)) v u v).inv : v.val.adicCompletion F) * x.2 v))
    rw [Pi.mulSingle_eq_same]

private theorem stageTranslate_other (S : Finset V) {i j : (InfinitePlace F ⊕ ↥S)} (u : stageUnits S i)
    (hj : j ≠ i) (x : SAdeleRing F S) :
    sAdeleToProduct S (Multiplicative.ofAdd ((stageUnit S i u).inv * x)) j = sAdeleToProduct S (Multiplicative.ofAdd x) j := by
  let : DecidableEq S := Classical.decEq _
  cases i with
  | inl w =>
    change w.Completionˣ at u
    cases j with
    | inl t =>
      change Multiplicative.ofAdd ((Pi.mulSingle (M := (fun p : InfinitePlace F ↦ p.Completionˣ)) w u t).inv * x.1 t) = _
      rw [Pi.mulSingle_eq_of_ne (fun h ↦ hj (congrArg Sum.inl h))]
      exact congrArg Multiplicative.ofAdd (one_mul _)
    | inr v => exact congrArg (fun y : v.val.adicCompletion F ↦ Multiplicative.ofAdd y) (one_mul (x.2 v))
  | inr v =>
    change (v.val.adicCompletion F)ˣ at u
    cases j with
    | inl w => exact congrArg (fun y : w.Completion ↦ Multiplicative.ofAdd y) (one_mul (x.1 w))
    | inr t =>
      change Multiplicative.ofAdd ((Pi.mulSingle (M := (fun p : S ↦ (p.val.adicCompletion F)ˣ)) v u t).inv * x.2 t) = _
      rw [Pi.mulSingle_eq_of_ne (fun h ↦ hj (congrArg Sum.inr h))]
      exact congrArg Multiplicative.ofAdd (one_mul _)

private theorem eval_of_unique_eigen {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (W : Submodule ℂ (StrongDual ℂ E)) (d T : StrongDual ℂ E) (b : E)
    (hd : ∀ L : StrongDual ℂ E, L = d ↔ L ∈ W ∧ L b = 1) (hT : T ∈ W) (f : E) :
    T f = d f * T b := by
  have hb := (hd d).mp rfl
  let L := T + (1 - T b) • d
  have he : L = d := (hd L).mpr ⟨W.add_mem hT (W.smul_mem _ hb.1), by
    change T b + (1 - T b) * d b = 1
    rw [hb.2, mul_one]; ring⟩
  have h := DFunLike.congr_fun he f
  change T f + (1 - T b) * d f = d f at h
  linear_combination h

private theorem stageLocal_ratio_arch (χ : PontryaginDual C_F) (S : Finset V) (z : ℂ) (w : InfinitePlace F)
    (L : StrongDual ℂ ℬ(w.Completion))
    (hL : ∀ (u : w.Completionˣ) k, L (schwartzBruhatUnitTranslate u k) =
      ideleClassNormTwist χ z (classOf (sIdeleInsertion F S au(S,w,u))) * L k) (f : ℬ(w.Completion)) :
    L f = DA(χ,w) z f * L (a₀(χ,w)) := by
  have hloc : L ∈ schwartzBruhatEigendistributions (arc(χ,w,z)) := by
    intro u k
    have e := sIdeleInsertion_infiniteUnit (F := F) (S := S) w u
    have e' := congrArg (fun g : I_F ↦ ideleClassNormTwist χ z (classOf g)) e
    exact (hL u k).trans (congrArg (· * L k) (e'.trans (DFunLike.congr_fun (infinitePlaceRestriction_eq_twist χ w z) u)))
  exact eval_of_unique_eigen _ (DA(χ,w) z) L _ ((infiniteEigendistribution_normalized w χ∞(χ,w)).choose_spec.2.1 z) hloc f

private theorem stageLocal_ratio_fin (χ : PontryaginDual C_F) (S : Finset V) (z : ℂ) (v : S)
    (L : StrongDual ℂ ℬ(v.val.adicCompletion F))
    (hL : ∀ (u : (v.val.adicCompletion F)ˣ) k, L (schwartzBruhatUnitTranslate u k) =
      ideleClassNormTwist χ z (classOf (sIdeleInsertion F S fu(S,v,u))) * L k) (f : ℬ(v.val.adicCompletion F)) :
    L f = DB(χ,v.val) z f * L (b₀(χ,v.val)) := by
  have hloc : L ∈ schwartzBruhatEigendistributions (fin(χ,v.val,z)) := by
    intro u k
    have e := sIdeleInsertion_finiteUnit (F := F) (S := S) v u
    have e' := congrArg (fun g : I_F ↦ ideleClassNormTwist χ z (classOf g)) e
    exact (hL u k).trans (congrArg (· * L k) (e'.trans (DFunLike.congr_fun (finitePlaceRestriction_eq_twist χ v.val z) u)))
  have hG := (congrArg (finiteStandardGaussian v.val) (finitePlaceRestriction_eq_twist χ v.val z).symm).trans (finiteGaussian_twist_eq χ v.val z)
  have h := eval_of_unique_eigen _ (DB(χ,v.val) z) L _ ((finiteEigendistribution_normalized v.val χv(χ,v.val)).choose_spec.2.1 z) hloc f
  exact h.trans (congrArg (DB(χ,v.val) z f * ·) (congrArg L hG))

private theorem stageLocal_ratio (χ : PontryaginDual C_F) (S : Finset V) (z : ℂ) (i : (InfinitePlace F ⊕ ↥S)) :
    ∀ (L : StrongDual ℂ (SchwartzBruhat (stageCoordinateGroup S i)))
    (hL : ∀ (u : stageUnits S i) k, L (stageLocalTranslate S i u k) =
      ideleClassNormTwist χ z (classOf (sIdeleInsertion F S (stageUnit S i u))) * L k) (f : SchwartzBruhat (stageCoordinateGroup S i)),
    L f = stageLocalDual χ S i z f * L (stageGaussian χ S i) := by
  cases i with
  | inl w => exact stageLocal_ratio_arch χ S z w
  | inr v => exact stageLocal_ratio_fin χ S z v

private def InsertEigenValue : Prop :=
  ∀ (χ : PontryaginDual C_F) (s : ℂ) (S : Finset V)
    (T : StrongDual ℂ ℬ(𝔸[F])) (hT : T ∈ adelicEigendistributions (ideleClassNormTwist χ s))
    (i : InfinitePlace F ⊕ S) (q : ∀ j, SchwartzBruhat (stageCoordinateGroup S j))
    (ins : SchwartzBruhat (stageCoordinateGroup S i) →L[ℂ] ℬ(SAdeleRing F S))
    (atX : ∀ (k : SchwartzBruhat (stageCoordinateGroup S i)) (x : Multiplicative (SAdeleRing F S)),
      ins k x = k (sAdeleToProduct S x i) * ∏ j : {j // j ≠ i}, q j.val (sAdeleToProduct S x j.val))
    (k : SchwartzBruhat (stageCoordinateGroup S i)),
    T (sAdeleSchwartzToGlobal F S (ins k)) =
      stageLocalDual χ S i s k * T (sAdeleSchwartzToGlobal F S (ins (stageGaussian χ S i)))

private theorem stageEigen_insert_value : InsertEigenValue (F := F) := by
  intro χ s S T hT i q ins atX k
  let extS : ℬ(SAdeleRing F S) →L[ℂ] ℬ(𝔸[F]) := ⟨sAdeleSchwartzToGlobal F S, (sAdeleSchwartzToGlobal_isEmbedding F S).continuous⟩
  let L := (T.comp extS).comp ins
  have he (u : stageUnits S i) (a : SchwartzBruhat (stageCoordinateGroup S i)) :
      L (stageLocalTranslate S i u a) =
        ideleClassNormTwist χ s (classOf (sIdeleInsertion F S (stageUnit S i u))) * L a := by
    classical
    let v := stageUnit S i u
    have he : ins (stageLocalTranslate S i u a) = schwartzBruhatUnitTranslate v (ins a) := by
      apply Subtype.ext
      funext x
      let y := Multiplicative.ofAdd (v.inv * x.toAdd)
      have left := stageTranslate_same S i u a x.toAdd
      have right : (∏ j : {j // j ≠ i}, q j.val (sAdeleToProduct S x j.val)) =
          ∏ j : {j // j ≠ i}, q j.val (sAdeleToProduct S y j.val) := Finset.prod_congr rfl fun j _ ↦
        congrArg (q j.val) (stageTranslate_other S u j.property x.toAdd).symm
      exact (atX _ x).trans ((congrArg₂ (· * ·) left right).trans (atX a y).symm)
    exact (congrArg (fun t ↦ T (sAdeleSchwartzToGlobal F S t)) he).trans
      ((congrArg T (sAdeleToGlobal_translate S v (ins a))).trans (hT _ (sAdeleSchwartzToGlobal F S (ins a))))
  change L k = stageLocalDual χ S i s k * L (stageGaussian χ S i)
  exact stageLocal_ratio (F := F) χ S s i L he k

private def StageEigenFactor : Prop :=
  ∀ (χ : PontryaginDual C_F) (s : ℂ) (S : Finset V)
    (T : StrongDual ℂ ℬ(𝔸[F])) (hT : T ∈ adelicEigendistributions (ideleClassNormTwist χ s))
    (eval : (∀ j, SchwartzBruhat (stageCoordinateGroup S j)) → ℂ)
    (eval_pure : ∀ q k, stagePure S q k → eval q = T (sAdeleSchwartzToGlobal F S k))
    (i : InfinitePlace F ⊕ S) (q : ∀ j, SchwartzBruhat (stageCoordinateGroup S j)),
    eval q = stageLocalDual χ S i s (q i) * eval (Function.update q i (stageGaussian χ S i))

private theorem stageEigen_factor : StageEigenFactor (F := F) := by
  intro χ s S T hT eval eval_pure i q
  classical
  let G := stageCoordinateGroup S
  let e := sAdeleToProduct S
  let : LocallyCompactSpace (Multiplicative (SAdeleRing F S)) := e.toHomeomorph.isOpenEmbedding.locallyCompactSpace
  let : T2Space (Multiplicative (SAdeleRing F S)) := e.toHomeomorph.isEmbedding.t2Space
  with_reducible refine (exists_schwartzBruhat_comp_equivCLM e).elim fun r hr ↦ ?_
  with_reducible refine (insertLocalTest G i q).elim fun J hJ ↦ ?_
  let ins := r.comp J
  let L (k : SchwartzBruhat (G i)) := T (sAdeleSchwartzToGlobal F S (ins k))
  have atX (k : SchwartzBruhat (G i)) (x : Multiplicative (SAdeleRing F S)) :
      ins k x = k (e x i) * ∏ j : {j // j ≠ i}, q j.val (e x j.val) := (hr (J k) x).trans (hJ k (e x))
  have eq₁ : eval q = L (q i) := eval_pure q (ins (q i)) fun x ↦
    (atX _ x).trans (prod_at_index i (fun j ↦ q j (e x j))).symm
  let d := stageGaussian χ S i
  have eq₂ : eval (Function.update q i d) = L d := by
    refine eval_pure (Function.update q i d) (ins d) (fun x ↦ ?_)
    refine (atX d x).trans ?_
    rw [prod_at_index i (fun j ↦ Function.update q i d j (e x j)), Function.update_self]
    exact congrArg (_ * ·) (Finset.prod_congr rfl fun j _ ↦
      (congrArg (fun k : SchwartzBruhat (G j.val) ↦ k (e x j.val)) (Function.update_of_ne j.property d q)).symm)
  have rule := stageEigen_insert_value (F := F)
  have he := rule χ s S T hT i q ins atX (q i)
  exact eq₁.trans (he.trans (congrArg (_ * ·) eq₂.symm))

private theorem globalEigen_on_stage (χ : PontryaginDual C_F) (s : ℂ) (S : Finset V)
    (T : StrongDual ℂ ℬ(𝔸[F])) (hT : T ∈ adelicEigendistributions (ideleClassNormTwist χ s))
    (a : ∀ i, SchwartzBruhat (stageCoordinateGroup S i)) (f b : ℬ(SAdeleRing F S))
    (hf : stagePure S a f) (hb : stagePure S (stageGaussian χ S) b) :
    T (sAdeleSchwartzToGlobal F S f) = (∏ i, stageLocalDual χ S i s (a i)) * T (sAdeleSchwartzToGlobal F S b) := by
  classical
  let G := stageCoordinateGroup S
  let e := sAdeleToProduct S
  let : LocallyCompactSpace (Multiplicative (SAdeleRing F S)) := e.toHomeomorph.isOpenEmbedding.locallyCompactSpace
  let : T2Space (Multiplicative (SAdeleRing F S)) := e.toHomeomorph.isEmbedding.t2Space
  let extS : ℬ(SAdeleRing F S) →L[ℂ] ℬ(𝔸[F]) := ⟨sAdeleSchwartzToGlobal F S, (sAdeleSchwartzToGlobal_isEmbedding F S).continuous⟩
  let Tₛ := T.comp extS
  with_reducible refine (exists_schwartzBruhat_comp_equivCLM e).elim fun r hr ↦ ?_
  choose p hp using (schwartzBruhat_pi_test G)
  let eval (q : ∀ i, SchwartzBruhat (G i)) := Tₛ (r (p q))
  have eval_pure (q : ∀ i, SchwartzBruhat (G i)) (k : ℬ(SAdeleRing F S)) (hk : stagePure S q k) :
      eval q = Tₛ k := congrArg Tₛ (Subtype.ext (funext fun x ↦
        (hr (p q) x).trans ((hp q (e x)).trans (hk x).symm)))
  have rule := stageEigen_factor (F := F)
  have factor := rule χ s S T hT eval eval_pure
  exact (eval_pure a f hf).symm.trans ((scalar_of_coordinate_factors eval (fun i ↦ stageLocalDual χ S i s)
    (stageGaussian χ S) factor a).trans (congrArg (_ * ·) (eval_pure _ b hb)))

private theorem global_normalized_ext (χ : PontryaginDual C_F) (s : ℂ)
    (T U : StrongDual ℂ ℬ(𝔸[F]))
    (ht : T ∈ adelicEigendistributions (ideleClassNormTwist χ s))
    (hu : U ∈ adelicEigendistributions (ideleClassNormTwist χ s))
    (hG : T (adelicStandardGaussian χ) = U (adelicStandardGaussian χ)) : T = U := by
  classical
  apply ContinuousLinearMap.ext
  intro f
  have covered := exists_normalized_stage (F := F) χ 0 f (fun v ↦ b₀(χ,v)) (.of_forall fun _ ↦ rfl)
  refine covered.elim fun S h ↦ ?_
  refine h.2.2.elim fun fS hh ↦ hh.elim fun b hb ↦ ?_
  let extS : ℬ(SAdeleRing F S) →L[ℂ] ℬ(𝔸[F]) := ⟨sAdeleSchwartzToGlobal F S, (sAdeleSchwartzToGlobal_isEmbedding F S).continuous⟩
  have hzero (v : V) (hv : v ∉ S) : b₀(χ,v) (Multiplicative.ofAdd 0) = 1 := by
    have hr := (unramifiedAt_iff_restriction _ v).mp (h.1 0 v hv)
    exact (ite_eq_left hr).trans (indicator_of_mem (v.adicCompletionIntegers F).zero_mem _)
  have hb' := sAdeleSchwartz_pureTensor_of_global S b (fun w ↦ a₀(χ,w)) (fun v ↦ b₀(χ,v)) hzero
    (fun x ↦ by rw [hb.2]; rfl)
  have pure : stagePure S (stageGaussian χ S) b := fun x ↦
    (hb' x.toAdd).trans (Fintype.prod_sum_type (fun i ↦ stageGaussian χ S i (sAdeleToProduct S x i))).symm
  have equalB : T (sAdeleSchwartzToGlobal F S b) = U (sAdeleSchwartzToGlobal F S b) :=
    (congrArg T hb.2).trans (hG.trans (congrArg U hb.2).symm)
  let rule := @globalEigen_on_stage F _ _
  have he : T.comp extS = U.comp extS := by
    apply (stageProducts (F := F) χ S).2
    intro a k hk
    exact (rule χ s S T ht a k b hk pure).trans
      ((congrArg (_ * ·) equalB).trans (rule χ s S U hu a k b hk pure).symm)
  exact (congrArg T hb.1.symm).trans ((DFunLike.congr_fun he fS).trans (congrArg U hb.1))

end

/-- Paper: Theorem 3.4.3.3(2), p. 153. The unique global eigendistribution normalized
on the adelic Gaussian varies holomorphically. Multiplication by the Gaussian zeta
function recovers the global zeta function away from its possible poles.
Deviation: The scalar factor uses the Gaussian normalization of p. 152, including
its Tamagawa scale relative to the completed Euler product in §3.2. -/
theorem adelicEigendistribution_normalized (χ : PontryaginDual C_F) :
    ∃ D : ℂ → StrongDual ℂ ℬ(𝔸[F]), VectorHolomorphicOn D univ ∧
      (∀ s : ℂ, ∀ T : StrongDual ℂ ℬ(𝔸[F]),
        T = D s ↔ T ∈ adelicEigendistributions (ideleClassNormTwist χ s) ∧
          T (adelicStandardGaussian χ) = 1) ∧
      ∀ s : ℂ, ideleClassNormTwist χ s ≠ 1 →
        ideleClassNormTwist χ s ≠ ideleClassNormTwist (1 : PontryaginDual C_F) 1 →
        ∀ f : ℬ(𝔸[F]), globalIdelicZFunction f (ideleClassNormTwist χ s) =
          gaussianCompletedHeckeL χ s * D s f := by
  let germ := @globalFamily_germ F _ _
  let eigen := @globalFamily_eigen F _ _
  let normed := @globalFamily_normalized F _ _
  let hstrong := @adelic_dual_holomorphic F _ _
  let matchZ := @globalFamily_matches_zeta F _ _
  let unique := @global_normalized_ext F _ _
  refine (germ χ).elim fun D hh ↦ ?_
  have ha := hh.1
  have hg := hh.2
  have he := eigen χ D ha hg
  have hn := normed χ D ha hg
  refine ⟨D, hstrong D ha, fun s T ↦ ⟨?_, ?_⟩, matchZ χ D ha hg⟩
  · rintro rfl
    exact ⟨he s, hn s⟩
  · intro ht
    exact unique χ s T (D s) ht.1 (he s) (ht.2.trans (hn s).symm)

/-- Paper: Theorem 3.4.3.3(2), p. 153. The global eigendistributions of
each idelic weight form a one-dimensional space. -/
theorem adelicEigendistributions_rank (c : X) :
    Module.rank ℂ (adelicEigendistributions c) = 1 := by
  let : T2Space C_F := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.1
  let : LocallyCompactSpace C_F := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.1
  have hx : ∃ (χ : PontryaginDual C_F) (s : ℂ), ideleClassNormTwist χ s = c := exists_unitary_normTwist (ideleClassNorm F) (isProperMap_ideleClassNorm F)
    ideleClassNorm_ne_one c
  refine hx.elim fun χ hχ ↦ hχ.elim fun s hs ↦ ?_
  exact (congrArg (fun d : X ↦ Module.rank ℂ (adelicEigendistributions d)) hs.symm).trans
    (rank_one_of_unique_normalization _ _ ((adelicEigendistribution_normalized χ).choose s)
      ((adelicEigendistribution_normalized χ).choose_spec.2.1 s))

local notation "DG(" χ ")" => (adelicEigendistribution_normalized (χ)).choose

private theorem globalIntegral_normalized_ratio (χ : PontryaginDual C_F) {z : ℂ} (hz : 1 < z.re)
    (f : ℬ(𝔸[F])) :
    globalIdelicZetaIntegral f (ideleClassNormTwist χ z) = gaussianCompletedHeckeL χ z * DG(χ) z f := by
  have ha := ideleClassNormTwist_abscissa χ z
  let σ := quasiCharacterAbscissa (ideleClassNorm F) (isProperMap_ideleClassNorm F) (ideleClassNorm_ne_one (F := F))
  have h₀ : σ 1 = 0 := by
    change Real.log ‖(1 : ℂ)‖ / _ = 0
    rw [norm_one, Real.log_one, zero_div]
  have h₁ := ideleClassNormTwist_abscissa (1 : PontryaginDual C_F) 1
  have hn : ideleClassNormTwist χ z ≠ 1 := fun h ↦ (zero_lt_one.trans hz).ne' (ha.symm.trans ((congrArg σ h).trans h₀))
  have hn' : ideleClassNormTwist χ z ≠ ideleClassNormTwist (1 : PontryaginDual C_F) 1 :=
    fun h ↦ hz.ne' (ha.symm.trans ((congrArg σ h).trans h₁))
  exact (globalIdelicZFunction_eq_integral f (x := ideleClassNormTwist χ z) (hz.trans_eq ha.symm)).symm.trans
    ((adelicEigendistribution_normalized χ).choose_spec.2.2 z hn hn' f)

private theorem normalized_tensor_on_stage (χ : PontryaginDual C_F) (s : ℂ) (S : Finset V)
    (houtside : ∀ z : ℂ, ideleClassNormTwist χ z ∈ unramifiedOutside F S)
    (f : ℬ(𝔸[F])) (a : (w : InfinitePlace F) → ℬ(w.Completion)) (b : (v : V) → ℬ(v.adicCompletion F))
    (fS gS : ℬ(SAdeleRing F S)) (hF : sAdeleSchwartzToGlobal F S fS = f)
    (hG : sAdeleSchwartzToGlobal F S gS = adelicStandardGaussian χ)
    (hb : ∀ v ∉ S, b v = finiteStandardGaussian v (finitePlaceRestriction F v (ideleClassNormTwist χ s)))
    (hf : ∀ x : 𝔸[F], f (Multiplicative.ofAdd x) = (∏ w, a w (Multiplicative.ofAdd (x.1 w))) *
      ∏ᶠ v : V, b v (Multiplicative.ofAdd (x.2 v))) :
    DG(χ) s f = (∏ w, DA(χ,w) s (a w)) * ∏ v : S, DB(χ,v.val) s (b v.val) := by
  classical
  have h0 (v : V) (hv : v ∉ S) : b₀(χ,v) (Multiplicative.ofAdd 0) = 1 := by
    have hU := (unramifiedAt_iff_restriction _ v).mp (houtside 0 v hv)
    exact (ite_eq_left hU).trans (indicator_of_mem (v.adicCompletionIntegers F).zero_mem _)
  have hsF := sAdeleSchwartz_pureTensor_of_global S fS a b (fun v hv ↦ by
    rw [hb v hv, finiteGaussian_twist_eq χ v s]; exact h0 v hv) (fun x ↦ by rw [hF]; exact hf x)
  have hsG := sAdeleSchwartz_pureTensor_of_global S gS (fun w ↦ a₀(χ,w)) (fun v ↦ b₀(χ,v))
    h0 (fun x ↦ by rw [hG]; rfl)
  let A (z : ℂ) := ∏ w, DA(χ,w) z (a w)
  let B (z : ℂ) := ∏ v : S, DB(χ,v.val) z (b v.val)
  have hg := analytic_eval_normalized (adelicEigendistribution_normalized χ).choose_spec.1 f
  have hpa : AnalyticOnNhd ℂ A univ := Finset.univ.analyticOnNhd_fun_prod fun w _ ↦
    analytic_eval_normalized (infiniteEigendistribution_normalized w χ∞(χ,w)).choose_spec.1 (a w)
  have hpb : AnalyticOnNhd ℂ B univ := Finset.univ.analyticOnNhd_fun_prod fun v _ ↦
    analytic_eval_normalized (finiteEigendistribution_normalized v.val χv(χ,v.val)).choose_spec.1 (b v.val)
  have hnear : ∀ᶠ z : ℂ in 𝓝[≠] 2, 1 < z.re :=
    (Complex.continuous_re.continuousAt.eventually (lt_mem_nhds (by norm_num : 1 < (2 : ℂ).re))).filter_mono nhdsWithin_le_nhds
  have he : ∀ᶠ z : ℂ in 𝓝[≠] 2, DG(χ) z f = A z * B z := by
    refine (hnear.and (all_infiniteIntegral_normalized_ratio χ)).mono fun z hh ↦ ?_
    have hz : 1 < z.re := hh.1
    have h := globalIntegral_tensor_ratio χ z hz S (houtside z) fS gS a b hsF hsG (fun w ↦ hh.2 w (a w))
    let Z (k : ℬ(𝔸[F])) := globalIdelicZetaIntegral k (ideleClassNormTwist χ z)
    have eF : Z (sAdeleSchwartzToGlobal F S fS) = gaussianCompletedHeckeL χ z * DG(χ) z f := (congrArg Z hF).trans (globalIntegral_normalized_ratio χ hz f)
    have eG : Z (sAdeleSchwartzToGlobal F S gS) = gaussianCompletedHeckeL χ z := (congrArg Z hG).trans (gaussianCompletedHeckeL_eq_integral χ z hz).symm
    have hne : gaussianCompletedHeckeL χ z ≠ 0 := by
      rw [gaussianCompletedHeckeL_eq_completedHeckeL χ z hz]
      exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (inv_ne_zero (Real.sqrt_ne_zero'.mpr
        (abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero F))))) (mul_ne_zero
        (heckeGammaFactor_ne_zero_of_re_pos χ (zero_lt_one.trans hz)) (finiteHeckeL_ne_zero_of_one_lt_re χ ⟨z,hz⟩))
    exact mul_left_cancel₀ hne (eF.symm.trans (h.trans (congrArg (· * (A z * B z)) eG)))
  exact hg.eqOn_of_preconnected_of_frequently_eq (hpa.mul hpb) isPreconnected_univ (mem_univ 2) he.frequently (mem_univ s)

private theorem finprod_eq_subtype_prod_of_tail {ι : Type*} (S : Finset ι) (f : ι → ℂ)
    (h : ∀ i ∉ S, f i = 1) : (∏ᶠ i, f i) = ∏ i : S, f i.val :=
  (finprod_eq_prod_of_mulSupport_subset f (mulSupport_subset_iff'.mpr h)).trans
    (Finset.prod_subtype S (fun _ ↦ Iff.rfl) f)

/-- Paper: Equation (3.4.3.14), p. 153. The normalized global eigendistribution
evaluates on a restricted pure tensor as the product of normalized local evaluations.
Deviation: Pointwise factorization specifies the test tensor. The product of finite-place
evaluations has finite support because the local factors are normalized on the standard Gaussians. -/
theorem adelicEigendistribution_apply_pureTensor (χ : PontryaginDual C_F) (s : ℂ) :
    let c := ideleClassNormTwist χ s
    ∀ (T : StrongDual ℂ ℬ(𝔸[F]))
      (TArch : (w : InfinitePlace F) → StrongDual ℂ ℬ(w.Completion))
      (TFin : (v : V) → StrongDual ℂ ℬ(v.adicCompletion F)),
      T ∈ adelicEigendistributions c → T (adelicStandardGaussian χ) = 1 →
      (∀ w, TArch w ∈ schwartzBruhatEigendistributions (infinitePlaceRestriction F w c) ∧
        TArch w (infiniteStandardGaussian w (infiniteUnitaryRestriction(χ,w))) = 1) →
      (∀ v, TFin v ∈ schwartzBruhatEigendistributions (finitePlaceRestriction F v c) ∧
        TFin v (finiteStandardGaussian v (finitePlaceRestriction F v c)) = 1) →
      ∀ (f : ℬ(𝔸[F])) (fArch : (w : InfinitePlace F) → ℬ(w.Completion))
        (fFin : (v : V) → ℬ(v.adicCompletion F)),
        (∀ᶠ v in cofinite, fFin v = finiteStandardGaussian v (finitePlaceRestriction F v c)) →
        (∀ x : 𝔸[F], f (Multiplicative.ofAdd x) =
          (∏ w : InfinitePlace F, fArch w (Multiplicative.ofAdd (x.1 w))) *
            ∏ᶠ v : V, fFin v (Multiplicative.ofAdd (x.2 v))) →
        T f = (∏ w : InfinitePlace F, TArch w (fArch w)) * ∏ᶠ v : V, TFin v (fFin v) := by
  classical
  intro c T TArch TFin hT hTG hA hB f a b htail hf
  have heT : T = DG(χ) s := ((adelicEigendistribution_normalized χ).choose_spec.2.1 s T).mpr ⟨hT, hTG⟩
  have heA (w : InfinitePlace F) : TArch w = DA(χ,w) s := by
    apply ((infiniteEigendistribution_normalized w χ∞(χ,w)).choose_spec.2.1 s _).mpr
    exact ⟨(congrArg (fun d : QuasiCharacter w.Completionˣ ↦ TArch w ∈ schwartzBruhatEigendistributions d)
      (infinitePlaceRestriction_eq_twist χ w s)).mp (hA w).1, (hA w).2⟩
  have heB (v : V) : TFin v = DB(χ,v) s := by
    apply ((finiteEigendistribution_normalized v χv(χ,v)).choose_spec.2.1 s _).mpr
    exact (congrArg (fun d : QuasiCharacter (v.adicCompletion F)ˣ ↦ TFin v ∈ schwartzBruhatEigendistributions d ∧
      TFin v (finiteStandardGaussian v d) = 1) (finitePlaceRestriction_eq_twist χ v s)).mp (hB v)
  refine (exists_normalized_stage χ s f b htail).elim fun S h ↦ ?_
  have hS := h.1
  have hb := h.2.1
  refine h.2.2.elim fun fS hstage ↦ hstage.elim fun gS hh ↦ ?_
  have hF := hh.1
  have hG := hh.2
  have hall := normalized_tensor_on_stage χ s S hS f a b fS gS hF hG hb hf
  have vprod (v : V) (hv : v ∉ S) : TFin v (b v) = 1 :=
    (congrArg (TFin v) (hb v hv)).trans (hB v).2
  have hfin := finprod_eq_subtype_prod_of_tail S (fun v : V ↦ TFin v (b v)) vprod
  refine (congrArg (fun M : StrongDual ℂ ℬ(𝔸[F]) ↦ M f) heT).trans (hall.trans (congrArg₂ (· * ·) ?_ ?_))
  · exact Finset.prod_congr rfl fun w _ ↦ congrArg (fun M : StrongDual ℂ ℬ(w.Completion) ↦ M (a w)) (heA w).symm
  · refine Eq.trans (Finset.prod_congr rfl fun v _ ↦ ?_) hfin.symm
    exact congrArg (fun M : StrongDual ℂ ℬ(v.val.adicCompletion F) ↦ M (b v.val)) (heB v.val).symm

end


-- Remark 3.4.3.4, p. 153. The tensor acts on the full test space by continuity.
-- The completed archimedean product uses `schwartzBruhat_kernel_equiv`; the finite
-- stages and their passage to the adeles use `sAdeleSchwartz_inductiveTensor_equiv`
-- and `sAdeleSchwartzToGlobal_finalTopology`.

end Gaussians

end RiemannMasullo
