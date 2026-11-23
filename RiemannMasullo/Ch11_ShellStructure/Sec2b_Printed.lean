module

public import RiemannMasullo.Ch11_ShellStructure.Sec2b
import RiemannMasullo.Ch10_TraceSpectral.Sec1
import all RiemannMasullo.Ch06_LocalGlobal.Sec2
import all RiemannMasullo.Ch03_IdelicZeta.Sec3
import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-! # §11.2.1–11.2.2 assertions that are false as printed -/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

set_option quotPrecheck false
set_option maxSynthPendingDepth 8
set_option Elab.async false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 instSIdeleQuotientMeasurableSpaceSec1

local notation "C𝔽(" F ")" => IdeleClassGroup (𝓞 F) F
local notation "C₁(" F ")" => (ideleClassNorm F).ker
local notation "V(" F ")" => HeightOneSpectrum (𝓞 F)
local notation "m𝔽(" F ")" =>
  (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽(F) →ₜ* ℝ≥0ˣ)
local notation "mₛ(" F ", " S ")" =>
  (⟨sIdeleQuotientNorm F S, (isProperMap_sIdeleQuotientNorm F S).continuous⟩ :
    SIdeleQuotient F S →ₜ* ℝ≥0ˣ)
local notation "μₛ(" F ", " S ")" => sLocalQuotientTamagawaMeasure F S
local notation "Wω(" F ", " hs ", " ω ")" =>
  actionIsotype ((hardySobolevTranslation (ideleClassTamagawaMeasure F) (m𝔽(F))
    0 0 _ (le_rfl (a := (0 : ℝ))) hs).comp (ideleClassNorm F).ker.subtype) ω
local notation "localMeasure(" F ", " S ", " s ")" =>
  (μₛ(F, S)).withDensity (fun g ↦
    ENNReal.ofReal (intervalSobolevDensity 0 0 s (Real.log (((mₛ(F, S)) g).val : ℝ))))
local notation "localTheta(" F ", " S ", " a ", " ω ", " f ")" =>
  modulationWeight (mₛ(F, S)) a (sLocalHomogeneousAdelicThetaLinearMap F S ω f)

local notation "qₛ(" F ", " S ", " ω ")" =>
  (LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap F S ω)).mkQ

private theorem sec2bP_units (ξ : (Set.integer ((∅ : Finset V(ℚ)) : Set V(ℚ)) ℚ)ˣ) :
    ξ = 1 ∨ ξ = -1 := by
  have hmem : ∀ x : (Set.integer ((∅ : Finset V(ℚ)) : Set V(ℚ)) ℚ),
      ∃ y : 𝓞 ℚ, algebraMap (𝓞 ℚ) ℚ y = (x : ℚ) := by
    intro x
    have he : ((∅ : Finset V(ℚ)) : Set V(ℚ)).integer ℚ = ⊥ := by
      rw [Finset.coe_empty, integer_empty]
    have hx : (x : ℚ) ∈ (⊥ : Subalgebra (𝓞 ℚ) ℚ) := he ▸ x.property
    exact Algebra.mem_bot.mp hx
  obtain ⟨a, ha⟩ := hmem ξ.val
  obtain ⟨b, hb⟩ := hmem (ξ⁻¹).val
  have hab : a * b = 1 := by
    apply IsFractionRing.injective (𝓞 ℚ) ℚ
    rw [map_mul, ha, hb, map_one]
    have h := congrArg Subtype.val ξ.mul_inv
    exact h
  have hu : IsUnit (Rat.ringOfIntegersEquiv a) := (IsUnit.of_mul_eq_one b hab).map _
  rcases Int.isUnit_iff.mp hu with h | h
  · left
    have ha1 : a = 1 := Rat.ringOfIntegersEquiv.injective (h.trans (map_one _).symm)
    apply Units.ext
    apply Subtype.ext
    rw [← ha, ha1, map_one]
    rfl
  · right
    have ha1 : a = -1 := Rat.ringOfIntegersEquiv.injective (h.trans (by simp))
    apply Units.ext
    apply Subtype.ext
    rw [← ha, ha1, map_neg, map_one]
    rfl

private theorem sec2bP_one_ne_neg_one :
    (1 : (Set.integer ((∅ : Finset V(ℚ)) : Set V(ℚ)) ℚ)ˣ) ≠ -1 := by
  intro h
  have h' := congrArg (fun u : (Set.integer ((∅ : Finset V(ℚ)) : Set V(ℚ)) ℚ)ˣ ↦
    Subtype.val (Units.val u)) h
  norm_num at h'

private theorem sec2bP_norm (x : (SAdeleRing ℚ ∅)ˣ) :
    ((sIdeleNorm ℚ ∅ x : ℝ≥0) : ℝ) = ‖x.val.1 Rat.infinitePlace‖ := by
  simp [sIdeleNorm]
  rw [Unique.eq_default Rat.infinitePlace]

private theorem sec2bP_abs (z : Rat.infinitePlace.Completion) :
    |InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace z| = ‖z‖ := by
  rw [← Real.norm_eq_abs, ← dist_zero_right, ← dist_zero_right z,
    ← map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace)]
  exact (InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace).dist_eq z 0

private theorem sec2bP_thetaClasses (f : SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅)))
    (φ : ℝ → ℂ) (hf : ∀ x : SAdeleRing ℚ ∅, f (Multiplicative.ofAdd x) =
      φ (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
        (x.1 Rat.infinitePlace)))
    (x : (SAdeleRing ℚ ∅)ˣ) :
    sLocalAdelicThetaOnClasses ℚ ∅ f (QuotientGroup.mk x) =
      φ (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
        (x.val.1 Rat.infinitePlace)) +
      φ (-(InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
        (x.val.1 Rat.infinitePlace))) := by
  have hU : (Units.map (RingHom.toMonoidHom (RingHom.comp (adeleProjection ℚ ∅)
      (Subring.subtype (integralAdelesOutside ℚ ∅)))))
      (Units.map (RingHom.toMonoidHom (integralAdeleDiagonal ℚ ∅)) (-1)) = -1 := by
    apply Units.ext
    change ((adeleProjection ℚ ∅).comp (integralAdelesOutside ℚ ∅).subtype)
      (integralAdeleDiagonal ℚ ∅
        (-1 : (Set.integer ((∅ : Finset V(ℚ)) : Set V(ℚ)) ℚ)ˣ).val) =
      (-1 : (SAdeleRing ℚ ∅)ˣ).val
    simp
  rw [sLocalAdelicThetaOnClasses_mk, sLocalAdelicTheta_apply]
  dsimp only
  rw [tsum_eq_sum (s := {1, -1}) (fun ξ hξ ↦ ?_)]
  · rw [Finset.sum_pair sec2bP_one_ne_neg_one]
    simp only [MonoidHom.comp_apply, hU, map_one, one_mul, hf]
    simp only [Units.val_neg, neg_mul, one_mul]
    rw [show ((-(x : SAdeleRing ℚ ∅)).1 Rat.infinitePlace) =
      -((x : SAdeleRing ℚ ∅).1 Rat.infinitePlace) from rfl, map_neg]
  · rcases sec2bP_units ξ with h | h <;> simp_all

private theorem sec2bP_normOne_trivial (h : (sIdeleQuotientNorm ℚ ∅).ker) : h = 1 := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
  apply Subtype.ext
  change (QuotientGroup.mk x : SIdeleQuotient ℚ ∅) = 1
  rw [sIdeleQuotient_mk_eq_one]
  have hn : ‖x.val.1 Rat.infinitePlace‖ = 1 := by
    rw [← sec2bP_norm]
    have h1 : sIdeleNorm ℚ ∅ x = 1 := hg
    rw [h1]
    simp
  rw [← sec2bP_abs] at hn
  rcases (abs_eq zero_le_one).mp hn with h1 | h1
  · refine ⟨1, ?_⟩
    simp only [map_one]
    apply Units.ext
    refine Prod.ext (funext fun w ↦ ?_) (Subsingleton.elim _ _)
    obtain rfl : w = Rat.infinitePlace := Subsingleton.elim _ _
    apply (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).injective
    exact h1.trans (map_one _).symm
  · refine ⟨-1, ?_⟩
    apply Units.ext
    change (x : SAdeleRing ℚ ∅) = ((adeleProjection ℚ ∅).comp (integralAdelesOutside ℚ ∅).subtype)
      (integralAdeleDiagonal ℚ ∅
        (-1 : (Set.integer ((∅ : Finset V(ℚ)) : Set V(ℚ)) ℚ)ˣ).val)
    simp only [Units.val_neg, Units.val_one, map_neg, map_one]
    refine Prod.ext (funext fun w ↦ ?_) (Subsingleton.elim _ _)
    obtain rfl : w = Rat.infinitePlace := Subsingleton.elim _ _
    apply (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).injective
    exact h1.trans ((map_neg _ _).trans (congrArg Neg.neg (map_one _))).symm

private theorem sec2bP_single {ι : Type*} [Unique ι] {M : ι → Type*} [∀ i, Zero (M i)]
    {d : DecidableEq ι} (v : M default) : @Pi.single ι M _ d (default : ι) v default = v := by
  let := d
  exact Pi.single_eq_same _ _

open scoped FourierTransform in
private theorem sec2bP_character (x y : SAdeleRing ℚ ∅) :
    (sAdeleStandardCharacter ℚ ∅ (x * y) : ℂ) =
      Real.fourierChar (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
        (x.1 Rat.infinitePlace) *
        InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
          (y.1 Rat.infinitePlace)) := by
  let : Unique (InfinitePlace ℚ) := ⟨⟨Rat.infinitePlace⟩, fun _ ↦ Subsingleton.elim _ _⟩
  unfold sAdeleStandardCharacter
  rw [Fintype.prod_unique, Finset.univ_eq_empty, Finset.prod_empty, mul_one,
    adeleStandardCharacter_rat, ratAdeleStandardCharacter_real _ rfl]
  rw [Real.fourierChar_apply']
  congr 3
  dsimp only
  exact (congrArg (InfinitePlace.Completion.extensionEmbeddingOfIsReal Rat.isReal_infinitePlace)
    (sec2bP_single (M := InfinitePlace.Completion) _)).trans
    (map_mul (InfinitePlace.Completion.extensionEmbeddingOfIsReal Rat.isReal_infinitePlace) _ _)

open scoped FourierTransform in
private theorem sec2bP_integral (G : Rat.infinitePlace.Completion → ℂ) :
    letI : MeasurableSpace Rat.infinitePlace.Completion := borel _
    ∫ x : SAdeleRing ℚ ∅, G (x.1 Rat.infinitePlace) ∂sAdditiveTamagawaMeasure ℚ ∅ =
      ∫ r : ℝ, G ((InfinitePlace.Completion.ringEquivRealOfIsReal
        Rat.isReal_infinitePlace).symm r) := by
  let (w : InfinitePlace ℚ) : MeasurableSpace w.Completion :=
    instMeasurableSpaceCompletion_riemannMasullo ℚ w
  let : MeasurableSpace (InfiniteAdeleRing ℚ) := instMeasurableSpaceInfiniteAdeleRing_riemannMasullo ℚ
  let (v : V(ℚ)) : MeasurableSpace (v.adicCompletion ℚ) :=
    instMeasurableSpaceAdicCompletionRingOfIntegers_riemannMasullo ℚ v
  let : Unique (InfinitePlace ℚ) := ⟨⟨Rat.infinitePlace⟩, fun _ ↦ Subsingleton.elim _ _⟩
  have : BorelSpace Rat.infinitePlace.Completion := ⟨rfl⟩
  let e : ℝ ≃ᵐ Rat.infinitePlace.Completion :=
    (InfinitePlace.Completion.isometryEquivRealOfIsReal
      Rat.isReal_infinitePlace).symm.toHomeomorph.toMeasurableEquiv
  have hν : infiniteLocalAdditiveTamagawaMeasure ℚ Rat.infinitePlace = (volume : Measure ℝ).map e := by
    rw [infiniteLocalAdditiveTamagawaMeasure, dite_eq_left Rat.isReal_infinitePlace]
    rfl
  have hσ : ∀ w : InfinitePlace ℚ, SigmaFinite (infiniteLocalAdditiveTamagawaMeasure ℚ w) := by
    intro w
    obtain rfl : w = Rat.infinitePlace := Subsingleton.elim _ _
    rw [hν]
    exact e.sigmaFinite_map
  have : @SFinite (InfiniteAdeleRing ℚ) (instMeasurableSpaceInfiniteAdeleRing_riemannMasullo ℚ)
      (Measure.pi (infiniteLocalAdditiveTamagawaMeasure ℚ)) :=
    (inferInstance : SFinite (Measure.pi (infiniteLocalAdditiveTamagawaMeasure ℚ)))
  unfold sAdditiveTamagawaMeasure
  rw [integral_fun_fst (f := fun a : InfiniteAdeleRing ℚ ↦ G (a Rat.infinitePlace))]
  rw [Measure.pi_of_empty (x := isEmptyElim)]
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  have hp := measurePreserving_piUnique (X := fun w : InfinitePlace ℚ ↦ w.Completion)
    (infiniteLocalAdditiveTamagawaMeasure ℚ)
  refine (hp.integral_comp' G).trans ?_
  refine (congrArg (fun μ : Measure Rat.infinitePlace.Completion ↦ ∫ y, G y ∂μ) hν).trans ?_
  rw [integral_map_equiv]
  rfl

open scoped FourierTransform in
private theorem sec2bP_fourier (φ : SchwartzMap ℝ ℂ)
    (f : SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅)))
    (hf : ∀ x : SAdeleRing ℚ ∅, f (Multiplicative.ofAdd x) =
      φ (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
        (x.1 Rat.infinitePlace)))
    (y : SAdeleRing ℚ ∅) :
    sAdeleSchwartzFourier f (Multiplicative.ofAdd y) =
      𝓕 φ (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
        (y.1 Rat.infinitePlace)) := by
  let : MeasurableSpace (SAdeleRing ℚ ∅) := instMeasurableSpaceSAdeleRing ℚ ∅
  change tamagawaFourier (sAdditiveTamagawaMeasure ℚ ∅) (sAdeleStandardCharacter ℚ ∅)
    (fun x ↦ f (Multiplicative.ofAdd x)) y = _
  unfold tamagawaFourier
  simp only [hf, sec2bP_character]
  rw [sec2bP_integral (fun z ↦ φ (InfinitePlace.Completion.ringEquivRealOfIsReal
    Rat.isReal_infinitePlace z) * star ((Real.fourierChar (InfinitePlace.Completion.ringEquivRealOfIsReal
    Rat.isReal_infinitePlace z * InfinitePlace.Completion.ringEquivRealOfIsReal
    Rat.isReal_infinitePlace (y.1 Rat.infinitePlace)) : ℂ)))]
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq]
  congr 1
  funext r
  rw [RingEquiv.apply_symm_apply, Circle.smul_def, smul_eq_mul, mul_comm]
  congr 1
  rw [AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]
  rfl

open LineDeriv in
private theorem sec2bP_lineDeriv_tsupport (f : SchwartzMap ℝ ℂ) :
    tsupport ⇑(∂_{(1 : ℝ)} f : SchwartzMap ℝ ℂ) ⊆ tsupport ⇑f := by
  apply closure_minimal ?_ (isClosed_tsupport _)
  intro x hx
  by_contra h
  apply hx
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv,
    image_eq_zero_of_notMem_tsupport (fun h' ↦ h (tsupport_fderiv_subset ℝ h'))]
  rfl

open scoped FourierTransform in
open LineDeriv in
private theorem sec2bP_test : ∃ φ : SchwartzMap ℝ ℂ,
    φ 0 = 0 ∧ (𝓕 φ : SchwartzMap ℝ ℂ) 0 = 0 ∧ HasCompactSupport ⇑(𝓕 φ : SchwartzMap ℝ ℂ) ∧
      tsupport ⇑(𝓕 φ : SchwartzMap ℝ ℂ) ⊆ Metric.closedBall 0 1 ∧
      ∃ c > 0, ∀ t : ℝ, |t| ≤ 1 → c * t ^ 2 ≤ ‖φ t + φ (-t)‖ := by
  let b : ContDiffBump (1 / 16 : ℝ) := ⟨1 / 64, 1 / 32, by norm_num, by norm_num⟩
  have hb_supp : HasCompactSupport (fun ξ : ℝ ↦ (b ξ : ℂ)) :=
    b.hasCompactSupport.comp_left Complex.ofReal_zero
  have hb_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun ξ : ℝ ↦ (b ξ : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp b.contDiff
  let ψ₀ : SchwartzMap ℝ ℂ := hb_supp.toSchwartzMap hb_smooth
  have hψ₀ (ξ : ℝ) : ψ₀ ξ = (b ξ : ℂ) := rfl
  let ψ : SchwartzMap ℝ ℂ := ∂_{(1 : ℝ)} (∂_{(1 : ℝ)} ψ₀)
  have hφ (t : ℝ) : (𝓕⁻ ψ) t = ((-(4 * Real.pi ^ 2 * t ^ 2) : ℝ) : ℂ) * (𝓕⁻ ψ₀) t := by
    have hg : (fun x : ℝ ↦ inner ℝ x (1 : ℝ)).HasTemperateGrowth := by fun_prop
    simp only [ψ, SchwartzMap.fourierInv_lineDerivOp_eq, smul_apply,
      SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul]
    simp only [inner, one_mul, star_trivial, RCLike.re_to_real, Complex.real_smul]
    push_cast
    linear_combination ((4 : ℂ) * Real.pi ^ 2 * t ^ 2 * (𝓕⁻ ψ₀) t) * Complex.I_sq
  have htsψ₀ : tsupport ⇑ψ₀ ⊆ Metric.closedBall (1 / 16) (1 / 32) := by
    rw [← b.tsupport_eq]
    exact tsupport_comp_subset Complex.ofReal_zero _
  have htsψ : tsupport ⇑ψ ⊆ Metric.closedBall (1 / 16) (1 / 32) :=
    (sec2bP_lineDeriv_tsupport _).trans ((sec2bP_lineDeriv_tsupport _).trans htsψ₀)
  have hF : 𝓕 (𝓕⁻ ψ) = ψ := FourierTransform.fourier_fourierInv_eq ψ
  refine ⟨𝓕⁻ ψ, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hφ]
    simp
  · rw [hF]
    refine image_eq_zero_of_notMem_tsupport fun h ↦ ?_
    have h' := htsψ h
    rw [Metric.mem_closedBall, Real.dist_eq] at h'
    norm_num [abs_le] at h'
  · rw [hF]
    exact (isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _) htsψ
  · rw [hF]
    refine htsψ.trans (Metric.closedBall_subset_closedBall' ?_)
    norm_num
  · have hint (t : ℝ) : Integrable (fun ξ : ℝ ↦ 𝐞 (inner ℝ ξ t) • ψ₀ ξ) := by
      refine ψ₀.integrable.norm.mono' (by fun_prop) (ae_of_all _ fun ξ ↦ ?_)
      rw [Circle.smul_def, norm_smul, Circle.norm_coe, one_mul]
    have hsum (t : ℝ) : ((𝓕⁻ ψ₀) t + (𝓕⁻ ψ₀) (-t)).re =
        ∫ ξ, 2 * Real.cos (2 * Real.pi * (ξ * t)) * b ξ := by
      rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq, Real.fourierInv_eq,
        ← integral_add (hint t) (hint (-t))]
      refine (integral_re ((hint t).add (hint (-t)))).symm.trans ?_
      congr 1
      funext ξ
      simp only [Circle.smul_def, hψ₀, Real.fourierChar_apply, inner, star_trivial, RCLike.re_to_real]
      simp only [Pi.add_apply, smul_eq_mul, RCLike.re_to_complex, Complex.add_re,
        Complex.re_mul_ofReal, Complex.exp_ofReal_mul_I_re]
      rw [show -t * ξ = -(t * ξ) by ring, mul_neg, Real.cos_neg, mul_comm ξ t]
      ring
    have hb_int : 0 < ∫ ξ, b ξ := b.integral_pos
    refine ⟨4 * Real.pi ^ 2 * ∫ ξ, b ξ, by positivity, fun t ht ↦ ?_⟩
    have hle : ∫ ξ, b ξ ≤ ∫ ξ, 2 * Real.cos (2 * Real.pi * (ξ * t)) * b ξ := by
      refine integral_mono b.integrable ?_ fun ξ ↦ ?_
      · exact (b.integrable.const_mul 2).mono'
          (Continuous.aestronglyMeasurable (by have := b.continuous; fun_prop))
          (ae_of_all _ fun ξ ↦ by
            rw [norm_mul, norm_mul, Real.norm_of_nonneg (b.nonneg' ξ), Real.norm_two,
              Real.norm_eq_abs]
            have := Real.abs_cos_le_one (2 * Real.pi * (ξ * t))
            have := b.nonneg' ξ
            calc 2 * |Real.cos (2 * Real.pi * (ξ * t))| * b ξ ≤ 2 * 1 * b ξ := by gcongr
              _ = 2 * b ξ := by ring)
      · by_cases hξ : b ξ = 0
        · simp [hξ]
        have hmem : ξ ∈ Metric.ball (1 / 16 : ℝ) (1 / 32) := by
          rw [← b.support_eq]; exact hξ
        rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hmem
        have hx : |2 * Real.pi * (ξ * t)| ≤ 2 * 3.15 * (3 / 32) := by
          rw [abs_mul, abs_mul, abs_mul, abs_two, abs_of_pos Real.pi_pos]
          have h1 : |ξ| ≤ 3 / 32 := by rw [abs_le]; constructor <;> linarith
          have := Real.pi_lt_d2
          have h2 : |ξ| * |t| ≤ 3 / 32 := by
            calc |ξ| * |t| ≤ 3 / 32 * 1 := by gcongr
              _ = 3 / 32 := by ring
          have h3 : 2 * Real.pi * (|ξ| * |t|) ≤ 2 * 3.15 * (3 / 32) := by
            gcongr
          exact h3
        have hc := Real.one_sub_sq_div_two_le_cos (x := 2 * Real.pi * (ξ * t))
        have hsq : (2 * Real.pi * (ξ * t)) ^ 2 ≤ (2 * 3.15 * (3 / 32)) ^ 2 := by
          rw [← sq_abs]; gcongr
        have hcos : 1 / 2 ≤ Real.cos (2 * Real.pi * (ξ * t)) := by norm_num at hsq; linarith
        have h2c : (1 : ℝ) ≤ 2 * Real.cos (2 * Real.pi * (ξ * t)) := by linarith
        have h4 := mul_le_mul_of_nonneg_right h2c (b.nonneg' ξ)
        rwa [one_mul] at h4
    have heq : (𝓕⁻ ψ) t + (𝓕⁻ ψ) (-t) =
        (((-(4 * Real.pi ^ 2 * t ^ 2)) : ℝ) : ℂ) * ((𝓕⁻ ψ₀) t + (𝓕⁻ ψ₀) (-t)) := by
      rw [hφ, hφ]; push_cast; ring
    rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg,
      abs_of_nonneg (by positivity)]
    calc 4 * Real.pi ^ 2 * (∫ ξ, b ξ) * t ^ 2
        ≤ 4 * Real.pi ^ 2 * t ^ 2 * ((𝓕⁻ ψ₀) t + (𝓕⁻ ψ₀) (-t)).re := by
          rw [hsum]
          have : 0 ≤ 4 * Real.pi ^ 2 * t ^ 2 := by positivity
          calc 4 * Real.pi ^ 2 * (∫ ξ, b ξ) * t ^ 2 = 4 * Real.pi ^ 2 * t ^ 2 * (∫ ξ, b ξ) := by
                ring
            _ ≤ _ := mul_le_mul_of_nonneg_left hle this
      _ ≤ 4 * Real.pi ^ 2 * t ^ 2 * ‖(𝓕⁻ ψ₀) t + (𝓕⁻ ψ₀) (-t)‖ := by
          gcongr; exact Complex.re_le_norm _
    exact le_rfl

/-- The trivial character restricted to the norm-one classes is unramified outside `S = ∅`. -/
private theorem sec2bP_unramified :
    NormOneCharacterUnramifiedOutside ((1 : PontryaginDual C𝔽(ℚ)).comp
      (⟨(ideleClassNorm ℚ).ker.subtype, continuous_subtype_val⟩ : C₁(ℚ) →ₜ* C𝔽(ℚ))) ∅ :=
  ⟨⟨1, (mem_unramifiedOutside_iff ℚ ∅ 1).mpr (fun _ _ _ ↦ rfl)⟩, fun _ ↦ rfl⟩

/-- Over ℚ with `S = ∅` the S-integers are a principal ideal ring. -/
private theorem sec2bP_pic :
    Subsingleton (CommRing.Pic (((∅ : Finset V(ℚ)) : Set V(ℚ)).integer ℚ)) := by
  rw [Finset.coe_empty, integer_empty]
  let e := (Algebra.botEquivOfInjective (IsFractionRing.injective (𝓞 ℚ) ℚ)).toRingEquiv
  let i := Rat.ringOfIntegersEquiv.symm.trans e.symm
  let := IsPrincipalIdealRing.of_surjective i i.surjective
  infer_instance

/-- The norm-one quotient over ℚ with `S = ∅` is a point of positive finite mass. -/
private theorem sec2bP_mass_pos : 0 < (sLocalNormOneQuotientMeasure ℚ ∅).real univ := by
  have := (sLocalNormOneQuotientMeasure_normProduct (F := ℚ) (S := ∅)).1
  have : Subsingleton (sIdeleQuotientNorm ℚ ∅).ker :=
    ⟨fun a b ↦ (sec2bP_normOne_trivial a).trans (sec2bP_normOne_trivial b).symm⟩
  have : Finite (sIdeleQuotientNorm ℚ ∅).ker := Finite.of_subsingleton
  have : CompactSpace (sIdeleQuotientNorm ℚ ∅).ker := Finite.compactSpace
  exact ENNReal.toReal_pos (isOpen_univ.measure_pos _ ⟨1, trivial⟩).ne'
    isCompact_univ.measure_lt_top.ne

/-- Over ℚ with `S = ∅` the homogeneous theta function is the theta function on classes
times the total norm-one mass. -/
private theorem sec2bP_homTheta (ω : PontryaginDual (sIdeleQuotientNorm ℚ ∅).ker)
    (f : SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅))) (g : SIdeleQuotient ℚ ∅) :
    sLocalHomogeneousAdelicThetaLinearMap ℚ ∅ ω f g =
      ((sLocalNormOneQuotientMeasure ℚ ∅).real univ : ℂ) * sLocalAdelicThetaOnClasses ℚ ∅ f g := by
  rw [sLocalHomogeneousAdelicThetaLinearMap_apply,
    integral_congr_ae (g := fun _ ↦ sLocalAdelicThetaOnClasses ℚ ∅ f g) (ae_of_all _ fun h ↦ ?_)]
  · rw [integral_const, Complex.real_smul]
  · have := sec2bP_normOne_trivial h
    subst this
    simp

/-- The test of the counterexample weighted by the inverse square of the norm stays
bounded below on classes of norm less than one. -/
private theorem sec2bP_lower (ω : PontryaginDual (sIdeleQuotientNorm ℚ ∅).ker)
    (φ : SchwartzMap ℝ ℂ) (f : SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅)))
    (hf : ∀ x : SAdeleRing ℚ ∅, f (Multiplicative.ofAdd x) =
      φ (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
        (x.1 Rat.infinitePlace)))
    (c : ℝ) (hlow : ∀ t : ℝ, |t| ≤ 1 → c * t ^ 2 ≤ ‖φ t + φ (-t)‖) (x : (SAdeleRing ℚ ∅)ˣ)
    (hx : ((sIdeleQuotientNorm ℚ ∅ (QuotientGroup.mk x) : ℝ≥0) : ℝ) < 1) :
    (sLocalNormOneQuotientMeasure ℚ ∅).real univ * c ≤
      ‖localTheta(ℚ, ∅, -2, ω, f) (QuotientGroup.mk x)‖ := by
  set t := InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
    (x.val.1 Rat.infinitePlace) with ht
  have hr : ((sIdeleQuotientNorm ℚ ∅ (QuotientGroup.mk x) : ℝ≥0) : ℝ) = |t| := by
    rw [ht, sec2bP_abs]; exact sec2bP_norm x
  have hpos : 0 < |t| := by
    rw [← hr]; exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))
  have hν := sec2bP_mass_pos
  have h1 := hlow t (by rw [← hr]; exact hx.le)
  change ‖((((sIdeleQuotientNorm ℚ ∅ (QuotientGroup.mk x) : ℝ≥0) : ℝ) ^ (-2 : ℝ) : ℝ) : ℂ) *
    sLocalHomogeneousAdelicThetaLinearMap ℚ ∅ ω f (QuotientGroup.mk x)‖ ≥ _
  rw [sec2bP_homTheta, sec2bP_thetaClasses f φ hf x, norm_mul, norm_mul, Complex.norm_real,
    Complex.norm_real, Real.norm_of_nonneg hν.le, hr,
    Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg t) _),
    Real.rpow_neg (abs_nonneg t), Real.rpow_two, ← ht]
  have ht2 : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
  have hne : |t| ^ 2 ≠ 0 := by positivity
  calc (sLocalNormOneQuotientMeasure ℚ ∅).real univ * c
      = (|t| ^ 2)⁻¹ * ((sLocalNormOneQuotientMeasure ℚ ∅).real univ * (c * t ^ 2)) := by
        rw [ht2]; field_simp
    _ ≤ _ := by gcongr

/-- A left-invariant measure on a group with a continuous surjection onto the positive reals
gives infinite mass to the elements of norm less than one. -/
private theorem sec2bP_measure {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsOpenPosMeasure]
    (N : G →* ℝ≥0ˣ) (hN : Continuous N) (hs : Function.Surjective N) :
    μ {g | ((N g : ℝ≥0) : ℝ) < 1} = ⊤ := by
  obtain ⟨t, ht⟩ := hs (Units.mk0 (2 : ℝ≥0) two_ne_zero)
  obtain ⟨g₀, hg₀⟩ := hs (Units.mk0 (3 / 4 : ℝ≥0) (by norm_num))
  have hcont : Continuous fun g ↦ ((N g : ℝ≥0) : ℝ) :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp hN)
  let A : Set G := {g | 1 / 2 < ((N g : ℝ≥0) : ℝ) ∧ ((N g : ℝ≥0) : ℝ) < 1}
  have hAo : IsOpen A :=
    (isOpen_lt continuous_const hcont).inter (isOpen_lt hcont continuous_const)
  have hg₀A : g₀ ∈ A := by
    simp only [A, mem_ofPred_eq, hg₀, Units.val_mk0, NNReal.coe_div, NNReal.coe_ofNat]
    norm_num
  have hA0 : μ A ≠ 0 := (hAo.measure_pos μ ⟨g₀, hg₀A⟩).ne'
  let B (k : ℕ) : Set G := (fun g ↦ t ^ k * g) ⁻¹' A
  have hB (k : ℕ) (g : G) : g ∈ B k ↔
      1 / 2 < 2 ^ k * ((N g : ℝ≥0) : ℝ) ∧ 2 ^ k * ((N g : ℝ≥0) : ℝ) < 1 := by
    show (1 / 2 < ((N (t ^ k * g) : ℝ≥0) : ℝ) ∧ ((N (t ^ k * g) : ℝ≥0) : ℝ) < 1) ↔ _
    rw [map_mul, map_pow, ht]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0, NNReal.coe_mul,
      NNReal.coe_pow, NNReal.coe_ofNat]
  have hmeas (k : ℕ) : μ (B k) = μ A := measure_preimage_mul μ (t ^ k) A
  have hdisj : Pairwise (Function.onFun Disjoint B) := by
    have key (k l : ℕ) (h : k < l) (g : G) (h1 : g ∈ B k) (h2 : g ∈ B l) : False := by
      rw [hB] at h1 h2
      have h2l : (2 : ℝ) * 2 ^ k ≤ 2 ^ l := by
        calc (2 : ℝ) * 2 ^ k = 2 ^ (k + 1) := by ring
          _ ≤ 2 ^ l := pow_le_pow_right₀ (by norm_num) h
      have hr : 0 ≤ ((N g : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
      nlinarith
    intro k l hkl
    rw [Function.onFun, Set.disjoint_left]
    intro g h1 h2
    rcases lt_or_gt_of_ne hkl with h | h
    · exact key k l h g h1 h2
    · exact key l k h g h2 h1
  have hsub : (⋃ k, B k) ⊆ {g | ((N g : ℝ≥0) : ℝ) < 1} := by
    intro g hg
    obtain ⟨k, hk⟩ := mem_iUnion.mp hg
    rw [hB] at hk
    have h1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    have hr : 0 ≤ ((N g : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
    simp only [mem_ofPred_eq]
    nlinarith
  refine eq_top_mono (measure_mono hsub) ?_
  rw [measure_iUnion hdisj (fun k ↦ (measurable_const_mul (t ^ k)) hAo.measurableSet)]
  simp only [hmeas]
  exact ENNReal.tsum_const_eq_top_of_ne_zero hA0

/-- The weighted theta function of the counterexample is not square integrable. -/
private theorem sec2bP_not_memLp (ω : PontryaginDual (sIdeleQuotientNorm ℚ ∅).ker)
    (φ : SchwartzMap ℝ ℂ) (f : SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅)))
    (hf : ∀ x : SAdeleRing ℚ ∅, f (Multiplicative.ofAdd x) =
      φ (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
        (x.1 Rat.infinitePlace)))
    (c : ℝ) (hc : 0 < c) (hlow : ∀ t : ℝ, |t| ≤ 1 → c * t ^ 2 ≤ ‖φ t + φ (-t)‖) :
    ¬ MemLp (localTheta(ℚ, ∅, -2, ω, f)) 2 (localMeasure(ℚ, ∅, 0)) := by
  intro hm
  have hμ : localMeasure(ℚ, ∅, 0) = μₛ(ℚ, ∅) := by
    conv_rhs => rw [← withDensity_one (μ := μₛ(ℚ, ∅))]
    congr 1
    funext g
    simp [intervalSobolevDensity]
  rw [hμ] at hm
  let Θ := localTheta(ℚ, ∅, -2, ω, f)
  have hint : Integrable (fun g ↦ ‖Θ g‖ ^ (2 : ℝ)) μₛ(ℚ, ∅) := by
    simpa using hm.integrable_norm_rpow two_ne_zero ENNReal.ofNat_ne_top
  have : BorelSpace (SIdeleQuotient ℚ ∅) := ⟨rfl⟩
  have hW := sLocalQuotientTamagawaMeasure_isWeil (F := ℚ) (S := ∅)
  have : (sLocalQuotientTamagawaMeasure ℚ ∅).IsHaarMeasure := hW.1
  obtain ⟨σ, hσ⟩ := sIdeleQuotientNorm_exists_section (F := ℚ) (S := ∅)
  have hNc : Continuous (sIdeleQuotientNorm ℚ ∅) :=
    (isProperMap_sIdeleQuotientNorm ℚ ∅).continuous
  have hB := sec2bP_measure (sLocalQuotientTamagawaMeasure ℚ ∅)
    (sIdeleQuotientNorm ℚ ∅) hNc hσ.surjective
  let B := {g : SIdeleQuotient ℚ ∅ | ((sIdeleQuotientNorm ℚ ∅ g : ℝ≥0) : ℝ) < 1}
  have hBm : MeasurableSet B :=
    (isOpen_lt (NNReal.continuous_coe.comp (Units.continuous_val.comp hNc))
      continuous_const).measurableSet
  set K := (sLocalNormOneQuotientMeasure ℚ ∅).real univ * c with hK
  have hKpos : 0 < K := mul_pos sec2bP_mass_pos hc
  have hlow' : ∀ g ∈ B, ENNReal.ofReal (K ^ (2 : ℝ)) ≤ ‖‖Θ g‖ ^ (2 : ℝ)‖ₑ := by
    intro g hg
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
    have h1 := sec2bP_lower ω φ f hf c hlow x hg
    rw [Real.eNorm_eq_ofReal (by positivity)]
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hKpos.le h1 (by norm_num))
  have hfin : (∫⁻ g, ‖‖Θ g‖ ^ (2 : ℝ)‖ₑ ∂μₛ(ℚ, ∅)) < ⊤ := hint.hasFiniteIntegral
  have hge : ⊤ ≤ ∫⁻ g, ‖‖Θ g‖ ^ (2 : ℝ)‖ₑ ∂μₛ(ℚ, ∅) :=
    calc (⊤ : ENNReal) = ENNReal.ofReal (K ^ (2 : ℝ)) * μₛ(ℚ, ∅) B := by
          rw [hB, ENNReal.mul_top (by simp; positivity)]
      _ = ∫⁻ _ in B, ENNReal.ofReal (K ^ (2 : ℝ)) ∂μₛ(ℚ, ∅) := (setLIntegral_const B _).symm
      _ ≤ ∫⁻ g in B, ‖‖Θ g‖ ^ (2 : ℝ)‖ₑ ∂μₛ(ℚ, ∅) := setLIntegral_mono' hBm hlow'
      _ ≤ _ := setLIntegral_le_lintegral B _
  exact absurd (lt_of_le_of_lt hge hfin) (lt_irrefl _)

/-- The transition from `∅` to itself is the identity. -/
private theorem sec2bP_transition (f : SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅))) :
    sAdeleSchwartzTransition ℚ (le_refl (∅ : Finset V(ℚ))) f = f := by
  refine Subtype.ext (funext fun x ↦ ?_)
  change sAdeleSchwartzTransition ℚ (le_refl (∅ : Finset V(ℚ))) f
    (Multiplicative.ofAdd (Multiplicative.toAdd x)) = f x
  rw [sAdeleSchwartzTransition_apply, ite_eq_left (fun w ↦ absurd w.2 (Finset.notMem_empty _))]
  rfl

/-- The test of the counterexample has compact Fourier support inside the unit ball
at the real place. -/
private theorem sec2bP_inBand (φ : SchwartzMap ℝ ℂ)
    (hts : tsupport ⇑(FourierTransform.fourier φ : SchwartzMap ℝ ℂ) ⊆ Metric.closedBall 0 1)
    (f : SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅)))
    (hf : ∀ x : SAdeleRing ℚ ∅, f (Multiplicative.ofAdd x) =
      φ (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
        (x.1 Rat.infinitePlace))) :
    HasCompactSupport (sAdeleSchwartzFourier f).val ∧
      tsupport (sAdeleSchwartzFourier f).val ⊆
        Multiplicative.toAdd ⁻¹' {x : SAdeleRing ℚ ∅ | ‖x.1 Rat.infinitePlace‖ ≤ 1} := by
  let r : Multiplicative (SAdeleRing ℚ ∅) → ℝ := fun y ↦
    InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
      ((Multiplicative.toAdd y).1 Rat.infinitePlace)
  have hr : Continuous r :=
    (InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace).continuous.comp
      ((continuous_apply _).comp (continuous_fst.comp continuous_toAdd))
  have hsub : tsupport (sAdeleSchwartzFourier f).val ⊆
      r ⁻¹' tsupport ⇑(FourierTransform.fourier φ : SchwartzMap ℝ ℂ) := by
    refine closure_minimal (fun y hy ↦ ?_) ((isClosed_tsupport _).preimage hr)
    refine subset_tsupport _ ?_
    rw [mem_support] at hy ⊢
    rwa [← sec2bP_fourier φ f hf]
  have hsub' : tsupport (sAdeleSchwartzFourier f).val ⊆
      Multiplicative.toAdd ⁻¹' {x : SAdeleRing ℚ ∅ | ‖x.1 Rat.infinitePlace‖ ≤ 1} := by
    intro y hy
    have h := hts (hsub hy)
    rw [Metric.mem_closedBall, dist_zero_right] at h
    change ‖(Multiplicative.toAdd y).1 Rat.infinitePlace‖ ≤ 1
    rwa [← sec2bP_abs, ← Real.norm_eq_abs]
  refine ⟨?_, hsub'⟩
  refine (isCompact_sLocalPWBox (F := ℚ) (S := ∅) 1).of_isClosed_subset (isClosed_tsupport _)
    (fun y hy ↦ ⟨fun w ↦ ?_, fun v ↦ absurd v.2 (Finset.notMem_empty _)⟩)
  obtain rfl : w = Rat.infinitePlace := Subsingleton.elim _ _
  rw [Rat.isReal_infinitePlace.mult_eq_one, pow_one]
  exact hsub' hy

/-- The test of the counterexample lies in the polar subspace. -/
private theorem sec2bP_polar (φ : SchwartzMap ℝ ℂ) (hφ0 : φ 0 = 0)
    (hFφ0 : (FourierTransform.fourier φ : SchwartzMap ℝ ℂ) 0 = 0)
    (f : SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅)))
    (hf : ∀ x : SAdeleRing ℚ ∅, f (Multiplicative.ofAdd x) =
      φ (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
        (x.1 Rat.infinitePlace))) :
    sAdeleSchwartzTransition ℚ (le_refl (∅ : Finset V(ℚ))) f ∈ sAdelePolarSubspace ℚ ∅ := by
  rw [sec2bP_transition, mem_sAdelePolarSubspace, sec2bP_fourier φ f hf, hf]
  exact ⟨by rw [show ((0 : SAdeleRing ℚ ∅).1 Rat.infinitePlace) = 0 from rfl, map_zero, hφ0],
    by rw [show ((0 : SAdeleRing ℚ ∅).1 Rat.infinitePlace) = 0 from rfl, map_zero]; exact hFφ0⟩

/-- Paper: Definition 11.2.1.1(1) and (11.2.1.1), pp. 487–488.
The absolute local closure presupposes that each weighted class in the §7.3.2 level is in
the ambient Sobolev space, for every real twist and every nonnegative degree.
Deviation: Express membership on representatives of all classes in the §7.3.2 level. -/
def Printed.sLocalAbsolutePWSobolev_memLp : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C𝔽(F)) (S : Finset V(F))
    (hω : NormOneCharacterUnramifiedOutside
      (χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁(F) →ₜ* C𝔽(F))) S),
    Subsingleton (CommRing.Pic ((S : Set V(F)).integer F)) →
    ∀ (Λ a s : ℝ), 0 < Λ → 0 ≤ s →
      let ω := sLocalNormOneCharacter S _ hω
      ∀ f, qₛ(F, S, ω) f ∈ sLocalAbsolutePW (S := S) (T := S) le_rfl Λ
          (sAdelePolarSubspace F S) ω →
        MemLp (localTheta(F, S, a, ω, f)) 2 (localMeasure(F, S, s))

/-- Paper: Definition 11.2.1.1(1) and (11.2.1.1), pp. 487–488.
Take F = ℚ, S = {∞, 2}, χ = 1, Λ = 1 and a = s = 0.
Let H be the inverse Fourier transform of a nonzero nonnegative even smooth bump
supported where 1/8 < |ξ| < 1/4. The test is (H(u) - H(2u)) times the 2-adic
integer indicator. Both zero moments vanish. At the class of (t, 1), the local
theta series telescopes to 2 H(t), up to the positive norm-one Haar mass.
Since H(0) > 0, its squared integral against dt/t diverges at zero. -/
theorem Printed.sLocalAbsolutePWSobolev_memLp_false :
    ¬ Printed.sLocalAbsolutePWSobolev_memLp := by
  intro h
  obtain ⟨E, hE⟩ := ratTrivialHomogeneousTheta_quotient_realEquiv
  obtain ⟨φ, hφ0, hFφ0, -, hts, c, hc, hlow⟩ := sec2bP_test
  refine sec2bP_not_memLp _ φ (E φ) (hE φ) c hc hlow
    (h ℚ 1 ∅ sec2bP_unramified sec2bP_pic 1 (-2) 0 one_pos le_rfl (E φ) ?_)
  have hb := sec2bP_inBand φ hts (E φ) (hE φ)
  rw [← sec2bP_transition (E φ)]
  refine sLocalAbsolutePW_mk_mem _ _ _ _ (E φ) ⟨hb.1, hb.2.trans fun y hy ↦
    ⟨fun w ↦ ?_, fun v ↦ absurd v.2 (Finset.notMem_empty _)⟩⟩ (sec2bP_polar φ hφ0 hFφ0 _ (hE φ))
  obtain rfl : w = Rat.infinitePlace := Subsingleton.elim _ _
  rw [Rat.isReal_infinitePlace.mult_eq_one, pow_one]
  exact hy

/-- Paper: Definition 11.2.1.3(1) and (11.2.1.6), pp. 488–489.
The invariant local closure presupposes Sobolev membership of the weighted
classes in the §7.3.2 level for every real twist and every nonnegative degree.
Deviation: Express membership on representatives of all classes in the §7.3.2 level. -/
def Printed.sLocalInvariantPWSobolev_memLp : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C𝔽(F)) (S : Finset V(F))
    (hω : NormOneCharacterUnramifiedOutside
      (χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁(F) →ₜ* C𝔽(F))) S),
    Subsingleton (CommRing.Pic ((S : Set V(F)).integer F)) →
    ∀ (Λ a s : ℝ), 0 < Λ → 0 ≤ s →
      let ω := sLocalNormOneCharacter S _ hω
      ∀ f, qₛ(F, S, ω) f ∈ sLocalInvariantPW (S := S) (T := S) le_rfl Λ
          (sAdelePolarSubspace F S) ω →
        MemLp (localTheta(F, S, a, ω, f)) 2 (localMeasure(F, S, s))

/-- Paper: Definition 11.2.1.3(1) and (11.2.1.6), pp. 488–489.
Use ℚ, S = {∞, 2}, χ = 1, Λ = 1 and a = s = 0. The test
(H(u) - H(2u)) times the 2-adic integer indicator from the absolute-level
counterexample also lies in the invariant region. Its Fourier support satisfies
|ξ∞| ≤ 1 and |ξ₂|₂ ≤ 1. The local theta is proportional to 2 H(t) and is outside L²(dt/t). -/
theorem Printed.sLocalInvariantPWSobolev_memLp_false :
    ¬ Printed.sLocalInvariantPWSobolev_memLp := by
  intro h
  obtain ⟨E, hE⟩ := ratTrivialHomogeneousTheta_quotient_realEquiv
  obtain ⟨φ, hφ0, hFφ0, -, hts, c, hc, hlow⟩ := sec2bP_test
  refine sec2bP_not_memLp _ φ (E φ) (hE φ) c hc hlow
    (h ℚ 1 ∅ sec2bP_unramified sec2bP_pic 1 (-2) 0 one_pos le_rfl (E φ) ?_)
  have hb := sec2bP_inBand φ hts (E φ) (hE φ)
  rw [← sec2bP_transition (E φ)]
  refine sLocalInvariantPW_mk_mem _ _ _ _ (E φ) ⟨hb.1, hb.2.trans fun y hy ↦ ?_⟩
    (sec2bP_polar φ hφ0 hFφ0 _ (hE φ))
  let : Unique (InfinitePlace ℚ) := ⟨⟨Rat.infinitePlace⟩, fun _ ↦ Subsingleton.elim _ _⟩
  change (∏ w : InfinitePlace ℚ, ‖(Multiplicative.toAdd y).1 w‖ ^ w.mult) *
    (∏ v : (∅ : Finset V(ℚ)), ‖(Multiplicative.toAdd y).2 v‖) ≤ 1
  rw [Fintype.prod_unique, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
  change ‖(Multiplicative.toAdd y).1 Rat.infinitePlace‖ ^ Rat.infinitePlace.mult ≤ 1
  rw [Rat.isReal_infinitePlace.mult_eq_one, pow_one]
  exact hy

local notation "GeoIsotype(" F ", " hs ", " ω ")" =>
  actionIsotype ((hardySobolevTranslation (ideleClassTamagawaMeasure F) (m𝔽(F))
    (-(0 : ℝ)) 0 _ (neg_nonpos.mpr (le_rfl (a := (0 : ℝ)))) hs).comp
    (ideleClassNorm F).ker.subtype) ω

local notation "cutoffConv(" F ", " hs ", " ω ", " a ", " hρ ", " φ ")" =>
  ((GeoIsotype(F, hs, ω)).orthogonalProjectionOnto.comp
    ((geometricTruncatedConvolution (F := F) a (le_rfl (a := (0 : ℝ))) hs hρ φ).comp
      (GeoIsotype(F, hs, ω)).subtypeL))
local notation "aboveOne(" F ", " φ ")" =>
  (tsupport (φ : BruhatCompactSupport C𝔽(F)).val ⊆ {g | 1 ≤ ((m𝔽(F) g).val : ℝ)})
local notation "productTraceClass(" T ", " P ")" =>
  (⟨(T).val * (P), mul_mem_nuclearEndomorphisms_right (P) (T)⟩ : nuclearEndomorphisms _)

/-- Paper: Theorem 11.2.1.2(2) and (11.2.1.4), p. 488.
For every fixed cutoff, the trace-norm limit of absolute condensation is asserted
to be the uncompressed cutoff geometric convolution.
Deviation: Use the global absolute projector specified by the declared codomain
in (11.2.1.3), with the Fourier box bound X = Λ. -/
def Printed.absolutePWCondensation_traceNorm_tendsto : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C𝔽(F))
    (S : Finset V(F)) (a s : ℝ) (hs : 0 ≤ s),
    let ω := χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁(F) →ₜ* C𝔽(F))
    letI : CompleteSpace ↥(GeoIsotype(F, hs, ω)) :=
      (instClosedSpectralIsotypeSec2 (F := F) (neg_nonpos.mpr (le_rfl (a := (0 : ℝ))))
        hs ω).completeSpace_coe
    NormOneCharacterUnramifiedOutside ω S →
    Subsingleton (CommRing.Pic ((S : Set V(F)).integer F)) →
    ∀ (φ : BruhatCompactSupport C𝔽(F)), aboveOne(F, φ) →
      ∀ (R ε : ℝ) (ρ : C𝔽(F) → ℝ) (hρ : IsModulatedCutoff (m𝔽(F)) R ε ρ),
        ∃ T : nuclearEndomorphisms GeoIsotype(F, hs, ω),
          T.val = cutoffConv(F, hs, ω, a, hρ, φ) ∧
            Tendsto (fun Λ ↦ traceNorm
              (productTraceClass(T, absolutePWProjection (F := F) (S := S) hs a ω Λ) - T))
              atTop (𝓝 0)

/-- A trace-norm limit of right products determines the operator value on a pointwise limit. -/
private theorem absolutePWCondensation_traceNorm_tendsto_false_apply
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : nuclearEndomorphisms H) (P : ℝ → H →L[ℂ] H) (u v : H)
    (hP : Tendsto (fun Λ ↦ P Λ u) atTop (𝓝 v))
    (hT : Tendsto (fun Λ ↦ traceNorm
      ((⟨T.val * P Λ, mul_mem_nuclearEndomorphisms_right (P Λ) T⟩ : nuclearEndomorphisms H) - T))
      atTop (𝓝 0)) : T.val v = T.val u := by
  by_cases hu : u = 0
  · subst u
    simp only [map_zero] at hP ⊢
    rw [tendsto_nhds_unique hP tendsto_const_nhds, map_zero]
  let f := innerSL ℂ u
  let A := f.smulRight u
  let D (Λ : ℝ) : nuclearEndomorphisms H :=
    ⟨T.val * P Λ, mul_mem_nuclearEndomorphisms_right (P Λ) T⟩ - T
  have hbound (Λ : ℝ) : ‖f‖ * ‖T.val (P Λ u) - T.val u‖ ≤ ‖A‖ * traceNorm (D Λ) := by
    have hmul : (D Λ).val * A = f.smulRight (T.val (P Λ u) - T.val u) := by
      ext1 x
      simp [D, A, smul_sub]
    rw [← traceNorm_smulRight f (T.val (P Λ u) - T.val u)]
    have hprod : (⟨(D Λ).val * A, mul_mem_nuclearEndomorphisms_right A (D Λ)⟩ :
        nuclearEndomorphisms H) =
        ⟨f.smulRight (T.val (P Λ u) - T.val u), smulRight_mem_nuclearEndomorphisms _ _⟩ :=
      Subtype.ext hmul
    rw [← hprod]
    exact traceNorm_mul_right_le A (D Λ)
  have hLeft : Tendsto (fun Λ ↦ ‖f‖ * ‖T.val (P Λ u) - T.val u‖) atTop
      (𝓝 (‖f‖ * ‖T.val v - T.val u‖)) :=
    tendsto_const_nhds.mul (((T.val.continuous.tendsto v).comp hP).sub tendsto_const_nhds).norm
  have hRight : Tendsto (fun Λ ↦ ‖A‖ * traceNorm (D Λ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hT
  have hle := le_of_tendsto_of_tendsto' hLeft hRight hbound
  have hf : 0 < ‖f‖ := by simpa only [f, innerSL_apply_norm, norm_pos_iff] using hu
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm (nonpos_of_mul_nonpos_right hle hf) (norm_nonneg _)))

open scoped nonZeroDivisors in
/-- The rational integers have trivial Picard group. -/
private theorem rational_empty_picTrivial :
    Subsingleton (CommRing.Pic (((∅ : Finset V(ℚ)) : Set V(ℚ)).integer ℚ)) := by
  rw [Finset.coe_empty, integer_empty]
  let e := (Algebra.botEquivOfInjective (IsFractionRing.injective (𝓞 ℚ) ℚ)).toRingEquiv
  let i := Rat.ringOfIntegersEquiv.symm.trans e.symm
  let := IsPrincipalIdealRing.of_surjective i i.surjective
  infer_instance

/-- The restriction of the trivial rational character is unramified everywhere. -/
private theorem rational_one_unramifiedOutside_empty :
    NormOneCharacterUnramifiedOutside
      ((1 : PontryaginDual C𝔽(ℚ)).comp
        (⟨(ideleClassNorm ℚ).ker.subtype, continuous_subtype_val⟩ : C₁(ℚ) →ₜ* C𝔽(ℚ))) ∅ := by
  refine ⟨⟨1, (mem_unramifiedOutside_iff ℚ ∅ 1).mpr (fun _ _ _ ↦ rfl)⟩, fun _ ↦ rfl⟩

/-- A fixed-cutoff geometric convolution is nonzero on a vector orthogonal to theta
in the trivial rational isotype. Use a critical-line ordinate γ and the log-norm
vector `exp(-iγx)/(1+x²)`. Pair its translates with the theta vector from
`(3u² - 2πu⁴) exp(-πu²)` and the finite integer indicators. The pairing is analytic,
and the Cauchy kernel has a nonvanishing Fourier multiplier, so it is nonzero at some
positive translation. A bump near that point and a large cutoff preserve the
nonzero geometric output. -/
private theorem rational_cutoffConv_ne_zero_of_geometricProjection_eq_zero :
    let hs : (0 : ℝ) ≤ 2 := by norm_num
    let ω := (1 : PontryaginDual C𝔽(ℚ)).comp
      (⟨(ideleClassNorm ℚ).ker.subtype, continuous_subtype_val⟩ : C₁(ℚ) →ₜ* C𝔽(ℚ))
    letI : CompleteSpace ↥(GeoIsotype(ℚ, hs, ω)) :=
      (instClosedSpectralIsotypeSec2 (F := ℚ) (neg_nonpos.mpr (le_rfl (a := (0 : ℝ))))
        hs ω).completeSpace_coe
    ∃ (φ : BruhatCompactSupport C𝔽(ℚ)), aboveOne(ℚ, φ) ∧
      ∃ (R ε : ℝ) (ρ : C𝔽(ℚ) → ℝ) (hρ : IsModulatedCutoff (m𝔽(ℚ)) R ε ρ)
          (u : GeoIsotype(ℚ, hs, ω)),
        ((GeoIsotype(ℚ, hs, ω)).orthogonalProjectionOnto.comp
          ((geometricProjection (F := ℚ) (1 / 2) (le_rfl (a := (0 : ℝ))) hs).comp
            (GeoIsotype(ℚ, hs, ω)).subtypeL)) u = 0 ∧
        ((GeoIsotype(ℚ, hs, ω)).orthogonalProjectionOnto.comp
          ((geometricTruncatedConvolution (F := ℚ) (1 / 2) (le_rfl (a := (0 : ℝ))) hs hρ φ).comp
            (GeoIsotype(ℚ, hs, ω)).subtypeL)) u ≠ 0 := by sorry

/-- Paper: Theorem 11.2.1.2(2) and (11.2.1.4), p. 488.
On the trivial rational component with no finite places, a = 1/2 and s = 2, let γ be
the first positive ordinate of a critical-line zeta zero. The vector
v(x) = exp(-iγx)/(1+x²) is orthogonal to theta by the Mellin zero.
Use the nonzero half-weighted theta profile G of
(3u² - 2πu⁴) exp(-πu²) with integer indicators at finite places.
The inner products of the translates v(x-t) with G cannot vanish for all t > 0.
Up to a phase they convolve G(x) exp(iγx)(1+x²) with 1/(1+x²).
That convolution is real analytic and its Fourier multiplier is nowhere zero.
A nonnegative test bump near a positive t with nonzero inner product still pairs
nontrivially, and a sufficiently large fixed symmetric cutoff preserves a nonzero
part of its geometric projection. Every right PW projection kills v. -/
theorem Printed.absolutePWCondensation_traceNorm_tendsto_false :
    ¬ Printed.absolutePWCondensation_traceNorm_tendsto := by
  intro h
  have hs : (0 : ℝ) ≤ 2 := by norm_num
  let ω := (1 : PontryaginDual C𝔽(ℚ)).comp
    (⟨(ideleClassNorm ℚ).ker.subtype, continuous_subtype_val⟩ : C₁(ℚ) →ₜ* C𝔽(ℚ))
  let H := ↥(GeoIsotype(ℚ, hs, ω))
  let : CompleteSpace H :=
    (instClosedSpectralIsotypeSec2 (F := ℚ) (neg_nonpos.mpr (le_rfl (a := (0 : ℝ))))
      hs ω).completeSpace_coe
  let P (Λ : ℝ) : H →L[ℂ] H := absolutePWProjection (F := ℚ) (S := ∅) hs (1 / 2) ω Λ
  obtain ⟨φ, hφ, R, ε, ρ, hρ, u, hu, hcut⟩ :=
    rational_cutoffConv_ne_zero_of_geometricProjection_eq_zero
  obtain ⟨T, hT, hlim⟩ := h ℚ 1 ∅ (1 / 2) 2 hs
    rational_one_unramifiedOutside_empty rational_empty_picTrivial φ hφ R ε ρ hρ
  have hstrong := absolutePWProjection_tendsto (F := ℚ) (S := ∅) hs (1 / 2) ω
    rational_one_unramifiedOutside_empty rational_empty_picTrivial u
  have hzero : Tendsto (fun Λ ↦ P Λ u) atTop (𝓝 0) :=
    (congrArg (fun v : H ↦ Tendsto (fun Λ ↦ P Λ u) atTop (𝓝 v)) hu).mp hstrong
  have heq : T.val 0 = T.val u :=
    absolutePWCondensation_traceNorm_tendsto_false_apply H T P u 0 hzero hlim
  exact hcut ((congrArg (fun A : H →L[ℂ] H ↦ A u) hT).symm.trans
    (heq.symm.trans (map_zero T.val)))

/-- Paper: Theorem 11.2.1.4(2) and (11.2.1.9), p. 489.
For every fixed cutoff, the trace-norm limit of invariant condensation is asserted
to be the uncompressed cutoff geometric convolution. -/
def Printed.invariantPWCondensation_traceNorm_tendsto : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C𝔽(F))
    (S : Finset V(F)) (a s : ℝ) (hs : 0 ≤ s),
    let ω := χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁(F) →ₜ* C𝔽(F))
    letI : CompleteSpace ↥(GeoIsotype(F, hs, ω)) :=
      (instClosedSpectralIsotypeSec2 (F := F) (neg_nonpos.mpr (le_rfl (a := (0 : ℝ))))
        hs ω).completeSpace_coe
    NormOneCharacterUnramifiedOutside ω S →
    Subsingleton (CommRing.Pic ((S : Set V(F)).integer F)) →
    ∀ (φ : BruhatCompactSupport C𝔽(F)), aboveOne(F, φ) →
      ∀ (R ε : ℝ) (ρ : C𝔽(F) → ℝ) (hρ : IsModulatedCutoff (m𝔽(F)) R ε ρ),
        ∃ T : nuclearEndomorphisms GeoIsotype(F, hs, ω),
          T.val = cutoffConv(F, hs, ω, a, hρ, φ) ∧
            Tendsto (fun Λ ↦ traceNorm
              (productTraceClass(T, invariantPWProjection (F := F) (S := S) hs a ω Λ) - T))
              atTop (𝓝 0)

/-- Paper: Theorem 11.2.1.4(2) and (11.2.1.9), p. 489.
For ℚ with no finite places, the trivial character, a = 1/2 and s = 2, the product
region is the same interval as the absolute box. The zeta-zero vector, positive test bump and
fixed symmetric cutoff of the absolute counterexample also refute this limit. -/
theorem Printed.invariantPWCondensation_traceNorm_tendsto_false :
    ¬ Printed.invariantPWCondensation_traceNorm_tendsto := by
  intro h
  have hs : (0 : ℝ) ≤ 2 := by norm_num
  let ω := (1 : PontryaginDual C𝔽(ℚ)).comp
    (⟨(ideleClassNorm ℚ).ker.subtype, continuous_subtype_val⟩ : C₁(ℚ) →ₜ* C𝔽(ℚ))
  let H := ↥(GeoIsotype(ℚ, hs, ω))
  let : CompleteSpace H :=
    (instClosedSpectralIsotypeSec2 (F := ℚ) (neg_nonpos.mpr (le_rfl (a := (0 : ℝ))))
      hs ω).completeSpace_coe
  let P (Λ : ℝ) : H →L[ℂ] H := invariantPWProjection (F := ℚ) (S := ∅) hs (1 / 2) ω Λ
  obtain ⟨φ, hφ, R, ε, ρ, hρ, u, hu, hcut⟩ :=
    rational_cutoffConv_ne_zero_of_geometricProjection_eq_zero
  obtain ⟨T, hT, hlim⟩ := h ℚ 1 ∅ (1 / 2) 2 hs
    rational_one_unramifiedOutside_empty rational_empty_picTrivial φ hφ R ε ρ hρ
  have hstrong := invariantPWProjection_tendsto (F := ℚ) (S := ∅) hs (1 / 2) ω
    rational_one_unramifiedOutside_empty rational_empty_picTrivial u
  have hzero : Tendsto (fun Λ ↦ P Λ u) atTop (𝓝 0) :=
    (congrArg (fun v : H ↦ Tendsto (fun Λ ↦ P Λ u) atTop (𝓝 v)) hu).mp hstrong
  have heq : T.val 0 = T.val u :=
    absolutePWCondensation_traceNorm_tendsto_false_apply H T P u 0 hzero hlim
  exact hcut ((congrArg (fun A : H →L[ℂ] H ↦ A u) hT).symm.trans
    (heq.symm.trans (map_zero T.val)))

/-- Paper: Theorem 11.2.1.2(2) and (11.2.1.5), p. 488.
The traces at fixed cutoff are asserted to converge to the trace of the
uncompressed cutoff geometric convolution.
Deviation: Interpret the absolute projector by the PW codomain of (11.2.1.3)
and take the box parameter X = Λ, as for the operator assertion. -/
def Printed.absolutePWCondensation_trace_tendsto : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C𝔽(F))
    (S : Finset V(F)) (a s : ℝ) (hs : 0 ≤ s),
    let ω := χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁(F) →ₜ* C𝔽(F))
    letI : CompleteSpace ↥(GeoIsotype(F, hs, ω)) :=
      (instClosedSpectralIsotypeSec2 (F := F) (neg_nonpos.mpr (le_rfl (a := (0 : ℝ))))
        hs ω).completeSpace_coe
    NormOneCharacterUnramifiedOutside ω S →
    Subsingleton (CommRing.Pic ((S : Set V(F)).integer F)) →
    ∀ (φ : BruhatCompactSupport C𝔽(F)), aboveOne(F, φ) →
      ∀ (R ε : ℝ) (ρ : C𝔽(F) → ℝ) (hρ : IsModulatedCutoff (m𝔽(F)) R ε ρ),
        ∃ T : nuclearEndomorphisms GeoIsotype(F, hs, ω),
          T.val = cutoffConv(F, hs, ω, a, hρ, φ) ∧
            Tendsto (fun Λ ↦ hilbertTrace
              (productTraceClass(T, absolutePWProjection (F := F) (S := S) hs a ω Λ)))
              atTop (𝓝 (hilbertTrace T))

/-- Paper: Theorem 11.2.1.2(2) and (11.2.1.5), p. 488.
In the rational trivial isotype take S = {∞}, a = 1/2 and s = 2.
In Fourier H¹ let E project onto the complement of the functions vanishing
at the critical-line ordinates. A smooth frequency multiplier supported
around a single ordinate γ and equal to one there induces a rank-one
idempotent in the quotient. A fixed large symmetric cutoff leaves its trace
near one. Translate the inverse transform far to the right, compensate by
the phase at γ and cut the Schwartz tails to obtain a positive-time test.
The spatially cut translated operator on E tends to zero in trace norm,
while its quotient action retains the rank-one trace. The two fixed-cutoff
traces thus differ. See the rational calculation in the PR review. -/
theorem Printed.absolutePWCondensation_trace_tendsto_false :
    ¬ Printed.absolutePWCondensation_trace_tendsto := by sorry

/-- Paper: Theorem 11.2.1.4(2) and (11.2.1.10), p. 489.
The traces at fixed cutoff are asserted to converge to the trace of the
uncompressed cutoff geometric convolution. -/
def Printed.invariantPWCondensation_trace_tendsto : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C𝔽(F))
    (S : Finset V(F)) (a s : ℝ) (hs : 0 ≤ s),
    let ω := χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁(F) →ₜ* C𝔽(F))
    letI : CompleteSpace ↥(GeoIsotype(F, hs, ω)) :=
      (instClosedSpectralIsotypeSec2 (F := F) (neg_nonpos.mpr (le_rfl (a := (0 : ℝ))))
        hs ω).completeSpace_coe
    NormOneCharacterUnramifiedOutside ω S →
    Subsingleton (CommRing.Pic ((S : Set V(F)).integer F)) →
    ∀ (φ : BruhatCompactSupport C𝔽(F)), aboveOne(F, φ) →
      ∀ (R ε : ℝ) (ρ : C𝔽(F) → ℝ) (hρ : IsModulatedCutoff (m𝔽(F)) R ε ρ),
        ∃ T : nuclearEndomorphisms GeoIsotype(F, hs, ω),
          T.val = cutoffConv(F, hs, ω, a, hρ, φ) ∧
            Tendsto (fun Λ ↦ hilbertTrace
              (productTraceClass(T, invariantPWProjection (F := F) (S := S) hs a ω Λ)))
              atTop (𝓝 (hilbertTrace T))

/-- Paper: Theorem 11.2.1.4(2) and (11.2.1.10), p. 489.
For the rational data of the absolute scalar counterexample the
only place in S is real. The product region equals the box at every level,
so both scalar limits have the same discrepancy. -/
theorem Printed.invariantPWCondensation_trace_tendsto_false :
    ¬ Printed.invariantPWCondensation_trace_tendsto := by sorry

local notation "theta0(" F ", " hs ")" => globalThetaSobolev F 0 (le_rfl (a := (0 : ℝ))) hs
local notation "Sₚ(" F ", " p ")" => (finite_nuclearityPlacesAbove (F := F) p).toFinset

/-- Paper: Paragraph before (11.2.2.1), p. 489.
The raw principal-value range defining the prime quotient is asserted to be
closed in the zero-line theta isotype.
Deviation: Use the equivalent ambient isotypic model at zero twist. -/
def Printed.primeOrbitalSobolevDenominator_closed : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C𝔽(F))
    (p : HeightOneSpectrum (𝓞 ℚ)),
    (∀ v ∈ Sₚ(F, p), (ideleClassNormTwist χ 0).IsUnramifiedAt v) →
    ∀ (s : ℝ) (hs : 0 ≤ s),
      let ω := χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁(F) →ₜ* C𝔽(F))
      IsClosed {x : Wω(F, hs, ω) | ∃ y : theta0(F, hs), y.val ∈ Wω(F, hs, ω) ∧
        (globalThetaSobolevPrincipalValue F (Sₚ(F, p)) 0 hs y).val = x.val}

/-- Paper: Paragraph before (11.2.2.1), p. 489.
Take ℚ, the trivial character, p = 2 and s = 2. In log norm the principal
value is the difference with a shift by log 2, up to translation sign.
It is injective on weighted L² because every periodic vector there vanishes.
For any nonzero smooth bump ψ supported in (1, 2), the normalized difference
of ψ(x/R) tends to zero as R grows. The map is therefore not bounded below,
so its range is not closed. -/
theorem Printed.primeOrbitalSobolevDenominator_closed_false :
    ¬ Printed.primeOrbitalSobolevDenominator_closed := by sorry

end RiemannMasullo
