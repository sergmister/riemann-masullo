module

public import RiemannMasullo.Ch10_TraceSpectral.Sec1
public import RiemannMasullo.Ch03_IdelicZeta.RatEmptyFourier
import RiemannMasullo.Ch11_ShellStructure.Sec1b
import Mathlib.Analysis.Distribution.SchwartzSpace.CompactSupport

/-! # The rational radial generators of the geometric theta space -/

public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped FourierTransform NumberField.AdeleRing NNReal SchwartzMap

namespace RiemannMasullo.StripNuclearity

set_option quotPrecheck false

local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ
local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "Bℚ" => SchwartzBruhat (Multiplicative 𝔸)
local notation "B∞" => SchwartzBruhat (Multiplicative (InfiniteAdeleRing ℚ))
local notation "realCoord" => InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
local notation "K" => (homogeneousAdelicThetaLinearMap ℚ 1).ker
local notation "𝓢ℝ" => SchwartzMap ℝ ℂ

private theorem real_arch_test_mem (f : 𝓢ℝ) :
    (fun x : Multiplicative (InfiniteAdeleRing ℚ) ↦ f (realCoord (x.toAdd Rat.infinitePlace))) ∈
      schwartzBruhatSubmodule (Multiplicative (InfiniteAdeleRing ℚ)) := by
  classical
  let : Unique {w : InfinitePlace ℚ // w.IsReal} :=
    uniqueOfSubsingleton ⟨Rat.infinitePlace, Rat.isReal_infinitePlace⟩
  let : IsEmpty {w : InfinitePlace ℚ // w.IsComplex} :=
    ⟨fun w ↦ (InfinitePlace.not_isReal_iff_isComplex.mpr w.property) (IsTotallyReal.isReal w.val)⟩
  let e := (ContinuousLinearEquiv.prodUnique ℝ
      ({w : InfinitePlace ℚ // w.IsReal} → ℝ) ({w : InfinitePlace ℚ // w.IsComplex} → ℂ)).trans
    (ContinuousLinearEquiv.piUnique ℝ (fun _ : {w : InfinitePlace ℚ // w.IsReal} ↦ ℝ))
  apply (mem_archimedeanSchwartzBruhat_iff (F := ℚ)
    (fun x : InfiniteAdeleRing ℚ ↦ f (realCoord (x Rat.infinitePlace)))).2
  exact ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e f, fun _ ↦ rfl⟩

private def realArchTest (f : 𝓢ℝ) : B∞ :=
  ⟨_, real_arch_test_mem f⟩

private def realEmptyTest (f : 𝓢ℝ) :=
  sLocalStandardThetaTensor (F := ℚ) (S := ∅) 1 (realArchTest f)

private theorem realEmptyTest_apply (f : 𝓢ℝ) (x : SAdeleRing ℚ ∅) :
    realEmptyTest f (Multiplicative.ofAdd x) = f (realCoord (x.1 Rat.infinitePlace)) := by
  rw [realEmptyTest, sLocalStandardThetaTensor_apply, Fintype.prod_empty, mul_one]
  rfl

/-- A real Schwartz function at infinity, with the integer indicator at each finite place. -/
def ratStandardAdelicTest (f : 𝓢ℝ) : Bℚ :=
  sAdeleSchwartzToGlobal ℚ ∅ (realEmptyTest f)

open Classical in
/-- The finite components restrict the argument to integral finite adeles. -/
theorem ratStandardAdelicTest_apply (f : 𝓢ℝ) (x : 𝔸) :
    ratStandardAdelicTest f (Multiplicative.ofAdd x) =
      if ∀ v : HeightOneSpectrum (𝓞 ℚ), x.2 v ∈ v.adicCompletionIntegers ℚ then
        f (realCoord (x.1 Rat.infinitePlace)) else 0 := by
  rw [ratStandardAdelicTest, sAdeleSchwartzToGlobal_apply, realEmptyTest_apply]
  simp [adeleProjection]
  rfl

/-- Both global polar conditions are exactly the two real conditions for this insertion. -/
theorem ratStandardAdelicTest_polar_iff (f : 𝓢ℝ) :
    ratStandardAdelicTest f ∈ adelePolarSubspace ℚ ↔ f 0 = 0 ∧ 𝓕 f 0 = 0 := by
  rw [ratStandardAdelicTest, sAdeleSchwartzToGlobal_mem_polarSubspace_iff, realEmptyTest_apply,
    sAdeleSchwartzFourier_ratEmpty_apply f (realEmptyTest f) (realEmptyTest_apply f)]
  change (f (realCoord 0) = 0 ∧ 𝓕 f (realCoord 0) = 0) ↔ _
  rw [map_zero]

private def ratThetaClass := ratTrivialHomogeneousTheta_quotient.choose

private theorem ratThetaClass_eq (f : 𝓢ℝ) :
    ratThetaClass f = (K).mkQ (ratStandardAdelicTest f) :=
  ratTrivialHomogeneousTheta_quotient.choose_spec.2 f (realArchTest f) (fun _ ↦ rfl)

private theorem standard_class_polar_iff (f : 𝓢ℝ) :
    ratThetaClass f ∈ globalPolarFreeThetaSubmodule (F := ℚ) 1 ↔
      f 0 = 0 ∧ 𝓕 f 0 = 0 := by
  obtain ⟨R, hR, hK, _⟩ := globalConverse_normTwist_exact (F := ℚ)
  let : MeasurableSpace Cℚ := borel _
  let μ := normOneIdeleClassTamagawaMeasure ℚ
  let : CompactSpace (ideleClassNorm ℚ).ker := (ideleClassGroup_finiteness ℚ).2.1
  let : μ.IsHaarMeasure := (multiplicativeTamagawaMeasures_existsUnique ℚ).exists.choose_spec.2.2.2.1
  have hm : ((μ univ).toReal : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (measureReal_univ_pos (μ := μ)).ne'
  rw [← ratStandardAdelicTest_polar_iff, ← hK, LinearMap.mem_ker, ratThetaClass_eq]
  change R ((K).mkQ (ratStandardAdelicTest f)) = 0 ↔ _
  rw [hR, mem_adelePolarSubspace, Prod.mk_eq_zero]
  dsimp only [μ] at hm
  simp only [mul_eq_zero, hm, neg_eq_zero, false_or]

private def reflect (f : 𝓢ℝ) : 𝓢ℝ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (LinearIsometryEquiv.neg ℝ (E := ℝ)) f

private theorem reflect_apply (f : 𝓢ℝ) (x : ℝ) : reflect f x = f (-x) := rfl

private theorem reflect_test_apply (f : 𝓢ℝ) (x : 𝔸) :
    ratStandardAdelicTest (reflect f) (Multiplicative.ofAdd x) =
      ratStandardAdelicTest f (Multiplicative.ofAdd (-x)) := by
  classical
  rw [ratStandardAdelicTest_apply, ratStandardAdelicTest_apply]
  have hi (v : HeightOneSpectrum (𝓞 ℚ)) : (-x).2 v = -(x.2 v) := rfl
  have hr : (-x).1 Rat.infinitePlace = -(x.1 Rat.infinitePlace) := rfl
  simp only [hi, neg_mem_iff, hr, map_neg, reflect_apply]

private theorem ratThetaClass_reflect (f : 𝓢ℝ) : ratThetaClass (reflect f) = ratThetaClass f := by
  have ht : adelicTheta (ratStandardAdelicTest (reflect f)) = adelicTheta (ratStandardAdelicTest f) := by
    ext x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    rw [adelicTheta_mk, adelicTheta_mk]
    have hmul (u : ℚˣ) : (Equiv.mulLeft (-1 : ℚˣ)) u = (-1 : ℚˣ) * u := rfl
    simpa only [reflect_test_apply, hmul, Units.val_mul, Units.val_neg, Units.val_one, neg_one_mul,
      map_neg, neg_mul, one_mul] using (Equiv.mulLeft (-1 : ℚˣ)).tsum_eq
        (fun t : ℚˣ ↦ ratStandardAdelicTest f
          (Multiplicative.ofAdd (algebraMap ℚ 𝔸 (t : ℚ) * g.val)))
  rw [ratThetaClass_eq, ratThetaClass_eq]
  apply (Submodule.Quotient.eq K).2
  rw [LinearMap.mem_ker, map_sub, sub_eq_zero, homogeneousAdelicThetaLinearMap_apply,
    homogeneousAdelicThetaLinearMap_apply]
  ext g
  simp only [homogeneousAdelicTheta, ht]

private def evenPart (f : 𝓢ℝ) : 𝓢ℝ := (2 : ℂ)⁻¹ • (f + reflect f)

private theorem evenPart_even (f : 𝓢ℝ) : Function.Even (evenPart f : ℝ → ℂ) := by
  intro x
  change (2 : ℂ)⁻¹ * (f (-x) + f (- -x)) = (2 : ℂ)⁻¹ * (f x + f (-x))
  rw [neg_neg, add_comm]

private theorem ratThetaClass_evenPart (f : 𝓢ℝ) : ratThetaClass (evenPart f) = ratThetaClass f := by
  rw [evenPart, map_smul, map_add, ratThetaClass_reflect, ← two_smul ℂ, smul_smul]
  norm_num

private def bandSubmodule : Submodule ℂ 𝓢ℝ where
  carrier := {f | HasCompactSupport ((𝓕 f : 𝓢ℝ) : ℝ → ℂ)}
  zero_mem' := by simpa using (HasCompactSupport.zero : HasCompactSupport (0 : ℝ → ℂ))
  add_mem' {f g} hf hg := by
    change HasCompactSupport ((𝓕 (f + g) : 𝓢ℝ) : ℝ → ℂ)
    rw [FourierTransform.fourier_add]
    exact hf.add hg
  smul_mem' c f hf := by
    change HasCompactSupport ((𝓕 (c • f) : 𝓢ℝ) : ℝ → ℂ)
    rw [FourierTransform.fourier_smul]
    exact HasCompactSupport.smul_left (f := fun _ : ℝ ↦ c) hf

private theorem bandSubmodule_dense : Dense (bandSubmodule : Set 𝓢ℝ) := by
  let F := (FourierTransform.fourierCLE ℂ 𝓢ℝ).symm
  apply (F.surjective.denseRange.dense_image F.continuous SchwartzMap.dense_hasCompactSupport).mono
  rintro _ ⟨f, hf, rfl⟩
  change HasCompactSupport ((𝓕 (𝓕⁻ f) : 𝓢ℝ) : ℝ → ℂ)
  rw [FourierTransform.fourier_fourierInv_eq]
  exact hf

private theorem evenPart_mem_band (f : 𝓢ℝ) (hf : f ∈ bandSubmodule) :
    evenPart f ∈ bandSubmodule := by
  apply bandSubmodule.smul_mem
  apply bandSubmodule.add_mem hf
  have h (g : 𝓢ℝ) : reflect (𝓕 g) = 𝓕⁻ g := rfl
  have hr : reflect f = 𝓕⁻ (𝓕⁻ f) := by
    rw [← h (𝓕⁻ f), FourierTransform.fourier_fourierInv_eq]
  change HasCompactSupport ((𝓕 (reflect f) : 𝓢ℝ) : ℝ → ℂ)
  rw [hr, FourierTransform.fourier_fourierInv_eq, ← h]
  exact HasCompactSupport.comp_homeomorph (show HasCompactSupport ((𝓕 f : 𝓢ℝ) : ℝ → ℂ) from hf)
    (Homeomorph.neg ℝ)

/-- Every polar-free rational trivial-character theta class can be approximated in its own
quotient topology by an even real test with compact Fourier support and both polar values zero. -/
theorem rat_even_bandlimited_homogeneous_theta_dense :
    Dense {y : globalPolarFreeThetaSubmodule (F := ℚ) 1 | ∃ f : 𝓢ℝ,
      Function.Even (f : ℝ → ℂ) ∧ HasCompactSupport ((𝓕 f : 𝓢ℝ) : ℝ → ℂ) ∧
      f 0 = 0 ∧ 𝓕 f 0 = 0 ∧ y.val = (K).mkQ (ratStandardAdelicTest f)} := by
  obtain ⟨R, _, hK, hRo, _⟩ := globalConverse_normTwist_exact (F := ℚ)
  have hq : Surjective ratThetaClass := ratTrivialHomogeneousTheta_quotient.choose_spec.1.surjective
  let p := R.comp ratThetaClass
  let r := p.comp bandSubmodule.subtypeL
  have hp : Surjective p := hRo.surjective.comp hq
  have hd : Dense (Set.range r) := by
    have h := hp.denseRange.dense_image p.continuous bandSubmodule_dense
    apply h.mono
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨⟨f, hf⟩, rfl⟩
  have hrt : r.range = ⊤ := by
    apply SetLike.coe_set_eq.mp
    exact (r.range.isClosed_of_finiteDimensional.dense_iff).mp hd
  obtain ⟨j, hj⟩ := r.exists_rightInverse_of_surjective hrt
  have hsec (v : ℂ × ℂ) : p (j v).val = v :=
    DFunLike.congr_fun hj v
  let proj := ContinuousLinearMap.id ℂ 𝓢ℝ - bandSubmodule.subtypeL.comp (j.comp p)
  have hz (f : 𝓢ℝ) : ratThetaClass (proj f) ∈ globalPolarFreeThetaSubmodule (F := ℚ) 1 := by
    rw [← hK]
    change p (f - (j (p f)).val) = 0
    rw [map_sub, hsec, sub_self]
  let lift := (ratThetaClass.comp proj).codRestrict _ hz
  have hl : Surjective lift := by
    rintro ⟨y, hy⟩
    obtain ⟨f, hf⟩ := hq y
    have hf' : p f = 0 := by
      change R (ratThetaClass f) = 0
      rw [show ratThetaClass f = y from hf]
      change y ∈ R.ker
      rwa [hK]
    refine ⟨f, Subtype.ext ?_⟩
    change ratThetaClass (f - (j (p f)).val) = y
    simpa only [hf', map_zero, ZeroMemClass.coe_zero, sub_zero] using hf
  apply (hl.denseRange.dense_image lift.continuous bandSubmodule_dense).mono
  rintro _ ⟨f, hf, rfl⟩
  have hb : proj f ∈ bandSubmodule := bandSubmodule.sub_mem hf (j (p f)).property
  have he := ratThetaClass_evenPart (proj f)
  have hm := (standard_class_polar_iff (evenPart (proj f))).mp (he.symm ▸ hz f)
  exact ⟨evenPart (proj f), evenPart_even _, evenPart_mem_band _ hb, hm.1, hm.2,
    he.symm.trans (ratThetaClass_eq _)⟩

local instance : MeasurableSpace Cℚ := borel _
local notation "mℚ" => (⟨ideleClassNorm ℚ, (isProperMap_ideleClassNorm ℚ).continuous⟩ : Cℚ →ₜ* ℝ≥0ˣ)
local notation "H₁(" a ", " h ", " s ")" =>
  actionIsotype ((exists_globalThetaSobolevAction (F := ℚ) a h s).choose.comp (ideleClassNorm ℚ).ker.subtype) 1

/-- In the actual geometric trivial isotype, the weighted homogeneous theta functions of even
polar-free real tests with compactly supported Fourier transform are dense at every interval and
Sobolev order allowed by Chapter 10. The finite components are integer indicators. -/
theorem rat_even_bandlimited_globalThetaSobolev_dense (a : ℝ) {α β s : ℝ} (hI : α ≤ β)
    (hs : 0 ≤ s) :
    Dense {y : H₁(a, hI, hs) | ∃ f : 𝓢ℝ,
      Function.Even (f : ℝ → ℂ) ∧ HasCompactSupport ((𝓕 f : 𝓢ℝ) : ℝ → ℂ) ∧
      f 0 = 0 ∧ 𝓕 f 0 = 0 ∧
      (y.val.val : Cℚ → ℂ) =ᵐ[ideleClassTamagawaMeasure ℚ]
        modulationWeight mℚ a (homogeneousAdelicTheta 1 (ratStandardAdelicTest f))} := by
  let j := (exists_globalHomogeneousThetaSobolevInclusion (F := ℚ) (a := a) hI hs 1).choose
  have hj : DenseRange j := (exists_globalHomogeneousThetaSobolevInclusion (F := ℚ) (a := a) hI hs 1).choose_spec.2.1
  have hrepr := (exists_globalHomogeneousThetaSobolevInclusion (F := ℚ) (a := a) hI hs 1).choose_spec.2.2
  apply (hj.dense_image j.continuous rat_even_bandlimited_homogeneous_theta_dense).mono
  rintro _ ⟨y, ⟨f, he, hb, hf, hF, hy⟩, rfl⟩
  have hmem := (ratStandardAdelicTest_polar_iff f).2 ⟨hf, hF⟩
  exact ⟨f, he, hb, hf, hF, (hrepr ⟨ratStandardAdelicTest f, hmem⟩ y hy).2⟩

end RiemannMasullo.StripNuclearity
