module

public import RiemannMasullo.Ch05_ThetaZSpaces.Sec3a
public import RiemannMasullo.AppD_SchwartzBruhat.Sec3b
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import all RiemannMasullo.AppD_SchwartzBruhat.Sec1b
import all RiemannMasullo.AppD_SchwartzBruhat.Sec2b
import all RiemannMasullo.AppD_SchwartzBruhat.Sec3a
import all RiemannMasullo.AppD_SchwartzBruhat.Sec3a_part2
import all RiemannMasullo.AppD_SchwartzBruhat.Sec1c
import all RiemannMasullo.AppD_SchwartzBruhat.Sec1b
import all RiemannMasullo.AppD_SchwartzBruhat.Sec3a_part2
import all RiemannMasullo.Ch02_AdelicTheta.Sec1
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Meromorphic.RCLike
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Topology.Algebra.IsOpenUnits
import RiemannMasullo.ForMathlib.Analysis.Normed.Field.ProperSpace

/-! # Extensions by zero and holomorphic S-idelic zeta functions

Masullo, §5.3.3–5.3.4, pp. 249–265.
-/

@[expose] public noncomputable section

open Bornology Filter Function IsDedekindDomain MeasureTheory NumberField Set TopologicalSpace Topology
open scoped ContDiff Distributions FourierTransform NNReal NumberField.AdeleRing SchwartzMap TensorProduct Topology

namespace RiemannMasullo

set_option quotPrecheck false

section PuncturedLine

-- TODO(paper-gap): The logarithmic argument substitution leaves the exponent interval I fixed.

/-- Paper: Example 5.3.3.1, p. 249.
Logarithmic coordinates give a linear homeomorphism between the weighted spaces on
the real line and the positive multiplicative reals.
Deviation: The exponents are unchanged under the logarithmic change of the argument. -/
theorem positiveRealExponentialDecay_log_equiv (I : Set ℝ) (hI : OrdConnected I)
    (hne : I.Nonempty) :
    ∃ e : PositiveRealExponentialDecay I ≃L[ℂ]
        ModulatedExponentialDecay (ContinuousMonoidHom.id ℝ≥0ˣ) I,
      ∀ f t, (e f).val t = f.val (Real.log (t.val : ℝ)) :=
  identityModulationExponentialDecay_equiv I hI hne

local notation "normPower(" K ", " d ")" =>
  (Units.map nnNormHom.toMonoidHom ^ d : Kˣ →* ℝ≥0ˣ)

/-- Paper: Proposition 5.3.3.2, p. 249.
Natural powers of the norm on the multiplicative group are continuous as
maps to the positive reals. -/
theorem continuous_archimedeanUnitModulation (K : Type*) [NormedField K] (d : ℕ) :
    Continuous (normPower(K, d)) := by
  rw [Units.continuous_iff]
  have h1 : Continuous fun x : Kˣ ↦ (‖(x : K)‖₊ : ℝ≥0) ^ d :=
    (continuous_nnnorm.comp Units.continuous_val).pow d
  have h2 : Continuous fun x : Kˣ ↦ (‖((x⁻¹ : Kˣ) : K)‖₊ : ℝ≥0) ^ d :=
    (continuous_nnnorm.comp Units.continuous_val |>.comp continuous_inv).pow d
  refine ⟨?_, ?_⟩
  · convert h1 using 2 with x
    simp
  · convert h2 using 2 with x
    simp [map_inv₀]

/-- Paper: Proposition 5.3.3.2, p. 249.
The real multiplicative group uses the norm, and the complex multiplicative group
uses the squared norm. -/
def archimedeanUnitModulation (K : Type*) [NormedField K] (d : ℕ) : Kˣ →ₜ* ℝ≥0ˣ :=
  ⟨normPower(K, d), continuous_archimedeanUnitModulation K d⟩

/-- Paper: Proposition 5.3.3.2, p. 249.
At a nonzero argument the module evaluates to the indicated power of its norm. -/
theorem archimedeanUnitModulation_apply (K : Type*) [NormedField K] (d : ℕ) (u : Kˣ) :
    ((archimedeanUnitModulation K d u).val : ℝ) = ‖(u : K)‖ ^ d := by
  show (((((Units.map nnNormHom.toMonoidHom ^ d : Kˣ →* ℝ≥0ˣ) u) : ℝ≥0ˣ).val : ℝ≥0) : ℝ) = _
  rw [MonoidHom.pow_apply]
  simp [nnNormHom]

local notation "𝓔(" K ", " d ", " I ")" => ModulatedExponentialDecay (archimedeanUnitModulation K d) I
local notation "punctured(" K ")" => (⟨{0}ᶜ, isClosed_singleton.isOpen_compl⟩ : Opens K)
local notation "𝒟₀(" K ")" => 𝓓(punctured(K), ℂ)
local notation "zeroExtension(" f ")" =>
  (fun x ↦ if hx : x ≠ 0 then f (Units.mk0 x hx) else (0 : ℂ))
local notation "complexCoordinate(" conjugate ")" =>
  (fun z : ℂ ↦ if conjugate then star z else z)
local notation "wirtinger(" conjugate ")" =>
  (if conjugate then wirtingerConjDeriv else wirtingerDeriv)

/-- Paper: §5.3.3, p. 249.
Restriction gives a continuous linear injection of additive real Schwartz functions into
the space with all positive weights. -/
theorem realSchwartz_restrict_positiveDecay :
    ∃ R : 𝓢(ℝ, ℂ) →L[ℂ] 𝓔(ℝ, 1, Ioi 0), Injective R ∧
      ∀ (f : 𝓢(ℝ, ℂ)) (u : ℝˣ), (R f).val u = f u.val := by sorry

/-- Paper: §5.3.3, p. 249.
Restriction of an additive complex Schwartz function to the units gives a continuous
linear injection into the space with all positive squared-norm weights. -/
theorem complexSchwartz_restrict_positiveDecay :
    ∃ R : 𝓢(ℂ, ℂ) →L[ℂ] 𝓔(ℂ, 2, Ioi 0), Injective R ∧
      ∀ (f : 𝓢(ℂ, ℂ)) (u : ℂˣ), (R f).val u = f u.val := by sorry

open scoped Manifold in
private theorem puncturedTest_mul_equiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (a : E → ℂ) (ha : ContDiff ℝ (∞) a)
    (ha₀ : ∀ x ≠ 0, a x ≠ 0) :
    ∃ M : 𝒟₀(E) ≃L[ℂ] 𝒟₀(E), ∀ f x, M f x = a x * f x := by
  let Ω := punctured(E)
  have mulSmooth (b : E → ℂ) (hb : ContDiffOn ℝ (∞) b Ω) (f : E → ℂ)
      (hf : ContDiff ℝ (∞) f) (hs : ∀ x ∉ Ω, ∀ᶠ y in 𝓝 x, f y = 0) :
      ContDiff ℝ (∞) (fun x ↦ b x * f x) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ Ω
    · exact ((hb x hx).contDiffAt (Ω.isOpen.mem_nhds hx)).mul hf.contDiffAt
    · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [hs x hx] with y hy
      simp [hy]
  have mulCLM (b : E → ℂ) (hb : ContDiffOn ℝ (∞) b Ω) :
      ∃ T : 𝓓(Ω, ℂ) →L[ℂ] 𝓓(Ω, ℂ), ∀ f x, T f x = b x * f x := by
    have zeroLocally (f : 𝓓(Ω, ℂ)) (x : E) (hx : x ∉ Ω) : ∀ᶠ y in 𝓝 x, f y = 0 := by
      have hxf : x ∉ tsupport f := fun h ↦ hx (f.tsupport_subset h)
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hxf] with y hy
      exact notMem_support.mp fun h ↦ hy (subset_closure h)
    let F (f : 𝓓(Ω, ℂ)) : 𝓓(Ω, ℂ) :=
      ⟨fun x ↦ b x * f x, mulSmooth b hb f f.contDiff (zeroLocally f),
        f.hasCompactSupport.mono (support_mul_subset_right b f),
        tsupport_mul_subset_right.trans f.tsupport_subset⟩
    refine ⟨TestFunction.mkCLM ℂ F ?_ ?_ ?_, fun _ _ ↦ rfl⟩
    · intro f g
      ext x
      exact mul_add _ _ _
    · intro c f
      ext x
      exact mul_left_comm _ _ _
    · intro K hK
      -- On each fixed support stage, replace the multiplier by a globally smooth one.
      obtain ⟨χ, hχ₀, hχ₁, _⟩ :=
        exists_contMDiffMap_zero_one_nhds_of_isClosed (𝓘(ℝ, E)) Ω.isOpen.isClosed_compl
          K.isCompact.isClosed (disjoint_left.mpr (fun _ hx hy ↦ hx (hK hy))) (n := (⊤ : ℕ∞))
      have hχ : ContDiff ℝ (∞) (fun x ↦ (χ x : ℂ)) :=
        Complex.ofRealCLM.contDiff.comp (contMDiff_iff_contDiff.mp χ.contMDiff)
      have h : ContDiff ℝ (∞) (fun x ↦ b x * (χ x : ℂ)) :=
        mulSmooth b hb _ hχ fun x hx ↦ by
          filter_upwards [hχ₀.filter_mono (nhds_le_nhdsSet hx)] with y hy
          simp [hy]
      let L := ContDiffMapSupportedIn.bilinLeftCLM (K := K) (ContinuousLinearMap.mul ℂ ℂ) h
      refine ((TestFunction.continuous_ofSupportedIn hK).comp L.continuous).congr ?_
      intro f
      ext x
      change (f x) * (b x * (χ x : ℂ)) = b x * f x
      by_cases hx : x ∈ K
      · have he := hχ₁.self_of_nhdsSet x hx
        simp [he, mul_comm]
      · have hf := notMem_support.mp (fun hh ↦ hx (f.tsupport_subset (subset_closure hh)))
        simp [hf]
  obtain ⟨M, hM⟩ := mulCLM a ha.contDiffOn
  obtain ⟨N, hN⟩ := mulCLM (fun x ↦ (a x)⁻¹) (ha.contDiffOn.inv ha₀)
  have hcomp (f : 𝓓(Ω, ℂ)) (x : E) :
      N (M f) x = f x ∧ M (N f) x = f x := by
    rw [hN, hM, hM, hN]
    by_cases hx : x = 0
    · have hf : f x = 0 :=
        notMem_support.mp (fun h ↦ (f.tsupport_subset (subset_closure h)) (by simp [hx]))
      simp [hf]
    · simp [ha₀ x hx]
  let e : 𝓓(Ω, ℂ) ≃ₗ[ℂ] 𝓓(Ω, ℂ) :=
    { M.toLinearMap with
      invFun := N
      left_inv := fun f ↦ TestFunction.ext (fun x ↦ (hcomp f x).1)
      right_inv := fun f ↦ TestFunction.ext (fun x ↦ (hcomp f x).2) }
  exact ⟨⟨e, M.continuous, N.continuous⟩, hM⟩

/-- Paper: Proposition 5.3.3.2(1), p. 249.
Multiplication by the real coordinate is a linear homeomorphism on compactly supported
smooth tests on the punctured real line. -/
theorem realCoordinate_mul_puncturedTest :
    ∃ M : 𝒟₀(ℝ) ≃L[ℂ] 𝒟₀(ℝ), ∀ f x, M f x = (x : ℂ) * f x := by
  exact puncturedTest_mul_equiv (fun x : ℝ ↦ (x : ℂ)) Complex.ofRealCLM.contDiff
    (fun x hx ↦ by exact_mod_cast hx)

/-- Paper: Proposition 5.3.3.2(1), p. 249.
Multiplication by either complex coordinate, z or its conjugate, is a linear homeomorphism
on compactly supported smooth tests on the punctured complex plane. -/
theorem complexCoordinate_mul_puncturedTest (conjugate : Bool) :
    ∃ M : 𝒟₀(ℂ) ≃L[ℂ] 𝒟₀(ℂ), ∀ f z, M f z = complexCoordinate(conjugate) z * f z := by
  cases conjugate
  · exact puncturedTest_mul_equiv (id : ℂ → ℂ) contDiff_id (fun _ hx ↦ hx)
  · exact puncturedTest_mul_equiv (star : ℂ → ℂ) Complex.conjCLE.contDiff (fun z hz ↦ by simpa using hz)

private theorem realCoordinate_mul_exponentialDecay_good : IsBruhatGoodSubgroup (⊥ : Subgroup ℝˣ) := by
  let e : EuclideanSpace ℝ (Fin 1) ≃L[ℝ] ℝ := PiLp.equivOfUnique 2 ℝ _
  exact isBruhatGoodSubgroup_bot_iff.mpr ⟨1, ⟨(e.symm.toHomeomorph.isOpenEmbedding.comp
    (Units.isOpenEmbedding_val (R := ℝ))).singletonChartedSpace⟩⟩

/-- The positive units give a Bruhat stage. They lie in every open stage subgroup,
while their intersection with each compact stage kernel is trivial. -/
private theorem realCoordinate_mul_exponentialDecay_posStage :
    ∃ a : BruhatStructuralPair ℝˣ, a.val.1 = Units.posSubgroup ℝ ∧
      OrderDual.ofDual a.val.2 = ⊥ ∧ ∀ b : BruhatStructuralPair ℝˣ,
        a.val.1 ≤ b.val.1 ∧ ∀ x ∈ a.val.1, x ∈ OrderDual.ofDual b.val.2 → x = 1 := by
  let P := Units.posSubgroup ℝ
  have hP : IsOpen (P : Set ℝˣ) := isOpen_Ioi.preimage Units.continuous_val
  have hPc : PreconnectedSpace P := by
    apply isPreconnected_iff_preconnectedSpace.mp
    apply Units.isOpenEmbedding_val.isInducing.isPreconnected_image.mp
    have he : Units.val '' (P : Set ℝˣ) = Ioi (0 : ℝ) := by
      ext x
      exact ⟨fun ⟨u, hu, he⟩ ↦ he ▸ hu, fun hx ↦ ⟨Units.mk0 x (ne_of_gt hx), hx, rfl⟩⟩
    rw [he]
    exact isPreconnected_Ioi
  let : LocallyCompactSpace P := hP.isOpenEmbedding_subtypeVal.locallyCompactSpace
  have hgen : IsCompactlyGeneratedGroup P := by
    obtain ⟨U, hUc, hU⟩ := exists_compact_mem_nhds (1 : P)
    have ho : IsOpen (Subgroup.closure U : Set P) :=
      Subgroup.isOpen_of_mem_nhds _ (mem_of_superset hU Subgroup.subset_closure)
    exact ⟨U, hU, hUc, SetLike.coe_injective
      ((OpenSubgroup.isClopen ⟨Subgroup.closure U, ho⟩).eq_univ ⟨1, Subgroup.one_mem _⟩)⟩
  refine ⟨⟨(P, OrderDual.toDual ⊥), hP, hgen, realCoordinate_mul_exponentialDecay_good, bot_le⟩,
    rfl, rfl, fun b ↦ ⟨?_, ?_⟩⟩
  · have h := (OpenSubgroup.isClopen ⟨b.val.1, b.property.1⟩).preimage
      (continuous_subtype_val (p := fun x ↦ x ∈ P))
    have hu := h.eq_univ ⟨1, b.val.1.one_mem⟩
    intro x hx
    exact (Set.eq_univ_iff_forall.mp hu) (⟨x, hx⟩ : P)
  · intro x hx hk
    let m := archimedeanUnitModulation ℝ 1
    have hm : m x = 1 := compactSubgroup_le_modulation_ker m _
      (isCompact_of_isBruhatGoodSubgroup_aux _ b.property.2.2.1) hk
    have he := archimedeanUnitModulation_apply ℝ 1 x
    change ((m x).val : ℝ) = _ at he
    rw [hm, pow_one, Real.norm_eq_abs, abs_of_pos (show 0 < x.val from hx)] at he
    exact Units.ext he.symm

/-- Restrict an arbitrary stage to the positive component and realize the result
in the positive stage, extending by zero on the other component. -/
private theorem realCoordinate_mul_exponentialDecay_restrictStage
    (a b : BruhatStructuralPair ℝˣ) (ha : OrderDual.ofDual a.val.2 = ⊥)
    (hab : a.val.1 ≤ b.val.1)
    (hk : ∀ x ∈ a.val.1, x ∈ OrderDual.ofDual b.val.2 → x = 1)
    (e : ElementaryLCAPresentation a.quotient) (d : ElementaryLCAPresentation b.quotient) :
    ∃ R : SchwartzBruhatStage d →L[ℂ] SchwartzBruhatStage e,
      ∀ f x, schwartzBruhatStageRealization a e (R f) x =
        (a.val.1 : Set ℝˣ).indicator (schwartzBruhatStageRealization b d f) x := by
  classical
  let _ := e.finiteGroup
  let _ := e.finiteTopology
  let _ := e.finiteDiscrete
  let _ := e.finiteFintype
  let _ := d.finiteGroup
  let _ := d.finiteTopology
  let _ := d.finiteDiscrete
  let _ := d.finiteFintype
  let inc := Subgroup.inclusion hab
  let p := MonoidHom.toAdditive ((d.equiv.toMulEquiv.toMonoidHom.comp (QuotientGroup.mk' _)).comp inc)
  let q := MonoidHom.toAdditive (e.equiv.toMulEquiv.toMonoidHom.comp (QuotientGroup.mk' _))
  have hqker (x : a.val.1) (hx : (QuotientGroup.mk x : a.quotient) = 1) : x = 1 := by
    apply Subtype.ext
    change x.val = 1
    simpa only [ha, Subgroup.mem_bot] using (a.quotient_mk_eq_one x).mp hx
  have hqi : Injective q := by
    apply (AddMonoidHom.ker_eq_bot_iff _).mp
    refine le_antisymm (fun x hx ↦ ?_) bot_le
    change Additive.toMul x = 1
    apply hqker
    exact e.equiv.injective ((show e.equiv _ = 1 from hx).trans (map_one _).symm)
  have hqs : Surjective q := fun y ↦ (e.equiv.surjective (Multiplicative.ofAdd y)).elim
    fun t ht ↦ (QuotientGroup.mk_surjective t).elim fun x hx ↦ ⟨Additive.ofMul x, (congrArg e.equiv hx).trans ht⟩
  let v := Equiv.ofBijective q ⟨hqi, hqs⟩
  have hker : p.ker ≤ q.ker := by
    intro x hx
    have he := d.equiv.injective ((show d.equiv (QuotientGroup.mk (inc (Additive.toMul x))) = 1 from hx).trans
      (map_one _).symm)
    have h1 := hk _ (Additive.toMul x).property ((b.quotient_mk_eq_one _).mp he)
    have hx0 : x = 0 := congrArg Additive.ofMul (Subtype.ext h1)
    rw [hx0]
    exact q.ker.zero_mem
  let T : SchwartzBruhatStage d →ₗ[ℂ] SchwartzBruhatStage e :=
    { toFun := fun f ↦ ⟨fun y ↦ f (p (v.symm y)), by
        apply elementarySchwartz_of_common_pullback p _ _ q _ _ hqs hker f
        · intro x
          exact congrArg (fun z ↦ f (p z)) (v.symm_apply_apply x).symm
        · exact d.equiv.continuous.comp (QuotientGroup.continuous_mk.comp
            (show Continuous inc from continuous_subtype_val.subtype_mk _))
        · exact d.equiv.toHomeomorph.isOpenMap.comp (QuotientGroup.isOpenMap_coe.comp
            (a.property.1.isOpenMap_inclusion hab))
        · exact e.equiv.continuous.comp (QuotientGroup.continuous_mk
            (N := (OrderDual.ofDual a.val.2).comap a.val.1.subtype))
        · exact e.equiv.toHomeomorph.isOpenMap.comp (QuotientGroup.isOpenMap_coe
            (N := (OrderDual.ofDual a.val.2).comap a.val.1.subtype))⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let X := SchwartzBruhatStage d
  let : BarrelledSpace ℂ X := isFrechetTVS_barrelled elementarySchwartz_isFrechet
  let : ContinuousSMul ℂ X := elementarySchwartz_withSeminorms.continuousSMul
  have hT : Continuous T := by
    apply continuous_toElementarySchwartz_of_eval T
    intro y
    exact elementarySchwartz_eval_continuousLinear (p (v.symm y))
  refine ⟨⟨T, hT⟩, fun f x ↦ ?_⟩
  by_cases hx : x ∈ a.val.1
  · exact ((schwartzBruhatStageRealization_apply a e (T f) x).trans (dite_eq_left hx)).trans <|
      (congrArg (fun z ↦ f (p z)) (v.symm_apply_apply (Additive.ofMul (⟨x, hx⟩ : a.val.1)))).trans <|
      (((schwartzBruhatStageRealization_apply b d f x).trans (dite_eq_left (hab hx))).symm.trans
        (Set.indicator_of_mem hx _).symm)
  · exact ((schwartzBruhatStageRealization_apply a e (T f) x).trans (dite_eq_right hx)).trans
      (Set.indicator_of_notMem hx _).symm

/-- Twice the projection onto the positive component minus the identity multiplies
Schwartz–Bruhat functions by the sign. -/
private theorem realCoordinate_mul_exponentialDecay_sign :
    ∃ S : SchwartzBruhat ℝˣ →L[ℂ] SchwartzBruhat ℝˣ,
      ∀ f (x : ℝˣ), S f x = (if 0 < x.val then (1 : ℂ) else -1) * f x := by
  classical
  let a := realCoordinate_mul_exponentialDecay_posStage.choose
  have has := realCoordinate_mul_exponentialDecay_posStage.choose_spec
  have ha : a.val.1 = Units.posSubgroup ℝ := has.1
  let e := a.elementary.some
  let H := (a.val.1 : Set ℝˣ)
  let L : (ℝˣ → ℂ) →ₗ[ℂ] (ℝˣ → ℂ) :=
    { toFun := H.indicator
      map_add' := H.indicator_add'
      map_smul' := fun c f ↦ H.indicator_smul (fun _ ↦ c) f }
  have hstage (b : BruhatStructuralPair ℝˣ) (d : ElementaryLCAPresentation b.quotient) :=
    realCoordinate_mul_exponentialDecay_restrictStage a b has.2.1 (has.2.2 b).1 (has.2.2 b).2 e d
  have hmem : schwartzBruhatSubmodule ℝˣ ≤ (schwartzBruhatSubmodule ℝˣ).comap L := by
    refine iSup_le fun b ↦ iSup_le fun d ↦ ?_
    rintro _ ⟨f, rfl⟩
    let R := (hstage b d).choose
    have hr := funext ((hstage b d).choose_spec f)
    change H.indicator _ ∈ schwartzBruhatSubmodule ℝˣ
    exact hr ▸ (schwartzBruhatStageInclusion a e (R f)).property
  let P : SchwartzBruhat ℝˣ →ₗ[ℂ] SchwartzBruhat ℝˣ :=
    (L.comp (schwartzBruhatSubmodule ℝˣ).subtype).codRestrict _ (fun f ↦ hmem f.property)
  have hc : Continuous P := by
    have gen := withGeneratingSeminorms_spec (schwartzBruhatSubmodule ℝˣ)
      (Subtype.val : {p : Seminorm ℂ (schwartzBruhatSubmodule ℝˣ) //
        ∀ b d, Continuous (p ∘ schwartzBruhatStageInclusion b d)} → _)
    refine gen.continuous_of_continuous_comp P fun p ↦ gen.continuous_seminorm ⟨p.val.comp P, ?_⟩
    intro b d
    let R := (hstage b d).choose
    exact ((p.property a e).comp R.continuous).congr fun f ↦
      congrArg p.val (Subtype.ext (funext ((hstage b d).choose_spec f)))
  let A : SchwartzBruhat ℝˣ →L[ℂ] SchwartzBruhat ℝˣ := ⟨P, hc⟩
  refine ⟨A + A - ContinuousLinearMap.id ℂ _, fun f x ↦ ?_⟩
  change H.indicator f.val x + H.indicator f.val x - f.val x = _
  have hx : x ∈ H ↔ 0 < x.val := by
    change x ∈ a.val.1 ↔ _
    rw [ha, Units.mem_posSubgroup]
  by_cases h : 0 < x.val
  · rw [Set.indicator_of_mem (hx.mpr h), ite_eq_left h, one_mul, add_sub_cancel_right]
  · rw [Set.indicator_of_notMem (mt hx.mp h), ite_eq_right h, zero_add, zero_sub, neg_one_mul]

private theorem realCoordinate_mul_exponentialDecay_weight (b : ℝ) (x : ℝˣ) :
    (if 0 < x.val then (1 : ℂ) else -1) * (↑(‖x.val‖ ^ (b + 1)) : ℂ) =
      (↑(‖x.val‖ ^ b) : ℂ) * (x.val : ℂ) := by
  rw [Real.rpow_add (norm_pos_iff.mpr x.ne_zero), Real.rpow_one, Complex.ofReal_mul]
  by_cases hx : 0 < x.val
  · rw [ite_eq_left hx, one_mul, Real.norm_eq_abs, abs_of_pos hx]
  · rw [ite_eq_right hx, Real.norm_eq_abs, abs_of_nonpos (le_of_not_gt hx), Complex.ofReal_neg]
    ring

/-- Paper: Proposition 5.3.3.2(1), p. 249.
Multiplication by the real coordinate is continuous for decay on a closed upper half-line. -/
theorem realCoordinate_mul_exponentialDecay (a : ℝ) :
    ∃ M : 𝓔(ℝ, 1, Ici a) →L[ℂ] 𝓔(ℝ, 1, Ici a),
      ∀ f x, (M f).val x = ((x : ℝ) : ℂ) * f.val x := by
  let m := archimedeanUnitModulation ℝ 1
  let I := Ici a
  let E := ModulatedExponentialDecay m I
  -- Use the stage for the trivial compact subgroup, so the output loses no sign information.
  let k : {k : Subgroup ℝˣ // IsCompact (k : Set ℝˣ) ∧ IsCompactlyGeneratedGroup (lcaAnnihilator k)} :=
    ⟨⊥, by simpa only [Subgroup.coe_bot] using isCompact_singleton (x := (1 : ℝˣ)),
      realCoordinate_mul_exponentialDecay_good.2.2⟩
  let v : (ℝˣ ⧸ k.val) ≃ₜ* ℝˣ :=
    { QuotientGroup.quotientBot with
      continuous_toFun := (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr continuous_id
      continuous_invFun := QuotientGroup.continuous_mk }
  let n := quotientModulation m k.val k.property.1
  have pull := exists_schwartzBruhat_pullback (A := ℝˣ ⧸ k.val) (B := ℝˣ) v
  let S := realCoordinate_mul_exponentialDecay_sign.choose
  let coord (x : ℝˣ ⧸ k.val) : ℂ := (v x).val
  let L : E →ₗ[ℂ] ((ℝˣ ⧸ k.val) → ℂ) := (LinearMap.mulLeft ℂ coord).comp
    ((LinearMap.funLeft ℂ ℂ v).comp (modulatedExponentialDecaySubmodule m I).subtype)
  let next (b : I) : I := ⟨b + 1, le_trans b.property (le_add_of_nonneg_right zero_le_one)⟩
  let W (b : I) : E →L[ℂ] SchwartzBruhat (ℝˣ ⧸ k.val) := pull.choose.comp <| S.comp
    ⟨modulatedExponentialDecayTwist m I (next b), continuous_decay_twist m I (next b)⟩
  -- The b-twist of x f is the sign times the (b+1)-twist of f.
  have hw (b : I) (f : E) : (W b f).val = modulationWeight n b (L f) := by
    funext y
    refine QuotientGroup.induction_on y fun x ↦ ?_
    refine (pull.choose_spec (S (modulatedExponentialDecayTwist m I (next b) f)) _).trans ?_
    refine (realCoordinate_mul_exponentialDecay_sign.choose_spec
      (modulatedExponentialDecayTwist m I (next b) f) x).trans ?_
    change (if 0 < x.val then (1 : ℂ) else -1) *
      (((((m x).val : ℝ) ^ ((b : ℝ) + 1) : ℝ) : ℂ) * f.val x) =
      ((((m x).val : ℝ) ^ (b : ℝ) : ℝ) : ℂ) * ((x.val : ℂ) * f.val x)
    rw [show ((m x).val : ℝ) = ‖x.val‖ by simpa only [pow_one] using archimedeanUnitModulation_apply ℝ 1 x,
      ← mul_assoc, realCoordinate_mul_exponentialDecay_weight, mul_assoc]
  let T : E →ₗ[ℂ] ModulatedExponentialDecayStage m I k := L.codRestrict _ (fun f ↦
    (Submodule.mem_iInf _).mpr fun b ↦ Submodule.mem_comap.mpr ((hw b f) ▸ (W b f).property))
  have hT : Continuous T := by
    apply (modulatedExponentialDecayStage_twists_isInducing m I k).continuous_iff.mpr
    exact continuous_pi fun b ↦ (W b).continuous.congr fun f ↦ Subtype.ext (hw b f)
  let j : ModulatedExponentialDecayStage m I k →ₗ[ℂ] E := modulatedExponentialDecayStageInclusion m I k
  have hj : Continuous j :=
    (withGeneratingSeminorms_spec _ _).continuous_of_continuous_comp j (fun p ↦ p.property k)
  exact ⟨(⟨j, hj⟩ : _ →L[ℂ] E).comp ⟨T, hT⟩, fun _ _ ↦ rfl⟩

/-- Paper: Proposition 5.3.3.2(1), p. 249.
Multiplication by z or its conjugate is continuous for decay on a closed upper half-line. -/
theorem complexCoordinate_mul_exponentialDecay (conjugate : Bool) (a : ℝ) :
    ∃ M : 𝓔(ℂ, 2, Ici a) →L[ℂ] 𝓔(ℂ, 2, Ici a),
      ∀ f z, (M f).val z = complexCoordinate(conjugate) z.val * f.val z := by sorry

/-- The real absolute value on the units is a surjective modulation. -/
private theorem realCoordinate_mul_allExponentialDecay_modulation
    [SecondCountableTopology ℝˣ] :
    IsModulation (archimedeanUnitModulation ℝ 1) ∧ Surjective (archimedeanUnitModulation ℝ 1) := by
  refine ⟨⟨isProperMap_units_nnNorm_pow (K := ℝ) 1 one_ne_zero, ⟨Units.mk0 2 two_ne_zero, ?_⟩⟩, ?_⟩
  · intro h
    have h2 := congrArg (fun t : ℝ≥0ˣ ↦ (t.val : ℝ)) h
    simp only [archimedeanUnitModulation_apply, Units.val_mk0, pow_one, Units.val_one,
      NNReal.coe_one] at h2
    norm_num at h2
  · intro t
    have ht : ((t.val : ℝ≥0) : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr t.ne_zero
    refine ⟨Units.mk0 _ ht, Units.ext (NNReal.eq ?_)⟩
    rw [archimedeanUnitModulation_apply, Units.val_mk0, pow_one, Real.norm_eq_abs,
      abs_of_nonneg (NNReal.coe_nonneg _)]

/-- Paper: Proposition 5.3.3.2(1), p. 249.
Multiplication by the real coordinate is continuously invertible for decay at all exponents. -/
theorem realCoordinate_mul_allExponentialDecay :
    ∃ M : 𝓔(ℝ, 1, univ) ≃L[ℂ] 𝓔(ℝ, 1, univ),
      ∀ f x, (M f).val x = ((x : ℝ) : ℂ) * f.val x := by
  letI : SecondCountableTopology ℝˣ := Units.isEmbedding_val₀.secondCountableTopology
  have hm := realCoordinate_mul_allExponentialDecay_modulation.1
  have hms := realCoordinate_mul_allExponentialDecay_modulation.2
  let c : QuasiCharacter ℝˣ :=
    ⟨Complex.ofRealHom.toMonoidHom.comp (Units.coeHom ℝ),
      Complex.continuous_ofReal.comp Units.continuous_val⟩
  exact modulatedExponentialDecay_mul_quasiCharacter _ hm hms c

/-- The squared complex absolute value on the units is a surjective modulation. -/
private theorem complexCoordinate_mul_allExponentialDecay_modulation
    [SecondCountableTopology ℂˣ] :
    IsModulation (archimedeanUnitModulation ℂ 2) ∧ Surjective (archimedeanUnitModulation ℂ 2) := by
  refine ⟨⟨isProperMap_units_nnNorm_pow (K := ℂ) 2 two_ne_zero, ⟨Units.mk0 2 two_ne_zero, ?_⟩⟩, ?_⟩
  · intro h
    have h2 := congrArg (fun t : ℝ≥0ˣ ↦ (t.val : ℝ)) h
    simp only [archimedeanUnitModulation_apply, Units.val_mk0, Units.val_one,
      NNReal.coe_one, Complex.norm_ofNat] at h2
    norm_num at h2
  · intro t
    have ht : ((Real.sqrt ((t.val : ℝ≥0) : ℝ) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (NNReal.coe_pos.mpr (Units.zero_lt t)))
    refine ⟨Units.mk0 _ ht, Units.ext (NNReal.eq ?_)⟩
    rw [archimedeanUnitModulation_apply, Units.val_mk0, Complex.norm_real, Real.norm_eq_abs,
      sq_abs, Real.sq_sqrt (NNReal.coe_nonneg _)]

/-- Paper: Proposition 5.3.3.2(1), p. 249.
Multiplication by z or its conjugate is continuously invertible for decay at all exponents. -/
theorem complexCoordinate_mul_allExponentialDecay (conjugate : Bool) :
    ∃ M : 𝓔(ℂ, 2, univ) ≃L[ℂ] 𝓔(ℂ, 2, univ),
      ∀ f z, (M f).val z = complexCoordinate(conjugate) z.val * f.val z := by
  letI : SecondCountableTopology ℂˣ := Units.isEmbedding_val₀.secondCountableTopology
  have hm := complexCoordinate_mul_allExponentialDecay_modulation.1
  have hms := complexCoordinate_mul_allExponentialDecay_modulation.2
  cases conjugate
  · exact modulatedExponentialDecay_mul_quasiCharacter _ hm hms
      ⟨Units.coeHom ℂ, Units.continuous_val⟩
  · exact modulatedExponentialDecay_mul_quasiCharacter _ hm hms
      ⟨(starRingEnd ℂ).toMonoidHom.comp (Units.coeHom ℂ),
        Complex.continuous_conj.comp Units.continuous_val⟩

-- TODO(paper-gap): Footnote 8 flags the closed-range argument. A convergent net in the LF
-- space of tests need not eventually be bounded and a directed set need not have countable cofinality.

/-- Paper: Proposition 5.3.3.2(2)(1), p. 249.
Each ordinary derivative is a continuous operator of closed range on punctured real tests. -/
theorem iteratedDeriv_puncturedTest_closedRange (m : ℕ) :
    ∃ D : 𝒟₀(ℝ) →L[ℂ] 𝒟₀(ℝ), IsClosed (range D) ∧
      ∀ f x, D f x = iteratedDeriv m (f : ℝ → ℂ) x := by sorry

/-- Paper: Proposition 5.3.3.2(2)(2), p. 250.
Both first Wirtinger operators have closed range on punctured complex tests. -/
theorem wirtinger_puncturedTest_closedRange (conjugate : Bool) :
    ∃ D : 𝒟₀(ℂ) →L[ℂ] 𝒟₀(ℂ), IsClosed (range D) ∧
      ∀ f z, D f z = wirtinger(conjugate) f z := by sorry

/-- Elementary logarithmic coordinates on the two components of the punctured line. -/
private theorem iteratedDeriv_exponentialDecay_chart :
    ∃ w : ℝˣ ≃ₜ* Multiplicative (ElementaryLieGroup 1 0 0 (ZMod 2)), ∀ x,
      realBruhatCoordinate (w x).toAdd.1 = Real.log x.val ∧
      (w x).toAdd.2.2.2 = if 0 < x.val then 0 else 1 := by
  let X := ElementaryLieGroup 1 0 0 (ZMod 2)
  let s (x : ℝˣ) : ZMod 2 := if 0 < x.val then 0 else 1
  let u (x : ℝˣ) : Multiplicative X := Multiplicative.ofAdd
    (realBruhatCoordinate.symm (Real.log x.val), 0, 0, s x)
  let r (y : X) := Real.exp (realBruhatCoordinate y.1)
  let v (y : Multiplicative X) : ℝˣ := Units.mk0
    (if y.toAdd.2.2.2 = 0 then r y.toAdd else -r y.toAdd)
    (by split <;> simp [r, Real.exp_ne_zero])
  have hs : Continuous s := by
    have hco : IsClopen {x : ℝˣ | 0 < x.val} := by
      refine ⟨?_, isOpen_lt continuous_const Units.continuous_val⟩
      have h : {x : ℝˣ | 0 < x.val} = {x | 0 ≤ x.val} :=
        Set.ext fun x ↦ (show 0 < x.val ↔ 0 ≤ x.val from ⟨le_of_lt, fun h ↦ lt_of_le_of_ne h x.ne_zero.symm⟩)
      rw [h]
      exact isClosed_le continuous_const Units.continuous_val
    exact Continuous.if (by simp [hco.frontier_eq]) continuous_const continuous_const
  have hlog : Continuous (fun x : ℝˣ ↦ Real.log x.val) := continuous_iff_continuousAt.mpr
    fun x ↦ (Real.continuousAt_log x.ne_zero).comp Units.continuous_val.continuousAt
  let w : ℝˣ ≃ₜ* Multiplicative X :=
    { toFun := u
      invFun := v
      left_inv := fun x ↦ by
        apply Units.ext
        change (if s x = 0 then Real.exp (Real.log x.val) else -Real.exp (Real.log x.val)) = x.val
        rw [Real.exp_log_eq_abs x.ne_zero]
        by_cases h : 0 < x.val
        · simp [s, h, abs_of_pos h]
        · simp [s, h, abs_of_nonpos (le_of_not_gt h)]
      right_inv := fun y ↦ by
        change (realBruhatCoordinate.symm (Real.log (v y).val), 0, 0, s (v y)) = y.toAdd
        refine Prod.ext ?_ (Prod.ext (Subsingleton.elim _ _) (Prod.ext (Subsingleton.elim _ _) ?_))
        · change realBruhatCoordinate.symm (Real.log (if y.toAdd.2.2.2 = 0 then _ else _)) = _
          split <;> simp only [r, Real.log_neg_eq_log, Real.log_exp, realBruhatCoordinate.symm_apply_apply]
        · have hb : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
          rcases hb y.toAdd.2.2.2 with h | h <;> simp [s, v, h, r, Real.exp_pos, (Real.exp_pos _).le]
      map_mul' := fun x y ↦ by
        change (realBruhatCoordinate.symm (Real.log (x.val * y.val)), 0, 0, s (x*y)) =
          ((realBruhatCoordinate.symm (Real.log x.val), 0, 0, s x) : X) +
          (realBruhatCoordinate.symm (Real.log y.val), 0, 0, s y)
        refine Prod.ext ?_ (Prod.ext (Subsingleton.elim _ _) (Prod.ext (Subsingleton.elim _ _) ?_))
        · change realBruhatCoordinate.symm (Real.log (x.val * y.val)) = _
          rw [Real.log_mul x.ne_zero y.ne_zero, map_add]
          rfl
        · change s (x*y) = s x + s y
          rcases lt_or_gt_of_ne x.ne_zero with hx | hx <;> rcases lt_or_gt_of_ne y.ne_zero with hy | hy
          · simp [s, hx.not_gt, hy.not_gt, mul_pos_of_neg_of_neg hx hy]; decide
          · simp [s, hx.not_gt, hy, (mul_neg_of_neg_of_pos hx hy).not_gt]
          · simp [s, hx, hy.not_gt, (mul_neg_of_pos_of_neg hx hy).not_gt]
          · simp [s, hx, hy, mul_pos hx hy]
      continuous_toFun := (realBruhatCoordinate.symm.continuous.comp hlog).prodMk
        (continuous_const.prodMk (continuous_const.prodMk hs))
      continuous_invFun := by
        apply Units.isOpenEmbedding_val.isInducing.continuous_iff.mpr
        change Continuous (fun y : X ↦ if y.2.2.2 = 0 then r y else -r y)
        have hco : IsClopen {y : X | y.2.2.2 = 0} :=
          (isClopen_discrete ({0} : Set (ZMod 2))).preimage (continuous_snd.comp (continuous_snd.comp continuous_snd))
        have hr : Continuous r := Real.continuous_exp.comp (realBruhatCoordinate.continuous.comp continuous_fst)
        exact Continuous.if (by simp [hco.frontier_eq]) hr hr.neg }
  exact ⟨w, fun x ↦ ⟨realBruhatCoordinate.apply_symm_apply _, rfl⟩⟩

private theorem iteratedDeriv_exponentialDecay_goodBot :
    IsCompactlyGeneratedGroup (lcaAnnihilator (⊥ : Subgroup ℝˣ)) := by
  obtain ⟨w, _⟩ := iteratedDeriv_exponentialDecay_chart
  let e : ElementaryLCAPresentation ℝˣ := ⟨1, 0, 0, ZMod 2, w⟩
  exact (isBruhatGoodSubgroup_bot_iff.mpr ((lca_elementary_iff.mpr ⟨e⟩).2)).2.2

/-- Glue two elementary real-line functions on the two fibres. Each output seminorm
is controlled by the maximum of the corresponding input seminorms. -/
private theorem iteratedDeriv_exponentialDecay_glue :
    ∃ L : (ElementarySchwartz 1 0 0 PUnit × ElementarySchwartz 1 0 0 PUnit) →L[ℂ]
        ElementarySchwartz 1 0 0 (ZMod 2), ∀ f p,
      L f p = (if p.2.2.2 = 0 then f.1 else f.2) (p.1, p.2.1, p.2.2.1, PUnit.unit) := by
  let E := ElementarySchwartz 1 0 0 PUnit
  let X := ElementaryLieGroup 1 0 0 (ZMod 2)
  let fn (f : E × E) (p : X) :=
    (if p.2.2.2 = 0 then f.1 else f.2) (p.1, p.2.1, p.2.2.1, PUnit.unit)
  have hb (f : E × E) (i : ElementarySchwartzIndex 1 0 0) :
      elementarySchwartzBound (fn f) i ≤
        max (elementarySchwartzBound f.1.val i) (elementarySchwartzBound f.2.val i) := by
    refine iSup_le fun xt ↦ iSup_le fun a ↦ iSup_le fun b ↦ ?_
    let g : E := if b = 0 then f.1 else f.2
    have h : elementarySchwartzBound g.val i ≤
        max (elementarySchwartzBound f.1.val i) (elementarySchwartzBound f.2.val i) := by
      dsimp only [g]; split <;> simp
    refine le_trans ?_ h
    unfold elementarySchwartzBound
    exact le_iSup_of_le xt (le_iSup_of_le a (le_iSup_of_le PUnit.unit le_rfl))
  let A : E × E →ₗ[ℂ] ElementarySchwartz 1 0 0 (ZMod 2) :=
    { toFun := fun f ↦ ⟨fn f, fun a b ↦ (if b = 0 then f.1 else f.2).property.1 a PUnit.unit,
        fun i ↦ (hb f i).trans_lt (max_lt (f.1.property.2 i) (f.2.property.2 i))⟩
      map_add' := fun f g ↦ Subtype.ext (funext fun p ↦ by
        change fn (f+g) p = fn f p + fn g p
        by_cases h : p.2.2.2 = 0 <;> simp [fn, h] <;> rfl)
      map_smul' := fun c f ↦ Subtype.ext (funext fun p ↦ by
        change fn (c • f) p = c • fn f p
        by_cases h : p.2.2.2 = 0 <;> simp [fn, h] <;> rfl) }
  refine ⟨⟨A, elementarySchwartz_withSeminorms.continuous_of_continuous_comp A fun i ↦ ?_⟩,
    fun _ _ ↦ rfl⟩
  let q : Seminorm ℂ E := elementarySchwartzSeminorm i
  have hq : Continuous q := elementarySchwartz_withSeminorms.continuous_seminorm i
  let Q := (q.comp (LinearMap.fst ℂ E E)) ⊔ (q.comp (LinearMap.snd ℂ E E))
  have hQ : Continuous Q := (hq.comp continuous_fst).max (hq.comp continuous_snd)
  apply Seminorm.continuous_of_le hQ
  intro f
  change (elementarySchwartzBound (fn f) i).toReal ≤
    max (elementarySchwartzBound f.1.val i).toReal (elementarySchwartzBound f.2.val i).toReal
  rw [← ENNReal.toReal_max (f.1.property.2 i).ne (f.2.property.2 i).ne]
  exact ENNReal.toReal_mono (max_lt (f.1.property.2 i) (f.2.property.2 i)).ne (hb f i)

/-- Continuous forward realization from an elementary presentation; only the stage
inclusion is needed, not its inverse. -/
private theorem iteratedDeriv_exponentialDecay_realize {G : Type*} [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (e : ElementaryLCAPresentation G) :
    ∃ j : SchwartzBruhatStage e →L[ℂ] SchwartzBruhat G, ∀ g x, j g x = g (e.equiv x).toAdd := by
  have hE := (lca_elementary_iff (G := G)).mpr ⟨e⟩
  let hk := (isBruhatGoodSubgroup_bot_iff (G := G)).mpr hE.2
  let a := fullBruhatStage hE.1 hk
  have hV := fullBruhatStage_quotientEquiv hE.1 hk (MonoidHom.id G) IsOpenQuotientMap.id (by simp)
  let v := hV.choose
  let d : ElementaryLCAPresentation a.quotient := {e with equiv := v.trans e.equiv}
  let j : SchwartzBruhatStage e →L[ℂ] SchwartzBruhat G :=
    ⟨schwartzBruhatStageInclusion a d, (withGeneratingSeminorms_spec _ _).continuous_of_continuous_comp _
      fun q ↦ q.property a d⟩
  refine ⟨j, fun g x ↦ ?_⟩
  change schwartzBruhatStageRealization a d g x = _
  have hx : x ∈ a.val.1 := Subgroup.mem_top x
  rw [schwartzBruhatStageRealization_apply, dite_eq_left hx]
  exact congrArg (fun y : G ↦ g (e.equiv y).toAdd) (hV.choose_spec x)

/-- Assemble independently prescribed logarithmic profiles by realizing them in the
full elementary stage with trivial kernel. -/
private theorem iteratedDeriv_exponentialDecay_assemble :
    ∃ J : (𝓢(ℝ, ℂ) × 𝓢(ℝ, ℂ)) →L[ℂ] SchwartzBruhat ℝˣ,
      ∀ f x, J f x = if 0 < x.val then f.1 (Real.log x.val) else f.2 (Real.log x.val) := by
  let w := iteratedDeriv_exponentialDecay_chart.choose
  have hw := iteratedDeriv_exponentialDecay_chart.choose_spec
  let e : ElementaryLCAPresentation ℝˣ := ⟨1, 0, 0, ZMod 2, w⟩
  let j := (iteratedDeriv_exponentialDecay_realize e).choose
  have hj := (iteratedDeriv_exponentialDecay_realize e).choose_spec
  let I := (elementarySchwartz_real_equiv PUnit.{1}).choose
  have hI := (elementarySchwartz_real_equiv PUnit.{1}).choose_spec
  let L := iteratedDeriv_exponentialDecay_glue.choose
  have hL := iteratedDeriv_exponentialDecay_glue.choose_spec
  refine ⟨j.comp (L.comp (I.toContinuousLinearMap.prodMap I.toContinuousLinearMap)), fun f x ↦ ?_⟩
  change j (L (I f.1, I f.2)) x = _
  rw [hj, hL]
  change (if (w x).toAdd.2.2.2 = 0 then I f.1 else I f.2)
    ((w x).toAdd.1, (w x).toAdd.2.1, (w x).toAdd.2.2.1, PUnit.unit) = _
  rw [(hw x).2]
  by_cases hx : 0 < x.val <;> simp only [hx, ite_true, ite_false, one_ne_zero]
  · exact (hI f.1 _).trans (congrArg (f.1 : ℝ → ℂ) (hw x).1)
  · exact (hI f.2 _).trans (congrArg (f.2 : ℝ → ℂ) (hw x).1)

/-- Exponential coordinates on either component restrict an elementary Bruhat stage
of the real units to the elementary Schwartz space of a line. -/
private theorem iteratedDeriv_exponentialDecay_stage_slice
    (u : ℝˣ) (q : ℝ ≃ₜ+ ElementaryLieGroup 1 0 0 PUnit.{1})
    (a : BruhatStructuralPair ℝˣ) (e : ElementaryLCAPresentation a.quotient)
    (s : SchwartzBruhatStage e) :
    (fun x ↦ schwartzBruhatStageRealization a e s
      (u * Units.mk0 (Real.exp (q.symm x)) (Real.exp_pos _).ne')) ∈
        elementarySchwartzSubmodule 1 0 0 PUnit.{1} := by
  classical
  let expU : Multiplicative ℝ →* ℝˣ :=
    { toFun := fun x ↦ Units.mk0 (Real.exp x.toAdd) (Real.exp_pos _).ne'
      map_one' := Units.ext Real.exp_zero
      map_mul' := fun x y ↦ Units.ext (Real.exp_add _ _) }
  have hc : Continuous expU := Units.isEmbedding_val₀.continuous_iff.mpr Real.continuous_exp
  have ho : IsOpenMap expU :=
    (IsOpenUnits.isOpenEmbedding_unitsVal (M := ℝ)).isOpenMap_iff.mpr Real.isOpenEmbedding_exp.isOpenMap
  have hmem (t : Multiplicative ℝ) : expU t ∈ a.val.1 := by
    let V : OpenSubgroup ℝˣ := ⟨a.val.1, a.property.1⟩
    have h : IsClopen ((fun x : ℝ ↦ expU (.ofAdd x)) ⁻¹' (V : Set ℝˣ)) := V.isClopen.preimage hc
    have h1 : (0 : ℝ) ∈ (fun x : ℝ ↦ expU (.ofAdd x)) ⁻¹' (V : Set ℝˣ) := by
      change expU 1 ∈ a.val.1
      rw [map_one]; exact a.val.1.one_mem
    exact (Set.eq_univ_iff_forall.mp (h.eq_univ ⟨0, h1⟩)) t.toAdd
  by_cases hu : u ∈ a.val.1
  · let E := ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor
    let j : Multiplicative ℝ →* a.val.1 := expU.codRestrict _ hmem
    let k : a.val.1 →* Multiplicative E := e.equiv.toMulEquiv.toMonoidHom.comp (QuotientGroup.mk' _)
    let p : ℝ →+ E := MonoidHom.toAdditive (k.comp j)
    have hkc : Continuous k := e.equiv.continuous.comp QuotientGroup.continuous_mk
    have hko : IsOpenMap k := e.equiv.toHomeomorph.isOpenMap.comp (QuotientGroup.isOpenMap_coe
      (N := (OrderDual.ofDual a.val.2).comap a.val.1.subtype))
    have hpc : Continuous p := hkc.comp (hc.subtype_mk hmem)
    have hpo : IsOpenMap p := hko.comp (ho.subtype_mk hmem)
    have hk : p.ker ≤ q.toAddEquiv.toAddMonoidHom.ker := by
      intro t ht
      have hqt : (QuotientGroup.mk (j (.ofAdd t)) : a.quotient) = 1 :=
        e.equiv.injective ((show k (j (.ofAdd t)) = 1 from ht).trans (map_one e.equiv).symm)
      have hkernel := (a.quotient_mk_eq_one _).mp hqt
      let m := archimedeanUnitModulation ℝ 1
      have hm : m (expU (.ofAdd t)) = 1 := compactSubgroup_le_modulation_ker m _ (compact_bruhat_kernel a) hkernel
      have ht0 := congrArg (fun v : ℝ≥0ˣ ↦ (v.val : ℝ)) hm
      change ((archimedeanUnitModulation ℝ 1 (expU (.ofAdd t))).val : ℝ) = 1 at ht0
      rw [archimedeanUnitModulation_apply, pow_one] at ht0
      change ‖Real.exp t‖ = 1 at ht0
      rw [Real.norm_of_nonneg (Real.exp_pos t).le] at ht0
      rw [(Real.exp_eq_one_iff t).mp ht0]
      exact q.toAddEquiv.toAddMonoidHom.ker.zero_mem
    obtain ⟨T, hT⟩ := elementarySchwartz_translate_jointly (m := e.realDim) (n := e.torusDim)
      (r := e.latticeRank) (F := e.finiteFactor)
    let v : a.val.1 := ⟨u, hu⟩
    apply elementarySchwartz_of_common_pullback p hpc hpo q.toAddEquiv.toAddMonoidHom q.continuous
      q.toHomeomorph.isOpenMap q.surjective hk (T ((k v).toAdd, s))
    intro t
    rw [hT]
    change s ((k v).toAdd + p t) = schwartzBruhatStageRealization a e s (u * expU (.ofAdd (q.symm (q t))))
    rw [q.symm_apply_apply, schwartzBruhatStageRealization_apply, dite_eq_left (a.val.1.mul_mem hu (hmem _))]
    exact congrArg (fun w ↦ s w.toAdd) (map_mul k v (j (.ofAdd t))).symm
  · have hz (t : ℝ) : schwartzBruhatStageRealization a e s (u * expU (.ofAdd t)) = 0 := by
      rw [schwartzBruhatStageRealization_apply, dite_eq_right ((a.val.1.mul_mem_cancel_right (hmem _)).not.mpr hu)]
    convert (elementarySchwartzSubmodule 1 0 0 PUnit.{1}).zero_mem using 1
    exact funext fun x ↦ hz (q.symm x)

/-- Stagewise restriction assembles into a continuous linear map, since the
source has the final seminorm topology and each stage is Fréchet. -/
private theorem iteratedDeriv_exponentialDecay_elementary_slice (u : ℝˣ)
    (v : ElementaryLieGroup 1 0 0 PUnit.{1} ≃ₜ+ ℝ) :
    ∃ A : SchwartzBruhat ℝˣ →L[ℂ] ElementarySchwartz 1 0 0 PUnit.{1},
      ∀ f x, A f x = f (u * Units.mk0 (Real.exp (v x)) (Real.exp_pos _).ne') := by
  let E := ElementaryLieGroup 1 0 0 PUnit.{1}
  let X := ElementarySchwartz 1 0 0 PUnit.{1}
  let pt (x : E) := u * Units.mk0 (Real.exp (v x)) (Real.exp_pos _).ne'
  let L := LinearMap.funLeft ℂ ℂ pt
  have hmem : schwartzBruhatSubmodule ℝˣ ≤ (elementarySchwartzSubmodule 1 0 0 PUnit.{1}).comap L := by
    unfold schwartzBruhatSubmodule
    apply iSup_le fun a ↦ iSup_le fun e ↦ ?_
    rintro _ ⟨s, rfl⟩
    exact iteratedDeriv_exponentialDecay_stage_slice u v.symm a e s
  let A : SchwartzBruhat ℝˣ →ₗ[ℂ] X :=
    (L.comp (schwartzBruhatSubmodule ℝˣ).subtype).codRestrict _ fun f ↦ hmem f.property
  have hA : Continuous A := by
    let : PolynormableSpace ℂ X := elementarySchwartz_withSeminorms.toPolynormableSpace
    apply continuous_out_of_schwartzBruhat
    intro a e
    let : BarrelledSpace ℂ (SchwartzBruhatStage e) := isFrechetTVS_barrelled elementarySchwartz_isFrechet
    apply continuous_toElementarySchwartz_of_eval (A.comp (schwartzBruhatStageCLM a e).toLinearMap)
    intro x
    let ev := (LinearMap.proj (pt x)).comp (schwartzBruhatStageRealization a e)
    exact ⟨⟨ev, continuous_schwartzBruhatStage_eval a e (pt x)⟩, fun _ ↦ rfl⟩
  exact ⟨⟨A, hA⟩, fun _ _ ↦ rfl⟩

/-- Pulling back along a translate of the exponential gives an ordinary
Schwartz function, continuously and linearly in the Schwartz–Bruhat test. -/
private theorem iteratedDeriv_exponentialDecay_slice (u : ℝˣ) :
    ∃ S : SchwartzBruhat ℝˣ →L[ℂ] 𝓢(ℝ, ℂ),
      ∀ f (t : ℝ), S f t = f (u * Units.mk0 (Real.exp t) (Real.exp_pos t).ne') := by
  classical
  let E := ElementaryLieGroup 1 0 0 PUnit.{1}
  let X := ElementarySchwartz 1 0 0 PUnit.{1}
  let line := realBruhatCoordinate
  let : Unique ((Fin 0 → AddCircle (1 : ℝ)) × (Fin 0 → ℤ) × PUnit.{1}) := uniqueOfSubsingleton 0
  let v : E ≃ₜ+ ℝ := ContinuousAddEquiv.mk' ((Homeomorph.prodUnique _ _).trans line.toHomeomorph)
    (fun x y ↦ line.map_add x.1 y.1)
  refine (iteratedDeriv_exponentialDecay_elementary_slice u v).elim fun A hA ↦ ?_
  refine (elementarySchwartz_real_equiv PUnit.{1}).elim fun T hT ↦ ?_
  refine ⟨T.symm.toContinuousLinearMap.comp A, fun f t ↦ ?_⟩
  let x : E := (line.symm t, 0)
  have hv : v x = t := line.apply_symm_apply t
  calc
    _ = (T (T.symm (A f))) x := ((hT (T.symm (A f)) x).trans (congrArg (⇑(T.symm (A f))) hv)).symm
    _ = A f x := congrArg (fun g : X ↦ g x) (T.apply_symm_apply (A f))
    _ = _ := (hA f x).trans (congrArg (fun z : ℝ ↦ f (u * Units.mk0 (Real.exp z) (Real.exp_pos z).ne')) hv)

/-- If the trivial subgroup gives an admissible stage, its inclusion is surjective,
so the ambient topology is induced by the joint Schwartz–Bruhat twists. -/
private theorem iteratedDeriv_exponentialDecay_inducing_of_bot {G : Type*}
    [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (m : G →ₜ* ℝ≥0ˣ) (I : Set ℝ) (hb : IsCompactlyGeneratedGroup (lcaAnnihilator (⊥ : Subgroup G))) :
    IsInducing (fun (f : ModulatedExponentialDecay m I) (a : I) ↦ modulatedExponentialDecayTwist m I a f) := by
  let E := ModulatedExponentialDecay m I
  let K := {k : Subgroup G // IsCompact (k : Set G) ∧
    IsCompactlyGeneratedGroup (lcaAnnihilator k)}
  let k : K := ⟨⊥, by rw [Subgroup.coe_bot]; exact isCompact_singleton, hb⟩
  let S := ModulatedExponentialDecayStage m I k
  let j : S →ₗ[ℂ] E := modulatedExponentialDecayStageInclusion m I k
  have hj : Continuous j := (withGeneratingSeminorms_spec _ _).continuous_of_continuous_comp
    j fun p ↦ p.property k
  have hsur : Surjective j := fun f ↦ ((modulatedExponentialDecayStageInclusion_range m I k).2 f).mpr
    fun g u ↦ congrArg f.val (by rw [show u.val = 1 from Subgroup.mem_bot.mp u.property, mul_one])
  let e : G ⧸ k.val ≃ₜ* G := QuotientGroup.quotientBot.toContinuousMulEquiv fun _ ↦
    (QuotientGroup.isQuotientMap_mk k.val).isOpen_preimage.symm
  let P := schwartzBruhatPullbackEquiv e
  let T (f : E) (a : I) := modulatedExponentialDecayTwist m I a f
  have hT : Continuous T := continuous_pi (continuous_decay_twist m I)
  let d (F : I → SchwartzBruhat G) (a : I) := P (F a)
  have hd : Continuous d := continuous_pi fun a ↦ P.continuous.comp (continuous_apply a)
  let U (f : S) (a : I) :=
    modulatedExponentialDecayTwist (quotientModulation m k.val k.property.1) I a f
  have hfac : d ∘ (T ∘ j) = U := by
    funext f a
    apply Subtype.ext
    funext q
    exact QuotientGroup.induction_on q fun g ↦ rfl
  have hU : IsInducing U := modulatedExponentialDecayStage_twists_isInducing m I k
  have hcomp : IsInducing (d ∘ (T ∘ j)) := Eq.mpr (congrArg IsInducing hfac) hU
  have hi : IsInducing (T ∘ j) := IsInducing.of_comp (hT.comp hj) hd hcomp
  refine ⟨le_antisymm hT.le_induced (fun V hV ↦ ?_)⟩
  obtain ⟨B, hB, hpre⟩ := hi.isOpen_iff.mp (hV.preimage hj)
  exact isOpen_induced_iff.mpr ⟨B, hB, hsur.preimage_injective hpre⟩

private theorem iteratedDeriv_exponentialDecay_inducing (I : Set ℝ) :
    IsInducing (fun (f : ModulatedExponentialDecay (archimedeanUnitModulation ℝ 1) I) (a : I) ↦
      modulatedExponentialDecayTwist (archimedeanUnitModulation ℝ 1) I a f) :=
  iteratedDeriv_exponentialDecay_inducing_of_bot _ _ iteratedDeriv_exponentialDecay_goodBot

private theorem iteratedDeriv_exponentialDecay_logDeriv (f : ℝ → ℂ) (g : 𝓢(ℝ, ℂ))
    (b x : ℝ) (hx : x ≠ 0) (hg : ∀ᶠ y in 𝓝 x,
      f y = (Real.exp (Real.log y * -b) : ℂ) * g (Real.log y)) :
    ((|x| ^ (b + 1) : ℝ) : ℂ) * deriv f x =
      ((|x| / x : ℝ) : ℂ) * (deriv g (Real.log x) - (b : ℂ) * g (Real.log x)) := by
  have hl := Real.hasDerivAt_log hx
  have hw := ((hl.mul_const (-b)).exp).ofReal_comp
  have hd := ((g.differentiableAt (x := Real.log x)).hasDerivAt.scomp x hl)
  have h := ((hw.fun_mul hd).congr_of_eventuallyEq hg).deriv
  have hcancel : |x| ^ b * Real.exp (Real.log x * -b) = 1 := by
    rw [Real.rpow_def_of_pos (abs_pos.mpr hx), Real.log_abs, ← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  rw [h, Real.rpow_add_one (abs_ne_zero.mpr hx)]
  simp only [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_neg, Complex.ofReal_div,
    Complex.real_smul, Function.comp_apply]
  have hc : ((|x| ^ b : ℝ) : ℂ) * (Real.exp (Real.log x * -b) : ℂ) = 1 := by exact_mod_cast hcancel
  linear_combination ((|x| : ℝ) : ℂ) * (x : ℂ)⁻¹ *
    (deriv g (Real.log x) - (b : ℂ) * g (Real.log x)) * hc

private theorem iteratedDeriv_exponentialDecay_twistFormula (f : ℝˣ → ℂ)
    (g : 𝓢(ℝ, ℂ) × 𝓢(ℝ, ℂ)) (b : ℝ) (hg : ∀ x : ℝˣ,
      (if 0 < x.val then g.1 else g.2) (Real.log x.val) = ((|x.val| ^ b : ℝ) : ℂ) * f x)
    (x : ℝˣ) :
    ((|x.val| ^ (b + 1) : ℝ) : ℂ) * deriv zeroExtension(f) x.val =
      if 0 < x.val then deriv g.1 (Real.log x.val) - b * g.1 (Real.log x.val)
      else -(deriv g.2 (Real.log x.val) - b * g.2 (Real.log x.val)) := by
  have hlocal (y : ℝ) (hy : y ≠ 0) : zeroExtension(f) y =
      (Real.exp (Real.log y * -b) : ℂ) *
        (if 0 < y then g.1 else g.2) (Real.log y) := by
    rw [show (if 0 < y then g.1 else g.2) (Real.log y) = _ from hg (Units.mk0 y hy)]
    simp only [dite_eq_left hy]
    change f _ = _ * (((|y| ^ b : ℝ) : ℂ) * f _)
    rw [Real.rpow_def_of_pos (abs_pos.mpr hy), Real.log_abs, ← mul_assoc, ← Complex.ofReal_mul,
      ← Real.exp_add, show Real.log y * -b + Real.log y * b = 0 by ring]
    simp
  by_cases hx : 0 < x.val
  · rw [ite_eq_left hx]
    have h := iteratedDeriv_exponentialDecay_logDeriv zeroExtension(f) g.1 b x.val x.ne_zero (by
      filter_upwards [lt_mem_nhds hx] with y hy
      simpa only [ite_eq_left hy] using hlocal y hy.ne')
    simpa only [abs_of_pos hx, div_self x.ne_zero, Complex.ofReal_one, one_mul] using h
  · rw [ite_eq_right hx]
    have hx' := lt_of_le_of_ne (le_of_not_gt hx) x.ne_zero
    have h := iteratedDeriv_exponentialDecay_logDeriv zeroExtension(f) g.2 b x.val x.ne_zero (by
      filter_upwards [gt_mem_nhds hx'] with y hy
      simpa only [ite_eq_right hy.not_gt] using hlocal y hy.ne)
    simpa only [abs_of_neg hx', neg_div, div_self x.ne_zero, Complex.ofReal_neg,
      Complex.ofReal_one, neg_one_mul] using h

/-- On the two logarithmic profiles of the twist at exponent \(b\), the twist of the
ordinary derivative at exponent \(b+1\) acts by \(\pm(\partial_t-b)\). -/
private theorem iteratedDeriv_exponentialDecay_onTwist (b : ℝ) :
    ∃ T : SchwartzBruhat ℝˣ →L[ℂ] SchwartzBruhat ℝˣ, ∀ (f : ℝˣ → ℂ) (w : SchwartzBruhat ℝˣ),
      (∀ x, w x = ((|x.val| ^ b : ℝ) : ℂ) * f x) → ∀ x,
        T w x = ((|x.val| ^ (b + 1) : ℝ) : ℂ) * deriv zeroExtension(f) x.val := by
  refine iteratedDeriv_exponentialDecay_assemble.elim fun J hJ ↦ ?_
  refine (iteratedDeriv_exponentialDecay_slice 1).elim fun P hP ↦ ?_
  refine (iteratedDeriv_exponentialDecay_slice (-1)).elim fun N hN ↦ ?_
  let B := SchwartzMap.derivCLM ℂ ℂ - (b : ℂ) • ContinuousLinearMap.id ℂ 𝓢(ℝ, ℂ)
  refine ⟨J.comp ((B.comp P).prod (-(B.comp N))), fun f w hw x ↦ ?_⟩
  have hchart (y : ℝˣ) :
      (if 0 < y.val then P w else N w) (Real.log y.val) = ((|y.val| ^ b : ℝ) : ℂ) * f y := by
    refine Eq.trans ?_ (hw y)
    split_ifs with hy
    · refine (hP w _).trans (congrArg w.val ?_)
      rw [one_mul]
      exact Units.ext (Real.exp_log hy)
    · refine (hN w _).trans (congrArg w.val ?_)
      apply Units.ext
      change -1 * Real.exp (Real.log y.val) = y.val
      rw [Real.exp_log_eq_abs y.ne_zero, abs_of_nonpos (le_of_not_gt hy), neg_one_mul, neg_neg]
  exact (hJ _ x).trans (iteratedDeriv_exponentialDecay_twistFormula f (P w, N w) b hchart x).symm

private theorem iteratedDeriv_exponentialDecay_weight (b : ℝ) (f : ℝˣ → ℂ) (x : ℝˣ) :
    modulationWeight (archimedeanUnitModulation ℝ 1) b f x = ((|x.val| ^ b : ℝ) : ℂ) * f x := by
  change (((((archimedeanUnitModulation ℝ 1 x).val : ℝ) ^ b : ℝ) : ℂ) * f x) = _
  rw [archimedeanUnitModulation_apply, pow_one, Real.norm_eq_abs]

/-- Construct the derivative by untwisting at one output exponent; the coordinate
identities at all exponents give both membership and continuity. -/
private theorem iteratedDeriv_exponentialDecay_step (a : ℝ) :
    ∃ D : 𝓔(ℝ, 1, Ioi a) →L[ℂ] 𝓔(ℝ, 1, Ioi (a + 1)),
      ∀ f x, (D f).val x = deriv zeroExtension(f.val) x.val := by
  let n := archimedeanUnitModulation ℝ 1
  let I := Ioi a
  let J := Ioi (a + 1)
  let E := ModulatedExponentialDecay n I
  let d (f : E) (x : ℝˣ) := deriv zeroExtension(f.val) x.val
  have htwist (c : J) : ∃ U : E →L[ℂ] SchwartzBruhat ℝˣ,
      ∀ f, (U f).val = modulationWeight n c (d f) := by
    let b : I := ⟨c.val - 1, lt_sub_iff_add_lt.mpr c.property⟩
    let W : E →L[ℂ] SchwartzBruhat ℝˣ := ⟨modulatedExponentialDecayTwist n I b,
      (continuous_apply b).comp (iteratedDeriv_exponentialDecay_inducing I).continuous⟩
    refine (iteratedDeriv_exponentialDecay_onTwist b).elim fun T hT ↦ ?_
    refine ⟨T.comp W, fun f ↦ funext fun x ↦ ?_⟩
    have h := hT f.val (W f) (fun y ↦ iteratedDeriv_exponentialDecay_weight b f.val y) x
    refine h.trans ?_
    rw [show (b : ℝ) + 1 = c.val from sub_add_cancel _ _, iteratedDeriv_exponentialDecay_weight]
  let c₀ : J := ⟨a + 1 + 1, lt_add_one _⟩
  let U := (htwist c₀).choose
  let L : E →ₗ[ℂ] (ℝˣ → ℂ) := (modulationWeight n (-c₀.val)).comp
    ((schwartzBruhatSubmodule ℝˣ).subtype.comp U.toLinearMap)
  have hL (f : E) : L f = d f := by
    funext x
    change modulationWeight n (-c₀.val) (U f).val x = _
    rw [(htwist c₀).choose_spec f, iteratedDeriv_exponentialDecay_weight,
      iteratedDeriv_exponentialDecay_weight, ← mul_assoc, ← Complex.ofReal_mul,
      ← Real.rpow_add (abs_pos.mpr x.ne_zero), neg_add_cancel, Real.rpow_zero, Complex.ofReal_one, one_mul]
  let D := L.codRestrict (modulatedExponentialDecaySubmodule n J) fun f ↦
    (Submodule.mem_iInf _).mpr fun c ↦ Submodule.mem_comap.mpr (by
      change modulationWeight n c (L f) ∈ schwartzBruhatSubmodule ℝˣ
      rw [hL f, ← (htwist c).choose_spec f]
      exact ((htwist c).choose f).property)
  refine ⟨⟨D, (iteratedDeriv_exponentialDecay_inducing J).continuous_iff.mpr (continuous_pi fun c ↦ ?_)⟩, fun f ↦ congrFun (hL f)⟩
  exact (htwist c).choose.continuous.congr fun f ↦ Subtype.ext
    (((htwist c).choose_spec f).trans (congrArg (modulationWeight n c) (hL f).symm))

private theorem iteratedDeriv_exponentialDecay_succ (m : ℕ) (g : ℝˣ → ℂ) (F : ℝ → ℂ)
    (hg : ∀ x : ℝˣ, g x = iteratedDeriv m F x.val) (x : ℝˣ) :
    deriv zeroExtension(g) x.val = iteratedDeriv (m + 1) F x.val := by
  rw [iteratedDeriv_succ]
  apply EventuallyEq.deriv_eq
  filter_upwards [isOpen_compl_singleton.mem_nhds (show x.val ∈ ({0}ᶜ : Set ℝ) from x.ne_zero)] with y hy
  exact (dite_eq_left (show y ≠ 0 from hy)).trans (hg (Units.mk0 y hy))

/-- Paper: Proposition 5.3.3.2(2)(1), p. 249.
An ordinary derivative of order m shifts the lower endpoint of the decay interval by m. -/
theorem iteratedDeriv_exponentialDecay (m : ℕ) (a : ℝ) :
    ∃ D : 𝓔(ℝ, 1, Ioi a) →L[ℂ] 𝓔(ℝ, 1, Ioi (a + m)),
      ∀ f x, (D f).val x = iteratedDeriv m zeroExtension(f.val) x.val := by
  let P (k : ℕ) (b : ℝ) := ∃ D : 𝓔(ℝ, 1, Ioi a) →L[ℂ] 𝓔(ℝ, 1, Ioi b),
    ∀ f x, (D f).val x = iteratedDeriv k zeroExtension(f.val) x.val
  change P m (a + m)
  induction m with
  | zero =>
    rw [Nat.cast_zero, add_zero]
    refine ⟨ContinuousLinearMap.id ℂ _, fun f x ↦ ?_⟩
    change f.val x = iteratedDeriv 0 _ x.val
    simp only [iteratedDeriv_zero, dite_eq_left x.ne_zero]
    exact congrArg f.val (Units.ext rfl)
  | succ m ih =>
    rw [Nat.cast_succ, ← add_assoc]
    refine ih.elim fun A hA ↦ ?_
    refine (iteratedDeriv_exponentialDecay_step (a + m)).elim fun B hB ↦ ?_
    refine ⟨B.comp A, fun f x ↦ ?_⟩
    refine (hB (A f) x).trans ?_
    exact iteratedDeriv_exponentialDecay_succ m (A f).val zeroExtension(f.val) (hA f) x

-- TODO(paper-gap): The first Wirtinger operator in the printed weighted shift is
-- missing the exponent m. The proof uses m derivatives for both operators.

/-- Paper: Proposition 5.3.3.2(2)(2), p. 250.
Either iterated Wirtinger derivative gives a continuous operator into the indicated decay space.
Deviation: Both derivatives have order m, as in the proof. The stated target with shift m is
retained, although the squared norm permits a shift of m/2. -/
theorem iteratedWirtinger_exponentialDecay (conjugate : Bool) (m : ℕ) {a : ℝ} (_ha : a < 0) :
    ∃ D : 𝓔(ℂ, 2, Ioi a) →L[ℂ] 𝓔(ℂ, 2, Ioi (a + m)),
      ∀ f z, (D f).val z = ((wirtinger(conjugate))^[m] zeroExtension(f.val)) z.val := by sorry

/-- Every output weight of the derivative comes from the input weight one lower;
the initial topology of all twists makes this a continuous endomorphism. -/
private theorem iteratedDeriv_allExponentialDecay_step :
    ∃ D : 𝓔(ℝ, 1, univ) →L[ℂ] 𝓔(ℝ, 1, univ),
      ∀ f x, (D f).val x = deriv zeroExtension(f.val) x.val := by
  let n := archimedeanUnitModulation ℝ 1
  let I : Set ℝ := univ
  let J : Set ℝ := univ
  let E := ModulatedExponentialDecay n I
  let d (f : E) (x : ℝˣ) := deriv zeroExtension(f.val) x.val
  have htwist (c : J) : ∃ U : E →L[ℂ] SchwartzBruhat ℝˣ,
      ∀ f, (U f).val = modulationWeight n c (d f) := by
    let b : I := ⟨c.val - 1, mem_univ _⟩
    let W : E →L[ℂ] SchwartzBruhat ℝˣ := ⟨modulatedExponentialDecayTwist n I b,
      (continuous_apply b).comp (iteratedDeriv_exponentialDecay_inducing I).continuous⟩
    refine (iteratedDeriv_exponentialDecay_onTwist b).elim fun T hT ↦ ?_
    refine ⟨T.comp W, fun f ↦ funext fun x ↦ ?_⟩
    have h := hT f.val (W f) (fun y ↦ iteratedDeriv_exponentialDecay_weight b f.val y) x
    refine h.trans ?_
    rw [show (b : ℝ) + 1 = c.val from sub_add_cancel _ _, iteratedDeriv_exponentialDecay_weight]
  let c₀ : J := ⟨0, mem_univ _⟩
  let U := (htwist c₀).choose
  let L : E →ₗ[ℂ] (ℝˣ → ℂ) := (modulationWeight n (-c₀.val)).comp
    ((schwartzBruhatSubmodule ℝˣ).subtype.comp U.toLinearMap)
  have hL (f : E) : L f = d f := by
    funext x
    change modulationWeight n (-c₀.val) (U f).val x = _
    rw [(htwist c₀).choose_spec f, iteratedDeriv_exponentialDecay_weight,
      iteratedDeriv_exponentialDecay_weight, ← mul_assoc, ← Complex.ofReal_mul,
      ← Real.rpow_add (abs_pos.mpr x.ne_zero), neg_add_cancel, Real.rpow_zero, Complex.ofReal_one, one_mul]
  let D := L.codRestrict (modulatedExponentialDecaySubmodule n J) fun f ↦
    (Submodule.mem_iInf _).mpr fun c ↦ Submodule.mem_comap.mpr (by
      change modulationWeight n c (L f) ∈ schwartzBruhatSubmodule ℝˣ
      rw [hL f, ← (htwist c).choose_spec f]
      exact ((htwist c).choose f).property)
  refine ⟨⟨D, (iteratedDeriv_exponentialDecay_inducing J).continuous_iff.mpr (continuous_pi fun c ↦ ?_)⟩, fun f ↦ congrFun (hL f)⟩
  exact (htwist c).choose.continuous.congr fun f ↦ Subtype.ext
    (((htwist c).choose_spec f).trans (congrArg (modulationWeight n c) (hL f).symm))

/-- Paper: Proposition 5.3.3.2(2)(1), p. 249.
Ordinary derivatives act continuously on the punctured real space with decay at all exponents. -/
theorem iteratedDeriv_allExponentialDecay (m : ℕ) :
    ∃ D : 𝓔(ℝ, 1, univ) →L[ℂ] 𝓔(ℝ, 1, univ),
      ∀ f x, (D f).val x = iteratedDeriv m zeroExtension(f.val) x.val := by
  induction m with
  | zero =>
    refine ⟨ContinuousLinearMap.id ℂ _, fun f x ↦ ?_⟩
    change f.val x = iteratedDeriv 0 _ x.val
    simp only [iteratedDeriv_zero, dite_eq_left x.ne_zero]
    exact congrArg f.val (Units.ext rfl)
  | succ m ih =>
    obtain ⟨A, hA⟩ := ih
    obtain ⟨B, hB⟩ := iteratedDeriv_allExponentialDecay_step
    refine ⟨B.comp A, fun f x ↦ ?_⟩
    exact (hB (A f) x).trans
      (iteratedDeriv_exponentialDecay_succ m (A f).val zeroExtension(f.val) (hA f) x)

/-- Paper: Proposition 5.3.3.2(2)(2), p. 250.
Both iterated Wirtinger operators preserve the punctured complex space with decay at all
exponents and act continuously there. -/
theorem iteratedWirtinger_allExponentialDecay (conjugate : Bool) (m : ℕ) :
    ∃ D : 𝓔(ℂ, 2, univ) →L[ℂ] 𝓔(ℂ, 2, univ),
      ∀ f z, (D f).val z = ((wirtinger(conjugate))^[m] zeroExtension(f.val)) z.val := by sorry

/-- In exponential coordinates, the realization of a Schwartz–Bruhat stage is
smooth along every translate of a continuous homomorphism from a real vector space. -/
private theorem complexExponentialDecay_contDiffOn_alongTranslate {K G : Type*}
    [NormedAddCommGroup K] [NormedSpace ℝ K] [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (U : Multiplicative K →ₜ* G) (f : SchwartzBruhat G) (u : G) :
    ContDiff ℝ (∞ : ℕ∞ω) (fun t : K ↦ f (U (Multiplicative.ofAdd t) * u)) := by
  obtain ⟨p, e, s, hs⟩ := (mem_schwartzBruhatSubmodule_iff f.val).mp f.property
  let H := p.val.1
  have hU : Continuous (fun t : K ↦ U (Multiplicative.ofAdd t)) := U.continuous
  have hpre : IsClopen ((fun t : K ↦ U (Multiplicative.ofAdd t)) ⁻¹' (H : Set G)) :=
    (show IsClopen (H : Set G) from ⟨H.isClosed_of_isOpen p.property.1, p.property.1⟩).preimage hU
  have hfull := hpre.eq_univ ⟨0, by change U 1 ∈ H; simp⟩
  have hmem (t : Multiplicative K) : U t ∈ H := by
    change t.toAdd ∈ (fun v : K ↦ U (Multiplicative.ofAdd v)) ⁻¹' (H : Set G)
    rw [hfull]
    exact mem_univ _
  let UH : Multiplicative K →* H := U.toMonoidHom.codRestrict H hmem
  by_cases hu : u ∈ H
  · let q : H →* p.quotient := QuotientGroup.mk' _
    let a := AddMonoidHom.toMultiplicative.symm
      (e.equiv.toMulEquiv.toMonoidHom.comp (q.comp UH))
    let c := Multiplicative.toAdd (e.equiv (q ⟨u, hu⟩))
    have ha : Continuous a := e.equiv.continuous.comp
      (QuotientGroup.continuous_mk.comp (hU.subtype_mk _))
    have heq (t : K) : f (U (Multiplicative.ofAdd t) * u) = s (a t + c) := by
      rw [← show schwartzBruhatStageRealization p e s = f.val from hs,
        schwartzBruhatStageRealization_apply, dite_eq_left (H.mul_mem (hmem _) hu)]
      change s (Multiplicative.toAdd (e.equiv (q (UH (Multiplicative.ofAdd t) * ⟨u, hu⟩)))) = _
      rw [map_mul, map_mul]
      rfl
    rw [funext heq]
    exact contDiff_comp_affine_elementary a ha c s.property.1
  · have heq (t : K) : f (U (Multiplicative.ofAdd t) * u) = 0 := by
      have hnot : U (Multiplicative.ofAdd t) * u ∉ H := by
        intro h
        exact hu (H.mul_mem_cancel_left (hmem _) |>.mp h)
      rw [← show schwartzBruhatStageRealization p e s = f.val from hs,
        schwartzBruhatStageRealization_apply, dite_eq_right hnot]
    rw [funext heq]
    exact contDiff_const

/-- The local inverse of the Banach-algebra exponential transfers smoothness in
multiplicative coordinates to smoothness in the punctured field. -/
private theorem complexExponentialDecay_contDiffOn_unitsChart {K : Type*} [NormedField K] [NormedAlgebra ℝ K]
    [CompleteSpace K] [LocallyCompactSpace K] [DecidableEq K] (f : SchwartzBruhat Kˣ) :
    ContDiffOn ℝ (∞ : ℕ∞ω) zeroExtension(f.val) ({0}ᶜ : Set K) := by
  let +nondep : NormedAlgebra ℚ K := .restrictScalars ℚ ℝ K
  let U : Multiplicative K →ₜ* Kˣ :=
    { toFun := fun v ↦ ⟨NormedSpace.exp v.toAdd, NormedSpace.exp (-v.toAdd),
        by rw [← NormedSpace.exp_add, add_neg_cancel, NormedSpace.exp_zero],
        by rw [← NormedSpace.exp_add, neg_add_cancel, NormedSpace.exp_zero]⟩
      map_one' := Units.ext NormedSpace.exp_zero
      map_mul' := fun x y ↦ Units.ext NormedSpace.exp_add
      continuous_toFun := Units.isOpenEmbedding_val.isInducing.continuous_iff.mpr
        ((show Continuous (NormedSpace.exp : K → K) from NormedSpace.exp_continuous).comp
          (show Continuous (Multiplicative.toAdd : Multiplicative K → K) from continuous_id)) }
  let : LocallyCompactSpace Kˣ := (IsOpenUnits.isOpenEmbedding_unitsVal (M := K)).locallyCompactSpace
  have hExp : ContDiffAt ℝ (∞ : ℕ∞ω) (NormedSpace.exp : K → K) 0 :=
    (NormedSpace.exp_analytic (𝕂 := ℝ) (x := (0 : K))).contDiffAt
  let L := ContinuousLinearEquiv.refl ℝ K
  have hD : HasFDerivAt NormedSpace.exp (L : K →L[ℝ] K) 0 := hasFDerivAt_exp_zero
  let log := hExp.localInverse (f' := L) hD (by simp)
  have hlog : ContDiffAt ℝ (∞ : ℕ∞ω) log 1 := by
    simpa only [NormedSpace.exp_zero] using hExp.to_localInverse (f' := L) hD (by simp)
  have hright : ∀ᶠ y : K in 𝓝 1, NormedSpace.exp (log y) = y := by
    unfold log ContDiffAt.localInverse
    simpa only [NormedSpace.exp_zero] using
      (hExp.hasStrictFDerivAt (f' := L) hD (by simp)).eventually_right_inverse
  intro x hx
  have hx0 : x ≠ 0 := hx
  let u := Units.mk0 x hx0
  have hp : ContDiff ℝ (∞ : ℕ∞ω) (fun y : K ↦ y / x) := contDiff_id.div_const x
  have hp0 : x / x = 1 := div_self hx0
  have hlogx : ContDiffAt ℝ (∞ : ℕ∞ω) log (x / x) := by rw [hp0]; exact hlog
  have hg := complexExponentialDecay_contDiffOn_alongTranslate U f u
  have hc : ContDiffAt ℝ (∞ : ℕ∞ω)
      (fun y : K ↦ f (U (Multiplicative.ofAdd (log (y / x))) * u)) x :=
    hg.contDiffAt.comp x (hlogx.comp (f := fun y : K ↦ y / x) (g := log) x hp.contDiffAt)
  apply ContDiffAt.contDiffWithinAt
  apply hc.congr_of_eventuallyEq
  have hnear : Tendsto (fun y : K ↦ y / x) (𝓝 x) (𝓝 1) :=
    hp0 ▸ hp.continuous.continuousAt
  filter_upwards [hnear.eventually hright, isOpen_compl_singleton.mem_nhds hx] with y hy hy0
  have hunit : U (Multiplicative.ofAdd (log (y / x))) * u = Units.mk0 y hy0 := by
    apply Units.ext
    change NormedSpace.exp (log (y / x)) * x = y
    rw [hy, div_mul_cancel₀ _ hx0]
  have hy0' : y ≠ 0 := hy0
  simp only [hunit, dite_eq_left hy0']

/-- Dividing a positive weighted Schwartz–Bruhat twist by its smooth nonzero
weight recovers the original function on the punctured field. -/
private theorem complexExponentialDecay_contDiffOn_of_weight {K : Type*} [NormedField K]
    [NormedAlgebra ℝ K] [CompleteSpace K] [LocallyCompactSpace K] [DecidableEq K]
    (m : Kˣ →ₜ* ℝ≥0ˣ) (a : ℝ) (ha : a ∈ Ioi (0 : ℝ))
    (f : ModulatedExponentialDecay m (Ioi (0 : ℝ)))
    (w : K → ℂ) (hw : ContDiff ℝ (∞ : ℕ∞ω) w)
    (hwu : ∀ u : Kˣ, w u.val = (((m u).val : ℝ) ^ a : ℝ)) :
    ContDiffOn ℝ (∞ : ℕ∞ω) zeroExtension(f.val) ({0}ᶜ : Set K) := by
  let g := modulatedExponentialDecayTwist m (Ioi (0 : ℝ)) ⟨a, ha⟩ f
  have hn (x : K) (hx : x ≠ 0) : w x ≠ 0 := by
    change w (Units.mk0 x hx).val ≠ 0
    rw [hwu]
    exact Complex.ofReal_ne_zero.mpr
      (Real.rpow_pos_of_pos (NNReal.coe_pos.mpr (Units.zero_lt _)) _).ne'
  have h := (complexExponentialDecay_contDiffOn_unitsChart g).mul (hw.contDiffOn.inv fun x hx ↦ hn x hx)
  apply h.congr
  intro x hx
  have hx0 : x ≠ 0 := hx
  let u := Units.mk0 x hx0
  simp only [dite_eq_left hx0, Pi.inv_apply]
  have hg : g.val u = w x * f.val u :=
    (modulatedExponentialDecayTwist_apply m _ _ f u).trans (by rw [← hwu]; rfl)
  change f.val u = g.val u * (w x)⁻¹
  rw [hg, mul_right_comm, mul_inv_cancel₀ (hn x hx0), one_mul]

/-- Paper: Proposition 5.3.3.2(2)(1), p. 250.
Weighted Schwartz–Bruhat functions are smooth on the punctured real line. -/
theorem realExponentialDecay_contDiffOn (f : 𝓔(ℝ, 1, Ioi 0)) :
    ContDiffOn ℝ (∞ : ℕ∞ω) zeroExtension(f.val) ({0}ᶜ : Set ℝ) := by
  apply complexExponentialDecay_contDiffOn_of_weight (archimedeanUnitModulation ℝ 1) 2
    (by norm_num : (2 : ℝ) ∈ Ioi 0) f (fun x ↦ ((x ^ 2 : ℝ) : ℂ))
    (Complex.ofRealCLM.contDiff.comp (contDiff_id.pow 2))
  intro u
  rw [archimedeanUnitModulation_apply, pow_one, Real.norm_eq_abs, Real.rpow_two, sq_abs]

/-- Paper: Proposition 5.3.3.2(2)(2), p. 250.
Weighted Schwartz–Bruhat functions are smooth on the punctured complex plane
as functions of two real variables. -/
theorem complexExponentialDecay_contDiffOn (f : 𝓔(ℂ, 2, Ioi 0)) :
    ContDiffOn ℝ (∞ : ℕ∞ω) zeroExtension(f.val) ({0}ᶜ : Set ℂ) := by
  have hRe : ContDiff ℝ (∞ : ℕ∞ω) Complex.re := Complex.reCLM.contDiff
  have hIm : ContDiff ℝ (∞ : ℕ∞ω) Complex.im := Complex.imCLM.contDiff
  have hn : ContDiff ℝ (∞ : ℕ∞ω) (fun z : ℂ ↦ Complex.normSq z) := by
    simp only [Complex.normSq_apply]
    exact (hRe.mul hRe).add (hIm.mul hIm)
  apply complexExponentialDecay_contDiffOn_of_weight (archimedeanUnitModulation ℂ 2) 1
    (by norm_num : (1 : ℝ) ∈ Ioi 0) f (fun z ↦ (Complex.normSq z : ℂ))
    (Complex.ofRealCLM.contDiff.comp hn)
  intro u
  rw [archimedeanUnitModulation_apply, Real.rpow_one, Complex.normSq_eq_norm_sq]

end PuncturedLine

section ArchimedeanProduct

attribute [local instance] uniformContinuousConstSMul_of_continuousConstSMul

local notation "archAdd(" ι ", " κ ")" => ((ι → ℝ) × (κ → ℂ))
local notation "archMul(" ι ", " κ ")" => ((ι → ℝˣ) × (κ → ℂˣ))
local notation "archVal" => fun u ↦ (fun i ↦ (u.1 i).val, fun j ↦ (u.2 j).val)
local notation "meetsWall(" x ")" => ((∃ i, x.1 i = 0) ∨ (∃ j, x.2 j = 0))
local notation "weights(" ι ", " κ ", " I ")" =>
  ((ι → (insert 0 I : Set ℝ)) × (κ → (insert 0 I : Set ℝ)))

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

local notation "weightMap(" a ")" => LinearMap.mulLeft ℂ
  (fun u : archMul(ι, κ) ↦
    ((∏ i, ‖(u.1 i).val‖ ^ (a.1 i : ℝ)) : ℝ) *
    ((∏ j, (‖(u.2 j).val‖ ^ (2 : ℕ)) ^ (a.2 j : ℝ)) : ℝ) : archMul(ι, κ) → ℂ)

/-- Paper: Lemma 5.3.3.3, p. 252.
Every partial coordinate weight with exponents in I must yield a Schwartz–Bruhat function.
Deviation: A zero exponent encodes an omitted coordinate in (5.3.3.5), including the
unweighted condition when every coordinate is omitted. -/
def archimedeanWeightedSchwartzSubmodule (I : Set ℝ) :
    Submodule ℂ (archMul(ι, κ) → ℂ) :=
  ⨅ a : weights(ι, κ, I), (schwartzBruhatSubmodule _).comap (weightMap(a))

/-- Paper: Lemma 5.3.3.3, p. 252.
The map for a family of exponents applies its weight and returns a Schwartz–Bruhat function. -/
def archimedeanSchwartzTwist (I : Set ℝ) (a : weights(ι, κ, I)) :
    archimedeanWeightedSchwartzSubmodule (ι := ι) (κ := κ) I →ₗ[ℂ]
      SchwartzBruhat (archMul(ι, κ)) :=
  ((weightMap(a)).comp (archimedeanWeightedSchwartzSubmodule I).subtype).codRestrict
    (schwartzBruhatSubmodule _) (fun f ↦
      Submodule.mem_comap.1 ((Submodule.mem_iInf _).1 f.property a))

/-- Paper: Lemma 5.3.3.3, p. 252.
The twist uses one power of the real norm and the corresponding power of the squared
complex norm in each coordinate. -/
theorem archimedeanSchwartzTwist_apply (I : Set ℝ) (a : weights(ι, κ, I))
    (f : archimedeanWeightedSchwartzSubmodule (ι := ι) (κ := κ) I)
    (u : archMul(ι, κ)) :
    archimedeanSchwartzTwist I a f u =
      (↑(∏ i, ‖(u.1 i).val‖ ^ (a.1 i : ℝ)) : ℂ) *
      (↑(∏ j, (‖(u.2 j).val‖ ^ (2 : ℕ)) ^ (a.2 j : ℝ)) : ℂ) * f.val u := by
  rfl

/-- Paper: Lemma 5.3.3.3, p. 252.
On both the real and complex coordinates, choosing only zero exponents gives the
unweighted Schwartz–Bruhat space. -/
theorem archimedeanWeightedSchwartzSubmodule_singleton_zero :
    archimedeanWeightedSchwartzSubmodule (ι := ι) (κ := κ) {0} =
      schwartzBruhatSubmodule (archMul(ι, κ)) := by
  have hw : ∀ a : weights(ι, κ, ({0} : Set ℝ)), ∀ f : archMul(ι, κ) → ℂ, weightMap(a) f = f := by
    intro a f
    have h1 : ∀ i, (a.1 i : ℝ) = 0 := fun i ↦ by simpa using (a.1 i).property
    have h2 : ∀ j, (a.2 j : ℝ) = 0 := fun j ↦ by simpa using (a.2 j).property
    funext u
    simp [h1, h2]
  ext f
  simp only [archimedeanWeightedSchwartzSubmodule, Submodule.mem_iInf, Submodule.mem_comap]
  constructor
  · intro h
    have := h (fun _ ↦ ⟨0, by simp⟩, fun _ ↦ ⟨0, by simp⟩)
    rwa [hw] at this
  · intro h a
    rwa [hw]

/-- Paper: Lemma 5.3.3.3, p. 252.
The topology is the initial locally convex topology for all the partial weight maps into
the Schwartz–Bruhat space in (5.3.3.8).

This is a `def` with its own instances, not an `abbrev`, so that instance terms over it do
not spell out its seminorm family (#5398). -/
def ArchimedeanWeightedSchwartz (I : Set ℝ) :=
  WithGeneratingSeminorms (archimedeanWeightedSchwartzSubmodule (ι := ι) (κ := κ) I)
    (fun i : weights(ι, κ, I) ×
      {p : Seminorm ℂ (SchwartzBruhat (archMul(ι, κ))) // Continuous p} ↦
      i.2.val.comp (archimedeanSchwartzTwist I i.1))

namespace ArchimedeanWeightedSchwartz

variable (I : Set ℝ)

instance instAddCommGroup : AddCommGroup (ArchimedeanWeightedSchwartz (ι := ι) (κ := κ) I) :=
  inferInstanceAs (AddCommGroup (WithGeneratingSeminorms
    (archimedeanWeightedSchwartzSubmodule (ι := ι) (κ := κ) I) _))

instance instModule : Module ℂ (ArchimedeanWeightedSchwartz (ι := ι) (κ := κ) I) :=
  inferInstanceAs (Module ℂ (WithGeneratingSeminorms
    (archimedeanWeightedSchwartzSubmodule (ι := ι) (κ := κ) I) _))

instance instTopologicalSpace :
    TopologicalSpace (ArchimedeanWeightedSchwartz (ι := ι) (κ := κ) I) :=
  inferInstanceAs (TopologicalSpace (WithGeneratingSeminorms
    (archimedeanWeightedSchwartzSubmodule (ι := ι) (κ := κ) I) _))

instance instPolynormableSpace :
    PolynormableSpace ℂ (ArchimedeanWeightedSchwartz (ι := ι) (κ := κ) I) :=
  inferInstanceAs (PolynormableSpace ℂ (WithGeneratingSeminorms
    (archimedeanWeightedSchwartzSubmodule (ι := ι) (κ := κ) I) _))

instance instIsTopologicalAddGroup :
    IsTopologicalAddGroup (ArchimedeanWeightedSchwartz (ι := ι) (κ := κ) I) :=
  inferInstanceAs (IsTopologicalAddGroup (WithGeneratingSeminorms
    (archimedeanWeightedSchwartzSubmodule (ι := ι) (κ := κ) I) _))

instance instUniformSpace : UniformSpace (ArchimedeanWeightedSchwartz (ι := ι) (κ := κ) I) :=
  inferInstanceAs (UniformSpace (WithGeneratingSeminorms
    (archimedeanWeightedSchwartzSubmodule (ι := ι) (κ := κ) I) _))

instance instIsUniformAddGroup :
    IsUniformAddGroup (ArchimedeanWeightedSchwartz (ι := ι) (κ := κ) I) :=
  inferInstanceAs (IsUniformAddGroup (WithGeneratingSeminorms
    (archimedeanWeightedSchwartzSubmodule (ι := ι) (κ := κ) I) _))

end ArchimedeanWeightedSchwartz

local notation "𝓦(" I ")" => ArchimedeanWeightedSchwartz (ι := ι) (κ := κ) I

/-- Paper: Lemma 5.3.3.3, p. 252.
When there are no coordinates, the weighted Schwartz space is the scalar field. -/
theorem archimedeanWeightedSchwartz_empty_equiv (I : Set ℝ) :
    ∃ e : ArchimedeanWeightedSchwartz (ι := Empty) (κ := Empty) I ≃L[ℂ] ℂ,
      ∀ f, e f = f.val (1 : archMul(Empty, Empty)) := by
  classical
  let G := archMul(Empty, Empty)
  let W := weights(Empty, Empty, I)
  let E := archimedeanWeightedSchwartzSubmodule (ι := Empty) (κ := Empty) I
  let P : SeminormFamily ℂ E (W × {p : Seminorm ℂ (SchwartzBruhat G) // Continuous p}) :=
    fun i ↦ i.2.val.comp (archimedeanSchwartzTwist I i.1)
  let X := WithGeneratingSeminorms E P
  let a : W := (Empty.elim, Empty.elim)
  have htwist (b : W) (f : E) (u : G) : archimedeanSchwartzTwist I b f u = f.val u := by
    simp [archimedeanSchwartzTwist_apply]
  obtain ⟨f, hf, _⟩ := schwartzBruhat_exists_test (1 : G) 1
  let f₀ : E := ⟨f.val, by
    apply (Submodule.mem_iInf _).mpr
    intro b
    change (fun u : G ↦ _ * _ * f.val u) ∈ schwartzBruhatSubmodule G
    simpa using f.property⟩
  let L : X →ₗ[ℂ] ℂ := (LinearMap.proj (1 : G)).comp E.subtype
  have hL : Bijective L := by
    constructor
    · intro f g h
      apply Subtype.ext
      funext u
      exact (congrArg f.val (Subsingleton.elim u 1)).trans
        (h.trans (congrArg g.val (Subsingleton.elim 1 u)))
    · intro c
      refine ⟨(c / f 1) • f₀, ?_⟩
      change (c / f 1) * f 1 = c
      exact div_mul_cancel₀ c hf
  let e : X ≃ₗ[ℂ] ℂ := LinearEquiv.ofBijective L hL
  have hP := withGeneratingSeminorms_spec E P
  let : ContinuousSMul ℂ X := hP.continuousSMul
  have he : Continuous e := by
    let ev : SchwartzBruhat G →ₗ[ℂ] ℂ := (LinearMap.proj (1 : G)).comp (schwartzBruhatSubmodule G).subtype
    let q : Seminorm ℂ (SchwartzBruhat G) := (normSeminorm ℂ ℂ).comp ev
    have hq : Continuous q := (continuous_schwartzBruhat_eval_forEndpoints (1 : G)).norm
    apply (norm_withSeminorms ℂ ℂ).continuous_of_continuous_comp e.toLinearMap
    intro _
    exact (hP.continuous_seminorm (a, ⟨q, hq⟩)).congr (fun f ↦ by
      change ‖archimedeanSchwartzTwist I a f 1‖ = ‖f.val 1‖
      exact congrArg norm (htwist a f 1))
  have he' : Continuous e.symm := by
    have h : (e.symm : ℂ → X) = fun c ↦ c • e.symm 1 := by
      funext c
      rw [← map_smul, smul_eq_mul, mul_one]
    rw [h]
    fun_prop
  exact ⟨⟨e, he, he'⟩, fun _ ↦ rfl⟩

-- TODO(paper-gap): The proof's integer exponents need not meet I. Use a countable
-- family of exponents in I bracketing each exponent in I, together with zero.

/-- Paper: Lemma 5.3.3.3(1), p. 252.
For an open nonempty interval the topology from the partial weight maps is Fréchet. -/
theorem archimedeanWeightedSchwartz_frechet {I : Set ℝ} (_ho : IsOpen I)
    (_hi : OrdConnected I) (_hne : I.Nonempty) : IsFrechetTVS 𝓦(I) := by sorry

/-- Paper: Lemma 5.3.3.3(1), p. 252.
For an open nonempty interval the weighted Schwartz–Bruhat space is separable. -/
theorem archimedeanWeightedSchwartz_separable {I : Set ℝ} (_ho : IsOpen I)
    (_hi : OrdConnected I) (_hne : I.Nonempty) : SeparableSpace 𝓦(I) := by
  classical
  have sep {E : Type _} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
      [FirstCountableTopology E] (h : IsNuclearTVS.{0} E) : SeparableSpace E := by
    let := h.1
    let := h.2.1
    let := PolynormableSpace.isTopologicalAddGroup ℂ E
    have hw := PolynormableSpace.withSeminorms ℂ E
    let : ContinuousSMul ℂ E := hw.continuousSMul
    obtain ⟨U, hU⟩ := (𝓝 (0 : E)).exists_antitone_basis
    have hex (n : ℕ) : ∃ q : Seminorm ℂ E, Continuous q ∧ ∃ r > 0, q.ball 0 r ⊆ U n := by
      obtain ⟨s, r, hr, hsub⟩ := (hw.mem_nhds_iff 0 (U n)).mp (hU.mem n)
      refine ⟨s.sup fun p : {p : Seminorm ℂ E // Continuous p} ↦ p.1, ?_, r, hr, hsub⟩
      exact hw.continuous_finsetSup_seminorm s
    choose q hq r hr hsub using hex
    have hsep (n : ℕ) : SeparableSpace (WithLocalSeminorm (q n)) :=
      seminorm_separable_of_nuclear h (q n) (hq n)
    have hd (n : ℕ) : ∃ d : ℕ → E, ∀ x : E, ∃ m, q n (x - d m) < r n := by
      obtain ⟨d, hd⟩ := exists_dense_seq (WithLocalSeminorm (q n))
      refine ⟨d, fun x ↦ ?_⟩
      let x' : WithLocalSeminorm (q n) := x
      obtain ⟨m, hm⟩ := hd.exists_dist_lt x' (hr n)
      rw [dist_eq_norm] at hm
      exact ⟨m, hm⟩
    choose d hd using hd
    refine ⟨range fun m : ℕ × ℕ ↦ d m.1 m.2, countable_range _, ?_⟩
    intro x
    rw [mem_closure_iff_nhds]
    intro W hW
    have hW0 : (fun y ↦ x + y) ⁻¹' W ∈ 𝓝 (0 : E) :=
      (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds (by simpa using hW)
    obtain ⟨n, -, hn⟩ := hU.1.mem_iff.mp hW0
    obtain ⟨m, hm⟩ := hd n x
    refine ⟨d n m, ?_, ⟨(n, m), rfl⟩⟩
    have : d n m - x ∈ U n := hsub n (by rw [Seminorm.mem_ball, sub_zero, map_sub_rev]; exact hm)
    simpa using hn this
  let : SecondCountableTopology ℝˣ := Units.isEmbedding_val₀.secondCountableTopology
  let : SecondCountableTopology ℂˣ := Units.isEmbedding_val₀.secondCountableTopology
  let X := SchwartzBruhat (archMul(ι, κ))
  let Z := weights(ι, κ, I)
  let t : 𝓦(I) →ₗ[ℂ] (Z → X) := LinearMap.pi (archimedeanSchwartzTwist I)
  let : PolynormableSpace ℂ X := (schwartzBruhat_nuclear.{0} (G := archMul(ι, κ))).2.1
  have hp := withSeminorms_pi fun _ : Z ↦ PolynormableSpace.withSeminorms ℂ X
  have hs := withGeneratingSeminorms_spec (archimedeanWeightedSchwartzSubmodule (ι := ι) (κ := κ) I)
    (fun i : Z × {p : Seminorm ℂ X // Continuous p} ↦ i.2.val.comp (archimedeanSchwartzTwist I i.1))
  have ht : Topology.IsEmbedding t := by
    constructor
    · constructor
      refine hs.topologicalSpace_eq_iInf.trans ?_
      refine Eq.trans ?_ (WithSeminorms.topologicalSpace_eq_iInf
        (t := TopologicalSpace.induced t inferInstance) (t.withSeminorms_induced hp)).symm
      rw [iInf_sigma, iInf_prod]
      rfl
    · intro f g h
      let a : Z := (fun _ ↦ ⟨0, Set.mem_insert _ _⟩, fun _ ↦ ⟨0, Set.mem_insert _ _⟩)
      apply Subtype.ext
      funext u
      have hu := congrArg (fun v : X ↦ v u) (congrFun h a)
      change archimedeanSchwartzTwist I a f u = archimedeanSchwartzTwist I a g u at hu
      have hv := (archimedeanSchwartzTwist_apply I a f u).symm.trans
        (hu.trans (archimedeanSchwartzTwist_apply I a g u))
      simpa [a] using hv
  have hn : IsNuclearTVS.{0} 𝓦(I) := isNuclearTVS_of_linearEmbedding t ht
    (isNuclearTVS_pi fun _ : Z ↦ schwartzBruhat_nuclear (G := archMul(ι, κ)))
  obtain ⟨_, -, _, -⟩ := archimedeanWeightedSchwartz_frechet (ι := ι) (κ := κ) _ho _hi _hne
  exact sep hn

/-- Paper: Lemma 5.3.3.3(1), p. 252.
For an open nonempty interval the weighted Schwartz–Bruhat space is nuclear. -/
theorem archimedeanWeightedSchwartz_nuclear {I : Set ℝ} (_ho : IsOpen I)
    (_hi : OrdConnected I) (_hne : I.Nonempty) : IsNuclearTVS 𝓦(I) := by sorry

/-- Paper: Lemma 5.3.3.3(2), p. 252.
The finite projective tensor topology is generated by seminorms with jointly continuous
pullback along the pure tensor map, as for the binary projective tensor product of §C.2.3. -/
abbrev FiniteProjectiveTensor {ι : Type*} [Fintype ι] (E : ι → Type*)
    [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)] [∀ i, TopologicalSpace (E i)] :=
  WithGeneratingSeminorms (⨂[ℂ] i, E i)
    (fun p : {p : Seminorm ℂ (⨂[ℂ] i, E i) //
      Continuous (fun f : ∀ i, E i ↦ p (⨂ₜ[ℂ] i, f i))} ↦ p.val)

/-- Paper: Lemma 5.3.3.3(2), p. 252.
With no factors the projective tensor product identifies topologically with the scalars
and the empty pure tensor maps to one. -/
theorem finiteProjectiveTensor_empty_equiv :
    ∃ e : FiniteProjectiveTensor (fun _ : Empty ↦ ℂ) ≃L[ℂ] ℂ,
      e (⨂ₜ[ℂ] i : Empty, (0 : ℂ)) = 1 := by
  let X := ⨂[ℂ] _i : Empty, ℂ
  let P : SeminormFamily ℂ X
      {p : Seminorm ℂ X // Continuous (fun f : Empty → ℂ ↦ p (⨂ₜ[ℂ] i, f i))} := fun p ↦ p.val
  let l : WithGeneratingSeminorms X P ≃ₗ[ℂ] ℂ := PiTensorProduct.isEmptyEquiv Empty
  have hP := withGeneratingSeminorms_spec X P
  have : ContinuousSMul ℂ (WithGeneratingSeminorms X P) := hP.continuousSMul
  -- The norm of the scalar coordinate is one of the generating seminorms.
  have hl : Continuous l := by
    let q : Seminorm ℂ X := (normSeminorm ℂ ℂ).comp (PiTensorProduct.isEmptyEquiv Empty).toLinearMap
    have hq : Continuous (fun f : Empty → ℂ ↦ q (⨂ₜ[ℂ] i, f i)) := continuous_of_discreteTopology
    refine WithSeminorms.continuous_normedSpace_rng ℂ hP l.toLinearMap
      ⟨{⟨q, hq⟩}, 1, Seminorm.le_def.mpr fun x ↦ ?_⟩
    have hx : (({⟨q, hq⟩} : Finset _).sup P) x = q x :=
      congrArg (fun p : Seminorm ℂ X ↦ p x) Finset.sup_singleton
    exact le_of_eq (hx.symm.trans (one_smul ℝ≥0 _).symm)
  have hl' : Continuous l.symm := by
    have hsymm : (l.symm : ℂ → WithGeneratingSeminorms X P) = fun c ↦ c • l.symm 1 := by
      funext c
      rw [← map_smul, smul_eq_mul, mul_one]
    rw [hsymm]
    fun_prop
  exact ⟨⟨l, hl, hl'⟩, PiTensorProduct.isEmptyEquiv_apply_tprod Empty _⟩

-- TODO(paper-gap): If 0 ∉ I the factors S_I need not be unweighted Schwartz–Bruhat,
-- whereas (5.3.3.6) requires this. Include the unweighted twist on each factor.

set_option maxHeartbeats 600000 in
/-- Paper: Lemma 5.3.3.3(2), p. 252.
The canonical map multiplies pure factors evaluated in their own coordinates and
extends to a linear homeomorphism on the completion.
Deviation: The factors include weight zero for the unweighted condition in (5.3.3.6).
When zero already belongs to I these are the factors printed in the paper. -/
theorem archimedeanWeightedSchwartz_tensor {I : Set ℝ} (_ho : IsOpen I)
    (_hi : OrdConnected I) (_hne : I.Nonempty) :
    let J := insert 0 I
    let R := ModulatedExponentialDecay (archimedeanUnitModulation ℝ 1) J
    let C := ModulatedExponentialDecay (archimedeanUnitModulation ℂ 2) J
    let T := ProjectiveTensor (FiniteProjectiveTensor (fun _ : ι ↦ R))
      (FiniteProjectiveTensor (fun _ : κ ↦ C))
    ∃ L : T →L[ℂ] 𝓦(I), IsEmbedding L ∧
      (∀ (f : ι → R) (g : κ → C) (u : archMul(ι, κ)),
        (L ((⨂ₜ[ℂ] i, f i) ⊗ₜ[ℂ] (⨂ₜ[ℂ] j, g j))).val u =
          (∏ i, (f i).val (u.1 i)) * ∏ j, (g j).val (u.2 j)) ∧
      ∃ e : UniformSpace.Completion T ≃L[ℂ] 𝓦(I), ∀ z : T, e z = L z := by sorry

local notation "jet(" n ", " x ", " v ")" =>
  (fun f : 𝓢(archAdd(ι, κ), ℂ) ↦ iteratedFDeriv ℝ n (f : archAdd(ι, κ) → ℂ) x v)

/-- Paper: Lemma 5.3.3.3(3), p. 252.
Evaluation of the real derivative of order n at a point and a tuple of directions
is complex-linear in the Schwartz function. -/
theorem archimedeanSchwartzJet_isLinear (n : ℕ) (x : archAdd(ι, κ))
    (v : Fin n → archAdd(ι, κ)) : IsLinearMap ℂ (jet(n, x, v)) := by
  constructor
  · intro f g
    change iteratedFDeriv ℝ n ((f : _ → ℂ) + (g : _ → ℂ)) x v = _
    rw [iteratedFDeriv_add_apply (f.smooth n).contDiffAt (g.smooth n).contDiffAt,
      ContinuousMultilinearMap.add_apply]
  · intro a f
    change iteratedFDeriv ℝ n (a • (f : _ → ℂ)) x v = _
    rw [iteratedFDeriv_const_smul_apply (f.smooth n).contDiffAt, ContinuousMultilinearMap.smul_apply]

/-- Paper: Lemma 5.3.3.3(3), p. 252.
The flat Schwartz subspace is the intersection of the kernels of all jets on the
union of the coordinate hyperplanes.
Deviation: Full real Fréchet derivatives express the equivalent vanishing of the
mixed ordinary and Wirtinger derivatives. The coordinates are the product field coordinates. -/
def archimedeanFlatSchwartz : Submodule ℂ 𝓢(archAdd(ι, κ), ℂ) :=
  ⨅ x : {x : archAdd(ι, κ) // meetsWall(x)}, ⨅ n : ℕ, ⨅ v : Fin n → archAdd(ι, κ),
    LinearMap.ker ((archimedeanSchwartzJet_isLinear n x.val v).mk' _)

/-- Paper: Lemma 5.3.3.3(3), p. 252.
For one real factor the jet conditions recover the real flat subspace of §5.3.2. -/
theorem archimedeanFlatSchwartz_one_real :
    ∃ e : ↥(archimedeanFlatSchwartz (ι := Unit) (κ := Empty)) ≃L[ℂ] ↥realSchwartzFlatAtOrigin,
      ∀ f (x : ℝ), (e f).val x = f.val (fun _ ↦ x, fun j ↦ Empty.elim j) := by
  let L : ℝ ≃ₗ[ℝ] ((Unit → ℝ) × (Empty → ℂ)) :=
    { toFun := fun x ↦ (fun _ ↦ x, fun j ↦ Empty.elim j)
      invFun := fun p ↦ p.1 ()
      map_add' := fun x y ↦ Prod.ext rfl (funext fun j ↦ Empty.elim j)
      map_smul' := fun t x ↦ Prod.ext rfl (funext fun j ↦ Empty.elim j)
      left_inv := fun x ↦ rfl
      right_inv := fun p ↦ Prod.ext (funext fun _ ↦ rfl) (funext fun j ↦ Empty.elim j) }
  let φ : ℝ ≃L[ℝ] ((Unit → ℝ) × (Empty → ℂ)) := L.toContinuousLinearEquiv
  let A : 𝓢((Unit → ℝ) × (Empty → ℂ), ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ φ
  let B : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢((Unit → ℝ) × (Empty → ℂ), ℂ) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ φ.symm
  -- Pulling back along the coordinate line gives a real function flat at zero.
  have hA (f : 𝓢((Unit → ℝ) × (Empty → ℂ), ℂ))
      (hf : f ∈ archimedeanFlatSchwartz (ι := Unit) (κ := Empty)) :
      A f ∈ realSchwartzFlatAtOrigin := by
    rw [mem_realSchwartzFlatAtOrigin_iff]
    intro k
    simp only [archimedeanFlatSchwartz, Submodule.mem_iInf, LinearMap.mem_ker,
      IsLinearMap.mk'_apply] at hf
    have h0 := hf ⟨φ 0, Or.inl ⟨(), rfl⟩⟩ k (fun _ ↦ φ 1)
    rw [iteratedDeriv_eq_iteratedFDeriv]
    change iteratedFDeriv ℝ k ((f : (Unit → ℝ) × (Empty → ℂ) → ℂ) ∘ φ) 0 (fun _ ↦ 1) = 0
    erw [φ.toContinuousLinearMap.iteratedFDeriv_comp_right (f.smooth ⊤) 0 (i := k)
      (mod_cast le_top)]
    exact h0
  -- Conversely every jet on the wall is a multiple of a derivative at zero.
  have hB (g : 𝓢(ℝ, ℂ)) (hg : g ∈ realSchwartzFlatAtOrigin) :
      B g ∈ archimedeanFlatSchwartz (ι := Unit) (κ := Empty) := by
    rw [mem_realSchwartzFlatAtOrigin_iff] at hg
    simp only [archimedeanFlatSchwartz, Submodule.mem_iInf, LinearMap.mem_ker,
      IsLinearMap.mk'_apply]
    rintro ⟨x, hx⟩ n v
    have hx0 : φ.symm x = 0 := by
      rcases hx with ⟨i, hi⟩ | ⟨j, _⟩
      · cases i
        exact hi
      · exact j.elim
    change iteratedFDeriv ℝ n ((g : ℝ → ℂ) ∘ φ.symm) x v = 0
    erw [φ.symm.toContinuousLinearMap.iteratedFDeriv_comp_right (g.smooth ⊤) x (i := n)
      (mod_cast le_top)]
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    change iteratedFDeriv ℝ n (g : ℝ → ℂ) (φ.symm x) (fun i ↦ φ.symm (v i)) = 0
    rw [hx0, iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, hg, smul_zero]
  let e : ↥(archimedeanFlatSchwartz (ι := Unit) (κ := Empty)) ≃L[ℂ]
      ↥realSchwartzFlatAtOrigin :=
    ContinuousLinearEquiv.equivOfInverse
      ((A.comp (archimedeanFlatSchwartz (ι := Unit) (κ := Empty)).subtypeL).codRestrict
        realSchwartzFlatAtOrigin fun f ↦ hA f f.2)
      ((B.comp realSchwartzFlatAtOrigin.subtypeL).codRestrict
        (archimedeanFlatSchwartz (ι := Unit) (κ := Empty)) fun g ↦ hB g g.2)
      (fun f ↦ Subtype.ext (SchwartzMap.ext fun y ↦ by
        change (f.val : (Unit → ℝ) × (Empty → ℂ) → ℂ) (φ (φ.symm y)) = f.val y
        rw [ContinuousLinearEquiv.apply_symm_apply]))
      (fun g ↦ Subtype.ext (SchwartzMap.ext fun y ↦ by
        change (g.val : ℝ → ℂ) (φ.symm (φ y)) = g.val y
        rw [ContinuousLinearEquiv.symm_apply_apply]))
  exact ⟨e, fun f x ↦ rfl⟩

/-- Paper: Lemma 5.3.3.3(3), p. 252.
For one complex factor the real jet conditions recover the mixed Wirtinger conditions of §5.3.2. -/
theorem archimedeanFlatSchwartz_one_complex :
    ∃ e : ↥(archimedeanFlatSchwartz (ι := Empty) (κ := Unit)) ≃L[ℂ] ↥complexSchwartzFlatAtOrigin,
      ∀ f (z : ℂ), (e f).val z = f.val (fun i ↦ Empty.elim i, fun _ ↦ z) := by sorry

/-- Paper: Lemma 5.3.3.3(3), p. 252.
Schwartz functions supported away from every coordinate hyperplane are flat along them. -/
theorem mem_archimedeanFlatSchwartz_of_tsupport (f : 𝓢(archAdd(ι, κ), ℂ))
    (_hf : Disjoint (tsupport f) {x : archAdd(ι, κ) | meetsWall(x)}) :
    f ∈ archimedeanFlatSchwartz := by
  simp only [archimedeanFlatSchwartz, Submodule.mem_iInf, LinearMap.mem_ker]
  intro x n v
  have hx : x.val ∉ tsupport f := fun h ↦ Set.disjoint_left.mp _hf h x.2
  have hev : (f : archAdd(ι, κ) → ℂ) =ᶠ[nhds x.val] 0 := notMem_tsupport_iff_eventuallyEq.mp hx
  have h0 : iteratedFDeriv ℝ n (f : archAdd(ι, κ) → ℂ) x.val =
      iteratedFDeriv ℝ n (0 : archAdd(ι, κ) → ℂ) x.val :=
    (hev.iteratedFDeriv ℝ n).self_of_nhds
  simp [IsLinearMap.mk', h0]

/-- Paper: Lemma 5.3.3.3(3), p. 252.
The subspace of Schwartz functions with all jets zero on the coordinate hyperplanes is closed. -/
theorem archimedeanFlatSchwartz_isClosed :
    IsClosed (↑(archimedeanFlatSchwartz (ι := ι) (κ := κ)) : Set 𝓢(archAdd(ι, κ), ℂ)) := by
  simp only [archimedeanFlatSchwartz, Submodule.coe_iInf]
  refine isClosed_iInter fun x ↦ isClosed_iInter fun n ↦ isClosed_iInter fun v ↦ ?_
  let J := (TemperedDistribution.delta x.val).comp
    (LineDeriv.iteratedLineDerivOpCLM ℂ 𝓢(archAdd(ι, κ), ℂ) v)
  have hJ : (archimedeanSchwartzJet_isLinear n x.val v).mk' _ = J.toLinearMap := by
    ext f
    exact SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv.symm
  rw [hJ]
  exact J.isClosed_ker

-- TODO(paper-gap): The estimates (5.3.3.21)–(5.3.3.23) fail for bumps
-- supported close to, but away from, the origin.

/-- Paper: Lemma 5.3.3.3(3), p. 253.
Restriction to the product of the punctured lines identifies flat Schwartz functions
with the all-exponent weighted space. The inverse extends by zero. -/
theorem archimedeanFlatSchwartz_restrict_equiv :
    ∃ e : ↥(archimedeanFlatSchwartz (ι := ι) (κ := κ)) ≃L[ℂ] 𝓦(univ),
      ∀ (f : archimedeanFlatSchwartz) (u : archMul(ι, κ)), (e f).val u = f.val (archVal u) :=
  by sorry

/-- Paper: Lemma 5.3.3.3(3), p. 253.
A continuous quasi-character on the product of punctured fields acts by multiplication
through a unique linear homeomorphism of the flat Schwartz space. -/
theorem archimedeanFlatSchwartz_quasiCharacter_mul (c : QuasiCharacter (archMul(ι, κ))) :
    ∃! M : ↥(archimedeanFlatSchwartz (ι := ι) (κ := κ)) ≃L[ℂ]
        ↥(archimedeanFlatSchwartz (ι := ι) (κ := κ)),
      ∀ (f : archimedeanFlatSchwartz) (u : archMul(ι, κ)),
        (M f).val (archVal u) = c u * f.val (archVal u) := by sorry

end ArchimedeanProduct

section ArchimedeanMellin

local notation "realProfile(" f ", " ε ")" =>
  (fun t : ℝ ↦ f t + (-1 : ℂ) ^ (ε).val * f (-t))
local notation "unitAngle(" θ ")" => Complex.exp ((θ : ℂ) * Complex.I)
local notation "complexProfile(" f ", " n ")" =>
  (fun t : ℝ ↦ ∫ θ in (0 : ℝ)..(2 * Real.pi),
    (unitAngle(θ)) ^ n * f ((Real.sqrt t : ℂ) * unitAngle(θ)))

/-- A Schwartz function is `O(x^(-a))` at infinity for every `a`. -/
private theorem realArchimedeanMellin_existsUnique_isBigO_atTop (G : SchwartzMap ℝ ℂ) (a : ℝ) :
    (G : ℝ → ℂ) =O[atTop] (· ^ (-a)) := by
  have h := G.isBigO_cocompact_rpow (-a)
  refine (h.mono atTop_le_cocompact).congr' (EventuallyEq.refl _ _) ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [Real.norm_eq_abs, abs_of_pos hx]

/-- A Schwartz function is bounded near zero. -/
private theorem realArchimedeanMellin_existsUnique_isBigO_zero (G : SchwartzMap ℝ ℂ) :
    (G : ℝ → ℂ) =O[𝓝[>] 0] (· ^ (-(0 : ℝ))) := by
  have hb : (G : ℝ → ℂ) =O[⊤] (fun _ ↦ (1 : ℝ)) := by
    obtain ⟨C, -, hC⟩ := G.decay 0 0
    refine Asymptotics.isBigO_iff.mpr ⟨C, .of_forall fun x ↦ ?_⟩
    simpa using hC x
  refine (hb.mono le_top).congr' (EventuallyEq.refl _ _) (.of_forall fun x ↦ ?_)
  simp

private theorem realArchimedeanMellin_existsUnique_convergent (G : SchwartzMap ℝ ℂ) {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent G s :=
  mellinConvergent_of_isBigO_rpow (G.continuous.continuousOn.locallyIntegrableOn measurableSet_Ioi)
    (realArchimedeanMellin_existsUnique_isBigO_atTop G (s.re + 1)) (lt_add_one _) (realArchimedeanMellin_existsUnique_isBigO_zero G) (by simpa using hs)

private theorem realArchimedeanMellin_existsUnique_differentiableAt (G : SchwartzMap ℝ ℂ) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (mellin G) s :=
  mellin_differentiableAt_of_isBigO_rpow
    (G.continuous.continuousOn.locallyIntegrableOn measurableSet_Ioi)
    (realArchimedeanMellin_existsUnique_isBigO_atTop G (s.re + 1)) (lt_add_one _) (realArchimedeanMellin_existsUnique_isBigO_zero G) (by simpa using hs)

private theorem realArchimedeanMellin_existsUnique_ibp (G : SchwartzMap ℝ ℂ) {s : ℂ} (hs : 0 < s.re) :
    mellin G s = -(1 / s) * mellin (SchwartzMap.derivCLM ℂ ℂ G) (s + 1) := by
  have hs0 : s ≠ 0 := fun h ↦ by simp [h] at hs
  let G' := SchwartzMap.derivCLM ℂ ℂ G
  let u : ℝ → ℂ := fun t ↦ (t : ℂ) ^ ((s - 1) + 1) / ((s - 1) + 1)
  have hu_eq (t : ℝ) : u t = (t : ℂ) ^ s / s := by simp [u]
  have hu : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt u ((x : ℂ) ^ (s - 1)) x := fun x hx ↦
    hasDerivAt_ofReal_cpow_const' (ne_of_gt hx) (fun h ↦ hs0 (by linear_combination h))
  have hv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (G : ℝ → ℂ) (G' x) x := fun x _ ↦
    (G.differentiableAt).hasDerivAt
  have hs1 : 0 < (s + 1).re := by simp; linarith
  have hG's := realArchimedeanMellin_existsUnique_convergent G' hs1
  have hGs := realArchimedeanMellin_existsUnique_convergent G hs
  have huv' : IntegrableOn (u * (G' : ℝ → ℂ)) (Ioi 0) := by
    refine IntegrableOn.congr_fun (hG's.const_mul (1 / s)) (fun t _ ↦ ?_) measurableSet_Ioi
    simp only [Pi.mul_apply, hu_eq, smul_eq_mul, add_sub_cancel_right]
    ring
  have hu'v : IntegrableOn ((fun x : ℝ ↦ (x : ℂ) ^ (s - 1)) * (G : ℝ → ℂ)) (Ioi 0) := hGs
  have h0 : Tendsto (u * (G : ℝ → ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousAt (fun t : ℝ ↦ (t : ℂ) ^ s / s * G t) 0 :=
      ((Complex.continuousAt_ofReal_cpow_const 0 s (Or.inl hs)).div_const s).mul
        G.continuous.continuousAt
    have := hc.tendsto
    simp only [Complex.ofReal_zero, Complex.zero_cpow hs0, zero_div, zero_mul] at this
    refine tendsto_nhdsWithin_of_tendsto_nhds (this.congr fun t ↦ ?_)
    simp only [Pi.mul_apply, hu_eq]
  have hinf : Tendsto (u * (G : ℝ → ℂ)) atTop (𝓝 0) := by
    have hub : u =O[atTop] (fun t : ℝ ↦ t ^ s.re) := by
      refine Asymptotics.isBigO_iff.mpr ⟨‖s‖⁻¹, ?_⟩
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      rw [hu_eq, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos ht, Real.norm_eq_abs,
        abs_of_pos (Real.rpow_pos_of_pos ht _), div_eq_mul_inv, mul_comm]
    have hprod := hub.mul (realArchimedeanMellin_existsUnique_isBigO_atTop G (s.re + 1))
    have hexp : (fun t : ℝ ↦ t ^ s.re * t ^ (-(s.re + 1))) =ᶠ[atTop] fun t ↦ t ^ (-1 : ℝ) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      rw [← Real.rpow_add ht]
      ring_nf
    exact (hprod.congr' (EventuallyEq.refl _ _) hexp).trans_tendsto
      (tendsto_rpow_neg_atTop one_pos)
  have key := integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v h0 hinf
  simp only [sub_zero, zero_sub] at key
  unfold mellin
  have hL : (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) • G t) =
      -∫ t in Ioi (0 : ℝ), u t * G' t := by
    rw [key, neg_neg]
    rfl
  rw [hL]
  have hR : (∫ t in Ioi (0 : ℝ), u t * G' t) =
      (1 / s) * ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s + 1 - 1) • G' t := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
    simp only [hu_eq, smul_eq_mul, add_sub_cancel_right]
    ring
  rw [hR]
  ring

private theorem realArchimedeanMellin_existsUnique_succ (G : SchwartzMap ℝ ℂ) (E : ℕ → ℂ → ℂ)
    (hE : ∀ N s, E N s = (-1 : ℂ) ^ N * (∏ j ∈ Finset.range N, (s + j))⁻¹ *
      mellin ((SchwartzMap.derivCLM ℂ ℂ)^[N] G) (s + N)) (N : ℕ) {s : ℂ} (hs : 0 < (s + N).re) :
    E N s = E (N + 1) s := by
  rw [hE, hE]
  rw [realArchimedeanMellin_existsUnique_ibp _ hs, Function.iterate_succ_apply', Finset.prod_range_succ,
    pow_succ, Nat.cast_succ, ← add_assoc, mul_inv]
  ring

private theorem realArchimedeanMellin_existsUnique_eq (G : SchwartzMap ℝ ℂ) (E : ℕ → ℂ → ℂ)
    (hE : ∀ N s, E N s = (-1 : ℂ) ^ N * (∏ j ∈ Finset.range N, (s + j))⁻¹ *
      mellin ((SchwartzMap.derivCLM ℂ ℂ)^[N] G) (s + N)) {s : ℂ} {N M : ℕ} (hN : 0 < (s + N).re) (hNM : N ≤ M) :
    E N s = E M s := by
  induction M, hNM using Nat.le_induction with
  | base => rfl
  | succ M hNM ih =>
    refine ih.trans (realArchimedeanMellin_existsUnique_succ G E hE M ?_)
    have : (N : ℝ) ≤ M := by exact_mod_cast hNM
    simp only [Complex.add_re, Complex.natCast_re] at hN ⊢
    linarith

private theorem realArchimedeanMellin_existsUnique_contEq (G : SchwartzMap ℝ ℂ) (E : ℕ → ℂ → ℂ)
    (hE : ∀ N s, E N s = (-1 : ℂ) ^ N * (∏ j ∈ Finset.range N, (s + j))⁻¹ *
      mellin ((SchwartzMap.derivCLM ℂ ℂ)^[N] G) (s + N))
    (F : ℂ → ℂ) (hF : ∀ s, F s = E (⌈-s.re⌉₊ + 1) s) {s : ℂ} {N : ℕ} (hN : 0 < (s + N).re) :
    F s = E N s := by
  rw [hF]
  have hn : 0 < (s + ((⌈-s.re⌉₊ + 1 : ℕ) : ℂ)).re := by
    simp only [Complex.add_re, Complex.natCast_re, Nat.cast_add, Nat.cast_one, Complex.one_re]
    have := Nat.le_ceil (-s.re)
    linarith
  rcases le_total N (⌈-s.re⌉₊ + 1) with h | h
  · exact (realArchimedeanMellin_existsUnique_eq G E hE hN h).symm
  · exact realArchimedeanMellin_existsUnique_eq G E hE hn h

private theorem realArchimedeanMellin_existsUnique_analyticAt (G : SchwartzMap ℝ ℂ) (N : ℕ) {s : ℂ} (hs : 0 < (s + N).re) :
    AnalyticAt ℂ (fun z ↦ mellin ((SchwartzMap.derivCLM ℂ ℂ)^[N] G) (z + N)) s := by
  have hU : IsOpen {z : ℂ | 0 < (z + N).re} :=
    isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_id.add continuous_const))
  have hd : DifferentiableOn ℂ (fun z ↦ mellin ((SchwartzMap.derivCLM ℂ ℂ)^[N] G) (z + N))
      {z : ℂ | 0 < (z + N).re} := fun z hz ↦
    ((realArchimedeanMellin_existsUnique_differentiableAt _ hz).comp z
      (differentiableAt_id.add_const _)).differentiableWithinAt
  exact hd.analyticAt (hU.mem_nhds hs)

private theorem realArchimedeanMellin_existsUnique_meromorphicAt (G : SchwartzMap ℝ ℂ) (E : ℕ → ℂ → ℂ)
    (hE : ∀ N s, E N s = (-1 : ℂ) ^ N * (∏ j ∈ Finset.range N, (s + j))⁻¹ *
      mellin ((SchwartzMap.derivCLM ℂ ℂ)^[N] G) (s + N))
    (F : ℂ → ℂ) (hF : ∀ s, F s = E (⌈-s.re⌉₊ + 1) s) (s : ℂ) :
    MeromorphicAt F s := by
  set N := ⌈-s.re⌉₊ + 1
  have hN : 0 < (s + N).re := by
    simp only [N, Complex.add_re, Complex.natCast_re, Nat.cast_add, Nat.cast_one, Complex.one_re]
    have := Nat.le_ceil (-s.re)
    linarith
  have hU : IsOpen {z : ℂ | 0 < (z + N).re} :=
    isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_id.add continuous_const))
  have hP : AnalyticAt ℂ (fun z : ℂ ↦ ∏ j ∈ Finset.range N, (z + j)) s := by fun_prop
  have hE' : MeromorphicAt (E N) s := by
    have h0 := ((MeromorphicAt.const ((-1 : ℂ) ^ N) s).mul hP.meromorphicAt.inv).mul
      (realArchimedeanMellin_existsUnique_analyticAt G N hN).meromorphicAt
    exact h0.congr (Eventually.of_forall fun z ↦ (hE N z).symm)
  refine hE'.congr ?_
  filter_upwards [nhdsWithin_le_nhds (hU.mem_nhds hN)] with z hz
  exact (realArchimedeanMellin_existsUnique_contEq G E hE F hF hz).symm

private theorem realArchimedeanMellin_existsUnique_eqMellin (G : SchwartzMap ℝ ℂ) (E : ℕ → ℂ → ℂ)
    (hE : ∀ N s, E N s = (-1 : ℂ) ^ N * (∏ j ∈ Finset.range N, (s + j))⁻¹ *
      mellin ((SchwartzMap.derivCLM ℂ ℂ)^[N] G) (s + N))
    (F : ℂ → ℂ) (hF : ∀ s, F s = E (⌈-s.re⌉₊ + 1) s) {s : ℂ} (hs : 0 < s.re) :
    F s = mellin G s := by
  rw [realArchimedeanMellin_existsUnique_contEq G E hE F hF (N := 0) (by simpa using hs), hE]
  simp

private theorem realArchimedeanMellin_existsUnique_contAnalyticAt (G : SchwartzMap ℝ ℂ) (E : ℕ → ℂ → ℂ)
    (hE : ∀ N s, E N s = (-1 : ℂ) ^ N * (∏ j ∈ Finset.range N, (s + j))⁻¹ *
      mellin ((SchwartzMap.derivCLM ℂ ℂ)^[N] G) (s + N))
    (F : ℂ → ℂ) (hF : ∀ s, F s = E (⌈-s.re⌉₊ + 1) s) {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ F s := by
  have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have h := realArchimedeanMellin_existsUnique_analyticAt G 0 (s := s) (by simpa using hs)
  simp only [Function.iterate_zero, id_eq, Nat.cast_zero, add_zero] at h
  refine h.congr ?_
  filter_upwards [hU.mem_nhds hs] with z hz
  exact (realArchimedeanMellin_existsUnique_eqMellin G E hE F hF hz).symm

/-- Two functions in meromorphic normal form on the plane that agree on the right
half-plane agree everywhere. -/
private theorem realArchimedeanMellin_existsUnique_eqNF {G H : ℂ → ℂ}
    (hG : MeromorphicNFOn G univ) (hH : MeromorphicNFOn H univ)
    (h : ∀ z : ℂ, 0 < z.re → G z = H z) (s : ℂ) : G s = H s := by
  have hAt : meromorphicOrderAt (G - H) (1 : ℂ) = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    have hn : ∀ᶠ z : ℂ in 𝓝 (1 : ℂ), 0 < z.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    exact (hn.filter_mono nhdsWithin_le_nhds).mono fun z hz ↦ sub_eq_zero.mpr (h z hz)
  have hOrd := (hG.meromorphicOn.sub hH.meromorphicOn).meromorphicOrderAt_eq_top_of_isPreconnected
    isPreconnected_univ (mem_univ (1 : ℂ)) (mem_univ s) hAt
  have hNear : G =ᶠ[𝓝[≠] s] H :=
    (meromorphicOrderAt_eq_top_iff.mp hOrd).mono fun _ h ↦ sub_eq_zero.mp h
  exact (((hG (mem_univ s)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds (hH (mem_univ s))).mp
    hNear).eq_of_nhds

private theorem realArchimedeanMellin_existsUnique_schwartz (G : SchwartzMap ℝ ℂ) :
    ∃! L : ℂ → ℂ, MeromorphicNFOn L univ ∧ ∀ s : ℂ, 0 < s.re → HasMellin G s (L s) := by
  let E : ℕ → ℂ → ℂ := fun N s ↦ (-1 : ℂ) ^ N * (∏ j ∈ Finset.range N, (s + j))⁻¹ *
    mellin ((SchwartzMap.derivCLM ℂ ℂ)^[N] G) (s + N)
  have hE : ∀ N s, E N s = (-1 : ℂ) ^ N * (∏ j ∈ Finset.range N, (s + j))⁻¹ *
      mellin ((SchwartzMap.derivCLM ℂ ℂ)^[N] G) (s + N) := fun _ _ ↦ rfl
  let F : ℂ → ℂ := fun s ↦ E (⌈-s.re⌉₊ + 1) s
  have hF : ∀ s, F s = E (⌈-s.re⌉₊ + 1) s := fun _ ↦ rfl
  have hm : MeromorphicOn F univ := fun s _ ↦ realArchimedeanMellin_existsUnique_meromorphicAt G E hE F hF s
  refine ⟨toMeromorphicNFOn F univ, ⟨meromorphicNFOn_toMeromorphicNFOn _ _,
    fun s hs ↦ ⟨realArchimedeanMellin_existsUnique_convergent G hs, ?_⟩⟩, ?_⟩
  · rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hm (mem_univ s),
      toMeromorphicNFAt_eq_self.mpr (realArchimedeanMellin_existsUnique_contAnalyticAt G E hE F hF hs).meromorphicNFAt,
      realArchimedeanMellin_existsUnique_eqMellin G E hE F hF hs]
  · rintro L ⟨hL, hLm⟩
    funext s
    refine realArchimedeanMellin_existsUnique_eqNF hL (meromorphicNFOn_toMeromorphicNFOn _ _) (fun z hz ↦ ?_) s
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hm (mem_univ z),
      toMeromorphicNFAt_eq_self.mpr (realArchimedeanMellin_existsUnique_contAnalyticAt G E hE F hF hz).meromorphicNFAt,
      realArchimedeanMellin_existsUnique_eqMellin G E hE F hF hz]
    exact (hLm z hz).2.symm

/-- Paper: Proposition 5.3.3.4, p. 258.
The real Mellin integral converges on the right half-plane and has a unique
meromorphic continuation for each sign parity. -/
theorem realArchimedeanMellin_existsUnique (f : 𝓢(ℝ, ℂ)) (ε : Fin 2) :
    ∃! L : ℂ → ℂ, MeromorphicNFOn L univ ∧
      ∀ s : ℂ, 0 < s.re → HasMellin (realProfile(f, ε)) s (L s) := by
  let G : 𝓢(ℝ, ℂ) := f + ((-1 : ℂ) ^ ε.val) •
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.neg ℝ) f
  have hG : realProfile(f, ε) = ⇑G := by
    funext t
    simp [G]
  rw [hG]
  exact realArchimedeanMellin_existsUnique_schwartz G

/-- Paper: Proposition 5.3.3.4, p. 258.
The real local Mellin transform is the meromorphic continuation of the weighted
integral over the two signs in (5.3.3.26). -/
def realArchimedeanMellin (f : 𝓢(ℝ, ℂ)) (ε : Fin 2) : ℂ → ℂ :=
  (realArchimedeanMellin_existsUnique f ε).exists.choose

/-- Paper: Proposition 5.3.3.4, p. 258.
The positive half-plane gives the defining integral for the real Mellin transform. -/
theorem realArchimedeanMellin_eq_integral (f : 𝓢(ℝ, ℂ)) (ε : Fin 2)
    (s : ℂ) (_hs : 0 < s.re) :
    realArchimedeanMellin f ε s = mellin (realProfile(f, ε)) s :=
  ((realArchimedeanMellin_existsUnique f ε).exists.choose_spec.2 s _hs).2.symm

/-- Paper: Proposition 5.3.3.4, p. 258.
The complex Mellin integral converges on the right half-plane and has a unique
meromorphic continuation for each integral angular weight.
Deviation: The angular measure is dθ in the norm coordinate t = |z|², as in §3.3.
The printed 2 dθ would double the Tamagawa integral. -/
theorem complexArchimedeanMellin_existsUnique (f : 𝓢(ℂ, ℂ)) (n : ℤ) :
    ∃! L : ℂ → ℂ, MeromorphicNFOn L univ ∧
      ∀ s : ℂ, 0 < s.re → HasMellin (complexProfile(f, n)) s (L s) := by sorry

/-- Paper: Proposition 5.3.3.4, p. 258.
The complex local Mellin transform is the meromorphic continuation of the angular
and radial integral in (5.3.3.26).
Deviation: The angular measure is normalized as in §3.3. -/
def complexArchimedeanMellin (f : 𝓢(ℂ, ℂ)) (n : ℤ) : ℂ → ℂ :=
  (complexArchimedeanMellin_existsUnique f n).exists.choose

/-- Paper: Proposition 5.3.3.4, p. 258.
The positive half-plane gives the defining integral for the complex Mellin transform.
Deviation: The angular measure is normalized as in §3.3. -/
theorem complexArchimedeanMellin_eq_integral (f : 𝓢(ℂ, ℂ)) (n : ℤ)
    (s : ℂ) (_hs : 0 < s.re) :
    complexArchimedeanMellin f n s = mellin (complexProfile(f, n)) s :=
  ((complexArchimedeanMellin_existsUnique f n).exists.choose_spec.2 s _hs).2.symm

/-- Multiplicative Tamagawa integration in real coordinates is integration against dx/|x|. -/
private theorem realArchimedeanMellin_eq_infiniteLocalIdelicZFunction_measure {F : Type*} [Field F] [NumberField F] (w : InfinitePlace F) (hw : w.IsReal) (H : ℝ → ℂ) :
    let : MeasurableSpace w.Completion := borel _
    (∫ u : w.Completionˣ, H ((InfinitePlace.Completion.ringEquivRealOfIsReal hw) u.val) ∂(infiniteLocalMultiplicativeTamagawaMeasure F w)) =
      ∫ t : ℝ, (‖t‖ : ℂ)⁻¹ * H t := by
  let : MeasurableSpace w.Completion := borel _
  classical
  let K := w.Completion
  let : BorelSpace K := ⟨rfl⟩
  let : BorelSpace Kˣ := borelSpace_units_of_continuousInv₀ K
  let e := (InfinitePlace.Completion.ringEquivRealOfIsReal hw)
  let j := InfinitePlace.Completion.isometryEquivRealOfIsReal hw
  let μ := infiniteLocalAdditiveTamagawaMeasure F w
  let D (x : K) : ENNReal := (↑(‖x‖₊ ^ w.mult) : ENNReal)⁻¹
  let ι : Kˣ → K := Units.val
  have hι : MeasurableEmbedding ι := (IsOpenUnits.isOpenEmbedding_unitsVal (M := K)).measurableEmbedding
  have hμ : μ = (volume : Measure ℝ).map e.symm := by
    exact dite_eq_left hw
  have hj : MeasurableEmbedding (e.symm : ℝ → K) := j.symm.toHomeomorph.measurableEmbedding
  have hμ₀ : μ {0} = 0 := by
    rw [hμ, hj.map_apply]
    have hpre : e.symm ⁻¹' ({0} : Set K) = {0} := by
      ext x
      exact e.symm.map_eq_zero_iff
    rw [hpre, measure_singleton]
  have hneμ : ∀ᵐ x ∂μ, x ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not, ofPred_eq_eq_singleton] using hμ₀
  have hν : ∀ᵐ x ∂μ.withDensity D, x ≠ 0 :=
    (withDensity_absolutelyContinuous μ D).ae_le hneμ
  have hmap : ((infiniteLocalMultiplicativeTamagawaMeasure F w)).map ι = μ.withDensity D := by
    rw [infiniteLocalMultiplicativeTamagawaMeasure, hι.map_comap, Measure.restrict_eq_self_of_ae_mem]
    exact hν.mono fun x hx ↦ ⟨Units.mk0 x hx, rfl⟩
  have hD : Measurable D := (measurable_coe_nnreal_ennreal.comp ((continuous_nnNorm.pow w.mult).measurable)).inv
  have hfinite : ∀ᵐ x ∂μ, D x < ⊤ := by
    filter_upwards [hneμ] with x hx
    change x ≠ 0 at hx
    simpa [D, hw.mult_eq_one] using hx
  calc
    _ = ∫ x : K, H (e x) ∂(((infiniteLocalMultiplicativeTamagawaMeasure F w)).map ι) := (hι.integral_map (fun x ↦ H (e x))).symm
    _ = ∫ x : K, (D x).toReal • H (e x) ∂μ := by rw [hmap, integral_withDensity_eq_integral_toReal_smul hD hfinite]
    _ = _ := by
      rw [hμ, hj.integral_map]
      apply integral_congr_ae
      filter_upwards with t
      have hn : ‖e.symm t‖ = ‖t‖ := j.symm.isometry.norm_map_of_map_zero (map_zero e.symm) _
      simp only [D, hw.mult_eq_one, pow_one, ENNReal.toReal_inv, ENNReal.coe_toReal, coe_nnNorm,
        e.apply_symm_apply, hn, Complex.real_smul, Complex.ofReal_inv]

/-- Splitting the real local integral into its positive and negative rays gives the Mellin integral. -/
private theorem realArchimedeanMellin_eq_infiniteLocalIdelicZFunction_integral {F : Type*} [Field F] [NumberField F] (w : InfinitePlace F) (hw : w.IsReal)
    (g : SchwartzMap ℝ ℂ) (c : QuasiCharacter w.Completionˣ) (z : ℂ) (a : Fin 2)
    (hc : (∀ x : ℝˣ, c (Units.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toMonoidHom x) = (‖(x : ℝ)‖ : ℂ) ^ z * (if 0 < (x : ℝ) then 1 else (-1 : ℂ)) ^ a.val)) (hz : 0 < z.re) :
    let : MeasurableSpace w.Completion := borel _
    localIdelicZetaIntegral (infiniteLocalMultiplicativeTamagawaMeasure F w) (fun x ↦ g ((InfinitePlace.Completion.ringEquivRealOfIsReal hw) x)) c =
      mellin (fun x : ℝ ↦ g x + (-1:ℂ)^a.val * g (-x)) z := by
  let : MeasurableSpace w.Completion := borel _
  let e := (InfinitePlace.Completion.ringEquivRealOfIsReal hw)
  let H (t : ℝ) := g t * ((‖t‖:ℂ)^z * (if 0 < t then 1 else (-1:ℂ))^a.val)
  let J (t : ℝ) := (‖t‖ : ℂ)⁻¹ * H t
  have he (u : w.Completionˣ) : g (e u.val) * c u = H (e u.val) := by
    let x := Units.map e.toMonoidHom u
    have h := hc x
    rw [show Units.map e.symm.toMonoidHom x = u from Units.ext (e.symm_apply_apply u.val)] at h
    exact congrArg (g (e u.val) * ·) h
  change (∫ u : w.Completionˣ, g (e u.val) * c u ∂(infiniteLocalMultiplicativeTamagawaMeasure F w)) = _
  rw [integral_congr_ae (.of_forall he)]
  rw [realArchimedeanMellin_eq_infiniteLocalIdelicZFunction_measure]
  change (∫ x : ℝ, J x) = _
  let P (t : ℝ) := (t : ℂ) ^ (z-1)
  have hpos {t : ℝ} (ht : 0<t) : J t = P t * g t ∧ J (-t) = P t * ((-1:ℂ)^a.val * g (-t)) := by
    have hne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
    simp only [P, J, H, Real.norm_eq_abs, abs_neg, abs_of_pos ht, ite_eq_left ht, one_pow,
      ite_eq_right (not_lt.mpr (neg_nonpos.mpr ht.le)), Complex.cpow_sub _ _ hne, Complex.cpow_one]
    constructor <;> ring
  have hconv (k : SchwartzMap ℝ ℂ) : MellinConvergent (fun t : ℝ ↦ k t) z := by
    apply mellinConvergent_of_isBigO_rpow (a := z.re+1) (b := 0) (k.continuous.continuousOn.locallyIntegrableOn measurableSet_Ioi)
    · have h := (k.isBigO_cocompact_rpow (-(z.re+1))).mono (atTop_le_cocompact (α := ℝ))
      apply h.congr' .rfl
      filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
      simp [Real.norm_eq_abs, abs_of_nonneg ht]
    · linarith
    · simpa using ((k.continuous.continuousAt (x := 0)).isBigO_one ℝ).mono nhdsWithin_le_nhds
    · exact hz
  let k := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.neg ℝ : ℝ ≃L[ℝ] ℝ) (F := ℂ) g
  have hi₁ : IntegrableOn (fun x ↦ P x * g x) (Ioi (0:ℝ)) := hconv g
  have hi₂ : IntegrableOn (fun x ↦ P x * ((-1:ℂ)^a.val * g (-x))) (Ioi (0:ℝ)) := by
    apply ((hconv k).const_mul ((-1:ℂ)^a.val)).congr
    filter_upwards with x
    change (-1:ℂ)^a.val * (P x * g (-x)) = _
    ring
  have hiPos : IntegrableOn J (Ioi 0) := hi₁.congr (ae_restrict_mem measurableSet_Ioi |>.mono fun t ht ↦ (hpos ht).1.symm)
  have hiNeg : IntegrableOn (fun t ↦ J (-t)) (Ioi 0) := hi₂.congr (ae_restrict_mem measurableSet_Ioi |>.mono fun t ht ↦ (hpos ht).2.symm)
  have hiLeft : IntegrableOn J (Iic 0) := by
    rw [integrableOn_Iic_iff_integrableOn_Iio]
    simpa using hiNeg.comp_neg
  have hneg : (∫ x in Iic (0:ℝ), J x) = ∫ x in Ioi (0:ℝ), J (-x) := by
    simpa only [neg_zero] using (integral_comp_neg_Ioi 0 J).symm
  rw [← intervalIntegral.integral_Iic_add_Ioi hiLeft hiPos, hneg]
  rw [setIntegral_congr_fun (f := fun t ↦ J (-t)) measurableSet_Ioi (fun t ht ↦ (hpos ht).2),
    setIntegral_congr_fun (f := J) measurableSet_Ioi (fun t ht ↦ (hpos ht).1), add_comm, ← integral_add hi₁ hi₂]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  change (P t * g t + P t * _) = P t * _
  ring

/-- Uniqueness of continuation identifies the Mellin transform with the local zeta function. -/
private theorem realArchimedeanMellin_eq_infiniteLocalIdelicZFunction_compare
    {F : Type*} [Field F] [NumberField F] (w : InfinitePlace F) (hw : w.IsReal)
    (f : SchwartzBruhat (Multiplicative w.Completion)) (g : 𝓢(ℝ, ℂ))
    (hg : ∀ x : w.Completion,
      g (InfinitePlace.Completion.ringEquivRealOfIsReal hw x) = f (Multiplicative.ofAdd x)) :
    ∀ c : QuasiCharacter w.Completionˣ,
      infiniteLocalIdelicZFunction w f c =
        realArchimedeanMellin g (realLocalEulerParameters w hw c).exists.choose.2
          (realLocalEulerParameters w hw c).exists.choose.1 := by
  let Z (c : QuasiCharacter w.Completionˣ) :=
    realArchimedeanMellin g (realLocalEulerParameters w hw c).exists.choose.2
      (realLocalEulerParameters w hw c).exists.choose.1
  have hZ : Z = infiniteLocalIdelicZFunction w f := by
    apply (infiniteLocalIdelicZFunction_existsUnique w f).unique
    · intro χ
      let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
      let i : ℝˣ →ₜ* w.Completionˣ := ⟨Units.map e.symm.toMonoidHom,
        (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.continuous.units_map _⟩
      let unit : QuasiCharacter w.Completionˣ :=
        (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ
      obtain ⟨p, ht, hp⟩ :=
        (existsUnique_realUnits_character_parameters (unit.comp i)
          (fun _ ↦ Circle.norm_coe _)).exists
      let chart := quasiCharacterNormTwist
        (Units.map nnNormHom.toMonoidHom ^ w.mult) (continuous_infiniteLocalModule w) unit
      have hshape (s : ℂ) (x : ℝˣ) :
          chart s (Units.map e.symm.toMonoidHom x) =
            (‖(x : ℝ)‖ : ℂ) ^ (s + p.1) *
              (if 0 < (x : ℝ) then 1 else (-1 : ℂ)) ^ p.2.val := by
        have hn : ‖e.symm x.val‖ = ‖x.val‖ :=
          (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.isometry.norm_map_of_map_zero
            (map_zero e.symm) x.val
        change unit (Units.map e.symm.toMonoidHom x) *
          ((‖e.symm x.val‖ ^ w.mult : ℝ) : ℂ) ^ s = _
        have hx := hp x
        change unit (Units.map e.symm.toMonoidHom x) = _ at hx
        rw [hx, hn, hw.mult_eq_one, pow_one,
          Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr x.ne_zero))]
        ring
      have hparam (s : ℂ) :
          (realLocalEulerParameters w hw (chart s)).exists.choose = (s + p.1, p.2) :=
        (realLocalEulerParameters w hw (chart s)).unique
          (realLocalEulerParameters w hw (chart s)).exists.choose_spec (hshape s)
      have he : (Z ∘ chart) = fun s ↦ realArchimedeanMellin g p.2 (s + p.1) := by
        funext s
        dsimp only [Function.comp_def, Z]
        rw [hparam]
      change MeromorphicNFOn (Z ∘ chart) univ ∧ _
      constructor
      · rw [he]
        intro s _
        exact (meromorphicNFAt_comp_add_const_iff_meromorphicNFAt
          (f := realArchimedeanMellin g p.2)).mpr
          ((realArchimedeanMellin_existsUnique g p.2).exists.choose_spec.1 (mem_univ _))
      · intro s hs
        change (Z ∘ chart) s = _
        rw [he]
        dsimp only
        have hz : 0 < (s + p.1).re := by simpa [Complex.add_re, ht] using hs
        rw [realArchimedeanMellin_eq_integral g p.2 _ hz]
        have hf : (fun x ↦ f (Multiplicative.ofAdd x)) = fun x ↦ g (e x) :=
          funext fun x ↦ (hg x).symm
        rw [hf]
        exact (realArchimedeanMellin_eq_infiniteLocalIdelicZFunction_integral
          w hw g (chart s) (s + p.1) p.2 (hshape s) hz).symm
    · exact (infiniteLocalIdelicZFunction_existsUnique w f).exists.choose_spec
  intro c
  exact congrFun hZ.symm c

/-- Paper: Proposition 5.3.3.4, p. 258.
In the real field model the local zeta function of §3.3 is the two-sign Mellin transform
at the radial exponent and parity of the given quasi-character. -/
theorem realArchimedeanMellin_eq_infiniteLocalIdelicZFunction
    {F : Type*} [Field F] [NumberField F] (w : InfinitePlace F) (hw : w.IsReal)
    (f : SchwartzBruhat (Multiplicative w.Completion)) :
    ∃ g : 𝓢(ℝ, ℂ), (∀ x : w.Completion,
      g (InfinitePlace.Completion.ringEquivRealOfIsReal hw x) = f (Multiplicative.ofAdd x)) ∧
      ∀ c : QuasiCharacter w.Completionˣ,
        let p := (realLocalEulerParameters w hw c).exists.choose
        infiniteLocalIdelicZFunction w f c = realArchimedeanMellin g p.2 p.1 := by
  let e : Multiplicative w.Completion ≃ₜ* Multiplicative ℝ :=
    { (InfinitePlace.Completion.ringEquivRealOfIsReal hw).toAddEquiv.toMultiplicative with
      continuous_toFun := (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).continuous
      continuous_invFun := (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.continuous }
  obtain ⟨E, hE⟩ := schwartzBruhat_realCoordinate_equiv e
  let g := E.symm f
  have hg : ∀ x : w.Completion,
      g (InfinitePlace.Completion.ringEquivRealOfIsReal hw x) = f (Multiplicative.ofAdd x) := by
    intro x
    have h := hE (E.symm f) (Multiplicative.ofAdd x)
    rw [E.apply_symm_apply] at h
    exact h.symm
  refine ⟨g, hg, ?_⟩
  intro c
  exact realArchimedeanMellin_eq_infiniteLocalIdelicZFunction_compare w hw f g hg c

/-- Euclidean coordinates identify Schwartz–Bruhat functions with classical Schwartz functions. -/
private theorem complexArchimedeanMellin_eq_infiniteLocalIdelicZFunction_euclidean
    {A : Type*} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] [T2Space A]
    [LocallyCompactSpace A] {n : ℕ}
    (v : A ≃ₜ* Multiplicative (EuclideanSpace ℝ (Fin n))) (g : A → ℂ) :
    g ∈ schwartzBruhatSubmodule A ↔
      ∃ s : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ, ∀ x, s (v x).toAdd = g x := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  let P := ElementaryLieGroup n 0 0 PUnit
  let D := (Fin 0 → AddCircle (1 : ℝ)) × (Fin 0 → ℤ) × PUnit
  let : Unique D := uniqueOfSubsingleton 0
  let p : Multiplicative E ≃ₜ* Multiplicative P :=
    { toMulEquiv := (AddEquiv.prodUnique (M := E) (N := D)).symm.toMultiplicative
      continuous_toFun := (continuous_id.prodMk continuous_const :
        Continuous (fun x : E ↦ (x, (default : D))))
      continuous_invFun := (continuous_fst : Continuous (Prod.fst : E × D → E)) }
  let e : ElementaryLCAPresentation A :=
    { realDim := n, torusDim := 0, latticeRank := 0, finiteFactor := PUnit, equiv := v.trans p }
  have hA := (lca_elementary_iff (G := A)).mpr ⟨e⟩
  let i : (⊤ : Subgroup A) ≃ₜ* A :=
    { Subgroup.topEquiv with
      continuous_toFun := continuous_subtype_val
      continuous_invFun := continuous_id.subtype_mk _ }
  let a : BruhatStructuralPair A := ⟨(⊤, OrderDual.toDual ⊥), by simp,
    isCompactlyGeneratedGroup_of_continuousMulEquiv i.symm hA.1,
    isBruhatGoodSubgroup_bot_iff.mpr hA.2, bot_le⟩
  let q₀ : A →* a.quotient := (QuotientGroup.mk' _).comp i.symm.toMulEquiv.toMonoidHom
  have hq₀ : IsOpenQuotientMap q₀ :=
    QuotientGroup.isOpenQuotientMap_mk.comp i.symm.toHomeomorph.isOpenQuotientMap
  have hinj : Injective q₀ := (MonoidHom.ker_eq_bot_iff q₀).mp (eq_bot_iff.mpr fun x hx ↦ by
    exact (a.quotient_mk_eq_one (i.symm x)).mp hx)
  let q := (MulEquiv.ofBijective q₀ ⟨hinj, hq₀.surjective⟩).toContinuousMulEquiv
    (fun _ ↦ hq₀.isQuotientMap.isOpen_preimage)
  let e₀ : ElementaryLCAPresentation a.quotient := { e with equiv := q.symm.trans e.equiv }
  have hreal (s : SchwartzBruhatStage e₀) (x : A) :
      schwartzBruhatStageRealization a e₀ s x = s ((v x).toAdd, 0, 0, PUnit.unit) := by
    have hx : x ∈ a.val.1 := Subgroup.mem_top x
    rw [schwartzBruhatStageRealization_apply, dite_eq_left hx]
    change s ((e₀.equiv (q x)).toAdd) = _
    change s ((e.equiv (q.symm (q x))).toAdd) = _
    rw [q.symm_apply_apply]
    rfl
  have hrange : schwartzBruhatSubmodule A = (schwartzBruhatStageRealization a e₀).range := by
    refine le_antisymm (iSup_le fun b ↦ iSup_le fun eb ↦ ?_) ?_
    · rintro _ ⟨sb, rfl⟩
      obtain ⟨j, hj, _⟩ := schwartzBruhatStage_transition (show b ≤ a from ⟨le_top, le_top⟩) eb e₀
      exact ⟨j sb, hj sb⟩
    · exact le_iSup_of_le a (le_iSup (fun e ↦ (schwartzBruhatStageRealization a e).range) e₀)
  rw [hrange, LinearMap.mem_range]
  constructor
  · rintro ⟨s, hs⟩
    let f : E → ℂ := fun x ↦ s (x, 0, 0, PUnit.unit)
    have hs' (y : P) : f y.1 = s y :=
      congrArg (fun z : P ↦ s z) (Prod.ext rfl (Subsingleton.elim _ _))
    have hf : (fun y : P ↦ f y.1) ∈ elementarySchwartzSubmodule n 0 0 PUnit :=
      (funext hs').symm ▸ s.property
    obtain ⟨S, hS⟩ := (elementarySchwartzSubmodule_real_iff f).mp hf
    refine ⟨S, fun x ↦ ?_⟩
    exact (congrFun hS (v x).toAdd).trans
      ((hreal s x).symm.trans (congrFun hs x))
  · rintro ⟨s, hs⟩
    let t : SchwartzBruhatStage e₀ :=
      ⟨fun y : P ↦ s y.1, (elementarySchwartzSubmodule_real_iff _).mpr ⟨s, rfl⟩⟩
    exact ⟨t, funext fun x ↦ (hreal t x).trans (hs x)⟩

/-- The complex coordinate model of a local Schwartz–Bruhat function is a Schwartz function. -/
private theorem complexArchimedeanMellin_eq_infiniteLocalIdelicZFunction_coordinates
    {F : Type*} [Field F] [NumberField F] (w : InfinitePlace F) (hw : w.IsComplex)
    (f : SchwartzBruhat (Multiplicative w.Completion)) :
    ∃ g : 𝓢(ℂ, ℂ), ∀ x : w.Completion,
      g (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw x) = f (Multiplicative.ofAdd x) := by
  let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
  let j := InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw
  let L : ℂ ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ ℂ)) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  let v : Multiplicative w.Completion ≃ₜ*
      Multiplicative (EuclideanSpace ℝ (Fin (Module.finrank ℝ ℂ))) :=
    { toMulEquiv := (e.toAddEquiv.trans L.toLinearEquiv.toAddEquiv).toMultiplicative
      continuous_toFun := L.continuous.comp j.continuous
      continuous_invFun := j.symm.continuous.comp L.symm.continuous }
  obtain ⟨G, hG⟩ :=
    (complexArchimedeanMellin_eq_infiniteLocalIdelicZFunction_euclidean v f).mp f.property
  exact ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L G,
    fun x ↦ hG (Multiplicative.ofAdd x)⟩

/-- Multiplicative Tamagawa integration in complex coordinates uses twice Lebesgue measure divided by the squared norm. -/
private theorem complexArchimedeanMellin_eq_infiniteLocalIdelicZFunction_complexLocalIntegral_model {F : Type*} [Field F] [NumberField F] (w : InfinitePlace F) (hw : w.IsComplex) (H : ℂ → ℂ) :
    let : MeasurableSpace w.Completion := borel _
    (∫ u : w.Completionˣ, H ((InfinitePlace.Completion.ringEquivComplexOfIsComplex hw) u.val) ∂(infiniteLocalMultiplicativeTamagawaMeasure F w)) =
      (2:ℂ) * ∫ t : ℂ, ((‖t‖ : ℂ)^2)⁻¹ * H t := by
  let : MeasurableSpace w.Completion := borel _
  classical
  let K := w.Completion
  let : BorelSpace K := ⟨rfl⟩
  let : BorelSpace Kˣ := borelSpace_units_of_continuousInv₀ K
  let e := (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw)
  let j := InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw
  let μ := infiniteLocalAdditiveTamagawaMeasure F w
  let D (x : K) : ENNReal := (↑(‖x‖₊ ^ w.mult) : ENNReal)⁻¹
  let ι : Kˣ → K := Units.val
  have hι : MeasurableEmbedding ι := (IsOpenUnits.isOpenEmbedding_unitsVal (M := K)).measurableEmbedding
  have hμ : μ = (2 • (volume : Measure ℂ)).map e.symm := by
    exact dite_eq_right (InfinitePlace.not_isReal_iff_isComplex.mpr hw)
  have hj : MeasurableEmbedding (e.symm : ℂ → K) := j.symm.toHomeomorph.measurableEmbedding
  have hμ₀ : μ {0} = 0 := by
    rw [hμ, hj.map_apply]
    have hpre : e.symm ⁻¹' ({0} : Set K) = {0} := by
      ext x
      exact e.symm.map_eq_zero_iff
    simp [hpre]
  have hneμ : ∀ᵐ x ∂μ, x ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not, ofPred_eq_eq_singleton] using hμ₀
  have hν : ∀ᵐ x ∂μ.withDensity D, x ≠ 0 :=
    (withDensity_absolutelyContinuous μ D).ae_le hneμ
  have hmap : ((infiniteLocalMultiplicativeTamagawaMeasure F w)).map ι = μ.withDensity D := by
    rw [infiniteLocalMultiplicativeTamagawaMeasure, hι.map_comap, Measure.restrict_eq_self_of_ae_mem]
    exact hν.mono fun x hx ↦ ⟨Units.mk0 x hx, rfl⟩
  have hD : Measurable D := (measurable_coe_nnreal_ennreal.comp ((continuous_nnNorm.pow w.mult).measurable)).inv
  have hfinite : ∀ᵐ x ∂μ, D x < ⊤ := by
    filter_upwards [hneμ] with x hx
    change x ≠ 0 at hx
    simp [D, hw.mult_eq_two]
    exact bot_lt_iff_ne_bot.mpr (pow_ne_zero _ (ENNReal.coe_ne_zero.mpr (nnNorm_ne_zero_iff.mpr hx)))
  calc
    _ = ∫ x : K, H (e x) ∂(((infiniteLocalMultiplicativeTamagawaMeasure F w)).map ι) := (hι.integral_map (fun x ↦ H (e x))).symm
    _ = ∫ x : K, (D x).toReal • H (e x) ∂μ := by rw [hmap, integral_withDensity_eq_integral_toReal_smul hD hfinite]
    _ = _ := by
      rw [hμ, hj.integral_map, show (2 • (volume : Measure ℂ)) = (2 : ENNReal) • volume by simp [two_smul], integral_smul_measure]
      simp only [ENNReal.toReal_ofNat, Complex.real_smul, Complex.ofReal_ofNat]
      congr 1
      apply integral_congr_ae
      filter_upwards with t
      have hn : ‖e.symm t‖ = ‖t‖ := j.symm.isometry.norm_map_of_map_zero (map_zero e.symm) _
      simp only [D, hw.mult_eq_two, ENNReal.toReal_inv, ENNReal.coe_toReal, coe_nnNorm,
        e.apply_symm_apply, hn, Complex.ofReal_inv, Complex.ofReal_pow, NNReal.coe_pow]

/-- Integral angular weights have unit norm. -/
private theorem complexArchimedeanMellin_eq_infiniteLocalIdelicZFunction_angularWeight_norm (r : ℤ) (θ : ℝ) : ‖(fun (r : ℤ) (θ : ℝ) ↦ Complex.exp ((r : ℂ) * (θ : ℂ) * Complex.I)) r θ‖ = 1 := by
  simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]

/-- Integral angular weights are smooth. -/
private theorem complexArchimedeanMellin_eq_infiniteLocalIdelicZFunction_angularWeight_smooth (r : ℤ) : ContDiff (ℝ) (∞) ((fun (r : ℤ) (θ : ℝ) ↦ Complex.exp ((r : ℂ) * (θ : ℂ) * Complex.I)) r) := by
  exact (Complex.contDiff_exp (𝕜 := ℝ)).comp ((contDiff_const.mul Complex.ofRealCLM.contDiff).mul contDiff_const)

/-- Angular averaging preserves rapid decay on the positive ray. -/
private theorem complexArchimedeanMellin_eq_infiniteLocalIdelicZFunction_angularProfile_decay {g : ℂ → ℂ} {f : SchwartzMap ℂ ℂ}
    (h : ∀ z, ‖g z‖ ≤ ‖f z‖) (r : ℤ) (p : ℝ) :
    (fun (g : ℂ → ℂ) (r : ℤ) (t : ℝ) ↦ ∫ θ in Ioo (-Real.pi) Real.pi, Complex.exp ((r : ℂ) * (θ : ℂ) * Complex.I) * g ((t : ℂ) * Complex.exp (((1 : ℤ) : ℂ) * (θ : ℂ) * Complex.I))) g r =O[atTop] (fun x : ℝ ↦ x^p) := by
  obtain ⟨C,hC⟩ := (f.isBigO_cocompact_rpow p).bound
  obtain ⟨R,hR⟩ := (Metric.mem_cocompact_iff_closedBall_compl_subset (0:ℂ)).mp hC
  refine Asymptotics.isBigO_iff.mpr ⟨C * volume.real (Ioo (-Real.pi) Real.pi), ?_⟩
  filter_upwards [eventually_gt_atTop (max R 0)] with t ht
  have ht₀ : 0<t := (le_max_right _ _).trans_lt ht
  have hn (θ : ℝ) : ‖(t:ℂ) * (fun (r : ℤ) (θ : ℝ) ↦ Complex.exp ((r : ℂ) * (θ : ℂ) * Complex.I)) 1 θ‖ = t := by
    simp [abs_of_pos ht₀]
  have hnorm (θ : ℝ) : ‖(fun (r : ℤ) (θ : ℝ) ↦ Complex.exp ((r : ℂ) * (θ : ℂ) * Complex.I)) r θ * g ((t:ℂ)*(fun (r : ℤ) (θ : ℝ) ↦ Complex.exp ((r : ℂ) * (θ : ℂ) * Complex.I)) 1 θ)‖ ≤ C * ‖t^p‖ := by
    rw [norm_mul, complexArchimedeanMellin_eq_infiniteLocalIdelicZFunction_angularWeight_norm, one_mul]
    have hx : (t:ℂ)*(fun (r : ℤ) (θ : ℝ) ↦ Complex.exp ((r : ℂ) * (θ : ℂ) * Complex.I)) 1 θ ∉ Metric.closedBall 0 R := by
      rw [Metric.mem_closedBall, dist_zero_right, hn]
      exact not_le.mpr ((le_max_left _ _).trans_lt ht)
    have hb : ‖f ((t:ℂ)*(fun (r : ℤ) (θ : ℝ) ↦ Complex.exp ((r : ℂ) * (θ : ℂ) * Complex.I)) 1 θ)‖ ≤ C * ‖‖(t:ℂ)*(fun (r : ℤ) (θ : ℝ) ↦ Complex.exp ((r : ℂ) * (θ : ℂ) * Complex.I)) 1 θ‖^p‖ := hR hx
    rw [hn θ] at hb
    exact (h _).trans hb
  exact (norm_setIntegral_le_of_norm_le_const (measure_mono Ioo_subset_Icc_self |>.trans_lt
    (isCompact_Icc.measure_lt_top (μ := volume))) (fun θ _ ↦ hnorm θ)).trans_eq (by ring)

/-- Absolute integrability permits angular integration before the radial Mellin transform. -/
private theorem complexArchimedeanMellin_eq_infiniteLocalIdelicZFunction_angularMellin_fubini (g : SchwartzMap ℂ ℂ) (r : ℤ) (z : ℂ) (hz : 0 < z.re) :
    (∫ p in Ioi (0 : ℝ) ×ˢ (Ioo (-Real.pi) Real.pi), (p.1:ℂ)^(z-1) * ((fun (r : ℤ) (θ : ℝ) ↦ Complex.exp ((r : ℂ) * (θ : ℂ) * Complex.I)) r p.2 *
      g ((p.1:ℂ)*(fun (r : ℤ) (θ : ℝ) ↦ Complex.exp ((r : ℂ) * (θ : ℂ) * Complex.I)) 1 p.2))) = mellin ((fun (g : ℂ → ℂ) (r : ℤ) (t : ℝ) ↦ ∫ θ in Ioo (-Real.pi) Real.pi, Complex.exp ((r : ℂ) * (θ : ℂ) * Complex.I) * g ((t : ℂ) * Complex.exp (((1 : ℤ) : ℂ) * (θ : ℂ) * Complex.I))) g r) z := by
  let J := fun p : ℝ × ℝ ↦ (p.1:ℂ)^(z-1) * ((fun (r : ℤ) (θ : ℝ) ↦ Complex.exp ((r : ℂ) * (θ : ℂ) * Complex.I)) r p.2 * g ((p.1:ℂ)*(fun (r : ℤ) (θ : ℝ) ↦ Complex.exp ((r : ℂ) * (θ : ℂ) * Complex.I)) 1 p.2))
  let B (t : ℝ) := ∫ θ in (Ioo (-Real.pi) Real.pi), ‖g ((t:ℂ)*(fun (r : ℤ) (θ : ℝ) ↦ Complex.exp ((r : ℂ) * (θ : ℂ) * Complex.I)) 1 θ)‖
  let Bc (t : ℝ) : ℂ := B t
  have hω (j : ℤ) := (complexArchimedeanMellin_eq_infiniteLocalIdelicZFunction_angularWeight_smooth j).continuous
  have hfin : volume (Ioo (-Real.pi) Real.pi) < ⊤ := (measure_mono Ioo_subset_Icc_self).trans_lt isCompact_Icc.measure_lt_top
  have hc : Continuous B := by
    apply continuous_of_dominated (bound := fun _ ↦ SchwartzMap.seminorm ℝ 0 0 g)
    · intro x
      exact (g.continuous.comp (continuous_const.mul (hω 1))).norm.aestronglyMeasurable
    · intro x
      exact .of_forall fun θ ↦ (Real.norm_of_nonneg (norm_nonneg _)).le.trans (g.norm_le_seminorm ℝ _)
    · exact integrableOn_const hfin.ne
    · exact .of_forall fun θ ↦ (g.continuous.comp (Complex.continuous_ofReal.mul continuous_const)).norm
  have he : Bc = (fun (g : ℂ → ℂ) (r : ℤ) (t : ℝ) ↦ ∫ θ in Ioo (-Real.pi) Real.pi, Complex.exp ((r : ℂ) * (θ : ℂ) * Complex.I) * g ((t : ℂ) * Complex.exp (((1 : ℤ) : ℂ) * (θ : ℂ) * Complex.I))) (fun x ↦ (‖g x‖ : ℂ)) 0 := by
    funext t
    simp [Bc, B, integral_complex_ofReal]
  have hbc : Continuous Bc := Complex.continuous_ofReal.comp hc
  have hdec (p : ℝ) : Bc =O[atTop] fun t : ℝ ↦ t^p := by
    rw [he]
    exact complexArchimedeanMellin_eq_infiniteLocalIdelicZFunction_angularProfile_decay (g := fun x ↦ (‖g x‖ : ℂ)) (f := g) (fun x ↦ by simp) 0 p
  have hconv : MellinConvergent Bc z := mellinConvergent_of_isBigO_rpow
    (hbc.continuousOn.locallyIntegrableOn measurableSet_Ioi) (hdec _) (lt_add_one z.re)
    (b := 0) (by simpa using (hbc.continuousAt (x := 0)).isBigO_one ℝ |>.mono nhdsWithin_le_nhds) hz
  let μ := (volume : Measure ℝ).restrict (Ioi 0)
  let ν := (volume : Measure ℝ).restrict (Ioo (-Real.pi) Real.pi)
  have hmeas : Measurable J := by
    exact ((Complex.continuous_ofReal.comp continuous_fst).measurable.pow measurable_const).mul
      (((hω r).comp continuous_snd).mul (g.continuous.comp
        ((Complex.continuous_ofReal.comp continuous_fst).mul ((hω 1).comp continuous_snd)))).measurable
  have hInt : Integrable J (μ.prod ν) := by
    apply (integrable_prod_iff hmeas.aestronglyMeasurable).mpr
    constructor
    · apply Eventually.of_forall
      intro t
      have ht : Continuous (fun θ : ℝ ↦ J (t,θ)) :=
        (continuous_const (y := (t:ℂ)^(z-1))).mul ((hω r).mul (g.continuous.comp
          ((continuous_const (y := (t:ℂ))).mul (hω 1))))
      exact (ht.continuousOn.integrableOn_compact (K := Icc (-Real.pi) Real.pi) isCompact_Icc).mono_set Ioo_subset_Icc_self
    · apply hconv.norm.congr
      filter_upwards with t
      change ‖(t:ℂ)^(z-1) * Bc t‖ = ∫ θ in (Ioo (-Real.pi) Real.pi), ‖J (t,θ)‖
      simp only [J, norm_mul, complexArchimedeanMellin_eq_infiniteLocalIdelicZFunction_angularWeight_norm, one_mul, integral_const_mul, Bc, Complex.norm_real,
        Real.norm_of_nonneg (show 0 ≤ B t from integral_nonneg fun _ ↦ norm_nonneg _)]
      rfl
  change (∫ p in Ioi (0:ℝ) ×ˢ (Ioo (-Real.pi) Real.pi), J p) = _
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod J hInt]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  exact integral_const_mul (μ := ν) ((t:ℂ)^(z-1)) (fun θ ↦ (fun (r : ℤ) (θ : ℝ) ↦ Complex.exp ((r : ℂ) * (θ : ℂ) * Complex.I)) r θ * g ((t:ℂ)*(fun (r : ℤ) (θ : ℝ) ↦ Complex.exp ((r : ℂ) * (θ : ℂ) * Complex.I)) 1 θ))

/-- Polar coordinates express the complex local integral as twice a radial Mellin transform. -/
private theorem complexArchimedeanMellin_eq_infiniteLocalIdelicZFunction_complexIntegral_shape {F : Type*} [Field F] [NumberField F] (w : InfinitePlace F) (hw : w.IsComplex)
    (g : SchwartzMap ℂ ℂ) (c : QuasiCharacter w.Completionˣ) (z : ℂ) (r : ℤ)
    (hc : (∀ x : ℂˣ, c (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm.toMonoidHom x) = ((‖(x : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ z * ((x : ℂ) / (‖(x : ℂ)‖ : ℂ)) ^ r)) (hz : 0 < z.re) :
    let : MeasurableSpace w.Completion := borel _
    localIdelicZetaIntegral (infiniteLocalMultiplicativeTamagawaMeasure F w) (fun x ↦ g ((InfinitePlace.Completion.ringEquivComplexOfIsComplex hw) x)) c =
      2 * mellin ((fun (g : ℂ → ℂ) (r : ℤ) (t : ℝ) ↦ ∫ θ in Ioo (-Real.pi) Real.pi, Complex.exp ((r : ℂ) * (θ : ℂ) * Complex.I) * g ((t : ℂ) * Complex.exp (((1 : ℤ) : ℂ) * (θ : ℂ) * Complex.I))) g r) (2*z) := by
  let : MeasurableSpace w.Completion := borel _
  let e := (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw)
  let H (t : ℂ) := g t * (((‖t‖^2:ℝ):ℂ)^z * (t / (‖t‖:ℂ))^r)
  have he (u : w.Completionˣ) : g (e u.val) * c u = H (e u.val) := by
    let x := Units.map e.toMonoidHom u
    have h := hc x
    rw [show Units.map e.symm.toMonoidHom x = u from Units.ext (e.symm_apply_apply u.val)] at h
    exact congrArg (g (e u.val) * ·) h
  change (∫ u : w.Completionˣ, g (e u.val) * c u ∂(infiniteLocalMultiplicativeTamagawaMeasure F w)) = _
  rw [integral_congr_ae (.of_forall he)]
  rw [complexArchimedeanMellin_eq_infiniteLocalIdelicZFunction_complexLocalIntegral_model, ← Complex.integral_comp_polarCoord_symm, polarCoord_target]
  congr 1
  rw [← complexArchimedeanMellin_eq_infiniteLocalIdelicZFunction_angularMellin_fubini g r (2*z) (by simpa using mul_pos (by norm_num : (0:ℝ)<2) hz)]
  apply setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
  intro p hp
  obtain ⟨t,θ⟩ := p
  have ht : 0<t := hp.1
  have ht' : (t:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hn : ‖Complex.polarCoord.symm (t,θ)‖ = t := (Complex.norm_polarCoord_symm _).trans (abs_of_pos ht)
  have ha : Complex.polarCoord.symm (t,θ) = (t:ℂ)*(fun (r : ℤ) (θ : ℝ) ↦ Complex.exp ((r : ℂ) * (θ : ℂ) * Complex.I)) 1 θ := by
    simp [Complex.polarCoord_symm_apply, Complex.exp_mul_I]
  have hpow : (((t:ℂ)^2)^z) = (t:ℂ)^(2*z) := by
    rw [pow_two, Complex.mul_cpow_ofReal_nonneg ht.le ht.le]
    rw [show (2:ℂ)*z = z+z by ring, Complex.cpow_add _ _ ht']
  have hr : ((fun (r : ℤ) (θ : ℝ) ↦ Complex.exp ((r : ℂ) * (θ : ℂ) * Complex.I)) 1 θ)^r = (fun (r : ℤ) (θ : ℝ) ↦ Complex.exp ((r : ℂ) * (θ : ℂ) * Complex.I)) r θ := by
    simp only [Int.cast_one, one_mul, ← Complex.exp_int_mul]
    congr 1
    ring
  dsimp only [H, Prod.fst, Prod.snd]
  rw [hn, ha, Complex.real_smul, mul_div_cancel_left₀ _ ht', hr, Complex.ofReal_pow, hpow, Complex.cpow_sub _ _ ht', Complex.cpow_one]
  field_simp

/-- Changing the angular interval and substituting the squared radius gives the complex Mellin profile. -/
private theorem complexArchimedeanMellin_eq_infiniteLocalIdelicZFunction_change (g : ℂ → ℂ) (n : ℤ) (s : ℂ) :
    mellin (fun t : ℝ ↦ ∫ θ in (0 : ℝ)..(2 * Real.pi),
      (Complex.exp ((θ : ℂ) * Complex.I)) ^ n *
        g ((Real.sqrt t : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) s =
    2 * mellin (fun t : ℝ ↦ ∫ θ in Set.Ioo (-Real.pi) Real.pi,
      Complex.exp ((n : ℂ) * (θ : ℂ) * Complex.I) *
        g ((t : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) (2 * s) := by
  let A (t : ℝ) := ∫ θ in Set.Ioo (-Real.pi) Real.pi,
    Complex.exp ((n : ℂ) * (θ : ℂ) * Complex.I) *
      g ((t : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
  have hp (t : ℝ) : (∫ θ in (0 : ℝ)..(2 * Real.pi),
      (Complex.exp ((θ : ℂ) * Complex.I)) ^ n *
        g ((t : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) = A t := by
    let H (θ : ℝ) := (Complex.exp ((θ : ℂ) * Complex.I)) ^ n *
      g ((t : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
    have hper : Function.Periodic H (2 * Real.pi) := by
      intro θ
      have he : Complex.exp (((θ + 2 * Real.pi : ℝ) : ℂ) * Complex.I) =
          Complex.exp ((θ : ℂ) * Complex.I) := by
        rw [Complex.ofReal_add, add_mul, Complex.exp_add]
        simp [Complex.ofReal_mul, Complex.exp_two_pi_mul_I]
      simp only [H, he]
    have h := hper.intervalIntegral_add_eq 0 (-Real.pi)
    rw [zero_add, show -Real.pi + 2 * Real.pi = Real.pi by ring] at h
    rw [h, intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi),
      integral_Ioc_eq_integral_Ioo]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro θ _
    dsimp [H, A]
    rw [← Complex.exp_int_mul]
    congr 2
    ring
  have hprofile : (fun t : ℝ ↦ ∫ θ in (0 : ℝ)..(2 * Real.pi),
      (Complex.exp ((θ : ℂ) * Complex.I)) ^ n *
        g ((Real.sqrt t : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) =
      fun t : ℝ ↦ A (t ^ (1 / 2 : ℝ)) := by
    funext t
    rw [hp, Real.sqrt_eq_rpow]
  rw [hprofile, mellin_comp_rpow]
  norm_num [Complex.real_smul, smul_eq_mul, div_eq_mul_inv]
  congr 1
  ring

/-- Uniqueness of continuation identifies the complex Mellin transform with the local zeta function. -/
private theorem complexArchimedeanMellin_eq_infiniteLocalIdelicZFunction_compare
    {F : Type*} [Field F] [NumberField F] (w : InfinitePlace F) (hw : w.IsComplex)
    (f : SchwartzBruhat (Multiplicative w.Completion)) (g : 𝓢(ℂ, ℂ))
    (hg : ∀ x : w.Completion,
      g (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw x) = f (Multiplicative.ofAdd x)) :
    ∀ c : QuasiCharacter w.Completionˣ,
      infiniteLocalIdelicZFunction w f c =
        complexArchimedeanMellin g (complexLocalEulerParameters w hw c).exists.choose.2
          (complexLocalEulerParameters w hw c).exists.choose.1 := by
  let Z (c : QuasiCharacter w.Completionˣ) :=
    complexArchimedeanMellin g (complexLocalEulerParameters w hw c).exists.choose.2
      (complexLocalEulerParameters w hw c).exists.choose.1
  have hZ : Z = infiniteLocalIdelicZFunction w f := by
    apply (infiniteLocalIdelicZFunction_existsUnique w f).unique
    · intro χ
      let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
      let i : ℂˣ →ₜ* w.Completionˣ := ⟨Units.map e.symm.toMonoidHom,
        (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).symm.continuous.units_map _⟩
      let unit : QuasiCharacter w.Completionˣ :=
        (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ
      obtain ⟨p, ht, hp⟩ :=
        (existsUnique_complexUnits_character_parameters (unit.comp i)
          (fun _ ↦ Circle.norm_coe _)).exists
      let chart := quasiCharacterNormTwist
        (Units.map nnNormHom.toMonoidHom ^ w.mult) (continuous_infiniteLocalModule w) unit
      have hshape (s : ℂ) (x : ℂˣ) :
          chart s (Units.map e.symm.toMonoidHom x) =
            ((‖(x : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ (s + p.1) *
              ((x : ℂ) / (‖(x : ℂ)‖ : ℂ)) ^ p.2 := by
        have hn : ‖e.symm x.val‖ = ‖x.val‖ :=
          (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).symm.isometry.norm_map_of_map_zero
            (map_zero e.symm) x.val
        change unit (Units.map e.symm.toMonoidHom x) *
          ((‖e.symm x.val‖ ^ w.mult : ℝ) : ℂ) ^ s = _
        have hx := hp x
        change unit (Units.map e.symm.toMonoidHom x) = _ at hx
        rw [hx, hn, hw.mult_eq_two,
          Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr x.ne_zero)))]
        ring
      have hparam (s : ℂ) :
          (complexLocalEulerParameters w hw (chart s)).exists.choose = (s + p.1, p.2) :=
        (complexLocalEulerParameters w hw (chart s)).unique
          (complexLocalEulerParameters w hw (chart s)).exists.choose_spec (hshape s)
      have he : (Z ∘ chart) = fun s ↦ complexArchimedeanMellin g p.2 (s + p.1) := by
        funext s
        dsimp only [Function.comp_def, Z]
        rw [hparam]
      change MeromorphicNFOn (Z ∘ chart) univ ∧ _
      constructor
      · rw [he]
        intro s _
        exact (meromorphicNFAt_comp_add_const_iff_meromorphicNFAt
          (f := complexArchimedeanMellin g p.2)).mpr
          ((complexArchimedeanMellin_existsUnique g p.2).exists.choose_spec.1 (mem_univ _))
      · intro s hs
        change (Z ∘ chart) s = _
        rw [he]
        dsimp only
        have hz : 0 < (s + p.1).re := by simpa [Complex.add_re, ht] using hs
        rw [complexArchimedeanMellin_eq_integral g p.2 _ hz, complexArchimedeanMellin_eq_infiniteLocalIdelicZFunction_change]
        have hf : (fun x ↦ f (Multiplicative.ofAdd x)) = fun x ↦ g (e x) :=
          funext fun x ↦ (hg x).symm
        rw [hf]
        simpa only [Int.cast_one, one_mul] using (complexArchimedeanMellin_eq_infiniteLocalIdelicZFunction_complexIntegral_shape
          w hw g (chart s) (s + p.1) p.2 (hshape s) hz).symm
    · exact (infiniteLocalIdelicZFunction_existsUnique w f).exists.choose_spec
  intro c
  exact congrFun hZ.symm c

/-- Paper: Proposition 5.3.3.4, p. 258.
In the complex field model the local zeta function of §3.3 is the angular Mellin transform
at the squared-norm exponent and angular weight of the given quasi-character. -/
theorem complexArchimedeanMellin_eq_infiniteLocalIdelicZFunction
    {F : Type*} [Field F] [NumberField F] (w : InfinitePlace F) (hw : w.IsComplex)
    (f : SchwartzBruhat (Multiplicative w.Completion)) :
    ∃ g : 𝓢(ℂ, ℂ), (∀ x : w.Completion,
      g (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw x) = f (Multiplicative.ofAdd x)) ∧
      ∀ c : QuasiCharacter w.Completionˣ,
        let p := (complexLocalEulerParameters w hw c).exists.choose
        infiniteLocalIdelicZFunction w f c = complexArchimedeanMellin g p.2 p.1 := by
  obtain ⟨g, hg⟩ := complexArchimedeanMellin_eq_infiniteLocalIdelicZFunction_coordinates w hw f
  exact ⟨g, hg, complexArchimedeanMellin_eq_infiniteLocalIdelicZFunction_compare w hw f g hg⟩

local notation "realMonomial(" n ")" => SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ) ^ n)
local notation "complexMonomial(" p ", " q ")" =>
  SchwartzMap.smulLeftCLM ℂ (fun z : ℂ ↦ z ^ p * star z ^ q)
local notation "shiftParity(" ε ", " n ")" => Fin.ofNat 2 ((ε).val + n)
local notation "rhoReal(" ε ", " s ")" =>
  ((Complex.I ^ (ε).val) *
    (Complex.Gammaℝ (s + (ε).val) / Complex.Gammaℝ (1 - s + (ε).val)))
local notation "rhoComplex(" n ", " s ")" =>
  ((Complex.I ^ (n).natAbs) *
    (Complex.Gammaℂ (s + ((n).natAbs : ℂ) / 2) / Complex.Gammaℂ (1 - s + ((n).natAbs : ℂ) / 2)))

/-- Translating the argument preserves meromorphic normal form on the whole plane. -/
private theorem archimedeanMellin_meromorphicNFOn_comp_add_const {L : ℂ → ℂ}
    (hL : MeromorphicNFOn L univ) (d : ℂ) : MeromorphicNFOn (fun s ↦ L (s + d)) univ := fun _ _ ↦
  (meromorphicNFAt_comp_add_const_iff_meromorphicNFAt (f := L)).mpr (hL (mem_univ _))

-- TODO(paper-gap): (5.3.3.28) drops M_{x^n} on the left. Its proof supplies the multiplier.

/-- Paper: Proposition 5.3.3.4(1), p. 258.
Multiplying by xⁿ shifts the real Mellin exponent by n and shifts the sign character by
the parity of n.
Deviation: The multiplier on the left is restored from (5.3.3.32)–(5.3.3.34). -/
theorem realArchimedeanMellin_monomial (n : ℕ) (ε : Fin 2) (f : 𝓢(ℝ, ℂ)) :
    realArchimedeanMellin (realMonomial(n) f) ε =
      fun s ↦ realArchimedeanMellin f shiftParity(ε, n) (s + n) := by
  have hspec := (realArchimedeanMellin_existsUnique f shiftParity(ε, n)).exists.choose_spec
  have hg : (fun x : ℝ ↦ (x : ℂ) ^ n).HasTemperateGrowth := Complex.hasTemperateGrowth_ofReal.pow n
  -- On the profiles, the monomial is the Mellin shift by n with the parity moved by n.
  have hprofile : realProfile(realMonomial(n) f, ε) =
      fun t : ℝ ↦ (t : ℂ) ^ (n : ℂ) • realProfile(f, shiftParity(ε, n)) t := by
    funext t
    have hsign : (-1 : ℂ) ^ (shiftParity(ε, n)).val = (-1) ^ ε.val * (-1) ^ n := by
      rw [Fin.val_ofNat, ← neg_one_pow_eq_pow_mod_two, pow_add]
    change SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ) ^ n) f t +
        (-1 : ℂ) ^ ε.val * SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ) ^ n) f (-t) =
      (t : ℂ) ^ (n : ℂ) • (f t + (-1 : ℂ) ^ (shiftParity(ε, n)).val * f (-t))
    rw [SchwartzMap.smulLeftCLM_apply_apply hg, SchwartzMap.smulLeftCLM_apply_apply hg, hsign,
      Complex.cpow_natCast, Complex.ofReal_neg, neg_pow]
    simp only [smul_eq_mul]
    ring
  refine (realArchimedeanMellin_existsUnique (realMonomial(n) f) ε).unique
    (realArchimedeanMellin_existsUnique (realMonomial(n) f) ε).exists.choose_spec
    ⟨archimedeanMellin_meromorphicNFOn_comp_add_const hspec.1 n, fun s hs ↦ ?_⟩
  have hsn : 0 < (s + (n : ℂ)).re := by
    rw [Complex.add_re, Complex.natCast_re]
    positivity
  have h := hspec.2 (s + n) hsn
  rw [hprofile]
  exact ⟨MellinConvergent.cpow_smul.mpr h.1, (mellin_cpow_smul _ s n).trans h.2⟩

/-- Paper: Proposition 5.3.3.4(1), p. 258.
The real monomial Mellin transform satisfies the Fourier relation at the shifted
exponent and parity. The product is understood as a meromorphic identity. -/
theorem realArchimedeanMellin_monomial_functionalEquation (n : ℕ) (ε : Fin 2) (f : 𝓢(ℝ, ℂ)) :
    ∀ᶠ s : ℂ in codiscrete ℂ,
      let a := shiftParity(ε, n)
      let t := s + (n : ℂ)
      realArchimedeanMellin (realMonomial(n) f) ε s =
        rhoReal(a, t) * realArchimedeanMellin (𝓕 f) a (1 - t) := by sorry

/-- Paper: Proposition 5.3.3.4(2), p. 258.
Multiplying by zᵖ times the qth power of its conjugate shifts the Mellin exponent
by (p+q)/2 and the angular weight by p−q. -/
theorem complexArchimedeanMellin_monomial (p q : ℕ) (n : ℤ) (f : 𝓢(ℂ, ℂ)) :
    complexArchimedeanMellin (complexMonomial(p, q) f) n =
      fun s ↦ complexArchimedeanMellin f (n + (p : ℤ) - q) (s + ((p : ℂ) + q) / 2) := by
  have hspec := (complexArchimedeanMellin_existsUnique f (n + (p : ℤ) - q)).exists.choose_spec
  have hg : (fun z : ℂ ↦ z ^ p * star z ^ q).HasTemperateGrowth :=
    (Function.HasTemperateGrowth.id'.pow p).mul (Complex.conjCLE.hasTemperateGrowth.pow q)
  have hE (θ : ℝ) : unitAngle(θ) ≠ 0 := Complex.exp_ne_zero _
  have hstar (θ : ℝ) : star (unitAngle(θ)) = (unitAngle(θ))⁻¹ := by
    rw [← Complex.exp_neg, Complex.star_def, ← Complex.exp_conj]
    congr 1
    simp
  -- For positive t the monomial contributes the radial power t^((p+q)/2) and the angular
  -- weight p - q.
  have hprofile : EqOn (complexProfile(complexMonomial(p, q) f, n))
      (fun t : ℝ ↦ (t : ℂ) ^ (((p : ℂ) + q) / 2) • complexProfile(f, n + (p : ℤ) - q) t)
      (Ioi 0) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    have hroot : (Real.sqrt t : ℂ) ^ (p + q) = (t : ℂ) ^ (((p : ℂ) + q) / 2) := by
      have hr : Real.sqrt t ^ (p + q) = t ^ (((p : ℝ) + q) / 2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ht0.le]
        congr 1
        push_cast
        ring
      rw [← Complex.ofReal_pow, hr, Complex.ofReal_cpow ht0.le]
      congr 1
      push_cast
      ring
    change (∫ θ in (0 : ℝ)..(2 * Real.pi), unitAngle(θ) ^ n *
        SchwartzMap.smulLeftCLM ℂ (fun z : ℂ ↦ z ^ p * star z ^ q) f
          ((Real.sqrt t : ℂ) * unitAngle(θ))) =
      (t : ℂ) ^ (((p : ℂ) + q) / 2) • ∫ θ in (0 : ℝ)..(2 * Real.pi),
        unitAngle(θ) ^ (n + (p : ℤ) - q) * f ((Real.sqrt t : ℂ) * unitAngle(θ))
    rw [smul_eq_mul, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun θ _ ↦ ?_
    have hz : star ((Real.sqrt t : ℂ) * unitAngle(θ)) = (Real.sqrt t : ℂ) * (unitAngle(θ))⁻¹ := by
      rw [star_mul', hstar]
      congr 1
      exact Complex.conj_ofReal _
    change unitAngle(θ) ^ n *
        SchwartzMap.smulLeftCLM ℂ (fun z : ℂ ↦ z ^ p * star z ^ q) f
          ((Real.sqrt t : ℂ) * unitAngle(θ)) =
      (t : ℂ) ^ (((p : ℂ) + q) / 2) *
        (unitAngle(θ) ^ (n + (p : ℤ) - q) * f ((Real.sqrt t : ℂ) * unitAngle(θ)))
    rw [SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul, hz, ← hroot, mul_pow, mul_pow,
      pow_add, zpow_sub₀ (hE θ), zpow_add₀ (hE θ), zpow_natCast, zpow_natCast, inv_pow]
    ring
  refine (complexArchimedeanMellin_existsUnique (complexMonomial(p, q) f) n).unique
    (complexArchimedeanMellin_existsUnique (complexMonomial(p, q) f) n).exists.choose_spec
    ⟨archimedeanMellin_meromorphicNFOn_comp_add_const hspec.1 _, fun s hs ↦ ?_⟩
  have hsa : 0 < (s + ((p : ℂ) + q) / 2).re := by
    have hre : (((p : ℂ) + q) / 2).re = ((p : ℝ) + q) / 2 := by
      rw [show ((p : ℂ) + q) / 2 = ((((p : ℝ) + q) / 2 : ℝ) : ℂ) by push_cast; ring,
        Complex.ofReal_re]
    rw [Complex.add_re, hre]
    positivity
  have h := hspec.2 _ hsa
  have hmul : EqOn
      (fun t : ℝ ↦ (t : ℂ) ^ (s - 1) • complexProfile(complexMonomial(p, q) f, n) t)
      (fun t : ℝ ↦ (t : ℂ) ^ (s - 1) •
        ((t : ℂ) ^ (((p : ℂ) + q) / 2) • complexProfile(f, n + (p : ℤ) - q) t)) (Ioi 0) :=
    fun t ht ↦ congrArg (fun w : ℂ ↦ (t : ℂ) ^ (s - 1) • w) (hprofile ht)
  exact ⟨IntegrableOn.congr_fun (MellinConvergent.cpow_smul.mpr h.1) hmul.symm measurableSet_Ioi,
    (setIntegral_congr_fun measurableSet_Ioi hmul).trans
      ((mellin_cpow_smul _ s (((p : ℂ) + q) / 2)).trans h.2)⟩

-- TODO(paper-gap): The complex phase in (5.3.3.25) disagrees with the trace-pairing Fourier
-- transform for nontrivial angular weights. Use the phase from §3.3, per ERRATA I91.

/-- Paper: Proposition 5.3.3.4(2), p. 258.
The complex monomial Mellin transform satisfies the Fourier relation at the shifted
exponent and angular weight. The trace-pairing transform is the Euclidean Fourier
transform evaluated at twice the conjugate argument and multiplied by the self-dual mass factor.
Deviation: The phase is i to the absolute angular weight, as in ERRATA I91. -/
theorem complexArchimedeanMellin_monomial_functionalEquation (p q : ℕ) (n : ℤ)
    (f : 𝓢(ℂ, ℂ)) :
    ∃ fHat : 𝓢(ℂ, ℂ), (∀ z : ℂ, fHat z = 2 * (𝓕 f) (2 * star z)) ∧
      ∀ᶠ s : ℂ in codiscrete ℂ,
        let k := n + (p : ℤ) - q
        let t := s + ((p : ℂ) + q) / 2
        complexArchimedeanMellin (complexMonomial(p, q) f) n s =
          rhoComplex(k, t) * complexArchimedeanMellin fHat (-k) (1 - t) := by sorry

end ArchimedeanMellin

section SAdele

open Classical

variable {F : Type*} [Field F] [NumberField F]
variable {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "ℬ(" R ")" => SchwartzBruhat (Multiplicative R)
local notation "Aₛ" => SAdeleRing F S
local notation "ℬₛ" => ℬ(Aₛ)
local notation "Jₛ" => SIdeleQuotient F S
local notation "mₛ" => sIdeleQuotientNorm F S
local notation "J₁" => (mₛ).ker
local notation "Xₛ" => QuasiCharacter Jₛ
local notation "circleToComplex" => (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ)
local notation "chartₛ(" χ ")" =>
  quasiCharacterNormTwist (G := Jₛ) mₛ (isProperMap_sIdeleQuotientNorm F S).continuous
    ((circleToComplex).comp (χ))
local notation "χ₁(" χ ")" =>
  ((χ : Jₛ →ₜ* Circle).comp
    (⟨((mₛ).ker).subtype, continuous_subtype_val⟩ : J₁ →ₜ* Jₛ) : PontryaginDual J₁)
local notation "thetaAt(" χ ")" => sLocalHomogeneousAdelicThetaLinearMap F S (χ)
local notation "A∞" => InfiniteAdeleRing F
local notation "RealPlaces" => {w : InfinitePlace F // w.IsReal}
local notation "ComplexPlaces" => {w : InfinitePlace F // w.IsComplex}
local notation "ArchCoordinates" => ((RealPlaces → ℝ) × (ComplexPlaces → ℂ))
local notation "RealModels" => ((w : RealPlaces) →
  {e : w.val.Completion ≃+* ℝ // IsHomeomorph (e : w.val.Completion → ℝ)})
local notation "ComplexModels" => ((w : ComplexPlaces) →
  {e : w.val.Completion ≃+* ℂ // IsHomeomorph (e : w.val.Completion → ℂ)})
local notation "assemble(" r ", " c ", " x ")" =>
  (show A∞ from fun w ↦ if h : w.IsReal then ((r ⟨w, h⟩).val.symm) ((x).1 ⟨w, h⟩)
    else ((c ⟨w, InfinitePlace.not_isReal_iff_isComplex.mp h⟩).val.symm)
      ((x).2 ⟨w, InfinitePlace.not_isReal_iff_isComplex.mp h⟩))

-- TODO(paper-gap): In (5.3.4.1), (5.3.4.7) and (5.3.4.15), the finite
-- zero-extension factors must be compactly supported locally constant tests on the
-- units. Remark 2.1.2.1 distinguishes these from the full multiplicative Schwartz
-- space. On Q_p, the sequence p^(-k) on shells of valuation k ≥ 0 is Schwartz on Z,
-- but its zero extension is not locally constant at zero.

/-- Paper: Definition 5.3.4.1, p. 259.
A function on the unit group has an additive Schwartz extension vanishing at zero
exactly when it is locally constant and compactly supported there.
Deviation: The finite punctured test space in (5.3.4.1) is interpreted as
compactly supported locally constant tests, consistently with Remark 2.1.2.1. -/
theorem exists_finitePlaceSchwartz_zeroExtension_iff (v : V) (h : (v.adicCompletion F)ˣ → ℂ) :
    (∃ f : ℬ(v.adicCompletion F), f (Multiplicative.ofAdd 0) = 0 ∧
      ∀ u : (v.adicCompletion F)ˣ, f (Multiplicative.ofAdd u.val) = h u) ↔
      IsLocallyConstant h ∧ HasCompactSupport h := by
  classical
  let K := v.adicCompletion F
  let j : Kˣ → K := Units.val
  have hj : IsOpenEmbedding j := Units.isOpenEmbedding_val
  have hn : (0 : K) ∉ Set.range j := by
    rintro ⟨u, hu⟩
    exact u.ne_zero hu
  constructor
  · rintro ⟨f, hzero, hh⟩
    let g : K → ℂ := fun x ↦ f (Multiplicative.ofAdd x)
    have hg := (mem_finitePlaceSchwartz_iff F v g).mp ⟨f, fun _ ↦ rfl⟩
    have he : h = g ∘ j := funext fun u ↦ (hh u).symm
    refine ⟨he.symm ▸ hg.1.comp_continuous hj.continuous, ?_⟩
    have hc : IsCompact (Function.support g) := by
      have hs : IsClosed (Function.support g) := (hg.1.isOpen_fiber 0).isClosed_compl
      simpa only [tsupport, hs.closure_eq] using (show IsCompact (tsupport g) from hg.2)
    have hr : Function.support g ⊆ Set.range j := by
      intro x hx
      have hx0 : x ≠ 0 := fun h ↦ hx (h ▸ hzero)
      exact ⟨Units.mk0 x hx0, rfl⟩
    apply HasCompactSupport.of_support_subset_isCompact
      ((hj.isEmbedding.isInducing.isCompact_preimage_iff hr).2 hc)
    intro u hu
    exact fun hz ↦ hu ((hh u).symm.trans hz)
  · rintro ⟨hl, hc⟩
    let g : K → ℂ := Function.extend j h (fun _ ↦ 0)
    have he (u : Kˣ) : g (j u) = h u := hj.injective.extend_apply _ _ _
    have hz {x : K} (hx : x ∉ Set.range j) : g x = 0 :=
      Function.extend_apply' _ _ _ hx
    have hk : IsCompact (j '' tsupport h) := hc.image hj.continuous
    have hs : Function.support g ⊆ j '' tsupport h := by
      intro x hx
      by_cases hr : x ∈ Set.range j
      · obtain ⟨u, rfl⟩ := hr
        exact ⟨u, subset_tsupport h (fun hu ↦ hx ((he u).trans hu)), rfl⟩
      · exact False.elim (hx (hz hr))
    have hl' : IsLocallyConstant g := by
      rw [IsLocallyConstant.iff_exists_open]
      intro x
      by_cases hr : x ∈ Set.range j
      · obtain ⟨u, rfl⟩ := hr
        refine ⟨j '' {w | h w = h u}, hj.isOpenMap _ (hl.isOpen_fiber _), ⟨u, rfl, rfl⟩, ?_⟩
        rintro _ ⟨w, hw, rfl⟩
        exact (he w).trans (hw.trans (he u).symm)
      · refine ⟨(j '' tsupport h)ᶜ, hk.isClosed.isOpen_compl, ?_, ?_⟩
        · rintro ⟨u, _, hu⟩
          exact hr ⟨u, hu⟩
        · intro y hy
          exact (not_not.mp (fun hy' ↦ hy (hs hy'))).trans (hz hr).symm
    obtain ⟨f, hf⟩ :=
      (mem_finitePlaceSchwartz_iff F v g).mpr ⟨hl', HasCompactSupport.of_support_subset_isCompact hk hs⟩
    exact ⟨f, (hf 0).trans (hz hn), fun u ↦ (hf (j u)).trans (he u)⟩

/-- Paper: Definition 5.3.4.1, p. 259.
The finite-place conditions are the kernels of evaluation at adeles with a zero
coordinate at one of the selected finite places. -/
def sAdeleFiniteZeroSchwartz (S T : Finset V) : Submodule ℂ ℬ(SAdeleRing F S) :=
  ⨅ x : {x : SAdeleRing F S // ∃ v : S, v.val ∈ T ∧ x.2 v = 0},
    LinearMap.ker ((LinearMap.proj (Multiplicative.ofAdd x.val)).comp
      (schwartzBruhatSubmodule (Multiplicative (SAdeleRing F S))).subtype)

/-- Paper: Definition 5.3.4.1, p. 259.
Passing from a Schwartz function in archimedean coordinates to its underlying
function is complex-linear. -/
theorem archimedeanSchwartz_coe_isLinear :
    IsLinearMap ℂ (fun f : 𝓢(ArchCoordinates, ℂ) ↦ (f : ArchCoordinates → ℂ)) :=
  ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩

/-- Paper: Definition 5.3.4.1, p. 259.
The polar-free subspace imposes flatness on every archimedean slice and vanishing
at a zero coordinate at every finite place.
Deviation: The finite punctured factors in (5.3.4.1) are compactly supported tests on
the units. The subspace has the topology inherited from the S-adelic Schwartz space
of Proposition 2.1.4.1, which uses the inductive archimedean–finite tensor topology.
The span identity below is algebraic. The projective topology in print is generally coarser. -/
def sAdelePolarFree (S : Finset V) (r : RealModels) (c : ComplexModels) :
    Submodule ℂ ℬ(SAdeleRing F S) :=
  sAdeleFiniteZeroSchwartz S S ⊓
    ⨅ y : (v : S) → v.val.adicCompletion F,
      let flat := (archimedeanFlatSchwartz (ι := RealPlaces) (κ := ComplexPlaces)).map
        ((archimedeanSchwartz_coe_isLinear (F := F)).mk' _)
      let slice := LinearMap.funLeft ℂ ℂ (fun x : ArchCoordinates ↦
        Multiplicative.ofAdd (assemble(r, c, x), y))
      flat.comap (slice.comp (schwartzBruhatSubmodule (Multiplicative (SAdeleRing F S))).subtype)

/-- Paper: Definition 5.3.4.1, p. 259.
For a pure tensor with nonzero factors, finite-coordinate vanishing is exactly
vanishing at zero of each factor selected by T. -/
theorem sAdeleFiniteZeroSchwartz_tmul_iff (T : Finset V)
    (f : ℬ(A∞)) (g : ∀ v : S, ℬ(v.val.adicCompletion F)) (_hf : f ≠ 0)
    (_hg : ∀ v, g v ≠ 0) :
    let e := (sAdeleSchwartz_inductiveTensor_equiv F S).choose
    e (f ⊗ₜ[ℂ] (⨂ₜ[ℂ] v, g v)) ∈ sAdeleFiniteZeroSchwartz S T ↔
      ∀ v : S, v.val ∈ T → g v (Multiplicative.ofAdd 0) = 0 := by
  classical
  let e := (sAdeleSchwartz_inductiveTensor_equiv F S).choose
  let u := e (f ⊗ₜ[ℂ] (⨂ₜ[ℂ] v, g v))
  let X := {x : SAdeleRing F S // ∃ v : S, v.val ∈ T ∧ x.2 v = 0}
  have mem : u ∈ sAdeleFiniteZeroSchwartz S T ↔ ∀ x : X, u (Multiplicative.ofAdd x.val) = 0 :=
    Submodule.mem_iInf _
  have he (x : SAdeleRing F S) : u (Multiplicative.ofAdd x) =
      f (Multiplicative.ofAdd x.1) * ∏ v : S, g v (Multiplicative.ofAdd (x.2 v)) :=
    (sAdeleSchwartz_inductiveTensor_equiv F S).choose_spec f g x
  change u ∈ sAdeleFiniteZeroSchwartz S T ↔ _
  rw [mem]
  constructor
  · intro hu v hv
    by_contra hne
    obtain ⟨a, ha⟩ : ∃ a : A∞, f (Multiplicative.ofAdd a) ≠ 0 := by
      by_contra! hn
      exact _hf (Subtype.ext (funext fun x ↦ hn x.toAdd))
    have hnon (w : S) : ∃ y : w.val.adicCompletion F, g w (Multiplicative.ofAdd y) ≠ 0 := by
      by_contra! hn
      exact _hg w (Subtype.ext (funext fun x ↦ hn x.toAdd))
    choose y hy using hnon
    let b := Function.update y v 0
    have hz := hu ⟨(a, b), v, hv, Function.update_self ..⟩
    rw [he] at hz
    apply (mul_ne_zero ha (Finset.prod_ne_zero_iff.mpr ?_)) hz
    intro w _
    by_cases hw : w = v
    · subst w
      simpa [b] using hne
    · simpa [b, Function.update_of_ne hw] using hy w
  · intro h x
    obtain ⟨v, hv, hx⟩ := x.property
    rw [he, Finset.prod_eq_zero (Finset.mem_univ v) (by rw [hx, h v hv]), mul_zero]

/-- Paper: Proposition 5.3.4.5(3), p. 264.
The selected finite zero-coordinate conditions cut out the span in (5.3.4.15).
Deviation: At the selected places its factors are the zero extensions of compactly
supported locally constant tests on the unit group. -/
theorem sAdeleFiniteZeroSchwartz_eq_span_tmul (T : Finset V) :
    let e := (sAdeleSchwartz_inductiveTensor_equiv F S).choose
    sAdeleFiniteZeroSchwartz S T = Submodule.span ℂ {h : ℬₛ |
      ∃ (f : ℬ(A∞)) (g : ∀ v : S, ℬ(v.val.adicCompletion F)),
        (∀ v : S, v.val ∈ T → g v (Multiplicative.ofAdd 0) = 0) ∧
        e (f ⊗ₜ[ℂ] (⨂ₜ[ℂ] v, g v)) = h} := by sorry

/-- Paper: Definition 5.3.4.1, p. 259.
The slice definition equals the span of the corrected pure tensors in (5.3.4.1). Their
archimedean factor is flat and their finite factors vanish at zero. -/
theorem sAdelePolarFree_eq_span_tmul (r : RealModels) (c : ComplexModels) :
    let e := (sAdeleSchwartz_inductiveTensor_equiv F S).choose
    sAdelePolarFree S r c = Submodule.span ℂ {h : ℬₛ |
      ∃ (f : ℬ(A∞)) (g : ∀ v : S, ℬ(v.val.adicCompletion F)),
        (∃ f₀ : archimedeanFlatSchwartz (ι := RealPlaces) (κ := ComplexPlaces),
          ∀ x : ArchCoordinates, f₀.val x = f (Multiplicative.ofAdd (assemble(r, c, x)))) ∧
        (∀ v : S, g v (Multiplicative.ofAdd 0) = 0) ∧
        e (f ⊗ₜ[ℂ] (⨂ₜ[ℂ] v, g v)) = h} := by sorry

/-- Paper: Lemma 5.3.4.2(1), p. 260.
The polar-free functions form a closed subspace in the S-adelic Schwartz–Bruhat topology. -/
theorem sAdelePolarFree_isClosed (r : RealModels) (c : ComplexModels) :
    IsClosed (↑(sAdelePolarFree S r c) : Set ℬₛ) := by sorry

/-- Paper: Lemma 5.3.4.2(1), p. 260.
Inverse left translation by an S-idele preserves the polar-free subspace. -/
theorem sAdelePolarFree_translate (r : RealModels) (c : ComplexModels)
    (g : Aₛˣ) (f : ℬₛ) (_hf : f ∈ sAdelePolarFree S r c) :
    schwartzBruhatUnitTranslate g f ∈ sAdelePolarFree S r c := by
  classical
  obtain ⟨hz, hflat⟩ := Submodule.mem_inf.1 _hf
  let u : Aₛ := (g⁻¹ : Aₛˣ).val
  have hu (w : InfinitePlace F) : u.1 w ≠ 0 := by
    have h1 : u.1 w * (g : Aₛ).1 w = 1 := by
      change (u * (g : Aₛ)).1 w = 1
      simp only [u, Units.inv_mul]
      rfl
    exact left_ne_zero_of_mul_eq_one h1
  refine Submodule.mem_inf.2 ⟨?_, ?_⟩
  · -- Multiplying by a unit keeps a zero finite coordinate.
    simp only [sAdeleFiniteZeroSchwartz, Submodule.mem_iInf, LinearMap.mem_ker] at hz ⊢
    rintro ⟨x, v, hv, hx⟩
    exact hz ⟨u * x, v, hv, by simp [hx]⟩
  · -- The archimedean part of the unit dilates the coordinates of every slice.
    let a : RealPlaces → ℝ := fun w ↦ (r w).val (u.1 w.val)
    let b : ComplexPlaces → ℂ := fun w ↦ (c w).val (u.1 w.val)
    have ha (w : RealPlaces) : a w ≠ 0 := (map_ne_zero_iff _ (r w).val.injective).2 (hu w.val)
    have hb (w : ComplexPlaces) : b w ≠ 0 := (map_ne_zero_iff _ (c w).val.injective).2 (hu w.val)
    let L : ArchCoordinates ≃ₗ[ℝ] ArchCoordinates :=
      { toFun := fun x ↦ (fun w ↦ a w * x.1 w, fun w ↦ b w * x.2 w)
        invFun := fun x ↦ (fun w ↦ (a w)⁻¹ * x.1 w, fun w ↦ (b w)⁻¹ * x.2 w)
        map_add' := fun x y ↦ Prod.ext (funext fun w ↦ mul_add _ _ _)
          (funext fun w ↦ mul_add _ _ _)
        map_smul' := fun t x ↦ Prod.ext (funext fun w ↦ by simp [mul_left_comm])
          (funext fun w ↦ by simp [Complex.real_smul, mul_left_comm])
        left_inv := fun x ↦ Prod.ext (funext fun w ↦ inv_mul_cancel_left₀ (ha w) _)
          (funext fun w ↦ inv_mul_cancel_left₀ (hb w) _)
        right_inv := fun x ↦ Prod.ext (funext fun w ↦ mul_inv_cancel_left₀ (ha w) _)
          (funext fun w ↦ mul_inv_cancel_left₀ (hb w) _) }
    let D : ArchCoordinates ≃L[ℝ] ArchCoordinates := L.toContinuousLinearEquiv
    have hD (x : ArchCoordinates) : D x = (fun w ↦ a w * x.1 w, fun w ↦ b w * x.2 w) := rfl
    have hasm (x : ArchCoordinates) : u.1 * assemble(r, c, x) = assemble(r, c, D x) := by
      funext w
      change u.1 w * _ = _
      by_cases hw : w.IsReal
      · simp only [hw, ↓reduceDIte, hD, a, map_mul, RingEquiv.symm_apply_apply]
      · simp only [hw, ↓reduceDIte, hD, b, map_mul, RingEquiv.symm_apply_apply]
    simp only [Submodule.mem_iInf] at hflat ⊢
    intro y
    have hy := hflat (u.2 * y)
    simp only [Submodule.mem_comap, Submodule.mem_map] at hy ⊢
    obtain ⟨h, hh, hfun⟩ := hy
    refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ D h, ?_, ?_⟩
    · simp only [archimedeanFlatSchwartz, Submodule.mem_iInf, LinearMap.mem_ker,
        IsLinearMap.mk'_apply] at hh ⊢
      rintro ⟨x, hx⟩ n v
      have hwall : (∃ i, (D x).1 i = 0) ∨ (∃ j, (D x).2 j = 0) := by
        rcases hx with ⟨i, hi⟩ | ⟨j, hj⟩
        · exact Or.inl ⟨i, by simp [hD, hi]⟩
        · exact Or.inr ⟨j, by simp [hD, hj]⟩
      have hcomp := D.toContinuousLinearMap.iteratedFDeriv_comp_right (h.smooth ⊤) x
        (i := n) (mod_cast le_top)
      change iteratedFDeriv ℝ n ((h : ArchCoordinates → ℂ) ∘ D) x v = 0
      erw [hcomp]
      exact hh ⟨D x, hwall⟩ n (fun i ↦ D (v i))
    · funext x
      have e := congrFun hfun (D x)
      refine e.trans ?_
      change f (Multiplicative.ofAdd (assemble(r, c, D x), u.2 * y)) =
        f (Multiplicative.ofAdd (u * (assemble(r, c, x), y)))
      rw [← hasm]
      rfl

/-- Composing a flat Schwartz function with a real-linear automorphism of the
archimedean coordinates that keeps the coordinate walls keeps it flat. -/
private theorem archimedeanFlatSchwartz_comp_wall (D : ArchCoordinates ≃L[ℝ] ArchCoordinates)
    (hD : ∀ x : ArchCoordinates, ((∃ i, x.1 i = 0) ∨ (∃ j, x.2 j = 0)) →
      ((∃ i, (D x).1 i = 0) ∨ (∃ j, (D x).2 j = 0)))
    (h : 𝓢(ArchCoordinates, ℂ))
    (hh : h ∈ archimedeanFlatSchwartz (ι := RealPlaces) (κ := ComplexPlaces)) :
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ D h ∈
      archimedeanFlatSchwartz (ι := RealPlaces) (κ := ComplexPlaces) := by
  simp only [archimedeanFlatSchwartz, Submodule.mem_iInf, LinearMap.mem_ker,
    IsLinearMap.mk'_apply] at hh ⊢
  rintro ⟨x, hx⟩ n v
  have hcomp := D.toContinuousLinearMap.iteratedFDeriv_comp_right (h.smooth ⊤) x
    (i := n) (mod_cast le_top)
  change iteratedFDeriv ℝ n ((h : ArchCoordinates → ℂ) ∘ D) x v = 0
  erw [hcomp]
  exact hh ⟨D x, hD x hx⟩ n (fun i ↦ D (v i))

/-- Changing the archimedean field identifications changes each slice by a
real-linear automorphism of the coordinates that keeps the walls. -/
private theorem sAdelePolarFree_le_of_models (r r' : RealModels) (c c' : ComplexModels) :
    sAdelePolarFree S r c ≤ sAdelePolarFree S r' c' := by
  classical
  intro f hf
  obtain ⟨hz, hflat⟩ := Submodule.mem_inf.1 hf
  refine Submodule.mem_inf.2 ⟨hz, ?_⟩
  -- At a real place both identifications agree, since `ℝ` has one ring endomorphism.
  have hR (w : RealPlaces) (t : ℝ) : (r' w).val.symm t = (r w).val.symm t := by
    have hρ : (r w).val.toRingHom.comp (r' w).val.symm.toRingHom = RingHom.id ℝ :=
      Subsingleton.elim _ _
    have h1 := RingHom.congr_fun hρ t
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingHom.id_apply] at h1
    calc (r' w).val.symm t = (r w).val.symm ((r w).val ((r' w).val.symm t)) :=
          ((r w).val.symm_apply_apply _).symm
      _ = (r w).val.symm t := by rw [h1]
  -- At a complex place they differ by a continuous automorphism of `ℂ`.
  have hcont (w : ComplexPlaces) : Continuous (c' w).val.symm := by
    convert (IsHomeomorph.homeomorph _ (c' w).property).symm.continuous using 1
    funext z
    apply (c' w).property.injective
    rw [RingEquiv.apply_symm_apply]
    exact ((IsHomeomorph.homeomorph _ (c' w).property).apply_symm_apply z).symm
  let ψ (w : ComplexPlaces) : ℂ →+* ℂ :=
    (c w).val.toRingHom.comp (c' w).val.symm.toRingHom
  let ψ' (w : ComplexPlaces) : ℂ →+* ℂ :=
    (c' w).val.toRingHom.comp (c w).val.symm.toRingHom
  have hψ (w : ComplexPlaces) (z : ℂ) : ψ w z = (c w).val ((c' w).val.symm z) := rfl
  have hψ' (w : ComplexPlaces) (z : ℂ) : ψ' w z = (c' w).val ((c w).val.symm z) := rfl
  have hreal (w : ComplexPlaces) (t : ℝ) : ψ w t = t := by
    rcases Complex.ringHom_eq_id_or_conj_of_continuous (f := ψ w)
      ((c w).property.continuous.comp (hcont w)) with h | h
    · rw [h, RingHom.id_apply]
    · rw [h]
      exact Complex.conj_ofReal t
  let L : ArchCoordinates ≃ₗ[ℝ] ArchCoordinates :=
    { toFun := fun x ↦ (x.1, fun w ↦ ψ w (x.2 w))
      invFun := fun x ↦ (x.1, fun w ↦ ψ' w (x.2 w))
      map_add' := fun x y ↦ Prod.ext rfl (funext fun w ↦ map_add _ _ _)
      map_smul' := fun t x ↦ Prod.ext rfl (funext fun w ↦ by
        change ψ w (t • x.2 w) = t • ψ w (x.2 w)
        rw [Complex.real_smul, Complex.real_smul, map_mul, hreal])
      left_inv := fun x ↦ Prod.ext rfl (funext fun w ↦ by
        change ψ' w (ψ w (x.2 w)) = x.2 w
        rw [hψ, hψ', RingEquiv.symm_apply_apply, RingEquiv.apply_symm_apply])
      right_inv := fun x ↦ Prod.ext rfl (funext fun w ↦ by
        change ψ w (ψ' w (x.2 w)) = x.2 w
        rw [hψ, hψ', RingEquiv.symm_apply_apply, RingEquiv.apply_symm_apply]) }
  let D : ArchCoordinates ≃L[ℝ] ArchCoordinates := L.toContinuousLinearEquiv
  have hD (x : ArchCoordinates) : D x = (x.1, fun w ↦ ψ w (x.2 w)) := rfl
  have hwall (x : ArchCoordinates) : ((∃ i, x.1 i = 0) ∨ (∃ j, x.2 j = 0)) →
      ((∃ i, (D x).1 i = 0) ∨ (∃ j, (D x).2 j = 0)) := by
    rintro (⟨i, hi⟩ | ⟨j, hj⟩)
    · exact Or.inl ⟨i, by simp [hD, hi]⟩
    · exact Or.inr ⟨j, by simp [hD, hj]⟩
  have hasm (x : ArchCoordinates) : assemble(r, c, D x) = assemble(r', c', x) := by
    funext w
    by_cases hw : w.IsReal
    · simp only [hw, ↓reduceDIte, hD, hR]
    · simp only [hw, ↓reduceDIte, hD, hψ, RingEquiv.symm_apply_apply]
  simp only [Submodule.mem_iInf] at hflat ⊢
  intro y
  have hy := hflat y
  simp only [Submodule.mem_comap, Submodule.mem_map] at hy ⊢
  obtain ⟨h, hh, hfun⟩ := hy
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ D h,
    archimedeanFlatSchwartz_comp_wall D hwall h hh, ?_⟩
  funext x
  refine (congrFun hfun (D x)).trans ?_
  change f (Multiplicative.ofAdd (assemble(r, c, D x), y)) =
    f (Multiplicative.ofAdd (assemble(r', c', x), y))
  rw [hasm]

/-- Paper: Lemma 5.3.4.2(1), p. 260.
The polar-free subspace is independent of the archimedean field identifications. -/
theorem sAdelePolarFree_eq_of_models (r r' : RealModels) (c c' : ComplexModels) :
    sAdelePolarFree S r c = sAdelePolarFree S r' c' :=
  le_antisymm (sAdelePolarFree_le_of_models r r' c c') (sAdelePolarFree_le_of_models r' r c' c)

-- TODO(paper-gap): The proof of (2) starts from entireness and concludes local vanishing.
-- Restricted local characters are coupled by the S-units, and a pole can cancel against
-- a zero of a different factor. The stated implication goes in the other direction.

/-- Paper: Lemma 5.3.4.2(2), p. 260.
The zeta transform of a polar-free test is entire on every norm-twist component. -/
theorem sLocalIdelicZFunction_entire_of_polarFree (r : RealModels) (c : ComplexModels)
    (f : ℬₛ) (_hf : f ∈ sAdelePolarFree S r c) (χ : PontryaginDual Jₛ) :
    AnalyticOnNhd ℂ (fun s ↦ sLocalIdelicZFunction f (chartₛ(χ) s)) univ := by sorry

/-- Paper: Lemma 5.3.4.2(3), p. 260.
A continuous quasi-character of the S-ideles trivial on S-units acts on polar-free
functions by pointwise multiplication and defines a linear homeomorphism.
The character is given on the S-idele quotient. -/
theorem sAdelePolarFree_quasiCharacter_mul (r : RealModels) (c : ComplexModels) (b : Xₛ) :
    ∃ M : ↥(sAdelePolarFree S r c) ≃L[ℂ] ↥(sAdelePolarFree S r c),
      ∀ f (g : Aₛˣ), (M f).val (Multiplicative.ofAdd g.val) =
        b (QuotientGroup.mk g) * f.val (Multiplicative.ofAdd g.val) := by sorry

-- TODO(paper-gap): In (5.3.4.9), the summation index m_v does not occur in the summand.
-- Norm-one class representatives with archimedean component one need not exist.

/-- Paper: Lemma 5.3.4.3, p. 261.
Every log-Schwartz function decaying at all real exponents lifts to a polar-free test
whose trivial homogeneous theta function is the given radial function. -/
theorem sLocalHomogeneousTheta_trivial_exists_polarFree (r : RealModels) (c : ComplexModels)
    (φ : PositiveRealExponentialDecay univ) :
    ∃ f : sAdelePolarFree S r c, ∀ g : Jₛ,
      thetaAt(1) f.val g = φ.val (Real.log ((mₛ g).val : ℝ)) := by sorry

/-- Paper: Proposition 5.3.4.4(1)–(2), p. 264.
On the component of χ, a zeta transform is entire exactly when it agrees there
with the transform of a polar-free test. -/
theorem sLocalIdelicZFunction_entire_iff_eq_polarFree (r : RealModels) (c : ComplexModels)
    (χ : PontryaginDual Jₛ) (f : ℬₛ) :
    AnalyticOnNhd ℂ (fun s ↦ sLocalIdelicZFunction f (chartₛ(χ) s)) univ ↔
      ∃ f₀ : sAdelePolarFree S r c, ∀ s : ℂ,
        sLocalIdelicZFunction f (chartₛ(χ) s) = sLocalIdelicZFunction f₀.val (chartₛ(χ) s) := by sorry

/-- Paper: Proposition 5.3.4.4(1) and (3), p. 264.
On the component of χ, a zeta transform is entire exactly when the homogeneous theta
function has exponential decay at every real exponent. Its covariance is the
norm-one isotype property already supplied by §2.3. -/
theorem sLocalIdelicZFunction_entire_iff_theta_exponentialDecay (χ : PontryaginDual Jₛ) (f : ℬₛ) :
    AnalyticOnNhd ℂ (fun s ↦ sLocalIdelicZFunction f (chartₛ(χ) s)) univ ↔
      (⇑(thetaAt(χ₁(χ)) f) : Jₛ → ℂ) ∈ modulatedExponentialDecaySubmodule
        ⟨mₛ, (isProperMap_sIdeleQuotientNorm F S).continuous⟩ univ := by sorry

/-- Mellin integration turns a compact unit average followed by dilation into the
average of the character times the scalar dilation. -/
private theorem sLocalIdelicZFunction_principalValue_average {G : Type*} [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (U : Subgroup G) (π : G) (f : G → ℂ) (hf : Continuous f) (c : G →ₜ* ℂ)
    (hfc : Integrable (fun x ↦ f x * c x) μ) (hc : IntegrableOn c U μ) :
    (∫ x, (f x - (μ.real U : ℂ)⁻¹ *
      ∫ u in U, f (u⁻¹ * (π⁻¹ * x)) ∂μ) * c x ∂μ) =
      (1 - (μ.real U : ℂ)⁻¹ * (∫ u in U, c u ∂μ) * c π) *
        ∫ x, f x * c x ∂μ := by
  let b (u x : G) := f (u⁻¹ * (π⁻¹ * x)) * c x
  let h (x : G) := f x * c x
  have hb (u x : G) : b u x = (c u * c π) * h ((π * u)⁻¹ * x) := by
    have hx : x = (π * u) * ((π * u)⁻¹ * x) := by group
    unfold b h
    rw [← mul_assoc, ← mul_inv_rev, congrArg c hx, map_mul, map_mul]
    ring
  have hcont : Continuous (Function.uncurry b) := by
    unfold Function.uncurry b
    fun_prop
  have hnorm (u : G) : (∫ x, ‖h ((π * u)⁻¹ * x)‖ ∂μ) = ∫ x, ‖h x‖ ∂μ :=
    integral_mul_left_eq_self (μ := μ) (fun x ↦ ‖h x‖) _
  have hh : Integrable h μ := hfc
  have hi : Integrable (Function.uncurry b) ((μ.restrict U).prod μ) := by
    refine (integrable_prod_iff hcont.aestronglyMeasurable).mpr ⟨.of_forall fun u ↦ ?_, ?_⟩
    · simpa only [Function.uncurry_apply_pair, Function.comp_apply, hb] using
        ((measurePreserving_mul_left μ (π * u)⁻¹).integrable_comp_of_integrable hh).const_mul (c u * c π)
    · simp only [Function.uncurry_apply_pair, hb, norm_mul, integral_const_mul, hnorm]
      exact (hc.norm.mul_const _).mul_const _
  have hsub (x : G) : (f x - (μ.real U : ℂ)⁻¹ * ∫ u in U, f (u⁻¹ * (π⁻¹ * x)) ∂μ) * c x =
      h x - (μ.real U : ℂ)⁻¹ * ∫ u in U, b u x ∂μ := by
    rw [sub_mul, mul_assoc, ← integral_mul_const]
  simp_rw [hsub]
  have hbi : Integrable (fun x ↦ ∫ u in U, b u x ∂μ) μ := hi.integral_prod_right
  rw [integral_sub hh (hbi.const_mul _), integral_const_mul,
    ← integral_integral_swap hi]
  simp_rw [hb, integral_const_mul, integral_mul_left_eq_self, integral_mul_const]
  ring

/-- The integral of a character over the integer units is zero unless the character
is trivial there. -/
private theorem sLocalIdelicZFunction_principalValue_units {G : Type*} [CommGroup G]
    [MeasurableSpace G] [MeasurableMul G] [TopologicalSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] (U : Subgroup G) (hU : MeasurableSet (U : Set G))
    (c : G →ₜ* ℂ) :
    (∫ u in U, c u ∂μ) = if ∀ u ∈ U, c u = 1 then (μ.real U : ℂ) else 0 := by
  classical
  split_ifs with h
  · rw [setIntegral_congr_fun hU h, setIntegral_const, Complex.real_smul, mul_one]
  · obtain ⟨a, ha, hne⟩ := not_forall.mp h |>.imp fun a h ↦ not_imp.mp h
    have he : (fun x : G ↦ a * x) ⁻¹' (U : Set G) = U := by
      ext x
      exact U.mul_mem_cancel_left ha
    have hv := (measurePreserving_mul_left μ a).setIntegral_preimage_emb
      (MeasurableEquiv.mulLeft a).measurableEmbedding (fun u ↦ c u) (U : Set G)
    rw [he] at hv
    simp only [map_mul, integral_const_mul] at hv
    exact (mul_eq_zero.mp (show (c a - 1) * (∫ u in U, c u ∂μ) = 0 by linear_combination hv)).resolve_left
      (sub_ne_zero.mpr hne)

/-- Restricting the global norm chart to a finite component gives the local norm chart. -/
private theorem sLocalIdelicZFunction_principalValue_chart (χ : PontryaginDual Jₛ) (v : S) :
    ∃ η : PontryaginDual (v.val.adicCompletion F)ˣ, ∀ z, sLocalFiniteRestriction v (chartₛ(χ) z) =
      quasiCharacterNormTwist _ (continuous_finiteLocalModule v.val) ((circleToComplex).comp η) z := by
  let h := sLocalFiniteInsertion_properties v
  let i : (v.val.adicCompletion F)ˣ →ₜ* Jₛ :=
    ⟨{ toFun := fun g ↦ QuotientGroup.mk ((ContinuousMulEquiv.prodUnits (InfiniteAdeleRing F)
          ((v : S) → v.val.adicCompletion F)).symm (1, ContinuousMulEquiv.piUnits.symm
            (@Pi.mulSingle _ _ _ (Classical.decEq _) v g))),
       map_one' := h.1, map_mul' := h.2.1 }, h.2.2⟩
  refine ⟨χ.comp i, fun z ↦ ContinuousMonoidHom.ext fun g ↦ ?_⟩
  have hn := sLocalFiniteRestriction_norm v g
  change ((1 : PontryaginDual Jₛ) (i g) : ℂ) *
    (((mₛ (i g) : ℝ≥0) : ℝ) : ℂ) ^ (1 : ℂ) = _ at hn
  simp only [PontryaginDual.one_apply, Circle.coe_one, one_mul, Complex.cpow_one] at hn
  exact congrArg (fun t : ℂ ↦ (χ (i g) : ℂ) * t ^ z) hn

/-- The local principal value multiplies the zeta integral by the inverse Euler factor. -/
private theorem sLocalIdelicZFunction_principalValue_finite (v : S) (f : ℬ(v.val.adicCompletion F))
    (χ : PontryaginDual Jₛ) (z : ℂ) (hz : 0 < z.re) :
    letI : MeasurableSpace (v.val.adicCompletion F)ˣ := borel _
    let c := sLocalFiniteRestriction v (chartₛ(χ) z)
    let μ := finiteLocalMultiplicativeTamagawaMeasure F v.val
    localIdelicZetaIntegral μ (fun x ↦ finitePlacePrincipalValue v.val f (Multiplicative.ofAdd x)) c =
      localIdelicZetaIntegral μ (fun x ↦ f (Multiplicative.ofAdd x)) c / finiteLocalEulerFactor v.val c := by
  let : MeasurableSpace (v.val.adicCompletion F)ˣ := borel _
  intro c μ
  let K := v.val.adicCompletion F
  let O := v.val.adicCompletionIntegers F
  let : ProperSpace K := properSpace_adicCompletion v.val
  let : SecondCountableTopology Kˣ := (Units.isEmbedding_val₀ (G₀ := K)).secondCountableTopology
  let : BorelSpace Kˣ := ⟨rfl⟩
  let : μ.IsHaarMeasure := finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure v.val
  let hp := (Valued.v : Valuation K (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
  let π : Kˣ := Units.mk0 (hp.choose : K) hp.choose_spec.ne_zero
  let h (u : Kˣ) := f (Multiplicative.ofAdd u.val)
  have hcont : Continuous h := (schwartzBruhat_continuous f).comp (continuous_ofAdd.comp Units.continuous_val)
  obtain ⟨η, hη⟩ := sLocalIdelicZFunction_principalValue_chart χ v
  have hf : Integrable (fun u ↦ h u * c u) μ := by
    dsimp only [c]
    rw [hη]
    exact finiteLocalIdelicZetaIntegral_integrable v.val f η hz
  have hK : IsCompact (O.units : Set Kˣ) := Submonoid.units_isCompact
    (isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v.val))
  have hO : IsOpen (O.units : Set Kˣ) := Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)
  have hm : (μ.real O.units : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (finitePlacePrincipalValue_integrable v.val π f (Multiplicative.ofAdd 0)).1.ne'
  have hram : (∀ u : Oˣ, c (Units.map O.subtype.toMonoidHom u) = 1) ↔ ∀ u ∈ O.units, c u = 1 := by
    constructor
    · intro H u hu
      let t : Oˣ := ⟨⟨u.val, hu.1⟩, ⟨u.inv, hu.2⟩, Subtype.ext u.val_inv, Subtype.ext u.inv_val⟩
      exact H t
    · intro H u
      exact H _ ⟨u.val.property, u.inv.property⟩
  let avg (x : Kˣ) := ∫ u in O.units, h (u⁻¹ * (π⁻¹ * x)) ∂μ
  have hev (x : Kˣ) : finitePlacePrincipalValue v.val f (Multiplicative.ofAdd x.val) =
      h x - (μ.real O.units : ℂ)⁻¹ * avg x :=
    finitePlacePrincipalValue_spec v.val π hp.choose_spec f _
  have hI := sLocalIdelicZFunction_principalValue_average μ O.units π h hcont c hf
    (c.continuous.continuousOn.integrableOn_compact hK)
  let Z := ∫ x, h x * c x ∂μ
  have hF : 1 - (μ.real O.units : ℂ)⁻¹ * (∫ u in O.units, c u ∂μ) * c π =
      (finiteLocalEulerFactor v.val c)⁻¹ := by
    rw [sLocalIdelicZFunction_principalValue_units μ O.units hO.measurableSet c]
    unfold finiteLocalEulerFactor
    rw [hram]
    split_ifs <;> simp only [inv_inv, inv_mul_cancel₀ hm, one_mul, mul_zero, zero_mul, sub_zero, inv_one]
    rfl
  calc
    _ = ∫ x, (h x - (μ.real O.units : ℂ)⁻¹ * avg x) * c x ∂μ :=
      integral_congr_ae (.of_forall fun x ↦ congrArg (· * c x) (hev x))
    _ = (1 - (μ.real O.units : ℂ)⁻¹ * (∫ u in O.units, c u ∂μ) * c π) * Z := hI
    _ = _ := (congrArg (· * Z) hF).trans (mul_comm _ _)

/-- The product of finitely many local tests belongs to the Schwartz–Bruhat space
of the product group. -/
private theorem sLocalIdelicZFunction_principalValue_productTest {ι : Type*} [Fintype ι] (G : ι → Type*)
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
    obtain ⟨g, hg⟩ := sLocalIdelicZFunction_principalValue_productTest (ι := J) (fun j ↦ G j.val) (fun j ↦ f j.val)
    let e : ((j : ι) → G j) ≃ₜ* (G i × ((j : J) → G j.val)) :=
      { Homeomorph.piSplitAt i G with map_mul' := fun _ _ ↦ rfl }
    obtain ⟨t, ht⟩ := schwartzBruhat_kernel_equiv (G := G i) (H := (j : J) → G j.val)
    let q := t (UniformSpace.Completion.coe' (α := InductiveTensor (SchwartzBruhat (G i))
      (SchwartzBruhat ((j : J) → G j.val))) ((f i) ⊗ₜ[ℂ] g))
    refine ⟨⟨q.val ∘ e, schwartzBruhat_pullback_mem e q⟩, fun x ↦ ?_⟩
    change q (x i, fun j ↦ x j.val) = _
    rw [show q (x i, fun j ↦ x j.val) = _ from ht (f i) g _ _, hg, Fintype.prod_eq_mul_prod_compl i]
    exact congrArg (_ * ·) (Finset.prod_subtype _ (fun j ↦ by simp) (fun j ↦ f j (x j))).symm
termination_by Fintype.card ι
decreasing_by
  classical
  exact Fintype.card_subtype_lt (x := i) (not_not_intro rfl)

/-- Assemble the archimedean product in the test space of the infinite adeles. -/
private theorem sLocalIdelicZFunction_principalValue_archTest
    (a : (w : InfinitePlace F) → ℬ(w.Completion)) :
    ∃ arch : ℬ(A∞), ∀ x : A∞, arch (Multiplicative.ofAdd x) =
      ∏ w : InfinitePlace F, a w (Multiplicative.ofAdd (x w)) := by
  let G (w : InfinitePlace F) := Multiplicative w.Completion
  let (w : InfinitePlace F) : T2Space (G w) := (inferInstance : T2Space w.Completion)
  let (w : InfinitePlace F) : LocallyCompactSpace (G w) := (inferInstance : LocallyCompactSpace w.Completion)
  let (w : InfinitePlace F) : SecondCountableTopology (G w) :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  obtain ⟨a₀, ha⟩ := sLocalIdelicZFunction_principalValue_productTest G a
  let e : Multiplicative (InfiniteAdeleRing F) ≃ₜ* ((w : InfinitePlace F) → G w) :=
    { toFun := fun x w ↦ Multiplicative.ofAdd (x.toAdd w)
      invFun := fun x ↦ Multiplicative.ofAdd (fun w ↦ (x w).toAdd)
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl
      continuous_toFun := continuous_id
      continuous_invFun := continuous_id }
  exact ⟨⟨a₀.val ∘ e, schwartzBruhat_pullback_mem e a₀⟩, fun x ↦ ha (e (Multiplicative.ofAdd x))⟩

/-- Tate's product formula and the tensor action of principal value give the identity on pure tests. -/
private theorem sLocalIdelicZFunction_principalValue_pure (T : Finset V) (hT : T ⊆ S)
    (χ : PontryaginDual Jₛ) (z : ℂ) (hz : 0 < z.re) (f : ℬₛ)
    (a : (w : InfinitePlace F) → ℬ(w.Completion)) (b : (v : S) → ℬ(v.val.adicCompletion F))
    (hf : ∀ x : Aₛ, f (Multiplicative.ofAdd x) =
      (∏ w : InfinitePlace F, a w (Multiplicative.ofAdd (x.1 w))) *
        ∏ v : S, b v (Multiplicative.ofAdd (x.2 v))) :
    let c := chartₛ(χ) z
    sLocalIdelicZetaIntegral (sAdelePrincipalValue F hT f) c = sLocalIdelicZetaIntegral f c /
      ∏ v : S, if v.val ∈ T then finiteLocalEulerFactor v.val (sLocalFiniteRestriction v c) else 1 := by
  classical
  intro c
  let (v : S) : MeasurableSpace (v.val.adicCompletion F)ˣ := borel _
  obtain ⟨a₀, ha⟩ := sLocalIdelicZFunction_principalValue_archTest a
  let e := (sAdeleSchwartz_inductiveTensor_equiv F S).choose
  let b' (v : S) := if v.val ∈ T then finitePlacePrincipalValue v.val (b v) else b v
  have hpack : f = e (a₀ ⊗ₜ[ℂ] (⨂ₜ[ℂ] v, b v)) := by
    apply Subtype.ext
    funext x
    exact (hf x.toAdd).trans (((sAdeleSchwartz_inductiveTensor_equiv F S).choose_spec a₀ b x.toAdd).trans
      (congrArg (· * _) (ha x.toAdd.1))).symm
  have hpv (x : Aₛ) : sAdelePrincipalValue F hT f (Multiplicative.ofAdd x) =
      (∏ w : InfinitePlace F, a w (Multiplicative.ofAdd (x.1 w))) *
        ∏ v : S, b' v (Multiplicative.ofAdd (x.2 v)) := by
    rw [hpack, sAdelePrincipalValue_tmul hT a₀ b]
    exact ((sAdeleSchwartz_inductiveTensor_equiv F S).choose_spec a₀ b' x).trans
      (congrArg (· * _) (ha x.1))
  rw [sLocalIdelicZetaIntegral_pureTensor c ⟨χ, z, hz, rfl⟩ _ a b' hpv,
    sLocalIdelicZetaIntegral_pureTensor c ⟨χ, z, hz, rfl⟩ f a b hf, mul_div_assoc]
  apply congrArg (_ * ·)
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro v _
  by_cases hv : v.val ∈ T
  · simp only [b', hv, ite_true]
    exact sLocalIdelicZFunction_principalValue_finite v (b v) χ z hz
  · simp only [b', hv, ite_false, div_one]

/-- The reciprocal of a finite Euler factor is entire along a norm chart. -/
private theorem sLocalIdelicZFunction_principalValue_analytic (χ : PontryaginDual Jₛ) (v : S) (t : ℂ) :
    AnalyticAt ℂ (fun z ↦ (finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (chartₛ(χ) z)))⁻¹) t := by
  obtain ⟨η, hη⟩ := sLocalIdelicZFunction_principalValue_chart χ v
  let K := v.val.adicCompletion F
  let O := v.val.adicCompletionIntegers F
  let c := quasiCharacterNormTwist _ (continuous_finiteLocalModule v.val) ((circleToComplex).comp η)
  have hu (u : Oˣ) (z : ℂ) : c z (Units.map O.subtype.toMonoidHom u) =
      (η (Units.map O.subtype.toMonoidHom u) : ℂ) := by
    let g := Units.map O.subtype.toMonoidHom u
    have hmem : g ∈ O.units := ⟨u.val.property, u.inv.property⟩
    have hnorm := Valued.toNormedField.norm_eq_one_iff.mpr
      (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp hmem)
    change (η g : ℂ) * (‖g.val‖ : ℂ) ^ z = (η g : ℂ)
    simp [hnorm]
  let hp := (Valued.v : Valuation K (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
  let π : Kˣ := Units.mk0 (hp.choose : K) hp.choose_spec.ne_zero
  have hc (z : ℂ) : (finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (chartₛ(χ) z)))⁻¹ =
      if ∀ u : Oˣ, (η (Units.map O.subtype.toMonoidHom u) : ℂ) = 1 then 1 - c z π else 1 := by
    rw [hη]
    change (finiteLocalEulerFactor v.val (c z))⁻¹ = _
    have H : (∀ u : Oˣ, c z (Units.map O.subtype.toMonoidHom u) = 1) ↔
        ∀ u : Oˣ, (η (Units.map O.subtype.toMonoidHom u) : ℂ) = 1 :=
      forall_congr' fun u ↦ by rw [hu u z]
    rw [finiteLocalEulerFactor, H]
    split_ifs <;> simp only [inv_inv, inv_one]
    rfl
  simp_rw [hc]
  split_ifs
  · have hn : (‖π.val‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr π.ne_zero)
    exact analyticAt_const.sub (analyticAt_const.mul ((differentiable_id.const_cpow (Or.inl hn)).analyticAt t))
  · exact analyticAt_const

/-- Equality on the positive half-plane continues to equality away from a discrete set. -/
private theorem sLocalIdelicZFunction_principalValue_continue {f g : ℂ → ℂ}
    (hf : MeromorphicOn f univ) (hg : MeromorphicOn g univ) (h : ∀ z : ℂ, 0 < z.re → f z = g z) :
    f =ᶠ[codiscrete ℂ] g := by
  have ho : meromorphicOrderAt (f - g) (1 : ℂ) = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    have hn : ∀ᶠ z : ℂ in 𝓝 (1 : ℂ), 0 < z.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    exact (hn.filter_mono nhdsWithin_le_nhds).mono fun z hz ↦ sub_eq_zero.mpr (h z hz)
  apply eventuallyEq_codiscrete_iff_forall_eventuallyEq_nhdsNE.mpr
  intro z
  have hz := (hf.sub hg).meromorphicOrderAt_eq_top_of_isPreconnected isPreconnected_univ
    (mem_univ (1 : ℂ)) (mem_univ z) ho
  exact (meromorphicOrderAt_eq_top_iff.mp hz).mono fun _ he ↦ sub_eq_zero.mp he

/-- Paper: Proposition 5.3.4.5(1), p. 264.
Applying the principal value at selected finite places divides the zeta function
by their Euler factors as a meromorphic identity. -/
theorem sLocalIdelicZFunction_principalValue (T : Finset V) (hT : T ⊆ S)
    (f : ℬₛ) (χ : PontryaginDual Jₛ) :
    ∀ᶠ s : ℂ in codiscrete ℂ,
      let c := chartₛ(χ) s
      sLocalIdelicZFunction (sAdelePrincipalValue F hT f) c =
        sLocalIdelicZFunction f c /
          ∏ v : S, if v.val ∈ T then finiteLocalEulerFactor v.val (sLocalFiniteRestriction v c)
            else 1 := by
  classical
  let d (z : ℂ) := ∏ v : S, if v.val ∈ T then
    (finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (chartₛ(χ) z)))⁻¹ else 1
  have hd (z : ℂ) : d z = (∏ v : S, if v.val ∈ T then
      finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (chartₛ(χ) z)) else 1)⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    apply Finset.prod_congr rfl
    intro v _
    split_ifs <;> simp only [inv_one]
  have ha (z : ℂ) : AnalyticAt ℂ d z := by
    dsimp only [d]
    apply Finset.analyticAt_fun_prod
    intro v _
    by_cases h : v.val ∈ T
    · simpa only [h, ite_true] using sLocalIdelicZFunction_principalValue_analytic χ v z
    · simp only [h, ite_false]
      exact analyticAt_const
  let P : ℬₛ →L[ℂ] ℬₛ := ⟨sAdelePrincipalValue F hT, (sAdelePrincipalValue_isClosedEmbedding hT).continuous⟩
  have hright (z : ℂ) (hz : 0 < z.re) : sLocalIdelicZetaIntegral (P f) (chartₛ(χ) z) =
      sLocalIdelicZetaIntegral f (chartₛ(χ) z) * d z := by
    let c := chartₛ(χ) z
    obtain ⟨L, hL⟩ := sLocalIdelicZetaIntegral_tempered c ⟨χ, z, hz, rfl⟩
    let Λ := L.comp P - d z • L + L
    have he := sLocalIdelicZetaIntegral_eq_of_pureTensor c ⟨χ, z, hz, rfl⟩ Λ (fun g a b hg ↦ by
      change L (P g) - d z * L g + L g = _
      have hpure : sLocalIdelicZetaIntegral (P g) c = sLocalIdelicZetaIntegral g c * d z := by
        rw [hd, ← div_eq_mul_inv]
        exact sLocalIdelicZFunction_principalValue_pure T hT χ z hz g a b hg
      rw [hL, hL, hpure]
      ring) f
    change L (P f) - d z * L f + L f = _ at he
    rw [← hL f] at he
    rw [← hL, ← hL]
    linear_combination he
  have hmer := sLocalIdelicZFunction_principalValue_continue
    (sLocalIdelicZFunction_meromorphic (P f) χ).meromorphicOn
    ((sLocalIdelicZFunction_meromorphic f χ).meromorphicOn.mul (fun z _ ↦ (ha z).meromorphicAt))
    (fun z hz ↦ (sLocalIdelicZFunction_eq_integral (P f) ⟨χ, z, hz, rfl⟩).trans
      ((hright z hz).trans (congrArg (· * d z) (sLocalIdelicZFunction_eq_integral f ⟨χ, z, hz, rfl⟩).symm)))
  filter_upwards [hmer] with z hz
  change sLocalIdelicZFunction (P f) (chartₛ(χ) z) = sLocalIdelicZFunction f (chartₛ(χ) z) * d z at hz
  exact hz.trans (by rw [div_eq_mul_inv, hd])

-- TODO(paper-gap): (5.3.4.14) gives the allowed pole multiplicity, which can exceed
-- the actual order. A local gamma factor contributes a positive multiplicity at a pole.

/-- Paper: Proposition 5.3.4.5(2), p. 264.
The archimedean pole bound counts the local Euler factors with a pole on the
given norm-twist line at the given exponent. Each such pole is simple. -/
def sLocalArchimedeanPoleMultiplicity (χ : PontryaginDual Jₛ) (s : ℂ) : ℕ :=
  (Finset.univ.filter (fun w : InfinitePlace F ↦
    meromorphicOrderAt (fun z ↦ infiniteLocalEulerFactor w
      (sLocalInfiniteRestriction w (chartₛ(χ) z))) s < 0)).card

/-- Paper: Proposition 5.3.4.5(2), p. 264.
The pole multiplicity is positive exactly at a pole of some pulled-back
archimedean Euler factor. -/
theorem sLocalArchimedeanPoleMultiplicity_pos_iff (χ : PontryaginDual Jₛ) (s : ℂ) :
    0 < sLocalArchimedeanPoleMultiplicity χ s ↔
      ∃ w : InfinitePlace F, meromorphicOrderAt (fun z ↦ infiniteLocalEulerFactor w
        (sLocalInfiniteRestriction w (chartₛ(χ) z))) s < 0 := by
  rw [sLocalArchimedeanPoleMultiplicity, Finset.card_pos]
  simp [Finset.Nonempty]

/-- The reciprocal Gamma function satisfies the order recursion coming from
`1 / Γ(u) = u / Γ(u + 1)`. -/
private theorem meromorphicOrderAt_inv_Gamma_step (x : ℂ) :
    meromorphicOrderAt (fun u : ℂ ↦ (Complex.Gamma u)⁻¹) x =
      meromorphicOrderAt (id : ℂ → ℂ) x +
        meromorphicOrderAt (fun u : ℂ ↦ (Complex.Gamma u)⁻¹) (x + 1) := by
  have hg : ∀ y, AnalyticAt ℂ (fun u : ℂ ↦ (Complex.Gamma u)⁻¹) y := fun y ↦
    Complex.differentiable_one_div_Gamma.analyticAt y
  have heq : (fun u : ℂ ↦ (Complex.Gamma u)⁻¹) =
      (id : ℂ → ℂ) * ((fun u : ℂ ↦ (Complex.Gamma u)⁻¹) ∘ (· + 1)) := by
    funext u
    exact Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one u
  have hcomp : MeromorphicAt ((fun u : ℂ ↦ (Complex.Gamma u)⁻¹) ∘ (· + 1)) x :=
    ((hg (x + 1)).comp (f := fun u : ℂ ↦ u + 1) (by fun_prop)).meromorphicAt
  calc meromorphicOrderAt (fun u : ℂ ↦ (Complex.Gamma u)⁻¹) x
      = meromorphicOrderAt ((id : ℂ → ℂ) *
          ((fun u : ℂ ↦ (Complex.Gamma u)⁻¹) ∘ (· + 1))) x := by rw [← heq]
    _ = _ := by
      rw [meromorphicOrderAt_mul analyticAt_id.meromorphicAt hcomp,
        meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt]

/-- The reciprocal Gamma function has at most a simple zero at each point. -/
private theorem meromorphicOrderAt_inv_Gamma_le_one (x : ℂ) :
    meromorphicOrderAt (fun u : ℂ ↦ (Complex.Gamma u)⁻¹) x ≤ 1 := by
  have hg : ∀ y, AnalyticAt ℂ (fun u : ℂ ↦ (Complex.Gamma u)⁻¹) y := fun y ↦
    Complex.differentiable_one_div_Gamma.analyticAt y
  have hzero : ∀ {f : ℂ → ℂ} {y : ℂ}, AnalyticAt ℂ f y → f y ≠ 0 →
      meromorphicOrderAt f y = 0 := by
    intro f y hf hy
    rw [hf.meromorphicOrderAt_eq, analyticOrderAt_eq_zero.mpr (Or.inr hy), ENat.map_zero,
      CharP.cast_eq_zero, WithTop.coe_zero]
  by_cases hx : ∃ m : ℕ, x = -(m : ℂ)
  · obtain ⟨m, rfl⟩ := hx
    refine le_of_eq ?_
    induction m with
    | zero =>
      rw [meromorphicOrderAt_inv_Gamma_step, Nat.cast_zero, neg_zero, zero_add,
        meromorphicOrderAt_id,
        hzero (hg 1) (by simp [Complex.Gamma_one]), add_zero]
    | succ m ih =>
      rw [meromorphicOrderAt_inv_Gamma_step,
        hzero analyticAt_id (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.add_one_ne_zero m))),
        zero_add, show -((m + 1 : ℕ) : ℂ) + 1 = -(m : ℂ) by push_cast; ring]
      exact ih
  · rw [hzero (hg x) (inv_ne_zero (Complex.Gamma_ne_zero fun m hm ↦ hx ⟨m, hm⟩))]
    exact zero_le_one

/-- Every pole of the Gamma function is simple. -/
private theorem neg_one_le_meromorphicOrderAt_Gamma (x : ℂ) :
    ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt Complex.Gamma x := by
  have h := meromorphicOrderAt_inv_Gamma_le_one x
  have hinv : meromorphicOrderAt (fun u : ℂ ↦ (Complex.Gamma u)⁻¹) x =
      -meromorphicOrderAt Complex.Gamma x := meromorphicOrderAt_inv
  rw [hinv] at h
  cases hn : meromorphicOrderAt Complex.Gamma x with
  | top => exact le_top
  | coe n =>
    rw [hn] at h
    have h1 : -n ≤ 1 := by exact_mod_cast h
    exact_mod_cast (by omega : (-1 : ℤ) ≤ n)

/-- Every pole of the real Gamma factor is simple. -/
private theorem neg_one_le_meromorphicOrderAt_Gammaℝ (x : ℂ) :
    ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt Complex.Gammaℝ x := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have heq : Complex.Gammaℝ = (fun s : ℂ ↦ (Real.pi : ℂ) ^ (-s / 2)) *
      (Complex.Gamma ∘ fun s : ℂ ↦ s / 2) := by
    funext s
    exact Complex.Gammaℝ_def s
  have han : AnalyticAt ℂ (fun s : ℂ ↦ (Real.pi : ℂ) ^ (-s / 2)) x :=
    ((differentiable_id.neg.div_const 2).const_cpow (Or.inl hpi)).analyticAt x
  rw [heq, meromorphicOrderAt_mul_of_ne_zero han (by simp [hpi]),
    meromorphicOrderAt_comp_of_deriv_ne_zero (by fun_prop) (by simp)]
  exact neg_one_le_meromorphicOrderAt_Gamma _

/-- Every pole of the complex Gamma factor is simple. -/
private theorem neg_one_le_meromorphicOrderAt_Gammaℂ (x : ℂ) :
    ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt Complex.Gammaℂ x := by
  have hpi : (2 * Real.pi : ℂ) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have heq : Complex.Gammaℂ = (fun s : ℂ ↦ 2 * (2 * Real.pi : ℂ) ^ (-s)) * Complex.Gamma := by
    funext s
    exact Complex.Gammaℂ_def s
  have han : AnalyticAt ℂ (fun s : ℂ ↦ 2 * (2 * Real.pi : ℂ) ^ (-s)) x :=
    ((differentiable_id.neg.const_cpow (Or.inl hpi)).const_mul 2).analyticAt x
  rw [heq, meromorphicOrderAt_mul_of_ne_zero han (by simp [hpi])]
  exact neg_one_le_meromorphicOrderAt_Gamma _

/-- Along a norm-twist chart, the restriction to an archimedean place is the restriction
at exponent zero times the complex power of the local module. -/
private theorem sLocalInfiniteRestriction_chart_apply (χ : PontryaginDual Jₛ)
    (w : InfinitePlace F) (z : ℂ) (g : w.Completionˣ) :
    sLocalInfiniteRestriction w (chartₛ(χ) z) g =
      sLocalInfiniteRestriction w (chartₛ(χ) 0) g *
        ((((Units.map nnNormHom.toMonoidHom ^ w.mult : w.Completionˣ →* ℝ≥0ˣ) g : ℝ≥0) : ℝ) :
          ℂ) ^ z := by
  obtain ⟨x, hx⟩ : ∃ x : Jₛ, ∀ c : Xₛ, sLocalInfiniteRestriction w c g = c x :=
    ⟨_, fun _ ↦ rfl⟩
  have hN : ((((mₛ) x : ℝ≥0) : ℝ) : ℂ) =
      ((((Units.map nnNormHom.toMonoidHom ^ w.mult : w.Completionˣ →* ℝ≥0ˣ) g : ℝ≥0) : ℝ) :
        ℂ) := by
    have he := sLocalInfiniteRestriction_norm (S := S) w g
    rw [hx] at he
    change ((1 : PontryaginDual Jₛ) x : ℂ) * ((((mₛ) x : ℝ≥0) : ℝ) : ℂ) ^ (1 : ℂ) = _ at he
    simpa only [PontryaginDual.one_apply, Circle.coe_one, one_mul, Complex.cpow_one] using he
  rw [hx, hx, ← hN]
  change (χ x : ℂ) * ((((mₛ) x : ℝ≥0) : ℝ) : ℂ) ^ z =
    ((χ x : ℂ) * ((((mₛ) x : ℝ≥0) : ℝ) : ℂ) ^ (0 : ℂ)) * ((((mₛ) x : ℝ≥0) : ℝ) : ℂ) ^ z
  rw [Complex.cpow_zero, mul_one]

/-- Along a norm-twist chart, the Euler factor at a real place is a translate of the real
Gamma factor. -/
private theorem infiniteLocalEulerFactor_chart_real (χ : PontryaginDual Jₛ)
    (w : InfinitePlace F) (hw : w.IsReal) :
    ∃ b : ℂ, ∀ z : ℂ, infiniteLocalEulerFactor w
      (sLocalInfiniteRestriction w (chartₛ(χ) z)) = Complex.Gammaℝ (z + b) := by
  let e := (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm
  have hp := (realLocalEulerParameters w hw
    (sLocalInfiniteRestriction w (chartₛ(χ) 0))).exists.choose_spec
  obtain ⟨p, hpdef⟩ : ∃ p : ℂ × Fin 2, p = (realLocalEulerParameters w hw
    (sLocalInfiniteRestriction w (chartₛ(χ) 0))).exists.choose := ⟨_, rfl⟩
  rw [← hpdef] at hp
  refine ⟨p.1 + (p.2.val : ℂ), fun z ↦ ?_⟩
  have hshape : ∀ x : ℝˣ, sLocalInfiniteRestriction w (chartₛ(χ) z)
      (Units.map e.toMonoidHom x) =
        (‖(x : ℝ)‖ : ℂ) ^ (z + p.1) * (if 0 < (x : ℝ) then 1 else (-1 : ℂ)) ^ p.2.val := by
    intro x
    have hn : ‖(e (x : ℝ) : w.Completion)‖ = ‖(x : ℝ)‖ :=
      (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.isometry.norm_map_of_map_zero
        (map_zero e) (x : ℝ)
    have hm : (((Units.map nnNormHom.toMonoidHom ^ w.mult : w.Completionˣ →* ℝ≥0ˣ)
        (Units.map e.toMonoidHom x) : ℝ≥0) : ℝ) = ‖(x : ℝ)‖ := by
      simp [InfinitePlace.mult, hw, hn]
    rw [sLocalInfiniteRestriction_chart_apply, hp x, hm,
      Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr x.ne_zero))]
    ring
  have hq := (realLocalEulerParameters w hw (sLocalInfiniteRestriction w (chartₛ(χ) z))).unique
    (realLocalEulerParameters w hw (sLocalInfiniteRestriction w (chartₛ(χ) z))).exists.choose_spec
    (y₂ := (z + p.1, p.2)) hshape
  simp only [infiniteLocalEulerFactor, hw, ↓reduceDIte, hq, add_assoc]

/-- Along a norm-twist chart, the Euler factor at a complex place is half a translate of the
complex Gamma factor. -/
private theorem infiniteLocalEulerFactor_chart_complex (χ : PontryaginDual Jₛ)
    (w : InfinitePlace F) (hw : w.IsComplex) :
    ∃ b : ℂ, ∀ z : ℂ, infiniteLocalEulerFactor w
      (sLocalInfiniteRestriction w (chartₛ(χ) z)) = Complex.Gammaℂ (z + b) / 2 := by
  let e := (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm
  have hp := (complexLocalEulerParameters w hw
    (sLocalInfiniteRestriction w (chartₛ(χ) 0))).exists.choose_spec
  obtain ⟨p, hpdef⟩ : ∃ p : ℂ × ℤ, p = (complexLocalEulerParameters w hw
    (sLocalInfiniteRestriction w (chartₛ(χ) 0))).exists.choose := ⟨_, rfl⟩
  rw [← hpdef] at hp
  refine ⟨p.1 + (p.2.natAbs : ℂ) / 2, fun z ↦ ?_⟩
  have hshape : ∀ x : ℂˣ, sLocalInfiniteRestriction w (chartₛ(χ) z)
      (Units.map e.toMonoidHom x) =
        ((‖(x : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ (z + p.1) * ((x : ℂ) / (‖(x : ℂ)‖ : ℂ)) ^ p.2 := by
    intro x
    have hn : ‖(e (x : ℂ) : w.Completion)‖ = ‖(x : ℂ)‖ :=
      (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
        hw).symm.isometry.norm_map_of_map_zero (map_zero e) (x : ℂ)
    have hm : (((Units.map nnNormHom.toMonoidHom ^ w.mult : w.Completionˣ →* ℝ≥0ˣ)
        (Units.map e.toMonoidHom x) : ℝ≥0) : ℝ) = ‖(x : ℂ)‖ ^ 2 := by
      simp [InfinitePlace.mult, InfinitePlace.not_isReal_iff_isComplex.mpr hw, hn]
    rw [sLocalInfiniteRestriction_chart_apply, hp x, hm,
      Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr
        (pow_ne_zero _ (norm_ne_zero_iff.mpr x.ne_zero)))]
    ring
  have hq := (complexLocalEulerParameters w hw
      (sLocalInfiniteRestriction w (chartₛ(χ) z))).unique
    (complexLocalEulerParameters w hw
      (sLocalInfiniteRestriction w (chartₛ(χ) z))).exists.choose_spec
    (y₂ := (z + p.1, p.2)) hshape
  simp only [infiniteLocalEulerFactor, InfinitePlace.not_isReal_iff_isComplex.mpr hw,
    ↓reduceDIte, hq, add_assoc]

/-- For orders bounded below by minus one, the negative parts sum to minus the number of
negative orders. -/
private theorem neg_card_filter_eq_sum_min {ι : Type*} [Fintype ι] (ord : ι → WithTop ℤ)
    [DecidablePred fun i ↦ ord i < 0] (h : ∀ i, ((-1 : ℤ) : WithTop ℤ) ≤ ord i) :
    ((-((Finset.univ.filter fun i ↦ ord i < 0).card : ℤ) : ℤ) : WithTop ℤ) =
      ∑ i, min 0 (ord i) := by
  have hneg : ∀ i ∈ Finset.univ.filter (fun i ↦ ord i < 0),
      min 0 (ord i) = ((-1 : ℤ) : WithTop ℤ) := by
    intro i hi
    have hi' : ord i < 0 := (Finset.mem_filter.mp hi).2
    rw [min_eq_right hi'.le]
    refine le_antisymm ?_ (h i)
    cases hn : ord i with
    | top =>
      rw [hn] at hi'
      exact absurd hi' not_top_lt
    | coe n =>
      rw [hn] at hi'
      have h0 : n < 0 := by exact_mod_cast hi'
      exact_mod_cast (by omega : n ≤ -1)
  have hpos : ∀ i ∈ Finset.univ.filter (fun i ↦ ¬ ord i < 0), min 0 (ord i) = 0 := fun i hi ↦
    min_eq_left (not_lt.mp (Finset.mem_filter.mp hi).2)
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i ↦ ord i < 0),
    Finset.sum_congr rfl hneg, Finset.sum_eq_zero hpos, add_zero, Finset.sum_const,
    ← WithTop.coe_nsmul]
  congr 1
  simp

/-- Along a norm-twist chart, every pole of an archimedean Euler factor is simple. -/
private theorem neg_one_le_meromorphicOrderAt_infiniteLocalEulerFactor_chart
    (χ : PontryaginDual Jₛ) (w : InfinitePlace F) (s : ℂ) :
    ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (fun z ↦ infiniteLocalEulerFactor w
      (sLocalInfiniteRestriction w (chartₛ(χ) z))) s := by
  by_cases hw : w.IsReal
  · obtain ⟨b, hb⟩ := infiniteLocalEulerFactor_chart_real χ w hw
    have hfun : (fun z ↦ infiniteLocalEulerFactor w
        (sLocalInfiniteRestriction w (chartₛ(χ) z))) = Complex.Gammaℝ ∘ (· + b) := funext hb
    rw [hfun, meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt]
    exact neg_one_le_meromorphicOrderAt_Gammaℝ _
  · obtain ⟨b, hb⟩ := infiniteLocalEulerFactor_chart_complex χ w
      (InfinitePlace.not_isReal_iff_isComplex.mp hw)
    have hfun : (fun z ↦ infiniteLocalEulerFactor w
        (sLocalInfiniteRestriction w (chartₛ(χ) z))) =
        (fun _ : ℂ ↦ (2 : ℂ)⁻¹) * (Complex.Gammaℂ ∘ (· + b)) :=
      funext fun z ↦ (hb z).trans (div_eq_inv_mul _ _)
    rw [hfun, meromorphicOrderAt_mul_of_ne_zero analyticAt_const (inv_ne_zero two_ne_zero),
      meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt]
    exact neg_one_le_meromorphicOrderAt_Gammaℂ _

/-- Paper: Proposition 5.3.4.5(2), p. 264.
The negative of the allowed pole multiplicity is the sum of the negative parts
of the meromorphic orders of the local archimedean Euler factors. -/
theorem sLocalArchimedeanPoleMultiplicity_eq_sum (χ : PontryaginDual Jₛ) (s : ℂ) :
    (↑(-(sLocalArchimedeanPoleMultiplicity χ s : ℤ)) : WithTop ℤ) =
      ∑ w : InfinitePlace F, min 0
        (meromorphicOrderAt (fun z ↦ infiniteLocalEulerFactor w
          (sLocalInfiniteRestriction w (chartₛ(χ) z))) s) := by
  rw [sLocalArchimedeanPoleMultiplicity]
  exact neg_card_filter_eq_sum_min _ fun w ↦
    neg_one_le_meromorphicOrderAt_infiniteLocalEulerFactor_chart χ w s

/-- Paper: Proposition 5.3.4.5(2), p. 264.
After all finite principal values, the zeta pole order is bounded by the total
archimedean Euler pole multiplicity.
Deviation: The assertion gives an upper bound since the input can cancel poles.
The multiplicity counts positive pole orders. -/
theorem sLocalIdelicZFunction_principalValue_pole_bound (f : ℬₛ)
    (χ : PontryaginDual Jₛ) (s : ℂ) :
    (↑(-(sLocalArchimedeanPoleMultiplicity χ s : ℤ)) : WithTop ℤ) ≤
      meromorphicOrderAt (fun z ↦ sLocalIdelicZFunction
        (sAdelePrincipalValue F (Finset.Subset.refl S) f) (chartₛ(χ) z)) s := by
  classical
  let E (w : InfinitePlace F) (z : ℂ) := infiniteLocalEulerFactor w
    (sLocalInfiniteRestriction w (chartₛ(χ) z))
  let A (z : ℂ) := ∏ w : InfinitePlace F, E w z
  let G (z : ℂ) := sLocalNormalizedZFunction f (chartₛ(χ) z)
  let Z (z : ℂ) := sLocalIdelicZFunction (sAdelePrincipalValue F (Finset.Subset.refl S) f) (chartₛ(χ) z)
  have hw (w : InfinitePlace F) : Meromorphic (E w) ∧
      ∃ d : ℝ, ∀ z : ℂ, d < z.re → E w z ≠ 0 := by
    by_cases hr : w.IsReal
    · obtain ⟨b, hb⟩ := infiniteLocalEulerFactor_chart_real χ w hr
      have hi : (E w)⁻¹ = fun z : ℂ ↦ (Complex.Gammaℝ (z + b))⁻¹ :=
        funext fun z ↦ congrArg Inv.inv (hb z)
      have hd : Differentiable ℂ ((E w)⁻¹) := hi ▸
        (Complex.differentiable_Gammaℝ_inv.comp (show Differentiable ℂ (fun z : ℂ ↦ z + b) by fun_prop))
      refine ⟨fun z ↦ by simpa only [inv_inv] using (hd.analyticAt z).meromorphicAt.inv, -b.re, ?_⟩
      intro z hz
      rw [show E w z = _ from hb z]
      exact Complex.Gammaℝ_ne_zero_of_re_pos (by simpa only [Complex.add_re] using
        (show 0 < z.re + b.re by linarith))
    · obtain ⟨b, hb⟩ := infiniteLocalEulerFactor_chart_complex χ w (InfinitePlace.not_isReal_iff_isComplex.mp hr)
      have hi : (E w)⁻¹ = fun z : ℂ ↦ 2 * (Complex.Gammaℂ (z + b))⁻¹ := by
        funext z
        rw [Pi.inv_apply, show E w z = _ from hb z, inv_div, div_eq_mul_inv]
      have hd : Differentiable ℂ ((E w)⁻¹) := by
        rw [hi]
        exact (Complex.differentiable_Gammaℂ_inv.comp
          (show Differentiable ℂ (fun z : ℂ ↦ z + b) by fun_prop)).const_mul 2
      refine ⟨fun z ↦ by simpa only [inv_inv] using (hd.analyticAt z).meromorphicAt.inv, -b.re, ?_⟩
      intro z hz
      rw [show E w z = _ from hb z]
      apply div_ne_zero _ two_ne_zero
      rw [Complex.Gammaℂ_def]
      have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
      exact mul_ne_zero (mul_ne_zero two_ne_zero (fun h ↦ hpi ((Complex.cpow_eq_zero_iff _ _).mp h).1))
        (Complex.Gamma_ne_zero_of_re_pos (by simp only [Complex.add_re]; linarith))
  choose d hd using fun w ↦ (hw w).2
  let R := ∑ w : InfinitePlace F, |d w|
  have hR : 0 ≤ R := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  have hA : Meromorphic A := fun z ↦ MeromorphicAt.fun_prod fun w _ ↦ (hw w).1 z
  have hG : ∀ z, AnalyticAt ℂ G z := fun z ↦ (sLocalNormalizedZFunction_entire f χ) z (mem_univ z)
  have hZ : Meromorphic Z := fun z ↦ (sLocalIdelicZFunction_meromorphic _ χ).meromorphicOn z (mem_univ z)
  have hloc : Z =ᶠ[𝓝[≠] ((R + 1 : ℝ) : ℂ)] G * A := by
    have hs' : ∀ᶠ z : ℂ in 𝓝[≠] ((R + 1 : ℝ) : ℂ), R < z.re := nhdsWithin_le_nhds
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp))
    filter_upwards [hs', nhdsNE_le_codiscrete _ (sLocalIdelicZFunction_principalValue S (Finset.Subset.refl S) f χ)]
      with z hz hpv
    have ha : A z ≠ 0 := Finset.prod_ne_zero_iff.mpr fun w _ ↦ hd w z <|
      ((le_abs_self _).trans (Finset.single_le_sum (fun v _ ↦ abs_nonneg (d v)) (Finset.mem_univ w))).trans_lt hz
    have hpos := hR.trans_lt hz
    change sLocalIdelicZFunction _ _ = sLocalNormalizedZFunction f _ * A z
    rw [hpv, sLocalNormalizedZFunction_eq_div f χ hpos, ← sLocalIdelicZFunction_eq_integral f ⟨χ, z, hpos, rfl⟩]
    have hmem (v : S) : v.val ∈ S := v.property
    simp only [hmem, ite_true, sLocalHeckeL]
    change _ / _ = _ / (A z * _) * A z
    simp only [div_eq_mul_inv, mul_inv]
    field_simp [ha]
  have hdiff : Meromorphic (Z - G * A) := fun z ↦ (hZ z).sub ((hG z).meromorphicAt.mul (hA z))
  have hall := hdiff.exists_meromorphicOrderAt_eq_top_iff_eventually_zero.mp
    ⟨_, meromorphicOrderAt_eq_top_iff.mpr (hloc.mono fun _ hz ↦ sub_eq_zero.mpr hz)⟩
  have he : Z =ᶠ[𝓝[≠] s] G * A := nhdsNE_le_codiscrete s
    (hall.mono fun _ hz ↦ sub_eq_zero.mp hz)
  change _ ≤ meromorphicOrderAt Z s
  rw [sLocalArchimedeanPoleMultiplicity_eq_sum, meromorphicOrderAt_congr he,
    meromorphicOrderAt_mul (hG s).meromorphicAt (hA s)]
  apply le_trans _ (le_add_of_nonneg_left (hG s).meromorphicOrderAt_nonneg)
  change _ ≤ meromorphicOrderAt (fun z ↦ ∏ w : InfinitePlace F, E w z) s
  rw [meromorphicOrderAt_fun_prod fun w _ ↦ (hw w).1 s]
  exact Finset.sum_le_sum fun w _ ↦ min_le_right _ _

/-- Extend the inverse unit character by zero as an additive Schwartz–Bruhat test. -/
private theorem exists_sLocalIdelicZFunction_principalValue_attaining_poles_units (v : V)
    (c : QuasiCharacter (v.adicCompletion F)ˣ) :
    let U := (v.adicCompletionIntegers F).units
    ∃ b : ℬ(v.adicCompletion F), b (Multiplicative.ofAdd 0) = 0 ∧ ∀ g : (v.adicCompletion F)ˣ,
      b (Multiplicative.ofAdd g.val) = if g ∈ U then (c g)⁻¹ else 0 := by
  classical
  intro U
  let K := v.adicCompletion F
  have h0 : (0 : K) ∉ Units.val '' (U : Set Kˣ) := fun ⟨g, _, hg⟩ ↦ g.ne_zero hg
  have hmem (g : Kˣ) : g.val ∈ Units.val '' (U : Set Kˣ) ↔ g ∈ U :=
    ⟨fun ⟨u, hu, he⟩ ↦ (Units.ext he : u = g) ▸ hu, fun hg ↦ ⟨g, hg, rfl⟩⟩
  by_cases h : ∀ g ∈ U, c g = 1
  · let hp := (Valued.v : Valuation K (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
    let π : Kˣ := Units.mk0 (hp.choose : K) hp.choose_spec.ne_zero
    refine ⟨finitePlaceDifference v π (finiteStandardGaussian v 1), ?_, fun g ↦ ?_⟩
    · exact (finitePlaceDifference_integerIndicator v π hp.choose_spec 0).trans (indicator_of_notMem h0 _)
    · rw [finitePlaceDifference_integerIndicator v π hp.choose_spec]
      by_cases hg : g ∈ U
      · rw [indicator_of_mem ((hmem g).mpr hg), ite_eq_left hg, h g hg, inv_one]
      · rw [indicator_of_notMem (mt (hmem g).mp hg), ite_eq_right hg]
  · refine ⟨finiteStandardGaussian v c, ?_, fun g ↦ ?_⟩
    · change finiteStandardGaussianValue v c 0 = 0
      rw [finiteStandardGaussianValue, ite_eq_right h, indicator_of_notMem h0]
    · by_cases hg : g ∈ U
      · exact (finiteStandardGaussian_integerUnit v c g hg).trans (ite_eq_left hg).symm
      · rw [ite_eq_right hg]
        change finiteStandardGaussianValue v c g.val = 0
        rw [finiteStandardGaussianValue, ite_eq_right h, indicator_of_notMem (mt (hmem g).mp hg)]

/-- A preimage of the inverse unit character contributes the positive unit mass at every exponent. -/
private theorem exists_sLocalIdelicZFunction_principalValue_attaining_poles_finite
    (χ : PontryaginDual Jₛ) (v : S) :
    letI : MeasurableSpace (v.val.adicCompletion F)ˣ := borel _
    let μ := finiteLocalMultiplicativeTamagawaMeasure F v.val
    let U := (v.val.adicCompletionIntegers F).units
    ∃ b : ℬ(v.val.adicCompletion F), (μ.real U : ℂ) ≠ 0 ∧ ∀ z : ℂ,
      localIdelicZetaIntegral μ (fun x ↦ finitePlacePrincipalValue v.val b (Multiplicative.ofAdd x))
        (sLocalFiniteRestriction v (chartₛ(χ) z)) = μ.real U := by
  classical
  let : MeasurableSpace (v.val.adicCompletion F)ˣ := borel _
  intro μ U
  let : BorelSpace (v.val.adicCompletion F)ˣ := ⟨rfl⟩
  obtain ⟨η, hη⟩ := sLocalIdelicZFunction_principalValue_chart χ v
  let c₀ := (circleToComplex).comp η
  obtain ⟨b₀, h0, hb₀⟩ := exists_sLocalIdelicZFunction_principalValue_attaining_poles_units v.val c₀
  obtain ⟨b, hb⟩ : b₀ ∈ Set.range (finitePlacePrincipalValue v.val) := by
    rw [finitePlacePrincipalValue_range]
    exact h0
  refine ⟨b, Complex.ofReal_ne_zero.mpr
    (finitePlacePrincipalValue_integrable v.val 1 b (Multiplicative.ofAdd 0)).1.ne', fun z ↦ ?_⟩
  let hO : IsOpen (U : Set (v.val.adicCompletion F)ˣ) := Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)
  rw [hb, hη]
  let c := quasiCharacterNormTwist _ (continuous_finiteLocalModule v.val) c₀ z
  have hh (g : (v.val.adicCompletion F)ˣ) : b₀ (Multiplicative.ofAdd g.val) * c g =
      (U : Set (v.val.adicCompletion F)ˣ).indicator (fun _ ↦ (1 : ℂ)) g := by
    rw [hb₀]
    by_cases hg : g ∈ U
    · rw [ite_eq_left hg, indicator_of_mem hg]
      have hn := Valued.toNormedField.norm_eq_one_iff.mpr
        (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp hg)
      change (η g : ℂ)⁻¹ * ((η g : ℂ) * (‖g.val‖ : ℂ) ^ z) = 1
      simp [hn, Circle.coe_ne_zero]
    · rw [ite_eq_right hg, indicator_of_notMem hg, zero_mul]
  change (∫ g, b₀ (Multiplicative.ofAdd g.val) * c g ∂μ) = _
  simp_rw [hh]
  rw [integral_indicator_const _ hO.measurableSet, Complex.real_smul, mul_one]

/-- The local standard Gaussian realizes the archimedean Euler factor on the entire positive half-plane. -/
private theorem exists_sLocalIdelicZFunction_principalValue_attaining_poles_arch
    (χ : PontryaginDual Jₛ) (w : InfinitePlace F) :
    letI : MeasurableSpace w.Completion := borel _
    ∃ a : ℬ(w.Completion), ∀ z : ℂ, 0 < z.re →
      localIdelicZetaIntegral (infiniteLocalMultiplicativeTamagawaMeasure F w)
        (fun x ↦ a (Multiplicative.ofAdd x)) (sLocalInfiniteRestriction w (chartₛ(χ) z)) =
        infiniteLocalEulerFactor w (sLocalInfiniteRestriction w (chartₛ(χ) z)) := by
  let : MeasurableSpace w.Completion := borel _
  let h := sLocalInfiniteInsertion_properties (S := S) w
  let i : w.Completionˣ →ₜ* Jₛ :=
    ⟨{ toFun := fun g ↦ QuotientGroup.mk ((ContinuousMulEquiv.prodUnits (InfiniteAdeleRing F)
          ((v : S) → v.val.adicCompletion F)).symm (ContinuousMulEquiv.piUnits.symm
            (@Pi.mulSingle _ _ _ (Classical.decEq _) w g), 1)),
       map_one' := h.1, map_mul' := h.2.1 }, h.2.2⟩
  let η := χ.comp i
  refine ⟨infiniteStandardGaussian w η, fun z hz ↦ ?_⟩
  have hchart : sLocalInfiniteRestriction w (chartₛ(χ) z) =
      quasiCharacterNormTwist _ (continuous_infiniteLocalModule w) ((circleToComplex).comp η) z := by
    ext1 g
    have hn := sLocalInfiniteRestriction_norm w (S := S) g
    change ((1 : PontryaginDual Jₛ) (i g) : ℂ) * (((mₛ (i g) : ℝ≥0) : ℝ) : ℂ) ^ (1 : ℂ) = _ at hn
    simp only [PontryaginDual.one_apply, Circle.coe_one, one_mul, Complex.cpow_one] at hn
    exact congrArg (fun t : ℂ ↦ (χ (i g) : ℂ) * t ^ z) hn
  rw [hchart, ← infiniteLocalIdelicZFunction_eq_integral w _ η hz]
  exact infiniteLocalIdelicZFunction_standardGaussian w η z hz

/-- A function with an entire reciprocal which is nonzero somewhere has meromorphic order at most zero. -/
private theorem exists_sLocalIdelicZFunction_principalValue_attaining_poles_reciprocal (f : ℂ → ℂ)
    (ha : Differentiable ℂ (fun z ↦ (f z)⁻¹)) (u : ℂ) (hu : f u ≠ 0) (s : ℂ) :
    MeromorphicAt f s ∧ meromorphicOrderAt f s ≤ 0 := by
  let g (z : ℂ) := (f z)⁻¹
  have hm : MeromorphicOn g univ := fun z _ ↦ (ha.analyticAt z).meromorphicAt
  have h₀ : meromorphicOrderAt g u = 0 :=
    (ha.analyticAt u).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr (inv_ne_zero hu)
  have hfin := hm.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (mem_univ u) (mem_univ s) (by rw [h₀]; exact WithTop.coe_ne_top)
  have hf : (fun z ↦ (g z)⁻¹) = f := funext fun z ↦ inv_inv _
  refine ⟨hf ▸ (hm s (mem_univ s)).inv, ?_⟩
  rw [← hf]
  change meromorphicOrderAt g⁻¹ s ≤ 0
  rw [meromorphicOrderAt_inv]
  have hn : 0 ≤ meromorphicOrderAt g s := (ha.analyticAt s).meromorphicOrderAt_nonneg
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hfin
  rw [← hk] at hn ⊢
  exact_mod_cast neg_nonpos.mpr (show 0 ≤ k by exact_mod_cast hn)

/-- Shifted real and complex Gamma factors have no zeros. Their orders therefore equal their negative parts. -/
private theorem exists_sLocalIdelicZFunction_principalValue_attaining_poles_order
    (χ : PontryaginDual Jₛ) (w : InfinitePlace F) (s : ℂ) :
    let L := fun z ↦ infiniteLocalEulerFactor w (sLocalInfiniteRestriction w (chartₛ(χ) z))
    MeromorphicAt L s ∧ meromorphicOrderAt L s ≤ 0 := by
  intro L
  by_cases hw : w.IsReal
  · obtain ⟨b, hb⟩ := infiniteLocalEulerFactor_chart_real χ w hw
    have h : L = fun z ↦ Complex.Gammaℝ (z + b) := funext hb
    rw [h]
    apply exists_sLocalIdelicZFunction_principalValue_attaining_poles_reciprocal _
      (Complex.differentiable_Gammaℝ_inv.comp (differentiable_id.add_const b)) (1 - b)
    simp [Complex.Gammaℝ_one]
  · obtain ⟨b, hb⟩ := infiniteLocalEulerFactor_chart_complex χ w
      (InfinitePlace.not_isReal_iff_isComplex.mp hw)
    have h : L = fun z ↦ Complex.Gammaℂ (z + b) / 2 := funext hb
    rw [h]
    refine exists_sLocalIdelicZFunction_principalValue_attaining_poles_reciprocal _ ?_ (1 - b) ?_ s
    · simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
      exact (Complex.differentiable_Gammaℂ_inv.comp (differentiable_id.add_const b)).const_mul 2
    · simp [Complex.Gammaℂ_one, Real.pi_ne_zero]

/-- Paper: Proposition 5.3.4.5(2), p. 264.
On each component a choice of test realizes the full allowed archimedean pole divisor.
Deviation: Attainment is an existence assertion. The input can cancel any allowed pole. -/
theorem exists_sLocalIdelicZFunction_principalValue_attaining_poles (χ : PontryaginDual Jₛ) :
    ∃ f : ℬₛ, ∀ s : ℂ,
      meromorphicOrderAt (fun z ↦ sLocalIdelicZFunction
        (sAdelePrincipalValue F (Finset.Subset.refl S) f) (chartₛ(χ) z)) s =
        (↑(-(sLocalArchimedeanPoleMultiplicity χ s : ℤ)) : WithTop ℤ) := by
  classical
  let (w : InfinitePlace F) : MeasurableSpace w.Completion := borel _
  let (v : S) : MeasurableSpace (v.val.adicCompletion F)ˣ := borel _
  choose a ha using exists_sLocalIdelicZFunction_principalValue_attaining_poles_arch χ
  choose b hmass hb using exists_sLocalIdelicZFunction_principalValue_attaining_poles_finite χ
  obtain ⟨a₀, ha₀⟩ := sLocalIdelicZFunction_principalValue_archTest a
  let e := (sAdeleSchwartz_inductiveTensor_equiv F S).choose
  let f := e (a₀ ⊗ₜ[ℂ] (⨂ₜ[ℂ] v, b v))
  let p := sAdelePrincipalValue F (Finset.Subset.refl S) f
  let b' (v : S) := finitePlacePrincipalValue v.val (b v)
  have hp (x : Aₛ) : p (Multiplicative.ofAdd x) =
      (∏ w : InfinitePlace F, a w (Multiplicative.ofAdd (x.1 w))) *
        ∏ v : S, b' v (Multiplicative.ofAdd (x.2 v)) := by
    have H : p = e (a₀ ⊗ₜ[ℂ] (⨂ₜ[ℂ] v, b' v)) := by
      simpa only [p, f, e, b', Finset.coe_mem, ite_true] using
        sAdelePrincipalValue_tmul (F := F) (Finset.Subset.refl S) a₀ b
    rw [H]
    exact ((sAdeleSchwartz_inductiveTensor_equiv F S).choose_spec a₀ b' x).trans
      (congrArg (· * _) (ha₀ x.1))
  let L (w : InfinitePlace F) (z : ℂ) := infiniteLocalEulerFactor w (sLocalInfiniteRestriction w (chartₛ(χ) z))
  let M := ∏ v : S, (((finiteLocalMultiplicativeTamagawaMeasure F v.val).real
    (v.val.adicCompletionIntegers F).units : ℝ) : ℂ)
  have hM : M ≠ 0 := Finset.prod_ne_zero_iff.mpr fun v _ ↦ hmass v
  have hL (w : InfinitePlace F) (z : ℂ) : MeromorphicAt (L w) z ∧ meromorphicOrderAt (L w) z ≤ 0 :=
    exists_sLocalIdelicZFunction_principalValue_attaining_poles_order χ w z
  have hmer (z : ℂ) : MeromorphicAt (fun t ↦ M * ∏ w, L w t) z :=
    MeromorphicAt.mul analyticAt_const.meromorphicAt (MeromorphicAt.fun_prod fun w _ ↦ (hL w z).1)
  have H := sLocalIdelicZFunction_principalValue_continue (sLocalIdelicZFunction_meromorphic p χ).meromorphicOn
    (fun z _ ↦ hmer z) (fun z hz ↦ by
      rw [sLocalIdelicZFunction_eq_integral p ⟨χ, z, hz, rfl⟩,
        sLocalIdelicZetaIntegral_pureTensor (chartₛ(χ) z) ⟨χ, z, hz, rfl⟩ p a b' hp]
      exact (congrArg₂ (· * ·) (Finset.prod_congr rfl fun w _ ↦ ha w z hz)
        (Finset.prod_congr rfl fun v _ ↦ hb v z)).trans (mul_comm _ _))
  refine ⟨f, fun s ↦ ?_⟩
  have hs := meromorphicOrderAt_congr (H.filter_mono (nhdsNE_le_codiscrete s))
  refine hs.trans ?_
  change meromorphicOrderAt ((fun _ : ℂ ↦ M) * (fun z ↦ ∏ w, L w z)) s = _
  rw [meromorphicOrderAt_mul_of_ne_zero analyticAt_const hM,
    meromorphicOrderAt_fun_prod (fun w _ ↦ (hL w s).1), sLocalArchimedeanPoleMultiplicity_eq_sum]
  exact Finset.sum_congr rfl fun w _ ↦ (min_eq_right (hL w s).2).symm

private theorem continuous_schwartzBruhat_pointEval {G : Type*} [CommGroup G]
    [TopologicalSpace G] (x : G) : Continuous (fun f : SchwartzBruhat G ↦ f x) := by
  classical
  let L : SchwartzBruhat G →ₗ[ℂ] ℂ :=
    (LinearMap.proj x).comp (schwartzBruhatSubmodule G).subtype
  let p := (normSeminorm ℂ ℂ).comp L
  have hstage (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient) :
      Continuous (p ∘ schwartzBruhatStageInclusion a e) := by
    let _ := e.finiteGroup
    let q : Seminorm ℂ (SchwartzBruhatStage e) := elementarySchwartzSeminorm (0, 0, 0, 0)
    have hq : Continuous q := elementarySchwartz_withSeminorms.continuous_seminorm (0, 0, 0, 0)
    change Continuous (p.comp (schwartzBruhatStageInclusion a e))
    refine Seminorm.continuous_of_le hq ?_
    intro f
    change ‖schwartzBruhatStageRealization a e f x‖ ≤ q f
    rw [schwartzBruhatStageRealization_apply]
    split_ifs with hx
    · let y := Multiplicative.toAdd (e.equiv (QuotientGroup.mk ⟨x, hx⟩))
      change (↑‖f y‖₊ : ENNReal).toReal ≤ (elementarySchwartzBound f.val (0, 0, 0, 0)).toReal
      refine ENNReal.toReal_mono (f.property.2 (0, 0, 0, 0)).ne ?_
      rw [elementarySchwartzBound_zero]
      exact le_iSup (fun z ↦ (↑‖f z‖₊ : ENNReal)) y
    · simpa only [norm_zero] using apply_nonneg q f
  exact (norm_withSeminorms ℂ ℂ).continuous_of_continuous_comp L fun _ ↦
    (withGeneratingSeminorms_spec _ Subtype.val).continuous_seminorm ⟨p, hstage⟩

/-- Paper: Proposition 5.3.4.5(3), p. 264.
The subspace cut out by the selected finite zero-coordinate conditions is closed. -/
theorem sAdeleFiniteZeroSchwartz_isClosed (T : Finset V) :
    IsClosed (↑(sAdeleFiniteZeroSchwartz S T) : Set ℬₛ) := by
  let X := {x : SAdeleRing F S // ∃ v : S, v.val ∈ T ∧ x.2 v = 0}
  have h : IsClosed (⋂ x : X, {f : ℬₛ | f (Multiplicative.ofAdd x.val) = 0}) :=
    isClosed_iInter fun x : X ↦
      isClosed_eq (continuous_schwartzBruhat_pointEval (Multiplicative.ofAdd x.val)) continuous_const
  have heq : (⋂ x : X, {f : ℬₛ | f (Multiplicative.ofAdd x.val) = 0}) =
      (↑(sAdeleFiniteZeroSchwartz S T) : Set ℬₛ) :=
    Set.ext fun f ↦ by
      refine Set.mem_iInter.trans ?_
      let K (x : X) : Submodule ℂ ℬₛ :=
        LinearMap.ker ((LinearMap.proj (Multiplicative.ofAdd x.val)).comp
          (schwartzBruhatSubmodule (Multiplicative (SAdeleRing F S))).subtype)
      change (∀ x : X, f ∈ K x) ↔ f ∈ ⨅ x : X, K x
      exact (Submodule.mem_iInf K).symm
  exact (congrArg (fun s : Set ℬₛ ↦ IsClosed s) heq).mp h

local notation "thetaQuotient(" χ ")" => (LinearMap.ker (thetaAt(χ))).mkQ

/-- Paper: Proposition 5.3.4.5(3), p. 264.
The principal value preserves the kernel of each homogeneous theta transform. -/
theorem sAdelePrincipalValue_preserves_homogeneousThetaKernel {T : Finset V} (hT : T ⊆ S)
    (ψ : PontryaginDual J₁) :
    LinearMap.ker (thetaAt(ψ)) ≤
      (LinearMap.ker (thetaAt(ψ))).comap (sAdelePrincipalValue F hT) := by
  let K := LinearMap.ker (thetaAt(ψ))
  let A := (existsUnique_sLocalThetaIsotypicAverage (F := F) (S := S) ψ).exists.choose
  obtain ⟨e, he⟩ := (sLocalThetaIsotypicAverage_equiv (F := F) (S := S) ψ).2
  intro f hf
  have hz : K.mkQ f = 0 := (Submodule.Quotient.mk_eq_zero K).mpr hf
  have hA : A (Submodule.Quotient.mk f) = 0 := (he f).symm.trans
    (congrArg Subtype.val ((congrArg e hz).trans e.map_zero))
  have hcomm := sLocalThetaPrincipalValue_isotypicAverage (F := F) hT ψ (Submodule.Quotient.mk f)
  have hzero : A (Submodule.Quotient.mk (sAdelePrincipalValue F hT f)) = 0 :=
    hcomm.symm.trans ((congrArg (sLocalThetaPrincipalValue F hT) hA).trans (map_zero _))
  apply (Submodule.Quotient.mk_eq_zero K).mp
  apply e.injective
  apply Subtype.ext
  exact ((he _).trans hzero).trans (congrArg Subtype.val e.map_zero).symm

/-- Paper: Proposition 5.3.4.5(3), p. 264.
Weil's operator on homogeneous theta classes is induced by its action on tests. -/
def sLocalHomogeneousThetaPrincipalValue {T : Finset V} (hT : T ⊆ S) (ψ : PontryaginDual J₁) :
    SLocalHomogeneousThetaSpace F S ψ →ₗ[ℂ] SLocalHomogeneousThetaSpace F S ψ :=
  (LinearMap.ker (thetaAt(ψ))).mapQ (LinearMap.ker (thetaAt(ψ))) (sAdelePrincipalValue F hT)
    (sAdelePrincipalValue_preserves_homogeneousThetaKernel hT ψ)

/-- Paper: Proposition 5.3.4.5(3), p. 264.
On a homogeneous theta class the operator sends the representative to its principal value. -/
theorem sLocalHomogeneousThetaPrincipalValue_mk {T : Finset V} (hT : T ⊆ S)
    (ψ : PontryaginDual J₁) (f : ℬₛ) :
    sLocalHomogeneousThetaPrincipalValue hT ψ (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (sAdelePrincipalValue F hT f) := rfl

/-- Paper: Proposition 5.3.4.5(3), p. 264.
The closed embedding of Lemma 5.3.1.5 restricts to the homogeneous theta quotient,
identified with its isotype by §5.2. -/
theorem sLocalHomogeneousThetaPrincipalValue_isClosedEmbedding {T : Finset V} (hT : T ⊆ S)
    (ψ : PontryaginDual J₁) : IsClosedEmbedding (sLocalHomogeneousThetaPrincipalValue hT ψ) :=
  by
  classical
  let K := LinearMap.ker (thetaAt(ψ))
  rcases T.eq_empty_or_nonempty with rfl | hn
  · have conjugate {E G Y : Type _} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
        [AddCommGroup G] [Module ℂ G] [TopologicalSpace G]
        [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
        (e : InductiveTensor E G ≃L[ℂ] Y) (P : G →ₗ[ℂ] G) (hp : ∀ x, P x = x) :
        e.toLinearMap.comp ((TensorProduct.map (LinearMap.id : E →ₗ[ℂ] E) P).comp e.symm.toLinearMap)
          = LinearMap.id := by
      have he : P = LinearMap.id := LinearMap.ext hp
      subst he
      refine LinearMap.ext fun x ↦ ?_
      have h := LinearMap.congr_fun (TensorProduct.map_id (R := ℂ) (M := E) (N := G)) (e.symm x)
      exact (congrArg e h).trans (e.apply_symm_apply x)
    have hP : sAdelePrincipalValue F hT = LinearMap.id := by
      unfold sAdelePrincipalValue
      refine conjugate _ _ fun x ↦ ?_
      simp only [Finset.notMem_empty, ite_false, PiTensorProduct.map_id]
      rfl
    have hU : ⇑(sLocalHomogeneousThetaPrincipalValue hT ψ) = id := by
      funext y
      obtain ⟨f, rfl⟩ := K.mkQ_surjective y
      exact congrArg K.mkQ (LinearMap.congr_fun hP f)
    rw [hU]
    exact IsClosedEmbedding.id
  · obtain ⟨hs, e, he⟩ := sLocalThetaIsotypicAverage_equiv (F := F) (S := S) ψ
    let j := Subtype.val ∘ e
    have hj : IsClosedEmbedding j := hs.isClosedEmbedding_subtypeVal.comp e.toHomeomorph.isClosedEmbedding
    have hcomp : j ∘ sLocalHomogeneousThetaPrincipalValue hT ψ = sLocalThetaPrincipalValue F hT ∘ j := by
      funext y
      obtain ⟨f, rfl⟩ := K.mkQ_surjective y
      exact (he (sAdelePrincipalValue F hT f)).trans
        ((sLocalThetaPrincipalValue_isotypicAverage (F := F) hT ψ (Submodule.Quotient.mk f)).symm.trans
          (congrArg (sLocalThetaPrincipalValue F hT) (he f).symm))
    apply hj.of_comp_iff.mp
    rw [hcomp]
    exact (sLocalThetaPrincipalValue_isClosedEmbedding (F := F) hT hn).comp hj

/-- Paper: Proposition 5.3.4.5(3), p. 264.
The principal value range in the homogeneous theta quotient is the image of tests
vanishing at the finite zero-coordinate hyperplanes. -/
theorem sLocalPrincipalValue_homogeneousTheta_range (χ : PontryaginDual Jₛ) :
    LinearMap.range (sLocalHomogeneousThetaPrincipalValue (Finset.Subset.refl S) χ₁(χ)) =
      (sAdeleFiniteZeroSchwartz S S).map (thetaQuotient(χ₁(χ))) := by
  classical
  let pv := sAdelePrincipalValue F (Finset.Subset.refl S)
  let Z := sAdeleFiniteZeroSchwartz S S
  let e := (sAdeleSchwartz_inductiveTensor_equiv F S).choose
  have ht (f : ℬ(A∞)) (g : ∀ v : S, ℬ(v.val.adicCompletion F)) :
      pv (e (f ⊗ₜ[ℂ] (⨂ₜ[ℂ] v, g v))) =
        e (f ⊗ₜ[ℂ] (⨂ₜ[ℂ] v, finitePlacePrincipalValue v.val (g v))) := by
    simpa [pv, e] using
      sAdelePrincipalValue_tmul (F := F) (Finset.Subset.refl S) f g
  let pack (a : ℬ(A∞)) (b : ∀ v : S, ℬ(v.val.adicCompletion F)) := e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] v, b v))
  let act (b : ∀ v : S, ℬ(v.val.adicCompletion F)) := fun v ↦ finitePlacePrincipalValue v.val (b v)
  let D (T : Finset V) (b : ∀ v : S, ℬ(v.val.adicCompletion F)) :=
    ∀ v : S, v.val ∈ T → b v (Multiplicative.ofAdd 0) = 0
  have rangeSpan {X A B : Type _} [AddCommGroup X] [Module ℂ X] (P : X →ₗ[ℂ] X)
      (w : A → B → X) (l : B → B) (p q : B → Prop)
      (hw : ∀ a b, P (w a b) = w a (l b))
      (hgen : ∀ x, x ∈ Submodule.span ℂ {y | ∃ a b, p b ∧ w a b = y})
      (hm : ∀ b, q (l b)) (hs : ∀ b, q b → ∃ c, l c = b) :
      LinearMap.range P = Submodule.span ℂ {y | ∃ a b, q b ∧ w a b = y} := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      have incl : Submodule.span ℂ {y | ∃ a b, p b ∧ w a b = y} ≤
          (Submodule.span ℂ {y | ∃ a b, q b ∧ w a b = y}).comap P := by
        apply Submodule.span_le.mpr
        rintro _ ⟨a, b, -, rfl⟩
        exact Submodule.subset_span ⟨a, l b, hm b, (hw a b).symm⟩
      exact incl (hgen x)
    · apply Submodule.span_le.mpr
      rintro _ ⟨a, b, hb, rfl⟩
      obtain ⟨c, rfl⟩ := hs b hb
      exact ⟨w a c, hw a c⟩
  have hgen (f : ℬₛ) : f ∈ Submodule.span ℂ {y | ∃ a b, D ∅ b ∧ pack a b = y} := by
    apply (sAdeleFiniteZeroSchwartz_eq_span_tmul (F := F) (S := S) ∅).le
    exact (Submodule.mem_iInf _).2 fun x ↦ by
      obtain ⟨v, hv, -⟩ := x.property
      exact False.elim (Finset.notMem_empty _ hv)
  have hm (b) : D S (act b) := by
    intro v _
    have hmem := Set.mem_range_self (f := finitePlacePrincipalValue v.val) (b v)
    rwa [finitePlacePrincipalValue_range] at hmem
  have hs (b) (hb : D S b) : ∃ c, act c = b := by
    have hmem (v : S) : b v ∈ Set.range (finitePlacePrincipalValue v.val) := by
      rw [finitePlacePrincipalValue_range]
      exact hb v v.property
    choose c hc using hmem
    exact ⟨c, funext hc⟩
  have hr : LinearMap.range pv = Z :=
    (rangeSpan pv pack act (D ∅) (D S) ht hgen hm hs).trans
      (sAdeleFiniteZeroSchwartz_eq_span_tmul (F := F) (S := S) S).symm
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    induction y using Submodule.Quotient.induction_on with
    | _ f => exact ⟨pv f, hr.le ⟨f, rfl⟩, rfl⟩
  · rintro _ ⟨f, hf, rfl⟩
    obtain ⟨g, hg⟩ := hr.ge hf
    exact ⟨Submodule.Quotient.mk g, congrArg (thetaQuotient(χ₁(χ))) hg⟩

/-- Paper: Proposition 5.3.4.5(3), p. 264.
The same homogeneous theta image is obtained by imposing finite zero-coordinate
vanishing only at the unramified places of χ. -/
theorem sLocalPrincipalValue_homogeneousTheta_range_unramified (χ : PontryaginDual Jₛ)
    (T : Finset V) (_hT : T ⊆ S)
    (_hχ : ∀ v : S, v.val ∈ T ↔ ∀ u : (v.val.adicCompletionIntegers F)ˣ,
      sLocalFiniteRestriction v (chartₛ(χ) 0)
        (Units.map (HeightOneSpectrum.adicCompletionIntegers F v.val).subtype.toMonoidHom u) = 1) :
    LinearMap.range (sLocalHomogeneousThetaPrincipalValue (Finset.Subset.refl S) χ₁(χ)) =
      (sAdeleFiniteZeroSchwartz S T).map (thetaQuotient(χ₁(χ))) := by sorry

end SAdele

end RiemannMasullo
