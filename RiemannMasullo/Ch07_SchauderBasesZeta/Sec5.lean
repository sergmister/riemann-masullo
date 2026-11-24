module

public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec4
import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec2
import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec4
import all RiemannMasullo.Ch04_PeriodicSchauderBases.Sec6
import Mathlib.Topology.Algebra.Module.Equiv.Submodule

import all RiemannMasullo.AppA_AlgebraicNT.Sec3

import all RiemannMasullo.Ch03_IdelicZeta.Sec2

import all RiemannMasullo.Ch05_ThetaZSpaces.Sec3a
import all RiemannMasullo.Ch05_ThetaZSpaces.Sec5

import Mathlib.Analysis.Calculus.DSlope
import RiemannMasullo.Ch05_ThetaZSpaces.Sec1
import RiemannMasullo.Ch03_IdelicZeta.Sec4
import RiemannMasullo.Ch03_IdelicZeta.Sec3
import RiemannMasullo.Ch07_SchauderBasesZeta.Sec3a
import RiemannMasullo.Ch06_LocalGlobal.Sec3
import RiemannMasullo.ForMathlib.Topology.Maps.Strict.Module
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.Barrelled
import RiemannMasullo.Ch09_HardySobolev.Sec2

/-! # §7.5 Strong co-primality -/

@[expose] public noncomputable section

open Function IsDedekindDomain NumberField Set Topology
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false

variable {F : Type*} [Field F] [NumberField F]

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "I𝔽" => IdeleGroup (𝓞 F) F
local notation "U" => PontryaginDual (IdeleClassGroup (𝓞 F) F)
local notation "C₁" => (ideleClassNorm F).ker
local notation "ω(" χ ")" => (χ : U).comp
  (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁ →ₜ* C𝔽)
local notation "m𝔽" =>
  (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "P" => adelePolarSubspace F
local notation "K(" ω ")" => LinearMap.ker ((homogeneousAdelicThetaLinearMap F ω).domRestrict P)
local notation "B" => SchwartzBergman (univ : Set ℝ)

local instance instIdeleClassT2Sec5 : T2Space C𝔽 :=
  (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.1

local instance instIdeleClassLocallyCompactSec5 : LocallyCompactSpace C𝔽 :=
  (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.1

local instance instIdeleClassSecondCountableSec5 : SecondCountableTopology C𝔽 :=
  letI : SecondCountableTopology I𝔽 := idele_secondCountable F
  (ideleGroup_quotient.{_, 0} F).2.2.2.2.1.secondCountableTopology

/-- Paper: Equation (7.5.0.2), p. 374.
The pole-free homogeneous theta space is the quotient of zero-moment tests
by the kernel of their homogeneous theta transform.

Kept as an `abbrev` for now (#5398): as a `def` with its own instances it breaks proofs and
statements that use it, see the issue. Do not copy this pattern: a new type synonym with
structure is a `def` with its own instances (`AGENTS.md`). -/
abbrev StrongCoprimalityThetaSpace (ω : PontryaginDual C₁) := ↥P ⧸ K(ω)

/-- Paper: Equation (7.5.0.2), p. 374.
The comparison space is the norm-one isotype of the full exponential-decay space. -/
abbrev StrongCoprimalityDecaySpace (ω : PontryaginDual C₁) :=
  ↥(modulatedDecayIsotype m𝔽 univ (mem_univ (0 : ℝ)) ω)

/-- Closed graph theorem between Fréchet spaces. The proof is the one of the private
`weilTest_continuous_of_isClosed_graph` in `AppB_AnalyticNT/Sec4b.lean`, for the whole space. -/
private theorem exists_strongCoprimalityThetaLinearMap_closedGraph {E Y : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℂ E]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
    [ContinuousSMul ℂ Y]
    (hE : IsFrechetTVS E) (hY : IsFrechetTVS Y)
    (T : E →ₗ[ℂ] Y) (hT : IsClosed (T.graph : Set (E × Y))) : Continuous T := by
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  let : UniformSpace Y := IsTopologicalAddGroup.rightUniformSpace Y
  have : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  have : IsUniformAddGroup Y := isUniformAddGroup_of_addCommGroup
  have : CompleteSpace E := hE.2.2.2
  have : CompleteSpace Y := hY.2.2.2
  have : TopologicalSpace.MetrizableSpace E := hE.2.2.1
  have : TopologicalSpace.MetrizableSpace Y := hY.2.2.1
  let Γ := T.graph
  have : CompleteSpace Γ := completeSpace_coe_iff_isComplete.mpr hT.isComplete
  have : IsUniformAddGroup Γ := Γ.toAddSubgroup.isUniformAddGroup
  have : TopologicalSpace.MetrizableSpace (E × Y) := inferInstance
  have : TopologicalSpace.MetrizableSpace Γ :=
    inferInstanceAs (TopologicalSpace.MetrizableSpace (Γ : Set (E × Y)))
  have : FirstCountableTopology Γ := inferInstance
  have : FirstCountableTopology E := inferInstance
  have : (uniformity E).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  have : BaireSpace E := BaireSpace.of_completelyPseudoMetrizable
  let Pr : Γ →L[ℂ] E := (ContinuousLinearMap.fst ℂ E Y).comp Γ.subtypeL
  have hmem (x : E) : (x, T x) ∈ Γ := (LinearMap.mem_graph_iff _ _).mpr rfl
  have hval (p : Γ) : p.val.2 = T p.val.1 := (LinearMap.mem_graph_iff _ _).mp p.property
  have hinj : Injective Pr := fun p q h ↦ by
    have h1 : p.val.1 = q.val.1 := h
    exact Subtype.ext (Prod.ext h1 (by rw [hval, hval, h1]))
  have hsurj : Surjective Pr := fun x ↦ ⟨⟨(x, T x), hmem x⟩, rfl⟩
  have ho : IsOpenMap Pr := by
    apply isOpenMap_of_not_isMeagre_range Pr
    rw [hsurj.range_eq]
    exact not_isMeagre_of_isOpen isOpen_univ univ_nonempty
  let h : Γ ≃ₜ E :=
    (Equiv.ofBijective Pr ⟨hinj, hsurj⟩).toHomeomorphOfContinuousOpen Pr.continuous ho
  refine (continuous_snd.comp (continuous_subtype_val.comp h.symm.continuous)).congr fun x ↦ ?_
  have h1 : (h.symm x).val.1 = x := h.apply_symm_apply x
  change (h.symm x).val.2 = T x
  rw [hval, h1]

/-- A linear map from a final locally convex topology to a polynormable space is continuous
if its composites with the defining maps are. The proof is the one of the private
`continuous_of_locallyConvexFinalTopology` in `AppC_LCTVS/Sec2b.lean`. -/
private theorem exists_strongCoprimalityThetaLinearMap_final
    {I : Type*} {X : I → Type*} [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]
    [∀ i, TopologicalSpace (X i)] {D G : Type*} [AddCommGroup D] [Module ℂ D]
    [AddCommGroup G] [Module ℂ G] [TopologicalSpace G] [PolynormableSpace ℂ G]
    (j : ∀ i, X i →ₗ[ℂ] D) (g : D →ₗ[ℂ] G) (hg : ∀ i, Continuous (g ∘ j i)) :
    letI := locallyConvexFinalTopology j
    Continuous g := by
  let := locallyConvexFinalTopology j
  have hD : WithSeminorms
      (Subtype.val : {p : Seminorm ℂ D // ∀ i, Continuous (p ∘ j i)} → Seminorm ℂ D) := ⟨rfl⟩
  let := hD.isTopologicalAddGroup
  exact (PolynormableSpace.withSeminorms ℂ G).continuous_of_continuous_comp g fun p ↦
    hD.continuous_seminorm ⟨p.val.comp g, fun i ↦ p.property.comp (hg i)⟩

/-- At a fixed idele class, global theta is continuous in the test function, by the
Banach–Steinhaus theorem on the barrelled Schwartz–Bruhat space applied to the finite partial
sums of point evaluations. The proof is the one of the private `adelicTheta_eval_continuous`
in `Ch05_ThetaZSpaces/Sec1.lean`. -/
private theorem exists_strongCoprimalityThetaLinearMap_thetaEval (c : C𝔽) :
    Continuous (fun f : SchwartzBruhat (Multiplicative (AdeleRing (𝓞 F) F)) ↦ adelicTheta f c) := by
  induction c using QuotientGroup.induction_on with | H g => ?_
  let : BarrelledSpace ℂ (SchwartzBruhat (Multiplicative (AdeleRing (𝓞 F) F))) :=
    (adeleSchwartz_montel (F := F)).2.1
  let : Countable F := Countable.of_moduleFinite (R := ℚ)
  let : Countable Fˣ := Units.val_injective.countable
  let pt (ξ : Fˣ) : Multiplicative (AdeleRing (𝓞 F) F) :=
    Multiplicative.ofAdd (algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) * g.val)
  let ev (ξ : Fˣ) : SchwartzBruhat (Multiplicative (AdeleRing (𝓞 F) F)) →L[ℂ] ℂ :=
    ⟨(LinearMap.proj (pt ξ)).comp (schwartzBruhatSubmodule _).subtype,
      continuous_schwartzBruhat_eval (pt ξ)⟩
  let L (s : Finset Fˣ) : SchwartzBruhat (Multiplicative (AdeleRing (𝓞 F) F)) →L[ℂ] ℂ :=
    ∑ ξ ∈ s, ev ξ
  have hL (s : Finset Fˣ) (f : SchwartzBruhat (Multiplicative (AdeleRing (𝓞 F) F))) :
      L s f = ∑ ξ ∈ s, f (pt ξ) := by
    simp only [L, FunLike.coe_sum, Finset.sum_apply]
    rfl
  have hsum (f : SchwartzBruhat (Multiplicative (AdeleRing (𝓞 F) F))) :
      HasSum (fun ξ ↦ f (pt ξ)) (adelicTheta f (QuotientGroup.mk g)) := by
    rw [adelicTheta_mk]
    refine Summable.hasSum ?_
    have hs := ((adelicAverage_summableUniformlyOn f {(g, 0)} isCompact_singleton).summable
      rfl).of_norm
    simpa only [add_zero, mul_comm g.val] using hs
  have hT : Filter.Tendsto (fun s f ↦ L s f) Filter.atTop
      (𝓝 fun f ↦ adelicTheta f (QuotientGroup.mk g)) :=
    tendsto_pi_nhds.mpr fun f ↦ by
      simp only [hL]
      exact hsum f
  exact (continuousLinearMapOfTendsto L hT).continuous

open MeasureTheory in
/-- On a barrelled space, the integral over a compact space of a family of continuous linear
functionals is continuous if each test vector gives a continuous function of the parameter.
The proof is the one of the private `continuous_integral_of_continuous_eval` in
`Ch05_ThetaZSpaces/Sec1.lean`. -/
private theorem exists_strongCoprimalityThetaLinearMap_integral {E H : Type*} [AddCommGroup E]
    [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousConstSMul ℂ E]
    [BarrelledSpace ℂ E] [TopologicalSpace H] [CompactSpace H] {m : MeasurableSpace H}
    (μ : Measure H) [IsFiniteMeasure μ]
    (Φ : E → H → ℂ) (hlin : ∀ h, IsLinearMap ℂ fun f ↦ Φ f h)
    (hE : ∀ h, Continuous fun f ↦ Φ f h) (hH : ∀ f, Continuous (Φ f))
    (hint : ∀ f, Integrable (Φ f) μ) : Continuous fun f ↦ ∫ h, Φ f h ∂μ := by
  let p (h : H) : Seminorm ℂ E := (normSeminorm ℂ ℂ).comp (IsLinearMap.mk' _ (hlin h))
  have hp (h : H) : Continuous (p h) := continuous_norm.comp (hE h)
  have hpt (f : E) : BddAbove (Set.range fun h ↦ p h f) :=
    (isCompact_range (hH f).norm).bddAbove
  have hbdd : BddAbove (Set.range p) := Seminorm.bddAbove_range_iff.mpr hpt
  have hsup : Continuous (⨆ h, p h : Seminorm ℂ E) :=
    (congrArg Continuous (Seminorm.coe_iSup_eq hbdd)).mpr (Seminorm.continuous_iSup p hp hbdd)
  let I : E →ₗ[ℂ] ℂ := IsLinearMap.mk' (fun f ↦ ∫ h, Φ f h ∂μ)
    ⟨fun f f' ↦ (integral_congr_ae (.of_forall fun h ↦ (hlin h).map_add f f')).trans
        (integral_add (hint f) (hint f')),
      fun c f ↦ (integral_congr_ae (.of_forall fun h ↦ (hlin h).map_smul c f)).trans
        (integral_smul c _)⟩
  have hq : Continuous ((μ Set.univ).toNNReal • ⨆ h, p h : Seminorm ℂ E) :=
    hsup.const_smul _
  refine (norm_withSeminorms ℂ ℂ).continuous_of_continuous_comp I fun _ ↦
    Seminorm.continuous_of_le hq fun f ↦ ?_
  have hle (h : H) : ‖Φ f h‖ ≤ (⨆ h, p h) f := by
    rw [Seminorm.coe_iSup_eq hbdd, iSup_apply]
    exact le_ciSup (hpt f) h
  exact (norm_integral_le_of_norm_le_const (.of_forall hle)).trans_eq
    (mul_comm _ ((μ Set.univ).toNNReal : ℝ))

/-- At a fixed idele class, global homogeneous theta is continuous in the test function. -/
private theorem exists_strongCoprimalityThetaLinearMap_eval (ω : PontryaginDual C₁) (g : C𝔽) :
    Continuous (fun f : SchwartzBruhat (Multiplicative (AdeleRing (𝓞 F) F)) ↦
      homogeneousAdelicTheta ω f g) := by
  let : BarrelledSpace ℂ (SchwartzBruhat (Multiplicative (AdeleRing (𝓞 F) F))) :=
    (adeleSchwartz_montel (F := F)).2.1
  let : MeasurableSpace C𝔽 := borel _
  let : CompactSpace C₁ := (ideleClassGroup_finiteness F).2.1
  let : (normOneIdeleClassTamagawaMeasure F).IsHaarMeasure :=
    (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  have hθ := adelicTheta_isLinear (F := F)
  have hlin (c : C𝔽) : IsLinearMap ℂ fun f : SchwartzBruhat (Multiplicative (AdeleRing (𝓞 F) F)) ↦
      adelicTheta f c :=
    ⟨fun f f' ↦ congrArg (fun φ : C(C𝔽, ℂ) ↦ φ c) (hθ.map_add f f'),
      fun a f ↦ congrArg (fun φ : C(C𝔽, ℂ) ↦ φ c) (hθ.map_smul a f)⟩
  exact exists_strongCoprimalityThetaLinearMap_integral (normOneIdeleClassTamagawaMeasure F)
    (fun f h ↦ adelicTheta f (h.val * g) * (ω h : ℂ))
    (fun h ↦ ⟨fun f f' ↦ (congrArg (· * (ω h : ℂ)) ((hlin _).map_add f f')).trans
        (add_mul _ _ _),
      fun a f ↦ (congrArg (· * (ω h : ℂ)) ((hlin _).map_smul a f)).trans
        (smul_mul_assoc _ _ _)⟩)
    (fun h ↦ (exists_strongCoprimalityThetaLinearMap_thetaEval (h.val * g)).mul continuous_const)
    (fun f ↦ ((adelicTheta f).continuous.comp
      (continuous_subtype_val.mul continuous_const)).mul
        (continuous_subtype_val.comp ω.continuous))
    (fun f ↦ homogeneousAdelicTheta_integrable ω f g)

open MeasureTheory in
/-- The homogeneous theta function of a zero-moment test decays exponentially in both
directions: each real twist is the isotypic average of the corresponding twist of the plain
theta function (Remark 9.2.0.1), up to the volume of the norm-one classes. -/
private theorem exists_strongCoprimalityThetaLinearMap_mem (ω : PontryaginDual C₁) (f : P) :
    (homogeneousAdelicTheta ω f.val : C𝔽 → ℂ) ∈ modulatedExponentialDecaySubmodule m𝔽 univ := by
  let : MeasurableSpace C𝔽 := borel _
  have : BorelSpace C𝔽 := ⟨rfl⟩
  let : CompactSpace C₁ := (ideleClassGroup_finiteness F).2.1
  let μ₁ := normOneIdeleClassTamagawaMeasure F
  let : μ₁.IsHaarMeasure :=
    (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  have hm : IsModulation m𝔽 := ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
  have hθ := adelicTheta_mem_modulatedExponentialDecay_of_polar f.val f.property
  simp only [modulatedExponentialDecaySubmodule, Submodule.mem_iInf, Submodule.mem_comap] at hθ ⊢
  intro a
  let φ : SchwartzBruhat C𝔽 := ⟨_, hθ a⟩
  let Q := schwartzBruhatIsotypicProjector m𝔽 hm μ₁ ω
  let w (x : C𝔽) : ℂ := ((((m𝔽 x).val : ℝ) ^ (a : ℝ) : ℝ) : ℂ)
  have hφ (k : C₁) (x : C𝔽) :
      φ ((k : C𝔽)⁻¹ * x) = w x * adelicTheta f.val ((k : C𝔽)⁻¹ * x) := by
    change w ((k : C𝔽)⁻¹ * x) * _ = _
    have hk : m𝔽 ((k : C𝔽)⁻¹ * x) = m𝔽 x := by
      change ideleClassNorm F ((k : C𝔽)⁻¹ * x) = ideleClassNorm F x
      rw [map_mul, map_inv, MonoidHom.mem_ker.mp k.property, inv_one, one_mul]
    simp only [w, hk]
  have hreal : μ₁.real univ ≠ 0 := measureReal_univ_ne_zero
  have key : modulationWeight m𝔽 a (⇑(homogeneousAdelicTheta ω f.val)) =
      ((μ₁.real univ : ℝ) : ℂ) • ⇑(Q φ) := by
    funext x
    change w x * (∫ k : C₁, adelicTheta f.val (k.val * x) * (ω k : ℂ) ∂μ₁) =
      ((μ₁.real univ : ℝ) : ℂ) * Q φ x
    rw [(schwartzBruhatIsotypicProjector_apply m𝔽 hm μ₁ ω φ x).2, Complex.real_smul,
      ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hreal, Complex.ofReal_one, one_mul]
    calc w x * (∫ k : C₁, adelicTheta f.val (k.val * x) * (ω k : ℂ) ∂μ₁)
        = ∫ k : C₁, w x * (adelicTheta f.val (k.val * x) * (ω k : ℂ)) ∂μ₁ :=
          (integral_const_mul _ _).symm
      _ = ∫ k : C₁, (fun k : C₁ ↦ w x * (adelicTheta f.val (k.val * x) * (ω k : ℂ))) k⁻¹ ∂μ₁ :=
          (integral_inv_eq_self _ μ₁).symm
      _ = ∫ k : C₁, star (ω k : ℂ) * φ ((k : C𝔽)⁻¹ * x) ∂μ₁ := by
          refine integral_congr_ae (.of_forall fun k ↦ ?_)
          simp only [hφ, Subgroup.coe_inv, map_inv, Circle.coe_inv_eq_conj, Complex.star_def]
          ring
  rw [key]
  exact Submodule.smul_mem _ _ (Q φ).property

/-- Paper: Equation (7.5.0.2), p. 374.
The homogeneous theta transform of a zero-moment test is an exponentially decaying function of
the given isotype, continuously in the test. Continuity is with respect to the topology of the
zero-moment test space and that of the isotype. -/
theorem exists_strongCoprimalityThetaLinearMap (ω : PontryaginDual C₁) :
    ∃ T : P →L[ℂ] StrongCoprimalityDecaySpace ω, ∀ (f : P) (g : C𝔽),
      (T f).val.val g = homogeneousAdelicThetaLinearMap F ω f.val g := by
  classical
  have hm : IsModulation m𝔽 := ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
  have hms : Surjective m𝔽 := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.2.2.2.1
  let Y := StrongCoprimalityDecaySpace ω
  have hY : IsFrechetTVS Y := isotype_frechet m𝔽 hm hms ω
  have : PolynormableSpace ℂ Y := hY.2.1
  have : ContinuousSMul ℂ Y := PolynormableSpace.continuousSMul ℂ Y
  have hθlin := homogeneousAdelicTheta_isLinear (F := F) ω
  -- The theta function of a zero-moment test as a vector of the isotype.
  let Vθ (f : P) : Y := ⟨⟨⇑(homogeneousAdelicTheta ω f.val),
    exists_strongCoprimalityThetaLinearMap_mem ω f⟩, by
      apply (mem_modulatedDecayIsotype_iff (m := m𝔽) (ω := ω) _ _ _).mpr
      intro u x
      exact homogeneousAdelicTheta_homogeneous ω f.val u x⟩
  let A : P →ₗ[ℂ] Y :=
    { toFun := Vθ
      map_add' := fun f f' ↦ Subtype.ext (Subtype.ext (funext fun g ↦
        congrArg (fun v : C(C𝔽, ℂ) ↦ v g) (hθlin.map_add f.val f'.val)))
      map_smul' := fun t f ↦ Subtype.ext (Subtype.ext (funext fun g ↦
        congrArg (fun v : C(C𝔽, ℂ) ↦ v g) (hθlin.map_smul t f.val))) }
  -- A continuous projection of all tests onto the zero-moment tests.
  obtain ⟨e₁, he₁⟩ := adelePolarValues_surjective (F := F) (1, 0)
  obtain ⟨e₂, he₂⟩ := adelePolarValues_surjective (F := F) (0, 1)
  let pv := adelePolarValues (F := F)
  let π₀ := LinearMap.id - (LinearMap.fst ℂ ℂ ℂ ∘ₗ pv).smulRight e₁ -
    (LinearMap.snd ℂ ℂ ℂ ∘ₗ pv).smulRight e₂
  have he₁' : pv e₁ = (1, 0) := he₁
  have he₂' : pv e₂ = (0, 1) := he₂
  have hπ₀ (f) : π₀ f ∈ P := by
    change pv (π₀ f) = 0
    simp only [π₀, map_sub, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
      LinearMap.comp_apply, map_smul, he₁', he₂', LinearMap.fst_apply, LinearMap.snd_apply]
    ext <;> simp
  have hπ₀P (f : P) : π₀ f.val = f.val := by
    have hf : pv f.val = 0 := f.property
    simp only [π₀, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
      LinearMap.comp_apply, hf, LinearMap.fst_apply, LinearMap.snd_apply, Prod.fst_zero,
      Prod.snd_zero, zero_smul, sub_zero]
  have hπ₀c : Continuous π₀ := by
    have hpv := adelePolarValues_continuous (F := F)
    exact (continuous_id.sub ((continuous_fst.comp hpv).smul continuous_const)).sub
      ((continuous_snd.comp hpv).smul continuous_const)
  let T₀ : SchwartzBruhat (Multiplicative (AdeleRing (𝓞 F) F)) →ₗ[ℂ] Y :=
    A ∘ₗ (π₀.codRestrict P hπ₀)
  -- Continuity on the strict LF space of all tests, stage by stage, by the closed graph theorem.
  let : MeasurableSpace C𝔽 := borel _
  have : BorelSpace C𝔽 := ⟨rfl⟩
  obtain ⟨-, S, -, hS, -, ht⟩ := (adeleSchwartz_strictLF (F := F)).2
  have hstage (k : ℕ) : Continuous (T₀ ∘ (S k).subtype) := by
    have hE := hS k
    have : IsTopologicalAddGroup (S k) := hE.1
    have : PolynormableSpace ℂ (S k) := hE.2.1
    have : ContinuousSMul ℂ (S k) := PolynormableSpace.continuousSMul ℂ (S k)
    refine exists_strongCoprimalityThetaLinearMap_closedGraph hE hY (T₀ ∘ₗ (S k).subtype) ?_
    have hset : ((T₀ ∘ₗ (S k).subtype).graph : Set (S k × Y)) =
        ⋂ g : C𝔽, {p | p.2.val.val g = (T₀ p.1.val).val.val g} := by
      ext p
      refine ⟨fun h ↦ mem_iInter.mpr fun g ↦ ?_, fun h ↦ ?_⟩
      · exact congrArg (fun y : Y ↦ y.val.val g) ((LinearMap.mem_graph_iff _ p).mp h)
      · exact (LinearMap.mem_graph_iff _ p).mpr (Subtype.ext (Subtype.ext (funext fun g ↦
          mem_iInter.mp h g)))
    rw [hset]
    refine isClosed_iInter fun g ↦ isClosed_eq
      ((isotype_eval_continuous m𝔽 hm hms ω g).comp continuous_snd) ?_
    exact ((exists_strongCoprimalityThetaLinearMap_eval ω g).comp hπ₀c).comp
      (continuous_subtype_val.comp continuous_fst)
  have hT₀ : Continuous T₀ := by
    have hc := exists_strongCoprimalityThetaLinearMap_final (fun k ↦ (S k).subtype) T₀ hstage
    rw [ht]
    exact hc
  have hA (f : P) : T₀ f.val = A f := by
    change A (⟨π₀ f.val, hπ₀ f.val⟩ : P) = A f
    rw [show (⟨π₀ f.val, hπ₀ f.val⟩ : P) = f from Subtype.ext (hπ₀P f)]
  exact ⟨⟨A, (hT₀.comp continuous_subtype_val).congr hA⟩, fun f g ↦ rfl⟩

private theorem exists_strongCoprimalityThetaEmbedding_ker_le (ω : PontryaginDual C₁)
    (T : P →L[ℂ] StrongCoprimalityDecaySpace ω)
    (hT : ∀ (f : P) (g : C𝔽),
      (T f).val.val g = homogeneousAdelicThetaLinearMap F ω f.val g) :
    K(ω) ≤ T.ker := by
  intro f hf
  rw [LinearMap.mem_ker]
  have h0 : (homogeneousAdelicThetaLinearMap F ω) (f : P) = 0 := by
    simpa only [LinearMap.mem_ker, LinearMap.domRestrict_apply] using hf
  refine Subtype.ext (Subtype.ext (funext fun g ↦ ?_))
  have hg : (T f).val.val g = 0 := by
    rw [hT, h0]
    simp
  exact hg.trans (by rfl)

/-- Paper: Equation (7.5.0.2), p. 374.
Two zero-moment tests with the same homogeneous theta function give the same class, so a
map with the theta values separates the classes of the pole-free theta space. -/
private theorem exists_strongCoprimalityThetaEmbedding_injective (ω : PontryaginDual C₁)
    (j : StrongCoprimalityThetaSpace ω →L[ℂ] StrongCoprimalityDecaySpace ω)
    (hj : ∀ (f : P) (g : C𝔽),
      (j ((K(ω)).mkQ f)).val.val g = homogeneousAdelicThetaLinearMap F ω f.val g) :
    Function.Injective j := by
  intro x y hxy
  obtain ⟨f, rfl⟩ := (K(ω)).mkQ_surjective x
  obtain ⟨f', rfl⟩ := (K(ω)).mkQ_surjective y
  have hθ : (homogeneousAdelicThetaLinearMap F ω) (f : P) =
      (homogeneousAdelicThetaLinearMap F ω) (f' : P) := by
    ext g
    rw [← hj f g, ← hj f' g, hxy]
  have hmem : f - f' ∈ (K(ω) : Submodule ℂ P) := by
    rw [LinearMap.mem_ker, LinearMap.domRestrict_apply, Submodule.coe_sub, map_sub, hθ, sub_self]
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  exact hmem

/-- Paper: Equation (7.5.0.2), p. 374.
The homogeneous theta functions of zero-moment tests form a closed subspace of the
exponentially decaying isotype: the range of any continuous linear map that sends the class
of a zero-moment test to its homogeneous theta function is closed.
The group Mellin transform of the isotype sends that range onto the pole-free theta Mellin
image, which is the (unshifted) spectral nuclearity denominator of Equation (7.4.0.1) in the
Schwartz-Bergman model, a closed divisible subspace. -/
private theorem exists_strongCoprimalityThetaEmbedding_isClosed_range (ω : PontryaginDual C₁)
    (j : StrongCoprimalityThetaSpace ω →L[ℂ] StrongCoprimalityDecaySpace ω)
    (hj : ∀ (f : P) (g : C𝔽),
      (j ((K(ω)).mkQ f)).val.val g = homogeneousAdelicThetaLinearMap F ω f.val g) :
    IsClosed (range j) := by
  classical
  have hm : IsModulation m𝔽 := ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
  have hms : Surjective m𝔽 := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.2.2.2.1
  let : MeasurableSpace C𝔽 := borel _
  let : BorelSpace C𝔽 := ⟨rfl⟩
  -- A continuous section of the idele norm and its image in the class group.
  let τI : ℝ≥0ˣ →ₜ* I𝔽 :=
    ⟨canonicalIdeleNormSection F, canonicalIdeleNormSection_continuous F⟩
  have hτI : RightInverse τI (ideleNorm F) := canonicalIdeleNormSection_rightInverse F
  let τ : ℝ≥0ˣ →ₜ* C𝔽 :=
    { toMonoidHom :=
        (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 F) F)).comp τI.toMonoidHom
      continuous_toFun := continuous_quotient_mk'.comp τI.continuous }
  have hτapp (t : ℝ≥0ˣ) : τ t = QuotientGroup.mk (τI t) := rfl
  have hτval (t : ℝ≥0ˣ) : ideleClassNorm F (τ t) = t := by
    rw [hτapp t]
    show ideleNorm F (τI t) = t
    exact hτI t
  have hτm (t : ℝ≥0ˣ) : m𝔽 (τ t) = t := hτval t
  have hτ : RightInverse τ m𝔽 := fun t ↦ hτval t
  have hmem (g : C𝔽) : g / τ (m𝔽 g) ∈ C₁ := by
    rw [MonoidHom.mem_ker, map_div]
    have h1 : ideleClassNorm F (τ (m𝔽 g)) = ideleClassNorm F g := by
      rw [hτval (m𝔽 g)]
      rfl
    rw [h1, div_self']
  -- Extension of `ω` to a character of the class group, trivial on the norm section.
  let χfun : C𝔽 → Circle := fun g ↦ ω ⟨g / τ (m𝔽 g), hmem g⟩
  have hsub1 : (⟨(1 : C𝔽) / τ (m𝔽 1), hmem 1⟩ : C₁) = 1 := by
    apply Subtype.ext
    show (1 : C𝔽) / τ (m𝔽 1) = 1
    rw [map_one, map_one]
    simp
  have hχ1 : χfun 1 = 1 := (congrArg (fun z : C₁ ↦ ω z) hsub1).trans (map_one ω)
  have hsubmul (g h : C𝔽) : (⟨g * h / τ (m𝔽 (g * h)), hmem (g * h)⟩ : C₁) =
      (⟨g / τ (m𝔽 g), hmem g⟩ : C₁) * ⟨h / τ (m𝔽 h), hmem h⟩ := by
    apply Subtype.ext
    show g * h / τ (m𝔽 (g * h)) = (g / τ (m𝔽 g)) * (h / τ (m𝔽 h))
    have hmul : m𝔽 (g * h) = m𝔽 g * m𝔽 h := by
      change ideleClassNorm F (g * h) = ideleClassNorm F g * ideleClassNorm F h
      exact map_mul (ideleClassNorm F) g h
    have hτmul : τ (m𝔽 g * m𝔽 h) = τ (m𝔽 g) * τ (m𝔽 h) := map_mul τ _ _
    rw [hmul, hτmul, div_mul_div_comm]
  have hχmul (g h : C𝔽) : χfun (g * h) = χfun g * χfun h :=
    (congrArg (fun z : C₁ ↦ ω z) (hsubmul g h)).trans (map_mul ω _ _)
  have hχcont : Continuous χfun :=
    ω.continuous.comp (Continuous.subtype_mk (by fun_prop) hmem)
  let χ : PontryaginDual C𝔽 :=
    { toFun := χfun, map_one' := hχ1, map_mul' := hχmul, continuous_toFun := hχcont }
  have hχapp (g : C𝔽) : χ g = ω ⟨g / τ (m𝔽 g), hmem g⟩ := rfl
  have hsubτ (t : ℝ≥0ˣ) : (⟨τ t / τ (m𝔽 (τ t)), hmem (τ t)⟩ : C₁) = 1 := by
    apply Subtype.ext
    show τ t / τ (m𝔽 (τ t)) = 1
    rw [hτm t]
    simp
  have hχτ (t : ℝ≥0ˣ) : χ (τ t) = 1 :=
    (congrArg (fun z : C₁ ↦ ω z) (hsubτ t)).trans (map_one ω)
  have hχk (k : C₁) : ((χ (k : C𝔽) : Circle) : ℂ) = ((ω k : Circle) : ℂ) := by
    have hsub : (⟨(k : C𝔽) / τ (m𝔽 (k : C𝔽)), hmem (k : C𝔽)⟩ : C₁) = k := by
      apply Subtype.ext
      show (k : C𝔽) / τ (m𝔽 (k : C𝔽)) = (k : C𝔽)
      have hk1 : m𝔽 (k : C𝔽) = 1 := k.property
      rw [hk1]
      simp
    show ((ω ⟨(k : C𝔽) / τ (m𝔽 (k : C𝔽)), hmem (k : C𝔽)⟩ : Circle) : ℂ) =
      ((ω k : Circle) : ℂ)
    exact congrArg (fun z : C₁ ↦ ((ω z : Circle) : ℂ)) hsub
  have hωχ : (χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ :
      C₁ →ₜ* C𝔽)) = ω := by
    ext k
    exact hχk k
  -- The pole-free theta Mellin image is closed in the Schwartz-Bergman model.
  let Z := (exists_globalPolarThetaMellin (F := F) χ τI hτI).choose
  have hZ := (exists_globalPolarThetaMellin (F := F) χ τI hτI).choose_spec
  have hZclosed : IsClosed (Z.toLinearMap.range : Set B) := by
    have hD : IsClosed (spectralNuclearityDenominator χ τI hτI 0 : Set B) :=
      schwartzBergmanDivisible_isClosed
        ⟨⟨_, (spectralNuclearityGenerator_differentiable χ τI hτI 0).continuous⟩,
          spectralNuclearityGenerator_differentiable χ τI hτI 0⟩
    rw [spectralNuclearityDenominator_zero] at hD
    simpa [Z] using hD
  -- The group Mellin transform on the ambient decay space.
  let : CompactSpace (m𝔽).toMonoidHom.ker :=
    isCompact_iff_compactSpace.mp (IsModulation.isCompact_ker hm)
  let μ₁ : MeasureTheory.Measure (m𝔽).toMonoidHom.ker :=
    MeasureTheory.Measure.haarMeasure ⊤
  have hμ₁ : μ₁ univ = 1 := MeasureTheory.Measure.haarMeasure_self
  let μ : MeasureTheory.Measure C𝔽 := canonicalModulatedHaar m𝔽 hm
  have hμhaar : μ.IsHaarMeasure :=
    (Classical.choose_spec (existsUnique_canonicalModulatedHaar m𝔽 hm).exists).1
  let : μ.IsHaarMeasure := hμhaar
  have hμ : μ = (μ₁.prod positiveRealHaar).map
      (fun z : (m𝔽).toMonoidHom.ker × ℝ≥0ˣ ↦ z.1.val * τ z.2) :=
    canonicalModulatedHaar_eq_map_prod m𝔽 hm τ hτ μ₁ MeasureTheory.Measure.haarMeasure_self
  obtain ⟨Am, Fm, Tm, em, hAm, hFm, hTm, hem, hTFm⟩ :=
    modulatedMellin_isotypicDiagram (m := m𝔽) (hm := hm) (hms := hms) (I := univ)
      (hOpen := isOpen_univ) (hInt := ordConnected_univ) (hne := univ_nonempty)
      (τ := τ) (hτ := hτ) (μ₁ := μ₁) (μ := μ) (hμ := hμ) (χ := χ) (b := 0)
      (hb := fun t ↦ by rw [zero_mul]; simp [hχτ t])
  -- The compact average of an isotype vector is its section value.
  have hYavg (y : StrongCoprimalityDecaySpace ω) (t : ℝ≥0ˣ) :
      (∫ k : (m𝔽).toMonoidHom.ker, (χ k.val : ℂ) * y.val.val (k.val * τ t) ∂μ₁) =
        y.val.val (τ t) := by
    have hkω (k : (m𝔽).toMonoidHom.ker) :
        (χ k.val : ℂ) = ((ω k : Circle) : ℂ) := by
      have h := congrArg (fun ψ : PontryaginDual C₁ ↦ ((ψ k : Circle) : ℂ)) hωχ
      exact h
    have hv' (k : (m𝔽).toMonoidHom.ker) :
        (χ k.val : ℂ) * y.val.val (k.val * τ t) = y.val.val (τ t) := by
      have he := (mem_modulatedDecayIsotype_iff (m := m𝔽) (ω := ω) univ
        (mem_univ (0 : ℝ)) y.val).mp y.property k⁻¹ (τ t)
      rw [Subgroup.coe_inv, inv_inv, map_inv, Circle.coe_inv] at he
      have hne : ((ω k : Circle) : ℂ) ≠ 0 := by simp
      rw [he, hkω k, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
    rw [MeasureTheory.integral_congr_ae (.of_forall hv'), MeasureTheory.integral_const,
      MeasureTheory.measureReal_def, hμ₁, ENNReal.toReal_one, one_smul]
  -- The two Mellin transforms agree on theta classes.
  have hjF (f : P) : Fm (j ((K(ω)).mkQ f)).val = Z ((K(ω(χ))).mkQ f) := by
    have hval (g : C𝔽) : (j ((K(ω)).mkQ f)).val.val g = homogeneousAdelicTheta ω f.val g := by
      rw [hj f g]
      rfl
    have hZval : ∀ (g : P) (s : ℂ), (Z ((K(ω(χ))).mkQ g)).val s =
        homogeneousThetaMellinIntegral τI (ω(χ)) g.val (ideleClassNormTwist χ s) :=
      fun g s ↦ (hZ g s).1
    refine Subtype.ext (funext fun s => ?_)
    calc (Fm (j ((K(ω)).mkQ f)).val).val s
        = modulatedFourierMellin m𝔽 univ hm μ (j ((K(ω)).mkQ f)).val.val
            (quasiCharacterNormTwist (m𝔽).toMonoidHom (m𝔽).continuous
              ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ) s) :=
          hFm _ s (mem_univ s)
      _ = ∫ t : ℝ≥0ˣ, ((t.val : ℝ) : ℂ) ^ s * (χ (τ t) : ℂ) *
            (j ((K(ω)).mkQ f)).val.val (τ t) ∂positiveRealHaar := by
          rw [(modulatedMellin_split (m := m𝔽) (hm := hm) (hms := hms) (I := univ)
            (hOpen := isOpen_univ) (hInt := ordConnected_univ) (hne := univ_nonempty)
            (τ := τ) (hτ := hτ) (μ₁ := μ₁) (μ := μ) (hμ := hμ) (χ := χ)
            (f := (j ((K(ω)).mkQ f)).val) (s := s) (hs := mem_univ s)).2.2]
          exact MeasureTheory.integral_congr_ae (.of_forall fun t ↦ by
            beta_reduce
            rw [hYavg _ t])
      _ = ∫ t : ℝ≥0ˣ, ((t.val : ℝ) : ℂ) ^ s *
            homogeneousAdelicTheta ω f.val (τ t) ∂positiveRealHaar := by
          refine MeasureTheory.integral_congr_ae (.of_forall fun t ↦ ?_)
          beta_reduce
          simp only [hval (τ t), hχτ t, Circle.coe_one, mul_one]
      _ = (Z ((K(ω(χ))).mkQ f)).val s := by
          rw [hZval f s]
          unfold homogeneousThetaMellinIntegral
          refine MeasureTheory.integral_congr_ae (.of_forall fun t ↦ ?_)
          beta_reduce
          rw [hωχ]
          have htw : (ideleClassNormTwist χ s) (QuotientGroup.mk (τI t)) =
              ((t.val : ℝ) : ℂ) ^ s := by
            rw [show QuotientGroup.mk (τI t) = τ t from rfl]
            change (χ (τ t) : ℂ) * (((ideleClassNorm F (τ t) : ℝ≥0) : ℝ) : ℂ) ^ s =
              (((t.val : ℝ≥0) : ℝ) : ℂ) ^ s
            rw [hχτ t, hτval t]
            simp
          rw [hτapp t, htw, mul_comm]
  -- Injectivity on the isotype.
  have hFker : Fm.ker = Am.ker := by
    refine le_antisymm (fun f hf ↦ ?_) (fun f hf ↦ ?_)
    · rw [LinearMap.mem_ker] at hf
      have h1 : positiveRealFourierMellin univ isOpen_univ ordConnected_univ univ_nonempty
          (em (Am.ker.mkQ f)) = 0 :=
        ((hTFm f).symm.trans (congrArg Tm hf)).trans (map_zero Tm)
      have h2 : em (Am.ker.mkQ f) = 0 :=
        (positiveRealFourierMellin univ isOpen_univ ordConnected_univ univ_nonempty).injective
          (h1.trans (map_zero _).symm)
      have h3 : Am.ker.mkQ f = 0 := em.injective (h2.trans (map_zero em).symm)
      exact (Submodule.Quotient.mk_eq_zero Am.ker).mp h3
    · rw [LinearMap.mem_ker] at hf ⊢
      have h3 : Am.ker.mkQ f = 0 := (Submodule.Quotient.mk_eq_zero Am.ker).mpr hf
      refine Tm.injective ?_
      calc Tm (Fm f) = positiveRealFourierMellin univ isOpen_univ ordConnected_univ
              univ_nonempty (em (Am.ker.mkQ f)) := hTFm f
        _ = positiveRealFourierMellin univ isOpen_univ ordConnected_univ univ_nonempty
              (em 0) := by rw [h3]
        _ = Tm 0 := by simp
  have hAker : ∀ y : StrongCoprimalityDecaySpace ω, y.val ∈ Am.ker → y = 0 := by
    intro y hy
    rw [LinearMap.mem_ker] at hy
    have hyτ (t : ℝ≥0ˣ) : y.val.val (τ t) = 0 := by
      have h1 : (Am y.val).val (Real.log (t.val : ℝ)) = 0 :=
        congrArg (fun z : PositiveRealExponentialDecay univ ↦ z.val (Real.log (t.val : ℝ))) hy
      rw [hAm y.val t] at h1
      exact (hYavg y t).symm.trans h1
    refine Subtype.ext (Subtype.ext (funext fun g ↦ ?_))
    have hg : (⟨g / τ (m𝔽 g), hmem g⟩ : C₁).val * τ (m𝔽 g) = g :=
      div_mul_cancel g (τ (m𝔽 g))
    have he := (mem_modulatedDecayIsotype_iff (m := m𝔽) (ω := ω) univ
      (mem_univ (0 : ℝ)) y.val).mp y.property (⟨g / τ (m𝔽 g), hmem g⟩ : C₁)⁻¹ (τ (m𝔽 g))
    rw [Subgroup.coe_inv, inv_inv] at he
    calc y.val.val g
        = y.val.val ((⟨g / τ (m𝔽 g), hmem g⟩ : C₁).val * τ (m𝔽 g)) := by rw [hg]
      _ = _ := he
      _ = 0 := by rw [hyτ, mul_zero]
  have hrange : (range j : Set (StrongCoprimalityDecaySpace ω)) =
      {y | Fm y.val ∈ (Z.toLinearMap.range : Set B)} := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨f, rfl⟩ := (K(ω)).mkQ_surjective x
      exact ⟨(K(ω(χ))).mkQ f, (hjF f).symm⟩
    · intro hy
      obtain ⟨w, hw⟩ := hy
      obtain ⟨f, rfl⟩ := (K(ω(χ))).mkQ_surjective w
      refine ⟨(K(ω)).mkQ f, ?_⟩
      have hzero : Fm (y - j ((K(ω)).mkQ f)).val = 0 := by
        rw [show (y - j ((K(ω)).mkQ f)).val = y.val - (j ((K(ω)).mkQ f)).val from rfl,
          map_sub]
        exact sub_eq_zero.mpr ((hw.symm).trans (hjF f).symm)
      have hmem0 : (y - j ((K(ω)).mkQ f)).val ∈ Fm.ker := hzero
      rw [hFker] at hmem0
      have hsub : y - j ((K(ω)).mkQ f) = 0 := hAker _ hmem0
      exact (sub_eq_zero.mp hsub).symm
  rw [hrange]
  exact hZclosed.preimage (Fm.continuous.comp continuous_subtype_val)

/-- A space with a closed linear embedding into a Fréchet space is Fréchet. -/
private theorem exists_strongCoprimalityThetaEmbedding_frechet {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    (i : X →L[ℂ] Y) (hi : IsClosedEmbedding i) (hY : IsFrechetTVS Y) : IsFrechetTVS X := by
  obtain ⟨_, _, _, c⟩ := hY
  let : UniformSpace Y := IsTopologicalAddGroup.rightUniformSpace Y
  have : IsUniformAddGroup Y := isUniformAddGroup_of_addCommGroup
  have : CompleteSpace Y := c
  let : UniformSpace X := IsTopologicalAddGroup.rightUniformSpace X
  have : IsUniformAddGroup X := isUniformAddGroup_of_addCommGroup
  have hu := AddMonoidHom.isUniformInducing_of_isInducing
    (f := i.toLinearMap.toAddMonoidHom) hi.isInducing
  exact ⟨inferInstance, hi.eq_induced ▸ PolynormableSpace.induced i.toLinearMap,
    hi.isEmbedding.metrizableSpace, hu.completeSpace hi.isClosed_range.isComplete⟩

/-- An injective continuous linear map with closed range from a quotient of a closed subspace
of a strict LF-space into a Fréchet space is inducing, by the open mapping theorem onto its
range. -/
private theorem exists_strongCoprimalityThetaEmbedding_isInducing_of_isClosed {W Y : Type*}
    [AddCommGroup W] [Module ℂ W] [TopologicalSpace W] [IsTopologicalAddGroup W]
    [ContinuousSMul ℂ W]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
    (hB : IsStrictLFSpace W) (Q : Submodule ℂ W) (hQ : IsClosed (Q : Set W))
    (K : Submodule ℂ Q) (hY : IsFrechetTVS Y)
    (j : Q ⧸ K →L[ℂ] Y) (hinj : Injective j) (hc : IsClosed (range j)) : IsInducing j := by
  obtain ⟨-, S, hmono, hS, hcov, -⟩ := hB
  have hY' := hY
  obtain ⟨_, _, hmetY, -⟩ := hY'
  have : T2Space (Q ⧸ K) := T2Space.of_injective_continuous hinj j.continuous
  let R : Submodule ℂ Y := LinearMap.range (j : Q ⧸ K →ₗ[ℂ] Y)
  have hR : IsClosed (R : Set Y) := by
    rw [LinearMap.coe_range]
    exact hc
  have hRF : IsFrechetTVS R :=
    exists_strongCoprimalityThetaEmbedding_frechet R.subtypeL hR.isClosedEmbedding_subtypeVal hY
  let j' : Q ⧸ K →L[ℂ] R := j.codRestrict R fun x ↦ ⟨x, rfl⟩
  have hsurj : Surjective j' := by
    rintro ⟨y, x, rfl⟩
    exact ⟨x, rfl⟩
  let Xk (k : ℕ) : Submodule ℂ (S k) := Q.comap (S k).subtype
  have hXk (k : ℕ) : IsFrechetTVS (Xk k) := by
    have hcl : IsClosed (Xk k : Set (S k)) := hQ.preimage continuous_subtype_val
    exact exists_strongCoprimalityThetaEmbedding_frechet (Xk k).subtypeL
      hcl.isClosedEmbedding_subtypeVal (hS k)
  let ι (k : ℕ) : Xk k →L[ℂ] Q :=
    ((S k).subtypeL.comp (Xk k).subtypeL).codRestrict Q fun x ↦ x.property
  let u (k : ℕ) : Xk k →L[ℂ] Q ⧸ K := K.mkQL.comp (ι k)
  have hr (k : ℕ) : range (u k) ⊆ range (u (k + 1)) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨⟨⟨x.val.val, hmono (Nat.le_succ k) x.val.property⟩, x.property⟩, rfl⟩
  have hcov' (z : Q ⧸ K) : ∃ k, z ∈ range (u k) := by
    obtain ⟨f, rfl⟩ := K.mkQ_surjective z
    obtain ⟨k, hk⟩ := hcov f.val
    exact ⟨k, ⟨⟨f.val, hk⟩, f.property⟩, rfl⟩
  have hopen : IsOpenMap j' :=
    isOpenMap_of_surjective_toLF (isLFSpace_of_isFrechetTVS hRF) hXk u hr hcov' j' hsurj
  have hinj' : Injective j' := fun x y h ↦ hinj (congrArg Subtype.val h)
  let L := LinearEquiv.ofBijective (j' : Q ⧸ K →ₗ[ℂ] R) ⟨hinj', hsurj⟩
  let H := L.toEquiv.toHomeomorphOfContinuousOpen j'.continuous hopen
  exact IsInducing.subtypeVal.comp H.isInducing

/-- Paper: Equation (7.5.0.2), p. 374.
The homogeneous theta functions of zero-moment tests form a closed subspace of the
exponentially decaying isotype, so the theta transform is a topological embedding.
The paper obtains this from the Mellin model of §7.4, where the theta image is the
closed denominator of the nuclearity quotient. -/
private theorem exists_strongCoprimalityThetaEmbedding_isInducing (ω : PontryaginDual C₁)
    (j : StrongCoprimalityThetaSpace ω →L[ℂ] StrongCoprimalityDecaySpace ω)
    (hj : ∀ (f : P) (g : C𝔽),
      (j ((K(ω)).mkQ f)).val.val g = homogeneousAdelicThetaLinearMap F ω f.val g) :
    IsInducing j := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hsurj, _⟩ := ideleGroup_quotient.{_, 0} F
  have hmod : IsModulation m𝔽 ∧ Surjective m𝔽 :=
    ⟨⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩, hsurj⟩
  exact exists_strongCoprimalityThetaEmbedding_isInducing_of_isClosed
    (adeleSchwartz_strictLF (F := F)).2 P adelePolarSubspace_closed K(ω)
    (isotype_frechet m𝔽 hmod.1 hmod.2 ω) j
    (exists_strongCoprimalityThetaEmbedding_injective ω j hj)
    (exists_strongCoprimalityThetaEmbedding_isClosed_range ω j hj)

/-- Paper: Equation (7.5.0.2), p. 374.
The topological linear embedding takes a zero-moment test class to its homogeneous theta
function, viewed in the corresponding exponentially decaying isotype. -/
theorem exists_strongCoprimalityThetaEmbedding (ω : PontryaginDual C₁) :
    ∃ j : StrongCoprimalityThetaSpace ω →L[ℂ] StrongCoprimalityDecaySpace ω,
      IsEmbedding j ∧ ∀ (f : P) (g : C𝔽),
        (j ((K(ω)).mkQ f)).val.val g = homogeneousAdelicThetaLinearMap F ω f.val g := by
  obtain ⟨T, hT⟩ := exists_strongCoprimalityThetaLinearMap (F := F) ω
  have hker : K(ω) ≤ T.ker :=
    exists_strongCoprimalityThetaEmbedding_ker_le (F := F) ω T hT
  set j : StrongCoprimalityThetaSpace ω →L[ℂ] StrongCoprimalityDecaySpace ω :=
    (K(ω)).liftQL T hker with hj
  have hformula : ∀ (f : P) (g : C𝔽),
      (j ((K(ω)).mkQ f)).val.val g = homogeneousAdelicThetaLinearMap F ω f.val g := by
    intro f g
    rw [hj, Submodule.liftQL_apply, Submodule.mkQ_apply, Submodule.liftQ_apply]
    exact hT f g
  exact ⟨j, ⟨exists_strongCoprimalityThetaEmbedding_isInducing (F := F) ω j hformula,
      exists_strongCoprimalityThetaEmbedding_injective (F := F) ω j hformula⟩, hformula⟩

private theorem strongCoprimalityPrincipalValue_mem_polar_of_line
    {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (W : Submodule ℂ (StrongDual ℂ E)) (b l k : StrongDual ℂ E)
    (hw : W = Submodule.span ℂ {b}) (hl : l ∈ W) (hk : k ∈ W)
    (y x : E) (hy : l y = 1) (hx : l x = 0) : k x = 0 := by
  rw [hw, Submodule.mem_span_singleton] at hl hk
  obtain ⟨a, rfl⟩ := hl
  obtain ⟨c, rfl⟩ := hk
  change a * b y = 1 at hy
  change a * b x = 0 at hx
  change c * b x = 0
  have ha : a ≠ 0 := fun h ↦ by simp [h] at hy
  exact mul_eq_zero_of_right _ ((mul_eq_zero.mp hx).resolve_left ha)

/-- Paper: Theorem 7.5.0.1 and Equation (7.5.0.3), pp. 374–375.
The two zero moments are preserved by the finite principal-value operator. -/
theorem strongCoprimalityPrincipalValue_mem_polar (S : Finset V) (f : P) :
    adelePrincipalValue F S f.val ∈ P := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hn
  · rw [globalThetaPrincipalValue_isotypicAverage_emptyTest (F := F)]
    exact f.property
  let E := SchwartzBruhat (Multiplicative 𝔸[F])
  let pv : E →L[ℂ] E :=
    ⟨adelePrincipalValue F S, (adelePrincipalValue_isClosedEmbedding S).continuous⟩
  let vals : E →L[ℂ] ℂ × ℂ := ⟨adelePolarValues, adelePolarValues_continuous⟩
  obtain ⟨y, hy⟩ := adelePolarValues_surjective (F := F) ((1, 1) : ℂ × ℂ)
  change vals y = (1, 1) at hy
  have hx : vals f.val = 0 := f.property
  have coord (L : ℂ × ℂ →L[ℂ] ℂ) (c : QuasiCharacter C𝔽)
      (hL : L.comp vals ∈ adelicEigendistributions c) (h1 : L (1, 1) = 1) :
      L (vals (pv f.val)) = 0 := by
    let l := L.comp vals
    have hk : l.comp pv ∈ adelicEigendistributions c := by
      intro u t
      have he := congrArg (fun q : GlobalAdelicThetaSpace F ↦ L (globalThetaPolarValues q))
        (globalThetaPrincipalValue_equivariant hn u t)
      exact he.trans (hL u (pv t))
    exact strongCoprimalityPrincipalValue_mem_polar_of_line (adelicEigendistributions c)
      (adelicNormalizedEigendistribution c) l (l.comp pv) (adelicEigendistributions_eq_span c) hL hk y f.val
      ((congrArg L hy).trans h1) ((congrArg L hx).trans (map_zero L))
  apply (mem_adelePolarSubspace _).2
  constructor
  · apply coord (ContinuousLinearMap.fst ℂ ℂ ℂ) 1 _ rfl
    intro u t
    change t (Multiplicative.ofAdd ((↑u⁻¹ : 𝔸[F]) * 0)) = 1 * t (Multiplicative.ofAdd 0)
    rw [mul_zero, one_mul]
  · apply coord (ContinuousLinearMap.snd ℂ ℂ ℂ) (ideleClassNormTwist (1 : U) 1) _ rfl
    intro u t
    change adeleSchwartzFourier (schwartzBruhatUnitTranslate u t) (Multiplicative.ofAdd 0) =
      ((1 : ℂ) * (((ideleNorm F u).val : ℝ) : ℂ) ^ (1 : ℂ)) *
        adeleSchwartzFourier t (Multiplicative.ofAdd 0)
    rw [Complex.cpow_one, one_mul]
    exact adeleSchwartzFourier_zero_unitTranslate u t

/-- Paper: Equation (7.5.0.3), p. 375.
The denominator is the image in homogeneous theta classes of principal values of
zero-moment tests. -/
def strongCoprimalityDenominator (ω : PontryaginDual C₁) (S : Finset V) :
    Submodule ℂ (StrongCoprimalityThetaSpace ω) :=
  Submodule.span ℂ (range fun f : P ↦
    (Submodule.Quotient.mk ⟨adelePrincipalValue F S f.val,
      strongCoprimalityPrincipalValue_mem_polar S f⟩ : StrongCoprimalityThetaSpace ω))

/-- Paper: Equation (7.5.0.3), p. 375.
The global orbital quotient carries the quotient topology of the pole-free theta space.

Kept as an `abbrev` for now (#5398): as a `def` with its own instances it breaks proofs and
statements that use it, see the issue. Do not copy this pattern: a new type synonym with
structure is a `def` with its own instances (`AGENTS.md`). -/
abbrev StrongCoprimalityQuotient (ω : PontryaginDual C₁) (S : Finset V) :=
  StrongCoprimalityThetaSpace ω ⧸ strongCoprimalityDenominator ω S

private theorem mkQ_span_range_eq_zero {E M : Type*} [AddCommGroup E] [AddCommGroup M]
    [Module ℂ E] [Module ℂ M] (L : E →ₗ[ℂ] M) (x : M) :
    (Submodule.span ℂ (Set.range L)).mkQ x = 0 ↔ ∃ y, x = L y := by
  have hle : Submodule.span ℂ (Set.range L) ≤ LinearMap.range L :=
    Submodule.span_le.mpr Set.Subset.rfl
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := hle hx
    exact ⟨y, hy.symm⟩
  · rintro ⟨y, hy⟩
    exact Submodule.subset_span ⟨y, hy.symm⟩

/-- Paper: Equation (7.5.0.3), p. 375.
A theta class represents zero in the quotient exactly when a principal-value test
represents that same theta class. -/
theorem strongCoprimalityQuotient_mk_eq_zero (ω : PontryaginDual C₁) (S : Finset V)
    (f : P) :
    (strongCoprimalityDenominator ω S).mkQ ((K(ω)).mkQ f) = 0 ↔
      ∃ g : P, (K(ω)).mkQ f = (K(ω)).mkQ
        ⟨adelePrincipalValue F S g.val, strongCoprimalityPrincipalValue_mem_polar S g⟩ :=
  by
    let A : P →ₗ[ℂ] P := ((adelePrincipalValue F S).domRestrict P).codRestrict P
      (strongCoprimalityPrincipalValue_mem_polar S)
    exact mkQ_span_range_eq_zero (((K(ω)).mkQ).comp A) ((K(ω)).mkQ f)

/-- Paper: Theorem 7.5.0.1, p. 374.
The class norm used for the comparison is the surjective modulation of §D.2. -/
theorem strongCoprimalityNorm_isModulation_surjective :
    IsModulation (m𝔽 : C𝔽 →ₜ* ℝ≥0ˣ) ∧ Surjective (m𝔽 : C𝔽 →ₜ* ℝ≥0ˣ) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hsurj, _⟩ := ideleGroup_quotient.{_, 0} F
  exact ⟨⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩, hsurj⟩

/-- Paper: Theorem 7.5.0.1, pp. 374–375.
The comparison difference composes the operators that subtract translation by
each selected inverse uniformizer. -/
def strongCoprimalityDifference (S : Finset V)
    (π : (v : V) → (v.adicCompletion F)ˣ) (f : C𝔽 → ℂ) : C𝔽 → ℂ :=
  S.toList.foldr (fun v h g ↦
    h g - h ((IdeleClassGroup.ofAdicCompletion (𝓞 F) F v (π v))⁻¹ * g)) f

/-- Paper: Theorem 7.5.0.1, pp. 374–375.
A single-place difference subtracts the inverse uniformizer translate pointwise. -/
theorem strongCoprimalityDifference_singleton_apply
    (π : (v : V) → (v.adicCompletion F)ˣ) (v : V) (f : C𝔽 → ℂ) (g : C𝔽) :
    strongCoprimalityDifference {v} π f g =
      f g - f ((IdeleClassGroup.ofAdicCompletion (𝓞 F) F v (π v))⁻¹ * g) := by
  simp [strongCoprimalityDifference]

section
variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
/-- Paper: Equation (7.5.0.1), p. 374.
The comparison uses the range of the full-interval difference product of §4.6. -/
def fullDecayDifferenceRange (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m) (hms : Surjective m)
    (ω : PontryaginDual m.toMonoidHom.ker) (gs : List G) :
    Submodule ℂ ↥(modulatedDecayIsotype m univ (mem_univ (0 : ℝ)) ω) :=
  (modulatedIsotypicDifferenceProduct m hm hms ω univ ordConnected_univ
    (mem_univ (0 : ℝ)) gs).toLinearMap.range

/-- Paper: Equation (7.5.0.1), p. 374.
The span of pointwise iterated differences is the range of the continuous product
on the full decay isotype. -/
theorem fullDecayDifferenceRange_eq_span (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m)
    (hms : Surjective m) (ω : PontryaginDual m.toMonoidHom.ker) (gs : List G) :
    let E := ↥(modulatedDecayIsotype m univ (mem_univ (0 : ℝ)) ω)
    fullDecayDifferenceRange m hm hms ω gs = Submodule.span ℂ
      {h : E | ∃ f : E, h.val.val =
        gs.foldr (fun a (u : G → ℂ) x ↦ u x - u (a * x)) f.val.val} := by
  let E := ↥(modulatedDecayIsotype m univ (mem_univ (0 : ℝ)) ω)
  let D (l : List G) := modulatedIsotypicDifferenceProduct m hm hms ω univ
    ordConnected_univ (mem_univ (0 : ℝ)) l
  have eval (f : E) (l : List G) (x : G) : ((D l) f).val.val x =
      l.foldr (fun a (u : G → ℂ) y ↦ u y - u (a * y)) f.val.val x := by
    induction l generalizing x with
    | nil => rfl
    | cons a l ih =>
      exact (modulatedCyclicDifference_apply m a hm hms univ ordConnected_univ univ_nonempty
        ((D l) f).val x).trans (congrArg₂ (· - ·) (ih x) (ih (a * x)))
  apply le_antisymm
  · rintro h ⟨f, rfl⟩
    exact Submodule.subset_span ⟨f, funext (eval f gs)⟩
  · refine Submodule.span_le.mpr ?_
    rintro h ⟨f, hf⟩
    exact ⟨f, Subtype.ext (Subtype.ext ((funext (eval f gs)).trans hf.symm))⟩
end

/-- Paper: Equation (7.5.0.1), p. 374.
The comparison denominator is the submodule generated by differences of
exponentially decaying functions of the same isotype.
Specializing fullDecayDifferenceRange_eq_span to the class norm and the list
of inverse uniformizer classes recovers this formula by List.foldr_map. -/
def strongCoprimalityDifferenceRange (ω : PontryaginDual C₁) (S : Finset V)
    (π : (v : V) → (v.adicCompletion F)ˣ) : Submodule ℂ (StrongCoprimalityDecaySpace ω) :=
  Submodule.span ℂ {h | ∃ f : StrongCoprimalityDecaySpace ω,
    h.val.val = strongCoprimalityDifference S π f.val.val}

private theorem strongCoprimalityDifference_add (S : Finset V)
    (π : (v : V) → (v.adicCompletion F)ˣ) (f g : C𝔽 → ℂ) :
    strongCoprimalityDifference S π (f + g) =
      strongCoprimalityDifference S π f + strongCoprimalityDifference S π g := by
  unfold strongCoprimalityDifference
  induction S.toList with
  | nil => rfl
  | cons v l ih =>
    simp only [List.foldr_cons, ih]
    funext x
    simp only [Pi.add_apply]
    ring

private theorem strongCoprimalityDifference_smul (S : Finset V)
    (π : (v : V) → (v.adicCompletion F)ˣ) (c : ℂ) (f : C𝔽 → ℂ) :
    strongCoprimalityDifference S π (c • f) = c • strongCoprimalityDifference S π f := by
  unfold strongCoprimalityDifference
  induction S.toList with
  | nil => rfl
  | cons v l ih =>
    simp only [List.foldr_cons, ih]
    funext x
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

private theorem strongCoprimalityDifference_zero (S : Finset V)
    (π : (v : V) → (v.adicCompletion F)ˣ) :
    strongCoprimalityDifference S π (0 : C𝔽 → ℂ) = 0 := by
  simpa using strongCoprimalityDifference_smul S π 0 0

private theorem span_image_eq_of_linear {M X : Type*} [AddCommGroup M] [Module ℂ M]
    [AddCommGroup X] [Module ℂ X] (φ : M → X) (D : X → X)
    (hφa : ∀ a b, φ (a + b) = φ a + φ b) (hφs : ∀ (c : ℂ) a, φ (c • a) = c • φ a)
    (hφ0 : φ 0 = 0)
    (hDa : ∀ a b, D (a + b) = D a + D b) (hDs : ∀ (c : ℂ) a, D (c • a) = c • D a)
    (hD0 : D 0 = 0) (h : M) :
    h ∈ Submodule.span ℂ {h | ∃ f : M, φ h = D (φ f)} ↔ ∃ f : M, φ h = D (φ f) := by
  let N : Submodule ℂ M :=
    { carrier := {h | ∃ f : M, φ h = D (φ f)}
      add_mem' := by
        rintro a b ⟨f, hf⟩ ⟨g, hg⟩
        exact ⟨f + g, by rw [hφa, hf, hg, hφa, hDa]⟩
      zero_mem' := ⟨0, by rw [hφ0, hD0]⟩
      smul_mem' := by
        rintro c a ⟨f, hf⟩
        exact ⟨c • f, by rw [hφs, hf, hφs, hDs]⟩ }
  constructor
  · intro hm
    exact (Submodule.span_le.mpr (fun x hx ↦ hx) : _ ≤ N) hm
  · intro hm
    exact Submodule.subset_span hm

/-- Paper: Equation (7.5.0.1), p. 374.
Each element of the comparison denominator is a single iterated difference
of an exponentially decaying function in the given isotype. -/
theorem mem_strongCoprimalityDifferenceRange (ω : PontryaginDual C₁) (S : Finset V)
    (π : (v : V) → (v.adicCompletion F)ˣ) (h : StrongCoprimalityDecaySpace ω) :
    h ∈ strongCoprimalityDifferenceRange ω S π ↔
      ∃ f : StrongCoprimalityDecaySpace ω,
        h.val.val = strongCoprimalityDifference S π f.val.val := by
  exact span_image_eq_of_linear (fun x : StrongCoprimalityDecaySpace ω ↦ x.val.val)
    (strongCoprimalityDifference S π) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) rfl
    (strongCoprimalityDifference_add S π) (strongCoprimalityDifference_smul S π)
    (strongCoprimalityDifference_zero S π) h

/-- The comparison denominator is an expanding difference-product range, whose quotient
is separable, nuclear, and Fréchet. It repeats `strongCoprimalityPrimaryQuotient_decay`, which is
declared after `strongCoprimality` and so is out of its reach. -/
private theorem strongCoprimality_decayQuotient (ω : PontryaginDual C₁) (S : Finset V)
    (π : (v : V) → (v.adicCompletion F)ˣ)
    (hπ : ∀ v ∈ S, Valuation.IsUniformizer
      (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))) (π v).val) :
    let X := StrongCoprimalityDecaySpace ω ⧸ strongCoprimalityDifferenceRange ω S π
    TopologicalSpace.SeparableSpace X ∧ IsNuclearTVS X ∧ IsFrechetTVS X := by
  classical
  have hmod := strongCoprimalityNorm_isModulation_surjective (F := F)
  let a := fun v : V ↦ (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v (π v))⁻¹
  let gs := S.toList.map a
  have hgs : ∀ g ∈ gs, 1 < (m𝔽 g).val := by
    rintro g hg
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hg
    have hu := hπ v (Finset.mem_toList.mp hv)
    change (1 : ℝ≥0) < ((ideleClassNorm F ((IdeleClassGroup.ofAdicCompletion (𝓞 F) F v (π v))⁻¹)).val)
    rw [map_inv, ideleClassNorm_ofAdicCompletion]
    rw [Units.coe_map_inv]
    change (1 : ℝ≥0) < ‖((π v)⁻¹).val‖₊
    apply NNReal.coe_lt_coe.mp
    simp only [NNReal.coe_one, coe_nnNorm, Units.val_inv_eq_inv_val, norm_inv]
    rw [norm_uniformizer_adicCompletion v _ hu, inv_inv]
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have heq : strongCoprimalityDifferenceRange ω S π =
      fullDecayDifferenceRange m𝔽 hmod.1 hmod.2 ω gs := by
    rw [fullDecayDifferenceRange_eq_span]
    unfold strongCoprimalityDifferenceRange
    congr 1
    ext h
    simp only [gs, List.foldr_map, a, strongCoprimalityDifference]
  rw [heq]
  exact modulatedIsotypicDifferenceProduct_quotient m𝔽 hmod.1 hmod.2 ω gs hgs

/-- A topological linear embedding with closed range into a Fréchet space, followed by a
quotient map onto a Fréchet space, is open when every class of the target meets the range. -/
private theorem strongCoprimality_isOpenMap {X Y Q : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    [AddCommGroup Q] [Module ℂ Q] [TopologicalSpace Q]
    (hY : IsFrechetTVS Y) (hQ : IsFrechetTVS Q)
    (j : X →L[ℂ] Y) (hj : IsEmbedding j) (hc : IsClosed (range j))
    (q : Y →L[ℂ] Q) (hq : Surjective q) (hs : ∀ y, ∃ x, q y = q (j x)) :
    IsOpenMap (fun x ↦ q (j x)) := by
  obtain ⟨_, hpolY, hmetY, hcompY⟩ := hY
  obtain ⟨_, hpolQ, hmetQ, hcompQ⟩ := hQ
  have : ContinuousSMul ℂ Y := PolynormableSpace.continuousSMul ℂ Y
  have : ContinuousSMul ℂ Q := PolynormableSpace.continuousSMul ℂ Q
  let : UniformSpace Y := IsTopologicalAddGroup.rightUniformSpace Y
  have : IsUniformAddGroup Y := isUniformAddGroup_of_addCommGroup
  have : CompleteSpace Y := hcompY
  let : UniformSpace Q := IsTopologicalAddGroup.rightUniformSpace Q
  have : IsUniformAddGroup Q := isUniformAddGroup_of_addCommGroup
  have : CompleteSpace Q := hcompQ
  have : (uniformity Q).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  have : BaireSpace Q := BaireSpace.of_completelyPseudoMetrizable
  let R : Submodule ℂ Y := LinearMap.range (j : X →ₗ[ℂ] Y)
  have hR : IsClosed (R : Set Y) := by
    rw [LinearMap.coe_range]
    exact hc
  have : CompleteSpace R := completeSpace_coe_iff_isComplete.mpr hR.isComplete
  have : IsUniformAddGroup R := R.toAddSubgroup.isUniformAddGroup
  have : TopologicalSpace.MetrizableSpace R :=
    inferInstanceAs (TopologicalSpace.MetrizableSpace (R : Set Y))
  let ψ : R →L[ℂ] Q := q.comp R.subtypeL
  have hψ : IsOpenMap ψ := by
    apply isOpenMap_of_not_isMeagre_range
    have hsurj : Surjective ψ := by
      intro z
      obtain ⟨y, rfl⟩ := hq z
      obtain ⟨x, hx⟩ := hs y
      exact ⟨⟨j x, x, rfl⟩, hx.symm⟩
    rw [hsurj.range_eq]
    exact not_isMeagre_of_isOpen isOpen_univ univ_nonempty
  let j' : X → R := fun x ↦ ⟨j x, x, rfl⟩
  have hj' : IsOpenMap j' := by
    intro W hW
    obtain ⟨Z, hZ, rfl⟩ := hj.isInducing.isOpen_iff.mp hW
    have himage : j' '' (j ⁻¹' Z) = Subtype.val ⁻¹' Z := by
      ext ⟨y, x, rfl⟩
      exact ⟨fun ⟨x', hx', hxy⟩ ↦ by
          have h := congrArg Subtype.val hxy
          change j x' = j x at h
          change j x ∈ Z
          exact h ▸ hx',
        fun h ↦ ⟨x, h, rfl⟩⟩
    rw [himage]
    exact hZ.preimage continuous_subtype_val
  exact hψ.comp hj'

/-- A topological linear embedding with closed range into a Fréchet space induces a topological
linear isomorphism of quotients, once the target quotient is Fréchet, the source denominator is
the preimage of the target one, and every target class meets the range. -/
private theorem strongCoprimality_quotientEquiv {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
    (D : Submodule ℂ X) (E : Submodule ℂ Y)
    (hY : IsFrechetTVS Y) (hQ : IsFrechetTVS (Y ⧸ E))
    (j : X →L[ℂ] Y) (hj : IsEmbedding j) (hc : IsClosed (range j))
    (hmem : ∀ x, j x ∈ E ↔ x ∈ D) (hs : ∀ y, ∃ x, y - j x ∈ E) :
    ∃ e : (X ⧸ D) ≃L[ℂ] (Y ⧸ E), ∀ x : X,
      e (Submodule.Quotient.mk x) = Submodule.Quotient.mk (j x) := by
  let φ : X →L[ℂ] Y ⧸ E := E.mkQL.comp j
  have hle : D ≤ LinearMap.ker (φ : X →ₗ[ℂ] Y ⧸ E) := fun x hx ↦ by
    rw [LinearMap.mem_ker]
    exact (Submodule.Quotient.mk_eq_zero E).mpr ((hmem x).mpr hx)
  let J : X ⧸ D →L[ℂ] Y ⧸ E := D.liftQL φ hle
  have hJ (x : X) : J (Submodule.Quotient.mk x) = Submodule.Quotient.mk (j x) := rfl
  have hinj : Injective J := by
    refine (injective_iff_map_eq_zero J).mpr fun z hz ↦ ?_
    obtain ⟨x, rfl⟩ := D.mkQ_surjective z
    change Submodule.Quotient.mk (j x) = (0 : Y ⧸ E) at hz
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact (hmem x).mp ((Submodule.Quotient.mk_eq_zero E).mp hz)
  have hs' (y : Y) : ∃ x, E.mkQL y = E.mkQL (j x) := by
    obtain ⟨x, hx⟩ := hs y
    exact ⟨x, (Submodule.Quotient.eq E).mpr hx⟩
  have hsurj : Surjective J := by
    intro z
    obtain ⟨y, rfl⟩ := E.mkQ_surjective z
    obtain ⟨x, hx⟩ := hs' y
    exact ⟨Submodule.Quotient.mk x, hx.symm⟩
  have hopen0 := strongCoprimality_isOpenMap hY hQ j hj hc E.mkQL E.mkQ_surjective hs'
  have hopen : IsOpenMap J := by
    intro W hW
    have himage : J '' W = (fun x ↦ E.mkQL (j x)) '' (D.mkQ ⁻¹' W) := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        obtain ⟨x, rfl⟩ := D.mkQ_surjective w
        exact ⟨x, hw, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨D.mkQ x, hx, rfl⟩
    rw [himage]
    exact hopen0 _ (hW.preimage D.isQuotientMap_mkQ.continuous)
  let L := LinearEquiv.ofBijective (J : X ⧸ D →ₗ[ℂ] Y ⧸ E) ⟨hinj, hsurj⟩
  let H := L.toEquiv.toHomeomorphOfContinuousOpen J.continuous hopen
  exact ⟨⟨L, J.continuous, H.symm.continuous⟩, hJ⟩

open MeasureTheory in
/-- Translation of an isotypic function along a right inverse of the norm multiplies its
Mellin integral by the value of the Mellin character at the translating element. It repeats
`strongCoprimality_bezout_translate`, which is declared after `strongCoprimality`. -/
private theorem strongCoprimality_mem_differenceRange_iff_translate {G : Type*} [CommGroup G]
    (m : G →* ℝ≥0ˣ) (σ : ℝ≥0ˣ →* G) (hσ : RightInverse σ m)
    (c : G →* ℂ) (u : G → ℂ)
    (hu : ∀ (k : m.ker) x, u (k.val⁻¹ * x) = c k.val * u x) (g : G) :
    (∫ t, u (g⁻¹ * σ t) * c (σ t) ∂positiveRealHaar) =
      c g * ∫ t, u (σ t) * c (σ t) ∂positiveRealHaar := by
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  let : positiveRealHaar.IsHaarMeasure := RiemannMasullo.positiveRealHaar_isHaarMeasure
  let k : m.ker := ⟨g / σ (m g), by rw [MonoidHom.mem_ker, map_div, hσ, div_self']⟩
  rw [← integral_mul_left_eq_self (μ := positiveRealHaar)
    (fun t ↦ u (g⁻¹ * σ t) * c (σ t)) (m g), ← integral_const_mul]
  apply integral_congr_ae (.of_forall fun t ↦ ?_)
  have he : g⁻¹ * σ (m g * t) = k.val⁻¹ * σ t := by
    simp [k, map_mul, div_eq_mul_inv, mul_comm, mul_left_comm]
  rw [he, hu, map_mul, map_mul, show c k.val = c (g / σ (m g)) from rfl, map_div]
  have hn : c (σ (m g)) ≠ 0 := ((Group.isUnit _).map c).ne_zero
  field_simp

/-- The Mellin character of a uniformizer gives the single-place Euler polynomial. It repeats
`strongCoprimality_bezout_factor`, which is declared after `strongCoprimality`. -/
private theorem strongCoprimality_mem_differenceRange_iff_factor (χ : U) (v : V)
    (u : (v.adicCompletion F)ˣ) (hu : Valued.v.IsUniformizer (u : v.adicCompletion F))
    (hv : (ideleClassNormTwist χ 0).IsUnramifiedAt v) (s : ℂ) :
    1 - ideleClassNormTwist χ s (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u) =
      (finiteHeckeEulerFactor χ v s)⁻¹ := by
  rw [finiteHeckeEulerFactor, ite_eq_left hv, inv_inv, hv.localValue_eq u hu,
    HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
  let g := IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u
  change 1 - (χ g : ℂ) * ((((ideleClassNorm F g).val : ℝ) : ℂ) ^ s) =
    1 - ((χ g : ℂ) * ((((ideleClassNorm F g).val : ℝ) : ℂ) ^ (0 : ℂ))) *
      (v.asIdeal.absNorm : ℂ) ^ (-s)
  have hn : (((ideleClassNorm F g).val : ℝ)) = (v.asIdeal.absNorm : ℝ)⁻¹ :=
    (congrArg (fun t : ℝ≥0ˣ ↦ (t.val : ℝ)) (ideleClassNorm_ofAdicCompletion F v u)).trans
      (norm_uniformizer_adicCompletion v _ hu)
  rw [hn, Complex.cpow_zero, mul_one, Complex.ofReal_inv,
    Complex.inv_cpow_ofReal_nonneg (Nat.cast_nonneg _), Complex.cpow_neg, Complex.ofReal_natCast]

open MeasureTheory in
/-- The Mellin model of the decay isotype takes an unramified difference product to
multiplication by its reciprocal Euler polynomial. It repeats
`strongCoprimality_bezout_difference`, which is declared after `strongCoprimality`. -/
private theorem strongCoprimality_mem_differenceRange_iff_mellin (χ : U)
    (τ : ℝ≥0ˣ →ₜ* I𝔽) (hτ : RightInverse τ (ideleNorm F))
    (S : Finset V) (π : (v : V) → (v.adicCompletion F)ˣ)
    (hπ : ∀ v ∈ S, Valued.v.IsUniformizer (π v : v.adicCompletion F))
    (hS : ∀ v ∈ S, (ideleClassNormTwist χ 0).IsUnramifiedAt v)
    (M : StrongCoprimalityDecaySpace ω(χ) ≃L[ℂ] B)
    (hM : ∀ (f : StrongCoprimalityDecaySpace ω(χ)) s, (M f).val s =
      ∫ t : ℝ≥0ˣ, f.val.val (QuotientGroup.mk (τ t)) *
        ideleClassNormTwist χ s (QuotientGroup.mk (τ t)) ∂positiveRealHaar)
    (f g : StrongCoprimalityDecaySpace ω(χ))
    (hg : g.val.val = strongCoprimalityDifference S π f.val.val) (s : ℂ) :
    (M g).val s = reciprocalPartialHeckeEulerProduct χ S s * (M f).val s := by
  let σ : ℝ≥0ˣ →* C𝔽 := (QuotientGroup.mk' _).comp τ.toMonoidHom
  have hσ : RightInverse σ (ideleClassNorm F) := fun t ↦ hτ t
  let c := ideleClassNormTwist χ s
  let a (v : V) := IdeleClassGroup.ofAdicCompletion (𝓞 F) F v (π v)
  let hm := strongCoprimalityNorm_isModulation_surjective (F := F)
  let D (l : List V) := modulatedIsotypicDifferenceProduct m𝔽 hm.1 hm.2 ω(χ) univ
    ordConnected_univ (mem_univ (0 : ℝ)) (l.map fun v ↦ (a v)⁻¹)
  have hsub (v : V) (l : List V) (x : C𝔽) :
      ((D (v :: l)) f).val.val x = ((D l) f).val.val x - ((D l) f).val.val ((a v)⁻¹ * x) :=
    modulatedCyclicDifference_apply m𝔽 (a v)⁻¹ hm.1 hm.2 univ ordConnected_univ univ_nonempty
      ((D l) f).val x
  have htrans (v : V) (l : List V) : (M ((D (v :: l)) f)).val s =
      (1 - c (a v)) * (M ((D l) f)).val s := by
    let z := (D l) f
    let y := z - (D (v :: l)) f
    have hy (x : C𝔽) : y.val.val x = z.val.val ((a v)⁻¹ * x) := by
      change z.val.val x - ((D (v :: l)) f).val.val x = _
      rw [hsub]
      ring
    have hk (k : (ideleClassNorm F).ker) (x : C𝔽) :
        z.val.val (k.val⁻¹ * x) = c k.val * z.val.val x := by
      have hh := (mem_modulatedDecayIsotype_iff m𝔽 ω(χ) univ (mem_univ _) z.val).mp z.property k x
      have hck : c k.val = (χ k.val : ℂ) := by
        change (χ k.val : ℂ) * ((((ideleClassNorm F k.val).val : ℝ) : ℂ) ^ s) = _
        rw [k.property]
        simp
      rw [hck]
      exact hh
    have he : (M y).val s = c (a v) * (M z).val s := by
      rw [hM, hM]
      simp only [hy]
      exact strongCoprimality_mem_differenceRange_iff_translate (ideleClassNorm F) σ hσ
        c.toMonoidHom z.val.val hk (a v)
    rw [show (D (v :: l)) f = z - y from (sub_sub_cancel z ((D (v :: l)) f)).symm, map_sub]
    change (M z).val s - (M y).val s = _
    rw [he]
    ring
  have hprod (l : List V) (hl : ∀ v ∈ l, v ∈ S) : (M ((D l) f)).val s =
      ((l.map fun v ↦ (finiteHeckeEulerFactor χ v s)⁻¹).prod) * (M f).val s := by
    induction l with
    | nil => rw [List.map_nil, List.prod_nil, one_mul]; rfl
    | cons v l ih =>
      have hv := hl v (List.mem_cons_self ..)
      rw [htrans, strongCoprimality_mem_differenceRange_iff_factor χ v (π v) (hπ v hv) (hS v hv),
        ih (fun w hw ↦ hl w (List.mem_cons_of_mem _ hw))]
      simp [mul_assoc]
  have hfold (l : List V) (x : C𝔽) : ((D l) f).val.val x =
      l.foldr (fun v (w : C𝔽 → ℂ) y ↦ w y - w ((a v)⁻¹ * y)) f.val.val x := by
    induction l generalizing x with
    | nil => rfl
    | cons v l ih => exact (hsub v l x).trans (congrArg₂ (· - ·) (ih x) (ih ((a v)⁻¹ * x)))
  have he : g = (D S.toList) f :=
    Subtype.ext (Subtype.ext (funext fun x ↦ (congrFun hg x).trans (hfold S.toList x).symm))
  rw [he, hprod S.toList (fun v hv ↦ Finset.mem_toList.mp hv)]
  simp [reciprocalPartialHeckeEulerProduct]

/-- The iterated difference of a function of the decay isotype is again a function of the
decay isotype. -/
private theorem strongCoprimality_mem_differenceRange_iff_difference (ω : PontryaginDual C₁)
    (T : Finset V) (π : (v : V) → (v.adicCompletion F)ˣ) (z : StrongCoprimalityDecaySpace ω) :
    ∃ y : StrongCoprimalityDecaySpace ω,
      y.val.val = strongCoprimalityDifference T π z.val.val := by
  let a (v : V) := IdeleClassGroup.ofAdicCompletion (𝓞 F) F v (π v)
  let hm := strongCoprimalityNorm_isModulation_surjective (F := F)
  let D (l : List V) := modulatedIsotypicDifferenceProduct m𝔽 hm.1 hm.2 ω univ
    ordConnected_univ (mem_univ (0 : ℝ)) (l.map fun v ↦ (a v)⁻¹)
  have hsub (v : V) (l : List V) (x : C𝔽) :
      ((D (v :: l)) z).val.val x = ((D l) z).val.val x - ((D l) z).val.val ((a v)⁻¹ * x) :=
    modulatedCyclicDifference_apply m𝔽 (a v)⁻¹ hm.1 hm.2 univ ordConnected_univ univ_nonempty
      ((D l) z).val x
  have hfold (l : List V) (x : C𝔽) : ((D l) z).val.val x =
      l.foldr (fun v (w : C𝔽 → ℂ) y ↦ w y - w ((a v)⁻¹ * y)) z.val.val x := by
    induction l generalizing x with
    | nil => rfl
    | cons v l ih => exact (hsub v l x).trans (congrArg₂ (· - ·) (ih x) (ih ((a v)⁻¹ * x)))
  exact ⟨(D T.toList) z, funext fun x ↦ hfold T.toList x⟩

open MeasureTheory in
/-- In the Mellin model of the decay isotype, the homogeneous theta function of a zero-moment
test has the global zeta function of the test as its transform. -/
private theorem strongCoprimality_mem_differenceRange_iff_theta (χ : U)
    (τ : ℝ≥0ˣ →ₜ* I𝔽) (hτ : RightInverse τ (ideleNorm F))
    (j : StrongCoprimalityThetaSpace ω(χ) →L[ℂ] StrongCoprimalityDecaySpace ω(χ))
    (hj : ∀ (f : P) (g : C𝔽),
      (j ((K(ω(χ))).mkQ f)).val.val g = homogeneousAdelicThetaLinearMap F ω(χ) f.val g)
    (M : StrongCoprimalityDecaySpace ω(χ) ≃L[ℂ] B)
    (hM : ∀ (f : StrongCoprimalityDecaySpace ω(χ)) s, (M f).val s =
      ∫ t : ℝ≥0ˣ, f.val.val (QuotientGroup.mk (τ t)) *
        ideleClassNormTwist χ s (QuotientGroup.mk (τ t)) ∂positiveRealHaar)
    (f : P) (s : ℂ) :
    (M (j ((K(ω(χ))).mkQ f))).val s =
      globalIdelicZFunction f.val (ideleClassNormTwist χ s) := by
  have h := (exists_globalPolarThetaMellin χ τ hτ).choose_spec f s
  rw [hM]
  refine Eq.trans ?_ (h.1.symm.trans h.2)
  exact integral_congr_ae (.of_forall fun t ↦ congrArg
    (· * ideleClassNormTwist χ s (QuotientGroup.mk (τ t))) (hj f (QuotientGroup.mk (τ t))))

/-- The reciprocal Euler product over a finite set of places is an entire function. -/
private theorem strongCoprimality_mem_differenceRange_iff_euler (χ : U) (S : Finset V) :
    Differentiable ℂ (reciprocalPartialHeckeEulerProduct χ S) := by
  have hfactor (v : V) : Differentiable ℂ (fun s ↦ (finiteHeckeEulerFactor χ v s)⁻¹) := by
    unfold finiteHeckeEulerFactor
    split_ifs
    · simp_rw [inv_inv]
      have hq : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr
        ((Ideal.absNorm_eq_zero_iff).not.mpr v.ne_bot)
      exact (differentiable_const _).sub ((differentiable_const _).mul
        ((differentiable_neg).const_cpow (Or.inl hq)))
    · simp_rw [inv_one]
      exact differentiable_const _
  unfold reciprocalPartialHeckeEulerProduct
  exact Differentiable.fun_finsetProd fun v _ ↦ hfactor v

/-- On zero-moment tests the principal value multiplies the global zeta function by the
reciprocal Euler product at every point: both sides are entire, and they agree off a
discrete set. -/
private theorem strongCoprimality_mem_differenceRange_iff_principalValue (χ : U)
    (S : Finset V) (g : P) (s : ℂ) :
    globalIdelicZFunction (adelePrincipalValue F S g.val) (ideleClassNormTwist χ s) =
      reciprocalPartialHeckeEulerProduct χ S s *
        globalIdelicZFunction g.val (ideleClassNormTwist χ s) := by
  have hE := strongCoprimality_mem_differenceRange_iff_euler χ S
  have hg := globalIdelicZFunction_entire_of_vanishing g.val g.property χ
  have hpv := globalIdelicZFunction_entire_of_vanishing (adelePrincipalValue F S g.val)
    (strongCoprimalityPrincipalValue_mem_polar S g) χ
  have H := nhdsNE_le_codiscrete s (globalPrincipalValueConverse_mellin S χ g.val)
  exact (((hpv.analyticAt s).meromorphicNFAt.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
    ((hE.mul hg).analyticAt s).meromorphicNFAt).mp H).eq_of_nhds

/-- The homogeneous theta function of the principal value of a zero-moment test is the
difference product, over a set of unramified places carrying the same reciprocal Euler
product, of the homogeneous theta function of the test: the two have the same transform
in the Mellin model of the decay isotype. -/
private theorem strongCoprimality_mem_differenceRange_iff_thetaPrincipalValue (χ : U)
    (S T : Finset V) (π : (v : V) → (v.adicCompletion F)ˣ)
    (hπ : ∀ v ∈ T, Valued.v.IsUniformizer (π v : v.adicCompletion F))
    (hT : ∀ v ∈ T, (ideleClassNormTwist χ 0).IsUnramifiedAt v)
    (hST : ∀ s, reciprocalPartialHeckeEulerProduct χ S s =
      reciprocalPartialHeckeEulerProduct χ T s)
    (j : StrongCoprimalityThetaSpace ω(χ) →L[ℂ] StrongCoprimalityDecaySpace ω(χ))
    (hj : ∀ (f : P) (g : C𝔽),
      (j ((K(ω(χ))).mkQ f)).val.val g = homogeneousAdelicThetaLinearMap F ω(χ) f.val g)
    (g : P) :
    (j ((K(ω(χ))).mkQ ⟨adelePrincipalValue F S g.val,
      strongCoprimalityPrincipalValue_mem_polar S g⟩)).val.val =
      strongCoprimalityDifference T π (j ((K(ω(χ))).mkQ g)).val.val := by
  let τ : ℝ≥0ˣ →ₜ* I𝔽 :=
    ⟨canonicalIdeleNormSection F, canonicalIdeleNormSection_continuous F⟩
  have hτ : RightInverse τ (ideleNorm F) := canonicalIdeleNormSection_rightInverse F
  obtain ⟨M, hM, -⟩ := spectralNuclearityDenominator_isotypeModel χ τ hτ 0
  obtain ⟨y, hy⟩ := strongCoprimality_mem_differenceRange_iff_difference ω(χ) T π
    (j ((K(ω(χ))).mkQ g))
  have he : j ((K(ω(χ))).mkQ ⟨adelePrincipalValue F S g.val,
      strongCoprimalityPrincipalValue_mem_polar S g⟩) = y := by
    refine M.injective (Subtype.ext (funext fun s ↦ ?_))
    rw [strongCoprimality_mem_differenceRange_iff_theta χ τ hτ j hj M hM,
      strongCoprimality_mem_differenceRange_iff_mellin χ τ hτ T π hπ hT M hM _ y hy s,
      strongCoprimality_mem_differenceRange_iff_theta χ τ hτ j hj M hM, ← hST]
    exact strongCoprimality_mem_differenceRange_iff_principalValue χ S g s
  rw [he, hy]

/-- A Schwartz–Bergman function lies in the divisible subspace of an entire function exactly
when it is that function times an entire function. It repeats the private `specDenom_mem_div`
of `Ch07_SchauderBasesZeta/Sec4.lean`. -/
private theorem strongCoprimality_mem_differenceRange_iff_divisible
    (g : entireContinuousMapSubalgebra) (φ : B) :
    φ ∈ schwartzBergmanDivisible g ↔
      ∃ u : ℂ → ℂ, Differentiable ℂ u ∧ ∀ s, φ.val s = g.val s * u s := by
  rw [schwartzBergmanDivisible, Submodule.mem_comap, Submodule.restrictScalars_mem,
    Ideal.mem_span_singleton']
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a.val, a.property, fun s ↦ ?_⟩
    have h := congrArg (fun e : entireContinuousMapSubalgebra ↦ e.val s) ha
    change a.val s * g.val s = (schwartzBergmanEntireInclusion φ).val s at h
    rw [schwartzBergmanEntireInclusion_apply] at h
    rw [← h, mul_comm]
  · rintro ⟨u, hu, h⟩
    refine ⟨⟨⟨u, hu.continuous⟩, hu⟩, ?_⟩
    apply Subtype.ext
    ext s
    change u s * g.val s = (schwartzBergmanEntireInclusion φ).val s
    rw [schwartzBergmanEntireInclusion_apply, h, mul_comm]

/-- An entire function divides another one, with entire quotient, as soon as its vanishing
order at every point is at most that of the other. The proof is the one of the private
`archNuclearityMellin_range_entire_dvd` of `Ch07_SchauderBasesZeta/Sec4.lean`. -/
private theorem strongCoprimality_mem_differenceRange_iff_dvd (g f : ℂ → ℂ)
    (hg : Differentiable ℂ g) (hf : Differentiable ℂ f)
    (hord : ∀ z : ℂ, analyticOrderAt g z ≤ analyticOrderAt f z) :
    ∃ q : ℂ → ℂ, Differentiable ℂ q ∧ ∀ z, f z = g z * q z := by
  let q := f / g
  have hq : MeromorphicOn q univ :=
    fun z _ ↦ (hf.analyticAt z).meromorphicAt.div (hg.analyticAt z).meromorphicAt
  have hdiff : Differentiable ℂ (toMeromorphicNFOn q univ) := by
    intro z
    apply AnalyticAt.differentiableAt
    have hnf := meromorphicNFOn_toMeromorphicNFOn q univ (mem_univ z)
    apply hnf.meromorphicOrderAt_nonneg_iff_analyticAt.mp
    rw [meromorphicOrderAt_toMeromorphicNFOn hq (mem_univ z),
      meromorphicOrderAt_div (hf.analyticAt z).meromorphicAt (hg.analyticAt z).meromorphicAt,
      (hf.analyticAt z).meromorphicOrderAt_eq, (hg.analyticAt z).meromorphicOrderAt_eq]
    have hle := hord z
    generalize analyticOrderAt f z = m at hle ⊢
    generalize analyticOrderAt g z = n at hle ⊢
    cases m using ENat.recTopCoe with
    | top => simp
    | coe m =>
      cases n using ENat.recTopCoe with
      | top => simp at hle
      | coe n =>
        exact WithTop.coe_le_coe.mpr (sub_nonneg.mpr (by exact_mod_cast hle : (n : ℤ) ≤ m))
  refine ⟨_, hdiff, fun z ↦ ?_⟩
  by_cases hz : g z = 0
  · have hpos := lt_of_lt_of_le
      (pos_iff_ne_zero.mpr ((hg.analyticAt z).analyticOrderAt_ne_zero.mpr hz)) (hord z)
    rw [hz, zero_mul]
    exact (hf.analyticAt z).analyticOrderAt_ne_zero.mp hpos.ne'
  · rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hq (mem_univ z),
      toMeromorphicNFAt_eq_self.mpr ((hf.analyticAt z).div (hg.analyticAt z) hz).meromorphicNFAt]
    exact (mul_div_cancel₀ _ hz).symm

/-- The functional equation and the zero-free right boundary exclude completed zeros in the
closed left half-plane. It repeats the private
`archNuclearityMellin_range_completed_order_left` of `Ch07_SchauderBasesZeta/Sec4.lean`. -/
private theorem strongCoprimality_mem_differenceRange_iff_order_left
    (χ : U) (s : ℂ) (hs : s.re ≤ 0) :
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
  rw [ho]
  apply le_of_not_gt
  intro hz
  have hzre := completedHeckeL_continuation_zeros χ⁻¹ (continuedCompletedHeckeL χ⁻¹)
    (continuedCompletedHeckeL_spec χ⁻¹).1 (continuedCompletedHeckeL_spec χ⁻¹).2
    (s := r s) (by change 0 < 1 - s.re; linarith) hz
  change 1 - s.re < 1 at hzre
  linarith

/-- After removing the two poles, the completed generator is nonzero in the closed left
half-plane. It repeats the private `archNuclearityMellin_range_completed_ne_zero_left` of
`Ch07_SchauderBasesZeta/Sec4.lean`. -/
private theorem strongCoprimality_mem_differenceRange_iff_ne_zero_left
    (χ : U) (τ : ℝ≥0ˣ →ₜ* I𝔽) (hτ : RightInverse τ (ideleNorm F))
    (s : ℂ) (hs : s.re ≤ 0) :
    (regularizedCompletedHeckeL χ τ hτ (continuedCompletedHeckeL χ)
      (continuedCompletedHeckeL_spec χ).1 (continuedCompletedHeckeL_spec χ).2).val s ≠ 0 := by
  classical
  let L := continuedCompletedHeckeL χ
  let G := regularizedCompletedHeckeL χ τ hτ L
    (continuedCompletedHeckeL_spec χ).1 (continuedCompletedHeckeL_spec χ).2
  let x : ℝ := (existsUnique_ideleNormSection_character_phase χ τ hτ).exists.choose
  let b : ℂ := (x : ℂ) * Complex.I
  let δ : ℕ := if χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1 then 1 else 0
  let p : ℂ → ℂ := fun z ↦ (z + b) ^ δ * (1 - z - b) ^ δ
  have hG : Differentiable ℂ (G.val : ℂ → ℂ) := G.property
  have hp : Differentiable ℂ p := by dsimp [p]; fun_prop
  have hL := (continuedCompletedHeckeL_spec χ).1
  by_cases hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1
  · by_cases hs₀ : s = -b
    · subst s
      exact (regularizedCompletedHeckeL_ne_zero_at_canceled_poles χ τ hτ L
        (continuedCompletedHeckeL_spec χ).1 (continuedCompletedHeckeL_spec χ).2 hχ).1
    · have hp₀ : p s ≠ 0 := by
        simp only [p, δ, ite_eq_left hχ, pow_one]
        apply mul_ne_zero
        · intro h
          exact hs₀ (eq_neg_of_add_eq_zero_left h)
        · intro h
          have hreal := congrArg Complex.re h
          simp only [Complex.sub_re, Complex.one_re, Complex.zero_re,
            b, Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
            Complex.ofReal_im, Complex.I_im, zero_mul, sub_self] at hreal
          linarith
      have hm : MeromorphicOn (p * L) univ := fun z _ ↦
        (hp.analyticAt z).meromorphicAt.mul (hL (mem_univ z)).meromorphicAt
      have hord : meromorphicOrderAt (G.val : ℂ → ℂ) s = meromorphicOrderAt L s := by
        change meromorphicOrderAt (toMeromorphicNFOn (p * L) univ) s = _
        rw [meromorphicOrderAt_toMeromorphicNFOn hm (mem_univ s),
          meromorphicOrderAt_mul_of_ne_zero (hp.analyticAt s) hp₀]
      apply (hG.analyticAt s).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp
      apply le_antisymm
      · rw [hord]
        exact strongCoprimality_mem_differenceRange_iff_order_left χ s hs
      · exact (hG.analyticAt s).meromorphicOrderAt_nonneg
  · have he : (G.val : ℂ → ℂ) = L := by
      change toMeromorphicNFOn (fun z ↦ (z + b) ^ δ * (1 - z - b) ^ δ * L z) univ = L
      simp only [δ, ite_eq_right hχ, pow_zero, one_mul]
      exact toMeromorphicNFOn_eq_self.mpr hL
    apply (hG.analyticAt s).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp
    apply le_antisymm
    · rw [he]
      exact strongCoprimality_mem_differenceRange_iff_order_left χ s hs
    · exact (hG.analyticAt s).meromorphicOrderAt_nonneg

/-- A zero of the reciprocal Euler product over unramified places lies on the imaginary
axis: there the norm twist takes the value one on the class of a uniformizer, and the norm
of that class differs from one. -/
private theorem strongCoprimality_mem_differenceRange_iff_re_eq_zero (χ : U) (T : Finset V)
    (π : (v : V) → (v.adicCompletion F)ˣ)
    (hπ : ∀ v ∈ T, Valued.v.IsUniformizer (π v : v.adicCompletion F))
    (hT : ∀ v ∈ T, (ideleClassNormTwist χ 0).IsUnramifiedAt v) (s : ℂ)
    (hs : reciprocalPartialHeckeEulerProduct χ T s = 0) : s.re = 0 := by
  obtain ⟨v, hv, h0⟩ := Finset.prod_eq_zero_iff.mp hs
  rw [← strongCoprimality_mem_differenceRange_iff_factor χ v (π v) (hπ v hv) (hT v hv) s] at h0
  let g := IdeleClassGroup.ofAdicCompletion (𝓞 F) F v (π v)
  have h1 : (χ g : ℂ) * ((((ideleClassNorm F g).val : ℝ) : ℂ) ^ s) = 1 :=
    (sub_eq_zero.mp h0).symm
  have hn : (((ideleClassNorm F g).val : ℝ)) = (v.asIdeal.absNorm : ℝ)⁻¹ :=
    (congrArg (fun t : ℝ≥0ˣ ↦ (t.val : ℝ)) (ideleClassNorm_ofAdicCompletion F v (π v))).trans
      (norm_uniformizer_adicCompletion v _ (hπ v hv))
  have hN : (1 : ℝ) < (v.asIdeal.absNorm : ℝ) := by
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hpos : (0 : ℝ) < (v.asIdeal.absNorm : ℝ)⁻¹ := inv_pos.mpr (zero_lt_one.trans hN)
  have hnorm := congrArg norm h1
  rw [norm_mul, Circle.norm_coe, one_mul, norm_one, hn,
    Complex.norm_cpow_eq_rpow_re_of_pos hpos] at hnorm
  have hlt : (v.asIdeal.absNorm : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hN
  rcases lt_trichotomy s.re 0 with h | h | h
  · exact absurd hnorm (Real.one_lt_rpow_of_pos_of_lt_one_of_neg hpos hlt h).ne'
  · exact h
  · exact absurd hnorm (Real.rpow_lt_one hpos.le hlt h).ne

/-- In the Mellin model, a Schwartz–Bergman function whose product with the reciprocal
Euler product over unramified places is divisible by the regularized completed Hecke
function is itself divisible by it: the zeros of the Euler product lie on the imaginary
axis, where the completed function does not vanish. -/
private theorem strongCoprimality_mem_differenceRange_iff_cancel (χ : U)
    (τ : ℝ≥0ˣ →ₜ* I𝔽) (hτ : RightInverse τ (ideleNorm F)) (T : Finset V)
    (π : (v : V) → (v.adicCompletion F)ˣ)
    (hπ : ∀ v ∈ T, Valued.v.IsUniformizer (π v : v.adicCompletion F))
    (hT : ∀ v ∈ T, (ideleClassNormTwist χ 0).IsUnramifiedAt v) (φ b : B)
    (hφ : φ ∈ spectralNuclearityDenominator χ τ hτ 0)
    (h : ∀ s, φ.val s = reciprocalPartialHeckeEulerProduct χ T s * b.val s) :
    b ∈ spectralNuclearityDenominator χ τ hτ 0 := by
  let Λ := regularizedCompletedHeckeL χ τ hτ (continuedCompletedHeckeL χ)
    (continuedCompletedHeckeL_spec χ).1 (continuedCompletedHeckeL_spec χ).2
  let G (s : ℂ) : ℂ := Λ.val (s + ((0 : ℝ) : ℂ))
  have hG : Differentiable ℂ G := spectralNuclearityGenerator_differentiable χ τ hτ 0
  have hG0 (z : ℂ) : G z = Λ.val z := by
    change Λ.val (z + ((0 : ℝ) : ℂ)) = Λ.val z
    rw [Complex.ofReal_zero, add_zero]
  rw [spectralNuclearityDenominator, strongCoprimality_mem_differenceRange_iff_divisible] at hφ ⊢
  obtain ⟨u, hu, hφu⟩ := hφ
  change ∀ s, φ.val s = G s * u s at hφu
  have hb : Differentiable ℂ (b.val : ℂ → ℂ) := by
    have hd : Differentiable ℂ ((schwartzBergmanEntireInclusion b).val : ℂ → ℂ) :=
      (schwartzBergmanEntireInclusion b).property
    rwa [show ((schwartzBergmanEntireInclusion b).val : ℂ → ℂ) = b.val from
      funext (schwartzBergmanEntireInclusion_apply b)] at hd
  have hR := strongCoprimality_mem_differenceRange_iff_euler χ T
  have hord (z : ℂ) : analyticOrderAt G z ≤ analyticOrderAt (b.val : ℂ → ℂ) z := by
    by_cases hz : reciprocalPartialHeckeEulerProduct χ T z = 0
    · have hre := strongCoprimality_mem_differenceRange_iff_re_eq_zero χ T π hπ hT z hz
      have hne : G z ≠ 0 := (hG0 z).trans_ne
        (strongCoprimality_mem_differenceRange_iff_ne_zero_left χ τ hτ z hre.le)
      rw [(hG.analyticAt z).analyticOrderAt_eq_zero.mpr hne]
      exact bot_le
    · have he : G * u = reciprocalPartialHeckeEulerProduct χ T * (b.val : ℂ → ℂ) :=
        funext fun s ↦ (hφu s).symm.trans (h s)
      have ho := congrArg (fun w : ℂ → ℂ ↦ analyticOrderAt w z) he
      simp only [analyticOrderAt_mul (hG.analyticAt z) (hu.analyticAt z),
        analyticOrderAt_mul (hR.analyticAt z) (hb.analyticAt z),
        (hR.analyticAt z).analyticOrderAt_eq_zero.mpr hz, zero_add] at ho
      rw [← ho]
      exact self_le_add_right _ _
  obtain ⟨q, hq, hbq⟩ := strongCoprimality_mem_differenceRange_iff_dvd G b.val hG hb hord
  exact ⟨q, hq, hbq⟩

open Classical in
/-- Paper: Theorem 7.5.0.1, pp. 374–376.
A pole-free homogeneous theta class lies in the principal-value denominator over `S` exactly
when its homogeneous theta function lies in the range of the difference product over the
unramified places of `S`, each difference taken along the inverse class of `π v`. -/
private theorem strongCoprimality_mem_differenceRange_iff (χ : U) (S : Finset V)
    (π : (v : V) → (v.adicCompletion F)ˣ)
    (hπ : ∀ v ∈ S, Valuation.IsUniformizer
      (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))) (π v).val)
    (j : StrongCoprimalityThetaSpace ω(χ) →L[ℂ] StrongCoprimalityDecaySpace ω(χ))
    (hj : ∀ (f : P) (g : C𝔽),
      (j ((K(ω(χ))).mkQ f)).val.val g = homogeneousAdelicThetaLinearMap F ω(χ) f.val g)
    (x : StrongCoprimalityThetaSpace ω(χ)) :
    j x ∈ strongCoprimalityDifferenceRange ω(χ)
        (S.filter (fun v ↦ (ideleClassNormTwist χ 0).IsUnramifiedAt v)) π ↔
      x ∈ strongCoprimalityDenominator ω(χ) S := by
  have hπT : ∀ v ∈ S.filter (fun v ↦ (ideleClassNormTwist χ 0).IsUnramifiedAt v),
      Valued.v.IsUniformizer (π v : v.adicCompletion F) :=
    fun v hv ↦ hπ v (Finset.mem_filter.mp hv).1
  have hT : ∀ v ∈ S.filter (fun v ↦ (ideleClassNormTwist χ 0).IsUnramifiedAt v),
      (ideleClassNormTwist χ 0).IsUnramifiedAt v := fun v hv ↦ (Finset.mem_filter.mp hv).2
  have hST (s : ℂ) : reciprocalPartialHeckeEulerProduct χ S s =
      reciprocalPartialHeckeEulerProduct χ
        (S.filter (fun v ↦ (ideleClassNormTwist χ 0).IsUnramifiedAt v)) s := by
    unfold reciprocalPartialHeckeEulerProduct
    rw [Finset.prod_filter]
    refine Finset.prod_congr rfl fun v _ ↦ ?_
    by_cases hv : (ideleClassNormTwist χ 0).IsUnramifiedAt v
    · rw [ite_eq_left hv]
    · rw [ite_eq_right hv, finiteHeckeEulerFactor, ite_eq_right hv, inv_one]
  have hpv := strongCoprimality_mem_differenceRange_iff_thetaPrincipalValue χ S _ π hπT hT hST
    j hj
  constructor
  · intro hx
    obtain ⟨z, hz⟩ := (mem_strongCoprimalityDifferenceRange ω(χ) _ π (j x)).mp hx
    let τ : ℝ≥0ˣ →ₜ* I𝔽 :=
      ⟨canonicalIdeleNormSection F, canonicalIdeleNormSection_continuous F⟩
    have hτ : RightInverse τ (ideleNorm F) := canonicalIdeleNormSection_rightInverse F
    obtain ⟨M, hM, hθ⟩ := spectralNuclearityDenominator_isotypeModel χ τ hτ 0
    have hjx : M (j x) ∈ spectralNuclearityDenominator χ τ hτ 0 := by
      obtain ⟨f, rfl⟩ := (K(ω(χ))).mkQ_surjective x
      refine (hθ _).mpr ⟨f, fun g ↦ ?_⟩
      simp only [Real.rpow_zero, Complex.ofReal_one, one_mul]
      rw [← homogeneousAdelicThetaLinearMap_apply (F := F) ω(χ) f.val]
      exact hj f g
    have hMz : M z ∈ spectralNuclearityDenominator χ τ hτ 0 :=
      strongCoprimality_mem_differenceRange_iff_cancel χ τ hτ _ π hπT hT (M (j x)) (M z) hjx
        (strongCoprimality_mem_differenceRange_iff_mellin χ τ hτ _ π hπT hT M hM z (j x) hz)
    obtain ⟨g, hg⟩ := (hθ z).mp hMz
    have hzg : z = j ((K(ω(χ))).mkQ g) := by
      refine Subtype.ext (Subtype.ext (funext fun c ↦ ?_))
      have h := hg c
      simp only [Real.rpow_zero, Complex.ofReal_one, one_mul] at h
      rw [← homogeneousAdelicThetaLinearMap_apply (F := F) ω(χ) g.val] at h
      exact h.trans (hj g c).symm
    have hx' : j ((K(ω(χ))).mkQ ⟨adelePrincipalValue F S g.val,
        strongCoprimalityPrincipalValue_mem_polar S g⟩) = j x :=
      Subtype.ext (Subtype.ext ((hpv g).trans
        ((congrArg _ (congrArg (fun w ↦ w.val.val) hzg.symm)).trans hz.symm)))
    rw [← exists_strongCoprimalityThetaEmbedding_injective ω(χ) j hj hx']
    exact Submodule.subset_span ⟨g, rfl⟩
  · intro hx
    obtain ⟨f, rfl⟩ := (K(ω(χ))).mkQ_surjective x
    have h0 : (strongCoprimalityDenominator ω(χ) S).mkQ ((K(ω(χ))).mkQ f) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr hx
    obtain ⟨g, hg⟩ := (strongCoprimalityQuotient_mk_eq_zero ω(χ) S f).mp h0
    rw [hg]
    exact (mem_strongCoprimalityDifferenceRange ω(χ) _ π _).mpr ⟨j ((K(ω(χ))).mkQ g), hpv g⟩

/-- Cardinal interpolation of summable values on the exponential lattice. The divided
difference of the exponential is one at zero and vanishes at the other lattice points.
Its imaginary translates are uniformly bounded on each vertical strip. -/
private theorem strongCoprimality_exists_sub_mem_cardinal (a : ℤ → ℂ) (ha : Summable fun n ↦ ‖a n‖) :
    ∃ A : ℂ → ℂ, Differentiable ℂ A ∧
      (∀ R : ℝ, ∃ C : ℝ, ∀ z : ℂ, |z.re| ≤ R → ‖A z‖ ≤ C) ∧
      ∀ n : ℤ, A (n * (2 * Real.pi * Complex.I)) = a n := by
  let K := dslope Complex.exp 0
  let p (n : ℤ) : ℂ := n * (2 * Real.pi * Complex.I)
  have hK : Differentiable ℂ K := fun z ↦
    ((Complex.differentiable_exp.analyticAt z).dslope 0).differentiableAt
  have hKr (R : ℝ) : ∃ C : ℝ, ∀ z : ℂ, |z.re| ≤ R → ‖K z‖ ≤ C := by
    obtain ⟨C, hC⟩ :=
      (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hK.continuous.continuousOn
    refine ⟨max C (Real.exp R + 1), fun z hz ↦ ?_⟩
    by_cases h : ‖z‖ ≤ 1
    · exact (hC z (mem_closedBall_zero_iff.mpr h)).trans (le_max_left ..)
    · have hne : z ≠ 0 := fun he ↦ h (by simp [he])
      rw [show K z = (Complex.exp z - 1) / z by simp [K, dslope_of_ne _ hne, slope_def_field], norm_div]
      apply le_trans _ (le_max_right ..)
      apply (div_le_self (norm_nonneg _) (by linarith : 1 ≤ ‖z‖)).trans
      exact (norm_sub_le _ _).trans (by rw [Complex.norm_exp, norm_one]; gcongr; exact (le_abs_self _).trans hz)
  let F (n : ℤ) (z : ℂ) := a n * K (z - p n)
  have bound (R : ℝ) : ∃ u : ℤ → ℝ, Summable u ∧
      ∀ n (z : ℂ), |z.re| ≤ R → ‖F n z‖ ≤ u n := by
    obtain ⟨C, hC⟩ := hKr R
    refine ⟨_, ha.mul_right C, fun n z hz ↦ ?_⟩
    exact (norm_mul ..).le.trans (mul_le_mul_of_nonneg_left
      (hC (z - p n) (by simpa [p] using hz)) (norm_nonneg _))
  refine ⟨fun z ↦ ∑' n, F n z, fun z ↦ ?_, fun R ↦ ?_, fun n ↦ ?_⟩
  · let R := |z.re| + 1
    obtain ⟨u, hu, hbu⟩ := bound R
    have hopen : IsOpen {w : ℂ | |w.re| < R} :=
      isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const
    exact (Complex.differentiableOn_tsum_of_summable_norm hu
      (fun n ↦ ((hK.comp (differentiable_id.sub_const (p n))).const_mul (a n)).differentiableOn)
      hopen (fun n w hw ↦ hbu n w (le_of_lt hw))).differentiableAt
        (hopen.mem_nhds (show |z.re| < R by dsimp [R]; linarith))
  · obtain ⟨u, hu, hbu⟩ := bound R
    exact ⟨∑' n, u n, fun z hz ↦ tsum_of_norm_bounded hu.hasSum (fun n ↦ hbu n z hz)⟩
  · change ∑' m, F m (p n) = _
    rw [tsum_eq_single n]
    · simp [F, K, dslope_same, Complex.deriv_exp]
    · intro m hm
      have hne : p n - p m ≠ 0 := by
        rw [show p n - p m = ((n : ℂ) - m) * (2 * Real.pi * Complex.I) by simp [p, sub_mul]]
        exact mul_ne_zero (sub_ne_zero.mpr (by exact_mod_cast hm.symm)) (by simp [Real.pi_ne_zero])
      simp [F, K, dslope_of_ne _ hne, slope_def_field, Complex.exp_sub, p,
        Complex.exp_int_mul_two_pi_mul_I]

/-- At sufficiently large height the completed continuation is analytic. This is the
two-pole argument used in `finiteHeckeL_continuation_isBigO_exp` in Appendix B. -/
private theorem strongCoprimality_exists_sub_mem_high (χ : U) :
    ∃ T : ℝ, ∀ z : ℂ, T ≤ |z.im| → AnalyticAt ℂ (continuedCompletedHeckeL χ) z := by
  classical
  let L := continuedCompletedHeckeL χ
  obtain ⟨hL, hEq⟩ := continuedCompletedHeckeL_spec χ
  by_cases hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1
  · obtain ⟨t, ⟨_, _, _, ha⟩, _⟩ := completedHeckeL_continuation_simplePoles χ L hL hEq hχ
    refine ⟨|t| + 1, fun z hz ↦ ha z ?_⟩
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    constructor <;> rintro rfl <;> norm_num at hz
  · exact ⟨0, fun z _ ↦ (completedHeckeL_continuation_entire χ L hL hEq hχ).analyticAt z⟩

/-- A multiple of the regularized completed generator has polynomial growth on strips
and polynomially bounded reciprocal at large height on the imaginary axis. Multiply by
the epsilon factor and the reflected inverse gamma factor. The functional equation then
identifies the result with the pole polynomial times the reflected finite L-function. -/
private theorem strongCoprimality_exists_sub_mem_multiplier (χ : U) (τ : ℝ≥0ˣ →ₜ* I𝔽)
    (hτ : RightInverse τ (ideleNorm F)) :
    let G := regularizedCompletedHeckeL χ τ hτ (continuedCompletedHeckeL χ)
      (continuedCompletedHeckeL_spec χ).1 (continuedCompletedHeckeL_spec χ).2
    ∃ A : ℂ → ℂ, Differentiable ℂ A ∧ (∀ z : ℂ, z.re = 0 → G.val z * A z ≠ 0) ∧
      (∀ R : ℝ, ∃ (k : ℕ) (T : ℝ), ∀ z : ℂ, |z.re| ≤ R → T ≤ |z.im| →
        ‖G.val z * A z‖ ≤ ‖z‖ ^ k) ∧
      ∃ (k : ℕ) (C T : ℝ), ∀ z : ℂ, z.re = 0 → T ≤ |z.im| →
        ‖(G.val z * A z)⁻¹‖ ≤ C * |z.im| ^ k := by
  classical
  intro G
  let L := continuedCompletedHeckeL χ
  let L' := continuedCompletedHeckeL χ⁻¹
  obtain ⟨hL, heL⟩ := continuedCompletedHeckeL_spec χ
  obtain ⟨hL', heL'⟩ := continuedCompletedHeckeL_spec χ⁻¹
  obtain ⟨ε, hε, hε₀, hFE⟩ :=
    completedHeckeL_continuation_functionalEquation χ L L' hL heL hL' heL'
  let Γi (s : ℂ) := (heckeGammaFactor χ⁻¹ s)⁻¹
  have hΓ := differentiable_inv_heckeGammaFactor χ⁻¹
  let raw := Γi * L'
  have hm : MeromorphicOn raw univ :=
    fun s hs ↦ (hΓ.analyticAt s).meromorphicAt.mul (hL' hs).meromorphicAt
  let f := toMeromorphicNFOn raw univ
  have hf := meromorphicNFOn_toMeromorphicNFOn raw univ
  have hfval (s) (hs : AnalyticAt ℂ L' s) : f s = Γi s * L' s := by
    rw [show f s = toMeromorphicNFAt raw s s from toMeromorphicNFOn_eq_toMeromorphicNFAt hm (mem_univ s),
      toMeromorphicNFAt_eq_self.mpr ((hΓ.analyticAt s).mul hs).meromorphicNFAt]
    rfl
  have hseries (s : Complex.re ⁻¹' Ioi (1 : ℝ)) : f s = finiteHeckeL χ⁻¹ s := by
    have hne := heckeGammaFactor_ne_zero_of_re_pos χ⁻¹ (zero_lt_one.trans s.property)
    have hn := (meromorphicNFAt_mul_iff_right (hΓ.analyticAt s) (inv_ne_zero hne)).2 (hL' (mem_univ _))
    rw [show f s = toMeromorphicNFAt raw s s from toMeromorphicNFOn_eq_toMeromorphicNFAt hm (mem_univ _),
      toMeromorphicNFAt_eq_self.mpr hn]
    change (heckeGammaFactor χ⁻¹ s)⁻¹ * L' s = _
    rw [show L' s = completedHeckeL χ⁻¹ s from heL' s]
    simp [completedHeckeL, finiteHeckeL, hne]
  let b := ((existsUnique_ideleNormSection_character_phase χ τ hτ).exists.choose : ℂ) * Complex.I
  let δ : ℕ := if χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1 then 1 else 0
  let polePoly (z : ℂ) := (z + b) ^ δ * (1 - z - b) ^ δ
  have hP : Differentiable ℂ polePoly := by dsimp [polePoly]; fun_prop
  let A (z : ℂ) := ε z * Γi (1 - z)
  have hA : Differentiable ℂ A := hε.mul (hΓ.comp (differentiable_id.const_sub 1))
  obtain ⟨T₁, ha₁⟩ := strongCoprimality_exists_sub_mem_high χ
  obtain ⟨T₂, ha₂⟩ := strongCoprimality_exists_sub_mem_high χ⁻¹
  let T₀ := max T₁ T₂
  have he (z : ℂ) (hz : T₀ ≤ |z.im|) : G.val z * A z = polePoly z * f (1 - z) := by
    have h₁ := ha₁ z ((le_max_left ..).trans hz)
    have h₂ := ha₂ (1 - z) (by simpa using (le_max_right T₁ T₂).trans hz)
    have hPL : MeromorphicOn (polePoly * L) univ :=
      fun w hw ↦ (hP.analyticAt w).meromorphicAt.mul (hL hw).meromorphicAt
    have hG : G.val z = polePoly z * L z := by
      change toMeromorphicNFOn (polePoly * L) univ z = _
      rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hPL (mem_univ z),
        toMeromorphicNFAt_eq_self.mpr ((hP.analyticAt z).mul h₁).meromorphicNFAt]
      rfl
    rw [hG, hfval _ h₂, hFE]
    dsimp only [A]
    ring
  refine ⟨A, hA, fun z hz ↦ mul_ne_zero
    (strongCoprimality_mem_differenceRange_iff_ne_zero_left χ τ hτ z hz.le)
    (mul_ne_zero (hε₀ z) (inv_ne_zero (heckeGammaFactor_ne_zero_of_re_pos χ⁻¹ (by simp [hz])))), ?_, ?_⟩
  · intro R
    let r := |R| + 1
    obtain ⟨M, _, hM⟩ := finiteHeckeL_continuation_isBigO_rpow χ⁻¹ f hf hseries (1 - r) (1 + r)
      (by dsimp [r]; linarith [abs_nonneg R])
    obtain ⟨k, hk⟩ := exists_nat_gt M
    obtain ⟨c, hc⟩ := hM.bound
    simp only [Filter.eventually_inf_principal, Filter.eventually_comap, Filter.eventually_atTop] at hc
    obtain ⟨T, hT⟩ := hc
    refine ⟨2 * δ + 2 * δ + (k + 1), max (max T₀ T) (max c (‖b‖ + 3)), fun z hz ht ↦ ?_⟩
    have h₀ := (le_max_left _ _).trans ht
    have h₁ := (le_max_right _ _).trans ht
    have hbig : ‖b‖ + 3 ≤ ‖z‖ := ((le_max_right _ _).trans h₁).trans (Complex.abs_im_le_norm z)
    have hone : 1 ≤ |z.im| := by linarith [(le_max_right _ _).trans h₁, norm_nonneg b]
    have hs : (1 - z).re ∈ Icc (1 - r) (1 + r) := by
      simp only [Complex.sub_re, Complex.one_re, mem_Icc]
      dsimp [r]
      constructor <;> linarith [(abs_le.mp hz).1, (abs_le.mp hz).2, le_abs_self R]
    have hbound := hT |z.im| ((le_max_right _ _).trans h₀) (1 - z) (by simp) hs
    simp only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg,
      Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)] at hbound
    have hfbound : ‖f (1 - z)‖ ≤ ‖z‖ ^ (k + 1) := by
      calc ‖f (1 - z)‖ ≤ c * |z.im| ^ M := hbound
           _ ≤ |z.im| * |z.im| ^ (k : ℝ) := by gcongr; exact (le_max_left _ _).trans h₁
           _ ≤ ‖z‖ ^ (k + 1) := by rw [Real.rpow_natCast, pow_succ']; gcongr <;> exact Complex.abs_im_le_norm _
    have hs₁ : ‖z + b‖ ≤ ‖z‖ ^ 2 := (norm_add_le ..).trans (by nlinarith [norm_nonneg b])
    have hs₂ : ‖1 - z - b‖ ≤ ‖z‖ ^ 2 := (norm_sub_le ..).trans (by
      have h := norm_sub_le (1 : ℂ) z
      rw [norm_one] at h
      nlinarith [norm_nonneg b])
    rw [he z ((le_max_left _ _).trans h₀)]
    dsimp only [polePoly]
    rw [norm_mul, norm_mul, norm_pow, norm_pow,
      pow_add, pow_add, pow_mul]
    gcongr
  · obtain ⟨_, k, _, hk⟩ := finiteHeckeL_inv_isBigO_oneLine χ⁻¹ f hf hseries
    obtain ⟨C, hC⟩ := hk.bound
    simp only [Filter.eventually_comap, Filter.eventually_atTop] at hC
    obtain ⟨T, hT⟩ := hC
    refine ⟨k, C, max (max T₀ T) (‖b‖ + 3), fun z hz ht ↦ ?_⟩
    have h₀ := (le_max_left _ _).trans ht
    have heq : 1 - z = (⟨1, -z.im⟩ : ℂ) := by apply Complex.ext <;> simp [hz]
    have h := hT |z.im| ((le_max_right _ _).trans h₀) (-z.im) (abs_neg _)
    simp only [abs_neg, Real.norm_of_nonneg (pow_nonneg (abs_nonneg _) _)] at h
    have hbig : ‖b‖ + 3 ≤ ‖z‖ := ((le_max_right _ _).trans ht).trans (Complex.abs_im_le_norm z)
    have hnorm : 1 ≤ ‖polePoly z‖ := by
      dsimp only [polePoly]
      rw [norm_mul, norm_pow, norm_pow]
      apply one_le_mul_of_one_le_of_one_le <;> apply one_le_pow₀
      · have h := norm_sub_le (z + b) b
        rw [add_sub_cancel_right] at h
        linarith
      · have h := norm_sub_le (1 - z - b) (1 - b)
        rw [show 1 - z - b - (1 - b) = -z by ring, norm_neg] at h
        linarith [norm_sub_le (1 : ℂ) b, norm_one (α := ℂ)]
    rw [he z ((le_max_left _ _).trans h₀), heq, mul_inv_rev, norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (by rw [norm_inv]; exact inv_le_one_of_one_le₀ hnorm)).trans h

/-- Interpolate the inverse of a function on a single Euler lattice. Dividing the samples
by a power of `1 - z` makes their norms summable. The cardinal series then gives a bounded
holomorphic interpolant on each strip, and restoring the power recovers the inverse. -/
private theorem strongCoprimality_exists_sub_mem_inverse (H : ℂ → ℂ)
    (hne : ∀ z : ℂ, z.re = 0 → H z ≠ 0)
    (hbound : ∃ (k : ℕ) (C T : ℝ), ∀ z : ℂ, z.re = 0 → T ≤ |z.im| →
      ‖(H z)⁻¹‖ ≤ C * |z.im| ^ k) (c : ℂ) (hc : ‖c‖ = 1) (l : ℝ) (hl : 0 < l) :
    ∃ (k : ℕ) (u : ℂ → ℂ), Differentiable ℂ u ∧
      (∀ R : ℝ, ∃ C : ℝ, ∀ z : ℂ, |z.re| ≤ R → ‖u z‖ ≤ C) ∧
      ∀ z : ℂ, c * Complex.exp (-(l : ℂ) * z) = 1 → H z * (1 - z) ^ k * u z = 1 := by
  obtain ⟨k, C, T, hC⟩ := hbound
  let w (z : ℂ) := Complex.log c - (l : ℂ) * z
  let d := -(2 * Real.pi) / l
  let b := -c.arg / (2 * Real.pi)
  let t (n : ℤ) := d * ((n : ℝ) + b)
  let s (n : ℤ) : ℂ := ⟨0, t n⟩
  have hd : d ≠ 0 := div_ne_zero (neg_ne_zero.mpr Real.two_pi_pos.ne') hl.ne'
  have hw (n : ℤ) : w (s n) = n * (2 * Real.pi * Complex.I) := by
    apply Complex.ext
    · simp [w, s, Complex.log_re, hc]
    · simp [w, s, t, d, b, Complex.log_im, Complex.mul_im]
      field_simp
      ring
  let a (n : ℤ) := (H (s n))⁻¹ / (1 - s n) ^ (k + 2)
  have ha : Summable fun n ↦ ‖a n‖ := by
    have hs := (Real.summable_one_div_int_add_rpow b 2).2 (by norm_num)
    simp only [Real.rpow_two] at hs
    apply (hs.mul_left (C / |d| ^ 2)).of_norm_bounded_eventually
    have hlim : Filter.Tendsto (fun n : ℤ ↦ |(n : ℝ)|) Filter.cofinite Filter.atTop :=
      tendsto_norm_cocompact_atTop.comp Int.tendsto_coe_cofinite
    filter_upwards [hlim.eventually_gt_atTop (|b| + (max T 1) / |d|)] with n hn
    have htd : max T 1 < |t n| := by
      rw [show |t n| = |((n : ℝ) + b)| * |d| by rw [mul_comm]; exact abs_mul ..]
      apply (div_lt_iff₀ (abs_pos.mpr hd)).mp
      have h := abs_sub ((n : ℝ) + b) b
      rw [add_sub_cancel_right] at h
      linarith
    have ht := (le_max_left T 1).trans htd.le
    have hpos : 0 < |t n| := zero_lt_one.trans ((le_max_right ..).trans_lt htd)
    have hnorm : |t n| ≤ ‖1 - s n‖ := by simpa [s] using Complex.abs_im_le_norm (1 - s n)
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    change ‖(H (s n))⁻¹ / (1 - s n) ^ (k + 2)‖ ≤ _
    rw [norm_div, norm_pow]
    calc
      _ ≤ (C * |t n| ^ k) / |t n| ^ (k + 2) :=
        (div_le_div_of_nonneg_left (norm_nonneg _) (pow_pos hpos _)
          (pow_le_pow_left₀ hpos.le hnorm _)).trans
            (div_le_div_of_nonneg_right (hC (s n) rfl ht) (pow_nonneg hpos.le _))
      _ = (C / |d| ^ 2) * (1 / |(n : ℝ) + b| ^ 2) := by
        rw [pow_add, mul_comm (|t n| ^ k), mul_div_mul_right _ _ (pow_ne_zero k hpos.ne')]
        simp [t, abs_mul, mul_pow, div_eq_mul_inv, mul_left_comm, mul_comm]
  obtain ⟨A, hA, hstrip, hval⟩ := strongCoprimality_exists_sub_mem_cardinal a ha
  have hlog : (Complex.log c).re = 0 := by rw [Complex.log_re, hc, Real.log_one]
  refine ⟨k + 2, A ∘ w, hA.comp ((differentiable_const _).sub (differentiable_id.const_mul _)),
    fun R ↦ ?_, fun z hz ↦ ?_⟩
  · obtain ⟨C, hC⟩ := hstrip (l * R)
    refine ⟨C, fun z hz ↦ hC _ ?_⟩
    simpa [w, Complex.mul_re, hlog, abs_mul, abs_of_pos hl] using mul_le_mul_of_nonneg_left hz hl.le
  · have hexp : Complex.exp (w z) = 1 := by
      simpa [w, sub_eq_add_neg, Complex.exp_add,
        Complex.exp_log (norm_ne_zero_iff.mp (hc.trans_ne one_ne_zero))] using hz
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp
    have hzinj : Injective w := fun _ _ h ↦
      mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hl.ne') (sub_right_injective h)
    have hzs := hzinj (hn.trans (hw n).symm)
    rw [hzs, Function.comp_apply, hw, hval]
    have h₁ : (1 : ℂ) - s n ≠ 0 := by intro e; have := congrArg Complex.re e; simp [s] at this
    dsimp only [a]
    field_simp [hne (s n) rfl, h₁]

/-- The entire interpolating multiplier preserves rapid decay on each vertical strip.
Above the height threshold its polynomial growth is absorbed by a higher Schwartz weight.
The remaining rectangle is compact. -/
private theorem strongCoprimality_exists_sub_mem_rapid (H u : ℂ → ℂ)
    (hH : Differentiable ℂ H) (hu : Differentiable ℂ u) (k : ℕ)
    (hpoly : ∀ R : ℝ, ∃ (m : ℕ) (T : ℝ), ∀ z : ℂ, |z.re| ≤ R → T ≤ |z.im| →
      ‖H z‖ ≤ ‖z‖ ^ m) (hb : ∀ R : ℝ, ∃ C : ℝ, ∀ z : ℂ, |z.re| ≤ R → ‖u z‖ ≤ C)
    (φ : B) : (fun z ↦ H z * (1 - z) ^ k * u z * φ.val z) ∈ schwartzBergmanSubmodule univ := by
  let f (z : ℂ) := H z * (1 - z) ^ k * u z * φ.val z
  have hφ : Differentiable ℂ φ.val := differentiableOn_univ.mp (by simpa using φ.property.2.1)
  have hf : Differentiable ℂ f := ((hH.mul ((differentiable_id.const_sub 1).pow k)).mul hu).mul hφ
  refine ⟨fun z hz ↦ (hz (mem_univ _)).elim, hf.differentiableOn, fun a b hab hI N ↦ ?_⟩
  let R := |a| + |b|
  obtain ⟨m, T, hT⟩ := hpoly R
  obtain ⟨C, hC⟩ := hb R
  obtain ⟨Bφ, hBφ⟩ := φ.property.2.2 a b hab hI (N + m + 2 * k)
  obtain ⟨B₀, hB₀⟩ := (isCompact_closedBall (0 : ℂ) (R + max T 3)).exists_bound_of_continuousOn
    (((continuous_id.pow N).mul hf.continuous).continuousOn)
  refine ⟨max B₀ (max C 0 * Bφ), ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  change ‖z ^ N * f z‖ ≤ _
  have hre : |z.re| ≤ R := by
    apply abs_le.mpr
    dsimp [R]
    constructor <;> linarith [hz.1, hz.2, neg_abs_le a, le_abs_self b, abs_nonneg a, abs_nonneg b]
  by_cases ht : max T 3 ≤ |z.im|
  · have hn : 3 ≤ ‖z‖ := ((le_max_right _ _).trans ht).trans (Complex.abs_im_le_norm z)
    have h₁ : ‖1 - z‖ ≤ ‖z‖ ^ 2 := (norm_sub_le ..).trans (by rw [norm_one]; nlinarith)
    have h₂ : ‖z ^ (N + m + 2 * k) * φ.val z‖ ≤ Bφ := hBφ ⟨z, hz, rfl⟩
    apply le_trans _ (le_max_right ..)
    calc
      ‖z ^ N * f z‖ = ‖u z‖ * (‖z‖ ^ N * ‖H z‖ * ‖1 - z‖ ^ k * ‖φ.val z‖) := by
        simp only [f, norm_mul, norm_pow]; ring
      _ ≤ max C 0 * (‖z‖ ^ N * ‖z‖ ^ m * (‖z‖ ^ 2) ^ k * ‖φ.val z‖) := by
        gcongr
        · exact (hC z hre).trans (le_max_left ..)
        · exact hT z hre ((le_max_left ..).trans ht)
      _ = max C 0 * ‖z ^ (N + m + 2 * k) * φ.val z‖ := by rw [norm_mul, norm_pow, pow_add, pow_add, pow_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left h₂ (le_max_right ..)
  · exact (hB₀ z (mem_closedBall_zero_iff.mpr ((Complex.norm_le_abs_re_add_abs_im z).trans
      (add_le_add hre (le_of_not_ge ht))))).trans (le_max_left ..)

/-- The reciprocal Euler factor in exponential coordinates on the Mellin line. -/
private theorem strongCoprimality_exists_sub_mem_factor (χ : U) (v : V)
    (hv : (ideleClassNormTwist χ 0).IsUnramifiedAt v) (z : ℂ) :
    reciprocalPartialHeckeEulerProduct χ {v} z = 1 - (ideleClassNormTwist χ 0).localValue v *
      Complex.exp (-(Real.log (v.asIdeal.absNorm : ℝ) : ℂ) * z) := by
  have hq : (v.asIdeal.absNorm : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr
    (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v)).ne'
  rw [reciprocalPartialHeckeEulerProduct_singleton χ v hv, Complex.cpow_def_of_ne_zero hq,
    ← Complex.natCast_log, mul_neg, neg_mul]

/-- Match the Mellin data of an arbitrary ambient function at all the zeros of one Euler
factor by a pole-free theta transform, including the value at a canceled pole. -/
private theorem strongCoprimality_exists_sub_mem_interpolate (χ : U)
    (τ : ℝ≥0ˣ →ₜ* I𝔽) (hτ : RightInverse τ (ideleNorm F)) (v : V)
    (hv : (ideleClassNormTwist χ 0).IsUnramifiedAt v) (φ : B) :
    ∃ w ∈ spectralNuclearityDenominator χ τ hτ 0, ∀ z : ℂ,
      reciprocalPartialHeckeEulerProduct χ {v} z = 0 → w.val z = φ.val z := by
  let G := regularizedCompletedHeckeL χ τ hτ (continuedCompletedHeckeL χ)
    (continuedCompletedHeckeL_spec χ).1 (continuedCompletedHeckeL_spec χ).2
  obtain ⟨A, hA, hne, hpoly, hinv⟩ := strongCoprimality_exists_sub_mem_multiplier χ τ hτ
  let H (z : ℂ) := G.val z * A z
  let c := (ideleClassNormTwist χ 0).localValue v
  let l := Real.log (v.asIdeal.absNorm : ℝ)
  have hq : (1 : ℝ) < v.asIdeal.absNorm := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hl := Real.log_pos hq
  obtain ⟨k, u, hu, hstrip, hmatch⟩ := strongCoprimality_exists_sub_mem_inverse H hne hinv c
    (norm_ideleClassNormTwist_zero_localValue χ v) l hl
  let w : B :=
    ⟨_, strongCoprimality_exists_sub_mem_rapid H u (G.property.mul hA) hu k hpoly hstrip φ⟩
  refine ⟨w, ?_, fun z hz ↦ ?_⟩
  · rw [spectralNuclearityDenominator, strongCoprimality_mem_differenceRange_iff_divisible]
    have hφ : Differentiable ℂ φ.val := differentiableOn_univ.mp (by simpa using φ.property.2.1)
    refine ⟨fun z ↦ A z * (1 - z) ^ k * u z * φ.val z,
      ((hA.mul ((differentiable_id.const_sub 1).pow k)).mul hu).mul hφ, fun z ↦ ?_⟩
    change G.val z * A z * _ * _ * _ = G.val (z + ((0 : ℝ) : ℂ)) * _
    simp only [Complex.ofReal_zero, add_zero, mul_assoc]
  · rw [strongCoprimality_exists_sub_mem_factor χ v hv] at hz
    exact (congrArg (· * φ.val z) (hmatch z (sub_eq_zero.mp hz).symm)).trans (one_mul _)

/-- Removing the simple zeros of one reciprocal Euler factor gives an entire quotient.
Imaginary periodicity of the factor preserves rapid decay on strips under this division. -/
private theorem strongCoprimality_exists_sub_mem_divide (χ : U) (v : V)
    (hv : (ideleClassNormTwist χ 0).IsUnramifiedAt v) (f : B)
    (hf : ∀ z, reciprocalPartialHeckeEulerProduct χ {v} z = 0 → f.val z = 0) :
    ∃ b : B, ∀ z, f.val z = reciprocalPartialHeckeEulerProduct χ {v} z * b.val z := by
  let q : ℝ := v.asIdeal.absNorm
  let c := (ideleClassNormTwist χ 0).localValue v
  let D := reciprocalPartialHeckeEulerProduct χ {v}
  have hq : 1 < q := by dsimp [q]; exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hq₀ := zero_lt_one.trans hq
  have hlog := Real.log_pos hq
  have hD : D = fun z ↦ 1 - c * Complex.exp (-(Real.log q : ℂ) * z) := by
    funext z
    exact strongCoprimality_exists_sub_mem_factor χ v hv z
  have hd := strongCoprimality_mem_differenceRange_iff_euler χ {v}
  have hfd : Differentiable ℂ f.val := differentiableOn_univ.mp (by simpa using f.property.2.1)
  obtain ⟨b, hb, he⟩ := strongCoprimality_mem_differenceRange_iff_dvd D f.val hd hfd
    (fun z ↦ by
      by_cases hz : D z = 0
      · have hder : deriv D z ≠ 0 := by
          rw [hD]
          apply ((((hasDerivAt_id z).const_mul (-(Real.log q : ℂ))).cexp.const_mul c).const_sub
            1).deriv.trans_ne
          have hc : c ≠ 0 := norm_ne_zero_iff.mp
            ((norm_ideleClassNormTwist_zero_localValue χ v).trans_ne one_ne_zero)
          simp [hc, hlog.ne']
        rw [(hd.analyticAt z).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hz hder]
        exact Order.one_le_iff_ne_zero.mpr ((hfd.analyticAt z).analyticOrderAt_ne_zero.mpr (hf z hz))
      · rw [(hd.analyticAt z).analyticOrderAt_eq_zero.mpr hz]
        exact bot_le)
  let T := 2 * Real.pi / Real.log q
  have hT : 0 < T := div_pos (by positivity) hlog
  have hper : Periodic D ((T : ℂ) * Complex.I) := by
    intro z
    rw [hD]
    have hphase : -(Real.log q : ℂ) * ((T : ℂ) * Complex.I) =
        -(2 * Real.pi * Complex.I) := by
      dsimp [T]
      push_cast
      field_simp [Complex.ofReal_ne_zero.mpr hlog.ne']
    simp only [mul_add, Complex.exp_add, hphase, Complex.exp_neg, Complex.exp_two_pi_mul_I,
      inv_one, mul_one]
  have hne : ∃ z, D z ≠ 0 := by
    refine ⟨1, ?_⟩
    rw [hD]
    apply sub_ne_zero.mpr
    intro h
    have hnorm := congrArg norm h
    simp only [norm_one, norm_mul, c, norm_ideleClassNormTwist_zero_localValue, one_mul,
      mul_one, Complex.norm_exp, Complex.neg_re, Complex.ofReal_re, Real.exp_neg,
      Real.exp_log hq₀] at hnorm
    exact (inv_lt_one_of_one_lt₀ hq).ne' hnorm
  exact ⟨⟨b, schwartzBergman_of_periodic_mul hd hne hT hper hb (funext he ▸ f.property)⟩, he⟩

/-- Successive single-place divisions keep the theta part divisible by the same entire
generator. Each next division acts on the preceding quotient, including at shared zeros. -/
private theorem strongCoprimality_exists_sub_mem_product (χ : U) (τ : ℝ≥0ˣ →ₜ* I𝔽)
    (hτ : RightInverse τ (ideleNorm F)) (T : Finset V)
    (hT : ∀ v ∈ T, (ideleClassNormTwist χ 0).IsUnramifiedAt v) (φ : B) :
    let G := regularizedCompletedHeckeL χ τ hτ (continuedCompletedHeckeL χ)
      (continuedCompletedHeckeL_spec χ).1 (continuedCompletedHeckeL_spec χ).2
    ∃ (b : B) (u : ℂ → ℂ), Differentiable ℂ u ∧ ∀ z, φ.val z =
      G.val z * u z + reciprocalPartialHeckeEulerProduct χ T z * b.val z := by
  classical
  intro G
  induction T using Finset.induction_on generalizing φ with
  | empty => exact ⟨φ, 0, differentiable_const _, by simp [reciprocalPartialHeckeEulerProduct]⟩
  | insert v T hnot ih =>
    have hv := hT v (Finset.mem_insert_self ..)
    obtain ⟨w, hw, hmatch⟩ := strongCoprimality_exists_sub_mem_interpolate χ τ hτ v hv φ
    rw [spectralNuclearityDenominator, strongCoprimality_mem_differenceRange_iff_divisible] at hw
    obtain ⟨a, ha, hwa⟩ := hw
    have hw' (z : ℂ) : w.val z = G.val z * a z := by
      have h : w.val z = G.val (z + ((0 : ℝ) : ℂ)) * a z := hwa z
      simpa only [Complex.ofReal_zero, add_zero] using h
    obtain ⟨d, hd⟩ := strongCoprimality_exists_sub_mem_divide χ v hv (φ - w)
      (fun z hz ↦ sub_eq_zero.mpr (hmatch z hz).symm)
    obtain ⟨b, u, hu, hbu⟩ := ih (fun i hi ↦ hT i (Finset.mem_insert_of_mem hi)) d
    let D := reciprocalPartialHeckeEulerProduct χ {v}
    refine ⟨b, fun z ↦ a z + D z * u z,
      ha.add ((strongCoprimality_mem_differenceRange_iff_euler χ {v}).mul hu), fun z ↦ ?_⟩
    have he : φ.val z - w.val z = D z * d.val z := hd z
    rw [hw', hbu] at he
    simp only [D, reciprocalPartialHeckeEulerProduct, Finset.prod_insert hnot,
      Finset.prod_singleton] at he ⊢
    linear_combination he

open Classical in
/-- Paper: Theorem 7.5.0.1, pp. 375–376.
Every exponentially decaying function of the isotype is the homogeneous theta function of a
pole-free theta class, up to an element of the range of the difference product over the
unramified places of `S`, each difference taken along the inverse class of `π v`. -/
private theorem strongCoprimality_exists_sub_mem (χ : U) (S : Finset V)
    (π : (v : V) → (v.adicCompletion F)ˣ)
    (hπ : ∀ v ∈ S, Valuation.IsUniformizer
      (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))) (π v).val)
    (j : StrongCoprimalityThetaSpace ω(χ) →L[ℂ] StrongCoprimalityDecaySpace ω(χ))
    (hj : ∀ (f : P) (g : C𝔽),
      (j ((K(ω(χ))).mkQ f)).val.val g = homogeneousAdelicThetaLinearMap F ω(χ) f.val g)
    (y : StrongCoprimalityDecaySpace ω(χ)) :
    ∃ x, y - j x ∈ strongCoprimalityDifferenceRange ω(χ)
      (S.filter (fun v ↦ (ideleClassNormTwist χ 0).IsUnramifiedAt v)) π := by
  let T := S.filter (fun v ↦ (ideleClassNormTwist χ 0).IsUnramifiedAt v)
  have hT (v) (hv : v ∈ T) := (Finset.mem_filter.mp hv).2
  have hπT (v) (hv : v ∈ T) := hπ v (Finset.mem_filter.mp hv).1
  let τ : ℝ≥0ˣ →ₜ* I𝔽 := ⟨canonicalIdeleNormSection F, canonicalIdeleNormSection_continuous F⟩
  have hτ : RightInverse τ (ideleNorm F) := canonicalIdeleNormSection_rightInverse F
  obtain ⟨M, hM, hθ⟩ := spectralNuclearityDenominator_isotypeModel χ τ hτ 0
  obtain ⟨b, u, hu, he⟩ := strongCoprimality_exists_sub_mem_product χ τ hτ T hT (M y)
  obtain ⟨d, hd⟩ := strongCoprimality_mem_differenceRange_iff_difference ω(χ) T π (M.symm b)
  have hdiff := strongCoprimality_mem_differenceRange_iff_mellin χ τ hτ T π hπT hT M hM
    (M.symm b) d hd
  have hmem : M (y - d) ∈ spectralNuclearityDenominator χ τ hτ 0 := by
    rw [spectralNuclearityDenominator, strongCoprimality_mem_differenceRange_iff_divisible]
    refine ⟨u, hu, fun z ↦ ?_⟩
    rw [map_sub]
    change (M y).val z - (M d).val z = _
    rw [hdiff, M.apply_symm_apply, he]
    simp
  obtain ⟨f, hf⟩ := (hθ _).mp hmem
  have hjf : y - d = j ((K(ω(χ))).mkQ f) := by
    refine Subtype.ext (Subtype.ext (funext fun g ↦ ?_))
    have h := hf g
    simp only [Real.rpow_zero, Complex.ofReal_one, one_mul] at h
    exact h.trans (hj f g).symm
  refine ⟨(K(ω(χ))).mkQ f, ?_⟩
  rw [← hjf, sub_sub_cancel]
  exact (mem_strongCoprimalityDifferenceRange ω(χ) T π d).mpr ⟨M.symm b, hd⟩

open Classical in
/-- Paper: Theorem 7.5.0.1, p. 374.
The map induced by homogeneous theta is a topological linear isomorphism from the Weil
principal-value quotient to the exponential-decay quotient.
Deviation: The comparison product uses the unramified places of the selected set.
At a ramified place Weil principal value acts as the identity on this isotype. -/
theorem strongCoprimality (χ : U) (S : Finset V)
    (π : (v : V) → (v.adicCompletion F)ˣ)
    (_hπ : ∀ v ∈ S, Valuation.IsUniformizer
      (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))) (π v).val) :
    let ω := ω(χ)
    let j := (exists_strongCoprimalityThetaEmbedding ω).choose
    let D := strongCoprimalityDenominator ω S
    let T := S.filter (fun v ↦ (ideleClassNormTwist χ 0).IsUnramifiedAt v)
    let E := strongCoprimalityDifferenceRange ω T π
    ∃ e : (StrongCoprimalityThetaSpace ω ⧸ D) ≃L[ℂ] (StrongCoprimalityDecaySpace ω ⧸ E),
      ∀ x : StrongCoprimalityThetaSpace ω,
        e (Submodule.Quotient.mk x) = Submodule.Quotient.mk (j x) := by
  intro ω j D T E
  have hspec := (exists_strongCoprimalityThetaEmbedding ω).choose_spec
  have hT : ∀ v ∈ T, Valuation.IsUniformizer
      (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))) (π v).val :=
    fun v hv ↦ _hπ v (Finset.mem_filter.mp hv).1
  have hmod := strongCoprimalityNorm_isModulation_surjective (F := F)
  exact strongCoprimality_quotientEquiv D E (isotype_frechet m𝔽 hmod.1 hmod.2 ω)
    (strongCoprimality_decayQuotient.{_, 0} ω T π hT).2.2 j hspec.1
    (exists_strongCoprimalityThetaEmbedding_isClosed_range ω j hspec.2)
    (strongCoprimality_mem_differenceRange_iff χ S π _hπ j hspec.2)
    (strongCoprimality_exists_sub_mem χ S π _hπ j hspec.2)

private theorem strongCoprimalityDenominator_insert_le_conj_left {E G N : Type*} [AddCommGroup E]
    [Module ℂ E] [TopologicalSpace E] [AddCommGroup G] [Module ℂ G] [TopologicalSpace G]
    [AddCommGroup N] [Module ℂ N] [TopologicalSpace N]
    (e : InductiveTensor E G ≃L[ℂ] N) (T₁ Q R : G →ₗ[ℂ] G) (h : T₁ = Q.comp R) :
    e.toLinearMap.comp ((TensorProduct.map (LinearMap.id : E →ₗ[ℂ] E) T₁).comp
      e.symm.toLinearMap) =
    (e.toLinearMap.comp ((TensorProduct.map (LinearMap.id : E →ₗ[ℂ] E) Q).comp
      e.symm.toLinearMap)).comp
    (e.toLinearMap.comp ((TensorProduct.map (LinearMap.id : E →ₗ[ℂ] E) R).comp
      e.symm.toLinearMap)) := by
  subst h
  refine LinearMap.ext fun x ↦ ?_
  have h := LinearMap.congr_fun (TensorProduct.map_comp (R := ℂ)
    (LinearMap.id : E →ₗ[ℂ] E) Q (LinearMap.id : E →ₗ[ℂ] E) R) (e.symm x)
  rw [LinearMap.id_comp] at h
  exact congrArg e (h.trans (congrArg (TensorProduct.map (LinearMap.id : E →ₗ[ℂ] E) Q)
    (e.symm_apply_apply _).symm))

open scoped TensorProduct in
private theorem strongCoprimalityDenominator_insert_le_piMap {ι : Type*} [Fintype ι] {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)] {p₁ p₂ p₃ : ι → Prop}
    {d₁ : ∀ i, Decidable (p₁ i)} {d₂ : ∀ i, Decidable (p₂ i)} {d₃ : ∀ i, Decidable (p₃ i)}
    {T : ∀ i, M i →ₗ[ℂ] M i} (h : ∀ i, (p₁ i ↔ p₂ i ∨ p₃ i) ∧ ¬ (p₂ i ∧ p₃ i)) :
    (PiTensorProduct.map (fun i ↦ if p₁ i then T i else LinearMap.id) :
        FinestLocallyConvex (⨂[ℂ] i, M i) →ₗ[ℂ] FinestLocallyConvex (⨂[ℂ] i, M i)) =
      (PiTensorProduct.map (fun i ↦ if p₂ i then T i else LinearMap.id) :
        FinestLocallyConvex (⨂[ℂ] i, M i) →ₗ[ℂ] FinestLocallyConvex (⨂[ℂ] i, M i)).comp
      (PiTensorProduct.map (fun i ↦ if p₃ i then T i else LinearMap.id) :
        FinestLocallyConvex (⨂[ℂ] i, M i) →ₗ[ℂ] FinestLocallyConvex (⨂[ℂ] i, M i)) := by
  have hf : (fun i ↦ if p₁ i then T i else LinearMap.id) = fun i ↦
      (if p₂ i then T i else LinearMap.id) ∘ₗ (if p₃ i then T i else LinearMap.id) := by
    funext i
    obtain ⟨h1, h23⟩ := h i
    by_cases a : p₂ i <;> by_cases b : p₃ i
    · exact absurd ⟨a, b⟩ h23
    · rw [ite_eq_left (h1.mpr (Or.inl a)), ite_eq_left a, ite_eq_right b, LinearMap.comp_id]
    · rw [ite_eq_left (h1.mpr (Or.inr b)), ite_eq_right a, ite_eq_left b, LinearMap.id_comp]
    · rw [ite_eq_right (fun c ↦ (h1.mp c).elim a b), ite_eq_right a, ite_eq_right b, LinearMap.id_comp]
  exact (congrArg PiTensorProduct.map hf).trans (PiTensorProduct.map_comp _ _)

open Classical in
private theorem strongCoprimalityDenominator_insert_le_sPV {S' S₁ S₂ S₃ : Finset V}
    (h₁ : S₁ ⊆ S') (h₂ : S₂ ⊆ S') (h₃ : S₃ ⊆ S')
    (h : ∀ w ∈ S', (w ∈ S₁ ↔ w ∈ S₂ ∨ w ∈ S₃) ∧ ¬ (w ∈ S₂ ∧ w ∈ S₃)) :
    sAdelePrincipalValue F h₁ = (sAdelePrincipalValue F h₂).comp (sAdelePrincipalValue F h₃) := by
  unfold sAdelePrincipalValue
  exact strongCoprimalityDenominator_insert_le_conj_left _ _ _ _ (strongCoprimalityDenominator_insert_le_piMap fun w ↦ h w.val w.2)

open scoped TensorProduct in
private theorem strongCoprimalityDenominator_insert_le_conj_right {E G N : Type*} [AddCommGroup E]
    [Module ℂ E] [TopologicalSpace E] [AddCommGroup G] [Module ℂ G] [TopologicalSpace G]
    [AddCommGroup N] [Module ℂ N] [TopologicalSpace N]
    (e : InductiveTensor E G ≃L[ℂ] N) (T₁ Q R : E →ₗ[ℂ] E) (L₁ L₂ L₃ : N →ₗ[ℂ] N)
    (h : T₁ = Q.comp R) (hA : ∀ f g, L₁ (e (f ⊗ₜ[ℂ] g)) = e (T₁ f ⊗ₜ[ℂ] g))
    (hB : ∀ f g, L₂ (e (f ⊗ₜ[ℂ] g)) = e (Q f ⊗ₜ[ℂ] g))
    (hC : ∀ f g, L₃ (e (f ⊗ₜ[ℂ] g)) = e (R f ⊗ₜ[ℂ] g)) :
    L₁ = L₂.comp L₃ := by
  have key : L₁.comp (e.toLinearMap : E ⊗[ℂ] G →ₗ[ℂ] N) =
      (L₂.comp L₃).comp (e.toLinearMap : E ⊗[ℂ] G →ₗ[ℂ] N) := by
    refine TensorProduct.ext' fun f g ↦ ?_
    change L₁ (e (f ⊗ₜ[ℂ] g)) = L₂ (L₃ (e (f ⊗ₜ[ℂ] g)))
    rw [hA, hC, hB, h]
    rfl
  refine LinearMap.ext fun x ↦ ?_
  have hx := LinearMap.congr_fun key (e.symm x)
  change L₁ (e (e.symm x)) = L₂ (L₃ (e (e.symm x))) at hx
  rwa [e.apply_symm_apply] at hx

private theorem strongCoprimalityDenominator_insert_le_PV {S' S₁ S₂ S₃ : Finset V}
    (h₁ : S₁ ⊆ S') (h₂ : S₂ ⊆ S') (h₃ : S₃ ⊆ S')
    (hs : sAdelePrincipalValue F h₁ = (sAdelePrincipalValue F h₂).comp (sAdelePrincipalValue F h₃)) :
    adelePrincipalValue F S₁ = (adelePrincipalValue F S₂).comp (adelePrincipalValue F S₃) :=
  strongCoprimalityDenominator_insert_le_conj_right (sAdeleTailSchwartz_inductiveTensor_equiv F S').choose _ _ _ _ _ _ hs
    (fun f g ↦ adelePrincipalValue_tmul h₁ f g) (fun f g ↦ adelePrincipalValue_tmul h₂ f g)
    (fun f g ↦ adelePrincipalValue_tmul h₃ f g)

private theorem strongCoprimalityDenominator_insert_le_span_le {M X Y : Type*} [AddCommGroup M] [Module ℂ M]
    (a : X → M) (b : Y → M) (h : ∀ x, ∃ y, a x = b y) :
    Submodule.span ℂ (range a) ≤ Submodule.span ℂ (range b) :=
  Submodule.span_mono (by rintro _ ⟨x, rfl⟩; obtain ⟨y, hy⟩ := h x; exact ⟨y, hy.symm⟩)

private theorem strongCoprimalityDenominator_insert_le_final {E M : Type*} [AddCommGroup E]
    [Module ℂ E] [AddCommGroup M] [Module ℂ M] (W : Submodule ℂ E) (π : W → M)
    (L₁ L₂ L₃ : E →ₗ[ℂ] E) (hABC : L₁ = L₂.comp L₃)
    (hA : ∀ f : W, L₁ f.val ∈ W) (hB : ∀ f : W, L₂ f.val ∈ W) (hC : ∀ f : W, L₃ f.val ∈ W) :
    Submodule.span ℂ (range fun f : W ↦ π ⟨L₁ f.val, hA f⟩) ≤
      Submodule.span ℂ (range fun f : W ↦ π ⟨L₂ f.val, hB f⟩) :=
  strongCoprimalityDenominator_insert_le_span_le _ _ fun f ↦
    ⟨⟨L₃ f.val, hC f⟩, congrArg π (Subtype.ext (LinearMap.congr_fun hABC f.val))⟩

open Classical in
/-- Paper: Equation (7.5.0.4), p. 375.
Adding one place shrinks the image of principal value, so its image is a submodule
of the image for the original set of places. -/
theorem strongCoprimalityDenominator_insert_le (ω : PontryaginDual C₁) (S : Finset V) (v : V) :
    strongCoprimalityDenominator ω (insert v S) ≤ strongCoprimalityDenominator ω S := by
  have hPV : ∃ C : _ →ₗ[ℂ] _,
      adelePrincipalValue F (insert v S) = (adelePrincipalValue F S).comp C ∧
      ∀ f : P, C f.val ∈ P := by
    by_cases hv : v ∈ S
    · exact ⟨LinearMap.id, (congrArg (adelePrincipalValue F) (Finset.insert_eq_of_mem hv)).trans
        (LinearMap.comp_id _).symm, fun f ↦ f.2⟩
    · have hdis : ∀ w ∈ insert v S, (w ∈ insert v S ↔ w ∈ S ∨ w ∈ ({v} : Finset V)) ∧
          ¬ (w ∈ S ∧ w ∈ ({v} : Finset V)) := fun w _ ↦
        ⟨by rw [Finset.mem_insert, Finset.mem_singleton, or_comm], fun ⟨a, b⟩ ↦
          hv (Finset.mem_singleton.mp b ▸ a)⟩
      have h₁ : insert v S ⊆ insert v S := Finset.Subset.refl _
      have h₂ : S ⊆ insert v S := Finset.subset_insert v S
      have h₃ : ({v} : Finset V) ⊆ insert v S :=
        Finset.singleton_subset_iff.mpr (Finset.mem_insert_self v S)
      have hs := strongCoprimalityDenominator_insert_le_sPV (F := F) h₁ h₂ h₃ hdis
      have hPV := strongCoprimalityDenominator_insert_le_PV h₁ h₂ h₃ hs
      exact ⟨adelePrincipalValue F {v}, hPV, strongCoprimalityPrincipalValue_mem_polar {v}⟩
  obtain ⟨C, hC, hCP⟩ := hPV
  unfold strongCoprimalityDenominator
  have key := strongCoprimalityDenominator_insert_le_final (P)
    (Submodule.Quotient.mk : _ → StrongCoprimalityThetaSpace ω) _ _ C hC
    (strongCoprimalityPrincipalValue_mem_polar (insert v S))
    (strongCoprimalityPrincipalValue_mem_polar S) hCP
  with_reducible_and_instances exact key

open Classical in
/-- Paper: Equation (7.5.0.4), p. 375.
The layer for one added place is the quotient of the current principal-value image
by the image after applying principal value at that place as well.

Kept as an `abbrev` for now (#5398): as a `def` with its own instances it breaks proofs and
statements that use it, see the issue. Do not copy this pattern: a new type synonym with
structure is a `def` with its own instances (`AGENTS.md`). -/
abbrev StrongCoprimalityLayer (ω : PontryaginDual C₁) (S : Finset V) (v : V) :=
  let D := strongCoprimalityDenominator ω S
  D ⧸ (strongCoprimalityDenominator ω (insert v S)).comap D.subtype

open Classical in
/-- Paper: Equation (7.5.0.4), p. 375.
A vector in the current principal-value image vanishes in the layer exactly when it
belongs to the image after adding the new place. -/
theorem strongCoprimalityLayer_mk_eq_zero (ω : PontryaginDual C₁) (S : Finset V) (v : V)
    (x : strongCoprimalityDenominator ω S) :
    (Submodule.Quotient.mk x : StrongCoprimalityLayer ω S v) = 0 ↔
      x.val ∈ strongCoprimalityDenominator ω (insert v S) :=
  Submodule.Quotient.mk_eq_zero
    ((strongCoprimalityDenominator ω (insert v S)).comap
      (strongCoprimalityDenominator ω S).subtype)

-- TODO(paper-gap): The references to (8.1.0.4), (8.1.0.5), (8.1.0.7), and
-- (8.1.0.8) in the proof point to local formulas (7.5.0.5), (7.5.0.6),
-- (7.5.0.7), and (7.5.0.11), respectively.

-- TODO(paper-gap): In the injectivity argument on pp. 375–376 the pulled-back
-- functionals must separate the source quotient. A biorthogonal family alone
-- gives no such separation. In theta space H with comparison map j the required
-- identity is j⁻¹(range Δ) = PV(H), for the product on the unramified places.

variable (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
  (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F) (hτ : RightInverse τ (ideleNorm F))

/-- Paper: Equation (7.5.0.8), p. 377.
The reflected Fourier jet is the derivative evaluation of the global Mellin transform at
the original spectral point, with the sign from reflection in odd orders.
Deviation: The functional is on the zero-moment quotient from (7.5.0.1), where the
global Mellin transform is entire. -/
def strongCoprimalityFourierJet (s : ℂ) (k : ℕ) : StrongDual ℂ (StrongCoprimalityThetaSpace (ω(χ))) :=
  (-1 : ℂ) ^ k • ((entireJet s k).comp
    (schwartzBergmanEntireInclusion.comp (exists_globalPolarThetaMellin χ τ hτ).choose))

/-- Paper: Equation (7.5.0.8), p. 377.
On a zero-moment representative, the reflected jet evaluates the k-th complex derivative
of the Fourier-transformed global zeta function at 1 − s. This zeta function is entire.
Deviation: Entireness uses the two zero moments, which the Fourier transform exchanges. -/
theorem strongCoprimalityFourierJet_mk (s : ℂ) (k : ℕ) (f : P) :
    let Z := fun z ↦ globalIdelicZFunction (adeleSchwartzFourier f.val)
      (ideleClassNormTwist χ⁻¹ z)
    Differentiable ℂ Z ∧
      strongCoprimalityFourierJet χ τ hτ s k ((K(ω(χ))).mkQ f) = iteratedDeriv k Z (1 - s) := by
  let Z := fun z ↦ globalIdelicZFunction (adeleSchwartzFourier f.val) (ideleClassNormTwist χ⁻¹ z)
  let G := fun z ↦ globalIdelicZFunction f.val (ideleClassNormTwist χ z)
  have href : Z = fun z ↦ G (1 - z) := by
    funext z
    have hz := globalIdelicZFunction_functionalEquation f.val (ideleClassNormTwist χ (1 - z))
    rw [dualQuasiCharacter_ideleClassNormTwist, sub_sub_cancel] at hz
    exact hz.symm
  have hG : Differentiable ℂ G := globalIdelicZFunction_entire_of_vanishing f.val f.property χ
  change Differentiable ℂ Z ∧ _ = iteratedDeriv k Z (1 - s)
  constructor
  · rw [href]
    exact hG.comp ((differentiable_const (c := (1 : ℂ))).sub differentiable_id)
  · let M := (exists_globalPolarThetaMellin χ τ hτ).choose
    have he : ((schwartzBergmanEntireInclusion (M ((K(ω(χ))).mkQ f))).val : ℂ → ℂ) = G := by
      funext z
      rw [schwartzBergmanEntireInclusion_apply]
      exact ((exists_globalPolarThetaMellin χ τ hτ).choose_spec f z).2
    change (-1 : ℂ) ^ k • iteratedDeriv k
      ((schwartzBergmanEntireInclusion (M ((K(ω(χ))).mkQ f))).val : ℂ → ℂ) s = _
    rw [he, href, iteratedDeriv_comp_const_sub]
    simp only [sub_sub_cancel]

/-- The reflected zeta function of a Fourier transformed test is analytic at the evaluation
point of an imaginary-axis center, away from the exceptional center of the norm twist. -/
private theorem exists_strongCoprimalityFourierJet_full_analytic (s : ℂ) (hs : s.re = 0)
    (hc : ideleClassNormTwist χ s ≠ 1) (f : SchwartzBruhat (Multiplicative (𝔸[F]))) :
    AnalyticAt ℂ (fun z ↦ globalIdelicZFunction (adeleSchwartzFourier f)
      (ideleClassNormTwist χ⁻¹ z)) (1 - s) := by
  have hne1 : ideleClassNormTwist χ⁻¹ (1 - s) ≠ 1 := by
    intro h
    have habs : (1 - s).re = 0 := by
      rw [← quasiCharacterAbscissa_ideleClassNormTwist χ⁻¹ (1 - s), h]
      simp [quasiCharacterAbscissa]
    rw [Complex.sub_re, Complex.one_re, hs] at habs
    norm_num at habs
  have hne2 : ideleClassNormTwist χ⁻¹ (1 - s) ≠ ideleClassNormTwist (1 : U) 1 := by
    intro h
    apply hc
    ext g
    have hg := DFunLike.congr_fun h g
    set N : ℂ := (((ideleClassNorm F g : NNReal) : ℝ) : ℂ) with hNdef
    change (Circle.coeHom ((χ⁻¹ : U) g)) * N ^ (1 - s) = 1 * N ^ (1 : ℂ) at hg
    change (Circle.coeHom (χ g)) * N ^ s = 1
    have hinv : Circle.coeHom ((χ⁻¹ : U) g) = (Circle.coeHom (χ g))⁻¹ := rfl
    rw [hinv, Complex.cpow_one, one_mul] at hg
    have hN : N ≠ 0 := by
      rw [hNdef]
      exact_mod_cast (ideleClassNorm F g).ne_zero
    have hNs : N ^ s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hN)
    rw [Complex.cpow_sub _ _ hN, Complex.cpow_one, div_eq_mul_inv] at hg
    have h2 : (Circle.coeHom (χ g))⁻¹ = N ^ s := by
      have h1 : (Circle.coeHom (χ g))⁻¹ * (N ^ s)⁻¹ = 1 := by
        refine mul_right_cancel₀ hN ?_
        calc (Circle.coeHom (χ g))⁻¹ * (N ^ s)⁻¹ * N
            = (Circle.coeHom (χ g))⁻¹ * (N * (N ^ s)⁻¹) := by ring
          _ = N := hg
          _ = 1 * N := (one_mul N).symm
      calc (Circle.coeHom (χ g))⁻¹ = (Circle.coeHom (χ g))⁻¹ * ((N ^ s)⁻¹ * N ^ s) := by
              rw [inv_mul_cancel₀ hNs, mul_one]
        _ = (Circle.coeHom (χ g))⁻¹ * (N ^ s)⁻¹ * N ^ s := by ring
        _ = 1 * N ^ s := by rw [h1]
        _ = N ^ s := one_mul _
    rw [← h2]
    exact mul_inv_cancel₀ (Circle.coe_ne_zero (χ g))
  exact (globalIdelicZFunction_poles (adeleSchwartzFourier f) χ⁻¹).1 (1 - s) ⟨hne1, hne2⟩

/-- Paper: Equation (7.5.0.8), p. 377.
The reflected jet, read on the full homogeneous theta space, is a continuous linear
functional taking a test to the corresponding derivative of its reflected zeta function. -/
private theorem exists_strongCoprimalityFourierJet_full_functional (s : ℂ) (hs : s.re = 0)
    (hc : ideleClassNormTwist χ s ≠ 1) (k : ℕ) :
    let q := (LinearMap.ker (homogeneousAdelicThetaLinearMap F (ω(χ)))).mkQ
    ∃ d : StrongDual ℂ (GlobalHomogeneousThetaSpace F (ω(χ))),
      ∀ f : SchwartzBruhat (Multiplicative (𝔸[F])),
        d (q f) = iteratedDeriv k (fun z ↦ globalIdelicZFunction (adeleSchwartzFourier f)
          (ideleClassNormTwist χ⁻¹ z)) (1 - s) := by
  classical
  intro q
  let E := GlobalHomogeneousThetaSpace F (ω(χ))
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  let : BarrelledSpace ℂ E := (globalHomogeneousThetaSpace_montel (F := F) (ω := ω(χ))).1
  let c := ideleClassNormTwist χ
  let N := ideleClassNormTwist (1 : U) 1
  let regularSet := (c ⁻¹' ({1, N} : Set (QuasiCharacter C𝔽)))ᶜ
  have hi : Injective c := by
    intro z w he
    apply trivial_normTwist_injective (F := F)
    ext g
    have h := DFunLike.congr_fun he g
    change (χ g : ℂ) * _ ^ z = (χ g : ℂ) * _ ^ w at h
    change 1 * ((((ideleClassNorm F g).val : ℝ) : ℂ) ^ z) =
      1 * ((((ideleClassNorm F g).val : ℝ) : ℂ) ^ w)
    exact congrArg (1 * ·) (mul_left_cancel₀ (Circle.coe_ne_zero _) h)
  have ho : IsOpen regularSet := (((Set.finite_singleton N).insert 1).preimage hi.injOn).isClosed.isOpen_compl
  have hnot (z : ℂ) (hz : z ∈ regularSet) : c z ≠ 1 ∧ c z ≠ N := not_or.mp hz
  have hreg : s ∈ regularSet := by
    refine not_or.mpr ⟨hc, fun he ↦ ?_⟩
    have h := congrArg (quasiCharacterAbscissa (ideleClassNorm F) (isProperMap_ideleClassNorm F)
      (ideleClassNorm_ne_one (F := F))) he
    change quasiCharacterAbscissa _ _ _ (ideleClassNormTwist χ s) =
      quasiCharacterAbscissa _ _ _ (ideleClassNormTwist (1 : U) 1) at h
    rw [quasiCharacterAbscissa_ideleClassNormTwist, quasiCharacterAbscissa_ideleClassNormTwist, hs] at h
    norm_num at h
  let Z (f : SchwartzBruhat (Multiplicative (𝔸[F]))) (z : ℂ) := globalIdelicZFunction f (c z)
  have hev (z : ℂ) (hz : z ∈ regularSet) : ∃ l : StrongDual ℂ E, ∀ f, l (q f) = Z f z := by
    let Ω := {d : QuasiCharacter C𝔽 // ∀ h : C₁, d h.val = (ω(χ) h : ℂ)}
    let v : Ω := ⟨c z, fun h ↦ by
      change (χ h.val : ℂ) * (((ideleClassNorm F h.val).val : ℝ) : ℂ) ^ z = _
      have ht : (((ideleClassNorm F h.val).val : ℝ) : ℂ) = 1 := by rw [h.property]; rfl
      rw [ht, Complex.one_cpow, mul_one]
      rfl⟩
    let a : {d : Ω // 0 ≤ globalIdelicOrderBound d.val} := ⟨v, by
      change 0 ≤ globalIdelicOrderBound (c z)
      simp [globalIdelicOrderBound, (hnot z hz).1, (hnot z hz).2, N]⟩
    obtain ⟨M, _, hM⟩ := exists_globalHomogeneousThetaMellin (F := F) (ω(χ))
    let A := meromorphicNormOneComponent (ideleClassNorm F) (isProperMap_ideleClassNorm F).continuous
      (ω(χ)) (globalIdelicOrderBound (F := F))
    refine ⟨(ContinuousMap.evalCLM ℂ a).comp (A.subtypeL.comp M), fun f ↦ ?_⟩
    exact (hM f a).trans (globalIdelicMellin_apply f _)
  have hq : Surjective q := Submodule.mkQ_surjective _
  choose r hr using hq
  let Φ (x : E) := Z (r x)
  have ha (x : E) : AnalyticOnNhd ℂ (Φ x) regularSet :=
    fun z hz ↦ (globalIdelicZFunction_poles (r x) χ).1 z (hnot z hz)
  have hΦ (x : E) (z : ℂ) (hz : z ∈ regularSet) :
      (hev z hz).choose x = Φ x z := (congrArg (hev z hz).choose (hr x).symm).trans ((hev z hz).choose_spec (r x))
  obtain ⟨d, hd⟩ := exists_continuousLinearMap_iteratedDeriv_of_analytic Φ ho ha
    (fun z hz ↦ ⟨(hev z hz).choose, fun x ↦ hΦ x z hz⟩) k s hreg
  refine ⟨(-1 : ℂ) ^ k • d, fun f ↦ ?_⟩
  have hfun : Φ (q f) =ᶠ[𝓝 s] Z f :=
    Filter.mem_of_superset (ho.mem_nhds hreg) fun z hz ↦ (hΦ (q f) z hz).symm.trans ((hev z hz).choose_spec f)
  have hrefl : (fun z ↦ globalIdelicZFunction (adeleSchwartzFourier f) (ideleClassNormTwist χ⁻¹ z)) =
      fun z ↦ Z f (1 - z) := by
    funext z
    have h := globalIdelicZFunction_functionalEquation f (ideleClassNormTwist χ (1 - z))
    rw [dualQuasiCharacter_ideleClassNormTwist, sub_sub_cancel] at h
    exact h.symm
  change (-1 : ℂ) ^ k • d (q f) = _
  rw [hd, hfun.iteratedDeriv_eq k, hrefl, iteratedDeriv_comp_const_sub]
  dsimp only
  rw [sub_sub_cancel]

/-- Paper: Equation (7.5.0.8), p. 377.
At each regular center on the imaginary axis the reflected jet is defined on
the full homogeneous theta space and restricts to the jet on polar tests.
Deviation: The trivial quasi-character is the exceptional center on this axis. -/
theorem exists_strongCoprimalityFourierJet_full (s : ℂ) (_hs : s.re = 0)
    (_hc : ideleClassNormTwist χ s ≠ 1) (k : ℕ) :
    let q := (LinearMap.ker (homogeneousAdelicThetaLinearMap F (ω(χ)))).mkQ
    ∃ d : StrongDual ℂ (GlobalHomogeneousThetaSpace F (ω(χ))),
      (∀ f : SchwartzBruhat (Multiplicative (𝔸[F])),
        let Z := fun z ↦ globalIdelicZFunction (adeleSchwartzFourier f)
          (ideleClassNormTwist χ⁻¹ z)
        AnalyticAt ℂ Z (1 - s) ∧ d (q f) = iteratedDeriv k Z (1 - s)) ∧
      ∀ f : P, d (q f.val) =
        strongCoprimalityFourierJet χ τ hτ s k ((K(ω(χ))).mkQ f) := by
  obtain ⟨d, hd⟩ := exists_strongCoprimalityFourierJet_full_functional (F := F) χ s _hs _hc k
  refine ⟨d, ?_, ?_⟩
  · intro f
    exact ⟨exists_strongCoprimalityFourierJet_full_analytic (F := F) χ s _hs _hc f, hd f⟩
  · intro f
    exact (hd f.val).trans (strongCoprimalityFourierJet_mk (F := F) χ τ hτ s k f).2.symm

-- In the proof on pp. 376–377 one can enlarge S to contain the primes of
-- the different and all places above each rational prime occurring in S
-- (saturation in §7.3). Then the outside indicators are self-dual and
-- the outside unit masses are one. The local-to-global quotient in (7.5.0.16)
-- itself only needs the hypotheses in its statement below.

/-- Paper: Equation (7.5.0.13), p. 378.
Multiplication by a factor holomorphic at the reflected point acts on unnormalized
derivatives by an upper-triangular binomial matrix. For the regular blocks the
factor is the outside Euler product of the conjugate character when S contains
all primes of the different. Both sets of raw derivatives here use the reflected variable.
Deviation: A block of size N has indices 0 through N − 1, as in (7.5.0.11). -/
def strongCoprimalityJetMatrix (S : Finset V)
    (hS : ideleClassNormTwist χ⁻¹ 0 ∈ unramifiedOutside F S) (s : ℂ)
    (_hL : AnalyticAt ℂ (heckeEulerProductOutside S χ⁻¹ hS) (1 - s)) (N : ℕ) :
    Matrix (Fin N) (Fin N) ℂ :=
  let L := heckeEulerProductOutside S χ⁻¹ hS
  fun m k ↦
    if m ≤ k then (k.val.choose m.val : ℂ) * iteratedDeriv (k.val - m.val) L (1 - s) else 0

/-- Paper: Equation (7.5.0.13), p. 378.
The diagonal entries of the derivative matrix are the value of the multiplier at the
reflected point, so the determinant is that value raised to the block size. -/
theorem strongCoprimalityJetMatrix_det (S : Finset V)
    (hS : ideleClassNormTwist χ⁻¹ 0 ∈ unramifiedOutside F S) (s : ℂ)
    (hL : AnalyticAt ℂ (heckeEulerProductOutside S χ⁻¹ hS) (1 - s)) (N : ℕ) :
    (strongCoprimalityJetMatrix χ S hS s hL N).det =
      heckeEulerProductOutside S χ⁻¹ hS (1 - s) ^ N := by
  rw [Matrix.det_of_isUpperTriangular]
  · simp [strongCoprimalityJetMatrix, Finset.prod_const]
  · intro i j hij
    simp [strongCoprimalityJetMatrix, not_le.mpr (show j < i from hij)]

/-- The reciprocal finite Euler polynomial is entire and nonzero to the right
of the imaginary axis. -/
theorem strongCoprimalityJetMatrix_det_ne_zero_euler
    {F : Type*} [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    (∀ z : ℂ, AnalyticAt ℂ (reciprocalPartialHeckeEulerProduct χ S) z) ∧
      ∀ z : ℂ, 0 < z.re → reciprocalPartialHeckeEulerProduct χ S z ≠ 0 := by
  classical
  have hfactor (v : HeightOneSpectrum (𝓞 F)) (z : ℂ) :
      AnalyticAt ℂ (fun w ↦ (finiteHeckeEulerFactor χ v w)⁻¹) z ∧
        (0 < z.re → (finiteHeckeEulerFactor χ v z)⁻¹ ≠ 0) := by
    by_cases hv : (ideleClassNormTwist χ 0).IsUnramifiedAt v
    · have hq : 1 < (v.asIdeal.absNorm : ℝ) := by
        exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
      have hq0 : (v.asIdeal.absNorm : ℂ) ≠ 0 := by
        exact_mod_cast (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v)).ne'
      simp only [finiteHeckeEulerFactor, ite_eq_left hv, inv_inv]
      constructor
      · have hc : Differentiable ℂ (fun w : ℂ ↦ (v.asIdeal.absNorm : ℂ) ^ (-w)) :=
          differentiable_id.neg.const_cpow (Or.inl hq0)
        exact ((hc.const_mul ((ideleClassNormTwist χ 0).localValue v)).const_sub 1).analyticAt z
      · intro hz hzero
        have hlt : ‖(ideleClassNormTwist χ 0).localValue v *
            (v.asIdeal.absNorm : ℂ) ^ (-z)‖ < 1 := by
          rw [norm_mul, norm_ideleClassNormTwist_zero_localValue, one_mul,
            ← Complex.ofReal_natCast,
            Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hq), Complex.neg_re]
          exact Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith)
        have he := (sub_eq_zero.mp hzero).symm
        exact hlt.ne (by rw [he, norm_one])
    · simp only [finiteHeckeEulerFactor, ite_eq_right hv, inv_one]
      exact ⟨analyticAt_const, fun _ ↦ one_ne_zero⟩
  constructor
  · intro z
    exact S.analyticAt_fun_prod (fun v _ ↦ (hfactor v z).1)
  · intro z hz
    exact Finset.prod_ne_zero_iff.mpr (fun v _ ↦ (hfactor v z).2 hz)

/-- The boundary line of absolute convergence lies in the existing zero-free region. -/
private theorem strongCoprimalityJetMatrix_det_ne_zero_order
    {F : Type*} [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (L : ℂ → ℂ)
    (hNF : MeromorphicNFOn L univ)
    (hSeries : ∀ z : Complex.re ⁻¹' Ioi (1 : ℝ), L z = finiteHeckeL χ z)
    (z : ℂ) (hz : z.re = 1) : meromorphicOrderAt L z ≤ 0 := by
  obtain ⟨A, hA, hfield⟩ := finiteHeckeL_zeroFreeRegion
  obtain ⟨scale, hB, hbound⟩ := hfield F χ
  apply hbound L hNF hSeries z
  have hlog : 0 ≤ Real.log (scale * (|z.im| + 3)) := by
    apply Real.log_nonneg
    have hBpos : 0 < scale := by linarith
    nlinarith [mul_nonneg hBpos.le (abs_nonneg z.im)]
  rw [hz]
  exact sub_le_self _ (div_nonneg hA.le (mul_nonneg (by positivity) hlog))

/-- Paper: Equation (7.5.0.13), p. 378.
The regular block is invertible at a spectral point on the imaginary axis.
Deviation: At the exceptional pole of a norm twist the regular-block hypothesis fails. -/
theorem strongCoprimalityJetMatrix_det_ne_zero (S : Finset V)
    (hS : ideleClassNormTwist χ⁻¹ 0 ∈ unramifiedOutside F S) (s : ℂ) (_hs : s.re = 0)
    (hL : AnalyticAt ℂ (heckeEulerProductOutside S χ⁻¹ hS) (1 - s)) (N : ℕ) :
    (strongCoprimalityJetMatrix χ S hS s hL N).det ≠ 0 := by
  rw [strongCoprimalityJetMatrix_det]
  apply pow_ne_zero
  let r : ℂ := 1 - s
  have hr : r.re = 1 := by simp only [r, Complex.sub_re, Complex.one_re, _hs, sub_zero]
  obtain ⟨L, hNF, hSeries⟩ := finiteHeckeL_exists_continuation χ⁻¹
  obtain ⟨hP, hPne⟩ := strongCoprimalityJetMatrix_det_ne_zero_euler χ⁻¹ S
  have hM : MeromorphicOn
      (fun z ↦ reciprocalPartialHeckeEulerProduct χ⁻¹ S z * L z) univ :=
    fun z hz ↦ (hP z).meromorphicAt.mul (hNF hz).meromorphicAt
  have horder : meromorphicOrderAt (heckeEulerProductOutside S χ⁻¹ hS) r =
      meromorphicOrderAt L r := by
    rw [heckeEulerProductOutside_eq_finite S χ⁻¹ hS L hNF hSeries,
      meromorphicOrderAt_toMeromorphicNFOn hM (mem_univ r)]
    exact meromorphicOrderAt_mul_of_ne_zero (hP r) (hPne r (by rw [hr]; norm_num))
  apply (hL.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff).mp
  apply le_antisymm _ hL.meromorphicOrderAt_nonneg
  change meromorphicOrderAt (heckeEulerProductOutside S χ⁻¹ hS) r ≤ 0
  rw [horder]
  exact strongCoprimalityJetMatrix_det_ne_zero_order χ⁻¹ L hNF hSeries r hr

local notation "Vℚ" => HeightOneSpectrum (𝓞 ℚ)

/-- Paper: Remark 7.5.0.2 and Equation (7.5.0.15), p. 378.
At the places above one rational prime the denominator agrees with the
primary denominator of §7.4. -/
theorem strongCoprimalityDenominator_primary (p : Vℚ) :
    let T := (finite_nuclearityPlacesAbove (F := F) p).toFinset
    strongCoprimalityDenominator (ω(χ)) T = finiteNuclearityDenominator χ p := by
  unfold strongCoprimalityDenominator finiteNuclearityDenominator
  with_reducible rfl

/-- A norm-one character extends by projecting along a section of the class norm. -/
private theorem strongCoprimalityPrimaryQuotient_lift (ω : PontryaginDual C₁) :
    ∃ χ : U, ω(χ) = ω := by
  have hmod := strongCoprimalityNorm_isModulation_surjective (F := F)
  obtain ⟨σ, hσ⟩ := exists_surjectiveModulation_section m𝔽 hmod.1 hmod.2
  have hk (g : C𝔽) : g / σ (m𝔽 g) ∈ (ideleClassNorm F).ker := by
    change (ideleClassNorm F) (g / σ (m𝔽 g)) = 1
    rw [map_div, show ideleClassNorm F (σ (m𝔽 g)) = m𝔽 g from hσ (m𝔽 g)]
    change (ideleClassNorm F g) / (ideleClassNorm F g) = 1
    exact div_self' _
  let q : C𝔽 →ₜ* C₁ :=
    { toFun := fun g ↦ ⟨g / σ (m𝔽 g), hk g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun g h ↦ Subtype.ext (by simp [mul_div_mul_comm])
      continuous_toFun := (continuous_id.div' (σ.continuous.comp (m𝔽).continuous)).subtype_mk hk }
  refine ⟨ω.comp q, ?_⟩
  ext1 u
  change ω (q u) = ω u
  congr 1
  apply Subtype.ext
  change u.val / σ ((ideleClassNorm F) u.val) = u.val
  rw [u.property, map_one, div_one]

/-- The comparison denominator is an expanding difference-product range, whose quotient
is separable, nuclear, and Fréchet. -/
private theorem strongCoprimalityPrimaryQuotient_decay (ω : PontryaginDual C₁) (S : Finset V)
    (π : (v : V) → (v.adicCompletion F)ˣ)
    (hπ : ∀ v ∈ S, Valuation.IsUniformizer
      (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))) (π v).val) :
    let X := StrongCoprimalityDecaySpace ω ⧸ strongCoprimalityDifferenceRange ω S π
    TopologicalSpace.SeparableSpace X ∧ IsNuclearTVS X ∧ IsFrechetTVS X := by
  classical
  have hmod := strongCoprimalityNorm_isModulation_surjective (F := F)
  let a := fun v : V ↦ (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v (π v))⁻¹
  let gs := S.toList.map a
  have hgs : ∀ g ∈ gs, 1 < (m𝔽 g).val := by
    rintro g hg
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hg
    have hu := hπ v (Finset.mem_toList.mp hv)
    change (1 : ℝ≥0) < ((ideleClassNorm F ((IdeleClassGroup.ofAdicCompletion (𝓞 F) F v (π v))⁻¹)).val)
    rw [map_inv, ideleClassNorm_ofAdicCompletion]
    rw [Units.coe_map_inv]
    change (1 : ℝ≥0) < ‖((π v)⁻¹).val‖₊
    apply NNReal.coe_lt_coe.mp
    simp only [NNReal.coe_one, coe_nnNorm, Units.val_inv_eq_inv_val, norm_inv]
    rw [norm_uniformizer_adicCompletion v _ hu, inv_inv]
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have heq : strongCoprimalityDifferenceRange ω S π =
      fullDecayDifferenceRange m𝔽 hmod.1 hmod.2 ω gs := by
    rw [fullDecayDifferenceRange_eq_span]
    unfold strongCoprimalityDifferenceRange
    congr 1
    ext h
    simp only [gs, List.foldr_map, a, strongCoprimalityDifference]
  rw [heq]
  exact modulatedIsotypicDifferenceProduct_quotient m𝔽 hmod.1 hmod.2 ω gs hgs

/-- The strong-coprimality equivalence transfers the nuclear Fréchet structure from its
difference quotient. -/
private theorem strongCoprimalityPrimaryQuotient_character (χ : U) (S : Finset V) :
    IsFrechetTVS (StrongCoprimalityQuotient ω(χ) S) ∧
      IsNuclearTVS (StrongCoprimalityQuotient ω(χ) S) := by
  classical
  have h (v : V) := (Valued.v : Valuation (v.adicCompletion F)
    (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
  let π : (v : V) → (v.adicCompletion F)ˣ := fun v ↦ Units.mk0 (h v).choose (h v).choose_spec.ne_zero
  have hπ (v : V) : Valuation.IsUniformizer
      (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))) (π v).val :=
    (h v).choose_spec
  let T := S.filter (fun v ↦ (ideleClassNormTwist χ 0).IsUnramifiedAt v)
  have hp := strongCoprimalityPrimaryQuotient_decay ω(χ) T π (fun v _ ↦ hπ v)
  let e := (strongCoprimality χ S π (fun v _ ↦ hπ v)).choose
  have ht := separable_nuclear_frechet_of_equiv e.symm hp
  exact ⟨ht.2.2, ht.2.1⟩

/-- Paper: Remark 7.5.0.2 and Equation (7.5.0.15), p. 378.
The primary principal-value quotient is a Hausdorff nuclear Fréchet space. -/
theorem strongCoprimalityPrimaryQuotient_nuclearFrechet (ω : PontryaginDual C₁) (p : Vℚ) :
    let T := (finite_nuclearityPlacesAbove (F := F) p).toFinset
    IsFrechetTVS (StrongCoprimalityQuotient ω T) ∧ IsNuclearTVS (StrongCoprimalityQuotient ω T) := by
  let h := strongCoprimalityPrimaryQuotient_lift ω
  let χ := h.choose
  have hχ : ω(χ) = ω := h.choose_spec
  exact (congrArg (fun η ↦ IsFrechetTVS (StrongCoprimalityQuotient η
    (finite_nuclearityPlacesAbove (F := F) p).toFinset) ∧
      IsNuclearTVS (StrongCoprimalityQuotient η (finite_nuclearityPlacesAbove (F := F) p).toFinset))
    hχ).mp (strongCoprimalityPrimaryQuotient_character χ _)

/-- A linear equivalence preserves infinite-dimensionality. -/
private theorem not_finiteDimensional_iff_of_linearEquiv {X Y : Type*} [AddCommGroup X]
    [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (e : X ≃ₗ[ℂ] Y) :
    ¬ FiniteDimensional ℂ X ↔ ¬ FiniteDimensional ℂ Y := by
  constructor
  · intro hX hY
    haveI := hY
    exact hX (FiniteDimensional.of_injective e.toLinearMap e.injective)
  · intro hY hX
    haveI := hX
    exact hY (FiniteDimensional.of_surjective e.toLinearMap e.surjective)

open Classical in
/-- Paper: Remark 7.5.0.2 and Equation (7.5.0.15), p. 378.
The primary quotient is infinite-dimensional exactly when the comparison difference quotient is:
`strongCoprimality` identifies the two by a topological linear equivalence. The difference
quotient is the modulated decay isotype modulo the range of the difference product over the
unramified places, so the remaining input for the refutation of the printed subquotient model
is that this range has infinite codimension. -/
theorem not_finiteDimensional_strongCoprimalityQuotient_iff (χ : U) (S : Finset V)
    (π : (v : V) → (v.adicCompletion F)ˣ)
    (hπ : ∀ v ∈ S, Valuation.IsUniformizer
      (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))) (π v).val) :
    let T := S.filter (fun v ↦ (ideleClassNormTwist χ 0).IsUnramifiedAt v)
    ¬ FiniteDimensional ℂ (StrongCoprimalityQuotient ω(χ) S) ↔
      ¬ FiniteDimensional ℂ (StrongCoprimalityDecaySpace ω(χ) ⧸
        strongCoprimalityDifferenceRange ω(χ) T π) := by
  obtain ⟨e, _⟩ := strongCoprimality χ S π hπ
  exact not_finiteDimensional_iff_of_linearEquiv e.toLinearEquiv

/-- Riesz's theorem: a compact set with nonempty interior in a Hausdorff topological vector
space forces finite-dimensionality. -/
private theorem finiteDimensional_of_isCompact_of_interior_nonempty {E : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℂ E] [T2Space E] {K : Set E} (hK : IsCompact K)
    (hKi : (interior K).Nonempty) : FiniteDimensional ℂ E := by
  obtain ⟨x, hx⟩ := hKi
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  have : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  exact FiniteDimensional.of_totallyBounded_nhds (𝕜 := ℂ)
    (isOpen_interior.mem_nhds hx) (hK.totallyBounded.subset interior_subset)

/-- A space whose strong dual is finite-dimensional is finite-dimensional. -/
private theorem finiteDimensional_of_finiteDimensional_strongDual {E : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [PolynormableSpace ℂ E]
    [T2Space E] (h : FiniteDimensional ℂ (StrongDual ℂ E)) : FiniteDimensional ℂ E := by
  have : SeparatingDual ℂ E := polynormableSpace_separatingDual ℂ E
  let f : E →ₗ[ℂ] Module.Dual ℂ (StrongDual ℂ E) :=
    { toFun := fun x =>
        { toFun := fun φ => φ x
          map_add' := fun _ _ => rfl
          map_smul' := fun c φ => rfl }
      map_add' := fun x y => by
        ext φ
        exact map_add φ x y
      map_smul' := fun c x => by
        ext φ
        exact map_smul φ c x }
  have hf : Function.Injective f := by
    intro x y hxy
    refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).mpr fun φ => ?_
    exact congrFun (congrArg DFunLike.coe hxy) φ
  exact FiniteDimensional.of_injective f hf

open scoped Pointwise in
/-- The strong dual of an infinite-dimensional nuclear Fréchet space is meagre: a countable
neighbourhood basis of the primal has polars that are compact in the strong dual, and no
compact subset of a Hausdorff topological vector space with nonempty interior can exist in
an infinite-dimensional space by Riesz's theorem. -/
theorem not_bairespace_strongDual (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsFrechetTVS E) (hN : IsNuclearTVS E)
    (hinf : ¬ FiniteDimensional ℂ E) : ¬ BaireSpace (StrongDual ℂ E) := by
  classical
  have hFE : IsFrechetTVS E := hE
  obtain ⟨hadd, hpoly, hmet, hcomplete⟩ := hE
  let : IsTopologicalAddGroup E := hadd
  have : PolynormableSpace ℂ E := hpoly
  have : ContinuousSMul ℂ E := PolynormableSpace.continuousSMul ℂ E
  have : TopologicalSpace.MetrizableSpace E := hmet
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  have : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  -- A nuclear Fréchet space is Schwartz, hence Montel, so polars are strongly compact.
  have hMontel : MontelSpace ℂ E :=
    montelSpace_of_schwartz_frechet hFE (isSchwartzTVS_of_isNuclearTVS hN)
  have : MontelSpace ℂ E := hMontel
  -- A countable decreasing neighbourhood basis of the primal.
  obtain ⟨Un, hUn⟩ := (𝓝 (0 : E)).exists_antitone_basis
  set K : ℕ → Set (StrongDual ℂ E) :=
    fun n => (((n + 1 : ℕ) : ℂ)) • StrongDual.polar ℂ (Un (n + 1)) with hKdef
  -- The scaled polars cover the strong dual.
  have hcover : (univ : Set (StrongDual ℂ E)) ⊆ ⋃ n, K n := by
    intro φ _
    have hb : Metric.ball (0 : ℂ) 1 ∈ 𝓝 (φ 0) := by
      rw [map_zero]
      exact Metric.ball_mem_nhds 0 one_pos
    have hopen : φ ⁻¹' Metric.ball (0 : ℂ) 1 ∈ 𝓝 (0 : E) :=
      φ.continuous.continuousAt.preimage_mem_nhds hb
    obtain ⟨m, hm⟩ := hUn.mem_iff.mp hopen
    refine mem_iUnion.mpr ⟨m, ?_⟩
    have hsub : Un (m + 1) ⊆ Un m := hUn.antitone (Nat.le_succ m)
    have hφ : φ ∈ StrongDual.polar ℂ (Un (m + 1)) := by
      rw [StrongDual.mem_polar_iff]
      intro x hx
      exact (mem_ball_zero_iff.mp (hm (hsub hx))).le
    have hcast : (((m + 1 : ℕ) : ℂ)) ≠ 0 := by
      simpa using Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)
    have hsmul : (((m + 1 : ℕ) : ℂ)) • (((((m + 1 : ℕ) : ℂ)))⁻¹ • φ) = φ := by
      rw [smul_smul, mul_inv_cancel₀ hcast, one_smul]
    have hψ : (((((m + 1 : ℕ) : ℂ)))⁻¹ • φ) ∈ StrongDual.polar ℂ (Un (m + 1)) := by
      rw [StrongDual.mem_polar_iff]
      intro x hx
      rw [smul_apply, norm_smul, norm_inv, Complex.norm_natCast]
      have h1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) :=
        mod_cast Nat.succ_le_succ (Nat.zero_le m)
      have hle : ‖φ x‖ ≤ 1 := hφ x hx
      rw [inv_mul_le_iff₀ (by linarith)]
      nlinarith [norm_nonneg (φ x)]
    rw [← hsmul]
    exact smul_mem_smul_set hψ
  have hKcompact (n : ℕ) : IsCompact (K n) :=
    (isCompact_strongDual_polar (hUn.mem (n + 1))).smul (((n + 1 : ℕ) : ℂ))
  -- A compact set with nonempty interior would make the strong dual finite-dimensional.
  have hKempty (n : ℕ) : interior (K n) = ∅ := by
    by_contra hne
    have hne' : (interior (K n)).Nonempty := Set.nonempty_iff_ne_empty.mpr hne
    have hfin : FiniteDimensional ℂ (StrongDual ℂ E) :=
      finiteDimensional_of_isCompact_of_interior_nonempty (hKcompact n) hne'
    have hN' : IsNuclearTVS (StrongDual ℂ E) := (isNuclearTVS_strongDual_iff hFE).mpr hN
    exact hinf (finiteDimensional_of_finiteDimensional_strongDual hfin)
  intro hb
  have : BaireSpace (StrongDual ℂ E) := hb
  have hmeagre : IsMeagre (⋃ n, K n) := isMeagre_iUnion fun n =>
    ((hKcompact n).isClosed.isNowhereDense_iff.mpr (hKempty n)).isMeagre
  exact not_isMeagre_of_isOpen isOpen_univ univ_nonempty (IsMeagre.mono hcover hmeagre)

section SLocal

variable {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Pₛ" => sAdelePolarSubspace F S
local notation "J₁" => (sIdeleQuotientNorm F S).ker
local notation "Kₛ(" η ")" => LinearMap.ker ((sLocalHomogeneousAdelicThetaLinearMap F S η).domRestrict Pₛ)

local notation "twistₛ" => quasiCharacterNormTwist (sIdeleQuotientNorm F S)
  (isProperMap_sIdeleQuotientNorm F S).continuous
local notation "dualₛ" => dualQuasiCharacter (sIdeleQuotientNorm F S)
  (isProperMap_sIdeleQuotientNorm F S).continuous
local notation "insertPolar(" f ")" => (⟨sAdeleSchwartzToGlobal F S (f : Pₛ).val,
  sAdeleSchwartzToGlobal_mem_polarSubspace f⟩ : P)

section

private theorem strongCoprimalityFourierJet_toGlobal_reflected_product_jets (f L : ℂ → ℂ) (r : ℂ) (k : ℕ)
    (hf : AnalyticAt ℂ f r) (hL : AnalyticAt ℂ L r) :
    iteratedDeriv k (fun z ↦ f z * L z) r =
      ∑ i : Fin (k + 1), ((-1 : ℂ) ^ i.val * iteratedDeriv i.val (fun w ↦ f (r - w)) 0) *
        ((k.choose i.val : ℂ) * iteratedDeriv (k - i.val) L r) := by
  rw [iteratedDeriv_fun_mul hf.contDiffAt hL.contDiffAt, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  rw [iteratedDeriv_comp_const_sub]
  simp only [sub_zero, smul_eq_mul]
  have hs : (-1 : ℂ) ^ i.val * (-1) ^ i.val = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  calc
    (k.choose i.val : ℂ) * iteratedDeriv i.val f r * iteratedDeriv (k - i.val) L r =
        (((-1 : ℂ) ^ i.val * (-1) ^ i.val) * iteratedDeriv i.val f r) *
          ((k.choose i.val : ℂ) * iteratedDeriv (k - i.val) L r) := by rw [hs]; ring
    _ = _ := by ring

private theorem strongCoprimalityFourierJet_toGlobal_jet_twist_add
    (G : Type*) [CommGroup G] [TopologicalSpace G] (m : G →* ℝ≥0ˣ)
    (hm : Continuous m) (c : QuasiCharacter G) (a z : ℂ) :
    quasiCharacterNormTwist m hm (quasiCharacterNormTwist m hm c a) z =
      quasiCharacterNormTwist m hm c (z + a) := by
  ext g
  let N : ℂ := (((m g : ℝ≥0) : ℝ) : ℂ)
  change c g * N ^ a * N ^ z = c g * N ^ (z + a)
  rw [add_comm, Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr
    (NNReal.coe_ne_zero.mpr (m g).ne_zero)), mul_assoc]

private theorem strongCoprimalityFourierJet_toGlobal_jet_rightHalf_bound
    (F : Type*) [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (z : ℂ) (hz : 1 < z.re) :
    0 ≤ globalIdelicOrderBound (ideleClassNormTwist χ z) := by
  have h0 : ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) 0 = 1 := by
    ext g
    change 1 * _ ^ (0 : ℂ) = (1 : ℂ)
    simp
  rw [globalIdelicOrderBound, ite_eq_right]
  rintro (h | h)
  · rw [← h0] at h
    have he := congrArg (quasiCharacterAbscissa (ideleClassNorm F) (isProperMap_ideleClassNorm F)
      ideleClassNorm_ne_one) h
    rw [quasiCharacterAbscissa_ideleClassNormTwist, quasiCharacterAbscissa_ideleClassNormTwist, Complex.zero_re] at he
    linarith
  · have he := congrArg (quasiCharacterAbscissa (ideleClassNorm F) (isProperMap_ideleClassNorm F)
      ideleClassNorm_ne_one) h
    rw [quasiCharacterAbscissa_ideleClassNormTwist, quasiCharacterAbscissa_ideleClassNormTwist, Complex.one_re] at he
    exact hz.ne' he

private theorem strongCoprimalityFourierJet_toGlobal_theta_globalZ_congr
    (F : Type*) [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
    (f g : SchwartzBruhat (Multiplicative 𝔸[F]))
    (hq : (LinearMap.ker (adelicThetaLinearMap F)).mkQ f =
      (LinearMap.ker (adelicThetaLinearMap F)).mkQ g) :
    (fun z ↦ globalIdelicZFunction f (ideleClassNormTwist χ z)) =
      (fun z ↦ globalIdelicZFunction g (ideleClassNormTwist χ z)) := by
  have hM : globalIdelicMellin f = globalIdelicMellin g := by
    have hh := congrArg (globalThetaMellin (F := F)) hq
    change globalThetaMellin (Submodule.Quotient.mk f) = globalThetaMellin (Submodule.Quotient.mk g) at hh
    simpa only [globalThetaMellin_mk] using hh
  have hAgree (z : ℂ) (hz : 1 < z.re) :
      globalIdelicZFunction f (ideleClassNormTwist χ z) = globalIdelicZFunction g (ideleClassNormTwist χ z) := by
    let c : {c : QuasiCharacter (IdeleClassGroup (𝓞 F) F) // 0 ≤ globalIdelicOrderBound c} :=
      ⟨ideleClassNormTwist χ z, strongCoprimalityFourierJet_toGlobal_jet_rightHalf_bound F χ z hz⟩
    exact DFunLike.congr_fun (congrArg Subtype.val hM) c
  funext z
  exact globalIdelicZetaIntegral_chartContinuation_eq f
    (globalIdelicZFunction_meromorphic f χ) (globalIdelicZFunction_meromorphic g χ)
    (fun w hw ↦ globalIdelicZFunction_eq_integral f (tate_twist_mem_rightHalf χ w hw))
    (fun w hw ↦ (hAgree w hw).symm.trans (globalIdelicZFunction_eq_integral f (tate_twist_mem_rightHalf χ w hw)))
    (s := z) (s' := z) rfl

private theorem strongCoprimalityFourierJet_toGlobal_fourier_insert_theta
    (F : Type*) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hgood : ∀ v : HeightOneSpectrum (𝓞 F), v.asIdeal ∣ differentIdeal ℤ (𝓞 F) → v ∈ S)
    (f : SchwartzBruhat (Multiplicative (SAdeleRing F S))) :
    (LinearMap.ker (adelicThetaLinearMap F)).mkQ (adeleSchwartzFourier (sAdeleSchwartzToGlobal F S f)) =
      (LinearMap.ker (adelicThetaLinearMap F)).mkQ (sAdeleSchwartzToGlobal F S (sAdeleSchwartzFourier f)) := by
  have hh := sLocalThetaFourier_toGlobal hgood (Submodule.Quotient.mk f)
  have hG := (existsUnique_globalThetaFourier (F := F)).exists.choose_spec.2 (sAdeleSchwartzToGlobal F S f)
  have hS := (existsUnique_sLocalThetaFourier (F := F) (S := S)).exists.choose_spec.2 f
  simp only [Submodule.mkQ_apply] at hG hS
  dsimp only at hh
  rw [sLocalThetaToGlobal_mk] at hh
  with_unfolding_all
    exact hG.symm.trans (hh.trans ((congrArg (sLocalThetaToGlobal F S) hS).trans
      (sLocalThetaToGlobal_mk (sAdeleSchwartzFourier f))))

private theorem strongCoprimalityFourierJet_toGlobal_insertion_factorization
    (F : Type*) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
    (hS : ideleClassNormTwist χ 0 ∈ unramifiedOutside F S)
    (hgood : ∀ v : HeightOneSpectrum (𝓞 F), v.asIdeal ∣ differentIdeal ℤ (𝓞 F) → v ∈ S)
    (f : SchwartzBruhat (Multiplicative (SAdeleRing F S))) :
    (fun z ↦ globalIdelicZFunction (sAdeleSchwartzToGlobal F S f) (ideleClassNormTwist χ z))
      =ᶠ[Filter.codiscrete ℂ] fun z ↦
        sLocalIdelicZFunction f (quasiCharacterNormTwist (sIdeleQuotientNorm F S)
          (isProperMap_sIdeleQuotientNorm F S).continuous (sIdeleRestriction F S ⟨ideleClassNormTwist χ 0, hS⟩) z) *
          heckeEulerProductOutside S χ hS z := by
  classical
  obtain ⟨L, hNF, hSeries⟩ := finiteHeckeL_exists_continuation χ
  have hmass : (∏ᶠ v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
      (((finiteLocalMultiplicativeTamagawaMeasure F v.val) (v.val.adicCompletionIntegers F).units).toReal : ℂ)) = 1 := by
    apply finprod_eq_one_of_forall_eq_one
    intro v
    have hv : ¬ v.val.asIdeal ∣ differentIdeal ℤ (𝓞 F) := fun h ↦ v.property (hgood v.val h)
    simp [finiteLocalMultiplicativeTamagawaMeasure_integerUnits, multiplicity_eq_zero_of_not_dvd hv]
  have hw := weilIdentity_unramifiedOutside_meromorphic S f χ hS L hNF (fun z hz ↦ hSeries ⟨z, hz⟩)
  have hP := (strongCoprimalityJetMatrix_det_ne_zero_euler χ S).1
  have hM : MeromorphicOn (fun z ↦ reciprocalPartialHeckeEulerProduct χ S z * L z) univ :=
    fun z hz ↦ (hP z).meromorphicAt.mul (hNF hz).meromorphicAt
  have ho : (fun z ↦ reciprocalPartialHeckeEulerProduct χ S z * L z) =ᶠ[Filter.codiscrete ℂ]
      heckeEulerProductOutside S χ hS := by
    rw [heckeEulerProductOutside_eq_finite S χ hS L hNF hSeries]
    exact toMeromorphicNFOn_eqOn_codiscrete hM
  filter_upwards [hw, ho] with z hz hzo
  rw [hmass, one_mul] at hz
  rw [← hzo, hz]
  dsimp only [reciprocalPartialHeckeEulerProduct]
  ring

private theorem strongCoprimalityFourierJet_toGlobal_reflected_insertion_factorization
    (F : Type*) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
    (hS : ideleClassNormTwist χ 0 ∈ unramifiedOutside F S)
    (hgood : ∀ v : HeightOneSpectrum (𝓞 F), v.asIdeal ∣ differentIdeal ℤ (𝓞 F) → v ∈ S)
    (f : SchwartzBruhat (Multiplicative (SAdeleRing F S))) :
    (fun z ↦ globalIdelicZFunction (adeleSchwartzFourier (sAdeleSchwartzToGlobal F S f)) (ideleClassNormTwist χ z))
      =ᶠ[Filter.codiscrete ℂ] fun z ↦
        sLocalIdelicZFunction (sAdeleSchwartzFourier f) (quasiCharacterNormTwist (sIdeleQuotientNorm F S)
          (isProperMap_sIdeleQuotientNorm F S).continuous (sIdeleRestriction F S ⟨ideleClassNormTwist χ 0, hS⟩) z) *
          heckeEulerProductOutside S χ hS z := by
  rw [strongCoprimalityFourierJet_toGlobal_theta_globalZ_congr F χ _ _ (strongCoprimalityFourierJet_toGlobal_fourier_insert_theta F S hgood f)]
  exact strongCoprimalityFourierJet_toGlobal_insertion_factorization F S χ hS hgood (sAdeleSchwartzFourier f)

private theorem strongCoprimalityFourierJet_toGlobal_local_reflection
    (F : Type*) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (c b : QuasiCharacter (SIdeleQuotient F S)) (r : ℂ)
    (hc : dualQuasiCharacter (sIdeleQuotientNorm F S) (isProperMap_sIdeleQuotientNorm F S).continuous c =
      quasiCharacterNormTwist (sIdeleQuotientNorm F S) (isProperMap_sIdeleQuotientNorm F S).continuous b r)
    (z : ℂ) :
    dualQuasiCharacter (sIdeleQuotientNorm F S) (isProperMap_sIdeleQuotientNorm F S).continuous
      (quasiCharacterNormTwist (sIdeleQuotientNorm F S) (isProperMap_sIdeleQuotientNorm F S).continuous c z) =
      quasiCharacterNormTwist (sIdeleQuotientNorm F S) (isProperMap_sIdeleQuotientNorm F S).continuous b (r - z) := by
  have hh : dualQuasiCharacter (sIdeleQuotientNorm F S) (isProperMap_sIdeleQuotientNorm F S).continuous
      (quasiCharacterNormTwist (sIdeleQuotientNorm F S) (isProperMap_sIdeleQuotientNorm F S).continuous c z) =
      quasiCharacterNormTwist (sIdeleQuotientNorm F S) (isProperMap_sIdeleQuotientNorm F S).continuous
        (dualQuasiCharacter (sIdeleQuotientNorm F S) (isProperMap_sIdeleQuotientNorm F S).continuous c) (-z) := by
    ext g
    let N : ℂ := (((sIdeleQuotientNorm F S g : ℝ≥0) : ℝ) : ℂ)
    change N * (quasiCharacterNormTwist (sIdeleQuotientNorm F S) (isProperMap_sIdeleQuotientNorm F S).continuous c z) g⁻¹ =
      (N * c g⁻¹) * N ^ (-z)
    rw [map_inv, map_inv]
    change N * (c g * N ^ z)⁻¹ = (N * (c g)⁻¹) * N ^ (-z)
    rw [mul_inv_rev, Complex.cpow_neg]
    ring
  rw [hh, hc, strongCoprimalityFourierJet_toGlobal_jet_twist_add]
  congr 1
  ring

private theorem strongCoprimalityFourierJet_toGlobal_local_reflected_analytic
    (F : Type*) [Field F] [NumberField F] (S T : Finset (HeightOneSpectrum (𝓞 F)))
    (η : PontryaginDual (sIdeleQuotientNorm F S).ker)
    (j : SLocalOrbitalIndex (F := F) (S := S) T η)
    (b : QuasiCharacter (SIdeleQuotient F S)) (r : ℂ)
    (hc : dualQuasiCharacter (sIdeleQuotientNorm F S) (isProperMap_sIdeleQuotientNorm F S).continuous j.val.1 =
      quasiCharacterNormTwist (sIdeleQuotientNorm F S) (isProperMap_sIdeleQuotientNorm F S).continuous b r)
    (f : SchwartzBruhat (Multiplicative (SAdeleRing F S))) :
    AnalyticAt ℂ (fun z ↦ sLocalIdelicZFunction (sAdeleSchwartzFourier f)
      (quasiCharacterNormTwist (sIdeleQuotientNorm F S) (isProperMap_sIdeleQuotientNorm F S).continuous b z)) r := by
  let A (z : ℂ) := sLocalIdelicZFunction (sAdeleSchwartzFourier f)
    (quasiCharacterNormTwist (sIdeleQuotientNorm F S) (isProperMap_sIdeleQuotientNorm F S).continuous b z)
  have href : (fun z ↦ sLocalIdelicZFunction (sAdeleSchwartzFourier f)
      (dualQuasiCharacter (sIdeleQuotientNorm F S) (isProperMap_sIdeleQuotientNorm F S).continuous
        (quasiCharacterNormTwist (sIdeleQuotientNorm F S) (isProperMap_sIdeleQuotientNorm F S).continuous j.val.1 z))) =
      (fun z ↦ A (r - z)) := by
    funext z
    exact congrArg (sLocalIdelicZFunction (sAdeleSchwartzFourier f)) (strongCoprimalityFourierJet_toGlobal_local_reflection F S j.val.1 b r hc z)
  have h0 := sLocalOrbitalFourierZeta_analyticAt j f
  dsimp only at h0
  rw [href] at h0
  have hh := h0.comp_of_eq (f := fun z : ℂ ↦ r - z) (x := r) (by fun_prop) (sub_self r)
  simpa only [Function.comp_def, sub_sub_cancel, A] using hh

private theorem strongCoprimalityFourierJet_toGlobal_analytic_germ_of_codiscrete (f g : ℂ → ℂ) (r : ℂ)
    (hf : AnalyticAt ℂ f r) (hg : AnalyticAt ℂ g r) (he : f =ᶠ[Filter.codiscrete ℂ] g) :
    f =ᶠ[𝓝 r] g := by
  have hh := (eventuallyEq_codiscreteWithin_iff_forall_eventually_nhdsNE.mp he) r (mem_univ r)
  exact (hf.meromorphicNFAt.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds hg.meromorphicNFAt).mp (hh.mono (fun y hy ↦ hy (mem_univ y)))

private theorem strongCoprimalityFourierJet_toGlobal_local_jet_reflection
    (F : Type*) [Field F] [NumberField F] (S T : Finset (HeightOneSpectrum (𝓞 F)))
    (η : PontryaginDual (sIdeleQuotientNorm F S).ker)
    (j : SLocalOrbitalIndex (F := F) (S := S) T η)
    (b : QuasiCharacter (SIdeleQuotient F S)) (r : ℂ)
    (hc : dualQuasiCharacter (sIdeleQuotientNorm F S) (isProperMap_sIdeleQuotientNorm F S).continuous j.val.1 =
      quasiCharacterNormTwist (sIdeleQuotientNorm F S) (isProperMap_sIdeleQuotientNorm F S).continuous b r)
    (f : SchwartzBruhat (Multiplicative (SAdeleRing F S))) :
    sLocalOrbitalFourierJet j ((LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap F S η)).mkQ f) =
      iteratedDeriv j.val.2 (fun z ↦ sLocalIdelicZFunction (sAdeleSchwartzFourier f)
        (quasiCharacterNormTwist (sIdeleQuotientNorm F S) (isProperMap_sIdeleQuotientNorm F S).continuous b (r - z))) 0 := by
  have hh := sLocalOrbitalFourierJet_mk j f
  have he : (fun z ↦ sLocalIdelicZFunction (sAdeleSchwartzFourier f)
      (dualQuasiCharacter (sIdeleQuotientNorm F S) (isProperMap_sIdeleQuotientNorm F S).continuous
        (quasiCharacterNormTwist (sIdeleQuotientNorm F S) (isProperMap_sIdeleQuotientNorm F S).continuous j.val.1 z))) =
      (fun z ↦ sLocalIdelicZFunction (sAdeleSchwartzFourier f)
        (quasiCharacterNormTwist (sIdeleQuotientNorm F S) (isProperMap_sIdeleQuotientNorm F S).continuous b (r - z))) := by
    funext z
    exact congrArg (sLocalIdelicZFunction (sAdeleSchwartzFourier f)) (strongCoprimalityFourierJet_toGlobal_local_reflection F S j.val.1 b r hc z)
  dsimp only at hh
  rw [he] at hh
  exact hh

end

/-- Paper: Equations (7.5.0.8)–(7.5.0.13), pp. 377–378.
On an inserted polar test, the regular change of coordinates uses the Fourier
functionals of §7.3 and their signs from differentiation before reflection.
Deviation: Taking S to contain all primes of the different makes the outside
insertion self-dual and gives every outside unit group mass one. -/
theorem strongCoprimalityFourierJet_toGlobal {T : Finset V} (_hT : T ⊆ S)
    {η : PontryaginDual J₁} (j : SLocalOrbitalIndex (F := F) (S := S) T η)
    (s : ℂ) (hS : ideleClassNormTwist χ⁻¹ 0 ∈ unramifiedOutside F S)
    (_hgood : ∀ v : V, v.asIdeal ∣ differentIdeal ℤ (𝓞 F) → v ∈ S)
    (_hc : dualₛ j.val.1 = twistₛ (sIdeleRestriction F S ⟨ideleClassNormTwist χ⁻¹ 0, hS⟩) (1 - s))
    (hL : AnalyticAt ℂ (heckeEulerProductOutside S χ⁻¹ hS) (1 - s)) (f : Pₛ) :
    let k := j.val.2
    let idx (i : Fin (k + 1)) : SLocalOrbitalIndex (F := F) (S := S) T η :=
      ⟨(j.val.1, i.val), j.property.1, lt_of_le_of_lt (Nat.le_of_lt_succ i.isLt) j.property.2⟩
    let x := (LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap F S η)).mkQ f.val
    let A := strongCoprimalityJetMatrix χ S hS s hL (k + 1)
    strongCoprimalityFourierJet χ τ hτ s k ((K(ω(χ))).mkQ insertPolar(f)) =
      ∑ i : Fin (k + 1), (-1 : ℂ) ^ i.val *
        sLocalOrbitalFourierJet (F := F) (S := S) (T := T) (ω := η) (idx i) x *
          A i (Fin.last k) := by
  intro k idx x mat
  let b := sIdeleRestriction F S ⟨ideleClassNormTwist χ⁻¹ 0, hS⟩
  let localZ (z : ℂ) := sLocalIdelicZFunction (sAdeleSchwartzFourier f.val) (twistₛ b z)
  let globalZ (z : ℂ) := globalIdelicZFunction (adeleSchwartzFourier (sAdeleSchwartzToGlobal F S f.val)) (ideleClassNormTwist χ⁻¹ z)
  let outside := heckeEulerProductOutside S χ⁻¹ hS
  have hlocal : AnalyticAt ℂ localZ (1 - s) := strongCoprimalityFourierJet_toGlobal_local_reflected_analytic F S T η j b (1 - s) _hc f.val
  have hglobal := strongCoprimalityFourierJet_mk χ τ hτ s k insertPolar(f)
  have hfactor : globalZ =ᶠ[Filter.codiscrete ℂ] (fun z ↦ localZ z * outside z) :=
    strongCoprimalityFourierJet_toGlobal_reflected_insertion_factorization F S χ⁻¹ hS _hgood f.val
  have heq := strongCoprimalityFourierJet_toGlobal_analytic_germ_of_codiscrete globalZ (fun z ↦ localZ z * outside z) (1 - s)
    (hglobal.1.analyticAt _) (by fun_prop) hfactor
  rw [hglobal.2, heq.iteratedDeriv_eq k, strongCoprimalityFourierJet_toGlobal_reflected_product_jets localZ outside (1 - s) k hlocal hL]
  apply Finset.sum_congr rfl
  intro i hi
  have hjet := strongCoprimalityFourierJet_toGlobal_local_jet_reflection F S T η (idx i) b (1 - s) _hc f.val
  rw [hjet]
  simp only [mat, strongCoprimalityJetMatrix, Fin.le_last, ite_true, Fin.val_last]
  rfl

section

private theorem strongCoprimalityFourierJet_toGlobal_at_pole_linear_factor_deriv (g : ℂ → ℂ) (r : ℂ) (hg : AnalyticAt ℂ g r) (n : ℕ) :
    iteratedDeriv (n + 1) (fun z ↦ (z - r) * g z) r = (n + 1 : ℂ) * iteratedDeriv n g r := by
  have hf : AnalyticAt ℂ (fun z : ℂ ↦ z - r) r := by fun_prop
  rw [iteratedDeriv_fun_mul hf.contDiffAt hg.contDiffAt]
  have hlin (i : ℕ) : iteratedDeriv i (fun z : ℂ ↦ z - r) r = if i = 1 then 1 else 0 := by
    by_cases hi : i = 0
    · subst i; simp
    · have hh := congrFun (iteratedDeriv_comp_sub_const (f := id) (n := i) (s := r)) r
      simpa [id, iteratedDeriv_id, hi] using hh
  rw [Finset.sum_eq_single 1]
  · simp [hlin]
  · intro i hi hne
    rw [hlin, ite_eq_right hne, mul_zero, zero_mul]
  · intro hne
    exact (hne (by simp)).elim

private theorem strongCoprimalityFourierJet_toGlobal_at_pole_dslope_jet (f : ℂ → ℂ) (r : ℂ) (hf : AnalyticAt ℂ f r) (hzero : f r = 0) (n : ℕ) :
    iteratedDeriv n (dslope f r) r = iteratedDeriv (n + 1) f r / (n + 1 : ℂ) := by
  have hfun : f = (fun z ↦ (z - r) * dslope f r z) := by
    funext z
    simpa only [hzero, sub_zero, smul_eq_mul] using (sub_smul_dslope f r z).symm
  have hh := strongCoprimalityFourierJet_toGlobal_at_pole_linear_factor_deriv (dslope f r) r (hf.dslope r) n
  rw [← hfun] at hh
  apply (eq_div_iff (by exact_mod_cast Nat.succ_ne_zero n : (n + 1 : ℂ) ≠ 0)).mpr
  rw [mul_comm, ← hh]

private theorem strongCoprimalityFourierJet_toGlobal_at_pole_cancelled_product_jets (Z H f : ℂ → ℂ) (r : ℂ) (k : ℕ)
    (hH : AnalyticAt ℂ H r) (hf : AnalyticAt ℂ f r) (hzero : f r = 0)
    (heq : Z =ᶠ[𝓝 r] fun z ↦ dslope f r z * H z) :
    iteratedDeriv k Z r = ∑ m ∈ Finset.range (k + 1), (k.choose m : ℂ) *
      iteratedDeriv (k - m) H r * (iteratedDeriv (m + 1) f r / (m + 1 : ℂ)) := by
  rw [heq.iteratedDeriv_eq k, iteratedDeriv_fun_mul (hf.dslope r).contDiffAt hH.contDiffAt]
  apply Finset.sum_congr rfl
  intro m hm
  rw [strongCoprimalityFourierJet_toGlobal_at_pole_dslope_jet f r hf hzero m]
  ring

private theorem strongCoprimalityFourierJet_toGlobal_at_pole_simple_pole_cancel (L f Z : ℂ → ℂ) (r : ℂ)
    (hL : MeromorphicNFOn L univ) (horder : meromorphicOrderAt L r = -1)
    (hf : AnalyticAt ℂ f r) (hZ : AnalyticAt ℂ Z r)
    (heq : Z =ᶠ[𝓝[≠] r] fun z ↦ f z * L z) :
    let H := toMeromorphicNFOn (fun z ↦ (z - r) * L z) univ
    AnalyticAt ℂ H r ∧ H r ≠ 0 ∧ f r = 0 ∧
      Z =ᶠ[𝓝 r] fun z ↦ dslope f r z * H z := by
  intro H
  have hlin (z : ℂ) : AnalyticAt ℂ (fun w : ℂ ↦ w - r) z := by fun_prop
  have hM : MeromorphicOn (fun z ↦ (z - r) * L z) univ :=
    fun z hz ↦ (hlin z).meromorphicAt.mul (hL.meromorphicOn z hz)
  have hHNF := meromorphicNFOn_toMeromorphicNFOn (fun z ↦ (z - r) * L z) univ (mem_univ r)
  have hHo : meromorphicOrderAt H r = 0 := by
    rw [meromorphicOrderAt_toMeromorphicNFOn hM (mem_univ r)]
    change meromorphicOrderAt ((fun z : ℂ ↦ z - r) * L) r = 0
    rw [meromorphicOrderAt_mul (hlin r).meromorphicAt (hL.meromorphicOn r (mem_univ r)),
      meromorphicOrderAt_id_sub_const, horder]
    norm_num
  have hHa : AnalyticAt ℂ H r := hHNF.meromorphicOrderAt_nonneg_iff_analyticAt.mp (hHo ▸ le_rfl)
  have hHne : H r ≠ 0 := hHNF.meromorphicOrderAt_eq_zero_iff.mp hHo
  have hfzero : f r = 0 := by
    by_contra hn
    have hfo := hf.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hn
    have hzo := meromorphicOrderAt_congr heq
    change meromorphicOrderAt Z r = meromorphicOrderAt (f * L) r at hzo
    rw [meromorphicOrderAt_mul hf.meromorphicAt (hL.meromorphicOn r (mem_univ r)), hfo, horder] at hzo
    have hh := hZ.meromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt.mpr hZ
    rw [hzo] at hh
    exact (show ¬ (0 : WithTop ℤ) ≤ -1 by decide) hh
  refine ⟨hHa, hHne, hfzero, ?_⟩
  let D (z : ℂ) := dslope f r z * H z
  have hEqNE : Z =ᶠ[𝓝[≠] r] D := by
    filter_upwards [heq, hM.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ r), self_mem_nhdsWithin] with z hz hHz hne
    change Z z = dslope f r z * H z
    change H z = (z - r) * L z at hHz
    rw [hz, hHz, dslope_of_ne f hne]
    simp only [slope, vsub_eq_sub, hfzero, sub_zero, smul_eq_mul]
    field_simp [sub_ne_zero.mpr hne]
  have hD : ContinuousAt D r := (hf.dslope r).continuousAt.mul hHa.continuousAt
  have hsame : Z r = D r := tendsto_nhds_unique
    (hZ.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    ((hD.tendsto.mono_left nhdsWithin_le_nhds).congr' hEqNE.symm)
  have hn : ∀ᶠ z in 𝓝 r, z ≠ r → Z z = D z := eventually_nhdsWithin_iff.mp hEqNE
  filter_upwards [hn] with z hz
  by_cases he : z = r
  · simpa only [he] using hsame
  · exact hz he

private theorem strongCoprimalityFourierJet_toGlobal_at_pole_jet_local_chart
    (F : Type*) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (c : QuasiCharacter (SIdeleQuotient F S)) :
    ∃ (ψ : PontryaginDual (SIdeleQuotient F S)) (a : ℂ),
      quasiCharacterNormTwist (sIdeleQuotientNorm F S) (isProperMap_sIdeleQuotientNorm F S).continuous
        ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp ψ) a = c := by
  let : LocallyCompactSpace (SAdeleRing F S)ˣ := (sIdeleGroup_description F S).2.2.1
  have := isClosed_sProjectedDiagonal (F := F) (S := S)
  obtain ⟨σ, hσ⟩ := sIdeleQuotientNorm_exists_section F S
  obtain ⟨t, ht⟩ := exists_ne (1 : ℝ≥0ˣ)
  let m := sIdeleQuotientNorm F S
  have hm := isProperMap_sIdeleQuotientNorm F S
  have hne : ∃ g, m g ≠ 1 := ⟨σ t, (hσ t).trans_ne ht⟩
  let a := quasiCharacterAbscissa m hm hne c
  let d := quasiCharacterNormTwist m hm.continuous c (-(a : ℂ))
  have hpos (g : SIdeleQuotient F S) : 0 < ((m g : ℝ≥0) : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hd (g : SIdeleQuotient F S) : ‖d g‖ = 1 := by
    change ‖c g * (((m g : ℝ≥0) : ℝ) : ℂ) ^ (-(a : ℂ))‖ = 1
    rw [norm_mul, norm_quasiCharacter_eq_rpow_abscissa m hm hne,
      Complex.norm_cpow_eq_rpow_re_of_pos (hpos g), Complex.neg_re, Complex.ofReal_re]
    exact (Real.rpow_add (hpos g) a (-a)).symm.trans (by simp)
  let ψ : PontryaginDual (SIdeleQuotient F S) :=
    { toFun := fun g ↦ ⟨d g, mem_sphere_zero_iff_norm.mpr (hd g)⟩
      map_one' := Circle.ext (map_one d)
      map_mul' := fun x y ↦ Circle.ext (map_mul d x y)
      continuous_toFun := d.continuous.subtype_mk _ }
  refine ⟨ψ, a, ContinuousMonoidHom.ext fun g ↦ ?_⟩
  change c g * _ ^ (-(a : ℂ)) * _ ^ (a : ℂ) = c g
  rw [mul_assoc, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (hpos g).ne'),
    neg_add_cancel, Complex.cpow_zero, mul_one]

private theorem strongCoprimalityFourierJet_toGlobal_at_pole_pole_product_input_analytic (L A Z : ℂ → ℂ) (r : ℂ)
    (hL : MeromorphicAt L r) (horder : meromorphicOrderAt L r = -1)
    (hA : MeromorphicNFAt A r) (hZ : AnalyticAt ℂ Z r)
    (heq : Z =ᶠ[𝓝[≠] r] fun z ↦ A z * L z) : AnalyticAt ℂ A r := by
  have ho := meromorphicOrderAt_congr heq
  change meromorphicOrderAt Z r = meromorphicOrderAt (A * L) r at ho
  rw [meromorphicOrderAt_mul hA.meromorphicAt hL, horder] at ho
  apply hA.meromorphicOrderAt_nonneg_iff_analyticAt.mp
  by_cases ht : meromorphicOrderAt A r = ⊤
  · simp [ht]
  · generalize hn : meromorphicOrderAt A r = n at ho ht ⊢
    lift n to ℤ using ht
    have hb := hZ.meromorphicOrderAt_nonneg
    rw [ho] at hb
    change ((0 : ℤ) : WithTop ℤ) ≤ ((n + -1 : ℤ) : WithTop ℤ) at hb
    have hb' : (0 : ℤ) ≤ n + -1 := by exact_mod_cast hb
    have hn' : (0 : ℤ) ≤ n := by omega
    exact_mod_cast hn'

private theorem strongCoprimalityFourierJet_toGlobal_at_pole_local_twist_meromorphicNF
    (F : Type*) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (b : QuasiCharacter (SIdeleQuotient F S))
    (f : SchwartzBruhat (Multiplicative (SAdeleRing F S))) :
    MeromorphicNFOn (fun z ↦ sLocalIdelicZFunction f
      (quasiCharacterNormTwist (sIdeleQuotientNorm F S) (isProperMap_sIdeleQuotientNorm F S).continuous b z)) univ := by
  obtain ⟨ψ, a, ha⟩ := strongCoprimalityFourierJet_toGlobal_at_pole_jet_local_chart F S b
  have he : (fun z ↦ sLocalIdelicZFunction f
      (quasiCharacterNormTwist (sIdeleQuotientNorm F S) (isProperMap_sIdeleQuotientNorm F S).continuous b z)) =
      (fun z ↦ sLocalIdelicZFunction f
        (quasiCharacterNormTwist (sIdeleQuotientNorm F S) (isProperMap_sIdeleQuotientNorm F S).continuous ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp ψ) (z + a))) := by
    funext z
    rw [← ha, strongCoprimalityFourierJet_toGlobal_jet_twist_add]
  rw [he]
  intro z hz
  exact meromorphicNFAt_comp_add_const_iff_meromorphicNFAt.mpr
    (sLocalIdelicZFunction_meromorphic f ψ (mem_univ _))

end

/-- Paper: Equations (7.5.0.9)–(7.5.0.14), pp. 377–378.
At a simple pole r of the outside factor L, write H for the holomorphic extension
of (z − r)L(z). The local zeta function A of the Fourier-transformed polar test vanishes at r.
The k-th global derivative uses local derivatives of orders 1 through k + 1.
Deviation: This is the pole-cancelled Leibniz rule at the exceptional point. -/
theorem strongCoprimalityFourierJet_toGlobal_at_pole (s : ℂ)
    (hS : ideleClassNormTwist χ⁻¹ 0 ∈ unramifiedOutside F S)
    (_hgood : ∀ v : V, v.asIdeal ∣ differentIdeal ℤ (𝓞 F) → v ∈ S)
    (_hpole : meromorphicOrderAt (heckeEulerProductOutside S χ⁻¹ hS) (1 - s) = -1)
    (f : Pₛ) (k : ℕ) :
    let r := 1 - s
    let H := toMeromorphicNFOn (fun z ↦ (z - r) * heckeEulerProductOutside S χ⁻¹ hS z) univ
    let c := sIdeleRestriction F S ⟨ideleClassNormTwist χ⁻¹ 0, hS⟩
    let A := fun z ↦ sLocalIdelicZFunction (sAdeleSchwartzFourier f.val) (twistₛ c z)
    AnalyticAt ℂ H r ∧ H r ≠ 0 ∧ AnalyticAt ℂ A r ∧ A r = 0 ∧
      strongCoprimalityFourierJet χ τ hτ s k ((K(ω(χ))).mkQ insertPolar(f)) =
        ∑ m ∈ Finset.range (k + 1), (k.choose m : ℂ) * iteratedDeriv (k - m) H r *
          (iteratedDeriv (m + 1) A r / (m + 1 : ℂ)) := by
  intro r H c A
  let outside := heckeEulerProductOutside S χ⁻¹ hS
  let globalZ (z : ℂ) := globalIdelicZFunction (adeleSchwartzFourier (sAdeleSchwartzToGlobal F S f.val)) (ideleClassNormTwist χ⁻¹ z)
  have hglobal := strongCoprimalityFourierJet_mk χ τ hτ s k insertPolar(f)
  have hfactor : globalZ =ᶠ[Filter.codiscrete ℂ] (fun z ↦ A z * outside z) :=
    strongCoprimalityFourierJet_toGlobal_reflected_insertion_factorization F S χ⁻¹ hS _hgood f.val
  have heq : globalZ =ᶠ[𝓝[≠] r] (fun z ↦ A z * outside z) := by
    have hh := (eventuallyEq_codiscreteWithin_iff_forall_eventually_nhdsNE.mp hfactor) r (mem_univ r)
    exact hh.mono (fun z hz ↦ hz (mem_univ z))
  have houtside : MeromorphicNFOn outside univ := by
    unfold outside heckeEulerProductOutside
    exact meromorphicNFOn_toMeromorphicNFOn _ _
  have hA := strongCoprimalityFourierJet_toGlobal_at_pole_local_twist_meromorphicNF F S c (sAdeleSchwartzFourier f.val) (mem_univ r)
  have hanalytic := strongCoprimalityFourierJet_toGlobal_at_pole_pole_product_input_analytic outside A globalZ r
    (houtside (mem_univ r)).meromorphicAt _hpole hA (hglobal.1.analyticAt r) heq
  obtain ⟨hH, hHne, hzero, hgerm⟩ := strongCoprimalityFourierJet_toGlobal_at_pole_simple_pole_cancel outside A globalZ r houtside _hpole
    hanalytic (hglobal.1.analyticAt r) heq
  refine ⟨hH, hHne, hanalytic, hzero, ?_⟩
  rw [hglobal.2]
  exact strongCoprimalityFourierJet_toGlobal_at_pole_cancelled_product_jets globalZ H A r k hH hanalytic hzero hgerm

-- TODO(paper-gap): The basis in §7.3 is for unrestricted local tests. On the
-- polar quotient its order-zero Fourier functional at the exceptional point
-- vanishes. To use that basis in (7.5.0.14), identify a basis of the polar
-- quotient with the shifted orders above (or use another surjectivity proof).

open MeasureTheory in
/-- Dilation by a local unit rescales additive Haar integration. -/
private theorem sAdelePV_integral_dilate (v : V) (a : (v.adicCompletion F)ˣ) :
    ∃ c : ℝ, ∀ p : v.adicCompletion F → ℂ,
      ∫ y, p ((a : v.adicCompletion F) * y) ∂finiteLocalAdditiveTamagawaMeasure F v =
        (c : ℂ) * ∫ y, p y ∂finiteLocalAdditiveTamagawaMeasure F v := by
  let K := v.adicCompletion F
  let : MeasurableSpace K := borel _
  let μ := finiteLocalAdditiveTamagawaMeasure F v
  let : ProperSpace K := properSpace_adicCompletion v
  let : BorelSpace K := ⟨rfl⟩
  let : μ.IsAddHaarMeasure := finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  let d := DomMulAct.mk a⁻¹
  refine ⟨Measure.addHaarScalarFactor (d • μ) μ, fun p ↦ ?_⟩
  have h := integral_domSMul (μ := μ) d p
  simp only [d, Equiv.symm_apply_apply, inv_inv, Units.smul_def, smul_eq_mul] at h
  apply h.symm.trans
  apply (congrArg (fun ν ↦ ∫ y, p y ∂ν) (Measure.isAddLeftInvariant_eq_smul (d • μ) μ)).trans
  rw [integral_smul_nnreal_measure]
  rfl

private theorem sAdelePV_uniformizer (v : V) :
    ∃ π : (v.adicCompletion F)ˣ,
      (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).IsUniformizer π.val := by
  let h := (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
  exact ⟨Units.mk0 (h.choose : v.adicCompletion F) h.choose_spec.ne_zero, h.choose_spec⟩

open MeasureTheory in
open scoped ENNReal in
/-- The local principal value rescales the integral by a scalar independent of the test. -/
private theorem sAdelePV_integral_local (v : V) :
    ∃ κ : ℂ, ∀ g : SchwartzBruhat (Multiplicative (v.adicCompletion F)),
      ∫ y, finitePlacePrincipalValue v g (Multiplicative.ofAdd y)
          ∂finiteLocalAdditiveTamagawaMeasure F v =
        κ * ∫ y, g (Multiplicative.ofAdd y) ∂finiteLocalAdditiveTamagawaMeasure F v := by
  let π := (sAdelePV_uniformizer (F := F) v).choose
  have hπ0 := (sAdelePV_uniformizer (F := F) v).choose_spec
  classical
  let Fv := v.adicCompletion F
  let : MeasurableSpace Fv := borel _
  let : MeasurableSpace Fvˣ := borel _
  let : BorelSpace Fv := ⟨rfl⟩
  let : BorelSpace Fvˣ := ⟨rfl⟩
  let : ProperSpace Fv := properSpace_adicCompletion v
  let : SecondCountableTopology Fvˣ := Units.isEmbedding_val₀.secondCountableTopology
  let μ := finiteLocalAdditiveTamagawaMeasure F v
  let : μ.IsAddHaarMeasure := finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  let Uv : Set Fvˣ := (v.adicCompletionIntegers F).units
  let μx := finiteLocalMultiplicativeTamagawaMeasure F v
  choose c hc using fun u : Fvˣ ↦ sAdelePV_integral_dilate (F := F) v (u⁻¹ * π⁻¹)
  have hUpos : 0 < μx.real Uv := (finitePlacePrincipalValue_integrable v π (finiteStandardGaussian v 1) 1).1
  have hUfin : μx Uv ≠ ∞ := fun h ↦ by
    simp [Measure.real, Uv, μx, h] at hUpos
  let ν := μx.restrict Uv
  let : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr hUfin
  let m := μx.real Uv
  refine ⟨1 - (m : ℂ)⁻¹ * ∫ u in Uv, (c u : ℂ) ∂μx, fun g ↦ ?_⟩
  let p : Fv → ℂ := fun y ↦ g (Multiplicative.ofAdd y)
  have hpm := (mem_finitePlaceSchwartz_iff F v p).mp ⟨g, fun _ ↦ rfl⟩
  have hcs : HasCompactSupport p := hpm.2
  have hpc : Continuous p := hpm.1.continuous
  have hpi : Integrable p μ := hpc.integrable_of_hasCompactSupport hcs
  let H : Fvˣ × Fv → ℂ := fun z ↦ p ((↑z.1⁻¹ : Fv) * ((↑π⁻¹ : Fv) * z.2))
  have hHi : Integrable H (ν.prod μ) := by
    have hHc : Continuous H := hpc.comp ((Units.continuous_val.comp
      (continuous_inv.comp continuous_fst)).mul (continuous_const.mul continuous_snd))
    have hUc : IsCompact Uv := Submonoid.units_isCompact
      (isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v))
    have hUo : IsOpen Uv := Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)
    let L : Set Fv := (fun z : Fvˣ × Fv ↦ (π : Fv) * (z.1 : Fv) * z.2) '' (Uv ×ˢ tsupport p)
    have hLc : IsCompact L := (hUc.prod hcs).image (by fun_prop)
    have hK := hUc.prod hLc
    have hKint : IntegrableOn H (Uv ×ˢ L) (ν.prod μ) := hHc.continuousOn.integrableOn_compact hK
    apply ((integrable_indicator_iff (μ := ν.prod μ) hK.measurableSet).2 hKint).congr
    have hfst : ∀ᵐ z ∂(ν.prod μ), z.1 ∈ Uv :=
      QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_fst
        (ae_restrict_mem hUo.measurableSet)
    filter_upwards [hfst] with z hz
    by_cases h0 : H z = 0
    · exact Set.indicator_apply_eq_self.mpr (fun _ ↦ h0)
    · have hk : (↑z.1⁻¹ : Fv) * ((↑π⁻¹ : Fv) * z.2) ∈ tsupport p := subset_tsupport _ h0
      have hzL : z.2 ∈ L := by
        refine ⟨(z.1, (↑z.1⁻¹ : Fv) * ((↑π⁻¹ : Fv) * z.2)), ⟨hz, hk⟩, ?_⟩
        have h1 := z.1.ne_zero
        have h2 := π.ne_zero
        simp only [Units.val_inv_eq_inv_val]
        field_simp
      exact Set.indicator_of_mem (show z ∈ Uv ×ˢ L from ⟨hz, hzL⟩) H
  have hpv : ∀ y, finitePlacePrincipalValue v g (Multiplicative.ofAdd y) =
      p y - (m : ℂ)⁻¹ * ∫ u, H (u, y) ∂ν := fun y ↦ by
    rw [finitePlacePrincipalValue_spec v π hπ0 g]
    rfl
  have hinner : ∀ u, ∫ y, H (u, y) ∂μ = c u * ∫ y, p y ∂μ := fun u ↦ by
    have := hc u p
    simp only [Units.val_mul] at this
    simp only [H, ← mul_assoc]
    exact this
  rw [integral_congr_ae (Filter.Eventually.of_forall hpv)]
  rw [integral_sub hpi (hHi.integral_prod_right.const_mul _), integral_const_mul,
    ← integral_integral_swap hHi]
  rw [integral_congr_ae (Filter.Eventually.of_forall hinner), integral_mul_const]
  change ∫ y, p y ∂μ - _ = (1 - (m : ℂ)⁻¹ * ∫ u, (c u : ℂ) ∂ν) * ∫ y, p y ∂μ
  ring

open scoped TensorProduct in
private theorem sAdelePV_ext_tensor {ι : Type*} [Fintype ι] {E X M : Type*} {W : ι → Type*}
    [AddCommGroup E] [Module ℂ E] [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup M] [Module ℂ M]
    (e : E ⊗[ℂ] PiTensorProduct ℂ W →ₗ[ℂ] X) (he : Function.Surjective e) (Q : X →ₗ[ℂ] X)
    (φ ψ : X →ₗ[ℂ] M)
    (h : ∀ a g, φ (Q (e (a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ g))) =
      ψ (e (a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ g))) (f : X) :
    φ (Q f) = ψ f := by
  obtain ⟨t, rfl⟩ := he f
  have key : (φ ∘ₗ Q) ∘ₗ e = ψ ∘ₗ e :=
    TensorProduct.ext (LinearMap.ext fun a ↦ PiTensorProduct.ext (MultilinearMap.ext fun g ↦ h a g))
  exact LinearMap.congr_fun key t

open Classical in
open scoped TensorProduct in
/-- An identity between linear maps after the S-local principal value can be checked on pure
tensors. -/
private theorem sAdelePV_ext {S T : Finset V} (hT : T ⊆ S) {M : Type*} [AddCommGroup M]
    [Module ℂ M] (φ ψ : SchwartzBruhat (Multiplicative (SAdeleRing F S)) →ₗ[ℂ] M)
    (h : ∀ (a : SchwartzBruhat (Multiplicative (InfiniteAdeleRing F))) (g : ∀ w : S, SchwartzBruhat (Multiplicative (w.val.adicCompletion F))),
      φ ((sAdeleSchwartz_inductiveTensor_equiv F S).choose (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w,
        if w.val ∈ T then finitePlacePrincipalValue w.val (g w) else g w))) =
      ψ ((sAdeleSchwartz_inductiveTensor_equiv F S).choose (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g w))))
    (f : SchwartzBruhat (Multiplicative (SAdeleRing F S))) : φ (sAdelePrincipalValue F hT f) = ψ f :=
  sAdelePV_ext_tensor (sAdeleSchwartz_inductiveTensor_equiv F S).choose.toLinearEquiv.toLinearMap
    (sAdeleSchwartz_inductiveTensor_equiv F S).choose.surjective (sAdelePrincipalValue F hT) φ ψ
    (fun a g ↦ (congrArg φ (sAdelePrincipalValue_tmul hT a g)).trans (h a g)) f

open MeasureTheory in
open scoped TensorProduct in
/-- At zero the Fourier transform of a pure tensor factors into the archimedean integral
and the product of the finite local integrals. -/
private theorem sAdelePV_fourier_tensor {S : Finset V}
    (a : SchwartzBruhat (Multiplicative (InfiniteAdeleRing F))) :
    ∃ I : ℂ, ∀ g : (w : S) → SchwartzBruhat (Multiplicative (w.val.adicCompletion F)),
    sAdeleSchwartzFourier ((sAdeleSchwartz_inductiveTensor_equiv F S).choose
      (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g w))) (Multiplicative.ofAdd 0) =
      I * ∏ w, ∫ y, g w (Multiplicative.ofAdd y) ∂finiteLocalAdditiveTamagawaMeasure F w.val := by
  classical
  let (w : InfinitePlace F) : MeasurableSpace w.Completion := borel _
  let (v : S) : MeasurableSpace (v.val.adicCompletion F) := borel _
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (w : InfinitePlace F) : BorelSpace w.Completion := ⟨rfl⟩
  let (v : S) : BorelSpace (v.val.adicCompletion F) := ⟨rfl⟩
  let (w : InfinitePlace F) : (infiniteLocalAdditiveTamagawaMeasure F w).IsAddHaarMeasure :=
    infiniteLocalAdditiveTamagawaMeasure_haar F w
  let (v : S) : (finiteLocalAdditiveTamagawaMeasure F v.val).IsAddHaarMeasure :=
    finiteLocalAdditiveTamagawaMeasure_isAddHaar F v.val
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let A (x : InfiniteAdeleRing F) := a (Multiplicative.ofAdd x)
  refine ⟨∫ x, A x ∂Measure.pi (infiniteLocalAdditiveTamagawaMeasure F), fun g ↦ ?_⟩
  let factor (v : S) (y : v.val.adicCompletion F) := g v (Multiplicative.ofAdd y)
  rw [sAdeleSchwartzFourier_apply_zero]
  simp_rw [(sAdeleSchwartz_inductiveTensor_equiv F S).choose_spec a g]
  exact (integral_prod_mul (μ := Measure.pi (infiniteLocalAdditiveTamagawaMeasure F))
    (ν := Measure.pi fun v : S ↦ finiteLocalAdditiveTamagawaMeasure F v.val)
    A (fun x ↦ ∏ v, factor v (x v))).trans
      (congrArg (_ * ·) (integral_fintype_prod_eq_prod factor))

open Classical in
private theorem sAdelePV_zero_prod {S T : Finset V} (hT : T ⊆ S)
    (g : (w : S) → SchwartzBruhat (Multiplicative (w.val.adicCompletion F))) :
    let g' := fun w : S ↦ if w.val ∈ T then finitePlacePrincipalValue w.val (g w) else g w
    (∏ w : S, g' w (Multiplicative.ofAdd 0)) =
      (if T.Nonempty then 0 else 1) * ∏ w : S, g w (Multiplicative.ofAdd 0) := by
  intro g'
  by_cases h : T.Nonempty
  · obtain ⟨v, hv⟩ := h
    let w : S := ⟨v, hT hv⟩
    have hw : w.val ∈ T := hv
    have hz : finitePlacePrincipalValue w.val (g w) (Multiplicative.ofAdd 0) = 0 := by
      have hm : finitePlacePrincipalValue w.val (g w) ∈ range (finitePlacePrincipalValue w.val) := ⟨g w, rfl⟩
      rwa [finitePlacePrincipalValue_range] at hm
    have hp := Finset.prod_eq_zero (s := Finset.univ) (f := fun i : S ↦ g' i (Multiplicative.ofAdd 0))
      (Finset.mem_univ w) (show g' w (Multiplicative.ofAdd 0) = 0 by simpa only [g', ite_eq_left hw] using hz)
    exact hp.trans (by rw [ite_eq_left ⟨v, hv⟩, zero_mul])
  · have hg : g' = g := funext fun w ↦ ite_eq_right (fun hw ↦ h ⟨w.val, hw⟩)
    rw [hg, ite_eq_right h, one_mul]

open MeasureTheory in
open scoped TensorProduct in
/-- Paper: Remark 7.5.0.2 and Equation (7.5.0.16), p. 378.
The local principal-value operator preserves the common kernel of the two local polar moments. -/
theorem strongCoprimalityLocalPrincipalValue_mem_polar {T : Finset V} (hT : T ⊆ S) (f : Pₛ) :
    sAdelePrincipalValue F hT f.val ∈ Pₛ := by
  classical
  let L := (sAdelePolarValues_isLinear (F := F) (S := S)).mk' _
  let c (w : S) : ℂ := if w.val ∈ T then (sAdelePV_integral_local (F := F) w.val).choose else 1
  let k : ℂ := if T.Nonempty then 0 else 1
  let D := (k • (LinearMap.id : ℂ →ₗ[ℂ] ℂ)).prodMap ((∏ w, c w) • (LinearMap.id : ℂ →ₗ[ℂ] ℂ))
  have he := sAdelePV_ext (F := F) hT L (D.comp L) (fun a g ↦ ?_) f.val
  · change L (sAdelePrincipalValue F hT f.val) = 0
    exact he.trans (show D (L f.val) = 0 from (congrArg D f.property).trans (map_zero D))
  · let g' (w : S) := if w.val ∈ T then finitePlacePrincipalValue w.val (g w) else g w
    let e := (sAdeleSchwartz_inductiveTensor_equiv F S).choose
    refine Prod.ext ?_ ?_
    · change e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g' w)) (Multiplicative.ofAdd 0) =
        k * e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g w)) (Multiplicative.ofAdd 0)
      apply ((sAdeleSchwartz_inductiveTensor_equiv F S).choose_spec a g' 0).trans
      refine Eq.trans ?_ (congrArg (k * ·) ((sAdeleSchwartz_inductiveTensor_equiv F S).choose_spec a g 0).symm)
      exact (congrArg (_ * ·) (sAdelePV_zero_prod hT g)).trans (mul_left_comm ..)
    · change sAdeleSchwartzFourier (e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g' w))) (Multiplicative.ofAdd 0) =
        (∏ w, c w) * sAdeleSchwartzFourier (e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g w))) (Multiplicative.ofAdd 0)
      let hI := sAdelePV_fourier_tensor (S := S) a
      apply (hI.choose_spec g').trans
      refine Eq.trans ?_ (congrArg ((∏ w, c w) * ·) (hI.choose_spec g).symm)
      have hi (w : S) : (∫ y, g' w (Multiplicative.ofAdd y) ∂finiteLocalAdditiveTamagawaMeasure F w.val) =
          c w * ∫ y, g w (Multiplicative.ofAdd y) ∂finiteLocalAdditiveTamagawaMeasure F w.val := by
        by_cases h : w.val ∈ T
        · simpa only [g', c, ite_eq_left h] using (sAdelePV_integral_local (F := F) w.val).choose_spec (g w)
        · simp only [g', c, ite_eq_right h, one_mul]
      have hprod := (Finset.prod_congr (s₁ := Finset.univ) rfl fun w _ ↦ hi w).trans Finset.prod_mul_distrib
      exact (congrArg (hI.choose * ·) hprod).trans (mul_left_comm ..)

/-- Equality of two polar classes can be checked in the unrestricted homogeneous quotient. -/
private theorem strongCoprimalityPrimaryQuotient_local_equiv_mk {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (θ : X →ₗ[ℂ] Y) (W : Submodule ℂ X) (f g : W) :
    (θ.domRestrict W).ker.mkQ f = (θ.domRestrict W).ker.mkQ g ↔
      θ.ker.mkQ f.val = θ.ker.mkQ g.val := by
  simp only [Submodule.mkQ_apply, Submodule.Quotient.eq, LinearMap.mem_ker,
    LinearMap.domRestrict_apply, Submodule.coe_sub]

/-- Applying the global principal value to two representatives with equal homogeneous
theta class preserves their equality on every norm-one character. -/
private theorem strongCoprimalityPrimaryQuotient_local_equiv_PV (ω : PontryaginDual C₁)
    (T : Finset V) (f g : SchwartzBruhat (Multiplicative 𝔸[F]))
    (h : (homogeneousAdelicThetaLinearMap F ω).ker.mkQ f =
      (homogeneousAdelicThetaLinearMap F ω).ker.mkQ g) :
    (homogeneousAdelicThetaLinearMap F ω).ker.mkQ (adelePrincipalValue F T f) =
      (homogeneousAdelicThetaLinearMap F ω).ker.mkQ (adelePrincipalValue F T g) := by
  obtain ⟨e, he⟩ := (globalThetaIsotypicAverage_equiv (F := F) ω).2
  apply e.injective
  apply Subtype.ext
  rw [he, he]
  let q := (adelicThetaLinearMap F).ker.mkQ
  let A := (existsUnique_globalThetaIsotypicAverage (F := F) ω).exists.choose
  change A (globalThetaPrincipalValue F T (q f)) = A (globalThetaPrincipalValue F T (q g))
  rw [← globalThetaPrincipalValue_isotypicAverage T ω (q f),
    ← globalThetaPrincipalValue_isotypicAverage T ω (q g)]
  exact congrArg _ ((he f).symm.trans ((congrArg Subtype.val (congrArg e h)).trans (he g)))

/-- Insertion intertwines the local and global principal values on homogeneous classes.
This follows by first passing to ordinary theta and then taking the character average. -/
private theorem strongCoprimalityPrimaryQuotient_local_equiv_commutes (ω : PontryaginDual C₁)
    {T : Finset V} (hp : T ⊆ S) (hn : T.Nonempty) (f : Pₛ) :
    (K(ω)).mkQ insertPolar(⟨sAdelePrincipalValue F hp f.val,
      strongCoprimalityLocalPrincipalValue_mem_polar hp f⟩) =
      (K(ω)).mkQ ⟨adelePrincipalValue F T (insertPolar(f)).val,
        strongCoprimalityPrincipalValue_mem_polar T insertPolar(f)⟩ := by
  apply (strongCoprimalityPrimaryQuotient_local_equiv_mk _ _ _ _).mpr
  obtain ⟨e, he⟩ := (globalThetaIsotypicAverage_equiv (F := F) ω).2
  apply e.injective
  apply Subtype.ext
  rw [he, he]
  exact congrArg _ (LinearMap.congr_fun (sLocalThetaPrincipalValue_toGlobal hp hn)
    ((sLocalAdelicTheta F S).ker.mkQ f.val))

/-- If insertion induces an open surjection from polar tests onto global polar theta classes,
the unrestricted insertion isomorphism identifies the kernel and gives the polar isomorphism. -/
private theorem strongCoprimalityPrimaryQuotient_local_equiv_polar {ω : PontryaginDual C₁}
    (hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F)))
    (hω : NormOneCharacterUnramifiedOutside ω S)
    (hopen : IsOpenQuotientMap (fun f : Pₛ ↦ (K(ω)).mkQ insertPolar(f))) :
    let η := sLocalNormOneCharacter S ω hω
    ∃ e : (↥Pₛ ⧸ Kₛ(η)) ≃L[ℂ] StrongCoprimalityThetaSpace ω,
      ∀ f : Pₛ, e ((Kₛ(η)).mkQ f) = (K(ω)).mkQ insertPolar(f) := by
  intro η
  obtain ⟨equiv, hU⟩ := sLocalHomogeneousThetaToGlobal_equiv_of_unramified (F := F) hPic hω
  let I : Pₛ →ₗ[ℂ] P :=
    ((sAdeleSchwartzToGlobal F S).domRestrict Pₛ).codRestrict P
      (fun f ↦ sAdeleSchwartzToGlobal_mem_polarSubspace f)
  let A := (K(ω)).mkQ.comp I
  have heq (f g : Pₛ) : (Kₛ(η)).mkQ f = (Kₛ(η)).mkQ g ↔ A f = A g := by
    rw [strongCoprimalityPrimaryQuotient_local_equiv_mk]
    change _ ↔ (K(ω)).mkQ (I f) = (K(ω)).mkQ (I g)
    rw [strongCoprimalityPrimaryQuotient_local_equiv_mk]
    have e (z : Pₛ) : equiv ((sLocalHomogeneousAdelicThetaLinearMap F S η).ker.mkQ z.val) =
        (homogeneousAdelicThetaLinearMap F ω).ker.mkQ (I z).val :=
      (LinearMap.congr_fun hU _).trans (sLocalHomogeneousThetaToGlobal_mk hω z.val)
    rw [← e, ← e, equiv.injective.eq_iff]
  let K := Kₛ(η)
  let lift := K.liftQ A (fun x hx ↦ by
    rw [LinearMap.mem_ker, ← A.map_zero]
    exact (heq x 0).mp ((Submodule.Quotient.mk_eq_zero K).mpr hx |>.trans K.mkQ.map_zero.symm))
  have hB (x : Pₛ) : lift (K.mkQ x) = A x := rfl
  have hbij : Bijective lift := by
    refine ⟨?_, fun y ↦ ?_⟩
    · rintro x y h
      obtain ⟨a, rfl⟩ := K.mkQ_surjective x
      obtain ⟨b, rfl⟩ := K.mkQ_surjective y
      exact (heq a b).mpr h
    · obtain ⟨f, hf⟩ := hopen.surjective y
      exact ⟨K.mkQ f, hf⟩
  let e := LinearEquiv.ofBijective lift hbij
  have hA : IsOpenQuotientMap (fun x ↦ lift (K.mkQ x)) := hopen
  have hcont := K.isQuotientMap_mkQL.continuous_iff.mpr hA.continuous
  have hopen' : IsOpenMap lift := by
    intro t ht
    have ht' := hA.isOpenMap _ (K.mkQL.continuous.isOpen_preimage _ ht)
    change IsOpen ((fun x ↦ lift (K.mkQ x)) '' (K.mkQ ⁻¹' t)) at ht'
    simpa only [← Set.image_image, Set.image_preimage_eq _ K.mkQ_surjective] using ht'
  exact ⟨⟨e, hcont, (e.toEquiv.toHomeomorphOfContinuousOpen hcont hopen').symm.continuous⟩, hB⟩

/-- A bijection carrying a family of generators to the corresponding family transports
their spans. It suffices that the global operation respects equality of classes. -/
private theorem strongCoprimalityPrimaryQuotient_local_equiv_span {X Y A C : Type*}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (e : X →ₗ[ℂ] Y) (q : A → X) (r : C → Y) (i : A → C)
    (u : A → A) (v : C → C) (hq : Surjective q) (he : Surjective e)
    (hi : ∀ x, e (q x) = r (i x)) (hc : ∀ x, e (q (u x)) = r (v (i x)))
    (hv : ∀ a b, r a = r b → r (v a) = r (v b)) :
    (Submodule.span ℂ (range fun x ↦ q (u x))).map e =
      Submodule.span ℂ (range fun x ↦ r (v x)) := by
  rw [Submodule.map_span, ← range_comp]
  congr 1
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨i x, (hc x).symm⟩
  · rintro ⟨b, rfl⟩
    obtain ⟨z, hz⟩ := he (r b)
    obtain ⟨x, rfl⟩ := hq z
    exact ⟨x, (hc x).trans (hv _ _ ((hi x).symm.trans hz))⟩

/-- A continuous map with finite-dimensional range is strict. Strictness can therefore
be exchanged across the two kernels to restrict an open quotient to zero-moment tests. -/
private theorem strongCoprimalityPrimaryQuotient_local_equiv_strict {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [ContinuousSMul ℂ X] [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    [IsTopologicalAddGroup Y] (q : X →ₗ[ℂ] Y) (hq : IsOpenQuotientMap q)
    (p : X →L[ℂ] ℂ × ℂ) (hp : Surjective p) :
    IsOpenMap (q.comp p.ker.subtype).rangeRestrict := by
  have hpq : IsOpenQuotientMap p.toLinearMap :=
    AddMonoidHom.isOpenQuotientMap_of_isQuotientMap (p.isQuotientMap_of_finiteDimensional (LinearMap.range_eq_top.mpr hp))
  have hk : IsStrictMap (p.toLinearMap.comp q.ker.subtype) :=
    (p.comp q.ker.subtypeL).isStrictMap_of_finiteDimensional
  have h := (isStrictMap_comp_ker_subtype_iff p.toLinearMap q hpq hq).mp hk
  exact (LinearMap.isStrictMap_iff_isOpenQuotientMap_rangeRestrict.mp h).isOpenMap

/-- Openness onto the range of a continuous injection detects openness on its domain. -/
private theorem strongCoprimalityPrimaryQuotient_local_equiv_open {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (a : X → Y) (b : Y → Z) (ha : Surjective a) (hb : Continuous b) (hi : Injective b)
    (h : IsOpenMap (rangeFactorization (b ∘ a))) : IsOpenMap a := by
  let j (y : Y) : range (b ∘ a) :=
    ⟨b y, (ha y).imp fun x hx ↦ congrArg b hx⟩
  have hc : Continuous j := hb.subtype_mk _
  intro u hu
  have he : a '' u = j ⁻¹' ((rangeFactorization (b ∘ a)) '' u) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, hxy⟩
      exact ⟨x, hx, hi (congrArg Subtype.val hxy)⟩
  exact he ▸ hc.isOpen_preimage _ (h u hu)

local notation "Xₛ" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "qω(" ω ")" => (homogeneousAdelicThetaLinearMap F ω).ker.mkQ

/-- The inserted unrestricted S-local tests cover a complete unramified theta component
when the S-integer Picard group is trivial. -/
private theorem strongCoprimalityPrimaryQuotient_local_equiv_unrestricted
    {ω : PontryaginDual C₁} (hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F)))
    (hω : NormOneCharacterUnramifiedOutside ω S) :
    IsOpenQuotientMap ((qω(ω)).comp (sAdeleSchwartzToGlobal F S)) := by
  let η := sLocalNormOneCharacter S ω hω
  let σ := sLocalHomogeneousAdelicThetaLinearMap F S η
  obtain ⟨equiv, he⟩ := sLocalHomogeneousThetaToGlobal_equiv_of_unramified (F := F) hPic hω
  have h := equiv.toHomeomorph.isOpenQuotientMap.comp σ.ker.isOpenQuotientMap_mkQL
  have hh : (⇑equiv.toHomeomorph ∘ ⇑σ.ker.mkQL) =
      ((qω(ω)).comp (sAdeleSchwartzToGlobal F S)) := funext fun f ↦
    (LinearMap.congr_fun he _).trans (sLocalHomogeneousThetaToGlobal_mk hω f)
  exact hh ▸ h

/-- Two surjections onto the same finite-dimensional space have equal kernels if one
kernel contains the other: the induced endomorphism is surjective and thus injective. -/
private theorem strongCoprimalityPrimaryQuotient_local_equiv_kernels {X : Type*}
    [AddCommGroup X] [Module ℂ X] (l p : X →ₗ[ℂ] ℂ × ℂ)
    (hl : Surjective l) (hp : Surjective p) (hle : l.ker ≤ p.ker) : p.ker = l.ker := by
  let t := (l.ker.liftQ p hle).comp (l.quotKerEquivOfSurjective hl).symm.toLinearMap
  have ht (x : X) : t (l x) = p x := by
    change l.ker.liftQ p hle ((l.quotKerEquivOfSurjective hl).symm (l x)) = p x
    rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
    rfl
  have hs : Surjective t := fun y ↦ (hp y).elim fun x hx ↦ ⟨l x, (ht x).trans hx⟩
  refine le_antisymm (fun x hx ↦ ?_) hle
  apply LinearMap.injective_iff_surjective.mpr hs
  exact (ht x).trans (hx.trans t.map_zero.symm)

/-- The global residue map on the trivial component, composed with local insertion,
is a continuous surjection to both residues, with kernel the local polar tests. -/
private theorem strongCoprimalityPrimaryQuotient_local_equiv_residues
    (hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F))) :
    ∃ (R : GlobalHomogeneousThetaSpace F 1 →L[ℂ] ℂ × ℂ) (p : Xₛ →L[ℂ] ℂ × ℂ),
      (∀ f, p f = R ((qω(1)) (sAdeleSchwartzToGlobal F S f))) ∧
      p.ker = Pₛ ∧ Surjective p ∧ ∀ g : P, R ((qω(1)) g.val) = 0 := by
  obtain ⟨R, hR, _, hopen, _⟩ := globalConverse_normTwist_exact (F := F)
  have htriv : NormOneCharacterUnramifiedOutside (F := F) 1 S :=
    ⟨⟨1, (mem_unramifiedOutside_iff F S 1).mpr (fun _ _ _ ↦ rfl)⟩, fun _ ↦ rfl⟩
  let q := (qω(1)).comp (sAdeleSchwartzToGlobal F S)
  have hq := strongCoprimalityPrimaryQuotient_local_equiv_unrestricted hPic htriv
  let p := R.comp (⟨q, hq.continuous⟩ : Xₛ →L[ℂ] _)
  have hp : Surjective p := hopen.surjective.comp hq.surjective
  have hz (g : P) : R ((qω(1)) g.val) = 0 := by
    obtain ⟨h₁, h₂⟩ := (mem_adelePolarSubspace _).mp g.property
    rw [hR, h₁, h₂, mul_zero, mul_zero, Prod.zero_eq_mk]
  refine ⟨R, p, fun _ ↦ rfl, ?_, hp, hz⟩
  let l := (sAdelePolarValues_isLinear (F := F) (S := S)).mk' _
  have hl : Surjective l := by
    intro y
    obtain ⟨f, _, hf, hF⟩ := sLocalPWTests_moments_surjective (F := F) (T := S)
      (Finset.Subset.refl S) univ Filter.univ_mem y.1 y.2
    exact ⟨f, Prod.ext hf hF⟩
  change p.toLinearMap.ker = l.ker
  apply strongCoprimalityPrimaryQuotient_local_equiv_kernels l _ hl hp
  exact fun x hx ↦ hz ⟨_, sAdeleSchwartzToGlobal_mem_polarSubspace (⟨x, hx⟩ : Pₛ)⟩

/-- Each norm-one class has an idelic representative integral and invertible outside S
when the S-integer Picard group is trivial. -/
private theorem strongCoprimalityPrimaryQuotient_local_equiv_unit
    (hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F))) (k : C₁) :
    ∃ u : (integralAdelesOutside F S)ˣ, QuotientGroup.mk (integralIdeleInsertion F S u) = k.val := by
  obtain ⟨e⟩ := (sIdeleClassInsertion_cokernel F S).1
  let : Subsingleton (C𝔽 ⧸ (sIdeleClassInsertion F S).range) := e.toEquiv.subsingleton
  have hk : k.val ∈ (sIdeleClassInsertion F S).range :=
    (QuotientGroup.eq_one_iff k.val).mp (Subsingleton.elim (QuotientGroup.mk k.val) 1)
  obtain ⟨x, hx⟩ := hk
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective _ x
  exact ⟨u, hx⟩

/-- Translating a local test by an S-integral representative of a norm-one class
multiplies its inserted homogeneous theta class by the value of the character. -/
private theorem strongCoprimalityPrimaryQuotient_local_equiv_translate
    (ω : PontryaginDual C₁) (k : C₁) (u : (integralAdelesOutside F S)ˣ)
    (hu : QuotientGroup.mk (integralIdeleInsertion F S u) = k.val) (f : Xₛ) :
    let g := integralIdeleInsertion F S u
    let v := Units.map (adeleProjection F S).toMonoidHom g
    let i := sAdeleSchwartzToGlobal F S
    (qω(ω)) (i (schwartzBruhatUnitTranslate v f)) = (ω k : ℂ) • (qω(ω)) (i f) := by
  intro g v i
  let t := schwartzBruhatUnitTranslate v f
  let G := schwartzBruhatUnitTranslate g (i f)
  let θ := adelicThetaLinearMap F
  have he : θ.ker.mkQ (i t) = θ.ker.mkQ G := sLocalThetaToGlobal_equivariant u f
  have hθ : θ (i t) = θ G := by
    simpa only [Submodule.mkQ_apply, Submodule.Quotient.eq, LinearMap.mem_ker, map_sub, sub_eq_zero] using he
  have ht (a : C𝔽) : adelicTheta (i t) a = adelicTheta (i f) ((QuotientGroup.mk g)⁻¹ * a) := by
    refine (congrArg (fun q ↦ (q : C(C𝔽, ℂ)) a) hθ).trans ?_
    change adelicTheta G a = _
    induction a using QuotientGroup.induction_on with | H x => ?_
    change adelicTheta G (QuotientGroup.mk x) = adelicTheta (i f) (QuotientGroup.mk (g⁻¹ * x))
    rw [adelicTheta_mk, adelicTheta_mk]
    exact tsum_congr fun z ↦ congrArg (fun y ↦ i f (Multiplicative.ofAdd y))
      (mul_left_comm g.inv (algebraMap F 𝔸[F] (z : F)) x.val)
  rw [← map_smul]
  change Submodule.Quotient.mk (p := (homogeneousAdelicThetaLinearMap F ω).ker) (i t) =
    Submodule.Quotient.mk ((ω k : ℂ) • i f)
  rw [Submodule.Quotient.eq, LinearMap.mem_ker, map_sub, map_smul, sub_eq_zero]
  apply ContinuousMap.ext
  intro a
  change homogeneousAdelicTheta ω (i t) a = (ω k : ℂ) * homogeneousAdelicTheta ω (i f) a
  rw [← homogeneousAdelicTheta_homogeneous]
  apply MeasureTheory.integral_congr_ae (.of_forall fun j ↦ ?_)
  have hh : (QuotientGroup.mk g)⁻¹ * (j.val * a) = j.val * (k.val⁻¹ * a) := by
    rw [hu, mul_left_comm]
  exact congrArg (· * (ω j : ℂ)) ((ht (j.val * a)).trans (congrArg (adelicTheta (i f)) hh))

/-- On a nontrivial character, a normalized translate-minus-identity keeps the homogeneous
class and kills the two trivial-character residues. -/
private theorem strongCoprimalityPrimaryQuotient_local_equiv_adjust {X Y Z E : Type*}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Z] [Module ℂ Z] [AddCommGroup E] [Module ℂ E]
    (q : X →ₗ[ℂ] Y) (q₁ : X →ₗ[ℂ] Z) (R : Z →ₗ[ℂ] E) (c : ℂ) (hc : c ≠ 1)
    (f t : X) (hf : q t = c • q f) (ht : q₁ t = q₁ f) :
    ∃ b : X, R (q₁ b) = 0 ∧ q b = q f := by
  refine ⟨(c - 1)⁻¹ • (t - f), ?_, ?_⟩
  · rw [map_smul, map_sub, ht, sub_self, smul_zero, map_zero]
  · have hx : (c - 1) • q f = c • q f - q f := by rw [sub_smul, one_smul]
    rw [map_smul, map_sub, hf, ← hx, inv_smul_smul₀ (sub_ne_zero.mpr hc)]

/-- Every globally polar test has the same homogeneous theta class as an inserted
S-local test with vanishing moments. The trivial character detects polar tests by
the two residues, and a nontrivial character admits a normalized unit difference. -/
private theorem strongCoprimalityPrimaryQuotient_local_equiv_representative
    (ω : PontryaginDual C₁) (hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F)))
    (hω : NormOneCharacterUnramifiedOutside ω S) (g : P) :
    ∃ f : Pₛ, (qω(ω)) (sAdeleSchwartzToGlobal F S f.val) = (qω(ω)) g.val := by
  let i := sAdeleSchwartzToGlobal F S
  let q := (qω(ω)).comp i
  obtain ⟨R, p, hp, hk, _, hz⟩ := strongCoprimalityPrimaryQuotient_local_equiv_residues hPic
  obtain ⟨f, hf⟩ := (strongCoprimalityPrimaryQuotient_local_equiv_unrestricted hPic hω).surjective ((qω(ω)) g.val)
  by_cases h : ω = 1
  · subst ω
    refine ⟨⟨f, hk ▸ ?_⟩, hf⟩
    exact (hp f).trans ((congrArg R hf).trans (hz g))
  · have hex : ∃ k : C₁, (ω k : ℂ) ≠ 1 :=
      not_forall.mp fun hall ↦ h (PontryaginDual.ext fun x ↦ Subtype.ext (hall x))
    obtain ⟨k, hc⟩ := hex
    obtain ⟨u, hu⟩ := strongCoprimalityPrimaryQuotient_local_equiv_unit hPic k
    have h1 := strongCoprimalityPrimaryQuotient_local_equiv_translate (F := F) 1 k u hu f
    dsimp only at h1
    simp only [show (((1 : PontryaginDual C₁) k : Circle) : ℂ) = 1 from rfl, one_smul] at h1
    obtain ⟨b, hb, hq⟩ := strongCoprimalityPrimaryQuotient_local_equiv_adjust q
      ((qω(1)).comp i) R.toLinearMap (ω k : ℂ) hc f _
      (strongCoprimalityPrimaryQuotient_local_equiv_translate ω k u hu f) h1
    exact ⟨⟨b, hk ▸ (hp b).trans hb⟩, hq.trans hf⟩

/-- The open quotient on unrestricted tests remains open on the two-moment kernels.
The only algebraic input is that polar global classes admit polar S-local representatives. -/
private theorem strongCoprimalityPrimaryQuotient_local_equiv_openPolar
    (ω : PontryaginDual C₁) (hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F)))
    (hω : NormOneCharacterUnramifiedOutside ω S) :
    IsOpenQuotientMap (fun f : Pₛ ↦ (K(ω)).mkQ insertPolar(f)) := by
  let θ := homogeneousAdelicThetaLinearMap F ω
  let q := θ.ker.mkQ.comp (sAdeleSchwartzToGlobal F S)
  have hq := strongCoprimalityPrimaryQuotient_local_equiv_unrestricted hPic hω
  obtain ⟨_, p, _, hker, hp, _⟩ := strongCoprimalityPrimaryQuotient_local_equiv_residues hPic
  have ho : IsOpenMap (q.comp (Pₛ).subtype).rangeRestrict := by
    rw [← hker]
    exact strongCoprimalityPrimaryQuotient_local_equiv_strict q hq p hp
  let I : Pₛ →ₗ[ℂ] P :=
    ((sAdeleSchwartzToGlobal F S).domRestrict Pₛ).codRestrict P
      (fun f ↦ sAdeleSchwartzToGlobal_mem_polarSubspace f)
  let A := (K(ω)).mkQ.comp I
  have ha : Surjective A := by
    intro y
    obtain ⟨g, rfl⟩ := (K(ω)).mkQ_surjective y
    obtain ⟨f, hf⟩ := strongCoprimalityPrimaryQuotient_local_equiv_representative ω hPic hω g
    exact ⟨f, (strongCoprimalityPrimaryQuotient_local_equiv_mk _ _ _ _).mpr hf⟩
  let j := (K(ω)).liftQL (θ.ker.mkQL.comp (P).subtypeL) fun f hf ↦
    (Submodule.Quotient.mk_eq_zero θ.ker).mpr hf
  have hi : Injective j := by
    intro x y h
    obtain ⟨f, rfl⟩ := (K(ω)).mkQ_surjective x
    obtain ⟨g, rfl⟩ := (K(ω)).mkQ_surjective y
    exact (strongCoprimalityPrimaryQuotient_local_equiv_mk _ _ _ _).mpr h
  have hA : Continuous A := (K(ω)).mkQL.continuous.comp
    (((sAdeleSchwartzToGlobal_isEmbedding F S).continuous.comp continuous_subtype_val).subtype_mk
      (fun f ↦ sAdeleSchwartzToGlobal_mem_polarSubspace f))
  exact ⟨ha, hA, strongCoprimalityPrimaryQuotient_local_equiv_open A j ha j.continuous hi ho⟩

/-- Paper: Remark 7.5.0.2 and Equations (7.5.0.15)–(7.5.0.16), pp. 378–379.
Insertion of the outside integer indicators gives the primary quotient isomorphism
once the norm-one character is unramified outside S and the S-integer Picard group is trivial.
Deviation: S includes the selected primary places. The denominator uses the same S-adelic
space as the numerator, with all archimedean places implicit. -/
theorem strongCoprimalityPrimaryQuotient_local_equiv (ω : PontryaginDual C₁) (p : Vℚ)
    (hp : (finite_nuclearityPlacesAbove (F := F) p).toFinset ⊆ S)
    (_hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F)))
    (hω : NormOneCharacterUnramifiedOutside ω S) :
    let T := (finite_nuclearityPlacesAbove (F := F) p).toFinset
    let η : PontryaginDual J₁ := sLocalNormOneCharacter S ω hω
    let Dₛ := Submodule.span ℂ (range fun f : Pₛ ↦
      (Submodule.Quotient.mk ⟨sAdelePrincipalValue F hp f.val,
        strongCoprimalityLocalPrincipalValue_mem_polar hp f⟩ : ↥Pₛ ⧸ Kₛ(η)))
    let D := strongCoprimalityDenominator ω T
    ∃ e : ((↥Pₛ ⧸ Kₛ(η)) ⧸ Dₛ) ≃L[ℂ] (StrongCoprimalityThetaSpace ω ⧸ D),
      ∀ f : Pₛ, e (Dₛ.mkQ ((Kₛ(η)).mkQ f)) = D.mkQ ((K(ω)).mkQ
        ⟨sAdeleSchwartzToGlobal F S f.val, sAdeleSchwartzToGlobal_mem_polarSubspace f⟩) := by
  intro T η Dₛ D
  obtain ⟨e, he⟩ := strongCoprimalityPrimaryQuotient_local_equiv_polar _hPic hω
    (strongCoprimalityPrimaryQuotient_local_equiv_openPolar ω _hPic hω)
  have hn : T.Nonempty := by
    have := p.isMaximal
    obtain ⟨q, hq, hqp⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 F) p.asIdeal
    let v : V := ⟨q, hq.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot p.ne_bot q⟩
    exact ⟨v, (finite_nuclearityPlacesAbove p).mem_toFinset.mpr (HeightOneSpectrum.ext hqp.over.symm)⟩
  let localPV (f : Pₛ) : Pₛ := ⟨sAdelePrincipalValue F hp f.val,
    strongCoprimalityLocalPrincipalValue_mem_polar hp f⟩
  let globalPV (f : P) : P := ⟨adelePrincipalValue F T f.val,
    strongCoprimalityPrincipalValue_mem_polar T f⟩
  have commute (f : Pₛ) : e ((Kₛ(η)).mkQ (localPV f)) = (K(ω)).mkQ (globalPV insertPolar(f)) :=
    by
      rw [he]
      with_reducible_and_instances exact strongCoprimalityPrimaryQuotient_local_equiv_commutes ω hp hn f
  have hglobal (a b : P) (hab : (K(ω)).mkQ a = (K(ω)).mkQ b) :
      (K(ω)).mkQ (globalPV a) = (K(ω)).mkQ (globalPV b) := by
    apply (strongCoprimalityPrimaryQuotient_local_equiv_mk _ _ _ _).mpr
    exact strongCoprimalityPrimaryQuotient_local_equiv_PV ω T _ _
      ((strongCoprimalityPrimaryQuotient_local_equiv_mk _ _ _ _).mp hab)
  have hmap : Dₛ.map e.toLinearMap = D := by
    dsimp only [Dₛ, D, strongCoprimalityDenominator]
    change (Submodule.span ℂ (range fun f ↦ (Kₛ(η)).mkQ (localPV f))).map e.toLinearMap =
      Submodule.span ℂ (range fun f ↦ (K(ω)).mkQ (globalPV f))
    exact strongCoprimalityPrimaryQuotient_local_equiv_span e.toLinearMap (Kₛ(η)).mkQ
        (K(ω)).mkQ (fun f : Pₛ ↦ insertPolar(f)) localPV globalPV (Kₛ(η)).mkQ_surjective
        e.surjective he commute hglobal
  refine ⟨e.quotientMapEquiv Dₛ D hmap, fun f ↦ ?_⟩
  change D.mkQ (e ((Kₛ(η)).mkQ f)) = _
  exact congrArg D.mkQ (he f)

end SLocal

open TopologicalSpace Filter MeasureTheory in
open scoped Uniformity in
/-- Count overlapping lattices with multiplicity, preserving the character coordinate. -/
private theorem strongCoprimalityPrimaryQuotient_sequence_indices {α : Type*} {N : ℕ}
    (f : Fin N → ℤ → α) (hf : ∀ k, Injective (f k))
    (I : α → Finset (Fin N)) (hI : ∀ ξ k, k ∈ I ξ ↔ ξ ∈ range (f k)) :
    ∃ e : (Fin N × ℤ) ≃ {j : α × ℕ // j.2 < (I j.1).card},
      ∀ p, (e p).val.1 = f p.1 p.2 := by
  classical
  let J := {j : α × ℕ // j.2 < (I j.1).card}
  let g (p : Fin N × ℤ) := f p.1 p.2
  let q (j : J) := j.val.1
  have fiber (ξ : α) : {p // g p = ξ} ≃ {j // q j = ξ} := by
    let a : {p // g p = ξ} → ↥(I ξ) := fun p ↦
      ⟨p.val.1, (hI ξ p.val.1).mpr ⟨p.val.2, p.property⟩⟩
    have ha : Bijective a := by
      constructor
      · intro p r h
        have hk : p.val.1 = r.val.1 := congrArg Subtype.val h
        apply Subtype.ext
        apply Prod.ext hk
        apply hf r.val.1
        exact (congrArg (fun k ↦ f k p.val.2) hk).symm.trans
          (p.property.trans r.property.symm)
      · intro k
        obtain ⟨n, hn⟩ := (hI ξ k.val).mp k.property
        exact ⟨⟨(k.val, n), hn⟩, rfl⟩
    let b : Fin (I ξ).card ≃ {j // q j = ξ} :=
      { toFun r := ⟨⟨(ξ, r.val), r.isLt⟩, rfl⟩
        invFun j := ⟨j.val.val.2, by simpa only [← j.property] using j.val.property⟩
        left_inv _ := rfl
        right_inv := by
          intro j
          apply Subtype.ext
          apply Subtype.ext
          exact Prod.ext j.property.symm rfl }
    exact (Equiv.ofBijective a ha).trans ((Fintype.equivFinOfCardEq
      (Fintype.card_coe (I ξ))).trans b)
  exact ⟨Equiv.ofFiberEquiv fiber, Equiv.ofFiberEquiv_map fiber⟩
open TopologicalSpace Filter MeasureTheory in
open scoped Uniformity in
/-- Rapidly decreasing coefficients synthesize polynomially growing vectors continuously. -/
private theorem strongCoprimalityPrimaryQuotient_sequence_synthesis {X : Type*} [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℂ X] [T2Space X]
    {ι : Type*} {p : ι → Seminorm ℂ X} (hX : IsFrechetTVS X) (hp : WithSeminorms p)
    (b : ℕ → X)
    (hgrowth : ∀ i, ∃ (C : ℝ) (k : ℕ), ∀ n, p i (b n) ≤ C * latticeWeight n ^ k) :
    ∃ A : RapidDecaySequence 1 →L[ℂ] X, ∀ a,
      Summable (fun n ↦ a (latticeIndex n) • b n) ∧
      A a = ∑' n, a (latticeIndex n) • b n := by
  classical
  let : UniformSpace X := IsTopologicalAddGroup.rightUniformSpace X
  have : IsUniformAddGroup X := isUniformAddGroup_of_addCommGroup
  obtain ⟨_, _, hmet, hcomplete⟩ := hX
  let : PolynormableSpace ℂ X := hp.toPolynormableSpace
  let R := RapidDecaySequence 1
  have hR : IsFrechetTVS R := rapidDecaySequence_isFrechet
  let : MetrizableSpace R := hR.2.2.1
  let : BarrelledSpace ℂ R := isFrechetTVS_barrelled hR
  let coord (n : ℕ) : R →L[ℂ] ℂ :=
    { toFun a := a (latticeIndex n), map_add' _ _ := rfl, map_smul' _ _ := rfl,
      cont := rapidCoordinate_continuous n }
  let t (a : R) (n : ℕ) := coord n a • b n
  have ht (a : R) : Summable (t a) := by
    apply summable_iff_cauchySeq_finset.mpr
    rw [CauchySeq, cauchy_map_iff', uniformity_eq_comap_nhds_zero, Filter.tendsto_comap_iff,
      hp.tendsto_nhds]
    intro i ε hε
    obtain ⟨C, k, hC⟩ := hgrowth i
    let j : X →ₗ[ℂ] LocalBanach (p i) := UniformSpace.Completion.toComplL.toLinearMap.comp LinearMap.id
    have hj (x : X) : ‖j x‖ = p i x := localBanach_norm_coe (p i) x
    have hsum : Summable (fun n ↦ j (t a n)) := by
      apply Summable.of_norm
      apply (((rapidSequence_mem_iff a.val).mp a.property k).mul_left C).of_nonneg_of_le
        (fun _ ↦ norm_nonneg _)
      intro n
      rw [hj, show p i (t a n) = ‖coord n a‖ * p i (b n) from map_smul_eq_mul ..]
      calc
        _ ≤ ‖coord n a‖ * (C * latticeWeight n ^ k) := mul_le_mul_of_nonneg_left (hC n) (norm_nonneg _)
        _ = _ := by change _ = C * (latticeWeight n ^ k * ‖coord n a‖); ring
    have ht' := cauchy_map_iff'.mp (summable_iff_cauchySeq_finset.mp hsum)
    rw [tendsto_uniformity_iff_dist_tendsto_zero, Metric.tendsto_nhds] at ht'
    filter_upwards [ht' ε hε] with z hz
    rw [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg, dist_eq_norm', ← map_sum, ← map_sum,
      ← map_sub, hj] at hz
    simpa only [sub_zero, Function.comp_apply] using hz
  let synthesisSum (N : ℕ) := ∑ n ∈ Finset.range N, (coord n).smulRight (b n)
  have htend : Filter.Tendsto (fun N a ↦ synthesisSum N a) Filter.atTop (𝓝 (fun a ↦ ∑' n, t a n)) := by
    apply tendsto_pi_nhds.mpr
    intro a
    simpa only [synthesisSum, sum_apply, ContinuousLinearMap.smulRight_apply] using (ht a).hasSum.tendsto_sum_nat
  let A : R →L[ℂ] X := continuousLinearMapOfTendsto synthesisSum htend
  exact ⟨A, fun a ↦ ⟨ht a, rfl⟩⟩
open TopologicalSpace Filter MeasureTheory in
open scoped Uniformity in
/-- Finite lattice synthesis is bijective for separating biorthogonal coordinates. -/
private theorem strongCoprimalityPrimaryQuotient_sequence_finiteSynthesis {X : Type*} [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℂ X] [T2Space X]
    {ι : Type*} {p : ι → Seminorm ℂ X} (hX : IsFrechetTVS X) (hp : WithSeminorms p)
    {N : ℕ} (b : Fin N × ℕ → X) (c : Fin N × ℕ → StrongDual ℂ X)
    (hortho : ∀ j k, c j (b k) = if j = k then 1 else 0)
    (hsep : ∀ x, (∀ j, c j x = 0) → x = 0)
    (hgrowth : ∀ k i, ∃ (C : ℝ) (d : ℕ), ∀ n, p i (b (k,n)) ≤ C * latticeWeight n ^ d)
    (hdecay : ∀ (x : X) k, ∃ a : RapidDecaySequence 1, ∀ n, a (latticeIndex n) = c (k,n) x) :
    ∃ A : (Fin N → RapidDecaySequence 1) →L[ℂ] X, Bijective A := by
  classical
  let source (k : Fin N) := strongCoprimalityPrimaryQuotient_sequence_synthesis hX hp (fun n ↦ b (k,n)) (hgrowth k)
  let S (k : Fin N) : RapidDecaySequence 1 →L[ℂ] X := (source k).choose
  have hS (k : Fin N) (a : RapidDecaySequence 1) :
      Summable (fun n ↦ a (latticeIndex n) • b (k,n)) ∧
      S k a = ∑' n, a (latticeIndex n) • b (k,n) := (source k).choose_spec a
  have hcoord (j : Fin N × ℕ) (k : Fin N) (a : RapidDecaySequence 1) :
      c j (S k a) = if j.1 = k then a (latticeIndex j.2) else 0 := by
    rw [(hS k a).2, (c j).map_tsum (hS k a).1]
    simp only [map_smul, hortho, smul_eq_mul, mul_ite, mul_one, mul_zero]
    by_cases h : j.1 = k
    · subst k
      simp only [Prod.ext_iff, true_and, ↓reduceIte]
      simpa only [↓reduceIte] using (tsum_eq_single j.2 (fun n hn ↦ by simp [Ne.symm hn]) : (∑' n, if j.2 = n then a (latticeIndex n) else 0) = _)
    · simp [Prod.ext_iff, h]
  let A : (Fin N → RapidDecaySequence 1) →L[ℂ] X :=
    ∑ k : Fin N, (S k).comp (ContinuousLinearMap.proj k)
  have hA (j : Fin N × ℕ) (a : Fin N → RapidDecaySequence 1) :
      c j (A a) = a j.1 (latticeIndex j.2) := by
    simp only [A, sum_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply, map_sum, hcoord]
    simp
  refine ⟨A, ⟨?_, fun x ↦ ?_⟩⟩
  · intro a d he
    funext k
    apply Subtype.ext
    funext i
    obtain ⟨n, rfl⟩ := latticeIndex.surjective i
    exact (hA (k,n) a).symm.trans ((congrArg (c (k,n)) he).trans (hA (k,n) d))
  let a : Fin N → RapidDecaySequence 1 := fun k ↦ (hdecay x k).choose
  refine ⟨a, sub_eq_zero.mp (hsep _ fun j ↦ ?_)⟩
  rw [map_sub]
  have he : c j (A a) = c j x := by
    simp only [A, sum_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
    rw [map_sum]
    simp only [hcoord]
    rw [Finset.sum_eq_single j.1]
    · simpa only [↓reduceIte] using (hdecay x j.1).choose_spec j.2
    · intro k _ hk
      simp [Ne.symm hk]
    · simp
  rw [he, sub_self]
open TopologicalSpace Filter MeasureTheory in
open scoped Uniformity in
/-- Selecting one of finitely many rapid sequences at each index preserves rapid decay. -/
private theorem strongCoprimalityPrimaryQuotient_sequence_select {N : ℕ} (a : Fin N → RapidDecaySequence 1) (r : ℕ → Fin N) :
    ∃ v : RapidDecaySequence 1, ∀ n, v (latticeIndex n) = a (r n) (latticeIndex n) := by
  let v (i : Fin 1 → ℤ) := a (r (latticeIndex.symm i)) i
  have hv : v ∈ rapidDecaySequenceSubmodule 1 := by
    apply (rapidSequence_mem_iff v).mpr
    intro j
    have hs : Summable (fun n ↦ ∑ k : Fin N, latticeWeight n ^ j * ‖a k (latticeIndex n)‖) :=
      summable_sum fun k _ ↦ (rapidSequence_mem_iff (a k).val).mp (a k).property j
    apply hs.of_nonneg_of_le
    · intro n
      exact mul_nonneg (pow_nonneg (le_trans (by norm_num) (latticeWeight_bounds n).1) _) (norm_nonneg _)
    · intro n
      simp only [v, latticeIndex.symm_apply_apply]
      exact Finset.single_le_sum (fun k _ ↦ mul_nonneg
        (pow_nonneg (le_trans (by norm_num) (latticeWeight_bounds n).1) _) (norm_nonneg (a k (latticeIndex n))))
        (Finset.mem_univ (r n))
  exact ⟨⟨v,hv⟩, fun n ↦ by simp only [v, latticeIndex.symm_apply_apply]⟩
open TopologicalSpace Filter MeasureTheory in
open scoped Uniformity in
/-- The moment basis identifies a nonempty commensurate difference quotient with rapid sequences. -/
private theorem strongCoprimalityPrimaryQuotient_sequence_periodic_pos {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m) (hms : Surjective m)
    (ω : PontryaginDual m.toMonoidHom.ker) {N : ℕ} (hN : 0 < N) (γs : Fin N → G)
    (hγs : ∀ k, 1 < (m (γs k)).val) [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure]
    (hcomm : ∃ a : ℝ, 0 < a ∧ ∀ k, ∃ r : ℚ, Real.log ((m (γs k)).val : ℝ) = (r : ℝ) * a) :
    let X := ↥(modulatedDecayIsotype m univ (mem_univ (0 : ℝ)) ω) ⧸
      (modulatedIsotypicDifferenceProduct m hm hms ω univ ordConnected_univ
        (mem_univ (0 : ℝ)) (List.ofFn γs)).range
    ∃ A : (Fin N → RapidDecaySequence 1) →L[ℂ] X, Bijective A := by
  classical
  let X := ↥(modulatedDecayIsotype m univ (mem_univ (0 : ℝ)) ω) ⧸
      (modulatedIsotypicDifferenceProduct m hm hms ω univ ordConnected_univ
        (mem_univ (0 : ℝ)) (List.ofFn γs)).range
  let J := {j : PontryaginDual G × ℕ // j.2 < modulatedPeriodicMultiplicity m ω γs j.1}
  let D : J → StrongDual ℂ X := modulatedQuotientLogMoment m hm hms ω γs hγs μ
  let τ := (exists_surjectiveModulation_section m hm hms).choose
  have hτ := (exists_surjectiveModulation_section m hm hms).choose_spec
  let lift := exists_modulatedCyclicCharacter_lifts m (γs ⟨0,hN⟩) τ hτ (hγs ⟨0,hN⟩)
  let χ := lift.choose
  have hχ : ∀ ω' (u : m.toMonoidHom.ker), χ ω' u.val = ω' u :=
    lift.choose_spec.choose_spec.choose_spec.1
  let phase (k : Fin N) (ω' : PontryaginDual m.toMonoidHom.ker) :=
    (existsUnique_modulatedCharacterPhase m (γs k) (hγs k) (χ ω')).exists
  let t₀ (k : Fin N) (ω' : PontryaginDual m.toMonoidHom.ker) := (phase k ω').choose
  have ht₀ (k : Fin N) (ω' : PontryaginDual m.toMonoidHom.ker) := (phase k ω').choose_spec
  let f (k : Fin N) (n : ℤ) : PontryaginDual G :=
    (PontryaginDual.map (⟨QuotientGroup.mk' (Subgroup.zpowers (γs k)),
        QuotientGroup.continuous_mk⟩ : G →ₜ* (G ⧸ Subgroup.zpowers (γs k)))
      (modulatedCyclicCharacter m (γs k) (hγs k) χ (t₀ k) (ht₀ k) (ω,n)))⁻¹
  have hf (k : Fin N) := modulatedPeriodicFrequency_bijective m hm hms ω γs hγs χ hχ t₀ ht₀ k
  let I (ξ : PontryaginDual G) := Finset.univ.filter (fun k ↦ ξ ∈ modulatedCyclicAnnihilatorFiber m ω (γs k))
  have hI (ξ : PontryaginDual G) (k : Fin N) : k ∈ I ξ ↔ ξ ∈ range (f k) := by
    simp only [I, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [(hf k).2]
  let equiv := strongCoprimalityPrimaryQuotient_sequence_indices f (fun k ↦ (hf k).1) I hI
  let e : (Fin N × ℤ) ≃ J := equiv.choose
  have he (p : Fin N × ℤ) : (e p).val.1 = f p.1 p.2 := equiv.choose_spec p
  let σ := (modulatedPeriodicMomentIndex_enumerable m hm hms ω γs hγs hN).some
  let basis := modulatedQuotientLogMoment_bases m hm hms ω γs hγs μ hcomm σ
  let ψ : J → X := basis.choose
  have hb : IsSchauderBasis (ψ ∘ σ) (D ∘ σ) := basis.choose_spec.1
  have hdiag (j : J) : D j (ψ j) = 1 := by
    simpa using hb.1 (σ.symm j) (σ.symm j)
  have hoff (j k : J) (h : j ≠ k) : D j (ψ k) = 0 := by
    have hh : σ.symm j ≠ σ.symm k := σ.symm.injective.ne h
    simpa [hh] using hb.1 (σ.symm j) (σ.symm k)
  let en : (Fin N × ℕ) ≃ J := (Equiv.prodCongr (Equiv.refl (Fin N)) Equiv.intEquivNat.symm).trans e
  let b : Fin N × ℕ → X := ψ ∘ en
  let c : Fin N × ℕ → StrongDual ℂ X := D ∘ en
  have hprops : SeparableSpace X ∧ IsNuclearTVS.{0} X ∧ IsFrechetTVS X := modulatedIsotypicDifferenceProduct_quotient m hm hms ω (List.ofFn γs)
    (by intro g hg; obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hg; exact hγs k)
  have hX : IsFrechetTVS X := hprops.2.2
  let : PolynormableSpace ℂ X := hX.2.1
  let : MetrizableSpace X := hX.2.2.1
  let : T2Space X := inferInstance
  let p := fun q : {q : Seminorm ℂ X // Continuous q} ↦ q.val
  have hp : WithSeminorms p := PolynormableSpace.withSeminorms ℂ X
  apply strongCoprimalityPrimaryQuotient_sequence_finiteSynthesis hX hp b c
  · intro j k
    by_cases h : j = k
    · subst k; simpa only [b,c,Function.comp_apply,↓reduceIte] using hdiag (en j)
    · simpa only [b,c,Function.comp_apply,ite_eq_right h] using hoff (en j) (en k) (en.injective.ne h)
  · intro x hx
    have hh (n : ℕ) : D (σ n) x = 0 := by simpa only [c,Function.comp_apply,en.apply_symm_apply] using hx (en.symm (σ n))
    have hs := hb.2 x
    simp only [Function.comp_apply, ContinuousLinearMap.coe_coe, hh, zero_smul] at hs
    exact hs.unique hasSum_zero
  · intro k i
    obtain ⟨d, hd⟩ := modulatedQuotientLogMoment_biorthogonal_growth m hm hms ω γs hγs
      χ hχ t₀ ht₀ μ hcomm ψ hdiag hoff (p i) i.property
    obtain ⟨C,hC,hbound⟩ := hd k
    refine ⟨C,d,fun n ↦ ?_⟩
    exact hbound (Equiv.intEquivNat.symm n) (en (k,n)) (he (k,Equiv.intEquivNat.symm n))
  · intro x k
    obtain ⟨u,rfl⟩ := Submodule.mkQ_surjective _ x
    let hs (r : Fin N) := modulatedLogMoment_lattice_schwartz m hm hms ω γs hγs
      χ hχ t₀ ht₀ μ u r k
    let iso := integer_schwartz_sequence
    let a (r : Fin N) : RapidDecaySequence 1 := iso.choose.symm (hs r).choose
    have ha (r : Fin N) (n : ℤ) : a r (fun _ ↦ n) =
        if r.val < modulatedPeriodicMultiplicity m ω γs (f k n) then
          modulatedLogMoment m hm hms ω μ (f k n) r.val u else 0 := by
      have ht := iso.choose_spec (a r) n
      rw [show iso.choose (a r) = (hs r).choose from iso.choose.apply_symm_apply _] at ht
      exact ht.symm.trans ((hs r).choose_spec n)
    have hlt (j : J) : j.val.2 < N := by
      apply j.property.trans_le
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp)
    let r (n : ℕ) : Fin N := ⟨(en (k,n)).val.2, hlt (en (k,n))⟩
    let chooseSeq := strongCoprimalityPrimaryQuotient_sequence_select a r
    refine ⟨chooseSeq.choose, fun n ↦ ?_⟩
    rw [chooseSeq.choose_spec n]
    have hn : latticeIndex n = (fun _ : Fin 1 ↦ Equiv.intEquivNat.symm n) := rfl
    rw [hn, ha]
    have hj : (en (k,n)).val.1 = f k (Equiv.intEquivNat.symm n) := he _
    have hr : (r n).val < modulatedPeriodicMultiplicity m ω γs (f k (Equiv.intEquivNat.symm n)) := by
      rw [← hj]
      exact (en (k,n)).property
    rw [ite_eq_left hr]
    change _ = modulatedQuotientLogMoment m hm hms ω γs hγs μ (en (k,n)) _
    rw [modulatedQuotientLogMoment_mkQ]
    change _ = modulatedLogMoment m hm hms ω μ (en (k,n)).val.1 (en (k,n)).val.2 u
    rw [hj]

open TopologicalSpace Filter MeasureTheory in
open scoped Uniformity in
/-- Include the empty difference product, whose quotient and sequence source are both zero. -/
private theorem strongCoprimalityPrimaryQuotient_sequence_periodic {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m) (hms : Surjective m)
    (ω : PontryaginDual m.toMonoidHom.ker) {N : ℕ} (γs : Fin N → G)
    (hγs : ∀ k, 1 < (m (γs k)).val) [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure]
    (hcomm : ∃ a : ℝ, 0 < a ∧ ∀ k, ∃ r : ℚ, Real.log ((m (γs k)).val : ℝ) = (r : ℝ) * a) :
    let X := ↥(modulatedDecayIsotype m univ (mem_univ (0 : ℝ)) ω) ⧸
      (modulatedIsotypicDifferenceProduct m hm hms ω univ ordConnected_univ
        (mem_univ (0 : ℝ)) (List.ofFn γs)).range
    ∃ A : (Fin N → RapidDecaySequence 1) →L[ℂ] X, Bijective A := by
  by_cases hN : 0 < N
  · exact strongCoprimalityPrimaryQuotient_sequence_periodic_pos m hm hms ω hN γs hγs μ hcomm
  have hN : N = 0 := Nat.eq_zero_of_not_pos hN
  subst N
  let R := (modulatedIsotypicDifferenceProduct m hm hms ω univ ordConnected_univ
    (mem_univ (0 : ℝ)) (List.ofFn γs)).range
  have hr (u : ↥(modulatedDecayIsotype m univ (mem_univ (0 : ℝ)) ω)) : u ∈ R := by
    refine ⟨u, ?_⟩
    simp only [List.ofFn_zero, modulatedIsotypicDifferenceProduct, modulatedDifferenceProduct]
    rfl
  have hz (x : ↥(modulatedDecayIsotype m univ (mem_univ (0 : ℝ)) ω) ⧸ R) : x = 0 := by
    obtain ⟨u,rfl⟩ := R.mkQ_surjective x
    exact (Submodule.Quotient.mk_eq_zero R).mpr (hr u)
  refine ⟨0, ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun x ↦ ⟨0, ?_⟩⟩⟩
  exact (hz x).symm
open TopologicalSpace Filter MeasureTheory in
open scoped Uniformity in
/-- The inverse uniformizer class has norm equal to the residue cardinality. -/
private theorem strongCoprimalityPrimaryQuotient_sequence_norm {F : Type*} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (π : (v.adicCompletion F)ˣ)
    (hπ : Valuation.IsUniformizer
      (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))) π.val) :
    (((ideleClassNorm F ((IdeleClassGroup.ofAdicCompletion (𝓞 F) F v π)⁻¹)).val : ℝ≥0) : ℝ) =
      (Ideal.absNorm v.asIdeal : ℝ) := by
  rw [map_inv, ideleClassNorm_ofAdicCompletion, Units.coe_map_inv]
  change (‖(π⁻¹).val‖₊ : ℝ) = _
  simp only [coe_nnNorm, Units.val_inv_eq_inv_val, norm_inv]
  rw [norm_uniformizer_adicCompletion v _ hπ, inv_inv]
open TopologicalSpace Filter MeasureTheory in
open scoped Uniformity in
/-- Residue cardinalities above one rational prime have commensurate logarithms. -/
private theorem strongCoprimalityPrimaryQuotient_sequence_commensurate {F : Type*} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (p : HeightOneSpectrum (𝓞 ℚ))
    (hv : v.under (𝓞 ℚ) = p) :
    ∃ r : ℚ, Real.log (Ideal.absNorm v.asIdeal : ℝ) =
      (r : ℝ) * Real.log (Ideal.absNorm p.asIdeal : ℝ) := by
  let : v.asIdeal.LiesOver p.asIdeal := ⟨(congrArg HeightOneSpectrum.asIdeal hv).symm⟩
  refine ⟨v.asIdeal.inertiaDeg (𝓞 ℚ), ?_⟩
  rw [← Ideal.absNorm_pow_inertiaDeg p.asIdeal v.asIdeal, Nat.cast_pow, Real.log_pow]
  simp only [Rat.cast_natCast]
open TopologicalSpace Filter MeasureTheory in
open scoped Uniformity in
/-- Extra sequence coordinates may be discarded by a continuous surjection. -/
private theorem strongCoprimalityPrimaryQuotient_sequence_projection {M N : ℕ} (h : M ≤ N) :
    ∃ A : (Fin N → RapidDecaySequence 1) →L[ℂ] (Fin M → RapidDecaySequence 1), Surjective A := by
  classical
  let A : (Fin N → RapidDecaySequence 1) →L[ℂ] (Fin M → RapidDecaySequence 1) :=
    ContinuousLinearMap.pi fun k ↦ ContinuousLinearMap.proj (Fin.castLE h k)
  refine ⟨A, fun a ↦ ?_⟩
  let b (i : Fin N) : RapidDecaySequence 1 := if hi : i.val < M then a ⟨i.val, hi⟩ else 0
  refine ⟨b, funext fun k ↦ ?_⟩
  change (if hi : k.val < M then a ⟨k.val, hi⟩ else 0) = a k
  simp only [dite_eq_left k.isLt]

open TopologicalSpace Filter MeasureTheory in
open scoped Uniformity in
/-- Open mapping identifies a Fréchet target with the quotient by a closed synthesis kernel. -/
private theorem strongCoprimalityPrimaryQuotient_sequence_closedKernel {X : Type*} [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℂ X]
    (hX : IsFrechetTVS X) {N : ℕ}
    (A : (Fin N → RapidDecaySequence 1) →L[ℂ] X) (hA : Surjective A) :
    let E := Fin N → RapidDecaySequence 1
    ∃ (D : Submodule ℂ E) (W : Submodule ℂ (E ⧸ D)),
      IsClosed (D : Set E) ∧ IsClosed (W : Set (E ⧸ D)) ∧ Nonempty (X ≃L[ℂ] W) := by
  let R := RapidDecaySequence 1
  let E := Fin N → R
  obtain ⟨_, _, hm, hc⟩ := (rapidDecaySequence_isFrechet (r := 1))
  let : CompleteSpace R := by rwa [IsUniformAddGroup.rightUniformSpace_eq] at hc
  have hE : IsFrechetTVS E := by
    refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
    rw [IsUniformAddGroup.rightUniformSpace_eq]
    infer_instance
  let : MetrizableSpace X := hX.2.2.1
  let : T2Space X := inferInstance
  have hop : IsOpenMap A := isOpenMap_of_surjective_toLF (isLFSpace_of_isFrechetTVS hX)
    (X := fun _ ↦ E) (fun _ ↦ hE) (fun _ ↦ ContinuousLinearMap.id ℂ E)
    (fun _ ↦ Subset.rfl) (fun a ↦ ⟨0,a,rfl⟩) A hA
  let e := (exists_quotient_equiv_of_kernel A (hop.isQuotientMap A.continuous hA) A.ker rfl).choose
  refine ⟨A.ker, ⊤, A.isClosed_ker, ?_, ?_⟩
  · exact isClosed_univ
  · exact ⟨e.symm.trans (Submodule.topContEquiv (R := ℂ) (M := E ⧸ A.ker)).symm⟩
open TopologicalSpace Filter MeasureTheory in
open scoped Uniformity in
/-- The primary difference quotient has a finite rapid-sequence synthesis model. -/
private theorem strongCoprimalityPrimaryQuotient_sequence_decay {F : Type*} [Field F] [NumberField F]
    (ω : PontryaginDual (ideleClassNorm F).ker) (p : HeightOneSpectrum (𝓞 ℚ))
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : ∀ v ∈ S, v.under (𝓞 ℚ) = p)
    (π : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (hπ : ∀ v ∈ S, Valuation.IsUniformizer
      (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))) (π v).val) :
    ∃ A : (Fin S.card → RapidDecaySequence 1) →L[ℂ]
      (StrongCoprimalityDecaySpace ω ⧸ strongCoprimalityDifferenceRange ω S π), Bijective A := by
  classical
  let G := IdeleClassGroup (𝓞 F) F
  let : T2Space G := (ideleGroup_quotient.{_,0} F).2.2.2.2.2.1
  let : LocallyCompactSpace G := (ideleGroup_quotient.{_,0} F).2.2.2.2.2.2.1
  let : SecondCountableTopology G := by
    let : SecondCountableTopology (IdeleGroup (𝓞 F) F) := idele_secondCountable F
    exact (ideleGroup_quotient.{_,0} F).2.2.2.2.1.secondCountableTopology
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let μ := ideleClassTamagawaMeasure F
  let : μ.IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil F).1
  let m : G →ₜ* ℝ≥0ˣ := ⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩
  have hmod := strongCoprimalityNorm_isModulation_surjective (F := F)
  let a (v : HeightOneSpectrum (𝓞 F)) := (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v (π v))⁻¹
  let γs (k : Fin S.toList.length) := a (S.toList.get k)
  have hnorm (k : Fin S.toList.length) : ((m (γs k)).val : ℝ) =
      (Ideal.absNorm (S.toList.get k).asIdeal : ℝ) :=
    strongCoprimalityPrimaryQuotient_sequence_norm _ _ (hπ _ (Finset.mem_toList.mp (List.get_mem _ _)))
  have hγs (k : Fin S.toList.length) : 1 < (m (γs k)).val := by
    apply NNReal.coe_lt_coe.mp
    rw [NNReal.coe_one, hnorm]
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm (S.toList.get k)
  have hcomm : ∃ t : ℝ, 0 < t ∧ ∀ k, ∃ r : ℚ,
      Real.log ((m (γs k)).val : ℝ) = (r : ℝ) * t := by
    refine ⟨Real.log (Ideal.absNorm p.asIdeal : ℝ), Real.log_pos ?_, fun k ↦ ?_⟩
    · exact_mod_cast HeightOneSpectrum.one_lt_absNorm p
    · rw [hnorm]
      exact strongCoprimalityPrimaryQuotient_sequence_commensurate _ p (hS _ (Finset.mem_toList.mp (List.get_mem _ _)))
  have hlist : List.ofFn γs = S.toList.map a := by
    dsimp only [γs]
    rw [List.ofFn_comp', List.ofFn_get]
  have heq : strongCoprimalityDifferenceRange ω S π =
      (modulatedIsotypicDifferenceProduct m hmod.1 hmod.2 ω univ ordConnected_univ
        (mem_univ (0 : ℝ)) (List.ofFn γs)).range := by
    rw [hlist]
    change _ = fullDecayDifferenceRange m hmod.1 hmod.2 ω (S.toList.map a)
    rw [fullDecayDifferenceRange_eq_span]
    unfold strongCoprimalityDifferenceRange
    congr 1
    ext h
    simp only [List.foldr_map, a, strongCoprimalityDifference]
    rfl
  rw [heq, ← Finset.length_toList S]
  exact strongCoprimalityPrimaryQuotient_sequence_periodic m hmod.1 hmod.2 ω γs hγs μ hcomm
open TopologicalSpace Filter MeasureTheory in
open scoped Uniformity in
/-- Discard ramified places, synthesize the comparison quotient, and transfer by strong coprimality. -/
private theorem strongCoprimalityPrimaryQuotient_sequence_character {F : Type*} [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (p : HeightOneSpectrum (𝓞 ℚ)) :
    let ω := χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ :
      (ideleClassNorm F).ker →ₜ* IdeleClassGroup (𝓞 F) F)
    let S := (finite_nuclearityPlacesAbove (F := F) p).toFinset
    let E := Fin S.card → RapidDecaySequence 1
    ∃ (D : Submodule ℂ E) (W : Submodule ℂ (E ⧸ D)),
      IsClosed (D : Set E) ∧ IsClosed (W : Set (E ⧸ D)) ∧
        Nonempty (StrongCoprimalityQuotient ω S ≃L[ℂ] W) := by
  classical
  let ω := χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ :
      (ideleClassNorm F).ker →ₜ* IdeleClassGroup (𝓞 F) F)
  let S := (finite_nuclearityPlacesAbove (F := F) p).toFinset
  have h (v : HeightOneSpectrum (𝓞 F)) := (Valued.v : Valuation (v.adicCompletion F)
    (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
  let π : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ :=
    fun v ↦ Units.mk0 (h v).choose (h v).choose_spec.ne_zero
  have hπ (v : HeightOneSpectrum (𝓞 F)) : Valuation.IsUniformizer
      (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))) (π v).val :=
    (h v).choose_spec
  let T := S.filter (fun v ↦ (ideleClassNormTwist χ 0).IsUnramifiedAt v)
  have hT (v : HeightOneSpectrum (𝓞 F)) (hv : v ∈ T) : v.under (𝓞 ℚ) = p :=
    (finite_nuclearityPlacesAbove (F := F) p).mem_toFinset.mp (Finset.mem_filter.mp hv).1
  let model := strongCoprimalityPrimaryQuotient_sequence_decay ω p T hT π (fun v _ ↦ hπ v)
  let proj := strongCoprimalityPrimaryQuotient_sequence_projection (Finset.card_filter_le S (fun v ↦ (ideleClassNormTwist χ 0).IsUnramifiedAt v))
  let equiv := (strongCoprimality χ S π (fun v _ ↦ hπ v)).choose
  let A := equiv.symm.toContinuousLinearMap.comp (model.choose.comp proj.choose)
  have hA : Surjective A := equiv.symm.surjective.comp (model.choose_spec.2.comp proj.choose_spec)
  have hNF : IsFrechetTVS (StrongCoprimalityQuotient ω S) ∧
      IsNuclearTVS.{0} (StrongCoprimalityQuotient ω S) :=
    strongCoprimalityPrimaryQuotient_nuclearFrechet ω p
  exact strongCoprimalityPrimaryQuotient_sequence_closedKernel hNF.1 A hA
open TopologicalSpace Filter MeasureTheory in
open scoped Uniformity in
/-- Extend a norm-one character using a section of the idelic norm. -/
private theorem strongCoprimalityPrimaryQuotient_sequence_lift {F : Type*} [Field F] [NumberField F] (ω : PontryaginDual (ideleClassNorm F).ker) :
    ∃ χ : PontryaginDual (IdeleClassGroup (𝓞 F) F), χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : (ideleClassNorm F).ker →ₜ* IdeleClassGroup (𝓞 F) F) = ω := by
  let : T2Space (IdeleClassGroup (𝓞 F) F) := (ideleGroup_quotient.{_,0} F).2.2.2.2.2.1
  let : LocallyCompactSpace (IdeleClassGroup (𝓞 F) F) :=
    (ideleGroup_quotient.{_,0} F).2.2.2.2.2.2.1
  let : SecondCountableTopology (IdeleClassGroup (𝓞 F) F) := by
    let : SecondCountableTopology (IdeleGroup (𝓞 F) F) := idele_secondCountable F
    exact (ideleGroup_quotient.{_,0} F).2.2.2.2.1.secondCountableTopology
  let m : IdeleClassGroup (𝓞 F) F →ₜ* ℝ≥0ˣ :=
    ⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩
  have hmod := strongCoprimalityNorm_isModulation_surjective (F := F)
  obtain ⟨σ, hσ⟩ := exists_surjectiveModulation_section m hmod.1 hmod.2
  have hk (g : IdeleClassGroup (𝓞 F) F) : g / σ (m g) ∈ (ideleClassNorm F).ker := by
    change (ideleClassNorm F) (g / σ (m g)) = 1
    rw [map_div, show ideleClassNorm F (σ (m g)) = m g from hσ (m g)]
    change (ideleClassNorm F g) / (ideleClassNorm F g) = 1
    exact div_self' _
  let q : IdeleClassGroup (𝓞 F) F →ₜ* (ideleClassNorm F).ker :=
    { toFun := fun g ↦ ⟨g / σ (m g), hk g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun g h ↦ Subtype.ext (by simp [mul_div_mul_comm])
      continuous_toFun := (continuous_id.div' (σ.continuous.comp (isProperMap_ideleClassNorm F).continuous)).subtype_mk hk }
  refine ⟨ω.comp q, ?_⟩
  ext1 u
  change ω (q u) = ω u
  congr 1
  apply Subtype.ext
  change u.val / σ ((ideleClassNorm F) u.val) = u.val
  rw [u.property, map_one, div_one]

/-- Paper: Remark 7.5.0.2, p. 379.
The primary quotient is a closed subspace of a Hausdorff quotient of a finite product
of smooth periodic spaces, expressed via their rapidly decreasing Fourier sequences. -/
theorem strongCoprimalityPrimaryQuotient_sequence_subquotient (ω : PontryaginDual C₁) (p : Vℚ) :
    let T := (finite_nuclearityPlacesAbove (F := F) p).toFinset
    let E := Fin T.card → RapidDecaySequence 1
    ∃ (D : Submodule ℂ E) (W : Submodule ℂ (E ⧸ D)),
      IsClosed (D : Set E) ∧ IsClosed (W : Set (E ⧸ D)) ∧
        Nonempty (StrongCoprimalityQuotient ω T ≃L[ℂ] W) := by
  let lift := strongCoprimalityPrimaryQuotient_sequence_lift ω
  let χ := lift.choose
  have hχ := lift.choose_spec
  rw [← hχ]
  exact strongCoprimalityPrimaryQuotient_sequence_character χ p

-- TODO(prerequisite): The separate Köthe-space assertion requires a general
-- Köthe-space model. The example in §C.1.5, p. 667 is unfinished.

open TopologicalSpace in
/-- Coordinate projection has a continuous zero-extension right inverse, including empty products. -/
private theorem strongCoprimalityPrimaryQuotient_strongDual_coordinates {M N : ℕ} (h : M ≤ N) :
    ∃ (proj : (Fin N → RapidDecaySequence 1) →L[ℂ] (Fin M → RapidDecaySequence 1))
      (J : (Fin M → RapidDecaySequence 1) →L[ℂ] (Fin N → RapidDecaySequence 1)), RightInverse J proj := by
  classical
  let proj : (Fin N → RapidDecaySequence 1) →L[ℂ] (Fin M → RapidDecaySequence 1) :=
    ContinuousLinearMap.pi fun k ↦ ContinuousLinearMap.proj (Fin.castLE h k)
  let J : (Fin M → RapidDecaySequence 1) →L[ℂ] (Fin N → RapidDecaySequence 1) :=
    ContinuousLinearMap.pi fun i ↦ if hi : i.val < M then ContinuousLinearMap.proj ⟨i.val, hi⟩ else 0
  refine ⟨proj,J,fun a ↦ funext fun k ↦ ?_⟩
  simp [proj,J,k.isLt]
open TopologicalSpace in
/-- Open mapping upgrades bijective rapid-sequence synthesis to a topological linear equivalence. -/
private theorem strongCoprimalityPrimaryQuotient_strongDual_sequenceEquiv {X : Type*} [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℂ X]
    (hX : IsFrechetTVS X) {N : ℕ}
    (A : (Fin N → RapidDecaySequence 1) →L[ℂ] X) (hA : Bijective A) :
    Nonempty ((Fin N → RapidDecaySequence 1) ≃L[ℂ] X) := by
  let R := RapidDecaySequence 1
  let E := Fin N → R
  obtain ⟨_, _, hm, hc⟩ := (rapidDecaySequence_isFrechet (r := 1))
  let : CompleteSpace R := by rwa [IsUniformAddGroup.rightUniformSpace_eq] at hc
  have hE : IsFrechetTVS E := by
    refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
    rw [IsUniformAddGroup.rightUniformSpace_eq]
    infer_instance
  let : MetrizableSpace X := hX.2.2.1
  let : T2Space X := inferInstance
  have hop : IsOpenMap A := isOpenMap_of_surjective_toLF (isLFSpace_of_isFrechetTVS hX)
    (X := fun _ ↦ E) (fun _ ↦ hE) (fun _ ↦ ContinuousLinearMap.id ℂ E)
    (fun _ ↦ Subset.rfl) (fun a ↦ ⟨0,a,rfl⟩) A hA.2
  let e := LinearEquiv.ofBijective A.toLinearMap hA
  exact ⟨{ e with continuous_toFun := A.continuous, continuous_invFun := e.toEquiv.continuous_symm_iff.mpr hop }⟩
open TopologicalSpace in
/-- Transposing a split surjection identifies its strong dual with a closed complemented subspace. -/
private theorem strongCoprimalityPrimaryQuotient_strongDual_retract {X E : Type*} [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℂ X]
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    (A : E →L[ℂ] X) (J : X →L[ℂ] E) (hAJ : RightInverse J A) :
    ∃ (W : Submodule ℂ (StrongDual ℂ E)) (D : Submodule ℂ W),
      IsClosed (W : Set (StrongDual ℂ E)) ∧ IsClosed (D : Set W) ∧
        Nonempty (StrongDual ℂ X ≃L[ℂ] (W ⧸ D)) := by
  let T : StrongDual ℂ X →L[ℂ] StrongDual ℂ E := A.precomp ℂ
  let R : StrongDual ℂ E →L[ℂ] StrongDual ℂ X := J.precomp ℂ
  have hRT : LeftInverse R T := by
    intro l
    ext x
    change l (A (J x)) = l x
    rw [hAJ x]
  have hclosed : IsClosed (T.range : Set (StrongDual ℂ E)) :=
    hRT.isClosed_range R.continuous T.continuous
  let e := LinearEquiv.ofInjective T.toLinearMap hRT.injective
  have hi : Continuous e.symm := by
    apply (R.continuous.comp continuous_subtype_val).congr
    intro w
    obtain ⟨l,hl⟩ := w.property
    have hw : e l = w := Subtype.ext hl
    rw [← hw, e.symm_apply_apply]
    exact hRT l
  let ec : StrongDual ℂ X ≃L[ℂ] T.range :=
    { e with continuous_toFun := T.continuous.subtype_mk _, continuous_invFun := hi }
  let idW := ContinuousLinearMap.id ℂ T.range
  let eqQ := (exists_ker_quotientEquiv_of_rightInverse idW idW (fun _ ↦ rfl)).choose
  exact ⟨T.range,idW.ker,hclosed,idW.isClosed_ker,⟨ec.trans eqQ.symm⟩⟩
open TopologicalSpace in
/-- Pad the finite sequence model, transpose the retraction, and take the zero-kernel quotient. -/
private theorem strongCoprimalityPrimaryQuotient_strongDual_model {X : Type*} [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℂ X]
    {M N : ℕ} (e : (Fin M → RapidDecaySequence 1) ≃L[ℂ] X) (h : M ≤ N) :
    ∃ (W : Submodule ℂ (StrongDual ℂ (Fin N → RapidDecaySequence 1))) (D : Submodule ℂ W),
      IsClosed (W : Set (StrongDual ℂ (Fin N → RapidDecaySequence 1))) ∧ IsClosed (D : Set W) ∧
        Nonempty (StrongDual ℂ X ≃L[ℂ] (W ⧸ D)) := by
  let ret := strongCoprimalityPrimaryQuotient_strongDual_coordinates h
  let proj := ret.choose
  let J := ret.choose_spec.choose
  have hPJ : RightInverse J proj := ret.choose_spec.choose_spec
  apply strongCoprimalityPrimaryQuotient_strongDual_retract (e.toContinuousLinearMap.comp proj) (J.comp e.symm.toContinuousLinearMap)
  intro x
  change e (proj (J (e.symm x))) = x
  rw [hPJ, e.apply_symm_apply]

open TopologicalSpace in
/-- Use the unramified sequence model to realize the strong dual inside the prescribed ambient dual. -/
private theorem strongCoprimalityPrimaryQuotient_strongDual_character {F : Type*} [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (p : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) :
    let ω := χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ :
      (ideleClassNorm F).ker →ₜ* IdeleClassGroup (𝓞 F) F)
    let T := (finite_nuclearityPlacesAbove (F := F) p).toFinset
    let E := StrongDual ℂ (Fin T.card → RapidDecaySequence 1)
    ∃ (W : Submodule ℂ E) (D : Submodule ℂ W),
      IsClosed (W : Set E) ∧ IsClosed (D : Set W) ∧
        Nonempty (StrongDual ℂ (StrongCoprimalityQuotient ω T) ≃L[ℂ] (W ⧸ D)) := by
  classical
  let ω := χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ :
      (ideleClassNorm F).ker →ₜ* IdeleClassGroup (𝓞 F) F)
  let S := (finite_nuclearityPlacesAbove (F := F) p).toFinset
  have h (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) := (Valued.v : Valuation (v.adicCompletion F)
    (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
  let π : (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ :=
    fun v ↦ Units.mk0 (h v).choose (h v).choose_spec.ne_zero
  have hπ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : Valuation.IsUniformizer
      (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))) (π v).val :=
    (h v).choose_spec
  let T := S.filter (fun v ↦ (ideleClassNormTwist χ 0).IsUnramifiedAt v)
  have hT (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (hv : v ∈ T) : v.under (𝓞 ℚ) = p :=
    (finite_nuclearityPlacesAbove (F := F) p).mem_toFinset.mp (Finset.mem_filter.mp hv).1
  let model := strongCoprimalityPrimaryQuotient_sequence_decay ω p T hT π (fun v _ ↦ hπ v)
  let equiv := (strongCoprimality χ S π (fun v _ ↦ hπ v)).choose
  let C := equiv.symm.toContinuousLinearMap.comp model.choose
  have hC : Bijective C := equiv.symm.bijective.comp model.choose_spec
  have hNF : IsFrechetTVS (StrongCoprimalityQuotient ω S) ∧
      IsNuclearTVS.{0} (StrongCoprimalityQuotient ω S) :=
    strongCoprimalityPrimaryQuotient_nuclearFrechet ω p
  let e := (strongCoprimalityPrimaryQuotient_strongDual_sequenceEquiv hNF.1 C hC).some
  exact strongCoprimalityPrimaryQuotient_strongDual_model e (Finset.card_filter_le S (fun v ↦ (ideleClassNormTwist χ 0).IsUnramifiedAt v))

/-- Paper: Remark 7.5.0.2, p. 379.
The strong dual of the primary quotient is a Hausdorff quotient of a closed subspace
of the strong dual of the finite product of rapidly decreasing sequence spaces.
Deviation: The ambient sequence spaces on the dual side are strong duals. -/
theorem strongCoprimalityPrimaryQuotient_strongDual_subquotient (ω : PontryaginDual C₁) (p : Vℚ) :
    let T := (finite_nuclearityPlacesAbove (F := F) p).toFinset
    let E := StrongDual ℂ (Fin T.card → RapidDecaySequence 1)
    ∃ (W : Submodule ℂ E) (D : Submodule ℂ W),
      IsClosed (W : Set E) ∧ IsClosed (D : Set W) ∧
        Nonempty (StrongDual ℂ (StrongCoprimalityQuotient ω T) ≃L[ℂ] (W ⧸ D)) := by
  let lift := strongCoprimalityPrimaryQuotient_sequence_lift ω
  let χ := lift.choose
  have hχ := lift.choose_spec
  rw [← hχ]
  exact strongCoprimalityPrimaryQuotient_strongDual_character χ p

-- TODO(later): needs §8.1 for the orbital-support and support-constrained basis claims
-- announced on p. 374 and at the start of Chapter 8 on p. 381.

open MeasureTheory in
/-- Translation of an isotypic function on a norm section multiplies its Mellin integral
by the value of the Mellin character at the translating element. -/
private theorem strongCoprimality_bezout_translate {G : Type*} [CommGroup G]
    (m : G →* ℝ≥0ˣ) (σ : ℝ≥0ˣ →* G) (hσ : RightInverse σ m)
    (c : G →* ℂ) (u : G → ℂ)
    (hu : ∀ (k : m.ker) x, u (k.val⁻¹ * x) = c k.val * u x) (g : G) :
    (∫ t, u (g⁻¹ * σ t) * c (σ t) ∂positiveRealHaar) =
      c g * ∫ t, u (σ t) * c (σ t) ∂positiveRealHaar := by
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  let : positiveRealHaar.IsHaarMeasure := RiemannMasullo.positiveRealHaar_isHaarMeasure
  let k : m.ker := ⟨g / σ (m g), by rw [MonoidHom.mem_ker, map_div, hσ, div_self']⟩
  rw [← integral_mul_left_eq_self (μ := positiveRealHaar)
    (fun t ↦ u (g⁻¹ * σ t) * c (σ t)) (m g), ← integral_const_mul]
  apply integral_congr_ae (.of_forall fun t ↦ ?_)
  have he : g⁻¹ * σ (m g * t) = k.val⁻¹ * σ t := by
    simp [k, map_mul, div_eq_mul_inv, mul_comm, mul_left_comm]
  rw [he, hu, map_mul, map_mul, show c k.val = c (g / σ (m g)) from rfl, map_div]
  have hn : c (σ (m g)) ≠ 0 := ((Group.isUnit _).map c).ne_zero
  field_simp

/-- The Mellin character of a uniformizer gives the single-place Euler polynomial. -/
private theorem strongCoprimality_bezout_factor (χ : U) (v : V) (u : (v.adicCompletion F)ˣ)
    (hu : Valued.v.IsUniformizer (u : v.adicCompletion F))
    (hv : (ideleClassNormTwist χ 0).IsUnramifiedAt v) (s : ℂ) :
    1 - ideleClassNormTwist χ s (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u) =
      (finiteHeckeEulerFactor χ v s)⁻¹ := by
  rw [finiteHeckeEulerFactor, ite_eq_left hv, inv_inv, hv.localValue_eq u hu,
    HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
  let g := IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u
  change 1 - (χ g : ℂ) * ((((ideleClassNorm F g).val : ℝ) : ℂ) ^ s) =
    1 - ((χ g : ℂ) * ((((ideleClassNorm F g).val : ℝ) : ℂ) ^ (0 : ℂ))) *
      (v.asIdeal.absNorm : ℂ) ^ (-s)
  have hn : (((ideleClassNorm F g).val : ℝ)) = (v.asIdeal.absNorm : ℝ)⁻¹ :=
    (congrArg (fun t : ℝ≥0ˣ ↦ (t.val : ℝ)) (ideleClassNorm_ofAdicCompletion F v u)).trans
      (norm_uniformizer_adicCompletion v _ hu)
  rw [hn, Complex.cpow_zero, mul_one, Complex.ofReal_inv,
    Complex.inv_cpow_ofReal_nonneg (Nat.cast_nonneg _), Complex.cpow_neg, Complex.ofReal_natCast]

open MeasureTheory in
/-- The section Mellin transform takes an unramified difference product to multiplication
by its reciprocal Euler polynomial. -/
private theorem strongCoprimality_bezout_difference (χ : U)
    (τ : ℝ≥0ˣ →ₜ* I𝔽) (hτ : RightInverse τ (ideleNorm F))
    (S : Finset V) (π : (v : V) → (v.adicCompletion F)ˣ)
    (hπ : ∀ v ∈ S, Valued.v.IsUniformizer (π v : v.adicCompletion F))
    (hS : ∀ v ∈ S, (ideleClassNormTwist χ 0).IsUnramifiedAt v)
    (M : StrongCoprimalityDecaySpace ω(χ) ≃L[ℂ] B)
    (hM : ∀ (f : StrongCoprimalityDecaySpace ω(χ)) s, (M f).val s =
      ∫ t : ℝ≥0ˣ, f.val.val (QuotientGroup.mk (τ t)) *
        ideleClassNormTwist χ s (QuotientGroup.mk (τ t)) ∂positiveRealHaar)
    (f g : StrongCoprimalityDecaySpace ω(χ))
    (hg : g.val.val = strongCoprimalityDifference S π f.val.val) (s : ℂ) :
    (M g).val s = reciprocalPartialHeckeEulerProduct χ S s * (M f).val s := by
  let σ : ℝ≥0ˣ →* C𝔽 := (QuotientGroup.mk' _).comp τ.toMonoidHom
  have hσ : RightInverse σ (ideleClassNorm F) := fun t ↦ hτ t
  let c := ideleClassNormTwist χ s
  let a (v : V) := IdeleClassGroup.ofAdicCompletion (𝓞 F) F v (π v)
  let hm := strongCoprimalityNorm_isModulation_surjective (F := F)
  let D (l : List V) := modulatedIsotypicDifferenceProduct m𝔽 hm.1 hm.2 ω(χ) univ
    ordConnected_univ (mem_univ (0 : ℝ)) (l.map fun v ↦ (a v)⁻¹)
  have hsub (v : V) (l : List V) (x : C𝔽) :
      ((D (v :: l)) f).val.val x = ((D l) f).val.val x - ((D l) f).val.val ((a v)⁻¹ * x) :=
    modulatedCyclicDifference_apply m𝔽 (a v)⁻¹ hm.1 hm.2 univ ordConnected_univ univ_nonempty
      ((D l) f).val x
  have htrans (v : V) (l : List V) : (M ((D (v :: l)) f)).val s =
      (1 - c (a v)) * (M ((D l) f)).val s := by
    let z := (D l) f
    let y := z - (D (v :: l)) f
    have hy (x : C𝔽) : y.val.val x = z.val.val ((a v)⁻¹ * x) := by
      change z.val.val x - ((D (v :: l)) f).val.val x = _
      rw [hsub]
      ring
    have hk (k : (ideleClassNorm F).ker) (x : C𝔽) :
        z.val.val (k.val⁻¹ * x) = c k.val * z.val.val x := by
      have hh := (mem_modulatedDecayIsotype_iff m𝔽 ω(χ) univ (mem_univ _) z.val).mp z.property k x
      have hck : c k.val = (χ k.val : ℂ) := by
        change (χ k.val : ℂ) * ((((ideleClassNorm F k.val).val : ℝ) : ℂ) ^ s) = _
        rw [k.property]
        simp
      rw [hck]
      exact hh
    have he : (M y).val s = c (a v) * (M z).val s := by
      rw [hM, hM]
      simp only [hy]
      exact strongCoprimality_bezout_translate (ideleClassNorm F) σ hσ c.toMonoidHom
        z.val.val hk (a v)
    rw [show (D (v :: l)) f = z - y from (sub_sub_cancel z ((D (v :: l)) f)).symm, map_sub]
    change (M z).val s - (M y).val s = _
    rw [he]
    ring
  have hprod (l : List V) (hl : ∀ v ∈ l, v ∈ S) : (M ((D l) f)).val s =
      ((l.map fun v ↦ (finiteHeckeEulerFactor χ v s)⁻¹).prod) * (M f).val s := by
    induction l with
    | nil => rw [List.map_nil, List.prod_nil, one_mul]; rfl
    | cons v l ih =>
      have hv := hl v (List.mem_cons_self ..)
      rw [htrans, strongCoprimality_bezout_factor χ v (π v) (hπ v hv) (hS v hv),
        ih (fun w hw ↦ hl w (List.mem_cons_of_mem _ hw))]
      simp [mul_assoc]
  have hfold (l : List V) (x : C𝔽) : ((D l) f).val.val x =
      l.foldr (fun v (w : C𝔽 → ℂ) y ↦ w y - w ((a v)⁻¹ * y)) f.val.val x := by
    induction l generalizing x with
    | nil => rfl
    | cons v l ih => exact (hsub v l x).trans (congrArg₂ (· - ·) (ih x) (ih ((a v)⁻¹ * x)))
  have he : g = (D S.toList) f :=
    Subtype.ext (Subtype.ext (funext fun x ↦ (congrFun hg x).trans (hfold S.toList x).symm))
  rw [he, hprod S.toList (fun v hv ↦ Finset.mem_toList.mp hv)]
  simp [reciprocalPartialHeckeEulerProduct]

/-- Surjectivity of the induced quotient map decomposes each target vector as an image
vector plus an element of the target denominator. -/
private theorem strongCoprimality_bezout_decompose {X Y : Type*} [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] (A : Submodule ℂ X) (D : Submodule ℂ Y)
    (j : X →ₗ[ℂ] Y) (e : (X ⧸ A) ≃ₗ[ℂ] (Y ⧸ D)) (he : ∀ x, e (A.mkQ x) = D.mkQ (j x))
    (y : Y) : ∃ x : X, y - j x ∈ D := by
  obtain ⟨q, hq⟩ := e.surjective (D.mkQ y)
  obtain ⟨x, rfl⟩ := A.mkQ_surjective q
  exact ⟨x, (Submodule.Quotient.eq D).mp (hq.symm.trans (he x))⟩

open Classical in
/-- Paper: Corollary 7.5.0.3 and Equation (7.5.0.17), p. 379.
Every entire Schwartz–Bergman function is the sum of an entire multiple of the
regularized completed Hecke function and an Euler polynomial times another
Schwartz–Bergman function. The first summand is itself Schwartz–Bergman.
The sign converts the pole polynomial of §7.1.4 to the convention in (7.5.0.17). -/
theorem strongCoprimality_bezout (S : Finset V)
    (_hS : ∀ v ∈ S, (ideleClassNormTwist χ 0).IsUnramifiedAt v) (φ : B) :
    let L := regularizedCompletedHeckeL χ τ hτ (continuedCompletedHeckeL χ)
      (continuedCompletedHeckeL_spec χ).1 (continuedCompletedHeckeL_spec χ).2
    let δ : ℕ := if χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1 then 1 else 0
    ∃ (u : entireContinuousMapSubalgebra) (v w : B),
      (∀ s : ℂ, w.val s = (-1 : ℂ) ^ δ * L.val s * u.val s) ∧
      ∀ s : ℂ, w.val s + reciprocalPartialHeckeEulerProduct χ S s * v.val s = φ.val s := by
  intro L δ
  let val (v : V) := (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)))
  let raw (v : V) := (val v).exists_isUniformizer_of_isCyclic_of_nontrivial
  let π (v : V) := Units.mk0 ((raw v).choose : v.adicCompletion F) (raw v).choose_spec.ne_zero
  have hπ (v : V) : (val v).IsUniformizer (π v).val := (raw v).choose_spec
  let j := (exists_strongCoprimalityThetaEmbedding ω(χ)).choose
  have heq := strongCoprimality χ S π (fun v _ ↦ hπ v)
  dsimp only at heq
  rw [Finset.filter_true_of_mem _hS] at heq
  obtain ⟨e, he⟩ := heq
  obtain ⟨M, hM, hθ⟩ := spectralNuclearityDenominator_isotypeModel χ τ hτ 0
  let y := M.symm φ
  have ⟨x, hx⟩ := strongCoprimality_bezout_decompose (strongCoprimalityDenominator ω(χ) S)
    (strongCoprimalityDifferenceRange ω(χ) S π) j.toLinearMap e.toLinearEquiv he y
  obtain ⟨z, hz⟩ := (mem_strongCoprimalityDifferenceRange ω(χ) S π (y - j x)).mp hx
  have hdiff := strongCoprimality_bezout_difference χ τ hτ S π (fun v _ ↦ hπ v) _hS M hM
    z (y - j x) hz
  let w := M (j x)
  have hw : w ∈ spectralNuclearityDenominator χ τ hτ 0 := by
    apply (hθ (j x)).mpr
    obtain ⟨f, rfl⟩ := (K(ω(χ))).mkQ_surjective x
    refine ⟨f, fun g ↦ ?_⟩
    simp only [Real.rpow_zero, Complex.ofReal_one, one_mul]
    rw [← homogeneousAdelicThetaLinearMap_apply (F := F) ω(χ) f.val]
    exact (exists_strongCoprimalityThetaEmbedding ω(χ)).choose_spec.2 f g
  rw [spectralNuclearityDenominator, schwartzBergmanDivisible, Submodule.mem_comap,
    Submodule.restrictScalars_mem, Ideal.mem_span_singleton'] at hw
  obtain ⟨a, ha⟩ := hw
  let u : entireContinuousMapSubalgebra := (-1 : entireContinuousMapSubalgebra) ^ δ * a
  refine ⟨u, M z, w, fun s ↦ ?_, fun s ↦ ?_⟩
  · have h := congrArg (fun b : entireContinuousMapSubalgebra ↦ b.val s) ha
    change a.val s * L.val (s + (0 : ℝ)) = (schwartzBergmanEntireInclusion w).val s at h
    rw [schwartzBergmanEntireInclusion_apply, Complex.ofReal_zero, add_zero] at h
    change w.val s = (-1 : ℂ) ^ δ * L.val s * ((-1 : ℂ) ^ δ * a.val s)
    simp only [← h]
    calc
      _ = ((-1 : ℂ) * -1) ^ δ * (a.val s * L.val s) := by simp
      _ = _ := by rw [mul_pow]; ring
  · have h := hdiff s
    rw [map_sub, show M y = φ from M.apply_symm_apply φ] at h
    change φ.val s - w.val s = _ at h
    rw [← h]
    ring

end RiemannMasullo
