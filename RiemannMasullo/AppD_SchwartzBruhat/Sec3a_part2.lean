module

public import RiemannMasullo.AppD_SchwartzBruhat.Sec3a
public import RiemannMasullo.Ch03_IdelicZeta.Sec1
import all RiemannMasullo.AppD_SchwartzBruhat.Sec3a
import all RiemannMasullo.AppC_LCTVS.Sec1
import all RiemannMasullo.AppC_LCTVS.Sec2a_part2
import all RiemannMasullo.AppD_SchwartzBruhat.Sec1a
import all RiemannMasullo.AppD_SchwartzBruhat.Sec1b
import all RiemannMasullo.AppD_SchwartzBruhat.Sec2a
import all RiemannMasullo.AppD_SchwartzBruhat.Sec2b
import RiemannMasullo.ForMathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Pow.Complex
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.Completion
import Mathlib.Analysis.Distribution.SchwartzSpace.CompactSupport
import Mathlib.Analysis.LocallyConvex.ContinuousOfBounded
import RiemannMasullo.ForMathlib.Topology.ContinuousMap.LocallyConvex
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# Structure and Fourier–Mellin transform of Schwartz–Bruhat decay spaces

Masullo, Appendix D, §D.3.3, from the end of Example D.3.3.5.
-/

@[expose] public noncomputable section

namespace RiemannMasullo

open Bornology Function MeasureTheory Set Topology TopologicalSpace UniformSpace
open scoped Manifold NNReal TensorProduct

-- TODO(later): needs §B.2
-- Lemma D.3.2.3(4)–(6) uses the three decay spaces in Definition B.2.1.1, p. 593.

attribute [local instance] uniformContinuousConstSMul_of_continuousConstSMul

local instance {X : Type*} [AddCommGroup X] [Module ℂ X] {ι : Type*}
    (p : SeminormFamily ℂ X ι) : ContinuousSMul ℂ (WithGeneratingSeminorms X p) :=
  (withGeneratingSeminorms_spec X p).continuousSMul

variable {G : Type*} [CommGroup G] [TopologicalSpace G]
local notation "GoodCompact" => {k : Subgroup G // IsCompact (k : Set G) ∧
  IsCompactlyGeneratedGroup (lcaAnnihilator k)}

/-- Normalized averaging over a compact subgroup descends every invariant function. -/
private theorem schwartzBruhat_compactQuotient_average [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] (k : Subgroup G) (hk : IsCompact (k : Set G)) :
    ∃ A : SchwartzBruhat G →L[ℂ] SchwartzBruhat (G ⧸ k), ∀ f : SchwartzBruhat G,
      (∀ g (u : k), f (g * u.val) = f g) → ∀ g : G, A f (g : G ⧸ k) = f g := by
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let : CompactSpace k := isCompact_iff_compactSpace.mp hk
  let μ : Measure k := Measure.haarMeasure ⊤
  let : IsProbabilityMeasure μ := ⟨Measure.haarMeasure_self⟩
  have havg := schwartzBruhatCosetIntegral_continuousLinear k μ hk.isClosed
  let A : SchwartzBruhat G →L[ℂ] SchwartzBruhat (G ⧸ k) := havg.choose
  have hA := havg.choose_spec
  refine ⟨A, fun f hf g ↦ ?_⟩
  calc
    _ = schwartzBruhatCosetIntegral k μ hk.isClosed f (g : G ⧸ k) :=
      congrArg (fun F : SchwartzBruhat (G ⧸ k) ↦ F (g : G ⧸ k)) (hA f)
    _ = ∫ u : k, f (g * u.val) ∂μ := schwartzBruhatCosetIntegral_mk k μ hk.isClosed f g
    _ = ∫ _ : k, f g ∂μ := congrArg (fun F : k → ℂ ↦ ∫ u, F u ∂μ) (funext (hf g))
    _ = f g := (integral_const _).trans <|
      (congrArg (fun r : ℝ ↦ r • f g) (probReal_univ (μ := μ))).trans (one_smul ℝ _)

/-- Paper: Example D.3.3.5, p. 805. Pullback along the quotient map for nested
compact subgroups with compactly generated annihilators is a topological embedding
on the ordinary Schwartz–Bruhat spaces. -/
theorem schwartzBruhat_compactQuotient_pullback [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] (k k' : GoodCompact) (h : k'.val ≤ k.val) :
    ∃ j : SchwartzBruhat (G ⧸ k.val) →L[ℂ] SchwartzBruhat (G ⧸ k'.val),
      IsEmbedding j ∧ ∀ f (g : G), j f (g : G ⧸ k'.val) = f (g : G ⧸ k.val) := by
  have hp := continuous_schwartzBruhat_compactQuotient_pullback k.val k.property.1
  let P := hp.choose
  have hP := hp.choose_spec
  have hp' := continuous_schwartzBruhat_compactQuotient_pullback k'.val k'.property.1
  let P' := hp'.choose
  have hP' := hp'.choose_spec
  have ha := schwartzBruhat_compactQuotient_average k.val k.property.1
  let A := ha.choose
  have hA := ha.choose_spec
  have ha' := schwartzBruhat_compactQuotient_average k'.val k'.property.1
  let A' := ha'.choose
  have hA' := ha'.choose_spec
  let j := A'.comp P
  have hinv (f : SchwartzBruhat (G ⧸ k.val)) (g : G) (u : k.val) :
      P f (g * u.val) = P f g := by
    exact (hP f _).trans ((congrArg f.val (QuotientGroup.mk_mul_of_mem g u.property)).trans
      (hP f g).symm)
  have hj (f : SchwartzBruhat (G ⧸ k.val)) (g : G) : j f (g : G ⧸ k'.val) = f (g : G ⧸ k.val) :=
    (hA' (P f) (fun x u ↦ hinv f x ⟨u.val, h u.property⟩) g).trans (hP f g)
  refine ⟨j, Function.LeftInverse.isEmbedding (f := A.comp P') ?_ (A.comp P').continuous
    j.continuous, hj⟩
  intro f
  have he : P' (j f) = P f :=
    Subtype.ext (funext fun x ↦ (hP' (j f) x).trans ((hj f x).trans (hP f x).symm))
  change A (P' (j f)) = f
  refine (congrArg A he).trans ?_
  apply Subtype.ext
  funext x
  exact QuotientGroup.induction_on x fun g ↦ (hA (P f) (hinv f) g).trans (hP f g)

variable [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
variable (m : G →ₜ* ℝ≥0ˣ) (I : Set ℝ)

local notation "K" => m.toMonoidHom.ker
local notation "E" => ModulatedExponentialDecay m I
local notation "P" => PositiveRealExponentialDecay I

section Stages

/-- Paper: (D.3.3.2), p. 805. The topology of a decay stage is induced by the
joint map to the product of its Schwartz–Bruhat twists. -/
private theorem modulatedExponentialDecayStage_twists_isInducing (k : GoodCompact) :
    IsInducing (fun (f : ModulatedExponentialDecayStage m I k) (a : I) ↦
      modulatedExponentialDecayTwist (quotientModulation m k.val k.property.1) I a f) := by
  let T : ModulatedExponentialDecayStage m I k →ₗ[ℂ] (I → SchwartzBruhat (G ⧸ k.val)) :=
    LinearMap.pi (modulatedExponentialDecayTwist (quotientModulation m k.val k.property.1) I)
  change IsInducing T
  have hPi := withSeminorms_pi
    (fun _ : I ↦ PolynormableSpace.withSeminorms ℂ (SchwartzBruhat (G ⧸ k.val)))
  have hInduced := WithSeminorms.topologicalSpace_eq_iInf (t := induced T inferInstance)
    (T.withSeminorms_induced hPi)
  refine ⟨(ModulatedExponentialDecayStage.withSeminorms m I k).topologicalSpace_eq_iInf.trans
    (Eq.trans ?_ hInduced.symm)⟩
  exact (Equiv.sigmaEquivProd I _).symm.iInf_congr (fun _ ↦ rfl)

variable (hm : IsModulation m) (hms : Surjective m) (hInt : OrdConnected I) (hne : I.Nonempty)

set_option linter.unusedSectionVars false in
include hm hms hInt hne in
/-- Paper: Example D.3.3.5, p. 805. When k' is contained in k, pullback
from G/k to G/k' embeds the decay stage topologically in the larger stage. -/
theorem modulatedExponentialDecayStage_transition (k k' : GoodCompact) (h : k'.val ≤ k.val) :
    ∃ j : ModulatedExponentialDecayStage m I k →L[ℂ] ModulatedExponentialDecayStage m I k',
      IsEmbedding j ∧ ∀ f (g : G), (j f).val (g : G ⧸ k'.val) = f.val (g : G ⧸ k.val) := by
  have hSchwartz := schwartzBruhat_compactQuotient_pullback (G := G) k k' h
  let L := hSchwartz.choose
  have hL : IsEmbedding L := hSchwartz.choose_spec.1
  have hL_apply := hSchwartz.choose_spec.2
  let n := quotientModulation m k.val k.property.1
  let n' := quotientModulation m k'.val k'.property.1
  let q : (G ⧸ k'.val) →* (G ⧸ k.val) :=
    QuotientGroup.map k'.val k.val (MonoidHom.id G) (by simpa only [Subgroup.comap_id] using h)
  let pullback : ModulatedExponentialDecayStage m I k →ₗ[ℂ] ((G ⧸ k'.val) → ℂ) :=
    (LinearMap.pi fun x ↦ LinearMap.proj (q x)).comp
      (modulatedExponentialDecaySubmodule n I).subtype
  have hweight (f : ModulatedExponentialDecayStage m I k) (a : I) :
      modulationWeight n' a (pullback f) =
        (L (modulatedExponentialDecayTwist n I a f) : (G ⧸ k'.val) → ℂ) := by
    funext x
    exact QuotientGroup.induction_on x fun g ↦
      (hL_apply (modulatedExponentialDecayTwist n I a f) g).symm
  let j : ModulatedExponentialDecayStage m I k →ₗ[ℂ] ModulatedExponentialDecayStage m I k' :=
    pullback.codRestrict (modulatedExponentialDecaySubmodule n' I) (by
      intro f
      refine (Submodule.mem_iInf _).mpr fun a ↦ Submodule.mem_comap.mpr ?_
      rw [hweight]
      exact (L (modulatedExponentialDecayTwist n I a f)).property)
  let twists (f : ModulatedExponentialDecayStage m I k) (a : I) :=
    modulatedExponentialDecayTwist n I a f
  let twists' (f : ModulatedExponentialDecayStage m I k') (a : I) :=
    modulatedExponentialDecayTwist n' I a f
  let mapTwists := Pi.map fun _ : I ↦
    (L : SchwartzBruhat (G ⧸ k.val) → SchwartzBruhat (G ⧸ k'.val))
  have hcomm : twists' ∘ j = mapTwists ∘ twists :=
    funext fun f ↦ funext fun a ↦ Subtype.ext (hweight f a)
  have hmapTwists : IsInducing mapTwists := IsInducing.piMap fun _ ↦ hL.isInducing
  have hcomposite : IsInducing (twists' ∘ j) :=
    Eq.mpr (congrArg (fun φ : ModulatedExponentialDecayStage m I k →
      I → SchwartzBruhat (G ⧸ k'.val) ↦ IsInducing φ) hcomm)
      (hmapTwists.comp (modulatedExponentialDecayStage_twists_isInducing m I k))
  have htwists' : IsInducing twists' := modulatedExponentialDecayStage_twists_isInducing m I k'
  have hj : IsInducing j := htwists'.of_comp_iff.mp hcomposite
  refine ⟨⟨j, hj.continuous⟩, ⟨hj, ?_⟩, fun _ _ ↦ rfl⟩
  intro f g hfg
  apply Subtype.ext
  funext x
  exact QuotientGroup.induction_on x fun y ↦
    congrArg (fun z : ModulatedExponentialDecayStage m I k' ↦ z.val (y : G ⧸ k'.val)) hfg

variable [hSC : SecondCountableTopology G]

/-- Paper: Example D.3.3.5, p. 805. The compact components of a cofinal sequence of
Bruhat structural pairs are cofinal among compact subgroups with compactly generated annihilator. -/
private theorem exists_antitone_goodCompact :
    ∃ k : ℕ → GoodCompact, Antitone (fun n ↦ (k n).val) ∧
      ∀ k' : GoodCompact, ∃ n, (k n).val ≤ k'.val := by
  obtain ⟨a, _, _, ha, hcof, _⟩ := schwartzBruhat_exists_topologicallyExact (G := G)
  let subgroup (n : ℕ) := OrderDual.ofDual (a n).val.2
  have hgood (n : ℕ) : IsBruhatGoodSubgroup (subgroup n) := (a n).property.2.2.1
  have hcomp (n : ℕ) : IsCompact (subgroup n : Set G) := by
    obtain ⟨_, _, _, hker, hc⟩ := lca_dualSubgroup_quotient
      (⟨lcaAnnihilator (subgroup n), (hgood n).2⟩ : OpenCompactlyGeneratedSubgroups (PontryaginDual G))
    rwa [hker, lcaDualAnnihilator_annihilator (subgroup n) (hgood n).1] at hc
  refine ⟨fun n ↦ ⟨subgroup n, hcomp n, (hgood n).2.2⟩, fun _ _ h ↦ (ha h).2, ?_⟩
  intro k'
  obtain ⟨H, hH⟩ := exists_openCompactlyGeneratedSubgroup_contains k'.property.1
  let b : BruhatStructuralPair G := ⟨(H.val, OrderDual.toDual k'.val), H.property.1,
    H.property.2, ⟨k'.property.1.isClosed, isOpen_lcaAnnihilator _ k'.property.1,
      k'.property.2⟩, hH⟩
  obtain ⟨n, hn⟩ := hcof b
  exact ⟨n, hn.2⟩

/-- A decreasing cofinal sequence of indices for a family of embedded stages has the
same union and final locally convex topology, and its maps into the union are embeddings. -/
private theorem stageLimit_of_cofinal {ι : Type*} [Preorder ι]
    {F : Type*} [AddCommGroup F] [Module ℂ F] [t : TopologicalSpace F] [IsTopologicalAddGroup F]
    {X : ι → Type*} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    [∀ a, TopologicalSpace (X a)] [∀ a, IsTopologicalAddGroup (X a)]
    [∀ a, PolynormableSpace ℂ (X a)]
    (i : ∀ a, X a →ₗ[ℂ] F) (hinj : ∀ a, Injective (i a))
    (hex : ∀ x : F, ∃ a, x ∈ (i a).range) (ht : t = locallyConvexFinalTopology i)
    (htrans : ∀ a b, b ≤ a → ∃ j : X a →L[ℂ] X b,
      IsEmbedding j ∧ ∀ x, i b (j x) = i a x)
    (k : ℕ → ι) (hk : Antitone k) (hcof : ∀ a, ∃ n, k n ≤ a) :
    (∀ n, IsEmbedding (i (k n))) ∧ (∀ x : F, ∃ n, x ∈ (i (k n)).range) ∧
      t = locallyConvexFinalTopology (fun n ↦ i (k n)) := by
  have hfactor (a : ι) : ∃ n, ∃ j : X a →L[ℂ] X (k n), ∀ x, i (k n) (j x) = i a x := by
    obtain ⟨n, hn⟩ := hcof a
    obtain ⟨j, _, hj⟩ := htrans a (k n) hn
    exact ⟨n, j, hj⟩
  have hcover (x : F) : ∃ n, x ∈ (i (k n)).range := by
    obtain ⟨a, y, rfl⟩ := hex x
    obtain ⟨n, j, hj⟩ := hfactor a
    exact ⟨n, j y, hj y⟩
  have htests : (fun p : Seminorm ℂ F ↦ ∀ a, Continuous (p ∘ i a)) =
      (fun p : Seminorm ℂ F ↦ ∀ n, Continuous (p ∘ i (k n))) := by
    funext p
    apply propext
    refine ⟨fun h n ↦ h (k n), fun h a ↦ ?_⟩
    obtain ⟨n, j, hj⟩ := hfactor a
    exact ((h n).comp j.continuous).congr fun x ↦ congrArg p (hj x)
  have ht' : t = locallyConvexFinalTopology (fun n ↦ i (k n)) :=
    ht.trans (congrArg (fun pred : Seminorm ℂ F → Prop ↦
      (SeminormFamily.moduleFilterBasis (Subtype.val : Subtype pred → Seminorm ℂ F)).topology) htests)
  have hseminorms : WithSeminorms
      (Subtype.val : {p : Seminorm ℂ F // ∀ a, Continuous (p ∘ i a)} → Seminorm ℂ F) := ⟨ht⟩
  let incl (n : ℕ) : X (k n) →L[ℂ] F :=
    ⟨i (k n), hseminorms.continuous_of_continuous_comp _ fun p ↦ p.property (k n)⟩
  choose j hj hcomm using fun n ↦ htrans (k n) (k (n + 1)) (hk (Nat.le_succ n))
  have hlim : IsInjectiveLCLimit (X := fun n ↦ X (k n)) j incl :=
    ⟨fun n ↦ hinj (k n), fun n ↦ ContinuousLinearMap.ext (hcomm n), hcover, ht'⟩
  exact ⟨hlim.isEmbedding_stage hj, hcover, ht'⟩

-- Checking unused section variables traverses the expanded seminorm families.
set_option linter.unusedSectionVars false in
include hSC hm hms hInt hne in
/-- Paper: Example D.3.3.5, p. 805. A decreasing cofinal sequence of stages
presents the decay space as a strict locally convex inductive limit. -/
theorem modulatedExponentialDecay_stageLimit :
    ∃ k : ℕ → GoodCompact,
      let i (n : ℕ) : ModulatedExponentialDecayStage m I (k n) →ₗ[ℂ] E :=
        modulatedExponentialDecayStageInclusion m I (k n)
      Antitone (fun n ↦ (k n).val) ∧ (∀ k' : GoodCompact, ∃ n, (k n).val ≤ k'.val) ∧
      (∀ n, IsEmbedding (i n)) ∧ (∀ f : E, ∃ n, f ∈ (i n).range) ∧
      (inferInstance : TopologicalSpace E) = locallyConvexFinalTopology i := by
  have hc := exists_antitone_goodCompact (G := G)
  let k := hc.choose
  exact ⟨k, hc.choose_spec.1, hc.choose_spec.2,
    stageLimit_of_cofinal (F := E) (X := ModulatedExponentialDecayStage m I)
      (fun a ↦ modulatedExponentialDecayStageInclusion m I a)
      (fun a ↦ (modulatedExponentialDecayStageInclusion_range m I a).1)
      (modulatedExponentialDecay_exists_stage m I hm hms hInt hne) rfl
      (fun a b h ↦ (modulatedExponentialDecayStage_transition m I hm hms hInt hne a b h).imp
        fun _ hj ↦ ⟨hj.1, fun f ↦ Subtype.ext (funext (hj.2 f))⟩)
      k hc.choose_spec.1 hc.choose_spec.2⟩

/-- Point evaluation on the Schwartz–Bruhat space is continuous since on each
structural stage it is bounded by the zeroth Schwartz seminorm. -/
private theorem continuous_schwartzBruhat_eval {A : Type*} [CommGroup A] [TopologicalSpace A]
    (x : A) : Continuous (fun f : SchwartzBruhat A ↦ f x) := by
  let ev : SchwartzBruhat A →ₗ[ℂ] ℂ :=
    (LinearMap.proj x).comp (schwartzBruhatSubmodule A).subtype
  let p : Seminorm ℂ (SchwartzBruhat A) := (normSeminorm ℂ ℂ).comp ev
  have hp : Continuous p := by
    apply (withGeneratingSeminorms_spec _ _).continuous_seminorm
      (⟨p, ?_⟩ : {p : Seminorm ℂ (schwartzBruhatSubmodule A) //
        ∀ (a : BruhatStructuralPair A) (e : ElementaryLCAPresentation a.quotient),
          Continuous (p ∘ schwartzBruhatStageInclusion a e)})
    intro a e
    let _ := e.finiteGroup
    let i : ElementarySchwartzIndex e.realDim e.torusDim e.latticeRank := (0, 0, 0, 0)
    change Continuous (p.comp (schwartzBruhatStageInclusion a e) :
      Seminorm ℂ (SchwartzBruhatStage e))
    refine Seminorm.continuous_of_le («E» := SchwartzBruhatStage e)
      (q := elementarySchwartzSeminorm i) (elementarySchwartz_withSeminorms.continuous_seminorm i) ?_
    intro f
    change ‖schwartzBruhatStageRealization a e f x‖ ≤ elementarySchwartzSeminorm i f
    classical
    erw [schwartzBruhatStageRealization_apply]
    split_ifs with hx
    · let y := Multiplicative.toAdd (e.equiv (QuotientGroup.mk ⟨x, hx⟩))
      change (‖f.val y‖₊ : ENNReal).toReal ≤ (elementarySchwartzBound f.val i).toReal
      apply ENNReal.toReal_mono (f.property.2 i).ne
      rw [show i = (0, 0, 0, 0) from rfl, elementarySchwartzBound_zero]
      exact le_iSup (fun z ↦ (‖f.val z‖₊ : ENNReal)) y
    · exact (norm_zero («E» := ℂ)).le.trans (apply_nonneg (elementarySchwartzSeminorm i) f)
  exact (norm_withSeminorms ℂ ℂ).continuous_of_continuous_comp («E» := SchwartzBruhat A) ev
    (fun _ ↦ hp)

/-- The joint twist map has closed range because its coordinates obey pointwise
compatibility equations with any one fixed twist. -/
private theorem modulatedExponentialDecayTwists_closedRange {A : Type*} [CommGroup A]
    [TopologicalSpace A] (n : A →ₜ* ℝ≥0ˣ) (J : Set ℝ) (hJ : J.Nonempty) :
    IsClosed (range (fun (f : modulatedExponentialDecaySubmodule n J) (b : J) ↦
      modulatedExponentialDecayTwist n J b f)) := by
  let twists (f : modulatedExponentialDecaySubmodule n J) (b : J) :=
    modulatedExponentialDecayTwist n J b f
  change IsClosed (range twists)
  obtain ⟨a, ha⟩ := hJ
  let a₀ : J := ⟨a, ha⟩
  let w (b : J) (x : A) : ℂ := ((((n x).val : ℝ) ^ (b : ℝ) : ℝ) : ℂ)
  have hw (b : J) (x : A) : w b x ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (NNReal.coe_pos.mpr (Units.zero_lt (n x))) _).ne'
  have heval (b : J) (x : A) :
      Continuous (fun g : J → SchwartzBruhat A ↦ g b x) := by
    have hb : Continuous (fun g : J → SchwartzBruhat A ↦ g b) := continuous_apply b
    exact (continuous_schwartzBruhat_eval (A := A) x).comp hb
  let compatible (b : J) (x : A) : Set (J → SchwartzBruhat A) :=
    {g | w a₀ x * g b x = w b x * g a₀ x}
  have hrange : range twists = ⋂ (b : J) (x : A), compatible b x := by
    refine Set.ext fun g ↦ ?_
    simp only [mem_range, mem_iInter, compatible, mem_ofPred_eq]
    constructor
    · rintro ⟨f, rfl⟩ b x
      change w a₀ x * (w b x * f.val x) = w b x * (w a₀ x * f.val x)
      exact mul_left_comm _ _ _
    · intro hg
      let f (x : A) := g a₀ x / w a₀ x
      have hmatch (b : J) (x : A) : w b x * f x = g b x := by
        change w b x * (g a₀ x / w a₀ x) = g b x
        rw [← mul_div_assoc]
        exact (div_eq_iff (hw a₀ x)).mpr ((hg b x).symm.trans (mul_comm _ _))
      have hf : f ∈ modulatedExponentialDecaySubmodule n J := by
        refine (Submodule.mem_iInf _).mpr fun b ↦ Submodule.mem_comap.mpr ?_
        let gb : schwartzBruhatSubmodule A := g b
        have hb : modulationWeight n b f = gb.val := funext (hmatch b)
        exact hb ▸ gb.property
      refine ⟨⟨f, hf⟩, ?_⟩
      funext b
      exact Subtype.ext (funext (hmatch b))
  have hCompatible (b : J) (x : A) : IsClosed (compatible b x) :=
    isClosed_eq (continuous_const.mul (heval b x)) (continuous_const.mul (heval a₀ x))
  have hIntersection : IsClosed (⋂ (b : J) (x : A), compatible b x) :=
    isClosed_iInter fun b ↦ isClosed_iInter (hCompatible b)
  exact (congrArg (fun s : Set (J → SchwartzBruhat A) ↦ IsClosed s) hrange).mpr hIntersection

set_option linter.unusedSectionVars false in
include hSC hm hms hInt hne in
/-- Paper: Example D.3.3.5, p. 806. Each compact-subgroup decay stage is complete. -/
theorem modulatedExponentialDecayStage_complete (k : GoodCompact) :
    CompleteSpace (ModulatedExponentialDecayStage m I k) := by
  let n := quotientModulation m k.val k.property.1
  let T : ModulatedExponentialDecayStage m I k →ₗ[ℂ] (I → SchwartzBruhat (G ⧸ k.val)) :=
    LinearMap.pi (modulatedExponentialDecayTwist n I)
  have hInd : IsInducing T := modulatedExponentialDecayStage_twists_isInducing m I k
  have hT : IsUniformInducing T := AddMonoidHom.isUniformInducing_of_isInducing
    (f := T) hInd
  have hClosed : IsClosed (range T) :=
    modulatedExponentialDecayTwists_closedRange n I hne
  let _ : IsClosed (k.val : Set G) := k.property.1.isClosed
  let _ := schwartzBruhat_complete (G := G ⧸ k.val)
  exact hT.completeSpace hClosed.isComplete

set_option linter.unusedSectionVars false in
include hm hms hInt hne in
/-- Paper: Remark D.3.3.6, p. 806. Multiplying by the module to the power a
moves the decay interval to its translate by -a and gives a topological isomorphism. -/
theorem modulatedExponentialDecay_shift_equiv (a : ℝ) :
    ∃ e : E ≃L[ℂ] ModulatedExponentialDecay m ((fun b : ℝ ↦ b - a) '' I),
      ∀ f, (e f).val = modulationWeight m a f.val := by
  have weight_add {A : Type _} [CommGroup A] [TopologicalSpace A]
      (n : A →ₜ* ℝ≥0ˣ) (b c : ℝ) (f : A → ℂ) :
      modulationWeight n b (modulationWeight n c f) = modulationWeight n (b + c) f := by
    funext x
    have hx : 0 < ((n x).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt (n x))
    simp only [modulationWeight, LinearMap.mulLeft_apply, Pi.mul_apply,
      Real.rpow_add hx, Complex.ofReal_mul, mul_assoc]
  let shift {A : Type _} [CommGroup A] [TopologicalSpace A]
      (n : A →ₜ* ℝ≥0ˣ) (S T : Set ℝ) (c : ℝ) (h : ∀ b ∈ T, b + c ∈ S) :
      modulatedExponentialDecaySubmodule n S →ₗ[ℂ] modulatedExponentialDecaySubmodule n T :=
    ((modulationWeight n c).comp (modulatedExponentialDecaySubmodule n S).subtype).codRestrict
      (modulatedExponentialDecaySubmodule n T) (by
        intro f
        refine (Submodule.mem_iInf _).mpr fun b ↦ Submodule.mem_comap.mpr ?_
        change modulationWeight n b (modulationWeight n c f.val) ∈ schwartzBruhatSubmodule A
        rw [weight_add]
        exact modulationWeight_mem_schwartzBruhat n S ⟨b + c, h b b.property⟩ f)
  let continuousShift (S T : Set ℝ) (c : ℝ) (h : ∀ b ∈ T, b + c ∈ S) :
      ModulatedExponentialDecay m S →L[ℂ] ModulatedExponentialDecay m T := by
    let F : ModulatedExponentialDecay m S →ₗ[ℂ] ModulatedExponentialDecay m T := shift m S T c h
    refine ⟨F, ?_⟩
    change Continuous F
    let FinalSeminorms (U : Set ℝ) := {q : Seminorm ℂ (modulatedExponentialDecaySubmodule m U) //
      ∀ k : GoodCompact, Continuous (q ∘ modulatedExponentialDecayStageInclusion m U k)}
    have generating (U : Set ℝ) :=
      withGeneratingSeminorms_spec _ (Subtype.val : FinalSeminorms U → _)
    refine (generating T).continuous_of_continuous_comp F fun p ↦ ?_
    let q : Seminorm ℂ (ModulatedExponentialDecay m S) := p.val.comp F
    change Continuous q
    have hq (k : GoodCompact) : Continuous (q ∘ modulatedExponentialDecayStageInclusion m S k) := by
      let n := quotientModulation m k.val k.property.1
      let stageShift : ModulatedExponentialDecayStage m S k →ₗ[ℂ]
          ModulatedExponentialDecayStage m T k := shift n S T c h
      have hstage : Continuous stageShift := by
        apply (modulatedExponentialDecayStage_twists_isInducing m T k).continuous_iff.mpr
        apply continuous_pi
        intro b
        let d : S := ⟨b + c, h b b.property⟩
        have htwist : Continuous (fun f : ModulatedExponentialDecayStage m S k ↦
            modulatedExponentialDecayTwist n S d f) :=
          (continuous_apply d).comp (modulatedExponentialDecayStage_twists_isInducing m S k).continuous
        exact htwist.congr fun f ↦ Subtype.ext (weight_add n b c f.val).symm
      exact ((p.property k).comp hstage).congr fun f ↦ congrArg p.val (Subtype.ext rfl)
    exact (generating S).continuous_seminorm (⟨q, hq⟩ : FinalSeminorms S)
  let J := (fun b : ℝ ↦ b - a) '' I
  have hforward : ∀ b ∈ J, b + a ∈ I := by
    rintro b ⟨d, hd, rfl⟩
    simpa only [sub_add_cancel] using hd
  have hbackward : ∀ b ∈ I, b + -a ∈ J := by
    intro b hb
    exact ⟨b, hb, sub_eq_add_neg b a⟩
  let forward : E →L[ℂ] ModulatedExponentialDecay m J := continuousShift I J a hforward
  let backward : ModulatedExponentialDecay m J →L[ℂ] E := continuousShift J I (-a) hbackward
  have hleft : LeftInverse backward forward := by
    intro f
    apply Subtype.ext
    change modulationWeight m (-a) (modulationWeight m a f.val) = f.val
    rw [weight_add, neg_add_cancel, modulationWeight_zero]
  have hright : RightInverse backward forward := by
    intro f
    apply Subtype.ext
    change modulationWeight m a (modulationWeight m (-a) f.val) = f.val
    rw [weight_add, add_neg_cancel, modulationWeight_zero]
  exact ⟨ContinuousLinearEquiv.equivOfInverse forward backward hleft hright, fun _ ↦ rfl⟩

/-- Multiplication by a unitary character is continuous on Schwartz–Bruhat functions,
since the Fourier transform turns it into translation on the dual group. -/
private theorem schwartzBruhat_mul_unitaryCharacter {A : Type*} [CommGroup A]
    [TopologicalSpace A] [IsTopologicalGroup A] [T2Space A] [LocallyCompactSpace A]
    [SecondCountableTopology A] (η : PontryaginDual A) :
    ∃ M : SchwartzBruhat A →L[ℂ] SchwartzBruhat A,
      ∀ f x, M f x = (η x : ℂ) * f x := by
  let : MeasurableSpace A := borel A
  let : BorelSpace A := ⟨rfl⟩
  let μ : Measure A := Measure.haar
  have : μ.IsHaarMeasure := inferInstanceAs ((Measure.haar (G := A)).IsHaarMeasure)
  have : μ.Regular := inferInstanceAs ((Measure.haar (G := A)).Regular)
  let : SecondCountableTopology Circle :=
    inferInstanceAs (SecondCountableTopology (Metric.sphere (0 : ℂ) 1))
  let : SecondCountableTopology (PontryaginDual A) :=
    (ContinuousMonoidHom.isEmbedding_toContinuousMap A Circle).secondCountableTopology
  have hFourier := schwartzBruhat_fourier_equiv (G := A) μ
  let F := hFourier.choose
  have hF := hFourier.choose_spec
  let T : SchwartzBruhat (PontryaginDual A) →L[ℂ] SchwartzBruhat (PontryaginDual A) :=
    { toFun := schwartzBruhatTranslate η
      map_add' := fun f g ↦ Subtype.ext (funext fun χ ↦ rfl)
      map_smul' := fun a f ↦ Subtype.ext (funext fun χ ↦ rfl)
      cont := (schwartzBruhatTranslate_continuous (G := PontryaginDual A)).comp
        (continuous_const.prodMk continuous_id) }
  let M := F.symm.toContinuousLinearMap.comp (T.comp F.toContinuousLinearMap)
  refine ⟨M, fun f x ↦ ?_⟩
  let g (y : A) := (η y : ℂ) * f y
  have hη : Continuous (fun y : A ↦ (η y : ℂ)) := continuous_subtype_val.comp η.continuous
  have hg : Integrable g μ := by
    simpa only [g, mul_comm] using
      (hF f).1.mul_bdd (c := 1) hη.aestronglyMeasurable (.of_forall fun y ↦ by simp)
  have htransform (χ : PontryaginDual A) : lcaFourier μ (M f) χ = lcaFourier μ g χ := by
    rw [← (hF (M f)).2 χ]
    have hM : F (M f) = T (F f) := F.apply_symm_apply _
    rw [hM]
    change F f (η⁻¹ * χ) = _
    rw [(hF f).2]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y ↦ by
      change f y * star (((η y)⁻¹ * χ y : Circle) : ℂ) = g y * star (χ y : ℂ)
      rw [Circle.coe_mul, Circle.coe_inv_eq_conj, ← Complex.star_def, star_mul, star_star]
      dsimp only [g]
      ring
  let u : A → ℂ := M f
  have hu : Integrable u μ := (hF (M f)).1
  have hz (χ : PontryaginDual A) : lcaFourier μ (u - g) χ = 0 := by
    change (∫ y, (u y - g y) * star (χ y : ℂ) ∂μ) = 0
    simp_rw [sub_mul]
    rw [integral_sub (integrable_fourierIntegrand (G := A) μ hu χ)
      (integrable_fourierIntegrand (G := A) μ hg χ)]
    exact sub_eq_zero.mpr (htransform χ)
  have hae : u =ᵐ[μ] g :=
    (ae_eq_zero_of_lcaFourier_eq_zero (G := A) μ (hu.sub hg) hz).mono
      fun _ hy ↦ sub_eq_zero.mp hy
  have hcont : Continuous u := continuous_schwartzBruhat (G := A) (M f)
  have heq := (hcont.ae_eq_iff_eq μ (hη.mul (continuous_schwartzBruhat (G := A) f))).mp hae
  exact congrFun heq x

omit hSC in
/-- Every compact-subgroup stage admits a refinement on whose quotient a given
unitary character descends. -/
private theorem goodCompact_refine_unitaryCharacter (k : GoodCompact) (η : PontryaginDual G) :
    ∃ (l : GoodCompact) (η' : PontryaginDual (G ⧸ l.val)),
      l.val ≤ k.val ∧ ∀ g : G, η' (g : G ⧸ l.val) = η g := by
  let K' : OpenCompactlyGeneratedSubgroups (PontryaginDual G) :=
    ⟨lcaAnnihilator k.val, isOpen_lcaAnnihilator k.val k.property.1, k.property.2⟩
  have hgroups := openCompactlyGeneratedSubgroups_colimit (G := PontryaginDual G)
  obtain ⟨H, hηH⟩ := hgroups.2.1 η
  obtain ⟨J, hKJ, hHJ⟩ := hgroups.1.directed K' H
  let L := lcaDualAnnihilator J.val
  have hLc : IsCompact (L : Set G) := isCompact_lcaDualAnnihilator J.val J.property.1
  have hAnn : lcaAnnihilator L = J.val :=
    lcaAnnihilator_dualAnnihilator_of_open J.val J.property.1
  have hLgen : IsCompactlyGeneratedGroup (lcaAnnihilator L) := by
    rw [hAnn]
    exact J.property.2
  let l : GoodCompact := ⟨L, hLc, hLgen⟩
  have hlk : l.val ≤ k.val := by
    intro g hg
    rw [← lcaDualAnnihilator_annihilator k.val k.property.1.isClosed]
    exact (mem_lcaDualAnnihilator_iff _ _).mpr fun χ ↦
      (mem_lcaDualAnnihilator_iff _ _).mp hg ⟨χ.val, hKJ χ.property⟩
  obtain ⟨e, he⟩ := lcaQuotientDual_equiv_annihilator L hLc.isClosed
  let ηL : lcaAnnihilator L := ⟨η, by
    rw [hAnn]
    exact hHJ hηH⟩
  refine ⟨l, e.symm ηL, hlk, fun g ↦ ?_⟩
  rw [← he (e.symm ηL) g, e.apply_symm_apply]

/-- The pointwise multiplier on the decay submodule is well-defined because it commutes
with each real twist and preserves Schwartz–Bruhat functions. -/
private def modulatedExponentialDecayUnitaryMultiplication {A : Type*} [CommGroup A]
    [TopologicalSpace A] (n : A →ₜ* ℝ≥0ˣ) (χ : PontryaginDual A)
    (U : SchwartzBruhat A →L[ℂ] SchwartzBruhat A)
    (hU : ∀ (f : SchwartzBruhat A) (x : A), U f x = (χ x : ℂ) * f x) :
    modulatedExponentialDecaySubmodule n I →ₗ[ℂ] modulatedExponentialDecaySubmodule n I :=
  ((LinearMap.mulLeft ℂ (fun x ↦ (χ x : ℂ))).comp
    (modulatedExponentialDecaySubmodule n I).subtype).codRestrict _ (by
      intro f
      refine (Submodule.mem_iInf _).mpr fun a ↦ Submodule.mem_comap.mpr ?_
      let u := U (modulatedExponentialDecayTwist n I a f)
      have h : modulationWeight n a (fun x ↦ (χ x : ℂ) * f.val x) = u.val := by
        funext x
        let w : ℂ := (((n x).val : ℝ) ^ (a : ℝ) : ℝ)
        exact (mul_left_comm w (χ x : ℂ) (f.val x)).trans
          (hU (modulatedExponentialDecayTwist n I a f) x).symm
      exact h ▸ u.property)

-- The unused-section-variable check expands the seminorm families of the decay spaces.
set_option linter.unusedSectionVars false in
include hm hms hInt hne in
/-- Unitary character multiplication commutes with the real twists and is continuous
on the inductive limit by refining each source stage to a quotient carrying the character. -/
private theorem modulatedExponentialDecay_mul_unitaryCharacter (η : PontryaginDual G) :
    ∃ M : E →L[ℂ] E, ∀ f g, (M f).val g = (η g : ℂ) * f.val g := by
  have hMultiply := schwartzBruhat_mul_unitaryCharacter (A := G) η
  let U := hMultiply.choose
  have hU := hMultiply.choose_spec
  let M : E →ₗ[ℂ] E := modulatedExponentialDecayUnitaryMultiplication I m η U hU
  let FinalSeminorms := {p : Seminorm ℂ (modulatedExponentialDecaySubmodule m I) //
    ∀ k : GoodCompact, Continuous (p ∘ modulatedExponentialDecayStageInclusion m I k)}
  have generating := withGeneratingSeminorms_spec _ (Subtype.val : FinalSeminorms → _)
  refine ⟨⟨M, ?_⟩, fun _ _ ↦ rfl⟩
  change Continuous M
  refine generating.continuous_of_continuous_comp M fun p ↦ ?_
  let q : Seminorm ℂ E := p.val.comp M
  change Continuous q
  refine generating.continuous_seminorm (⟨q, fun k ↦ ?_⟩ : FinalSeminorms)
  refine (goodCompact_refine_unitaryCharacter (G := G) k η).elim fun l h ↦ ?_
  refine h.elim fun η' hη ↦ ?_
  have hlk := hη.1
  have hη' := hη.2
  have hTransition := modulatedExponentialDecayStage_transition m I hm hms hInt hne k l hlk
  let j := hTransition.choose
  have hj := hTransition.choose_spec.2
  let : IsClosed (l.val : Set G) := l.property.1.isClosed
  have hMultiply' := schwartzBruhat_mul_unitaryCharacter (A := G ⧸ l.val) η'
  let V := hMultiply'.choose
  have hV := hMultiply'.choose_spec
  let n := quotientModulation m l.val l.property.1
  let B : ModulatedExponentialDecayStage m I l →ₗ[ℂ] ModulatedExponentialDecayStage m I l :=
    modulatedExponentialDecayUnitaryMultiplication I n η' V hV
  have hInd := modulatedExponentialDecayStage_twists_isInducing m I l
  have hB : Continuous B := by
    apply hInd.continuous_iff.mpr
    apply continuous_pi
    intro a
    change Continuous (fun f : ModulatedExponentialDecayStage m I l ↦
      modulatedExponentialDecayTwist n I a (B f))
    have htwist : Continuous (fun f : ModulatedExponentialDecayStage m I l ↦
        modulatedExponentialDecayTwist n I a f) := (continuous_apply a).comp hInd.continuous
    have hVtwist : Continuous (fun f : ModulatedExponentialDecayStage m I l ↦
        V (modulatedExponentialDecayTwist n I a f)) := V.continuous.comp htwist
    have hcomm (f : ModulatedExponentialDecayStage m I l) :
        V (modulatedExponentialDecayTwist n I a f) =
          modulatedExponentialDecayTwist n I a (B f) := by
      apply Subtype.ext
      funext x
      let w : ℂ := (((n x).val : ℝ) ^ (a : ℝ) : ℝ)
      change V (modulatedExponentialDecayTwist n I a f) x =
        w * ((η' x : ℂ) * f.val x)
      exact (hV (modulatedExponentialDecayTwist n I a f) x).trans
        (mul_left_comm (η' x : ℂ) w (f.val x))
    exact hVtwist.congr hcomm
  have hcomm (f : ModulatedExponentialDecayStage m I k) :
      modulatedExponentialDecayStageInclusion m I l (B (j f)) =
        M (modulatedExponentialDecayStageInclusion m I k f) := by
    apply Subtype.ext
    funext g
    change (η' (g : G ⧸ l.val) : ℂ) * (j f).val (g : G ⧸ l.val) =
      (η g : ℂ) * f.val (g : G ⧸ k.val)
    exact congrArg₂ (fun z : Circle ↦ fun w : ℂ ↦ (z : ℂ) * w) (hη' g) (hj f g)
  change Continuous (fun f : ModulatedExponentialDecayStage m I k ↦
    p.val (M (modulatedExponentialDecayStageInclusion m I k f)))
  have hstage : Continuous (fun f : ModulatedExponentialDecayStage m I k ↦
      p.val (modulatedExponentialDecayStageInclusion m I l (B (j f)))) :=
    (p.property l).comp (hB.comp j.continuous)
  exact hstage.congr fun f ↦ congrArg p.val (hcomm f)

set_option linter.unusedSectionVars false in
include hm hms in
/-- The quasi-character multiplier is the composition of its unitary multiplier and the
real shift given by its abscissa. -/
private theorem modulatedExponentialDecay_quasiCharacterMultiplier (d : QuasiCharacter G) :
    ∃ M : ModulatedExponentialDecay m univ →L[ℂ] ModulatedExponentialDecay m univ,
      ∀ f g, (M f).val g = d g * f.val g := by
  let D := ModulatedExponentialDecay m univ
  have hnonzero (g : G) : d g ≠ 0 := ((Group.isUnit g).map d).ne_zero
  let a := quasiCharacterAbscissa m hm.1 hm.2 d
  have habs (g : G) : ‖d g‖ = ((m g).val : ℝ) ^ a :=
    norm_quasiCharacter_eq_rpow_abscissa m hm.1 hm.2 d g
  let unit (g : G) := d g / (‖d g‖ : ℂ)
  have hnorm (g : G) : ‖unit g‖ = 1 := by
    change ‖d g / (‖d g‖ : ℂ)‖ = 1
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
      div_self (norm_ne_zero_iff.mpr (hnonzero g))]
  let η : PontryaginDual G :=
    { toFun := fun g ↦ ⟨unit g, mem_sphere_zero_iff_norm.mpr (hnorm g)⟩
      map_one' := Circle.ext (by simp [unit])
      map_mul' := fun g h ↦ Circle.ext (by
        change unit (g * h) = unit g * unit h
        simp only [unit, map_mul, norm_mul, Complex.ofReal_mul, mul_div_mul_comm])
      continuous_toFun := (d.continuous.div (Complex.continuous_ofReal.comp d.continuous.norm)
        (fun g ↦ Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hnonzero g)))).subtype_mk _ }
  have hMultiply := modulatedExponentialDecay_mul_unitaryCharacter m univ hm hms
    ordConnected_univ univ_nonempty η
  let U := hMultiply.choose
  have hU := hMultiply.choose_spec
  have hJ : (fun b : ℝ ↦ b - a) '' univ = univ :=
    image_univ_of_surjective fun b ↦ ⟨b + a, add_sub_cancel_right b a⟩
  have hshift : ∃ S : D ≃L[ℂ] D, ∀ f, (S f).val = modulationWeight m a f.val :=
    (congrArg (fun J : Set ℝ ↦ ∃ S : D ≃L[ℂ] ModulatedExponentialDecay m J,
      ∀ f, (S f).val = modulationWeight m a f.val) hJ).mp
      (modulatedExponentialDecay_shift_equiv m univ hm hms ordConnected_univ univ_nonempty a)
  let S := hshift.choose
  have hS := hshift.choose_spec
  refine ⟨U.comp S.toContinuousLinearMap, fun f g ↦ ?_⟩
  change (U (S f)).val g = _
  rw [hU (S f) g, hS f]
  change (d g / (‖d g‖ : ℂ)) * (((((m g).val : ℝ) ^ a : ℝ) : ℂ) * f.val g) = _
  rw [← habs g, ← mul_assoc, div_mul_cancel₀ _
    (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hnonzero g)))]

set_option linter.unusedSectionVars false in
include hm hms in
/-- Paper: Remark D.3.3.6, p. 806. Multiplication by a continuous quasi-character
is a topological automorphism of the space with two-sided exponential decay. -/
theorem modulatedExponentialDecay_mul_quasiCharacter (c : QuasiCharacter G) :
    ∃ e : ModulatedExponentialDecay m univ ≃L[ℂ] ModulatedExponentialDecay m univ,
      ∀ f g, (e f).val g = c g * f.val g := by
  let D := ModulatedExponentialDecay m univ
  have cancel {X : Type _} (value : X → G → ℂ) (hinj : Injective value)
      (A B : X → X) (a b : G → ℂ)
      (hA : ∀ f g, value (A f) g = a g * value f g)
      (hB : ∀ f g, value (B f) g = b g * value f g) (hab : ∀ g, b g * a g = 1) :
      LeftInverse B A := by
    intro f
    apply hinj
    funext g
    rw [hB (A f) g, hA f g, ← mul_assoc, hab g, one_mul]
  let cInv := c.comp (ContinuousMonoidHom.inv G)
  refine (modulatedExponentialDecay_quasiCharacterMultiplier m hm hms c).elim fun M hM ↦ ?_
  refine (modulatedExponentialDecay_quasiCharacterMultiplier m hm hms cInv).elim fun N hN ↦ ?_
  have hInv (g : G) : cInv g = (c g)⁻¹ := map_inv c g
  have hcancel (g : G) : cInv g * c g = 1 := by
    rw [hInv, inv_mul_cancel₀ ((Group.isUnit g).map c).ne_zero]
  have hleft : LeftInverse N M :=
    cancel (fun f : D ↦ f.val) Subtype.val_injective M N c cInv hM hN hcancel
  have hright : RightInverse N M :=
    cancel (fun f : D ↦ f.val) Subtype.val_injective N M cInv c hN hM fun g ↦
      (mul_comm _ _).trans (hcancel g)
  exact ⟨ContinuousLinearEquiv.equivOfInverse M N hleft hright, hM⟩

end Stages

section Structure

variable [hSC : SecondCountableTopology G]
variable (hm : IsModulation m) (hInt : OrdConnected I) (hne : I.Nonempty)
variable (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ m)

include hτ in
/-- Paper: §D.3.3.1, p. 806. A splitting gives each quasi-character in the
relative strip a unique pair of coordinates, a kernel character and an exponent in the strip. -/
theorem modulatedExponentialDecay_strip_coordinates
    (c : relativeVerticalStrip m.toMonoidHom hm.1 hm.2 I) :
    ∃! p : PontryaginDual K × ℂ, p.2.re ∈ I ∧
      ∀ (u : K) (t : ℝ≥0ˣ),
        (c : QuasiCharacter G) ((u : G) * τ t) = (p.1 u : ℂ) * ((t.val : ℝ) : ℂ) ^ p.2 := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp
    (hm.1.isCompact_preimage (isCompact_singleton (x := 1)))
  let d : QuasiCharacter G := c
  obtain ⟨e, he⟩ :=
    quasiCharacterParametrization_of_split m.toMonoidHom m.continuous τ hτ
  obtain ⟨hs, hχ⟩ := he d
  change ∀ t : ℝ≥0ˣ, d (τ t) = ((t.val : ℝ) : ℂ) ^ (e d).1 at hs
  have hre : (e d).1.re = quasiCharacterAbscissa m.toMonoidHom hm.1 hm.2 d := by
    let t : ℝ≥0ˣ := Units.mk0 2 (by norm_num)
    have ht : (t.val : ℝ) = 2 := by norm_num [t]
    have hnorm := norm_quasiCharacter_eq_rpow_abscissa m.toMonoidHom hm.1 hm.2 d (τ t)
    change ‖d (τ t)‖ = ((m.toMonoidHom (τ t)).val : ℝ) ^ _ at hnorm
    rw [hs t, show m.toMonoidHom (τ t) = t from hτ t, ht,
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2)] at hnorm
    exact (Real.rpow_right_inj (by norm_num : (0 : ℝ) < 2) (by norm_num)).mp hnorm
  refine ⟨((e d).2, (e d).1), ⟨?_, ?_⟩, ?_⟩
  · change (e d).1.re ∈ I
    rw [hre]
    exact c.property
  · intro u t
    change d ((u : G) * τ t) = ((e d).2 u : ℂ) * ((t.val : ℝ) : ℂ) ^ (e d).1
    rw [map_mul, hχ u, hs t]
  · rintro ⟨χ, s⟩ ⟨_, h⟩
    apply Prod.ext
    · apply ContinuousMonoidHom.ext
      intro u
      apply Circle.ext
      have hu : d (u : G) = (χ u : ℂ) := by simpa using h u 1
      exact hu.symm.trans (hχ u).symm
    · obtain ⟨_, _, hz⟩ := existsUnique_complexPower (d.comp τ)
      refine (hz s fun t ↦ ?_).trans (hz (e d).1 hs).symm
      simpa using h 1 t

local notation "T" => InductiveTensor (SchwartzBruhat K) P

/-- A surjective inducing continuous linear map out of a separated space
can be bundled as a continuous linear equivalence with the same evaluations. -/
private theorem bundle_inducing_surjection
    {A B : Type*} [AddCommGroup A] [Module ℂ A] [TopologicalSpace A] [T0Space A]
    [AddCommGroup B] [Module ℂ B] [TopologicalSpace B]
    (p : (A → B) → Prop)
    (hex : ∃ F : A →L[ℂ] B, p F)
    (hs : ∀ F : A →L[ℂ] B, p F → Surjective F)
    (hi : ∀ F : A →L[ℂ] B, p F → IsInducing F) :
    ∃ e : A ≃L[ℂ] B, p e := by
  rcases hex with ⟨F, hF⟩
  have hh : IsHomeomorph F := isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨(hi F hF).isEmbedding, hs F hF⟩
  exact ⟨ContinuousLinearEquiv.ofIsHomeomorph
      (LinearEquiv.ofBijective F.toLinearMap hh.bijective) hh, hF⟩

open scoped SchwartzMap in
/-- Paper: Remark D.3.2.2, p. 801. Translation in logarithmic coordinates acts on each
weighted Schwartz profile by Schwartz translation followed by multiplication by a constant. -/
private theorem exists_positiveRealExponentialDecay_translate (c : ℝ) (hI : I.Nonempty) :
    ∃ L : P →L[ℂ] P, ∀ f x, (L f).val x = f.val (x - c) := by
  let shift : ℝ → ℝ := fun x ↦ x - c
  have hIsometry : Isometry shift := by
    apply Isometry.of_dist_eq
    intro x y
    simp only [shift, dist_eq_norm, sub_sub_sub_cancel_right]
  let S : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) := SchwartzMap.compCLMOfAntilipschitz ℂ
    (Function.HasTemperateGrowth.id'.sub (Function.HasTemperateGrowth.const c))
    hIsometry.antilipschitzWith
  let weighted (a : I) : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
    (Real.exp ((a : ℝ) * c) : ℂ) • S
  have hw (a : I) (f : P) (x : ℝ) :
      weighted a (logExponentialDecayTwist I a f) x =
        (Real.exp ((a : ℝ) * x) : ℂ) * f.val (x - c) := by
    have hexp : (a : ℝ) * c + (a : ℝ) * (x - c) = (a : ℝ) * x := by ring
    change (Real.exp ((a : ℝ) * c) : ℂ) * logExponentialDecayTwist I a f (x - c) = _
    rw [logExponentialDecayTwist_apply I a f (x - c), ← mul_assoc, ← Complex.ofReal_mul,
      ← Real.exp_add, hexp]
  let shiftLinear : P →ₗ[ℂ] (ℝ → ℂ) :=
    (LinearMap.pi fun x ↦ LinearMap.proj (x - c)).comp (logExponentialDecaySubmodule I).subtype
  let L : P →ₗ[ℂ] P := shiftLinear.codRestrict (logExponentialDecaySubmodule I) (by
    intro f
    refine (Submodule.mem_iInf _).mpr fun a ↦ Submodule.mem_comap.mpr ?_
    exact ⟨weighted a (logExponentialDecayTwist I a f), funext (hw a f)⟩)
  refine ⟨⟨L, ?_⟩, fun _ _ ↦ rfl⟩
  have hInd := (positiveRealExponentialDecay_isEmbedding I hI).isInducing
  apply hInd.continuous_iff.mpr
  apply continuous_pi
  intro a
  refine ((weighted a).continuous.comp ((continuous_apply a).comp hInd.continuous)).congr
    fun f ↦ ?_
  exact SchwartzMap.ext fun x ↦ (hw a f x).trans (logExponentialDecayTwist_apply I a (L f) x).symm

set_option linter.unusedSectionVars false in
/-- Point evaluation on the decay space is continuous because on each quotient
stage it is a constant multiple of evaluation of any one weighted profile. -/
private theorem continuous_modulatedExponentialDecay_eval (hI : I.Nonempty) (g : G) :
    Continuous (fun f : E ↦ f.val g) := by
  let b : I := ⟨hI.choose, hI.choose_spec⟩
  let ev : E →ₗ[ℂ] ℂ := (LinearMap.proj g).comp (modulatedExponentialDecaySubmodule m I).subtype
  let p : Seminorm ℂ E := (normSeminorm ℂ ℂ).comp ev
  have hp : Continuous p := by
    apply (withGeneratingSeminorms_spec _ _).continuous_seminorm
      (⟨p, ?_⟩ : {q : Seminorm ℂ (modulatedExponentialDecaySubmodule m I) //
        ∀ k : GoodCompact, Continuous (q ∘ modulatedExponentialDecayStageInclusion m I k)})
    intro k
    let x : G ⧸ k.val := g
    let n := quotientModulation m k.val k.property.1
    let w : ℂ := ((((n x).val : ℝ) ^ (b : ℝ) : ℝ) : ℂ)
    have hw : w ≠ 0 := Complex.ofReal_ne_zero.mpr
      (Real.rpow_pos_of_pos (NNReal.coe_pos.mpr (Units.zero_lt (n x))) b).ne'
    let twists (f : ModulatedExponentialDecayStage m I k) (b : I) :
        SchwartzBruhat (G ⧸ k.val) := modulatedExponentialDecayTwist n I b f
    have hInd : IsInducing twists := modulatedExponentialDecayStage_twists_isInducing m I k
    have hproj : Continuous (fun F : I → SchwartzBruhat (G ⧸ k.val) ↦ F b) := continuous_apply b
    have hx : Continuous (fun f : ModulatedExponentialDecayStage m I k ↦ twists f b x) :=
      (continuous_schwartzBruhat_eval x).comp (hproj.comp hInd.continuous)
    change Continuous (fun f : ModulatedExponentialDecayStage m I k ↦ ‖f.val x‖)
    refine (continuous_const (y := w⁻¹).mul hx).norm.congr ?_
    intro f
    change ‖w⁻¹ * (w * f.val x)‖ = ‖f.val x‖
    rw [← mul_assoc, inv_mul_cancel₀ hw, one_mul]
  exact (norm_withSeminorms ℂ ℂ).continuous_of_continuous_comp ev (fun _ ↦ hp)

/-- Continuous linear maps induce a uniformly continuous map on the inductive tensor product. -/
private theorem uniformContinuous_inductiveTensorMap {U V : Type*}
    [AddCommGroup U] [Module ℂ U] [TopologicalSpace U]
    [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    (A : U →L[ℂ] U) (B : V →L[ℂ] V) :
    UniformContinuous (inductiveTensorMap A.toLinearMap B.toLinearMap :
      InductiveTensor U V → InductiveTensor U V) := by
  let M := inductiveTensorMap A.toLinearMap B.toLinearMap
  apply uniformContinuous_addMonoidHom_of_continuous (f := M.toAddMonoidHom)
  have hS := withGeneratingSeminorms_spec (U ⊗[ℂ] V)
    (fun q : {q : Seminorm ℂ (U ⊗[ℂ] V) //
      (∀ a : U, Continuous (fun b : V ↦ q (a ⊗ₜ[ℂ] b))) ∧
      (∀ b : V, Continuous (fun a : U ↦ q (a ⊗ₜ[ℂ] b)))} ↦ q.val)
  refine hS.continuous_of_continuous_comp M fun q ↦ ?_
  exact hS.continuous_seminorm
    ⟨q.val.comp M, fun a ↦ (q.property.1 (A a)).comp B.continuous,
      fun b ↦ (q.property.2 (B b)).comp A.continuous⟩

section

universe u

/-- Equality of two point evaluations after a tensor map can be checked on pure tensors. -/
private theorem inductiveTensor_completion_eval_eq {U W : Type u} {V : Type}
    [AddCommGroup U] [Module ℂ U] [TopologicalSpace U]
    [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
    (e : Completion (InductiveTensor U V) ≃L[ℂ] W)
    (A : U →L[ℂ] U) (B : V →L[ℂ] V) (a b : W → ℂ)
    (aL bL : W →ₗ[ℂ] ℂ) (ha : ∀ z, aL z = a z) (hb : ∀ z, bL z = b z)
    (h : ∀ u v,
      aL (e (Completion.coe' (α := InductiveTensor U V) (A u ⊗ₜ[ℂ] B v))) =
        bL (e (Completion.coe' (α := InductiveTensor U V) (u ⊗ₜ[ℂ] v))))
    (x : InductiveTensor U V) (y z : Completion (InductiveTensor U V))
    (hy : y = Completion.coe' (inductiveTensorMap A.toLinearMap B.toLinearMap x))
    (hz : z = Completion.coe' x) : a (e y) = b (e z) := by
  let M := inductiveTensorMap A.toLinearMap B.toLinearMap
  let J : InductiveTensor U V →ₗ[ℂ] W := e.toLinearEquiv.toLinearMap.comp
    (Completion.toComplL : InductiveTensor U V →L[ℂ] Completion (InductiveTensor U V)).toLinearMap
  have hEq : aL.comp (J.comp M) = bL.comp J := TensorProduct.ext' h
  calc
    _ = a (e (Completion.coe' (M x))) := congrArg (fun w ↦ a (e w)) hy
    _ = aL (e (Completion.coe' (M x))) := (ha _).symm
    _ = bL (e (Completion.coe' x)) := LinearMap.congr_fun hEq x
    _ = b (e (Completion.coe' x)) := hb _
    _ = _ := congrArg (fun w ↦ b (e w)) hz.symm


end

include hτ in
/-- Equivariance on the image of the algebraic tensor product, where it follows
from the split-coordinate formula on pure tensors and linearity. -/
private theorem modulatedExponentialDecay_tensor_equivariant_coe
    [CompactSpace K] [SecondCountableTopology K]
    (e : Completion T ≃L[ℂ] E)
    (he : ∀ (h : SchwartzBruhat K) (f : P) (u : K) (t : ℝ≥0ˣ),
      (e (Completion.coe' (α := T) (h ⊗ₜ[ℂ] f))).val ((u : G) * τ t) =
        h u * f.val (Real.log (t.val : ℝ)))
    (u : K) (t : ℝ≥0ˣ) (L : P →L[ℂ] P)
    (hL : ∀ f x, (L f).val x = f.val (x - Real.log (t.val : ℝ)))
    (x : T) (g : G) :
    (e (Completion.map (inductiveTensorMap
      ((schwartzBruhatTranslationAction (G := K)) u).toLinearMap L.toLinearMap : T → T)
      (Completion.coe' x))).val g = (e (Completion.coe' x)).val (((u : G) * τ t)⁻¹ * g) := by
  let A := schwartzBruhatTranslationAction (G := K) u
  let g' := ((u : G) * τ t)⁻¹ * g
  let ev (a : G) : E →ₗ[ℂ] ℂ :=
    { toFun := fun f ↦ f.val a
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hPure (h : SchwartzBruhat K) (f : P) :
      (e (Completion.coe' (α := T) (A h ⊗ₜ[ℂ] L f))).val g =
        (e (Completion.coe' (α := T) (h ⊗ₜ[ℂ] f))).val g' := by
    let v : K := ⟨g / τ (m g), by
      change m (g / τ (m g)) = 1
      rw [map_div, hτ (m g), div_self']⟩
    let s := m g
    have hg : g = (v : G) * τ s := (div_mul_cancel _ _).symm
    have hg' : g' = ((u⁻¹ * v : K) : G) * τ (t⁻¹ * s) := by
      change ((u : G) * τ t)⁻¹ * g = _
      rw [hg, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, mul_inv_rev]
      simp only [mul_assoc, mul_left_comm, mul_comm]
    have hlog : Real.log ((t⁻¹ * s : ℝ≥0ˣ).val : ℝ) =
        Real.log (s.val : ℝ) - Real.log (t.val : ℝ) := by
      rw [mul_comm t⁻¹ s, Units.val_mul, NNReal.coe_mul, Units.val_inv_eq_inv_val,
        NNReal.coe_inv, ← div_eq_mul_inv, Real.log_div
          (NNReal.coe_ne_zero.mpr s.ne_zero) (NNReal.coe_ne_zero.mpr t.ne_zero)]
    calc
      _ = A h v * (L f).val (Real.log (s.val : ℝ)) :=
        (congrArg (e (Completion.coe' (α := T) (A h ⊗ₜ[ℂ] L f))).val hg).trans (he _ _ v s)
      _ = h (u⁻¹ * v) * f.val (Real.log ((t⁻¹ * s).val : ℝ)) :=
        congrArg₂ (· * ·) (schwartzBruhatTranslationAction_apply u v h)
          ((hL f _).trans (congrArg f.val hlog.symm))
      _ = _ :=
        ((congrArg (e (Completion.coe' (α := T) (h ⊗ₜ[ℂ] f))).val hg').trans (he h f _ _)).symm
  have hev (a : G) (z : E) : ev a z = z.val a := rfl
  have hPure' (h : SchwartzBruhat K) (f : P) :
      ev g (e (Completion.coe' (α := T) (A h ⊗ₜ[ℂ] L f))) =
        ev g' (e (Completion.coe' (α := T) (h ⊗ₜ[ℂ] f))) :=
    (hev g _).trans ((hPure h f).trans (hev g' _).symm)
  let M : T →ₗ[ℂ] T := inductiveTensorMap A.toLinearMap L.toLinearMap
  let y : Completion T := Completion.map (inductiveTensorMap
    ((schwartzBruhatTranslationAction (G := K)) u).toLinearMap L.toLinearMap : T → T)
    (Completion.coe' x)
  let z : Completion T := Completion.coe' x
  have hUniform := uniformContinuous_inductiveTensorMap (U := SchwartzBruhat K) (V := P) A L
  have hy : y = Completion.coe' (M x) := Completion.map_coe hUniform x
  let H := inductiveTensor_completion_eval_eq (U := SchwartzBruhat K) (V := P) (W := E)
    e A L (fun f : E ↦ f.val g) (fun f : E ↦ f.val (((u : G) * τ t)⁻¹ * g))
    (ev g) (ev g') (hev g) (hev g')
  have hResult := H hPure' x y z hy rfl
  with_reducible exact hResult

set_option linter.unusedSectionVars false in
include hm hInt hne hτ in
/-- Paper: Theorem D.3.3.7(1), p. 806. The tensor isomorphism intertwines
translation in each factor with translation on G. -/
theorem modulatedExponentialDecay_tensor_equivariant
    (e : Completion T ≃L[ℂ] E)
    (he : ∀ (h : SchwartzBruhat K) (f : P) (u : K) (t : ℝ≥0ˣ),
      (e (Completion.coe' (α := T) (h ⊗ₜ[ℂ] f))).val ((u : G) * τ t) =
        h u * f.val (Real.log (t.val : ℝ))) :
    letI : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
    letI : SecondCountableTopology K := TopologicalSpace.Subtype.secondCountableTopology (K : Set G)
    ∀ (u : K) (t : ℝ≥0ˣ), ∃ L : P →L[ℂ] P,
      (∀ f x, (L f).val x = f.val (x - Real.log (t.val : ℝ))) ∧
      ∀ z : Completion T, ∀ g : G,
        (e (Completion.map (inductiveTensorMap
          ((schwartzBruhatTranslationAction (G := K)) u).toLinearMap L.toLinearMap : T → T) z)
          ).val g = (e z).val (((u : G) * τ t)⁻¹ * g) := by
  intro u t
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let : SecondCountableTopology K := TopologicalSpace.Subtype.secondCountableTopology (K : Set G)
  have hTranslate := exists_positiveRealExponentialDecay_translate I (Real.log (t.val : ℝ)) hne
  let L : P →L[ℂ] P := hTranslate.choose
  have hL := hTranslate.choose_spec
  refine ⟨L, hL, fun z g ↦ ?_⟩
  let g' := ((u : G) * τ t)⁻¹ * g
  induction z using Completion.induction_on with
  | hp =>
    apply isClosed_eq (X := ℂ)
    · exact (continuous_modulatedExponentialDecay_eval m I hne g).comp
        (e.continuous.comp Completion.continuous_map)
    · exact (continuous_modulatedExponentialDecay_eval m I hne g').comp e.continuous
  | ih x =>
    apply modulatedExponentialDecay_tensor_equivariant_coe m I τ hτ e he u t L
    exact hL

include hSC hm hInt hne hτ in
/-- Paper: Theorem D.3.3.7(1), p. 806. The tensor isomorphism on a quotient
stage commutes with the two inclusions into the full spaces, and the inclusion of the stage is
continuous for the locally convex topology of the full decay space. (The inclusion is declared
with the bare submodule as its target, so the topology is named explicitly here: without that,
Lean takes the topology of pointwise convergence.)
Deviation: The subgroup on the norm-one factor is the restriction of k to that factor. -/
theorem modulatedExponentialDecay_tensor_stage
    (e : Completion T ≃L[ℂ] E)
    (he : ∀ (h : SchwartzBruhat K) (f : P) (u : K) (t : ℝ≥0ˣ),
      (e (Completion.coe' (α := T) (h ⊗ₜ[ℂ] f))).val ((u : G) * τ t) =
        h u * f.val (Real.log (t.val : ℝ)))
    (k : GoodCompact) :
    let k₁ := k.val.comap (Subgroup.subtype K)
    let Tₖ := InductiveTensor (SchwartzBruhat (K ⧸ k₁)) P
    ∃ (eₖ : Completion Tₖ ≃L[ℂ] ModulatedExponentialDecayStage m I k)
      (j : SchwartzBruhat (K ⧸ k₁) →L[ℂ] SchwartzBruhat K),
      (∀ h u, j h u = h (u : K ⧸ k₁)) ∧
      (∀ (h : SchwartzBruhat (K ⧸ k₁)) (f : P) (u : K) (t : ℝ≥0ˣ),
        (eₖ (Completion.coe' (α := Tₖ) (h ⊗ₜ[ℂ] f))).val
          (((u : G) * τ t : G) : G ⧸ k.val) = h (u : K ⧸ k₁) * f.val (Real.log (t.val : ℝ))) ∧
      @Continuous (ModulatedExponentialDecayStage m I k) E _ _
        (modulatedExponentialDecayStageInclusion m I k) ∧
      ∀ z : Completion Tₖ,
        modulatedExponentialDecayStageInclusion m I k (eₖ z) =
          e (Completion.map (inductiveTensorMap j.toLinearMap
            (LinearMap.id : P →ₗ[ℂ] P) : Tₖ → T) z) := by sorry

/-- An elementary group has a largest Bruhat stage, whose realization is a homeomorphism. -/
private theorem schwartzBruhat_frechet_of_elementary {Q : Type*} [CommGroup Q] [TopologicalSpace Q]
    [IsTopologicalGroup Q] [T2Space Q] [LocallyCompactSpace Q] (hgen : IsCompactlyGeneratedGroup Q)
    (hlocal : IsLocallyEuclidean Q) : IsFrechetTVS (SchwartzBruhat Q) := by
  let e := Classical.choice ((lca_elementary_iff (G := Q)).mp ⟨hgen, hlocal⟩)
  let _ := e.finiteGroup
  let _ := e.finiteTopology
  let _ := e.finiteDiscrete
  let _ := e.finiteFintype
  have : SecondCountableTopology Q := e.equiv.toHomeomorph.isEmbedding.secondCountableTopology
  let top : (⊤ : Subgroup Q) ≃ₜ* Q :=
    { Subgroup.topEquiv with
      continuous_toFun := continuous_subtype_val
      continuous_invFun := continuous_id.subtype_mk _ }
  let a : BruhatStructuralPair Q := ⟨(⊤, OrderDual.toDual ⊥), isOpen_univ,
    isCompactlyGeneratedGroup_of_continuousMulEquiv top.symm hgen,
    isBruhatGoodSubgroup_bot_iff.mpr hlocal, bot_le⟩
  let p := Classical.choice a.elementary
  have ha (b : BruhatStructuralPair Q) : b ≤ a := by
    change b.val.1 ≤ ⊤ ∧ (⊥ : Subgroup Q) ≤ OrderDual.ofDual b.val.2
    exact ⟨le_top, bot_le⟩
  let J : SchwartzBruhatStage p →ₗ[ℂ] SchwartzBruhat Q := schwartzBruhatStageInclusion a p
  have hJ : IsEmbedding J := schwartzBruhatStage_isEmbedding a p
  have hsurj : Surjective J := schwartzBruhat_maxStage_surjective a ha p
  let H : SchwartzBruhatStage p ≃ₜ SchwartzBruhat Q :=
    (Equiv.ofBijective J ⟨hJ.injective, hsurj⟩).toHomeomorphOfIsInducing hJ.isInducing
  let _ := p.finiteGroup
  let _ := p.finiteTopology
  let _ := p.finiteDiscrete
  let _ := p.finiteFintype
  have hF : IsFrechetTVS (SchwartzBruhatStage p) :=
    elementarySchwartz_isFrechet (m := p.realDim) (n := p.torusDim) (r := p.latticeRank)
      (F := p.finiteFactor)
  let _ : MetrizableSpace (SchwartzBruhatStage p) := hF.choose_spec.2.1
  refine ⟨inferInstance, inferInstance, H.symm.isEmbedding.metrizableSpace, ?_⟩
  rw [IsUniformAddGroup.rightUniformSpace_eq]
  exact schwartzBruhat_complete

/-- An injective continuous homomorphism pulls back a neighborhood containing no nontrivial
cyclic subgroup, which supplies Euclidean local coordinates on a locally compact group. -/
private theorem locallyEuclidean_of_injective_hom {X Y : Type*} [CommGroup X] [TopologicalSpace X]
    [IsTopologicalGroup X] [T2Space X] [LocallyCompactSpace X]
    [CommGroup Y] [TopologicalSpace Y] [IsTopologicalGroup Y] [T2Space Y] [LocallyCompactSpace Y]
    (i : X →ₜ* Y) (hi : Injective i) (hy : IsLocallyEuclidean Y) : IsLocallyEuclidean X := by
  obtain ⟨W, hW, hPow⟩ := exists_nhds_one_of_isLocallyEuclidean hy
  have hW' : W ∈ 𝓝 (i 1) := by rwa [map_one]
  refine isLocallyEuclidean_of_noSmallCyclicSubgroups (i.continuous.continuousAt.preimage_mem_nhds hW') ?_
  intro x hx
  exact hi ((hPow (i x) fun n ↦ map_pow i x n ▸ hx n).trans (map_one i).symm)

include hSC hm hInt hne hτ in
/-- Paper: Theorem D.3.3.7(1), p. 806. The comparison from the completed
inductive tensor product at a compact-subgroup stage to the completed
projective tensor product is a topological isomorphism. -/
theorem modulatedExponentialDecay_stage_tensor_comparison (k : GoodCompact) :
    let Q := SchwartzBruhat (K ⧸ k.val.comap (Subgroup.subtype K))
    IsHomeomorph (@Completion.map (InductiveTensor Q P) _ (ProjectiveTensor Q P) _ id) :=
  by
  intro Q
  let k₁ := k.val.comap (Subgroup.subtype K)
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let : IsClosed (k.val : Set G) := k.property.1.isClosed
  let : IsClosed (k₁ : Set K) := k.property.1.isClosed.preimage continuous_subtype_val
  let f : K →* G ⧸ k.val := (QuotientGroup.mk' k.val).comp (Subgroup.subtype K)
  have hker : k₁ = f.ker := congrArg (fun H : Subgroup G ↦ H.comap (Subgroup.subtype K))
    (QuotientGroup.ker_mk' k.val).symm
  let j : (K ⧸ k₁) →ₜ* G ⧸ k.val := ⟨QuotientGroup.lift k₁ f hker.le,
    (QuotientGroup.isQuotientMap_mk k₁).continuous_iff.mpr (QuotientGroup.continuous_mk.comp continuous_subtype_val)⟩
  have hj : Injective j := (QuotientGroup.injective_lift_iff k₁ f hker.le).mpr hker
  let d := (lcaQuotientDual_equiv_annihilator k.val k.property.1.isClosed).choose
  have hloc := isLocallyEuclidean_of_isCompactlyGeneratedGroup_dual
    (isCompactlyGeneratedGroup_of_continuousMulEquiv d.symm k.property.2)
  have hQ := schwartzBruhat_frechet_of_elementary isCompactlyGeneratedGroup_of_compact
    (locallyEuclidean_of_injective_hom j hj hloc)
  have hP := positiveRealExponentialDecay_frechet I hInt hne
  let : MetrizableSpace Q := hQ.choose_spec.2.1
  let : MetrizableSpace P := hP.choose_spec.2.1
  exact completedInductiveTensor_to_projectiveTensor_of_frechet hQ hP

include hSC hm hInt hne hτ

omit hSC hm hInt hne hτ in
/-- An embedded Fréchet stage is linearly homeomorphic to its image and gives that
image the same complete metrizable locally convex structure. -/
private theorem frechet_range_of_embedding {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [UniformSpace X] [IsUniformAddGroup X]
    [AddCommGroup Y] [Module ℂ Y] [UniformSpace Y] [IsUniformAddGroup Y]
    [PolynormableSpace ℂ Y] (i : X →ₗ[ℂ] Y) (hi : IsEmbedding i) (hF : IsFrechetTVS X) :
    IsFrechetTVS i.range := by
  let e := LinearEquiv.ofInjective i hi.injective
  have he : IsInducing e := IsInducing.subtypeVal.of_comp_iff.mp hi.isInducing
  let h := e.toEquiv.toHomeomorphOfIsInducing he
  obtain ⟨_, _, hmet, hcomp⟩ := hF
  refine ⟨inferInstance, inferInstance, h.symm.isEmbedding.metrizableSpace, ?_⟩
  let : UniformSpace i.range := IsTopologicalAddGroup.rightUniformSpace _
  let : IsUniformAddGroup i.range := isUniformAddGroup_of_addCommGroup
  rw [IsUniformAddGroup.rightUniformSpace_eq (G := X)] at hcomp
  exact ((AddMonoidHom.isUniformInducing_of_isInducing
    (f := e.toLinearMap.toAddMonoidHom) he).completeSpace_congr e.surjective).mp hcomp

omit hSC hm hInt hne hτ in
/-- Identifying embedded stages with their ranges preserves the final seminorm tests. -/
private theorem finalTopology_range_stages {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    [TopologicalSpace Y] {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Module ℂ (X n)]
    [∀ n, TopologicalSpace (X n)] (i : ∀ n, X n →ₗ[ℂ] Y) (hi : ∀ n, IsEmbedding (i n)) :
    locallyConvexFinalTopology i = locallyConvexFinalTopology (fun n ↦ (i n).range.subtype) := by
  have hp : (fun p : Seminorm ℂ Y ↦ ∀ n, Continuous (p ∘ i n)) =
      (fun p : Seminorm ℂ Y ↦ ∀ n, Continuous (p ∘ (i n).range.subtype)) := by
    funext p
    apply propext
    apply forall_congr'
    intro n
    let e := LinearEquiv.ofInjective (i n) (hi n).injective
    have he : IsInducing e := IsInducing.subtypeVal.of_comp_iff.mp (hi n).isInducing
    exact (e.toEquiv.toHomeomorphOfIsInducing he).isQuotientMap.continuous_iff (g := p ∘ (i n).range.subtype) |>.symm
  exact congrArg (fun pred : Seminorm ℂ Y → Prop ↦
    (SeminormFamily.moduleFilterBasis (Subtype.val : Subtype pred → Seminorm ℂ Y)).topology) hp

/-- The cofinal quotient stages have increasing ranges in the decay space. -/
private theorem decay_stage_ranges_mono (k : ℕ → GoodCompact) (hk : Antitone (fun n ↦ (k n).val)) :
    Monotone (fun n ↦ (modulatedExponentialDecayStageInclusion m I (k n)).range) := by
  intro a b hab x hx
  have htrans := modulatedExponentialDecayStage_transition m I hm hτ.surjective hInt hne
    (k a) (k b) (hk hab)
  exact hx.elim fun f hf ↦ ⟨htrans.choose f, (Subtype.ext (funext (htrans.choose_spec.2 f))).trans hf⟩
omit hSC hm hInt hne hτ in
/-- Embedded Fréchet stages give a strict LF presentation by their ranges. -/
private theorem strictLF_of_embedded_stages {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    [UniformSpace Y] [IsUniformAddGroup Y] [PolynormableSpace ℂ Y]
    {A : Type*} {X : A → Type*} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    [∀ a, UniformSpace (X a)] [∀ a, IsUniformAddGroup (X a)]
    (i : ∀ a, X a →ₗ[ℂ] Y) (k : ℕ → A) (hT : T2Space Y)
    (hm : Monotone (fun n ↦ (i (k n)).range)) (hF : ∀ a, IsFrechetTVS (X a))
    (he : ∀ n, IsEmbedding (i (k n))) (hc : ∀ y, ∃ n, y ∈ (i (k n)).range)
    (ht : (inferInstance : TopologicalSpace Y) = locallyConvexFinalTopology (fun n ↦ i (k n))) :
    IsStrictLFSpace Y :=
  ⟨hT, _, hm, fun n ↦ frechet_range_of_embedding _ (he n) (hF _), hc,
    ht.trans (finalTopology_range_stages _ he)⟩

/-- Paper: Theorem D.3.3.7(2), p. 806. The decay space is a strict LF-space. -/
theorem modulatedExponentialDecay_strictLF : IsStrictLFSpace E := by
  have hlim := modulatedExponentialDecay_stageLimit m I hm hτ.surjective hInt hne
  refine hlim.elim fun k hk ↦ ?_
  have hT : T2Space E := T2Space.of_injective_continuous (f := fun f : E ↦ f.val)
    (fun _ _ h ↦ Subtype.ext h) (continuous_pi (continuous_modulatedExponentialDecay_eval m I hne))
  exact strictLF_of_embedded_stages (Y := E) (X := ModulatedExponentialDecayStage m I)
    (fun a ↦ modulatedExponentialDecayStageInclusion m I a) k hT
    (decay_stage_ranges_mono m I hm hInt hne τ hτ k hk.1)
    (modulatedExponentialDecayStage_frechet m hm hτ.surjective I hInt hne) hk.2.2.1 hk.2.2.2.1 hk.2.2.2.2

/-- Paper: Theorem D.3.3.7(2), p. 806. The decay space is complete. -/
theorem modulatedExponentialDecay_complete : CompleteSpace E := by
  rw [← IsUniformAddGroup.rightUniformSpace_eq (G := E)]
  exact (modulatedExponentialDecay_strictLF m I hm hInt hne τ hτ).completeSpace

omit hSC hm hInt hne hτ in
/-- Nuclearity passes from embedded nuclear Fréchet stages to their locally convex limit. -/
private theorem nuclear_of_embedded_stages.{u,v} {Y : Type u} [AddCommGroup Y] [Module ℂ Y]
    [UniformSpace Y] [IsUniformAddGroup Y] [PolynormableSpace ℂ Y] [T2Space Y]
    {A : Type*} {X : A → Type u} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    [∀ a, UniformSpace (X a)] [∀ a, IsUniformAddGroup (X a)] [∀ a, PolynormableSpace ℂ (X a)]
    (i : ∀ a, X a →ₗ[ℂ] Y) (k : ℕ → A)
    (hm : Monotone (fun n ↦ (i (k n)).range)) (hF : ∀ a, IsFrechetTVS (X a))
    (hN : ∀ a, IsNuclearTVS.{v} (X a))
    (he : ∀ n, IsEmbedding (i (k n))) (hc : ∀ y, ∃ n, y ∈ (i (k n)).range)
    (ht : (inferInstance : TopologicalSpace Y) = locallyConvexFinalTopology (fun n ↦ i (k n))) :
    IsNuclearTVS.{v} Y := by
  refine isNuclearTVS_of_strictLF_stages _ hm (fun n ↦ frechet_range_of_embedding _ (he n) (hF _))
    (fun n ↦ ?_) hc (ht.trans (finalTopology_range_stages _ he))
  let e := LinearEquiv.ofInjective (i (k n)) (he n).injective
  have hi : IsInducing e := IsInducing.subtypeVal.of_comp_iff.mp (he n).isInducing
  exact isNuclearTVS_of_linearEmbedding e.symm.toLinearMap
    (e.toEquiv.toHomeomorphOfIsInducing hi).symm.isEmbedding (hN _)

/-- Paper: Theorem D.3.3.7(2), p. 806. The decay space is nuclear. -/
theorem modulatedExponentialDecay_nuclear : IsNuclearTVS E := by
  let : T2Space E := (modulatedExponentialDecay_strictLF m I hm hInt hne τ hτ).1
  refine (modulatedExponentialDecay_stageLimit m I hm hτ.surjective hInt hne).elim fun k hk ↦ ?_
  exact nuclear_of_embedded_stages (Y := E) (X := ModulatedExponentialDecayStage m I)
    (fun a ↦ modulatedExponentialDecayStageInclusion m I a) k
    (decay_stage_ranges_mono m I hm hInt hne τ hτ k hk.1)
    (modulatedExponentialDecayStage_frechet m hm hτ.surjective I hInt hne)
    (modulatedExponentialDecayStage_nuclear m hm hτ.surjective I hInt hne) hk.2.2.1 hk.2.2.2.1 hk.2.2.2.2

/-- Paper: Theorem D.3.3.7(2), p. 806. The decay space is Montel and barrelled. -/
theorem modulatedExponentialDecay_montel : BarrelledSpace ℂ E ∧ MontelSpace ℂ E := by
  have h := modulatedExponentialDecay_strictLF m I hm hInt hne τ hτ
  exact ⟨(lfSpace_quotient_properties.1 h).barrelled,
    montelSpace_of_nuclear_strictLF.{0} h (modulatedExponentialDecay_nuclear m I hm hInt hne τ hτ)⟩

omit hSC hm hInt hne hτ in
/-- A seminorm bounded on bounded sets of a first-countable space is continuous.
Apply the bounded linear map criterion to the identity into its seminormed copy. -/
private theorem continuous_seminorm_of_bounded_images {X : Type*} [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℂ X] [FirstCountableTopology X]
    (p : Seminorm ℂ X) (hp : ∀ B : Set X, IsVonNBounded ℂ B → BddAbove (p '' B)) : Continuous p := by
  let Y := ULift.{0} X
  let e : Y ≃ₗ[ℂ] X := ULift.moduleEquiv
  let q := p.comp e.toLinearMap
  let : SeminormedAddCommGroup Y := q.toAddGroupSeminorm.toSeminormedAddCommGroup
  let : TopologicalSpace Y := PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  let : NormedSpace ℂ Y := ⟨fun c x ↦ (map_smul_eq_mul q c x).le⟩
  have he : Continuous e.symm := e.symm.toLinearMap.continuous_of_locally_bounded fun B hB ↦ by
    obtain ⟨r, hr⟩ := hp B hB
    exact (NormedSpace.image_isVonNBounded_iff ℂ).mpr ⟨r, fun x hx ↦ hr (mem_image_of_mem p hx)⟩
  exact he.norm

omit hSC hm hInt hne hτ in
/-- Boundedness of a seminorm gives continuity on each metrizable stage and hence
on their locally convex final topology. -/
private theorem strictLF_bounded_seminorm_continuous {X : Type*} [AddCommGroup X] [Module ℂ X]
    [t : TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℂ X]
    (h : IsStrictLFSpace X) (p : Seminorm ℂ X)
    (hp : ∀ B : Set X, IsVonNBounded ℂ B → BddAbove (p '' B)) : Continuous p := by
  obtain ⟨_, S, _, hF, _, ht⟩ := h
  let tests := {q : Seminorm ℂ X // ∀ n, Continuous (q ∘ (S n).subtype)}
  have H : WithSeminorms (Subtype.val : tests → Seminorm ℂ X) := ⟨ht⟩
  refine H.continuous_seminorm (⟨p, fun n ↦ ?_⟩ : tests)
  let : MetrizableSpace (S n) := (hF n).choose_spec.2.1
  apply continuous_seminorm_of_bounded_images (p.comp (S n).subtype)
  intro B hB
  obtain ⟨r, hr⟩ := hp ((S n).subtypeL '' B) (hB.image (S n).subtypeL)
  exact ⟨r, fun z ⟨v, hv, he⟩ ↦ he ▸ hr (mem_image_of_mem p (mem_image_of_mem (S n).subtypeL hv))⟩

/-- Paper: Theorem D.3.3.7(2), p. 806. The decay space is bornological,
expressed by continuity of seminorms bounded on every bounded set. -/
theorem modulatedExponentialDecay_bornological :
    ∀ p : Seminorm ℂ E,
      (∀ B : Set E, IsVonNBounded ℂ B → BddAbove (p '' B)) → Continuous p := by
  exact strictLF_bounded_seminorm_continuous (modulatedExponentialDecay_strictLF m I hm hInt hne τ hτ)

omit hInt hne in
/-- The split kernel coordinate and the modulation together detect small cyclic subgroups. -/
private theorem locallyEuclidean_of_modulation_kernel (hK : IsCompactlyGeneratedGroup (PontryaginDual K)) :
    IsLocallyEuclidean G := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let W := (exists_nhds_one_of_isLocallyEuclidean
    (isLocallyEuclidean_of_isCompactlyGeneratedGroup_dual hK)).choose
  have hW := (exists_nhds_one_of_isLocallyEuclidean
    (isLocallyEuclidean_of_isCompactlyGeneratedGroup_dual hK)).choose_spec
  let line : EuclideanSpace ℝ (Fin 1) ≃L[ℝ] ℝ := PiLp.equivOfUnique 2 ℝ _
  let chart : EuclideanSpace ℝ (Fin 1) ≃ₜ ℝ≥0ˣ := line.toHomeomorph.trans positiveRealLogEquiv.symm.toHomeomorph
  have haxis : IsLocallyEuclidean ℝ≥0ˣ := ⟨1, ⟨chart.chartedSpace⟩⟩
  obtain ⟨V, hV, hpow⟩ := exists_nhds_one_of_isLocallyEuclidean haxis
  let r (x : G) : K := ⟨x / τ (m x), by change m (x / τ (m x)) = 1; rw [map_div, hτ, div_self']⟩
  have hr : Continuous r := (continuous_id.div' (τ.continuous.comp m.continuous)).subtype_mk _
  have hr1 : r 1 = 1 := Subtype.ext (by change (1 : G) / τ (m 1) = 1; rw [map_one, map_one, div_self'])
  have hrW : W ∈ 𝓝 (r 1) := hr1 ▸ hW.1
  have hmV : V ∈ 𝓝 (m 1) := by rw [map_one]; exact hV
  refine isLocallyEuclidean_of_noSmallCyclicSubgroups
    (Filter.inter_mem (hr.continuousAt.preimage_mem_nhds hrW) (m.continuous.continuousAt.preimage_mem_nhds hmV)) ?_
  intro x hx
  have hm1 : m x = 1 := hpow _ fun n ↦ map_pow m x n ▸ (hx n).2
  have hk : (⟨x, hm1⟩ : K) = 1 := hW.2 _ fun n ↦ by
    have he : r (x ^ n) = (⟨x, hm1⟩ : K) ^ n := Subtype.ext (by
      change x ^ n / τ (m (x ^ n)) = x ^ n
      simp [map_pow, hm1])
    exact he ▸ (hx n).1
  exact congrArg Subtype.val hk

/-- Paper: Theorem D.3.3.7(2), p. 806. The decay space is Fréchet when
the norm-one subgroup has compactly generated dual. -/
theorem modulatedExponentialDecay_frechet
    (hK : IsCompactlyGeneratedGroup (PontryaginDual K)) : IsFrechetTVS E := by
  have hg := isBruhatGoodSubgroup_bot_iff.mpr (locallyEuclidean_of_modulation_kernel m hm τ hτ hK)
  let k₀ : GoodCompact := ⟨⊥, isCompact_of_isBruhatGoodSubgroup_aux _ hg, hg.2.2⟩
  refine (modulatedExponentialDecay_stageLimit m I hm hτ.surjective hInt hne).elim fun stages hs ↦ ?_
  refine (hs.2.1 k₀).elim fun n hn ↦ ?_
  let X := ModulatedExponentialDecayStage m I (stages n)
  let i : X →ₗ[ℂ] E := modulatedExponentialDecayStageInclusion m I (stages n)
  have hsurj : Surjective i := fun f ↦ ((modulatedExponentialDecayStageInclusion_range m I (stages n)).2 f).mpr
    fun g u ↦ congrArg f.val (by rw [show (u : G) = 1 from hn u.property, mul_one])
  have he := hs.2.2.1 n
  let e : X ≃ₜ E := (Equiv.ofBijective i ⟨he.injective, hsurj⟩).toHomeomorphOfIsInducing he.isInducing
  let : MetrizableSpace X := (modulatedExponentialDecayStage_frechet m hm hτ.surjective I hInt hne
    (stages n)).choose_spec.2.1
  refine ⟨inferInstance, inferInstance, e.symm.isEmbedding.metrizableSpace, ?_⟩
  rw [IsUniformAddGroup.rightUniformSpace_eq]
  exact modulatedExponentialDecay_complete m I hm hInt hne τ hτ

omit hSC hm hInt hne hτ in
/-- Restriction embeds the strong dual of a strict LF-space as the closed space
of compatible functionals on its defining Fréchet subspaces. -/
private theorem strictLF_dual_closed_embedding {X : Type*} [AddCommGroup X] [Module ℂ X]
    [UniformSpace X] [IsUniformAddGroup X] [ContinuousSMul ℂ X] [PolynormableSpace ℂ X]
    (h : IsStrictLFSpace X) :
    ∃ S : ℕ → Submodule ℂ X, (∀ n, IsFrechetTVS (S n)) ∧
      IsClosedEmbedding (fun (L : StrongDual ℂ X) n ↦ L.comp (S n).subtypeL) := by
  obtain ⟨hT, S, hmono, hF, hex, ht⟩ := h
  let (n : ℕ) : UniformSpace (S n) := IsTopologicalAddGroup.rightUniformSpace (S n)
  let (n : ℕ) : IsUniformAddGroup (S n) := isUniformAddGroup_of_addCommGroup
  let j (n : ℕ) := (S n).subtypeL.codRestrict (S (n+1)) fun x ↦ hmono n.le_succ x.property
  let i (n : ℕ) := (S n).subtypeL
  have hlim : IsInjectiveLCLimit j i := by
    refine ⟨fun _ ↦ Subtype.val_injective, fun _ ↦ rfl, fun x ↦ ?_, ht⟩
    obtain ⟨n, hn⟩ := hex x
    exact ⟨n, ⟨x, hn⟩, rfl⟩
  have hj (n : ℕ) : IsClosedEmbedding (j n) := by
    have he := IsEmbedding.of_comp (j n).continuous (i (n+1)).continuous
      (show IsEmbedding (i (n+1) ∘ j n) from IsEmbedding.subtypeVal)
    have hu := AddMonoidHom.isUniformInducing_of_isInducing (f := (j n).toLinearMap.toAddMonoidHom)
      he.isInducing
    have hc : CompleteSpace (S n) := (hF n).choose_spec.2.2
    exact (show IsUniformEmbedding (j n) from ⟨hu, he.injective⟩).isClosedEmbedding
  have hd := dual_of_injectiveLCLimit hlim
  let R (L : StrongDual ℂ X) n := L.comp (i n)
  have hR : IsEmbedding R := hd.2.2 fun B hB ↦ by
    obtain ⟨k, A, hA, he⟩ := (isVonNBounded_iff_bounded_stage hlim hj B).mp hB
    exact ⟨k, A, hA, he.symm⟩
  refine ⟨S, hF, hR, ?_⟩
  let eqn (n : ℕ) := {l : (k : ℕ) → StrongDual ℂ (S k) | (l (n+1)).comp (j n) = l n}
  have heq : range R = ⋂ n, eqn n := by
    ext l
    simp only [mem_range, mem_iInter, eqn, mem_ofPred_eq]
    exact ⟨fun ⟨L, hL⟩ ↦ hL ▸ fun _ ↦ rfl, fun hl ↦
      ⟨(hd.1 l hl).exists.choose, funext (hd.1 l hl).exists.choose_spec⟩⟩
  rw [heq]
  exact isClosed_iInter fun n ↦ isClosed_eq
    ((ContinuousLinearMap.precomp ℂ (j n) : StrongDual ℂ (S (n+1)) →L[ℂ] StrongDual ℂ (S n)).continuous.comp (continuous_apply (n+1)))
    (continuous_apply n)
omit hSC hm hInt hne hτ in
/-- The closed compatible families form a complete subspace of the product of stage duals. -/
private theorem strictLF_dual_complete {X : Type*} [AddCommGroup X] [Module ℂ X]
    [UniformSpace X] [IsUniformAddGroup X] [ContinuousSMul ℂ X] [PolynormableSpace ℂ X]
    (h : IsStrictLFSpace X) : CompleteSpace (StrongDual ℂ X) := by
  obtain ⟨S, hF, he⟩ := strictLF_dual_closed_embedding h
  let (n : ℕ) : MetrizableSpace (S n) := (hF n).choose_spec.2.1
  let R : StrongDual ℂ X →L[ℂ] ((n : ℕ) → StrongDual ℂ (S n)) :=
    ContinuousLinearMap.pi fun n ↦ ContinuousLinearMap.precomp ℂ (S n).subtypeL
  exact (AddMonoidHom.isUniformInducing_of_isInducing (f := R.toLinearMap.toAddMonoidHom)
    he.isInducing).completeSpace he.isClosed_range.isComplete

/-- Paper: Theorem D.3.3.7(3), p. 807. The Hausdorff strong dual of the decay
space is complete. -/
theorem modulatedExponentialDecay_strongDual_complete :
    CompleteSpace (StrongDual ℂ E) := by
  exact strictLF_dual_complete (modulatedExponentialDecay_strictLF m I hm hInt hne τ hτ)

omit hSC hm hInt hne hτ in
/-- Restriction to the stages realizes the strong dual inside a product of nuclear duals. -/
private theorem strictLF_dual_nuclear.{u,v} {X : Type u} [AddCommGroup X] [Module ℂ X]
    [UniformSpace X] [IsUniformAddGroup X] [ContinuousSMul ℂ X] [PolynormableSpace ℂ X]
    (h : IsStrictLFSpace X) (hN : IsNuclearTVS.{v} X) : IsNuclearTVS.{v} (StrongDual ℂ X) := by
  obtain ⟨S, hF, he⟩ := strictLF_dual_closed_embedding h
  let : T2Space X := hN.1
  let D := StrongDual ℂ X
  let tests : Set (Set X) := {s | IsVonNBounded ℂ s}
  let : PolynormableSpace ℂ D :=
    uniformConvergenceCLM_polynormable (F := ℂ) tests (fun _ hs ↦ hs)
      (by rw [show ⋃₀ tests = univ from sUnion_isVonNBounded_eq_univ, Submodule.span_univ]; simp)
  let R : D →L[ℂ] ((n : ℕ) → StrongDual ℂ (S n)) :=
    ContinuousLinearMap.pi fun n ↦ ContinuousLinearMap.precomp ℂ (S n).subtypeL
  exact isNuclearTVS_of_linearEmbedding R.toLinearMap he.isEmbedding
    (isNuclearTVS_pi fun n ↦ (isNuclearTVS_strongDual_iff (hF n)).mpr (isNuclearTVS_submodule hN (S n)))

/-- Paper: Theorem D.3.3.7(3), p. 807. The strong dual is nuclear. -/
theorem modulatedExponentialDecay_strongDual_nuclear :
    IsNuclearTVS (StrongDual ℂ E) := by
  exact strictLF_dual_nuclear (modulatedExponentialDecay_strictLF m I hm hInt hne τ hτ)
    (modulatedExponentialDecay_nuclear m I hm hInt hne τ hτ)

omit hSC hm hInt hne hτ in
open scoped ComplexOrder in
/-- The polar of a closed dual seminorm ball is bounded, and bidual surjectivity
identifies its bipolar with the ball. Thus these balls are strong neighborhoods. -/
private theorem montel_strongDual_barrelled {X : Type*} [AddCommGroup X] [Module ℂ X] [UniformSpace X]
    [IsUniformAddGroup X] [ContinuousSMul ℂ X] [PolynormableSpace ℂ X] [T2Space X]
    [MontelSpace ℂ X] : BarrelledSpace ℂ (StrongDual ℂ X) := by
  let D := StrongDual ℂ X
  let S : Set (Set X) := {s | IsVonNBounded ℂ s}
  have hS : ⋃₀ S = (univ : Set X) := sUnion_isVonNBounded_eq_univ (𝕜 := ℂ) («E» := X)
  have hdense : Dense (Submodule.span ℂ (⋃₀ S) : Set X) := by
    rw [hS, Submodule.span_univ, Submodule.top_coe]
    exact dense_univ
  let : PolynormableSpace ℂ D :=
    uniformConvergenceCLM_polynormable («E» := X) (F := ℂ) S (fun _ hs ↦ hs) hdense
  refine ⟨fun p hp ↦ Seminorm.continuous' (r := 1) ?_⟩
  let U := p.closedBall 0 1
  let A := (topDualPairing ℂ X).polar U
  -- The polar of the absorbing unit ball is bounded under every functional on X.
  have hA : IsVonNBounded ℂ A := by
    apply (isVonNBounded_iff_dual_image («E» := X) A).mpr
    intro φ
    obtain ⟨c, hc⟩ := (p.absorbent_closedBall_zero one_pos φ).exists
    refine isBounded_iff_forall_norm_le.mpr ⟨‖c‖, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨ψ, hψ, hφ⟩ := hc (mem_singleton φ)
    rw [← hφ]
    change ‖(c • ψ) x‖ ≤ ‖c‖
    rw [smul_apply, norm_smul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hx ψ hψ)
  have hU : IsClosed U := by
    rw [show U = {φ | p φ ≤ 1} from p.closedBall_zero_eq]
    exact hp.isClosed_preimage 1
  let : Module ℝ D := Module.restrictScalars ℝ ℂ D
  let : IsScalarTower ℝ ℂ D := IsScalarTower.restrictScalars ℝ ℂ D
  have haU : AbsConvex ℂ U := ⟨p.balanced_closedBall_zero 1,
    convex_RCLike_iff_convex_real.mpr (p.convex_closedBall 0 1)⟩
  have hzU : 0 ∈ U := p.mem_closedBall_zero.mpr (by simp)
  -- A separating functional is evaluation at a point of A.
  filter_upwards [ContinuousLinearMap.eventually_nhds_zero_mapsTo (σ := RingHom.id ℂ) hA
    (Metric.ball_mem_nhds (0 : ℂ) one_pos)] with φ hφ
  by_contra hnot
  obtain ⟨l, hl, hlt⟩ := exists_dual_norm_le_one_lt_of_notMem hU haU hzU hnot
  obtain ⟨x, rfl⟩ := surjective_strongBidual_eval («E» := X) l
  have hx : x ∈ A := fun ψ hψ ↦ hl ψ hψ
  exact (not_lt_of_ge (mem_ball_zero_iff.mp (hφ hx)).le) hlt


/-- Paper: Theorem D.3.3.7(3), p. 807. The strong dual is Montel and barrelled. -/
theorem modulatedExponentialDecay_strongDual_montel :
    BarrelledSpace ℂ (StrongDual ℂ E) ∧ MontelSpace ℂ (StrongDual ℂ E) := by
  have H := modulatedExponentialDecay_montel m I hm hInt hne τ hτ
  let : BarrelledSpace ℂ E := H.1
  let : MontelSpace ℂ E := H.2
  let : T2Space E := (modulatedExponentialDecay_strictLF m I hm hInt hne τ hτ).1
  exact ⟨montel_strongDual_barrelled, montelSpace_strongDual⟩

omit hSC hm hInt hne hτ in
/-- A weighted coordinate is continuous on the final decay topology, since on each
stage it is the quotient twist followed by Schwartz–Bruhat pullback. -/
private theorem continuous_decay_twist (a : I) :
    Continuous (fun f : E ↦ modulatedExponentialDecayTwist m I a f) := by
  let L : E →ₗ[ℂ] SchwartzBruhat G := modulatedExponentialDecayTwist m I a
  let tests := {q : Seminorm ℂ (modulatedExponentialDecaySubmodule m I) //
    ∀ k : GoodCompact, Continuous (q ∘ modulatedExponentialDecayStageInclusion m I k)}
  have gen := withGeneratingSeminorms_spec (modulatedExponentialDecaySubmodule m I)
    (Subtype.val : tests → Seminorm ℂ (modulatedExponentialDecaySubmodule m I))
  refine (PolynormableSpace.withSeminorms ℂ (SchwartzBruhat G)).continuous_of_continuous_comp L
    fun p ↦ ?_
  let q : Seminorm ℂ E := p.val.comp L
  change Continuous q
  refine gen.continuous_seminorm (⟨q, fun k ↦ ?_⟩ : tests)
  let n := quotientModulation m k.val k.property.1
  have hP := continuous_schwartzBruhat_compactQuotient_pullback k.val k.property.1
  let j := hP.choose
  have hj := hP.choose_spec
  have ha : Continuous (fun f : ModulatedExponentialDecayStage m I k ↦
      modulatedExponentialDecayTwist n I a f) := (continuous_apply a).comp
        (modulatedExponentialDecayStage_twists_isInducing m I k).continuous
  refine (p.property.comp (j.continuous.comp ha)).congr fun f ↦ congrArg p.val ?_
  exact Subtype.ext (funext (hj (modulatedExponentialDecayTwist n I a f)))

omit hSC hm hInt hne hτ in
/-- Every weight is strictly positive, so a single weighted profile determines the function. -/
private theorem decay_twist_injective (a : I) :
    Injective (modulatedExponentialDecayTwist m I a) := by
  intro f g h
  refine Subtype.ext (funext fun x ↦ ?_)
  have hw := Real.rpow_pos_of_pos (NNReal.coe_pos.mpr (Units.zero_lt (m x))) (a : ℝ)
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hw.ne')
    (congrArg (fun F : SchwartzBruhat G ↦ F x) h)

/-- Paper: Theorem D.3.3.7(4), p. 807. If zero belongs to the interval,
the decay space includes continuously into the ordinary Schwartz–Bruhat space. -/
theorem modulatedExponentialDecay_continuous_inclusion (h0 : 0 ∈ I) :
    ∃ j : E →L[ℂ] SchwartzBruhat G, Injective j ∧ ∀ f g, j f g = f.val g := by
  let a : I := ⟨0, h0⟩
  refine ⟨⟨modulatedExponentialDecayTwist m I a, continuous_decay_twist m I a⟩,
    decay_twist_injective m I a, fun f g ↦ ?_⟩
  exact congrFun (modulationWeight_zero m f.val) g

/-- One bounded Schwartz–Bruhat coordinate supplies a common compact subgroup of
invariance. Normalized averaging then bounds the other coordinates on that quotient. -/
private theorem bounded_stage_of_twists (B : Set E)
    (hB : ∀ a : I, IsVonNBounded ℂ (modulatedExponentialDecayTwist m I a '' B)) :
    ∃ (k : GoodCompact) (C : Set (ModulatedExponentialDecayStage m I k)),
      IsVonNBounded ℂ C ∧ modulatedExponentialDecayStageInclusion m I k '' C = B := by
  let a : I := ⟨hne.choose, hne.choose_spec⟩
  let tw := modulatedExponentialDecayTwist m I
  have hs := schwartzBruhat_bounded_image_stage (hB a)
  obtain ⟨b, d, C, _, hC⟩ := hs
  let k₀ := OrderDual.ofDual b.val.2
  let k : GoodCompact := ⟨k₀, isCompact_of_isBruhatGoodSubgroup_aux k₀ b.property.2.2.1,
    b.property.2.2.1.2.2⟩
  have hd := schwartzBruhatStage_compactQuotient_descent b d
  let descend := hd.choose
  have hinv (f : E) (hf : f ∈ B) (g : G) (u : k.val) : f.val (g * u.val) = f.val g := by
    have hmem := mem_image_of_mem (tw a) hf
    change tw a f ∈ modulatedExponentialDecayTwist m I a '' B at hmem
    have hmem' := Eq.mpr (congrArg (fun S : Set (SchwartzBruhat G) ↦ tw a f ∈ S) hC) hmem
    obtain ⟨s, _, he⟩ := hmem'
    have heval (x : G) : descend s (x : G ⧸ k.val) = tw a f x :=
      (hd.choose_spec s x).trans (congrArg (fun v : SchwartzBruhat G ↦ v x) he)
    have hweight := (heval (g * u.val)).symm.trans
      ((congrArg (descend s).val (QuotientGroup.mk_mul_of_mem g u.property)).trans (heval g))
    have hmu : m u.val = 1 := compactSubgroup_le_modulation_ker m k.val k.property.1 u.property
    change ((((m (g * u.val)).val : ℝ) ^ a.val : ℝ) : ℂ) * f.val (g * u.val) =
      ((((m g).val : ℝ) ^ a.val : ℝ) : ℂ) * f.val g at hweight
    rw [map_mul, hmu, mul_one] at hweight
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr
      (Real.rpow_pos_of_pos (NNReal.coe_pos.mpr (Units.zero_lt (m g))) _).ne') hweight
  let i : ModulatedExponentialDecayStage m I k →ₗ[ℂ] E := modulatedExponentialDecayStageInclusion m I k
  let C' := i ⁻¹' B
  have hcover : i '' C' = B := image_preimage_eq_of_subset fun f hf ↦
    ((modulatedExponentialDecayStageInclusion_range m I k).2 f).mpr (hinv f hf)
  have havg := schwartzBruhat_compactQuotient_average k.val k.property.1
  let A := havg.choose
  let n := quotientModulation m k.val k.property.1
  have hmatch (v : ModulatedExponentialDecayStage m I k) (t : I) :
      A (tw t (i v)) = modulatedExponentialDecayTwist n I t v := by
    let V := modulatedExponentialDecayTwist n I t v
    have he (g : G) : tw t (i v) g = V (g : G ⧸ k.val) := rfl
    have hfix (g : G) (u : k.val) : tw t (i v) (g * u.val) = tw t (i v) g :=
      (he _).trans ((congrArg V.val (QuotientGroup.mk_mul_of_mem g u.property)).trans (he g).symm)
    refine Subtype.ext (funext fun x ↦ QuotientGroup.induction_on x fun g ↦ ?_)
    exact (havg.choose_spec _ hfix g).trans (he g)
  have hstage : IsVonNBounded ℂ C' := by
    apply (withGeneratingSeminorms_spec _ _).isVonNBounded_iff_seminorm_bounded.mpr
    rintro ⟨t, p⟩
    have hS := PolynormableSpace.withSeminorms ℂ (SchwartzBruhat (G ⧸ k.val))
    have hb := (hS.isVonNBounded_iff_seminorm_bounded.mp ((hB t).image A)) p
    obtain ⟨r, hr, hb⟩ := hb
    refine ⟨r, hr, fun v hv ↦ ?_⟩
    have hmem := mem_image_of_mem A (mem_image_of_mem (tw t) (show i v ∈ B from hv))
    exact (congrArg (fun z : SchwartzBruhat (G ⧸ k.val) ↦ p.val z < r)
      (hmatch v t)).mp (hb _ hmem)
  exact ⟨k, C', hstage, hcover⟩

/-- Paper: Theorem D.3.3.7(1), p. 806. A bounded family in the full decay
space is the image of a bounded family in one compact-subgroup stage. -/
theorem modulatedExponentialDecay_bounded_image_stage {B : Set E} (hB : IsVonNBounded ℂ B) :
    ∃ (k : GoodCompact) (C : Set (ModulatedExponentialDecayStage m I k)),
      IsVonNBounded ℂ C ∧ modulatedExponentialDecayStageInclusion m I k '' C = B := by
  apply bounded_stage_of_twists m I hm hInt hne τ hτ B
  exact fun a ↦ hB.image (⟨modulatedExponentialDecayTwist m I a, continuous_decay_twist m I a⟩ :
    E →L[ℂ] SchwartzBruhat G)

/-- Bounded stage inclusions carry bounded families back to the full decay space. -/
private theorem decay_bounded_of_twists (B : Set E)
    (hB : ∀ a : I, IsVonNBounded ℂ (modulatedExponentialDecayTwist m I a '' B)) :
    IsVonNBounded ℂ B := by
  refine (bounded_stage_of_twists m I hm hInt hne τ hτ B hB).elim fun k hk ↦ hk.elim fun C hC ↦ ?_
  let i : ModulatedExponentialDecayStage m I k →ₗ[ℂ] E := modulatedExponentialDecayStageInclusion m I k
  let j : ModulatedExponentialDecayStage m I k →L[ℂ] E := ⟨i,
    (withGeneratingSeminorms_spec _ _).continuous_of_continuous_comp i fun q ↦ q.property k⟩
  exact (congrArg (fun S : Set E ↦ IsVonNBounded ℂ S) hC.2).mp (hC.1.image j)

omit hSC hm hInt hne hτ in
open scoped ContDiff in
/-- Reconstruct a function from the sum of its endpoint profiles. Each intermediate
twist of the reconstruction is a bounded smooth function of the log modulation
times the unweighted input. -/
private theorem decay_endpoint_reconstruction (a b : I) (ha : ∀ c : I, a.val ≤ c.val)
    (hb : ∀ c : I, c.val ≤ b.val) :
    ∃ R : SchwartzBruhat G →ₗ[ℂ] E,
      (∀ c : I, ∃ M : SchwartzBruhat G →L[ℂ] SchwartzBruhat G, ∀ f,
        modulatedExponentialDecayTwist m I c (R f) = M f) ∧
      ∀ f : E, R (modulatedExponentialDecayTwist m I a f + modulatedExponentialDecayTwist m I b f) = f := by
  let w (c : I) (x : G) : ℂ := (((m x).val : ℝ) ^ c.val : ℝ)
  have hw (x : G) : w a x + w b x ≠ 0 := by
    have hp := NNReal.coe_pos.mpr (Units.zero_lt (m x))
    exact (Complex.ofReal_add _ _ ▸ Complex.ofReal_ne_zero.mpr
      (add_pos (Real.rpow_pos_of_pos hp _) (Real.rpow_pos_of_pos hp _)).ne')
  let L : SchwartzBruhat G →ₗ[ℂ] (G → ℂ) :=
    (LinearMap.mulLeft ℂ fun x : G ↦ (w a x + w b x)⁻¹).comp (schwartzBruhatSubmodule G).subtype
  have hs (f : SchwartzBruhat G) :
      modulationWeight m a (L f) + modulationWeight m b (L f) = f.val := by
    funext x
    change w a x * ((w a x + w b x)⁻¹ * f x) + w b x * ((w a x + w b x)⁻¹ * f x) = f x
    rw [← add_mul, mul_inv_cancel_left₀ (hw x)]
  have ht (c : I) : ∃ M : SchwartzBruhat G →L[ℂ] SchwartzBruhat G, ∀ f : SchwartzBruhat G,
      modulationWeight m c (L f) = (M f).val := by
    let φ (t : ℝ) : ℂ := ((Real.exp (-(c.val - a.val) * t) + Real.exp ((b.val - c.val) * t))⁻¹ : ℝ)
    have hφ : ContDiff ℝ ∞ φ ∧ ∀ j, ∃ C, ∀ t, ‖iteratedFDeriv ℝ j φ t‖ ≤ C :=
      twoSidedExpWeight_bounds_of_nonneg (sub_nonneg.mpr (ha c)) (sub_nonneg.mpr (hb c))
    have hM := logModulation_mul_schwartzBruhat_continuousLinear m hφ.1 hφ.2
    refine ⟨hM.choose, fun f ↦ funext fun x ↦ ?_⟩
    exact (congrFun (modulationWeight_between_eq m (L f) a c b) x).trans
      ((congrArg (fun s : G → ℂ ↦ φ (Real.log ((m x).val : ℝ)) * s x) (hs f)).trans (hM.choose_spec f x).symm)
  let R : SchwartzBruhat G →ₗ[ℂ] E := L.codRestrict (modulatedExponentialDecaySubmodule m I) fun f ↦
    (Submodule.mem_iInf _).mpr fun c ↦ Eq.mpr (congrArg (fun z : G → ℂ ↦ z ∈ schwartzBruhatSubmodule G)
      ((ht c).choose_spec f)) ((ht c).choose f).property
  refine ⟨R, fun c ↦ ⟨(ht c).choose, fun f ↦ Subtype.ext ((ht c).choose_spec f)⟩, fun f ↦ ?_⟩
  refine Subtype.ext (funext fun x ↦ ?_)
  change (w a x + w b x)⁻¹ * (w a x * f.val x + w b x * f.val x) = f.val x
  rw [← add_mul, inv_mul_cancel_left₀ (hw x)]
omit hSC hm hInt hne hτ in
private theorem continuous_linear_of_bornological {X Y : Type*} [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] [IsTopologicalAddGroup X] [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [PolynormableSpace ℂ Y]
    (h : ∀ p : Seminorm ℂ X, (∀ B : Set X, IsVonNBounded ℂ B → BddAbove (p '' B)) → Continuous p)
    (f : X →ₗ[ℂ] Y) (hf : ∀ B : Set X, IsVonNBounded ℂ B → IsVonNBounded ℂ (f '' B)) :
    Continuous f := by
  let ps := PolynormableSpace.withSeminorms ℂ Y
  refine ps.continuous_of_continuous_comp f fun p ↦ h (p.val.comp f) fun B hB ↦ ?_
  refine (ps.isVonNBounded_iff_seminorm_bddAbove.mp (hf B hB) p).elim fun r hr ↦ ?_
  exact ⟨r, fun z hz ↦ hz.elim fun x hx ↦
    (congrArg (fun t : ℝ ↦ t ≤ r) hx.2).mp (hr (mem_image_of_mem p.val (mem_image_of_mem f hx.1)))⟩

/-- Paper: Theorem D.3.3.7(4), p. 807. For a compact interval,
the topology is induced by the family of weighted Schwartz–Bruhat profiles. -/
theorem modulatedExponentialDecay_compact_projective_topology (hI : IsCompact I) :
    IsEmbedding (fun (f : E) (a : I) ↦ modulatedExponentialDecayTwist m I a f) := by
  let a : I := ⟨sInf I, (hI.isLeast_sInf hne).1⟩
  let b : I := ⟨sSup I, (hI.isGreatest_sSup hne).1⟩
  have h := decay_endpoint_reconstruction m I a b (fun c ↦ (hI.isLeast_sInf hne).2 c.property)
    (fun c ↦ (hI.isGreatest_sSup hne).2 c.property)
  refine h.elim fun R hR ↦ ?_
  have hbound (B : Set (SchwartzBruhat G)) (hb : IsVonNBounded ℂ B) : IsVonNBounded ℂ (R '' B) := by
    apply decay_bounded_of_twists m I hm hInt hne τ hτ
    intro c
    refine (hb.image (hR.1 c).choose).subset fun z hz ↦ ?_
    exact hz.elim fun y hy ↦ hy.1.elim fun f hf ↦
      ⟨f, hf.1, ((hR.1 c).choose_spec f).symm.trans
        ((congrArg (modulatedExponentialDecayTwist m I c) hf.2).trans hy.2)⟩
  have hcont : Continuous R := continuous_linear_of_bornological (X := SchwartzBruhat G) (Y := E)
    schwartzBruhat_bornological R hbound
  exact Function.LeftInverse.isEmbedding (f := fun z : I → SchwartzBruhat G ↦ R (z a + z b))
    hR.2 (hcont.comp ((continuous_apply a).add (continuous_apply b))) (continuous_pi (continuous_decay_twist m I))

omit hSC hm hInt hne hτ

/-- The ordinary split Schwartz product has logarithmic scalar coordinate. -/
private theorem split_schwartz_product {H : Type*} [CommGroup H] [TopologicalSpace H]
    [IsTopologicalGroup H] [T2Space H] [LocallyCompactSpace H] [SecondCountableTopology H]
    (d : H × ℝ≥0ˣ ≃ₜ* G) :
    ∃ M : InductiveTensor (SchwartzBruhat H) (SchwartzMap ℝ ℂ) →L[ℂ] SchwartzBruhat G,
      ∀ (h : SchwartzBruhat H) (f : SchwartzMap ℝ ℂ) (u : H) (t : ℝ≥0ˣ),
         M (h ⊗ₜ[ℂ] f) (d (u,t)) = h u * f (Real.log (t.val : ℝ)) := by
  let : PolynormableSpace ℂ (SchwartzMap ℝ ℂ) := (schwartz_withSeminorms ℂ ℝ ℂ).toPolynormableSpace
  let : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let : T2Space (SchwartzBruhat H) := schwartzBruhat_t2
  let : T2Space (SchwartzBruhat ℝ≥0ˣ) := schwartzBruhat_t2
  refine (schwartzBruhat_realCoordinate_equiv positiveRealLogEquiv).elim fun s hs ↦ ?_
  refine (schwartzBruhat_kernel_equiv (G := H) (H := ℝ≥0ˣ)).elim fun v hv ↦ ?_
  refine (schwartzBruhat_congr d).elim fun w hw ↦ ?_
  let A := InductiveTensor (SchwartzBruhat H) (SchwartzMap ℝ ℂ)
  let J := InductiveTensor (SchwartzBruhat H) (SchwartzBruhat ℝ≥0ˣ)
  let i := ContinuousLinearMap.id ℂ (SchwartzBruhat H)
  let L : A →L[ℂ] J := ⟨inductiveTensorMap i.toLinearMap s.toLinearMap,
    inductiveTensorMap_continuous i s.toContinuousLinearMap⟩
  let M := w.toContinuousLinearMap.comp (v.toContinuousLinearMap.comp
    ((Completion.toComplL : J →L[ℂ] Completion J).comp L))
  refine ⟨M, fun h f u t ↦ ?_⟩
  have hp := (hw _ (u,t)).trans (hv h (s f) u t)
  exact hp.trans (congrArg (h u * ·) ((hs f t).trans (congrArg f (positiveRealLogEquiv_apply t))))

include hSC hm hInt hne hτ in
/-- A map from a bornological space into a decay space is continuous if all its
weighted profiles are continuous. -/
private theorem continuous_decay_of_twisted_maps {X : Type*} [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] [IsTopologicalAddGroup X]
    (hX : ∀ p : Seminorm ℂ X, (∀ B : Set X, IsVonNBounded ℂ B → BddAbove (p '' B)) → Continuous p)
    (D : X →ₗ[ℂ] E)
    (hD : ∀ a : I, Continuous ((modulatedExponentialDecayTwist m I a).comp D)) :
    Continuous D := by
  refine continuous_linear_of_bornological (X := X) (Y := E) hX D fun B hB ↦ ?_
  refine decay_bounded_of_twists m I hm hInt hne τ hτ (D '' B) fun a ↦ ?_
  let L : X →L[ℂ] SchwartzBruhat G := ⟨(modulatedExponentialDecayTwist m I a).comp D, hD a⟩
  exact (congrArg (IsVonNBounded ℂ) (image_image (modulatedExponentialDecayTwist m I a) D B)).mpr
    (hB.image L)

/-- Separate continuity can be tested on the defining coordinates of the target.
When the target is complete, the resulting tensor map extends to the completion. -/
private theorem complete_inductiveTensor_of_coordinates {X Y Z V ι A B : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [PolynormableSpace ℂ X] [T2Space X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [PolynormableSpace ℂ Y] [T2Space Y]
    [AddCommGroup Z] [Module ℂ Z] [UniformSpace Z] [IsUniformAddGroup Z] [ContinuousSMul ℂ Z]
    [PolynormableSpace ℂ Z] [CompleteSpace Z] [T2Space Z]
    [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] [PolynormableSpace ℂ V] [T2Space V]
    (t : ι → Z →ₗ[ℂ] V)
    (hX : ∀ D : X →ₗ[ℂ] Z, (∀ a, Continuous ((t a).comp D)) → Continuous D)
    (hY : ∀ D : Y →ₗ[ℂ] Z, (∀ a, Continuous ((t a).comp D)) → Continuous D)
    (D : X →ₗ[ℂ] Y →ₗ[ℂ] Z) (W : ι → InductiveTensor X Y →L[ℂ] V)
    (he : ∀ a x y, t a (D x y) = W a (x ⊗ₜ[ℂ] y)) 
    (ev : Z → A → B → ℂ) (u : X → A → ℂ) (v : Y → B → ℂ)
    (hval : ∀ x y a b, ev (D x y) a b = u x a * v y b) :
    ∃ L : Completion (InductiveTensor X Y) →L[ℂ] Z, ∀ x y a b,
      ev (L (Completion.coe' (α := InductiveTensor X Y) (x ⊗ₜ[ℂ] y))) a b = u x a * v y b := by
  have hW (a : ι) := (continuous_inductiveTensor_iff («E» := X) (F := Y) (G := V)
    (W a).toLinearMap).mp (W a).continuous
  let F : InductiveTensor X Y →L[ℂ] Z := ⟨TensorProduct.lift D,
    (continuous_inductiveTensor_iff («E» := X) (F := Y) (G := Z) _).mpr
      ⟨fun x ↦ hY (D x) fun a ↦ ((hW a).1 x).congr fun y ↦ (he a x y).symm,
       fun y ↦ hX (D.flip y) fun a ↦ ((hW a).2 y).congr fun x ↦ (he a x y).symm⟩⟩
  exact ⟨F.fromCompletion, fun x y a b ↦
    (congrArg (fun z ↦ ev z a b) (F.fromCompletion_apply_coe (x ⊗ₜ[ℂ] y))).trans (hval x y a b)⟩

include hne hτ in
/-- Lift the ordinary products of all scalar twists to one bilinear map into the decay space. -/
private theorem decay_product_data [T2Space (SchwartzBruhat K)] [T2Space P]
    (d : K × ℝ≥0ˣ ≃ₜ* G) (hd : ∀ p, d p = (p.1 : G) * τ p.2)
    (M : InductiveTensor (SchwartzBruhat K) (SchwartzMap ℝ ℂ) →L[ℂ] SchwartzBruhat G)
    (hM : ∀ (h : SchwartzBruhat K) (f : SchwartzMap ℝ ℂ) (u : K) (t : ℝ≥0ˣ),
      M (h ⊗ₜ[ℂ] f) (d (u,t)) = h u * f (Real.log (t.val : ℝ))) :
    ∃ (D : SchwartzBruhat K →ₗ[ℂ] P →ₗ[ℂ] E) (W : I → T →L[ℂ] SchwartzBruhat G),
      (∀ (a : I) (h : SchwartzBruhat K) (f : P),
        modulatedExponentialDecayTwist m I a (D h f) = W a (h ⊗ₜ[ℂ] f)) ∧
      (∀ (h : SchwartzBruhat K) (f : P) (u : K) (t : ℝ≥0ˣ),
        (D h f).val ((u : G) * τ t) = h u * f.val (Real.log (t.val : ℝ))) := by
  let : PolynormableSpace ℂ (SchwartzMap ℝ ℂ) := (schwartz_withSeminorms ℂ ℝ ℂ).toPolynormableSpace
  let tw (a : I) : P →L[ℂ] SchwartzMap ℝ ℂ := ⟨logExponentialDecayTwist I a,
    (continuous_apply a).comp (positiveRealExponentialDecay_isEmbedding I hne).continuous⟩
  let i := ContinuousLinearMap.id ℂ (SchwartzBruhat K)
  let W (a : I) : T →L[ℂ] SchwartzBruhat G := M.comp
    ⟨inductiveTensorMap i.toLinearMap (tw a).toLinearMap, inductiveTensorMap_continuous i (tw a)⟩
  let w (a : I) (x : G) : ℂ := ((((m x).val : ℝ) ^ a.val : ℝ) : ℂ)
  have hcoord (a : I) (h : SchwartzBruhat K) (f : P) (u : K) (t : ℝ≥0ˣ) :
      W a (h ⊗ₜ[ℂ] f) (d (u,t)) = w a (d (u,t)) * (h u * f.val (Real.log (t.val : ℝ))) := by
    have hmt : m (d (u,t)) = t := (congrArg m (hd (u,t))).trans (by
      rw [map_mul, show m u.val = 1 from u.property, one_mul, hτ])
    have hWa : W a (h ⊗ₜ[ℂ] f) = M (h ⊗ₜ[ℂ] tw a f) :=
      congrArg M (inductiveTensorMap_tmul i (tw a) h f)
    refine (congrArg (fun z : SchwartzBruhat G ↦ z (d (u,t))) hWa).trans ((hM h (tw a f) u t).trans ?_)
    change h u * logExponentialDecayTwist I a f _ = _ * _
    dsimp only [w]
    rw [logExponentialDecayTwist_apply I a f (Real.log (t.val : ℝ)), hmt,
      identityWeight_log a.val t, positiveRealLogEquiv_apply t]
    exact mul_left_comm _ _ _
  let prod (h : SchwartzBruhat K) (f : P) (x : G) :=
    h (d.symm x).1 * f.val (Real.log ((d.symm x).2.val : ℝ))
  have hprod (h : SchwartzBruhat K) (f : P) (a : I) :
      modulationWeight m a (prod h f) = (W a (h ⊗ₜ[ℂ] f)).val := by
    funext x
    let q := d.symm x
    have hx : d (q.1, q.2) = x := d.apply_symm_apply x
    exact (congrArg (fun y : G ↦ w a y * prod h f x = (W a (h ⊗ₜ[ℂ] f)).val y) hx).mp
      (hcoord a h f q.1 q.2).symm
  let D₂ : SchwartzBruhat K →ₗ[ℂ] P →ₗ[ℂ] E := LinearMap.mk₂ ℂ
    (fun h f ↦ ⟨prod h f, (Submodule.mem_iInf _).mpr fun a ↦ Submodule.mem_comap.mpr
      ((congrArg (fun g : G → ℂ ↦ g ∈ schwartzBruhatSubmodule G) (hprod h f a)).mpr
        (W a (h ⊗ₜ[ℂ] f)).property)⟩)
    (fun h k f ↦ Subtype.ext (funext fun x ↦ add_mul _ _ _))
    (fun c h f ↦ Subtype.ext (funext fun x ↦ mul_assoc _ _ _))
    (fun h f g ↦ Subtype.ext (funext fun x ↦ mul_add _ _ _))
    (fun c h f ↦ Subtype.ext (funext fun x ↦ mul_left_comm _ _ _))
  have hD (a : I) (h : SchwartzBruhat K) (f : P) :
      modulatedExponentialDecayTwist m I a (D₂ h f) = W a (h ⊗ₜ[ℂ] f) :=
    Subtype.ext (hprod h f a)
  have hval (h : SchwartzBruhat K) (f : P) (u : K) (t : ℝ≥0ˣ) :
      (D₂ h f).val ((u : G) * τ t) = h u * f.val (Real.log (t.val : ℝ)) := by
    have hy : d.symm ((u : G) * τ t) = (u,t) :=
      (congrArg d.symm (hd (u,t)).symm).trans (d.symm_apply_apply _)
    exact congrArg (fun q : K × ℝ≥0ˣ ↦ h q.1 * f.val (Real.log (q.2.val : ℝ))) hy
  exact ⟨D₂, W, hD, hval⟩

include hSC hm hInt hne hτ in
/-- Complete the separately continuous product after testing its slices by all twists. -/
private theorem finish_split_product (D : SchwartzBruhat K →ₗ[ℂ] P →ₗ[ℂ] E)
    (W : I → T →L[ℂ] SchwartzBruhat G)
    (hw : (∀ (a : I) (h : SchwartzBruhat K) (f : P),
        modulatedExponentialDecayTwist m I a (D h f) = W a (h ⊗ₜ[ℂ] f)) ∧
      (∀ (h : SchwartzBruhat K) (f : P) (u : K) (t : ℝ≥0ˣ),
        (D h f).val ((u : G) * τ t) = h u * f.val (Real.log (t.val : ℝ)))) :
    ∃ L : Completion T →L[ℂ] E,
      ∀ (h : SchwartzBruhat K) (f : P) (u : K) (t : ℝ≥0ˣ),
        (L (Completion.coe' (α := T) (h ⊗ₜ[ℂ] f))).val ((u : G) * τ t) =
          h u * f.val (Real.log (t.val : ℝ)) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let : SecondCountableTopology K := TopologicalSpace.Subtype.secondCountableTopology (K : Set G)
  let : T2Space (SchwartzBruhat K) := schwartzBruhat_t2
  let : T2Space (SchwartzBruhat G) := schwartzBruhat_t2
  let : MetrizableSpace P := (positiveRealExponentialDecay_frechet I hInt hne).choose_spec.2.1
  let : T2Space E := (modulatedExponentialDecay_strictLF m I hm hInt hne τ hτ).1
  let : CompleteSpace E := modulatedExponentialDecay_complete m I hm hInt hne τ hτ
  let t (a : I) : E →ₗ[ℂ] SchwartzBruhat G := modulatedExponentialDecayTwist m I a
  have hX (D : SchwartzBruhat K →ₗ[ℂ] E) : (∀ a, Continuous ((t a).comp D)) → Continuous D :=
    continuous_decay_of_twisted_maps (X := SchwartzBruhat K) m I hm hInt hne τ hτ
      (schwartzBruhat_bornological (G := K)) D
  have hY (D : P →ₗ[ℂ] E) : (∀ a, Continuous ((t a).comp D)) → Continuous D :=
    continuous_decay_of_twisted_maps (X := P) m I hm hInt hne τ hτ
      (fun p ↦ continuous_seminorm_of_bounded_images (X := P) p) D
  let value (b : E) (u : K) (t : ℝ≥0ˣ) := b.val (u.val * τ t)
  let kernel (h : SchwartzBruhat K) (u : K) := h u
  let profile (f : P) (t : ℝ≥0ˣ) := f.val (Real.log (t.val : ℝ))
  with_reducible_and_instances
    exact complete_inductiveTensor_of_coordinates (X := SchwartzBruhat K) (Y := P) (Z := E)
      (V := SchwartzBruhat G) (A := K) (B := ℝ≥0ˣ) t hX hY D W hw.1
      value kernel profile hw.2

include hSC hm hInt hne hτ in
/-- Paper: Theorem D.3.3.7(1), p. 806. Multiplication in split coordinates
extends to a continuous linear map from the completed inductive tensor product
to the decay space. -/
private theorem modulatedExponentialDecay_completedTensor_mul :
    ∃ L : Completion T →L[ℂ] E,
      ∀ (h : SchwartzBruhat K) (f : P) (u : K) (t : ℝ≥0ˣ),
        (L (Completion.coe' (α := T) (h ⊗ₜ[ℂ] f))).val ((u : G) * τ t) =
          h u * f.val (Real.log (t.val : ℝ)) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let : SecondCountableTopology K := TopologicalSpace.Subtype.secondCountableTopology (K : Set G)
  let : T2Space (SchwartzBruhat K) := schwartzBruhat_t2
  let : T2Space P := (positiveRealExponentialDecay_isEmbedding I hne).t2Space
  refine (hm.exists_sectionEquiv τ hτ).elim fun d hd ↦ ?_
  refine (split_schwartz_product d).elim fun M hM ↦ ?_
  refine (decay_product_data m I hne τ hτ d hd M hM).elim fun D h ↦ h.elim fun W hW ↦ ?_
  with_reducible_and_instances
    exact finish_split_product m I hm hInt hne τ hτ D W hW

/-- The Schwartz kernel theorem transported to the coordinates of a splitting. -/
private theorem split_schwartz_kernel {H Q : Type*}
    [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    [LocallyCompactSpace H] [SecondCountableTopology H]
    [CommGroup Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [T2Space Q]
    [LocallyCompactSpace Q] [SecondCountableTopology Q] (d : H × Q ≃ₜ* G) :
    ∃ e : Completion (InductiveTensor (SchwartzBruhat H) (SchwartzBruhat Q)) ≃L[ℂ] SchwartzBruhat G,
      ∀ (h : SchwartzBruhat H) (f : SchwartzBruhat Q) (u : H) (t : Q),
        e (Completion.coe' (α := InductiveTensor (SchwartzBruhat H) (SchwartzBruhat Q))
          (h ⊗ₜ[ℂ] f)) (d (u,t)) = h u * f t := by
  refine (schwartzBruhat_kernel_equiv (G := H) (H := Q)).elim fun v hv ↦ ?_
  refine (schwartzBruhat_congr d).elim fun w hw ↦ ?_
  refine ⟨v.trans w, fun h f u t ↦ ?_⟩
  change w (v _) (d (u,t)) = _
  with_reducible_and_instances exact (hw _ (u,t)).trans (hv h f u t)

/-- To test density in an induced product topology, finitely many coordinates
can be reconstructed from a single dense image. -/
private theorem dense_of_finite_coordinates {X Y Z ι : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (t : X → ι → Y) (ht : IsInducing t) (M : Set X)
    (h : ∀ s : Finset ι, ∃ J : X → Z, Dense (J '' M) ∧
      ∀ i ∈ s, ∃ R : Z → Y, Continuous R ∧ ∀ x, R (J x) = t x i) :
    Dense M := by
  rw [dense_iff_inter_open]
  intro O hO hne
  obtain ⟨U, hU, rfl⟩ := ht.isOpen_iff.mp hO
  obtain ⟨x, hx⟩ := hne
  obtain ⟨s, V, hV, hs⟩ := isOpen_pi_iff.mp hU (t x) hx
  obtain ⟨J, hJ, hR⟩ := h s
  choose R hRc hRt using fun i : s ↦ hR i.val i.property
  let W := ⋂ i : s, R i ⁻¹' V i.val
  have hW : IsOpen W := isOpen_iInter_of_finite fun i ↦ (hV _ i.property).1.preimage (hRc i)
  have hxW : J x ∈ W := mem_iInter.mpr fun i ↦ (congrArg (· ∈ V i.val) (hRt i x)).mpr (hV _ i.property).2
  obtain ⟨y, hyW, z, hz, hyz⟩ := hJ.inter_open_nonempty W hW ⟨_, hxW⟩
  refine ⟨z, hs (fun i hi ↦ ?_), hz⟩
  have hy := mem_iInter.mp hyW (⟨i,hi⟩ : s)
  exact (congrArg (· ∈ V i) (hRt ⟨i,hi⟩ z)).mp ((congrArg (fun v ↦ R ⟨i,hi⟩ v ∈ V i) hyz).mpr hy)

/-- A closed subspace containing the images of pure tensors from a dense subset
of the right factor contains the full image of a completed tensor equivalence. -/
private theorem dense_of_split_products {X Y Z : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
    [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z] [IsTopologicalAddGroup Z] [ContinuousConstSMul ℂ Z]
    (e : Completion (InductiveTensor X Y) ≃L[ℂ] Z) (S : Submodule ℂ Z) {D : Set Y} (hd : Dense D)
    (hp : ∀ x y, y ∈ D → e (Completion.coe' (α := InductiveTensor X Y) (x ⊗ₜ[ℂ] y)) ∈ S) :
    Dense (S : Set Z) := by
  let Ts := InductiveTensor X Y
  let L := e.toContinuousLinearMap.comp (Completion.toComplL : Ts →L[ℂ] Completion Ts)
  let C := S.topologicalClosure
  have hC : IsClosed (C : Set Z) := S.isClosed_topologicalClosure
  have hA (x : X) (y : Y) : L (x ⊗ₜ[ℂ] y) ∈ C := by
    let ps := fun p : {p : Seminorm ℂ (X ⊗[ℂ] Y) //
      (∀ x : X, Continuous (fun y : Y ↦ p (x ⊗ₜ[ℂ] y))) ∧
      (∀ y : Y, Continuous (fun x : X ↦ p (x ⊗ₜ[ℂ] y)))} ↦ p.val
    have hc : @Continuous Y Ts _ _ (fun b ↦ x ⊗ₜ[ℂ] b) :=
      (withGeneratingSeminorms_spec _ ps).continuous_of_continuous_comp (TensorProduct.mk ℂ X Y x)
        fun p ↦ p.property.1 x
    exact closure_minimal (t := {b : Y | L (x ⊗ₜ[ℂ] b) ∈ C})
      (fun b hb ↦ S.le_topologicalClosure (hp x b hb)) (hC.preimage (L.continuous.comp hc)) (hd y)
  have hL (z : Ts) : L z ∈ C := TensorProduct.inductionOn (motive := fun a ↦ L a ∈ C) z hA
    (fun _ _ hx hy ↦ (C.comap L.toLinearMap).add_mem hx hy)
  intro z
  exact e.surjective z |>.elim fun w hw ↦ (congrArg (fun v ↦ v ∈ C) hw).mp
    (Completion.induction_on (p := fun v ↦ e v ∈ C) w (hC.preimage e.continuous) hL)

open scoped ContDiff in
/-- A compactly supported scalar Schwartz function is the sum of the two
given twists of a single compactly supported smooth decay profile. -/
private theorem compact_profile_sum_twists (a b : ℝ) (f : SchwartzMap ℝ ℂ)
    (hf : HasCompactSupport (f : ℝ → ℂ)) :
    ∃ g : P, ∀ x : ℝ, (Real.exp (a*x) + Real.exp (b*x) : ℝ) * g.val x = f x := by
  let w (x : ℝ) : ℂ := ((Real.exp (a*x) + Real.exp (b*x) : ℝ) : ℂ)
  have hw (x : ℝ) : w x ≠ 0 := Complex.ofReal_ne_zero.mpr (add_pos (Real.exp_pos _) (Real.exp_pos _)).ne'
  have hs : ContDiff ℝ ∞ w := Complex.ofRealCLM.contDiff.comp
    ((Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).add
      (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)))
  let g (x : ℝ) := (w x)⁻¹ * f x
  have hg : g ∈ logExponentialDecaySubmodule I :=
    mem_logExponentialDecaySubmodule_of_hasCompactSupport I (hf.mul_left) ((hs.inv hw).mul (f.smooth ⊤))
  exact ⟨⟨g, hg⟩, fun x ↦ mul_inv_cancel_left₀ (hw x) (f x)⟩

/-- An intermediate twist factors continuously through the sum of the endpoint twists. -/
private theorem decay_coordinate_of_sum (a b c : I) (ha : a ≤ c) (hb : c ≤ b) :
    ∃ M : SchwartzBruhat G →L[ℂ] SchwartzBruhat G, ∀ f : modulatedExponentialDecaySubmodule m I,
      M (modulatedExponentialDecayTwist m I a f + modulatedExponentialDecayTwist m I b f) =
        modulatedExponentialDecayTwist m I c f := by
  let φ (t : ℝ) : ℂ := ((Real.exp (-(c.val - a.val) * t) + Real.exp ((b.val - c.val) * t))⁻¹ : ℝ)
  have hφ := twoSidedExpWeight_bounds_of_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)
  refine (logModulation_mul_schwartzBruhat_continuousLinear (φ := φ) m hφ.1 hφ.2).elim fun M hM ↦ ?_
  refine ⟨M, fun f ↦ Subtype.ext (funext fun x ↦ ?_)⟩
  exact (hM _ x).trans (congrFun (modulationWeight_between_eq m f.val a c b) x).symm

/-- On split coordinates, the sum of two twists of a pure function is the
ordinary product with the sum of the two weighted scalar profiles. -/
private theorem decay_sum_on_product {H : Type*} (d : H × ℝ≥0ˣ → G)
    (hd : ∀ u t, m (d (u,t)) = t) (a b : I)
    (x : modulatedExponentialDecaySubmodule m I) (h : H → ℂ) (g : P) (f : SchwartzMap ℝ ℂ)
    (hx : ∀ u (t : ℝ≥0ˣ), x.val (d (u,t)) = h u * g.val (Real.log (t.val : ℝ)))
    (hg : ∀ y : ℝ, ((Real.exp (a.val*y) + Real.exp (b.val*y) : ℝ) : ℂ) * g.val y = f y)
    (u : H) (t : ℝ≥0ˣ) :
    (modulatedExponentialDecayTwist m I a x + modulatedExponentialDecayTwist m I b x).val (d (u,t)) =
      h u * f (Real.log (t.val : ℝ)) := by
  change _ * x.val _ + _ * x.val _ = _
  rw [← add_mul]
  dsimp only
  rw [hd u t, hx u t, identityWeight_log a.val t, identityWeight_log b.val t,
    positiveRealLogEquiv_apply t, mul_left_comm, ← Complex.ofReal_add, hg]

include hne in
/-- On a quotient stage, approximate finitely many twists simultaneously using compactly
supported scalar factors and the sum of the two extreme weights. -/
private theorem dense_decay_stage_of_products {H : Type*} [CommGroup H] [TopologicalSpace H]
    [IsTopologicalGroup H] [T2Space H] [LocallyCompactSpace H] [SecondCountableTopology H]
    (k : GoodCompact) [IsClosed (k.val : Set G)] (d : H × ℝ≥0ˣ ≃ₜ* (G ⧸ k.val))
    (hd : ∀ u t, quotientModulation m k.val k.property.1 (d (u,t)) = t)
    (S : Submodule ℂ (ModulatedExponentialDecayStage m I k))
    (hS : ∀ (h : SchwartzBruhat H) (g : P), ∃ z ∈ S, ∀ (u : H) (t : ℝ≥0ˣ),
      z.val (d (u,t)) = h u * g.val (Real.log (t.val : ℝ))) : Dense (S : Set (ModulatedExponentialDecayStage m I k)) := by
  classical
  let Q := G ⧸ k.val
  let n := quotientModulation m k.val k.property.1
  let A := ModulatedExponentialDecayStage m I k
  let Y := SchwartzBruhat Q
  let : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  refine (split_schwartz_kernel d).elim fun e he ↦ ?_
  refine (schwartzBruhat_realCoordinate_equiv positiveRealLogEquiv).elim fun v hv ↦ ?_
  let tw (a : I) : A →ₗ[ℂ] Y := modulatedExponentialDecayTwist n I a
  refine dense_of_finite_coordinates (Z := Y) (fun x a ↦ tw a x)
    (modulatedExponentialDecayStage_twists_isInducing m I k) (S : Set A) fun F ↦ ?_
  let c₀ : I := ⟨hne.some, hne.some_mem⟩
  let U := insert c₀ F
  have hU : U.Nonempty := Finset.insert_nonempty c₀ F
  let a := U.min' hU
  let b := U.max' hU
  let J := tw a + tw b
  refine ⟨J, ?_, fun c hc ↦ ?_⟩
  · let D := {f : SchwartzMap ℝ ℂ | HasCompactSupport (f : ℝ → ℂ)}
    have hD : Dense (v '' D) := v.surjective.denseRange.dense_image v.continuous SchwartzMap.dense_hasCompactSupport
    refine dense_of_split_products e (S.map J) hD fun h q hq ↦ ?_
    refine hq.elim fun f hf ↦ ?_
    refine (compact_profile_sum_twists I a b f hf.1).elim fun g hg ↦ ?_
    refine (hS h g).elim fun z hz ↦ ?_
    refine ⟨z, hz.1, Subtype.ext (funext fun y ↦ ?_)⟩
    let p := d.symm y
    have hyp := d.apply_symm_apply y
    let L := e (Completion.coe' (α := InductiveTensor (SchwartzBruhat H) (SchwartzBruhat ℝ≥0ˣ)) (h ⊗ₜ[ℂ] q))
    refine (congrArg (fun y : Q ↦ (J z).val y = L y) hyp).mp ?_
    refine (decay_sum_on_product n I d hd a b z (fun u ↦ h u) g f hz.2 hg p.1 p.2).trans ?_
    have hr : q p.2 = f (Real.log (p.2.val : ℝ)) :=
      (congrArg (fun w : SchwartzBruhat ℝ≥0ˣ ↦ w p.2) hf.2.symm).trans
        ((hv f p.2).trans (congrArg f (positiveRealLogEquiv_apply p.2)))
    exact (congrArg (h p.1 * ·) hr.symm).trans (he h q p.1 p.2).symm
  · have hc' : c ∈ U := Finset.mem_insert_of_mem hc
    exact (decay_coordinate_of_sum n I a b c (U.min'_le c hc') (U.le_max' c hc')).elim
      fun M hM ↦ ⟨M, M.continuous, hM⟩

/-- The kernel of the quotient modulation is the quotient of the original kernel. -/
private theorem decay_quotient_kernel_equiv (k : GoodCompact) [CompactSpace K]
    [IsClosed (k.val : Set G)] :
    let n := quotientModulation m k.val k.property.1
    let k₁ := k.val.comap (Subgroup.subtype K)
    ∃ d : (K ⧸ k₁) ≃ₜ* n.toMonoidHom.ker,
      ∀ u : K, ((d (u : K ⧸ k₁)) : G ⧸ k.val) = ((u : G) : G ⧸ k.val) := by
  let n := quotientModulation m k.val k.property.1
  let k₁ := k.val.comap (Subgroup.subtype K)
  let g : K →* G ⧸ k.val := (QuotientGroup.mk' k.val).comp (Subgroup.subtype K)
  let f := g.codRestrict n.toMonoidHom.ker (fun u ↦ u.property)
  have hker : k₁ = f.ker := by
    ext u
    have he := QuotientGroup.eq_one_iff (N := k.val) (u : G)
    exact ⟨fun h ↦ Subtype.ext (he.mpr h), fun h ↦ he.mp (congrArg Subtype.val (show f u = 1 from h))⟩
  let v := QuotientGroup.lift k₁ f hker.le
  have hinj : Injective v := (QuotientGroup.injective_lift_iff _ _ _).mpr hker
  have hsurj : Surjective v := by
    intro z
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective z.val
    have hu : x ∈ K := (congrArg n hx).trans z.property
    exact ⟨((⟨x, hu⟩ : K) : K ⧸ k₁), Subtype.ext hx⟩
  let e := MulEquiv.ofBijective v ⟨hinj, hsurj⟩
  have hc : Continuous e := (QuotientGroup.isQuotientMap_mk k₁).continuous_iff.mpr
    ((QuotientGroup.continuous_mk.comp continuous_subtype_val).subtype_mk _)
  let d : (K ⧸ k₁) ≃ₜ* n.toMonoidHom.ker := { e with
    continuous_toFun := hc
    continuous_invFun := (hc.homeoOfEquivCompactToT2 (f := e.toEquiv)).continuous_symm }
  exact ⟨d, fun _ ↦ rfl⟩

/-- A split evaluation determines the original function. -/
private theorem split_decay_eval_injective (d : K × ℝ≥0ˣ ≃ₜ* G)
    (hd : ∀ p : K × ℝ≥0ˣ, d p = p.1.val * τ p.2) :
    Injective (fun (v : E) (u : K) (t : ℝ≥0ˣ) ↦ v.val (u.val * τ t)) := by
  intro f g h
  apply Subtype.ext
  funext x
  obtain ⟨p, hp⟩ := d.surjective x
  have hpt := (hd p).symm.trans hp
  exact (congrArg (fun y ↦ f.val y = g.val y) hpt).mp (congrFun (congrFun h p.1) p.2)

/-- Pulling back a pure product in split coordinates puts its stage
realization in any subspace containing all global pure products. -/
private theorem stage_product_preimage {A B X Y V H κ σ : Type*}
    (i : A → B) (e : B → κ → σ → ℂ) (he : Injective e) (v : A → H → σ → ℂ)
    (r : κ → H) (hi : ∀ a k t, e (i a) k t = v a (r k) t)
    (g : X → H → ℂ) (h : Y → κ → ℂ) (f : V → σ → ℂ)
    (j : X → Y) (hj : ∀ x k, h (j x) k = g x (r k))
    (S : Set B) (hS : ∀ y w, ∃ b ∈ S, ∀ k t, e b k t = h y k * f w t)
    (hA : ∀ x w, ∃ a, ∀ u t, v a u t = g x u * f w t) :
    ∀ x w, ∃ a ∈ i ⁻¹' S, ∀ u t, v a u t = g x u * f w t := by
  intro x w
  obtain ⟨a, ha⟩ := hA x w
  obtain ⟨b, hb, hval⟩ := hS (j x) w
  have hab : i a = b := he (funext fun k ↦ funext fun t ↦ (hi a k t).trans
    ((ha (r k) t).trans ((congrArg (· * f w t) (hj x k).symm).trans (hval k t).symm)))
  exact ⟨a, (congrArg (· ∈ S) hab).mpr hb, ha⟩

private theorem stage_subspace_contains {X Y : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] (i : X →ₗ[ℂ] Y)
    (S : Submodule ℂ Y) (hs : IsClosed (S : Set Y)) (hi : Continuous i)
    (hD : Dense ((S.comap i : Submodule ℂ X) : Set X)) : ∀ z, i z ∈ S :=
  fun z ↦ (hs.preimage hi).closure_eq.le (hD z)

include hSC hm hInt hne hτ in
/-- Each split pure product defines a decay function on the entire interval. -/
private theorem split_pure_decay_mem (h : SchwartzBruhat K) (f : P) :
    ∃ z : E, ∀ (u : K) (t : ℝ≥0ˣ), z.val (u.val * τ t) = h u * f.val (Real.log (t.val : ℝ)) := by
  refine (modulatedExponentialDecay_completedTensor_mul m I hm hInt hne τ hτ).elim fun M hM ↦ ?_
  exact ⟨M (Completion.coe' (α := T) (h ⊗ₜ[ℂ] f)), hM h f⟩

include hSC in
/-- A Schwartz test function on the quotient kernel pulls back to the original kernel. -/
private theorem pull_quotient_kernel_test (k : GoodCompact) [CompactSpace K]
    [IsClosed (k.val : Set G)] [CompactSpace (quotientModulation m k.val k.property.1).toMonoidHom.ker] :
    let n := quotientModulation m k.val k.property.1
    ∃ j : SchwartzBruhat n.toMonoidHom.ker → SchwartzBruhat K, ∀ h u,
      j h u = h ⟨((u.val : G) : G ⧸ k.val), u.property⟩ := by
  let K₁ := k.val.comap (Subgroup.subtype K)
  let n := quotientModulation m k.val k.property.1
  let : IsClosed (K₁ : Set K) := k.property.1.isClosed.preimage continuous_subtype_val
  let : SecondCountableTopology K := TopologicalSpace.Subtype.secondCountableTopology (K : Set G)
  let : SecondCountableTopology (K ⧸ K₁) := QuotientGroup.isOpenQuotientMap_mk.secondCountableTopology
  let : SecondCountableTopology (G ⧸ k.val) := QuotientGroup.isOpenQuotientMap_mk.secondCountableTopology
  let : SecondCountableTopology n.toMonoidHom.ker := TopologicalSpace.Subtype.secondCountableTopology _
  refine (decay_quotient_kernel_equiv m k).elim fun r hr ↦ ?_
  refine (schwartzBruhat_congr r.symm).elim fun U hU ↦ ?_
  have hk₁ : IsCompact (K₁ : Set K) := IsClosed.isCompact (s := (K₁ : Set K)) inferInstance
  refine (continuous_schwartzBruhat_compactQuotient_pullback K₁ hk₁).elim fun J hJ ↦ ?_
  refine ⟨fun h ↦ J (U h), fun h u ↦ ?_⟩
  let x := (u : K ⧸ K₁)
  have hx : r x = (⟨((u.val : G) : G ⧸ k.val), u.property⟩ : n.toMonoidHom.ker) := Subtype.ext (hr u)
  exact (hJ (U h) u).trans ((congrArg (U h).val (r.symm_apply_apply x).symm).trans
    ((hU h (r x)).trans (congrArg h hx)))

include hSC hm hInt hne hτ in
/-- Quotient pure products pull back into any subspace containing the global split products. -/
private theorem split_products_on_quotient (k : GoodCompact) (S : Submodule ℂ E)
    (hS : ∀ (h : SchwartzBruhat K) (f : P), ∃ b ∈ S, ∀ (u : K) (t : ℝ≥0ˣ),
      b.val (u.val * τ t) = h u * f.val (Real.log (t.val : ℝ))) :
  let n := quotientModulation m k.val k.property.1
  ∃ (d : n.toMonoidHom.ker × ℝ≥0ˣ ≃ₜ* (G ⧸ k.val)),
    (∀ u t, n (d (u,t)) = t) ∧
    ∀ (x : SchwartzBruhat n.toMonoidHom.ker) (w : P),
      ∃ z : ModulatedExponentialDecayStage m I k, modulatedExponentialDecayStageInclusion m I k z ∈ S ∧
        ∀ u t, z.val (d (u,t)) = x u * w.val (Real.log (t.val : ℝ)) := by
  let K₁ := k.val.comap (Subgroup.subtype K)
  let Q := G ⧸ k.val
  let n := quotientModulation m k.val k.property.1
  let q : G →ₜ* Q := ⟨QuotientGroup.mk' k.val, QuotientGroup.continuous_mk⟩
  let s := q.comp τ
  have hs : RightInverse s n := hτ
  have hn : IsModulation n := ⟨isProperMap_of_comp_of_surj q.continuous n.continuous hm.1
    (QuotientGroup.mk'_surjective k.val), hm.2.elim fun g hg ↦ ⟨q g, hg⟩⟩
  let : IsClosed (k.val : Set G) := k.property.1.isClosed
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let : IsClosed (K₁ : Set K) := k.property.1.isClosed.preimage continuous_subtype_val
  let : SecondCountableTopology K := TopologicalSpace.Subtype.secondCountableTopology (K : Set G)
  let : SecondCountableTopology Q := QuotientGroup.isOpenQuotientMap_mk.secondCountableTopology
  let : CompactSpace n.toMonoidHom.ker := isCompact_iff_compactSpace.mp hn.isCompact_ker
  let : SecondCountableTopology (K ⧸ K₁) := QuotientGroup.isOpenQuotientMap_mk.secondCountableTopology
  let : SecondCountableTopology n.toMonoidHom.ker := TopologicalSpace.Subtype.secondCountableTopology _
  refine (hn.exists_sectionEquiv s hs).elim fun d hd ↦ ?_
  have hmd (u : n.toMonoidHom.ker) (t : ℝ≥0ˣ) : n (d (u,t)) = t := (congrArg n (hd (u,t))).trans
    (by rw [map_mul, show n u.val = 1 from u.property, one_mul, hs])
  let i : ModulatedExponentialDecayStage m I k →ₗ[ℂ] E := modulatedExponentialDecayStageInclusion m I k
  let A := ModulatedExponentialDecayStage m I k
  let H := n.toMonoidHom.ker
  let ev (b : E) (u : K) (t : ℝ≥0ˣ) := b.val (u.val * τ t)
  let v (a : A) (u : H) (t : ℝ≥0ˣ) := a.val (d (u,t))
  let g (h : SchwartzBruhat H) (u : H) := h u
  let c (h : SchwartzBruhat K) (u : K) := h u
  let f (w : P) (t : ℝ≥0ˣ) := w.val (Real.log (t.val : ℝ))
  refine (hm.exists_sectionEquiv τ hτ).elim fun dG hdG ↦ ?_
  have hev : Injective ev := split_decay_eval_injective m I τ dG hdG
  let r₀ (u : K) : H := ⟨q u.val, u.property⟩
  have hi (a : A) (u : K) (t : ℝ≥0ˣ) : ev (i a) u t = v a (r₀ u) t := by
    change a.val (q (u.val * τ t)) = a.val (d (r₀ u,t))
    exact congrArg a.val ((map_mul q u.val (τ t)).trans (hd (r₀ u,t)).symm)
  refine (pull_quotient_kernel_test m k).elim fun j hj ↦ ?_
  have ha (x : SchwartzBruhat H) (w : P) : ∃ a : A, ∀ u t, v a u t = g x u * f w t := by
    refine (split_pure_decay_mem n I hn hInt hne s hs x w).elim fun z hz ↦ ?_
    let a : A := ⟨z.val, z.property⟩
    refine ⟨a, fun u t ↦ ?_⟩
    exact (congrArg z.val (hd (u,t))).trans (hz u t)
  have hj' (x : SchwartzBruhat H) (u : K) : c (j x) u = g x (r₀ u) := hj x u
  have hS' (x : SchwartzBruhat K) (w : P) : ∃ b ∈ S, ∀ u t, ev b u t = c x u * f w t := hS x w
  have hp := stage_product_preimage (A := A) (B := E) i ev hev v r₀ hi g c f j hj' (S : Set E) hS' ha
  refine ⟨d, hmd, fun x w ↦ ?_⟩
  refine (hp x w).elim fun a hmem ↦ ⟨a, hmem.1, fun u t ↦ ?_⟩
  exact hmem.2 u t

include hne in
/-- Closed subspaces containing the split products on a single quotient
contain that whole stage. -/
private theorem closed_contains_quotient_stage {H : Type*} [CommGroup H] [TopologicalSpace H]
    [IsTopologicalGroup H] [T2Space H] [LocallyCompactSpace H] [SecondCountableTopology H]
    (k : GoodCompact) [IsClosed (k.val : Set G)] (d : H × ℝ≥0ˣ ≃ₜ* (G ⧸ k.val))
    (hd : ∀ u t, quotientModulation m k.val k.property.1 (d (u,t)) = t)
    (S : Submodule ℂ E) (hS : IsClosed (S : Set E))
    (hp : ∀ (x : SchwartzBruhat H) (w : P),
      ∃ z : ModulatedExponentialDecayStage m I k, modulatedExponentialDecayStageInclusion m I k z ∈ S ∧
        ∀ u t, z.val (d (u,t)) = x u * w.val (Real.log (t.val : ℝ))) :
    ∀ a : ModulatedExponentialDecayStage m I k, modulatedExponentialDecayStageInclusion m I k a ∈ S := by
  let A := ModulatedExponentialDecayStage m I k
  let i : A →ₗ[ℂ] E := modulatedExponentialDecayStageInclusion m I k
  let V : Submodule ℂ A := S.comap i
  have hc : @Continuous A E _ _ i := (withGeneratingSeminorms_spec _ _).continuous_of_continuous_comp i
    fun p ↦ p.property k
  have hprod (x : SchwartzBruhat H) (w : P) :
      ∃ z ∈ V, ∀ u t, z.val (d (u,t)) = x u * w.val (Real.log (t.val : ℝ)) := hp x w
  have hD := dense_decay_stage_of_products m I hne k d hd V hprod
  intro a
  exact stage_subspace_contains (X := A) (Y := E) i S hS hc hD a

include hSC hm hInt hne hτ in
/-- A closed subspace containing all split products contains every quotient stage. -/
private theorem contains_stage_of_split_products (k : GoodCompact) (S : Submodule ℂ E)
    (hsC : IsClosed (S : Set E))
    (hS : ∀ (h : SchwartzBruhat K) (f : P), ∃ b ∈ S, ∀ (u : K) (t : ℝ≥0ˣ),
      b.val (u.val * τ t) = h u * f.val (Real.log (t.val : ℝ))) :
    ∀ a : ModulatedExponentialDecayStage m I k, modulatedExponentialDecayStageInclusion m I k a ∈ S := by
  let : IsClosed (k.val : Set G) := k.property.1.isClosed
  let n := quotientModulation m k.val k.property.1
  let Q := G ⧸ k.val
  let : SecondCountableTopology Q := QuotientGroup.isOpenQuotientMap_mk.secondCountableTopology
  have hnc : IsClosed (n.toMonoidHom.ker : Set Q) := isClosed_singleton.preimage n.continuous
  let : LocallyCompactSpace n.toMonoidHom.ker := hnc.locallyCompactSpace
  let : SecondCountableTopology n.toMonoidHom.ker := TopologicalSpace.Subtype.secondCountableTopology _
  refine (split_products_on_quotient m I hm hInt hne τ hτ k S hS).elim fun d hd ↦ ?_
  exact closed_contains_quotient_stage (H := n.toMonoidHom.ker) m I hne k d hd.1 S hsC hd.2
/-- The closure of a linear image is the whole space if the image contains
the pure products and these generate every quotient stage densely. -/
private theorem dense_of_stage_span {X Y ι A B κ σ : Type*} {Z : ι → Type*}
    [TopologicalSpace X] [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace Y] [AddCommGroup Y] [Module ℂ Y] [IsTopologicalAddGroup Y] [ContinuousConstSMul ℂ Y]
    (L : X →L[ℂ] Y)
    (j : ∀ k, Z k → Y) (hc : ∀ y, ∃ k, y ∈ range (j k))
    (v : Y → κ → σ → ℂ) (g : A → κ → ℂ) (f : B → σ → ℂ) (pure : A → B → X)
    (hp : ∀ a b u t, v (L (pure a b)) u t = g a u * f b t)
    (hs : ∀ (k : ι) (S : Submodule ℂ Y), IsClosed (S : Set Y) →
      (∀ a b, ∃ y ∈ S, ∀ u t, v y u t = g a u * f b t) → ∀ z, j k z ∈ S) :
    DenseRange L := by
  let R := L.toLinearMap.range
  let S := R.topologicalClosure
  have hP (a : A) (b : B) : ∃ y ∈ S, ∀ u t, v y u t = g a u * f b t :=
    ⟨L (pure a b), R.le_topologicalClosure ⟨_,rfl⟩, hp a b⟩
  intro y
  obtain ⟨k, z, hz⟩ := hc y
  exact (congrArg (· ∈ S) hz).mp (hs k S R.isClosed_topologicalClosure hP z)

include hSC hm hInt hne hτ in
/-- Split products have dense span in the full decay topology. -/
private theorem dense_split_decay_product
    (L : Completion T →L[ℂ] E)
    (hL : ∀ (h : SchwartzBruhat K) (f : P) (u : K) (t : ℝ≥0ˣ),
      (L (Completion.coe' (α := T) (h ⊗ₜ[ℂ] f))).val ((u : G) * τ t) =
          h u * f.val (Real.log (t.val : ℝ))) :
    DenseRange L := by
  let j (k : GoodCompact) : ModulatedExponentialDecayStage m I k → E := modulatedExponentialDecayStageInclusion m I k
  let v (b : E) (u : K) (t : ℝ≥0ˣ) := b.val (u.val * τ t)
  let g (h : SchwartzBruhat K) (u : K) := h u
  let f (w : P) (t : ℝ≥0ˣ) := w.val (Real.log (t.val : ℝ))
  let pure (h : SchwartzBruhat K) (w : P) := Completion.coe' (α := T) (h ⊗ₜ[ℂ] w)
  have hc : ∀ y : E, ∃ k, y ∈ range (j k) := modulatedExponentialDecay_exists_stage m I hm hτ.surjective hInt hne
  with_reducible_and_instances
    exact dense_of_stage_span (X := Completion T) (Y := E) (Z := ModulatedExponentialDecayStage m I)
      L j hc v g f pure hL (contains_stage_of_split_products m I hm hInt hne τ hτ)

section

local notation "TI" => InductiveTensor P (SchwartzBruhat K)
local notation "TP" => ProjectiveTensor P (SchwartzBruhat K)
local notation "compareTensors" => @Completion.map TI _ TP _ id

include hSC hm hInt hne hτ

/-- Paper: Proposition D.3.3.10, p. 807. The continuous linear comparison from the
completed inductive tensor product to the completed projective tensor product is bijective
and identifies their bounded subsets. -/
theorem modulatedExponentialDecay_tensor_comparison_bounded :
    ∃ C : Completion TI →L[ℂ] Completion TP, (C : Completion TI → Completion TP) = compareTensors ∧
      Bijective C ∧ ∀ B : Set (Completion TI), IsVonNBounded ℂ (C '' B) ↔ IsVonNBounded ℂ B :=
  by sorry

omit hSC hm hInt hne hτ in
private theorem continuous_inductiveTensor_flip (A B : Type*) [AddCommGroup A] [Module ℂ A]
    [TopologicalSpace A] [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] :
    @Continuous (InductiveTensor A B) (InductiveTensor B A) _ _ (TensorProduct.comm ℂ A B) := by
  let flipMap : InductiveTensor A B →ₗ[ℂ] InductiveTensor B A := (TensorProduct.comm ℂ A B).toLinearMap
  let ps := (fun p : {p : Seminorm ℂ (A ⊗[ℂ] B) //
    (∀ x : A, Continuous (fun y : B ↦ p (x ⊗ₜ[ℂ] y))) ∧
    (∀ y : B, Continuous (fun x : A ↦ p (x ⊗ₜ[ℂ] y)))} ↦ p.val)
  refine (withGeneratingSeminorms_spec _ _).continuous_of_continuous_comp flipMap fun q ↦ ?_
  exact (withGeneratingSeminorms_spec _ ps).continuous_seminorm
    ⟨q.val.comp flipMap, fun x ↦ q.property.2 x, fun y ↦ q.property.1 y⟩

omit hSC hm hInt hne hτ in
/-- Flipping the two factors preserves the separately continuous seminorms that
generate the inductive tensor topology. The two flips remain inverse on completion. -/
private theorem completedInductiveTensor_swap (X Y : Type*)
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] :
    ∃ e : Completion (InductiveTensor X Y) ≃L[ℂ] Completion (InductiveTensor Y X),
      ∀ x y, e (Completion.coe' (α := InductiveTensor X Y) (x ⊗ₜ[ℂ] y)) =
        Completion.coe' (α := InductiveTensor Y X) (y ⊗ₜ[ℂ] x) := by
  let flipMap : InductiveTensor X Y →L[ℂ] InductiveTensor Y X := ⟨(TensorProduct.comm ℂ X Y).toLinearMap, continuous_inductiveTensor_flip X Y⟩
  let U : InductiveTensor Y X →L[ℂ] InductiveTensor X Y := ⟨(TensorProduct.comm ℂ Y X).toLinearMap, continuous_inductiveTensor_flip Y X⟩
  have hT (x : Completion (InductiveTensor X Y)) : U.completion (flipMap.completion x) = x := by
    refine Completion.induction_on (p := fun z ↦ U.completion (flipMap.completion z) = z) x
      (isClosed_eq (U.completion.continuous.comp flipMap.completion.continuous) continuous_id) ?_
    intro z
    rw [ContinuousLinearMap.completion_apply_coe, ContinuousLinearMap.completion_apply_coe]
    exact congrArg Completion.coe' ((TensorProduct.comm ℂ X Y).symm_apply_apply z)
  have hU (x : Completion (InductiveTensor Y X)) : flipMap.completion (U.completion x) = x := by
    refine Completion.induction_on (p := fun z ↦ flipMap.completion (U.completion z) = z) x
      (isClosed_eq (flipMap.completion.continuous.comp U.completion.continuous) continuous_id) ?_
    intro z
    rw [ContinuousLinearMap.completion_apply_coe, ContinuousLinearMap.completion_apply_coe]
    exact congrArg Completion.coe' ((TensorProduct.comm ℂ Y X).symm_apply_apply z)
  exact ⟨ContinuousLinearEquiv.equivOfInverse flipMap.completion U.completion hT hU,
    fun x y ↦ flipMap.completion_apply_coe (x ⊗ₜ[ℂ] y)⟩

end

/-- If a nuclear factor embeds into a product, its coordinate tensor maps into
the completed injective tensors embed the full projective completion. -/
private theorem projective_tensor_coordinates {A B X ι : Type*}
    [AddCommGroup A] [Module ℂ A] [TopologicalSpace A] [PolynormableSpace ℂ A] [T2Space A]
    [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] [PolynormableSpace ℂ B] [T2Space B]
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [PolynormableSpace ℂ X] [T2Space X]
    (t : A →L[ℂ] (ι → X)) (ht : IsEmbedding t)
    (hN : @IsInducing (ProjectiveTensor A B) (InjectiveTensor A B) _ _ id) :
    ∃ J : Completion (ProjectiveTensor A B) →L[ℂ] (ι → Completion (InjectiveTensor X B)),
      IsEmbedding J ∧ ∀ a b i, J (Completion.coe' (α := ProjectiveTensor A B) (a ⊗ₜ[ℂ] b)) i =
        Completion.coe' (α := InjectiveTensor X B) (t a i ⊗ₜ[ℂ] b) := by
  let unit : B →L[ℂ] (Unit → B) := ContinuousLinearMap.pi fun _ ↦ ContinuousLinearMap.id ℂ B
  have hu : IsEmbedding unit := ⟨IsInducing.of_comp unit.continuous (continuous_apply ()) IsInducing.id,
    fun _ _ he ↦ congrFun he ()⟩
  let A₁ := InjectiveTensor A B
  let A₂ := InjectiveTensor (ι → X) (Unit → B)
  let B₂ := InjectiveTensor X B
  let H : A₁ →ₗ[ℂ] A₂ := injectiveTensorMap t.toLinearMap unit.toLinearMap
  have hH : IsInducing H := (injectiveTensorMap_isEmbedding t unit ht hu).isInducing
  let v (i : ι × Unit) : A₂ →ₗ[ℂ] B₂ := injectiveTensorMap (LinearMap.proj i.1) (LinearMap.proj i.2)
  have hv : IsInducing (fun z : A₂ ↦ fun i ↦ v i z) :=
    (injectiveTensor_products_isUniformInducing (fun _ : ι ↦ X) (fun _ : Unit ↦ B)).isInducing
  let inc := (Completion.toComplL : B₂ →L[ℂ] Completion B₂)
  have hi := IsInducing.piMap (fun _ : ι × Unit ↦ (Completion.isDenseInducing_coe (α := B₂)).isInducing)
  let P₀ := ProjectiveTensor A B
  let M : P₀ →ₗ[ℂ] (ι → Completion B₂) :=
    LinearMap.pi fun i ↦ (inc.toLinearMap.comp (v (i,()))).comp (show P₀ →ₗ[ℂ] A₂ from H)
  let dup (z : ι → Completion B₂) (p : ι × Unit) := z p.1
  have hd : Continuous dup := continuous_pi fun p ↦ continuous_apply p.1
  have hcomp : IsInducing (dup ∘ M) := hi.comp (hv.comp (hH.comp hN))
  have hc : Continuous M := continuous_pi fun i ↦ (continuous_apply (i,())).comp hcomp.continuous
  let D : P₀ →L[ℂ] (ι → Completion B₂) := ⟨M,hc⟩
  have him : IsInducing D := IsInducing.of_comp hc hd hcomp
  have hU := AddMonoidHom.isUniformInducing_of_isInducing (f := D.toAddMonoidHom) him
  let J := D.fromCompletion
  have hJ : IsUniformInducing J := Completion.isUniformInducing_extension hU
  exact ⟨J, hJ.isInducing.isEmbedding, fun a b i ↦ congrFun (D.fromCompletion_apply_coe (a ⊗ₜ[ℂ] b)) i⟩

/-- A bounded inverse on a comparison space gives a continuous inverse on a
bornological function space when the comparison embeds by weighted coordinates. -/
private theorem inducing_of_bounded_comparison {A Y W V : Type*}
    [AddCommGroup A] [Module ℂ A] [TopologicalSpace A] [PolynormableSpace ℂ A]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
    [AddCommGroup W] [Module ℂ W] [UniformSpace W] [IsUniformAddGroup W] [CompleteSpace W]
    [AddCommGroup V] [Module ℂ V] [UniformSpace V] [IsUniformAddGroup V] [T2Space V]
    (L : A →L[ℂ] Y) (hd : DenseRange L)
    (C : A →L[ℂ] W) (hC : Bijective C) (hb : ∀ B : Set A, IsVonNBounded ℂ (C '' B) → IsVonNBounded ℂ B)
    (J : W →L[ℂ] V) (hJ : IsEmbedding J) (F : Y →L[ℂ] V) (hF : ∀ a, F (L a) = J (C a))
    (hY : ∀ p : Seminorm ℂ Y, (∀ B : Set Y, IsVonNBounded ℂ B → BddAbove (p '' B)) → Continuous p) :
    IsInducing L := by
  let e := LinearEquiv.ofBijective C.toLinearMap hC
  let jr := LinearEquiv.ofInjective J.toLinearMap hJ.injective
  have hclosed : IsClosed (range J) :=
    (AddMonoidHom.isUniformInducing_of_isInducing (f := J.toAddMonoidHom) hJ.isInducing).isComplete_range.isClosed
  have hmem (y : Y) : F y ∈ J.range := closure_minimal (s := range L) (t := F ⁻¹' range J)
    (fun _ ⟨a,ha⟩ ↦ ⟨C a, (hF a).symm.trans (congrArg F ha)⟩) (hclosed.preimage F.continuous) (hd y)
  let r := jr.symm.toLinearMap.comp (F.toLinearMap.codRestrict J.range hmem)
  have hr (y : Y) : J (r y) = F y := congrArg Subtype.val (jr.apply_symm_apply _)
  have hc : Continuous r := hJ.isInducing.continuous_iff.mpr (by
    have heq : J ∘ r = F := funext hr
    rw [heq]
    exact F.continuous)
  let R := e.symm.toLinearMap.comp r
  have hCR (y : Y) : C (R y) = r y := e.apply_symm_apply _
  have hR : Continuous R := continuous_linear_of_bornological (X := Y) (Y := A) hY R fun B hB ↦ by
    apply hb
    rw [image_image, show (fun x ↦ C (R x)) = r from funext hCR]
    exact hB.image (⟨r,hc⟩ : Y →L[ℂ] W)
  have hRL : R ∘ L = id := funext fun a ↦ hC.1 ((hCR (L a)).trans (hJ.injective ((hr (L a)).trans (hF a))))
  exact IsInducing.of_comp L.continuous hR (hRL.symm ▸ IsInducing.id)

/-- Identify multiplication as an inducing map by embedding its projective
comparison in the product of its ordinary weighted kernel coordinates. -/
private theorem split_mul_inducing {A B X Y V ι : Type*}
    [AddCommGroup A] [Module ℂ A] [TopologicalSpace A] [PolynormableSpace ℂ A] [T2Space A]
    [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] [PolynormableSpace ℂ B] [T2Space B]
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [PolynormableSpace ℂ X] [T2Space X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
    [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    (t : A →L[ℂ] (ι → X)) (ht : IsEmbedding t)
    (hN : @IsInducing (ProjectiveTensor A B) (InjectiveTensor A B) _ _ id)
    (L : Completion (InductiveTensor B A) →L[ℂ] Y) (hd : DenseRange L)
    (hcompare : ∃ C : Completion (InductiveTensor A B) →L[ℂ] Completion (ProjectiveTensor A B),
      ⇑C = @Completion.map (InductiveTensor A B) _ (ProjectiveTensor A B) _ id ∧
      Bijective C ∧ ∀ S, IsVonNBounded ℂ (C '' S) ↔ IsVonNBounded ℂ S)
    (e : Completion (InductiveTensor B X) ≃L[ℂ] V) (w : ι → Y →L[ℂ] V)
    (hw : ∀ a b i, w i (L (Completion.coe' (α := InductiveTensor B A) (b ⊗ₜ[ℂ] a))) =
      e (Completion.coe' (α := InductiveTensor B X) (b ⊗ₜ[ℂ] t a i)))
    (hY : ∀ p : Seminorm ℂ Y, (∀ S : Set Y, IsVonNBounded ℂ S → BddAbove (p '' S)) → Continuous p) :
    IsInducing L := by
  obtain ⟨C, heq, hC, hCb⟩ := hcompare
  let TI := InductiveTensor B A
  let TT := InductiveTensor A B
  let TP := ProjectiveTensor A B
  let D := InjectiveTensor X B
  let : PolynormableSpace ℂ (Completion TI) := polynormableSpace_completion
  refine (projective_tensor_coordinates t ht hN).elim fun J hJ ↦ ?_
  refine (completedInductiveTensor_swap B A).elim fun r hr ↦ ?_
  let C' := C.comp r.toContinuousLinearMap
  have hb (S : Set (Completion TI)) (hS : IsVonNBounded ℂ (C' '' S)) : IsVonNBounded ℂ S := by
    have hB := (hCb (r '' S)).mp ((congrArg (IsVonNBounded ℂ) (image_image C r S)).mpr hS)
    have he : r.symm '' (r '' S) = S := r.toEquiv.symm_image_image S
    exact (congrArg (IsVonNBounded ℂ) he).mp (hB.image r.symm.toContinuousLinearMap)
  let Q : InductiveTensor X B →L[ℂ] D := ⟨LinearMap.id, (continuous_projectiveTensor_to_injectiveTensor X B).comp
    (continuous_inductiveTensor_to_projectiveTensor («E» := X) (F := B))⟩
  refine (completedInductiveTensor_swap B X).elim fun sw hsw ↦ ?_
  let coord := Q.completion.comp (sw.toContinuousLinearMap.comp e.symm.toContinuousLinearMap)
  let F := ContinuousLinearMap.pi fun i ↦ coord.comp (w i)
  let left := F.comp L
  let right := J.comp C'
  let inc := (Completion.toComplL : TI →L[ℂ] Completion TI)
  let c : TT →L[ℂ] TP := ⟨LinearMap.id, continuous_inductiveTensor_to_projectiveTensor⟩
  have hU : @UniformContinuous TT TP _ _ id := c.uniformContinuous
  have hmap (b : B) (a : A) : C' (Completion.coe' (α := TI) (b ⊗ₜ[ℂ] a)) =
      Completion.coe' (α := TP) (a ⊗ₜ[ℂ] b) := (congrArg C (hr b a)).trans
    ((congrFun heq _).trans (Completion.map_coe hU _))
  have he : (left.comp inc).toLinearMap = (right.comp inc).toLinearMap := by
    refine TensorProduct.ext' fun b a ↦ funext fun i ↦ ?_
    let z := Completion.coe' (α := InductiveTensor B X) (b ⊗ₜ[ℂ] t a i)
    have hcoord : coord (e z) = Completion.coe' (α := D) (t a i ⊗ₜ[ℂ] b) :=
      (congrArg (fun d ↦ Q.completion (sw d)) (e.symm_apply_apply z)).trans
        ((congrArg Q.completion (hsw b (t a i))).trans (Q.completion_apply_coe (t a i ⊗ₜ[ℂ] b)))
    exact (congrArg coord (hw a b i)).trans (hcoord.trans
      ((hJ.2 a b i).symm.trans (congrArg (fun u ↦ J u i) (hmap b a).symm)))
  have hF (z : Completion TI) : left z = right z := Completion.induction_on
    (p := fun y ↦ left y = right y) z (isClosed_eq left.continuous right.continuous)
    (fun a ↦ LinearMap.congr_fun he a)
  exact inducing_of_bounded_comparison L hd C' (hC.comp r.bijective) hb J hJ.1 F hF hY

include hne in
/-- All scalar twists together embed the scalar decay profiles in a product of
ordinary Schwartz spaces on the multiplicative positive reals. -/
private theorem scalar_twist_embedding :
    ∃ t : P →L[ℂ] (I → SchwartzBruhat ℝ≥0ˣ), IsEmbedding t ∧
      ∀ (f : P) (a : I) (v : ℝ≥0ˣ), t f a v = logExponentialDecayTwist I a f (Real.log (v.val : ℝ)) := by
  let : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  refine (schwartzBruhat_realCoordinate_equiv positiveRealLogEquiv).elim fun s hs ↦ ?_
  let t₀ (a : I) : P →L[ℂ] SchwartzMap ℝ ℂ := ⟨logExponentialDecayTwist I a,
    (continuous_apply a).comp (positiveRealExponentialDecay_isEmbedding I hne).continuous⟩
  let t := ContinuousLinearMap.pi fun a ↦ s.toContinuousLinearMap.comp (t₀ a)
  have hEmb : IsEmbedding t := (IsEmbedding.piMap (fun _ : I ↦ s.toHomeomorph.isEmbedding)).comp
    (positiveRealExponentialDecay_isEmbedding I hne)
  exact ⟨t,hEmb,fun f a v ↦ (hs (t₀ a f) v).trans (congrArg (t₀ a f) (positiveRealLogEquiv_apply v))⟩

include hτ in
private theorem split_twist_pure_values (D : E) (f : P) (h : SchwartzBruhat K)
    (hD : ∀ (u : K) (t : ℝ≥0ˣ), D.val (u.val * τ t) = h u * f.val (Real.log (t.val : ℝ)))
    (a : I) (u : K) (t : ℝ≥0ˣ) :
    modulatedExponentialDecayTwist m I a D (u.val * τ t) =
      h u * logExponentialDecayTwist I a f (Real.log (t.val : ℝ)) := by
  have hmt : m (u.val * τ t) = t := by rw [map_mul, show m u.val = 1 from u.property, one_mul, hτ]
  change ((((m (u.val * τ t)).val : ℝ) ^ (a : ℝ) : ℝ) : ℂ) * D.val (u.val * τ t) = _
  rw [hmt, identityWeight_log, positiveRealLogEquiv_apply, hD]
  exact (mul_left_comm _ _ _).trans (congrArg (h u * ·) (logExponentialDecayTwist_apply I a f _).symm)

include hτ in
/-- The ordinary Schwartz representative of a weighted pure product is
determined by its values in split coordinates. -/
private theorem split_decay_twist_eq (d : K × ℝ≥0ˣ ≃ₜ* G) (hd : ∀ p, d p = p.1.val * τ p.2)
    (y : E) (f : P) (h : SchwartzBruhat K)
    (hy : ∀ (u : K) (t : ℝ≥0ˣ), y.val (u.val * τ t) = h u * f.val (Real.log (t.val : ℝ)))
    (a : I) (z : SchwartzBruhat G) (hz : ∀ u t, z (d (u,t)) =
      h u * logExponentialDecayTwist I a f (Real.log (t.val : ℝ))) :
    modulatedExponentialDecayTwist m I a y = z := by
  let A := modulatedExponentialDecayTwist m I a y
  refine Subtype.ext (funext fun x ↦ ?_)
  let p := d.symm x
  exact (congrArg (fun w : G ↦ A w = z w) (d.apply_symm_apply x)).mp
    ((congrArg A (hd p)).trans ((split_twist_pure_values m I τ hτ y f h hy a p.1 p.2).trans (hz p.1 p.2).symm))

include hSC hm hInt hne in
private theorem decay_projective_to_injective :
    @IsInducing (ProjectiveTensor P (SchwartzBruhat K)) (InjectiveTensor P (SchwartzBruhat K)) _ _ id := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let : SecondCountableTopology K := TopologicalSpace.Subtype.secondCountableTopology (K : Set G)
  let : T2Space (SchwartzBruhat K) := schwartzBruhat_t2
  exact
    ((positiveRealExponentialDecay_nuclear I hInt hne).2.2 (SchwartzBruhat K)
      inferInstance inferInstance inferInstance inferInstance inferInstance).isEmbedding.isInducing

include hSC hm hInt hne hτ in
/-- Paper: (D.3.3.3), p. 806. Pulling back the decay-space topology by
multiplication gives the topology of the completed inductive tensor product. -/
private theorem modulatedExponentialDecay_completedTensor_mul_isInducing
    (L : Completion T →L[ℂ] E)
    (hL : ∀ (h : SchwartzBruhat K) (f : P) (u : K) (t : ℝ≥0ˣ),
      (L (Completion.coe' (α := T) (h ⊗ₜ[ℂ] f))).val ((u : G) * τ t) =
          h u * f.val (Real.log (t.val : ℝ))) :
    IsInducing L := by
  have hDense : DenseRange L := dense_split_decay_product m I hm hInt hne τ hτ L hL
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let : SecondCountableTopology K := TopologicalSpace.Subtype.secondCountableTopology (K : Set G)
  let : T2Space (SchwartzBruhat K) := schwartzBruhat_t2
  let : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let : T2Space (SchwartzBruhat ℝ≥0ˣ) := schwartzBruhat_t2
  let : T2Space P := (positiveRealExponentialDecay_isEmbedding I hne).t2Space
  have hN := decay_projective_to_injective m I hm hInt hne
  refine (hm.exists_sectionEquiv τ hτ).elim fun d hd ↦ ?_
  refine (split_schwartz_kernel d).elim fun e he ↦ ?_
  refine (scalar_twist_embedding I hne).elim fun t ht ↦ ?_
  have hC := modulatedExponentialDecay_tensor_comparison_bounded m I hm hInt hne τ hτ
  let w (a : I) : E →L[ℂ] SchwartzBruhat G := ⟨modulatedExponentialDecayTwist m I a, continuous_decay_twist m I a⟩
  have hw (f : P) (h : SchwartzBruhat K) (a : I) :
      w a (L (Completion.coe' (α := T) (h ⊗ₜ[ℂ] f))) =
        e (Completion.coe' (α := InductiveTensor (SchwartzBruhat K) (SchwartzBruhat ℝ≥0ˣ)) (h ⊗ₜ[ℂ] t f a)) := by
    let y := L (Completion.coe' (α := T) (h ⊗ₜ[ℂ] f))
    let z := e (Completion.coe' (α := InductiveTensor (SchwartzBruhat K) (SchwartzBruhat ℝ≥0ˣ))
      (h ⊗ₜ[ℂ] t f a))
    have hz (u : K) (v : ℝ≥0ˣ) : z (d (u,v)) =
        h u * logExponentialDecayTwist I a f (Real.log (v.val : ℝ)) :=
      (he h (t f a) u v).trans (congrArg (h u * ·) (ht.2 f a v))
    exact split_decay_twist_eq m I τ hτ d hd y f h (hL h f) a z hz
  have hY := modulatedExponentialDecay_bornological m I hm hInt hne τ hτ
  with_reducible_and_instances
    exact split_mul_inducing (A := P) (B := SchwartzBruhat K) (X := SchwartzBruhat ℝ≥0ˣ) (Y := E)
      (V := SchwartzBruhat G) t ht.1 hN L hDense hC e w hw hY

/-- An inducing linear map with dense range from a complete space onto a
Hausdorff target is surjective. -/
private theorem surjective_of_inducing_dense {X Y : Type*}
    [UniformSpace X] [AddCommGroup X] [IsUniformAddGroup X] [Module ℂ X] [CompleteSpace X]
    [UniformSpace Y] [AddCommGroup Y] [IsUniformAddGroup Y] [Module ℂ Y] [T2Space Y]
    (L : X →L[ℂ] Y) (hi : IsInducing L) (hd : DenseRange L) : Surjective L :=
  fun y ↦ (AddMonoidHom.isUniformInducing_of_isInducing (f := L.toAddMonoidHom) hi).isComplete_range.isClosed.closure_eq.le (hd y)

include hSC hm hInt hne hτ in
/-- Paper: (D.3.3.3), p. 806. Multiplication from the completed tensor product
reaches every decay function. The quotient-stage isomorphisms give preimages
for functions in the individual compact-subgroup stages. -/
private theorem modulatedExponentialDecay_completedTensor_mul_surjective
    (L : Completion T →L[ℂ] E)
    (hL : ∀ (h : SchwartzBruhat K) (f : P) (u : K) (t : ℝ≥0ˣ),
      (L (Completion.coe' (α := T) (h ⊗ₜ[ℂ] f))).val ((u : G) * τ t) =
          h u * f.val (Real.log (t.val : ℝ))) :
    Surjective L := by
  let : T2Space E := (modulatedExponentialDecay_strictLF m I hm hInt hne τ hτ).1
  have hi := modulatedExponentialDecay_completedTensor_mul_isInducing m I hm hInt hne τ hτ L hL
  have hd := dense_split_decay_product m I hm hInt hne τ hτ L hL
  with_reducible_and_instances
    exact surjective_of_inducing_dense (X := Completion T) (Y := E) L hi hd

include hSC hm hInt hne hτ in
/-- Paper: Theorem D.3.3.7(1), p. 806. The splitting of the modulation induces
the completed inductive tensor isomorphism, given by multiplication in split coordinates. -/
theorem modulatedExponentialDecay_tensor_equiv :
    ∃ e : Completion T ≃L[ℂ] E,
      ∀ (h : SchwartzBruhat K) (f : P) (u : K) (t : ℝ≥0ˣ),
        (e (Completion.coe' (α := T) (h ⊗ₜ[ℂ] f))).val ((u : G) * τ t) =
          h u * f.val (Real.log (t.val : ℝ)) := by
  exact bundle_inducing_surjection (A := Completion T) (B := E)
    (fun L ↦ ∀ (h : SchwartzBruhat K) (f : P) (u : K) (t : ℝ≥0ˣ),
      (L (Completion.coe' (α := T) (h ⊗ₜ[ℂ] f))).val ((u : G) * τ t) =
        h u * f.val (Real.log (t.val : ℝ)))
    (modulatedExponentialDecay_completedTensor_mul m I hm hInt hne τ hτ)
    (modulatedExponentialDecay_completedTensor_mul_surjective m I hm hInt hne τ hτ)
    (modulatedExponentialDecay_completedTensor_mul_isInducing m I hm hInt hne τ hτ)

end Structure

section BoundedSets

variable [hSC : SecondCountableTopology G]
variable (hm : IsModulation m) (hInt : OrdConnected I) (hne : I.Nonempty)
variable (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ m)

-- Remark D.3.3.8 is the cofinality assertion in modulatedExponentialDecay_stageLimit.
-- Remark D.3.3.9 applies schwartzBruhat_acyclic on the norm-one subgroup.

local notation "TI" => InductiveTensor P (SchwartzBruhat K)
local notation "TP" => ProjectiveTensor P (SchwartzBruhat K)
local notation "compareTensors" => @Completion.map TI _ TP _ id

include hSC hm hInt hne hτ

omit hm hτ hInt hne hSC in
private theorem stage_tensor_swap (k : GoodCompact) :
    let k₁ := k.val.comap (Subgroup.subtype K)
    let Q := SchwartzBruhat (K ⧸ k₁)
    let A := InductiveTensor P Q
    let B := InductiveTensor Q P
    ∃ s : Completion A ≃L[ℂ] Completion B, ∀ (f : P) (h : Q),
      s (Completion.coe' (α := A) (f ⊗ₜ[ℂ] h)) = Completion.coe' (α := B) (h ⊗ₜ[ℂ] f) := by
  dsimp only
  with_reducible exact completedInductiveTensor_swap P (SchwartzBruhat (K ⧸ k.val.comap (Subgroup.subtype K)))

omit hSC hm hInt hne hτ in
private theorem eval_trans_of_equal {A B C D : Type*} [AddCommGroup A] [Module ℂ A] [TopologicalSpace A]
    [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] [AddCommGroup C] [Module ℂ C] [TopologicalSpace C]
    (r : A ≃L[ℂ] B) (v : B ≃L[ℂ] C) (ev : C → D) {x : A} {y : B} {d : D}
    (hr : r x = y) (hv : ev (v y) = d) : ev ((r.trans v) x) = d :=
  (congrArg (fun q ↦ ev (v q)) hr).trans hv

/-- Paper: Proposition D.3.3.10, p. 807. The reversed ordering of the completed
inductive tensor factors gives the same quotient stage, with multiplication in split coordinates. -/
theorem modulatedExponentialDecay_stage_tensor_equiv_swap (k : GoodCompact) :
    let k₁ := k.val.comap (Subgroup.subtype K)
    let Tₖ := InductiveTensor P (SchwartzBruhat (K ⧸ k₁))
    ∃ e : Completion Tₖ ≃L[ℂ] ModulatedExponentialDecayStage m I k,
      ∀ (f : P) (h : SchwartzBruhat (K ⧸ k₁)) (u : K) (t : ℝ≥0ˣ),
        (e (Completion.coe' (α := Tₖ) (f ⊗ₜ[ℂ] h))).val
          (((u : G) * τ t : G) : G ⧸ k.val) = h (u : K ⧸ k₁) * f.val (Real.log (t.val : ℝ)) :=
  by
  dsimp only
  refine (modulatedExponentialDecay_tensor_equiv m I hm hInt hne τ hτ).elim fun e he ↦ ?_
  refine (modulatedExponentialDecay_tensor_stage m I hm hInt hne τ hτ e he k).elim fun V hV ↦ ?_
  refine hV.elim fun j hj ↦ ?_
  refine (stage_tensor_swap m I k).elim fun R hR ↦ ?_
  refine ⟨R.trans V, fun f h u t ↦ ?_⟩
  let ev (w : ModulatedExponentialDecayStage m I k) : ℂ := w.val (((u : G) * τ t : G) : G ⧸ k.val)
  have hr := hR f h
  have hv := hj.2.1 h f u t
  with_reducible_and_instances exact eval_trans_of_equal R V ev hr hv

omit hSC hm hInt hne hτ in
private theorem separable_metrizable_subset_range {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [MetrizableSpace X] [SeparableSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] (i : X →ₗ[ℂ] Y) (hi : IsEmbedding i)
    (B : Set Y) (hsub : B ⊆ (i.range : Set Y)) : SeparableSpace B ∧ MetrizableSpace B := by
  let e := LinearEquiv.ofInjective i hi.injective
  have he : IsInducing e := IsInducing.subtypeVal.of_comp_iff.mp hi.isInducing
  have hEmb := (e.toEquiv.toHomeomorphOfIsInducing he).symm.isEmbedding.comp (IsEmbedding.inclusion hsub)
  let : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  let : SecondCountableTopology X := UniformSpace.secondCountable_of_separable X
  let : SecondCountableTopology B := hEmb.secondCountableTopology
  exact ⟨inferInstance, hEmb.metrizableSpace⟩

/-- Paper: Proposition D.3.3.10(1), p. 807. A bounded subset of the inductive
decay space is separable and metrizable in the subspace topology. -/
theorem modulatedExponentialDecay_bounded_separable_metrizable
    (B : Set E) (hB : IsVonNBounded ℂ B) : SeparableSpace B ∧ MetrizableSpace B := by
  refine (modulatedExponentialDecay_bounded_image_stage m I hm hInt hne τ hτ hB).elim fun k hstage ↦ ?_
  refine hstage.elim fun C hC ↦ ?_
  refine (modulatedExponentialDecay_stageLimit m I hm hτ.surjective hInt hne).elim fun stages hs ↦ ?_
  refine (hs.2.1 k).elim fun n hn ↦ ?_
  let X := ModulatedExponentialDecayStage m I (stages n)
  let : MetrizableSpace X := (modulatedExponentialDecayStage_frechet m hm hτ.surjective I hInt hne
    (stages n)).choose_spec.2.1
  let : SeparableSpace X := modulatedExponentialDecayStage_separable m hm hτ.surjective I hInt hne (stages n)
  refine separable_metrizable_subset_range (X := X) (Y := E)
    (modulatedExponentialDecayStageInclusion m I (stages n)) (hs.2.2.1 n) B fun x hx ↦ ?_
  have hmem := Eq.mpr (congrArg (fun S : Set E ↦ x ∈ S) hC.2) hx
  refine hmem.elim fun v hv ↦ ?_
  apply ((modulatedExponentialDecayStageInclusion_range m I (stages n)).2 x).mpr
  intro g u
  exact ((modulatedExponentialDecayStageInclusion_range m I k).2 x).mp ⟨v, hv.2⟩ g ⟨u.val, hn u.property⟩

/-- Paper: Proposition D.3.3.10(2), p. 807. The weighted profiles are
continuous for the inductive topology, which is therefore at least as fine
as the topology induced by the family of twists. -/
theorem modulatedExponentialDecay_twists_continuous :
    Continuous (fun (f : E) (a : I) ↦ modulatedExponentialDecayTwist m I a f) := by
  exact continuous_pi (continuous_decay_twist m I)

-- TODO(paper-gap): The author flags the proof of D.3.3.10(2) as incomplete
-- in footnote 21 on p. 810, including the missing contact with the decay stages.

omit hSC hm hInt hne hτ in
/-- For the induced topology, boundedness is precisely coordinatewise boundedness. -/
private theorem decay_induced_bounded_iff (B : Set E) :
    let L : E →ₗ[ℂ] (I → SchwartzBruhat G) := LinearMap.pi (modulatedExponentialDecayTwist m I)
    @IsVonNBounded ℂ E _ _ _ (TopologicalSpace.induced L inferInstance) B ↔
      ∀ a : I, IsVonNBounded ℂ (modulatedExponentialDecayTwist m I a '' B) := by
  intro L
  let ps := fun _ : I ↦ PolynormableSpace.withSeminorms ℂ (SchwartzBruhat G)
  have hpi := withSeminorms_pi ps
  let : TopologicalSpace E := TopologicalSpace.induced L inferInstance
  have h := (L.withSeminorms_induced hpi).isVonNBounded_iff_seminorm_bounded (s := B)
  exact h.trans ((hpi.image_isVonNBounded_iff_seminorm_bounded L).symm.trans
    (isVonNBounded_pi_iff.trans (forall_congr' fun a ↦ (congrArg (IsVonNBounded ℂ)
      (image_image (Function.eval a) L B)).to_iff)))

/-- Paper: Proposition D.3.3.10(2), p. 807. The inductive topology and the
topology induced by the product of the twists have the same bounded sets. -/
theorem modulatedExponentialDecay_bounded_iff_projective (B : Set E) :
    IsVonNBounded ℂ B ↔
      @IsVonNBounded ℂ E _ _ _
        (TopologicalSpace.induced (fun (f : E) (a : I) ↦ modulatedExponentialDecayTwist m I a f)
          inferInstance) B := by
  refine (Iff.intro (fun h a ↦ h.image
    (⟨modulatedExponentialDecayTwist m I a, continuous_decay_twist m I a⟩ : E →L[ℂ] SchwartzBruhat G))
    (decay_bounded_of_twists m I hm hInt hne τ hτ B)).trans (decay_induced_bounded_iff m I B).symm

/-- Paper: Proposition D.3.3.10(3), p. 807. A set of decay functions is
bounded exactly when every weighted image is Schwartz–Bruhat bounded. -/
theorem modulatedExponentialDecay_bounded_iff_twists (B : Set E) :
    IsVonNBounded ℂ B ↔
      ∀ a : I, IsVonNBounded ℂ (modulatedExponentialDecayTwist m I a '' B) := by
  exact (modulatedExponentialDecay_bounded_iff_projective m I hm hInt hne τ hτ B).trans
    (decay_induced_bounded_iff m I B)

-- TODO(paper-gap): Accumulation at an included endpoint does not control
-- the twist at that endpoint. The countable testing statement includes it.

omit hSC hm hInt hne hτ in
/-- Applying a continuous linear map to two bounded families gives a bounded family. -/
private theorem bounded_image_pair {D X : Type*} [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] [IsTopologicalAddGroup X] {B : Set D} (f g : D → X)
    (hf : IsVonNBounded ℂ (f '' B)) (hg : IsVonNBounded ℂ (g '' B)) (F : X × X →L[ℂ] X) :
    IsVonNBounded ℂ ((fun d ↦ F (f d, g d)) '' B) := by
  let u := ContinuousLinearMap.inl ℂ X X
  let v := ContinuousLinearMap.inr ℂ X X
  apply (((hf.image u).add (hg.image v)).image F).subset
  rintro _ ⟨d, hd, rfl⟩
  exact ⟨u (f d) + v (g d), Set.add_mem_add (mem_image_of_mem u (mem_image_of_mem f hd))
    (mem_image_of_mem v (mem_image_of_mem g hd)), congrArg F (Prod.ext (add_zero _) (zero_add _))⟩
omit hSC hm hInt hne hτ in
/-- If every coordinate is recovered continuously from two test coordinates, those
test coordinates detect boundedness of the whole family. -/
private theorem bounded_coordinates_iff_test {A D X : Type*} [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] [IsTopologicalAddGroup X] (t : A → D → X) (J : Set A)
    (h : ∀ a, ∃ b ∈ J, ∃ c ∈ J, ∃ F : X × X →L[ℂ] X, ∀ d, F (t b d, t c d) = t a d)
    (B : Set D) :
    (∀ a, IsVonNBounded ℂ (t a '' B)) ↔ ∀ a ∈ J, IsVonNBounded ℂ (t a '' B) := by
  refine ⟨fun h a _ ↦ h a, fun hb a ↦ ?_⟩
  obtain ⟨b, hbj, c, hcj, F, hF⟩ := h a
  exact (congrArg (fun f : D → X ↦ IsVonNBounded ℂ (f '' B)) (funext hF)).mp
    (bounded_image_pair (t b) (t c) (hb b hbj) (hb c hcj) F)

/-- Paper: Proposition D.3.3.10(3), p. 807. Boundedness can be checked
on a countable subset of exponents reaching both ends of the interval.
Deviation: Every a in I must lie between two test exponents, allowing equality.
This includes finite endpoints when they belong to I and handles unbounded intervals. -/
theorem modulatedExponentialDecay_bounded_iff_countable_twists
    (B : Set E) (J : Set I) (hJ : J.Countable)
    (hEnds : ∀ a : I, (∃ b ∈ J, (b : ℝ) ≤ a) ∧ ∃ c ∈ J, (a : ℝ) ≤ c) :
    IsVonNBounded ℂ B ↔
      ∀ a ∈ J, IsVonNBounded ℂ (modulatedExponentialDecayTwist m I a '' B) := by
  refine (modulatedExponentialDecay_bounded_iff_twists m I hm hInt hne τ hτ B).trans
    (bounded_coordinates_iff_test (D := E) (fun a f ↦ modulatedExponentialDecayTwist m I a f) J ?_ B)
  intro a
  refine (hEnds a).1.elim fun b hb ↦ ?_
  refine (hEnds a).2.elim fun c hc ↦ ?_
  have hF := modulationWeight_between_continuous m b a c hb.2 hc.2
  exact ⟨b, hb.1, c, hc.1, hF.choose, fun d ↦ Subtype.ext
    (hF.choose_spec d.val _ rfl rfl)⟩

omit hSC hm hInt hne hτ in
private theorem continuous_bounded_seminorm_of_equiv {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    (e : X ≃L[ℂ] Y)
    (hy : ∀ p : Seminorm ℂ Y, (∀ B : Set Y, IsVonNBounded ℂ B → BddAbove (p '' B)) → Continuous p)
    (p : Seminorm ℂ X) (hp : ∀ B : Set X, IsVonNBounded ℂ B → BddAbove (p '' B)) : Continuous p := by
  have hq : Continuous (p.comp e.symm.toLinearMap) := hy _ fun B hB ↦ by
    obtain ⟨r, hr⟩ := hp (e.symm '' B) (hB.image e.symm.toContinuousLinearMap)
    exact ⟨r, fun z ⟨y, hy, hz⟩ ↦ hz ▸ hr (mem_image_of_mem p (mem_image_of_mem e.symm hy))⟩
  exact (hq.comp e.continuous).congr fun x ↦ congrArg p (e.symm_apply_apply x)

omit hSC hm hInt hne hτ in
/-- A bounded bijection in both directions from a bornological space identifies
its topology with the one generated by bounded seminorms on the target. -/
private theorem topology_eq_induced_bounded_seminorms {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [t : TopologicalSpace X] [IsTopologicalAddGroup X] [PolynormableSpace ℂ X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    (map : X → Y) (C : X →L[ℂ] Y) (heq : ⇑C = map) (hC : Bijective C) (hB : ∀ B : Set X, IsVonNBounded ℂ (C '' B) ↔ IsVonNBounded ℂ B)
    (hx : ∀ p : Seminorm ℂ X, (∀ B : Set X, IsVonNBounded ℂ B → BddAbove (p '' B)) → Continuous p) :
    t = TopologicalSpace.induced map
      (inferInstanceAs (TopologicalSpace (WithGeneratingSeminorms Y
        (Subtype.val : {p : Seminorm ℂ Y // ∀ B : Set Y, IsVonNBounded ℂ B → BddAbove (p '' B)} → _)))) := by
  subst map
  let ps := (Subtype.val : {p : Seminorm ℂ Y // ∀ B : Set Y, IsVonNBounded ℂ B → BddAbove (p '' B)} → Seminorm ℂ Y)
  let Z := WithGeneratingSeminorms Y ps
  let e := LinearEquiv.ofBijective C.toLinearMap hC
  let f : X →ₗ[ℂ] Z := e.toLinearMap
  let g : Z →ₗ[ℂ] X := e.symm.toLinearMap
  have hgen := withGeneratingSeminorms_spec Y ps
  have hf : Continuous f := by
    refine hgen.continuous_of_continuous_comp f fun p ↦ hx (p.val.comp f) fun B hb ↦ ?_
    obtain ⟨r, hr⟩ := p.property (C '' B) ((hB B).mpr hb)
    exact ⟨r, fun z ⟨x, hx, hz⟩ ↦ hz ▸ hr (mem_image_of_mem p.val (mem_image_of_mem C hx))⟩
  have hg : Continuous g := by
    let qs := PolynormableSpace.withSeminorms ℂ X
    refine qs.continuous_of_continuous_comp g fun q ↦ hgen.continuous_seminorm ⟨q.val.comp g, fun B hb ↦ ?_⟩
    have hi : C '' (g '' B) = B := by
      ext y
      constructor
      · rintro ⟨_, ⟨z, hz, rfl⟩, hzy⟩
        exact ((e.apply_symm_apply z).symm.trans hzy) ▸ hz
      · intro hy
        exact ⟨g y, mem_image_of_mem g hy, e.apply_symm_apply y⟩
    have hb' := (hB (g '' B)).mp (Eq.mpr (congrArg (IsVonNBounded ℂ) hi) hb)
    obtain ⟨r, hr⟩ := qs.isVonNBounded_iff_seminorm_bddAbove.mp hb' q
    exact ⟨r, fun z ⟨y, hy, hz⟩ ↦ hz ▸ hr (mem_image_of_mem q.val (mem_image_of_mem g hy))⟩
  exact (Function.LeftInverse.isEmbedding (f := g) (g := f) e.symm_apply_apply hg hf).isInducing.eq_induced

/-- Paper: Remark D.3.3.11, p. 811. Pullback along the comparison bijection
identifies the topology generated by bounded seminorms on the projective completion
with the completed inductive tensor topology. -/
theorem modulatedExponentialDecay_tensor_bornologification :
    (inferInstance : TopologicalSpace (Completion TI)) =
      TopologicalSpace.induced compareTensors
        (inferInstanceAs (TopologicalSpace (WithGeneratingSeminorms (Completion TP)
          (Subtype.val : {p : Seminorm ℂ (Completion TP) //
            ∀ B : Set (Completion TP), IsVonNBounded ℂ B → BddAbove (p '' B)} → _)))) :=
  by
  let : PolynormableSpace ℂ (Completion TI) := polynormableSpace_completion
  have hC := modulatedExponentialDecay_tensor_comparison_bounded m I hm hInt hne τ hτ
  have he := modulatedExponentialDecay_tensor_equiv m I hm hInt hne τ hτ
  have hf := completedInductiveTensor_swap P (SchwartzBruhat K)
  have hbE := continuous_bounded_seminorm_of_equiv he.choose (modulatedExponentialDecay_bornological m I hm hInt hne τ hτ)
  have hb := continuous_bounded_seminorm_of_equiv hf.choose hbE
  exact topology_eq_induced_bounded_seminorms compareTensors hC.choose hC.choose_spec.1
    hC.choose_spec.2.1 hC.choose_spec.2.2 hb

omit hSC hm hInt hne hτ in
/-- A family of functionals that vanishes eventually on every bounded set of the
second factor gives a continuous inductive tensor seminorm by taking the supremum
of the norms of the paired functionals. -/
private theorem tensor_diagonal_seminorm {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [ContinuousSMul ℂ X] [FirstCountableTopology X] [PolynormableSpace ℂ X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [ContinuousSMul ℂ Y]
    [PolynormableSpace ℂ Y]
    (hY : ∀ p : Seminorm ℂ Y, (∀ B : Set Y, IsVonNBounded ℂ B → BddAbove (p '' B)) → Continuous p)
    (v : ℕ → StrongDual ℂ X) (w : ℕ → StrongDual ℂ Y)
    (hvan : ∀ B : Set Y, IsVonNBounded ℂ B → ∃ N, ∀ n ≥ N, ∀ y ∈ B, w n y = 0) :
    ∃ p : Seminorm ℂ (InductiveTensor X Y), Continuous p ∧
      ∀ n x y, ‖v n x‖ * ‖w n y‖ ≤ p (x ⊗ₜ[ℂ] y) := by
  let t (n : ℕ) := tensorDualForm (v n) (w n)
  let q (n : ℕ) := (normSeminorm ℂ ℂ).comp (t n)
  have hz (z : X ⊗[ℂ] Y) : ∃ N, ∀ n ≥ N, t n z = 0 := by
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
      obtain ⟨N, hN⟩ := hvan {y} (isVonNBounded_singleton _)
      exact ⟨N, fun n hn ↦ by
        change tensorDualForm (v n) (w n) _ = 0
        rw [tensorDualForm_tmul, hN n hn y rfl, mul_zero]⟩
    | add a b ha hb =>
      obtain ⟨i, hi⟩ := ha
      obtain ⟨j, hj⟩ := hb
      exact ⟨max i j, fun n hn ↦ by rw [map_add, hi n ((le_max_left ..).trans hn),
        hj n ((le_max_right ..).trans hn), zero_add]⟩
  have hb : BddAbove (range q) := Seminorm.bddAbove_range_iff.mpr fun z ↦ by
    obtain ⟨N, hN⟩ := hz z
    refine ⟨∑ j ∈ Finset.range N, q j z, forall_mem_range.mpr fun n ↦ ?_⟩
    by_cases h : n < N
    · exact Finset.single_le_sum (fun j _ ↦ apply_nonneg (q j) z) (Finset.mem_range.mpr h)
    · change ‖t n z‖ ≤ _
      rw [hN n (Nat.le_of_not_gt h), norm_zero]
      exact Finset.sum_nonneg fun j _ ↦ apply_nonneg (q j) z
  let p := ⨆ n, q n
  have hrect (A : Set X) (B : Set Y) (hA : IsVonNBounded ℂ A) (hB : IsVonNBounded ℂ B) :
      ∃ C, ∀ x ∈ A, ∀ y ∈ B, p (x ⊗ₜ[ℂ] y) ≤ C := by
    choose a ha using fun n ↦ (NormedSpace.image_isVonNBounded_iff ℂ).mp (hA.image (v n))
    choose b hb' using fun n ↦ (NormedSpace.image_isVonNBounded_iff ℂ).mp (hB.image (w n))
    obtain ⟨N, hN⟩ := hvan B hB
    let c (n : ℕ) := |a n| * |b n|
    have hc (n : ℕ) : 0 ≤ c n := mul_nonneg (abs_nonneg _) (abs_nonneg _)
    refine ⟨∑ n ∈ Finset.range N, c n, fun x hx y hy ↦ ?_⟩
    rw [show p = ⨆ n, q n from rfl, Seminorm.iSup_apply hb]
    apply ciSup_le
    intro n
    change ‖tensorDualForm (v n) (w n) (x ⊗ₜ[ℂ] y)‖ ≤ _
    rw [tensorDualForm_tmul, norm_mul]
    by_cases hn : n < N
    · exact (mul_le_mul ((ha n x hx).trans (le_abs_self _)) ((hb' n y hy).trans (le_abs_self _))
        (norm_nonneg _) (abs_nonneg _)).trans (Finset.single_le_sum (fun j _ ↦ hc j) (Finset.mem_range.mpr hn))
    · rw [hN n (Nat.le_of_not_gt hn) y hy, norm_zero, mul_zero]
      exact Finset.sum_nonneg fun j _ ↦ hc j
  have hleft (y : Y) : Continuous (p.comp ((TensorProduct.mk ℂ X Y).flip y)) := by
    apply continuous_seminorm_of_bounded_images
    intro A hA
    obtain ⟨C, hC⟩ := hrect A {y} hA (isVonNBounded_singleton _)
    exact ⟨C, forall_mem_image.mpr fun x hx ↦ hC x hx y rfl⟩
  have hright (x : X) : Continuous (p.comp (TensorProduct.mk ℂ X Y x)) := by
    apply hY
    intro B hB
    obtain ⟨C, hC⟩ := hrect {x} B (isVonNBounded_singleton _) hB
    exact ⟨C, forall_mem_image.mpr fun y hy ↦ hC x rfl y hy⟩
  let ps := fun r : {r : Seminorm ℂ (X ⊗[ℂ] Y) //
    (∀ x : X, Continuous (fun y : Y ↦ r (x ⊗ₜ[ℂ] y))) ∧
    (∀ y : Y, Continuous (fun x : X ↦ r (x ⊗ₜ[ℂ] y)))} ↦ r.val
  refine ⟨p, (withGeneratingSeminorms_spec _ ps).continuous_seminorm ⟨p, hright, hleft⟩, fun n x y ↦ ?_⟩
  have he : q n (x ⊗ₜ[ℂ] y) = ‖v n x‖ * ‖w n y‖ := norm_mul _ _
  exact he.ge.trans ((le_ciSup hb n : q n ≤ p) (x ⊗ₜ[ℂ] y))

omit hSC hm hInt hne hτ in
/-- Joint continuity on pure tensors would bound a functional that was chosen to
be unbounded on a member of the neighborhood basis of the first factor. -/
private theorem tensor_diagonal_not_homeomorph {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [ContinuousSMul ℂ X] [FirstCountableTopology X] [PolynormableSpace ℂ X] [T2Space X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
    [ContinuousSMul ℂ Y] [PolynormableSpace ℂ Y] [T2Space Y]
    (hX : ∀ U ∈ 𝓝 (0 : X), ¬ IsVonNBounded ℂ U)
    (hY : ∀ p : Seminorm ℂ Y, (∀ B : Set Y, IsVonNBounded ℂ B → BddAbove (p '' B)) → Continuous p)
    (w : ℕ → StrongDual ℂ Y) (hw : ∀ n, ∃ y, w n y ≠ 0)
    (hvan : ∀ B : Set Y, IsVonNBounded ℂ B → ∃ N, ∀ n ≥ N, ∀ y ∈ B, w n y = 0) :
    ¬ IsHomeomorph (@Completion.map (InductiveTensor X Y) _ (ProjectiveTensor X Y) _ id) := by
  intro h
  obtain ⟨U, hU⟩ := (𝓝 (0 : X)).exists_antitone_basis
  have hv (n : ℕ) : ∃ v : StrongDual ℂ X, ¬IsBounded (v '' U n) := by
    simpa only [isVonNBounded_iff_dual_image, not_forall] using hX (U n) (hU.mem n)
  choose v hv using hv
  obtain ⟨p, hp, hle⟩ := tensor_diagonal_seminorm hY v w hvan
  let A := InductiveTensor X Y
  let B := ProjectiveTensor X Y
  let C : A →L[ℂ] B := ⟨LinearMap.id, continuous_inductiveTensor_to_projectiveTensor⟩
  have ht : @Continuous (X × Y) B _ _ (fun z ↦ z.1 ⊗ₜ[ℂ] z.2) :=
    (continuous_projectiveTensor_iff (LinearMap.id : B →ₗ[ℂ] B)).mp continuous_id
  have ht' : @Continuous (X × Y) A _ _ (fun z ↦ z.1 ⊗ₜ[ℂ] z.2) := by
    apply (Completion.isDenseInducing_coe (α := A)).isInducing.continuous_iff.mpr
    apply h.isInducing.continuous_iff.mpr
    exact ((Completion.continuous_coe B).comp ht).congr fun z ↦ (C.completion_apply_coe _).symm
  have hz : p ((0 : X) ⊗ₜ[ℂ] (0 : Y)) < 1 := by
    rw [TensorProduct.zero_tmul]
    exact (map_zero p).trans_lt zero_lt_one
  have hsmall := (hp.comp ht').continuousAt (x := ((0 : X), (0 : Y))) |>.preimage_mem_nhds
    (Iio_mem_nhds hz)
  obtain ⟨O, hO, V, hV, hOV⟩ := mem_nhds_prod_iff.mp hsmall
  obtain ⟨n, _, hn⟩ := hU.1.mem_iff.mp hO
  obtain ⟨y, hy⟩ := hw n
  obtain ⟨c, hc, hcV⟩ : ∃ c : ℂ, c ≠ 0 ∧ c • y ∈ V := by
    have he := (Filter.tendsto_id.smul_const y : Filter.Tendsto (fun c : ℂ ↦ c • y) (𝓝 0) (𝓝 ((0 : ℂ) • y)))
    rw [zero_smul] at he
    exact ((eventually_mem_nhdsWithin (s := ({0}ᶜ : Set ℂ)) (a := 0)).and
      (he.mono_left nhdsWithin_le_nhds hV)).exists
  have hnz : 0 < ‖w n (c • y)‖ := norm_pos_iff.mpr (by
    rw [map_smul, smul_eq_mul]
    exact mul_ne_zero hc hy)
  apply hv n
  refine isBounded_iff_forall_norm_le.mpr ⟨1 / ‖w n (c • y)‖, forall_mem_image.mpr fun x hx ↦ ?_⟩
  exact (le_div_iff₀ hnz).mpr ((hle n x (c • y)).trans
    (show p (x ⊗ₜ[ℂ] (c • y)) < 1 from @hOV (x, c • y) ⟨hn hx, hcV⟩).le)

omit hSC hm hτ in
/-- Translates of a bump with disjoint supports give an infinite independent family
of scalar decay profiles. Montel compactness therefore rules out a bounded neighborhood. -/
private theorem decay_profile_unbounded_nhds (U : Set P) (hU : U ∈ 𝓝 0) :
    ¬ IsVonNBounded ℂ U := by
  intro hB
  let : MetrizableSpace P := (positiveRealExponentialDecay_frechet I hInt hne).choose_spec.2.1
  let : MontelSpace ℂ P := (positiveRealExponentialDecay_montel I hInt hne).2
  have hc := MontelSpace.isCompact_of_isClosed_of_isVonNBounded ℂ isClosed_closure hB.closure
  let : LocallyCompactSpace P := hc.locallyCompactSpace_of_mem_nhds_of_addGroup
    (Filter.mem_of_superset hU subset_closure)
  let : FiniteDimensional ℂ P := FiniteDimensional.of_locallyCompactSpace ℂ
  let b (n : ℕ) : ContDiffBump (n : ℝ) := ⟨1/2, 1, by norm_num, by norm_num⟩
  let f (n : ℕ) : P := ⟨fun x ↦ ((b n x : ℝ) : ℂ), mem_logExponentialDecaySubmodule_of_hasCompactSupport I
    ((b n).hasCompactSupport.comp_left (by simp : (Complex.ofReal 0) = 0))
    (Complex.ofRealCLM.contDiff.comp (b n).contDiff)⟩
  let ev (n : ℕ) : P →ₗ[ℂ] ℂ := (LinearMap.proj (n : ℝ)).comp (logExponentialDecaySubmodule I).subtype
  have hlin : LinearIndependent ℂ f := LinearIndependent.of_pairwise_dual_eq_zero_one f ev (by
    intro i j hij
    have hd : 1 ≤ dist (i : ℝ) (j : ℝ) := by
      rw [Real.dist_eq]
      rcases lt_or_gt_of_ne hij with h | h
      · rw [abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast h.le))]
        have hij : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
        linarith
      · rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast h.le))]
        have hij : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
        linarith
    change ((b j (i : ℝ) : ℝ) : ℂ) = 0
    exact_mod_cast (b j).zero_of_le_dist hd) (fun i ↦ by
      change ((b i (i : ℝ) : ℝ) : ℂ) = 1
      rw [(b i).one_of_mem_closedBall (Metric.mem_closedBall_self (b i).rIn_pos.le), Complex.ofReal_one])
  let : Finite ℕ := hlin.finite
  exact _root_.not_finite ℕ

omit hSC hm hInt hne hτ in
/-- On a compact kernel with non-compactly-generated dual, evaluation differences
detect nontrivial points while vanishing eventually on every bounded Schwartz family. -/
private theorem compact_kernel_differences {A : Type*} [CommGroup A] [TopologicalSpace A]
    [IsTopologicalGroup A] [T2Space A] [CompactSpace A] [SecondCountableTopology A]
    (h : ¬IsCompactlyGeneratedGroup (PontryaginDual A)) :
    ∃ w : ℕ → StrongDual ℂ (SchwartzBruhat A), (∀ n, ∃ f, w n f ≠ 0) ∧
      ∀ B : Set (SchwartzBruhat A), IsVonNBounded ℂ B → ∃ N, ∀ n ≥ N, ∀ f ∈ B, w n f = 0 := by
  refine (exists_antitone_goodCompact (G := A)).elim fun k hk ↦ ?_
  have hanti := hk.1
  have hcof := hk.2
  have hnontriv (n : ℕ) : (k n).val ≠ ⊥ := by
    intro he
    have hg : IsBruhatGoodSubgroup (k n).val := ⟨(k n).property.1.isClosed,
      isOpen_lcaAnnihilator _ (k n).property.1, (k n).property.2⟩
    exact h (isCompactlyGeneratedGroup_dual_of_isLocallyEuclidean
      (isBruhatGoodSubgroup_bot_iff.mp ((congrArg IsBruhatGoodSubgroup he).mp hg)))
  choose u hu using fun n ↦ Subgroup.ne_bot_iff_exists_ne_one.mp (hnontriv n)
  let ev (a : A) : StrongDual ℂ (SchwartzBruhat A) :=
    ⟨(LinearMap.proj a).comp (schwartzBruhatSubmodule A).subtype, continuous_schwartzBruhat_eval a⟩
  refine ⟨fun n ↦ ev (u n).val - ev 1, fun n ↦ ?_, fun B hB ↦ ?_⟩
  · refine (schwartzBruhat_exists_test (1 : A) (u n).val).elim fun f hf ↦ ?_
    exact ⟨f, sub_ne_zero.mpr (hf.2 (fun he ↦ hu n (Subtype.ext he)))⟩
  · refine (schwartzBruhat_bounded_image_stage hB).elim fun b hb ↦
      hb.elim fun e he ↦ he.elim fun C hC ↦ ?_
    let k₀ := OrderDual.ofDual b.val.2
    refine (hcof ⟨k₀, isCompact_of_isBruhatGoodSubgroup_aux k₀ b.property.2.2.1,
      b.property.2.2.1.2.2⟩).elim fun N hN ↦ ?_
    refine ⟨N, fun n hn f hf ↦ ?_⟩
    refine (hC.2.ge hf).elim fun s hs ↦ ?_
    refine (congrArg (fun z : SchwartzBruhat A ↦ (ev (u n).val - ev 1) z = 0) hs.2).mp ?_
    refine sub_eq_zero.mpr ?_
    let g := schwartzBruhatStageRealization b e s
    exact (congrArg g (mul_one (u n).val).symm).trans
      (stage_realization_mul_kernel b e s (hN (hanti hn (u n).property)) 1)

/-- Paper: Remark D.3.3.11, p. 811. The comparison between the completed
tensor products is a topological isomorphism exactly when the norm-one dual
is compactly generated. -/
theorem modulatedExponentialDecay_tensor_comparison_homeomorph_iff :
    IsHomeomorph compareTensors ↔ IsCompactlyGeneratedGroup (PontryaginDual K) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let : SecondCountableTopology K := TopologicalSpace.Subtype.secondCountableTopology (K : Set G)
  let : T2Space (SchwartzBruhat K) := schwartzBruhat_t2
  have hP := positiveRealExponentialDecay_frechet I hInt hne
  let : MetrizableSpace P := hP.choose_spec.2.1
  constructor
  · intro h
    by_contra hK
    refine (compact_kernel_differences hK).elim fun w hw ↦ ?_
    exact tensor_diagonal_not_homeomorph (X := P) (Y := SchwartzBruhat K) (decay_profile_unbounded_nhds I hInt hne)
      (schwartzBruhat_bornological (G := K)) w hw.1 hw.2 h
  · intro hK
    have hQ := schwartzBruhat_frechet_of_elementary (Q := K) isCompactlyGeneratedGroup_of_compact
      (isLocallyEuclidean_of_isCompactlyGeneratedGroup_dual hK)
    exact completedInductiveTensor_to_projectiveTensor_of_frechet hP hQ

end BoundedSets

section Isotypes

-- TODO(paper-gap): The proof on p. 812 invokes a closed embedding for the
-- product of twists, although the topology is defined by the inductive stages
-- and Theorem D.3.3.7(4) identifies it with the projective topology for compact I.

variable [hSC : SecondCountableTopology G]
variable (hm : IsModulation m) (hms : Surjective m) (hInt : OrdConnected I) (hne : I.Nonempty)

/-- Translating a weighted profile introduces just the constant weight at the translating element. -/
private theorem decay_weight_translate (g : G) (a : I) (f : modulatedExponentialDecaySubmodule m I) :
    modulationWeight m a (fun x ↦ f.val (g⁻¹ * x)) =
      (((((m g).val : ℝ) ^ a.val : ℝ) : ℂ) • schwartzBruhatTranslate g (modulatedExponentialDecayTwist m I a f)).val := by
  let w (x : G) : ℂ := (((m x).val : ℝ) ^ a.val : ℝ)
  funext x
  have hx : (m x).val = (m g).val * (m (g⁻¹ * x)).val := by rw [← Units.val_mul, ← map_mul, mul_inv_cancel_left]
  have hw : w x = w g * w (g⁻¹ * x) := by
    unfold w
    rw [hx, NNReal.coe_mul, Real.mul_rpow (NNReal.coe_nonneg _) (NNReal.coe_nonneg _), Complex.ofReal_mul]
  change w x * f.val (g⁻¹ * x) = w g * (w (g⁻¹ * x) * f.val (g⁻¹ * x))
  rw [hw, mul_assoc]

private def decayTranslateLinear (g : G) : modulatedExponentialDecaySubmodule m I →ₗ[ℂ] modulatedExponentialDecaySubmodule m I where
  toFun f := ⟨fun x ↦ f.val (g⁻¹ * x), (Submodule.mem_iInf _).mpr fun a ↦ Eq.mpr
    (congrArg (fun v : G → ℂ ↦ v ∈ schwartzBruhatSubmodule G) (decay_weight_translate m I g a f))
    (Submodule.smul_mem _ _ (schwartzBruhatTranslate g (modulatedExponentialDecayTwist m I a f)).property)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem continuous_decayTranslate_stage (k : GoodCompact) :
    @Continuous (G × ModulatedExponentialDecayStage m I k) E _ _ (fun p ↦
      (decayTranslateLinear m I p.1 (modulatedExponentialDecayStageInclusion m I k p.2) : E)) := by
  let n := quotientModulation m k.val k.property.1
  let X := ModulatedExponentialDecayStage m I k
  let : IsClosed (k.val : Set G) := k.property.1.isClosed
  let : SecondCountableTopology (G ⧸ k.val) := QuotientGroup.isOpenQuotientMap_mk.secondCountableTopology
  let act (v : G × X) : X := decayTranslateLinear n I (v.1 : G ⧸ k.val) v.2
  have hind := modulatedExponentialDecayStage_twists_isInducing m I k
  have hc : Continuous act := by
    apply hind.continuous_iff.mpr
    apply continuous_pi
    intro a
    let tw (f : X) := modulatedExponentialDecayTwist n I a f
    have htw : Continuous tw := (continuous_apply a).comp hind.continuous
    have hq : Continuous (fun p : G × X ↦ (p.1 : G ⧸ k.val)) := QuotientGroup.continuous_mk.comp continuous_fst
    have hw : Continuous (fun p : G × X ↦ (((((m p.1).val : ℝ) ^ a.val : ℝ) : ℂ))) :=
      Complex.continuous_ofReal.comp (((NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)).rpow
        continuous_const fun g ↦ Or.inl (NNReal.coe_ne_zero.mpr (m g).ne_zero)).comp continuous_fst)
    have ht := schwartzBruhatTranslate_continuous (G := G ⧸ k.val)
    exact (hw.smul (ht.comp (hq.prodMk (htw.comp continuous_snd)))).congr fun p ↦
      Subtype.ext (decay_weight_translate n I (p.1 : G ⧸ k.val) a p.2).symm
  let i : X →ₗ[ℂ] E := modulatedExponentialDecayStageInclusion m I k
  have hi : Continuous i := (withGeneratingSeminorms_spec _ _).continuous_of_continuous_comp i fun p ↦ p.property k
  refine (hi.comp hc).congr fun p ↦ Subtype.ext (funext fun x ↦ ?_)
  exact congrArg p.2.val (by change (p.1 : G ⧸ k.val)⁻¹ * (x : G ⧸ k.val) = ((p.1⁻¹ * x : G) : G ⧸ k.val); rfl)

open scoped ComplexOrder in
private theorem continuous_action_of_final_stages {A X : Type*} [TopologicalSpace A] [LocallyCompactSpace A]
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [IsTopologicalAddGroup X] [PolynormableSpace ℂ X]
    {J : Type*} {Y : J → Type*} [∀ j, AddCommGroup (Y j)] [∀ j, Module ℂ (Y j)] [∀ j, TopologicalSpace (Y j)]
    (i : ∀ j, Y j →ₗ[ℂ] X) (cov : ∀ x, ∃ j, x ∈ (i j).range)
    (hf : (inferInstance : TopologicalSpace X) = locallyConvexFinalTopology i) (L : A → X →ₗ[ℂ] X)
    (hs : ∀ j, Continuous (fun p : A × Y j ↦ L p.1 (i j p.2))) : Continuous (fun p : A × X ↦ L p.1 p.2) := by
  let : PolynormableSpace ℂ C(A, X) := polynormableSpace_continuousMap ℂ A X
  have ho (x : X) : Continuous fun g ↦ L g x := by
    obtain ⟨j, y, rfl⟩ := cov x
    exact (hs j).comp (continuous_id.prodMk continuous_const)
  let T : X →ₗ[ℂ] C(A, X) :=
    { toFun := fun x ↦ ⟨_, ho x⟩
      map_add' := fun x y ↦ ContinuousMap.ext fun g ↦ (L g).map_add x y
      map_smul' := fun c x ↦ ContinuousMap.ext fun g ↦ (L g).map_smul c x }
  have hT : Continuous T := by
    have hps : WithSeminorms (Subtype.val : {q : Seminorm ℂ X // ∀ j, Continuous (q ∘ i j)} → _) := ⟨hf⟩
    refine (PolynormableSpace.withSeminorms ℂ C(A, X)).continuous_of_continuous_comp T fun p ↦ ?_
    exact hps.continuous_seminorm ⟨p.val.comp T, fun j ↦ p.property.comp
      (ContinuousMap.continuous_of_continuous_uncurry (fun y ↦ T (i j y)) ((hs j).comp continuous_swap))⟩
  exact continuous_eval.comp ((hT.comp continuous_snd).prodMk continuous_fst)

include hSC hm hms hInt hne in
/-- Paper: Proposition D.3.3.12, p. 811. Left translation defines a jointly
continuous action of G by continuous linear operators on the decay space. -/
theorem exists_modulatedExponentialDecay_translationAction :
    ∃ ρ : G →* (E →L[ℂ] E),
      (∀ g f x, (ρ g f).val x = f.val (g⁻¹ * x)) ∧
      Continuous (fun p : G × E ↦ ρ p.1 p.2) := by
  let L (g : G) : E →ₗ[ℂ] E := decayTranslateLinear m I g
  let i (k : GoodCompact) : ModulatedExponentialDecayStage m I k →ₗ[ℂ] E := modulatedExponentialDecayStageInclusion m I k
  have hfinal : (inferInstance : TopologicalSpace E) = locallyConvexFinalTopology i := rfl
  have hc := @continuous_action_of_final_stages G E inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance GoodCompact (ModulatedExponentialDecayStage m I)
    (fun _ ↦ inferInstance) (fun _ ↦ inferInstance) (fun _ ↦ inferInstance) i
    (modulatedExponentialDecay_exists_stage m I hm hms hInt hne) hfinal L (continuous_decayTranslate_stage m I)
  let ρ : G →* (E →L[ℂ] E) :=
    { toFun := fun g ↦ ⟨L g, hc.comp (continuous_const.prodMk continuous_id)⟩
      map_one' := ContinuousLinearMap.ext fun f ↦ Subtype.ext (funext fun x ↦ congrArg f.val (by simp))
      map_mul' := fun g h ↦ ContinuousLinearMap.ext fun f ↦ Subtype.ext (funext fun x ↦
        congrArg f.val (by simp [mul_assoc])) }
  exact ⟨ρ, fun _ _ _ ↦ rfl, hc⟩

variable [MeasurableSpace G] [BorelSpace G]
variable (μ₁ : Measure m.toMonoidHom.ker) [μ₁.IsHaarMeasure]
variable (ρ : G →* (ModulatedExponentialDecay m I →L[ℂ] ModulatedExponentialDecay m I))
variable (hρ : ∀ g f x, (ρ g f).val x = f.val (g⁻¹ * x))
variable (ω : PontryaginDual m.toMonoidHom.ker)

local notation "Eω" => actionIsotype (ρ.comp (Subgroup.subtype K)) ω
local notation "Φ" => schwartzBruhatIsotypicProjector m hm μ₁ ω

include hm hms hInt hne hρ

omit hm hms hInt hne hρ in
private theorem mem_translation_isotype_iff_coordinates {A X : Type*} [CommGroup A] [TopologicalSpace A]
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [ContinuousAdd X]
    (k : Subgroup A) (s : A →* (X →L[ℂ] X)) (χ : PontryaginDual k)
    (ev : X → A → ℂ) (hi : Injective ev) (ha : ∀ g f x, ev (s g f) x = ev f (g⁻¹ * x))
    (hs : ∀ (z : ℂ) f x, ev (z • f) x = z * ev f x) (f : X) :
    f ∈ actionIsotype (s.comp k.subtype) χ ↔ ∀ (u : k) x, ev f ((u : A)⁻¹ * x) = (χ u : ℂ) * ev f x := by
  rw [mem_actionIsotype]
  refine forall_congr' fun u ↦ ?_
  have he : ∀ (x : A), ev (s (u : A) f) x = ev f ((u : A)⁻¹ * x) := ha _ _
  constructor
  · intro h x
    exact (he x).symm.trans ((congrFun (congrArg ev h) x).trans (hs _ _ _))
  · intro h
    exact hi (funext fun x ↦ (he x).trans ((h x).trans (hs _ _ _).symm))

/-- The kernel preserves the modulation, so twisting commutes with translation
by a kernel element and detects the same character subspace. -/
private theorem decay_twist_mem_isotype (a : I) (f : E) :
    modulatedExponentialDecayTwist m I a f ∈ actionIsotype
      ((schwartzBruhatTranslationAction (G := G)).comp (Subgroup.subtype K)) ω ↔ f ∈ Eω := by
  let S := SchwartzBruhat G
  let tw := modulatedExponentialDecayTwist m I a f
  let w (x : G) : ℂ := (((m x).val : ℝ) ^ a.val : ℝ)
  have htw (x : G) : tw.val x = w x * f.val x := rfl
  have hS := mem_translation_isotype_iff_coordinates K (schwartzBruhatTranslationAction (G := G)) ω
    (fun z : S ↦ z.val) Subtype.val_injective (fun g z x ↦ schwartzBruhatTranslationAction_apply g x z)
    (fun _ _ _ ↦ rfl) tw
  have hE := mem_translation_isotype_iff_coordinates K ρ ω (fun z : E ↦ z.val)
    Subtype.val_injective hρ (fun _ _ _ ↦ rfl) f
  refine hS.trans (Iff.trans ?_ hE.symm)
  refine forall_congr' fun u ↦ forall_congr' fun x ↦ ?_
  have hu : m (u : G) = 1 := u.property
  have hw : w ((u : G)⁻¹ * x) = w x := by
    unfold w
    rw [map_mul, map_inv, hu, inv_one, one_mul]
  have hn : w x ≠ 0 := Complex.ofReal_ne_zero.mpr
    (Real.rpow_pos_of_pos (NNReal.coe_pos.mpr (Units.zero_lt (m x))) _).ne'
  change tw.val _ = _ * tw.val _ ↔ _
  rw [htw, htw, hw, mul_left_comm]
  exact mul_right_inj' hn

/-- Paper: Proposition D.3.3.12, p. 812. Twisting restricts to a continuous
linear map between the isotypes for the same compact-kernel character. -/
theorem modulatedExponentialDecay_isotype_twist (a : I) :
    let Sω := actionIsotype
      ((schwartzBruhatTranslationAction (G := G)).comp (Subgroup.subtype K)) ω
    ∃ T : Eω →L[ℂ] Sω,
      ∀ f, (T f : SchwartzBruhat G) = modulatedExponentialDecayTwist m I a (f : E) := by
  intro Sω
  let L : E →L[ℂ] SchwartzBruhat G := ⟨modulatedExponentialDecayTwist m I a, continuous_decay_twist m I a⟩
  refine ⟨L.restrict (fun f hf ↦ ?_), fun _ ↦ rfl⟩
  exact (decay_twist_mem_isotype m I hm hms hInt hne ρ hρ ω a f).mpr hf

omit hms hInt hne hρ in
/-- The kernel leaves the weight constant on each orbit, so it factors out of
the normalized projector integral. -/
private theorem decay_projector_weighted_formula (a : I) (f : E) (x : G) :
    Φ (modulatedExponentialDecayTwist m I a f) x =
      ((((m x).val : ℝ) ^ a.val : ℝ) : ℂ) * ((μ₁.real univ)⁻¹ •
        ∫ u : K, star (ω u : ℂ) * f.val ((u : G)⁻¹ * x) ∂μ₁) := by
  let w : ℂ := (((m x).val : ℝ) ^ a.val : ℝ)
  let v := modulatedExponentialDecayTwist m I a f
  have he (u : K) : star (ω u : ℂ) * v ((u : G)⁻¹ * x) =
      w * (star (ω u : ℂ) * f.val ((u : G)⁻¹ * x)) := by
    have hu : m (u : G) = 1 := u.property
    change _ * (((((m ((u : G)⁻¹ * x)).val : ℝ) ^ a.val : ℝ) : ℂ) * _) = _
    rw [map_mul, map_inv, hu, inv_one, one_mul, mul_left_comm]
    rfl
  refine (schwartzBruhatIsotypicProjector_apply m hm μ₁ ω v x).2.trans ?_
  rw [integral_congr_ae (Filter.Eventually.of_forall he), integral_const_mul, Complex.real_smul, Complex.real_smul]
  exact mul_left_comm _ _ _

/-- Paper: Proposition D.3.3.12, p. 812. The passage to the given isotype
is the unique linear map that commutes with every twist and its ordinary
Schwartz–Bruhat projector.
Deviation: The commuting square is checked in the ambient Schwartz–Bruhat space. -/
theorem existsUnique_modulatedExponentialDecay_isotypicProjector :
    ∃! Q : E →ₗ[ℂ] Eω, ∀ (f : E) (a : I),
      modulatedExponentialDecayTwist m I a (Q f : E) =
        Φ (modulatedExponentialDecayTwist m I a f) := by
  let a : I := ⟨hne.choose, hne.choose_spec⟩
  let w (b : I) (x : G) : ℂ := (((m x).val : ℝ) ^ b.val : ℝ)
  let A (f : E) (x : G) : ℂ := (μ₁.real univ)⁻¹ • ∫ u : K, star (ω u : ℂ) * f.val ((u : G)⁻¹ * x) ∂μ₁
  let proj (b : I) : E →ₗ[ℂ] SchwartzBruhat G := (Φ).toLinearMap.comp (modulatedExponentialDecayTwist m I b)
  let L : E →ₗ[ℂ] (G → ℂ) := (LinearMap.mulLeft ℂ fun x : G ↦ (w a x)⁻¹).comp
    ((schwartzBruhatSubmodule G).subtype.comp (proj a))
  have hpr (b : I) (f : E) (x : G) : (proj b f).val x = w b x * A f x :=
    decay_projector_weighted_formula m I hm μ₁ ω b f x
  have hL (f : E) (x : G) : L f x = A f x := by
    change (w a x)⁻¹ * (proj a f).val x = _
    rw [hpr, inv_mul_cancel_left₀]
    exact Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (NNReal.coe_pos.mpr (Units.zero_lt (m x))) _).ne'
  have hmatch (f : E) (b : I) : modulationWeight m b (L f) = (proj b f).val := funext fun x ↦
    (congrArg (w b x * ·) (hL f x)).trans (hpr b f x).symm
  let V : E →ₗ[ℂ] E := L.codRestrict (modulatedExponentialDecaySubmodule m I) fun f ↦ by
    apply (Submodule.mem_iInf _).mpr
    intro b
    exact Eq.mpr (congrArg (fun v : G → ℂ ↦ v ∈ schwartzBruhatSubmodule G) (hmatch f b)) (proj b f).property
  have hw (f : E) (b : I) : modulatedExponentialDecayTwist m I b (V f) = proj b f := Subtype.ext (hmatch f b)
  let Sω := actionIsotype ((schwartzBruhatTranslationAction (G := G)).comp (Subgroup.subtype K)) ω
  have hΦ := (schwartzBruhat_modulation_source_projector m hm μ₁ ω).2.1
  let Q := V.codRestrict Eω fun f ↦ (decay_twist_mem_isotype m I hm hms hInt hne ρ hρ ω a (V f)).mp
    (Eq.mpr (congrArg (fun v : SchwartzBruhat G ↦ v ∈ Sω) (hw f a)) (hΦ _))
  refine ⟨Q, hw, fun Q' hQ' ↦ LinearMap.ext fun f ↦ Subtype.ext ?_⟩
  exact decay_twist_injective m I a ((hQ' f a).trans (hw f a).symm)

variable (Q : ModulatedExponentialDecay m I →ₗ[ℂ]
  actionIsotype (ρ.comp m.toMonoidHom.ker.subtype) ω)
variable (hQ : ∀ (f : ModulatedExponentialDecay m I) (a : I),
  modulatedExponentialDecayTwist m I a (Q f : ModulatedExponentialDecay m I) =
    schwartzBruhatIsotypicProjector m hm μ₁ ω (modulatedExponentialDecayTwist m I a f))

include hQ

/-- Paper: Proposition D.3.3.12, p. 812. The passage to the isotype is continuous. -/
theorem modulatedExponentialDecay_isotypicProjector_continuous : Continuous Q := by
  let σ := hm.exists_section.choose
  have hσ := hm.exists_section.choose_spec
  let j : ℝ≥0ˣ →ₜ* m.toMonoidHom.range :=
    { toFun := fun t ↦ ⟨t, hms t⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      continuous_toFun := continuous_id.subtype_mk _ }
  let τ := σ.comp j
  have hτ : RightInverse τ m := fun t ↦ hσ (j t)
  let L : E →ₗ[ℂ] E := (actionIsotype (ρ.comp (Subgroup.subtype K)) ω).subtype.comp Q
  have hL (B : Set E) (hB : IsVonNBounded ℂ B) : IsVonNBounded ℂ (L '' B) := by
    apply (modulatedExponentialDecay_bounded_iff_twists m I hm hInt hne τ hτ _).mpr
    intro a
    have hb := (modulatedExponentialDecay_bounded_iff_twists m I hm hInt hne τ hτ B).mp hB a
    apply (hb.image Φ).subset
    rintro _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    exact ⟨_, mem_image_of_mem _ hf, (hQ f a).symm⟩
  apply IsInducing.subtypeVal.continuous_iff.mpr
  let ps := PolynormableSpace.withSeminorms ℂ E
  apply ps.continuous_of_continuous_comp L
  intro p
  apply modulatedExponentialDecay_bornological m I hm hInt hne τ hτ (p.val.comp L)
  intro B hB
  refine (ps.isVonNBounded_iff_seminorm_bddAbove.mp (hL B hB) p).elim fun r hr ↦ ?_
  exact ⟨r, fun z hz ↦ hz.elim fun v hv ↦
    (congrArg (fun t : ℝ ↦ t ≤ r) hv.2).mp (hr (mem_image_of_mem p.val (mem_image_of_mem L hv.1)))⟩

/-- Paper: Proposition D.3.3.12, p. 812. The passage to the isotype is a
retraction of its inclusion, hence a surjective projector. -/
theorem modulatedExponentialDecay_isotypicProjector_retract (f : Eω) : Q (f : E) = f := by
  let a : I := ⟨hne.choose, hne.choose_spec⟩
  have ht := modulatedExponentialDecay_isotype_twist m I hm hms hInt hne ρ hρ ω a
  have hmem := (ht.choose f).property
  have he := ht.choose_spec f
  apply Subtype.ext
  apply decay_twist_injective m I a
  exact (hQ f a).trans (schwartzBruhatIsotypicProjector_apply_isotype m hm μ₁ ω _
    (Eq.mp (congrArg (fun v : SchwartzBruhat G ↦ v ∈ actionIsotype
      ((schwartzBruhatTranslationAction (G := G)).comp (Subgroup.subtype K)) ω) he) hmem))

omit hm hms hInt hne hρ hQ in
/-- A linear surjection with a continuous linear section is open by translating the section. -/
private theorem isOpenMap_of_linear_section {X : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] (S : Submodule ℂ X)
    (q : X →ₗ[ℂ] S) (hs : ∀ y : S, q (y : X) = y) : IsOpenMap q := by
  apply IsOpenMap.of_sections
  intro x
  refine ⟨fun y ↦ x + ((y : X) - (q x : X)), (continuous_const.add (continuous_subtype_val.sub continuous_const)).continuousAt,
    by simp, fun y ↦ ?_⟩
  rw [map_add, map_sub, hs, hs, add_sub_cancel]

/-- Paper: Proposition D.3.3.12, p. 812. The passage to the isotype is open
for the subspace topology on the isotype. -/
theorem modulatedExponentialDecay_isotypicProjector_open : IsOpenMap Q := by
  exact isOpenMap_of_linear_section (X := E) (actionIsotype (ρ.comp (Subgroup.subtype K)) ω) Q
    (modulatedExponentialDecay_isotypicProjector_retract m I hm hms hInt hne μ₁ ρ hρ ω Q hQ)

end Isotypes

section FourierMellin

variable [hSC : SecondCountableTopology G]
variable (hm : IsModulation m) (hInt : OrdConnected I) (hne : I.Nonempty)
variable (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ m)

local notation "ΩI" => relativeVerticalStrip m.toMonoidHom (And.left hm) (And.right hm) I

variable [MeasurableSpace G] [hBorel : BorelSpace G]
variable (μ : Measure G) [hHaar : μ.IsHaarMeasure]
variable (hOpen : IsOpen I) (hms : Surjective m)

/-- Paper: Theorem D.3.3.13, p. 812. The Fourier–Mellin integral
uses the quasi-character itself as the multiplier.
Deviation: The formula takes an unbundled function and is extended by zero
outside the relative strip. The convergence statement uses the decay space. -/
def modulatedFourierMellin (f : G → ℂ) (c : QuasiCharacter G) : ℂ :=
  Set.indicator ΩI (fun c ↦ ∫ g, f g * c g ∂μ) c

/-- Paper: Theorem D.3.3.13, p. 812. At the trivial quasi-character the
Fourier–Mellin integral gives the integral of the original function.
Deviation: This is the sanity check at abscissa zero. -/
theorem modulatedFourierMellin_one (f : E) (h0 : (1 : QuasiCharacter G) ∈ ΩI) :
    modulatedFourierMellin m I hm μ f.val 1 = ∫ g, f.val g ∂μ := by
  unfold modulatedFourierMellin
  rw [Set.indicator_of_mem h0]
  simp

include hSC hBorel hHaar hInt hne hOpen

include hms in
/-- Paper: Theorem D.3.3.13, p. 812. The Fourier–Mellin integrand is
absolutely integrable at every quasi-character in the strip. -/
theorem modulatedFourierMellin_integrable (f : E) (c : ΩI) :
    Integrable (fun g ↦ f.val g * (c : QuasiCharacter G) g) μ := by
  let d : QuasiCharacter G := c
  let a : I := ⟨quasiCharacterAbscissa m.toMonoidHom hm.1 hm.2 d, c.property⟩
  let F := modulatedExponentialDecayTwist m I a f
  have hnorm (x : G) : ‖F x‖ = ‖f.val x * d x‖ := by
    change ‖(((((m x).val : ℝ) ^ (a : ℝ)) : ℝ) : ℂ) * f.val x‖ = ‖f.val x * d x‖
    rw [norm_mul, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _),
      norm_quasiCharacter_eq_rpow_abscissa m.toMonoidHom hm.1 hm.2]
    exact mul_comm _ _
  have hden (x : G) : (‖d x‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr ((Group.isUnit x).map d).ne_zero)
  have hf : Continuous f.val := by
    refine ((continuous_schwartzBruhat F).div (Complex.continuous_ofReal.comp d.continuous.norm) hden).congr
      fun x ↦ (div_eq_iff (hden x)).mpr ?_
    rw [norm_quasiCharacter_eq_rpow_abscissa m.toMonoidHom hm.1 hm.2]
    exact mul_comm _ _
  have hFourier := schwartzBruhat_fourier_equiv (G := G) μ
  exact (hFourier.choose_spec F).1.norm.mono' (hf.mul d.continuous).aestronglyMeasurable
    (ae_of_all μ fun x ↦ (hnorm x).ge)

omit hSC hBorel hHaar hInt hne hOpen in
/-- On a disk about zero the first derivative of an exponential integral is
dominated by its two real weights a little outside the disk. -/
private theorem differentiableAt_weighted_exp_integral {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (F : X → ℂ) (L : X → ℝ) (hF : Integrable F μ) (hL : Measurable L)
    (d : ℝ) (hd : 0 < d)
    (hp : Integrable (fun x ↦ ‖F x‖ * Real.exp (2*d*L x)) μ)
    (hm : Integrable (fun x ↦ ‖F x‖ * Real.exp (-(2*d)*L x)) μ) :
    DifferentiableAt ℂ (fun z : ℂ ↦ ∫ x, F x * Complex.exp (z * L x) ∂μ) 0 := by
  let b (x : X) := d⁻¹ * (‖F x‖ * Real.exp (2*d*L x) + ‖F x‖ * Real.exp (-(2*d)*L x))
  have hb : Integrable b μ := (hp.add hm).const_mul _
  have h (z : ℂ) (hz : z ∈ Metric.ball 0 d) (t : ℝ) :
      |t| * Real.exp (z.re * t) ≤ d⁻¹ * (Real.exp (2*d*t) + Real.exp (-(2*d)*t)) := by
    have hnorm : ‖z‖ < d := by simpa only [Metric.mem_ball, dist_zero_right] using hz
    have ht : z.re * t ≤ d * |t| := (le_abs_self _).trans ((abs_mul _ _).le.trans
      (mul_le_mul_of_nonneg_right ((Complex.abs_re_le_norm z).trans hnorm.le) (abs_nonneg t)))
    have h1 : |t| ≤ d⁻¹ * Real.exp (d * |t|) := by
      rw [← div_eq_inv_mul, le_div_iff₀ hd, mul_comm]
      exact (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
    have h2 : Real.exp (2*d*|t|) ≤ Real.exp (2*d*t) + Real.exp (-(2*d)*t) := by
      rcases le_total 0 t with ht | ht
      · rw [abs_of_nonneg ht]; exact le_add_of_nonneg_right (Real.exp_pos _).le
      · rw [abs_of_nonpos ht, mul_neg, neg_mul]; exact le_add_of_nonneg_left (Real.exp_pos _).le
    calc
      _ ≤ (d⁻¹ * Real.exp (d*|t|)) * Real.exp (d*|t|) := by gcongr
      _ = d⁻¹ * Real.exp (2*d*|t|) := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr hd.le)
  let D (z : ℂ) (x : X) := F x * (Complex.exp (z * L x) * (L x : ℂ))
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (bound := b)
    (F := fun (z : ℂ) x ↦ F x * Complex.exp (z * L x)) (F' := D) (Metric.ball_mem_nhds _ hd)
    ?_ ?_ ?_ ?_ hb ?_).2.differentiableAt
  · exact Filter.Eventually.of_forall fun z ↦ hF.aestronglyMeasurable.mul (by fun_prop)
  · simpa using hF
  · simp only [D, zero_mul, Complex.exp_zero, one_mul]
    exact hF.aestronglyMeasurable.mul (by fun_prop)
  · refine ae_of_all _ fun x z hz ↦ ?_
    simp only [D, norm_mul, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ = ‖F x‖ * (|L x| * Real.exp (z.re * L x)) := by ring
      _ ≤ ‖F x‖ * (d⁻¹ * (Real.exp (2*d*L x) + Real.exp (-(2*d)*L x))) :=
        mul_le_mul_of_nonneg_left (h z hz (L x)) (norm_nonneg _)
      _ = _ := by unfold b; ring
  · exact ae_of_all _ fun x z _ ↦ ((hasDerivAt_id z).mul_const (L x : ℂ)).cexp.const_mul (F x) |>.congr_deriv (by simp [D])

include hms in
/-- Paper: Theorem D.3.3.13, p. 812. The integral is holomorphic on the
relative strip for the norm-twist atlas of §3.1.1. -/
theorem modulatedFourierMellin_holomorphic (f : E) :
    letI := quasiCharacterChartedSpace m.toMonoidHom
      (hasNormTwistCharts_of_proper m.toMonoidHom hm.1 hm.2)
    MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (modulatedFourierMellin m I hm μ f.val) ΩI := by
  let charts := hasNormTwistCharts_of_proper m.toMonoidHom hm.1 hm.2
  let := quasiCharacterChartedSpace m.toMonoidHom charts
  intro c hc
  let σ := quasiCharacterAbscissa m.toMonoidHom hm.1 hm.2 c
  let L (x : G) := Real.log ((m x).val : ℝ)
  let F (x : G) := f.val x * c x
  let M (z : ℂ) := ∫ x, F x * Complex.exp (z * L x) ∂μ
  have hF : Integrable F μ := modulatedFourierMellin_integrable m I hm hInt hne μ hOpen hms f ⟨c, hc⟩
  have hL : Continuous L := (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)).log
    fun x ↦ NNReal.coe_ne_zero.mpr (m x).ne_zero
  have hw (s : ℝ) (hs : σ + s ∈ I) : Integrable (fun x ↦ ‖F x‖ * Real.exp (s * L x)) μ := by
    let T := modulatedExponentialDecayTwist m I ⟨σ + s,hs⟩ f
    have hT := ((schwartzBruhat_fourier_equiv (G := G) μ).choose_spec T).1.norm
    refine hT.congr (ae_of_all _ fun x ↦ ?_)
    have hp : 0 < ((m x).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt (m x))
    change ‖(((((m x).val : ℝ) ^ (σ + s) : ℝ) : ℂ) * f.val x)‖ = ‖f.val x * c x‖ * _
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hp _),
      norm_quasiCharacter_eq_rpow_abscissa m.toMonoidHom hm.1 hm.2, Real.rpow_add hp]
    rw [show Real.exp (s * L x) = ((m x).val : ℝ) ^ s by rw [Real.rpow_def_of_pos hp]; congr 1; exact mul_comm _ _]
    change (((m x).val : ℝ) ^ σ * ((m x).val : ℝ) ^ s) * ‖f.val x‖ =
      (‖f.val x‖ * ((m x).val : ℝ) ^ σ) * ((m x).val : ℝ) ^ s
    ring
  have hσ : σ ∈ I := hc
  obtain ⟨r, hr, hrI⟩ := Metric.isOpen_iff.mp hOpen σ hσ
  let d := r / 4
  have hnear (s : ℝ) (hs : |s| < r) : σ + s ∈ I :=
    hrI (by simpa only [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left] using hs)
  have hM : DifferentiableAt ℂ M 0 := differentiableAt_weighted_exp_integral μ F L hF hL.measurable d
    (by dsimp [d]; positivity)
    (hw _ (hnear _ (by dsimp [d]; rw [abs_of_nonneg (by positivity)]; linarith)))
    (hw _ (hnear _ (by dsimp [d]; rw [abs_neg, abs_of_nonneg (by positivity)]; linarith)))
  let a := (charts c).choose
  have ha := (charts c).choose_spec
  have hopen : IsOpen ΩI := hOpen.preimage (continuous_quasiCharacterAbscissa m.toMonoidHom hm.1 hm.2)
  have hc' : a.symm (a c) ∈ ΩI := (a.left_inv ha.1).symm ▸ hc
  have heq : modulatedFourierMellin m I hm μ f.val ∘ a.symm =ᶠ[𝓝 (a c)] M := by
    filter_upwards [a.open_target.mem_nhds (a.map_source ha.1),
      (a.continuousAt_symm (a.map_source ha.1)).preimage_mem_nhds (hopen.mem_nhds hc')] with z hz hstrip
    change modulatedFourierMellin m I hm μ f.val (a.symm z) = M z
    have hstrip' : a.symm z ∈ ΩI := hstrip
    rw [modulatedFourierMellin, Set.indicator_of_mem hstrip']
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    have hp : 0 < ((m x).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt (m x))
    have hchar : a.symm z x = c x * (((m x).val : ℝ) : ℂ) ^ z := ha.2.2 z hz x
    have hpow : (((m x).val : ℝ) : ℂ) ^ z = Complex.exp (z * L x) := by
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne'), ← Complex.ofReal_log hp.le, mul_comm _ z]
    exact (congrArg (f.val x * ·) hchar).trans ((congrArg (fun v ↦ f.val x * (c x * v)) hpow).trans
      (mul_assoc (f.val x) (c x) _).symm)
  have hd : DifferentiableAt ℂ (modulatedFourierMellin m I hm μ f.val ∘ a.symm) (a c) :=
    (show DifferentiableAt ℂ M (a c) from (ha.2.1.symm ▸ hM)).congr_of_eventuallyEq heq
  apply MDifferentiableAt.mdifferentiableWithinAt
  apply (mdifferentiableAt_iff _ _).mpr
  exact ⟨(a.symm.continuousAt_iff_continuousAt_comp_right ha.1).mpr hd.continuousAt, hd.differentiableWithinAt⟩

include hms in
/-- Paper: Theorem D.3.3.13, p. 812. The values on the relative strip depend
linearly on the test function.
Deviation: Holomorphy of the range is stated in modulatedFourierMellin_holomorphic. -/
theorem modulatedFourierMellin_linear :
    ∃ M : E →ₗ[ℂ] (ΩI → ℂ), ∀ f c, M f c = modulatedFourierMellin m I hm μ f.val c := by
  let M (f : E) (c : ΩI) := ∫ x, f.val x * (c : QuasiCharacter G) x ∂μ
  refine ⟨{ toFun := M, map_add' := ?_, map_smul' := ?_ },
    fun f c ↦ (Set.indicator_of_mem c.property (fun d : QuasiCharacter G ↦ ∫ x, f.val x * d x ∂μ)).symm⟩
  · intro f g
    funext c
    have hf := modulatedFourierMellin_integrable m I hm hInt hne μ hOpen hms f c
    have hg := modulatedFourierMellin_integrable m I hm hInt hne μ hOpen hms g c
    exact (integral_congr_ae (ae_of_all μ fun x ↦
      add_mul (f.val x) (g.val x) ((c : QuasiCharacter G) x))).trans (integral_add hf hg)
  · intro r f
    funext c
    exact (integral_congr_ae (ae_of_all μ fun x ↦
      mul_assoc r (f.val x) ((c : QuasiCharacter G) x))).trans (integral_const_mul _ _)

/-- Paper: Theorem D.3.3.13, p. 812. Left translating a test function
multiplies its transform at c by c(g). -/
theorem modulatedFourierMellin_equivariant (g : G) (f : E) (c : ΩI) :
    let f' : E := ⟨fun x ↦ f.val (g⁻¹ * x),
      modulatedExponentialDecaySubmodule_translate m I hm hms g f⟩
    modulatedFourierMellin m I hm μ f'.val c =
      (c : QuasiCharacter G) g * modulatedFourierMellin m I hm μ f.val c := by
  intro f'
  unfold modulatedFourierMellin
  rw [Set.indicator_of_mem c.property, Set.indicator_of_mem c.property]
  have h1 : ∀ x, f.val (g⁻¹ * x) * (c : QuasiCharacter G) x =
      (c : QuasiCharacter G) g * (f.val (g⁻¹ * x) * (c : QuasiCharacter G) (g⁻¹ * x)) := by
    intro x
    have : (c : QuasiCharacter G) x = (c : QuasiCharacter G) g * (c : QuasiCharacter G) (g⁻¹ * x) := by
      rw [← map_mul, mul_inv_cancel_left]
    rw [this]; ring
  show ∫ x, f.val (g⁻¹ * x) * (c : QuasiCharacter G) x ∂μ = _
  simp_rw [h1]
  rw [integral_const_mul]
  congr 1
  exact integral_mul_left_eq_self (fun x ↦ f.val x * (c : QuasiCharacter G) x) g⁻¹

include hms in
/-- Paper: Theorem D.3.3.13, p. 815. The values on the strip determine
the test function. -/
theorem modulatedFourierMellin_injective :
    Injective (fun (f : E) (c : ΩI) ↦ modulatedFourierMellin m I hm μ f.val c) := by
  let a : I := ⟨hne.choose, hne.choose_spec⟩
  let L := modulatedExponentialDecayTwist m I a
  have hFourier := schwartzBruhat_fourier_equiv (G := G) μ
  let F := hFourier.choose
  intro f g h
  apply decay_twist_injective m I a
  apply F.injective
  refine Subtype.ext (funext fun χ ↦ ?_)
  let ψ := (χ⁻¹ : PontryaginDual G)
  let n := (Units.coeHom ℝ≥0).comp m.toMonoidHom
  let w := Complex.ofRealHom.toMonoidHom.comp
    (NNReal.toRealHom.toMonoidHom.comp ((NNReal.rpowMonoidHom (a : ℝ)).comp n))
  have hw : Continuous w := Complex.continuous_ofReal.comp
    ((NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)).rpow continuous_const
      (fun x ↦ Or.inl (NNReal.coe_ne_zero.mpr (m x).ne_zero)))
  let cc : Circle →ₜ* ℂ := ⟨Circle.coeHom, continuous_subtype_val⟩
  let c : QuasiCharacter G := cc.comp ψ * ⟨w, hw⟩
  have hc : c ∈ ΩI := by
    change quasiCharacterAbscissa m.toMonoidHom hm.1 hm.2 c ∈ I
    have hs := quasiCharacterAbscissa_of_unitary_twist m.toMonoidHom hm.1 hm.2 c ψ (a : ℝ) (by
      intro x
      exact congrArg ((ψ x : ℂ) * ·) (Complex.ofReal_cpow (NNReal.coe_nonneg _) (a : ℝ)))
    exact hs.symm ▸ a.property
  have eval (v : E) : F (L v) χ = modulatedFourierMellin m I hm μ v.val c := by
    refine ((hFourier.choose_spec (L v)).2 χ).trans ?_
    refine Eq.trans ?_ (Set.indicator_of_mem hc
      (fun d : QuasiCharacter G ↦ ∫ x, v.val x * d x ∂μ)).symm
    apply integral_congr_ae
    apply ae_of_all
    intro x
    change (w x * v.val x) * star (χ x : ℂ) = v.val x * ((((χ x)⁻¹ : Circle) : ℂ) * w x)
    rw [Circle.coe_inv_eq_conj]
    exact (mul_assoc _ _ _).trans (mul_rotate' (w x) (v.val x) (star (χ x : ℂ)))
  exact (eval f).trans ((congrFun h ⟨c, hc⟩).trans (eval g).symm)

-- TODO(paper-gap): The proof on pp. 813–814 evaluates the scalar profile at τ(t)
-- and later replaces the scalar decay factor with the ordinary Schwartz space.
-- TODO(paper-gap): The tensor formula with probability Haar on K and the scalar
-- Mellin transform requires compatible Haar normalization on G.

omit hSC hBorel hHaar hInt hne hOpen in
private theorem completion_tensor_congr {A B C D : Type*}
    [AddCommGroup A] [Module ℂ A] [TopologicalSpace A] [PolynormableSpace ℂ A] [T2Space A]
    [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] [PolynormableSpace ℂ B] [T2Space B]
    [AddCommGroup C] [Module ℂ C] [TopologicalSpace C] [PolynormableSpace ℂ C] [T2Space C]
    [AddCommGroup D] [Module ℂ D] [TopologicalSpace D] [PolynormableSpace ℂ D] [T2Space D]
    (e : A ≃L[ℂ] C) (v : B ≃L[ℂ] D) :
    ∃ M : Completion (InductiveTensor A B) ≃L[ℂ] Completion (InductiveTensor C D), ∀ a b,
      M (Completion.coe' (α := InductiveTensor A B) (a ⊗ₜ[ℂ] b)) =
        Completion.coe' (α := InductiveTensor C D) (e a ⊗ₜ[ℂ] v b) := by
  let L : InductiveTensor A B →L[ℂ] InductiveTensor C D :=
    ⟨inductiveTensorMap e.toLinearMap v.toLinearMap, inductiveTensorMap_continuous e.toContinuousLinearMap v.toContinuousLinearMap⟩
  let R : InductiveTensor C D →L[ℂ] InductiveTensor A B :=
    ⟨inductiveTensorMap e.symm.toLinearMap v.symm.toLinearMap, inductiveTensorMap_continuous e.symm.toContinuousLinearMap v.symm.toContinuousLinearMap⟩
  let J := TensorProduct.congr e.toLinearEquiv v.toLinearEquiv
  have hr (x : Completion (InductiveTensor A B)) : R.completion (L.completion x) = x := by
    refine Completion.induction_on (p := fun z ↦ R.completion (L.completion z) = z) x
      (isClosed_eq (R.completion.continuous.comp L.completion.continuous) continuous_id) fun a ↦ ?_
    rw [ContinuousLinearMap.completion_apply_coe, ContinuousLinearMap.completion_apply_coe]
    exact congrArg Completion.coe' (J.symm_apply_apply a)
  have hl (x : Completion (InductiveTensor C D)) : L.completion (R.completion x) = x := by
    refine Completion.induction_on (p := fun z ↦ L.completion (R.completion z) = z) x
      (isClosed_eq (L.completion.continuous.comp R.completion.continuous) continuous_id) fun a ↦ ?_
    rw [ContinuousLinearMap.completion_apply_coe, ContinuousLinearMap.completion_apply_coe]
    exact congrArg Completion.coe' (J.apply_symm_apply a)
  exact ⟨ContinuousLinearEquiv.equivOfInverse L.completion R.completion hr hl,
    fun a b ↦ L.completion_apply_coe (a ⊗ₜ[ℂ] b)⟩

omit hSC hBorel hHaar hInt hne hOpen in
private theorem completion_tensor_evaluations {A B ι : Type*}
    [AddCommGroup A] [Module ℂ A] [TopologicalSpace A] [PolynormableSpace ℂ A] [T2Space A]
    [AddCommGroup B] [Module ℂ B] [UniformSpace B] [IsUniformAddGroup B] [ContinuousSMul ℂ B]
    [PolynormableSpace ℂ B] [T2Space B] [CompleteSpace B] (ev : ι → A →L[ℂ] ℂ) :
    ∃ j : Completion (InductiveTensor A B) →L[ℂ] (ι → B), ∀ a b k,
      j (Completion.coe' (α := InductiveTensor A B) (a ⊗ₜ[ℂ] b)) k = ev k a • b := by
  let L (k : ι) : InductiveTensor A B →ₗ[ℂ] B :=
    TensorProduct.lift ((LinearMap.lsmul ℂ B).comp (ev k).toLinearMap)
  have hc (k : ι) : Continuous (L k) :=
    (continuous_inductiveTensor_iff (L k)).mpr ⟨fun a ↦ by
      change Continuous (fun y : B ↦ ev k a • y)
      exact continuous_const_smul _, fun b ↦ by
      change Continuous (fun x : A ↦ ev k x • b)
      exact (ev k).continuous.smul continuous_const⟩
  let F (k : ι) : InductiveTensor A B →L[ℂ] B := ⟨L k, hc k⟩
  let H (k : ι) := (F k).fromCompletion
  refine ⟨ContinuousLinearMap.pi H, fun a b k ↦ ?_⟩
  exact (F k).fromCompletion_apply_coe (a ⊗ₜ[ℂ] b)

omit hSC hBorel hHaar hInt hne hOpen in
private theorem completion_tensor_eval_ext {A B : Type*}
    [AddCommGroup A] [Module ℂ A] [TopologicalSpace A]
    [AddCommGroup B] [Module ℂ B] [TopologicalSpace B]
    (L R : Completion (InductiveTensor A B) →L[ℂ] ℂ)
    (h : ∀ a b, L (Completion.coe' (α := InductiveTensor A B) (a ⊗ₜ[ℂ] b)) =
      R (Completion.coe' (α := InductiveTensor A B) (a ⊗ₜ[ℂ] b))) : ∀ z, L z = R z := by
  let J := (Completion.toComplL : InductiveTensor A B →L[ℂ] Completion (InductiveTensor A B))
  have hall : (L.comp J).toLinearMap = (R.comp J).toLinearMap := by
    apply TensorProduct.ext'
    exact h
  intro z
  exact Completion.induction_on (p := fun v ↦ L v = R v) z (isClosed_eq L.continuous R.continuous)
    (fun v ↦ LinearMap.congr_fun hall v)

omit hSC hBorel hHaar hInt hne hOpen in
private theorem tensor_observations_ext {A B X Y Z ι : Type*}
    [AddCommGroup A] [Module ℂ A] [TopologicalSpace A] [AddCommGroup B] [Module ℂ B] [TopologicalSpace B]
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z]
    (e : Completion (InductiveTensor A B) ≃L[ℂ] X) (F : Completion (InductiveTensor A B) ≃L[ℂ] Y)
    (j : Y →L[ℂ] (ι → Z)) (i : ι) (p : X → ℂ) (q : Z → ℂ)
    (hp : ∃ L : X →L[ℂ] ℂ, ∀ x, L x = p x) (hq : ∃ R : Z →L[ℂ] ℂ, ∀ z, R z = q z)
    (heq : ∀ a b, p (e (Completion.coe' (α := InductiveTensor A B) (a ⊗ₜ[ℂ] b))) =
      q (j (F (Completion.coe' (α := InductiveTensor A B) (a ⊗ₜ[ℂ] b))) i)) :
    ∀ z, p (e z) = q (j (F z) i) := by
  obtain ⟨L, hL⟩ := hp
  obtain ⟨R, hR⟩ := hq
  let U := L.comp e.toContinuousLinearMap
  let V := ((R.comp (ContinuousLinearMap.proj i)).comp j).comp F.toContinuousLinearMap
  intro z
  exact (hL _).symm.trans ((completion_tensor_eval_ext U V (fun a b ↦
    (hL _).trans ((heq a b).trans (hR _).symm)) z).trans (hR _))

omit hSC hBorel hHaar hInt hne hOpen in
open scoped SchwartzMap in
private theorem bergman_eval_at (hOpen : IsOpen I) (hInt : OrdConnected I) (s : ℂ) (hs : s.re ∈ I) :
    ∃ L : SchwartzBergman I →L[ℂ] ℂ, ∀ f, L f = f.val s := by
  let line : SchwartzBergman I →L[ℂ] 𝓢(ℝ, ℂ) := ⟨bergmanLine hOpen hInt ⟨s.re,hs⟩, continuous_bergmanLine hOpen hInt _⟩
  let V := (BoundedContinuousFunction.evalCLM ℂ s.im).comp (SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ)
  refine ⟨V.comp line, fun f ↦ ?_⟩
  change f.val (s.re + s.im * Complex.I) = f.val s
  rw [Complex.re_add_im]

omit hSC hBorel hHaar hInt hne hOpen in
private theorem scalar_mellin_integral (f : ℝ → ℂ) (s : ℂ) :
    (∫ t : ℝ≥0ˣ, f (Real.log (t.val : ℝ)) * (((t.val : ℝ) : ℂ) ^ s) ∂positiveRealHaar) =
      mellin (fun t ↦ f (Real.log t)) s := by
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  let e : ℝ → ℝ≥0ˣ := fun x ↦ Units.mk0 (Real.exp x).toNNReal (by positivity)
  have he : e = fun x : ℝ ↦ positiveRealLogEquiv.symm (Multiplicative.ofAdd x) := by
    funext x
    apply positiveRealLogEquiv.injective
    rw [positiveRealLogEquiv.apply_symm_apply]
    apply Multiplicative.toAdd.injective
    rw [positiveRealLogEquiv_apply]
    change Real.log ((Real.exp x).toNNReal : ℝ) = x
    rw [Real.coe_toNNReal _ (Real.exp_pos x).le, Real.log_exp]
  have hh : Topology.IsClosedEmbedding e := by
    rw [he]
    exact positiveRealLogEquiv.symm.toHomeomorph.isClosedEmbedding
  change (∫ t : ℝ≥0ˣ, _ ∂volume.map e) = _
  rw [hh.integral_map, mellin, ← integral_comp_exp]
  apply integral_congr_ae
  filter_upwards with x
  change f (Real.log ((Real.exp x).toNNReal : ℝ)) * ((((Real.exp x).toNNReal : ℝ) : ℂ) ^ s) = _
  simp only [Real.coe_toNNReal _ (Real.exp_pos x).le, Real.log_exp, Complex.real_smul, smul_eq_mul]
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos x).ne'),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos x).ne'),
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp]
  simp only [Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
  rw [mul_comm (f x)]
  congr 2
  ring

omit hHaar in
include hτ in
private theorem fourierMellin_product_evaluation (μ₁ : Measure K) [μ₁.IsHaarMeasure] (hprob : μ₁ univ = 1)
    (hμ : μ = (μ₁.prod positiveRealHaar).map (fun z : K × ℝ≥0ˣ ↦ (z.1 : G) * τ z.2))
    (v : E) (h : SchwartzBruhat K) (f : P)
    (hv : ∀ (u : K) (t : ℝ≥0ˣ), v.val ((u : G) * τ t) = h u * f.val (Real.log (t.val : ℝ)))
    (c : ΩI) (ω : PontryaginDual K) (s : ℂ) (hs : s.re ∈ I)
    (hc : ∀ (u : K) (t : ℝ≥0ˣ), (c : QuasiCharacter G) ((u : G) * τ t) = (ω u : ℂ) * ((t.val : ℝ) : ℂ) ^ s) :
    modulatedFourierMellin m I hm μ v.val c =
      lcaFourier μ₁ h ω⁻¹ * (positiveRealFourierMellin I hOpen hInt hne f).val s := by
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  let : SecondCountableTopology ℝ≥0ˣ := (Units.isEmbedding_val₀ (G₀ := ℝ≥0)).secondCountableTopology
  let : SecondCountableTopology K := TopologicalSpace.Subtype.secondCountableTopology (K : Set G)
  let : IsProbabilityMeasure μ₁ := ⟨hprob⟩
  let : SFinite positiveRealHaar := by unfold positiveRealHaar; infer_instance
  obtain ⟨d, hd⟩ := hm.exists_sectionEquiv τ hτ
  have his : IsClosedEmbedding (fun z : K × ℝ≥0ˣ ↦ (z.1 : G) * τ z.2) :=
    (congrArg IsClosedEmbedding (funext hd)).mp d.toHomeomorph.isClosedEmbedding
  unfold modulatedFourierMellin
  rw [indicator_of_mem c.property, hμ, his.integral_map, positiveRealFourierMellin_apply _ _ _ _ _ _ hs]
  let a (u : K) := h u * (ω u : ℂ)
  let b (t : ℝ≥0ˣ) := f.val (Real.log (t.val : ℝ)) * ((t.val : ℝ) : ℂ) ^ s
  have hab (z : K × ℝ≥0ˣ) : v.val ((z.1 : G) * τ z.2) * (c : QuasiCharacter G) ((z.1 : G) * τ z.2) =
      a z.1 * b z.2 := by rw [hv, hc]; dsimp only [a,b]; ring
  have hcomp : (∫ u, a u ∂μ₁) = lcaFourier μ₁ h ω⁻¹ := by
    apply integral_congr_ae
    filter_upwards with u
    change h u * (ω u : ℂ) = h u * star (((ω u)⁻¹ : Circle) : ℂ)
    rw [Circle.coe_inv_eq_conj, ← Complex.star_def, star_star]
  exact (integral_congr_ae (ae_of_all _ hab)).trans
    ((integral_prod_mul a b).trans (congrArg₂ (· * ·) hcomp (scalar_mellin_integral f.val s)))

omit hSC hBorel hHaar hInt hne hOpen in
private theorem exists_fourier_inverted {A : Type*} [CommGroup A] [TopologicalSpace A]
    [IsTopologicalGroup A] [T2Space A] [LocallyCompactSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A] (μA : Measure A) [μA.IsHaarMeasure] :
    ∃ F : SchwartzBruhat A ≃L[ℂ] SchwartzBruhat (PontryaginDual A), ∀ h ω, F h ω = lcaFourier μA h ω⁻¹ := by
  let : SecondCountableTopology Circle := inferInstanceAs (SecondCountableTopology (Metric.sphere (0 : ℂ) 1))
  let : SecondCountableTopology (PontryaginDual A) := (ContinuousMonoidHom.isEmbedding_toContinuousMap A Circle).secondCountableTopology
  let d : PontryaginDual A ≃ₜ* PontryaginDual A := { MulEquiv.inv _ with continuous_toFun := continuous_inv, continuous_invFun := continuous_inv }
  let HV := schwartzBruhat_congr d
  let V := HV.choose
  have hV := HV.choose_spec
  let F := schwartzBruhat_fourier_equiv (G := A) μA
  refine ⟨F.choose.trans V, fun h ω ↦ ?_⟩
  have he := hV (F.choose h) ω⁻¹
  have hω : d ω⁻¹ = ω := inv_inv ω
  have hp := congrArg (V (F.choose h)).val hω.symm
  have hh := hp.trans he
  have ht := ContinuousLinearEquiv.trans_apply F.choose V h
  have ht' := congrArg (fun q : SchwartzBruhat (PontryaginDual A) ↦ q ω) ht
  exact ht'.trans (hh.trans ((F.choose_spec h).2 _))

omit hSC hBorel hHaar hInt hne hOpen in
private theorem exists_phase_character {A : Type*} [CommGroup A] [TopologicalSpace A] (d : QuasiCharacter A) :
    ∃ χ : PontryaginDual A, ∀ x, (χ x : ℂ) = d x / (‖d x‖ : ℂ) := by
  have hz (x : A) : d x ≠ 0 := ((Group.isUnit x).map d).ne_zero
  have hn (x : A) : (‖d x‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hz x))
  let v (x : A) : Circle := ⟨d x / (‖d x‖ : ℂ), by
    apply mem_sphere_zero_iff_norm.mpr
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _), div_self (norm_ne_zero_iff.mpr (hz x))]⟩
  let χ : PontryaginDual A := {
    toFun := v
    map_one' := by apply Circle.ext; change d 1 / (‖d 1‖ : ℂ) = 1; simp
    map_mul' := by
      intro x y
      apply Circle.ext
      change d (x*y) / (‖d (x*y)‖ : ℂ) = _ * _
      rw [map_mul, norm_mul, Complex.ofReal_mul]
      exact mul_div_mul_comm _ _ _ _
    continuous_toFun := (d.continuous.div (Complex.continuous_ofReal.comp d.continuous.norm) hn).subtype_mk _ }
  exact ⟨χ, fun _ ↦ rfl⟩

omit hInt hne hOpen in
include hSC hBorel hHaar in
private theorem continuous_fourierMellin_at_character (c : ΩI) :
    Continuous fun f : E ↦ modulatedFourierMellin m I hm μ f.val c := by
  let d : QuasiCharacter G := c
  let a : I := ⟨quasiCharacterAbscissa m.toMonoidHom hm.1 hm.2 d,c.property⟩
  let W := exists_phase_character d
  let χ := W.choose
  have hχ := W.choose_spec
  let F := schwartzBruhat_fourier_equiv (G := G) μ
  let : SecondCountableTopology Circle := inferInstanceAs (SecondCountableTopology (Metric.sphere (0 : ℂ) 1))
  let : SecondCountableTopology (PontryaginDual G) := (ContinuousMonoidHom.isEmbedding_toContinuousMap G Circle).secondCountableTopology
  have he := (continuous_schwartzBruhat_eval_forEndpoints (χ⁻¹)).comp
    (F.choose.continuous.comp (continuous_decay_twist m I a))
  apply he.congr
  intro f
  refine ((F.choose_spec _).2 _).trans ?_
  refine Eq.trans ?_ (Set.indicator_of_mem c.property (fun q : QuasiCharacter G ↦ ∫ x, f.val x * q x ∂μ)).symm
  apply integral_congr_ae
  filter_upwards with x
  change (((((m x).val : ℝ) ^ a.val : ℝ) : ℂ) * f.val x) * star (((χ x)⁻¹ : Circle) : ℂ) = f.val x * d x
  have ha : ((m x).val : ℝ) ^ (a : ℝ) = ‖d x‖ := (norm_quasiCharacter_eq_rpow_abscissa m.toMonoidHom hm.1 hm.2 d x).symm
  have hn : (‖d x‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr ((Group.isUnit x).map d).ne_zero)
  have cancel (w z v : ℂ) (hw : w ≠ 0) : (w * v) * (z / w) = v * z := by field_simp
  have hphase : star (((χ x)⁻¹ : Circle) : ℂ) = d x / (‖d x‖ : ℂ) := by
    rw [Circle.coe_inv_eq_conj, ← Complex.star_def, star_star]
    exact hχ x
  exact (congrArg₂ (· * ·) (congrArg (fun t : ℝ ↦ (t : ℂ) * f.val x) ha) hphase).trans (cancel _ _ _ hn)

omit hSC hBorel hHaar hInt hne hOpen in
private theorem tensor_family_injective {A B X Y D J : Type*}
    (e : A ≃ X) (F : A ≃ B) (j : B → Y) (p : X → J → D) (hp : Injective p)
    (h : ∀ i, ∃ q : Y → D, ∀ a, p (e a) i = q (j (F a))) : Injective j := by
  intro z w hzw
  apply F.symm.injective
  apply e.injective
  apply hp
  funext i
  obtain ⟨q,hq⟩ := h i
  simpa only [F.apply_symm_apply] using
    (hq (F.symm z)).trans ((congrArg q (by simpa only [F.apply_symm_apply] using hzw : j (F (F.symm z)) = j (F (F.symm w)))).trans (hq (F.symm w)).symm)

omit hBorel hHaar in
include hm in
private theorem decayTensor_congr (F₁ : SchwartzBruhat K ≃L[ℂ] SchwartzBruhat (PontryaginDual K)) :
    ∃ F : Completion (InductiveTensor (SchwartzBruhat K) P) ≃L[ℂ]
      Completion (InductiveTensor (SchwartzBruhat (PontryaginDual K)) (SchwartzBergman I)), ∀ (h : SchwartzBruhat K) (f : P), F (Completion.coe' (α := InductiveTensor (SchwartzBruhat K) P) (h ⊗ₜ[ℂ] f)) =
      Completion.coe' (α := InductiveTensor (SchwartzBruhat (PontryaginDual K)) (SchwartzBergman I))
        (F₁ h ⊗ₜ[ℂ] positiveRealFourierMellin I hOpen hInt hne f) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let : SecondCountableTopology K := TopologicalSpace.Subtype.secondCountableTopology (K : Set G)
  let : SecondCountableTopology Circle := inferInstanceAs (SecondCountableTopology (Metric.sphere (0 : ℂ) 1))
  let : SecondCountableTopology (PontryaginDual K) := (ContinuousMonoidHom.isEmbedding_toContinuousMap K Circle).secondCountableTopology
  let : T2Space (SchwartzBruhat K) := schwartzBruhat_t2 (G := K)
  let : T2Space (SchwartzBruhat (PontryaginDual K)) := schwartzBruhat_t2 (G := PontryaginDual K)
  let : T2Space P := (positiveRealExponentialDecay_isEmbedding I hne).t2Space
  let hB := schwartzBergman_frechet I hOpen hInt hne
  let : MetrizableSpace (SchwartzBergman I) := hB.choose_spec.2.1
  let : CompleteSpace (SchwartzBergman I) := hB.choose_spec.2.2
  with_reducible_and_instances exact completion_tensor_congr F₁ (positiveRealFourierMellin I hOpen hInt hne)

omit hBorel hHaar in
include hm hOpen hInt hne hSC in
private theorem decayTensor_evaluation : ∃ j : Completion (InductiveTensor (SchwartzBruhat (PontryaginDual K)) (SchwartzBergman I)) →L[ℂ]
      (PontryaginDual K → SchwartzBergman I), ∀ (H : SchwartzBruhat (PontryaginDual K)) (B : SchwartzBergman I) (ω : PontryaginDual K),
      j (Completion.coe' (α := InductiveTensor (SchwartzBruhat (PontryaginDual K)) (SchwartzBergman I)) (H ⊗ₜ[ℂ] B)) ω = H ω • B := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let : SecondCountableTopology K := TopologicalSpace.Subtype.secondCountableTopology (K : Set G)
  let : SecondCountableTopology Circle := inferInstanceAs (SecondCountableTopology (Metric.sphere (0 : ℂ) 1))
  let : SecondCountableTopology (PontryaginDual K) := (ContinuousMonoidHom.isEmbedding_toContinuousMap K Circle).secondCountableTopology
  let : T2Space (SchwartzBruhat (PontryaginDual K)) := schwartzBruhat_t2 (G := PontryaginDual K)
  let hB := schwartzBergman_frechet I hOpen hInt hne
  let : MetrizableSpace (SchwartzBergman I) := hB.choose_spec.2.1
  let : CompleteSpace (SchwartzBergman I) := hB.choose_spec.2.2
  let ev (ω : PontryaginDual K) : SchwartzBruhat (PontryaginDual K) →L[ℂ] ℂ :=
    ⟨(LinearMap.proj ω).comp (schwartzBruhatSubmodule (PontryaginDual K)).subtype, continuous_schwartzBruhat_eval_forEndpoints ω⟩
  have hev (ω : PontryaginDual K) (H : SchwartzBruhat (PontryaginDual K)) : ev ω H = H.val ω := rfl
  let out := completion_tensor_evaluations (B := SchwartzBergman I) ev
  refine out.elim fun j hj ↦ ⟨j, fun H B ω ↦ ?_⟩
  have vv := hj H B ω
  have ww := congrArg (fun q : ℂ ↦ q • B) (hev ω H)
  have hh := vv.trans ww
  dsimp only at hh ⊢
  with_reducible_and_instances exact hh

omit hSC hBorel hHaar hInt hne hOpen in
private theorem tensor_coordinate_eval {X Y : Type*} (j : X → Y) (q : Y → ℂ)
    {x y : X} (hx : x = y) {b : Y} (hy : j y = b) {v w : ℂ}
    (hq : q b = w) (hv : v = w) : v = q (j x) := by rw [hx, hy, hq, hv]

include hτ in
private theorem decay_transform_tensor_value
    (μ₁ : Measure K) [μ₁.IsHaarMeasure] (hμ₁ : μ₁ univ = 1)
    (hμ : μ = (μ₁.prod positiveRealHaar).map (fun z : K × ℝ≥0ˣ ↦ (z.1 : G) * τ z.2))
    (e : Completion (InductiveTensor (SchwartzBruhat K) P) ≃L[ℂ] E)
    (he : ∀ (h : SchwartzBruhat K) (f : P) (u : K) (t : ℝ≥0ˣ),
      (e (Completion.coe' (α := InductiveTensor (SchwartzBruhat K) P) (h ⊗ₜ[ℂ] f))).val
        ((u : G) * τ t) = h u * f.val (Real.log (t.val : ℝ)))
    (F₁ : SchwartzBruhat K ≃L[ℂ] SchwartzBruhat (PontryaginDual K))
    (hF₁ : ∀ h ω, F₁ h ω = lcaFourier μ₁ h ω⁻¹)
    (F : Completion (InductiveTensor (SchwartzBruhat K) P) ≃L[ℂ]
      Completion (InductiveTensor (SchwartzBruhat (PontryaginDual K)) (SchwartzBergman I)))
    (hF : ∀ (h : SchwartzBruhat K) (f : P), F (Completion.coe' (α := InductiveTensor (SchwartzBruhat K) P) (h ⊗ₜ[ℂ] f)) =
      Completion.coe' (α := InductiveTensor (SchwartzBruhat (PontryaginDual K)) (SchwartzBergman I))
        (F₁ h ⊗ₜ[ℂ] positiveRealFourierMellin I hOpen hInt hne f))
    (j : Completion (InductiveTensor (SchwartzBruhat (PontryaginDual K)) (SchwartzBergman I)) →L[ℂ]
      (PontryaginDual K → SchwartzBergman I))
    (hj : ∀ (H : SchwartzBruhat (PontryaginDual K)) (B : SchwartzBergman I) (ω : PontryaginDual K),
      j (Completion.coe' (α := InductiveTensor (SchwartzBruhat (PontryaginDual K)) (SchwartzBergman I)) (H ⊗ₜ[ℂ] B)) ω = H ω • B)
    (z : Completion (InductiveTensor (SchwartzBruhat K) P)) (c : ΩI) (ω : PontryaginDual K) (s : Complex.re ⁻¹' I)
      (hc : ∀ (u : K) (t : ℝ≥0ˣ), (c : QuasiCharacter G) ((u : G) * τ t) = (ω u : ℂ) * ((t.val : ℝ) : ℂ) ^ (s : ℂ)) :
      modulatedFourierMellin m I hm μ (e z).val c = (j (F z) ω).val s := by
  let T := InductiveTensor (SchwartzBruhat K) P
  let V := positiveRealFourierMellin I hOpen hInt hne
  let M := modulatedFourierMellin_linear m I hm hInt hne μ hOpen hτ.surjective
  let L := (LinearMap.proj c).comp M.choose
  have hL (f : E) : L f = modulatedFourierMellin m I hm μ f.val c := M.choose_spec _ _
  let N : E →L[ℂ] ℂ := ⟨L, (continuous_fourierMellin_at_character m I hm μ c).congr fun x ↦ (hL x).symm⟩
  let p (f : E) := modulatedFourierMellin m I hm μ f.val c
  let q (v : SchwartzBergman I) := v.val s
  have hp : ∃ L' : E →L[ℂ] ℂ, ∀ x, L' x = p x := ⟨N, hL⟩
  have hq := bergman_eval_at I hOpen hInt s s.property
  have extend := tensor_observations_ext (A := SchwartzBruhat K) (B := P) e F j ω p q hp hq
  with_reducible_and_instances refine extend ?_ z
  intro h f
  let x := Completion.coe' (α := T) (h ⊗ₜ[ℂ] f)
  let W0 := fourierMellin_product_evaluation m I hm hInt hne τ hτ μ hOpen μ₁ hμ₁ hμ
  let W1 := W0 (e (Completion.coe' (α := InductiveTensor (SchwartzBruhat K) P) (h ⊗ₜ[ℂ] f))) h f
  have hv := he h f
  have W2 := W1 (fun u t ↦ by
    have vv := hv u t
    dsimp only at vv ⊢
    with_reducible_and_instances exact vv)
  have hprod := W2 c ω s s.property hc
  have hx := hF h f
  have hjv := hj (F₁ h) (V f) ω
  have hk := hF₁ h ω
  have hg := congrArg (· * (V f).val s) hk
  let J (v : Completion (InductiveTensor (SchwartzBruhat (PontryaginDual K)) (SchwartzBergman I))) := j v ω
  have hr (t : ℂ) (B : SchwartzBergman I) : q (t • B) = t * B.val s := rfl
  have hg' := (hr ((F₁ h) ω) (V f)).trans hg
  dsimp only at hx hjv hg' hprod ⊢
  with_reducible_and_instances exact tensor_coordinate_eval J q hx hjv hg' hprod

omit hSC hBorel hHaar hInt hne hOpen in
private theorem continuous_tensor_family_injective {A B X W S Z D J : Type*}
    [AddCommGroup A] [Module ℂ A] [TopologicalSpace A] [AddCommGroup B] [Module ℂ B] [TopologicalSpace B]
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    (e : A ≃L[ℂ] X) (F : A ≃L[ℂ] B) (j : B → W → Z) (p : X → J → D) (q : Z → S → D)
    (r : J → W → S → Prop) (hp : Injective p) (hr : ∀ i, ∃ w s, r i w s)
    (hv : ∀ a i w s, r i w s → p (e a) i = q (j (F a) w) s) : Injective j := by
  apply tensor_family_injective e.toEquiv F.toEquiv j p hp
  intro i
  obtain ⟨w, s, h⟩ := hr i
  exact ⟨fun y ↦ q (y w) s, fun a ↦ hv a i w s h⟩

include hτ in
/-- Paper: Theorem D.3.3.13, p. 812. In split coordinates the transform is the
completed tensor of compact Fourier transform with frequency inversion and
the scalar Fourier–Mellin transform, followed by the componentwise Schwartz–Bergman evaluations.
Deviation: The tensor identity assumes the product normalization used on
p. 813. -/
theorem modulatedFourierMellin_tensor
    (μ₁ : Measure K) [μ₁.IsHaarMeasure] (hμ₁ : μ₁ univ = 1)
    (hμ : μ = (μ₁.prod positiveRealHaar).map (fun z : K × ℝ≥0ˣ ↦ (z.1 : G) * τ z.2))
    (e : Completion (InductiveTensor (SchwartzBruhat K) P) ≃L[ℂ] E)
    (he : ∀ (h : SchwartzBruhat K) (f : P) (u : K) (t : ℝ≥0ˣ),
      (e (Completion.coe' (α := InductiveTensor (SchwartzBruhat K) P) (h ⊗ₜ[ℂ] f))).val
        ((u : G) * τ t) = h u * f.val (Real.log (t.val : ℝ))) :
    let T := InductiveTensor (SchwartzBruhat K) P
    let U := InductiveTensor (SchwartzBruhat (PontryaginDual K)) (SchwartzBergman I)
    let C := Complex.re ⁻¹' I
    ∃ (F₁ : SchwartzBruhat K ≃L[ℂ] SchwartzBruhat (PontryaginDual K))
      (F : Completion T ≃L[ℂ] Completion U)
      (j : Completion U →L[ℂ] (PontryaginDual K → SchwartzBergman I)),
      (∀ h ω, F₁ h ω = lcaFourier μ₁ h ω⁻¹) ∧
      (∀ (h : SchwartzBruhat K) (f : P),
        F (Completion.coe' (α := T) (h ⊗ₜ[ℂ] f)) =
          Completion.coe' (α := U) (F₁ h ⊗ₜ[ℂ] positiveRealFourierMellin I hOpen hInt hne f)) ∧
      Injective j ∧
      (∀ (H : SchwartzBruhat (PontryaginDual K)) (A : SchwartzBergman I) (ω : PontryaginDual K),
        j (Completion.coe' (α := U) (H ⊗ₜ[ℂ] A)) ω = H ω • A) ∧
      ∀ (z : Completion T) (c : ΩI) (ω : PontryaginDual K) (s : C),
        (∀ (u : K) (t : ℝ≥0ˣ),
          (c : QuasiCharacter G) ((u : G) * τ t) = (ω u : ℂ) * ((t.val : ℝ) : ℂ) ^ (s : ℂ)) →
        modulatedFourierMellin m I hm μ (e z).val c = (j (F z) ω).val s := by
  intro T U C
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let : SecondCountableTopology K := TopologicalSpace.Subtype.secondCountableTopology (K : Set G)
  let : SecondCountableTopology Circle := inferInstanceAs (SecondCountableTopology (Metric.sphere (0 : ℂ) 1))
  let : SecondCountableTopology (PontryaginDual K) := (ContinuousMonoidHom.isEmbedding_toContinuousMap K Circle).secondCountableTopology
  refine (exists_fourier_inverted μ₁).elim fun F₁ hF₁ ↦ ?_
  refine (decayTensor_congr m I hm hInt hne hOpen F₁).elim fun F hF ↦ ?_
  refine (decayTensor_evaluation m I hm hInt hne hOpen).elim fun j hj ↦ ?_
  let H0 := decay_transform_tensor_value m I hm hInt hne τ hτ μ hOpen μ₁ hμ₁ hμ e he
  let H1 := H0 F₁ hF₁
  let H2 := H1 F hF
  have hval := H2 j hj
  with_reducible_and_instances refine ⟨F₁, F, j, hF₁, hF, ?_, hj, hval⟩
  let r (c : ΩI) (ω : PontryaginDual K) (s : C) := ∀ (u : K) (t : ℝ≥0ˣ),
    (c : QuasiCharacter G) ((u : G) * τ t) = (ω u : ℂ) * ((t.val : ℝ) : ℂ) ^ (s : ℂ)
  have hr (c : ΩI) : ∃ ω s, r c ω s := by
    have sc := modulatedExponentialDecay_strip_coordinates m I hm τ hτ c
    let pt := sc.exists.choose
    exact ⟨pt.1, ⟨pt.2, sc.exists.choose_spec.1⟩, sc.exists.choose_spec.2⟩
  let p (f : E) (c : ΩI) := modulatedFourierMellin m I hm μ f.val c
  let q (b : SchwartzBergman I) (s : C) := b.val s
  have hp := modulatedFourierMellin_injective m I hm hInt hne μ hOpen hτ.surjective
  with_reducible_and_instances exact continuous_tensor_family_injective e F j p q r hp hr hval

end FourierMellin

end RiemannMasullo
