module

import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.MittagLefflerLift
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

import all RiemannMasullo.Ch05_ThetaZSpaces.Sec1
import all RiemannMasullo.Ch05_ThetaZSpaces.Sec2
import all RiemannMasullo.Ch05_ThetaZSpaces.Sec5
import RiemannMasullo.Ch06_LocalGlobal.Sec2
import RiemannMasullo.Ch06_LocalGlobal.Sec3
import all RiemannMasullo.Ch07_SchauderBasesZeta.Sec2

public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec3a
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace
import RiemannMasullo.ForMathlib.MeasureTheory.Integral.ProdPi
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Complex.ExpPolynomial

import all RiemannMasullo.Ch03_IdelicZeta.Sec3

/-! # §7.3.2–7.3.4 Paley–Wiener levels and archimedean principal parts

The finsets in this file list the finite places. Each S-local stage also
contains all the archimedean places. The PW constructions use the restriction
of the character to the norm-one group, which determines its theta isotype.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain NumberField Set Topology
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false
set_option maxHeartbeats 600000
set_option Elab.async false

variable {F : Type*} [Field F] [NumberField F]
variable {S T R : Finset (HeightOneSpectrum (𝓞 F))}

local notation "C₁" => (ideleClassNorm F).ker
local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "J(" T ")" => SIdeleQuotient F T
local notation "m(" T ")" => sIdeleQuotientNorm F T
local notation "J₁(" T ")" => (m(T)).ker
local notation "B(" T ")" => SchwartzBruhat (Multiplicative (SAdeleRing F T))
local notation "Θ(" T ", " ω ")" => SLocalHomogeneousThetaSpace F T ω
local notation "q(" T ", " ω ")" => (LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap F T ω)).mkQ
local notation "Z₀(" T ")" => sAdelePolarSubspace F T
local notation "Π(" h ")" => sAdeleSchwartzTransition F h
local notation "PicTrivial" => Subsingleton (CommRing.Pic ((S : Set V).integer F))
local notation "A(" T ", " ω ")" =>
  (existsUnique_sLocalHomogeneousThetaAction (F := F) (S := T) ω).exists.choose
local notation "PV(" h ", " ω ")" => sLocalHomogeneousThetaPrincipalValue (F := F) h ω
local notation "count(" S ")" => (Fintype.card (InfinitePlace F) + Finset.card S)
local notation "size(" R ")" => (∏ v ∈ R, (v.asIdeal.absNorm : ℝ))
local notation "large(" g ")" => (1 ≤ ((m(T) g).val : ℝ))
local notation "descend(" h ", " ω ", " hu ")" =>
  sLocalNormOneCharacter (F := F) T ω
    (NormOneCharacterUnramifiedOutside.mono (F := F) hu h)
local notation "onComponent(" c ", " ω ")" =>
  (normOneRestriction (m(S)) c =
    (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp ω)

/-- Paper: Definition 7.3.2.1(1), p. 351.
The Fourier box bounds the normalized absolute value at every selected place. -/
def sLocalPWBox (_S : Finset V) (X : ℝ) : Set (SAdeleRing F _S) :=
  {x | (∀ w : InfinitePlace F, ‖x.1 w‖ ^ w.mult ≤ X) ∧ ∀ v : _S, ‖x.2 v‖ ≤ X}

/-- Paper: Definition 7.3.2.1(1), p. 351.
The Fourier box is compact. -/
theorem isCompact_sLocalPWBox (X : ℝ) : IsCompact (sLocalPWBox S X) := by
  let A (w : InfinitePlace F) := {z : w.Completion | ‖z‖ ^ w.mult ≤ X}
  let D (v : S) := Metric.closedBall (0 : v.val.adicCompletion F) X
  have hA (w : InfinitePlace F) : IsCompact (A w) := by
    have he := InfinitePlace.Completion.isometry_extensionEmbedding w
    let : ProperSpace w.Completion :=
      LipschitzWith.properSpace he.isClosedEmbedding.isProperMap he.lipschitzWith
    refine (isCompact_closedBall (0 : w.Completion) (max 1 X)).of_isClosed_subset
      (isClosed_le (continuous_norm.pow w.mult) continuous_const) ?_
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right]
    by_cases h : ‖z‖ ≤ 1
    · exact h.trans (le_max_left _ _)
    · exact ((le_self_pow₀ (le_of_not_ge h) w.mult_ne_zero).trans hz).trans (le_max_right _ _)
  have hD (v : S) : IsCompact (D v) := by
    let := properSpace_adicCompletion v.val (K := F)
    exact isCompact_closedBall _ _
  have hbox : sLocalPWBox S X = (univ.pi A) ×ˢ (univ.pi D) := by
    apply Set.ext
    intro z
    simp only [sLocalPWBox, A, D, mem_ofPred_eq, mem_prod, Set.mem_pi, mem_univ, forall_const,
      Metric.mem_closedBall, dist_zero_right]
  rw [hbox]
  exact (isCompact_univ_pi hA).prod (isCompact_univ_pi hD)

local notation "inBand(" K ", " f ")" =>
  (HasCompactSupport (sAdeleSchwartzFourier f).val ∧
    tsupport (sAdeleSchwartzFourier f).val ⊆ Multiplicative.toAdd ⁻¹' K)

/-- Paper: Definitions 7.3.2.1(1) and 7.3.2.3(1), pp. 351, 355.
The tests at the larger stage are insertions of small-stage tests with compact Fourier
support contained in the specified region.
Deviation: Uses the cited transition (2.1.4.2), which inserts integer-ring indicators,
as in the proofs on pp. 352–359. Equations (7.3.2.2) and (7.3.2.13) print unit indicators. -/
def sLocalPWTests (hST : S ⊆ T) (K : Set (SAdeleRing F S)) : Submodule ℂ (B(T)) :=
  (Submodule.span ℂ {f : B(S) | inBand(K, f)}).map (Π(hST))

/-- The compactly supported functions with support in a fixed set form a submodule.
Consequently, taking the span of their preimages under a linear map preserves the set. -/
private theorem mem_sLocalPWTests_map_span {G E E' : Type*} [TopologicalSpace G]
    [AddCommMonoid E] [Module ℂ E] [AddCommMonoid E'] [Module ℂ E']
    (s : Set G) (L : E →ₗ[ℂ] (G → ℂ)) (φ : E → G → ℂ) (hL : ∀ g, L g = φ g)
    (j : E →ₗ[ℂ] E') (f : E') :
    f ∈ (Submodule.span ℂ {g : E | HasCompactSupport (φ g) ∧ tsupport (φ g) ⊆ s}).map j ↔
      ∃ g, j g = f ∧ HasCompactSupport (φ g) ∧ tsupport (φ g) ⊆ s := by
  obtain rfl : φ = L := (funext hL).symm
  let Q : Submodule ℂ (G → ℂ) :=
    { carrier := {g | HasCompactSupport g ∧ tsupport g ⊆ s}
      zero_mem' := ⟨HasCompactSupport.zero, by simp⟩
      add_mem' := by
        rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
        exact ⟨hx.add hy, (tsupport_add x y).trans (union_subset hx' hy')⟩
      smul_mem' := by
        rintro c x ⟨hx, hx'⟩
        exact ⟨hx.smul_left (f := fun _ ↦ c), (tsupport_smul_subset_right (fun _ ↦ c) x).trans hx'⟩ }
  have hgen : {g : E | HasCompactSupport (L g) ∧ tsupport (L g) ⊆ s} = (Q.comap L : Set E) := rfl
  rw [hgen, Submodule.span_eq]
  exact ⟨fun ⟨g, hg, hf⟩ ↦ ⟨g, hf, hg⟩, fun ⟨g, hf, hg⟩ ↦ ⟨g, hg, hf⟩⟩

/-- Paper: Definitions 7.3.2.1(1) and 7.3.2.3(1), pp. 351, 355.
Every test in the Fourier level is the insertion of a single small-stage test
satisfying both Fourier-support conditions.
Deviation: The insertion uses the integer-ring indicators of (2.1.4.2). -/
theorem mem_sLocalPWTests (hST : S ⊆ T) (K : Set (SAdeleRing F S)) (f : B(T)) :
    f ∈ sLocalPWTests hST K ↔ ∃ g : B(S), Π(hST) g = f ∧ inBand(K, g) := by
  let hF := sLocal_fourier_continuousLinear (F := F) (S := S)
  let A : B(S) →L[ℂ] B(S) := hF.choose
  have hA (g : B(S)) : A g = sAdeleSchwartzFourier g := hF.choose_spec g
  let L : B(S) →ₗ[ℂ] (Multiplicative (SAdeleRing F S) → ℂ) :=
    (schwartzBruhatSubmodule _).subtype.comp A.toLinearMap
  have hL (g : B(S)) : L g = (sAdeleSchwartzFourier g).val :=
    congrArg (fun f : B(S) ↦ f.val) (hA g)
  unfold sLocalPWTests
  exact mem_sLocalPWTests_map_span (Multiplicative.toAdd ⁻¹' K) L
    (fun g : B(S) ↦ (sAdeleSchwartzFourier g).val) hL (Π(hST)) f

/-- Dirac support supplies a compactly supported test with prescribed value one. -/
private theorem sLocalPWTests_moments_surjective_bump
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] (x : G) (U : Set G) (hU : U ∈ 𝓝 x) :
    ∃ f : SchwartzBruhat G, HasCompactSupport f.val ∧ tsupport f.val ⊆ U ∧ f x = 1 := by
  classical
  obtain ⟨U₀, hVU, hV, hxV⟩ := mem_nhds_iff.mp hU
  obtain ⟨C, hC, hxC, hCV⟩ := exists_compact_subset hV hxV
  obtain ⟨δ, hδ, hvan, -⟩ := schwartzBruhat_dirac_support x
  have hex : ∃ f : SchwartzBruhat G, tsupport f.val ⊆ interior C ∧ f x ≠ 0 := by
    by_contra! hn
    have hxvan : x ∈ schwartzBruhatVanishingLocus δ := by
      apply Set.mem_sUnion.mpr
      refine ⟨interior C, ⟨isOpen_interior, ?_⟩, hxC⟩
      intro f hf
      rw [hδ]
      exact hn f hf
    rw [hvan] at hxvan
    exact hxvan (Set.mem_singleton x)
  obtain ⟨f, hf, hfx⟩ := hex
  have hc : HasCompactSupport f.val :=
    hC.of_isClosed_subset isClosed_closure (hf.trans interior_subset)
  refine ⟨(f x)⁻¹ • f, hc.smul_left (f := fun _ ↦ (f x)⁻¹), ?_, ?_⟩
  · exact (tsupport_smul_subset_right (fun _ ↦ (f x)⁻¹) f.val).trans
      (hf.trans (interior_subset.trans (hCV.trans hVU)))
  · change (f x)⁻¹ * f x = 1
    exact inv_mul_cancel₀ hfx

/-- Modulating a nonzero bump by a character can make its integral nonzero
without enlarging its support. -/
private theorem sLocalPWTests_moments_surjective_zero_bump_modulate
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure]
    (p : SchwartzBruhat G) (hp : p ≠ 0) :
    ∃ h : SchwartzBruhat G, tsupport h.val ⊆ tsupport p.val ∧
      MeasureTheory.integral μ h.val ≠ 0 := by
  obtain ⟨L, hL⟩ := schwartzBruhat_fourier_equiv μ
  obtain ⟨χ, hχ⟩ : ∃ χ, L p χ ≠ 0 := by
    by_contra! hall
    exact hp (L.map_eq_zero_iff.mp (Subtype.ext (funext hall)))
  let h : SchwartzBruhat G := ⟨_, pontryaginDual_mul_schwartzBruhat χ⁻¹ p⟩
  refine ⟨h, tsupport_mul_subset_right, ?_⟩
  rw [(hL p).2 χ] at hχ
  intro he
  apply hχ
  refine (MeasureTheory.integral_congr_ae ?_).trans he
  exact .of_forall fun x ↦ by
    change p x * star (χ x : ℂ) = (((χ x)⁻¹ : Circle) : ℂ) * p x
    rw [Circle.coe_inv_eq_conj, Complex.star_def, mul_comm]

/-- Paper: Definitions 7.3.2.1(1) and 7.3.2.3(1), pp. 351, 355.
Every neighborhood of zero contains the support of a compact Schwartz–Bruhat
bump vanishing at zero and having nonzero additive Tamagawa integral.
One can place a nonnegative bump near a nonzero point in the neighborhood. -/
theorem sLocalPWTests_moments_surjective_zero_bump
    {F : Type*} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (K : Set (SAdeleRing F S)) (hK : K ∈ 𝓝 0) :
    ∃ h : SchwartzBruhat (Multiplicative (SAdeleRing F S)),
      HasCompactSupport h.val ∧ tsupport h.val ⊆ Multiplicative.toAdd ⁻¹' K ∧
      h (Multiplicative.ofAdd 0) = 0 ∧
      MeasureTheory.integral (sAdditiveTamagawaMeasure F S)
        (fun x ↦ h (Multiplicative.ofAdd x)) ≠ 0 := by
  classical
  let A := SAdeleRing F S
  let G := Multiplicative A
  let w : InfinitePlace F := Classical.arbitrary _
  have hi := InfinitePlace.Completion.isometry_extensionEmbedding w
  let : NontriviallyNormedField w.Completion := ⟨⟨2, by
    rw [← hi.norm_map_of_map_zero (map_zero _) (2 : w.Completion), map_ofNat]
    norm_num⟩⟩
  let j (z : w.Completion) : A := (Pi.single w z, 0)
  have hj : Continuous j := (continuous_single w).prodMk continuous_const
  have h0 : j 0 = 0 := by
    change (Pi.single w 0, (0 : (v : S) → v.val.adicCompletion F)) = (0, 0)
    rw [Pi.single_zero]
  have hnear : ∀ᶠ z in 𝓝[≠] (0 : w.Completion), j z ∈ interior K :=
    ((hj.tendsto' _ _ h0).mono_left nhdsWithin_le_nhds) (interior_mem_nhds.mpr hK)
  obtain ⟨z, hzK, hz⟩ := (hnear.and (self_mem_nhdsWithin :
    {0}ᶜ ∈ 𝓝[≠] (0 : w.Completion))).exists
  have hjz : j z ≠ 0 := by
    intro he
    have hz0 : Pi.single w z w = (0 : w.Completion) := congrArg (fun a : A ↦ a.1 w) he
    exact hz (Set.mem_singleton_iff.mpr ((Pi.single_eq_same w z).symm.trans hz0))
  let (v : HeightOneSpectrum (𝓞 F)) : MeasurableSpace (v.adicCompletion F) := borel _
  let (v : InfinitePlace F) : MeasurableSpace v.Completion := borel _
  let : MeasurableSpace (InfiniteAdeleRing F) :=
    inferInstanceAs (MeasurableSpace ((v : InfinitePlace F) → v.Completion))
  let : MeasurableSpace A := inferInstanceAs
    (MeasurableSpace (InfiniteAdeleRing F × ((v : S) → v.val.adicCompletion F)))
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (v : InfinitePlace F) : SecondCountableTopology v.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.secondCountableTopology
  let : SecondCountableTopology G := inferInstanceAs (SecondCountableTopology
    (((v : InfinitePlace F) → v.Completion) × ((v : S) → v.val.adicCompletion F)))
  let μ : MeasureTheory.Measure G := sAdditiveTamagawaMeasure F S
  obtain ⟨hT₂, hLC, hBor, hHaar, -⟩ := sAdele_fourierMeasure (F := F) (S := S)
  let : T2Space G := hT₂
  let : LocallyCompactSpace G := hLC
  let : BorelSpace G := hBor
  let : μ.IsHaarMeasure := hHaar
  let U : Set G := (Multiplicative.toAdd ⁻¹' interior K) ∩ {Multiplicative.ofAdd (0 : A)}ᶜ
  have hU : IsOpen U := (isOpen_interior.preimage continuous_toAdd).inter isClosed_singleton.isOpen_compl
  obtain ⟨p, hpc, hpU, hpx⟩ := sLocalPWTests_moments_surjective_bump
    (Multiplicative.ofAdd (j z)) U (hU.mem_nhds ⟨hzK, hjz⟩)
  have hp : p ≠ 0 := fun he ↦ zero_ne_one ((congrArg
    (fun f : SchwartzBruhat G ↦ f (Multiplicative.ofAdd (j z))) he).symm.trans hpx)
  obtain ⟨h, hs, hI⟩ := sLocalPWTests_moments_surjective_zero_bump_modulate μ p hp
  refine ⟨h, hpc.of_isClosed_subset isClosed_closure hs, fun x hx ↦
    interior_subset (hpU (hs hx)).1, ?_, hI⟩
  exact image_eq_zero_of_notMem_tsupport fun hx ↦ (hpU (hs hx)).2 rfl

open MeasureTheory in
/-- Paper: Definitions 7.3.2.1(1) and 7.3.2.3(1), pp. 351, 355.
Insertion of integer-ring indicators multiplies the Fourier value at zero by
one nonzero scalar, independent of the test.
The scalar is the product of the additive Tamagawa volumes of the inserted rings. -/
private theorem sLocalPWTests_moments_surjective_transition
    {F : Type*} [Field F] [NumberField F]
    {S T : Finset (HeightOneSpectrum (𝓞 F))} (hST : S ⊆ T) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ g : SchwartzBruhat (Multiplicative (SAdeleRing F S)),
      sAdeleSchwartzFourier (sAdeleSchwartzTransition F hST g) (Multiplicative.ofAdd 0) =
        c * sAdeleSchwartzFourier g (Multiplicative.ofAdd 0) := by
  classical
  obtain ⟨D, hd, rfl⟩ : ∃ D : Finset (HeightOneSpectrum (𝓞 F)),
      Disjoint S D ∧ T = S ∪ D :=
    ⟨T \ S, Finset.disjoint_sdiff, (Finset.union_sdiff_of_subset hST).symm⟩
  let (w : InfinitePlace F) : MeasurableSpace w.Completion := borel _
  let (w : InfinitePlace F) : BorelSpace w.Completion := ⟨rfl⟩
  let (v : HeightOneSpectrum (𝓞 F)) : MeasurableSpace (v.adicCompletion F) := borel _
  let (v : HeightOneSpectrum (𝓞 F)) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
  let (v : HeightOneSpectrum (𝓞 F)) : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
  let μ := finiteLocalAdditiveTamagawaMeasure F
  let (v : HeightOneSpectrum (𝓞 F)) : (μ v).IsAddHaarMeasure :=
    finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  let b (v : D) := (v.val.adicCompletionIntegers F : Set (v.val.adicCompletion F)).indicator (fun _ ↦ (1 : ℂ))
  refine ⟨∏ v : D, ∫ x, b v x ∂μ v, Finset.prod_ne_zero_iff.mpr ?_, fun g ↦ ?_⟩
  · intro v _
    let O := (v.val.adicCompletionIntegers F : Set (v.val.adicCompletion F))
    have ho : IsOpen O := Valued.isOpen_valuationSubring _
    have hc : IsCompact O := isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v.val)
    have hm : 0 < (μ v).real O := ENNReal.toReal_pos
      (ho.measure_pos (μ v) ⟨0, (v.val.adicCompletionIntegers F).zero_mem⟩).ne'
      (hc.measure_ne_top (μ := μ v))
    change (∫ x, O.indicator (fun _ ↦ (1 : ℂ)) x ∂μ v) ≠ 0
    rw [integral_indicator_const _ ho.measurableSet, Complex.real_smul, mul_one]
    exact Complex.ofReal_ne_zero.mpr hm.ne'
  rw [sAdeleSchwartzFourier_apply_zero, sAdeleSchwartzFourier_apply_zero, mul_comm]
  let (w : InfinitePlace F) : SigmaFinite (infiniteLocalAdditiveTamagawaMeasure F w) := by
    rw [infiniteLocalAdditiveTamagawaMeasure]
    split_ifs with hw
    · exact (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.toHomeomorph.measurableEmbedding.sigmaFinite_map
    · rw [two_nsmul]
      exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
        (InfinitePlace.not_isReal_iff_isComplex.mp hw)).symm.toHomeomorph.measurableEmbedding.sigmaFinite_map
  apply integral_prod_piFinsetUnion (Measure.pi (infiniteLocalAdditiveTamagawaMeasure F)) μ hd
    (fun z ↦ g (Multiplicative.ofAdd z)) b
  intro a x y
  rw [sAdeleSchwartzTransition_apply]
  let X (v : HeightOneSpectrum (𝓞 F)) := v.adicCompletion F
  let t := MeasurableEquiv.piFinsetUnion X hd (x, y)
  have hmem : (∀ w : ↥(S ∪ D), w.val ∉ S → t w ∈ w.val.adicCompletionIntegers F) ↔
      ∀ v : D, y v ∈ v.val.adicCompletionIntegers F := by
    constructor
    · intro h v
      have hv := h ⟨v.val, Finset.mem_union_right S v.property⟩
        (fun hs ↦ Finset.disjoint_left.mp hd hs v.property)
      simpa only [t, MeasurableEquiv.piFinsetUnion_right X hd v.property] using hv
    · intro h w hw
      have hv := (Finset.mem_union.mp w.property).resolve_left hw
      simpa only [t, MeasurableEquiv.piFinsetUnion_right X hd hv] using! h ⟨w.val, hv⟩
  change (if _ then g (Multiplicative.ofAdd (a, fun v : S ↦ t ⟨v.val, hST v.property⟩)) else 0) = _
  have hx : (fun v : S ↦ t ⟨v.val, hST v.property⟩) = x :=
    funext fun v ↦ MeasurableEquiv.piFinsetUnion_left X hd v.property _
  simp only [b, indicator_apply, Fintype.prod_boole, mul_ite, mul_one, mul_zero]
  exact if_congr hmem (congrArg (fun u ↦ g (Multiplicative.ofAdd (a, u))) hx) rfl

/-- Paper: Definitions 7.3.2.1(1) and 7.3.2.3(1), pp. 351, 355.
The two moments on the inserted test space can be specified independently whenever
the Fourier region contains a neighborhood of zero, as both positive levels do.
Deviation: This uses the integer-ring transition. -/
theorem sLocalPWTests_moments_surjective (hST : S ⊆ T) (K : Set (SAdeleRing F S))
    (hK : K ∈ 𝓝 0) (a b : ℂ) :
    ∃ f ∈ sLocalPWTests hST K, f (Multiplicative.ofAdd 0) = a ∧
      sAdeleSchwartzFourier f (Multiplicative.ofAdd 0) = b := by
  let G := Multiplicative (SAdeleRing F S)
  have hG := sAdele_fourierMeasure (F := F) (S := S)
  let : T2Space G := hG.1
  let : LocallyCompactSpace G := hG.2.1
  have hK' : Multiplicative.toAdd ⁻¹' K ∈ 𝓝 (Multiplicative.ofAdd (0 : SAdeleRing F S)) :=
    continuous_toAdd.continuousAt.preimage_mem_nhds hK
  obtain ⟨p, hpc, hpK, hp0⟩ :=
    sLocalPWTests_moments_surjective_bump (Multiplicative.ofAdd 0) _ hK'
  obtain ⟨q, hqc, hqK, hq0, hqI⟩ :=
    sLocalPWTests_moments_surjective_zero_bump S K hK
  obtain ⟨c, hc, htrans⟩ := sLocalPWTests_moments_surjective_transition (F := F) hST
  obtain ⟨L, hL⟩ := sLocal_fourier_continuousLinear (F := F) (S := S)
  let I := sAdeleSchwartzFourier q (Multiplicative.ofAdd 0)
  have hI : I ≠ 0 := by
    simpa only [I, sAdeleSchwartzFourier_apply_zero] using hqI
  let d := b / c
  let e := (a - d * sAdeleSchwartzFourier p (Multiplicative.ofAdd 0)) / I
  let u := e • q + d • p
  have hu0 : u (Multiplicative.ofAdd 0) = d := by
    change e * q (Multiplicative.ofAdd 0) + d * p (Multiplicative.ofAdd 0) = d
    rw [hq0, hp0, mul_zero, mul_one, zero_add]
  have huF : sAdeleSchwartzFourier u (Multiplicative.ofAdd 0) = a := by
    rw [← hL u]
    change L (e • q + d • p) (Multiplicative.ofAdd 0) = a
    rw [map_add, map_smul, map_smul]
    change e * L q (Multiplicative.ofAdd 0) + d * L p (Multiplicative.ofAdd 0) = a
    rw [hL q, hL p]
    change (a - d * sAdeleSchwartzFourier p (Multiplicative.ofAdd 0)) / I * I +
      d * sAdeleSchwartzFourier p (Multiplicative.ofAdd 0) = a
    rw [div_mul_cancel₀ _ hI, sub_add_cancel]
  have huc : HasCompactSupport u.val :=
    (hqc.smul_left (f := fun _ ↦ e)).add (hpc.smul_left (f := fun _ ↦ d))
  have huK : tsupport u.val ⊆ Multiplicative.toAdd ⁻¹' K :=
    (tsupport_add _ _).trans (union_subset
      ((tsupport_smul_subset_right (fun _ ↦ e) q.val).trans hqK)
      ((tsupport_smul_subset_right (fun _ ↦ d) p.val).trans hpK))
  let g := sAdeleSchwartzFourier (sAdeleSchwartzFourier (sAdeleSchwartzFourier u))
  have hgF : sAdeleSchwartzFourier g = u := by
    apply Subtype.ext
    funext x
    change sAdeleSchwartzFourier (sAdeleSchwartzFourier
      (sAdeleSchwartzFourier (sAdeleSchwartzFourier u))) x = u x
    exact (sLocal_fourier_inversion (sAdeleSchwartzFourier (sAdeleSchwartzFourier u))
      x.toAdd).trans ((sLocal_fourier_inversion u (-x.toAdd)).trans
        (congrArg (fun y ↦ u (Multiplicative.ofAdd y)) (neg_neg x.toAdd)))
  have hg0 : g (Multiplicative.ofAdd 0) = a := by
    simpa only [g, sLocal_fourier_inversion, neg_zero] using huF
  refine ⟨sAdeleSchwartzTransition F hST g,
    (mem_sLocalPWTests hST K _).mpr ⟨g, rfl, ?_⟩, ?_, ?_⟩
  · rw [hgF]
    exact ⟨huc, huK⟩
  · rw [sAdeleSchwartzTransition_apply]
    rw [ite_eq_left (show ∀ w : T, w.val ∉ S →
      (0 : SAdeleRing F T).2 w ∈ w.val.adicCompletionIntegers F from
      fun w _ ↦ (w.val.adicCompletionIntegers F).zero_mem)]
    exact hg0
  · rw [htrans g, hgF, hu0]
    exact mul_div_cancel₀ b hc

local notation "level(" h ", " K ", " D ", " ω ")" =>
  (((sLocalPWTests h K ⊓ D).map (q(_, ω))).topologicalClosure)

/-- Paper: Definition 7.3.2.1(2), p. 351.
The absolute PW level is the closure of the theta image of box-limited tests.
The test constraint is the whole space or the common kernel of the two zero evaluations.
Deviation: Uses the integer-ring insertion of the cited transition. -/
def sLocalAbsolutePW (hST : S ⊆ T) (X : ℝ) (D : Submodule ℂ (B(T)))
    (ω : PontryaginDual J₁(T)) : Submodule ℂ (Θ(T, ω)) :=
  level(hST, sLocalPWBox S X, D, ω)

/-- Paper: Definition 7.3.2.1(2), p. 351.
The theta class of an inserted box-limited test satisfying the chosen test constraint
belongs to the absolute level.
Deviation: Uses the integer-ring insertion of the cited transition. -/
theorem sLocalAbsolutePW_mk_mem (hST : S ⊆ T) (X : ℝ) (D : Submodule ℂ (B(T)))
    (ω : PontryaginDual J₁(T)) (f : B(S)) (_hf : inBand(sLocalPWBox S X, f))
    (_hD : Π(hST) f ∈ D) : q(T, ω) (Π(hST) f) ∈ sLocalAbsolutePW hST X D ω :=
  Submodule.le_topologicalClosure _
    (Submodule.mem_map_of_mem ⟨Submodule.mem_map_of_mem (Submodule.subset_span _hf), _hD⟩)

section LocalFourierSupport

open Classical

private theorem sLocalAbsolutePW_fourier_transition_support {S T : Finset V} (hST : S ⊆ T)
    (g : B(S)) (y : SAdeleRing F T)
    (hy : sAdeleSchwartzFourier (Π(hST) g) (Multiplicative.ofAdd y) ≠ 0) :
    let yS : SAdeleRing F S := (y.1, fun w : S ↦ y.2 ⟨w.val, hST w.property⟩)
    sAdeleSchwartzFourier g (Multiplicative.ofAdd yS) ≠ 0 ∧
      ∀ v : {v : T // v.val ∉ S},
        ‖y.2 v.val‖ ≤
          (v.val.val.asIdeal.absNorm : ℝ) ^ multiplicity v.val.val.asIdeal (differentIdeal ℤ (𝓞 F)) := by
  intro yS
  let (w : InfinitePlace F) : MeasurableSpace w.Completion := borel _
  let (v : HeightOneSpectrum (𝓞 F)) : MeasurableSpace (v.adicCompletion F) := borel _
  let (w : InfinitePlace F) : BorelSpace w.Completion := ⟨rfl⟩
  let (v : HeightOneSpectrum (𝓞 F)) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
  let (v : HeightOneSpectrum (𝓞 F)) : ProperSpace (v.adicCompletion F) :=
    properSpace_adicCompletion v
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let (w : InfinitePlace F) : (infiniteLocalAdditiveTamagawaMeasure F w).IsAddHaarMeasure :=
    infiniteLocalAdditiveTamagawaMeasure_haar F w
  let (v : HeightOneSpectrum (𝓞 F)) :
      (finiteLocalAdditiveTamagawaMeasure F v).IsAddHaarMeasure :=
    finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  let : MeasurableSpace (InfiniteAdeleRing F) :=
    inferInstanceAs (MeasurableSpace ((w : InfinitePlace F) → w.Completion))
  let (w : InfinitePlace F) :
      MeasureTheory.SigmaFinite (infiniteLocalAdditiveTamagawaMeasure F w) :=
    inferInstanceAs (MeasureTheory.SigmaFinite (infiniteLocalAdditiveTamagawaMeasure F w))
  let (v : HeightOneSpectrum (𝓞 F)) :
      MeasureTheory.SigmaFinite (finiteLocalAdditiveTamagawaMeasure F v) :=
    inferInstanceAs (MeasureTheory.SigmaFinite (finiteLocalAdditiveTamagawaMeasure F v))
  let μArch := MeasureTheory.Measure.pi (infiniteLocalAdditiveTamagawaMeasure F)
  let μS := MeasureTheory.Measure.pi (fun w : S ↦ finiteLocalAdditiveTamagawaMeasure F w.val)
  let μT := MeasureTheory.Measure.pi (fun v : T ↦ finiteLocalAdditiveTamagawaMeasure F v.val)
  let μP := MeasureTheory.Measure.pi (fun v : {v : T // v.val ∈ S} ↦
    finiteLocalAdditiveTamagawaMeasure F v.val.val)
  let μU := MeasureTheory.Measure.pi (fun v : {v : T // v.val ∉ S} ↦
    finiteLocalAdditiveTamagawaMeasure F v.val.val)
  let eS : S ≃ {v : T // v.val ∈ S} :=
    { toFun := fun w ↦ ⟨⟨w.val, hST w.property⟩, w.property⟩
      invFun := fun v ↦ ⟨v.val.val, v.property⟩
      left_inv := fun ⟨_, _⟩ ↦ rfl
      right_inv := fun ⟨⟨_, _⟩, _⟩ ↦ rfl }
  let B : T → Type _ := fun v ↦ v.val.adicCompletion F
  let e1 : ((v : T) → B v) ≃ᵐ
      ((v : {v : T // v.val ∈ S}) → B v.val) × ((v : {v : T // v.val ∉ S}) → B v.val) :=
    MeasurableEquiv.piEquivPiSubtypeProd B (fun v : T ↦ v.val ∈ S)
  let e2 : ((w : S) → B ⟨w.val, hST w.property⟩) ≃ᵐ ((v : {v : T // v.val ∈ S}) → B v.val) :=
    MeasurableEquiv.piCongrLeft (fun v : {v : T // v.val ∈ S} ↦ B v.val) eS
  let eFin : (((w : S) → B ⟨w.val, hST w.property⟩) ×
      ((v : {v : T // v.val ∉ S}) → B v.val)) ≃ᵐ ((v : T) → B v) :=
    (e2.prodCongr (MeasurableEquiv.refl _)).trans e1.symm
  let eTotal : (SAdeleRing F S × ((v : {v : T // v.val ∉ S}) → B v.val)) ≃ᵐ SAdeleRing F T :=
    (MeasurableEquiv.prodAssoc).trans ((MeasurableEquiv.refl _).prodCongr eFin)
  have he1 : MeasureTheory.MeasurePreserving e1 μT (μP.prod μU) :=
    MeasureTheory.measurePreserving_piEquivPiSubtypeProd
      (fun v : T ↦ finiteLocalAdditiveTamagawaMeasure F v.val) (fun v : T ↦ v.val ∈ S)
  have he2 : MeasureTheory.MeasurePreserving e2 μS μP :=
    MeasureTheory.measurePreserving_piCongrLeft
      (fun v : {v : T // v.val ∈ S} ↦ finiteLocalAdditiveTamagawaMeasure F v.val.val) eS
  have heFin : MeasureTheory.MeasurePreserving eFin (μS.prod μU) μT :=
    he1.symm.comp (he2.prod (MeasureTheory.MeasurePreserving.id μU))
  have heTotal : MeasureTheory.MeasurePreserving eTotal ((μArch.prod μS).prod μU) (μArch.prod μT) :=
    ((MeasureTheory.MeasurePreserving.id μArch).prod heFin).comp
      (MeasureTheory.measurePreserving_prodAssoc μArch μS μU)
  let Φ : SAdeleRing F T → ℂ := fun x ↦
    (Π(hST) g) (Multiplicative.ofAdd x) * star (sAdeleStandardCharacter F T (x * y) : ℂ)
  let H : SAdeleRing F S → ℂ := fun xS ↦
    g (Multiplicative.ofAdd xS) * star (sAdeleStandardCharacter F S (xS * yS) : ℂ)
  let b : (v : {v : T // v.val ∉ S}) → B v.val → ℂ := fun v xv ↦
    ((v.val.val.adicCompletionIntegers F : Set (B v.val)).indicator (fun _ ↦ (1 : ℂ)) xv) *
      star (finiteLocalStandardCharacter F v.val.val (xv * y.2 v.val) : ℂ)
  have hΦ (p : SAdeleRing F S × ((v : {v : T // v.val ∉ S}) → B v.val)) :
      Φ (eTotal p) = H p.1 * ∏ v : {v : T // v.val ∉ S}, b v (p.2 v) := by
    rcases p with ⟨⟨aArch, aS⟩, aU⟩
    let x := eTotal ((aArch, aS), aU)
    have hx1 : x.1 = aArch := rfl
    have hxS (w : S) : x.2 ⟨w.val, hST w.property⟩ = aS w := by
      change (e1.symm (e2 aS, aU)) ⟨w.val, hST w.property⟩ = aS w
      have hw : e1.symm (e2 aS, aU) (eS w).val = (e2 aS) (eS w) := by
        change (Equiv.piEquivPiSubtypeProd (fun v : T ↦ v.val ∈ S) B).symm
          (e2 aS, aU) (eS w).val = _
        simp [Equiv.piEquivPiSubtypeProd_symm_apply, (eS w).property]
      refine hw.trans ?_
      exact Equiv.piCongrLeft_apply_apply (fun v : {v : T // v.val ∈ S} ↦ B v.val) eS aS w
    have hxU (v : {v : T // v.val ∉ S}) : x.2 v.val = aU v := by
      change (Equiv.piEquivPiSubtypeProd (fun v : T ↦ v.val ∈ S) B).symm (e2 aS, aU) v.val = aU v
      simp [Equiv.piEquivPiSubtypeProd_symm_apply, v.property]
    have hproj : (x.1, fun w : S ↦ x.2 ⟨w.val, hST w.property⟩) = (aArch, aS) :=
      Prod.ext hx1 (funext hxS)
    have htrans : (Π(hST) g) (Multiplicative.ofAdd x) =
        g (Multiplicative.ofAdd (aArch, aS)) *
          ∏ v : {v : T // v.val ∉ S},
            ((v.val.val.adicCompletionIntegers F : Set (B v.val)).indicator
              (fun _ ↦ (1 : ℂ)) (aU v)) := by
      rw [sAdeleSchwartzTransition_apply, hproj]
      by_cases hmem : ∀ w : T, w.val ∉ S → x.2 w ∈ w.val.adicCompletionIntegers F
      · rw [ite_eq_left hmem]
        have hprod : (∏ v : {v : T // v.val ∉ S},
            ((v.val.val.adicCompletionIntegers F : Set (B v.val)).indicator
              (fun _ ↦ (1 : ℂ)) (aU v))) = 1 := by
          refine Finset.prod_eq_one fun v _ ↦ Set.indicator_of_mem ?_ _
          rw [← hxU v]
          exact hmem v.val v.property
        rw [hprod, mul_one]
      · rw [ite_eq_right hmem]
        push Not at hmem
        rcases hmem with ⟨w, hwS, hxw⟩
        have hprod : (∏ v : {v : T // v.val ∉ S},
            ((v.val.val.adicCompletionIntegers F : Set (B v.val)).indicator
              (fun _ ↦ (1 : ℂ)) (aU v))) = 0 := by
          refine Finset.prod_eq_zero (Finset.mem_univ (⟨w, hwS⟩ : {v : T // v.val ∉ S})) ?_
          apply Set.indicator_of_notMem
          simpa only [SetLike.mem_coe, ← hxU ⟨w, hwS⟩] using hxw
        rw [hprod, mul_zero]
    have hchar : (sAdeleStandardCharacter F T (x * y) : ℂ) =
        (sAdeleStandardCharacter F S ((aArch, aS) * yS) : ℂ) *
          ∏ v : {v : T // v.val ∉ S},
            (finiteLocalStandardCharacter F v.val.val (aU v * y.2 v.val) : ℂ) := by
      unfold sAdeleStandardCharacter
      have hsplit := Fintype.prod_subtype_mul_prod_subtype (fun v : T ↦ v.val ∈ S)
        (fun v : T ↦ finiteLocalStandardCharacter F v.val ((x * y).2 v))
      have hfst : (∏ w : InfinitePlace F,
          adeleStandardCharacter F (Pi.single w ((x * y).1 w), 0)) =
          (∏ w : InfinitePlace F,
            adeleStandardCharacter F (Pi.single w (((aArch, aS) * yS).1 w), 0)) := by
        refine Finset.prod_congr rfl fun w _ ↦ ?_
        rw [Prod.fst_mul, Prod.fst_mul, hx1]
      have hsub : (∏ v : {v : T // v.val ∈ S},
          finiteLocalStandardCharacter F v.val.val ((x * y).2 v.val)) =
          ∏ w : S, finiteLocalStandardCharacter F w.val (((aArch, aS) * yS).2 w) := by
        refine Fintype.prod_equiv eS.symm _ _ fun v ↦ ?_
        change finiteLocalStandardCharacter F v.val.val (x.2 v.val * y.2 v.val) =
          finiteLocalStandardCharacter F v.val.val (aS ⟨v.val.val, v.property⟩ * y.2 v.val)
        rw [← hxS ⟨v.val.val, v.property⟩]
      have hsnd : (∏ v : {v : T // v.val ∉ S},
          finiteLocalStandardCharacter F v.val.val ((x * y).2 v.val)) =
          ∏ v : {v : T // v.val ∉ S},
            finiteLocalStandardCharacter F v.val.val (aU v * y.2 v.val) := by
        refine Finset.prod_congr rfl fun v _ ↦ ?_
        change finiteLocalStandardCharacter F v.val.val (x.2 v.val * y.2 v.val) = _
        rw [hxU v]
      have hcoe : (↑(∏ v : {v : T // v.val ∉ S},
            finiteLocalStandardCharacter F v.val.val (aU v * y.2 v.val)) : ℂ) =
          ∏ v : {v : T // v.val ∉ S},
            (finiteLocalStandardCharacter F v.val.val (aU v * y.2 v.val) : ℂ) :=
        map_prod Circle.coeHom _ Finset.univ
      rw [← hsplit, hfst, hsub, hsnd]
      simp only [Circle.coe_mul]
      rw [← mul_assoc]
      exact congrArg (fun z : ℂ ↦ _ * z) hcoe
    have hstar : star (sAdeleStandardCharacter F T (x * y) : ℂ) =
        star (sAdeleStandardCharacter F S ((aArch, aS) * yS) : ℂ) *
          ∏ v : {v : T // v.val ∉ S},
            star (finiteLocalStandardCharacter F v.val.val (aU v * y.2 v.val) : ℂ) := by
      rw [hchar, star_mul', star_prod]
    dsimp only [Φ]
    rw [htrans, hstar, Finset.prod_mul_distrib]
    dsimp only [H, b]
    ring
  have hfact : sAdeleSchwartzFourier (Π(hST) g) (Multiplicative.ofAdd y) =
      sAdeleSchwartzFourier g (Multiplicative.ofAdd yS) *
        ∏ v : {v : T // v.val ∉ S},
          tamagawaFourier (finiteLocalAdditiveTamagawaMeasure F v.val.val)
            (finiteLocalStandardCharacter F v.val.val)
            ((v.val.val.adicCompletionIntegers F : Set (B v.val)).indicator fun _ ↦ (1 : ℂ))
            (y.2 v.val) := by
    calc
      sAdeleSchwartzFourier (Π(hST) g) (Multiplicative.ofAdd y)
        = ∫ x : SAdeleRing F T, Φ x ∂(μArch.prod μT) := rfl
      _ = ∫ p : SAdeleRing F S × ((v : {v : T // v.val ∉ S}) → B v.val), Φ (eTotal p)
            ∂((μArch.prod μS).prod μU) := (heTotal.integral_comp' Φ).symm
      _ = ∫ p : SAdeleRing F S × ((v : {v : T // v.val ∉ S}) → B v.val),
            H p.1 * ∏ v : {v : T // v.val ∉ S}, b v (p.2 v) ∂((μArch.prod μS).prod μU) := by
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hΦ)
      _ = (∫ xS : SAdeleRing F S, H xS ∂(μArch.prod μS)) *
            ∫ aU : (v : {v : T // v.val ∉ S}) → B v.val,
              ∏ v : {v : T // v.val ∉ S}, b v (aU v) ∂μU :=
          MeasureTheory.integral_prod_mul (μ := μArch.prod μS) (ν := μU) H
            (fun aU ↦ ∏ v : {v : T // v.val ∉ S}, b v (aU v))
      _ = sAdeleSchwartzFourier g (Multiplicative.ofAdd yS) *
            ∏ v : {v : T // v.val ∉ S},
              tamagawaFourier (finiteLocalAdditiveTamagawaMeasure F v.val.val)
                (finiteLocalStandardCharacter F v.val.val)
                ((v.val.val.adicCompletionIntegers F : Set (B v.val)).indicator fun _ ↦ (1 : ℂ))
                (y.2 v.val) :=
          congrArg₂ (· * ·) rfl (MeasureTheory.integral_fintype_prod_eq_prod b)
  rw [hfact] at hy
  refine ⟨left_ne_zero_of_mul hy, fun v ↦ ?_⟩
  have hFT : tamagawaFourier (finiteLocalAdditiveTamagawaMeasure F v.val.val)
      (finiteLocalStandardCharacter F v.val.val)
      ((v.val.val.adicCompletionIntegers F : Set (B v.val)).indicator fun _ ↦ (1 : ℂ))
      (y.2 v.val) ≠ 0 := by
    intro hv
    apply right_ne_zero_of_mul hy
    exact Finset.prod_eq_zero (Finset.mem_univ v) hv
  rw [finiteLocalTamagawaFourier_integers] at hFT
  by_contra hle
  apply hFT
  simp only [Pi.smul_apply, smul_eq_mul, mul_eq_zero]
  right
  exact Set.indicator_of_notMem hle _

end LocalFourierSupport

section AbsoluteLevels

open Classical

/-- Paper: Proposition 7.3.2.2(1), p. 352.
Increasing the box size enlarges each of the two absolute PW levels. -/
theorem sLocalAbsolutePW_mono (hST : S ⊆ T) {X Y : ℝ} (_hXY : X ≤ Y)
    (D : Submodule ℂ (B(T))) (ω : PontryaginDual J₁(T)) :
    sLocalAbsolutePW hST X D ω ≤ sLocalAbsolutePW hST Y D ω := by
  have hbox : sLocalPWBox S X ⊆ sLocalPWBox S Y := fun _ hx ↦
    ⟨fun w ↦ (hx.1 w).trans _hXY, fun v ↦ (hx.2 v).trans _hXY⟩
  have hgen : {f : B(S) | inBand(sLocalPWBox S X, f)} ⊆
      {f : B(S) | inBand(sLocalPWBox S Y, f)} :=
    fun _ hf ↦ ⟨hf.1, hf.2.trans (Set.preimage_mono hbox)⟩
  have htests : sLocalPWTests hST (sLocalPWBox S X) ≤ sLocalPWTests hST (sLocalPWBox S Y) :=
    Submodule.map_mono (Submodule.span_mono hgen)
  exact Submodule.topologicalClosure_mono (Submodule.map_mono (inf_le_inf htests le_rfl))

private theorem sLocalZeroMomentTheta_eq_top_of_translate
    {E W : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup W] [Module ℂ W]
    (p : E →ₗ[ℂ] ℂ × ℂ) (θ : E →ₗ[ℂ] W) (t : E → E)
    (a b : ℂ) (ha : a ≠ 1) (hab : a ≠ b)
    (hp : ∀ f, p (t f) = ((p f).1, b * (p f).2)) (hθ : ∀ f, θ (t f) = a • θ f) :
    p.ker.map θ.ker.mkQ = ⊤ := by
  apply top_unique
  rintro x -
  obtain ⟨f, rfl⟩ := θ.ker.mkQ_surjective x
  -- The first difference kills evaluation at zero. The second kills the Fourier value at zero.
  let k := t f - f
  let h := t k - b • k
  have hk : (p k).1 = 0 := by simp [k, hp]
  have hh : h ∈ p.ker := by
    change p (t k - b • k) = 0
    rw [map_sub, map_smul, hp, sub_eq_zero]
    exact Prod.ext (by simp [hk]) (by simp)
  have hθk : θ k = (a - 1) • θ f := by simp [k, hθ, sub_smul]
  have hθh : θ h = ((a - b) * (a - 1)) • θ f := by
    change θ (t k - b • k) = _
    rw [map_sub, map_smul, hθ, ← sub_smul, hθk, smul_smul]
  let c := (a - b) * (a - 1)
  have hc : c ≠ 0 := mul_ne_zero (sub_ne_zero.mpr hab) (sub_ne_zero.mpr ha)
  refine ⟨c⁻¹ • h, p.ker.smul_mem _ hh, ?_⟩
  simp only [Submodule.mkQ_apply, Submodule.Quotient.eq]
  change θ (c⁻¹ • h - f) = 0
  rw [map_sub, map_smul, hθh]
  change c⁻¹ • (c • θ f) - θ f = 0
  rw [inv_smul_smul₀ hc, sub_self]

open MeasureTheory in
private theorem sLocalZeroMomentTheta_eq_top_fourier {F : Type*} [Field F] [NumberField F]
    {T : Finset (HeightOneSpectrum (𝓞 F))} (u : (SAdeleRing F T)ˣ) :
    ∃ b : ℝ≥0, ∀ f : SchwartzBruhat (Multiplicative (SAdeleRing F T)),
      sAdeleSchwartzFourier (schwartzBruhatUnitTranslate u f) (Multiplicative.ofAdd 0) =
        ((b : ℝ) : ℂ) * sAdeleSchwartzFourier f (Multiplicative.ofAdd 0) := by
  let A := SAdeleRing F T
  let G := Multiplicative A
  let (w : InfinitePlace F) : MeasurableSpace w.Completion := borel _
  let (v : HeightOneSpectrum (𝓞 F)) : MeasurableSpace (v.adicCompletion F) := borel _
  let : MeasurableSpace (InfiniteAdeleRing F) :=
    inferInstanceAs (MeasurableSpace ((w : InfinitePlace F) → w.Completion))
  let : MeasurableSpace A :=
    inferInstanceAs (MeasurableSpace (InfiniteAdeleRing F × ((v : T) → v.val.adicCompletion F)))
  let μ : Measure G := sAdditiveTamagawaMeasure F T
  obtain ⟨hT₂, hLC, hBor, hHaar, hReg⟩ := sAdele_fourierMeasure (F := F) (S := T)
  let : T2Space G := hT₂
  let : LocallyCompactSpace G := hLC
  let : BorelSpace G := hBor
  let : μ.IsHaarMeasure := hHaar
  let : μ.Regular := hReg
  let d : G ≃ₜ* G :=
    { toFun := fun x ↦ Multiplicative.ofAdd ((↑u⁻¹ : A) * x.toAdd)
      invFun := fun x ↦ Multiplicative.ofAdd ((u : A) * x.toAdd)
      left_inv := fun x ↦ Multiplicative.ext (by simp [← mul_assoc])
      right_inv := fun x ↦ Multiplicative.ext (by simp [← mul_assoc])
      map_mul' := fun x y ↦ Multiplicative.ext (mul_add _ _ _)
      continuous_toFun := continuous_ofAdd.comp (continuous_const.mul continuous_toAdd)
      continuous_invFun := continuous_ofAdd.comp (continuous_const.mul continuous_toAdd) }
  -- Dilation sends additive Haar measure to a nonnegative multiple of itself.
  let ν := μ.map d
  let : ν.IsHaarMeasure := d.isHaarMeasure_map μ
  let : ν.Regular := Measure.Regular.map d.toHomeomorph
  refine ⟨ν.haarScalarFactor μ, fun f ↦ ?_⟩
  rw [sAdeleSchwartzFourier_apply_zero, sAdeleSchwartzFourier_apply_zero]
  change (∫ x : G, f (d.toHomeomorph.toMeasurableEquiv x) ∂μ) = _ * ∫ x : G, f x ∂μ
  rw [← integral_map_equiv d.toHomeomorph.toMeasurableEquiv (fun x ↦ f x)]
  change (∫ x : G, f x ∂ν) = _
  calc
    _ = ∫ x : G, f x ∂(ν.haarScalarFactor μ • μ) :=
      congrArg (fun m : Measure G ↦ ∫ x : G, f x ∂m)
        (Measure.isMulLeftInvariant_eq_smul_of_regular ν μ)
    _ = _ := by
      rw [integral_smul_nnreal_measure]
      rfl

/-- Paper: Equation (7.3.3.25), p. 363.
For a nontrivial norm-one character the tests with both zero moments
have the same homogeneous theta image as the unrestricted tests. -/
theorem sLocalZeroMomentTheta_eq_top (ω : PontryaginDual J₁(T)) (_hω : ω ≠ 1) :
    (Z₀(T)).map (q(T, ω)) = ⊤ := by
  have hex : ∃ h : J₁(T), (ω h : ℂ) ≠ 1 :=
    not_forall.mp fun hall ↦ _hω (PontryaginDual.ext fun x ↦ Subtype.ext (hall x))
  obtain ⟨h, hh⟩ := hex
  obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective h.val
  obtain ⟨b, hb⟩ := sLocalZeroMomentTheta_eq_top_fourier u
  have hne : (ω h : ℂ) ≠ ((b : ℝ) : ℂ) := by
    intro he
    have hb1 : (b : ℝ) = 1 :=
      (Real.norm_of_nonneg b.property).symm.trans
        ((Complex.norm_real _).symm.trans ((congrArg norm he).symm.trans (Circle.norm_coe _)))
    exact hh (he.trans (by exact_mod_cast hb1))
  apply sLocalZeroMomentTheta_eq_top_of_translate
    ((sAdelePolarValues_isLinear (F := F) (S := T)).mk' _)
    (sLocalHomogeneousAdelicThetaLinearMap F T ω)
    (schwartzBruhatUnitTranslate u) (ω h : ℂ) ((b : ℝ) : ℂ) hh hne
  · intro f
    apply Prod.ext
    · exact congrArg f (congrArg Multiplicative.ofAdd (mul_zero _))
    · exact hb f
  · exact sLocalHomogeneousTheta_unitTranslate ω h u hu


/-- Fourier inversion gives a continuous inverse on the local test space. -/
private theorem sLocalAbsolutePW_fourier_inv (f : B(S)) :
    sAdeleSchwartzFourier (sAdeleSchwartzFourier (sAdeleSchwartzFourier
      (sAdeleSchwartzFourier f))) = f := by
  apply Subtype.ext
  funext x
  exact (sLocal_fourier_inversion (sAdeleSchwartzFourier (sAdeleSchwartzFourier f))
    x.toAdd).trans ((sLocal_fourier_inversion f (-x.toAdd)).trans
      (congrArg (fun y ↦ f (Multiplicative.ofAdd y)) (neg_neg x.toAdd)))

private theorem sLocalAbsolutePW_transition_self (f : B(S)) : sAdeleSchwartzTransition F (le_rfl (a := S)) f = f := by
  classical
  apply Subtype.ext
  funext x
  rw [← show Multiplicative.ofAdd x.toAdd = x from rfl, sAdeleSchwartzTransition_apply,
    ite_eq_left (fun w hw ↦ (hw w.property).elim)]

/-- Tests with compact Fourier support approximate every local test. -/
private theorem sLocalAbsolutePW_fourier_compact_seq (f : B(S)) :
    ∃ fₙ : ℕ → B(S), (∀ n, HasCompactSupport (sAdeleSchwartzFourier (fₙ n)).val) ∧
      Tendsto fₙ atTop (𝓝 f) := by
  obtain ⟨L, hL⟩ := sLocal_fourier_continuousLinear (F := F) (S := S)
  obtain ⟨u, hu, ht⟩ := exists_sAdeleSchwartz_compact_support_seq (sAdeleSchwartzFourier f)
  let M := L.comp (L.comp L)
  have hM (g : B(S)) : M g = sAdeleSchwartzFourier (sAdeleSchwartzFourier (sAdeleSchwartzFourier g)) := by
    change L (L (L g)) = _
    rw [hL, hL, hL]
  refine ⟨M ∘ u, fun n ↦ ?_, ?_⟩
  · change HasCompactSupport (sAdeleSchwartzFourier (M (u n))).val
    rw [hM, sLocalAbsolutePW_fourier_inv]
    exact hu n
  · have he := M.continuous.continuousAt.tendsto.comp ht
    rwa [hM, sLocalAbsolutePW_fourier_inv] at he

/-- The two zero moments can be imposed by subtracting fixed tests whose Fourier
transforms are compactly supported. -/
private theorem sLocalAbsolutePW_fourier_compact_seq_polar (f : Z₀(S)) :
    ∃ fₙ : ℕ → B(S), (∀ n, fₙ n ∈ Z₀(S) ∧ HasCompactSupport (sAdeleSchwartzFourier (fₙ n)).val) ∧
      Tendsto fₙ atTop (𝓝 f.val) := by
  obtain ⟨L, hL⟩ := sLocal_fourier_continuousLinear (F := F) (S := S)
  let P (g : B(S)) := g (Multiplicative.ofAdd 0)
  let Q (g : B(S)) := L g (Multiplicative.ofAdd 0)
  let K : Set (SAdeleRing F S) := univ
  obtain ⟨a, haK, haP, haQ⟩ := sLocalPWTests_moments_surjective (F := F) (S := S) (T := S)
    le_rfl K univ_mem 1 0
  obtain ⟨b, hbK, hbP, hbQ⟩ := sLocalPWTests_moments_surjective (F := F) (S := S) (T := S)
    le_rfl K univ_mem 0 1
  have hc (z : B(S)) (hz : z ∈ sLocalPWTests le_rfl K) :
      HasCompactSupport (L z).val := by
    obtain ⟨w, hw, hwc, -⟩ := (mem_sLocalPWTests le_rfl K z).mp hz
    rw [sLocalAbsolutePW_transition_self] at hw
    rw [hL, ← hw]
    exact hwc
  obtain ⟨u, hu, ht⟩ := sLocalAbsolutePW_fourier_compact_seq f.val
  let r (g : B(S)) := g - P g • a - Q g • b
  have hP : Continuous P := continuous_sAdeleSchwartz_eval 0
  have hQ : Continuous Q := hP.comp L.continuous
  have hr : Continuous r := (continuous_id.sub (hP.smul continuous_const)).sub (hQ.smul continuous_const)
  have hf := (mem_sAdelePolarSubspace f.val).mp f.property
  have hrf : r f.val = f.val := by
    change f.val - (f.val (Multiplicative.ofAdd 0)) • a - (L f.val (Multiplicative.ofAdd 0)) • b = f.val
    rw [hL, hf.1, hf.2, zero_smul, zero_smul, sub_zero, sub_zero]
  refine ⟨r ∘ u, fun n ↦ ?_, ?_⟩
  · have he : L (r (u n)) = L (u n) - P (u n) • L a - Q (u n) • L b := by
      change L (u n - P (u n) • a - Q (u n) • b) = _
      simp only [map_sub, map_smul]
    change r (u n) ∈ Z₀(S) ∧ HasCompactSupport (sAdeleSchwartzFourier (r (u n))).val
    constructor
    · apply (mem_sAdelePolarSubspace _).mpr
      constructor
      · change P (u n) - P (u n) * a (Multiplicative.ofAdd 0) -
          Q (u n) * b (Multiplicative.ofAdd 0) = 0
        rw [haP, hbP, mul_one, mul_zero, sub_self, sub_zero]
      · rw [← hL, he]
        change Q (u n) - P (u n) * L a (Multiplicative.ofAdd 0) -
          Q (u n) * L b (Multiplicative.ofAdd 0) = 0
        rw [hL, hL, haQ, hbQ, mul_zero, mul_one, sub_zero, sub_self]
    · rw [← hL, he]
      have huc : HasCompactSupport (L (u n)).val := (hL (u n)).symm ▸ hu n
      exact (huc.sub ((hc a haK).smul_left (f := fun _ ↦ P (u n)))).sub
        ((hc b hbK).smul_left (f := fun _ ↦ Q (u n)))
  · have h := hr.continuousAt.tendsto.comp ht
    rwa [hrf] at h

/-- A compact set is contained in a sufficiently large Fourier box. -/
private theorem sLocalAbsolutePW_compact_box {K : Set (Multiplicative (SAdeleRing F S))}
    (hK : IsCompact K) : ∃ X > 0, K ⊆ Multiplicative.toAdd ⁻¹' sLocalPWBox S X := by
  let N (x : SAdeleRing F S) :=
    (∑ w : InfinitePlace F, ‖x.1 w‖ ^ w.mult) + ∑ v : S, ‖x.2 v‖
  have hN : Continuous N := (continuous_finsetSum _ fun w _ ↦
    ((continuous_apply w).comp continuous_fst).norm.pow w.mult).add
      (continuous_finsetSum _ fun v _ ↦ ((continuous_apply v).comp continuous_snd).norm)
  obtain ⟨R, hR⟩ := (hK.image (hN.comp continuous_toAdd)).bddAbove
  refine ⟨max R 1, zero_lt_one.trans_le (le_max_right _ _), fun x hx ↦ ?_⟩
  have hxR : N x.toAdd ≤ max R 1 := (hR (mem_image_of_mem _ hx)).trans (le_max_left _ _)
  refine ⟨fun w ↦ ?_, fun v ↦ ?_⟩
  · exact (Finset.single_le_sum (fun i _ ↦ by positivity) (Finset.mem_univ w)).trans
      ((le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)).trans hxR)
  · exact (Finset.single_le_sum (fun i _ ↦ norm_nonneg _) (Finset.mem_univ v)).trans
      ((le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ ↦ by positivity)).trans hxR)

private theorem sLocalAbsolutePW_insert_polar (hST : S ⊆ T) (f : B(S)) :
    Π(hST) f ∈ Z₀(T) ↔ f ∈ Z₀(S) := by
  classical
  obtain ⟨c, hc, hF⟩ := sLocalPWTests_moments_surjective_transition (F := F) hST
  have h0 : Π(hST) f (Multiplicative.ofAdd 0) = f (Multiplicative.ofAdd 0) := by
    rw [sAdeleSchwartzTransition_apply, ite_eq_left (fun w _ ↦ (w.val.adicCompletionIntegers F).zero_mem)]
    rfl
  rw [mem_sAdelePolarSubspace, mem_sAdelePolarSubspace, h0, hF, mul_eq_zero, or_iff_right hc]

open MeasureTheory in
/-- On the trivial local component the theta kernel has both moments zero, as
seen by continuing the class into the global trivial-character residue map. -/
private theorem sLocalAbsolutePW_trivial_kernel_polar (f : B(T))
    (hf : f ∈ (sLocalHomogeneousAdelicThetaLinearMap F T 1).ker) :
    f ∈ Z₀(T) := by
  let c : unramifiedOutside F T := ⟨1, (mem_unramifiedOutside_iff F T 1).mpr (fun _ _ _ ↦ rfl)⟩
  have hc : ∀ x : C₁, c.val x.val = ((1 : PontryaginDual C₁) x : ℂ) := fun _ ↦ rfl
  let hω : NormOneCharacterUnramifiedOutside (F := F) 1 T := ⟨c, hc⟩
  have htriv : sLocalNormOneCharacter (F := F) T 1 hω = 1 := by
    apply PontryaginDual.ext
    intro y
    apply Subtype.ext
    have h := sLocalNormOneCharacter_eq_sIdeleRestriction 1 c hc y
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective y.val
    rw [← hg, sIdeleRestriction_mk] at h
    exact h
  have hf' : f ∈ (sLocalHomogeneousAdelicThetaLinearMap F T
      (sLocalNormOneCharacter (F := F) T 1 hω)).ker := by rw [htriv]; exact hf
  let G := sAdeleSchwartzToGlobal F T f
  have hG : G ∈ (homogeneousAdelicThetaLinearMap F 1).ker :=
    sLocalHomogeneousThetaToGlobal_preserves_kernel hω hf'
  obtain ⟨R, hR, -, -, -⟩ := globalConverse_normTwist_exact (F := F)
  have hp := hR G
  rw [show (LinearMap.ker (homogeneousAdelicThetaLinearMap F 1)).mkQ G = 0 from
    (Submodule.Quotient.mk_eq_zero (homogeneousAdelicThetaLinearMap F 1).ker).mpr hG, map_zero] at hp
  let : MeasurableSpace (IdeleClassGroup (𝓞 F) F) := borel _
  let μ := normOneIdeleClassTamagawaMeasure F
  let : CompactSpace C₁ := (ideleClassGroup_finiteness F).2.1
  let : μ.IsHaarMeasure := (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  have hm : ((μ univ).toReal : ℂ) ≠ 0 := by
    exact_mod_cast (measureReal_univ_pos (μ := μ)).ne'
  have hG0 : G (Multiplicative.ofAdd 0) = 0 :=
    (mul_eq_zero.mp (congrArg Prod.fst hp.symm)).resolve_left (neg_ne_zero.mpr hm)
  have hGF : adeleSchwartzFourier G (Multiplicative.ofAdd 0) = 0 :=
    (mul_eq_zero.mp (congrArg Prod.snd hp.symm)).resolve_left hm
  obtain ⟨m, hm₀, hM⟩ := sAdeleSchwartzToGlobal_fourier_zero_scale (F := F) (S := T)
  apply (mem_sAdelePolarSubspace f).mpr
  constructor
  · change sAdeleSchwartzToGlobal F T f (Multiplicative.ofAdd 0) = 0 at hG0
    rwa [sAdeleSchwartzToGlobal_apply, ite_eq_left (fun v _ ↦ (v.adicCompletionIntegers F).zero_mem),
      map_zero] at hG0
  · change adeleSchwartzFourier (sAdeleSchwartzToGlobal F T f) (Multiplicative.ofAdd 0) = 0 at hGF
    rw [hM] at hGF
    exact (mul_eq_zero.mp hGF).resolve_left hm₀

/-- Each larger-stage quotient representative can be replaced by an inserted
test with the same pole constraint. -/
private theorem sLocalAbsolutePW_exists_insert_rep
    (hST : S ⊆ T) (hPic : PicTrivial) (ω : PontryaginDual C₁)
    (hω : NormOneCharacterUnramifiedOutside ω S) (χ : PontryaginDual J₁(T))
    (hχ : χ = descend(hST, ω, hω))
    (f : B(T)) :
    ∃ g : B(S), q(T, χ) (Π(hST) g) = q(T, χ) f ∧ (f ∈ Z₀(T) → g ∈ Z₀(S)) := by
  classical
  rcases eq_or_lt_of_le hST with h | h
  · subst T
    exact ⟨f, congrArg (q(S, χ)) (sLocalAbsolutePW_transition_self f), id⟩
  · have hU : ∀ (x : J₁(T)) (u : relativeIntegralIdeleUnits F S T),
        x.val = QuotientGroup.mk u.val → χ x = 1 := by
      rw [hχ]
      exact sLocalHomogeneousThetaToGlobal_equiv_of_unramified_units hST hω
    obtain ⟨η, e, hη, he⟩ := sLocalHomogeneousThetaTransition_equiv_of_unramified h hPic χ hU
    let x := e.symm (q(T, χ) f)
    have hx (g : B(S)) (hg : q(S, η) g = x) : q(T, χ) (Π(hST) g) = q(T, χ) f :=
      (he g).symm.trans ((congrArg e hg).trans (e.apply_symm_apply _))
    by_cases ht : η = 1
    · obtain ⟨g, hg⟩ := (sLocalHomogeneousAdelicThetaLinearMap F S η).ker.mkQ_surjective x
      refine ⟨g, hx g hg, fun hf ↦ ?_⟩
      have ht' : χ = 1 := by
        apply PontryaginDual.ext
        intro y
        have h := hη y
        rw [ht] at h
        exact h.symm
      have hker : Π(hST) g - f ∈ (sLocalHomogeneousAdelicThetaLinearMap F T (1 : PontryaginDual J₁(T))).ker := by
        rw [← ht']
        apply (Submodule.Quotient.mk_eq_zero (sLocalHomogeneousAdelicThetaLinearMap F T χ).ker).mp
        change q(T, χ) (Π(hST) g - f) = 0
        rw [map_sub, hx g hg, sub_self]
      have hzero := sLocalAbsolutePW_trivial_kernel_polar (Π(hST) g - f) hker
      have hsum := (Z₀(T)).add_mem hzero hf
      rw [sub_add_cancel] at hsum
      exact (sLocalAbsolutePW_insert_polar hST g).mp hsum
    · have hy : x ∈ (Z₀(S)).map (q(S, η)) := by
        rw [sLocalZeroMomentTheta_eq_top η ht]
        exact Submodule.mem_top
      obtain ⟨g, hg, hq⟩ := Submodule.mem_map.mp hy
      exact ⟨g, hx g hq, fun _ ↦ hg⟩

private theorem sLocalAbsolutePW_push_seq (hST : S ⊆ T) (D : Submodule ℂ (B(T)))
    (χ : PontryaginDual J₁(T)) (g : B(S))
    (u : ℕ → B(S)) (hu : ∀ n, HasCompactSupport (sAdeleSchwartzFourier (u n)).val)
    (hD : ∀ n, Π(hST) (u n) ∈ D) (ht : Tendsto u atTop (𝓝 g)) :
    ∃ v : ℕ → Θ(T, χ), (∀ n, ∃ X > 0, v n ∈ sLocalAbsolutePW hST X D χ) ∧
      Tendsto v atTop (𝓝 (q(T, χ) (Π(hST) g))) := by
  refine ⟨fun n ↦ q(T, χ) (Π(hST) (u n)), fun n ↦ ?_, ?_⟩
  · obtain ⟨X, hX, hbox⟩ := sLocalAbsolutePW_compact_box (hu n)
    exact ⟨X, hX, sLocalAbsolutePW_mk_mem hST X D χ (u n) ⟨hu n, hbox⟩ (hD n)⟩
  · exact (((sLocalHomogeneousAdelicThetaLinearMap F T χ).ker.mkQL.continuous).comp
      (sAdeleSchwartzTransition_isEmbedding F hST).continuous).continuousAt.tendsto.comp ht

/-- Paper: Proposition 7.3.2.2(1), p. 352.
The union of the absolute PW levels is sequentially dense in the full or zero-moment
homogeneous theta space, according to the chosen test constraint.
Deviation: Uses integer-ring insertion, as required by the density argument and §6.2. -/
theorem sLocalAbsolutePW_seqDense {S₀ : Finset (HeightOneSpectrum (𝓞 F))}
    (hST : S ⊆ T) (_hT : T = S ∪ S₀)
    (_hdis : Disjoint S S₀) (_hsat : IsSaturatedPlaceSet (F := F) S₀)
    (_hPic : PicTrivial) (ω : PontryaginDual C₁) (hu : NormOneCharacterUnramifiedOutside ω S)
    (χ : PontryaginDual J₁(T)) (_hχ : χ = descend(hST, ω, hu))
    (D : Submodule ℂ (B(T))) (_hD : D = ⊤ ∨ D = Z₀(T)) :
    ∀ (x : Θ(T, χ)), x ∈ D.map (q(T, χ)) → ∃ u : ℕ → Θ(T, χ),
      (∀ n, ∃ X > 0, u n ∈ sLocalAbsolutePW hST X D χ) ∧
        Tendsto u atTop (𝓝 x) := by
  intro x hx
  obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hx
  obtain ⟨g, hg, hpol⟩ := sLocalAbsolutePW_exists_insert_rep hST _hPic ω hu χ _hχ f
  rcases _hD with rfl | rfl
  · obtain ⟨u, hu, ht⟩ := sLocalAbsolutePW_fourier_compact_seq g
    rw [← hg]
    exact sLocalAbsolutePW_push_seq hST ⊤ χ g u hu (fun _ ↦ Submodule.mem_top) ht
  · obtain ⟨u, hu, ht⟩ := sLocalAbsolutePW_fourier_compact_seq_polar ⟨g, hpol hf⟩
    rw [← hg]
    exact sLocalAbsolutePW_push_seq hST (Z₀(T)) χ g u (fun n ↦ (hu n).2)
      (fun n ↦ (sLocalAbsolutePW_insert_polar hST (u n)).mpr (hu n).1) ht

/-- Paper: Theorem 2.2.3.2, p. 82, and the proof of Proposition 7.3.2.2(2)–(3), p. 353.
The global Fourier transform of the global insertion of an S-local test vanishes at every
adele where the S-local Fourier transform vanishes at the projection, and at every adele
having a coordinate outside S beyond a fixed bound. The bounds are at least one and equal
to one at all but finitely many places.
The proof would integrate over the integer tail: translation by the omitted integer rings
leaves the inserted test invariant, so the transform vanishes off the annihilator of those
rings, and on the annihilator the tail integrates to a positive constant
(compare `tamagawaFourier_sAdeleLift` in `AppA_AlgebraicNT/Sec3.lean`, where the bound is
the absolute norm of the place raised to the exponent of the different). -/
private theorem sLocalAbsolutePW_globalSupport_fourier {F : Type*} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ D : HeightOneSpectrum (𝓞 F) → ℝ, (∀ v, 1 ≤ D v) ∧ (mulSupport D).Finite ∧
      ∀ (h : SchwartzBruhat (Multiplicative (SAdeleRing F S))) (y : AdeleRing (𝓞 F) F),
        adeleSchwartzFourier (sAdeleSchwartzToGlobal F S h) (Multiplicative.ofAdd y) ≠ 0 →
          sAdeleSchwartzFourier h (Multiplicative.ofAdd (adeleProjection F S y)) ≠ 0 ∧
            ∀ v, v ∉ S → ‖y.2 v‖ ≤ D v := by
  classical
  let D (v : HeightOneSpectrum (𝓞 F)) :=
    (v.asIdeal.absNorm : ℝ) ^ multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F))
  refine ⟨D, fun v ↦ one_le_pow₀ (by exact_mod_cast (HeightOneSpectrum.one_lt_absNorm v).le), ?_, ?_⟩
  · apply (Ideal.finite_factors (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F))).subset
    intro v hv
    by_contra hn
    exact hv (by simp [D, multiplicity_eq_zero_of_not_dvd hn])
  · obtain ⟨c, _, hc⟩ := adeleSchwartzFourier_sAdeleSchwartzToGlobal (F := F) (S := S)
    intro h y hy
    rw [hc] at hy
    split at hy
    · rename_i htail
      exact ⟨fun hz ↦ hy (by rw [hz, smul_zero]), htail⟩
    · exact (hy rfl).elim

/-- An idele whose S-coordinates lie in the S-product region of size `Y` and whose other
finite coordinates are bounded by `D` has idelic norm at most `Y` times the product of `D`. -/
private theorem sLocalAbsolutePW_globalSupport_norm {F : Type*} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (D : HeightOneSpectrum (𝓞 F) → ℝ)
    (hD : ∀ v, 1 ≤ D v) (hDf : (mulSupport D).Finite) (Y : ℝ) (z : IdeleGroup (𝓞 F) F)
    (hz : (∏ w : InfinitePlace F, ‖(adeleProjection F S z.val).1 w‖ ^ w.mult) *
      (∏ v : S, ‖(adeleProjection F S z.val).2 v‖) ≤ Y)
    (hout : ∀ v, v ∉ S → ‖z.val.2 v‖ ≤ D v) :
    ((ideleNorm F z : ℝ≥0) : ℝ) ≤ Y * ∏ᶠ v, D v := by
  classical
  obtain ⟨hfin, hnorm⟩ := (ideleNorm_spec F).1 z
  let a : HeightOneSpectrum (𝓞 F) → ℝ := fun v ↦ ‖z.val.2 v‖
  let U : Finset (HeightOneSpectrum (𝓞 F)) := S ∪ hDf.toFinset ∪ Set.Finite.toFinset hfin
  have ha : (∏ᶠ v, a v) = ∏ v ∈ U, a v :=
    finprod_eq_prod_of_mulSupport_subset _ fun v hv ↦ by simp [U, (Set.Finite.mem_toFinset hfin).mpr hv]
  have hDU : (∏ᶠ v, D v) = ∏ v ∈ U, D v :=
    finprod_eq_prod_of_mulSupport_subset _ fun v hv ↦ by
      have hv' : D v ≠ 1 := hv
      simp [U, hv']
  have hSU : S ⊆ U := fun v hv ↦ by simp [U, hv]
  have hD0 (v) : 0 ≤ D v := zero_le_one.trans (hD v)
  let P := ∏ w : InfinitePlace F, ‖z.val.1 w‖ ^ w.mult
  have hP : 0 ≤ P := Finset.prod_nonneg fun w _ ↦ pow_nonneg (norm_nonneg _) _
  have hS : (∏ v ∈ S, a v) = ∏ v : S, ‖(adeleProjection F S z.val).2 v‖ :=
    (Finset.prod_coe_sort S a).symm
  have hPS : P * ∏ v ∈ S, a v ≤ Y := by
    rw [hS]
    exact hz
  have hSnn : 0 ≤ ∏ v ∈ S, a v := Finset.prod_nonneg fun v _ ↦ norm_nonneg _
  have hY : 0 ≤ Y := (mul_nonneg hP hSnn).trans hPS
  have hrest : (∏ v ∈ U \ S, a v) ≤ ∏ v ∈ U \ S, D v :=
    Finset.prod_le_prod₀ (fun v _ ↦ norm_nonneg _)
      fun v hv ↦ hout v (Finset.mem_sdiff.mp hv).2
  have hrestD : (∏ v ∈ U \ S, D v) ≤ ∏ v ∈ U, D v := by
    rw [← Finset.prod_sdiff hSU]
    exact le_mul_of_one_le_right (Finset.prod_nonneg fun v _ ↦ hD0 v)
      (Finset.one_le_prod₀ fun v _ ↦ hD v)
  have hrestD0 : 0 ≤ ∏ v ∈ U \ S, D v := Finset.prod_nonneg fun v _ ↦ hD0 v
  rw [show ((ideleNorm F z : ℝ≥0) : ℝ) = P * ∏ᶠ v, a v from hnorm, ha, hDU,
    ← Finset.prod_sdiff hSU]
  calc P * ((∏ v ∈ U \ S, a v) * ∏ v ∈ S, a v)
      = (P * ∏ v ∈ S, a v) * ∏ v ∈ U \ S, a v := by ring
    _ ≤ Y * ∏ v ∈ U \ S, D v := mul_le_mul hPS hrest
        (Finset.prod_nonneg fun v _ ↦ norm_nonneg _) hY
    _ ≤ Y * ∏ v ∈ U, D v := mul_le_mul_of_nonneg_left hrestD hY

/-- Paper: Proposition 7.3.2.2(2), p. 352, and Proposition 7.3.2.4(2), p. 356.
For any Fourier region inside an S-product region, the global homogeneous theta functions
of the inserted zero-moment tests vanish below a uniform positive idelic norm.
By Riemann–Roch they are the theta functions of the Fourier transforms at the inverse
class, and those vanish above a uniform norm by the product formula. -/
private theorem sLocalAbsolutePW_globalSupport_region {F : Type*} [Field F] [NumberField F]
    {S T : Finset (HeightOneSpectrum (𝓞 F))} (hST : S ⊆ T)
    (ω : PontryaginDual (ideleClassNorm F).ker) (K : Set (SAdeleRing F S)) (Y : ℝ)
    (hY : 0 < Y)
    (hK : ∀ x ∈ K, (∏ w : InfinitePlace F, ‖x.1 w‖ ^ w.mult) * (∏ v : S, ‖x.2 v‖) ≤ Y) :
    ∃ bound > (0 : ℝ), ∀ (f : SchwartzBruhat (Multiplicative (SAdeleRing F T))),
      f ∈ sLocalPWTests hST K ⊓ sAdelePolarSubspace F T →
      tsupport (homogeneousAdelicTheta ω (sAdeleSchwartzToGlobal F T f)) ⊆
        {g | bound⁻¹ ≤ ((ideleClassNorm F g).val : ℝ)} := by
  classical
  obtain ⟨D, hD, hDf, hA⟩ := sLocalAbsolutePW_globalSupport_fourier (F := F) S
  have hD1 : 1 ≤ ∏ᶠ v, D v := by
    rw [finprod_eq_prod_of_mulSupport_subset D (s := hDf.toFinset) fun v hv ↦
      hDf.mem_toFinset.mpr hv]
    exact Finset.one_le_prod₀ fun v _ ↦ hD v
  let bound := Y * ∏ᶠ v, D v
  have hb : 0 < bound := mul_pos hY (zero_lt_one.trans_le hD1)
  refine ⟨bound, hb, ?_⟩
  rintro f ⟨hf, hf0⟩
  obtain ⟨h, rfl, -, hhK⟩ := (mem_sLocalPWTests hST K f).mp hf
  let Φ := sAdeleSchwartzToGlobal F T (sAdeleSchwartzTransition F hST h)
  have hΦ : Φ = sAdeleSchwartzToGlobal F S h :=
    LinearMap.congr_fun (sAdeleSchwartzToGlobal_comp (F := F) hST) h
  obtain ⟨hΦ0, hΦ1⟩ := (mem_adelePolarSubspace Φ).mp
    (sAdeleSchwartzToGlobal_mem_polarSubspace (F := F) (S := T) ⟨_, hf0⟩)
  -- The theta function of the Fourier transform vanishes at classes of large norm.
  have hlarge (z : IdeleGroup (𝓞 F) F) (hz : bound < ((ideleNorm F z : ℝ≥0) : ℝ)) :
      adelicTheta (adeleSchwartzFourier Φ) (QuotientGroup.mk z) = 0 := by
    rw [adelicTheta_mk]
    refine (tsum_congr fun ξ ↦ ?_).trans tsum_zero
    by_contra hne
    rw [hΦ] at hne
    obtain ⟨hloc, htail⟩ := hA h _ hne
    let u : IdeleGroup (𝓞 F) F := IdeleGroup.unitEmbedding (𝓞 F) F ξ * z
    have hu : u.val = algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) * z.val := rfl
    have huK : adeleProjection F S u.val ∈ K := by
      have hmem := hhK (subset_tsupport _ hloc)
      rw [hu]
      exact hmem
    have hn := sLocalAbsolutePW_globalSupport_norm S D hD hDf Y u (hK _ huK)
      (fun v hv ↦ by rw [hu]; exact htail v hv)
    have hprin : ideleNorm F u = ideleNorm F z := by
      rw [map_mul, MonoidHom.mem_ker.mp ((ideleNorm_spec F).2 ⟨ξ, rfl⟩), one_mul]
    rw [hprin] at hn
    exact absurd hz (not_lt.mpr hn)
  -- Hence theta of the test vanishes at classes of small norm.
  have hsmall (x : IdeleClassGroup (𝓞 F) F)
      (hx : ((ideleClassNorm F x).val : ℝ) < bound⁻¹) : adelicTheta Φ x = 0 := by
    have hpos : (0 : ℝ) < ((ideleClassNorm F x).val : ℝ) :=
      NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (ideleClassNorm F x).ne_zero)
    rw [adelicTheta_riemannRoch, hΦ0, hΦ1, smul_zero, add_zero, sub_zero]
    induction x using QuotientGroup.induction_on with
    | _ z =>
      rw [← QuotientGroup.mk_inv]
      have hz : ((ideleClassNorm F (QuotientGroup.mk z)).val : ℝ) =
          ((ideleNorm F z : ℝ≥0) : ℝ) := rfl
      have hinv : bound < ((ideleNorm F z⁻¹ : ℝ≥0) : ℝ) := by
        rw [map_inv, Units.val_inv_eq_inv_val, NNReal.coe_inv, ← hz]
        exact (lt_inv_comm₀ hpos hb).mp hx
      rw [hlarge z⁻¹ hinv, smul_zero]
  have hclosed : IsClosed {g : IdeleClassGroup (𝓞 F) F |
      bound⁻¹ ≤ ((ideleClassNorm F g).val : ℝ)} :=
    isClosed_le continuous_const (NNReal.continuous_coe.comp
      (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous))
  refine closure_minimal (fun g hg ↦ ?_) hclosed
  by_contra hlt
  simp only [Set.mem_ofPred_eq, not_le] at hlt
  apply hg
  change (∫ k, adelicTheta Φ (k.val * g) * (ω k : ℂ) ∂_) = 0
  refine (MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun k ↦ ?_)).trans
    (MeasureTheory.integral_zero _ _)
  have hk : ((ideleClassNorm F (k.val * g)).val : ℝ) < bound⁻¹ := by
    rw [map_mul, MonoidHom.mem_ker.mp k.property, one_mul]
    exact hlt
  change adelicTheta Φ (k.val * g) * (ω k : ℂ) = 0
  rw [hsmall _ hk, zero_mul]

/-- Paper: Proposition 7.3.2.2(2), p. 352.
At fixed finite stages, global theta of every inserted zero-moment test at this absolute
level vanishes below a uniform positive idelic norm. -/
theorem sLocalAbsolutePW_globalSupport {S₀ : Finset (HeightOneSpectrum (𝓞 F))}
    (hST : S ⊆ T) (_hT : T = S ∪ S₀)
    (_hdis : Disjoint S S₀) (_hsat : IsSaturatedPlaceSet (F := F) S₀)
    (_hPic : PicTrivial) (ω : PontryaginDual C₁) (_hu : NormOneCharacterUnramifiedOutside ω S)
    (X : ℝ) (_hX : 0 < X) :
    ∃ bound > (0 : ℝ), ∀ (f : B(T)), f ∈ sLocalPWTests hST (sLocalPWBox S X) ⊓ Z₀(T) →
      tsupport (homogeneousAdelicTheta ω (sAdeleSchwartzToGlobal F T f)) ⊆
        {g | bound⁻¹ ≤ ((ideleClassNorm F g).val : ℝ)} := by
  refine sLocalAbsolutePW_globalSupport_region hST ω _ (X ^ count(S)) (pow_pos _hX _) ?_
  rintro x ⟨hinf, hfin⟩
  rw [pow_add]
  have h1 : (∏ w : InfinitePlace F, ‖x.1 w‖ ^ w.mult) ≤ X ^ Fintype.card (InfinitePlace F) :=
    calc (∏ w : InfinitePlace F, ‖x.1 w‖ ^ w.mult) ≤ ∏ _w : InfinitePlace F, X :=
          Finset.prod_le_prod₀ (fun w _ ↦ pow_nonneg (norm_nonneg _) _) fun w _ ↦ hinf w
      _ = X ^ Fintype.card (InfinitePlace F) := by rw [Finset.prod_const, Finset.card_univ]
  have h2 : (∏ v : S, ‖x.2 v‖) ≤ X ^ S.card :=
    calc (∏ v : S, ‖x.2 v‖) ≤ ∏ _v : S, X :=
          Finset.prod_le_prod₀ (fun v _ ↦ norm_nonneg _) fun v _ ↦ hfin v
      _ = X ^ S.card := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe]
  exact mul_le_mul h1 h2 (Finset.prod_nonneg fun v _ ↦ norm_nonneg _) (pow_nonneg _hX.le _)

/-- Paper: Proposition 7.3.2.2(3), p. 352.
The local homogeneous theta of the Fourier-transformed level tests has a uniform upper
norm bound.
Deviation: Part (3) leaves the test variable free. The Fourier support bound applies to
every band-limited input, since the product norm bounds each contributing orbit. -/
theorem sLocalAbsolutePW_localFourierSupport {S₀ : Finset (HeightOneSpectrum (𝓞 F))}
    (hST : S ⊆ T) (_hT : T = S ∪ S₀)
    (_hdis : Disjoint S S₀) (_hsat : IsSaturatedPlaceSet (F := F) S₀)
    (_hPic : PicTrivial) (ω : PontryaginDual C₁) (hu : NormOneCharacterUnramifiedOutside ω S)
    (χ : PontryaginDual J₁(T)) (_hχ : χ = descend(hST, ω, hu))
    (X : ℝ) (_hX : 0 < X) :
    ∃ bound > (0 : ℝ), ∀ (f : B(T)), f ∈ sLocalPWTests hST (sLocalPWBox S X) →
      tsupport (sLocalHomogeneousAdelicThetaLinearMap F T χ (sAdeleSchwartzFourier f)) ⊆
          {g | ((m(T) g).val : ℝ) ≤ bound} := by
  let U := {v : T // v.val ∉ S}
  let radius (v : V) : ℝ :=
    (v.asIdeal.absNorm : ℝ) ^ multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F))
  let bound₀ : ℝ :=
    X ^ (Fintype.card (InfinitePlace F) + S.card) * ∏ v : U, radius v.val.val
  let bound : ℝ := max 1 bound₀
  refine ⟨bound, zero_lt_one.trans_le (le_max_left 1 bound₀), fun f hf ↦ ?_⟩
  obtain ⟨g, rfl, _, hsupp⟩ := (mem_sLocalPWTests hST (sLocalPWBox S X) f).mp hf
  let φ : B(T) := sAdeleSchwartzFourier (Π(hST) g)
  have hbound_adele : ∀ y : SAdeleRing F T,
      φ (Multiplicative.ofAdd y) ≠ 0 →
        (∏ w : InfinitePlace F, ‖y.1 w‖ ^ w.mult) * ∏ v : T, ‖y.2 v‖ ≤ bound := by
    intro y hy
    obtain ⟨hyS_ne, hyU_bound⟩ := sLocalAbsolutePW_fourier_transition_support (F := F) hST g y hy
    have hyS_box : (y.1, fun w : S ↦ y.2 ⟨w.val, hST w.property⟩) ∈ sLocalPWBox S X :=
      hsupp (subset_tsupport _ hyS_ne)
    have harch : (∏ w : InfinitePlace F, ‖y.1 w‖ ^ w.mult) ≤
        X ^ Fintype.card (InfinitePlace F) := by
      calc
        _ ≤ ∏ _w : InfinitePlace F, X :=
          Finset.prod_le_prod₀ (fun w _ ↦ pow_nonneg (norm_nonneg _) _) fun w _ ↦ hyS_box.1 w
        _ = X ^ Fintype.card (InfinitePlace F) := by
          rw [Finset.prod_const, Finset.card_univ]
    have hfinS : (∏ v : {v : T // v.val ∈ S}, ‖y.2 v.val‖) ≤ X ^ S.card := by
      let eS : S ≃ {v : T // v.val ∈ S} :=
        { toFun := fun w ↦ ⟨⟨w.val, hST w.property⟩, w.property⟩
          invFun := fun v ↦ ⟨v.val.val, v.property⟩
          left_inv := fun ⟨_, _⟩ ↦ rfl
          right_inv := fun ⟨⟨_, _⟩, _⟩ ↦ rfl }
      calc
        (∏ v : {v : T // v.val ∈ S}, ‖y.2 v.val‖)
          = ∏ w : S, ‖y.2 ⟨w.val, hST w.property⟩‖ := Fintype.prod_equiv eS.symm _ _ fun _ ↦ rfl
        _ ≤ ∏ _w : S, X :=
          Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun w _ ↦ hyS_box.2 w
        _ = X ^ S.card := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe]
    have hfinU : (∏ v : U, ‖y.2 v.val‖) ≤ ∏ v : U, radius v.val.val :=
      Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun v _ ↦ hyU_bound v
    have hfin : (∏ v : T, ‖y.2 v‖) ≤ X ^ S.card * ∏ v : U, radius v.val.val := by
      rw [← Fintype.prod_subtype_mul_prod_subtype (fun v : T ↦ v.val ∈ S) (fun v : T ↦ ‖y.2 v‖)]
      exact mul_le_mul hfinS hfinU (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _)
        (pow_nonneg _hX.le _)
    have htot : (∏ w : InfinitePlace F, ‖y.1 w‖ ^ w.mult) * (∏ v : T, ‖y.2 v‖) ≤ bound₀ := by
      calc
        _ ≤ X ^ Fintype.card (InfinitePlace F) * (X ^ S.card * ∏ v : U, radius v.val.val) :=
          mul_le_mul harch hfin (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _)
            (pow_nonneg _hX.le _)
        _ = bound₀ := by
          dsimp only [bound₀]
          rw [pow_add, mul_assoc]
    exact htot.trans (le_max_right 1 bound₀)
  have hvanish : ∀ q : J(T), bound < ((m(T) q).val : ℝ) →
      sLocalHomogeneousAdelicThetaLinearMap F T χ φ q = 0 := by
    intro q hq
    rw [sLocalHomogeneousAdelicThetaLinearMap_apply]
    have hint : ∀ h : J₁(T), sLocalAdelicThetaOnClasses F T φ (q * h.val) * (χ h : ℂ) = 0 := by
      intro h
      have hm_eq : m(T) (q * h.val) = m(T) q := by
        rw [map_mul, MonoidHom.mem_ker.mp h.property, mul_one]
      have hq' : bound < ((m(T) (q * h.val)).val : ℝ) := hm_eq.symm ▸ hq
      obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (q * h.val)
      have ha_theta : sLocalAdelicThetaOnClasses F T φ (QuotientGroup.mk a) = 0 := by
        rw [sLocalAdelicThetaOnClasses_mk, sLocalAdelicTheta_apply]
        have hzero : ∀ ξ : (Set.integer (T : Set V) F)ˣ,
            φ (Multiplicative.ofAdd (Units.val (sUnitEmbedding F T ξ * a))) = 0 := by
          intro ξ
          let unitAtT : (Set.integer (T : Set V) F)ˣ →* (SAdeleRing F T)ˣ :=
            sUnitEmbedding F T
          by_contra hnz
          have hle := hbound_adele (unitAtT ξ * a).val hnz
          have hnorm_unit : sIdeleNorm F T (unitAtT ξ) = 1 :=
            MonoidHom.mem_ker.mp ((sIdeleNorm_spec F T).2 ⟨ξ, rfl⟩)
          have hnorm_eq : ((sIdeleNorm F T (unitAtT ξ * a)).val : ℝ) =
              ((m(T) (q * h.val)).val : ℝ) := by
            rw [map_mul, hnorm_unit, one_mul, ← ha, sIdeleQuotientNorm_mk]
          have hmod_fn (z : (SAdeleRing F T)ˣ) : ((sIdeleNorm F T z).val : ℝ) =
              (∏ w : InfinitePlace F, ‖z.val.1 w‖ ^ w.mult) * ∏ v : T, ‖z.val.2 v‖ := by
            simp [sIdeleNorm]
          have hmod := hmod_fn (unitAtT ξ * a)
          linarith [hle, hmod, hnorm_eq, hq']
        exact (tsum_congr hzero).trans tsum_zero
      rw [← ha, ha_theta, zero_mul]
    simp only [hint]
    exact MeasureTheory.integral_zero (α := ↥J₁(T)) (G := ℂ)
  refine closure_minimal (fun q hq ↦ ?_) ?_
  · by_contra hle
    exact hq (hvanish q (lt_of_not_ge hle))
  · exact isClosed_le (NNReal.continuous_coe.comp
      (Units.continuous_val.comp (isProperMap_sIdeleQuotientNorm F T).continuous)) continuous_const

end AbsoluteLevels

/-- A dilate of a compactly supported function by a self-homeomorphism is compactly supported,
and its support stays in a set whose preimage under the homeomorphism it contains. -/
private theorem sLocalAbsolutePW_translate_support {G : Type*} [TopologicalSpace G]
    (e : G ≃ₜ G) (b : ℂ) (φ ψ : G → ℂ) (hψ : ∀ x, ψ x = b * φ (e x)) (s : Set G)
    (hs : e ⁻¹' s ⊆ s) (hc : HasCompactSupport φ) (hφ : tsupport φ ⊆ s) :
    HasCompactSupport ψ ∧ tsupport ψ ⊆ s := by
  have hsub : tsupport ψ ⊆ e ⁻¹' tsupport φ := by
    refine closure_minimal (fun x hx ↦ ?_) ((isClosed_tsupport φ).preimage e.continuous)
    refine subset_tsupport φ ?_
    intro h0
    exact hx ((hψ x).trans (by rw [h0, mul_zero]))
  have hcomp : IsCompact (e ⁻¹' tsupport φ) := e.isCompact_preimage.mpr hc
  exact ⟨hcomp.of_isClosed_subset (isClosed_tsupport ψ) hsub,
    hsub.trans ((Set.preimage_mono hφ).trans hs)⟩

/-- The S-adelic Fourier transform of a unit translate is a nonnegative multiple of the
dilate of the Fourier transform by the same unit. -/
private theorem sLocalAbsolutePW_translate_fourier {F : Type*} [Field F] [NumberField F]
    {T : Finset (HeightOneSpectrum (𝓞 F))} (u : (SAdeleRing F T)ˣ) :
    ∃ b : ℝ≥0, ∀ (f : SchwartzBruhat (Multiplicative (SAdeleRing F T))) (y : SAdeleRing F T),
      sAdeleSchwartzFourier (schwartzBruhatUnitTranslate u f) (Multiplicative.ofAdd y) =
        ((b : ℝ) : ℂ) * sAdeleSchwartzFourier f (Multiplicative.ofAdd ((u : SAdeleRing F T) * y)) := by
  let A := SAdeleRing F T
  let G := Multiplicative A
  let (w : InfinitePlace F) : MeasurableSpace w.Completion := borel _
  let (v : HeightOneSpectrum (𝓞 F)) : MeasurableSpace (v.adicCompletion F) := borel _
  let : MeasurableSpace (InfiniteAdeleRing F) :=
    inferInstanceAs (MeasurableSpace ((w : InfinitePlace F) → w.Completion))
  let : MeasurableSpace A :=
    inferInstanceAs (MeasurableSpace (InfiniteAdeleRing F × ((v : T) → v.val.adicCompletion F)))
  let μ : MeasureTheory.Measure G := sAdditiveTamagawaMeasure F T
  obtain ⟨hT₂, hLC, hBor, hHaar, hReg⟩ := sAdele_fourierMeasure (F := F) (S := T)
  let : T2Space G := hT₂
  let : LocallyCompactSpace G := hLC
  let : BorelSpace G := hBor
  let : μ.IsHaarMeasure := hHaar
  let : μ.Regular := hReg
  let d : G ≃ₜ* G :=
    { toFun := fun x ↦ Multiplicative.ofAdd ((↑u⁻¹ : A) * x.toAdd)
      invFun := fun x ↦ Multiplicative.ofAdd ((u : A) * x.toAdd)
      left_inv := fun x ↦ Multiplicative.ext (by simp [← mul_assoc])
      right_inv := fun x ↦ Multiplicative.ext (by simp [← mul_assoc])
      map_mul' := fun x y ↦ Multiplicative.ext (mul_add _ _ _)
      continuous_toFun := continuous_ofAdd.comp (continuous_const.mul continuous_toAdd)
      continuous_invFun := continuous_ofAdd.comp (continuous_const.mul continuous_toAdd) }
  let ν := μ.map d
  let : ν.IsHaarMeasure := d.isHaarMeasure_map μ
  let : ν.Regular := MeasureTheory.Measure.Regular.map d.toHomeomorph
  refine ⟨ν.haarScalarFactor μ, fun f y ↦ ?_⟩
  let k : G → ℂ := fun x ↦
    f x * star ((sAdeleStandardCharacter F T (x.toAdd * ((u : A) * y)) : Circle) : ℂ)
  have h1 : (∫ x : G, k (d.toHomeomorph.toMeasurableEquiv x) ∂μ) =
      ((ν.haarScalarFactor μ : ℝ) : ℂ) * ∫ x : G, k x ∂μ := by
    rw [← MeasureTheory.integral_map_equiv d.toHomeomorph.toMeasurableEquiv k]
    change (∫ x : G, k x ∂ν) = _
    calc
      _ = ∫ x : G, k x ∂(ν.haarScalarFactor μ • μ) :=
        congrArg (fun m : MeasureTheory.Measure G ↦ ∫ x : G, k x ∂m)
          (MeasureTheory.Measure.isMulLeftInvariant_eq_smul_of_regular ν μ)
      _ = _ := by
        rw [MeasureTheory.integral_smul_nnreal_measure]
        rfl
  refine Eq.trans ?_ h1
  change (∫ x : A, f (Multiplicative.ofAdd ((↑u⁻¹ : A) * x)) *
    star ((sAdeleStandardCharacter F T (x * y) : Circle) : ℂ) ∂(sAdditiveTamagawaMeasure F T)) =
    ∫ x : A, f (Multiplicative.ofAdd ((↑u⁻¹ : A) * x)) *
      star ((sAdeleStandardCharacter F T (((↑u⁻¹ : A) * x) * ((u : A) * y)) : Circle) : ℂ)
      ∂(sAdditiveTamagawaMeasure F T)
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  change _ * star ((sAdeleStandardCharacter F T (x * y) : Circle) : ℂ) =
    _ * star ((sAdeleStandardCharacter F T (((↑u⁻¹ : A) * x) * ((u : A) * y)) : Circle) : ℂ)
  rw [mul_mul_mul_comm, Units.inv_mul, one_mul]

/-- A level built from a Fourier region that is stable under shrinking by ideles of absolute
value at least one at the infinite places and one at the finite places is preserved by the
classes of norm at least one. The norm-one part of a class acts by a scalar, and the remaining
part is represented by a positive real at one infinite place. -/
private theorem sLocalAbsolutePW_translate_level (hST : S ⊆ T) (K : Set (SAdeleRing F S))
    (hK : ∀ a : (SAdeleRing F S)ˣ, (∀ w : InfinitePlace F, 1 ≤ ‖a.val.1 w‖) →
      (∀ v : S, ‖a.val.2 v‖ = 1) → ∀ y : SAdeleRing F S, a.val * y ∈ K → y ∈ K)
    (D : Submodule ℂ (B(T))) (hD : D = ⊤ ∨ D = Z₀(T))
    (ω : PontryaginDual J₁(T)) (g : J(T)) (hg : large(g))
    (x : Θ(T, ω)) (hx : x ∈ level(hST, K, D, ω)) :
    A(T, ω) g x ∈ level(hST, K, D, ω) := by
  classical
  let ρ := A(T, ω)
  have hρ : ∀ (a : (SAdeleRing F T)ˣ) (f : B(T)),
      ρ (QuotientGroup.mk a) (q(T, ω) f) = q(T, ω) (schwartzBruhatUnitTranslate a f) :=
    (existsUnique_sLocalHomogeneousThetaAction (F := F) (S := T) ω).exists.choose_spec.2
  refine map_mem_closure (ρ g).continuous hx ?_
  rintro _ ⟨f, ⟨hf, hfD⟩, rfl⟩
  obtain ⟨h, rfl, hband⟩ := (mem_sLocalPWTests hST K f).mp hf
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  let t : ℝ≥0ˣ := m(T) g
  let x₀ := (infinitePlaceRealPower F w (w.mult : ℝ)⁻¹ t).val
  have hx₀ : 1 ≤ ‖x₀‖ := by
    have hiso : ‖InfinitePlace.Completion.extensionEmbedding w x₀‖ = ‖x₀‖ :=
      (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
        (map_zero _) x₀
    rw [← hiso, infinitePlaceRealPower_apply, Complex.norm_real, Real.norm_eq_abs]
    exact (Real.one_le_rpow hg (inv_nonneg.mpr (Nat.cast_nonneg _))).trans (le_abs_self _)
  have hsS : ∃ uS : (integralAdelesOutside F S)ˣ,
      integralIdeleInsertion F S uS = singlePlaceIdeleNormSection F w t := by
    refine (mem_range_integralIdeleInsertion F S _).mpr fun v _ ↦ ⟨?_, ?_⟩
    · exact (v.adicCompletionIntegers F).one_mem
    · change ((singlePlaceIdeleNormSection F w t)⁻¹).val.2 v ∈ _
      rw [← map_inv]
      exact (v.adicCompletionIntegers F).one_mem
  obtain ⟨uS, huS⟩ := hsS
  let gS := Units.map (adeleProjection F S).toMonoidHom (integralIdeleInsertion F S uS)
  let gT := Units.map (adeleProjection F T).toMonoidHom (integralIdeleInsertion F S uS)
  have htr : Π(hST) (schwartzBruhatUnitTranslate gS h) =
      schwartzBruhatUnitTranslate gT (Π(hST) h) := testTransition_translate_eq hST uS h
  have hnorm : m(T) (QuotientGroup.mk gT) = t := by
    obtain ⟨uT, huT⟩ := insert_mem_larger hST uS
    have hspec := (sIdeleNorm_spec F T).1 uT
    have hgT : gT = Units.map ((adeleProjection F T).comp
        (integralAdelesOutside F T).subtype).toMonoidHom uT := by
      change Units.map (adeleProjection F T).toMonoidHom (integralIdeleInsertion F S uS) = _
      rw [← huT]
      rfl
    change sIdeleNorm F T gT = t
    rw [hgT, ← hspec]
    change ideleNorm F (integralIdeleInsertion F T uT) = t
    rw [huT, huS]
    exact singlePlaceIdeleNormSection_rightInverse F w t
  let g₀ : J(T) := g * (QuotientGroup.mk gT)⁻¹
  have hg₀ : g₀ ∈ (m(T)).ker := MonoidHom.mem_ker.mpr (by
    change m(T) (g * (QuotientGroup.mk gT)⁻¹) = 1
    rw [map_mul, map_inv, hnorm]
    exact mul_inv_cancel t)
  obtain ⟨v, hv⟩ := QuotientGroup.mk_surjective g₀
  have hgv : g = QuotientGroup.mk v * QuotientGroup.mk gT := by
    rw [hv]
    exact (inv_mul_cancel_right g _).symm
  let c : ℂ := (ω ⟨g₀, hg₀⟩ : ℂ)
  have hscal := sLocalHomogeneousTheta_unitTranslate ω ⟨g₀, hg₀⟩ v hv
    (schwartzBruhatUnitTranslate gT (Π(hST) h))
  have hq : q(T, ω) (schwartzBruhatUnitTranslate v (schwartzBruhatUnitTranslate gT (Π(hST) h))) =
      c • q(T, ω) (schwartzBruhatUnitTranslate gT (Π(hST) h)) := by
    rw [← map_smul]
    refine (Submodule.Quotient.eq _).mpr (LinearMap.mem_ker.mpr ?_)
    rw [map_sub, map_smul, hscal, sub_self]
  have key : ρ g (q(T, ω) (Π(hST) h)) =
      c • q(T, ω) (Π(hST) (schwartzBruhatUnitTranslate gS h)) := by
    rw [hgv, map_mul]
    change ρ (QuotientGroup.mk v) (ρ (QuotientGroup.mk gT) (q(T, ω) (Π(hST) h))) = _
    rw [hρ, hρ, hq, htr]
  change ρ g (q(T, ω) (Π(hST) h)) ∈ ((sLocalPWTests hST K ⊓ D).map (q(T, ω)))
  rw [key]
  refine Submodule.smul_mem _ _ (Submodule.mem_map_of_mem
    ⟨(mem_sLocalPWTests hST K _).mpr ⟨_, rfl, ?_⟩, ?_⟩)
  · obtain ⟨b, hb⟩ := sLocalAbsolutePW_translate_fourier gS
    let e : Multiplicative (SAdeleRing F S) ≃ₜ Multiplicative (SAdeleRing F S) :=
      { toFun := fun y ↦ Multiplicative.ofAdd ((gS : SAdeleRing F S) * y.toAdd)
        invFun := fun y ↦ Multiplicative.ofAdd ((↑gS⁻¹ : SAdeleRing F S) * y.toAdd)
        left_inv := fun y ↦ Multiplicative.ext (by simp [← mul_assoc])
        right_inv := fun y ↦ Multiplicative.ext (by simp [← mul_assoc])
        continuous_toFun := continuous_ofAdd.comp (continuous_const.mul continuous_toAdd)
        continuous_invFun := continuous_ofAdd.comp (continuous_const.mul continuous_toAdd) }
    refine sLocalAbsolutePW_translate_support e ((b : ℝ) : ℂ) (sAdeleSchwartzFourier h).val
      (sAdeleSchwartzFourier (schwartzBruhatUnitTranslate gS h)).val (fun y ↦ hb h y.toAdd)
      (Multiplicative.toAdd ⁻¹' K) ?_ hband.1 hband.2
    intro y hy
    refine hK gS (fun w' ↦ ?_) (fun v' ↦ ?_) y.toAdd hy
    · have h1 : (gS : SAdeleRing F S).1 w' = Pi.mulSingle w x₀ w' :=
        congrArg (fun z : IdeleGroup (𝓞 F) F ↦ z.val.1 w') huS
      rw [h1]
      by_cases hw : w' = w
      · subst hw
        rw [Pi.mulSingle_eq_same]
        exact hx₀
      · rw [Pi.mulSingle_eq_of_ne hw, norm_one]
    · have h2 : (gS : SAdeleRing F S).2 v' = 1 :=
        congrArg (fun z : IdeleGroup (𝓞 F) F ↦ z.val.2 v'.val) huS
      rw [h2, norm_one]
  · rcases hD with rfl | rfl
    · trivial
    · rw [htr]
      obtain ⟨h0, h1⟩ := (mem_sAdelePolarSubspace _).mp hfD
      obtain ⟨b, hb⟩ := sLocalAbsolutePW_translate_fourier gT
      refine (mem_sAdelePolarSubspace _).mpr ⟨?_, ?_⟩
      · refine (schwartzBruhatUnitTranslate_apply gT _ 0).trans ?_
        rw [mul_zero]
        exact h0
      · rw [hb, mul_zero, h1, mul_zero]

/-- Paper: Proposition 7.3.2.2(4), p. 352.
Left translation by an idele class of norm at least one preserves the absolute levels,
with or without the zero-moment constraint.
Deviation: Stated directly for the local norm-one character and the inclusion of stages.
The preservation uses no class-number assumption. -/
theorem sLocalAbsolutePW_translate (hST : S ⊆ T) {X : ℝ} (_hX : 0 < X)
    (D : Submodule ℂ (B(T))) (_hD : D = ⊤ ∨ D = Z₀(T))
    (ω : PontryaginDual J₁(T)) (g : J(T)) (_hg : large(g))
    (x : Θ(T, ω)) (_hx : x ∈ sLocalAbsolutePW hST X D ω) :
    A(T, ω) g x ∈ sLocalAbsolutePW hST X D ω := by
  refine sLocalAbsolutePW_translate_level hST (sLocalPWBox S X) ?_ D _hD ω g _hg x _hx
  intro a ha1 ha2 y hy
  refine ⟨fun w ↦ le_trans ?_ (hy.1 w), fun v ↦ le_trans ?_ (hy.2 v)⟩
  · refine pow_le_pow_left₀ (norm_nonneg _) ?_ _
    change ‖y.1 w‖ ≤ ‖a.val.1 w * y.1 w‖
    rw [norm_mul]
    exact le_mul_of_one_le_left (norm_nonneg _) (ha1 w)
  · change ‖y.2 v‖ ≤ ‖a.val.2 v * y.2 v‖
    rw [norm_mul, ha2 v, one_mul]

/-- Paper: Definition 7.3.2.3(1), p. 354–355.
The invariant Fourier region bounds the product of the normalized local absolute values,
including at tuples having a zero coordinate. -/
def sLocalPWProductRegion (S : Finset V) (Y : ℝ) : Set (SAdeleRing F S) :=
  {x | (∏ w : InfinitePlace F, ‖x.1 w‖ ^ w.mult) * (∏ v : S, ‖x.2 v‖) ≤ Y}

/-- Paper: Definition 7.3.2.3(1), p. 355.
On invertible adeles the product bound is the S-idelic norm bound. -/
theorem mem_sLocalPWProductRegion_units (Y : ℝ) (u : (SAdeleRing F S)ˣ) :
    u.val ∈ sLocalPWProductRegion S Y ↔ ((sIdeleNorm F S u).val : ℝ) ≤ Y := by
  simp [sLocalPWProductRegion, sIdeleNorm, Units.coe_prod]

/-- Paper: Definition 7.3.2.3(2), p. 355.
The invariant PW level is the closure of the theta image of tests with compact Fourier
support in the product region, optionally subject to the zero-moment constraint.
Deviation: Uses the cited integer-ring insertion and the unrestricted test space for
the unrestricted level. The sentence after (7.3.2.17) repeats the zero-moment space. -/
def sLocalInvariantPW (hST : S ⊆ T) (Y : ℝ) (D : Submodule ℂ (B(T)))
    (ω : PontryaginDual J₁(T)) : Submodule ℂ (Θ(T, ω)) :=
  level(hST, sLocalPWProductRegion S Y, D, ω)

/-- Paper: Definition 7.3.2.3(2), p. 355.
An inserted test with compact Fourier support in the product region and satisfying the
chosen test constraint represents an element of the invariant level.
Deviation: Uses the integer-ring insertion of the cited transition. -/
theorem sLocalInvariantPW_mk_mem (hST : S ⊆ T) (Y : ℝ) (D : Submodule ℂ (B(T)))
    (ω : PontryaginDual J₁(T)) (f : B(S)) (_hf : inBand(sLocalPWProductRegion S Y, f))
    (_hD : Π(hST) f ∈ D) : q(T, ω) (Π(hST) f) ∈ sLocalInvariantPW hST Y D ω :=
  Submodule.le_topologicalClosure _
    (Submodule.mem_map_of_mem ⟨Submodule.mem_map_of_mem (Submodule.subset_span _hf), _hD⟩)

/-- Paper: Proposition 7.3.2.4(1), p. 355.
Increasing the product bound enlarges each of the two invariant PW levels. -/
theorem sLocalInvariantPW_mono (hST : S ⊆ T) {Y Y' : ℝ} (_hYY' : Y ≤ Y')
    (D : Submodule ℂ (B(T))) (ω : PontryaginDual J₁(T)) :
    sLocalInvariantPW hST Y D ω ≤ sLocalInvariantPW hST Y' D ω := by
  have hbox : sLocalPWProductRegion S Y ⊆ sLocalPWProductRegion S Y' :=
    fun _ hx ↦ le_trans hx _hYY'
  have hgen : {f : B(S) | inBand(sLocalPWProductRegion S Y, f)} ⊆
      {f : B(S) | inBand(sLocalPWProductRegion S Y', f)} :=
    fun _ hf ↦ ⟨hf.1, hf.2.trans (Set.preimage_mono hbox)⟩
  have htests : sLocalPWTests hST (sLocalPWProductRegion S Y) ≤ sLocalPWTests hST (sLocalPWProductRegion S Y') :=
    Submodule.map_mono (Submodule.span_mono hgen)
  exact Submodule.topologicalClosure_mono (Submodule.map_mono (inf_le_inf htests le_rfl))

section InvariantLevels

open Classical

/-- Paper: Proposition 7.3.2.4(1), p. 356.
The union of the invariant PW levels is sequentially dense in the corresponding
full or zero-moment homogeneous theta space.
Deviation: Uses integer-ring insertion, as in the density proof. -/
theorem sLocalInvariantPW_seqDense {S₀ : Finset (HeightOneSpectrum (𝓞 F))}
    (hST : S ⊆ T) (_hT : T = S ∪ S₀)
    (_hdis : Disjoint S S₀) (_hsat : IsSaturatedPlaceSet (F := F) S₀)
    (_hPic : PicTrivial) (ω : PontryaginDual C₁) (hu : NormOneCharacterUnramifiedOutside ω S)
    (χ : PontryaginDual J₁(T)) (_hχ : χ = descend(hST, ω, hu))
    (D : Submodule ℂ (B(T))) (_hD : D = ⊤ ∨ D = Z₀(T)) :
    ∀ (x : Θ(T, χ)), x ∈ D.map (q(T, χ)) → ∃ u : ℕ → Θ(T, χ),
      (∀ n, ∃ Y > 0, u n ∈ sLocalInvariantPW hST Y D χ) ∧
        Tendsto u atTop (𝓝 x) := by
  intro x hx
  have seq := sLocalAbsolutePW_seqDense (F := F) hST _hT _hdis _hsat _hPic ω hu χ _hχ D _hD x hx
  refine ⟨seq.choose, fun n ↦ ?_, seq.choose_spec.2⟩
  let X := (seq.choose_spec.1 n).choose
  have hn := (seq.choose_spec.1 n).choose_spec.2
  let m : SAdeleRing F S → ℝ := fun y ↦
    (∏ w : InfinitePlace F, ‖y.1 w‖ ^ w.mult) * (∏ v : S, ‖y.2 v‖)
  have hm : Continuous m := by
    dsimp only [m]
    exact (continuous_finsetProd Finset.univ (fun w _ ↦
      ((continuous_apply w).comp continuous_fst).norm.pow w.mult)).mul
      (continuous_finsetProd Finset.univ (fun v _ ↦ ((continuous_apply v).comp continuous_snd).norm))
  have bounded := ((isCompact_sLocalPWBox (F := F) (S := S) X).image hm).bddAbove
  let Y : ℝ := bounded.choose
  have hY : Y ∈ upperBounds (m '' sLocalPWBox S X) := bounded.choose_spec
  have hbox : sLocalPWBox S X ⊆ sLocalPWProductRegion S (max 1 Y) :=
    fun y hy ↦ (hY (Set.mem_image_of_mem m hy)).trans (le_max_right _ _)
  have hgen : {f : B(S) | inBand(sLocalPWBox S X, f)} ⊆
      {f : B(S) | inBand(sLocalPWProductRegion S (max 1 Y), f)} :=
    fun _ hf ↦ ⟨hf.1, hf.2.trans (Set.preimage_mono hbox)⟩
  have htests : sLocalPWTests hST (sLocalPWBox S X) ≤
      sLocalPWTests hST (sLocalPWProductRegion S (max 1 Y)) :=
    Submodule.map_mono (Submodule.span_mono hgen)
  have hlevel : sLocalAbsolutePW hST X D χ ≤ sLocalInvariantPW hST (max 1 Y) D χ :=
    Submodule.topologicalClosure_mono (Submodule.map_mono (inf_le_inf htests (le_refl D)))
  exact ⟨max 1 Y, zero_lt_one.trans_le (le_max_left _ _), hlevel hn⟩

/-- Paper: Proposition 7.3.2.4(2), p. 356.
At fixed finite stages, the global theta of the invariant zero-moment level tests has
a uniform positive lower idelic norm bound. -/
theorem sLocalInvariantPW_globalSupport {S₀ : Finset (HeightOneSpectrum (𝓞 F))}
    (hST : S ⊆ T) (_hT : T = S ∪ S₀)
    (_hdis : Disjoint S S₀) (_hsat : IsSaturatedPlaceSet (F := F) S₀)
    (_hPic : PicTrivial) (ω : PontryaginDual C₁) (_hu : NormOneCharacterUnramifiedOutside ω S)
    (Y : ℝ) (_hY : 0 < Y) :
    ∃ bound > (0 : ℝ), ∀ (f : B(T)), f ∈ sLocalPWTests hST (sLocalPWProductRegion S Y) ⊓ Z₀(T) →
      tsupport (homogeneousAdelicTheta ω (sAdeleSchwartzToGlobal F T f)) ⊆
        {g | bound⁻¹ ≤ ((ideleClassNorm F g).val : ℝ)} :=
  sLocalAbsolutePW_globalSupport_region hST ω _ Y _hY fun _ hx ↦ hx

end InvariantLevels

/-- A dilate of a compactly supported function by a self-homeomorphism is compactly supported,
and its support stays in a set whose preimage under the homeomorphism it contains. -/
private theorem sLocalInvariantPW_translate_support {G : Type*} [TopologicalSpace G]
    (e : G ≃ₜ G) (b : ℂ) (φ ψ : G → ℂ) (hψ : ∀ x, ψ x = b * φ (e x)) (s t : Set G)
    (hs : e ⁻¹' s ⊆ t) (hc : HasCompactSupport φ) (hφ : tsupport φ ⊆ s) :
    HasCompactSupport ψ ∧ tsupport ψ ⊆ t := by
  have hsub : tsupport ψ ⊆ e ⁻¹' tsupport φ := by
    refine closure_minimal (fun x hx ↦ ?_) ((isClosed_tsupport φ).preimage e.continuous)
    refine subset_tsupport φ ?_
    intro h0
    exact hx ((hψ x).trans (by rw [h0, mul_zero]))
  have hcomp : IsCompact (e ⁻¹' tsupport φ) := e.isCompact_preimage.mpr hc
  exact ⟨hcomp.of_isClosed_subset (isClosed_tsupport ψ) hsub,
    hsub.trans ((Set.preimage_mono hφ).trans hs)⟩

/-- The S-adelic Fourier transform of a unit translate is a nonnegative multiple of the
dilate of the Fourier transform by the same unit. -/
private theorem sLocalInvariantPW_translate_fourier {F : Type*} [Field F] [NumberField F]
    {T : Finset (HeightOneSpectrum (𝓞 F))} (u : (SAdeleRing F T)ˣ) :
    ∃ b : ℝ≥0, ∀ (f : SchwartzBruhat (Multiplicative (SAdeleRing F T))) (y : SAdeleRing F T),
      sAdeleSchwartzFourier (schwartzBruhatUnitTranslate u f) (Multiplicative.ofAdd y) =
        ((b : ℝ) : ℂ) * sAdeleSchwartzFourier f (Multiplicative.ofAdd ((u : SAdeleRing F T) * y)) := by
  let A := SAdeleRing F T
  let G := Multiplicative A
  let (w : InfinitePlace F) : MeasurableSpace w.Completion := borel _
  let (v : HeightOneSpectrum (𝓞 F)) : MeasurableSpace (v.adicCompletion F) := borel _
  let : MeasurableSpace (InfiniteAdeleRing F) :=
    inferInstanceAs (MeasurableSpace ((w : InfinitePlace F) → w.Completion))
  let : MeasurableSpace A :=
    inferInstanceAs (MeasurableSpace (InfiniteAdeleRing F × ((v : T) → v.val.adicCompletion F)))
  let μ : MeasureTheory.Measure G := sAdditiveTamagawaMeasure F T
  obtain ⟨hT₂, hLC, hBor, hHaar, hReg⟩ := sAdele_fourierMeasure (F := F) (S := T)
  let : T2Space G := hT₂
  let : LocallyCompactSpace G := hLC
  let : BorelSpace G := hBor
  let : μ.IsHaarMeasure := hHaar
  let : μ.Regular := hReg
  let d : G ≃ₜ* G :=
    { toFun := fun x ↦ Multiplicative.ofAdd ((↑u⁻¹ : A) * x.toAdd)
      invFun := fun x ↦ Multiplicative.ofAdd ((u : A) * x.toAdd)
      left_inv := fun x ↦ Multiplicative.ext (by simp [← mul_assoc])
      right_inv := fun x ↦ Multiplicative.ext (by simp [← mul_assoc])
      map_mul' := fun x y ↦ Multiplicative.ext (mul_add _ _ _)
      continuous_toFun := continuous_ofAdd.comp (continuous_const.mul continuous_toAdd)
      continuous_invFun := continuous_ofAdd.comp (continuous_const.mul continuous_toAdd) }
  let ν := μ.map d
  let : ν.IsHaarMeasure := d.isHaarMeasure_map μ
  let : ν.Regular := MeasureTheory.Measure.Regular.map d.toHomeomorph
  refine ⟨ν.haarScalarFactor μ, fun f y ↦ ?_⟩
  let k : G → ℂ := fun x ↦
    f x * star ((sAdeleStandardCharacter F T (x.toAdd * ((u : A) * y)) : Circle) : ℂ)
  have h1 : (∫ x : G, k (d.toHomeomorph.toMeasurableEquiv x) ∂μ) =
      ((ν.haarScalarFactor μ : ℝ) : ℂ) * ∫ x : G, k x ∂μ := by
    rw [← MeasureTheory.integral_map_equiv d.toHomeomorph.toMeasurableEquiv k]
    change (∫ x : G, k x ∂ν) = _
    calc
      _ = ∫ x : G, k x ∂(ν.haarScalarFactor μ • μ) :=
        congrArg (fun m : MeasureTheory.Measure G ↦ ∫ x : G, k x ∂m)
          (MeasureTheory.Measure.isMulLeftInvariant_eq_smul_of_regular ν μ)
      _ = _ := by
        rw [MeasureTheory.integral_smul_nnreal_measure]
        rfl
  refine Eq.trans ?_ h1
  change (∫ x : A, f (Multiplicative.ofAdd ((↑u⁻¹ : A) * x)) *
    star ((sAdeleStandardCharacter F T (x * y) : Circle) : ℂ) ∂(sAdditiveTamagawaMeasure F T)) =
    ∫ x : A, f (Multiplicative.ofAdd ((↑u⁻¹ : A) * x)) *
      star ((sAdeleStandardCharacter F T (((↑u⁻¹ : A) * x) * ((u : A) * y)) : Circle) : ℂ)
      ∂(sAdditiveTamagawaMeasure F T)
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  change _ * star ((sAdeleStandardCharacter F T (x * y) : Circle) : ℂ) =
    _ * star ((sAdeleStandardCharacter F T (((↑u⁻¹ : A) * x) * ((u : A) * y)) : Circle) : ℂ)
  rw [mul_mul_mul_comm, Units.inv_mul, one_mul]

/-- Transfer a Fourier-region bound along an idele class. The norm-one part acts
by a scalar, so only a representative of the norm in the smaller stage is needed. -/
private theorem sLocalInvariantPW_translate_level (hST : S ⊆ T)
    (K L : Set (SAdeleRing F S)) (D : Submodule ℂ (B(T))) (hD : D = ⊤ ∨ D = Z₀(T))
    (ω : PontryaginDual J₁(T)) (g : J(T))
    (hKL : ∀ a : (SAdeleRing F S)ˣ, sIdeleNorm F S a = m(T) g →
      ∀ y : SAdeleRing F S, a.val * y ∈ K → y ∈ L)
    (x : Θ(T, ω)) (hx : x ∈ level(hST, K, D, ω)) :
    A(T, ω) g x ∈ level(hST, L, D, ω) := by
  let ρ := A(T, ω)
  have hρ : ∀ (a : (SAdeleRing F T)ˣ) (f : B(T)),
      ρ (QuotientGroup.mk a) (q(T, ω) f) = q(T, ω) (schwartzBruhatUnitTranslate a f) :=
    (existsUnique_sLocalHomogeneousThetaAction (F := F) (S := T) ω).exists.choose_spec.2
  refine map_mem_closure (ρ g).continuous hx ?_
  rintro _ ⟨f, ⟨hf, hfD⟩, rfl⟩
  obtain ⟨h, rfl, hband⟩ := (mem_sLocalPWTests hST K f).mp hf
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  let t : ℝ≥0ˣ := m(T) g
  have hsS : ∃ uS : (integralAdelesOutside F S)ˣ,
      integralIdeleInsertion F S uS = singlePlaceIdeleNormSection F w t := by
    refine (mem_range_integralIdeleInsertion F S _).mpr fun v _ ↦ ⟨?_, ?_⟩
    · exact (v.adicCompletionIntegers F).one_mem
    · change ((singlePlaceIdeleNormSection F w t)⁻¹).val.2 v ∈ _
      rw [← map_inv]
      exact (v.adicCompletionIntegers F).one_mem
  obtain ⟨uS, huS⟩ := hsS
  let gS := Units.map (adeleProjection F S).toMonoidHom (integralIdeleInsertion F S uS)
  let gT := Units.map (adeleProjection F T).toMonoidHom (integralIdeleInsertion F S uS)
  have htr : Π(hST) (schwartzBruhatUnitTranslate gS h) =
      schwartzBruhatUnitTranslate gT (Π(hST) h) := testTransition_translate_eq hST uS h
  have hnorm : m(T) (QuotientGroup.mk gT) = t := by
    obtain ⟨uT, huT⟩ := insert_mem_larger hST uS
    have hspec := (sIdeleNorm_spec F T).1 uT
    have hgT : gT = Units.map ((adeleProjection F T).comp
        (integralAdelesOutside F T).subtype).toMonoidHom uT := by
      change Units.map (adeleProjection F T).toMonoidHom (integralIdeleInsertion F S uS) = _
      rw [← huT]
      rfl
    change sIdeleNorm F T gT = t
    rw [hgT, ← hspec]
    change ideleNorm F (integralIdeleInsertion F T uT) = t
    rw [huT, huS]
    exact singlePlaceIdeleNormSection_rightInverse F w t
  have hnormS : sIdeleNorm F S gS = t := by
    change sIdeleNorm F S
      (Units.map ((adeleProjection F S).comp (integralAdelesOutside F S).subtype).toMonoidHom uS) = t
    rw [← (sIdeleNorm_spec F S).1 uS]
    change ideleNorm F (integralIdeleInsertion F S uS) = t
    rw [huS]
    exact singlePlaceIdeleNormSection_rightInverse F w t
  let g₀ : J(T) := g * (QuotientGroup.mk gT)⁻¹
  have hg₀ : g₀ ∈ (m(T)).ker := MonoidHom.mem_ker.mpr (by
    change m(T) (g * (QuotientGroup.mk gT)⁻¹) = 1
    rw [map_mul, map_inv, hnorm]
    exact mul_inv_cancel t)
  obtain ⟨v, hv⟩ := QuotientGroup.mk_surjective g₀
  have hgv : g = QuotientGroup.mk v * QuotientGroup.mk gT := by
    rw [hv]
    exact (inv_mul_cancel_right g _).symm
  let c : ℂ := (ω ⟨g₀, hg₀⟩ : ℂ)
  have hscal := sLocalHomogeneousTheta_unitTranslate ω ⟨g₀, hg₀⟩ v hv
    (schwartzBruhatUnitTranslate gT (Π(hST) h))
  have hq : q(T, ω) (schwartzBruhatUnitTranslate v (schwartzBruhatUnitTranslate gT (Π(hST) h))) =
      c • q(T, ω) (schwartzBruhatUnitTranslate gT (Π(hST) h)) := by
    rw [← map_smul]
    refine (Submodule.Quotient.eq _).mpr (LinearMap.mem_ker.mpr ?_)
    rw [map_sub, map_smul, hscal, sub_self]
  have key : ρ g (q(T, ω) (Π(hST) h)) =
      c • q(T, ω) (Π(hST) (schwartzBruhatUnitTranslate gS h)) := by
    rw [hgv, map_mul]
    change ρ (QuotientGroup.mk v) (ρ (QuotientGroup.mk gT) (q(T, ω) (Π(hST) h))) = _
    rw [hρ, hρ, hq, htr]
  change ρ g (q(T, ω) (Π(hST) h)) ∈ ((sLocalPWTests hST L ⊓ D).map (q(T, ω)))
  rw [key]
  refine Submodule.smul_mem _ _ (Submodule.mem_map_of_mem
    ⟨(mem_sLocalPWTests hST L _).mpr ⟨_, rfl, ?_⟩, ?_⟩)
  · obtain ⟨b, hb⟩ := sLocalInvariantPW_translate_fourier gS
    let e : Multiplicative (SAdeleRing F S) ≃ₜ Multiplicative (SAdeleRing F S) :=
      { toFun := fun y ↦ Multiplicative.ofAdd ((gS : SAdeleRing F S) * y.toAdd)
        invFun := fun y ↦ Multiplicative.ofAdd ((↑gS⁻¹ : SAdeleRing F S) * y.toAdd)
        left_inv := fun y ↦ Multiplicative.ext (by simp [← mul_assoc])
        right_inv := fun y ↦ Multiplicative.ext (by simp [← mul_assoc])
        continuous_toFun := continuous_ofAdd.comp (continuous_const.mul continuous_toAdd)
        continuous_invFun := continuous_ofAdd.comp (continuous_const.mul continuous_toAdd) }
    refine sLocalInvariantPW_translate_support e ((b : ℝ) : ℂ) (sAdeleSchwartzFourier h).val
      (sAdeleSchwartzFourier (schwartzBruhatUnitTranslate gS h)).val (fun y ↦ hb h y.toAdd)
      (Multiplicative.toAdd ⁻¹' K) (Multiplicative.toAdd ⁻¹' L)
      (fun y hy ↦ hKL gS hnormS y.toAdd hy) hband.1 hband.2
  · rcases hD with rfl | rfl
    · trivial
    · rw [htr]
      obtain ⟨h0, h1⟩ := (mem_sAdelePolarSubspace _).mp hfD
      obtain ⟨b, hb⟩ := sLocalInvariantPW_translate_fourier gT
      refine (mem_sAdelePolarSubspace _).mpr ⟨?_, ?_⟩
      · refine (schwartzBruhatUnitTranslate_apply gT _ 0).trans ?_
        rw [mul_zero]
        exact h0
      · rw [hb, mul_zero, h1, mul_zero]

private def sLocalPWProduct (x : SAdeleRing F S) : ℝ :=
  (∏ w : InfinitePlace F, ‖x.1 w‖ ^ w.mult) * ∏ v : S, ‖x.2 v‖

private theorem sLocalPWProduct_unit (a : (SAdeleRing F S)ˣ) :
    sLocalPWProduct a.val = ((sIdeleNorm F S a).val : ℝ) := by
  let evaluate : ((SAdeleRing F S)ˣ →* ℝ≥0ˣ) →* ℝ :=
    NNReal.toRealHom.toMonoidHom.comp ((Units.coeHom ℝ≥0).comp (MonoidHom.eval a))
  change sLocalPWProduct a.val = evaluate (sIdeleNorm F S)
  simp only [sIdeleNorm, map_mul, map_prod, map_pow]
  rfl

private theorem sLocalPWProduct_mul (x y : SAdeleRing F S) :
    sLocalPWProduct (x * y) = sLocalPWProduct x * sLocalPWProduct y := by
  unfold sLocalPWProduct
  change (∏ w : InfinitePlace F, ‖x.1 w * y.1 w‖ ^ w.mult) *
    (∏ v : S, ‖x.2 v * y.2 v‖) = _
  simp only [norm_mul, mul_pow, Finset.prod_mul_distrib]
  exact mul_mul_mul_comm _ _ _ _

private theorem sLocalInvariantPW_translate_bound (hST : S ⊆ T) (Y Z : ℝ)
    (D : Submodule ℂ (B(T))) (hD : D = ⊤ ∨ D = Z₀(T))
    (χ : PontryaginDual J₁(T)) (g : J(T))
    (hYZ : Y ≤ ((m(T) g).val : ℝ) * Z)
    (x : Θ(T, χ)) (hx : x ∈ sLocalInvariantPW hST Y D χ) :
    A(T, χ) g x ∈ sLocalInvariantPW hST Z D χ := by
  refine sLocalInvariantPW_translate_level hST _ _ D hD χ g ?_ x hx
  intro a ha y hy
  change sLocalPWProduct (a.val * y) ≤ Y at hy
  change sLocalPWProduct y ≤ Z
  rw [sLocalPWProduct_mul, sLocalPWProduct_unit, ha] at hy
  exact le_of_mul_le_mul_left (hy.trans hYZ)
    (by exact_mod_cast (pos_iff_ne_zero.mpr (Units.ne_zero (m(T) g))))

/-- Paper: Proposition 7.3.2.4(3), p. 356.
Left translation by an idele class of norm at least one preserves the invariant levels,
with or without the zero-moment constraint.
Deviation: Stated directly for the local norm-one character and the inclusion of stages. -/
theorem sLocalInvariantPW_translate (hST : S ⊆ T) {Y : ℝ} (_hY : 0 < Y)
    (D : Submodule ℂ (B(T))) (_hD : D = ⊤ ∨ D = Z₀(T))
    (ω : PontryaginDual J₁(T)) (g : J(T)) (_hg : large(g))
    (x : Θ(T, ω)) (_hx : x ∈ sLocalInvariantPW hST Y D ω) :
    A(T, ω) g x ∈ sLocalInvariantPW hST Y D ω := by
  exact sLocalInvariantPW_translate_bound hST Y Y D _hD ω g
    (le_mul_of_one_le_left _hY.le _hg) x _hx

/-- Paper: Proposition 7.3.2.4(4), p. 356.
The coordinate box bound implies the product bound with exponent the total number of places.
Both the unrestricted and the zero-moment level use the same comparison. -/
theorem sLocalAbsolutePW_le_invariant (hST : S ⊆ T) (X : ℝ) (_hX : 0 < X)
    (D : Submodule ℂ (B(T))) (ω : PontryaginDual J₁(T)) :
    sLocalAbsolutePW hST X D ω ≤ sLocalInvariantPW hST (X ^ count(S)) D ω := by
  have hbox : sLocalPWBox S X ⊆ sLocalPWProductRegion S (X ^ count(S)) := by
    intro x hx
    have ha : (∏ w : InfinitePlace F, ‖x.1 w‖ ^ w.mult) ≤ X ^ Fintype.card (InfinitePlace F) := by
      simpa only [Finset.prod_const, Finset.card_univ] using
        (Finset.prod_le_prod₀ (s := Finset.univ) (g := fun _ : InfinitePlace F ↦ X)
          (fun w _ ↦ pow_nonneg (norm_nonneg (x.1 w)) w.mult) (fun w _ ↦ hx.1 w))
    have hf : (∏ v : S, ‖x.2 v‖) ≤ X ^ S.card := by
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_coe] using
        (Finset.prod_le_prod₀ (s := Finset.univ) (g := fun _ : S ↦ X)
          (fun v _ ↦ norm_nonneg (x.2 v)) (fun v _ ↦ hx.2 v))
    change _ * _ ≤ X ^ count(S)
    rw [pow_add]
    exact mul_le_mul ha hf (Finset.prod_nonneg fun v _ ↦ norm_nonneg (x.2 v))
      (pow_nonneg _hX.le _)
  have hgen : {f : B(S) | inBand(sLocalPWBox S X, f)} ⊆
      {f : B(S) | inBand(sLocalPWProductRegion S (X ^ count(S)), f)} :=
    fun _ hf ↦ ⟨hf.1, hf.2.trans (Set.preimage_mono hbox)⟩
  have htests : sLocalPWTests hST (sLocalPWBox S X) ≤ sLocalPWTests hST (sLocalPWProductRegion S (X ^ count(S))) :=
    Submodule.map_mono (Submodule.span_mono hgen)
  exact Submodule.topologicalClosure_mono (Submodule.map_mono (inf_le_inf htests le_rfl))

section PrincipalValues

open Classical

local notation "absPW(" h ", " b ", " ω ")" => sLocalAbsolutePW h b (Z₀(_)) ω
local notation "invPW(" h ", " b ", " ω ")" => sLocalInvariantPW h b (Z₀(_)) ω

section SLocalAbsolutePWPrincipalValue

private theorem sLocalAbsolutePW_picTrivial_uniformizer
    (hPic : PicTrivial) (v : V) (hv : v ∉ S) :
    ∃ ξ : Fˣ, v.valuation F ξ = WithZero.exp (-1 : ℤ) ∧
      ∀ w ∉ S, w ≠ v → w.valuation F ξ = 1 := by
  let O_S := (S : Set V).integer F
  have : Fact (IsMulTorsion (ClassGroup (𝓞 F))) := ⟨fun x ↦ isOfFinOrder_of_finite x⟩
  have : Subsingleton (ClassGroup O_S) := (ClassGroup.equivPic O_S).toEquiv.subsingleton
  let I : Ideal O_S :=
    { carrier := {x : O_S | v.valuation F (x : F) < 1}
      zero_mem' := by simp
      add_mem' := fun {x y} hx hy ↦
        lt_of_le_of_lt (ValuationClass.map_add_le_max (v.valuation F) (x : F) (y : F)) (max_lt hx hy)
      smul_mem' := fun c {x} hx ↦ by
        change v.valuation F ((c : F) * (x : F)) < 1
        rw [map_mul]
        calc
          v.valuation F (c : F) * v.valuation F (x : F)
              ≤ 1 * v.valuation F (x : F) :=
            mul_le_mul_of_nonneg_right (Set.integer_valuation_le_one (S : Set V) F c hv) zero_le
          _ = v.valuation F (x : F) := one_mul _
          _ < 1 := hx }
  have hI_prime : I.IsPrime := by
    refine ⟨?_, fun {x y} hxy ↦ ?_⟩
    · intro h1
      have h1' : (1 : O_S) ∈ I := h1.symm ▸ trivial
      have h1_lt : v.valuation F (1 : F) < 1 := h1'
      simp at h1_lt
    · change v.valuation F ((x : F) * (y : F)) < 1 at hxy
      rw [map_mul] at hxy
      by_contra hnot
      rw [not_or] at hnot
      have hx : (1 : WithZero (Multiplicative ℤ)) ≤ v.valuation F (x : F) :=
        not_lt.mp hnot.1
      have hy : (1 : WithZero (Multiplicative ℤ)) ≤ v.valuation F (y : F) :=
        not_lt.mp hnot.2
      exact (lt_self_iff_false (1 : WithZero (Multiplicative ℤ))).mp
        (lt_of_le_of_lt (by simpa using mul_le_mul' hx hy) hxy)
  obtain ⟨π₀, hπ₀⟩ := v.intValuation_exists_uniformizer
  have hπ₀_val : v.valuation F (π₀ : F) = WithZero.exp (-1 : ℤ) := by
    simpa [HeightOneSpectrum.valuation_of_algebraMap] using hπ₀
  have hπ₀_ne : (π₀ : F) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hπ₀_val
    exact absurd hπ₀_val WithZero.zero_ne_coe
  have hπ₀_mem : (π₀ : F) ∈ O_S := fun w _ ↦ HeightOneSpectrum.valuation_le_one w π₀
  have hI_ne_bot : I ≠ ⊥ := by
    intro hbot
    have hmem : (⟨(π₀ : F), hπ₀_mem⟩ : O_S) ∈ I := by
      change v.valuation F (π₀ : F) < 1
      rw [hπ₀_val]
      decide
    rw [hbot, Ideal.mem_bot] at hmem
    exact hπ₀_ne (congrArg Subtype.val hmem)
  have hprinc : Submodule.IsPrincipal (I : Submodule O_S O_S) :=
    (ClassGroup.mk0_eq_one_iff (mem_nonZeroDivisors_iff_ne_zero.mpr hI_ne_bot)).mp
      (Subsingleton.elim _ _)
  obtain ⟨ξ, hξ⟩ := hprinc
  have hξ_eq : I = Ideal.span ({ξ} : Set O_S) := hξ
  have hξ_mem : ξ ∈ I := by
    rw [hξ_eq]
    exact Ideal.subset_span (Set.mem_singleton ξ)
  have hπ₀_in_I : (⟨(π₀ : F), hπ₀_mem⟩ : O_S) ∈ I := by
    change v.valuation F (π₀ : F) < 1
    rw [hπ₀_val]
    decide
  rw [hξ_eq] at hπ₀_in_I
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hπ₀_in_I
  have hval_v : v.valuation F (ξ : F) = WithZero.exp (-1 : ℤ) := by
    have hle : v.valuation F (ξ : F) ≤ WithZero.exp (-1 : ℤ) := by
      have hlt : v.valuation F (ξ : F) < 1 := hξ_mem
      rcases eq_or_ne (v.valuation F (ξ : F)) 0 with h0 | hne
      · simp [h0]
      · obtain ⟨m, hm⟩ := WithZero.ne_zero_iff_exists.mp hne
        rw [← hm] at hlt ⊢
        exact WithZero.coe_le_coe.mpr (Int.le_sub_one_of_lt (WithZero.coe_lt_coe.mp hlt))
    have hge : WithZero.exp (-1 : ℤ) ≤ v.valuation F (ξ : F) := by
      calc
        WithZero.exp (-1 : ℤ) = v.valuation F (π₀ : F) := hπ₀_val.symm
        _ = v.valuation F ((ξ : F) * (c : F)) := congrArg (v.valuation F) (congrArg Subtype.val hc)
        _ = v.valuation F (ξ : F) * v.valuation F (c : F) := map_mul _ _ _
        _ ≤ v.valuation F (ξ : F) * 1 :=
          mul_le_mul_of_nonneg_left (Set.integer_valuation_le_one (S : Set V) F c hv) zero_le
        _ = v.valuation F (ξ : F) := mul_one _
    exact le_antisymm hle hge
  have hξ_ne : (ξ : F) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hval_v
    exact absurd hval_v WithZero.zero_ne_coe
  refine ⟨Units.mk0 (ξ : F) hξ_ne, hval_v, fun w hw hwv ↦ ?_⟩
  refine le_antisymm (Set.integer_valuation_le_one (S : Set V) F ξ hw) ?_
  by_contra hlt
  push Not at hlt
  have hcop : w.asIdeal ⊔ v.asIdeal = ⊤ :=
    w.isMaximal.coprime_of_ne v.isMaximal (fun hvw ↦ hwv (HeightOneSpectrum.ext hvw))
  obtain ⟨a, ha, b, hb, hab⟩ :=
    Submodule.mem_sup.mp (hcop.symm ▸ (Submodule.mem_top : (1 : 𝓞 F) ∈ (⊤ : Ideal (𝓞 F))))
  have ha_mem : ((a : 𝓞 F) : F) ∈ O_S := fun u _ ↦ HeightOneSpectrum.valuation_le_one u a
  have hb_mem : ((b : 𝓞 F) : F) ∈ O_S := fun u _ ↦ HeightOneSpectrum.valuation_le_one u b
  have hb_in_I : (⟨((b : 𝓞 F) : F), hb_mem⟩ : O_S) ∈ I := by
    change v.valuation F (b : F) < 1
    simpa [HeightOneSpectrum.valuation_of_algebraMap] using
      (v.intValuation_lt_one_iff_mem b).mpr hb
  rw [hξ_eq] at hb_in_I
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp hb_in_I
  have hsum : (1 : F) = (a : F) + (ξ : F) * (d : F) := by
    have h1 := congrArg (algebraMap (𝓞 F) F) hab
    have h2 := congrArg Subtype.val hd
    simpa using h1.symm.trans (congrArg ((a : F) + ·) h2)
  have ha_lt : w.valuation F (a : F) < 1 := by
    simpa [HeightOneSpectrum.valuation_of_algebraMap] using
      (w.intValuation_lt_one_iff_mem a).mpr ha
  have hxd_lt : w.valuation F ((ξ : F) * (d : F)) < 1 := by
    rw [map_mul]
    calc
      w.valuation F (ξ : F) * w.valuation F (d : F)
          ≤ w.valuation F (ξ : F) * 1 :=
        mul_le_mul_of_nonneg_left (Set.integer_valuation_le_one (S : Set V) F d hw) zero_le
      _ = w.valuation F (ξ : F) := mul_one _
      _ < 1 := hlt
  have h1_lt : w.valuation F (1 : F) < 1 := by
    rw [hsum]
    exact lt_of_le_of_lt (ValuationClass.map_add_le_max (w.valuation F) _ _) (max_lt ha_lt hxd_lt)
  simp at h1_lt

private theorem sLocalAbsolutePW_pv_gaussian (v : V) (π : (v.adicCompletion F)ˣ)
    (hπ : (Valued.v : Valuation (v.adicCompletion F) _).IsUniformizer π.val) :
    finitePlacePrincipalValue v (finiteStandardGaussian v 1) =
      finiteStandardGaussian v 1 - schwartzBruhatUnitTranslate π (finiteStandardGaussian v 1) := by
  let : MeasurableSpace (v.adicCompletion F)ˣ := borel _
  have : BorelSpace (v.adicCompletion F)ˣ := ⟨rfl⟩
  ext x
  rw [finitePlacePrincipalValue_spec v π hπ]
  change finitePlacePrincipalValueFun v π (finiteStandardGaussian v 1) x =
    finiteStandardGaussian v 1 x - schwartzBruhatUnitTranslate π (finiteStandardGaussian v 1) x
  unfold finitePlacePrincipalValueFun
  have hpos := (finitePlacePrincipalValue_integrable v π (finiteStandardGaussian v 1) x).1
  have hcongr :
      ∫ u in (HeightOneSpectrum.adicCompletionIntegers F v).units,
          finiteStandardGaussian v 1
            (Multiplicative.ofAdd ((↑u⁻¹ : v.adicCompletion F) * ((↑π⁻¹ : v.adicCompletion F) * x.toAdd)))
        ∂(finiteLocalMultiplicativeTamagawaMeasure F v) =
      ∫ _u in (HeightOneSpectrum.adicCompletionIntegers F v).units,
          finiteStandardGaussian v 1 (Multiplicative.ofAdd ((↑π⁻¹ : v.adicCompletion F) * x.toAdd))
        ∂(finiteLocalMultiplicativeTamagawaMeasure F v) := by
    refine MeasureTheory.setIntegral_congr_fun
      (Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)).measurableSet fun u hu ↦ ?_
    change finiteStandardGaussianValue v 1 ((↑u⁻¹ : v.adicCompletion F) * ((↑π⁻¹ : v.adicCompletion F) * x.toAdd)) =
      finiteStandardGaussianValue v 1 ((↑π⁻¹ : v.adicCompletion F) * x.toAdd)
    unfold finiteStandardGaussianValue
    have hu_val : Valued.v ((↑u : v.adicCompletion F)⁻¹) = 1 := by
      have hu1 := HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp hu
      rw [map_inv₀, hu1, inv_one]
    have hmem_iff :
        ((↑u : v.adicCompletion F)⁻¹ * ((↑π : v.adicCompletion F)⁻¹ * x.toAdd) ∈
          (HeightOneSpectrum.adicCompletionIntegers F v : Set (v.adicCompletion F))) ↔
        ((↑π : v.adicCompletion F)⁻¹ * x.toAdd ∈
          (HeightOneSpectrum.adicCompletionIntegers F v : Set (v.adicCompletion F))) := by
      simp only [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers,
        map_mul, hu_val, one_mul]
    simp [Set.indicator_apply, hmem_iff]
  rw [hcongr, MeasureTheory.setIntegral_const, Complex.real_smul]
  have hne : (finiteLocalMultiplicativeTamagawaMeasure F v).real
      (HeightOneSpectrum.adicCompletionIntegers F v).units ≠ 0 := hpos.ne'
  have htrans : schwartzBruhatUnitTranslate π (finiteStandardGaussian v 1) x =
      finiteStandardGaussian v 1 (Multiplicative.ofAdd ((↑π⁻¹ : v.adicCompletion F) * x.toAdd)) := by
    rw [show x = Multiplicative.ofAdd x.toAdd from rfl, schwartzBruhatUnitTranslate_apply]
    rfl
  rw [htrans, ← mul_assoc, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hne), one_mul]

private def singleFinitePlaceIdele (T : Finset V) {v : V} (_hv : v ∈ T)
    (π : (v.adicCompletion F)ˣ) : (SAdeleRing F T)ˣ where
  val := (1, fun w : T ↦ if h : w.1 = v then h ▸ (π : v.adicCompletion F) else 1)
  inv := (1, fun w : T ↦ if h : w.1 = v then h ▸ ((π⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) else 1)
  val_inv := Prod.ext (one_mul _) (funext fun w ↦ by
    rw [Prod.snd_mul, Pi.mul_apply, Prod.snd_one, Pi.one_apply]
    dsimp only
    split_ifs with h
    · subst h; simp
    · exact mul_one 1)
  inv_val := Prod.ext (one_mul _) (funext fun w ↦ by
    rw [Prod.snd_mul, Pi.mul_apply, Prod.snd_one, Pi.one_apply]
    dsimp only
    split_ifs with h
    · subst h; simp
    · exact mul_one 1)

private theorem sLocalAbsolutePW_tensor_ext {ι : Type*} [Fintype ι] {E X Y : Type*} {W : ι → Type*}
    [AddCommGroup E] [Module ℂ E] [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (e : TensorProduct ℂ E (PiTensorProduct ℂ W) →ₗ[ℂ] X) (he : Function.Surjective e)
    (L₁ L₂ : X →ₗ[ℂ] Y)
    (h : ∀ a g, L₁ (e (TensorProduct.tmul ℂ a (PiTensorProduct.tprod ℂ g))) =
      L₂ (e (TensorProduct.tmul ℂ a (PiTensorProduct.tprod ℂ g)))) :
    L₁ = L₂ := by
  apply LinearMap.ext
  intro x
  obtain ⟨t, rfl⟩ := he x
  have key : L₁ ∘ₗ e = L₂ ∘ₗ e :=
    TensorProduct.ext (LinearMap.ext fun a ↦ PiTensorProduct.ext (MultilinearMap.ext fun g ↦ h a g))
  exact LinearMap.congr_fun key t

private theorem sLocalAbsolutePW_pv_singleton_transition (hST : S ⊆ T) {v : V}
    (hvS : v ∉ S) (hvT : v ∈ T) (π : (v.adicCompletion F)ˣ)
    (hπ : (Valued.v : Valuation (v.adicCompletion F) _).IsUniformizer π.val) (f₀ : B(S)) :
    sAdelePrincipalValue F (Finset.singleton_subset_iff.mpr hvT) (Π(hST) f₀) =
      Π(hST) f₀ -
        schwartzBruhatUnitTranslate (singleFinitePlaceIdele T hvT π) (Π(hST) f₀) := by
  let eS := (sAdeleSchwartz_inductiveTensor_equiv F S).choose
  have heS := (sAdeleSchwartz_inductiveTensor_equiv F S).choose_spec
  let eT := (sAdeleSchwartz_inductiveTensor_equiv F T).choose
  have heT := (sAdeleSchwartz_inductiveTensor_equiv F T).choose_spec
  let translateLin : B(T) →ₗ[ℂ] B(T) :=
    { toFun := schwartzBruhatUnitTranslate (singleFinitePlaceIdele T hvT π)
      map_add' := fun _ _ ↦ by ext x; rfl
      map_smul' := fun _ _ ↦ by ext x; rfl }
  let L₁ : B(S) →ₗ[ℂ] B(T) :=
    (sAdelePrincipalValue F (Finset.singleton_subset_iff.mpr hvT)).comp (Π(hST))
  let L₂ : B(S) →ₗ[ℂ] B(T) := Π(hST) - translateLin.comp (Π(hST))
  suffices hL : L₁ = L₂ from DFunLike.congr_fun hL f₀
  refine sLocalAbsolutePW_tensor_ext eS.toLinearEquiv.toLinearMap eS.surjective L₁ L₂ fun a b ↦ ?_
  let extend : ∀ w : T, SchwartzBruhat (Multiplicative (w.1.adicCompletion F)) :=
    fun w ↦ if hw : w.1 ∈ S then b ⟨w.1, hw⟩ else finiteStandardGaussian w.1 1
  have hExt : ∀ (w : T), w.1 ∉ S → ∀ y : w.1.adicCompletion F,
      extend w (Multiplicative.ofAdd y) =
        (HeightOneSpectrum.adicCompletionIntegers F w.1 : Set (w.1.adicCompletion F)).indicator
          (fun _ ↦ 1) y := by
    intro w hw y
    change (dite (w.1 ∈ S) (fun hw' ↦ b ⟨w.1, hw'⟩)
      (fun _ ↦ finiteStandardGaussian w.1 1)) (Multiplicative.ofAdd y) = _
    split_ifs
    change finiteStandardGaussianValue w.1 1 y = _
    unfold finiteStandardGaussianValue
    simp
  have heS_ext : ∀ x : SAdeleRing F S,
      eS (TensorProduct.tmul ℂ a (PiTensorProduct.tprod ℂ b)) (Multiplicative.ofAdd x) =
        a (Multiplicative.ofAdd x.1) *
          ∏ w : S, extend ⟨w.1, hST w.2⟩ (Multiplicative.ofAdd (x.2 w)) := by
    intro x
    refine (heS a b x).trans (congrArg _ (Finset.prod_congr rfl fun w _ ↦ ?_))
    have hbw : extend ⟨w.1, hST w.2⟩ = b w := by
      change (dite (w.1 ∈ S) (fun hw' ↦ b ⟨w.1, hw'⟩) (fun _ ↦ finiteStandardGaussian w.1 1)) = b w
      split_ifs with h
      · rfl
      · exact False.elim (h w.2)
    rw [hbw]
  have hPi : Π(hST) (eS (TensorProduct.tmul ℂ a (PiTensorProduct.tprod ℂ b))) =
      eT (TensorProduct.tmul ℂ a (PiTensorProduct.tprod ℂ extend)) := by
    ext x
    change (Π(hST) (eS (TensorProduct.tmul ℂ a (PiTensorProduct.tprod ℂ b)))) (Multiplicative.ofAdd x.toAdd) =
      (eT (TensorProduct.tmul ℂ a (PiTensorProduct.tprod ℂ extend))) (Multiplicative.ofAdd x.toAdd)
    exact (sAdeleSchwartzTransition_pure F hST a extend hExt _ heS_ext x.toAdd).trans
      (heT a extend x.toAdd).symm
  refine Eq.trans (congrArg (sAdelePrincipalValue F (Finset.singleton_subset_iff.mpr hvT)) hPi) ?_
  refine Eq.trans (sAdelePrincipalValue_tmul (Finset.singleton_subset_iff.mpr hvT) a extend) ?_
  refine Eq.trans ?_ (congrArg (fun z ↦ z - schwartzBruhatUnitTranslate (singleFinitePlaceIdele T hvT π) z) hPi).symm
  ext x
  have heL := heT a (fun w : T ↦
    if w.1 ∈ ({v} : Finset V) then finitePlacePrincipalValue w.1 (extend w) else extend w) x.toAdd
  have heR := heT a extend x.toAdd
  have heR_shift := heT a extend
    ((↑((singleFinitePlaceIdele T hvT π)⁻¹) : SAdeleRing F T) * x.toAdd)
  change eT (TensorProduct.tmul ℂ a (PiTensorProduct.tprod ℂ fun w ↦
      if w.1 ∈ ({v} : Finset V) then finitePlacePrincipalValue w.1 (extend w) else extend w))
      (Multiplicative.ofAdd x.toAdd) =
    eT (TensorProduct.tmul ℂ a (PiTensorProduct.tprod ℂ extend)) (Multiplicative.ofAdd x.toAdd) -
      (schwartzBruhatUnitTranslate (singleFinitePlaceIdele T hvT π)
        (eT (TensorProduct.tmul ℂ a (PiTensorProduct.tprod ℂ extend)))) (Multiplicative.ofAdd x.toAdd)
  have hshift_eval :
      (schwartzBruhatUnitTranslate (singleFinitePlaceIdele T hvT π)
        (eT (TensorProduct.tmul ℂ a (PiTensorProduct.tprod ℂ extend))))
        (Multiplicative.ofAdd x.toAdd) =
      a (Multiplicative.ofAdd x.toAdd.1) *
        ∏ w : T, extend w (Multiplicative.ofAdd
          (((↑((singleFinitePlaceIdele T hvT π)⁻¹) : SAdeleRing F T) * x.toAdd).2 w)) := by
    rw [schwartzBruhatUnitTranslate_apply]
    change eT (TensorProduct.tmul ℂ a (PiTensorProduct.tprod ℂ extend))
      (Multiplicative.ofAdd ((↑((singleFinitePlaceIdele T hvT π)⁻¹) : SAdeleRing F T) * x.toAdd)) = _
    refine heR_shift.trans ?_
    simp [singleFinitePlaceIdele]
  refine heL.trans (Eq.trans ?_ (congrArg₂ (· - ·) heR hshift_eval).symm)
  let vT : T := ⟨v, hvT⟩
  have hv_eq : extend vT = finiteStandardGaussian v 1 := by
    change (dite (vT.1 ∈ S) (fun hw' ↦ b ⟨vT.1, hw'⟩)
      (fun _ ↦ finiteStandardGaussian vT.1 1)) = finiteStandardGaussian v 1
    split_ifs with h
    · exact False.elim (hvS h)
    · rfl
  have hprodL :
      (∏ w : T, (if w.1 ∈ ({v} : Finset V) then finitePlacePrincipalValue w.1 (extend w) else extend w)
          (Multiplicative.ofAdd (x.toAdd.2 w))) =
      (finitePlacePrincipalValue v (finiteStandardGaussian v 1) (Multiplicative.ofAdd (x.toAdd.2 vT))) *
        ∏ w ∈ Finset.univ.erase vT, extend w (Multiplicative.ofAdd (x.toAdd.2 w)) := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ vT)]
    refine congrArg₂ (· * ·) ?_ (Finset.prod_congr rfl fun w hw ↦ ?_)
    · simp [vT, hv_eq]
    · have hw_ne : w.1 ≠ v := fun h ↦ (Finset.mem_erase.mp hw).1 (Subtype.ext h)
      simp [hw_ne]
  have hprodR1 :
      (∏ w : T, extend w (Multiplicative.ofAdd (x.toAdd.2 w))) =
      finiteStandardGaussian v 1 (Multiplicative.ofAdd (x.toAdd.2 vT)) *
        ∏ w ∈ Finset.univ.erase vT, extend w (Multiplicative.ofAdd (x.toAdd.2 w)) := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ vT), hv_eq]
  have hprodR2 :
      (∏ w : T, extend w (Multiplicative.ofAdd
          (((↑((singleFinitePlaceIdele T hvT π)⁻¹) : SAdeleRing F T) * x.toAdd).2 w))) =
      finiteStandardGaussian v 1 (Multiplicative.ofAdd ((↑π⁻¹ : v.adicCompletion F) * x.toAdd.2 vT)) *
        ∏ w ∈ Finset.univ.erase vT, extend w (Multiplicative.ofAdd (x.toAdd.2 w)) := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ vT)]
    refine congrArg₂ (· * ·) ?_ (Finset.prod_congr rfl fun w hw ↦ ?_)
    · simp [vT, hv_eq, singleFinitePlaceIdele]
    · have hw_ne : w.1 ≠ v := fun h ↦ (Finset.mem_erase.mp hw).1 (Subtype.ext h)
      simp [singleFinitePlaceIdele, hw_ne]
  have hpv := congrArg
    (fun g : SchwartzBruhat (Multiplicative (v.adicCompletion F)) ↦
      g (Multiplicative.ofAdd (x.toAdd.2 vT)))
    (sLocalAbsolutePW_pv_gaussian v π hπ)
  have hpv_shift :
      (schwartzBruhatUnitTranslate π (finiteStandardGaussian v 1)) (Multiplicative.ofAdd (x.toAdd.2 vT)) =
      finiteStandardGaussian v 1 (Multiplicative.ofAdd ((↑π⁻¹ : v.adicCompletion F) * x.toAdd.2 vT)) := by
    rw [schwartzBruhatUnitTranslate_apply]
  change finitePlacePrincipalValue v (finiteStandardGaussian v 1) (Multiplicative.ofAdd (x.toAdd.2 vT)) =
    finiteStandardGaussian v 1 (Multiplicative.ofAdd (x.toAdd.2 vT)) -
      (schwartzBruhatUnitTranslate π (finiteStandardGaussian v 1)) (Multiplicative.ofAdd (x.toAdd.2 vT)) at hpv
  rw [hpv_shift] at hpv
  rw [hprodL, hprodR1, hprodR2]
  change a (Multiplicative.ofAdd x.toAdd.1) *
      (finitePlacePrincipalValue v (finiteStandardGaussian v 1) (Multiplicative.ofAdd (x.toAdd.2 vT)) * _) =
    a (Multiplicative.ofAdd x.toAdd.1) *
      (finiteStandardGaussian v 1 (Multiplicative.ofAdd (x.toAdd.2 vT)) * _) -
    a (Multiplicative.ofAdd x.toAdd.1) *
      (finiteStandardGaussian v 1 (Multiplicative.ofAdd ((↑π⁻¹ : v.adicCompletion F) * x.toAdd.2 vT)) * _)
  rw [hpv]
  ring

private theorem sLocalAbsolutePW_pv_empty (h : (∅ : Finset V) ⊆ T) (χ : PontryaginDual J₁(T)) :
    PV(h, χ) = LinearMap.id := by
  apply LinearMap.ext
  intro g
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ g
  change PV(h, χ) (Submodule.Quotient.mk f) = Submodule.Quotient.mk f
  rw [sLocalHomogeneousThetaPrincipalValue_mk]
  congr 1
  suffices hlin : sAdelePrincipalValue F h = LinearMap.id from DFunLike.congr_fun hlin f
  let eT := (sAdeleSchwartz_inductiveTensor_equiv F T).choose
  refine sLocalAbsolutePW_tensor_ext eT.toLinearEquiv.toLinearMap eT.surjective
    (sAdelePrincipalValue F h) LinearMap.id fun a b ↦ ?_
  refine (sAdelePrincipalValue_tmul h a b).trans ?_
  simp only [Finset.notMem_empty, ↓reduceIte]
  rfl

private theorem sLocalAbsolutePW_pv_insert (R' : Finset V) (v : V) (hv : v ∉ R')
    (hRT : insert v R' ⊆ T) (χ : PontryaginDual J₁(T)) :
    PV(hRT, χ) =
      (PV(Finset.singleton_subset_iff.mpr (hRT (Finset.mem_insert_self v R')), χ)).comp
        (PV((Finset.subset_insert v R').trans hRT, χ)) := by
  apply LinearMap.ext
  intro g
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ g
  change PV(hRT, χ) (Submodule.Quotient.mk f) =
    PV(Finset.singleton_subset_iff.mpr (hRT (Finset.mem_insert_self v R')), χ)
      (PV((Finset.subset_insert v R').trans hRT, χ) (Submodule.Quotient.mk f))
  rw [sLocalHomogeneousThetaPrincipalValue_mk, sLocalHomogeneousThetaPrincipalValue_mk,
    sLocalHomogeneousThetaPrincipalValue_mk]
  congr 1
  let hvSub : ({v} : Finset V) ⊆ T := Finset.singleton_subset_iff.mpr (hRT (Finset.mem_insert_self v R'))
  let hR₀T : R' ⊆ T := (Finset.subset_insert v R').trans hRT
  suffices hlin : sAdelePrincipalValue F hRT =
      (sAdelePrincipalValue F hvSub).comp (sAdelePrincipalValue F hR₀T) from
    DFunLike.congr_fun hlin f
  let eT := (sAdeleSchwartz_inductiveTensor_equiv F T).choose
  refine sLocalAbsolutePW_tensor_ext eT.toLinearEquiv.toLinearMap eT.surjective
    (sAdelePrincipalValue F hRT) ((sAdelePrincipalValue F hvSub).comp (sAdelePrincipalValue F hR₀T))
    fun a b ↦ ?_
  refine (sAdelePrincipalValue_tmul hRT a b).trans ?_
  refine Eq.trans ?_ (congrArg (sAdelePrincipalValue F hvSub) (sAdelePrincipalValue_tmul hR₀T a b)).symm
  refine Eq.trans ?_ (sAdelePrincipalValue_tmul hvSub a _).symm
  congr 2
  refine congrArg (PiTensorProduct.tprod ℂ) (funext fun w ↦ ?_)
  by_cases hwv : w.1 = v
  · simp [hwv, hv]
  · simp [hwv]

private theorem sLocalAbsolutePW_unitTranslate_polar (u : (SAdeleRing F T)ˣ) (g : B(T))
    (hg : g ∈ Z₀(T)) : schwartzBruhatUnitTranslate u g ∈ Z₀(T) := by
  obtain ⟨h0, h1⟩ := (mem_sAdelePolarSubspace _).mp hg
  obtain ⟨b, hb⟩ := sLocalAbsolutePW_translate_fourier (F := F) u
  refine (mem_sAdelePolarSubspace _).mpr ⟨?_, ?_⟩
  · change schwartzBruhatUnitTranslate u g (Multiplicative.ofAdd 0) = 0
    rw [schwartzBruhatUnitTranslate_apply, mul_zero]
    exact h0
  · rw [hb g 0, mul_zero]
    exact mul_eq_zero_of_right _ h1

private theorem sLocalAbsolutePW_quotient_unitTranslate (χ : PontryaginDual J₁(T))
    (u : (SAdeleRing F T)ˣ) (hu : (QuotientGroup.mk u : J(T)) ∈ J₁(T)) (f : B(T)) :
    q(T, χ) (schwartzBruhatUnitTranslate u f) =
      (χ ⟨QuotientGroup.mk u, hu⟩ : ℂ) • q(T, χ) f := by
  let g₀ : J₁(T) := ⟨QuotientGroup.mk u, hu⟩
  let c : ℂ := ((χ g₀ : Circle) : ℂ)
  change (LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap F T χ)).mkQ
      (schwartzBruhatUnitTranslate u f) =
    c • (LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap F T χ)).mkQ f
  refine Eq.trans ?_ (Submodule.Quotient.mk_smul (LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap F T χ)) c f)
  change Submodule.Quotient.mk (schwartzBruhatUnitTranslate u f) = Submodule.Quotient.mk (c • f)
  rw [Submodule.Quotient.eq, LinearMap.mem_ker, map_sub, map_smul,
    sLocalHomogeneousTheta_unitTranslate χ g₀ u rfl f, sub_self]

private theorem sLocalAbsolutePW_principalValue_singleton
    (hST : S ⊆ T) (hPic : PicTrivial) (v : V) (hvS : v ∉ S) (hvT : v ∈ T)
    (χ : PontryaginDual J₁(T)) (Y : ℝ) (hY : 0 < Y) :
    (absPW(hST, Y, χ)).map (PV(Finset.singleton_subset_iff.mpr hvT, χ)) ≤
      absPW(hST, (v.asIdeal.absNorm : ℝ) * Y, χ) := by
  have hcl : IsClosed (absPW(hST, (v.asIdeal.absNorm : ℝ) * Y, χ) : Set Θ(T, χ)) := by
    unfold sLocalAbsolutePW
    exact Submodule.isClosed_topologicalClosure _
  refine Submodule.map_le_iff_le_comap.mpr (Submodule.topologicalClosure_minimal _ ?_
    (hcl.preimage (sLocalHomogeneousThetaPrincipalValue_isClosedEmbedding _ χ).continuous))
  rintro _ ⟨f, ⟨hf_test, hf_Z⟩, rfl⟩
  obtain ⟨f₀, rfl, hf₀⟩ := (mem_sLocalPWTests hST (sLocalPWBox S Y) f).mp hf_test
  change PV(Finset.singleton_subset_iff.mpr hvT, χ) (Submodule.Quotient.mk (Π(hST) f₀)) ∈
    absPW(hST, (v.asIdeal.absNorm : ℝ) * Y, χ)
  rw [sLocalHomogeneousThetaPrincipalValue_mk]
  obtain ⟨ξ, hξ_v, hξ_other⟩ := sLocalAbsolutePW_picTrivial_uniformizer hPic v hvS
  let πv : (v.adicCompletion F)ˣ := Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom ξ
  have hπv : (Valued.v : Valuation (v.adicCompletion F) _).IsUniformizer πv.val := by
    rw [Valuation.IsUniformizer.iff,
      congrArg Units.val (Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
        (v.valuedAdicCompletion_surjective F))]
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (ξ : F)).trans hξ_v
  let πT := singleFinitePlaceIdele T hvT πv
  rw [sLocalAbsolutePW_pv_singleton_transition hST hvS hvT πv hπv f₀]
  change q(T, χ) (Π(hST) f₀ - schwartzBruhatUnitTranslate πT (Π(hST) f₀)) ∈
    absPW(hST, (v.asIdeal.absNorm : ℝ) * Y, χ)
  rw [map_sub]
  refine Submodule.sub_mem _ ?_ ?_
  · have h1le : (1 : ℝ) ≤ (v.asIdeal.absNorm : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.mp v.ne_bot)
    have hY_le : Y ≤ (v.asIdeal.absNorm : ℝ) * Y := le_mul_of_one_le_left hY.le h1le
    exact sLocalAbsolutePW_mono hST hY_le _ _ (sLocalAbsolutePW_mk_mem hST Y _ χ f₀ hf₀ hf_Z)
  · have hξ_memT : (ξ : F) ∈ (T : Set V).integer F := by
      intro w hw
      have hwS : w ∉ S := fun h ↦ hw (hST h)
      have hwv : w ≠ v := fun h ↦ hw (h ▸ hvT)
      rw [hξ_other w hwS hwv]
    have hξinv_memT : (ξ⁻¹ : F) ∈ (T : Set V).integer F := by
      intro w hw
      have hwS : w ∉ S := fun h ↦ hw (hST h)
      have hwv : w ≠ v := fun h ↦ hw (h ▸ hvT)
      change w.valuation F (ξ : F)⁻¹ ≤ 1
      rw [map_inv₀, hξ_other w hwS hwv, inv_one]
    let u₀ : ((T : Set V).integer F)ˣ :=
      { val := ⟨ξ, hξ_memT⟩
        inv := ⟨ξ⁻¹, hξinv_memT⟩
        val_inv := Subtype.ext (mul_inv_cancel₀ ξ.ne_zero)
        inv_val := Subtype.ext (inv_mul_cancel₀ ξ.ne_zero) }
    let ξ₀_T : (SAdeleRing F T)ˣ :=
      Units.map ((adeleProjection F T).comp (integralAdelesOutside F T).subtype).toMonoidHom
        (Units.map (integralAdeleDiagonal F T).toMonoidHom u₀)
    have hξ₀_norm : sIdeleNorm F T ξ₀_T = 1 :=
      (sIdeleNorm_spec (F := F) (S := T)).2 ⟨u₀, rfl⟩
    have hξ₀_quot : (QuotientGroup.mk ξ₀_T : J(T)) = 1 :=
      (sIdeleQuotient_mk_eq_one (F := F) (S := T) ξ₀_T).mpr ⟨u₀, rfl⟩
    let w₀ : InfinitePlace F := Classical.arbitrary (InfinitePlace F)
    have hq_pos : 0 < v.asIdeal.absNorm :=
      Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.mp v.ne_bot)
    let qNN : ℝ≥0ˣ := Units.mk0 (v.asIdeal.absNorm : ℝ≥0) (Nat.cast_ne_zero.mpr hq_pos.ne')
    let x₀ : w₀.Completionˣ := infinitePlaceRealPower F w₀ (w₀.mult : ℝ)⁻¹ qNN
    have hx₀_norm : ‖(x₀ : w₀.Completion)‖ ^ w₀.mult = (v.asIdeal.absNorm : ℝ) := by
      have hx : ‖(x₀ : w₀.Completion)‖ = (v.asIdeal.absNorm : ℝ) ^ (w₀.mult : ℝ)⁻¹ := by
        rw [← (InfinitePlace.Completion.isometry_extensionEmbedding w₀).norm_map_of_map_zero
          (map_zero _) (x₀ : w₀.Completion)]
        change ‖InfinitePlace.Completion.extensionEmbedding w₀
          (infinitePlaceRealPower F w₀ (w₀.mult : ℝ)⁻¹ qNN).val‖ = _
        rw [infinitePlaceRealPower_apply, Complex.norm_real,
          Real.norm_of_nonneg (Real.rpow_nonneg qNN.val.coe_nonneg _)]
        simp [qNN]
      rw [hx, ← Real.rpow_mul_natCast (Nat.cast_nonneg _), inv_mul_cancel₀ w₀.mult_coe_ne_zero,
        Real.rpow_one]
    let tInf : (InfiniteAdeleRing F)ˣ :=
      { val := fun w ↦ if h : w = w₀ then h ▸ (x₀ : w₀.Completion) else 1
        inv := fun w ↦ if h : w = w₀ then h ▸ ((x₀⁻¹ : w₀.Completionˣ) : w₀.Completion) else 1
        val_inv := funext fun w ↦ by
          rw [Pi.mul_apply, Pi.one_apply]
          split_ifs with h
          · subst h; simp
          · exact mul_one 1
        inv_val := funext fun w ↦ by
          rw [Pi.mul_apply, Pi.one_apply]
          split_ifs with h
          · subst h; simp
          · exact mul_one 1 }
    let tS : (SAdeleRing F S)ˣ :=
      { val := (tInf.val, 1)
        inv := (tInf.inv, 1)
        val_inv := Prod.ext tInf.val_inv (one_mul _)
        inv_val := Prod.ext tInf.inv_val (one_mul _) }
    let tT : (SAdeleRing F T)ˣ :=
      { val := (tInf.val, 1)
        inv := (tInf.inv, 1)
        val_inv := Prod.ext tInf.val_inv (one_mul _)
        inv_val := Prod.ext tInf.inv_val (one_mul _) }
    let f₂ : B(S) := schwartzBruhatUnitTranslate (tS⁻¹) f₀
    have hf₂_band : inBand(sLocalPWBox S ((v.asIdeal.absNorm : ℝ) * Y), f₂) := by
      obtain ⟨b, hb⟩ := sLocalAbsolutePW_translate_fourier (F := F) (tS⁻¹)
      let e : Multiplicative (SAdeleRing F S) ≃ₜ Multiplicative (SAdeleRing F S) :=
        { toFun := fun z ↦ Multiplicative.ofAdd ((↑(tS⁻¹) : SAdeleRing F S) * z.toAdd)
          invFun := fun z ↦ Multiplicative.ofAdd ((↑tS : SAdeleRing F S) * z.toAdd)
          left_inv := fun z ↦ by
            change Multiplicative.ofAdd ((↑tS : SAdeleRing F S) * ((↑(tS⁻¹) : SAdeleRing F S) * z.toAdd)) = z
            rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
            rfl
          right_inv := fun z ↦ by
            change Multiplicative.ofAdd ((↑(tS⁻¹) : SAdeleRing F S) * ((↑tS : SAdeleRing F S) * z.toAdd)) = z
            rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
            rfl
          continuous_toFun := continuous_const_mul (M := SAdeleRing F S) _
          continuous_invFun := continuous_const_mul (M := SAdeleRing F S) _ }
      let ψ : Multiplicative (SAdeleRing F S) → ℂ := sAdeleSchwartzFourier f₂
      let φ : Multiplicative (SAdeleRing F S) → ℂ := sAdeleSchwartzFourier f₀
      have hψ : ∀ x, ψ x = ((b : ℝ) : ℂ) * φ (e x) := fun x ↦ by
        change sAdeleSchwartzFourier (schwartzBruhatUnitTranslate (tS⁻¹) f₀)
          (Multiplicative.ofAdd x.toAdd) = _
        rw [hb f₀ x.toAdd]
        rfl
      have htsup : tsupport ψ ⊆ e ⁻¹' tsupport φ := by
        refine closure_minimal (fun x hx ↦ subset_tsupport φ ?_)
          ((isClosed_tsupport φ).preimage e.continuous)
        intro h0
        apply hx
        rw [hψ x, h0, mul_zero]
      have hcomp_pre : IsCompact (e ⁻¹' tsupport φ) := by
        have himg : e ⁻¹' tsupport φ = e.symm '' tsupport φ := by
          ext z
          simp [e.symm_apply_eq]
        rw [himg]
        exact hf₀.1.isCompact.image e.symm.continuous
      have hcomp_ψ : HasCompactSupport ψ :=
        hcomp_pre.of_isClosed_subset (isClosed_tsupport ψ) htsup
      refine ⟨hcomp_ψ, htsup.trans ?_⟩
      intro x hx
      have hy : (e x).toAdd ∈ sLocalPWBox S Y := hf₀.2 hx
      have hx_eq : x.toAdd = (↑tS : SAdeleRing F S) * (e x).toAdd := by
        change x.toAdd = (↑tS : SAdeleRing F S) * ((↑(tS⁻¹) : SAdeleRing F S) * x.toAdd)
        rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
      rw [Set.mem_preimage, hx_eq]
      refine ⟨fun w ↦ ?_, fun u ↦ ?_⟩
      · change ‖tS.val.1 w * (e x).toAdd.1 w‖ ^ w.mult ≤ (v.asIdeal.absNorm : ℝ) * Y
        rw [norm_mul, mul_pow]
        by_cases hw : w = w₀
        · subst hw
          have ht_w : ‖tS.val.1 w₀‖ ^ w₀.mult = (v.asIdeal.absNorm : ℝ) := by
            have heq : tInf.val w₀ = (x₀ : w₀.Completion) := by
              change (if h : w₀ = w₀ then _ else 1) = _
              simp
            change ‖tInf.val w₀‖ ^ w₀.mult = _
            rw [heq]
            exact hx₀_norm
          rw [ht_w]
          exact mul_le_mul_of_nonneg_left (hy.1 w₀) (Nat.cast_nonneg _)
        · have ht_w : ‖tS.val.1 w‖ ^ w.mult = 1 := by
            have heq : tInf.val w = 1 := by
              change (if h : w = w₀ then _ else 1) = 1
              simp [hw]
            change ‖tInf.val w‖ ^ w.mult = 1
            rw [heq, norm_one, one_pow]
          rw [ht_w, one_mul]
          have h1le : (1 : ℝ) ≤ (v.asIdeal.absNorm : ℝ) := by exact_mod_cast hq_pos
          exact (hy.1 w).trans (le_mul_of_one_le_left hY.le h1le)
      · change ‖(tS.val.2 u) * (e x).toAdd.2 u‖ ≤ (v.asIdeal.absNorm : ℝ) * Y
        have ht_u : tS.val.2 u = 1 := rfl
        rw [ht_u, one_mul]
        have h1le : (1 : ℝ) ≤ (v.asIdeal.absNorm : ℝ) := by exact_mod_cast hq_pos
        exact (hy.2 u).trans (le_mul_of_one_le_left hY.le h1le)
    have hPi_f₂ : Π(hST) f₂ = schwartzBruhatUnitTranslate (tT⁻¹) (Π(hST) f₀) := by
      ext x
      rw [show x = Multiplicative.ofAdd x.toAdd from rfl, sAdeleSchwartzTransition_apply,
        schwartzBruhatUnitTranslate_apply]
      change (if ∀ w : T, w.1 ∉ S → x.toAdd.2 w ∈ w.1.adicCompletionIntegers F then
          f₂ (Multiplicative.ofAdd (x.toAdd.1, fun w : S ↦ x.toAdd.2 ⟨w.1, hST w.2⟩)) else 0) =
        (Π(hST) f₀) (Multiplicative.ofAdd ((↑(tT⁻¹)⁻¹ : SAdeleRing F T) * x.toAdd))
      rw [inv_inv, sAdeleSchwartzTransition_apply]
      have hfin : ((↑tT : SAdeleRing F T) * x.toAdd).2 = x.toAdd.2 := by
        ext w
        simp [tT]
      have hmem_iff :
          (∀ w : T, w.1 ∉ S → x.toAdd.2 w ∈ w.1.adicCompletionIntegers F) ↔
          (∀ w : T, w.1 ∉ S → ((↑tT : SAdeleRing F T) * x.toAdd).2 w ∈ w.1.adicCompletionIntegers F) := by
        simp [hfin]
      by_cases hcond : ∀ w : T, w.1 ∉ S → x.toAdd.2 w ∈ w.1.adicCompletionIntegers F
      · rw [ite_eq_left hcond, ite_eq_left (hmem_iff.mp hcond), schwartzBruhatUnitTranslate_apply]
        change f₀ (Multiplicative.ofAdd ((↑(tS⁻¹)⁻¹ : SAdeleRing F S) * (x.toAdd.1, fun w : S ↦ x.toAdd.2 ⟨w.1, hST w.2⟩))) =
          f₀ (Multiplicative.ofAdd (((↑tT : SAdeleRing F T) * x.toAdd).1, fun w : S ↦ ((↑tT : SAdeleRing F T) * x.toAdd).2 ⟨w.1, hST w.2⟩))
        rw [inv_inv]
        congr 2
      · rw [ite_eq_right hcond, ite_eq_right (mt hmem_iff.mpr hcond)]
    have hf₂_Z : Π(hST) f₂ ∈ Z₀(T) := by
      rw [hPi_f₂]
      exact sLocalAbsolutePW_unitTranslate_polar (tT⁻¹) (Π(hST) f₀) hf_Z
    let aT : (SAdeleRing F T)ˣ :=
      { val := (tInf.inv * ξ₀_T.val.1,
          fun w : T ↦ if w.1 = v then 1 else ξ₀_T.val.2 w)
        inv := (tInf.val * ξ₀_T.inv.1,
          fun w : T ↦ if w.1 = v then 1 else ξ₀_T.inv.2 w)
        val_inv := Prod.ext (funext fun w ↦ by
          have hξ := congrFun (Prod.ext_iff.mp ξ₀_T.val_inv).1 w
          have ht := congrFun tInf.inv_val w
          rw [Prod.fst_mul, Pi.mul_apply, Prod.fst_one, Pi.one_apply] at hξ
          rw [Pi.mul_apply, Pi.one_apply] at ht
          change (tInf.inv w * ξ₀_T.val.1 w) * (tInf.val w * ξ₀_T.inv.1 w) = 1
          calc
            tInf.inv w * ξ₀_T.val.1 w * (tInf.val w * ξ₀_T.inv.1 w)
                = (tInf.inv w * tInf.val w) * (ξ₀_T.val.1 w * ξ₀_T.inv.1 w) := by ring
            _ = 1 * 1 := by rw [ht, hξ]
            _ = 1 := one_mul 1) (funext fun w ↦ by
          have hξ := congrFun (Prod.ext_iff.mp ξ₀_T.val_inv).2 w
          rw [Prod.snd_mul, Pi.mul_apply, Prod.snd_one, Pi.one_apply] at hξ ⊢
          change (if w.1 = v then 1 else ξ₀_T.val.2 w) *
              (if w.1 = v then 1 else ξ₀_T.inv.2 w) = 1
          split_ifs
          · exact one_mul 1
          · exact hξ)
        inv_val := Prod.ext (funext fun w ↦ by
          have hξ := congrFun (Prod.ext_iff.mp ξ₀_T.inv_val).1 w
          have ht := congrFun tInf.val_inv w
          rw [Prod.fst_mul, Pi.mul_apply, Prod.fst_one, Pi.one_apply] at hξ
          rw [Pi.mul_apply, Pi.one_apply] at ht
          change (tInf.val w * ξ₀_T.inv.1 w) * (tInf.inv w * ξ₀_T.val.1 w) = 1
          calc
            tInf.val w * ξ₀_T.inv.1 w * (tInf.inv w * ξ₀_T.val.1 w)
                = (tInf.val w * tInf.inv w) * (ξ₀_T.inv.1 w * ξ₀_T.val.1 w) := by ring
            _ = 1 * 1 := by rw [ht, hξ]
            _ = 1 := one_mul 1) (funext fun w ↦ by
          have hξ := congrFun (Prod.ext_iff.mp ξ₀_T.inv_val).2 w
          rw [Prod.snd_mul, Pi.mul_apply, Prod.snd_one, Pi.one_apply] at hξ ⊢
          change (if w.1 = v then 1 else ξ₀_T.inv.2 w) *
              (if w.1 = v then 1 else ξ₀_T.val.2 w) = 1
          split_ifs
          · exact one_mul 1
          · exact hξ) }
    have haT_mul : aT * πT = ξ₀_T * tT⁻¹ := by
      apply Units.ext
      apply Prod.ext
      · funext w
        change tInf.inv w * ξ₀_T.val.1 w * 1 = ξ₀_T.val.1 w * tInf.inv w
        ring
      · funext w
        change (if w.1 = v then 1 else ξ₀_T.val.2 w) *
            (if h : w.1 = v then h ▸ (πv : v.adicCompletion F) else 1) =
          ξ₀_T.val.2 w * 1
        by_cases hwv : w.1 = v
        · simp only [hwv, ↓reduceIte, one_mul, mul_one]
          rcases w with ⟨wval, hwT⟩
          dsimp at hwv
          subst hwv
          rfl
        · simp [hwv]
    have haT_norm : sIdeleNorm F T aT = 1 := by
      apply Units.ext
      apply NNReal.eq
      have hξ_eq : (sIdeleNorm F T ξ₀_T : ℝ) = 1 := by
        rw [hξ₀_norm]
        rfl
      have hnorm_formula (u : (SAdeleRing F T)ˣ) :
          ((sIdeleNorm F T u : ℝ≥0) : ℝ) =
            (∏ w : InfinitePlace F, ‖u.val.1 w‖ ^ w.mult) * ∏ w : T, ‖u.val.2 w‖ := by
        simp [sIdeleNorm]
      have hprod_inf :
          (∏ w : InfinitePlace F, ‖aT.val.1 w‖ ^ w.mult) =
            (v.asIdeal.absNorm : ℝ)⁻¹ * ∏ w : InfinitePlace F, ‖ξ₀_T.val.1 w‖ ^ w.mult := by
        have heq : (∏ w : InfinitePlace F, ‖aT.val.1 w‖ ^ w.mult) =
            ∏ w : InfinitePlace F, (‖tInf.inv w‖ ^ w.mult * ‖ξ₀_T.val.1 w‖ ^ w.mult) := by
          refine Finset.prod_congr rfl fun w _ ↦ ?_
          change ‖tInf.inv w * ξ₀_T.val.1 w‖ ^ w.mult = _
          rw [norm_mul, mul_pow]
        rw [heq, Finset.prod_mul_distrib]
        congr 1
        rw [Finset.prod_eq_single_of_mem w₀ (Finset.mem_univ _)]
        · have hxinv : ‖tInf.inv w₀‖ ^ w₀.mult = (v.asIdeal.absNorm : ℝ)⁻¹ := by
            have hmul : ‖tInf.val w₀‖ ^ w₀.mult * ‖tInf.inv w₀‖ ^ w₀.mult = 1 := by
              rw [← mul_pow, ← norm_mul]
              have hv := congrFun tInf.val_inv w₀
              rw [Pi.mul_apply, Pi.one_apply] at hv
              rw [hv, norm_one, one_pow]
            have hval : ‖tInf.val w₀‖ ^ w₀.mult = (v.asIdeal.absNorm : ℝ) := by
              have heq : tInf.val w₀ = (x₀ : w₀.Completion) := by
                change (if h : w₀ = w₀ then _ else 1) = _
                simp
              change ‖tInf.val w₀‖ ^ w₀.mult = _
              rw [heq]
              exact hx₀_norm
            rw [hval] at hmul
            exact eq_inv_of_mul_eq_one_right hmul
          exact hxinv
        · intro w _ hw
          have heq : tInf.inv w = 1 := by
            change (if h : w = w₀ then _ else 1) = 1
            split_ifs with h
            · exact absurd h hw
            · rfl
          change ‖tInf.inv w‖ ^ w.mult = 1
          rw [heq, norm_one, one_pow]
      have hprod_fin :
          (∏ w : T, ‖aT.val.2 w‖) * (v.asIdeal.absNorm : ℝ)⁻¹ = ∏ w : T, ‖ξ₀_T.val.2 w‖ := by
        let vT : T := ⟨v, hvT⟩
        rw [← Finset.mul_prod_erase Finset.univ (fun w : T ↦ ‖aT.val.2 w‖) (Finset.mem_univ vT),
          ← Finset.mul_prod_erase Finset.univ (fun w : T ↦ ‖ξ₀_T.val.2 w‖) (Finset.mem_univ vT)]
        have ha_v : ‖aT.val.2 vT‖ = 1 := by simp [aT, vT]
        have hξ_vnorm : ‖ξ₀_T.val.2 vT‖ = (v.asIdeal.absNorm : ℝ)⁻¹ := by
          change ‖(πv : v.adicCompletion F)‖ = _
          exact norm_uniformizer_adicCompletion v πv.val hπv
        have hrest : (∏ w ∈ Finset.univ.erase vT, ‖aT.val.2 w‖) =
            ∏ w ∈ Finset.univ.erase vT, ‖ξ₀_T.val.2 w‖ := by
          refine Finset.prod_congr rfl fun w hw ↦ ?_
          have hwv : w.1 ≠ v := fun h ↦ (Finset.mem_erase.mp hw).1 (Subtype.ext h)
          simp [aT, hwv]
        rw [ha_v, one_mul, hξ_vnorm, hrest, mul_comm]
      rw [hnorm_formula aT, hprod_inf]
      calc
        ((v.asIdeal.absNorm : ℝ)⁻¹ * ∏ w : InfinitePlace F, ‖ξ₀_T.val.1 w‖ ^ w.mult) *
            ∏ w : T, ‖aT.val.2 w‖
            = (∏ w : InfinitePlace F, ‖ξ₀_T.val.1 w‖ ^ w.mult) *
              ((∏ w : T, ‖aT.val.2 w‖) * (v.asIdeal.absNorm : ℝ)⁻¹) := by ring
        _ = (∏ w : InfinitePlace F, ‖ξ₀_T.val.1 w‖ ^ w.mult) * ∏ w : T, ‖ξ₀_T.val.2 w‖ := by
          rw [hprod_fin]
        _ = ((sIdeleNorm F T ξ₀_T : ℝ≥0) : ℝ) := (hnorm_formula ξ₀_T).symm
        _ = 1 := hξ_eq
    have hshift_eq :
        schwartzBruhatUnitTranslate πT (Π(hST) f₀) =
          schwartzBruhatUnitTranslate (aT⁻¹) (schwartzBruhatUnitTranslate ξ₀_T (Π(hST) f₂)) := by
      ext x
      rw [show x = Multiplicative.ofAdd x.toAdd from rfl, schwartzBruhatUnitTranslate_apply,
        schwartzBruhatUnitTranslate_apply, schwartzBruhatUnitTranslate_apply, hPi_f₂,
        schwartzBruhatUnitTranslate_apply]
      refine congrArg (fun z ↦ (Π(hST) f₀) (Multiplicative.ofAdd z)) ?_
      have hunit_eq : πT⁻¹ = tT * ξ₀_T⁻¹ * aT := by
        refine inv_eq_iff_mul_eq_one.mpr ?_
        calc
          πT * (tT * ξ₀_T⁻¹ * aT) = (aT * πT) * (tT * ξ₀_T⁻¹) := by ac_rfl
          _ = (ξ₀_T * tT⁻¹) * (tT * ξ₀_T⁻¹) := by rw [haT_mul]
          _ = (ξ₀_T * ξ₀_T⁻¹) * (tT⁻¹ * tT) := by ac_rfl
          _ = 1 := by simp
      calc
        (↑(πT⁻¹) : SAdeleRing F T) * x.toAdd
            = (↑(tT * ξ₀_T⁻¹ * aT) : SAdeleRing F T) * x.toAdd := by rw [hunit_eq]
        _ = (↑(tT⁻¹)⁻¹ : SAdeleRing F T) *
              ((↑(ξ₀_T⁻¹) : SAdeleRing F T) * ((↑(aT⁻¹)⁻¹ : SAdeleRing F T) * x.toAdd)) := by
          simp only [inv_inv, Units.val_mul, mul_assoc]
    rw [hshift_eq]
    have haTinv_mem : (QuotientGroup.mk (aT⁻¹) : J(T)) ∈ J₁(T) := by
      change sIdeleQuotientNorm F T (QuotientGroup.mk (aT⁻¹)) = 1
      rw [sIdeleQuotientNorm_mk, map_inv, haT_norm, inv_one]
    have hξ₀_mem : (QuotientGroup.mk ξ₀_T : J(T)) ∈ J₁(T) := by
      change sIdeleQuotientNorm F T (QuotientGroup.mk ξ₀_T) = 1
      rw [sIdeleQuotientNorm_mk, hξ₀_norm]
    rw [sLocalAbsolutePW_quotient_unitTranslate χ (aT⁻¹) haTinv_mem,
      sLocalAbsolutePW_quotient_unitTranslate χ ξ₀_T hξ₀_mem]
    have hξ₁ : (⟨QuotientGroup.mk ξ₀_T, hξ₀_mem⟩ : J₁(T)) = 1 := Subtype.ext hξ₀_quot
    rw [hξ₁, map_one]
    simp only [Circle.coe_one, one_smul]
    exact Submodule.smul_mem _ _
      (sLocalAbsolutePW_mk_mem hST ((v.asIdeal.absNorm : ℝ) * Y) _ χ f₂ hf₂_band hf₂_Z)

private theorem sLocalAbsolutePW_principalValue_aux
    (hST : S ⊆ T) (hPic : PicTrivial) (R' : Finset V) :
    ∀ (hRT : R' ⊆ T), Disjoint S R' → ∀ (χ : PontryaginDual J₁(T)) (Y : ℝ), 0 < Y →
      (absPW(hST, Y, χ)).map (PV(hRT, χ)) ≤ absPW(hST, size(R') * Y, χ) := by
  induction R' using Finset.induction_on with
  | empty =>
    intro hRT _ χ Y _
    rw [sLocalAbsolutePW_pv_empty hRT χ, Submodule.map_id, Finset.prod_empty, one_mul]
  | @insert v R₀ hv ih =>
    intro hRT hRdis χ Y hY
    have hR₀T : R₀ ⊆ T := (Finset.subset_insert v R₀).trans hRT
    have hvT : v ∈ T := hRT (Finset.mem_insert_self v R₀)
    have hvS : v ∉ S := Finset.disjoint_right.mp hRdis (Finset.mem_insert_self v R₀)
    have hR₀dis : Disjoint S R₀ := hRdis.mono_right (Finset.subset_insert v R₀)
    have hR₀pos : 0 < size(R₀) := Finset.prod_pos fun w _ ↦ Nat.cast_pos.mpr
      (Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.mp w.ne_bot))
    rw [sLocalAbsolutePW_pv_insert R₀ v hv hRT χ, Submodule.map_comp]
    refine (Submodule.map_mono (ih hR₀T hR₀dis χ Y hY)).trans ?_
    rw [Finset.prod_insert hv, mul_assoc]
    exact sLocalAbsolutePW_principalValue_singleton hST hPic v hvS hvT χ
      (size(R₀) * Y) (mul_pos hR₀pos hY)

end SLocalAbsolutePWPrincipalValue

/-- Paper: Proposition 7.3.3.2, p. 357–358.
The finite principal value maps the zero-moment absolute level at X into the
absolute level at the product of the residue sizes times X. -/
theorem sLocalAbsolutePW_principalValue {S₀ : Finset (HeightOneSpectrum (𝓞 F))}
    (hST : S ⊆ T) (_hT : T = S ∪ S₀)
    (hRT : R ⊆ T) (_hR : R ⊆ S₀) (_hsatR : IsSaturatedPlaceSet (F := F) R)
    (_hdis : Disjoint S S₀) (_hsat : IsSaturatedPlaceSet (F := F) S₀) (_hPic : PicTrivial)
    (ω : PontryaginDual C₁) (hu : NormOneCharacterUnramifiedOutside ω S)
    (χ : PontryaginDual J₁(T)) (_hχ : χ = descend(hST, ω, hu))
    (X : ℝ) (_hX : 0 < X) :
    (absPW(hST, X, χ)).map (PV(hRT, χ)) ≤ absPW(hST, size(R) * X, χ) :=
  sLocalAbsolutePW_principalValue_aux hST _hPic R hRT (_hdis.mono_right _hR) χ X _hX

local notation "B∞" => SchwartzBruhat (Multiplicative (InfiniteAdeleRing F))
local notation "Bᵥ[" v "]" => SchwartzBruhat (Multiplicative (HeightOneSpectrum.adicCompletion F v))

-- The normalized unit integral on the integer indicator is its value at the
-- dilated point, as in the singleton Gaussian calculation in Chapter 11, Sec1b.
private theorem sLocalPW_integer_gaussian (v : V) (x : v.adicCompletion F) :
    finiteStandardGaussian v 1 (Multiplicative.ofAdd x) =
      if Valued.v x ≤ 1 then 1 else 0 := by
  change finiteStandardGaussianValue v 1 x = _
  have h : ∀ u ∈ (v.adicCompletionIntegers F).units, (1 : QuasiCharacter (v.adicCompletion F)ˣ) u = 1 :=
    fun u _ ↦ rfl
  rw [finiteStandardGaussianValue, ite_eq_left h]
  change (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ ↦ (1 : ℂ)) x = _
  by_cases hx : Valued.v x ≤ 1
  · rw [Set.indicator_of_mem (show x ∈ v.adicCompletionIntegers F from hx), ite_eq_left hx]
  · rw [Set.indicator_of_notMem (show x ∉ v.adicCompletionIntegers F from hx), ite_eq_right hx]

private theorem sLocalPW_principalValue_gaussian (v : V) (x : v.adicCompletion F)
    (p : v.adicCompletion F)
    (hp : (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).IsUniformizer p) :
    let π := Units.mk0 p hp.ne_zero
    finitePlacePrincipalValue v (finiteStandardGaussian v 1) (Multiplicative.ofAdd x) =
      finiteStandardGaussian v 1 (Multiplicative.ofAdd x) -
        finiteStandardGaussian v 1 (Multiplicative.ofAdd ((↑π⁻¹ : v.adicCompletion F) * x)) := by
  intro π
  let K := v.adicCompletion F
  let U := (v.adicCompletionIntegers F).units
  let : MeasurableSpace Kˣ := borel _
  let : BorelSpace Kˣ := ⟨rfl⟩
  let μ := finiteLocalMultiplicativeTamagawaMeasure F v
  let z := (↑π⁻¹ : K) * x
  let g := finiteStandardGaussian v 1
  have havg : (∫ u in U, g (Multiplicative.ofAdd ((↑u⁻¹ : K) * z)) ∂μ) =
      (μ.real U : ℂ) * g (Multiplicative.ofAdd z) := by
    calc
      _ = ∫ _u in U, g (Multiplicative.ofAdd z) ∂μ := by
        have hU : IsOpen (U : Set Kˣ) := Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)
        apply MeasureTheory.setIntegral_congr_fun hU.measurableSet
        intro u hu
        have hv := HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp (show u ∈ U from hu)
        have hui : Valued.v (↑u⁻¹ : K) = 1 := by rw [Units.val_inv_eq_inv_val, map_inv₀, hv, inv_one]
        dsimp only [g]
        rw [sLocalPW_integer_gaussian, sLocalPW_integer_gaussian, map_mul, hui, one_mul]
      _ = _ := by rw [MeasureTheory.setIntegral_const, Complex.real_smul]
  have hm : (μ.real U : ℂ) ≠ 0 := by
    exact_mod_cast (finitePlacePrincipalValue_integrable v π g (Multiplicative.ofAdd x)).1.ne'
  rw [finitePlacePrincipalValue_spec v π hp]
  change g (Multiplicative.ofAdd x) - (μ.real U : ℂ)⁻¹ *
    (∫ u in U, g (Multiplicative.ofAdd ((↑u⁻¹ : K) * z)) ∂μ) = _
  rw [havg, inv_mul_cancel_left₀ hm]

private def sLocalPW_singlePlaceUnit (v : T) (π : (v.val.adicCompletion F)ˣ) :
    (SAdeleRing F T)ˣ where
  val := (1, Pi.mulSingle (M := fun w : T ↦ w.val.adicCompletion F) v (π : v.val.adicCompletion F))
  inv := (1, Pi.mulSingle (M := fun w : T ↦ w.val.adicCompletion F) v (↑π⁻¹ : v.val.adicCompletion F))
  val_inv := Prod.ext (one_mul _) (funext fun w ↦ by
    change Pi.mulSingle (M := fun w : T ↦ w.val.adicCompletion F) v (π : v.val.adicCompletion F) w *
      Pi.mulSingle (M := fun w : T ↦ w.val.adicCompletion F) v (↑π⁻¹ : v.val.adicCompletion F) w = 1
    by_cases hw : w = v
    · subst w
      simp
    · simp [Pi.mulSingle_eq_of_ne hw])
  inv_val := Prod.ext (one_mul _) (funext fun w ↦ by
    change Pi.mulSingle (M := fun w : T ↦ w.val.adicCompletion F) v (↑π⁻¹ : v.val.adicCompletion F) w *
      Pi.mulSingle (M := fun w : T ↦ w.val.adicCompletion F) v (π : v.val.adicCompletion F) w = 1
    by_cases hw : w = v
    · subst w
      simp
    · simp [Pi.mulSingle_eq_of_ne hw])

private theorem sLocalPW_singlePlaceUnit_norm (v : T) (p : v.val.adicCompletion F)
    (hp : (Valued.v : Valuation (v.val.adicCompletion F) (WithZero (Multiplicative ℤ))).IsUniformizer p) :
    ((sIdeleNorm F T (sLocalPW_singlePlaceUnit v (Units.mk0 p hp.ne_zero))).val : ℝ) =
      (v.val.asIdeal.absNorm : ℝ)⁻¹ := by
  rw [← sLocalPWProduct_unit]
  change (∏ w : InfinitePlace F, ‖(1 : w.Completion)‖ ^ w.mult) *
    (∏ w : T, ‖Pi.mulSingle (M := fun w : T ↦ w.val.adicCompletion F) v p w‖) = _
  simp only [norm_one, one_pow, Finset.prod_const_one, one_mul]
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ v)]
  rw [Pi.mulSingle_eq_same, norm_uniformizer_adicCompletion v.val _ hp]
  have h : (∏ w ∈ Finset.univ.erase v,
        ‖Pi.mulSingle (M := fun w : T ↦ w.val.adicCompletion F) v p w‖) = 1 :=
    Finset.prod_eq_one fun w hw ↦ by
      rw [Pi.mulSingle_eq_of_ne (Finset.ne_of_mem_erase hw), norm_one]
  rw [h, one_mul]

open scoped TensorProduct in
private theorem sLocalPW_transition_tmul (hST : S ⊆ T)
    (a : B∞) (g : ∀ w : S, Bᵥ[w.val]) :
    let f := (sAdeleSchwartz_inductiveTensor_equiv F S).choose (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g w))
    let G (w : T) : Bᵥ[w.val] :=
      if hw : w.val ∈ S then g ⟨w.val, hw⟩ else finiteStandardGaussian w.val 1
    Π(hST) f = (sAdeleSchwartz_inductiveTensor_equiv F T).choose (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, G w)) := by
  intro f G
  have hG (w : T) (hw : w.val ∉ S) (z : w.val.adicCompletion F) :
      G w (Multiplicative.ofAdd z) =
        (w.val.adicCompletionIntegers F : Set (w.val.adicCompletion F)).indicator (fun _ ↦ 1) z := by
    rw [show G w = finiteStandardGaussian w.val 1 from dite_eq_right hw]
    change finiteStandardGaussianValue w.val 1 z = _
    unfold finiteStandardGaussianValue
    exact ite_eq_left fun _ _ ↦ rfl
  have hr (w : S) : G ⟨w.val, hST w.property⟩ = g w := dite_eq_left w.property
  apply Subtype.ext
  funext x
  with_reducible refine Eq.trans ?_ ((sAdeleSchwartz_inductiveTensor_equiv F T).choose_spec a G x.toAdd).symm
  change Π(hST) f (Multiplicative.ofAdd x.toAdd) = _
  with_reducible refine sAdeleSchwartzTransition_pure F hST a G hG f ?_ x.toAdd
  intro z
  simp only [hr]
  with_reducible exact (sAdeleSchwartz_inductiveTensor_equiv F S).choose_spec a g z

open scoped TensorProduct in
private theorem sLocalPW_principalValue_singleton_tmul (hST : S ⊆ T) (v : T)
    (hv : v.val ∉ S) (h : ({v.val} : Finset V) ⊆ T)
    (p : v.val.adicCompletion F)
    (hp : (Valued.v : Valuation (v.val.adicCompletion F) (WithZero (Multiplicative ℤ))).IsUniformizer p)
    (a : B∞) (g : ∀ w : S, Bᵥ[w.val]) (x : SAdeleRing F T) :
    let f := (sAdeleSchwartz_inductiveTensor_equiv F S).choose (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g w))
    let u := sLocalPW_singlePlaceUnit v (Units.mk0 p hp.ne_zero)
    sAdelePrincipalValue F h (Π(hST) f) (Multiplicative.ofAdd x) =
      Π(hST) f (Multiplicative.ofAdd x) -
        Π(hST) f (Multiplicative.ofAdd ((↑u⁻¹ : SAdeleRing F T) * x)) := by
  intro f u
  let G (w : T) : Bᵥ[w.val] :=
    if hw : w.val ∈ S then g ⟨w.val, hw⟩ else finiteStandardGaussian w.val 1
  let P (w : T) := if w.val ∈ ({v.val} : Finset V) then finitePlacePrincipalValue w.val (G w) else G w
  let e := (sAdeleSchwartz_inductiveTensor_equiv F T).choose
  let fT : B(T) := e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, G w))
  let fP : B(T) := e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, P w))
  let y : SAdeleRing F T := (↑u⁻¹ : SAdeleRing F T) * x
  have hT : Π(hST) f = fT := sLocalPW_transition_tmul hST a g
  have hPV : sAdelePrincipalValue F h fT = fP := sAdelePrincipalValue_tmul h a G
  have hpure (z : SAdeleRing F T) :
      fT (Multiplicative.ofAdd z) = a (Multiplicative.ofAdd z.1) *
        ∏ w : T, G w (Multiplicative.ofAdd (z.2 w)) := by
    with_reducible exact (sAdeleSchwartz_inductiveTensor_equiv F T).choose_spec a G z
  have hiver :
      fP (Multiplicative.ofAdd x) = a (Multiplicative.ofAdd x.1) *
        ∏ w : T, P w (Multiplicative.ofAdd (x.2 w)) := by
    with_reducible exact (sAdeleSchwartz_inductiveTensor_equiv F T).choose_spec a P x
  with_reducible rw [hT, hPV, hiver, hpure x, hpure y]
  have hy : y.1 = x.1 := one_mul _
  rw [hy]
  let π := Units.mk0 p hp.ne_zero
  have hx (w : T) (hw : w ∈ Finset.univ.erase v) : y.2 w = x.2 w := by
    change Pi.mulSingle (M := fun w : T ↦ w.val.adicCompletion F) v
      (↑π⁻¹ : v.val.adicCompletion F) w * x.2 w = _
    rw [Pi.mulSingle_eq_of_ne (Finset.ne_of_mem_erase hw), one_mul]
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ v),
    ← Finset.prod_erase_mul _ _ (Finset.mem_univ v),
    ← Finset.prod_erase_mul _ _ (Finset.mem_univ v)]
  have hP : (∏ w ∈ Finset.univ.erase v, P w (Multiplicative.ofAdd (x.2 w))) =
      ∏ w ∈ Finset.univ.erase v, G w (Multiplicative.ofAdd (x.2 w)) := by
    refine Finset.prod_congr rfl fun w hw ↦ ?_
    have hne : w.val ≠ v.val := fun hEq ↦ Finset.ne_of_mem_erase hw (Subtype.ext hEq)
    rw [show P w = G w from ite_eq_right (by simpa using hne)]
  have hG : (∏ w ∈ Finset.univ.erase v, G w (Multiplicative.ofAdd (y.2 w))) =
      ∏ w ∈ Finset.univ.erase v, G w (Multiplicative.ofAdd (x.2 w)) :=
    Finset.prod_congr rfl fun w hw ↦ by rw [hx w hw]
  rw [hP, hG, show P v = finitePlacePrincipalValue v.val (G v) from ite_eq_left (Finset.mem_singleton_self _),
    show G v = finiteStandardGaussian v.val 1 from dite_eq_right hv,
    sLocalPW_principalValue_gaussian v.val (x.2 v) p hp]
  have hyv : y.2 v = (↑π⁻¹ : v.val.adicCompletion F) * x.2 v := by
    change Pi.mulSingle (M := fun w : T ↦ w.val.adicCompletion F) v
      (↑π⁻¹ : v.val.adicCompletion F) v * _ = _
    rw [Pi.mulSingle_eq_same]
  rw [hyv, mul_sub, mul_sub]

-- Tensor extensionality on the same small-stage generators as the cutoff calculation.
open scoped TensorProduct in
private theorem sLocalPW_linear_eq_on_pure {A B : Type*} [AddCommGroup A] [Module ℂ A]
    [TopologicalSpace A] [AddCommGroup B] [Module ℂ B] [TopologicalSpace B]
    {ι : Type*} {D : ι → Type*} [∀ i, AddCommGroup (D i)] [∀ i, Module ℂ (D i)]
    (E : InductiveTensor A (FinestLocallyConvex (⨂[ℂ] i, D i)) ≃L[ℂ] B)
    (L R : B →ₗ[ℂ] ℂ)
    (h : ∀ (a : A) (g : ∀ i, D i), L (E (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] i, g i))) =
      R (E (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] i, g i)))) : L = R := by
  let W := FinestLocallyConvex (⨂[ℂ] i, D i)
  have H : L ∘ₗ E.toLinearMap = R ∘ₗ E.toLinearMap := by
    refine TensorProduct.ext' fun a z ↦ ?_
    let A₁ : W →ₗ[ℂ] ℂ := (L ∘ₗ E.toLinearMap) ∘ₗ TensorProduct.mk ℂ A W a
    let A₂ : W →ₗ[ℂ] ℂ := (R ∘ₗ E.toLinearMap) ∘ₗ TensorProduct.mk ℂ A W a
    change A₁ z = A₂ z
    refine PiTensorProduct.induction_on
      (motive := fun z : ⨂[ℂ] i, D i ↦ A₁ z = A₂ z) z ?_ ?_
    · intro r g
      have hg : A₁ (⨂ₜ[ℂ] i, g i) = A₂ (⨂ₜ[ℂ] i, g i) := h a g
      change A₁ (r • (show W from (⨂ₜ[ℂ] i, g i))) = A₂ (r • (show W from (⨂ₜ[ℂ] i, g i)))
      rw [map_smul, map_smul, hg]
    · intro z₁ z₂ h₁ h₂
      exact (map_add A₁ _ _).trans ((congrArg₂ (· + ·) h₁ h₂).trans (map_add A₂ _ _).symm)
  refine LinearMap.ext fun g ↦ ?_
  obtain ⟨z, rfl⟩ := E.surjective g
  exact LinearMap.congr_fun H z


private theorem sLocalPW_principalValue_singleton_test (hST : S ⊆ T) (v : T)
    (hv : v.val ∉ S) (h : ({v.val} : Finset V) ⊆ T)
    (p : v.val.adicCompletion F)
    (hp : (Valued.v : Valuation (v.val.adicCompletion F) (WithZero (Multiplicative ℤ))).IsUniformizer p)
    (f : B(S)) :
    let u := sLocalPW_singlePlaceUnit v (Units.mk0 p hp.ne_zero)
    sAdelePrincipalValue F h (Π(hST) f) =
      Π(hST) f - schwartzBruhatUnitTranslate u (Π(hST) f) := by
  intro u
  apply Subtype.ext
  funext x
  let eval (z : Multiplicative (SAdeleRing F T)) : B(T) →ₗ[ℂ] ℂ :=
    { toFun := fun g ↦ g z, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  let L := (eval x).comp ((sAdelePrincipalValue F h).comp (Π(hST)))
  let y := Multiplicative.ofAdd ((↑u⁻¹ : SAdeleRing F T) * x.toAdd)
  let M := (eval x).comp (Π(hST)) - (eval y).comp (Π(hST))
  change L f = M f
  refine LinearMap.congr_fun (sLocalPW_linear_eq_on_pure
    (sAdeleSchwartz_inductiveTensor_equiv F S).choose L M ?_) f
  exact fun a g ↦ sLocalPW_principalValue_singleton_tmul hST v hv h p hp a g x.toAdd

/-- At a new place, the principal value is the difference of the identity and a
uniformizer translate on inserted tests. That translate costs exactly one residue size. -/
private theorem sLocalInvariantPW_principalValue_singleton (hST : S ⊆ T) (v : T)
    (hv : v.val ∉ S) (h : ({v.val} : Finset V) ⊆ T)
    (χ : PontryaginDual J₁(T)) (Y : ℝ) (hY : 0 ≤ Y)
    (x : Θ(T, χ)) (hx : x ∈ invPW(hST, Y, χ)) :
    PV(h, χ) x ∈ invPW(hST, (v.val.asIdeal.absNorm : ℝ) * Y, χ) := by
  obtain ⟨p, hp⟩ := (Valued.v : Valuation (v.val.adicCompletion F)
    (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
  let u := sLocalPW_singlePlaceUnit v (Units.mk0 p.val hp.ne_zero)
  let c : J(T) := QuotientGroup.mk u
  let N : ℝ := v.val.asIdeal.absNorm
  have hN : 1 ≤ N := by
    change (1 : ℝ) ≤ (v.val.asIdeal.absNorm : ℝ)
    exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm v.val).le
  have hc : ((m(T) c).val : ℝ) = N⁻¹ := sLocalPW_singlePlaceUnit_norm v p hp
  have hNY : Y ≤ N * Y := le_mul_of_one_le_left hY hN
  have hNY' : Y ≤ ((m(T) c).val : ℝ) * (N * Y) := by
    rw [hc, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt (zero_lt_one.trans_le hN)), one_mul]
  refine Set.MapsTo.closure_left (t := (invPW(hST, N * Y, χ) : Set (Θ(T, χ)))) ?_
    (sLocalHomogeneousThetaPrincipalValue_isClosedEmbedding h χ).continuous
    (Submodule.isClosed_topologicalClosure _) hx
  rintro _ ⟨f, ⟨hf, hf₀⟩, rfl⟩
  obtain ⟨g, rfl, hg⟩ := (mem_sLocalPWTests hST _ f).mp hf
  have hsmall : q(T, χ) (Π(hST) g) ∈ invPW(hST, Y, χ) :=
    Submodule.le_topologicalClosure _
      (Submodule.mem_map_of_mem ⟨(mem_sLocalPWTests hST _ _).mpr ⟨g, rfl, hg⟩, hf₀⟩)
  have hlarge : q(T, χ) (Π(hST) g) ∈ invPW(hST, N * Y, χ) :=
    Submodule.le_topologicalClosure _
      (Submodule.mem_map_of_mem ⟨(mem_sLocalPWTests hST _ _).mpr
        ⟨g, rfl, hg.1, fun z hz ↦ (hg.2 hz).trans hNY⟩, hf₀⟩)
  have htranslate := sLocalInvariantPW_translate_bound
    hST Y (N * Y) (Z₀(T)) (Or.inr rfl) χ c hNY' _ hsmall
  have haction : A(T, χ) c (q(T, χ) (Π(hST) g)) =
      q(T, χ) (schwartzBruhatUnitTranslate u (Π(hST) g)) :=
    (existsUnique_sLocalHomogeneousThetaAction (F := F) (S := T) χ).exists.choose_spec.2 u _
  rw [haction] at htranslate
  change PV(h, χ) (Submodule.Quotient.mk (Π(hST) g)) ∈ _
  rw [sLocalHomogeneousThetaPrincipalValue_mk h χ,
    sLocalPW_principalValue_singleton_test hST v hv h p hp]
  change q(T, χ) (Π(hST) g - schwartzBruhatUnitTranslate u (Π(hST) g)) ∈ _
  rw [map_sub]
  exact Submodule.sub_mem _ hlarge htranslate

-- Disjoint finite principal values compose coordinatewise, as in the
-- strong-coprimality calculation in Sec5.
private theorem sLocalPW_principalValue_conj_comp {E G N : Type*} [AddCommGroup E]
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
private theorem sLocalPW_principalValue_piMap_comp {ι : Type*} [Fintype ι] {M : ι → Type*}
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
private theorem sLocalPW_principalValue_comp {S' S₁ S₂ S₃ : Finset V}
    (h₁ : S₁ ⊆ S') (h₂ : S₂ ⊆ S') (h₃ : S₃ ⊆ S')
    (h : ∀ w ∈ S', (w ∈ S₁ ↔ w ∈ S₂ ∨ w ∈ S₃) ∧ ¬ (w ∈ S₂ ∧ w ∈ S₃)) :
    sAdelePrincipalValue F h₁ = (sAdelePrincipalValue F h₂).comp (sAdelePrincipalValue F h₃) := by
  unfold sAdelePrincipalValue
  exact sLocalPW_principalValue_conj_comp _ _ _ _ (sLocalPW_principalValue_piMap_comp fun w ↦ h w.val w.2)

private theorem sLocalPW_principalValue_diagram_empty (h : (∅ : Finset V) ⊆ T) :
    sAdelePrincipalValue F h = LinearMap.id := by
  have conj {E G Y : Type _} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
      [AddCommGroup G] [Module ℂ G] [TopologicalSpace G]
      [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
      (e : InductiveTensor E G ≃L[ℂ] Y) (P : G →ₗ[ℂ] G) (hp : ∀ x, P x = x) :
      e.toLinearMap.comp ((TensorProduct.map (LinearMap.id : E →ₗ[ℂ] E) P).comp e.symm.toLinearMap)
        = LinearMap.id := by
    have he : P = LinearMap.id := LinearMap.ext hp
    subst he
    exact LinearMap.ext fun x ↦ (congrArg e (LinearMap.congr_fun
      (TensorProduct.map_id (R := ℂ) (M := E) (N := G)) (e.symm x))).trans (e.apply_symm_apply x)
  unfold sAdelePrincipalValue
  refine conj _ _ fun x ↦ ?_
  simp only [Finset.notMem_empty, ite_false, PiTensorProduct.map_id]
  rfl


private theorem sLocalInvariantPW_principalValue_finset (hST : S ⊆ T) (R : Finset V)
    (hRT : R ⊆ T) (hRS : Disjoint R S) (χ : PontryaginDual J₁(T)) (Y : ℝ) (hY : 0 ≤ Y)
    (x : Θ(T, χ)) (hx : x ∈ invPW(hST, Y, χ)) :
    PV(hRT, χ) x ∈ invPW(hST, size(R) * Y, χ) := by
  induction R using Finset.induction_on with
  | empty =>
    obtain ⟨f, rfl⟩ := Submodule.mkQ_surjective _ x
    change PV(hRT, χ) (Submodule.Quotient.mk f) ∈ _
    rw [sLocalHomogeneousThetaPrincipalValue_mk hRT χ, sLocalPW_principalValue_diagram_empty hRT]
    rw [LinearMap.id_apply, Finset.prod_empty, one_mul]
    change q(T, χ) f ∈ _
    exact hx
  | @insert v R hv ih =>
    have hR : R ⊆ T := (Finset.subset_insert v R).trans hRT
    have hvT : v ∈ T := hRT (Finset.mem_insert_self v R)
    have hd := Finset.disjoint_insert_left.mp hRS
    have hs : ({v} : Finset V) ⊆ T := Finset.singleton_subset_iff.mpr hvT
    have hcomp := sLocalPW_principalValue_comp (F := F) hRT hs hR (by
      intro w _
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact ⟨trivial, fun ⟨hw, hwR⟩ ↦ hv (hw ▸ hwR)⟩)
    have heq : PV(hRT, χ) x = PV(hs, χ) (PV(hR, χ) x) := by
      obtain ⟨f, rfl⟩ := Submodule.mkQ_surjective _ x
      change PV(hRT, χ) (Submodule.Quotient.mk f) = PV(hs, χ) (PV(hR, χ) (Submodule.Quotient.mk f))
      rw [sLocalHomogeneousThetaPrincipalValue_mk, sLocalHomogeneousThetaPrincipalValue_mk hR,
        sLocalHomogeneousThetaPrincipalValue_mk, hcomp, LinearMap.comp_apply]
    have hRy : 0 ≤ size(R) * Y :=
      mul_nonneg (Finset.prod_nonneg fun _ _ ↦ Nat.cast_nonneg _) hY
    have hmem := sLocalInvariantPW_principalValue_singleton
      hST ⟨v, hvT⟩ hd.1 hs χ (size(R) * Y) hRy _
      (ih hR hd.2)
    rw [heq, Finset.prod_insert hv, mul_assoc]
    exact hmem

/-- Paper: Proposition 7.3.3.2, p. 357–358.
The finite principal value maps the zero-moment invariant level at Y into the
invariant level at the product of the residue sizes times Y. -/
theorem sLocalInvariantPW_principalValue {S₀ : Finset (HeightOneSpectrum (𝓞 F))}
    (hST : S ⊆ T) (_hT : T = S ∪ S₀)
    (hRT : R ⊆ T) (_hR : R ⊆ S₀) (_hsatR : IsSaturatedPlaceSet (F := F) R)
    (_hdis : Disjoint S S₀) (_hsat : IsSaturatedPlaceSet (F := F) S₀) (_hPic : PicTrivial)
    (ω : PontryaginDual C₁) (hu : NormOneCharacterUnramifiedOutside ω S)
    (χ : PontryaginDual J₁(T)) (_hχ : χ = descend(hST, ω, hu))
    (Y : ℝ) (_hY : 0 < Y) :
    (invPW(hST, Y, χ)).map (PV(hRT, χ)) ≤ invPW(hST, size(R) * Y, χ) := by
  have hRS : Disjoint R S := _hdis.symm.mono_left _hR
  rintro _ ⟨x, hx, rfl⟩
  exact sLocalInvariantPW_principalValue_finset hST R hRT hRS χ Y _hY.le x hx

/-- Modulo an arbitrary subspace, the kernel of the two moments is still closed:
its preimage is the inverse image of a subspace of the moment plane. -/
private theorem sLocalPW_principalValue_diagram_closed {E : Type*} [AddCommGroup E]
    [Module ℂ E] [TopologicalSpace E] (K : Submodule ℂ E) (m : E →ₗ[ℂ] ℂ × ℂ)
    (hm : Continuous m) : IsClosed (m.ker.map K.mkQ : Set (E ⧸ K)) := by
  apply K.isQuotientMap_mkQ.isCoinducing.isClosed_preimage.mp
  change IsClosed (((m.ker.map K.mkQ).comap K.mkQ : Submodule ℂ E) : Set E)
  rw [Submodule.comap_map_mkQ, ← Submodule.comap_map_eq m K]
  exact (K.map m).isClosed_of_finiteDimensional.preimage hm

private theorem sLocalPW_principalValue_diagram_polar (χ : PontryaginDual J₁(T)) :
    IsClosed ((Z₀(T)).map (q(T, χ)) : Set (Θ(T, χ))) := by
  unfold sAdelePolarSubspace
  apply sLocalPW_principalValue_diagram_closed
  obtain ⟨L, hL⟩ := sLocal_fourier_continuousLinear (F := F) (S := T)
  have he := schwartzBruhat_eval_continuous (Multiplicative.ofAdd (0 : SAdeleRing F T))
  exact he.prodMk ((he.comp L.continuous).congr fun f ↦ congrArg (fun g : B(T) ↦
    g (Multiplicative.ofAdd 0)) (hL f))

private theorem sLocalPW_principalValue_diagram_test (h : R ⊆ T) (χ : PontryaginDual J₁(T))
    (u : (SAdeleRing F T)ˣ) (f : B(T)) :
    q(T, χ) (sAdelePrincipalValue F h (schwartzBruhatUnitTranslate u f)) =
      q(T, χ) (schwartzBruhatUnitTranslate u (sAdelePrincipalValue F h f)) := by
  rcases R.eq_empty_or_nonempty with rfl | hn
  · rw [sLocalPW_principalValue_diagram_empty h]
    rfl
  · apply (sLocalHomogeneousThetaSpace_mk_eq_iff χ _ _).2
    have he := (sLocalAdelicThetaSpace_mk_eq_iff (F := F) (S := T) _ _).1
      (sLocalThetaPrincipalValue_equivariant (F := F) h hn u f)
    exact ContinuousMap.ext fun y ↦ by simp only [sLocalHomogeneousAdelicThetaLinearMap_apply, he]

private theorem sLocalPW_principalValue_diagram_comm (h : R ⊆ T) (χ : PontryaginDual J₁(T))
    (g : J(T)) (x : Θ(T, χ)) : PV(h, χ) (A(T, χ) g x) = A(T, χ) g (PV(h, χ) x) := by
  let ρ := A(T, χ)
  let U := PV(h, χ)
  let Q := q(T, χ)
  change U (ρ g x) = ρ g (U x)
  have hx : Surjective (Q : B(T) → Θ(T, χ)) := Submodule.mkQ_surjective _
  obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective g
  obtain ⟨f, hf⟩ := hx x
  rw [← hu, ← hf]
  have ha := (existsUnique_sLocalHomogeneousThetaAction (F := F) (S := T) χ).exists.choose_spec.2 u
  exact ((congrArg U (ha f)).trans (sLocalPW_principalValue_diagram_test h χ u f)).trans
    (ha (sAdelePrincipalValue F h f)).symm

/-- Paper: Proposition 7.3.3.2, p. 358.
There are inclusions along both rows of the PW diagram. The restrictions of the
ambient principal value are continuous and commute with the translations.
Deviation: The lower row needs its own level comparison. The commutative squares
can be read by composing the restrictions with the inclusions into the ambient space. -/
theorem sLocalPW_principalValue_diagram {S₀ : Finset (HeightOneSpectrum (𝓞 F))}
    (hST : S ⊆ T) (_hT : T = S ∪ S₀)
    (hRT : R ⊆ T) (_hR : R ⊆ S₀) (_hsatR : IsSaturatedPlaceSet (F := F) R)
    (_hdis : Disjoint S S₀) (_hsat : IsSaturatedPlaceSet (F := F) S₀) (_hPic : PicTrivial)
    (ω : PontryaginDual C₁) (hu : NormOneCharacterUnramifiedOutside ω S)
    (χ : PontryaginDual J₁(T)) (_hχ : χ = descend(hST, ω, hu))
    (X Y : ℝ) (_hX : 0 < X) (_hY : 0 < Y) (_hXY : X ^ count(S) ≤ Y)
    (_hXY' : (size(R) * X) ^ count(S) ≤ size(R) * Y) :
    let a := absPW(hST, X, χ)
    let a' := absPW(hST, size(R) * X, χ)
    let b := invPW(hST, Y, χ)
    let b' := invPW(hST, size(R) * Y, χ)
    a ≤ b ∧ a' ≤ b' ∧ b ≤ (Z₀(T)).map (q(T, χ)) ∧ b' ≤ (Z₀(T)).map (q(T, χ)) ∧
      ∃ (P : a →L[ℂ] a') (P' : b →L[ℂ] b'),
        (∀ x : a, (P x).val = PV(hRT, χ) x.val) ∧
        (∀ x : b, (P' x).val = PV(hRT, χ) x.val) ∧
        ∀ (g : J(T)), 1 ≤ ((m(T) g).val : ℝ) →
          ∀ x : (Z₀(T)).map (q(T, χ)),
            PV(hRT, χ) (A(T, χ) g x.val) = A(T, χ) g (PV(hRT, χ) x.val) := by
  have hsize : 0 < size(R) := Finset.prod_pos fun v _ ↦
    Nat.cast_pos.mpr (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v))
  have row (l r : ℝ) (hl : 0 < l) (hlr : l ^ count(S) ≤ r) : absPW(hST, l, χ) ≤ invPW(hST, r, χ) :=
    (sLocalAbsolutePW_le_invariant hST l hl _ χ).trans (sLocalInvariantPW_mono hST hlr _ χ)
  have polar (r : ℝ) : invPW(hST, r, χ) ≤ (Z₀(T)).map (q(T, χ)) :=
    Submodule.topologicalClosure_minimal _ (Submodule.map_mono inf_le_right)
      (sLocalPW_principalValue_diagram_polar χ)
  let p : Θ(T, χ) →L[ℂ] Θ(T, χ) := ⟨PV(hRT, χ),
    (sLocalHomogeneousThetaPrincipalValue_isClosedEmbedding hRT χ).continuous⟩
  have hA := sLocalAbsolutePW_principalValue hST _hT hRT _hR _hsatR _hdis _hsat _hPic ω hu χ _hχ X _hX
  have hB := sLocalInvariantPW_principalValue hST _hT hRT _hR _hsatR _hdis _hsat _hPic ω hu χ _hχ Y _hY
  exact ⟨row _ _ _hX _hXY, row _ _ (mul_pos hsize _hX) _hXY', polar _, polar _,
    (p.comp (absPW(hST, X, χ)).subtypeL).codRestrict _ (fun x ↦ hA ⟨x, x.property, rfl⟩),
    (p.comp (invPW(hST, Y, χ)).subtypeL).codRestrict _ (fun x ↦ hB ⟨x, x.property, rfl⟩),
    fun _ ↦ rfl, fun _ ↦ rfl, fun g _ x ↦ sLocalPW_principalValue_diagram_comm hRT χ g x.val⟩

end PrincipalValues

section PWOrbitalQuotients

open Classical

local notation "Vℚ" => HeightOneSpectrum (𝓞 ℚ)
local notation "Rₚ(" p ", " ω ")" => sLocalPrimaryOrbitalSubmodule (F := F) (S := T) p ω
local notation "Qₚ(" p ", " ω ")" => SLocalPrimaryOrbitalQuotient (F := F) (S := T) p ω
local notation "Iₚ(" p ", " ω ")" => SLocalOrbitalIndex (F := F) (S := T)
  (sLocalPrimaryPlaces (F := F) T p) ω

local notation "PVₚ(" p ", " ω ")" =>
  PV((sLocalPrimaryPlaces_subset (F := F) T p), ω)
local notation "Rₚ₀(" p ", " ω ")" =>
  (((Z₀(T)).map (q(T, ω))).map (PVₚ(p, ω)))

/-- Paper: Definition 7.3.3.3(1)–(2), p. 359, and (7.3.3.18)–(7.3.3.19), p. 361.
The denominator inside the level consists of principal values with a zero-moment preimage.
Deviation: Uses the intersection from the proof on p. 361. The displayed quotients on
p. 359 require a containment that fails even for one added rational prime.

This is a `def` with its own instances, not an `abbrev`, so that instance terms over it do
not spell out its definition (#5398). -/
def SLocalPWOrbitalQuotient (ω : PontryaginDual J₁(T)) (p : Vℚ)
    (W : Submodule ℂ (Θ(T, ω))) :=
  W ⧸ (Rₚ₀(p, ω)).comap W.subtype

namespace SLocalPWOrbitalQuotient

instance instAddCommGroup (ω : PontryaginDual J₁(T)) (p : Vℚ)
    (W : Submodule ℂ (Θ(T, ω))) :
    AddCommGroup (SLocalPWOrbitalQuotient ω p W) :=
  inferInstanceAs (AddCommGroup (W ⧸ (Rₚ₀(p, ω)).comap W.subtype))

instance instModule (ω : PontryaginDual J₁(T)) (p : Vℚ)
    (W : Submodule ℂ (Θ(T, ω))) :
    Module ℂ (SLocalPWOrbitalQuotient ω p W) :=
  inferInstanceAs (Module ℂ (W ⧸ (Rₚ₀(p, ω)).comap W.subtype))

instance instTopologicalSpace (ω : PontryaginDual J₁(T)) (p : Vℚ)
    (W : Submodule ℂ (Θ(T, ω))) :
    TopologicalSpace (SLocalPWOrbitalQuotient ω p W) :=
  inferInstanceAs (TopologicalSpace (W ⧸ (Rₚ₀(p, ω)).comap W.subtype))

instance instIsTopologicalAddGroup (ω : PontryaginDual J₁(T)) (p : Vℚ)
    (W : Submodule ℂ (Θ(T, ω))) :
    IsTopologicalAddGroup (SLocalPWOrbitalQuotient ω p W) :=
  inferInstanceAs (IsTopologicalAddGroup (W ⧸ (Rₚ₀(p, ω)).comap W.subtype))

instance instContinuousSMul (ω : PontryaginDual J₁(T)) (p : Vℚ)
    (W : Submodule ℂ (Θ(T, ω))) :
    ContinuousSMul ℂ (SLocalPWOrbitalQuotient ω p W) :=
  inferInstanceAs (ContinuousSMul ℂ (W ⧸ (Rₚ₀(p, ω)).comap W.subtype))

end SLocalPWOrbitalQuotient

/-- Paper: Equations (7.3.3.18)–(7.3.3.19), p. 361.
A class vanishes precisely when its vector is the principal value of a zero-moment class. -/
theorem sLocalPWOrbitalQuotient_mk_eq_zero (ω : PontryaginDual J₁(T)) (p : Vℚ)
    (W : Submodule ℂ (Θ(T, ω))) (x : W) :
    ((Rₚ₀(p, ω)).comap W.subtype).mkQ x = (0 : SLocalPWOrbitalQuotient ω p W) ↔
      ∃ y ∈ (Z₀(T)).map (q(T, ω)), PVₚ(p, ω) y = x.val := by
  exact Submodule.Quotient.mk_eq_zero _

local notation "absPW(" h ", " b ", " ω ")" => sLocalAbsolutePW h b (Z₀(_)) ω
local notation "invPW(" h ", " b ", " ω ")" => sLocalInvariantPW h b (Z₀(_)) ω

-- TODO(paper-gap): At c = 1 both the order-zero Fourier jet and the top Laurent
-- coefficient vanish on zero-moment classes. Theorem 7.3.3.4 does not supply a
-- biorthogonal system for the shifted coefficient range of Corollary 7.2.2.2.
-- A restricted quotient can also contain a nonzero class in the kernel of its
-- map to the unrestricted ambient quotient at this character.

-- TODO(paper-gap): The argument on p. 363 needs a single Fourier support bound for
-- lifts of the full compact-window quotient. Pointwise existence of test representatives
-- in Proposition 5.3.4.4 does not supply that bound.
-- The basis and growth statements in §7.3.1 assume saturation of the whole target T.
-- To use them for an unsaturated base S, their proofs must be localized to the fiber over p.

/-- When the Picard group of the `S`-integers is trivial, every idele becomes a unit at
all finite places outside `S` after division by a single principal idele. -/
private theorem sLocalPWOrbital_eventually_equiv_inf_unitOutside
    {F : Type*} [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hPic : Subsingleton (CommRing.Pic ((S : Set (HeightOneSpectrum (𝓞 F))).integer F)))
    (g : IdeleGroup (𝓞 F) F) :
    ∃ x : Fˣ, ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S →
      Valued.v ((g * IdeleGroup.unitEmbedding (𝓞 F) F x⁻¹).val.2 v) =
        (1 : WithZero (Multiplicative ℤ)) := by
  classical
  have hg : {v : HeightOneSpectrum (𝓞 F) |
      Valued.v (g.val.2 v) ≠ (1 : WithZero (Multiplicative ℤ))}.Finite :=
    eventually_cofinite.mp (AdeleRing.isUnit_iff.mp g.isUnit).2.2
  obtain ⟨T, hT, hPicT⟩ := (picard_uniformization F (S ∪ hg.toFinset)).1
  have hST : S ⊆ T := Finset.subset_union_left.trans hT
  let D := T \ S
  let I (v : HeightOneSpectrum (𝓞 F)) : IdeleGroup (𝓞 F) F →* (v.adicCompletion F)ˣ :=
    Units.map (((RestrictedProduct.evalRingHom
      (fun w : HeightOneSpectrum (𝓞 F) ↦ w.adicCompletion F) v).comp
      (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))).toMonoidHom)
  let u : (v : D) → (v.val.adicCompletion F)ˣ ⧸ (v.val.adicCompletionIntegers F).units :=
    fun v ↦ QuotientGroup.mk (I v.val g)
  obtain ⟨e, -⟩ := (picard_uniformization F S).2.1 T hST hPicT
  have he : (QuotientGroup.mk u : _ ⧸ (sUnitLocalClasses F T D).range) = 1 :=
    e.injective (hPic.elim _ _)
  obtain ⟨x, hx⟩ := (QuotientGroup.eq_one_iff (N := (sUnitLocalClasses F T D).range) u).mp he
  refine ⟨x.val, fun v hv ↦ ?_⟩
  have hmul : I v (g * IdeleGroup.unitEmbedding (𝓞 F) F x.val⁻¹) =
      I v g * (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom x.val)⁻¹ := by
    rw [map_mul, ← map_inv]
    rfl
  change Valued.v (I v (g * IdeleGroup.unitEmbedding (𝓞 F) F x.val⁻¹)).val = 1
  rw [hmul]
  by_cases hvT : v ∈ T
  · -- inside the enlarged set the local classes of `g` and of the unit `x` agree
    let w : D := ⟨v, Finset.mem_sdiff.mpr ⟨hvT, hv⟩⟩
    have h := congrFun hx w
    change (QuotientGroup.mk (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom x.val) :
        (v.adicCompletion F)ˣ ⧸ (v.adicCompletionIntegers F).units) =
      QuotientGroup.mk (I v g) at h
    have hmem : I v g * (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom x.val)⁻¹ ∈
        (v.adicCompletionIntegers F).units := by
      apply (QuotientGroup.eq_one_iff _).mp
      change (QuotientGroup.mk' (v.adicCompletionIntegers F).units)
        (I v g * (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom x.val)⁻¹) = 1
      rw [map_mul, map_inv]
      exact mul_inv_eq_one.mpr h.symm
    exact HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp hmem
  · -- outside it both `g` and the unit `x` already have valuation one
    have hg' : Valued.v (g.val.2 v) = (1 : WithZero (Multiplicative ℤ)) := by
      by_contra h
      exact hvT (hT (Finset.mem_union_right _ (hg.mem_toFinset.mpr h)))
    have hx' : Valued.v ((x.val : F) : v.adicCompletion F) =
        (1 : WithZero (Multiplicative ℤ)) := by
      rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      exact x.property v hvT
    rw [Units.val_mul, Units.val_inv_eq_inv_val]
    change Valued.v (g.val.2 v * (((x.val : F) : v.adicCompletion F)⁻¹)) = 1
    rw [map_mul, map_inv₀, hg', hx', inv_one, one_mul]

/-- A character of the norm-one idele classes that is unramified outside `S` is trivial as
soon as its descent to a larger stage `T` is trivial, provided the Picard group of the
`S`-integers is trivial. -/
private theorem sLocalPWOrbital_eventually_equiv_inf_character
    {F : Type*} [Field F] [NumberField F] {S T : Finset (HeightOneSpectrum (𝓞 F))}
    (hST : S ⊆ T)
    (hPic : Subsingleton (CommRing.Pic ((S : Set (HeightOneSpectrum (𝓞 F))).integer F)))
    (ω : PontryaginDual (ideleClassNorm F).ker) (hu : NormOneCharacterUnramifiedOutside ω S)
    (h : sLocalNormOneCharacter (F := F) T ω
      (NormOneCharacterUnramifiedOutside.mono (F := F) hu hST) = 1) : ω = 1 := by
  apply PontryaginDual.ext
  intro x
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective x.val
  obtain ⟨a, ha⟩ := sLocalPWOrbital_eventually_equiv_inf_unitOutside S hPic g
  let d := IdeleGroup.unitEmbedding (𝓞 F) F
  let t := g * d a⁻¹
  -- `t` represents the same idele class as `g` and is a unit at every place outside `S`
  have ht : (QuotientGroup.mk t : IdeleClassGroup (𝓞 F) F) = x.val := by
    have hd : (QuotientGroup.mk (d a⁻¹) : IdeleClassGroup (𝓞 F) F) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨a⁻¹, rfl⟩
    change (QuotientGroup.mk' _) (g * d a⁻¹) = x.val
    rw [map_mul]
    change (QuotientGroup.mk g : IdeleClassGroup (𝓞 F) F) * QuotientGroup.mk (d a⁻¹) = x.val
    rw [hd, mul_one, hg]
  have htu : t ∈ range (integralIdeleInsertion F T) := by
    apply (mem_range_integralIdeleInsertion F T t).mpr
    intro v hv
    have hvS : v ∉ S := fun hvS ↦ hv (hST hvS)
    have h1 : t.val.2 v * t.inv.2 v = 1 :=
      congrArg (fun z : AdeleRing (𝓞 F) F ↦ z.2 v) t.val_inv
    have hval : Valued.v (t.inv.2 v) = 1 := by
      have hvp := congrArg Valued.v h1
      rw [map_mul, ha v hvS, one_mul, map_one] at hvp
      exact hvp
    exact ⟨(ha v hvS).le, hval.le⟩
  obtain ⟨u, hu'⟩ := htu
  let y₀ := Units.map (adeleProjection F T).toMonoidHom t
  have hy : sIdeleQuotientNorm F T (QuotientGroup.mk y₀) = 1 := by
    rw [sIdeleQuotientNorm_mk]
    have hh := (sIdeleNorm_spec F T).1 u
    change ideleNorm F (integralIdeleInsertion F T u) =
      sIdeleNorm F T (Units.map (adeleProjection F T).toMonoidHom
        (integralIdeleInsertion F T u)) at hh
    rw [hu'] at hh
    change ideleClassNorm F (QuotientGroup.mk t) = sIdeleNorm F T y₀ at hh
    rw [ht, MonoidHom.mem_ker.mp x.property] at hh
    exact hh.symm
  let y : (sIdeleQuotientNorm F T).ker := ⟨QuotientGroup.mk y₀, hy⟩
  have hh := sLocalNormOneCharacter_apply ω (hu.mono hST) u x y (by rw [hu', ht])
    (by rw [hu'])
  rw [h] at hh
  exact hh.symm

/-- Paper: Theorem 7.3.3.4, equations (7.3.3.18)–(7.3.3.19), p. 361.
The first of the two level conditions of the theorem: for large enough absolute or
invariant Paley–Wiener levels, the level meets the primary principal-value image exactly
in the principal-value image of the zero-moment classes. This is the statement that the
denominators displayed in (7.3.3.18)–(7.3.3.19) agree inside the level.
It is one of the two inputs of `sLocalPWOrbital_eventually_equiv_quotient`. -/
private theorem sLocalPWOrbital_eventually_equiv_inf {S₀ : Finset V} (hST : S ⊆ T)
    (_hT : T = S ∪ S₀) (_hdis : Disjoint S S₀) (_hsat : IsSaturatedPlaceSet (F := F) S₀)
    (_hPic : PicTrivial) (p : Vℚ) (_hp : (sLocalPrimaryPlaces (F := F) T p).Nonempty)
    (_hp₀ : sLocalPrimaryPlaces (F := F) T p ⊆ S₀)
    (ω : PontryaginDual C₁) (hu : NormOneCharacterUnramifiedOutside ω S)
    (χ : PontryaginDual J₁(T)) (_hχ : χ = descend(hST, ω, hu)) (_hω : ω ≠ 1) :
    ∃ B : ℝ, 0 < B ∧ ∀ X Y : ℝ, B ≤ X → B ≤ Y → X ^ count(S) ≤ Y →
      ∀ (W : Submodule ℂ (Θ(T, χ))), (W = absPW(hST, X, χ) ∨ W = invPW(hST, Y, χ)) →
        W ⊓ Rₚ(p, χ) = W ⊓ Rₚ₀(p, χ) := by
  -- the descended character is nontrivial, because the Picard group is trivial
  have hχ1 : χ ≠ 1 := fun h ↦ _hω
    (sLocalPWOrbital_eventually_equiv_inf_character hST _hPic ω hu (_hχ.symm.trans h))
  -- hence every theta class has a zero-moment representative, and the two images coincide
  have hR : Rₚ₀(p, χ) = Rₚ(p, χ) := by
    rw [sLocalZeroMomentTheta_eq_top (F := F) (T := T) χ hχ1, Submodule.map_top]
    rfl
  exact ⟨1, one_pos, fun X Y _ _ _ W _ ↦ by rw [hR]⟩

/-- Paper: Theorem 7.3.3.4, arrow (4) of diagram (7.3.3.15), pp. 361–362.
The second of the two level conditions of the theorem: for large enough absolute or
invariant Paley–Wiener levels, the level and the primary principal-value image together
fill the homogeneous theta space, so that every class of the primary orbital quotient has
a representative in the level.
It is one of the two inputs of `sLocalPWOrbital_eventually_equiv_quotient`. -/
private theorem sLocalPWOrbital_eventually_equiv_sup {S₀ : Finset V} (hST : S ⊆ T)
    (_hT : T = S ∪ S₀) (_hdis : Disjoint S S₀) (_hsat : IsSaturatedPlaceSet (F := F) S₀)
    (_hPic : PicTrivial) (p : Vℚ) (_hp : (sLocalPrimaryPlaces (F := F) T p).Nonempty)
    (_hp₀ : sLocalPrimaryPlaces (F := F) T p ⊆ S₀)
    (ω : PontryaginDual C₁) (hu : NormOneCharacterUnramifiedOutside ω S)
    (χ : PontryaginDual J₁(T)) (_hχ : χ = descend(hST, ω, hu)) (_hω : ω ≠ 1) :
    ∃ B : ℝ, 0 < B ∧ ∀ X Y : ℝ, B ≤ X → B ≤ Y → X ^ count(S) ≤ Y →
      ∀ (W : Submodule ℂ (Θ(T, χ))), (W = absPW(hST, X, χ) ∨ W = invPW(hST, Y, χ)) →
        W ⊔ Rₚ(p, χ) = ⊤ := by sorry

/-- Paper: Theorem 7.3.3.4, p. 360, and diagram (7.3.3.15), p. 361.
The quotient transfer: if a closed level `W` meets the primary principal-value image in
the principal-value image of the zero-moment classes and, together with that image, fills
the theta space, then the map induced by `W ⊆ Θ(T, χ)` on the quotients is a topological
linear isomorphism onto the primary orbital quotient.
This is the linear-algebra and topology part of the theorem; it carries no arithmetic. -/
private theorem sLocalPWOrbital_eventually_equiv_quotient (p : Vℚ)
    (χ : PontryaginDual J₁(T)) (W : Submodule ℂ (Θ(T, χ)))
    (hW : IsClosed (W : Set (Θ(T, χ))))
    (hinf : W ⊓ Rₚ(p, χ) = W ⊓ Rₚ₀(p, χ)) (hsup : W ⊔ Rₚ(p, χ) = ⊤) :
    ∃ e : SLocalPWOrbitalQuotient χ p W ≃L[ℂ] Qₚ(p, χ),
      ∀ x : W, e (((Rₚ₀(p, χ)).comap W.subtype).mkQ x) = (Rₚ(p, χ)).mkQ x.val := by
  classical
  -- the inclusion of the level, followed by the quotient map
  let A : W →L[ℂ] Qₚ(p, χ) := (Rₚ(p, χ)).mkQL.comp W.subtypeL
  have hA (x : W) : A x = (Rₚ(p, χ)).mkQ x.val := rfl
  -- inside the level the two principal-value images agree
  have hmem (x : W) : (x : Θ(T, χ)) ∈ Rₚ(p, χ) ↔ (x : Θ(T, χ)) ∈ Rₚ₀(p, χ) := by
    have h := SetLike.ext_iff.mp hinf (x : Θ(T, χ))
    simp only [Submodule.mem_inf, x.property, true_and] at h
    exact h
  -- the kernel of `A` is the zero-moment part of the level
  have hker : A.ker = (Rₚ₀(p, χ)).comap W.subtype := by
    ext x
    show A x = 0 ↔ (W.subtype x : Θ(T, χ)) ∈ Rₚ₀(p, χ)
    have h1 : A x = 0 ↔ (W.subtype x : Θ(T, χ)) ∈ Rₚ(p, χ) := by
      rw [hA]
      exact Submodule.Quotient.mk_eq_zero _
    exact h1.trans (hmem x)
  -- and `A` is surjective because the level and the principal-value image fill the space
  have hsurj : Function.Surjective A := by
    intro y
    obtain ⟨z, rfl⟩ := (Rₚ(p, χ)).mkQ_surjective y
    have hz : z ∈ W ⊔ Rₚ(p, χ) := by rw [hsup]; exact Submodule.mem_top
    obtain ⟨w, hw, r, hr, hwr⟩ := Submodule.mem_sup.mp hz
    refine ⟨⟨w, hw⟩, ?_⟩
    show (Rₚ(p, χ)).mkQ w = (Rₚ(p, χ)).mkQ z
    rw [← hwr, map_add,
      show (Rₚ(p, χ)).mkQ r = 0 from (Submodule.Quotient.mk_eq_zero _).mpr hr, add_zero]
  -- the open mapping theorem for Fréchet spaces, which is what makes the inverse continuous
  have hopen : IsOpenMap A := by
    have hR : IsClosed (Rₚ(p, χ) : Set (Θ(T, χ))) :=
      (sLocalHomogeneousThetaPrincipalValue_isClosedEmbedding (F := F) (S := T)
        (sLocalPrimaryPlaces_subset (F := F) T p) χ).isClosed_range
    have hFΘ : IsFrechetTVS (Θ(T, χ)) :=
      sLocalHomogeneousThetaSpace_frechet (F := F) (S := T) χ
    have hFW : IsFrechetTVS W :=
      frechet_of_closed_embedding W.subtypeL (W.isClosedEmbedding_subtypeL hW) hFΘ
    have hFQ : IsFrechetTVS (Qₚ(p, χ)) := isFrechetTVS_quotient hFΘ (Rₚ(p, χ)) hR
    obtain ⟨hTΘ, hPΘ, hMΘ, hCΘ⟩ := hFΘ
    obtain ⟨hTW, hP0W, hMW, hCW⟩ := hFW
    obtain ⟨hTQ, hPQ, hMQ, hCQ⟩ := hFQ
    let : UniformSpace (Θ(T, χ)) := IsTopologicalAddGroup.rightUniformSpace (Θ(T, χ))
    let : UniformSpace (Qₚ(p, χ)) := IsTopologicalAddGroup.rightUniformSpace (Qₚ(p, χ))
    have : IsUniformAddGroup (Θ(T, χ)) := isUniformAddGroup_of_addCommGroup
    have : IsUniformAddGroup W := W.toAddSubgroup.isUniformAddGroup
    have : IsUniformAddGroup (Qₚ(p, χ)) := isUniformAddGroup_of_addCommGroup
    have : TopologicalSpace.MetrizableSpace (Θ(T, χ)) := hMΘ
    have : TopologicalSpace.MetrizableSpace W := hMW
    have : TopologicalSpace.MetrizableSpace (Qₚ(p, χ)) := hMQ
    have : CompleteSpace (Θ(T, χ)) := hCΘ
    have : CompleteSpace W := completeSpace_coe_iff_isComplete.mpr hW.isComplete
    have : CompleteSpace (Qₚ(p, χ)) := hCQ
    let : ContinuousSMul ℂ W := PolynormableSpace.continuousSMul ℂ W
    have : (uniformity (Θ(T, χ))).IsCountablyGenerated := by
      rw [uniformity_eq_comap_nhds_zero (Θ(T, χ))]
      infer_instance
    have : (uniformity (Qₚ(p, χ))).IsCountablyGenerated := by
      rw [uniformity_eq_comap_nhds_zero (Qₚ(p, χ))]
      infer_instance
    have : BaireSpace (Qₚ(p, χ)) := by
      let := UniformSpace.metricSpace (Qₚ(p, χ))
      infer_instance
    refine isOpenMap_of_not_isMeagre_range A ?_
    rw [hsurj.range_eq]
    exact not_isMeagre_of_isOpen isOpen_univ univ_nonempty
  exact exists_quotient_equiv_of_kernel A (hopen.isQuotientMap A.continuous hsurj) _ hker

/-- Paper: Theorem 7.3.3.4 and its proof, pp. 360–363.
For sufficiently large levels the inclusion induces the isomorphism used to transfer
the two bases and the Fourier seminorm bounds.
Deviation: Uses zero-moment principal-value preimages and a nontrivial component. -/
theorem sLocalPWOrbital_eventually_equiv {S₀ : Finset V} (hST : S ⊆ T) (_hT : T = S ∪ S₀)
    (_hdis : Disjoint S S₀) (_hsat : IsSaturatedPlaceSet (F := F) S₀) (_hPic : PicTrivial)
    (p : Vℚ) (_hp : (sLocalPrimaryPlaces (F := F) T p).Nonempty)
    (_hp₀ : sLocalPrimaryPlaces (F := F) T p ⊆ S₀)
    (ω : PontryaginDual C₁) (hu : NormOneCharacterUnramifiedOutside ω S)
    (χ : PontryaginDual J₁(T)) (_hχ : χ = descend(hST, ω, hu)) (_hω : ω ≠ 1) :
    ∃ B : ℝ, 0 < B ∧ ∀ X Y : ℝ, B ≤ X → B ≤ Y → X ^ count(S) ≤ Y →
      ∀ (W : Submodule ℂ (Θ(T, χ))), (W = absPW(hST, X, χ) ∨ W = invPW(hST, Y, χ)) →
        ∃ e : SLocalPWOrbitalQuotient χ p W ≃L[ℂ] Qₚ(p, χ),
          ∀ x : W, e (((Rₚ₀(p, χ)).comap W.subtype).mkQ x) = (Rₚ(p, χ)).mkQ x.val := by
  obtain ⟨B₁, hB₁, hlev₁⟩ := sLocalPWOrbital_eventually_equiv_inf (S := S) (T := T)
    (S₀ := S₀) hST _hT _hdis _hsat _hPic p _hp _hp₀ ω hu χ _hχ _hω
  obtain ⟨B₂, hB₂, hlev₂⟩ := sLocalPWOrbital_eventually_equiv_sup (S := S) (T := T)
    (S₀ := S₀) hST _hT _hdis _hsat _hPic p _hp _hp₀ ω hu χ _hχ _hω
  refine ⟨max B₁ B₂, lt_max_of_lt_left hB₁, ?_⟩
  intro X Y hX hY hXY W hW
  have hclosed : IsClosed (W : Set (Θ(T, χ))) := by
    rcases hW with rfl | rfl
    · change IsClosed ((Submodule.topologicalClosure _ : Submodule ℂ (Θ(T, χ))) : Set (Θ(T, χ)))
      exact Submodule.isClosed_topologicalClosure _
    · change IsClosed ((Submodule.topologicalClosure _ : Submodule ℂ (Θ(T, χ))) : Set (Θ(T, χ)))
      exact Submodule.isClosed_topologicalClosure _
  exact sLocalPWOrbital_eventually_equiv_quotient (T := T) p χ W hclosed
    (hlev₁ X Y ((le_max_left B₁ B₂).trans hX) ((le_max_left B₁ B₂).trans hY) hXY W hW)
    (hlev₂ X Y ((le_max_right B₁ B₂).trans hX) ((le_max_right B₁ B₂).trans hY) hXY W hW)

/-- Paper: Theorem 7.3.3.4(1)–(2), pp. 360–361.
For sufficiently large absolute or invariant levels, with the same enumeration
as the ambient system, the restricted functionals are an unconditional dual basis
and their biorthogonal lifts are an absolute quotient basis.
Deviation: Uses the intersections from (7.3.3.18)–(7.3.3.19) and a nontrivial
norm-one character. At the trivial character an ambient Fourier functional
restricts to zero. The pole orders use the S′-local Mellin transform and order k selects
Laurent exponent −k in the signed convention of Definition 7.1.2.1. -/
theorem sLocalPWOrbital_bases {S₀ : Finset V} (hST : S ⊆ T) (_hT : T = S ∪ S₀)
    (_hdis : Disjoint S S₀) (_hsat : IsSaturatedPlaceSet (F := F) S₀) (_hPic : PicTrivial)
    (p : Vℚ) (_hp : (sLocalPrimaryPlaces (F := F) T p).Nonempty)
    (_hp₀ : sLocalPrimaryPlaces (F := F) T p ⊆ S₀)
    (ω : PontryaginDual C₁) (hu : NormOneCharacterUnramifiedOutside ω S)
    (χ : PontryaginDual J₁(T)) (_hχ : χ = descend(hST, ω, hu)) (_hω : ω ≠ 1) :
    ∃ B : ℝ, 0 < B ∧ ∀ X Y : ℝ, B ≤ X → B ≤ Y → X ^ count(S) ≤ Y →
      ∀ (W : Submodule ℂ (Θ(T, χ))), (W = absPW(hST, X, χ) ∨ W = invPW(hST, Y, χ)) →
      ∀ (L : Iₚ(p, χ) → StrongDual ℂ (Θ(T, χ))),
        (L = sLocalOrbitalPrincipalPart (F := F) (S := T) ∨
          L = sLocalOrbitalFourierJet (F := F) (S := T)) →
        ∀ (σ : ℕ ≃ Iₚ(p, χ)),
          ∃ (d : ℕ → StrongDual ℂ (Qₚ(p, χ))) (e : ℕ → Qₚ(p, χ))
            (dW : ℕ → StrongDual ℂ (SLocalPWOrbitalQuotient χ p W))
            (eW : ℕ → SLocalPWOrbitalQuotient χ p W)
            (ev : ℕ → StrongDual ℂ (StrongDual ℂ (SLocalPWOrbitalQuotient χ p W))),
            (∀ n x, d n ((Rₚ(p, χ)).mkQ x) = L (σ n) x) ∧ IsSchauderBasis e d ∧
            (∀ n (x : W), dW n (((Rₚ₀(p, χ)).comap W.subtype).mkQ x) = L (σ n) x.val) ∧
            (∀ n, ∃ x : W, ((Rₚ₀(p, χ)).comap W.subtype).mkQ x = eW n ∧
              (Rₚ(p, χ)).mkQ x.val = e n) ∧
            (∀ n ℓ, ev n ℓ = ℓ (eW n)) ∧
            IsSchauderBasis dW ev ∧ SchauderBasis.IsUnconditional dW ev ∧
            IsSchauderBasis eW dW ∧ SchauderBasis.IsAbsolute eW dW := by sorry

/-- Paper: Theorem 7.3.1.6(4), p. 345, as used on p. 361. The ambient orbital
quotient needs the polynomial seminorm estimate when all places above the
chosen prime are present. The base set may be unsaturated at other primes.
The lattice is indexed from a contributing pole. -/
private theorem sLocalPWOrbital_biorthogonal_growth_primary (hST : S ⊆ T) (_hPic : PicTrivial)
    (p : Vℚ) (_hfull : ∀ w : V, w.under (𝓞 ℚ) = p → w ∈ T) (χ : PontryaginDual J₁(T))
    (ψ : Iₚ(p, χ) → Qₚ(p, χ))
    (_hψ : ∀ (i j : Iₚ(p, χ)) (x : Θ(T, χ)), (Rₚ(p, χ)).mkQ x = ψ j →
      sLocalOrbitalFourierJet (F := F) (S := T) i x = if i = j then 1 else 0) :
    ∀ (v : T), v.val ∈ sLocalPrimaryPlaces (F := F) T p →
    ∀ (c₀ : QuasiCharacter J(T)),
      (∃ j : Iₚ(p, χ), j.val.1 = c₀ ∧ v ∈ sLocalFinitePolePlaces (F := F) (S := T) c₀) →
    ∀ q : Seminorm ℂ Qₚ(p, χ), Continuous q →
      ∃ d : ℕ, ∃ C > (0 : ℝ), ∀ (n : ℤ) (j : Iₚ(p, χ)),
        j.val.1 = quasiCharacterNormTwist (G := J(T)) (m(T))
          (isProperMap_sIdeleQuotientNorm F T).continuous c₀
          (((n : ℝ) * (2 * Real.pi / Real.log (v.val.asIdeal.absNorm : ℝ)) : ℝ) * Complex.I) →
        q (ψ j) ≤ C * (1 + |(n : ℝ)|) ^ d := by
  sorry

/-- Paper: Theorem 7.3.3.4(3), p. 361.
Fourier-biorthogonal vectors of either sufficiently large level satisfy a polynomial
bound for each continuous seminorm along each pole lattice, uniformly in the jet order.
Deviation: Uses the nontrivial components of the repaired basis theorem. -/
theorem sLocalPWOrbital_biorthogonal_growth {S₀ : Finset V} (hST : S ⊆ T) (_hT : T = S ∪ S₀)
    (_hdis : Disjoint S S₀) (_hsat : IsSaturatedPlaceSet (F := F) S₀) (_hPic : PicTrivial)
    (p : Vℚ) (_hp : (sLocalPrimaryPlaces (F := F) T p).Nonempty)
    (_hp₀ : sLocalPrimaryPlaces (F := F) T p ⊆ S₀)
    (ω : PontryaginDual C₁) (hu : NormOneCharacterUnramifiedOutside ω S)
    (χ : PontryaginDual J₁(T)) (_hχ : χ = descend(hST, ω, hu)) (_hω : ω ≠ 1) :
    ∃ B : ℝ, 0 < B ∧ ∀ X Y : ℝ, B ≤ X → B ≤ Y → X ^ count(S) ≤ Y →
      ∀ (W : Submodule ℂ (Θ(T, χ))), (W = absPW(hST, X, χ) ∨ W = invPW(hST, Y, χ)) →
        ∀ (ψ : Iₚ(p, χ) → SLocalPWOrbitalQuotient χ p W),
          (∀ (i j : Iₚ(p, χ)) (x : W), ((Rₚ₀(p, χ)).comap W.subtype).mkQ x = ψ j →
            sLocalOrbitalFourierJet (F := F) (S := T) i x.val = if i = j then 1 else 0) →
          ∀ (v : T), v.val ∈ sLocalPrimaryPlaces (F := F) T p →
          ∀ (c₀ : QuasiCharacter J(T)),
            (∃ j : Iₚ(p, χ), j.val.1 = c₀ ∧ v ∈ sLocalFinitePolePlaces (F := F) (S := T) c₀) →
          ∀ q : Seminorm ℂ (SLocalPWOrbitalQuotient χ p W), Continuous q →
            ∃ d : ℕ, ∃ C > (0 : ℝ), ∀ (n : ℤ) (j : Iₚ(p, χ)),
              j.val.1 = quasiCharacterNormTwist (m(T))
                (isProperMap_sIdeleQuotientNorm F T).continuous c₀
                (((n : ℝ) * (2 * Real.pi / Real.log (v.val.asIdeal.absNorm : ℝ)) : ℝ) * Complex.I) →
              q (ψ j) ≤ C * (1 + |(n : ℝ)|) ^ d := by
  obtain ⟨B, hB, hlevel⟩ := sLocalPWOrbital_eventually_equiv hST _hT _hdis _hsat _hPic
    p _hp _hp₀ ω hu χ _hχ _hω
  refine ⟨B, hB, ?_⟩
  intro X Y hX hY hXY W hW ψ hψ v hv c₀ hc₀ q hq
  obtain ⟨e, he⟩ := hlevel X Y hX hY hXY W hW
  have hfull (w : V) (hw : w.under (𝓞 ℚ) = p) : w ∈ T := by
    have hvp := ((mem_sLocalPrimaryPlaces (F := F) (S := T) p v.val).mp hv).2
    have hw₀ := _hsat (_hp₀ hv) (hw.trans hvp.symm)
    rw [_hT]
    exact Finset.mem_union_right _ hw₀
  have hamb (i j : Iₚ(p, χ)) (x : Θ(T, χ)) (hx : (Rₚ(p, χ)).mkQ x = e (ψ j)) :
      sLocalOrbitalFourierJet (F := F) (S := T) i x = if i = j then 1 else 0 := by
    obtain ⟨u, hu⟩ := ((Rₚ₀(p, χ)).comap W.subtype).mkQ_surjective (ψ j)
    have heq : (Rₚ(p, χ)).mkQ x = (Rₚ(p, χ)).mkQ u.val :=
      hx.trans ((congrArg e hu.symm).trans (he u))
    let D := (Rₚ(p, χ)).liftQ (sLocalOrbitalFourierJet (F := F) (S := T) i).toLinearMap
      (sLocalOrbitalFourierJet_range_le_ker p χ i)
    exact (congrArg D heq).trans (hψ i j u hu)
  obtain ⟨d, C, hC, hbound⟩ := sLocalPWOrbital_biorthogonal_growth_primary hST _hPic p hfull χ
    (fun j ↦ e (ψ j)) hamb v hv c₀ hc₀ (q.comp e.symm.toLinearMap) (hq.comp e.symm.continuous)
  refine ⟨d, C, hC, fun n j hj ↦ ?_⟩
  have hb := hbound n j hj
  change q (e.symm (e (ψ j))) ≤ _ at hb
  simpa only [e.symm_apply_apply] using hb

section

open scoped ENNReal

/-- Sampling a vertically Schwartz function on an affine lattice preserves rapid decay. -/
private theorem rapidLatticeSamples (G : ℂ → ℂ) (hG : UniformlySchwartzOnStrip G (1/2) (3/2))
    (t d : ℝ) (hd : 0 < d) (N : ℕ) :
    ∃ C > (0 : ℝ), ∀ n : ℤ, ‖G (1 + ((t - n * d : ℝ) : ℂ) * Complex.I)‖ ≤
      C / (1 + |(n : ℝ)|) ^ N := by
  obtain ⟨C, hC, ht⟩ := hG.2.2 (1/4) (by norm_num) (by norm_num) (N+1) (by omega)
  obtain ⟨T, hT⟩ := eventually_atTop.mp (eventually_comap.mp ht)
  let A := max 1 T
  let g (y : ℝ) := G (1 + (y : ℂ) * Complex.I)
  have hg : Continuous g := by
    apply hG.2.1.continuousOn.comp_continuous (by fun_prop)
    intro y
    change 1 / 2 < (1 + (y : ℂ) * Complex.I).re ∧ (1 + (y : ℂ) * Complex.I).re < 3 / 2
    norm_num
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := -A) (b := A)).bddAbove_image
    (f := fun y : ℝ ↦ (1 + |y|)^N * ‖g y‖) (by fun_prop)
  let K := max (max B (2 ^ N * C)) 1
  have hK : 0 < K := zero_lt_one.trans_le (le_max_right _ _)
  have bound (y : ℝ) : (1 + |y|)^N * ‖g y‖ ≤ K := by
    by_cases hy : |y| ≤ A
    · exact (hB ⟨y, abs_le.mp hy, rfl⟩).trans ((le_max_left _ _).trans (le_max_left _ _))
    have h1 : 1 ≤ |y| := (le_max_left _ _).trans (le_of_not_ge hy)
    have hp : 0 < |y| := zero_lt_one.trans_le h1
    have hh := hT |y| ((le_max_right _ _).trans (le_of_not_ge hy)) y rfl 1 (by norm_num)
    change ‖g y‖ ≤ C / |y| ^ (N+1) at hh
    have hm := (le_div_iff₀ (pow_pos hp _)).mp hh
    have hn : |y| ^ N ≤ |y| ^ (N+1) := pow_le_pow_right₀ h1 (by omega)
    calc
      (1 + |y|)^N * ‖g y‖ ≤ (2 * |y|)^N * ‖g y‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) _) (norm_nonneg _)
      _ = 2^N * (|y| ^ N * ‖g y‖) := by rw [mul_pow]; ring
      _ ≤ 2^N * C := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (mul_le_mul_of_nonneg_right hn (norm_nonneg _)).trans (by simpa only [mul_comm ‖g y‖] using hm)
      _ ≤ K := (le_max_right _ _).trans (le_max_left _ _)
  let M := (1 + |t| + d) / d
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨M^N * K, mul_pos (pow_pos hM _) hK, fun n ↦ ?_⟩
  let y := t - (n : ℝ) * d
  have htri : |(n : ℝ)| * d ≤ |t| + |y| := by
    rw [← abs_of_pos hd, ← abs_mul]
    simpa [y] using (abs_sub t y)
  have hscale : 1 + |(n : ℝ)| ≤ M * (1 + |y|) := by
    dsimp [M]
    rw [div_mul_eq_mul_div, le_div_iff₀ hd]
    nlinarith [abs_nonneg t, abs_nonneg y, mul_nonneg (abs_nonneg t) (abs_nonneg y),
      mul_nonneg hd.le (abs_nonneg y)]
  apply (le_div_iff₀ (by positivity)).2
  change ‖g y‖ * (1 + |(n : ℝ)|)^N ≤ _
  calc
    _ ≤ ‖g y‖ * (M * (1 + |y|))^N :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hscale _) (norm_nonneg _)
    _ = M^N * ((1 + |y|)^N * ‖g y‖) := by rw [mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (bound y) (pow_pos hM _).le

/-- A sequence with all inverse-power bounds defines an elementary Schwartz test on the integer lattice. -/
private theorem orbitalIntegerRapid (g : ℤ → ℂ)
    (hg : ∀ N : ℕ, ∃ C > (0 : ℝ), ∀ n : ℤ, ‖g n‖ ≤ C / (1 + |(n : ℝ)|)^N) :
    ∃ s : RapidDecaySequence 1, ∀ n : ℤ, s (fun _ ↦ n) = g n := by
  let e := (Equiv.funUnique (Fin 1) ℤ).symm
  have hbase : Summable (fun n : ℤ ↦ 1 / (1 + |(n : ℝ)|)^2) := by
    have hn := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2))
    apply Summable.of_nat_of_neg
    · simpa [abs_of_nonneg, add_comm] using hn
    · simpa [abs_of_nonneg, add_comm] using hn
  let f (a : Fin 1 → ℤ) := g (a 0)
  have hs (j : ℕ) : Summable (fun n : ℤ ↦ (1 + |(n : ℝ)|)^j * ‖g n‖) := by
    obtain ⟨C, hC, hb⟩ := hg (j+2)
    apply (hbase.mul_left C).of_nonneg_of_le (fun _ ↦ by positivity)
    intro n
    have hn : 0 < 1 + |(n : ℝ)| := by positivity
    calc
      _ ≤ (1 + |(n : ℝ)|)^j * (C / (1 + |(n : ℝ)|)^(j+2)) :=
        mul_le_mul_of_nonneg_left (hb _) (pow_pos hn _).le
      _ = _ := by rw [pow_add]; field_simp
  refine ⟨⟨f, fun j ↦ ?_⟩, fun _ ↦ rfl⟩
  rw [rapidDecaySequenceBound, ← e.tsum_eq]
  have he (n : ℤ) : ‖(WithLp.toLp 2 (fun i ↦ ((e n i : ℤ) : ℝ)) : EuclideanSpace ℝ (Fin 1))‖ =
      |(n : ℝ)| := by simp [e, EuclideanSpace.norm_eq, Real.norm_eq_abs, Real.sqrt_sq_eq_abs]
  calc
    _ = ∑' n : ℤ, ENNReal.ofReal ((1 + |(n : ℝ)|)^j * ‖g n‖) := by
      apply tsum_congr
      intro n
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
        ENNReal.ofReal_add zero_le_one (abs_nonneg _), ENNReal.ofReal_one, ofReal_norm]
      congr 2
      apply congrArg (fun q : ℝ≥0∞ ↦ 1 + q)
      exact (ofReal_norm _).symm.trans (congrArg ENNReal.ofReal (he n))
    _ < ⊤ := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ by positivity) (hs j)]
      exact ENNReal.ofReal_lt_top

/-- The maximal elementary stage of the discrete group ℤ realizes its rapidly decreasing sequences. -/
private theorem orbitalIntegerSchwartz (g : ℤ → ℂ)
    (hg : ∀ N : ℕ, ∃ C > (0 : ℝ), ∀ n : ℤ, ‖g n‖ ≤ C / (1 + |(n : ℝ)|)^N) :
    ∃ a : SchwartzBruhat (Multiplicative ℤ), ∀ n : ℤ, a (Multiplicative.ofAdd n) = g n := by
  obtain ⟨s, hs⟩ := orbitalIntegerRapid g hg

  let H := Multiplicative ℤ
  let E₀ := ElementaryLieGroup 0 0 1 PUnit
  let c : H ≃ₜ* Multiplicative E₀ :=
    { toFun := fun n ↦ Multiplicative.ofAdd (0, 0, fun _ ↦ n.toAdd, 0)
      invFun := fun x ↦ Multiplicative.ofAdd (x.toAdd.2.2.1 0)
      left_inv := fun _ ↦ rfl
      right_inv := fun x ↦ by
        apply Multiplicative.toAdd.injective
        apply Prod.ext (Subsingleton.elim _ _)
        apply Prod.ext (Subsingleton.elim _ _)
        apply Prod.ext _ (Subsingleton.elim _ _)
        exact funext fun i ↦ congrArg x.toAdd.2.2.1 (Subsingleton.elim 0 i)
      map_mul' := fun _ _ ↦ by
        apply Multiplicative.toAdd.injective
        apply Prod.ext (Subsingleton.elim _ _)
        apply Prod.ext (Subsingleton.elim _ _)
        exact Prod.ext rfl (Subsingleton.elim _ _)
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }
  let p : ElementaryLCAPresentation H := ⟨0, 0, 1, PUnit, c⟩
  have hG := (lca_elementary_iff (G := H)).mpr ⟨p⟩
  let top : (⊤ : Subgroup H) ≃ₜ* H := ⟨Subgroup.topEquiv, continuous_subtype_val, continuous_id.subtype_mk _⟩
  let a : BruhatStructuralPair H := ⟨(⊤, OrderDual.toDual ⊥), isOpen_univ,
    isCompactlyGeneratedGroup_of_continuousMulEquiv top.symm hG.1,
    isBruhatGoodSubgroup_bot_iff.mpr hG.2, bot_le⟩
  let q : a.quotient ≃* H :=
    QuotientGroup.quotientKerEquivOfRightInverse a.val.1.subtype top.symm (fun _ ↦ rfl)
  let q' : a.quotient ≃ₜ* H :=
    { q with
      continuous_toFun := (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr continuous_subtype_val
      continuous_invFun := QuotientGroup.continuous_mk.comp top.symm.continuous }
  let e : ElementaryLCAPresentation a.quotient := ⟨0, 0, 1, PUnit, q'.trans c⟩
  obtain ⟨E, hE⟩ := rapidDecaySequence_equiv_elementarySchwartz (r := 1)
  refine ⟨schwartzBruhatStageInclusion a e (E s), fun n ↦ ?_⟩
  change schwartzBruhatStageRealization a e (E s) (Multiplicative.ofAdd n) = _
  rw [schwartzBruhatStageRealization_apply, dite_eq_left (Subgroup.mem_top _)]
  exact (hE s _).trans (hs n)

end

open Classical in
/-- Paper: Theorem 7.3.3.4(3), p. 361.
Fourier coefficients of each class in a PW orbital quotient decay as a Schwartz
sequence along each local pole lattice at fixed derivative order.
Deviation: Uses the intersection quotient from the proof and the same zero-extension
convention as Theorem 7.3.1.6(5). The lattice is based at any pole at the chosen place. -/
theorem sLocalPWOrbital_fourier_decay (p : Vℚ) (ω : PontryaginDual J₁(T))
    (W : Submodule ℂ (Θ(T, ω)))
    (d : Iₚ(p, ω) → StrongDual ℂ (SLocalPWOrbitalQuotient ω p W))
    (_hd : ∀ j (x : W), d j (((Rₚ₀(p, ω)).comap W.subtype).mkQ x) =
      sLocalOrbitalFourierJet (F := F) (S := T) j x.val)
    (v : T) (_hv : v.val ∈ sLocalPrimaryPlaces (F := F) T p)
    (c₀ : QuasiCharacter J(T))
    (_hc₀ : ∃ j : Iₚ(p, ω), j.val.1 = c₀ ∧ v ∈ sLocalFinitePolePlaces (F := F) (S := T) c₀)
    (k : ℕ) (x : SLocalPWOrbitalQuotient ω p W) :
    let c := fun n : ℤ ↦ quasiCharacterNormTwist (m(T))
      (isProperMap_sIdeleQuotientNorm F T).continuous c₀
      (((n : ℝ) * (2 * Real.pi / Real.log (v.val.asIdeal.absNorm : ℝ)) : ℝ) * Complex.I)
    ∃ a : SchwartzBruhat (Multiplicative ℤ), ∀ n : ℤ,
      (∀ j : Iₚ(p, ω), j.val = (c n, k) → a (Multiplicative.ofAdd n) = d j x) ∧
      ((¬ ∃ j : Iₚ(p, ω), j.val = (c n, k)) → a (Multiplicative.ofAdd n) = 0) := by
  classical
  let period := 2 * Real.pi / Real.log (v.val.asIdeal.absNorm : ℝ)
  have hperiod : 0 < period := div_pos (by positivity) (Real.log_pos (by
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v.val))
  let twist := quasiCharacterNormTwist (m(T)) (isProperMap_sIdeleQuotientNorm F T).continuous
  let unitary (χ : PontryaginDual J(T)) :=
    (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ
  let dual := dualQuasiCharacter (m(T)) (isProperMap_sIdeleQuotientNorm F T).continuous
  let c (n : ℤ) := twist c₀ (((n : ℝ) * period : ℝ) * Complex.I)
  obtain ⟨χ, s, hs⟩ := exists_sLocalNormTwist (F := F) (S := T) c₀
  obtain ⟨π, hπ⟩ := (Valued.v : Valuation (v.val.adicCompletion F)
    (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
  let u : (v.val.adicCompletion F)ˣ := Units.mk0 (π : v.val.adicCompletion F) hπ.ne_zero
  have hu := norm_uniformizer_adicCompletion v.val (π : v.val.adicCompletion F) hπ
  obtain ⟨t, ht⟩ := (existsUnique_sLocalOrbitalPhase χ v u hu).exists
  obtain ⟨m, hm⟩ := (existsUnique_sLocalOrbitalLatticeIndex χ v u hu t ht c₀
    ⟨s, hs.symm⟩ _hc₀.choose_spec.2).exists
  let b := (m : ℝ) * period - t
  have hbase : c₀ = twist (unitary χ) ((b : ℂ) * Complex.I) := hm
  obtain ⟨w, rfl⟩ := ((Rₚ₀(p, ω)).comap W.subtype).mkQ_surjective x
  obtain ⟨f, hf⟩ := (LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap F T ω)).mkQ_surjective w.val
  let jet (n : ℤ) := iteratedDeriv k
    (fun z : ℂ ↦ sLocalIdelicZFunction (sAdeleSchwartzFourier f) (dual (twist (c n) z))) 0
  let g (n : ℤ) := if ∃ j : Iₚ(p, ω), j.val = (c n, k) then jet n else 0
  let Z (s : ℂ) := sLocalIdelicZFunction (sAdeleSchwartzFourier f) (twist (unitary χ⁻¹) s)
  have hZ : UniformlySchwartzOnStrip (iteratedDeriv k Z) (1/2) (3/2) :=
    sLocalIdelicZFunction_schwartzOnStrip (sAdeleSchwartzFourier f) χ⁻¹ _ _
      (by norm_num) (by norm_num) k
  have hg (N : ℕ) : ∃ C > (0 : ℝ), ∀ n : ℤ, ‖g n‖ ≤ C / (1 + |(n : ℝ)|)^N := by
    obtain ⟨C, hC, h⟩ := rapidLatticeSamples (iteratedDeriv k Z) hZ (-b) period hperiod N
    refine ⟨C, hC, fun n ↦ ?_⟩
    dsimp only [g]
    split_ifs
    · let a : ℂ := ((b + (n : ℝ) * period : ℝ) : ℂ) * Complex.I
      have he : (fun z : ℂ ↦ sLocalIdelicZFunction (sAdeleSchwartzFourier f) (dual (twist (c n) z))) =
          fun z ↦ Z ((1 - a) - z) := by
        funext z
        dsimp only [Z, dual, c, twist, unitary]
        rw [hbase]
        dsimp only [twist, unitary]
        simp only [normTwist_normTwist, sLocal_dual_normTwist]
        dsimp only [a]
        congr 2
        push_cast
        ring
      simp only [jet, he, iteratedDeriv_comp_const_sub, sub_zero, norm_smul, norm_pow, norm_neg,
        norm_one, one_pow, one_mul]
      convert h n using 3
      dsimp only [a]
      push_cast
      ring
    · simp only [norm_zero]
      positivity
  obtain ⟨a, ha⟩ := orbitalIntegerSchwartz g hg
  refine ⟨a, fun n ↦ ⟨fun j hj ↦ ?_, fun hn ↦ ?_⟩⟩
  · rw [ha, show g n = jet n from if_pos ⟨j, hj⟩, _hd, ← hf]
    change jet n = sLocalOrbitalFourierJet j ((LinearMap.ker
      (sLocalHomogeneousAdelicThetaLinearMap F T ω)).mkQL f)
    rw [sLocalOrbitalFourierJet_mk, show j.val.1 = c n from congrArg Prod.fst hj,
      show j.val.2 = k from congrArg Prod.snd hj]
  · exact (ha n).trans (if_neg hn)


end PWOrbitalQuotients

section ArchimedeanPoles

local notation "Xₛ" => QuasiCharacter J(S)
local notation "fullPV(" ω ")" => (PV((Finset.Subset.refl S), ω)).range
local notation "noPoles(" ω ")" => sLocalThetaPoleBound (F := F) (S := S) ω (fun _ ↦ 0)
local notation "chart(" c ")" => quasiCharacterNormTwist (m(S))
  (isProperMap_sIdeleQuotientNorm F S).continuous c
local notation "shift(" c ", " z ")" => chart(c) z
local notation "arch(" c ")" => sLocalArchPolePlaces (F := F) (S := S) c
local notation "depths" => (InfinitePlace F → ℕ)

/-- Paper: Notation 7.3.4.1, p. 364.
The selected centers on a component are among the first specified number of poles
at one or more archimedean places, starting at the rightmost pole.
Deviation: The real and complex cutoff tuples are combined into a single
place-indexed family. Local poles are ranked by positive real norm shifts, so a
cutoff of n includes n + 1 local poles. -/
def sLocalGammaPoleCutoff (ω : PontryaginDual J₁(S)) (N : depths) : Set Xₛ :=
  {c | onComponent(c, ω) ∧
    ∃ w ∈ arch(c), ({t : ℝ | 0 < t ∧ w ∈ arch(shift(c, (t : ℂ)))} : Set ℝ).encard ≤ N w}

variable (S) in
/-- Paper: Notation 7.3.4.1, p. 364.
The zero cutoff selects the trivial quasi-character on the trivial component
and excludes its shift down by two. -/
theorem sLocalGammaPoleCutoff_zero :
    (1 : Xₛ) ∈ sLocalGammaPoleCutoff (F := F) (S := S) 1 (fun _ ↦ 0) ∧
      shift((1 : Xₛ), (-2 : ℂ)) ∉ sLocalGammaPoleCutoff (F := F) (S := S) 1 (fun _ ↦ 0) := by
  classical
  -- Twisting twice adds the exponents.
  have htw (a z : ℂ) : shift(shift((1 : Xₛ), a), z) = shift((1 : Xₛ), z + a) := by
    ext1 g
    change (1 : Xₛ) g * _ ^ a * _ ^ z = (1 : Xₛ) g * _ ^ (z + a)
    rw [add_comm, Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr
      (NNReal.coe_ne_zero.mpr (m(S) g).ne_zero)), mul_assoc]
  have h10 : shift((1 : Xₛ), 0) = 1 := by
    ext1 g
    change (1 : Xₛ) g * _ ^ (0 : ℂ) = (1 : Xₛ) g
    rw [Complex.cpow_zero, mul_one]
  -- The archimedean Euler factor along the chart through the trivial character.
  let G : InfinitePlace F → ℂ → ℂ := fun w s ↦
    if w.IsReal then Complex.Gammaℝ s else Complex.Gammaℂ s / 2
  have hres (w : InfinitePlace F) (s : ℂ) (g : w.Completionˣ) :
      sLocalInfiniteRestriction w (shift((1 : Xₛ), s)) g =
        ((((Units.map nnNormHom.toMonoidHom ^ w.mult : w.Completionˣ →* ℝ≥0ˣ) g : ℝ≥0) : ℝ) :
          ℂ) ^ s := by
    have h1 : shift((1 : Xₛ), s) = quasiCharacterNormTwist (m(S))
        (isProperMap_sIdeleQuotientNorm F S).continuous
        ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp
          (1 : PontryaginDual J(S))) s := by
      ext1 x
      change (1 : ℂ) * _ = ((1 : Circle) : ℂ) * _
      rw [Circle.coe_one]
      rfl
    rw [h1]
    exact sLocalInfiniteRestriction_normTwist w s g
  have hE (w : InfinitePlace F) (s : ℂ) :
      infiniteLocalEulerFactor w (sLocalInfiniteRestriction w (shift((1 : Xₛ), s))) = G w s := by
    by_cases hw : w.IsReal
    · let e := (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm
      have hshape : ∀ x : ℝˣ, sLocalInfiniteRestriction w (shift((1 : Xₛ), s))
          (Units.map e.toMonoidHom x) =
            (‖(x : ℝ)‖ : ℂ) ^ s * (if 0 < (x : ℝ) then 1 else (-1 : ℂ)) ^ (0 : Fin 2).val := by
        intro x
        have hn : ‖(e (x : ℝ) : w.Completion)‖ = ‖(x : ℝ)‖ :=
          (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.isometry.norm_map_of_map_zero
            (map_zero e) (x : ℝ)
        have hm : (((Units.map nnNormHom.toMonoidHom ^ w.mult : w.Completionˣ →* ℝ≥0ˣ)
            (Units.map e.toMonoidHom x) : ℝ≥0) : ℝ) = ‖(x : ℝ)‖ := by
          simp [InfinitePlace.mult, hw, hn]
        rw [hres, hm, Fin.val_zero, pow_zero, mul_one]
      have hq := (realLocalEulerParameters w hw (sLocalInfiniteRestriction w
        (shift((1 : Xₛ), s)))).unique (realLocalEulerParameters w hw
          (sLocalInfiniteRestriction w (shift((1 : Xₛ), s)))).exists.choose_spec
        (y₂ := (s, 0)) hshape
      simp only [infiniteLocalEulerFactor, hw, ↓reduceDIte, hq, G, ite_true, Fin.val_zero,
        Nat.cast_zero, add_zero]
    · have hwc := InfinitePlace.not_isReal_iff_isComplex.mp hw
      let e := (InfinitePlace.Completion.ringEquivComplexOfIsComplex hwc).symm
      have hshape : ∀ x : ℂˣ, sLocalInfiniteRestriction w (shift((1 : Xₛ), s))
          (Units.map e.toMonoidHom x) =
            ((‖(x : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ s * ((x : ℂ) / (‖(x : ℂ)‖ : ℂ)) ^ (0 : ℤ) := by
        intro x
        have hn : ‖(e (x : ℂ) : w.Completion)‖ = ‖(x : ℂ)‖ :=
          (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
            hwc).symm.isometry.norm_map_of_map_zero (map_zero e) (x : ℂ)
        have hm : (((Units.map nnNormHom.toMonoidHom ^ w.mult : w.Completionˣ →* ℝ≥0ˣ)
            (Units.map e.toMonoidHom x) : ℝ≥0) : ℝ) = ‖(x : ℂ)‖ ^ 2 := by
          simp [InfinitePlace.mult, hw, hn]
        rw [hres, hm, zpow_zero, mul_one]
      have hq := (complexLocalEulerParameters w hwc (sLocalInfiniteRestriction w
        (shift((1 : Xₛ), s)))).unique (complexLocalEulerParameters w hwc
          (sLocalInfiniteRestriction w (shift((1 : Xₛ), s)))).exists.choose_spec
        (y₂ := (s, 0)) hshape
      simp only [infiniteLocalEulerFactor, hw, ↓reduceDIte, hq, G, ite_false, Int.natAbs_zero,
        Nat.cast_zero, zero_div, add_zero]
  -- `G w` has a pole at zero and is regular at every positive real point.
  have hinv (w : InfinitePlace F) : Differentiable ℂ (fun s ↦ (G w s)⁻¹) := by
    by_cases hw : w.IsReal
    · simpa only [G, hw, ite_true] using Complex.differentiable_Gammaℝ_inv
    · simp only [G, hw, ite_false, inv_div]
      exact Complex.differentiable_Gammaℂ_inv.const_mul 2
  have hmer (w : InfinitePlace F) (x : ℂ) : MeromorphicAt (G w) x := by
    convert ((hinv w).analyticAt x).meromorphicAt.inv using 1
    funext s
    simp
  have hpole (w : InfinitePlace F) : meromorphicOrderAt (G w) 0 < 0 := by
    have hlim : ∃ c ≠ (0 : ℂ), Tendsto (fun s ↦ s * G w s) (𝓝[≠] 0) (𝓝 c) := by
      by_cases hw : w.IsReal
      · exact ⟨2, two_ne_zero, by simpa only [G, hw, ite_true] using Complex.Gammaℝ_residue_zero⟩
      · refine ⟨1, one_ne_zero, ?_⟩
        have := Complex.Gammaℂ_residue_zero.div_const 2
        simp only [div_self (two_ne_zero' ℂ)] at this
        simpa only [G, hw, ite_false, mul_div_assoc] using this
    have h0 := (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero
      (analyticAt_id.meromorphicAt.mul (hmer w 0))).mp hlim
    have hm := meromorphicOrderAt_mul (f := id) analyticAt_id.meromorphicAt (hmer w 0)
    change meromorphicOrderAt (id * G w) 0 = 0 at h0
    rw [hm, meromorphicOrderAt_id] at h0
    cases hn : meromorphicOrderAt (G w) 0 with
    | top => rw [hn] at h0; simp at h0
    | coe n =>
      rw [hn] at h0
      have : 1 + n = 0 := by exact_mod_cast h0
      exact_mod_cast (by omega : n < 0)
  have hreg (w : InfinitePlace F) (t : ℝ) (ht : 0 < t) :
      ¬ meromorphicOrderAt (fun z ↦ G w (z + t)) 0 < 0 := by
    have hne : (G w t)⁻¹ ≠ 0 := by
      refine inv_ne_zero ?_
      by_cases hw : w.IsReal
      · simpa only [G, hw, ite_true] using Complex.Gammaℝ_ne_zero_of_re_pos (by simpa using ht)
      · simp only [G, hw, ite_false, Complex.Gammaℂ_def]
        refine div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero ?_) ?_) two_ne_zero
        · exact (Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by simpa using ht.ne')).mpr
            (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
        · exact Complex.Gamma_ne_zero_of_re_pos (by simpa using ht)
    have han : AnalyticAt ℂ (fun z ↦ ((G w (z + t))⁻¹)⁻¹) 0 :=
      (((hinv w).analyticAt _).comp (f := fun z : ℂ ↦ z + t) (by fun_prop)).inv
        (by simpa using hne)
    simp only [inv_inv] at han
    exact not_lt.mpr han.meromorphicOrderAt_nonneg
  have harch (a : ℂ) (w : InfinitePlace F) :
      w ∈ arch(shift((1 : Xₛ), a)) ↔ meromorphicOrderAt (fun z ↦ G w (z + a)) 0 < 0 := by
    simp only [sLocalArchPolePlaces, Finset.mem_filter, Finset.mem_univ, true_and]
    refine iff_of_eq (congrArg (· < 0) (congrArg (meromorphicOrderAt · 0) ?_))
    funext z
    rw [htw, hE]
  have h1 (w : InfinitePlace F) : w ∈ arch((1 : Xₛ)) := by
    rw [← h10, harch]
    simpa only [add_zero] using hpole w
  refine ⟨⟨?_, Classical.arbitrary _, h1 _, ?_⟩, ?_⟩
  · ext g
    change (1 : ℂ) = ((1 : Circle) : ℂ)
    rw [Circle.coe_one]
  · have hempty : {t : ℝ | 0 < t ∧ Classical.arbitrary (InfinitePlace F) ∈
        arch(shift((1 : Xₛ), (t : ℂ)))} = ∅ :=
      Set.eq_empty_of_forall_notMem fun t ⟨ht, hw⟩ ↦ hreg _ t ht ((harch _ _).mp hw)
    rw [hempty, Set.encard_empty]
    exact zero_le
  · rintro ⟨-, w, -, hcard⟩
    have h2 : (2 : ℝ) ∈ {t : ℝ | 0 < t ∧ w ∈ arch(shift(shift((1 : Xₛ), (-2 : ℂ)), (t : ℂ)))} := by
      refine ⟨two_pos, ?_⟩
      rw [htw, show ((2 : ℝ) : ℂ) + -2 = 0 by push_cast; ring, h10]
      exact h1 w
    have hc : _ ≤ (0 : ℕ∞) := hcard
    exact (Set.encard_pos.mpr ⟨2, h2⟩).ne' (nonpos_iff_eq_zero.mp hc)

local notation "ΓIndex(" ω ", " U ")" =>
  {j : Xₛ × ℕ // onComponent(j.1, ω) ∧ j.1 ∈ U ∧ 0 < j.2 ∧ j.2 ≤ (arch(j.1)).card}
local notation "ΓCoeff(" ω ", " j ")" =>
  ((sLocalThetaPrincipalPartCoeff (F := F) (S := S) ω (j).val.1 (j).property.1 (j).val.2).comp
    (fullPV(ω)).subtypeL)

/-- Paper: Notation 7.3.4.1, p. 364.
The filtered subspace of the full finite principal-value image has no poles at
the selected archimedean centers. It carries the induced topology.
Deviation: Cutoffs are indexed by places. Increasing all local cutoffs gives
the filtration inclusions. -/
def sLocalGammaFiltration (ω : PontryaginDual J₁(S)) (N : depths) :
    Submodule ℂ (fullPV(ω)) :=
  ⨅ j : ΓIndex(ω, sLocalGammaPoleCutoff (F := F) (S := S) ω N), (ΓCoeff(ω, j)).ker

/-- On a full finite principal value only archimedean poles remain. Express the
pole bound of §5.3.4 in the norm coordinate centered at the given character. -/
private theorem gammaFiltration_principalValue_bound (g : B(S)) (c : Xₛ) :
    sLocalPolarMultiplicity (sAdelePrincipalValue F (Finset.Subset.refl S) g) c ≤
      (arch(c)).card := by
  classical
  obtain ⟨χ, a, rfl⟩ := exists_sLocalNormTwist (F := F) (S := S) c
  let d : Xₛ := (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ
  have translate (H : Xₛ → ℂ) :
      meromorphicOrderAt (fun z : ℂ ↦ H (shift(shift(d, a), z))) 0 =
        meromorphicOrderAt (fun z : ℂ ↦ H (shift(d, z))) a := by
    have e : (fun z : ℂ ↦ H (shift(shift(d, a), z))) =
        (fun z : ℂ ↦ H (shift(d, z))) ∘ (· + a) := by
      funext z
      rw [normTwist_normTwist]
      rfl
    rw [e, meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt, zero_add]
  have places : (arch(shift(d, a))).card = sLocalArchimedeanPoleMultiplicity χ a := by
    unfold sLocalArchPolePlaces sLocalArchimedeanPoleMultiplicity
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro w _
    rw [translate (fun b ↦ infiniteLocalEulerFactor w (sLocalInfiniteRestriction w b))]
  let p := sAdelePrincipalValue F (Finset.Subset.refl S) g
  change (-(meromorphicOrderAt (fun z : ℂ ↦ sLocalIdelicZFunction p (shift(shift(d, a), z))) 0).untop₀).toNat ≤ _
  rw [translate (sLocalIdelicZFunction p), places]
  have hb := sLocalIdelicZFunction_principalValue_pole_bound g χ a
  change ((-(sLocalArchimedeanPoleMultiplicity χ a : ℤ) : ℤ) : WithTop ℤ) ≤
    meromorphicOrderAt (fun z : ℂ ↦ sLocalIdelicZFunction p (shift(d, z))) a at hb
  generalize meromorphicOrderAt (fun z : ℂ ↦ sLocalIdelicZFunction p (shift(d, z))) a = o at hb ⊢
  induction o using WithTop.recTopCoe with
  | top => simp
  | coe n =>
    have hn := WithTop.coe_le_coe.mp hb
    simp only [WithTop.untop₀_coe]
    omega

/-- Paper: Notation 7.3.4.1, p. 364.
A class in the full finite principal-value image is in a filtered stage exactly
when its representative's Mellin transform has no poles at the selected centers. -/
theorem mem_sLocalGammaFiltration (ω : PontryaginDual J₁(S)) (N : depths)
    (x : fullPV(ω)) (f : B(S)) (_hf : q(S, ω) f = x.val) :
    x ∈ sLocalGammaFiltration ω N ↔
      ∀ c ∈ sLocalGammaPoleCutoff (F := F) (S := S) ω N,
        0 ≤ meromorphicOrderAt (fun z : ℂ ↦ sLocalIdelicZFunction f (shift(c, z))) 0 := by
  classical
  change (x ∈ ⨅ j : ΓIndex(ω, sLocalGammaPoleCutoff (F := F) (S := S) ω N),
    (ΓCoeff(ω, j)).ker) ↔ _
  rw [Submodule.mem_iInf]
  constructor
  · intro h c hc
    rw [← sLocalPolarMultiplicity_eq_zero_iff]
    by_contra hne
    let k := sLocalPolarMultiplicity f c
    have hk : 0 < k := Nat.pos_of_ne_zero hne
    let L := sLocalThetaPrincipalPartCoeff ω c hc.1 k
    have hL : L x.val ≠ 0 := by
      rw [← _hf]
      exact mem_sLocalThetaPoleBound_iff_leading (sLocalZ_centered f c).1 hk rfl
    obtain ⟨y, hy⟩ := x.property
    obtain ⟨g, rfl⟩ := (Submodule.mkQ_surjective _) y
    have hg : sLocalPrincipalPartCoeff c k (sAdelePrincipalValue F (Finset.Subset.refl S) g) ≠ 0 := by
      rw [← hy] at hL
      exact hL
    have hle := (sLocalPrincipalPartCoeff_ne_zero_imp_pole c k hk _ hg).2
    let j : ΓIndex(ω, sLocalGammaPoleCutoff (F := F) (S := S) ω N) :=
      ⟨(c, k), hc.1, hc, hk, hle.trans (gammaFiltration_principalValue_bound g c)⟩
    exact hL (h j)
  · intro h j
    change sLocalThetaPrincipalPartCoeff ω j.val.1 j.property.1 j.val.2 x.val = 0
    rw [← _hf]
    change sLocalPrincipalPartCoeff j.val.1 j.val.2 f = 0
    by_contra hne
    have hle := (sLocalPrincipalPartCoeff_ne_zero_imp_pole _ _ j.property.2.2.1 f hne).2
    rw [(sLocalPolarMultiplicity_eq_zero_iff f _).2 (h _ j.property.2.1)] at hle
    exact (not_lt_of_ge hle) j.property.2.2.1

/-- Paper: Notation 7.3.4.1, p. 364.
The denominator of the archimedean polar quotient is the subspace with entire Mellin transform.
Deviation: Uses the equivalent zero-pole-bound model for the theta image of S₀₀ from §7.2. -/
def sLocalGammaEntireSubmodule (ω : PontryaginDual J₁(S)) : Submodule ℂ (fullPV(ω)) :=
  (noPoles(ω)).comap (fullPV(ω)).subtype

local notation "Γker(" ω ")" => sLocalGammaEntireSubmodule (F := F) (S := S) ω

/-- Paper: Notation 7.3.4.1, p. 364.
The archimedean polar quotient divides the full finite principal-value image
by the subspace with entire Mellin transform, and carries the quotient topology.

This is a `def` with its own instances, not an `abbrev`, so that instance terms over it do
not spell out its definition (#5398). -/
def SLocalGammaOrbitalQuotient (ω : PontryaginDual J₁(S)) := fullPV(ω) ⧸ Γker(ω)

namespace SLocalGammaOrbitalQuotient

instance instAddCommGroup (ω : PontryaginDual J₁(S)) :
    AddCommGroup (SLocalGammaOrbitalQuotient ω) :=
  inferInstanceAs (AddCommGroup (fullPV(ω) ⧸ Γker(ω)))

instance instModule (ω : PontryaginDual J₁(S)) : Module ℂ (SLocalGammaOrbitalQuotient ω) :=
  inferInstanceAs (Module ℂ (fullPV(ω) ⧸ Γker(ω)))

instance instTopologicalSpace (ω : PontryaginDual J₁(S)) :
    TopologicalSpace (SLocalGammaOrbitalQuotient ω) :=
  inferInstanceAs (TopologicalSpace (fullPV(ω) ⧸ Γker(ω)))

instance instIsTopologicalAddGroup (ω : PontryaginDual J₁(S)) :
    IsTopologicalAddGroup (SLocalGammaOrbitalQuotient ω) :=
  inferInstanceAs (IsTopologicalAddGroup (fullPV(ω) ⧸ Γker(ω)))

instance instContinuousSMul (ω : PontryaginDual J₁(S)) :
    ContinuousSMul ℂ (SLocalGammaOrbitalQuotient ω) :=
  inferInstanceAs (ContinuousSMul ℂ (fullPV(ω) ⧸ Γker(ω)))

end SLocalGammaOrbitalQuotient

/-- Paper: Notation 7.3.4.1, p. 364.
A representative of the zero coset has a Mellin transform with no poles on the
component, and the entire-Mellin subspace consists of these representatives. -/
theorem mem_sLocalGammaEntireSubmodule (ω : PontryaginDual J₁(S))
    (x : fullPV(ω)) (f : B(S)) (_hf : q(S, ω) f = x.val) :
    x ∈ Γker(ω) ↔
      ∀ c : Xₛ, onComponent(c, ω) →
        0 ≤ meromorphicOrderAt (fun z : ℂ ↦ sLocalIdelicZFunction (F := F) (S := S) f (shift(c, z))) 0 :=
  by
  -- A germ with no pole has vanishing polar Laurent coefficients.
  have hres (Z : ℂ → ℂ) (hZ : MeromorphicAt Z 0) (h0 : 0 ≤ meromorphicOrderAt Z 0) (N : ℕ)
      (hN : 0 < N) : complexResidue (fun z ↦ Z z / z ^ (-(N : ℤ) + 1)) 0 = 0 := by
    have ha := hZ.meromorphicOrderAt_nonneg_iff_analyticAt_toMeromorphicNFAt.1 h0
    have he : (fun z ↦ Z z / z ^ (-(N : ℤ) + 1)) =ᶠ[𝓝[≠] (0 : ℂ)]
        (fun z ↦ z ^ N * toMeromorphicNFAt Z 0 z / (z - 0)) := by
      filter_upwards [hZ.eq_nhdsNE_toMeromorphicNFAt, self_mem_nhdsWithin] with z hz hz0
      have hz0' : z ≠ 0 := hz0
      rw [hz, sub_zero, zpow_add₀ hz0', zpow_one, zpow_neg, zpow_natCast]
      field_simp
    have hg : AnalyticAt ℂ (fun z ↦ z ^ N * toMeromorphicNFAt Z 0 z) 0 :=
      (analyticAt_id.pow N).mul ha
    rw [mem_sLocalThetaPoleBound_iff_residue_congr he, complexResidue_div_sub hg]
    simp [zero_pow hN.ne']
  change x.val ∈ noPoles(ω) ↔ _
  rw [← _hf]
  constructor
  · intro hx c hc
    rw [← sLocalPolarMultiplicity_eq_zero_iff]
    by_contra hne
    have hN : 0 < sLocalPolarMultiplicity f c := Nat.pos_of_ne_zero hne
    let T := sLocalThetaPrincipalPartCoeff ω c hc (sLocalPolarMultiplicity f c)
    have hle : noPoles(ω) ≤ LinearMap.ker (T : Θ(S, ω) →ₗ[ℂ] ℂ) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨g, rfl, hg⟩
      change complexResidue (fun z ↦ sLocalIdelicZFunction g (shift(c, z)) /
        z ^ (-((sLocalPolarMultiplicity f c : ℕ) : ℤ) + 1)) 0 = 0
      exact hres _ (sLocalZ_centered g c).1
        ((sLocalPolarMultiplicity_eq_zero_iff g c).1 (Nat.le_zero.1 (hg c hc))) _ hN
    have h0 : complexResidue (fun z ↦ sLocalIdelicZFunction f (shift(c, z)) /
        z ^ (-((sLocalPolarMultiplicity f c : ℕ) : ℤ) + 1)) 0 = 0 := hle hx
    exact mem_sLocalThetaPoleBound_iff_leading (sLocalZ_centered f c).1 hN rfl h0
  · intro h
    exact Submodule.subset_span
      ⟨f, rfl, fun c hc ↦ ((sLocalPolarMultiplicity_eq_zero_iff f c).2 (h c hc)).le⟩

/-- Paper: Notation 7.3.4.1, p. 364.
The archimedean polar quotient is Fréchet. -/
theorem sLocalGammaOrbitalQuotient_frechet (ω : PontryaginDual J₁(S)) :
    let P := Γker(ω)
    @IsFrechetTVS _ (Submodule.Quotient.addCommGroup P) (Submodule.Quotient.module P)
      (QuotientModule.Quotient.topologicalSpace P) := by
  intro P
  have hP : IsClosed (P : Set (fullPV(ω))) :=
    (sLocalThetaPoleBound_isClosed (F := F) (S := S) ω (fun _ ↦ 0)).preimage continuous_subtype_val
  have hR := (sLocalHomogeneousThetaPrincipalValue_isClosedEmbedding (Finset.Subset.refl S) ω).isClosed_range
  exact isFrechetTVS_quotient
    (frechet_of_closed_embedding (fullPV(ω)).subtypeL ((fullPV(ω)).isClosedEmbedding_subtypeL hR)
      (sLocalHomogeneousThetaSpace_frechet (F := F) (S := S) ω)) P hP

/-- Paper: Notation 7.3.4.1, p. 364.
The archimedean polar quotient is nuclear. -/
theorem sLocalGammaOrbitalQuotient_nuclear (ω : PontryaginDual J₁(S)) :
    let P := Γker(ω)
    @IsNuclearTVS _ (Submodule.Quotient.addCommGroup P) (Submodule.Quotient.module P)
      (QuotientModule.Quotient.topologicalSpace P) := by
  intro P
  have hR := isNuclearTVS_submodule
    (sLocalHomogeneousThetaSpace_nuclear (F := F) (S := S) ω) (fullPV(ω))
  let := hR.2.1
  let : IsTopologicalAddGroup (fullPV(ω)) := PolynormableSpace.isTopologicalAddGroup ℂ _
  have hP : IsClosed (P : Set (fullPV(ω))) :=
    (sLocalThetaPoleBound_isClosed (F := F) (S := S) ω (fun _ ↦ 0)).preimage continuous_subtype_val
  let : T3Space (fullPV(ω) ⧸ P) := Submodule.t3_quotient_of_isClosed P
  let : T2Space (fullPV(ω) ⧸ P) := @T25Space.t2Space _ _ T3Space.t25Space
  exact isNuclearTVS_quotient hR P

/-- Paper: Notation 7.3.4.1, p. 364.
Increasing all local cutoffs decreases the corresponding subspace.
Deviation: Uses the pointwise order. Lexicographic order need not give nested stages. -/
theorem sLocalGammaFiltration_antitone (ω : PontryaginDual J₁(S)) :
    Antitone (sLocalGammaFiltration ω) := by
  intro N N' hN
  unfold sLocalGammaFiltration
  refine le_iInf fun j ↦ iInf_le_of_le ⟨j.val, j.property.1, ?_, j.property.2.2⟩ le_rfl
  obtain ⟨hc, w, hw, hcard⟩ := j.property.2.1
  exact ⟨hc, w, hw, hcard.trans (by exact_mod_cast hN w)⟩

private theorem isClosed_iInf_ker {E ι : Type*} [AddCommMonoid E] [Module ℂ E]
    [TopologicalSpace E] (f : ι → E →L[ℂ] ℂ) :
    IsClosed (↑(⨅ i, (f i).ker) : Set E) := by
  rw [Submodule.coe_iInf]
  exact isClosed_iInter fun i ↦ (f i).isClosed_ker

/-- Paper: Theorem 7.3.4.1(1), p. 364.
Each stage of the archimedean pole filtration is closed. -/
theorem sLocalGammaFiltration_isClosed (ω : PontryaginDual J₁(S)) (N : depths) :
    IsClosed (sLocalGammaFiltration ω N : Set (fullPV(ω))) := by
  exact isClosed_iInf_ker
    (fun j : ΓIndex(ω, sLocalGammaPoleCutoff (F := F) (S := S) ω N) ↦ ΓCoeff(ω, j))

private theorem meromorphicOrderAt_gamma_lt_zero_iff (u : ℂ) :
    meromorphicOrderAt (fun z : ℂ ↦ Complex.Gamma (z + u)) 0 < 0 ↔ ∃ m : ℕ, u = -(m : ℂ) := by
  have hg : ∀ y, AnalyticAt ℂ (fun x : ℂ ↦ (Complex.Gamma x)⁻¹) y := fun y ↦
    Complex.differentiable_one_div_Gamma.analyticAt y
  have hinv (y : ℂ) : meromorphicOrderAt Complex.Gamma y =
      -meromorphicOrderAt (fun x : ℂ ↦ (Complex.Gamma x)⁻¹) y := by
    have heq : (fun x : ℂ ↦ (Complex.Gamma x)⁻¹)⁻¹ = Complex.Gamma := by
      funext x; simp
    conv_lhs => rw [← heq, meromorphicOrderAt_inv]
  have hcomp : meromorphicOrderAt (fun z : ℂ ↦ Complex.Gamma (z + u)) 0 =
      meromorphicOrderAt Complex.Gamma u := by
    change meromorphicOrderAt (Complex.Gamma ∘ (· + u)) 0 = meromorphicOrderAt Complex.Gamma u
    simpa [zero_add] using meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt
      (f := Complex.Gamma) (x := (0 : ℂ)) (c := u)
  rw [hcomp]
  clear hcomp
  constructor
  · intro hlt
    by_contra hnot
    have hne : (Complex.Gamma u)⁻¹ ≠ 0 := inv_ne_zero (Complex.Gamma_ne_zero fun m ↦ by
      intro hm; exact hnot ⟨m, hm⟩)
    have han : AnalyticAt ℂ Complex.Gamma u :=
      ((hg u).inv hne).congr (Filter.Eventually.of_forall fun x ↦ by simp)
    exact not_lt_of_ge han.meromorphicOrderAt_nonneg hlt
  · rintro ⟨m, rfl⟩
    rw [hinv]
    have hstep (y : ℂ) : meromorphicOrderAt (fun x : ℂ ↦ (Complex.Gamma x)⁻¹) y =
        meromorphicOrderAt (id : ℂ → ℂ) y +
          meromorphicOrderAt (fun x : ℂ ↦ (Complex.Gamma x)⁻¹) (y + 1) := by
      have heq : (fun x : ℂ ↦ (Complex.Gamma x)⁻¹) =
          (id : ℂ → ℂ) * ((fun x : ℂ ↦ (Complex.Gamma x)⁻¹) ∘ (· + 1)) := by
        funext x
        exact Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one x
      have hc : MeromorphicAt ((fun x : ℂ ↦ (Complex.Gamma x)⁻¹) ∘ (· + 1)) y :=
        ((hg (y + 1)).comp (f := fun x : ℂ ↦ x + 1) (by fun_prop)).meromorphicAt
      calc meromorphicOrderAt (fun x : ℂ ↦ (Complex.Gamma x)⁻¹) y
          = meromorphicOrderAt ((id : ℂ → ℂ) *
              ((fun x : ℂ ↦ (Complex.Gamma x)⁻¹) ∘ (· + 1))) y := by rw [← heq]
        _ = _ := by
          rw [meromorphicOrderAt_mul analyticAt_id.meromorphicAt hc,
            meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt]
    have hzero {f : ℂ → ℂ} {y : ℂ} (hf : AnalyticAt ℂ f y) (hy : f y ≠ 0) :
        meromorphicOrderAt f y = 0 := by
      rw [hf.meromorphicOrderAt_eq, analyticOrderAt_eq_zero.mpr (Or.inr hy), ENat.map_zero,
        CharP.cast_eq_zero, WithTop.coe_zero]
    have h1 : meromorphicOrderAt (fun x : ℂ ↦ (Complex.Gamma x)⁻¹) (-(m : ℂ)) = 1 := by
      induction m with
      | zero =>
        rw [hstep, Nat.cast_zero, neg_zero, zero_add, meromorphicOrderAt_id,
          hzero (hg 1) (by simp [Complex.Gamma_one]), add_zero]
      | succ k ih =>
        rw [hstep]
        have hne : -((k + 1 : ℕ) : ℂ) ≠ 0 := by norm_cast
        have h0 : meromorphicOrderAt (id : ℂ → ℂ) (-((k + 1 : ℕ) : ℂ)) = 0 :=
          hzero analyticAt_id hne
        have hadd : -((k + 1 : ℕ) : ℂ) + 1 = -(k : ℂ) := by push_cast; ring
        rw [h0, zero_add, hadd, ih]
    rw [h1]
    decide

private theorem meromorphicOrderAt_gammaR_lt_zero_iff (u : ℂ) :
    meromorphicOrderAt (fun z : ℂ ↦ Complex.Gammaℝ (z + u)) 0 < 0 ↔
      ∃ m : ℕ, u = -(2 * (m : ℂ)) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have heq : (fun z : ℂ ↦ Complex.Gammaℝ (z + u)) =
      (fun z : ℂ ↦ (Real.pi : ℂ) ^ (-(z + u) / 2)) * (fun z : ℂ ↦ Complex.Gamma ((z + u) / 2)) := by
    funext z
    rfl
  have he_an : AnalyticAt ℂ (fun z : ℂ ↦ (Real.pi : ℂ) ^ (-(z + u) / 2)) 0 := by
    have hdiff : Differentiable ℂ (fun z : ℂ ↦ (Real.pi : ℂ) ^ (-(z + u) / 2)) :=
      fun z ↦ (((differentiableAt_id.add (differentiableAt_const u)).neg.div_const 2).const_cpow
        (Or.inl hpi))
    exact hdiff.analyticAt 0
  have he_ne : (Real.pi : ℂ) ^ (-(0 + u) / 2) ≠ 0 := by
    by_cases h0 : -(0 + u) / 2 = 0
    · rw [h0, Complex.cpow_zero]; exact one_ne_zero
    · exact (Complex.cpow_ne_zero_iff_of_exponent_ne_zero h0).mpr hpi
  have he_ord : meromorphicOrderAt (fun z : ℂ ↦ (Real.pi : ℂ) ^ (-(z + u) / 2)) 0 = 0 := by
    have hord : analyticOrderAt (fun z : ℂ ↦ (Real.pi : ℂ) ^ (-(z + u) / 2)) 0 = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr he_ne)
    rw [he_an.meromorphicOrderAt_eq, hord, ENat.map_zero, CharP.cast_eq_zero, WithTop.coe_zero]
  have hG_mer : MeromorphicAt (fun z : ℂ ↦ Complex.Gamma ((z + u) / 2)) 0 := by
    have h1 : AnalyticAt ℂ (fun z : ℂ ↦ (Complex.Gamma ((z + u) / 2))⁻¹) 0 :=
      (Complex.differentiable_one_div_Gamma.analyticAt _).comp (by fun_prop)
    convert h1.meromorphicAt.inv using 1
    funext z; simp
  have hmul : meromorphicOrderAt (fun z : ℂ ↦ Complex.Gammaℝ (z + u)) 0 =
      meromorphicOrderAt (fun z : ℂ ↦ Complex.Gamma ((z + u) / 2)) 0 := by
    rw [heq, meromorphicOrderAt_mul he_an.meromorphicAt hG_mer, he_ord, zero_add]
  have hcomp : meromorphicOrderAt (fun z : ℂ ↦ Complex.Gamma ((z + u) / 2)) 0 =
      meromorphicOrderAt (fun z : ℂ ↦ Complex.Gamma (z + u / 2)) 0 := by
    have h1 : (fun z : ℂ ↦ Complex.Gamma ((z + u) / 2)) =
        (fun w : ℂ ↦ Complex.Gamma (w + u / 2)) ∘ (fun z : ℂ ↦ z / 2) := by
      funext z; simp [add_div]
    rw [h1]
    have hd : deriv (fun z : ℂ ↦ z / 2) 0 ≠ 0 := by
      have : HasDerivAt (fun z : ℂ ↦ z / 2) (1 / 2 : ℂ) 0 := (hasDerivAt_id 0).div_const 2
      rw [this.deriv]
      norm_num
    simpa using meromorphicOrderAt_comp_of_deriv_ne_zero (f := fun w : ℂ ↦ Complex.Gamma (w + u / 2))
      (g := fun z : ℂ ↦ z / 2) (by fun_prop) hd
  rw [hmul, hcomp, meromorphicOrderAt_gamma_lt_zero_iff]
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m, by linear_combination 2 * hm⟩
  · rintro ⟨m, rfl⟩
    exact ⟨m, by ring⟩

private theorem meromorphicOrderAt_gammaC_div_two_lt_zero_iff (u : ℂ) :
    meromorphicOrderAt (fun z : ℂ ↦ Complex.Gammaℂ (z + u) / 2) 0 < 0 ↔
      ∃ m : ℕ, u = -(m : ℂ) := by
  have h2pi : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have heq : (fun z : ℂ ↦ Complex.Gammaℂ (z + u) / 2) =
      (fun z : ℂ ↦ (2 * (Real.pi : ℂ)) ^ (-(z + u))) * (fun z : ℂ ↦ Complex.Gamma (z + u)) := by
    funext z
    change (2 * (2 * (Real.pi : ℂ)) ^ (-(z + u)) * Complex.Gamma (z + u)) / 2 =
      (2 * (Real.pi : ℂ)) ^ (-(z + u)) * Complex.Gamma (z + u)
    ring
  have he_an : AnalyticAt ℂ (fun z : ℂ ↦ (2 * (Real.pi : ℂ)) ^ (-(z + u))) 0 := by
    have hdiff : Differentiable ℂ (fun z : ℂ ↦ (2 * (Real.pi : ℂ)) ^ (-(z + u))) :=
      fun z ↦ ((differentiableAt_id.add (differentiableAt_const u)).neg.const_cpow (Or.inl h2pi))
    exact hdiff.analyticAt 0
  have he_ne : (2 * (Real.pi : ℂ)) ^ (-(0 + u)) ≠ 0 := by
    by_cases h0 : -(0 + u) = 0
    · rw [h0, Complex.cpow_zero]; exact one_ne_zero
    · exact (Complex.cpow_ne_zero_iff_of_exponent_ne_zero h0).mpr h2pi
  have he_ord : meromorphicOrderAt (fun z : ℂ ↦ (2 * (Real.pi : ℂ)) ^ (-(z + u))) 0 = 0 := by
    have hord : analyticOrderAt (fun z : ℂ ↦ (2 * (Real.pi : ℂ)) ^ (-(z + u))) 0 = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr he_ne)
    rw [he_an.meromorphicOrderAt_eq, hord, ENat.map_zero, CharP.cast_eq_zero, WithTop.coe_zero]
  have hG_mer : MeromorphicAt (fun z : ℂ ↦ Complex.Gamma (z + u)) 0 := by
    have h1 : AnalyticAt ℂ (fun z : ℂ ↦ (Complex.Gamma (z + u))⁻¹) 0 :=
      (Complex.differentiable_one_div_Gamma.analyticAt _).comp (by fun_prop)
    convert h1.meromorphicAt.inv using 1
    funext z; simp
  rw [heq, meromorphicOrderAt_mul he_an.meromorphicAt hG_mer, he_ord, zero_add,
    meromorphicOrderAt_gamma_lt_zero_iff]

/-- The selected centers and orders form a finite index set. Along the norm-twist line of a
component each archimedean place has its poles in an arithmetic progression running to the
left, and a cutoff keeps finitely many of them. -/
private theorem sLocalGammaFiltration_coeff_independent_finite (ω : PontryaginDual J₁(S))
    (N : depths) :
    Finite (ΓIndex(ω, sLocalGammaPoleCutoff (F := F) (S := S) ω N)) := by
  let U := sLocalGammaPoleCutoff (F := F) (S := S) ω N
  have hU_fin : U.Finite := by
    by_cases hUne : U.Nonempty
    · obtain ⟨c₀, hc₀⟩ := hUne
      have hc₀_comp : onComponent(c₀, ω) := hc₀.1
      have htw (c : Xₛ) (a z : ℂ) : shift(shift(c, a), z) = shift(c, z + a) := by
        ext1 g
        change c g * _ ^ a * _ ^ z = c g * _ ^ (z + a)
        rw [add_comm, Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr
          (NNReal.coe_ne_zero.mpr (m(S) g).ne_zero)), mul_assoc]
      have hcomp_shift (c : Xₛ) (hc : onComponent(c, ω)) : ∃ s : ℂ, c = shift(c₀, s) := by
        obtain ⟨σ, hσ⟩ := sIdeleQuotientNorm_exists_section F S
        let c₀inv := c₀.comp (ContinuousMonoidHom.inv J(S))
        let P : QuasiCharacter ℝ≥0ˣ := (c * c₀inv).comp σ
        obtain ⟨s, hs⟩ := (existsUnique_complexPower P).exists
        refine ⟨s, ?_⟩
        ext1 g
        let u : J(S) := g * (σ (m(S) g))⁻¹
        have hu_mem : u ∈ J₁(S) := by
          change m(S) (g * (σ (m(S) g))⁻¹) = 1
          rw [map_mul, map_inv, hσ, mul_inv_cancel]
        have hu_eq : c u = c₀ u := DFunLike.congr_fun (hc.trans hc₀_comp.symm) ⟨u, hu_mem⟩
        have hdecomp : g = u * σ (m(S) g) := by simp [u]
        have hcg : c g = c u * c (σ (m(S) g)) := by
          conv_lhs => rw [hdecomp]
          exact map_mul c _ _
        have hc₀g : c₀ g = c₀ u * c₀ (σ (m(S) g)) := by
          conv_lhs => rw [hdecomp]
          exact map_mul c₀ _ _
        have hP : c (σ (m(S) g)) * (c₀ (σ (m(S) g)))⁻¹ =
            (((m(S) g : ℝ≥0) : ℝ) : ℂ) ^ s := by
          have h1 := hs (m(S) g)
          change c (σ (m(S) g)) * c₀ (σ (m(S) g))⁻¹ = _ at h1
          rwa [map_inv] at h1
        have hc₀σ_ne : c₀ (σ (m(S) g)) ≠ 0 :=
          ((Group.isUnit _).map c₀).ne_zero
        change c g = c₀ g * (((m(S) g : ℝ≥0) : ℝ) : ℂ) ^ s
        rw [hcg, hc₀g, hu_eq, ← hP]
        field_simp [hc₀σ_ne]
      have hres_shift (w : InfinitePlace F) (z : ℂ) (g : w.Completionˣ) :
          sLocalInfiniteRestriction w (shift(c₀, z)) g =
            sLocalInfiniteRestriction w c₀ g *
              ((((Units.map nnNormHom.toMonoidHom ^ w.mult : w.Completionˣ →* ℝ≥0ˣ) g : ℝ≥0) : ℝ) : ℂ) ^ z := by
        have h1 := sLocalInfiniteRestriction_normTwist (F := F) (S := S) w z g
        rw [← h1]
        change c₀ _ * _ = c₀ _ * (((1 : Circle) : ℂ) * _)
        rw [Circle.coe_one, one_mul]
        rfl
      have hplace_poles (w : InfinitePlace F) :
          ∃ (a : ℂ) (step : ℝ), 0 < step ∧
            ∀ s : ℂ, w ∈ arch(shift(c₀, s)) ↔
              ∃ m : ℕ, s = -(step * (m : ℝ) : ℂ) - a := by
        by_cases hw : w.IsReal
        · let p := (realLocalEulerParameters w hw (sLocalInfiniteRestriction w c₀)).exists.choose
          have hp := (realLocalEulerParameters w hw (sLocalInfiniteRestriction w c₀)).exists.choose_spec
          have hE (u : ℂ) :
              infiniteLocalEulerFactor w (sLocalInfiniteRestriction w (shift(c₀, u))) =
                Complex.Gammaℝ (u + (p.1 + (p.2.val : ℂ))) := by
            let e := (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm
            have hshape : ∀ x : ℝˣ, sLocalInfiniteRestriction w (shift(c₀, u))
                (Units.map e.toMonoidHom x) =
                  (‖(x : ℝ)‖ : ℂ) ^ (p.1 + u) * (if 0 < (x : ℝ) then 1 else (-1 : ℂ)) ^ p.2.val := by
              intro x
              have hn : ‖(e (x : ℝ) : w.Completion)‖ = ‖(x : ℝ)‖ :=
                (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.isometry.norm_map_of_map_zero
                  (map_zero e) (x : ℝ)
              have hm : (((Units.map nnNormHom.toMonoidHom ^ w.mult : w.Completionˣ →* ℝ≥0ˣ)
                  (Units.map e.toMonoidHom x) : ℝ≥0) : ℝ) = ‖(x : ℝ)‖ := by
                simp [InfinitePlace.mult, hw, hn]
              rw [hres_shift, hp x, hm]
              have hne : (‖(x : ℝ)‖ : ℂ) ≠ 0 :=
                Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr x.ne_zero)
              rw [Complex.cpow_add _ _ hne]
              ring
            have hq := (realLocalEulerParameters w hw (sLocalInfiniteRestriction w (shift(c₀, u)))).unique
              (realLocalEulerParameters w hw (sLocalInfiniteRestriction w (shift(c₀, u)))).exists.choose_spec
              (y₂ := (p.1 + u, p.2)) hshape
            simp only [infiniteLocalEulerFactor, hw, ↓reduceDIte, hq]
            congr 1; ring
          refine ⟨p.1 + (p.2.val : ℂ), 2, two_pos, fun s ↦ ?_⟩
          simp only [sLocalArchPolePlaces, Finset.mem_filter, Finset.mem_univ, true_and]
          have hfun : (fun z : ℂ ↦ infiniteLocalEulerFactor w
              (sLocalInfiniteRestriction w (shift(shift(c₀, s), z)))) =
              fun z : ℂ ↦ Complex.Gammaℝ (z + (s + (p.1 + (p.2.val : ℂ)))) := by
            funext z
            rw [htw, hE]
            congr 1; ring
          rw [hfun, meromorphicOrderAt_gammaR_lt_zero_iff]
          constructor <;> rintro ⟨m, hm⟩ <;> refine ⟨m, ?_⟩
          · push_cast at hm ⊢; linear_combination hm
          · push_cast at hm ⊢; linear_combination hm
        · have hwc : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hw
          let p := (complexLocalEulerParameters w hwc (sLocalInfiniteRestriction w c₀)).exists.choose
          have hp := (complexLocalEulerParameters w hwc (sLocalInfiniteRestriction w c₀)).exists.choose_spec
          have hE (u : ℂ) :
              infiniteLocalEulerFactor w (sLocalInfiniteRestriction w (shift(c₀, u))) =
                Complex.Gammaℂ (u + (p.1 + (p.2.natAbs : ℂ) / 2)) / 2 := by
            let e := (InfinitePlace.Completion.ringEquivComplexOfIsComplex hwc).symm
            have hshape : ∀ x : ℂˣ, sLocalInfiniteRestriction w (shift(c₀, u))
                (Units.map e.toMonoidHom x) =
                  ((‖(x : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ (p.1 + u) * ((x : ℂ) / (‖(x : ℂ)‖ : ℂ)) ^ p.2 := by
              intro x
              have hn : ‖(e (x : ℂ) : w.Completion)‖ = ‖(x : ℂ)‖ :=
                (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hwc).symm.isometry.norm_map_of_map_zero
                  (map_zero e) (x : ℂ)
              have hm : (((Units.map nnNormHom.toMonoidHom ^ w.mult : w.Completionˣ →* ℝ≥0ˣ)
                  (Units.map e.toMonoidHom x) : ℝ≥0) : ℝ) = ‖(x : ℂ)‖ ^ 2 := by
                simp [InfinitePlace.mult, hw, hn]
              rw [hres_shift, hp x, hm]
              have hne : ((‖(x : ℂ)‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
                Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr x.ne_zero))
              rw [Complex.cpow_add _ _ hne]
              ring
            have hq := (complexLocalEulerParameters w hwc (sLocalInfiniteRestriction w (shift(c₀, u)))).unique
              (complexLocalEulerParameters w hwc (sLocalInfiniteRestriction w (shift(c₀, u)))).exists.choose_spec
              (y₂ := (p.1 + u, p.2)) hshape
            simp only [infiniteLocalEulerFactor, hw, ↓reduceDIte, hq]
            congr 2; ring
          refine ⟨p.1 + (p.2.natAbs : ℂ) / 2, 1, one_pos, fun s ↦ ?_⟩
          simp only [sLocalArchPolePlaces, Finset.mem_filter, Finset.mem_univ, true_and]
          have hfun : (fun z : ℂ ↦ infiniteLocalEulerFactor w
              (sLocalInfiniteRestriction w (shift(shift(c₀, s), z)))) =
              fun z : ℂ ↦ Complex.Gammaℂ (z + (s + (p.1 + (p.2.natAbs : ℂ) / 2))) / 2 := by
            funext z
            rw [htw, hE]
            congr 2; ring
          rw [hfun, meromorphicOrderAt_gammaC_div_two_lt_zero_iff]
          constructor <;> rintro ⟨m, hm⟩ <;> refine ⟨m, ?_⟩
          · push_cast at hm ⊢; linear_combination hm
          · push_cast at hm ⊢; linear_combination hm
      have hsub : U ⊆ ⋃ w : InfinitePlace F,
          let h := hplace_poles w
          (fun m : Fin (N w + 1) ↦ shift(c₀, -(h.choose_spec.choose * (m.val : ℝ) : ℂ) - h.choose)) ''
            Set.univ := by
        intro c hc
        obtain ⟨s, rfl⟩ := hcomp_shift c hc.1
        obtain ⟨w, hw, hcard⟩ := hc.2
        refine Set.mem_iUnion.mpr ⟨w, ?_⟩
        have hstep' : 0 < (hplace_poles w).choose_spec.choose :=
          (hplace_poles w).choose_spec.choose_spec.1
        have hiff' := (hplace_poles w).choose_spec.choose_spec.2
        obtain ⟨m, rfl⟩ := (hiff' s).mp hw
        have hm_le : m ≤ N w := by
          let f : Fin m → ℝ := fun k ↦ (hplace_poles w).choose_spec.choose * ((k.val + 1 : ℕ) : ℝ)
          have hfinj : Function.Injective f := by
            intro k₁ k₂ hk
            have h1 : ((k₁.val + 1 : ℕ) : ℝ) = ((k₂.val + 1 : ℕ) : ℝ) :=
              mul_left_cancel₀ hstep'.ne' hk
            have h2 : k₁.val + 1 = k₂.val + 1 := by exact_mod_cast h1
            exact Fin.ext (by omega)
          have hfrange : Set.range f ⊆
              {t : ℝ | 0 < t ∧ w ∈ arch(shift(shift(c₀,
                -((hplace_poles w).choose_spec.choose * (m : ℝ) : ℂ) - (hplace_poles w).choose),
                (t : ℂ)))} := by
            rintro _ ⟨k, rfl⟩
            refine ⟨by positivity, ?_⟩
            rw [htw, hiff']
            refine ⟨m - (k.val + 1), ?_⟩
            have hle : k.val + 1 ≤ m := k.isLt
            dsimp only [f]
            push_cast [Nat.cast_sub hle]
            ring
          have hle_enc : (m : ℕ∞) ≤
              ({t : ℝ | 0 < t ∧ w ∈ arch(shift(shift(c₀,
                -((hplace_poles w).choose_spec.choose * (m : ℝ) : ℂ) - (hplace_poles w).choose),
                (t : ℂ)))} : Set ℝ).encard := by
            calc (m : ℕ∞) = (Set.range f).encard := by
                  rw [← Set.image_univ, hfinj.injOn.encard_image, Set.encard_univ,
                    ENat.card_eq_coe_fintype_card, Fintype.card_fin]
              _ ≤ _ := Set.encard_le_encard hfrange
          exact_mod_cast hle_enc.trans hcard
        exact ⟨⟨m, Nat.lt_succ_of_le hm_le⟩, Set.mem_univ _, rfl⟩
      exact (Set.finite_iUnion fun w ↦ (Set.finite_univ).image _).subset hsub
    · rw [Set.not_nonempty_iff_eq_empty.mp hUne]
      exact Set.finite_empty
  have hι_fin : Finite (ΓIndex(ω, U)) := by
    have : Finite U := hU_fin.to_subtype
    let f : ΓIndex(ω, U) → U × Fin (Fintype.card (InfinitePlace F) + 1) := fun j ↦
      ⟨⟨j.val.1, j.property.2.1⟩,
        ⟨j.val.2, Nat.lt_succ_of_le (j.property.2.2.2.trans (Finset.card_le_univ _))⟩⟩
    have hf : Function.Injective f := by
      intro j₁ j₂ h
      have h1 : j₁.val.1 = j₂.val.1 := congrArg (fun p ↦ p.1.val) h
      have h2 : j₁.val.2 = j₂.val.2 := congrArg (fun p ↦ p.2.val) h
      exact Subtype.ext (Prod.ext h1 h2)
    exact Finite.of_injective f hf
  exact hι_fin

/-- Paper: Theorem 7.3.4.1(2), pp. 364–365.
On each component some principal value attains the full archimedean pole order at every
center: its Laurent coefficient of the top admissible order does not vanish there.
This follows from `exists_sLocalIdelicZFunction_principalValue_attaining_poles` for one unitary
character on the component. Every center of the component is a norm twist of it, the pole
multiplicity at a twist is the number of archimedean pole places (the computation in
`gammaFiltration_principalValue_bound`), and `mem_sLocalThetaPoleBound_iff_leading` gives the
leading coefficient. -/
private theorem sLocalGammaFiltration_coeff_independent_attaining (ω : PontryaginDual J₁(S)) :
    ∃ g : B(S), ∀ c : Xₛ, onComponent(c, ω) → 0 < (arch(c)).card →
      sLocalPrincipalPartCoeff c (arch(c)).card
        (sAdelePrincipalValue F (Finset.Subset.refl S) g) ≠ 0 := by
  classical
  by_cases hne : ∃ c₀ : Xₛ, onComponent(c₀, ω)
  swap
  · exact ⟨0, fun c hc ↦ (hne ⟨c, hc⟩).elim⟩
  obtain ⟨c₀, hc₀⟩ := hne
  obtain ⟨χ, a, ha⟩ := exists_sLocalNormTwist (F := F) (S := S) c₀
  let d : Xₛ := (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ
  obtain ⟨f, hf⟩ := exists_sLocalIdelicZFunction_principalValue_attaining_poles (F := F) (S := S) χ
  refine ⟨f, fun c hc hpos ↦ ?_⟩
  have htw (b : Xₛ) (a z : ℂ) : shift(shift(b, a), z) = shift(b, z + a) := by
    ext1 g
    change b g * _ ^ a * _ ^ z = b g * _ ^ (z + a)
    rw [add_comm, Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr
      (NNReal.coe_ne_zero.mpr (m(S) g).ne_zero)), mul_assoc]
  -- Every quasi-character of the component is a norm twist of `c₀`.
  obtain ⟨s, hs⟩ : ∃ s : ℂ, c = shift(c₀, s) := by
    obtain ⟨σ, hσ⟩ := sIdeleQuotientNorm_exists_section (F := F) (S := S)
    let c₀inv := c₀.comp (ContinuousMonoidHom.inv J(S))
    let P : QuasiCharacter ℝ≥0ˣ := (c * c₀inv).comp σ
    obtain ⟨s, hs⟩ := (existsUnique_complexPower P).exists
    refine ⟨s, ?_⟩
    ext1 g
    let u : J(S) := g * (σ (m(S) g))⁻¹
    have hu_mem : u ∈ J₁(S) := by
      change m(S) (g * (σ (m(S) g))⁻¹) = 1
      rw [map_mul, map_inv, hσ, mul_inv_cancel]
    have hu_eq : c u = c₀ u := DFunLike.congr_fun (hc.trans hc₀.symm) ⟨u, hu_mem⟩
    have hdecomp : g = u * σ (m(S) g) := by simp [u]
    have hcg : c g = c u * c (σ (m(S) g)) := by
      conv_lhs => rw [hdecomp]
      exact map_mul c _ _
    have hc₀g : c₀ g = c₀ u * c₀ (σ (m(S) g)) := by
      conv_lhs => rw [hdecomp]
      exact map_mul c₀ _ _
    have hP : c (σ (m(S) g)) * (c₀ (σ (m(S) g)))⁻¹ = (((m(S) g : ℝ≥0) : ℝ) : ℂ) ^ s := by
      have h1 := hs (m(S) g)
      change c (σ (m(S) g)) * c₀ (σ (m(S) g))⁻¹ = _ at h1
      rwa [map_inv] at h1
    have hc₀σ_ne : c₀ (σ (m(S) g)) ≠ 0 := ((Group.isUnit _).map c₀).ne_zero
    change c g = c₀ g * (((m(S) g : ℝ≥0) : ℝ) : ℂ) ^ s
    rw [hcg, hc₀g, hu_eq, ← hP]
    field_simp [hc₀σ_ne]
  have hct : c = shift(d, s + a) := by rw [hs, ← ha, htw]
  subst hct
  have translate (H : Xₛ → ℂ) :
      meromorphicOrderAt (fun z : ℂ ↦ H (shift(shift(d, s + a), z))) 0 =
        meromorphicOrderAt (fun z : ℂ ↦ H (shift(d, z))) (s + a) := by
    have e : (fun z : ℂ ↦ H (shift(shift(d, s + a), z))) =
        (fun z : ℂ ↦ H (shift(d, z))) ∘ (· + (s + a)) := by
      funext z
      rw [htw]
      rfl
    rw [e, meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt, zero_add]
  have places : (arch(shift(d, s + a))).card = sLocalArchimedeanPoleMultiplicity χ (s + a) := by
    unfold sLocalArchPolePlaces sLocalArchimedeanPoleMultiplicity
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro w _
    rw [translate (fun b ↦ infiniteLocalEulerFactor w (sLocalInfiniteRestriction w b))]
  let p := sAdelePrincipalValue F (Finset.Subset.refl S) f
  have hord : meromorphicOrderAt (fun z ↦ sLocalIdelicZFunction p (shift(shift(d, s + a), z))) 0 =
      ((-((arch(shift(d, s + a))).card : ℤ) : ℤ) : WithTop ℤ) := by
    rw [translate (sLocalIdelicZFunction p), places]
    exact hf (s + a)
  have hZ := sLocalZ_centered p (shift(d, s + a))
  rw [sLocalPrincipalPartCoeff_apply]
  refine mem_sLocalThetaPoleBound_iff_leading hZ.1 hpos ?_
  change (-(meromorphicOrderAt (fun z ↦ sLocalIdelicZFunction p
    (shift(shift(d, s + a), z))) 0).untop₀).toNat = _
  rw [hord]
  simp

/-- Paper: Theorem 7.3.4.1(2), pp. 364–365, and Theorem 7.2.1.1(2), p. 334.
The Laurent coefficients of the principal value of a translated test are an upper triangular
combination of those of the principal value of the test, with powers of the logarithm of the
norm of the translating idele.
This follows as `sLocalPrincipalPartCoeff_translate` does. By
`sLocalIdelicZFunction_principalValue`, applied to the test and to its translate, and
`sLocalPrincipalPartCoeff_translate_zeta`, the zeta function of the principal value of the
translate is the character value times that of the principal value, off a discrete set of each
norm-twist line. Residues only see such germs (`sLocalPrincipalPartCoeff_translate_congr`), and
`sLocalPrincipalPartCoeff_translate_laurent` applies with the pole bound of
`gammaFiltration_principalValue_bound`. -/
private theorem sLocalGammaFiltration_coeff_independent_translate (g : B(S))
    (u : (SAdeleRing F S)ˣ) (c : Xₛ) (k : ℕ) (hk : 0 < k) (hkc : k ≤ (arch(c)).card) :
    sLocalPrincipalPartCoeff c k (sAdelePrincipalValue F (Finset.Subset.refl S)
        (schwartzBruhatUnitTranslate u g)) =
      c (QuotientGroup.mk u : J(S)) * ∑ i ∈ Finset.range ((arch(c)).card - k + 1),
        sLocalPrincipalPartCoeff c (k + i) (sAdelePrincipalValue F (Finset.Subset.refl S) g) *
          ((Real.log (((m(S) (QuotientGroup.mk u : J(S)) : ℝ≥0) : ℝ)) : ℝ) : ℂ) ^ i /
            (i.factorial : ℂ) := by
  classical
  let P := sAdelePrincipalValue F (Finset.Subset.refl S)
  let gu : J(S) := QuotientGroup.mk u
  let L : ℂ := ((Real.log (((m(S) gu : ℝ≥0) : ℝ)) : ℝ) : ℂ)
  have hZ := sLocalZ_centered (P g) c
  have hbound := gammaFiltration_principalValue_bound g c
  have hord : ((-((arch(c)).card : ℤ) : ℤ) : WithTop ℤ) ≤
      meromorphicOrderAt (fun z ↦ sLocalIdelicZFunction (P g) (shift(c, z))) 0 := by
    change (-(meromorphicOrderAt (fun z ↦ sLocalIdelicZFunction (P g) (shift(c, z))) 0).untop₀).toNat
      ≤ _ at hbound
    generalize meromorphicOrderAt (fun z ↦ sLocalIdelicZFunction (P g) (shift(c, z))) 0 = o
      at hbound ⊢
    induction o using WithTop.recTopCoe with
    | top => exact le_top
    | coe n =>
      simp only [WithTop.untop₀_coe] at hbound
      exact WithTop.coe_le_coe.mpr (by omega)
  have hM : (((m(S) gu : ℝ≥0) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (Units.ne_zero _))
  have hval (b : Xₛ) (z : ℂ) : (shift(b, z)) gu = b gu * Complex.exp (L * z) := by
    change b gu * (((m(S) gu : ℝ≥0) : ℝ) : ℂ) ^ z = _
    rw [Complex.cpow_def_of_ne_zero hM, ← Complex.ofReal_log (NNReal.coe_nonneg _)]
  -- The zeta functions of the two principal values differ by the character value at `u`.
  have hgerm : (fun z ↦ sLocalIdelicZFunction (P (schwartzBruhatUnitTranslate u g)) (shift(c, z)))
      =ᶠ[𝓝[≠] (0 : ℂ)]
      fun z ↦ (shift(c, z)) gu * sLocalIdelicZFunction (P g) (shift(c, z)) := by
    obtain ⟨χ, a, hc⟩ := exists_sLocalNormTwist (F := F) (S := S) c
    let d : Xₛ := (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ
    have e (H : Xₛ → ℂ) (z : ℂ) : H (shift(c, z)) = H (shift(d, z + a)) := by
      rw [← hc, normTwist_normTwist]
    have hPV (h : B(S)) := sLocalIdelicZFunction_principalValue (F := F) (S := S) S
      (Finset.Subset.refl S) h χ
    have hcod : (fun s ↦ sLocalIdelicZFunction (P (schwartzBruhatUnitTranslate u g)) (shift(d, s)))
        =ᶠ[codiscrete ℂ] fun s ↦ (shift(d, s)) gu * sLocalIdelicZFunction (P g) (shift(d, s)) := by
      filter_upwards [hPV (schwartzBruhatUnitTranslate u g), hPV g] with s h1 h2
      dsimp only at h1 h2
      change sLocalIdelicZFunction (P (schwartzBruhatUnitTranslate u g)) (shift(d, s)) = _
      erw [h1, h2, sLocalPrincipalPartCoeff_translate_zeta, mul_div_assoc]
    have hT : Tendsto (fun z : ℂ ↦ z + a) (𝓝[≠] 0) (𝓝[≠] a) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_nhdsWithin_of_tendsto_nhds ?_, ?_⟩
      · simpa using (Continuous.tendsto (f := fun z : ℂ ↦ z + a) (by fun_prop) 0)
      · filter_upwards [self_mem_nhdsWithin] with z hz
        simpa using hz
    filter_upwards [(eventuallyEq_codiscrete_iff_forall_eventuallyEq_nhdsNE.mp hcod a).comp_tendsto hT]
      with z hz
    simp only [Function.comp_apply] at hz
    rw [e (sLocalIdelicZFunction (P (schwartzBruhatUnitTranslate u g))) z,
      e (sLocalIdelicZFunction (P g)) z, e (fun b ↦ b gu) z, hz]
  rw [sLocalPrincipalPartCoeff_apply]
  change complexResidue (fun z ↦ sLocalIdelicZFunction (P (schwartzBruhatUnitTranslate u g))
    (shift(c, z)) / z ^ (-(k : ℤ) + 1)) 0 = _
  rw [sLocalPrincipalPartCoeff_translate_congr (h := fun z ↦ c gu * (Complex.exp (L * z) *
    sLocalIdelicZFunction (P g) (shift(c, z)) / z ^ (-(k : ℤ) + 1))) ?_]
  · rw [sLocalPrincipalPartCoeff_translate_laurent hZ.1 hkc hord]
    rfl
  · filter_upwards [hgerm] with z hz
    rw [hz, hval]
    ring

/-- Paper: Theorem 7.3.4.1(2), pp. 364–365.
There is a family of S-ideles indexed by the logarithm of their norm on which every
quasi-character is an exponential, and the exponents separate the quasi-characters of one
component.
This follows from a continuous section of the norm (`sIdeleQuotientNorm_exists_section`),
lifted to S-ideles at the points `exp t`: a quasi-character composed with the section is a
complex power (`existsUnique_complexPower`), and two quasi-characters of one component which
agree on the section agree everywhere, since every class is a norm-one class times a value of
the section. -/
private theorem sLocalGammaFiltration_coeff_independent_section :
    ∃ (u : ℝ → (SAdeleRing F S)ˣ) (s : Xₛ → ℂ),
      (∀ t : ℝ, Real.log (((m(S) (QuotientGroup.mk (u t) : J(S)) : ℝ≥0) : ℝ)) = t) ∧
      (∀ (c : Xₛ) (t : ℝ), c (QuotientGroup.mk (u t) : J(S)) = Complex.exp (s c * t)) ∧
      ∀ (ω : PontryaginDual J₁(S)) (c c' : Xₛ), onComponent(c, ω) → onComponent(c', ω) →
        s c = s c' → c = c' := by
  classical
  obtain ⟨σ, hσ⟩ := sIdeleQuotientNorm_exists_section (F := F) (S := S)
  let E (t : ℝ) : ℝ≥0ˣ := Units.mk0 (Real.exp t).toNNReal (Real.toNNReal_pos.mpr (Real.exp_pos t)).ne'
  have hE (t : ℝ) : (((E t : ℝ≥0ˣ) : ℝ≥0) : ℝ) = Real.exp t := Real.coe_toNNReal _ (Real.exp_pos t).le
  choose u hu using fun t ↦ QuotientGroup.mk_surjective (σ (E t))
  let s (c : Xₛ) : ℂ := (existsUnique_complexPower (c.comp σ)).exists.choose
  have hs (c : Xₛ) (x : ℝ≥0ˣ) : c (σ x) = (((x : ℝ≥0) : ℝ) : ℂ) ^ s c :=
    (existsUnique_complexPower (c.comp σ)).exists.choose_spec x
  refine ⟨u, s, fun t ↦ ?_, fun c t ↦ ?_, fun ω c c' hc hc' hcc ↦ ?_⟩
  · rw [hu, hσ (E t), hE, Real.log_exp]
  · rw [hu, hs, hE, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos t).ne'),
      ← Complex.ofReal_log (Real.exp_pos t).le, Real.log_exp, mul_comm]
  · have hk (k : J(S)) (hk : k ∈ J₁(S)) : c k = c' k :=
      DFunLike.congr_fun (hc.trans hc'.symm) ⟨k, hk⟩
    have hsec (x : ℝ≥0ˣ) : c (σ x) = c' (σ x) := by rw [hs, hs, hcc]
    ext g
    have hg : g * (σ (m(S) g))⁻¹ ∈ J₁(S) := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hσ, mul_inv_cancel]
    have hsplit : g = g * (σ (m(S) g))⁻¹ * σ (m(S) g) := by group
    calc c g = c (g * (σ (m(S) g))⁻¹) * c (σ (m(S) g)) := by rw [← map_mul, ← hsplit]
      _ = c' (g * (σ (m(S) g))⁻¹) * c' (σ (m(S) g)) := by rw [hk _ hg, hsec]
      _ = c' g := by rw [← map_mul, ← hsplit]

-- TODO(paper-gap): The test list (7.3.4.9) does not separate the two coefficients
-- of a double real pole at cutoff (0,0). See ERRATA I169. Finite interpolation can
-- use translations of a test attaining the full pole order.

/-- Paper: Theorem 7.3.4.1(2), pp. 364–365.
The Laurent coefficients at the selected centers form a finite linearly independent family. -/
theorem sLocalGammaFiltration_coeff_independent (ω : PontryaginDual J₁(S)) (N : depths) :
    let U := sLocalGammaPoleCutoff (F := F) (S := S) ω N
    Finite (ΓIndex(ω, U)) ∧ LinearIndependent ℂ (fun j : ΓIndex(ω, U) ↦ ΓCoeff(ω, j)) := by
  intro U
  have hfin : Finite (ΓIndex(ω, U)) := sLocalGammaFiltration_coeff_independent_finite ω N
  refine ⟨hfin, ?_⟩
  classical
  let := Fintype.ofFinite (ΓIndex(ω, U))
  obtain ⟨g₀, hg₀⟩ := sLocalGammaFiltration_coeff_independent_attaining (F := F) (S := S) ω
  obtain ⟨u, s, hnorm, hchar, hsinj⟩ :=
    sLocalGammaFiltration_coeff_independent_section (F := F) (S := S)
  rw [Fintype.linearIndependent_iff]
  intro a ha j₀
  let x (t : ℝ) : fullPV(ω) :=
    ⟨PV((Finset.Subset.refl S), ω) (q(S, ω) (schwartzBruhatUnitTranslate (u t) g₀)),
      LinearMap.mem_range_self _ _⟩
  refine expPolynomial_translate_coeff_eq_zero (Finset.univ : Finset (ΓIndex(ω, U)))
    (fun j ↦ j.val.1) (fun j ↦ j.val.2) s (fun c ↦ (arch(c)).card)
    (fun c m ↦ sLocalPrincipalPartCoeff c m (sAdelePrincipalValue F (Finset.Subset.refl S) g₀))
    a ?_ ?_ ?_ ?_ ?_ ?_ j₀ (Finset.mem_univ _)
  · intro j _ j' _ h1 h2
    exact Subtype.ext (Prod.ext h1 h2)
  · intro j _ j' _ h
    exact hsinj ω _ _ j.property.1 j'.property.1 h
  · intro j _
    exact j.property.2.2.2
  · intro j _
    exact hg₀ j.val.1 j.property.1 (lt_of_lt_of_le j.property.2.2.1 j.property.2.2.2)
  · intro c m hm
    by_contra hne
    have hle := (sLocalPrincipalPartCoeff_ne_zero_imp_pole c m (Nat.zero_lt_of_lt hm) _ hne).2
    exact absurd (hle.trans (gammaFiltration_principalValue_bound g₀ c)) (not_le.mpr hm)
  · intro t
    have hat := congrArg (fun φ : StrongDual ℂ (fullPV(ω)) ↦ φ (x t)) ha
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      ContinuousLinearMap.zero_apply] at hat
    refine Eq.trans (Finset.sum_congr rfl fun j _ ↦ congrArg (a j * ·) ?_) hat
    have h2 := sLocalGammaFiltration_coeff_independent_translate (F := F) (S := S) g₀ (u t)
      j.val.1 j.val.2 j.property.2.2.1 j.property.2.2.2
    rw [hchar, hnorm] at h2
    exact h2.symm

private theorem dual_range_mkQL_eq_span_of_finite {E ι : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℂ E] [Finite ι] (φ : ι → StrongDual ℂ E) :
    let stage : Submodule ℂ E := ⨅ j : ι, (φ j).ker
    Set.range (fun ℓ : StrongDual ℂ (E ⧸ stage) ↦ ℓ.comp stage.mkQL) =
      (Submodule.span ℂ (Set.range φ) : Set (StrongDual ℂ E)) := by
  intro stage
  classical
  let : Fintype ι := Fintype.ofFinite ι
  ext ψ
  constructor
  · rintro ⟨ℓ, rfl⟩
    let T : E →ₗ[ℂ] (ι → ℂ) := LinearMap.pi (fun j ↦ (φ j).toLinearMap)
    have hker : T.ker ≤ (ℓ.comp stage.mkQL).toLinearMap.ker := by
      intro x hx
      have hx' : x ∈ stage := by
        rw [Submodule.mem_iInf]
        intro j
        exact congrFun hx j
      change ℓ (stage.mkQ x) = 0
      rw [stage.mkQ_apply, (Submodule.Quotient.mk_eq_zero stage).mpr hx', map_zero]
    let f₀ : T.range →ₗ[ℂ] ℂ :=
      (Submodule.liftQ T.ker (ℓ.comp stage.mkQL).toLinearMap hker).comp
        T.quotKerEquivRange.symm.toLinearMap
    obtain ⟨g, hg⟩ := LinearMap.exists_extend f₀
    have hsum : ℓ.comp stage.mkQL = ∑ j : ι, g (Pi.single j 1) • φ j := by
      ext x
      have hTx : T x = ∑ j : ι, (φ j x) • Pi.single j (1 : ℂ) := by
        ext k
        simp [T, Finset.sum_apply, Pi.single_apply]
      have h1 : (ℓ.comp stage.mkQL) x = g (T x) := by
        have := congrArg (fun h : T.range →ₗ[ℂ] ℂ ↦ h ⟨T x, LinearMap.mem_range_self T x⟩) hg
        simpa [f₀, LinearEquiv.symm_apply_apply] using this.symm
      rw [h1, hTx, map_sum]
      simp [smul_eq_mul, mul_comm]
    change ℓ.comp stage.mkQL ∈ Submodule.span ℂ (Set.range φ)
    rw [hsum]
    exact Submodule.sum_mem _ fun j _ ↦
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · intro hψ
    have hker : stage ≤ ψ.toLinearMap.ker := by
      refine Submodule.span_induction
        (p := fun (ψ' : StrongDual ℂ E) _ ↦ stage ≤ ψ'.toLinearMap.ker)
        ?_ ?_ ?_ ?_ hψ
      · rintro _ ⟨j, rfl⟩ x hx
        rw [Submodule.mem_iInf] at hx
        exact hx j
      · intro x _; simp
      · intro a b _ _ ha hb x hx
        have ha' : a x = 0 := ha hx
        have hb' : b x = 0 := hb hx
        change a x + b x = 0
        rw [ha', hb', add_zero]
      · intro c a _ ha x hx
        have ha' : a x = 0 := ha hx
        change c * a x = 0
        rw [ha', mul_zero]
    let ℓ_lin : (E ⧸ stage) →ₗ[ℂ] ℂ := stage.liftQ ψ.toLinearMap hker
    have hcont : Continuous ℓ_lin := by
      have hq : Topology.IsQuotientMap (stage.mkQ : E → E ⧸ stage) :=
        QuotientAddGroup.isQuotientMap_mk _
      rw [hq.continuous_iff]
      exact ψ.continuous
    refine ⟨⟨ℓ_lin, hcont⟩, ?_⟩
    ext x
    rfl

/-- Paper: Theorem 7.3.4.1(2), p. 365.
The transposes of the linear functionals on the filtered quotient are precisely the
span of the selected Laurent coefficients on the principal-value space.
Deviation: The displayed positive order k in (7.3.4.4) selects Laurent exponent −k. -/
theorem sLocalGammaFiltration_dual_span (ω : PontryaginDual J₁(S)) (N : depths) :
    let stage := sLocalGammaFiltration (F := F) (S := S) ω N
    Set.range (fun ℓ : StrongDual ℂ ((fullPV(ω)) ⧸ stage) ↦ ℓ.comp stage.mkQL) =
      (Submodule.span ℂ (Set.range (fun j : ΓIndex(ω, sLocalGammaPoleCutoff (F := F) (S := S) ω N) ↦
        ΓCoeff(ω, j))) : Set (StrongDual ℂ (fullPV(ω)))) := by
  let U := sLocalGammaPoleCutoff (F := F) (S := S) ω N
  have hι_fin : Finite (ΓIndex(ω, U)) := sLocalGammaFiltration_coeff_independent_finite ω N
  exact @dual_range_mkQL_eq_span_of_finite _ _ _ _ _ _ _ hι_fin
    (fun j : ΓIndex(ω, U) ↦ ΓCoeff(ω, j))

/-- Along the norm-twist line through a quasi-character, an archimedean place has its
poles at an arithmetic progression running to the left. -/
private theorem sLocalGammaFiltration_iInf_placePoles (c₀ : Xₛ) (w : InfinitePlace F) :
    ∃ (a : ℂ) (step : ℝ), 0 < step ∧
      ∀ s : ℂ, w ∈ arch(shift(c₀, s)) ↔ ∃ m : ℕ, s = -(step * (m : ℝ) : ℂ) - a := by
  have htw (c : Xₛ) (a z : ℂ) : shift(shift(c, a), z) = shift(c, z + a) := by
    ext1 g
    change c g * _ ^ a * _ ^ z = c g * _ ^ (z + a)
    rw [add_comm, Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr
      (NNReal.coe_ne_zero.mpr (m(S) g).ne_zero)), mul_assoc]
  have hres_shift (z : ℂ) (g : w.Completionˣ) :
      sLocalInfiniteRestriction w (shift(c₀, z)) g =
        sLocalInfiniteRestriction w c₀ g *
          ((((Units.map nnNormHom.toMonoidHom ^ w.mult : w.Completionˣ →* ℝ≥0ˣ) g : ℝ≥0) : ℝ) : ℂ) ^ z := by
    have h1 := sLocalInfiniteRestriction_normTwist (F := F) (S := S) w z g
    rw [← h1]
    change c₀ _ * _ = c₀ _ * (((1 : Circle) : ℂ) * _)
    rw [Circle.coe_one, one_mul]
    rfl
  by_cases hw : w.IsReal
  · let p := (realLocalEulerParameters w hw (sLocalInfiniteRestriction w c₀)).exists.choose
    have hp := (realLocalEulerParameters w hw (sLocalInfiniteRestriction w c₀)).exists.choose_spec
    have hE (u : ℂ) :
        infiniteLocalEulerFactor w (sLocalInfiniteRestriction w (shift(c₀, u))) =
          Complex.Gammaℝ (u + (p.1 + (p.2.val : ℂ))) := by
      let e := (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm
      have hshape : ∀ x : ℝˣ, sLocalInfiniteRestriction w (shift(c₀, u))
          (Units.map e.toMonoidHom x) =
            (‖(x : ℝ)‖ : ℂ) ^ (p.1 + u) * (if 0 < (x : ℝ) then 1 else (-1 : ℂ)) ^ p.2.val := by
        intro x
        have hn : ‖(e (x : ℝ) : w.Completion)‖ = ‖(x : ℝ)‖ :=
          (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.isometry.norm_map_of_map_zero
            (map_zero e) (x : ℝ)
        have hm : (((Units.map nnNormHom.toMonoidHom ^ w.mult : w.Completionˣ →* ℝ≥0ˣ)
            (Units.map e.toMonoidHom x) : ℝ≥0) : ℝ) = ‖(x : ℝ)‖ := by
          simp [InfinitePlace.mult, hw, hn]
        rw [hres_shift, hp x, hm]
        have hne : (‖(x : ℝ)‖ : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr x.ne_zero)
        rw [Complex.cpow_add _ _ hne]
        ring
      have hq := (realLocalEulerParameters w hw (sLocalInfiniteRestriction w (shift(c₀, u)))).unique
        (realLocalEulerParameters w hw (sLocalInfiniteRestriction w (shift(c₀, u)))).exists.choose_spec
        (y₂ := (p.1 + u, p.2)) hshape
      simp only [infiniteLocalEulerFactor, hw, ↓reduceDIte, hq]
      congr 1; ring
    refine ⟨p.1 + (p.2.val : ℂ), 2, two_pos, fun s ↦ ?_⟩
    simp only [sLocalArchPolePlaces, Finset.mem_filter, Finset.mem_univ, true_and]
    have hfun : (fun z : ℂ ↦ infiniteLocalEulerFactor w
        (sLocalInfiniteRestriction w (shift(shift(c₀, s), z)))) =
        fun z : ℂ ↦ Complex.Gammaℝ (z + (s + (p.1 + (p.2.val : ℂ)))) := by
      funext z
      rw [htw, hE]
      congr 1; ring
    rw [hfun, meromorphicOrderAt_gammaR_lt_zero_iff]
    constructor <;> rintro ⟨m, hm⟩ <;> refine ⟨m, ?_⟩
    · push_cast at hm ⊢; linear_combination hm
    · push_cast at hm ⊢; linear_combination hm
  · have hwc : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hw
    let p := (complexLocalEulerParameters w hwc (sLocalInfiniteRestriction w c₀)).exists.choose
    have hp := (complexLocalEulerParameters w hwc (sLocalInfiniteRestriction w c₀)).exists.choose_spec
    have hE (u : ℂ) :
        infiniteLocalEulerFactor w (sLocalInfiniteRestriction w (shift(c₀, u))) =
          Complex.Gammaℂ (u + (p.1 + (p.2.natAbs : ℂ) / 2)) / 2 := by
      let e := (InfinitePlace.Completion.ringEquivComplexOfIsComplex hwc).symm
      have hshape : ∀ x : ℂˣ, sLocalInfiniteRestriction w (shift(c₀, u))
          (Units.map e.toMonoidHom x) =
            ((‖(x : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ (p.1 + u) * ((x : ℂ) / (‖(x : ℂ)‖ : ℂ)) ^ p.2 := by
        intro x
        have hn : ‖(e (x : ℂ) : w.Completion)‖ = ‖(x : ℂ)‖ :=
          (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hwc).symm.isometry.norm_map_of_map_zero
            (map_zero e) (x : ℂ)
        have hm : (((Units.map nnNormHom.toMonoidHom ^ w.mult : w.Completionˣ →* ℝ≥0ˣ)
            (Units.map e.toMonoidHom x) : ℝ≥0) : ℝ) = ‖(x : ℂ)‖ ^ 2 := by
          simp [InfinitePlace.mult, hw, hn]
        rw [hres_shift, hp x, hm]
        have hne : ((‖(x : ℂ)‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr x.ne_zero))
        rw [Complex.cpow_add _ _ hne]
        ring
      have hq := (complexLocalEulerParameters w hwc (sLocalInfiniteRestriction w (shift(c₀, u)))).unique
        (complexLocalEulerParameters w hwc (sLocalInfiniteRestriction w (shift(c₀, u)))).exists.choose_spec
        (y₂ := (p.1 + u, p.2)) hshape
      simp only [infiniteLocalEulerFactor, hw, ↓reduceDIte, hq]
      congr 2; ring
    refine ⟨p.1 + (p.2.natAbs : ℂ) / 2, 1, one_pos, fun s ↦ ?_⟩
    simp only [sLocalArchPolePlaces, Finset.mem_filter, Finset.mem_univ, true_and]
    have hfun : (fun z : ℂ ↦ infiniteLocalEulerFactor w
        (sLocalInfiniteRestriction w (shift(shift(c₀, s), z)))) =
        fun z : ℂ ↦ Complex.Gammaℂ (z + (s + (p.1 + (p.2.natAbs : ℂ) / 2))) / 2 := by
      funext z
      rw [htw, hE]
      congr 2; ring
    rw [hfun, meromorphicOrderAt_gammaC_div_two_lt_zero_iff]
    constructor <;> rintro ⟨m, hm⟩ <;> refine ⟨m, ?_⟩
    · push_cast at hm ⊢; linear_combination hm
    · push_cast at hm ⊢; linear_combination hm

/-- An archimedean place has only finitely many poles to the right of a quasi-character
along its norm-twist line. -/
private theorem sLocalGammaFiltration_iInf_finite (c : Xₛ) (w : InfinitePlace F) :
    ({t : ℝ | 0 < t ∧ w ∈ arch(shift(c, (t : ℂ)))} : Set ℝ).Finite := by
  obtain ⟨a, step, hstep, hiff⟩ := sLocalGammaFiltration_iInf_placePoles c w
  obtain ⟨M, hM⟩ := exists_nat_gt (-a.re / step)
  refine ((Set.finite_lt_nat M).image fun m : ℕ ↦ -(step * (m : ℝ)) - a.re).subset ?_
  rintro t ⟨ht, hw⟩
  obtain ⟨m, hm⟩ := (hiff _).mp hw
  have hre : t = -(step * (m : ℝ)) - a.re := by
    have := congrArg Complex.re hm
    simpa using this
  refine ⟨m, ?_, hre.symm⟩
  have h1 : step * (m : ℝ) < -a.re := by linarith
  have h2 : (m : ℝ) < -a.re / step := by rwa [lt_div_iff₀ hstep, mul_comm]
  exact_mod_cast h2.trans hM

/-- Every quasi-character with an archimedean pole on the component lies in some cutoff. -/
private theorem sLocalGammaFiltration_iInf_mem_cutoff (ω : PontryaginDual J₁(S)) (c : Xₛ)
    (hc : onComponent(c, ω)) (hne : (arch(c)).Nonempty) :
    ∃ N : depths, c ∈ sLocalGammaPoleCutoff (F := F) (S := S) ω N := by
  obtain ⟨w, hw⟩ := hne
  refine ⟨fun w' ↦ (sLocalGammaFiltration_iInf_finite c w').toFinset.card, hc, w, hw, ?_⟩
  rw [Set.Finite.encard_eq_coe_toFinset_card (sLocalGammaFiltration_iInf_finite c w)]

/-- After the finite principal values, the pole order on a component is bounded by the
number of archimedean places with a pole there. -/
private theorem sLocalGammaFiltration_iInf_bound (g : B(S)) (c : Xₛ) :
    sLocalPolarMultiplicity (sAdelePrincipalValue F (Finset.Subset.refl S) g) c ≤
      (arch(c)).card := by
  obtain ⟨χ, s, rfl⟩ := exists_sLocalNormTwist (F := F) (S := S) c
  have hb := sLocalIdelicZFunction_principalValue_pole_bound (F := F) (S := S) g χ s
  let ch := quasiCharacterNormTwist (m(S)) (isProperMap_sIdeleQuotientNorm F S).continuous
    ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ)
  have hcomp (G : Xₛ → ℂ) : meromorphicOrderAt (fun z ↦ G (shift(ch s, z))) 0 =
      meromorphicOrderAt (fun z ↦ G (ch z)) s := by
    have htw (z : ℂ) : shift(ch s, z) = ch (z + s) := normTwist_normTwist _ _ _ s z
    simp only [htw]
    rw [meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt (f := fun z ↦ G (ch z)),
      zero_add]
  have hcard : (arch(ch s)).card = sLocalArchimedeanPoleMultiplicity χ s := by
    unfold sLocalArchPolePlaces sLocalArchimedeanPoleMultiplicity
    congr 1
    refine Finset.filter_congr fun w _ ↦ ?_
    rw [hcomp (fun c ↦ infiniteLocalEulerFactor w (sLocalInfiniteRestriction w c))]
  rw [hcard]
  unfold sLocalPolarMultiplicity
  rw [hcomp (sLocalIdelicZFunction (sAdelePrincipalValue F (Finset.Subset.refl S) g))]
  generalize meromorphicOrderAt (fun z ↦ sLocalIdelicZFunction
    (sAdelePrincipalValue F (Finset.Subset.refl S) g) (ch z)) s = o at hb ⊢
  induction o using WithTop.recTopCoe with
  | top => simp
  | coe n =>
    have hn : -(sLocalArchimedeanPoleMultiplicity χ s : ℤ) ≤ n := WithTop.coe_le_coe.mp hb
    simp only [WithTop.untop₀_coe]
    omega

/-- Paper: Theorem 7.3.4.1(3), p. 365.
The intersection of all stages is the entire-Mellin subspace. -/
theorem sLocalGammaFiltration_iInf (ω : PontryaginDual J₁(S)) :
    (⨅ N : depths, sLocalGammaFiltration ω N) = Γker(ω) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y, hy⟩ := x.property
    obtain ⟨g, rfl⟩ := Submodule.mkQ_surjective _ y
    let f := sAdelePrincipalValue F (Finset.Subset.refl S) g
    have hf : q(S, ω) f = x.val := hy
    rw [mem_sLocalGammaEntireSubmodule ω x f hf]
    intro c hc
    rw [← sLocalPolarMultiplicity_eq_zero_iff]
    by_contra hne
    have hN : 0 < sLocalPolarMultiplicity f c := Nat.pos_of_ne_zero hne
    have hbound : sLocalPolarMultiplicity f c ≤ (arch(c)).card :=
      sLocalGammaFiltration_iInf_bound g c
    obtain ⟨N, hcN⟩ := sLocalGammaFiltration_iInf_mem_cutoff ω c hc
      (Finset.card_pos.mp (hN.trans_le hbound))
    have hx' := (Submodule.mem_iInf _).mp hx N
    have h0 := (Submodule.mem_iInf _).mp hx'
      ⟨(c, sLocalPolarMultiplicity f c), hc, hcN, hN, hbound⟩
    change sLocalThetaPrincipalPartCoeff ω c hc (sLocalPolarMultiplicity f c) x.val = 0 at h0
    rw [← hf] at h0
    exact mem_sLocalThetaPoleBound_iff_leading (sLocalZ_centered f c).1 hN rfl h0
  · intro x hx
    obtain ⟨y, hy⟩ := x.property
    obtain ⟨g, rfl⟩ := Submodule.mkQ_surjective _ y
    let f := sAdelePrincipalValue F (Finset.Subset.refl S) g
    have hf : q(S, ω) f = x.val := hy
    have hent := (mem_sLocalGammaEntireSubmodule ω x f hf).mp hx
    refine (Submodule.mem_iInf _).mpr fun N ↦ (Submodule.mem_iInf _).mpr fun j ↦ ?_
    change sLocalThetaPrincipalPartCoeff ω j.val.1 j.property.1 j.val.2 x.val = 0
    rw [← hf]
    change sLocalZLaurentCoeff f j.val.1 (-(j.val.2 : ℤ)) = 0
    have hZ := (sLocalZ_centered f j.val.1).1
    have ha := hZ.meromorphicOrderAt_nonneg_iff_analyticAt_toMeromorphicNFAt.1
      (hent j.val.1 j.property.1)
    have he : (fun z ↦ sLocalIdelicZFunction f (shift(j.val.1, z)) /
        z ^ (-(j.val.2 : ℤ) + 1)) =ᶠ[𝓝[≠] (0 : ℂ)]
        (fun z ↦ z ^ j.val.2 * toMeromorphicNFAt
          (fun z ↦ sLocalIdelicZFunction f (shift(j.val.1, z))) 0 z / (z - 0)) := by
      filter_upwards [hZ.eq_nhdsNE_toMeromorphicNFAt, self_mem_nhdsWithin] with z hz hz0
      have hz0' : z ≠ 0 := hz0
      rw [hz, sub_zero, zpow_add₀ hz0', zpow_one, zpow_neg, zpow_natCast]
      field_simp
    change complexResidue (fun z ↦ sLocalIdelicZFunction f (shift(j.val.1, z)) /
        z ^ (-(j.val.2 : ℤ) + 1)) 0 = 0
    have hg : AnalyticAt ℂ (fun z ↦ z ^ j.val.2 * toMeromorphicNFAt
        (fun z ↦ sLocalIdelicZFunction f (shift(j.val.1, z))) 0 z) 0 :=
      (analyticAt_id.pow _).mul ha
    rw [mem_sLocalThetaPoleBound_iff_residue_congr he, complexResidue_div_sub hg]
    simp [zero_pow j.property.2.2.1.ne']

/-- Every unitary character of the norm-one group is the restriction of a quasi-character. -/
private theorem sLocalGammaOrbitalQuotient_coeff_exists (ω : PontryaginDual J₁(S)) :
    ∃ c₀ : Xₛ, onComponent(c₀, ω) := by
  let : LocallyCompactSpace (SAdeleRing F S)ˣ := (sIdeleGroup_description F S).2.2.1
  have := isClosed_sProjectedDiagonal (F := F) (S := S)
  obtain ⟨σ, hσ⟩ := sIdeleQuotientNorm_exists_section F S
  obtain ⟨t, ht⟩ := exists_ne (1 : ℝ≥0ˣ)
  have hr := range_normOneRestriction (m(S)) (isProperMap_sIdeleQuotientNorm F S)
    ⟨σ t, (hσ t).trans_ne ht⟩
  obtain ⟨c₀, hc₀⟩ : (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp ω ∈
      Set.range (normOneRestriction (m(S))) := hr ▸ ⟨ω, rfl⟩
  exact ⟨c₀, hc₀⟩

/-- A norm twist stays on the component of the quasi-character it twists. -/
private theorem sLocalGammaOrbitalQuotient_coeff_onComponent (ω : PontryaginDual J₁(S)) (c₀ : Xₛ)
    (h₀ : onComponent(c₀, ω)) (s : ℂ) : onComponent(shift(c₀, s), ω) := by
  refine Eq.trans ?_ h₀
  ext u
  change c₀ u.val * (((m(S) u.val : ℝ≥0) : ℝ) : ℂ) ^ s = c₀ u.val
  rw [u.prop]
  simp

/-- Two quasi-characters on one component differ by a norm twist. -/
private theorem sLocalGammaOrbitalQuotient_coeff_shift (ω : PontryaginDual J₁(S)) (c₀ c : Xₛ)
    (h₀ : onComponent(c₀, ω)) (hc : onComponent(c, ω)) : ∃ s : ℂ, c = shift(c₀, s) := by
  obtain ⟨σ, hσ⟩ := sIdeleQuotientNorm_exists_section F S
  let c₀inv := c₀.comp (ContinuousMonoidHom.inv J(S))
  let P : QuasiCharacter ℝ≥0ˣ := (c * c₀inv).comp σ
  obtain ⟨s, hs⟩ := (existsUnique_complexPower P).exists
  refine ⟨s, ?_⟩
  ext1 g
  let u : J(S) := g * (σ (m(S) g))⁻¹
  have hu_mem : u ∈ J₁(S) := by
    change m(S) (g * (σ (m(S) g))⁻¹) = 1
    rw [map_mul, map_inv, hσ, mul_inv_cancel]
  have hu_eq : c u = c₀ u := DFunLike.congr_fun (hc.trans h₀.symm) ⟨u, hu_mem⟩
  have hdecomp : g = u * σ (m(S) g) := by simp [u]
  have hcg : c g = c u * c (σ (m(S) g)) := by
    conv_lhs => rw [hdecomp]
    exact map_mul c _ _
  have hc₀g : c₀ g = c₀ u * c₀ (σ (m(S) g)) := by
    conv_lhs => rw [hdecomp]
    exact map_mul c₀ _ _
  have hP : c (σ (m(S) g)) * (c₀ (σ (m(S) g)))⁻¹ =
      (((m(S) g : ℝ≥0) : ℝ) : ℂ) ^ s := by
    have h1 := hs (m(S) g)
    change c (σ (m(S) g)) * c₀ (σ (m(S) g))⁻¹ = _ at h1
    rwa [map_inv] at h1
  have hc₀σ_ne : c₀ (σ (m(S) g)) ≠ 0 :=
    ((Group.isUnit _).map c₀).ne_zero
  change c g = c₀ g * (((m(S) g : ℝ≥0) : ℝ) : ℂ) ^ s
  rw [hcg, hc₀g, hu_eq, ← hP]
  field_simp [hc₀σ_ne]

/-- The pairs of an archimedean center on the component and an admissible Laurent order
form a countable set. -/
private theorem sLocalGammaOrbitalQuotient_coeff_countable (ω : PontryaginDual J₁(S)) :
    Countable (ΓIndex(ω, (Set.univ : Set Xₛ))) := by
  obtain ⟨c₀, h₀⟩ := sLocalGammaOrbitalQuotient_coeff_exists ω
  let P (w : InfinitePlace F) := sLocalGammaFiltration_iInf_placePoles c₀ w
  let pole (w : InfinitePlace F) (m : ℕ) : Xₛ :=
    shift(c₀, -((P w).choose_spec.choose * (m : ℝ) : ℂ) - (P w).choose)
  let U := ⋃ w : InfinitePlace F, Set.range (pole w)
  have hU : U.Countable := Set.countable_iUnion fun w ↦ Set.countable_range _
  have hmem (j : ΓIndex(ω, (Set.univ : Set Xₛ))) : j.val.1 ∈ U := by
    obtain ⟨s, hs⟩ := sLocalGammaOrbitalQuotient_coeff_shift ω c₀ j.val.1 h₀ j.property.1
    obtain ⟨w, hw⟩ := Finset.card_pos.mp (j.property.2.2.1.trans_le j.property.2.2.2)
    rw [hs] at hw
    obtain ⟨m, hm⟩ := ((P w).choose_spec.choose_spec.2 s).mp hw
    exact Set.mem_iUnion.mpr ⟨w, m, by rw [hs, hm]⟩
  have : Countable U := hU.to_subtype
  refine Function.Injective.countable
    (f := fun j : ΓIndex(ω, (Set.univ : Set Xₛ)) ↦ ((⟨j.val.1, hmem j⟩ : U), j.val.2)) ?_
  intro j₁ j₂ h
  have h1 : j₁.val.1 = j₂.val.1 := congrArg (fun p ↦ p.1.val) h
  have h2 : j₁.val.2 = j₂.val.2 := congrArg (fun p ↦ p.2) h
  exact Subtype.ext (Prod.ext h1 h2)

/-- There are infinitely many pairs of an archimedean center on the component and an
admissible Laurent order. -/
private theorem sLocalGammaOrbitalQuotient_coeff_infinite (ω : PontryaginDual J₁(S)) :
    Infinite (ΓIndex(ω, (Set.univ : Set Xₛ))) := by
  obtain ⟨c₀, h₀⟩ := sLocalGammaOrbitalQuotient_coeff_exists ω
  let P (w : InfinitePlace F) := sLocalGammaFiltration_iInf_placePoles c₀ w
  let pole (w : InfinitePlace F) (m : ℕ) : Xₛ :=
    shift(c₀, -((P w).choose_spec.choose * (m : ℝ) : ℂ) - (P w).choose)
  have hpole (w : InfinitePlace F) (m : ℕ) : w ∈ arch(pole w m) :=
    ((P w).choose_spec.choose_spec.2 _).mpr ⟨m, rfl⟩
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  obtain ⟨σ, hσ⟩ := sIdeleQuotientNorm_exists_section F S
  let t : ℝ≥0ˣ := Units.mk0 2 two_ne_zero
  let f : ℕ → ΓIndex(ω, (Set.univ : Set Xₛ)) := fun m ↦
    ⟨(pole w m, 1), sLocalGammaOrbitalQuotient_coeff_onComponent ω c₀ h₀ _, Set.mem_univ _,
      one_pos, Finset.card_pos.mpr ⟨w, hpole w m⟩⟩
  refine Infinite.of_injective f fun m₁ m₂ h ↦ ?_
  have hc : pole w m₁ = pole w m₂ := congrArg (fun j ↦ j.val.1) h
  have hg := DFunLike.congr_fun hc (σ t)
  change c₀ (σ t) * (((m(S) (σ t) : ℝ≥0) : ℝ) : ℂ) ^ (_ : ℂ) =
    c₀ (σ t) * (((m(S) (σ t) : ℝ≥0) : ℝ) : ℂ) ^ (_ : ℂ) at hg
  have hne : c₀ (σ t) ≠ 0 := ((Group.isUnit _).map c₀).ne_zero
  have hpow := congrArg norm (mul_left_cancel₀ hne hg)
  rw [hσ t] at hpow
  have h2 : (0 : ℝ) < ((t : ℝ≥0) : ℝ) := by norm_num [t]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos h2, Complex.norm_cpow_eq_rpow_re_of_pos h2] at hpow
  have hre := (Real.rpow_right_inj h2 (by norm_num [t])).mp hpow
  have hstep := (P w).choose_spec.choose_spec.1
  have hm : (P w).choose_spec.choose * (m₁ : ℝ) = (P w).choose_spec.choose * (m₂ : ℝ) := by
    simpa [Complex.mul_re] using hre
  exact_mod_cast mul_left_cancel₀ hstep.ne' hm

/-- A class lies in the entire-Mellin subspace exactly when all of its archimedean
Laurent coefficients on the component vanish. -/
private theorem sLocalGammaOrbitalQuotient_coeff_ker (ω : PontryaginDual J₁(S))
    (x : fullPV(ω)) :
    x ∈ Γker(ω) ↔ ∀ j : ΓIndex(ω, (Set.univ : Set Xₛ)), ΓCoeff(ω, j) x = 0 := by
  rw [← sLocalGammaFiltration_iInf, Submodule.mem_iInf]
  constructor
  · intro h j
    obtain ⟨N, hN⟩ := sLocalGammaFiltration_iInf_mem_cutoff ω j.val.1 j.property.1
      (Finset.card_pos.mp (j.property.2.2.1.trans_le j.property.2.2.2))
    exact (Submodule.mem_iInf _).mp (h N) ⟨j.val, j.property.1, hN, j.property.2.2⟩
  · intro h N
    exact (Submodule.mem_iInf _).mpr fun j ↦
      h ⟨j.val, j.property.1, Set.mem_univ _, j.property.2.2⟩

-- Repair the open-mapping gap (ERRATA I168) by a Borel–Mittag-Leffler lift.
-- Norm translations give exponentially small finite interpolants at far-left poles;
-- the closed full principal-value range is Fréchet, so the corrections converge.
section GammaInterpolationHelpers

private theorem finite_interpolant_small
    (E ι : Type*) [AddCommGroup E] [Module ℂ E] [Fintype ι]
    (q : Seminorm ℂ E) (v : ι → ℝ → E) (a : ι → ℝ → ℂ) (b : ι → ℝ → ℝ)
    (hv : ∀ i, ∀ᶠ t in atTop, q (v i t) ≤ b i t)
    (ha : ∀ i, Tendsto (fun t ↦ ‖a i t‖ * b i t) atTop (𝓝 0)) :
    Tendsto (fun t ↦ q (∑ i, a i t • v i t)) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ apply_nonneg _ _)
    (g := fun t ↦ ∑ i, ‖a i t‖ * b i t)
  · have hall : ∀ᶠ t in atTop, ∀ i, q (v i t) ≤ b i t :=
      Filter.eventually_all.mpr hv
    filter_upwards [hall] with t ht
    refine (Finset.le_sum_of_subadditive q (map_zero q).le (map_add_le_add q) _ _).trans ?_
    apply Finset.sum_le_sum
    intro i hi
    rw [map_smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (ht i) (norm_nonneg _)
  · simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun i _ ↦ ha i)
open Classical in
private theorem finite_level_small
    (E ι : Type*) [AddCommGroup E] [Module ℂ E] [Fintype ι]
    (P : Submodule ℂ E) (L : ι → E →ₗ[ℂ] ℂ)
    (ρ : ℝ → E →ₗ[ℂ] E)
    (hinv : ∀ t x, ρ t (ρ (-t) x) = x)
    (hP : ∀ t x, x ∈ P → ρ t x ∈ P)
    (hK : ∀ t x, x ∈ P → (∀ i, L i x = 0) → ∀ i, L i (ρ t x) = 0)
    (v : ι → E) (hvP : ∀ i, v i ∈ P)
    (hvL : ∀ i j, L i (v j) = if i = j then 1 else 0)
    (q q' : Seminorm ℂ E) (a : ℝ)
    (hbound : ∀ x, ∀ᶠ t in atTop, q (ρ t x) ≤ Real.exp (-a*t) * q' x)
    (hdecay : ∀ y ∈ P, ∀ i,
      Tendsto (fun t ↦ Real.exp (-a*t) * ‖L i (ρ (-t) y)‖) atTop (𝓝 0))
    (c : ι → ℂ) (ε : ℝ) (hε : 0 < ε) :
    ∃ x ∈ P, (∀ i, L i x = c i) ∧ q x < ε := by
  classical
  let y := ∑ i, c i • v i
  have hyP : y ∈ P := P.sum_mem fun i _ ↦ P.smul_mem _ (hvP i)
  have hyL (i) : L i y = c i := by simp [y, map_sum, map_smul, hvL]
  let z (t : ℝ) := ∑ i, L i (ρ (-t) y) • v i
  have hzP (t) : z t ∈ P := P.sum_mem fun i _ ↦ P.smul_mem _ (hvP i)
  have hzL (t) (i) : L i (z t) = L i (ρ (-t) y) := by simp [z, map_sum, map_smul, hvL]
  have hcoef (t) (i) : L i (ρ t (z t)) = c i := by
    have hzero (j) : L j (z t - ρ (-t) y) = 0 := by rw [map_sub, hzL]; exact sub_self _
    have hh := hK t (z t - ρ (-t) y) (P.sub_mem (hzP t) (hP _ _ hyP)) hzero i
    rw [map_sub, hinv, map_sub, sub_eq_zero, hyL] at hh
    exact hh
  have hsmall : Tendsto (fun t ↦ q (ρ t (z t))) atTop (𝓝 0) := by
    have h := finite_interpolant_small E ι q (fun i t ↦ ρ t (v i))
      (fun i t ↦ L i (ρ (-t) y)) (fun i t ↦ Real.exp (-a*t) * q' (v i))
      (fun i ↦ hbound (v i)) (fun i ↦ ?_)
    · simpa only [z, map_sum, map_smul] using h
    · have hh := (hdecay y hyP i).mul_const (q' (v i))
      convert hh using 1 <;> try { simp }
      funext t
      ring
  obtain ⟨t,ht⟩ := (hsmall.eventually (gt_mem_nhds hε)).exists
  exact ⟨ρ t (z t), hP _ _ (hzP t), hcoef t, ht⟩
private theorem image_action_bound
    (E κ U : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (p : SeminormFamily ℂ E κ) (hp : WithSeminorms p) (r : κ → ℝ)
    (ρ : ℝ → U → U) (J : U → E)
    (he : ∀ i t x, p i (J (ρ t x)) = Real.exp (-r i*t) * p i (J x))
    (q : Seminorm ℂ E) (hq : Continuous q) :
    ∃ a : ℝ, ∃ q' : Seminorm ℂ E,
      ∀ x, ∀ᶠ t in atTop, q (J (ρ t x)) ≤ Real.exp (-a*t) * q' (J x) := by
  classical
  obtain ⟨s,C,hC,hb⟩ := Seminorm.bound_sum_of_continuous hp q hq
  let a := -∑ i ∈ s, |r i|
  let q' : Seminorm ℂ E := C • ∑ i ∈ s, p i
  refine ⟨a,q',fun x ↦ ?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  have hr (i) (hi : i ∈ s) : a ≤ r i := by
    have h := Finset.single_le_sum (fun i _ ↦ abs_nonneg (r i)) hi
    have h' := neg_abs_le (r i)
    dsimp [a]
    linarith
  have hsum : (∑ i ∈ s, p i (J (ρ t x))) ≤ Real.exp (-a*t) * ∑ i ∈ s, p i (J x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    rw [he]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith [hr i hi])) (apply_nonneg _ _)
  have hh := hb (J (ρ t x))
  simp only [smul_apply, sum_apply, NNReal.smul_def, smul_eq_mul] at hh
  change q (J (ρ t x)) ≤ _ at hh
  calc
    q (J (ρ t x)) ≤ (C : ℝ) * ∑ i ∈ s, p i (J (ρ t x)) := hh
    _ ≤ (C : ℝ) * (Real.exp (-a*t) * ∑ i ∈ s, p i (J x)) := mul_le_mul_of_nonneg_left hsum C.coe_nonneg
    _ = Real.exp (-a*t) * q' (J x) := by
      simp only [q', smul_apply, sum_apply, NNReal.smul_def, smul_eq_mul]
      ring
private theorem exponential_polynomial_decay (s : ℂ) (a : ℝ) (hsa : s.re < a)
    (n : ℕ) (b : ℕ → ℂ) :
    Tendsto (fun t : ℝ ↦ Real.exp (-a*t) *
      ‖Complex.exp (s*(t : ℂ)) * ∑ k ∈ Finset.range n, b k * (t : ℂ)^k‖) atTop (𝓝 0) := by
  have hlim (k : ℕ) : Tendsto (fun t : ℝ ↦ t^k * Real.exp (-(a-s.re)*t)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k : ℝ) (a-s.re) (sub_pos.mpr hsa)
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
    (g := fun t : ℝ ↦ ∑ k ∈ Finset.range n, ‖b k‖ * (t^k * Real.exp (-(a-s.re)*t)))
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    have hS : ‖∑ k ∈ Finset.range n, b k * (t : ℂ)^k‖ ≤ ∑ k ∈ Finset.range n, ‖b k‖ * t^k := by
      simpa only [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht] using
        norm_sum_le (Finset.range n) (fun k ↦ b k * (t : ℂ)^k)
    have he : Real.exp (-a*t) * ‖Complex.exp (s*(t : ℂ))‖ = Real.exp (-(a-s.re)*t) := by
      rw [Complex.norm_exp, ← Real.exp_add]
      congr 1
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      ring
    rw [norm_mul, ← mul_assoc, he]
    calc
      _ ≤ Real.exp (-(a-s.re)*t) * ∑ k ∈ Finset.range n, ‖b k‖ * t^k :=
        mul_le_mul_of_nonneg_left hS (Real.exp_pos _).le
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
  · have h := tendsto_finsetSum (Finset.range n) (fun k _ ↦ (hlim k).const_mul ‖b k‖)
    simpa only [mul_zero, Finset.sum_const_zero] using h
open MeasureTheory in
private theorem bergman_trace_multiplier_norm
    (I : Set ℝ) (a : I) (N : ℕ) (f g : schwartzBergmanSubmodule I) (t : ℝ)
    (he : ∀ z ∈ Complex.re ⁻¹' I, g.val z = Complex.exp (-(t : ℂ)*z) * f.val z) :
    lpNorm (weightedVerticalTrace a N g.val) 2 volume =
      Real.exp (-t*(a : ℝ)) * lpNorm (weightedVerticalTrace a N f.val) 2 volume := by
  have hg := schwartzBergman_trace_memLp I a 2 (by norm_num) (by norm_num) N g
  have hf := schwartzBergman_trace_memLp I a 2 (by norm_num) (by norm_num) N f
  have hn (y : ℝ) : ‖weightedVerticalTrace a N g.val y‖ =
      ‖((Real.exp (-t*(a : ℝ))) • weightedVerticalTrace a N f.val) y‖ := by
    have hz : (a : ℂ) + (y : ℂ)*Complex.I ∈ Complex.re ⁻¹' I := by
      change ((a : ℂ) + (y : ℂ)*Complex.I).re ∈ I
      simpa using a.property
    simp only [weightedVerticalTrace]
    rw [he _ hz]
    simp only [weightedVerticalTrace, norm_mul, Complex.norm_exp, Pi.smul_apply, norm_smul,
      Real.norm_of_nonneg (Real.exp_pos _).le, Complex.mul_re, Complex.neg_re,
      Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
      Complex.add_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, neg_zero,
      add_zero, zero_add, sub_zero, mul_one]
    ring
  unfold lpNorm
  rw [eLpNorm_congr_norm_ae hg.aestronglyMeasurable
    (hf.const_smul (Real.exp (-t*(a : ℝ)))).aestronglyMeasurable (Eventually.of_forall hn)]
  change lpNorm ((Real.exp (-t*(a : ℝ))) • weightedVerticalTrace a N f.val) 2 volume = _
  rw [lpNorm_const_smul]
  change |Real.exp (-t*(a : ℝ))| * lpNorm (weightedVerticalTrace a N f.val) 2 volume = _
  rw [abs_of_pos (Real.exp_pos _)]
  rfl
private theorem finite_interpolation
    (E ι : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [Fintype ι]
    (L : ι → E →L[ℂ] ℂ) (hL : LinearIndependent ℂ L) :
    Surjective (fun x : E ↦ fun i ↦ L i x) := by
  classical
  let T : E →ₗ[ℂ] (ι → ℂ) := LinearMap.pi (fun i ↦ (L i).toLinearMap)
  change Surjective T
  apply LinearMap.dualMap_injective_iff.mp
  apply (injective_iff_map_eq_zero _).mpr
  intro f hf
  have hsum : ∑ i, f (Pi.single i 1) • L i = 0 := by
    ext x
    have hTx : T x = ∑ i, L i x • Pi.single i (1 : ℂ) := by
      ext j
      simp [T, Pi.single_apply]
    have hh := congrArg (fun ℓ : Module.Dual ℂ E ↦ ℓ x) hf
    change f (T x) = 0 at hh
    rw [hTx, map_sum] at hh
    simpa only [sum_apply, smul_apply, map_smul, smul_eq_mul, mul_comm, zero_apply] using hh
  have hc := (Fintype.linearIndependent_iff.mp hL) (fun i ↦ f (Pi.single i 1)) hsum
  apply LinearMap.ext
  intro u
  have hu : u = ∑ i, u i • Pi.single i (1 : ℂ) := by
    ext j
    simp [Pi.single_apply]
  change f u = 0
  rw [hu,map_sum]
  simp only [map_smul, hc, smul_zero, Finset.sum_const_zero]
private theorem gamma_frechet_embed
    {X Y : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    (i : X →L[ℂ] Y) (hi : IsClosedEmbedding i) (hY : IsFrechetTVS Y) : IsFrechetTVS X := by
  obtain ⟨hadd,hpoly,hmet,hcomplete⟩ := hY
  let : UniformSpace Y := IsTopologicalAddGroup.rightUniformSpace Y
  let : IsUniformAddGroup Y := isUniformAddGroup_of_addCommGroup
  let : CompleteSpace Y := hcomplete
  let : UniformSpace X := IsTopologicalAddGroup.rightUniformSpace X
  let : IsUniformAddGroup X := isUniformAddGroup_of_addCommGroup
  have hu := AddMonoidHom.isUniformInducing_of_isInducing (f := i.toLinearMap.toAddMonoidHom) hi.isInducing
  exact ⟨inferInstance, hi.eq_induced ▸ PolynormableSpace.induced i.toLinearMap,
    hi.isEmbedding.metrizableSpace, hu.completeSpace hi.isClosed_range.isComplete⟩
private theorem gamma_range_frechet (F : Type*) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (ω : PontryaginDual (sIdeleQuotientNorm F S).ker) :
    IsFrechetTVS ↥((sLocalHomogeneousThetaPrincipalValue (F := F) (Finset.Subset.refl S) ω).range) := by
  let D := (sLocalHomogeneousThetaPrincipalValue (F := F) (Finset.Subset.refl S) ω).range
  have hD : IsClosed (D : Set (SLocalHomogeneousThetaSpace F S ω)) :=
    (sLocalHomogeneousThetaPrincipalValue_isClosedEmbedding (F := F) (Finset.Subset.refl S) ω).isClosed_range
  exact gamma_frechet_embed D.subtypeL (D.isClosedEmbedding_subtypeL hD)
    (sLocalHomogeneousThetaSpace_frechet (F := F) (S := S) ω)
private theorem action_on_range
    (G E : Type*) [Monoid G] [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (A : G →* (E →L[ℂ] E)) (P : E →ₗ[ℂ] E)
    (hcomm : ∀ g x, A g (P x) = P (A g x)) :
    ∃ ρ : G →* (P.range →L[ℂ] P.range), ∀ g x, (ρ g x).val = A g x.val := by
  have hpres (g) : ∀ x ∈ P.range, A g x ∈ P.range := by
    rintro x ⟨y,rfl⟩
    exact ⟨A g y,(hcomm g y).symm⟩
  let ρ (g : G) : P.range →L[ℂ] P.range := (A g).restrict (hpres g)
  refine ⟨{ toFun := ρ, map_one' := ?_, map_mul' := ?_ },fun g x ↦ rfl⟩
  · ext x
    change A 1 x.val = x.val
    rw [A.map_one]
    rfl
  · intro g h
    ext x
    change A (g*h) x.val = A g (A h x.val)
    rw [A.map_mul]
    rfl
private theorem product_action_bound
    (E X Y κ ιY : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    (p : SeminormFamily ℂ X κ) (hp : WithSeminorms p)
    (q : SeminormFamily ℂ Y ιY) (hq : WithSeminorms q)
    (r : κ → ℝ) (s : ιY → ℝ)
    (ρ : ℝ → E →ₗ[ℂ] E) (J : E →ₗ[ℂ] X × Y) (hJ : IsInducing J)
    (hx : ∀ i t x, p i (J (ρ t x)).1 = Real.exp (-r i*t) * p i (J x).1)
    (hy : ∀ i t x, q i (J (ρ t x)).2 = Real.exp (-s i*t) * q i (J x).2)
    (Q : Seminorm ℂ E) (hQ : Continuous Q) :
    ∃ a : ℝ, ∃ Q' : Seminorm ℂ E,
      ∀ x, ∀ᶠ t in atTop, Q (ρ t x) ≤ Real.exp (-a*t) * Q' x := by
  let : PolynormableSpace ℂ X := hp.toPolynormableSpace
  let : PolynormableSpace ℂ Y := hq.toPolynormableSpace
  obtain ⟨B,hB,hQB⟩ := Seminorm.exists_le_comp_of_isInducing hQ hJ
  let Bx := B.comp (LinearMap.inl ℂ X Y)
  let By := B.comp (LinearMap.inr ℂ X Y)
  have hBx : Continuous Bx := hB.comp (continuous_id.prodMk continuous_const)
  have hBy : Continuous By := hB.comp (continuous_const.prodMk continuous_id)
  obtain ⟨ax,Bx',hx'⟩ := image_action_bound X κ E p hp r (fun t ↦ ρ t) (fun x ↦ (J x).1) hx Bx hBx
  obtain ⟨ay,By',hy'⟩ := image_action_bound Y ιY E q hq s (fun t ↦ ρ t) (fun x ↦ (J x).2) hy By hBy
  let a := min ax ay
  let Q' := (Bx'.comp ((LinearMap.fst ℂ X Y).comp J)) + (By'.comp ((LinearMap.snd ℂ X Y).comp J))
  refine ⟨a,Q',fun x ↦ ?_⟩
  filter_upwards [hx' x,hy' x,eventually_ge_atTop (0 : ℝ)] with t htX htY ht
  have heX : Real.exp (-ax*t) ≤ Real.exp (-a*t) := Real.exp_le_exp.mpr (by have := min_le_left ax ay; dsimp [a]; nlinarith)
  have heY : Real.exp (-ay*t) ≤ Real.exp (-a*t) := Real.exp_le_exp.mpr (by have := min_le_right ax ay; dsimp [a]; nlinarith)
  calc
    Q (ρ t x) ≤ B (J (ρ t x)) := hQB _
    _ ≤ Bx (J (ρ t x)).1 + By (J (ρ t x)).2 := by
      have hb := map_add_le_add B ((J (ρ t x)).1,0) (0,(J (ρ t x)).2)
      change B ((J (ρ t x)).1,(J (ρ t x)).2) ≤
        B ((J (ρ t x)).1,0) + B (0,(J (ρ t x)).2)
      simpa only [Prod.mk_add_mk,add_zero,zero_add] using hb
    _ ≤ Real.exp (-ax*t) * Bx' (J x).1 + Real.exp (-ay*t) * By' (J x).2 := add_le_add htX htY
    _ ≤ Real.exp (-a*t) * (Bx' (J x).1 + By' (J x).2) := by
      rw [mul_add]
      exact add_le_add (mul_le_mul_of_nonneg_right heX (apply_nonneg _ _))
        (mul_le_mul_of_nonneg_right heY (apply_nonneg _ _))
    _ = Real.exp (-a*t) * Q' x := rfl
private theorem finite_code_prefix (ι : Type*) (code : ι → ℕ)
    (hf : ∀ n, Finite {i : ι // code i = n}) (k : ℕ) :
    Finite {i : ι // code i ≤ k} := by
  letI (n : Fin (k+1)) : Finite {i : ι // code i = n.val} := hf n.val
  let f : {i : ι // code i ≤ k} → (n : Fin (k+1)) × {i : ι // code i = n.val} :=
    fun i ↦ ⟨⟨code i.val,Nat.lt_succ_of_le i.property⟩,⟨i.val,rfl⟩⟩
  apply Finite.of_injective f
  intro i j h
  apply Subtype.ext
  exact congrArg (fun x : (n : Fin (k+1)) × {i : ι // code i = n.val} ↦ x.2.val) h
open Classical in
private theorem surjective_of_translated_coefficients
    (E ι : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (hE : IsFrechetTVS E) (L : ι → E →L[ℂ] ℂ) (code : ι → ℕ)
    (hf : ∀ k, Finite {i : ι // code i = k})
    (hv : ∀ k, ∃ v : {i : ι // code i = k} → E,
      (∀ i j, code j < k → L j (v i) = 0) ∧
      ∀ i j, (i = j → L j.val (v i) = 1) ∧ (i ≠ j → L j.val (v i) = 0))
    (ρ : ℝ → E →ₗ[ℂ] E) (hinv : ∀ t x, ρ t (ρ (-t) x) = x)
    (hker : ∀ (p : ℕ → Prop) t x, (∀ i, p (code i) → L i x = 0) →
      ∀ i, p (code i) → L i (ρ t x) = 0)
    (hbound : ∀ q : Seminorm ℂ E, Continuous q → ∃ a : ℝ, ∃ q' : Seminorm ℂ E,
      ∀ x, ∀ᶠ t in atTop, q (ρ t x) ≤ Real.exp (-a*t) * q' x)
    (htail : ∀ a : ℝ, ∃ K : ℕ, ∀ i, K ≤ code i → ∀ y,
      Tendsto (fun t ↦ Real.exp (-a*t) * ‖L i (ρ (-t) y)‖) atTop (𝓝 0)) :
    Surjective (fun x : E ↦ fun i ↦ L i x) := by
  obtain ⟨hadd,hpoly,hmet,hcomplete⟩ := hE
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  let : CompleteSpace E := hcomplete
  letI (k : ℕ) : Fintype {i : ι // code i = k} := Fintype.ofFinite _
  have hs : Surjective (fun x : E ↦ fun k (i : {i : ι // code i = k}) ↦ L i.val x) := by
    apply surjective_coeff_of_eventually_small
    · intro k c
      obtain ⟨v,hv0,hvraw⟩ := hv k
      have hv1 (i j) : L j.val (v i) = if i = j then 1 else 0 := by
        by_cases h : i = j
        · rw [if_pos h]; exact (hvraw i j).1 h
        · rw [if_neg h]; exact (hvraw i j).2 h
      let y := ∑ i, c i • v i
      refine ⟨y,?_,?_⟩
      · intro j hj i
        simp [y,map_sum,map_smul,hv0 _ _ (by rw [i.property]; exact hj)]
      · intro i
        simp [y,map_sum,map_smul,hv1,eq_comm]
    · intro q hq
      obtain ⟨a,q',hb⟩ := hbound q hq
      obtain ⟨K,hK⟩ := htail a
      refine ⟨K,fun k hk c ε hε ↦ ?_⟩
      let P : Submodule ℂ E := ⨅ i : {i : ι // code i < k}, (L i.val).ker
      have hP (x : E) : x ∈ P ↔ ∀ i, code i < k → L i x = 0 := by simp [P]
      obtain ⟨v,hv0,hv1⟩ := hv k
      obtain ⟨x,hx,hL,hsmall⟩ := finite_level_small E {i : ι // code i = k} P
        (fun i ↦ (L i.val).toLinearMap) ρ hinv
        (fun t x hx ↦ (hP _).mpr (hker (fun n ↦ n < k) t x ((hP _).mp hx)))
        (fun t x hx hz i ↦ hker (fun n ↦ n ≤ k) t x (fun j hj ↦ by
          rcases lt_or_eq_of_le hj with hj | hj
          · exact (hP _).mp hx j hj
          · exact hz ⟨j,hj⟩) i.val (by rw [i.property]))
        v (fun i ↦ (hP _).mpr (hv0 i)) (fun i j ↦ by
          by_cases h : i = j
          · subst j
            rw [if_pos rfl]
            exact (hv1 i i).1 rfl
          · rw [if_neg h]
            exact (hv1 j i).2 (Ne.symm h)) q q' a hb
        (fun y hy i ↦ hK i.val (by rw [i.property]; exact hk) y) c ε hε
      · refine ⟨x,fun j hj i ↦ (hP x).mp hx i.val ?_,hL,hsmall⟩
        rw [i.property]
        exact hj
  intro c
  obtain ⟨x,hx⟩ := hs (fun k i ↦ c i.val)
  refine ⟨x,funext fun i ↦ ?_⟩
  exact congrFun (congrFun hx (code i)) ⟨i,rfl⟩
private theorem real_action_inverse (E : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (B : Multiplicative ℝ →* (E →L[ℂ] E)) (t : ℝ) (x : E) :
    B (Multiplicative.ofAdd (-t)) (B (Multiplicative.ofAdd (-(-t))) x) = x := by
  have hh : (Multiplicative.ofAdd (-t) : Multiplicative ℝ) * Multiplicative.ofAdd (-(-t)) = 1 := by
    change -t + -(-t) = 0
    ring
  have hB : B (Multiplicative.ofAdd (-t)) * B (Multiplicative.ofAdd (-(-t))) = 1 := by
    rw [← B.map_mul,hh,B.map_one]
  exact congrArg (fun f : E →L[ℂ] E ↦ f x) hB

private theorem gamma_full_action (ω : PontryaginDual J₁(S)) :
    ∃ ρ : J(S) →* (fullPV(ω) →L[ℂ] fullPV(ω)),
      ∀ g x, (ρ g x).val = A(S, ω) g x.val := by
  exact action_on_range J(S) Θ(S, ω) A(S, ω) PV((Finset.Subset.refl S), ω)
    (fun g x ↦ (sLocalPW_principalValue_diagram_comm (F := F) (Finset.Subset.refl S) ω g x).symm)

private theorem gamma_action_laurent (ω : PontryaginDual J₁(S)) (x : Θ(S, ω))
    (c : Xₛ) (hc : onComponent(c, ω)) (k : ℕ) (hk : k ≤ sLocalRhoPoleOrder c)
    (u : (SAdeleRing F S)ˣ) :
    sLocalThetaPrincipalPartCoeff ω c hc k (A(S, ω) (QuotientGroup.mk u) x) =
      c (QuotientGroup.mk u) * ∑ j ∈ Finset.range (sLocalRhoPoleOrder c-k+1),
        sLocalThetaPrincipalPartCoeff ω c hc (k+j) x *
          (Real.log (((m(S) (QuotientGroup.mk u)).val : ℝ)) : ℂ)^j / (j.factorial : ℂ) := by
  obtain ⟨f,rfl⟩ := Submodule.mkQ_surjective (LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap F S ω)) x
  rw [(existsUnique_sLocalHomogeneousThetaAction (F := F) (S := S) ω).exists.choose_spec.2 u f]
  change sLocalPrincipalPartCoeff c k (schwartzBruhatUnitTranslate u f) =
    c (QuotientGroup.mk u) * ∑ j ∈ Finset.range (sLocalRhoPoleOrder c-k+1),
      sLocalPrincipalPartCoeff c (k+j) f *
        (Real.log (((m(S) (QuotientGroup.mk u)).val : ℝ)) : ℂ)^j / (j.factorial : ℂ)
  exact sLocalPrincipalPartCoeff_translate c k hk u f

private theorem gamma_high_coeff_zero (ω : PontryaginDual J₁(S)) (x : fullPV(ω))
    (c : Xₛ) (hc : onComponent(c, ω)) (k : ℕ) (hk : (arch(c)).card < k) :
    sLocalThetaPrincipalPartCoeff ω c hc k x.val = 0 := by
  obtain ⟨y,hy⟩ := x.property
  obtain ⟨f,rfl⟩ := Submodule.mkQ_surjective (LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap F S ω)) y
  let g := sAdelePrincipalValue F (Finset.Subset.refl S) f
  have hg : q(S, ω) g = x.val := hy
  rw [← hg]
  change sLocalPrincipalPartCoeff c k g = 0
  by_contra hne
  have hpos : 0 < k := lt_of_le_of_lt (Nat.zero_le _) hk
  have hpole := (sLocalPrincipalPartCoeff_ne_zero_imp_pole c k hpos g hne).2
  have hb := gammaFiltration_principalValue_bound f c
  dsimp [g] at hpole
  omega

private theorem gamma_zeta_translate (χ : PontryaginDual J(S)) (g : J(S)) :
    let ω := χ.comp (⟨(m(S)).ker.subtype, continuous_subtype_val⟩ : J₁(S) →ₜ* J(S))
    let Z := sLocalZetaPair (F := F) (S := S) χ
    ∀ x : Θ(S, ω),
      EqOn (Z (A(S, ω) g x)).1.val
        (fun z ↦ shift((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ, z) g * (Z x).1.val z)
        (Complex.re ⁻¹' Ioi (0 : ℝ)) ∧
      EqOn (Z (A(S, ω) g x)).2.val
        (fun z ↦ shift((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ, z) g * (Z x).2.val z)
        (Complex.re ⁻¹' Iio (1 : ℝ)) := by
  intro ω Z x
  obtain ⟨u,rfl⟩ := QuotientGroup.mk_surjective g
  refine Quotient.inductionOn' x ?_
  intro f
  have ha := (existsUnique_sLocalHomogeneousThetaAction (F := F) (S := S) ω).exists.choose_spec.2 u f
  have ht := sLocalZetaPair_translate (F := F) (S := S) χ u f
  constructor
  · intro z hz
    have he := congrArg (fun y : Θ(S, ω) ↦ (Z y).1.val z) ha
    exact he.trans (ht.1 hz)
  · intro z hz
    have he := congrArg (fun y : Θ(S, ω) ↦ (Z y).2.val z) ha
    exact he.trans (ht.2 hz)

open MeasureTheory in
private theorem gamma_action_bound (χ : PontryaginDual J(S)) (g : ℝ → J(S))
    (hnorm : ∀ t, (((m(S) (g t)).val : ℝ)) = Real.exp (-t))
    (hχ : ∀ t, χ (g t) = 1) :
    let ω := χ.comp (⟨(m(S)).ker.subtype, continuous_subtype_val⟩ : J₁(S) →ₜ* J(S))
    ∀ (ρ : J(S) →* (fullPV(ω) →L[ℂ] fullPV(ω))),
      (∀ h x, (ρ h x).val = A(S, ω) h x.val) →
    ∀ Q : Seminorm ℂ (fullPV(ω)), Continuous Q →
      ∃ a : ℝ, ∃ Q' : Seminorm ℂ (fullPV(ω)),
        ∀ x, ∀ᶠ t in atTop, Q (ρ (g t) x) ≤ Real.exp (-a*t) * Q' x := by
  intro ω ρ hρ Q hQ
  let X := SchwartzBergman (Ioi (0 : ℝ))
  let Y := SchwartzBergman (Iio (1 : ℝ))
  let Z := sLocalZetaPair (F := F) (S := S) χ
  let J : fullPV(ω) →ₗ[ℂ] X × Y := Z.comp (fullPV(ω)).subtype
  have hJ : IsInducing J := (sLocalZetaPair_isClosedEmbedding (F := F) (S := S) χ).isInducing.comp
    Topology.IsInducing.subtypeVal
  let p (I : Set ℝ) : I × ℕ → Seminorm ℂ (SchwartzBergman I) := fun i ↦ Seminorm.of
    (fun f : schwartzBergmanSubmodule I ↦ (eLpNorm (weightedVerticalTrace i.1 i.2 f.val) 2 volume).toReal)
    (schwartzBergman_l2_seminorm I i).1 (schwartzBergman_l2_seminorm I i).2
  have hp (I : Set ℝ) : WithSeminorms (p I) := withGeneratingSeminorms_spec _ _
  have hfactor (t : ℝ) (z : ℂ) :
      shift((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ, z) (g t) =
        Complex.exp (-(t : ℂ)*z) := by
    change (χ (g t) : ℂ) * ((((m(S) (g t)).val : ℝ) : ℂ)^z) = _
    rw [hχ t, Circle.coe_one, one_mul, hnorm t]
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'),
      ← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp, Complex.ofReal_neg]
  apply product_action_bound (fullPV(ω)) X Y ((Ioi (0 : ℝ)) × ℕ) ((Iio (1 : ℝ)) × ℕ)
    (p _) (hp _) (p _) (hp _) (fun i ↦ (i.1 : ℝ)) (fun i ↦ (i.1 : ℝ))
    (fun t ↦ (ρ (g t)).toLinearMap) J hJ ?_ ?_ Q hQ
  · intro i t x
    have he : ∀ z ∈ Complex.re ⁻¹' Ioi (0 : ℝ),
        (J (ρ (g t) x)).1.val z = Complex.exp (-(t : ℂ)*z) * (J x).1.val z := by
      intro z hz
      have hmap := congrArg (fun y : Θ(S, ω) ↦ (Z y).1.val z) (hρ (g t) x)
      have ht := (gamma_zeta_translate χ (g t) x.val).1 hz
      exact hmap.trans (ht.trans (congrArg (fun w : ℂ ↦ w * (J x).1.val z) (hfactor t z)))
    have h := bergman_trace_multiplier_norm (Ioi (0 : ℝ)) i.1 i.2 (J x).1 (J (ρ (g t) x)).1 t he
    change lpNorm (weightedVerticalTrace i.1 i.2 (J (ρ (g t) x)).1.val) 2 volume =
      Real.exp (-(i.1 : ℝ)*t) * lpNorm (weightedVerticalTrace i.1 i.2 (J x).1.val) 2 volume
    rw [show -(i.1 : ℝ)*t = -t*(i.1 : ℝ) by ring]
    exact h
  · intro i t x
    have he : ∀ z ∈ Complex.re ⁻¹' Iio (1 : ℝ),
        (J (ρ (g t) x)).2.val z = Complex.exp (-(t : ℂ)*z) * (J x).2.val z := by
      intro z hz
      have hmap := congrArg (fun y : Θ(S, ω) ↦ (Z y).2.val z) (hρ (g t) x)
      have ht := (gamma_zeta_translate χ (g t) x.val).2 hz
      exact hmap.trans (ht.trans (congrArg (fun w : ℂ ↦ w * (J x).2.val z) (hfactor t z)))
    have h := bergman_trace_multiplier_norm (Iio (1 : ℝ)) i.1 i.2 (J x).2 (J (ρ (g t) x)).2 t he
    change lpNorm (weightedVerticalTrace i.1 i.2 (J (ρ (g t) x)).2.val) 2 volume =
      Real.exp (-(i.1 : ℝ)*t) * lpNorm (weightedVerticalTrace i.1 i.2 (J x).2.val) 2 volume
    rw [show -(i.1 : ℝ)*t = -t*(i.1 : ℝ) by ring]
    exact h

private theorem gamma_weight_shift (τ : ℝ≥0ˣ →ₜ* J(S)) (hτ : RightInverse τ (m(S)))
    (c : Xₛ) (z : ℂ) :
    let u : ℝ≥0ˣ := Units.mk0 2 two_ne_zero
    Real.log ‖shift(c,z) (τ u)‖ / Real.log 2 = Real.log ‖c (τ u)‖ / Real.log 2 + z.re := by
  intro u
  have hu : (((u : ℝ≥0ˣ).val : ℝ)) = 2 := by norm_num [u]
  have hn : ‖shift(c,z) (τ u)‖ = ‖c (τ u)‖ * (2 : ℝ)^z.re := by
    change ‖c (τ u) * ((((m(S) (τ u)).val : ℝ) : ℂ)^z)‖ = _
    rw [norm_mul,hτ u,hu,Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
  have hc : ‖c (τ u)‖ ≠ 0 := norm_ne_zero_iff.mpr (((Group.isUnit (τ u)).map c).ne_zero)
  rw [hn,Real.log_mul hc (Real.rpow_pos_of_pos (by norm_num) _).ne',Real.log_rpow (by norm_num)]
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  field_simp

private theorem gamma_finite_centers_above (ω : PontryaginDual J₁(S))
    (τ : ℝ≥0ˣ →ₜ* J(S)) (hτ : RightInverse τ (m(S))) (A : ℝ) :
    let u : ℝ≥0ˣ := Units.mk0 2 two_ne_zero
    Set.Finite {c : Xₛ | onComponent(c,ω) ∧ (arch(c)).Nonempty ∧
      A ≤ Real.log ‖c (τ u)‖ / Real.log 2} := by
  intro u
  classical
  obtain ⟨c₀,h₀⟩ := sLocalGammaOrbitalQuotient_coeff_exists ω
  let P (w : InfinitePlace F) := sLocalGammaFiltration_iInf_placePoles c₀ w
  let b := Real.log ‖c₀ (τ u)‖ / Real.log 2
  let pole (w : InfinitePlace F) (n : ℕ) : Xₛ :=
    shift(c₀, -((P w).choose_spec.choose * (n : ℝ) : ℂ) - (P w).choose)
  choose N hN using fun w : InfinitePlace F ↦
    exists_nat_gt ((b - (P w).choose.re - A) / (P w).choose_spec.choose)
  let U := ⋃ w : InfinitePlace F, Set.range (fun n : Fin (N w) ↦ pole w n.val)
  have hU : U.Finite := Set.finite_iUnion fun w ↦ Set.finite_range _
  apply hU.subset
  rintro c ⟨hc,hw,hA⟩
  obtain ⟨s,hs⟩ := sLocalGammaOrbitalQuotient_coeff_shift ω c₀ c h₀ hc
  obtain ⟨w,hw⟩ := hw
  rw [hs] at hw
  obtain ⟨n,hn⟩ := ((P w).choose_spec.choose_spec.2 s).mp hw
  have he : c = pole w n := by rw [hs,hn]
  have hwgt : Real.log ‖c (τ u)‖ / Real.log 2 =
      b - (P w).choose_spec.choose * (n : ℝ) - (P w).choose.re := by
    rw [he]
    have h := gamma_weight_shift τ hτ c₀
      (-((P w).choose_spec.choose * (n : ℝ) : ℂ) - (P w).choose)
    change Real.log ‖(pole w n) (τ u)‖ / Real.log 2 = b + _ at h
    rw [h]
    simp only [Complex.sub_re,Complex.neg_re,Complex.ofReal_re,Complex.mul_re,
      Complex.ofReal_im,mul_zero,sub_zero]
    ring
  have hstep := (P w).choose_spec.choose_spec.1
  have hnr : (n : ℝ) < N w := lt_of_le_of_lt
    ((le_div_iff₀ hstep).mpr (by rw [hwgt] at hA; linarith)) (hN w)
  have hnn : n < N w := by exact_mod_cast hnr
  exact Set.mem_iUnion.mpr ⟨w,⟨⟨n,hnn⟩,he.symm⟩⟩

private theorem gamma_finite_indices_above (ω : PontryaginDual J₁(S))
    (τ : ℝ≥0ˣ →ₜ* J(S)) (hτ : RightInverse τ (m(S))) (A : ℝ) :
    let u : ℝ≥0ˣ := Units.mk0 2 two_ne_zero
    Set.Finite {j : ΓIndex(ω,(Set.univ : Set Xₛ)) |
      A ≤ Real.log ‖j.val.1 (τ u)‖ / Real.log 2} := by
  intro u
  have hC := gamma_finite_centers_above ω τ hτ A
  apply Set.Finite.of_injOn (f := fun j : ΓIndex(ω,(Set.univ : Set Xₛ)) ↦ j.val) ?_
    Subtype.val_injective.injOn (hC.prod (Set.finite_Iic (Fintype.card (InfinitePlace F))))
  intro j hj
  exact ⟨⟨j.property.1,Finset.card_pos.mp (j.property.2.2.1.trans_le j.property.2.2.2),hj⟩,
    j.property.2.2.2.trans (Finset.card_le_univ _)⟩

private theorem gamma_block_code (ω : PontryaginDual J₁(S)) :
    ∃ code : ΓIndex(ω,(Set.univ : Set Xₛ)) → ℕ,
      (∀ i j, code i = code j ↔ i.val.1 = j.val.1) ∧
      ∀ k, Finite {j : ΓIndex(ω,(Set.univ : Set Xₛ)) // code j = k} := by
  classical
  let C := {c : Xₛ // onComponent(c,ω) ∧ (arch(c)).Nonempty}
  let center (j : ΓIndex(ω,(Set.univ : Set Xₛ))) : C :=
    ⟨j.val.1,j.property.1,Finset.card_pos.mp (j.property.2.2.1.trans_le j.property.2.2.2)⟩
  have : Countable (ΓIndex(ω,(Set.univ : Set Xₛ))) := sLocalGammaOrbitalQuotient_coeff_countable ω
  have : Countable C := Function.Injective.countable
    (f := fun c : C ↦ (⟨(c.val,1),c.property.1,Set.mem_univ _,one_pos,Finset.card_pos.mpr c.property.2⟩ : ΓIndex(ω,(Set.univ : Set Xₛ))))
    (fun i j h ↦ Subtype.ext (congrArg (fun j : ΓIndex(ω,(Set.univ : Set Xₛ)) ↦ j.val.1) h))
  let : Encodable C := Encodable.ofCountable C
  let code (j : ΓIndex(ω,(Set.univ : Set Xₛ))) := Encodable.encode (center j)
  have he (i j) : code i = code j ↔ i.val.1 = j.val.1 := by
    constructor
    · intro h
      exact congrArg Subtype.val (Encodable.encode_injective h)
    · intro h
      exact congrArg Encodable.encode (Subtype.ext h)
  refine ⟨code,he,fun k ↦ ?_⟩
  let f : {j : ΓIndex(ω,(Set.univ : Set Xₛ)) // code j = k} → Fin (Fintype.card (InfinitePlace F)+1) :=
    fun j ↦ ⟨j.val.val.2,Nat.lt_succ_of_le (j.val.property.2.2.2.trans (Finset.card_le_univ _))⟩
  apply Finite.of_injective f
  intro i j h
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · exact (he i.val j.val).mp (i.property.trans j.property.symm)
  · exact congrArg Fin.val h

private theorem gamma_positive_flow :
    ∃ ν : Multiplicative ℝ →* ℝ≥0ˣ,
      ∀ t : ℝ, ((ν (Multiplicative.ofAdd t)).val : ℝ) = Real.exp t := by
  let ν : Multiplicative ℝ →* ℝ≥0ˣ :=
    { toFun := fun t ↦ Units.mk0 (Real.exp t.toAdd).toNNReal (by positivity)
      map_one' := by apply Units.ext; apply NNReal.coe_injective; simp
      map_mul' := by
        intro t u
        apply Units.ext
        apply NNReal.coe_injective
        simp [Real.exp_add,max_eq_left (Real.exp_pos t.toAdd).le,
          max_eq_left (Real.exp_pos u.toAdd).le,
          max_eq_left (mul_nonneg (Real.exp_pos t.toAdd).le (Real.exp_pos u.toAdd).le)] }
  exact ⟨ν,fun t ↦ Real.coe_toNNReal _ (Real.exp_pos t).le⟩

private theorem gamma_character_exponent (τ : ℝ≥0ˣ →ₜ* J(S))
    (ν : Multiplicative ℝ →* ℝ≥0ˣ)
    (hν : ∀ t : ℝ, ((ν (Multiplicative.ofAdd t)).val : ℝ) = Real.exp t) (c : Xₛ) :
    ∃ s : ℂ,
      (∀ t : ℝ, c (τ (ν (Multiplicative.ofAdd t))) = Complex.exp (s*(t : ℂ))) ∧
      (let u : ℝ≥0ˣ := Units.mk0 2 two_ne_zero
       Real.log ‖c (τ u)‖ / Real.log 2 = s.re) := by
  obtain ⟨s,hs,_⟩ := existsUnique_complexPower (c.comp τ)
  refine ⟨s,fun t ↦ ?_,?_⟩
  · have h := hs (ν (Multiplicative.ofAdd t))
    change c (τ (ν (Multiplicative.ofAdd t))) =
      ((((ν (Multiplicative.ofAdd t)).val : ℝ) : ℂ)^s) at h
    rw [hν t] at h
    rw [h,Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'),
      ← Complex.ofReal_log (Real.exp_pos _).le,Real.log_exp]
    congr 1
    ring
  · intro u
    have h := congrArg norm (hs u)
    change ‖c (τ u)‖ = ‖(((u.val : ℝ) : ℂ)^s)‖ at h
    have hu : ((u.val : ℝ)) = 2 := by norm_num [u]
    rw [hu,Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)] at h
    rw [h,Real.log_rpow (by norm_num)]
    exact mul_div_cancel_right₀ _ (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'

private theorem gamma_action_laurent_class (ω : PontryaginDual J₁(S)) (x : Θ(S, ω))
    (c : Xₛ) (hc : onComponent(c, ω)) (k : ℕ) (hk : k ≤ sLocalRhoPoleOrder c)
    (g : J(S)) :
    sLocalThetaPrincipalPartCoeff ω c hc k (A(S, ω) g x) =
      c g * ∑ j ∈ Finset.range (sLocalRhoPoleOrder c-k+1),
        sLocalThetaPrincipalPartCoeff ω c hc (k+j) x *
          (Real.log (((m(S) g).val : ℝ)) : ℂ)^j / (j.factorial : ℂ) := by
  refine Quotient.inductionOn' g ?_
  intro u
  exact gamma_action_laurent ω x c hc k hk u

private theorem gamma_coefficient_decay (ω : PontryaginDual J₁(S))
    (τ : ℝ≥0ˣ →ₜ* J(S)) (hτ : RightInverse τ (m(S)))
    (ν : Multiplicative ℝ →* ℝ≥0ˣ)
    (hν : ∀ t : ℝ, ((ν (Multiplicative.ofAdd t)).val : ℝ) = Real.exp t)
    (ρ : J(S) →* (fullPV(ω) →L[ℂ] fullPV(ω)))
    (hρ : ∀ g x, (ρ g x).val = A(S, ω) g x.val)
    (c : Xₛ) (hc : onComponent(c, ω)) (k : ℕ) (hk : k ≤ sLocalRhoPoleOrder c)
    (a : ℝ) (ha : Real.log ‖c (τ (Units.mk0 2 two_ne_zero))‖ / Real.log 2 < a)
    (y : fullPV(ω)) :
    Tendsto (fun t : ℝ ↦ Real.exp (-a*t) *
      ‖sLocalThetaPrincipalPartCoeff ω c hc k (ρ (τ (ν (Multiplicative.ofAdd t))) y).val‖)
      atTop (𝓝 0) := by
  obtain ⟨s,hs,hw⟩ := gamma_character_exponent τ ν hν c
  let N := sLocalRhoPoleOrder c-k+1
  let b (j : ℕ) := sLocalThetaPrincipalPartCoeff ω c hc (k+j) y.val / (j.factorial : ℂ)
  have he (t : ℝ) :
      sLocalThetaPrincipalPartCoeff ω c hc k (ρ (τ (ν (Multiplicative.ofAdd t))) y).val =
        Complex.exp (s*(t : ℂ)) * ∑ j ∈ Finset.range N, b j * (t : ℂ)^j := by
    let g := τ (ν (Multiplicative.ofAdd t))
    have hlog : Real.log (((m(S) g).val : ℝ)) = t := by
      change Real.log (((m(S) (τ (ν (Multiplicative.ofAdd t)))).val : ℝ)) = t
      rw [hτ,hν,Real.log_exp]
    calc
      _ = sLocalThetaPrincipalPartCoeff ω c hc k (A(S, ω) g y.val) :=
        congrArg (sLocalThetaPrincipalPartCoeff ω c hc k) (hρ g y)
      _ = c g * ∑ j ∈ Finset.range N,
          sLocalThetaPrincipalPartCoeff ω c hc (k+j) y.val *
            (Real.log (((m(S) g).val : ℝ)) : ℂ)^j / (j.factorial : ℂ) :=
        gamma_action_laurent_class ω y.val c hc k hk g
      _ = _ := by
        apply congrArg₂ (fun u v : ℂ ↦ u*v) (hs t)
        apply Finset.sum_congr rfl
        intro j hj
        calc
          _ = sLocalThetaPrincipalPartCoeff ω c hc (k+j) y.val * (t : ℂ)^j / (j.factorial : ℂ) :=
            congrArg (fun w : ℂ ↦ sLocalThetaPrincipalPartCoeff ω c hc (k+j) y.val * w^j / (j.factorial : ℂ))
              (congrArg Complex.ofReal hlog)
          _ = b j * (t : ℂ)^j := by dsimp [b]; ring
  have hsa : s.re < a := by rw [← hw]; exact ha
  exact (exponential_polynomial_decay s a hsa N b).congr'
    (Eventually.of_forall fun t ↦ (congrArg (fun w : ℂ ↦ Real.exp (-a*t)*‖w‖) (he t)).symm)

private theorem gamma_finite_coeff_independent (ω : PontryaginDual J₁(S))
    (ι : Type*) [Finite ι] (j : ι → ΓIndex(ω,(Set.univ : Set Xₛ))) (hj : Injective j) :
    LinearIndependent ℂ (fun i ↦ ΓCoeff(ω,j i)) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  choose N hN using fun i ↦ sLocalGammaFiltration_iInf_mem_cutoff ω (j i).val.1
    (j i).property.1 (Finset.card_pos.mp ((j i).property.2.2.1.trans_le (j i).property.2.2.2))
  let M : depths := Finset.univ.sup N
  have hM (i : ι) : (j i).val.1 ∈ sLocalGammaPoleCutoff (F := F) (S := S) ω M := by
    obtain ⟨hc,w,hw,hcard⟩ := hN i
    refine ⟨hc,w,hw,hcard.trans ?_⟩
    have hle : N i ≤ M := Finset.le_sup (Finset.mem_univ i)
    exact_mod_cast hle w
  let e (i : ι) : ΓIndex(ω,sLocalGammaPoleCutoff (F := F) (S := S) ω M) :=
    ⟨(j i).val,(j i).property.1,hM i,(j i).property.2.2⟩
  have he : Injective e := by
    intro i k h
    apply hj
    exact Subtype.ext (congrArg (fun a : ΓIndex(ω,sLocalGammaPoleCutoff (F := F) (S := S) ω M) ↦ a.val) h)
  exact (sLocalGammaFiltration_coeff_independent ω M).2.comp e he

open Classical in
private theorem gamma_prefix_biorthogonal (ω : PontryaginDual J₁(S))
    (code : ΓIndex(ω,(Set.univ : Set Xₛ)) → ℕ)
    (hf : ∀ n, Finite {j : ΓIndex(ω,(Set.univ : Set Xₛ)) // code j = n}) (k : ℕ) :
    ∃ v : {j : ΓIndex(ω,(Set.univ : Set Xₛ)) // code j = k} → fullPV(ω),
      (∀ i j, code j < k → ΓCoeff(ω,j) (v i) = 0) ∧
      ∀ i j, (i = j → ΓCoeff(ω,j.val) (v i) = 1) ∧ (i ≠ j → ΓCoeff(ω,j.val) (v i) = 0) := by
  classical
  let I := {j : ΓIndex(ω,(Set.univ : Set Xₛ)) // code j ≤ k}
  let B := {j : ΓIndex(ω,(Set.univ : Set Xₛ)) // code j = k}
  letI : Finite I := finite_code_prefix _ code hf k
  letI : Fintype I := Fintype.ofFinite I
  have hli := gamma_finite_coeff_independent ω I Subtype.val Subtype.val_injective
  have hs := finite_interpolation (fullPV(ω)) I (fun j ↦ ΓCoeff(ω,j.val)) hli
  choose v hv using fun i : B ↦ hs (fun j : I ↦ if j.val = i.val then 1 else 0)
  refine ⟨v,?_,?_⟩
  · intro i j hj
    have hne : j ≠ i.val := by
      intro h
      have hi := i.property
      rw [← h] at hi
      omega
    exact (congrFun (hv i) ⟨j,le_of_lt hj⟩).trans (if_neg hne)
  · intro i j
    have h := congrFun (hv i) (⟨j.val,le_of_eq j.property⟩ : I)
    constructor
    · intro hij
      exact h.trans (if_pos (congrArg Subtype.val hij).symm)
    · intro hij
      exact h.trans (if_neg (fun he ↦ hij (Subtype.ext he.symm)))

private theorem gamma_coeff_kernel_invariant (ω : PontryaginDual J₁(S))
    (ρ : J(S) →* (fullPV(ω) →L[ℂ] fullPV(ω)))
    (hρ : ∀ g x, (ρ g x).val = A(S, ω) g x.val)
    (U : Xₛ → Prop) (x : fullPV(ω))
    (hx : ∀ j : ΓIndex(ω,(Set.univ : Set Xₛ)), U j.val.1 → ΓCoeff(ω,j) x = 0)
    (g : J(S)) (j : ΓIndex(ω,(Set.univ : Set Xₛ))) (hj : U j.val.1) :
    ΓCoeff(ω,j) (ρ g x) = 0 := by
  have hk : j.val.2 ≤ sLocalRhoPoleOrder j.val.1 := by
    rw [sLocalRhoPoleOrder_eq_card_polePlaces]
    exact j.property.2.2.2.trans (Nat.le_add_right _ _)
  change sLocalThetaPrincipalPartCoeff ω j.val.1 j.property.1 j.val.2 (ρ g x).val = 0
  calc
    _ = sLocalThetaPrincipalPartCoeff ω j.val.1 j.property.1 j.val.2 (A(S, ω) g x.val) :=
      congrArg (sLocalThetaPrincipalPartCoeff ω j.val.1 j.property.1 j.val.2) (hρ g x)
    _ = j.val.1 g * ∑ r ∈ Finset.range (sLocalRhoPoleOrder j.val.1-j.val.2+1),
        sLocalThetaPrincipalPartCoeff ω j.val.1 j.property.1 (j.val.2+r) x.val *
          (Real.log (((m(S) g).val : ℝ)) : ℂ)^r / (r.factorial : ℂ) :=
      gamma_action_laurent_class ω x.val j.val.1 j.property.1 j.val.2 hk g
    _ = 0 := by
      have hz (r : ℕ) : sLocalThetaPrincipalPartCoeff ω j.val.1 j.property.1 (j.val.2+r) x.val = 0 := by
        by_cases hr : j.val.2+r ≤ (arch(j.val.1)).card
        · let j' : ΓIndex(ω,(Set.univ : Set Xₛ)) :=
            ⟨(j.val.1,j.val.2+r),j.property.1,Set.mem_univ _,by have := j.property.2.2.1; omega,hr⟩
          exact hx j' hj
        · exact gamma_high_coeff_zero ω x j.val.1 j.property.1 _ (Nat.lt_of_not_ge hr)
      rw [Finset.sum_eq_zero (fun r hr ↦ by rw [hz,zero_mul,zero_div]),mul_zero]

private theorem gamma_coded_kernel (ω : PontryaginDual J₁(S))
    (ρ : J(S) →* (fullPV(ω) →L[ℂ] fullPV(ω)))
    (hρ : ∀ g x, (ρ g x).val = A(S, ω) g x.val)
    (code : ΓIndex(ω,(Set.univ : Set Xₛ)) → ℕ)
    (he : ∀ i j, code i = code j ↔ i.val.1 = j.val.1)
    (p : ℕ → Prop) (g : J(S)) (x : fullPV(ω))
    (hx : ∀ j, p (code j) → ΓCoeff(ω,j) x = 0)
    (j : ΓIndex(ω,(Set.univ : Set Xₛ))) (hj : p (code j)) : ΓCoeff(ω,j) (ρ g x) = 0 := by
  apply gamma_coeff_kernel_invariant ω ρ hρ
    (fun c ↦ ∃ i, i.val.1 = c ∧ p (code i)) x ?_ g j ⟨j,rfl,hj⟩
  intro i ⟨l,hli,hl⟩
  have hcode := (he l i).mpr hli
  exact hx i (hcode ▸ hl)

private theorem gamma_unitary_interpolation (τ : ℝ≥0ˣ →ₜ* J(S)) (hτ : RightInverse τ (m(S)))
    (χ : PontryaginDual J(S)) (hχ : ∀ u, χ (τ u) = 1) :
    let ω := χ.comp (⟨(m(S)).ker.subtype, continuous_subtype_val⟩ : J₁(S) →ₜ* J(S))
    Surjective (fun (x : fullPV(ω)) (j : ΓIndex(ω,(Set.univ : Set Xₛ))) ↦ ΓCoeff(ω,j) x) := by
  classical
  intro ω
  obtain ⟨ν,hν⟩ := gamma_positive_flow
  obtain ⟨ρ,hρ⟩ := gamma_full_action ω
  obtain ⟨code,he,hf⟩ := gamma_block_code ω
  let g : Multiplicative ℝ →* J(S) := τ.toMonoidHom.comp ν
  let R (t : ℝ) := (ρ (g (Multiplicative.ofAdd (-t)))).toLinearMap
  have hV := gamma_prefix_biorthogonal ω code hf
  have hinv : ∀ t x, R t (R (-t) x) = x := by
    intro t x
    exact real_action_inverse _ (ρ.comp g) t x
  have hF := gamma_range_frechet F S ω
  apply surjective_of_translated_coefficients (fullPV(ω)) (ΓIndex(ω,(Set.univ : Set Xₛ))) hF
    (fun j ↦ ΓCoeff(ω,j)) code hf hV R hinv ?_ ?_ ?_
  · intro p t x hx j hj
    exact gamma_coded_kernel ω ρ hρ code he p (g (Multiplicative.ofAdd (-t))) x hx j hj
  · intro q hq
    apply gamma_action_bound χ (fun t ↦ g (Multiplicative.ofAdd (-t))) ?_ ?_ ρ hρ q hq
    · intro t
      change (((m(S) (τ (ν (Multiplicative.ofAdd (-t))))).val : ℝ)) = _
      rw [hτ,hν]
    · intro t
      exact hχ _
  · intro a
    let weight (j : ΓIndex(ω,(Set.univ : Set Xₛ))) :=
      Real.log ‖j.val.1 (τ (Units.mk0 2 two_ne_zero))‖ / Real.log 2
    have hbad : Set.Finite {j : ΓIndex(ω,(Set.univ : Set Xₛ)) | a ≤ weight j} :=
      gamma_finite_indices_above ω τ hτ a
    let K := hbad.toFinset.sup code + 1
    refine ⟨K,fun j hj y ↦ ?_⟩
    have hweight : weight j < a := by
      by_contra h
      have hmem : j ∈ hbad.toFinset := hbad.mem_toFinset.mpr (le_of_not_gt h)
      have hb : code j ≤ hbad.toFinset.sup code := Finset.le_sup hmem
      dsimp [K] at hj
      omega
    have hk : j.val.2 ≤ sLocalRhoPoleOrder j.val.1 := by
      rw [sLocalRhoPoleOrder_eq_card_polePlaces]
      exact j.property.2.2.2.trans (Nat.le_add_right _ _)
    have h := gamma_coefficient_decay ω τ hτ ν hν ρ hρ j.val.1 j.property.1 j.val.2 hk a hweight y
    change Tendsto (fun t : ℝ ↦ Real.exp (-a*t) *
      ‖sLocalThetaPrincipalPartCoeff ω j.val.1 j.property.1 j.val.2
        (ρ (τ (ν (Multiplicative.ofAdd (-(-t))))) y).val‖) atTop (𝓝 0)
    simpa only [neg_neg] using h

end GammaInterpolationHelpers

/-- Paper: Theorem 7.3.4.1(4), p. 365.
Every array of archimedean principal parts on the component is realized by one
class in the full finite principal-value range.
Deviation: States explicitly the interpolation needed for the canonical product model. -/
theorem sLocalGamma_all_coeff_surjective (ω : PontryaginDual J₁(S)) :
    Function.Surjective (fun (x : fullPV(ω)) (j : ΓIndex(ω, (Set.univ : Set Xₛ))) ↦
      ΓCoeff(ω, j) x) := by
  obtain ⟨τ,hτ⟩ := sIdeleQuotientNorm_exists_section F S
  obtain ⟨χ,⟨hω,hχ⟩,_⟩ := existsUnique_sLocalNormSectionCharacter τ hτ ω
  subst ω
  exact gamma_unitary_interpolation τ hτ χ hχ



/-- A surjective continuous linear map from a Fréchet space onto a countable product of
complex lines is open. -/
private theorem sLocalGammaOrbitalQuotient_coeff_isOpenMap {Q ι : Type*} [AddCommGroup Q]
    [Module ℂ Q] [TopologicalSpace Q] [IsTopologicalAddGroup Q] [ContinuousSMul ℂ Q]
    [Countable ι] (hQ : IsFrechetTVS Q) (L : Q →L[ℂ] (ι → ℂ))
    (hL : Function.Surjective L) : IsOpenMap L := by
  obtain ⟨_, _, hmet, hcomplete⟩ := hQ
  let : UniformSpace Q := IsTopologicalAddGroup.rightUniformSpace Q
  have : IsUniformAddGroup Q := isUniformAddGroup_of_addCommGroup
  have : CompleteSpace Q := hcomplete
  have := hmet
  refine isOpenMap_of_not_isMeagre_range L ?_
  rw [hL.range_eq]
  exact not_isMeagre_of_isOpen isOpen_univ Set.univ_nonempty

/-- The archimedean Laurent coefficients identify the archimedean polar quotient with the
product of complex lines indexed by centers and orders. -/
private theorem sLocalGammaOrbitalQuotient_coeff_equiv (ω : PontryaginDual J₁(S)) :
    ∃ Ψ : (fullPV(ω) ⧸ Γker(ω)) ≃L[ℂ] (ΓIndex(ω, (Set.univ : Set Xₛ)) → ℂ),
      ∀ (x : fullPV(ω)) (j : ΓIndex(ω, (Set.univ : Set Xₛ))),
        Ψ ((Γker(ω)).mkQ x) j = ΓCoeff(ω, j) x := by
  have := sLocalGammaOrbitalQuotient_coeff_countable ω
  let Φ : fullPV(ω) →L[ℂ] (ΓIndex(ω, (Set.univ : Set Xₛ)) → ℂ) :=
    ContinuousLinearMap.pi fun j ↦ ΓCoeff(ω, j)
  have hker : Γker(ω) ≤ LinearMap.ker Φ.toLinearMap := fun x hx ↦
    funext fun j ↦ (sLocalGammaOrbitalQuotient_coeff_ker ω x).mp hx j
  let L := (Γker(ω)).liftQ Φ.toLinearMap hker
  have hcont : Continuous L :=
    (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.mpr Φ.continuous
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot]
    refine Submodule.ker_liftQ_eq_bot _ _ _ fun x hx ↦ ?_
    exact (sLocalGammaOrbitalQuotient_coeff_ker ω x).mpr fun j ↦ congrFun hx j
  have hsurj : Function.Surjective L := fun v ↦ by
    obtain ⟨x, hx⟩ := sLocalGamma_all_coeff_surjective ω v
    exact ⟨(Γker(ω)).mkQ x, hx⟩
  let e := LinearEquiv.ofBijective L ⟨hinj, hsurj⟩
  have hopen : IsOpenMap L :=
    sLocalGammaOrbitalQuotient_coeff_isOpenMap (sLocalGammaOrbitalQuotient_frechet ω)
      ⟨L, hcont⟩ hsurj
  let h := e.toEquiv.toHomeomorphOfContinuousOpen hcont hopen
  exact ⟨{ e with continuous_toFun := hcont, continuous_invFun := h.symm.continuous },
    fun x j ↦ rfl⟩

/-- If a product of lines is identified with a quotient by coefficient functionals, each of
which already vanishes on one of a family of larger subspaces, then the maps to the quotients by
that family induce the topology of the quotient. -/
private theorem sLocalGammaOrbitalQuotient_projectiveTopology_inducing {E ι κ : Type*}
    {_ : AddCommGroup E} {_ : Module ℂ E} {_ : TopologicalSpace E}
    (P : Submodule ℂ E) (stage : κ → Submodule ℂ E) (hle : ∀ N, P ≤ stage N)
    (φ : ι → StrongDual ℂ E) (Ψ : E ⧸ P → ι → ℂ) (hΨi : IsInducing Ψ)
    (hΨ : ∀ (x : E) (j : ι), Ψ (P.mkQ x) j = φ j x)
    (hN : ∀ j, ∃ N, ∀ x ∈ stage N, φ j x = 0) :
    IsInducing (fun (x : E ⧸ P) (N : κ) ↦ P.mapQ (stage N) LinearMap.id (hle N) x) := by
  let ℓ (j : ι) : (E ⧸ stage (hN j).choose) →ₗ[ℂ] ℂ :=
    (stage (hN j).choose).liftQ (φ j).toLinearMap fun x hx ↦ (hN j).choose_spec x hx
  have hℓ (j : ι) : Continuous (ℓ j) :=
    (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.mpr (φ j).continuous
  let H : ((N : κ) → E ⧸ stage N) → (ι → ℂ) := fun y j ↦ ℓ j (y (hN j).choose)
  have hH : Continuous H := continuous_pi fun j ↦ (hℓ j).comp (continuous_apply _)
  have hF : Continuous (fun (x : E ⧸ P) (N : κ) ↦ P.mapQ (stage N) LinearMap.id (hle N) x) :=
    continuous_pi fun N ↦ (QuotientAddGroup.isQuotientMap_mk P.toAddSubgroup).continuous_iff.mpr
      (QuotientAddGroup.isQuotientMap_mk (stage N).toAddSubgroup).continuous
  have hcomp : H ∘ (fun (x : E ⧸ P) (N : κ) ↦ P.mapQ (stage N) LinearMap.id (hle N) x) =
      fun x ↦ Ψ x := by
    funext x j
    obtain ⟨x, rfl⟩ := P.mkQ_surjective x
    exact (hΨ x j).symm
  refine IsInducing.of_comp hF hH ?_
  rw [hcomp]
  exact hΨi

/-- Each archimedean Laurent coefficient vanishes on some stage of the filtration. -/
private theorem sLocalGammaOrbitalQuotient_projectiveTopology_cutoff (ω : PontryaginDual J₁(S))
    (j : ΓIndex(ω, (Set.univ : Set Xₛ))) : ∃ N : depths,
      ∀ x ∈ sLocalGammaFiltration (F := F) (S := S) ω N, ΓCoeff(ω, j) x = 0 := by
  obtain ⟨N, hN⟩ := sLocalGammaFiltration_iInf_mem_cutoff ω j.val.1 j.property.1
    (Finset.card_pos.mp (j.property.2.2.1.trans_le j.property.2.2.2))
  exact ⟨N, fun x hx ↦
    (Submodule.mem_iInf _).mp hx ⟨j.val, j.property.1, hN, j.property.2.2⟩⟩

/-- The statement of `sLocalGammaOrbitalQuotient_projectiveTopology` with its abbreviations
expanded. -/
private theorem sLocalGammaOrbitalQuotient_projectiveTopology_aux (ω : PontryaginDual J₁(S)) :
    ∃ qN : (N : depths) → (fullPV(ω) ⧸ Γker(ω)) →ₗ[ℂ]
        (fullPV(ω) ⧸ sLocalGammaFiltration (F := F) (S := S) ω N),
      (∀ N (x : fullPV(ω)), qN N ((Γker(ω)).mkQ x) = (sLocalGammaFiltration ω N).mkQ x) ∧
      IsInducing (fun (x : fullPV(ω) ⧸ Γker(ω)) (N : depths) ↦ qN N x) := by
  have hle (N : depths) : Γker(ω) ≤ sLocalGammaFiltration (F := F) (S := S) ω N := by
    rw [← sLocalGammaFiltration_iInf]
    exact iInf_le _ N
  have h := sLocalGammaOrbitalQuotient_coeff_equiv ω
  have k := sLocalGammaOrbitalQuotient_projectiveTopology_inducing (Γker(ω))
      (sLocalGammaFiltration (F := F) (S := S) ω) hle (fun j ↦ ΓCoeff(ω, j)) h.choose
      h.choose.toHomeomorph.isInducing (fun x j ↦ by
        have := h.choose_spec x j
        rw [this])
      (fun j ↦ by
        obtain ⟨N, hN⟩ := sLocalGammaOrbitalQuotient_projectiveTopology_cutoff ω j
        refine ⟨N, fun x hx ↦ ?_⟩
        have := hN x hx
        rw [this])
  exact ⟨fun N ↦ (Γker(ω)).mapQ (sLocalGammaFiltration (F := F) (S := S) ω N) LinearMap.id (hle N),
    fun N x ↦ rfl, k⟩

/-- Paper: Theorem 7.3.4.1(4), p. 365.
The quotient topology is induced by the family of canonical finite-cutoff quotient maps. -/
theorem sLocalGammaOrbitalQuotient_projectiveTopology (ω : PontryaginDual J₁(S)) :
    let E := ↥(fullPV(ω))
    let P := Γker(ω)
    let stage := sLocalGammaFiltration (F := F) (S := S) ω
    ∃ qN : (N : depths) → (E ⧸ P) →ₗ[ℂ] (E ⧸ stage N),
      (∀ N (x : E), qN N (P.mkQ x) = (stage N).mkQ x) ∧
      IsInducing (fun (x : E ⧸ P) (N : depths) ↦ qN N x) := by
  exact sLocalGammaOrbitalQuotient_projectiveTopology_aux ω

/-- Paper: Theorem 7.3.4.1(4), p. 365.
The quotient is topologically linearly isomorphic to the product of complex
lines indexed by cutoff tuples. -/
theorem sLocalGammaOrbitalQuotient_product (ω : PontryaginDual J₁(S)) :
    let E := ↥(fullPV(ω))
    let P := Γker(ω)
    Nonempty ((E ⧸ P) ≃L[ℂ] (depths → ℂ)) := by
  intro E P
  obtain ⟨Ψ, -⟩ := sLocalGammaOrbitalQuotient_coeff_equiv ω
  have := sLocalGammaOrbitalQuotient_coeff_countable ω
  have := sLocalGammaOrbitalQuotient_coeff_infinite ω
  let := Encodable.ofCountable (ΓIndex(ω, (Set.univ : Set Xₛ)))
  let := Denumerable.ofEncodableOfInfinite (ΓIndex(ω, (Set.univ : Set Xₛ)))
  let := Encodable.ofCountable depths
  let := Denumerable.ofEncodableOfInfinite depths
  let e : ΓIndex(ω, (Set.univ : Set Xₛ)) ≃ depths :=
    (Denumerable.eqv _).trans (Denumerable.eqv depths).symm
  exact ⟨Ψ.trans (ContinuousLinearEquiv.piCongrLeft ℂ (fun _ : depths ↦ ℂ) e)⟩

/-- The strong dual of a space identified with a countably infinite product of complex lines is
the direct sum of complex lines over the same index with its finest locally convex topology. The
product is identified with formal power series, whose strong dual is the space of polynomials. -/
private theorem sLocalGammaOrbitalQuotient_dual_directSum_of_equiv {Q ι : Type*}
    [AddCommGroup Q] [Module ℂ Q] [TopologicalSpace Q]
    (Ψ : Q ≃L[ℂ] (ι → ℂ)) (σ : ℕ ≃ ι) :
    Nonempty (StrongDual ℂ Q ≃L[ℂ] FinestLocallyConvex (ι →₀ ℂ)) := by
  obtain ⟨t, _⟩ := realSchwartzTaylor_equiv
  obtain ⟨p, _⟩ := realDiracDerivatives_polynomialEquiv
  let : TopologicalSpace (PowerSeries ℂ) := inferInstanceAs (TopologicalSpace ((Unit →₀ ℕ) → ℂ))
  let idx := (Finsupp.uniqueLinearEquiv ℕ ℕ ()).symm.toEquiv
  let series := ContinuousLinearEquiv.piCongrLeft ℂ (fun _ : Unit →₀ ℕ ↦ ℂ) idx
  let q : Q ≃L[ℂ] (ℕ → ℂ) :=
    Ψ.trans (ContinuousLinearEquiv.piCongrLeft ℂ (fun _ : ℕ ↦ ℂ) σ.symm)
  let e := (q.trans series).trans t.symm
  let d : FinestLocallyConvex (Polynomial ℂ) ≃L[ℂ] StrongDual ℂ Q :=
    p.trans (e.symm.arrowCongr (ContinuousLinearEquiv.refl ℂ ℂ))
  let l : FinestLocallyConvex (Polynomial ℂ) ≃ₗ[ℂ] FinestLocallyConvex (ι →₀ ℂ) :=
    (AddMonoidAlgebra.coeffLinearEquiv ℂ).trans (Finsupp.domLCongr σ)
  let := finestLocallyConvex_t2 (Polynomial ℂ)
  let := finestLocallyConvex_t2 (ι →₀ ℂ)
  have h := continuous_of_finestLocallyConvex (Polynomial ℂ) l.toLinearMap
  have h' := continuous_of_finestLocallyConvex (ι →₀ ℂ) l.symm.toLinearMap
  exact ⟨d.symm.trans ⟨l, h, h'⟩⟩

/-- Paper: Theorem 7.3.4.1(4), p. 365.
The strong dual of the quotient is topologically linearly isomorphic to the
direct sum of complex lines with its finest locally convex topology.
The quotient dual represents the annihilator via pullback along the quotient map. -/
theorem sLocalGammaOrbitalQuotient_dual_directSum (ω : PontryaginDual J₁(S)) :
    let E := ↥(fullPV(ω))
    let P := Γker(ω)
    Nonempty (StrongDual ℂ (E ⧸ P) ≃L[ℂ] FinestLocallyConvex (depths →₀ ℂ)) := by
  intro E P
  obtain ⟨Ψ⟩ := sLocalGammaOrbitalQuotient_product ω
  let := Encodable.ofCountable depths
  let := Denumerable.ofEncodableOfInfinite depths
  exact sLocalGammaOrbitalQuotient_dual_directSum_of_equiv Ψ (Denumerable.eqv depths).symm

/-- Paper: Theorem 7.3.4.1(5), pp. 365–366.
The set of archimedean centers with their admissible Laurent orders admits an enumeration. -/
theorem sLocalGammaIndex_enumerable (ω : PontryaginDual J₁(S)) :
    Nonempty (ℕ ≃ ΓIndex(ω, (Set.univ : Set Xₛ))) := by
  have := sLocalGammaOrbitalQuotient_coeff_countable ω
  have := sLocalGammaOrbitalQuotient_coeff_infinite ω
  let := Encodable.ofCountable (ΓIndex(ω, (Set.univ : Set Xₛ)))
  let := Denumerable.ofEncodableOfInfinite (ΓIndex(ω, (Set.univ : Set Xₛ)))
  exact ⟨(Denumerable.eqv _).symm⟩

/-- A continuous linear functional on a product of complex lines vanishes on every vector
whose coordinates vanish on some finite set of indices. -/
private theorem sLocalGammaOrbitalQuotient_dual_basis_finite {ι : Type*}
    (L : (ι → ℂ) →L[ℂ] ℂ) : ∃ T : Finset ι, ∀ y : ι → ℂ, (∀ i ∈ T, y i = 0) → L y = 0 := by
  have hU : L ⁻¹' Metric.ball 0 1 ∈ 𝓝 (0 : ι → ℂ) :=
    L.continuous.continuousAt.preimage_mem_nhds (by
      rw [map_zero]
      exact Metric.ball_mem_nhds 0 one_pos)
  rw [nhds_pi, Filter.mem_pi'] at hU
  obtain ⟨T, t, ht, hsub⟩ := hU
  refine ⟨T, fun y hy ↦ ?_⟩
  by_contra hne
  have h2 : L ((2 / L y) • y) = 2 := by
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hne]
  have hmem : (2 / L y) • y ∈ Set.pi (↑T) t := fun i hi ↦ by
    rw [Pi.smul_apply, hy i hi, smul_zero]
    exact mem_of_mem_nhds (ht i)
  have h1 := hsub hmem
  rw [Set.mem_preimage, h2, Metric.mem_ball, dist_zero_right] at h1
  norm_num at h1

/-- On a space identified with a product of complex lines indexed by an enumerated set, the
coordinate functionals form a Schauder basis of the strong dual, with evaluation at the
dual vectors as coefficient functionals. -/
private theorem sLocalGammaOrbitalQuotient_dual_basis_pi {Q ι : Type*} [AddCommGroup Q]
    [Module ℂ Q] [TopologicalSpace Q] [IsTopologicalAddGroup Q] [ContinuousSMul ℂ Q]
    [DecidableEq ι] (Ψ : Q ≃L[ℂ] (ι → ℂ)) (σ : ℕ ≃ ι) :
    IsSchauderBasis
      (fun n ↦ (ContinuousLinearMap.proj (σ n) : (ι → ℂ) →L[ℂ] ℂ).comp (Ψ : Q →L[ℂ] (ι → ℂ)))
      (fun n ↦ ContinuousLinearMap.applyₗ ℂ (RingHom.id ℂ) (Ψ.symm (Pi.single (σ n) 1))) := by
  refine ⟨fun m n ↦ ?_, fun ℓ ↦ ?_⟩
  · change Ψ (Ψ.symm (Pi.single (σ m) 1)) (σ n) = if m = n then 1 else 0
    rw [Ψ.apply_symm_apply, Pi.single_apply]
    by_cases hmn : m = n
    · subst hmn
      simp
    · have hne : σ n ≠ σ m := fun e ↦ hmn (σ.injective e).symm
      simp [hmn, hne]
  · obtain ⟨T, hT⟩ := sLocalGammaOrbitalQuotient_dual_basis_finite
      (ℓ.comp (Ψ.symm : (ι → ℂ) →L[ℂ] Q))
    have hzero (m : ℕ) (hm : σ m ∉ T) : ℓ (Ψ.symm (Pi.single (σ m) 1)) = 0 :=
      hT _ fun i hi ↦ by
        simp [show i ≠ σ m from fun e ↦ hm (e ▸ hi)]
    have hrep : ℓ = ∑ i ∈ T, ℓ (Ψ.symm (Pi.single i 1)) •
        (ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).comp (Ψ : Q →L[ℂ] (ι → ℂ)) := by
      ext q
      have hy := hT (Ψ q - ∑ i ∈ T, Ψ q i • Pi.single i (1 : ℂ)) fun i hi ↦ by
        simp [Finset.sum_apply, Pi.single_apply, hi]
      simp only [ContinuousLinearMap.comp_apply, map_sub, map_sum, map_smul,
        ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply,
        sub_eq_zero] at hy
      rw [hy]
      simp [mul_comm]
    let K := (T.image σ.symm).sup id + 1
    unfold HasSum
    rw [SummationFilter.conditional_filter_eq_map_range, Filter.tendsto_map'_iff]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop K] with k hk
    have hsub : T.map σ.symm.toEmbedding ⊆ Finset.range k := by
      intro m hm
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hm
      have hle : σ.symm i ≤ (T.image σ.symm).sup id :=
        Finset.le_sup (f := id) (Finset.mem_image_of_mem _ hi)
      change σ.symm i ∈ Finset.range k
      exact Finset.mem_range.mpr (by omega)
    symm
    change ∑ m ∈ Finset.range k, ℓ (Ψ.symm (Pi.single (σ m) 1)) •
        (ContinuousLinearMap.proj (σ m) : (ι → ℂ) →L[ℂ] ℂ).comp (Ψ : Q →L[ℂ] (ι → ℂ)) = ℓ
    rw [← Finset.sum_subset hsub fun m _ hm ↦ ?_, Finset.sum_map]
    · conv_rhs => rw [hrep]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      simp
    · have hσ : σ m ∉ T := fun h ↦ hm (Finset.mem_map.mpr ⟨σ m, h, by simp⟩)
      rw [hzero m hσ, zero_smul]

/-- On a quotient identified with a product of complex lines through coefficient
functionals, the descended coefficients in any enumeration form a Schauder basis of the
strong dual. -/
private theorem sLocalGammaOrbitalQuotient_dual_basis_quot {E ι : Type*} {_ : AddCommGroup E}
    {_ : Module ℂ E} {_ : TopologicalSpace E} (P : Submodule ℂ E)
    [IsTopologicalAddGroup (E ⧸ P)] [ContinuousSMul ℂ (E ⧸ P)] [DecidableEq ι]
    (φ : ι → StrongDual ℂ E) (Ψ : (E ⧸ P) ≃L[ℂ] (ι → ℂ))
    (hΨ : ∀ (x : E) (j : ι), Ψ (P.mkQ x) j = φ j x) (σ : ℕ ≃ ι) :
    ∃ (a : ℕ → StrongDual ℂ (E ⧸ P)) (d : ℕ → StrongDual ℂ (StrongDual ℂ (E ⧸ P))),
      (∀ n (x : E), a n (P.mkQ x) = φ (σ n) x) ∧ IsSchauderBasis a d :=
  ⟨_, _, fun n x ↦ hΨ x (σ n), sLocalGammaOrbitalQuotient_dual_basis_pi Ψ σ⟩

/-- The statement of `sLocalGammaOrbitalQuotient_dual_basis` with its abbreviations
expanded. -/
private theorem sLocalGammaOrbitalQuotient_dual_basis_aux (ω : PontryaginDual J₁(S))
    (σ : ℕ ≃ ΓIndex(ω, (Set.univ : Set Xₛ))) :
    ∃ (a : ℕ → StrongDual ℂ (fullPV(ω) ⧸ Γker(ω)))
      (d : ℕ → StrongDual ℂ (StrongDual ℂ (fullPV(ω) ⧸ Γker(ω)))),
      (∀ n (x : fullPV(ω)), a n ((Γker(ω)).mkQ x) = ΓCoeff(ω, (σ n)) x) ∧
      IsSchauderBasis a d := by
  classical
  have h := sLocalGammaOrbitalQuotient_coeff_equiv ω
  exact sLocalGammaOrbitalQuotient_dual_basis_quot (ι := ΓIndex(ω, (Set.univ : Set Xₛ)))
    (Γker(ω)) (fun j ↦ ΓCoeff(ω, j)) h.choose (fun x j ↦ by
      have := h.choose_spec x j
      rw [this]) σ

/-- Paper: Theorem 7.3.4.1(5), p. 365.
In every enumeration, the archimedean Laurent coefficients descend to a
Schauder basis of the strong dual of the archimedean polar quotient.
Deviation: Uses the coefficient of exponent −k for order k in (7.3.4.8). -/
theorem sLocalGammaOrbitalQuotient_dual_basis (ω : PontryaginDual J₁(S))
    (σ : ℕ ≃ ΓIndex(ω, (Set.univ : Set Xₛ))) :
    let E := ↥(fullPV(ω))
    let P := Γker(ω)
    ∃ (a : ℕ → StrongDual ℂ (E ⧸ P)) (d : ℕ → StrongDual ℂ (StrongDual ℂ (E ⧸ P))),
      (∀ n (x : E), a n (P.mkQ x) = ΓCoeff(ω, (σ n)) x) ∧
      IsSchauderBasis a d := by
  exact sLocalGammaOrbitalQuotient_dual_basis_aux ω σ

end ArchimedeanPoles

end RiemannMasullo
