module

import all RiemannMasullo.Ch05_ThetaZSpaces.Sec1
import all RiemannMasullo.Ch05_ThetaZSpaces.Sec2
import all RiemannMasullo.Ch05_ThetaZSpaces.Sec5
import all RiemannMasullo.Ch07_SchauderBasesZeta.Sec2

public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec3a
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace
import RiemannMasullo.ForMathlib.MeasureTheory.Integral.ProdPi

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
private theorem sLocalPWTests_moments_surjective_zero_bump
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
        Tendsto u atTop (𝓝 x) := by sorry

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
        {g | bound⁻¹ ≤ ((ideleClassNorm F g).val : ℝ)} := by sorry

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
          {g | ((m(T) g).val : ℝ) ≤ bound} := by sorry

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
        {g | bound⁻¹ ≤ ((ideleClassNorm F g).val : ℝ)} := by sorry

end InvariantLevels

/-- A dilate of a compactly supported function by a self-homeomorphism is compactly supported,
and its support stays in a set whose preimage under the homeomorphism it contains. -/
private theorem sLocalInvariantPW_translate_support {G : Type*} [TopologicalSpace G]
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

/-- A level built from a Fourier region that is stable under shrinking by ideles of absolute
value at least one at the infinite places and one at the finite places is preserved by the
classes of norm at least one. The norm-one part of a class acts by a scalar, and the remaining
part is represented by a positive real at one infinite place. -/
private theorem sLocalInvariantPW_translate_level (hST : S ⊆ T) (K : Set (SAdeleRing F S))
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
      obtain ⟨b, hb⟩ := sLocalInvariantPW_translate_fourier gT
      refine (mem_sAdelePolarSubspace _).mpr ⟨?_, ?_⟩
      · refine (schwartzBruhatUnitTranslate_apply gT _ 0).trans ?_
        rw [mul_zero]
        exact h0
      · rw [hb, mul_zero, h1, mul_zero]

/-- Paper: Proposition 7.3.2.4(3), p. 356.
Left translation by an idele class of norm at least one preserves the invariant levels,
with or without the zero-moment constraint.
Deviation: Stated directly for the local norm-one character and the inclusion of stages. -/
theorem sLocalInvariantPW_translate (hST : S ⊆ T) {Y : ℝ} (_hY : 0 < Y)
    (D : Submodule ℂ (B(T))) (_hD : D = ⊤ ∨ D = Z₀(T))
    (ω : PontryaginDual J₁(T)) (g : J(T)) (_hg : large(g))
    (x : Θ(T, ω)) (_hx : x ∈ sLocalInvariantPW hST Y D ω) :
    A(T, ω) g x ∈ sLocalInvariantPW hST Y D ω := by
  refine sLocalInvariantPW_translate_level hST (sLocalPWProductRegion S Y) ?_ D _hD ω g _hg x _hx
  intro a ha1 ha2 y hy
  refine le_trans ?_ (show (∏ w : InfinitePlace F, ‖(a.val * y).1 w‖ ^ w.mult) *
    (∏ v : S, ‖(a.val * y).2 v‖) ≤ Y from hy)
  refine mul_le_mul ?_ ?_ (Finset.prod_nonneg fun v _ ↦ norm_nonneg _)
    (Finset.prod_nonneg fun w _ ↦ pow_nonneg (norm_nonneg _) _)
  · refine Finset.prod_le_prod₀ (fun w _ ↦ pow_nonneg (norm_nonneg _) _) fun w _ ↦ ?_
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ _
    change ‖y.1 w‖ ≤ ‖a.val.1 w * y.1 w‖
    rw [norm_mul]
    exact le_mul_of_one_le_left (norm_nonneg _) (ha1 w)
  · refine Finset.prod_le_prod₀ (fun v _ ↦ norm_nonneg _) fun v _ ↦ ?_
    change ‖y.2 v‖ ≤ ‖a.val.2 v * y.2 v‖
    rw [norm_mul, ha2 v, one_mul]

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
    (absPW(hST, X, χ)).map (PV(hRT, χ)) ≤ absPW(hST, size(R) * X, χ) := by sorry

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
    (invPW(hST, Y, χ)).map (PV(hRT, χ)) ≤ invPW(hST, size(R) * Y, χ) := by sorry

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
            PV(hRT, χ) (A(T, χ) g x.val) = A(T, χ) g (PV(hRT, χ) x.val) := by sorry

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
          ∀ x : W, e (((Rₚ₀(p, χ)).comap W.subtype).mkQ x) = (Rₚ(p, χ)).mkQ x.val := by sorry

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
              q (ψ j) ≤ C * (1 + |(n : ℝ)|) ^ d := by sorry

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
      ((¬ ∃ j : Iₚ(p, ω), j.val = (c n, k)) → a (Multiplicative.ofAdd n) = 0) := by sorry

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

-- TODO(paper-gap): The test list (7.3.4.9) does not separate the two coefficients
-- of a double real pole at cutoff (0,0). See ERRATA I169. Finite interpolation can
-- use translations of a test attaining the full pole order.

/-- Paper: Theorem 7.3.4.1(2), pp. 364–365.
The Laurent coefficients at the selected centers form a finite linearly independent family. -/
theorem sLocalGammaFiltration_coeff_independent (ω : PontryaginDual J₁(S)) (N : depths) :
    let U := sLocalGammaPoleCutoff (F := F) (S := S) ω N
    Finite (ΓIndex(ω, U)) ∧ LinearIndependent ℂ (fun j : ΓIndex(ω, U) ↦ ΓCoeff(ω, j)) := by sorry

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

-- TODO(paper-gap): ERRATA I168 applies to the appeal to §5.4 on p. 365.
-- Finite interpolation only gives a dense coefficient image in the product topology.
-- Simultaneous realization in the original space is a separate proof obligation.

/-- Paper: Theorem 7.3.4.1(4), p. 365.
Every array of archimedean principal parts on the component is realized by one
class in the full finite principal-value range.
Deviation: States explicitly the interpolation needed for the canonical product model. -/
theorem sLocalGamma_all_coeff_surjective (ω : PontryaginDual J₁(S)) :
    Function.Surjective (fun (x : fullPV(ω)) (j : ΓIndex(ω, (Set.univ : Set Xₛ))) ↦
      ΓCoeff(ω, j) x) := by sorry

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

/-- Paper: Theorem 7.3.4.1(4), p. 365.
The strong dual of the quotient is topologically linearly isomorphic to the
direct sum of complex lines with its finest locally convex topology.
The quotient dual represents the annihilator via pullback along the quotient map. -/
theorem sLocalGammaOrbitalQuotient_dual_directSum (ω : PontryaginDual J₁(S)) :
    let E := ↥(fullPV(ω))
    let P := Γker(ω)
    Nonempty (StrongDual ℂ (E ⧸ P) ≃L[ℂ] FinestLocallyConvex (depths →₀ ℂ)) := by sorry

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
