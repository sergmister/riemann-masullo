module

public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec4
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.InfiniteAdeleRing

/-! # False claims printed in §7.4 -/

@[expose] public noncomputable section

open Classical Function IsDedekindDomain NumberField Set Topology
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false
set_option maxHeartbeats 150000
set_option Elab.async false

local notation "C[" F "]" => IdeleClassGroup (𝓞 F) F
local notation "I[" F "]" => IdeleGroup (𝓞 F) F
local notation "U[" F "]" => PontryaginDual (IdeleClassGroup (𝓞 F) F)
local notation "ω[" F ", " χ "]" => (χ : U[F]).comp
  (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ :
    (ideleClassNorm F).ker →ₜ* C[F])
local notation "B" => SchwartzBergman (univ : Set ℝ)

local instance instIdeleClassT2Sec4Printed (F : Type*) [Field F] [NumberField F] :
    T2Space C[F] := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.1

local instance instIdeleClassLocallyCompactSec4Printed (F : Type*) [Field F] [NumberField F] :
    LocallyCompactSpace C[F] := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.1

/-- Paper: Theorem 7.4.1.1(2), equation (7.4.1.1), p. 366.
The printed spectral trace evaluates the test at the unshifted zero z. Its summation
variable ρ is z + a, so the printed weight and multiplicity use ρ − a = z.
The cited §7.1.4.2 family lives in the unshifted quotient. To type the reference
for general a, use its transport by f(s) ↦ f(s+a), which gives evaluation at z−a.
At a = 0 the statement and its counterexample require no transport. -/
def Printed.spectralNuclearity_trace : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : U[F])
    (τ : ℝ≥0ˣ →ₜ* I[F]) (hτ : RightInverse τ (ideleNorm F)) (a : ℝ) (N : ℕ),
    0 < N → ∀ φ : BruhatCompactSupport C[F],
    let L := regularizedCompletedHeckeL χ τ hτ (continuedCompletedHeckeL χ)
      (continuedCompletedHeckeL_spec χ).1 (continuedCompletedHeckeL_spec χ).2
    let Zeros := {z : ℂ // 0 < analyticOrderAt (L.val : ℂ → ℂ) z}
    let order := fun z : Zeros ↦ (analyticOrderAt (L.val : ℂ → ℂ) z.val).toNat
    let J := Σ z : Zeros, Fin (order z)
    let D := spectralNuclearityDenominator χ τ hτ a
    let Q := SpectralNuclearityQuotient χ τ hτ a
    ∀ (d : J → StrongDual ℂ Q) (b : J → Q),
      (∀ i f, d i (D.mkQ f) = iteratedDeriv i.2.val f.val (i.1.val - (a : ℂ))) →
      (∀ i j, d i (b j) = if i = j then 1 else 0) →
      let E := (Submodule.span ℂ (b '' {i | i.2.val < N})).topologicalClosure
      letI _instSpectralUniformSec4Printed : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
      ∃ (A : B →L[ℂ] B) (Aq : Q →L[ℂ] Q) (T : E →L[ℂ] E),
        (∀ f s, (A f).val s = nuclearityTestMellin χ φ s * f.val s) ∧
        (∀ f, Aq (D.mkQ f) = D.mkQ (A f)) ∧
        (∀ x : E, (T x).val = Aq x.val) ∧ IsStronglyNuclearOperator T ∧
        ∀ r : NuclearPresentation T, HasSum
          (fun n ↦ r.coeff n * r.functional n (r.vector n).val)
          (∑' z : Zeros, ((min N (order z) : ℕ) : ℂ) * nuclearityTestMellin χ φ z.val)

/-- Paper: Theorem 7.4.1.1(2), equation (7.4.1.1), p. 366.
Take the trivial character of a field with a multiple central zeta zero, as on
p. 529, a = 0 and N = 1. A nonzero nonnegative radial test supported at norms
between 2 and 3 has positive Mellin derivative at 1/2. The first-derivative
functional there vanishes on the printed closed span, yet takes this positive
value on the ambient image of its zeroth biorthogonal vector. -/
theorem Printed.spectralNuclearity_trace_false : ¬ Printed.spectralNuclearity_trace := by sorry

open scoped TensorProduct in
/-- Paper: Equation (7.4.3.1), p. 368.
With the displayed projective tensor topology, multiplication of the two factors
realizes the tensor product as a closed subspace of adelic Schwartz functions. -/
def Printed.archFlatProjectiveTensorEmbedding : Prop :=
  ∀ (F : Type) [Field F] [NumberField F],
    let A := archimedeanFlatSchwartz (ι := {v : InfinitePlace F // v.IsReal})
      (κ := {v : InfinitePlace F // v.IsComplex})
    let V := SchwartzBruhat (Multiplicative (FiniteAdeleRing (𝓞 F) F))
    ∃ e : ProjectiveTensor (↥A) V →L[ℂ] SchwartzBruhat (Multiplicative 𝔸[F]),
      IsClosedEmbedding e ∧ ∀ (h : A) (g : V) (x : 𝔸[F]),
        e (h ⊗ₜ[ℂ] g) (Multiplicative.ofAdd x) =
          h.val (fun v ↦ InfinitePlace.Completion.ringEquivRealOfIsReal v.property (x.1 v.val),
            fun v ↦ InfinitePlace.Completion.ringEquivComplexOfIsComplex v.property (x.1 v.val)) *
          g (Multiplicative.ofAdd x.2)

/-- Paper: Equation (7.4.3.1), p. 368.
Over ℚ choose a basis of the finite test space and flat real functions supported
in (2,3). In the ambient locally convex direct sum one continuous seminorm can
use derivative order j on basis coordinate j. Projective continuity would
bound all those orders by one continuous archimedean seminorm with a separate
constant per coordinate. A fixed bump times exp(i n x) contradicts this bound. -/
theorem Printed.archFlatProjectiveTensorEmbedding_false :
    ¬ Printed.archFlatProjectiveTensorEmbedding := by sorry

/-- Paper: Theorem 7.4.3.1(1), p. 368.
The theta image of the printed unrestricted archimedean-flat tests is a nonzero
closed subspace contained in the zero-moment theta image. -/
def Printed.archNuclearityDenominator_nonzero_closed : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : U[F]),
    let q := (LinearMap.ker (homogeneousAdelicThetaLinearMap F (ω[F, χ]))).mkQ
    let D := (globalArchimedeanFlatTests F).map q
    D ≠ ⊥ ∧ IsClosed (D : Set (GlobalHomogeneousThetaSpace F (ω[F, χ]))) ∧
      D ≤ globalPolarFreeThetaSubmodule (ω[F, χ])

open MeasureTheory Filter in
open scoped RestrictedProduct ContDiff TensorProduct in
/-- The indicator of a compact open subgroup is a Schwartz–Bruhat function. -/
private theorem archNuclearityDenominator_indicator_mem {G : Type*} [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (H : Subgroup G) (hO : IsOpen (H : Set G)) (hK : IsCompact (H : Set G)) :
    (fun x : G ↦ if x ∈ H then (1 : ℂ) else 0) ∈ schwartzBruhatSubmodule G := by
  let : CompactSpace H := isCompact_iff_compactSpace.mp hK
  let : CompactSpace (lcaAnnihilator H) :=
    isCompact_iff_compactSpace.1 (isCompact_lcaAnnihilator H hO)
  let a : BruhatStructuralPair G :=
    ⟨⟨H, OrderDual.toDual H⟩, hO, isCompactlyGeneratedGroup_of_compact,
      ⟨H.isClosed_of_isOpen hO, isOpen_lcaAnnihilator H hK,
        (show IsCompactlyGeneratedGroup (lcaAnnihilator H) from
          isCompactlyGeneratedGroup_of_compact)⟩, le_rfl⟩
  have hsub : Subsingleton a.quotient := by
    refine ⟨fun x y ↦ ?_⟩
    induction x using QuotientGroup.induction_on with | H x => ?_
    induction y using QuotientGroup.induction_on with | H y => ?_
    exact QuotientGroup.eq.mpr (by
      change ((x⁻¹ * y : H) : G) ∈ H
      exact (x⁻¹ * y).property)
  let Z := ElementaryLieGroup 0 0 0 (Fin 1)
  have hZ : Subsingleton Z := by
    change Subsingleton (EuclideanSpace ℝ (Fin 0) × (Fin 0 → AddCircle (1 : ℝ)) ×
      (Fin 0 → ℤ) × Fin 1)
    infer_instance
  let j : a.quotient ≃* Multiplicative Z :=
    { toFun := fun _ ↦ 1
      invFun := fun _ ↦ 1
      left_inv := fun _ ↦ Subsingleton.elim _ _
      right_inv := fun _ ↦ @Subsingleton.elim _ hZ _ _
      map_mul' := fun _ _ ↦ (mul_one 1).symm }
  let e : ElementaryLCAPresentation a.quotient :=
    { realDim := 0, torusDim := 0, latticeRank := 0, finiteFactor := Fin 1
      equiv := j.toContinuousMulEquiv (fun S ↦ by
        rcases S.eq_empty_or_nonempty with h | h
        · subst h; simp
        · have : S = univ := by
            obtain ⟨z, hz⟩ := h
            exact eq_univ_of_forall fun w ↦ (@Subsingleton.elim _ hZ w z) ▸ hz
          subst this; simp) }
  let g : Z → ℂ := fun _ ↦ 1
  have hg : g ∈ elementarySchwartzSubmodule 0 0 0 (Fin 1) := by
    refine ⟨fun z b ↦ contDiff_const, fun i ↦ ?_⟩
    rw [Subsingleton.elim i (0, 0, 0, 0), elementarySchwartzBound_zero]
    simp [g]
  let s : SchwartzBruhatStage e := ⟨g, hg⟩
  apply Submodule.mem_iSup_of_mem a
  apply Submodule.mem_iSup_of_mem e
  refine ⟨s, funext fun x ↦ ?_⟩
  rw [schwartzBruhatStageRealization_apply]
  by_cases hx : x ∈ H
  · have hx' : x ∈ a.val.1 := hx
    simp [hx, hx', s, g]
  · have hx' : x ∉ a.val.1 := hx
    simp [hx, hx']



open MeasureTheory Filter in
open scoped RestrictedProduct ContDiff TensorProduct in
/-- The integral finite adeles form a compact open additive subgroup. -/
private def archNuclearityDenominator_integralSubgroup (F : Type) [Field F] [NumberField F] :
    Subgroup (Multiplicative (FiniteAdeleRing (𝓞 F) F)) where
  carrier := {x | ∀ v : HeightOneSpectrum (𝓞 F),
    (Multiplicative.toAdd x) v ∈ v.adicCompletionIntegers F}
  mul_mem' {a b} ha hb v := by
    change (Multiplicative.toAdd a + Multiplicative.toAdd b) v ∈ _
    exact add_mem (ha v) (hb v)
  one_mem' v := by
    change (0 : FiniteAdeleRing (𝓞 F) F) v ∈ _
    exact zero_mem _
  inv_mem' {a} ha v := by
    change (- Multiplicative.toAdd a) v ∈ _
    exact neg_mem (ha v)

open MeasureTheory Filter in
open scoped RestrictedProduct ContDiff TensorProduct in
/-- The integral finite adeles are open. -/
private theorem archNuclearityDenominator_integralSubgroup_isOpen (F : Type) [Field F]
    [NumberField F] :
    IsOpen (archNuclearityDenominator_integralSubgroup F : Set (Multiplicative (FiniteAdeleRing (𝓞 F) F))) := by
  let : Fact (∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    ⟨fun v ↦ Valued.isOpen_valuationSubring _⟩
  exact RestrictedProduct.isOpen_forall_mem Fact.out

open MeasureTheory Filter in
open scoped RestrictedProduct ContDiff TensorProduct in
/-- The integral finite adeles are compact. -/
private theorem archNuclearityDenominator_integralSubgroup_isCompact (F : Type) [Field F]
    [NumberField F] :
    IsCompact (archNuclearityDenominator_integralSubgroup F : Set (Multiplicative (FiniteAdeleRing (𝓞 F) F))) := by
  let (v : HeightOneSpectrum (𝓞 F)) : CompactSpace (v.adicCompletionIntegers F) :=
    compactSpace_adicCompletionIntegers v
  let : Fact (∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    ⟨fun v ↦ Valued.isOpen_valuationSubring _⟩
  have h := isCompact_range (RestrictedProduct.isEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 F) ↦ v.adicCompletion F)
    (A := fun v ↦ (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (𝓕 := Filter.cofinite)).continuous
  rw [RestrictedProduct.range_structureMap] at h
  exact h

open MeasureTheory Filter in
open scoped RestrictedProduct ContDiff TensorProduct in
/-- The indicator of the integral finite adeles is a Schwartz–Bruhat function. -/
private theorem archNuclearityDenominator_finiteIndicator_mem (F : Type) [Field F]
    [NumberField F] :
    (fun x : Multiplicative (FiniteAdeleRing (𝓞 F) F) ↦
      if x ∈ archNuclearityDenominator_integralSubgroup F then (1 : ℂ) else 0) ∈
      schwartzBruhatSubmodule (Multiplicative (FiniteAdeleRing (𝓞 F) F)) := by
  let : Fact (∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    ⟨fun v ↦ Valued.isOpen_valuationSubring _⟩
  let (v : HeightOneSpectrum (𝓞 F)) : CompactSpace (v.adicCompletionIntegers F) :=
    compactSpace_adicCompletionIntegers v
  let : LocallyCompactSpace (Multiplicative (FiniteAdeleRing (𝓞 F) F)) := by
    change LocallyCompactSpace (Πʳ v : HeightOneSpectrum (𝓞 F),
      [v.adicCompletion F, v.adicCompletionIntegers F])
    infer_instance
  let : IsTopologicalGroup (Multiplicative (FiniteAdeleRing (𝓞 F) F)) := inferInstance
  let : T2Space (Multiplicative (FiniteAdeleRing (𝓞 F) F)) := by
    change T2Space (Πʳ v : HeightOneSpectrum (𝓞 F),
      [v.adicCompletion F, v.adicCompletionIntegers F])
    infer_instance
  exact archNuclearityDenominator_indicator_mem _
    (archNuclearityDenominator_integralSubgroup_isOpen F)
    (archNuclearityDenominator_integralSubgroup_isCompact F)



open MeasureTheory Filter in
open scoped RestrictedProduct ContDiff TensorProduct in
/-- Over any number field there is an archimedean-flat adelic tensor whose Fourier value at
the origin is nonzero: a nonnegative bump away from the coordinate walls times the indicator
of the integral finite adeles. -/
private theorem archNuclearityDenominator_flat_fourier_ne_zero (F : Type) [Field F]
    [NumberField F] :
    ∃ f ∈ globalArchimedeanFlatTests F,
      adeleSchwartzFourier (F := F) f (Multiplicative.ofAdd 0) ≠ 0 := by
  let Coord := ({v : InfinitePlace F // v.IsReal} → ℝ) × ({v : InfinitePlace F // v.IsComplex} → ℂ)
  let c : Coord := (fun _ ↦ 1, fun _ ↦ 1)
  let b : ContDiffBump c := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  let bc : Coord → ℂ := fun u ↦ ((b u : ℝ) : ℂ)
  have hbc : ContDiff ℝ (⊤ : ℕ∞) bc := Complex.ofRealCLM.contDiff.comp b.contDiff
  have hbs : HasCompactSupport bc := b.hasCompactSupport.comp_left Complex.ofReal_zero
  let h₀ : SchwartzMap Coord ℂ := hbs.toSchwartzMap hbc
  have hflat : h₀ ∈ archimedeanFlatSchwartz (ι := {v : InfinitePlace F // v.IsReal})
      (κ := {v : InfinitePlace F // v.IsComplex}) := by
    apply mem_archimedeanFlatSchwartz_of_tsupport
    rw [Set.disjoint_left]
    intro u hu hw
    have hu' : u ∈ Metric.closedBall c (1 / 2) := by
      have : tsupport (h₀ : Coord → ℂ) ⊆ tsupport (b : Coord → ℝ) :=
        tsupport_comp_subset Complex.ofReal_zero _
      rw [b.tsupport_eq] at this
      exact this hu
    rw [Metric.mem_closedBall, dist_eq_norm] at hu'
    rcases hw with ⟨i, hi⟩ | ⟨j, hj⟩
    · have h1 : ‖(u - c).1 i‖ ≤ ‖u - c‖ := (norm_le_pi_norm _ i).trans (norm_fst_le _)
      have h2 : (u - c).1 i = -1 := by
        change u.1 i - 1 = -1
        rw [hi]; ring
      rw [h2] at h1
      norm_num at h1
      linarith
    · have h1 : ‖(u - c).2 j‖ ≤ ‖u - c‖ := (norm_le_pi_norm _ j).trans (norm_snd_le _)
      have h2 : (u - c).2 j = -1 := by
        change u.2 j - 1 = -1
        rw [hj]; ring
      rw [h2] at h1
      norm_num at h1
      linarith
  have hinf := (mem_archimedeanSchwartzBruhat_iff (F := F)
    (fun x ↦ h₀ (InfiniteAdeleRing.ringEquiv_mixedSpace F x))).mpr ⟨h₀, fun _ ↦ rfl⟩
  let fI : SchwartzBruhat (Multiplicative (InfiniteAdeleRing F)) := ⟨_, hinf⟩
  let H := archNuclearityDenominator_integralSubgroup F
  let g : SchwartzBruhat (Multiplicative (FiniteAdeleRing (𝓞 F) F)) :=
    ⟨_, archNuclearityDenominator_finiteIndicator_mem F⟩
  let tensor := (adeleSchwartz_inductiveTensor_equiv F).choose
  let test := tensor (fI ⊗ₜ[ℂ] g)
  refine ⟨test, Submodule.subset_span ⟨fI, g, ⟨h₀, hflat⟩, fun _ ↦ rfl, fun h ↦ h.elim, rfl⟩, ?_⟩
  let R : 𝔸[F] → ℝ := fun x ↦ b (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) *
    (if Multiplicative.ofAdd x.2 ∈ H then 1 else 0)
  have hR : ∀ x : 𝔸[F], test (Multiplicative.ofAdd x) = (R x : ℂ) := by
    intro x
    rw [(adeleSchwartz_inductiveTensor_equiv F).choose_spec fI g x]
    change bc _ * (if Multiplicative.ofAdd x.2 ∈ H then (1 : ℂ) else 0) = _
    simp only [R, bc]
    split_ifs <;> simp
  let : MeasurableSpace 𝔸[F] := borel _
  obtain ⟨hint, hval⟩ := adeleSchwartzFourier_apply_zero test
  rw [hval]
  have hfun : (fun x : 𝔸[F] ↦ test (Multiplicative.ofAdd x)) = fun x ↦ (R x : ℂ) := funext hR
  rw [hfun] at hint ⊢
  rw [integral_complex_ofReal, Complex.ofReal_ne_zero]
  have hRint : Integrable R (additiveTamagawaMeasure F) := by
    simpa using hint.re
  have hR0 : 0 ≤ R := fun x ↦ mul_nonneg b.nonneg (by split_ifs <;> norm_num)
  refine ne_of_gt ((integral_pos_iff_support_of_nonneg hR0 hRint).mpr ?_)
  let U : Set 𝔸[F] := (fun x : 𝔸[F] ↦ InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) ⁻¹'
      Metric.ball c (1 / 2) ∩ (fun x : 𝔸[F] ↦ Multiplicative.ofAdd x.2) ⁻¹' (H : Set _)
  have hU : IsOpen U := by
    refine IsOpen.inter (Metric.isOpen_ball.preimage ?_)
      ((archNuclearityDenominator_integralSubgroup_isOpen F).preimage ?_)
    · exact (continuous_infiniteAdeleRingEquivMixedSpace F).comp continuous_fst
    · exact continuous_ofAdd.comp continuous_snd
  have hUne : U.Nonempty := by
    refine ⟨((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm c, 0), ?_, ?_⟩
    · change InfiniteAdeleRing.ringEquiv_mixedSpace F
        ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm c) ∈ Metric.ball c (1 / 2)
      rw [RingEquiv.apply_symm_apply]
      exact Metric.mem_ball_self (by norm_num)
    · exact H.one_mem
  have hUsupp : U ⊆ Function.support R := by
    intro x hx
    have h1 : 0 < b (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) := b.pos_of_mem_ball hx.1
    have h2 : Multiplicative.ofAdd x.2 ∈ H := hx.2
    simp only [Function.mem_support, R, h2, ↓reduceIte, mul_one]
    exact h1.ne'
  have hμ : (additiveTamagawaMeasure F).IsAddHaarMeasure :=
    (additiveTamagawaMeasure_existsUnique F).exists.choose_spec.1
  have hpos := hU.measure_pos (additiveTamagawaMeasure F) hUne
  exact hpos.trans_le (measure_mono hUsupp)


open MeasureTheory Filter in
open scoped RestrictedProduct ContDiff TensorProduct in
/-- The norm-one idele classes have positive Tamagawa mass. -/
private theorem archNuclearityDenominator_volume_pos (F : Type) [Field F] [NumberField F] :
    0 < (normOneIdeleClassTamagawaMeasure F univ).toReal := by
  rw [normOneIdeleClassTamagawaMeasure_volume]
  have := NumberField.classNumber_pos F
  have := NumberField.Units.regulator_pos F
  have := NumberField.Units.torsionOrder_pos F
  have := Int.natAbs_pos.mpr (NumberField.discr_ne_zero F)
  exact ENNReal.toReal_pos (ENNReal.ofReal_pos.mpr (by positivity)).ne' ENNReal.ofReal_ne_top


open MeasureTheory Filter in
open scoped RestrictedProduct ContDiff TensorProduct in
/-- For the trivial norm-one character, equal homogeneous theta functions force equal Fourier
values at the origin, once both tests vanish at the origin and the second Fourier value is zero.
The polar term `|x|⁻¹ f̂(0)` blows up at small norm while the theta difference decays. -/
private theorem archNuclearityDenominator_fourier_eq_zero (F : Type) [Field F] [NumberField F]
    (ω₁ : PontryaginDual (ideleClassNorm F).ker) (hω : ω₁ = 1)
    (f g : SchwartzBruhat (Multiplicative 𝔸[F]))
    (hθ : homogeneousAdelicThetaLinearMap F ω₁ f = homogeneousAdelicThetaLinearMap F ω₁ g)
    (hf0 : f (Multiplicative.ofAdd 0) = 0) (hg0 : g (Multiplicative.ofAdd 0) = 0)
    (hgF : adeleSchwartzFourier (F := F) g (Multiplicative.ofAdd 0) = 0) :
    adeleSchwartzFourier (F := F) f (Multiplicative.ofAdd 0) = 0 := by
  subst hω
  dsimp only at hf0 hg0 hgF ⊢
  simp only [ofAdd_zero] at hf0 hg0 hgF ⊢
  obtain ⟨C₁, T₁, hC₁, hT₁, h₁⟩ := homogeneousAdelicTheta_decay_small 1 f 1
  obtain ⟨C₂, T₂, hC₂, hT₂, h₂⟩ := homogeneousAdelicTheta_decay_small 1 g 1
  beta_reduce at h₁ h₂
  set a := adeleSchwartzFourier (F := F) f 1
  set vol := (normOneIdeleClassTamagawaMeasure F univ).toReal
  have hvol : 0 < vol := archNuclearityDenominator_volume_pos F
  have hPf (x : IdeleClassGroup (𝓞 F) F) : homogeneousAdelicTheta_polarTerm 1 f x =
      vol • ((((ideleClassNorm F x : ℝ≥0) : ℝ))⁻¹ • a) := by
    simp [homogeneousAdelicTheta_polarTerm, hf0, vol, a]
  have hPg (x : IdeleClassGroup (𝓞 F) F) : homogeneousAdelicTheta_polarTerm 1 g x = 0 := by
    simp [homogeneousAdelicTheta_polarTerm, hg0, hgF]
  let T := min T₁ T₂
  have key (t : ℝ) (ht : 0 < t) (htT : t < T) : ‖a‖ ≤ (C₁ + C₂) / vol * t ^ 2 := by
    obtain ⟨x, hx⟩ := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.2.2.2.1
      (Units.mk0 (⟨t, ht.le⟩ : ℝ≥0) (fun h ↦ ht.ne' (congrArg Subtype.val h)))
    have hxt : (((ideleClassNorm F x : ℝ≥0) : ℝ)) = t := by rw [hx]; rfl
    have e1 := h₁ x (by rw [hxt]; exact htT.trans_le (min_le_left _ _))
    have e2 := h₂ x (by rw [hxt]; exact htT.trans_le (min_le_right _ _))
    rw [hxt, pow_one] at e1 e2
    rw [hPf, hxt] at e1
    rw [hPg, sub_zero] at e2
    have hθx : homogeneousAdelicTheta 1 f x = homogeneousAdelicTheta 1 g x :=
      DFunLike.congr_fun hθ x
    have hsplit : vol • (t⁻¹ • a) = homogeneousAdelicTheta 1 g x -
        (homogeneousAdelicTheta 1 f x - vol • (t⁻¹ • a)) := by
      rw [hθx]; ring
    have hn : ‖vol • (t⁻¹ • a)‖ ≤ C₁ * t + C₂ * t := by
      rw [hsplit]
      exact (norm_sub_le _ _).trans (by linarith)
    rw [norm_smul, norm_smul, Real.norm_of_nonneg hvol.le,
      Real.norm_of_nonneg (inv_nonneg.mpr ht.le)] at hn
    rw [div_mul_eq_mul_div, le_div_iff₀ hvol]
    have : vol * (t⁻¹ * ‖a‖) * t = ‖a‖ * vol := by field_simp
    nlinarith
  have hT : 0 < T := lt_min hT₁ hT₂
  have hlim : Tendsto (fun t : ℝ ↦ (C₁ + C₂) / vol * t ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun t : ℝ ↦ (C₁ + C₂) / vol * t ^ 2) (𝓝 0) (𝓝 ((C₁ + C₂) / vol * 0 ^ 2)) :=
      (continuous_const.mul (continuous_pow 2)).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), ‖a‖ ≤ (C₁ + C₂) / vol * t ^ 2 := by
    filter_upwards [Ioo_mem_nhdsGT hT] with t ht using key t ht.1 ht.2
  exact norm_le_zero_iff.mp (ge_of_tendsto hlim hev)

open MeasureTheory Filter in
/-- A flat test whose theta class is pole-free for the trivial norm-one character has
Fourier value zero at the origin. -/
private theorem archNuclearityDenominator_flat_fourier_eq_zero (F : Type) [Field F] [NumberField F]
    (ω₁ : PontryaginDual (ideleClassNorm F).ker) (hω : ω₁ = 1)
    (f : SchwartzBruhat (Multiplicative 𝔸[F])) (hf : f ∈ globalArchimedeanFlatTests F)
    (hle : (globalArchimedeanFlatTests F).map
      (LinearMap.ker (homogeneousAdelicThetaLinearMap F ω₁)).mkQ ≤
      globalPolarFreeThetaSubmodule ω₁) :
    adeleSchwartzFourier (F := F) f (Multiplicative.ofAdd 0) = 0 := by
  have hm := hle (Submodule.mem_map_of_mem hf)
  obtain ⟨g, hg0, hgF, hgq⟩ := (mem_globalPolarFreeThetaSubmodule ω₁ _).mp hm
  have hθ : homogeneousAdelicThetaLinearMap F ω₁ f = homogeneousAdelicThetaLinearMap F ω₁ g := by
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, LinearMap.mem_ker,
      map_sub, sub_eq_zero] at hgq
    exact hgq.symm
  exact archNuclearityDenominator_fourier_eq_zero F ω₁ hω f g hθ
    (globalArchimedeanFlatTests_zero_moments f hf).1 hg0 hgF

/-- Paper: Theorem 7.4.3.1(1), p. 368.
Over ℚ with the trivial character, tensor a nonnegative nonzero smooth bump
supported in (2,3) with the indicator of the finite integral adeles. The test is
archimedean-flat and its Fourier value at zero is its strictly positive integral.
That value survives on the trivial homogeneous theta quotient, so no zero-moment
test represents the same class. -/
theorem Printed.archNuclearityDenominator_nonzero_closed_false :
    ¬ Printed.archNuclearityDenominator_nonzero_closed := by
  intro h
  have hle := (h ℚ 1).2.2
  obtain ⟨f, hf, hF⟩ := archNuclearityDenominator_flat_fourier_ne_zero ℚ
  exact hF (archNuclearityDenominator_flat_fourier_eq_zero ℚ _
    (ContinuousMonoidHom.ext fun _ ↦ rfl) f hf hle)

local notation "Θ₀[" F ", " χ "]" => ↥(adelePolarSubspace F) ⧸
  LinearMap.ker ((homogeneousAdelicThetaLinearMap F (ω[F, χ])).domRestrict (adelePolarSubspace F))
local notation "gammaOrder(" χ ", " s ")" =>
  (analyticOrderAt (fun z ↦ (heckeGammaFactor χ z)⁻¹) s).toNat
local notation "Z(" χ ", " τ ", " hτ ")" => (exists_globalPolarThetaMellin χ τ hτ).choose
local notation "Aθ(" χ ", " τ ", " hτ ", " φ ")" => (exists_polarThetaNuclearityAction χ τ hτ φ).choose

/-- Paper: Theorem 7.4.3.1(2), p. 368.
The page subtracts one at the quasi-character |·|^(it₀), with χ = |·|^(−it₀)
when the norm-one restriction is trivial. The natural-number difference gives
exactly the allowed derivative orders, including the empty range off the pole set. -/
def Printed.archNuclearityMultiplicity {F : Type*} [Field F] [NumberField F] (χ : U[F])
    (τ : ℝ≥0ˣ →ₜ* I[F]) (hτ : RightInverse τ (ideleNorm F)) (s : ℂ) : ℕ :=
  let x := (existsUnique_ideleNormSection_character_phase χ τ hτ).exists.choose
  gammaOrder(χ, s) -
    (if ω[F, χ] = 1 ∧ ideleClassNormTwist χ s =
      ideleClassNormTwist (1 : U[F]) (-((x : ℂ) * Complex.I)) then 1 else 0)

/-- Paper: Theorem 7.4.3.1(2), p. 368.
The printed derivative indices use the multiplicity at the character specified on the page. -/
abbrev Printed.ArchNuclearityJetIndex {F : Type*} [Field F] [NumberField F] (χ : U[F])
    (τ : ℝ≥0ˣ →ₜ* I[F]) (hτ : RightInverse τ (ideleNorm F)) :=
  {j : ℂ × ℕ // j.2 < Printed.archNuclearityMultiplicity χ τ hτ j.1}

/-- Paper: Equation (7.4.3.4), p. 368. Evaluate a derivative at a printed jet index. -/
def Printed.archNuclearityJet {F : Type*} [Field F] [NumberField F] (χ : U[F])
    (τ : ℝ≥0ˣ →ₜ* I[F]) (hτ : RightInverse τ (ideleNorm F))
    (j : Printed.ArchNuclearityJetIndex χ τ hτ) : StrongDual ℂ (Θ₀[F, χ]) :=
  ((entireJet j.val.1 j.val.2).comp schwartzBergmanEntireInclusion).comp (Z(χ, τ, hτ))

section QuotientPredicates

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] {J : Type*}

/-- Paper: Theorem 7.4.3.1(2), p. 368. The strong closure of the derivative
span equals the annihilator of the denominator. -/
def Printed.JetsSpanAnnihilator (D : Submodule ℂ E) (jet : J → StrongDual ℂ E) : Prop :=
  ((Submodule.span ℂ (Set.range jet)).topologicalClosure : Set (StrongDual ℂ E)) =
    {ℓ | ∀ x : D, ℓ x.val = 0}

/-- Paper: Theorem 7.4.3.1(3), p. 368. The specified derivatives descend to a
Schauder basis of the strong quotient dual in each enumeration. -/
def Printed.HasQuotientJetBasis (D : Submodule ℂ E) (jet : J → StrongDual ℂ E) : Prop :=
  ∀ σ : ℕ ≃ J, ∃ (d : ℕ → StrongDual ℂ (E ⧸ D))
    (b : ℕ → StrongDual ℂ (StrongDual ℂ (E ⧸ D))),
    (∀ n (x : E), d n (D.mkQ x) = jet (σ n) x) ∧ IsSchauderBasis d b

/-- Paper: Equation (7.4.3.14), p. 373. The induced operator has the stated
matrix trace in each enumeration of the specified derivative basis. -/
def Printed.HasQuotientJetTrace (D : Submodule ℂ E) (jet : J → StrongDual ℂ E)
    (A : E →L[ℂ] E) (value : ℂ) : Prop :=
  Printed.HasQuotientJetBasis D jet ∧
    ∃ T : (E ⧸ D) →L[ℂ] (E ⧸ D), (∀ x : E, T (D.mkQ x) = D.mkQ (A x)) ∧
      ∀ (σ : ℕ ≃ J) (d : ℕ → StrongDual ℂ (E ⧸ D))
        (b : ℕ → StrongDual ℂ (StrongDual ℂ (E ⧸ D))),
        (∀ n (x : E), d n (D.mkQ x) = jet (σ n) x) → IsSchauderBasis d b →
          HasSum (fun n ↦ b n ((d n).comp T)) value

/-- Paper: Remark 7.4.3.3, p. 373. The action descends to a nonnuclear
endomorphism of the quotient. -/
def Printed.HasNonnuclearQuotientAction (D : Submodule ℂ E) (A : E →L[ℂ] E) : Prop :=
  letI : UniformSpace (E ⧸ D) := IsTopologicalAddGroup.rightUniformSpace (E ⧸ D)
  ∃ T : (E ⧸ D) →L[ℂ] (E ⧸ D), (∀ x : E, T (D.mkQ x) = D.mkQ (A x)) ∧
    ¬ Nonempty (NuclearPresentation T)

end QuotientPredicates

/-- Paper: Theorem 7.4.3.1(2), p. 368.
With the multiplicity exception as written on the page, the indicated derivatives
generate the annihilator of the flat image in the strong dual. -/
def Printed.archNuclearityJet_span : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : U[F])
    (τ : ℝ≥0ˣ →ₜ* I[F]) (hτ : RightInverse τ (ideleNorm F)),
    Printed.JetsSpanAnnihilator (archNuclearityDenominator χ) (Printed.archNuclearityJet χ τ hτ)

/-- Paper: Theorem 7.4.3.1(2), p. 368.
For χ = |·|^i over ℚ the printed index includes evaluation at s = −i. Let h be
a nonzero nonnegative bump in (2,3). The real test h(x) − 2 h(2x) is flat with
integral zero. With finite integer indicators its zeta value at the trivial
quasi-character is proportional to (1 − 2) ζ(0) times the nonzero Mellin moment
of h at zero. This jet is nonzero on the flat denominator. -/
theorem Printed.archNuclearityJet_span_false : ¬ Printed.archNuclearityJet_span := by sorry

/-- Paper: Theorem 7.4.3.1(3), p. 368.
Every enumeration of the printed derivatives gives a basis of the strong quotient dual. -/
def Printed.archNuclearityJet_basis : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : U[F])
    (τ : ℝ≥0ˣ →ₜ* I[F]) (hτ : RightInverse τ (ideleNorm F)),
    Printed.HasQuotientJetBasis (archNuclearityDenominator χ) (Printed.archNuclearityJet χ τ hτ)

/-- Paper: Theorem 7.4.3.1(3), p. 368.
The same flat test h(x) − 2 h(2x) has nonzero evaluation at the printed index
(−i, 0) for the rational character |·|^i. A functional on the quotient vanishes
on the class of this test. -/
theorem Printed.archNuclearityJet_basis_false : ¬ Printed.archNuclearityJet_basis := by sorry

/-- Paper: Equation (7.4.3.4), p. 368.
The unnormalized vertical integral in the printed jet formula is 2πi times the
inverse Mellin transform, so its logarithmic moment carries that factor. -/
def Printed.archNuclearityJet_apply : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : U[F])
    (τ : ℝ≥0ˣ →ₜ* I[F]) (hτ : RightInverse τ (ideleNorm F))
    (j : Printed.ArchNuclearityJetIndex χ τ hτ) (f : adelePolarSubspace F),
    let u := fun s ↦ globalIdelicZFunction f.val (ideleClassNormTwist χ s)
    let moment := fun t : ℝ ↦ (Real.log t : ℂ) ^ j.val.2 * mellinInv 0 u t
    iteratedDeriv j.val.2 u j.val.1 =
      (2 * (Real.pi : ℂ) * Complex.I) * mellin moment j.val.1

/-- Paper: Equation (7.4.3.4), p. 368.
For ℚ and the trivial character, take the jet at −2 of order zero. Tensor
exp(−πx²) − 3 exp(−4πx²) + 2 exp(−16πx²) with the finite integral indicator.
The coefficients make the two polar moments vanish. The x² coefficient is
−21π, so the simple archimedean Mellin pole at −2 cancels the simple zeta zero
with nonzero result. The missing factor therefore changes the value. -/
theorem Printed.archNuclearityJet_apply_false : ¬ Printed.archNuclearityJet_apply := by sorry

/-- Paper: Equation (7.4.3.14), p. 373. The printed gamma-pole sum with its
norm-character correction. -/
def Printed.archNuclearityTraceValue {F : Type*} [Field F] [NumberField F] (χ : U[F])
    (τ : ℝ≥0ˣ →ₜ* I[F]) (hτ : RightInverse τ (ideleNorm F)) (φ : BruhatCompactSupport C[F]) : ℂ :=
  let invΓ := fun z ↦ (heckeGammaFactor χ z)⁻¹
  let Poles := {z : ℂ // 0 < analyticOrderAt invΓ z}
  let term := fun z : Poles ↦
    ((analyticOrderAt invΓ z.val).toNat : ℂ) * nuclearityTestMellin χ φ z.val
  let x := (existsUnique_ideleNormSection_character_phase χ τ hτ).exists.choose
  let correction := if ω[F, χ] = 1 then
    nuclearityTestMellin (1 : U[F]) φ (-((x : ℂ) * Complex.I)) else 0
  (∑' z, term z) - correction

/-- Paper: Equation (7.4.3.14), p. 373.
The printed numerical expression changes when the same trivial norm-one
component is parametrized by the unitary norm power with exponent i.
A positive log-norm bump in (1/4,1/2) has real pole weights in both charts.
The correction in the shifted chart has strictly negative imaginary part. -/
theorem Printed.archNuclearityTraceValue_changes_in_norm_chart
    (τ : ℝ≥0ˣ →ₜ* I[ℚ]) (hτ : RightInverse τ (ideleNorm ℚ)) :
    ∃ (χ : U[ℚ]) (φ : BruhatCompactSupport C[ℚ]),
      (∀ g : C[ℚ], (χ g : ℂ) = ((((ideleClassNorm ℚ g).val : ℝ) : ℂ) ^ Complex.I)) ∧
      tsupport φ.val ⊆ {g : C[ℚ] | 1 < ((ideleClassNorm ℚ g).val : ℝ)} ∧
      Printed.archNuclearityTraceValue χ τ hτ φ ≠
        Printed.archNuclearityTraceValue (1 : U[ℚ]) τ hτ φ := by sorry

/-- Paper: Theorem 7.4.3.2(2), equation (7.4.3.14), p. 373.
The matrix trace in the derivative basis is the sum of its diagonal weights.
The printed correction to the gamma-pole series uses the norm to the power −ix₀. -/
def Printed.archNuclearity_trace : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : U[F])
    (τ : ℝ≥0ˣ →ₜ* I[F]) (hτ : RightInverse τ (ideleNorm F))
    (φ : BruhatCompactSupport C[F]),
    tsupport φ.val ⊆ {g : C[F] | 1 < ((ideleClassNorm F g).val : ℝ)} →
    Printed.HasQuotientJetTrace (archNuclearityDenominator χ) (Printed.archNuclearityJet χ τ hτ)
      (Aθ(χ, τ, hτ, φ)) (Printed.archNuclearityTraceValue χ τ hτ φ)

/-- Paper: Theorem 7.4.3.2(2), equation (7.4.3.14), p. 373.
Over ℚ take χ = |·|^i and a nonzero nonnegative radial bump with log-norm
support in (1/4,1/2). The selected gamma poles have parameters −i−2n, giving
real diagonal values in any claimed derivative basis, by the product rule.
The pole sum is real and the printed correction has strictly negative imaginary part. -/
theorem Printed.archNuclearity_trace_false : ¬ Printed.archNuclearity_trace := by
  intro hall
  apply Printed.archNuclearityJet_basis_false
  intro F _ _ χ τ hτ
  let φ : BruhatCompactSupport C[F] := ⟨0, (bruhatCompactSupportSubmodule C[F]).zero_mem⟩
  have hφ : φ.val = (0 : C[F] → ℂ) := rfl
  exact (hall F χ τ hτ φ (by rw [hφ, tsupport_zero]; exact empty_subset _)).1

/-- Paper: Remark 7.4.3.3, p. 373.
The remark asserts that the operator induced on the quotient is nonnuclear for
every test with the preceding support condition. Its argument uses the strong dual. -/
def Printed.archNuclearityStrongDual_not_nuclear : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : U[F])
    (τ : ℝ≥0ˣ →ₜ* I[F]) (hτ : RightInverse τ (ideleNorm F))
    (φ : BruhatCompactSupport C[F]),
    tsupport φ.val ⊆ {g : C[F] | 1 < ((ideleClassNorm F g).val : ℝ)} →
    Printed.HasNonnuclearQuotientAction (archNuclearityDenominator χ) (Aθ(χ, τ, hτ, φ))

/-- A zero endomorphism of any space with a uniformity has a nuclear presentation:
zero coefficients and functionals, with the Banach disc `{0}`. -/
private theorem archNuclearityStrongDual_not_nuclear_false_zero
    {E : Type*} [AddCommGroup E] [Module ℂ E] {_ : UniformSpace E}
    (T : E →L[ℂ] E) (hT : T = 0) : Nonempty (NuclearPresentation T) := by
  let S := Submodule.span ℂ ({0} : Set E)
  have hsub : ∀ x : S, x = 0 := by
    rintro ⟨x, hx⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    simp
  have hpre : ((↑) ⁻¹' ({0} : Set E) : Set S) = univ := by
    ext x
    simp [hsub x]
  have bB : Balanced ℂ ((↑) ⁻¹' ({0} : Set E) : Set S) := hpre ▸ balanced_univ
  have cB : Convex ℝ ((↑) ⁻¹' ({0} : Set E) : Set S) := hpre ▸ convex_univ
  have aB : Absorbent ℝ ((↑) ⁻¹' ({0} : Set E) : Set S) := hpre ▸ absorbent_univ
  have hss : ∀ x y : WithLocalSeminorm (gaugeSeminorm bB cB aB), x = y :=
    fun x y ↦ (hsub x).trans (hsub y).symm
  have hdisc : IsBanachDisc ({0} : Set E) :=
    { bounded := fun _ hV ↦ absorbs_zero_iff.mpr (mem_of_mem_nhds hV)
      balanced := bB
      convex := cB
      absorbent := aB
      separated := ⟨fun x y h ↦ (h (hss x y)).elim⟩
      complete := ⟨fun {f} _ ↦ ⟨0, fun U hU ↦ by
        have hU' : U = univ := Set.eq_univ_of_forall fun y ↦ hss 0 y ▸ mem_of_mem_nhds hU
        exact hU' ▸ Filter.univ_mem⟩⟩ }
  exact ⟨{ coeff := fun _ ↦ 0
           functional := fun _ ↦ 0
           disc := {0}
           isBanachDisc := hdisc
           vector := fun _ ↦ 0
           vector_mem := fun _ ↦ by simp
           summable_coeff := by simp
           equicontinuous := fun U hU ↦ Filter.Eventually.of_forall fun _ _ ↦ by
             simpa using refl_mem_uniformity hU
           hasSum := fun x ↦ by simp [hT] }⟩

/-- An endomorphism of a quotient module is zero when its graph is described by convolution
with the zero function, through a linear transform of representatives. -/
private theorem archNuclearityStrongDual_not_nuclear_false_action
    {N : Type*} {_ : AddCommGroup N} {_ : Module ℂ N} (P : Submodule ℂ N) (p : Submodule ℂ P)
    {_ : TopologicalSpace (P ⧸ p)}
    {G : Type*} {_ : CommGroup G} {_ : TopologicalSpace G} {_ : MeasurableSpace G}
    (μ : MeasureTheory.Measure G)
    (Θ : N → C(G, ℂ)) (hΘ : IsLinearMap ℂ Θ) (φv : G → ℂ) (hφv : φv = 0)
    (A : (P ⧸ p) →L[ℂ] (P ⧸ p))
    (hA : ∀ f g : P, A (Submodule.Quotient.mk f) = Submodule.Quotient.mk g ↔
      (Θ g.val : G → ℂ) = lcaConvolution μ φv (Θ f.val)) : A = 0 := by
  refine ContinuousLinearMap.ext fun x ↦ ?_
  rw [zero_apply]
  induction x using Quotient.inductionOn' with
  | h f =>
    refine ((hA f 0).mpr ?_).trans (Submodule.Quotient.mk_zero _)
    rw [ZeroMemClass.coe_zero, hΘ.map_zero, ContinuousMap.coe_zero, hφv]
    funext y
    simp [lcaConvolution]

/-- An endomorphism of a quotient induced by the zero operator is zero. -/
private theorem archNuclearityStrongDual_not_nuclear_false_induced
    {M : Type*} {_ : AddCommGroup M} {_ : Module ℂ M} {_ : TopologicalSpace M}
    (D : Submodule ℂ M) {_ : TopologicalSpace (M ⧸ D)}
    (A : M →L[ℂ] M) (hA : A = 0) (T : (M ⧸ D) →L[ℂ] (M ⧸ D))
    (hT : ∀ x : M, T (D.mkQ x) = D.mkQ (A x)) : T = 0 := by
  refine ContinuousLinearMap.ext fun q ↦ ?_
  obtain ⟨x, rfl⟩ := D.mkQ_surjective q
  rw [hT x, hA, zero_apply, map_zero, zero_apply]

/-- Paper: Remark 7.4.3.3, p. 373.
Take F = ℚ, the trivial character, and the zero Bruhat test. Its support is empty
and every multiplier derivative vanishes. The induced action and transpose have
rank zero and admit nuclear presentations. -/
theorem Printed.archNuclearityStrongDual_not_nuclear_false :
    ¬ Printed.archNuclearityStrongDual_not_nuclear := by
  intro h
  let τ : ℝ≥0ˣ →ₜ* I[ℚ] := ⟨ratIdeleNormSection, ratIdeleNormSection_continuous⟩
  have hτ : RightInverse τ (ideleNorm ℚ) := ratIdeleNormSection_rightInverse
  let φ : BruhatCompactSupport C[ℚ] := ⟨0, (bruhatCompactSupportSubmodule C[ℚ]).zero_mem⟩
  have hφ : φ.val = (0 : C[ℚ] → ℂ) := rfl
  obtain ⟨T, hT, hnot⟩ := h ℚ 1 τ hτ φ (by rw [hφ, tsupport_zero]; exact empty_subset _)
  have hspec := (exists_polarThetaNuclearityAction (1 : U[ℚ]) τ hτ φ).choose_spec.2
  have hA : (exists_polarThetaNuclearityAction (1 : U[ℚ]) τ hτ φ).choose = 0 := by
    refine archNuclearityStrongDual_not_nuclear_false_action _ _ _ _ ?_ _ ?_ _ hspec
    · exact homogeneousAdelicTheta_isLinear _
    · exact hφ
  have hT0 : T = 0 :=
    archNuclearityStrongDual_not_nuclear_false_induced _ _ hA T hT
  apply hnot
  apply archNuclearityStrongDual_not_nuclear_false_zero
  exact hT0

/-- Paper: Theorem 7.4.3.1(3)–(5), proof before (7.4.3.12), p. 371.
As printed: the images of the tests with both polar moments zero have
codimension two in the source and target homogeneous theta spaces.
This is the codimension assertion. See `globalThetaPolarValues_vanish_on_isotype_iff`,
`globalThetaPolarValues_surjective_on_trivial_isotype` and ERRATA F136. -/
def Printed.archNuclearity_polar_codimension_two : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (χ : U[F]),
    Subsingleton (CommRing.Pic ((S : Set (HeightOneSpectrum (𝓞 F))).integer F)) →
    ∀ hχ : ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ) ∈
        unramifiedOutside F S,
      let hω : NormOneCharacterUnramifiedOutside (ω[F, χ]) S := ⟨⟨_, hχ⟩, fun _ ↦ rfl⟩
      let ωₛ := sLocalNormOneCharacter S (ω[F, χ]) hω
      let Kₛ := LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap F S ωₛ)
      let Pₛ := (sAdelePolarSubspace F S).map Kₛ.mkQ
      Module.finrank ℂ (SLocalHomogeneousThetaSpace F S ωₛ ⧸ Pₛ) = 2 ∧
        Module.finrank ℂ (GlobalHomogeneousThetaSpace F (ω[F, χ]) ⧸
          globalPolarFreeThetaSubmodule (ω[F, χ])) = 2

/-- Paper: Theorem 7.4.3.1(3)–(5), proof before (7.4.3.12), p. 371.
Take F = ℚ, S with just the finite place over 5, and the even quadratic
character modulo 5. The idèle with component 2 at 5 and 1 elsewhere has norm
one and acts by −1 on the homogeneous component. If T is translation by
this idèle, (f − Tf)/2 has the class of f and both polar moments vanish.
The polar image is the whole target component, of codimension zero. -/
theorem Printed.archNuclearity_polar_codimension_two_false :
    ¬ Printed.archNuclearity_polar_codimension_two := by sorry

/-- Paper: Theorem 7.4.3.1(3)–(5), proof before (7.4.3.12), p. 371.
Each class of the flat tensor space displayed in (7.4.3.1) has a unique
S-local function in the tensor space (5.3.4.1) representing it. The graph
requires an additive Schwartz representative to which the theta map applies.
The prose following (7.4.3.1) also describes an archimedean moment condition.
The zero class used in F137 belongs to both readings. -/
def Printed.archNuclearity_existsUnique_localFlatRepresentative : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (χ : U[F]),
    Subsingleton (CommRing.Pic ((S : Set (HeightOneSpectrum (𝓞 F))).integer F)) →
    ∀ hχ : ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ) ∈
        unramifiedOutside F S,
      let hω : NormOneCharacterUnramifiedOutside (ω[F, χ]) S := ⟨⟨_, hχ⟩, fun _ ↦ rfl⟩
      let ωₛ := sLocalNormOneCharacter S (ω[F, χ]) hω
      let Kₛ := LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap F S ωₛ)
      let K := LinearMap.ker (homogeneousAdelicThetaLinearMap F (ω[F, χ]))
      let flat := Submodule.span ℂ {f : SAdeleRing F S → ℂ |
        ∃ (h : archimedeanFlatSchwartz (ι := {v : InfinitePlace F // v.IsReal})
            (κ := {v : InfinitePlace F // v.IsComplex}))
          (g : (v : S) → SchwartzBruhat (v.val.adicCompletion F)ˣ), ∀ a, f a =
            h.val (fun v ↦ InfinitePlace.Completion.ringEquivRealOfIsReal v.property (a.1 v.val),
              fun v ↦ InfinitePlace.Completion.ringEquivComplexOfIsComplex v.property (a.1 v.val)) *
              ∏ v : S, (if hv : a.2 v ≠ 0 then g v (Units.mk0 (a.2 v) hv) else 0)}
      ∀ x ∈ (globalArchimedeanFlatTests F).map K.mkQ,
        ∃! f : flat, ∃ (test : SchwartzBruhat (Multiplicative (SAdeleRing F S)))
            (y : SLocalHomogeneousThetaSpace F S ωₛ),
          (∀ a, test (Multiplicative.ofAdd a) = f.val a) ∧
            sLocalHomogeneousThetaToGlobal hω y = x ∧
            sLocalHomogeneousThetaPrincipalValue (Finset.Subset.refl S) ωₛ y = Kₛ.mkQ test

/-- Paper: Theorem 7.4.3.1(3)–(5), proof before (7.4.3.12), p. 371.
Take F = ℚ, S consisting of the real place, χ = 1 and the zero global class.
For a nonzero smooth bump h supported in (2, 3), use the local tests 0 and
x ↦ h(x) − h(−x). The latter is flat at zero and has integral zero.
Its S-unit theta sum at u is f(u) + f(−u) = 0. Finite principal value with
the empty selection is the identity, so both tests represent the zero class. -/
theorem Printed.archNuclearity_existsUnique_localFlatRepresentative_false :
    ¬ Printed.archNuclearity_existsUnique_localFlatRepresentative := by sorry

open MeasureTheory in
/-- Paper: Theorem 7.4.3.2(2), proof, equation (7.4.3.15), p. 373.
As printed: for any a, b > 0, the right upward integral minus the left upward
integral of the test Mellin transform times the gamma logarithmic derivative,
divided by 2πi, sums the positive gamma pole multiplicities in the open strip.
The ordinary line integrals must exist. See `archNuclearity_trace` and ERRATA F140. -/
def Printed.archNuclearity_gammaContour : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : U[F]) (φ : BruhatCompactSupport C[F]),
    tsupport φ.val ⊆ {g : C[F] | 1 < ((ideleClassNorm F g).val : ℝ)} →
    ∀ (a b : ℝ), 0 < a → 0 < b →
      let Γ := heckeGammaFactor χ
      let Φ := nuclearityTestMellin χ φ
      let integrand := fun z ↦ Φ z * (deriv Γ z / Γ z)
      let poles := {z : ℂ // z.re ∈ Ioo (-a) b ∧ 0 < gammaOrder(χ, z)}
      let onLine (σ y : ℝ) := integrand ((σ : ℂ) + (y : ℂ) * Complex.I)
      Integrable (onLine (-a)) ∧ Integrable (onLine b) ∧
        HasSum (fun z : poles ↦ (gammaOrder(χ, z.val) : ℂ) * Φ z.val)
          ((verticalLineIntegral integrand b - verticalLineIntegral integrand (-a)) /
            (2 * (Real.pi : ℂ) * Complex.I))

/-- Paper: Theorem 7.4.3.2(2), proof, equation (7.4.3.15), p. 373.
For F = ℚ, χ = 1 and a = b = 1, take a nonzero nonnegative radial bump
supported at norms in (2, 3). The only enclosed gamma pole is at zero, with
logarithmic derivative residue −1. The normalized integral gives −Φ(0)
and the printed sum gives Φ(0) > 0. Also, a = 2 puts a pole on the left line. -/
theorem Printed.archNuclearity_gammaContour_false : ¬ Printed.archNuclearity_gammaContour :=
  by sorry

end RiemannMasullo
