module

public import RiemannMasullo.Ch12_TraceGeometric.Sec2
public import RiemannMasullo.Ch11_ShellStructure.Sec2b
public import RiemannMasullo.AppB_AnalyticNT.Sec4b
public import RiemannMasullo.Ch06_LocalGlobal.Sec1
import all RiemannMasullo.AppB_AnalyticNT.Sec4b

/-! # S-local trace calculation

Masullo, §§12.3–12.4, pp. 514–519. The additive kernel, its sharp orbital mass,
and the diagonal integral on the idele quotient use different measures.
-/

@[expose] public noncomputable section

open Classical Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped ContDiff ENNReal NNReal NumberField.AdeleRing SchwartzMap Topology

namespace RiemannMasullo

-- TODO(paper-gap): §12.3, p. 514, contains only the heading and footnote 1
-- asking to include the section. No global-to-S-local comparison is stated.

set_option quotPrecheck false
set_option maxSynthPendingDepth 8

variable {F : Type*} [Field F] [NumberField F]
  {S : Finset (HeightOneSpectrum (𝓞 F))}

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instSIdeleQuotientMeasurableSpaceSec1
  instNormOneSIdeleQuotientMeasurableSpaceSec1 instSAdeleMeasurableSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instSIdeleLocallyCompactSec1
  instFiniteCompletionUnitsLocallyCompactSec4b

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "Aₛ" => SAdeleRing F S
local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "Jₛ" => SIdeleQuotient F S
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "Hₛ" =>
  Subgroup.map (Units.map ((adeleProjection F S).comp (integralAdelesOutside F S).subtype).toMonoidHom)
    (Units.map (integralAdeleDiagonal F S).toMonoidHom).range
local notation "classAtS(" g ")" => (QuotientGroup.mk (sIdeleInsertion F S g) : C𝔽)
local notation "modS(" x ")" => ((∏ w : InfinitePlace F, ‖(x : Aₛ).1 w‖ ^ w.mult) *
  ∏ v : S, ‖(x : Aₛ).2 v‖)
local notation "normS(" x ")" => (((sIdeleNorm F S x).val : ℝ))
local notation "νₛ" => sAdditiveTamagawaMeasure F S
local notation "μₛ" => sMultiplicativeTamagawaMeasure F S
local notation "μJ" => sLocalQuotientTamagawaMeasure F S
local notation "volume₁" => ((sLocalNormOneQuotientMeasure F S) univ).toReal
local notation "ψₛ" => sAdeleStandardCharacter F S
local notation "fourierₛ" => tamagawaFourier νₛ ψₛ
local notation "band(" L ")" => sLocalPWProductRegion (F := F) S L
local notation "testₛ" => SchwartzBruhat (Multiplicative Aₛ)
local notation "testAt(" f "," x ")" => (f : testₛ) (Multiplicative.ofAdd x)

local instance instSIdeleT2Sec4 : T2Space Iₛ := (sIdeleGroup_description F S).2.1

/-- Paper: (12.4.1.4), p. 515. The restriction of an outside-unit-invariant test admits
a compactly supported Bruhat lift whose S-unit periodization recovers the restriction.
Deviation: The inserted S-idele evaluates the global test before taking the quotient. -/
theorem exists_sLocalTraceLift
    (_hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F)))
    (φ : BruhatCompactSupport C𝔽)
    (_hOutside : ∀ (a : outsideIntegralIdeleUnits F S) (c : C𝔽),
      φ.val (QuotientGroup.mk a.val * c) = φ.val c) :
    ∃ f : BruhatCompactSupport Iₛ, ∀ g : Iₛ,
      HasSum (fun ξ : Hₛ ↦ f.val (ξ.val * g)) (φ.val (classAtS(g))) := by sorry

-- TODO(paper-gap): The operator A on p. 515 has an extra factor |x|^(1/2)
-- in its output. Step I computes the scalar kernel with that factor removed.
-- The asserted factorization through the revised Proposition 5.3.4.4 needs a
-- comparison of the actual norm-weighted spaces and operators.

/-- Paper: (12.4.1.5) and (12.4.1.7), p. 516. Acting on a test integrates its values
at the translated points against the lift weighted by the inverse square-root norm.
Deviation: The definition gives the scalar pairing of the distributional kernel. -/
def sLocalTraceDilationKernel (f : BruhatCompactSupport Iₛ) (b : Aₛ → ℂ) (x : Aₛ) : ℂ :=
  ∫ g : Iₛ, f.val g / (Real.sqrt (normS(g)) : ℂ) * b ((g⁻¹).val * x) ∂μₛ

/-- Continuity of a Bruhat-smooth function follows already from order zero
(ported from the private `continuous_of_bruhatSmooth` in Ch09 Sec3). -/
private theorem sLocalTraceDilationKernel_apply_zero_continuous {G : Type*} [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    {f : G → ℂ} (hf : IsBruhatSmooth f) : Continuous f := by
  classical
  obtain ⟨k, hk, _, hdesc⟩ := hf 0
  have hkc := hk.isCompact
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨U, hU, hU₁⟩ := exists_compact_mem_nhds (1 : G)
  let K := insert x (U ∪ (k : Set G))
  let H := Subgroup.closure K
  have hK : K ⊆ (H : Set G) := Subgroup.subset_closure
  have hK₁ : K ∈ 𝓝 (1 : G) := mem_of_superset hU₁ (subset_union_left.trans (subset_insert ..))
  have hH : IsOpen (H : Set G) := H.isOpen_of_mem_nhds (mem_of_superset hK₁ hK)
  let a : BruhatStructuralPair G :=
    ⟨(H, OrderDual.toDual k), hH,
      ⟨Subtype.val ⁻¹' K, continuous_subtype_val.continuousAt.preimage_mem_nhds hK₁,
        (H.isClosed_of_isOpen hH).isClosedEmbedding_subtypeVal.isCompact_preimage
          ((hU.union hkc).insert x), Subgroup.closure_preimage_eq_top K⟩,
      hk, subset_union_right.trans ((subset_insert ..).trans hK)⟩
  let e := Classical.choice a.elementary
  obtain ⟨f₀, hval, hsm⟩ := hdesc a rfl
  let q : EuclideanSpace ℝ (Fin e.torusDim) → (Fin e.torusDim → AddCircle (1 : ℝ)) :=
    fun t i ↦ (t i : AddCircle (1 : ℝ))
  have hq : IsOpenQuotientMap q :=
    (IsOpenQuotientMap.piMap (fun _ ↦ QuotientAddGroup.isOpenQuotientMap_mk)).comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin e.torusDim ↦ ℝ)).toHomeomorph.isOpenQuotientMap
  have hmodel : Continuous (fun y : ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor ↦
      f₀ (e.equiv.symm (Multiplicative.ofAdd y))) := by
    rw [← (Homeomorph.prodAssoc _ _ _).isOpenQuotientMap.continuous_comp_iff]
    refine continuous_prod_of_discrete_right.mpr fun zd ↦ ?_
    rw [← ((IsOpenQuotientMap.id (X := EuclideanSpace ℝ (Fin e.realDim))).prodMap hq).continuous_comp_iff]
    exact (hsm e zd.1 zd.2).continuous
  have hf₀ : Continuous f₀ := by
    simpa only [Function.comp_def, ofAdd_toAdd, ContinuousMulEquiv.symm_apply_apply]
      using hmodel.comp (show Continuous (fun z : a.quotient ↦ (e.equiv z).toAdd) from e.equiv.continuous)
  have hcont : Continuous (fun z : H ↦ f (z : G)) :=
    (hf₀.comp (QuotientGroup.continuous_mk (N := (OrderDual.ofDual a.val.2).comap a.val.1.subtype))).congr hval
  exact hH.isOpenEmbedding_subtypeVal.continuousAt_iff.mp (hcont.continuousAt (x := ⟨x, hK (mem_insert ..)⟩))

/-- Paper: (12.4.1.5) and (12.4.1.7), p. 516. At the origin each translated
evaluation is the test value at zero, and the kernel has the corresponding weighted mass. -/
theorem sLocalTraceDilationKernel_apply_zero (f : BruhatCompactSupport Iₛ) (b : testₛ) :
    Integrable (fun g ↦ f.val g / (Real.sqrt (normS(g)) : ℂ)) μₛ ∧
      sLocalTraceDilationKernel f (fun y ↦ testAt(b, y)) 0 =
        (∫ g : Iₛ, f.val g / (Real.sqrt (normS(g)) : ℂ) ∂μₛ) * testAt(b, 0) := by
  have : BorelSpace Iₛ := sIdeleGroup_borelSpace (F := F) (S := S)
  have : (sMultiplicativeTamagawaMeasure F S).IsHaarMeasure :=
    sMultiplicativeTamagawaMeasure_isHaarMeasure (F := F) (S := S)
  have hc : Continuous f.val := sLocalTraceDilationKernel_apply_zero_continuous
    ((mem_bruhatSmoothSubmodule_iff _).1 f.property.1)
  have hn : Continuous fun g : Iₛ ↦ normS(g) := by
    have h : Continuous fun g : Iₛ ↦ sIdeleQuotientNorm F S (QuotientGroup.mk g) :=
      (isProperMap_sIdeleQuotientNorm F S).continuous.comp continuous_quot_mk
    exact NNReal.continuous_coe.comp (Units.continuous_val.comp h)
  have hpos (g : Iₛ) : 0 < normS(g) := NNReal.coe_pos.mpr (Units.zero_lt (sIdeleNorm F S g))
  have hsq : Continuous fun g : Iₛ ↦ (Real.sqrt (normS(g)) : ℂ) :=
    Complex.continuous_ofReal.comp hn.sqrt
  have hne (g : Iₛ) : (Real.sqrt (normS(g)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hpos g)).ne'
  have hcs : HasCompactSupport fun g ↦ f.val g / (Real.sqrt (normS(g)) : ℂ) :=
    HasCompactSupport.mono f.property.2 fun g hg h0 ↦ hg (by simp [h0])
  refine ⟨(hc.div hsq hne).integrable_of_hasCompactSupport hcs, ?_⟩
  simp [sLocalTraceDilationKernel, integral_mul_const]

private theorem exists_sLocalTraceDilationStrongDual_exists_norm_le {H : Type*} [CommGroup H]
    [TopologicalSpace H] {g : H → ℂ} (hg : g ∈ schwartzBruhatSubmodule H) :
    ∃ C : ℝ, ∀ x, ‖g x‖ ≤ C := by
  let P (g : H → ℂ) : Prop := ∃ C : ℝ, ∀ x, ‖g x‖ ≤ C
  have hzero : P 0 := ⟨0, fun x ↦ by simp⟩
  have hadd : ∀ g h, P g → P h → P (g + h) := by
    rintro g h ⟨C, hC⟩ ⟨D, hD⟩
    exact ⟨C + D, fun x ↦ (norm_add_le (g x) (h x)).trans (add_le_add (hC x) (hD x))⟩
  refine Submodule.iSup_induction (motive := P) _ hg (fun a g hg ↦ ?_) hzero hadd
  refine Submodule.iSup_induction (motive := P) _ hg (fun e g hg ↦ ?_) hzero hadd
  obtain ⟨s, rfl⟩ := LinearMap.mem_range.mp hg
  have hb (z) : ‖s z‖ ≤ (elementarySchwartzBound (s : _ → ℂ) (0, 0, 0, 0)).toReal := by
    have hz : (‖s z‖₊ : ℝ≥0∞) ≤ elementarySchwartzBound (s : _ → ℂ) (0, 0, 0, 0) := by
      rw [elementarySchwartzBound_zero]
      exact le_iSup (fun y ↦ (‖s y‖₊ : ℝ≥0∞)) z
    exact ENNReal.toReal_mono (s.property.2 (0, 0, 0, 0)).ne hz
  refine ⟨(elementarySchwartzBound (s : _ → ℂ) (0, 0, 0, 0)).toReal, fun x ↦ ?_⟩
  rw [schwartzBruhatStageRealization_apply]
  split_ifs
  · exact hb _
  · simp

private theorem exists_sLocalTraceDilationStrongDual_integrable
    (f : BruhatCompactSupport Iₛ) (x : Aₛ) (b : testₛ) :
    Integrable (fun g : Iₛ ↦
      f.val g / (Real.sqrt (normS(g)) : ℂ) * testAt(b, (g⁻¹).val * x)) μₛ := by
  have : BorelSpace Iₛ := sIdeleGroup_borelSpace (F := F) (S := S)
  have hweight := (sLocalTraceDilationKernel_apply_zero f 0).1
  obtain ⟨M, hM⟩ := exists_sLocalTraceDilationStrongDual_exists_norm_le b.property
  have hshift : Continuous (fun g : Iₛ ↦ Multiplicative.ofAdd ((g⁻¹).val * x)) :=
    continuous_ofAdd.comp ((Units.continuous_val.comp continuous_inv).mul continuous_const)
  exact hweight.mul_bdd ((schwartzBruhat_continuous b).comp hshift).aestronglyMeasurable
    (.of_forall fun g ↦ hM _)

private theorem exists_sLocalTraceDilationStrongDual_continuous_of_sup_bound {A : Type*} [CommGroup A]
    [TopologicalSpace A] (Λ : SchwartzBruhat A →ₗ[ℂ] ℂ) (C : ℝ≥0)
    (hΛ : ∀ (f : SchwartzBruhat A) (M : ℝ), (∀ x, ‖f x‖ ≤ M) → ‖Λ f‖ ≤ C * M) :
    Continuous Λ := by
  classical
  let p := (normSeminorm ℂ ℂ).comp Λ
  have hp : ∀ (b : BruhatStructuralPair A) (s : ElementaryLCAPresentation b.quotient),
      Continuous (p ∘ schwartzBruhatStageInclusion b s) := by
    intro b s
    let q := (normSeminorm ℂ ℂ).comp (Λ.comp (schwartzBruhatStageInclusion b s))
    change Continuous q
    let p₀ : Seminorm ℂ (SchwartzBruhatStage s) := elementarySchwartzSeminorm (0, 0, 0, 0)
    have hp₀ : Continuous p₀ :=
      (withGeneratingSeminorms_spec _ _).continuous_seminorm (0, 0, 0, 0)
    have hpt (f : SchwartzBruhatStage s) (x : A) :
        ‖schwartzBruhatStageRealization b s f x‖ ≤ p₀ f := by
      let := s.finiteGroup
      have he := schwartzBruhatStageRealization_apply b s f x
      by_cases hx : x ∈ b.val.1
      · rw [dite_eq_left hx] at he
        rw [he]
        let y := Multiplicative.toAdd (s.equiv (QuotientGroup.mk ⟨x, hx⟩))
        change (‖f y‖₊ : ENNReal).toReal ≤ (elementarySchwartzBound f.val (0, 0, 0, 0)).toReal
        have hb : (‖f y‖₊ : ENNReal) ≤ elementarySchwartzBound f.val (0, 0, 0, 0) :=
          (le_iSup (fun g ↦ (‖f.val g‖₊ : ENNReal)) y).trans_eq
            (elementarySchwartzBound_zero f.val).symm
        exact ENNReal.toReal_mono (f.property.2 (0, 0, 0, 0)).ne hb
      · rw [dite_eq_right hx] at he
        exact ((congrArg norm he).trans (norm_zero : ‖(0 : ℂ)‖ = 0)).le.trans
          (apply_nonneg p₀ f)
    have hC : Continuous (C • p₀) := hp₀.const_smul C
    exact Seminorm.continuous_of_le hC fun f ↦
      hΛ (schwartzBruhatStageInclusion b s f) (p₀ f) (hpt f)
  let i : {q : Seminorm ℂ (schwartzBruhatSubmodule A) //
      ∀ (b : BruhatStructuralPair A) (s : ElementaryLCAPresentation b.quotient),
        Continuous (q ∘ schwartzBruhatStageInclusion b s)} := ⟨p, hp⟩
  exact (norm_withSeminorms ℂ ℂ).continuous_of_continuous_comp Λ fun _ ↦
    (withGeneratingSeminorms_spec _ Subtype.val).continuous_seminorm i

/-- Paper: (12.4.1.5)–(12.4.1.7), p. 516. At each output point the scalar
pairing with the test defines a continuous linear functional on additive
Schwartz–Bruhat functions. -/
theorem exists_sLocalTraceDilationStrongDual (f : BruhatCompactSupport Iₛ) (x : Aₛ) :
    ∃ K : StrongDual ℂ testₛ, ∀ b : testₛ,
      Integrable (fun g : Iₛ ↦
        f.val g / (Real.sqrt (normS(g)) : ℂ) * testAt(b, (g⁻¹).val * x)) μₛ ∧
      K b = sLocalTraceDilationKernel f (fun y ↦ testAt(b, y)) x := by
  let weight (g : Iₛ) := f.val g / (Real.sqrt (normS(g)) : ℂ)
  let shift (g : Iₛ) : Multiplicative Aₛ := Multiplicative.ofAdd ((g⁻¹).val * x)
  let Φ (b : testₛ) : ℂ := ∫ g, weight g * b (shift g) ∂μₛ
  have hint (b : testₛ) : Integrable (fun g ↦ weight g * b (shift g)) μₛ :=
    exists_sLocalTraceDilationStrongDual_integrable f x b
  have hlin : IsLinearMap ℂ Φ := by
    constructor
    · intro b c
      change (∫ g, weight g * (b + c) (shift g) ∂μₛ) =
        (∫ g, weight g * b (shift g) ∂μₛ) + ∫ g, weight g * c (shift g) ∂μₛ
      simp_rw [show ∀ g, (b + c) (shift g) = b (shift g) + c (shift g) from fun g ↦ by rfl]
      simp_rw [mul_add]
      exact integral_add (hint b) (hint c)
    · intro c b
      change (∫ g, weight g * (c • b) (shift g) ∂μₛ) =
        c • ∫ g, weight g * b (shift g) ∂μₛ
      simp_rw [show ∀ g, (c • b) (shift g) = c * b (shift g) from fun g ↦ by rfl]
      simp_rw [mul_left_comm (weight _) c]
      simpa only [smul_eq_mul] using (integral_const_mul c (fun g ↦ weight g * b (shift g)))
  let Λ : testₛ →ₗ[ℂ] ℂ := IsLinearMap.mk' Φ hlin
  have hweight : Integrable weight μₛ := (sLocalTraceDilationKernel_apply_zero f 0).1
  let C : ℝ≥0 := ⟨∫ g, ‖weight g‖ ∂μₛ, integral_nonneg fun _ ↦ norm_nonneg _⟩
  have hΛ : ∀ (b : testₛ) (M : ℝ), (∀ z, ‖b z‖ ≤ M) → ‖Λ b‖ ≤ C * M := by
    intro b M hM
    change ‖∫ g, weight g * b (shift g) ∂μₛ‖ ≤ C * M
    calc
      _ ≤ ∫ g, ‖weight g * b (shift g)‖ ∂μₛ := norm_integral_le_integral_norm _
      _ ≤ ∫ g, ‖weight g‖ * M ∂μₛ := by
        apply integral_mono (hint b).norm (hweight.norm.mul_const M)
        intro g
        change ‖weight g * b (shift g)‖ ≤ ‖weight g‖ * M
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)
      _ = C * M := by rw [integral_mul_const]; rfl
  refine ⟨⟨Λ, exists_sLocalTraceDilationStrongDual_continuous_of_sup_bound Λ C hΛ⟩, fun b ↦ ⟨hint b, ?_⟩⟩
  rfl

-- TODO(paper-gap): The application of (12.4.1.6) requires a kernel theorem for
-- the particular vector-valued Schwartz–Bruhat space and operator topology.
-- The scalar distribution pairing above does not establish that assertion.

-- TODO(paper-gap): Footnotes 2–4 request new one-sided smooth cutoffs and an
-- independent lower bound. In Step II the product-norm multipliers also fail
-- to have the advertised Schwartz–Bruhat mapping properties (I218 and R9).

/-- Paper: Step II, p. 516. In the rational real model, a compact smooth cutoff
vanishing near zero multiplies any Schwartz test into the flat subspace.
Deviation: A ball cutoff that is one near zero does not have this range. -/
theorem realSpatialCutoff_flat_of_eventually_zero (ρ : ℝ → ℝ)
    (_hSmooth : ContDiff ℝ (∞ : ℕ∞ω) ρ) (_hCompact : HasCompactSupport ρ)
    (_hZero : ∀ᶠ x in 𝓝 (0 : ℝ), ρ x = 0) (f : 𝓢(ℝ, ℂ)) :
    ∃ h : 𝓢(ℝ, ℂ), h ∈ realSchwartzFlatAtOrigin ∧
      ∀ x : ℝ, h x = (ρ x : ℂ) * f x := by
  have hg : (fun x : ℝ ↦ (ρ x : ℂ)).HasTemperateGrowth :=
    (_hCompact.comp_left Complex.ofReal_zero).hasTemperateGrowth
      (Complex.ofRealCLM.contDiff.comp _hSmooth)
  refine ⟨SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (ρ x : ℂ)) f,
    (mem_realSchwartzFlatAtOrigin_iff _).2 fun k ↦ ?_, fun x ↦ ?_⟩
  · have h0 : (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (ρ x : ℂ)) f : ℝ → ℂ) =ᶠ[𝓝 0]
        fun _ ↦ 0 :=
      _hZero.mono fun x hx ↦ by simp [SchwartzMap.smulLeftCLM_apply_apply hg, hx]
    rw [h0.iteratedDeriv_eq]
    simp
  · simp [SchwartzMap.smulLeftCLM_apply_apply hg]

/-- Paper: Step II and (12.4.1.8)–(12.4.1.10), pp. 516–517. The Fourier cutoff
multiplies the Fourier transform by a symbol, then applies the inverse transform.
Deviation: This is a scalar function on the additive adeles. The definition makes
no assertion that the result belongs to the Schwartz–Bruhat test space. -/
def sLocalTraceFourierCutoff (ρ' : Aₛ → ℂ) (b : testₛ) (x : Aₛ) : ℂ :=
  fourierₛ (fun u ↦ ρ' u * testAt(sAdeleSchwartzFourier b, u)) (-x)

/-- Paper: (12.4.1.8), p. 517. The constant-one Fourier symbol recovers the test
by inversion. -/
theorem sLocalTraceFourierCutoff_one (b : testₛ) (x : Aₛ) :
    sLocalTraceFourierCutoff (fun _ ↦ 1) b x = testAt(b, x) := by
  have h := sLocal_fourier_inversion b (-x)
  rw [neg_neg] at h
  unfold sLocalTraceFourierCutoff
  simp only [one_mul]
  unfold sAdeleSchwartzFourier at h
  exact h

/-- Paper: Step II, p. 517. For an integrable symbol the inverse Fourier transform
of the symbol, evaluated at output minus input, is the Fourier cutoff kernel.
Deviation: The inverse transform gives the sign for general symbols. For the even
symbols in the paper the forward transform has the same values. -/
def sLocalTraceFourierKernel (ρ' : Aₛ → ℂ) (_hρ' : Integrable ρ' νₛ) (x y : Aₛ) : ℂ :=
  fourierₛ ρ' (y - x)

/-- Paper: Step II, p. 517. The diagonal Fourier kernel for an integrable
symbol is its integral against additive Tamagawa measure. -/
theorem sLocalTraceFourierKernel_diagonal (ρ' : Aₛ → ℂ) (hρ' : Integrable ρ' νₛ)
    (x : Aₛ) :
    sLocalTraceFourierKernel ρ' hρ' x x = ∫ u, ρ' u ∂νₛ := by
  have h0 : ψₛ 0 = 1 := by
    have h1 : ∀ w : InfinitePlace F, (0 : Aₛ).1 w = 0 := fun _ ↦ rfl
    simp [sAdeleStandardCharacter, adeleStandardCharacter_zero, finiteLocalStandardCharacter_zero,
      h1, Pi.single_zero, Prod.mk_zero_zero]
  simp [sLocalTraceFourierKernel, tamagawaFourier, h0]

/-- Paper: Step II, p. 517. With an S-idele as output, integrate the
dilation average of the Fourier phases against the frequency symbol and multiply
by the spatial cutoff.
Deviation: The dilation average is taken first. This formula can be used even
when the frequency symbol has no ordinary inverse Fourier kernel. -/
def sLocalTraceCutoffKernel (f : BruhatCompactSupport Iₛ) (ρ : Iₛ → ℂ) (ρ' : Aₛ → ℂ)
    (x : Iₛ) (y : Aₛ) : ℂ :=
  ρ x * ∫ u, ρ' u *
    sLocalTraceDilationKernel f (fun z ↦ (ψₛ ((z - y) * u) : ℂ)) x.val ∂νₛ

/-- An integrable product weight dominates the joint integrand of the two kernels. -/
private theorem sLocalTraceCutoffKernel_eq_comp_fubini
    {G A : Type*} [MeasurableSpace G] [MeasurableSpace A]
    (μ : Measure G) (ν : Measure A) [SFinite μ] [SFinite ν]
    (weight : G → ℂ) (symbol : A → ℂ) (phase : G → A → ℂ)
    (hweight : Integrable weight μ) (hsymbol : Integrable symbol ν)
    (hphase : AEStronglyMeasurable (fun p : A × G ↦ phase p.2 p.1) (ν.prod μ))
    (hunit : ∀ g u, ‖phase g u‖ = 1) :
    (∫ u, symbol u * (∫ g, weight g * phase g u ∂μ) ∂ν) =
      ∫ g, weight g * (∫ u, symbol u * phase g u ∂ν) ∂μ := by
  have hweightProd := hsymbol.mul_prod hweight
  have hprod : Integrable (uncurry fun u g ↦ symbol u * weight g * phase g u)
      (ν.prod μ) := by
    refine hweightProd.mono (hweightProd.aestronglyMeasurable.mul hphase) ?_
    exact ae_of_all _ fun p ↦ by simp [uncurry, hunit]
  simp_rw [← integral_const_mul]
  simpa only [mul_assoc, mul_left_comm] using integral_integral_swap hprod

/-- Paper: Step II, p. 517. For an integrable symbol the composed kernel
agrees with the dilation average of the inverse Fourier kernel, multiplied by the
spatial cutoff. -/
theorem sLocalTraceCutoffKernel_eq_comp (f : BruhatCompactSupport Iₛ)
    (ρ : Iₛ → ℂ) (ρ' : Aₛ → ℂ) (hρ' : Integrable ρ' νₛ) (x : Iₛ) (y : Aₛ) :
    sLocalTraceCutoffKernel f ρ ρ' x y =
      ρ x * sLocalTraceDilationKernel f (fun z ↦ sLocalTraceFourierKernel ρ' hρ' z y) x.val :=
  by
    have : BorelSpace Aₛ := sAdeleRing_borelSpace (F := F) (S := S)
    have : BorelSpace Iₛ := sIdeleGroup_borelSpace (F := F) (S := S)
    let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
    let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
      (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
    let : SecondCountableTopology Aₛ := inferInstanceAs (SecondCountableTopology
      (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
    let : SecondCountableTopology Iₛ := (sIdeleGroup_description F S).1.secondCountableTopology
    let : (μₛ).IsHaarMeasure := sMultiplicativeTamagawaMeasure_isHaarMeasure
    let (w : InfinitePlace F) : MeasurableSpace w.Completion := borel _
    let (v : S) : MeasurableSpace (v.val.adicCompletion F) := borel _
    let (w : InfinitePlace F) : BorelSpace w.Completion := ⟨rfl⟩
    let (v : S) : BorelSpace (v.val.adicCompletion F) := ⟨rfl⟩
    let (w : InfinitePlace F) : (infiniteLocalAdditiveTamagawaMeasure F w).IsAddHaarMeasure :=
      infiniteLocalAdditiveTamagawaMeasure_haar F w
    let (v : S) : (finiteLocalAdditiveTamagawaMeasure F v.val).IsAddHaarMeasure :=
      finiteLocalAdditiveTamagawaMeasure_isAddHaar F v.val
    let : (Measure.pi (infiniteLocalAdditiveTamagawaMeasure F)).IsAddHaarMeasure :=
      Measure.pi.isAddHaarMeasure _
    let : (Measure.pi (fun v : S ↦ finiteLocalAdditiveTamagawaMeasure F v.val)).IsAddHaarMeasure :=
      Measure.pi.isAddHaarMeasure _
    let : (νₛ).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
    let weight (g : Iₛ) := f.val g / (Real.sqrt (normS(g)) : ℂ)
    have hweight : Integrable weight μₛ := (sLocalTraceDilationKernel_apply_zero f 0).1
    obtain ⟨e, he, _⟩ := sAdditiveTamagawaMeasure_selfDual F S
    let char := e (Multiplicative.ofAdd (1 : Aₛ))
    have hchar (z : Aₛ) : char (Multiplicative.ofAdd z) = ψₛ z := by
      simpa only [one_mul] using he 1 z
    have hcontinuous : Continuous (fun z : Aₛ ↦ (ψₛ z : ℂ)) := by
      simp_rw [← hchar]
      exact continuous_subtype_val.comp ((map_continuous char).comp continuous_ofAdd)
    have hneg (z : Aₛ) : star (ψₛ (-z) : ℂ) = (ψₛ z : ℂ) := by
      rw [← hchar, ofAdd_neg, map_inv, Circle.coe_inv_eq_conj,
        ← Complex.star_def, star_star, hchar]
    let phase (g : Iₛ) (u : Aₛ) := (ψₛ (((g⁻¹).val * x.val - y) * u) : ℂ)
    have hphase : Continuous (uncurry phase) := hcontinuous.comp
      (((((Units.continuous_val.comp continuous_inv).comp continuous_fst).mul
        continuous_const).sub continuous_const).mul continuous_snd)
    have hfourier (g : Iₛ) :
        sLocalTraceFourierKernel ρ' hρ' ((g⁻¹).val * x.val) y =
          ∫ u, ρ' u * phase g u ∂νₛ := by
      unfold sLocalTraceFourierKernel tamagawaFourier
      apply integral_congr_ae
      exact ae_of_all _ fun u ↦ by
        change ρ' u * star (ψₛ (u * (y - (g⁻¹).val * x.val)) : ℂ) = ρ' u * phase g u
        rw [show u * (y - (g⁻¹).val * x.val) = -(((g⁻¹).val * x.val - y) * u) by
          rw [← neg_sub ((g⁻¹).val * x.val) y, mul_neg, mul_comm u], hneg]
    unfold sLocalTraceCutoffKernel sLocalTraceDilationKernel
    apply congrArg (fun z : ℂ ↦ ρ x * z)
    simp_rw [hfourier]
    exact sLocalTraceCutoffKernel_eq_comp_fubini μₛ νₛ weight ρ' phase hweight hρ'
      (hphase.comp continuous_swap).aestronglyMeasurable (fun g u ↦ Circle.norm_coe _)

-- TODO(paper-gap): The function on additive adeles constructed in Step II
-- requires a measure conversion and a quotient kernel construction before
-- Proposition 12.2.2.2 can be applied to it. On the additive side the
-- skew-diagonal convention below puts ξx in the output slot. The resulting
-- orbit sum reindexes the S-units by inversion.

-- TODO(paper-gap): The reference to (12.4.1.4) on pp. 514, 516 and 519 should
-- refer to (12.4.1.1)–(12.4.1.3). Equation (12.4.1.4) is the lifting identity.

/-- Paper: (12.4.1.17), p. 518. The factor converting additive to
multiplicative measure is the product of q/(q−1) over the finite places. -/
def sLocalTraceMeasureFactor (S : Finset V) : ℝ :=
  ∏ v ∈ S, (v.asIdeal.absNorm : ℝ) / ((v.asIdeal.absNorm : ℝ) - 1)

/-- Paper: (12.4.1.17), p. 518. The factor for the empty finite set is one
and the factor for one finite place is the corresponding Euler factor. -/
theorem sLocalTraceMeasureFactor_empty_singleton (v : V) :
    sLocalTraceMeasureFactor (F := F) ∅ = 1 ∧
      sLocalTraceMeasureFactor {v} = (v.asIdeal.absNorm : ℝ) / ((v.asIdeal.absNorm : ℝ) - 1) := by
  constructor <;> simp [sLocalTraceMeasureFactor]

/-- The lower integral of a product of coordinate functions over a product measure on
`n` coordinates is the product of the lower integrals. -/
private theorem sLocalTrace_measure_density_lintegral_fin {n : ℕ} {E : Fin n → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : Fin n) → Measure (E i)} [∀ i, SigmaFinite (μ i)]
    (f : (i : Fin n) → E i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  induction n with
  | zero => simp
  | succ n n_ih =>
      rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb
        (MeasurableEquiv.measurableEmbedding _), Fin.prod_univ_succAbove _ 0]
      have hfun : (fun p ↦ ∏ i, f i ((MeasurableEquiv.piFinSuccAbove E 0).symm p i)) =
          fun p ↦ f 0 p.1 * ∏ j : Fin n, f (Fin.succAbove 0 j) (p.2 j) := by
        funext p
        rw [Fin.prod_univ_succAbove _ 0]
        exact congrArg₂ (· * ·) (congrArg (f 0) (Fin.insertNth_apply_same 0 p.1 p.2))
          (Finset.prod_congr rfl fun j _ ↦ congrArg _ (Fin.insertNth_apply_succAbove 0 p.1 p.2 j))
      rw [hfun, lintegral_prod_mul (f := f 0) (g := fun x : (j : Fin n) → E (Fin.succAbove 0 j) ↦
          ∏ j : Fin n, f (Fin.succAbove 0 j) (x j))
        (hf 0).aemeasurable (Finset.measurable_prod _ fun j _ ↦
          (hf (Fin.succAbove 0 j)).comp (measurable_pi_apply j)).aemeasurable,
        n_ih (fun j ↦ f (Fin.succAbove 0 j)) (fun j ↦ hf _)]

/-- The lower integral of a product of coordinate functions over a finite product measure
is the product of the lower integrals. -/
private theorem sLocalTrace_measure_density_lintegral_pi {ι : Type*} [Fintype ι]
    {E : ι → Type*} {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : ι) → Measure (E i)}
    [∀ i, SigmaFinite (μ i)] (f : (i : ι) → E i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  let e := (Fintype.equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft _ e).lintegral_comp_emb
    (MeasurableEquiv.measurableEmbedding _)]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  exact sLocalTrace_measure_density_lintegral_fin (fun i ↦ f (e i)) (fun i ↦ hf (e i))

/-- A finite product of measures with densities is the product measure with the
product density. -/
private theorem sLocalTrace_measure_density_pi_withDensity {ι : Type*} [Fintype ι]
    {E : ι → Type*} {mE : ∀ i, MeasurableSpace (E i)} (μ : (i : ι) → Measure (E i))
    [∀ i, SigmaFinite (μ i)] (f : (i : ι) → E i → ℝ≥0∞) (hf : ∀ i, Measurable (f i))
    [∀ i, SigmaFinite ((μ i).withDensity (f i))] :
    Measure.pi (fun i ↦ (μ i).withDensity (f i)) =
      (Measure.pi μ).withDensity (fun x ↦ ∏ i, f i (x i)) := by
  refine Measure.pi_eq fun s hs ↦ ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi,
    sLocalTrace_measure_density_lintegral_pi f hf]
  exact Finset.prod_congr rfl fun i _ ↦ (withDensity_apply _ (hs i)).symm

/-- Paper: (12.4.1.17), p. 518. The pushforward of multiplicative Tamagawa
measure to the invertible locus has density c_S divided by the product norm.
Deviation: The density is applied to additive measure restricted to the invertible locus. -/
theorem sLocalTrace_measure_density :
    (μₛ).map (Units.val : Iₛ → Aₛ) =
      ((νₛ).restrict (range (Units.val : Iₛ → Aₛ))).withDensity
        (fun z ↦ ENNReal.ofReal (sLocalTraceMeasureFactor S / modS(z))) := by
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let (w : InfinitePlace F) : MeasurableSpace w.Completion := borel _
  let (v : S) : MeasurableSpace (v.val.adicCompletion F) := borel _
  let (v : S) : MeasurableSpace (v.val.adicCompletion F)ˣ := borel _
  let (w : InfinitePlace F) : BorelSpace w.Completion := ⟨rfl⟩
  let (v : S) : BorelSpace (v.val.adicCompletion F) := ⟨rfl⟩
  let (w : InfinitePlace F) : BorelSpace w.Completionˣ := borelSpace_units_of_continuousInv₀ _
  let (v : S) : BorelSpace (v.val.adicCompletion F)ˣ := ⟨rfl⟩
  let (w : InfinitePlace F) : SecondCountableTopology w.Completionˣ :=
    Units.isEmbedding_val₀.secondCountableTopology
  let (v : S) : SecondCountableTopology (v.val.adicCompletion F)ˣ :=
    Units.isEmbedding_val₀.secondCountableTopology
  let (w : InfinitePlace F) : LocallyCompactSpace w.Completionˣ :=
    (IsOpenUnits.isOpenEmbedding_unitsVal (M := w.Completion)).locallyCompactSpace
  let (w : InfinitePlace F) : (infiniteLocalMultiplicativeTamagawaMeasure F w).IsHaarMeasure :=
    infiniteLocalMultiplicativeTamagawaMeasure_haar F w
  let (v : S) : (finiteLocalMultiplicativeTamagawaMeasure F v.val).IsHaarMeasure :=
    finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure v.val
  let (w : InfinitePlace F) : (infiniteLocalAdditiveTamagawaMeasure F w).IsAddHaarMeasure :=
    infiniteLocalAdditiveTamagawaMeasure_haar F w
  let (v : S) : (finiteLocalAdditiveTamagawaMeasure F v.val).IsAddHaarMeasure :=
    finiteLocalAdditiveTamagawaMeasure_isAddHaar F v.val
  let ρI (w : InfinitePlace F) (x : w.Completion) : ℝ≥0∞ := (↑(‖x‖₊ ^ w.mult) : ℝ≥0∞)⁻¹
  let c (v : S) : ℝ≥0∞ := ↑v.val.asIdeal.absNorm / (↑v.val.asIdeal.absNorm - 1)
  let ρS (v : S) (x : v.val.adicCompletion F) : ℝ≥0∞ := c v * (↑‖x‖₊ : ℝ≥0∞)⁻¹
  have hq (v : S) : 1 < v.val.asIdeal.absNorm := HeightOneSpectrum.one_lt_absNorm v.val
  have hc (v : S) : c v ≠ ⊤ := ENNReal.div_ne_top (ENNReal.natCast_ne_top _)
    (tsub_pos_of_lt (by exact_mod_cast hq v)).ne'
  have hρI (w : InfinitePlace F) : Measurable (ρI w) :=
    ((measurable_nnNorm.pow_const _).coe_nnreal_ennreal).inv
  have hρS (v : S) : Measurable (ρS v) :=
    measurable_const.mul measurable_nnNorm.coe_nnreal_ennreal.inv
  have hRI (w : InfinitePlace F) : MeasurableSet (range (Units.val : w.Completionˣ → _)) :=
    (IsOpenUnits.isOpenEmbedding_unitsVal (M := w.Completion)).isOpen_range.measurableSet
  have hRS (v : S) : MeasurableSet (range (Units.val : (v.val.adicCompletion F)ˣ → _)) :=
    (IsOpenUnits.isOpenEmbedding_unitsVal (M := v.val.adicCompletion F)).isOpen_range.measurableSet
  have hlocI (w : InfinitePlace F) : (infiniteLocalMultiplicativeTamagawaMeasure F w).map Units.val =
      ((infiniteLocalAdditiveTamagawaMeasure F w).restrict (range Units.val)).withDensity (ρI w) := by
    rw [infiniteLocalMultiplicativeTamagawaMeasure,
      (IsOpenUnits.isOpenEmbedding_unitsVal (M := w.Completion)).measurableEmbedding.map_comap,
      restrict_withDensity (hRI w)]
  have hlocS (v : S) : (finiteLocalMultiplicativeTamagawaMeasure F v.val).map Units.val =
      ((finiteLocalAdditiveTamagawaMeasure F v.val).restrict (range Units.val)).withDensity
        (ρS v) := by
    rw [finiteLocalMultiplicativeTamagawaMeasure_eq_withDensity, Measure.map_smul,
      (IsOpenUnits.isOpenEmbedding_unitsVal (M := v.val.adicCompletion F)).measurableEmbedding.map_comap,
      restrict_withDensity (hRS v), ← withDensity_smul' _ _ (hc v)]
    · rfl
    · exact Units.continuous_val.measurable.aemeasurable
  have hsfI (w : InfinitePlace F) : SigmaFinite
      (((infiniteLocalAdditiveTamagawaMeasure F w).restrict (range Units.val)).withDensity
        (ρI w)) :=
    SigmaFinite.withDensity_of_ne_top ((ae_restrict_iff' (hRI w)).2 (ae_of_all _ fun x hx ↦ by
      obtain ⟨u, rfl⟩ := hx
      exact ENNReal.inv_ne_top.2 (ENNReal.coe_ne_zero.2 (pow_ne_zero _
        (nnNorm_ne_zero_iff.2 u.ne_zero)))))
  have hsfS (v : S) : SigmaFinite
      (((finiteLocalAdditiveTamagawaMeasure F v.val).restrict (range Units.val)).withDensity
        (ρS v)) :=
    SigmaFinite.withDensity_of_ne_top ((ae_restrict_iff' (hRS v)).2 (ae_of_all _ fun x hx ↦ by
      obtain ⟨u, rfl⟩ := hx
      exact ENNReal.mul_ne_top (hc v) (ENNReal.inv_ne_top.2 (ENNReal.coe_ne_zero.2
        (nnNorm_ne_zero_iff.2 u.ne_zero)))))
  have (w : InfinitePlace F) :
      SigmaFinite ((infiniteLocalMultiplicativeTamagawaMeasure F w).map Units.val) := by
    rw [hlocI w]; exact hsfI w
  have (v : S) :
      SigmaFinite ((finiteLocalMultiplicativeTamagawaMeasure F v.val).map Units.val) := by
    rw [hlocS v]; exact hsfS v
  have hAI : Measurable (fun (f : (w : InfinitePlace F) → w.Completionˣ) (w : InfinitePlace F) ↦
      (f w).val) :=
    measurable_pi_iff.2 fun w ↦ Units.continuous_val.measurable.comp (measurable_pi_apply w)
  have hAS : Measurable (fun (f : (v : S) → (v.val.adicCompletion F)ˣ) (v : S) ↦ (f v).val) :=
    measurable_pi_iff.2 fun v ↦ Units.continuous_val.measurable.comp (measurable_pi_apply v)
  have hmapL : (μₛ).map (Units.val : Iₛ → Aₛ) =
      ((Measure.pi (infiniteLocalMultiplicativeTamagawaMeasure F)).map
        (fun (f : (w : InfinitePlace F) → w.Completionˣ) (w : InfinitePlace F) ↦ (f w).val)).prod
      ((Measure.pi fun v : S ↦ finiteLocalMultiplicativeTamagawaMeasure F v.val).map
        (fun (f : (v : S) → (v.val.adicCompletion F)ˣ) (v : S) ↦ (f v).val)) := by
    rw [Measure.map_prod_map _ _ hAI hAS]
    unfold sMultiplicativeTamagawaMeasure
    rw [Measure.map_map]
    · rfl
    · exact fun s hs ↦ ⟨s, hs, rfl⟩
    · rintro _ ⟨t, ht, rfl⟩
      exact (hAI.prodMap hAS) ht
  have hrange : range (Units.val : Iₛ → Aₛ) =
      (univ.pi fun w : InfinitePlace F ↦ range (Units.val : w.Completionˣ → w.Completion)) ×ˢ
        (univ.pi fun v : S ↦
          range (Units.val : (v.val.adicCompletion F)ˣ → v.val.adicCompletion F)) := by
    ext z
    simp only [Set.mem_prod, Set.mem_univ_pi]
    change IsUnit z ↔ (∀ w, IsUnit (z.1 w)) ∧ ∀ v, IsUnit (z.2 v)
    rw [Prod.isUnit_iff, Pi.isUnit_iff, Pi.isUnit_iff]
  have hbox : MeasurableSet ((univ.pi fun w : InfinitePlace F ↦
      range (Units.val : w.Completionˣ → w.Completion)) ×ˢ (univ.pi fun v : S ↦
          range (Units.val : (v.val.adicCompletion F)ˣ → v.val.adicCompletion F))) :=
    (MeasurableSet.univ_pi hRI).prod (MeasurableSet.univ_pi hRS)
  have hpiI : (Measure.pi (infiniteLocalMultiplicativeTamagawaMeasure F)).map
      (fun (f : (w : InfinitePlace F) → w.Completionˣ) (w : InfinitePlace F) ↦ (f w).val) =
      Measure.pi fun w ↦ (infiniteLocalMultiplicativeTamagawaMeasure F w).map Units.val :=
    Measure.pi_map_pi fun w ↦ Units.continuous_val.measurable.aemeasurable
  have hpiS : (Measure.pi fun v : S ↦ finiteLocalMultiplicativeTamagawaMeasure F v.val).map
      (fun (f : (v : S) → (v.val.adicCompletion F)ˣ) (v : S) ↦ (f v).val) =
      Measure.pi fun v : S ↦ (finiteLocalMultiplicativeTamagawaMeasure F v.val).map Units.val :=
    Measure.pi_map_pi fun v ↦ Units.continuous_val.measurable.aemeasurable
  rw [hmapL, hpiI, hpiS]
  simp_rw [hlocI, hlocS]
  rw [sLocalTrace_measure_density_pi_withDensity _ ρI hρI,
    sLocalTrace_measure_density_pi_withDensity _ ρS hρS,
    prod_withDensity (f := fun x : (w : InfinitePlace F) → w.Completion ↦ ∏ w, ρI w (x w))
      (g := fun x : (v : S) → v.val.adicCompletion F ↦ ∏ v, ρS v (x v))
      (Finset.measurable_prod _ fun w _ ↦ (hρI w).comp (measurable_pi_apply w))
      (Finset.measurable_prod _ fun v _ ↦ (hρS v).comp (measurable_pi_apply v)),
    ← Measure.restrict_pi_pi, ← Measure.restrict_pi_pi, Measure.prod_restrict, hrange]
  refine withDensity_congr_ae ((ae_restrict_iff' hbox).2 (ae_of_all _ fun z hz ↦ ?_))
  have hz1 (w : InfinitePlace F) : 0 < ‖z.1 w‖ := by
    obtain ⟨u, hu⟩ := (Set.mem_univ_pi.1 hz.1) w
    exact norm_pos_iff.2 (hu ▸ u.ne_zero)
  have hz2 (v : S) : 0 < ‖z.2 v‖ := by
    obtain ⟨u, hu⟩ := (Set.mem_univ_pi.1 hz.2) v
    exact norm_pos_iff.2 (hu ▸ u.ne_zero)
  have hq' (v : S) : (1 : ℝ) < v.val.asIdeal.absNorm := by exact_mod_cast hq v
  have e1 (w : InfinitePlace F) :
      ρI w (z.1 w) = ENNReal.ofReal ((‖z.1 w‖ ^ w.mult)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos (pow_pos (hz1 w) _),
      show ‖z.1 w‖ ^ w.mult = ((‖z.1 w‖₊ ^ w.mult : ℝ≥0) : ℝ) by simp,
      ENNReal.ofReal_coe_nnreal]
  have e2 (v : S) : ρS v (z.2 v) =
      ENNReal.ofReal ((v.val.asIdeal.absNorm : ℝ) / ((v.val.asIdeal.absNorm : ℝ) - 1)) *
        ENNReal.ofReal ‖z.2 v‖⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos (hz2 v), ENNReal.ofReal_div_of_pos (sub_pos.2 (hq' v)),
      ENNReal.ofReal_sub _ zero_le_one, ENNReal.ofReal_natCast, ENNReal.ofReal_one,
      ← coe_nnNorm, ENNReal.ofReal_coe_nnreal]
  simp only [e1, e2]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun w _ ↦ inv_nonneg.2 (pow_nonneg (hz1 w).le _))]
  simp_rw [← ENNReal.ofReal_mul (div_nonneg (Nat.cast_nonneg _) (sub_pos.2 (hq' _)).le)]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun v _ ↦ mul_nonneg
      (div_nonneg (Nat.cast_nonneg _) (sub_pos.2 (hq' v)).le) (inv_nonneg.2 (hz2 v).le)),
    ← ENNReal.ofReal_mul (Finset.prod_nonneg fun w _ ↦ inv_nonneg.2 (pow_nonneg (hz1 w).le _))]
  congr 1
  rw [sLocalTraceMeasureFactor, ← Finset.prod_coe_sort S, Finset.prod_mul_distrib,
    Finset.prod_inv_distrib, Finset.prod_inv_distrib]
  ring

/-- Paper: (12.4.1.18)–(12.4.1.21), p. 518. Translate and invert the lifted test
and divide by the square-root norm after the change of variable z = gξ − 1.
Deviation: The function on the additive adeles is extended by zero where 1 + z
is not invertible. The printed domain in (12.4.1.18) is written for g. -/
def sLocalTraceEta (f : BruhatCompactSupport Iₛ) (ξ : Hₛ) (z : Aₛ) : ℂ :=
  Function.extend (Units.val : Iₛ → Aₛ)
    (fun u ↦ f.val ((ξ.val⁻¹ * u)⁻¹) / (Real.sqrt (normS(ξ.val⁻¹ * u)) : ℂ))
    (fun _ ↦ 0) (1 + z)

/-- Paper: (12.4.1.20), p. 518. The translated test has value f(ξ) at the
origin, and it is zero at minus one. -/
theorem sLocalTraceEta_zero_neg_one (f : BruhatCompactSupport Iₛ) (ξ : Hₛ) :
    sLocalTraceEta f ξ 0 = f.val ξ.val ∧ sLocalTraceEta f ξ (-1) = 0 := by
  have h2 : sIdeleNorm F S ξ.val = 1 := by
    obtain ⟨γ, hγ, hξ⟩ := Subgroup.mem_map.mp ξ.property
    have h1 := ((sIdeleNorm_spec F S).2 hγ)
    rw [← hξ]; exact h1
  constructor
  · unfold sLocalTraceEta
    have h : (1 : Aₛ) + 0 = ((1 : Iₛ) : Aₛ) := by simp
    rw [h, Units.val_injective.extend_apply]
    simp [h2]
  · unfold sLocalTraceEta
    have h : (1 : Aₛ) + -1 = 0 := by simp
    rw [h, Function.extend_apply']
    rintro ⟨u, hu⟩
    exact not_isUnit_zero (hu ▸ u.isUnit)

/-- Paper: (12.4.1.12)–(12.4.1.22), pp. 517–518. The skew diagonal of the
composed kernel is the integral of the Fourier transform of the translated test,
weighted by both cutoffs.
Deviation: Retain the cutoffs in the exact identity, and write the skew diagonal
with its output first. Measurable bounded even frequency symbols suffice here. -/
theorem sLocalTraceCutoffKernel_skew (f : BruhatCompactSupport Iₛ)
    (ρ : Iₛ → ℂ) (ρ' : Aₛ → ℂ) (_hρ' : Measurable ρ')
    (_hBound : ∃ C : ℝ, ∀ u, ‖ρ' u‖ ≤ C) (_hEven : ∀ u, ρ' (-u) = ρ' u)
    (ξ : Hₛ) (x : Iₛ) :
    Integrable (fun u ↦ ρ' u * fourierₛ (sLocalTraceEta f ξ) (x.val * u)) νₛ ∧
      sLocalTraceCutoffKernel f ρ ρ' (ξ.val * x) x.val =
        ρ (ξ.val * x) * (sLocalTraceMeasureFactor S : ℂ) *
          ∫ u, ρ' u * fourierₛ (sLocalTraceEta f ξ) (x.val * u) ∂νₛ := by sorry

/-- Paper: (12.4.1.23)–(12.4.1.24), p. 518. One sharp orbital mass integrates
the transformed test against the logarithmic width of the spatial norm interval.
Deviation: This defines the sharp one-sided expression for a product of radii.
The additive integral omits the null nonunit locus before taking its logarithm. -/
def sLocalTraceSharpMass (f : BruhatCompactSupport Iₛ) (ξ : Hₛ) (R : ℝ) : ℂ :=
  (volume₁ : ℂ) * ∫ w in band(R) ∩ range (Units.val : Iₛ → Aₛ),
    fourierₛ (sLocalTraceEta f ξ) w * ((Real.log R - Real.log (modS(w)) : ℝ) : ℂ) ∂νₛ

/-- Paper: (12.4.1.24), p. 518. The sharp orbital mass of the zero lift vanishes
at every radius. -/
theorem sLocalTraceSharpMass_zero (ξ : Hₛ) (R : ℝ) :
    sLocalTraceSharpMass (0 : BruhatCompactSupport Iₛ) ξ R = 0 := by
  have h0 : sLocalTraceEta (0 : BruhatCompactSupport Iₛ) ξ = 0 := by
    funext z
    have h : (0 : BruhatCompactSupport Iₛ).val = 0 := rfl
    simp only [sLocalTraceEta, h]
    simp
  have h1 : fourierₛ (0 : Aₛ → ℂ) = 0 := by
    funext w; simp [tamagawaFourier]
  simp [sLocalTraceSharpMass, h0, h1]

/-- Paper: (12.4.1.22)–(12.4.1.24), p. 518. With sharp upper cutoffs the orbital
mass is the skew-diagonal integral on an S-unit fundamental domain. The change
of variable w = xu converts the integral to the log-weighted Fourier integral.
Deviation: Use the sharp indicators explicitly. The spatial variable is an S-idele,
and its additive integral uses the image of the fundamental domain under the unit embedding. -/
theorem sLocalTraceSharpMass_eq_integral (f : BruhatCompactSupport Iₛ) (ξ : Hₛ)
    (D : Set Iₛ) (_hD : IsFundamentalDomain Hₛ D μₛ)
    (L L' : ℝ) (_hL : 0 < L) (_hL' : 0 < L') :
    let d := D ∩ {x : Iₛ | normS(x) ≤ L}
    let K := sLocalTraceCutoffKernel f (indicator {x : Iₛ | normS(x) ≤ L} (fun _ ↦ 1))
      (indicator band(L') (fun _ ↦ 1))
    let diag := fun x : Iₛ ↦ K (ξ.val * x) x.val
    IntegrableOn diag d ((νₛ).comap (Units.val : Iₛ → Aₛ)) ∧
      (∫ x in d, diag x ∂((νₛ).comap (Units.val : Iₛ → Aₛ))) =
        sLocalTraceSharpMass f ξ (L * L') := by sorry

local notation "archTest" => ((w : InfinitePlace F) → BruhatCompactSupport w.Completionˣ)
local notation "finiteTest" => ((v : S) → BruhatCompactSupport (v.val.adicCompletion F)ˣ)
local notation "archClass(" w ")" => IdeleClassGroup.ofCompletion (𝓞 F) F w
local notation "finiteClass(" v ")" => IdeleClassGroup.ofAdicCompletion (𝓞 F) F v
local notation "finiteVolume(" v ")" =>
  (finiteLocalMultiplicativeTamagawaMeasure F v
    ((HeightOneSpectrum.adicCompletionIntegers F v).units : Set _)).toReal
local notation "principalValues(" a "," b ")" =>
  ((∑ w : InfinitePlace F, infiniteConnesWeilPrincipalValue w (a w)) +
    ∑ v : S, ((Real.log (v.val.asIdeal.absNorm : ℝ) / finiteVolume(v.val) : ℝ) : ℂ) *
      finiteConnesWeilPrincipalValue v.val 1 (b v))

/-- Paper: (12.4.1.25)–(12.4.1.28), p. 519. After subtraction of the logarithmic
term the sum of sharp orbital masses tends to the norm-one volume times the local
principal values.
Deviation: Uses the sharp expression from (12.4.1.24) with R = λλ′. The replacement
of φ(g⁻¹) by φ(g) is the last step on p. 519. Appendix B.4 incorporates the real and
complex normalization factors in the archimedean distributions. -/
theorem sLocalTraceSharpMass_asymptotic
    (φ : BruhatCompactSupport C𝔽)
    (_hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F)))
    (_hRamified : ∀ v : V, differentIdeal ℤ (𝓞 F) ≤ v.asIdeal → v ∈ S)
    (_hOutside : ∀ (a : outsideIntegralIdeleUnits F S) (c : C𝔽),
      φ.val (QuotientGroup.mk a.val * c) = φ.val c)
    (f : BruhatCompactSupport Iₛ)
    (_hLift : ∀ g : Iₛ, HasSum (fun ξ : Hₛ ↦ f.val (ξ.val * g)) (φ.val (classAtS(g)))) :
    ∃ (a : archTest) (b : finiteTest) (M : ℝ → ℂ),
      (∀ (w : InfinitePlace F) (u : w.Completionˣ),
        (a w).val u = φ.val (archClass(w) u)) ∧
      (∀ (v : S) (u : (v.val.adicCompletion F)ˣ),
        (b v).val u = φ.val (finiteClass(v.val) u)) ∧
      (∀ᶠ R in atTop, HasSum (fun ξ : Hₛ ↦ sLocalTraceSharpMass f ξ R) (M R)) ∧
      Tendsto (fun R ↦ M R - (volume₁ : ℂ) * φ.val 1 * (Real.log R : ℂ))
        atTop (𝓝 ((volume₁ : ℂ) * principalValues(a, b))) := by sorry

-- TODO(paper-gap): Theorem 12.4.1.1 needs the actual smoothed PW quotient kernel
-- and a limit for its difference from the sharp orbital mass. Neither the cutoff
-- family with the independent lower bound nor the comparison is specified.
-- The following statement records the conclusion with that comparison exposed.

/-- Paper: Theorem 12.4.1.1, p. 514. The normalized quotient diagonal integral,
with its logarithmic term removed, tends to the sum of local principal values.
Deviation: The chosen quotient kernel must have integrable diagonals and agree
asymptotically with the summed sharp masses. These hypotheses expose the missing
comparison with the regularized Paley–Wiener operator. The limit is joint. -/
theorem sLocalTrace_asymptotic_of_sharp_comparison
    (φ : BruhatCompactSupport C𝔽)
    (_hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F)))
    (_hRamified : ∀ v : V, differentIdeal ℤ (𝓞 F) ≤ v.asIdeal → v ∈ S)
    (_hOutside : ∀ (a : outsideIntegralIdeleUnits F S) (c : C𝔽),
      φ.val (QuotientGroup.mk a.val * c) = φ.val c)
    (f : BruhatCompactSupport Iₛ)
    (_hLift : ∀ g : Iₛ, HasSum (fun ξ : Hₛ ↦ f.val (ξ.val * g)) (φ.val (classAtS(g))))
    (k : ℝ × ℝ → Jₛ → Jₛ → ℂ) (M : ℝ → ℂ)
    (_hSum : ∀ᶠ R in atTop, HasSum (fun ξ : Hₛ ↦ sLocalTraceSharpMass f ξ R) (M R))
    (_hDiag : ∀ᶠ p in atTop ×ˢ atTop, Integrable (fun x ↦ k p x x) μJ)
    (_hComparison : Tendsto
      (fun p : ℝ × ℝ ↦ (∫ x, k p x x ∂μJ) - M (p.1 * p.2))
      (atTop ×ˢ atTop) (𝓝 0)) :
    ∃ (a : archTest) (b : finiteTest),
      (∀ (w : InfinitePlace F) (u : w.Completionˣ),
        (a w).val u = φ.val (archClass(w) u)) ∧
      (∀ (v : S) (u : (v.val.adicCompletion F)ˣ),
        (b v).val u = φ.val (finiteClass(v.val) u)) ∧
      Tendsto (fun p : ℝ × ℝ ↦ (∫ x, k p x x ∂μJ) / (volume₁ : ℂ) -
        φ.val 1 * (Real.log (p.1 * p.2) : ℂ)) (atTop ×ˢ atTop) (𝓝 principalValues(a, b)) := by sorry

end RiemannMasullo
