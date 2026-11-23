module

public import RiemannMasullo.AppA_AlgebraicNT.Sec2b
public import RiemannMasullo.AppD_SchwartzBruhat.Sec1a
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.NumberTheory.NumberField.Units.Regulator
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.Topology.Algebra.Group.Units

import all RiemannMasullo.AppA_AlgebraicNT.Sec1  -- for the open integral subgroups
import RiemannMasullo.AppA_AlgebraicNT.Sec2  -- for the diagonal adelic basis
import all RiemannMasullo.AppD_SchwartzBruhat.Sec1a  -- for Weil disintegration
import RiemannMasullo.AppD_SchwartzBruhat.Sec1b  -- for duality of a quotient and its annihilator
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.LinearAlgebra.Countable
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.MeasureTheory.Measure.Haar.Extension
import Mathlib.MeasureTheory.Measure.Haar.Quotient
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Algebra.IsOpenUnits
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import RiemannMasullo.ForMathlib.Analysis.Fourier.LpSpace
import RiemannMasullo.ForMathlib.MeasureTheory.Group.Arithmetic
import RiemannMasullo.ForMathlib.MeasureTheory.Measure.Haar.Extension
import RiemannMasullo.ForMathlib.MeasureTheory.Measure.Haar.Unique
import RiemannMasullo.ForMathlib.MeasureTheory.Measure.Haar.Units
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace
import RiemannMasullo.ForMathlib.RingTheory.Trace.Defs
import RiemannMasullo.ForMathlib.Topology.Algebra.PontryaginDual.Real

/-! # Haar measures

Masullo, §A.3, pp. 555–562.
-/

@[expose] public noncomputable section

set_option maxSynthPendingDepth 8

namespace RiemannMasullo

open Function MeasureTheory NumberField IsDedekindDomain InfinitePlace.Completion Set
open scoped Classical ENNReal NNReal NumberField.AdeleRing Pointwise

variable (F : Type*) [Field F] [NumberField F]

local notation "Primes(" F ")" => HeightOneSpectrum (𝓞 F)
local notation "𝕀[" F "]" => IdeleGroup (𝓞 F) F
local notation "C[" F "]" => IdeleClassGroup (𝓞 F) F
local notation "P[" F "]" => IdeleGroup.principalSubgroup (𝓞 F) F
local notation "A[" F "]" => AddSubgroup.toSubgroup (AdeleRing.principalSubgroup (𝓞 F) F)
local notation "N[" F "]" => MonoidHom.ker (ideleNorm F)
local notation "C₁[" F "]" => MonoidHom.ker (ideleClassNorm F)

local instance (v : InfinitePlace F) : MeasurableSpace v.Completion := borel _
local instance : MeasurableSpace (InfiniteAdeleRing F) :=
  inferInstanceAs (MeasurableSpace ((v : InfinitePlace F) → v.Completion))
local instance (v : Primes(F)) : MeasurableSpace (v.adicCompletion F) := borel _
local instance (v : Primes(F)) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
local instance (v : Primes(F)) : LocallyCompactSpace (v.adicCompletion F) :=
  locallyCompactSpace_adicCompletion v
local instance (v : Primes(F)) : LocallyCompactSpace (v.adicCompletion F)ˣ :=
  (IsOpenUnits.isOpenEmbedding_unitsVal (M := v.adicCompletion F)).locallyCompactSpace
local instance (v : Primes(F)) : MeasurableSpace (v.adicCompletion F)ˣ := borel _
local instance (v : Primes(F)) : BorelSpace (v.adicCompletion F)ˣ := ⟨rfl⟩
local instance : MeasurableSpace 𝔸[F] := borel _
local instance : MeasurableSpace (Multiplicative 𝔸[F] ⧸ A[F]) := borel _
local instance : MeasurableSpace 𝕀[F] := borel _
local instance : MeasurableSpace C[F] := borel _
local instance : MeasurableSpace (C[F] ⧸ C₁[F]) := borel _
local instance : MeasurableSpace (𝕀[F] ⧸ N[F]) := borel _

variable (S : Finset (Primes(F)))

local notation "dₛ" => RingHom.comp (adeleProjection F S)
  (RingHom.comp (Subring.subtype (integralAdelesOutside F S)) (integralAdeleDiagonal F S))
local notation "Aₛ" => AddSubgroup.toSubgroup (AddMonoidHom.range (RingHom.toAddMonoidHom dₛ))
local notation "𝕀ₛ" => (SAdeleRing F S)ˣ
local notation "Nₛ" => MonoidHom.ker (sIdeleNorm F S)

local instance : MeasurableSpace (SAdeleRing F S) :=
  inferInstanceAs (MeasurableSpace (InfiniteAdeleRing F × ((v : S) → v.val.adicCompletion F)))
local instance : MeasurableSpace (Multiplicative (SAdeleRing F S) ⧸ Aₛ) := borel _
local instance : MeasurableSpace (𝕀ₛ ⧸ Nₛ) := borel _

open scoped IsDedekindDomain.FiniteAdeleRing RestrictedProduct in
/-- Paper: Definition A.3.1.1, p. 555. Exactly one regular additive Haar measure on
the adeles gives the additive quotient mass one when the diagonal has counting measure. -/
theorem additiveTamagawaMeasure_existsUnique :
    ∃! μ : Measure 𝔸[F], μ.IsAddHaarMeasure ∧ μ.Regular ∧
      ∃ ν : Measure (Multiplicative 𝔸[F] ⧸ A[F]),
        IsWeilQuotientMeasure A[F] (show Measure (Multiplicative 𝔸[F]) from μ)
          Measure.count ν ∧ ν univ = 1 := by
  classical
  let G := Multiplicative 𝔸[F]
  let H := A[F]
  let Q := G ⧸ H
  obtain ⟨-, hclosed, hdiscrete, -, -, hcompact, -, -⟩ := adele_additive_quotient.{_, 0} F
  let : CompactSpace Q := hcompact
  let : DiscreteTopology H := isDiscrete_iff_discreteTopology.mp hdiscrete
  let (v : Primes(F)) : CompactSpace (v.adicCompletionIntegers F) :=
    compactSpace_adicCompletionIntegers v
  let : Fact (∀ v : Primes(F), IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    ⟨fun v ↦ Valued.isOpen_valuationSubring _⟩
  let : LocallyCompactSpace 𝔸ᶠ[𝓞 F, F] := by
    change LocallyCompactSpace (Πʳ v : Primes(F), [v.adicCompletion F, v.adicCompletionIntegers F])
    infer_instance
  let : LocallyCompactSpace G := by
    change LocallyCompactSpace (InfiniteAdeleRing F × 𝔸ᶠ[𝓞 F, F])
    infer_instance
  let : T2Space G := by
    change T2Space (((v : InfinitePlace F) → v.Completion) ×
      (Πʳ v : Primes(F), [v.adicCompletion F, v.adicCompletionIntegers F]))
    infer_instance
  let : IsClosed (H : Set G) := hclosed
  let : BorelSpace G := ⟨rfl⟩
  let : BorelSpace Q := ⟨rfl⟩
  let : (Measure.count : Measure H).IsHaarMeasure :=
    { lt_top_of_isCompact := fun _ hs ↦ Measure.count_apply_lt_top.mpr hs.finite_of_discrete
      open_pos := fun _ _ hs ↦ Measure.count_ne_zero hs }
  let ses := TopologicalGroup.IsSES.ofClosedSubgroup H hclosed
  let count : Measure H := Measure.count
  let : count.IsHaarMeasure := inferInstanceAs (Measure.count : Measure H).IsHaarMeasure
  -- Normalize Haar measure on the compact quotient using the whole space.
  let K : TopologicalSpace.PositiveCompacts Q := ⟨⟨univ, isCompact_univ⟩, by simp⟩
  let ν : Measure Q := Measure.haarMeasure K
  have hν : ν univ = 1 := Measure.haarMeasure_self (K₀ := K)
  let μ := ses.inducedMeasure count ν
  let : μ.Regular := ses.inducedMeasure_regular count ν
  have hμ : ∀ f : C(G, ℂ), HasCompactSupport f →
      (∫ x, f x ∂μ) = ∫ q, lcaCosetIntegral H count f q ∂ν := by
    intro f hf
    let fc : CompactlySupportedContinuousMap G ℂ := ⟨f, hf⟩
    have hfiber (q : Q) : ses.pushforward count fc q = lcaCosetIntegral H count f q := by
      calc
        ses.pushforward count fc q =
            ses.pushforward count fc (QuotientGroup.mk' H q.out) :=
          congrArg (ses.pushforward count fc) (QuotientGroup.out_eq' q).symm
        _ = lcaCosetIntegral H count f q := ses.pushforward_apply_apply count fc q.out
    -- The induced measure formula for real functions applies to both complex coordinates.
    have hcoord (L : ℂ →L[ℝ] ℝ) :
        L (∫ x, f x ∂μ) = L (∫ q, ses.pushforward count fc q ∂ν) := by
      let g : CompactlySupportedContinuousMap G ℝ :=
        ⟨⟨fun x ↦ L (f x), L.continuous.comp f.continuous⟩, hf.comp_left L.map_zero⟩
      change L (∫ x, fc x ∂μ) = _
      rw [← L.integral_comp_comm (fc.integrable (μ := μ)),
        ← L.integral_comp_comm ((ses.pushforward count fc).integrable (μ := ν))]
      change (∫ x, g x ∂μ) = ∫ q, L (ses.pushforward count fc q) ∂ν
      rw [ses.integral_inducedMeasure, ses.integrate_apply]
      congr with q
      obtain ⟨x, rfl⟩ := ses.isOpenQuotientMap.surjective q
      rw [ses.pushforward_apply_apply, ses.pushforward_apply_apply,
        ← L.integral_comp_comm (ses.pullback fc x).integrable]
      rfl
    simp_rw [← hfiber]
    exact Complex.ext (hcoord Complex.reCLM) (hcoord Complex.imCLM)
  refine ⟨μ, ⟨?_, ses.inducedMeasure_regular count ν, ν, ⟨inferInstance, inferInstance, hμ⟩, hν⟩,
    ?_⟩
  · have hhaar := ses.isHaarMeasure_inducedMeasure count ν
    exact
      { toIsFiniteMeasureOnCompacts := hhaar.toIsFiniteMeasureOnCompacts
        toIsOpenPosMeasure := hhaar.toIsOpenPosMeasure
        map_add_left_eq_self := fun x ↦ hhaar.map_mul_left_eq_self (Multiplicative.ofAdd x) }
  rintro μ' ⟨-, hregular, ν', ⟨hhaar', hregular', hweil⟩, hν'⟩
  let : (show Measure G from μ').Regular := hregular
  let : ν'.IsHaarMeasure := hhaar'
  let : ν'.Regular := hregular'
  have heq : ν' = ν := by
    have hscale := Measure.isMulLeftInvariant_eq_smul_of_regular ν' ν
    have hmass := congrArg (fun m : Measure Q ↦ m univ) hscale
    change ν' univ = (ν'.haarScalarFactor ν : ℝ≥0∞) * ν univ at hmass
    have hfactor : ν'.haarScalarFactor ν = 1 := by
      rw [hν', hν, mul_one] at hmass
      exact ENNReal.coe_inj.mp hmass.symm
    rw [hscale, hfactor, one_smul]
  subst ν'
  apply Measure.ext_of_integral_eq_on_compactlySupported (X := G)
  intro f
  let fc : C(G, ℂ) := ⟨fun x ↦ (f x : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
  have hc : HasCompactSupport fc := f.hasCompactSupport.comp_left Complex.ofReal_zero
  have heq := (hweil fc hc).trans (hμ fc hc).symm
  apply Complex.ofReal_injective
  calc
    Complex.ofReal (∫ x : G, f x ∂(show Measure G from μ')) =
        ∫ x : G, (f x : ℂ) ∂(show Measure G from μ') := integral_complex_ofReal.symm
    _ = ∫ x : G, (f x : ℂ) ∂μ := heq
    _ = Complex.ofReal (∫ x : G, f x ∂μ) := integral_complex_ofReal

/-- Paper: Definition A.3.1.1, p. 555. The additive Tamagawa measure is the
adelic Haar measure normalized to give the quotient by the diagonal mass one. -/
def additiveTamagawaMeasure : Measure 𝔸[F] :=
  (additiveTamagawaMeasure_existsUnique F).exists.choose

/-- Paper: Definition A.3.1.1, p. 555. The adelic measure has a Weil quotient
of mass one with counting measure on the diagonal. -/
theorem additiveTamagawaMeasure_quotientVolume :
    ∃ ν : Measure (Multiplicative 𝔸[F] ⧸ A[F]),
      IsWeilQuotientMeasure A[F] (show Measure (Multiplicative 𝔸[F]) from
        additiveTamagawaMeasure F) Measure.count ν ∧ ν univ = 1 :=
  (Classical.choose_spec (additiveTamagawaMeasure_existsUnique F).exists).2.2

section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

local instance instMeasurableSpaceWeilQuotientForFundamentalDomain (H : Subgroup G) :
    MeasurableSpace (G ⧸ H) := borel _

/-- For a closed discrete subgroup with counting measure, the mass of a precompact
fundamental domain meeting every coset is the mass of the Weil quotient measure. -/
private theorem weilQuotientMeasure_univ_eq_measure_fundamentalDomain
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {H : Subgroup G} [Countable H] [DiscreteTopology H] (hH : IsClosed (H : Set G))
    {μ : Measure G} [μ.IsHaarMeasure] {ν : Measure (G ⧸ H)}
    (hν : IsWeilQuotientMeasure H μ Measure.count ν)
    (hνfinite : ν univ ≠ ⊤)
    {D : Set G} (hD : IsFundamentalDomain H.op D μ) (hcompact : IsCompact (closure D))
    (hcover : ∀ a : G, ∃ h : H.op, h • a ∈ D) :
    ν univ = μ D := by
  let π := QuotientGroup.mk' H
  let νD := (μ.restrict D).map π
  let : IsClosed (H : Set G) := hH
  let : BorelSpace (G ⧸ H) := ⟨rfl⟩
  have hπ : Continuous π := QuotientGroup.continuous_mk
  let count : Measure H := Measure.count
  let : count.IsHaarMeasure :=
    { lt_top_of_isCompact := fun _ hs ↦ Measure.count_apply_lt_top.mpr hs.finite_of_discrete
      open_pos := fun _ _ hs ↦ Measure.count_ne_zero hs }
  let ses := TopologicalGroup.IsSES.ofClosedSubgroup H hH
  have hsum (f : CompactlySupportedContinuousMap G ℝ) :
      QuotientGroup.automorphize (Γ := H) f = ses.pushforward count f := by
    funext q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective H q
    rw [ses.pushforward_apply_apply, integral_countable (ses.pullback f x).integrable]
    simp only [count, count_real_singleton, one_smul]
    change (∑' h : H.op, f (x * (h.val.unop : G))) = ∑' h : H, f (x * (h : G))
    exact (H.equivOp.tsum_eq (fun h : H.op ↦ f (x * h.val.unop))).symm
  -- A compactly supported function equal to one on the domain has positive periodization.
  obtain ⟨f, hf, -, hfc, hf₀⟩ :=
    exists_continuous_one_zero_of_isCompact hcompact isClosed_empty (disjoint_empty _)
  let f₀ : CompactlySupportedContinuousMap G ℝ := ⟨f, hfc⟩
  let c := ses.pushforward count f₀
  have hc (q : G ⧸ H) : 0 < c q := by
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective H q
    obtain ⟨h, hd⟩ := hcover a
    let d : G := h • a
    have hdq : π d = π a := QuotientGroup.mk_mul_of_mem a (H.equivOp.symm h).property
    change 0 < ses.pushforward count f₀ (π a)
    rw [← hdq, ses.pushforward_apply_apply]
    apply (integral_pos_iff_support_of_nonneg (fun _ ↦ (hf₀ _).1)
      (ses.pullback f₀ d).integrable).mpr
    apply pos_iff_ne_zero.mpr ∘ Measure.count_ne_zero
    exact ⟨1, by simpa only [Function.mem_support, ses.pullback_def, Subgroup.coe_subtype,
      Subgroup.coe_one, mul_one] using
        (show f d ≠ 0 from (hf (subset_closure hd)).trans_ne one_ne_zero)⟩
  -- Divide by the periodization so both quotient integrals test the constant one.
  let g : CompactlySupportedContinuousMap G ℝ :=
    ⟨⟨fun x ↦ (c (π x))⁻¹ • f₀ x,
      ((c.continuous.comp hπ).inv₀ fun x ↦ (hc (π x)).ne').smul f₀.continuous⟩,
      by
        change HasCompactSupport ((fun x : G ↦ (c (π x))⁻¹) • ⇑f₀)
        exact f₀.hasCompactSupport.smul_left⟩
  have hg : QuotientGroup.automorphize (Γ := H) g = fun _ ↦ 1 := by
    calc
      _ = (fun q ↦ (c q)⁻¹) • QuotientGroup.automorphize (Γ := H) f₀ :=
        QuotientGroup.automorphize_smul_left (⇑f₀) (fun q ↦ (c q)⁻¹)
      _ = _ := by
        rw [hsum f₀]
        funext q
        exact inv_mul_cancel₀ (hc q).ne'
  let fc : CompactlySupportedContinuousMap G ℂ :=
    ⟨⟨fun x ↦ (g x : ℂ), Complex.continuous_ofReal.comp g.continuous⟩,
      g.hasCompactSupport.comp_left Complex.ofReal_zero⟩
  have hcoset (q : G ⧸ H) :
      lcaCosetIntegral H count fc q = (ses.pushforward count g q : ℂ) := by
    have hp := ses.pushforward_apply_apply count g q.out
    have hq : π q.out = q := QuotientGroup.out_eq' q
    change ses.pushforward count g (π q.out) = _ at hp
    rw [hq] at hp
    rw [hp, lcaCosetIntegral]
    exact integral_complex_ofReal
  have hweil : (∫ x, g x ∂μ) = ∫ _q : G ⧸ H, (1 : ℝ) ∂ν := by
    have h := hν.2.2 fc.toContinuousMap fc.hasCompactSupport
    change (∫ x, (g x : ℂ) ∂μ) = ∫ q, lcaCosetIntegral H count fc q ∂ν at h
    simp_rw [hcoset, ← hsum g, hg, integral_complex_ofReal] at h
    exact Complex.ofReal_injective h
  have hmeas : AEStronglyMeasurable (QuotientGroup.automorphize (Γ := H) g) νD :=
    hg ▸ aestronglyMeasurable_const
  have hunfold := QuotientGroup.integral_eq_integral_automorphize hD g.integrable hmeas
  rw [hg] at hunfold
  have hmass : νD univ = μ D := by
    rw [Measure.map_apply hπ.measurable MeasurableSet.univ, Set.preimage_univ,
      Measure.restrict_apply_univ]
  have heq := hweil.symm.trans hunfold
  simp only [integral_const, smul_eq_mul, mul_one, measureReal_def] at heq
  change (ν univ).toReal = (νD univ).toReal at heq
  rw [hmass] at heq
  exact (ENNReal.toReal_eq_toReal_iff' hνfinite
    ((measure_mono subset_closure).trans_lt hcompact.measure_lt_top).ne).mp heq

end

open scoped IsDedekindDomain.FiniteAdeleRing RestrictedProduct in
/-- Paper: Definition A.3.1.1, p. 555. The additive Tamagawa measure of the
chosen adelic fundamental domain equals the mass of the additive quotient, namely one. -/
theorem additiveTamagawaMeasure_fundamentalDomain :
    additiveTamagawaMeasure F (adeleFundamentalDomain F (RingOfIntegers.basis F)) = 1 := by
  classical
  let G := Multiplicative 𝔸[F]
  let H := A[F]
  let μ : Measure G := additiveTamagawaMeasure F
  let b := RingOfIntegers.basis F
  let D : Set G := adeleFundamentalDomain F b
  obtain ⟨-, hclosed, hdiscrete, -⟩ := adele_additive_quotient.{_, 0} F
  let : DiscreteTopology H := isDiscrete_iff_discreteTopology.mp hdiscrete
  let : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  let : Countable H := (Set.countable_range (algebraMap F 𝔸[F])).to_subtype
  let (v : Primes(F)) : CompactSpace (v.adicCompletionIntegers F) :=
    compactSpace_adicCompletionIntegers v
  let : Fact (∀ v : Primes(F), IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    ⟨fun v ↦ Valued.isOpen_valuationSubring _⟩
  let : LocallyCompactSpace G := by
    change LocallyCompactSpace (InfiniteAdeleRing F ×
      (Πʳ v : Primes(F), [v.adicCompletion F, v.adicCompletionIntegers F]))
    infer_instance
  let : T2Space G := by
    change T2Space (((v : InfinitePlace F) → v.Completion) ×
      (Πʳ v : Primes(F), [v.adicCompletion F, v.adicCompletionIntegers F]))
    infer_instance
  let : BorelSpace G := ⟨rfl⟩
  let : BorelSpace (G ⧸ H) := ⟨rfl⟩
  have hμ := (Classical.choose_spec (additiveTamagawaMeasure_existsUnique F).exists)
  let : μ.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := hμ.1.toIsFiniteMeasureOnCompacts
      toIsOpenPosMeasure := hμ.1.toIsOpenPosMeasure
      map_mul_left_eq_self := fun x ↦ hμ.1.map_add_left_eq_self x.toAdd }
  have hmeas : MeasurableSet D := by
    have hinf : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
      change Continuous (fun x : InfiniteAdeleRing F ↦ InfiniteAdeleRing.ringEquiv_mixedSpace F x)
      simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
      exact (continuous_pi fun v ↦ (isometryEquivRealOfIsReal v.2).continuous.comp
        (continuous_apply v.1)).prodMk
        (continuous_pi fun v ↦ (isometryEquivComplexOfIsComplex v.2).continuous.comp
          (continuous_apply v.1))
    have hIntegral : IsOpen (integralAdelesOutside F ∅ : Set 𝔸[F]) := by
      simp only [integralAdelesOutside, Subring.coe_iInf, Set.iInter_ofPred, Finset.notMem_empty,
        not_false_eq_true, true_implies]
      exact (RestrictedProduct.isOpen_forall_mem (fun v : Primes(F) ↦
        Valued.isOpen_integer (v.adicCompletion F))).preimage continuous_snd
    let : BorelSpace 𝔸[F] := ⟨rfl⟩
    have hfst : Continuous (Prod.fst : 𝔸[F] → InfiniteAdeleRing F) := continuous_fst
    have hm : Measurable (fun a : 𝔸[F] ↦ InfiniteAdeleRing.ringEquiv_mixedSpace F a.1) :=
      Continuous.measurable (α := 𝔸[F]) (hinf.comp hfst)
    have hInt : MeasurableSet (integralAdelesOutside F ∅ : Set 𝔸[F]) := hIntegral.measurableSet
    exact ((ZSpan.fundamentalDomain_measurableSet _).preimage hm).inter hInt
  have hcover (a : G) : ∃ h : H.op, h • a ∈ D := by
    have ha : a.toAdd ∈ ⋃ x : F, algebraMap F 𝔸[F] x +ᵥ adeleFundamentalDomain F b :=
      (adeleFundamentalDomain_cover F b).symm ▸ mem_univ _
    obtain ⟨x, hx⟩ := Set.mem_iUnion.mp ha
    obtain ⟨d, hd, hda⟩ := Set.mem_vadd_set.mp hx
    let h : H := ⟨Multiplicative.ofAdd (algebraMap F 𝔸[F] x), ⟨x, rfl⟩⟩
    refine ⟨H.equivOp h⁻¹, ?_⟩
    change a * (h : G)⁻¹ ∈ D
    have ha : Multiplicative.ofAdd d * (h : G) = a := (add_comm _ _).trans hda
    rwa [← ha, mul_inv_cancel_right]
  have hD : IsFundamentalDomain H.op D μ := by
    refine IsFundamentalDomain.mk'' hmeas.nullMeasurableSet (Filter.Eventually.of_forall hcover) ?_
      (fun h ↦ (measurePreserving_smul h μ).quasiMeasurePreserving)
    · intro h hh
      obtain ⟨x, hx⟩ := (H.equivOp.symm h).property
      have hx0 : x ≠ 0 := by
        rintro rfl
        apply hh
        apply H.equivOp.symm.injective
        exact Subtype.ext (by simpa using hx.symm)
      have htranslate : (h • D : Set G) =
          (algebraMap F 𝔸[F] x +ᵥ adeleFundamentalDomain F b : Set 𝔸[F]) := by
        ext d
        simp only [Set.mem_smul_set]
        change (∃ a ∈ D, a.toAdd + (H.equivOp.symm h).val.toAdd = d.toAdd) ↔
          (∃ a ∈ D, algebraMap F 𝔸[F] x + a.toAdd = d.toAdd)
        change algebraMap F 𝔸[F] x = (H.equivOp.symm h).val.toAdd at hx
        simp only [hx, add_comm]
      rw [htranslate]
      exact (adeleFundamentalDomain_disjoint F b x hx0).aedisjoint
  have hcompact : IsCompact (closure D) := adeleFundamentalDomain_precompact F b
  obtain ⟨ν, hν, hmass⟩ := additiveTamagawaMeasure_quotientVolume F
  have hνfinite : ν univ ≠ ⊤ := hmass.trans_ne ENNReal.one_ne_top
  exact (weilQuotientMeasure_univ_eq_measure_fundamentalDomain hclosed hν hνfinite hD
    hcompact hcover).symm.trans hmass

/-- Paper: Definition A.3.1.1, p. 555. Exactly one regular additive Haar measure on
the S-adeles gives the quotient by the diagonal S-integers mass one. -/
theorem sAdditiveCovolumeOneMeasure_existsUnique :
    ∃! μ : Measure (SAdeleRing F S), μ.IsAddHaarMeasure ∧ μ.Regular ∧
      ∃ ν : Measure (Multiplicative (SAdeleRing F S) ⧸ Aₛ),
        IsWeilQuotientMeasure Aₛ (show Measure (Multiplicative (SAdeleRing F S)) from μ)
          Measure.count ν ∧ ν univ = 1 := by
  let G := Multiplicative (SAdeleRing F S)
  let H := Aₛ
  let Q := G ⧸ H
  obtain ⟨-, hclosed, hdiscrete, -, -, hcompact, -, -⟩ := sAdele_additive_quotient F S
  let : IsClosed (H : Set G) := hclosed
  let : DiscreteTopology H := isDiscrete_iff_discreteTopology.mp hdiscrete
  let : CompactSpace Q := hcompact
  let (v : Primes(F)) : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
  let (v : InfinitePlace F) : SecondCountableTopology v.Completion :=
    (isometry_extensionEmbedding v).isEmbedding.secondCountableTopology
  let (v : InfinitePlace F) : BorelSpace v.Completion := ⟨rfl⟩
  let : BorelSpace G := by
    change BorelSpace (((v : InfinitePlace F) → v.Completion) × ((v : S) → v.val.adicCompletion F))
    infer_instance
  let : LocallyCompactSpace G := by
    change LocallyCompactSpace (InfiniteAdeleRing F × ((v : S) → v.val.adicCompletion F))
    infer_instance
  let : T2Space G := by
    change T2Space (((v : InfinitePlace F) → v.Completion) × ((v : S) → v.val.adicCompletion F))
    infer_instance
  let : BorelSpace Q := ⟨rfl⟩
  let count : Measure H := Measure.count
  let : count.IsHaarMeasure :=
    { lt_top_of_isCompact := fun _ hs ↦ Measure.count_apply_lt_top.mpr hs.finite_of_discrete
      open_pos := fun _ _ hs ↦ Measure.count_ne_zero hs }
  let ses := TopologicalGroup.IsSES.ofClosedSubgroup H hclosed
  -- Start with Haar probability measure on the quotient and lift it using counting measure.
  let K : TopologicalSpace.PositiveCompacts Q := ⟨⟨univ, isCompact_univ⟩, by simp⟩
  let ν : Measure Q := Measure.haarMeasure K
  have hν : ν univ = 1 := Measure.haarMeasure_self (K₀ := K)
  let μ := ses.inducedMeasure count ν
  have hweil : IsWeilQuotientMeasure H μ count ν := by
    refine ⟨inferInstance, inferInstance, fun f hf ↦ ?_⟩
    let fc : CompactlySupportedContinuousMap G ℂ := ⟨f, hf⟩
    change (∫ x, fc x ∂μ) = _
    rw [integral_inducedMeasure_complex ses count ν fc, ses.integrate_apply]
    refine integral_congr_ae (Filter.Eventually.of_forall fun q ↦ ?_)
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    exact ses.pushforward_apply_apply count fc q.out
  refine ⟨μ, ⟨?_, ses.inducedMeasure_regular count ν, ν, hweil, hν⟩, ?_⟩
  · have hhaar := ses.isHaarMeasure_inducedMeasure count ν
    exact
      { toIsFiniteMeasureOnCompacts := hhaar.toIsFiniteMeasureOnCompacts
        toIsOpenPosMeasure := hhaar.toIsOpenPosMeasure
        map_add_left_eq_self := fun x ↦ hhaar.map_mul_left_eq_self (Multiplicative.ofAdd x) }
  rintro μ' ⟨-, hregular, ν', ⟨hhaar', hregular', hweil'⟩, hν'⟩
  let : (show Measure G from μ').Regular := hregular
  let : ν'.IsHaarMeasure := hhaar'
  let : ν'.Regular := hregular'
  have heq : ν' = ν := by
    have hscale := Measure.isMulLeftInvariant_eq_smul_of_regular ν' ν
    have hmass := congrArg (fun m : Measure Q ↦ m univ) hscale
    change ν' univ = (ν'.haarScalarFactor ν : ℝ≥0∞) * ν univ at hmass
    rw [hν', hν, mul_one] at hmass
    rw [hscale, ENNReal.coe_inj.mp hmass.symm, one_smul]
  subst ν'
  apply Measure.ext_of_integral_eq_on_compactlySupported (X := G)
  intro f
  let fc : C(G, ℂ) := ⟨fun x ↦ (f x : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
  have hc : HasCompactSupport fc := f.hasCompactSupport.comp_left Complex.ofReal_zero
  apply Complex.ofReal_injective
  calc
    Complex.ofReal (∫ x : G, f x ∂(show Measure G from μ')) =
        ∫ x : G, (f x : ℂ) ∂(show Measure G from μ') := integral_complex_ofReal.symm
    _ = ∫ x : G, (f x : ℂ) ∂μ := (hweil' fc hc).trans (hweil.2.2 fc hc).symm
    _ = Complex.ofReal (∫ x : G, f x ∂μ) := integral_complex_ofReal

/-- Paper: Definition A.3.1.1, p. 555. This normalization gives the additive
quotient by the diagonal S-integers mass one.
Deviation: The notation distinguishes it from the product measure of Definition A.3.4.1. -/
def sAdditiveCovolumeOneMeasure : Measure (SAdeleRing F S) :=
  (sAdditiveCovolumeOneMeasure_existsUnique F S).exists.choose

/-- Paper: Definition A.3.1.1, p. 555. An S-adelic fundamental domain has mass one
for the additive measure normalized by the quotient. -/
theorem sAdditiveCovolumeOneMeasure_fundamentalDomain :
    sAdditiveCovolumeOneMeasure F S
      (sAdeleFundamentalDomain F S (RingOfIntegers.basis F)) = 1 := by
  classical
  let G := Multiplicative (SAdeleRing F S)
  let H := Aₛ
  let μ : Measure G := sAdditiveCovolumeOneMeasure F S
  let b := RingOfIntegers.basis F
  let D : Set G := sAdeleFundamentalDomain F S b
  let I := integralAdelesOutside F S
  let p := adeleProjection F S
  obtain ⟨-, hclosed, hdiscrete, -⟩ := sAdele_additive_quotient F S
  let : DiscreteTopology H := isDiscrete_iff_discreteTopology.mp hdiscrete
  let : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  let : Countable ((S : Set (Primes(F))).integer F) := inferInstance
  let : Countable H := (Set.countable_range dₛ).to_subtype
  let (v : Primes(F)) : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
  let (v : InfinitePlace F) : SecondCountableTopology v.Completion :=
    (isometry_extensionEmbedding v).isEmbedding.secondCountableTopology
  let (v : InfinitePlace F) : BorelSpace v.Completion := ⟨rfl⟩
  let : BorelSpace (InfiniteAdeleRing F) :=
    inferInstanceAs (BorelSpace ((v : InfinitePlace F) → v.Completion))
  let : BorelSpace G := by
    change BorelSpace (((v : InfinitePlace F) → v.Completion) × ((v : S) → v.val.adicCompletion F))
    infer_instance
  let : LocallyCompactSpace G := by
    change LocallyCompactSpace (InfiniteAdeleRing F × ((v : S) → v.val.adicCompletion F))
    infer_instance
  let : T2Space G := by
    change T2Space (((v : InfinitePlace F) → v.Completion) × ((v : S) → v.val.adicCompletion F))
    infer_instance
  obtain ⟨hμ, -, ν, hν, hmass⟩ :=
    Classical.choose_spec (sAdditiveCovolumeOneMeasure_existsUnique F S).exists
  let : μ.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := hμ.toIsFiniteMeasureOnCompacts
      toIsOpenPosMeasure := hμ.toIsOpenPosMeasure
      map_mul_left_eq_self := fun x ↦ hμ.map_add_left_eq_self x.toAdd }
  obtain ⟨e, -, -, he⟩ := integralAdelesOutside_factors F S
  have hlift (a : SAdeleRing F S) : ∃ c : I, p c.val = a :=
    ⟨e.symm (a, 0), (he _).1.symm.trans (congrArg Prod.fst (e.apply_symm_apply _))⟩
  have hIntegral (a : 𝔸[F]) (ha : a ∈ adeleFundamentalDomain F b) : a ∈ I := by
    have h := ha.2
    simp only [I, integralAdelesOutside, Subring.mem_iInf, Finset.notMem_empty, not_false_eq_true,
      true_implies] at h ⊢
    exact fun v _ ↦ h v
  -- On adeles integral outside S, membership in the two domains agrees under projection.
  have hproject (a : I) : p a.val ∈ D ↔ a.val ∈ adeleFundamentalDomain F b := by
    change (_ ∧ ∀ v : S, a.val.2 v.val ∈ v.val.adicCompletionIntegers F) ↔
      (_ ∧ a.val ∈ integralAdelesOutside F ∅)
    refine and_congr_right fun _ ↦ ?_
    have houtside := a.property
    simp only [I, integralAdelesOutside, Subring.mem_iInf, Finset.notMem_empty, not_false_eq_true,
      true_implies] at houtside ⊢
    refine ⟨fun h v ↦ ?_, fun h v ↦ h v.val⟩
    by_cases hv : v ∈ S
    · exact h ⟨v, hv⟩
    · exact houtside v hv
  have hmeas : MeasurableSet D := by
    have hinf : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
      change Continuous (fun x : InfiniteAdeleRing F ↦ InfiniteAdeleRing.ringEquiv_mixedSpace F x)
      simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
      exact (continuous_pi fun v ↦ (isometryEquivRealOfIsReal v.2).continuous.comp
        (continuous_apply v.1)).prodMk
        (continuous_pi fun v ↦ (isometryEquivComplexOfIsComplex v.2).continuous.comp
          (continuous_apply v.1))
    have hinfMeas : MeasurableSet (infiniteAdeleFundamentalDomain F b) :=
      (ZSpan.fundamentalDomain_measurableSet _).preimage hinf.measurable
    have hfinMeas : MeasurableSet {x : ∀ v : S, v.val.adicCompletion F |
        ∀ v : S, x v ∈ v.val.adicCompletionIntegers F} :=
      MeasurableSet.univ_pi' fun _ ↦ (Valued.isClosed_integer _).measurableSet
    exact hinfMeas.prod hfinMeas
  have hcompact : IsCompact (closure D) := by
    have hp : Continuous p :=
      continuous_fst.prodMk (continuous_pi fun v ↦
        (RestrictedProduct.continuous_eval v.val).comp continuous_snd)
    refine ((adeleFundamentalDomain_precompact F b).image hp).closure_of_subset ?_
    intro a ha
    obtain ⟨c, hc⟩ := hlift a
    exact ⟨c.val, subset_closure ((hproject c).mp (hc.symm ▸ ha)), hc⟩
  have hcover (a : G) : ∃ h : H.op, h • a ∈ D := by
    obtain ⟨c, hc⟩ := hlift a.toAdd
    have hcu : c.val ∈ ⋃ x : F, algebraMap F 𝔸[F] x +ᵥ adeleFundamentalDomain F b :=
      (adeleFundamentalDomain_cover F b).symm ▸ mem_univ _
    obtain ⟨x, hx⟩ := Set.mem_iUnion.mp hcu
    obtain ⟨y, hy, hxy⟩ := Set.mem_vadd_set.mp hx
    change algebraMap F 𝔸[F] x + y = c.val at hxy
    have hxI : algebraMap F 𝔸[F] x ∈ I := by
      have h := I.sub_mem c.property (hIntegral y hy)
      rwa [← hxy, add_sub_cancel_right] at h
    let xS : (S : Set (Primes(F))).integer F :=
      ⟨x, (diagonal_mem_integralAdelesOutside F S x).mp hxI⟩
    let h : H := ⟨Multiplicative.ofAdd (dₛ xS), ⟨xS, rfl⟩⟩
    have hd : Multiplicative.ofAdd (p y) * (h : G) = a := by
      change p y + p (algebraMap F 𝔸[F] x) = a.toAdd
      rw [add_comm, ← map_add, hxy, hc]
    refine ⟨H.equivOp h⁻¹, ?_⟩
    change a * (h : G)⁻¹ ∈ D
    rw [← hd, mul_inv_cancel_right]
    exact (hproject ⟨y, hIntegral y hy⟩).mpr hy
  have hD : IsFundamentalDomain H.op D μ := by
    refine IsFundamentalDomain.mk'' hmeas.nullMeasurableSet (Filter.Eventually.of_forall hcover) ?_
      (fun h ↦ (measurePreserving_smul h μ).quasiMeasurePreserving)
    intro h hh
    apply Disjoint.aedisjoint
    apply Set.disjoint_left.mpr
    intro a ha haD
    obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.mp ha
    obtain ⟨x, hx⟩ := (H.equivOp.symm h).property
    change dₛ x = (H.equivOp.symm h).val.toAdd at hx
    have hx0 : (x : F) ≠ 0 := by
      intro hzero
      have : x = 0 := Subtype.ext hzero
      subst x
      apply hh
      apply H.equivOp.symm.injective
      exact Subtype.ext (by simpa using hx.symm)
    obtain ⟨c, hc⟩ := hlift y.toAdd
    let a₀ : I := integralAdeleDiagonal F S x + c
    have ha₀ : p a₀.val ∈ D := by
      change p (algebraMap F 𝔸[F] (x : F) + c.val) ∈ D
      rw [map_add, hc, show p (algebraMap F 𝔸[F] (x : F)) = dₛ x from rfl, hx, add_comm]
      exact haD
    refine Set.disjoint_left.mp (adeleFundamentalDomain_disjoint F b (x : F) hx0)
      (Set.mem_vadd_set.mpr ⟨c.val, (hproject c).mp (hc.symm ▸ hy), rfl⟩)
      ((hproject a₀).mp ha₀)
  exact (weilQuotientMeasure_univ_eq_measure_fundamentalDomain (μ := μ) hclosed hν
    (hmass.trans_ne ENNReal.one_ne_top) hD hcompact hcover).symm.trans hmass

/-- Paper: Definition A.3.1.2(1)–(2), p. 556. Transfer Lebesgue measure from the
real line or twice plane Lebesgue measure from the complex line to the completion. -/
def infiniteLocalAdditiveTamagawaMeasure (v : InfinitePlace F) : Measure v.Completion :=
  if h : v.IsReal then
    Measure.map (ringEquivRealOfIsReal h).symm (volume : Measure ℝ)
  else
    Measure.map (ringEquivComplexOfIsComplex (InfinitePlace.not_isReal_iff_isComplex.mp h)).symm
      (2 • (volume : Measure ℂ))

/-- Paper: Definition A.3.1.2(1)–(2), p. 556. The local archimedean additive measure
assigns mass one to the real unit interval and mass two to the complex unit square. -/
theorem infiniteLocalAdditiveTamagawaMeasure_unitBox (v : InfinitePlace F) :
    (∀ h : v.IsReal, infiniteLocalAdditiveTamagawaMeasure F v
      ((ringEquivRealOfIsReal h).symm '' Icc (0 : ℝ) 1) = 1) ∧
    (∀ h : v.IsComplex, infiniteLocalAdditiveTamagawaMeasure F v
      ((ringEquivComplexOfIsComplex h).symm '' {z : ℂ | z.re ∈ Icc 0 1 ∧ z.im ∈ Icc 0 1}) = 2) :=
  by
    let : BorelSpace v.Completion := ⟨rfl⟩
    constructor
    · intro h
      rw [infiniteLocalAdditiveTamagawaMeasure, dite_eq_left h]
      let e := (isometryEquivRealOfIsReal h).symm.toHomeomorph.toMeasurableEquiv
      change (volume : Measure ℝ).map e (e '' Icc 0 1) = 1
      rw [e.map_apply, e.injective.preimage_image]
      simp [Real.volume_Icc]
    · intro h
      rw [infiniteLocalAdditiveTamagawaMeasure,
        dite_eq_right (InfinitePlace.not_isReal_iff_isComplex.mpr h)]
      let e := (isometryEquivComplexOfIsComplex h).symm.toHomeomorph.toMeasurableEquiv
      let square := Complex.measurableEquivRealProd ⁻¹' (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
      change Measure.map e (2 • (volume : Measure ℂ)) (e '' square) = 2
      rw [e.map_apply, e.injective.preimage_image]
      have hvolume : volume square = 1 := by
        dsimp only [square]
        rw [Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv,
          Measure.volume_eq_prod, Measure.prod_prod]
        simp [Real.volume_Icc]
      rw [two_nsmul, add_apply, hvolume]
      norm_num

-- The exponent of v in the global different is the exponent of the local different.
local notation "differentExp(" F ", " v ")" =>
  multiplicity (HeightOneSpectrum.asIdeal v) (differentIdeal ℤ (𝓞 F))
local notation "differentMass(" F ", " v ")" =>
  Inv.inv (ENNReal.ofReal (Real.sqrt (Nat.cast (Ideal.absNorm (HeightOneSpectrum.asIdeal v)) ^
    differentExp(F, v))))

/-- Paper: Definition A.3.1.2(3), p. 556. Scale additive Haar measure so that the
integer ring has mass equal to the inverse square root of the norm of the local different.
Deviation: The norm is computed using the corresponding exponent in the global different. -/
def finiteLocalAdditiveTamagawaMeasure (v : Primes(F)) : Measure (v.adicCompletion F) :=
  let μ := Measure.addHaar (G := v.adicCompletion F)
  (differentMass(F, v) / μ (v.adicCompletionIntegers F : Set (v.adicCompletion F))) • μ

/-- Paper: Definition A.3.1.2(3), p. 556. The mass of the local integer ring is
the inverse square root of the local different norm. -/
theorem finiteLocalAdditiveTamagawaMeasure_integers (v : Primes(F)) :
    finiteLocalAdditiveTamagawaMeasure F v (v.adicCompletionIntegers F : Set (v.adicCompletion F)) =
      differentMass(F, v) := by
  let O := (v.adicCompletionIntegers F : Set (v.adicCompletion F))
  have hO : IsOpen O := Valued.isOpen_valuationSubring _
  have hK : IsCompact O := isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v)
  let μ := Measure.addHaar (G := v.adicCompletion F)
  have hpos := hO.measure_pos μ ⟨0, (v.adicCompletionIntegers F).zero_mem⟩
  exact ENNReal.div_mul_cancel hpos.ne' (hK.measure_ne_top (μ := μ))

/-- Paper: Definition A.3.1.2, p. 556. The local additive Tamagawa measures
are additive Haar measures on their completions. -/
theorem finiteLocalAdditiveTamagawaMeasure_isAddHaar (v : Primes(F)) :
    (finiteLocalAdditiveTamagawaMeasure F v).IsAddHaarMeasure := by
  let μ := Measure.addHaar (G := v.adicCompletion F)
  let O := (v.adicCompletionIntegers F : Set (v.adicCompletion F))
  have hO : IsOpen O := Valued.isOpen_valuationSubring _
  have hK : IsCompact O := isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v)
  have hmass := hO.measure_pos μ ⟨0, (v.adicCompletionIntegers F).zero_mem⟩
  have hnorm : 0 < (v.asIdeal.absNorm : ℝ) :=
    Nat.cast_pos.mpr (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v))
  have hsqrt := Real.sqrt_pos_of_pos (pow_pos hnorm (differentExp(F, v)))
  change ((differentMass(F, v) / μ O) • μ).IsAddHaarMeasure
  exact Measure.IsAddHaarMeasure.smul μ
    (ENNReal.div_ne_zero.mpr ⟨ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top,
      hK.measure_ne_top (μ := μ)⟩)
    (ENNReal.div_ne_top (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hsqrt).ne') hmass.ne')

/-- Paper: §A.3.1, p. 556. The local different contributes mass one at
all but finitely many places, so the finite-tail products have finite support. -/
theorem finiteLocalTamagawaMass_finite :
    {v : Primes(F) | differentMass(F, v) ≠ 1}.Finite := by
  have hDifferent : differentIdeal ℤ (𝓞 F) ≠ (0 : Ideal (𝓞 F)) := differentIdeal_ne_bot
  refine (Ideal.finite_factors hDifferent).subset ?_
  intro v hv
  by_contra h
  exact hv (by simp [multiplicity_eq_zero_of_not_dvd h])

open scoped IsDedekindDomain.FiniteAdeleRing RestrictedProduct in
section

omit [NumberField F] in
/-- The archimedean factors are additive Haar measures by transport from the real and
complex lines. -/
private theorem infiniteLocalAdditiveTamagawaMeasure_haar (v : InfinitePlace F) :
    (infiniteLocalAdditiveTamagawaMeasure F v).IsAddHaarMeasure := by
  let : BorelSpace v.Completion := ⟨rfl⟩
  by_cases h : v.IsReal
  · rw [infiniteLocalAdditiveTamagawaMeasure, dite_eq_left h]
    exact (ringEquivRealOfIsReal h).symm.toAddEquiv.isAddHaarMeasure_map volume
      (isometryEquivRealOfIsReal h).symm.continuous (isometryEquivRealOfIsReal h).continuous
  · let hc := InfinitePlace.not_isReal_iff_isComplex.mp h
    rw [infiniteLocalAdditiveTamagawaMeasure, dite_eq_right h]
    have : (2 • (volume : Measure ℂ)).IsAddHaarMeasure := by
      rw [show 2 • (volume : Measure ℂ) = (2 : ℝ≥0∞) • volume by simp [two_smul]]
      exact Measure.IsAddHaarMeasure.smul (μ := (volume : Measure ℂ)) (by norm_num) (by simp)
    exact (ringEquivComplexOfIsComplex hc).symm.toAddEquiv.isAddHaarMeasure_map _
      (isometryEquivComplexOfIsComplex hc).symm.continuous
      (isometryEquivComplexOfIsComplex hc).continuous

/-- In mixed real and complex coordinates, the archimedean product measure is Lebesgue
measure multiplied by two for each complex place. -/
private theorem infiniteLocalAdditiveTamagawaMeasure_map_mixedSpace :
    (Measure.pi (infiniteLocalAdditiveTamagawaMeasure F)).map
        (InfiniteAdeleRing.ringEquiv_mixedSpace F) =
      ((2 : ℝ≥0∞) ^ InfinitePlace.nrComplexPlaces F) • (volume : Measure (mixedEmbedding.mixedSpace F)) := by
  let μ := infiniteLocalAdditiveTamagawaMeasure F
  let (v : InfinitePlace F) : BorelSpace v.Completion := ⟨rfl⟩
  let (v : InfinitePlace F) : SecondCountableTopology v.Completion :=
    (isometry_extensionEmbedding v).isEmbedding.secondCountableTopology
  let (v : InfinitePlace F) : (μ v).IsAddHaarMeasure :=
    infiniteLocalAdditiveTamagawaMeasure_haar F v
  have hsplit := measurePreserving_piEquivPiSubtypeProd μ (fun v ↦ v.IsReal)
  let reindex : {v : InfinitePlace F // ¬ v.IsReal} ≃ {v : InfinitePlace F // v.IsComplex} :=
    Equiv.subtypeEquivRight fun _ ↦ InfinitePlace.not_isReal_iff_isComplex
  have hr (v : {v : InfinitePlace F // v.IsReal}) :
      MeasurePreserving (ringEquivRealOfIsReal v.2) (μ v) volume := by
    let e := (isometryEquivRealOfIsReal v.2).toHomeomorph.toMeasurableEquiv
    refine ⟨e.measurable, ?_⟩
    change (infiniteLocalAdditiveTamagawaMeasure F v).map e = _
    rw [infiniteLocalAdditiveTamagawaMeasure, dite_eq_left v.2]
    change (volume.map e.symm).map e = _
    rw [Measure.map_map e.measurable e.symm.measurable, e.self_comp_symm, Measure.map_id]
  have hc (v : {v : InfinitePlace F // ¬ v.IsReal}) :
      MeasurePreserving (ringEquivComplexOfIsComplex (reindex v).2)
        (μ v) ((2 : ℝ≥0) • (volume : Measure ℂ)) := by
    let e := (isometryEquivComplexOfIsComplex (reindex v).2).toHomeomorph.toMeasurableEquiv
    refine ⟨e.measurable, ?_⟩
    change (infiniteLocalAdditiveTamagawaMeasure F v).map e = _
    rw [infiniteLocalAdditiveTamagawaMeasure, dite_eq_right v.2]
    change (Measure.map e.symm (2 • (volume : Measure ℂ))).map e = _
    rw [show 2 • (volume : Measure ℂ) = (2 : ℝ≥0) • volume by simp [two_smul]]
    rw [Measure.map_map e.measurable e.symm.measurable, e.self_comp_symm, Measure.map_id]
  have hright := (measurePreserving_piCongrLeft
    (fun _ : {v : InfinitePlace F // v.IsComplex} ↦ (2 : ℝ≥0) • (volume : Measure ℂ)) reindex).comp
      (measurePreserving_pi (ι := {v : InfinitePlace F // ¬ v.IsReal}) _ _ hc)
  let μreal := fun v : {v : InfinitePlace F // v.IsReal} ↦ μ v
  let μcomplex := fun v : {v : InfinitePlace F // ¬ v.IsReal} ↦ μ v
  let (v : {v : InfinitePlace F // v.IsReal}) : SigmaFinite (μreal v) :=
    inferInstanceAs (SigmaFinite (μ v.val))
  let (v : {v : InfinitePlace F // ¬ v.IsReal}) : SigmaFinite (μcomplex v) :=
    inferInstanceAs (SigmaFinite (μ v.val))
  let : SigmaFinite (Measure.pi μreal) := Measure.pi.sigmaFinite μreal
  let : SigmaFinite (Measure.pi μcomplex) := Measure.pi.sigmaFinite μcomplex
  have hleft := measurePreserving_pi μreal (fun _ ↦ volume) hr
  let hreal : SFinite (Measure.pi μreal) := inferInstance
  let hcomplex : SFinite (Measure.pi μcomplex) := inferInstance
  have hmap := (hleft.prod (μc := Measure.pi μcomplex) hright).comp hsplit
  let μr : Measure ({v : InfinitePlace F // v.IsReal} → ℝ) := volume
  let μc : Measure ({v : InfinitePlace F // v.IsComplex} → ℂ) := volume
  let k : ℝ≥0 := 2 ^ InfinitePlace.nrComplexPlaces F
  have hpow : (Measure.pi fun _ : {v : InfinitePlace F // v.IsComplex} ↦
      (2 : ℝ≥0) • (volume : Measure ℂ)) = k • μc := by
    apply Measure.pi_eq
    intro T hT
    rw [Measure.coe_nnreal_smul_apply, show μc = Measure.pi (fun _ ↦ volume) from volume_pi,
      Measure.pi_pi]
    simp only [Measure.coe_nnreal_smul_apply, k, ENNReal.coe_pow, ENNReal.coe_ofNat,
      Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, InfinitePlace.nrComplexPlaces]
  have hmap' : (Measure.pi μ).map (InfiniteAdeleRing.ringEquiv_mixedSpace F) =
      μr.prod (Measure.pi fun _ : {v : InfinitePlace F // v.IsComplex} ↦
        (2 : ℝ≥0) • (volume : Measure ℂ)) := by
    rw [show μr = Measure.pi (fun _ ↦ volume) from volume_pi]
    exact hmap.map_eq
  rw [hmap', hpow]
  have hk : (k : ℝ≥0∞) = (2 : ℝ≥0∞) ^ InfinitePlace.nrComplexPlaces F := by simp [k]
  rw [← hk, ← ENNReal.smul_def]
  change μr.prod (k • μc) = k • μr.prod μc
  refine Measure.prod_eq fun U V _ _ ↦ ?_
  rw [Measure.coe_nnreal_smul_apply, Measure.prod_prod, Measure.coe_nnreal_smul_apply,
    mul_left_comm]

/-- The archimedean fundamental domain has local product mass the square root of the
absolute discriminant. -/
private theorem infiniteAdeleFundamentalDomain_tamagawaMass :
    let B := infiniteAdeleFundamentalDomain F (RingOfIntegers.basis F)
    MeasurableSet B ∧
      Measure.pi (infiniteLocalAdditiveTamagawaMeasure F) B =
        ENNReal.ofReal (Real.sqrt (↑(discr F).natAbs : ℝ)) := by
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  let D := ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F)
  let (v : InfinitePlace F) : BorelSpace v.Completion := ⟨rfl⟩
  let (v : InfinitePlace F) : SecondCountableTopology v.Completion :=
    (isometry_extensionEmbedding v).isEmbedding.secondCountableTopology
  let : BorelSpace (InfiniteAdeleRing F) :=
    inferInstanceAs (BorelSpace ((v : InfinitePlace F) → v.Completion))
  have he : Continuous e := by
    change Continuous (fun x : InfiniteAdeleRing F ↦ InfiniteAdeleRing.ringEquiv_mixedSpace F x)
    simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    exact (continuous_pi fun v ↦ (isometryEquivRealOfIsReal v.2).continuous.comp
      (continuous_apply v.1)).prodMk
      (continuous_pi fun v ↦ (isometryEquivComplexOfIsComplex v.2).continuous.comp
        (continuous_apply v.1))
  have hD : MeasurableSet D := ZSpan.fundamentalDomain_measurableSet _
  have hB : infiniteAdeleFundamentalDomain F (RingOfIntegers.basis F) = e ⁻¹' D := by
    unfold infiniteAdeleFundamentalDomain
    dsimp only [D]
    congr 2
    apply DFunLike.ext
    intro i
    rw [Module.Basis.ofZLatticeBasis_apply, Module.Basis.map_apply,
      mixedEmbedding.latticeBasis_apply, integralBasis_apply]
    rfl
  dsimp only
  rw [hB, ← Measure.map_apply he.measurable hD, infiniteLocalAdditiveTamagawaMeasure_map_mixedSpace,
    smul_apply, smul_eq_mul, mixedEmbedding.volume_fundamentalDomain_latticeBasis]
  refine ⟨hD.preimage he.measurable, ?_⟩
  rw [← mul_assoc, ← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by simp), one_pow, one_mul]
  rw [← ENNReal.ofReal_coe_nnreal, Real.coe_sqrt, coe_nnNorm, Int.norm_eq_abs, Nat.cast_natAbs, Int.cast_abs]

/-- The product of the local integer masses is the reciprocal square root of the
absolute discriminant. -/
private theorem finiteLocalTamagawaMass_finprod :
    (∏ᶠ v : Primes(F), differentMass(F, v)) =
      (ENNReal.ofReal (Real.sqrt (↑(discr F).natAbs : ℝ)))⁻¹ := by
  let J := differentIdeal ℤ (𝓞 F)
  have hJ : J ≠ ⊥ := differentIdeal_ne_bot
  let T := (Ideal.finite_factors hJ).toFinset
  have hout (v : Primes(F)) (hv : v ∉ T) : differentExp(F, v) = 0 := by
    apply multiplicity_eq_zero_of_not_dvd
    simpa [T, J] using hv
  have hfactor : ∏ v ∈ T, v.asIdeal ^ differentExp(F, v) = J := by
    rw [← finprod_eq_finsetProd_of_mulSupport_subset
      (f := fun v : Primes(F) ↦ v.asIdeal ^ differentExp(F, v))]
    · exact Ideal.finprod_heightOneSpectrum_pow_multiplicity hJ
    · intro v hv
      by_contra hn
      exact hv (by simp [hout v hn])
  have hnorm : (∏ v ∈ T, (↑(Ideal.absNorm v.asIdeal) : ℝ) ^ differentExp(F, v)) =
      (↑(discr F).natAbs : ℝ) := by
    exact_mod_cast (by
      simpa only [map_prod, map_pow, J, NumberField.absNorm_differentIdeal F (𝓞 F)] using
        congrArg (fun I : Ideal (𝓞 F) ↦ Ideal.absNorm I) hfactor :
      (∏ v ∈ T, Ideal.absNorm v.asIdeal ^ differentExp(F, v)) = (discr F).natAbs)
  rw [finprod_eq_finsetProd_of_mulSupport_subset _ (s := T)]
  · rw [← ENNReal.prod_inv_distrib, ← ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦ Real.sqrt_nonneg _),
      ← Real.sqrt_prod T (fun _ _ ↦ by positivity), hnorm]
    exact fun v _ w _ _ ↦ Or.inr ENNReal.ofReal_ne_top
  · intro v hv
    by_contra hn
    exact hv (by simp [hout v hn])

/-- On the open subring of adeles integral outside S, restriction followed by projection
to the S-adeles preserves the Haar property. The omitted local integer factors are compact. -/
private theorem additiveTamagawaMeasure_projected_haar :
    let I := integralAdelesOutside F S
    ∃ μ : Measure (SAdeleRing F S), μ.IsAddHaarMeasure ∧
      ∀ W : Set (SAdeleRing F S), MeasurableSet W →
        μ W = additiveTamagawaMeasure F {a | a ∈ I ∧ adeleProjection F S a ∈ W} := by
  let I := integralAdelesOutside F S
  let p := (adeleProjection F S).comp I.subtype
  let (v : Primes(F)) : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
  let (v : Primes(F)) : CompactSpace (v.adicCompletionIntegers F) :=
    compactSpace_adicCompletionIntegers v
  let (v : InfinitePlace F) : SecondCountableTopology v.Completion :=
    (isometry_extensionEmbedding v).isEmbedding.secondCountableTopology
  let (v : InfinitePlace F) : BorelSpace v.Completion := ⟨rfl⟩
  let : BorelSpace (SAdeleRing F S) :=
    inferInstanceAs (BorelSpace (((v : InfinitePlace F) → v.Completion) ×
      ((v : S) → v.val.adicCompletion F)))
  let : LocallyCompactSpace (SAdeleRing F S) :=
    inferInstanceAs (LocallyCompactSpace (InfiniteAdeleRing F × ((v : S) → v.val.adicCompletion F)))
  let : T2Space (SAdeleRing F S) :=
    inferInstanceAs (T2Space (((v : InfinitePlace F) → v.Completion) ×
      ((v : S) → v.val.adicCompletion F)))
  let : BorelSpace 𝔸[F] := ⟨rfl⟩
  let hAdd : MeasurableAdd 𝔸[F] := by
    let : Fact (∀ v : Primes(F), IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
      ⟨fun v ↦ Valued.isOpen_valuationSubring _⟩
    exact ContinuousAdd.measurableAdd
  let : MeasurableSpace I := borel _
  let : BorelSpace I := ⟨rfl⟩
  have hopen : IsOpen (I : Set 𝔸[F]) := by
    change IsOpen (integralAdelesOutside F S : Set 𝔸[F])
    simp only [integralAdelesOutside, Subring.coe_iInf, Set.iInter_ofPred]
    exact (isOpen_restrictedProduct_forall_mem
      (G := fun v : Primes(F) ↦ v.adicCompletion F)
      (A := fun v ↦ v.adicCompletionIntegers F) (S : Set (Primes(F)))ᶜ
      (fun _ _ ↦ Valued.isOpen_valuationSubring _)).preimage continuous_snd
  let μ := additiveTamagawaMeasure F
  let : μ.IsAddHaarMeasure :=
    (Classical.choose_spec (additiveTamagawaMeasure_existsUnique F).exists).1
  let μI := μ.comap I.subtype
  let : μI.IsAddHaarMeasure :=
    Measure.IsAddHaarMeasure.comap (mH := hAdd) (f := I.subtype.toAddMonoidHom) μ
      hopen.isOpenEmbedding_subtypeVal
  obtain ⟨e, he, he', hcoord⟩ := integralAdelesOutside_factors F S
  let E : I ≃ₜ _ := ⟨e.toEquiv, he, he'⟩
  have hp : (p : I → SAdeleRing F S) = Prod.fst ∘ E := funext fun a ↦ (hcoord a).1.symm
  have hproper : IsProperMap (p : I → SAdeleRing F S) :=
    hp ▸ (isProperMap_fst_of_compactSpace.comp E.isProperMap)
  have hsurj : Surjective p := hp ▸ Prod.fst_surjective.comp E.surjective
  refine ⟨μI.map p, Measure.isAddHaarMeasure_map μI p.toAddMonoidHom hproper.continuous hsurj
    (isProperMap_iff_tendsto_cocompact.mp hproper).2, ?_⟩
  intro W hW
  rw [Measure.map_apply hproper.continuous.measurable hW]
  change (μ.comap (Subtype.val : I → 𝔸[F])) (p ⁻¹' W) = _
  have hi : MeasurableEmbedding (Subtype.val : I → 𝔸[F]) :=
    hopen.isOpenEmbedding_subtypeVal.measurableEmbedding
  rw [hi.comap_apply]
  congr 1
  ext a
  exact ⟨fun ⟨x, hx, hxa⟩ ↦ ⟨hxa ▸ x.property, hxa ▸ hx⟩,
    fun ⟨ha, hWa⟩ ↦ ⟨⟨a, ha⟩, hWa, rfl⟩⟩

/-- Paper: Lemma A.3.1.3, p. 556. The global additive measure is the restricted
product of the local measures, expressed on rectangles with integral tails.
Deviation: The infinite places are grouped into a finite product measure. -/
theorem additiveTamagawaMeasure_restrictedProduct
    (B : Set (InfiniteAdeleRing F)) (hB : MeasurableSet B)
    (U : (v : S) → Set (v.val.adicCompletion F)) (hU : ∀ v, MeasurableSet (U v)) :
    additiveTamagawaMeasure F
        {a | a.1 ∈ B ∧ (∀ v : S, a.2 v.val ∈ U v) ∧ a ∈ integralAdelesOutside F S} =
      Measure.pi (infiniteLocalAdditiveTamagawaMeasure F) B *
        (∏ v : S, finiteLocalAdditiveTamagawaMeasure F v.val (U v)) *
          ∏ᶠ v : {v : Primes(F) // v ∉ S}, differentMass(F, v.val) := by
  let (v : Primes(F)) : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
  let (v : Primes(F)) : CompactSpace (v.adicCompletionIntegers F) :=
    compactSpace_adicCompletionIntegers v
  let (v : InfinitePlace F) : SecondCountableTopology v.Completion :=
    (isometry_extensionEmbedding v).isEmbedding.secondCountableTopology
  let (v : InfinitePlace F) : BorelSpace v.Completion := ⟨rfl⟩
  let : BorelSpace (SAdeleRing F S) :=
    inferInstanceAs (BorelSpace (((v : InfinitePlace F) → v.Completion) ×
      ((v : S) → v.val.adicCompletion F)))
  let : SecondCountableTopology (SAdeleRing F S) :=
    inferInstanceAs (SecondCountableTopology (((v : InfinitePlace F) → v.Completion) ×
      ((v : S) → v.val.adicCompletion F)))
  let : LocallyCompactSpace (SAdeleRing F S) :=
    inferInstanceAs (LocallyCompactSpace (InfiniteAdeleRing F × ((v : S) → v.val.adicCompletion F)))
  let μarch := infiniteLocalAdditiveTamagawaMeasure F
  let μf (v : S) := finiteLocalAdditiveTamagawaMeasure F v.val
  let (v : InfinitePlace F) : (μarch v).IsAddHaarMeasure :=
    infiniteLocalAdditiveTamagawaMeasure_haar F v
  have hfinite (v : S) : (μf v).IsAddHaarMeasure := by
    let O := (v.val.adicCompletionIntegers F : Set (v.val.adicCompletion F))
    let μ := Measure.addHaar (G := v.val.adicCompletion F)
    have hO : IsOpen O := Valued.isOpen_valuationSubring _
    have hK : IsCompact O := isCompact_iff_compactSpace.mpr inferInstance
    have hpos : μ O ≠ 0 := (hO.measure_pos μ ⟨0, (v.val.adicCompletionIntegers F).zero_mem⟩).ne'
    have htop : μ O ≠ ⊤ := hK.measure_ne_top
    have hnorm : 0 < Ideal.absNorm v.val.asIdeal :=
      Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr v.val.ne_bot)
    change ((differentMass(F, v.val) / μ O) • μ).IsAddHaarMeasure
    rw [div_eq_mul_inv]
    apply Measure.IsAddHaarMeasure.smul
    · exact mul_ne_zero (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)
        (ENNReal.inv_ne_zero.mpr htop)
    · exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr (by positivity)).ne')
        (ENNReal.inv_ne_top.mpr hpos)
  let (v : S) : (μf v).IsAddHaarMeasure := hfinite v
  let μ : Measure (SAdeleRing F S) := (Measure.pi μarch).prod (Measure.pi μf)
  let : BorelSpace ((v : InfinitePlace F) → v.Completion) := inferInstance
  let : BorelSpace ((v : S) → v.val.adicCompletion F) := inferInstance
  let : (Measure.pi μarch).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  let : (Measure.pi μf).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  let : μ.IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  obtain ⟨ν, hν, hrect⟩ := additiveTamagawaMeasure_projected_haar F S
  let : ν.IsAddHaarMeasure := hν
  let c := ν.addHaarScalarFactor μ
  have hscale : ν = c • μ := Measure.isAddLeftInvariant_eq_smul ν μ
  have happly (B' : Set (InfiniteAdeleRing F)) (hB' : MeasurableSet B')
      (U' : (v : S) → Set (v.val.adicCompletion F)) (hU' : ∀ v, MeasurableSet (U' v)) :
      additiveTamagawaMeasure F
          {a | a.1 ∈ B' ∧ (∀ v : S, a.2 v.val ∈ U' v) ∧ a ∈ integralAdelesOutside F S} =
        (c : ℝ≥0∞) * (Measure.pi μarch B' * ∏ v : S, μf v (U' v)) := by
    let W : Set (SAdeleRing F S) := B' ×ˢ Set.univ.pi U'
    have hW : MeasurableSet W := hB'.prod (MeasurableSet.pi (Set.to_countable _) fun v _ ↦ hU' v)
    have hset : {a : 𝔸[F] | a ∈ integralAdelesOutside F S ∧ adeleProjection F S a ∈ W} =
        {a | a.1 ∈ B' ∧ (∀ v : S, a.2 v.val ∈ U' v) ∧ a ∈ integralAdelesOutside F S} := by
      ext a
      change (a ∈ integralAdelesOutside F S ∧ (a.1 ∈ B' ∧ (fun v : S ↦ a.2 v.val) ∈
        Set.univ.pi U')) ↔ _
      simp only [Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_ofPred_eq]
      tauto
    rw [← hset, ← hrect W hW, hscale, smul_apply]
    change (c : ℝ≥0∞) * ((Measure.pi μarch).prod (Measure.pi μf)) (B' ×ˢ Set.univ.pi U') = _
    rw [Measure.prod_prod, Measure.pi_pi]
  let D := infiniteAdeleFundamentalDomain F (RingOfIntegers.basis F)
  let O (v : S) := (v.val.adicCompletionIntegers F : Set (v.val.adicCompletion F))
  let d := ENNReal.ofReal (Real.sqrt (↑(discr F).natAbs : ℝ))
  obtain ⟨hD, hmassD⟩ := infiniteAdeleFundamentalDomain_tamagawaMass F
  have hO (v : S) : MeasurableSet (O v) := (Valued.isOpen_valuationSubring _).measurableSet
  have hdomain : {a : 𝔸[F] | a.1 ∈ D ∧ (∀ v : S, a.2 v.val ∈ O v) ∧
      a ∈ integralAdelesOutside F S} = adeleFundamentalDomain F (RingOfIntegers.basis F) := by
    ext a
    change (_ ∧ (∀ v : S, a.2 v.val ∈ O v) ∧ a ∈ integralAdelesOutside F S) ↔
      (_ ∧ a ∈ integralAdelesOutside F ∅)
    simp only [integralAdelesOutside, Subring.mem_iInf, Finset.notMem_empty, not_false_eq_true,
      true_implies]
    refine and_congr_right fun _ ↦ ⟨fun ⟨hin, hout⟩ v ↦ ?_, fun hall ↦ ⟨fun v ↦ hall v.val,
      fun v _ ↦ hall v⟩⟩
    by_cases hv : v ∈ S
    · exact hin ⟨v, hv⟩
    · exact hout v hv
  have hnormalize := happly D hD O hO
  rw [hdomain, additiveTamagawaMeasure_fundamentalDomain, hmassD] at hnormalize
  simp only [μf, O, finiteLocalAdditiveTamagawaMeasure_integers] at hnormalize
  let tail := ∏ᶠ v : {v : Primes(F) // v ∉ S}, differentMass(F, v.val)
  have hsplit : (∏ v : S, differentMass(F, v.val)) * tail = d⁻¹ := by
    rw [show d⁻¹ = _ from (finiteLocalTamagawaMass_finprod F).symm]
    rw [← Finset.prod_subtype S (fun _ ↦ Iff.rfl) (fun v ↦ differentMass(F, v)),
      ← finprod_mem_coe_finset,
      show tail = ∏ᶠ v ∈ (S : Set (Primes(F)))ᶜ, differentMass(F, v) from
        finprod_set_coe_eq_finprod_mem (f := fun v ↦ differentMass(F, v))
          (S : Set (Primes(F)))ᶜ]
    have hpartition := finprod_mem_inter_mul_sdiff'
      (f := fun v : Primes(F) ↦ differentMass(F, v)) (s := Set.univ) (S : Set (Primes(F)))
      ((finiteLocalTamagawaMass_finite F).subset Set.inter_subset_right)
    rw [Set.univ_inter, ← Set.compl_eq_univ_sdiff, finprod_mem_univ] at hpartition
    exact hpartition
  have hdisc : 0 < (discr F).natAbs := Int.natAbs_pos.mpr (discr_ne_zero F)
  have hcancel : d * d⁻¹ = 1 :=
    ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr (by positivity)).ne' ENNReal.ofReal_ne_top
  have hc : (c : ℝ≥0∞) = tail := calc
    (c : ℝ≥0∞) = (c : ℝ≥0∞) * (d * d⁻¹) := by rw [hcancel, mul_one]
    _ = ((c : ℝ≥0∞) * (d * ∏ v : S, differentMass(F, v.val))) * tail := by
      rw [← hsplit, ← mul_assoc d, ← mul_assoc]
    _ = tail := by rw [← hnormalize, one_mul]
  rw [happly B hB U hU, hc, mul_comm tail]

end

-- TODO(paper-gap): The S-local equality in (A.3.1.3) fails for the quotient-volume-one
-- measure of Definition A.3.1.1. For F = ℚ(i) and S archimedean, the product has
-- quotient mass 2, since the Gaussian integers have Euclidean covolume 1 and ν∞ = 2 dx dy.

section AdeleHaarScaling

open Filter Topology
open scoped IsDedekindDomain.FiniteAdeleRing RestrictedProduct

local notation "AF" => FiniteAdeleRing (𝓞 F) F
local notation "AI" => InfiniteAdeleRing F
local notation:max "𝒪[" v "]" => HeightOneSpectrum.adicCompletionIntegers F v

private local instance (v : InfinitePlace F) : BorelSpace v.Completion := ⟨rfl⟩
private local instance (v : InfinitePlace F) : SecondCountableTopology v.Completion :=
  (isometry_extensionEmbedding v).isEmbedding.secondCountableTopology
private local instance (v : Primes(F)) : CompactSpace (v.adicCompletionIntegers F) :=
  compactSpace_adicCompletionIntegers v
private local instance :
    Fact (∀ v : Primes(F), IsOpen (𝒪[v] : Set (v.adicCompletion F))) :=
  ⟨fun v ↦ Valued.isOpen_valuationSubring (v.adicCompletion F)⟩
private local instance : BorelSpace AI :=
  inferInstanceAs (BorelSpace ((v : InfinitePlace F) → v.Completion))
private local instance : SecondCountableTopology AI :=
  inferInstanceAs (SecondCountableTopology ((v : InfinitePlace F) → v.Completion))
private local instance : T2Space AI :=
  inferInstanceAs (T2Space ((v : InfinitePlace F) → v.Completion))
private local instance : LocallyCompactSpace AF := by
  change LocallyCompactSpace (Πʳ v : Primes(F), [v.adicCompletion F, 𝒪[v]])
  infer_instance
private local instance : T2Space AF := by
  change T2Space (Πʳ v : Primes(F), [v.adicCompletion F, 𝒪[v]])
  infer_instance
private local instance : MeasurableSpace AF := borel _
private local instance : BorelSpace AF := ⟨rfl⟩
private local instance : BorelSpace 𝔸[F] := ⟨rfl⟩
private local instance : LocallyCompactSpace 𝔸[F] :=
  inferInstanceAs (LocallyCompactSpace (InfiniteAdeleRing F × AF))
private local instance : T2Space 𝔸[F] := inferInstanceAs (T2Space (AI × AF))

/-- Principal translates of the precompact adelic fundamental domain give a countable compact cover. -/
private theorem adeleHaar_sigmaCompactSpace : SigmaCompactSpace 𝔸[F] := by
  let : Countable F := Countable.of_moduleFinite (R := ℚ)
  let b := RingOfIntegers.basis F
  let D := adeleFundamentalDomain F b
  let K (q : F) := algebraMap F 𝔸[F] q +ᵥ closure D
  refine SigmaCompactSpace.of_countable (Set.range K) (Set.countable_range K) ?_ ?_
  · rintro _ ⟨q, rfl⟩
    exact IsCompact.vadd _ (adeleFundamentalDomain_precompact F b)
  · rw [Set.sUnion_range]
    exact eq_top_mono (Set.iUnion_mono fun _ ↦ Set.vadd_set_mono (subset_closure (s := D)))
      (adeleFundamentalDomain_cover F b)

omit [NumberField F] in
/-- The archimedean local measure is Haar, by transport from the real or complex line. -/
private theorem infiniteLocalAdditiveTamagawaMeasure_isAddHaar (v : InfinitePlace F) :
    (infiniteLocalAdditiveTamagawaMeasure F v).IsAddHaarMeasure := by
  by_cases h : v.IsReal
  · rw [infiniteLocalAdditiveTamagawaMeasure, dite_eq_left h]
    let e : ℝ ≃ₜ+ v.Completion :=
      { (ringEquivRealOfIsReal h).symm.toAddEquiv,
        (isometryEquivRealOfIsReal h).symm.toHomeomorph with }
    exact e.isAddHaarMeasure_map volume
  · rw [infiniteLocalAdditiveTamagawaMeasure, dite_eq_right h]
    let h' := InfinitePlace.not_isReal_iff_isComplex.mp h
    let e : ℂ ≃ₜ+ v.Completion :=
      { (ringEquivComplexOfIsComplex h').symm.toAddEquiv,
        (isometryEquivComplexOfIsComplex h').symm.toHomeomorph with }
    have : (2 • (volume : Measure ℂ)).IsAddHaarMeasure := by
      have heq : (2 : ℕ) • (volume : Measure ℂ) = (2 : ℝ≥0∞) • volume := by
        rw [two_nsmul, ← one_add_one_eq_two, add_smul, one_smul]
      rw [heq]
      exact Measure.IsAddHaarMeasure.smul volume (by norm_num) (by simp)
    exact e.isAddHaarMeasure_map (2 • volume)

/-- Archimedean multiplication scales the measure of the closed unit polydisc by the product
of the real absolute values and the squares of the complex absolute values. -/
private theorem infiniteAdeleHaar_unitPolydisc (u : AIˣ) :
    let D : Set AI := Set.univ.pi (fun _ ↦ Metric.closedBall 0 1)
    let ν := Measure.pi (infiniteLocalAdditiveTamagawaMeasure F)
    ν ((fun a : AI ↦ u.val * a) '' D) =
      ENNReal.ofReal (∏ w : InfinitePlace F, ‖u.val w‖ ^ w.mult) * ν D := by
  let (v : InfinitePlace F) : (infiniteLocalAdditiveTamagawaMeasure F v).IsAddHaarMeasure :=
    infiniteLocalAdditiveTamagawaMeasure_isAddHaar F v
  dsimp only
  rw [show (fun a : AI ↦ u.val * a) =
    Pi.map (fun v ↦ (u.val v * ·)) from rfl, Set.piMap_image_univ_pi, Measure.pi_pi, Measure.pi_pi]
  have hl (v : InfinitePlace F) :
      (fun x : v.Completion ↦ u.val v * x) '' Metric.closedBall 0 1 =
        Metric.closedBall 0 ‖u.val v‖ := by
    have hne : u.val v ≠ 0 := by
      have hprod : u.val v * u.inv v = 1 := congrFun u.val_inv v
      intro h
      simp [h] at hprod
    change u.val v • Metric.closedBall 0 1 = _
    simpa only [smul_zero, mul_one] using smul_closedBall' hne (0 : v.Completion) 1
  have hlocal (v : InfinitePlace F) (r : ℝ) :
      infiniteLocalAdditiveTamagawaMeasure F v (Metric.closedBall 0 r) =
        ENNReal.ofReal r ^ v.mult *
          infiniteLocalAdditiveTamagawaMeasure F v (Metric.closedBall 0 1) := by
    by_cases h : v.IsReal
    · rw [h.mult_eq_one, pow_one, infiniteLocalAdditiveTamagawaMeasure, dite_eq_left h]
      let e := isometryEquivRealOfIsReal h
      let em := e.toHomeomorph.toMeasurableEquiv
      change Measure.map em.symm volume (Metric.closedBall 0 r) =
        _ * Measure.map em.symm volume (Metric.closedBall 0 1)
      have hpre (s : ℝ) : em.symm ⁻¹' Metric.closedBall 0 s = Metric.closedBall 0 s := by
        rw [← em.image_eq_preimage_symm]
        change e '' Metric.closedBall 0 s = _
        rw [e.image_closedBall]
        exact congrArg (Metric.closedBall · s) ((ringEquivRealOfIsReal h).map_zero)
      rw [em.symm.map_apply, em.symm.map_apply, hpre, hpre, Real.volume_closedBall,
        Real.volume_closedBall, mul_one, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        mul_comm]
    · have hc := InfinitePlace.not_isReal_iff_isComplex.mp h
      rw [hc.mult_eq_two, infiniteLocalAdditiveTamagawaMeasure, dite_eq_right h]
      let e := isometryEquivComplexOfIsComplex hc
      let em := e.toHomeomorph.toMeasurableEquiv
      change Measure.map em.symm (2 • volume) (Metric.closedBall 0 r) =
        _ * Measure.map em.symm (2 • volume) (Metric.closedBall 0 1)
      have hpre (s : ℝ) : em.symm ⁻¹' Metric.closedBall 0 s = Metric.closedBall 0 s := by
        rw [← em.image_eq_preimage_symm]
        change e '' Metric.closedBall 0 s = _
        rw [e.image_closedBall]
        exact congrArg (Metric.closedBall · s) ((ringEquivComplexOfIsComplex hc).map_zero)
      rw [em.symm.map_apply, em.symm.map_apply, hpre, hpre]
      simp only [two_nsmul, add_apply, Complex.volume_closedBall,
        ENNReal.ofReal_one, one_pow, one_mul, mul_add]
  simp_rw [hl, hlocal _ ‖u.val _‖]
  rw [Finset.prod_mul_distrib, ENNReal.ofReal_prod_of_nonneg fun _ _ ↦ pow_nonneg (norm_nonneg _) _]
  simp_rw [ENNReal.ofReal_pow (norm_nonneg _)]

/-- The product of all local integer rings. -/
private abbrev finiteAdeleIntegersProduct := ∀ v : Primes(F), 𝒪[v]

/-- Finite adeles integral at all finite places. -/
private def integralFiniteAdeles : Set AF := {a | ∀ v : Primes(F), a v ∈ 𝒪[v]}

/-- The pointwise inclusion of the product of integer rings into the finite adeles. -/
private def finiteAdeleIntegerEmbedding : finiteAdeleIntegersProduct F →+ AF where
  toFun := RestrictedProduct.structureMap (fun v : Primes(F) ↦ v.adicCompletion F)
    (fun v ↦ (𝒪[v] : Set (v.adicCompletion F))) cofinite
  map_zero' := by ext v; rfl
  map_add' x y := by ext v; rfl

/-- The integral finite adeles form a compact open subgroup. -/
private theorem finiteAdeleIntegerEmbedding_isOpenEmbedding :
    IsOpenEmbedding (finiteAdeleIntegerEmbedding F) :=
  RestrictedProduct.isOpenEmbedding_structureMap
    (fun v : Primes(F) ↦ Valued.isOpen_valuationSubring (v.adicCompletion F))

/-- A unit at a single finite place gives a unit in the restricted product. -/
private def finiteAdeleSingleUnit (v : Primes(F)) : (v.adicCompletion F)ˣ →* AFˣ :=
  Units.map (RestrictedProduct.mulSingleMonoidHom (fun w : Primes(F) ↦ 𝒪[w]) v)

/-- Evaluation at the selected place gives the original unit. -/
private theorem finiteAdeleSingleUnit_val_same (v : Primes(F)) (u : (v.adicCompletion F)ˣ) :
    (finiteAdeleSingleUnit F v u).val v = u.val :=
  RestrictedProduct.mulSingle_eq_same _ _ _

/-- At every other place a unit supported at one place has coordinate one. -/
private theorem finiteAdeleSingleUnit_val_ne {v w : Primes(F)} (h : w ≠ v)
    (u : (v.adicCompletion F)ˣ) :
    (finiteAdeleSingleUnit F v u).val w = 1 :=
  RestrictedProduct.mulSingle_eq_of_ne _ _ h

/-- The integral finite adeles have positive mass because they are open and contain zero. -/
private theorem finiteAdeleInteger_volume_pos :
    0 < (Measure.addHaar (G := AF)) (integralFiniteAdeles F) := by
  let ν : Measure AF := Measure.addHaar
  have hopen : IsOpen (integralFiniteAdeles F) :=
    RestrictedProduct.isOpen_forall_mem
      (fun v : Primes(F) ↦ Valued.isOpen_valuationSubring (v.adicCompletion F))
  exact hopen.measure_pos ν ⟨0, fun v ↦ 𝒪[v].zero_mem⟩

/-- The integral finite adeles are compact as the image of the product of the local integer rings. -/
private theorem finiteAdeleInteger_isCompact : IsCompact (integralFiniteAdeles F) := by
  have hr : Set.range (finiteAdeleIntegerEmbedding F) = integralFiniteAdeles F :=
    RestrictedProduct.range_structureMap _ _
  rw [← hr]
  have (v : Primes(F)) : CompactSpace ↥(𝒪[v] : Set (v.adicCompletion F)) :=
    compactSpace_adicCompletionIntegers v
  exact isCompact_range (finiteAdeleIntegerEmbedding_isOpenEmbedding F).continuous

/-- A finite idele with local absolute value one everywhere preserves the integral open subgroup. -/
private theorem finiteAdeleHaar_char_eq_one (u : AFˣ)
    (hu : ∀ v : Primes(F), Valued.v (u.val v) = 1) :
    distribHaarChar AF u = 1 := by
  let ν : Measure AF := Measure.addHaar
  have hmem (v : Primes(F)) (x : AF) :
      (u.val * x) v ∈ 𝒪[v] ↔ x v ∈ 𝒪[v] := by
    change Valued.v (u.val v * x v) ≤ 1 ↔ Valued.v (x v) ≤ 1
    rw [map_mul, hu, one_mul]
  have heq : u • integralFiniteAdeles F = integralFiniteAdeles F := by
    ext x
    change x ∈ (fun a : AF ↦ u.val * a) '' (integralFiniteAdeles F) ↔ _
    constructor
    · rintro ⟨a, ha, rfl⟩ v
      exact (hmem v a).2 (ha v)
    · intro hx
      refine ⟨u.inv * x, fun v ↦ (hmem v _).1 ?_, ?_⟩
      · rw [← mul_assoc, u.val_inv, one_mul]
        exact hx v
      · change u.val * (u.inv * x) = x
        rw [← mul_assoc, u.val_inv, one_mul]
  apply distribHaarChar_eq_of_measure_smul_eq_mul (μ := ν)
    (finiteAdeleInteger_volume_pos F).ne' (finiteAdeleInteger_isCompact F).measure_ne_top
  rw [heq, ENNReal.coe_one, one_mul]

/-- At one finite place, multiplication by a uniformizer replaces its integer ring by its
maximal ideal. The resulting subgroup has index equal to the residue field cardinality. -/
private theorem finiteAdeleHaar_char_uniformizer (v : Primes(F)) (π : 𝒪[v])
    (hπ : Valued.v.IsUniformizer (π : v.adicCompletion F)) :
    distribHaarChar AF (finiteAdeleSingleUnit F v (Units.mk0 (π : v.adicCompletion F) hπ.ne_zero)) =
      ‖(π : v.adicCompletion F)‖₊ := by
  let u := finiteAdeleSingleUnit F v (Units.mk0 (π : v.adicCompletion F) hπ.ne_zero)
  let e := finiteAdeleIntegerEmbedding F
  let : MeasurableSpace (finiteAdeleIntegersProduct F) := borel _
  let : BorelSpace (finiteAdeleIntegersProduct F) := ⟨rfl⟩
  let ν : Measure AF := Measure.addHaar
  let νO := ν.comap e
  have he := (finiteAdeleIntegerEmbedding_isOpenEmbedding F).measurableEmbedding
  have : νO.IsAddLeftInvariant := ⟨fun x ↦ by
    ext s hs
    have hcont : Continuous (x + ·) := continuous_const.add continuous_id
    rw [Measure.map_apply hcont.measurable hs, he.comap_apply, he.comap_apply]
    have hpre : e '' ((x + ·) ⁻¹' s) = (e x + ·) ⁻¹' (e '' s) := by
      ext a
      constructor
      · rintro ⟨b, hb, rfl⟩
        exact ⟨x + b, hb, map_add e x b⟩
      · rintro ⟨b, hb, h⟩
        refine ⟨b - x, ?_, ?_⟩
        · show x + (b - x) ∈ s
          simpa [add_comm x] using hb
        · rw [map_sub, h]
          exact add_sub_cancel_left (e x) a
    have hm : Measurable (e x + ·) := (continuous_const.add continuous_id).measurable
    rw [hpre, ← Measure.map_apply hm (he.measurableSet_image.mpr hs), map_add_left_eq_self]⟩
  let f : finiteAdeleIntegersProduct F →+ IsLocalRing.ResidueField (𝒪[v]) :=
    (IsLocalRing.residue 𝒪[v]).toAddMonoidHom.comp
      (Pi.evalAddMonoidHom (fun w : Primes(F) ↦ 𝒪[w]) v)
  have hf : Surjective f := by
    intro a
    obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective a
    refine ⟨Function.update (0 : finiteAdeleIntegersProduct F) v b, ?_⟩
    change IsLocalRing.residue (𝒪[v]) (Function.update (0 : finiteAdeleIntegersProduct F) v b v) = _
    rw [Function.update_self]
  have hindex : f.ker.index = v.asIdeal.absNorm := by
    rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr hf, AddSubgroup.card_top,
      card_residueField_adicCompletion]
  have hindexpos := zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v)
  have : f.ker.FiniteIndex := ⟨by simp [hindex, hindexpos.ne']⟩
  have hk (a : finiteAdeleIntegersProduct F) : a ∈ f.ker ↔ ∃ b : 𝒪[v], π * b = a v := by
    change IsLocalRing.residue (𝒪[v]) (a v) = 0 ↔ _
    rw [IsLocalRing.residue_eq_zero_iff]
    have hg : IsLocalRing.maximalIdeal (𝒪[v]) = Ideal.span {π} := hπ.is_generator
    rw [hg, Ideal.mem_span_singleton]
    exact dvd_def.trans (exists_congr fun b ↦ eq_comm)
  have hmeas : MeasurableSet (f.ker : Set (finiteAdeleIntegersProduct F)) := by
    have hcont : Continuous (fun a : finiteAdeleIntegersProduct F ↦ (a v : v.adicCompletion F)) :=
      continuous_subtype_val.comp (continuous_apply v)
    let val : Valuation (v.adicCompletion F) _ := Valued.v
    have hop := (Valued.isOpen_ball (v.adicCompletion F) 1).preimage hcont
    have hs : (f.ker : Set (finiteAdeleIntegersProduct F)) =
        {a | val.restrict (a v : v.adicCompletion F) < 1} := by
      ext a
      change IsLocalRing.residue (𝒪[v]) (a v) = 0 ↔ _
      rw [IsLocalRing.residue_eq_zero_iff]
      have hlt : a v ∈ IsLocalRing.maximalIdeal (𝒪[v]) ↔ val (a v : v.adicCompletion F) < 1 :=
        Valuation.mem_maximalIdeal_iff _ val
      rw [hlt]
      change val (a v : v.adicCompletion F) < 1 ↔ val.restrict _ < 1
      rw [Valuation.restrict_lt_iff_lt_embedding, map_one]
    rw [hs]
    exact hop.measurableSet
  have himage : e '' (f.ker : Set (finiteAdeleIntegersProduct F)) = u • integralFiniteAdeles F := by
    ext a
    change a ∈ e '' (f.ker : Set (finiteAdeleIntegersProduct F)) ↔
      a ∈ (fun x : AF ↦ u.val * x) '' integralFiniteAdeles F
    constructor
    · rintro ⟨b, hb, rfl⟩
      obtain ⟨c, hc⟩ := (hk b).1 hb
      let d := Function.update b v c
      refine ⟨e d, fun w ↦ (d w).property, ?_⟩
      apply Subtype.ext
      funext w
      change u.val w * (d w : w.adicCompletion F) = b w
      by_cases h : w = v
      · subst w
        rw [show u.val v = (π : v.adicCompletion F) from finiteAdeleSingleUnit_val_same F v _]
        have hd : d v = c := Function.update_self _ _ _
        rw [hd]
        exact congrArg Subtype.val hc
      · rw [show u.val w = 1 from finiteAdeleSingleUnit_val_ne F h _, one_mul,
          show d w = b w from Function.update_of_ne h _ _]
    · rintro ⟨a, ha, rfl⟩
      let b (w : Primes(F)) : 𝒪[w] := ⟨a w, ha w⟩
      let d := Function.update b v (π * b v)
      have hd : d v = π * b v := Function.update_self _ _ _
      refine ⟨d, (hk d).2 ⟨b v, hd.symm⟩, ?_⟩
      apply Subtype.ext
      funext w
      change (d w : w.adicCompletion F) = u.val w * a w
      by_cases h : w = v
      · subst w
        rw [show u.val v = (π : v.adicCompletion F) from finiteAdeleSingleUnit_val_same F v _,
          hd]
        rfl
      · rw [show u.val w = 1 from finiteAdeleSingleUnit_val_ne F h _, one_mul,
          show d w = b w from Function.update_of_ne h _ _]
  have hmass := f.ker.index_mul_measure hmeas νO
  change (f.ker.index : ℝ≥0∞) * ν.comap e f.ker = ν.comap e univ at hmass
  rw [hindex, he.comap_apply, he.comap_apply, himage, Set.image_univ,
    show range e = integralFiniteAdeles F from RestrictedProduct.range_structureMap _ _] at hmass
  apply distribHaarChar_eq_of_measure_smul_eq_mul (μ := ν)
    (finiteAdeleInteger_volume_pos F).ne' (finiteAdeleInteger_isCompact F).measure_ne_top
  change ν (u • integralFiniteAdeles F) =
    (↑‖(π : v.adicCompletion F)‖₊ : ℝ≥0∞) * ν (integralFiniteAdeles F)
  rw [← hmass, ← ENNReal.ofReal_coe_nnreal, coe_nnNorm, norm_uniformizer_adicCompletion v _ hπ,
    ENNReal.ofReal_inv_of_pos (by exact_mod_cast hindexpos), ENNReal.ofReal_natCast,
    ← mul_assoc, ENNReal.inv_mul_cancel (by exact_mod_cast hindexpos.ne') (ENNReal.natCast_ne_top _),
    one_mul]

/-- On units supported at one finite place, the Haar character is the normalized local
absolute value. A uniformizer and the local integral units generate the local unit group. -/
private theorem finiteAdeleHaar_char_single (v : Primes(F)) (x : (v.adicCompletion F)ˣ) :
    distribHaarChar AF (finiteAdeleSingleUnit F v x) = ‖x.val‖₊ := by
  let val : Valuation (v.adicCompletion F) _ := Valued.v
  obtain ⟨π, hπ⟩ := val.exists_isUniformizer_of_isCyclic_of_nontrivial
  let p : (v.adicCompletion F)ˣ := Units.mk0 π.val hπ.ne_zero
  let ι := Units.map 𝒪[v].subtype.toMonoidHom
  obtain ⟨e, hep, heι⟩ := finitePlace_unitDecomposition v p
    (norm_uniformizer_adicCompletion v _ hπ)
  let k := (e x).1.toAdd
  let t := (e x).2
  have hx : x = p ^ k * ι t := by
    apply e.injective
    rw [map_mul, map_zpow, hep, heι]
    apply Prod.ext
    · change (e x).1 = Multiplicative.ofAdd (k * 1) * 1
      simp [k]
    · change t = (1 : (𝒪[v])ˣ) ^ k * t
      simp
  have hval : Valued.v ((ι t).val) = 1 :=
    (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one (a := ι t)).mp
      ⟨t.val.prop, t.inv.prop⟩
  have hn : ‖(ι t).val‖₊ = 1 := by
    apply NNReal.eq
    exact Valued.toNormedField.norm_eq_one_iff.mpr hval
  have hunit : distribHaarChar AF (finiteAdeleSingleUnit F v (ι t)) = 1 := by
    apply finiteAdeleHaar_char_eq_one
    intro w
    by_cases h : w = v
    · subst w
      exact (congrArg Valued.v (finiteAdeleSingleUnit_val_same F v (ι t))).trans hval
    · rw [finiteAdeleSingleUnit_val_ne F h, map_one]
  conv_lhs => rw [hx, map_mul, map_mul, map_zpow, map_zpow,
    finiteAdeleHaar_char_uniformizer F v π hπ, hunit, mul_one]
  conv_rhs => rw [hx, Units.val_mul, nnNorm_mul, Units.val_zpow_eq_zpow_val,
    nnNorm_zpow, hn, mul_one]
  rfl

/-- The compact open subgroup of integral finite adeles acquires the product of the normalized
finite-place norms as its volume ratio under multiplication by a finite idele. -/
private theorem finiteAdeleHaar_integralImage (u : AFˣ) :
    let D := integralFiniteAdeles F
    let ν : Measure AF := Measure.addHaar
    ν ((fun a : AF ↦ u.val * a) '' D) =
      ENNReal.ofReal (∏ᶠ v : Primes(F), ‖u.val v‖) * ν D := by
  dsimp only
  let χ : AFˣ →* ℝ≥0 := distribHaarChar AF
  let hs := FiniteAdeleRing.hasFiniteMulSupport_norm u
  let s := hs.toFinset
  let ev (v : Primes(F)) : AFˣ →* (v.adicCompletion F)ˣ :=
    Units.map (RestrictedProduct.evalMonoidHom (fun w : Primes(F) ↦ w.adicCompletion F) v)
  let p : AFˣ := ∏ v ∈ s, finiteAdeleSingleUnit F v (ev v u)
  have hp (w : Primes(F)) :
      p.val w = if w ∈ s then u.val w else 1 := by
    let e := (Units.coeHom _).comp (ev w)
    change e p = _
    rw [map_prod]
    by_cases hw : w ∈ s
    · rw [ite_eq_left hw, Finset.prod_eq_single_of_mem w hw]
      · exact finiteAdeleSingleUnit_val_same F w _
      · intro v _ hv
        exact finiteAdeleSingleUnit_val_ne F (Ne.symm hv) _
    · rw [ite_eq_right hw, Finset.prod_eq_one]
      intro v hv
      exact finiteAdeleSingleUnit_val_ne F (v := v) (w := w) (fun h ↦ hw (h.symm ▸ hv)) _
  have hunit : χ (u / p) = 1 := by
    apply finiteAdeleHaar_char_eq_one
    intro v
    change Valued.v ((ev v (u / p)).val) = 1
    rw [map_div, Units.val_div_eq_div_val]
    change Valued.v (u.val v / p.val v) = 1
    rw [hp]
    split_ifs with hv
    · have hu : u.val v ≠ 0 := (ev v u).ne_zero
      rw [div_self hu, map_one]
    · rw [div_one]
      apply Valued.toNormedField.norm_eq_one_iff.mp
      exact not_not.mp (fun h ↦ hv (hs.mem_toFinset.mpr h))
  have hχ : χ u = ∏ v ∈ s, ‖u.val v‖₊ := by
    calc
      χ u = χ ((u / p) * p) := congrArg χ (by simp)
      _ = χ p := by rw [map_mul, hunit, one_mul]
      _ = _ := ?_
    change χ (∏ v ∈ s, finiteAdeleSingleUnit F v (ev v u)) = _
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro v _
    exact finiteAdeleHaar_char_single F v (ev v u)
  change Measure.addHaar (u • integralFiniteAdeles F) =
    _ * Measure.addHaar (integralFiniteAdeles F)
  rw [← distribHaarChar_mul, hχ,
    finprod_eq_prod_of_mulSupport_subset _ (s := s) (fun _ h ↦ hs.mem_toFinset.mpr h),
    ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦ norm_nonneg _)]
  push_cast
  simp only [← coe_nnNorm, ENNReal.ofReal_coe_nnreal]

/-- Paper: Lemma A.3.1.4, p. 556. Multiplication of a Borel set by an idele
scales any additive Haar measure by the idelic norm. -/
theorem adeleHaar_mul_image (μ : Measure 𝔸[F]) [μ.IsAddHaarMeasure]
    (g : 𝕀[F]) (B : Set 𝔸[F]) (hB : MeasurableSet B) :
    μ ((fun a : 𝔸[F] ↦ g.val * a) '' B) = (↑(ideleNorm F g).val : ℝ≥0∞) * μ B := by
  let : SigmaCompactSpace 𝔸[F] := adeleHaar_sigmaCompactSpace F
  let : SigmaCompactSpace (AI × AF) := ‹SigmaCompactSpace 𝔸[F]›
  let : SigmaCompactSpace AF := by
    have h : IsSigmaCompact (Set.range (Prod.snd : AI × AF → AF)) :=
      isSigmaCompact_range continuous_snd
    have hsurj : Surjective (Prod.snd : AI × AF → AF) := Prod.snd_surjective
    exact ⟨hsurj.range_eq ▸ h⟩
  let νinf : Measure AI := Measure.pi (infiniteLocalAdditiveTamagawaMeasure F)
  let νf : Measure AF := Measure.addHaar
  let (v : InfinitePlace F) : (infiniteLocalAdditiveTamagawaMeasure F v).IsAddHaarMeasure :=
    infiniteLocalAdditiveTamagawaMeasure_isAddHaar F v
  let : νinf.IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  -- Compute the Haar character using the product of Haar measures on the two factors.
  let ν := νinf.prod νf
  have : ν.IsAddHaarMeasure :=
    { toIsOpenPosMeasure := Measure.prod.instIsOpenPosMeasure
      toIsFiniteMeasureOnCompacts := Measure.prod.instIsFiniteMeasureOnCompacts _ _
      map_add_left_eq_self := fun a ↦ by
        change Measure.map (Prod.map (a.1 + ·) (a.2 + ·)) (νinf.prod νf) = _
        have hai : Measurable (a.1 + ·) := (continuous_const.add continuous_id).measurable
        have haf : Measurable (a.2 + ·) := (continuous_const.add continuous_id).measurable
        rw [← Measure.map_prod_map _ _ hai haf,
          map_add_left_eq_self, map_add_left_eq_self] }
  have hνprod (U : Set AI) (V : Set AF) : ν (U ×ˢ V) = νinf U * νf V := Measure.prod_prod U V
  let U : Set AI := univ.pi (fun _ ↦ Metric.closedBall 0 1)
  let V := integralFiniteAdeles F
  have hucompact : IsCompact U := by
    apply isCompact_univ_pi
    intro v
    by_cases h : v.IsReal
    · let e := isometryEquivRealOfIsReal h
      apply e.toHomeomorph.isEmbedding.isCompact_iff.mpr
      rw [show ⇑e.toHomeomorph = ⇑e from rfl, e.image_closedBall]
      exact isCompact_closedBall _ _
    · let e := isometryEquivComplexOfIsComplex (InfinitePlace.not_isReal_iff_isComplex.mp h)
      apply e.toHomeomorph.isEmbedding.isCompact_iff.mpr
      rw [show ⇑e.toHomeomorph = ⇑e from rfl, e.image_closedBall]
      exact isCompact_closedBall _ _
  have hupos : 0 < νinf U := by
    let W : Set AI := univ.pi (fun _ ↦ Metric.ball 0 1)
    have hWopen : IsOpen W := isOpen_set_pi finite_univ fun _ _ ↦ Metric.isOpen_ball
    have hWne : W.Nonempty := ⟨0, by
      intro v _
      change (0 : v.Completion) ∈ Metric.ball 0 1
      exact Metric.mem_ball_self (by norm_num)⟩
    exact (hWopen.measure_pos νinf hWne).trans_le
      (measure_mono (Set.pi_mono fun _ _ ↦ Metric.ball_subset_closedBall))
  have hpos : ν (U ×ˢ V) ≠ 0 := by
    rw [hνprod]
    exact mul_ne_zero hupos.ne' (finiteAdeleInteger_volume_pos F).ne'
  have htop : ν (U ×ˢ V) ≠ ∞ := (hucompact.prod (finiteAdeleInteger_isCompact F)).measure_ne_top
  let ui : AIˣ := (MulEquiv.prodUnits g).1
  let uf : AFˣ := (MulEquiv.prodUnits g).2
  let g' : (AI × AF)ˣ := g
  have himage :
      g' • (U ×ˢ V) =
        ((fun x : AI ↦ ui.val * x) '' U) ×ˢ ((fun x : AF ↦ uf.val * x) '' V) := by
    exact Set.prodMap_image_prod _ _ _ _
  have hscale : ν (g' • (U ×ˢ V)) = (↑(ideleNorm F g).val : ℝ≥0∞) * ν (U ×ˢ V) := by
    rw [himage, hνprod, hνprod]
    change νinf ((fun a : AI ↦ ui.val * a) '' U) * νf ((fun a : AF ↦ uf.val * a) '' V) = _
    rw [infiniteAdeleHaar_unitPolydisc F ui, finiteAdeleHaar_integralImage F uf]
    rw [← ENNReal.ofReal_coe_nnreal, ((ideleNorm_spec F).1 g).2,
      ENNReal.ofReal_mul (Finset.prod_nonneg fun _ _ ↦ pow_nonneg (norm_nonneg _) _)]
    change (ENNReal.ofReal (∏ v : InfinitePlace F, ‖g.val.1 v‖ ^ v.mult) * νinf U) *
      (ENNReal.ofReal (∏ᶠ v : Primes(F), ‖g.val.2 v‖) * νf V) = _
    ac_rfl
  have : ν.Regular := addHaar_regular_of_sigmaCompactSpace ν
  have : μ.Regular := addHaar_regular_of_sigmaCompactSpace μ
  have hchar : distribHaarChar 𝔸[F] g = (ideleNorm F g).val :=
    show distribHaarChar (AI × AF) g' = _ from
      distribHaarChar_eq_of_measure_smul_eq_mul hpos htop hscale
  have hmeasure : DomMulAct.mk g • μ = (ideleNorm F g).val • μ := by
    rw [Measure.isAddLeftInvariant_eq_smul_of_regular (DomMulAct.mk g • μ) μ,
      addHaarScalarFactor_smul_eq_distribHaarChar, hchar]
  have hmass := congrArg (fun m : Measure 𝔸[F] ↦ m B) hmeasure
  have hinv : Measurable (fun a : 𝔸[F] ↦ g⁻¹ • a) := measurable_const_smul g⁻¹
  change μ.map (g⁻¹ • ·) B = _ at hmass
  rw [Measure.map_apply hinv hB, Set.preimage_smul_inv] at hmass
  exact hmass

end AdeleHaarScaling


section SelfDuality

variable {R : Type*} [CommRing R] [TopologicalSpace R] [MeasurableSpace R]

local instance : MeasurableSpace (PontryaginDual (Multiplicative R)) := borel _

/-- Paper: §A.3.1.1, p. 557. After identifying a ring's additive group with its dual
by the pairing `(x,y) ↦ ψ (x*y)`, the Fourier transform uses the conjugate character. -/
def tamagawaFourier (μ : Measure R) (ψ : R → Circle) (f : R → ℂ) (y : R) : ℂ :=
  ∫ x, f x * star (ψ (x * y) : ℂ) ∂μ

/-- Paper: §A.3.1.1, p. 557. Under the character pairing, the Fourier integral is
the transform of §D.1.1 evaluated at the character attached to the frequency. -/
theorem tamagawaFourier_eq_lcaFourier (μ : Measure R) (ψ : R → Circle) (f : R → ℂ)
    (y : R) (χ : PontryaginDual (Multiplicative R))
    (hχ : ∀ x : R, χ (Multiplicative.ofAdd x) = ψ (x * y)) :
    tamagawaFourier μ ψ f y = lcaFourier (G := Multiplicative R) μ
      (fun x ↦ f x.toAdd) χ := by
  unfold tamagawaFourier lcaFourier
  congr 1
  funext x
  rw [← hχ]
  rfl

/-- Paper: §A.3.1.1, p. 557. A measure is self-dual when the pairing identifies the
additive group with its Pontryagin dual and transports the measure to its Plancherel measure. -/
def IsTamagawaSelfDual (μ : Measure R) (ψ : R → Circle) : Prop :=
  ∃ e : Multiplicative R ≃ₜ* PontryaginDual (Multiplicative R),
    (∀ x y : R, e (Multiplicative.ofAdd x) (Multiplicative.ofAdd y) = ψ (x * y)) ∧
      IsLCAPlancherelMeasure (G := Multiplicative R) μ
        (Measure.map e (show Measure (Multiplicative R) from μ))

end SelfDuality

open scoped FourierTransform in
/-- Paper: Example A.3.1.5, p. 557. Lebesgue measure is self-dual for the real
character with phase `2πx`. -/
theorem realTamagawaMeasure_selfDual :
    IsTamagawaSelfDual (volume : Measure ℝ) (fun x ↦ Circle.exp (2 * Real.pi * x)) := by
  obtain ⟨e, he⟩ := exists_realPontryaginDualEquiv
  refine ⟨e, he, ?_⟩
  let μ : Measure (Multiplicative ℝ) := volume (α := ℝ)
  let : MeasurableSpace (PontryaginDual (Multiplicative ℝ)) := borel _
  let : BorelSpace (PontryaginDual (Multiplicative ℝ)) := ⟨rfl⟩
  let hvol : (volume : Measure ℝ).IsAddHaarMeasure := inferInstance
  let : μ.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := hvol.toIsFiniteMeasureOnCompacts
      toIsOpenPosMeasure := hvol.toIsOpenPosMeasure
      map_mul_left_eq_self := fun x ↦ hvol.map_add_left_eq_self x.toAdd }
  let : μ.Regular := inferInstanceAs (volume : Measure ℝ).Regular
  refine ⟨e.isHaarMeasure_map μ, Measure.Regular.map e.toHomeomorph, ?_⟩
  intro f hf₁ hf₂
  let g : ℝ → ℂ := fun x ↦ f (Multiplicative.ofAdd x)
  have hFourier : lcaFourier μ f ∘ e = 𝓕 g := by
    funext y
    change lcaFourier μ f (e y) = 𝓕 g y.toAdd
    rw [lcaFourier, Real.fourier_eq]
    change (∫ x : ℝ, g x * star (e y (Multiplicative.ofAdd x) : ℂ)) =
      ∫ x : ℝ, Real.fourierChar (-inner ℝ x y.toAdd) • g x
    congr 1
    funext x
    have hPair : e y (Multiplicative.ofAdd x) = Real.fourierChar (x * y.toAdd) := by
      change e (Multiplicative.ofAdd y.toAdd) (Multiplicative.ofAdd x) = _
      rw [he, Real.fourierChar_apply', mul_comm x y.toAdd]
    rw [hPair, Circle.star_addChar, Real.inner_apply, Circle.smul_def, smul_eq_mul, mul_comm]
  have h := memLp_two_fourier_and_eLpNorm_eq (f := g) hf₁ hf₂
  have hEmb := e.toHomeomorph.measurableEmbedding
  refine ⟨hEmb.memLp_map_measure_iff.mpr (hFourier ▸ h.1), ?_⟩
  calc
    _ = eLpNorm (lcaFourier μ f ∘ e) 2 μ := hEmb.eLpNorm_map_measure
    _ = eLpNorm (𝓕 g) 2 volume :=
      congrArg (fun k : Multiplicative ℝ → ℂ ↦ eLpNorm k 2 μ) hFourier
    _ = _ := h.2

/-- Paper: Example A.3.1.5, p. 557. The complex Tamagawa pairing identifies the
additive complex plane with its Pontryagin dual. -/
private theorem exists_complexTamagawaDualEquiv :
    ∃ e : Multiplicative ℂ ≃ₜ* PontryaginDual (Multiplicative ℂ),
      ∀ x y : ℂ, e (Multiplicative.ofAdd x) (Multiplicative.ofAdd y) =
        Circle.exp (4 * Real.pi * (x * y).re) := by
  let G := Multiplicative ℂ
  let phase : ℂ → Circle := fun z ↦ Circle.exp (4 * Real.pi * z.re)
  have hzero : phase 0 = 1 := by simp [phase]
  have hadd (x y : ℂ) : phase (x + y) = phase x * phase y := by
    simp only [phase, Complex.add_re, mul_add, Circle.exp_add]
  have hcont : Continuous phase := Circle.exp.continuous.comp (by fun_prop)
  let pairing : G →* PontryaginDual G :=
    { toFun := fun x ↦
        { toFun := fun y ↦ phase (x.toAdd * y.toAdd)
          map_one' := by change phase (x.toAdd * 0) = 1; rw [mul_zero, hzero]
          map_mul' := fun y z ↦ by
            change phase (x.toAdd * (y.toAdd + z.toAdd)) = _
            rw [mul_add, hadd]
          continuous_toFun := hcont.comp (continuous_const.mul continuous_id) }
      map_one' := PontryaginDual.ext fun y ↦ by
        change phase (0 * y.toAdd) = 1
        rw [zero_mul, hzero]
      map_mul' := fun x y ↦ PontryaginDual.ext fun z ↦ by
        change phase ((x.toAdd + y.toAdd) * z.toAdd) =
          phase (x.toAdd * z.toAdd) * phase (y.toAdd * z.toAdd)
        rw [add_mul, hadd] }
  have hpcont : Continuous pairing :=
    ContinuousMonoidHom.continuous_of_continuous_uncurry
      (show G → (G →ₜ* Circle) from pairing)
      (hcont.comp (continuous_fst.mul continuous_snd))
  obtain ⟨eR, heR⟩ := exists_realPontryaginDualEquiv
  let axis (u : ℂ) : Multiplicative ℝ →ₜ* G :=
    let l := (1 : ℝ →L[ℝ] ℝ).smulRight u
    ⟨l.toLinearMap.toAddMonoidHom.toMultiplicative, l.continuous⟩
  -- Restrict a character to each coordinate axis to use real Pontryagin duality.
  have haxis (u : ℂ) (x : G) :
      PontryaginDual.map (axis u) (pairing x) =
        eR (Multiplicative.ofAdd (2 * (x.toAdd * u).re)) := by
    apply PontryaginDual.ext
    intro t
    change phase (x.toAdd * (t.toAdd • u)) =
      eR (Multiplicative.ofAdd (2 * (x.toAdd * u).re)) (Multiplicative.ofAdd t.toAdd)
    rw [heR _ t.toAdd]
    apply congrArg Circle.exp
    rw [mul_smul_comm, Complex.smul_re, smul_eq_mul]
    ring
  have hreal (x : G) :
      PontryaginDual.map (axis 1) (pairing x) = eR (Multiplicative.ofAdd (2 * x.toAdd.re)) := by
    simpa only [mul_one] using haxis 1 x
  have himag (x : G) :
      PontryaginDual.map (axis Complex.I) (pairing x) =
        eR (Multiplicative.ofAdd (-(2 * x.toAdd.im))) := by
    simpa only [Complex.mul_I_re, mul_neg] using haxis Complex.I x
  have hinj : Injective pairing := by
    intro x y hxy
    have hre := eR.injective <| (hreal x).symm.trans <|
      (congrArg (PontryaginDual.map (axis 1)) hxy).trans (hreal y)
    have him := eR.injective <| (himag x).symm.trans <|
      (congrArg (PontryaginDual.map (axis Complex.I)) hxy).trans (himag y)
    change 2 * x.toAdd.re = 2 * y.toAdd.re at hre
    change -(2 * x.toAdd.im) = -(2 * y.toAdd.im) at him
    change x.toAdd = y.toAdd
    exact Complex.ext (by linarith) (by linarith)
  have hsurj : Surjective pairing := by
    intro χ
    let a := (eR.symm (PontryaginDual.map (axis 1) χ)).toAdd
    let b := (eR.symm (PontryaginDual.map (axis Complex.I) χ)).toAdd
    let x : G := Multiplicative.ofAdd (⟨a / 2, -(b / 2)⟩ : ℂ)
    have hre : PontryaginDual.map (axis 1) (pairing x) = PontryaginDual.map (axis 1) χ := by
      rw [hreal, show 2 * x.toAdd.re = a by change 2 * (a / 2) = a; ring]
      exact eR.apply_symm_apply _
    have him : PontryaginDual.map (axis Complex.I) (pairing x) =
        PontryaginDual.map (axis Complex.I) χ := by
      rw [himag, show -(2 * x.toAdd.im) = b by change -(2 * -(b / 2)) = b; ring]
      exact eR.apply_symm_apply _
    refine ⟨x, PontryaginDual.ext fun y ↦ ?_⟩
    have hy : y = axis 1 (Multiplicative.ofAdd y.toAdd.re) *
        axis Complex.I (Multiplicative.ofAdd y.toAdd.im) := by
      change y.toAdd = y.toAdd.re • (1 : ℂ) + y.toAdd.im • Complex.I
      apply Complex.ext <;> simp
    rw [hy, map_mul, map_mul]
    exact congrArg₂ (· * ·) (DFunLike.congr_fun hre _) (DFunLike.congr_fun him _)
  let equiv := MulEquiv.ofBijective pairing ⟨hinj, hsurj⟩
  exact ⟨{ equiv with
    continuous_toFun := hpcont
    continuous_invFun := (Equiv.continuous_symm_iff equiv.toEquiv).mpr
      (pairing.isOpenMap_of_sigmaCompact hsurj hpcont) }, fun _ _ ↦ rfl⟩

open scoped FourierTransform in
/-- Paper: Example A.3.1.5, p. 557. Twice plane Lebesgue measure is self-dual
for the complex character with phase `4π Re(z)`. -/
theorem complexTamagawaMeasure_selfDual :
    IsTamagawaSelfDual (2 • (volume : Measure ℂ)) (fun z ↦ Circle.exp (4 * Real.pi * z.re)) := by
  rw [← Nat.cast_smul_eq_nsmul ℝ≥0∞]
  norm_num only [Nat.cast_ofNat]
  obtain ⟨e, he⟩ := exists_complexTamagawaDualEquiv
  refine ⟨e, he, ?_⟩
  let μ : Measure (Multiplicative ℂ) := (2 : ℝ≥0∞) • (volume : Measure ℂ)
  let : MeasurableSpace (PontryaginDual (Multiplicative ℂ)) := borel _
  let : BorelSpace (PontryaginDual (Multiplicative ℂ)) := ⟨rfl⟩
  have hvol : ((2 : ℝ≥0∞) • (volume : Measure ℂ)).IsAddHaarMeasure :=
    Measure.IsAddHaarMeasure.smul _ (by norm_num) (by norm_num)
  let : μ.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := hvol.toIsFiniteMeasureOnCompacts
      toIsOpenPosMeasure := hvol.toIsOpenPosMeasure
      map_mul_left_eq_self := fun x ↦ hvol.map_add_left_eq_self x.toAdd }
  let : μ.Regular := Measure.Regular.smul (μ := (volume : Measure ℂ)) (by norm_num)
  change IsLCAPlancherelMeasure (G := Multiplicative ℂ) μ (Measure.map e μ)
  refine ⟨e.isHaarMeasure_map μ, Measure.Regular.map e.toHomeomorph, ?_⟩
  intro f hf₁ hf₂
  let g : ℂ → ℂ := fun x ↦ f (Multiplicative.ofAdd x)
  -- The trace pairing is the Euclidean pairing with the frequency doubled and conjugated.
  let T : ℂ ≃ₜ ℂ :=
    (Units.mk0 (2 : ℝ) two_ne_zero • Complex.conjCLE).toHomeomorph
  have hT (y : ℂ) : T y = (2 : ℝ) • star y := rfl
  have hmap : Measure.map T (volume : Measure ℂ) = (4 : ℝ≥0∞)⁻¹ • volume := by
    change Measure.map ((fun z : ℂ ↦ (2 : ℝ) • z) ∘ Complex.conjLIE) volume = _
    rw [← Measure.map_map (by fun_prop) Complex.conjLIE.measurePreserving.measurable,
      Complex.conjLIE.measurePreserving.map_eq, Measure.map_addHaar_smul _ two_ne_zero,
      Complex.finrank_real_complex]
    rw [show |((2 : ℝ) ^ (2 : ℕ))⁻¹| = (4 : ℝ)⁻¹ by norm_num,
      ENNReal.ofReal_inv_of_pos (by norm_num)]
    norm_num
  have hFourier : lcaFourier μ f ∘ e = (2 : ℝ) • ((𝓕 g) ∘ T) := by
    funext y
    change lcaFourier μ f (e y) = (2 : ℝ) • 𝓕 g (T y.toAdd)
    rw [lcaFourier, Real.fourier_eq]
    change (∫ x : ℂ, g x * star (e y (Multiplicative.ofAdd x) : ℂ)
      ∂((2 : ℝ≥0∞) • (volume : Measure ℂ))) = _
    rw [integral_smul_measure]
    norm_num only [ENNReal.toReal_ofNat]
    congr 1
    apply integral_congr_ae
    filter_upwards with x
    have hPair : e y (Multiplicative.ofAdd x) = Real.fourierChar (inner ℝ x (T y.toAdd)) := by
      change e (Multiplicative.ofAdd y.toAdd) (Multiplicative.ofAdd x) = _
      rw [he, Real.fourierChar_apply', hT, real_inner_smul_right]
      have hInner : inner ℝ x (star y.toAdd) = (y.toAdd * x).re := by
        change (star y.toAdd * star x).re = _
        rw [← star_mul, mul_comm x y.toAdd]
        exact Complex.conj_re _
      rw [hInner]
      apply congrArg Circle.exp
      ring
    rw [hPair, Circle.star_addChar, Circle.smul_def, smul_eq_mul, mul_comm]
  have hle : (volume : Measure ℂ) ≤ (2 : ℝ≥0∞) • volume := by
    rw [two_smul]
    exact Measure.le_add_right le_rfl
  have h := memLp_two_fourier_and_eLpNorm_eq (f := g) (Integrable.mono_measure hf₁ hle)
    (MemLp.mono_measure hle hf₂)
  have hTEmb := T.measurableEmbedding
  have hLp : MemLp ((2 : ℝ) • ((𝓕 g) ∘ T)) 2 (volume : Measure ℂ) := by
    apply MemLp.const_smul
    apply hTEmb.memLp_map_measure_iff.mp
    rw [hmap]
    exact h.1.smul_measure (by norm_num)
  -- The Jacobian contributes a factor of one half to the L² norm.
  have hNorm : eLpNorm ((2 : ℝ) • ((𝓕 g) ∘ T)) 2 (volume : Measure ℂ) =
      eLpNorm g 2 volume := by
    rw [eLpNorm_const_smul, ← hTEmb.eLpNorm_map_measure, hmap,
      eLpNorm_smul_measure_of_ne_zero (by norm_num), h.2]
    rw [show ‖(2 : ℝ)‖ₑ = (2 : ℝ≥0∞) by norm_num [← ofReal_norm]]
    simp only [one_div, ENNReal.toReal_inv, ENNReal.toReal_ofNat, smul_eq_mul]
    rw [ENNReal.inv_rpow, show (4 : ℝ≥0∞) = (2 : ℝ≥0∞) ^ (2 : ℝ) by
      rw [ENNReal.rpow_ofNat]; norm_num]
    rw [ENNReal.rpow_rpow_inv two_ne_zero, ← mul_assoc,
      ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
  have hEmb := e.toHomeomorph.measurableEmbedding
  refine ⟨hEmb.memLp_map_measure_iff.mpr (hFourier ▸ hLp.smul_measure (by norm_num)), ?_⟩
  calc
    _ = eLpNorm (lcaFourier μ f ∘ e) 2 μ := hEmb.eLpNorm_map_measure
    _ = eLpNorm g 2 ((2 : ℝ≥0∞) • (volume : Measure ℂ)) := ?_
  rw [hFourier]
  change eLpNorm ((2 : ℝ) • ((𝓕 g) ∘ T)) 2 ((2 : ℝ≥0∞) • (volume : Measure ℂ)) =
    eLpNorm g 2 ((2 : ℝ≥0∞) • (volume : Measure ℂ))
  simp only [eLpNorm_smul_measure_of_ne_zero (by norm_num : (2 : ℝ≥0∞) ≠ 0), hNorm]

section Padic

variable (p : ℕ) [Fact p.Prime]

local instance instPadicMeasurableSpace : MeasurableSpace ℚ_[p] := borel _
local instance : BorelSpace ℚ_[p] := ⟨rfl⟩

/-- Paper: Example A.3.1.6, p. 557. Multiplying by the power of p that clears
the negative valuation places the result in the p-adic integer ring. -/
theorem padicStandardCharacter_integral (x : ℚ_[p]) :
    ‖(p : ℚ_[p]) ^ (-x.valuation).toNat * x‖ ≤ 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rw [norm_mul, Padic.norm_p_pow, Padic.norm_eq_zpow_neg_valuation hx, ← zpow_add₀]
  · apply zpow_le_one_of_nonpos₀
    · exact_mod_cast (Fact.out : p.Prime).one_lt.le
    · have := Int.self_le_toNat (-x.valuation)
      omega
  · exact_mod_cast (Fact.out : p.Prime).ne_zero

/-- Paper: Example A.3.1.6, p. 557. The standard character exponentiates
the rational representative of the coset modulo the p-adic integers.
The representative uses the residue of the cleared integer modulo the clearing power.
Deviation: the sign is opposite to the printed `exp(2πit)`. With the printed sign at the real
place (Example A.3.1.5) and at the p-adic places, the product character of Example A.3.1.8 takes
the value `exp(4πi/3)` on the rational number 1/3. It must be trivial on the rationals for
Theorem 2.2.3.2 and Theorem 3.2.2.1, as in Tate's thesis, where the two kinds of place carry
opposite signs. The real character keeps the printed sign. -/
def padicStandardCharacter (x : ℚ_[p]) : Circle :=
  let n := (-x.valuation).toNat
  let a : ℤ_[p] := ⟨(p : ℚ_[p]) ^ n * x, padicStandardCharacter_integral p x⟩
  Circle.exp (-(2 * Real.pi * ((PadicInt.toZModPow n a).val : ℝ) / (p : ℝ) ^ n))

/-- Paper: Example A.3.1.6, p. 557. On a fraction with denominator a power of p,
the p-adic character has the phase opposite to the real exponential of that fraction.
Deviation: the sign, as in `padicStandardCharacter`. -/
theorem padicStandardCharacter_div_pow (a : ℤ) (n : ℕ) :
    padicStandardCharacter p ((a : ℚ_[p]) / (p : ℚ_[p]) ^ n) =
      Circle.exp (-(2 * Real.pi * ((a : ℝ) / (p : ℝ) ^ n))) := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  set x : ℚ_[p] := (a : ℚ_[p]) / (p : ℚ_[p]) ^ n with hx
  set m := (-x.valuation).toNat with hm
  -- The cleared element `p ^ m * x` is an integer `b` with `b / p ^ m = a / p ^ n`.
  obtain ⟨b, hb, hbR⟩ : ∃ b : ℤ, (p : ℚ_[p]) ^ m * x = b ∧
      (b : ℝ) / (p : ℝ) ^ m = (a : ℝ) / (p : ℝ) ^ n := by
    rcases le_or_gt n m with h | h
    · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
      refine ⟨a * p ^ k, ?_, ?_⟩
      · rw [hx, hk, pow_add]
        push_cast
        field_simp
      · rw [hk, pow_add]
        push_cast
        field_simp
    · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h.le
      have hint := padicStandardCharacter_integral p x
      have hxk : (p : ℚ_[p]) ^ m * x = (a : ℚ_[p]) / (p : ℚ_[p]) ^ k := by
        rw [hx, hk, pow_add]
        field_simp
      rw [← hm, hxk, norm_div, div_le_one (norm_pos_iff.mpr (pow_ne_zero _ hp0)), Padic.norm_p_pow] at hint
      obtain ⟨c, rfl⟩ := (Padic.norm_int_le_pow_iff_dvd a k).mp hint
      refine ⟨c, ?_, ?_⟩
      · rw [hxk]
        push_cast
        field_simp
      · rw [hk, pow_add]
        push_cast
        field_simp
  have hA : (⟨(p : ℚ_[p]) ^ m * x, padicStandardCharacter_integral p x⟩ : ℤ_[p]) = (b : ℤ_[p]) :=
    Subtype.ext (by
      change (p : ℚ_[p]) ^ m * x = ((b : ℤ_[p]) : ℚ_[p])
      rw [hb]
      simp)
  have hval : (((PadicInt.toZModPow m (b : ℤ_[p])).val : ℕ) : ℝ) = ((b % (p ^ m : ℕ) : ℤ) : ℝ) := by
    rw [map_intCast]
    have := NeZero.of_pos (pow_pos (Fact.out : p.Prime).pos m)
    exact_mod_cast ZMod.val_intCast (n := p ^ m) b
  have hdiv := Int.emod_add_mul_ediv b (p ^ m : ℕ)
  change Circle.exp (-(2 * Real.pi * ((PadicInt.toZModPow m
    (⟨(p : ℚ_[p]) ^ m * x, padicStandardCharacter_integral p x⟩ : ℤ_[p])).val : ℝ) /
      (p : ℝ) ^ m)) = _
  rw [hA, hval, Circle.exp_eq_exp]
  refine ⟨b / (p ^ m : ℕ), ?_⟩
  rw [← hbR]
  have hdivR : ((b % (p ^ m : ℕ) : ℤ) : ℝ) = b - (p : ℝ) ^ m * ((b / (p ^ m : ℕ) : ℤ) : ℝ) := by
    rw [eq_sub_iff_add_eq]
    exact_mod_cast hdiv
  rw [hdivR]
  field_simp
  ring

local notation "ℤₚ" => Metric.closedBall (0 : ℚ_[p]) 1

/-- Paper: Example A.3.1.7, p. 557. The standard additive measure on the
p-adic field is Haar measure with the integer ring assigned volume one. -/
theorem padicTamagawaMeasure_existsUnique :
    ∃! μ : Measure ℚ_[p], μ.IsAddHaarMeasure ∧ μ.Regular ∧ μ (ℤₚ) = 1 := by
  let K : TopologicalSpace.PositiveCompacts ℚ_[p] :=
    ⟨⟨ℤₚ, isCompact_closedBall _ _⟩,
      ⟨0, Metric.ball_subset_interior_closedBall (Metric.mem_ball_self zero_lt_one)⟩⟩
  refine ⟨Measure.addHaarMeasure K,
    ⟨inferInstance, inferInstance, Measure.addHaarMeasure_self⟩, ?_⟩
  rintro μ ⟨hhaar, -, hμ⟩
  let : μ.IsAddHaarMeasure := hhaar
  exact ((Measure.addHaarMeasure_eq_iff K μ).2 hμ).symm

/-- Paper: Example A.3.1.7, p. 557. Use the unique regular additive Haar
measure on the p-adic field for which the integer ring has mass one. -/
def padicTamagawaMeasure : Measure ℚ_[p] :=
  (padicTamagawaMeasure_existsUnique p).exists.choose

/-- The phase defining the standard character can be computed with any clearing power. -/
private theorem padicStandardCharacter_of_clear (x : ℚ_[p]) (m : ℕ)
    (h : ‖(p : ℚ_[p]) ^ m * x‖ ≤ 1) :
    let : NeZero (p ^ m) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
    padicStandardCharacter p x =
      (ZMod.toCircle (PadicInt.toZModPow m ⟨_, h⟩))⁻¹ := by
  have hp : 1 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (p : ℝ) ≠ 0 := (zero_lt_one.trans hp).ne'
  let k := (-x.valuation).toNat
  have hkm : k ≤ m := by
    by_cases hx : x = 0
    · simp [k, hx, Padic.valuation_zero]
    · rw [norm_mul, Padic.norm_p_pow, Padic.norm_eq_zpow_neg_valuation hx, ← zpow_add₀ hp0,
        ← zpow_zero (p : ℝ), zpow_le_zpow_iff_right₀ hp] at h
      dsimp [k]
      omega
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkm
  let : NeZero (p ^ k) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  let : NeZero (p ^ (k + d)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  let a : ℤ_[p] := ⟨_, padicStandardCharacter_integral p x⟩
  let r := (PadicInt.toZModPow k a).val
  -- An extra clearing factor multiplies both the residue representative and the modulus.
  have hr : a - (r : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p]) ^ k} := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast]
    simp [r]
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hr
  have hscaled : (⟨_, h⟩ : ℤ_[p]) = (p : ℤ_[p]) ^ d * a := by
    ext
    change (p : ℚ_[p]) ^ (k + d) * x = _
    push_cast
    change _ = (p : ℚ_[p]) ^ d * ((p : ℚ_[p]) ^ k * x)
    rw [pow_add, mul_comm ((p : ℚ_[p]) ^ k), mul_assoc]
  have hres : PadicInt.toZModPow (k + d) (⟨_, h⟩ : ℤ_[p]) = (p ^ d * r : ℕ) := by
    rw [hscaled, ← sub_eq_zero, ← map_natCast (PadicInt.toZModPow (k + d)),
      ← map_sub (PadicInt.toZModPow (k + d)), ← RingHom.mem_ker,
      PadicInt.ker_toZModPow, Ideal.mem_span_singleton]
    refine ⟨b, ?_⟩
    push_cast
    rw [← mul_sub, hb, pow_add]
    ac_rfl
  have hlt : p ^ d * r < p ^ (k + d) := by
    rw [pow_add, mul_comm (p ^ k)]
    exact Nat.mul_lt_mul_of_pos_left (ZMod.val_lt _) (pow_pos (Fact.out : p.Prime).pos _)
  change Circle.exp (-(2 * Real.pi * (r : ℝ) / (p : ℝ) ^ k)) = _
  rw [ZMod.toCircle_eq_circleExp, ← Circle.exp_neg, hres, ZMod.val_natCast_of_lt hlt]
  congr 2
  push_cast
  rw [pow_add]
  field_simp

/-- The standard character is multiplicative on sums of p-adic numbers. -/
private theorem padicStandardCharacter_add (x y : ℚ_[p]) :
    padicStandardCharacter p (x + y) =
      padicStandardCharacter p x * padicStandardCharacter p y := by
  let m := max (-x.valuation).toNat (-y.valuation).toNat
  have hp : 1 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have clearPower (z : ℚ_[p]) (hz : (-z.valuation).toNat ≤ m) :
      ‖(p : ℚ_[p]) ^ m * z‖ ≤ 1 := by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hz
    rw [hd, pow_add, mul_comm ((p : ℚ_[p]) ^ (-z.valuation).toNat), mul_assoc, norm_mul,
      Padic.norm_p_pow]
    exact (mul_le_mul_of_nonneg_right (zpow_le_one_of_nonpos₀ hp.le (by omega))
      (norm_nonneg _)).trans (by simpa only [one_mul] using padicStandardCharacter_integral p z)
  have hx := clearPower x (le_max_left _ _)
  have hy := clearPower y (le_max_right _ _)
  have hxy : ‖(p : ℚ_[p]) ^ m * (x + y)‖ ≤ 1 := by
    rw [mul_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
  let : NeZero (p ^ m) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  rw [padicStandardCharacter_of_clear p _ m hxy, padicStandardCharacter_of_clear p _ m hx,
    padicStandardCharacter_of_clear p _ m hy]
  let a : ℤ_[p] := ⟨_, hx⟩
  let b : ℤ_[p] := ⟨_, hy⟩
  have hsum : (⟨_, hxy⟩ : ℤ_[p]) = a + b := Subtype.ext (mul_add ..)
  change (ZMod.toCircle (PadicInt.toZModPow m ⟨_, hxy⟩))⁻¹ =
    (ZMod.toCircle (PadicInt.toZModPow m a))⁻¹ * (ZMod.toCircle (PadicInt.toZModPow m b))⁻¹
  rw [hsum, map_add, AddChar.map_add_eq_mul, mul_inv]

/-- The kernel of the standard character is precisely the unit ball. -/
private theorem padicStandardCharacter_eq_one_iff (x : ℚ_[p]) :
    padicStandardCharacter p x = 1 ↔ ‖x‖ ≤ 1 := by
  constructor
  · intro h
    let m := (-x.valuation).toNat
    let a : ℤ_[p] := ⟨_, padicStandardCharacter_integral p x⟩
    let : NeZero (p ^ m) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
    rw [padicStandardCharacter_of_clear p _ m a.property] at h
    change (ZMod.toCircle (PadicInt.toZModPow m a))⁻¹ = 1 at h
    rw [inv_eq_one, ← (ZMod.toCircle (N := p ^ m)).map_zero_eq_one,
      ZMod.injective_toCircle.eq_iff] at h
    rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at h
    obtain ⟨b, hb⟩ := h
    have hval : (p : ℚ_[p]) ^ m * x = (p : ℚ_[p]) ^ m * (b : ℚ_[p]) := by
      exact congrArg (fun z : ℤ_[p] ↦ (z : ℚ_[p])) hb
    have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    rw [mul_right_inj' (pow_ne_zero _ hp0)] at hval
    exact hval ▸ b.property
  · intro h
    have hx : ‖(p : ℚ_[p]) ^ (0 : ℕ) * x‖ ≤ 1 := by simpa using h
    rw [padicStandardCharacter_of_clear p _ 0 hx]
    have hz : PadicInt.toZModPow 0 (⟨_, hx⟩ : ℤ_[p]) = 0 := by
      change (_ : ZMod 1) = _
      exact Subsingleton.elim _ _
    rw [hz, AddChar.map_zero_eq_one, inv_one]

/-- The `p` residue classes in the integer ball have equal Haar mass. -/
private theorem padicTamagawaMeasure_mul_prime :
    padicTamagawaMeasure p (((p : ℚ_[p]) * ·) '' ℤₚ) = (p : ℝ≥0∞)⁻¹ := by
  let μ := padicTamagawaMeasure p
  obtain ⟨hμ, -, hmass⟩ := Classical.choose_spec (padicTamagawaMeasure_existsUnique p).exists
  change μ.IsAddHaarMeasure at hμ
  change μ ℤₚ = 1 at hmass
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hp : 1 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  let B (i : Fin p) := Metric.closedBall (i.val : ℚ_[p]) (p : ℝ)⁻¹
  have hsubset (i : Fin p) : B i ⊆ ℤₚ := by
    intro x hx
    have hnorm : ‖x - (i.val : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ := by
      simpa only [B, Metric.mem_closedBall, dist_eq_norm] using hx
    have hi : ‖(i.val : ℚ_[p])‖ ≤ 1 := (i.val : ℤ_[p]).property
    rw [Metric.mem_closedBall, dist_zero_right, ← sub_add_cancel x (i.val : ℚ_[p])]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le (hnorm.trans (inv_le_one_of_one_le₀ hp.le)) hi)
  have hrepr (x : ℤ_[p]) (i : Fin p) :
      (x : ℚ_[p]) ∈ B i ↔ x.zmodRepr = i.val := by
    change dist (x : ℚ_[p]) _ ≤ _ ↔ _
    rw [dist_eq_norm]
    have hnorm : ‖(x : ℚ_[p]) - (i.val : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ ↔
        x - (i.val : ℤ_[p]) ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
      rw [PadicInt.maximalIdeal_eq_span_p]
      simpa [PadicInt.norm_def] using
        ((x - (i.val : ℤ_[p])).norm_le_pow_iff_mem_span_pow 1)
    rw [hnorm]
    exact ⟨fun h ↦ x.zmodRepr_unique _ i.isLt h,
      fun h ↦ h ▸ x.sub_zmodRepr_mem⟩
  have hcover : (⋃ i, B i) = ℤₚ := by
    refine Set.Subset.antisymm (Set.iUnion_subset hsubset) ?_
    intro x hx
    let z : ℤ_[p] := ⟨x, by
      change ‖x‖ ≤ 1
      simpa only [Metric.mem_closedBall, dist_zero_right] using hx⟩
    exact Set.mem_iUnion.mpr ⟨⟨z.zmodRepr, z.zmodRepr_lt_p⟩, (hrepr z _).mpr rfl⟩
  have hdisjoint : Pairwise (Disjoint on B) := by
    intro i j hij
    refine Set.disjoint_left.mpr fun x hi hj ↦ hij (Fin.ext ?_)
    let z : ℤ_[p] := ⟨x, by
      change ‖x‖ ≤ 1
      simpa only [Metric.mem_closedBall, dist_zero_right] using hsubset i hi⟩
    exact ((hrepr z i).mp hi).symm.trans ((hrepr z j).mp hj)
  have hball (i : Fin p) : μ (B i) = μ (((p : ℚ_[p]) * ·) '' ℤₚ) := by
    change μ (B i) = μ (((p : ℚ_[p]) • ·) '' ℤₚ)
    rw [Metric.smul_image_closedBall hp0, smul_zero, mul_one, Padic.norm_p]
    exact Measure.addHaar_closedBall_center μ _ _
  have hsum := measure_iUnion (μ := μ) hdisjoint
    (fun i ↦ (Metric.isClosed_closedBall : IsClosed (B i)).measurableSet)
  rw [hcover, hmass, tsum_fintype] at hsum
  simp only [hball, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hpn : (p : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hpt : (p : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [← ENNReal.mul_inv_cancel hpn hpt, ENNReal.mul_right_inj hpn hpt] at hsum
  exact hsum.symm

/-- Multiplication by a power of p scales the Haar mass of the integer ball by its norm. -/
private theorem padicTamagawaMeasure_scaledIntegers_real (n : ℤ) :
    (padicTamagawaMeasure p).real (((p : ℚ_[p]) ^ n * ·) '' ℤₚ) = (p : ℝ) ^ (-n) := by
  let μ := padicTamagawaMeasure p
  obtain ⟨hμ, hreg, hmass⟩ := Classical.choose_spec (padicTamagawaMeasure_existsUnique p).exists
  change μ.IsAddHaarMeasure at hμ
  change μ.Regular at hreg
  change μ ℤₚ = 1 at hmass
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  let u := Units.mk0 (p : ℚ_[p]) hp0
  have hu (j : ℤ) :
      u ^ j • ℤₚ = (((p : ℚ_[p]) ^ j * ·) '' ℤₚ) := by
    change ((fun x : ℚ_[p] ↦ (↑(u ^ j) : ℚ_[p]) * x) '' ℤₚ) = _
    simp [u]
  have hprime : μ (u • ℤₚ) = (p : ℝ≥0∞)⁻¹ := by
    have h := hu 1
    simp only [zpow_one] at h
    rw [h]
    exact padicTamagawaMeasure_mul_prime p
  have hpN : (p : ℝ≥0) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hchar : distribHaarChar ℚ_[p] u = (p : ℝ≥0)⁻¹ := by
    apply ENNReal.coe_injective
    have h := distribHaarChar_mul μ u ℤₚ
    rw [hmass, mul_one, hprime] at h
    simpa [ENNReal.coe_inv hpN] using h
  have h := distribHaarChar_mul μ (u ^ n) ℤₚ
  rw [hmass, mul_one, map_zpow, hchar, hu] at h
  rw [measureReal_def, ← h, ENNReal.coe_toReal, NNReal.coe_zpow, NNReal.coe_inv,
    NNReal.coe_natCast, inv_zpow, zpow_neg]

-- TODO(paper-gap): In (A.3.1.5) the scaling step inserts an incorrect frequency
-- shift, and the translation phase needs conjugation under (D.1.1.4).
-- The zero-translation specialization and the unit formula are unaffected.

/-- Paper: Example A.3.1.6, p. 557. The Fourier transform of the indicator of
the scaled p-adic integer ring is the reciprocal-scale indicator times the scaling factor.
Deviation: This is the valid zero-translation specialization of (A.3.1.5). -/
theorem padicTamagawaFourier_scaledIntegers (n : ℤ) :
    tamagawaFourier (padicTamagawaMeasure p) (padicStandardCharacter p)
        ((((p : ℚ_[p]) ^ n * ·) '' ℤₚ).indicator (fun _ ↦ (1 : ℂ))) =
      ((p : ℝ) ^ (-n) : ℂ) • ((((p : ℚ_[p]) ^ (-n) * ·) '' ℤₚ).indicator (fun _ ↦ (1 : ℂ))) := by
  let μ := padicTamagawaMeasure p
  have hμ : μ.IsAddHaarMeasure :=
    (Classical.choose_spec (padicTamagawaMeasure_existsUnique p).exists).1
  let a := (p : ℚ_[p]) ^ n
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have ha : a ≠ 0 := zpow_ne_zero _ hp0
  let H := ((PadicInt.subring p).toAddSubgroup).map (AddMonoidHom.mulLeft a)
  let s := (a * ·) '' ℤₚ
  have hs : (H : Set ℚ_[p]) = s := by
    change (a * ·) '' {x : ℚ_[p] | ‖x‖ ≤ 1} = _
    simp only [s, Metric.closedBall, dist_zero_right]
  have haH : a ∈ H := by
    refine AddSubgroup.mem_map.mpr ⟨1, (PadicInt.subring p).one_mem, ?_⟩
    exact mul_one a
  have hsmeas : MeasurableSet s := by
    change MeasurableSet ((a • ·) '' ℤₚ)
    rw [Metric.smul_image_closedBall ha]
    exact Metric.isClosed_closedBall.measurableSet
  funext y
  let f (x : ℚ_[p]) : ℂ := star (padicStandardCharacter p (x * y) : ℂ)
  let g := s.indicator f
  change (∫ x, s.indicator (fun _ ↦ (1 : ℂ)) x * f x ∂μ) =
    ((p : ℝ) ^ (-n) : ℂ) * (((p : ℚ_[p]) ^ (-n) * ·) '' ℤₚ).indicator (fun _ ↦ 1) y
  simp_rw [← Set.indicator_mul_left, one_mul]
  have hymem : y ∈ (((p : ℚ_[p]) ^ (-n) * ·) '' ℤₚ) ↔ ‖a * y‖ ≤ 1 := by
    rw [zpow_neg]
    change y ∈ a⁻¹ • ℤₚ ↔ _
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero ha), inv_inv]
    simp only [smul_eq_mul, Metric.mem_closedBall, dist_zero_right]
  by_cases hy : y ∈ (((p : ℚ_[p]) ^ (-n) * ·) '' ℤₚ)
  · rw [Set.indicator_of_mem hy, mul_one, integral_indicator hsmeas]
    calc
      (∫ x in s, f x ∂μ) = ∫ _ in s, (1 : ℂ) ∂μ := by
        refine setIntegral_congr_fun hsmeas ?_
        rintro _ ⟨z, hz, rfl⟩
        have hz' : ‖z‖ ≤ 1 := by
          simpa only [Metric.mem_closedBall, dist_zero_right] using hz
        have hzy : ‖a * z * y‖ ≤ 1 := by
          rw [show a * z * y = z * (a * y) by ac_rfl, norm_mul]
          exact (mul_le_of_le_one_left (norm_nonneg _) hz').trans (hymem.mp hy)
        simp [f, (padicStandardCharacter_eq_one_iff p _).mpr hzy]
      _ = ((p : ℝ) ^ (-n) : ℂ) := by
        rw [setIntegral_const, Complex.real_smul, mul_one]
        have h := congrArg Complex.ofReal (padicTamagawaMeasure_scaledIntegers_real p n)
        simpa only [Complex.ofReal_zpow, Complex.ofReal_natCast] using h
  · -- Translation by `a ∈ p ^ n ℤₚ` leaves the integral invariant and multiplies it by `f a`.
    rw [Set.indicator_of_notMem hy, mul_zero]
    change (∫ x, g x ∂μ) = 0
    have hne : f a ≠ 1 := by
      intro h
      apply hy
      apply hymem.mpr
      apply (padicStandardCharacter_eq_one_iff p _).mp
      exact Subtype.ext (by simpa [f] using congrArg star h)
    have htranslate (x : ℚ_[p]) : g (a + x) = f a * g x := by
      have hmem : a + x ∈ s ↔ x ∈ s := by
        rw [← hs]
        exact H.add_mem_cancel_left haH
      by_cases hx : x ∈ s
      · simp only [g, Set.indicator_of_mem hx, Set.indicator_of_mem (hmem.mpr hx), f,
          add_mul, padicStandardCharacter_add, Circle.coe_mul, star_mul']
      · rw [show g (a + x) = 0 from Set.indicator_of_notMem (mt hmem.mp hx) _,
          show g x = 0 from Set.indicator_of_notMem hx _, mul_zero]
    have h : f a * (∫ x, g x ∂μ) = 1 * (∫ x, g x ∂μ) := by
      rw [one_mul, ← integral_const_mul, ← integral_add_left_eq_self (μ := μ) g a]
      exact integral_congr_ae (ae_of_all _ fun x ↦ (htranslate x).symm)
    exact (mul_eq_mul_right_iff.mp h).resolve_left hne

/-- The defining phase with the clearing exponent and its integrality proof supplied explicitly. -/
private theorem padicStandardCharacter_eq_exp_of_clearingPower (x : ℚ_[p]) (n : ℕ) (hn : (-x.valuation).toNat = n)
    (hx : ‖(p : ℚ_[p]) ^ n * x‖ ≤ 1) :
    padicStandardCharacter p x =
      Circle.exp (-(2 * Real.pi * ((PadicInt.toZModPow n
        (⟨(p : ℚ_[p]) ^ n * x, hx⟩ : ℤ_[p])).val : ℝ) / (p : ℝ) ^ n)) := by
  subst n
  rfl

/-- The standard character is trivial on the p-adic integers. -/
private theorem padicStandardCharacter_eq_one_of_norm_le_one {x : ℚ_[p]} (hx : ‖x‖ ≤ 1) :
    padicStandardCharacter p x = 1 := by
  have hn : (-x.valuation).toNat = 0 := by
    have := (Padic.norm_le_one_iff_val_nonneg x).mp hx
    omega
  let a : ℤ_[p] := ⟨(p : ℚ_[p]) ^ (0 : ℕ) * x, by
    change ‖(p : ℚ_[p]) ^ (0 : ℕ) * x‖ ≤ 1
    simpa using hx⟩
  rw [padicStandardCharacter_eq_exp_of_clearingPower p x 0 hn a.property]
  change Circle.exp (-(2 * Real.pi * ((PadicInt.toZModPow 0 a).val : ℝ) / (p : ℝ) ^ (0 : ℕ))) = 1
  have : Subsingleton (ZMod (p ^ (0 : ℕ))) := by
    simpa only [pow_zero] using (inferInstance : Subsingleton (ZMod 1))
  have hzero (a : ℤ_[p]) : (PadicInt.toZModPow 0 a).val = 0 := by
    have heq : PadicInt.toZModPow 0 a = 0 := Subsingleton.elim _ _
    exact (congrArg ZMod.val heq).trans ZMod.val_zero
  simp only [hzero, Nat.cast_zero, mul_zero, zero_div, neg_zero, Circle.exp_zero]

/-- Adding an integral element preserves the clearing residue of a nonintegral element,
and hence preserves the character. -/
private theorem padicStandardCharacter_add_of_norm_le_one (x z : ℚ_[p]) (hz : ‖z‖ ≤ 1) :
    padicStandardCharacter p (x + z) = padicStandardCharacter p x := by
  by_cases hx : ‖x‖ ≤ 1
  · rw [padicStandardCharacter_eq_one_of_norm_le_one p hx, padicStandardCharacter_eq_one_of_norm_le_one p ((Padic.nonarchimedean x z).trans (max_le hx hz))]
  have hnorm : ‖x + z‖ = ‖x‖ := by
    have hlt := hz.trans_lt (lt_of_not_ge hx)
    rw [Padic.add_eq_max_of_ne hlt.ne', max_eq_left hlt.le]
  have hx0 : x ≠ 0 := by
    intro h
    simp [h] at hx
  have hxz0 : x + z ≠ 0 := by
    intro h
    have := norm_pos_iff.mpr hx0
    rw [← hnorm, h, norm_zero] at this
    exact (lt_irrefl _ this)
  have hval : (x + z).valuation = x.valuation := by
    rw [Padic.norm_eq_zpow_neg_valuation hxz0, Padic.norm_eq_zpow_neg_valuation hx0,
      (zpow_right_strictMono₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt : (1 : ℝ) < p)).injective.eq_iff,
      neg_inj] at hnorm
    exact hnorm
  let n := (-x.valuation).toNat
  let a : ℤ_[p] := ⟨(p : ℚ_[p]) ^ n * x, padicStandardCharacter_integral p x⟩
  let b : ℤ_[p] := ⟨(p : ℚ_[p]) ^ n * (x + z), by
    change ‖(p : ℚ_[p]) ^ n * (x + z)‖ ≤ 1
    simpa only [hval] using padicStandardCharacter_integral p (x + z)⟩
  let c : ℤ_[p] := ⟨z, hz⟩
  have hb : b = a + (p : ℤ_[p]) ^ n * c := by
    apply Subtype.ext
    change (p : ℚ_[p]) ^ n * (x + z) = _
    rw [PadicInt.coe_add, PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast]
    exact mul_add _ _ _
  have hc : PadicInt.toZModPow n ((p : ℤ_[p]) ^ n * c) = 0 := by
    change (p : ℤ_[p]) ^ n * c ∈ RingHom.ker (PadicInt.toZModPow n)
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton]
    exact dvd_mul_right _ _
  have hres : PadicInt.toZModPow n b = PadicInt.toZModPow n a := by
    rw [hb, map_add, hc, add_zero]
  rw [padicStandardCharacter_eq_exp_of_clearingPower p (x + z) n (by rw [hval]) b.property,
    padicStandardCharacter_eq_exp_of_clearingPower p x n rfl a.property]
  change Circle.exp (-(2 * Real.pi * ((PadicInt.toZModPow n b).val : ℝ) / (p : ℝ) ^ n)) =
    Circle.exp (-(2 * Real.pi * ((PadicInt.toZModPow n a).val : ℝ) / (p : ℝ) ^ n))
  rw [hres]

/-- The standard character is locally constant on translates of the p-adic integers. -/
private theorem padicStandardCharacter_continuous : Continuous (padicStandardCharacter p) := by
  refine continuous_iff_continuousAt.mpr fun x ↦ Metric.continuousAt_iff.mpr ?_
  intro ε hε
  refine ⟨1, zero_lt_one, fun {y} hy ↦ ?_⟩
  rw [dist_eq_norm] at hy
  have h := padicStandardCharacter_add_of_norm_le_one p x (y - x) hy.le
  rw [add_comm x, sub_add_cancel] at h
  simpa [h]

/-- The inverse of p has a nontrivial standard character value. -/
private theorem padicStandardCharacter_inv_prime_ne_one :
    padicStandardCharacter p ((p : ℚ_[p])⁻¹) ≠ 1 := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hphase : padicStandardCharacter p ((p : ℚ_[p])⁻¹) =
      Circle.exp (-(2 * Real.pi * (p : ℝ)⁻¹)) := by
    simpa [one_div] using padicStandardCharacter_div_pow p 1 1
  rw [hphase]
  intro h
  obtain ⟨k, hk⟩ := Circle.exp_eq_one.mp h
  have heq : -((p : ℝ)⁻¹) = (k : ℝ) := by
    apply mul_left_cancel₀ (show (2 : ℝ) * Real.pi ≠ 0 by positivity)
    nlinarith only [hk]
  have hlo : (-1 : ℝ) < (k : ℝ) := by
    rw [← heq]
    linarith [inv_lt_one_of_one_lt₀ hp]
  have hhi : (k : ℝ) < 0 := by
    rw [← heq]
    exact neg_lt_zero.mpr (inv_pos.mpr (zero_lt_one.trans hp))
  have hlo' : (-1 : ℤ) < k := by exact_mod_cast hlo
  have hhi' : k < 0 := by exact_mod_cast hhi
  omega

/-- Scaling the p-adic integer ring by a nonzero scalar gives the closed ball
with radius equal to the norm of that scalar. -/
private theorem padicScaledIntegers_eq_closedBall (c : ℚ_[p]) (hc : c ≠ 0) :
    (c * ·) '' ℤₚ = Metric.closedBall 0 ‖c‖ := by
  have hnorm (x : ℚ_[p]) : x ∈ ℤₚ ↔ ‖c * x‖ ≤ ‖c‖ := by
    rw [Metric.mem_closedBall, dist_zero_right, norm_mul, mul_le_iff_le_one_right (norm_pos_iff.mpr hc)]
  ext x
  rw [Metric.mem_closedBall, dist_zero_right]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (hnorm z).mp hz
  · intro hx
    have heq : c * (x / c) = x := by rw [mul_comm, div_mul_cancel₀ _ hc]
    exact ⟨x / c, (hnorm _).mpr (by rw [heq]; exact hx), heq⟩

/-- The multiples of p in the p-adic integer ring form the open unit ball. -/
private theorem padicPrimeMulIntegers_eq_ball (hp : (p : ℚ_[p]) ≠ 0) :
    ((p : ℚ_[p]) * ·) '' ℤₚ = Metric.ball 0 1 := by
  rw [padicScaledIntegers_eq_closedBall p _ hp, Padic.norm_p]
  ext x
  simpa only [Metric.mem_ball, dist_zero_right, mem_closedBall_zero_iff, zpow_zero, zero_sub,
    zpow_neg_one] using (Padic.norm_lt_pow_iff_norm_le_pow_sub_one x 0).symm

/-- The open unit ball has Tamagawa mass 1/p because it is the kernel of
reduction of the integer ring modulo p. -/
private theorem padicTamagawaMeasure_real_primeMulIntegers (hp : (p : ℚ_[p]) ≠ 0) :
    (padicTamagawaMeasure p).real (((p : ℚ_[p]) * ·) '' ℤₚ) = (p : ℝ)⁻¹ := by
  let μ := padicTamagawaMeasure p
  have hμ := Classical.choose_spec (padicTamagawaMeasure_existsUnique p).exists
  have : μ.IsAddHaarMeasure := hμ.1
  let : MeasurableSpace ℤ_[p] := MeasurableSpace.comap (fun x : ℤ_[p] ↦ (x : ℚ_[p])) inferInstance
  have : BorelSpace ℤ_[p] := ⟨borel_comap.symm⟩
  let e : ℤ_[p] →+ ℚ_[p] :=
    { toFun := fun x ↦ (x : ℚ_[p])
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  have he : MeasurableEmbedding e := by
    change MeasurableEmbedding (Subtype.val : (PadicInt.subring p) → ℚ_[p])
    exact MeasurableEmbedding.subtype_coe (by
      change MeasurableSet {x : ℚ_[p] | ‖x‖ ≤ 1}
      exact isClosed_le continuous_norm continuous_const |>.measurableSet)
  have : (μ.comap e).IsAddLeftInvariant := Measure.IsAddLeftInvariant.comap μ he
  let f : ℤ_[p] →+ ZMod p := PadicInt.toZMod.toAddMonoidHom
  have hf : Surjective f := fun a ↦ ⟨(a.val : ℤ_[p]), by
    change PadicInt.toZMod (a.val : ℤ_[p]) = a
    rw [map_natCast, ZMod.natCast_zmod_val]⟩
  have hindex : f.ker.index = p := by
    rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr hf, AddSubgroup.card_top, Nat.card_eq_fintype_card, ZMod.card]
  have : f.ker.FiniteIndex := ⟨hindex.trans_ne (Fact.out : p.Prime).ne_zero⟩
  have hker (a : ℤ_[p]) : a ∈ f.ker ↔ ‖a‖ < 1 := by
    change a ∈ RingHom.ker PadicInt.toZMod ↔ _
    rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton,
      PadicInt.norm_lt_one_iff_dvd]
  have hmeas : MeasurableSet (f.ker : Set ℤ_[p]) := by
    have heq : (f.ker : Set ℤ_[p]) = {a | ‖a‖ < 1} := by
      ext a
      exact hker a
    rw [heq]
    exact (isOpen_lt continuous_norm continuous_const).measurableSet
  have himage : e '' (f.ker : Set ℤ_[p]) = ((p : ℚ_[p]) * ·) '' ℤₚ := by
    rw [padicPrimeMulIntegers_eq_ball p hp]
    ext x
    rw [Metric.mem_ball, dist_zero_right]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (hker a).mp ha
    · intro hx
      exact ⟨⟨x, hx.le⟩, (hker _).mpr hx, rfl⟩
  have hrange : Set.range e = ℤₚ := by
    ext x
    rw [mem_closedBall_zero_iff]
    exact ⟨fun ⟨a, ha⟩ ↦ ha ▸ a.norm_le_one, fun hx ↦ ⟨⟨x, hx⟩, rfl⟩⟩
  have hone : μ ℤₚ = 1 := hμ.2.2
  have hm := f.ker.index_mul_measure hmeas (μ.comap e)
  rw [hindex, he.comap_apply, he.comap_apply, himage, Set.image_univ, hrange, hone] at hm
  have hm' := congrArg ENNReal.toReal hm
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_one] at hm'
  change (μ (((p : ℚ_[p]) * ·) '' ℤₚ)).toReal = _
  rw [← one_div, eq_div_iff (by exact_mod_cast (Fact.out : p.Prime).ne_zero), mul_comm]
  exact hm'

/-- The transform of the indicator of a scaled p-adic integer ball is its mass
times the indicator of the reciprocal ball. -/
private theorem padicTamagawaFourier_scaledIntegers_eq_measure (c : ℚ_[p]) (hc : c ≠ 0) :
    tamagawaFourier (padicTamagawaMeasure p) (padicStandardCharacter p)
      (((c * ·) '' ℤₚ).indicator (fun _ ↦ (1 : ℂ))) =
    ((padicTamagawaMeasure p).real ((c * ·) '' ℤₚ) : ℂ) •
      (((c⁻¹ * ·) '' ℤₚ).indicator (fun _ ↦ (1 : ℂ))) := by
  let μ := padicTamagawaMeasure p
  have : μ.IsAddHaarMeasure :=
    (Classical.choose_spec (padicTamagawaMeasure_existsUnique p).exists).1
  let B := Metric.closedBall (0 : ℚ_[p]) ‖c‖
  have hB : MeasurableSet B := Metric.isClosed_closedBall.measurableSet
  rw [padicScaledIntegers_eq_closedBall p c hc, padicScaledIntegers_eq_closedBall p c⁻¹ (inv_ne_zero hc)]
  funext y
  let g (x : ℚ_[p]) : ℂ := star (padicStandardCharacter p (x * y) : ℂ)
  change (∫ x, B.indicator (fun _ ↦ (1 : ℂ)) x * g x ∂μ) = _
  simp only [← Set.indicator_mul_left, one_mul, integral_indicator hB]
  have hy : y ∈ Metric.closedBall (0 : ℚ_[p]) ‖c⁻¹‖ ↔ ‖y‖ * ‖c‖ ≤ 1 := by
    rw [mem_closedBall_zero_iff, norm_inv, ← one_div, le_div_iff₀ (norm_pos_iff.mpr hc)]
  by_cases hyc : y ∈ Metric.closedBall (0 : ℚ_[p]) ‖c⁻¹‖
  · have hg : EqOn g (fun _ ↦ (1 : ℂ)) B := fun x hx ↦ by
      have hx' : ‖x‖ ≤ ‖c‖ := mem_closedBall_zero_iff.mp hx
      have hnorm : ‖x * y‖ ≤ 1 := by
        rw [norm_mul, mul_comm]
        exact (mul_le_mul_of_nonneg_left hx' (norm_nonneg _)).trans (hy.mp hyc)
      simp [g, padicStandardCharacter_eq_one_of_norm_le_one p hnorm]
    rw [setIntegral_congr_fun hB hg]
    rw [Pi.smul_apply, indicator_of_mem hyc]
    simp [Complex.real_smul, B, μ]
  · have hy' := lt_of_not_ge (mt hy.mpr hyc)
    have hy0 : y ≠ 0 := by
      intro h
      exact (not_lt_of_ge (by simp [h])) hy'
    have hge : (p : ℝ) ≤ ‖y‖ * ‖c‖ := by
      by_contra! h
      have hlt : ‖y * c‖ < (p : ℝ) ^ (1 : ℤ) := by simpa [norm_mul] using h
      have hle := (Padic.norm_lt_pow_iff_norm_le_pow_sub_one (y * c) 1).mp hlt
      exact (not_le_of_gt hy') (by simpa [norm_mul] using hle)
    -- Translation by this point stays in the ball and multiplies the integral by a nontrivial value.
    let t : ℚ_[p] := (p : ℚ_[p])⁻¹ / y
    have ht : ‖t‖ ≤ ‖c‖ := by
      change ‖(p : ℚ_[p])⁻¹ / y‖ ≤ ‖c‖
      rw [norm_div, norm_inv, Padic.norm_p, inv_inv, div_le_iff₀ (norm_pos_iff.mpr hy0), mul_comm]
      exact hge
    have hmem (x : ℚ_[p]) : x + t ∈ B ↔ x ∈ B := by
      simp only [B, mem_closedBall_zero_iff]
      refine ⟨fun h ↦ ?_, fun h ↦ (Padic.nonarchimedean x t).trans (max_le h ht)⟩
      have h' := (Padic.nonarchimedean (x + t) (-t)).trans (max_le h (by simpa using ht))
      simpa using h'
    have ht_mul : t * y = (p : ℚ_[p])⁻¹ := div_mul_cancel₀ _ hy0
    have hnontrivial : g t ≠ 1 := by
      intro h
      apply padicStandardCharacter_inv_prime_ne_one p
      apply Subtype.ext
      exact star_injective (by simpa only [g, ht_mul, Circle.coe_one, star_one] using h)
    have hshift : (fun x ↦ B.indicator g (x + t)) =
        fun x ↦ B.indicator g x * g t := by
      funext x
      by_cases hx : x ∈ B
      · rw [indicator_of_mem hx, indicator_of_mem ((hmem x).mpr hx)]
        simp only [g, add_mul, padicStandardCharacter_add, Circle.coe_mul, star_mul]
        exact mul_comm _ _
      · simp [hx, mt (hmem x).mp hx]
    have h := integral_add_right_eq_self (μ := μ) (B.indicator g) t
    rw [show (fun x ↦ B.indicator g (x + t)) = _ from hshift, integral_mul_const,
      integral_indicator hB] at h
    have hzero : (∫ x in B, g x ∂μ) = 0 := by
      by_contra hne
      exact hnontrivial ((mul_eq_left₀ hne).mp h)
    rw [hzero, Pi.smul_apply, indicator_of_notMem hyc, smul_zero]

/-- Paper: Example A.3.1.6, p. 557. The Fourier transform of the indicator of the
p-adic integer units is the difference in (A.3.1.6). -/
theorem padicTamagawaFourier_integerUnits :
    tamagawaFourier (padicTamagawaMeasure p) (padicStandardCharacter p)
        ({x : ℚ_[p] | ‖x‖ = 1}.indicator (fun _ ↦ (1 : ℂ))) =
      ((ℤₚ).indicator (fun _ ↦ (1 : ℂ))) - ((p : ℂ)⁻¹) • ((((p : ℚ_[p])⁻¹ * ·) '' ℤₚ).indicator (fun _ ↦ (1 : ℂ))) := by
  let μ := padicTamagawaMeasure p
  have hμ := Classical.choose_spec (padicTamagawaMeasure_existsUnique p).exists
  have : μ.IsAddHaarMeasure := hμ.1
  have hp : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  let P := ((p : ℚ_[p]) * ·) '' ℤₚ
  have hP : P = Metric.ball 0 1 := padicPrimeMulIntegers_eq_ball p hp
  have hsub : P ⊆ ℤₚ := hP ▸ Metric.ball_subset_closedBall
  have hdiff : {x : ℚ_[p] | ‖x‖ = 1} = ℤₚ \ P := by
    ext x
    simp only [hP, mem_ofPred_eq, mem_sdiff, mem_closedBall_zero_iff, Metric.mem_ball, dist_zero_right,
      not_lt]
    exact le_antisymm_iff
  have h0 : tamagawaFourier μ (padicStandardCharacter p) ((ℤₚ).indicator (fun _ ↦ (1 : ℂ))) =
      (ℤₚ).indicator (fun _ ↦ (1 : ℂ)) := by
    have hone : (padicTamagawaMeasure p) ℤₚ = 1 := hμ.2.2
    have hmass : (padicTamagawaMeasure p).real ℤₚ = 1 := by
      rw [measureReal_def, hone, ENNReal.toReal_one]
    simpa [hmass] using padicTamagawaFourier_scaledIntegers_eq_measure p 1 one_ne_zero
  have h1 : tamagawaFourier μ (padicStandardCharacter p) (P.indicator (fun _ ↦ (1 : ℂ))) =
      ((p : ℂ)⁻¹) • ((((p : ℚ_[p])⁻¹ * ·) '' ℤₚ).indicator (fun _ ↦ (1 : ℂ))) := by
    simpa [P, padicTamagawaMeasure_real_primeMulIntegers p hp, Complex.ofReal_inv] using padicTamagawaFourier_scaledIntegers_eq_measure p p hp
  rw [hdiff, Set.indicator_sdiff hsub]
  conv_rhs => rw [← h0, ← h1]
  funext y
  let g (x : ℚ_[p]) : ℂ := star (padicStandardCharacter p (x * y) : ℂ)
  have hg : Continuous g :=
    (continuous_subtype_val.comp ((padicStandardCharacter_continuous p).comp (continuous_id.mul continuous_const))).star
  have hInt (s : Set ℚ_[p]) (hs : IsCompact s) : Integrable (s.indicator g) μ :=
    (integrable_indicator_iff hs.measurableSet).mpr (hg.continuousOn.integrableOn_compact hs)
  unfold tamagawaFourier
  change (∫ x, ((ℤₚ).indicator (fun _ ↦ (1 : ℂ)) x - P.indicator (fun _ ↦ (1 : ℂ)) x) * g x ∂μ) =
    (∫ x, (ℤₚ).indicator (fun _ ↦ (1 : ℂ)) x * g x ∂μ) -
      ∫ x, P.indicator (fun _ ↦ (1 : ℂ)) x * g x ∂μ
  simp only [sub_mul, ← indicator_mul_left, one_mul]
  exact integral_sub (hInt _ (isCompact_closedBall _ _))
    (hInt _ (by
      change IsCompact (((p : ℚ_[p]) * ·) '' ℤₚ)
      rw [padicScaledIntegers_eq_closedBall p _ hp]
      exact isCompact_closedBall _ _))

open Filter Topology in
/-- A nontrivial continuous additive character on a proper normed field identifies
the additive group with its Pontryagin dual via multiplication. -/
private theorem exists_pontryaginDualEquiv_of_normedField
    {K : Type*} [NormedField K] [ProperSpace K] (ψ : Multiplicative K →ₜ* Circle)
    (hψ : ∃ z, ψ (Multiplicative.ofAdd z) ≠ 1) :
    ∃ e : Multiplicative K ≃ₜ* PontryaginDual (Multiplicative K),
      ∀ x y : K, e (Multiplicative.ofAdd x) (Multiplicative.ofAdd y) =
        ψ (Multiplicative.ofAdd (x * y)) := by
  let G := Multiplicative K
  let char (x : G) : PontryaginDual G :=
    { toFun := fun y ↦ ψ (Multiplicative.ofAdd (x.toAdd * y.toAdd))
      map_one' := by
        change ψ (Multiplicative.ofAdd (x.toAdd * 0)) = 1
        rw [mul_zero]
        exact map_one ψ
      map_mul' := fun a b ↦ by
        change ψ (Multiplicative.ofAdd (x.toAdd * (a.toAdd + b.toAdd))) = _
        rw [mul_add]
        exact map_mul ψ (Multiplicative.ofAdd (x.toAdd * a.toAdd))
          (Multiplicative.ofAdd (x.toAdd * b.toAdd))
      continuous_toFun := ψ.continuous.comp
        (show Continuous (fun y : K ↦ x.toAdd * y) from continuous_const.mul continuous_id) }
  let e : G →ₜ* PontryaginDual G :=
    { toFun := char
      map_one' := PontryaginDual.ext fun y ↦ by
        change ψ (Multiplicative.ofAdd (0 * y.toAdd)) = 1
        rw [zero_mul]
        exact map_one ψ
      map_mul' := fun a b ↦ PontryaginDual.ext fun y ↦ by
        change ψ (Multiplicative.ofAdd ((a.toAdd + b.toAdd) * y.toAdd)) = _
        rw [add_mul]
        exact map_mul ψ (Multiplicative.ofAdd (a.toAdd * y.toAdd))
          (Multiplicative.ofAdd (b.toAdd * y.toAdd))
      continuous_toFun := ContinuousMonoidHom.continuous_of_continuous_uncurry char
        (ψ.continuous.comp (show Continuous (fun p : K × K ↦ p.1 * p.2) from
          continuous_fst.mul continuous_snd)) }
  obtain ⟨z, hz⟩ := hψ
  have htriv (x : G) (hx : e x = 1) : x = 1 := by
    by_contra hne
    have hx0 : x.toAdd ≠ 0 := hne
    apply hz
    have h := DFunLike.congr_fun hx (Multiplicative.ofAdd (z / x.toAdd))
    change ψ (Multiplicative.ofAdd (x.toAdd * (z / x.toAdd))) = 1 at h
    simpa only [mul_comm x.toAdd (z / x.toAdd), div_mul_cancel₀ _ hx0] using h
  have hInducing : IsInducing e := by
    rw [IsTopologicalGroup.isInducing_iff_nhds_one]
    refine le_antisymm ?_ ?_
    · have h := e.continuous.tendsto (1 : G)
      have hOne : e 1 = 1 := map_one e
      exact (hOne ▸ h).le_comap
    · intro U hU
      -- Testing on a compact ball detects every frequency outside the given neighborhood.
      obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (show U ∈ 𝓝 (0 : K) from hU)
      let B : Set G := Metric.closedBall (0 : K) (‖z‖ / ε)
      let V : Set (PontryaginDual G) :=
        {χ | MapsTo χ B ({ψ (Multiplicative.ofAdd z)}ᶜ : Set Circle)}
      have hV : IsOpen V :=
        (ContinuousMap.isOpen_setOfPred_mapsTo (show IsCompact B from isCompact_closedBall _ _)
          isClosed_singleton.isOpen_compl).preimage
          (ContinuousMonoidHom.isInducing_toContinuousMap G Circle).continuous
      refine Filter.mem_comap.mpr ⟨V, hV.mem_nhds (fun y _ ↦ hz.symm), ?_⟩
      intro x hx
      apply hball
      by_contra h
      change x.toAdd ∉ Metric.ball (0 : K) ε at h
      have hxε : ε ≤ ‖x.toAdd‖ := by simpa [Metric.mem_ball, dist_zero_right] using h
      have hx0 := norm_pos_iff.mp (hε.trans_le hxε)
      have hy : Multiplicative.ofAdd (z / x.toAdd) ∈ B := by
        change dist (z / x.toAdd) 0 ≤ ‖z‖ / ε
        rw [dist_zero_right, norm_div]
        exact div_le_div_of_nonneg_left (norm_nonneg _) hε hxε
      have hc := hx hy
      change ψ (Multiplicative.ofAdd (x.toAdd * (z / x.toAdd))) ≠
        ψ (Multiplicative.ofAdd z) at hc
      exact hc (by rw [mul_comm x.toAdd (z / x.toAdd), div_mul_cancel₀ _ hx0])
  have hInj : Injective e := by
    intro a b hab
    exact div_eq_one.mp (htriv (a / b) (by rw [map_div, hab, div_self']))
  let : UniformSpace G := IsTopologicalGroup.rightUniformSpace G
  let : UniformSpace (PontryaginDual G) := IsTopologicalGroup.rightUniformSpace _
  let : IsUniformGroup G := isUniformGroup_of_commGroup
  let : IsUniformGroup (PontryaginDual G) := isUniformGroup_of_commGroup
  let : CompleteSpace G := IsRightUniformGroup.completeSpace_of_weaklyLocallyCompactSpace G
  have hClosed := (MonoidHom.isUniformEmbedding_of_isEmbedding (f := e)
    ⟨hInducing, hInj⟩).isClosedEmbedding
  let H := e.toMonoidHom.range
  let : T1Space (PontryaginDual G ⧸ H) := QuotientGroup.t1Space_iff.mpr hClosed.isClosed_range
  let q : PontryaginDual G →ₜ* (PontryaginDual G ⧸ H) :=
    ⟨QuotientGroup.mk' H, QuotientGroup.continuous_mk⟩
  obtain ⟨bidual, hbidual⟩ := pontryaginDual_bidual (G := G)
  -- By biduality, a character that vanishes on the image would give an element in the kernel of e.
  have hSurj : Surjective e := by
    intro χ
    have hq : q χ = 1 := by
      apply (pontryaginDual_pairing_separates (G := PontryaginDual G ⧸ H)).1
      funext η
      let x := bidual.symm (PontryaginDual.map q η)
      have hx (γ : PontryaginDual G) : η (q γ) = γ x := by
        rw [← hbidual, show bidual x = PontryaginDual.map q η from bidual.apply_symm_apply _]
        rfl
      have hx1 : e x = 1 := by
        apply PontryaginDual.ext
        intro y
        have hy : q (e y) = 1 := (QuotientGroup.eq_one_iff _).mpr ⟨y, rfl⟩
        have h := (hx (e y)).symm.trans (hy ▸ map_one η)
        change ψ (Multiplicative.ofAdd (y.toAdd * x.toAdd)) = 1 at h
        exact (congrArg (ψ ∘ Multiplicative.ofAdd) (mul_comm x.toAdd y.toAdd)).trans h
      change η (q χ) = η 1
      rw [hx, htriv x hx1, map_one, map_one]
    exact (QuotientGroup.eq_one_iff _).mp hq
  let equiv := MulEquiv.ofBijective e.toMonoidHom ⟨hInj, hSurj⟩
  have hOpen := hInducing.isOpenMap (by rw [hSurj.range_eq]; exact isOpen_univ)
  exact ⟨equiv.toContinuousMulEquiv (fun _ ↦
    (hOpen.isQuotientMap e.continuous hSurj).isCoinducing.isOpen_preimage), fun _ _ ↦ rfl⟩

/-- Paper: Example A.3.1.6, p. 557. Multiplication followed by the standard character
identifies the additive group of the p-adic field with its Pontryagin dual. -/
theorem exists_padicPontryaginDualEquiv :
    ∃ e : Multiplicative ℚ_[p] ≃ₜ* PontryaginDual (Multiplicative ℚ_[p]),
      ∀ x y : ℚ_[p], e (Multiplicative.ofAdd x) (Multiplicative.ofAdd y) =
        padicStandardCharacter p (x * y) := by
  let ψ : Multiplicative ℚ_[p] →ₜ* Circle :=
    { toFun := fun x ↦ padicStandardCharacter p x.toAdd
      map_one' := (padicStandardCharacter_eq_one_iff p 0).mpr (by simp)
      map_mul' := fun x y ↦ padicStandardCharacter_add p x.toAdd y.toAdd
      continuous_toFun := padicStandardCharacter_continuous p }
  exact exists_pontryaginDualEquiv_of_normedField ψ
    ⟨(p : ℚ_[p])⁻¹, padicStandardCharacter_inv_prime_ne_one p⟩

/-- Paper: Example A.3.1.7, p. 558. The standard additive measure on the p-adic field
is self-dual under the standard character. -/
theorem padicTamagawaMeasure_selfDual :
    IsTamagawaSelfDual (padicTamagawaMeasure p) (padicStandardCharacter p) := by
  obtain ⟨e, he⟩ := exists_padicPontryaginDualEquiv p
  refine ⟨e, he, ?_⟩
  let G := Multiplicative ℚ_[p]
  let μ : Measure G := padicTamagawaMeasure p
  let : MeasurableSpace (PontryaginDual G) := borel _
  let : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  obtain ⟨hHaar, hRegular, hMass⟩ :=
    Classical.choose_spec (padicTamagawaMeasure_existsUnique p).exists
  let : μ.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := hHaar.toIsFiniteMeasureOnCompacts
      toIsOpenPosMeasure := hHaar.toIsOpenPosMeasure
      map_mul_left_eq_self := fun x ↦ hHaar.map_add_left_eq_self x.toAdd }
  let : μ.Regular := hRegular
  let ν₀ : Measure (PontryaginDual G) := μ.map e
  let : ν₀.IsHaarMeasure := e.isHaarMeasure_map μ
  let : ν₀.Regular := Measure.Regular.map e.toHomeomorph
  obtain ⟨ν, hν, -⟩ := lcaPlancherelMeasure_existsUnique μ
  let : ν.IsHaarMeasure := hν.1
  let : ν.Regular := hν.2.1
  let K : Set G := ℤₚ
  let f : G → ℂ := K.indicator (fun _ ↦ 1)
  have hK : MeasurableSet K := Metric.isClosed_closedBall.measurableSet
  have hKMass : μ K = 1 := hMass
  have hKFinite : μ K ≠ ⊤ := by rw [hKMass]; exact ENNReal.one_ne_top
  have hf₁ : Integrable f μ :=
    memLp_one_iff_integrable.mp (memLp_indicator_const 1 hK.nullMeasurableSet 1 (Or.inr hKFinite))
  have hf₂ : MemLp f 2 μ := memLp_indicator_const 2 hK.nullMeasurableSet 1 (Or.inr hKFinite)
  -- The unit ball indicator is fixed by Fourier transform in the pairing coordinates.
  have hFourier : lcaFourier μ f ∘ e = f := by
    have h := padicTamagawaFourier_scaledIntegers p 0
    simp only [zpow_zero, neg_zero, one_mul, image_id', one_smul] at h
    funext y
    change lcaFourier μ f (e y) = f y
    have hy := tamagawaFourier_eq_lcaFourier (padicTamagawaMeasure p)
      (padicStandardCharacter p) ((ℤₚ).indicator (fun _ ↦ (1 : ℂ))) y.toAdd (e y)
      (fun x ↦ (he y.toAdd x).trans (congrArg _ (mul_comm _ _)))
    exact hy.symm.trans (congrFun h y.toAdd)
  have hScale := Measure.isMulLeftInvariant_eq_smul_of_regular ν ν₀
  have hNorm := (hν.2.2 f hf₁ hf₂).2
  have hMeas : StronglyMeasurable (lcaFourier μ f) := by
    have hf : StronglyMeasurable f := stronglyMeasurable_const.indicator hK
    convert hf.comp_measurable e.symm.continuous.measurable using 1
    funext χ
    change lcaFourier μ f χ = f (e.symm χ)
    simpa only [Function.comp_apply, e.apply_symm_apply] using congrFun hFourier (e.symm χ)
  have hEmb : MeasurableEmbedding (e : G → PontryaginDual G) :=
    e.toHomeomorph.measurableEmbedding
  have hMap : eLpNorm (lcaFourier μ f) 2 ν₀ = eLpNorm f 2 μ := by
    exact (hEmb.eLpNorm_map_measure).trans (congrArg (fun g ↦ eLpNorm g 2 μ) hFourier)
  rw [hScale, eLpNorm_smul_measure_of_ne_top' (by simp : (2 : ℝ≥0∞) ≠ ⊤) _ _
      hMeas.aestronglyMeasurable, hMap] at hNorm
  have hfNorm : eLpNorm f 2 μ = 1 := by
    rw [eLpNorm_indicator_const hK.nullMeasurableSet (by simp) (by simp), hKMass]
    simp
  rw [hfNorm] at hNorm
  change (↑(ν.haarScalarFactor ν₀ ^ ((2 : ℝ≥0∞).toReal)⁻¹) : ℝ≥0∞) * 1 = 1 at hNorm
  rw [mul_one] at hNorm
  have hFactor : ν.haarScalarFactor ν₀ = 1 := by
    apply ENNReal.coe_injective
    apply (ENNReal.strictMono_rpow_of_pos (by norm_num : 0 < ((2 : ℝ≥0∞).toReal)⁻¹)).injective
    simpa [ENNReal.coe_rpow_of_nonneg] using hNorm
  rw [hFactor, one_smul] at hScale
  change IsLCAPlancherelMeasure μ ν₀
  exact hScale ▸ hν

end Padic

/-- Paper: Example A.3.1.8, p. 558. The rational adelic character multiplies the real
character and all the p-adic characters, only finitely many of which contribute. -/
def ratAdeleStandardCharacter (a : 𝔸[ℚ]) : Circle :=
  Circle.exp (2 * Real.pi * extensionEmbeddingOfIsReal Rat.isReal_infinitePlace
    (a.1 Rat.infinitePlace)) *
    ∏ᶠ v : Primes(ℚ),
      let p := Rat.HeightOneSpectrum.primesEquiv v
      letI : Fact p.val.Prime := ⟨p.property⟩
      padicStandardCharacter p.val (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v (a.2 v))

/-- Paper: Example A.3.1.8, p. 558. On an adele supported at the real place, the
global rational character takes the value of the standard real character. -/
theorem ratAdeleStandardCharacter_real (a : 𝔸[ℚ]) (ha : a.2 = 0) :
    ratAdeleStandardCharacter a =
      Circle.exp (2 * Real.pi * extensionEmbeddingOfIsReal Rat.isReal_infinitePlace
        (a.1 Rat.infinitePlace)) := by
  have h0 (q : ℕ) [Fact q.Prime] : padicStandardCharacter q 0 = 1 := by
    have hval (n : ℕ) (hn : n = 0) (x : ZMod (q ^ n)) : x.val = 0 := by
      subst hn
      exact Nat.lt_one_iff.mp (by simpa using x.val_lt)
    simp only [padicStandardCharacter]
    rw [hval _ (by simp) _]
    simp
  have h0' (v : Primes(ℚ)) : (0 : FiniteAdeleRing (𝓞 ℚ) ℚ) v = 0 := rfl
  rw [ratAdeleStandardCharacter, ha]
  simp [h0', h0]

/-- The local factor of the rational standard character at a finite place. -/
private def ratLocalStandardFactor (v : Primes(ℚ)) (x : v.adicCompletion ℚ) : Circle :=
  letI : Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).property⟩
  padicStandardCharacter (Rat.HeightOneSpectrum.primesEquiv v).val
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v x)

/-- The local factor is trivial on local integers. -/
private theorem ratLocalStandardFactor_eq_one (v : Primes(ℚ)) {x : v.adicCompletion ℚ}
    (hx : x ∈ v.adicCompletionIntegers ℚ) : ratLocalStandardFactor v x = 1 := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).property⟩
  exact padicStandardCharacter_eq_one_of_norm_le_one _
    ((Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn v).mapsTo hx)

/-- On a diagonal rational, the local factor is the p-adic character of that rational. -/
private theorem ratLocalStandardFactor_algebraMap (v : Primes(ℚ)) (q : ℚ) :
    ratLocalStandardFactor v ((algebraMap ℚ 𝔸[ℚ] q).2 v) =
      letI : Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime :=
        ⟨(Rat.HeightOneSpectrum.primesEquiv v).property⟩
      padicStandardCharacter (Rat.HeightOneSpectrum.primesEquiv v).val (q : ℚ_[_]) := by
  have h : (algebraMap ℚ 𝔸[ℚ] q).2 v = (q : v.adicCompletion ℚ) :=
    eq_ratCast (algebraMap ℚ (v.adicCompletion ℚ)) q
  simp only [ratLocalStandardFactor, h, map_ratCast]

/-- The rational standard character is the real exponential times the local factors. -/
private theorem ratAdeleStandardCharacter_eq_factors (a : 𝔸[ℚ]) :
    ratAdeleStandardCharacter a =
      Circle.exp (2 * Real.pi * extensionEmbeddingOfIsReal Rat.isReal_infinitePlace
        (a.1 Rat.infinitePlace)) * ∏ᶠ v : Primes(ℚ), ratLocalStandardFactor v (a.2 v) := rfl

/-- The rational standard character is additive. -/
private theorem ratAdeleStandardCharacter_add' (a b : 𝔸[ℚ]) :
    ratAdeleStandardCharacter (a + b) =
      ratAdeleStandardCharacter a * ratAdeleStandardCharacter b := by
  let f (x : 𝔸[ℚ]) (v : Primes(ℚ)) := ratLocalStandardFactor v (x.2 v)
  have hfinite (x : 𝔸[ℚ]) : (f x).HasFiniteMulSupport := by
    apply Filter.eventually_cofinite.mp
    filter_upwards [x.2.2] with v hv
    exact ratLocalStandardFactor_eq_one v hv
  have hsum : f (a + b) = f a * f b := by
    funext v
    let : Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv v).property⟩
    change padicStandardCharacter _ (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
        (a.2 v + b.2 v)) =
      padicStandardCharacter _ (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v (a.2 v)) *
        padicStandardCharacter _ (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v (b.2 v))
    rw [map_add, padicStandardCharacter_add]
  have hreal : extensionEmbeddingOfIsReal Rat.isReal_infinitePlace ((a + b).1 Rat.infinitePlace) =
      extensionEmbeddingOfIsReal Rat.isReal_infinitePlace (a.1 Rat.infinitePlace) +
        extensionEmbeddingOfIsReal Rat.isReal_infinitePlace (b.1 Rat.infinitePlace) :=
    map_add (extensionEmbeddingOfIsReal Rat.isReal_infinitePlace) _ _
  rw [ratAdeleStandardCharacter_eq_factors, ratAdeleStandardCharacter_eq_factors,
    ratAdeleStandardCharacter_eq_factors, hreal, mul_add, Circle.exp_add]
  change _ * (∏ᶠ v, f (a + b) v) = (_ * ∏ᶠ v, f a v) * (_ * ∏ᶠ v, f b v)
  rw [hsum]
  simp only [Pi.mul_apply, finprod_mul_distrib (hfinite a) (hfinite b)]
  ac_rfl

/-- The p-adic character of a reciprocal prime power is trivial away from that prime. -/
private theorem padicStandardCharacter_inv_prime_pow (l : ℕ) [Fact l.Prime] {p : ℕ}
    (hp : p.Prime) (k : ℕ) :
    padicStandardCharacter l (((1 / (p : ℚ) ^ k : ℚ)) : ℚ_[l]) =
      if l = p then Circle.exp (-(2 * Real.pi * (1 / (p : ℝ) ^ k))) else 1 := by
  split_ifs with hl
  · subst hl
    have := padicStandardCharacter_div_pow l 1 k
    simpa using this
  · apply padicStandardCharacter_eq_one_of_norm_le_one
    have hcop : ¬ (l : ℤ) ∣ (p : ℤ) := by
      rw [Int.natCast_dvd_natCast]
      exact fun h ↦ hl ((Nat.prime_dvd_prime_iff_eq (Fact.out) hp).mp h)
    have hnorm : ‖((p : ℚ) : ℚ_[l])‖ = 1 := by
      have h := le_antisymm (Padic.norm_int_le_one (p : ℤ))
        (not_lt.mp fun h ↦ hcop (Padic.norm_intCast_lt_one_iff.mp h))
      exact_mod_cast h
    rw [Rat.cast_div, Rat.cast_one, Rat.cast_pow, norm_div, norm_one, norm_pow, hnorm, one_pow,
      div_one]

/-- Paper: Example A.3.1.8, p. 558. The global rational character is trivial on the
diagonally embedded rational numbers. The paper uses this without stating it; it is what
Poisson summation over the rationals needs, and it fails for the signs as printed. -/
theorem ratAdeleStandardCharacter_algebraMap (q : ℚ) :
    ratAdeleStandardCharacter (algebraMap ℚ 𝔸[ℚ] q) = 1 := by
  classical
  -- The character restricted to the diagonal is a homomorphism from the rationals.
  let Ψ : Multiplicative ℚ →* Circle :=
    { toFun := fun x ↦ ratAdeleStandardCharacter (algebraMap ℚ 𝔸[ℚ] x.toAdd)
      map_one' := by
        have h := ratAdeleStandardCharacter_add' 0 0
        rw [add_zero] at h
        simpa using h
      map_mul' := fun x y ↦ by
        simp only [toAdd_mul, map_add]
        exact ratAdeleStandardCharacter_add' _ _ }
  have hΨ (x : ℚ) : Ψ (Multiplicative.ofAdd x) =
      ratAdeleStandardCharacter (algebraMap ℚ 𝔸[ℚ] x) := rfl
  have hreal (x : ℚ) : extensionEmbeddingOfIsReal Rat.isReal_infinitePlace
      ((algebraMap ℚ 𝔸[ℚ] x).1 Rat.infinitePlace) = x := by
    have h : (algebraMap ℚ 𝔸[ℚ] x).1 Rat.infinitePlace = (x : Rat.infinitePlace.Completion) :=
      eq_ratCast (algebraMap ℚ Rat.infinitePlace.Completion) x
    rw [h, map_ratCast]
  -- Integers.
  have hint (n : ℤ) : Ψ (Multiplicative.ofAdd (n : ℚ)) = 1 := by
    rw [hΨ, ratAdeleStandardCharacter_eq_factors, hreal]
    rw [finprod_eq_one_of_forall_eq_one fun v ↦ ?_, mul_one]
    · rw [Rat.cast_intCast, mul_comm]
      exact Circle.exp_int_mul_two_pi n
    · let : Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime :=
        ⟨(Rat.HeightOneSpectrum.primesEquiv v).property⟩
      rw [ratLocalStandardFactor_algebraMap]
      apply padicStandardCharacter_eq_one_of_norm_le_one
      rw [Rat.cast_intCast]
      exact Padic.norm_int_le_one n
  -- Reciprocal prime powers.
  have hprime (p : ℕ) (hp : p.Prime) (k : ℕ) :
      Ψ (Multiplicative.ofAdd (1 / (p : ℚ) ^ k)) = 1 := by
    let v₀ : Primes(ℚ) := Rat.HeightOneSpectrum.primesEquiv.symm ⟨p, hp⟩
    have hv₀ : (Rat.HeightOneSpectrum.primesEquiv v₀).val = p := by
      exact congrArg Subtype.val
        (Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply (⟨p, hp⟩ : Nat.Primes))
    rw [hΨ, ratAdeleStandardCharacter_eq_factors, hreal]
    rw [finprod_eq_single _ v₀ fun v hv ↦ ?_]
    · let : Fact (Rat.HeightOneSpectrum.primesEquiv v₀).val.Prime :=
        ⟨(Rat.HeightOneSpectrum.primesEquiv v₀).property⟩
      rw [ratLocalStandardFactor_algebraMap, padicStandardCharacter_inv_prime_pow _ hp]
      simp only [hv₀, ↓reduceIte]
      rw [← Circle.exp_add]
      push_cast
      rw [add_neg_cancel, Circle.exp_zero]
    · let : Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime :=
        ⟨(Rat.HeightOneSpectrum.primesEquiv v).property⟩
      have hne : (Rat.HeightOneSpectrum.primesEquiv v).val ≠ p := fun h ↦
        hv (Rat.HeightOneSpectrum.primesEquiv.injective (Subtype.ext (h.trans hv₀.symm)))
      rw [ratLocalStandardFactor_algebraMap, padicStandardCharacter_inv_prime_pow _ hp]
      simp only [hne, ↓reduceIte]
  -- Every rational with a given denominator, by induction on the denominator.
  have hden (b : ℕ) : ∀ a : ℤ, Ψ (Multiplicative.ofAdd ((a : ℚ) / b)) = 1 := by
    induction b using Nat.recOnPosPrimePosCoprime with
    | prime_pow p k hp hk =>
      intro a
      have h := congrArg (· ^ a) (hprime p hp k)
      simp only [one_zpow, ← map_zpow, ← ofAdd_zsmul, zsmul_eq_mul] at h
      rw [Nat.cast_pow, div_eq_mul_one_div]
      exact h
    | zero => intro a; simp
    | one => intro a; simpa using hint a
    | coprime m n hm hn hmn ihm ihn =>
      intro a
      obtain ⟨s, t, hst⟩ : ∃ s t : ℤ, s * m + t * n = 1 := by
        refine ⟨Nat.gcdA m n, Nat.gcdB m n, ?_⟩
        rw [mul_comm _ (m : ℤ), mul_comm _ (n : ℤ), ← Nat.gcd_eq_gcd_ab, hmn, Nat.cast_one]
      have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
      have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
      have hsplit : (a : ℚ) / ((m * n : ℕ) : ℚ) = ((a * t : ℤ) : ℚ) / m + ((a * s : ℤ) : ℚ) / n := by
        have hst' : (s : ℚ) * m + t * n = 1 := by exact_mod_cast hst
        rw [eq_comm, div_add_div _ _ hm0 hn0, div_eq_div_iff (mul_ne_zero hm0 hn0)
          (by push_cast; exact mul_ne_zero hm0 hn0)]
        push_cast
        linear_combination ((a : ℚ) * m * n) * hst'
      rw [hsplit, ofAdd_add, map_mul, ihm, ihn, one_mul]
  have hq := hden q.den q.num
  rwa [Rat.num_div_den] at hq

section RatAdeleSelfDuality

local instance : BorelSpace 𝔸[ℚ] := ⟨rfl⟩

/-- The real coordinate of a rational adele in the unique real completion. -/
private def ratRealPart (a : 𝔸[ℚ]) : ℝ :=
  extensionEmbeddingOfIsReal Rat.isReal_infinitePlace (a.1 Rat.infinitePlace)

local notation "ratIntegralAdeles" => (integralAdelesOutside ℚ ∅ : Set 𝔸[ℚ])

open scoped IsDedekindDomain.FiniteAdeleRing RestrictedProduct in
/-- The adeles integral at every finite place form an open subring. -/
private theorem isOpen_ratIntegralAdeles : IsOpen ratIntegralAdeles := by
  simp only [integralAdelesOutside, Subring.coe_iInf, Set.iInter_ofPred, Finset.notMem_empty,
    not_false_eq_true, true_implies]
  exact (RestrictedProduct.isOpen_forall_mem (fun v : Primes(ℚ) ↦
    Valued.isOpen_integer (v.adicCompletion ℚ))).preimage continuous_snd

/-- Projecting the restriction to integral finite components onto the real coordinate
gives Lebesgue measure. The finite integral factors have product mass one. -/
private theorem ratTamagawaMeasurePreserving_realPart :
    MeasurePreserving ratRealPart ((additiveTamagawaMeasure ℚ).restrict ratIntegralAdeles)
      (volume : Measure ℝ) := by
  let t : InfiniteAdeleRing ℚ → ℝ := fun a ↦
    extensionEmbeddingOfIsReal Rat.isReal_infinitePlace (a Rat.infinitePlace)
  have ht : Continuous t :=
    (isometryEquivRealOfIsReal Rat.isReal_infinitePlace).continuous.comp (continuous_apply _)
  let μ := infiniteLocalAdditiveTamagawaMeasure ℚ
  let : Unique (InfinitePlace ℚ) := ⟨⟨Rat.infinitePlace⟩, fun _ ↦ Subsingleton.elim _ _⟩
  let (v : InfinitePlace ℚ) : BorelSpace v.Completion := ⟨rfl⟩
  let (v : InfinitePlace ℚ) : SecondCountableTopology v.Completion :=
    (isometry_extensionEmbedding v).isEmbedding.secondCountableTopology
  let : BorelSpace (InfiniteAdeleRing ℚ) :=
    inferInstanceAs (BorelSpace ((v : InfinitePlace ℚ) → v.Completion))
  let e := (isometryEquivRealOfIsReal Rat.isReal_infinitePlace).toHomeomorph.toMeasurableEquiv
  have he : MeasurePreserving e (μ Rat.infinitePlace) volume := by
    refine ⟨e.measurable, ?_⟩
    change (infiniteLocalAdditiveTamagawaMeasure ℚ Rat.infinitePlace).map e = _
    rw [infiniteLocalAdditiveTamagawaMeasure, dite_eq_left Rat.isReal_infinitePlace]
    change (Measure.map e.symm volume).map e = _
    rw [Measure.map_map e.measurable e.symm.measurable, e.self_comp_symm, Measure.map_id]
  have hπ : MeasurePreserving t (Measure.pi μ) volume :=
    he.comp (measurePreserving_piUnique μ)
  have hm : Measurable ratRealPart :=
    Continuous.measurable (α := 𝔸[ℚ]) (ht.comp continuous_fst)
  refine ⟨hm, Measure.ext fun B hB ↦ ?_⟩
  rw [Measure.map_apply hm hB, Measure.restrict_apply (hm hB)]
  have hset : ratRealPart ⁻¹' B ∩ ratIntegralAdeles =
      {a : 𝔸[ℚ] | a.1 ∈ t ⁻¹' B ∧
        (∀ v : (∅ : Finset (Primes(ℚ))), a.2 v.val ∈ (Set.univ : Set (v.val.adicCompletion ℚ))) ∧
        a ∈ integralAdelesOutside ℚ ∅} := by
    ext a
    simp [t, ratRealPart]
  rw [hset, additiveTamagawaMeasure_restrictedProduct ℚ ∅ _ (ht.measurable hB) _
    (fun _ ↦ MeasurableSet.univ)]
  have htail : (∏ᶠ v : {v : Primes(ℚ) // v ∉ (∅ : Finset (Primes(ℚ)))},
      differentMass(ℚ, v.val)) = 1 := by
    rw [finprod_subtype_eq_finprod_cond (f := fun v : Primes(ℚ) ↦ differentMass(ℚ, v))
      (fun v ↦ v ∉ (∅ : Finset (Primes(ℚ))))]
    simp only [Finset.notMem_empty, not_false_eq_true, finprod_true,
      finiteLocalTamagawaMass_finprod]
    simp
  simp only [htail, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
  exact hπ.measure_preimage hB.nullMeasurableSet

/-- Paper: Example A.3.1.8, p. 558. The adelic Gaussian is the real Gaussian times
the indicator of the adeles integral at every finite place. -/
private def ratAdeleGaussian : 𝔸[ℚ] → ℂ :=
  Set.indicator ratIntegralAdeles (fun a ↦ (Real.exp (-Real.pi * (ratRealPart a) ^ 2) : ℂ))

/-- The adelic Gaussian is integrable and square-integrable. -/
private theorem ratAdeleGaussian_integrable_memLp :
    Integrable ratAdeleGaussian (additiveTamagawaMeasure ℚ) ∧
      MemLp ratAdeleGaussian 2 (additiveTamagawaMeasure ℚ) := by
  let g : ℝ → ℂ := fun x ↦ (Real.exp (-Real.pi * x ^ 2) : ℂ)
  have hg : Integrable g volume := (integrable_exp_neg_mul_sq Real.pi_pos).ofReal
  have hg₂ : MemLp g 2 volume := by
    apply (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).2
    convert integrable_exp_neg_mul_sq (b := 2 * Real.pi) (by positivity) using 1
    funext x
    dsimp [g]
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, ← Real.exp_nat_mul]
    push_cast
    congr 1
    ring
  have hI := isOpen_ratIntegralAdeles.measurableSet
  exact ⟨(integrable_indicator_iff hI).2
    (ratTamagawaMeasurePreserving_realPart.integrable_comp_of_integrable hg),
    (memLp_indicator_iff_restrict hI.nullMeasurableSet).2
      (hg₂.comp_measurePreserving ratTamagawaMeasurePreserving_realPart)⟩

/-- The standard character on the completion at a finite rational place. -/
private def ratLocalCharacter (v : Primes(ℚ)) (x : v.adicCompletion ℚ) : Circle :=
  let p := Rat.HeightOneSpectrum.primesEquiv v
  letI : Fact p.val.Prime := ⟨p.property⟩
  padicStandardCharacter p.val (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v x)

/-- At each finite rational place, the local character has kernel the local integers. -/
private theorem ratLocalCharacter_eq_one (v : Primes(ℚ)) (x : v.adicCompletion ℚ) :
    ratLocalCharacter v x = 1 ↔ x ∈ v.adicCompletionIntegers ℚ := by
  let p := Rat.HeightOneSpectrum.primesEquiv v
  let : Fact p.val.Prime := ⟨p.property⟩
  let e := Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
  change padicStandardCharacter p.val (e x) = 1 ↔ _
  rw [padicStandardCharacter_eq_one_iff]
  have h := Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn v
  refine ⟨fun hx ↦ ?_, fun hx ↦ h.mapsTo hx⟩
  obtain ⟨z, hz, he⟩ := h.surjOn hx
  exact e.injective he ▸ hz

/-- Membership in the integral subring amounts to integrality in each finite coordinate. -/
private theorem mem_ratIntegralAdeles (a : 𝔸[ℚ]) :
    a ∈ ratIntegralAdeles ↔ ∀ v : Primes(ℚ), a.2 v ∈ v.adicCompletionIntegers ℚ := by
  change a ∈ integralAdelesOutside ℚ ∅ ↔ _
  simp only [integralAdelesOutside, Subring.mem_iInf, Finset.notMem_empty, not_false_eq_true,
    true_implies]
  rfl

/-- On integral finite components the global character is its real factor. -/
private theorem ratAdeleStandardCharacter_of_integral (a : 𝔸[ℚ]) (ha : a ∈ ratIntegralAdeles) :
    ratAdeleStandardCharacter a = Circle.exp (2 * Real.pi * ratRealPart a) := by
  change Circle.exp (2 * Real.pi * ratRealPart a) *
    (∏ᶠ v : Primes(ℚ), ratLocalCharacter v (a.2 v)) = _
  rw [finprod_eq_one_of_forall_eq_one (fun v ↦
    (ratLocalCharacter_eq_one v (a.2 v)).2 ((mem_ratIntegralAdeles a).1 ha v)), mul_one]

/-- The global character is multiplicative on sums of rational adeles. -/
private theorem ratAdeleStandardCharacter_add (a b : 𝔸[ℚ]) :
    ratAdeleStandardCharacter (a + b) =
      ratAdeleStandardCharacter a * ratAdeleStandardCharacter b := by
  let f (x : 𝔸[ℚ]) (v : Primes(ℚ)) := ratLocalCharacter v (x.2 v)
  have hfinite (x : 𝔸[ℚ]) : (f x).HasFiniteMulSupport := by
    apply Filter.eventually_cofinite.mp
    filter_upwards [x.2.2] with v hv
    exact (ratLocalCharacter_eq_one v _).2 hv
  have hsum : f (a + b) = f a * f b := by
    funext v
    let p := Rat.HeightOneSpectrum.primesEquiv v
    let : Fact p.val.Prime := ⟨p.property⟩
    let e := Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
    change padicStandardCharacter p.val (e (a.2 v + b.2 v)) =
      padicStandardCharacter p.val (e (a.2 v)) * padicStandardCharacter p.val (e (b.2 v))
    rw [map_add, padicStandardCharacter_add]
  have hreal : ratRealPart (a + b) = ratRealPart a + ratRealPart b :=
    map_add (extensionEmbeddingOfIsReal Rat.isReal_infinitePlace) _ _
  change Circle.exp (2 * Real.pi * ratRealPart (a + b)) * (∏ᶠ v, f (a + b) v) =
    (Circle.exp (2 * Real.pi * ratRealPart a) * (∏ᶠ v, f a v)) *
      (Circle.exp (2 * Real.pi * ratRealPart b) * (∏ᶠ v, f b v))
  rw [hreal, mul_add, Circle.exp_add, hsum]
  simp only [Pi.mul_apply, finprod_mul_distrib (hfinite a) (hfinite b)]
  ac_rfl

open scoped IsDedekindDomain.FiniteAdeleRing RestrictedProduct in
/-- A frequency with a nonintegral finite component gives a nontrivial character
on some integral adele supported at one finite place. -/
private theorem exists_ratIntegralAdeles_character_ne_one (y : 𝔸[ℚ]) (hy : y ∉ ratIntegralAdeles) :
    ∃ b : 𝔸[ℚ], b ∈ ratIntegralAdeles ∧ b.1 = 0 ∧ ratAdeleStandardCharacter (b * y) ≠ 1 := by
  classical
  rw [mem_ratIntegralAdeles, not_forall] at hy
  obtain ⟨v, hv⟩ := hy
  let O := fun w : Primes(ℚ) ↦ w.adicCompletionIntegers ℚ
  let b : 𝔸[ℚ] := (0, RestrictedProduct.single O v 1)
  refine ⟨b, (mem_ratIntegralAdeles b).2 ?_, rfl, ?_⟩
  · intro w
    change RestrictedProduct.single O v 1 w ∈ O w
    by_cases hw : w = v
    · subst w
      rw [RestrictedProduct.single_eq_same]
      exact (O v).one_mem
    · rw [RestrictedProduct.single_eq_of_ne O _ hw]
      exact (O w).zero_mem
  have hval : ratAdeleStandardCharacter (b * y) = ratLocalCharacter v (y.2 v) := by
    change Circle.exp (2 * Real.pi * ratRealPart (b * y)) *
      (∏ᶠ w : Primes(ℚ), ratLocalCharacter w (RestrictedProduct.single O v 1 w * y.2 w)) = _
    have hz : ratRealPart (b * y) = 0 := by
      change extensionEmbeddingOfIsReal Rat.isReal_infinitePlace
        ((0 : Rat.infinitePlace.Completion) * y.1 Rat.infinitePlace) = 0
      rw [zero_mul, map_zero]
    rw [hz, mul_zero, Circle.exp_zero, one_mul, finprod_eq_single _ v]
    · rw [RestrictedProduct.single_eq_same, one_mul]
    · intro w hw
      rw [RestrictedProduct.single_eq_of_ne O _ hw, zero_mul]
      exact (ratLocalCharacter_eq_one w 0).2 (O w).zero_mem
  rw [hval]
  exact fun h ↦ hv ((ratLocalCharacter_eq_one v _).1 h)

open scoped FourierTransform in
/-- Paper: Example A.3.1.8, p. 558. The real Gaussian times the indicator of the
integral finite adeles is fixed by the rational adelic Fourier transform. -/
private theorem tamagawaFourier_ratAdeleGaussian :
    tamagawaFourier (additiveTamagawaMeasure ℚ) ratAdeleStandardCharacter ratAdeleGaussian =
      ratAdeleGaussian := by
  funext y
  let I := integralAdelesOutside ℚ ∅
  let μ := additiveTamagawaMeasure ℚ
  by_cases hy : y ∈ I
  · let g : ℝ → ℂ := fun t ↦ (Real.exp (-Real.pi * t ^ 2) : ℂ)
    let k : ℝ → ℂ := fun t ↦
      g t * star (Circle.exp (2 * Real.pi * (t * ratRealPart y)) : ℂ)
    have hK : AEStronglyMeasurable k (volume : Measure ℝ) := by
      apply Continuous.aestronglyMeasurable
      dsimp [k, g]
      fun_prop
    have hIntegrand (x : 𝔸[ℚ]) :
        ratAdeleGaussian x * star (ratAdeleStandardCharacter (x * y) : ℂ) =
          (I : Set 𝔸[ℚ]).indicator (k ∘ ratRealPart) x := by
      by_cases hx : x ∈ I
      · rw [ratAdeleGaussian, indicator_of_mem hx, indicator_of_mem hx,
          ratAdeleStandardCharacter_of_integral _ (I.mul_mem hx hy)]
        have hmul : ratRealPart (x * y) = ratRealPart x * ratRealPart y :=
          map_mul (extensionEmbeddingOfIsReal Rat.isReal_infinitePlace) _ _
        rw [hmul]
        rfl
      · rw [ratAdeleGaussian, indicator_of_notMem hx, indicator_of_notMem hx, zero_mul]
    rw [tamagawaFourier]
    simp_rw [hIntegrand]
    rw [integral_indicator isOpen_ratIntegralAdeles.measurableSet]
    have hMap := integral_map ratTamagawaMeasurePreserving_realPart.measurable.aemeasurable
      (f := k) (ratTamagawaMeasurePreserving_realPart.map_eq.symm ▸ hK)
    rw [ratTamagawaMeasurePreserving_realPart.map_eq] at hMap
    change (∫ x, k (ratRealPart x) ∂μ.restrict I) = ratAdeleGaussian y
    rw [← hMap]
    have hFourier : (∫ t, k t) = 𝓕 g (ratRealPart y) := by
      rw [Real.fourier_eq]
      congr 1
      funext t
      dsimp only [k]
      rw [← Real.fourierChar_apply', Circle.star_addChar, Real.inner_apply,
        Circle.smul_def, smul_eq_mul, mul_comm t (ratRealPart y), mul_comm (g t)]
    have hg : 𝓕 g = g := by
      have hg' : (fun t : ℝ ↦ Complex.exp (-(Real.pi : ℂ) * 1 * (t : ℂ) ^ 2)) = g := by
        funext t
        dsimp only [g]
        rw [Complex.ofReal_exp]
        push_cast
        rw [mul_one]
      rw [← hg']
      simpa using fourier_gaussian_pi (b := (1 : ℂ)) (by norm_num)
    rw [hFourier, hg]
    rw [ratAdeleGaussian, indicator_of_mem hy]
  · obtain ⟨b, hb, hreal, hchar⟩ := exists_ratIntegralAdeles_character_ne_one y hy
    let h : 𝔸[ℚ] → ℂ := fun x ↦ ratAdeleGaussian x *
      star (ratAdeleStandardCharacter (x * y) : ℂ)
    have hμ : μ.IsAddHaarMeasure := (additiveTamagawaMeasure_existsUnique ℚ).exists.choose_spec.1
    have htranslate (x : 𝔸[ℚ]) :
        h (b + x) = h x * star (ratAdeleStandardCharacter (b * y) : ℂ) := by
      have hI : b + x ∈ I ↔ x ∈ I := ⟨fun hx ↦ by
        simpa only [add_comm b x, add_sub_cancel_right] using I.sub_mem hx hb, I.add_mem hb⟩
      have hg : ratAdeleGaussian (b + x) = ratAdeleGaussian x := by
        have hx : ratRealPart (b + x) = ratRealPart x := by
          change extensionEmbeddingOfIsReal Rat.isReal_infinitePlace
            (b.1 Rat.infinitePlace + x.1 Rat.infinitePlace) = _
          rw [hreal, Pi.zero_apply, zero_add]
          rfl
        unfold ratAdeleGaussian
        by_cases hmem : x ∈ I
        · rw [indicator_of_mem (hI.2 hmem), indicator_of_mem hmem, hx]
        · rw [indicator_of_notMem (hI.not.2 hmem), indicator_of_notMem hmem]
      simp only [h, hg, add_mul, ratAdeleStandardCharacter_add, Circle.coe_mul, star_mul']
      ring
    have hJ : (∫ x, h x ∂μ) =
        (∫ x, h x ∂μ) * star (ratAdeleStandardCharacter (b * y) : ℂ) := by
      rw [← integral_mul_const]
      simp_rw [← htranslate]
      exact (integral_add_left_eq_self h b).symm
    have hne : star (ratAdeleStandardCharacter (b * y) : ℂ) ≠ 1 := by
      intro hc
      apply hchar
      apply Circle.coe_injective
      rw [Circle.coe_one]
      exact star_injective (hc.trans (star_one ℂ).symm)
    change (∫ x, h x ∂μ) = ratAdeleGaussian y
    rw [ratAdeleGaussian, indicator_of_notMem hy]
    by_contra hn
    exact hne (mul_left_cancel₀ hn (hJ.symm.trans (mul_one _).symm))

/-- Multiplication followed by the rational adelic character gives a continuous pairing. -/
private def ratAdelePairing :
    Multiplicative 𝔸[ℚ] →ₜ* PontryaginDual (Multiplicative 𝔸[ℚ]) := by
  let G := Multiplicative 𝔸[ℚ]
  let ψ : G →* Circle :=
    { toFun := fun x ↦ ratAdeleStandardCharacter x.toAdd
      map_one' := by
        change ratAdeleStandardCharacter 0 = 1
        simpa only [map_zero] using ratAdeleStandardCharacter_algebraMap 0
      map_mul' := fun _ _ ↦ ratAdeleStandardCharacter_add _ _ }
  have hψ : Continuous ψ := by
    apply continuous_of_continuousAt_one
    change ContinuousAt ratAdeleStandardCharacter 0
    have hr : Continuous ratRealPart :=
      (isometryEquivRealOfIsReal Rat.isReal_infinitePlace).continuous.comp
        ((continuous_apply _).comp continuous_fst)
    apply (Circle.exp.continuous.comp (continuous_const.mul hr)).continuousAt.congr_of_eventuallyEq
    filter_upwards [isOpen_ratIntegralAdeles.mem_nhds (integralAdelesOutside ℚ ∅).zero_mem] with x hx
    exact ratAdeleStandardCharacter_of_integral x hx
  let χ (x : G) : PontryaginDual G :=
    ⟨ψ.comp (AddMonoidHom.mulLeft x.toAdd).toMultiplicative,
      hψ.comp (show Continuous (fun y : 𝔸[ℚ] ↦ x.toAdd * y) from continuous_const.mul continuous_id)⟩
  refine
    { toFun := χ
      map_one' := PontryaginDual.ext (fun y ↦ ?_)
      map_mul' := fun x y ↦ PontryaginDual.ext (fun z ↦ ?_)
      continuous_toFun := ContinuousMonoidHom.continuous_of_continuous_uncurry χ (hψ.comp
        (show Continuous (fun p : 𝔸[ℚ] × 𝔸[ℚ] ↦ p.1 * p.2) from continuous_mul)) }
  · change ratAdeleStandardCharacter (0 * y.toAdd) = 1
    rw [zero_mul]
    exact map_one ψ
  · change ratAdeleStandardCharacter ((x.toAdd + y.toAdd) * z.toAdd) = _
    rw [add_mul, ratAdeleStandardCharacter_add]
    rfl

/-- A symmetric nondegenerate pairing has dense image by Pontryagin biduality. -/
private theorem denseRange_of_symmetric_pairing {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (e : G →ₜ* PontryaginDual G) (hsymm : ∀ x y, e x y = e y x)
    (hker : ∀ x, e x = 1 → x = 1) : DenseRange e := by
  let H := e.toMonoidHom.range.topologicalClosure
  let : T1Space (PontryaginDual G ⧸ H) := QuotientGroup.t1Space_iff.mpr
    e.toMonoidHom.range.isClosed_topologicalClosure
  let q : PontryaginDual G →ₜ* (PontryaginDual G ⧸ H) :=
    ⟨QuotientGroup.mk' H, QuotientGroup.continuous_mk⟩
  obtain ⟨b, hb⟩ := pontryaginDual_bidual (G := G)
  intro χ
  change χ ∈ H
  apply (QuotientGroup.eq_one_iff _).mp
  apply (pontryaginDual_pairing_separates (G := PontryaginDual G ⧸ H)).1
  funext η
  let x := b.symm (PontryaginDual.map q η)
  have hx (γ : PontryaginDual G) : η (q γ) = γ x := by
    rw [← hb, show b x = PontryaginDual.map q η from b.apply_symm_apply _]
    rfl
  have hx1 : e x = 1 := by
    refine PontryaginDual.ext fun y ↦ (hsymm x y).trans ((hx (e y)).symm.trans ?_)
    have hy : q (e y) = 1 := (QuotientGroup.eq_one_iff _).mpr
      (e.toMonoidHom.range.le_topologicalClosure ⟨y, rfl⟩)
    rw [hy, map_one]
    rfl
  change η (q χ) = η 1
  rw [hx, hker x hx1, map_one, map_one]

/-- The Gaussian superlevel set above `exp (-π)` lies in the product of the local unit balls.
This compact box contains no nonzero ideal of the adele ring. -/
private theorem ratAdeleGaussian_compact_test :
    ∃ K : Set 𝔸[ℚ], IsCompact K ∧
      (∀ x, Real.exp (-Real.pi) < ‖ratAdeleGaussian x‖ → x ∈ K) ∧
      ∀ x : 𝔸[ℚ], (∀ a, a * x ∈ K) → x = 0 := by
  let arch := univ.pi (fun v : InfinitePlace ℚ ↦ Metric.closedBall (0 : v.Completion) 1)
  let K : Set 𝔸[ℚ] := arch ×ˢ integralFiniteAdeles ℚ
  have hc : IsCompact arch := by
    apply isCompact_univ_pi
    intro v
    obtain rfl := Subsingleton.elim v Rat.infinitePlace
    let e := isometryEquivRealOfIsReal Rat.isReal_infinitePlace
    apply e.isometry.isEmbedding.isCompact_iff.mpr
    rw [e.image_closedBall]
    exact isCompact_closedBall _ _
  refine ⟨K, hc.prod (finiteAdeleInteger_isCompact ℚ), ?_, ?_⟩
  · intro x hx
    by_cases hi : x ∈ ratIntegralAdeles
    · rw [ratAdeleGaussian, indicator_of_mem hi, Complex.norm_real,
        Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_lt_exp] at hx
      refine ⟨fun v _ ↦ ?_, (mem_ratIntegralAdeles x).mp hi⟩
      obtain rfl := Subsingleton.elim v Rat.infinitePlace
      rw [Metric.mem_closedBall, dist_zero_right, ← (isometry_extensionEmbeddingOfIsReal
        Rat.isReal_infinitePlace).norm_map_of_map_zero (map_zero _) _, Real.norm_eq_abs]
      change |ratRealPart x| ≤ 1
      have hs : (ratRealPart x) ^ 2 < 1 :=
        (mul_lt_mul_left_of_neg (neg_lt_zero.mpr Real.pi_pos)).mp (by simpa using hx)
      exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
    · rw [ratAdeleGaussian, indicator_of_notMem hi, norm_zero] at hx
      exact (not_lt_of_ge (Real.exp_pos _).le hx).elim
  · intro x hx
    apply Prod.ext
    · funext v
      by_contra hn
      have hne : x.1 v ≠ 0 := hn
      let a : 𝔸[ℚ] := (fun w ↦ 2 / x.1 w, 0)
      have h := (hx a).1 v (mem_univ _)
      change dist (2 / x.1 v * x.1 v) 0 ≤ 1 at h
      rw [div_mul_cancel₀ _ hne, dist_zero_right] at h
      obtain rfl := Subsingleton.elim v Rat.infinitePlace
      rw [← (isometry_extensionEmbeddingOfIsReal Rat.isReal_infinitePlace).norm_map_of_map_zero
        (map_zero _) _, map_ofNat] at h
      norm_num at h
    · apply finiteAdele_eq_zero_of_forall_nat_mul ℚ
      intro n hn
      let d := algebraMap ℚ 𝔸[ℚ]
      let a := d (n : ℚ)⁻¹
      refine ⟨(a * x).2, (mem_finiteIntegralAdeles_iff ℚ _).mpr (hx a).2, ?_⟩
      have he : x = (n : 𝔸[ℚ]) * (a * x) := by
        rw [← mul_assoc, ← map_natCast d, ← map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hn),
          map_one, one_mul]
      exact congrArg Prod.snd he

open scoped IsDedekindDomain.FiniteAdeleRing RestrictedProduct in
/-- Paper: Example A.3.1.8, p. 558. The product character pairing identifies
the additive rational adeles with their Pontryagin dual as topological groups.
The local integer rings are their own annihilators for the finite-place pairings. -/
theorem exists_ratAdeleDualEquiv :
    ∃ e : Multiplicative 𝔸[ℚ] ≃ₜ* PontryaginDual (Multiplicative 𝔸[ℚ]),
      ∀ x y : 𝔸[ℚ], e (Multiplicative.ofAdd x) (Multiplicative.ofAdd y) =
        ratAdeleStandardCharacter (x * y) := by
  let G := Multiplicative 𝔸[ℚ]
  let e := ratAdelePairing
  let (v : Primes(ℚ)) : CompactSpace (v.adicCompletionIntegers ℚ) :=
    compactSpace_adicCompletionIntegers v
  let : Fact (∀ v : Primes(ℚ), IsOpen (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))) :=
    ⟨fun v ↦ Valued.isOpen_valuationSubring _⟩
  let : LocallyCompactSpace G := by
    change LocallyCompactSpace (InfiniteAdeleRing ℚ ×
      (Πʳ v : Primes(ℚ), [v.adicCompletion ℚ, v.adicCompletionIntegers ℚ]))
    infer_instance
  let : T2Space G := by
    change T2Space (((v : InfinitePlace ℚ) → v.Completion) ×
      (Πʳ v : Primes(ℚ), [v.adicCompletion ℚ, v.adicCompletionIntegers ℚ]))
    infer_instance
  let : SigmaCompactSpace G := adeleHaar_sigmaCompactSpace ℚ
  let : BorelSpace G := ⟨rfl⟩
  let μ : Measure G := additiveTamagawaMeasure ℚ
  have hμ := (additiveTamagawaMeasure_existsUnique ℚ).exists.choose_spec
  let : μ.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := hμ.1.toIsFiniteMeasureOnCompacts
      toIsOpenPosMeasure := hμ.1.toIsOpenPosMeasure
      map_mul_left_eq_self := fun x ↦ hμ.1.map_add_left_eq_self x.toAdd }
  let : μ.Regular := hμ.2.1
  obtain ⟨f, hf⟩ := lcaFourier_zeroAtInfty (G := G) μ
    (f := fun x ↦ ratAdeleGaussian x.toAdd) ratAdeleGaussian_integrable_memLp.1
  have hfe (x : G) : f (e x) = ratAdeleGaussian x.toAdd := by
    calc
      f (e x) = lcaFourier μ (fun z ↦ ratAdeleGaussian z.toAdd) (e x) := hf _
      _ = tamagawaFourier (additiveTamagawaMeasure ℚ) ratAdeleStandardCharacter
          ratAdeleGaussian x.toAdd := (tamagawaFourier_eq_lcaFourier _ _ _ _ _ (fun y ↦
            congrArg ratAdeleStandardCharacter (mul_comm x.toAdd y))).symm
      _ = ratAdeleGaussian x.toAdd := congrFun tamagawaFourier_ratAdeleGaussian x.toAdd
  let V := {χ : PontryaginDual G | Real.exp (-Real.pi) < ‖f χ‖}
  have hV : IsOpen V := isOpen_lt continuous_const f.continuous.norm
  have h1 : 1 ∈ V := by
    change Real.exp (-Real.pi) < ‖f 1‖
    rw [← map_one e, hfe]
    change Real.exp (-Real.pi) < ‖ratAdeleGaussian 0‖
    have hr : ratRealPart 0 = 0 := map_zero (extensionEmbeddingOfIsReal Rat.isReal_infinitePlace)
    have hg : ratAdeleGaussian 0 = 1 := by
      simp [ratAdeleGaussian, (integralAdelesOutside ℚ ∅).zero_mem, hr]
    rw [hg, norm_one]
    exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr Real.pi_pos)
  obtain ⟨K, hK, hbox, htriv⟩ := ratAdeleGaussian_compact_test
  have hpre (x : G) (hx : e x ∈ V) : x.toAdd ∈ K :=
    hbox _ (hfe x ▸ hx : Real.exp (-Real.pi) < ‖ratAdeleGaussian x.toAdd‖)
  -- The kernel is an ideal, and the only ideal contained in the compact box is zero.
  have hker (x : G) (hx : e x = 1) : x = 1 := by
    apply htriv x.toAdd
    intro a
    apply hpre (Multiplicative.ofAdd (a * x.toAdd))
    have he : e (Multiplicative.ofAdd (a * x.toAdd)) = 1 := by
      apply PontryaginDual.ext
      intro y
      have hz := DFunLike.congr_fun hx (Multiplicative.ofAdd (a * y.toAdd))
      change ratAdeleStandardCharacter ((a * x.toAdd) * y.toAdd) = 1
      rw [mul_comm a x.toAdd, mul_assoc]
      exact hz
    exact he ▸ h1
  have hdense := denseRange_of_symmetric_pairing e
    (fun x y ↦ congrArg ratAdeleStandardCharacter (mul_comm x.toAdd y.toAdd)) hker
  -- On V the dense image is contained in the closed image of K.
  let H := e.toMonoidHom.range
  have hclosed : IsClosed (e '' (K : Set G)) := (hK.image e.continuous).isClosed
  have hsub : V ∩ range e ⊆ e '' (K : Set G) := by
    rintro _ ⟨hx, x, rfl⟩
    exact ⟨x, hpre x hx, rfl⟩
  have hVsub : V ⊆ (H : Set (PontryaginDual G)) :=
    ((hdense.open_subset_closure_inter hV).trans (closure_minimal hsub hclosed)).trans
      (image_subset_range ..)
  have hopen := H.isOpen_of_mem_nhds (Filter.mem_of_superset (hV.mem_nhds h1) hVsub)
  have hsurj : Surjective e := by
    intro χ
    change χ ∈ (H : Set (PontryaginDual G))
    rw [← (H.isClosed_of_isOpen hopen).closure_eq]
    exact hdense χ
  let equiv := MulEquiv.ofBijective e.toMonoidHom ⟨(injective_iff_map_eq_one e).mpr hker, hsurj⟩
  let E : G ≃ₜ* PontryaginDual G :=
    { equiv with
      continuous_toFun := e.continuous
      continuous_invFun := equiv.toEquiv.continuous_symm_iff.mpr
        (e.toMonoidHom.isOpenMap_of_sigmaCompact hsurj e.continuous) }
  exact ⟨E, fun _ _ ↦ rfl⟩

open scoped IsDedekindDomain.FiniteAdeleRing RestrictedProduct in
/-- Paper: Example A.3.1.8, p. 558. The additive Tamagawa measure on the rational
adeles is self-dual under the product of the standard local characters. -/
theorem ratAdditiveTamagawaMeasure_selfDual :
    IsTamagawaSelfDual (additiveTamagawaMeasure ℚ) ratAdeleStandardCharacter := by
  obtain ⟨e, he⟩ := exists_ratAdeleDualEquiv
  refine ⟨e, he, ?_⟩
  let G := Multiplicative 𝔸[ℚ]
  let μ : Measure G := additiveTamagawaMeasure ℚ
  let (v : Primes(ℚ)) : CompactSpace (v.adicCompletionIntegers ℚ) :=
    compactSpace_adicCompletionIntegers v
  let : Fact (∀ v : Primes(ℚ), IsOpen (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))) :=
    ⟨fun v ↦ Valued.isOpen_valuationSubring _⟩
  let : LocallyCompactSpace G := by
    change LocallyCompactSpace (InfiniteAdeleRing ℚ ×
      (Πʳ v : Primes(ℚ), [v.adicCompletion ℚ, v.adicCompletionIntegers ℚ]))
    infer_instance
  let : T2Space G := by
    change T2Space (((v : InfinitePlace ℚ) → v.Completion) ×
      (Πʳ v : Primes(ℚ), [v.adicCompletion ℚ, v.adicCompletionIntegers ℚ]))
    infer_instance
  let : BorelSpace G := ⟨rfl⟩
  let : MeasurableSpace (PontryaginDual G) := borel _
  let : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  have hμ := (additiveTamagawaMeasure_existsUnique ℚ).exists.choose_spec
  let : μ.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := hμ.1.toIsFiniteMeasureOnCompacts
      toIsOpenPosMeasure := hμ.1.toIsOpenPosMeasure
      map_mul_left_eq_self := fun x ↦ hμ.1.map_add_left_eq_self x.toAdd }
  let : μ.Regular := hμ.2.1
  obtain ⟨ν, hν, _⟩ := lcaPlancherelMeasure_existsUnique μ
  let : ν.IsHaarMeasure := hν.1
  let : ν.Regular := hν.2.1
  let η := μ.map e.toHomeomorph
  let : η.IsHaarMeasure := e.isHaarMeasure_map μ
  let : η.Regular := Measure.Regular.map e.toHomeomorph
  let c := ν.haarScalarFactor η
  have hc : ν = c • η := Measure.isMulLeftInvariant_eq_smul_of_regular ν η
  let f : G → ℂ := fun x ↦ ratAdeleGaussian x.toAdd
  obtain ⟨hf₁, hf₂⟩ := ratAdeleGaussian_integrable_memLp
  have hFourier : lcaFourier μ f ∘ e.toHomeomorph = f := by
    funext x
    have hx := congrFun tamagawaFourier_ratAdeleGaussian x.toAdd
    rw [tamagawaFourier_eq_lcaFourier _ _ _ _ _ (fun y ↦ by
      rw [he x.toAdd y, mul_comm])] at hx
    exact hx
  have hnorm : eLpNorm f 2 μ ≠ 0 := by
    intro hzero
    have hae := (eLpNorm_eq_zero_iff (by norm_num : (2 : ℝ≥0∞) ≠ 0)).1 hzero
    have hI : IsClopen ratIntegralAdeles :=
      ⟨(integralAdelesOutside ℚ ∅).toAddSubgroup.isClosed_of_isOpen isOpen_ratIntegralAdeles,
        isOpen_ratIntegralAdeles⟩
    have hfun : Continuous ratAdeleGaussian := by
      unfold ratAdeleGaussian
      apply hI.continuous_indicator
      exact Complex.continuous_ofReal.comp (Real.continuous_exp.comp
        (continuous_const.mul (((isometryEquivRealOfIsReal Rat.isReal_infinitePlace).continuous.comp
          ((continuous_apply Rat.infinitePlace).comp continuous_fst)).pow 2)))
    have heq : f = 0 := Measure.eq_of_ae_eq hae hfun continuous_const
    have h1 := congrFun heq (1 : G)
    change ratAdeleGaussian 0 = 0 at h1
    simp [ratAdeleGaussian, ratRealPart, (integralAdelesOutside ℚ ∅).zero_mem] at h1
  have hLp : MemLp (lcaFourier μ f) 2 η := by
    apply e.toHomeomorph.measurableEmbedding.memLp_map_measure_iff.mpr
    rw [hFourier]
    exact hf₂
  have hScale := (hν.2.2 f hf₁ hf₂).2
  have hMap : eLpNorm (lcaFourier μ f) 2 η =
      eLpNorm (lcaFourier μ f ∘ e.toHomeomorph) 2 μ :=
    e.toHomeomorph.measurableEmbedding.eLpNorm_map_measure
  rw [hc, eLpNorm_smul_measure_of_ne_top' (by simp) _
    _ hLp.aestronglyMeasurable, hMap, hFourier] at hScale
  change (↑(c ^ ((2 : ℝ≥0∞).toReal)⁻¹) : ℝ≥0∞) * eLpNorm f 2 μ = eLpNorm f 2 μ at hScale
  rw [ENNReal.coe_rpow_of_nonneg _ (by positivity)] at hScale
  have hRoot : (c : ℝ≥0∞) ^ ((2 : ℝ≥0∞).toReal)⁻¹ = 1 :=
    (ENNReal.mul_left_inj hnorm hf₂.eLpNorm_ne_top).mp (hScale.trans (one_mul _).symm)
  have hc₁ : c = 1 := by
    apply ENNReal.coe_injective
    apply (ENNReal.strictMono_rpow_of_pos
      (by norm_num : 0 < ((2 : ℝ≥0∞).toReal)⁻¹)).injective
    simpa only [ENNReal.coe_one, ENNReal.one_rpow] using hRoot
  change IsLCAPlancherelMeasure μ η
  simpa only [hc, hc₁, one_smul] using hν

end RatAdeleSelfDuality

/-- Paper: Example A.3.1.9, p. 558. In (A.3.1.7) the standard adelic character is
the rational adelic character composed with the adelic trace.
Deviation: The displayed field trace is extended to the adele algebra as required by its domain. -/
def adeleStandardCharacter (a : 𝔸[F]) : Circle :=
  letI := (rationalAdeleEmbedding F).toAlgebra
  ratAdeleStandardCharacter (Algebra.trace 𝔸[ℚ] 𝔸[F] a)

/-- Paper: Example A.3.1.9, p. 558. The standard adelic character is trivial on the
diagonally embedded field, which is what Theorem 2.2.3.2 and Theorem 3.2.2.1 need. -/
theorem adeleStandardCharacter_algebraMap (x : F) :
    adeleStandardCharacter F (algebraMap F 𝔸[F] x) = 1 := by
  classical
  -- The adelic trace of a diagonal element is the diagonal field trace.
  let ι := Fin (Module.finrank ℚ F)
  let dQ := algebraMap ℚ 𝔸[ℚ]
  let dF := algebraMap F 𝔸[F]
  let : Algebra 𝔸[ℚ] 𝔸[F] := (rationalAdeleEmbedding F).toAlgebra
  obtain ⟨b₀, hb₀⟩ := exists_adelicIntegralBasis F
  let reindex : Module.Free.ChooseBasisIndex ℤ (𝓞 F) ≃ ι :=
    (Fintype.equivFin _).trans (finCongr (Module.finrank_eq_card_basis (integralBasis F)).symm)
  let c := (integralBasis F).reindex reindex
  let b := b₀.reindex reindex
  have hb (i : ι) : b i = dF (c i) := by
    simpa only [b, c, Module.Basis.reindex_apply] using hb₀ (reindex.symm i)
  have hdiag (q : ι → ℚ) : b.equivFun.symm (dQ ∘ q) = dF (c.equivFun.symm q) := by
    rw [Module.Basis.equivFun_symm_apply, Module.Basis.equivFun_symm_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [hb, Function.comp_apply, Algebra.smul_def, map_mul]
    exact congrArg (· * dF (c i)) ((rationalAdeleEmbedding_spec F).2.1 (q i))
  have hrepr (y : F) (i : ι) : b.repr (dF y) i = dQ (c.repr y i) := by
    have h := hdiag (c.equivFun y)
    rw [LinearEquiv.symm_apply_apply] at h
    rw [← h, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    rfl
  have htrace : Algebra.trace 𝔸[ℚ] 𝔸[F] (dF x) = dQ (Algebra.trace ℚ F x) := by
    rw [Algebra.trace_eq_matrix_trace b, Algebra.trace_eq_matrix_trace c, AddMonoidHom.map_trace]
    congr 1
    ext i j
    change (Algebra.leftMulMatrix b (dF x)) i j = dQ ((Algebra.leftMulMatrix c x) i j)
    rw [Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul, hb, ← map_mul,
      hrepr]
  change ratAdeleStandardCharacter (Algebra.trace 𝔸[ℚ] 𝔸[F] (dF x)) = 1
  rw [htrace]
  exact ratAdeleStandardCharacter_algebraMap _

/-- Paper: Example A.3.1.9, p. 558. The standard adelic character reduces to the
rational adelic character for the rational field. -/
theorem adeleStandardCharacter_rat (a : 𝔸[ℚ]) :
    adeleStandardCharacter ℚ a = ratAdeleStandardCharacter a := by
  obtain ⟨-, -, -, -, -, -, -, -, -, extensions⟩ := adele_additive_quotient ℚ
  have h : rationalAdeleEmbedding ℚ = RingHom.id 𝔸[ℚ] :=
    (extensions ℚ (RingHom.id ℚ)).1.unique
      (rationalAdeleEmbedding_spec ℚ) (isAdeleExtension_id ℚ)
  unfold adeleStandardCharacter
  rw [h]
  exact congrArg ratAdeleStandardCharacter (Algebra.trace_self_apply a)

section AdeleSelfDuality

local instance : BorelSpace 𝔸[F] := ⟨rfl⟩

local instance : BorelSpace (Multiplicative 𝔸[F]) := ⟨rfl⟩

open scoped IsDedekindDomain.FiniteAdeleRing RestrictedProduct in
/-- The rational adeles are second countable by the countable open cover obtained by
allowing a finite set of primes to have nonintegral components. -/
private theorem ratAdele_secondCountable : SecondCountableTopology (Multiplicative 𝔸[ℚ]) := by
  let I := Primes(ℚ)
  let K (v : I) := v.adicCompletion ℚ
  let O (v : I) : Set (K v) := v.adicCompletionIntegers ℚ
  let : Countable I := Rat.HeightOneSpectrum.primesEquiv.injective.countable
  let (v : I) : SecondCountableTopology (K v) := by
    let p := Rat.HeightOneSpectrum.primesEquiv v
    let : Fact p.val.Prime := ⟨p.property⟩
    let : TopologicalSpace.SeparableSpace ℚ_[p.val] :=
      ⟨⟨range ((↑) : ℚ → ℚ_[p.val]), countable_range _, Padic.denseRange_ratCast _⟩⟩
    exact (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toHomeomorph.isEmbedding
      |>.secondCountableTopology
  let U := fun s : Finset I ↦ {a : FiniteAdeleRing (𝓞 ℚ) ℚ | ∀ v ∉ s, a v ∈ O v}
  have hopen (v : I) : IsOpen (O v) := Valued.isOpen_integer (K v)
  let (s : Finset I) : SecondCountableTopology (U s) := by
    have hs : Filter.cofinite ≤ Filter.principal (s : Set I)ᶜ :=
      Filter.le_principal_iff.mpr s.finite_toSet.compl_mem_cofinite
    have he := RestrictedProduct.isOpenEmbedding_inclusion_principal (R := K) (A := O) hopen hs
    let : SecondCountableTopology (Πʳ v : I, [K v, O v]_[Filter.principal (s : Set I)ᶜ]) :=
      (RestrictedProduct.isEmbedding_coe_of_principal (R := K) (A := O)).secondCountableTopology
    have hrange : range (RestrictedProduct.inclusion K O hs) = U s := by
      rw [RestrictedProduct.range_inclusion]
      rfl
    exact hrange ▸ he.toIsEmbedding.toHomeomorph.symm.isEmbedding.secondCountableTopology
  let : SecondCountableTopology (FiniteAdeleRing (𝓞 ℚ) ℚ) := by
    refine TopologicalSpace.secondCountableTopology_of_countable_cover (U := U)
      (fun _ ↦ RestrictedProduct.isOpen_forall_imp_mem hopen) (eq_univ_of_forall fun a ↦ ?_)
    have he := Filter.eventually_cofinite.mp a.2
    exact mem_iUnion.mpr ⟨he.toFinset, fun v hv ↦ by
      by_contra h
      exact hv (he.mem_toFinset.mpr h)⟩
  let (v : InfinitePlace ℚ) : SecondCountableTopology v.Completion :=
    (isometry_extensionEmbedding v).isEmbedding.secondCountableTopology
  change SecondCountableTopology (((v : InfinitePlace ℚ) → v.Completion) ×
    FiniteAdeleRing (𝓞 ℚ) ℚ)
  infer_instance

attribute [local instance] ratAdele_secondCountable

open scoped RestrictedProduct in
/-- The product of the infinite adeles and the locally compact restricted product of
the finite completions is locally compact. -/
private theorem adele_locallyCompact : LocallyCompactSpace (Multiplicative 𝔸[F]) := by
  let (v : Primes(F)) : CompactSpace (v.adicCompletionIntegers F) :=
    compactSpace_adicCompletionIntegers v
  let : Fact (∀ v : Primes(F), IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    ⟨fun v ↦ Valued.isOpen_valuationSubring _⟩
  change LocallyCompactSpace (InfiniteAdeleRing F ×
    (Πʳ v : Primes(F), [v.adicCompletion F, v.adicCompletionIntegers F]))
  infer_instance

attribute [local instance] adele_locallyCompact

open scoped RestrictedProduct in
local instance : T2Space (Multiplicative 𝔸[F]) := by
  change T2Space (((v : InfinitePlace F) → v.Completion) ×
    (Πʳ v : Primes(F), [v.adicCompletion F, v.adicCompletionIntegers F]))
  infer_instance

/-- The covolume-one measure is Haar on the multiplicative synonym of the
additive group of adeles. -/
private theorem additiveTamagawaMeasure_isHaar :
    (show Measure (Multiplicative 𝔸[F]) from additiveTamagawaMeasure F).IsHaarMeasure := by
  have h := (additiveTamagawaMeasure_existsUnique F).exists.choose_spec.1
  exact { toIsFiniteMeasureOnCompacts := h.toIsFiniteMeasureOnCompacts
          toIsOpenPosMeasure := h.toIsOpenPosMeasure
          map_mul_left_eq_self := fun x ↦ h.map_add_left_eq_self x.toAdd }

attribute [local instance] additiveTamagawaMeasure_isHaar

open scoped TensorProduct in
/-- Paper: Example A.3.1.9, p. 558. A rational basis of `F` and its trace-dual basis
give adelic coordinates in which the trace character pairing is coordinatewise. Both
coordinate maps carry the diagonal rational vectors onto the diagonal copy of `F`. -/
theorem exists_adeleTrace_dualCoordinates :
    let ι := Fin (Module.finrank ℚ F)
    let d := fun q : ι → ℚ ↦ fun i ↦ Multiplicative.ofAdd (algebraMap ℚ 𝔸[ℚ] (q i))
    ∃ u v : (ι → Multiplicative 𝔸[ℚ]) ≃ₜ* Multiplicative 𝔸[F],
      u '' range d = (A[F] : Set (Multiplicative 𝔸[F])) ∧
      v '' range d = (A[F] : Set (Multiplicative 𝔸[F])) ∧
      ∀ x y, adeleStandardCharacter F ((u x).toAdd * (v y).toAdd) =
        ∏ i, ratAdeleStandardCharacter ((x i).toAdd * (y i).toAdd) := by
  classical
  let ι := Fin (Module.finrank ℚ F)
  let dQ := algebraMap ℚ 𝔸[ℚ]
  let dF := algebraMap F 𝔸[F]
  let : Algebra 𝔸[ℚ] 𝔸[F] := (rationalAdeleEmbedding F).toAlgebra
  obtain ⟨b₀, hb₀⟩ := exists_adelicIntegralBasis F
  let reindex : Module.Free.ChooseBasisIndex ℤ (𝓞 F) ≃ ι :=
    (Fintype.equivFin _).trans (finCongr (Module.finrank_eq_card_basis (integralBasis F)).symm)
  let c := (integralBasis F).reindex reindex
  let b := b₀.reindex reindex
  have hb (i : ι) : b i = dF (c i) := by
    simpa only [b, c, Module.Basis.reindex_apply] using hb₀ (reindex.symm i)
  have hdiag (B : Module.Basis ι 𝔸[ℚ] 𝔸[F]) (C : Module.Basis ι ℚ F)
      (hB : ∀ i, B i = dF (C i)) (q : ι → ℚ) :
      B.equivFun.symm (dQ ∘ q) = dF (C.equivFun.symm q) := by
    rw [Module.Basis.equivFun_symm_apply, Module.Basis.equivFun_symm_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [hB, Function.comp_apply, Algebra.smul_def, map_mul]
    exact congrArg (· * dF (C i)) ((rationalAdeleEmbedding_spec F).2.1 (q i))
  have hrepr (x : F) (i : ι) : b.repr (dF x) i = dQ (c.repr x i) := by
    have h := hdiag b c hb (c.equivFun x)
    rw [LinearEquiv.symm_apply_apply] at h
    rw [← h, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    rfl
  let tr := Algebra.trace 𝔸[ℚ] 𝔸[F]
  have htrace (x : F) : tr (dF x) = dQ (Algebra.trace ℚ F x) := by
    change Algebra.trace 𝔸[ℚ] 𝔸[F] (dF x) = _
    rw [Algebra.trace_eq_matrix_trace b, Algebra.trace_eq_matrix_trace c, AddMonoidHom.map_trace]
    congr 1
    ext i j
    change (Algebra.leftMulMatrix b (dF x)) i j = dQ ((Algebra.leftMulMatrix c x) i j)
    rw [Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul, hb, ← map_mul, hrepr]
  let lift : (𝔸[ℚ] ⊗[ℚ] F) ≃ₗ[𝔸[ℚ]] 𝔸[F] :=
    (c.baseChange 𝔸[ℚ]).equivFun.trans b.equivFun.symm
  have hlift (x : F) : lift ((1 : 𝔸[ℚ]) ⊗ₜ[ℚ] x) = dF x := by
    have hcoords : (c.baseChange 𝔸[ℚ]).equivFun ((1 : 𝔸[ℚ]) ⊗ₜ[ℚ] x) = dQ ∘ c.equivFun x := by
      funext i
      change (c.baseChange 𝔸[ℚ]).repr ((1 : 𝔸[ℚ]) ⊗ₜ[ℚ] x) i = dQ (c.repr x i)
      rw [Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]
    change b.equivFun.symm ((c.baseChange 𝔸[ℚ]).equivFun ((1 : 𝔸[ℚ]) ⊗ₜ[ℚ] x)) = _
    rw [hcoords, hdiag b c hb, LinearEquiv.symm_apply_apply]
  let b' := (c.traceDual.baseChange 𝔸[ℚ]).map lift
  have hb' (i : ι) : b' i = dF (c.traceDual i) := by
    simp only [b', Module.Basis.map_apply, Module.Basis.baseChange_apply, hlift]
  have hδ (i j : ι) : tr (b i * b' j) = if i = j then 1 else 0 := by
    rw [hb, hb', ← map_mul, htrace, c.trace_mul_traceDual]
    split_ifs <;> simp
  let P := ι → Multiplicative 𝔸[ℚ]
  let G := Multiplicative 𝔸[F]
  let coords (B : Module.Basis ι 𝔸[ℚ] 𝔸[F]) : P ≃ₜ* G := by
    let L := B.equivFun.symm
    have hL : Continuous L := by
      change Continuous (fun a ↦ L a)
      simp only [L, Module.Basis.equivFun_symm_apply, Algebra.smul_def]
      exact continuous_finsetSum _ fun i _ ↦
        ((rationalAdeleEmbedding_spec F).1.comp (continuous_apply i)).mul continuous_const
    let : SigmaCompactSpace (Multiplicative 𝔸[ℚ]) := inferInstance
    let : SigmaCompactSpace 𝔸[ℚ] := ‹SigmaCompactSpace (Multiplicative 𝔸[ℚ])›
    let : LocallyCompactSpace 𝔸[F] := adele_locallyCompact F
    let : T2Space 𝔸[F] := inferInstanceAs (T2Space (Multiplicative 𝔸[F]))
    have hinv : Continuous L.symm := L.toEquiv.continuous_symm_iff.mpr
      (L.toAddMonoidHom.isOpenMap_of_sigmaCompact L.surjective hL)
    exact { L.toAddEquiv.toMultiplicative with
      continuous_toFun := hL
      continuous_invFun := hinv }
  have hcoords (B : Module.Basis ι 𝔸[ℚ] 𝔸[F]) (x : P) :
      (coords B x).toAdd = B.equivFun.symm (fun i ↦ (x i).toAdd) := rfl
  let d (q : ι → ℚ) : P := fun i ↦ Multiplicative.ofAdd (dQ (q i))
  have himage (B : Module.Basis ι 𝔸[ℚ] 𝔸[F]) (C : Module.Basis ι ℚ F)
      (hB : ∀ i, B i = dF (C i)) : coords B '' range d = (A[F] : Set G) := by
    ext x
    change x ∈ coords B '' range d ↔ ∃ z : F, dF z = x.toAdd
    rw [← range_comp]
    constructor
    · rintro ⟨q, hq⟩
      refine ⟨C.equivFun.symm q, ?_⟩
      exact (hdiag B C hB q).symm.trans ((hcoords B (d q)).symm.trans
        (congrArg Multiplicative.toAdd hq))
    · rintro ⟨z, hz⟩
      refine ⟨C.equivFun z, ?_⟩
      apply Multiplicative.toAdd.injective
      change (coords B (d (C.equivFun z))).toAdd = x.toAdd
      rw [hcoords]
      exact (hdiag B C hB (C.equivFun z)).trans (by rw [LinearEquiv.symm_apply_apply, hz])
  refine ⟨coords b, coords b', himage b c hb, himage b' c.traceDual hb', ?_⟩
  intro x y
  rw [hcoords, hcoords]
  change ratAdeleStandardCharacter (tr (b.equivFun.symm (fun i ↦ (x i).toAdd) *
    b'.equivFun.symm (fun i ↦ (y i).toAdd))) = _
  have hPair (a z : ι → 𝔸[ℚ]) :
      tr (b.equivFun.symm a * b'.equivFun.symm z) = ∑ i, a i * z i := by
    simp only [Module.Basis.equivFun_symm_apply, Finset.sum_mul, Finset.mul_sum,
      smul_mul_assoc, mul_smul_comm, map_sum, map_smul, smul_eq_mul, hδ,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact Finset.sum_congr rfl fun i _ ↦ mul_comm (z i) (a i)
  rw [hPair]
  let ψ : 𝔸[ℚ] →+ Additive Circle :=
    { toFun := fun a ↦ Additive.ofMul (ratAdeleStandardCharacter a)
      map_zero' := by
        have h := ratAdeleStandardCharacter_add 0 0
        rw [zero_add] at h
        have hzero : ratAdeleStandardCharacter 0 = 1 :=
          mul_left_cancel (h.symm.trans (mul_one _).symm)
        exact hzero
      map_add' := ratAdeleStandardCharacter_add }
  exact congrArg Additive.toMul (map_sum ψ (fun i ↦ (x i).toAdd * (y i).toAdd) Finset.univ)

/-- Paper: Definition A.3.1.1, p. 555. An adelic coordinate map carrying the diagonal
rational vectors onto the diagonal field transports the product of rational Tamagawa
measures to the covolume-one measure. The product of rational fundamental domains
has mass one and its image is a fundamental domain for the diagonal field. -/
theorem adeleTamagawaMeasurePreserving_of_diagonal
    (u : (Fin (Module.finrank ℚ F) → Multiplicative 𝔸[ℚ]) ≃ₜ* Multiplicative 𝔸[F])
    (hu : u '' range (fun q : Fin (Module.finrank ℚ F) → ℚ ↦
      fun i ↦ Multiplicative.ofAdd (algebraMap ℚ 𝔸[ℚ] (q i))) =
        (A[F] : Set (Multiplicative 𝔸[F]))) :
    MeasurePreserving u (Measure.pi fun _ ↦ additiveTamagawaMeasure ℚ)
      (additiveTamagawaMeasure F) := by
  classical
  let ι := Fin (Module.finrank ℚ F)
  let P := ι → Multiplicative 𝔸[ℚ]
  let G := Multiplicative 𝔸[F]
  let H := A[F]
  let mRat : Measure (Multiplicative 𝔸[ℚ]) := additiveTamagawaMeasure ℚ
  let ν : Measure P := Measure.pi fun _ ↦ mRat
  let μ : Measure G := additiveTamagawaMeasure F
  let m : Measure G := ν.map u
  let : SecondCountableTopology G := u.symm.toHomeomorph.isEmbedding.secondCountableTopology
  let : mRat.IsHaarMeasure := additiveTamagawaMeasure_isHaar ℚ
  let : SigmaFinite mRat := inferInstance
  let : ν.IsHaarMeasure := Measure.pi.isHaarMeasure _
  let : μ.IsHaarMeasure := additiveTamagawaMeasure_isHaar F
  let : m.IsHaarMeasure := u.isHaarMeasure_map ν
  let d (q : ι → ℚ) : P := fun i ↦ Multiplicative.ofAdd (algebraMap ℚ 𝔸[ℚ] (q i))
  let E₀ : Set (Multiplicative 𝔸[ℚ]) := ratAdeleFundamentalDomain
  let E : Set P := univ.pi fun _ ↦ E₀
  let D : Set G := u '' E
  have hrat : MeasurableSet ratAdeleFundamentalDomain :=
    (ratTamagawaMeasurePreserving_realPart.measurable measurableSet_Ico).inter
      isOpen_ratIntegralAdeles.measurableSet
  have hE : MeasurableSet E := MeasurableSet.pi countable_univ (fun _ _ ↦ hrat)
  have huemb : MeasurableEmbedding (u : P → G) := u.toHomeomorph.measurableEmbedding
  have hD : MeasurableSet D := huemb.measurableSet_image.mpr hE
  have hνE : ν E = 1 := by
    have hmass : additiveTamagawaMeasure ℚ ratAdeleFundamentalDomain = 1 := by
      have h := ratTamagawaMeasurePreserving_realPart.measure_preimage
        (measurableSet_Ico.nullMeasurableSet (s := Ico (0 : ℝ) 1))
      rwa [Measure.restrict_apply (ratTamagawaMeasurePreserving_realPart.measurable measurableSet_Ico),
        Real.volume_Ico, sub_zero, ENNReal.ofReal_one] at h
    change Measure.pi (fun _ : ι ↦ mRat) (univ.pi fun _ ↦ E₀) = 1
    rw [Measure.pi_pi]
    exact Finset.prod_eq_one fun _ _ ↦ hmass
  have hprecompact : IsCompact (closure D) := by
    have hK : IsCompact (closure ratAdeleFundamentalDomain) := by
      simpa using ratAdeleFundamentalDomain_precompact_translate 0
    have hC : IsCompact (u '' (univ.pi fun _ : ι ↦
        (show Set (Multiplicative 𝔸[ℚ]) from closure ratAdeleFundamentalDomain))) :=
      (isCompact_univ_pi fun _ ↦ hK).image u.continuous
    exact hC.of_isClosed_subset isClosed_closure
      (closure_minimal (Set.image_mono (Set.pi_mono fun _ _ ↦ subset_closure)) hC.isClosed)
  have hu' : u '' range d = (H : Set G) := hu
  let j : (ι → ℚ) → H := fun q ↦ ⟨u (d q), by
    change u (d q) ∈ (H : Set G)
    rw [← hu']
    exact Set.mem_image_of_mem u (mem_range_self q)⟩
  have hj : Bijective j := by
    have hinj := (adele_additive_quotient.{0, 0} ℚ).1
    refine ⟨fun x y h ↦ funext fun i ↦ ?_, fun a ↦ ?_⟩
    · exact hinj (congrFun (u.injective (congrArg Subtype.val h)) i)
    · have ha : a.val ∈ (H : Set G) := a.property
      rw [← hu'] at ha
      obtain ⟨_, ⟨q, rfl⟩, hq⟩ := ha
      exact ⟨q, Subtype.ext hq⟩
  let e : (ι → ℚ) ≃ H.op := ((Equiv.ofBijective j hj).trans (Equiv.inv H)).trans H.equivOp
  have htiles (a : G) : ∃! h : H.op, h • a ∈ D := by
    have hmem (q : ι → ℚ) : e q • a ∈ D ↔ ∀ i,
        (u.symm a i).toAdd ∈ algebraMap ℚ 𝔸[ℚ] (q i) +ᵥ ratAdeleFundamentalDomain := by
      change a * (u (d q))⁻¹ ∈ u '' E ↔ _
      have hx : u ((d q)⁻¹ * u.symm a) = a * (u (d q))⁻¹ := by
        rw [map_mul, map_inv, u.apply_symm_apply, mul_comm]
      rw [← hx, u.injective.mem_set_image]
      simp only [E, Set.mem_univ_pi, Set.mem_vadd_set_iff_neg_vadd_mem]
      rfl
    choose q hq huniq using fun i ↦ ratAdeleFundamentalDomain_unique_translate (u.symm a i).toAdd
    refine ⟨e q, (hmem q).mpr hq, fun h hh ↦ ?_⟩
    obtain ⟨r, rfl⟩ := e.surjective h
    exact congrArg e (funext fun i ↦ huniq i (r i) ((hmem r).mp hh i))
  have hFund : IsFundamentalDomain H.op D μ := IsFundamentalDomain.mk' hD.nullMeasurableSet htiles
  obtain ⟨-, hclosed, hdiscrete, -⟩ := adele_additive_quotient.{_, 0} F
  let : DiscreteTopology H := isDiscrete_iff_discreteTopology.mp hdiscrete
  let : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  let : Countable H := (Set.countable_range (algebraMap F 𝔸[F])).to_subtype
  obtain ⟨η, hη, hηmass⟩ := additiveTamagawaMeasure_quotientVolume F
  have hμD : μ D = 1 := (weilQuotientMeasure_univ_eq_measure_fundamentalDomain hclosed hη
    (hηmass.trans_ne ENNReal.one_ne_top) hFund hprecompact (fun a ↦ (htiles a).exists)).symm.trans hηmass
  have hmD : m D = 1 := (huemb.map_apply ν D).trans (by
    rw [show u ⁻¹' D = E from Set.preimage_image_eq _ u.injective, hνE])
  have hscale := Measure.isMulLeftInvariant_eq_smul m μ
  have hc : (m.haarScalarFactor μ : ℝ≥0∞) = 1 := by
    have h := congrArg (fun η : Measure G ↦ η D) hscale
    change m D = (m.haarScalarFactor μ : ℝ≥0∞) * μ D at h
    rw [hmD, hμD, mul_one] at h
    exact h.symm
  refine ⟨huemb.measurable, ?_⟩
  change m = μ
  rw [hscale, ENNReal.coe_eq_one.mp hc, one_smul]

/-- Paper: Example A.3.1.9, p. 558. For a finite power of the rational adeles, the
product of the rational pairings identifies the power with its Pontryagin dual and
sends the product Haar measure to the Plancherel measure. -/
theorem ratAdeleProduct_plancherel (n : ℕ) :
    let G := Fin n → Multiplicative 𝔸[ℚ]
    let μ : Measure G := Measure.pi fun _ ↦ additiveTamagawaMeasure ℚ
    letI : MeasurableSpace (PontryaginDual G) := borel _
    ∃ e : G ≃ₜ* PontryaginDual G,
      (∀ x y, e x y = ∏ i, ratAdeleStandardCharacter ((x i).toAdd * (y i).toAdd)) ∧
        IsLCAPlancherelMeasure μ (μ.map e) := by
  classical
  let G := Multiplicative 𝔸[ℚ]
  let P := Fin n → G
  let m : Measure G := additiveTamagawaMeasure ℚ
  let : m.IsHaarMeasure := additiveTamagawaMeasure_isHaar ℚ
  let : SigmaFinite m := inferInstance
  let μ : Measure P := Measure.pi fun _ ↦ m
  let : μ.IsHaarMeasure := Measure.pi.isHaarMeasure _
  let : μ.Regular := inferInstance
  let : MeasurableSpace (PontryaginDual P) := borel _
  let : BorelSpace (PontryaginDual P) := ⟨rfl⟩
  obtain ⟨e₀, he₀⟩ := exists_ratAdeleDualEquiv
  let pr (i : Fin n) : P →ₜ* G := ⟨Pi.evalMonoidHom (fun _ ↦ G) i, continuous_apply i⟩
  let j (i : Fin n) : G →ₜ* P :=
    ⟨MonoidHom.mulSingle (fun _ ↦ G) i, continuous_mulSingle (A := fun _ ↦ G) i⟩
  let χ (x : P) : PontryaginDual P := ∏ i, PontryaginDual.map (pr i) (e₀ (x i))
  have hχ (x y : P) : χ x y = ∏ i, e₀ (x i) (y i) := by
    let ev : PontryaginDual P →* Circle := ⟨⟨fun ψ ↦ ψ y, rfl⟩, fun _ _ ↦ rfl⟩
    exact map_prod ev _ _
  let coords (ψ : PontryaginDual P) : P := fun i ↦ e₀.symm (PontryaginDual.map (j i) ψ)
  let e : P ≃ₜ* PontryaginDual P :=
    { toFun := χ
      invFun := coords
      left_inv := by
        intro x
        funext i
        apply e₀.injective
        change e₀ (e₀.symm (PontryaginDual.map (j i) (χ x))) = e₀ (x i)
        rw [e₀.apply_symm_apply]
        apply PontryaginDual.ext
        intro y
        change χ x (Pi.mulSingle i y) = _
        rw [hχ, Finset.prod_eq_single i]
        · rw [Pi.mulSingle_eq_same]
        · intro k _ hk
          rw [Pi.mulSingle_eq_of_ne' hk.symm, map_one]
        · simp
      right_inv := fun ψ ↦ PontryaginDual.ext fun x ↦ by
        rw [hχ]
        simp only [coords, e₀.apply_symm_apply, PontryaginDual.map_apply]
        change (∏ i, ψ (Pi.mulSingle i (x i))) = ψ x
        rw [← map_prod, Finset.univ_prod_mulSingle]
      map_mul' := fun x y ↦ PontryaginDual.ext fun z ↦ by
        change χ (x * y) z = χ x z * χ y z
        rw [hχ, hχ, hχ, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun i _ ↦ ?_
        change e₀ (x i * y i) (z i) = _
        rw [map_mul]
        rfl
      continuous_toFun := continuous_finsetProd _ fun i _ ↦
        (PontryaginDual.map (pr i)).continuous.comp (e₀.continuous.comp (continuous_apply i))
      continuous_invFun := continuous_pi fun i ↦
        e₀.symm.continuous.comp (PontryaginDual.map (j i)).continuous }
  have hp (x y : P) : e x y = ∏ i, ratAdeleStandardCharacter ((x i).toAdd * (y i).toAdd) := by
    change χ x y = _
    rw [hχ]
    exact Finset.prod_congr rfl fun i _ ↦ he₀ (x i).toAdd (y i).toAdd
  refine ⟨e, hp, ?_⟩
  let g : G → ℂ := fun x ↦ ratAdeleGaussian x.toAdd
  let f : P → ℂ := fun x ↦ ∏ i, g (x i)
  obtain ⟨hg₁, hg₂⟩ := ratAdeleGaussian_integrable_memLp
  have hg₁' : Integrable g m := hg₁
  have hg₂' : MemLp g 2 m := hg₂
  have hf₁ : Integrable f μ := Integrable.fintype_prod (fun _ ↦ hg₁')
  have hf₂ : MemLp f 2 μ := by
    apply (memLp_two_iff_integrable_sq_norm hf₁.aestronglyMeasurable).mpr
    have hsq : Integrable (fun x ↦ ‖g x‖ ^ 2) m :=
      (memLp_two_iff_integrable_sq_norm hg₁'.aestronglyMeasurable).mp hg₂'
    simpa only [f, Complex.norm_prod, Finset.prod_pow] using
      (Integrable.fintype_prod (ι := Fin n) (fun _ ↦ hsq))
  have hfourier : lcaFourier μ f ∘ e = f := by
    funext y
    let k (i : Fin n) (x : G) := g x *
      star (ratAdeleStandardCharacter (x.toAdd * (y i).toAdd) : ℂ)
    calc
      _ = ∫ x : P, ∏ i, k i (x i) ∂μ := by
        apply integral_congr_ae
        refine Filter.Eventually.of_forall fun x ↦ ?_
        change (∏ i, g (x i)) * star (Circle.coeHom (e y x)) = _
        simp only [hp, map_prod, star_prod, k, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun i _ ↦ ?_
        rw [mul_comm (y i).toAdd]
        rfl
      _ = ∏ i, ∫ x, k i x ∂m := integral_fintype_prod_eq_prod k
      _ = _ := Finset.prod_congr rfl fun i _ ↦
        congrFun tamagawaFourier_ratAdeleGaussian (y i).toAdd
  have hnorm : eLpNorm f 2 μ ≠ 0 := by
    intro hzero
    have hae := (eLpNorm_eq_zero_iff (by norm_num : (2 : ℝ≥0∞) ≠ 0)).mp hzero
    have hg : g 1 = 1 := by
      change ratAdeleGaussian 0 = 1
      have hz : ratRealPart 0 = 0 :=
        map_zero (extensionEmbeddingOfIsReal Rat.isReal_infinitePlace)
      simp [ratAdeleGaussian, hz, (integralAdelesOutside ℚ ∅).zero_mem]
    have hf : f (1 : P) = 1 := Finset.prod_eq_one fun _ _ ↦ hg
    have h := congrFun hfourier (1 : P)
    change lcaFourier μ f (e 1) = f 1 at h
    rw [hf, lcaFourier, integral_congr_ae (hae.mono fun x hx ↦ by
      change f x = 0 at hx
      rw [hx, zero_mul]), integral_zero] at h
    exact zero_ne_one h
  obtain ⟨η, hη, _⟩ := lcaPlancherelMeasure_existsUnique μ
  let : η.IsHaarMeasure := hη.1
  let : η.Regular := hη.2.1
  let ν := μ.map e
  let : ν.IsHaarMeasure := e.isHaarMeasure_map μ
  let : ν.Regular := Measure.Regular.map e.toHomeomorph
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, η = c • ν := ⟨_, Measure.isMulLeftInvariant_eq_smul_of_regular η ν⟩
  have he : MeasurableEmbedding (e : P → PontryaginDual P) := e.toHomeomorph.measurableEmbedding
  have hLp : MemLp (lcaFourier μ f) 2 ν := by
    apply he.memLp_map_measure_iff.mpr
    rw [hfourier]
    exact hf₂
  have hNorm := (hη.2.2 f hf₁ hf₂).2
  have hMap : eLpNorm (lcaFourier μ f) 2 ν = eLpNorm f 2 μ :=
    he.eLpNorm_map_measure.trans (congrArg (fun k ↦ eLpNorm k 2 μ) hfourier)
  rw [hc, eLpNorm_smul_measure_of_ne_top' (by simp) _ _ hLp.aestronglyMeasurable, hMap] at hNorm
  have hr : 0 < ((2 : ℝ≥0∞).toReal)⁻¹ := by norm_num
  have hRoot : (c : ℝ≥0∞) ^ ((2 : ℝ≥0∞).toReal)⁻¹ = 1 := by
    apply (ENNReal.mul_left_inj hnorm hf₂.eLpNorm_ne_top).mp
    rw [one_mul, ← ENNReal.coe_rpow_of_nonneg _ hr.le]
    exact hNorm
  have hc₁ : c = 1 := ENNReal.coe_injective (by
    apply (ENNReal.strictMono_rpow_of_pos hr).injective
    simpa only [ENNReal.coe_one, ENNReal.one_rpow] using hRoot)
  change IsLCAPlancherelMeasure μ ν
  simpa only [hc, hc₁, one_smul] using hη

/-- Paper: Example A.3.1.9, p. 558. The global additive Tamagawa measure is self-dual
under the pairing from the trace character. -/
theorem additiveTamagawaMeasure_selfDual :
    IsTamagawaSelfDual (additiveTamagawaMeasure F) (adeleStandardCharacter F) := by
  let P := Fin (Module.finrank ℚ F) → Multiplicative 𝔸[ℚ]
  let G := Multiplicative 𝔸[F]
  let ν : Measure P := Measure.pi fun _ ↦ additiveTamagawaMeasure ℚ
  let μ : Measure G := additiveTamagawaMeasure F
  let : MeasurableSpace (PontryaginDual P) := borel _
  let : BorelSpace (PontryaginDual P) := ⟨rfl⟩
  let : MeasurableSpace (PontryaginDual G) := borel _
  let : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  obtain ⟨u, v, hu, hv, hpair⟩ := exists_adeleTrace_dualCoordinates F
  have huμ : MeasurePreserving u ν μ := adeleTamagawaMeasurePreserving_of_diagonal F u hu
  have hvμ : MeasurePreserving v ν μ := adeleTamagawaMeasurePreserving_of_diagonal F v hv
  obtain ⟨d, hd, hν⟩ := ratAdeleProduct_plancherel (Module.finrank ℚ F)
  let u₁ : P →ₜ* G := ⟨u.toMulEquiv.toMonoidHom, u.continuous⟩
  let u₂ : G →ₜ* P := ⟨u.symm.toMulEquiv.toMonoidHom, u.symm.continuous⟩
  let t : PontryaginDual P ≃ₜ* PontryaginDual G :=
    { toFun := PontryaginDual.map u₂
      invFun := PontryaginDual.map u₁
      left_inv := fun χ ↦ PontryaginDual.ext fun x ↦ congrArg χ (u.symm_apply_apply x)
      right_inv := fun χ ↦ PontryaginDual.ext fun x ↦ congrArg χ (u.apply_symm_apply x)
      map_mul' := fun _ _ ↦ rfl
      continuous_toFun := (PontryaginDual.map u₂).continuous
      continuous_invFun := (PontryaginDual.map u₁).continuous }
  let e := v.symm.trans (d.trans t)
  refine ⟨e, fun x y ↦ ?_, ?_⟩
  · change d (v.symm (Multiplicative.ofAdd x)) (u.symm (Multiplicative.ofAdd y)) = _
    rw [hd]
    simp_rw [mul_comm ((v.symm (Multiplicative.ofAdd x) _) : Multiplicative 𝔸[ℚ]).toAdd]
    rw [← hpair, u.apply_symm_apply, v.apply_symm_apply, mul_comm]
    rfl
  have hμ := (additiveTamagawaMeasure_existsUnique F).exists.choose_spec
  let : μ.IsHaarMeasure := additiveTamagawaMeasure_isHaar F
  let : μ.Regular := hμ.2.1
  refine ⟨e.isHaarMeasure_map μ, Measure.Regular.map e.toHomeomorph, ?_⟩
  intro f hf₁ hf₂
  have hFourier : lcaFourier μ f ∘ t = lcaFourier ν (f ∘ u) := by
    funext χ
    let k : G → ℂ := fun x ↦ f x * star (t χ x : ℂ)
    change (∫ x, k x ∂μ) = _
    calc
      _ = ∫ x : P, k (u x) ∂ν :=
        (huμ.integral_comp u.toHomeomorph.measurableEmbedding k).symm
      _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun x ↦
        congrArg (fun z : P ↦ f (u x) * star (χ z : ℂ)) (u.symm_apply_apply x))
  have hmap : μ.map e = (ν.map d).map t := by
    have he : Measurable (e : G → PontryaginDual G) := e.continuous.measurable
    have ht : Measurable (t : PontryaginDual P → PontryaginDual G) := t.continuous.measurable
    have hd' : Measurable (d : P → PontryaginDual P) := d.continuous.measurable
    rw [← hvμ.map_eq, Measure.map_map he hvμ.measurable, Measure.map_map ht hd']
    congr 1
    funext x
    change t (d (v.symm (v x))) = t (d x)
    rw [v.symm_apply_apply]
  have h := hν.2.2 (f ∘ u) (huμ.integrable_comp_of_integrable hf₁)
    (hf₂.comp_measurePreserving huμ)
  have ht : MeasurableEmbedding (t : PontryaginDual P → PontryaginDual G) :=
    t.toHomeomorph.measurableEmbedding
  rw [hmap]
  refine ⟨ht.memLp_map_measure_iff.mpr (hFourier ▸ h.1), ?_⟩
  calc
    _ = eLpNorm (lcaFourier μ f ∘ t) 2 (ν.map d) := ht.eLpNorm_map_measure
    _ = eLpNorm (f ∘ u) 2 ν := hFourier.symm ▸ h.2
    _ = _ := eLpNorm_comp_measurePreserving hf₂.aestronglyMeasurable huμ

end AdeleSelfDuality

/-- Paper: Example A.3.1.10, p. 558. The local character is the finite component
of the adelic trace character, evaluated on an adele supported at the given place.
Deviation: It is expressed by restriction of the adelic trace, whose component is the local trace. -/
def finiteLocalStandardCharacter (v : Primes(F)) (x : v.adicCompletion F) : Circle :=
  adeleStandardCharacter F (0, RestrictedProduct.single (fun w : Primes(F) ↦
    w.adicCompletionIntegers F) v x)

section FiniteLocalTrace

open scoped IsDedekindDomain.FiniteAdeleRing RestrictedProduct

local notation "O(" F ")" => (fun w : Primes(F) ↦ HeightOneSpectrum.adicCompletionIntegers F w)
local notation "K(" F ")" => (fun w : Primes(F) ↦ HeightOneSpectrum.adicCompletion F w)

/-- Projection to a finite coordinate of the adele ring. -/
private def finiteAdeleEval (v : Primes(F)) : 𝔸[F] →+* v.adicCompletion F :=
  (RestrictedProduct.evalRingHom (K(F)) v).comp (RingHom.snd _ _)

/-- Inclusion of a finite completion as the adeles supported at its place. -/
private def finiteAdeleSingle (v : Primes(F)) : v.adicCompletion F →+ 𝔸[F] where
  toFun x := (0, RestrictedProduct.single (O(F)) v x)
  map_zero' := Prod.ext rfl (RestrictedProduct.single_zero (O(F)) v)
  map_add' x y := Prod.ext (zero_add _).symm (RestrictedProduct.single_add (O(F)) v x y)

/-- Inserting an element at one finite place is continuous for the restricted product topology. -/
private theorem continuous_finiteAdeleSingle (v : Primes(F)) :
    Continuous (finiteAdeleSingle F v) := by
  let S : Set Primes(F) := {v}ᶜ
  let hS : Filter.cofinite ≤ Filter.principal S := by simp [S, Filter.le_principal_iff]
  let s (x : v.adicCompletion F) : Πʳ w, [K(F) w, O(F) w]_[Filter.principal S] :=
    ⟨Pi.single v x, by
      rw [Filter.eventually_principal]
      intro w hw
      exact (Pi.single_eq_of_ne hw x).symm ▸ (O(F) w).zero_mem⟩
  have hs : Continuous s := RestrictedProduct.continuous_rng_of_principal.mpr (continuous_single v)
  exact continuous_const.prodMk ((RestrictedProduct.continuous_inclusion hS).comp hs)

/-- Multiplying an adele supported at one finite place uses only that coordinate of the multiplier. -/
private theorem finiteAdeleSingle_mul (v : Primes(F)) (a : 𝔸[F]) (x : v.adicCompletion F) :
    finiteAdeleSingle F v (finiteAdeleEval F v a * x) = a * finiteAdeleSingle F v x :=
  Prod.ext (mul_zero _).symm (RestrictedProduct.mul_single (O(F)) v x a.2)

/-- The rational adelic embedding induces the local embedding on a finite coordinate. -/
private theorem exists_finiteAdeleEmbedding (v : Primes(F)) (u : Primes(ℚ))
    (hu : u.asIdeal = v.asIdeal.comap (RingOfIntegers.mapRingHom (algebraMap ℚ F))) :
    ∃ j : u.adicCompletion ℚ →+* v.adicCompletion F,
      Continuous j ∧ (∀ r : ℚ, j (algebraMap ℚ (u.adicCompletion ℚ) r) =
        algebraMap F (v.adicCompletion F) (algebraMap ℚ F r)) ∧
      ∀ a : 𝔸[ℚ], finiteAdeleEval F v (rationalAdeleEmbedding F a) =
        j (finiteAdeleEval ℚ u a) := by
  let p := finiteAdeleEval ℚ u
  let s := finiteAdeleSingle ℚ u
  let f := (finiteAdeleEval F v).comp (rationalAdeleEmbedding F)
  have hps (x) : p (s x) = x := RestrictedProduct.single_eq_same (O(ℚ)) u x
  have hfactor (a) : f a = f (s (p a)) := by
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply (rationalAdeleEmbedding_spec F).2.2.2 u v hu
    change p (a - s (p a)) = 0
    rw [map_sub, hps, sub_self]
  let j : u.adicCompletion ℚ →+* v.adicCompletion F :=
    { toFun := fun x ↦ f (s x)
      map_zero' := by rw [map_zero, map_zero]
      map_one' := by rw [← (map_one p), ← hfactor, map_one]
      map_add' := fun x y ↦ by rw [map_add, map_add]
      map_mul' := fun x y ↦ by
        have hm := finiteAdeleSingle_mul ℚ u (s x) y
        change s (p (s x) * y) = s x * s y at hm
        rw [hps] at hm
        rw [hm, map_mul] }
  have hj : Continuous j := ((RestrictedProduct.continuous_eval v).comp
    (continuous_snd.comp (rationalAdeleEmbedding_spec F).1)).comp
      (continuous_finiteAdeleSingle ℚ u)
  refine ⟨j, hj, ?_, hfactor⟩
  intro r
  have ha := hfactor (algebraMap ℚ 𝔸[ℚ] r)
  rw [show f (algebraMap ℚ 𝔸[ℚ] r) =
      algebraMap F (v.adicCompletion F) (algebraMap ℚ F r) from
    congrArg (finiteAdeleEval F v) ((rationalAdeleEmbedding_spec F).2.1 r)] at ha
  exact ha.symm

/-- Paper: Example A.3.1.10, p. 558. At a finite place the trace character
agrees with the standard p-adic character composed with the local field trace. -/
theorem finiteLocalStandardCharacter_trace (v : Primes(F)) (u : Primes(ℚ))
    (hu : u.asIdeal = v.asIdeal.comap (RingOfIntegers.mapRingHom (algebraMap ℚ F))) :
    let p := Rat.HeightOneSpectrum.primesEquiv u
    letI : Fact p.val.Prime := ⟨p.property⟩
    ∃ j : u.adicCompletion ℚ →+* v.adicCompletion F,
      Continuous j ∧ (∀ r : ℚ, j (algebraMap ℚ (u.adicCompletion ℚ) r) =
        algebraMap F (v.adicCompletion F) (algebraMap ℚ F r)) ∧
      letI := j.toAlgebra
      Module.Finite (u.adicCompletion ℚ) (v.adicCompletion F) ∧
        ∀ x : v.adicCompletion F, finiteLocalStandardCharacter F v x =
          padicStandardCharacter p.val (Rat.HeightOneSpectrum.adicCompletion.padicEquiv u
            (Algebra.trace (u.adicCompletion ℚ) (v.adicCompletion F) x)) := by
  dsimp only
  obtain ⟨j, hj, hdiag, hlocal⟩ := exists_finiteAdeleEmbedding F v u hu
  let := (rationalAdeleEmbedding F).toAlgebra
  let := j.toAlgebra
  obtain ⟨b⟩ := rationalAdeleEmbedding_hasBasis F
  let p := finiteAdeleEval ℚ u
  let s := finiteAdeleSingle F v
  have hp : Surjective p := fun z ↦
    ⟨finiteAdeleSingle ℚ u z, RestrictedProduct.single_eq_same (O(ℚ)) u z⟩
  obtain ⟨hfinite, htrace⟩ := trace_of_algebra_projection b p hp (finiteAdeleEval F v) s
    (fun z ↦ RestrictedProduct.single_eq_same (O(F)) v z) hlocal (finiteAdeleSingle_mul F v)
  refine ⟨j, hj, hdiag, hfinite, fun x ↦ ?_⟩
  let e := finiteAdeleSingle ℚ u 1
  let t := Algebra.trace 𝔸[ℚ] 𝔸[F] (s x)
  -- The scalar adele supported at u acts as the identity on the summand at v.
  have he : e • s x = s x := by
    change rationalAdeleEmbedding F e * s x = s x
    rw [← finiteAdeleSingle_mul, hlocal]
    have hp₁ : p e = 1 := RestrictedProduct.single_eq_same (O(ℚ)) u 1
    change s (j (p e) * x) = s x
    rw [hp₁, map_one, one_mul]
  have ht : e * t = t := by
    change e • Algebra.trace 𝔸[ℚ] 𝔸[F] (s x) = t
    rw [← map_smul, he]
  have ht_single : finiteAdeleSingle ℚ u (p t) = t := by
    have h := finiteAdeleSingle_mul ℚ u t 1
    change finiteAdeleSingle ℚ u (p t * 1) = t * e at h
    rwa [mul_one, mul_comm t e, ht] at h
  change ratAdeleStandardCharacter t = ratLocalCharacter u
    (Algebra.trace (u.adicCompletion ℚ) (v.adicCompletion F) x)
  rw [← htrace x]
  conv_lhs => rw [← ht_single]
  change Circle.exp (2 * Real.pi * extensionEmbeddingOfIsReal Rat.isReal_infinitePlace 0) *
    (∏ᶠ w : Primes(ℚ), ratLocalCharacter w (RestrictedProduct.single (O(ℚ)) u (p t) w)) =
      ratLocalCharacter u (p t)
  rw [map_zero, mul_zero, Circle.exp_zero, one_mul, finprod_eq_single _ u]
  · rw [RestrictedProduct.single_eq_same]
  · intro w hw
    rw [RestrictedProduct.single_eq_of_ne (O(ℚ)) _ hw]
    exact (ratLocalCharacter_eq_one w 0).2 ((O(ℚ) w).zero_mem)

end FiniteLocalTrace

section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

local instance instMeasurableSpacePontryaginDualForCompactOpen :
    MeasurableSpace (PontryaginDual G) := borel _
local instance instBorelSpacePontryaginDualForCompactOpen : BorelSpace (PontryaginDual G) := ⟨rfl⟩

/-- The characters trivial on a subgroup form a closed subset of the dual. -/
private theorem isClosed_subgroupAnnihilator {G : Type*} [Group G] [TopologicalSpace G]
    (H : Subgroup G) :
    IsClosed {χ : PontryaginDual G | ∀ x ∈ H, χ x = 1} := by
  rw [show {χ : PontryaginDual G | ∀ x ∈ H, χ x = 1} =
    ⋂ x : H, {χ : PontryaginDual G | χ x = 1} by ext; simp]
  exact isClosed_iInter fun x ↦ isClosed_eq
    ((continuous_eval_const (F := C(G, Circle)) (x : G)).comp
      (ContinuousMonoidHom.isInducing_toContinuousMap G Circle).continuous) continuous_const

/-- A regular Haar measure on the dual is Plancherel if it assigns the annihilator of
a compact open subgroup the reciprocal of the subgroup's Haar mass. -/
private theorem isLCAPlancherelMeasure_of_compactOpenSubgroup
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    (ν : Measure (PontryaginDual G)) [ν.IsHaarMeasure] [ν.Regular]
    (H : Subgroup G) (hH : IsCompact (H : Set G)) (hOpen : IsOpen (H : Set G))
    (hMass : ν {χ | ∀ x ∈ H, χ x = 1} = (μ H)⁻¹) :
    IsLCAPlancherelMeasure μ ν := by
  let A : Set (PontryaginDual G) := {χ | ∀ x ∈ H, χ x = 1}
  have hA : MeasurableSet A := (isClosed_subgroupAnnihilator H).measurableSet
  let f : G → ℂ := (H : Set G).indicator (fun _ ↦ 1)
  have hFin : μ H ≠ ⊤ := hH.measure_ne_top
  have hPos : μ H ≠ 0 := (hOpen.measure_pos μ ⟨1, H.one_mem⟩).ne'
  have hMeas : MeasurableSet (H : Set G) := hOpen.measurableSet
  have hFourier : lcaFourier μ f = A.indicator (fun _ ↦ (μ.real H : ℂ)) := by
    funext χ
    by_cases hχ : χ ∈ A
    · rw [indicator_of_mem hχ]
      unfold lcaFourier
      simp only [f, ← indicator_mul_left (H : Set G) (fun _ ↦ (1 : ℂ))
        (fun x ↦ star (χ x : ℂ)), one_mul, integral_indicator hMeas]
      rw [setIntegral_congr_fun hMeas (g := fun _ ↦ (1 : ℂ)) (fun x hx ↦ by simp [hχ x hx])]
      simp
    · rw [indicator_of_notMem hχ]
      change ¬∀ x ∈ H, χ x = 1 at hχ
      push Not at hχ
      obtain ⟨a, ha, hχa⟩ := hχ
      have hf (x : G) : f (a * x) = f x := by
        have hmem : a * x ∈ H ↔ x ∈ H := H.mul_mem_cancel_left ha
        by_cases hx : x ∈ H <;> simp [f, hmem, hx]
      have hShift : lcaFourier μ f χ = lcaFourier μ f χ * star (χ a : ℂ) := by
        unfold lcaFourier
        rw [← integral_mul_const, ← integral_mul_left_eq_self (μ := μ)
          (fun x ↦ f x * star (χ x : ℂ)) a]
        simp only [hf, map_mul, Circle.coe_mul, star_mul, mul_assoc]
      by_contra hne
      have hStar := (mul_eq_left₀ hne).mp hShift.symm
      exact hχa (Circle.coe_eq_one.mp (by simpa only [star_star, star_one] using congrArg star hStar))
  obtain ⟨ν', hν', -⟩ := lcaPlancherelMeasure_existsUnique μ
  let : ν'.IsHaarMeasure := hν'.1
  let : ν'.Regular := hν'.2.1
  have hf₁ : Integrable f μ :=
    memLp_one_iff_integrable.mp (memLp_indicator_const 1 hMeas.nullMeasurableSet 1 (Or.inr hFin))
  have hf₂ : MemLp f 2 μ :=
    memLp_indicator_const 2 hMeas.nullMeasurableSet 1 (Or.inr hFin)
  have hNorm := (hν'.2.2 f hf₁ hf₂).2
  rw [hFourier, eLpNorm_indicator_const hA.nullMeasurableSet (by simp) (by simp)] at hNorm
  have hNormF : eLpNorm f 2 μ = (μ H) ^ (1 / 2 : ℝ) := by
    dsimp only [f]
    rw [eLpNorm_indicator_const hMeas.nullMeasurableSet (by simp) (by simp)]
    norm_num
  have hEnorm : ‖(μ.real H : ℂ)‖ₑ = μ H := by
    simp [ENNReal.ofReal_toReal hFin, ← ofReal_norm, Real.norm_eq_abs, measureReal_def]
  rw [hNormF, hEnorm] at hNorm
  have hSquared := congrArg (fun t : ℝ≥0∞ ↦ t ^ (2 : ℝ)) hNorm
  have hSquare : (μ H) ^ (2 : ℕ) * ν' A = μ H := by
    have hExp : (1 / (2 : ℝ≥0∞).toReal) * 2 = (1 : ℝ) := by norm_num
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul,
      ← ENNReal.rpow_mul, hExp, show (1 / 2 : ℝ) * 2 = 1 by norm_num,
      ENNReal.rpow_one, ENNReal.rpow_one, ENNReal.rpow_two] at hSquared
    exact hSquared
  have hMass' : ν' A = (μ H)⁻¹ := by
    rw [pow_two, mul_assoc] at hSquare
    have heq : μ H * ν' A = 1 :=
      (ENNReal.mul_right_inj hPos hFin).mp (hSquare.trans (mul_one _).symm)
    exact (ENNReal.mul_right_inj hPos hFin).mp (heq.trans (ENNReal.mul_inv_cancel hPos hFin).symm)
  have hScale := Measure.isMulLeftInvariant_eq_smul_of_regular ν' ν
  have hMassNeZero : ν A ≠ 0 := hMass.trans_ne (ENNReal.inv_ne_zero.mpr hFin)
  have hMassNeTop : ν A ≠ ⊤ := hMass.trans_ne (ENNReal.inv_ne_top.mpr hPos)
  have heq : (↑(ν'.haarScalarFactor ν) : ℝ≥0∞) * ν A = 1 * ν A := by
    have hSame : ν' A = ν A := hMass'.trans hMass.symm
    nth_rw 1 [hScale] at hSame
    change (↑(ν'.haarScalarFactor ν) : ℝ≥0∞) * ν A = ν A at hSame
    rwa [one_mul]
  have hFactor : ν'.haarScalarFactor ν = 1 :=
    ENNReal.coe_injective ((ENNReal.mul_left_inj hMassNeZero hMassNeTop).mp heq)
  rw [hFactor, one_smul] at hScale
  exact hScale ▸ hν'

end

/-- The local trace character is continuous, additive, and nontrivial. -/
private theorem finiteLocalStandardCharacter_exists_continuousMonoidHom (v : Primes(F)) :
    ∃ ψ : Multiplicative (v.adicCompletion F) →ₜ* Circle,
      (∀ x : v.adicCompletion F, ψ (Multiplicative.ofAdd x) = finiteLocalStandardCharacter F v x) ∧
      ∃ x : v.adicCompletion F, ψ (Multiplicative.ofAdd x) ≠ 1 := by
  let u := v.under (𝓞 ℚ)
  let p := Rat.HeightOneSpectrum.primesEquiv u
  let : Fact p.val.Prime := ⟨p.property⟩
  let K := u.adicCompletion ℚ
  let L := v.adicCompletion F
  obtain ⟨j, hj, -, hFinite, hψ⟩ := finiteLocalStandardCharacter_trace F v u rfl
  let : Algebra K L := j.toAlgebra
  let : Module.Finite K L := hFinite
  let t : K ≃+* ℚ_[p.val] := Rat.HeightOneSpectrum.adicCompletion.padicEquiv u
  let tr := Algebra.trace K L
  let : ContinuousSMul K L := ⟨(hj.comp continuous_fst).mul continuous_snd⟩
  let : NontriviallyNormedField K := Valued.toNontriviallyNormedField K (WithZero (Multiplicative ℤ))
  have htr : Continuous (tr : L → K) := LinearMap.continuous_of_finiteDimensional tr
  have ht : Continuous t := (Rat.HeightOneSpectrum.adicCompletion.padicEquiv u).continuous
  have hψ' (x : L) : finiteLocalStandardCharacter F v x = padicStandardCharacter p.val (t (tr x)) := hψ x
  have hAdd (x y : L) : finiteLocalStandardCharacter F v (x + y) =
      finiteLocalStandardCharacter F v x * finiteLocalStandardCharacter F v y := by
    rw [hψ', hψ', hψ', map_add, map_add, padicStandardCharacter_add]
  have hOne : finiteLocalStandardCharacter F v (0 : L) = 1 := by
    apply mul_left_cancel (a := finiteLocalStandardCharacter F v (0 : L))
    simpa only [zero_add, mul_one] using (hAdd 0 0).symm
  let ψ : Multiplicative L →ₜ* Circle :=
    { toFun := fun x ↦ finiteLocalStandardCharacter F v x.toAdd
      map_one' := hOne
      map_mul' := hAdd
      continuous_toFun := by
        change Continuous (fun x : L ↦ finiteLocalStandardCharacter F v x)
        rw [show (fun x : L ↦ finiteLocalStandardCharacter F v x) = _ from funext hψ']
        exact (padicStandardCharacter_continuous p.val).comp (ht.comp htr) }
  refine ⟨ψ, fun _ ↦ rfl, ?_⟩
  let : CharZero K := charZero_of_injective_ringHom (f := t.symm.toRingHom) t.symm.injective
  have hn : (Module.finrank K L : K) ≠ 0 := Nat.cast_ne_zero.mpr (Module.finrank_pos.ne')
  let a := t.symm ((p.val : ℚ_[p.val])⁻¹)
  refine ⟨algebraMap K L (a / Module.finrank K L), ?_⟩
  change finiteLocalStandardCharacter F v (algebraMap K L (a / Module.finrank K L)) ≠ 1
  rw [hψ', show tr (algebraMap K L (a / Module.finrank K L)) = a by
    rw [Algebra.trace_algebraMap, nsmul_eq_mul, mul_comm, div_mul_cancel₀ _ hn]]
  rw [show t a = _ from t.apply_symm_apply _]
  exact padicStandardCharacter_inv_prime_ne_one p.val

/-- The local Tamagawa measure is regular because its Haar scalar is finite. -/
private theorem finiteLocalAdditiveTamagawaMeasure_regular (v : Primes(F)) :
    (finiteLocalAdditiveTamagawaMeasure F v).Regular := by
  let μ := Measure.addHaar (G := v.adicCompletion F)
  let O := (v.adicCompletionIntegers F : Set (v.adicCompletion F))
  have hO : IsOpen O := Valued.isOpen_valuationSubring _
  have hpos := hO.measure_pos μ ⟨0, (v.adicCompletionIntegers F).zero_mem⟩
  have hnorm : 0 < (v.asIdeal.absNorm : ℝ) := by
    exact_mod_cast zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v)
  have hsqrt := Real.sqrt_pos_of_pos (pow_pos hnorm (differentExp(F, v)))
  change ((differentMass(F, v) / μ O) • μ).Regular
  exact Measure.Regular.smul
    (ENNReal.div_ne_top (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hsqrt).ne') hpos.ne')

/-- The ball representing the inverse different has mass reciprocal to the integer ring. -/
private theorem finiteLocalAdditiveTamagawaMeasure_inverseDifferentBall (v : Primes(F)) :
    let μ := finiteLocalAdditiveTamagawaMeasure F v
    μ {x : v.adicCompletion F | ‖x‖ ≤ (v.asIdeal.absNorm : ℝ) ^ differentExp(F, v)} =
      (μ (v.adicCompletionIntegers F : Set (v.adicCompletion F)))⁻¹ := by
  dsimp only
  let K := v.adicCompletion F
  let O := v.adicCompletionIntegers F
  let μ := finiteLocalAdditiveTamagawaMeasure F v
  let : μ.IsAddHaarMeasure := finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  let : μ.Regular := finiteLocalAdditiveTamagawaMeasure_regular F v
  let val : Valuation K _ := Valued.v
  obtain ⟨π, hπ⟩ : ∃ π : O, val.IsUniformizer (π : K) :=
    val.exists_isUniformizer_of_isCyclic_of_nontrivial
  let u : Kˣ := Units.mk0 π.val hπ.ne_zero
  let q := v.asIdeal.absNorm
  let d := differentExp(F, v)
  have hq : 0 < (q : ℝ) := by exact_mod_cast zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v)
  have hu : ‖u.val‖ = (q : ℝ)⁻¹ := norm_uniformizer_adicCompletion v _ hπ
  let : MeasurableSpace O := borel _
  let : BorelSpace O := ⟨rfl⟩
  let e := O.toSubring.subtype
  let μO := μ.comap e
  have hO : IsOpen (O : Set K) := Valued.isOpen_valuationSubring _
  have he : MeasurableEmbedding e := hO.isOpenEmbedding_subtypeVal.measurableEmbedding
  have : μO.IsAddLeftInvariant := ⟨fun x ↦ by
    ext s hs
    have hcont : Continuous (x + ·) := continuous_const.add continuous_id
    rw [Measure.map_apply hcont.measurable hs, he.comap_apply, he.comap_apply]
    have hpre : e '' ((x + ·) ⁻¹' s) = (e x + ·) ⁻¹' (e '' s) := by
      ext a
      constructor
      · rintro ⟨b, hb, rfl⟩
        exact ⟨x + b, hb, map_add e x b⟩
      · rintro ⟨b, hb, h⟩
        refine ⟨b - x, ?_, ?_⟩
        · show x + (b - x) ∈ s
          simpa [add_comm x] using hb
        · rw [map_sub, h]
          exact add_sub_cancel_left (e x) a
    have hm : Measurable (e x + ·) := (continuous_const.add continuous_id).measurable
    rw [hpre, ← Measure.map_apply hm (he.measurableSet_image.mpr hs), map_add_left_eq_self]⟩
  let r := (IsLocalRing.residue O).toAddMonoidHom
  have hindex : r.ker.index = q := by
    rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr (IsLocalRing.residue_surjective (R := O)),
      AddSubgroup.card_top, card_residueField_adicCompletion]
  have : r.ker.FiniteIndex := ⟨by rw [hindex]; exact_mod_cast hq.ne'⟩
  have hker (a : O) : a ∈ r.ker ↔ π ∣ a := by
    change IsLocalRing.residue O a = 0 ↔ π ∣ a
    have hgen : IsLocalRing.maximalIdeal O = Ideal.span {π} := hπ.is_generator
    rw [IsLocalRing.residue_eq_zero_iff, hgen, Ideal.mem_span_singleton]
  have hmeas : MeasurableSet (r.ker : Set O) := by
    have hSet : (r.ker : Set O) = {a | val.restrict (e a) < 1} := by
      ext a
      change IsLocalRing.residue O a = 0 ↔ val.restrict (e a) < 1
      rw [IsLocalRing.residue_eq_zero_iff, Valuation.restrict_lt_iff_lt_embedding, map_one]
      exact Valuation.mem_maximalIdeal_iff K val (a := a)
    rw [hSet]
    exact ((Valued.isOpen_ball K 1).preimage continuous_subtype_val).measurableSet
  have himage : e '' (r.ker : Set O) = u • (O : Set K) := by
    ext x
    change (∃ a : O, a ∈ r.ker ∧ e a = x) ↔ ∃ b ∈ (O : Set K), u.val * b = x
    simp only [hker]
    constructor
    · rintro ⟨a, ⟨b, rfl⟩, rfl⟩
      exact ⟨b, b.property, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      let bO : O := ⟨b, hb⟩
      exact ⟨π * bO, dvd_mul_right π bO, rfl⟩
  have hmass := r.ker.index_mul_measure hmeas μO
  change (r.ker.index : ℝ≥0∞) * μ.comap e r.ker = μ.comap e univ at hmass
  rw [hindex, he.comap_apply, he.comap_apply, himage, Set.image_univ,
    show range e = (O : Set K) from Subtype.range_coe] at hmass
  have hχ : distribHaarChar K u = (q : ℝ≥0)⁻¹ := by
    apply distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ)
      (hO.measure_pos μ ⟨0, O.zero_mem⟩).ne'
      (isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v)).measure_ne_top
    have hqN : q ≠ 0 := (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v)).ne'
    have hq0 : (q : ℝ≥0∞) ≠ 0 :=
      Nat.cast_ne_zero.mpr (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v)).ne'
    rw [← hmass, ENNReal.coe_inv (Nat.cast_ne_zero.mpr hqN), ENNReal.coe_natCast, ← mul_assoc,
      ENNReal.inv_mul_cancel hq0 (ENNReal.natCast_ne_top _), one_mul]
  let w : Kˣ := (u ^ d)⁻¹
  have hw : ‖w.val‖ = (q : ℝ) ^ d := by
    change ‖((u ^ d)⁻¹ : Kˣ).val‖ = _
    rw [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, norm_inv, norm_pow, hu, inv_pow, inv_inv]
  have hball : {x : K | ‖x‖ ≤ (q : ℝ) ^ d} = w • (O : Set K) := by
    ext x
    change ‖x‖ ≤ (q : ℝ) ^ d ↔ ∃ y ∈ (O : Set K), w.val * y = x
    rw [← hw]
    constructor
    · intro hx
      refine ⟨x / w.val, ?_, ?_⟩
      · apply (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).mpr
        apply Valued.toNormedField.norm_le_one_iff.mp
        rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr w.ne_zero), one_mul]
        exact hx
      · rw [mul_comm, div_mul_cancel₀ _ w.ne_zero]
    · rintro ⟨y, hy, rfl⟩
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (Valued.toNormedField.norm_le_one_iff.mpr ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).mp hy))
  change μ {x : K | ‖x‖ ≤ (q : ℝ) ^ d} = (μ (O : Set K))⁻¹
  rw [hball, ← distribHaarChar_mul μ, show distribHaarChar K w = (q : ℝ≥0) ^ d by
    rw [show w = (u ^ d)⁻¹ from rfl, map_inv, map_pow, hχ, inv_pow, inv_inv]]
  change ((↑((q : ℝ≥0) ^ d) : ℝ≥0∞) * μ (O : Set K)) = _
  rw [show μ (O : Set K) = differentMass(F, v) from finiteLocalAdditiveTamagawaMeasure_integers F v]
  change (↑((q : ℝ≥0) ^ d) : ℝ≥0∞) * (ENNReal.ofReal (Real.sqrt ((q : ℝ) ^ d)))⁻¹ =
    ((ENNReal.ofReal (Real.sqrt ((q : ℝ) ^ d)))⁻¹)⁻¹
  have hSq : (↑((q : ℝ≥0) ^ d) : ℝ≥0∞) =
      ENNReal.ofReal (Real.sqrt ((q : ℝ) ^ d)) ^ 2 := by
    rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _) 2, Real.sq_sqrt (pow_nonneg hq.le _)]
    simp [ENNReal.ofReal_pow hq.le]
  rw [hSq, pow_two, mul_assoc, ENNReal.mul_inv_cancel
    (ENNReal.ofReal_pos.mpr (Real.sqrt_pos_of_pos (pow_pos hq _))).ne' ENNReal.ofReal_ne_top,
    mul_one, inv_inv]

section FiniteLocalTraceDual

open scoped IsDedekindDomain.FiniteAdeleRing RestrictedProduct

local notation "O(" F ")" => (fun w : Primes(F) ↦ HeightOneSpectrum.adicCompletionIntegers F w)

/-- Norms on a completion at a finite place are integral powers of the residue cardinality. -/
private theorem norm_adicCompletion_eq_zpow (v : Primes(F)) {z : v.adicCompletion F} (hz : z ≠ 0) :
    ‖z‖ = (v.asIdeal.absNorm : ℝ) ^ (WithZero.log (Valued.v z)) := by
  rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ ((Valuation.ne_zero_iff _).mpr hz)]
  push_cast
  rfl

private theorem norm_coe_le_zpow_iff (v : Primes(F)) (r : 𝓞 F) (n : ℕ) :
    ‖(algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F r))‖ ≤
      (v.asIdeal.absNorm : ℝ) ^ (-(n : ℤ)) ↔ r ∈ v.asIdeal ^ n := by
  rw [← HeightOneSpectrum.intValuation_le_pow_iff_mem, FinitePlace.norm_def]
  have hq : (1 : ℝ≥0) < v.asIdeal.absNorm := HeightOneSpectrum.one_lt_absNorm_nnreal v
  have hval : Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F r)) =
      v.intValuation r := by
    rw [show algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F r) =
      ((algebraMap (𝓞 F) F r : F) : v.adicCompletion F) from rfl,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      HeightOneSpectrum.valuation_of_algebraMap]
  rw [hval, ← (WithZeroMulInt.toNNReal_strictMono hq).le_iff_le,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero, WithZero.log_exp]
  rw [← NNReal.coe_le_coe]
  push_cast
  rfl

private theorem exists_ball_trace_mem (v : Primes(F)) (u : Primes(ℚ))
    (j : u.adicCompletion ℚ →+* v.adicCompletion F) (hj : Continuous j) :
    letI := j.toAlgebra
    Module.Finite (u.adicCompletion ℚ) (v.adicCompletion F) →
      ∃ ε > 0, ∀ z : v.adicCompletion F, ‖z‖ < ε →
        Algebra.trace (u.adicCompletion ℚ) (v.adicCompletion F) z ∈ u.adicCompletionIntegers ℚ := by
  intro hfin
  let := j.toAlgebra
  let K := u.adicCompletion ℚ
  obtain ⟨π, hπ⟩ : ∃ π : u.adicCompletionIntegers ℚ, (Valued.v : Valuation K _).IsUniformizer (π : K) :=
    (Valued.v : Valuation K _).exists_isUniformizer_of_isCyclic_of_nontrivial
  have hπn : ‖(π : K)‖ = (u.asIdeal.absNorm : ℝ)⁻¹ := norm_uniformizer_adicCompletion u _ hπ
  let : NontriviallyNormedField K :=
    { (inferInstance : NormedField K) with
      non_trivial := ⟨(π : K)⁻¹, by
        rw [norm_inv, hπn, inv_inv]
        exact_mod_cast HeightOneSpectrum.one_lt_absNorm u⟩ }
  let : ContinuousSMul K (v.adicCompletion F) :=
    ⟨(hj.comp continuous_fst).mul continuous_snd⟩
  let : FiniteDimensional K (v.adicCompletion F) := hfin
  have hc : Continuous (Algebra.trace K (v.adicCompletion F)) :=
    LinearMap.continuous_of_finiteDimensional _
  have hopen : IsOpen ((Algebra.trace K (v.adicCompletion F)) ⁻¹'
      (u.adicCompletionIntegers ℚ : Set K)) :=
    (Valued.isOpen_valuationSubring _).preimage hc
  have h0 : (0 : v.adicCompletion F) ∈ (Algebra.trace K (v.adicCompletion F)) ⁻¹'
      (u.adicCompletionIntegers ℚ : Set K) := by
    simp only [mem_preimage, map_zero]
    exact (u.adicCompletionIntegers ℚ).zero_mem
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen 0 h0
  refine ⟨ε, hε, fun z hz ↦ hball ?_⟩
  simpa [Metric.mem_ball, dist_zero_right] using hz

/-- The adelic trace of a diagonal element is the diagonal image of its field trace. -/
private theorem adeleTrace_algebraMap (x : F) :
    letI := (rationalAdeleEmbedding F).toAlgebra
    Algebra.trace 𝔸[ℚ] 𝔸[F] (algebraMap F 𝔸[F] x) =
      algebraMap ℚ 𝔸[ℚ] (Algebra.trace ℚ F x) := by
  classical
  let ι := Module.Free.ChooseBasisIndex ℤ (𝓞 F)
  let dQ := algebraMap ℚ 𝔸[ℚ]
  let dF := algebraMap F 𝔸[F]
  let : Algebra 𝔸[ℚ] 𝔸[F] := (rationalAdeleEmbedding F).toAlgebra
  obtain ⟨b, hb⟩ := exists_adelicIntegralBasis F
  let c := integralBasis F
  have hdiag (q : ι → ℚ) : b.equivFun.symm (dQ ∘ q) = dF (c.equivFun.symm q) := by
    rw [Module.Basis.equivFun_symm_apply, Module.Basis.equivFun_symm_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [hb, Function.comp_apply, Algebra.smul_def, map_mul]
    exact congrArg (· * dF (c i)) ((rationalAdeleEmbedding_spec F).2.1 (q i))
  have hrepr (x : F) (i : ι) : b.repr (dF x) i = dQ (c.repr x i) := by
    have h := hdiag (c.equivFun x)
    rw [LinearEquiv.symm_apply_apply] at h
    rw [← h, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    rfl
  change Algebra.trace 𝔸[ℚ] 𝔸[F] (dF x) = _
  rw [Algebra.trace_eq_matrix_trace b, Algebra.trace_eq_matrix_trace c, AddMonoidHom.map_trace]
  congr 1
  ext i j
  change (Algebra.leftMulMatrix b (dF x)) i j = dQ ((Algebra.leftMulMatrix c x) i j)
  rw [Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul, hb, ← map_mul, hrepr]

/-- The component at a rational prime of an adelic trace only sees the places above it. -/
private theorem adeleTrace_eval_eq_sum (u : Primes(ℚ)) (S : Finset (Primes(F)))
    (hS : ∀ w : Primes(F),
      u.asIdeal = w.asIdeal.comap (RingOfIntegers.mapRingHom (algebraMap ℚ F)) → w ∈ S)
    (a : 𝔸[F]) :
    letI := (rationalAdeleEmbedding F).toAlgebra
    finiteAdeleEval ℚ u (Algebra.trace 𝔸[ℚ] 𝔸[F] a) =
      ∑ w ∈ S, finiteAdeleEval ℚ u (Algebra.trace 𝔸[ℚ] 𝔸[F]
        (finiteAdeleSingle F w (finiteAdeleEval F w a))) := by
  let := (rationalAdeleEmbedding F).toAlgebra
  let T := Algebra.trace 𝔸[ℚ] 𝔸[F]
  let e : 𝔸[ℚ] := finiteAdeleSingle ℚ u 1
  let a' : 𝔸[F] := ∑ w ∈ S, finiteAdeleSingle F w (finiteAdeleEval F w a)
  have hs := rationalAdeleEmbedding_spec F
  have hz : rationalAdeleEmbedding F e * (a - a') = 0 := by
    apply Prod.ext
    · funext w
      change (rationalAdeleEmbedding F e).1 w * (a - a').1 w = 0
      rw [hs.2.2.1 w e rfl, zero_mul]
    · apply FiniteAdeleRing.ext
      intro w
      change finiteAdeleEval F w (rationalAdeleEmbedding F e * (a - a')) = 0
      by_cases hw : w ∈ S
      · have h : finiteAdeleEval F w a' = finiteAdeleEval F w a := by
          rw [map_sum, Finset.sum_eq_single w]
          · exact RestrictedProduct.single_eq_same (O(F)) w _
          · intro w' _ hw'
            exact RestrictedProduct.single_eq_of_ne (O(F)) _ (Ne.symm hw')
          · exact fun h ↦ (h hw).elim
        rw [map_mul, map_sub, h, sub_self, mul_zero]
      · have h : finiteAdeleEval F w (rationalAdeleEmbedding F e) = 0 := by
          refine hs.2.2.2 (w.under (𝓞 ℚ)) w rfl e ?_
          change RestrictedProduct.single (O(ℚ)) u 1 (w.under (𝓞 ℚ)) = 0
          refine RestrictedProduct.single_eq_of_ne (O(ℚ)) _ fun h ↦ hw (hS w ?_)
          rw [← h]
          rfl
        rw [map_mul, h, zero_mul]
  have hT : e • T (a - a') = 0 := by
    rw [← map_smul, Algebra.smul_def]
    change T (rationalAdeleEmbedding F e * (a - a')) = 0
    rw [hz, map_zero]
  have he : finiteAdeleEval ℚ u e = 1 := RestrictedProduct.single_eq_same (O(ℚ)) u 1
  have h0 : finiteAdeleEval ℚ u (T (a - a')) = 0 := by
    have := congrArg (finiteAdeleEval ℚ u) hT
    rwa [smul_eq_mul, map_mul, he, one_mul, map_zero] at this
  rw [map_sub, map_sub, sub_eq_zero] at h0
  change finiteAdeleEval ℚ u (T a) = _
  rw [h0, map_sum, map_sum]

/-- Only finitely many primes lie above a given rational prime. -/
private theorem finite_primesAbove (u : Primes(ℚ)) :
    {w : Primes(F) |
      u.asIdeal = w.asIdeal.comap (RingOfIntegers.mapRingHom (algebraMap ℚ F))}.Finite := by
  let I : Ideal (𝓞 F) := u.asIdeal.map (RingOfIntegers.mapRingHom (algebraMap ℚ F))
  have hI : I ≠ 0 := by
    intro h
    apply u.ne_bot
    refine (Ideal.map_eq_bot_iff_of_injective (f := RingOfIntegers.mapRingHom (algebraMap ℚ F))
      fun a b hab ↦ RingOfIntegers.ext ((algebraMap ℚ F).injective ?_)).mp h
    rw [← RingOfIntegers.mapRingHom_apply, ← RingOfIntegers.mapRingHom_apply, hab]
  refine (Ideal.finite_factors hI).subset fun w hw ↦ ?_
  change w.asIdeal ∣ I
  rw [Ideal.dvd_iff_le]
  exact Ideal.map_le_iff_le_comap.mpr (le_of_eq hw)

/-- Local-global compatibility of traces: up to local integers, the local trace at `v`
of a global element is its field trace once it is small at the other places above `u`. -/
private theorem trace_localGlobal (v : Primes(F)) (u : Primes(ℚ))
    (hu : u.asIdeal = v.asIdeal.comap (RingOfIntegers.mapRingHom (algebraMap ℚ F)))
    (j : u.adicCompletion ℚ →+* v.adicCompletion F) (hj : Continuous j)
    (hdiag : ∀ r : ℚ, j (algebraMap ℚ (u.adicCompletion ℚ) r) =
      algebraMap F (v.adicCompletion F) (algebraMap ℚ F r)) :
    letI := j.toAlgebra
    ∃ ε : Primes(F) → ℝ, (∀ w, 0 < ε w) ∧ ∀ x : F,
      (∀ w : Primes(F), w ≠ v →
        u.asIdeal = w.asIdeal.comap (RingOfIntegers.mapRingHom (algebraMap ℚ F)) →
          ‖algebraMap F (w.adicCompletion F) x‖ < ε w) →
      Algebra.trace (u.adicCompletion ℚ) (v.adicCompletion F) (algebraMap F (v.adicCompletion F) x) -
        algebraMap ℚ (u.adicCompletion ℚ) (Algebra.trace ℚ F x) ∈ u.adicCompletionIntegers ℚ := by
  let := j.toAlgebra
  let := (rationalAdeleEmbedding F).toAlgebra
  let T := Algebra.trace 𝔸[ℚ] 𝔸[F]
  let P := finiteAdeleEval ℚ u
  obtain ⟨b⟩ := rationalAdeleEmbedding_hasBasis F
  have hp : Surjective P := fun z ↦
    ⟨finiteAdeleSingle ℚ u z, RestrictedProduct.single_eq_same (O(ℚ)) u z⟩
  have hloc (w : Primes(F))
      (hw : u.asIdeal = w.asIdeal.comap (RingOfIntegers.mapRingHom (algebraMap ℚ F))) :
      ∃ ε > 0, ∀ z : w.adicCompletion F, ‖z‖ < ε →
        P (T (finiteAdeleSingle F w z)) ∈ u.adicCompletionIntegers ℚ := by
    obtain ⟨jw, hjw, -, hlocalw⟩ := exists_finiteAdeleEmbedding F w u hw
    let := jw.toAlgebra
    obtain ⟨hfinite, htrace⟩ := trace_of_algebra_projection b P hp (finiteAdeleEval F w)
      (finiteAdeleSingle F w) (fun z ↦ RestrictedProduct.single_eq_same (O(F)) w z) hlocalw
      (finiteAdeleSingle_mul F w)
    obtain ⟨ε, hε, hball⟩ := exists_ball_trace_mem F w u jw hjw hfinite
    exact ⟨ε, hε, fun z hz ↦ (htrace z).symm ▸ hball z hz⟩
  have hv (z : v.adicCompletion F) : P (T (finiteAdeleSingle F v z)) =
      Algebra.trace (u.adicCompletion ℚ) (v.adicCompletion F) z := by
    obtain ⟨jv, hjv, hdiagv, hlocalv⟩ := exists_finiteAdeleEmbedding F v u hu
    have hjj : j = jv := by
      apply RingHom.ext
      intro r
      exact congrFun ((HeightOneSpectrum.denseRange_algebraMap (K := ℚ) (v := u)).equalizer
        hj hjv (funext fun q ↦ (hdiag q).trans (hdiagv q).symm)) r
    subst hjj
    exact (trace_of_algebra_projection b P hp (finiteAdeleEval F v)
      (finiteAdeleSingle F v) (fun z ↦ RestrictedProduct.single_eq_same (O(F)) v z) hlocalv
      (finiteAdeleSingle_mul F v)).2 z
  let ε (w : Primes(F)) : ℝ :=
    if hw : u.asIdeal = w.asIdeal.comap (RingOfIntegers.mapRingHom (algebraMap ℚ F)) then
      Classical.choose (hloc w hw) else 1
  have hε (w : Primes(F)) : 0 < ε w := by
    by_cases hw : u.asIdeal = w.asIdeal.comap (RingOfIntegers.mapRingHom (algebraMap ℚ F))
    · simp only [ε, dite_eq_left hw]
      exact (Classical.choose_spec (hloc w hw)).1
    · simp only [ε, dite_eq_right hw]
      exact one_pos
  refine ⟨ε, hε, fun x hx ↦ ?_⟩
  let S := (finite_primesAbove F u).toFinset
  have hS (w : Primes(F))
      (hw : u.asIdeal = w.asIdeal.comap (RingOfIntegers.mapRingHom (algebraMap ℚ F))) : w ∈ S :=
    (finite_primesAbove F u).mem_toFinset.mpr hw
  have hsum := adeleTrace_eval_eq_sum F u S hS (algebraMap F 𝔸[F] x)
  rw [adeleTrace_algebraMap] at hsum
  change algebraMap ℚ (u.adicCompletion ℚ) (Algebra.trace ℚ F x) =
    ∑ w ∈ S, P (T (finiteAdeleSingle F w (algebraMap F (w.adicCompletion F) x))) at hsum
  rw [hsum, ← Finset.add_sum_erase S _ (hS v hu), hv, sub_add_cancel_left]
  refine neg_mem (sum_mem fun w hw ↦ ?_)
  obtain ⟨hwv, hwS⟩ := Finset.mem_erase.mp hw
  have hwu := (finite_primesAbove F u).mem_toFinset.mp hwS
  refine (Classical.choose_spec (hloc w hwu)).2 _ ?_
  have h := hx w hwv hwu
  have hεw : ε w = Classical.choose (hloc w hwu) := dite_eq_left hwu
  rwa [hεw] at h

private theorem norm_algebraMap_adicCompletion (v : Primes(F)) (k : F) :
    ‖algebraMap F (v.adicCompletion F) k‖ =
      (WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero v) (v.valuation F k) : ℝ) := by
  rw [FinitePlace.norm_def, show algebraMap F (v.adicCompletion F) k = (k : v.adicCompletion F)
    from rfl, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']

/-- Global integers are dense in the local integers. -/
private theorem exists_integer_near (v : Primes(F)) (b : v.adicCompletion F) (hb : ‖b‖ ≤ 1)
    {η : ℝ} (hη : 0 < η) :
    ∃ a : 𝓞 F, ‖b - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)‖ < η := by
  have hq : (1 : ℝ) < v.asIdeal.absNorm := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  obtain ⟨f, hf⟩ : ∃ f : F, ‖b - algebraMap F (v.adicCompletion F) f‖ < min (η / 2) 1 := by
    obtain ⟨f, hf⟩ := Metric.denseRange_iff.mp
      (HeightOneSpectrum.denseRange_algebraMap (K := F) (v := v)) b _
      (lt_min (half_pos hη) one_pos)
    exact ⟨f, by rwa [dist_eq_norm] at hf⟩
  have hf1 : ‖algebraMap F (v.adicCompletion F) f‖ ≤ 1 := by
    have h := IsUltrametricDist.norm_add_le_max b (algebraMap F (v.adicCompletion F) f - b)
    rw [add_sub_cancel] at h
    refine h.trans (max_le hb ?_)
    rw [norm_sub_rev]
    exact (hf.trans_le (min_le_right _ _)).le
  have hfv : v.valuation F f ≤ 1 := by
    rw [norm_algebraMap_adicCompletion] at hf1
    exact (WithZeroMulInt.toNNReal_le_one_iff (HeightOneSpectrum.one_lt_absNorm_nnreal v)).mp
      (by exact_mod_cast hf1)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (half_pos hη) (inv_lt_one_of_one_lt₀ hq)
  obtain ⟨a, ha⟩ := HeightOneSpectrum.exists_valuation_sub_lt_of_integer (K := F) v hfv
    (Units.mk0 (WithZero.exp (-(n : ℤ))) WithZero.exp_ne_zero)
  refine ⟨a, ?_⟩
  have hfa : ‖algebraMap F (v.adicCompletion F) f -
      algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)‖ < η / 2 := by
    rw [norm_sub_rev, ← map_sub, norm_algebraMap_adicCompletion]
    have h1 := (WithZeroMulInt.toNNReal_strictMono (HeightOneSpectrum.one_lt_absNorm_nnreal v)) ha
    rw [Units.val_mk0, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero,
      WithZero.log_exp] at h1
    calc _ < (((v.asIdeal.absNorm : ℝ≥0) ^ (-(n : ℤ)) : ℝ≥0) : ℝ) := NNReal.coe_lt_coe.mpr h1
      _ = (v.asIdeal.absNorm : ℝ)⁻¹ ^ n := by
        push_cast
        rw [zpow_neg, zpow_natCast, inv_pow]
      _ < η / 2 := hn
  calc _ ≤ ‖b - algebraMap F (v.adicCompletion F) f‖ + ‖algebraMap F (v.adicCompletion F) f -
        algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < η / 2 + η / 2 := add_lt_add (hf.trans_le (min_le_left _ _)) hfa
    _ = η := add_halves η

/-- An element of a given ideal that is a unit at `v` and small at finitely many other places. -/
private theorem exists_mem_notMem_small (v : Primes(F)) (I : Ideal (𝓞 F)) (hI : ¬ I ≤ v.asIdeal)
    (T : Finset (Primes(F))) (η : Primes(F) → ℝ) (hη : ∀ w, 0 < η w) :
    ∃ s ∈ I, s ∉ v.asIdeal ∧ ∀ w ∈ T, w ≠ v →
      ‖algebraMap F (w.adicCompletion F) (algebraMap (𝓞 F) F s)‖ < η w := by
  have hL (w : Primes(F)) : ∃ L : ℕ, (w.asIdeal.absNorm : ℝ) ^ (-(L : ℤ)) < η w := by
    have hq : (1 : ℝ) < w.asIdeal.absNorm := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm w
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (hη w) (inv_lt_one_of_one_lt₀ hq)
    exact ⟨n, by rwa [zpow_neg, zpow_natCast, ← inv_pow]⟩
  choose L hL using hL
  have hM : ¬ (∏ w ∈ T.erase v, w.asIdeal ^ L w) ≤ v.asIdeal := by
    rw [Ideal.IsPrime.prod_le v.isPrime]
    rintro ⟨w, hw, hle⟩
    have hwv := (Finset.mem_erase.mp hw).1
    have hwle : w.asIdeal ≤ v.asIdeal := v.isPrime.le_of_pow_le hle
    exact hwv (HeightOneSpectrum.ext (w.isMaximal.eq_of_le v.isPrime.ne_top hwle))
  have hIM : ¬ I * (∏ w ∈ T.erase v, w.asIdeal ^ L w) ≤ v.asIdeal := by
    rw [Ideal.IsPrime.mul_le v.isPrime]
    exact not_or.mpr ⟨hI, hM⟩
  obtain ⟨s, hs, hsv⟩ : ∃ s ∈ I * (∏ w ∈ T.erase v, w.asIdeal ^ L w), s ∉ v.asIdeal := by
    by_contra hcon
    exact hIM fun s hs ↦ by_contra fun hsv ↦ hcon ⟨s, hs, hsv⟩
  have hsI : s ∈ I := (Ideal.mul_le_left : I * (∏ w ∈ T.erase v, w.asIdeal ^ L w) ≤ I) hs
  have hsM : s ∈ ∏ w ∈ T.erase v, w.asIdeal ^ L w :=
    (Ideal.mul_le_right : I * (∏ w ∈ T.erase v, w.asIdeal ^ L w) ≤ _) hs
  refine ⟨s, hsI, hsv, fun w hw hwv ↦ ?_⟩
  have hsw : s ∈ w.asIdeal ^ L w :=
    Ideal.le_of_dvd (Finset.dvd_prod_of_mem (fun w : Primes(F) ↦ w.asIdeal ^ L w)
      (Finset.mem_erase.mpr ⟨hwv, hw⟩)) hsM
  exact ((norm_coe_le_zpow_iff F w s (L w)).mpr hsw).trans_lt (hL w)

/-- An element of the different with the exact `v`-adic order. -/
private theorem exists_different_witness (v : Primes(F)) :
    ∃ δ ∈ differentIdeal ℤ (𝓞 F), δ ∈ v.asIdeal ^ differentExp(F, v) ∧
      δ ∉ v.asIdeal ^ (differentExp(F, v) + 1) := by
  have hD : differentIdeal ℤ (𝓞 F) ≠ ⊥ := differentIdeal_ne_bot
  have hfin : FiniteMultiplicity v.asIdeal (differentIdeal ℤ (𝓞 F)) :=
    FiniteMultiplicity.of_prime_left v.prime hD
  have hle : differentIdeal ℤ (𝓞 F) ≤ v.asIdeal ^ differentExp(F, v) :=
    Ideal.le_of_dvd (pow_multiplicity_dvd _ _)
  have hnle : ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal ^ (differentExp(F, v) + 1) := fun h ↦
    hfin.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self _) (Ideal.dvd_iff_le.mpr h)
  obtain ⟨δ, hδ, hδv⟩ := IsConcreteLE.not_le_iff_exists.mp hnle
  exact ⟨δ, hδ, hle hδ, hδv⟩

private theorem norm_of_exact_order (v : Primes(F)) (δ : 𝓞 F) (n : ℕ) (h1 : δ ∈ v.asIdeal ^ n)
    (h2 : δ ∉ v.asIdeal ^ (n + 1)) :
    ‖algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F δ)‖ =
      (v.asIdeal.absNorm : ℝ) ^ (-(n : ℤ)) := by
  have hq : (1 : ℝ) < v.asIdeal.absNorm := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hle := (norm_coe_le_zpow_iff F v δ n).mpr h1
  have hlt : ¬ _ := mt (norm_coe_le_zpow_iff F v δ (n + 1)).mp h2
  have hne : algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F δ) ≠ 0 := by
    intro h0
    apply hlt
    rw [h0, norm_zero]
    positivity
  rw [norm_adicCompletion_eq_zpow F v hne] at hle hlt ⊢
  rw [zpow_le_zpow_iff_right₀ hq] at hle
  rw [not_le, zpow_lt_zpow_iff_right₀ hq] at hlt
  congr 1
  push_cast at hlt
  omega

open scoped nonZeroDivisors in
/-- Membership in the inverse different, as a trace condition and as a multiplier condition. -/
private theorem trace_int_iff_mul_different (x : F) :
    (∀ a : 𝓞 F, Algebra.trace ℚ F (x * algebraMap (𝓞 F) F a) ∈ (algebraMap ℤ ℚ).range) ↔
      ∀ δ ∈ differentIdeal ℤ (𝓞 F), x * algebraMap (𝓞 F) F δ ∈ (algebraMap (𝓞 F) F).range := by
  have hD : (differentIdeal ℤ (𝓞 F) : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := by
    rw [ne_eq, FractionalIdeal.coeIdeal_eq_zero]
    exact differentIdeal_ne_bot
  have h1 : x ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) ↔
      ∀ a : 𝓞 F, Algebra.trace ℚ F (x * algebraMap (𝓞 F) F a) ∈ (algebraMap ℤ ℚ).range := by
    rw [FractionalIdeal.mem_dual one_ne_zero]
    constructor
    · intro h a
      exact h _ (FractionalIdeal.mem_one_iff _ |>.mpr ⟨a, rfl⟩)
    · intro h a ha
      obtain ⟨a', rfl⟩ := (FractionalIdeal.mem_one_iff _).mp ha
      exact h a'
  have h2 : x ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) ↔
      ∀ δ ∈ differentIdeal ℤ (𝓞 F), x * algebraMap (𝓞 F) F δ ∈ (algebraMap (𝓞 F) F).range := by
    rw [← inv_inv (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F)),
      ← coeIdeal_differentIdeal (A := ℤ) (K := ℚ) (L := F) (B := 𝓞 F), FractionalIdeal.mem_inv_iff hD]
    constructor
    · intro h δ hδ
      obtain ⟨y, hy⟩ := (FractionalIdeal.mem_one_iff _).mp
        (h _ (FractionalIdeal.mem_coeIdeal _ |>.mpr ⟨δ, hδ, rfl⟩))
      exact ⟨y, hy⟩
    · intro h y hy
      obtain ⟨δ, hδ, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hy
      obtain ⟨z, hz⟩ := h δ hδ
      exact (FractionalIdeal.mem_one_iff _).mpr ⟨z, hz⟩
  rw [← h1, h2]

private theorem norm_coe_int_le_one (v : Primes(F)) (a : 𝓞 F) :
    ‖algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)‖ ≤ 1 := by
  rw [norm_algebraMap_adicCompletion, HeightOneSpectrum.valuation_of_algebraMap]
  exact_mod_cast (WithZeroMulInt.toNNReal_le_one_iff
    (HeightOneSpectrum.one_lt_absNorm_nnreal v)).mpr (v.intValuation_le_one a)

private theorem norm_coe_int_eq_one (v : Primes(F)) (a : 𝓞 F) (ha : a ∉ v.asIdeal) :
    ‖algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)‖ = 1 := by
  rw [norm_algebraMap_adicCompletion, HeightOneSpectrum.valuation_of_algebraMap,
    (v.intValuation_eq_one_iff_mem_primeCompl a).mpr ha, map_one, NNReal.coe_one]

/-- Elements of the inverse different have `v`-adic norm at most `qᵥ^dᵥ`. -/
private theorem norm_le_of_mul_different (v : Primes(F)) (x : F)
    (hx : ∀ δ ∈ differentIdeal ℤ (𝓞 F), x * algebraMap (𝓞 F) F δ ∈ (algebraMap (𝓞 F) F).range) :
    ‖algebraMap F (v.adicCompletion F) x‖ ≤ (v.asIdeal.absNorm : ℝ) ^ differentExp(F, v) := by
  obtain ⟨δ, hδ, h1, h2⟩ := exists_different_witness F v
  have hn := norm_of_exact_order F v δ _ h1 h2
  obtain ⟨a, ha⟩ := hx δ hδ
  have hq : (0 : ℝ) < v.asIdeal.absNorm := by
    exact_mod_cast zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v)
  have hle : ‖algebraMap F (v.adicCompletion F) x‖ *
      ‖algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F δ)‖ ≤ 1 := by
    rw [← norm_mul, ← map_mul, ← ha]
    exact norm_coe_int_le_one F v a
  rw [hn, zpow_neg, zpow_natCast, ← div_eq_mul_inv, div_le_one (pow_pos hq _)] at hle
  exact hle

/-- An element of the inverse different of exact `v`-adic norm `qᵥ^dᵥ`, small at finitely
many other places. -/
private theorem exists_inverseDifferent_small (v : Primes(F)) (T : Finset (Primes(F)))
    (η : Primes(F) → ℝ) (hη : ∀ w, 0 < η w) :
    ∃ x : F, (∀ δ ∈ differentIdeal ℤ (𝓞 F),
        x * algebraMap (𝓞 F) F δ ∈ (algebraMap (𝓞 F) F).range) ∧
      ‖algebraMap F (v.adicCompletion F) x‖ = (v.asIdeal.absNorm : ℝ) ^ differentExp(F, v) ∧
      ∀ w ∈ T, w ≠ v → ‖algebraMap F (w.adicCompletion F) x‖ < η w := by
  obtain ⟨δ, hδ, h1, h2⟩ := exists_different_witness F v
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    exact h2 (Ideal.zero_mem _)
  have hδF : algebraMap (𝓞 F) F δ ≠ 0 := fun h ↦ hδ0 (RingOfIntegers.coe_injective (by
    rw [h, map_zero]))
  obtain ⟨E, hE⟩ : differentIdeal ℤ (𝓞 F) ∣ Ideal.span {δ} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hδ)
  have hEv : ¬ E ≤ v.asIdeal := by
    intro hle
    apply h2
    have hspan : Ideal.span {δ} ≤ v.asIdeal ^ (differentExp(F, v) + 1) := by
      rw [hE, pow_succ]
      exact Ideal.mul_mono (Ideal.le_of_dvd (pow_multiplicity_dvd _ _)) hle
    exact hspan (Ideal.mem_span_singleton_self δ)
  have hδw (w : Primes(F)) : 0 < ‖algebraMap F (w.adicCompletion F) (algebraMap (𝓞 F) F δ)‖ :=
    norm_pos_iff.mpr ((map_ne_zero _).mpr hδF)
  obtain ⟨c, hcE, hcv, hcw⟩ := exists_mem_notMem_small F v E hEv T
    (fun w ↦ η w * ‖algebraMap F (w.adicCompletion F) (algebraMap (𝓞 F) F δ)‖)
    (fun w ↦ mul_pos (hη w) (hδw w))
  refine ⟨algebraMap (𝓞 F) F c / algebraMap (𝓞 F) F δ, ?_, ?_, ?_⟩
  · intro δ' hδ'
    have hmem : c * δ' ∈ Ideal.span {δ} := by
      rw [hE, mul_comm c]
      exact Ideal.mul_mem_mul hδ' hcE
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hmem
    refine ⟨t, ?_⟩
    rw [div_mul_eq_mul_div, eq_div_iff hδF, ← map_mul, ← map_mul, ht]
  · rw [map_div₀, norm_div, norm_coe_int_eq_one F v c hcv, norm_of_exact_order F v δ _ h1 h2,
      zpow_neg, zpow_natCast, one_div, inv_inv]
  · intro w hw hwv
    rw [map_div₀, norm_div, div_lt_iff₀ (hδw w)]
    exact hcw w hw hwv

private theorem natGenerator_dvd_iff' (u : Primes(ℚ)) (n : ℕ) :
    Rat.HeightOneSpectrum.natGenerator u ∣ n ↔ (n : 𝓞 ℚ) ∈ u.asIdeal := by
  rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff, Ideal.mem_map_of_equiv]
  constructor
  · rintro ⟨y, hy, hy'⟩
    have hyn : y = (n : 𝓞 ℚ) :=
      (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).injective (by rw [hy', map_natCast])
    rwa [← hyn]
  · intro h
    exact ⟨n, h, map_natCast _ n⟩

/-- A rational number which is integral at `u` and has a denominator dividing a power
of the prime below `u` is an integer. -/
private theorem rat_mem_range_of (u : Primes(ℚ)) (r : ℚ) (k : ℕ)
    (hk : ((Rat.HeightOneSpectrum.natGenerator u : ℚ) ^ k * r) ∈ (algebraMap ℤ ℚ).range)
    (hr : algebraMap ℚ (u.adicCompletion ℚ) r ∈ u.adicCompletionIntegers ℚ) :
    r ∈ (algebraMap ℤ ℚ).range := by
  have hp : (Rat.HeightOneSpectrum.natGenerator u).Prime :=
    Rat.HeightOneSpectrum.prime_natGenerator u
  have hval : u.valuation ℚ r ≤ 1 := by
    have h := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ u).mp hr
    have hcoe : algebraMap ℚ (u.adicCompletion ℚ) r = FinitePlace.embedding u r :=
      RingHom.congr_fun (Subsingleton.elim (algebraMap ℚ (u.adicCompletion ℚ))
        (FinitePlace.embedding u)) r
    rwa [hcoe, FinitePlace.embedding_apply,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h
  have hden : ((r.den : ℕ) : 𝓞 ℚ) ∉ u.asIdeal := Rat.valuation_le_one_iff_den.mp hval
  obtain ⟨n, hn⟩ := hk
  have hdvd : r.den ∣ Rat.HeightOneSpectrum.natGenerator u ^ k := by
    have hpk : ((Rat.HeightOneSpectrum.natGenerator u : ℚ) ^ k) ≠ 0 :=
      pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
    have hr' : r = Rat.divInt n ((Rat.HeightOneSpectrum.natGenerator u : ℤ) ^ k) := by
      rw [Rat.divInt_eq_div]
      push_cast
      rw [eq_div_iff hpk, mul_comm]
      simpa using hn.symm
    have h := Rat.den_dvd n ((Rat.HeightOneSpectrum.natGenerator u : ℤ) ^ k)
    rw [← hr'] at h
    exact_mod_cast h
  have hndvd : ¬ Rat.HeightOneSpectrum.natGenerator u ∣ r.den := fun h ↦
    hden ((natGenerator_dvd_iff' u r.den).mp h)
  have hcop : Nat.Coprime r.den (Rat.HeightOneSpectrum.natGenerator u ^ k) :=
    (Nat.Coprime.pow_left k (hp.coprime_iff_not_dvd.mpr hndvd)).symm
  have hden1 : r.den = 1 := hcop.eq_one_of_dvd hdvd
  exact ⟨r.num, by simpa using Rat.intCast_num_of_den_eq_one hden1⟩

/-- Paper: Example A.3.1.10, p. 558. The trace dual of the local integer ring consists
of the elements that pair integrally with every local integer. It is the closed ball
of radius `qᵥ^dᵥ`, where `dᵥ` is the exponent in the global different. -/
theorem finiteLocalTraceDual_eq_closedBall (v : Primes(F)) (u : Primes(ℚ))
    (hu : u.asIdeal = v.asIdeal.comap (RingOfIntegers.mapRingHom (algebraMap ℚ F)))
    (j : u.adicCompletion ℚ →+* v.adicCompletion F) (hj : Continuous j)
    (hdiag : ∀ r : ℚ, j (algebraMap ℚ (u.adicCompletion ℚ) r) =
      algebraMap F (v.adicCompletion F) (algebraMap ℚ F r)) :
    letI := j.toAlgebra
    Module.Finite (u.adicCompletion ℚ) (v.adicCompletion F) →
      ∀ y : v.adicCompletion F,
        (∀ x ∈ v.adicCompletionIntegers F,
          Algebra.trace (u.adicCompletion ℚ) (v.adicCompletion F) (x * y) ∈
            u.adicCompletionIntegers ℚ) ↔
        ‖y‖ ≤ (v.asIdeal.absNorm : ℝ) ^ differentExp(F, v) := by
  let := j.toAlgebra
  intro hfinite y
  have hq1 : (1 : ℝ) < v.asIdeal.absNorm := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hq0 : (0 : ℝ) < v.asIdeal.absNorm := zero_lt_one.trans hq1
  obtain ⟨ε, hε, hLG⟩ := trace_localGlobal F v u hu j hj hdiag
  obtain ⟨εv, hεv, hball⟩ := exists_ball_trace_mem F v u j hj hfinite
  have hT (w : Primes(F))
      (hw : u.asIdeal = w.asIdeal.comap (RingOfIntegers.mapRingHom (algebraMap ℚ F))) :
      w ∈ (finite_primesAbove F u).toFinset :=
    (finite_primesAbove F u).mem_toFinset.mpr hw
  have hmemO (z : v.adicCompletion F) : z ∈ v.adicCompletionIntegers F ↔ ‖z‖ ≤ 1 := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v]
    exact Valued.toNormedField.norm_le_one_iff.symm
  have hmod (y z : v.adicCompletion F)
      (hy : ∀ x ∈ v.adicCompletionIntegers F, Algebra.trace (u.adicCompletion ℚ)
        (v.adicCompletion F) (x * y) ∈ u.adicCompletionIntegers ℚ) (hzy : ‖z‖ ≤ ‖y‖) :
      ∀ x ∈ v.adicCompletionIntegers F, Algebra.trace (u.adicCompletion ℚ)
        (v.adicCompletion F) (x * z) ∈ u.adicCompletionIntegers ℚ := by
    intro x hx
    by_cases hy0 : y = 0
    · rw [hy0, norm_zero, norm_le_zero_iff] at hzy
      rw [hzy, mul_zero, map_zero]
      exact (u.adicCompletionIntegers ℚ).zero_mem
    · have hzy' : z / y ∈ v.adicCompletionIntegers F := (hmemO _).mpr (by
        rw [norm_div, div_le_one (norm_pos_iff.mpr hy0)]
        exact hzy)
      have h := hy (x * (z / y)) (mul_mem hx hzy')
      rwa [mul_assoc, div_mul_cancel₀ z hy0] at h
  have hintZ (t : ℚ) (ht : t ∈ (algebraMap ℤ ℚ).range) :
      algebraMap ℚ (u.adicCompletion ℚ) t ∈ u.adicCompletionIntegers ℚ := by
    obtain ⟨n, rfl⟩ := ht
    rw [show algebraMap ℚ (u.adicCompletion ℚ) (algebraMap ℤ ℚ n) = (n : u.adicCompletion ℚ) by
      simp]
    exact intCast_mem _ n
  have hsmall (x : F) (hx : ∀ w ∈ (finite_primesAbove F u).toFinset, w ≠ v →
      ‖algebraMap F (w.adicCompletion F) x‖ < ε w) (a : 𝓞 F) (w : Primes(F)) (hwv : w ≠ v)
      (hwu : u.asIdeal = w.asIdeal.comap (RingOfIntegers.mapRingHom (algebraMap ℚ F))) :
      ‖algebraMap F (w.adicCompletion F) (x * algebraMap (𝓞 F) F a)‖ < ε w := by
    rw [map_mul, norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (norm_coe_int_le_one F w a)).trans_lt
      (hx w (hT w hwu) hwv)
  constructor
  · intro hy
    by_contra hlt'
    have hlt := not_le.mp hlt'
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [norm_zero] at hlt
      exact (pow_pos hq0 _).not_gt hlt
    let p := Rat.HeightOneSpectrum.natGenerator u
    have hp : p.Prime := Rat.HeightOneSpectrum.prime_natGenerator u
    have hpF : (p : F) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hpL : (p : v.adicCompletion F) ≠ 0 := by
      rw [← map_natCast (algebraMap F (v.adicCompletion F))]
      exact (map_ne_zero _).mpr hpF
    have hpv : (p : 𝓞 F) ∈ v.asIdeal := by
      have h := (natGenerator_dvd_iff' u p).mp dvd_rfl
      rw [hu, Ideal.mem_comap, map_natCast] at h
      exact h
    have hpn : ‖(p : v.adicCompletion F)‖ < 1 := by
      have h := (norm_coe_le_zpow_iff F v (p : 𝓞 F) 1).mpr (by rw [pow_one]; exact hpv)
      rw [map_natCast, map_natCast, Nat.cast_one, zpow_neg, zpow_one] at h
      exact h.trans_lt (inv_lt_one_of_one_lt₀ hq1)
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr (norm_pos_iff.mpr hy0)) hpn
    let b : v.adicCompletion F := (p : v.adicCompletion F) ^ k * y
    have hbn : ‖b‖ = ‖(p : v.adicCompletion F)‖ ^ k * ‖y‖ := by
      rw [norm_mul, norm_pow]
    have hb : ‖b‖ ≤ 1 := by
      rw [hbn]
      calc _ ≤ ‖y‖⁻¹ * ‖y‖ := mul_le_mul_of_nonneg_right hk.le (norm_nonneg _)
        _ = 1 := inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy0)
    have hbpos : 0 < ‖b‖ := norm_pos_iff.mpr (mul_ne_zero (pow_ne_zero _ hpL) hy0)
    obtain ⟨a, ha⟩ := exists_integer_near F v b hb hbpos
    let x1 : F := algebraMap (𝓞 F) F a / (p : F) ^ k
    have hx1 : ‖algebraMap F (v.adicCompletion F) x1 - y‖ < ‖y‖ := by
      have heq : algebraMap F (v.adicCompletion F) x1 - y =
          (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a) - b) /
            (p : v.adicCompletion F) ^ k := by
        rw [eq_div_iff (pow_ne_zero _ hpL)]
        simp only [x1, b, map_div₀, map_pow, map_natCast]
        field_simp
      rw [heq, norm_div, norm_sub_rev, norm_pow,
        div_lt_iff₀ (pow_pos (norm_pos_iff.mpr hpL) k)]
      calc _ < ‖b‖ := ha
        _ = ‖y‖ * ‖(p : v.adicCompletion F)‖ ^ k := by rw [hbn, mul_comm]
    have hx1n : ‖algebraMap F (v.adicCompletion F) x1‖ = ‖y‖ := by
      have h1 := IsUltrametricDist.norm_add_le_max y (algebraMap F (v.adicCompletion F) x1 - y)
      rw [add_sub_cancel] at h1
      have h2 := IsUltrametricDist.norm_add_le_max (algebraMap F (v.adicCompletion F) x1)
        (y - algebraMap F (v.adicCompletion F) x1)
      rw [add_sub_cancel, norm_sub_rev] at h2
      refine le_antisymm (h1.trans (max_le le_rfl hx1.le)) ?_
      rcases le_max_iff.mp h2 with h | h
      · exact h
      · exact absurd (h.trans_lt hx1) (lt_irrefl _)
    obtain ⟨s, -, hsv, hsw⟩ := exists_mem_notMem_small F v ⊤
      (fun h ↦ v.isPrime.ne_top (top_le_iff.mp h)) (finite_primesAbove F u).toFinset
      (fun w ↦ ε w / (‖algebraMap F (w.adicCompletion F) x1‖ + 1))
      (fun w ↦ div_pos (hε w) (by positivity))
    let x : F := x1 * algebraMap (𝓞 F) F s
    have hxv : ‖algebraMap F (v.adicCompletion F) x‖ = ‖y‖ := by
      rw [map_mul, norm_mul, hx1n, norm_coe_int_eq_one F v s hsv, mul_one]
    have hxw : ∀ w ∈ (finite_primesAbove F u).toFinset, w ≠ v →
        ‖algebraMap F (w.adicCompletion F) x‖ < ε w := by
      intro w hw hwv
      have h := hsw w hw hwv
      rw [lt_div_iff₀ (by positivity)] at h
      rw [map_mul, norm_mul]
      nlinarith [norm_nonneg (algebraMap F (w.adicCompletion F) (algebraMap (𝓞 F) F s)),
        norm_nonneg (algebraMap F (w.adicCompletion F) x1)]
    have hxD := hmod y _ hy hxv.le
    have htr (a' : 𝓞 F) :
        Algebra.trace ℚ F (x * algebraMap (𝓞 F) F a') ∈ (algebraMap ℤ ℚ).range := by
      have h1 := hLG (x * algebraMap (𝓞 F) F a') (hsmall x hxw a')
      have h2 : Algebra.trace (u.adicCompletion ℚ) (v.adicCompletion F)
          (algebraMap F (v.adicCompletion F) (x * algebraMap (𝓞 F) F a')) ∈
            u.adicCompletionIntegers ℚ := by
        rw [map_mul, mul_comm]
        exact hxD _ ((hmemO _).mpr (norm_coe_int_le_one F v a'))
      have h3 := (u.adicCompletionIntegers ℚ).sub_mem h2 h1
      rw [sub_sub_cancel] at h3
      refine rat_mem_range_of u _ k ?_ h3
      have hint := (trace_int_iff_mul_different F 1).mpr
        (fun δ _ ↦ ⟨δ, by rw [one_mul]⟩) (a * s * a')
      rw [one_mul] at hint
      have hpk : (p : ℚ) ^ k * Algebra.trace ℚ F (x * algebraMap (𝓞 F) F a') =
          Algebra.trace ℚ F (algebraMap (𝓞 F) F (a * s * a')) := by
        rw [← smul_eq_mul, ← LinearMap.map_smul, Algebra.smul_def]
        congr 1
        simp only [x, x1, map_mul, map_pow, map_natCast]
        field_simp
      rw [hpk]
      exact hint
    exact (not_lt.mpr (norm_le_of_mul_different F v x
      ((trace_int_iff_mul_different F x).mp htr))) (hxv ▸ hlt)
  · intro hy
    obtain ⟨x, hxD, hxv, hxw⟩ := exists_inverseDifferent_small F v
      (finite_primesAbove F u).toFinset ε hε
    have hx0 : algebraMap F (v.adicCompletion F) x ≠ 0 := by
      intro h
      rw [h, norm_zero] at hxv
      exact (pow_pos hq0 _).ne' hxv.symm
    have hxloc : ∀ b ∈ v.adicCompletionIntegers F, Algebra.trace (u.adicCompletion ℚ)
        (v.adicCompletion F) (b * algebraMap F (v.adicCompletion F) x) ∈
          u.adicCompletionIntegers ℚ := by
      intro b hb
      obtain ⟨a, ha⟩ := exists_integer_near F v b ((hmemO b).mp hb)
        (div_pos hεv (norm_pos_iff.mpr hx0))
      have hsplit : b * algebraMap F (v.adicCompletion F) x =
          (b - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) *
            algebraMap F (v.adicCompletion F) x +
          algebraMap F (v.adicCompletion F) (x * algebraMap (𝓞 F) F a) := by
        rw [map_mul]
        ring
      rw [hsplit, map_add]
      refine add_mem (hball _ ?_) ?_
      · rw [norm_mul, ← lt_div_iff₀ (norm_pos_iff.mpr hx0)]
        exact ha
      · have h1 := hLG (x * algebraMap (𝓞 F) F a) (hsmall x hxw a)
        have h2 := hintZ _ ((trace_int_iff_mul_different F x).mpr hxD a)
        have h3 := add_mem h1 h2
        rwa [sub_add_cancel] at h3
    exact hmod _ y hxloc (hy.trans hxv.symm.le)


end FiniteLocalTraceDual

/-- Paper: Example A.3.1.10, p. 558. The annihilator of the local integer ring
under the standard trace pairing is the inverse different.
Deviation: The inverse different is expressed as the ball of radius `qᵥ^dᵥ`,
where `dᵥ` is the exponent of the prime in the global different. -/
theorem finiteLocalStandardCharacter_annihilator_integers (v : Primes(F)) :
    {y : v.adicCompletion F | ∀ x ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F)),
      finiteLocalStandardCharacter F v (x * y) = 1} =
    {y : v.adicCompletion F | ‖y‖ ≤ (v.asIdeal.absNorm : ℝ) ^ differentExp(F, v)} := by
  let u := v.under (𝓞 ℚ)
  obtain ⟨j, hj, hdiag, hfinite, htrace⟩ := finiteLocalStandardCharacter_trace F v u rfl
  let := j.toAlgebra
  change ∀ z, finiteLocalStandardCharacter F v z =
    ratLocalCharacter u (Algebra.trace (u.adicCompletion ℚ) (v.adicCompletion F) z) at htrace
  ext y
  simp only [mem_ofPred_eq, htrace, ratLocalCharacter_eq_one]
  exact finiteLocalTraceDual_eq_closedBall F v u rfl j hj hdiag hfinite y

/-- Paper: Example A.3.1.10, p. 558. The local measure is self-dual under
the local trace character. -/
theorem finiteLocalAdditiveTamagawaMeasure_selfDual (v : Primes(F)) :
    IsTamagawaSelfDual (finiteLocalAdditiveTamagawaMeasure F v)
      (finiteLocalStandardCharacter F v) := by
  let K := v.adicCompletion F
  let G := Multiplicative K
  let : ProperSpace K := properSpace_adicCompletion v
  obtain ⟨ψ, hψ, hNontrivial⟩ := finiteLocalStandardCharacter_exists_continuousMonoidHom F v
  obtain ⟨e, he⟩ := exists_pontryaginDualEquiv_of_normedField ψ hNontrivial
  have he' (x y : K) :
      e (Multiplicative.ofAdd x) (Multiplicative.ofAdd y) =
        finiteLocalStandardCharacter F v (x * y) := (he x y).trans (hψ _)
  refine ⟨e, he', ?_⟩
  let μ : Measure G := finiteLocalAdditiveTamagawaMeasure F v
  have hHaar := finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  let : μ.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := hHaar.toIsFiniteMeasureOnCompacts
      toIsOpenPosMeasure := hHaar.toIsOpenPosMeasure
      map_mul_left_eq_self := fun x ↦ hHaar.map_add_left_eq_self x.toAdd }
  let : μ.Regular := finiteLocalAdditiveTamagawaMeasure_regular F v
  let : MeasurableSpace (PontryaginDual G) := borel _
  let : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  let ν := μ.map e
  let : ν.IsHaarMeasure := e.isHaarMeasure_map μ
  let : ν.Regular := Measure.Regular.map e.toHomeomorph
  let H : Subgroup G := (v.adicCompletionIntegers F).toSubring.toAddSubgroup.toSubgroup
  have hCompact : IsCompact (H : Set G) :=
    isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v)
  have hOpen : IsOpen (H : Set G) := by
    change IsOpen (v.adicCompletionIntegers F : Set K)
    exact Valued.isOpen_valuationSubring (v.adicCompletion F)
  apply isLCAPlancherelMeasure_of_compactOpenSubgroup μ ν H hCompact hOpen
  let A : Set (PontryaginDual G) := {χ | ∀ x ∈ H, χ x = 1}
  have hA : MeasurableSet A := (isClosed_subgroupAnnihilator H).measurableSet
  have hPreimage : (fun y : K ↦ e (Multiplicative.ofAdd y)) ⁻¹' A =
      {y : K | ∀ x ∈ (v.adicCompletionIntegers F : Set K),
        finiteLocalStandardCharacter F v (x * y) = 1} := by
    ext y
    change (∀ x : G, x ∈ H → e (Multiplicative.ofAdd y) x = 1) ↔
      ∀ x ∈ (v.adicCompletionIntegers F : Set K), finiteLocalStandardCharacter F v (x * y) = 1
    constructor
    · intro hy x hx
      have hxH : Multiplicative.ofAdd x ∈ H := hx
      simpa only [he', mul_comm y x] using hy (Multiplicative.ofAdd x) hxH
    · intro hy x hx
      have hxO : x.toAdd ∈ (v.adicCompletionIntegers F : Set K) := hx
      have heval := he' y x.toAdd
      rw [mul_comm y] at heval
      exact heval.trans (hy x.toAdd hxO)
  have hm : Measurable (e : G → PontryaginDual G) := e.continuous.measurable
  change ν A = (μ H)⁻¹
  calc
    ν A = μ ((fun y : K ↦ e (Multiplicative.ofAdd y)) ⁻¹' A) := Measure.map_apply hm hA
    _ = (μ H)⁻¹ := by
      change finiteLocalAdditiveTamagawaMeasure F v
          ((fun y : K ↦ e (Multiplicative.ofAdd y)) ⁻¹' A) =
        (finiteLocalAdditiveTamagawaMeasure F v (v.adicCompletionIntegers F : Set K))⁻¹
      rw [hPreimage, finiteLocalStandardCharacter_annihilator_integers F v]
      exact finiteLocalAdditiveTamagawaMeasure_inverseDifferentBall F v

/-- Paper: Example A.3.1.10, p. 558. The Fourier transform of the local integer-ring
indicator is the inverse-different indicator multiplied by the mass of the integer ring.
Deviation: The inverse different is the closed ball of normalized radius `qᵥ^dᵥ`. -/
theorem finiteLocalTamagawaFourier_integers (v : Primes(F)) :
    tamagawaFourier (finiteLocalAdditiveTamagawaMeasure F v) (finiteLocalStandardCharacter F v)
        ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ ↦ (1 : ℂ))) =
      (differentMass(F, v).toReal : ℂ) •
        ({x : v.adicCompletion F | ‖x‖ ≤ (v.asIdeal.absNorm : ℝ) ^ differentExp(F, v)}.indicator
          (fun _ ↦ (1 : ℂ))) := by
  let u := v.under (𝓞 ℚ)
  obtain ⟨j, hj, hdiag, hfinite, htrace⟩ := finiteLocalStandardCharacter_trace F v u rfl
  let := j.toAlgebra
  let ψ := finiteLocalStandardCharacter F v
  let t := Algebra.trace (u.adicCompletion ℚ) (v.adicCompletion F)
  change ∀ x, ψ x = ratLocalCharacter u (t x) at htrace
  have hadd (x z : v.adicCompletion F) : ψ (x + z) = ψ x * ψ z := by
    simp only [htrace, ratLocalCharacter, map_add, padicStandardCharacter_add]
  let O := v.adicCompletionIntegers F
  let B := {y : v.adicCompletion F | ‖y‖ ≤ (v.asIdeal.absNorm : ℝ) ^ differentExp(F, v)}
  have hB (y : v.adicCompletion F) : y ∈ B ↔ ∀ x ∈ O, ψ (x * y) = 1 := by
    simp_rw [htrace, ratLocalCharacter_eq_one]
    exact (finiteLocalTraceDual_eq_closedBall F v u rfl j hj hdiag hfinite y).symm
  let μ := finiteLocalAdditiveTamagawaMeasure F v
  let : μ.IsAddHaarMeasure := finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  have hO : MeasurableSet (O : Set (v.adicCompletion F)) :=
    (Valued.isOpen_valuationSubring _).measurableSet
  funext y
  let f (x : v.adicCompletion F) : ℂ := star (ψ (x * y) : ℂ)
  let g := (O : Set (v.adicCompletion F)).indicator f
  change (∫ x, (O : Set (v.adicCompletion F)).indicator (fun _ ↦ (1 : ℂ)) x * f x ∂μ) =
    (differentMass(F, v).toReal : ℂ) * B.indicator (fun _ ↦ 1) y
  simp_rw [← Set.indicator_mul_left, one_mul]
  by_cases hy : y ∈ B
  · rw [Set.indicator_of_mem hy, mul_one, integral_indicator hO]
    calc
      (∫ x in (O : Set (v.adicCompletion F)), f x ∂μ) =
          ∫ _ in (O : Set (v.adicCompletion F)), (1 : ℂ) ∂μ := by
        apply setIntegral_congr_fun hO
        intro x hx
        simp [f, (hB y).mp hy x hx]
      _ = _ := by
        rw [setIntegral_const, Complex.real_smul, mul_one, measureReal_def,
          finiteLocalAdditiveTamagawaMeasure_integers F v]
  · obtain ⟨a, ha⟩ := not_forall.mp ((hB y).not.mp hy)
    obtain ⟨ha, hψa⟩ := not_imp.mp ha
    rw [Set.indicator_of_notMem hy, mul_zero]
    change (∫ x, g x ∂μ) = 0
    have hne : f a ≠ 1 := by
      intro h
      apply hψa
      apply Circle.coe_injective
      rw [Circle.coe_one]
      exact star_injective (h.trans (star_one ℂ).symm)
    have htranslate (x : v.adicCompletion F) : g (a + x) = f a * g x := by
      have hmem : a + x ∈ O ↔ x ∈ O := O.toAddSubgroup.add_mem_cancel_left ha
      by_cases hx : x ∈ O
      · simp only [g, Set.indicator_of_mem hx, Set.indicator_of_mem (hmem.mpr hx),
          f, add_mul, hadd, Circle.coe_mul, star_mul']
      · rw [show g (a + x) = 0 from Set.indicator_of_notMem (mt hmem.mp hx) _,
          show g x = 0 from Set.indicator_of_notMem hx _, mul_zero]
    have h : f a * (∫ x, g x ∂μ) = 1 * (∫ x, g x ∂μ) := by
      rw [one_mul, ← integral_const_mul, ← integral_add_left_eq_self (μ := μ) g a]
      exact integral_congr_ae (ae_of_all _ fun x ↦ (htranslate x).symm)
    exact (mul_eq_mul_right_iff.mp h).resolve_left hne

/-- Paper: Example A.3.1.11, p. 559. The standard S-local character is the product
over all archimedean places and the finite places in S, as in (A.3.1.9).
Deviation: Each local character is expressed as a restriction of the global trace character. -/
def sAdeleStandardCharacter (a : SAdeleRing F S) : Circle :=
  (∏ w : InfinitePlace F, adeleStandardCharacter F (Pi.single w (a.1 w), 0)) *
    ∏ v : S, finiteLocalStandardCharacter F v.val (a.2 v)

/-- The standard p-adic character is trivial at zero. -/
theorem padicStandardCharacter_zero (p : ℕ) [Fact p.Prime] : padicStandardCharacter p 0 = 1 := by
  have h (n : ℕ) (hx : ‖(p : ℚ_[p]) ^ n * 0‖ ≤ 1) :
      PadicInt.toZModPow n (⟨(p : ℚ_[p]) ^ n * 0, hx⟩ : ℤ_[p]) = 0 := by
    rw [show (⟨(p : ℚ_[p]) ^ n * 0, hx⟩ : ℤ_[p]) = (0 : ℤ_[p]) from Subtype.ext (mul_zero _)]
    exact map_zero _
  simp only [padicStandardCharacter]
  rw [h]
  simp

/-- The rational adelic character is trivial at zero. -/
theorem ratAdeleStandardCharacter_zero : ratAdeleStandardCharacter 0 = 1 := by
  have h₁ : (0 : InfiniteAdeleRing ℚ) Rat.infinitePlace = 0 := rfl
  have h₂ (v : Primes(ℚ)) : (0 : FiniteAdeleRing (𝓞 ℚ) ℚ) v = 0 := rfl
  simp [ratAdeleStandardCharacter, h₁, h₂, padicStandardCharacter_zero]

/-- The standard adelic character is trivial at zero. -/
theorem adeleStandardCharacter_zero : adeleStandardCharacter F 0 = 1 := by
  simp [adeleStandardCharacter, ratAdeleStandardCharacter_zero]

/-- The local character at a finite place is trivial at zero. -/
theorem finiteLocalStandardCharacter_zero (v : Primes(F)) :
    finiteLocalStandardCharacter F v 0 = 1 := by
  have h : (RestrictedProduct.single (fun w : Primes(F) ↦ w.adicCompletionIntegers F) v
      (0 : v.adicCompletion F) : FiniteAdeleRing (𝓞 F) F) = 0 :=
    RestrictedProduct.single_zero _ _
  simp only [finiteLocalStandardCharacter, h]
  exact adeleStandardCharacter_zero F

/-- Paper: Example A.3.1.11, p. 559. On an S-adele supported at a single finite
place, the product character restricts to the trace character at that place. -/
theorem sAdeleStandardCharacter_single_finite (v : S) (x : v.val.adicCompletion F) :
    sAdeleStandardCharacter F S (0, Pi.single v x) = finiteLocalStandardCharacter F v.val x := by
  have h₀ (w : InfinitePlace F) : (0 : InfiniteAdeleRing F) w = 0 := rfl
  have h₁ (w : InfinitePlace F) :
      adeleStandardCharacter F (Pi.single w ((0 : InfiniteAdeleRing F) w), 0) = 1 := by
    rw [h₀, Pi.single_zero]
    exact adeleStandardCharacter_zero F
  unfold sAdeleStandardCharacter
  dsimp only
  rw [Finset.prod_eq_one fun w _ ↦ h₁ w, one_mul, Finset.prod_eq_single v]
  · rw [Pi.single_eq_same]
  · intro w _ hw
    rw [Pi.single_eq_of_ne hw, finiteLocalStandardCharacter_zero]
  · simp

-- TODO(paper-gap): In Example A.3.1.11, the lattice fails to annihilate itself
-- under (A.3.1.10) with the real and p-adic signs as printed. For F = ℚ and
-- S = {∞, 3}, the pairing of 1/3 with 1 is exp(4πi/3).
-- The proof also reverses the ambient group of the annihilator for (A.3.1.11).

/-- Bundle the global character as a continuous homomorphism by evaluating the
adelic duality pairing at the multiplicative identity of the adele ring. -/
private theorem exists_adeleCharacterHom :
    ∃ ψ : Multiplicative 𝔸[F] →ₜ* Circle, ∀ a : 𝔸[F],
      ψ (Multiplicative.ofAdd a) = adeleStandardCharacter F a := by
  obtain ⟨e, he, -⟩ := additiveTamagawaMeasure_selfDual F
  exact ⟨e (Multiplicative.ofAdd (1 : 𝔸[F])), fun a ↦ (he 1 a).trans (congrArg _ (one_mul a))⟩

open Filter Topology in
open scoped RestrictedProduct IsDedekindDomain.FiniteAdeleRing in
/-- The finite component of an adele is the sum of its single-place inclusions.
Truncations converge in the product chart determined by its integral coordinates. -/
private theorem hasSum_finiteAdeleSingle (a : 𝔸ᶠ[𝓞 F, F]) :
    HasSum (fun v : Primes(F) ↦ finiteAdeleSingle F v (a v)) (0, a) := by
  let K (v : Primes(F)) := v.adicCompletion F
  let O (v : Primes(F)) := v.adicCompletionIntegers F
  let J := {v : Primes(F) | a v ∈ O v}
  let L := Πʳ v, [K v, O v]_[principal J]
  let x : L := ⟨a, eventually_principal.mpr (fun _ h ↦ h)⟩
  let part (T : Finset (Primes(F))) : L :=
    ⟨fun v ↦ if v ∈ T then a v else 0, eventually_principal.mpr fun v hv ↦ by
      change (if v ∈ T then a v else 0) ∈ O v
      split_ifs <;> first | exact hv | exact (O v).zero_mem⟩
  have hlim : Tendsto part atTop (𝓝 x) := by
    apply RestrictedProduct.isEmbedding_coe_of_principal.isInducing.tendsto_nhds_iff.mpr
    apply tendsto_pi_nhds.mpr
    intro v
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop ({v} : Finset (Primes(F)))] with T hT
    exact (ite_eq_left (hT (Finset.mem_singleton_self v))).symm
  let inc := RestrictedProduct.inclusion K (fun v ↦ (O v : Set (K v)))
    (le_principal_iff.mpr a.2 : cofinite ≤ principal J)
  have hinc : Continuous inc := RestrictedProduct.continuous_inclusion _
  have h : Tendsto (fun T ↦ ((0, inc (part T)) : 𝔸[F])) atTop (𝓝 (0, a)) :=
    tendsto_const_nhds.prodMk_nhds (hinc.continuousAt.tendsto.comp hlim)
  apply h.congr
  intro T
  apply Prod.ext
  · change 0 = (RingHom.fst _ _) (∑ v ∈ T, finiteAdeleSingle F v (a v))
    simp [map_sum, finiteAdeleSingle]
  · apply RestrictedProduct.ext
    intro v
    change (if v ∈ T then a v else 0) =
      finiteAdeleEval F v (∑ w ∈ T, finiteAdeleSingle F w (a w))
    rw [map_sum]
    by_cases hv : v ∈ T
    · rw [ite_eq_left hv, Finset.sum_eq_single_of_mem v hv]
      · exact (RestrictedProduct.single_eq_same O v (a v)).symm
      · intro w _ hw
        exact RestrictedProduct.single_eq_of_ne O _ hw.symm
    · rw [ite_eq_right hv]
      exact (Finset.sum_eq_zero fun w hw ↦
        RestrictedProduct.single_eq_of_ne (i := w) (j := v) O (a w) (fun h ↦ hv (h ▸ hw))).symm

open Filter Topology in
/-- Omitting coordinates with trivial character preserves the global character. -/
private theorem sAdeleStandardCharacter_eq_of_trivial_outside (a : 𝔸[F])
    (houtside : ∀ v : Primes(F), v ∉ S → finiteLocalStandardCharacter F v (a.2 v) = 1) :
    sAdeleStandardCharacter F S (adeleProjection F S a) = adeleStandardCharacter F a := by
  obtain ⟨ψ, hψ⟩ := exists_adeleCharacterHom F
  let χ (a : 𝔸[F]) := ψ (Multiplicative.ofAdd a)
  have hχ {ι : Type _} (T : Finset ι) (f : ι → 𝔸[F]) :
      χ (∑ i ∈ T, f i) = ∏ i ∈ T, χ (f i) := by
    simp only [χ, ofAdd_sum, map_prod]
  let f (v : Primes(F)) := finiteAdeleSingle F v (a.2 v)
  have hout (v : Primes(F)) (hv : v ∉ S) : χ (f v) = 1 :=
    (hψ _).trans (houtside v hv)
  have hfin : (∏ v ∈ S, χ (f v)) = χ (0, a.2) := by
    have ht := (ψ.continuous.comp continuous_ofAdd).continuousAt.tendsto.comp
      (hasSum_finiteAdeleSingle F a.2)
    apply tendsto_nhds_unique tendsto_const_nhds (ht.congr' _)
    filter_upwards [eventually_ge_atTop S] with T hT
    exact (hχ T f).trans (Finset.prod_subset hT (fun v _ hv ↦ hout v hv)).symm
  let arch (w : InfinitePlace F) : 𝔸[F] := (Pi.single w (a.1 w), 0)
  have harch : ∑ w, arch w = (a.1, 0) := by
    apply Prod.ext
    · change (RingHom.fst _ _) (∑ w, arch w) = _
      rw [map_sum]
      apply funext
      intro w
      rw [Finset.sum_apply]
      change ∑ i : InfinitePlace F, Pi.single i (a.1 i) w = a.1 w
      rw [Finset.sum_eq_single w]
      · exact Pi.single_eq_same _ _
      · intro i _ hi
        exact Pi.single_eq_of_ne hi.symm _
      · simp
    · change (RingHom.snd _ _) (∑ w, arch w) = 0
      simp [arch]
  change (∏ w, adeleStandardCharacter F (arch w)) *
      (∏ v : S, finiteLocalStandardCharacter F v.val (a.2 v.val)) = _
  have hlocal (v : S) : finiteLocalStandardCharacter F v.val (a.2 v.val) = χ (f v.val) :=
    (hψ _).symm
  simp_rw [hlocal, ← hψ]
  change (∏ w, χ (arch w)) * (∏ v : S, χ (f v.val)) = χ a
  rw [← Finset.prod_subtype S (fun _ ↦ Iff.rfl) (fun v ↦ χ (f v)), hfin, ← hχ, harch]
  exact (map_mul ψ (Multiplicative.ofAdd (a.1, 0)) (Multiplicative.ofAdd (0, a.2))).symm.trans
    (congrArg χ (Prod.ext (add_zero _) (zero_add _)))

/-- Projecting an adele integral outside S omits only finite characters with
value one. This comparison applies to the entire open subring. -/
private theorem sAdeleStandardCharacter_projection (a : integralAdelesOutside F S) :
    sAdeleStandardCharacter F S (adeleProjection F S a.val) = adeleStandardCharacter F a.val := by
  apply sAdeleStandardCharacter_eq_of_trivial_outside
  intro v hv
  have h := a.property
  simp only [integralAdelesOutside, Subring.mem_iInf] at h
  have hq : (1 : ℝ) ≤ v.asIdeal.absNorm := by
    exact_mod_cast (HeightOneSpectrum.one_lt_absNorm v).le
  have h1 : (1 : v.adicCompletion F) ∈ {y : v.adicCompletion F |
      ‖y‖ ≤ (v.asIdeal.absNorm : ℝ) ^ differentExp(F, v)} := by
    simpa using one_le_pow₀ hq (n := differentExp(F, v))
  rw [← finiteLocalStandardCharacter_annihilator_integers F v] at h1
  exact (congrArg (finiteLocalStandardCharacter F v) (mul_one _).symm).trans
    (h1 (a.val.2 v) (h v hv))

/-- Paper: Example A.3.1.11, p. 559. The standard S-local character takes the
value one on every diagonally embedded S-integer.
Deviation: This consequence of the lattice pairing holds for every finite S with the
finite-place sign correction of ERRATA F13. -/
theorem sAdeleStandardCharacter_sInteger (x : (S : Set (Primes(F))).integer F) :
    sAdeleStandardCharacter F S (adeleProjection F S (integralAdeleDiagonal F S x).val) = 1 := by
  exact (sAdeleStandardCharacter_projection F S _).trans (adeleStandardCharacter_algebraMap F x.val)

/-- Extend an S-adele by zero at the omitted places. Multiplication by any
global adele acts on this summand through its projection. -/
private theorem exists_sAdeleExtension :
    ∃ j : SAdeleRing F S →+ integralAdelesOutside F S, Continuous j ∧
      (∀ y, adeleProjection F S (j y).val = y) ∧
      ∀ (a : 𝔸[F]) y, (j (adeleProjection F S a * y)).val = a * (j y).val := by
  obtain ⟨e, -, he, hc⟩ := integralAdelesOutside_factors F S
  let Outside := (v : {v : Primes(F) // v ∉ S}) → v.val.adicCompletionIntegers F
  let j := e.symm.toAddMonoidHom.comp (AddMonoidHom.inl (SAdeleRing F S) Outside)
  have hj (y) : e (j y) = (y, 0) := e.apply_symm_apply _
  have hp (y) := (hc (j y)).1.symm.trans (congrArg Prod.fst (hj y))
  have hout (y) (v : Primes(F)) (hv : v ∉ S) : (j y).val.2 v = 0 :=
    ((hc (j y)).2 ⟨v, hv⟩).symm.trans
      (congrArg (fun z : SAdeleRing F S × Outside ↦ (z.2 ⟨v, hv⟩).val) (hj y))
  refine ⟨j, he.comp (continuous_id.prodMk continuous_const), hp, fun a y ↦ ?_⟩
  have h := (hp (adeleProjection F S a * y)).trans
    (congrArg (adeleProjection F S a * ·) (hp y).symm)
  refine Prod.ext (congrArg (fun z : SAdeleRing F S ↦ z.1) h) ?_
  apply RestrictedProduct.ext
  intro v
  by_cases hv : v ∈ S
  · exact congrArg (fun z : SAdeleRing F S ↦ z.2 ⟨v, hv⟩) h
  · change (j _).val.2 v = a.2 v * (j y).val.2 v
    rw [hout _ v hv, hout _ v hv, mul_zero]

private theorem continuous_adeleProjection : Continuous (adeleProjection F S) :=
  continuous_fst.prodMk (continuous_pi fun v ↦ (RestrictedProduct.continuous_eval v.val).comp continuous_snd)

/-- Restrict the global self-duality to the summand supported at the places of S. -/
private theorem exists_sAdeleDualEquiv :
    ∃ e : Multiplicative (SAdeleRing F S) ≃ₜ* PontryaginDual (Multiplicative (SAdeleRing F S)),
      ∀ x y : SAdeleRing F S,
        e (Multiplicative.ofAdd x) (Multiplicative.ofAdd y) = sAdeleStandardCharacter F S (x * y) := by
  obtain ⟨j, hj, hpj, hjmul⟩ := exists_sAdeleExtension F S
  obtain ⟨e, he, -⟩ := additiveTamagawaMeasure_selfDual F
  let p := adeleProjection F S
  let P : Multiplicative 𝔸[F] →ₜ* Multiplicative (SAdeleRing F S) :=
    ⟨p.toAddMonoidHom.toMultiplicative, continuous_adeleProjection F S⟩
  let J : Multiplicative (SAdeleRing F S) →ₜ* Multiplicative 𝔸[F] :=
    ⟨((integralAdelesOutside F S).subtype.toAddMonoidHom.comp j).toMultiplicative,
      show Continuous (fun x : SAdeleRing F S ↦ (j x).val) from continuous_subtype_val.comp hj⟩
  let d := (PontryaginDual.map J).comp ((ContinuousMonoidHom.toContinuousMonoidHom e).comp J)
  let inv := P.comp ((ContinuousMonoidHom.toContinuousMonoidHom e.symm).comp (PontryaginDual.map P))
  have hpair (a : 𝔸[F]) (x : SAdeleRing F S) :
      e (Multiplicative.ofAdd a) (J (Multiplicative.ofAdd x)) =
        sAdeleStandardCharacter F S (p a * x) := by
    rw [show e (Multiplicative.ofAdd a) (J (Multiplicative.ofAdd x)) =
      adeleStandardCharacter F (a * (j x).val) from he _ _, ← hjmul]
    exact (sAdeleStandardCharacter_projection F S _).symm.trans (congrArg _ (hpj _))
  have hd (x z : SAdeleRing F S) : d (Multiplicative.ofAdd x) (Multiplicative.ofAdd z) =
      sAdeleStandardCharacter F S (x * z) := (hpair (j x).val z).trans (by rw [show p (j x).val = x from hpj x])
  refine ⟨{ toFun := d, invFun := inv, map_mul' := map_mul d,
            continuous_toFun := d.continuous, continuous_invFun := inv.continuous,
            left_inv := ?_, right_inv := ?_ }, hd⟩
  · intro x
    have heq : PontryaginDual.map P (d x) = e (J x) := by
      apply PontryaginDual.ext
      intro a
      change d x (P a) = e (J x) a
      calc
        _ = sAdeleStandardCharacter F S (x.toAdd * p a.toAdd) := hd _ _
        _ = sAdeleStandardCharacter F S (p a.toAdd * x.toAdd) := congrArg _ (mul_comm _ _)
        _ = e a (J x) := (hpair a.toAdd x.toAdd).symm
        _ = e (J x) a := (he a.toAdd (j x.toAdd).val).trans
          ((congrArg _ (mul_comm _ _)).trans (he (j x.toAdd).val a.toAdd).symm)
    change P (e.symm (PontryaginDual.map P (d x))) = x
    rw [heq, e.symm_apply_apply]
    exact congrArg Multiplicative.ofAdd (hpj x.toAdd)
  · intro χ
    apply PontryaginDual.ext
    intro z
    let a := e.symm (PontryaginDual.map P χ)
    calc
      _ = sAdeleStandardCharacter F S (p a.toAdd * z.toAdd) := hd _ _
      _ = e a (J z) := (hpair a.toAdd z.toAdd).symm
      _ = (PontryaginDual.map P χ) (J z) :=
        congrArg (fun k : PontryaginDual (Multiplicative 𝔸[F]) ↦ k (J z)) (e.apply_symm_apply _)
      _ = χ z := congrArg χ (congrArg Multiplicative.ofAdd (hpj z.toAdd))

open scoped RestrictedProduct in
/-- The global trace annihilator of the diagonal is the diagonal. It is discrete
by compactness of the adelic quotient. Reducing field multiples into a compact
fundamental domain then gives a nonzero multiple on the diagonal. -/
private theorem adeleCharacter_annihilator_diagonal (y : 𝔸[F])
    (hy : ∀ t : F, adeleStandardCharacter F (algebraMap F 𝔸[F] t * y) = 1) :
    ∃ t : F, algebraMap F 𝔸[F] t = y := by
  let G := Multiplicative 𝔸[F]
  let H := A[F]
  let d := algebraMap F 𝔸[F]
  obtain ⟨-, hH, -, -, -, hcomp, -⟩ := adele_additive_quotient.{_, 0} F
  let : CompactSpace (G ⧸ H) := hcomp
  let : LocallyCompactSpace G := adele_locallyCompact F
  let : T2Space G := by
    change T2Space (((w : InfinitePlace F) → w.Completion) ×
      (Πʳ v : Primes(F), [v.adicCompletion F, v.adicCompletionIntegers F]))
    infer_instance
  obtain ⟨e, he, -⟩ := additiveTamagawaMeasure_selfDual F
  let W := (lcaAnnihilator H).comap e.toMonoidHom
  have hW (z : 𝔸[F]) : Multiplicative.ofAdd z ∈ W ↔
      ∀ t : F, adeleStandardCharacter F (d t * z) = 1 := by
    rw [Subgroup.mem_comap, mem_lcaAnnihilator_iff]
    constructor
    · intro h t
      have h' := h ⟨Multiplicative.ofAdd (d t), ⟨t, rfl⟩⟩
      exact ((he z (d t)).trans (congrArg _ (mul_comm _ _))).symm.trans h'
    · intro h a
      obtain ⟨t, ht⟩ := a.property
      change Multiplicative.ofAdd (d t) = a.val at ht
      rw [← ht]
      exact (he z (d t)).trans ((congrArg _ (mul_comm _ _)).trans (h t))
  obtain ⟨u, -⟩ := lcaQuotientDual_equiv_annihilator H hH
  let : DiscreteTopology (lcaAnnihilator H) := u.symm.toHomeomorph.isEmbedding.discreteTopology
  let emb (w : W) : lcaAnnihilator H := ⟨e w.val, w.property⟩
  let : DiscreteTopology W := DiscreteTopology.of_continuous_injective
    (f := emb) (continuous_induced_rng.mpr (e.continuous.comp continuous_subtype_val))
    (fun a b h ↦ Subtype.ext (e.injective (congrArg Subtype.val h)))
  have hclosed : IsClosed (W : Set G) :=
    W.isClosed_of_isDiscrete (SetLike.isDiscrete_iff_discreteTopology.mpr inferInstance)
  let D := adeleFundamentalDomain F (RingOfIntegers.basis F)
  let K : Set W := Subtype.val ⁻¹' (closure D : Set G)
  have hK : IsCompact K := hclosed.isClosedEmbedding_subtypeVal.isCompact_preimage
    (adeleFundamentalDomain_precompact F _)
  let : Finite K := hK.finite_of_discrete.to_subtype
  have hrep (t : F) : ∃ x : F, d t * y - d x ∈ D := by
    have h : d t * y ∈ ⋃ x : F, d x +ᵥ D := (adeleFundamentalDomain_cover F _).symm ▸ mem_univ _
    obtain ⟨x, z, hz, hxz⟩ := mem_iUnion.mp h
    exact ⟨x, by rw [← hxz]; simpa only [vadd_eq_add, add_sub_cancel_left] using hz⟩
  choose x hx using hrep
  have hmem (t : F) : Multiplicative.ofAdd (d t * y - d (x t)) ∈ W := by
    apply W.div_mem
    · apply (hW _).mpr
      intro a
      change adeleStandardCharacter F (d a * (d t * y)) = 1
      rw [← mul_assoc, ← map_mul]
      exact hy _
    · apply (hW _).mpr
      intro a
      change adeleStandardCharacter F (d a * d (x t)) = 1
      rw [← map_mul]
      exact adeleStandardCharacter_algebraMap F _
  let rep (t : F) : K := ⟨⟨_, hmem t⟩, subset_closure (hx t)⟩
  obtain ⟨a, b, hab, heq⟩ := Finite.exists_ne_map_eq_of_infinite rep
  have heq' : d a * y - d (x a) = d b * y - d (x b) :=
    congrArg (fun k : K ↦ k.val.val.toAdd) heq
  have hmul : d (a - b) * y = d (x a - x b) := by
    rw [map_sub, map_sub, sub_mul]
    exact sub_eq_sub_iff_sub_eq_sub.mp heq'
  refine ⟨(a - b)⁻¹ * (x a - x b), ?_⟩
  rw [map_mul, ← hmul, ← mul_assoc, ← map_mul, inv_mul_cancel₀ (sub_ne_zero.mpr hab), map_one, one_mul]

/-- A single omitted local integer lies in the integral tail and projects to zero. -/
private theorem finiteAdeleSingle_outside (v : Primes(F)) (hv : v ∉ S)
    (x : v.adicCompletion F) (hx : x ∈ v.adicCompletionIntegers F) :
    finiteAdeleSingle F v x ∈ integralAdelesOutside F S ∧
      adeleProjection F S (finiteAdeleSingle F v x) = 0 := by
  let O (w : Primes(F)) := w.adicCompletionIntegers F
  constructor
  · simp only [integralAdelesOutside, Subring.mem_iInf]
    intro u _
    by_cases huv : u = v
    · subst u
      change RestrictedProduct.single O v x v ∈ v.adicCompletionIntegers F
      rwa [RestrictedProduct.single_eq_same]
    · change RestrictedProduct.single O v x u ∈ u.adicCompletionIntegers F
      rw [RestrictedProduct.single_eq_of_ne _ _ huv]
      exact Subring.zero_mem _
  · refine Prod.ext rfl (funext fun u ↦ ?_)
    exact RestrictedProduct.single_eq_of_ne O x (fun h : u.val = v ↦ hv (h ▸ u.property))

/-- Paper: Example A.3.1.11, p. 559. The diagonal S-integers are their own annihilator
for the standard character pairing when S contains every finite prime dividing the different.
Deviation: The pairing uses the finite-place sign correction of ERRATA F13. -/
theorem sInteger_annihilator_iff
    (hS : ∀ v : Primes(F), v.asIdeal ∣ differentIdeal ℤ (𝓞 F) → v ∈ S)
    (y : SAdeleRing F S) :
    (∀ x : (S : Set (Primes(F))).integer F,
        sAdeleStandardCharacter F S
          (adeleProjection F S (integralAdeleDiagonal F S x).val * y) = 1) ↔
      ∃ x : (S : Set (Primes(F))).integer F,
        y = adeleProjection F S (integralAdeleDiagonal F S x).val := by
  let p := adeleProjection F S
  let I := integralAdelesOutside F S
  let i := integralAdeleDiagonal F S
  let d := (p.comp I.subtype).comp i
  let qA := QuotientAddGroup.mk' (AdeleRing.principalSubgroup (𝓞 F) F)
  constructor
  · intro hy
    obtain ⟨eS, heS⟩ := exists_sAdeleDualEquiv F S
    let φ := (eS (Multiplicative.ofAdd y)).toMonoidHom.toAdditiveRight
    have hφ (z) : (φ z).toMul = sAdeleStandardCharacter F S (z * y) :=
      (heS y z).trans (congrArg _ (mul_comm _ _))
    let φQ := QuotientAddGroup.lift d.toAddMonoidHom.range φ (by
      rintro _ ⟨x, rfl⟩
      exact congrArg Additive.ofMul ((hφ _).trans (hy x)))
    obtain ⟨-, -, -, -, hq, -, -, ⟨π, hπ, -, hπq⟩, e, heq⟩ := sAdele_additive_quotient F S
    have hc : Continuous φQ := hq.isQuotientMap.continuous_iff.mpr
      (show Continuous (eS (Multiplicative.ofAdd y)) from (eS _).continuous)
    let f := ((φQ.comp π).comp e.symm.toAddMonoidHom).comp qA
    let χ : PontryaginDual (Multiplicative 𝔸[F]) :=
      ⟨f.toMultiplicativeLeft, show Continuous f from hc.comp (hπ.continuous.comp (e.symm.continuous.comp
        QuotientAddGroup.continuous_mk))⟩
    obtain ⟨E, hE, -⟩ := additiveTamagawaMeasure_selfDual F
    let w := (E.symm χ).toAdd
    have hw (a : 𝔸[F]) : adeleStandardCharacter F (a * w) = (f a).toMul := by
      rw [mul_comm, ← hE w a, show E (Multiplicative.ofAdd w) = χ from E.apply_symm_apply _]
      rfl
    have hw' (t : F) : adeleStandardCharacter F (algebraMap F 𝔸[F] t * w) = 1 := by
      rw [hw]
      have ht : qA (algebraMap F 𝔸[F] t) = 0 := (QuotientAddGroup.eq_zero_iff _).mpr ⟨t, rfl⟩
      change (((φQ.comp π).comp e.symm.toAddMonoidHom) (qA _)).toMul = 1
      rw [ht, map_zero]
      rfl
    obtain ⟨t, ht⟩ := adeleCharacter_annihilator_diagonal F w hw'
    have htest (a : I) :
        adeleStandardCharacter F (a.val * algebraMap F 𝔸[F] t) =
          sAdeleStandardCharacter F S (p a.val * y) := by
      rw [ht, hw, ← hφ]
      change (φQ (π (e.symm (qA a.val)))).toMul = _
      rw [← heq a, e.symm_apply_apply, hπq a]
      rfl
    have hInt : algebraMap F 𝔸[F] t ∈ I := by
      simp only [I, integralAdelesOutside, Subring.mem_iInf]
      intro v hv
      have htestv : finiteAdeleEval F v (algebraMap F 𝔸[F] t) ∈
          {z : v.adicCompletion F | ∀ x ∈ (v.adicCompletionIntegers F : Set _),
            finiteLocalStandardCharacter F v (x * z) = 1} := by
        intro x hx
        let a := finiteAdeleSingle F v x
        obtain ⟨ha, hp⟩ := finiteAdeleSingle_outside F S v hv x hx
        have H := htest ⟨a, ha⟩
        change adeleStandardCharacter F (a * _) = sAdeleStandardCharacter F S (p a * y) at H
        rw [hp, zero_mul, ← map_zero d, show d 0 = p (i 0).val from rfl,
          sAdeleStandardCharacter_sInteger] at H
        rw [mul_comm x, show finiteLocalStandardCharacter F v _ =
          adeleStandardCharacter F (finiteAdeleSingle F v (_ * x)) from rfl,
          finiteAdeleSingle_mul, mul_comm]
        exact H
      rw [finiteLocalStandardCharacter_annihilator_integers F v] at htestv
      have hn : ‖finiteAdeleEval F v (algebraMap F 𝔸[F] t)‖ ≤ 1 := by
        simpa only [mem_ofPred_eq, multiplicity_eq_zero_of_not_dvd (fun h ↦ hv (hS v h)),
          pow_zero] using htestv
      exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).mpr
        (Valued.toNormedField.norm_le_one_iff.mp hn)
    let x : (S : Set (Primes(F))).integer F := ⟨t, (diagonal_mem_integralAdelesOutside F S t).mp hInt⟩
    refine ⟨x, Multiplicative.ofAdd.injective (eS.injective (PontryaginDual.ext fun z ↦ ?_))⟩
    obtain ⟨j, -, hpj, -⟩ := exists_sAdeleExtension F S
    have H := htest (j z.toAdd)
    let a := j z.toAdd * i x
    have ha := sAdeleStandardCharacter_projection F S a
    change sAdeleStandardCharacter F S (p ((j z.toAdd).val * (i x).val)) = _ at ha
    rw [map_mul, hpj] at ha
    change adeleStandardCharacter F ((j z.toAdd).val * (i x).val) = _ at H
    rw [show p (j z.toAdd).val = z.toAdd from hpj _] at H
    calc
      _ = sAdeleStandardCharacter F S (z.toAdd * y) :=
        (heS y z.toAdd).trans (congrArg _ (mul_comm _ _))
      _ = sAdeleStandardCharacter F S (z.toAdd * p (i x).val) := H.symm.trans ha.symm
      _ = _ := (congrArg _ (mul_comm _ _)).trans (heS (p (i x).val) z.toAdd).symm
  · rintro ⟨x, rfl⟩ z
    change sAdeleStandardCharacter F S (d z * d x) = 1
    rw [← map_mul]
    exact sAdeleStandardCharacter_sInteger F S _

/-- Paper: Definition A.3.2.1, p. 559. The measure `dt/t` on the positive
reals is the pushforward of real Lebesgue measure along the exponential. -/
def positiveRealHaar : Measure ℝ≥0ˣ :=
  Measure.map (fun x : ℝ ↦
    Units.mk0 (Real.exp x).toNNReal
      (Real.toNNReal_eq_zero.not.mpr (not_le_of_gt (Real.exp_pos x)))) volume

/-- Paper: §A.3.3.1, p. 561. The mass of the interval with endpoints 1 and T
under `dt/t` is the logarithm of T for T at least 1. -/
theorem positiveRealHaar_interval (T : ℝ≥0ˣ) (hT : 1 ≤ (T.val : ℝ)) :
    positiveRealHaar {t | (t.val : ℝ) ∈ Icc 1 (T.val : ℝ)} =
      ENNReal.ofReal (Real.log (T.val : ℝ)) := by
  let e (x : ℝ) := Units.mk0 (Real.exp x).toNNReal (by positivity)
  have he : Measurable e :=
    measurable_comap_iff.mpr (continuous_real_toNNReal.comp Real.continuous_exp).measurable
  have hset : MeasurableSet {t : ℝ≥0ˣ | (t.val : ℝ) ∈ Icc 1 (T.val : ℝ)} :=
    measurableSet_Icc.preimage (NNReal.continuous_coe.measurable.comp MeasurableSpace.le_map_comap)
  change (volume.map e) _ = _
  rw [Measure.map_apply he hset]
  have hpre : e ⁻¹' {t | (t.val : ℝ) ∈ Icc 1 (T.val : ℝ)} = Icc 0 (Real.log (T.val : ℝ)) := by
    ext x
    change (1 ≤ ((Real.exp x).toNNReal : ℝ) ∧ ((Real.exp x).toNNReal : ℝ) ≤ _) ↔ _
    rw [Real.coe_toNNReal _ (Real.exp_pos x).le, Real.one_le_exp_iff,
      ← Real.le_log_iff_exp_le (zero_lt_one.trans_le hT)]
    rfl
  rw [hpre, Real.volume_Icc, sub_zero]

local notation "classVolume(" F ")" =>
  ENNReal.ofReal ((2 : ℝ) ^ InfinitePlace.nrRealPlaces F *
    (2 * Real.pi) ^ InfinitePlace.nrComplexPlaces F * Nat.cast (NumberField.classNumber F) *
    Units.regulator F / (Real.sqrt (Nat.cast (Int.natAbs (NumberField.discr F))) *
      Nat.cast (Units.torsionOrder F)))

/-- The exponential pushforward of Lebesgue measure is Haar measure on the positive reals. -/
private theorem positiveRealHaar_isHaarMeasure : positiveRealHaar.IsHaarMeasure := by
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  let μ : Measure (Multiplicative ℝ) := (volume : Measure ℝ)
  let : μ.IsHaarMeasure := by
    have : IsFiniteMeasureOnCompacts μ :=
      inferInstanceAs (IsFiniteMeasureOnCompacts (volume : Measure ℝ))
    have : Measure.IsOpenPosMeasure μ :=
      inferInstanceAs (Measure.IsOpenPosMeasure (volume : Measure ℝ))
    have : μ.IsMulLeftInvariant :=
      ⟨fun t ↦ (measurePreserving_add_left (volume : Measure ℝ) t.toAdd).map_eq⟩
    constructor
  let h := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
  let e : Multiplicative ℝ ≃ₜ* ℝ≥0ˣ :=
    { h with
      map_mul' := fun x y ↦ by
        apply Units.ext
        apply NNReal.eq
        exact Real.exp_add x.toAdd y.toAdd }
  have he (x : ℝ) :
      e (Multiplicative.ofAdd x) = Units.mk0 (Real.exp x).toNNReal (by positivity) := by
    apply Units.ext
    apply NNReal.eq
    exact (Real.coe_toNNReal _ (Real.exp_pos x).le).symm
  convert e.isHaarMeasure_map μ using 1
  unfold positiveRealHaar
  congr 1
  funext x
  exact (he x).symm

/-- Given Haar measures on a closed subgroup and its quotient, Weil's formula
determines a unique regular Haar measure on the ambient group. -/
private theorem existsUnique_isWeilQuotientMeasure_left
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G)) (μH : Measure H) [μH.IsHaarMeasure] :
    letI : MeasurableSpace (G ⧸ H) := borel _
    ∀ (ν : Measure (G ⧸ H)), ν.IsHaarMeasure → ν.Regular →
      ∃! μ : Measure G, μ.IsHaarMeasure ∧ μ.Regular ∧ IsWeilQuotientMeasure H μ μH ν := by
  let : MeasurableSpace (G ⧸ H) := borel _
  intro ν hνH hνR
  let : ν.IsHaarMeasure := hνH
  let : ν.Regular := hνR
  let : BorelSpace (G ⧸ H) := ⟨rfl⟩
  let ses := TopologicalGroup.IsSES.ofClosedSubgroup H hH
  let μ := ses.inducedMeasure μH ν
  have hweil : IsWeilQuotientMeasure H μ μH ν := by
    refine ⟨inferInstance, inferInstance, fun f hf ↦ ?_⟩
    let fc : CompactlySupportedContinuousMap G ℂ := ⟨f, hf⟩
    change (∫ x, fc x ∂μ) = _
    rw [integral_inducedMeasure_complex ses μH ν fc, ses.integrate_apply]
    refine integral_congr_ae (Filter.Eventually.of_forall fun q ↦ ?_)
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    exact ses.pushforward_apply_apply μH fc q.out
  refine ⟨μ, ⟨ses.isHaarMeasure_inducedMeasure μH ν, ses.inducedMeasure_regular μH ν, hweil⟩, ?_⟩
  rintro μ' ⟨-, hregular, hweil'⟩
  let : μ'.Regular := hregular
  let : μ.Regular := ses.inducedMeasure_regular μH ν
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  let fc : C(G, ℂ) := ⟨fun x ↦ (f x : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
  have hc : HasCompactSupport fc := f.hasCompactSupport.comp_left Complex.ofReal_zero
  apply Complex.ofReal_injective
  simpa only [fc, ContinuousMap.coe_mk, integral_complex_ofReal] using
    (hweil'.2.2 fc hc).trans (hweil.2.2 fc hc).symm

/-- Paper: Definition A.3.2.1, pp. 559–560. There is a unique compatible triple
of regular Haar measures on the ideles, the idele classes and the norm-one
classes. The quotient normalizations use counting measure and `dt/t`, respectively. -/
theorem multiplicativeTamagawaMeasures_existsUnique :
    ∃! m : Measure 𝕀[F] × Measure C[F] × Measure C₁[F],
      m.1.IsHaarMeasure ∧ m.1.Regular ∧
        IsWeilQuotientMeasure P[F] m.1 Measure.count m.2.1 ∧
        m.2.2.IsHaarMeasure ∧ m.2.2.Regular ∧ m.2.2 univ = classVolume(F) ∧
        IsWeilQuotientMeasure C₁[F] m.2.1 m.2.2
          (positiveRealHaar.comap (QuotientGroup.kerLift (ideleClassNorm F))) := by
  let G := 𝕀[F]
  let P := P[F]
  let C := C[F]
  let K := C₁[F]
  let Q := C ⧸ K
  obtain ⟨hG₂, hGlc, -⟩ := ideleGroup_topology F
  obtain ⟨-, hP, hPd, -, -, hC₂, hClc, -, hn, -, ⟨s, hs, hsn⟩, -⟩ :=
    ideleGroup_quotient.{_, 0} F
  obtain ⟨hK, hKc, hK₂, -⟩ := ideleClassGroup_finiteness F
  let : T2Space G := hG₂
  let : LocallyCompactSpace G := hGlc
  let : T2Space C := hC₂
  let : LocallyCompactSpace C := hClc
  let : T2Space K := hK₂
  let : CompactSpace K := hKc
  let : DiscreteTopology P := isDiscrete_iff_discreteTopology.mp hPd
  let : BorelSpace G := ⟨rfl⟩
  let : BorelSpace C := ⟨rfl⟩
  let : BorelSpace Q := ⟨rfl⟩
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  let count : Measure P := Measure.count
  let : count.IsHaarMeasure :=
    { lt_top_of_isCompact := fun _ h ↦ Measure.count_apply_lt_top.mpr h.finite_of_discrete
      open_pos := fun _ _ h ↦ Measure.count_ne_zero h }
  let e₀ := QuotientGroup.quotientKerEquivOfRightInverse (ideleClassNorm F) s hsn
  let e : Q ≃ₜ* ℝ≥0ˣ :=
    { e₀ with
      continuous_toFun := (QuotientGroup.isQuotientMap_mk K).continuous_iff.mpr hn
      continuous_invFun := QuotientGroup.continuous_mk.comp hs }
  let dt : Measure Q := positiveRealHaar.comap (QuotientGroup.kerLift (ideleClassNorm F))
  let : positiveRealHaar.IsHaarMeasure := positiveRealHaar_isHaarMeasure
  let : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  have hdt : positiveRealHaar.map e.symm = dt :=
    e.toHomeomorph.toMeasurableEquiv.map_symm
  have hdtH : dt.IsHaarMeasure := hdt ▸ e.symm.isHaarMeasure_map positiveRealHaar
  have hdtR : dt.Regular := hdt ▸ Measure.Regular.map e.symm.toHomeomorph
  have hvol : 0 < classVolume(F) := by
    have := NumberField.classNumber_pos F
    have := NumberField.Units.regulator_pos F
    have := NumberField.Units.torsionOrder_pos F
    have := Int.natAbs_pos.mpr (NumberField.discr_ne_zero F)
    exact ENNReal.ofReal_pos.mpr (by positivity)
  let U : TopologicalSpace.PositiveCompacts K := ⟨⟨univ, isCompact_univ⟩, by simp⟩
  let ν₀ := Measure.haarMeasure U
  have hν₀ : ν₀ univ = 1 := Measure.haarMeasure_self (K₀ := U)
  let c := (classVolume(F)).toNNReal
  have hc : (c : ℝ≥0∞) = classVolume(F) := ENNReal.coe_toNNReal ENNReal.ofReal_ne_top
  let ν := c • ν₀
  have hνH : ν.IsHaarMeasure :=
    Measure.IsHaarMeasure.nnreal_smul ν₀ (by exact_mod_cast hc ▸ hvol.ne')
  have hνR : ν.Regular := inferInstanceAs ((c • ν₀).Regular)
  have hν : ν univ = classVolume(F) := by
    rw [show ν univ = (c : ℝ≥0∞) * ν₀ univ from rfl, hν₀, mul_one, hc]
  obtain ⟨η, ⟨hηH, hηR, hη⟩, hηunique⟩ :=
    existsUnique_isWeilQuotientMeasure_left K hK ν dt hdtH hdtR
  obtain ⟨μ, ⟨hμH, hμR, hμ⟩, hμunique⟩ :=
    existsUnique_isWeilQuotientMeasure_left P hP count η hηH hηR
  refine ⟨(μ, η, ν), ⟨hμH, hμR, hμ, hνH, hνR, hν, hη⟩, ?_⟩
  rintro ⟨μ', η', ν'⟩ ⟨hμH', hμR', hμ', hνH', hνR', hν', hη'⟩
  let : ν'.IsHaarMeasure := hνH'
  let : ν'.Regular := hνR'
  have hνeq : ν' = ν := by
    have hscale := Measure.isMulLeftInvariant_eq_smul_of_regular ν' ν₀
    have hmass := congrArg (fun m : Measure K ↦ m univ) hscale
    change ν' univ = (ν'.haarScalarFactor ν₀ : ℝ≥0∞) * ν₀ univ at hmass
    rw [hν', hν₀, mul_one, ← hc] at hmass
    rw [hscale, ← ENNReal.coe_inj.mp hmass]
  subst ν'
  have hηeq : η' = η := hηunique η' ⟨hμ'.1, hμ'.2.1, hη'⟩
  subst η'
  rw [hμunique μ' ⟨hμH', hμR', hμ'⟩]

/-- Paper: Definition A.3.2.1, pp. 559–560. The global multiplicative Tamagawa
measure uses the prescribed mass on the norm-one idele classes. -/
def multiplicativeTamagawaMeasure : Measure 𝕀[F] :=
  (multiplicativeTamagawaMeasures_existsUnique F).exists.choose.1

/-- Paper: Definition A.3.2.1, pp. 559–560. The class measure is the quotient
of the idelic Tamagawa measure by counting measure on the principal ideles. -/
def ideleClassTamagawaMeasure : Measure C[F] :=
  (multiplicativeTamagawaMeasures_existsUnique F).exists.choose.2.1

/-- Paper: Definition A.3.2.1, pp. 559–560. Disintegrating the class measure
against `dt/t` gives the Tamagawa measure on the norm-one classes. -/
def normOneIdeleClassTamagawaMeasure : Measure C₁[F] :=
  (multiplicativeTamagawaMeasures_existsUnique F).exists.choose.2.2

/-- Paper: Definition A.3.2.1, pp. 559–560. The global idelic and class measures
satisfy Weil's formula with counting measure on the principal ideles. -/
theorem ideleClassTamagawaMeasure_isWeil :
    IsWeilQuotientMeasure P[F] (multiplicativeTamagawaMeasure F)
      Measure.count (ideleClassTamagawaMeasure F) :=
  (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.1

/-- Paper: Definition A.3.2.1, p. 560. The norm-one idele classes have the
mass in (A.3.2.1), expressed with Mathlib's regulator and class number. -/
theorem normOneIdeleClassTamagawaMeasure_volume :
    normOneIdeleClassTamagawaMeasure F univ = classVolume(F) :=
  (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.2.2.1

/-- Paper: Definition A.3.2.1, pp. 559–560. The class and norm-one class measures
satisfy Weil's formula with `dt/t` on the norm quotient. -/
theorem normOneIdeleClassTamagawaMeasure_isWeil :
    IsWeilQuotientMeasure C₁[F] (ideleClassTamagawaMeasure F)
      (normOneIdeleClassTamagawaMeasure F)
      (positiveRealHaar.comap (QuotientGroup.kerLift (ideleClassNorm F))) :=
  (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.2.2.2

/-- Paper: Definition A.3.2.2(1), p. 560. The multiplicative measure at an infinite
place is the additive measure weighted by the reciprocal normalized absolute value. -/
def infiniteLocalMultiplicativeTamagawaMeasure (v : InfinitePlace F) : Measure v.Completionˣ :=
  ((infiniteLocalAdditiveTamagawaMeasure F v).withDensity
    (fun x ↦ (↑(‖x‖₊ ^ v.mult) : ℝ≥0∞)⁻¹)).comap Units.val

/-- Paper: Definition A.3.2.2(1), p. 560. On units at a real place with coordinate
between 1 and 2 the measure is the integral of `dt/t`, namely `log 2`. -/
theorem infiniteLocalMultiplicativeTamagawaMeasure_real_interval (v : InfinitePlace F)
    (h : v.IsReal) :
    infiniteLocalMultiplicativeTamagawaMeasure F v
      {x | ringEquivRealOfIsReal h x.val ∈ Icc 1 2} = ENNReal.ofReal (Real.log 2) := by
  let : BorelSpace v.Completion := ⟨rfl⟩
  let : BorelSpace v.Completionˣ := borelSpace_units_of_continuousInv₀ _
  let e := (isometryEquivRealOfIsReal h).toHomeomorph.toMeasurableEquiv
  have hval := (IsOpenUnits.isOpenEmbedding_unitsVal (M := v.Completion)).measurableEmbedding
  have hpos {t : ℝ} (ht : t ∈ Icc (1 : ℝ) 2) : 0 < t := zero_lt_one.trans_le ht.1
  have hsub : e ⁻¹' Icc 1 2 ⊆ range (Units.val : v.Completionˣ → v.Completion) := by
    intro x hx
    have hx0 : x ≠ 0 := (ringEquivRealOfIsReal h).map_ne_zero_iff.mp (hpos hx).ne'
    exact ⟨Units.mk0 x hx0, rfl⟩
  change infiniteLocalMultiplicativeTamagawaMeasure F v
    (Units.val ⁻¹' (e ⁻¹' Icc 1 2)) = _
  rw [infiniteLocalMultiplicativeTamagawaMeasure, hval.comap_preimage,
    inter_eq_self_of_subset_left hsub, withDensity_apply _ (e.measurable measurableSet_Icc),
    infiniteLocalAdditiveTamagawaMeasure, dite_eq_left h]
  change (∫⁻ x in e ⁻¹' Icc 1 2, (↑(‖x‖₊ ^ v.mult) : ℝ≥0∞)⁻¹ ∂volume.map e.symm) = _
  rw [e.symm.restrict_map, e.symm.measurableEmbedding.lintegral_map, e.symm_preimage_preimage]
  have hnorm (t : ℝ) : ‖e.symm t‖ = ‖t‖ :=
    (isometryEquivRealOfIsReal h).symm.isometry.norm_map_of_map_zero
      (map_zero (ringEquivRealOfIsReal h).symm) t
  rw [setLIntegral_congr_fun (g := fun t : ℝ ↦ ENNReal.ofReal t⁻¹) measurableSet_Icc
    (fun t ht ↦ by
      rw [h.mult_eq_one, pow_one, ← ENNReal.ofReal_coe_nnreal, coe_nnNorm, hnorm,
        Real.norm_eq_abs, abs_of_pos (hpos ht)]
      exact (ENNReal.ofReal_inv_of_pos (hpos ht)).symm)]
  have hint : IntegrableOn (fun t : ℝ ↦ t⁻¹) (Icc 1 2) :=
    (continuousOn_inv₀.mono fun _ ht ↦ (hpos ht).ne').integrableOn_Icc
  rw [← ofReal_integral_eq_lintegral_ofReal hint
      ((ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall
        fun _ ht ↦ inv_nonneg.mpr (hpos ht).le)),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 2),
    integral_inv_of_pos zero_lt_one zero_lt_two, div_one]

/-- Paper: Definition A.3.2.2(2), p. 560. Scale local multiplicative Haar
measure so that the integer units have the inverse square root different-norm mass. -/
def finiteLocalMultiplicativeTamagawaMeasure (v : Primes(F)) : Measure (v.adicCompletion F)ˣ :=
  let μ := Measure.haar (G := (v.adicCompletion F)ˣ)
  (differentMass(F, v) / μ (v.adicCompletionIntegers F).units) • μ

/-- Paper: Definition A.3.2.2(2), p. 560. The local multiplicative measure assigns
the mass in (A.3.2.2) to the integer units. -/
theorem finiteLocalMultiplicativeTamagawaMeasure_integerUnits (v : Primes(F)) :
    finiteLocalMultiplicativeTamagawaMeasure F v (v.adicCompletionIntegers F).units =
      differentMass(F, v) := by
  let μ := Measure.haar (G := (v.adicCompletion F)ˣ)
  have hO : IsOpen ((v.adicCompletionIntegers F).units : Set (v.adicCompletion F)ˣ) :=
    Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)
  have hK : IsCompact ((v.adicCompletionIntegers F).units : Set (v.adicCompletion F)ˣ) :=
    Submonoid.units_isCompact (isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v))
  have hpos := hO.measure_pos μ ⟨1, (v.adicCompletionIntegers F).units.one_mem⟩
  change ((differentMass(F, v) / μ (v.adicCompletionIntegers F).units) • μ)
    (v.adicCompletionIntegers F).units = _
  rw [smul_apply, smul_eq_mul]
  exact ENNReal.div_mul_cancel hpos.ne' (hK.measure_ne_top (μ := μ))

/-- Paper: Lemma A.3.2.3, p. 560. At a finite place the multiplicative
measure is the weighted additive measure times `qᵥ / (qᵥ - 1)`. -/
theorem finiteLocalMultiplicativeTamagawaMeasure_eq_withDensity (v : Primes(F)) :
    finiteLocalMultiplicativeTamagawaMeasure F v =
      (↑v.asIdeal.absNorm / (↑v.asIdeal.absNorm - 1) : ℝ≥0∞) •
        ((finiteLocalAdditiveTamagawaMeasure F v).withDensity
          (fun x ↦ (↑‖x‖₊ : ℝ≥0∞)⁻¹)).comap Units.val := by
  let K := v.adicCompletion F
  let : ProperSpace K := properSpace_adicCompletion v
  let O := v.adicCompletionIntegers F
  let U : Set Kˣ := O.units
  let μ := finiteLocalAdditiveTamagawaMeasure F v
  let : μ.IsAddHaarMeasure := finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  let : μ.Regular := finiteLocalAdditiveTamagawaMeasure_regular F v
  let q : ℝ≥0∞ := v.asIdeal.absNorm
  have hq : 1 < q := by
    dsimp only [q]
    exact_mod_cast (show 1 < v.asIdeal.absNorm from HeightOneSpectrum.one_lt_absNorm v)
  have hq₀ : q ≠ 0 := (zero_lt_one.trans hq).ne'
  have hqf : q ≠ ⊤ := ENNReal.natCast_ne_top _
  have hO : IsOpen (O : Set K) := Valued.isOpen_valuationSubring K
  have hOmem (x : K) : x ∈ (O : Set K) ↔ ‖x‖ ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).trans
      Valued.toNormedField.norm_le_one_iff.symm
  have hOc : IsCompact (O : Set K) :=
    isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v)
  have hO₀ : μ (O : Set K) ≠ 0 := (hO.measure_pos μ ⟨0, O.zero_mem⟩).ne'
  have hOf : μ (O : Set K) ≠ ⊤ := hOc.measure_ne_top

  -- The uniformizer sends the integer ring to the kernel of reduction.
  let val : Valuation K (WithZero (Multiplicative ℤ)) := Valued.v
  obtain ⟨π, hπ⟩ : ∃ π : O, val.IsUniformizer (π : K) :=
    val.exists_isUniformizer_of_isCyclic_of_nontrivial
  let p : Kˣ := Units.mk0 π.val hπ.ne_zero
  have hp : ‖p.val‖ = (v.asIdeal.absNorm : ℝ)⁻¹ := norm_uniformizer_adicCompletion v _ hπ
  obtain ⟨hπball, hπmass⟩ :
      p • (O : Set K) = {x : K | ‖x‖ < 1} ∧
        μ (p • (O : Set K)) = μ (O : Set K) / q := by
    let : MeasurableSpace O := borel _
    let : BorelSpace O := ⟨rfl⟩
    let i := O.toSubring.subtype
    have hi : Topology.IsOpenEmbedding i := hO.isOpenEmbedding_subtypeVal
    let μO := μ.comap i
    let : μO.IsAddHaarMeasure :=
      Measure.IsAddHaarMeasure.comap (mH := inferInstance) μ (f := i.toAddMonoidHom) hi
    let r := (IsLocalRing.residue O).toAddMonoidHom
    have hindex : r.ker.index = v.asIdeal.absNorm := by
      rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr (IsLocalRing.residue_surjective (R := O)),
        AddSubgroup.card_top, card_residueField_adicCompletion]
    let : r.ker.FiniteIndex := ⟨by rw [hindex]; exact (HeightOneSpectrum.one_lt_absNorm v).pos.ne'⟩
    have hker (a : O) : a ∈ r.ker ↔ ‖(a : K)‖ < 1 :=
      (IsLocalRing.residue_eq_zero_iff a).trans
        ((Valuation.mem_maximalIdeal_iff K val).trans Valued.toNormedField.norm_lt_one_iff.symm)
    have hkerMeas : MeasurableSet (r.ker : Set O) := by
      change MeasurableSet {a : O | a ∈ r.ker}
      simp_rw [hker]
      exact (isOpen_lt (continuous_norm.comp
        (continuous_subtype_val : Continuous (Subtype.val : O → K))) continuous_const).measurableSet
    have hπO : i '' (r.ker : Set O) = p • (O : Set K) := by
      have hdiv (a : O) : a ∈ r.ker ↔ π ∣ a := by
        change IsLocalRing.residue O a = 0 ↔ _
        have hgen : IsLocalRing.maximalIdeal O = Ideal.span {π} := hπ.is_generator
        rw [IsLocalRing.residue_eq_zero_iff, hgen, Ideal.mem_span_singleton]
      ext x
      change (∃ a : O, a ∈ r.ker ∧ i a = x) ↔ ∃ b ∈ (O : Set K), p.val * b = x
      simp only [hdiv]
      constructor
      · rintro ⟨a, ⟨b, rfl⟩, rfl⟩
        exact ⟨b, b.property, rfl⟩
      · rintro ⟨b, hb, rfl⟩
        let bO : O := ⟨b, hb⟩
        exact ⟨π * bO, dvd_mul_right π bO, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← hπO]
      ext x
      change x ∈ i '' (r.ker : Set O) ↔ ‖x‖ < 1
      refine ⟨?_, ?_⟩
      · rintro ⟨a, ha, rfl⟩
        exact (hker a).mp ha
      · intro hx
        let a : O := ⟨x, (hOmem x).mpr hx.le⟩
        exact ⟨a, (hker a).mpr hx, rfl⟩
    · have h := r.ker.index_mul_measure hkerMeas μO
      change (r.ker.index : ℝ≥0∞) * μ.comap i r.ker = μ.comap i univ at h
      rw [hindex, hi.measurableEmbedding.comap_apply, hi.measurableEmbedding.comap_apply,
        hπO, Set.image_univ, show range i = (O : Set K) from Subtype.range_coe] at h
      rw [← h, mul_comm, ENNReal.mul_div_cancel_right hq₀ hqf]
  -- The Haar scaling character agrees with the norm on a uniformizer and on integer units.
  have hχp : distribHaarChar K p = ‖p.val‖₊ := by
    apply ENNReal.coe_injective
    rw [distribHaarChar_eq_div hO₀ hOf, hπmass]
    simp only [div_eq_mul_inv]
    rw [mul_right_comm, ENNReal.mul_inv_cancel hO₀ hOf, one_mul]
    have hp' : ‖p.val‖₊ = (v.asIdeal.absNorm : ℝ≥0)⁻¹ := NNReal.eq (by simpa using hp)
    rw [hp', ENNReal.coe_inv (by exact_mod_cast (HeightOneSpectrum.one_lt_absNorm v).pos.ne'),
      ENNReal.coe_natCast]

  have hUnorm (u : Kˣ) : u ∈ U ↔ ‖u.val‖ = 1 :=
    HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.trans
      Valued.toNormedField.norm_eq_one_iff.symm
  have hUnnNorm (u : Kˣ) (hu : u ∈ U) : ‖u.val‖₊ = 1 := by
    apply NNReal.eq
    simpa only [NNReal.coe_one, coe_nnNorm] using (hUnorm u).mp hu
  have hχU (u : Kˣ) (hu : u ∈ U) : distribHaarChar K u = ‖u.val‖₊ := by
    have hset : u • (O : Set K) = O := by
      rw [← preimage_smul_inv]
      ext x
      change u⁻¹ • x ∈ (O : Set K) ↔ x ∈ (O : Set K)
      simp only [hOmem, Units.smul_def, Units.val_inv_eq_inv_val, smul_eq_mul, norm_mul, norm_inv,
        (hUnorm u).mp hu, inv_one, one_mul]
    rw [hUnnNorm u hu]
    apply distribHaarChar_eq_of_measure_smul_eq_mul hO₀ hOf
    simp [hset]
  have hχ (u : Kˣ) : distribHaarChar K u = ‖u.val‖₊ := by
    obtain ⟨e, hep, heι⟩ := finitePlace_unitDecomposition v p hp
    let ι := Units.map O.subtype.toMonoidHom
    have hdecomp : u = p ^ (e u).1.toAdd * ι (e u).2 := by
      apply e.injective
      rw [map_mul, map_zpow, hep, heι]
      refine Prod.ext ?_ (by simp)
      change (e u).1.toAdd = (e u).1.toAdd * 1 + 0
      simp
    have hz : ι (e u).2 ∈ U := ⟨(e u).2.val.property, (e u).2.inv.property⟩
    conv_lhs => rw [hdecomp]
    rw [map_mul, map_zpow, hχp, hχU _ hz]
    conv_rhs => rw [hdecomp]
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, nnNorm_mul, nnNorm_zpow]

  -- The additive Haar scaling cancels the change in the inverse-norm density.
  let D (x : K) := (↑‖x‖₊ : ℝ≥0∞)⁻¹
  have hD : Measurable D := by dsimp [D]; fun_prop
  let ν := (μ.withDensity D).comap (Units.val : Kˣ → K)
  have he : MeasurableEmbedding (Units.val : Kˣ → K) :=
    (IsOpenUnits.isOpenEmbedding_unitsVal (M := K)).measurableEmbedding
  let : ν.IsMulLeftInvariant := ⟨fun u ↦ by
    have hm : Measurable (u • · : K → K) := (measurableEmbedding_const_smul u).measurable
    have hmap : μ.map (u • · : K → K) = (↑‖u.val‖₊ : ℝ≥0∞)⁻¹ • μ := by
      ext s hs
      rw [Measure.map_apply hm hs, preimage_smul, ← distribHaarChar_mul μ, hχ,
        Units.val_inv_eq_inv_val, nnNorm_inv, ENNReal.coe_inv (by simp [u.ne_zero])]
      rfl
    ext s hs
    have hs' := he.measurableSet_image.mpr hs
    have hpre : (Units.val : Kˣ → K) '' ((u * ·) ⁻¹' s) =
        (u • · : K → K) ⁻¹' ((Units.val : Kˣ → K) '' s) := by
      change Units.val '' ((u • ·) ⁻¹' s) = _
      rw [preimage_smul, preimage_smul, ← image_smul, ← image_smul, image_image, image_image]
      rfl
    rw [Measure.map_apply (by fun_prop) hs, he.comap_apply, he.comap_apply, hpre,
      withDensity_apply _ (hs'.preimage hm), withDensity_apply _ hs']
    have hDmul (x : K) : D x = D (u • x) * ↑‖u.val‖₊ := by
      have hu : (↑‖u.val‖₊ : ℝ≥0∞) ≠ 0 := by simp [u.ne_zero]
      simp only [D, Units.smul_def, smul_eq_mul, nnNorm_mul, ENNReal.coe_mul]
      rw [ENNReal.mul_inv (Or.inl hu) (Or.inl ENNReal.coe_ne_top), mul_right_comm,
        ENNReal.inv_mul_cancel hu ENNReal.coe_ne_top, one_mul]
    calc
      (∫⁻ x in (u • ·) ⁻¹' (Units.val '' s), D x ∂μ) =
          ∫⁻ x in (u • ·) ⁻¹' (Units.val '' s), D (u • x) * ↑‖u.val‖₊ ∂μ :=
        lintegral_congr hDmul
      _ = _ := by
        rw [lintegral_mul_const' _ _ ENNReal.coe_ne_top, ← setLIntegral_map hs' hD hm, hmap,
          Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul, mul_right_comm,
          ENNReal.inv_mul_cancel (by simp [u.ne_zero]) ENNReal.coe_ne_top, one_mul]⟩

  -- The density equals one on integer units, the complement of the open unit ball in O.
  have hUo : IsOpen U := Submonoid.isOpen_units hO
  have hUunit : (Units.val : Kˣ → K) '' U = {x : K | ‖x‖ = 1} := by
    ext x
    refine ⟨?_, ?_⟩
    · rintro ⟨u, hu, rfl⟩
      exact (hUnorm u).mp hu
    · intro hx
      have hx₀ := norm_ne_zero_iff.mp (hx.trans_ne one_ne_zero)
      exact ⟨Units.mk0 x hx₀, (hUnorm _).mpr hx, rfl⟩
  have hUimage : (Units.val : Kˣ → K) '' U = (O : Set K) \ (p • (O : Set K)) := by
    rw [hUunit, hπball]
    ext x
    change ‖x‖ = 1 ↔ x ∈ (O : Set K) ∧ ¬ ‖x‖ < 1
    rw [hOmem, not_lt, le_antisymm_iff]
  have hνU : ν U = (1 - q⁻¹) * μ (O : Set K) := by
    rw [he.comap_apply, withDensity_apply _ (he.measurableSet_image.mpr hUo.measurableSet)]
    calc
      (∫⁻ x in Units.val '' U, D x ∂μ) = ∫⁻ _ in Units.val '' U, (1 : ℝ≥0∞) ∂μ := by
        apply setLIntegral_congr_fun (he.measurableSet_image.mpr hUo.measurableSet)
        rintro _ ⟨u, hu, rfl⟩
        simp [D, hUnnNorm u hu]
      _ = (1 - q⁻¹) * μ (O : Set K) := by
        have hsub : p • (O : Set K) ⊆ (O : Set K) := by
          rw [hπball]
          exact fun x hx ↦ (hOmem x).mpr hx.le
        have hπm : MeasurableSet (p • (O : Set K)) := by
          rw [hπball]
          exact (isOpen_lt continuous_norm continuous_const).measurableSet
        have hπf : μ (p • (O : Set K)) ≠ ⊤ :=
          ((measure_mono hsub).trans_lt hOf.lt_top).ne
        rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter, one_mul,
          hUimage, measure_sdiff hsub hπm.nullMeasurableSet hπf,
          hπmass, ENNReal.sub_mul (fun _ _ ↦ hOf), one_mul, div_eq_mul_inv, mul_comm q⁻¹]
  have hνf : ν U ≠ ⊤ := by
    rw [hνU]
    exact ENNReal.mul_ne_top ((tsub_le_self : 1 - q⁻¹ ≤ 1).trans_lt ENNReal.one_lt_top).ne hOf
  let : IsLocallyFiniteMeasure ν :=
    isLocallyFiniteMeasure_of_smulInvariant (G := Kˣ) hUo ⟨1, O.units.one_mem⟩ hνf
  let : SecondCountableTopology Kˣ := (Units.isEmbedding_val₀ (G₀ := K)).secondCountableTopology
  let η := Measure.haar (G := Kˣ)
  have hscale := Measure.isMulLeftInvariant_eq_smul ν η

  -- Haar uniqueness reduces the equality to the common normalization on U.
  let c := q / (q - 1)
  have hc : c * ν U = μ (O : Set K) := by
    have hqsub : q - 1 ≠ 0 := (tsub_pos_of_lt hq).ne'
    have hqsubf : q - 1 ≠ ⊤ := tsub_le_self.trans_lt hqf.lt_top |>.ne
    have hdiv : 1 - q⁻¹ = (q - 1) / q := by
      rw [div_eq_mul_inv, ENNReal.sub_mul (fun _ _ ↦ ENNReal.inv_ne_top.mpr hq₀),
        ENNReal.mul_inv_cancel hq₀ hqf, one_mul]
    rw [hνU, hdiv, ← mul_assoc, ENNReal.div_mul_div_cancel hqsub hqsubf,
      ENNReal.div_self hq₀ hqf, one_mul]
  have hη₀ : η U ≠ 0 := (hUo.measure_pos η ⟨1, O.units.one_mem⟩).ne'
  have hηf : η U ≠ ⊤ := by
    apply IsCompact.measure_ne_top
    apply (Units.isEmbedding_val₀ (G₀ := K)).isCompact_iff.mpr
    rw [hUunit]
    exact hOc.of_isClosed_subset (isClosed_eq continuous_norm continuous_const)
      (fun x hx ↦ (hOmem x).mpr hx.le)
  have ha : c * (↑(ν.haarScalarFactor η) : ℝ≥0∞) = μ (O : Set K) / η U := by
    apply (ENNReal.mul_left_inj hη₀ hηf).mp
    rw [mul_assoc, ENNReal.div_mul_cancel hη₀ hηf, ← hc]
    congr 1
    exact (congrArg (fun m : Measure Kˣ ↦ m U) hscale).symm
  change (differentMass(F, v) / η U) • η = c • ν
  rw [← finiteLocalAdditiveTamagawaMeasure_integers F v, hscale, ENNReal.smul_def, smul_smul, ha]

local notation "∞unitAt" => fun w : InfinitePlace F ↦
  Units.map (RingHom.toMonoidHom (RingHom.comp (Pi.evalRingHom InfinitePlace.Completion w)
    (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))))
local notation "finiteUnitAt" => fun v : Primes(F) ↦
  Units.map (RingHom.toMonoidHom (RingHom.comp
    (RestrictedProduct.evalRingHom (fun w : Primes(F) ↦ HeightOneSpectrum.adicCompletion F w) v)
    (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))))

/-- The product of local unit groups at infinity and at the selected finite places. -/
private abbrev IdeleCoordinates :=
  ((w : InfinitePlace F) → w.Completionˣ) × ((v : S) → (v.val.adicCompletion F)ˣ)

open Topology in
open scoped RestrictedProduct in
/-- Restricting idelic Haar measure to the subgroup of units outside S and projecting
away its compact tail gives a Haar measure on the selected local coordinates. -/
private theorem multiplicativeTamagawaMeasure_projected_haar :
    ∃ ν : Measure (IdeleCoordinates F S), ν.IsHaarMeasure ∧
      ∀ W : Set (IdeleCoordinates F S), MeasurableSet W →
        ν W = multiplicativeTamagawaMeasure F
          {g | ((fun w ↦ (∞unitAt) w g), (fun v : S ↦ (finiteUnitAt) v.val g)) ∈ W ∧
            ∀ v : Primes(F), v ∉ S → (finiteUnitAt) v g ∈ (v.adicCompletionIntegers F).units} := by
  let I := integralAdelesOutside F S
  let i := Units.map I.subtype.toMonoidHom
  let : Fact (∀ v : Primes(F), IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    ⟨fun _ ↦ Valued.isOpen_valuationSubring _⟩
  let : MeasurableSpace Iˣ := borel _
  let : BorelSpace Iˣ := ⟨rfl⟩
  let : BorelSpace 𝕀[F] := ⟨rfl⟩
  let (w : InfinitePlace F) : BorelSpace w.Completion := ⟨rfl⟩
  let (w : InfinitePlace F) : BorelSpace w.Completionˣ :=
    borelSpace_units_of_continuousInv₀ _
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let (w : InfinitePlace F) : SecondCountableTopology w.Completionˣ :=
    Units.isEmbedding_val₀.secondCountableTopology
  let (v : Primes(F)) : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
  let (v : Primes(F)) : SecondCountableTopology (v.adicCompletion F)ˣ :=
    Units.isEmbedding_val₀.secondCountableTopology
  let : BorelSpace (IdeleCoordinates F S) := inferInstance
  have hI : IsOpen (I : Set 𝔸[F]) := by
    change IsOpen (integralAdelesOutside F S : Set 𝔸[F])
    simp only [integralAdelesOutside, Subring.coe_iInf, Set.iInter_ofPred]
    exact (isOpen_restrictedProduct_forall_mem
      (G := fun v : Primes(F) ↦ v.adicCompletion F)
      (A := fun v ↦ v.adicCompletionIntegers F) (S : Set (Primes(F)))ᶜ
      (fun _ _ ↦ Valued.isOpen_valuationSubring _)).preimage continuous_snd
  have hrange : Set.range i = {g : 𝕀[F] | g.val ∈ I ∧ g.inv ∈ I} := by
    ext g
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u.val.property, u.inv.property⟩
    · rintro ⟨hg, hg'⟩
      exact ⟨⟨⟨g.val, hg⟩, ⟨g.inv, hg'⟩, Subtype.ext g.val_inv, Subtype.ext g.inv_val⟩,
        Units.ext rfl⟩
  have hi : IsOpenEmbedding i := by
    refine ⟨?_, hrange ▸
      (hI.preimage Units.continuous_val).inter (hI.preimage Units.continuous_coe_inv)⟩
    have hv : IsEmbedding (I.subtype : I → 𝔸[F]) := IsEmbedding.subtypeVal
    refine IsEmbedding.of_comp
      (hv.continuous.units_map I.subtype.toMonoidHom) Units.isEmbedding_embedProduct.continuous ?_
    exact (hv.prodMap (MulOpposite.opHomeomorph.isEmbedding.comp
      (hv.comp MulOpposite.opHomeomorph.symm.isEmbedding))).comp Units.isEmbedding_embedProduct
  have htail (g : 𝕀[F]) :
      g ∈ Set.range i ↔
        ∀ v : Primes(F), v ∉ S → (finiteUnitAt) v g ∈ (v.adicCompletionIntegers F).units := by
    rw [hrange]
    change (g.val ∈ integralAdelesOutside F S ∧ g.inv ∈ integralAdelesOutside F S) ↔ _
    simp only [integralAdelesOutside, Subring.mem_iInf]
    exact ⟨fun ⟨h, h'⟩ v hv ↦ ⟨h v hv, h' v hv⟩,
      fun h ↦ ⟨fun v hv ↦ (h v hv).1, fun v hv ↦ (h v hv).2⟩⟩
  let μ := multiplicativeTamagawaMeasure F
  let : μ.IsHaarMeasure :=
    (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.1
  let μI := μ.comap i
  let : μI.IsHaarMeasure := Measure.IsHaarMeasure.comap (mH := inferInstance) (f := i) μ hi
  obtain ⟨e, he, he', hcoord⟩ := integralAdelesOutside_factors F S
  obtain ⟨-, -, -, d, hd⟩ := sIdeleGroup_description F S
  let K := ((v : {v : Primes(F) // v ∉ S}) → v.val.adicCompletionIntegers F)ˣ
  let (v : {v : Primes(F) // v ∉ S}) : CompactSpace (v.val.adicCompletionIntegers F) :=
    compactSpace_adicCompletionIntegers v.val
  let : CompactSpace K := inferInstance
  let E : Iˣ ≃ₜ* ((SAdeleRing F S)ˣ × K) :=
    (Units.mapContinuousMulEquiv
      { e.toMulEquiv with continuous_toFun := he, continuous_invFun := he' }).trans
      (ContinuousMulEquiv.prodUnits _ _)
  let p := d.toMonoidHom.comp ((MonoidHom.fst _ _).comp E.toMonoidHom)
  have hp : IsProperMap (p : Iˣ → IdeleCoordinates F S) :=
    d.toHomeomorph.isProperMap.comp (isProperMap_fst_of_compactSpace.comp E.toHomeomorph.isProperMap)
  have hps : Surjective p := d.surjective.comp (Prod.fst_surjective.comp E.surjective)
  have hcoords (u : Iˣ) :
      p u = ((fun w ↦ (∞unitAt) w (i u)), (fun v : S ↦ (finiteUnitAt) v.val (i u))) := by
    have hval : ((E u).1).val = adeleProjection F S u.val.val := (hcoord u.val).1
    exact Prod.ext
      (funext fun w ↦ Units.ext (((hd (E u).1).1 w).trans
        (congrArg (fun a : SAdeleRing F S ↦ a.1 w) hval)))
      (funext fun v ↦ Units.ext (((hd (E u).1).2 v).trans
        (congrArg (fun a : SAdeleRing F S ↦ a.2 v) hval)))
  refine ⟨μI.map p, Measure.isHaarMeasure_map μI p hp.continuous hps
    (isProperMap_iff_tendsto_cocompact.mp hp).2, ?_⟩
  intro W hW
  rw [Measure.map_apply hp.continuous.measurable hW, hi.measurableEmbedding.comap_apply]
  congr 1
  ext g
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨hcoords u ▸ hu, (htail _).mp ⟨u, rfl⟩⟩
  · rintro ⟨hg, hg'⟩
    obtain ⟨u, rfl⟩ := (htail g).mpr hg'
    refine ⟨u, ?_, rfl⟩
    change p u ∈ W
    rw [hcoords u]
    exact hg

/-- The finite-place normalization rescales Haar measure by a positive finite constant. -/
private theorem finiteLocalMultiplicativeTamagawaMeasure_haar (v : Primes(F)) :
    (finiteLocalMultiplicativeTamagawaMeasure F v).IsHaarMeasure := by
  let μ := Measure.haar (G := (v.adicCompletion F)ˣ)
  let O := (v.adicCompletionIntegers F).units
  have hO : IsOpen (O : Set (v.adicCompletion F)ˣ) :=
    Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)
  have hK : IsCompact (O : Set (v.adicCompletion F)ˣ) :=
    Submonoid.units_isCompact (isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v))
  have hmass := hO.measure_pos μ ⟨1, O.one_mem⟩
  have hnorm : 0 < (v.asIdeal.absNorm : ℝ) :=
    Nat.cast_pos.mpr (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v))
  have hsqrt := Real.sqrt_pos_of_pos (pow_pos hnorm (differentExp(F, v)))
  change ((differentMass(F, v) / μ O) • μ).IsHaarMeasure
  exact Measure.IsHaarMeasure.smul μ
    (ENNReal.div_ne_zero.mpr ⟨ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top,
      hK.measure_ne_top (μ := μ)⟩)
    (ENNReal.div_ne_top (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hsqrt).ne') hmass.ne')

omit [NumberField F] in
private theorem infiniteLocalMultiplicative_isHaar (w : InfinitePlace F) :
    (infiniteLocalMultiplicativeTamagawaMeasure F w).IsHaarMeasure := by
  let : BorelSpace w.Completion := ⟨rfl⟩
  let := infiniteLocalAdditiveTamagawaMeasure_haar F w
  apply isHaarMeasure_comap_units_withDensity
  intro a ha
  by_cases h : w.IsReal
  · rw [infiniteLocalAdditiveTamagawaMeasure, dite_eq_left h]
    let e := (ringEquivRealOfIsReal h).symm
    have he : Measurable e := (isometryEquivRealOfIsReal h).symm.continuous.measurable
    rw [map_mul_left_map_ringEquiv e he volume _ real_map_mul_left_volume a ha, h.mult_eq_one]
    have hn : ‖e.symm a‖₊ = ‖a‖₊ := by
      ext
      exact (isometry_extensionEmbeddingOfIsReal h).norm_map_of_map_zero (map_zero _) a
    rw [hn]
  · let h' := InfinitePlace.not_isReal_iff_isComplex.mp h
    rw [infiniteLocalAdditiveTamagawaMeasure, dite_eq_right h]
    let e := (ringEquivComplexOfIsComplex h').symm
    have he : Measurable e := (isometryEquivComplexOfIsComplex h').symm.continuous.measurable
    have hscale (b : ℂ) (hb : b ≠ 0) : ((2 : ℕ) • (volume : Measure ℂ)).map (b * ·) =
        ((↑(‖b‖₊ ^ 2) : ℝ≥0∞))⁻¹ • ((2 : ℕ) • (volume : Measure ℂ)) := by
      rw [Measure.map_smul, complex_map_mul_left_volume b hb, ← Nat.cast_smul_eq_nsmul ENNReal,
        ← Nat.cast_smul_eq_nsmul ENNReal, smul_smul, smul_smul, mul_comm]
      exact (measurable_const_mul b).aemeasurable
    rw [map_mul_left_map_ringEquiv e he _ _ hscale a ha, h'.mult_eq_two]
    have hn : ‖e.symm a‖₊ = ‖a‖₊ := by
      ext
      exact (isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) a
    rw [hn]

-- The public statement specializes the preceding lemma to number fields.
set_option linter.unusedSectionVars false in
/-- The weighted additive measure on a real or complex completion is multiplicative Haar
measure. The additive Jacobian of multiplication by a unit cancels the change in density. -/
theorem infiniteLocalMultiplicativeTamagawaMeasure_haar (w : InfinitePlace F) :
    (infiniteLocalMultiplicativeTamagawaMeasure F w).IsHaarMeasure :=
  infiniteLocalMultiplicative_isHaar F w

/-- In logarithmic coordinates the omitted place is recovered from the sum.
The strip has total log norm in `[0,1]` and the remaining logs in the regulator
parallelotope. It includes all signs and phases. -/
def archimedeanRegulatorStrip :
    Set ((w : InfinitePlace F) → w.Completionˣ) :=
  {a | (∑ w, (w.mult : ℝ) * Real.log ‖(a w).val‖) ∈ Icc 0 1 ∧
    (fun w : {w : InfinitePlace F // w ≠ Units.dirichletUnitTheorem.w₀ (K := F)} ↦
      (w.val.mult : ℝ) * Real.log ‖(a w.val).val‖) ∈
      regulatorParallelotope F (Units.basisModTorsion F)}

/-- The regulator strip is measurable because the local logarithms and parallelotope are. -/
private theorem archimedeanRegulatorStrip_measurableSet :
    MeasurableSet (archimedeanRegulatorStrip F) := by
  let (w : InfinitePlace F) : BorelSpace w.Completion := ⟨rfl⟩
  let (w : InfinitePlace F) : BorelSpace w.Completionˣ := borelSpace_units_of_continuousInv₀ _
  have hlog (w : InfinitePlace F) : Measurable
      (fun a : (w : InfinitePlace F) → w.Completionˣ ↦ (w.mult : ℝ) * Real.log ‖(a w).val‖) :=
    measurable_const.mul
      (Real.measurable_log.comp ((continuous_norm.comp Units.continuous_val).measurable.comp
        (measurable_pi_apply w)))
  have hP : MeasurableSet (regulatorParallelotope F (Units.basisModTorsion F)) :=
    ZSpan.fundamentalDomain_measurableSet _
  exact (measurableSet_Icc.preimage (Finset.measurable_sum Finset.univ fun w _ ↦ hlog w)).inter
    (hP.preimage (Measurable.of_eval fun w ↦ hlog w.val))

local notation "archRegulatorMass(" F ")" =>
  ENNReal.ofReal ((2 : ℝ) ^ InfinitePlace.nrRealPlaces F *
    (2 * Real.pi) ^ InfinitePlace.nrComplexPlaces F * Units.regulator F)

/-- The integral of `dt / t` over `(e^a, e^b]` is `b - a`. -/
private theorem infiniteLocalMultiplicativeTamagawaMeasure_regulatorStrip_Ioc_exp {a b : ℝ} (hab : a ≤ b) :
    ∫⁻ t in Ioc (Real.exp a) (Real.exp b), ENNReal.ofReal t⁻¹ = ENNReal.ofReal (b - a) := by
  have hpos {t : ℝ} (ht : t ∈ Ioc (Real.exp a) (Real.exp b)) : 0 < t :=
    (Real.exp_pos a).trans ht.1
  have hint : IntegrableOn (fun t : ℝ ↦ t⁻¹) (Ioc (Real.exp a) (Real.exp b)) :=
    (ContinuousOn.integrableOn_Icc (f := fun t : ℝ ↦ t⁻¹) (continuousOn_inv₀.mono
      fun t ht ↦ ((Real.exp_pos a).trans_le ht.1).ne')).mono_set Ioc_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hint
      ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall
        fun _ ht ↦ inv_nonneg.mpr (hpos ht).le)),
    ← intervalIntegral.integral_of_le (Real.exp_le_exp.mpr hab),
    integral_inv_of_pos (Real.exp_pos a) (Real.exp_pos b), ← Real.exp_sub, Real.log_exp]

/-- On the real line, `dt / |t|` gives the band `log |t| ∈ (a, b]` mass `2 (b - a)`. -/
private theorem infiniteLocalMultiplicativeTamagawaMeasure_regulatorStrip_lintegral_real {a b : ℝ} (hab : a ≤ b) :
    ∫⁻ t in {t : ℝ | t ≠ 0 ∧ Real.log ‖t‖ ∈ Ioc a b}, (↑(‖t‖₊ ^ 1) : ℝ≥0∞)⁻¹ =
      2 * ENNReal.ofReal (b - a) := by
  set A := Ioc (Real.exp a) (Real.exp b)
  have hS : {t : ℝ | t ≠ 0 ∧ Real.log ‖t‖ ∈ Ioc a b} = A ∪ Neg.neg ⁻¹' A := by
    ext t
    simp only [mem_ofPred_eq, mem_union, mem_preimage, A, mem_Ioc, Real.norm_eq_abs]
    constructor
    · rintro ⟨ht, h1, h2⟩
      have h1' := Real.exp_lt_exp.mpr h1
      have h2' := Real.exp_le_exp.mpr h2
      rw [Real.exp_log (abs_pos.mpr ht)] at h1' h2'
      rcases lt_or_gt_of_ne ht with h | h
      · right; rw [abs_of_neg h] at h1' h2'; exact ⟨h1', h2'⟩
      · left; rw [abs_of_pos h] at h1' h2'; exact ⟨h1', h2'⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · have ht : 0 < t := (Real.exp_pos a).trans h1
        refine ⟨ht.ne', ?_, ?_⟩ <;> rw [abs_of_pos ht]
        · exact (Real.lt_log_iff_exp_lt ht).mpr h1
        · exact (Real.log_le_iff_le_exp ht).mpr h2
      · have ht : 0 < -t := (Real.exp_pos a).trans h1
        refine ⟨by linarith, ?_, ?_⟩ <;> rw [abs_of_neg (by linarith)]
        · exact (Real.lt_log_iff_exp_lt ht).mpr h1
        · exact (Real.log_le_iff_le_exp ht).mpr h2
  have hdisj : Disjoint A (Neg.neg ⁻¹' A) := by
    rw [Set.disjoint_left]
    intro t ht ht'
    have h1 : 0 < t := (Real.exp_pos a).trans ht.1
    have h2 : 0 < -t := (Real.exp_pos a).trans ht'.1
    linarith
  have hf (t : ℝ) (ht : 0 < t) : (↑(‖t‖₊ ^ 1) : ℝ≥0∞)⁻¹ = ENNReal.ofReal t⁻¹ := by
    rw [pow_one, ← ENNReal.ofReal_coe_nnreal, coe_nnNorm, Real.norm_eq_abs, abs_of_pos ht,
      ENNReal.ofReal_inv_of_pos ht]
  have hA : ∫⁻ t in A, (↑(‖t‖₊ ^ 1) : ℝ≥0∞)⁻¹ = ENNReal.ofReal (b - a) := by
    rw [setLIntegral_congr_fun measurableSet_Ioc
      (fun t ht ↦ hf t ((Real.exp_pos a).trans ht.1)), infiniteLocalMultiplicativeTamagawaMeasure_regulatorStrip_Ioc_exp hab]
  have hneg : ∫⁻ t in Neg.neg ⁻¹' A, (↑(‖t‖₊ ^ 1) : ℝ≥0∞)⁻¹ =
      ∫⁻ t in A, (↑(‖t‖₊ ^ 1) : ℝ≥0∞)⁻¹ := by
    have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).setLIntegral_comp_preimage
      (s := A) measurableSet_Ioc (f := fun t : ℝ ↦ (↑(‖t‖₊ ^ 1) : ℝ≥0∞)⁻¹) (by fun_prop)
    simpa only [nnNorm_neg] using h
  rw [hS, lintegral_union (measurableSet_Ioc.preimage measurable_neg) hdisj, hneg, hA, two_mul]

/-- On the plane, `2 dA / |z|²` gives the band `2 log |z| ∈ (a, b]` mass `2π (b - a)`. -/
private theorem infiniteLocalMultiplicativeTamagawaMeasure_regulatorStrip_lintegral_complex {a b : ℝ} (hab : a ≤ b) :
    ∫⁻ z in {z : ℂ | z ≠ 0 ∧ 2 * Real.log ‖z‖ ∈ Ioc a b}, (↑(‖z‖₊ ^ 2) : ℝ≥0∞)⁻¹
        ∂(2 • (volume : Measure ℂ)) =
      ENNReal.ofReal (2 * Real.pi) * ENNReal.ofReal (b - a) := by
  set S := {z : ℂ | z ≠ 0 ∧ 2 * Real.log ‖z‖ ∈ Ioc a b}
  set A := Ioc (Real.exp (a / 2)) (Real.exp (b / 2))
  have hSm : MeasurableSet S :=
    show MeasurableSet ({(0 : ℂ)}ᶜ ∩ (fun z : ℂ ↦ 2 * Real.log ‖z‖) ⁻¹' Ioc a b) from
      (measurableSet_singleton 0).compl.inter (measurableSet_Ioc.preimage
        (measurable_const.mul (Real.measurable_log.comp measurable_norm)))
  have hmemS (r θ : ℝ) (hr : 0 < r) : Complex.polarCoord.symm (r, θ) ∈ S ↔ r ∈ A := by
    have hn : ‖Complex.polarCoord.symm (r, θ)‖ = r := by
      rw [Complex.norm_polarCoord_symm, abs_of_pos hr]
    have hz : Complex.polarCoord.symm (r, θ) ≠ 0 := by
      rw [← norm_ne_zero_iff, hn]
      exact hr.ne'
    simp only [S, A, mem_ofPred_eq, mem_Ioc, hn]
    constructor
    · rintro ⟨-, h1, h2⟩
      exact ⟨(Real.lt_log_iff_exp_lt hr).mp (by linarith), (Real.log_le_iff_le_exp hr).mp (by linarith)⟩
    · rintro ⟨h1, h2⟩
      have := (Real.lt_log_iff_exp_lt hr).mpr h1
      have := (Real.log_le_iff_le_exp hr).mpr h2
      exact ⟨hz, by linarith, by linarith⟩
  rw [Measure.restrict_smul, lintegral_smul_measure, ← lintegral_indicator hSm,
    ← Complex.lintegral_comp_polarCoord_symm]
  have hcongr : ∀ p ∈ polarCoord.target, ENNReal.ofReal p.1 •
      S.indicator (fun z : ℂ ↦ (↑(‖z‖₊ ^ 2) : ℝ≥0∞)⁻¹) (Complex.polarCoord.symm p) =
      A.indicator (fun r ↦ ENNReal.ofReal r⁻¹) p.1 * (Ioo (-Real.pi) Real.pi).indicator 1 p.2 := by
    rintro ⟨r, θ⟩ ⟨hr, hθ⟩
    simp only [mem_Ioi] at hr
    dsimp only
    rw [indicator_of_mem (show θ ∈ Ioo (-Real.pi) Real.pi from hθ), Pi.one_apply, mul_one]
    by_cases hA : r ∈ A
    · rw [indicator_of_mem ((hmemS r θ hr).mpr hA), indicator_of_mem hA, smul_eq_mul]
      have hn : ‖Complex.polarCoord.symm (r, θ)‖₊ = r.toNNReal := by
        ext
        simp only [coe_nnNorm, Complex.norm_polarCoord_symm, abs_of_pos hr,
          Real.coe_toNNReal _ hr.le]
      have hx : (((r.toNNReal ^ 2 : ℝ≥0) : ℝ≥0∞))⁻¹ = ENNReal.ofReal ((r ^ 2)⁻¹) := by
        rw [ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.ofReal_coe_nnreal]
        congr 2
        simp [hr.le]
      rw [hn, hx, ← ENNReal.ofReal_mul hr.le]
      congr 1
      field_simp
    · rw [indicator_of_notMem (fun h ↦ hA ((hmemS r θ hr).mp h)), indicator_of_notMem hA, smul_zero]
  have htarget : MeasurableSet polarCoord.target := measurableSet_Ioi.prod measurableSet_Ioo
  rw [setLIntegral_congr_fun htarget hcongr, show polarCoord.target =
      Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi from rfl, Measure.volume_eq_prod,
    ← Measure.prod_restrict,
    lintegral_prod_mul (f := A.indicator (fun r ↦ ENNReal.ofReal r⁻¹))
      (g := (Ioo (-Real.pi) Real.pi).indicator 1)
      ((Measurable.ennreal_ofReal measurable_inv).indicator measurableSet_Ioc).aemeasurable
      (measurable_one.indicator measurableSet_Ioo).aemeasurable,
    lintegral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
    inter_eq_self_of_subset_left (fun r (hr : r ∈ A) ↦ mem_Ioi.mpr ((Real.exp_pos _).trans hr.1)),
    infiniteLocalMultiplicativeTamagawaMeasure_regulatorStrip_Ioc_exp (by linarith), lintegral_indicator_one measurableSet_Ioo,
    Measure.restrict_apply_self, Real.volume_Ioo, nsmul_eq_mul, Nat.cast_ofNat,
    show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
    ← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul zero_le_two,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

/-- The regulator parallelotope has volume equal to the regulator. -/
private theorem infiniteLocalMultiplicativeTamagawaMeasure_regulatorStrip_parallelotope :
    volume (regulatorParallelotope F (Units.basisModTorsion F)) =
      ENNReal.ofReal (Units.regulator F) := by
  set B := ((Units.basisModTorsion F).map (Units.logEmbeddingEquiv F)).ofZLatticeBasis ℝ
    (Units.unitLattice F)
  have hspan : Submodule.span ℤ (Set.range B) = Units.unitLattice F :=
    Module.Basis.ofZLatticeBasis_span ℝ (Units.unitLattice F) _
  have hfd := ZSpan.isAddFundamentalDomain B (volume : Measure ({w : InfinitePlace F // w ≠ Units.dirichletUnitTheorem.w₀} → ℝ))
  rw [hspan] at hfd
  have hcov := ZLattice.covolume_eq_measure_fundamentalDomain (Units.unitLattice F) volume hfd
  have hfin : volume (ZSpan.fundamentalDomain B) ≠ ⊤ :=
    (ZSpan.fundamentalDomain_isBounded B).measure_lt_top.ne
  change volume (ZSpan.fundamentalDomain B) = _
  rw [Units.regulator, hcov, Measure.real, ENNReal.ofReal_toReal hfin]


/-- At a real place, the band `log ‖x‖ ∈ (a, b]` has multiplicative mass `2 (b - a)`. -/
private theorem infiniteLocalMultiplicativeTamagawaMeasure_regulatorStrip_real (w : InfinitePlace F) (h : w.IsReal) {a b : ℝ} (hab : a ≤ b) :
    infiniteLocalMultiplicativeTamagawaMeasure F w
      {x | (w.mult : ℝ) * Real.log ‖x.val‖ ∈ Ioc a b} = 2 * ENNReal.ofReal (b - a) := by
  let : BorelSpace w.Completion := ⟨rfl⟩
  let : BorelSpace w.Completionˣ := borelSpace_units_of_continuousInv₀ _
  let e := (isometryEquivRealOfIsReal h).toHomeomorph.toMeasurableEquiv
  have hval := (IsOpenUnits.isOpenEmbedding_unitsVal (M := w.Completion)).measurableEmbedding
  have hnorm (t : ℝ) : ‖e.symm t‖ = ‖t‖ :=
    (isometryEquivRealOfIsReal h).symm.isometry.norm_map_of_map_zero
      (map_zero (ringEquivRealOfIsReal h).symm) t
  set S : Set w.Completion := {x | x ≠ 0 ∧ (w.mult : ℝ) * Real.log ‖x‖ ∈ Ioc a b}
  have hSm : MeasurableSet S :=
    show MeasurableSet ({(0 : w.Completion)}ᶜ ∩ (fun x : w.Completion ↦ (w.mult : ℝ) * Real.log ‖x‖) ⁻¹' Ioc a b) from
      (measurableSet_singleton 0).compl.inter (measurableSet_Ioc.preimage
        (measurable_const.mul (Real.measurable_log.comp measurable_norm)))
  have hsub : S ⊆ range (Units.val : w.Completionˣ → w.Completion) :=
    fun x hx ↦ ⟨Units.mk0 x hx.1, rfl⟩
  have hset : {x : w.Completionˣ | (w.mult : ℝ) * Real.log ‖x.val‖ ∈ Ioc a b} =
      Units.val ⁻¹' S := by
    ext x
    simp [S]
  rw [hset]
  rw [infiniteLocalMultiplicativeTamagawaMeasure, hval.comap_preimage,
    inter_eq_self_of_subset_left hsub, withDensity_apply _ hSm,
    infiniteLocalAdditiveTamagawaMeasure, dite_eq_left h]
  change (∫⁻ x in S, (↑(‖x‖₊ ^ w.mult) : ℝ≥0∞)⁻¹ ∂volume.map e.symm) = _
  rw [e.symm.restrict_map, e.symm.measurableEmbedding.lintegral_map]
  have hz (t : ℝ) : e.symm t ≠ 0 ↔ t ≠ 0 := by
    rw [← norm_ne_zero_iff, hnorm, norm_ne_zero_iff]
  have hpre : e.symm ⁻¹' S = {t : ℝ | t ≠ 0 ∧ Real.log ‖t‖ ∈ Ioc a b} := by
    ext t
    simp only [S, mem_preimage, mem_ofPred_eq, hnorm, h.mult_eq_one, Nat.cast_one, one_mul, hz]
  have hnn (t : ℝ) : ‖e.symm t‖₊ = ‖t‖₊ := NNReal.eq (hnorm t)
  rw [hpre]
  simp only [hnn, h.mult_eq_one]
  exact infiniteLocalMultiplicativeTamagawaMeasure_regulatorStrip_lintegral_real hab

/-- At a complex place, the band `2 log ‖x‖ ∈ (a, b]` has multiplicative mass `2π (b - a)`. -/
private theorem infiniteLocalMultiplicativeTamagawaMeasure_regulatorStrip_complex (w : InfinitePlace F) (h : ¬ w.IsReal) {a b : ℝ} (hab : a ≤ b) :
    infiniteLocalMultiplicativeTamagawaMeasure F w
      {x | (w.mult : ℝ) * Real.log ‖x.val‖ ∈ Ioc a b} =
        ENNReal.ofReal (2 * Real.pi) * ENNReal.ofReal (b - a) := by
  have h' := InfinitePlace.not_isReal_iff_isComplex.mp h
  let : BorelSpace w.Completion := ⟨rfl⟩
  let : BorelSpace w.Completionˣ := borelSpace_units_of_continuousInv₀ _
  let e := (isometryEquivComplexOfIsComplex h').toHomeomorph.toMeasurableEquiv
  have hval := (IsOpenUnits.isOpenEmbedding_unitsVal (M := w.Completion)).measurableEmbedding
  have hnorm (z : ℂ) : ‖e.symm z‖ = ‖z‖ :=
    (isometryEquivComplexOfIsComplex h').symm.isometry.norm_map_of_map_zero
      (map_zero (ringEquivComplexOfIsComplex h').symm) z
  set S : Set w.Completion := {x | x ≠ 0 ∧ (w.mult : ℝ) * Real.log ‖x‖ ∈ Ioc a b}
  have hSm : MeasurableSet S :=
    show MeasurableSet ({(0 : w.Completion)}ᶜ ∩ (fun x : w.Completion ↦ (w.mult : ℝ) * Real.log ‖x‖) ⁻¹' Ioc a b) from
      (measurableSet_singleton 0).compl.inter (measurableSet_Ioc.preimage
        (measurable_const.mul (Real.measurable_log.comp measurable_norm)))
  have hsub : S ⊆ range (Units.val : w.Completionˣ → w.Completion) :=
    fun x hx ↦ ⟨Units.mk0 x hx.1, rfl⟩
  have hset : {x : w.Completionˣ | (w.mult : ℝ) * Real.log ‖x.val‖ ∈ Ioc a b} =
      Units.val ⁻¹' S := by
    ext x
    simp [S]
  rw [hset]
  rw [infiniteLocalMultiplicativeTamagawaMeasure, hval.comap_preimage,
    inter_eq_self_of_subset_left hsub, withDensity_apply _ hSm,
    infiniteLocalAdditiveTamagawaMeasure, dite_eq_right h]
  change (∫⁻ x in S, (↑(‖x‖₊ ^ w.mult) : ℝ≥0∞)⁻¹ ∂(2 • (volume : Measure ℂ)).map e.symm) = _
  rw [e.symm.restrict_map, e.symm.measurableEmbedding.lintegral_map]
  have hz (z : ℂ) : e.symm z ≠ 0 ↔ z ≠ 0 := by
    rw [← norm_ne_zero_iff, hnorm, norm_ne_zero_iff]
  have hpre : e.symm ⁻¹' S = {z : ℂ | z ≠ 0 ∧ 2 * Real.log ‖z‖ ∈ Ioc a b} := by
    ext z
    simp only [S, mem_preimage, mem_ofPred_eq, hnorm, h'.mult_eq_two, Nat.cast_ofNat, hz]
  have hnn (z : ℂ) : ‖e.symm z‖₊ = ‖z‖₊ := NNReal.eq (hnorm z)
  rw [hpre]
  simp only [hnn, h'.mult_eq_two]
  exact infiniteLocalMultiplicativeTamagawaMeasure_regulatorStrip_lintegral_complex hab

/-- The local multiplicative measure pushed forward by the normalized log norm is
`2` or `2π` times Lebesgue measure. -/
private theorem infiniteLocalMultiplicativeTamagawaMeasure_regulatorStrip_map (w : InfinitePlace F) :
    (infiniteLocalMultiplicativeTamagawaMeasure F w).map
      (fun x : w.Completionˣ ↦ (w.mult : ℝ) * Real.log ‖x.val‖) =
        (if w.IsReal then (2 : ℝ≥0) else Real.toNNReal (2 * Real.pi)) • volume := by
  let : BorelSpace w.Completion := ⟨rfl⟩
  let : BorelSpace w.Completionˣ := borelSpace_units_of_continuousInv₀ _
  have hmeas : Measurable (fun x : w.Completionˣ ↦ (w.mult : ℝ) * Real.log ‖x.val‖) :=
    measurable_const.mul (Real.measurable_log.comp
      (continuous_norm.comp Units.continuous_val).measurable)
  symm
  refine Measure.ext_of_Ioc' (α := ℝ) _ _ (fun a b _ ↦ ?_) (fun a b hab ↦ ?_)
  · rw [smul_apply, Real.volume_Ioc, ENNReal.smul_def, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top
  · rw [Measure.map_apply hmeas measurableSet_Ioc, smul_apply, Real.volume_Ioc,
      ENNReal.smul_def, smul_eq_mul]
    split_ifs with h
    · rw [ENNReal.coe_ofNat]
      exact (infiniteLocalMultiplicativeTamagawaMeasure_regulatorStrip_real F w h hab.le).symm
    · exact (infiniteLocalMultiplicativeTamagawaMeasure_regulatorStrip_complex F w h hab.le).symm

/-- Splitting off the omitted place: the strip over a set of log coordinates has the
volume of that set. -/
private theorem infiniteLocalMultiplicativeTamagawaMeasure_regulatorStrip_volume (P : Set ({w : InfinitePlace F // w ≠ Units.dirichletUnitTheorem.w₀} → ℝ))
    (hP : MeasurableSet P) :
    volume {y : InfinitePlace F → ℝ | ∑ w, y w ∈ Icc 0 1 ∧
      (fun w : {w : InfinitePlace F // w ≠ Units.dirichletUnitTheorem.w₀} ↦ y w.val) ∈ P} =
      volume P := by
  let p : InfinitePlace F → Prop := (· ≠ Units.dirichletUnitTheorem.w₀)
  have he := measurePreserving_piEquivPiSubtypeProd (fun _ : InfinitePlace F ↦ (volume : Measure ℝ)) p
  let : Unique {w // ¬ p w} := ⟨⟨⟨Units.dirichletUnitTheorem.w₀ (K := F), not_not.mpr rfl⟩⟩, fun w ↦ Subtype.ext (not_not.mp w.2)⟩
  set T : Set (({w // p w} → ℝ) × ({w // ¬ p w} → ℝ)) :=
    {z | z.1 ∈ P ∧ ∑ w, z.1 w + ∑ w, z.2 w ∈ Icc 0 1}
  have h1 : Measurable
      (fun z : ({w // p w} → ℝ) × ({w // ¬ p w} → ℝ) ↦ ∑ w, z.1 w + ∑ w, z.2 w) :=
    (Finset.measurable_sum Finset.univ fun (w : {w // p w}) _ ↦
      (measurable_pi_apply w).comp measurable_fst).add
    (Finset.measurable_sum Finset.univ fun (w : {w // ¬ p w}) _ ↦
      (measurable_pi_apply w).comp measurable_snd)
  have hT : MeasurableSet T := (hP.preimage measurable_fst).inter (measurableSet_Icc.preimage h1)
  have hpre : {y : InfinitePlace F → ℝ | ∑ w, y w ∈ Icc 0 1 ∧
      (fun w : {w : InfinitePlace F // w ≠ Units.dirichletUnitTheorem.w₀} ↦ y w.val) ∈ P} =
      MeasurableEquiv.piEquivPiSubtypeProd (fun _ ↦ ℝ) p ⁻¹' T := by
    ext y
    simp only [T, mem_preimage, mem_ofPred_eq, MeasurableEquiv.piEquivPiSubtypeProd,
      MeasurableEquiv.coe_mk, Equiv.piEquivPiSubtypeProd_apply]
    rw [Fintype.sum_subtype_add_sum_subtype p y]
    exact and_comm
  have hslice (z : {w // p w} → ℝ) :
      Measure.pi (fun _ : {w // ¬ p w} ↦ (volume : Measure ℝ)) (Prod.mk z ⁻¹' T) =
        P.indicator 1 z := by
    by_cases hz : z ∈ P
    · rw [indicator_of_mem hz, Pi.one_apply]
      have hset : Prod.mk z ⁻¹' T = Set.univ.pi fun _ ↦ Icc (-∑ w, z w) (1 - ∑ w, z w) := by
        ext u
        simp only [T, mem_preimage, mem_ofPred_eq, mem_Icc, hz, true_and, mem_univ_pi,
          Fintype.sum_unique, Unique.forall_iff]
        constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
      rw [hset, Measure.pi_pi, Finset.prod_const, Finset.card_univ, Fintype.card_unique, pow_one,
        Real.volume_Icc]
      norm_num
    · rw [indicator_of_notMem hz]
      have : Prod.mk z ⁻¹' T = ∅ := by
        ext u
        simp [T, hz]
      rw [this, measure_empty]
  rw [hpre, volume_pi, he.measure_preimage hT.nullMeasurableSet, Measure.prod_apply hT]
  simp_rw [hslice]
  exact lintegral_indicator_one hP

/-- The archimedean product measure of the regulator strip is the regulator times the
full sign and angular masses. In normalized radial logarithms each real place
contributes `2 dx` and each complex place contributes `2π dx`. Splitting off the
sum coordinate has Jacobian of absolute value one. -/
theorem infiniteLocalMultiplicativeTamagawaMeasure_regulatorStrip :
    Measure.pi (infiniteLocalMultiplicativeTamagawaMeasure F)
      (archimedeanRegulatorStrip F) = archRegulatorMass(F) := by
  let (w : InfinitePlace F) : BorelSpace w.Completion := ⟨rfl⟩
  let (w : InfinitePlace F) : BorelSpace w.Completionˣ := borelSpace_units_of_continuousInv₀ _
  set f : (w : InfinitePlace F) → w.Completionˣ → ℝ :=
    fun w x ↦ (w.mult : ℝ) * Real.log ‖x.val‖
  set c : InfinitePlace F → ℝ≥0 :=
    fun w ↦ if w.IsReal then (2 : ℝ≥0) else Real.toNNReal (2 * Real.pi)
  have hf (w : InfinitePlace F) : Measurable (f w) :=
    measurable_const.mul (Real.measurable_log.comp
      (continuous_norm.comp Units.continuous_val).measurable)
  have hmap (w : InfinitePlace F) :
      (infiniteLocalMultiplicativeTamagawaMeasure F w).map (f w) = c w • volume :=
    infiniteLocalMultiplicativeTamagawaMeasure_regulatorStrip_map F w
  have : ∀ w, SigmaFinite ((infiniteLocalMultiplicativeTamagawaMeasure F w).map (f w)) :=
    fun w ↦ by rw [hmap w]; infer_instance
  set P := regulatorParallelotope F (Units.basisModTorsion F)
  have hP : MeasurableSet P := ZSpan.fundamentalDomain_measurableSet _
  set T := {y : InfinitePlace F → ℝ | ∑ w, y w ∈ Icc 0 1 ∧
      (fun w : {w : InfinitePlace F // w ≠ Units.dirichletUnitTheorem.w₀} ↦ y w.val) ∈ P}
  have hT : MeasurableSet T :=
    show MeasurableSet ((fun y : InfinitePlace F → ℝ ↦ ∑ w, y w) ⁻¹' Icc 0 1 ∩
        (fun y : InfinitePlace F → ℝ ↦
          fun w : {w : InfinitePlace F // w ≠ Units.dirichletUnitTheorem.w₀} ↦ y w.val) ⁻¹' P) from
      (measurableSet_Icc.preimage (Finset.measurable_sum _ fun w _ ↦ measurable_pi_apply w)).inter
        (hP.preimage (Measurable.of_eval
          fun (w : {w : InfinitePlace F // w ≠ Units.dirichletUnitTheorem.w₀}) ↦
            measurable_pi_apply w.val))
  have hstrip : archimedeanRegulatorStrip F = (fun x w ↦ f w (x w)) ⁻¹' T := rfl
  have hpi : Measure.pi (fun w ↦ (infiniteLocalMultiplicativeTamagawaMeasure F w).map (f w)) =
      (∏ w, c w) • volume := by
    refine Measure.pi_eq fun s hs ↦ ?_
    rw [smul_apply, volume_pi_pi, ENNReal.smul_def, smul_eq_mul]
    push_cast
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun w _ ↦ ?_
    rw [hmap w, smul_apply, ENNReal.smul_def, smul_eq_mul]
  have hL : Measurable (fun (x : (w : InfinitePlace F) → w.Completionˣ) (w : InfinitePlace F) ↦
      f w (x w)) := Measurable.of_eval fun w ↦ (hf w).comp (measurable_pi_apply w)
  rw [hstrip, ← Measure.map_apply hL hT,
    Measure.pi_map_pi (fun w ↦ (hf w).aemeasurable), hpi, smul_apply, ENNReal.smul_def,
    smul_eq_mul, infiniteLocalMultiplicativeTamagawaMeasure_regulatorStrip_volume F P hP, infiniteLocalMultiplicativeTamagawaMeasure_regulatorStrip_parallelotope F]
  have hc : ((∏ w, c w : ℝ≥0) : ℝ) = (2 : ℝ) ^ InfinitePlace.nrRealPlaces F *
      (2 * Real.pi) ^ InfinitePlace.nrComplexPlaces F := by
    rw [NNReal.coe_prod]
    simp only [c, apply_ite NNReal.toReal, NNReal.coe_ofNat, Real.coe_toNNReal _ (by positivity : (0:ℝ) ≤ 2 * Real.pi)]
    rw [Finset.prod_ite]
    simp only [Finset.prod_const, ← Fintype.card_subtype, InfinitePlace.not_isReal_iff_isComplex]
  rw [← ENNReal.ofReal_coe_nnreal, hc, ← ENNReal.ofReal_mul (by positivity)]

/-- An idele lies in the integral idele units exactly when it is a unit at every finite place. -/
private theorem multiplicativeTamagawaMeasure_regulatorStrip_mem_integral (g : 𝕀[F]) :
    g ∈ (Units.map (integralAdelesOutside F ∅).subtype.toMonoidHom).range ↔
      ∀ v : Primes(F), (finiteUnitAt) v g ∈ (v.adicCompletionIntegers F).units := by
  have hmem (a : 𝔸[F]) : a ∈ integralAdelesOutside F ∅ ↔
      ∀ v : Primes(F), a.2 v ∈ v.adicCompletionIntegers F := by
    simp only [integralAdelesOutside, Subring.mem_iInf, Finset.notMem_empty, not_false_eq_true,
      true_implies]
    rfl
  constructor
  · rintro ⟨u, rfl⟩ v
    exact ⟨(hmem _).mp u.val.property v, (hmem _).mp u.inv.property v⟩
  · intro h
    exact ⟨⟨⟨g.val, (hmem _).mpr fun v ↦ (h v).1⟩, ⟨g.inv, (hmem _).mpr fun v ↦ (h v).2⟩,
      Subtype.ext g.val_inv, Subtype.ext g.inv_val⟩, Units.ext rfl⟩

/-- For an idele that is a unit at every finite place, the logarithm of its norm is the
sum of the weighted archimedean logarithms. -/
private theorem multiplicativeTamagawaMeasure_regulatorStrip_log_norm (g : 𝕀[F])
    (hg : ∀ v : Primes(F), (finiteUnitAt) v g ∈ (v.adicCompletionIntegers F).units) :
    Real.log ((ideleNorm F g : ℝ≥0) : ℝ) =
      ∑ w : InfinitePlace F, (w.mult : ℝ) * Real.log ‖g.val.1 w‖ := by
  have hfin (v : Primes(F)) : ‖g.val.2 v‖ = 1 := by
    apply Valued.toNormedField.norm_eq_one_iff.mpr
    exact (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one
      (a := (finiteUnitAt) v g)).mp (hg v)
  have hne (w : InfinitePlace F) : ‖g.val.1 w‖ ≠ 0 :=
    norm_ne_zero_iff.mpr ((∞unitAt) w g).ne_zero
  rw [((ideleNorm_spec F).1 g).2]
  simp only [hfin, finprod_one, mul_one]
  rw [Real.log_prod (fun w _ ↦ pow_ne_zero _ (hne w))]
  simp only [Real.log_pow]

/-- A principal idele that is a unit at every finite place comes from a global unit. -/
private theorem multiplicativeTamagawaMeasure_regulatorStrip_unit (x : Fˣ)
    (hx : ∀ v : Primes(F), (finiteUnitAt) v (IdeleGroup.unitEmbedding (𝓞 F) F x) ∈
      (v.adicCompletionIntegers F).units) :
    ∃ u : (𝓞 F)ˣ, Units.map (algebraMap (𝓞 F) F).toMonoidHom u = x := by
  obtain ⟨a, ha⟩ :=
    (multiplicativeTamagawaMeasure_regulatorStrip_mem_integral F _).mpr hx
  have lift (y : F) (hy : algebraMap F (AdeleRing (𝓞 F) F) y ∈ integralAdelesOutside F ∅) :
      y ∈ (algebraMap (𝓞 F) F).range := by
    have h := (diagonal_mem_integralAdelesOutside F ∅ y).mp hy
    rwa [Finset.coe_empty, integer_empty, Algebra.mem_bot] at h
  have hval : a.val.val = algebraMap F (AdeleRing (𝓞 F) F) x.val := congrArg Units.val ha
  have hinv : a.inv.val = algebraMap F (AdeleRing (𝓞 F) F) x.inv := congrArg Units.inv ha
  obtain ⟨y, hy⟩ := lift x.val (hval ▸ a.val.property)
  obtain ⟨z, hz⟩ := lift x.inv (hinv ▸ a.inv.property)
  let u : (𝓞 F)ˣ := ⟨y, z,
    (IsFractionRing.injective (𝓞 F) F) (by rw [map_mul, hy, hz, x.val_inv, map_one]),
    (IsFractionRing.injective (𝓞 F) F) (by rw [map_mul, hy, hz, x.inv_val, map_one])⟩
  exact ⟨u, Units.ext hy⟩

/-- The principal idele of a global unit is a unit at every finite place, and its
archimedean components have the absolute values of the unit. -/
private theorem multiplicativeTamagawaMeasure_regulatorStrip_unit_spec (u : (𝓞 F)ˣ) :
    (∀ v : Primes(F), (finiteUnitAt) v (IdeleGroup.unitEmbedding (𝓞 F) F
      (Units.map (algebraMap (𝓞 F) F).toMonoidHom u)) ∈ (v.adicCompletionIntegers F).units) ∧
    ∀ w : InfinitePlace F, ‖(IdeleGroup.unitEmbedding (𝓞 F) F
      (Units.map (algebraMap (𝓞 F) F).toMonoidHom u)).val.1 w‖ = w (algebraMap (𝓞 F) F u) := by
  constructor
  · apply (multiplicativeTamagawaMeasure_regulatorStrip_mem_integral F _).mp
    have hInt (y : F) :
        algebraMap F (AdeleRing (𝓞 F) F) y ∈ integralAdelesOutside F ∅ ↔
          y ∈ (algebraMap (𝓞 F) F).range := by
      rw [diagonal_mem_integralAdelesOutside, Finset.coe_empty, integer_empty, Algebra.mem_bot]
      rfl
    let f := ((algebraMap F (AdeleRing (𝓞 F) F)).comp (algebraMap (𝓞 F) F)).codRestrict
      (integralAdelesOutside F ∅) (fun y ↦ (hInt _).mpr ⟨y, rfl⟩)
    exact ⟨Units.map f.toMonoidHom u, Units.ext rfl⟩
  · intro w
    change ‖algebraMap F (InfiniteAdeleRing F) (algebraMap (𝓞 F) F u.val) w‖ = _
    rw [InfiniteAdeleRing.algebraMap_apply, AbsoluteValue.Completion.norm_coe]
    rfl

/-- Multiplying an idele by a principal idele adds the weighted archimedean logarithms. -/
private theorem multiplicativeTamagawaMeasure_regulatorStrip_log_mul (a b : 𝕀[F])
    (w : InfinitePlace F) :
    (w.mult : ℝ) * Real.log ‖(a * b).val.1 w‖ =
      (w.mult : ℝ) * Real.log ‖a.val.1 w‖ + (w.mult : ℝ) * Real.log ‖b.val.1 w‖ := by
  have hne (g : 𝕀[F]) : ‖g.val.1 w‖ ≠ 0 := norm_ne_zero_iff.mpr ((∞unitAt) w g).ne_zero
  rw [← mul_add, ← Real.log_mul (hne a) (hne b), ← norm_mul]
  rfl

/-- A point of the regulator strip with integral finite components stays there under a
principal idele exactly when that idele comes from a torsion unit. -/
private theorem multiplicativeTamagawaMeasure_regulatorStrip_translate (h : 𝕀[F])
    (hh : (fun w ↦ (∞unitAt) w h) ∈ archimedeanRegulatorStrip F ∧
      ∀ v : Primes(F), (finiteUnitAt) v h ∈ (v.adicCompletionIntegers F).units) (z : Fˣ) :
    ((fun w ↦ (∞unitAt) w (h * IdeleGroup.unitEmbedding (𝓞 F) F z)) ∈
        archimedeanRegulatorStrip F ∧ ∀ v : Primes(F),
        (finiteUnitAt) v (h * IdeleGroup.unitEmbedding (𝓞 F) F z) ∈
          (v.adicCompletionIntegers F).units) ↔
      ∃ ζ ∈ Units.torsion F, Units.map (algebraMap (𝓞 F) F).toMonoidHom ζ = z := by
  let d := IdeleGroup.unitEmbedding (𝓞 F) F
  let ι := Units.map (algebraMap (𝓞 F) F).toMonoidHom
  have hlog (u : (𝓞 F)ˣ) (w : InfinitePlace F) :
      (w.mult : ℝ) * Real.log ‖(h * d (ι u)).val.1 w‖ =
        (w.mult : ℝ) * Real.log ‖h.val.1 w‖ + (w.mult : ℝ) * Real.log (w (algebraMap (𝓞 F) F u)) := by
    rw [multiplicativeTamagawaMeasure_regulatorStrip_log_mul,
      (multiplicativeTamagawaMeasure_regulatorStrip_unit_spec F u).2 w]
  constructor
  · rintro ⟨⟨-, hpar⟩, hfin⟩
    have hz : ∀ v : Primes(F), (finiteUnitAt) v (d z) ∈ (v.adicCompletionIntegers F).units := by
      intro v
      have h1 := (v.adicCompletionIntegers F).units.mul_mem
        ((v.adicCompletionIntegers F).units.inv_mem (hh.2 v)) (hfin v)
      rwa [← map_inv, ← map_mul, inv_mul_cancel_left] at h1
    obtain ⟨u, rfl⟩ := multiplicativeTamagawaMeasure_regulatorStrip_unit F z hz
    refine ⟨u, ?_, rfl⟩
    rw [← Units.dirichletUnitTheorem.logEmbedding_eq_zero_iff]
    by_contra hne
    let x : (Units.logEmbedding F).range := ⟨_, Additive.ofMul u, rfl⟩
    have hx : x ≠ 0 := fun h0 ↦ hne (congrArg Subtype.val h0)
    refine Set.disjoint_left.mp
      (regulatorParallelotope_disjoint F (Units.basisModTorsion F) x hx) ?_ hpar
    refine Set.mem_vadd_set.mpr ⟨_, hh.1.2, ?_⟩
    funext w
    change Units.logEmbedding F (Additive.ofMul u) w + (w.val.mult : ℝ) * Real.log ‖h.val.1 w.val‖ = _
    rw [Units.dirichletUnitTheorem.logEmbedding_component]
    exact (add_comm _ _).trans (hlog u w.val).symm
  · rintro ⟨ζ, hζ, rfl⟩
    have hw (w : InfinitePlace F) := (Units.mem_torsion F).mp hζ w
    have hlog' (w : InfinitePlace F) :
        (w.mult : ℝ) * Real.log ‖(h * d (ι ζ)).val.1 w‖ = (w.mult : ℝ) * Real.log ‖h.val.1 w‖ := by
      rw [hlog ζ w]
      erw [hw w]
      rw [Real.log_one, mul_zero, add_zero]
    refine ⟨?_, fun v ↦ ?_⟩
    · change (∑ w, (w.mult : ℝ) * Real.log ‖(h * d (ι ζ)).val.1 w‖) ∈ Icc 0 1 ∧
        (fun w : {w : InfinitePlace F // w ≠ Units.dirichletUnitTheorem.w₀} ↦
          (w.val.mult : ℝ) * Real.log ‖(h * d (ι ζ)).val.1 w.val‖) ∈
          regulatorParallelotope F (Units.basisModTorsion F)
      simp only [hlog']
      exact hh.1
    · rw [map_mul]
      exact (v.adicCompletionIntegers F).units.mul_mem (hh.2 v)
        ((multiplicativeTamagawaMeasure_regulatorStrip_unit_spec F ζ).1 v)

/-- The class of an idele has a principal translate in the regulator strip with integral
finite components exactly when it lies over the integral units and has norm in `[1, e]`. -/
private theorem multiplicativeTamagawaMeasure_regulatorStrip_exists (g : 𝕀[F]) :
    (∃ x : Fˣ, (fun w ↦ (∞unitAt) w (g * IdeleGroup.unitEmbedding (𝓞 F) F x)) ∈
        archimedeanRegulatorStrip F ∧ ∀ v : Primes(F),
        (finiteUnitAt) v (g * IdeleGroup.unitEmbedding (𝓞 F) F x) ∈
          (v.adicCompletionIntegers F).units) ↔
      QuotientGroup.mk' P[F] g ∈
          (Units.map (integralAdelesOutside F ∅).subtype.toMonoidHom).range.map
            (QuotientGroup.mk' P[F]) ∧
        ((ideleClassNorm F (QuotientGroup.mk' P[F] g) : ℝ≥0) : ℝ) ∈ Icc 1 (Real.exp 1) := by
  let d := IdeleGroup.unitEmbedding (𝓞 F) F
  let ι := Units.map (algebraMap (𝓞 F) F).toMonoidHom
  let q := QuotientGroup.mk' P[F]
  have hnorm (x : Fˣ) : ideleNorm F (g * d x) = ideleNorm F g := by
    rw [map_mul, MonoidHom.mem_ker.mp ((ideleNorm_spec F).2 ⟨x, rfl⟩), mul_one]
  have hq (x : Fˣ) : q (g * d x) = q g := by
    rw [map_mul, show q (d x) = 1 from (QuotientGroup.eq_one_iff (N := P[F]) (d x)).mpr ⟨x, rfl⟩,
      mul_one]
  have hcl : ideleClassNorm F (q g) = ideleNorm F g := rfl
  have hpos : 0 < ((ideleNorm F g : ℝ≥0) : ℝ) :=
    NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (ideleNorm F g).ne_zero)
  have hIcc : ((ideleNorm F g : ℝ≥0) : ℝ) ∈ Icc 1 (Real.exp 1) ↔
      Real.log ((ideleNorm F g : ℝ≥0) : ℝ) ∈ Icc 0 1 := by
    rw [mem_Icc, mem_Icc, Real.log_nonneg_iff hpos, Real.log_le_iff_le_exp hpos]
  rw [hcl, hIcc]
  constructor
  · rintro ⟨x, ⟨⟨hsum, -⟩, hfin⟩⟩
    refine ⟨⟨g * d x, (multiplicativeTamagawaMeasure_regulatorStrip_mem_integral F _).mpr hfin,
      hq x⟩, ?_⟩
    rw [← hnorm x, multiplicativeTamagawaMeasure_regulatorStrip_log_norm F _ hfin]
    exact hsum
  · rintro ⟨⟨u, hu, hqu⟩, hlogn⟩
    obtain ⟨y, hy⟩ := ((ideleClassGroup_description F).2 u g).mp hqu
    have hgy : g * d y = u := by
      rw [hy, mul_comm]
    let h := g * d y
    have hh : ∀ v : Primes(F), (finiteUnitAt) v h ∈ (v.adicCompletionIntegers F).units :=
      (multiplicativeTamagawaMeasure_regulatorStrip_mem_integral F h).mp
        (by rw [show h = u from hgy]; exact hu)
    have hcover : (fun w : {w : InfinitePlace F // w ≠ Units.dirichletUnitTheorem.w₀} ↦
        (w.val.mult : ℝ) * Real.log ‖h.val.1 w.val‖) ∈
        ⋃ x : (Units.logEmbedding F).range,
          x.val +ᵥ regulatorParallelotope F (Units.basisModTorsion F) := by
      rw [regulatorParallelotope_cover F (Units.basisModTorsion F)]
      exact Set.mem_univ _
    obtain ⟨lam, hmem⟩ := Set.mem_iUnion.mp hcover
    obtain ⟨p, hp, hyp⟩ := Set.mem_vadd_set.mp hmem
    obtain ⟨a, ha⟩ := AddMonoidHom.mem_range.mp lam.property
    let u' : (𝓞 F)ˣ := Additive.toMul a
    refine ⟨y * ι u'⁻¹, ?_⟩
    have hx : g * d (y * ι u'⁻¹) = h * d (ι u'⁻¹) := by
      rw [map_mul, ← mul_assoc]
    rw [hx]
    have hfin' := (multiplicativeTamagawaMeasure_regulatorStrip_unit_spec F u'⁻¹).1
    have hall : ∀ v : Primes(F), (finiteUnitAt) v (h * d (ι u'⁻¹)) ∈
        (v.adicCompletionIntegers F).units := by
      intro v
      beta_reduce
      rw [map_mul]
      exact (v.adicCompletionIntegers F).units.mul_mem (hh v) (hfin' v)
    have hlog (w : InfinitePlace F) :
        (w.mult : ℝ) * Real.log ‖(h * d (ι u'⁻¹)).val.1 w‖ =
          (w.mult : ℝ) * Real.log ‖h.val.1 w‖ +
            (w.mult : ℝ) * Real.log (w (algebraMap (𝓞 F) F ↑u'⁻¹)) := by
      rw [multiplicativeTamagawaMeasure_regulatorStrip_log_mul,
        (multiplicativeTamagawaMeasure_regulatorStrip_unit_spec F u'⁻¹).2 w]
    refine ⟨⟨?_, ?_⟩, hall⟩
    · change (∑ w, (w.mult : ℝ) * Real.log ‖(h * d (ι u'⁻¹)).val.1 w‖) ∈ Icc 0 1
      rw [← multiplicativeTamagawaMeasure_regulatorStrip_log_norm F _ hall, ← hx, hnorm]
      exact hlogn
    · change (fun w : {w : InfinitePlace F // w ≠ Units.dirichletUnitTheorem.w₀} ↦
        (w.val.mult : ℝ) * Real.log ‖(h * d (ι u'⁻¹)).val.1 w.val‖) ∈ _
      convert hp using 1
      funext w
      rw [hlog w.val]
      have h1 := congrFun hyp w
      have h2 : Units.logEmbedding F (Additive.ofMul u'⁻¹) w = -lam.val w := by
        rw [ofMul_inv, map_neg, Pi.neg_apply]
        exact congrArg (fun f : Units.dirichletUnitTheorem.logSpace F ↦ -f w) ha
      rw [Units.dirichletUnitTheorem.logEmbedding_component] at h2
      change lam.val w + p w = (w.val.mult : ℝ) * Real.log ‖h.val.1 w.val‖ at h1
      rw [h2, ← h1]
      ring

/-- The principal ideles moving a fixed idele into the regulator strip with integral finite
components are either none or one coset of the torsion units. -/
private theorem multiplicativeTamagawaMeasure_regulatorStrip_fiber (g : 𝕀[F]) :
    (Measure.count : Measure P[F]) {k : P[F] | g * (k : 𝕀[F]) ∈
        {h : 𝕀[F] | (fun w ↦ (∞unitAt) w h) ∈ archimedeanRegulatorStrip F ∧
          ∀ v : Primes(F), (finiteUnitAt) v h ∈ (v.adicCompletionIntegers F).units}} =
      (Units.torsionOrder F : ℝ≥0∞) *
        {c : C[F] | c ∈ (Units.map (integralAdelesOutside F ∅).subtype.toMonoidHom).range.map
            (QuotientGroup.mk' P[F]) ∧
          ((ideleClassNorm F c : ℝ≥0) : ℝ) ∈ Icc 1 (Real.exp 1)}.indicator 1
          (QuotientGroup.mk' P[F] g) := by
  let d := IdeleGroup.unitEmbedding (𝓞 F) F
  let ι := Units.map (algebraMap (𝓞 F) F).toMonoidHom
  let : BorelSpace 𝕀[F] := ⟨rfl⟩
  let : T2Space 𝕀[F] := (ideleGroup_topology F).1
  by_cases hW : QuotientGroup.mk' P[F] g ∈
      {c : C[F] | c ∈ (Units.map (integralAdelesOutside F ∅).subtype.toMonoidHom).range.map
          (QuotientGroup.mk' P[F]) ∧
        ((ideleClassNorm F c : ℝ≥0) : ℝ) ∈ Icc 1 (Real.exp 1)}
  · rw [indicator_of_mem hW, Pi.one_apply, mul_one]
    obtain ⟨x₀, hx₀⟩ := (multiplicativeTamagawaMeasure_regulatorStrip_exists F g).mpr hW
    let φ : Units.torsion F → P[F] := fun ζ ↦ ⟨d (x₀ * ι ζ), x₀ * ι ζ, rfl⟩
    have hφ : Injective φ := by
      intro a b hab
      have h1 : d (x₀ * ι a) = d (x₀ * ι b) := congrArg Subtype.val hab
      have h2 := mul_left_cancel ((ideleGroup_quotient.{_, 0} F).1 h1)
      exact Subtype.ext (Units.map_injective (IsFractionRing.injective (𝓞 F) F) h2)
    have hset : {k : P[F] | g * (k : 𝕀[F]) ∈
        {h : 𝕀[F] | (fun w ↦ (∞unitAt) w h) ∈ archimedeanRegulatorStrip F ∧
          ∀ v : Primes(F), (finiteUnitAt) v h ∈ (v.adicCompletionIntegers F).units}} =
        range φ := by
      ext ⟨_, y, rfl⟩
      have hy : g * d y = (g * d x₀) * d (x₀⁻¹ * y) := by
        rw [map_mul, map_inv, mul_assoc, mul_inv_cancel_left]
      change ((fun w ↦ (∞unitAt) w (g * d y)) ∈ archimedeanRegulatorStrip F ∧
          ∀ v : Primes(F), (finiteUnitAt) v (g * d y) ∈ (v.adicCompletionIntegers F).units) ↔ _
      rw [hy, multiplicativeTamagawaMeasure_regulatorStrip_translate F _ hx₀]
      constructor
      · rintro ⟨ζ, hζ, hζy⟩
        refine ⟨⟨ζ, hζ⟩, Subtype.ext ?_⟩
        change d (x₀ * ι ζ) = d y
        rw [show ι ζ = x₀⁻¹ * y from hζy, mul_inv_cancel_left]
      · rintro ⟨⟨ζ, hζ⟩, hζy⟩
        have h1 : d (x₀ * ι ζ) = d y := congrArg Subtype.val hζy
        refine ⟨ζ, hζ, ?_⟩
        rw [← (ideleGroup_quotient.{_, 0} F).1 h1, inv_mul_cancel_left]
    rw [hset, Measure.count_apply (Set.finite_range φ).measurableSet, hφ.encard_range,
      ENat.card_eq_coe_natCard]
    rfl
  · rw [indicator_of_notMem hW, mul_zero, Measure.count_eq_zero_iff]
    apply eq_empty_iff_forall_notMem.mpr
    rintro ⟨_, y, rfl⟩ hy
    exact hW ((multiplicativeTamagawaMeasure_regulatorStrip_exists F g).mp ⟨y, hy⟩)

/-- The canonical section of the idelic norm is a unit at every finite place. -/
private theorem multiplicativeTamagawaMeasure_regulatorStrip_section (t : ℝ≥0ˣ) :
    canonicalIdeleNormSection F t ∈ (Units.map (integralAdelesOutside F ∅).subtype.toMonoidHom).range := by
  apply (multiplicativeTamagawaMeasure_regulatorStrip_mem_integral F _).mpr
  intro v
  have h1 : (finiteUnitAt) v (canonicalIdeleNormSection F t) = 1 := by
    apply Units.ext
    change (canonicalIdeleNormSection F t).val.2 v = 1
    rw [canonicalIdeleNormSection_finite]
    rfl
  rw [h1]
  exact one_mem _

/-- The norm-one idele classes over the integral idele units have index the class number. -/
private theorem multiplicativeTamagawaMeasure_regulatorStrip_index :
    (((Units.map (integralAdelesOutside F ∅).subtype.toMonoidHom).range.map
      (QuotientGroup.mk' P[F])).comap C₁[F].subtype).index = NumberField.classNumber F := by
  let : TopologicalSpace (CommRing.Pic (𝓞 F)) := ⊥
  obtain ⟨p, -, -, hexact, hpq⟩ := idele_ideal_class_exact F
  let U := (Units.map (integralAdelesOutside F ∅).subtype.toMonoidHom).range
  let q := QuotientGroup.mk' P[F]
  have hker (g : 𝕀[F]) : p g = 1 ↔ q g ∈ U.map q := by
    rw [hexact g, ← Subgroup.mem_comap, Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_comm]
    exact ⟨fun ⟨h, hh⟩ ↦ hh ▸ h.property, fun h ↦ ⟨⟨g, h⟩, rfl⟩⟩
  have hP : P[F] ≤ p.ker := fun g hg ↦ (hker g).mpr ⟨1, U.one_mem, by
    rw [map_one]
    exact ((QuotientGroup.eq_one_iff g).mpr hg).symm⟩
  let ψ := (QuotientGroup.lift P[F] p hP).comp C₁[F].subtype
  have hψ : (U.map q).comap C₁[F].subtype = ψ.ker := by
    ext ⟨c, hc⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective P[F] c
    exact (hker g).symm
  have hsurj : Surjective ψ := by
    intro π
    obtain ⟨g, rfl⟩ := hpq.surjective π
    let s := canonicalIdeleNormSection F
    let g' := g * (s (ideleNorm F g))⁻¹
    have hs : p (s (ideleNorm F g)) = 1 :=
      (hker _).mpr ⟨_, multiplicativeTamagawaMeasure_regulatorStrip_section F _, rfl⟩
    have hg' : q g' ∈ C₁[F] := by
      change ideleNorm F g' = 1
      rw [map_mul, map_inv, canonicalIdeleNormSection_rightInverse F, mul_inv_cancel]
    refine ⟨⟨q g', hg'⟩, ?_⟩
    change p g' = p g
    rw [map_mul, map_inv, hs, inv_one, mul_one]
  rw [hψ, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top,
    NumberField.classNumber, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (ClassGroup.equivPic (𝓞 F)).toEquiv.symm

/-- The ideles are second countable, since the adeles are. -/
private theorem multiplicativeTamagawaMeasure_regulatorStrip_secondCountable :
    SecondCountableTopology 𝕀[F] := by
  let := ratAdele_secondCountable
  obtain ⟨u, _, _⟩ := exists_adeleTrace_dualCoordinates F
  let : SecondCountableTopology 𝔸[F] := u.symm.toHomeomorph.isEmbedding.secondCountableTopology
  let : SecondCountableTopology 𝔸[F]ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

/-- The global idelic mass of the regulator strip with integral finite components.
The strip lies over the principal ideal class and contains all torsion sectors.
Under the two quotient normalizations its mass is the prescribed norm-one class
volume times the torsion order divided by the class number. -/
theorem multiplicativeTamagawaMeasure_regulatorStrip :
    multiplicativeTamagawaMeasure F
      {g | (fun w ↦ (∞unitAt) w g) ∈ archimedeanRegulatorStrip F ∧
        ∀ v : Primes(F), (finiteUnitAt) v g ∈ (v.adicCompletionIntegers F).units} =
      archRegulatorMass(F) * ∏ᶠ v : Primes(F), differentMass(F, v) := by
  let G := 𝕀[F]
  let P := P[F]
  let C := C[F]
  let K := C₁[F]
  let q := QuotientGroup.mk' P
  let U := (Units.map (integralAdelesOutside F ∅).subtype.toMonoidHom).range
  let Ubar := U.map q
  let V := Ubar.comap K.subtype
  let s := canonicalIdeleNormSection F
  let E := {g : G | (fun w ↦ (∞unitAt) w g) ∈ archimedeanRegulatorStrip F ∧
    ∀ v : Primes(F), (finiteUnitAt) v g ∈ (v.adicCompletionIntegers F).units}
  let W := {c : C | c ∈ Ubar ∧ ((ideleClassNorm F c : ℝ≥0) : ℝ) ∈ Icc 1 (Real.exp 1)}
  let I := {t : ℝ≥0ˣ | (t.val : ℝ) ∈ Icc 1 (Real.exp 1)}
  obtain ⟨h₂, hlc, _, _, -, -⟩ := ideleGroup_topology F
  obtain ⟨-, hP, hPd, -, hq, hC₂, hClc, -, hcn, -, ⟨sc, hsc, hrc⟩, -⟩ :=
    ideleGroup_quotient.{_, 0} F
  obtain ⟨hK, hKc, hK₂, -⟩ := ideleClassGroup_finiteness F
  let : BorelSpace G := ⟨rfl⟩
  let : BorelSpace C := ⟨rfl⟩
  let : BorelSpace (C ⧸ K) := ⟨rfl⟩
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ _
  let : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let := multiplicativeTamagawaMeasure_regulatorStrip_secondCountable F
  let : SecondCountableTopology C := inferInstanceAs (SecondCountableTopology (G ⧸ P))
  let : DiscreteTopology P := isDiscrete_iff_discreteTopology.mp hPd
  let : (Measure.count : Measure P).IsHaarMeasure :=
    { lt_top_of_isCompact := fun _ h ↦ Measure.count_apply_lt_top.mpr h.finite_of_discrete
      open_pos := fun _ _ h ↦ Measure.count_ne_zero h }
  let : LocallyCompactSpace P := hP.locallyCompactSpace
  let : (Measure.count : Measure P).Regular := inferInstance
  let : CompactSpace K := hKc
  let μ := multiplicativeTamagawaMeasure F
  let η := ideleClassTamagawaMeasure F
  let ν := normOneIdeleClassTamagawaMeasure F
  obtain ⟨hm, hmreg, hw, hv, hvreg, hvol, hcweil⟩ :=
    (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec
  let : μ.IsHaarMeasure := hm
  let : μ.Regular := hmreg
  let : η.IsHaarMeasure := hw.1
  let : η.Regular := hw.2.1
  let : ν.IsHaarMeasure := hv
  let : ν.Regular := hvreg
  -- Measurability of the sets involved.
  have hUo : IsOpen (U : Set G) := (isOpenEmbedding_integralAdeleUnits F ∅).isOpen_range
  have hUbaro : IsOpen (Ubar : Set C) := by
    rw [Subgroup.coe_map]
    exact hq.isOpenMap _ hUo
  have hnormc : Continuous (fun c : C ↦ ((ideleClassNorm F c : ℝ≥0) : ℝ)) :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp hcn)
  have hWm : MeasurableSet W :=
    hUbaro.measurableSet.inter (measurableSet_Icc.preimage hnormc.measurable)
  have hEm : MeasurableSet E := by
    let (w : InfinitePlace F) : BorelSpace w.Completion := ⟨rfl⟩
    let (w : InfinitePlace F) : BorelSpace w.Completionˣ := borelSpace_units_of_continuousInv₀ _
    let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
      (isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
    let (w : InfinitePlace F) : SecondCountableTopology w.Completionˣ :=
      Units.isEmbedding_val₀.secondCountableTopology
    have hcont : Continuous (fun g : G ↦ fun w ↦ (∞unitAt) w g) :=
      continuous_pi fun w ↦ ((continuous_apply w).comp continuous_fst).units_map _
    have hE : E = (fun g : G ↦ fun w ↦ (∞unitAt) w g) ⁻¹' archimedeanRegulatorStrip F ∩ U := by
      ext g
      exact and_congr Iff.rfl (multiplicativeTamagawaMeasure_regulatorStrip_mem_integral F g).symm
    rw [hE]
    exact ((archimedeanRegulatorStrip_measurableSet F).preimage hcont.measurable).inter
      hUo.measurableSet
  -- Weil's formula for the principal ideles counts the torsion sectors.
  have hμE : μ E = (Units.torsionOrder F : ℝ≥0∞) * η W := by
    obtain ⟨hκ, hμ⟩ := weilMeasure_eq_bind P hP μ Measure.count η hw
    rw [← hμ, Measure.bind_apply hEm hκ.aemeasurable, ← lintegral_indicator_one hWm,
      ← lintegral_const_mul _ (measurable_one.indicator hWm)]
    apply lintegral_congr
    intro c
    have ht : Measurable (fun h : P ↦ c.out * (h : G)) :=
      (continuous_const.mul continuous_subtype_val).measurable
    rw [Measure.map_apply ht hEm]
    have hc : q c.out = c := QuotientGroup.out_eq' c
    have := multiplicativeTamagawaMeasure_regulatorStrip_fiber F c.out
    rw [hc] at this
    exact this
  -- Weil's formula for the norm-one classes and `dt/t` reduces to the integral units.
  have hηW : η W = ν V := by
    obtain ⟨hκ, hη⟩ := weilMeasure_eq_bind K hK η ν
      (positiveRealHaar.comap (QuotientGroup.kerLift (ideleClassNorm F))) hcweil
    let L := QuotientGroup.kerLift (ideleClassNorm F)
    let e₀ := QuotientGroup.quotientKerEquivOfRightInverse (ideleClassNorm F) sc hrc
    let e : (C ⧸ K) ≃ₜ* ℝ≥0ˣ :=
      { e₀ with
        continuous_toFun := (QuotientGroup.isQuotientMap_mk K).continuous_iff.mpr hcn
        continuous_invFun := QuotientGroup.continuous_mk.comp hsc }
    have hemb : MeasurableEmbedding L := e.toHomeomorph.measurableEmbedding
    have hLs : Surjective L := e.surjective
    have hIm : MeasurableSet I :=
      measurableSet_Icc.preimage (NNReal.continuous_coe.comp Units.continuous_val).measurable
    have hsU (t : ℝ≥0ˣ) : q (s t) ∈ Ubar :=
      ⟨s t, multiplicativeTamagawaMeasure_regulatorStrip_section F t, rfl⟩
    have hpt (c : C ⧸ K) :
        (ν.map (fun h : K ↦ c.out * (h : C))) W = (L ⁻¹' I).indicator (fun _ ↦ ν V) c := by
      let x := c.out
      have hm : Measurable (fun h : K ↦ x * (h : C)) :=
        (continuous_const.mul continuous_subtype_val).measurable
      rw [Measure.map_apply hm hWm]
      have hLc : L c = ideleClassNorm F x := by
        rw [← QuotientGroup.out_eq' c]
        rfl
      have hnx (h : K) : ideleClassNorm F (x * h) = ideleClassNorm F x := by
        rw [map_mul, MonoidHom.mem_ker.mp h.property, mul_one]
      by_cases hI : L c ∈ I
      · rw [indicator_of_mem (show c ∈ L ⁻¹' I from hI)]
        let n := ideleClassNorm F x
        have hsn : ideleClassNorm F (q (s n)) = n := canonicalIdeleNormSection_rightInverse F n
        let y : K := ⟨(q (s n))⁻¹ * x, by
          change ideleClassNorm F ((q (s n))⁻¹ * x) = 1
          rw [map_mul, map_inv, hsn, inv_mul_cancel]⟩
        have hpre : (fun h : K ↦ x * (h : C)) ⁻¹' W = (fun h : K ↦ y * h) ⁻¹' V := by
          ext h
          change (x * h ∈ Ubar ∧ ((ideleClassNorm F (x * h) : ℝ≥0) : ℝ) ∈ Icc 1 (Real.exp 1)) ↔
            (q (s n))⁻¹ * x * h ∈ Ubar
          rw [hnx, mul_assoc, Subgroup.mul_mem_cancel_left _ (Ubar.inv_mem (hsU n))]
          rw [hLc] at hI
          exact and_iff_left hI
        rw [hpre, measure_preimage_mul]
      · rw [indicator_of_notMem (show c ∉ L ⁻¹' I from hI)]
        have hpre : (fun h : K ↦ x * (h : C)) ⁻¹' W = ∅ := by
          ext h
          simp only [mem_preimage, mem_empty_iff_false, iff_false]
          rintro ⟨-, hh⟩
          rw [hnx, ← hLc] at hh
          exact hI hh
        rw [hpre, measure_empty]
    rw [← hη, Measure.bind_apply hWm hκ.aemeasurable]
    simp_rw [hpt]
    rw [lintegral_indicator_const (hemb.measurable hIm), hemb.comap_apply,
      image_preimage_eq _ hLs]
    let T : ℝ≥0ˣ := Units.mk0 (Real.exp 1).toNNReal
      (Real.toNNReal_pos.mpr (Real.exp_pos 1)).ne'
    have hT : ((T.val : ℝ≥0) : ℝ) = Real.exp 1 := Real.coe_toNNReal _ (Real.exp_pos 1).le
    have hTI := positiveRealHaar_interval T (hT ▸ Real.one_le_exp zero_le_one)
    rw [hT, Real.log_exp, ENNReal.ofReal_one] at hTI
    change ν V * positiveRealHaar {t : ℝ≥0ˣ | (t.val : ℝ) ∈ Icc 1 (Real.exp 1)} = ν V
    rw [hTI, mul_one]
  -- The integral classes have index the class number in the norm-one classes.
  have hVm : MeasurableSet (V : Set K) := (hUbaro.preimage continuous_subtype_val).measurableSet
  have hidx := multiplicativeTamagawaMeasure_regulatorStrip_index F
  have : V.FiniteIndex := ⟨by
    change (Ubar.comap K.subtype).index ≠ 0
    rw [hidx]
    exact (NumberField.classNumber_pos F).ne'⟩
  have hνV := Subgroup.index_mul_measure V hVm ν
  change ((Ubar.comap K.subtype).index : ℝ≥0∞) * ν V = ν univ at hνV
  rw [hidx, show ν univ = _ from normOneIdeleClassTamagawaMeasure_volume F] at hνV
  -- Collect the constants.
  have hh := NumberField.classNumber_pos F
  have hR := NumberField.Units.regulator_pos F
  have hw := NumberField.Units.torsionOrder_pos F
  have hD : 0 < Real.sqrt ((Int.natAbs (NumberField.discr F) : ℕ) : ℝ) :=
    Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Int.natAbs_pos.mpr (NumberField.discr_ne_zero F)))
  have hνV' : ν V = ENNReal.ofReal ((2 : ℝ) ^ InfinitePlace.nrRealPlaces F *
      (2 * Real.pi) ^ InfinitePlace.nrComplexPlaces F * Units.regulator F /
        (Real.sqrt ((Int.natAbs (NumberField.discr F) : ℕ) : ℝ) * (Units.torsionOrder F : ℝ))) := by
    apply (ENNReal.mul_right_inj (Nat.cast_ne_zero.mpr hh.ne') (ENNReal.natCast_ne_top _)).mp
    rw [hνV, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    congr 1
    ring
  change μ E = _
  rw [hμE, hηW, hνV', finiteLocalTamagawaMass_finprod, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_inv_of_pos hD,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

/-- Paper: Lemma A.3.2.4, p. 560. The global multiplicative measure is the
restricted product of the local measures, evaluated on rectangles with integer-unit tails. -/
theorem multiplicativeTamagawaMeasure_restrictedProduct
    (B : (w : InfinitePlace F) → Set w.Completionˣ) (hB : ∀ w, MeasurableSet (B w))
    (U : (v : S) → Set (v.val.adicCompletion F)ˣ) (hU : ∀ v, MeasurableSet (U v)) :
    multiplicativeTamagawaMeasure F
        {g | (∀ w, (∞unitAt) w g ∈ B w) ∧ (∀ v : S, (finiteUnitAt) v.val g ∈ U v) ∧
          ∀ v : Primes(F), v ∉ S → (finiteUnitAt) v g ∈ (v.adicCompletionIntegers F).units} =
      (∏ w : InfinitePlace F, infiniteLocalMultiplicativeTamagawaMeasure F w (B w)) *
        (∏ v : S, finiteLocalMultiplicativeTamagawaMeasure F v.val (U v)) *
          ∏ᶠ v : {v : Primes(F) // v ∉ S}, differentMass(F, v.val) := by
  let (w : InfinitePlace F) : BorelSpace w.Completion := ⟨rfl⟩
  let (w : InfinitePlace F) : BorelSpace w.Completionˣ := borelSpace_units_of_continuousInv₀ _
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let (w : InfinitePlace F) : SecondCountableTopology w.Completionˣ :=
    Units.isEmbedding_val₀.secondCountableTopology
  let (v : Primes(F)) : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
  let (v : Primes(F)) : SecondCountableTopology (v.adicCompletion F)ˣ :=
    Units.isEmbedding_val₀.secondCountableTopology
  let : LocallyCompactSpace (IdeleCoordinates F S) := by
    change LocallyCompactSpace
      (((w : InfinitePlace F) → w.Completionˣ) × ((v : S) → (v.val.adicCompletion F)ˣ))
    infer_instance
  let : SecondCountableTopology (IdeleCoordinates F S) := by
    change SecondCountableTopology
      (((w : InfinitePlace F) → w.Completionˣ) × ((v : S) → (v.val.adicCompletion F)ˣ))
    infer_instance
  let : BorelSpace (IdeleCoordinates F S) := inferInstance
  let μarch := Measure.pi (infiniteLocalMultiplicativeTamagawaMeasure F)
  let μf (v : S) := finiteLocalMultiplicativeTamagawaMeasure F v.val
  let (w : InfinitePlace F) : (infiniteLocalMultiplicativeTamagawaMeasure F w).IsHaarMeasure :=
    infiniteLocalMultiplicativeTamagawaMeasure_haar F w
  let (v : S) : (μf v).IsHaarMeasure := finiteLocalMultiplicativeTamagawaMeasure_haar F v.val
  let : μarch.IsHaarMeasure := Measure.pi.isHaarMeasure _
  let : (Measure.pi μf).IsHaarMeasure := Measure.pi.isHaarMeasure _
  let μ : Measure (IdeleCoordinates F S) := μarch.prod (Measure.pi μf)
  let : μ.IsHaarMeasure := Measure.prod.instIsHaarMeasure _ _
  obtain ⟨ν, hν, hνapply⟩ := multiplicativeTamagawaMeasure_projected_haar F S
  let : ν.IsHaarMeasure := hν
  let c := ν.haarScalarFactor μ
  have hc : ν = c • μ := Measure.isMulLeftInvariant_eq_smul ν μ
  let A := archimedeanRegulatorStrip F
  let O (v : S) := ((v.val.adicCompletionIntegers F).units : Set (v.val.adicCompletion F)ˣ)
  let W : Set (IdeleCoordinates F S) := A ×ˢ Set.univ.pi O
  have hW : MeasurableSet W := (archimedeanRegulatorStrip_measurableSet F).prod
    (MeasurableSet.univ_pi fun _ ↦ Submonoid.isOpen_units (Valued.isOpen_valuationSubring _) |>.measurableSet)
  have hset : {g : 𝕀[F] |
        ((fun w ↦ (∞unitAt) w g), (fun v : S ↦ (finiteUnitAt) v.val g)) ∈ W ∧
        ∀ v : Primes(F), v ∉ S → (finiteUnitAt) v g ∈ (v.adicCompletionIntegers F).units} =
        {g | (fun w ↦ (∞unitAt) w g) ∈ archimedeanRegulatorStrip F ∧
          ∀ v : Primes(F), (finiteUnitAt) v g ∈ (v.adicCompletionIntegers F).units} := by
    ext g
    simp only [W, O, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ_pi]
    constructor
    · rintro ⟨⟨ha, hin⟩, hout⟩
      refine ⟨ha, fun v ↦ ?_⟩
      by_cases hv : v ∈ S
      · exact hin ⟨v, hv⟩
      · exact hout v hv
    · rintro ⟨ha, hall⟩
      exact ⟨⟨ha, fun v ↦ hall v.val⟩, fun v _ ↦ hall v⟩
  let tail := ∏ᶠ v : {v : Primes(F) // v ∉ S}, differentMass(F, v.val)
  let selected := ∏ v : S, differentMass(F, v.val)
  have hsplit : selected * tail = ∏ᶠ v : Primes(F), differentMass(F, v) := by
    rw [show selected = _ from (Finset.prod_subtype S (fun _ ↦ Iff.rfl)
      (fun v ↦ differentMass(F, v))).symm, ← finprod_mem_coe_finset,
      show tail = ∏ᶠ v ∈ (S : Set (Primes(F)))ᶜ, differentMass(F, v) from
        finprod_set_coe_eq_finprod_mem (f := fun v ↦ differentMass(F, v))
          (S : Set (Primes(F)))ᶜ]
    have hpartition := finprod_mem_inter_mul_sdiff'
      (f := fun v : Primes(F) ↦ differentMass(F, v)) (s := Set.univ) (S : Set (Primes(F)))
      ((finiteLocalTamagawaMass_finite F).subset Set.inter_subset_right)
    rwa [Set.univ_inter, ← Set.compl_eq_univ_sdiff, finprod_mem_univ] at hpartition
  have hmass : μ W = archRegulatorMass(F) * selected := by
    change (μarch.prod (Measure.pi μf)) (A ×ˢ Set.univ.pi O) = _
    rw [Measure.prod_prod, Measure.pi_pi,
      infiniteLocalMultiplicativeTamagawaMeasure_regulatorStrip F]
    simp only [μf, O, finiteLocalMultiplicativeTamagawaMeasure_integerUnits, selected]
  have happly (V : Set (IdeleCoordinates F S)) : ν V = (c : ℝ≥0∞) * μ V := by
    rw [hc]
    rfl
  have hnormal := (hνapply W hW).trans
    ((congrArg (fun D ↦ multiplicativeTamagawaMeasure F D) hset).trans
      (multiplicativeTamagawaMeasure_regulatorStrip F))
  rw [happly, hmass, ← hsplit, ← mul_assoc (archRegulatorMass(F))] at hnormal
  have hpos : archRegulatorMass(F) ≠ 0 := by
    have := Units.regulator_pos F
    have := Real.pi_pos
    exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hselpos : selected ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun v _ ↦ ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top
  have hseltop : selected ≠ ⊤ := by
    refine ENNReal.prod_ne_top fun v _ ↦ ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr ?_).ne'
    have hv : 0 < (v.val.asIdeal.absNorm : ℝ) :=
      Nat.cast_pos.mpr (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v.val))
    exact Real.sqrt_pos_of_pos (pow_pos hv _)
  have hctail : (c : ℝ≥0∞) = tail :=
    (ENNReal.mul_left_inj (mul_ne_zero hpos hselpos)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hseltop)).mp (hnormal.trans (mul_comm _ _))
  let V : Set (IdeleCoordinates F S) := Set.univ.pi B ×ˢ Set.univ.pi U
  have hV : MeasurableSet V :=
    (MeasurableSet.univ_pi hB).prod (MeasurableSet.univ_pi hU)
  have hrect := hνapply V hV
  simp only [V, Set.mem_prod, Set.mem_univ_pi, and_assoc] at hrect
  refine hrect.symm.trans ?_
  rw [happly, hctail]
  change tail * (μarch.prod (Measure.pi μf)) (Set.univ.pi B ×ˢ Set.univ.pi U) = _
  rw [Measure.prod_prod, Measure.pi_pi, Measure.pi_pi, mul_comm tail]

/-- A continuous section of the norm identifies the quotient by its kernel with
the positive reals, with inverse induced by the section. -/
private def normQuotientEquiv {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] (n : G →* ℝ≥0ˣ) (hn : Continuous n)
    (s : ℝ≥0ˣ → G) (hs : Continuous s) (hr : RightInverse s n) : G ⧸ n.ker ≃ₜ* ℝ≥0ˣ :=
  { QuotientGroup.quotientKerEquivOfRightInverse n s hr with
    continuous_toFun := (QuotientGroup.isQuotientMap_mk n.ker).continuous_iff.mpr hn
    continuous_invFun := QuotientGroup.continuous_mk.comp hs }

/-- Scaling a Haar measure on the kernel scales the ambient Weil integral by
the same factor. Its normalization is fixed by the ambient measure and dt/t. -/
private theorem existsUnique_normKernelMeasure {G : Type*} [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    (n : G →* ℝ≥0ˣ) (hn : Continuous n) (s : ℝ≥0ˣ → G) (hs : Continuous s)
    (hr : RightInverse s n) :
    letI : MeasurableSpace (G ⧸ n.ker) := borel _
    ∃! ν : Measure n.ker, ν.IsHaarMeasure ∧ ν.Regular ∧
      IsWeilQuotientMeasure n.ker μ ν (positiveRealHaar.comap (QuotientGroup.kerLift n)) := by
  let H := n.ker
  let : MeasurableSpace (G ⧸ H) := borel _
  let : BorelSpace (G ⧸ H) := ⟨rfl⟩
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ _
  let : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  have hH : IsClosed (H : Set G) := isClosed_singleton.preimage hn
  let : LocallyCompactSpace H := hH.locallyCompactSpace
  let e := normQuotientEquiv n hn s hs hr
  let dt := positiveRealHaar.comap (QuotientGroup.kerLift n)
  have hdt : positiveRealHaar.map e.symm = dt := e.toHomeomorph.toMeasurableEquiv.map_symm
  let := positiveRealHaar_isHaarMeasure
  let : dt.IsHaarMeasure := hdt ▸ e.symm.isHaarMeasure_map positiveRealHaar
  let : dt.Regular := hdt ▸ Measure.Regular.map e.symm.toHomeomorph
  let ν₀ := Measure.haar (G := H)
  obtain ⟨μ₀, ⟨hμ₀, hreg, hw⟩, -⟩ :=
    existsUnique_isWeilQuotientMeasure_left H hH ν₀ dt ‹_› ‹_›
  let c := μ.haarScalarFactor μ₀
  have hc := (Measure.haarScalarFactor_pos_of_isHaarMeasure μ μ₀).ne'
  have hscale : μ = c • μ₀ := Measure.isMulLeftInvariant_eq_smul_of_regular μ μ₀
  have hscaled (d : ℝ≥0) : IsWeilQuotientMeasure H (d • μ₀) (d • ν₀) dt := by
    refine ⟨hw.1, hw.2.1, fun f hf ↦ ?_⟩
    simp only [lcaCosetIntegral, integral_smul_nnreal_measure, NNReal.smul_def, integral_smul]
    exact congrArg (d • ·) (hw.2.2 f hf)
  refine ⟨c • ν₀, ⟨Measure.IsHaarMeasure.nnreal_smul ν₀ hc, inferInstance,
    hscale ▸ hscaled c⟩, ?_⟩
  rintro ν ⟨hν, hνreg, hweil⟩
  let d := ν.haarScalarFactor ν₀
  have hd := (Measure.haarScalarFactor_pos_of_isHaarMeasure ν ν₀).ne'
  have hνscale : ν = d • ν₀ := Measure.isMulLeftInvariant_eq_smul_of_regular ν ν₀
  let : (d • μ₀).IsHaarMeasure := Measure.IsHaarMeasure.nnreal_smul μ₀ hd
  obtain ⟨_, _, hu⟩ := existsUnique_isWeilQuotientMeasure_left H hH ν dt ‹_› ‹_›
  have heq : μ = d • μ₀ := (hu μ ⟨inferInstance, inferInstance, hweil⟩).trans
    (hu _ ⟨inferInstance, inferInstance, hνscale ▸ hscaled d⟩).symm
  have hcd : c = d := by
    change μ.haarScalarFactor μ₀ = d
    calc
      _ = (d • μ₀).haarScalarFactor μ₀ := by congr 1
      _ = d := by simp
  rw [hνscale, hcd]

/-- Paper: §A.3.3.1, p. 561. Weil's formula for the idelic norm and `dt/t`
determines a unique regular Haar measure on the norm-one ideles. -/
theorem normOneIdeleTamagawaMeasure_existsUnique :
    ∃! ν : Measure N[F], ν.IsHaarMeasure ∧ ν.Regular ∧
      IsWeilQuotientMeasure N[F] (multiplicativeTamagawaMeasure F) ν
        (positiveRealHaar.comap (QuotientGroup.kerLift (ideleNorm F))) := by
  obtain ⟨h₂, hlc, _, _, hn, _⟩ := ideleGroup_topology F
  let : BorelSpace 𝕀[F] := ⟨rfl⟩
  obtain ⟨hμ, hreg, _⟩ := (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec
  let : (multiplicativeTamagawaMeasure F).IsHaarMeasure := hμ
  let : (multiplicativeTamagawaMeasure F).Regular := hreg
  exact existsUnique_normKernelMeasure _ _ hn _ (canonicalIdeleNormSection_continuous F)
    (canonicalIdeleNormSection_rightInverse F)

/-- Paper: §A.3.3.1, p. 561. Normalize the Haar measure on the norm-one
ideles by the global multiplicative Tamagawa measure and `dt/t`. -/
def normOneIdeleTamagawaMeasure : Measure N[F] :=
  (normOneIdeleTamagawaMeasure_existsUnique F).exists.choose

private theorem idele_secondCountable : SecondCountableTopology 𝕀[F] := by
  let := ratAdele_secondCountable
  obtain ⟨u, _, _⟩ := exists_adeleTrace_dualCoordinates F
  let : SecondCountableTopology 𝔸[F] := u.symm.toHomeomorph.isEmbedding.secondCountableTopology
  let : SecondCountableTopology 𝔸[F]ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

/-- In a split norm sequence the conditional measure at t is the translate of the
kernel measure by s(t). Integrating these translates gives the product formula. -/
private theorem normProduct_of_isWeil {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (n : G →* ℝ≥0ˣ) (hn : Continuous n)
    (s : ℝ≥0ˣ → G) (hs : Continuous s) (hr : RightInverse s n)
    (μ : Measure G) [μ.IsHaarMeasure] (hμreg : μ.Regular) (ν : Measure n.ker)
    [ν.IsHaarMeasure] (hνreg : ν.Regular) :
    letI : MeasurableSpace (G ⧸ n.ker) := borel _
    IsWeilQuotientMeasure n.ker μ ν (positiveRealHaar.comap (QuotientGroup.kerLift n)) →
      (positiveRealHaar.prod ν).map (fun p : ℝ≥0ˣ × n.ker ↦ s p.1 * p.2.val) = μ := by
  let H := n.ker
  let : MeasurableSpace (G ⧸ H) := borel _
  let : BorelSpace (G ⧸ H) := ⟨rfl⟩
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ _
  let : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  have hH : IsClosed (H : Set G) := isClosed_singleton.preimage hn
  let : LocallyCompactSpace H := hH.locallyCompactSpace
  let : SigmaCompactSpace n.ker := hH.sigmaCompactSpace
  let e := (normQuotientEquiv n hn s hs hr).toHomeomorph.toMeasurableEquiv
  let dt := positiveRealHaar.comap (QuotientGroup.kerLift n)
  have hdt : positiveRealHaar.map e.symm = dt := e.map_symm
  intro hw
  obtain ⟨hκ, hμ⟩ := weilMeasure_eq_bind H hH μ ν dt hw
  let φ (p : ℝ≥0ˣ × H) := s p.1 * p.2.val
  have hφ : Measurable φ := ((hs.comp continuous_fst).mul
    (continuous_subtype_val.comp continuous_snd)).measurable
  ext U hU
  rw [Measure.map_apply hφ hU, Measure.prod_apply (hφ hU), ← hμ, Measure.bind_apply hU hκ.aemeasurable,
    ← hdt, lintegral_map_equiv]
  apply lintegral_congr
  intro t
  have ht : Measurable (fun h : n.ker ↦ (e.symm t).out * (h : G)) :=
    (continuous_const.mul continuous_subtype_val).measurable
  rw [Measure.map_apply ht hU]
  exact fibreMeasure_eq_of_mk_eq H hH ν (x := s t) (y := (e.symm t).out)
    (U := U) (QuotientGroup.out_eq' (e.symm t)).symm

/-- Paper: §A.3.3.1, p. 561. Under any continuous homomorphic section, the
idelic decomposition transports the product of `dt/t` and the norm-one idele measure. -/
theorem multiplicativeTamagawaMeasure_normProduct (s : ℝ≥0ˣ →* 𝕀[F]) (hs : Continuous s)
    (hn : RightInverse s (ideleNorm F)) :
    (positiveRealHaar.prod (normOneIdeleTamagawaMeasure F)).map
        (fun tg : ℝ≥0ˣ × N[F] ↦ s tg.1 * tg.2.val) =
      multiplicativeTamagawaMeasure F := by
  obtain ⟨h₂, hlc, _, _, hnorm, _⟩ := ideleGroup_topology F
  let := idele_secondCountable F
  let : BorelSpace 𝕀[F] := ⟨rfl⟩
  obtain ⟨hm, hreg, _⟩ := (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec
  let : (multiplicativeTamagawaMeasure F).IsHaarMeasure := hm
  let : (multiplicativeTamagawaMeasure F).Regular := hreg
  obtain ⟨hν, hνreg, hw⟩ := (normOneIdeleTamagawaMeasure_existsUnique F).exists.choose_spec
  let : (normOneIdeleTamagawaMeasure F).IsHaarMeasure := hν
  let : (normOneIdeleTamagawaMeasure F).Regular := hνreg
  exact normProduct_of_isWeil _ hnorm s hs hn _ hreg _ hνreg hw

private theorem measurableSet_ideleFundamentalDomain
    (v₀ : InfinitePlace F) (σ : ℂ ≃ₐ[ℝ] ℂ)
    (b : Module.Basis (Fin (Units.rank F)) ℤ (Additive ((𝓞 F)ˣ ⧸ Units.torsion F)))
    (r : CommRing.Pic (𝓞 F) → N[F]) : MeasurableSet (ideleFundamentalDomain F b v₀ σ r) := by
  let K := (infiniteIdeleNorm F).ker
  let : BorelSpace 𝕀[F] := ⟨rfl⟩
  let : MeasurableSpace (InfiniteAdeleRing F)ˣ := borel _
  let : BorelSpace (InfiniteAdeleRing F)ˣ := ⟨rfl⟩
  let p (g : K) : Units.dirichletUnitTheorem.logSpace F := fun w ↦ infiniteIdeleLog F g.val w.val
  let q (g : K) := σ (extensionEmbedding v₀ (g.val.val v₀))
  have hp : Continuous p := continuous_pi fun w ↦
    (continuous_apply w.val).comp ((infiniteIdeleLog_continuous F).comp continuous_subtype_val)
  have hq : Continuous q := σ.toLinearEquiv.toContinuousLinearEquiv.continuous.comp
    ((isometry_extensionEmbedding v₀).continuous.comp ((continuous_apply v₀).comp
      (Units.continuous_val.comp continuous_subtype_val)))
  have hD : MeasurableSet (infiniteIdeleFundamentalDomain F b v₀ σ) :=
    ((ZSpan.fundamentalDomain_measurableSet _).preimage hp.measurable).inter
      (measurableSet_Ico.preimage (Complex.measurable_arg.comp hq.measurable))
  have hK := (infiniteIdeleNorm_ker_closed F).isClosedEmbedding_subtypeVal.measurableEmbedding
  let a : 𝕀[F] →* (InfiniteAdeleRing F)ˣ :=
    Units.map (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)).toMonoidHom
  have ha : Continuous a := continuous_fst.units_map _
  obtain ⟨_, _, _, _, _, hFinite, ⟨ePic⟩⟩ := ideleClassGroup_finiteness F
  let : Finite (CommRing.Pic (𝓞 F)) := @Finite.of_equiv _ _ hFinite ePic.toEquiv
  apply MeasurableSet.iUnion
  intro c
  apply MeasurableSet.const_smul
  exact (((isOpenEmbedding_integralAdeleUnits F ∅).isOpen_range.preimage
    continuous_subtype_val).measurableSet).inter
    ((hK.measurableSet_image.mpr hD).preimage (ha.comp continuous_subtype_val).measurable)

/-- Paper: §A.3.3.1, p. 561. A section strip over the idelic fundamental domain
has volume `log T` times the volume of the norm-one idele classes.
Deviation: The formula uses `T ≥ 1` so that the logarithm equals the interval mass. -/
theorem multiplicativeTamagawaMeasure_sectionStrip
    (s : ℝ≥0ˣ →* 𝕀[F]) (hs : Continuous s) (hn : RightInverse s (ideleNorm F))
    (v₀ : InfinitePlace F) (σ : ℂ ≃ₐ[ℝ] ℂ)
    (b : Module.Basis (Fin (Units.rank F)) ℤ (Additive ((𝓞 F)ˣ ⧸ Units.torsion F)))
    (r : CommRing.Pic (𝓞 F) → N[F]) (hr₁ : r 1 = 1)
    (hr : ∀ c, ideleIdealClass F (r c).val = c) (T : ℝ≥0ˣ) (hT : 1 ≤ (T.val : ℝ)) :
    multiplicativeTamagawaMeasure F
      {g | ∃ t : ℝ≥0ˣ, (t.val : ℝ) ∈ Icc 1 (T.val : ℝ) ∧
        ∃ x ∈ ideleFundamentalDomain F b v₀ σ r, g = s t * (x : N[F]).val} =
      ENNReal.ofReal (Real.log (T.val : ℝ)) * normOneIdeleClassTamagawaMeasure F univ := by
  let G := 𝕀[F]
  let H := N[F]
  let P := P[F]
  let C := C[F]
  let n := ideleNorm F
  let q := QuotientGroup.mk' P
  let d := IdeleGroup.unitEmbedding (𝓞 F) F
  let d₁ := d.codRestrict H (fun x ↦ (ideleNorm_spec F).2 (mem_range_self x))
  let E := ideleFundamentalDomain F b v₀ σ r
  let I := {t : ℝ≥0ˣ | (t.val : ℝ) ∈ Icc 1 (T.val : ℝ)}
  obtain ⟨h₂, hlc, _, _, hnorm, hclosed⟩ := ideleGroup_topology F
  obtain ⟨hd, hP, hPd, _, hq, hC₂, hClc, hqn, hcn, _, ⟨sc, hsc, hrc⟩, _⟩ :=
    ideleGroup_quotient.{_, 0} F
  let : BorelSpace G := ⟨rfl⟩
  let : BorelSpace C := ⟨rfl⟩
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ _
  let : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let := idele_secondCountable F
  let : SecondCountableTopology C := inferInstanceAs (SecondCountableTopology (G ⧸ P))
  let : DiscreteTopology P := isDiscrete_iff_discreteTopology.mp hPd
  let : (Measure.count : Measure P).IsHaarMeasure :=
    { lt_top_of_isCompact := fun _ h ↦ Measure.count_apply_lt_top.mpr h.finite_of_discrete
      open_pos := fun _ _ h ↦ Measure.count_ne_zero h }
  let : LocallyCompactSpace P := hP.locallyCompactSpace
  let : (Measure.count : Measure P).Regular := inferInstance
  let μ := multiplicativeTamagawaMeasure F
  let η := ideleClassTamagawaMeasure F
  let ν := normOneIdeleClassTamagawaMeasure F
  obtain ⟨hm, hmreg, hw, hv, hvreg, _, hcweil⟩ :=
    (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec
  let : μ.IsHaarMeasure := hm
  let : μ.Regular := hmreg
  let : η.IsHaarMeasure := hw.1
  let : η.Regular := hw.2.1
  let : ν.IsHaarMeasure := hv
  have hη := normProduct_of_isWeil (ideleClassNorm F) hcn sc hsc hrc η hw.2.1 ν hvreg hcweil
  obtain ⟨e, he⟩ := ideleNormSection_product F s hs hn
  let U := e '' (I ×ˢ E)
  have hI : MeasurableSet I := measurableSet_Icc.preimage
    (NNReal.continuous_coe.comp Units.continuous_val).measurable
  have hU : MeasurableSet U := e.toHomeomorph.measurableEmbedding.measurableSet_image.mpr
    (hI.prod (measurableSet_ideleFundamentalDomain F v₀ σ b r))
  have htarget : {g : G | ∃ t ∈ I, ∃ x ∈ E, g = s t * (x : H).val} = U := by
    ext g
    constructor
    · rintro ⟨t, ht, x, hx, rfl⟩
      exact ⟨(t, x), ⟨ht, hx⟩, he t x⟩
    · rintro ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩
      exact ⟨t, ht, x, hx, he t x⟩
  change μ {g : G | ∃ t ∈ I, ∃ x ∈ E, g = s t * (x : H).val} = _
  rw [htarget]
  -- Each norm-one coset has exactly one representative in the chosen domain.
  have htranslate (x : H) : ∃! k : P, x * (⟨k.val, (ideleNorm_spec F).2 k.property⟩ : H) ∈ E := by
    have hx : x ∈ ⋃ z : Fˣ, d₁ z • E := (ideleFundamentalDomain_cover F b v₀ σ r hr₁ hr).symm ▸ mem_univ _
    obtain ⟨z, y, hy, hzy⟩ := mem_iUnion.mp hx
    change d₁ z * y = x at hzy
    subst x
    refine ⟨⟨d z⁻¹, mem_range_self _⟩, ?_, ?_⟩
    · change d₁ z * y * d₁ z⁻¹ ∈ E
      simpa [map_inv, mul_right_comm] using hy
    · rintro ⟨_, w, rfl⟩ hw
      change d₁ z * y * d₁ w ∈ E at hw
      have hwz : z * w = 1 := by
        by_contra h
        apply Set.disjoint_left.mp (ideleFundamentalDomain_disjoint F b v₀ σ r hr₁ hr _ h)
          (Set.smul_mem_smul_set (a := d₁ (z * w)) hy)
        simpa only [smul_eq_mul, map_mul, mul_right_comm] using hw
      exact Subtype.ext (congrArg d (eq_inv_of_mul_eq_one_right hwz))
  have hfiber (g : G) : (Measure.count : Measure P) {k | g * (k : G) ∈ U} =
      I.indicator (fun _ ↦ (1 : ℝ≥0∞)) (n g) := by
    obtain ⟨⟨t, x⟩, rfl⟩ := e.surjective g
    have hnorm' : n (e (t, x)) = t := by
      rw [he, map_mul, hn, MonoidHom.mem_ker.mp x.property, mul_one]
    have htest (k : P) : e (t, x) * k.val ∈ U ↔
        t ∈ I ∧ x * (⟨k.val, (ideleNorm_spec F).2 k.property⟩ : H) ∈ E := by
      let z : H := ⟨k.val, (ideleNorm_spec F).2 k.property⟩
      rw [show e (t, x) * k.val = e (t, x * z) by rw [he, he]; exact mul_assoc _ _ _]
      exact e.injective.mem_set_image
    rw [hnorm']
    by_cases ht : t ∈ I
    · obtain ⟨k, hk, hu⟩ := htranslate x
      have hset : {k : P | e (t, x) * k.val ∈ U} = {k} := by
        ext l
        exact ⟨fun hl ↦ hu l ((htest l).mp hl).2, fun hl ↦ hl ▸ (htest k).mpr ⟨ht, hk⟩⟩
      rw [hset, Measure.count_singleton, indicator_of_mem ht]
    · have hset : {k : P | e (t, x) * k.val ∈ U} = ∅ :=
        eq_empty_iff_forall_notMem.mpr fun k h ↦ ht ((htest k).mp h).1
      rw [hset, measure_empty, indicator_of_notMem ht]
  -- Weil integration counts these representatives on each principal-idele orbit.
  obtain ⟨hκ, hμ⟩ := weilMeasure_eq_bind P hP μ Measure.count η hw
  rw [← hμ, Measure.bind_apply hU hκ.aemeasurable]
  let W := (ideleClassNorm F) ⁻¹' I
  have hW : MeasurableSet W := hcn.measurable hI
  calc
    _ = ∫⁻ c : C, W.indicator (fun _ ↦ (1 : ℝ≥0∞)) c ∂η := by
      apply lintegral_congr
      intro c
      have ht : Measurable (fun h : P ↦ c.out * (h : G)) :=
        (continuous_const.mul continuous_subtype_val).measurable
      rw [Measure.map_apply ht hU]
      change Measure.count {k : P | c.out * (k : G) ∈ U} = _
      rw [hfiber]
      have hnq : ideleClassNorm F c = n c.out :=
        (congrArg (ideleClassNorm F) (QuotientGroup.out_eq' c)).symm.trans (hqn c.out)
      simp [W, Set.indicator, hnq]
    _ = η W := lintegral_indicator_one hW
    _ = _ := by
      have hmap : Measurable (fun z : ℝ≥0ˣ × C₁[F] ↦ sc z.1 * z.2.val) :=
        ((hsc.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)).measurable
      rw [← hη, Measure.map_apply hmap hW]
      have hpre : (fun z : ℝ≥0ˣ × C₁[F] ↦ sc z.1 * z.2.val) ⁻¹' W = I ×ˢ univ := by
        ext z
        change ideleClassNorm F (sc z.1 * z.2.val) ∈ I ↔ _
        simp [map_mul, hrc z.1, MonoidHom.mem_ker.mp z.2.property]
      let : CompactSpace C₁[F] := (ideleClassGroup_finiteness F).2.1
      rw [hpre, Measure.prod_prod, positiveRealHaar_interval T hT]

/-- Paper: Definition A.3.4.1(1), p. 561. The S-local additive Tamagawa
measure is the product of all archimedean and the selected finite local measures. -/
def sAdditiveTamagawaMeasure : Measure (SAdeleRing F S) :=
  (Measure.pi (infiniteLocalAdditiveTamagawaMeasure F)).prod
    (Measure.pi (fun v : S ↦ finiteLocalAdditiveTamagawaMeasure F v.val))

/-- Paper: Definition A.3.4.1(2), p. 561. The S-local multiplicative Tamagawa
measure is the finite product of the local measures on the unit groups. -/
def sMultiplicativeTamagawaMeasure : Measure 𝕀ₛ :=
  let e := ContinuousMulEquiv.prodUnits (InfiniteAdeleRing F)
    ((v : S) → v.val.adicCompletion F)
  let eArch := ContinuousMulEquiv.piUnits (M := fun w : InfinitePlace F ↦ w.Completion)
  let eS := ContinuousMulEquiv.piUnits (M := fun v : S ↦ v.val.adicCompletion F)
  ((Measure.pi (infiniteLocalMultiplicativeTamagawaMeasure F)).prod
      (Measure.pi (fun v : S ↦ finiteLocalMultiplicativeTamagawaMeasure F v.val))).map
    (fun x ↦ e.symm (eArch.symm x.1, eS.symm x.2))

private theorem finiteLocalMultiplicative_isHaar (v : Primes(F)) :
    (finiteLocalMultiplicativeTamagawaMeasure F v).IsHaarMeasure := by
  let μ := Measure.haar (G := (v.adicCompletion F)ˣ)
  let U : Set (v.adicCompletion F)ˣ := (v.adicCompletionIntegers F).units
  have hopen : IsOpen U := Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)
  have hpos := hopen.measure_pos μ ⟨1, (v.adicCompletionIntegers F).units.one_mem⟩
  have hcompact : IsCompact U := Submonoid.units_isCompact
    (isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v))
  have hq : 0 < (v.asIdeal.absNorm : ℝ) := by
    exact_mod_cast zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v)
  exact Measure.IsHaarMeasure.smul μ
    (ENNReal.div_ne_zero.mpr ⟨ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top,
      hcompact.measure_ne_top⟩)
    (ENNReal.div_ne_top (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr
      (Real.sqrt_pos_of_pos (pow_pos hq _))).ne') hpos.ne')

private def sIdeleUnitsEquiv :
    (((w : InfinitePlace F) → w.Completionˣ) × ((v : S) → (v.val.adicCompletion F)ˣ)) ≃ₜ* 𝕀ₛ :=
  let e := ContinuousMulEquiv.prodUnits (InfiniteAdeleRing F) ((v : S) → v.val.adicCompletion F)
  let a := ContinuousMulEquiv.piUnits (M := fun w : InfinitePlace F ↦ w.Completion)
  let b := ContinuousMulEquiv.piUnits (M := fun v : S ↦ v.val.adicCompletion F)
  (ContinuousMulEquiv.mk' (a.symm.toHomeomorph.prodCongr b.symm.toHomeomorph)
    (fun x y ↦ Prod.ext (map_mul a.symm x.1 y.1) (map_mul b.symm x.2 y.2))).trans e.symm

private theorem sIdele_borelSpace
    [∀ w : InfinitePlace F, SecondCountableTopology w.Completion]
    [∀ v : S, SecondCountableTopology (v.val.adicCompletion F)] : BorelSpace 𝕀ₛ := by
  let (w : InfinitePlace F) : BorelSpace w.Completion := ⟨rfl⟩
  let : BorelSpace (SAdeleRing F S) := inferInstanceAs
    (BorelSpace (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  refine ⟨?_⟩
  rw [(sIdeleGroup_description F S).1.eq_induced, borel_comap, ← BorelSpace.measurable_eq]
  rfl

section SLocalIdeleMeasures

private local instance (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
private local instance (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
  (isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
private local instance (w : InfinitePlace F) : BorelSpace w.Completion := ⟨rfl⟩
private local instance (w : InfinitePlace F) : BorelSpace w.Completionˣ := borelSpace_units_of_continuousInv₀ _
private local instance (w : InfinitePlace F) : SecondCountableTopology w.Completionˣ :=
  Units.isEmbedding_val₀.secondCountableTopology
private local instance (v : S) : SecondCountableTopology (v.val.adicCompletion F)ˣ :=
  Units.isEmbedding_val₀.secondCountableTopology
private local instance (w : InfinitePlace F) : (infiniteLocalMultiplicativeTamagawaMeasure F w).IsHaarMeasure :=
  infiniteLocalMultiplicative_isHaar F w
private local instance (v : S) : (finiteLocalMultiplicativeTamagawaMeasure F v.val).IsHaarMeasure :=
  finiteLocalMultiplicative_isHaar F v.val
private local instance : BorelSpace 𝕀ₛ := sIdele_borelSpace F S

/-- Paper: Definition A.3.4.1(2), p. 561. The mass of an S-local unit rectangle
is the product of the archimedean coordinate masses and the finite integer-unit masses. -/
theorem sMultiplicativeTamagawaMeasure_integerUnits
    (B : (w : InfinitePlace F) → Set w.Completionˣ) (hB : ∀ w, MeasurableSet (B w)) :
    sMultiplicativeTamagawaMeasure F S
        {g | (∀ w, Units.map ((Pi.evalRingHom InfinitePlace.Completion w).comp
          (RingHom.fst _ _)).toMonoidHom g ∈ B w) ∧
            ∀ v : S, Units.map ((Pi.evalRingHom (fun u : S ↦ u.val.adicCompletion F) v).comp
              (RingHom.snd _ _)).toMonoidHom g ∈ (v.val.adicCompletionIntegers F).units} =
      (∏ w : InfinitePlace F, infiniteLocalMultiplicativeTamagawaMeasure F w (B w)) *
        ∏ v : S, differentMass(F, v.val) := by
  let e := (sIdeleUnitsEquiv F S).toHomeomorph.toMeasurableEquiv
  let U (v : S) : Set (v.val.adicCompletion F)ˣ := (v.val.adicCompletionIntegers F).units
  let μ := (Measure.pi (infiniteLocalMultiplicativeTamagawaMeasure F)).prod
    (Measure.pi fun v : S ↦ finiteLocalMultiplicativeTamagawaMeasure F v.val)
  change μ.map e _ = _
  rw [e.map_apply]
  calc
    _ = μ ((univ.pi B) ×ˢ (univ.pi U)) := by
      congr 1
      ext x
      simp only [mem_preimage, mem_ofPred_eq, mem_prod, mem_univ_pi]
      rfl
    _ = _ := by
      rw [show μ = (Measure.pi (infiniteLocalMultiplicativeTamagawaMeasure F)).prod
          (Measure.pi fun v : S ↦ finiteLocalMultiplicativeTamagawaMeasure F v.val) from rfl,
        Measure.prod_prod, Measure.pi_pi_aux _ B hB, Measure.pi_pi]
      simp only [U, finiteLocalMultiplicativeTamagawaMeasure_integerUnits]

/-- Paper: Definition A.3.4.1(3)(1), p. 561. The Haar measure on the norm-one
S-ideles is uniquely determined by Weil's formula using the product and `dt/t`. -/
theorem sNormOneIdeleTamagawaMeasure_existsUnique :
    ∃! ν : Measure Nₛ, ν.IsHaarMeasure ∧ ν.Regular ∧
      IsWeilQuotientMeasure Nₛ (sMultiplicativeTamagawaMeasure F S) ν
        (positiveRealHaar.comap (QuotientGroup.kerLift (sIdeleNorm F S))) := by
  let E := sIdeleUnitsEquiv F S
  let : T2Space 𝕀ₛ := (sIdeleGroup_description F S).2.1
  let : LocallyCompactSpace 𝕀ₛ := (sIdeleGroup_description F S).2.2.1
  let : SecondCountableTopology 𝕀ₛ := E.symm.toHomeomorph.isEmbedding.secondCountableTopology
  let : TopologicalSpace.MetrizableSpace 𝕀ₛ := E.symm.toHomeomorph.isEmbedding.metrizableSpace
  let m := sMultiplicativeTamagawaMeasure F S
  let μ := (Measure.pi (infiniteLocalMultiplicativeTamagawaMeasure F)).prod
    (Measure.pi fun v : S ↦ finiteLocalMultiplicativeTamagawaMeasure F v.val)
  let : (Measure.pi (infiniteLocalMultiplicativeTamagawaMeasure F)).IsHaarMeasure :=
    Measure.pi.isHaarMeasure _
  let : (Measure.pi fun v : S ↦ finiteLocalMultiplicativeTamagawaMeasure F v.val).IsHaarMeasure :=
    Measure.pi.isHaarMeasure _
  let : μ.IsHaarMeasure := Measure.prod.instIsHaarMeasure _ _
  let : m.IsHaarMeasure := E.isHaarMeasure_map μ
  let : m.Regular := inferInstance
  have hn : Continuous (sIdeleNorm F S) := by
    apply Units.isEmbedding_val₀.continuous_iff.mpr
    change Continuous (fun g : 𝕀ₛ ↦ ((sIdeleNorm F S g).val))
    simp only [sIdeleNorm, MonoidHom.mul_apply, MonoidHom.finsetProd_apply, MonoidHom.pow_apply,
      Units.val_mul, Units.coe_prod, Units.val_pow_eq_pow_val]
    change Continuous (fun g : 𝕀ₛ ↦ (∏ w : InfinitePlace F, ‖g.val.1 w‖₊ ^ w.mult) *
      ∏ v : S, ‖g.val.2 v‖₊)
    fun_prop
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  let s := singlePlaceIdeleNormSection F w
  let p := Units.map (adeleProjection F S).toMonoidHom
  have hp : Continuous p := (continuous_adeleProjection F S).units_map _
  apply existsUnique_normKernelMeasure m _ hn (p ∘ s) (hp.comp (singlePlaceIdeleNormSection_continuous F w))
  intro t
  let A := integralAdelesOutside F S
  have hmem (u : ℝ≥0ˣ) : (s u).val ∈ A := by
    simp only [A, integralAdelesOutside, Subring.mem_iInf]
    intro v _
    exact (v.adicCompletionIntegers F).one_mem
  have ht : s t ∈ A.toSubmonoid.units :=
    ⟨hmem t, by
      change ((s t)⁻¹).val ∈ A
      rw [← map_inv]
      exact hmem t⁻¹⟩
  let g := A.toSubmonoid.unitsEquivUnitsType ⟨s t, ht⟩
  exact ((sIdeleNorm_spec F S).1 g).symm.trans (singlePlaceIdeleNormSection_rightInverse F w t)

end SLocalIdeleMeasures

/-- Paper: Definition A.3.4.1(3)(1), p. 561. Use the Weil normalization of
the product measure on the norm-one S-ideles. -/
def sNormOneIdeleTamagawaMeasure : Measure Nₛ :=
  (sNormOneIdeleTamagawaMeasure_existsUnique F S).exists.choose

/-- Paper: Definition A.3.4.1(3)(1), p. 561. The chosen norm-one measure
satisfies Weil's formula with `dt/t` on the norm quotient. -/
theorem sNormOneIdeleTamagawaMeasure_isWeil :
    IsWeilQuotientMeasure Nₛ (sMultiplicativeTamagawaMeasure F S)
      (sNormOneIdeleTamagawaMeasure F S)
      (positiveRealHaar.comap (QuotientGroup.kerLift (sIdeleNorm F S))) :=
  (sNormOneIdeleTamagawaMeasure_existsUnique F S).exists.choose_spec.2.2

-- TODO(paper-gap): Definition A.3.4.1(3)(2)–(3) prescribes a measure on the
-- local S-ideles but takes the quotient of the larger group in (A.1.5.7).
-- The latter includes the product of the integer-unit groups outside S.

section SLocalPlancherel

private local instance (v : InfinitePlace F) : SecondCountableTopology v.Completion :=
  (isometry_extensionEmbedding v).isEmbedding.secondCountableTopology
private local instance (v : InfinitePlace F) : BorelSpace v.Completion := ⟨rfl⟩
private local instance (v : Primes(F)) : ProperSpace (v.adicCompletion F) :=
  properSpace_adicCompletion v
private local instance : BorelSpace 𝔸[F] := ⟨rfl⟩
private local instance : BorelSpace (SAdeleRing F S) :=
  inferInstanceAs (BorelSpace (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
private local instance : SecondCountableTopology (SAdeleRing F S) :=
  inferInstanceAs (SecondCountableTopology
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
private local instance : LocallyCompactSpace (SAdeleRing F S) :=
  inferInstanceAs (LocallyCompactSpace (InfiniteAdeleRing F × ((v : S) → v.val.adicCompletion F)))
private local instance : T2Space (SAdeleRing F S) :=
  inferInstanceAs (T2Space (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
private local instance (v : InfinitePlace F) : (infiniteLocalAdditiveTamagawaMeasure F v).IsAddHaarMeasure :=
  infiniteLocalAdditiveTamagawaMeasure_haar F v
private local instance (v : Primes(F)) : (finiteLocalAdditiveTamagawaMeasure F v).IsAddHaarMeasure :=
  finiteLocalAdditiveTamagawaMeasure_isAddHaar F v

/-- Restrict finitely many omitted coordinates to measurable sets and the remaining
ones to the integer rings. Projection multiplies the S-local product measure by
the product of the omitted masses. -/
private theorem sAdeleProjection_restrict (T : Finset (Primes(F))) (hST : Disjoint S T)
    (hT : ∀ v : Primes(F), v ∉ S ∪ T → differentExp(F, v) = 0)
    (U : (v : Primes(F)) → Set (v.adicCompletion F)) (hU : ∀ v, MeasurableSet (U v))
    (c : ℝ≥0) (hc : (c : ℝ≥0∞) = ∏ v ∈ T, finiteLocalAdditiveTamagawaMeasure F v (U v)) :
    MeasurePreserving (adeleProjection F S)
      ((additiveTamagawaMeasure F).restrict {a | (∀ v ∈ T, a.2 v ∈ U v) ∧
        a ∈ integralAdelesOutside F (S ∪ T)}) (c • sAdditiveTamagawaMeasure F S) := by
  let p := adeleProjection F S
  have hp := (continuous_adeleProjection F S).measurable
  let μ := Measure.pi (infiniteLocalAdditiveTamagawaMeasure F)
  let ν (v : S) := finiteLocalAdditiveTamagawaMeasure F v.val
  have htail : (∏ᶠ v : {v : Primes(F) // v ∉ S ∪ T}, differentMass(F, v.val)) = 1 :=
    finprod_eq_one_of_forall_eq_one fun v ↦ by simp [hT v.val v.property]
  refine ⟨hp, ?_⟩
  change _ = c • μ.prod (Measure.pi ν)
  rw [← Measure.prod_smul_left]
  symm
  apply Measure.prod_eq_generateFrom MeasurableSpace.generateFrom_measurableSet
    generateFrom_pi MeasurableSpace.isPiSystem_measurableSet
    isPiSystem_pi (c • μ).toFiniteSpanningSetsIn
    (Measure.FiniteSpanningSetsIn.pi fun v ↦ (ν v).toFiniteSpanningSetsIn)
  rintro B hB _ ⟨V, hV, rfl⟩
  change MeasurableSet B at hB
  have hV' (v : S) : MeasurableSet (V v) := hV v (mem_univ _)
  have hW : MeasurableSet (B ×ˢ univ.pi V) := hB.prod (MeasurableSet.pi countable_univ fun v _ ↦ hV' v)
  rw [Measure.map_apply hp hW, Measure.restrict_apply (hp hW), Measure.pi_pi,
    Measure.coe_nnreal_smul_apply, hc]
  let box (v : Primes(F)) := if h : v ∈ S then V ⟨v, h⟩ else U v
  let L := S ∪ T
  have hbox (v : L) : MeasurableSet (box v.val) := by
    dsimp only [box]
    split_ifs <;> first | exact hV' _ | exact hU _
  have hset : p ⁻¹' (B ×ˢ univ.pi V) ∩ {a | (∀ v ∈ T, a.2 v ∈ U v) ∧
        a ∈ integralAdelesOutside F L} =
      {a | a.1 ∈ B ∧ (∀ v : L, a.2 v.val ∈ box v.val) ∧ a ∈ integralAdelesOutside F L} := by
    ext a
    change ((a.1 ∈ B ∧ (fun v : S ↦ a.2 v.val) ∈ univ.pi V) ∧ _) ↔ _
    simp only [Set.mem_univ_pi, mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hB', hS'⟩, hT', hI⟩
      refine ⟨hB', fun v ↦ ?_, hI⟩
      by_cases hv : v.val ∈ S
      · simpa [box, hv] using hS' ⟨v.val, hv⟩
      · simpa [box, hv] using hT' v.val ((Finset.mem_union.mp v.property).resolve_left hv)
    · rintro ⟨hB', hL, hI⟩
      refine ⟨⟨hB', fun v ↦ ?_⟩, fun v hv ↦ ?_, hI⟩
      · simpa [box, v.property] using hL ⟨v.val, Finset.mem_union_left _ v.property⟩
      · have hvS := Finset.disjoint_right.mp hST hv
        simpa [box, hvS] using hL ⟨v, Finset.mem_union_right _ hv⟩
  rw [hset, additiveTamagawaMeasure_restrictedProduct F L B hB _ hbox, htail, mul_one]
  let m (v : Primes(F)) := finiteLocalAdditiveTamagawaMeasure F v (box v)
  have hs : (∏ v ∈ S, m v) = ∏ v : S, ν v (V v) := by
    rw [Finset.prod_subtype S (fun _ ↦ Iff.rfl) m]
    exact Finset.prod_congr rfl fun v _ ↦ by simp [m, box, ν, v.property]
  have ht : (∏ v ∈ T, m v) = ∏ v ∈ T, finiteLocalAdditiveTamagawaMeasure F v (U v) :=
    Finset.prod_congr rfl fun v hv ↦ by simp [m, box, Finset.disjoint_right.mp hST hv]
  change μ B * (∏ v : L, m v.val) = _
  rw [← Finset.prod_subtype L (fun _ ↦ Iff.rfl) m, Finset.prod_union hST, hs, ht]
  ac_rfl

/-- Frequencies whose outside coordinates annihilate the omitted local integer rings. -/
private def sAdeleTailDual : Set 𝔸[F] :=
  {y | ∀ v : Primes(F), v ∉ S → ‖y.2 v‖ ≤ (v.asIdeal.absNorm : ℝ) ^ differentExp(F, v)}

/-- The integer tail and its annihilator project with reciprocal masses. -/
private theorem sAdeleProjection_dual_masses :
    ∃ c : ℝ≥0, c ≠ 0 ∧ MeasurableSet (sAdeleTailDual F S) ∧
      MeasurePreserving (adeleProjection F S)
        ((additiveTamagawaMeasure F).restrict (integralAdelesOutside F S)) (c • sAdditiveTamagawaMeasure F S) ∧
      MeasurePreserving (adeleProjection F S)
        ((additiveTamagawaMeasure F).restrict (sAdeleTailDual F S)) (c⁻¹ • sAdditiveTamagawaMeasure F S) := by
  let R := (Ideal.finite_factors (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F))).toFinset
  let T := R \ S
  have hST : Disjoint S T := Finset.disjoint_sdiff
  have hT (v : Primes(F)) (hv : v ∉ S ∪ T) : differentExp(F, v) = 0 := by
    apply multiplicity_eq_zero_of_not_dvd
    intro hd
    by_cases hs : v ∈ S
    · exact hv (Finset.mem_union_left _ hs)
    · have hR : v ∈ R := by simpa [R] using hd
      exact hv (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hR, hs⟩))
  let O (v : Primes(F)) := (v.adicCompletionIntegers F : Set (v.adicCompletion F))
  let B (v : Primes(F)) := {z : v.adicCompletion F | ‖z‖ ≤ (v.asIdeal.absNorm : ℝ) ^ differentExp(F, v)}
  have hO (v) : MeasurableSet (O v) := (Valued.isOpen_valuationSubring _).measurableSet
  have hB (v) : MeasurableSet (B v) := (isClosed_le continuous_norm continuous_const).measurableSet
  have hBO (v : Primes(F)) (hv : v ∉ S ∪ T) : B v = O v := by
    ext z
    change (‖z‖ ≤ (v.asIdeal.absNorm : ℝ) ^ differentExp(F, v)) ↔ z ∈ v.adicCompletionIntegers F
    rw [hT v hv, pow_zero, HeightOneSpectrum.mem_adicCompletionIntegers]
    exact Valued.toNormedField.norm_le_one_iff
  let reg (U : ∀ v : Primes(F), Set (v.adicCompletion F)) : Set 𝔸[F] :=
    {a | (∀ v ∈ T, a.2 v ∈ U v) ∧ a ∈ integralAdelesOutside F (S ∪ T)}
  have hreg (U : ∀ v : Primes(F), Set (v.adicCompletion F))
      (hu : ∀ v, v ∉ S ∪ T → U v = O v) :
      reg U = {a : 𝔸[F] | ∀ v, v ∉ S → a.2 v ∈ U v} := by
    ext a
    simp only [reg, mem_ofPred_eq, integralAdelesOutside, Subring.mem_iInf]
    constructor
    · rintro ⟨hin, hout⟩ v hv
      by_cases ht : v ∈ T
      · exact hin v ht
      · have hv' := Finset.notMem_union.mpr ⟨hv, ht⟩
        rw [hu v hv']
        exact hout v hv'
    · intro h
      refine ⟨fun v hv ↦ h v (Finset.disjoint_right.mp hST hv), fun v hv ↦ ?_⟩
      change a.2 v ∈ O v
      rw [← hu v hv]
      exact h v (Finset.notMem_union.mp hv).1
  have hi : reg O = (integralAdelesOutside F S : Set 𝔸[F]) := by
    rw [hreg O (fun _ _ ↦ rfl)]
    ext a
    change (∀ v ∉ S, a.2 v ∈ O v) ↔ a ∈ integralAdelesOutside F S
    simp only [integralAdelesOutside, Subring.mem_iInf]
    rfl
  have hb : reg B = sAdeleTailDual F S := hreg B hBO
  let m (v : Primes(F)) := (Real.toNNReal (Real.sqrt ((v.asIdeal.absNorm : ℝ) ^ differentExp(F, v))))⁻¹
  have hpos (v : Primes(F)) : 0 < Real.sqrt ((v.asIdeal.absNorm : ℝ) ^ differentExp(F, v)) :=
    Real.sqrt_pos_of_pos (pow_pos (Nat.cast_pos.mpr (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v))) _)
  have hm (v : Primes(F)) : finiteLocalAdditiveTamagawaMeasure F v (O v) = (m v : ℝ≥0∞) := by
    rw [finiteLocalAdditiveTamagawaMeasure_integers, show (m v : ℝ≥0∞) = _ from
      ENNReal.coe_inv (Real.toNNReal_pos.mpr (hpos v)).ne']
    rfl
  have hm0 (v : Primes(F)) : m v ≠ 0 := inv_ne_zero (Real.toNNReal_pos.mpr (hpos v)).ne'
  let c := ∏ v ∈ T, m v
  have hc : c ≠ 0 := Finset.prod_ne_zero_iff.mpr fun v _ ↦ hm0 v
  refine ⟨c, hc, ?_, ?_, ?_⟩
  · rw [← hb]
    change MeasurableSet ({a : 𝔸[F] | ∀ v ∈ T, a.2 v ∈ B v} ∩ (integralAdelesOutside F (S ∪ T) : Set _))
    refine MeasurableSet.inter ?_ (isOpen_integralAdelesOutside F _).measurableSet
    simp only [ofPred_forall]
    exact T.finite_toSet.measurableSet_biInter fun v _ ↦ (hB v).preimage
      (((RestrictedProduct.continuous_eval v).comp continuous_snd :
        Continuous (fun a : 𝔸[F] ↦ a.2 v)).measurable)
  · rw [← hi]
    apply sAdeleProjection_restrict F S T hST hT O hO
    simp only [hm, c, ENNReal.ofNNReal_finsetProd]
  · rw [← hb]
    apply sAdeleProjection_restrict F S T hST hT B hB
    have hv (v : Primes(F)) : finiteLocalAdditiveTamagawaMeasure F v (B v) = ((m v)⁻¹ : ℝ≥0) := by
      rw [show finiteLocalAdditiveTamagawaMeasure F v (B v) = _ from
        finiteLocalAdditiveTamagawaMeasure_inverseDifferentBall F v, ENNReal.coe_inv (hm0 v)]
      exact congrArg Inv.inv (hm v)
    simp only [hv, c, ← Finset.prod_inv_distrib, ENNReal.ofNNReal_finsetProd]

/-- Extending a function by the integer-tail indicator restricts its Fourier
transform to the dual tail and multiplies it by the omitted integer mass. -/
private theorem tamagawaFourier_sAdeleLift (c : ℝ≥0)
    (hm : MeasurePreserving (adeleProjection F S)
      ((additiveTamagawaMeasure F).restrict (integralAdelesOutside F S)) (c • sAdditiveTamagawaMeasure F S))
    (f : SAdeleRing F S → ℂ) (hf : Integrable f (sAdditiveTamagawaMeasure F S)) :
    let I := (integralAdelesOutside F S : Set 𝔸[F])
    let p := adeleProjection F S
    tamagawaFourier (additiveTamagawaMeasure F) (adeleStandardCharacter F) (I.indicator (f ∘ p)) =
      (sAdeleTailDual F S).indicator (((c : ℝ) •
        tamagawaFourier (sAdditiveTamagawaMeasure F S) (sAdeleStandardCharacter F S) f) ∘ p) := by
  let I := integralAdelesOutside F S
  let p := adeleProjection F S
  let μ := additiveTamagawaMeasure F
  let μS := sAdditiveTamagawaMeasure F S
  have hI := (isOpen_integralAdelesOutside F S).measurableSet
  let : μ.IsAddHaarMeasure := (additiveTamagawaMeasure_existsUnique F).exists.choose_spec.1
  obtain ⟨e, he⟩ := exists_sAdeleDualEquiv F S
  funext y
  by_cases hy : y ∈ sAdeleTailDual F S
  · rw [indicator_of_mem hy]
    let k (z : SAdeleRing F S) := f z * star (sAdeleStandardCharacter F S (z * p y) : ℂ)
    have hψ (x : 𝔸[F]) (hx : x ∈ I) :
        adeleStandardCharacter F (x * y) = sAdeleStandardCharacter F S (p x * p y) := by
      rw [← map_mul]
      apply (sAdeleStandardCharacter_eq_of_trivial_outside F S _ _).symm
      intro v hv
      have hvy := hy v hv
      change y.2 v ∈ {t : v.adicCompletion F | ‖t‖ ≤ (v.asIdeal.absNorm : ℝ) ^ differentExp(F, v)} at hvy
      rw [← finiteLocalStandardCharacter_annihilator_integers F v] at hvy
      simp only [I, integralAdelesOutside, Subring.mem_iInf] at hx
      exact hvy (x.2 v) (hx v hv)
    have hk : AEStronglyMeasurable k μS := by
      have heval (z : SAdeleRing F S) :
          sAdeleStandardCharacter F S (z * p y) = e (Multiplicative.ofAdd (p y)) (Multiplicative.ofAdd z) :=
        (congrArg _ (mul_comm _ _)).trans (he _ _).symm
      simp only [k, heval]
      exact hf.aestronglyMeasurable.mul
        ((continuous_subtype_val.comp ((e _).continuous.comp continuous_ofAdd)).star.aestronglyMeasurable)
    change (∫ x, (I : Set 𝔸[F]).indicator (f ∘ p) x * star (adeleStandardCharacter F (x * y) : ℂ) ∂μ) =
      (c : ℝ) • ∫ z, k z ∂μS
    have hfun (x : 𝔸[F]) : (I : Set 𝔸[F]).indicator (f ∘ p) x * star (adeleStandardCharacter F (x * y) : ℂ) =
        (I : Set 𝔸[F]).indicator (k ∘ p) x := by
      by_cases hx : x ∈ I
      · simp only [indicator_of_mem hx, Function.comp_apply, hψ x hx, k]
      · simp only [indicator_of_notMem hx, zero_mul]
    simp_rw [hfun]
    rw [integral_indicator hI]
    calc
      _ = ∫ z, k z ∂(c • μS) := by
        have h := integral_map hm.measurable.aemeasurable
          (f := k) (hm.map_eq.symm ▸ hk.smul_measure (c : ℝ≥0∞))
        rw [hm.map_eq] at h
        exact h.symm
      _ = _ := integral_smul_nnreal_measure k c
  · rw [indicator_of_notMem hy]
    change ¬ ∀ v : Primes(F), v ∉ S → ‖y.2 v‖ ≤ (v.asIdeal.absNorm : ℝ) ^ differentExp(F, v) at hy
    obtain ⟨v, hv⟩ := not_forall.mp hy
    obtain ⟨hv, hbad⟩ := not_imp.mp hv
    change y.2 v ∉ {z : v.adicCompletion F | ‖z‖ ≤ (v.asIdeal.absNorm : ℝ) ^ differentExp(F, v)} at hbad
    rw [← finiteLocalStandardCharacter_annihilator_integers F v] at hbad
    obtain ⟨x, hx⟩ := not_forall.mp hbad
    obtain ⟨hx, hxy⟩ := not_imp.mp hx
    let b := finiteAdeleSingle F v x
    obtain ⟨hb, hpb⟩ := finiteAdeleSingle_outside F S v hv x hx
    have hne : star (adeleStandardCharacter F (b * y) : ℂ) ≠ 1 := by
      intro h
      apply hxy
      have heq : finiteAdeleSingle F v (x * y.2 v) = b * y := by
        rw [mul_comm x, mul_comm b]
        exact finiteAdeleSingle_mul F v y x
      apply Circle.coe_injective
      change (adeleStandardCharacter F (finiteAdeleSingle F v _) : ℂ) = 1
      rw [heq]
      exact star_injective (h.trans (star_one ℂ).symm)
    let g := (I : Set 𝔸[F]).indicator (f ∘ p)
    have hg (z : 𝔸[F]) : g (b + z) = g z := by
      have hmem : b + z ∈ I ↔ z ∈ I := I.toAddSubgroup.add_mem_cancel_left hb
      by_cases hz : z ∈ I
      · simp only [g, indicator_of_mem hz, indicator_of_mem (hmem.mpr hz), Function.comp_apply, map_add,
          show p b = 0 from hpb, zero_add]
      · exact (indicator_of_notMem (mt hmem.mp hz) _).trans (indicator_of_notMem hz _).symm
    obtain ⟨ψ, hψ⟩ := exists_adeleCharacterHom F
    have hadd (a z : 𝔸[F]) : adeleStandardCharacter F (a + z) =
        adeleStandardCharacter F a * adeleStandardCharacter F z := by
      simp only [← hψ, ofAdd_add, map_mul]
    let k (z : 𝔸[F]) := g z * star (adeleStandardCharacter F (z * y) : ℂ)
    have htranslate (z : 𝔸[F]) : k (b + z) = k z * star (adeleStandardCharacter F (b * y) : ℂ) := by
      simp only [k, hg, add_mul, hadd, Circle.coe_mul, star_mul']
      ring
    have h : (∫ z, k z ∂μ) = (∫ z, k z ∂μ) * star (adeleStandardCharacter F (b * y) : ℂ) := by
      rw [← integral_mul_const]
      simp_rw [← htranslate]
      exact (integral_add_left_eq_self k b).symm
    change (∫ z, k z ∂μ) = 0
    by_contra hn
    exact hne (mul_left_cancel₀ hn (h.symm.trans (mul_one _).symm))

/-- Paper: Example A.3.1.11, p. 559, and Remark A.3.4.2, p. 562. The S-local
product is self-dual under the pairing from the product character. -/
theorem sAdditiveTamagawaMeasure_selfDual :
    IsTamagawaSelfDual (sAdditiveTamagawaMeasure F S) (sAdeleStandardCharacter F S) := by
  let G := Multiplicative (SAdeleRing F S)
  let μ := sAdditiveTamagawaMeasure F S
  let μA := additiveTamagawaMeasure F
  let I := (integralAdelesOutside F S : Set 𝔸[F])
  let B := sAdeleTailDual F S
  let p := adeleProjection F S
  let : (Measure.pi (infiniteLocalAdditiveTamagawaMeasure F)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  let : (Measure.pi (fun v : S ↦ finiteLocalAdditiveTamagawaMeasure F v.val)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  have hm : μ.IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  let : T2Space G := inferInstanceAs (T2Space (SAdeleRing F S))
  let : LocallyCompactSpace G := inferInstanceAs (LocallyCompactSpace (SAdeleRing F S))
  let m : Measure G := μ
  let : m.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := hm.toIsFiniteMeasureOnCompacts, toIsOpenPosMeasure := hm.toIsOpenPosMeasure,
      map_mul_left_eq_self := fun x ↦ hm.map_add_left_eq_self x.toAdd }
  let : m.Regular := addHaar_regular_of_sigmaCompactSpace μ
  let : MeasurableSpace (PontryaginDual G) := borel _
  let : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  obtain ⟨e, he⟩ := exists_sAdeleDualEquiv F S
  obtain ⟨E, hE, hA⟩ := additiveTamagawaMeasure_selfDual F
  obtain ⟨c, hc, hB, hIproj, hBproj⟩ := sAdeleProjection_dual_masses F S
  have hI : MeasurableSet I := (isOpen_integralAdelesOutside F S).measurableSet
  refine ⟨e, he, e.isHaarMeasure_map m, Measure.Regular.map e.toHomeomorph, ?_⟩
  intro f hf₁ hf₂
  let fS (x : SAdeleRing F S) := f (Multiplicative.ofAdd x)
  let fA := I.indicator (fS ∘ p)
  let g := tamagawaFourier μ (sAdeleStandardCharacter F S) fS
  have hg : (lcaFourier m f ∘ e : G → ℂ) = fun x ↦ g x.toAdd := by
    funext x
    exact (tamagawaFourier_eq_lcaFourier μ _ fS x.toAdd (e x)
      (fun z ↦ (he x.toAdd z).trans (congrArg _ (mul_comm _ _)))).symm
  have hgcont : Continuous g := show Continuous (fun x : SAdeleRing F S ↦ g x) from
    (show Continuous (fun x : G ↦ g x.toAdd) from hg ▸ ((continuous_lcaFourier m hf₁).comp e.continuous))
  have hfA₁ : Integrable fA μA := (integrable_indicator_iff hI).mpr
    (hIproj.integrable_comp_of_integrable (show Integrable fS μ from hf₁).smul_measure_nnreal)
  have hfA₂ : MemLp fA 2 μA := (memLp_indicator_iff_restrict hI.nullMeasurableSet).mpr
    ((show MemLp fS 2 μ from hf₂).smul_measure_nnreal.comp_measurePreserving hIproj)
  have hnorm := (hA.2.2 (fun x ↦ fA x.toAdd) hfA₁ hfA₂).2
  let : MeasurableSpace (PontryaginDual (Multiplicative 𝔸[F])) := borel _
  let : BorelSpace (PontryaginDual (Multiplicative 𝔸[F])) := ⟨rfl⟩
  let : BorelSpace (Multiplicative 𝔸[F]) := ⟨rfl⟩
  have htrans : lcaFourier (G := Multiplicative 𝔸[F]) μA (fun x ↦ fA x.toAdd) ∘ E =
      fun x ↦ (B.indicator (((c : ℝ) • g) ∘ p)) x.toAdd := by
    funext x
    exact (tamagawaFourier_eq_lcaFourier μA _ fA x.toAdd (E x)
      (fun z ↦ (hE x.toAdd z).trans (congrArg _ (mul_comm _ _)))).symm.trans
        (congrFun (tamagawaFourier_sAdeleLift F S c hIproj fS hf₁) x.toAdd)
  have hEm : MeasurableEmbedding (E : Multiplicative 𝔸[F] → _) := E.toHomeomorph.measurableEmbedding
  have hnorm := hEm.eLpNorm_map_measure.symm.trans hnorm
  change eLpNorm (lcaFourier (G := Multiplicative 𝔸[F]) μA (fun x ↦ fA x.toAdd) ∘ E) 2 _ = _ at hnorm
  rw [htrans] at hnorm
  change eLpNorm (B.indicator (((c : ℝ) • g) ∘ p)) 2 μA = eLpNorm (I.indicator (fS ∘ p)) 2 μA at hnorm
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hB.nullMeasurableSet,
    eLpNorm_indicator_eq_eLpNorm_restrict hI.nullMeasurableSet,
    eLpNorm_comp_measurePreserving (hgcont.const_smul (c : ℝ)).aestronglyMeasurable hBproj,
    eLpNorm_comp_measurePreserving ((show MemLp fS 2 μ from hf₂).aestronglyMeasurable.smul_measure _) hIproj,
    eLpNorm_smul_measure_of_ne_zero' (inv_ne_zero hc), eLpNorm_smul_measure_of_ne_zero' hc,
    eLpNorm_const_smul] at hnorm
  have hroot : c ^ (2 : ℝ≥0∞).toReal⁻¹ = NNReal.sqrt c := by simp [NNReal.sqrt_eq_rpow, one_div]
  have hscale : (c⁻¹ ^ (2 : ℝ≥0∞).toReal⁻¹) * c = NNReal.sqrt c := by
    rw [NNReal.inv_rpow, hroot]
    nth_rw 2 [← NNReal.mul_self_sqrt c]
    rw [inv_mul_cancel_left₀ (NNReal.sqrt_eq_zero.not.mpr hc)]
  have hn : eLpNorm g 2 μ = eLpNorm fS 2 μ := by
    apply (ENNReal.mul_right_inj (ENNReal.coe_ne_zero.mpr (NNReal.sqrt_eq_zero.not.mpr hc))
      ENNReal.coe_ne_top).mp
    change (↑(c⁻¹ ^ (2 : ℝ≥0∞).toReal⁻¹) : ℝ≥0∞) * (‖(c : ℝ)‖ₑ * eLpNorm g 2 μ) =
      ↑(c ^ (2 : ℝ≥0∞).toReal⁻¹) * eLpNorm fS 2 μ at hnorm
    rwa [show ‖(c : ℝ)‖ₑ = (c : ℝ≥0∞) by simp,
      ← mul_assoc, ← ENNReal.coe_mul, hscale, hroot] at hnorm
  have hlocal : MemLp g 2 μ := by
    change eLpNorm g 2 μ < ⊤
    rw [hn]
    exact hf₂.eLpNorm_lt_top
  have hem := e.toHomeomorph.measurableEmbedding
  refine ⟨hem.memLp_map_measure_iff.mpr (hg.symm ▸ hlocal), ?_⟩
  exact hem.eLpNorm_map_measure.trans ((congrArg (fun k : G → ℂ ↦ eLpNorm k 2 m) hg).trans hn)


-- TODO(paper-gap): The last sentence of Remark A.3.4.2 reverses the criterion
-- for mass one. The preceding prime-to-S volume is one precisely when S contains
-- all the ramified finite places.

/-- The scalar between the S-local product and covolume-one measures is the
reciprocal of the mass of the omitted integer rings. -/
private theorem sAdditiveTamagawaMeasure_scale :
    ∃ c : ℝ≥0, c ≠ 0 ∧ sAdditiveTamagawaMeasure F S = c • sAdditiveCovolumeOneMeasure F S ∧
      (c : ℝ≥0∞) = ∏ᶠ v : {v : Primes(F) // v ∉ S}, (differentMass(F, v.val))⁻¹ := by
  let μ := sAdditiveTamagawaMeasure F S
  let ν := sAdditiveCovolumeOneMeasure F S
  let : μ.IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  let : ν.IsAddHaarMeasure := (sAdditiveCovolumeOneMeasure_existsUnique F S).exists.choose_spec.1
  let c := μ.addHaarScalarFactor ν
  have hscale : μ = c • ν := Measure.isAddLeftInvariant_eq_smul μ ν
  refine ⟨c, (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ ν).ne', hscale, ?_⟩
  let B := infiniteAdeleFundamentalDomain F (RingOfIntegers.basis F)
  let O (v : S) := (v.val.adicCompletionIntegers F : Set (v.val.adicCompletion F))
  let D := sAdeleFundamentalDomain F S (RingOfIntegers.basis F)
  have hc : (c : ℝ≥0∞) = μ D := by
    rw [hscale]
    change (c : ℝ≥0∞) = c * ν D
    simp only [ν, D, sAdditiveCovolumeOneMeasure_fundamentalDomain, mul_one]
  have hD : D = B ×ˢ univ.pi O := by ext a; simp [D, B, O, sAdeleFundamentalDomain]
  let m (v : {v : Primes(F) // v ∉ S}) := differentMass(F, v.val)
  have hrect := additiveTamagawaMeasure_restrictedProduct F S B
    (infiniteAdeleFundamentalDomain_tamagawaMass F).1 O
    (fun v ↦ (Valued.isOpen_valuationSubring _).measurableSet)
  have hg : {a : 𝔸[F] | a.1 ∈ B ∧ (∀ v : S, a.2 v.val ∈ O v) ∧
      a ∈ integralAdelesOutside F S} = adeleFundamentalDomain F (RingOfIntegers.basis F) := by
    ext a
    change (_ ∧ (∀ v : S, a.2 v.val ∈ O v) ∧ a ∈ integralAdelesOutside F S) ↔
      (_ ∧ a ∈ integralAdelesOutside F ∅)
    simp only [integralAdelesOutside, Subring.mem_iInf, Finset.notMem_empty, not_false_eq_true,
      true_implies]
    refine and_congr_right fun _ ↦ ⟨fun ⟨hin, hout⟩ v ↦ ?_, fun hall ↦ ⟨fun v ↦ hall v.val,
      fun v _ ↦ hall v⟩⟩
    by_cases hv : v ∈ S
    · exact hin ⟨v, hv⟩
    · exact hout v hv
  rw [hg, additiveTamagawaMeasure_fundamentalDomain] at hrect
  have hc_mul : (c : ℝ≥0∞) * (∏ᶠ v, m v) = 1 := by
    rw [hc, hD]
    change ((Measure.pi (infiniteLocalAdditiveTamagawaMeasure F)).prod
      (Measure.pi fun v : S ↦ finiteLocalAdditiveTamagawaMeasure F v.val)) _ * _ = 1
    rw [Measure.prod_prod, Measure.pi_pi]
    exact hrect.symm
  have hm : HasFiniteMulSupport m := (finiteLocalTamagawaMass_finite F).preimage
    (f := fun v : {v : Primes(F) // v ∉ S} ↦ v.val) Subtype.val_injective.injOn
  have hmi : HasFiniteMulSupport (fun v ↦ (m v)⁻¹) := hm.subset fun v hv h ↦ hv (by simp [h])
  have hcancel : (∏ᶠ v, m v) * (∏ᶠ v, (m v)⁻¹) = 1 := by
    rw [← finprod_mul_distrib hm hmi]
    apply finprod_eq_one_of_forall_eq_one
    intro v
    have hq : 0 < (v.val.asIdeal.absNorm : ℝ) := by
      exact_mod_cast zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v.val)
    exact ENNReal.mul_inv_cancel (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)
      (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr (Real.sqrt_pos_of_pos (pow_pos hq _))).ne')
  calc
    (c : ℝ≥0∞) = c * ((∏ᶠ v, m v) * (∏ᶠ v, (m v)⁻¹)) := by rw [hcancel, mul_one]
    _ = _ := by rw [← mul_assoc, hc_mul, one_mul]

end SLocalPlancherel

/-- Paper: Remark A.3.4.2, p. 562. The additive quotient mass of the product
measure is the square root of the part of the different norm outside S.
Deviation: The prime-to-S part is taken over places of the number field. -/
theorem sAdditiveTamagawaMeasure_quotientVolume :
    ∃ ν : Measure (Multiplicative (SAdeleRing F S) ⧸ Aₛ),
      IsWeilQuotientMeasure Aₛ (show Measure (Multiplicative (SAdeleRing F S)) from
        sAdditiveTamagawaMeasure F S) Measure.count ν ∧
      ν univ = ∏ᶠ v : {v : Primes(F) // v ∉ S}, (differentMass(F, v.val))⁻¹ := by
  obtain ⟨c, hc, hscale, hmass⟩ := sAdditiveTamagawaMeasure_scale F S
  obtain ⟨ν, hν, hνone⟩ := (sAdditiveCovolumeOneMeasure_existsUnique F S).exists.choose_spec.2.2
  let G := Multiplicative (SAdeleRing F S)
  let : BorelSpace (G ⧸ Aₛ) := ⟨rfl⟩
  let := hν.1
  let := hν.2.1
  refine ⟨c • ν, ⟨Measure.IsHaarMeasure.nnreal_smul ν hc, inferInstance, fun f hf ↦ ?_⟩, ?_⟩
  · let μ : Measure G := sAdditiveCovolumeOneMeasure F S
    have heq : (show Measure G from sAdditiveTamagawaMeasure F S) = c • μ := hscale
    rw [heq, integral_smul_nnreal_measure, integral_smul_nnreal_measure]
    exact congrArg (c • ·) (hν.2.2 f hf)
  · change (c : ℝ≥0∞) * ν univ = _
    rwa [hνone, mul_one]

/-- Paper: Example A.3.1.11, p. 558. If every prime dividing the different
is in S, the S-local additive product has the quotient-volume-one normalization. -/
theorem sAdditiveTamagawaMeasure_eq_covolumeOne
    (hS : ∀ v : Primes(F), v.asIdeal ∣ differentIdeal ℤ (𝓞 F) → v ∈ S) :
    sAdditiveTamagawaMeasure F S = sAdditiveCovolumeOneMeasure F S := by
  obtain ⟨c, -, hscale, hc⟩ := sAdditiveTamagawaMeasure_scale F S
  have hone : (c : ℝ≥0∞) = 1 := hc.trans (finprod_eq_one_of_forall_eq_one fun v ↦ by
    simp [multiplicity_eq_zero_of_not_dvd (fun hd ↦ v.property (hS v.val hd))])
  rw [hscale, show c = 1 from ENNReal.coe_inj.mp hone, one_smul]

/-- Paper: Remark A.3.4.2, p. 562. The local integer-ring indicator is fixed
by the Fourier transform exactly at places unramified over their residue prime.
Deviation: Unramifiedness is expressed by nondivisibility of the global different. -/
theorem finiteLocalTamagawaFourier_fixes_integers_iff (v : Primes(F)) :
    tamagawaFourier (finiteLocalAdditiveTamagawaMeasure F v) (finiteLocalStandardCharacter F v)
        ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ ↦ (1 : ℂ))) =
      (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ ↦ (1 : ℂ)) ↔
      ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 F) := by
  rw [finiteLocalTamagawaFourier_integers]
  have hq : 1 < (v.asIdeal.absNorm : ℝ) := by
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  constructor
  · intro h hdvd
    have hd := multiplicity_pos_of_dvd hdvd
      (Ideal.finiteMultiplicity v.isPrime.ne_top differentIdeal_ne_bot)
    have hpow := one_lt_pow₀ hq hd.ne'
    have hball : (0 : v.adicCompletion F) ∈
        {y : v.adicCompletion F | ‖y‖ ≤ (v.asIdeal.absNorm : ℝ) ^ differentExp(F, v)} := by
      simp
    have hzero := congrFun h 0
    simp only [Pi.smul_apply, Set.indicator_of_mem hball,
      Set.indicator_of_mem (v.adicCompletionIntegers F).zero_mem, smul_eq_mul, mul_one,
      ENNReal.toReal_inv, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] at hzero
    have hroot : Real.sqrt ((v.asIdeal.absNorm : ℝ) ^ differentExp(F, v)) = 1 := by
      exact inv_eq_one.mp (Complex.ofReal_injective (hzero.trans Complex.ofReal_one.symm))
    apply hpow.ne'
    calc
      _ = Real.sqrt ((v.asIdeal.absNorm : ℝ) ^ differentExp(F, v)) ^ 2 :=
        (Real.sq_sqrt (zero_le_one.trans hpow.le)).symm
      _ = 1 := by rw [hroot, one_pow]
  · intro h
    simp only [multiplicity_eq_zero_of_not_dvd h, pow_zero, Real.sqrt_one, ENNReal.ofReal_one,
      inv_one, ENNReal.toReal_one, Complex.ofReal_one, one_smul]
    congr 1
    ext x
    exact Valued.toNormedField.norm_le_one_iff.trans
      (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).symm

end RiemannMasullo
