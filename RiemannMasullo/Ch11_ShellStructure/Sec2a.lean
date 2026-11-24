module

public import RiemannMasullo.Ch10_TraceSpectral.Sec2
import RiemannMasullo.Ch10_TraceSpectral.Sec1
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

import all RiemannMasullo.Ch07_SchauderBasesZeta.Sec1b
public import RiemannMasullo.Ch11_ShellStructure.Sec1b
import all RiemannMasullo.Ch11_ShellStructure.Sec1b

/-! # Orbital Markushevich bases on the 0-line

Masullo, §11.2 before §11.2.1, pp. 483–487.
-/

@[expose] public noncomputable section

open Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false
set_option maxSynthPendingDepth 8

variable {F : Type*} [Field F] [NumberField F]

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" =>
  (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "logNorm" => (logIdeleClassNorm F)
local notation "W(" s ")" => CompactIntervalSobolev μ𝔽 logNorm 0 0 s
local notation "W'(" s ")" => CompactIntervalSobolev μ𝔽 logNorm 0 0 s true
local notation "μ'(" s ")" => (μ𝔽).withDensity (fun g ↦
  ENNReal.ofReal (intervalSobolevDensity 0 0 (s) (logNorm g))⁻¹)
local notation "hI" => (le_rfl (a := (0 : ℝ)))
local notation "H(" a ", " hs ")" => globalThetaSobolev F a hI hs
local notation "j(" a ", " hs ")" => globalThetaSobolevInclusion F a hI hs
local notation "ρ(" hs ")" => hardySobolevTranslation μ𝔽 m𝔽 0 0 _ hI hs
local notation "Wω(" hs ", " ω ")" =>
  actionIsotype ((ρ(hs)).comp (ideleClassNorm F).ker.subtype) ω
local notation "restriction" =>
  (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁ →ₜ* C𝔽)
local notation "ℬ₀" => ↥(adelePolarSubspace F)
local notation "jet(" χ ", " t ", " m ")" => spectralZeroJet χ 0 t m
local notation "frequency(" t ")" => ((t : ℝ) : ℂ) * Complex.I
local notation "q(" v ")" => (Ideal.absNorm (HeightOneSpectrum.asIdeal v))

-- (11.2.0.1) is spectralSobolevPairing at the interval [0, 0].
-- (11.2.0.2) recalls the quotient operator globalThetaPrincipalValue.

local notation "pvTest(" S ", " f ")" =>
  (⟨adelePrincipalValue F S (f : ℬ₀).val, adelePrincipalValue_mem_polarSubspace S f⟩ : ℬ₀)
local notation "theta(" f ")" =>
  (Submodule.Quotient.mk (f : ℬ₀) : GlobalPolarFreeThetaSpace F)

section ZeroLineDensity

/-- A positive zero order at real part zero would reflect to a zero on the
one-line, where the completed Hecke continuation has no zeros. -/
private theorem denseRange_globalTheta_zeroLine_order (χ : PontryaginDual C𝔽) {z : ℂ}
    (hz : z.re = 0) : meromorphicOrderAt (continuedCompletedHeckeL χ) z ≤ 0 := by
  let L := continuedCompletedHeckeL χ
  let L' := continuedCompletedHeckeL χ⁻¹
  obtain ⟨hL, h⟩ := continuedCompletedHeckeL_spec χ
  obtain ⟨hL', h'⟩ := continuedCompletedHeckeL_spec χ⁻¹
  obtain ⟨ε, hε, hn, hf⟩ := completedHeckeL_continuation_functionalEquation χ L L' hL h hL' h'
  let r (w : ℂ) := 1 - w
  have hfun : L' ∘ r = ε * L := funext hf
  have hr := (hasDerivAt_id z).const_sub (1 : ℂ)
  have he : meromorphicOrderAt L z = meromorphicOrderAt L' (1 - z) := by
    rw [← meromorphicOrderAt_mul_of_ne_zero (f := L) (hε.analyticAt z) (hn z), ← hfun]
    apply meromorphicOrderAt_comp_of_deriv_ne_zero (analyticAt_const.sub analyticAt_id)
    change deriv r z ≠ 0
    rw [show deriv r z = -1 from hr.deriv]
    norm_num
  change meromorphicOrderAt L z ≤ 0
  rw [he]
  have hRe : (1 - z).re = 1 := by simp [hz]
  apply le_of_not_gt
  intro hzero
  have hbad := completedHeckeL_continuation_zeros χ⁻¹ L' hL' h' (hRe ▸ zero_lt_one) hzero
  exact (lt_irrefl (1 : ℝ)) (hRe ▸ hbad)

/-- At degree greater than one the line common-kernel theorem applies.
There are no admitted jets on the zero-line. -/
private theorem denseRange_globalTheta_zeroLine_high {s : ℝ} (hs : 1 < s) :
    DenseRange (fun u : GlobalPolarFreeThetaSpace F ↦ (j(0, (zero_lt_one.trans hs).le) u : W(s))) := by
  obtain ⟨χ, hχ⟩ := exists_spectralBasepointChoice F
  intro y
  change y ∈ globalThetaSobolev F 0 hI (zero_lt_one.trans hs).le
  refine (spectralLineJet_commonKernel (a := 0) χ hχ hs y).mpr (fun i ↦ False.elim ?_)
  let z : ℂ := (0 : ℂ) + (i.val.2.1 : ℂ) * Complex.I
  have ho := denseRange_globalTheta_zeroLine_order (χ i.val.1) (z := z) (by simp [z])
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_le_ne_top (WithTop.coe_ne_top (a := (0 : ℤ))) ho)
  have hpos := ((lt_spectralBoundaryMultiplicity _ _ _).mp i.property).1
  change i.val.2.2 < (meromorphicOrderAt (continuedCompletedHeckeL (χ i.val.1)) z).untop₀.toNat at hpos
  rw [← hn] at ho hpos
  have hn' : n ≤ 0 := WithTop.coe_le_coe.mp ho
  simp [Int.toNat_of_nonpos hn'] at hpos

/-- Restriction from a stronger weighted L² norm has dense range when
compactly supported continuous functions belong to both spaces. -/
private theorem denseRange_globalTheta_zeroLine_restrict {X : Type*} [TopologicalSpace X]
    [T2Space X] [NormalSpace X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ ν : Measure X) [μ.Regular] [IsFiniteMeasureOnCompacts ν] (h : μ ≤ ν) :
    ∃ U : Lp ℂ 2 ν →L[ℝ] Lp ℂ 2 μ, DenseRange U ∧ ∀ f, (U f : X → ℂ) =ᵐ[μ] f := by
  have h1 : μ ≤ (1 : ENNReal) • ν := by simpa using h
  let U := Lp.LpToLpOfMeasureLeSMul (E := ℂ) (p := 2) ENNReal.one_ne_top h1
  have hU (f) : (U f : X → ℂ) =ᵐ[μ] f := Lp.coeFn_LpToLpOfMeasureLeSMul _ _ f
  refine ⟨U, fun x ↦ EMetric.mem_closure_iff.mpr fun ε hε ↦ ?_, hU⟩
  obtain ⟨δ, hδ, hδε⟩ := exists_between hε
  obtain ⟨g, hg, hclose, hgc, _⟩ := (Lp.memLp x).exists_hasCompactSupport_eLpNorm_sub_le
    ENNReal.ofNat_ne_top hδ.ne'
  have hgν : MemLp g 2 ν := hgc.memLp_of_hasCompactSupport hg
  have heq := (hU (hgν.toLp g)).trans (h.absolutelyContinuous.ae_eq hgν.coeFn_toLp)
  refine ⟨U (hgν.toLp g), mem_range_self _, ?_⟩
  rw [Lp.edist_def]
  exact (eLpNorm_congr_ae (Filter.EventuallyEq.rfl.sub heq)).trans_le hclose |>.trans_lt hδε

/-- The zero-line Sobolev density is polynomial in the log norm. Increasing
its degree increases the measure, and both measures are finite on compacts. -/
private theorem denseRange_globalTheta_zeroLine_compare {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hst : s ≤ t) (hd : DenseRange (fun u : GlobalPolarFreeThetaSpace F ↦ (j(0, ht) u : W(t)))) :
    DenseRange (fun u : GlobalPolarFreeThetaSpace F ↦ (j(0, hs) u : W(s))) := by
  let ρ (r : ℝ) (g : C𝔽) := intervalSobolevDensity 0 0 r (logNorm g)
  let μ (r : ℝ) := (μ𝔽).withDensity (fun g ↦ ENNReal.ofReal (ρ r g))
  have hlog : Continuous logNorm := (NNReal.continuous_coe.comp (Units.continuous_val.comp
    (isProperMap_ideleClassNorm F).continuous)).log fun x ↦ (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
  have hbase : Continuous (fun x : C𝔽 ↦ 1 + (logNorm x) ^ 2) := continuous_const.add (hlog.pow 2)
  have hρ (r : ℝ) : Continuous (ρ r) := by
    simpa [ρ, intervalSobolevDensity] using
      hbase.rpow_const (p := r / 2) (fun x ↦ Or.inl (by dsimp; positivity))
  let (r : ℝ) : IsLocallyFiniteMeasure (μ r) := IsLocallyFiniteMeasure.withDensity_ofReal (hρ r)
  have hst' : μ s ≤ μ t := withDensity_mono (.of_forall fun x ↦ ENNReal.ofReal_le_ofReal
    (by simpa [ρ, intervalSobolevDensity] using Real.rpow_le_rpow_of_exponent_le
          (le_add_of_nonneg_right (sq_nonneg (logNorm x))) (by linarith : s / 2 ≤ t / 2)))
  obtain ⟨U, hU, hrep⟩ := denseRange_globalTheta_zeroLine_restrict (μ s) (μ t) hst'
  have hEq (u : GlobalPolarFreeThetaSpace F) :
      U (j(0, ht) u : W(t)) = (j(0, hs) u : W(s)) := by
    induction u using Submodule.Quotient.induction_on with
    | H f =>
      apply Lp.ext
      apply (hrep _).trans
      apply (withDensity_absolutelyContinuous μ𝔽 _).ae_eq
      exact ((existsUnique_globalThetaSobolevEmbedding (F := F) 0 0 0 t hI ht).exists.choose_spec.2 f).trans
        ((existsUnique_globalThetaSobolevEmbedding (F := F) 0 0 0 s hI hs).exists.choose_spec.2 f).symm
  have hfull := hU.comp hd U.continuous
  exact (funext hEq) ▸ hfull

end ZeroLineDensity

/-- Paper: Proposition 11.2.0.1, p. 484. The polar-free theta classes are norm
dense in the full global Sobolev space on the 0-line.
Deviation: The cited line theorem assumes degree greater than one. Pass
from a higher degree through the dense inclusion of the weighted spaces
to cover every nonnegative degree in the printed statement. -/
theorem denseRange_globalTheta_zeroLine {s : ℝ} (hs : 0 ≤ s) :
    DenseRange (fun u : GlobalPolarFreeThetaSpace F ↦ (j(0, hs) u : W(s))) := by
  have ht : 1 < s + 2 := by linarith
  exact denseRange_globalTheta_zeroLine_compare hs (zero_lt_one.trans ht).le (by linarith)
    (denseRange_globalTheta_zeroLine_high ht)

/-- Inserting a local completion into the adeles is continuous. -/
private theorem globalThetaPrincipalValue_sobolevBound_formula_cont (v : V) :
    Continuous (AdeleRing.ofAdicCompletion (𝓞 F) F v) := by
  classical
  apply continuous_const.prodMk
  apply continuous_restrictedProduct_of_uniform
  · intro w
    exact (continuous_apply w).comp (continuous_mulSingle (A := fun u : V ↦
      u.adicCompletion F) v)
  · filter_upwards [Filter.eventually_cofinite_ne v] with w hw x
    change Pi.mulSingle v x w ∈ w.adicCompletionIntegers F
    rw [Pi.mulSingle_eq_of_ne hw]
    exact (w.adicCompletionIntegers F).one_mem

/-- The adele with `(π u)⁻¹` at `v` and `1` elsewhere, as a continuous function of the unit. -/
private theorem globalThetaPrincipalValue_sobolevBound_formula_contU (v : V)
    (π : (v.adicCompletion F)ˣ) :
    Continuous (fun u : (v.adicCompletion F)ˣ ↦
      ((IdeleGroup.ofAdicCompletion (𝓞 F) F v (π * u)⁻¹ : IdeleGroup (𝓞 F) F) : 𝔸[F])) :=
  (globalThetaPrincipalValue_sobolevBound_formula_cont v).comp
    (Units.continuous_val.comp ((continuous_const.mul continuous_id).inv))

/-- On an S-adele, the projection of the idele inserted at `v` has trivial infinite part and the
inserted value at `v`, for `S = {v}`. -/
private theorem globalThetaPrincipalValue_sobolevBound_formula_proj (v : V)
    (y : (v.adicCompletion F)ˣ) (z : SAdeleRing F {v}) :
    (z * adeleProjection F {v} (IdeleGroup.ofAdicCompletion (𝓞 F) F v y : 𝔸[F])).1 = z.1 ∧
      ((z * adeleProjection F {v} (IdeleGroup.ofAdicCompletion (𝓞 F) F v y : 𝔸[F])).2
        ⟨v, Finset.mem_singleton_self v⟩ : v.adicCompletion F) =
        (z.2 ⟨v, Finset.mem_singleton_self v⟩ : v.adicCompletion F) * (y : v.adicCompletion F) := by
  classical
  constructor
  · change z.1 * 1 = z.1
    rw [mul_one]
  · change (z.2 ⟨v, Finset.mem_singleton_self v⟩ : v.adicCompletion F) *
      Pi.mulSingle v (y : v.adicCompletion F) v = _
    rw [Pi.mulSingle_eq_same]

open scoped TensorProduct in
/-- A predicate on the target of an inductive tensor product with a finite tensor product holds
everywhere once it holds on pure tensors and is closed under zero, addition and scalars. -/
private theorem globalThetaPrincipalValue_sobolevBound_formula_ind {ι : Type*} [Fintype ι]
    {E N : Type*} {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup N] [Module ℂ N] [TopologicalSpace N]
    (e : InductiveTensor E (FinestLocallyConvex (⨂[ℂ] i, M i)) ≃L[ℂ] N) (P : N → Prop)
    (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y)) (hsmul : ∀ (r : ℂ) x, P x → P (r • x))
    (hpure : ∀ (a : E) (g : ∀ i, M i), P (e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] i, g i)))) (x : N) : P x := by
  have key : ∀ y : E ⊗[ℂ] (⨂[ℂ] i, M i), P (e y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => exact (congrArg P (map_zero e)).mpr h0
    | tmul a b =>
      induction b using PiTensorProduct.induction_on with
      | smul_tprod r g =>
        exact (congrArg (fun t ↦ P (e t)) (TensorProduct.tmul_smul r a _)).mpr
          ((congrArg P (map_smul e r _)).mpr (hsmul r _ (hpure a g)))
      | add b c hb hc =>
        exact (congrArg (fun t ↦ P (e t)) (TensorProduct.tmul_add a b c)).mpr
          ((congrArg P (map_add e _ _)).mpr (hadd _ _ hb hc))
    | add y z hy hz => exact (congrArg P (map_add e y z)).mpr (hadd _ _ hy hz)
  exact (congrArg P (e.apply_symm_apply x)).mp (key (e.symm x))

/-- Paper: Definition 5.3.1.4(1) and Lemma 5.3.1.3, p. 241. For `S = {v}` the S-local principal
value is the identity minus the normalized unit average of the translates by `(π u)⁻¹` at `v`. -/
private theorem globalThetaPrincipalValue_sobolevBound_formula_local (v : V)
    (π : (v.adicCompletion F)ˣ) (hπ : Valued.v.IsUniformizer π.val)
    (a : SchwartzBruhat (Multiplicative (SAdeleRing F {v}))) (z : SAdeleRing F {v}) :
    sAdelePrincipalValue F (Finset.Subset.refl {v}) a (Multiplicative.ofAdd z) =
      a (Multiplicative.ofAdd z) - ((finiteLocalMultiplicativeTamagawaMeasure F v).real
          ((HeightOneSpectrum.adicCompletionIntegers F v).units : Set (v.adicCompletion F)ˣ))⁻¹ *
        ∫ u in ((HeightOneSpectrum.adicCompletionIntegers F v).units : Set (v.adicCompletion F)ˣ),
          a (Multiplicative.ofAdd (z * adeleProjection F {v}
            (IdeleGroup.ofAdicCompletion (𝓞 F) F v (π * u)⁻¹ : 𝔸[F])))
          ∂(finiteLocalMultiplicativeTamagawaMeasure F v) := by
  classical
  letI : MeasurableSpace (v.adicCompletion F)ˣ := borel _
  haveI : BorelSpace (v.adicCompletion F)ˣ := ⟨rfl⟩
  haveI := finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure (F := F) v
  let μ := finiteLocalMultiplicativeTamagawaMeasure F v
  let U : Set (v.adicCompletion F)ˣ :=
    ((HeightOneSpectrum.adicCompletionIntegers F v).units : Set (v.adicCompletion F)ˣ)
  have hUc : IsCompact U := Submonoid.units_isCompact
    (isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v))
  let T : (v.adicCompletion F)ˣ → SAdeleRing F {v} := fun u ↦
    adeleProjection F {v} (IdeleGroup.ofAdicCompletion (𝓞 F) F v (π * u)⁻¹ : 𝔸[F])
  have hT : Continuous T :=
    (continuous_fst.prodMk (continuous_pi fun w ↦
      (RestrictedProduct.continuous_eval w.val).comp continuous_snd)).comp
      (globalThetaPrincipalValue_sobolevBound_formula_contU v π)
  have hint (b : SchwartzBruhat (Multiplicative (SAdeleRing F {v}))) (z : SAdeleRing F {v}) :
      IntegrableOn (fun u ↦ b (Multiplicative.ofAdd (z * T u))) U μ :=
    ((schwartzBruhat_continuous b).comp (continuous_ofAdd.comp
      (continuous_const.mul hT))).continuousOn.integrableOn_compact hUc
  let P : SchwartzBruhat (Multiplicative (SAdeleRing F {v})) → Prop := fun b ↦
    ∀ z : SAdeleRing F {v},
      sAdelePrincipalValue F (Finset.Subset.refl {v}) b (Multiplicative.ofAdd z) =
        b (Multiplicative.ofAdd z) - ((μ.real U)⁻¹ : ℝ) *
          ∫ u in U, b (Multiplicative.ofAdd (z * T u)) ∂μ
  have hzero : P 0 := fun z ↦ by
    rw [map_zero]
    change (0 : ℂ) = 0 - _ * ∫ u in U, (0 : ℂ) ∂μ
    simp
  have hadd (b₁ b₂ : SchwartzBruhat (Multiplicative (SAdeleRing F {v}))) (h₁ : P b₁)
      (h₂ : P b₂) : P (b₁ + b₂) := fun z ↦ by
    rw [map_add]
    change sAdelePrincipalValue F (Finset.Subset.refl {v}) b₁ (Multiplicative.ofAdd z) +
        sAdelePrincipalValue F (Finset.Subset.refl {v}) b₂ (Multiplicative.ofAdd z) =
      (b₁ (Multiplicative.ofAdd z) + b₂ (Multiplicative.ofAdd z)) - _ *
        ∫ u in U, (b₁ (Multiplicative.ofAdd (z * T u)) + b₂ (Multiplicative.ofAdd (z * T u))) ∂μ
    rw [integral_add (hint b₁ z) (hint b₂ z), h₁ z, h₂ z]
    ring
  have hsmul (r : ℂ) (b : SchwartzBruhat (Multiplicative (SAdeleRing F {v}))) (h : P b) :
      P (r • b) := fun z ↦ by
    rw [map_smul]
    change r * sAdelePrincipalValue F (Finset.Subset.refl {v}) b (Multiplicative.ofAdd z) =
      r * b (Multiplicative.ofAdd z) - _ * ∫ u in U, r * b (Multiplicative.ofAdd (z * T u)) ∂μ
    rw [integral_const_mul, h z]
    ring
  let w₀ : ({v} : Finset V) := ⟨v, Finset.mem_singleton_self v⟩
  have hw₀ (w : ({v} : Finset V)) : w = w₀ := Subtype.ext (Finset.mem_singleton.mp w.2)
  have hspec := (sAdeleSchwartz_inductiveTensor_equiv F {v}).choose_spec
  have hpure (f : SchwartzBruhat (Multiplicative (InfiniteAdeleRing F)))
      (g : ∀ w : ({v} : Finset V), SchwartzBruhat (Multiplicative (w.val.adicCompletion F))) :
      P ((sAdeleSchwartz_inductiveTensor_equiv F {v}).choose
        (f ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g w))) := fun z ↦ by
    have ht := sAdelePrincipalValue_tmul (F := F) (Finset.Subset.refl ({v} : Finset V)) f g
    refine (congrArg (fun b : SchwartzBruhat (Multiplicative (SAdeleRing F {v})) ↦
      b (Multiplicative.ofAdd z)) ht).trans ?_
    have hprod (x : SAdeleRing F {v}) (h : ∀ w : ({v} : Finset V),
        SchwartzBruhat (Multiplicative (w.val.adicCompletion F))) :
        ∏ w : ({v} : Finset V), h w (Multiplicative.ofAdd (x.2 w)) =
          h w₀ (Multiplicative.ofAdd (x.2 w₀)) :=
      Fintype.prod_eq_single w₀ fun w hw ↦ absurd (hw₀ w) hw
    have e1 := hspec f (fun w ↦ if w.val ∈ ({v} : Finset V) then
      finitePlacePrincipalValue w.val (g w) else g w) z
    have e2 := hspec f g z
    have e3 : ∫ u in U, (sAdeleSchwartz_inductiveTensor_equiv F {v}).choose
        (f ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g w)) (Multiplicative.ofAdd (z * T u)) ∂μ =
        ∫ u in U, f (Multiplicative.ofAdd (z * T u).1) *
          ∏ w : ({v} : Finset V), g w (Multiplicative.ofAdd ((z * T u).2 w)) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun u ↦ hspec f g (z * T u))
    refine e1.trans (Eq.trans ?_ (congrArg₂ (fun x y : ℂ ↦ x - (((μ.real U)⁻¹ : ℝ) : ℂ) * y)
      e2 e3).symm)
    dsimp only
    rw [hprod, hprod]
    have hin (u : (v.adicCompletion F)ˣ) : f (Multiplicative.ofAdd (z * T u).1) *
        ∏ w : ({v} : Finset V), g w (Multiplicative.ofAdd ((z * T u).2 w)) =
        f (Multiplicative.ofAdd z.1) * g w₀ (Multiplicative.ofAdd
          ((z.2 w₀ : v.adicCompletion F) * (((π * u)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F))) := by
      obtain ⟨h1, h2⟩ := globalThetaPrincipalValue_sobolevBound_formula_proj v ((π * u)⁻¹) z
      rw [hprod]
      exact congrArg₂ (· * ·) (congrArg (fun x ↦ f (Multiplicative.ofAdd x)) h1)
        (congrArg (fun x ↦ g w₀ (Multiplicative.ofAdd x)) h2)
    have hpv := finitePlacePrincipalValue_spec v π hπ (g w₀) (Multiplicative.ofAdd (z.2 w₀))
    unfold finitePlacePrincipalValueFun at hpv
    have hu (u : (v.adicCompletion F)ˣ) :
        (z.2 w₀ : v.adicCompletion F) * (((π * u)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
          (↑u⁻¹ : v.adicCompletion F) * ((↑π⁻¹ : v.adicCompletion F) *
            (Multiplicative.ofAdd (z.2 w₀ : v.adicCompletion F)).toAdd) := by
      rw [mul_inv_rev, Units.val_mul]
      change _ = _ * (_ * (z.2 w₀ : v.adicCompletion F))
      ring
    show f (Multiplicative.ofAdd z.1) *
        (if (w₀ : V) ∈ ({v} : Finset V) then finitePlacePrincipalValue (w₀ : V) (g w₀) else g w₀)
          (Multiplicative.ofAdd (z.2 w₀)) =
      f (Multiplicative.ofAdd z.1) * g w₀ (Multiplicative.ofAdd (z.2 w₀)) -
        (((μ.real U)⁻¹ : ℝ) : ℂ) * ∫ u in U, f (Multiplicative.ofAdd (z * T u).1) *
          ∏ w : ({v} : Finset V), g w (Multiplicative.ofAdd ((z * T u).2 w)) ∂μ
    rw [if_pos (Finset.mem_singleton_self v), integral_congr_ae (Filter.Eventually.of_forall hin),
      integral_const_mul]
    change f (Multiplicative.ofAdd z.1) *
        finitePlacePrincipalValue v (g w₀) (Multiplicative.ofAdd (z.2 w₀)) = _
    rw [hpv]
    simp only [hu, Complex.ofReal_inv]
    ring
  exact globalThetaPrincipalValue_sobolevBound_formula_ind
    (sAdeleSchwartz_inductiveTensor_equiv F {v}).choose P hzero hadd hsmul hpure a z

/-- A predicate on the target of an inductive tensor product of two factors holds everywhere
once it holds on pure tensors and is closed under zero, addition and scalars. -/
private theorem globalThetaPrincipalValue_sobolevBound_formula_ind₂ {E G N : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup G] [Module ℂ G] [TopologicalSpace G]
    [AddCommGroup N] [Module ℂ N] [TopologicalSpace N]
    (e : InductiveTensor E G ≃L[ℂ] N) (P : N → Prop)
    (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (hpure : ∀ (a : E) (b : G), P (e (a ⊗ₜ[ℂ] b))) (x : N) : P x := by
  have key : ∀ y : TensorProduct ℂ E G, P (e y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => exact (congrArg P (map_zero e)).mpr h0
    | tmul a b => exact hpure a b
    | add y z hy hz => exact (congrArg P (map_add e y z)).mpr (hadd _ _ hy hz)
  exact (congrArg P (e.apply_symm_apply x)).mp (key (e.symm x))

/-- Multiplying an adele by the idele inserted at `v` does not change its coordinates off `{v}`. -/
private theorem globalThetaPrincipalValue_sobolevBound_formula_tail (v : V)
    (y : (v.adicCompletion F)ˣ) (x : 𝔸[F]) :
    finiteAdeleTailProjection F {v}
        (x * (IdeleGroup.ofAdicCompletion (𝓞 F) F v y : 𝔸[F])).2 =
      finiteAdeleTailProjection F {v} x.2 := by
  classical
  apply RestrictedProduct.ext
  intro w
  rw [finiteAdeleTailProjection_apply, finiteAdeleTailProjection_apply]
  have hw : (w.val : V) ≠ v := fun h ↦ w.2 (by rw [h]; exact Finset.mem_singleton_self v)
  change x.2 w.val * Pi.mulSingle v (y : v.adicCompletion F) w.val = x.2 w.val
  rw [Pi.mulSingle_eq_of_ne hw, mul_one]

/-- Paper: Definition 5.3.1.4(2) and Lemma 5.3.1.3, p. 241. On adelic tests, the principal value
at the single place `v` is the identity minus the normalized unit average of the translates by
the idele `(π u)⁻¹` at `v`. -/
private theorem globalThetaPrincipalValue_sobolevBound_formula_global (v : V)
    (π : (v.adicCompletion F)ˣ) (hπ : Valued.v.IsUniformizer π.val)
    (f : SchwartzBruhat (Multiplicative 𝔸[F])) (x : 𝔸[F]) :
    adelePrincipalValue F {v} f (Multiplicative.ofAdd x) =
      f (Multiplicative.ofAdd x) - ((finiteLocalMultiplicativeTamagawaMeasure F v).real
          ((HeightOneSpectrum.adicCompletionIntegers F v).units : Set (v.adicCompletion F)ˣ))⁻¹ *
        ∫ u in ((HeightOneSpectrum.adicCompletionIntegers F v).units : Set (v.adicCompletion F)ˣ),
          f (Multiplicative.ofAdd (x * (IdeleGroup.ofAdicCompletion (𝓞 F) F v (π * u)⁻¹ : 𝔸[F])))
          ∂(finiteLocalMultiplicativeTamagawaMeasure F v) := by
  classical
  letI : MeasurableSpace (v.adicCompletion F)ˣ := borel _
  haveI : BorelSpace (v.adicCompletion F)ˣ := ⟨rfl⟩
  haveI := finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure (F := F) v
  let μ := finiteLocalMultiplicativeTamagawaMeasure F v
  let U : Set (v.adicCompletion F)ˣ :=
    ((HeightOneSpectrum.adicCompletionIntegers F v).units : Set (v.adicCompletion F)ˣ)
  have hUc : IsCompact U := Submonoid.units_isCompact
    (isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v))
  let E : (v.adicCompletion F)ˣ → 𝔸[F] := fun u ↦
    (IdeleGroup.ofAdicCompletion (𝓞 F) F v (π * u)⁻¹ : 𝔸[F])
  have hE : Continuous E := globalThetaPrincipalValue_sobolevBound_formula_contU v π
  have hint (b : SchwartzBruhat (Multiplicative 𝔸[F])) (x : 𝔸[F]) :
      IntegrableOn (fun u ↦ b (Multiplicative.ofAdd (x * E u))) U μ :=
    ((schwartzBruhat_continuous b).comp (continuous_ofAdd.comp
      (continuous_const.mul hE))).continuousOn.integrableOn_compact hUc
  let P : SchwartzBruhat (Multiplicative 𝔸[F]) → Prop := fun b ↦ ∀ x : 𝔸[F],
    adelePrincipalValue F {v} b (Multiplicative.ofAdd x) =
      b (Multiplicative.ofAdd x) - ((μ.real U)⁻¹ : ℝ) *
        ∫ u in U, b (Multiplicative.ofAdd (x * E u)) ∂μ
  have hzero : P 0 := fun x ↦ by
    rw [map_zero]
    change (0 : ℂ) = 0 - _ * ∫ u in U, (0 : ℂ) ∂μ
    simp
  have hadd (b₁ b₂ : SchwartzBruhat (Multiplicative 𝔸[F])) (h₁ : P b₁) (h₂ : P b₂) :
      P (b₁ + b₂) := fun x ↦ by
    rw [map_add]
    change adelePrincipalValue F {v} b₁ (Multiplicative.ofAdd x) +
        adelePrincipalValue F {v} b₂ (Multiplicative.ofAdd x) =
      (b₁ (Multiplicative.ofAdd x) + b₂ (Multiplicative.ofAdd x)) - _ *
        ∫ u in U, (b₁ (Multiplicative.ofAdd (x * E u)) + b₂ (Multiplicative.ofAdd (x * E u))) ∂μ
    rw [integral_add (hint b₁ x) (hint b₂ x), h₁ x, h₂ x]
    ring
  have hspec := (sAdeleTailSchwartz_inductiveTensor_equiv F {v}).choose_spec
  have hpure (a : SchwartzBruhat (Multiplicative (SAdeleRing F {v})))
      (b : SchwartzBruhat (Multiplicative (FiniteAdeleTail F {v}))) :
      P ((sAdeleTailSchwartz_inductiveTensor_equiv F {v}).choose (a ⊗ₜ[ℂ] b)) := fun x ↦ by
    have ht := adelePrincipalValue_tmul (F := F) (Finset.Subset.refl ({v} : Finset V)) a b
    refine (congrArg (fun c : SchwartzBruhat (Multiplicative 𝔸[F]) ↦
      c (Multiplicative.ofAdd x)) ht).trans ?_
    have e1 := hspec (sAdelePrincipalValue F (Finset.Subset.refl ({v} : Finset V)) a) b x
    have e2 := hspec a b x
    have e3 : ∫ u in U, (sAdeleTailSchwartz_inductiveTensor_equiv F {v}).choose (a ⊗ₜ[ℂ] b)
        (Multiplicative.ofAdd (x * E u)) ∂μ =
        ∫ u in U, a (Multiplicative.ofAdd (adeleProjection F {v} (x * E u))) *
          b (Multiplicative.ofAdd (finiteAdeleTailProjection F {v} (x * E u).2)) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun u ↦ hspec a b (x * E u))
    refine e1.trans (Eq.trans ?_ (congrArg₂ (fun y z : ℂ ↦ y - (((μ.real U)⁻¹ : ℝ) : ℂ) * z)
      e2 e3).symm)
    dsimp only
    have hin (u : (v.adicCompletion F)ˣ) :
        a (Multiplicative.ofAdd (adeleProjection F {v} (x * E u))) *
          b (Multiplicative.ofAdd (finiteAdeleTailProjection F {v} (x * E u).2)) =
        b (Multiplicative.ofAdd (finiteAdeleTailProjection F {v} x.2)) *
          a (Multiplicative.ofAdd (adeleProjection F {v} x * adeleProjection F {v}
            (IdeleGroup.ofAdicCompletion (𝓞 F) F v (π * u)⁻¹ : 𝔸[F]))) := by
      rw [globalThetaPrincipalValue_sobolevBound_formula_tail v ((π * u)⁻¹) x, map_mul, mul_comm]
    rw [integral_congr_ae (Filter.Eventually.of_forall hin), integral_const_mul,
      globalThetaPrincipalValue_sobolevBound_formula_local v π hπ a (adeleProjection F {v} x)]
    ring
  exact globalThetaPrincipalValue_sobolevBound_formula_ind₂
    (sAdeleTailSchwartz_inductiveTensor_equiv F {v}).choose P hzero hadd hpure f x

/-- Paper: Definition 5.3.1.2 and Lemma 5.3.1.3, p. 241, for the proof of
Proposition 11.2.0.1(1), p. 484. The principal value at one finite place `v`, on theta
functions: theta of `PV_v f` is theta of `f` minus the normalized average over the local
integer units `u` of its translates by the idele class of `(π u)⁻¹` at `v`. On a test this is
`finitePlacePrincipalValue_spec` at `v`. The sum over `Fˣ` and the integral over the compact
unit group may be exchanged because the theta series converges absolutely and locally
uniformly. -/
private theorem globalThetaPrincipalValue_sobolevBound_formula (v : V)
    (π : (v.adicCompletion F)ˣ) (_hπ : Valued.v.IsUniformizer π.val) (f : ℬ₀) (g : C𝔽) :
    adelicTheta (adelePrincipalValue F {v} f.val) g =
      adelicTheta f.val g - ((finiteLocalMultiplicativeTamagawaMeasure F v).real
          ((HeightOneSpectrum.adicCompletionIntegers F v).units : Set (v.adicCompletion F)ˣ))⁻¹ *
        ∫ u in ((HeightOneSpectrum.adicCompletionIntegers F v).units : Set (v.adicCompletion F)ˣ),
          adelicTheta f.val (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v (π * u)⁻¹ * g)
          ∂(finiteLocalMultiplicativeTamagawaMeasure F v) := by
  classical
  letI : MeasurableSpace (v.adicCompletion F)ˣ := borel _
  haveI : BorelSpace (v.adicCompletion F)ˣ := ⟨rfl⟩
  haveI := finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure (F := F) v
  haveI : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  haveI : Countable Fˣ := (show Function.Injective (Units.val : Fˣ → F) from
    fun _ _ h ↦ Units.ext h).countable
  let μ := finiteLocalMultiplicativeTamagawaMeasure F v
  let U : Set (v.adicCompletion F)ˣ :=
    ((HeightOneSpectrum.adicCompletionIntegers F v).units : Set (v.adicCompletion F)ˣ)
  have hUo : IsOpen U := Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)
  have hUc : IsCompact U := Submonoid.units_isCompact
    (isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v))
  have hUfin : μ U ≠ ⊤ := hUc.measure_ne_top
  let ι : (v.adicCompletion F)ˣ → IdeleGroup (𝓞 F) F := fun u ↦
    IdeleGroup.ofAdicCompletion (𝓞 F) F v (π * u)⁻¹
  have hι : Continuous ι :=
    (Continuous.units_map _ (globalThetaPrincipalValue_sobolevBound_formula_cont v)).comp
      ((continuous_const.mul continuous_id).inv)
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective g
  have hθ (φ : SchwartzBruhat (Multiplicative 𝔸[F])) (h : IdeleGroup (𝓞 F) F) :
      adelicTheta φ (QuotientGroup.mk h) = ∑' ξ : Fˣ, φ (Multiplicative.ofAdd
        ((IdeleGroup.unitEmbedding (𝓞 F) F ξ * h : IdeleGroup (𝓞 F) F) : 𝔸[F])) :=
    (ideleThetaSum_schwartzBruhat φ h).symm
  let x : Fˣ → 𝔸[F] := fun ξ ↦
    ((IdeleGroup.unitEmbedding (𝓞 F) F ξ * g₀ : IdeleGroup (𝓞 F) F) : 𝔸[F])
  let Φ : Fˣ → (v.adicCompletion F)ˣ → ℂ := fun ξ u ↦
    f.val (Multiplicative.ofAdd (x ξ * (ι u : 𝔸[F])))
  have hcls (u : (v.adicCompletion F)ˣ) :
      adelicTheta f.val (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v (π * u)⁻¹ *
        QuotientGroup.mk g₀) = ∑' ξ : Fˣ, Φ ξ u := by
    refine (hθ f.val (ι u * g₀)).trans (tsum_congr fun ξ ↦ congrArg f.val
      (congrArg Multiplicative.ofAdd ?_))
    change ((IdeleGroup.unitEmbedding (𝓞 F) F ξ : 𝔸[F]) * ((ι u : 𝔸[F]) * (g₀ : 𝔸[F]))) =
      (IdeleGroup.unitEmbedding (𝓞 F) F ξ : 𝔸[F]) * (g₀ : 𝔸[F]) * (ι u : 𝔸[F])
    ring
  let K : Set (IdeleGroup (𝓞 F) F × 𝔸[F]) := (fun u ↦ (ι u * g₀, (0 : 𝔸[F]))) '' U
  have hK : IsCompact K := hUc.image ((hι.mul continuous_const).prodMk continuous_const)
  have hsu := adelicAverage_summableUniformlyOn f.val K hK
  have hterm (ξ : Fˣ) (u : (v.adicCompletion F)ˣ) :
      ‖f.val (Multiplicative.ofAdd ((ι u * g₀).val * (algebraMap F 𝔸[F] (ξ : F) + 0)))‖ =
        ‖Φ ξ u‖ := by
    refine congrArg (fun y ↦ ‖f.val (Multiplicative.ofAdd y)‖) ?_
    change ((ι u : 𝔸[F]) * (g₀ : 𝔸[F])) * (algebraMap F 𝔸[F] (ξ : F) + 0) =
      (algebraMap F 𝔸[F] (ξ : F) * (g₀ : 𝔸[F])) * (ι u : 𝔸[F])
    ring
  have hcontS : ContinuousOn (fun p : IdeleGroup (𝓞 F) F × 𝔸[F] ↦ ∑' ξ : Fˣ,
      ‖f.val (Multiplicative.ofAdd (p.1.val * (algebraMap F 𝔸[F] (ξ : F) + p.2)))‖) K := by
    refine (hasSumUniformlyOn_iff_tendstoUniformlyOn.mp hsu.hasSumUniformlyOn).continuousOn
      (Filter.Eventually.of_forall fun I ↦
        (continuous_finsetSum I fun ξ _ ↦ ?_).continuousOn).frequently
    exact ((schwartzBruhat_continuous f.val).comp (continuous_ofAdd.comp
      ((Units.continuous_val.comp continuous_fst).mul
        (continuous_const.add continuous_snd)))).norm
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hcontS
  have hbound (u : (v.adicCompletion F)ˣ) (hu : u ∈ U) :
      Summable (fun ξ ↦ ‖Φ ξ u‖) ∧ ∑' ξ, ‖Φ ξ u‖ ≤ B := by
    have hp : (ι u * g₀, (0 : 𝔸[F])) ∈ K := ⟨u, hu, rfl⟩
    have hs := (hsu.summable hp).congr (fun ξ ↦ hterm ξ u)
    refine ⟨hs, ?_⟩
    have h1 := hB _ hp
    rw [Real.norm_of_nonneg (tsum_nonneg fun _ ↦ norm_nonneg _)] at h1
    exact (tsum_congr fun ξ ↦ (hterm ξ u).symm).trans_le h1
  have hΦc (ξ : Fˣ) : Continuous (Φ ξ) :=
    (schwartzBruhat_continuous f.val).comp (continuous_ofAdd.comp
      (continuous_const.mul (Units.continuous_val.comp hι)))
  have hfin : ∑' ξ, ∫⁻ u in U, ‖Φ ξ u‖ₑ ∂μ ≠ ⊤ := by
    rw [← lintegral_tsum fun ξ ↦ (hΦc ξ).measurable.eNorm.aemeasurable]
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := B)) hUfin)
      ((setLIntegral_mono' hUo.measurableSet fun u hu ↦ ?_).trans_eq
        (setLIntegral_const U (ENNReal.ofReal B)))
    obtain ⟨hs, hle⟩ := hbound u hu
    simp only [← ofReal_norm]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ norm_nonneg _) hs]
    exact ENNReal.ofReal_le_ofReal hle
  have hs1 : Summable (fun ξ : Fˣ ↦ f.val (Multiplicative.ofAdd (x ξ))) := by
    refine Summable.of_norm ((((adelicAverage_summableUniformlyOn f.val {(g₀, (0 : 𝔸[F]))}
      isCompact_singleton).summable (Set.mem_singleton _))).congr fun ξ ↦ ?_)
    refine congrArg (fun y ↦ ‖f.val (Multiplicative.ofAdd y)‖) ?_
    change (g₀ : 𝔸[F]) * (algebraMap F 𝔸[F] (ξ : F) + 0) = algebraMap F 𝔸[F] (ξ : F) * (g₀ : 𝔸[F])
    ring
  have hs2 : Summable (fun ξ : Fˣ ↦ ∫ u in U, Φ ξ u ∂μ) := by
    refine Summable.of_norm_bounded (ENNReal.summable_toReal hfin) fun ξ ↦ ?_
    refine (norm_integral_le_lintegral_norm _).trans_eq ?_
    simp only [ofReal_norm]
  have hswap : ∫ u in U, ∑' ξ : Fˣ, Φ ξ u ∂μ = ∑' ξ : Fˣ, ∫ u in U, Φ ξ u ∂μ :=
    integral_tsum (fun ξ ↦ (hΦc ξ).aestronglyMeasurable) hfin
  rw [hθ, hθ, integral_congr_ae (Filter.Eventually.of_forall hcls), hswap,
    ← tsum_mul_left, ← hs1.tsum_sub (hs2.mul_left _)]
  exact tsum_congr fun ξ ↦ globalThetaPrincipalValue_sobolevBound_formula_global v π _hπ f.val (x ξ)

/-- Paper: Proposition 11.2.0.1, pp. 484–485. On the trivial norm-one isotype, the
principal value at one finite place acts on the theta function by the difference
with its uniformizer translate. -/
theorem homogeneousAdelicTheta_one_principalValue_singleton (v : V) (π : (v.adicCompletion F)ˣ)
    (hπ : Valued.v.IsUniformizer π.val) (f : ℬ₀) (g : C𝔽) :
    homogeneousAdelicTheta (1 : PontryaginDual C₁) (adelePrincipalValue F {v} f.val) g =
      homogeneousAdelicTheta 1 f.val g - homogeneousAdelicTheta 1 f.val
        ((IdeleClassGroup.ofAdicCompletion (𝓞 F) F v π)⁻¹ * g) := by
  classical
  let : MeasurableSpace (v.adicCompletion F)ˣ := borel _
  have : BorelSpace (v.adicCompletion F)ˣ := ⟨rfl⟩
  let : CompactSpace C₁ := (ideleClassGroup_finiteness F).2.1
  have : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
  have : SecondCountableTopology (v.adicCompletion F)ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let ν := normOneIdeleClassTamagawaMeasure F
  let : ν.IsHaarMeasure := (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  let μ := finiteLocalMultiplicativeTamagawaMeasure F v
  let : μ.IsHaarMeasure := finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure (F := F) v
  let U : Set (v.adicCompletion F)ˣ :=
    ((HeightOneSpectrum.adicCompletionIntegers F v).units : Set (v.adicCompletion F)ˣ)
  have hUo : IsOpen U := Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)
  have hUc : IsCompact U := Submonoid.units_isCompact
    (isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v))
  have hm : μ.real U ≠ 0 := (measureReal_ne_zero_iff hUc.measure_ne_top).mpr
    (hUo.measure_pos μ ⟨1, Submonoid.one_mem _⟩).ne'
  let a := IdeleClassGroup.ofAdicCompletion (𝓞 F) F v
  let y := (a π)⁻¹ * g
  let K (k : C₁) (u : (v.adicCompletion F)ˣ) :=
    adelicTheta f.val (a (π * u)⁻¹ * (k.val * g))
  have hK : Continuous (uncurry K) :=
    (adelicTheta f.val).continuous.comp (((continuous_ideleClass_ofAdicCompletion F v).comp
      ((continuous_const.mul continuous_snd).inv)).mul
        ((continuous_subtype_val.comp continuous_fst).mul continuous_const))
  have hInt : Integrable (uncurry K) (ν.prod (μ.restrict U)) := by
    have h := hK.continuousOn.integrableOn_compact (μ := ν.prod μ) (isCompact_univ.prod hUc)
    rwa [IntegrableOn, ← Measure.prod_restrict, Measure.restrict_univ] at h
  have hθ (b : SchwartzBruhat (Multiplicative 𝔸[F])) (x : C𝔽) :
      homogeneousAdelicTheta (1 : PontryaginDual C₁) b x =
        ∫ k : C₁, adelicTheta b (k.val * x) ∂ν := by
    change (∫ k : C₁, adelicTheta b (k.val * x) * (1 : ℂ) ∂ν) = _
    simp
  have hθi : Integrable (fun k : C₁ ↦ adelicTheta f.val (k.val * g)) ν :=
    ((adelicTheta f.val).continuous.comp (continuous_subtype_val.mul continuous_const)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hinner (u : (v.adicCompletion F)ˣ) (hu : u ∈ U) :
      ∫ k : C₁, K k u ∂ν = homogeneousAdelicTheta 1 f.val y := by
    have hun : ideleClassNorm F (a u) = 1 := by
      rw [ideleClassNorm_ofAdicCompletion]
      apply Units.ext
      apply NNReal.coe_injective
      change ‖u.val‖ = 1
      have h1 : ‖u.val‖ ≤ 1 := Valued.toNormedField.norm_le_one_iff.mpr hu.1
      have h2 : ‖(u⁻¹ : (v.adicCompletion F)ˣ).val‖ ≤ 1 := Valued.toNormedField.norm_le_one_iff.mpr hu.2
      have h3 : ‖u.val‖ * ‖(u⁻¹ : (v.adicCompletion F)ˣ).val‖ = 1 := by
        rw [← norm_mul, Units.mul_inv, norm_one]
      nlinarith [norm_nonneg u.val, norm_nonneg (u⁻¹ : (v.adicCompletion F)ˣ).val]
    let k₀ : C₁ := ⟨a u, hun⟩
    have eqk (k : C₁) : K k u = adelicTheta f.val ((k₀⁻¹ * k).val * y) := by
      dsimp only [K, k₀, y, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [map_inv a, map_mul a]
      congr 1
      simp only [mul_inv_rev]
      ac_rfl
    rw [hθ, ← integral_mul_left_eq_self (μ := ν) (fun k : C₁ ↦ adelicTheta f.val (k.val * y)) k₀⁻¹]
    exact integral_congr_ae (.of_forall eqk)
  rw [hθ, hθ f.val g]
  let b : ℂ := ((μ.real U)⁻¹ : ℝ)
  have heq (k : C₁) : adelicTheta (adelePrincipalValue F {v} f.val) (k.val * g) =
      adelicTheta f.val (k.val * g) - b * ∫ u in U, K k u ∂μ :=
    globalThetaPrincipalValue_sobolevBound_formula v π hπ f _
  simp_rw [heq]
  have hKi : Integrable (fun k : C₁ ↦ b * ∫ u in U, K k u ∂μ) ν := hInt.integral_prod_left.const_mul b
  have hswap := integral_integral_swap (f := K) hInt
  rw [integral_sub hθi hKi, integral_const_mul, hswap, setIntegral_congr_fun hUo.measurableSet hinner, setIntegral_const]
  simp [b, y, a, Complex.real_smul, hm]

/-- Cauchy–Schwarz for lower Lebesgue integrals: the square of the integral is at most the
total mass times the integral of the square. -/
private theorem globalThetaPrincipalValue_sobolevBound_average_cs {X : Type*}
    [MeasurableSpace X] (ν : Measure X) (f : X → ENNReal) (hf : AEMeasurable f ν) :
    (∫⁻ x, f x ∂ν) ^ 2 ≤ ν univ * ∫⁻ x, f x ^ 2 ∂ν := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ν Real.HolderConjugate.two_two hf
    (aemeasurable_const (b := (1 : ENNReal)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, one_mul] at h
  calc (∫⁻ x, f x ∂ν) ^ 2
      ≤ ((∫⁻ x, f x ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ) * ν univ ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ zero_le h 2
    _ = ν univ * ∫⁻ x, f x ^ 2 ∂ν := by
      rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast (ν univ ^ (1 / 2 : ℝ)),
        ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
      norm_num
      rw [mul_comm]

/-- Abstract form of the bound for the unit average: on a group with a left-invariant measure
and a weight that each translate by `τ u`, `u ∈ U`, changes by at most the factor `M`, the
normalized average of the translates has weighted L² mass at most `M` times that of the
function. -/
private theorem globalThetaPrincipalValue_sobolevBound_average_abstract
    {G X : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    [IsTopologicalGroup G] [SecondCountableTopology G]
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ] (w : G → ENNReal) (hw : Measurable w)
    (μX : Measure X) (U : Set X) (hU : MeasurableSet U) (hUfin : μX U ≠ ⊤)
    (τ : X → G) (hτ : Continuous τ) (M : ENNReal)
    (hM : ∀ u ∈ U, ∀ g, w ((τ u)⁻¹ * g) ≤ M * w g)
    (φ : G → ℂ) (hφ : Continuous φ) :
    AEStronglyMeasurable (fun g ↦ (μX.real U)⁻¹ * ∫ u in U, φ (τ u * g) ∂μX)
        (μ.withDensity w) ∧
      ∫⁻ g, ‖(μX.real U)⁻¹ * ∫ u in U, φ (τ u * g) ∂μX‖ₑ ^ 2 ∂(μ.withDensity w) ≤
        M * ∫⁻ g, ‖φ g‖ₑ ^ 2 ∂(μ.withDensity w) := by
  haveI : IsFiniteMeasure (μX.restrict U) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.mpr hUfin⟩
  set c : ℝ := μX.real U with hcdef
  have hc0 : 0 ≤ c := measureReal_nonneg
  have hcU : μX U = ENNReal.ofReal c := (ENNReal.ofReal_toReal hUfin).symm
  have hsm : StronglyMeasurable (fun p : G × X ↦ φ (τ p.2 * p.1)) :=
    (hφ.comp ((hτ.comp continuous_snd).mul continuous_fst)).stronglyMeasurable
  have hAsm : StronglyMeasurable (fun g ↦ ((c⁻¹ : ℝ) : ℂ) * ∫ u in U, φ (τ u * g) ∂μX) :=
    (hsm.integral_prod_right' (ν := μX.restrict U)).const_mul _
  refine ⟨hAsm.aestronglyMeasurable, ?_⟩
  let F : X → G → ENNReal := fun u g ↦ ‖φ (τ u * g)‖ₑ ^ 2
  have hF : Measurable (Function.uncurry F) :=
    ((hφ.comp ((hτ.comp continuous_fst).mul continuous_snd)).measurable.eNorm).pow_const 2
  -- Pointwise: the square of the average is at most the average of the squares.
  have hpt (g : G) : ‖((c⁻¹ : ℝ) : ℂ) * ∫ u in U, φ (τ u * g) ∂μX‖ₑ ^ 2 ≤
      ENNReal.ofReal c⁻¹ * ∫⁻ u in U, F u g ∂μX := by
    have h1 : ‖((c⁻¹ : ℝ) : ℂ) * ∫ u in U, φ (τ u * g) ∂μX‖ₑ ≤
        ENNReal.ofReal c⁻¹ * ∫⁻ u in U, ‖φ (τ u * g)‖ₑ ∂μX := by
      rw [eNorm_mul]
      refine mul_le_mul' (le_of_eq ?_) (eNorm_integral_le_lintegral_eNorm _)
      rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hc0)]
    have h2 := globalThetaPrincipalValue_sobolevBound_average_cs (μX.restrict U)
      (fun u ↦ ‖φ (τ u * g)‖ₑ)
      ((hφ.comp (hτ.mul continuous_const)).measurable.eNorm.aemeasurable)
    rw [Measure.restrict_apply_univ, hcU] at h2
    have h3 : ENNReal.ofReal c⁻¹ ^ 2 * ENNReal.ofReal c ≤ ENNReal.ofReal c⁻¹ := by
      rcases hc0.eq_or_lt with h | h
      · rw [← h]; simp
      · rw [← ENNReal.ofReal_pow (inv_nonneg.mpr hc0), ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
        field_simp
    calc ‖((c⁻¹ : ℝ) : ℂ) * ∫ u in U, φ (τ u * g) ∂μX‖ₑ ^ 2
        ≤ (ENNReal.ofReal c⁻¹ * ∫⁻ u in U, ‖φ (τ u * g)‖ₑ ∂μX) ^ 2 :=
          pow_le_pow_left₀ zero_le h1 2
      _ = ENNReal.ofReal c⁻¹ ^ 2 * (∫⁻ u in U, ‖φ (τ u * g)‖ₑ ∂μX) ^ 2 := mul_pow _ _ _
      _ ≤ ENNReal.ofReal c⁻¹ ^ 2 * (ENNReal.ofReal c * ∫⁻ u in U, F u g ∂μX) :=
          mul_le_mul' le_rfl h2
      _ = (ENNReal.ofReal c⁻¹ ^ 2 * ENNReal.ofReal c) * ∫⁻ u in U, F u g ∂μX := by ring
      _ ≤ ENNReal.ofReal c⁻¹ * ∫⁻ u in U, F u g ∂μX := mul_le_mul' h3 le_rfl
  -- Each translate changes the weighted mass by at most `M`.
  have htr (u : X) (hu : u ∈ U) : ∫⁻ g, w g * F u g ∂μ ≤ M * ∫⁻ g, w g * ‖φ g‖ₑ ^ 2 ∂μ := by
    have he : ∫⁻ g, w g * F u g ∂μ = ∫⁻ g, w ((τ u)⁻¹ * g) * ‖φ g‖ₑ ^ 2 ∂μ := by
      rw [← lintegral_mul_left_eq_self (fun g ↦ w ((τ u)⁻¹ * g) * ‖φ g‖ₑ ^ 2) (τ u)]
      simp only [F, inv_mul_cancel_left]
    rw [he, ← lintegral_const_mul M (f := fun g ↦ w g * ‖φ g‖ₑ ^ 2)
      (hw.mul (hφ.measurable.eNorm.pow_const 2))]
    exact lintegral_mono fun g ↦ (mul_le_mul' (hM u hu g) le_rfl).trans_eq (mul_assoc _ _ _)
  have hwm : Measurable fun g ↦ ‖((c⁻¹ : ℝ) : ℂ) * ∫ u in U, φ (τ u * g) ∂μX‖ₑ ^ 2 :=
    (hAsm.measurable.eNorm).pow_const 2
  rw [lintegral_withDensity_eq_lintegral_mul _ hw hwm,
    lintegral_withDensity_eq_lintegral_mul _ hw (hφ.measurable.eNorm.pow_const 2)]
  calc ∫⁻ g, (w * fun g ↦ ‖((c⁻¹ : ℝ) : ℂ) * ∫ u in U, φ (τ u * g) ∂μX‖ₑ ^ 2) g ∂μ
      ≤ ∫⁻ g, w g * (ENNReal.ofReal c⁻¹ * ∫⁻ u in U, F u g ∂μX) ∂μ :=
        lintegral_mono fun g ↦ mul_le_mul' le_rfl (hpt g)
    _ = ENNReal.ofReal c⁻¹ * ∫⁻ u in U, ∫⁻ g, w g * F u g ∂μ ∂μX := by
        have hm2 : Measurable (Function.uncurry fun g u ↦ w g * F u g) :=
          (hw.comp measurable_fst).mul (hF.comp measurable_swap)
        have hin (g : G) : w g * (ENNReal.ofReal c⁻¹ * ∫⁻ u in U, F u g ∂μX) =
            ENNReal.ofReal c⁻¹ * ∫⁻ u in U, w g * F u g ∂μX := by
          rw [lintegral_const_mul (w g) (f := fun u ↦ F u g)
            (hF.comp (measurable_id.prodMk measurable_const))]
          ring
        rw [lintegral_congr hin, lintegral_const_mul (ENNReal.ofReal c⁻¹)
          (f := fun g ↦ ∫⁻ u in U, w g * F u g ∂μX) hm2.lintegral_prod_right',
          lintegral_lintegral_swap (f := fun g u ↦ w g * F u g) (μ := μ) (ν := μX.restrict U)
            hm2.aemeasurable]
    _ ≤ ENNReal.ofReal c⁻¹ * ∫⁻ u in U, M * ∫⁻ g, w g * ‖φ g‖ₑ ^ 2 ∂μ ∂μX :=
        mul_le_mul' le_rfl (setLIntegral_mono' hU htr)
    _ = (ENNReal.ofReal c⁻¹ * ENNReal.ofReal c) * (M * ∫⁻ g, w g * ‖φ g‖ₑ ^ 2 ∂μ) := by
        rw [setLIntegral_const, hcU]
        ring
    _ ≤ M * ∫⁻ g, (w * fun g ↦ ‖φ g‖ₑ ^ 2) g ∂μ := by
        refine (mul_le_mul' ?_ le_rfl).trans_eq (one_mul _)
        rcases hc0.eq_or_lt with h | h
        · rw [← h]; simp
        · rw [← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ h.ne', ENNReal.ofReal_one]

/-- Paper: for the proof of Proposition 11.2.0.1(1), p. 484. The normalized average over the
local integer units at `v` of the translates by the classes of `(π u)⁻¹` is bounded on the
weighted L² space of the 0-line, uniformly on continuous square-integrable functions. Each
such translate moves the idelic norm by the fixed factor `q_v`, so it changes the Sobolev
weight `(1 + log² ‖g‖)^{s/2}` by at most a constant factor (Peetre's inequality). The bound
for the average then follows from Minkowski's integral inequality. -/
private theorem globalThetaPrincipalValue_sobolevBound_average (v : V)
    (π : (v.adicCompletion F)ˣ) {s : ℝ} (_hs : 0 ≤ s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : C𝔽 → ℂ, Continuous φ →
      MemLp φ 2 ((μ𝔽).withDensity fun g ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (logNorm g))) →
      let A : C𝔽 → ℂ := fun g ↦ ((finiteLocalMultiplicativeTamagawaMeasure F v).real
          ((HeightOneSpectrum.adicCompletionIntegers F v).units : Set (v.adicCompletion F)ˣ))⁻¹ *
        ∫ u in ((HeightOneSpectrum.adicCompletionIntegers F v).units : Set (v.adicCompletion F)ˣ),
          φ (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v (π * u)⁻¹ * g)
          ∂(finiteLocalMultiplicativeTamagawaMeasure F v)
      MemLp A 2 ((μ𝔽).withDensity fun g ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (logNorm g))) ∧
        eLpNorm A 2 ((μ𝔽).withDensity fun g ↦
            ENNReal.ofReal (intervalSobolevDensity 0 0 s (logNorm g))) ≤
          ENNReal.ofReal C * eLpNorm φ 2 ((μ𝔽).withDensity fun g ↦
            ENNReal.ofReal (intervalSobolevDensity 0 0 s (logNorm g))) := by
  letI : MeasurableSpace (v.adicCompletion F)ˣ := borel _
  haveI : BorelSpace (v.adicCompletion F)ˣ := ⟨rfl⟩
  let U : Set (v.adicCompletion F)ˣ :=
    ((HeightOneSpectrum.adicCompletionIntegers F v).units : Set (v.adicCompletion F)ˣ)
  have hUo : IsOpen U := Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)
  have hUc : IsCompact U := Submonoid.units_isCompact
    (isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v))
  haveI := finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure (F := F) v
  have hUfin : finiteLocalMultiplicativeTamagawaMeasure F v U ≠ ⊤ := hUc.measure_ne_top
  let τ : (v.adicCompletion F)ˣ → C𝔽 := fun u ↦ IdeleClassGroup.ofAdicCompletion (𝓞 F) F v (π * u)⁻¹
  have hτ : Continuous τ :=
    (continuous_ideleClass_ofAdicCompletion F v).comp ((continuous_const.mul continuous_id).inv)
  let w : C𝔽 → ENNReal := fun g ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (logNorm g))
  have hw : Measurable w := by
    refine (Measurable.ennreal_ofReal ?_)
    simp only [intervalSobolevDensity, mul_zero, zero_mul, Real.exp_zero, max_self, one_mul]
    have hlog : Continuous (fun g : C𝔽 ↦ logNorm g) :=
      Real.continuousOn_log.comp_continuous
        (NNReal.continuous_coe.comp (Units.continuous_val.comp (m𝔽).continuous))
        fun _ ↦ (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
    exact ((continuous_const.add (hlog.pow 2)).rpow_const fun g ↦ Or.inl (by
      change (1 : ℝ) + (logNorm g) ^ 2 ≠ 0
      positivity)).measurable
  let c₀ : ℝ := Real.log ‖(π : v.adicCompletion F)‖
  let M : ℝ := (2 * (1 + c₀ ^ 2)) ^ (s / 2)
  have hnormu (u : (v.adicCompletion F)ˣ) (hu : u ∈ U) : ‖(u : v.adicCompletion F)‖ = 1 := by
    have h1 : ‖(u : v.adicCompletion F)‖ ≤ 1 :=
      (Valued.toNormedField.norm_le_one_iff).mpr hu.1
    have h2 : ‖((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)‖ ≤ 1 :=
      (Valued.toNormedField.norm_le_one_iff).mpr hu.2
    have h3 : ‖(u : v.adicCompletion F)‖ * ‖((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)‖ = 1 := by
      rw [← norm_mul, Units.mul_inv, norm_one]
    nlinarith [norm_nonneg (u : v.adicCompletion F),
      norm_nonneg ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)]
  have hπ0 : 0 < ‖(π : v.adicCompletion F)‖ := norm_pos_iff.mpr π.ne_zero
  have hM : ∀ u ∈ U, ∀ g, w ((τ u)⁻¹ * g) ≤ ENNReal.ofReal M * w g := by
    intro u hu g
    have hlog : logNorm ((τ u)⁻¹ * g) = c₀ + logNorm g := by
      have hn : (((ideleClassNorm F ((τ u)⁻¹ * g)).val : ℝ≥0) : ℝ) =
          ‖(π : v.adicCompletion F)‖ * (((ideleClassNorm F g).val : ℝ≥0) : ℝ) := by
        simp only [τ, map_mul, map_inv, inv_inv, ideleClassNorm_ofAdicCompletion, Units.val_mul,
          NNReal.coe_mul]
        change ‖(π : v.adicCompletion F)‖ * ‖(u : v.adicCompletion F)‖ * _ = _
        rw [hnormu u hu, mul_one]
      change Real.log _ = Real.log ‖(π : v.adicCompletion F)‖ + Real.log _
      rw [hn, Real.log_mul hπ0.ne' (NNReal.coe_pos.mpr (Units.zero_lt _)).ne']
    simp only [w, hlog, intervalSobolevDensity, mul_zero, zero_mul, Real.exp_zero, max_self,
      one_mul]
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    refine Real.rpow_le_rpow (by positivity) ?_ (by linarith)
    nlinarith [sq_nonneg (c₀ - logNorm g), sq_nonneg (c₀ * logNorm g)]
  refine ⟨Real.sqrt M, Real.sqrt_nonneg _, fun φ hφ hφm ↦ ?_⟩
  intro A
  obtain ⟨hAsm, hAle⟩ := globalThetaPrincipalValue_sobolevBound_average_abstract μ𝔽 w hw
    (finiteLocalMultiplicativeTamagawaMeasure F v) U hUo.measurableSet hUfin τ hτ
    (ENNReal.ofReal M) hM φ hφ
  have hrpow (f : C𝔽 → ℂ) (hf : AEStronglyMeasurable f ((μ𝔽).withDensity w)) :
      eLpNorm f 2 ((μ𝔽).withDensity w) =
      (∫⁻ g, ‖f g‖ₑ ^ 2 ∂((μ𝔽).withDensity w)) ^ (1 / 2 : ℝ) := by
    rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top hf]
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  have hbound : eLpNorm (fun g ↦ ((finiteLocalMultiplicativeTamagawaMeasure F v).real U)⁻¹ *
        ∫ u in U, φ (τ u * g) ∂(finiteLocalMultiplicativeTamagawaMeasure F v)) 2
        ((μ𝔽).withDensity w) ≤ ENNReal.ofReal (Real.sqrt M) * eLpNorm φ 2 ((μ𝔽).withDensity w) := by
    rw [hrpow _ hAsm, hrpow _ hφm.aestronglyMeasurable, Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg (by positivity)
      (by norm_num), ← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    exact ENNReal.rpow_le_rpow hAle (by norm_num)
  exact ⟨hbound.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hφm), hbound⟩

/-- The principal value at a single finite place is bounded in the norm of the unweighted
global theta completion: by the formula on theta functions and the bound for the unit average. -/
private theorem globalThetaPrincipalValue_sobolevBound_single (v : V) {s : ℝ} (hs : 0 ≤ s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℬ₀,
      ‖j(0, hs) (theta(pvTest({v}, f)))‖ ≤ C * ‖j(0, hs) (theta(f))‖ := by
  obtain ⟨π₀, hπ₀⟩ := (Valued.v : Valuation (v.adicCompletion F)
    (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
  let π : (v.adicCompletion F)ˣ := Units.mk0 π₀ hπ₀.ne_zero
  obtain ⟨C, hC, hA⟩ := globalThetaPrincipalValue_sobolevBound_average v π hs
  -- The norm of an unweighted theta class is the weighted L² norm of its theta function.
  have hθ (h : ℬ₀) : ((j(0, hs) (theta(h)) : W(s)) : C𝔽 → ℂ) =ᵐ[(μ𝔽).withDensity fun g ↦
      ENNReal.ofReal (intervalSobolevDensity 0 0 s (logNorm g))] (adelicTheta h.val : C𝔽 → ℂ) :=
    (withDensity_absolutelyContinuous _ _).ae_le
      (((existsUnique_globalThetaSobolevEmbedding (F := F) 0 0 0 s hI hs).exists.choose_spec.2
        h).trans (Filter.EventuallyEq.of_eq (modulationWeight_zero m𝔽 _)))
  have hmem (h : ℬ₀) : MemLp (adelicTheta h.val : C𝔽 → ℂ) 2 ((μ𝔽).withDensity fun g ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (logNorm g))) :=
    (Lp.memLp _).ae_eq (hθ h)
  have hnorm (h : ℬ₀) : ‖j(0, hs) (theta(h))‖ =
      (eLpNorm (adelicTheta h.val : C𝔽 → ℂ) 2 ((μ𝔽).withDensity fun g ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (logNorm g)))).toReal :=
    (Lp.norm_def _).trans (congrArg ENNReal.toReal (eLpNorm_congr_ae (hθ h)))
  refine ⟨1 + C, by linarith, fun f ↦ ?_⟩
  have hA' := hA _ (adelicTheta f.val).continuous (hmem f)
  let A : C𝔽 → ℂ := fun g ↦ ((finiteLocalMultiplicativeTamagawaMeasure F v).real
          ((HeightOneSpectrum.adicCompletionIntegers F v).units : Set (v.adicCompletion F)ˣ))⁻¹ *
        ∫ u in ((HeightOneSpectrum.adicCompletionIntegers F v).units : Set (v.adicCompletion F)ˣ),
          adelicTheta f.val (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v (π * u)⁻¹ * g)
          ∂(finiteLocalMultiplicativeTamagawaMeasure F v)
  have hAm : MemLp A 2 ((μ𝔽).withDensity fun g ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (logNorm g))) := hA'.1
  have hAle : eLpNorm A 2 ((μ𝔽).withDensity fun g ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (logNorm g))) ≤
      ENNReal.ofReal C * eLpNorm (adelicTheta f.val : C𝔽 → ℂ) 2 ((μ𝔽).withDensity fun g ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (logNorm g))) := hA'.2
  have hpv : (adelicTheta (pvTest({v}, f)).val : C𝔽 → ℂ) =
      fun g ↦ adelicTheta f.val g - A g :=
    funext fun g ↦ globalThetaPrincipalValue_sobolevBound_formula v π hπ₀ f g
  have hfin := (hmem f).eLpNorm_ne_top
  have hle : eLpNorm (fun g ↦ adelicTheta f.val g - A g) 2 ((μ𝔽).withDensity fun g ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (logNorm g))) ≤
      eLpNorm (adelicTheta f.val : C𝔽 → ℂ) 2 ((μ𝔽).withDensity fun g ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (logNorm g))) +
        ENNReal.ofReal C * eLpNorm (adelicTheta f.val : C𝔽 → ℂ) 2 ((μ𝔽).withDensity fun g ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (logNorm g))) :=
    (eLpNorm_sub_le (by norm_num : (1 : ENNReal) ≤ 2)).trans
      (add_le_add le_rfl hAle)
  have hfin' : ENNReal.ofReal C * eLpNorm (adelicTheta f.val : C𝔽 → ℂ) 2 ((μ𝔽).withDensity fun g ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (logNorm g))) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
  have hreal : (eLpNorm (adelicTheta f.val : C𝔽 → ℂ) 2 ((μ𝔽).withDensity fun g ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (logNorm g))) +
      ENNReal.ofReal C * eLpNorm (adelicTheta f.val : C𝔽 → ℂ) 2 ((μ𝔽).withDensity fun g ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (logNorm g)))).toReal =
      (1 + C) * (eLpNorm (adelicTheta f.val : C𝔽 → ℂ) 2 ((μ𝔽).withDensity fun g ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (logNorm g)))).toReal := by
    rw [ENNReal.toReal_add hfin hfin', ENNReal.toReal_mul, ENNReal.toReal_ofReal hC]
    ring
  refine (hnorm _).trans_le ?_
  refine (congrArg (fun φ : C𝔽 → ℂ ↦ (eLpNorm φ 2 ((μ𝔽).withDensity fun g ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (logNorm g)))).toReal) hpv).trans_le ?_
  refine (ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin, hfin'⟩) hle).trans_eq ?_
  exact hreal.trans (congrArg ((1 + C) * ·) (hnorm f).symm)

/-- Paper: Proposition 11.2.0.1(1), p. 484. The principal-value operator
is bounded in the norm induced on unweighted theta classes.
Deviation: The operator uses finite places as in (11.2.0.2) and the global
norm (10.1.1.6), since (10.1.1.5) is S-local. -/
theorem globalThetaPrincipalValue_sobolevBound (S : Finset V) {s : ℝ} (hs : 0 ≤ s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℬ₀,
      ‖j(0, hs) (theta(pvTest(S, f)))‖ ≤ C * ‖j(0, hs) (theta(f))‖ := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨1, zero_le_one, fun f ↦ ?_⟩
    have h : pvTest(∅, f) = f := by
      refine Subtype.ext ?_
      change adelePrincipalValue F ∅ f.val = f.val
      rw [sLocalUncutCarving_empty_PV]
      rfl
    rw [h, one_mul]
  | insert v T hvT ih =>
    obtain ⟨K₁, hK₁, h₁⟩ := ih
    have hsingle := globalThetaPrincipalValue_sobolevBound_single (F := F) v hs
    have hK₂ := hsingle.choose_spec.1
    have h₂ := hsingle.choose_spec.2
    refine ⟨K₁ * hsingle.choose, mul_nonneg hK₁ hK₂, fun f ↦ ?_⟩
    have hcomp : pvTest(insert v T, f) = pvTest(T, pvTest({v}, f)) := by
      refine Subtype.ext ?_
      change adelePrincipalValue F (insert v T) f.val =
        adelePrincipalValue F T (adelePrincipalValue F {v} f.val)
      rw [sLocalCutoffCarving_antitone_PV (Finset.subset_insert v T),
        Finset.insert_sdiff_cancel hvT]
      rfl
    calc ‖j(0, hs) (theta(pvTest(insert v T, f)))‖
        = ‖j(0, hs) (theta(pvTest(T, pvTest({v}, f))))‖ :=
          congrArg (fun h : ℬ₀ ↦ ‖j(0, hs) (theta(h))‖) hcomp
      _ ≤ K₁ * ‖j(0, hs) (theta(pvTest({v}, f)))‖ := h₁ _
      _ ≤ K₁ * (hsingle.choose * ‖j(0, hs) (theta(f))‖) := mul_le_mul_of_nonneg_left (h₂ f) hK₁
      _ = K₁ * hsingle.choose * ‖j(0, hs) (theta(f))‖ := (mul_assoc _ _ _).symm

/-- The polar-free theta test classes as a linear map into the global completion. -/
private def globalThetaSobolevTestClass (a : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    ℬ₀ →ₗ[ℂ] H(a, hs) :=
  (j(a, hs)).toLinearMap.comp (Submodule.mkQ
    ((LinearMap.ker (adelicThetaLinearMap F)).comap (adelePolarSubspace F).subtype))

/-- Abstract form of the last step of the weighted single-place bound: if `A` has L² norm at
most `C` times that of `φ`, then `φ - K A` has L² norm at most `1 + K C` times that of `φ`. -/
private theorem globalThetaPrincipalValue_sobolevBound_sub_abstract {X : Type*}
    [MeasurableSpace X] (ν : Measure X) (φ A : X → ℂ) {K C : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hφ : MemLp φ 2 ν) (hA : eLpNorm A 2 ν ≤ ENNReal.ofReal C * eLpNorm φ 2 ν) :
    (eLpNorm (fun g ↦ φ g - (K : ℂ) * A g) 2 ν).toReal ≤ (1 + K * C) * (eLpNorm φ 2 ν).toReal := by
  have hle : eLpNorm (fun g ↦ φ g - (K : ℂ) * A g) 2 ν ≤
      ENNReal.ofReal (1 + K * C) * eLpNorm φ 2 ν := by
    calc eLpNorm (fun g ↦ φ g - (K : ℂ) * A g) 2 ν
        ≤ eLpNorm φ 2 ν + eLpNorm (K • A) 2 ν :=
          eLpNorm_sub_le (by norm_num : (1 : ENNReal) ≤ 2)
      _ = eLpNorm φ 2 ν + ENNReal.ofReal K * eLpNorm A 2 ν := by
          rw [eLpNorm_const_smul, Real.eNorm_of_nonneg hK]
      _ ≤ eLpNorm φ 2 ν + ENNReal.ofReal K * (ENNReal.ofReal C * eLpNorm φ 2 ν) := by
          gcongr
      _ = ENNReal.ofReal (1 + K * C) * eLpNorm φ 2 ν := by
          rw [ENNReal.ofReal_add zero_le_one (mul_nonneg hK hC), ENNReal.ofReal_mul hK,
            ENNReal.ofReal_one, add_mul, one_mul, mul_assoc]
  refine (ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hφ.eLpNorm_ne_top)
    hle).trans_eq ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]

/-- Abstract form of the descent to the test classes: a linear map bounded by a constant
times another descends to a continuous linear map on the range of the other. -/
private theorem globalThetaPrincipalValue_clm_onTests_abstract {E W : Type*} [AddCommGroup E]
    [Module ℂ E] [NormedAddCommGroup W] [NormedSpace ℂ W] {H : Submodule ℂ W}
    (ι T : E →ₗ[ℂ] H) (C : ℝ) (hC : ∀ f, ‖T f‖ ≤ C * ‖ι f‖) :
    ∃ g : LinearMap.range ι →L[ℂ] H, ∀ f, g ⟨ι f, LinearMap.mem_range_self _ f⟩ = T f := by
  have hker : LinearMap.ker ι ≤ LinearMap.ker T := fun f hf ↦ by
    have h1 : ‖T f‖ ≤ 0 := (hC f).trans_eq (by rw [LinearMap.mem_ker.mp hf, norm_zero, mul_zero])
    exact LinearMap.mem_ker.mpr (norm_le_zero_iff.mp h1)
  let L : LinearMap.range ι →ₗ[ℂ] H :=
    (LinearMap.ker ι).liftQ T hker ∘ₗ (LinearMap.quotKerEquivRange ι).symm.toLinearMap
  have hL (f : E) : L ⟨ι f, LinearMap.mem_range_self _ f⟩ = T f := by
    simp only [L, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  refine ⟨L.mkContinuous C fun x ↦ ?_, fun f ↦ ?_⟩
  · obtain ⟨f, hf⟩ := LinearMap.mem_range.mp x.2
    have hx : x = ⟨ι f, LinearMap.mem_range_self _ f⟩ := Subtype.ext hf.symm
    calc ‖L x‖ = ‖T f‖ := by rw [hx, hL f]
      _ ≤ C * ‖ι f‖ := hC f
      _ = C * ‖x‖ := by rw [hf, Submodule.norm_coe]
  · rw [LinearMap.mkContinuous_apply]
    exact hL f

/-- The principal value at a single finite place is bounded in the norm of the weighted
global theta completion. Each unit translate in the average moves the idelic norm by the
fixed factor `‖π‖⁻¹`, so weighting by `‖g‖ ^ a` turns the average of the theta function into
`‖π‖ ^ a` times the average of the weighted theta function, which the unweighted estimate
bounds. -/
private theorem globalThetaPrincipalValue_sobolevBound_single_weighted_at (v : V)
    (π : (v.adicCompletion F)ˣ) (hπ₀ : Valued.v.IsUniformizer π.val) (a : ℝ)
    {s : ℝ} (hs : 0 ≤ s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℬ₀,
      ‖j(a, hs) (theta(pvTest({v}, f)))‖ ≤ C * ‖j(a, hs) (theta(f))‖ := by
  let _ : MeasurableSpace (v.adicCompletion F)ˣ := borel _
  have _ : BorelSpace (v.adicCompletion F)ˣ := ⟨rfl⟩
  obtain ⟨C, hC, hA⟩ := globalThetaPrincipalValue_sobolevBound_average v π hs
  let ν := (μ𝔽).withDensity fun g ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (logNorm g))
  let U : Set (v.adicCompletion F)ˣ :=
    ((HeightOneSpectrum.adicCompletionIntegers F v).units : Set (v.adicCompletion F)ˣ)
  let τ : (v.adicCompletion F)ˣ → C𝔽 := fun u ↦ IdeleClassGroup.ofAdicCompletion (𝓞 F) F v (π * u)⁻¹
  let w : C𝔽 → ℝ := fun g ↦ (((ideleClassNorm F g).val : ℝ≥0) : ℝ) ^ a
  let φ : ℬ₀ → C𝔽 → ℂ := fun h g ↦ (w g : ℂ) * adelicTheta h.val g
  let K : ℝ := ‖(π : v.adicCompletion F)‖ ^ a
  have hπ0 : 0 < ‖(π : v.adicCompletion F)‖ := norm_pos_iff.mpr π.ne_zero
  have hK : 0 ≤ K := Real.rpow_nonneg hπ0.le a
  have hw : Continuous w :=
    (NNReal.continuous_coe.comp (Units.continuous_val.comp (m𝔽).continuous)).rpow_const
      fun g ↦ Or.inl (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
  have hφc (h : ℬ₀) : Continuous (φ h) :=
    (Complex.continuous_ofReal.comp hw).mul (adelicTheta h.val).continuous
  -- The norm of a weighted theta class is the weighted L² norm of its weighted theta function.
  have hθ (h : ℬ₀) : ((j(a, hs) (theta(h)) : W(s)) : C𝔽 → ℂ) =ᵐ[ν] φ h :=
    (withDensity_absolutelyContinuous _ _).ae_le
      ((existsUnique_globalThetaSobolevEmbedding (F := F) a 0 0 s hI hs).exists.choose_spec.2 h)
  have hmem (h : ℬ₀) : MemLp (φ h) 2 ν := (Lp.memLp _).ae_eq (hθ h)
  have hnorm (h : ℬ₀) : ‖j(a, hs) (theta(h))‖ = (eLpNorm (φ h) 2 ν).toReal :=
    (Lp.norm_def _).trans (congrArg ENNReal.toReal (eLpNorm_congr_ae (hθ h)))
  -- A unit translate divides the idelic norm by `‖π‖`.
  have hnormu (u : (v.adicCompletion F)ˣ) (hu : u ∈ U) : ‖(u : v.adicCompletion F)‖ = 1 := by
    have h1 : ‖(u : v.adicCompletion F)‖ ≤ 1 :=
      (Valued.toNormedField.norm_le_one_iff).mpr hu.1
    have h2 : ‖((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)‖ ≤ 1 :=
      (Valued.toNormedField.norm_le_one_iff).mpr hu.2
    have h3 : ‖(u : v.adicCompletion F)‖ *
        ‖((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)‖ = 1 := by
      rw [← norm_mul, Units.mul_inv, norm_one]
    nlinarith [norm_nonneg (u : v.adicCompletion F),
      norm_nonneg ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)]
  have hwτ (u : (v.adicCompletion F)ˣ) (hu : u ∈ U) (g : C𝔽) : K * w (τ u * g) = w g := by
    have hn' (h : C𝔽) : (((ideleClassNorm F ((τ u)⁻¹ * h)).val : ℝ≥0) : ℝ) =
        ‖(π : v.adicCompletion F)‖ * (((ideleClassNorm F h).val : ℝ≥0) : ℝ) := by
      simp only [τ, map_mul, map_inv, inv_inv, ideleClassNorm_ofAdicCompletion, Units.val_mul,
        NNReal.coe_mul]
      change ‖(π : v.adicCompletion F)‖ * ‖(u : v.adicCompletion F)‖ * _ = _
      rw [hnormu u hu, mul_one]
    have hn := hn' (τ u * g)
    rw [inv_mul_cancel_left] at hn
    simp only [w, K, hn]
    rw [Real.mul_rpow hπ0.le (NNReal.coe_nonneg _)]
  refine ⟨1 + K * C, by positivity, fun f ↦ ?_⟩
  have hA' := hA _ (hφc f) (hmem f)
  let A : C𝔽 → ℂ := fun g ↦ ((finiteLocalMultiplicativeTamagawaMeasure F v).real U)⁻¹ *
    ∫ u in U, φ f (τ u * g) ∂(finiteLocalMultiplicativeTamagawaMeasure F v)
  have hAm : MemLp A 2 ν := hA'.1
  have hAle : eLpNorm A 2 ν ≤ ENNReal.ofReal C * eLpNorm (φ f) 2 ν := hA'.2
  -- The weighted principal value is the weighted theta function minus `K` times the average.
  have hpv : φ (pvTest({v}, f)) = fun g ↦ φ f g - (K : ℂ) * A g := by
    funext g
    have hint : ∫ u in U, φ f (τ u * g) ∂(finiteLocalMultiplicativeTamagawaMeasure F v) =
        ((K⁻¹ * w g : ℝ) : ℂ) * ∫ u in U, adelicTheta f.val (τ u * g)
          ∂(finiteLocalMultiplicativeTamagawaMeasure F v) := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun
        (Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)).measurableSet fun u hu ↦ ?_
      have hK0 : K ≠ 0 := (Real.rpow_pos_of_pos hπ0 a).ne'
      have hw' : w (τ u * g) = K⁻¹ * w g := by
        rw [← hwτ u hu g, ← mul_assoc, inv_mul_cancel₀ hK0, one_mul]
      simp only [φ, hw']
    simp only [φ, A]
    rw [globalThetaPrincipalValue_sobolevBound_formula v π hπ₀ f g, hint]
    have hK0 : (K : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hπ0 a).ne'
    change _ = _ - _ * (_ * (((K⁻¹ * w g : ℝ) : ℂ) * ∫ u in U, adelicTheta f.val (τ u * g)
      ∂(finiteLocalMultiplicativeTamagawaMeasure F v)))
    push_cast
    rw [mul_sub]
    congr 1
    field_simp
    rfl
  rw [hnorm, hnorm, hpv]
  exact globalThetaPrincipalValue_sobolevBound_sub_abstract ν (φ f) A hK hC (hmem f) hAle

/-- The principal value at a single finite place is bounded in the norm of the weighted
global theta completion, at some uniformizer of that place. -/
private theorem globalThetaPrincipalValue_sobolevBound_single_weighted (v : V) (a : ℝ)
    {s : ℝ} (hs : 0 ≤ s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℬ₀,
      ‖j(a, hs) (theta(pvTest({v}, f)))‖ ≤ C * ‖j(a, hs) (theta(f))‖ := by
  obtain ⟨π₀, hπ₀⟩ := (Valued.v : Valuation (v.adicCompletion F)
    (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
  exact globalThetaPrincipalValue_sobolevBound_single_weighted_at v (Units.mk0 π₀ hπ₀.ne_zero)
    hπ₀ a hs

/-- The principal value at a finite set of places is bounded in the norm of the weighted
global theta completion: compose the single-place bounds. -/
private theorem globalThetaPrincipalValue_sobolevBound_weighted (S : Finset V) (a : ℝ)
    {s : ℝ} (hs : 0 ≤ s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℬ₀,
      ‖j(a, hs) (theta(pvTest(S, f)))‖ ≤ C * ‖j(a, hs) (theta(f))‖ := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨1, zero_le_one, fun f ↦ ?_⟩
    have h : pvTest(∅, f) = f := by
      refine Subtype.ext ?_
      change adelePrincipalValue F ∅ f.val = f.val
      rw [sLocalUncutCarving_empty_PV]
      rfl
    rw [h, one_mul]
  | insert v T hvT ih =>
    obtain ⟨K₁, hK₁, h₁⟩ := ih
    have hsingle := globalThetaPrincipalValue_sobolevBound_single_weighted (F := F) v a hs
    have hK₂ := hsingle.choose_spec.1
    have h₂ := hsingle.choose_spec.2
    refine ⟨K₁ * hsingle.choose, mul_nonneg hK₁ hK₂, fun f ↦ ?_⟩
    have hcomp : pvTest(insert v T, f) = pvTest(T, pvTest({v}, f)) := by
      refine Subtype.ext ?_
      change adelePrincipalValue F (insert v T) f.val =
        adelePrincipalValue F T (adelePrincipalValue F {v} f.val)
      rw [sLocalCutoffCarving_antitone_PV (Finset.subset_insert v T),
        Finset.insert_sdiff_cancel hvT]
      rfl
    calc ‖j(a, hs) (theta(pvTest(insert v T, f)))‖
        = ‖j(a, hs) (theta(pvTest(T, pvTest({v}, f))))‖ :=
          congrArg (fun h : ℬ₀ ↦ ‖j(a, hs) (theta(h))‖) hcomp
      _ ≤ K₁ * ‖j(a, hs) (theta(pvTest({v}, f)))‖ := h₁ _
      _ ≤ K₁ * (hsingle.choose * ‖j(a, hs) (theta(f))‖) := mul_le_mul_of_nonneg_left (h₂ f) hK₁
      _ = K₁ * hsingle.choose * ‖j(a, hs) (theta(f))‖ := (mul_assoc _ _ _).symm

/-- Paper: Proposition 11.2.0.1(2), pp. 484–485. The principal value is bounded and well
defined on the polar-free theta test classes of the completion: on their span it is a
continuous linear map sending a test class to the class of its principal value. -/
private theorem globalThetaPrincipalValue_clm_onTests (S : Finset V) (a : ℝ) {s : ℝ}
    (hs : 0 ≤ s) :
    ∃ g : (LinearMap.range (globalThetaSobolevTestClass (F := F) a hs)) →L[ℂ] H(a, hs),
      ∀ f : ℬ₀,
        g ⟨globalThetaSobolevTestClass (F := F) a hs f, LinearMap.mem_range_self _ f⟩ =
          j(a, hs) (theta(pvTest(S, f))) := by
  -- Well defined: the principal value kills the kernel of the test class map, because the
  -- theta class of a test depends only on its theta function. Bounded: the estimates of
  -- `globalThetaPrincipalValue_sobolevBound` and of its local form bound the norm of the
  -- principal value by that of the test class.
  have hbound := globalThetaPrincipalValue_sobolevBound_weighted (F := F) S a hs
  have hCb := hbound.choose_spec.2
  let C := hbound.choose
  let Q := (LinearMap.ker (adelicThetaLinearMap F)).comap (adelePolarSubspace F).subtype
  let pv : ℬ₀ →ₗ[ℂ] ℬ₀ := (adelePrincipalValue F S).restrict
    fun f hf ↦ adelePrincipalValue_mem_polarSubspace S ⟨f, hf⟩
  let T : ℬ₀ →ₗ[ℂ] H(a, hs) := (j(a, hs)).toLinearMap ∘ₗ Q.mkQ ∘ₗ pv
  have hT (f : ℬ₀) : T f = j(a, hs) (theta(pvTest(S, f))) := rfl
  have hι (f : ℬ₀) : globalThetaSobolevTestClass (F := F) a hs f = j(a, hs) (theta(f)) := rfl
  have hg := globalThetaPrincipalValue_clm_onTests_abstract
    (globalThetaSobolevTestClass (F := F) a hs) T C fun f ↦ by rw [hT f, hι f]; exact hCb f
  exact ⟨hg.choose, fun f ↦ (hg.choose_spec f).trans (hT f)⟩

/-- Paper: Proposition 11.2.0.1(2) and (11.2.0.4), pp. 484–485. A continuous linear map on
the test classes of the completion which agrees with the principal value extends uniquely to
the whole completion, the test classes being dense in it. -/
private theorem globalThetaPrincipalValue_extension (S : Finset V) (a : ℝ) {s : ℝ}
    (hs : 0 ≤ s)
    (g : (LinearMap.range (globalThetaSobolevTestClass (F := F) a hs)) →L[ℂ] H(a, hs))
    (hg : ∀ f : ℬ₀,
      g ⟨globalThetaSobolevTestClass (F := F) a hs f, LinearMap.mem_range_self _ f⟩ =
        j(a, hs) (theta(pvTest(S, f)))) :
    ∃! P : H(a, hs) →L[ℂ] H(a, hs), ∀ f : ℬ₀,
      P (j(a, hs) (theta(f))) = j(a, hs) (theta(pvTest(S, f))) := by
  let T := globalThetaSobolevTestClass (F := F) a hs
  let R := LinearMap.range T
  have htc (f : ℬ₀) : T f = j(a, hs) (theta(f)) := by
    change globalThetaSobolevTestClass (F := F) a hs f = _
    rw [globalThetaSobolevTestClass, LinearMap.comp_apply, Submodule.mkQ_apply]
    rfl
  have hT : DenseRange T :=
    (globalThetaSobolev_dense (F := F) a hI hs).comp (Submodule.mkQ_surjective _).denseRange
      (globalThetaSobolevInclusion F a hI hs).continuous
  have hR : DenseRange R.subtypeL :=
    hT.mono fun y hy ↦ by
      obtain ⟨f, hf⟩ := hy
      exact ⟨⟨y, f, hf⟩, rfl⟩
  have hu : IsUniformInducing R.subtypeL := isUniformEmbedding_subtype_val.isUniformInducing
  have h₀ (f : ℬ₀) : g.extend R.subtypeL (T f) = j(a, hs) (theta(pvTest(S, f))) :=
    (g.extend_eq hR hu ⟨T f, LinearMap.mem_range_self _ f⟩).trans (hg f)
  refine ⟨g.extend R.subtypeL, fun f ↦ ?_, fun P hP ↦ ?_⟩
  · exact (congrArg (g.extend R.subtypeL) (htc f)).symm.trans (h₀ f)
  refine ContinuousLinearMap.coeFn_injective
    (hT.equalizer P.continuous (g.extend R.subtypeL).continuous (funext fun f ↦ ?_))
  exact (congrArg P (htc f)).trans ((hP f).trans (h₀ f).symm)

/-- Paper: Proposition 11.2.0.1(2) and (11.2.0.4), pp. 484–485.
The principal value has a unique bounded extension to the global theta completion.
Deviation: Continuity, without closed range, is stated here for every
nonnegative degree and every norm twist as in the paragraph before the proposition. -/
theorem existsUnique_globalThetaSobolevPrincipalValue (S : Finset V) (a : ℝ)
    {s : ℝ} (hs : 0 ≤ s) :
    ∃! P : H(a, hs) →L[ℂ] H(a, hs), ∀ f : ℬ₀,
      P (j(a, hs) (theta(f))) = j(a, hs) (theta(pvTest(S, f))) := by
  obtain ⟨g, hg⟩ := globalThetaPrincipalValue_clm_onTests (F := F) S a hs
  exact globalThetaPrincipalValue_extension S a hs g hg

variable (F) in
/-- Paper: (11.2.0.4), p. 484. The completed principal-value map is the
continuous extension of the operator on adelic tests. -/
def globalThetaSobolevPrincipalValue (S : Finset V) (a : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    H(a, hs) →L[ℂ] H(a, hs) :=
  (existsUnique_globalThetaSobolevPrincipalValue S a hs).exists.choose

local notation "P(" S ", " a ", " hs ")" => globalThetaSobolevPrincipalValue F S a hs

/-- Paper: (11.2.0.4), p. 484. The extended operator agrees with its test formula
on each polar-free theta class. -/
theorem globalThetaSobolevPrincipalValue_apply (S : Finset V) (a : ℝ) {s : ℝ}
    (hs : 0 ≤ s) (f : ℬ₀) :
    P(S, a, hs) (j(a, hs) (theta(f))) = j(a, hs) (theta(pvTest(S, f))) :=
  (existsUnique_globalThetaSobolevPrincipalValue S a hs).exists.choose_spec f

/-- An integrable nonnegative density cannot scale under translation by a
nontrivial factor. Even with factor one it vanishes if that translation
strictly decreases a bounded measurable function. -/
private theorem globalThetaPrincipalValue_invariant_mass {G : Type*} [Group G]
    [MeasurableSpace G] [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant]
    (p : G) (v b : G → ℝ) (hv : Integrable v μ) (hv₀ : ∀ x, 0 ≤ v x)
    (hb : Measurable b) (M : ℝ) (hM : ∀ x, ‖b x‖ ≤ M) (hlt : ∀ x, b (p * x) < b x)
    (c : ℝ) (he : v =ᵐ[μ] fun x ↦ c * v (p⁻¹ * x)) : v =ᵐ[μ] 0 := by
  by_cases hzero : ∫ x, v x ∂μ = 0
  · exact (integral_eq_zero_iff_of_nonneg hv₀ hv).mp hzero
  have hc : c = 1 := by
    have h := integral_congr_ae he
    rw [integral_const_mul, integral_mul_left_eq_self] at h
    exact (mul_eq_left₀ hzero).mp (by simpa [mul_comm] using h.symm)
  have hinv : v =ᵐ[μ] fun x ↦ v (p⁻¹ * x) := by simpa [hc] using he
  have hi (d : G → ℝ) (hd : Measurable d) (hbd : ∀ x, ‖d x‖ ≤ M) :
      Integrable (fun x ↦ d x * v x) μ :=
    hv.bdd_mul hd.aestronglyMeasurable (.of_forall hbd)
  have h := integral_mul_left_eq_self (μ := μ) (fun x ↦ b (p * x) * v x) p⁻¹
  have heq : ∫ x, b (p * x) * v x ∂μ = ∫ x, b x * v x ∂μ := by
    refine h.symm.trans (integral_congr_ae ?_)
    filter_upwards [hinv] with x hx
    simp only [mul_inv_cancel_left, ← hx]
  have hlt' := (integral_eq_iff_of_ae_le
    (hi _ (hb.comp (measurable_const_mul p)) (fun x ↦ hM _)) (hi b hb hM)
    (.of_forall fun x ↦ mul_le_mul_of_nonneg_right (hlt x).le (hv₀ x))).mp heq
  filter_upwards [hlt'] with x hx
  exact (mul_eq_mul_right_iff.mp hx).resolve_left (hlt x).ne

/-- A uniformizer translation has no nonzero eigenvector in the positive
Sobolev space. Its squared modulus is integrable for Haar measure, and
the bounded function arctan of the norm strictly decreases under translation. -/
private theorem globalThetaPrincipalValue_translation_eigen {s : ℝ} (hs : 0 ≤ s)
    (p : C𝔽) (hp : ((m𝔽 p).val : ℝ) < 1) (c : ℂ) (w : W(s))
    (hw : w = c • ρ(hs) p w) : w = 0 := by
  let ν := intervalSobolevMeasure μ𝔽 logNorm 0 0 s
  have hμ : μ𝔽 ≤ ν := by
    calc μ𝔽 = (μ𝔽).withDensity 1 := MeasureTheory.withDensity_one.symm
         _ ≤ ν := withDensity_mono (.of_forall fun g ↦ by
           change 1 ≤ ENNReal.ofReal (intervalSobolevDensity 0 0 s (logNorm g))
           rw [ENNReal.one_le_ofReal]
           simpa [intervalSobolevDensity] using Real.one_le_rpow
             (le_add_of_nonneg_right (sq_nonneg (logNorm g))) (by linarith : 0 ≤ s / 2))
  have hrep : (w : C𝔽 → ℂ) =ᵐ[μ𝔽] fun x ↦ c * w (p⁻¹ * x) := by
    have h := hμ.absolutelyContinuous.ae_eq (Lp.coeFn_smul c (ρ(hs) p w))
    have ht := hardySobolevTranslation_apply μ𝔽 m𝔽 0 0 s hI hs p w
    calc (w : C𝔽 → ℂ) =ᵐ[μ𝔽] ((c • ρ(hs) p w : W(s)) : C𝔽 → ℂ) :=
           Filter.EventuallyEq.of_eq (congrArg (fun t : W(s) ↦ (t : C𝔽 → ℂ)) hw)
         _ =ᵐ[μ𝔽] _ := h.trans (ht.fun_comp (c * ·))
  let m (x : C𝔽) : ℝ := (m𝔽 x).val
  have hm (x : C𝔽) : 0 < m x := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hmc : Continuous m :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp (m𝔽).continuous)
  have hb (x : C𝔽) : ‖Real.arctan (m x)‖ ≤ Real.pi / 2 := by
    rw [Real.norm_of_nonneg (Real.arctan_nonneg.mpr (hm x).le)]
    exact (Real.arctan_lt_pi_div_two _).le
  have hlt (x : C𝔽) : Real.arctan (m (p * x)) < Real.arctan (m x) := by
    apply Real.arctan_strictMono
    change ((m𝔽 (p * x)).val : ℝ) < _
    rw [map_mul, Units.val_mul, NNReal.coe_mul]
    exact mul_lt_of_lt_one_left (hm x) hp
  have hmem : MemLp (w : C𝔽 → ℂ) 2 μ𝔽 := (Lp.memLp w).mono_measure hμ
  have hz := globalThetaPrincipalValue_invariant_mass μ𝔽 p (fun x ↦ ‖w x‖ ^ 2)
    (fun x ↦ Real.arctan (m x)) ((memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).mp hmem)
    (fun x ↦ sq_nonneg _) (Real.continuous_arctan.comp hmc).measurable _ hb hlt (‖c‖ ^ 2)
    (hrep.fun_comp (fun z ↦ ‖z‖ ^ 2) |>.trans (.of_forall fun x ↦ by simp [mul_pow]))
  apply Lp.ext
  refine ((withDensity_absolutelyContinuous μ𝔽 _).ae_eq ?_).trans (Lp.coeFn_zero ..).symm
  filter_upwards [hz] with x hx
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hx)

/-- A translate of the compact-unit average has square equal to its
uniformizer translate, since the first average is invariant under the units. -/
private theorem globalThetaPrincipalValue_average_twice {U G Y : Type*} [CommGroup U]
    [MeasurableSpace U] [MeasurableMul U] [CommGroup G] (μ : Measure U) [μ.IsMulLeftInvariant]
    (K : Subgroup U) (hK : MeasurableSet (K : Set U)) (hm : μ.real K ≠ 0)
    (ι : U →* G) (π : U) (θ : Y → G → ℂ) (A : Y → Y)
    (hA : ∀ f x, θ (A f) x = ((μ.real K)⁻¹ : ℝ) *
      ∫ k in (K : Set U), θ f (ι ((π * k)⁻¹) * x) ∂μ) (f : Y) (x : G) :
    θ (A (A f)) x = θ (A f) ((ι π)⁻¹ * x) := by
  let y := (ι π)⁻¹ * x
  let ψ (t : U) := θ f (ι ((π * t)⁻¹) * y)
  have hinv (k : U) (hk : k ∈ K) : θ (A f) (ι ((π * k)⁻¹) * x) = θ (A f) y := by
    rw [hA, hA]
    congr 1
    have heq (t : U) : θ f (ι ((π * t)⁻¹) * (ι ((π * k)⁻¹) * x)) = ψ (k * t) := by
      dsimp only [ψ, y]
      congr 1
      simp only [map_inv, map_mul, mul_inv_rev]
      simp only [mul_comm, mul_left_comm, mul_assoc]
    simp_rw [heq]
    -- Restrict Haar invariance to K as in finitePlacePrincipalValue_spec_setIntegral_mul_left.
    rw [← integral_indicator hK, ← integral_indicator hK,
      ← integral_mul_left_eq_self ((K : Set U).indicator ψ) k]
    apply integral_congr_ae (.of_forall fun t ↦ ?_)
    by_cases ht : t ∈ K
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem (K.mul_mem hk ht)]
    · rw [Set.indicator_of_notMem ht,
        Set.indicator_of_notMem (fun h ↦ ht ((K.mul_mem_cancel_left hk).mp h))]
  rw [hA, setIntegral_congr_fun hK hinv, setIntegral_const, Complex.real_smul, ← mul_assoc,
    Complex.ofReal_inv, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hm), one_mul]

/-- Weighting a translated test by the norm to the power a contributes the
scalar |p|ᵃ in front of its Sobolev translation. -/
private theorem globalThetaPrincipalValue_weighted_translate (a : ℝ) {s : ℝ} (hs : 0 ≤ s)
    (p : C𝔽) (φ ψ : C𝔽 → ℂ) (u w : W(s))
    (hu : (u : C𝔽 → ℂ) =ᵐ[μ𝔽] modulationWeight m𝔽 a φ)
    (hw : (w : C𝔽 → ℂ) =ᵐ[μ𝔽] modulationWeight m𝔽 a ψ)
    (hφ : ∀ x, φ x = ψ (p⁻¹ * x)) :
    u = ((((m𝔽 p).val : ℝ) ^ a : ℝ) : ℂ) • ρ(hs) p w := by
  apply Lp.ext
  refine ((withDensity_absolutelyContinuous μ𝔽 _).ae_eq ?_).trans (Lp.coeFn_smul ..).symm
  have ht := (hardySobolevTranslation_apply μ𝔽 m𝔽 0 0 s hI hs p w).trans
    ((measurePreserving_mul_left μ𝔽 p⁻¹).quasiMeasurePreserving.ae_eq_comp hw)
  filter_upwards [hu, ht] with x hx hy
  rw [hx]
  change _ = _ * ((ρ(hs) p w : W(s)) x)
  rw [hy]
  change ((((m𝔽 x).val : ℝ) ^ a : ℝ) : ℂ) * φ x =
    _ * (((((m𝔽 (p⁻¹ * x)).val : ℝ) ^ a : ℝ) : ℂ) * ψ (p⁻¹ * x))
  rw [hφ x, ← mul_assoc, ← Complex.ofReal_mul, ← Real.mul_rpow (NNReal.coe_nonneg _)
    (NNReal.coe_nonneg _), ← NNReal.coe_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel_left]

/-- Extend the identity T² = RT for T = 1 - P from dense tests. Every
vector killed by P is then a fixed point of R. -/
private theorem globalThetaPrincipalValue_injective_of_dense {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X] (P R : X →L[ℂ] X)
    (D : Y → X) (hd : DenseRange D) (A : Y → Y)
    (hA : ∀ f, D f - P (D f) = D (A f)) (hR : ∀ f, D (A (A f)) = R (D (A f)))
    (hfix : ∀ w, w = R w → w = 0) : Injective P := by
  let T := ContinuousLinearMap.id ℂ X - P
  have hT (f : Y) : T (D f) = D (A f) := hA f
  have h := hd.equalizer (T.continuous.comp T.continuous) (R.continuous.comp T.continuous)
    (funext fun f ↦ (congrArg T (hT f)).trans
      ((hT (A f)).trans ((hR f).trans (congrArg R (hT f)).symm)))
  apply (injective_iff_map_eq_zero P).mpr
  intro w hw
  have he : T w = w := sub_eq_self.mpr hw
  apply hfix
  simpa only [Function.comp_apply, he] using congrFun h w

/-- On dense tests, the complementary operator to a singleton PV is a
translated average. Its square identity reduces the kernel question to
the absence of uniformizer-translation eigenvectors. -/
private theorem globalThetaPrincipalValue_injective_single (v : V) (a : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    Injective (P({v}, a, hs)) := by
  obtain ⟨π₀, hπ⟩ := (Valued.v : Valuation (v.adicCompletion F)
    (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
  let π : (v.adicCompletion F)ˣ := Units.mk0 (π₀ : v.adicCompletion F) hπ.ne_zero
  let ι := IdeleClassGroup.ofAdicCompletion (𝓞 F) F v
  let p := ι π
  let c : ℂ := (((m𝔽 p).val : ℝ) ^ a : ℝ)
  have hp : ((m𝔽 p).val : ℝ) < 1 := by
    change ((ideleClassNorm F (ι π)).val : ℝ) < 1
    rw [ideleClassNorm_ofAdicCompletion]
    change ‖(π₀ : v.adicCompletion F)‖ < 1
    rw [norm_uniformizer_adicCompletion v _ hπ]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v)
  let μ := finiteLocalMultiplicativeTamagawaMeasure F v
  let : MeasurableSpace (v.adicCompletion F)ˣ := borel _
  let : BorelSpace (v.adicCompletion F)ˣ := ⟨rfl⟩
  let : μ.IsHaarMeasure := finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure (F := F) v
  let K : Subgroup (v.adicCompletion F)ˣ := (HeightOneSpectrum.adicCompletionIntegers F v).units
  have hKo : IsOpen (K : Set (v.adicCompletion F)ˣ) :=
    Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)
  have hKc : IsCompact (K : Set (v.adicCompletion F)ˣ) := Submonoid.units_isCompact
    (isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v))
  have hm : μ.real K ≠ 0 := (measureReal_ne_zero_iff hKc.measure_ne_top).mpr
    (hKo.measure_pos μ ⟨1, K.one_mem⟩).ne'
  let A (f : ℬ₀) := f - pvTest({v}, f)
  let θ (f : ℬ₀) := (adelicTheta f.val : C𝔽 → ℂ)
  have hθ (f : ℬ₀) (x : C𝔽) : θ (A f) x = ((μ.real K)⁻¹ : ℝ) *
      ∫ k in (K : Set (v.adicCompletion F)ˣ), θ f (ι ((π * k)⁻¹) * x) ∂μ := by
    have hsub := congrArg (fun h : C(C𝔽, ℂ) ↦ h x)
      (map_sub (adelicThetaLinearMap F) f.val (pvTest({v}, f)).val)
    exact hsub.trans (sub_eq_iff_eq_add.mpr (by
      have h := globalThetaPrincipalValue_sobolevBound_formula v π hπ f x
      change _ = _ + adelicTheta (adelePrincipalValue F {v} f.val) x
      rw [h]
      abel))
  let D := globalThetaSobolevTestClass (F := F) a hs
  have hd : DenseRange D := (globalThetaSobolev_dense (F := F) a hI hs).comp
    (Submodule.mkQ_surjective _).denseRange (j(a, hs)).continuous
  let R := (exists_globalThetaSobolevAction (F := F) a hI hs).choose
  have hR (w : H(a, hs)) : (R p w).val = ρ(hs) p w.val :=
    (exists_globalThetaSobolevAction (F := F) a hI hs).choose_spec.1 p w
  have hrep (f : ℬ₀) : ((D f).val : C𝔽 → ℂ) =ᵐ[μ𝔽] modulationWeight m𝔽 a (θ f) :=
    (existsUnique_globalThetaSobolevEmbedding (F := F) a 0 0 s hI hs).exists.choose_spec.2 f
  refine globalThetaPrincipalValue_injective_of_dense (P({v}, a, hs)) (c • R p) D hd A
    (fun f ↦ ?_) (fun f ↦ Subtype.ext ?_) (fun w hw ↦ Subtype.ext ?_)
  · exact (congrArg (D f - ·) (globalThetaSobolevPrincipalValue_apply {v} a hs f)).trans
      (map_sub D f (pvTest({v}, f))).symm
  · change (D (A (A f))).val = c • (R p (D (A f))).val
    rw [hR]
    exact globalThetaPrincipalValue_weighted_translate a hs p _ _ _ _ (hrep _) (hrep _)
      (globalThetaPrincipalValue_average_twice μ K hKo.measurableSet hm ι π θ A hθ f)
  · apply globalThetaPrincipalValue_translation_eigen hs p hp c
    exact (congrArg Subtype.val hw).trans (congrArg (c • ·) (hR w))

/-- Paper: Lead-in to (11.2.0.3), p. 484. The extended principal value is injective.
Deviation: The inverse on its range can be discontinuous. -/
theorem globalThetaSobolevPrincipalValue_injective (S : Finset V) (a : ℝ) {s : ℝ}
    (hs : 0 ≤ s) : Injective (P(S, a, hs)) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have he : ∀ f : ℬ₀, pvTest(∅, f) = f := fun f ↦ Subtype.ext (by
      change adelePrincipalValue F ∅ f.val = f.val
      rw [sLocalUncutCarving_empty_PV]
      rfl)
    have hid : P(∅, a, hs) = ContinuousLinearMap.id ℂ _ :=
      (existsUnique_globalThetaSobolevPrincipalValue ∅ a hs).unique
        (existsUnique_globalThetaSobolevPrincipalValue ∅ a hs).exists.choose_spec
        (fun f ↦ congrArg (fun b : ℬ₀ ↦ j(a, hs) (theta(b))) (he f).symm)
    rw [hid]
    exact injective_id
  | insert v S hv ih =>
    have htest (f : ℬ₀) : pvTest(insert v S, f) = pvTest(S, pvTest({v}, f)) := by
      refine Subtype.ext ?_
      change adelePrincipalValue F (insert v S) f.val =
        adelePrincipalValue F S (adelePrincipalValue F {v} f.val)
      rw [sLocalCutoffCarving_antitone_PV (Finset.subset_insert v S), Finset.insert_sdiff_cancel hv]
      rfl
    have he : P(insert v S, a, hs) = (P(S, a, hs)).comp (P({v}, a, hs)) := by
      apply (existsUnique_globalThetaSobolevPrincipalValue (insert v S) a hs).unique
        (existsUnique_globalThetaSobolevPrincipalValue (insert v S) a hs).exists.choose_spec
      intro f
      rw [ContinuousLinearMap.comp_apply, globalThetaSobolevPrincipalValue_apply,
        globalThetaSobolevPrincipalValue_apply, htest]
    rw [he]
    exact ih.comp (globalThetaPrincipalValue_injective_single v a hs)

private theorem globalThetaSobolevPrincipalValue_equivariant_val_eq {A B : Type*}
    (θ : A → B) (pv : A → A) {x x' y y' : A} (hx : x = x') (hy : y = y')
    (h : θ (pv x') = θ y') : θ (pv x) = θ y := by
  subst hx hy
  exact h

private theorem globalThetaSobolevPrincipalValue_equivariant_ker_eq {R M N : Type*}
    {instR : CommRing R} {instM : AddCommGroup M} {instModM : Module R M}
    {instN : AddCommGroup N} {instModN : Module R N}
    {θ : @LinearMap R R _ _ (RingHom.id R) M N instM.toAddCommMonoid instN.toAddCommMonoid
      instModM instModN}
    {x y : M}
    (h : @Submodule.Quotient.mk R M instR.toRing instM instModM (LinearMap.ker θ) x =
         @Submodule.Quotient.mk R M instR.toRing instM instModM (LinearMap.ker θ) y) :
    θ x = θ y := by
  let _ := instR; let _ := instM; let _ := instModM; let _ := instN; let _ := instModN
  rw [Submodule.Quotient.eq, LinearMap.mem_ker, map_sub, sub_eq_zero] at h
  exact h

private theorem globalThetaSobolevPrincipalValue_equivariant_hcomm (S : Finset V) (hn : S.Nonempty)
    (g : IdeleGroup (𝓞 F) F) (f f₁ f₂ : ℬ₀)
    (hf₁ : f₁.val = schwartzBruhatUnitTranslate g f.val)
    (hf₂ : f₂.val = schwartzBruhatUnitTranslate g (adelePrincipalValue F S f.val)) :
    theta(pvTest(S, f₁)) = theta(f₂) :=
  (globalPolarFreeThetaSpace_mk_eq_iff (pvTest(S, f₁)) f₂).mpr
    (globalThetaSobolevPrincipalValue_equivariant_val_eq
      (adelicThetaLinearMap F) (adelePrincipalValue F S) hf₁ hf₂
      (globalThetaSobolevPrincipalValue_equivariant_ker_eq
        (globalThetaPrincipalValue_equivariant hn g f.val)))

private theorem globalThetaSobolevPrincipalValue_equivariant_val_eq_empty {α B : Type*}
    (S₀ S : α) (hS : S = S₀) (pv : α → B → B) (hpv : ∀ x, pv S₀ x = x) (tr : B → B)
    {f f₁ f₂ : B} (hf₁ : f₁ = tr f) (hf₂ : f₂ = tr (pv S f)) :
    pv S f₁ = f₂ := by
  subst hS
  rw [hpv, hf₁, hf₂, hpv]

private theorem globalThetaSobolevPrincipalValue_equivariant_id_apply {M : Type*}
    {instM : AddCommMonoid M} {instMod : @Module ℂ M _ instM}
    {f : @LinearMap ℂ ℂ _ _ (RingHom.id ℂ) M M instM instM instMod instMod}
    (hf : f = @LinearMap.id ℂ M _ instM instMod) (x : M) : f x = x := by
  subst hf
  rfl

private theorem globalThetaSobolevPrincipalValue_equivariant_conj_id {A B C ι : Type*}
    [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] [AddCommGroup C] [Module ℂ C]
    [TopologicalSpace C] (p : SeminormFamily ℂ (TensorProduct ℂ A B) ι)
    (e : WithGeneratingSeminorms (TensorProduct ℂ A B) p ≃L[ℂ] C) (g : A →ₗ[ℂ] A)
    (h : B →ₗ[ℂ] B) (hg : g = LinearMap.id) (hh : h = LinearMap.id) :
    e.toLinearMap.comp ((TensorProduct.map g h).comp e.symm.toLinearMap) = LinearMap.id := by
  subst hg hh
  rw [TensorProduct.map_id]
  ext x
  exact e.apply_symm_apply x

private theorem globalThetaSobolevPrincipalValue_equivariant_hcomm_empty
    (S : Finset V) (hn : ¬ S.Nonempty) (g : IdeleGroup (𝓞 F) F)
    (f f₁ f₂ : ℬ₀)
    (hf₁ : f₁.val = schwartzBruhatUnitTranslate g f.val)
    (hf₂ : f₂.val = schwartzBruhatUnitTranslate g (adelePrincipalValue F S f.val)) :
    theta(pvTest(S, f₁)) = theta(f₂) := by
  have key : ∀ h : (w : (∅ : Finset V)) →
      SchwartzBruhat (Multiplicative (w.val.adicCompletion F)) →ₗ[ℂ]
        SchwartzBruhat (Multiplicative (w.val.adicCompletion F)),
      PiTensorProduct.map (R := ℂ) h = LinearMap.id := fun h ↦ by
    rw [show h = fun _ ↦ LinearMap.id from funext fun w ↦ absurd w.2 (Finset.notMem_empty _)]
    exact PiTensorProduct.map_id
  have hP : sAdelePrincipalValue F (Finset.Subset.refl (∅ : Finset V)) = LinearMap.id := by
    unfold sAdelePrincipalValue
    exact globalThetaSobolevPrincipalValue_equivariant_conj_id _ _ _ _ rfl (key _)
  have hA : adelePrincipalValue F ∅ = LinearMap.id := by
    unfold adelePrincipalValue
    exact globalThetaSobolevPrincipalValue_equivariant_conj_id _ _ _ _ hP rfl
  exact congrArg (fun h : ℬ₀ ↦ theta(h))
    (Subtype.ext (globalThetaSobolevPrincipalValue_equivariant_val_eq_empty ∅ S
      (Finset.not_nonempty_iff_eq_empty.mp hn)
      (fun T x ↦ adelePrincipalValue F T x)
      (globalThetaSobolevPrincipalValue_equivariant_id_apply hA)
      (fun x ↦ schwartzBruhatUnitTranslate g x) hf₁ hf₂))

private theorem globalThetaSobolevPrincipalValue_equivariant_aux
    {C B X Y Z : Type*} [TopologicalSpace Z] [T2Space Z]
    (val : X → B) (j : Y → Z) (q : X → Y) (hi : DenseRange fun x ↦ j (q x))
    (P : Z → Z) (R : C → Z → Z) (hP : Continuous P) (k g' : C) (hg : g' = k)
    (hR : Continuous (R g'))
    (pv : X → X) (hPapp : ∀ x, P (j (q x)) = j (q (pv x)))
    {smul : ℝ → Z → Z} (c : ℝ) (hc : c = 1)
    (tr : B → B)
    (hRtr : ∀ x : X, ∃ x' : X, val x' = tr (val x) ∧ R g' (j (q x)) = smul c (j (q x')))
    (hone : ∀ z : Z, smul 1 z = z)
    (hcomm : ∀ (f f₁ f₂ : X), val f₁ = tr (val f) → val f₂ = tr (val (pv f)) →
      q (pv f₁) = q f₂)
    (u : Z) :
    P (R k u) = R k (P u) := by
  subst hg
  refine congrFun (hi.equalizer (hP.comp hR) (hR.comp hP) (funext fun x ↦ ?_)) u
  obtain ⟨x₁, hx₁, h1⟩ := hRtr x
  obtain ⟨x₂, hx₂, h2⟩ := hRtr (pv x)
  dsimp only [Function.comp_apply]
  rw [h1, hc, hone, hPapp, hPapp, h2, hc, hone, hcomm x x₁ x₂ hx₁ hx₂]

/-- Paper: Proposition 11.2.0.1(2), pp. 484–485. The extension commutes with
norm-one translations and hence preserves all norm-one isotypes.
Deviation: This compatibility is stated separately from closed range and holds
without the lower bound on the degree. -/
theorem globalThetaSobolevPrincipalValue_equivariant (S : Finset V) (a : ℝ)
    {s : ℝ} (hs : 0 ≤ s) (k : C₁) (u : H(a, hs)) :
    let R := (exists_globalThetaSobolevAction (F := F) a hI hs).choose
    P(S, a, hs) (R k.val u) = R k.val (P(S, a, hs) u) := by
  intro R
  have hq : Surjective (fun f : ℬ₀ ↦ theta(f)) := Submodule.mkQ_surjective
    ((LinearMap.ker (adelicThetaLinearMap F)).comap (adelePolarSubspace F).subtype)
  have hdense : DenseRange (fun f : ℬ₀ ↦ j(a, hs) (theta(f))) :=
    (globalThetaSobolev_dense (F := F) a hI hs).comp hq.denseRange (j(a, hs)).continuous
  refine Exists.elim (QuotientGroup.mk_surjective k.val) fun g hg ↦ ?_
  have hc : (((m𝔽 (QuotientGroup.mk g)).val : ℝ) ^ (-a) : ℝ) = 1 := by
    have hk : ideleClassNorm F k.val = 1 := k.property
    change ((ideleClassNorm F (QuotientGroup.mk g)).val : ℝ) ^ (-a) = 1
    rw [hg, hk]
    simp
  exact globalThetaSobolevPrincipalValue_equivariant_aux Subtype.val (j(a, hs))
    (fun f : ℬ₀ ↦ theta(f)) hdense
    (P(S, a, hs)) (fun c v ↦ R c v) (P(S, a, hs)).continuous k.val (QuotientGroup.mk g) hg
    (R (QuotientGroup.mk g)).continuous
    (fun f ↦ pvTest(S, f)) (globalThetaSobolevPrincipalValue_apply S a hs)
    _ hc
    (fun f' ↦ schwartzBruhatUnitTranslate g f')
    ((exists_globalThetaSobolevAction (F := F) a hI hs).choose_spec.2.2 g)
    (fun z ↦ one_smul ℝ z)
    (if hn : S.Nonempty then
      globalThetaSobolevPrincipalValue_equivariant_hcomm S hn g
    else
      globalThetaSobolevPrincipalValue_equivariant_hcomm_empty S hn g)
    u

/-- Banach–Steinhaus on a compact parameter set: a strongly continuous family of operators on
a Banach space is uniformly bounded there. -/
private theorem globalThetaSobolevPrincipalValue_singleton_bound {X W : Type*}
    [TopologicalSpace X] [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
    (T : X → W →L[ℂ] W) (hT : ∀ w, Continuous fun k ↦ T k w) (U : Set X) (hU : IsCompact U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k ∈ U, ‖T k‖ ≤ C := by
  obtain ⟨C, hC⟩ := banach_steinhaus (g := fun k : U ↦ T k.val) fun w ↦ by
    obtain ⟨C, hC⟩ := hU.exists_bound_of_continuousOn (hT w).continuousOn
    exact ⟨C, fun k ↦ hC k.val k.property⟩
  exact ⟨max C 0, le_max_right _ _, fun k hk ↦ (hC ⟨k, hk⟩).trans (le_max_left _ _)⟩

/-- A continuous linear map that is bounded by a multiple of the distance to `u` on a dense set
vanishes at `u`. -/
private theorem globalThetaSobolevPrincipalValue_singleton_dense {Y E W : Type*}
    [SeminormedAddCommGroup E] [NormedAddCommGroup W] [NormedSpace ℂ E] [NormedSpace ℂ W]
    (L : E →L[ℂ] W) (D : Y → E) (hD : DenseRange D) (u : E) (K : ℝ)
    (hK : ∀ y, ‖L (D y)‖ ≤ K * ‖D y - u‖) : L u = 0 := by
  refine norm_le_zero_iff.mp (le_of_forall_pos_le_add fun ε hε ↦ ?_)
  set M := ‖L‖ + |K| + 1 with hMdef
  have hM : 0 < M := by positivity
  obtain ⟨y, hy⟩ := Metric.denseRange_iff.mp hD u (ε / M) (div_pos hε hM)
  rw [dist_eq_norm] at hy
  have h1 : ‖L u‖ ≤ ‖L (D y)‖ + ‖L (u - D y)‖ := by
    rw [map_sub]; exact norm_le_norm_add_norm_sub' _ _
  have h2 : ‖L (u - D y)‖ ≤ ‖L‖ * ‖u - D y‖ := L.le_opNorm _
  have h3 : ‖L (D y)‖ ≤ |K| * ‖u - D y‖ := by
    rw [norm_sub_rev]
    exact (hK y).trans (mul_le_mul_of_nonneg_right (le_abs_self K) (norm_nonneg _))
  have h4 : M * ‖u - D y‖ ≤ ε := by
    have := (lt_div_iff₀ hM).mp hy; linarith [mul_comm M ‖u - D y‖]
  nlinarith [norm_nonneg (u - D y), norm_nonneg L, abs_nonneg K]

/-- The density step for the singleton formula: if `P x = x - R x` holds up to a multiple of the
distance to `u` on a dense set, it holds at `u`. -/
private theorem globalThetaSobolevPrincipalValue_singleton_eq {Y W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℂ W] (H : Submodule ℂ W) (P : H →L[ℂ] H)
    (R : W →L[ℂ] W) (D : Y → H) (hD : DenseRange D) (u : H) (K : ℝ)
    (hK : ∀ y, ‖(P (D y) : W) - ((D y : W) - R (D y))‖ ≤ K * ‖(D y : W) - u‖) :
    (P u : W) = u - R u := by
  have h := globalThetaSobolevPrincipalValue_singleton_dense
    (H.subtypeL.comp P - (H.subtypeL - R.comp H.subtypeL)) D hD u K hK
  exact sub_eq_zero.mp h

/-- The squared weighted L² mass of the normalized average of a measurable family over `U` is
at most a common bound for the squared masses of its members (pointwise Cauchy–Schwarz and
Tonelli). -/
private theorem globalThetaSobolevPrincipalValue_singleton_avg {G X : Type*}
    [MeasurableSpace G] [MeasurableSpace X] (ν : Measure G) [SFinite ν] (μX : Measure X)
    (U : Set X) (hU : MeasurableSet U) (hUfin : μX U ≠ ⊤)
    (F : X → G → ℂ) (hF : StronglyMeasurable (Function.uncurry F)) (B : ENNReal)
    (hB : ∀ k ∈ U, ∫⁻ x, ‖F k x‖ₑ ^ 2 ∂ν ≤ B) :
    ∫⁻ x, ‖(((μX.real U)⁻¹ : ℝ) : ℂ) * ∫ k in U, F k x ∂μX‖ₑ ^ 2 ∂ν ≤ B := by
  have : IsFiniteMeasure (μX.restrict U) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.mpr hUfin⟩
  set c : ℝ := μX.real U with hcdef
  have hc0 : 0 ≤ c := measureReal_nonneg
  have hcU : μX U = ENNReal.ofReal c := (ENNReal.ofReal_toReal hUfin).symm
  have hFm : Measurable (Function.uncurry fun x k ↦ ‖F k x‖ₑ ^ 2) :=
    ((hF.measurable.comp measurable_swap).eNorm).pow_const 2
  have hpt (x : G) : ‖((c⁻¹ : ℝ) : ℂ) * ∫ k in U, F k x ∂μX‖ₑ ^ 2 ≤
      ENNReal.ofReal c⁻¹ * ∫⁻ k in U, ‖F k x‖ₑ ^ 2 ∂μX := by
    have h1 : ‖((c⁻¹ : ℝ) : ℂ) * ∫ k in U, F k x ∂μX‖ₑ ≤
        ENNReal.ofReal c⁻¹ * ∫⁻ k in U, ‖F k x‖ₑ ∂μX := by
      rw [eNorm_mul]
      refine mul_le_mul' (le_of_eq ?_) (eNorm_integral_le_lintegral_eNorm _)
      rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hc0)]
    have h2 := globalThetaPrincipalValue_sobolevBound_average_cs (μX.restrict U)
      (fun k ↦ ‖F k x‖ₑ)
      ((hF.measurable.comp (measurable_id.prodMk measurable_const)).eNorm.aemeasurable)
    rw [Measure.restrict_apply_univ, hcU] at h2
    have h3 : ENNReal.ofReal c⁻¹ ^ 2 * ENNReal.ofReal c ≤ ENNReal.ofReal c⁻¹ := by
      rcases hc0.eq_or_lt with h | h
      · rw [← h]; simp
      · rw [← ENNReal.ofReal_pow (inv_nonneg.mpr hc0), ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
        field_simp
    calc ‖((c⁻¹ : ℝ) : ℂ) * ∫ k in U, F k x ∂μX‖ₑ ^ 2
        ≤ (ENNReal.ofReal c⁻¹ * ∫⁻ k in U, ‖F k x‖ₑ ∂μX) ^ 2 :=
          pow_le_pow_left₀ zero_le h1 2
      _ = ENNReal.ofReal c⁻¹ ^ 2 * (∫⁻ k in U, ‖F k x‖ₑ ∂μX) ^ 2 := mul_pow _ _ _
      _ ≤ ENNReal.ofReal c⁻¹ ^ 2 * (ENNReal.ofReal c * ∫⁻ k in U, ‖F k x‖ₑ ^ 2 ∂μX) :=
          mul_le_mul' le_rfl h2
      _ = (ENNReal.ofReal c⁻¹ ^ 2 * ENNReal.ofReal c) * ∫⁻ k in U, ‖F k x‖ₑ ^ 2 ∂μX := by ring
      _ ≤ ENNReal.ofReal c⁻¹ * ∫⁻ k in U, ‖F k x‖ₑ ^ 2 ∂μX := mul_le_mul' h3 le_rfl
  calc ∫⁻ x, ‖((c⁻¹ : ℝ) : ℂ) * ∫ k in U, F k x ∂μX‖ₑ ^ 2 ∂ν
      ≤ ∫⁻ x, ENNReal.ofReal c⁻¹ * ∫⁻ k in U, ‖F k x‖ₑ ^ 2 ∂μX ∂ν := lintegral_mono hpt
    _ = ENNReal.ofReal c⁻¹ * ∫⁻ k in U, ∫⁻ x, ‖F k x‖ₑ ^ 2 ∂ν ∂μX := by
        rw [lintegral_const_mul _ (f := fun x ↦ ∫⁻ k in U, ‖F k x‖ₑ ^ 2 ∂μX)
          hFm.lintegral_prod_right', lintegral_lintegral_swap hFm.aemeasurable]
    _ ≤ ENNReal.ofReal c⁻¹ * ∫⁻ k in U, B ∂μX := mul_le_mul' le_rfl (setLIntegral_mono' hU hB)
    _ = (ENNReal.ofReal c⁻¹ * ENNReal.ofReal c) * B := by rw [setLIntegral_const, hcU]; ring
    _ ≤ B := by
        refine (mul_le_mul' ?_ le_rfl).trans_eq (one_mul _)
        rcases hc0.eq_or_lt with h | h
        · rw [← h]; simp
        · rw [← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ h.ne', ENNReal.ofReal_one]

/-- An L² class represented by the normalized average over `U` of a measurable family has norm
at most a common bound for L² classes representing the members. -/
private theorem globalThetaSobolevPrincipalValue_singleton_est {G X : Type*}
    [MeasurableSpace G] [MeasurableSpace X] {ν : Measure G} [SFinite ν] (μX : Measure X)
    (U : Set X) (hU : MeasurableSet U) (hUfin : μX U ≠ ⊤)
    (F : X → G → ℂ) (hF : StronglyMeasurable (Function.uncurry F))
    (z : Lp ℂ 2 ν) (Y : X → Lp ℂ 2 ν) (B : ℝ) (hB0 : 0 ≤ B)
    (hz : (z : G → ℂ) =ᵐ[ν] fun x ↦ (((μX.real U)⁻¹ : ℝ) : ℂ) * ∫ k in U, F k x ∂μX)
    (hV : ∀ k ∈ U, (Y k : G → ℂ) =ᵐ[ν] F k) (hVB : ∀ k ∈ U, ‖Y k‖ ≤ B) : ‖z‖ ≤ B := by
  have hsq (g : Lp ℂ 2 ν) : ‖g‖ₑ ^ 2 = ∫⁻ x, ‖(g : G → ℂ) x‖ₑ ^ 2 ∂ν := by
    have h := eLpNorm_nnreal_pow_eq_lintegral (f := (g : G → ℂ)) (μ := ν) (p := 2) two_ne_zero
      (Lp.aestronglyMeasurable g)
    rw [Lp.eNorm_def]
    simpa using h
  have hle : ‖z‖ₑ ^ 2 ≤ ENNReal.ofReal B ^ 2 := by
    rw [hsq]
    refine (lintegral_congr_ae (hz.fun_comp fun y ↦ ‖y‖ₑ ^ 2)).trans_le ?_
    refine globalThetaSobolevPrincipalValue_singleton_avg ν μX U hU hUfin F hF _ fun k hk ↦ ?_
    refine (lintegral_congr_ae ((hV k hk).fun_comp fun y ↦ ‖y‖ₑ ^ 2)).symm.trans_le ?_
    refine (hsq (Y k)).symm.trans_le ?_
    rw [← ofReal_norm]
    exact pow_le_pow_left₀ zero_le (ENNReal.ofReal_le_ofReal (hVB k hk)) 2
  have hle' : ‖z‖ₑ ≤ ENNReal.ofReal B := by
    by_contra h
    exact absurd hle (not_le.mpr (ENNReal.pow_lt_pow_left two_ne_zero (not_le.mp h)))
  rw [← ofReal_norm] at hle'
  exact (ENNReal.ofReal_le_ofReal_iff hB0).mp hle'

/-- The pointwise identity behind the singleton formula: the theta function of `PV_v f`, minus
the difference of `θ f` with its translate by `a`, is the normalized unit average of the
differences of the translates by `a` and by `τ k`. -/
private theorem globalThetaSobolevPrincipalValue_singleton_pt {G X : Type*} [Group G]
    [MeasurableSpace X] (μX : Measure X) (U : Set X) (hUfin : μX U ≠ ⊤) (hUpos : 0 < μX.real U)
    (φ ψ : G → ℂ) (a : G) (τ : X → G) (x : G)
    (hint : IntegrableOn (fun k ↦ φ (τ k * x)) U μX)
    (hψ : ψ x = φ x - (((μX.real U)⁻¹ : ℝ) : ℂ) * ∫ k in U, φ (τ k * x) ∂μX) :
    ψ x - (φ x - φ (a⁻¹ * x)) =
      (((μX.real U)⁻¹ : ℝ) : ℂ) * ∫ k in U, (φ (a⁻¹ * x) - φ (τ k * x)) ∂μX := by
  rw [integral_sub (integrableOn_const hUfin) hint, setIntegral_const, hψ, Complex.real_smul,
    Complex.ofReal_inv]
  have hc : ((μX.real U : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hUpos.ne'
  field_simp
  ring

/-- The estimate behind the singleton formula, for one test. Let `w` and `z` be the classes of
`θ f` and `θ (PV_v f)`, where `θ (PV_v f) = θ f - avg_k θ f (τ k * ·)` with `τ k = (a * ι k)⁻¹`.
If the units `ι k` fix `u` and act with norm at most `C`, then the defect `z - (w - ρ a w)` has
norm at most `‖ρ a‖ (1 + C) ‖w - u‖`. -/
private theorem globalThetaSobolevPrincipalValue_singleton_step {G X : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
    [OpensMeasurableSpace X] {ν μ : Measure G} (hνμ : ν ≪ μ) [SFinite ν]
    (ρ : G →* (Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν))
    (htr : ∀ (g : G) (w : Lp ℂ 2 ν) (φ : G → ℂ), (w : G → ℂ) =ᵐ[μ] φ →
      (ρ g w : G → ℂ) =ᵐ[μ] fun x ↦ φ (g⁻¹ * x))
    (μX : Measure X) [IsFiniteMeasureOnCompacts μX] (U : Set X) (hUc : IsCompact U)
    (hUm : MeasurableSet U) (hUpos : 0 < μX.real U)
    (ι' : X → G) (a : G) (τ : X → G) (hτc : Continuous τ) (hτ : ∀ k, τ k = (a * ι' k)⁻¹)
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ k ∈ U, ‖ρ (ι' k)‖ ≤ C)
    (u w z : Lp ℂ 2 ν) (hinv : ∀ k ∈ U, ρ (ι' k) u = u)
    (φ ψ : G → ℂ) (hφ : Continuous φ) (hw : (w : G → ℂ) =ᵐ[μ] φ) (hz : (z : G → ℂ) =ᵐ[μ] ψ)
    (hψ : ∀ x, ψ x = φ x - (((μX.real U)⁻¹ : ℝ) : ℂ) * ∫ k in U, φ (τ k * x) ∂μX) :
    ‖z - (w - ρ a w)‖ ≤ ‖ρ a‖ * (1 + C) * ‖w - u‖ := by
  have hUfin : μX U ≠ ⊤ := hUc.measure_ne_top
  let Fk : X → G → ℂ := fun k x ↦ φ (a⁻¹ * x) - φ (τ k * x)
  have hFc : Continuous (Function.uncurry Fk) :=
    (hφ.comp (continuous_const.mul continuous_snd)).sub
      (hφ.comp ((hτc.comp continuous_fst).mul continuous_snd))
  have hint (x : G) : IntegrableOn (fun k ↦ φ (τ k * x)) U μX :=
    (hφ.comp (hτc.mul continuous_const)).continuousOn.integrableOn_compact hUc
  let Dk : X → Lp ℂ 2 ν := fun k ↦ ρ a (w - ρ (ι' k) w)
  have hV (k : X) (_hk : k ∈ U) : (Dk k : G → ℂ) =ᵐ[ν] Fk k := by
    have e : Dk k = ρ a w - ρ (a * ι' k) w := by
      change ρ a (w - ρ (ι' k) w) = ρ a w - ρ (a * ι' k) w
      rw [map_mul ρ]
      exact map_sub (ρ a) w (ρ (ι' k) w)
    rw [e]
    refine (Lp.coeFn_sub _ _).trans ((hνμ.ae_eq (htr a w φ hw)).sub (hνμ.ae_eq
      ((htr _ w φ hw).trans (Filter.Eventually.of_forall fun x ↦ ?_))))
    change φ ((a * ι' k)⁻¹ * x) = φ (τ k * x)
    rw [hτ k]
  have hVB (k : X) (hk : k ∈ U) : ‖Dk k‖ ≤ ‖ρ a‖ * (1 + C) * ‖w - u‖ := by
    have e : w - ρ (ι' k) w = (w - u) - ρ (ι' k) (w - u) := by
      rw [map_sub (ρ (ι' k)), hinv k hk, sub_sub_sub_cancel_right]
    have h1 : ‖(w - u) - ρ (ι' k) (w - u)‖ ≤ (1 + C) * ‖w - u‖ := by
      refine (norm_sub_le _ _).trans ?_
      have := ((ρ (ι' k)).le_opNorm (w - u)).trans
        (mul_le_mul_of_nonneg_right (hC k hk) (norm_nonneg _))
      linarith
    calc ‖Dk k‖ = ‖ρ a ((w - u) - ρ (ι' k) (w - u))‖ := by
          change ‖ρ a (w - ρ (ι' k) w)‖ = _
          rw [e]
      _ ≤ ‖ρ a‖ * ‖(w - u) - ρ (ι' k) (w - u)‖ := (ρ a).le_opNorm _
      _ ≤ ‖ρ a‖ * ((1 + C) * ‖w - u‖) := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = ‖ρ a‖ * (1 + C) * ‖w - u‖ := (mul_assoc _ _ _).symm
  have hz' : ((z - (w - ρ a w) : Lp ℂ 2 ν) : G → ℂ) =ᵐ[ν]
      fun x ↦ (((μX.real U)⁻¹ : ℝ) : ℂ) * ∫ k in U, Fk k x ∂μX := by
    refine ((Lp.coeFn_sub _ _).trans ((hνμ.ae_eq hz).sub ((Lp.coeFn_sub _ _).trans
      ((hνμ.ae_eq hw).sub (hνμ.ae_eq (htr a w φ hw)))))).trans
      (Filter.Eventually.of_forall fun x ↦ ?_)
    exact globalThetaSobolevPrincipalValue_singleton_pt μX U hUfin hUpos φ ψ a τ x (hint x)
      (hψ x)
  exact globalThetaSobolevPrincipalValue_singleton_est μX U hUm hUfin Fk hFc.stronglyMeasurable
    _ Dk _ (by positivity) hz' hV hVB

/-- Paper: Proof of Proposition 11.2.0.1, pp. 484–485. At an unramified
singleton place, the 0-line extension is the difference with the uniformizer translate.
Deviation: The difference formula applies on the local-unit-invariant summand.
Unramified norm-one isotypes lie in that summand by §5.3. -/
theorem globalThetaSobolevPrincipalValue_singleton (v : V) (π : (v.adicCompletion F)ˣ)
    (_hπ : Valued.v.IsUniformizer π.val) (χ : PontryaginDual C𝔽)
    (_hχ : (ideleClassNormTwist χ 0).IsUnramifiedAt v) {s : ℝ} (hs : 0 ≤ s)
    (u : H(0, hs)) (_hu : (u : W(s)) ∈ Wω(hs, χ.comp restriction)) :
    (P({v}, 0, hs) u : W(s)) =
      (u : W(s)) - ρ(hs) (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v π) u.val := by
  classical
  letI : MeasurableSpace (v.adicCompletion F)ˣ := borel _
  have : BorelSpace (v.adicCompletion F)ˣ := ⟨rfl⟩
  have := finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure (F := F) v
  let μX := finiteLocalMultiplicativeTamagawaMeasure F v
  let U : Set (v.adicCompletion F)ˣ :=
    ((HeightOneSpectrum.adicCompletionIntegers F v).units : Set (v.adicCompletion F)ˣ)
  have hUo : IsOpen U := Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)
  have hUc : IsCompact U := Submonoid.units_isCompact
    (isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v))
  have hUfin : μX U ≠ ⊤ := hUc.measure_ne_top
  have hUpos : 0 < μX.real U :=
    ENNReal.toReal_pos (hUo.measure_pos μX ⟨1, Subgroup.one_mem _⟩).ne' hUfin
  let ι := IdeleClassGroup.ofAdicCompletion (𝓞 F) F v
  have hι : Continuous ι := continuous_ideleClass_ofAdicCompletion F v
  let a : C𝔽 := ι π
  -- The regular representation is strongly continuous and acts by `x ↦ φ (g⁻¹ * x)`.
  have hρc (w : W(s)) : Continuous fun g : C𝔽 ↦ ρ(hs) g w :=
    (exists_hardySobolevTranslation μ𝔽 m𝔽 0 0 s hI hs).choose_spec.2.comp
      (continuous_id.prodMk continuous_const)
  have htr (g : C𝔽) (w : W(s)) (φ : C𝔽 → ℂ) (hw : (w : C𝔽 → ℂ) =ᵐ[μ𝔽] φ) :
      ((ρ(hs) g w : W(s)) : C𝔽 → ℂ) =ᵐ[μ𝔽] fun x ↦ φ (g⁻¹ * x) :=
    (hardySobolevTranslation_apply μ𝔽 m𝔽 0 0 s hI hs g w).trans
      ((measurePreserving_mul_left μ𝔽 g⁻¹).quasiMeasurePreserving.ae_eq_comp hw)
  have hθ (h : ℬ₀) : ((j(0, hs) (theta(h)) : W(s)) : C𝔽 → ℂ) =ᵐ[μ𝔽]
      (adelicTheta h.val : C𝔽 → ℂ) :=
    ((existsUnique_globalThetaSobolevEmbedding (F := F) 0 0 0 s hI hs).exists.choose_spec.2
      h).trans (Filter.EventuallyEq.of_eq (modulationWeight_zero m𝔽 _))
  -- Local integer units act trivially on the isotype.
  have hnormk (k : (v.adicCompletion F)ˣ) (hk : k ∈ U) : ‖(k : v.adicCompletion F)‖ = 1 := by
    have h1 : ‖(k : v.adicCompletion F)‖ ≤ 1 :=
      (Valued.toNormedField.norm_le_one_iff).mpr hk.1
    have h2 : ‖((k⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)‖ ≤ 1 :=
      (Valued.toNormedField.norm_le_one_iff).mpr hk.2
    have h3 : ‖(k : v.adicCompletion F)‖ *
        ‖((k⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)‖ = 1 := by
      rw [← norm_mul, Units.mul_inv, norm_one]
    nlinarith [norm_nonneg (k : v.adicCompletion F),
      norm_nonneg ((k⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)]
  have hker (k : (v.adicCompletion F)ˣ) (hk : k ∈ U) : ι k ∈ (ideleClassNorm F).ker := by
    rw [MonoidHom.mem_ker, ideleClassNorm_ofAdicCompletion]
    apply Units.ext
    apply NNReal.coe_injective
    change ‖(k : v.adicCompletion F)‖ = ((1 : ℝ≥0) : ℝ)
    rw [hnormk k hk, NNReal.coe_one]
  have hχk (k : (v.adicCompletion F)ˣ) (hk : k ∈ U) : (χ (ι k) : ℂ) = 1 := by
    let z : (v.adicCompletionIntegers F)ˣ :=
      ⟨⟨k.val, hk.1⟩, ⟨(k⁻¹ : (v.adicCompletion F)ˣ).val, hk.2⟩, Subtype.ext k.mul_inv,
        Subtype.ext k.inv_mul⟩
    have h := HeckeCharacter.isUnramifiedAt_iff.mp _hχ z
    let x := Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom z
    change (ideleClassNormTwist χ 0).restrict v x.val = 1 at h
    rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe] at h
    change (χ (ι x) : ℂ) * (((ideleClassNorm F (ι x) : ℝ≥0) : ℝ) : ℂ) ^ (0 : ℂ) = 1 at h
    rw [Complex.cpow_zero, mul_one] at h
    have hx : x = k := Units.ext rfl
    rw [← hx]
    exact h
  have hinv (k : (v.adicCompletion F)ˣ) (hk : k ∈ U) : ρ(hs) (ι k) (u : W(s)) = u := by
    have h := (mem_actionIsotype _ _ _).mp _hu ⟨ι k, hker k hk⟩
    change ρ(hs) (ι k) (u : W(s)) = (χ (ι k) : ℂ) • (u : W(s)) at h
    rw [h, hχk k hk, one_smul]
  have hρι (w : W(s)) : Continuous fun k : (v.adicCompletion F)ˣ ↦ ρ(hs) (ι k) w :=
    (hρc w).comp hι
  have hbd : ∃ C : ℝ, 0 ≤ C ∧ ∀ k ∈ U, ‖ρ(hs) (ι k)‖ ≤ C :=
    globalThetaSobolevPrincipalValue_singleton_bound (W := W(s)) (fun k ↦ ρ(hs) (ι k)) hρι U hUc
  obtain ⟨C, hC0, hC⟩ := hbd
  have hq : Surjective (fun f : ℬ₀ ↦ theta(f)) := Submodule.mkQ_surjective
    ((LinearMap.ker (adelicThetaLinearMap F)).comap (adelePolarSubspace F).subtype)
  have hdense : DenseRange (fun f : ℬ₀ ↦ j(0, hs) (theta(f))) :=
    (globalThetaSobolev_dense (F := F) 0 hI hs).comp hq.denseRange (j(0, hs)).continuous
  have hK (f : ℬ₀) : ‖(P({v}, 0, hs) (j(0, hs) (theta(f))) : W(s)) -
      ((j(0, hs) (theta(f)) : W(s)) - ρ(hs) a (j(0, hs) (theta(f)) : W(s)))‖ ≤
      (‖ρ(hs) a‖ * (1 + C)) * ‖(j(0, hs) (theta(f)) : W(s)) - (u : W(s))‖ := by
    have hzf : ((P({v}, 0, hs) (j(0, hs) (theta(f))) : W(s)) : C𝔽 → ℂ) =ᵐ[μ𝔽]
        (adelicTheta (pvTest({v}, f)).val : C𝔽 → ℂ) :=
      (Filter.EventuallyEq.of_eq (congrArg (fun y : H(0, hs) ↦ ((y : W(s)) : C𝔽 → ℂ))
        (globalThetaSobolevPrincipalValue_apply {v} 0 hs f))).trans (hθ (pvTest({v}, f)))
    have hτ (k : (v.adicCompletion F)ˣ) : ι ((π * k)⁻¹) = (a * ι k)⁻¹ := by
      rw [map_inv, map_mul]
    exact globalThetaSobolevPrincipalValue_singleton_step
      (withDensity_absolutelyContinuous _ _) ρ(hs) htr μX U hUc hUo.measurableSet hUpos
      (fun k ↦ ι k) a (fun k ↦ ι ((π * k)⁻¹))
      (hι.comp ((continuous_const.mul continuous_id).inv)) hτ C hC0 hC
      (u : W(s)) (j(0, hs) (theta(f)) : W(s)) (P({v}, 0, hs) (j(0, hs) (theta(f))) : W(s)) hinv
      (adelicTheta f.val) (adelicTheta (pvTest({v}, f)).val) (adelicTheta f.val).continuous
      (hθ f) hzf (fun x ↦ globalThetaPrincipalValue_sobolevBound_formula v π _hπ f x)
  exact globalThetaSobolevPrincipalValue_singleton_eq H(0, hs) P({v}, 0, hs) (ρ(hs) a)
    _ hdense u _ hK

-- TODO(paper-gap): Proposition 11.2.0.1(2) identifies the raw range with a
-- closed subspace. The singleton prime difference over ℚ has nonclosed range.
-- The kernel argument on p. 485 also requires each zero's own multiplicity.
-- For S = {2,3} and trivial χ over ℚ, 2πi/log 2 is simple. The difference
-- kills Mellin evaluation there but need not kill the first derivative.

/-- Paper: (11.2.0.3), p. 484. The closure of the extension's range agrees with
the norm closure of the principal values of the polar-free theta tests.
Deviation: The range of the extension must also be closed up. -/
theorem globalThetaSobolevPrincipalValue_range_closure (S : Finset V) (a : ℝ)
    {s : ℝ} (hs : 0 ≤ s) :
    closure (range (P(S, a, hs))) =
      closure (range fun f : ℬ₀ ↦ j(a, hs) (theta(pvTest(S, f)))) := by
  have closure_image (i : ℬ₀ → H(a, hs)) (p : H(a, hs) → H(a, hs)) (t : ℬ₀ → H(a, hs)) (hi : DenseRange i) (hp : Continuous p)
      (he : ∀ x, p (i x) = t x) : closure (range p) = closure (range t) := by
    rw [← show p ∘ i = t from funext he, Set.range_comp p i]
    exact le_antisymm (closure_minimal (hp.range_subset_closure_image_dense hi) isClosed_closure)
      (closure_mono (Set.image_subset_range _ _))
  let q : ℬ₀ → GlobalPolarFreeThetaSpace F := fun f ↦ theta(f)
  have hq : Surjective q := Submodule.mkQ_surjective
    ((LinearMap.ker (adelicThetaLinearMap F)).comap (adelePolarSubspace F).subtype)
  exact closure_image (fun f ↦ j(a, hs) (q f)) (P(S, a, hs))
    (fun f : ℬ₀ ↦ j(a, hs) (theta(pvTest(S, f))))
    ((globalThetaSobolev_dense (F := F) a hI hs).comp hq.denseRange (j(a, hs)).continuous)
    (P(S, a, hs)).continuous (globalThetaSobolevPrincipalValue_apply S a hs)

/-- Paper: Theorem 11.2.0.2(1), p. 485. The reciprocal partial Euler
product is the product of the unramified factors in the phase coordinates
of §6.3.1. The complex argument is the norm-twist parameter.
Deviation: For PV on S use the product over S on both sides. The product
over the places of S above p gives the operator for that subset. The canonical
phase in [0, 2π/log q) is given by unramifiedHeckeCharacter_existsUnique_phase. -/
theorem orbitalEulerProduct_eq_phase (χ : PontryaginDual C𝔽) (S : Finset V) (t : V → ℝ)
    (_hχ : ∀ v ∈ S, (ideleClassNormTwist χ 0).IsUnramifiedAt v)
    (_ht : ∀ v ∈ S, (ideleClassNormTwist χ 0).localValue v = (q(v) : ℂ) ^ (-frequency(t v)))
    (z : ℂ) :
    reciprocalPartialHeckeEulerProduct χ S z =
      ∏ v ∈ S, (1 - (q(v) : ℂ) ^ (-z - frequency(t v))) := by
  classical
  exact Finset.prod_congr rfl fun v hv ↦ finiteHeckeEulerFactor_inv_eq_phase χ v
    (_hχ v hv) (t v) (by simpa only [neg_mul] using _ht v hv) z

/-- Paper: Theorem 11.2.0.2(1), p. 485. The multiplicity is the order of the
reciprocal partial Euler product at the given point. -/
def orbitalEulerMultiplicity (χ : PontryaginDual C𝔽) (S : Finset V) (z : ℂ) : ℕ :=
  (meromorphicOrderAt (reciprocalPartialHeckeEulerProduct χ S) z).untop₀.toNat

open Classical in
/-- Paper: Theorem 11.2.0.2(1), p. 485. Each vanishing local factor contributes
one to the multiplicity, including when several places lie over the same prime. -/
theorem orbitalEulerMultiplicity_eq_card (χ : PontryaginDual C𝔽) (S : Finset V) (z : ℂ) :
    orbitalEulerMultiplicity χ S z =
      (S.filter fun v ↦ (finiteHeckeEulerFactor χ v z)⁻¹ = 0).card := by
  classical
  let f (v : V) (w : ℂ) := (finiteHeckeEulerFactor χ v w)⁻¹
  have hfac (v : V) : meromorphicOrderAt (f v) z = if f v z = 0 then 1 else 0 := by
    obtain ⟨ha, ho⟩ := reciprocalEulerProduct_over_prime_order_le_factor χ v z
    change AnalyticAt ℂ (f v) z at ha
    change analyticOrderAt (f v) z ≤ 1 at ho
    rw [ha.meromorphicOrderAt_eq]
    split_ifs with hv
    · have hone : analyticOrderAt (f v) z = 1 :=
        le_antisymm ho (Order.one_le_iff_ne_zero.mpr (ha.analyticOrderAt_ne_zero.mpr hv))
      simp [hone]
    · simp [ha.analyticOrderAt_eq_zero.mpr hv]
  have horder : meromorphicOrderAt (reciprocalPartialHeckeEulerProduct χ S) z =
      ((S.filter fun v ↦ f v z = 0).card : WithTop ℤ) := by
    change meromorphicOrderAt (fun w ↦ ∏ v ∈ S, f v w) z = _
    rw [meromorphicOrderAt_fun_prod (f := f) (fun v _ ↦
      (reciprocalEulerProduct_over_prime_order_le_factor χ v z).1.meromorphicAt)]
    simp only [hfac, Finset.sum_boole]
  rw [orbitalEulerMultiplicity, horder]
  simp [f]

/-- Paper: Theorem 11.2.0.2(1), p. 485. For a unitary character unramified
at the selected places, every zero of the reciprocal product has real part zero.
The complex argument is the norm-twist parameter, independent of the Sobolev degree. -/
theorem orbitalEulerZero_re_eq_zero (χ : PontryaginDual C𝔽) (S : Finset V)
    (_hχ : ∀ v ∈ S, (ideleClassNormTwist χ 0).IsUnramifiedAt v) {z : ℂ}
    (_hz : reciprocalPartialHeckeEulerProduct χ S z = 0) : z.re = 0 := by
  classical
  have hprod : (∏ v ∈ S, (finiteHeckeEulerFactor χ v z)⁻¹) = 0 := _hz
  obtain ⟨v, hv, hzero⟩ := Finset.prod_eq_zero_iff.mp hprod
  rw [finiteHeckeEulerFactor, ite_eq_left (_hχ v hv), inv_inv, sub_eq_zero] at hzero
  have hq : 1 < (q(v) : ℝ) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hn := congrArg (fun w : ℂ ↦ ‖w‖) hzero.symm
  simp only [norm_mul, norm_ideleClassNormTwist_zero_localValue, one_mul,
    Complex.norm_natCast_cpow_of_pos (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v)),
    Complex.neg_re, norm_one] at hn
  have he : -z.re = 0 := (Real.rpow_right_inj (zero_lt_one.trans hq) hq.ne').mp
    (hn.trans (Real.rpow_zero _).symm)
  exact neg_eq_zero.mp he

/-- Paper: Theorem 11.2.0.2(1)–(2) and (11.2.0.6), p. 485. Index jets by their
0-line ordinate and surviving log-power order.
Deviation: Use the strict reciprocal-weight integrability cutoff of §10.2,
which excludes a logarithmically divergent endpoint of the printed floor. -/
abbrev OrbitalJetIndex (χ : PontryaginDual C𝔽) (S : Finset V) (s : ℝ) :=
  {j : ℝ × ℕ //
    j.2 < spectralBoundaryMultiplicity s (orbitalEulerMultiplicity χ S (frequency(j.1)))}

private theorem OrbitalJetIndex.isZero_analyticAt (χ : PontryaginDual C𝔽) (S : Finset V)
    (z : ℂ) : AnalyticAt ℂ (reciprocalPartialHeckeEulerProduct χ S) z := by
  have h : ∀ v ∈ S, AnalyticAt ℂ (fun s ↦ (finiteHeckeEulerFactor χ v s)⁻¹) z := by
    intro v _
    have hq : (Ideal.absNorm v.asIdeal : ℂ) ∈ Complex.slitPlane :=
      Complex.natCast_mem_slitPlane.mpr ((Ideal.absNorm_eq_zero_iff).not.mpr v.ne_bot)
    classical
    by_cases hv : (ideleClassNormTwist χ 0).IsUnramifiedAt v
    · have : (fun s ↦ (finiteHeckeEulerFactor χ v s)⁻¹) = fun s ↦
          1 - (ideleClassNormTwist χ 0).localValue v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s) := by
        funext s
        rw [finiteHeckeEulerFactor, ite_eq_left hv, inv_inv]
      rw [this]
      exact analyticAt_const.sub
        (analyticAt_const.mul (AnalyticAt.cpow analyticAt_const analyticAt_id.neg hq))
    · have : (fun s ↦ (finiteHeckeEulerFactor χ v s)⁻¹) = fun _ ↦ 1 := by
        funext s
        rw [finiteHeckeEulerFactor, ite_eq_right hv, inv_one]
      rw [this]
      exact analyticAt_const
  have := Finset.analyticAt_prod S h
  convert this using 1
  funext s
  simp [reciprocalPartialHeckeEulerProduct]

private theorem OrbitalJetIndex.isZero_of_order_pos {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z)
    (h : 0 < (meromorphicOrderAt f z).untop₀.toNat) : f z = 0 := by
  by_contra hz
  have h0 : analyticOrderAt f z = 0 := hf.analyticOrderAt_eq_zero.mpr hz
  rw [hf.meromorphicOrderAt_eq, h0] at h
  simp at h

/-- Paper: Theorem 11.2.0.2(1)–(2), p. 485. An admitted jet has a zero of the
reciprocal Euler product at its ordinate. -/
theorem OrbitalJetIndex.isZero {χ : PontryaginDual C𝔽} {S : Finset V} {s : ℝ}
    (j : OrbitalJetIndex χ S s) :
    reciprocalPartialHeckeEulerProduct χ S (frequency(j.val.1)) = 0 :=
  OrbitalJetIndex.isZero_of_order_pos (OrbitalJetIndex.isZero_analyticAt χ S _)
    (Nat.zero_lt_of_lt (lt_of_lt_of_le j.property (min_le_left _ _)))

/-- The log-norm function on the idele class group is continuous. -/
theorem orbitalJet_logNorm_continuous :
    Continuous (fun g : C𝔽 ↦ logNorm g) :=
  Real.continuousOn_log.comp_continuous
    (NNReal.continuous_coe.comp (Units.continuous_val.comp (m𝔽).continuous))
    fun _ ↦ (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'

private theorem orbitalJet_log_positiveRealHaar :
    Measure.map (fun t : ℝ≥0ˣ ↦ Real.log ((t.val : ℝ≥0) : ℝ)) positiveRealHaar = volume := by
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  have hlogt : Measurable (fun t : ℝ≥0ˣ ↦ Real.log ((t.val : ℝ≥0) : ℝ)) :=
    (Real.continuousOn_log.comp_continuous (NNReal.continuous_coe.comp Units.continuous_val)
      fun _ ↦ (NNReal.coe_pos.mpr (Units.zero_lt _)).ne').measurable
  unfold positiveRealHaar
  have hexp : Measurable (fun x : ℝ ↦
      Units.mk0 (Real.exp x).toNNReal
        (Real.toNNReal_eq_zero.not.mpr (not_le_of_gt (Real.exp_pos x)))) :=
    measurable_comap_iff.mpr (continuous_real_toNNReal.comp Real.continuous_exp).measurable
  rw [Measure.map_map hlogt hexp]
  have hid : ((fun t : ℝ≥0ˣ ↦ Real.log ((t.val : ℝ≥0) : ℝ)) ∘ fun x : ℝ ↦
      Units.mk0 (Real.exp x).toNNReal
        (Real.toNNReal_eq_zero.not.mpr (not_le_of_gt (Real.exp_pos x)))) = id := by
    funext x
    change Real.log ((Real.exp x).toNNReal : ℝ) = x
    rw [Real.coe_toNNReal _ (Real.exp_pos x).le, Real.log_exp]
  rw [hid, Measure.map_id]

/-- The log-norm pushes canonical modulated Haar measure forward to Lebesgue measure on `ℝ`. -/
theorem orbitalJet_logNorm_measurePreserving :
    MeasurePreserving (fun g : C𝔽 ↦ logNorm g)
      (canonicalModulatedHaar m𝔽
        (⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ : IsModulation m𝔽))
      volume := by
  have hm : IsModulation m𝔽 := ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
  obtain ⟨τ, hτc, hτ⟩ := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.2.2.2.2.1
  let τ' : ℝ≥0ˣ →ₜ* C𝔽 := ⟨τ, hτc⟩
  let : CompactSpace (m𝔽).toMonoidHom.ker :=
    isCompact_iff_compactSpace.mp (IsModulation.isCompact_ker hm)
  let μ₁ : Measure (m𝔽).toMonoidHom.ker := Measure.haarMeasure ⊤
  let : IsProbabilityMeasure μ₁ := ⟨Measure.haarMeasure_self⟩
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  let : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let : SFinite positiveRealHaar := by unfold positiveRealHaar; infer_instance
  refine ⟨orbitalJet_logNorm_continuous.measurable, ?_⟩
  rw [canonicalModulatedHaar_eq_map_prod m𝔽 hm τ' hτ μ₁ Measure.haarMeasure_self]
  have hsplit_meas : Measurable (fun z : (m𝔽).toMonoidHom.ker × ℝ≥0ˣ ↦ (z.1 : C𝔽) * τ' z.2) :=
    ((continuous_subtype_val.comp continuous_fst).mul (τ'.continuous.comp continuous_snd)).measurable
  rw [Measure.map_map orbitalJet_logNorm_continuous.measurable hsplit_meas]
  have hcomp : ((fun g : C𝔽 ↦ logNorm g) ∘ fun z : (m𝔽).toMonoidHom.ker × ℝ≥0ˣ ↦ (z.1 : C𝔽) * τ' z.2) =
      (fun t : ℝ≥0ˣ ↦ Real.log ((t.val : ℝ≥0) : ℝ)) ∘ Prod.snd := by
    funext ⟨k, t⟩
    change Real.log ((ideleClassNorm F ((k : C𝔽) * τ t)).val : ℝ) = Real.log ((t.val : ℝ≥0) : ℝ)
    have hk : ideleClassNorm F (k : C𝔽) = 1 := k.property
    rw [map_mul, hk, one_mul, hτ t]
  have hlogt : Measurable (fun t : ℝ≥0ˣ ↦ Real.log ((t.val : ℝ≥0) : ℝ)) :=
    (Real.continuousOn_log.comp_continuous (NNReal.continuous_coe.comp Units.continuous_val)
      fun _ ↦ (NNReal.coe_pos.mpr (Units.zero_lt _)).ne').measurable
  rw [hcomp, ← Measure.map_map hlogt measurable_snd,
    (measurePreserving_snd (μ := μ₁) (ν := positiveRealHaar)).map_eq]
  exact orbitalJet_log_positiveRealHaar

private theorem orbitalJet_pow_mul_rpow_inv_continuous (k : ℕ) (s : ℝ) :
    Continuous (fun x : ℝ ↦ x ^ (2 * k) * ((1 + x ^ 2) ^ (s / 2))⁻¹) :=
  (continuous_id.pow (2 * k)).mul
    (((continuous_const.add (continuous_id.pow 2)).rpow_const fun x ↦
        Or.inl (by change (1 : ℝ) + x ^ 2 ≠ 0; positivity)).inv₀ fun x ↦
      (Real.rpow_pos_of_pos (by change (0 : ℝ) < 1 + x ^ 2; positivity) _).ne')

private theorem orbitalJet_integrable_pow_mul_rpow_inv {k : ℕ} {s : ℝ}
    (h : 2 * (k : ℝ) + 1 < s) :
    Integrable (fun x : ℝ ↦ x ^ (2 * k) * ((1 + x ^ 2) ^ (s / 2))⁻¹) volume := by
  have hr : ((Module.finrank ℝ ℝ : ℕ) : ℝ) < s - 2 * k := by
    rw [Module.finrank_self]
    push_cast
    linarith
  refine (integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) hr).mono'
    (orbitalJet_pow_mul_rpow_inv_continuous k s).aestronglyMeasurable (ae_of_all _ fun x ↦ ?_)
  have hy : 0 < 1 + x ^ 2 := by positivity
  have h1 : x ^ (2 * k) ≤ (1 + x ^ 2) ^ k := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (sq_nonneg x) (by linarith) k
  have h2 : (1 + x ^ 2) ^ (-(s - 2 * k) / 2) = (1 + x ^ 2) ^ k * ((1 + x ^ 2) ^ (s / 2))⁻¹ := by
    rw [← Real.rpow_natCast (1 + x ^ 2) k, ← Real.rpow_neg hy.le, ← Real.rpow_add hy]
    congr 1
    ring
  rw [Real.norm_of_nonneg (mul_nonneg (Even.pow_nonneg (even_two_mul k) x)
    (inv_nonneg.2 (Real.rpow_nonneg hy.le _))), Real.norm_eq_abs, sq_abs, h2]
  exact mul_le_mul_of_nonneg_right h1 (inv_nonneg.2 (Real.rpow_nonneg hy.le _))

private theorem orbitalJet_continuous (χ : PontryaginDual C𝔽) (t : ℝ) (k : ℕ) :
    Continuous (jet(χ, t, k)) :=
  (ideleClassNormTwist χ ((0 : ℂ) + (t : ℂ) * Complex.I)).continuous.mul
    ((Complex.continuous_ofReal.comp orbitalJet_logNorm_continuous).pow k)

private theorem orbitalJet_norm_sq (χ : PontryaginDual C𝔽) (t : ℝ) (k : ℕ) (g : C𝔽) :
    ‖jet(χ, t, k) g‖ ^ 2 = (logNorm g) ^ (2 * k) := by
  have htwist : ‖ideleClassNormTwist χ ((0 : ℂ) + (t : ℂ) * Complex.I) g‖ = 1 := by
    change ‖(χ g : ℂ) *
      (((ideleClassNorm F g).val : ℝ) : ℂ) ^ ((0 : ℂ) + (t : ℂ) * Complex.I)‖ = 1
    rw [norm_mul, Circle.norm_coe, one_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos
        (NNReal.coe_pos.mpr (Units.zero_lt (ideleClassNorm F g)))]
    simp
  change ‖ideleClassNormTwist χ ((0 : ℂ) + (t : ℂ) * Complex.I) g *
    (logNorm g : ℂ) ^ k‖ ^ 2 = _
  rw [norm_mul, htwist, one_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  calc
    (|logNorm g| ^ k) ^ 2 = (|logNorm g| ^ 2) ^ k := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm k 2]
    _ = ((logNorm g) ^ 2) ^ k := congrArg (fun y : ℝ ↦ y ^ k) (sq_abs (logNorm g))
    _ = (logNorm g) ^ (2 * k) := (pow_mul _ _ _).symm

private theorem orbitalJet_density_eq (s : ℝ) (g : C𝔽) :
    (intervalSobolevDensity 0 0 s (logNorm g))⁻¹ =
      ((1 + (logNorm g) ^ 2) ^ (s / 2))⁻¹ := by
  simp only [intervalSobolevDensity, mul_zero, zero_mul, Real.exp_zero, max_self, one_mul]

private theorem orbitalJet_density_pos (s : ℝ) (g : C𝔽) :
    0 < (intervalSobolevDensity 0 0 s (logNorm g))⁻¹ := by
  rw [orbitalJet_density_eq]
  exact inv_pos.mpr (Real.rpow_pos_of_pos (by positivity) _)

/-- The reciprocal Sobolev weight `(intervalSobolevDensity 0 0 s (logNorm g))⁻¹` is continuous. -/
theorem orbitalJet_density_continuous (s : ℝ) :
    Continuous (fun g : C𝔽 ↦ (intervalSobolevDensity 0 0 s (logNorm g))⁻¹) := by
  have hρ : Continuous (fun g : C𝔽 ↦ (1 + (logNorm g) ^ 2) ^ (s / 2)) :=
    ((continuous_const : Continuous (fun _ : C𝔽 ↦ (1 : ℝ))).add
      (orbitalJet_logNorm_continuous.pow 2)).rpow_const fun g ↦ Or.inl (by
        change (1 : ℝ) + (logNorm g) ^ 2 ≠ 0
        positivity)
  have heq : (fun g : C𝔽 ↦ (intervalSobolevDensity 0 0 s (logNorm g))⁻¹) =
      fun g : C𝔽 ↦ ((1 + (logNorm g) ^ 2) ^ (s / 2))⁻¹ :=
    funext (orbitalJet_density_eq s)
  rw [heq]
  exact hρ.inv₀ fun g ↦ (Real.rpow_pos_of_pos (by positivity) _).ne'

private theorem orbitalJet_ae_of_ae_withDensity {s : ℝ} {p : C𝔽 → Prop}
    (h : ∀ᵐ g ∂(μ'(s)), p g) : ∀ᵐ g ∂μ𝔽, p g := by
  have h' := (ae_withDensity_iff
    ((orbitalJet_density_continuous s).measurable.ennreal_ofReal)).mp h
  filter_upwards [h'] with g hg
  exact hg (ENNReal.ofReal_pos.mpr (orbitalJet_density_pos s g)).ne'

/-- Paper: Theorem 11.2.0.2 and (11.2.0.5), p. 485. Each admitted jet gives a
reciprocal-weight Sobolev vector.
Deviation: The cutoff excludes the divergent endpoint. -/
theorem orbitalJet_memLp (χ : PontryaginDual C𝔽) (S : Finset V) {s : ℝ} (_hs : 0 ≤ s)
    (j : OrbitalJetIndex χ S s) :
    MemLp (jet(χ, j.val.1, j.val.2)) 2 (μ'(s)) := by
  have horder : (j.val.2 : ℝ) < (s - 1) / 2 :=
    ((lt_spectralBoundaryMultiplicity s _ _).mp j.property).2
  have hk : 2 * (j.val.2 : ℝ) + 1 < s := by linarith
  have hm : IsModulation m𝔽 := ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
  let ν : Measure C𝔽 := canonicalModulatedHaar m𝔽 hm
  let : ν.IsHaarMeasure := (existsUnique_canonicalModulatedHaar m𝔽 hm).exists.choose_spec.1
  have hν : Integrable (fun g : C𝔽 ↦ (logNorm g) ^ (2 * j.val.2) *
      ((1 + (logNorm g) ^ 2) ^ (s / 2))⁻¹) ν :=
    orbitalJet_logNorm_measurePreserving.integrable_comp_of_integrable
      (orbitalJet_integrable_pow_mul_rpow_inv hk)
  have hμ : Integrable (fun g : C𝔽 ↦ (logNorm g) ^ (2 * j.val.2) *
      ((1 + (logNorm g) ^ 2) ^ (s / 2))⁻¹) μ𝔽 := by
    rw [Measure.isMulLeftInvariant_eq_smul μ𝔽 ν]
    exact hν.smul_measure_nnreal
  apply (memLp_two_iff_integrable_sq_norm
    (orbitalJet_continuous χ j.val.1 j.val.2).aestronglyMeasurable).2
  apply (integrable_withDensity_iff
    ((orbitalJet_density_continuous s).measurable.ennreal_ofReal)
    (ae_of_all μ𝔽 fun _ ↦ ENNReal.ofReal_lt_top)).2
  refine hμ.congr (ae_of_all μ𝔽 fun g ↦ ?_)
  dsimp only
  rw [orbitalJet_norm_sq, orbitalJet_density_eq,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (Real.rpow_pos_of_pos (by positivity) _).le)]

local notation "jetLp(" χ ", " S ", " hs ", " j ")" =>
  (orbitalJet_memLp χ S hs j).toLp (jet(χ, (j).val.1, (j).val.2))

/-- Paper: Theorem 11.2.0.2, p. 485. Under left translation, each admitted jet
lies in the conjugate isotype in the negative space. -/
theorem orbitalJet_isotype (χ : PontryaginDual C𝔽) (S : Finset V) {s : ℝ} (hs : 0 ≤ s)
    (j : OrbitalJetIndex χ S s) (k : C₁) :
    (fun g ↦ jetLp(χ, S, hs, j) (k.val⁻¹ * g)) =ᵐ[μ𝔽]
      fun g ↦ (χ⁻¹ k.val : ℂ) * jetLp(χ, S, hs, j) g := by
  have hae : (jetLp(χ, S, hs, j) : C𝔽 → ℂ) =ᵐ[μ𝔽] jet(χ, j.val.1, j.val.2) :=
    orbitalJet_ae_of_ae_withDensity (MemLp.coeFn_toLp _)
  have hae_tr : (fun g ↦ jetLp(χ, S, hs, j) (k.val⁻¹ * g)) =ᵐ[μ𝔽]
      fun g ↦ jet(χ, j.val.1, j.val.2) (k.val⁻¹ * g) :=
    (measurePreserving_mul_left μ𝔽 k.val⁻¹).quasiMeasurePreserving.ae_eq_comp hae
  have hpt : ∀ g : C𝔽, jet(χ, j.val.1, j.val.2) (k.val⁻¹ * g) =
      (χ⁻¹ k.val : ℂ) * jet(χ, j.val.1, j.val.2) g := by
    intro g
    have hk : ideleClassNorm F k.val = 1 := k.property
    have hnorm : ideleClassNorm F (k.val⁻¹ * g) = ideleClassNorm F g := by
      rw [map_mul, map_inv, hk, inv_one, one_mul]
    have hlog : logNorm (k.val⁻¹ * g) = logNorm g := by
      dsimp only [logIdeleClassNorm]
      rw [hnorm]
    change (χ (k.val⁻¹ * g) : ℂ) *
        (((ideleClassNorm F (k.val⁻¹ * g)).val : ℝ) : ℂ) ^ ((0 : ℂ) + (j.val.1 : ℂ) * Complex.I) *
        (logNorm (k.val⁻¹ * g) : ℂ) ^ j.val.2 =
      (χ⁻¹ k.val : ℂ) *
        ((χ g : ℂ) *
          (((ideleClassNorm F g).val : ℝ) : ℂ) ^ ((0 : ℂ) + (j.val.1 : ℂ) * Complex.I) *
          (logNorm g : ℂ) ^ j.val.2)
    rw [hnorm, hlog, map_mul, Circle.coe_mul, map_inv]
    have hχinv : (χ k.val)⁻¹ = χ⁻¹ k.val := rfl
    rw [hχinv]
    ring
  filter_upwards [hae_tr, hae] with g hg₁ hg₂
  rw [hg₁, hg₂, hpt g]

variable (F) in
/-- Paper: Theorem 11.2.0.2 and Remark 11.2.0.3, p. 485. Inside the chosen
positive Sobolev isotype, take the closed principal-value subspace.
Deviation: Close the completed principal-value range in the ambient space
before taking the isotype. -/
def orbitalSobolevSubmodule (S : Finset V) {s : ℝ} (hs : 0 ≤ s)
    (ω : PontryaginDual C₁) : Submodule ℂ Wω(hs, ω) :=
  ((((H(0, hs)).subtype.comp (P(S, 0, hs)).toLinearMap).range).topologicalClosure).comap
    (Wω(hs, ω)).subtype

local notation "N(" S ", " hs ", " ω ")" => orbitalSobolevSubmodule F S hs ω
local notation "Q(" S ", " hs ", " ω ")" => (↥(Wω(hs, ω)) ⧸ N(S, hs, ω))

/-- Paper: Remark 11.2.0.3, p. 485. The principal-value subspace is closed
in its isotype, so the quotient carries the canonical quotient norm.
Deviation: Sanity check for the closure used in the definition. -/
@[instance]
theorem instClosedOrbitalSobolevSubmoduleSec2a (S : Finset V) {s : ℝ} (hs : 0 ≤ s)
    (ω : PontryaginDual C₁) : IsClosed (N(S, hs, ω) : Set Wω(hs, ω)) :=
  (Submodule.isClosed_topologicalClosure _).preimage continuous_subtype_val

/-- Conjugating the tensor product of two identity maps by a linear
equivalence out of a seminorm-generated tensor space gives the identity. -/
theorem withGeneratingSeminorms_conj_map_id {A B C ι : Type*} [AddCommGroup A]
    [Module ℂ A] [AddCommGroup B] [Module ℂ B] [AddCommGroup C] [Module ℂ C]
    [TopologicalSpace C] (p : SeminormFamily ℂ (TensorProduct ℂ A B) ι)
    (e : WithGeneratingSeminorms (TensorProduct ℂ A B) p ≃L[ℂ] C) (g : A →ₗ[ℂ] A)
    (h : B →ₗ[ℂ] B) (hg : g = LinearMap.id) (hh : h = LinearMap.id) :
    e.toLinearMap.comp ((TensorProduct.map g h).comp e.symm.toLinearMap) = LinearMap.id := by
  subst hg hh
  rw [TensorProduct.map_id]
  ext x
  exact e.apply_symm_apply x

/-- Pulling back the closure of a dense submodule to any submodule gives the
whole submodule. -/
theorem comap_topologicalClosure_eq_top_of_dense {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [ContinuousAdd E] [ContinuousConstSMul ℂ E] (K R : Submodule ℂ E)
    (hR : Dense (R : Set E)) : R.topologicalClosure.comap K.subtype = ⊤ := by
  rw [(Submodule.dense_iff_topologicalClosure_eq_top).1 hR, Submodule.comap_top]

/-- Paper: Theorem 11.2.0.2, p. 485. With no finite places imposed, the
principal-value subspace is the whole isotype.
Deviation: Sanity check for the empty set of places. -/
theorem orbitalSobolevSubmodule_empty {s : ℝ} (hs : 0 ≤ s) (ω : PontryaginDual C₁) :
    N(∅, hs, ω) = ⊤ := by
  have key : ∀ g : (w : (∅ : Finset V)) →
      SchwartzBruhat (Multiplicative (w.val.adicCompletion F)) →ₗ[ℂ]
        SchwartzBruhat (Multiplicative (w.val.adicCompletion F)),
      PiTensorProduct.map (R := ℂ) g = LinearMap.id := fun g ↦ by
    rw [show g = fun _ ↦ LinearMap.id from funext fun w ↦ absurd w.2 (Finset.notMem_empty _)]
    exact PiTensorProduct.map_id
  have hP : sAdelePrincipalValue F (Finset.Subset.refl (∅ : Finset V)) = LinearMap.id := by
    unfold sAdelePrincipalValue
    exact withGeneratingSeminorms_conj_map_id _ _ _ _ rfl (key _)
  have hA : adelePrincipalValue F ∅ = LinearMap.id := by
    unfold adelePrincipalValue
    exact withGeneratingSeminorms_conj_map_id _ _ _ _ hP rfl
  have hpv : ∀ f : ℬ₀, pvTest(∅, f) = f := fun f ↦ Subtype.ext (by
    simp only [hA, LinearMap.id_apply])
  have hPid : P(∅, 0, hs) = ContinuousLinearMap.id ℂ _ :=
    (existsUnique_globalThetaSobolevPrincipalValue ∅ 0 hs).unique
      (existsUnique_globalThetaSobolevPrincipalValue ∅ 0 hs).exists.choose_spec
      (fun f ↦ congrArg (fun g : ℬ₀ ↦ j(0, hs) (theta(g))) (hpv f).symm)
  unfold orbitalSobolevSubmodule
  refine comap_topologicalClosure_eq_top_of_dense _ _ ?_
  refine (denseRange_globalTheta_zeroLine hs).mono ?_
  rintro _ ⟨u, rfl⟩
  exact ⟨j(0, hs) u, congrArg
    (fun T : H(0, hs) →L[ℂ] H(0, hs) ↦ ((T (j(0, hs) u) : H(0, hs)) : W(s))) hPid⟩

-- TODO(paper-gap): The proof on p. 486 needs density of both spans for the
-- completed PV quotient. Strong approximation on the ambient space in §9.3
-- alone does not identify the annihilator of that completed image.

/-- Positive finite orders of the reciprocal Euler product form a discrete divisor. -/
private theorem orbitalMarkushevichBasis_countable (χ : PontryaginDual C𝔽) (S : Finset V)
    (s : ℝ) : Countable (OrbitalJetIndex χ S s) := by
  let Z := {z : ℂ | 0 < orbitalEulerMultiplicity χ S z}
  have hm : Meromorphic (reciprocalPartialHeckeEulerProduct χ S) :=
    fun z ↦ (OrbitalJetIndex.isZero_analyticAt χ S z).meromorphicAt
  have hc : Zᶜ ∈ Filter.codiscrete ℂ := by
    filter_upwards [hm.meromorphicOn.codiscreteWithin_setOfPred_meromorphicOrderAt_eq_zero_or_top]
      with z hz
    rcases hz.2 with h | h <;> simp [Z, orbitalEulerMultiplicity, h]
  let : DiscreteTopology Z := isDiscrete_iff_discreteTopology.mp
    (compl_mem_codiscrete_iff.mp hc).2
  let : Countable Z := countable_of_Lindelof_of_discrete
  let e (j : OrbitalJetIndex χ S s) : Z × ℕ :=
    (⟨frequency(j.val.1), (lt_spectralBoundaryMultiplicity _ _ _ |>.mp j.property).1.pos⟩, j.val.2)
  apply Function.Injective.countable (f := e)
  intro i j h
  exact Subtype.ext (Prod.ext (by simpa [e] using congrArg (fun p : Z × ℕ ↦ p.1.val.im) h)
    (congrArg (fun p : Z × ℕ ↦ p.2) h))

/-- A jet is nonzero on its positive isotype. Its continuous representative is nonzero
at norm two, and Sobolev duality separates the two conjugate isotypes. -/
private theorem orbitalMarkushevichBasis_nonzero (χ : PontryaginDual C𝔽) (S : Finset V)
    {s : ℝ} (hs : 0 ≤ s) (j : OrbitalJetIndex χ S s) :
    ∃ f : Wω(hs, χ.comp restriction), spectralSobolevPairing f.val (jetLp(χ, S, hs, j)) ≠ 0 := by
  apply (spectralSobolevPairing_isotype hI hs (χ.comp restriction)).2 _
    (orbitalJet_isotype χ S hs j)
  intro h
  have hz : (jet(χ, j.val.1, j.val.2)) =ᵐ[μ𝔽] (0 : C𝔽 → ℂ) := by
    have he : (jetLp(χ, S, hs, j) : C𝔽 → ℂ) =ᵐ[μ𝔽] jet(χ, j.val.1, j.val.2) :=
      orbitalJet_ae_of_ae_withDensity (MemLp.coeFn_toLp _)
    rw [h] at he
    exact he.symm.trans (orbitalJet_ae_of_ae_withDensity (Lp.coeFn_zero _ _ _))
  have he := Measure.eq_of_ae_eq hz (orbitalJet_continuous χ _ _) continuous_const
  let r : ℝ≥0ˣ := Units.mk0 2 (by norm_num)
  let x : C𝔽 := QuotientGroup.mk (canonicalIdeleNormSection F r)
  have hx : ideleClassNorm F x = r := canonicalIdeleNormSection_rightInverse F r
  have hn := orbitalJet_norm_sq χ j.val.1 j.val.2 x
  rw [he] at hn
  change ‖(0 : ℂ)‖ ^ 2 = (Real.log ((ideleClassNorm F x).val : ℝ)) ^ _ at hn
  rw [hx] at hn
  change ‖(0 : ℂ)‖ ^ 2 = (Real.log 2) ^ _ at hn
  have hp := pow_pos (Real.log_pos (by norm_num : (1 : ℝ) < 2)) (2 * j.val.2)
  simp [← hn] at hp

-- The local domination estimate and first derivative follow Sec2a_PVKernel_Printed.
private theorem orbitalMarkushevichBasis_exp_bound (x s t : ℝ) (ht : s - 1 < t ∧ t < s + 1) :
    Real.exp (x * t) * |x| ≤ Real.exp (x * (s - 2)) + Real.exp (x * (s + 2)) := by
  have hx : |x| ≤ Real.exp |x| := by linarith [Real.add_one_le_exp |x|]
  apply (mul_le_mul_of_nonneg_left hx (Real.exp_pos _).le).trans
  rw [← Real.exp_add]
  by_cases h : 0 ≤ x
  · apply le_add_of_nonneg_of_le (Real.exp_pos _).le
    rw [Real.exp_le_exp, abs_of_nonneg h]
    nlinarith [mul_nonneg h (sub_nonneg.mpr ht.2.le)]
  · apply le_add_of_le_of_nonneg _ (Real.exp_pos _).le
    rw [Real.exp_le_exp, abs_of_nonpos (le_of_not_ge h)]
    nlinarith [mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge h) (sub_nonneg.mpr ht.1.le)]

open scoped Topology in
private theorem orbitalMarkushevichBasis_mellin_deriv (χ : PontryaginDual C𝔽) (f : C𝔽 → ℂ)
    (hint : ∀ w : ℂ, Integrable (fun g ↦ f g * ideleClassNormTwist χ w g) μ𝔽)
    (z : ℂ) :
    Integrable (fun g ↦ f g * ideleClassNormTwist χ z g * (logNorm g : ℂ)) μ𝔽 ∧
    HasDerivAt (fun w ↦ ∫ g, f g * ideleClassNormTwist χ w g ∂μ𝔽)
      (∫ g, f g * ideleClassNormTwist χ z g * (logNorm g : ℂ) ∂μ𝔽) z := by
  let N (g : C𝔽) : ℝ := (ideleClassNorm F g).val
  let l (g : C𝔽) := Real.log (N g)
  let A (w : ℂ) (g : C𝔽) := f g * ideleClassNormTwist χ w g
  let B (w : ℂ) (g : C𝔽) := A w g * (l g : ℂ)
  have hN (g : C𝔽) : 0 < N g := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hA (w : ℂ) (g : C𝔽) : ‖A w g‖ = ‖f g‖ * Real.exp (l g * w.re) := by
    change ‖f g * ((χ g : ℂ) * (N g : ℂ) ^ w)‖ = _
    rw [norm_mul, norm_mul, Circle.norm_coe, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hN g),
      Real.rpow_def_of_pos (hN g)]
  let U := Complex.re ⁻¹' Ioo (z.re - 1) (z.re + 1)
  have hU : U ∈ 𝓝 z := (isOpen_Ioo.preimage Complex.continuous_re).mem_nhds ⟨by linarith, by linarith⟩
  let D (g : C𝔽) := ‖A (z - 2) g‖ + ‖A (z + 2) g‖
  have hD : Integrable D μ𝔽 := (hint (z - 2)).norm.add (hint (z + 2)).norm
  have hb (g : C𝔽) (w : ℂ) (hw : w ∈ U) : ‖B w g‖ ≤ D g := by
    change ‖A w g * (l g : ℂ)‖ ≤ ‖A (z - 2) g‖ + ‖A (z + 2) g‖
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hA, hA, hA, ← mul_add, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    simpa using orbitalMarkushevichBasis_exp_bound (l g) z.re w.re hw
  have hl : Continuous l := (NNReal.continuous_coe.comp
    (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous)).log (fun g ↦ (hN g).ne')
  have hd (g : C𝔽) (w : ℂ) : HasDerivAt (fun v ↦ A v g) (B w g) w := by
    have hp := (Complex.hasStrictDerivAt_const_cpow (y := w) (Or.inl (Complex.ofReal_ne_zero.mpr (hN g).ne'))).hasDerivAt
    change HasDerivAt (fun v : ℂ ↦ f g * ((χ g : ℂ) * (N g : ℂ) ^ v))
      ((f g * ((χ g : ℂ) * (N g : ℂ) ^ w)) * (Real.log (N g) : ℂ)) w
    simpa only [← Complex.ofReal_log (hN g).le, mul_assoc] using (hp.const_mul (χ g : ℂ)).const_mul (f g)
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le hU
    (.of_forall fun w ↦ (hint w).aestronglyMeasurable) (hint z)
    ((hint z).aestronglyMeasurable.mul (Complex.continuous_ofReal.comp hl).aestronglyMeasurable)
    (.of_forall hb) hD (.of_forall fun g w _ ↦ hd g w)

/-- Every derivative of a polar theta Mellin transform is the corresponding log moment. -/
private theorem orbitalMarkushevichBasis_mellin_moment (χ : PontryaginDual C𝔽) (f : ℬ₀)
    (k : ℕ) (z : ℂ) :
    iteratedDeriv k (fun w ↦ globalIdelicZFunction f.val (ideleClassNormTwist χ w)) z =
      ∫ g, (adelicTheta f.val g * (logNorm g : ℂ) ^ k) * ideleClassNormTwist χ z g ∂μ𝔽 := by
  let a (n : ℕ) (g : C𝔽) := adelicTheta f.val g * (logNorm g : ℂ) ^ n
  let m (n : ℕ) (w : ℂ) (g : C𝔽) := a n g * ideleClassNormTwist χ w g
  have e (n : ℕ) (w : ℂ) (g : C𝔽) : m n w g * (logNorm g : ℂ) = m (n + 1) w g := by
    simp only [m, a, pow_succ]
    ring
  obtain ⟨hf, hF⟩ := (mem_adelePolarSubspace f.val).mp f.property
  have h (n : ℕ) : (∀ w, Integrable (m n w) μ𝔽) ∧
      iteratedDeriv n (fun w ↦ globalIdelicZFunction f.val (ideleClassNormTwist χ w)) =
        fun w ↦ ∫ g, m n w g ∂μ𝔽 := by
    induction n with
    | zero =>
      simp only [iteratedDeriv_zero, m, a, pow_zero, mul_one]
      exact ⟨fun w ↦ globalThetaMellinIntegral_integrable_of_vanishing _ hf hF _,
        funext fun w ↦ congrFun (globalThetaMellinIntegral_eq_continuation_of_vanishing
          _ hf hF).symm (ideleClassNormTwist χ w)⟩
    | succ n ih =>
      have hd (w : ℂ) := orbitalMarkushevichBasis_mellin_deriv χ (a n) ih.1 w
      change ∀ w, Integrable (fun g ↦ m n w g * (logNorm g : ℂ)) μ𝔽 ∧
        HasDerivAt (fun v ↦ ∫ g, m n v g ∂μ𝔽) (∫ g, m n w g * (logNorm g : ℂ) ∂μ𝔽) w at hd
      simp only [e] at hd
      rw [iteratedDeriv_succ, ih.2]
      exact ⟨fun w ↦ (hd w).1, funext fun w ↦ (hd w).2.deriv⟩
  exact congrFun (h k).2 z

/-- The Euler multiplier on polar tests kills the prescribed lower derivatives
at each of its zeros, including when several places contribute to the same order. -/
private theorem orbitalMarkushevichBasis_test (χ : PontryaginDual C𝔽) (S : Finset V)
    {s : ℝ} (j : OrbitalJetIndex χ S s) (f : ℬ₀) :
    (∫ g, adelicTheta (pvTest(S, f)).val g * jet(χ, j.val.1, j.val.2) g ∂μ𝔽) = 0 := by
  let E := reciprocalPartialHeckeEulerProduct χ S
  let Z (u : ℬ₀) (w : ℂ) := globalIdelicZFunction u.val (ideleClassNormTwist χ w)
  let z := frequency(j.val.1)
  have hE : AnalyticAt ℂ E z := OrbitalJetIndex.isZero_analyticAt χ S z
  have hZ := (globalIdelicZFunction_entire_of_vanishing _ f.property χ).analyticAt z
  -- Extend the multiplier identity across its exceptional points as in Ch11/Sec1b.
  have hmul : Z (pvTest(S, f)) = E * Z f := by
    funext w
    have h₁ := (globalIdelicZFunction_entire_of_vanishing _ (pvTest(S, f)).property χ).continuous.continuousAt
      (x := w)
    have h₂ := ((OrbitalJetIndex.isZero_analyticAt χ S w).continuousAt).mul
      ((globalIdelicZFunction_entire_of_vanishing _ f.property χ).continuous.continuousAt (x := w))
    exact ((h₁.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE h₂).mp
      ((globalPrincipalValueConverse_mellin S χ f.val).filter_mono (nhdsNE_le_codiscrete w))).eq_of_nhds
  have hk := (lt_spectralBoundaryMultiplicity _ _ _ |>.mp j.property).1
  change j.val.2 < (meromorphicOrderAt E z).untop₀.toNat at hk
  rw [hE.meromorphicOrderAt_eq] at hk
  have hle : (j.val.2 + 1 : ℕ) ≤ analyticOrderAt E z := by
    cases hn : analyticOrderAt E z with
    | top => simp
    | coe n =>
      simp only [hn, ENat.map_natCast, WithTop.untop₀_coe, Int.toNat_natCast] at hk
      exact_mod_cast hk
  have hle' : ((j.val.2 + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt (E * Z f) z := by
    rw [analyticOrderAt_mul hE hZ]
    exact hle.trans le_self_add
  have hv := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hE.mul hZ)).mp hle'
    j.val.2 (Nat.lt_succ_self _)
  rw [← hmul, orbitalMarkushevichBasis_mellin_moment] at hv
  refine (integral_congr_ae (.of_forall fun g ↦ ?_)).trans hv
  change _ * (ideleClassNormTwist χ ((0 : ℂ) + frequency(j.val.1)) g * _) = _
  rw [zero_add]
  dsimp only [z]
  ring

/-- Continuous jet functionals vanish on the closure of the principal values
because they vanish on the dense family of principal values of polar tests. -/
private theorem orbitalMarkushevichBasis_annihilates (χ : PontryaginDual C𝔽) (S : Finset V)
    {s : ℝ} (hs : 0 ≤ s) (j : OrbitalJetIndex χ S s) (L : StrongDual ℂ W(s))
    (hL : ∀ y, L y = spectralSobolevPairing y (jetLp(χ, S, hs, j)))
    (f : Wω(hs, χ.comp restriction)) (hf : f ∈ N(S, hs, χ.comp restriction)) :
    L f.val = 0 := by
  let H := H(0, hs)
  let A := L.comp H.subtypeL
  have htest (b : ℬ₀) : A (j(0, hs) (theta(pvTest(S, b)))) = 0 := by
    rw [show A (j(0, hs) (theta(pvTest(S, b)))) =
      spectralSobolevPairing (j(0, hs) (theta(pvTest(S, b))) : W(s)) (jetLp(χ, S, hs, j)) from hL _]
    have he := (existsUnique_globalThetaSobolevEmbedding (F := F) 0 0 0 s hI hs).exists.choose_spec.2
      (pvTest(S, b))
    rw [modulationWeight_zero] at he
    exact (integral_congr_ae (he.mul (orbitalJet_ae_of_ae_withDensity (MemLp.coeFn_toLp _)))).trans
      (orbitalMarkushevichBasis_test χ S j b)
  have hker : closure (range (P(S, 0, hs))) ⊆ A.ker := by
    rw [globalThetaSobolevPrincipalValue_range_closure]
    exact closure_minimal (range_subset_iff.mpr htest) A.isClosed_ker
  have hr : ((H.subtype.comp (P(S, 0, hs)).toLinearMap).range) ≤ L.ker := by
    rintro _ ⟨y, rfl⟩
    exact hker (subset_closure (mem_range_self y))
  exact (Submodule.topologicalClosure_minimal _ hr L.isClosed_ker) hf

/-- A nonzero entire multiplier has finite vanishing order at every frequency. -/
private theorem orbitalMarkushevichBasis_synthesis_order (E : ℂ → ℂ)
    (hE : Differentiable ℂ E) (hne : ∃ w, E w ≠ 0) (z : ℂ) : analyticOrderAt E z ≠ ⊤ := by
  obtain ⟨w, hw⟩ := hne
  have ha : AnalyticOnNhd ℂ E univ := fun x _ ↦ hE.analyticAt x
  exact ha.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ w) (mem_univ z)
    (by simp [analyticOrderAt_eq_zero.mpr (.inr hw)])

/-- In a fixed compact frequency band the Euler divisor has only finitely many jets.
At the degree in the theorem every derivative below the local multiplicity is admitted. -/
private theorem orbitalMarkushevichBasis_synthesis_band (χ : PontryaginDual C𝔽) (S : Finset V)
    {s : ℝ} (hc : 2 * (S.card : ℝ) ≤ s)
    (hχ : ∀ v ∈ S, (ideleClassNormTwist χ 0).IsUnramifiedAt v) (R : ℝ) :
    ∃ J : Finset (OrbitalJetIndex χ S s), ∀ t ∈ Icc (-R) R, ∀ k : ℕ,
      (k : ℕ∞) < analyticOrderAt (reciprocalPartialHeckeEulerProduct χ S) (frequency(t)) →
      ∃ j ∈ J, j.val = (t, k) := by
  classical
  let E := reciprocalPartialHeckeEulerProduct χ S
  have hE (z) : AnalyticAt ℂ E z := OrbitalJetIndex.isZero_analyticAt χ S z
  have hd : Differentiable ℂ E := fun z ↦ (hE z).differentiableAt
  have hn : ∃ z, E z ≠ 0 :=
    ⟨1, fun h ↦ one_ne_zero (orbitalEulerZero_re_eq_zero χ S hχ h)⟩
  have hord (z) : analyticOrderAt E z = (orbitalEulerMultiplicity χ S z : ℕ∞) := by
    obtain ⟨n, he⟩ := ENat.ne_top_iff_exists.mp (orbitalMarkushevichBasis_synthesis_order E hd hn z)
    simp [orbitalEulerMultiplicity, ← show E = reciprocalPartialHeckeEulerProduct χ S from rfl,
      (hE z).meromorphicOrderAt_eq, ← he]
  have hzero : (Metric.closedBall (0 : ℂ) R \ {z | E z ≠ 0}).Finite := by
    apply (isCompact_closedBall (0 : ℂ) R).finite_sdiff_of_mem_codiscreteWithin
    have ha : AnalyticOnNhd ℂ E univ := fun x _ ↦ hE x
    obtain h | h := ha.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_univ
    · exact False.elim (hn.choose_spec (h (mem_univ hn.choose)))
    · exact Filter.codiscreteWithin_mono (subset_univ _) h
  let p (j : OrbitalJetIndex χ S s) : ℂ × ℕ := (frequency(j.val.1), j.val.2)
  have hi : Injective p := fun j l h ↦ Subtype.ext (Prod.ext
    (by simpa [p] using congrArg (fun q : ℂ × ℕ ↦ q.1.im) h) (congrArg (fun q : ℂ × ℕ ↦ q.2) h))
  let B := {q : ℂ × ℕ | (q.2 : ℕ∞) < analyticOrderAt E q.1 ∧ ‖q.1‖ ≤ R}
  have hB : B.Finite := by
    apply (hzero.prod (Set.finite_Iio S.card)).subset
    rintro ⟨z, k⟩ ⟨hk, hz⟩
    have hk' : k < orbitalEulerMultiplicity χ S z := by
      exact_mod_cast (hord z ▸ hk : (k : ℕ∞) < (orbitalEulerMultiplicity χ S z : ℕ∞))
    have hz₀ : E z = 0 := by
      by_contra h
      rw [analyticOrderAt_eq_zero.mpr (.inr h)] at hk
      exact (not_lt_zero hk).elim
    rw [orbitalEulerMultiplicity_eq_card] at hk'
    exact ⟨⟨mem_closedBall_zero_iff.mpr hz, by simpa using hz₀⟩,
      hk'.trans_le (Finset.card_filter_le _ _)⟩
  refine ⟨(hB.preimage hi.injOn).toFinset, fun t ht k hk ↦ ?_⟩
  have hk' : k < orbitalEulerMultiplicity χ S (frequency(t)) := by
    exact_mod_cast (hord _ ▸ hk : (k : ℕ∞) < (orbitalEulerMultiplicity χ S (frequency(t)) : ℕ∞))
  have hcard : k + 1 ≤ S.card := (Nat.succ_le_of_lt hk').trans (by
    rw [orbitalEulerMultiplicity_eq_card]
    exact Finset.card_filter_le _ _)
  have hks : (k : ℝ) + 1 ≤ S.card := by exact_mod_cast hcard
  let j : OrbitalJetIndex χ S s := ⟨(t, k),
    (lt_spectralBoundaryMultiplicity _ _ _).mpr ⟨hk', by linarith⟩⟩
  refine ⟨j, (Set.Finite.mem_toFinset _).mpr ⟨hk, ?_⟩, rfl⟩
  simpa [p, j, norm_mul, Real.norm_eq_abs] using (abs_le.mpr ht : |t| ≤ R)

open scoped Topology in
/-- For a polar theta test, vanishing of the jets in a band gives a holomorphic
quotient by the Euler product near each point of the band, including its endpoints. -/
private theorem orbitalMarkushevichBasis_synthesis_germ (χ : PontryaginDual C𝔽) (S : Finset V)
    {s : ℝ} (hs : 0 ≤ s) (hχ : ∀ v ∈ S, (ideleClassNormTwist χ 0).IsUnramifiedAt v)
    (b : ℬ₀) (t : ℝ)
    (h : ∀ k : ℕ, (k : ℕ∞) < analyticOrderAt (reciprocalPartialHeckeEulerProduct χ S) (frequency(t)) →
      ∃ j : OrbitalJetIndex χ S s, j.val = (t, k) ∧
        spectralSobolevPairing (j(0, hs) (theta(b)) : W(s)) (jetLp(χ, S, hs, j)) = 0) :
    ∃ q : ℂ → ℂ, AnalyticAt ℂ q (frequency(t)) ∧ ∀ᶠ z in 𝓝 (frequency(t)),
      globalIdelicZFunction b.val (ideleClassNormTwist χ z) = reciprocalPartialHeckeEulerProduct χ S z * q z := by
  let E := reciprocalPartialHeckeEulerProduct χ S
  let Z (z : ℂ) := globalIdelicZFunction b.val (ideleClassNormTwist χ z)
  let w := frequency(t)
  have hE (z) : AnalyticAt ℂ E z := OrbitalJetIndex.isZero_analyticAt χ S z
  have hZ : AnalyticAt ℂ Z w := (globalIdelicZFunction_entire_of_vanishing _ b.property χ).analyticAt _
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (orbitalMarkushevichBasis_synthesis_order E
    (fun z ↦ (hE z).differentiableAt) ⟨1, fun h ↦ one_ne_zero (orbitalEulerZero_re_eq_zero χ S hχ h)⟩ w)
  have hz : (n : ℕ∞) ≤ analyticOrderAt Z w := by
    apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hZ).mpr
    intro k hk
    obtain ⟨j, hj, hzero⟩ := h k (hn ▸ (by exact_mod_cast hk : (k : ℕ∞) < n))
    have he := (existsUnique_globalThetaSobolevEmbedding (F := F) 0 0 0 s hI hs).exists.choose_spec.2 b
    rw [modulationWeight_zero] at he
    have hjet := orbitalJet_ae_of_ae_withDensity (s := s) (MemLp.coeFn_toLp (orbitalJet_memLp χ S hs j))
    change (∫ g, _ * _ ∂μ𝔽) = 0 at hzero
    have hraw := (integral_congr_ae (he.mul hjet)).symm.trans hzero
    rw [show iteratedDeriv k Z w = _ from orbitalMarkushevichBasis_mellin_moment χ b k w]
    refine (integral_congr_ae (.of_forall fun g ↦ ?_)).trans hraw
    change _ = _ * (ideleClassNormTwist χ ((0 : ℂ) + frequency(j.val.1)) g * (logNorm g : ℂ) ^ j.val.2)
    rw [hj, zero_add]
    dsimp only [w, Prod.fst, Prod.snd]
    ring
  obtain ⟨a, ha, ha₀, hea⟩ := (hE w).analyticOrderAt_eq_natCast.mp hn.symm
  obtain ⟨c, hca, hzc⟩ := (natCast_le_analyticOrderAt hZ).mp hz
  refine ⟨fun z ↦ c z / a z, hca.div ha ha₀, ?_⟩
  filter_upwards [hea, hzc, ha.continuousAt.eventually_ne ha₀] with z h₁ h₂ h₃
  change Z z = E z * _
  rw [h₁, h₂, smul_eq_mul, smul_eq_mul]
  field_simp

open Filter Topology in
/-- A dense linear test family still approximates a vector after finitely many
continuous moment constraints are imposed. Lift the finite-dimensional range of the
test moment map back to tests and subtract a correction tending to zero. -/
private theorem orbitalMarkushevichBasis_synthesis_correct {B X Y : Type*}
    [AddCommGroup B] [Module ℂ B] [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] [FiniteDimensional ℂ Y]
    (D : B →ₗ[ℂ] X) (hd : DenseRange D) (M : X →L[ℂ] Y) (x : X) (hx : M x = 0) :
    ∃ b : ℕ → B, (∀ n, M (D (b n)) = 0) ∧ Tendsto (fun n ↦ D (b n)) atTop (𝓝 x) := by
  let J := M.toLinearMap.comp D
  obtain ⟨L, hL⟩ := J.rangeRestrict.exists_rightInverse_of_surjective J.range_rangeRestrict
  obtain ⟨v, hv, hvlim⟩ := mem_closure_iff_seq_limit.mp (hd x)
  choose a ha using hv
  have halim : Tendsto (fun n ↦ D (a n)) atTop (𝓝 x) := by simpa only [ha] using hvlim
  have hlim : Tendsto (fun n ↦ J.rangeRestrict (a n)) atTop (𝓝 0) := by
    apply tendsto_subtype_rng.mpr
    change Tendsto (fun n ↦ M (D (a n))) atTop (𝓝 0)
    rw [← hx]
    exact M.continuous.continuousAt.tendsto.comp halim
  have hsmall := ((D.comp L).continuous_of_finiteDimensional.continuousAt.tendsto.comp hlim)
  refine ⟨fun n ↦ a n - L (J.rangeRestrict (a n)), fun n ↦ ?_, ?_⟩
  · change J (_ - _) = 0
    rw [map_sub, sub_eq_zero]
    exact (congrArg Subtype.val (LinearMap.congr_fun hL (J.rangeRestrict (a n)))).symm
  · simpa only [map_sub, map_zero, sub_zero, LinearMap.comp_apply, comp_def] using halim.sub hsmall

/-- At degree greater than one, integration against every unitary character is a
continuous Fourier evaluation on the positive Sobolev space. -/
private theorem orbitalMarkushevichBasis_synthesis_eval {s : ℝ} (hs : 0 ≤ s) (hs' : 1 < s)
    (ψ : PontryaginDual C𝔽) :
    ∃ L : StrongDual ℂ W(s), ∀ x : W(s), L x = lcaFourier μ𝔽 x ψ ∧
      Integrable (fun g ↦ x g * star (ψ g : ℂ)) μ𝔽 := by
  let hm : IsModulation m𝔽 := ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
  let ν := canonicalModulatedHaar m𝔽 hm
  let : ν.IsHaarMeasure := (existsUnique_canonicalModulatedHaar m𝔽 hm).exists.choose_spec.1
  have hν : Integrable (fun g : C𝔽 ↦ ((1 + (logNorm g) ^ 2) ^ (s / 2))⁻¹) ν := by
    apply (orbitalJet_logNorm_measurePreserving (F := F)).integrable_comp_of_integrable
      (g := fun x : ℝ ↦ ((1 + x ^ 2) ^ (s / 2))⁻¹)
    simpa using orbitalJet_integrable_pow_mul_rpow_inv (k := 0) (s := s) (by simpa using hs')
  have hμ : Integrable (fun g : C𝔽 ↦ (intervalSobolevDensity 0 0 s (logNorm g))⁻¹) μ𝔽 := by
    simp_rw [orbitalJet_density_eq]
    rw [Measure.isMulLeftInvariant_eq_smul μ𝔽 ν]
    exact hν.smul_measure_nnreal
  let : IsFiniteMeasure (μ'(s)) := isFiniteMeasure_withDensity_ofReal hμ.hasFiniteIntegral
  let η (g : C𝔽) := star (ψ g : ℂ)
  have hη : MemLp η 2 (μ'(s)) := MemLp.of_bound
    ((continuous_star.comp (continuous_subtype_val.comp ψ.continuous)).aestronglyMeasurable) 1
      (.of_forall fun g ↦ by simp [η])
  let T := (modulatedIntervalSobolev_dual m𝔽 hm μ𝔽 0 0 s hI hs).exists.choose
  let L := T.symm (hη.toLp η)
  have he := orbitalJet_ae_of_ae_withDensity (s := s) hη.coeFn_toLp
  refine ⟨L, fun x ↦ ?_⟩
  obtain ⟨hi, hv⟩ := spectralSobolevPairing_dual hI hs L x
  change Integrable (fun g ↦ x g * T L g) μ𝔽 at hi
  change L x = spectralSobolevPairing x (T L) at hv
  rw [show T L = hη.toLp η from T.apply_symm_apply _] at hi hv
  exact ⟨hv.trans (integral_congr_ae (Filter.EventuallyEq.rfl.mul he)), hi.congr (Filter.EventuallyEq.rfl.mul he)⟩

/-- Fourier evaluation of a cutoff is multiplication by the Fourier transform of its
Schwartz kernel. This follows by evaluating its defining Pettis integral. -/
private theorem orbitalMarkushevichBasis_synthesis_convolution {s : ℝ} (hs : 0 ≤ s)
    (ψ : PontryaginDual C𝔽) (L : StrongDual ℂ W(s)) (hL : ∀ x, L x = lcaFourier μ𝔽 x ψ)
    (φ : SchwartzBruhat C𝔽) (x : W(s)) :
    L ((existsUnique_schwartzBruhat_zeroLineAction μ𝔽 m𝔽 s hs).exists.choose φ x) =
      lcaFourier μ𝔽 φ ψ * L x := by
  let A := (existsUnique_schwartzBruhat_zeroLineAction μ𝔽 m𝔽 s hs).exists.choose
  have hA := (existsUnique_schwartzBruhat_zeroLineAction μ𝔽 m𝔽 s hs).exists.choose_spec φ x
  have hev : L (A φ x) = ∫ g, L ((φ g) • ρ(hs) g x) ∂μ𝔽 :=
    congrArg (fun z : PettisWeakCompletion W(s) ↦
      (show Module.Dual ℂ (StrongDual ℂ W(s)) from z) L) hA.2
  have htr (g : C𝔽) : L (ρ(hs) g x) = star (ψ g : ℂ) * L x := by
    rw [hL, hL, lcaFourier, lcaFourier]
    change (∫ y, _ * _ ∂μ𝔽) = _
    rw [← integral_mul_left_eq_self (μ := μ𝔽) (fun y ↦ (ρ(hs) g x) y * star (ψ y : ℂ)) g,
      ← integral_const_mul]
    have h := (measurePreserving_mul_left μ𝔽 g).quasiMeasurePreserving.ae_eq_comp
      (hardySobolevTranslation_apply μ𝔽 m𝔽 0 0 s hI hs g x)
    apply integral_congr_ae
    filter_upwards [h] with y hy
    change (ρ(hs) g x) (g * y) = x (g⁻¹ * (g * y)) at hy
    simp only [hy, inv_mul_cancel_left, map_mul, Circle.coe_mul, star_mul]
    ring
  rw [hev, lcaFourier, ← integral_mul_const]
  apply integral_congr_ae
  refine .of_forall fun g ↦ (L.map_smul (φ g) (ρ(hs) g x)).trans ?_
  change φ g * L (ρ(hs) g x) = (φ g * star (ψ g : ℂ)) * L x
  rw [htr, mul_assoc]

/-- The completed PV operator acts on every continuous zero-line Mellin evaluation
by the reciprocal Euler product, by continuity from polar tests. -/
private theorem orbitalMarkushevichBasis_synthesis_mul (χ : PontryaginDual C𝔽) (S : Finset V)
    {s : ℝ} (hs : 0 ≤ s) (z : ℂ) (L : StrongDual ℂ W(s))
    (hL : ∀ x : W(s), L x = ∫ g, x g * ideleClassNormTwist χ z g ∂μ𝔽) :
    ∀ u : H(0, hs), L (P(S, 0, hs) u : W(s)) = reciprocalPartialHeckeEulerProduct χ S z * L u.val := by
  let E := reciprocalPartialHeckeEulerProduct χ S
  let D := globalThetaSobolevTestClass (F := F) 0 hs
  let Z (b : ℬ₀) (w : ℂ) := globalIdelicZFunction b.val (ideleClassNormTwist χ w)
  have hd : DenseRange D := (globalThetaSobolev_dense (F := F) 0 hI hs).comp
    (Submodule.mkQ_surjective _).denseRange (j(0, hs)).continuous
  have hb (b : ℬ₀) : L (D b).val = Z b z := by
    have he := (existsUnique_globalThetaSobolevEmbedding (F := F) 0 0 0 s hI hs).exists.choose_spec.2 b
    rw [modulationWeight_zero] at he
    obtain ⟨h₀, h₁⟩ := (mem_adelePolarSubspace b.val).mp b.property
    exact (hL _).trans ((integral_congr_ae (he.mul Filter.EventuallyEq.rfl)).trans
      (congrFun (globalThetaMellinIntegral_eq_continuation_of_vanishing _ h₀ h₁) _))
  let B := L.comp (H(0, hs)).subtypeL
  apply congrFun (hd.equalizer (B.comp (P(S, 0, hs))).continuous ((E z) • B).continuous ?_)
  funext b
  change L (P(S, 0, hs) (j(0, hs) (theta(b))) : W(s)) = E z * L (D b).val
  rw [globalThetaSobolevPrincipalValue_apply, hb]
  change L (D (pvTest(S, b))).val = _
  rw [hb]
  have h₁ := (globalIdelicZFunction_entire_of_vanishing _ (pvTest(S, b)).property χ).continuous.continuousAt (x := z)
  have h₂ := ((OrbitalJetIndex.isZero_analyticAt χ S z).continuousAt).mul
    ((globalIdelicZFunction_entire_of_vanishing _ b.property χ).continuous.continuousAt (x := z))
  exact ((h₁.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE h₂).mp
    ((globalPrincipalValueConverse_mellin S χ b.val).filter_mono (nhdsNE_le_codiscrete z))).eq_of_nhds

open scoped Topology ContDiff in
/-- Cut off the removable quotient on a slightly wider band. The normal form supplies
one smooth representative even where the pointwise quotient takes the value zero. -/
private theorem orbitalMarkushevichBasis_synthesis_profile (E Z : ℂ → ℂ)
    (hE : Differentiable ℂ E) (hZ : Differentiable ℂ Z) (hne : ∃ w, E w ≠ 0) (n : ℕ)
    (h : ∀ t ∈ Icc (-(n + 2 : ℝ)) (n + 2), ∃ q : ℂ → ℂ, AnalyticAt ℂ q (frequency(t)) ∧
      Z =ᶠ[𝓝 (frequency(t))] E * q) :
    ∃ H : SchwartzMap ℝ ℂ, ∀ t ∈ Icc (-(n : ℝ)) n, Z (frequency(t)) = E (frequency(t)) * H t := by
  let Q := toMeromorphicNFOn (Z / E) univ
  have hm : MeromorphicOn (Z / E) univ := fun z _ ↦ (hZ.analyticAt z).meromorphicAt.div (hE.analyticAt z).meromorphicAt
  have hQ (t : ℝ) (ht : t ∈ Icc (-(n + 2 : ℝ)) (n + 2)) :
      AnalyticAt ℂ Q (frequency(t)) ∧ Z (frequency(t)) = E (frequency(t)) * Q (frequency(t)) := by
    let w := frequency(t)
    obtain ⟨q, hq, heq⟩ := h t ht
    have hpunct : ∀ᶠ z in 𝓝[≠] w, E z ≠ 0 :=
      (hE.analyticAt w).eventually_eq_zero_or_eventually_ne_zero.resolve_left
        (fun hz ↦ orbitalMarkushevichBasis_synthesis_order E hE hne w (analyticOrderAt_eq_top.mpr hz))
    have hloc : Q =ᶠ[𝓝 w] q := by
      apply ((meromorphicNFOn_toMeromorphicNFOn (Z / E) univ (mem_univ w)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
        hq.meromorphicNFAt).mp
      apply (hm.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ w)).trans
      filter_upwards [hpunct, heq.filter_mono nhdsWithin_le_nhds] with z hn hz
      change Z z / E z = q z
      rw [hz, Pi.mul_apply]
      field_simp
    exact ⟨(analyticAt_congr hloc).mpr hq, by rw [hloc.eq_of_nhds]; exact heq.eq_of_nhds⟩
  let B : ContDiffBump (0 : ℝ) := ⟨n + 1, n + 2, by positivity, by linarith⟩
  let p (t : ℝ) := B t • Q (frequency(t))
  have hp : ContDiff ℝ (∞) p := by
    apply contDiff_iff_contDiffAt.mpr
    intro t
    by_cases ht : t ∈ tsupport B
    · have hb := B.tsupport_eq ▸ ht
      have hbound : |t| ≤ n + 2 := by simpa [B, Real.norm_eq_abs] using (mem_closedBall_zero_iff.mp hb)
      exact B.contDiff.contDiffAt.smul (((hQ t (abs_le.mp hbound)).1.restrictScalars (𝕜 := ℝ)).contDiffAt.comp t
        (Complex.ofRealCLM.contDiff.contDiffAt.mul contDiffAt_const : ContDiffAt ℝ (∞) (fun y : ℝ ↦ frequency(y)) t))
    · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp ht] with y hy
      simp [p, hy]
  have hpc : HasCompactSupport p := B.hasCompactSupport.smul_right
  refine ⟨hpc.toSchwartzMap hp, fun t ht ↦ ?_⟩
  have ht' := abs_le.mpr ht
  change Z (frequency(t)) = E (frequency(t)) * (B t • _)
  rw [B.one_of_mem_closedBall (by rw [mem_closedBall_zero_iff, Real.norm_eq_abs]; exact ht'.trans (by dsimp [B]; linarith)), one_smul]
  exact (hQ t ⟨by linarith [ht.1], by linarith [ht.2]⟩).2

open scoped FourierTransform in
/-- With angular frequency t, the inverse transform represents a Schwartz profile
by integration against exp(itx) with respect to Lebesgue measure. -/
private theorem orbitalMarkushevichBasis_synthesis_inverse (H : SchwartzMap ℝ ℂ) :
    ∃ g : SchwartzMap ℝ ℂ, ∀ t : ℝ,
      (∫ x : ℝ, g x * Complex.exp ((x : ℂ) * frequency(t))) = H t := by
  let e := (LinearEquiv.smulOfNeZero ℝ ℝ (-2 * Real.pi) (mul_ne_zero (by norm_num) Real.pi_ne_zero)).toContinuousLinearEquiv
  let K := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e H
  let g := (FourierTransform.fourierCLE ℂ (SchwartzMap ℝ ℂ)).symm K
  have hft : 𝓕 g = K := (FourierTransform.fourierCLE ℂ (SchwartzMap ℝ ℂ)).apply_symm_apply _
  refine ⟨g, fun t ↦ ?_⟩
  let w := t / (-2 * Real.pi)
  have hval := congrArg (fun f : SchwartzMap ℝ ℂ ↦ f w) hft
  change 𝓕 (g : ℝ → ℂ) w = H ((-2 * Real.pi) * w) at hval
  have hw : (-2 * Real.pi) * w = t := by dsimp [w]; field_simp
  rw [hw, Real.fourier_real_eq_integral_exp_smul] at hval
  refine (integral_congr_ae (.of_forall fun x ↦ ?_)).trans hval
  have hexp : -2 * Real.pi * x * w = x * t := by rw [← hw]; ring
  rw [hexp, Complex.ofReal_mul, smul_eq_mul, mul_comm (g x), mul_assoc]

/-- Integrating an inverse-character Schwartz profile along log norm realizes its
ordinary Fourier transform on the corresponding Mellin line. The Haar scalar
accounts for the normalization of Lebesgue measure. -/
private theorem orbitalMarkushevichBasis_synthesis_lift (χ : PontryaginDual C𝔽)
    (s : ℝ) (H : SchwartzMap ℝ ℂ) :
    ∃ v : W(s), ∀ t : ℝ, (∫ x, v x * ideleClassNormTwist χ (frequency(t)) x ∂μ𝔽) = H t := by
  let hm : IsModulation m𝔽 := ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
  let ν := canonicalModulatedHaar m𝔽 hm
  let : ν.IsHaarMeasure := (existsUnique_canonicalModulatedHaar m𝔽 hm).exists.choose_spec.1
  let c : ℂ := (Measure.haarScalarFactor μ𝔽 ν : ℝ)
  have hc : c ≠ 0 := Complex.ofReal_ne_zero.mpr
    (by exact_mod_cast (Measure.haarScalarFactor_pos_of_isHaarMeasure μ𝔽 ν).ne')
  obtain ⟨g, hg⟩ := orbitalMarkushevichBasis_synthesis_inverse (c⁻¹ • H)
  let a (x : C𝔽) := (χ x : ℂ)⁻¹ * g (logNorm x)
  have ha : Continuous a := ((continuous_subtype_val.comp χ.continuous).inv₀ fun x ↦
    Circle.coe_ne_zero _).mul (g.continuous.comp orbitalJet_logNorm_continuous)
  let d (y : ℝ) := (1 + y ^ 2) ^ (s / 2)
  have hd (x : C𝔽) : intervalSobolevDensity 0 0 s (logNorm x) = d (logNorm x) :=
    inv_injective (orbitalJet_density_eq s x)
  have hdpos (x : ℝ) : 0 < d x := Real.rpow_pos_of_pos (by positivity) _
  have hdc : Continuous d := (continuous_const.add (continuous_id.pow 2)).rpow_const
    fun x ↦ .inl (by dsimp; positivity)
  have hmeas : MemLp a 2 (intervalSobolevMeasure μ𝔽 logNorm 0 0 s) := by
    change MemLp a 2 ((μ𝔽).withDensity fun x ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (logNorm x)))
    simp_rw [hd]
    apply (memLp_two_iff_integrable_sq_norm ha.aestronglyMeasurable).mpr
    apply (integrable_withDensity_iff ((hdc.comp orbitalJet_logNorm_continuous).measurable.ennreal_ofReal)
      (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)).mpr
    let w (x : ℝ) := (1 + ‖x‖ ^ 2) ^ (s / 4)
    have hw := Function.hasTemperateGrowth_one_add_norm_sq_rpow ℝ (s / 4)
    let G := SchwartzMap.smulLeftCLM ℂ w g
    have hwg := (memLp_two_iff_integrable_sq_norm G.continuous.aestronglyMeasurable).mp (G.memLp 2 volume)
    have hreal : Integrable (fun x : ℝ ↦ d x * ‖g x‖ ^ 2) volume := hwg.congr (.of_forall fun x ↦ by
      change ‖SchwartzMap.smulLeftCLM ℂ w g x‖ ^ 2 = _
      rw [SchwartzMap.smulLeftCLM_apply_apply hw, norm_smul, mul_pow, Real.norm_of_nonneg
        (show 0 ≤ w x from Real.rpow_nonneg (by positivity) _)]
      dsimp only [w, d]
      rw [Real.norm_eq_abs, sq_abs, ← Real.rpow_mul_natCast (by positivity : 0 ≤ 1 + x ^ 2)]
      congr 2
      ring)
    have hi : Integrable (fun x : C𝔽 ↦ d (logNorm x) * ‖g (logNorm x)‖ ^ 2) ν :=
      (orbitalJet_logNorm_measurePreserving (F := F)).integrable_comp_of_integrable hreal
    rw [Measure.isMulLeftInvariant_eq_smul μ𝔽 ν]
    apply Integrable.smul_measure_nnreal
    apply hi.congr
    exact .of_forall fun x ↦ by simp [a, ENNReal.toReal_ofReal (hdpos _).le, mul_comm]
  refine ⟨hmeas.toLp a, fun t ↦ ?_⟩
  have habs : μ𝔽 ≪ intervalSobolevMeasure μ𝔽 logNorm 0 0 s := by
    change μ𝔽 ≪ (μ𝔽).withDensity fun x ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (logNorm x))
    simp_rw [hd]
    exact withDensity_absolutelyContinuous' ((hdc.comp orbitalJet_logNorm_continuous).measurable.ennreal_ofReal.aemeasurable)
      (.of_forall fun x ↦ (ENNReal.ofReal_pos.mpr (hdpos _)).ne')
  let h (r : ℝ) := g r * Complex.exp ((r : ℂ) * frequency(t))
  have hraw (x : C𝔽) : a x * ideleClassNormTwist χ (frequency(t)) x = h (logNorm x) := by
    have hp := NNReal.coe_pos.mpr (Units.zero_lt (ideleClassNorm F x))
    change ((χ x : ℂ)⁻¹ * g (logNorm x)) * ((χ x : ℂ) * (((ideleClassNorm F x).val : ℝ) : ℂ) ^ (frequency(t))) = h (logNorm x)
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne'), ← Complex.ofReal_log hp.le]
    dsimp only [h, logIdeleClassNorm]
    field_simp
  refine (integral_congr_ae ((habs.ae_eq hmeas.coeFn_toLp).mul (Filter.EventuallyEq.rfl (f := fun x ↦ ideleClassNormTwist χ (frequency(t)) x)))).trans ?_
  change (∫ x, a x * ideleClassNormTwist χ (frequency(t)) x ∂μ𝔽) = _
  simp_rw [hraw]
  rw [Measure.isMulLeftInvariant_eq_smul μ𝔽 ν, integral_smul_nnreal_measure]
  have hl := orbitalJet_logNorm_measurePreserving (F := F)
  have hr : (∫ x, h (logNorm x) ∂ν) = ∫ y, h y := by
    conv_rhs => rw [← hl.map_eq, integral_map hl.measurable.aemeasurable
      (show Continuous h from g.continuous.mul (Complex.continuous_exp.comp
        (Complex.continuous_ofReal.mul continuous_const))).aestronglyMeasurable]
  rw [hr, show ∫ y, h y = (c⁻¹ • H) t from hg t]
  change c * (c⁻¹ * H t) = H t
  rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]

/-- The Fourier character in the band based at the inverse lift corresponds to
Mellin height minus its band parameter. -/
private theorem orbitalMarkushevichBasis_synthesis_twist (χ ψ : PontryaginDual C𝔽) (t : ℝ)
    (h : ∀ x, ψ x = χ⁻¹ x * Circle.exp (t * logNorm x)) (x : C𝔽) :
    star (ψ x : ℂ) = ideleClassNormTwist χ (frequency(-t)) x := by
  have hp := NNReal.coe_pos.mpr (Units.zero_lt (ideleClassNorm F x))
  change _ = (χ x : ℂ) * (((ideleClassNorm F x).val : ℝ) : ℂ) ^ (frequency(-t))
  rw [h, Circle.coe_mul, star_mul]
  rw [show (χ⁻¹ x : ℂ) = star (χ x : ℂ) from Circle.coe_inv_eq_conj _, star_star,
    Complex.star_def, ← Circle.coe_inv_eq_conj, ← Circle.exp_neg, Circle.coe_exp,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne'), ← Complex.ofReal_log hp.le]
  rw [mul_comm _ (χ x : ℂ)]
  congr 2
  push_cast
  dsimp only [logIdeleClassNorm]
  ring

/-- Fourier samples distinguish zero-line Sobolev vectors of degree greater than
one, since the underlying functions are integrable for Haar measure. -/
private theorem orbitalMarkushevichBasis_synthesis_ext {s : ℝ} (hs : 0 ≤ s) (hs' : 1 < s)
    (x y : W(s)) (h : ∀ ψ, lcaFourier μ𝔽 x ψ = lcaFourier μ𝔽 y ψ) : x = y := by
  obtain ⟨L, hL⟩ := orbitalMarkushevichBasis_synthesis_eval (F := F) hs hs' 1
  have hi (v : W(s)) : Integrable (v : C𝔽 → ℂ) μ𝔽 := by simpa using (hL v).2
  obtain ⟨U, hU, hinj, -⟩ := lcaFourier_L1 (G := C𝔽) μ𝔽
  have he (v : W(s)) (ψ : PontryaginDual C𝔽) : U ((hi v).toL1 _) ψ = lcaFourier μ𝔽 v ψ :=
    (hU _ _).trans (integral_congr_ae ((hi v).coeFn_toL1.mul Filter.EventuallyEq.rfl))
  have eq := hinj (show U ((hi x).toL1 _) = U ((hi y).toL1 _) from
    ZeroAtInftyContinuousMap.ext fun ψ ↦ (he x ψ).trans ((h ψ).trans (he y ψ).symm))
  apply Lp.ext
  apply (withDensity_absolutelyContinuous μ𝔽 _).ae_eq
  exact (hi x).coeFn_toL1.symm.trans (eq ▸ (hi y).coeFn_toL1)

/-- A band-limited convolution of a polar test with locally divisible Mellin transform
has an exact principal-value preimage. Cut off the holomorphic quotient, lift its inverse
Fourier transform and apply the same convolution to that lift. -/
private theorem orbitalMarkushevichBasis_synthesis_cutoff (χ : PontryaginDual C𝔽)
    (S : Finset V) {s : ℝ} (hs : 0 ≤ s) (hs' : 1 < s)
    (hχ : ∀ v ∈ S, (ideleClassNormTwist χ 0).IsUnramifiedAt v)
    (n : ℕ) (φ : SchwartzBruhat C𝔽)
    (hφ : tsupport (lcaFourier μ𝔽 φ) ⊆ modulatedFrequencyBand m𝔽 χ⁻¹ (-(n : ℝ)) n)
    (b : ℬ₀) (hq : ∀ t ∈ Icc (-(n + 2 : ℝ)) (n + 2), ∃ q : ℂ → ℂ, AnalyticAt ℂ q (frequency(t)) ∧
      (fun z ↦ globalIdelicZFunction b.val (ideleClassNormTwist χ z)) =ᶠ[nhds (frequency(t))]
        reciprocalPartialHeckeEulerProduct χ S * q) :
    ∃ u : H(0, hs), (P(S, 0, hs) u : W(s)) =
      (existsUnique_schwartzBruhat_zeroLineAction μ𝔽 m𝔽 s hs).exists.choose φ
        (j(0, hs) (theta(b)) : W(s)) := by
  let E := reciprocalPartialHeckeEulerProduct χ S
  let Z (z : ℂ) := globalIdelicZFunction b.val (ideleClassNormTwist χ z)
  have hd : Differentiable ℂ E := fun z ↦ (OrbitalJetIndex.isZero_analyticAt χ S z).differentiableAt
  let profile := orbitalMarkushevichBasis_synthesis_profile E Z hd
    (globalIdelicZFunction_entire_of_vanishing _ b.property χ)
    ⟨1, fun h ↦ one_ne_zero (orbitalEulerZero_re_eq_zero χ S hχ h)⟩ n hq
  let H := profile.choose
  have hH := profile.choose_spec
  let lift := orbitalMarkushevichBasis_synthesis_lift χ s H
  let v := lift.choose
  have hv := lift.choose_spec
  let A := (existsUnique_schwartzBruhat_zeroLineAction μ𝔽 m𝔽 s hs).exists.choose φ
  let u : H(0, hs) := ⟨A v, denseRange_globalTheta_zeroLine hs (A v)⟩
  let D : W(s) := j(0, hs) (theta(b))
  refine ⟨u, orbitalMarkushevichBasis_synthesis_ext hs hs' _ _ fun ψ ↦ ?_⟩
  let e := orbitalMarkushevichBasis_synthesis_eval hs hs' ψ
  let L := e.choose
  have hL := e.choose_spec
  have hc (x) : L (A x) = lcaFourier μ𝔽 φ ψ * L x :=
    orbitalMarkushevichBasis_synthesis_convolution hs ψ L (fun y ↦ (hL y).1) φ x
  refine (hL (P(S, 0, hs) u : W(s))).1.symm.trans ((Eq.trans ?_ (hc D).symm).trans (hL (A D)).1)
  have hsample (ξ : PontryaginDual C𝔽) (t : ℝ)
      (he : ∀ g, star (ψ g : ℂ) = ideleClassNormTwist ξ (frequency(t)) g) (x : W(s)) :
      L x = ∫ g, x g * ideleClassNormTwist ξ (frequency(t)) g ∂μ𝔽 :=
    (hL x).1.trans (integral_congr_ae (.of_forall fun g ↦ congrArg (x g * ·) (he g)))
  by_cases hmem : ψ ∈ modulatedFrequencyBand m𝔽 χ⁻¹ (-(n : ℝ)) n
  · obtain ⟨t, ht, htψ⟩ := hmem
    have h := hsample χ (-t) (orbitalMarkushevichBasis_synthesis_twist χ ψ t htψ)
    rw [orbitalMarkushevichBasis_synthesis_mul χ S hs (frequency(-t)) L h u, hc v, h v, hv]
    have hθ := (existsUnique_globalThetaSobolevEmbedding (F := F) 0 0 0 s hI hs).exists.choose_spec.2 b
    rw [modulationWeight_zero] at hθ
    obtain ⟨h₀, h₁⟩ := (mem_adelePolarSubspace b.val).mp b.property
    have hb : L D = Z (frequency(-t)) := (h D).trans
      ((integral_congr_ae (hθ.mul Filter.EventuallyEq.rfl)).trans
        (congrFun (globalThetaMellinIntegral_eq_continuation_of_vanishing _ h₀ h₁) _))
    rw [hb, hH (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩]
    ring
  · have hzero := image_eq_zero_of_notMem_tsupport (fun h ↦ hmem (hφ h))
    have h := hsample ψ⁻¹ 0 (fun g ↦ by
      change star (ψ g : ℂ) = (ψ⁻¹ g : ℂ) * (((ideleClassNorm F g).val : ℝ) : ℂ) ^ (frequency(0))
      simp only [Complex.ofReal_zero, zero_mul, Complex.cpow_zero, mul_one]
      exact (Circle.coe_inv_eq_conj _).symm)
    rw [orbitalMarkushevichBasis_synthesis_mul ψ⁻¹ S hs (frequency(0)) L h u, hc v, hzero, zero_mul, mul_zero, zero_mul]

/-- For one cutoff, correct theta tests in the finitely many moments on its band.
Their principal-value preimages put the cutoff of the limiting vector in the closed image. -/
private theorem orbitalMarkushevichBasis_synthesis_onBand (χ : PontryaginDual C𝔽) (S : Finset V)
    {s : ℝ} (hs : 0 ≤ s) (hS : S.Nonempty) (hc : 2 * (S.card : ℝ) ≤ s)
    (hχ : ∀ v ∈ S, (ideleClassNormTwist χ 0).IsUnramifiedAt v)
    (f : W(s)) (hf : ∀ j : OrbitalJetIndex χ S s, spectralSobolevPairing f (jetLp(χ, S, hs, j)) = 0)
    (n : ℕ) (φ : SchwartzBruhat C𝔽)
    (hband : tsupport (lcaFourier μ𝔽 φ) ⊆ modulatedFrequencyBand m𝔽 χ⁻¹ (-(n : ℝ)) n) :
    (existsUnique_schwartzBruhat_zeroLineAction μ𝔽 m𝔽 s hs).exists.choose φ f ∈
      ((H(0, hs)).subtype.comp (P(S, 0, hs)).toLinearMap).range.topologicalClosure := by
  classical
  let D := (H(0, hs)).subtype.comp (globalThetaSobolevTestClass (F := F) 0 hs)
  have hd : DenseRange D := by
    intro x
    apply closure_mono (t := range D) _ (denseRange_globalTheta_zeroLine hs x)
    rintro _ ⟨u, rfl⟩
    obtain ⟨b, hb⟩ := Submodule.mkQ_surjective
      ((LinearMap.ker (adelicThetaLinearMap F)).comap (adelePolarSubspace F).subtype) u
    exact ⟨b, congrArg (fun u : GlobalPolarFreeThetaSpace F ↦ (j(0, hs) u : W(s))) hb⟩
  let A := (existsUnique_schwartzBruhat_zeroLineAction μ𝔽 m𝔽 s hs).exists.choose
  let jets := orbitalMarkushevichBasis_synthesis_band χ S hc hχ (n + 2)
  let J := jets.choose
  have hJ := jets.choose_spec
  let T := (modulatedIntervalSobolev_dual m𝔽
    ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ μ𝔽 0 0 s hI hs).exists.choose
  let M : W(s) →L[ℂ] (J → ℂ) := ContinuousLinearMap.pi (fun j ↦ T.symm (jetLp(χ, S, hs, j.val)))
  have hM (x : W(s)) (j : J) : M x j = spectralSobolevPairing x (jetLp(χ, S, hs, j.val)) :=
    (spectralSobolevPairing_dual hI hs (T.symm (jetLp(χ, S, hs, j.val))) x).2.trans
      (congrArg (spectralSobolevPairing x) (T.apply_symm_apply _))
  let approx := orbitalMarkushevichBasis_synthesis_correct (B := ℬ₀) (X := W(s)) (Y := J → ℂ) D hd M f
    (funext fun j ↦ (hM _ j).trans (hf j.val))
  let b := approx.choose
  have hb := approx.choose_spec.1
  have hbto := approx.choose_spec.2
  apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto
    ((A φ).continuous.continuousAt.tendsto.comp hbto)
  apply Filter.Eventually.of_forall
  intro l
  have hs' : 1 < s := by
    have : (1 : ℝ) ≤ S.card := by exact_mod_cast Nat.succ_le_of_lt (Finset.card_pos.mpr hS)
    linarith
  obtain ⟨u, hu⟩ := orbitalMarkushevichBasis_synthesis_cutoff χ S hs hs' hχ n φ hband (b l)
    (fun t ht ↦ orbitalMarkushevichBasis_synthesis_germ χ S hs hχ (b l) t (fun k hk ↦ by
      obtain ⟨j, hj, he⟩ := hJ t ht k hk
      exact ⟨j, he, (hM (D (b l)) ⟨j, hj⟩).symm.trans (congrFun (hb l) ⟨j, hj⟩)⟩))
  exact Submodule.le_topologicalClosure _ ⟨u, hu⟩

/-- Every isotypic vector with zero admitted moments can be approximated in Sobolev norm
by principal values. Commutativity of the square on p. 486 gives the forward inclusion.
For the converse one needs density of the Euler multiplier image in this joint kernel. -/
private theorem orbitalMarkushevichBasis_synthesis (χ : PontryaginDual C𝔽) (S : Finset V)
    {s : ℝ} (hs : 0 ≤ s) (hS : S.Nonempty) (hc : 2 * (S.card : ℝ) ≤ s)
    (hχ : ∀ v ∈ S, (ideleClassNormTwist χ 0).IsUnramifiedAt v)
    (f : Wω(hs, χ.comp restriction))
    (hf : ∀ j : OrbitalJetIndex χ S s, spectralSobolevPairing f.val (jetLp(χ, S, hs, j)) = 0) :
    f ∈ N(S, hs, χ.comp restriction) := by
  classical
  let V₀ := ((H(0, hs)).subtype.comp (P(S, 0, hs)).toLinearMap).range.topologicalClosure
  obtain ⟨φ, U, -, -, hband, hU, hlim⟩ := exists_spectralLineIsotypeConvolution χ hs
  change f.val ∈ V₀
  apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto
    (continuous_subtype_val.continuousAt.tendsto.comp (hlim f))
  apply Filter.Eventually.of_forall
  intro n
  change (U n f).val ∈ V₀
  rw [hU]
  exact orbitalMarkushevichBasis_synthesis_onBand χ S hs hS hc hχ f.val hf n (φ n) (hband n)

/-- The logarithmic Sobolev weight has polynomial growth, so Schwartz functions
embed continuously and densely in its scalar weighted L² space. -/
private theorem orbitalMarkushevichBasis_singleJet_denseSpan_weight (c : ℝ≥0) {s : ℝ} (hs : 0 ≤ s) :
    let w (x : ℝ) := intervalSobolevDensity 0 0 s x
    ((c • (volume : Measure ℝ)).withDensity fun x ↦ ENNReal.ofReal (w x)).HasTemperateGrowth := by
  intro w
  obtain ⟨n, hn⟩ := exists_nat_ge s
  have hw (x : ℝ) : w x = (1 + x ^ 2) ^ (s / 2) := by simp [w, intervalSobolevDensity]
  have hc : Continuous w := by rw [funext hw]; fun_prop (disch := positivity)
  refine ⟨n + 2, ?_⟩
  apply (integrable_withDensity_iff hc.measurable.ennreal_ofReal (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)).2
  have hi : Integrable (fun x : ℝ ↦ (1 + ‖x‖) ^ (-(2 : ℝ))) volume :=
    integrable_one_add_norm (by norm_num)
  apply hi.smul_measure_nnreal.mono'
  · apply AEStronglyMeasurable.mul
    · exact ((continuous_const.add continuous_norm).rpow_const fun x : ℝ ↦
        Or.inl (show 1 + ‖x‖ ≠ 0 by positivity)).aestronglyMeasurable
    · exact hc.measurable.ennreal_ofReal.ennreal_toReal.aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro x
    have hpos : 0 < 1 + ‖x‖ := by positivity
    have h1 : 1 + x ^ 2 ≤ (1 + ‖x‖) ^ 2 := by
      rw [Real.norm_eq_abs]; nlinarith [abs_nonneg x, sq_abs x]
    have hbound : w x ≤ (1 + ‖x‖) ^ (n : ℝ) := calc
      w x ≤ ((1 + ‖x‖) ^ 2) ^ (s / 2) := hw x ▸ Real.rpow_le_rpow (by positivity) h1 (by linarith)
      _ = (1 + ‖x‖) ^ s := by rw [← Real.rpow_two, ← Real.rpow_mul hpos.le]; ring_nf
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg x]) hn
    rw [ENNReal.toReal_ofReal (by rw [hw]; positivity), Real.norm_of_nonneg (by rw [hw]; positivity)]
    convert mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg hpos.le (-(↑(n + 2) : ℝ))) using 1
    rw [← Real.rpow_add hpos]
    push_cast
    ring_nf

/-- Continuous representatives in the positive isotype are inverse-character
multiples of continuous log-norm profiles. Such representatives are dense. -/
private theorem orbitalMarkushevichBasis_singleJet_denseSpan_continuous (χ : PontryaginDual C𝔽)
    {s : ℝ} (hs : 0 ≤ s) :
    Dense {y : Wω(hs, χ.comp restriction) | ∃ p : ℝ → ℂ, Continuous p ∧
      (y.val : C𝔽 → ℂ) =ᵐ[μ𝔽] fun x ↦ (χ x : ℂ)⁻¹ * p (logNorm x)} := by
  let A := (existsUnique_spectralLineTestCompletion (F := F) 0 hs (χ.comp restriction)).exists
  apply A.choose_spec.2.1.mono
  rintro _ ⟨φ, rfl⟩
  let f := φ.val.val
  have hf : ((A.choose φ).val : C𝔽 → ℂ) =ᵐ[μ𝔽] f := by
    simpa only [modulationWeight_zero] using A.choose_spec.1 φ
  let φ₀ := modulatedExponentialDecayTwist m𝔽 univ ⟨0, mem_univ _⟩ φ.val
  have hcont : Continuous f := by
    have h := continuous_of_bruhatSmooth (schwartzBruhat_isBruhatSmooth φ₀)
    change Continuous (modulationWeight m𝔽 0 f) at h
    rwa [modulationWeight_zero] at h
  have he (k : C₁) (x : C𝔽) : f (k.val⁻¹ * x) = (χ k.val : ℂ) * f x := by
    let u := (A.choose φ).val
    have hk := (mem_actionIsotype _ _ _).mp (A.choose φ).property k
    change ρ(hs) k.val u = (χ k.val : ℂ) • u at hk
    have ht := hardySobolevTranslation_apply μ𝔽 m𝔽 0 0 s hI hs k.val u
    rw [hk] at ht
    have hpos : μ𝔽 ≪ (μ𝔽).withDensity (fun g ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (logNorm g))) := by
      apply withDensity_absolutelyContinuous'
      · have h := (orbitalJet_density_continuous (F := F) s).measurable.inv
        simpa only [Pi.inv_apply, inv_inv] using h.ennreal_ofReal.aemeasurable
      · exact .of_forall fun g ↦ (ENNReal.ofReal_pos.mpr (inv_pos.mp (orbitalJet_density_pos s g))).ne'
    have hh : (fun z ↦ f (k.val⁻¹ * z)) =ᵐ[μ𝔽] fun z ↦ (χ k.val : ℂ) * f z := by
      filter_upwards [(measurePreserving_mul_left μ𝔽 k.val⁻¹).quasiMeasurePreserving.ae_eq_comp hf,
        ht, hpos.ae_le (Lp.coeFn_smul (χ k.val : ℂ) u), hf] with z hz ht' hs' hf'
      exact hz.symm.trans (ht'.symm.trans (hs'.trans (congrArg ((χ k.val : ℂ) * ·) hf')))
    exact congrFun (Measure.eq_of_ae_eq hh (hcont.comp (continuous_const.mul continuous_id))
      (continuous_const.mul hcont)) x
  let e := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
  let σ (t : ℝ) : C𝔽 := QuotientGroup.mk (canonicalIdeleNormSection F (e t))
  have hσ : Continuous σ := QuotientGroup.continuous_mk.comp
    ((canonicalIdeleNormSection_continuous F).comp e.continuous)
  have hσnorm (x : C𝔽) : ideleClassNorm F (σ (logNorm x)) = ideleClassNorm F x := by
    rw [show ideleClassNorm F (σ (logNorm x)) = e (logNorm x) from canonicalIdeleNormSection_rightInverse F _]
    apply Units.ext
    apply NNReal.eq
    change Real.exp (Real.log _) = _
    exact Real.exp_log (NNReal.coe_pos.mpr (Units.zero_lt _))
  refine ⟨fun t ↦ (χ (σ t) : ℂ) * f (σ t),
    ((continuous_subtype_val.comp χ.continuous).comp hσ).mul (hcont.comp hσ), hf.trans (.of_forall fun x ↦ ?_)⟩
  let y := σ (logNorm x)
  let k : C₁ := ⟨y * x⁻¹, by change ideleClassNorm F (y * x⁻¹) = 1; rw [map_mul, map_inv, hσnorm, mul_inv_cancel]⟩
  have hky : k.val⁻¹ * y = x := by dsimp [k]; group
  change f x = (χ x : ℂ)⁻¹ * ((χ y : ℂ) * f y)
  calc
    f x = (χ k.val : ℂ) * f y := hky ▸ he k y
    _ = _ := by
      change (χ (y * x⁻¹) : ℂ) * f y = _
      simp only [map_mul, map_inv, Circle.coe_mul, Circle.coe_inv]
      ring

/-- Pulling scalar Schwartz functions back along log-norm and multiplying by the
inverse character gives a continuous map with dense range in the positive isotype. -/
private theorem orbitalMarkushevichBasis_singleJet_denseSpan_lift (χ : PontryaginDual C𝔽)
    {s : ℝ} (hs : 0 ≤ s) :
    ∃ T : SchwartzMap ℝ ℂ →L[ℂ] Wω(hs, χ.comp restriction), DenseRange T ∧
      ∀ p, ((T p).val : C𝔽 → ℂ) =ᵐ[μ𝔽] fun x ↦ (χ x : ℂ)⁻¹ * p (logNorm x) := by
  have hm : IsModulation m𝔽 := ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
  let ν := canonicalModulatedHaar m𝔽 hm
  let : ν.IsHaarMeasure := (existsUnique_canonicalModulatedHaar m𝔽 hm).exists.choose_spec.1
  let c := Measure.haarScalarFactor μ𝔽 ν
  have hl : MeasurePreserving logNorm μ𝔽 (c • volume) := by
    rw [Measure.isMulLeftInvariant_eq_smul μ𝔽 ν]
    exact orbitalJet_logNorm_measurePreserving.smul_measure _
  let w := intervalSobolevDensity 0 0 s
  have hw (x : ℝ) : w x = (1 + x ^ 2) ^ (s / 2) := by simp [w, intervalSobolevDensity]
  have hc : Continuous w := by rw [funext hw]; fun_prop (disch := positivity)
  have hp (x : ℝ) : 0 < w x := by rw [hw]; positivity
  let η := (c • (volume : Measure ℝ)).withDensity (fun x ↦ ENNReal.ofReal (w x))
  let μ := (μ𝔽).withDensity (fun x ↦ ENNReal.ofReal (w (logNorm x)))
  have hpres : MeasurePreserving logNorm μ η := by
    refine ⟨hl.measurable, ?_⟩
    ext b hb
    rw [Measure.map_apply hl.measurable hb, withDensity_apply _ (hl.measurable hb), withDensity_apply _ hb]
    exact hl.setLIntegral_comp_preimage hb hc.measurable.ennreal_ofReal
  have hac : μ𝔽 ≪ μ := withDensity_absolutelyContinuous'
    (hc.measurable.comp hl.measurable).ennreal_ofReal.aemeasurable
    (.of_forall fun x ↦ (ENNReal.ofReal_pos.mpr (hp _)).ne')
  let P := Lp.compMeasurePreservingₗᵢ (E := ℂ) (p := 2) ℂ logNorm hpres
  let v (x : C𝔽) := ((χ x)⁻¹ : Circle).val
  have hv : MemLp v ⊤ μ := memLp_top_of_bound
    (continuous_subtype_val.comp χ.continuous.inv).aestronglyMeasurable 1
    (.of_forall fun x ↦ (Circle.norm_coe _).le)
  let B := ContinuousLinearMap.mul ℂ ℂ
  let L := ((B.holderL μ ⊤ 2 2) (hv.toLp v)).comp P.toContinuousLinearMap
  have hL (p : Lp ℂ 2 η) : (L p : C𝔽 → ℂ) =ᵐ[μ𝔽] fun x ↦ (χ x : ℂ)⁻¹ * p (logNorm x) := by
    apply hac.ae_le
    filter_upwards [B.coeFn_holder (r := 2) (hv.toLp v) (P p), hv.coeFn_toLp,
      Lp.coeFn_compMeasurePreserving p hpres] with x hx hvx hpx
    change L p x = (hv.toLp v) x * P p x at hx
    change P p x = p (logNorm x) at hpx
    rw [hx, hvx, hpx]
    exact congrArg (· * p (logNorm x)) (Circle.coe_inv _)
  have hmem (p : Lp ℂ 2 η) : L p ∈ Wω(hs, χ.comp restriction) := by
    apply (mem_actionIsotype _ _ _).2
    intro k
    apply Lp.ext
    apply (withDensity_absolutelyContinuous μ𝔽 _).ae_le
    have ht := (hardySobolevTranslation_apply μ𝔽 m𝔽 0 0 s hI hs k.val (L p)).trans
      ((measurePreserving_mul_left μ𝔽 k.val⁻¹).quasiMeasurePreserving.ae_eq_comp (hL p))
    filter_upwards [ht, hac.ae_le (Lp.coeFn_smul (χ k.val : ℂ) (L p)), hL p] with x hx hsx hpx
    change ρ(hs) k.val (L p) x = ((χ k.val : ℂ) • L p) x
    rw [hx, hsx, Pi.smul_apply, smul_eq_mul, hpx]
    dsimp only [Function.comp_apply, logIdeleClassNorm]
    rw [map_mul (ideleClassNorm F), map_inv (ideleClassNorm F),
      show ideleClassNorm F k.val = 1 from k.property, inv_one, one_mul]
    simp only [map_mul, map_inv, Circle.coe_mul, Circle.coe_inv, mul_inv_rev, inv_inv]
    ring
  let R := L.codRestrict Wω(hs, χ.comp restriction) hmem
  have hd : DenseRange R := by
    apply (orbitalMarkushevichBasis_singleJet_denseSpan_continuous χ hs).mono
    rintro y ⟨p, hpc, hy⟩
    have hcomp : MemLp (p ∘ logNorm) 2 μ := by
      apply (Lp.memLp y.val).mono (hpc.comp orbitalJet_logNorm_continuous).aestronglyMeasurable
      filter_upwards [(withDensity_absolutelyContinuous μ𝔽 _).ae_le hy] with x hx
      simp [hx]
    have hm : MemLp p 2 η := by
      rw [← hpres.map_eq]
      exact (memLp_map_measure_iff hpc.aestronglyMeasurable hpres.aemeasurable).2 hcomp
    refine ⟨hm.toLp p, Subtype.ext (Lp.ext ?_)⟩
    apply (withDensity_absolutelyContinuous μ𝔽 _).ae_le
    filter_upwards [hL (hm.toLp p), hac.ae_le (hpres.quasiMeasurePreserving.ae_eq_comp hm.coeFn_toLp),
      hy] with x hx hp hyx
    exact hx.trans ((congrArg ((χ x : ℂ)⁻¹ * ·) hp).trans hyx.symm)
  let : η.HasTemperateGrowth := orbitalMarkushevichBasis_singleJet_denseSpan_weight c hs
  let : IsLocallyFiniteMeasure η := IsLocallyFiniteMeasure.withDensity_ofReal hc
  let T := R.comp (SchwartzMap.toLpCLM ℂ ℂ 2 η)
  refine ⟨T, hd.comp (SchwartzMap.denseRange_toLpCLM (F := ℂ) (by simp : (2 : ENNReal) ≠ ⊤) (μ := η))
    R.continuous, fun p ↦ (hL _).trans ?_⟩
  exact hac.ae_le ((hpres.quasiMeasurePreserving.ae_eq_comp (p.coeFn_toLp 2 η)).mono
    fun x hx ↦ congrArg ((χ x : ℂ)⁻¹ * ·) hx)

/-- With Mathlib's Fourier convention a moment of order k is a nonzero
multiple of the kth derivative at frequency −t/(2π). -/
private theorem orbitalMarkushevichBasis_singleJet_denseSpan_moment (χ : PontryaginDual C𝔽)
    (S : Finset V) {s : ℝ} (hs : 0 ≤ s) (j : OrbitalJetIndex χ S s) (p : SchwartzMap ℝ ℂ)
    (y : W(s)) (hy : (y : C𝔽 → ℂ) =ᵐ[μ𝔽] fun x ↦ (χ x : ℂ)⁻¹ * p (logNorm x)) :
    spectralSobolevPairing y (jetLp(χ, S, hs, j)) = 0 ↔
      iteratedDeriv j.val.2 (FourierTransform.fourier p : SchwartzMap ℝ ℂ) (-j.val.1 / (2 * Real.pi)) = 0 := by
  let k := j.val.2
  let t := j.val.1
  let q (r : ℝ) := p r * Complex.exp ((r : ℂ) * (t : ℂ) * Complex.I) * (r : ℂ) ^ k
  have hm : IsModulation m𝔽 := ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
  let ν := canonicalModulatedHaar m𝔽 hm
  let : ν.IsHaarMeasure := (existsUnique_canonicalModulatedHaar m𝔽 hm).exists.choose_spec.1
  let c := Measure.haarScalarFactor μ𝔽 ν
  have hc : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by exact_mod_cast
    (Measure.haarScalarFactor_pos_of_isHaarMeasure μ𝔽 ν).ne')
  have hpair : spectralSobolevPairing y (jetLp(χ, S, hs, j)) = (c : ℂ) * ∫ r, q r := by
    calc
      _ = ∫ x, q (logNorm x) ∂μ𝔽 := by
        apply integral_congr_ae
        filter_upwards [hy, orbitalJet_ae_of_ae_withDensity (MemLp.coeFn_toLp (orbitalJet_memLp χ S hs j))]
          with x hx hj
        rw [hx, hj]
        let u : ℝ := (ideleClassNorm F x).val
        have hu : 0 < u := NNReal.coe_pos.mpr (Units.zero_lt _)
        change _ * (((χ x : ℂ) * (u : ℂ) ^ (0 + (t : ℂ) * Complex.I)) * _) = _
        rw [zero_add, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hu.ne'),
          ← Complex.ofReal_log hu.le]
        change (χ x : ℂ)⁻¹ * p _ * ((↑(χ x) * Complex.exp _) * _) =
          p _ * Complex.exp _ * _
        simp only [← mul_assoc, mul_right_comm (↑(χ x))⁻¹ (p _), inv_mul_cancel₀ (Circle.coe_ne_zero _), one_mul,
          logIdeleClassNorm, u, k, t]
        ring_nf
      _ = _ := by
        have hl := orbitalJet_logNorm_measurePreserving (F := F)
        have hq : Continuous q := by dsimp [q]; fun_prop
        have hint : (∫ x, q (logNorm x) ∂ν) = ∫ r, q r := by
          rw [← hl.map_eq, integral_map hl.aemeasurable hq.aestronglyMeasurable]
        rw [Measure.isMulLeftInvariant_eq_smul μ𝔽 ν, integral_smul_nnreal_measure, hint]
        rfl
  let d := (-2 * (Real.pi : ℂ) * Complex.I) ^ k
  have hd : d ≠ 0 := by dsimp [d]; exact pow_ne_zero _ (by simp [Real.pi_ne_zero])
  have hfour : iteratedDeriv k (FourierTransform.fourier p : SchwartzMap ℝ ℂ)
      (-t / (2 * Real.pi)) = d * ∫ r, q r := by
    have hpow (n : ℕ) : Integrable (fun x : ℝ ↦ x ^ n • p x) := by
      apply (p.integrable_pow_mul volume n).mono' (by fun_prop)
      exact .of_forall fun x ↦ by simp
    rw [SchwartzMap.fourier_coe,
      Real.iteratedDeriv_fourier (N := ⊤) (fun n _ ↦ hpow n) le_top,
      Real.fourier_real_eq_integral_exp_smul, ← integral_const_mul]
    apply integral_congr_ae (.of_forall fun x ↦ ?_)
    have he : ((-2 * Real.pi * x * (-t / (2 * Real.pi)) : ℝ) : ℂ) * Complex.I =
        (x : ℂ) * (t : ℂ) * Complex.I := by push_cast; field_simp [Real.pi_ne_zero]
    simp only [he, smul_eq_mul, q, d, mul_pow]
    ring
  rw [hpair, hfour, mul_eq_zero, mul_eq_zero]
  simp [hc, hd]

/-- A bump equal to one near an isolated frequency times a centered
monomial singles out one derivative there and vanishes near all other frequencies. -/
private theorem orbitalMarkushevichBasis_singleJet_denseSpan_bump {Z : Set ℝ}
    (hZ : IsDiscrete Z) {a : ℝ} (ha : a ∈ Z) (m : ℕ) :
    ∃ b : SchwartzMap ℝ ℂ, ∀ t ∈ Z, ∀ k : ℕ,
      iteratedDeriv k (⇑b) t ≠ 0 ↔ t = a ∧ k = m := by
  obtain ⟨U, ho, he⟩ := isDiscrete_iff_forall_mem_exists_isOpen.mp hZ a ha
  have haU : a ∈ U := (show a ∈ U ∩ Z from he.symm ▸ mem_singleton _).1
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (ho.mem_nhds haU)
  let B : ContDiffBump a := ⟨r / 3, r / 2, by positivity, by linarith⟩
  let P (x : ℝ) := (x - a) ^ m • (1 : ℂ)
  let f (x : ℝ) := B x • P x
  have hc : HasCompactSupport f := B.hasCompactSupport.smul_right
  let b := hc.toSchwartzMap (B.contDiff.smul (((contDiff_id.sub contDiff_const).pow m).smul contDiff_const))
  refine ⟨b, fun t ht k ↦ ?_⟩
  by_cases h : t = a
  · subst t
    have hnear : (⇑b) =ᶠ[nhds a] P := B.eventuallyEq_one.mono fun x hx ↦ by
      change B x • P x = P x
      rw [show B x = 1 from hx, one_smul]
    rw [hnear.iteratedDeriv_eq]
    dsimp only [P]
    rw [iteratedDeriv_smul_const (by fun_prop), iteratedDeriv_comp_sub_const k (fun x : ℝ ↦ x ^ m) a]
    simp only [sub_self, iteratedDeriv_fun_pow_zero]
    split_ifs <;> simp_all [Nat.factorial_ne_zero]
  · have hout : t ∉ tsupport B := by
      intro ht'
      have hsmall : t ∈ Metric.ball a r := (Metric.closedBall_subset_ball (by
        change r / 2 < r; linarith)) (B.tsupport_eq ▸ ht')
      have htU : t ∈ U ∩ Z := ⟨hball hsmall, ht⟩
      exact h (mem_singleton_iff.mp (he ▸ htU))
    have hnear : (⇑b) =ᶠ[nhds t] 0 := (notMem_tsupport_iff_eventuallyEq.mp hout).mono fun x hx ↦ by
      change B x • P x = 0
      rw [show B x = 0 from hx, zero_smul]
    simp [hnear.iteratedDeriv_eq, h]

/-- Subtract the single-coordinate interpolants of a finite moment vector.
The remainder has empty support and hence belongs to the same span. -/
private theorem orbitalMarkushevichBasis_singleJet_denseSpan_finite {J E : Type*}
    [AddCommGroup E] [Module ℂ E] (L : J → E →ₗ[ℂ] ℂ)
    (hb : ∀ i, ∃ b, ∀ j, L j b ≠ 0 ↔ j = i) (y : E)
    (hy : (support fun i ↦ L i y).Finite) :
    y ∈ Submodule.span ℂ {x : E | (support fun i ↦ L i x).Subsingleton} := by
  classical
  choose b h using hb
  let M := Submodule.span ℂ {x : E | (support fun i ↦ L i x).Subsingleton}
  have hbM (i : J) : b i ∈ M := Submodule.subset_span
    (fun j hj k hk ↦ ((h i j).mp hj).trans ((h i k).mp hk).symm)
  let v (i : J) := (L i (b i))⁻¹ • b i
  have hv (i j : J) : L j (v i) = if i = j then 1 else 0 := by
    simp only [v, map_smul, smul_eq_mul]
    split_ifs with e
    · subst j
      exact inv_mul_cancel₀ ((h i i).2 rfl)
    · rw [not_ne_iff.mp (fun hn ↦ e ((h i j).mp hn).symm), mul_zero]
  let z := ∑ i ∈ hy.toFinset, L i y • v i
  have hz : z ∈ M := M.sum_mem fun i _ ↦ M.smul_mem _ (M.smul_mem _ (hbM i))
  have hrem (j : J) : L j (y - z) = 0 := by
    simp only [z, map_sub, map_sum, map_smul, hv, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq']
    by_cases hj : L j y = 0 <;> simp [Set.Finite.mem_toFinset, Function.mem_support, hj]
  have hremM : y - z ∈ M := Submodule.subset_span (by
    change (support fun j ↦ L j (y - z)).Subsingleton
    simp [hrem])
  exact sub_add_cancel y z ▸ M.add_mem hremM hz

/-- Compact frequency support meets a closed discrete set in finitely many
points. Local bump interpolants then decompose every such profile modulo the
joint jet kernel. -/
private theorem orbitalMarkushevichBasis_singleJet_denseSpan_profiles
    {J E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (L : J → E →ₗ[ℂ] ℂ) (T : SchwartzMap ℝ ℂ →L[ℂ] E) (hd : DenseRange T)
    (a : J → ℝ) (k : J → ℕ) (hinj : Injective fun j ↦ (a j, k j))
    (Z : Set ℝ) (hZc : IsClosed Z) (hZd : IsDiscrete Z) (hZ : ∀ j, a j ∈ Z)
    (n : ℕ) (hn : ∀ j, k j < n)
    (hL : ∀ p j, L j (T p) = 0 ↔ iteratedDeriv (k j) (⇑p) (a j) = 0) :
    Dense (Submodule.span ℂ {x : E | (support fun j ↦ L j x).Subsingleton} : Set E) := by
  classical
  have hb (i : J) : ∃ b, ∀ j, L j b ≠ 0 ↔ j = i := by
    obtain ⟨p, hp⟩ := orbitalMarkushevichBasis_singleJet_denseSpan_bump hZd (hZ i) (k i)
    refine ⟨T p, fun j ↦ (not_congr (hL p j)).trans ((hp (a j) (hZ j) (k j)).trans ?_)⟩
    exact ⟨fun h ↦ hinj (Prod.ext h.1 h.2), fun h ↦ h ▸ ⟨rfl, rfl⟩⟩
  apply hd.dense_of_mapsTo T.continuous (SchwartzMap.dense_hasCompactSupport (E := ℝ) (F := ℂ))
  intro p hp
  apply orbitalMarkushevichBasis_singleJet_denseSpan_finite L hb
  let K := tsupport (p : ℝ → ℂ) ∩ Z
  have hK : K.Finite := (hp.inter_right hZc).finite (hZd.mono inter_subset_right)
  apply ((hK.prod (Set.finite_Iio n)).preimage hinj.injOn).subset
  intro j hj
  refine ⟨⟨?_, hZ j⟩, hn j⟩
  by_contra habs
  have he := (notMem_tsupport_iff_eventuallyEq.mp habs).iteratedDeriv_eq (n := k j)
  exact hj ((hL p j).2 (he.trans (by simp)))

/-- In the positive isotype the vectors with at most one nonzero jet moment span
densely. It suffices to approximate by smooth compactly supported Fourier profiles in
the log-norm coordinate and interpolate the finitely many jets in each support.
The strong approximation cited on p. 486 alone does not supply those interpolants. -/
private theorem orbitalMarkushevichBasis_singleJet_denseSpan (χ : PontryaginDual C𝔽) (S : Finset V)
    {s : ℝ} (hs : 0 ≤ s) (hS : S.Nonempty) (hc : 2 * (S.card : ℝ) ≤ s)
    (hχ : ∀ v ∈ S, (ideleClassNormTwist χ 0).IsUnramifiedAt v) :
    let E := Wω(hs, χ.comp restriction)
    Dense (Submodule.span ℂ {f : E |
      (Function.support fun j : OrbitalJetIndex χ S s ↦
        spectralSobolevPairing f.val (jetLp(χ, S, hs, j))).Subsingleton} : Set E) := by
  classical
  intro E
  let J := OrbitalJetIndex χ S s
  let a (j : J) := -j.val.1 / (2 * Real.pi)
  let k (j : J) := j.val.2
  let z (u : ℝ) := frequency(-u * (2 * Real.pi))
  have hz (j : J) : z (a j) = frequency(j.val.1) := by
    dsimp only [z, a]
    rw [neg_div, neg_neg, div_mul_cancel₀ _ (by positivity)]
  have hzi : Injective z := by
    intro t u he
    have him := congrArg Complex.im he
    simp only [z, Complex.mul_I_im, Complex.ofReal_re] at him
    exact neg_injective (mul_right_cancel₀ (by positivity : 2 * Real.pi ≠ 0) him)
  let Z := {w : ℂ | 0 < orbitalEulerMultiplicity χ S w}
  have hm : Meromorphic (reciprocalPartialHeckeEulerProduct χ S) :=
    fun w ↦ (OrbitalJetIndex.isZero_analyticAt χ S w).meromorphicAt
  have hdiv : Zᶜ ∈ Filter.codiscrete ℂ := by
    filter_upwards [hm.meromorphicOn.codiscreteWithin_setOfPred_meromorphicOrderAt_eq_zero_or_top]
      with w hw
    rcases hw.2 with h | h <;> simp [Z, orbitalEulerMultiplicity, h]
  obtain ⟨hclosed, hdisc⟩ := compl_mem_codiscrete_iff.mp hdiv
  have hzc : Continuous z := by dsimp [z]; fun_prop
  obtain ⟨R, hR, hrep⟩ := orbitalMarkushevichBasis_singleJet_denseSpan_lift χ hs
  let U := FourierTransform.fourierCLE ℂ (SchwartzMap ℝ ℂ)
  let T := R.comp U.symm.toContinuousLinearMap
  let D := (modulatedIntervalSobolev_dual m𝔽
    ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ μ𝔽 0 0 s hI hs).exists.choose
  let L (j : J) := ((D.symm (jetLp(χ, S, hs, j))).comp Wω(hs, χ.comp restriction).subtypeL).toLinearMap
  have hL (j : J) (y : E) : L j y = spectralSobolevPairing y.val (jetLp(χ, S, hs, j)) :=
    (spectralSobolevPairing_dual hI hs (D.symm _) y.val).2.trans
      (congrArg (spectralSobolevPairing y.val) (D.apply_symm_apply _))
  simp_rw [← hL]
  apply orbitalMarkushevichBasis_singleJet_denseSpan_profiles L T
    (hR.comp U.symm.surjective.denseRange R.continuous) a k _ (z ⁻¹' Z)
    (hclosed.preimage hzc) (hdisc.preimage hzc.continuousOn hzi) _ S.card
  · intro j
    have h := (lt_spectralBoundaryMultiplicity _ _ _ |>.mp j.property).1
    rw [orbitalEulerMultiplicity_eq_card] at h
    exact h.trans_le (Finset.card_filter_le ..)
  · intro p j
    rw [hL]
    have he := orbitalMarkushevichBasis_singleJet_denseSpan_moment χ S hs j
      (U.symm p) (T p).val (hrep (U.symm p))
    change _ ↔ iteratedDeriv (k j) (⇑(U (U.symm p))) (a j) = 0 at he
    exact he.trans (congrArg (fun q : SchwartzMap ℝ ℂ ↦ iteratedDeriv (k j) (⇑q) (a j) = 0)
      (U.apply_symm_apply p)).to_iff
  · intro i j he
    obtain ⟨ha, hk⟩ := Prod.mk.inj he
    have hf := congrArg z ha
    change z (a i) = z (a j) at hf
    rw [hz, hz] at hf
    exact Subtype.ext (Prod.ext (by simpa using congrArg Complex.im hf) hk)
  · intro j
    change 0 < orbitalEulerMultiplicity χ S (z (a j))
    rw [hz]
    exact (lt_spectralBoundaryMultiplicity _ _ _ |>.mp j.property).1.pos

/-- A total family of functionals has dense span in the Hilbert dual, by the Riesz
isometry. This is the Hilbert-space argument of Ch10_TraceSpectral/Sec2. -/
private theorem orbitalMarkushevichBasis_denseDual {Q J : Type*}
    [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]
    (Λ : J → StrongDual ℂ Q) (h : ∀ q, (∀ j, Λ j q = 0) → q = 0) :
    Dense (Submodule.span ℂ (range Λ) : Set (StrongDual ℂ Q)) := by
  let R := InnerProductSpace.toDual ℂ Q
  let v (j : J) := R.symm (Λ j)
  have hv : Dense (Submodule.span ℂ (range v) : Set Q) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top,
      Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
    intro q hq
    exact h q fun j ↦ by
      simpa only [v, R, InnerProductSpace.toDual_symm_apply] using
        (Submodule.mem_orthogonal _ q).mp hq (v j) (Submodule.subset_span (mem_range_self j))
  apply (R.surjective.denseRange.dense_image R.continuous hv).mono
  apply (Submodule.image_span_subset R.toLinearEquiv.toLinearMap _ _).mpr
  rintro _ ⟨j, rfl⟩
  exact (R.apply_symm_apply (Λ j)).symm ▸ Submodule.subset_span (mem_range_self j)

/-- After quotienting by the joint kernel, every vector with a single nonzero
coordinate is proportional to a fixed normalized representative of that coordinate. -/
private theorem orbitalMarkushevichBasis_of_sparse {J E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (N : Submodule ℂ E) [IsClosed (N : Set E)]
    (L : J → StrongDual ℂ E) (b : J → E → ℂ) (hb : ∀ j f, L j f = b j f)
    (hk : ∀ f, f ∈ N ↔ ∀ j, b j f = 0)
    (hne : ∀ j, ∃ f, b j f ≠ 0)
    (hd : Dense (Submodule.span ℂ {f : E | (support fun j ↦ b j f).Subsingleton} : Set E)) :
    ∃ (x : J → E ⧸ N) (Λ : J → StrongDual ℂ (E ⧸ N)), IsSpectralMarkushevichBasis x Λ ∧
      ∀ j f, Λ j (N.mkQ f) = b j f := by
  classical
  obtain rfl : (fun j f ↦ L j f) = b := funext fun j ↦ funext (hb j)
  let Λ (j : J) := N.liftQL (L j) (fun f hf ↦ (hk f).mp hf j)
  let A := {f : E | (support fun j ↦ L j f).Subsingleton}
  have hA (j : J) : ∃ f ∈ A, L j f ≠ 0 := by
    by_contra! hh
    have hle : Submodule.span ℂ A ≤ (L j).ker := Submodule.span_le.mpr hh
    obtain ⟨f, hf⟩ := hne j
    exact hf (closure_minimal hle (L j).isClosed_ker (hd f))
  choose f hf hn using hA
  let v (i : J) := (L i (f i))⁻¹ • f i
  have hv (i j : J) : L j (v i) = if i = j then 1 else 0 := by
    simp only [v, map_smul, smul_eq_mul]
    split_ifs with e
    · subst j
      exact inv_mul_cancel₀ (hn i)
    · have hz : L j (f i) = 0 := by
        by_contra hj
        exact e (hf i (hn i) hj)
      rw [hz, mul_zero]
  have hz (q : E ⧸ N) (hq : ∀ j, Λ j q = 0) : q = 0 := by
    obtain ⟨f, rfl⟩ := N.mkQ_surjective q
    exact (Submodule.Quotient.mk_eq_zero N).mpr ((hk _).mpr hq)
  let x (j : J) := N.mkQ (v j)
  refine ⟨x, Λ, ⟨fun i ↦ (hv i i).trans (ite_eq_left rfl),
    fun i j hij ↦ (hv i j).trans (ite_eq_right hij), ?_,
    orbitalMarkushevichBasis_denseDual Λ hz⟩, fun _ _ ↦ rfl⟩
  let M := Submodule.span ℂ (range x)
  apply N.mkQ_surjective.denseRange.dense_of_mapsTo N.mkQL.continuous hd
  change Submodule.span ℂ A ≤ M.comap N.mkQ
  apply Submodule.span_le.mpr
  intro y hy
  change N.mkQ y ∈ M
  by_cases he : ∃ i, L i y ≠ 0
  · obtain ⟨i, hi⟩ := he
    have eqv : N.mkQ y = L i y • x i := by
      apply sub_eq_zero.mp
      apply hz
      intro j
      change Λ j (N.mkQ y - L i y • N.mkQ (v i)) = 0
      rw [map_sub, map_smul]
      change L j y - L i y * L j (v i) = 0
      rw [hv]
      split_ifs with h
      · subst j
        ring
      · have hj : L j y = 0 := by
          by_contra hj
          exact h (hy hi hj)
        simp [hj]
    exact eqv.symm ▸ M.smul_mem _ (Submodule.subset_span (mem_range_self i))
  · have h := hz (N.mkQ y) (fun j ↦ not_ne_iff.mp (fun hj ↦ he ⟨j, hj⟩))
    exact h.symm ▸ M.zero_mem

/-- Paper: Theorem 11.2.0.2 and Terminology 11.2.0.1, p. 485. The zero jets
constitute an orbital Markushevich basis in the strong dual of the isotypic
quotient, realized by the bilinear Sobolev pairing. The biorthogonal vectors
are written in the Hilbert predual.
Deviation: Use the conjugate isotype for the annihilator, as in the statement
of jet membership. Quotienting by the closure gives the same continuous
annihilator as the raw range. Index each zero of the product once with its
total multiplicity. The index type permits any reindexing, including the
empty family. -/
theorem orbitalMarkushevichBasis (χ : PontryaginDual C𝔽) (S : Finset V) {s : ℝ}
    (hs : 0 ≤ s) (_hcard : 2 * (S.card : ℝ) ≤ s)
    (_hχ : ∀ v ∈ S, (ideleClassNormTwist χ 0).IsUnramifiedAt v) :
    let J := OrbitalJetIndex χ S s
    let ω := χ.comp restriction
    letI : IsClosed (N(S, hs, ω) : Set Wω(hs, ω)) :=
      instClosedOrbitalSobolevSubmoduleSec2a S hs ω
    let Q := Q(S, hs, ω)
    Countable J ∧
    ∃ (x : J → Q) (Λ : J → StrongDual ℂ Q),
      IsSpectralMarkushevichBasis x Λ ∧ ∀ (j : J) (f : Wω(hs, ω)),
        Λ j ((N(S, hs, ω)).mkQ f) = spectralSobolevPairing f.val (jetLp(χ, S, hs, j)) :=
  by
    classical
    intro J ω Q
    let K := Wω(hs, ω)
    have : CompleteSpace K := (isClosed_actionIsotype _ ω).completeSpace_coe
    let : IsClosed (N(S, hs, ω) : Set K) := instClosedOrbitalSobolevSubmoduleSec2a S hs ω
    let hm : IsModulation m𝔽 := ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
    let T := (modulatedIntervalSobolev_dual m𝔽 hm μ𝔽 0 0 s hI hs).exists.choose
    let A (j : J) : StrongDual ℂ W(s) := T.symm (jetLp(χ, S, hs, j))
    have hA (j : J) (y : W(s)) : A j y = spectralSobolevPairing y (jetLp(χ, S, hs, j)) :=
      (spectralSobolevPairing_dual hI hs (A j) y).2.trans
        (congrArg (spectralSobolevPairing y) (T.apply_symm_apply _))
    refine ⟨orbitalMarkushevichBasis_countable χ S s, ?_⟩
    apply orbitalMarkushevichBasis_of_sparse (J := J) (E := K) (N(S, hs, ω))
      (fun j ↦ (A j).comp K.subtypeL) _ (fun j f ↦ hA j f.val)
    · intro f
      refine ⟨fun hf j ↦ (hA j f.val).symm.trans
        (orbitalMarkushevichBasis_annihilates χ S hs j (A j) (hA j) f hf), ?_⟩
      rcases S.eq_empty_or_nonempty with h | h
      · intro _
        have hall : N(S, hs, ω) = ⊤ :=
          (congrArg (fun T : Finset V ↦ N(T, hs, ω)) h).trans (orbitalSobolevSubmodule_empty hs ω)
        exact hall.ge Submodule.mem_top
      · exact orbitalMarkushevichBasis_synthesis χ S hs h _hcard _hχ f
    · exact orbitalMarkushevichBasis_nonzero χ S hs
    · rcases S.eq_empty_or_nonempty with h | h
      · have : IsEmpty J := ⟨fun j ↦ by
          have hk := (lt_spectralBoundaryMultiplicity _ _ _ |>.mp j.property).1
          simp [orbitalEulerMultiplicity_eq_card, h] at hk⟩
        simp [Set.subsingleton_of_subsingleton]
      · exact orbitalMarkushevichBasis_singleJet_denseSpan χ S hs h _hcard _hχ

/-- A Hilbert quotient of a closed subspace maps isometrically into the dual
model of the ambient space, onto the functionals that kill the orthogonal
complement of the subspace and the denominator. -/
private theorem orbitalQuotientDual_isometry_range_hilbert
    {H₀ Y₀ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℂ H₀] [CompleteSpace H₀]
    [NormedAddCommGroup Y₀] [NormedSpace ℂ Y₀]
    (K : Submodule ℂ H₀) (hK : IsClosed (K : Set H₀))
    (N : Submodule ℂ K) [IsClosed (N : Set K)] (B : H₀ → Y₀ → ℂ)
    (hT : ∃ T : StrongDual ℂ H₀ ≃ₗᵢ[ℂ] Y₀, ∀ (Λ : StrongDual ℂ H₀) (x : H₀), Λ x = B x (T Λ))
    (C : Y₀ → Prop) (hC : ∀ v, C v ↔ ∀ x ∈ Kᗮ, B x v = 0) :
    ∃ D : StrongDual ℂ (K ⧸ N) →ₗᵢ[ℂ] Y₀,
      range D = {u | C u ∧ ∀ f ∈ N, B f.val u = 0} ∧
      ∀ (Λ : StrongDual ℂ (K ⧸ N)) (f : K), B f.val (D Λ) = Λ (N.mkQ f) := by
  obtain ⟨T, hB⟩ := hT
  have : CompleteSpace K := hK.completeSpace_coe
  let Pr : H₀ →L[ℂ] K := K.orthogonalProjectionOnto
  have hPK (f : K) : Pr f.val = f := K.orthogonalProjectionOnto_mem_subspace_eq_self f
  have hPo (x : H₀) (hx : x ∈ Kᗮ) : Pr x = 0 :=
    K.orthogonalProjectionOnto_apply_of_mem_orthogonal hx
  let L : StrongDual ℂ (K ⧸ N) →ₗ[ℂ] StrongDual ℂ H₀ :=
    ((N.mkQL.comp Pr).precomp ℂ).toLinearMap
  have hL (Λ : StrongDual ℂ (K ⧸ N)) (x : H₀) : L Λ x = Λ (N.mkQ (Pr x)) := rfl
  have hnorm (Λ : StrongDual ℂ (K ⧸ N)) : ‖L Λ‖ = ‖Λ‖ := by
    apply le_antisymm
    · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg Λ)
      intro x
      rw [hL]
      calc ‖Λ (N.mkQ (Pr x))‖ ≤ ‖Λ‖ * ‖N.mkQ (Pr x)‖ := Λ.le_opNorm _
        _ ≤ ‖Λ‖ * ‖x‖ := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg Λ)
          exact (Submodule.Quotient.norm_mk_le N (Pr x)).trans
            (K.norm_orthogonalProjectionOnto_apply_le x)
    · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (L Λ))
      intro q
      let v : Nᗮ := N.quotientEquivOrthogonal q
      have hv : N.mkQ v.val = q := by
        change (Submodule.Quotient.mk v.val : K ⧸ N) = q
        exact (N.quotientEquivOrthogonal_symm_eq_mk v.val v.property).symm.trans
          (N.quotientEquivOrthogonal.symm_apply_apply q)
      have hn : ‖v.val‖ = ‖q‖ := N.quotientEquivOrthogonal.norm_map q
      calc
        ‖Λ q‖ = ‖(L Λ) (v.val : H₀)‖ := by rw [hL, hPK, hv]
        _ ≤ ‖L Λ‖ * ‖(v.val : H₀)‖ := (L Λ).le_opNorm _
        _ = ‖L Λ‖ * ‖q‖ := by rw [← hn]; rfl
  let D : StrongDual ℂ (K ⧸ N) →ₗᵢ[ℂ] Y₀ :=
    { toLinearMap := T.toLinearEquiv.toLinearMap.comp L
      norm_map' := fun Λ ↦ by
        change ‖T (L Λ)‖ = ‖Λ‖
        rw [T.norm_map, hnorm] }
  have hD (Λ : StrongDual ℂ (K ⧸ N)) : D Λ = T (L Λ) := rfl
  have hpair (Λ : StrongDual ℂ (K ⧸ N)) (x : H₀) : B x (D Λ) = Λ (N.mkQ (Pr x)) := by
    rw [hD, ← hB, hL]
  refine ⟨D, ?_, fun Λ f ↦ by rw [hpair, hPK]⟩
  ext u
  constructor
  · rintro ⟨Λ, rfl⟩
    refine ⟨(hC _).2 fun x hx ↦ ?_, fun f hf ↦ ?_⟩
    · rw [hpair, hPo x hx, map_zero, map_zero]
    · rw [hpair, hPK, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero N).mpr hf, map_zero]
  · rintro ⟨hCu, hN⟩
    let φ : StrongDual ℂ H₀ := T.symm u
    have hφ (x : H₀) : φ x = B x u := by
      rw [hB φ x]
      change B x (T (T.symm u)) = B x u
      rw [T.apply_symm_apply]
    let ψ : StrongDual ℂ K := φ.comp K.subtypeL
    have hψ : N ≤ ψ.ker := fun f hf ↦ by
      change φ f.val = 0
      rw [hφ]
      exact hN f hf
    refine ⟨N.liftQL ψ hψ, ?_⟩
    have hLφ : L (N.liftQL ψ hψ) = φ := by
      ext x
      rw [hL]
      change φ (Pr x : H₀) = φ x
      have hsub : x - (Pr x : H₀) ∈ Kᗮ := K.sub_starProjection_mem_orthogonal x
      have h0 : φ (x - (Pr x : H₀)) = 0 := by rw [hφ]; exact (hC u).1 hCu _ hsub
      rw [map_sub, sub_eq_zero] at h0
      exact h0.symm
    rw [hD, hLφ]
    exact T.apply_symm_apply u

/-- The unweighted product integral against a vector of the reciprocal-weight
space is the inner product with the conjugate vector divided by the weight. -/
private theorem orbitalQuotientDual_isometry_range_riesz {X : Type*} [MeasurableSpace X]
    (ν : Measure X) {ρ ρ' : X → ℝ} (hρ : Measurable ρ) (hρ' : Measurable ρ')
    (hpos : ∀ x, 0 < ρ x) (hpos' : ∀ x, 0 < ρ' x) (hr : ∀ x, ρ x * ρ' x = 1)
    (u : Lp ℂ 2 (ν.withDensity fun x ↦ ENNReal.ofReal (ρ' x))) :
    ∃ v : Lp ℂ 2 (ν.withDensity fun x ↦ ENNReal.ofReal (ρ x)),
      (v : X → ℂ) =ᵐ[ν] (fun x ↦ (ρ' x : ℂ) * star (u x)) ∧
      ∀ f : Lp ℂ 2 (ν.withDensity fun x ↦ ENNReal.ofReal (ρ x)),
        ∫ x, f x * u x ∂ν = inner ℂ v f := by
  have hbase {ρ : X → ℝ} (hρ : Measurable ρ) (hpos : ∀ x, 0 < ρ x) :
      ν ≪ ν.withDensity fun x ↦ ENNReal.ofReal (ρ x) :=
    withDensity_absolutelyContinuous' hρ.ennreal_ofReal.aemeasurable
      (ae_of_all _ fun x ↦ (ENNReal.ofReal_pos.mpr (hpos x)).ne')
  let g : X → ℂ := fun x ↦ (ρ' x : ℂ) * star (u x)
  have hsq (x : X) : ‖g x‖ ^ 2 * ρ x = ‖u x‖ ^ 2 * ρ' x := by
    calc
      _ = ‖u x‖ ^ 2 * ρ' x * (ρ x * ρ' x) := by
        dsimp only [g]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hpos' x), norm_star]
        ring
      _ = _ := by rw [hr, mul_one]
  have hmeas : AEStronglyMeasurable g (ν.withDensity fun x ↦ ENNReal.ofReal (ρ x)) :=
    (Complex.measurable_ofReal.comp hρ').aestronglyMeasurable.mul
      (((Lp.aestronglyMeasurable u).mono_ac (hbase hρ' hpos')).mono_ac
        (withDensity_absolutelyContinuous _ _)).star
  have hu2 : Integrable (fun x ↦ ‖u x‖ ^ 2 * ρ' x) ν := by
    have h1 := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).1 (Lp.memLp u)
    have h2 := (integrable_withDensity_iff hρ'.ennreal_ofReal
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)).1 h1
    refine h2.congr (ae_of_all _ fun x ↦ ?_)
    change ‖u x‖ ^ 2 * (ENNReal.ofReal (ρ' x)).toReal = ‖u x‖ ^ 2 * ρ' x
    rw [ENNReal.toReal_ofReal (hpos' x).le]
  have hmem : MemLp g 2 (ν.withDensity fun x ↦ ENNReal.ofReal (ρ x)) := by
    apply (memLp_two_iff_integrable_sq_norm hmeas).2
    apply (integrable_withDensity_iff hρ.ennreal_ofReal
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)).2
    refine hu2.congr (ae_of_all _ fun x ↦ ?_)
    change ‖u x‖ ^ 2 * ρ' x = ‖g x‖ ^ 2 * (ENNReal.ofReal (ρ x)).toReal
    rw [ENNReal.toReal_ofReal (hpos x).le, hsq]
  have hcoe : (hmem.toLp g : X → ℂ) =ᵐ[ν] g := (hbase hρ hpos).ae_eq hmem.coeFn_toLp
  refine ⟨hmem.toLp g, hcoe, fun f ↦ ?_⟩
  rw [L2.inner_def, integral_withDensity_eq_integral_toReal_smul hρ.ennreal_ofReal
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  refine integral_congr_ae ?_
  filter_upwards [hcoe] with x hx
  rw [hx, ENNReal.toReal_ofReal (hpos x).le, RCLike.inner_apply]
  dsimp only [g]
  simp only [map_mul, Complex.conj_ofReal, Complex.star_def, Complex.conj_conj,
    Complex.real_smul]
  have hr' : (ρ x : ℂ) * ρ' x = 1 := by exact_mod_cast hr x
  linear_combination (-(f x * u x)) * hr'

/-- On the 0-line, a reciprocal-weight vector is of the conjugate isotype exactly
when its product integral kills the orthogonal complement of the isotype. -/
private theorem orbitalQuotientDual_isometry_range_conj {s : ℝ} (hs : 0 ≤ s)
    (ω : PontryaginDual C₁) (u : W'(s)) :
    (∀ k : C₁, (fun g ↦ u (k.val⁻¹ * g)) =ᵐ[μ𝔽] fun g ↦ (ω⁻¹ k : ℂ) * u g) ↔
      ∀ x ∈ (Wω(hs, ω))ᗮ, spectralSobolevPairing x u = 0 := by
  let w : C𝔽 → ℝ := fun g ↦ intervalSobolevDensity 0 0 s (logNorm g)
  have hlog : Measurable logNorm :=
    (NNReal.continuous_coe.comp (Units.continuous_val.comp
      (isProperMap_ideleClassNorm F).continuous)).measurable.log
  have hdens : Continuous (intervalSobolevDensity 0 0 s) := by
    change Continuous fun x : ℝ ↦
      max (Real.exp (2 * 0 * x)) (Real.exp (2 * 0 * x)) * (1 + x ^ 2) ^ (s / 2)
    refine Continuous.mul (by fun_prop) (Continuous.rpow_const (by fun_prop) fun t ↦ Or.inl ?_)
    positivity
  have hw : Measurable w := hdens.measurable.comp hlog
  have hwpos : ∀ x, 0 < w x := fun x ↦ by
    change 0 < max (Real.exp (2 * 0 * logNorm x)) (Real.exp (2 * 0 * logNorm x)) *
      (1 + (logNorm x) ^ 2) ^ (s / 2)
    exact mul_pos (lt_max_of_lt_left (Real.exp_pos _)) (Real.rpow_pos_of_pos (by positivity) _)
  have hwk : ∀ (k : C₁) g, w (k.val⁻¹ * g) = w g := by
    intro k g
    have hk : ideleClassNorm F k.val = 1 := k.2
    simp only [w, logIdeleClassNorm, map_mul, map_inv, hk, inv_one, one_mul]
  have hbase : μ𝔽 ≪ (μ𝔽).withDensity (fun x ↦ ENNReal.ofReal (w x)) :=
    withDensity_absolutelyContinuous' hw.ennreal_ofReal.aemeasurable
      (ae_of_all _ fun x ↦ (ENNReal.ofReal_pos.mpr (hwpos x)).ne')
  have hwd : ((μ𝔽).withDensity fun x ↦ ENNReal.ofReal (w x)) ≪ μ𝔽 :=
    withDensity_absolutelyContinuous _ _
  have hiso (f : W(s)) : f ∈ Wω(hs, ω) ↔
      ∀ k : C₁, (fun g ↦ f (k.val⁻¹ * g)) =ᵐ[μ𝔽] fun g ↦ (ω k : ℂ) * f g := by
    rw [mem_actionIsotype]
    refine forall_congr' fun k ↦ ?_
    have htr := hardySobolevTranslation_apply μ𝔽 m𝔽 0 0 s hI hs k.val f
    have hsm := hbase.ae_eq (Lp.coeFn_smul (ω k : ℂ) f)
    change hardySobolevTranslation μ𝔽 m𝔽 0 0 s hI hs k.val f = (ω k : ℂ) • f ↔ _
    constructor
    · intro h
      rw [h] at htr
      exact htr.symm.trans hsm
    · intro h
      exact Lp.ext (hwd.ae_eq (htr.trans (h.trans hsm.symm)))
  have hωinv (k : C₁) : ((ω⁻¹ k : Circle) : ℂ) = star (ω k : ℂ) := by
    rw [show ω⁻¹ k = (ω k)⁻¹ from rfl, Circle.coe_inv_eq_conj]
    rfl
  have hqmp (k : C₁) := (measurePreserving_mul_left μ𝔽 k.val⁻¹).quasiMeasurePreserving
  obtain ⟨v, hv, hpair⟩ := orbitalQuotientDual_isometry_range_riesz μ𝔽
    (ρ := fun x ↦ if false = true then (w x)⁻¹ else w x)
    (ρ' := fun x ↦ if true = true then (w x)⁻¹ else w x)
    (by simpa using hw) (by simp only [↓reduceIte]; exact hw.inv) (by simpa using hwpos)
    (by simpa using fun x ↦ inv_pos.2 (hwpos x))
    (fun x ↦ by simpa using mul_inv_cancel₀ (hwpos x).ne') u
  have hv' : (v : C𝔽 → ℂ) =ᵐ[μ𝔽] fun x ↦ ((w x)⁻¹ : ℂ) * star (u x) := by
    filter_upwards [hv] with x hx
    rw [hx]
    simp only [↓reduceIte, Complex.ofReal_inv]
  have hu' : (u : C𝔽 → ℂ) =ᵐ[μ𝔽] fun x ↦ (w x : ℂ) * star (v x) := by
    filter_upwards [hv'] with x hx
    rw [hx, star_mul', star_star, ← mul_assoc]
    have h0 : (w x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hwpos x).ne'
    simp [h0]
  have key : (∀ k : C₁, (fun g ↦ u (k.val⁻¹ * g)) =ᵐ[μ𝔽] fun g ↦ (ω⁻¹ k : ℂ) * u g) ↔
      v ∈ Wω(hs, ω) := by
    rw [hiso]
    refine forall_congr' fun k ↦ ⟨fun hk ↦ ?_, fun hk ↦ ?_⟩
    · have h1 := (hqmp k).ae_eq_comp hv'
      filter_upwards [h1, hk, hv'] with g h1 h2 h3
      simp only [comp_apply] at h1
      rw [h1, h2, h3, hwk, star_mul']
      simp only [hωinv, star_star]
      ring
    · have h1 := (hqmp k).ae_eq_comp hu'
      filter_upwards [h1, hk, hu'] with g h1 h2 h3
      simp only [comp_apply] at h1
      rw [h1, h2, h3, hwk, star_mul']
      simp only [hωinv]
      ring
  have hK : (Wω(hs, ω)).HasOrthogonalProjection := by
    have : CompleteSpace (Wω(hs, ω)) := (isClosed_actionIsotype _ ω).completeSpace_coe
    infer_instance
  rw [key]
  conv_lhs => rw [← Submodule.orthogonal_orthogonal (Wω(hs, ω))]
  rw [Submodule.mem_orthogonal]
  refine forall₂_congr fun x _ ↦ ?_
  change _ = _ ↔ ∫ g, x g * u g ∂μ𝔽 = 0
  rw [hpair x, inner_eq_zero_symm]

-- TODO(paper-gap): Remark 11.2.0.3 drops PV from the denominator of the quotient.

/-- Paper: Remark 11.2.0.3, p. 485. The pairing represents the quotient
strong dual isometrically as the annihilator in the negative space.
Deviation: Divide the isotype by the closed principal-value subspace. -/
theorem orbitalQuotientDual_isometry_range (S : Finset V) {s : ℝ} (hs : 0 ≤ s)
    (ω : PontryaginDual C₁) :
    ∃ D : StrongDual ℂ Q(S, hs, ω) →ₗᵢ[ℂ] W'(s),
      range D = {u |
        (∀ k : C₁, (fun g ↦ u (k.val⁻¹ * g)) =ᵐ[μ𝔽] fun g ↦ (ω⁻¹ k : ℂ) * u g) ∧
        ∀ f ∈ N(S, hs, ω), spectralSobolevPairing f.val u = 0} ∧
      ∀ (Λ : StrongDual ℂ Q(S, hs, ω)) (f : Wω(hs, ω)),
        spectralSobolevPairing f.val (D Λ) = Λ ((N(S, hs, ω)).mkQ f) :=
  orbitalQuotientDual_isometry_range_hilbert (H₀ := W(s)) (Y₀ := W'(s)) (Wω(hs, ω))
    (isClosed_actionIsotype _ ω) (N(S, hs, ω)) spectralSobolevPairing
    ⟨_, fun Λ f ↦ (spectralSobolevPairing_dual hI hs Λ f).2⟩ _
    (orbitalQuotientDual_isometry_range_conj hs ω)

local notation "E" => ModulatedExponentialDecay m𝔽 (univ : Set ℝ)
local notation "hm𝔽" => (⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ :
  IsModulation m𝔽)
local notation "hms𝔽" => (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.2.2.2.1
local notation "ρE" => (exists_modulatedExponentialDecay_translationAction m𝔽 univ
  hm𝔽 hms𝔽 ordConnected_univ univ_nonempty).choose
local notation "Eω(" ω ")" => actionIsotype ((ρE).comp (ideleClassNorm F).ker.subtype) ω

/-- The zero twist of the decay-space isotypic projector is the normalized
Schwartz–Bruhat average. Restoring its Haar mass gives homogeneous theta,
as in `exists_ratHomogeneousTheta_decay` for the trivial character over ℚ. -/
private theorem orbitalSobolevPairing_homogeneousTest (ω : PontryaginDual C₁) (f : ℬ₀) :
    ∃ φ : Eω(ω), ∀ g, φ.val.val g = homogeneousAdelicTheta ω f.val g := by
  let μ := normOneIdeleClassTamagawaMeasure F
  let : μ.IsHaarMeasure := (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  let : μ.Regular := (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.2.1
  let : CompactSpace C₁ := (ideleClassGroup_finiteness F).2.1
  let : LocallyCompactSpace C₁ :=
    (isCompact_iff_compactSpace.mpr ‹CompactSpace C₁›).isClosed.locallyCompactSpace
  let ψ : E := ⟨adelicTheta f.val, adelicTheta_mem_modulatedExponentialDecay_of_polar f.val f.property⟩
  have hρ := (exists_modulatedExponentialDecay_translationAction m𝔽 univ hm𝔽 hms𝔽
    ordConnected_univ univ_nonempty).choose_spec.1
  have hA := (existsUnique_modulatedExponentialDecay_isotypicProjector m𝔽 univ hm𝔽 hms𝔽
    ordConnected_univ univ_nonempty μ ρE hρ ω).exists
  let A := hA.choose
  refine ⟨(μ.real univ : ℂ) • A ψ, fun x ↦ ?_⟩
  let z : (univ : Set ℝ) := ⟨0, mem_univ _⟩
  have htw (v : E) (y : C𝔽) : modulatedExponentialDecayTwist m𝔽 univ z v y = v.val y :=
    congrFun (modulationWeight_zero m𝔽 v.val) y
  have h := congrArg (fun b : SchwartzBruhat C𝔽 ↦ b x) (hA.choose_spec ψ z)
  have havg := (schwartzBruhatIsotypicProjector_apply m𝔽 hm𝔽 μ ω
    (modulatedExponentialDecayTwist m𝔽 univ z ψ) x).2
  have he : (A ψ).val.val x = _ := (htw _ x).symm.trans (h.trans havg)
  change (μ.real univ : ℂ) * (A ψ).val.val x = _
  rw [he, Complex.real_smul, Complex.ofReal_inv, ← mul_assoc,
    mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr measureReal_univ_ne_zero), one_mul]
  change _ = ∫ k : C₁, adelicTheta f.val (k.val * x) * (ω k : ℂ) ∂μ
  rw [← integral_inv_eq_self (fun k : C₁ ↦ adelicTheta f.val (k.val * x) * (ω k : ℂ)) μ]
  apply integral_congr_ae (.of_forall fun k ↦ ?_)
  refine (congrArg (star (ω k : ℂ) * ·) (htw ψ (k.val⁻¹ * x))).trans ?_
  change star (ω k : ℂ) * adelicTheta f.val (k.val⁻¹ * x) =
    adelicTheta f.val (k.val⁻¹ * x) * (ω k⁻¹ : ℂ)
  rw [map_inv, Circle.coe_inv_eq_conj, Complex.star_def, mul_comm]

/-- Equivariant continuous maps commute with the (unnormalized) Pettis average,
by scalar testing as in Ch10_TraceSpectral/Sec1. -/
private theorem orbitalSobolevPairing_average_comm {G X : Type*} [Monoid G]
    [TopologicalSpace G] [MeasurableSpace G] [NormedAddCommGroup X] [NormedSpace ℂ X]
    (μ : Measure G) (ω : PontryaginDual G) (ρ : G →* (X →L[ℂ] X))
    (B T : X →L[ℂ] X) (hB : IsPettisIsotypicAverageOn μ univ ρ ω B)
    (hT : ∀ k v, T (ρ k v) = ρ k (T v)) (v : X) : B (T v) = T (B v) := by
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2
  intro L
  have h₁ := LinearMap.congr_fun (hB (T v)).2 L
  have h₂ := LinearMap.congr_fun (hB v).2 (L.comp T)
  exact h₁.trans ((integral_congr_ae (.of_forall fun k ↦ congrArg L
    ((congrArg (star (ω k : ℂ) • ·) (hT k v).symm).trans (T.map_smul _ _).symm))).trans h₂.symm)

/-- The two completion maps give the same weighted function on a homogeneous test. -/
private theorem orbitalSobolevPairing_average_test (a : ℝ) {s : ℝ} (hs : 0 ≤ s)
    (ω : PontryaginDual C₁) (f : ℬ₀) (φ : Eω(ω))
    (hφ : ∀ x, φ.val.val x = homogeneousAdelicTheta ω f.val x) :
    let i := (existsUnique_spectralLineTestCompletion (F := F) a hs ω).exists.choose
    let A := (existsUnique_globalThetaSobolevAverage (F := F) (a := a) hI hs ω).exists.choose
    (i φ).val = (A (j(a, hs) (theta(f)))).val.val := by
  intro i A
  let x : globalPolarFreeThetaSubmodule (F := F) ω :=
    ⟨Submodule.Quotient.mk f.val, Submodule.mem_map.mpr ⟨f.val, f.property, rfl⟩⟩
  let j := (exists_globalHomogeneousThetaSobolevInclusion (F := F) (a := a) hI hs ω).choose
  have hj := (exists_globalHomogeneousThetaSobolevInclusion
    (F := F) (a := a) hI hs ω).choose_spec.2.2 f x rfl
  have he : (i φ).val = (j x).val.val := by
    apply Lp.ext
    apply (withDensity_absolutelyContinuous μ𝔽 _).ae_eq
    have hi := (existsUnique_spectralLineTestCompletion (F := F) a hs ω).exists.choose_spec.1 φ
    have hw := congrArg (modulationWeight m𝔽 a) (funext hφ)
    exact hi.trans ((Filter.EventuallyEq.of_eq hw).trans hj.2.symm)
  exact he.trans (congrArg (fun y ↦ y.val.val) hj.1)

/-- Paper: (11.2.0.7), p. 486, the commutativity of the square. For every
polar-free input `f` the homogeneous theta function of its principal-value test
`pvTest(S, f)` is the function of a test `φ` of the isotype `Eω(ω)`, and the
image of `φ` under the test inclusion is the extended principal value of the
averaged theta class. In this half of `orbitalSobolevPairing_pullback`, equivariance
lets the completed principal value commute with the norm-one average. -/
private theorem orbitalSobolevPairing_pullback_testLift (S : Finset V) (a : ℝ) {s : ℝ}
    (hs : 0 ≤ s) (ω : PontryaginDual C₁) :
    let i := (existsUnique_spectralLineTestCompletion (F := F) a hs ω).exists.choose
    let A := (existsUnique_globalThetaSobolevAverage (F := F) (a := a) hI hs ω).exists.choose
    ∀ f : ℬ₀, ∃ φ : Eω(ω),
      (∀ g : C𝔽, φ.val.val g = homogeneousAdelicTheta ω (pvTest(S, f)).val g) ∧
      (i φ).val = (P(S, a, hs) (A (j(a, hs) (theta(f)))).val).val := by
  intro i A f
  let b := pvTest(S, f)
  have h := orbitalSobolevPairing_homogeneousTest ω b
  refine ⟨h.choose, h.choose_spec, ?_⟩
  have ht := orbitalSobolevPairing_average_test a hs ω b h.choose h.choose_spec
  have hc := orbitalSobolevPairing_average_comm (normOneIdeleClassTamagawaMeasure F) ω
    ((exists_globalThetaSobolevAction (F := F) a hI hs).choose.comp (ideleClassNorm F).ker.subtype)
    _ (P(S, a, hs))
    (existsUnique_globalThetaSobolevAverage (F := F) (a := a) hI hs ω).exists.choose_spec.1
    (globalThetaSobolevPrincipalValue_equivariant S a hs) (j(a, hs) (theta(f)))
  exact ht.trans (congrArg Subtype.val
    ((congrArg (fun v ↦ (A v).val) (globalThetaSobolevPrincipalValue_apply S a hs f)).symm.trans hc))

/-- Paper: (11.2.0.7), p. 486. The continuous transpose of the test inclusion
evaluates by the Sobolev pairing. It gives the commutative square after
restriction to the homogeneous principal-value tests of every polar-free input.
Deviation: Use the equivalent isotypic presentation of the tests on idele
classes from §10.2, with the conjugate isotype on the negative side. -/
theorem orbitalSobolevPairing_pullback (S : Finset V) (a : ℝ) {s : ℝ} (hs : 0 ≤ s)
    (ω : PontryaginDual C₁) (u : W'(s))
    (_hu : ∀ k : C₁, (fun g ↦ u (k.val⁻¹ * g)) =ᵐ[μ𝔽] fun g ↦ (ω⁻¹ k : ℂ) * u g) :
    let i := (existsUnique_spectralLineTestCompletion a hs ω).exists.choose
    let A := (existsUnique_globalThetaSobolevAverage (F := F) (a := a) hI hs ω).exists.choose
    ∃ Λ : StrongDual ℂ Eω(ω),
      (∀ φ : Eω(ω), Λ φ = spectralSobolevPairing (i φ).val u) ∧
      ∀ f : ℬ₀, ∃ φ : Eω(ω),
        (∀ g : C𝔽, φ.val.val g = homogeneousAdelicTheta ω (pvTest(S, f)).val g) ∧
        (i φ).val = (P(S, a, hs) (A (j(a, hs) (theta(f)))).val).val := by
  refine ⟨(existsUnique_spectralLineTestCompletion (F := F) a hs ω).exists.choose_spec.2.2.choose
    u, ?_, orbitalSobolevPairing_pullback_testLift (F := F) S a hs ω⟩
  intro φ
  exact (existsUnique_spectralLineTestCompletion (F := F) a hs ω).exists.choose_spec.2.2.choose_spec.1
    u φ

-- TODO(paper-gap): Proposition 11.2.0.4 prints the full multiplicity and
-- claims noncontainment in an open ball even when S₀ is empty.

private theorem orbitalJet_lp_norm_sq {s : ℝ} (u : Lp ℂ 2 (μ'(s))) :
    ‖u‖ ^ 2 = ∫ g : C𝔽, ‖u g‖ ^ 2 ∂(μ'(s)) := by
  have hre : (inner ℂ u u).re = ‖u‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) u
  rw [← hre, L2.inner_def]
  have hre_int : (∫ g : C𝔽, inner ℂ (u g) (u g) ∂(μ'(s))).re =
      ∫ g : C𝔽, (inner ℂ (u g) (u g)).re ∂(μ'(s)) :=
    (Complex.reCLM.integral_comp_comm (L2.integrable_inner u u)).symm
  rw [hre_int]
  refine integral_congr_ae (ae_of_all _ fun g ↦ ?_)
  exact inner_self_eq_norm_sq (𝕜 := ℂ) (u g)

private theorem orbitalJet_integral_pos {s : ℝ} (hs : 1 < s) {k : ℕ}
    (hkN : k < Nat.ceil ((s - 1) / 2)) :
    0 < ∫ g : C𝔽, (logNorm g) ^ (2 * k) * ((1 + (logNorm g) ^ 2) ^ (s / 2))⁻¹ ∂μ𝔽 := by
  have hk' : (k : ℝ) < (s - 1) / 2 := Nat.lt_ceil.mp hkN
  have hk : 2 * (k : ℝ) + 1 < s := by linarith
  let ν : Measure C𝔽 := canonicalModulatedHaar m𝔽 hm𝔽
  let : ν.IsHaarMeasure := (existsUnique_canonicalModulatedHaar m𝔽 hm𝔽).exists.choose_spec.1
  let fk : ℝ → ℝ := fun x ↦ x ^ (2 * k) * ((1 + x ^ 2) ^ (s / 2))⁻¹
  have hfk_int : Integrable fk volume := orbitalJet_integrable_pow_mul_rpow_inv hk
  have hν_eq : ∫ g : C𝔽, fk (logNorm g) ∂ν = ∫ x : ℝ, fk x ∂volume := by
    rw [← (orbitalJet_logNorm_measurePreserving (F := F)).map_eq,
      integral_map (orbitalJet_logNorm_continuous (F := F)).measurable.aemeasurable
        (orbitalJet_pow_mul_rpow_inv_continuous k s).aestronglyMeasurable]
  have hvol_pos : 0 < ∫ x : ℝ, fk x ∂volume := by
    let c : ℝ := ((5 : ℝ) ^ (s / 2))⁻¹
    have hc : 0 < c := inv_pos.mpr (Real.rpow_pos_of_pos (by norm_num) _)
    have hind_int : Integrable ((Icc (1 : ℝ) 2).indicator fun _ ↦ c) volume :=
      (integrableOn_const (by simp)).integrable_indicator measurableSet_Icc
    have hle : ∀ x : ℝ, (Icc (1 : ℝ) 2).indicator (fun _ ↦ c) x ≤ fk x := by
      intro x
      by_cases hx : x ∈ Icc (1 : ℝ) 2
      · rw [indicator_of_mem hx]
        have hx1 : 1 ≤ x := hx.1
        have hx2 : x ≤ 2 := hx.2
        have hpow : (1 : ℝ) ≤ x ^ (2 * k) := one_le_pow₀ hx1
        have hbase : 1 + x ^ 2 ≤ 5 := by nlinarith
        have hrpow : (1 + x ^ 2) ^ (s / 2) ≤ (5 : ℝ) ^ (s / 2) :=
          Real.rpow_le_rpow (by positivity) hbase (by linarith)
        have hinv : c ≤ ((1 + x ^ 2) ^ (s / 2))⁻¹ :=
          inv_anti₀ (Real.rpow_pos_of_pos (by positivity) _) hrpow
        calc
          c = 1 * c := (one_mul c).symm
          _ ≤ x ^ (2 * k) * ((1 + x ^ 2) ^ (s / 2))⁻¹ :=
            mul_le_mul hpow hinv hc.le (by positivity)
      · rw [indicator_of_notMem hx]
        exact mul_nonneg (Even.pow_nonneg (even_two_mul k) x)
          (inv_nonneg.mpr (Real.rpow_pos_of_pos (by positivity) _).le)
    have hint_le : ∫ x : ℝ, (Icc (1 : ℝ) 2).indicator (fun _ ↦ c) x ∂volume ≤
        ∫ x : ℝ, fk x ∂volume :=
      integral_mono hind_int hfk_int hle
    have hind_val : ∫ x : ℝ, (Icc (1 : ℝ) 2).indicator (fun _ ↦ c) x ∂volume = c := by
      rw [integral_indicator measurableSet_Icc, setIntegral_const, Real.volume_real_Icc]
      norm_num
    linarith
  have hμ_eq : (∫ g : C𝔽, fk (logNorm g) ∂μ𝔽) =
      (Measure.haarScalarFactor μ𝔽 ν : ℝ) * ∫ x : ℝ, fk x ∂volume := by
    conv_lhs => rw [Measure.isMulLeftInvariant_eq_smul μ𝔽 ν]
    rw [integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul, hν_eq]
  change 0 < ∫ g : C𝔽, fk (logNorm g) ∂μ𝔽
  rw [hμ_eq]
  have hfac_pos : 0 < (Measure.haarScalarFactor μ𝔽 ν : ℝ) := by
    exact_mod_cast (Measure.haarScalarFactor_pos_of_isHaarMeasure μ𝔽 ν)
  exact mul_pos hfac_pos hvol_pos

/-- Paper: Proposition 11.2.0.4 and (11.2.0.8)–(11.2.0.9), p. 486. One
annulus bounds the norms of all admitted jets above and away from zero.
Deviation: Use the truncated multiplicity cited in (11.2.0.6) and the
conjugate isotype. The annulus condition is disjointness from the inner
open ball, which also holds for an empty family. -/
theorem orbitalJet_norm_annulus (χ : PontryaginDual C𝔽) (S : Finset V) {s : ℝ}
    (hs : 1 < s) (_hχ : ∀ v ∈ S, (ideleClassNormTwist χ 0).IsUnramifiedAt v) :
    ∃ C : ℝ, 0 < C ∧ ∀ j : OrbitalJetIndex χ S s,
      let u := jetLp(χ, S, (zero_lt_one.trans hs).le, j)
      C⁻¹ ≤ ‖u‖ ∧ ‖u‖ ≤ C := by
  let hs₀ : 0 ≤ s := (zero_lt_one.trans hs).le
  let N : ℕ := Nat.ceil ((s - 1) / 2)
  let I : ℕ → ℝ := fun k ↦
    ∫ g : C𝔽, (logNorm g) ^ (2 * k) * ((1 + (logNorm g) ^ 2) ^ (s / 2))⁻¹ ∂μ𝔽
  let r : ℕ → ℝ := fun k ↦ Real.sqrt (I k)
  have hnorm_sq : ∀ j : OrbitalJetIndex χ S s,
      ‖jetLp(χ, S, hs₀, j)‖ ^ 2 = I j.val.2 := by
    intro j
    let u := jetLp(χ, S, hs₀, j)
    have h1 : ‖u‖ ^ 2 = ∫ g : C𝔽, ‖u g‖ ^ 2 ∂(μ'(s)) := orbitalJet_lp_norm_sq u
    have h2 : ∫ g : C𝔽, ‖u g‖ ^ 2 ∂(μ'(s)) = ∫ g : C𝔽, (logNorm g) ^ (2 * j.val.2) ∂(μ'(s)) := by
      refine integral_congr_ae ?_
      filter_upwards [MemLp.coeFn_toLp (orbitalJet_memLp χ S hs₀ j)] with g hg
      rw [hg, orbitalJet_norm_sq]
    have h3 : ∫ g : C𝔽, (logNorm g) ^ (2 * j.val.2) ∂(μ'(s)) = I j.val.2 := by
      rw [integral_withDensity_eq_integral_toReal_smul
        ((orbitalJet_density_continuous s).measurable.ennreal_ofReal)
        (ae_of_all μ𝔽 fun _ ↦ ENNReal.ofReal_lt_top)]
      refine integral_congr_ae (ae_of_all μ𝔽 fun g ↦ ?_)
      dsimp only
      rw [smul_eq_mul, orbitalJet_density_eq,
        ENNReal.toReal_ofReal (inv_nonneg.mpr (Real.rpow_pos_of_pos (by positivity) _).le),
        mul_comm]
    exact h1.trans (h2.trans h3)
  let C : ℝ := 1 + ∑ k ∈ Finset.range N, (r k + (r k)⁻¹)
  have hC_pos : 0 < C := by
    have hsum_nonneg : 0 ≤ ∑ k ∈ Finset.range N, (r k + (r k)⁻¹) :=
      Finset.sum_nonneg fun k _ ↦ add_nonneg (Real.sqrt_nonneg _) (inv_nonneg.mpr (Real.sqrt_nonneg _))
    linarith
  refine ⟨C, hC_pos, fun j ↦ ?_⟩
  have hjN : j.val.2 ∈ Finset.range N :=
    Finset.mem_range.mpr (lt_of_lt_of_le j.property (min_le_right _ _))
  have hr_pos : 0 < r j.val.2 :=
    Real.sqrt_pos.mpr (orbitalJet_integral_pos hs (Finset.mem_range.mp hjN))
  have hnorm_eq : ‖jetLp(χ, S, hs₀, j)‖ = r j.val.2 := by
    rw [← Real.sqrt_sq (norm_nonneg _), hnorm_sq j]
  have hterm_le : r j.val.2 + (r j.val.2)⁻¹ ≤ C := by
    have h1 : r j.val.2 + (r j.val.2)⁻¹ ≤ ∑ k ∈ Finset.range N, (r k + (r k)⁻¹) :=
      Finset.single_le_sum
        (fun k _ ↦ add_nonneg (Real.sqrt_nonneg _) (inv_nonneg.mpr (Real.sqrt_nonneg _))) hjN
    linarith
  dsimp only
  rw [hnorm_eq]
  refine ⟨?_, by linarith [inv_pos.mpr hr_pos]⟩
  have hinv_le : (r j.val.2)⁻¹ ≤ C := by linarith
  calc
    C⁻¹ ≤ ((r j.val.2)⁻¹)⁻¹ := inv_anti₀ (inv_pos.mpr hr_pos) hinv_le
    _ = r j.val.2 := inv_inv _

/-- Identify each representing jet in the range of the quotient-dual isometry
by evaluating on quotient representatives, then transfer its two norm bounds. -/
private theorem orbitalMarkushevichBasis_normalized_of_isometry {X Y J : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X] [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (K : Submodule ℂ X) (N : Submodule ℂ K) [IsClosed (N : Set K)]
    (B : X → Y → ℂ) (C : Y → Prop) (η : J → Y)
    (hη : ∀ j, C (η j))
    (hbasis : ∃ (x : J → K ⧸ N) (Λ : J → StrongDual ℂ (K ⧸ N)),
      IsSpectralMarkushevichBasis x Λ ∧ ∀ j (f : K), Λ j (N.mkQ f) = B f.val (η j))
    (hann : ∃ c : ℝ, 0 < c ∧ ∀ j, c⁻¹ ≤ ‖η j‖ ∧ ‖η j‖ ≤ c)
    (hiso : ∃ D : StrongDual ℂ (K ⧸ N) →ₗᵢ[ℂ] Y,
      range D = {u | C u ∧ ∀ f ∈ N, B f.val u = 0} ∧
      ∀ L (f : K), B f.val (D L) = L (N.mkQ f)) :
    ∃ (x : J → K ⧸ N) (Λ : J → StrongDual ℂ (K ⧸ N)), IsSpectralMarkushevichBasis x Λ ∧
      IsNormalizedSpectralFamily Λ ∧ ∀ j (f : K), Λ j (N.mkQ f) = B f.val (η j) := by
  obtain ⟨x, Λ, hb, hΛ⟩ := hbasis
  obtain ⟨D, hD, hpair⟩ := hiso
  have hnorm (j : J) : ‖Λ j‖ = ‖η j‖ := by
    have hr : η j ∈ range D := by
      rw [hD]
      refine ⟨hη j, fun f hf ↦ ?_⟩
      rw [← hΛ, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).mpr hf, map_zero]
    obtain ⟨L, hL⟩ := hr
    have heq : L = Λ j := by
      apply ContinuousLinearMap.ext
      intro q
      obtain ⟨f, rfl⟩ := N.mkQ_surjective q
      rw [← hpair, hL, hΛ]
    rw [← heq, ← D.norm_map L, hL]
  obtain ⟨c, hc, h⟩ := hann
  exact ⟨x, Λ, hb, ⟨⟨c, fun j ↦ (hnorm j).trans_le (h j).2⟩,
    c⁻¹, inv_pos.mpr hc, fun j ↦ (h j).1.trans_eq (hnorm j).symm⟩, hΛ⟩

/-- Paper: Corollary 11.2.0.5 and (11.2.0.10), pp. 486–487. The orbital
Markushevich basis is normalized in the strong-dual norm.
Deviation: Use the isotypic quotient with the closed principal-value
denominator. The degree hypothesis already admits the full multiplicity. -/
theorem orbitalMarkushevichBasis_normalized (χ : PontryaginDual C𝔽) (S : Finset V) {s : ℝ}
    (hs : 1 < s) (_hcard : 2 * (S.card : ℝ) ≤ s)
    (_hχ : ∀ v ∈ S, (ideleClassNormTwist χ 0).IsUnramifiedAt v) :
    let hs₀ := (zero_lt_one.trans hs).le
    let J := OrbitalJetIndex χ S s
    let ω := χ.comp restriction
    letI : IsClosed (N(S, hs₀, ω) : Set Wω(hs₀, ω)) :=
      instClosedOrbitalSobolevSubmoduleSec2a S hs₀ ω
    let Q := Q(S, hs₀, ω)
    ∃ (x : J → Q) (Λ : J → StrongDual ℂ Q),
      IsSpectralMarkushevichBasis x Λ ∧ IsNormalizedSpectralFamily Λ ∧
      ∀ (j : J) (f : Wω(hs₀, ω)),
        Λ j ((N(S, hs₀, ω)).mkQ f) = spectralSobolevPairing f.val (jetLp(χ, S, hs₀, j)) := by
  intro hs₀ J ω Q
  have : IsClosed (N(S, hs₀, ω) : Set Wω(hs₀, ω)) := instClosedOrbitalSobolevSubmoduleSec2a S hs₀ ω
  exact orbitalMarkushevichBasis_normalized_of_isometry (Wω(hs₀, ω)) (N(S, hs₀, ω))
    spectralSobolevPairing (fun u : W'(s) ↦ ∀ k : C₁,
      (fun g ↦ u (k.val⁻¹ * g)) =ᵐ[μ𝔽] fun g ↦ (ω⁻¹ k : ℂ) * u g)
    (fun j : J ↦ jetLp(χ, S, hs₀, j)) (orbitalJet_isotype χ S hs₀)
    (orbitalMarkushevichBasis χ S hs₀ _hcard _hχ).2
    (orbitalJet_norm_annulus χ S hs _hχ) (orbitalQuotientDual_isometry_range S hs₀ ω)

end RiemannMasullo
