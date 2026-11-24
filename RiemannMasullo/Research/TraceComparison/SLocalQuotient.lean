module

public import RiemannMasullo.Ch06_LocalGlobal.Sec1
public import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.Ch02_AdelicTheta.Sec2a
import RiemannMasullo.AppA_AlgebraicNT.Sec2b
import RiemannMasullo.ForMathlib.MeasureTheory.Group.Arithmetic

/-! # The compact quotient behind the S-local comparison

Under the S-class-number-one hypothesis, deleting the complementary integral units gives
the quotient used for test descent on pp. 514–515. -/

@[expose] public noncomputable section

open Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped ENNReal NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false

variable {F : Type*} [Field F] [NumberField F] {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "Jₛ" => SIdeleQuotient F S
local notation "qF" => QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 F) F)
local notation "qS" => QuotientGroup.mk' (sProjectedDiagonal F S)
local notation "iS" => integralIdeleInsertion F S
local notation "prS" => Units.map (adeleProjection F S).toMonoidHom

private theorem sInsert_section (g : Iₛ) : prS (sIdeleInsertion F S g) = g := by
  obtain ⟨h, h', -⟩ := sIdeleInsertion_apply F S g
  exact Units.ext (Prod.ext h (funext h'))

private theorem sInsert_mem (g : Iₛ) : sIdeleInsertion F S g ∈ Set.range iS := by
  apply (mem_range_integralIdeleInsertion F S _).2
  intro v hv
  have h := (sIdeleInsertion_apply F S g).2.2 v hv
  have hi := (sIdeleInsertion_apply F S g⁻¹).2.2 v hv
  rw [map_inv] at hi
  exact ⟨h ▸ (v.adicCompletionIntegers F).one_mem, hi ▸ (v.adicCompletionIntegers F).one_mem⟩

/-- Paper: Theorem 12.4.1.1, pp. 514–515. When the S-integers have trivial Picard group,
the quotient map from global idele classes onto the S-local class group forgets precisely
the classes of the complementary integral units. It preserves the norm and takes each
S-idele extended by one to its given S-local class. -/
theorem exists_sLocalTraceQuotient (hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F))) :
    ∃ π : C𝔽 →ₜ* Jₛ, IsOpenQuotientMap π ∧
      π.toMonoidHom.ker = (outsideIntegralIdeleUnits F S).map qF ∧
      (∀ g, sIdeleQuotientNorm F S (π g) = ideleClassNorm F g) ∧
      ∀ t : Iₛ, π (qF (sIdeleInsertion F S t)) = qS t := by
  classical
  let A := integralAdelesOutside F S
  let p := Units.map ((adeleProjection F S).comp A.subtype).toMonoidHom
  let d := (Units.map (integralAdeleDiagonal F S).toMonoidHom).range
  let q := QuotientGroup.mk' d
  let f := QuotientGroup.map d (d.map p) p (Subgroup.le_comap_map _ _)
  obtain ⟨e, he, heN⟩ := sIdeleClassGroup_equiv_of_classNumberOne F S
  have hp : IsOpenQuotientMap p := by
    let B := (v : {v : V // v ∉ S}) → v.val.adicCompletionIntegers F
    obtain ⟨a, ha, ha', hcoord⟩ := integralAdelesOutside_factors F S
    let E : A ≃ₜ* (SAdeleRing F S × B) :=
      { a.toMulEquiv with continuous_toFun := ha, continuous_invFun := ha' }
    let U := (Units.mapContinuousMulEquiv E).trans (ContinuousMulEquiv.prodUnits _ _)
    have heq : (p : Aˣ → Iₛ) = Prod.fst ∘ U := by
      funext g
      exact Units.ext (hcoord g.val).1.symm
    rw [heq]
    exact isOpenQuotientMap_fst.comp U.toHomeomorph.isOpenQuotientMap
  have hf : IsOpenQuotientMap f :=
    (QuotientGroup.isOpenQuotientMap_mk (N := d)).of_comp_iff.mp
      ((QuotientGroup.isOpenQuotientMap_mk (N := d.map p)).comp hp)
  let π : C𝔽 →ₜ* Jₛ := (⟨f, hf.continuous⟩ : SIdeleClassGroup F S →ₜ* Jₛ).comp
    ⟨e.symm.toMonoidHom, e.symm.continuous⟩
  have hrep (u : Aˣ) : π (qF (iS u)) = qS (p u) := by
    have := congrArg (fun x ↦ π x) (he u)
    exact this.symm.trans (congrArg f (e.symm_apply_apply (q u)))
  have hpe (u : Aˣ) : prS (iS u) = p u := rfl
  refine ⟨π, hf.comp e.symm.toHomeomorph.isOpenQuotientMap, ?_, ?_, ?_⟩
  · ext c
    constructor
    · intro hc
      obtain ⟨t, rfl⟩ := e.surjective c
      obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective t
      have hu : qS (p u) = 1 := (congrArg f (e.symm_apply_apply (q u))).symm.trans (MonoidHom.mem_ker.mp hc)
      obtain ⟨y, hy, hyu⟩ := (QuotientGroup.eq_one_iff (p u)).mp hu
      let k := iS (u / y)
      have hk : k ∈ outsideIntegralIdeleUnits F S := by
        refine ⟨⟨_, rfl⟩, MonoidHom.mem_ker.mpr ?_⟩
        change prS (iS (u / y)) = 1
        rw [hpe, map_div, hyu, div_self']
      have hy' : q y = 1 := (QuotientGroup.eq_one_iff y).2 hy
      refine ⟨k, hk, ?_⟩
      change qF (iS (u / y)) = e (q u)
      apply (he (u / y)).symm.trans
      apply congrArg e
      change q (u / y) = q u
      rw [map_div, hy', div_one]
    · rintro ⟨k, hk, rfl⟩
      obtain ⟨u, rfl⟩ := hk.1
      exact MonoidHom.mem_ker.mpr ((hrep u).trans ((congrArg qS (MonoidHom.mem_ker.mp hk.2)).trans (map_one qS)))
  · intro c
    obtain ⟨t, rfl⟩ := e.surjective c
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective t
    calc
      sIdeleQuotientNorm F S (π (e (q u))) = sIdeleQuotientNorm F S (qS (p u)) :=
        congrArg (sIdeleQuotientNorm F S) (congrArg f (e.symm_apply_apply (q u)))
      _ = ideleClassNorm F (e (q u)) := (heN (q u)).symm
  · intro t
    obtain ⟨u, hu⟩ := sInsert_mem t
    rw [← hu, hrep]
    exact congrArg qS (((hpe u).symm.trans (congrArg prS hu)).trans (sInsert_section t))


/-- A proper quotient preserving a modulation sends its canonically normalized Haar
measure to the canonical Haar measure of the quotient. -/
private theorem map_canonical_of_norm {G H : Type*} [CommGroup G] [CommGroup H]
    [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G] [IsTopologicalGroup H]
    [T2Space G] [T2Space H] [LocallyCompactSpace G] [LocallyCompactSpace H]
    [SecondCountableTopology G] [SecondCountableTopology H]
    [MeasurableSpace G] [MeasurableSpace H] [BorelSpace G] [BorelSpace H]
    (m : G →ₜ* ℝ≥0ˣ) (n : H →ₜ* ℝ≥0ˣ) (hm : IsModulation m) (hn : IsModulation n)
    (π : G →ₜ* H) (hπ : Surjective π) (h : ∀ x, n (π x) = m x) :
    (canonicalModulatedHaar m hm).map π = canonicalModulatedHaar n hn := by
  let μ := canonicalModulatedHaar m hm
  have hμ := (existsUnique_canonicalModulatedHaar m hm).exists.choose_spec
  have : μ.IsHaarMeasure := hμ.1
  have hprop : IsProperMap π := isProperMap_of_comp_of_t2 π.continuous n.continuous
    (show IsProperMap (n ∘ π) from (funext h : n ∘ π = m) ▸ hm.1)
  refine (existsUnique_canonicalModulatedHaar n hn).unique
    ⟨Measure.isHaarMeasure_map μ π.toMonoidHom π.continuous hπ
      (isProperMap_iff_tendsto_cocompact.mp hprop).2, ?_⟩
    (existsUnique_canonicalModulatedHaar n hn).exists.choose_spec
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ _
  have hband (r : ℝ) : μ.map π {x | ((n x).val : ℝ) ∈ Icc r⁻¹ r} =
      μ {x | ((m x).val : ℝ) ∈ Icc r⁻¹ r} := by
    have hSet : MeasurableSet {x | ((n x).val : ℝ) ∈ Icc r⁻¹ r} :=
      (NNReal.continuous_coe.comp (Units.continuous_val.comp n.continuous)).measurable measurableSet_Icc
    have hπm : Measurable (π : G → H) := π.continuous.measurable
    rw [Measure.map_apply hπm hSet]
    congr 1
    ext x
    change ((n (π x)).val : ℝ) ∈ Icc r⁻¹ r ↔ ((m x).val : ℝ) ∈ Icc r⁻¹ r
    rw [h]
  apply hμ.2.congr_left
  intro r
  rw [hband]
  rfl

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instSIdeleQuotientMeasurableSpaceSec1 instSIdeleQuotientBorelSpaceSec1
  instSIdeleQuotientT2Sec1 instSIdeleQuotientLocallyCompactSec1 instSIdeleQuotientSecondCountableSec1
  instNormOneSIdeleQuotientMeasurableSpaceSec1

local notation "mF" => (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "mS" => (⟨sIdeleQuotientNorm F S, (isProperMap_sIdeleQuotientNorm F S).continuous⟩ :
  Jₛ →ₜ* ℝ≥0ˣ)
local notation "μF" => ideleClassTamagawaMeasure F
local notation "μS" => sLocalQuotientTamagawaMeasure F S
local notation "vF" => (normOneIdeleClassTamagawaMeasure F) univ
local notation "vS" => (sLocalNormOneQuotientMeasure F S) univ

private def unitLogBand : Set ℝ≥0ˣ := {t | (t.val : ℝ) ∈ Icc 1 (Real.exp 1)}

private theorem unitLogBand_measurable : MeasurableSet unitLogBand := by
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ _
  exact (NNReal.continuous_coe.comp Units.continuous_val).measurable measurableSet_Icc

private theorem normProduct_band_mass {X K : Type*} [MeasurableSpace X]
    [MeasurableSpace K] (n : X → ℝ≥0ˣ) (hn : Measurable n)
    (j : K × ℝ≥0ˣ → X) (hj : Measurable j) (h : ∀ z, n (j z) = z.2)
    (ν : Measure K) :
    (ν.prod positiveRealHaar).map j (n ⁻¹' unitLogBand) = ν univ := by
  have : SFinite positiveRealHaar := by unfold positiveRealHaar; infer_instance
  have hband : positiveRealHaar unitLogBand = 1 := by
    let t : ℝ≥0ˣ := Units.mk0 (Real.exp 1).toNNReal (by positivity)
    have ht : (t.val : ℝ) = Real.exp 1 := Real.coe_toNNReal _ (Real.exp_pos 1).le
    have hval := positiveRealHaar_interval t (by rw [ht]; exact Real.one_le_exp zero_le_one)
    rw [ht, Real.log_exp, ENNReal.ofReal_one] at hval
    exact hval
  have he : j ⁻¹' (n ⁻¹' unitLogBand) = univ ×ˢ unitLogBand := by
    ext z
    change n (j z) ∈ unitLogBand ↔ _ ∧ _
    simp [h]
  rw [Measure.map_apply hj (hn unitLogBand_measurable), he, Measure.prod_prod, hband, mul_one]

private theorem local_haar_scale (hm : IsModulation mS) :
    μS = vS • canonicalModulatedHaar mS hm := by
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ _
  let : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  have : (μS).IsHaarMeasure := (sLocalQuotientTamagawaMeasure_isWeil (F := F) (S := S)).1
  have hp : Continuous (prS : IdeleGroup (𝓞 F) F → Iₛ) :=
    (continuous_fst.prodMk (continuous_pi fun v : S ↦
      (RestrictedProduct.continuous_eval v.val).comp continuous_snd)).units_map _
  let t : ℝ≥0ˣ →ₜ* Iₛ := ⟨(prS).comp (canonicalIdeleNormSection F),
    hp.comp (canonicalIdeleNormSection_continuous F)⟩
  have ht : RightInverse t (sIdeleNorm F S) := sIdeleNorm_project_canonicalSection F S
  let σ : ℝ≥0ˣ →ₜ* Jₛ := (⟨qS, QuotientGroup.continuous_mk⟩ : Iₛ →ₜ* Jₛ).comp t
  have hσ : RightInverse σ mS := ht
  let B := (sIdeleQuotientNorm F S) ⁻¹' unitLogBand
  let j (x : (sIdeleQuotientNorm F S).ker × ℝ≥0ˣ) : Jₛ := x.1.val * σ x.2
  have hj : Continuous j := (continuous_subtype_val.comp continuous_fst).mul (σ.continuous.comp continuous_snd)
  have hnorm (x : (sIdeleQuotientNorm F S).ker × ℝ≥0ˣ) : mS (j x) = x.2 := by
    change sIdeleQuotientNorm F S (x.1.val * σ x.2) = _
    rw [map_mul, MonoidHom.mem_ker.mp x.1.property, one_mul]
    exact hσ x.2
  have hμB : μS B = vS := by
    let : BorelSpace (sIdeleQuotientNorm F S).ker := ⟨rfl⟩
    rw [← (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).2 t ht]
    exact normProduct_band_mass mS (mS).continuous.measurable j hj.measurable hnorm _
  have hcanB : canonicalModulatedHaar mS hm B = 1 := by
    let : MeasurableSpace (mS).toMonoidHom.ker := Subtype.instMeasurableSpace
    let : CompactSpace (mS).toMonoidHom.ker := isCompact_iff_compactSpace.mp hm.isCompact_ker
    let P : Measure (mS).toMonoidHom.ker := Measure.haarMeasure ⊤
    rw [canonicalModulatedHaar_eq_map_prod mS hm σ hσ P Measure.haarMeasure_self]
    exact (normProduct_band_mass mS (mS).continuous.measurable j hj.measurable hnorm P).trans
      Measure.haarMeasure_self
  have : (canonicalModulatedHaar mS hm).IsHaarMeasure :=
    (existsUnique_canonicalModulatedHaar mS hm).exists.choose_spec.1
  have hs := Measure.isMulLeftInvariant_eq_smul μS (canonicalModulatedHaar mS hm)
  have hb := congrArg (fun ν : Measure Jₛ ↦ ν B) hs
  change μS B = (Measure.haarScalarFactor μS (canonicalModulatedHaar mS hm) : ℝ≥0∞) *
    canonicalModulatedHaar mS hm B at hb
  rw [hcanB, mul_one, hμB] at hb
  rwa [ENNReal.smul_def, ← hb] at hs

/-- Paper: Theorem 12.4.1.1 and the comparison on p. 520. Pushing the global Tamagawa
measure to the S-local class quotient multiplies the local Tamagawa measure by the ratio
of the global and local norm-one volumes. -/
theorem sLocalTraceQuotient_map_tamagawa (π : C𝔽 →ₜ* Jₛ) (hπ : Surjective π)
    (hn : ∀ x, sIdeleQuotientNorm F S (π x) = ideleClassNorm F x) :
    (μF).map π = (vF / vS) • μS := by
  have hF : IsModulation mF := ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
  obtain ⟨x, hx⟩ := hF.2
  have hS : IsModulation mS := ⟨isProperMap_sIdeleQuotientNorm F S, π x, (hn x).trans_ne hx⟩
  have : CompactSpace (sIdeleQuotientNorm F S).ker := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage isCompact_singleton)
  have : (sLocalNormOneQuotientMeasure F S).IsHaarMeasure :=
    (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1
  have hv₀ : vS ≠ 0 := (isOpen_univ.measure_pos _ univ_nonempty).ne'
  have hv : vS ≠ ⊤ := measure_ne_top _ _
  have hπm : Measurable (π : C𝔽 → Jₛ) := π.continuous.measurable
  rw [ideleClassTamagawaMeasure_eq_smul_canonical (F := F),
    Measure.map_smul _ hπm.aemeasurable, local_haar_scale hS, smul_smul,
    ENNReal.div_mul_cancel hv₀ hv, map_canonical_of_norm mF mS hF hS π hπ hn]


/-- Paper: Theorem 12.4.1.1, pp. 514–515. A global test invariant under the outside
unit classes descends uniquely to a compactly supported Bruhat test on the actual
S-local class group. Pullback along insertion recovers its values on representatives. -/
theorem sLocalTraceQuotient_bruhat_descent (π : C𝔽 →ₜ* Jₛ) (hπ : IsOpenQuotientMap π)
    (hker : π.toMonoidHom.ker = (outsideIntegralIdeleUnits F S).map qF)
    (hn : ∀ x, sIdeleQuotientNorm F S (π x) = ideleClassNorm F x)
    (φ : BruhatCompactSupport C𝔽)
    (hout : ∀ (u : outsideIntegralIdeleUnits F S) (x : C𝔽), φ.val (qF u.val * x) = φ.val x) :
    ∃! b : BruhatCompactSupport Jₛ, ∀ x, b.val (π x) = φ.val x := by
  classical
  let K := π.toMonoidHom.ker
  let q := QuotientGroup.mk' K
  have hprop : IsProperMap π := isProperMap_of_comp_of_t2 π.continuous
    (isProperMap_sIdeleQuotientNorm F S).continuous
    ((funext hn : sIdeleQuotientNorm F S ∘ π = ideleClassNorm F) ▸ isProperMap_ideleClassNorm F)
  have hK : IsCompact (K : Set C𝔽) := hprop.isCompact_preimage isCompact_singleton
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have : T1Space (C𝔽 ⧸ K) := QuotientGroup.t1Space_iff.mpr hK.isClosed
  let E := QuotientGroup.quotientKerEquivOfSurjective π.toMonoidHom hπ.surjective
  have hE (x : C𝔽) : E (q x) = π x := rfl
  have hEs (x : C𝔽) : E.symm (π x) = q x := E.symm_apply_eq.mpr (hE x).symm
  let e : (C𝔽 ⧸ K) ≃ₜ* Jₛ :=
    { E with
      continuous_toFun := (QuotientGroup.isQuotientMap_mk K).continuous_iff.mpr π.continuous
      continuous_invFun := hπ.continuous_comp_iff.mp
        (QuotientGroup.continuous_mk.congr (fun x ↦ (hEs x).symm)) }
  have hF : IsModulation mF := ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
  have hsF : Surjective (mF) := fun z ↦
    ⟨qF (canonicalIdeleNormSection F z), canonicalIdeleNormSection_rightInverse F z⟩
  have hd := bruhatCompactSupport_le_modulatedExponentialDecay mF univ hF hsF φ.property
  have hmem := ((Submodule.mem_iInf _).mp hd) (⟨0, mem_univ 0⟩ : (univ : Set ℝ))
  change modulationWeight mF 0 φ.val ∈ schwartzBruhatSubmodule C𝔽 at hmem
  rw [modulationWeight_zero] at hmem
  let f : SchwartzBruhat C𝔽 := ⟨φ.val, hmem⟩
  let P : Measure K := Measure.haarMeasure ⊤
  have : IsProbabilityMeasure P := ⟨Measure.haarMeasure_self⟩
  let A := schwartzBruhatCosetIntegral K P hK.isClosed f
  let b : SchwartzBruhat Jₛ := ⟨A.val ∘ e.symm, schwartzBruhatSubmodule_comp_continuousMulEquiv
    e.symm A.property⟩
  have hb (x : C𝔽) : b (π x) = φ.val x := by
    change A (E.symm (π x)) = φ.val x
    rw [hEs x]
    change schwartzBruhatCosetIntegral K P hK.isClosed f (QuotientGroup.mk x) = φ.val x
    rw [schwartzBruhatCosetIntegral_mk]
    have hi (k : K) : f (x * k.val) = φ.val x := by
      have hk : k.val ∈ (outsideIntegralIdeleUnits F S).map qF := hker ▸ k.property
      obtain ⟨u, hu, heq⟩ := hk
      change φ.val (x * k.val) = φ.val x
      rw [← heq, mul_comm x]
      exact hout ⟨u, hu⟩ x
    simp_rw [hi]
    simp
  have hcs : HasCompactSupport b.val := by
    apply (φ.property.2.image π.continuous).of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ (φ.property.2.image π.continuous).isClosed
    intro y hy
    obtain ⟨x, rfl⟩ := hπ.surjective y
    exact ⟨x, subset_closure (show φ.val x ≠ 0 from fun hx ↦ hy ((hb x).trans hx)), rfl⟩
  let u : BruhatCompactSupport Jₛ :=
    ⟨b.val, (mem_bruhatSmoothSubmodule_iff _).2 (schwartzBruhat_isBruhatSmooth b), hcs⟩
  refine ⟨u, hb, fun v hv ↦ ?_⟩
  apply Subtype.ext
  funext y
  obtain ⟨x, rfl⟩ := hπ.surjective y
  exact (hv x).trans (hb x).symm



/-- Integrating a function pulled back through the S-local quotient multiplies its local
integral by the ratio of compact norm-one volumes. This applies in particular to a
measurable quotient kernel evaluated on its diagonal. -/
theorem sLocalTraceQuotient_integral (π : C𝔽 →ₜ* Jₛ) (hπ : Surjective π)
    (hn : ∀ x, sIdeleQuotientNorm F S (π x) = ideleClassNorm F x)
    (f : Jₛ → ℂ) (hf : Measurable f) :
    (∫ x, f (π x) ∂μF) = (vF / vS).toReal • ∫ j, f j ∂μS := by
  have hm : Measurable (π : C𝔽 → Jₛ) := π.continuous.measurable
  rw [← integral_map hm.aemeasurable hf.stronglyMeasurable.aestronglyMeasurable,
    sLocalTraceQuotient_map_tamagawa π hπ hn, integral_smul_measure]

/-- Paper: Theorem 12.4.1.1, p. 515. The convolution of an outside-unit-invariant global
test with a pulled-back function is the pullback of the local convolution, scaled by the
ratio of norm-one volumes. The two operators agree for canonically normalized measures. -/
theorem sLocalTraceQuotient_convolution (π : C𝔽 →ₜ* Jₛ) (hπ : Surjective π)
    (hn : ∀ x, sIdeleQuotientNorm F S (π x) = ideleClassNorm F x)
    (φ : BruhatCompactSupport C𝔽) (b : BruhatCompactSupport Jₛ)
    (hb : ∀ x, b.val (π x) = φ.val x) (u : Jₛ → ℂ) (hu : Continuous u) (y : C𝔽) :
    (∫ g, φ.val g * u (π (g⁻¹ * y)) ∂μF) =
      (vF / vS).toReal • ∫ j, b.val j * u (j⁻¹ * π y) ∂μS := by
  have hc := continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp b.property.1)
  have h := sLocalTraceQuotient_integral π hπ hn (fun j ↦ b.val j * u (j⁻¹ * π y))
    (hc.mul (hu.comp (continuous_inv.mul continuous_const))).measurable
  simpa only [hb, map_mul, map_inv] using h

/-- Paper: Theorem 12.5.1.1, pp. 519–520. For an outside-unit-invariant global test,
each norm-power Mellin integral descends with the same volume factor. Taking exponents
`1/2` and `-1/2` gives the two polar Mellin values appearing in (12.5.1.3). -/
theorem sLocalTraceQuotient_normPowerMellin (π : C𝔽 →ₜ* Jₛ) (hπ : Surjective π)
    (hn : ∀ x, sIdeleQuotientNorm F S (π x) = ideleClassNorm F x)
    (φ : BruhatCompactSupport C𝔽) (b : BruhatCompactSupport Jₛ)
    (hb : ∀ x, b.val (π x) = φ.val x) (s : ℂ) :
    modulatedFourierMellin mF univ ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
        μF φ.val (ideleClassNormTwist 1 s) =
      (vF / vS).toReal • ∫ j, b.val j * (((sIdeleQuotientNorm F S j).val : ℝ) : ℂ) ^ s ∂μS := by
  let p (j : Jₛ) : ℂ := (((sIdeleQuotientNorm F S j).val : ℝ) : ℂ) ^ s
  have hbase : Continuous (fun j : Jₛ ↦ (((sIdeleQuotientNorm F S j).val : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp (Units.continuous_val.comp
      (isProperMap_sIdeleQuotientNorm F S).continuous))
  have hp : Continuous p := hbase.cpow continuous_const (fun j ↦
    Complex.ofReal_mem_slitPlane.mpr (NNReal.coe_pos.mpr (Units.zero_lt _)))
  have hc := continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp b.property.1)
  have ht (x : C𝔽) : ideleClassNormTwist (1 : PontryaginDual C𝔽) s x = p (π x) := by
    change (1 : ℂ) * (((ideleClassNorm F x).val : ℝ) : ℂ) ^ s = _
    simp only [p, hn, one_mul]
  simp only [modulatedFourierMellin, relativeVerticalStrip, preimage_univ, indicator_univ]
  calc
    _ = ∫ x, b.val (π x) * p (π x) ∂μF := by simp_rw [hb, ht]
    _ = _ := sLocalTraceQuotient_integral π hπ hn (fun j ↦ b.val j * p j) (hc.mul hp).measurable

section Lift

attribute [local instance] instSAdeleMeasurableSpaceSec1 instSIdeleLocallyCompactSec1
  instSIdeleSecondCountableSec1

local instance : T2Space Iₛ := (sIdeleGroup_description F S).2.1

/-- Paper: (12.4.1.4), p. 515. A compact test on the S-ideles whose S-unit
periodization is the class test gives exactly the same integral against every continuous
weight on the quotient. In particular the two square-root norm weights can be integrated
on either side with the Tamagawa measures of §3.3. -/
theorem sLocalTraceLift_weighted_integral (f : BruhatCompactSupport Iₛ) (b : Jₛ → ℂ)
    (hLift : ∀ g : Iₛ, HasSum (fun ξ : sProjectedDiagonal F S ↦ f.val (ξ.val * g)) (b (qS g)))
    (w : Jₛ → ℂ) (hw : Continuous w) :
    (∫ g : Iₛ, f.val g * w (qS g) ∂sMultiplicativeTamagawaMeasure F S) =
      ∫ j, b j * w j ∂μS := by
  let H := sProjectedDiagonal F S
  let : BorelSpace Iₛ := sIdeleGroup_borelSpace
  let : DiscreteTopology H := discreteTopology_sProjectedDiagonal
  let : Countable H := (TopologicalSpace.separableSpace_iff_countable.mp inferInstance)
  let c : C(Iₛ, ℂ) := ⟨fun g ↦ f.val g * w (qS g),
    (continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp f.property.1)).mul
      (hw.comp continuous_quot_mk)⟩
  have hc : HasCompactSupport c := f.property.2.mul_right
  refine ((sLocalQuotientTamagawaMeasure_isWeil (F := F) (S := S)).2.2 c hc).trans ?_
  apply integral_congr_ae
  filter_upwards with j
  let g : Iₛ := j.out
  have hg : qS g = j := QuotientGroup.out_eq' j
  have hclass (y : H) : qS (g * (y : Iₛ)) = j :=
    (QuotientGroup.mk_mul_of_mem g y.property).trans hg
  have hsum : HasSum (fun y : H ↦ f.val (g * (y : Iₛ))) (b j) := by
    simpa only [mul_comm g, hg] using hLift g
  change (∫ y : H, f.val (g * (y : Iₛ)) * w (qS (g * (y : Iₛ))) ∂Measure.count) = _
  simp_rw [hclass]
  rw [integral_mul_const]
  congr 1
  have hInt := integrable_count_iff.mpr hsum.summable.norm
  calc
    _ = ∑' y : H, f.val (g * (y : Iₛ)) := by
      simpa only [count_real_singleton, one_smul] using integral_countable hInt
    _ = _ := hsum.tsum_eq

/-- Paper: (12.4.1.4) and (12.5.1.3), pp. 515, 519–520. The norm-power Mellin
integral of every compact global Bruhat test satisfying the outside-unit invariance
is the integral of any of its compact S-idelic periodization lifts, multiplied by the
ratio of the global and S-local norm-one volumes. The exponents ±1/2 give both polar
Mellin values. -/
theorem sLocalTraceLift_global_normPowerMellin
    (hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F)))
    (φ : BruhatCompactSupport C𝔽)
    (hout : ∀ (u : outsideIntegralIdeleUnits F S) (x : C𝔽), φ.val (qF u.val * x) = φ.val x)
    (f : BruhatCompactSupport Iₛ) (hLift : ∀ g : Iₛ,
      HasSum (fun ξ : sProjectedDiagonal F S ↦ f.val (ξ.val * g))
        (φ.val (qF (sIdeleInsertion F S g)))) (s : ℂ) :
    modulatedFourierMellin mF univ ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
        μF φ.val (ideleClassNormTwist 1 s) =
      (vF / vS).toReal • ∫ g, f.val g * (((sIdeleNorm F S g).val : ℝ) : ℂ) ^ s
        ∂sMultiplicativeTamagawaMeasure F S := by
  obtain ⟨π, hπ, hker, hn, hs⟩ := exists_sLocalTraceQuotient hPic
  obtain ⟨b, hb, -⟩ := sLocalTraceQuotient_bruhat_descent π hπ hker hn φ hout
  rw [sLocalTraceQuotient_normPowerMellin π hπ.surjective hn φ b hb s]
  congr 1
  let p (j : Jₛ) : ℂ := (((sIdeleQuotientNorm F S j).val : ℝ) : ℂ) ^ s
  have hp : Continuous p := (Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp
    (Units.continuous_val.comp (isProperMap_sIdeleQuotientNorm F S).continuous))).cpow
      continuous_const (fun j ↦ Complex.ofReal_mem_slitPlane.mpr (NNReal.coe_pos.mpr (Units.zero_lt _)))
  have hLift' (g : Iₛ) : HasSum (fun ξ : sProjectedDiagonal F S ↦ f.val (ξ.val * g)) (b.val (qS g)) := by
    rw [← hs, hb]
    exact hLift g
  have hq (g : Iₛ) : sIdeleQuotientNorm F S (qS g) = sIdeleNorm F S g := sIdeleQuotientNorm_mk F S g
  simpa only [p, hq] using (sLocalTraceLift_weighted_integral f b.val hLift' p hp).symm

end Lift

end RiemannMasullo
