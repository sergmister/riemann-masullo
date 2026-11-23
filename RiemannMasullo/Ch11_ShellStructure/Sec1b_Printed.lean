module

public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec2
public import RiemannMasullo.Ch11_ShellStructure.Sec1b

import RiemannMasullo.AppA_AlgebraicNT.Sec3

/-!
# Printed claims in §11.1.2

The repaired statements are in Sec1b.lean.
-/

@[expose] public noncomputable section

open Filter IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false

local notation "V[" F "]" => HeightOneSpectrum (𝓞 F)
local notation "C[" F "]" => IdeleClassGroup (𝓞 F) F
local notation "ω[" F ", " χ "]" =>
  (χ).comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ :
    (ideleClassNorm F).ker →ₜ* C[F])
local notation "norm[" F "]" => fun g : C[F] ↦ ((ideleClassNorm F g).val : ℝ)
local notation "band[" b ", " Λ "]" => sLocalCarvingBand b Λ
local notation "bandMeasurable[" b ", " Λ "]" => measurableSet_sLocalCarvingBand b Λ

local instance instIdeleClassMeasurableSpaceSec1bPrinted (F : Type*) [Field F] [NumberField F] :
    MeasurableSpace C[F] := borel _
local instance instIdeleClassBorelSpaceSec1bPrinted (F : Type*) [Field F] [NumberField F] :
    BorelSpace C[F] := ⟨rfl⟩

/-- Paper: Theorem 11.1.2.1(2), p. 480, strictness in (11.1.2.6).
The printed claim requires a strictly smaller closed cutoff stage along a
subsequence of every increasing exhaustion by radii, for each cutoff choice. -/
def Printed.sLocalCutoffCarving_strictSubsequence : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C[F]) (S : Finset V[F]),
    ideleClassNormTwist χ 0 ∈ unramifiedOutside F S →
    Subsingleton (CommRing.Pic (Set.integer (R := 𝓞 F) (S : Set V[F]) F)) →
    ∀ s : ℝ, 2 * (Module.finrank ℚ F : ℝ) ≤ s →
    ∀ i i' : SLocalCarvingIndex (F := F) S, i < i' →
    (∃ p : ℕ, p.Prime ∧ (∀ v ∈ i.val, (p : 𝓞 F) ∉ v.asIdeal) ∧
      ∃ v ∈ i'.val, (p : 𝓞 F) ∈ v.asIdeal) →
    ∀ (twoSided : Bool) (Λ : ℕ → ℝ), (∀ k, 0 < Λ k) → Monotone Λ →
      Tendsto Λ atTop atTop →
      ∃ k : ℕ → ℕ, StrictMono k ∧ ∀ m,
        sLocalCutoffCarving s (ω[F, χ]) i'.val (band[twoSided, Λ (k m)])
            (bandMeasurable[twoSided, Λ (k m)]) <
          sLocalCutoffCarving s (ω[F, χ]) i.val (band[twoSided, Λ (k m)])
            (bandMeasurable[twoSided, Λ (k m)])

/-- Paper: Theorem 11.1.2.1(2), p. 480, strictness in (11.1.2.6).
Take F = ℚ, the trivial character, S with no finite places, s = 2, the empty
index and the singleton at 2. Use bounded cutoffs with radii k + 2. On the
logarithmic line the principal value is I − T, where T translates by log 2
up to sign. The theta test space is translation invariant. Applying I − T
to a finite sum of translates of a test gives the test minus a distant
translate, which tends to zero after cutting off to any bounded window.
Thus the two closed stages are equal at every radius in the sequence. -/
theorem Printed.sLocalCutoffCarving_strictSubsequence_false :
    ¬ Printed.sLocalCutoffCarving_strictSubsequence := by sorry

/-- Paper: Theorem 11.1.2.1(3), p. 480, (11.1.2.7). The printed
generators are the raw cutoff theta series for all tests with both
polar values zero. Each raw generator must represent a weighted L² vector,
and the limit must be the closed span of those vectors. -/
def Printed.sLocalCarvingLimit_eq_rawClosedSpan : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C[F]) (S : Finset V[F]),
    ideleClassNormTwist χ 0 ∈ unramifiedOutside F S →
    Subsingleton (CommRing.Pic (Set.integer (R := 𝓞 F) (S : Set V[F]) F)) →
    ∀ (s : ℝ), 2 * (Module.finrank ℚ F : ℝ) ≤ s →
    ∀ (twoSided : Bool) (Λ : ℝ), 0 < Λ →
      let J := band[twoSided, Λ]
      let E := norm[F] ⁻¹' J
      let ν := (ideleClassTamagawaMeasure F).withDensity
        (fun g ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (Real.log (norm[F] g))))
      let raw := fun f ↦ E.indicator (sLocalCarvingTheta S f)
      (∀ f : sAdelePolarSubspace F S, MemLp (raw f.val) 2 ν) ∧
        sLocalCarvingLimit s (ω[F, χ]) S J (bandMeasurable[twoSided, Λ]) =
          (Submodule.span ℂ {u : IdeleClassZeroLineSobolev F s |
            ∃ f : sAdelePolarSubspace F S, (u : C[F] → ℂ) =ᵐ[ν] raw f.val}).topologicalClosure

/-- Paper: Theorem 11.1.2.1(3), p. 480, (11.1.2.7).
Take F = ℚ, the even quadratic character modulo 5, S with finite part {5},
s = 2 and the two-sided cutoff with radius 2. Take the local test with 5-adic
factor 1_{ℤ₅} and an even real bump supported at absolute values in (3/4, 5/4),
positive near 1. Subtract an even bump at absolute values in (1/4, 1/3)
to cancel the additive integral. The resulting raw theta is norm-one invariant
and is nonzero near norm 1, where the only contributing rationals are ±1.
It cannot belong to the nontrivial isotype of the left side. -/
theorem Printed.sLocalCarvingLimit_eq_rawClosedSpan_false :
    ¬ Printed.sLocalCarvingLimit_eq_rawClosedSpan := by sorry

/-- Paper: (11.1.2.9), p. 481. The printed lower-half-line integral is
claimed to compute the cutoff norm for both choices of cutoff. -/
def Printed.sLocalCarving_cutoff_norm : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C[F]) (S : Finset V[F]),
    ideleClassNormTwist χ 0 ∈ unramifiedOutside F S →
    Subsingleton (CommRing.Pic (Set.integer (R := 𝓞 F) (S : Set V[F]) F)) →
    ∀ (s : ℝ), 2 * (Module.finrank ℚ F : ℝ) ≤ s →
    ∀ (twoSided : Bool) (Λ : ℝ), 0 < Λ →
    ∀ f : adelePolarSubspace F,
      let μ := ideleClassTamagawaMeasure F
      let ν := μ.withDensity
        (fun g ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (Real.log (norm[F] g))))
      let m : C[F] →ₜ* ℝ≥0ˣ := ⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩
      let θ := homogeneousAdelicTheta (ω[F, χ]) f.val
      let u := (memLp_homogeneousTheta_zeroLine s (ω[F, χ]) f).toLp θ
      ‖modulatedAbsoluteCutoffOperator m ν (band[twoSided, Λ]) (bandMeasurable[twoSided, Λ]) u‖ =
        Real.sqrt (∫ g in (norm[F] ⁻¹' Ici Λ⁻¹), ‖θ g‖ ^ 2 *
          (1 + Real.log (norm[F] g) ^ 2) ^ (s / 2) ∂μ)

private theorem sLocalCarving_cutoff_norm_false_pos (f : adelePolarSubspace ℚ)
    (g₀ : IdeleClassGroup (𝓞 ℚ) ℚ)
    (hg₀ : 2 < ((ideleClassNorm ℚ g₀).val : ℝ))
    (hθ₀ : homogeneousAdelicTheta (1 : PontryaginDual (ideleClassNorm ℚ).ker) f.val g₀ ≠ 0) :
    0 < ∫ g in ((fun g : IdeleClassGroup (𝓞 ℚ) ℚ ↦ ((ideleClassNorm ℚ g).val : ℝ)) ⁻¹' Ici 2),
      ‖homogeneousAdelicTheta (1 : PontryaginDual (ideleClassNorm ℚ).ker) f.val g‖ ^ 2 *
        (1 + Real.log (((ideleClassNorm ℚ g).val : ℝ)) ^ 2) ∂(ideleClassTamagawaMeasure ℚ) := by
  let μ := ideleClassTamagawaMeasure ℚ
  let n : IdeleClassGroup (𝓞 ℚ) ℚ → ℝ :=
    fun g ↦ ((ideleClassNorm ℚ g).val : ℝ)
  let θ := homogeneousAdelicTheta (1 : PontryaginDual (ideleClassNorm ℚ).ker) f.val
  let w : IdeleClassGroup (𝓞 ℚ) ℚ → ℝ := fun g ↦ 1 + Real.log (n g) ^ 2
  let E := n ⁻¹' Ici 2
  let q : IdeleClassGroup (𝓞 ℚ) ℚ → ℝ := fun g ↦ ‖θ g‖ ^ 2 * w g
  change 0 < ∫ g in E, q g ∂μ
  have hn : Continuous n :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp
      (isProperMap_ideleClassNorm ℚ).continuous)
  have hlogcont : Continuous (fun g ↦ Real.log (n g)) := by
    apply continuous_iff_continuousAt.mpr
    intro g
    apply (Real.continuousAt_log _).comp hn.continuousAt
    exact ne_of_gt (NNReal.coe_pos.mpr (Units.zero_lt (ideleClassNorm ℚ g)))
  have hw : ∀ g, 0 ≤ w g := by
    intro g
    dsimp [w]
    positivity
  have hq : ∀ g, 0 ≤ q g := by
    intro g
    dsimp [q]
    positivity
  have hmem := memLp_homogeneousTheta_zeroLine (F := ℚ) 2
    (1 : PontryaginDual (ideleClassNorm ℚ).ker) f
  have hd : Measurable (fun g : IdeleClassGroup (𝓞 ℚ) ℚ ↦
      ENNReal.ofReal (intervalSobolevDensity 0 0 2 (Real.log (n g)))) := by
    convert ((measurable_const : Measurable
      (fun _ : IdeleClassGroup (𝓞 ℚ) ℚ ↦ (1 : ℝ))).add
      (hlogcont.measurable.pow_const 2)).ennreal_ofReal using 1
    funext g
    simp [intervalSobolevDensity]
  have hfin : ∀ᵐ g ∂μ, ENNReal.ofReal (intervalSobolevDensity 0 0 2 (Real.log (n g))) < ⊤ :=
    .of_forall fun _ ↦ ENNReal.ofReal_lt_top
  have hsq : Integrable (fun g ↦ ‖θ g‖ ^ 2)
      (μ.withDensity fun g ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 2 (Real.log (n g)))) := by
    have h := hmem.integrable_norm_rpow two_ne_zero ENNReal.ofNat_ne_top
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h
  have hqint : Integrable q μ := by
    have h := (integrable_withDensity_iff_integrable_smul' hd hfin).mp hsq
    refine h.congr (.of_forall fun g ↦ ?_)
    have hw_eq : intervalSobolevDensity 0 0 2 (Real.log (n g)) = w g := by
      simp [intervalSobolevDensity, w]
    simp only [hw_eq, ENNReal.toReal_ofReal (hw g), smul_eq_mul, mul_comm]
    rfl
  let U := {g : IdeleClassGroup (𝓞 ℚ) ℚ | 2 < n g ∧ θ g ≠ 0}
  have hUopen : IsOpen U :=
    (isOpen_lt continuous_const hn).inter (isOpen_ne.preimage θ.continuous)
  have hUne : U.Nonempty := ⟨g₀, hg₀, hθ₀⟩
  let : μ.IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil ℚ).1
  have hUpos : 0 < μ U := hUopen.measure_pos μ hUne
  have hUsub : U ⊆ Function.support q ∩ E := by
    intro g hg
    constructor
    · dsimp [Function.support, q]
      have hwpos : 0 < w g := by dsimp [w]; positivity
      exact mul_ne_zero (pow_ne_zero _ (norm_ne_zero_iff.mpr hg.2)) (ne_of_gt hwpos)
    · exact le_of_lt hg.1
  have hmeasure : 0 < μ (Function.support q ∩ E) :=
    lt_of_lt_of_le hUpos (measure_mono hUsub)
  exact (setIntegral_pos_iff_support_of_nonneg_ae (.of_forall hq) hqint.integrableOn).2 hmeasure

private theorem sLocalCarving_cutoff_norm_false_pic :
    Subsingleton (CommRing.Pic (Set.integer (R := 𝓞 ℚ)
      ((∅ : Finset (HeightOneSpectrum (𝓞 ℚ))) : Set (HeightOneSpectrum (𝓞 ℚ))) ℚ)) := by
  rw [Finset.coe_empty, integer_empty]
  let e := (Algebra.botEquivOfInjective (IsFractionRing.injective (𝓞 ℚ) ℚ)).toRingEquiv
  let i := Rat.ringOfIntegersEquiv.symm.trans e.symm
  let := IsPrincipalIdealRing.of_surjective i i.surjective
  infer_instance

private theorem sLocalCarving_cutoff_norm_false_unramified :
    ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)) 0 ∈ unramifiedOutside ℚ ∅ := by
  have h1 : ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)) 0 = 1 := by
    ext g
    change (1 : ℂ) * (((ideleClassNorm ℚ g).val : ℝ) : ℂ) ^ (0 : ℂ) = 1
    simp
  rw [h1]
  exact (mem_unramifiedOutside_iff ℚ ∅ 1).mpr (fun _ _ _ ↦ rfl)

private theorem sLocalCarving_cutoff_norm_false_translate
    (u : IdeleGroup (𝓞 ℚ) ℚ) (f : SchwartzBruhat (Multiplicative 𝔸[ℚ]))
    (a : IdeleClassGroup (𝓞 ℚ) ℚ) :
    homogeneousAdelicTheta (1 : PontryaginDual (ideleClassNorm ℚ).ker)
      (schwartzBruhatUnitTranslate u f) a =
    homogeneousAdelicTheta (1 : PontryaginDual (ideleClassNorm ℚ).ker) f
      ((QuotientGroup.mk u)⁻¹ * a) := by
  have ht (a : IdeleClassGroup (𝓞 ℚ) ℚ) :
      adelicTheta (schwartzBruhatUnitTranslate u f) a =
        adelicTheta f ((QuotientGroup.mk u)⁻¹ * a) := by
    induction a using QuotientGroup.induction_on with | H x => ?_
    change _ = adelicTheta f (QuotientGroup.mk (u⁻¹ * x))
    rw [adelicTheta_mk (schwartzBruhatUnitTranslate u f) x, adelicTheta_mk f (u⁻¹ * x)]
    exact tsum_congr fun t ↦ congrArg (fun y ↦ f (Multiplicative.ofAdd y))
      (mul_left_comm u.inv (algebraMap ℚ 𝔸[ℚ] (t : ℚ)) x.val)
  refine congrArg (integral _) (funext fun h ↦ ?_)
  refine congrArg (· * ((1 : PontryaginDual (ideleClassNorm ℚ).ker) h : ℂ)) ?_
  rw [ht, mul_left_comm]

private theorem sLocalCarving_cutoff_norm_false_integral_translate
    (u : IdeleGroup (𝓞 ℚ) ℚ) (k : 𝔸[ℚ] → ℂ) :
    ∫ x, k ((↑u⁻¹ : 𝔸[ℚ]) * x) ∂additiveTamagawaMeasure ℚ =
      (((ideleNorm ℚ u).val : ℝ) : ℂ) * ∫ x, k x ∂additiveTamagawaMeasure ℚ := by
  let : MeasurableSpace 𝔸[ℚ] := borel _
  have : BorelSpace 𝔸[ℚ] := ⟨rfl⟩
  have hH : (additiveTamagawaMeasure ℚ).IsAddHaarMeasure :=
    (additiveTamagawaMeasure_existsUnique ℚ).exists.choose_spec.1
  let d : 𝔸[ℚ] ≃ₜ 𝔸[ℚ] := Homeomorph.smul (u⁻¹ : IdeleGroup (𝓞 ℚ) ℚ)
  have hset (s : Set 𝔸[ℚ]) :
      d ⁻¹' s = (fun a : 𝔸[ℚ] ↦ (u : 𝔸[ℚ]) * a) '' s := by
    ext y
    constructor
    · intro hy
      exact ⟨(↑u⁻¹ : 𝔸[ℚ]) * y, hy, Units.mul_inv_cancel_left u y⟩
    · rintro ⟨a, ha, rfl⟩
      change (↑u⁻¹ : 𝔸[ℚ]) * ((u : 𝔸[ℚ]) * a) ∈ s
      rwa [Units.inv_mul_cancel_left]
  have hmap : (additiveTamagawaMeasure ℚ).map d =
      ((ideleNorm ℚ u).val : ENNReal) • additiveTamagawaMeasure ℚ := by
    refine Measure.ext fun s hs ↦ ?_
    rw [Measure.map_apply d.continuous.measurable hs, hset s]
    exact adeleHaar_mul_image ℚ (additiveTamagawaMeasure ℚ) u s hs
  have h1 := (integral_map_equiv (μ := additiveTamagawaMeasure ℚ) d.toMeasurableEquiv k).symm
  have h2 : ((additiveTamagawaMeasure ℚ).map d.toMeasurableEquiv) =
      ((ideleNorm ℚ u).val : ENNReal) • additiveTamagawaMeasure ℚ := hmap
  rw [h2, integral_smul_measure, ENNReal.coe_toReal, Complex.real_smul] at h1
  exact h1

private theorem sLocalCarving_cutoff_norm_false_norm (r : ℝ) (hr : 0 < r) :
    ∃ g : IdeleClassGroup (𝓞 ℚ) ℚ, ((ideleClassNorm ℚ g).val : ℝ) = r := by
  let t : ℝ≥0ˣ := Units.mk0 ⟨r, hr.le⟩ (by exact ne_of_gt hr)
  refine ⟨QuotientGroup.mk (canonicalIdeleNormSection ℚ t), ?_⟩
  change ((ideleNorm ℚ (canonicalIdeleNormSection ℚ t)).val : ℝ) = r
  rw [canonicalIdeleNormSection_rightInverse]
  rfl

/-- A polar test has nonzero theta above norm two.
Otherwise dilation differences of a test with polar values `(1, 0)` force its
theta to be constant, contradicting its large- and small-norm asymptotics. -/
private theorem sLocalCarving_cutoff_norm_false_witness :
    ∃ (f : adelePolarSubspace ℚ) (g : IdeleClassGroup (𝓞 ℚ) ℚ),
      2 < ((ideleClassNorm ℚ g).val : ℝ) ∧
        homogeneousAdelicTheta (1 : PontryaginDual (ideleClassNorm ℚ).ker) f.val g ≠ 0 := by
  by_contra hn
  have hz (f : adelePolarSubspace ℚ) (g : IdeleClassGroup (𝓞 ℚ) ℚ)
      (hg : 2 < ((ideleClassNorm ℚ g).val : ℝ)) :
      homogeneousAdelicTheta (1 : PontryaginDual (ideleClassNorm ℚ).ker) f.val g = 0 := by
    by_contra h
    exact hn ⟨f, g, hg, h⟩
  obtain ⟨f, hf⟩ := (adelePolarValues_surjective (F := ℚ)) (1, 0)
  have hf0 : f (Multiplicative.ofAdd 0) = 1 := congrArg Prod.fst hf
  have hfF : adeleSchwartzFourier f (Multiplicative.ofAdd 0) = 0 := congrArg Prod.snd hf
  obtain ⟨a, ha⟩ := sLocalCarving_cutoff_norm_false_norm 3 (by norm_num)
  let θ := homogeneousAdelicTheta (1 : PontryaginDual (ideleClassNorm ℚ).ker) f
  have hconst (g : IdeleClassGroup (𝓞 ℚ) ℚ) : θ g = θ a := by
    obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (a * g⁻¹)
    let d := schwartzBruhatUnitTranslate u f
    have hdF : adeleSchwartzFourier d (Multiplicative.ofAdd 0) = 0 := by
      rw [(adeleSchwartzFourier_apply_zero d).2]
      change (∫ x, f (Multiplicative.ofAdd ((↑u⁻¹ : 𝔸[ℚ]) * x))
        ∂additiveTamagawaMeasure ℚ) = 0
      rw [sLocalCarving_cutoff_norm_false_integral_translate u (fun z ↦ f (Multiplicative.ofAdd z)),
        ← (adeleSchwartzFourier_apply_zero f).2, hfF, mul_zero]
    have hd0 : d (Multiplicative.ofAdd 0) = 1 := by
      change f (Multiplicative.ofAdd (u⁻¹.val * 0)) = 1
      simpa only [mul_zero] using hf0
    have hmem : d - f ∈ adelePolarSubspace ℚ := by
      change adelePolarValues (d - f) = 0
      rw [map_sub]
      apply Prod.ext
      · change d (Multiplicative.ofAdd 0) - f (Multiplicative.ofAdd 0) = 0
        rw [hd0, hf0, sub_self]
      · change adeleSchwartzFourier d (Multiplicative.ofAdd 0) -
          adeleSchwartzFourier f (Multiplicative.ofAdd 0) = 0
        rw [hdF, hfF, sub_self]
    have hh := hz ⟨d - f, hmem⟩ a (by rw [ha]; norm_num)
    let hlin := IsLinearMap.mk' _ (homogeneousAdelicTheta_isLinear
      (1 : PontryaginDual (ideleClassNorm ℚ).ker))
    have he := congrArg (fun z : C(IdeleClassGroup (𝓞 ℚ) ℚ, ℂ) ↦ z a)
      (hlin.map_sub d f)
    change homogeneousAdelicTheta (1 : PontryaginDual (ideleClassNorm ℚ).ker) (d - f) a =
      homogeneousAdelicTheta (1 : PontryaginDual (ideleClassNorm ℚ).ker) d a - θ a at he
    rw [he, sLocalCarving_cutoff_norm_false_translate, hu] at hh
    simpa only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one] using sub_eq_zero.mp hh
  obtain ⟨C, T, hC, hT, hlarge⟩ :=
    homogeneousAdelicTheta_decay_large (1 : PontryaginDual (ideleClassNorm ℚ).ker) f 1
  dsimp only at hlarge
  have hzero : θ a = 0 := by
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    by_contra h
    have hp : 0 < ‖θ a‖ := lt_of_not_ge h
    let r := T + C / ‖θ a‖ + 1
    have hr : 0 < r := by dsimp [r]; positivity
    obtain ⟨g, hg⟩ := sLocalCarving_cutoff_norm_false_norm r hr
    have hb := hlarge g (by rw [hg]; dsimp [r]; have := div_pos hC hp; linarith)
    rw [hg, pow_one, ← div_eq_mul_inv] at hb
    change ‖θ g‖ ≤ C / r at hb
    rw [hconst g] at hb
    have hh := (le_div_iff₀ hr).mp hb
    have hcancel : C / ‖θ a‖ * ‖θ a‖ = C := div_mul_cancel₀ C hp.ne'
    dsimp [r] at hh
    nlinarith [mul_pos hT hp]
  obtain ⟨D, U, hD, hU, hsmall⟩ :=
    homogeneousAdelicTheta_decay_small (1 : PontryaginDual (ideleClassNorm ℚ).ker) f 1
  dsimp only at hsmall
  let : MeasurableSpace (IdeleClassGroup (𝓞 ℚ) ℚ) := borel _
  let : BorelSpace (IdeleClassGroup (𝓞 ℚ) ℚ) := ⟨rfl⟩
  let μ := normOneIdeleClassTamagawaMeasure ℚ
  let : CompactSpace (ideleClassNorm ℚ).ker := (ideleClassGroup_finiteness ℚ).2.1
  let : μ.IsHaarMeasure :=
    (multiplicativeTamagawaMeasures_existsUnique ℚ).exists.choose_spec.2.2.2.1
  have hm : 0 < μ.real univ := measureReal_univ_pos
  let r := min (U / 2) (μ.real univ / (2 * D))
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  obtain ⟨g, hg⟩ := sLocalCarving_cutoff_norm_false_norm r hr
  have hrU : r < U := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hb := hsmall g (by rw [hg]; exact hrU)
  have hp : homogeneousAdelicTheta_polarTerm
      (1 : PontryaginDual (ideleClassNorm ℚ).ker) f g = -(μ.real univ : ℂ) := by
    simp only [homogeneousAdelicTheta_polarTerm, ↓reduceIte, hfF, hf0, smul_zero, zero_sub, smul_neg, Complex.real_smul, mul_one]
    rfl
  rw [hp, show homogeneousAdelicTheta (1 : PontryaginDual (ideleClassNorm ℚ).ker) f g = 0
    from (hconst g).trans hzero, hg, pow_one, zero_sub, neg_neg,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm] at hb
  have hrbound : r ≤ μ.real univ / (2 * D) := min_le_right _ _
  have hh := (le_div_iff₀ (by positivity : 0 < 2 * D)).mp hrbound
  nlinarith

/-- Paper: (11.1.2.9), p. 481. Use F = ℚ, the trivial character, S with no
finite places, s = 2, and the two-sided radius 2 cutoff. Take the standard
integral factors at the finite places and an even real bump supported at
absolute values in (3, 4), positive near 7/2. Subtract an even bump below
absolute value 1/2, supported away from zero, to cancel the Fourier value at
zero. For norms near 7/2 only the terms ±1 contribute. This gives positive
norm mass in the lower half-line integral outside the bounded cutoff band. -/
theorem Printed.sLocalCarving_cutoff_norm_false :
    ¬ Printed.sLocalCarving_cutoff_norm := by
  intro hprinted
  obtain ⟨f, g, hg, hθ⟩ := sLocalCarving_cutoff_norm_false_witness
  have hs : 2 * (Module.finrank ℚ ℚ : ℝ) ≤ (2 : ℝ) := by simp
  have hband : sLocalCarvingBand true (1 / 2 : ℝ) = ∅ := by
    simp only [sLocalCarvingBand, ite_true]
    apply Icc_eq_empty_of_lt
    norm_num
  have hω : (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)).comp
      (⟨(ideleClassNorm ℚ).ker.subtype, continuous_subtype_val⟩ :
        (ideleClassNorm ℚ).ker →ₜ* IdeleClassGroup (𝓞 ℚ) ℚ) = 1 := by
    ext g
    rfl
  let ω := (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)).comp
      (⟨(ideleClassNorm ℚ).ker.subtype, continuous_subtype_val⟩ :
        (ideleClassNorm ℚ).ker →ₜ* IdeleClassGroup (𝓞 ℚ) ℚ)
  let θ := homogeneousAdelicTheta ω f.val
  let u := (memLp_homogeneousTheta_zeroLine 2 ω f).toLp θ
  have hcorr := (RiemannMasullo.sLocalCarving_cutoff_norm 2 true (1 / 2 : ℝ) u).2
  have hzero : ‖modulatedAbsoluteCutoffOperator
        (⟨ideleClassNorm ℚ, (isProperMap_ideleClassNorm ℚ).continuous⟩ :
          IdeleClassGroup (𝓞 ℚ) ℚ →ₜ* ℝ≥0ˣ)
        ((ideleClassTamagawaMeasure ℚ).withDensity
          (fun g ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 2
            (Real.log (((ideleClassNorm ℚ g).val : ℝ))))))
        (sLocalCarvingBand true (1 / 2 : ℝ))
        (measurableSet_sLocalCarvingBand true (1 / 2 : ℝ)) u‖ = 0 := by
    simpa only [hband, Set.preimage_empty, setIntegral_empty, Real.sqrt_zero] using hcorr
  have hpos := sLocalCarving_cutoff_norm_false_pos f g hg hθ
  have hclaim := hprinted ℚ 1 ∅ sLocalCarving_cutoff_norm_false_unramified
    sLocalCarving_cutoff_norm_false_pic 2 hs true (1 / 2 : ℝ) (by norm_num) f
  dsimp only at hclaim
  rw [hzero] at hclaim
  have hpos' : 0 < Real.sqrt (∫ g in ((fun g : IdeleClassGroup (𝓞 ℚ) ℚ ↦
      ((ideleClassNorm ℚ g).val : ℝ)) ⁻¹' Ici (1 / 2 : ℝ)⁻¹),
      ‖θ g‖ ^ 2 * (1 + Real.log (((ideleClassNorm ℚ g).val : ℝ)) ^ 2) ^ (2 / 2 : ℝ)
      ∂(ideleClassTamagawaMeasure ℚ)) := by
    convert (Real.sqrt_pos.2 hpos) using 1
    congr 1
    simp only [θ, ω, hω, show (1 / 2 : ℝ)⁻¹ = 2 by norm_num,
      show (2 / 2 : ℝ) = 1 by norm_num, Real.rpow_one]
    rfl
  exact (ne_of_gt hpos') hclaim.symm


end RiemannMasullo
