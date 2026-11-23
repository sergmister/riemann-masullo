module

public import RiemannMasullo.Ch05_ThetaZSpaces.Sec4
import all RiemannMasullo.Ch07_SchauderBasesZeta.Sec1a
import all RiemannMasullo.Ch05_ThetaZSpaces.Sec4
import all RiemannMasullo.Ch02_AdelicTheta.Sec3
import all RiemannMasullo.Ch04_PeriodicSchauderBases.Sec6

/-!
# Chapter 5.4: statements that are false as printed

The printed claims are propositions, with separate statements of their negations.
The corresponding results are in `Sec4.lean` and the errata are recorded in `ERRATA.md`.
-/

@[expose] public noncomputable section

namespace RiemannMasullo

open Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal

set_option quotPrecheck false
set_option maxSynthPendingDepth 8

local notation "Test(" A ")" => SchwartzBruhat (Multiplicative (A))
local notation "normℂ(" t ")" => (((t : ℝ≥0ˣ).val : ℝ) : ℂ)
local notation "restrict₁(" F ", " S ", " χ ")" => ((χ : PontryaginDual (SIdeleQuotient F S)).comp
  (⟨(sIdeleQuotientNorm F S).ker.subtype, continuous_subtype_val⟩ :
    (sIdeleQuotientNorm F S).ker →ₜ* SIdeleQuotient F S))
local notation "ρₛ(" field ", " places ", " χ ", " s ")" =>
  sLocalRhoFactor (F := field) (S := places)
    (quasiCharacterNormTwist (sIdeleQuotientNorm field places)
      (isProperMap_sIdeleQuotientNorm field places).continuous
      ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp (χ)) (s))

local notation "rightInterval" => Ioi (0 : ℝ)
local notation "leftInterval" => Iio (1 : ℝ)
local notation "rightHalf" => Complex.re ⁻¹' rightInterval
local notation "leftHalf" => Complex.re ⁻¹' leftInterval
local notation "overlap" => Complex.re ⁻¹' Ioo (0 : ℝ) 1
local notation "B⁺" => SchwartzBergman rightInterval
local notation "B⁻" => SchwartzBergman leftInterval
local notation "Eω(" field ", " places ", " I ", " ω ")" =>
  ↥(sLocalDecayIsotype (F := field) (S := places) (I) (ω))

/-- Paper: Theorem 5.4.1.1(1), p. 266.
As printed: the Fourier coordinate of the zeta pair is equivariant with multiplier
`t^(1-s) · ω̄(k)` for translation by the class `τ(t)k`. This records the second
coordinate on the common strip where the printed range `Re s > 0` meets the Fourier
coordinate’s domain `Re s < 1`. Character inversion expresses conjugation.
Remark 5.4.1.2 and Proposition 5.4.1.4 repeat this multiplier. The repaired declarations are
`sLocalZetaPair_translate` and `exists_sLocalZetaPair_action`. See ERRATA F60. -/
def Printed.sLocalZetaPair_translate : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))),
    let A := SAdeleRing F S
    let J := SIdeleQuotient F S
    let m := sIdeleQuotientNorm F S
    ∀ (τ : ℝ≥0ˣ →ₜ* J) (hτ : RightInverse τ m) (ω : PontryaginDual m.ker),
      let χ := (existsUnique_sLocalNormSectionCharacter (F := F) (S := S) τ hτ ω).exists.choose
      ∀ (u : Aˣ) (t : ℝ≥0ˣ) (k : m.ker) (f : Test(A)),
        (QuotientGroup.mk u : J) = τ t * k.val →
        let U := sLocalZetaPair (F := F) (S := S) χ
        let p := U (Submodule.Quotient.mk f)
        let q := U (Submodule.Quotient.mk (schwartzBruhatUnitTranslate (R := A) u f))
        EqOn q.2.val (fun s ↦ normℂ(t) ^ (1 - s) * ((ω⁻¹) k : ℂ) * p.2.val s) overlap

/-- A strictly positive integrable real function has nonzero complex integral. -/
private theorem Printed.sLocalZetaPair_translate_false_integral {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [NeZero μ] (g : X → ℝ)
    (hi : Integrable (fun x ↦ (g x : ℂ)) μ) (hp : ∀ x, 0 < g x) :
    (∫ x, (g x : ℂ) ∂μ) ≠ 0 := by
  have hi' : Integrable g μ := by simpa using hi.re
  have hs : Function.support g = univ := by ext x; simp [Function.mem_support, (hp x).ne']
  have hpos : 0 < ∫ x, g x ∂μ :=
    (integral_pos_iff_support_of_nonneg (fun x ↦ (hp x).le) hi').2
      (by rw [hs]; exact Measure.measure_univ_pos.mpr (NeZero.ne μ))
  exact (integral_complex_ofReal (f := g) (μ := μ)).trans_ne
    (Complex.ofReal_ne_zero.mpr hpos.ne')

/-- The rational Gaussian has a strictly positive radial Mellin integral at one quarter. -/
private theorem Printed.sLocalZetaPair_translate_false_gaussian
    (σ : ℝ≥0ˣ →ₜ* (SAdeleRing ℚ ∅)ˣ)
    (hσ : RightInverse σ (sIdeleNorm ℚ ∅)) :
    ∃ f : SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅)),
      sLocalIdelicZFunction f (quasiCharacterNormTwist (sIdeleQuotientNorm ℚ ∅)
        (isProperMap_sIdeleQuotientNorm ℚ ∅).continuous
        ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp (1 : PontryaginDual (SIdeleQuotient ℚ ∅))) (1/4)) ≠ 0 := by
  let m := sIdeleQuotientNorm ℚ ∅
  let : MeasurableSpace m.ker := borel m.ker
  let μ := sLocalNormOneQuotientMeasure ℚ ∅
  let : μ.IsHaarMeasure := (sLocalNormOneQuotientMeasure_normProduct (F := ℚ) (S := ∅)).1
  let : CompactSpace m.ker := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm ℚ ∅).isCompact_preimage (isCompact_singleton (x := 1)))
  let : IsFiniteMeasure μ := CompactSpace.isFiniteMeasure (μ := μ)
  let : positiveRealHaar.IsHaarMeasure := positiveRealHaar_isHaarMeasure
  let c : ℝ := μ.real univ
  have hc : 0 < c := measureReal_univ_pos (μ := μ)
  obtain ⟨f,hf⟩ := sLocalHomogeneousAdelicTheta_rat_not_isBigO_sqrt_gaussian
  let r (t : ℝ≥0ˣ) : ℝ := t.val
  let g (t : ℝ≥0ˣ) : ℝ := c * (2 * Real.exp (-(r t ^ 2))) * (r t) ^ (1/4 : ℝ)
  have hp (t : ℝ≥0ˣ) : 0 < g t :=
    mul_pos (mul_pos hc (mul_pos (by norm_num) (Real.exp_pos _)))
      (Real.rpow_pos_of_pos (NNReal.coe_pos.mpr (Units.zero_lt t)) _)
  have he (t : ℝ≥0ˣ) :
      sLocalHomogeneousAdelicTheta ℚ ∅ μ 1 f (QuotientGroup.mk (σ t)) *
        quasiCharacterNormTwist m (isProperMap_sIdeleQuotientNorm ℚ ∅).continuous
          ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp (1 : PontryaginDual (SIdeleQuotient ℚ ∅))) (1/4)
            (QuotientGroup.mk (σ t)) = (g t : ℂ) := by
    have hq : m (QuotientGroup.mk (σ t)) = t := hσ t
    have hpow : (r t : ℂ) ^ (1/4 : ℂ) = (((r t) ^ (1/4 : ℝ) : ℝ) : ℂ) := by
      simpa using (Complex.ofReal_cpow (show 0 ≤ r t from NNReal.coe_nonneg _) (1/4 : ℝ)).symm
    change sLocalHomogeneousAdelicTheta ℚ ∅ μ 1 f (QuotientGroup.mk (σ t)) *
      (1 * (((m (QuotientGroup.mk (σ t))).val : ℝ) : ℂ) ^ (1/4 : ℂ)) = _
    rw [sLocalHomogeneousAdelicTheta_rat_not_isBigO_sqrt_eval f hf, hq]
    change (c : ℂ) * (2 * (Real.exp (-(r t ^ 2)) : ℂ)) * (1 * (r t : ℂ) ^ (1/4 : ℂ)) = _
    rw [hpow]
    simp [g]
  have hi := sLocalRadialMellinIntegral_integrable σ hσ f 1 (1/4) (by norm_num)
  have hi' : Integrable (fun t ↦ (g t : ℂ)) positiveRealHaar := hi.congr (.of_forall he)
  have hnonzero := Printed.sLocalZetaPair_translate_false_integral positiveRealHaar g hi' hp
  have hrad : sLocalRadialMellinIntegral σ f 1 (1/4) = ∫ t, (g t : ℂ) ∂positiveRealHaar :=
    integral_congr_ae (.of_forall he)
  let c₀ := quasiCharacterNormTwist m (isProperMap_sIdeleQuotientNorm ℚ ∅).continuous
    ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp (1 : PontryaginDual (SIdeleQuotient ℚ ∅))) (1/4)
  have hr : ∃ (χ : PontryaginDual (SIdeleQuotient ℚ ∅)) (s : ℂ), 0 < s.re ∧
      c₀ = quasiCharacterNormTwist m (isProperMap_sIdeleQuotientNorm ℚ ∅).continuous
        ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ) s :=
    ⟨1,1/4,by norm_num,rfl⟩
  have hz : sLocalRadialMellinIntegral σ f 1 (1/4) = sLocalIdelicZFunction f c₀ :=
    (sLocalRadialMellinIntegral_eq_theta σ hσ f 1 (1/4) (by norm_num)).trans
      ((sLocalThetaMellinIntegral_eq_zeta f hr).trans (sLocalIdelicZFunction_eq_integral f hr).symm)
  exact ⟨f, fun h ↦ hnonzero (hrad.symm.trans (hz.trans h))⟩

/-- Paper: Theorem 5.4.1.1(1), p. 266.
Take `F = ℚ`, no finite places, the positive-real norm section, and `ω = 1`.
The Gaussian `exp(−x²)` has a nonzero first zeta coordinate at `s = 1/4`, since
its radial Mellin integrand is strictly positive. The functional equation then
forces the reflected Fourier coordinate to be nonzero there. Translation by a
norm-two idele multiplies this coordinate by `2^(1/4)`, while the printed rule
multiplies it by `2^(3/4)`, contradicting strict monotonicity of real powers. -/
theorem Printed.sLocalZetaPair_translate_false : ¬ Printed.sLocalZetaPair_translate := by
  intro h
  let p := Units.map (adeleProjection ℚ ∅).toMonoidHom
  have hp : Continuous p := (continuous_fst.prodMk (continuous_pi fun v : (∅ : Finset (HeightOneSpectrum (𝓞 ℚ))) ↦
    (RestrictedProduct.continuous_eval v.val).comp continuous_snd)).units_map _
  let σ : ℝ≥0ˣ →ₜ* (SAdeleRing ℚ ∅)ˣ := ⟨p.comp (canonicalIdeleNormSection ℚ),
    hp.comp (canonicalIdeleNormSection_continuous ℚ)⟩
  have hσ : RightInverse σ (sIdeleNorm ℚ ∅) := thetaSection_rightInverse ℚ ∅
  let q : (SAdeleRing ℚ ∅)ˣ →ₜ* SIdeleQuotient ℚ ∅ := ⟨QuotientGroup.mk' _, QuotientGroup.continuous_mk⟩
  let τ := q.comp σ
  have hτ : RightInverse τ (sIdeleQuotientNorm ℚ ∅) := hσ
  let χ : PontryaginDual (SIdeleQuotient ℚ ∅) :=
    (existsUnique_sLocalNormSectionCharacter τ hτ 1).exists.choose
  have hχ : χ = 1 := (existsUnique_sLocalNormSectionCharacter τ hτ 1).unique
    (existsUnique_sLocalNormSectionCharacter τ hτ 1).exists.choose_spec ⟨rfl, fun _ ↦ rfl⟩
  obtain ⟨f,hf⟩ := Printed.sLocalZetaPair_translate_false_gaussian σ hσ
  let t : ℝ≥0ˣ := Units.mk0 2 (by norm_num)
  have hrel : (QuotientGroup.mk (σ t) : SIdeleQuotient ℚ ∅) =
      τ t * (1 : (sIdeleQuotientNorm ℚ ∅).ker).val := (mul_one _).symm
  let P := sLocalZetaPair χ (Submodule.Quotient.mk f)
  have hP : P.2.val (1/4) ≠ 0 := by
    intro hz
    have he := existsUnique_sLocalZetaPair_equation χ f (1/4) (by norm_num)
    have hright := (sLocalZetaPair_mk χ f).2 (show (1/4 : ℂ).re < 1 by norm_num)
    have hf' : sLocalIdelicZFunction f (quasiCharacterNormTwist (sIdeleQuotientNorm ℚ ∅)
        (isProperMap_sIdeleQuotientNorm ℚ ∅).continuous
        ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ) (1/4)) ≠ 0 := by
      rw [hχ]
      with_reducible_and_instances exact hf
    exact hf' (he.trans ((congrArg (fun z : ℂ ↦ _ * z) (hright.symm.trans hz)).trans (mul_zero _)))
  have ha := (RiemannMasullo.sLocalZetaPair_translate χ (σ t) f).2 (show (1/4 : ℂ).re < 1 by norm_num)
  have hb := h ℚ ∅ τ hτ 1 (σ t) t 1 f hrel (show (1/4 : ℂ) ∈ Complex.re ⁻¹' Ioo (0 : ℝ) 1 by norm_num)
  have hm : quasiCharacterNormTwist (sIdeleQuotientNorm ℚ ∅)
      (isProperMap_sIdeleQuotientNorm ℚ ∅).continuous
      ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ) (1/4)
        (QuotientGroup.mk (σ t)) = (2 : ℂ) ^ (1/4 : ℂ) := by
    rw [hχ]
    change 1 * ((((sIdeleNorm ℚ ∅ (σ t)).val : ℝ) : ℂ) ^ (1/4 : ℂ)) = _
    rw [hσ]
    exact one_mul _
  have hfactor : ((((t.val : ℝ) : ℂ) ^ (1 - (1/4 : ℂ))) *
      (((1 : PontryaginDual (sIdeleQuotientNorm ℚ ∅).ker)⁻¹) 1 : ℂ)) =
      (2 : ℂ) ^ (3/4 : ℂ) := by norm_num [t]
  have heq : (2 : ℂ) ^ (1/4 : ℂ) * P.2.val (1/4) =
      (2 : ℂ) ^ (3/4 : ℂ) * P.2.val (1/4) :=
    ((congrArg (· * P.2.val (1/4)) hm).symm.trans ha.symm).trans
      (hb.trans (congrArg (· * P.2.val (1/4)) hfactor))
  have hpow := mul_right_cancel₀ hP heq
  have hreal : (2 : ℝ) ^ (1/4 : ℝ) = (2 : ℝ) ^ (3/4 : ℝ) := by
    apply Complex.ofReal_injective
    simpa only [Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 2), Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat] using hpow
  exact (Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2)
    (by norm_num : (1/4 : ℝ) < 3/4)).ne hreal

/-- Paper: Remark 5.4.1.2, p. 266.
As printed: for a unitary lift of section frequency `x`, the reflected Fourier coordinate
in the lift's chart is the normalized Fourier coordinate evaluated at `s − ix`. This records
the second vertical translation in the remark. `existsUnique_sLocalZetaPair` gives the chart
values, and `sLocalCech_left_commutes` gives the unreflected transforms. See ERRATA F61. -/
def Printed.sLocalZetaPair_reflectedShift : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))),
    let J := SIdeleQuotient F S
    ∀ (τ : ℝ≥0ˣ →ₜ* J) (hτ : RightInverse τ (sIdeleQuotientNorm F S))
      (χ : PontryaginDual J) (x : ℝ),
      (∀ t : ℝ≥0ˣ, (χ (τ t) : ℂ) = normℂ(t) ^ ((x : ℂ) * Complex.I)) →
      let χ₀ := (existsUnique_sLocalNormSectionCharacter (F := F) (S := S)
        τ hτ (restrict₁(F, S, χ))).exists.choose
      ∀ f : Test(SAdeleRing F S),
        let p := sLocalZetaPair (F := F) (S := S) χ (Submodule.Quotient.mk f)
        let p₀ := sLocalZetaPair (F := F) (S := S) χ₀ (Submodule.Quotient.mk f)
        EqOn p.2.val (fun s ↦ p₀.2.val (s - (x : ℂ) * Complex.I)) leftHalf

/-- A Schwartz–Bergman function constant on a vertical line vanishes there. -/
private theorem Printed.sLocalZetaPair_reflectedShift_false_vertical (I : Set ℝ) (p : SchwartzBergman I)
    (a : ℝ) (ha : a ∈ I) (hp : ∀ y : ℝ, p.val ((a : ℂ) + (y : ℂ) * Complex.I) = p.val a) :
    p.val a = 0 := by
  by_contra hn
  have hnpos : 0 < ‖p.val a‖ := norm_pos_iff.mpr hn
  obtain ⟨C,hC⟩ := p.property.2.2 a a le_rfl
    (by simpa only [Icc_self, singleton_subset_iff] using ha) 1
  obtain ⟨n,hn⟩ := exists_nat_gt (C / ‖p.val a‖)
  let z : ℂ := (a : ℂ) + (n : ℂ) * Complex.I
  have hz : z.re ∈ Icc a a := by simp [z]
  have hb := hC ⟨z,hz,rfl⟩
  have hv : p.val z = p.val a := by simpa only [Complex.ofReal_natCast] using hp n
  have hzn : (n : ℝ) ≤ ‖z‖ := by simpa [z] using Complex.abs_im_le_norm z
  have hlt : C < (n : ℝ) * ‖p.val a‖ := (div_lt_iff₀ hnpos).mp hn
  change ‖z ^ 1 * p.val z‖ ≤ C at hb
  rw [pow_one, norm_mul, hv] at hb
  exact (hlt.trans_le ((mul_le_mul_of_nonneg_right hzn hnpos.le).trans hb)).false
/-- A norm-frequency lift shifts the reflected Fourier coordinate by the positive frequency. -/
private theorem Printed.sLocalZetaPair_reflectedShift_false_coordinate (χ : PontryaginDual (SIdeleQuotient ℚ ∅)) (x : ℝ)
    (hχ : ∀ g, (χ g : ℂ) = ((((sIdeleQuotientNorm ℚ ∅ g).val : ℝ) : ℂ) ^ ((x : ℂ) * Complex.I)))
    (f : SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅)))
    (s : ℂ) (hs : s.re < 1) :
    (sLocalZetaPair χ (Submodule.Quotient.mk f)).2.val s =
      (sLocalZetaPair (1 : PontryaginDual (SIdeleQuotient ℚ ∅)) (Submodule.Quotient.mk f)).2.val
        (s + (x : ℂ) * Complex.I) := by
  let m := sIdeleQuotientNorm ℚ ∅
  let c (ψ : PontryaginDual (SIdeleQuotient ℚ ∅)) (z : ℂ) :=
    quasiCharacterNormTwist m (isProperMap_sIdeleQuotientNorm ℚ ∅).continuous
      ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp ψ) z
  have hc : c χ⁻¹ (1-s) = c 1⁻¹ (1-(s+(x:ℂ)*Complex.I)) := by
    apply ContinuousMonoidHom.ext
    intro g
    have hn : ((((m g).val : ℝ) : ℂ)) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (m g).ne_zero)
    change (χ⁻¹ g : ℂ) * ((((m g).val : ℝ) : ℂ) ^ (1-s)) =
      (((1 : PontryaginDual (SIdeleQuotient ℚ ∅))⁻¹ g : Circle) : ℂ) *
        ((((m g).val : ℝ) : ℂ) ^ (1-(s+(x:ℂ)*Complex.I)))
    simp only [inv_one, PontryaginDual.one_apply, Circle.coe_one]
    rw [show ((χ⁻¹ g : Circle) : ℂ) = (χ g : ℂ)⁻¹ from Circle.coe_inv (χ g),
      hχ g, ← Complex.cpow_neg, ← Complex.cpow_add _ _ hn, one_mul]
    congr 1
    ring
  have hs' : (s + (x : ℂ) * Complex.I).re < 1 := by simpa using hs
  exact ((sLocalZetaPair_mk χ f).2 hs).trans
    ((congrArg (sLocalIdelicZFunction (sAdeleSchwartzFourier f)) hc).trans
      ((sLocalZetaPair_mk (1 : PontryaginDual (SIdeleQuotient ℚ ∅)) f).2 hs').symm)

/-- Paper: Remark 5.4.1.2, p. 266.
Over the rationals with no finite places, the correct reflected coordinate for
`χ(g) = |g|^(ix)` is the trivial-character coordinate at `s + ix`. The printed
shift `s - ix`, applied for every real frequency, would make this coordinate
constant on the line `Re s = 1/4`. The weight-one Schwartz–Bergman bound forces
the constant to vanish. The rational Gaussian and the functional equation give
a nonzero value there, as in the translation refutation above. -/
theorem Printed.sLocalZetaPair_reflectedShift_false : ¬ Printed.sLocalZetaPair_reflectedShift := by
  intro h
  let p := Units.map (adeleProjection ℚ ∅).toMonoidHom
  have hp : Continuous p := (continuous_fst.prodMk (continuous_pi fun v : (∅ : Finset (HeightOneSpectrum (𝓞 ℚ))) ↦
    (RestrictedProduct.continuous_eval v.val).comp continuous_snd)).units_map _
  let σ : ℝ≥0ˣ →ₜ* (SAdeleRing ℚ ∅)ˣ := ⟨p.comp (canonicalIdeleNormSection ℚ),
    hp.comp (canonicalIdeleNormSection_continuous ℚ)⟩
  have hσ : RightInverse σ (sIdeleNorm ℚ ∅) := thetaSection_rightInverse ℚ ∅
  let q : (SAdeleRing ℚ ∅)ˣ →ₜ* SIdeleQuotient ℚ ∅ := ⟨QuotientGroup.mk' _, QuotientGroup.continuous_mk⟩
  let τ := q.comp σ
  let m := sIdeleQuotientNorm ℚ ∅
  have hτ : RightInverse τ m := hσ
  obtain ⟨f,hf⟩ := Printed.sLocalZetaPair_translate_false_gaussian σ hσ
  let ev (χ : PontryaginDual (SIdeleQuotient ℚ ∅)) (z : ℂ) :=
    (sLocalZetaPair χ (Submodule.Quotient.mk f)).2.val z
  have hconst (y : ℝ) : ev 1 ((1/4 : ℂ) + (y : ℂ) * Complex.I) = ev 1 (1/4) := by
    let x : ℝ := y/2
    obtain ⟨ψ,hψ⟩ := exists_positiveRealCharacter x
    let χ : PontryaginDual (SIdeleQuotient ℚ ∅) := ψ.comp ⟨m, (isProperMap_sIdeleQuotientNorm ℚ ∅).continuous⟩
    have hval (g : SIdeleQuotient ℚ ∅) : (χ g : ℂ) =
        ((((m g).val : ℝ) : ℂ) ^ ((x : ℂ) * Complex.I)) :=
      (congrArg (fun z : Circle ↦ (z : ℂ)) (hψ (m g))).trans (coe_circleExp_mul_log x (m g))
    have hres : χ.comp (⟨m.ker.subtype, continuous_subtype_val⟩ : m.ker →ₜ* SIdeleQuotient ℚ ∅) = (1 : PontryaginDual m.ker) := by
      apply ContinuousMonoidHom.ext
      intro g
      change ψ (m g.val) = 1
      rw [g.property, map_one]
    let χ₀ : PontryaginDual (SIdeleQuotient ℚ ∅) :=
      (existsUnique_sLocalNormSectionCharacter τ hτ
        (χ.comp (⟨m.ker.subtype, continuous_subtype_val⟩ : m.ker →ₜ* SIdeleQuotient ℚ ∅))).exists.choose
    have hχ₀ : χ₀ = 1 := (existsUnique_sLocalNormSectionCharacter τ hτ _).unique
      (existsUnique_sLocalNormSectionCharacter τ hτ _).exists.choose_spec
      ⟨hres.symm, fun _ ↦ rfl⟩
    have hx (t : ℝ≥0ˣ) : (χ (τ t) : ℂ) = (((t.val : ℝ) : ℂ) ^ ((x : ℂ) * Complex.I)) :=
      (hval (τ t)).trans (congrArg (fun u : ℝ≥0ˣ ↦ (((u.val : ℝ) : ℂ) ^ ((x : ℂ) * Complex.I))) (hτ t))
    let s : ℂ := (1/4 : ℂ) + (x : ℂ) * Complex.I
    have hs : s.re < 1 := by norm_num [s]
    have hc : ev χ s = ev 1 (s + (x : ℂ) * Complex.I) := Printed.sLocalZetaPair_reflectedShift_false_coordinate χ x hval f s hs
    have he : ev χ s = ev χ₀ (s - (x : ℂ) * Complex.I) := h ℚ ∅ τ hτ χ x hx f hs
    have hplus : s + (x : ℂ) * Complex.I = (1/4 : ℂ) + (y : ℂ) * Complex.I := by dsimp [s,x]; push_cast; ring
    have hminus : s - (x : ℂ) * Complex.I = (1/4 : ℂ) := by dsimp [s]; ring
    exact (congrArg (ev 1) hplus).symm.trans (hc.symm.trans
      (he.trans ((congrArg (fun ψ ↦ ev ψ (s - (x : ℂ) * Complex.I)) hχ₀).trans (congrArg (ev 1) hminus))))
  have hz := Printed.sLocalZetaPair_reflectedShift_false_vertical (Iio (1 : ℝ))
    (sLocalZetaPair (1 : PontryaginDual (SIdeleQuotient ℚ ∅)) (Submodule.Quotient.mk f)).2
    (1/4) (by norm_num) (by simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using hconst)
  have he := existsUnique_sLocalZetaPair_equation (1 : PontryaginDual (SIdeleQuotient ℚ ∅)) f (1/4) (by norm_num)
  have hr := (sLocalZetaPair_mk (1 : PontryaginDual (SIdeleQuotient ℚ ∅)) f).2
    (show (1/4 : ℂ).re < 1 by norm_num)
  have hz' : ev 1 (1/4) = 0 := by simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using hz
  exact hf (he.trans ((congrArg (fun z : ℂ ↦ _ * z) (hr.symm.trans hz')).trans (mul_zero _)))

/-- Paper: Theorem 5.4.2.2(2), p. 276.
As printed: radial inversion with the factor `t⁻¹` and the norm-one coordinate fixed sends
every function of the conjugate isotype with weights in `1 − I` back into the same weighted
isotype. This records the source and membership assertion in the prose, which uses `1 − I`
at both ends. The displayed type uses `I` at both ends.
`existsUnique_sLocalCechRadialReflection` exchanges the two intervals. See ERRATA F62. -/
def Printed.sLocalCechRadialReflection : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (χ : PontryaginDual (SIdeleQuotient F S)) (τ : ℝ≥0ˣ →ₜ* SIdeleQuotient F S)
    (_hτ : RightInverse τ (sIdeleQuotientNorm F S)),
    let E := Eω(F, S, leftInterval, restrict₁(F, S, χ⁻¹))
    ∀ f : E, ∃ j : E,
      ∀ (t : ℝ≥0ˣ) (k : (sIdeleQuotientNorm F S).ker),
        j.val.val (τ t * k.val) = normℂ(t)⁻¹ * f.val.val (τ t⁻¹ * k.val)

/-- Exponential decay with a smooth cutoff on the left is a Schwartz bound. -/
private theorem sLocalCechRadialReflection_false_decay (δ : ℝ) (hδ : 0 < δ) (k n : ℕ) :
    ∃ C, ∀ x : ℝ, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n
      (fun x : ℝ ↦ ((Real.exp (-δ * x) * Real.smoothTransition x : ℝ) : ℂ)) x‖ ≤ C := by
  let h : ℝ → ℝ := fun x ↦ Real.exp (-δ * x) * Real.smoothTransition x
  have hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h :=
    (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).mul (Real.smoothTransition.contDiff (n := ⊤))
  let g : ℝ → ℂ := Complex.ofRealLI ∘ h
  have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g := Complex.ofRealLI.contDiff.comp hh
  have key (x : ℝ) : ‖iteratedFDeriv ℝ n g x‖ = |iteratedDeriv n h x| := by
    rw [LinearIsometry.norm_iteratedFDeriv_comp_left _ hh.contDiffAt (by exact_mod_cast le_top),
      norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (f := fun x : ℝ ↦ ‖x‖ ^ k * ‖iteratedFDeriv ℝ n g x‖)
    (((continuous_norm.pow k).mul (hg.continuous_iteratedFDeriv
      (by exact_mod_cast le_top)).norm).continuousOn)
  have hB : 0 ≤ δ ^ n * (k.factorial / δ ^ k) := by positivity
  refine ⟨max M (δ ^ n * (k.factorial / δ ^ k)), fun x ↦ ?_⟩
  change ‖x‖ ^ k * ‖iteratedFDeriv ℝ n g x‖ ≤ _
  rcases lt_or_ge x 0 with hx | hx
  · have he : h =ᶠ[nhds x] fun _ ↦ 0 := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      simp [h, Real.smoothTransition.zero_of_nonpos (le_of_lt hy)]
    rw [key, he.iteratedDeriv_eq]
    have h0 : iteratedDeriv n (fun _ : ℝ ↦ (0 : ℝ)) x = 0 := by simp
    rw [h0, abs_zero, mul_zero]
    exact le_max_of_le_right hB
  rcases le_or_gt x 1 with hx1 | hx1
  · have := hM x ⟨hx, hx1⟩
    rw [Real.norm_of_nonneg (by positivity)] at this
    exact this.trans (le_max_left _ _)
  · have he : h =ᶠ[nhds x] fun y ↦ Real.exp (-δ * y) := by
      filter_upwards [Ioi_mem_nhds hx1] with y hy
      simp [h, Real.smoothTransition.one_of_one_le (le_of_lt hy)]
    rw [key, he.iteratedDeriv_eq, iteratedDeriv_exp_const_mul, Real.norm_of_nonneg hx]
    refine le_trans ?_ (le_max_right _ _)
    have hpow := Real.pow_div_factorial_le_exp (δ * x) (by positivity) k
    have hf : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
    rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_pow, abs_neg, abs_of_pos hδ]
    have hexp : Real.exp (-δ * x) * Real.exp (δ * x) = 1 := by
      rw [← Real.exp_add]; simp
    have : x ^ k * Real.exp (-δ * x) ≤ k.factorial / δ ^ k := by
      rw [le_div_iff₀ (by positivity)]
      rw [div_le_iff₀ hf, mul_pow] at hpow
      nlinarith [Real.exp_pos (-δ * x), pow_pos hδ k, pow_nonneg hx k]
    calc x ^ k * (δ ^ n * Real.exp (-δ * x)) = δ ^ n * (x ^ k * Real.exp (-δ * x)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left this (by positivity)

/-- The logarithmic profile of `t ↦ t⁻¹ ψ(log t)`, with `ψ` a smooth step from `0` to `1`,
decays after every exponential twist with exponent below one. -/
private theorem sLocalCechRadialReflection_false_profile :
    (fun x : ℝ ↦ ((Real.exp (-x) * Real.smoothTransition x : ℝ) : ℂ)) ∈
      logExponentialDecaySubmodule (Iio 1) := by
  refine (Submodule.mem_iInf _).2 fun a ↦ Submodule.mem_comap.2 ?_
  have hδ : 0 < 1 - (a : ℝ) := sub_pos.2 a.2
  have hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ ↦ Real.exp (-(1 - (a : ℝ)) * x) * Real.smoothTransition x) :=
    (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).mul (Real.smoothTransition.contDiff (n := ⊤))
  let s : SchwartzMap ℝ ℂ :=
    ⟨fun x : ℝ ↦ ((Real.exp (-(1 - (a : ℝ)) * x) * Real.smoothTransition x : ℝ) : ℂ),
      Complex.ofRealCLM.contDiff.comp hh, sLocalCechRadialReflection_false_decay _ hδ⟩
  refine ⟨s, funext fun x ↦ ?_⟩
  change ((Real.exp (-(1 - (a : ℝ)) * x) * Real.smoothTransition x : ℝ) : ℂ) =
    (Real.exp ((a : ℝ) * x) : ℂ) * ((Real.exp (-x) * Real.smoothTransition x : ℝ) : ℂ)
  rw [← Complex.ofReal_mul, ← mul_assoc, ← Real.exp_add]
  congr 3
  ring

/-- Functions in the Schwartz–Bruhat submodule are bounded. -/
private theorem sLocalCechRadialReflection_false_bounded {G : Type*} [CommGroup G]
    [TopologicalSpace G] {f : G → ℂ} (hf : f ∈ schwartzBruhatSubmodule G) :
    ∃ d : ℝ, ∀ x, ‖f x‖ ≤ d := by
  let B : Submodule ℂ (G → ℂ) :=
    { carrier := {f | ∃ d : ℝ, ∀ x, ‖f x‖ ≤ d}
      add_mem' := by
        rintro f g ⟨a, ha⟩ ⟨b, hb⟩
        exact ⟨a + b, fun x ↦ (norm_add_le _ _).trans (add_le_add (ha x) (hb x))⟩
      zero_mem' := ⟨0, fun x ↦ by simp⟩
      smul_mem' := by
        rintro c f ⟨a, ha⟩
        refine ⟨‖c‖ * a, fun x ↦ ?_⟩
        rw [Pi.smul_apply, smul_eq_mul, norm_mul]
        exact mul_le_mul_of_nonneg_left (ha x) (norm_nonneg c) }
  have hle : schwartzBruhatSubmodule G ≤ B := by
    unfold schwartzBruhatSubmodule
    refine iSup_le fun a ↦ iSup_le fun e ↦ ?_
    rintro _ ⟨s, rfl⟩
    refine ⟨elementarySchwartzSeminorm (0, 0, 0, 0) s, fun x ↦ ?_⟩
    rw [schwartzBruhatStageRealization_apply]
    split_ifs
    · change (‖s _‖₊ : ENNReal).toReal ≤ (elementarySchwartzBound s.val (0, 0, 0, 0)).toReal
      apply ENNReal.toReal_mono (s.property.2 _).ne
      rw [elementarySchwartzBound_zero]
      exact le_iSup (fun y ↦ (‖s y‖₊ : ENNReal)) _
    · exact norm_zero.trans_le (apply_nonneg _ _)
  exact hle hf

/-- The constant function one is a Schwartz–Bruhat function on a compact group
(as `compact_schwartzBruhat_one` in `AppD_SchwartzBruhat/Sec2b.lean`). -/
private theorem sLocalCechRadialReflection_false_one {H : Type*} [CommGroup H]
    [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] [LocallyCompactSpace H]
    [CompactSpace H] : ∃ c : SchwartzBruhat H, ∀ k, c k = 1 := by
  have hcompact : IsCompact ((⊤ : Subgroup H) : Set H) := isCompact_univ
  have : CompactSpace (⊤ : Subgroup H) := isCompact_iff_compactSpace.mp hcompact
  have : CompactSpace (lcaAnnihilator (⊤ : Subgroup H)) :=
    isCompact_iff_compactSpace.mp (isCompact_lcaAnnihilator ⊤ isOpen_univ)
  let a : BruhatStructuralPair H :=
    ⟨(⊤, OrderDual.toDual ⊤), isOpen_univ,
      isCompactlyGeneratedGroup_of_compact (G := (⊤ : Subgroup H)),
      ⟨isClosed_univ, isOpen_lcaAnnihilator ⊤ hcompact,
        isCompactlyGeneratedGroup_of_compact (G := lcaAnnihilator (⊤ : Subgroup H))⟩, le_rfl⟩
  have : Subsingleton a.quotient := by
    change Subsingleton ((⊤ : Subgroup H) ⧸ (⊤ : Subgroup (⊤ : Subgroup H)))
    exact QuotientGroup.subsingleton_quotient_top
  let A := Multiplicative (ElementaryLieGroup 0 0 0 PUnit)
  have : Subsingleton A := by
    change Subsingleton (ElementaryLieGroup 0 0 0 PUnit)
    infer_instance
  let f : a.quotient →* A := 1
  let e₀ : a.quotient ≃* A := MulEquiv.ofBijective f
    ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun y ↦ ⟨1, Subsingleton.elim _ y⟩⟩
  let e : ElementaryLCAPresentation a.quotient :=
    { realDim := 0
      torusDim := 0
      latticeRank := 0
      finiteFactor := PUnit
      equiv := { e₀ with
        continuous_toFun := (continuous_const (y := (1 : A))).congr fun _ ↦ Subsingleton.elim _ _
        continuous_invFun := (continuous_const (y := (1 : a.quotient))).congr
          fun _ ↦ Subsingleton.elim _ _ } }
  let s : SchwartzBruhatStage e := ⟨fun _ ↦ 1, by
    refine ⟨fun _ _ ↦ contDiff_const, ?_⟩
    intro idx
    have hi : idx = (0, 0, 0, 0) := Subsingleton.elim _ _
    subst idx
    simp [elementarySchwartzBound_zero]⟩
  refine ⟨schwartzBruhatStageInclusion a e s, fun k ↦ ?_⟩
  rw [schwartzBruhatStageInclusion_apply, schwartzBruhatStageRealization_apply,
    dite_eq_left (show k ∈ a.val.1 from Subgroup.mem_top k)]

/-- A radial function with profile `t ↦ t⁻¹ ψ(log t)` lies in the decay space with
exponents below one, by the tensor splitting of Theorem D.3.3.7(1). -/
private theorem sLocalCechRadialReflection_false_radial {G : Type*} [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    [SecondCountableTopology G] (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m)
    (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ m) :
    ∃ f : ModulatedExponentialDecay m (Iio 1), ∀ g : G,
      f.val g = ((Real.exp (-Real.log ((m g).val : ℝ)) *
        Real.smoothTransition (Real.log ((m g).val : ℝ)) : ℝ) : ℂ) := by
  have hK : IsCompact (m.toMonoidHom.ker : Set G) :=
    hm.1.isCompact_preimage (isCompact_singleton (x := (1 : ℝ≥0ˣ)))
  have : CompactSpace m.toMonoidHom.ker := isCompact_iff_compactSpace.mp hK
  obtain ⟨c, hc⟩ := sLocalCechRadialReflection_false_one (H := m.toMonoidHom.ker)
  obtain ⟨e, he⟩ := modulatedExponentialDecay_tensor_equiv m (Iio 1) hm ordConnected_Iio
    ⟨0, by norm_num⟩ τ hτ
  let p : PositiveRealExponentialDecay (Iio 1) := ⟨_, sLocalCechRadialReflection_false_profile⟩
  refine ⟨e (UniformSpace.Completion.coe'
    (α := InductiveTensor (SchwartzBruhat m.toMonoidHom.ker) (PositiveRealExponentialDecay (Iio 1)))
    (c ⊗ₜ[ℂ] p)), fun g ↦ ?_⟩
  have hu : g * (τ (m g))⁻¹ ∈ m.toMonoidHom.ker := by
    rw [MonoidHom.mem_ker]
    change m (g * (τ (m g))⁻¹) = 1
    rw [map_mul, map_inv, hτ (m g), mul_inv_cancel]
  have hg : ((⟨g * (τ (m g))⁻¹, hu⟩ : m.toMonoidHom.ker) : G) * τ (m g) = g := inv_mul_cancel_right _ _
  have h1 := he c p ⟨g * (τ (m g))⁻¹, hu⟩ (m g)
  rw [hg, hc, one_mul] at h1
  exact h1

/-- A function in the decay space with exponents below one cannot equal `ψ(−log t)`
along a section: its twist by `t⁻¹` would be unbounded. -/
private theorem sLocalCechRadialReflection_false_unbounded {G : Type*} [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] (m : G →ₜ* ℝ≥0ˣ) (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ m)
    (j : ModulatedExponentialDecay m (Iio 1))
    (hj : ∀ t : ℝ≥0ˣ, j.val (τ t) = (Real.smoothTransition (-Real.log (t.val : ℝ)) : ℂ)) :
    False := by
  obtain ⟨d, hd⟩ := sLocalCechRadialReflection_false_bounded
    (modulationWeight_mem_schwartzBruhat m (Iio 1) ⟨-1, by norm_num⟩ j)
  let x₀ : ℝ := |d| + 1
  let t : ℝ≥0ˣ := Units.mk0 ⟨Real.exp (-x₀), (Real.exp_pos _).le⟩
    (ne_of_gt (show (0 : ℝ≥0) < ⟨Real.exp (-x₀), (Real.exp_pos _).le⟩ from Real.exp_pos _))
  have ht : ((t.val : ℝ≥0) : ℝ) = Real.exp (-x₀) := rfl
  have h1 := hd (τ t)
  change ‖((((m (τ t)).val : ℝ) ^ ((-1 : ℝ)) : ℝ) : ℂ) * j.val (τ t)‖ ≤ d at h1
  rw [hτ t, hj t, ht, Real.log_exp, neg_neg,
    Real.smoothTransition.one_of_one_le (by simp [x₀, abs_nonneg] : (1 : ℝ) ≤ x₀),
    Complex.ofReal_one, mul_one, Complex.norm_real, Real.norm_of_nonneg (by positivity),
    Real.rpow_neg_one, ← Real.exp_neg, neg_neg] at h1
  have h2 := Real.add_one_le_exp x₀
  have h3 := le_abs_self d
  simp only [x₀] at h1 h2
  linarith

/-- Paper: Theorem 5.4.2.2(2), p. 276.
Take `F = ℚ`, `S` consisting of the real place, the positive-real section, and `χ = 1`.
Use `f(t) = exp(−1/t) / t`. For every `a < 1`, the twist `t^a f(t)` is Schwartz in
`log t`, since the power at infinity is `a−1 < 0` and the exponential dominates at zero.
The radial image is `exp(−t)`. Its weight-zero twist tends to `1` as `t` tends to zero,
and hence is outside the target with weights `a < 1`.
-/
theorem Printed.sLocalCechRadialReflection_false : ¬ Printed.sLocalCechRadialReflection := by
  intro h
  let S : Finset (HeightOneSpectrum (𝓞 ℚ)) := ∅
  obtain ⟨τ, hτ⟩ := sIdeleQuotientNorm_exists_section ℚ S
  have : LocallyCompactSpace (SAdeleRing ℚ S)ˣ := (sIdeleGroup_description ℚ S).2.2.1
  have : T2Space (SIdeleQuotient ℚ S) :=
    have := isClosed_sProjectedDiagonal (F := ℚ) (S := S)
    inferInstance
  have : ∀ w : InfinitePlace ℚ, SecondCountableTopology w.Completion := fun w ↦
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  have : ∀ v : S, SecondCountableTopology (v.val.adicCompletion ℚ) := fun v ↦
    (Finset.notMem_empty _ v.2).elim
  have : SecondCountableTopology (SAdeleRing ℚ S) :=
    inferInstanceAs (SecondCountableTopology
      (((w : InfinitePlace ℚ) → w.Completion) × ((v : S) → v.val.adicCompletion ℚ)))
  have : SecondCountableTopology (SAdeleRing ℚ S)ˣ :=
    (sIdeleGroup_description ℚ S).1.secondCountableTopology
  have : SecondCountableTopology (SIdeleQuotient ℚ S) := inferInstance
  let m : SIdeleQuotient ℚ S →ₜ* ℝ≥0ˣ :=
    ⟨sIdeleQuotientNorm ℚ S, (isProperMap_sIdeleQuotientNorm ℚ S).continuous⟩
  have hτm : RightInverse τ m := fun t ↦ hτ t
  have hm : IsModulation m := by
    refine ⟨isProperMap_sIdeleQuotientNorm ℚ S, τ (Units.mk0 2 (by norm_num)), ?_⟩
    change sIdeleQuotientNorm ℚ S (τ _) ≠ 1
    rw [hτ]
    intro h2
    have := congrArg (fun t : ℝ≥0ˣ ↦ (t.val : ℝ)) h2
    norm_num at this
  obtain ⟨f₀, hf₀⟩ := sLocalCechRadialReflection_false_radial m hm τ hτm
  obtain ⟨j, hj⟩ := h ℚ S 1 τ hτ ⟨f₀, by
    refine (mem_sLocalDecayIsotype (F := ℚ) (S := S) (Iio 1) _ f₀).mpr ?_
    intro u g
    have hmu : m (u.val⁻¹ * g) = m g := by
      change sIdeleQuotientNorm ℚ S (u.val⁻¹ * g) = sIdeleQuotientNorm ℚ S g
      rw [map_mul, map_inv, MonoidHom.mem_ker.mp u.property, inv_one, one_mul]
    rw [hf₀, hf₀, hmu]
    symm
    convert one_mul _ using 2
    rw [inv_one]
    exact Circle.coe_one⟩
  refine sLocalCechRadialReflection_false_unbounded m τ hτm j.val fun t ↦ ?_
  have h1 := hj t 1
  have ht : ((t.val : ℝ≥0) : ℝ) ≠ 0 := (NNReal.coe_pos.mpr (Units.zero_lt t)).ne'
  change j.val.val (τ t * 1) = _ * f₀.val (τ t⁻¹ * 1) at h1
  rw [mul_one, mul_one, hf₀] at h1
  change j.val.val (τ t) = _ * (((Real.exp (-Real.log ((m (τ t⁻¹)).val : ℝ)) *
    Real.smoothTransition (Real.log ((m (τ t⁻¹)).val : ℝ)) : ℝ) : ℂ)) at h1
  rw [hτm t⁻¹, Units.val_inv_eq_inv_val, NNReal.coe_inv, Real.log_inv, neg_neg,
    Real.exp_log (NNReal.coe_pos.mpr (Units.zero_lt t))] at h1
  change j.val.val (τ t) = _
  rw [h1, Complex.ofReal_mul, ← mul_assoc, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr ht), one_mul]

/-- Paper: Theorem 5.4.2.2(3), p. 276.
As printed: reflection followed by multiplication by the local correcting factor gives
a linear topological isomorphism from the right half-plane Schwartz–Bergman space to the
reflected half-plane Schwartz–Bergman space. `sLocalCechBergman_exact` uses the product on the
overlap where it is holomorphic. See ERRATA F63. -/
def Printed.sLocalCechBergman_reflection : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (χ : PontryaginDual (SIdeleQuotient F S)),
    ∃ J : B⁺ ≃L[ℂ] B⁻, ∀ p : B⁺,
      EqOn (J p).val (fun s ↦ ρₛ(F, S, χ, s) * p.val (1 - s)) leftHalf

private theorem Printed.sLocalCechBergman_reflection_false_pole :
    ∃ s₀ : ℂ, s₀.re < 1 ∧ meromorphicOrderAt
      (fun z ↦ ρₛ(ℚ, (∅ : Finset (HeightOneSpectrum (𝓞 ℚ))),
        (1 : PontryaginDual (SIdeleQuotient ℚ ∅)), z)) s₀ < 0 := by
  obtain ⟨w, hw⟩ : ∃ w : InfinitePlace ℚ, w.IsReal := by
    classical
    have hcard := InfinitePlace.nrRealPlaces_eq_one_of_finrank_eq_one (K := ℚ)
      (Module.finrank_self ℚ)
    obtain ⟨⟨w, hw⟩⟩ := Fintype.card_pos_iff.mp (lt_of_lt_of_eq one_pos hcard.symm)
    exact ⟨w, hw⟩
  let χ₀ := (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp
    (1 : PontryaginDual (SIdeleQuotient ℚ ∅))
  let c := quasiCharacterNormTwist (sIdeleQuotientNorm ℚ ∅)
    (isProperMap_sIdeleQuotientNorm ℚ ∅).continuous χ₀ 0
  let p := (realLocalEulerParameters w hw (sLocalInfiniteRestriction w c)).exists.choose
  obtain ⟨n, hn⟩ := exists_nat_gt (-p.1.re)
  refine ⟨-p.1 - ((2 * n + p.2.val : ℕ) : ℂ), ?_, ?_⟩
  · have h2 : (0 : ℝ) ≤ (p.2.val : ℝ) := Nat.cast_nonneg _
    rw [Complex.sub_re, Complex.neg_re, Complex.natCast_re]
    push_cast
    linarith
  · exact (sLocalRhoFactor_poles_iff (F := ℚ) (S := ∅) 1 _).2 (Or.inl ⟨w, hw, n, rfl⟩)

open scoped Topology in
/-- Paper: Theorem 5.4.2.2(3), p. 276.
Take `F = ℚ`, `S` consisting of the real place, and `χ = 1`. Use `p(s) = exp(s²)` on
the right half-plane. The factor `π^((1−2s)/2) Γ(s/2) / Γ((1−s)/2)` has a simple pole
at zero, where `p(1) = e`. The product is unbounded as `s` approaches zero through
positive real arguments, so no holomorphic output exists on the reflected half-plane.
-/
theorem Printed.sLocalCechBergman_reflection_false : ¬ Printed.sLocalCechBergman_reflection := by
  intro h
  obtain ⟨s₀, hs₀, hpole⟩ := Printed.sLocalCechBergman_reflection_false_pole
  obtain ⟨J, hJ⟩ := h ℚ ∅ 1
  let p : B⁺ := ⟨(Complex.re ⁻¹' rightInterval).indicator (fun z : ℂ ↦ Complex.exp (z ^ 2)),
    gaussian_mem_schwartzBergmanSubmodule _ isOpen_Ioi⟩
  have hopen : IsOpen leftHalf := isOpen_Iio.preimage Complex.continuous_re
  have hmem : s₀ ∈ leftHalf := hs₀
  have hd : DifferentiableOn ℂ (J p).val leftHalf := (J p).2.2.1
  have han : AnalyticAt ℂ (fun z ↦ (J p).val z / Complex.exp ((1 - z) ^ 2)) s₀ :=
    ((hd.analyticAt (hopen.mem_nhds hmem)).div (by fun_prop) (Complex.exp_ne_zero _))
  have heq : (fun z ↦ ρₛ(ℚ, (∅ : Finset (HeightOneSpectrum (𝓞 ℚ))),
      (1 : PontryaginDual (SIdeleQuotient ℚ ∅)), z)) =ᶠ[𝓝[≠] s₀]
      (fun z ↦ (J p).val z / Complex.exp ((1 - z) ^ 2)) := by
    refine Filter.Eventually.filter_mono nhdsWithin_le_nhds ?_
    filter_upwards [hopen.mem_nhds hmem] with z hz
    have hz' : (1 - z) ∈ Complex.re ⁻¹' rightInterval := by
      change 0 < (1 - z).re
      have : z.re < 1 := hz
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    have hv : p.val (1 - z) = Complex.exp ((1 - z) ^ 2) :=
      indicator_of_mem hz' (fun z : ℂ ↦ Complex.exp (z ^ 2))
    have hJz := hJ p hz
    simp only at hJz
    rw [hJz, hv, mul_div_cancel_right₀ _ (Complex.exp_ne_zero _)]
  rw [meromorphicOrderAt_congr heq] at hpole
  exact absurd han.meromorphicOrderAt_nonneg (not_le.mpr hpole)

local notation "mellinAt(" τ ", " f ", " z ")" =>
  (∫ t : ℝ≥0ˣ, (f) ((τ) t) * normℂ(t) ^ (z) ∂positiveRealHaar)

/-- Paper: Theorem 5.4.2.2(4)–(5), (5.4.2.6), p. 276.
As printed: the right square commutes on every input of the two upper weighted isotypes.
On the overlap, the top-then-right path has second term `ρ(s) Q(s)` by the conjugation of
the multiplier by Mellin in (4). The down-then-right path has second term `ρ(s) Q(1−s)`
by (3). Here `Q` denotes the second Mellin transform. We read “similarly” in (1) as using
the printed shift for both transforms and express the two paths after Mellin evaluation,
with the first projection as in (5) on p. 277. See `existsUnique_sLocalCechDifference`
for the repaired difference and ERRATA F64.
-/
def Printed.sLocalCech_right_commutes : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (χ : PontryaginDual (SIdeleQuotient F S)) (τ : ℝ≥0ˣ →ₜ* SIdeleQuotient F S)
    (_hτ : RightInverse τ (sIdeleQuotientNorm F S)) (x : ℝ),
    (∀ t : ℝ≥0ˣ, (χ (τ t) : ℂ) = normℂ(t) ^ ((x : ℂ) * Complex.I)) →
    ∀ (M₁ : Eω(F, S, rightInterval, restrict₁(F, S, χ)) ≃L[ℂ] B⁺)
      (M₂ : Eω(F, S, rightInterval, restrict₁(F, S, χ⁻¹)) ≃L[ℂ] B⁺),
      (∀ f s, s ∈ rightHalf → (M₁ f).val s = mellinAt(τ, f.val.val, s + (x : ℂ) * Complex.I)) →
      (∀ f s, s ∈ rightHalf → (M₂ f).val s = mellinAt(τ, f.val.val, s + (x : ℂ) * Complex.I)) →
      ∀ f g, EqOn
        (fun s ↦ (M₁ f).val s - ρₛ(F, S, χ, s) * (M₂ g).val s)
        (fun s ↦ (M₁ f).val s - ρₛ(F, S, χ, s) * (M₂ g).val (1 - s)) overlap

open scoped Topology in
private theorem Printed.sLocalCech_right_commutes_false_ne_zero :
    ∃ r : ℝ, 0 < r ∧ r < 1 / 2 ∧
      ρₛ(ℚ, (∅ : Finset (HeightOneSpectrum (𝓞 ℚ))),
        (1 : PontryaginDual (SIdeleQuotient ℚ ∅)), (r : ℂ)) ≠ 0 := by
  obtain ⟨s₀, -, hpole⟩ := Printed.sLocalCechBergman_reflection_false_pole
  have hmero : Meromorphic (fun z ↦ ρₛ(ℚ, (∅ : Finset (HeightOneSpectrum (𝓞 ℚ))),
      (1 : PontryaginDual (SIdeleQuotient ℚ ∅)), z)) :=
    sLocalRhoFactor_meromorphic (F := ℚ) (S := ∅) 1
  have hon : MeromorphicOn (fun z ↦ ρₛ(ℚ, (∅ : Finset (HeightOneSpectrum (𝓞 ℚ))),
      (1 : PontryaginDual (SIdeleQuotient ℚ ∅)), z)) univ := fun z _ ↦ hmero z
  have htop := hon.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (mem_univ s₀) (mem_univ (((1 / 4 : ℝ)) : ℂ)) (ne_top_of_lt hpole)
  have hev := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hmero _)).1 htop
  have ht : Filter.Tendsto (fun r : ℝ ↦ (r : ℂ)) (𝓝[≠] (1 / 4 : ℝ))
      (𝓝[≠] (((1 / 4 : ℝ)) : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact fun h ↦ hr (Complex.ofReal_injective h)
  have hI : ∀ᶠ r in 𝓝[≠] (1 / 4 : ℝ), r ∈ Ioo (0 : ℝ) (1 / 2) :=
    nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num) (by norm_num))
  obtain ⟨r, hr1, hr2⟩ := ((ht.eventually hev).and hI).exists
  exact ⟨r, hr2.1, hr2.2, hr1⟩

private theorem Printed.sLocalCech_right_commutes_false_cancel (a b c d : ℂ) (hb : b ≠ 0)
    (h : a - b * c = a - b * d) : c = d :=
  mul_left_cancel₀ hb (sub_right_injective h)

private theorem Printed.sLocalCech_right_commutes_false_gaussian (r : ℝ) (hr0 : 0 < r)
    (hr1 : r < 1 / 2)
    (h : (Complex.re ⁻¹' Ioi (0 : ℝ)).indicator (fun z : ℂ ↦ Complex.exp (z ^ 2)) (r : ℂ) =
      (Complex.re ⁻¹' Ioi (0 : ℝ)).indicator (fun z : ℂ ↦ Complex.exp (z ^ 2)) (1 - (r : ℂ))) :
    False := by
  have h1 : (r : ℂ) ∈ Complex.re ⁻¹' Ioi (0 : ℝ) := by
    change 0 < (r : ℂ).re
    rw [Complex.ofReal_re]
    exact hr0
  have h2 : (1 - (r : ℂ)) ∈ Complex.re ⁻¹' Ioi (0 : ℝ) := by
    change 0 < (1 - (r : ℂ)).re
    rw [Complex.sub_re, Complex.one_re, Complex.ofReal_re]
    linarith
  rw [indicator_of_mem h1, indicator_of_mem h2] at h
  have h3 : Real.exp (r ^ 2) = Real.exp ((1 - r) ^ 2) := by
    exact_mod_cast h
  have := Real.exp_injective h3
  nlinarith

private theorem Printed.sLocalCech_right_commutes_false_transport {X : Type*} (v : X → ℂ → ℂ)
    {x y : X} (e : x = y) {a b : ℂ} (h : v x a = v x b) : v y a = v y b :=
  e ▸ h

/-- Paper: Theorem 5.4.2.2(4)–(5), (5.4.2.6), p. 276.
Take `F = ℚ`, `S` consisting of the real place, the positive-real section, and `χ = 1`,
so both Mellin transforms have shift zero. Set the first input to zero and the second
to the inverse Mellin image of `Q(s) = exp((s−2)²)` on the right half-plane.
At `s = 1/4`, `Q(1/4)` and `Q(3/4)` differ and `ρ(1/4) ≠ 0`. Both arguments are in
the overlap and the two paths give different values there.
-/
theorem Printed.sLocalCech_right_commutes_false : ¬ Printed.sLocalCech_right_commutes := by
  intro h
  obtain ⟨r, hr0, hr1, hρ⟩ := Printed.sLocalCech_right_commutes_false_ne_zero
  obtain ⟨τ, hτ⟩ := sIdeleQuotientNorm_exists_section (F := ℚ) (S := ∅)
  obtain ⟨M₁, hM₁, -⟩ := existsUnique_sLocalDecayMellin (F := ℚ) (S := ∅) τ hτ rightInterval
    isOpen_Ioi ordConnected_Ioi nonempty_Ioi
    (restrict₁(ℚ, ∅, (1 : PontryaginDual (SIdeleQuotient ℚ ∅)))) 0
  obtain ⟨M₂, hM₂, -⟩ := existsUnique_sLocalDecayMellin (F := ℚ) (S := ∅) τ hτ rightInterval
    isOpen_Ioi ordConnected_Ioi nonempty_Ioi
    (restrict₁(ℚ, ∅, (1 : PontryaginDual (SIdeleQuotient ℚ ∅))⁻¹)) 0
  let q : B⁺ := ⟨(Complex.re ⁻¹' rightInterval).indicator (fun z : ℂ ↦ Complex.exp (z ^ 2)),
    gaussian_mem_schwartzBergmanSubmodule _ isOpen_Ioi⟩
  have hmem : (r : ℂ) ∈ overlap := by
    change (r : ℂ).re ∈ Ioo (0 : ℝ) 1
    rw [Complex.ofReal_re]
    exact ⟨hr0, by linarith⟩
  have hx : ∀ t : ℝ≥0ˣ, ((1 : PontryaginDual (SIdeleQuotient ℚ ∅)) (τ t) : ℂ) =
      normℂ(t) ^ (((0 : ℝ) : ℂ) * Complex.I) := fun t ↦ by simp
  have h₁ : ∀ f s, s ∈ rightHalf →
      (M₁ f).val s = mellinAt(τ, f.val.val, s + ((0 : ℝ) : ℂ) * Complex.I) :=
    fun f s hs ↦ (hM₁ f s hs).2
  have h₂ : ∀ f s, s ∈ rightHalf →
      (M₂ f).val s = mellinAt(τ, f.val.val, s + ((0 : ℝ) : ℂ) * Complex.I) :=
    fun f s hs ↦ (hM₂ f s hs).2
  have key := h ℚ ∅ 1 τ hτ 0 hx M₁ M₂ h₁ h₂ (M₁.symm q) (M₂.symm q) hmem
  have key₁ := Printed.sLocalCech_right_commutes_false_cancel _ _ _ _ hρ key
  have e : M₂ (M₂.symm q) = q := M₂.apply_symm_apply q
  have key₂ : q.val (r : ℂ) = q.val (1 - (r : ℂ)) :=
    Printed.sLocalCech_right_commutes_false_transport (fun x : B⁺ ↦ x.val) e key₁
  exact Printed.sLocalCech_right_commutes_false_gaussian r hr0 hr1 key₂

end RiemannMasullo
