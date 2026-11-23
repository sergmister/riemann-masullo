module

public import RiemannMasullo.Ch03_IdelicZeta.Sec2
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Analysis.SpecificLimits.Basic
import all RiemannMasullo.Ch02_AdelicTheta.Sec2b
import all RiemannMasullo.Ch03_IdelicZeta.Sec2
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic

/-! # Chapter 3.2: printed residues and absolute convergence -/

@[expose] public noncomputable section

namespace RiemannMasullo

open Filter MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing Topology

local notation "𝕀[" F "]" => IdeleGroup (𝓞 F) F
local notation "C[" F "]" => IdeleClassGroup (𝓞 F) F
local notation "ℬ[" F "]" => SchwartzBruhat (Multiplicative 𝔸[F])

local instance printedCh03Sec2ResiduesIdeleMeasurableSpace
    (F : Type) [Field F] [NumberField F] : MeasurableSpace 𝕀[F] := borel _

local instance printedCh03Sec2ResiduesClassMeasurableSpace
    (F : Type) [Field F] [NumberField F] : MeasurableSpace C[F] := borel _

/-- Paper: Proposition 3.2.1.3(2), p. 123. As printed: for every number field and
every character χ trivial on the norm-one classes, write χ = |·|^(-it).
The residues of the Hecke L-function at it and 1 + it are minus the norm-one
class volume and that volume divided by the square root of the absolute norm
of the different, respectively. This is the residue clause of
`completedHeckeL_continuation_simplePoles`. See ERRATA F209. -/
def Printed.completedHeckeL_residues : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C[F]),
    χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1 →
    ∀ (L : ℂ → ℂ), MeromorphicNFOn L univ →
      (∀ s : Complex.re ⁻¹' Ioi (1 : ℝ), L s = completedHeckeL χ s) →
      ∀ (t : ℝ),
        ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : PontryaginDual C[F])
          (-Complex.I * (t : ℂ)) →
        let z := Complex.I * (t : ℂ)
        let m : ℝ := (normOneIdeleClassTamagawaMeasure F univ).toReal
        let d : ℝ := (differentIdeal ℤ (𝓞 F)).absNorm
        Tendsto (fun s : ℂ ↦ (s - z) * L s) (𝓝[≠] z) (𝓝 (-(m : ℂ))) ∧
          Tendsto (fun s : ℂ ↦ (s - (1 + z)) * L s) (𝓝[≠] (1 + z))
            (𝓝 ((d ^ (-(1 / 2) : ℝ) * m : ℝ) : ℂ))

/-- Proposition 3.2.1.3(2), p. 123. For F = ℚ(i), χ = 1 and t = 0, the residue
at 1 of the completed L-function is m / (2π). The printed value is m / 2, with
m the norm-one class volume and ‖N(𝔡)‖ = 4. See ERRATA F209. -/
theorem Printed.completedHeckeL_residues_false :
    ¬ Printed.completedHeckeL_residues := by
  intro h
  let F := CyclotomicField 4 ℚ
  have : NeZero (4 : ℕ) := ⟨by decide⟩
  have : IsCyclotomicExtension {4} ℚ F := by
    convert CyclotomicField.isCyclotomicExtension 4 ℚ
    exact Subsingleton.elim _ _
  have : NumberField F := IsCyclotomicExtension.numberField {4} ℚ F
  have hR : InfinitePlace.nrRealPlaces F = 0 :=
    IsCyclotomicExtension.Rat.nrRealPlaces_eq_zero (n := 4) F (by norm_num)
  have hC : InfinitePlace.nrComplexPlaces F = 1 := by
    rw [IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two (n := 4) F]
    decide
  have hdisc : (NumberField.discr F).natAbs = 4 := by
    rw [IsCyclotomicExtension.Rat.natAbs_discr (n := 4) (K := F)]
    have hfac : Nat.primeFactors 4 = {2} := by
      rw [show (4 : ℕ) = 2 ^ 2 by decide]
      exact Nat.primeFactors_prime_pow (by decide) Nat.prime_two
    rw [hfac, Finset.prod_singleton]
    have ht : Nat.totient 4 = 2 := by decide
    rw [ht]
    norm_num
  have hdnorm : ((differentIdeal ℤ (𝓞 F)).absNorm : ℝ) = 4 := by
    rw [NumberField.absNorm_differentIdeal (K := F), hdisc]
    norm_num
  have hpow : ((differentIdeal ℤ (𝓞 F)).absNorm : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / 2 := by
    rw [hdnorm, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4), ← Real.sqrt_eq_rpow]
    rw [show Real.sqrt (4 : ℝ) = 2 by
      rw [Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)]; norm_num]
    norm_num
  have hγ : heckeGammaFactor (1 : PontryaginDual C[F]) 1 = (1 / (2 * Real.pi) : ℂ) := by
    rw [heckeGammaFactor_one, hR, hC, pow_zero, one_mul, pow_one, Complex.Gammaℂ_one]
    ring
  have hmass : (normOneIdeleClassTamagawaMeasure F univ).toReal = dedekindZeta_residue F := by
    rw [normOneIdeleClassTamagawaMeasure_volume]
    suffices hform :
        (2 : ℝ) ^ InfinitePlace.nrRealPlaces F *
          (2 * Real.pi) ^ InfinitePlace.nrComplexPlaces F *
          (NumberField.classNumber F : ℝ) * Units.regulator F /
          (Real.sqrt ((NumberField.discr F).natAbs : ℝ) *
            (Units.torsionOrder F : ℝ)) =
          dedekindZeta_residue F by
      rw [hform, ENNReal.toReal_ofReal (dedekindZeta_residue_pos F).le]
    rw [dedekindZeta_residue_def, Nat.cast_natAbs, Int.cast_abs]
    ring
  obtain ⟨L, hL, hEq⟩ := completedHeckeL_exists_continuation (1 : PontryaginDual C[F])
  have hker : (1 : PontryaginDual C[F]).toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1 :=
    rfl
  have ht : ideleClassNormTwist (1 : PontryaginDual C[F]) 0 =
      ideleClassNormTwist (1 : PontryaginDual C[F]) (-Complex.I * ((0 : ℝ) : ℂ)) := by
    simp
  obtain ⟨-, hres⟩ := by
    simpa [Complex.ofReal_zero, mul_zero, add_zero] using
      h F (1 : PontryaginDual C[F]) hker L hL hEq 0 ht
  have hpow' : ((differentIdeal ℤ (𝓞 F)).absNorm : ℝ) ^ (-(2 : ℝ)⁻¹) = 1 / 2 := by
    rw [show (-(2 : ℝ)⁻¹) = -(1 / 2 : ℝ) by ring]
    exact hpow
  have hreal : Tendsto (fun r : ℝ ↦ (r : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa using (Complex.continuous_ofReal.continuousAt (x := (1 : ℝ))).tendsto.mono_left
        nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      simpa using (show 1 < r from hr).ne'
  have hlim : Tendsto (fun r : ℝ ↦ ((r : ℂ) - 1) * L (r : ℂ)) (𝓝[>] (1 : ℝ))
      (𝓝 (heckeGammaFactor (1 : PontryaginDual C[F]) 1 * (dedekindZeta_residue F : ℂ))) := by
    let γ := heckeGammaFactor (1 : PontryaginDual C[F])
    have hγdiff : DifferentiableAt ℂ γ 1 :=
      differentiableAt_heckeGammaFactor_of_re_pos _ (by norm_num)
    apply ((hγdiff.continuousAt.tendsto.comp (hreal.mono_right nhdsWithin_le_nhds)).mul
      (tendsto_sub_one_mul_dedekindZeta_nhdsGT F)).congr'
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr' : (r : ℂ) ∈ Complex.re ⁻¹' Ioi (1 : ℝ) := by simpa using hr
    have he := hEq ⟨(r : ℂ), hr'⟩
    rw [completedHeckeL_one_eq_dedekindZeta, ← heckeGammaFactor_one] at he
    dsimp [γ]
    rw [show L (r : ℂ) =
        heckeGammaFactor (1 : PontryaginDual C[F]) (r : ℂ) * dedekindZeta F (r : ℂ) from he]
    ring
  have heq := tendsto_nhds_unique hlim (hres.comp hreal)
  rw [hγ, hmass, hpow'] at heq
  have hm : (dedekindZeta_residue F : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (dedekindZeta_residue_ne_zero F)
  have hcoeff : (1 / (2 * Real.pi) : ℂ) = ↑((1 : ℝ) / 2) :=
    mul_right_cancel₀ hm heq
  have hrealπ : (1 : ℝ) / (2 * Real.pi) = 1 / 2 := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_ofNat]
    exact hcoeff
  rw [div_eq_div_iff (mul_ne_zero two_ne_zero Real.pi_ne_zero) two_ne_zero] at hrealπ
  linarith only [hrealπ, Real.pi_gt_three]

/-- Paper: Theorem 3.2.2.1(2)(b), p. 125. As printed: for every number field
and every adelic Schwartz–Bruhat function, the theta Mellin integral (3.2.2.3)
converges absolutely at every quasi-character on a nontrivial norm-one
component. This is the pointwise absolute convergence clause. See
`globalIdelicZFunction_entire_of_nontrivial` and ERRATA F210. -/
def Printed.globalThetaMellinIntegral_integrable_of_nontrivial : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (f : ℬ[F]) (χ : PontryaginDual C[F]),
    χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1 →
    ∀ s : ℂ, Integrable (fun g : C[F] ↦ adelicTheta f g * ideleClassNormTwist χ s g)
      (ideleClassTamagawaMeasure F)

/-- Reduction modulo `p` on the `p`-adic integers is continuous. -/
private theorem toZMod_continuous_aux (p : ℕ) [Fact p.Prime] :
    Continuous (PadicInt.toZMod : ℤ_[p] →+* ZMod p) := by
  apply continuous_of_continuousAt_zero (PadicInt.toZMod : ℤ_[p] →+* ZMod p)
  refine (tendsto_pure.mpr ?_).mono_right (pure_le_nhds _)
  filter_upwards [Metric.ball_mem_nhds (0 : ℤ_[p]) one_pos] with x hx
  rw [map_zero, ← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal,
    PadicInt.mem_nonunits]
  simpa using hx

/-- A character of `(ℤ/3)ˣ` that is nontrivial at `-1`. -/
private theorem exists_zmod3_char :
    ∃ ψ : (ZMod 3)ˣ →* Circle, ψ (-1) ≠ 1 := by
  have h : (Additive.ofMul (-1 : (ZMod 3)ˣ)) ≠ 0 := by decide
  obtain ⟨ψ, hψ⟩ := AddChar.exists_apply_ne_zero.mpr h
  refine ⟨(AddChar.circleEquivComplex.symm ψ).toMonoidHom, fun h1 ↦ hψ ?_⟩
  have h2 := congrArg (fun z : Circle ↦ (z : ℂ)) h1
  exact h2


open IsDedekindDomain in
/-- A unit of the local integers has norm one. -/
private theorem norm_unit_integers_aux (w : HeightOneSpectrum (𝓞 ℚ))
    (u : (w.adicCompletionIntegers ℚ)ˣ) : ‖((u.val : w.adicCompletionIntegers ℚ) :
      w.adicCompletion ℚ)‖ = 1 := by
  have hle : ∀ y : w.adicCompletionIntegers ℚ, ‖(y : w.adicCompletion ℚ)‖ ≤ 1 := fun y ↦
    Valued.toNormedField.norm_le_one_iff.mpr y.2
  have hmul : ‖((u.val : w.adicCompletionIntegers ℚ) : w.adicCompletion ℚ)‖ *
      ‖(((u⁻¹ : (w.adicCompletionIntegers ℚ)ˣ).val : w.adicCompletionIntegers ℚ) :
        w.adicCompletion ℚ)‖ = 1 := by
    rw [← norm_mul, ← Subring.coe_mul, Units.mul_inv]
    simp
  have h1 := hle u.val
  have h2 := hle (u⁻¹).val
  nlinarith [norm_nonneg ((u.val : w.adicCompletionIntegers ℚ) : w.adicCompletion ℚ),
    norm_nonneg (((u⁻¹ : (w.adicCompletionIntegers ℚ)ˣ).val : w.adicCompletionIntegers ℚ) :
        w.adicCompletion ℚ)]

open IsDedekindDomain in
/-- The idele classes of `ℚ` carry a character that is nontrivial on the norm-one classes:
the quadratic character of `(ℤ/3)ˣ` read off the unit at the place `3`. -/
private theorem exists_rat_char_nontrivial :
    ∃ χ : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ),
      χ.toMonoidHom.comp (ideleClassNorm ℚ).ker.subtype ≠ 1 := by
  classical
  let p : Nat.Primes := ⟨3, Nat.prime_three⟩
  let v : HeightOneSpectrum (𝓞 ℚ) := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p
  let E := (PadicInt.adicCompletionIntegersEquiv (𝓞 ℚ) p).symm
  let φ : v.adicCompletionIntegers ℚ →+* ZMod 3 :=
    (PadicInt.toZMod : ℤ_[p] →+* ZMod p).comp E.toRingEquiv.toRingHom
  have hφ : Continuous φ := (toZMod_continuous_aux p).comp E.continuous
  obtain ⟨ψ, hψ⟩ := exists_zmod3_char
  obtain ⟨e, he⟩ := ratIdeleClassGroup_decomposition
  let χl : (v.adicCompletionIntegers ℚ)ˣ →* Circle := ψ.comp (Units.map φ.toMonoidHom)
  have hχl : Continuous χl := (continuous_of_discreteTopology (f := (ψ : (ZMod 3)ˣ → Circle))).comp (hφ.units_map _)
  let χh : IdeleClassGroup (𝓞 ℚ) ℚ →* Circle :=
    χl.comp ((Pi.evalMonoidHom _ v).comp ((MonoidHom.snd _ _).comp e.symm.toMonoidHom))
  have hχh : Continuous χh :=
    hχl.comp ((continuous_apply v).comp (continuous_snd.comp e.symm.continuous))
  let χ : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ) := ⟨χh, hχh⟩
  refine ⟨χ, fun h ↦ ?_⟩
  obtain ⟨g, hginf, hgfin, hge⟩ := he 1 (Pi.mulSingle v (-1))
  have hker : e (1, Pi.mulSingle v (-1)) ∈ (ideleClassNorm ℚ).ker := by
    rw [MonoidHom.mem_ker, hge]
    apply Units.ext
    apply NNReal.coe_injective
    change ((ideleNorm ℚ g : ℝ≥0) : ℝ) = 1
    rw [((ideleNorm_spec ℚ).1 g).2]
    have hfin : (∏ᶠ w : HeightOneSpectrum (𝓞 ℚ), ‖g.val.2 w‖) = 1 := by
      apply finprod_eq_one_of_forall_eq_one
      intro w
      rw [hgfin w]
      exact norm_unit_integers_aux w _
    have hinf : ∀ w : InfinitePlace ℚ, ‖g.val.1 w‖ ^ w.mult = 1 := by
      intro w
      obtain rfl : w = Rat.infinitePlace := Subsingleton.elim _ _
      have hiso := (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
        Rat.isReal_infinitePlace).norm_map_of_map_zero (map_zero _) (g.val.1 Rat.infinitePlace)
      rw [← hiso, hginf]
      simp
    rw [hfin, mul_one]
    exact Finset.prod_eq_one fun w _ ↦ hinf w
  have h1 := DFunLike.congr_fun h ⟨_, hker⟩
  change χh (e (1, Pi.mulSingle v (-1))) = 1 at h1
  apply hψ
  have h2 : χh (e (1, Pi.mulSingle v (-1))) = ψ (Units.map φ.toMonoidHom (-1)) := by
    change χl ((e.symm (e (1, Pi.mulSingle v (-1)))).2 v) = _
    rw [e.symm_apply_apply]
    simp [χl]
  rw [← h1, h2]
  exact congrArg ψ (Units.ext (by simp)).symm

/-- At `s = 0` the theta Mellin integrand has norm at least one near norm zero, a set of
infinite class measure, once the Fourier transform of the test is nonzero at zero. -/
private theorem not_integrable_aux (F : Type) [Field F] [NumberField F] (f : ℬ[F])
    (χ : PontryaginDual C[F])
    (ha : adeleSchwartzFourier f (Multiplicative.ofAdd (0 : 𝔸[F])) ≠ 0) :
    ¬ Integrable (fun g : C[F] ↦ adelicTheta f g * ideleClassNormTwist χ 0 g)
      (ideleClassTamagawaMeasure F) := by
  intro hI
  let nr : C[F] → ℝ := fun g ↦ ((ideleClassNorm F g : ℝ≥0) : ℝ)
  have hnpos : ∀ g, 0 < nr g := fun g ↦
    NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero (ideleClassNorm F g)))
  obtain ⟨C, T, hC, hT, hsmall⟩ := adelicTheta_decay_small f 1
  set a := adeleSchwartzFourier f (Multiplicative.ofAdd (0 : 𝔸[F]))
  set b := f (Multiplicative.ofAdd (0 : 𝔸[F]))
  have ha' : 0 < ‖a‖ := norm_pos_iff.mpr ha
  set δ := min T (min 1 (‖a‖ / (‖b‖ + C + 1)))
  have hδ : 0 < δ := lt_min hT (lt_min one_pos (by positivity))
  -- the integrand has norm at least one at small norm
  have hlow : ∀ g : C[F], nr g < δ →
      1 ≤ ‖adelicTheta f g * ideleClassNormTwist χ 0 g‖ := by
    intro g hg
    have hn := hnpos g
    have hgT : nr g < T := lt_of_lt_of_le hg (min_le_left _ _)
    have hg1 : nr g < 1 := lt_of_lt_of_le hg ((min_le_right _ _).trans (min_le_left _ _))
    have hga : nr g < ‖a‖ / (‖b‖ + C + 1) :=
      lt_of_lt_of_le hg ((min_le_right _ _).trans (min_le_right _ _))
    have hb := hsmall g hgT
    have htw : ‖ideleClassNormTwist χ 0 g‖ = 1 := by
      change ‖(χ g : ℂ) * ((nr g : ℂ) ^ (0 : ℂ))‖ = 1
      simp
    rw [norm_mul, htw, mul_one]
    have hsa : ‖(nr g)⁻¹ • a‖ = ‖a‖ / nr g := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hn, inv_mul_eq_div]
    have htri : ‖(nr g)⁻¹ • a‖ ≤ ‖adelicTheta f g‖ + ‖b‖ + C * nr g ^ 1 := by
      have := norm_sub_le_norm_sub_add_norm_sub ((nr g)⁻¹ • a) (adelicTheta f g + b) 0
      have e1 : ‖(nr g)⁻¹ • a - (adelicTheta f g + b)‖ =
          ‖adelicTheta f g - (nr g)⁻¹ • a + b‖ := by
        rw [← norm_neg]; congr 1; abel
      calc ‖(nr g)⁻¹ • a‖ ≤ ‖adelicTheta f g - (nr g)⁻¹ • a + b‖ + ‖adelicTheta f g + b‖ := by
            have := norm_sub_norm_le ((nr g)⁻¹ • a) (adelicTheta f g + b)
            rw [e1] at this; linarith
        _ ≤ C * nr g ^ 1 + (‖adelicTheta f g‖ + ‖b‖) := add_le_add hb (norm_add_le _ _)
        _ = _ := by ring
    rw [hsa] at htri
    have hbig : ‖b‖ + C + 1 < ‖a‖ / nr g := by
      rw [lt_div_iff₀ hn]
      have := (lt_div_iff₀ (by positivity : (0:ℝ) < ‖b‖ + C + 1)).mp hga
      linarith
    nlinarith
  -- the set of small norm has infinite measure
  have hinf : ideleClassTamagawaMeasure F {g | nr g < δ} = ⊤ := by
    have hmap := classTamagawa_map_log_norm (F := F)
    let : BorelSpace C[F] := ⟨rfl⟩
    have hcont : Continuous (ideleClassNorm F) :=
      (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr (ideleGroup_topology F).2.2.2.2.1
    have hmeas : Measurable fun g : C[F] ↦ Real.log (nr g) :=
      Real.measurable_log.comp
        (NNReal.continuous_coe.comp (Units.continuous_val.comp hcont)).measurable
    have hset : {g | nr g < δ} = (fun g : C[F] ↦ Real.log (nr g)) ⁻¹' Iio (Real.log δ) := by
      ext g
      simp only [mem_preimage, mem_Iio]
      exact (Real.log_lt_log_iff (hnpos g) hδ).symm
    rw [hset, ← Measure.map_apply hmeas measurableSet_Iio, hmap]
    let : CompactSpace (ideleClassNorm F).ker := (ideleClassGroup_finiteness F).2.1
    let : (normOneIdeleClassTamagawaMeasure F).IsHaarMeasure :=
      (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
    have hk : (normOneIdeleClassTamagawaMeasure F univ).toNNReal ≠ 0 := by
      rw [Ne, ENNReal.toNNReal_eq_zero_iff, not_or]
      exact ⟨isOpen_univ.measure_ne_zero _ univ_nonempty,
        measure_ne_top _ _⟩
    rw [smul_apply, Real.volume_Iio, ENNReal.smul_def, smul_eq_mul,
      ENNReal.mul_top (ENNReal.coe_ne_zero.mpr hk)]
  have hfin := hI.measure_norm_ge_lt_top one_pos
  exact absurd (lt_of_le_of_lt (measure_mono fun g hg ↦ hlow g hg) hfin) (by rw [hinf]; exact lt_irrefl _)

/-- Paper: Theorem 3.2.2.1(2)(b), p. 125. Take F = ℚ, the standard Gaussian
at infinity, the indicator of ℤ̂ at the finite places, and χ induced by the
quadratic Dirichlet character of conductor 5. At s = 0 the character has modulus
one and takes the value −1 at the norm-one idele with component 2 at 5 and 1
elsewhere. At norm t, the theta sum is
Σ_{n ≠ 0} exp(−πn²t²) ∼ 1/t as t tends to zero, so its integral against dt/t diverges. -/
theorem Printed.globalThetaMellinIntegral_integrable_of_nontrivial_false :
    ¬ Printed.globalThetaMellinIntegral_integrable_of_nontrivial := by
  intro hP
  obtain ⟨χ, hχ⟩ := exists_rat_char_nontrivial
  obtain ⟨f, -, ha⟩ := exists_positive_polar_test (F := ℚ)
  exact not_integrable_aux ℚ f χ ha (hP ℚ f χ hχ 0)

/-- Paper: Remark 3.2.2.2, p. 125. As printed: the domain of each truncated
idele integral with norm in [1/n, n] is compact. This is the compactness
assertion used to justify holomorphy. See `globalIdelicZetaIntegral_normBand_entire`
and ERRATA F210. -/
def Printed.ideleNormBand_isCompact : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ), 1 ≤ n →
    IsCompact (ideleNormBand F (n : ℝ)⁻¹ (n : ℝ))

open IsDedekindDomain Rat in
/-- Paper: Remark 3.2.2.2, p. 125. For F = ℚ and n = 2, the norm band contains every
principal idele (2^k). The 2-adic norm at that place is a continuous map sending the
band into ℝ; it sends the principal ideles to ‖2‖^k with 0 < ‖2‖ < 1, which tends to 0.
A compact image would be closed and thus contain 0, but the norm of the component of a
unit is strictly positive. -/
theorem Printed.ideleNormBand_isCompact_false :
    ¬ Printed.ideleNormBand_isCompact := by
  intro hband
  obtain hD : IsCompact (ideleNormBand ℚ (2 : ℝ)⁻¹ 2) := hband (F := ℚ) (n := 2) (by norm_num)
  -- The place of ℚ above 2: its natural generator is 2.
  obtain ⟨v₂, hv₂gen⟩ : ∃ v : HeightOneSpectrum (𝓞 ℚ), HeightOneSpectrum.natGenerator v = 2 :=
    ⟨HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) |>.symm ⟨2, Nat.prime_two⟩, by
      exact congrArg Subtype.val
        ((HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply ⟨2, Nat.prime_two⟩)⟩
  obtain ⟨r, hrmem, hrint⟩ :
      ∃ r : 𝓞 ℚ, r ∈ v₂.asIdeal ∧ IsIntegralClosure.intEquiv (𝓞 ℚ) r = (2 : ℤ) := by
    have h2 : (2 : ℤ) ∈ v₂.asIdeal.map (IsIntegralClosure.intEquiv (𝓞 ℚ)) := by
      rw [← HeightOneSpectrum.span_natGenerator v₂, hv₂gen]
      exact Ideal.mem_span_singleton_self 2
    exact Ideal.mem_map_iff_of_surjective
      (IsIntegralClosure.intEquiv (𝓞 ℚ)).toRingHom (RingEquiv.surjective _) |>.mp h2
  have hrq : (r : ℚ) = 2 := by
    rw [show (r : ℚ) = algebraMap (𝓞 ℚ) ℚ r from rfl, ← Rat.ringOfIntegersEquiv_apply_coe,
      ← Rat.IsIntegralClosure.intEquiv_apply_eq_ringOfIntegersEquiv, hrint]
    rfl
  have hv2lt : v₂.valuation ℚ (r : ℚ) < 1 := by
    rw [show (r : ℚ) = algebraMap (𝓞 ℚ) ℚ r from rfl,
      HeightOneSpectrum.valuation_lt_one_iff_mem v₂ r]
    exact hrmem
  rw [hrq] at hv2lt
  -- The two coercion instances of ℚ into the completion agree with the embedding.
  have hbrM : ∀ x : ℚ, ((x : ℚ) : v₂.adicCompletion ℚ) =
      (FinitePlace.embedding v₂) x := by
    intro x
    simp
  -- The 2-adic norm at that place: continuous, positive on ideles, smaller than 1 on 2.
  have hval : Valued.v ((2 : ℚ) : v₂.adicCompletion ℚ) < 1 := by
    rw [hbrM 2]
    calc Valued.v ((FinitePlace.embedding v₂) (2 : ℚ)) = v₂.valuation ℚ 2 :=
          HeightOneSpectrum.adicCompletion.valued_coe (K := ℚ) (v := v₂) (2 : ℚ)
      _ < 1 := hv2lt
  have h2lt : ‖((2 : ℚ) : v₂.adicCompletion ℚ)‖ < 1 :=
    Valued.toNormedField.norm_lt_one_iff.mpr hval
  have h2pos : 0 < ‖((2 : ℚ) : v₂.adicCompletion ℚ)‖ := by
    rw [hbrM 2, FinitePlace.norm_embedding]
    exact (HeightOneSpectrum.adicAbv ℚ v₂).pos two_ne_zero
  set φ : IdeleGroup (𝓞 ℚ) ℚ → ℝ := fun g ↦ ‖(g.val.2 v₂ : v₂.adicCompletion ℚ)‖ with hφdef
  have hφcont : Continuous φ := by
    have h1 : Continuous fun x : AdeleRing (𝓞 ℚ) ℚ ↦ (x.2 v₂ : v₂.adicCompletion ℚ) :=
      (RestrictedProduct.continuous_eval v₂).comp continuous_snd
    exact (continuous_norm.comp h1).comp Units.continuous_val
  have himg : IsCompact (φ '' (ideleNormBand ℚ (2 : ℝ)⁻¹ 2)) := hD.image hφcont
  have hclosed : IsClosed (φ '' (ideleNormBand ℚ (2 : ℝ)⁻¹ 2)) := himg.isClosed
  -- The principal ideles (2^k) lie in the band, with φ-values ‖2‖^k tending to 0.
  have hvalk : ∀ k : ℕ,
      φ (IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ (Units.mk0 (2 : ℚ) two_ne_zero ^ k)) =
        ‖((2 : ℚ) : v₂.adicCompletion ℚ)‖ ^ k := by
    intro k
    have hcoe : ∀ y : ℚˣ,
        (IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ y).val.2 v₂ =
          (FinitePlace.embedding v₂) (y : ℚ) := by
      intro y
      have h1 : (IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ y).val.2 v₂ =
          ((algebraMap ℚ 𝔸[𝓞 ℚ, ℚ]) (y : ℚ)).2 v₂ := rfl
      rw [h1, AdeleRing.algebraMap_snd_apply (𝓞 ℚ) ℚ y.val v₂]
      exact (FinitePlace.embedding_apply v₂ (y : ℚ)).symm
    show ‖((IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ
        (Units.mk0 (2 : ℚ) two_ne_zero ^ k)).val.2 v₂ : v₂.adicCompletion ℚ)‖ =
      ‖((2 : ℚ) : v₂.adicCompletion ℚ)‖ ^ k
    rw [hcoe, Units.val_pow_eq_pow_val, Units.val_mk0, hbrM 2, map_pow, norm_pow]
  have hbandk : ∀ k : ℕ,
      IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ (Units.mk0 (2 : ℚ) two_ne_zero ^ k) ∈
        ideleNormBand ℚ (2 : ℝ)⁻¹ 2 := by
    intro k
    have h1 : ideleNorm ℚ (IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ
        (Units.mk0 (2 : ℚ) two_ne_zero ^ k)) = 1 :=
      MonoidHom.mem_ker.mp ((ideleNorm_spec ℚ).2 ⟨_, rfl⟩)
    rw [ideleNormBand, Set.mem_ofPred_eq, h1]
    exact mem_Icc.mpr ⟨by norm_num, by norm_num⟩
  have htendsto : Tendsto (fun k : ℕ ↦ ‖((2 : ℚ) : v₂.adicCompletion ℚ)‖ ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one h2pos.le h2lt
  have h0 : (0 : ℝ) ∈ φ '' (ideleNormBand ℚ (2 : ℝ)⁻¹ 2) :=
    hclosed.mem_of_tendsto htendsto
      (Filter.Eventually.of_forall fun k ↦ ⟨_, hbandk k, hvalk k⟩)
  obtain ⟨g, -, hgzero⟩ := h0
  obtain ⟨-, h2ne, -⟩ := AdeleRing.isUnit_iff.mp g.isUnit
  have hpos : 0 < φ g := norm_pos_iff.mpr (h2ne v₂)
  exact absurd hgzero (ne_of_lt hpos).symm

end RiemannMasullo
