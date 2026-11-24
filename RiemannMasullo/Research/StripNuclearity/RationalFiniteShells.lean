module

public import RiemannMasullo.Research.StripNuclearity.RationalPrimeFreeDiagonal
public import RiemannMasullo.External.AlgebraicNumberTheoryLean.Chebotarev.DirichletHeckeRat
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! # The actual finite-place values of positive radial tests

On a shell of norm larger than one, the ultrametric denominator is exactly
the norm of the shell. Multiplicative Haar measure gives each such shell the
mass of the integer units. These facts recover the prime-power contribution
to the rational explicit formula with its exact local normalization.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped ContDiff NNReal NumberField.AdeleRing Topology
namespace RiemannMasullo.StripNuclearity

set_option quotPrecheck false
section FiniteShells

variable {F : Type*} [Field F] [NumberField F]
local notation "Pl" => HeightOneSpectrum (𝓞 F)
local notation "K(" v ")" => ((v : Pl).adicCompletion F)
local notation "q(" v ")" => ((v : Pl).asIdeal.absNorm : ℝ)
local notation "O(" v ")" => (((v : Pl).adicCompletionIntegers F).units : Set K(v)ˣ)
local instance shellLocalCompact (v : Pl) : LocallyCompactSpace K(v)ˣ :=
  letI : ProperSpace K(v) := properSpace_adicCompletion v
  inferInstance
local instance shellMeasurable (v : Pl) : MeasurableSpace K(v)ˣ := borel _
local instance shellBorel (v : Pl) : BorelSpace K(v)ˣ := ⟨rfl⟩
local notation "μ(" v ")" => finiteLocalMultiplicativeTamagawaMeasure F v
local notation "V(" v ")" => ((μ(v) O(v)).toReal)
local notation "scale(" v ")" => ((Real.log q(v) / V(v) : ℝ) : ℂ)
local notation "shell(" v ", " k ")" => {u : K(v)ˣ | ‖u.val‖ = q(v) ^ ((k : ℕ)+1)}

/-- Every positive power of the residue norm describes a translate of the
integer units, so each multiplicative shell has the same Tamagawa mass. -/
private theorem norm_shell_measure (v : Pl) (k : ℕ) : μ(v) (shell(v, k)) = μ(v) O(v) := by
  let : μ(v).IsHaarMeasure := finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure v
  let val : Valuation K(v) (WithZero (Multiplicative ℤ)) := Valued.v
  obtain ⟨π, hπ⟩ := val.exists_isUniformizer_of_isCyclic_of_nontrivial
  let p : K(v)ˣ := Units.mk0 (π : K(v)) hπ.ne_zero
  have hp : ‖p.val‖ = q(v)⁻¹ := norm_uniformizer_adicCompletion v _ hπ
  have hq : 0 < q(v) := by exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm v).pos
  have heq : shell(v, k) = ((p^(k + 1)) * ·) ⁻¹' O(v) := by
    ext u
    change ‖u.val‖ = q(v) ^ (k + 1) ↔ p^(k + 1) * u ∈ (v.adicCompletionIntegers F).units
    rw [HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one,
      ← Valued.toNormedField.norm_eq_one_iff, Units.val_mul, Units.val_pow_eq_pow_val, norm_mul, norm_pow,
      hp, inv_pow]
    exact eq_comm.trans (inv_mul_eq_one₀ (pow_ne_zero _ hq.ne')).symm
  rw [heq, measure_preimage_mul]

private theorem integer_unit_mass_pos (v : Pl) : 0 < V(v) := by
  let : μ(v).IsHaarMeasure := finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure v
  have ho : IsOpen O(v) := Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)
  have hk : IsCompact O(v) := Submonoid.units_isCompact
    (isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v))
  exact ENNReal.toReal_pos (ho.measure_pos μ(v) ⟨1,(v.adicCompletionIntegers F).units.one_mem⟩).ne' hk.measure_lt_top.ne

/-- Paper: Lemma B.4.4.3, p. 620, and §1.4.1, p. 28. For a radial test
supported at positive log norm, each shell of exponent k+1 contributes
exactly log(q) times the unshifted profile at log(q^(k + 1)) to the normalized
local principal value. This shell calculation applies over every number field. -/
theorem hasSum_finite_principalValue_positive_radial (v : Pl) (g : ℝ → ℂ)
    (hv : ∀ t ≤ 0, g t = 0) (f : BruhatCompactSupport K(v)ˣ)
    (hf : ∀ u, f.val u = rationalCenteredLogProfile g (Real.log ‖u.val‖)) :
    HasSum (fun k : ℕ ↦ (Real.log q(v) : ℂ) * g (Real.log (q(v) ^ (k + 1))))
      (scale(v) * finiteConnesWeilPrincipalValue v 1 f) := by
  classical
  let H (u : K(v)ˣ) := f.val u * (Real.sqrt ‖u.val‖ : ℂ) / (‖1 - u.val‖ : ℂ)
  have hq : 1 < q(v) := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have h1 : f.val 1 = 0 := by simp [hf, rationalCenteredLogProfile, hv 0 (le_refl _)]
  have hP := finiteConnesWeilPrincipalValue_of_apply_one_zero v f h1
  have hmem (u : K(v)ˣ) (hu : 1 < ‖u.val‖) : u ∈ ⋃ k : ℕ, shell(v, k) := by
    have hz : ‖u.val‖ = q(v) ^ (WithZero.log (Valued.v u.val)) := by
      rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ (Valued.v.ne_zero_iff.mpr u.ne_zero)]
      simp
    have hk := (one_lt_zpow_iff_right₀ hq).mp (hu.trans_eq hz)
    obtain ⟨k,hk'⟩ : ∃ k : ℕ, (WithZero.log (Valued.v u.val)) = (k : ℤ)+1 :=
      ⟨(WithZero.log (Valued.v u.val)-1).toNat, by omega⟩
    apply mem_iUnion.mpr ⟨k,?_⟩
    change ‖u.val‖ = _
    simpa only [hk', ← Nat.cast_one (R := ℤ), ← Nat.cast_add, zpow_natCast] using hz
  have hm (k : ℕ) : MeasurableSet (shell(v, k)) :=
    (isClosed_eq (continuous_norm.comp Units.continuous_val) continuous_const).measurableSet
  have hd : Pairwise (Disjoint on fun k : ℕ ↦ shell(v, k)) := by
    intro i j hij
    refine disjoint_left.mpr fun u hi hj ↦ hij ?_
    have h : q(v) ^ (i+1) = q(v) ^ (j+1) := hi.symm.trans hj
    exact Nat.add_right_cancel ((pow_right_strictMono₀ hq).injective h)
  have hz (u : K(v)ˣ) (hu : u ∉ ⋃ k : ℕ, shell(v, k)) : H u = 0 := by
    have hn : ‖u.val‖ ≤ 1 := not_lt.mp (hu ∘ hmem u)
    simp only [H, hf,rationalCenteredLogProfile,hv _ (Real.log_nonpos (norm_nonneg _) hn),mul_zero,
      zero_mul,zero_div]
  have hSum := hasSum_integral_iUnion (f := H) (μ := μ(v)) hm hd hP.1.integrableOn
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hz] at hSum
  have hlocal {u : K(v)ˣ} (hu : 1 < ‖u.val‖) : H u = g (Real.log ‖u.val‖) := by
    have hnorm : ‖1 - u.val‖ = ‖u.val‖ := by
      have h := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
        (x := (1 : K(v))) (y := -u.val) (by rw [norm_one,norm_neg]; exact hu.ne)
      simpa only [sub_eq_add_neg,norm_one,norm_neg,max_eq_right hu.le] using h
    have hpos := norm_pos_iff.mpr u.ne_zero
    have hex : Complex.exp ((Real.log ‖u.val‖ : ℂ) / 2) = (Real.sqrt ‖u.val‖ : ℂ) := by
      rw [show ((Real.log ‖u.val‖ : ℂ) / 2) = ((Real.log ‖u.val‖ / 2 : ℝ) : ℂ) by push_cast; rfl,
        ← Complex.ofReal_exp, Real.exp_half, Real.exp_log hpos]
    have hsq : (Real.sqrt ‖u.val‖ : ℂ) * (Real.sqrt ‖u.val‖ : ℂ) = (‖u.val‖ : ℂ) := by
      exact_mod_cast Real.mul_self_sqrt hpos.le
    simp only [H, hf, rationalCenteredLogProfile, hex, hnorm]
    rw [mul_right_comm, hsq, mul_div_cancel_left₀]
    exact_mod_cast hpos.ne'
  rw [hP.2]
  apply (hSum.mul_left (scale(v))).congr_fun
  intro k
  have hvv : (V(v) : ℂ) ≠ 0 := by exact_mod_cast (integer_unit_mass_pos v).ne'
  rw [setIntegral_congr_fun (hm k) (g := fun _ ↦ g (Real.log (q(v) ^ (k + 1)))) fun u hu ↦
    (hlocal (hu ▸ one_lt_pow₀ hq (Nat.succ_ne_zero _))).trans (congrArg (g ∘ Real.log) hu),
    setIntegral_const,Measure.real_def,norm_shell_measure,Complex.real_smul, Complex.ofReal_div]
  field_simp
end FiniteShells


section RationalPlaces

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 shellLocalCompact shellMeasurable shellBorel

local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "N(" x ")" => (((ideleClassNorm ℚ) (x : Cℚ)).val : ℝ)
local notation "wℝ" => Rat.infinitePlace
local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation "U∞" => ((w : InfinitePlace ℚ) → BruhatCompactSupport w.Completionˣ)
local notation "U𝔭" => ((v : V) → BruhatCompactSupport (v.adicCompletion ℚ)ˣ)
local notation "infClass(" w ")" => IdeleClassGroup.ofCompletion (𝓞 ℚ) ℚ w
local notation "finClass(" v ")" => IdeleClassGroup.ofAdicCompletion (𝓞 ℚ) ℚ v
local notation "finTerm(" v ", " B ")" =>
  ((Real.log ((v : V).asIdeal.absNorm : ℝ) / ((finiteLocalMultiplicativeTamagawaMeasure ℚ v)
    ((HeightOneSpectrum.adicCompletionIntegers ℚ v).units : Set _)).toReal : ℝ) : ℂ) *
    finiteConnesWeilPrincipalValue v 1 B
local notation "radial(" φ ", " g ")" =>
  (∀ x : Cℚ, (φ : BruhatCompactSupport Cℚ).val x = rationalCenteredLogProfile g (Real.log N(x)))
local notation "archRep(" A ", " φ ")" =>
  (∀ (w : InfinitePlace ℚ) (u : w.Completionˣ), ((A : U∞) w).val u = (φ : BruhatCompactSupport Cℚ).val (infClass(w) u))
local notation "finRep(" B ", " φ ")" =>
  (∀ (v : V) (u : (v.adicCompletion ℚ)ˣ), ((B : U𝔭) v).val u = (φ : BruhatCompactSupport Cℚ).val (finClass(v) u))
local notation "places(" A ", " B ")" =>
  ((∑ w : InfinitePlace ℚ, infiniteConnesWeilPrincipalValue w ((A : U∞) w)) + ∑' v : V, finTerm(v,(B : U𝔭) v))

local notation "P(" g ", " n ")" => (ArithmeticFunction.vonMangoldt (n : ℕ) : ℂ) *
  ((g : ℝ → ℂ) (Real.log n) + g (-Real.log n) / (n : ℂ))

/-- For positive-log rational radial profiles the sum of the actual finite
local distributions is the ordinary von Mangoldt sum. -/
theorem hasSum_rational_positive_log_finite_principalValues
    (g : ℝ → ℂ) (hg : ContDiff ℝ (∞) g) (hc : HasCompactSupport g) (hv : ∀ t ≤ 0, g t = 0)
    (φ : BruhatCompactSupport Cℚ) (hφ : radial(φ, g)) (B : U𝔭) (hB : finRep(B, φ)) :
    HasSum (fun v : V ↦ finTerm(v, B v)) (∑' n : ℕ, P(g, n)) := by
  let P (n : ℕ) := P(g, n)
  let e : V × ℕ ≃ {n : ℕ // IsPrimePow n} :=
    ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).prodCongr (Equiv.refl ℕ)).trans Nat.Primes.prodNatEquiv
  let ι (v : V × ℕ) := (e v).val
  have hi : Injective ι := Subtype.val_injective.comp e.injective
  have outside (n : ℕ) (hn : n ∉ range ι) : P n = 0 := by
    have h : ¬ IsPrimePow n := fun hp ↦ hn ⟨e.symm ⟨n,hp⟩, congrArg Subtype.val (e.apply_symm_apply _)⟩
    simp only [P, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr h, Complex.ofReal_zero, zero_mul]
  have htotal := (External.Grh.completedZeta_explicit_formula hg hc).2.1.of_norm.hasSum
  have hR : HasSum (fun i ↦ P (ι i)) (∑' n, P n) := (hi.hasSum_iff outside).mpr htotal
  apply hR.prod_fiberwise
  intro v
  have hB' (u : (v.adicCompletion ℚ)ˣ) : (B v).val u = rationalCenteredLogProfile g (Real.log ‖u.val‖) := by
    rw [hB, hφ, ideleClassNorm_ofAdicCompletion]
    rfl
  apply (hasSum_finite_principalValue_positive_radial v g hv (B v) hB').congr_fun
  intro k
  let p := (Rat.HeightOneSpectrum.primesEquiv v).val
  have hp : p.Prime := (Rat.HeightOneSpectrum.primesEquiv v).property
  have hr : v.asIdeal.absNorm = p := NumberFieldKB.Chebotarev.RatIdele.absNorm_asIdeal v
  change (ArithmeticFunction.vonMangoldt (p ^ (k + 1)) : ℂ) *
    (g (Real.log ((p ^ (k + 1) : ℕ) : ℝ)) + g (-Real.log ((p ^ (k + 1) : ℕ) : ℝ)) / _) = _
  rw [ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero k), ArithmeticFunction.vonMangoldt_apply_prime hp,
    hv _ (neg_nonpos.mpr (Real.log_natCast_nonneg _)),zero_div, add_zero,hr,Nat.cast_pow]

/-- All radial compact Bruhat tests on the rational idèle classes admit
compact Bruhat restrictions to the actual groups of units at every place. -/
theorem exists_rational_radial_place_tests (g : ℝ → ℂ) (hg : ContDiff ℝ (∞) g)
    (hc : HasCompactSupport g) (φ : BruhatCompactSupport Cℚ) (hφ : radial(φ, g)) :
    ∃ (A : U∞) (B : U𝔭), archRep(A, φ) ∧ finRep(B, φ) := by
  let G := rationalCenteredLogProfile g
  have hG : ContDiff ℝ (∞) G :=
    (Complex.contDiff_exp.comp ((Complex.ofRealCLM.contDiff).div_const 2)).mul hg
  have hGc : HasCompactSupport G := hc.mul_left
  obtain ⟨u, hu⟩ := exists_rational_archimedean_norm_test G hG hGc
  have hr (w : InfinitePlace ℚ) : ∃ u : BruhatCompactSupport w.Completionˣ, ∀ x, u.val x = φ.val (infClass(w) x) := by
    obtain rfl := Subsingleton.elim w wℝ
    refine ⟨u, fun x ↦ ?_⟩
    rw [hu, hφ, ideleClassNorm_ofCompletion, Rat.isReal_infinitePlace.mult_eq_one, pow_one]
    rfl
  have hf (v : V) : ∃ u : BruhatCompactSupport (v.adicCompletion ℚ)ˣ, ∀ x, u.val x = φ.val (finClass(v) x) := by
    let : ProperSpace (v.adicCompletion ℚ) := properSpace_adicCompletion v
    obtain ⟨u,hu⟩ := exists_normedField_logNorm_test (K := v.adicCompletion ℚ) G hG hGc
    refine ⟨u, fun x ↦ ?_⟩
    rw [hu, hφ, ideleClassNorm_ofAdicCompletion]
    rfl
  choose A hA using hr
  choose B hB using hf
  exact ⟨A, B, hA, hB⟩

/-- The classical prime-power and real gamma expressions coincide with the
actual normalized idelic place values on every compactly supported smooth
rational radial profile with positive log support. -/
theorem rationalWeilLocalValue_eq_positive_log_principalValues (g : ℝ → ℂ)
    (hg : ContDiff ℝ (∞) g) (hc : HasCompactSupport g) {a b : ℝ} (ha : 0 < a)
    (hs : tsupport g ⊆ Icc a b) (φ : BruhatCompactSupport Cℚ) (hφ : radial(φ, g))
    (A : U∞) (B : U𝔭) (hA : archRep(A, φ)) (hB : finRep(B, φ)) :
    rationalWeilLocalValue g = places(A, B) := by
  have hv (t : ℝ) (ht : t ≤ 0) : g t = 0 :=
    image_eq_zero_of_notMem_tsupport fun h ↦ (not_le.mpr (ht.trans_lt ha)) (hs h).1
  have hreal (x : Rat.infinitePlace.Completionˣ) : (A wℝ).val x = rationalCenteredLogProfile g (Real.log ‖x.val‖) := by
    rw [hA, hφ, ideleClassNorm_ofCompletion, Rat.isReal_infinitePlace.mult_eq_one, pow_one]
    rfl
  rw [rationalWeilLocalValue,
    (hasSum_rational_positive_log_finite_principalValues g hg hc hv φ hφ B hB).tsum_eq,
    Fintype.sum_subsingleton _ wℝ,rational_real_principalValue_positive_log_profile g hg.continuous ha hs _ hreal,
    add_comm]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
  simp only [hv _ (neg_nonpos.mpr (le_of_lt hx)),mul_zero,add_zero]

local notation "Vℚ" => (((normOneIdeleClassTamagawaMeasure ℚ) univ).toReal : ℂ)
local notation "μℚ" => ideleClassTamagawaMeasure ℚ
local notation "mℚ" => (⟨ideleClassNorm ℚ, (isProperMap_ideleClassNorm ℚ).continuous⟩ : Cℚ →ₜ* ℝ≥0ˣ)
local notation "pole(" φ ", " b ")" =>
  modulatedFourierMellin mℚ univ
    (⟨isProperMap_ideleClassNorm ℚ, ideleClassNorm_ne_one (F := ℚ)⟩ : IsModulation mℚ)
    μℚ (φ : BruhatCompactSupport Cℚ).val (ideleClassNormTwist (F := ℚ) 1 b)

open RiemannMasullo.External.Grh in
/-- On a positive-log window the numerical pole corrections are the two
global Mellin moments of the original test under Tamagawa Haar measure. -/
theorem rational_positive_log_places_sub_global_poles (g : ℝ → ℂ) (hg : ContDiff ℝ (∞) g) (hc : HasCompactSupport g)
    {a b : ℝ} (ha : 0 < a) (hs : tsupport g ⊆ Icc a b)
    (φ : BruhatCompactSupport Cℚ) (hφ : radial(φ, g)) (A : U∞) (B : U𝔭)
    (hA : archRep(A, φ)) (hB : finRep(B, φ)) :
    Vℚ * (rationalWeilLocalValue g - compactLogMellin g 0 - compactLogMellin g 1) =
      Vℚ * places(A, B) - pole(φ, -(1/2)) - pole(φ, 1/2) := by
  have hm : pole(φ,-(1/2)) = Vℚ * compactLogMellin g 0 := by
    simpa only [zero_sub] using rationalCenteredNormTest_mellin g φ hφ 0
  have hp : pole(φ,1/2) = Vℚ * compactLogMellin g 1 := by
    simpa only [show (1 : ℂ) - 1/2 = 1/2 by norm_num] using rationalCenteredNormTest_mellin g φ hφ 1
  rw [rationalWeilLocalValue_eq_positive_log_principalValues g hg hc ha hs φ hφ A B hA hB, hm, hp]
  ring

local notation "compareActual(" g ", " hg ", " hc ", " ha ", " hsupp ", " φ ", " hφ ", " A ", " B ", " hA ", " hB ", " hw ", " hs ", " U ", " hU ", " hm ")" =>
  (integral_rational_wide_diagonal_eq_weilLocal_sub_poles g hg hc
    (image_eq_zero_of_notMem_tsupport fun ht ↦ (not_le.mpr ha) ((hsupp) ht).1)
    φ hφ hw hs U hU hm).2.trans
    (rational_positive_log_places_sub_global_poles g hg hc ha hsupp φ hφ A B hA hB)

/-- Paper: Equations (12.5.1.2)–(12.5.1.4), pp. 519–520. For rational
radial tests of norm in any compact subinterval of (1,∞), the actual smoothened
wide geometric diagonal is the Tamagawa norm-one volume times the sum of the
normalized local principal values, minus the two global polar Mellin moments.
The half-width may be exactly one half and the Sobolev order at least three.
Deviation: The calculation uses the independent classical zeta contour formula.
It requires no passage from an S-local cutoff trace. -/
theorem integral_rational_positive_log_diagonal_eq_principalValues_sub_poles
    (g : ℝ → ℂ) (hg : ContDiff ℝ (∞) g) (hc : HasCompactSupport g)
    {a b : ℝ} (ha : 0 < a) (hsupp : tsupport g ⊆ Icc a b)
    (φ : BruhatCompactSupport Cℚ) (hφ : radial(φ, g)) (A : U∞) (B : U𝔭)
    (hA : archRep(A, φ)) (hB : finRep(B, φ))
    {α s : ℝ} (hw : 1/2 ≤ α) (hs : 3 ≤ s) (U : ℕ → Set Cℚ)
    (hU : IsDPrimeSequence μℚ U) (hm : ∀ n, MeasurableSet (U n)) :
    type_of% compareActual(g, hg, hc, ha, hsupp, φ, hφ, A, B, hA, hB, hw, hs, U, hU, hm) :=
  compareActual(g, hg, hc, ha, hsupp, φ, hφ, A, B, hA, hB, hw, hs, U, hU, hm)

local notation "twoPlace" => (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨2, Nat.prime_two⟩

/-- On any log window strictly inside (0,log 3), the only possible finite
local contribution is the first shell at 2. Its coefficient is exactly
log(2) times the unshifted profile at log(2). -/
theorem rational_finite_principalValues_prime_two (g : ℝ → ℂ) {a b : ℝ} (ha : 0 < a)
    (hb : b < Real.log 3) (hs : tsupport g ⊆ Icc a b) (φ : BruhatCompactSupport Cℚ)
    (hφ : radial(φ, g)) (B : U𝔭) (hB : finRep(B, φ)) :
    finTerm(twoPlace, B twoPlace) = (Real.log 2 : ℂ) * g (Real.log 2) ∧
      ∀ v : V, v ≠ twoPlace → finTerm(v, B v) = 0 := by
  let e : V ≃ Nat.Primes := Rat.HeightOneSpectrum.primesEquiv
  let v₂ : V := twoPlace
  have h₂ : v₂.asIdeal.absNorm = 2 :=
    (NumberFieldKB.Chebotarev.RatIdele.absNorm_asIdeal v₂).trans
      (congrArg Subtype.val (e.apply_symm_apply ⟨2,Nat.prime_two⟩))
  have hup {r : ℝ} (hr : 3 ≤ r) : g (Real.log r) = 0 :=
    image_eq_zero_of_notMem_tsupport fun ht ↦
      (not_le.mpr (hb.trans_le (Real.log_le_log (by norm_num) hr))) (hs ht).2
  have hv (t : ℝ) (ht : t ≤ 0) : g t = 0 :=
    image_eq_zero_of_notMem_tsupport fun h ↦ (not_le.mpr (ht.trans_lt ha)) (hs h).1
  have hS (v : V) := hasSum_finite_principalValue_positive_radial v g hv (B v) (fun u ↦ by
    rw [hB, hφ, ideleClassNorm_ofAdicCompletion]
    rfl)
  constructor
  · change finTerm(v₂, B v₂) = _
    rw [← (hS v₂).tsum_eq, h₂, Nat.cast_ofNat]
    rw [tsum_eq_single 0 (fun k hk ↦ ?_)]
    · simp only [zero_add, pow_one]
    · apply mul_eq_zero_of_right
      apply hup
      calc (3 : ℝ) ≤ 2 ^ 2 := by norm_num
           _ ≤ 2 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  · intro v hv₂
    have hprime : v.asIdeal.absNorm = (e v).val := NumberFieldKB.Chebotarev.RatIdele.absNorm_asIdeal v
    have hn : (e v).val ≠ 2 := fun h ↦ hv₂ (e.symm_apply_eq.mpr (Subtype.ext h.symm)).symm
    have hnat : 3 ≤ (e v).val := by have := (e v).property.two_le; omega
    have hq : (3 : ℝ) ≤ (v.asIdeal.absNorm : ℝ) := by rw [hprime]; exact_mod_cast hnat
    rw [← (hS v).tsum_eq]
    refine (tsum_congr fun k ↦ mul_eq_zero_of_right _ (hup ?_)).trans tsum_zero
    apply hq.trans
    simpa only [pow_one] using (pow_le_pow_right₀ (a := (v.asIdeal.absNorm : ℝ))
      (by linarith) (show 1 ≤ k+1 by omega))

/-- There are compact smooth log profiles of value one at log(2) inside
every prescribed neighborhood of that point. -/
theorem exists_rational_prime_two_log_pulse {a b : ℝ}
    (ha : a < Real.log 2) (hb : Real.log 2 < b) :
    ∃ g : ℝ → ℂ, ContDiff ℝ (∞) g ∧ HasCompactSupport g ∧
      tsupport g ⊆ Icc a b ∧ g (Real.log 2) = 1 := by
  obtain ⟨f,hs,hc,hd,_,hx⟩ := exists_contDiff_tsupport_subset (n := ⊤)
    (Ioo_mem_nhds ha hb)
  refine ⟨fun t ↦ (f t : ℂ), Complex.ofRealCLM.contDiff.comp hd,
    hc.comp_left Complex.ofReal_zero, ?_, by simp [hx]⟩
  apply (show tsupport (fun t ↦ (f t : ℂ)) ⊆ tsupport f from closure_mono fun t ht ↦
    fun h ↦ ht (by simp [h]))
    |>.trans (hs.trans Ioo_subset_Icc_self)

/-- Every positive-log window around log(2) whose upper edge precedes log(3)
contains an actual rational idelic test with normalized local contribution
log(2) at 2 and zero at every other finite place. -/
theorem exists_rational_pulse_with_prime_two_principalValue {a b : ℝ}
    (ha : 0 < a) (hl : a < Real.log 2) (hr : Real.log 2 < b) (hb : b < Real.log 3) :
    ∃ (g : ℝ → ℂ) (φ : BruhatCompactSupport Cℚ) (A : U∞) (B : U𝔭),
      ContDiff ℝ (∞) g ∧ HasCompactSupport g ∧ tsupport g ⊆ Icc a b ∧ g (Real.log 2) = 1 ∧
      radial(φ, g) ∧ archRep(A, φ) ∧ finRep(B, φ) ∧
      finTerm(twoPlace, B twoPlace) = (Real.log 2 : ℂ) ∧
      ∀ v : V, v ≠ twoPlace → finTerm(v, B v) = 0 := by
  obtain ⟨g, hg, hc, hs, hg₂⟩ := exists_rational_prime_two_log_pulse hl hr
  obtain ⟨φ, hφ⟩ := exists_rationalCenteredNormTest g hg hc
  obtain ⟨A, B, hA, hB⟩ := exists_rational_radial_place_tests g hg hc φ hφ
  obtain ⟨h₂, hout⟩ := rational_finite_principalValues_prime_two g ha hb hs φ hφ B hB
  exact ⟨g, φ, A, B, hg, hc, hs, hg₂, hφ, hA, hB, by simpa only [hg₂,mul_one] using h₂, hout⟩

end RationalPlaces
end RiemannMasullo.StripNuclearity
