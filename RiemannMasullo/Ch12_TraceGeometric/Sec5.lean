module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4
public import RiemannMasullo.Ch10_TraceSpectral.Sec4b
import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.AppB_AnalyticNT.Sec4b
import RiemannMasullo.Ch12_TraceGeometric.Sec1b
import RiemannMasullo.Ch10_TraceSpectral.Sec4a
import all RiemannMasullo.Ch02_AdelicTheta.Sec2b
import all RiemannMasullo.Ch03_IdelicZeta.Sec2
import all RiemannMasullo.Ch09_HardySobolev.Sec3
import RiemannMasullo.ForMathlib.Analysis.Complex.ExpSumUniqueness
import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-! # Trace formula: the Main Theorem

Masullo, §12.5, pp. 519–520. Zeros of the completed Hecke L-functions are listed
through a norm section, as in Theorem B.4.4.7: a quasi-character c = χ|·|^s with
χ trivial on the section has abscissa σ(c) = Re s.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 instFiniteCompletionUnitsLocallyCompactSec4b

variable {F : Type*} [Field F] [NumberField F]

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" =>
  (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "hm𝔽" => (⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ :
  IsModulation m𝔽)
local notation "M(" φ ", " c ")" =>
  modulatedFourierMellin m𝔽 univ hm𝔽 μ𝔽 (φ : BruhatCompactSupport C𝔽).val c
local notation "twist(" χ ", " s ")" => ideleClassNormTwist (F := F) χ s
local notation "ord(" χ ", " s ")" =>
  MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ s
local notation "interiorZeros(" τ ", " α ")" =>
  {z : {χ : PontryaginDual C𝔽 // ∀ t : ℝ≥0ˣ, χ (τ t) = 1} × ℂ //
    0 < ord(z.1.val, z.2) ∧ |z.2.re - 1 / 2| < α}
local notation "zeroTerm(" φ ", " z ")" =>
  ((ord((z).val.1.val, (z).val.2) : ℤ) : ℂ) * M(φ, twist((z).val.1.val, (z).val.2 - 1 / 2))
local notation "classVolume" => (((normOneIdeleClassTamagawaMeasure F) univ).toReal : ℂ)
local notation "archTest" => ((w : InfinitePlace F) → BruhatCompactSupport w.Completionˣ)
local notation "finiteTest" => ((v : V) → BruhatCompactSupport (v.adicCompletion F)ˣ)
local notation "archClass(" w ")" => IdeleClassGroup.ofCompletion (𝓞 F) F w
local notation "finiteClass(" v ")" => IdeleClassGroup.ofAdicCompletion (𝓞 F) F v
local notation "finiteVolume(" v ")" =>
  (finiteLocalMultiplicativeTamagawaMeasure F v
    ((HeightOneSpectrum.adicCompletionIntegers F v).units : Set _)).toReal
local notation "finiteTerm(" v ", " b ")" =>
  ((Real.log ((v : V).asIdeal.absNorm : ℝ) / finiteVolume(v) : ℝ) : ℂ) *
    finiteConnesWeilPrincipalValue v 1 b

local notation "exteriorZeros(" τ ", " α ")" =>
  {z : {χ : PontryaginDual C𝔽 // ∀ t : ℝ≥0ˣ, χ (τ t) = 1} × ℂ //
    0 < ord(z.1.val, z.2) ∧ α ≤ |z.2.re - 1 / 2|}

local notation "traceIdentity(" τ ", " φ ", " α ")" =>
  (∃ (a : archTest) (b : finiteTest),
      (∀ (w : InfinitePlace F) (u : w.Completionˣ), (a w).val u = (φ).val (archClass(w) u)) ∧
      (∀ (v : V) (u : (v.adicCompletion F)ˣ), (b v).val u = (φ).val (finiteClass(v) u)) ∧
      Summable (fun v : V ↦ finiteTerm(v, b v)) ∧
      HasSum (fun z : interiorZeros(τ, α) ↦ zeroTerm(φ, z))
        (M(φ, twist(1, 1 / 2)) + M(φ, twist(1, -1 / 2)) -
          classVolume * ((∑ w : InfinitePlace F, infiniteConnesWeilPrincipalValue w (a w)) +
            ∑' v : V, finiteTerm(v, b v))))

-- Page 519 introduces tests with φ(1) = 0 and states the theorem for φ(C_F¹) = 0.
-- TODO(paper-gap): Page 520 leaves χ free. Theorem 11.3.2.1 also requires
-- support above norm one. In (11.3.1.4), the signed differences sum to the
-- S-local restriction minus the original kernel. A quotient lift and comparison
-- of the separate shell integrals are missing (ERRATA I292).
-- TODO(paper-gap): Theorem 12.4.1.1 divides by the S-local norm-one volume.
-- Section 12.3 lacks the comparison of this local limit with the global Haar
-- diagonal and the two polar Mellin terms (ERRATA M25).

/-- Paper: Theorem 12.5.1.1, pp. 519–520. For a test vanishing on the norm-one
classes, the zero terms omitted by a positive-width open strip sum to zero.
Gap: The global to S-local comparison on p. 520 must account for every omitted
zero, including zeros on the edges. The all-zero identity of Theorem B.4.4.7
alone gives no such cancellation. -/
theorem traceFormula_exteriorZeros (τ : ℝ≥0ˣ →ₜ* C𝔽) (_hτ : RightInverse τ (ideleClassNorm F))
    (φ : BruhatCompactSupport C𝔽) (_hφ : ∀ g : C₁, φ.val g = 0) {α : ℝ} (_hα : 0 < α) :
    HasSum (fun z : exteriorZeros(τ, α) ↦ zeroTerm(φ, z)) 0 := by sorry

private theorem traceFormula_of_exteriorZeros_mul_congr {a b c d : ℂ} (h1 : a = b)
    (h2 : c = d) : a * c = b * d := by
  rw [h1, h2]

private theorem traceFormula_of_exteriorZeros_vol :
    (((normOneIdeleClassTamagawaMeasure F) univ).toReal : ℂ) ≠ 0 := by
  have hvol := normOneIdeleClassTamagawaMeasure_volume (F := F)
  have hc0 : normOneIdeleClassTamagawaMeasure F univ ≠ 0 := by
    rw [hvol, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    have := NumberField.Units.regulator_pos F
    have := NumberField.classNumber_pos F
    have := NumberField.Units.torsionOrder_pos F
    have : (0 : ℝ) < Real.sqrt (Int.natAbs (NumberField.discr F) : ℝ) :=
      Real.sqrt_pos.mpr (by exact_mod_cast Int.natAbs_pos.mpr (NumberField.discr_ne_zero F))
    positivity
  have hct : normOneIdeleClassTamagawaMeasure F univ ≠ ⊤ := by
    rw [hvol]; exact ENNReal.ofReal_ne_top
  exact Complex.ofReal_ne_zero.mpr (ENNReal.toReal_ne_zero.mpr ⟨hc0, hct⟩)

private theorem traceFormula_of_exteriorZeros_cpow (p a x s : ℂ) (hx : x ≠ 0) :
    p * (a * x ^ s) * x ^ (-1 / 2 : ℂ) = p * (a * x ^ (s - 1 / 2)) := by
  rw [sub_eq_add_neg, Complex.cpow_add _ _ hx]
  ring_nf

private theorem traceFormula_of_exteriorZeros_split {X : Type*} (G : X → ℂ) (Z E I : Set X)
    {T T' : ℂ}
    (hEZ : E ⊆ Z) (hI : ∀ p, p ∈ I ↔ p ∈ Z ∧ p ∉ E) (hT : T = T')
    (hZ : HasSum (fun z : Z ↦ G z) T) (hE : HasSum (fun z : E ↦ G z) 0) :
    HasSum (fun z : I ↦ G z) T' := by
  replace hZ := (hasSum_subtype_iff_indicator (f := G) (s := Z)).mp hZ
  replace hE := (hasSum_subtype_iff_indicator (f := G) (s := E)).mp hE
  refine (hasSum_subtype_iff_indicator (f := G) (s := I)).mpr ?_
  have h : I.indicator G = Z.indicator G - E.indicator G := by
    funext p
    by_cases hp : p ∈ E
    · simp [Set.indicator_of_mem hp, Set.indicator_of_mem (hEZ hp),
        Set.indicator_of_notMem (fun h ↦ ((hI p).mp h).2 hp)]
    · by_cases hz : p ∈ Z
      · simp [Set.indicator_of_mem ((hI p).mpr ⟨hz, hp⟩), Set.indicator_of_mem hz,
          Set.indicator_of_notMem hp]
      · simp [Set.indicator_of_notMem hz, Set.indicator_of_notMem hp,
          Set.indicator_of_notMem (fun h ↦ hz ((hI p).mp h).1)]
  rw [h, ← hT, ← sub_zero T]
  exact hZ.sub hE

private theorem traceFormula_of_exteriorZeros_hasSum_congr {ι : Type*} {f g : ι → ℂ} {a : ℂ}
    (h : HasSum f a) (hfg : ∀ i, f i = g i) : HasSum g a :=
  (funext hfg) ▸ h

private theorem traceFormula_of_exteriorZeros_val {v x p A Fs P1 P2 M1 M2 A' F' : ℂ}
    (hv : v ≠ 0) (hx : x = p - A - Fs) (hp : p = (P1 + P2) / v) (hA : A = A') (hF : Fs = F')
    (h1 : M1 = P2) (h2 : M2 = P1) :
    v * x = M1 + M2 - v * (A' + F') := by
  subst hx hp hA hF h1 h2
  field_simp
  ring

private theorem traceFormula_of_exteriorZeros_one (p a x : ℂ) (ha : a = 1) :
    p * (a * x) = p * x := by
  rw [ha, one_mul]

private theorem traceFormula_of_exteriorZeros_mul_div (v m I : ℂ) (hv : v ≠ 0) :
    v * (m / v * I) = m * I := by
  field_simp

/-- Paper: Theorem B.4.4.7, p. 623, applied to Theorem 12.5.1.1, pp. 519–520.
Evaluating the full explicit formula at a test and removing a zero subseries of
sum zero gives the strip identity. -/
theorem traceFormula_of_exteriorZeros (τ : ℝ≥0ˣ →ₜ* C𝔽) (_hτ : RightInverse τ (ideleClassNorm F))
    (φ : BruhatCompactSupport C𝔽) (α : ℝ)
    (_hTail : HasSum (fun z : exteriorZeros(τ, α) ↦ zeroTerm(φ, z)) 0) :
    traceIdentity(τ, φ, α) := by
  have h := idelicExplicitFormula τ _hτ
  obtain ⟨spectral, poles, arch, finite, hspec, hpoles, harch, hfin, _, hsupp, hsum, hHas⟩ := h
  choose a ha haPV using fun w ↦ harch w φ
  choose b hb hbPV using fun v ↦ hfin v φ
  let E : StrongDual ℂ (BruhatCompactSupport C𝔽) →+ ℂ :=
    { toFun := fun L ↦ L φ, map_zero' := rfl, map_add' := fun _ _ ↦ rfl }
  have hEc : Continuous E := continuous_eval_const φ
  have hT := hsum.hasSum.map E hEc
  have hS := hHas.map E hEc
  refine ⟨a, b, ha, hb, ?_, ?_⟩
  · refine (summable_of_ne_finset_zero (s := (hsupp φ).toFinset) fun v hv ↦ ?_).congr
      fun v ↦ hbPV v
    by_contra hne
    exact hv ((hsupp φ).mem_toFinset.mpr hne)
  have hvol : (classVolume : ℂ) ≠ 0 := traceFormula_of_exteriorZeros_vol
  have hM (c : QuasiCharacter C𝔽) : M(φ, c) = ∫ g, φ.val g * c g ∂μ𝔽 := by
    unfold modulatedFourierMellin
    rw [Set.indicator_of_mem (by simp [relativeVerticalStrip])]
  let X := {χ : PontryaginDual C𝔽 // ∀ t : ℝ≥0ˣ, χ (τ t) = 1} × ℂ
  let G : X → ℂ := fun p ↦
    ((ord(p.1.val, p.2) : ℤ) : ℂ) * M(φ, twist(p.1.val, p.2 - 1 / 2))
  let Z : Set X :=
    {p | 0 < MeromorphicOn.divisor (explicitFormulaCompletedHeckeL p.1.val) univ p.2}
  let Ext : Set X := {p | 0 < ord(p.1.val, p.2) ∧ α ≤ |p.2.re - 1 / 2|}
  let Int : Set X := {p | 0 < ord(p.1.val, p.2) ∧ |p.2.re - 1 / 2| < α}
  have hfun (z : Z) : (classVolume : ℂ) * E (spectral z) = G z.val := by
    change (classVolume : ℂ) * spectral z φ = _
    rw [hspec z φ]
    refine (traceFormula_of_exteriorZeros_mul_div _ _ _ hvol).trans
      (traceFormula_of_exteriorZeros_mul_congr rfl ((integral_congr_ae
        (Filter.Eventually.of_forall fun g ↦ ?_)).trans (hM _).symm))
    have hn : ((((ideleClassNorm F g : ℝ≥0) : ℝ)) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
    change φ.val g * (_ * ((((ideleClassNorm F g : ℝ≥0) : ℝ)) : ℂ) ^ z.val.2) *
        ((((ideleClassNorm F g : ℝ≥0) : ℝ)) : ℂ) ^ (-1 / 2 : ℂ) =
      φ.val g * (_ * ((((ideleClassNorm F g : ℝ≥0) : ℝ)) : ℂ) ^ (z.val.2 - 1 / 2))
    exact traceFormula_of_exteriorZeros_cpow _ _ _ _ hn
  have hZ : HasSum (fun z : Z ↦ G z.val) ((classVolume : ℂ) *
      E (poles - (∑ w, arch w) - (∑' v, finite v))) :=
    traceFormula_of_exteriorZeros_hasSum_congr (hS.mul_left (classVolume : ℂ)) hfun
  refine traceFormula_of_exteriorZeros_split G Z Ext Int (fun p hp ↦ hp.1)
    (fun p ↦ ⟨fun h ↦ ⟨h.1, fun h' ↦ (not_le.mpr h.2) h'.2⟩,
      fun h ↦ ⟨h.1, lt_of_not_ge fun h' ↦ h.2 ⟨h.1, h'⟩⟩⟩) ?_ hZ _hTail
  have hone (r : ℂ) : M(φ, twist(1, r)) = ∫ g, φ.val g *
      ((((ideleClassNorm F g : ℝ≥0) : ℝ)) : ℂ) ^ r ∂μ𝔽 := by
    refine (hM _).trans (integral_congr_ae (Filter.Eventually.of_forall fun g ↦ ?_))
    change φ.val g * (_ * ((((ideleClassNorm F g : ℝ≥0) : ℝ)) : ℂ) ^ r) =
      φ.val g * ((((ideleClassNorm F g : ℝ≥0) : ℝ)) : ℂ) ^ r
    exact traceFormula_of_exteriorZeros_one _ _ _ rfl
  have hx : E (poles - (∑ w, arch w) - (∑' v, finite v)) =
      E poles - E (∑ w, arch w) - E (∑' v, finite v) :=
    (map_sub E _ _).trans (congrArg (· - E _) (map_sub E _ _))
  refine traceFormula_of_exteriorZeros_val hvol hx (hpoles φ) ?_ ?_ (hone _) (hone _)
  · exact (map_sum E arch Finset.univ).trans (Finset.sum_congr rfl fun w _ ↦ haPV w)
  · exact hT.tsum_eq.symm.trans (tsum_congr fun v ↦ hbPV v)

/-- Paper: Theorem 12.5.1.1, pp. 519–520. For compactly supported Bruhat tests
vanishing on the norm-one classes, the pole terms minus the interior zero sum
equal the global norm-one volume times the sum of the local principal values.
Deviation: The half-width is positive as in §1.8.4, p. 53. The global volume
and the normalized complex denominator ‖1 − u‖² follow Theorem B.4.4.7 and
(12.4.1.26). The all-width conclusion uses `traceFormula_exteriorZeros`. -/
theorem traceFormula (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (φ : BruhatCompactSupport C𝔽) (hφ : ∀ g : C₁, φ.val g = 0) {α : ℝ} (hα : 0 < α) :
    traceIdentity(τ, φ, α) :=
  traceFormula_of_exteriorZeros τ hτ φ α (traceFormula_exteriorZeros τ hτ φ hφ hα)

section StripDiagonalProof

open Topology
open scoped ENNReal Pointwise
attribute [local instance] instSpectralQuotientPolynormableSec3
local notation "logNorm" => (fun g : C𝔽 ↦ Real.log ((ideleClassNorm F g).val : ℝ))

/-- Transfer the weighted smooth diagonal integral back to Haar measure. -/
private theorem stripDiagonal_withDensity {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] {μ ν : Measure G} [μ.IsHaarMeasure]
    [IsFiniteMeasureOnCompacts ν] [ν.InnerRegular] {U : ℕ → Set G}
    (hU : IsDPrimeSequence μ U) (hBorel : ∀ n, MeasurableSet (U n))
    {w : G → ℝ≥0} (hw : Continuous w) (hp : ∀ x, 0 < w x)
    (hν : ν = μ.withDensity (fun x ↦ ↑(w x)))
    {k : Lp ℂ 2 (ν.prod ν)} {κ K : G × G → ℂ}
    (hκ : κ =ᵐ[ν.prod ν] k) (hK : ∀ p, K p = (w p.2 : ℂ) * κ p)
    (hT : IsNuclearOperator (integralKernelOperator ν k).val) :
    Integrable (fun x ↦ dSequenceKernelSmoothening μ U K (x, x)) μ ∧
      (∫ x, dSequenceKernelSmoothening μ U K (x, x) ∂μ) =
        hilbertTrace ⟨(integralKernelOperator ν k).val, hT⟩ := by
  have hd := dSequenceKernelSmoothening_mul_continuous_snd_diagonal hU hBorel hw hp hν hκ hT
    (fun x ↦ (w x : ℂ)) (Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp hw))
  rw [← funext hK] at hd
  have hdiag : (fun x ↦ w x • dSequenceKernelSmoothening μ U κ (x, x)) =ᵐ[μ]
      fun x ↦ dSequenceKernelSmoothening μ U K (x, x) := by
    filter_upwards [hd] with x hx
    rw [hx.2]
    change (w x : ℝ) • dSequenceKernelSmoothening μ U κ (x, x) = _
    rw [Complex.real_smul]
  obtain ⟨hi, heq⟩ := integral_dSequenceKernelSmoothening_diagonal hκ hU hBorel hw hp hν hT
  rw [hν, integrable_withDensity_iff_integrable_smul hw.measurable] at hi
  have hchange : (∫ x, dSequenceKernelSmoothening μ U κ (x, x) ∂ν) =
      ∫ x, w x • dSequenceKernelSmoothening μ U κ (x, x) ∂μ := by
    rw [hν, integral_withDensity_eq_integral_smul hw.measurable]
  exact ⟨hi.congr hdiag, (integral_congr_ae hdiag.symm).trans (hchange.symm.trans heq)⟩

/-- Haar diagonal formula for the raw kernel of a nuclear weighted integral operator. -/
private theorem stripDiagonal_of_weightedKernel {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] {μ ν : Measure G} [μ.IsHaarMeasure]
    [IsFiniteMeasureOnCompacts ν] [ν.InnerRegular] {U : ℕ → Set G}
    (hU : IsDPrimeSequence μ U) (hBorel : ∀ n, MeasurableSet (U n))
    {w : G → ℝ≥0} (hw : Continuous w) (hp : ∀ x, 0 < w x)
    (hν : ν = μ.withDensity (fun x ↦ ↑(w x)))
    (K : G × G → ℂ) (T : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) (hT : IsNuclearOperator T)
    (hk : let κ := fun p : G × G ↦ ((w p.2 : ℝ)⁻¹ : ℝ) • K p
      ∃ h : MemLp κ 2 (ν.prod ν), (integralKernelOperator ν (h.toLp κ)).val = T) :
    Integrable (fun x ↦ dSequenceKernelSmoothening μ U K (x, x)) μ ∧
      (∫ x, dSequenceKernelSmoothening μ U K (x, x) ∂μ) = hilbertTrace ⟨T, hT⟩ := by
  let κ (p : G × G) := ((w p.2 : ℝ)⁻¹ : ℝ) • K p
  have hκ : κ =ᵐ[ν.prod ν] hk.choose.toLp κ := hk.choose.coeFn_toLp.symm
  have hN : IsNuclearOperator (integralKernelOperator ν (hk.choose.toLp κ)).val :=
    (congrArg (fun L : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν ↦ IsNuclearOperator L) hk.choose_spec).mpr hT
  have hK (p : G × G) : K p = (w p.2 : ℂ) * κ p := by
    change K p = (w p.2 : ℂ) * (((w p.2 : ℝ)⁻¹ : ℝ) • K p)
    rw [Complex.real_smul, Complex.ofReal_inv,
      mul_inv_cancel_left₀ (Complex.ofReal_ne_zero.mpr (NNReal.coe_pos.mpr (hp p.2)).ne')]
  obtain ⟨hi, heq⟩ := stripDiagonal_withDensity hU hBorel hw hp hν hκ hK hN
  exact ⟨hi, heq.trans (congrArg hilbertTrace (Subtype.ext hk.choose_spec : (⟨_, hN⟩ :
    nuclearEndomorphisms (Lp ℂ 2 ν)) = ⟨T, hT⟩))⟩

/-- A nuclear operator factoring through a bounded section and quotient has its
quotient compression's trace. -/
private theorem stripDiagonal_quotient_compression {H Q : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]
    (q : H →L[ℂ] Q) (j : Q →L[ℂ] H) (hqj : q.comp j = ContinuousLinearMap.id ℂ Q)
    (T : H →L[ℂ] H) (hT : IsNuclearOperator T) (hfac : (T.comp j).comp q = T) :
    ∃ hQ : IsNuclearOperator (q.comp (T.comp j)),
      hilbertTrace ⟨T, hT⟩ = hilbertTrace ⟨q.comp (T.comp j), hQ⟩ := by
  have hj : Injective j := by
    intro x y h
    have h' : (q.comp j) x = (q.comp j) y := congrArg q h
    simpa only [hqj, ContinuousLinearMap.id_apply] using h'
  have hqt : IsNuclearOperator (q.comp T) := by
    obtain ⟨a, l, y, ha, hl, hy, hs⟩ := (isNuclearOperator_iff_isBanachNuclear T).mp hT
    apply (isNuclearOperator_iff_isBanachNuclear _).mpr
    refine ⟨a, l, q ∘ y, ha, hl, ?_, fun x ↦ ?_⟩
    · simpa only [map_zero] using (q.continuous.tendsto 0).comp hy
    · simpa only [Function.comp_apply, ContinuousLinearMap.comp_apply, map_smul] using
        q.hasSum (hs x)
  let P := j.comp q
  let N : nuclearEndomorphisms H := ⟨T, hT⟩
  have hn := isNuclearOperator_factor_comps j hj (q.comp T) hqt
  have htrace := nuclearTrace_factor_comps (hilbert_approximationProperty (H := Q))
    (hilbert_approximationProperty (H := H)) j hj (q.comp T) hqt
  refine ⟨hn.1, ?_⟩
  calc
    hilbertTrace N = hilbertTrace ⟨T * P, mul_mem_nuclearEndomorphisms_right P N⟩ :=
      congrArg hilbertTrace (Subtype.ext hfac.symm)
    _ = hilbertTrace ⟨P * T, mul_mem_nuclearEndomorphisms_left P N⟩ :=
      (spectralRestriction_cyclic P N).symm
    _ = hilbertTrace ⟨q.comp (T.comp j), hn.1⟩ := by
      rw [hilbertTrace_eq_nuclearTrace, hilbertTrace_eq_nuclearTrace]
      exact htrace.symm

/-- Compression computes the trace of an action that descends to the quotient. -/
private theorem stripDiagonal_quotientAction {H Q : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]
    (q : H →L[ℂ] Q) (j : Q →L[ℂ] H) (P A : H →L[ℂ] H) (B : Q →L[ℂ] Q)
    (hqj : q.comp j = ContinuousLinearMap.id ℂ Q) (hjq : j.comp q = P)
    (hqA : q.comp A = B.comp q) (hT : IsNuclearOperator (A.comp P)) :
    ∃ hB : IsNuclearOperator B, hilbertTrace ⟨A.comp P, hT⟩ = hilbertTrace ⟨B, hB⟩ := by
  have hPj : P.comp j = j := by
    rw [← hjq, ContinuousLinearMap.comp_assoc, hqj, ContinuousLinearMap.comp_id]
  have hf : ((A.comp P).comp j).comp q = A.comp P := by
    rw [ContinuousLinearMap.comp_assoc A P j, hPj, ContinuousLinearMap.comp_assoc, hjq]
  have hb : q.comp ((A.comp P).comp j) = B := by
    rw [ContinuousLinearMap.comp_assoc A P j, hPj, ← ContinuousLinearMap.comp_assoc, hqA,
      ContinuousLinearMap.comp_assoc, hqj, ContinuousLinearMap.comp_id]
  obtain ⟨hn, ht⟩ := stripDiagonal_quotient_compression q j hqj (A.comp P) hT hf
  exact ⟨hb ▸ hn, ht.trans (congrArg hilbertTrace (Subtype.ext hb))⟩

/-- Subtracting the spectral kernel gives the negative diagonal for a test vanishing at one. -/
private theorem stripDiagonal_convolution_sub (U : ℕ → Set C𝔽) (hU : IsDPrimeSequence μ𝔽 U)
    (hBorel : ∀ n, MeasurableSet (U n)) (φ : BruhatCompactSupport C𝔽) (hφ : φ.val 1 = 0)
    (g : C𝔽 × C𝔽 → ℂ) (x : C𝔽) :
    dSequenceKernelSmoothening μ𝔽 U (fun y ↦ φ.val (y.1 * y.2⁻¹) - g y) (x, x) =
      -dSequenceKernelSmoothening μ𝔽 U g (x, x) := by
  classical
  let G := IdeleClassGroup (𝓞 F) F
  let μ : Measure (G × G) :=
    (ideleClassTamagawaMeasure F).prod (ideleClassTamagawaMeasure F)
  let rects : ℕ → Set (G × G) := fun n ↦ U n ×ˢ U n
  let f : G × G → ℂ := fun y ↦ φ.val (y.1 * y.2⁻¹)
  let p : G × G := (x, x)
  change dSequenceSmootheningOrZero μ rects (fun y ↦ f y - g y) p =
    -dSequenceSmootheningOrZero μ rects g p
  obtain ⟨hf, hlim⟩ := diagonal_mem_convolutionKernelRegularSet_averages hU hBorel φ x
  change ∀ᶠ n in atTop, IntegrableOn f (p • rects n) μ at hf
  change Tendsto (fun n ↦ dSequenceAverage μ (rects n) f p) atTop (𝓝 (φ.val 1)) at hlim
  rw [hφ] at hlim
  have hsum : Tendsto (fun n ↦
      dSequenceAverage μ (rects n) (fun y ↦ f y - g y) p +
        dSequenceAverage μ (rects n) g p) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (by simpa only [norm_zero] using hlim.norm)
    filter_upwards [hf] with n hn
    by_cases hg : IntegrableOn g (p • rects n) μ
    · change ‖(⨍ y in p • rects n, f y - g y ∂μ) +
          (⨍ y in p • rects n, g y ∂μ)‖ ≤ ‖⨍ y in p • rects n, f y ∂μ‖
      rw [setAverage_fun_sub hn hg, sub_add_cancel]
    · -- If the spectral integral is undefined, both totalized averages vanish.
      have hfg : ¬ IntegrableOn (fun y ↦ f y - g y) (p • rects n) μ := by
        intro h
        apply hg
        simpa only [Pi.sub_def, sub_sub_cancel] using hn.sub h
      have hzero : dSequenceAverage μ (rects n) g p = 0 := by
        rw [dSequenceAverage, setAverage_eq, integral_undef hg, smul_zero]
      have hsubzero : dSequenceAverage μ (rects n) (fun y ↦ f y - g y) p = 0 := by
        rw [dSequenceAverage, setAverage_eq, integral_undef hfg, smul_zero]
      rw [hzero, hsubzero, zero_add, norm_zero]
      exact norm_nonneg _
  by_cases hg : p ∈ dSequenceRegularSet μ rects g
  · obtain ⟨v, hv⟩ := hg
    have hgreg : p ∈ dSequenceRegularSet μ rects g := ⟨v, hv⟩
    have hsub : Tendsto (fun n ↦ dSequenceAverage μ (rects n) (fun y ↦ f y - g y) p)
        atTop (𝓝 (-v)) := by
      simpa only [add_sub_cancel_right, zero_sub] using hsum.sub hv
    have hreg : p ∈ dSequenceRegularSet μ rects (fun y ↦ f y - g y) := ⟨-v, hsub⟩
    simp only [dSequenceSmootheningOrZero, dite_eq_left hreg, dite_eq_left hgreg,
      dSequenceSmoothening, hsub.limUnder_eq, hv.limUnder_eq]
  · have hreg : p ∉ dSequenceRegularSet μ rects (fun y ↦ f y - g y) := by
      rintro ⟨v, hv⟩
      apply hg
      refine ⟨-v, ?_⟩
      simpa only [add_sub_cancel_left, zero_sub] using hsum.sub hv
    simp only [dSequenceSmootheningOrZero, dite_eq_right hreg, dite_eq_right hg, neg_zero]

variable {hone_lt_three : (1 : ℝ) < 3}
local notation "hs₁(" hs ")" => (lt_of_lt_of_le hone_lt_three hs)
local notation "hs₀(" hs ")" => (le_of_lt (zero_lt_one.trans hs₁(hs)))
local notation "hStrip(" hα ")" => (neg_nonpos.mpr hα |>.trans hα)
local notation "stripTensorExists(" hα ", " hs ", " φ ")" =>
  (∃ K, sobolevProjectiveKernelOperator (F := F) hα hs₀(hs) K =
    (hardySobolevTestAction μ𝔽 m𝔽 _ _ _ (hStrip(hα)) hs₀(hs) φ).comp
      (spectralProjection (F := F) (1 / 2) hα hs₀(hs)))

local notation "geomDiagonal(" hα ", " hs ", " φ ", " hK ", " U ")" =>
  (fun x : C𝔽 ↦ dSequenceKernelSmoothening μ𝔽 U
    (globalStripGeometricKernel (F := F) (1 / 2) hα hs₁(hs) φ hK) (x, x))
local notation "stripQuotientAction(" hα ", " hs ", " φ ")" =>
  spectralConvolution (F := F) (1 / 2) (hStrip(hα)) hs₀(hs) φ

/-- A projective tensor represents a nuclear operator on the Sobolev space. -/
private theorem stripDiagonal_projective_nuclear {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (K : UniformSpace.Completion (ProjectiveTensor
      (CompactIntervalSobolev μ𝔽 logNorm (-α) α s true)
      (CompactIntervalSobolev μ𝔽 logNorm (-α) α s))) :
    IsNuclearOperator (sobolevProjectiveKernelOperator (F := F) hα hs K) :=
  (isNuclearOperator_iff_isBanachNuclear _).mpr
    ((isBanachNuclear_iff_mem_range _).mpr ⟨_, rfl⟩)

local notation "AP(" hp ", " hs ", " φ ")" =>
  (hardySobolevTestAction μ𝔽 m𝔽 _ _ _ (hStrip(hp)) hs₀(hs) φ).comp
    (spectralProjection (F := F) (1 / 2) hp hs₀(hs))
local notation "spectralDiagonal(" hp ", " hs ", " φ ", " hK ", " U ")" =>
  (fun x : C𝔽 ↦ dSequenceKernelSmoothening μ𝔽 U (globalStripSpectralKernel (F := F)
    (1 / 2) hp hs₁(hs) φ hK) (x, x))

/-- The projective tensor gives nuclearity and equal traces for the ambient and quotient actions. -/
private theorem stripDiagonal_projective_trace (φ : BruhatCompactSupport C𝔽) {α s : ℝ}
    (hα : 0 < α) (hs : 3 ≤ s)
    (hK : stripTensorExists(hα.le, hs, φ)) :
    ∃ (hn : IsNuclearOperator (AP(hα.le, hs, φ)))
      (hq : IsNuclearOperator (spectralConvolution (F := F) (1 / 2) (hStrip(hα.le)) hs₀(hs) φ)),
      hilbertTrace ⟨AP(hα.le, hs, φ), hn⟩ =
        hilbertTrace ⟨spectralConvolution (F := F) (1 / 2) (hStrip(hα.le)) hs₀(hs) φ, hq⟩ := by
  let W := CompactIntervalSobolev μ𝔽 logNorm (-α) α s
  let A : W →L[ℂ] W := hardySobolevTestAction μ𝔽 m𝔽 (-α) α s (hStrip(hα.le)) hs₀(hs) φ
  let P : W →L[ℂ] W := spectralProjection (F := F) (1 / 2) hα.le hs₀(hs)
  let theta := globalThetaSobolev F (1 / 2) (hStrip(hα.le)) hs₀(hs)
  let q := theta.mkQL
  let j := theta.orthogonal.subtypeL.comp
    theta.quotientEquivOrthogonal.toContinuousLinearEquiv.toContinuousLinearMap
  let B := spectralConvolution (F := F) (1 / 2) (hStrip(hα.le)) hs₀(hs) φ
  have hap : IsNuclearOperator (A * P) :=
    (congrArg (fun L : W →L[ℂ] W ↦ IsNuclearOperator L) hK.choose_spec).mp
      (stripDiagonal_projective_nuclear (F := F) hα.le hs₀(hs) hK.choose)
  have hqj : q.comp j = ContinuousLinearMap.id ℂ _ := by
    ext x
    exact theta.quotientEquivOrthogonal.symm_apply_apply x
  have hjq : j.comp q = P := by
    apply ContinuousLinearMap.ext
    intro x
    exact (spectralQuotient_orthogonalRepresentative (F := F) (1 / 2) hα.le hs₀(hs)
      (by norm_num) x).1
  have hqA : q.comp A = B.comp q := by
    apply ContinuousLinearMap.ext
    intro x
    exact (spectralConvolution_mkQ (F := F) (1 / 2) (hStrip(hα.le)) hs₀(hs) φ x).symm
  exact ⟨hap, stripDiagonal_quotientAction q j P A B hqj hjq hqA hap⟩

/-- The weighted Hilbert–Schmidt representative recovers the Haar mass of the spectral diagonal. -/
private theorem stripDiagonal_projective_integral (φ : BruhatCompactSupport C𝔽) {α s : ℝ}
    (hα : 0 < α) (hs : 3 ≤ s)
    (hK : stripTensorExists(hα.le, hs, φ)) (hap : IsNuclearOperator (AP(hα.le, hs, φ)))
    (U : ℕ → Set C𝔽) (_hU : IsDPrimeSequence μ𝔽 U) (_hBorel : ∀ n, MeasurableSet (U n)) :
    Integrable spectralDiagonal(hα.le, hs, φ, hK, U) μ𝔽 ∧
      (∫ x, spectralDiagonal(hα.le, hs, φ, hK, U) x ∂μ𝔽) = hilbertTrace ⟨AP(hα.le, hs, φ), hap⟩ := by
  let w (x : C𝔽) := intervalSobolevDensity (-α) α s (logNorm x)
  let ν := (μ𝔽).withDensity (fun g ↦ ENNReal.ofReal (w g))
  let W := CompactIntervalSobolev μ𝔽 logNorm (-α) α s
  let κ := (globalStripSpectralKernel (F := F) (1 / 2) hα.le hs₁(hs) φ hK : C𝔽 × C𝔽 → ℂ)
  let A : W →L[ℂ] W := hardySobolevTestAction μ𝔽 m𝔽 (-α) α s (hStrip(hα.le)) hs₀(hs) φ
  let P : W →L[ℂ] W := spectralProjection (F := F) (1 / 2) hα.le hs₀(hs)
  have hw : Continuous w :=
    (continuous_intervalSobolevDensity (-α) α s).comp (continuous_logModule' m𝔽)
  have hwpos (x : C𝔽) : 0 < w x := intervalSobolevDensity_pos' _ _ _ _
  let wNN (x : C𝔽) : ℝ≥0 := ⟨w x, (hwpos x).le⟩
  have hwNN : Continuous wNN := hw.subtype_mk _
  have hν : ν = (μ𝔽).withDensity (fun x ↦ (wNN x : ℝ≥0∞)) :=
    congrArg (μ𝔽).withDensity (funext fun x ↦ ENNReal.ofReal_eq_coe_nnreal (hwpos x).le)
  let : IsLocallyFiniteMeasure ν := sobolevKernelWeight_locallyFinite (F := F) α s
  have hHS := spectralStripKernel_hilbertSchmidt (F := F) (1 / 2) hα.le hs₁(hs) φ (by norm_num) hK
  exact stripDiagonal_of_weightedKernel _hU _hBorel hwNN hwpos hν κ (A * P) hap hHS

/-- The smoothed spectral diagonal is integrable and has the quotient trace as its Haar integral. -/
private theorem stripDiagonal_spectral_integral (φ : BruhatCompactSupport C𝔽) {α s : ℝ}
    (hα : 0 < α) (hs : 3 ≤ s) (hK : stripTensorExists(hα.le, hs, φ))
    (U : ℕ → Set C𝔽) (hU : IsDPrimeSequence μ𝔽 U) (hBorel : ∀ n, MeasurableSet (U n)) :
    ∃ hq : IsNuclearOperator (stripQuotientAction(hα.le, hs, φ)),
      Integrable spectralDiagonal(hα.le, hs, φ, hK, U) μ𝔽 ∧
        (∫ x, spectralDiagonal(hα.le, hs, φ, hK, U) x ∂μ𝔽) =
          hilbertTrace ⟨stripQuotientAction(hα.le, hs, φ), hq⟩ := by
  have h := stripDiagonal_projective_trace (F := F) (hone_lt_three := hone_lt_three) φ hα hs hK
  have d := stripDiagonal_projective_integral (F := F) (hone_lt_three := hone_lt_three)
    φ hα hs hK h.choose U hU hBorel
  exact ⟨h.choose_spec.choose, d.1, d.2.trans h.choose_spec.choose_spec⟩

/-- If the test vanishes at one, subtraction gives the negative spectral diagonal at every point. -/
private theorem stripDiagonal_geometric_eq_neg (φ : BruhatCompactSupport C𝔽) {α s : ℝ}
    (hα : 0 < α) (hs : 3 ≤ s) (hK : stripTensorExists(hα.le, hs, φ))
    (U : ℕ → Set C𝔽) (hU : IsDPrimeSequence μ𝔽 U) (hBorel : ∀ n, MeasurableSet (U n))
    (hφ : φ.val 1 = 0) :
    geomDiagonal(hα.le, hs, φ, hK, U) = fun x ↦ -spectralDiagonal(hα.le, hs, φ, hK, U) x := by
  let K := (globalStripSpectralKernel (F := F) (1 / 2) hα.le hs₁(hs) φ hK : C𝔽 × C𝔽 → ℂ)
  exact funext (stripDiagonal_convolution_sub (F := F) U hU hBorel φ hφ K)

/-- Vanishing of the test on norm-one classes determines the Haar integral of the geometric diagonal. -/
private theorem stripDiagonal_trace (φ : BruhatCompactSupport C𝔽)
    (_hφ : ∀ g : C₁, φ.val g = 0) {α s : ℝ} (hα : 0 < α) (hs : 3 ≤ s)
    (hK : stripTensorExists(hα.le, hs, φ))
    (U : ℕ → Set C𝔽) (_hU : IsDPrimeSequence μ𝔽 U) (_hBorel : ∀ n, MeasurableSet (U n)) :
    ∃ hq : IsNuclearOperator (stripQuotientAction(hα.le, hs, φ)),
      Integrable geomDiagonal(hα.le, hs, φ, hK, U) μ𝔽 ∧
        (∫ x, geomDiagonal(hα.le, hs, φ, hK, U) x ∂μ𝔽) =
          -hilbertTrace ⟨stripQuotientAction(hα.le, hs, φ), hq⟩ := by
  have heq := stripDiagonal_geometric_eq_neg (F := F) (hone_lt_three := hone_lt_three)
    φ hα hs hK U _hU _hBorel (_hφ 1)
  have hspec := stripDiagonal_spectral_integral (F := F) (hone_lt_three := hone_lt_three)
    φ hα hs hK U _hU _hBorel
  let f := spectralDiagonal(hα.le, hs, φ, hK, U)
  have hchange := congrArg (fun q : C𝔽 → ℂ ↦ ∫ x, q x ∂μ𝔽) heq
  refine ⟨hspec.choose, ?_,
    hchange.trans ((integral_neg f).trans (congrArg Neg.neg hspec.choose_spec.2))⟩
  rw [heq]
  exact hspec.choose_spec.1.neg

end StripDiagonalProof

section SmoothenedDiagonal

local notation "hs₁(" hs ")" => (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 3) hs)
local notation "hs₀(" hs ")" => (le_of_lt (zero_lt_one.trans hs₁(hs)))
local notation "hStrip(" hα ")" => (neg_nonpos.mpr hα |>.trans hα)
local notation "stripTensorExists(" hα ", " hs ", " φ ")" =>
  (∃ K, sobolevProjectiveKernelOperator (F := F) hα hs₀(hs) K =
    (hardySobolevTestAction μ𝔽 m𝔽 _ _ _ (hStrip(hα)) hs₀(hs) φ).comp
      (spectralProjection (F := F) (1 / 2) hα hs₀(hs)))

local notation "geomDiagonal(" hα ", " hs ", " φ ", " hK ", " U ")" =>
  (fun x : C𝔽 ↦ dSequenceKernelSmoothening μ𝔽 U
    (globalStripGeometricKernel (F := F) (1 / 2) hα hs₁(hs) φ hK) (x, x))
local notation "quotientTrace(" hα ", " hs ", " φ ")" =>
  (hilbertTrace (H := spectralSobolevQuotient F (1 / 2) (hStrip(hα)) hs₀(hs))
    ⟨spectralConvolution (F := F) (1 / 2) (hStrip(hα)) hs₀(hs) φ,
      spectralStripConvolution_nuclear (F := F) (1 / 2) hα hs₁(hs) φ⟩)

/-- Paper: (12.5.1.4), p. 520. The smoothened geometric diagonal is
Haar-integrable and its integral is minus the strip quotient trace.
Gap: Theorem 10.4.2.8 gives a cutoff trace limit. Identifying it with this
Haar diagonal requires the input Sobolev weight and justification for
removing the cutoff (ERRATA I341 and I351).
Deviation: Definition 10.4.3.7 uses the tensor for convolution after projection.
The right side is the trace computed by `spectralStripConvolution_trace`. It
counts the closed strip with `spectralStripMultiplicity`. When the two edges
contain no zeros this recovers the interior sum in (12.5.1.4). -/
theorem integral_smoothenedStripGeometricKernel_diagonal (φ : BruhatCompactSupport C𝔽)
    (_hφ : ∀ g : C₁, φ.val g = 0) {α s : ℝ} (hα : 0 < α) (hs : 3 ≤ s)
    (hK : stripTensorExists(hα.le, hs, φ))
    (U : ℕ → Set C𝔽) (_hU : IsDPrimeSequence μ𝔽 U) (_hBorel : ∀ n, MeasurableSet (U n)) :
    Integrable geomDiagonal(hα.le, hs, φ, hK, U) μ𝔽 ∧
      (∫ x, geomDiagonal(hα.le, hs, φ, hK, U) x ∂μ𝔽) = -quotientTrace(hα.le, hs, φ) := by
  -- Reuse the statement’s proof of 1 < 3 throughout the Sobolev operator types.
  exact (stripDiagonal_trace (F := F)
    (hone_lt_three := integral_smoothenedStripGeometricKernel_diagonal._proof_1)
    φ _hφ hα hs hK U _hU _hBorel).choose_spec

end SmoothenedDiagonal

section ClosedStripZeroSum

local notation "oneLtThree" => (show (1 : ℝ) < 3 from Nat.one_lt_cast.mpr (Nat.one_lt_succ_succ 1))

local notation "hs₁(" hs ")" => (lt_of_lt_of_le oneLtThree hs)
local notation "hs₀(" hs ")" => (le_of_lt (zero_lt_one.trans hs₁(hs)))
local notation "hStrip(" hα ")" => (neg_nonpos.mpr hα |>.trans hα)
local notation "stripTensorExists(" hα ", " hs ", " φ ")" =>
  (∃ K, sobolevProjectiveKernelOperator (F := F) hα hs₀(hs) K =
    (hardySobolevTestAction μ𝔽 m𝔽 _ _ _ (hStrip(hα)) hs₀(hs) φ).comp
      (spectralProjection (F := F) (1 / 2) hα hs₀(hs)))

local notation "geomDiagonal(" hα ", " hs ", " φ ", " hK ", " U ")" =>
  (fun x : C𝔽 ↦ dSequenceKernelSmoothening μ𝔽 U
    (globalStripGeometricKernel (F := F) (1 / 2) hα hs₁(hs) φ hK) (x, x))

/-- Paper: (12.5.1.4), p. 520. Given the projective kernel, the smoothened
geometric diagonal is Haar-integrable. Its negative integral is the absolutely
convergent sum of the surviving Hecke zero jets.
Deviation: The trace counts the closed strip with strict reciprocal-weight
multiplicities on its two edges. If both edges are zero-free the sum is precisely
the interior sum printed on p. 520. -/
theorem hasSum_stripZeros_neg_integral_smoothenedDiagonal
    (φ : BruhatCompactSupport C𝔽) (hφ : ∀ g : C₁, φ.val g = 0)
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    {α s : ℝ} (hα : 0 < α) (hs : 3 ≤ s) (hK : stripTensorExists(hα.le, hs, φ))
    (U : ℕ → Set C𝔽) (hU : IsDPrimeSequence μ𝔽 U) (hBorel : ∀ n, MeasurableSet (U n)) :
    let shift (b t : ℝ) := (b : ℂ) + (t : ℂ) * Complex.I
    let order (η : PontryaginDual C𝔽) := meromorphicOrderAt (continuedCompletedHeckeL η)
    let Z := {z : PontryaginDual C₁ × ℝ × ℝ //
      z.2.1 ∈ Icc (-α) α ∧ 0 < order (χ z.1) (shift (1 / 2 + z.2.1) z.2.2)}
    let term (z : Z) := ((spectralStripMultiplicity α s z.val.2.1
      (order (χ z.val.1) (shift (1 / 2 + z.val.2.1) z.val.2.2)).untop₀.toNat : ℕ) : ℂ) *
      M(φ, twist(χ z.val.1, shift z.val.2.1 z.val.2.2))
    Integrable geomDiagonal(hα.le, hs, φ, hK, U) μ𝔽 ∧ Summable (fun z ↦ ‖term z‖) ∧
      HasSum term (-(∫ x, geomDiagonal(hα.le, hs, φ, hK, U) x ∂μ𝔽)) := by
  intro shift order Z term
  obtain ⟨hn, hint, heq⟩ := stripDiagonal_trace (F := F) (hone_lt_three := oneLtThree)
    φ hφ hα hs hK U hU hBorel
  let T : nuclearEndomorphisms (spectralSobolevQuotient F (1 / 2) (hStrip(hα.le)) hs₀(hs)) := ⟨_, hn⟩
  obtain ⟨hsum, ht⟩ := spectralStripConvolution_trace (F := F) (1 / 2) χ hχ hα.le hs₁(hs) φ T rfl
  refine ⟨hint, hsum, ?_⟩
  rw [heq, neg_neg]
  exact ht

end ClosedStripZeroSum

section ExteriorZerosGRH

/-! ### The exterior-zero cancellation is equivalent to GRH

`traceFormula_exteriorZeros` is recorded as a gap. For one half-width α, its conclusion for
every test is equivalent to the absence of zeros with |Re s − 1/2| ≥ α. -/

open scoped ContDiff

section BruhatSmoothNorm

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G]

/-- A continuous homomorphism into the reals kills every compact subgroup. -/
private theorem compact_subgroup_le_ker (L : G →* Multiplicative ℝ) (hL : Continuous L)
    {k : Subgroup G} (hk : IsCompact (k : Set G)) : k ≤ L.ker := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp ((hk.image
    ((show Continuous (Multiplicative.toAdd : Multiplicative ℝ → ℝ) from continuous_id).comp
      hL)).isBounded)
  intro x hx
  rw [MonoidHom.mem_ker]
  by_contra h
  have hne : (L x).toAdd ≠ 0 := h
  have hxpos : 0 < |(L x).toAdd| := abs_pos.mpr hne
  obtain ⟨n, hn⟩ := exists_nat_gt (C / |(L x).toAdd|)
  have hbound := hC (L (x ^ n)).toAdd ⟨x ^ n, k.pow_mem hx n, rfl⟩
  rw [map_pow, toAdd_pow, nsmul_eq_mul, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Nat.cast_nonneg n)] at hbound
  exact (not_lt_of_ge hbound) ((div_lt_iff₀ hxpos).mp hn)

private def coverZeroHom' {m n r : ℕ} {F : Type*} [AddCommGroup F] :
    EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) →+ ElementaryLieGroup m n r F where
  toFun := fun xt ↦ elementaryCover xt 0 0
  map_zero' := Prod.ext rfl (Prod.ext (funext fun _ ↦ AddCircle.coe_zero (1 : ℝ)) rfl)
  map_add' x y := Prod.ext rfl
    (Prod.ext (funext fun i ↦ AddCircle.coe_add (1 : ℝ) (x.2 i) (y.2 i)) (zero_add _).symm)

private theorem coverZeroHom'_continuous {m n r : ℕ} {F : Type*}
    [AddCommGroup F] [TopologicalSpace F] :
    Continuous (coverZeroHom' (m := m) (n := n) (r := r) (F := F)) :=
  continuous_fst.prodMk
    ((continuous_pi fun i ↦ (AddCircle.continuous_mk' (1 : ℝ)).comp
      ((PiLp.continuous_apply 2 _ i).comp continuous_snd)).prodMk continuous_const)

/-- On each fiber of an elementary group, a smooth function of a real-valued
continuous homomorphism is smooth in the cover coordinates. -/
private theorem contDiff_elementary_realHom {m n r : ℕ} {F : Type*} [AddCommGroup F]
    [TopologicalSpace F] [DiscreteTopology F]
    (ψ : Multiplicative (ElementaryLieGroup m n r F) →* Multiplicative ℝ) (hψ : Continuous ψ)
    {H : ℝ → ℂ} (hH : ContDiff ℝ (∞) H) (z : Fin r → ℤ) (b : F) {p : ℕ∞} :
    ContDiff ℝ p (fun u ↦ H (ψ (Multiplicative.ofAdd (elementaryCover u z b))).toAdd) := by
  let c := coverZeroHom' (m := m) (n := n) (r := r) (F := F)
  let ℓ : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) →+ ℝ :=
    (MonoidHom.toAdditive ψ).comp c
  have hℓ : Continuous ℓ := hψ.comp coverZeroHom'_continuous
  have hshift u : c u + elementaryCover 0 z b = elementaryCover u z b := by
    change elementaryCover u 0 0 + elementaryCover 0 z b = elementaryCover u z b
    refine Prod.ext (add_zero _) (Prod.ext (funext fun i ↦ ?_) (Prod.ext (zero_add _) (zero_add _)))
    change ((u.2 i : ℝ) : AddCircle (1 : ℝ)) + (((0 : EuclideanSpace ℝ (Fin n)) i : ℝ) :
      AddCircle (1 : ℝ)) = ((u.2 i : ℝ) : AddCircle (1 : ℝ))
    rw [show ((0 : EuclideanSpace ℝ (Fin n)) i : ℝ) = 0 from rfl, AddCircle.coe_zero, add_zero]
  have heq u : (ψ (Multiplicative.ofAdd (elementaryCover u z b))).toAdd =
      ℓ u + (ψ (Multiplicative.ofAdd (elementaryCover 0 z b))).toAdd := by
    rw [← hshift u, ofAdd_add, map_mul, toAdd_mul]
    rfl
  rw [show (fun u ↦ H (ψ (Multiplicative.ofAdd (elementaryCover u z b))).toAdd) =
      fun u ↦ H (ℓ u + (ψ (Multiplicative.ofAdd (elementaryCover 0 z b))).toAdd) from
    funext fun u ↦ by rw [heq u]]
  have : ContinuousSMul ℝ (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) :=
    Prod.continuousSMul
  have hlin : ContDiff ℝ p (fun u ↦ ℓ u) := (ℓ.toRealLinearMap hℓ).contDiff
  exact (hH.of_le (by exact_mod_cast le_top)).comp (hlin.add contDiff_const)

/-- A smooth function of a continuous real-valued homomorphism is Bruhat smooth. -/
private theorem isBruhatSmooth_comp_realHom (L : G →* Multiplicative ℝ) (hL : Continuous L)
    {H : ℝ → ℂ} (hH : ContDiff ℝ (∞) H) :
    IsBruhatSmooth (fun g ↦ H (L g).toAdd) := by
  obtain ⟨k, hk, -, -⟩ := isBruhatContDiff_zero (G := G) 0
  have hker : k ≤ L.ker := compact_subgroup_le_ker L hL hk.isCompact
  intro p
  refine ⟨k, hk, fun h x ↦ ?_, fun a ha ↦ ?_⟩
  · show H (L (h.val * x)).toAdd = H (L x).toAdd
    rw [map_mul, MonoidHom.mem_ker.mp (hker h.property), one_mul]
  · let N := (OrderDual.ofDual a.val.2).comap a.val.1.subtype
    let q : a.quotient →* Multiplicative ℝ :=
      QuotientGroup.lift N (L.comp a.val.1.subtype) (fun x hx ↦ hker (ha ▸ hx))
    have hq : Continuous q := (QuotientGroup.isQuotientMap_mk N).continuous_iff.mpr
      (hL.comp continuous_subtype_val)
    refine ⟨fun x ↦ H (q x).toAdd, fun x ↦ rfl, fun e z b ↦ ?_⟩
    exact contDiff_elementary_realHom (q.comp e.equiv.symm.toMulEquiv.toMonoidHom)
      (hq.comp e.equiv.symm.continuous) hH z b

/-- Multiplying a Bruhat `Cᵖ` function by a smooth function of a continuous real-valued
homomorphism keeps it Bruhat `Cᵖ` (with the same good subgroup). -/
private theorem IsBruhatContDiff.mul_comp_realHom {p : ℕ} {f : G → ℂ} (hf : IsBruhatContDiff p f)
    (L : G →* Multiplicative ℝ) (hL : Continuous L) {H : ℝ → ℂ} (hH : ContDiff ℝ (∞) H) :
    IsBruhatContDiff p (fun g ↦ f g * H (L g).toAdd) := by
  obtain ⟨k, hk, hinv, hdesc⟩ := hf
  have hker : k ≤ L.ker := compact_subgroup_le_ker L hL hk.isCompact
  refine ⟨k, hk, fun h x ↦ ?_, fun a ha ↦ ?_⟩
  · show f (h.val * x) * H (L (h.val * x)).toAdd = f x * H (L x).toAdd
    rw [hinv h x, map_mul, MonoidHom.mem_ker.mp (hker h.property), one_mul]
  · obtain ⟨f₀, hf₀, hcd⟩ := hdesc a ha
    let N := (OrderDual.ofDual a.val.2).comap a.val.1.subtype
    let q : a.quotient →* Multiplicative ℝ :=
      QuotientGroup.lift N (L.comp a.val.1.subtype) (fun x hx ↦ hker (ha ▸ hx))
    have hq : Continuous q := (QuotientGroup.isQuotientMap_mk N).continuous_iff.mpr
      (hL.comp continuous_subtype_val)
    refine ⟨fun x ↦ f₀ x * H (q x).toAdd, fun x ↦ ?_, fun e z b ↦ ?_⟩
    · show f₀ (QuotientGroup.mk x) * H (q (QuotientGroup.mk x)).toAdd = f x.val * H (L x.val).toAdd
      rw [hf₀ x]
      rfl
    · exact (hcd e z b).mul (contDiff_elementary_realHom
        (q.comp e.equiv.symm.toMulEquiv.toMonoidHom)
        (hq.comp e.equiv.symm.continuous) hH z b)

/-- Multiplying a Bruhat smooth function by a smooth function of a continuous real-valued
homomorphism keeps it Bruhat smooth. -/
private theorem IsBruhatSmooth.mul_comp_realHom {f : G → ℂ} (hf : IsBruhatSmooth f)
    (L : G →* Multiplicative ℝ) (hL : Continuous L) {H : ℝ → ℂ} (hH : ContDiff ℝ (∞) H) :
    IsBruhatSmooth (fun g ↦ f g * H (L g).toAdd) :=
  fun p ↦ (hf p).mul_comp_realHom L hL hH

/-- A unitary character times a smooth function of a continuous real-valued homomorphism
is Bruhat smooth. -/
private theorem isBruhatSmooth_character_mul_comp_realHom (ψ : PontryaginDual G)
    (L : G →* Multiplicative ℝ) (hL : Continuous L) {H : ℝ → ℂ} (hH : ContDiff ℝ (∞) H) :
    IsBruhatSmooth (fun g ↦ (ψ g : ℂ) * H (L g).toAdd) :=
  IsBruhatSmooth.mul_comp_realHom
    ((mem_bruhatSmoothSubmodule_iff _).mp (pontryaginDual_mem_bruhatSmooth ψ)) L hL hH

end BruhatSmoothNorm

section NormTests

private theorem nnrealUnits_coe_pos (u : ℝ≥0ˣ) : (0 : ℝ) < ((u : ℝ≥0) : ℝ) :=
  NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr u.ne_zero)

/-- The logarithm of the idele class norm, as a continuous homomorphism to the reals. -/
private noncomputable def ideleClassLogNorm (F : Type*) [Field F] [NumberField F] :
    IdeleClassGroup (𝓞 F) F →* Multiplicative ℝ where
  toFun x := Multiplicative.ofAdd (Real.log ((ideleClassNorm F x : ℝ≥0) : ℝ))
  map_one' := by simp
  map_mul' x y := by
    rw [map_mul, Units.val_mul, NNReal.coe_mul,
      Real.log_mul (nnrealUnits_coe_pos _).ne' (nnrealUnits_coe_pos _).ne', ofAdd_add]

private theorem continuous_ideleClassLogNorm : Continuous (ideleClassLogNorm F) := by
  have hc : Continuous (fun x : C𝔽 ↦ ((ideleClassNorm F x : ℝ≥0) : ℝ)) :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp
      (isProperMap_ideleClassNorm F).continuous)
  exact continuous_ofAdd.comp (hc.log fun x ↦ (nnrealUnits_coe_pos _).ne')

/-- A smooth compactly supported function of the logarithm of the norm is a test function. -/
private theorem exists_normTest (g : ℝ → ℂ) (hg : ContDiff ℝ (∞) g) (hgc : HasCompactSupport g) :
    ∃ φ : BruhatCompactSupport C𝔽,
      ∀ x, φ.val x = g (Real.log ((ideleClassNorm F x : ℝ≥0) : ℝ)) := by
  have hs := isBruhatSmooth_comp_realHom (ideleClassLogNorm F)
    (continuous_ideleClassLogNorm (F := F)) hg
  have hcs : HasCompactSupport (fun x : C𝔽 ↦ g (ideleClassLogNorm F x).toAdd) := by
    let E : ℝ → ℝ≥0ˣ := fun t ↦
      Units.mk0 (Real.exp t).toNNReal (Real.toNNReal_pos.mpr (Real.exp_pos t)).ne'
    have hE : Continuous E := Units.continuous_iff.mpr
      ⟨continuous_real_toNNReal.comp Real.continuous_exp,
        (continuous_real_toNNReal.comp Real.continuous_exp).inv₀ fun t ↦
          (Real.toNNReal_pos.mpr (Real.exp_pos t)).ne'⟩
    have hK : IsCompact (E '' tsupport g) := hgc.isCompact.image hE
    refine HasCompactSupport.intro ((isProperMap_ideleClassNorm F).isCompact_preimage hK)
      fun x hx ↦ image_eq_zero_of_notMem_tsupport fun hmem ↦ hx ⟨_, hmem, ?_⟩
    apply Units.ext
    change (Real.exp (Real.log _)).toNNReal = _
    rw [Real.exp_log (nnrealUnits_coe_pos _), Real.toNNReal_coe]
  exact ⟨(⟨_, (mem_bruhatSmoothSubmodule_iff _).mpr hs, hcs⟩ :
    bruhatCompactSupportSubmodule C𝔽), fun _ ↦ rfl⟩

/-- A unitary character times a smooth compactly supported function of the logarithm of
the norm is a test function. -/
private theorem exists_characterNormTest (ψ : PontryaginDual C𝔽) (g : ℝ → ℂ) (hg : ContDiff ℝ (∞) g)
    (hgc : HasCompactSupport g) :
    ∃ φ : BruhatCompactSupport C𝔽,
      ∀ x, φ.val x = (ψ x : ℂ) * g (Real.log ((ideleClassNorm F x : ℝ≥0) : ℝ)) := by
  obtain ⟨φ₀, hφ₀⟩ := exists_normTest (F := F) g hg hgc
  have hs := isBruhatSmooth_character_mul_comp_realHom ψ (ideleClassLogNorm F)
    (continuous_ideleClassLogNorm (F := F)) hg
  have hcs0 : HasCompactSupport (fun x : C𝔽 ↦ g (ideleClassLogNorm F x).toAdd) := by
    have h := φ₀.property.2
    rwa [show (φ₀.val : C𝔽 → ℂ) = fun x ↦ g (ideleClassLogNorm F x).toAdd from
      funext hφ₀] at h
  have hcs : HasCompactSupport (fun x : C𝔽 ↦ (ψ x : ℂ) * g (ideleClassLogNorm F x).toAdd) :=
    hcs0.mul_left
  exact ⟨(⟨_, (mem_bruhatSmoothSubmodule_iff _).mpr hs, hcs⟩ :
    bruhatCompactSupportSubmodule C𝔽), fun _ ↦ rfl⟩

local notation "σ𝔽" => fun t : ℝ≥0ˣ ↦
  (QuotientGroup.mk (canonicalIdeleNormSection F t) : C𝔽)

private theorem mul_rearrange (a b c d : ℂ) : a * (b * d * c) = a * b * c * d := by ring

open Classical in
/-- Fourier–Mellin transform of a test function of the norm: it vanishes unless the
unitary character is trivial on the norm-one classes, and is then the volume of those
classes times a one-variable Mellin transform for `dt/t`. -/
private theorem normTest_mellin (g : ℝ → ℂ) (_hg : Continuous g) (φ : BruhatCompactSupport C𝔽)
    (hφ : ∀ x, φ.val x = g (Real.log ((ideleClassNorm F x : ℝ≥0) : ℝ)))
    (χ : PontryaginDual C𝔽) (s : ℂ) :
    modulatedFourierMellin m𝔽 univ hm𝔽 μ𝔽 φ.val (ideleClassNormTwist χ s) =
      (if ∀ u : C₁, χ u.val = 1 then classVolume else 0) *
        ∫ t, g (Real.log ((t : ℝ≥0) : ℝ)) * (χ (σ𝔽 t) : ℂ) * (((t : ℝ≥0) : ℝ) : ℂ) ^ s
          ∂positiveRealHaar := by
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ _
  let : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let : SFinite positiveRealHaar := by unfold positiveRealHaar; infer_instance
  let : CompactSpace C₁ := (ideleClassGroup_finiteness F).2.1
  let : (normOneIdeleClassTamagawaMeasure F).IsHaarMeasure :=
    (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  have hσ : Continuous σ𝔽 := continuous_quotient_mk'.comp (canonicalIdeleNormSection_continuous F)
  have hr : RightInverse σ𝔽 (ideleClassNorm F) := canonicalIdeleNormSection_rightInverse F
  have hM : modulatedFourierMellin m𝔽 univ hm𝔽 μ𝔽 φ.val (ideleClassNormTwist χ s) =
      ∫ x, φ.val x * ideleClassNormTwist χ s x ∂μ𝔽 := by
    simp only [modulatedFourierMellin, relativeVerticalStrip, preimage_univ, indicator_univ]
  have hφc : Continuous φ.val :=
    continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp φ.property.1)
  have hj : Continuous (fun p : ℝ≥0ˣ × C₁ ↦ σ𝔽 p.1 * p.2.val) :=
    (hσ.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  have hcont : Continuous (fun x ↦ φ.val x * ideleClassNormTwist χ s x) :=
    hφc.mul (map_continuous (ideleClassNormTwist χ s))
  rw [hM, ← classTamagawa_normProduct σ𝔽 hσ hr, integral_map hj.measurable.aemeasurable
    hcont.aestronglyMeasurable]
  let ψ₁ : PontryaginDual C₁ := χ.comp ⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩
  have hpt (p : ℝ≥0ˣ × C₁) : φ.val (σ𝔽 p.1 * p.2.val) * ideleClassNormTwist χ s (σ𝔽 p.1 * p.2.val) =
      g (Real.log ((p.1 : ℝ≥0) : ℝ)) * (χ (σ𝔽 p.1) : ℂ) * (((p.1 : ℝ≥0) : ℝ) : ℂ) ^ s *
        (ψ₁ p.2 : ℂ) := by
    have hn : ideleClassNorm F (σ𝔽 p.1 * p.2.val) = p.1 := by
      rw [map_mul, hr p.1, MonoidHom.mem_ker.mp p.2.property, mul_one]
    change φ.val _ * ((χ (σ𝔽 p.1 * p.2.val) : ℂ) *
      (((ideleClassNorm F (σ𝔽 p.1 * p.2.val) : ℝ≥0) : ℝ) : ℂ) ^ s) = _
    rw [hφ, hn, map_mul, Circle.coe_mul]
    exact mul_rearrange _ _ _ _
  simp_rw [hpt]
  refine (integral_prod_mul (μ := positiveRealHaar) (ν := normOneIdeleClassTamagawaMeasure F)
    (fun t : ℝ≥0ˣ ↦ g (Real.log ((t : ℝ≥0) : ℝ)) * (χ (σ𝔽 t) : ℂ) * (((t : ℝ≥0) : ℝ) : ℂ) ^ s)
    (fun u ↦ (ψ₁ u : ℂ))).trans ?_
  rw [integral_normOneCharacter, mul_comm]
  congr 1
  have hiff : ψ₁ = 1 ↔ ∀ u : C₁, χ u.val = 1 :=
    ⟨fun h u ↦ (DFunLike.congr_fun h u).trans (PontryaginDual.one_apply u),
      fun h ↦ ContinuousMonoidHom.ext fun u ↦ (h u).trans (PontryaginDual.one_apply u).symm⟩
  simp only [hiff]

private theorem grh_mul_twist (p q a b n : ℂ) (h : p = q * a) :
    p * (b * n) = q * (b * a * n) := by
  rw [h]; ring

open Classical in
private theorem characterNormTest_mellin (g : ℝ → ℂ) (hg : ContDiff ℝ (∞) g)
    (hgc : HasCompactSupport g)
    (ψ : PontryaginDual C𝔽) (φ : BruhatCompactSupport C𝔽)
    (hφ : ∀ x, φ.val x = (ψ x : ℂ) * g (Real.log ((ideleClassNorm F x : ℝ≥0) : ℝ)))
    (χ : PontryaginDual C𝔽) (s : ℂ) :
    modulatedFourierMellin m𝔽 univ hm𝔽 μ𝔽 φ.val (ideleClassNormTwist χ s) =
      (if ∀ u : C₁, (χ * ψ) u.val = 1 then classVolume else 0) *
        ∫ t, g (Real.log ((t : ℝ≥0) : ℝ)) * ((χ * ψ) (σ𝔽 t) : ℂ) * (((t : ℝ≥0) : ℝ) : ℂ) ^ s
          ∂positiveRealHaar := by
  obtain ⟨φr, hφr⟩ := exists_normTest (F := F) g hg hgc
  rw [← normTest_mellin g hg.continuous φr hφr (χ * ψ) s]
  simp only [modulatedFourierMellin, relativeVerticalStrip, preimage_univ, indicator_univ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  change φ.val x * ((χ x : ℂ) * (((ideleClassNorm F x : ℝ≥0) : ℝ) : ℂ) ^ s) =
    φr.val x * (((χ * ψ) x : ℂ) * (((ideleClassNorm F x : ℝ≥0) : ℝ) : ℂ) ^ s)
  rw [show (((χ * ψ) x : Circle) : ℂ) = (χ x : ℂ) * (ψ x : ℂ) from Circle.coe_mul _ _]
  exact grh_mul_twist _ _ _ _ _ ((hφ x).trans ((congrArg _ (hφr x)).symm.trans (mul_comm _ _)))


/-- The exponential map from the reals to the positive real units. -/
private noncomputable def grhExp (x : ℝ) : ℝ≥0ˣ :=
  Units.mk0 (Real.exp x).toNNReal (Real.toNNReal_pos.mpr (Real.exp_pos x)).ne'

private theorem grhExp_val (x : ℝ) : (((grhExp x : ℝ≥0ˣ) : ℝ≥0) : ℝ) = Real.exp x :=
  Real.coe_toNNReal _ (Real.exp_pos x).le

private theorem integral_positiveRealHaar_eq {f : ℝ≥0ˣ → ℂ} (hf : Continuous f) :
    ∫ t, f t ∂positiveRealHaar = ∫ x : ℝ, f (grhExp x) := by
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ _
  have he : Measurable grhExp :=
    measurable_comap_iff.mpr (continuous_real_toNNReal.comp Real.continuous_exp).measurable
  exact integral_map he.aemeasurable hf.aestronglyMeasurable

private theorem grh_cpow_exp (x : ℝ) (w : ℂ) :
    ((Real.exp x : ℝ) : ℂ) ^ w = Complex.exp (w * x) := by
  rw [Complex.ofReal_exp, Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
    Complex.log_exp (by simp [Real.pi_pos]) (by simp [Real.pi_pos.le]), mul_comm]

/-- The shifted radial integral against `t ^ w`, in logarithmic coordinates. -/
private theorem grh_shift_integral (H : ℝ → ℂ) (hH : Continuous H) (c : ℝ≥0ˣ → ℂ)
    (hc : ∀ t, c t = 1) (y : ℝ) (w : ℂ) :
    ∫ t, H (Real.log ((t : ℝ≥0) : ℝ) - y) * c t * (((t : ℝ≥0) : ℝ) : ℂ) ^ w
        ∂positiveRealHaar =
      Complex.exp (w * y) * ∫ x : ℝ, H x * Complex.exp (w * x) := by
  have h1 : (fun t : ℝ≥0ˣ ↦ H (Real.log ((t : ℝ≥0) : ℝ) - y) * c t *
      (((t : ℝ≥0) : ℝ) : ℂ) ^ w) =
      fun t : ℝ≥0ˣ ↦ H (Real.log ((t : ℝ≥0) : ℝ) - y) * (((t : ℝ≥0) : ℝ) : ℂ) ^ w := by
    funext t; rw [hc t, mul_one]
  have hpos : Continuous (fun t : ℝ≥0ˣ ↦ ((t : ℝ≥0) : ℝ)) :=
    NNReal.continuous_coe.comp Units.continuous_val
  have hcont : Continuous (fun t : ℝ≥0ˣ ↦ H (Real.log ((t : ℝ≥0) : ℝ) - y) *
      (((t : ℝ≥0) : ℝ) : ℂ) ^ w) := by
    refine (hH.comp ((hpos.log fun t ↦ (nnrealUnits_coe_pos t).ne').sub continuous_const)).mul
      ((Complex.continuous_ofReal.comp hpos).cpow continuous_const fun t ↦
        Complex.ofReal_mem_slitPlane.mpr (nnrealUnits_coe_pos t))
  rw [h1, integral_positiveRealHaar_eq hcont]
  simp only [grhExp_val, Real.log_exp, grh_cpow_exp]
  calc ∫ x : ℝ, H (x - y) * Complex.exp (w * x)
      = ∫ x : ℝ, H (x - y) * Complex.exp (w * (((x - y : ℝ) : ℂ) + y)) := by
        congr 1; funext x; push_cast; ring_nf
    _ = ∫ x : ℝ, H x * Complex.exp (w * (x + y)) :=
        integral_sub_right_eq_self (μ := volume) (fun x : ℝ ↦ H x * Complex.exp (w * (x + y))) y
    _ = _ := by
        rw [← integral_const_mul]; congr 1; funext x; rw [mul_add, Complex.exp_add]; ring

/-- A character trivial on the norm section is determined by its restriction to `C¹`. -/
private theorem grh_character_eq (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    {χ χ₀ : PontryaginDual C𝔽} (h1 : ∀ t, χ (τ t) = 1) (h0 : ∀ t, χ₀ (τ t) = 1)
    (hC : ∀ u : C₁, (χ * χ₀⁻¹) u.val = 1) : χ = χ₀ := by
  refine ContinuousMonoidHom.ext fun x ↦ ?_
  let t := ideleClassNorm F x
  have hu : (τ t)⁻¹ * x ∈ C₁ := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hτ t, inv_mul_cancel]
  have key : ∀ ψ : PontryaginDual C𝔽, (∀ t, ψ (τ t) = 1) → ψ x = ψ ((τ t)⁻¹ * x) :=
    fun ψ hψ ↦ by rw [map_mul, map_inv, hψ, inv_one, one_mul]
  have h := hC ⟨_, hu⟩
  change χ ((τ t)⁻¹ * x) * (χ₀ ((τ t)⁻¹ * x))⁻¹ = 1 at h
  exact (key χ h1).trans ((mul_inv_eq_one.mp h).trans (key χ₀ h0).symm)



private theorem grh_classVolume_ne_zero : classVolume ≠ 0 := by
  have hvol := normOneIdeleClassTamagawaMeasure_volume (F := F)
  have hc0 : normOneIdeleClassTamagawaMeasure F univ ≠ 0 := by
    rw [hvol, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    have := NumberField.Units.regulator_pos F
    have := NumberField.classNumber_pos F
    have := NumberField.Units.torsionOrder_pos F
    have : (0 : ℝ) < Real.sqrt (Int.natAbs (NumberField.discr F) : ℝ) :=
      Real.sqrt_pos.mpr (by exact_mod_cast Int.natAbs_pos.mpr (NumberField.discr_ne_zero F))
    positivity
  have hct : normOneIdeleClassTamagawaMeasure F univ ≠ ⊤ := by
    rw [hvol]; exact ENNReal.ofReal_ne_top
  exact Complex.ofReal_ne_zero.mpr (ENNReal.toReal_ne_zero.mpr ⟨hc0, hct⟩)

/-- The positive part of the divisor of the continued completed Hecke L-function has no
accumulation point. -/
private theorem grh_zeros_discrete (χ : PontryaginDual C𝔽) (z : ℂ) :
    ∀ᶠ u in 𝓝[≠] z, ¬ 0 < ord(χ, u + 1 / 2) := by
  have hD :=
    (MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ).eq_zero_codiscreteWithin
  have h := (mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp hD) (z + 1 / 2) (mem_univ _)
  rw [compl_univ, union_empty] at h
  have ht : Tendsto (fun u : ℂ ↦ u + 1 / 2) (𝓝[≠] z) (𝓝[≠] (z + 1 / 2)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact ((continuous_id.add continuous_const).tendsto z).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with u hu
      exact fun h' ↦ hu (add_right_cancel h')
  filter_upwards [ht.eventually h] with u hu
  change _ = (0 : ℤ) at hu
  rw [hu]; exact lt_irrefl 0

private theorem grh_zero_re_le_one (χ : PontryaginDual C𝔽) {s : ℂ} (hs : 0 < ord(χ, s)) :
    s.re ≤ 1 := by
  rcases le_or_gt s.re 0 with h | h
  · linarith
  · have hspec := continuedCompletedHeckeL_spec χ
    rw [MeromorphicOn.divisor_apply hspec.1.meromorphicOn (mem_univ s)] at hs
    have ho : 0 < meromorphicOrderAt (continuedCompletedHeckeL χ) s := by
      by_contra hle
      rw [not_lt] at hle
      obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp
        (ne_top_of_le_ne_top (WithTop.coe_ne_top (a := (0 : ℤ))) hle)
      rw [← hn, WithTop.untop₀_coe] at hs
      rw [← hn] at hle
      exact absurd (WithTop.coe_le_coe.mp hle) (not_le.mpr hs)
    exact (completedHeckeL_continuation_zeros χ _ hspec.1 hspec.2 h ho).le


private theorem grh_bump_mul_exp (b w : ℂ) : b * Complex.exp (-w) * Complex.exp w = b := by
  rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]

open Classical in
/-- Paper: Theorem 12.5.1.1, pp. 519–520, and §1.4, p. 30. If, for one half-width α, the
exterior zero terms of every test vanishing on the norm-one classes sum to zero, then no
completed Hecke L-function of a character trivial on the norm section has a zero with
|Re s − 1/2| ≥ α. The test χ̄₀ · h(log|·| − y) isolates one L-function and turns the hypothesis
into the vanishing of an exponential sum on a half-line, whose coefficients must then vanish
(`eq_zero_of_hasSum_exp_eq_zero`). -/
theorem isEmpty_exteriorZeros_of_hasSum (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) (α : ℝ)
    (hT : ∀ φ : BruhatCompactSupport C𝔽, (∀ g : C₁, φ.val g = 0) →
      HasSum (fun z : exteriorZeros(τ, α) ↦ zeroTerm(φ, z)) 0) :
    IsEmpty exteriorZeros(τ, α) := by
  by_contra hne
  obtain ⟨z₀⟩ := not_isEmpty_iff.mp hne
  let χ₀ : PontryaginDual C𝔽 := z₀.val.1.val
  let w₀ : ℂ := z₀.val.2 - 1 / 2
  let β : ContDiffBump (1 / 2 : ℝ) := ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩
  let H₀ : ℝ → ℂ := fun x ↦ (β x : ℂ) * Complex.exp (-(w₀ * x))
  have hH₀ : ContDiff ℝ (∞) H₀ :=
    (Complex.ofRealCLM.contDiff.comp β.contDiff).mul
      (Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff).neg)
  have hH₀c : HasCompactSupport H₀ :=
    (β.hasCompactSupport.comp_left Complex.ofReal_zero).mul_right
  have hH₀neg : ∀ x : ℝ, x ≤ 0 → H₀ x = 0 := fun x hx ↦ by
    have : β x = 0 := β.zero_of_le_dist (by
      rw [Real.dist_eq, abs_of_neg (by linarith)]; change (1 / 4 : ℝ) ≤ _; linarith)
    simp only [H₀, this, Complex.ofReal_zero, zero_mul]
  have hg (y : ℝ) : ContDiff ℝ (∞) (fun x ↦ H₀ (x - y)) := hH₀.comp (contDiff_id.sub contDiff_const)
  have hgc (y : ℝ) : HasCompactSupport (fun x ↦ H₀ (x - y)) :=
    hH₀c.comp_homeomorph (Homeomorph.subRight y)
  choose φ hφ using fun y : ℝ ↦ exists_characterNormTest (F := F) χ₀⁻¹ _ (hg y) (hgc y)
  have hvan (y : ℝ) (hy : 0 ≤ y) : ∀ g : C₁, (φ y).val g = 0 := fun g ↦ by
    rw [hφ y, MonoidHom.mem_ker.mp g.property, Units.val_one, NNReal.coe_one, Real.log_one,
      zero_sub, hH₀neg _ (by linarith), mul_zero]
  let K : ℂ → ℂ := fun w ↦ ∫ x : ℝ, H₀ x * Complex.exp (w * x)
  -- the zero terms of the test `φ y`
  have hzt (y : ℝ) (z : exteriorZeros(τ, α)) : zeroTerm(φ y, z) =
      if z.val.1.val = χ₀ then ((ord(z.val.1.val, z.val.2) : ℤ) : ℂ) *
        (classVolume * K (z.val.2 - 1 / 2)) * Complex.exp ((z.val.2 - 1 / 2) * y) else 0 := by
    rw [characterNormTest_mellin _ (hg y) (hgc y) χ₀⁻¹ (φ y) (hφ y)]
    by_cases hχ : z.val.1.val = χ₀
    · have hone : z.val.1.val * χ₀⁻¹ = 1 := by rw [hχ, mul_inv_cancel]
      rw [ite_eq_left hχ, ite_eq_left (fun u ↦ by rw [hone]; rfl)]
      beta_reduce
      rw [grh_shift_integral H₀ hH₀.continuous _ (fun t ↦ by rw [hone]; rfl) y]
      ring
    · rw [ite_eq_right hχ, ite_eq_right (fun h1 ↦ hχ (grh_character_eq τ hτ z.val.1.property
        z₀.val.1.property h1)), zero_mul, mul_zero]
  let ι := {z : exteriorZeros(τ, α) // z.val.1.val = χ₀}
  let w : ι → ℂ := fun i ↦ i.val.val.2 - 1 / 2
  let b : ι → ℂ := fun i ↦
    ((ord(i.val.val.1.val, i.val.val.2) : ℤ) : ℂ) * (classVolume * K (w i))
  have hsum (y : ℝ) (hy : 0 ≤ y) : HasSum (fun i : ι ↦ b i * Complex.exp (w i * y)) 0 := by
    have h := hT (φ y) (hvan y hy)
    have hsupp : Function.support (fun z : exteriorZeros(τ, α) ↦ zeroTerm(φ y, z)) ⊆
        {z | z.val.1.val = χ₀} := by
      intro z hz
      by_contra hχ
      exact hz ((hzt y z).trans (ite_eq_right hχ))
    have h' := (hasSum_subtype_iff_of_support_subset hsupp).mpr h
    have hf : (fun i : ι ↦ b i * Complex.exp (w i * y)) =
        (fun z : exteriorZeros(τ, α) ↦ zeroTerm(φ y, z)) ∘ (Subtype.val : ι → _) := by
      funext i
      rw [Function.comp_apply, hzt y i.val, ite_eq_left i.property]
    rw [hf]
    exact h'
  have hw : Function.Injective w := fun i j hij ↦ by
    have hs : i.val.val.2 = j.val.val.2 := sub_left_inj.mp hij
    exact Subtype.ext (Subtype.ext (Prod.ext (Subtype.ext (i.property.trans j.property.symm)) hs))
  have hdisc : ∀ z : ℂ, ∀ᶠ u in 𝓝[≠] z, u ∉ Set.range w := fun z ↦ by
    filter_upwards [grh_zeros_discrete χ₀ z] with u hu
    rintro ⟨i, rfl⟩
    apply hu
    have h := i.val.property.1
    rw [i.property] at h
    rwa [sub_add_cancel]
  have hre : ∀ i, (w i).re ≤ 1 / 2 := fun i ↦ by
    have h := grh_zero_re_le_one _ i.val.property.1
    change (i.val.val.2 - 1 / 2).re ≤ 1 / 2
    rw [Complex.sub_re]
    norm_num
    linarith
  have hb : Summable b := by
    have h := (hsum 0 le_rfl).summable
    simpa using h
  have h0 := eq_zero_of_hasSum_exp_eq_zero w b hw hdisc hre hb hsum ⟨z₀, rfl⟩
  have hK : K w₀ = ((∫ x, β x : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x ↦ grh_bump_mul_exp _ _)
  have hord : ((ord(χ₀, z₀.val.2) : ℤ) : ℂ) ≠ 0 := Int.cast_ne_zero.mpr z₀.property.1.ne'
  have hKne : K w₀ ≠ 0 := by
    rw [hK]; exact Complex.ofReal_ne_zero.mpr β.integral_pos.ne'
  exact mul_ne_zero hord (mul_ne_zero grh_classVolume_ne_zero hKne) h0

/-- Paper: Theorem 12.5.1.1, pp. 519–520, and §1.4, p. 30. For each half-width α, the
conclusion of `traceFormula_exteriorZeros` holds for every test vanishing on the norm-one classes
exactly when no completed Hecke L-function of a character trivial on the norm section has a zero
with |Re s − 1/2| ≥ α. So the gap `traceFormula_exteriorZeros`, for all α > 0, is equivalent to
GRH for these functions. -/
theorem hasSum_exteriorZeros_iff_isEmpty (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) (α : ℝ) :
    (∀ φ : BruhatCompactSupport C𝔽, (∀ g : C₁, φ.val g = 0) →
      HasSum (fun z : exteriorZeros(τ, α) ↦ zeroTerm(φ, z)) 0) ↔
      IsEmpty exteriorZeros(τ, α) :=
  ⟨isEmpty_exteriorZeros_of_hasSum τ hτ α, fun h _ _ ↦ by
    have := h
    exact hasSum_empty⟩

end NormTests

end ExteriorZerosGRH

end RiemannMasullo
