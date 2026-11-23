module

public import RiemannMasullo.Ch10_TraceSpectral.Sec3
public import Mathlib.Analysis.Normed.Module.Bases
public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Analysis.LocallyConvex.WeakSpace
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
public import Mathlib.Topology.Algebra.Module.Spaces.WeakBilin
public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
public import Mathlib.Topology.Compactness.Compact
import all RiemannMasullo.AppA_AlgebraicNT.Sec3
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.SpecificLimits.Basic
import RiemannMasullo.Ch10_TraceSpectral.Sec1
import all RiemannMasullo.Ch10_TraceSpectral.Sec3
import all RiemannMasullo.AppC_LCTVS.Sec3a
import all RiemannMasullo.AppC_LCTVS.Sec3a_part2
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import all RiemannMasullo.Ch09_HardySobolev.Sec3

/-!
# Spectral and geometric truncations

Masullo, §§10.4.1–10.4.2, pp. 455–464. The operators act on the compact-interval
Hardy–Sobolev space. Its spectral quotient is represented by the orthogonal
complement of the closed weighted theta subspace.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

section Truncations

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" =>
  (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "logNorm" => (fun g : C𝔽 ↦ Real.log ((ideleClassNorm F g).val : ℝ))
local notation "hStrip(" hα ")" => (neg_nonpos.mpr hα |>.trans hα)
local notation "W(" α ", " s ")" => CompactIntervalSobolev μ𝔽 logNorm (-α) α s
local notation "Θ(" a ", " hα ", " hs ")" => globalThetaSobolev F a (hStrip(hα)) hs
local notation "H(" a ", " hα ", " hs ")" => spectralSobolevQuotient F a (hStrip(hα)) hs

variable (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)

local notation "W₀" => W(α, s)
local notation "Θ₀" => Θ(a, hα, hs)
local notation "H₀" => H(a, hα, hs)
local notation "Qₐ" => (Θ₀).mkQL
local notation "A(" φ ")" => hardySobolevTestAction μ𝔽 m𝔽 (-α) α s (hStrip(hα)) hs φ
local notation "Aₛ(" φ ")" => spectralConvolution (F := F) a (hStrip(hα)) hs φ
local notation "M(" hρ ")" => modulatedCutoffOperator m𝔽
  ((μ𝔽).withDensity fun g ↦ ENNReal.ofReal (intervalSobolevDensity (-α) α s (logNorm g))) hρ

-- Use the same norm-generated locally convex structure as in §10.3.
attribute [local instance] instSpectralQuotientPolynormableSec3

local notation "quotientNuclear(" φ ")" => IsNuclearOperator (E := H₀) (F := H₀) (Aₛ(φ))

-- On p. 455 the introduction calls the range of a smooth cutoff multiplier closed.
-- A profile tending continuously to zero at the edge of its support need not
-- have closed multiplier range. Taking its closure is an additional operation.

/-- Paper: Definition 10.4.1.1(1), p. 456. The geometric projection is the
orthogonal projector onto the closed weighted theta subspace.
Deviation: The projector exists for every real twist, as used in Definition 10.4.1.3. -/
def geometricProjection : W₀ →L[ℂ] W₀ :=
  (Θ₀).starProjection

/-- Paper: Definition 10.4.1.1(2), p. 456. The spectral projection is the
orthogonal projector onto the complement of the closed weighted theta subspace.
Deviation: The projector exists for every real twist, as used in Definition 10.4.1.3. -/
def spectralProjection : W₀ →L[ℂ] W₀ :=
  (Θ₀).orthogonal.starProjection

local notation "Pgeom" => geometricProjection (F := F) a hα hs
local notation "Pspec" => spectralProjection (F := F) a hα hs

/-- Helper for `geometricTruncation_apply_of_mem` and `spectralTruncation_apply_of_mem`. -/
private theorem w18_comp_apply_of_fix {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T P : E →L[ℂ] E) (u : E) (h : P u = u) : (T.comp P) u = T u := by
  simp [h]

/-- Helper for the truncated convolutions. -/
private theorem w18_comp_comp_apply_of_fix {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T P A : E →L[ℂ] E) (u : E) (h : P (A u) = A u) : ((T.comp P).comp A) u = T (A u) := by
  simp [h]

/-- Helper for the restrictions. -/
private theorem w18_comp_comp_apply_of_fix' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T P A : E →L[ℂ] E) (u : E) (h : P u = u) : (T.comp (A.comp P)) u = T (A u) := by
  simp [h]

/-- Helper for `geometricTruncation_add_spectralTruncation`. -/
private theorem w18_comp_add_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T P Q : E →L[ℂ] E) (h : ∀ u, P u + Q u = u) : T.comp P + T.comp Q = T := by
  ext u
  simp [← map_add, h]

/-- Paper: Definition 10.4.1.1(1), p. 456. The geometric projector fixes each
vector in the theta subspace. -/
theorem geometricProjection_apply_of_mem {u : W₀} (_hu : u ∈ Θ₀) :
    Pgeom u = u :=
  (Θ₀).starProjection_eq_self_iff.2 _hu

/-- Paper: Definition 10.4.1.1(2), p. 456. The spectral projector fixes each
vector orthogonal to the theta subspace. -/
theorem spectralProjection_apply_of_mem {u : W₀} (_hu : u ∈ (Θ₀).orthogonal) :
    Pspec u = u := by
  exact Submodule.starProjection_eq_self_iff.mpr _hu

/-- Paper: Lemma 10.4.1.2, p. 456. The spectral projection preserves the
quotient class of every vector. -/
theorem spectralQuotient_comp_spectralProjection (_ha : 0 < a) :
    (Qₐ).comp Pspec = Qₐ :=
  ContinuousLinearMap.ext fun u ↦ ((Submodule.Quotient.eq (Θ₀)).2 (by
    have h : u - Pspec u = (Θ₀).starProjection u :=
      sub_eq_of_eq_add ((Θ₀).starProjection_add_starProjection_orthogonal u).symm
    exact (congrArg (· ∈ Θ₀) h).mpr ((Θ₀).starProjection_apply_mem u))).symm

/-- Paper: Lemma 10.4.1.2, p. 456. The geometric projection has zero
composition with the quotient map. -/
theorem spectralQuotient_comp_geometricProjection (_ha : 0 < a) :
    (Qₐ).comp Pgeom = 0 :=
  ContinuousLinearMap.ext fun u ↦
    (Submodule.Quotient.mk_eq_zero (Θ₀)).2 ((Θ₀).starProjection_apply_mem u)

/-- Paper: Lemma 10.4.1.2, p. 456. The spectral projection of any representative
is the unique orthogonal representative, canonically isometric to the quotient
via Mathlib's quotient equivalence. -/
theorem spectralQuotient_orthogonalRepresentative (_ha : 0 < a) (u : W₀) :
    let v := (Θ₀).quotientEquivOrthogonal (Qₐ u)
    (v : W₀) = Pspec u ∧
      ∀ w : (Θ₀).orthogonal, Qₐ w = Qₐ u → w = v := by
  intro v
  have hu : Qₐ u = Qₐ (Pspec u) := (Submodule.Quotient.eq (Θ₀)).2 (by
    have h : u - Pspec u = (Θ₀).starProjection u :=
      sub_eq_of_eq_add ((Θ₀).starProjection_add_starProjection_orthogonal u).symm
    exact (congrArg (· ∈ Θ₀) h).mpr ((Θ₀).starProjection_apply_mem u))
  have hv : v = ⟨Pspec u, (Θ₀).orthogonal.starProjection_apply_mem u⟩ :=
    (congrArg (Θ₀).quotientEquivOrthogonal hu).trans
      ((Θ₀).quotientEquivOrthogonal_mk _ ((Θ₀).orthogonal.starProjection_apply_mem u))
  exact ⟨congrArg Subtype.val hv, fun w hw ↦
    ((Θ₀).quotientEquivOrthogonal_mk (w : W₀) w.2).symm.trans
      (congrArg (Θ₀).quotientEquivOrthogonal hw)⟩

variable {Λ ε : ℝ} {ρ : IdeleClassGroup (𝓞 F) F → ℝ}
local notation "innerBand" => (0 < Λ⁻¹ + ε ∧ Λ⁻¹ + ε < Λ - ε)

/-- Paper: Definition 10.4.1.3(1), p. 457. Geometric truncation first projects
onto theta and then multiplies by the cutoff.
Deviation: The cutoff is real as in Definition 9.3.3.1 in Lean. The operator is
defined whenever the cutoff exists, including outside the stated inner-band condition. -/
def geometricTruncation (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) : W₀ →L[ℂ] W₀ :=
  (M(hρ)).comp Pgeom

/-- Paper: Definition 10.4.1.3(1), p. 457. The geometric truncation of
convolution applies the geometric truncation operator after convolution. -/
def geometricTruncatedConvolution (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) (φ : BruhatCompactSupport C𝔽) :
    W₀ →L[ℂ] W₀ :=
  (geometricTruncation a hα hs hρ).comp (A(φ))

/-- Paper: Definition 10.4.1.3(2), p. 457. Spectral truncation first projects
onto the orthogonal complement of theta and then multiplies by the cutoff.
Deviation: As for geometric truncation, a real cutoff suffices to define the operator. -/
def spectralTruncation (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) : W₀ →L[ℂ] W₀ :=
  (M(hρ)).comp Pspec

/-- Paper: Definition 10.4.1.3(2), p. 457. The spectral truncation of
convolution applies the spectral truncation operator after convolution. -/
def spectralTruncatedConvolution (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) (φ : BruhatCompactSupport C𝔽) :
    W₀ →L[ℂ] W₀ :=
  (spectralTruncation a hα hs hρ).comp (A(φ))

/-- Paper: Definition 10.4.1.3(1), p. 457. On the theta subspace, geometric
truncation acts by multiplication by the cutoff. -/
theorem geometricTruncation_apply_of_mem (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) {u : W₀} (_hu : u ∈ Θ₀) :
    geometricTruncation a hα hs hρ u = M(hρ) u :=
  w18_comp_apply_of_fix _ _ _ (Submodule.starProjection_eq_self_iff.mpr _hu)

/-- Paper: Definition 10.4.1.3(2), p. 457. On the orthogonal complement of
theta, spectral truncation acts by multiplication by the cutoff. -/
theorem spectralTruncation_apply_of_mem (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) {u : W₀} (_hu : u ∈ (Θ₀).orthogonal) :
    spectralTruncation a hα hs hρ u = M(hρ) u :=
  w18_comp_apply_of_fix _ _ _ (Submodule.starProjection_eq_self_iff.mpr _hu)

/-- Paper: Definition 10.4.1.3(1), p. 457. If an input's convolution belongs
to theta, its geometric truncated convolution is just cutoff multiplication of the result. -/
theorem geometricTruncatedConvolution_apply_of_mem (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) (φ : BruhatCompactSupport C𝔽)
    {u : W₀} (_hu : A(φ) u ∈ Θ₀) :
    geometricTruncatedConvolution a hα hs hρ φ u = M(hρ) (A(φ) u) :=
  w18_comp_comp_apply_of_fix _ _ _ _ (Submodule.starProjection_eq_self_iff.mpr _hu)

/-- Paper: Definition 10.4.1.3(2), p. 457. If an input's convolution is
orthogonal to theta, its spectral truncated convolution is cutoff multiplication of the result. -/
theorem spectralTruncatedConvolution_apply_of_mem (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) (φ : BruhatCompactSupport C𝔽)
    {u : W₀} (_hu : A(φ) u ∈ (Θ₀).orthogonal) :
    spectralTruncatedConvolution a hα hs hρ φ u = M(hρ) (A(φ) u) :=
  w18_comp_comp_apply_of_fix _ _ _ _ (Submodule.starProjection_eq_self_iff.mpr _hu)

/-- Paper: Remark 10.4.1.4, p. 457. The two truncation operators add up to
multiplication by the common cutoff. -/
theorem geometricTruncation_add_spectralTruncation (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) :
    geometricTruncation a hα hs hρ + spectralTruncation a hα hs hρ = M(hρ) :=
  w18_comp_add_comp _ _ _ fun u ↦ Submodule.starProjection_add_starProjection_orthogonal u


/-- An L² indicator represents a set whose mass is the squared norm. -/
private theorem hardySobolevTranslation_zeroBase_powers_unbounded_indicator_mass (X : Type*) [MeasurableSpace X] (ν : Measure X)
    (A : Set X) (hA : MeasurableSet A) (u : Lp ℂ 2 ν)
    (hu : (u : X → ℂ) =ᵐ[ν] A.indicator (fun _ ↦ (1 : ℂ))) :
    ν A = ENNReal.ofReal (‖u‖ ^ 2) := by
  have hnorm : eLpNorm (u : X → ℂ) 2 ν = (ν A) ^ (1 / 2 : ℝ) := by
    rw [eLpNorm_congr_ae hu, eLpNorm_indicator_const hA.nullMeasurableSet (by norm_num) (by norm_num)]
    simp
  have hsq : ((ν A) ^ (1 / 2 : ℝ)) ^ 2 = ν A := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  calc
    ν A = (eLpNorm (u : X → ℂ) 2 ν) ^ 2 := by rw [hnorm, hsq]
    _ = ENNReal.ofReal (‖u‖ ^ 2) := by
      rw [ENNReal.ofReal_pow (norm_nonneg u), Lp.norm_def,
        ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top u)]

/-- Powers of a log-norm-one element give a quadratic lower bound for translated weighted mass. -/
private theorem hardySobolevTranslation_zeroBase_powers_unbounded_lower
    (G : Type*) [Group G] [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [μ.IsMulLeftInvariant] (l : G → ℝ)
    (hlmul : ∀ x y, l (x * y) = l x + l y) (g : G)
    (hlpow : ∀ k : ℕ, l (g ^ k) = (k : ℝ))
    (n : ℕ) (hn : 0 < n) (A : Set G) (hA : MeasurableSet A)
    (hleft : ∀ x ∈ A, -1 ≤ l x) (k : ℕ) (hk : 1 ≤ k) :
    ENNReal.ofReal (((k : ℝ) - 1) ^ 2) * μ A ≤
      (μ.withDensity (fun x ↦ ENNReal.ofReal ((1 + (l x) ^ 2) ^ n)))
        ((fun x ↦ (g ^ k)⁻¹ * x) ⁻¹' A) := by
  let B := (fun x ↦ (g ^ k)⁻¹ * x) ⁻¹' A
  have hB : MeasurableSet B := hA.preimage (measurable_const_mul _)
  have hmass : μ B = μ A := measure_preimage_mul μ (g ^ k)⁻¹ A
  change _ ≤ (μ.withDensity (fun x ↦ ENNReal.ofReal ((1 + (l x) ^ 2) ^ n))) B
  rw [withDensity_apply _ hB]
  calc
    ENNReal.ofReal (((k : ℝ) - 1) ^ 2) * μ A = ∫⁻ x in B, ENNReal.ofReal (((k : ℝ) - 1) ^ 2) ∂μ := by simp [hmass]
    _ ≤ ∫⁻ x in B, ENNReal.ofReal ((1 + (l x) ^ 2) ^ n) ∂μ := by
      apply lintegral_mono_ae
      apply ae_restrict_of_forall_mem hB
      intro x hx
      apply ENNReal.ofReal_le_ofReal
      have hx' : -1 ≤ l ((g ^ k)⁻¹ * x) := hleft _ hx
      have heq : l x = (k : ℝ) + l ((g ^ k)⁻¹ * x) := by
        rw [← hlpow, ← hlmul]
        simp
      have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
      have hbase : 1 ≤ 1 + (l x) ^ 2 := by nlinarith [sq_nonneg (l x)]
      have hpower : 1 + (l x) ^ 2 ≤ (1 + (l x) ^ 2) ^ n := le_self_pow₀ hbase hn.ne'
      nlinarith

/-- A bounded log-norm band has controlled weighted mass. -/
private theorem hardySobolevTranslation_zeroBase_powers_unbounded_upper
    (G : Type*) [MeasurableSpace G] (μ : Measure G) (l : G → ℝ)
    (n : ℕ) (A : Set G) (hA : MeasurableSet A) (hband : ∀ x ∈ A, |l x| ≤ 1) :
    (μ.withDensity (fun x ↦ ENNReal.ofReal ((1 + (l x) ^ 2) ^ n))) A ≤
      ENNReal.ofReal (2 ^ n : ℝ) * μ A := by
  rw [withDensity_apply _ hA]
  calc
    (∫⁻ x in A, ENNReal.ofReal ((1 + (l x) ^ 2) ^ n) ∂μ) ≤ ∫⁻ x in A, ENNReal.ofReal (2 ^ n : ℝ) ∂μ := by
      apply lintegral_mono_ae
      apply ae_restrict_of_forall_mem hA
      intro x hx
      apply ENNReal.ofReal_le_ofReal
      have hb := abs_le.mp (hband x hx)
      exact pow_le_pow_left₀ (by positivity) (by nlinarith [sq_nonneg (l x)]) n
    _ = _ := by simp

/-- A proper modulus has a compact positive-mass log band with finite weighted mass. -/
private theorem hardySobolevTranslation_zeroBase_powers_unbounded_band
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (m : G →ₜ* ℝ≥0ˣ) (hm : IsProperMap m) (n : ℕ) :
    ∃ A : Set G, MeasurableSet A ∧ μ A ≠ 0 ∧ μ A ≠ ⊤ ∧
      (∀ x ∈ A, |Real.log ((m x).val : ℝ)| ≤ 1) ∧
      (μ.withDensity (fun x ↦ ENNReal.ofReal ((1 + (Real.log ((m x).val : ℝ)) ^ 2) ^ n))) A ≠ ⊤ := by
  let e : ℝ≥0ˣ ≃ₜ ℝ := (Nonneg.unitsHomeomorphPos ℝ).trans Real.expOrderIso.symm.toHomeomorph
  have he (t : ℝ≥0ˣ) : e t = Real.log (t.val : ℝ) := (Real.log_of_pos (NNReal.coe_pos.mpr t.zero_lt)).symm
  let l : G → ℝ := fun x ↦ Real.log ((m x).val : ℝ)
  let A : Set G := l ⁻¹' Icc (-1) 1
  have hl : Continuous l := by simpa [l, Function.comp_def, he] using e.continuous.comp m.continuous
  have hcompact : IsCompact A := by
    have hh := (e.isProperMap.comp hm).isCompact_preimage (isCompact_Icc (a := (-1 : ℝ)) (b := 1))
    simpa only [Function.comp_def, he] using hh
  have hA : MeasurableSet A := hcompact.measurableSet
  have hmass : μ A ≠ 0 := by
    have hU : IsOpen (l ⁻¹' Ioo (-1) 1) := isOpen_Ioo.preimage hl
    have hnonempty : (l ⁻¹' Ioo (-1) 1).Nonempty := ⟨1, by simp [l]⟩
    intro hzero
    exact hU.measure_ne_zero μ hnonempty (measure_mono_null (preimage_mono Ioo_subset_Icc_self) hzero)
  have hband (x : G) (hx : x ∈ A) : |l x| ≤ 1 := abs_le.mpr hx
  have hfinite : μ A ≠ ⊤ := hcompact.measure_lt_top.ne
  refine ⟨A, hA, hmass, hfinite, hband, ?_⟩
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite)
    (hardySobolevTranslation_zeroBase_powers_unbounded_upper G μ l n A hA hband)

/-- A polynomial log weight makes translation powers unbounded in operator norm. -/
private theorem hardySobolevTranslation_zeroBase_powers_unbounded_weighted
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (m : G →ₜ* ℝ≥0ˣ) (hm : IsProperMap m)
    (n : ℕ) (hn : 0 < n) (g : G) (hg : Real.log ((m g).val : ℝ) = 1)
    (d : G → ENNReal) (hd : Measurable d)
    (hdeq : ∀ x, d x = ENNReal.ofReal ((1 + (Real.log ((m x).val : ℝ)) ^ 2) ^ n)) :
    let ν := μ.withDensity d
    ∀ (T : G →* (Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν)),
      (∀ h u, (T h u : G → ℂ) =ᵐ[μ] fun x ↦ u (h⁻¹ * x)) →
      ∀ C : ℝ, ∃ k : ℕ, C < ‖T (g ^ k)‖ := by
  intro ν T hT C
  classical
  let l : G → ℝ := fun x ↦ Real.log ((m x).val : ℝ)
  have hl : Measurable l := Real.measurable_log.comp
    (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)).measurable
  have hdensity : d = (fun x ↦ ENNReal.ofReal ((1 + (l x) ^ 2) ^ n)) := funext hdeq
  have hpos (x : G) : 0 < (1 + (l x) ^ 2) ^ n := pow_pos (by nlinarith [sq_nonneg (l x)]) _
  have hμν : μ ≪ ν := withDensity_absolutelyContinuous' hd.aemeasurable
    (Filter.Eventually.of_forall (fun x ↦ by rw [hdeq]; exact (ENNReal.ofReal_pos.mpr (hpos x)).ne'))
  have hνμ : ν ≪ μ := withDensity_absolutelyContinuous _ _
  obtain ⟨A, hA, hApos, hAfinite, hband, hνA⟩ := hardySobolevTranslation_zeroBase_powers_unbounded_band G μ m hm n
  have hνA' : ν A ≠ ⊤ := by simpa only [ν, hdensity] using hνA
  let f : G → ℂ := A.indicator (fun _ ↦ (1 : ℂ))
  have hf : MemLp f 2 ν := memLp_indicator_const 2 hA.nullMeasurableSet 1 (Or.inr hνA')
  let u : Lp ℂ 2 ν := hf.toLp f
  have hu : (u : G → ℂ) =ᵐ[μ] f := hμν.ae_eq (MemLp.coeFn_toLp hf)
  have hlmul (x y : G) : l (x * y) = l x + l y := by
    simp only [l, map_mul, Units.val_mul, NNReal.coe_mul]
    exact Real.log_mul (NNReal.coe_ne_zero.mpr (m x).ne_zero) (NNReal.coe_ne_zero.mpr (m y).ne_zero)
  have hlpow (k : ℕ) : l (g ^ k) = (k : ℝ) := by
    simp [l, map_pow, NNReal.coe_pow, Real.log_pow, hg]
  have hmasspos : 0 < (μ A).toReal := ENNReal.toReal_pos hApos hAfinite
  have hlower (k : ℕ) (hk : 1 ≤ k) : ((k : ℝ) - 1) ^ 2 * (μ A).toReal ≤ ‖T (g ^ k) u‖ ^ 2 := by
    let B := (fun x ↦ (g ^ k)⁻¹ * x) ⁻¹' A
    have hB : MeasurableSet B := hA.preimage (measurable_const_mul _)
    have hrep : (T (g ^ k) u : G → ℂ) =ᵐ[ν] B.indicator (fun _ ↦ (1 : ℂ)) := by
      apply hνμ.ae_eq
      have ht := (hT (g ^ k) u).trans
        ((measurePreserving_mul_left μ (g ^ k)⁻¹).quasiMeasurePreserving.ae_eq_comp hu)
      exact ht.trans (Filter.Eventually.of_forall (fun x ↦ by simp [f, B, indicator_apply]))
    have hmB := hardySobolevTranslation_zeroBase_powers_unbounded_indicator_mass G ν B hB (T (g ^ k) u) hrep
    have hh := hardySobolevTranslation_zeroBase_powers_unbounded_lower G μ l hlmul g hlpow n hn A hA
      (fun x hx ↦ (abs_le.mp (hband x hx)).1) k hk
    have hνeq : μ.withDensity (fun x ↦ ENNReal.ofReal ((1 + (l x) ^ 2) ^ n)) = ν := by simp only [ν, hdensity]
    rw [hνeq] at hh
    rw [hmB] at hh
    have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _)] using hr
  by_contra! hbounded
  have hC : 0 ≤ C := (norm_nonneg (T (g ^ 0))).trans (hbounded 0)
  have hupper (k : ℕ) : ‖T (g ^ k) u‖ ≤ C * ‖u‖ :=
    ((T (g ^ k)).le_opNorm u).trans (mul_le_mul_of_nonneg_right (hbounded k) (norm_nonneg u))
  obtain ⟨j, hj⟩ := exists_nat_gt (C * ‖u‖ / Real.sqrt ((μ A).toReal) + 1)
  have hsqrt : 0 < Real.sqrt ((μ A).toReal) := Real.sqrt_pos.mpr hmasspos
  have hmul : C * ‖u‖ < (j : ℝ) * Real.sqrt ((μ A).toReal) :=
    (div_lt_iff₀ hsqrt).mp (by linarith [hj])
  have hh := hlower (j + 1) (by omega)
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at hh
  have hsq : ((j : ℝ) * Real.sqrt ((μ A).toReal)) ^ 2 = (j : ℝ) ^ 2 * (μ A).toReal := by
    rw [mul_pow, Real.sq_sqrt (le_of_lt hmasspos)]
  have hu_nonneg : 0 ≤ C * ‖u‖ := mul_nonneg hC (norm_nonneg u)
  have hsquared := (sq_lt_sq₀ hu_nonneg (hu_nonneg.trans_lt hmul).le).mpr hmul
  nlinarith [hupper (j + 1), norm_nonneg (T (g ^ (j + 1)) u)]

/-- Paper: Remark 10.4.1.4, p. 457. For the singleton base and positive even
degree the translation operators are unbounded in operator norm along powers
of a class of logarithmic norm one.
Deviation: Polynomial growth in both directions and unboundedness of the
operator norms rule out the asserted equivalent conformal Hilbert norm. -/
theorem hardySobolevTranslation_zeroBase_powers_unbounded (n : ℕ) (_hn : 0 < n)
    (g : C𝔽) (_hg : logNorm g = 1) :
    ∀ C : ℝ, ∃ k : ℕ, C <
      ‖hardySobolevTranslation μ𝔽 m𝔽 0 0 (2 * (n : ℝ)) le_rfl
        (mul_nonneg zero_le_two (Nat.cast_nonneg n)) (g ^ k)‖ := by
  let d : C𝔽 → ENNReal := fun x ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 (2 * (n : ℝ)) (logNorm x))
  have hdeq (x : C𝔽) : d x = ENNReal.ofReal ((1 + (logNorm x) ^ 2) ^ n) := by
    simp [d, intervalSobolevDensity, Real.rpow_natCast]
  have hd : Measurable d := by
    rw [show d = (fun x ↦ ENNReal.ofReal ((1 + (logNorm x) ^ 2) ^ n)) from funext hdeq]
    have hl : Measurable logNorm := Real.measurable_log.comp
      (NNReal.continuous_coe.comp (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous)).measurable
    fun_prop
  with_unfolding_all
    exact hardySobolevTranslation_zeroBase_powers_unbounded_weighted C𝔽 μ𝔽 m𝔽
      (isProperMap_ideleClassNorm F) n _hn g _hg d hd hdeq
      (hardySobolevTranslation μ𝔽 m𝔽 0 0 (2 * (n : ℝ)) le_rfl (mul_nonneg zero_le_two (Nat.cast_nonneg n)))
      (fun h u ↦ hardySobolevTranslation_apply μ𝔽 m𝔽 0 0 (2 * (n : ℝ)) le_rfl
        (mul_nonneg zero_le_two (Nat.cast_nonneg n)) h u)

/-- Paper: Remark 10.4.1.4, p. 457. By invariance of theta, an output
geometric projection has no effect after convolution of a geometric vector. -/
theorem geometricProjection_convolution_geometricProjection (φ : BruhatCompactSupport C𝔽) :
    (Pgeom).comp ((A(φ)).comp Pgeom) = (A(φ)).comp Pgeom := by
  apply ContinuousLinearMap.ext
  intro u
  apply geometricProjection_apply_of_mem a hα hs
  apply (Submodule.Quotient.mk_eq_zero _).mp
  exact hardySobolevTestAction_preserves_globalTheta (F := F) a (hStrip(hα)) hs φ
    ((Θ₀).starProjection_apply_mem u)

/-- Paper: Remark 10.4.1.4, p. 458. Spectral projection after convolution
depends only on the input's spectral projection. -/
theorem spectralProjection_convolution_spectralProjection (φ : BruhatCompactSupport C𝔽) :
    (Pspec).comp ((A(φ)).comp Pspec) = (Pspec).comp (A(φ)) := by
  apply ContinuousLinearMap.ext
  intro u
  let L := (Pspec).comp (A(φ))
  have hz : L (Pgeom u) = 0 := by
    apply Submodule.starProjection_orthogonal_apply_eq_zero
    apply (Submodule.Quotient.mk_eq_zero (Θ₀)).mp
    exact hardySobolevTestAction_preserves_globalTheta (F := F) a (hStrip(hα)) hs φ
      ((Θ₀).starProjection_apply_mem u)
  calc
    L (Pspec u) = 0 + L (Pspec u) := (zero_add _).symm
    _ = L (Pgeom u) + L (Pspec u) := congrArg (fun v : W₀ ↦ v + L (Pspec u)) hz.symm
    _ = L (Pgeom u + Pspec u) := (map_add L _ _).symm
    _ = L u := congrArg L ((Θ₀).starProjection_add_starProjection_orthogonal u)

/-- Paper: Remark 10.4.1.4, p. 458. There is no convolution block from
the geometric subspace to the spectral subspace. -/
theorem spectralProjection_convolution_geometricProjection (φ : BruhatCompactSupport C𝔽) :
    (Pspec).comp ((A(φ)).comp Pgeom) = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  apply Submodule.starProjection_orthogonal_apply_eq_zero
  apply (Submodule.Quotient.mk_eq_zero _).mp
  exact hardySobolevTestAction_preserves_globalTheta (F := F) a (hStrip(hα)) hs φ
    ((Θ₀).starProjection_apply_mem u)

-- The reverse off-diagonal block on p. 458 can be nonzero. Its nonvanishing
-- cannot be universal in the test function, since the zero test kills every block.
-- The quotient action on the orthogonal complement is transported by its
-- isometry. Ambient translation on the complement would require invariance.

/-- Paper: Definition 10.4.1.5(1), p. 458. The geometric restriction applies
geometric projection, then convolution, then the cutoff multiplier. -/
def geometricRestriction (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) (φ : BruhatCompactSupport C𝔽) : W₀ →L[ℂ] W₀ :=
  (M(hρ)).comp ((A(φ)).comp Pgeom)

/-- Paper: Definition 10.4.1.5(2), p. 458. The spectral restriction applies
spectral projection, then convolution, then the cutoff multiplier. -/
def spectralRestriction (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) (φ : BruhatCompactSupport C𝔽) : W₀ →L[ℂ] W₀ :=
  (M(hρ)).comp ((A(φ)).comp Pspec)

/-- Paper: Definition 10.4.1.5(1), p. 458. On a geometric vector, the geometric
restriction is convolution followed by cutoff multiplication. -/
theorem geometricRestriction_apply_of_mem (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) (φ : BruhatCompactSupport C𝔽)
    {u : W₀} (_hu : u ∈ Θ₀) :
    geometricRestriction a hα hs hρ φ u = M(hρ) (A(φ) u) :=
  w18_comp_comp_apply_of_fix' _ _ _ _ (Submodule.starProjection_eq_self_iff.mpr _hu)

/-- Paper: Definition 10.4.1.5(2), p. 458. On a spectral vector, the spectral
restriction is convolution followed by cutoff multiplication. -/
theorem spectralRestriction_apply_of_mem (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) (φ : BruhatCompactSupport C𝔽)
    {u : W₀} (_hu : u ∈ (Θ₀).orthogonal) :
    spectralRestriction a hα hs hρ φ u = M(hρ) (A(φ) u) :=
  w18_comp_comp_apply_of_fix' _ _ _ _ (Submodule.starProjection_eq_self_iff.mpr _hu)

/-- Paper: (10.4.2.1), p. 458. Cutoff convolution is the sum of its geometric
and spectral truncations.
Deviation: The printed left-hand side has a stray trace, while the equation
has operators on the right-hand side. -/
theorem truncatedConvolution_eq_geometric_add_spectral (hρ : IsModulatedCutoff m𝔽 Λ ε ρ)
    (φ : BruhatCompactSupport C𝔽) :
    (M(hρ)).comp (A(φ)) =
      geometricTruncatedConvolution a hα hs hρ φ + spectralTruncatedConvolution a hα hs hρ φ :=
  by
  apply ContinuousLinearMap.ext
  intro u
  exact (DFunLike.congr_fun (geometricTruncation_add_spectralTruncation (F := F) a hα hs hρ)
    (A(φ) u)).symm

/-- Paper: (10.4.2.5), p. 459. Spectral projection after convolution is quotient
convolution transported back along the isometric section of the quotient map. -/
theorem spectralProjection_convolution_factor (φ : BruhatCompactSupport C𝔽) :
    (Pspec).comp (A(φ)) = ((Θ₀).orthogonal.subtypeL).comp
      ((Θ₀).quotientEquivOrthogonal.toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((Aₛ(φ)).comp Qₐ)) := by
  let sectionMap : H₀ → W₀ := fun x ↦ ((Θ₀).quotientEquivOrthogonal x).val
  have proj (w : W₀) : Pspec w = sectionMap ((Θ₀).mkQ w) := by
    have hzero : (Θ₀).mkQ (Pgeom w) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr ((Θ₀).starProjection_apply_mem w)
    have hsame : (Θ₀).mkQ w = (Θ₀).mkQ (Pspec w) := calc
      _ = (Θ₀).mkQ (Pgeom w + Pspec w) :=
        congrArg (Θ₀).mkQ ((Θ₀).starProjection_add_starProjection_orthogonal w).symm
      _ = _ := (map_add (Θ₀).mkQ _ _).trans (by rw [hzero, zero_add])
    have hrep := (Θ₀).quotientEquivOrthogonal_mk (Pspec w) ((Θ₀).orthogonal.starProjection_apply_mem w)
    exact (congrArg Subtype.val hrep).symm.trans (congrArg sectionMap hsame.symm)
  apply ContinuousLinearMap.ext
  intro u
  exact (proj (A(φ) u)).trans (congrArg sectionMap
    (spectralConvolution_mkQ (F := F) a (hStrip(hα)) hs φ u).symm)

-- TODO(paper-gap): The printed unconditional assertion for 0 ≤ s ≤ 1 needs
-- quotient nuclearity in that range. By (10.4.2.5) and Qₐ Sₐ = Id,
-- quotient nuclearity is equivalent to nuclearity of Pspec after convolution.

/-- Paper: Theorem 10.4.2.1, p. 459. The untruncated spectral projection
after convolution is nuclear.
Deviation: Quotient nuclearity is explicit so the theorem applies at every
nonnegative degree where this input holds. Section 10.3 states it for s > 1. Its proof is subject to ERRATA R5. -/
theorem spectralProjection_convolution_nuclear (φ : BruhatCompactSupport C𝔽)
    (_hquot : quotientNuclear(φ)) :
    IsNuclearOperator ((Pspec).comp (A(φ))) := by
  rw [spectralProjection_convolution_factor]
  let e := (Θ₀).quotientEquivOrthogonal.toContinuousLinearEquiv
  exact isNuclearOperator_comp_comp _hquot Qₐ ((Θ₀).orthogonal.subtypeL.comp e.toContinuousLinearMap)
    (Subtype.val_injective.comp e.injective)

/-- Paper: Theorem 10.4.2.1, p. 459. Spectral truncation of convolution is nuclear.
Deviation: Quotient nuclearity is explicit, as for the untruncated operator. -/
theorem spectralTruncatedConvolution_nuclear (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) (φ : BruhatCompactSupport C𝔽)
    (_hquot : quotientNuclear(φ)) :
    IsNuclearOperator (spectralTruncatedConvolution a hα hs hρ φ) := by
  exact mul_mem_nuclearEndomorphisms_left (M(hρ))
    ⟨(Pspec).comp (A(φ)), spectralProjection_convolution_nuclear a hα hs φ _hquot⟩

/-- Paper: Theorem 10.4.2.1, p. 459. Geometric truncation of convolution is nuclear.
Deviation: Quotient nuclearity is explicit, as for spectral truncation. -/
theorem geometricTruncatedConvolution_nuclear (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) (_hband : innerBand)
    (φ : BruhatCompactSupport C𝔽) (_hquot : quotientNuclear(φ)) :
    IsNuclearOperator (geometricTruncatedConvolution a hα hs hρ φ) := by
  have hφs : IsBruhatSmooth φ.val := (mem_bruhatSmoothSubmodule_iff _).mp φ.property.1
  have hc := continuous_of_bruhatSmooth hφs
  have hb := hc.bounded_above_of_compact_support (show HasCompactSupport φ.val from φ.property.2)
  have hm : IsModulation m𝔽 := ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
  have hsur : Function.Surjective m𝔽 := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.2.2.2.1
  obtain ⟨hT, _, _⟩ := truncatedHardySobolevConvolution_trace μ𝔽 m𝔽 (-α) α s (hStrip(hα)) hs φ.val
    hc.aemeasurable φ.property.2 hb hm hsur hφs hρ _hband
  have hconv := hardySobolevConvolution_eq_testAction μ𝔽 m𝔽 (-α) α s (hStrip(hα)) hs φ hc.aemeasurable hb
  let T : W₀ →L[ℂ] W₀ := (M(hρ)).comp (A(φ))
  have hn : T ∈ nuclearEndomorphisms W₀ :=
    (congrArg (fun U : W₀ →L[ℂ] W₀ ↦ IsNuclearOperator (E := W₀) (F := W₀) ((M(hρ)).comp U)) hconv).mp hT
  let S : nuclearEndomorphisms W₀ := ⟨_, spectralTruncatedConvolution_nuclear a hα hs hρ φ _hquot⟩
  have heq := truncatedConvolution_eq_geometric_add_spectral (F := F) a hα hs hρ φ
  have hdiff : geometricTruncatedConvolution a hα hs hρ φ = T - S.val :=
    eq_sub_of_add_eq heq.symm
  exact (congrArg (fun U : W₀ →L[ℂ] W₀ ↦ IsNuclearOperator U) hdiff).mpr
    ((nuclearEndomorphisms W₀).sub_mem hn S.property)

/-- Paper: Theorem 10.4.2.1, p. 459. The nuclear trace of cutoff convolution
splits as the sum of the geometric and spectral traces.
Deviation: Quotient nuclearity is explicit, and the trace identity includes
witnesses of nuclearity for all three operators. -/
theorem truncatedConvolution_trace_split (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) (_hband : innerBand)
    (φ : BruhatCompactSupport C𝔽) (_hquot : quotientNuclear(φ)) :
    let T := (M(hρ)).comp (A(φ))
    let G := geometricTruncatedConvolution a hα hs hρ φ
    let S := spectralTruncatedConvolution a hα hs hρ φ
    ∃ (hT : IsNuclearOperator T) (hG : IsNuclearOperator G) (hS : IsNuclearOperator S),
      hilbertTrace (H := W₀) ⟨T, hT⟩ =
        hilbertTrace (H := W₀) ⟨G, hG⟩ + hilbertTrace (H := W₀) ⟨S, hS⟩ := by
  intro T G S
  have heq : T = G + S := truncatedConvolution_eq_geometric_add_spectral (F := F) a hα hs hρ φ
  have hG : IsNuclearOperator G := geometricTruncatedConvolution_nuclear (F := F) a hα hs hρ _hband φ _hquot
  have hS : IsNuclearOperator S := spectralTruncatedConvolution_nuclear (F := F) a hα hs hρ φ _hquot
  clear_value T G S
  have addTrace {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (T G S : H →L[ℂ] H) (heq : T = G + S) (hG : IsNuclearOperator G) (hS : IsNuclearOperator S) :
      ∃ (hT : IsNuclearOperator T) (hg : IsNuclearOperator G) (hs' : IsNuclearOperator S),
        hilbertTrace (H := H) ⟨T, hT⟩ = hilbertTrace (H := H) ⟨G, hg⟩ + hilbertTrace (H := H) ⟨S, hs'⟩ := by
    subst T
    obtain ⟨L, hL⟩ := hilbertTrace_linear (H := H)
    let g : nuclearEndomorphisms H := ⟨G, hG⟩
    let s' : nuclearEndomorphisms H := ⟨S, hS⟩
    refine ⟨(g + s').property, hG, hS, ?_⟩
    exact (hL (g + s')).symm.trans ((L.map_add g s').trans (congrArg₂ (· + ·) (hL g) (hL s')))
  exact addTrace (H := ↥W₀) T G S heq hG hS

/-- The weighted L² norm squared is the integral of the squared pointwise norm. -/
private theorem spectralTruncatedConvolution_trace_tendsto_norm_sq (X : Type*) [MeasurableSpace X] (ν : Measure X) (v : Lp ℂ 2 ν) :
    ‖v‖ ^ 2 = ∫ x, ‖v x‖ ^ 2 ∂ν := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def]
  rw [← integral_re]
  congr 1
  funext x
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) (v x)).symm
  exact L2.integrable_inner v v

/-- Bounded pointwise-convergent multiplier symbols give strong convergence on L². -/
private theorem spectralTruncatedConvolution_trace_tendsto_multiplier (X : Type*) [MeasurableSpace X] (ν : Measure X)
    (σ : ℝ → X → ℝ) (hσ : ∀ R, Measurable (σ R)) (hbound : ∀ R x, |σ R x| ≤ 1)
    (hlim : ∀ x, Tendsto (fun R ↦ σ R x) atTop (𝓝 1))
    (P : ℝ → Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν)
    (hP : ∀ R u, (P R u : X → ℂ) =ᵐ[ν] fun x ↦ (σ R x : ℂ) * u x) :
    ∀ u, Tendsto (fun R ↦ P R u) atTop (𝓝 u) := by
  intro u
  let f (R : ℝ) (x : X) : ℂ := (σ R x : ℂ) * u x - u x
  have hfbound (R : ℝ) (x : X) : ‖f R x‖ ≤ 2 * ‖u x‖ := by
    calc
      ‖f R x‖ ≤ ‖(σ R x : ℂ) * u x‖ + ‖u x‖ := norm_sub_le _ _
      _ = |σ R x| * ‖u x‖ + ‖u x‖ := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ 2 * ‖u x‖ := by nlinarith [hbound R x, norm_nonneg (u x)]
  have hint : Integrable (fun x ↦ 4 * ‖u x‖ ^ 2) ν := by
    exact ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).mp (Lp.memLp u)).const_mul 4
  have hconv : Tendsto (fun R ↦ ∫ x, ‖f R x‖ ^ 2 ∂ν) atTop (𝓝 0) := by
    have hh := tendsto_integral_filter_of_dominated_convergence (l := (atTop : Filter ℝ))
      (F := fun R : ℝ ↦ fun x : X ↦ ‖f R x‖ ^ 2) (f := fun _ : X ↦ (0 : ℝ)) (fun x ↦ 4 * ‖u x‖ ^ 2)
      (Filter.Eventually.of_forall (fun R ↦ ((((Complex.measurable_ofReal.comp (hσ R)).aestronglyMeasurable.mul
        (Lp.aestronglyMeasurable u)).sub (Lp.aestronglyMeasurable u)).norm.pow 2)))
      (Filter.Eventually.of_forall (fun R ↦ Filter.Eventually.of_forall (fun x ↦ by
        change ‖‖f R x‖ ^ 2‖ ≤ 4 * ‖u x‖ ^ 2
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        nlinarith [hfbound R x, norm_nonneg (f R x), norm_nonneg (u x)]))) hint
      (Filter.Eventually.of_forall (fun x ↦ ?_))
    · simpa using hh
    · have hh := ((Complex.continuous_ofReal.tendsto 1).comp (hlim x)).mul
        (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ u x) atTop (𝓝 (u x)))
      have hh' : Tendsto (fun R ↦ f R x) atTop (𝓝 0) := by
        simpa [f] using hh.sub (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ u x) atTop (𝓝 (u x)))
      simpa using hh'.norm.pow 2
  have heq (R : ℝ) : ‖P R u - u‖ ^ 2 = ∫ x, ‖f R x‖ ^ 2 ∂ν := by
    rw [spectralTruncatedConvolution_trace_tendsto_norm_sq]
    apply integral_congr_ae
    filter_upwards [hP R u, Lp.coeFn_sub (P R u) u] with x hx hsub
    rw [hsub]
    change ‖P R u x - u x‖ ^ 2 = ‖f R x‖ ^ 2
    rw [hx]
  have hsquare : Tendsto (fun R ↦ ‖P R u - u‖ ^ 2) atTop (𝓝 0) := by simpa only [heq] using hconv
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa using hsquare.sqrt

/-- Expanding cutoffs extend to a contractive family converging strongly to the identity. -/
private theorem spectralTruncatedConvolution_trace_tendsto_family
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (m : G →ₜ* ℝ≥0ˣ) (ν : Measure G)
    (ε : ℝ → ℝ) (ρ : ℝ → G → ℝ)
    (hε : Tendsto (fun R ↦ ε R * R) atTop (𝓝 0))
    (hρ : ∀ᶠ R in atTop, IsModulatedCutoff m R (ε R) (ρ R) ∧
      0 < R⁻¹ + ε R ∧ R⁻¹ + ε R < R - ε R) :
    ∃ P : ℝ → Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν,
      (∀ R, ‖P R‖ ≤ 1) ∧ (∀ u, Tendsto (fun R ↦ P R u) atTop (𝓝 u)) ∧
      ∀ R (hcut : IsModulatedCutoff m R (ε R) (ρ R)), P R = modulatedCutoffOperator m ν hcut := by
  classical
  have heps : Tendsto ε atTop (𝓝 0) := by
    have hh := hε.mul tendsto_inv_atTop_zero
    apply (show Tendsto (fun R ↦ (ε R * R) * R⁻¹) atTop (𝓝 0) from by simpa using hh).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    field_simp
  have hl : Tendsto (fun R ↦ R⁻¹ + ε R) atTop (𝓝 0) := by simpa using tendsto_inv_atTop_zero.add heps
  have hu : Tendsto (fun R ↦ R - ε R) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [heps.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
      eventually_ge_atTop (b + 1)] with R he hR
    linarith
  have hrholim (x : G) : Tendsto (fun R ↦ ρ R x) atTop (𝓝 1) := by
    have hx : 0 < ((m x).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
    apply tendsto_const_nhds.congr'
    filter_upwards [hρ, hl.eventually (gt_mem_nhds hx), hu.eventually_ge_atTop ((m x).val : ℝ)] with R hcut hleft hright
    exact (hcut.1.eq_one ⟨hleft.le, hright⟩).symm
  let σ (R : ℝ) : G → ℝ := if h : IsModulatedCutoff m R (ε R) (ρ R) then ρ R else 1
  let P (R : ℝ) : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν :=
    if h : IsModulatedCutoff m R (ε R) (ρ R) then modulatedCutoffOperator m ν h else 1
  have hσ (R : ℝ) : Measurable (σ R) := by
    dsimp only [σ]
    split_ifs with h
    · exact h.measurable
    · exact measurable_const
  have hσbound (R : ℝ) (x : G) : |σ R x| ≤ 1 := by
    dsimp only [σ]
    split_ifs with h
    · exact h.abs_le_one x
    · norm_num
  have hσlim (x : G) : Tendsto (fun R ↦ σ R x) atTop (𝓝 1) := by
    apply (hrholim x).congr'
    filter_upwards [hρ] with R hR
    simp [σ, hR.1]
  have hPrep (R : ℝ) (u : Lp ℂ 2 ν) : (P R u : G → ℂ) =ᵐ[ν] fun x ↦ (σ R x : ℂ) * u x := by
    by_cases h : IsModulatedCutoff m R (ε R) (ρ R)
    · simpa only [P, σ, dite_eq_left h] using modulatedCutoffOperator_apply m ν h u
    · simp only [P, σ, dite_eq_right h]
      filter_upwards with x
      simp
  refine ⟨P, ?_, spectralTruncatedConvolution_trace_tendsto_multiplier G ν σ hσ hσbound hσlim P hPrep, ?_⟩
  · intro R
    dsimp only [P]
    split_ifs with h
    · exact (exists_lpCutoffMultiplier ν (ρ R) h.measurable h.abs_le_one).choose_spec.1
    · exact ContinuousLinearMap.norm_id_le
  · intro R hcut
    exact dite_eq_left hcut

/-- A uniformly bounded strongly null family kills a nuclear operator in trace norm. -/
private theorem spectralTruncatedConvolution_trace_tendsto_null
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Q : ℝ → H →L[ℂ] H) (hQ : ∀ x, Tendsto (fun R ↦ Q R x) atTop (𝓝 0))
    (hbound : ∀ R, ‖Q R‖ ≤ 2) (T : nuclearEndomorphisms H) :
    Tendsto (fun R ↦ traceNorm ⟨Q R * T.val, mul_mem_nuclearEndomorphisms_left (Q R) T⟩) atTop (𝓝 0) := by
  let product (R : ℝ) (A : nuclearEndomorphisms H) : nuclearEndomorphisms H :=
    ⟨Q R * A.val, mul_mem_nuclearEndomorphisms_left (Q R) A⟩
  let : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
  have hcore := (traceNorm_normedSpaceCore (H := H)).toCore
  have hnonneg (A : nuclearEndomorphisms H) : 0 ≤ traceNorm A := hcore.norm_nonneg A
  refine Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
  obtain ⟨z, hz⟩ := exists_tensorToFiniteRank_traceNorm_sub_lt T (by positivity : 0 < ε / 4)
  let F : nuclearEndomorphisms H :=
    ⟨tensorToFiniteRank z, tensorToFiniteRank_mem_nuclearEndomorphisms z⟩
  obtain ⟨_, hF⟩ := tendsto_traceNorm_mul_finiteRank Q hQ F.val (finiteDimensional_range_tensorToFiniteRank z)
  have hF' : Tendsto (fun R ↦ traceNorm (product R F)) atTop (𝓝 0) := hF
  filter_upwards [Metric.tendsto_nhds.mp hF' (ε / 2) (half_pos hε)] with R hR
  have hsplit : product R T = product R (T - F) + product R F := by
    apply Subtype.ext
    simp [product, mul_sub]
  have hle : traceNorm (product R (T - F)) ≤ 2 * traceNorm (T - F) :=
    (traceNorm_mul_left_le (Q R) (T - F)).trans
      (mul_le_mul_of_nonneg_right (hbound R) (hnonneg (T - F)))
  have htriangle : traceNorm (product R T) ≤
      traceNorm (product R (T - F)) + traceNorm (product R F) := by
    rw [hsplit]
    exact hcore.norm_triangle _ _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hnonneg (product R F))] at hR
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hnonneg (product R T))]
  change traceNorm (T - F) < ε / 4 at hz
  linarith

/-- Contractive strong approximation of the identity preserves nuclear traces. -/
private theorem spectralTruncatedConvolution_trace_tendsto_strong
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : ℝ → H →L[ℂ] H) (hP : ∀ x, Tendsto (fun R ↦ P R x) atTop (𝓝 x))
    (hbound : ∀ R, ‖P R‖ ≤ 1) (T : nuclearEndomorphisms H) :
    Tendsto (fun R ↦ hilbertTrace ⟨P R * T.val, mul_mem_nuclearEndomorphisms_left (P R) T⟩)
      atTop (𝓝 (hilbertTrace T)) := by
  let Q : ℝ → H →L[ℂ] H := fun R ↦ P R - 1
  have hQ : ∀ x, Tendsto (fun R ↦ Q R x) atTop (𝓝 0) := by
    intro x
    simpa [Q] using (hP x).sub (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ x) atTop (𝓝 x))
  have hQbound (R : ℝ) : ‖Q R‖ ≤ 2 := by
    have hid : ‖(1 : H →L[ℂ] H)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    exact (norm_sub_le (P R) 1).trans (by linarith [hbound R])
  let A (R : ℝ) : nuclearEndomorphisms H := ⟨Q R * T.val, mul_mem_nuclearEndomorphisms_left (Q R) T⟩
  let B (R : ℝ) : nuclearEndomorphisms H := ⟨P R * T.val, mul_mem_nuclearEndomorphisms_left (P R) T⟩
  have hn : Tendsto (fun R ↦ traceNorm (A R)) atTop (𝓝 0) :=
    spectralTruncatedConvolution_trace_tendsto_null H Q hQ hQbound T
  have hnorm : Tendsto (fun R ↦ ‖hilbertTrace (A R)‖) atTop (𝓝 0) :=
    squeeze_zero (fun R ↦ norm_nonneg _) (fun R ↦ norm_hilbertTrace_le (A R)) hn
  obtain ⟨L, hL⟩ := hilbertTrace_linear (H := H)
  have heq (R : ℝ) : hilbertTrace (B R) - hilbertTrace T = hilbertTrace (A R) := by
    have hAB : A R = B R - T := by apply Subtype.ext; simp [A, B, Q, sub_mul]
    rw [hAB, ← hL, ← hL, ← hL, map_sub]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  change Tendsto (fun R ↦ ‖hilbertTrace (B R) - hilbertTrace T‖) atTop (𝓝 0)
  simpa only [heq] using hnorm

/-- Strong cutoff convergence and cyclicity identify the limit with the quotient trace. -/
private theorem spectralTruncatedConvolution_trace_tendsto_factored
    (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [PolynormableSpace ℂ E] [PolynormableSpace ℂ F]
    (J : E →L[ℂ] F) (hJ : Injective J) (Q : F →L[ℂ] E)
    (hQJ : Q.comp J = ContinuousLinearMap.id ℂ E) (A : E →L[ℂ] E) (hA : IsNuclearOperator A)
    (P : ℝ → F →L[ℂ] F) (hP : ∀ x, Tendsto (fun R ↦ P R x) atTop (𝓝 x))
    (hbound : ∀ R, ‖P R‖ ≤ 1) :
    ∃ hB : IsNuclearOperator (J.comp (A.comp Q)),
      Tendsto (fun R ↦ hilbertTrace ⟨P R * (J.comp (A.comp Q)),
        mul_mem_nuclearEndomorphisms_left (P R) ⟨_, hB⟩⟩) atTop (𝓝 (hilbertTrace ⟨A, hA⟩)) := by
  have hAQ : IsNuclearOperator (A.comp Q) := by
    simpa using isNuclearOperator_comp_comp hA Q (ContinuousLinearMap.id ℂ E) injective_id
  have hrev : (A.comp Q).comp J = A := by
    rw [ContinuousLinearMap.comp_assoc, hQJ, ContinuousLinearMap.comp_id]
  have hn := isNuclearOperator_factor_comps J hJ (A.comp Q) hAQ
  have ht : hilbertTrace ⟨J.comp (A.comp Q), hn.2⟩ = hilbertTrace ⟨A, hA⟩ := by
    rw [hilbertTrace_eq_nuclearTrace, hilbertTrace_eq_nuclearTrace]
    have ht := nuclearTrace_factor_comps (hilbert_approximationProperty (H := E))
      (hilbert_approximationProperty (H := F)) J hJ (A.comp Q) hAQ
    simpa only [hrev] using ht.symm
  refine ⟨hn.2, ?_⟩
  have hh := spectralTruncatedConvolution_trace_tendsto_strong F P hP hbound ⟨_, hn.2⟩
  rw [ht] at hh
  exact hh

/-- Paper: Theorem 10.4.2.2, p. 460. As the cutoff radius tends to infinity
with width times radius tending to zero, the trace of projection after
convolution tends to the quotient convolution trace.
Deviation: Quotient nuclearity is explicit. The quotient trace on a general
strip is the one in Theorem 10.3.2.1, with Theorem 10.3.1.1 for the line. -/
theorem spectralTruncatedConvolution_trace_tendsto (φ : BruhatCompactSupport C𝔽)
    (hquot : quotientNuclear(φ)) (ε : ℝ → ℝ) (ρ : ℝ → C𝔽 → ℝ)
    (_hε : Tendsto (fun R ↦ ε R * R) atTop (𝓝 0))
    (_hρ : ∀ᶠ R in atTop, IsModulatedCutoff m𝔽 R (ε R) (ρ R) ∧
      0 < R⁻¹ + ε R ∧ R⁻¹ + ε R < R - ε R) :
    ∃ traces : ℝ → ℂ,
      (∀ᶠ R in atTop, ∃ hcut : IsModulatedCutoff m𝔽 R (ε R) (ρ R),
        let T := spectralTruncatedConvolution a hα hs hcut φ
        ∃ hT : IsNuclearOperator T, traces R = hilbertTrace (H := W₀) ⟨T, hT⟩) ∧
      Tendsto traces atTop (𝓝 (hilbertTrace (H := H₀) ⟨Aₛ(φ), hquot⟩)) := by
  have hfamily : ∃ P : ℝ → W₀ →L[ℂ] W₀,
      (∀ R, ‖P R‖ ≤ 1) ∧ (∀ u, Tendsto (fun R ↦ P R u) atTop (𝓝 u)) ∧
      ∀ R (hcut : IsModulatedCutoff m𝔽 R (ε R) (ρ R)), P R = M(hcut) := by
    with_unfolding_all
      exact spectralTruncatedConvolution_trace_tendsto_family C𝔽 m𝔽
        ((μ𝔽).withDensity fun g ↦ ENNReal.ofReal (intervalSobolevDensity (-α) α s (logNorm g))) ε ρ _hε _hρ
  obtain ⟨P, hPbound, hPstrong, hPagree⟩ := hfamily
  let J := (Θ₀).orthogonal.subtypeL.comp
    (Θ₀).quotientEquivOrthogonal.toContinuousLinearEquiv.toContinuousLinearMap
  have hJ : Injective J := Subtype.val_injective.comp (Θ₀).quotientEquivOrthogonal.injective
  have hQJ : (Qₐ).comp J = ContinuousLinearMap.id ℂ H₀ := by
    ext x
    exact (Θ₀).quotientEquivOrthogonal.symm_apply_apply x
  have hfactor : (Pspec).comp (A(φ)) = J.comp ((Aₛ(φ)).comp Qₐ) :=
    spectralProjection_convolution_factor (F := F) a hα hs φ
  clear_value J
  have hlimit : ∃ hB : IsNuclearOperator (J.comp ((Aₛ(φ)).comp Qₐ)),
      Tendsto (fun R ↦ hilbertTrace ⟨P R * (J.comp ((Aₛ(φ)).comp Qₐ)),
        mul_mem_nuclearEndomorphisms_left (P R) ⟨_, hB⟩⟩)
        atTop (𝓝 (hilbertTrace ⟨Aₛ(φ), hquot⟩)) := by
    with_unfolding_all
      exact spectralTruncatedConvolution_trace_tendsto_factored H₀ W₀ J hJ Qₐ hQJ (Aₛ(φ)) hquot P hPstrong hPbound
  obtain ⟨hB, hlimit⟩ := hlimit
  refine ⟨fun R ↦ hilbertTrace ⟨P R * (J.comp ((Aₛ(φ)).comp Qₐ)),
    mul_mem_nuclearEndomorphisms_left (P R) ⟨_, hB⟩⟩, ?_, hlimit⟩
  filter_upwards [_hρ] with R hR
  refine ⟨hR.1, spectralTruncatedConvolution_nuclear (F := F) a hα hs hR.1 φ hquot, ?_⟩
  apply congrArg (hilbertTrace (H := W₀))
  apply Subtype.ext
  change (P R).comp (J.comp ((Aₛ(φ)).comp Qₐ)) = _
  exact (congrArg (fun Z : W₀ →L[ℂ] W₀ ↦ Z.comp (J.comp ((Aₛ(φ)).comp Qₐ))) (hPagree R hR.1)).trans
    (congrArg (fun Z : W₀ →L[ℂ] W₀ ↦ (M(hR.1)).comp Z) hfactor.symm)

/-- Expanding cutoff windows eventually contain each fixed module value. -/
private theorem geometricTruncatedConvolution_trace_remainder_tendsto_cutoff
    (F : Type*) [Field F] [NumberField F]
    (ε : ℝ → ℝ) (ρ : ℝ → (IdeleClassGroup (𝓞 F) F) → ℝ)
    (hε : Tendsto (fun R ↦ ε R * R) atTop (𝓝 0))
    (hρ : ∀ᶠ R in atTop, IsModulatedCutoff (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : (IdeleClassGroup (𝓞 F) F) →ₜ* ℝ≥0ˣ) R (ε R) (ρ R) ∧
      0 < R⁻¹ + ε R ∧ R⁻¹ + ε R < R - ε R) :
    ∀ x, Tendsto (fun R ↦ ρ R x) atTop (𝓝 1) := by
  have heps : Tendsto ε atTop (𝓝 0) := by
    have hh := hε.mul tendsto_inv_atTop_zero
    apply (show Tendsto (fun R ↦ (ε R * R) * R⁻¹) atTop (𝓝 0) from by simpa using hh).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    field_simp
  have hl : Tendsto (fun R ↦ R⁻¹ + ε R) atTop (𝓝 0) := by simpa using tendsto_inv_atTop_zero.add heps
  have hu : Tendsto (fun R ↦ R - ε R) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [heps.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
      eventually_ge_atTop (b + 1)] with R he hR
    linarith
  intro x
  have hx : 0 < (((⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : (IdeleClassGroup (𝓞 F) F) →ₜ* ℝ≥0ˣ) x).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
  apply tendsto_const_nhds.congr'
  filter_upwards [hρ, hl.eventually (gt_mem_nhds hx), hu.eventually_ge_atTop (((⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : (IdeleClassGroup (𝓞 F) F) →ₜ* ℝ≥0ˣ) x).val : ℝ)] with R hcut hleft hright
  exact (hcut.1.eq_one ⟨hleft.le, hright⟩).symm

/-- The class measure splits as kernel Haar measure times positive-real Haar measure. -/
private theorem geometricTruncatedConvolution_trace_remainder_tendsto_normProduct
    (F : Type*) [Field F] [NumberField F]
    (τ : ℝ≥0ˣ →ₜ* (IdeleClassGroup (𝓞 F) F)) (hτ : RightInverse τ (ideleClassNorm F)) :
    (ideleClassTamagawaMeasure F) = ((normOneIdeleClassTamagawaMeasure F).prod positiveRealHaar).map
      (fun p : (ideleClassNorm F).ker × ℝ≥0ˣ ↦ p.1.val * τ p.2) := by
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ _
  let : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  have hc : IsCompact ((ideleClassNorm F).ker : Set (IdeleClassGroup (𝓞 F) F)) :=
    (isProperMap_ideleClassNorm F).isCompact_preimage isCompact_singleton
  let : LocallyCompactSpace (ideleClassNorm F).ker := hc.isClosed.locallyCompactSpace
  let : CompactSpace (ideleClassNorm F).ker := isCompact_iff_compactSpace.mp hc
  obtain ⟨_, _, hw, hν, hνreg, _, hweil⟩ :=
    (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec
  let : (normOneIdeleClassTamagawaMeasure F).IsHaarMeasure := hν
  have : SFinite positiveRealHaar := by unfold positiveRealHaar; infer_instance
  have : IsFiniteMeasure (normOneIdeleClassTamagawaMeasure F) := inferInstance
  have hprod := normProduct_of_isWeil (ideleClassNorm F) (isProperMap_ideleClassNorm F).continuous
    τ τ.continuous hτ (ideleClassTamagawaMeasure F) hw.2.1 (normOneIdeleClassTamagawaMeasure F) hνreg hweil
  let f : ℝ≥0ˣ × (ideleClassNorm F).ker → (IdeleClassGroup (𝓞 F) F) := fun p ↦ τ p.1 * p.2.val
  have hf : Measurable f := ((τ.continuous.comp continuous_fst).mul
    (continuous_subtype_val.comp continuous_snd)).measurable
  have heq : (fun p : (ideleClassNorm F).ker × ℝ≥0ˣ ↦ p.1.val * τ p.2) = f ∘ Prod.swap := by
    funext p
    exact mul_comm _ _
  rw [heq, ← Measure.map_map hf measurable_swap, Measure.prod_swap]
  exact hprod.symm

/-- The full cutoff convolution trace has its logarithmic main term. -/
private theorem geometricTruncatedConvolution_trace_remainder_tendsto_total
    (F : Type*) [Field F] [NumberField F] {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (φ : BruhatCompactSupport (IdeleClassGroup (𝓞 F) F)) (ε : ℝ → ℝ) (ρ : ℝ → (IdeleClassGroup (𝓞 F) F) → ℝ)
    (hε : Tendsto (fun R ↦ ε R * R) atTop (𝓝 0))
    (hρ : ∀ᶠ R in atTop, IsModulatedCutoff (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : (IdeleClassGroup (𝓞 F) F) →ₜ* ℝ≥0ˣ) R (ε R) (ρ R) ∧
      0 < R⁻¹ + ε R ∧ R⁻¹ + ε R < R - ε R) :
    ∃ traces : ℝ → ℂ,
      (∀ᶠ R in atTop, ∃ hcut : IsModulatedCutoff (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : (IdeleClassGroup (𝓞 F) F) →ₜ* ℝ≥0ˣ) R (ε R) (ρ R),
        ∃ hT : IsNuclearOperator (((modulatedCutoffOperator (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : (IdeleClassGroup (𝓞 F) F) →ₜ* ℝ≥0ˣ) ((ideleClassTamagawaMeasure F).withDensity fun g ↦ ENNReal.ofReal (intervalSobolevDensity (-α) α s (Real.log ((ideleClassNorm F g).val : ℝ))))) hcut).comp ((hardySobolevTestAction (ideleClassTamagawaMeasure F) (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : (IdeleClassGroup (𝓞 F) F) →ₜ* ℝ≥0ˣ) (-α) α s ((neg_nonpos.mpr hα).trans hα) hs φ))),
          traces R = hilbertTrace (H := (CompactIntervalSobolev (ideleClassTamagawaMeasure F) (fun g : (IdeleClassGroup (𝓞 F) F) ↦ Real.log ((ideleClassNorm F g).val : ℝ)) (-α) α s)) ⟨((modulatedCutoffOperator (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : (IdeleClassGroup (𝓞 F) F) →ₜ* ℝ≥0ˣ) ((ideleClassTamagawaMeasure F).withDensity fun g ↦ ENNReal.ofReal (intervalSobolevDensity (-α) α s (Real.log ((ideleClassNorm F g).val : ℝ))))) hcut).comp ((hardySobolevTestAction (ideleClassTamagawaMeasure F) (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : (IdeleClassGroup (𝓞 F) F) →ₜ* ℝ≥0ˣ) (-α) α s ((neg_nonpos.mpr hα).trans hα) hs φ)), hT⟩) ∧
      Tendsto (fun R ↦ traces R - ((2 * Real.log R * (normOneIdeleClassTamagawaMeasure F).real univ : ℝ) : ℂ) * φ.val 1)
        atTop (𝓝 0) := by
  let q : (AdeleRing (𝓞 F) F)ˣ →ₜ* (IdeleClassGroup (𝓞 F) F) := ⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩
  let τ : ℝ≥0ˣ →ₜ* (IdeleClassGroup (𝓞 F) F) := q.comp ⟨canonicalIdeleNormSection F, canonicalIdeleNormSection_continuous F⟩
  have hτ : RightInverse τ (ideleClassNorm F) := canonicalIdeleNormSection_rightInverse F
  let : (normOneIdeleClassTamagawaMeasure F).IsHaarMeasure :=
    (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  have hμ := geometricTruncatedConvolution_trace_remainder_tendsto_normProduct F τ hτ
  have hρlim := geometricTruncatedConvolution_trace_remainder_tendsto_cutoff F ε ρ hε hρ
  have hφs : IsBruhatSmooth φ.val := (mem_bruhatSmoothSubmodule_iff _).mp φ.property.1
  have hc := continuous_of_bruhatSmooth hφs
  have hb := hc.bounded_above_of_compact_support (show HasCompactSupport φ.val from φ.property.2)
  have hm : IsModulation (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : (IdeleClassGroup (𝓞 F) F) →ₜ* ℝ≥0ˣ) := ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
  have hconv := hardySobolevConvolution_eq_testAction (ideleClassTamagawaMeasure F) (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : (IdeleClassGroup (𝓞 F) F) →ₜ* ℝ≥0ˣ) (-α) α s (((neg_nonpos.mpr hα).trans hα)) hs φ hc.aemeasurable hb
  have hTotExists : ∃ traces : ℝ → ℂ,
      (∀ᶠ R in atTop, ∃ hcut : IsModulatedCutoff (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : (IdeleClassGroup (𝓞 F) F) →ₜ* ℝ≥0ˣ) R (ε R) (ρ R),
        ∃ hT : IsNuclearOperator (((modulatedCutoffOperator (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : (IdeleClassGroup (𝓞 F) F) →ₜ* ℝ≥0ˣ) ((ideleClassTamagawaMeasure F).withDensity fun g ↦ ENNReal.ofReal (intervalSobolevDensity (-α) α s (Real.log ((ideleClassNorm F g).val : ℝ))))) hcut).comp
          (hardySobolevConvolution (ideleClassTamagawaMeasure F) (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : (IdeleClassGroup (𝓞 F) F) →ₜ* ℝ≥0ˣ) (-α) α s (((neg_nonpos.mpr hα).trans hα)) hs φ.val hc.aemeasurable φ.property.2 hb)),
          traces R = hilbertTrace ⟨((modulatedCutoffOperator (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : (IdeleClassGroup (𝓞 F) F) →ₜ* ℝ≥0ˣ) ((ideleClassTamagawaMeasure F).withDensity fun g ↦ ENNReal.ofReal (intervalSobolevDensity (-α) α s (Real.log ((ideleClassNorm F g).val : ℝ))))) hcut).comp
            (hardySobolevConvolution (ideleClassTamagawaMeasure F) (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : (IdeleClassGroup (𝓞 F) F) →ₜ* ℝ≥0ˣ) (-α) α s (((neg_nonpos.mpr hα).trans hα)) hs φ.val hc.aemeasurable φ.property.2 hb), hT⟩) ∧
      Tendsto (fun R ↦ traces R - ((2 * Real.log R * (normOneIdeleClassTamagawaMeasure F).real univ : ℝ) : ℂ) * φ.val 1)
        atTop (𝓝 0) := by
    with_unfolding_all
      exact truncatedHardySobolevConvolution_trace_tendsto
        (ideleClassTamagawaMeasure F) (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : (IdeleClassGroup (𝓞 F) F) →ₜ* ℝ≥0ˣ) (-α) α s (((neg_nonpos.mpr hα).trans hα)) hs φ.val hc.aemeasurable φ.property.2 hb
        hm hφs τ hτ (normOneIdeleClassTamagawaMeasure F) hμ ε ρ hε hρlim hρ
  simpa only [hconv] using hTotExists

/-- Paper: Remark 10.4.2.3, p. 460. Subtracting the geometric truncated
trace from the logarithmic main term gives the quotient trace in the cutoff limit.
Deviation: The norm-one mass is the Tamagawa mass from Appendix A and
quotient nuclearity is explicit. -/
theorem geometricTruncatedConvolution_trace_remainder_tendsto (φ : BruhatCompactSupport C𝔽)
    (hquot : quotientNuclear(φ)) (ε : ℝ → ℝ) (ρ : ℝ → C𝔽 → ℝ)
    (_hε : Tendsto (fun R ↦ ε R * R) atTop (𝓝 0))
    (_hρ : ∀ᶠ R in atTop, IsModulatedCutoff m𝔽 R (ε R) (ρ R) ∧
      0 < R⁻¹ + ε R ∧ R⁻¹ + ε R < R - ε R) :
    ∃ traces : ℝ → ℂ,
      (∀ᶠ R in atTop, ∃ hcut : IsModulatedCutoff m𝔽 R (ε R) (ρ R),
        let T := geometricTruncatedConvolution a hα hs hcut φ
        ∃ hT : IsNuclearOperator T, traces R = hilbertTrace (H := W₀) ⟨T, hT⟩) ∧
      Tendsto (fun R ↦
        ((2 * Real.log R * (normOneIdeleClassTamagawaMeasure F).real univ : ℝ) : ℂ) *
          φ.val 1 - traces R) atTop (𝓝 (hilbertTrace (H := H₀) ⟨Aₛ(φ), hquot⟩)) := by
  have hTotAction : ∃ traces : ℝ → ℂ,
      (∀ᶠ R in atTop, ∃ hcut : IsModulatedCutoff m𝔽 R (ε R) (ρ R),
        ∃ hT : IsNuclearOperator ((M(hcut)).comp (A(φ))),
          traces R = hilbertTrace (H := W₀) ⟨(M(hcut)).comp (A(φ)), hT⟩) ∧
      Tendsto (fun R ↦ traces R - ((2 * Real.log R * (normOneIdeleClassTamagawaMeasure F).real univ : ℝ) : ℂ) * φ.val 1)
        atTop (𝓝 0) := by
    with_unfolding_all
      exact geometricTruncatedConvolution_trace_remainder_tendsto_total (F := F) (α := α) (s := s) hα hs φ ε ρ _hε _hρ
  obtain ⟨total, htotal, hlimtotal⟩ := hTotAction
  have hSpecExists : ∃ traces : ℝ → ℂ,
      (∀ᶠ R in atTop, ∃ hcut : IsModulatedCutoff m𝔽 R (ε R) (ρ R),
        ∃ hT : IsNuclearOperator (spectralTruncatedConvolution a hα hs hcut φ),
          traces R = hilbertTrace ⟨spectralTruncatedConvolution a hα hs hcut φ, hT⟩) ∧
      Tendsto traces atTop (𝓝 (hilbertTrace ⟨Aₛ(φ), hquot⟩)) := by
    with_unfolding_all
      exact spectralTruncatedConvolution_trace_tendsto (F := F) a hα hs φ hquot ε ρ _hε _hρ
  obtain ⟨spec, hspec, hlimspec⟩ := hSpecExists
  refine ⟨fun R ↦ total R - spec R, ?_, ?_⟩
  · with_unfolding_all
      filter_upwards [htotal, hspec, _hρ] with R htotalR hspecR hcut
      obtain ⟨hcutT, hT, ht⟩ := htotalR
      obtain ⟨hcutS, hS, htS⟩ := hspecR
      obtain ⟨hT', hG, hS', hsplit⟩ := truncatedConvolution_trace_split (F := F) a hα hs hcut.1 hcut.2 φ hquot
      refine ⟨hcut.1, hG, ?_⟩
      apply sub_eq_iff_eq_add.mpr
      exact ht.trans (hsplit.trans (congrArg (fun z : ℂ ↦ _ + z) htS.symm))
  · have heq : (fun R ↦
        ((2 * Real.log R * (normOneIdeleClassTamagawaMeasure F).real univ : ℝ) : ℂ) * φ.val 1 - (total R - spec R)) =
        (fun R ↦ spec R - (total R - ((2 * Real.log R * (normOneIdeleClassTamagawaMeasure F).real univ : ℝ) : ℂ) * φ.val 1)) := by
      funext R
      ring
    have hh := hlimspec.sub hlimtotal
    simp only [sub_zero] at hh
    apply hh.congr'
    exact Filter.Eventually.of_forall (fun R ↦ (congrFun heq R).symm)

/-- Cyclicity transfers a nuclear trace across a continuous linear section. -/
private theorem spectralProjection_convolution_trace_transfer
    (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [PolynormableSpace ℂ E] [PolynormableSpace ℂ F]
    (J : E →L[ℂ] F) (hJ : Injective J) (Q : F →L[ℂ] E)
    (hQJ : Q.comp J = ContinuousLinearMap.id ℂ E) (A : E →L[ℂ] E) (hA : IsNuclearOperator A) :
    ∃ hB : IsNuclearOperator (J.comp (A.comp Q)),
      hilbertTrace ⟨J.comp (A.comp Q), hB⟩ = hilbertTrace ⟨A, hA⟩ := by
  have hAQ : IsNuclearOperator (A.comp Q) := by
    simpa using isNuclearOperator_comp_comp hA Q (ContinuousLinearMap.id ℂ E) injective_id
  have hrev : (A.comp Q).comp J = A := by
    rw [ContinuousLinearMap.comp_assoc, hQJ, ContinuousLinearMap.comp_id]
  have hn := isNuclearOperator_factor_comps J hJ (A.comp Q) hAQ
  refine ⟨hn.2, ?_⟩
  rw [hilbertTrace_eq_nuclearTrace, hilbertTrace_eq_nuclearTrace]
  have ht := nuclearTrace_factor_comps (hilbert_approximationProperty (H := E))
    (hilbert_approximationProperty (H := F)) J hJ (A.comp Q) hAQ
  simpa only [hrev] using ht.symm

/-- Paper: Proposition 10.4.2.4, p. 460. For degree at least three the trace of
untruncated spectral projection after convolution equals the quotient trace.
Both operators are nuclear. -/
theorem spectralProjection_convolution_trace (_hs3 : 3 ≤ s) (φ : BruhatCompactSupport C𝔽) :
    ∃ (hT : IsNuclearOperator ((Pspec).comp (A(φ)))) (hquot : quotientNuclear(φ)),
      hilbertTrace (H := W₀) ⟨(Pspec).comp (A(φ)), hT⟩ =
        hilbertTrace (H := H₀) ⟨Aₛ(φ), hquot⟩ := by
  have hquot : quotientNuclear(φ) := spectralStripConvolution_nuclear (F := F) a hα (by linarith) φ
  let J := (Θ₀).orthogonal.subtypeL.comp
    (Θ₀).quotientEquivOrthogonal.toContinuousLinearEquiv.toContinuousLinearMap
  have hJ : Injective J := Subtype.val_injective.comp (Θ₀).quotientEquivOrthogonal.injective
  have hQJ : (Qₐ).comp J = ContinuousLinearMap.id ℂ H₀ := by
    ext x
    exact (Θ₀).quotientEquivOrthogonal.symm_apply_apply x
  have hfactor : (Pspec).comp (A(φ)) = J.comp ((Aₛ(φ)).comp Qₐ) := spectralProjection_convolution_factor (F := F) a hα hs φ
  clear_value J
  have hresult : ∃ hB : IsNuclearOperator (J.comp ((Aₛ(φ)).comp Qₐ)),
      hilbertTrace ⟨J.comp ((Aₛ(φ)).comp Qₐ), hB⟩ = hilbertTrace ⟨Aₛ(φ), hquot⟩ := by
    with_unfolding_all exact spectralProjection_convolution_trace_transfer H₀ W₀ J hJ Qₐ hQJ (Aₛ(φ)) hquot
  obtain ⟨hB, ht⟩ := hresult
  have hT := spectralProjection_convolution_nuclear (F := F) a hα hs φ hquot
  refine ⟨hT, hquot, ?_⟩
  have heq : (⟨(Pspec).comp (A(φ)), hT⟩ : nuclearEndomorphisms W₀) =
      ⟨J.comp ((Aₛ(φ)).comp Qₐ), hB⟩ := Subtype.ext hfactor
  exact (congrArg hilbertTrace heq).trans ht

local notation "closedSpan(" u ")" => (Submodule.span ℂ (Set.range u)).topologicalClosure

section ApproximateLifts

variable {ι : Type*} [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  (E₀ V : Submodule ℂ E) [IsClosed (E₀ : Set E)]

/-- Paper: Lemma 10.4.2.5, p. 461. Biorthogonal quotient vectors lying in the
image of V admit lifts in V in the enlarged norm collar. Their coefficient
functionals are pulled back along the quotient map.
Deviation: This records the biorthogonal lift and the norm bounds. The claimed
Schauder conclusion fails even for Schauder input in Banach spaces. The caller
chooses the tolerance, as in (10.4.2.24). The strict collar and arbitrary index
type also cover the finite and empty families of §10.2. -/
theorem exists_biorthogonalBasisLift (x : ι → E ⧸ E₀) (f : ι → StrongDual ℂ (E ⧸ E₀))
    (_hbio : ∀ m n, f m (x n) = if m = n then 1 else 0)
    (r r' ε : ℝ) (_hr : 0 < r) (_hr' : 0 < r') (_hε : 0 < ε) (_hεr : ε < r)
    (_hcollar : ∀ m, ‖x m‖ ∈ Icc r r')
    (_hdense : E₀ ≤ (V ⊓ E₀).topologicalClosure) (_himage : ∀ m, x m ∈ V.map E₀.mkQ) :
    ∃ u : ι → E,
      (∀ m, u m ∈ V ∧ E₀.mkQ (u m) = x m ∧ ‖u m‖ ∈ Ioo (r - ε) (r' + ε)) ∧
      ∀ m n, f m (E₀.mkQ (u n)) = if m = n then 1 else 0 := by
  classical
  have lift (m : ι) : ∃ u : E, u ∈ V ∧ E₀.mkQ u = x m ∧ ‖u‖ ∈ Ioo (r - ε) (r' + ε) := by
    obtain ⟨v, hv, hqv⟩ := _himage m
    obtain ⟨z, hz, hn⟩ := Submodule.Quotient.norm_mk_lt (x m) (half_pos _hε)
    have hdiff : v - z ∈ E₀ := (Submodule.Quotient.mk_eq_zero _).mp (by
      change E₀.mkQ (v - z) = 0
      rw [map_sub, hqv, show E₀.mkQ z = x m from hz, sub_self])
    obtain ⟨d, hd, hdist⟩ := Metric.mem_closure_iff.mp (_hdense hdiff) (ε / 2) (half_pos _hε)
    have hqd : E₀.mkQ d = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hd.2
    have hqu : E₀.mkQ (v - d) = x m := by rw [map_sub, hqv, hqd, sub_zero]
    refine ⟨v - d, V.sub_mem hv hd.1, hqu, ?_, ?_⟩
    · have hu := Submodule.Quotient.norm_mk_le E₀ (v - d)
      change ‖E₀.mkQ (v - d)‖ ≤ _ at hu
      rw [hqu] at hu
      linarith [(_hcollar m).1]
    · rw [dist_eq_norm] at hdist
      have heq : v - d = z + (v - z - d) := by abel
      rw [heq]
      linarith [norm_add_le z (v - z - d), (_hcollar m).2]
  choose u hu using lift
  exact ⟨u, hu, fun m n ↦ (congrArg (f m) (hu n).2.1).trans (_hbio m n)⟩

private theorem exists_biorthogonalBasisLift_stable_coeff
    {ι : Type*} [DecidableEq ι]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (u : ι → E) (φ : ι → StrongDual ℂ E)
    (hbio : ∀ m n, φ m (u n) = if m = n then (1 : ℂ) else 0) (c : ι →₀ ℂ) (j : ι) :
    φ j (Finsupp.linearCombination ℂ u c) = c j := by
  rw [Finsupp.linearCombination_apply]
  unfold Finsupp.sum
  rw [map_sum]
  simp_rw [map_smul, hbio]
  rw [Finset.sum_eq_single j]
  · simp [smul_eq_mul]
  · intro i _ hij
    rw [ite_eq_right hij.symm]
    simp [smul_eq_mul]
  · intro hj
    simp [Finsupp.notMem_support_iff.mp hj, smul_eq_mul]

private theorem exists_biorthogonalBasisLift_stable_pert_le
    {ι : Type*} [DecidableEq ι]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (u y : ι → E) (φ : ι → StrongDual ℂ E)
    (hbio : ∀ m n, φ m (u n) = if m = n then (1 : ℂ) else 0) (δ : ι → ℝ)
    (hδ : ∀ m, 0 ≤ δ m) (hy : ∀ m, ‖y m‖ ≤ δ m) (hsum : Summable fun m => ‖φ m‖ * δ m)
    (c : ι →₀ ℂ) :
    ‖Finsupp.linearCombination ℂ y c‖ ≤
      (∑' m, ‖φ m‖ * δ m) * ‖Finsupp.linearCombination ℂ u c‖ := by
  have hcoeff (i : ι) :
      ‖c i‖ ≤ ‖φ i‖ * ‖Finsupp.linearCombination ℂ u c‖ := by
    have hcoe := exists_biorthogonalBasisLift_stable_coeff u φ hbio c i
    simpa [hcoe] using
      ContinuousLinearMap.le_opNorm (φ i) (Finsupp.linearCombination ℂ u c)
  rw [Finsupp.linearCombination_apply]
  unfold Finsupp.sum
  refine (norm_sum_le _ _).trans ?_
  have hstep₁ :
      ∑ i ∈ c.support, ‖c i • y i‖ ≤ ∑ i ∈ c.support, ‖c i‖ * δ i := by
    refine Finset.sum_le_sum fun i _ => ?_
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hy i) (norm_nonneg _)
  have hstep₂ :
      ∑ i ∈ c.support, ‖c i‖ * δ i ≤
        ∑ i ∈ c.support, (‖φ i‖ * ‖Finsupp.linearCombination ℂ u c‖) * δ i := by
    refine Finset.sum_le_sum fun i _ => ?_
    exact mul_le_mul_of_nonneg_right (hcoeff i) (hδ i)
  have hstep₃ :
      ∑ i ∈ c.support, (‖φ i‖ * ‖Finsupp.linearCombination ℂ u c‖) * δ i =
        (∑ i ∈ c.support, ‖φ i‖ * δ i) * ‖Finsupp.linearCombination ℂ u c‖ := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => by ring
  have hstep₄ :
      (∑ i ∈ c.support, ‖φ i‖ * δ i) * ‖Finsupp.linearCombination ℂ u c‖ ≤
        (∑' m, ‖φ m‖ * δ m) * ‖Finsupp.linearCombination ℂ u c‖ := by
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    exact hsum.sum_le_tsum c.support fun i _ => mul_nonneg (norm_nonneg _) (hδ i)
  exact hstep₁.trans <| hstep₂.trans <| hstep₃.le.trans hstep₄

private theorem exists_biorthogonalBasisLift_stable_denseRange
    {ι : Type*} [DecidableEq ι]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (u : ι → E) :
    ∃ e : (ι →₀ ℂ) →ₗ[ℂ] closedSpan(u),
      DenseRange e ∧ ∀ c, (e c : E) = Finsupp.linearCombination ℂ u c := by
  let S := closedSpan(u)
  let hmem : ∀ c : ι →₀ ℂ, Finsupp.linearCombination ℂ u c ∈ S := fun c =>
    (Submodule.span ℂ (Set.range u)).le_topologicalClosure <| by
      rw [← Finsupp.range_linearCombination]
      exact LinearMap.mem_range_self _ c
  refine ⟨(Finsupp.linearCombination ℂ u).codRestrict S hmem, ?_, fun c =>
    LinearMap.codRestrict_apply _ _ c⟩
  intro z
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hz : (z : E) ∈ closure (Submodule.span ℂ (Set.range u) : Set E) := by
    rw [← Submodule.topologicalClosure_coe]
    exact z.property
  obtain ⟨v, hv, hdist⟩ := Metric.mem_closure_iff.mp hz ε hε
  rw [SetLike.mem_coe, ← Finsupp.range_linearCombination] at hv
  obtain ⟨c, rfl⟩ := hv
  refine ⟨(Finsupp.linearCombination ℂ u).codRestrict S hmem c, mem_range_self _, ?_⟩
  rw [dist_eq_norm, ← Submodule.norm_coe, Submodule.coe_sub, LinearMap.codRestrict_apply]
  simpa [dist_eq_norm] using hdist

private theorem exists_biorthogonalBasisLift_stable_unique
    {ι : Type*} [DecidableEq ι]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (u y : ι → E) (φ : ι → StrongDual ℂ E)
    (hbio : ∀ m n, φ m (u n) = if m = n then (1 : ℂ) else 0) (δ : ι → ℝ)
    (hδ : ∀ m, 0 ≤ δ m) (hy : ∀ m, ‖y m‖ ≤ δ m) (hsum : Summable fun m => ‖φ m‖ * δ m)
    (hKlt : ∑' m, ‖φ m‖ * δ m < 1) :
    ∃! T : closedSpan(u) ≃L[ℂ] closedSpan(fun m ↦ u m + y m),
      ∀ (v : closedSpan(u)) (m : ι), v.val = u m → (T v).val = u m + y m := by
  let K := ∑' m, ‖φ m‖ * δ m
  have hK0 : 0 ≤ K := tsum_nonneg fun m => mul_nonneg (norm_nonneg _) (hδ m)
  have hK1 : 0 < 1 - K := by linarith
  obtain ⟨e₁, hdense₁, he₁⟩ := exists_biorthogonalBasisLift_stable_denseRange u
  obtain ⟨e₂, hdense₂, he₂⟩ :=
    exists_biorthogonalBasisLift_stable_denseRange fun m ↦ u m + y m
  have hadd (c : ι →₀ ℂ) :
      Finsupp.linearCombination ℂ u c + Finsupp.linearCombination ℂ y c =
        Finsupp.linearCombination ℂ (fun m ↦ u m + y m) c := by
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, smul_add, Finset.sum_add_distrib]
  have hpert (c : ι →₀ ℂ) :=
    exists_biorthogonalBasisLift_stable_pert_le u y φ hbio δ hδ hy hsum c
  have hup (c : ι →₀ ℂ) :
      ‖Finsupp.linearCombination ℂ (fun m ↦ u m + y m) c‖ ≤
        (1 + K) * ‖Finsupp.linearCombination ℂ u c‖ := by
    calc ‖Finsupp.linearCombination ℂ (fun m ↦ u m + y m) c‖
        = ‖Finsupp.linearCombination ℂ u c + Finsupp.linearCombination ℂ y c‖ := by rw [← hadd]
      _ ≤ ‖Finsupp.linearCombination ℂ u c‖ + ‖Finsupp.linearCombination ℂ y c‖ := norm_add_le _ _
      _ ≤ ‖Finsupp.linearCombination ℂ u c‖ + K * ‖Finsupp.linearCombination ℂ u c‖ :=
          add_le_add_right (hpert c) _
      _ = (1 + K) * ‖Finsupp.linearCombination ℂ u c‖ := by ring
  have hdown (c : ι →₀ ℂ) :
      (1 - K) * ‖Finsupp.linearCombination ℂ u c‖ ≤
        ‖Finsupp.linearCombination ℂ (fun m ↦ u m + y m) c‖ := by
    have htri :
        ‖Finsupp.linearCombination ℂ u c‖ ≤
          ‖Finsupp.linearCombination ℂ (fun m ↦ u m + y m) c‖ +
            ‖Finsupp.linearCombination ℂ y c‖ := by
      have : Finsupp.linearCombination ℂ u c =
          Finsupp.linearCombination ℂ (fun m ↦ u m + y m) c +
            (-Finsupp.linearCombination ℂ y c) := by
        rw [← hadd]
        abel
      rw [this]
      simpa using norm_add_le (Finsupp.linearCombination ℂ (fun m ↦ u m + y m) c)
        (-Finsupp.linearCombination ℂ y c)
    linarith [hpert c]
  have hnorm₁ : ∀ c, ‖e₂ c‖ ≤ (1 + K) * ‖e₁ c‖ := fun c => by
    rw [← Submodule.norm_coe (e₁ c), ← Submodule.norm_coe (e₂ c), he₁, he₂]
    exact hup c
  have hnorm₂ : ∀ c, ‖e₁ c‖ ≤ (1 - K)⁻¹ * ‖e₂ c‖ := fun c => by
    rw [← Submodule.norm_coe (e₁ c), ← Submodule.norm_coe (e₂ c), he₁, he₂]
    rw [← mul_le_mul_iff_of_pos_left hK1]
    calc (1 - K) * ‖Finsupp.linearCombination ℂ u c‖
        ≤ ‖Finsupp.linearCombination ℂ (fun m ↦ u m + y m) c‖ := hdown c
      _ = (1 - K) * ((1 - K)⁻¹ * ‖Finsupp.linearCombination ℂ (fun m ↦ u m + y m) c‖) := by
          rw [← mul_assoc, mul_inv_cancel₀ hK1.ne', one_mul]
  let fL := LinearEquiv.refl ℂ (ι →₀ ℂ)
  let T := fL.extend e₁ e₂ hdense₁ ⟨1 + K, hnorm₁⟩ hdense₂ ⟨(1 - K)⁻¹, hnorm₂⟩
  have hTgen : ∀ (v : closedSpan(u)) (m : ι), v.val = u m → (T v).val = u m + y m := by
    intro v m hv
    have hv' : v = e₁ (Finsupp.single m 1) := by
      apply Subtype.ext
      rw [he₁, Finsupp.linearCombination_single, one_smul]
      exact hv
    rw [hv', LinearEquiv.extend_eq, LinearEquiv.refl_apply]
    rw [he₂, Finsupp.linearCombination_single, one_smul]
  refine ⟨T, hTgen, ?_⟩
  intro T' hT'
  apply ContinuousLinearEquiv.coe_injective
  let s : Set (closedSpan(u)) := {v | ∃ m, (v : E) = u m}
  have hs : Dense (Submodule.span ℂ s : Set (closedSpan(u))) := by
    have hrange : Set.range e₁ ⊆ (Submodule.span ℂ s : Set _) := by
      intro z hz
      rcases hz with ⟨c, rfl⟩
      rw [← Finsupp.sum_single c, Finsupp.sum]
      rw [map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [← Finsupp.smul_single_one, map_smul]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      refine ⟨i, ?_⟩
      rw [he₁, Finsupp.linearCombination_single, one_smul]
    exact hdense₁.mono hrange
  apply ContinuousLinearMap.ext_on hs
  intro v hv
  obtain ⟨m, hm⟩ := hv
  apply Subtype.ext
  rw [ContinuousLinearEquiv.coe_apply, ContinuousLinearEquiv.coe_apply]
  rw [hTgen v m hm, hT' v m hm]

/-- Paper: Lemma 10.4.2.5, p. 461. Lifts can be chosen to remain inside the
enlarged collar under sufficiently small kernel perturbations. Each perturbed
family has canonically isomorphic closed span via the assignment on its generators.
Deviation: The perturbation conclusion uses biorthogonality and exact quotient
lifts, with no general Schauder claim. -/
theorem exists_biorthogonalBasisLift_stable [Countable ι] (x : ι → E ⧸ E₀)
    (f : ι → StrongDual ℂ (E ⧸ E₀))
    (_hbio : ∀ m n, f m (x n) = if m = n then 1 else 0)
    (r r' ε : ℝ) (_hr : 0 < r) (_hr' : 0 < r') (_hε : 0 < ε) (_hεr : ε < r)
    (_hcollar : ∀ m, ‖x m‖ ∈ Icc r r')
    (_hdense : E₀ ≤ (V ⊓ E₀).topologicalClosure) (_himage : ∀ m, x m ∈ V.map E₀.mkQ) :
    ∃ (u : ι → E) (δ : ι → ℝ), (∀ m, 0 < δ m) ∧
      (∀ m, u m ∈ V ∧ E₀.mkQ (u m) = x m ∧ ‖u m‖ ∈ Ioo (r - ε) (r' + ε)) ∧
      ∀ y : ι → E, (∀ m, y m ∈ V ⊓ E₀ ∧ ‖y m‖ < δ m) →
        (∀ m, u m + y m ∈ V ∧ E₀.mkQ (u m + y m) = x m ∧
          ‖u m + y m‖ ∈ Ioo (r - ε) (r' + ε)) ∧
        ∃! T : closedSpan(u) ≃L[ℂ] closedSpan(fun m ↦ u m + y m),
          ∀ (v : closedSpan(u)) (m : ι), v.val = u m → (T v).val = u m + y m := by
  obtain ⟨u, hu, _hbio'⟩ :=
    exists_biorthogonalBasisLift E₀ V x f _hbio r r' ε _hr _hr' _hε _hεr _hcollar _hdense _himage
  let φ : ι → StrongDual ℂ E := fun m => (f m).comp E₀.mkQL
  have hφ : ∀ m n, φ m (u n) = if m = n then (1 : ℂ) else 0 := fun m n => by
    rw [ContinuousLinearMap.comp_apply, Submodule.mkQL_apply, (hu n).2.1]
    exact _hbio m n
  let slack : ι → ℝ := fun m => min (‖u m‖ - (r - ε)) ((r' + ε) - ‖u m‖)
  have hslack : ∀ m, 0 < slack m := fun m => by
    have hm := (hu m).2.2
    rw [mem_Ioo] at hm
    exact lt_min (sub_pos.mpr hm.1) (sub_pos.mpr hm.2)
  obtain ⟨ε', hε'pos, c, hc, hclt⟩ := NNReal.exists_pos_sum_of_countable (ε := 1) one_ne_zero ι
  let δ : ι → ℝ := fun m => min (slack m) ((ε' m : ℝ) / (1 + ‖φ m‖))
  have hδpos : ∀ m, 0 < δ m := fun m =>
    lt_min (hslack m) (div_pos (NNReal.coe_pos.mpr (hε'pos m)) (by positivity : 0 < 1 + ‖φ m‖))
  have hterm : ∀ m, ‖φ m‖ * δ m ≤ (ε' m : ℝ) := fun m => by
    have hfrac : ‖φ m‖ / (1 + ‖φ m‖) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [norm_nonneg (φ m)]
    calc ‖φ m‖ * δ m
        ≤ ‖φ m‖ * ((ε' m : ℝ) / (1 + ‖φ m‖)) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) (norm_nonneg _)
      _ = (ε' m : ℝ) * (‖φ m‖ / (1 + ‖φ m‖)) := by ring
      _ ≤ (ε' m : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hfrac (NNReal.coe_nonneg _)
      _ = (ε' m : ℝ) := mul_one _
  have hsumε : Summable fun m => (ε' m : ℝ) := NNReal.summable_coe.mpr hc.summable
  have hsum : Summable fun m => ‖φ m‖ * δ m :=
    Summable.of_nonneg_of_le (fun m => mul_nonneg (norm_nonneg _) (hδpos m).le) hterm hsumε
  have hK : ∑' m, ‖φ m‖ * δ m < 1 := by
    have hle := hsum.tsum_le_tsum hterm hsumε
    have heq : ∑' m, (ε' m : ℝ) = (c : ℝ) := (NNReal.hasSum_coe.mpr hc).tsum_eq
    have hc1 : (c : ℝ) < 1 := NNReal.coe_lt_coe.mpr hclt
    linarith
  refine ⟨u, δ, hδpos, hu, ?_⟩
  intro y hy
  have hyδ : ∀ m, ‖y m‖ ≤ δ m := fun m => (hy m).2.le
  have hδ0 : ∀ m, 0 ≤ δ m := fun m => (hδpos m).le
  refine ⟨fun m => ?_, exists_biorthogonalBasisLift_stable_unique u y φ hφ δ hδ0 hyδ hsum hK⟩
  have hym := hy m
  rw [Submodule.mem_inf] at hym
  refine ⟨V.add_mem (hu m).1 hym.1.1, ?_, ?_⟩
  · have hy0 : E₀.mkQ (y m) = 0 := by
      rw [Submodule.mkQ_apply]
      exact (Submodule.Quotient.mk_eq_zero _).mpr hym.1.2
    rw [map_add, (hu m).2.1, hy0, add_zero]
  · have habs := abs_norm_sub_norm_le (u m + y m) (u m)
    have hsub : (u m + y m) - u m = y m := by abel
    rw [hsub] at habs
    have hm := (hu m).2.2
    rw [mem_Ioo] at hm
    have hlow : ‖u m‖ - ‖y m‖ ≤ ‖u m + y m‖ := by linarith [abs_le.mp habs]
    have hupp : ‖u m + y m‖ ≤ ‖u m‖ + ‖y m‖ := norm_add_le _ _
    have hδlow : δ m ≤ ‖u m‖ - (r - ε) := (min_le_left _ _).trans (min_le_left _ _)
    have hδup : δ m ≤ (r' + ε) - ‖u m‖ := (min_le_left _ _).trans (min_le_right _ _)
    rw [mem_Ioo]
    constructor
    · linarith [hym.2]
    · linarith [hym.2]

/-- Paper: Terminology 10.4.2.1, p. 462. An ε-lift lies in the specified
subspace, represents the given quotient vectors, has the prescribed pulled-back
coefficient values, and stays in the enlarged norm collar.
Deviation: Exact representation is explicit. Totality gives it from the
coefficient equations for the bases in the paper. -/
def IsEpsilonBasisLift (x : ι → E ⧸ E₀) (f : ι → StrongDual ℂ (E ⧸ E₀))
    (r r' ε : ℝ) (u : ι → E) : Prop :=
  0 < ε ∧ ε < r ∧ (∀ m, u m ∈ V ∧ E₀.mkQ (u m) = x m ∧ ‖u m‖ ∈ Icc (r - ε) (r' + ε)) ∧
    ∀ m n, f m (E₀.mkQ (u n)) = if m = n then 1 else 0

/-- Paper: Terminology 10.4.2.1, p. 462. A lift of a biorthogonal family with
the required collar bounds satisfies the ε-lift conditions. -/
theorem isEpsilonBasisLift_of_mkQ_eq (x : ι → E ⧸ E₀) (f : ι → StrongDual ℂ (E ⧸ E₀))
    (_hbio : ∀ m n, f m (x n) = if m = n then 1 else 0)
    {r r' ε : ℝ} (_hε : 0 < ε) (_hεr : ε < r)
    (u : ι → E) (_hu : ∀ m, u m ∈ V ∧ E₀.mkQ (u m) = x m ∧
      ‖u m‖ ∈ Icc (r - ε) (r' + ε)) :
    IsEpsilonBasisLift E₀ V x f r r' ε u := by
  refine ⟨_hε, _hεr, _hu, fun m n ↦ ?_⟩
  exact (congrArg (f m) (_hu n).2.1).trans (_hbio m n)

/-- Paper: Remark 10.4.2.6, p. 463. The image of the open unit ball under
the quotient map is exactly the open unit ball in the quotient norm. -/
theorem quotient_image_openUnitBall :
    E₀.mkQ '' Metric.ball 0 1 = Metric.ball 0 1 := by
  ext y
  simp only [Set.mem_image, Metric.mem_ball, dist_zero_right]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (Submodule.Quotient.norm_mk_le E₀ x).trans_lt hx
  · intro hy
    obtain ⟨x, hxy, hx⟩ := Submodule.Quotient.norm_mk_lt y (sub_pos.mpr hy)
    exact ⟨x, by linarith, hxy⟩

private theorem quotient_image_closedUnitBall_of_reflexive_bidual_coe (w : WeakSpace ℂ E) :
    NormedSpace.inclusionInDoubleDualWeak ℂ E w =
      (NormedSpace.inclusionInDoubleDual ℂ E ((toWeakSpace ℂ E).symm w)).toWeakDual := by
  refine DFunLike.ext _ _ fun ψ => ?_
  rw [StrongDual.toWeakDual_apply]
  change (NormedSpace.inclusionInDoubleDualWeak ℂ E).toLinearMap w ψ = ψ ((toWeakSpace ℂ E).symm w)
  rw [NormedSpace.toLinearMap_inclusionInDoubleDualWeak, LinearEquiv.arrowCongr_apply,
    StrongDual.toWeakDual_apply]
  exact NormedSpace.dual_def ℂ E ((toWeakSpace ℂ E).symm w) ψ

private theorem quotient_image_closedUnitBall_of_reflexive_norm_bidual (x : E) :
    ‖NormedSpace.inclusionInDoubleDual ℂ E x‖ = ‖x‖ :=
  (NormedSpace.inclusionInDoubleDualLi ℂ (E := E)).norm_map x

private theorem quotient_image_closedUnitBall_of_reflexive_isClosed_ball (r : ℝ) :
    IsClosed ((toWeakSpace ℂ E) '' Metric.closedBall (0 : E) r) := by
  classical
  by_cases hr : 0 ≤ r
  · have himage :
        (toWeakSpace ℂ E) '' Metric.closedBall (0 : E) r =
          {w : WeakSpace ℂ E | ‖(toWeakSpace ℂ E).symm w‖ ≤ r} := by
      ext w
      constructor
      · rintro ⟨y, hy, rfl⟩
        rw [Metric.mem_closedBall, dist_zero_right] at hy
        change ‖(toWeakSpace ℂ E).symm ((toWeakSpace ℂ E) y)‖ ≤ r
        rw [LinearEquiv.symm_apply_apply]
        exact hy
      · intro hw
        refine ⟨(toWeakSpace ℂ E).symm w, ?_, (toWeakSpace ℂ E).apply_symm_apply w⟩
        rw [Metric.mem_closedBall, dist_zero_right]
        exact hw
    let ι : WeakSpace ℂ E →L[ℂ] WeakDual ℂ (StrongDual ℂ E) := NormedSpace.inclusionInDoubleDualWeak ℂ E
    have hpre : IsClosed
        (ι ⁻¹' (WeakDual.toStrongDual (𝕜 := ℂ) (E := StrongDual ℂ E) ⁻¹'
          Metric.closedBall (0 : StrongDual ℂ (StrongDual ℂ E)) r)) :=
      (WeakDual.isClosed_closedBall (0 : StrongDual ℂ (StrongDual ℂ E)) r).preimage ι.continuous
    have heq :
        {w : WeakSpace ℂ E | ‖(toWeakSpace ℂ E).symm w‖ ≤ r} =
          ι ⁻¹' (WeakDual.toStrongDual (𝕜 := ℂ) (E := StrongDual ℂ E) ⁻¹'
            Metric.closedBall (0 : StrongDual ℂ (StrongDual ℂ E)) r) := by
      ext w
      simp only [ι, mem_ofPred_eq, mem_preimage, Metric.mem_closedBall, dist_zero_right]
      rw [quotient_image_closedUnitBall_of_reflexive_bidual_coe,
        StrongDual.toStrongDual_toWeakDual,
        quotient_image_closedUnitBall_of_reflexive_norm_bidual]
    exact himage ▸ heq ▸ hpre
  · rw [Metric.closedBall_eq_empty.mpr (lt_of_not_ge hr), image_empty]
    exact isClosed_empty

private theorem quotient_image_closedUnitBall_of_reflexive_surjective_weak
    (hE : Function.Surjective (NormedSpace.inclusionInDoubleDual ℂ E)) :
    Function.Surjective (NormedSpace.inclusionInDoubleDualWeak ℂ E) := by
  intro w
  obtain ⟨φ, rfl⟩ := (StrongDual.toWeakDual (E := StrongDual ℂ E)).surjective w
  obtain ⟨x, hx⟩ := hE φ
  refine ⟨toWeakSpace ℂ E x, ?_⟩
  rw [quotient_image_closedUnitBall_of_reflexive_bidual_coe, LinearEquiv.symm_apply_apply, hx]

private theorem quotient_image_closedUnitBall_of_reflexive_isCompact_ball
    (hE : Function.Surjective (NormedSpace.inclusionInDoubleDual ℂ E)) (r : ℝ) :
    IsCompact ((toWeakSpace ℂ E) '' Metric.closedBall (0 : E) r) := by
  let S : Set (WeakSpace ℂ E) := (toWeakSpace ℂ E) '' Metric.closedBall (0 : E) r
  have hclosed : IsClosed S := quotient_image_closedUnitBall_of_reflexive_isClosed_ball r
  have hb : Bornology.IsBounded ((toWeakSpace ℂ E) ⁻¹' S) := by
    have : (toWeakSpace ℂ E) ⁻¹' S = Metric.closedBall (0 : E) r := by
      ext z
      constructor
      · intro hz
        obtain ⟨y, hy, heq⟩ := hz
        have : z = y := (toWeakSpace ℂ E).injective heq.symm
        rw [this]
        exact hy
      · intro hz
        exact ⟨z, hz, rfl⟩
    simpa [this] using Metric.isBounded_closedBall
  have hrange :
      closure (NormedSpace.inclusionInDoubleDualWeak ℂ E '' S) ⊆
        range (NormedSpace.inclusionInDoubleDualWeak ℂ E) := by
    rw [(quotient_image_closedUnitBall_of_reflexive_surjective_weak hE).range_eq]
    exact subset_univ _
  have hcomp := NormedSpace.isCompact_closure_of_isBounded (𝕜 := ℂ) (X := E) S hb hrange
  simpa [S, hclosed.closure_eq] using hcomp

private theorem quotient_image_closedUnitBall_of_reflexive_map_mkQ
    (E₀ : Submodule ℂ E) [IsClosed (E₀ : Set E)] (w : WeakSpace ℂ E) :
    WeakSpace.map E₀.mkQL w =
      (E₀.mkQ ((toWeakSpace ℂ E).symm w) : WeakSpace ℂ (E ⧸ E₀)) := by
  have hw : toWeakSpace ℂ E ((toWeakSpace ℂ E).symm w) = w :=
    (toWeakSpace ℂ E).apply_symm_apply w
  rw [← hw]
  exact WeakSpace.map_apply E₀.mkQL ((toWeakSpace ℂ E).symm w)

private theorem quotient_image_closedUnitBall_of_reflexive_isClosed_fiber
    (E₀ : Submodule ℂ E) [IsClosed (E₀ : Set E)] (y : E ⧸ E₀) :
    IsClosed {w : WeakSpace ℂ E | E₀.mkQ ((toWeakSpace ℂ E).symm w) = y} := by
  have hpre : IsClosed
      ((WeakSpace.map E₀.mkQL) ⁻¹' {toWeakSpace ℂ (E ⧸ E₀) y}) :=
    isClosed_singleton.preimage (WeakSpace.map E₀.mkQL).continuous
  have heq :
      {w : WeakSpace ℂ E | E₀.mkQ ((toWeakSpace ℂ E).symm w) = y} =
        (WeakSpace.map E₀.mkQL) ⁻¹' {toWeakSpace ℂ (E ⧸ E₀) y} := by
    ext w
    simp only [mem_ofPred_eq, mem_preimage, mem_singleton_iff]
    rw [quotient_image_closedUnitBall_of_reflexive_map_mkQ]
    exact (toWeakSpace ℂ (E ⧸ E₀)).injective.eq_iff
  exact heq ▸ hpre

/-- Paper: Remark 10.4.2.6, p. 463. In a reflexive Banach space the quotient
map also takes the closed unit ball onto the closed unit ball. -/
theorem quotient_image_closedUnitBall_of_reflexive
    (_hE : Surjective (NormedSpace.inclusionInDoubleDual ℂ E)) :
    E₀.mkQ '' Metric.closedBall 0 1 = Metric.closedBall 0 1 := by
  classical
  ext y
  simp only [mem_image, Metric.mem_closedBall, dist_zero_right]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (Submodule.Quotient.norm_mk_le E₀ x).trans hx
  · intro hy
    by_cases hy1 : ‖y‖ < 1
    · obtain ⟨m, hm, hlt⟩ := Submodule.Quotient.norm_mk_lt y (sub_pos.mpr hy1)
      exact ⟨m, (lt_of_le_of_lt le_rfl (by linarith : ‖m‖ < 1)).le, hm⟩
    · have hyeq : ‖y‖ = 1 := le_antisymm hy (le_of_not_gt hy1)
      let S : ℕ → Set (WeakSpace ℂ E) := fun n =>
        {w | E₀.mkQ ((toWeakSpace ℂ E).symm w) = y ∧
          ‖(toWeakSpace ℂ E).symm w‖ ≤ 1 + 1 / (n + 1 : ℝ)}
      have hSclosed (n : ℕ) : IsClosed (S n) := by
        have hball : IsClosed
            ((toWeakSpace ℂ E) '' Metric.closedBall (0 : E) (1 + 1 / (n + 1 : ℝ))) :=
          quotient_image_closedUnitBall_of_reflexive_isClosed_ball _
        have hfiber : IsClosed
            {w : WeakSpace ℂ E | E₀.mkQ ((toWeakSpace ℂ E).symm w) = y} :=
          quotient_image_closedUnitBall_of_reflexive_isClosed_fiber E₀ y
        have heq : S n =
            {w | E₀.mkQ ((toWeakSpace ℂ E).symm w) = y} ∩
              ((toWeakSpace ℂ E) '' Metric.closedBall (0 : E) (1 + 1 / (n + 1 : ℝ))) := by
          ext w
          constructor
          · rintro ⟨hmap, hnorm⟩
            refine ⟨hmap, (toWeakSpace ℂ E).symm w, ?_, (toWeakSpace ℂ E).apply_symm_apply w⟩
            rwa [Metric.mem_closedBall, dist_zero_right]
          · rintro ⟨hmap, z, hnorm, hz⟩
            have hmap' : E₀.mkQ ((toWeakSpace ℂ E).symm w) = y := by
              simpa only [mem_ofPred_eq] using hmap
            have hzE : (toWeakSpace ℂ E).symm w = z := by
              have hsym := congrArg (toWeakSpace ℂ E).symm hz
              rw [LinearEquiv.symm_apply_apply] at hsym
              exact hsym.symm
            rw [hzE] at hmap'
            rw [Metric.mem_closedBall, dist_zero_right] at hnorm
            change E₀.mkQ ((toWeakSpace ℂ E).symm w) = y ∧
              ‖(toWeakSpace ℂ E).symm w‖ ≤ 1 + 1 / (n + 1 : ℝ)
            rw [hzE]
            exact ⟨hmap', hnorm⟩
        exact heq ▸ hfiber.inter hball
      have hradius (n : ℕ) : 1 + 1 / (n + 1 : ℝ) ≤ 2 := by
        have hdiv : 1 / (n + 1 : ℝ) ≤ 1 := by
          rw [div_le_one (by positivity)]
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
        linarith
      have hScompact (n : ℕ) : IsCompact (S n) :=
        (quotient_image_closedUnitBall_of_reflexive_isCompact_ball _hE 2).of_isClosed_subset
          (hSclosed n) <| by
          intro w hw
          refine ⟨(toWeakSpace ℂ E).symm w, ?_, (toWeakSpace ℂ E).apply_symm_apply w⟩
          rw [Metric.mem_closedBall, dist_zero_right]
          exact hw.2.trans (hradius n)
      have hSnonempty (n : ℕ) : (S n).Nonempty := by
        obtain ⟨m, hm, hlt⟩ := Submodule.Quotient.norm_mk_lt y
          (one_div_pos.mpr (Nat.cast_add_one_pos n))
        rw [hyeq] at hlt
        refine ⟨toWeakSpace ℂ E m, ?_, ?_⟩
        · rw [LinearEquiv.symm_apply_apply]
          exact hm
        · rw [LinearEquiv.symm_apply_apply]
          exact hlt.le
      have hsucc (n : ℕ) : S (n + 1) ⊆ S n := by
        intro w hw
        refine ⟨hw.1, hw.2.trans ?_⟩
        have hdiv : (1 : ℝ) / (↑(n + 1) + 1) ≤ 1 / (↑n + 1) :=
          one_div_le_one_div_of_le
            (by positivity : (0 : ℝ) < (↑n + 1))
            (by exact_mod_cast Nat.le_succ (n + 1))
        exact add_le_add_right hdiv 1
      obtain ⟨x, hx⟩ :=
        IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hsucc
          hSnonempty (hScompact 0) hSclosed
      have hxall (n : ℕ) :
          E₀.mkQ ((toWeakSpace ℂ E).symm x) = y ∧
            ‖(toWeakSpace ℂ E).symm x‖ ≤ 1 + 1 / (n + 1 : ℝ) :=
        mem_iInter.mp hx n
      refine ⟨(toWeakSpace ℂ E).symm x, ?_, (hxall 0).1⟩
      refine le_of_forall_pos_le_add fun ε hε => ?_
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
      refine (hxall n).2.trans (le_of_lt ?_)
      rw [add_comm (1 : ℝ) (1 / (n + 1 : ℝ)), add_comm (1 : ℝ) ε]
      exact add_lt_add_left hn 1

-- The Schauder conclusion of Lemma 10.4.2.5 is false even for a Schauder
-- quotient basis. See the convergent-sequence example in the printed file.
-- The upper bound r' - ε/2 in the proof on p. 462 should be r' + ε/2.
-- The Hilbert-space repair below uses exact image membership.

end ApproximateLifts

private theorem exists_hilbertBasisLift_closedSpan_equiv_map
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (e : X ≃L[ℂ] Y) (b : _root_.SchauderBasis ℂ X) :
    ∃ B : _root_.SchauderBasis ℂ Y,
      (∀ n, B n = e (b n)) ∧
      (∀ n, B.coord n = (b.coord n).comp e.symm.toContinuousLinearMap) := by
  let S := e.symm.toContinuousLinearMap
  let T := e.toContinuousLinearMap
  refine ⟨{
    basis := fun n => e (b n)
    coord := fun n => (b.coord n).comp S
    ortho := by intro i j; simpa [S] using b.ortho i j
    expansion := by
      intro y
      have hh := T.hasSum (b.expansion (e.symm y))
      simpa [T, S] using hh }, fun _ => rfl, fun _ => rfl⟩

private theorem exists_hilbertBasisLift_closedSpan_equiv_orthogonal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (E₀ : Submodule ℂ E) [IsClosed (E₀ : Set E)]
    (b : _root_.SchauderBasis ℂ (E ⧸ E₀)) :
    ∃ B : _root_.SchauderBasis ℂ ↥E₀.orthogonal,
      ∀ m, (B m : E) = (E₀.quotientEquivOrthogonal (b m) : E) ∧
        E₀.mkQ (B m : E) = b m ∧ ‖(B m : E)‖ = ‖b m‖ := by
  let e := E₀.quotientEquivOrthogonal.toContinuousLinearEquiv
  obtain ⟨B, hB, _⟩ := exists_hilbertBasisLift_closedSpan_equiv_map e b
  refine ⟨B, fun m => ?_⟩
  have hval : (B m : E) = (E₀.quotientEquivOrthogonal (b m) : E) := by
    rw [hB, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  refine ⟨hval, ?_, ?_⟩
  · rw [hval, Submodule.mkQ_apply]
    exact (E₀.quotientEquivOrthogonal_symm_eq_mk _ (E₀.quotientEquivOrthogonal (b m)).property).symm.trans
      (E₀.quotientEquivOrthogonal.symm_apply_apply (b m))
  · rw [hval, Submodule.norm_coe]
    exact E₀.quotientEquivOrthogonal.norm_map _

private theorem exists_hilbertBasisLift_closedSpan_equiv_dense
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Q : Submodule ℂ E) (B : _root_.SchauderBasis ℂ Q) :
    ∃ e : (ℕ →₀ ℂ) →ₗ[ℂ] Q,
      DenseRange e ∧ ∀ c, (e c : E) = Finsupp.linearCombination ℂ (fun m => (B m : E)) c := by
  have hmem : ∀ c : ℕ →₀ ℂ, Finsupp.linearCombination ℂ (fun m => (B m : E)) c ∈ Q := fun c => by
    have hspan : Submodule.span ℂ (Set.range fun m => (B m : E)) ≤ Q :=
      Submodule.span_le.mpr (by rintro _ ⟨m, rfl⟩; exact (B m).property)
    exact hspan <| by
      rw [← Finsupp.range_linearCombination]
      exact LinearMap.mem_range_self _ c
  refine ⟨(Finsupp.linearCombination ℂ (fun m => (B m : E))).codRestrict Q hmem, ?_,
    fun c => LinearMap.codRestrict_apply _ _ c⟩
  intro q
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp (B.tendsto_proj q)) ε hε
  let c : ℕ →₀ ℂ := ∑ i ∈ Finset.range N, Finsupp.single i (B.coord i q)
  have hEq : (Finsupp.linearCombination ℂ (fun m => (B m : E))).codRestrict Q hmem c =
      B.proj N q := by
    apply Subtype.ext
    rw [LinearMap.codRestrict_apply, map_sum]
    simp_rw [Finsupp.linearCombination_single]
    simp [SchauderBasis.proj_apply]
  refine ⟨(Finsupp.linearCombination ℂ (fun m => (B m : E))).codRestrict Q hmem c,
    mem_range_self _, ?_⟩
  rw [hEq, dist_comm]
  exact hN N le_rfl

private theorem exists_hilbertBasisLift_closedSpan_equiv_perturb
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (E₀ V : Submodule ℂ E) (o v : ℕ → E)
    (hv : ∀ m, v m ∈ V ∧ E₀.mkQ (v m) = E₀.mkQ (o m))
    (hdense : E₀ ≤ (V ⊓ E₀).topologicalClosure)
    (η : ℕ → ℝ) (hη : ∀ m, 0 < η m) :
    ∃ u : ℕ → E, ∀ m, u m ∈ V ∧ E₀.mkQ (u m) = E₀.mkQ (o m) ∧
      u m - o m ∈ E₀ ∧ ‖u m - o m‖ < η m := by
  have hex : ∀ m, ∃ w : E, w ∈ V ∧ E₀.mkQ w = E₀.mkQ (o m) ∧
      w - o m ∈ E₀ ∧ ‖w - o m‖ < η m := fun m => by
    have hdiff : v m - o m ∈ E₀ := by
      have hmk : E₀.mkQ (v m) = E₀.mkQ (o m) := (hv m).2
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hmk
      exact hmk
    have hcl : v m - o m ∈ (V ⊓ E₀).topologicalClosure := hdense hdiff
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hcl
    obtain ⟨d, hd, hdist⟩ := Metric.mem_closure_iff.mp hcl (η m) (hη m)
    rw [SetLike.mem_coe, Submodule.mem_inf] at hd
    have hd0 : E₀.mkQ d = 0 := by
      rw [Submodule.mkQ_apply]
      exact (Submodule.Quotient.mk_eq_zero _).mpr hd.2
    refine ⟨v m - d, V.sub_mem (hv m).1 hd.1, ?_, ?_, ?_⟩
    · rw [map_sub, (hv m).2, hd0, sub_zero]
    · have : (v m - d) - o m = (v m - o m) - d := by abel
      rw [this]
      exact E₀.sub_mem hdiff hd.2
    · have : (v m - d) - o m = (v m - o m) - d := by abel
      rw [this, ← dist_eq_norm]
      exact hdist
  exact ⟨fun m => Classical.choose (hex m), fun m => Classical.choose_spec (hex m)⟩

/-- Paper: Remark 10.4.2.7, p. 463. In a Hilbert space, collar lifts in V
can be chosen so that their closed span is isomorphic to the orthogonal
complement of the kernel.
Deviation: The quotient basis vectors are required to lie in the exact
image of V as in Lemma 10.4.2.5. The perturbations use the same chosen lift. -/
theorem exists_hilbertBasisLift_closedSpan_equiv {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (E₀ V : Submodule ℂ E) [IsClosed (E₀ : Set E)]
    (b : _root_.SchauderBasis ℂ (E ⧸ E₀)) (r r' : ℝ) (_hr : 0 < r) (_hr' : 0 < r')
    (_hcollar : ∀ m, ‖b m‖ ∈ Icc r r')
    (_hdense : E₀ ≤ (V ⊓ E₀).topologicalClosure) (_himage : ∀ m, b m ∈ V.map E₀.mkQ) :
    ∃ (u : ℕ → E) (ε : ℝ), IsEpsilonBasisLift E₀ V b.basis b.coord r r' ε u ∧
      (∃ B : _root_.SchauderBasis ℂ (closedSpan(u)), ∀ m, (B m).val = u m) ∧
      Nonempty (closedSpan(u) ≃L[ℂ] E₀.orthogonal) ∧
      ∃ δ : ℕ → ℝ, (∀ m, 0 < δ m) ∧
        ∀ y : ℕ → E, (∀ m, y m ∈ V ⊓ E₀ ∧ ‖y m‖ < δ m) →
          IsEpsilonBasisLift E₀ V b.basis b.coord r r' ε (fun m ↦ u m + y m) ∧
          ∃! T : closedSpan(u) ≃L[ℂ] closedSpan(fun m ↦ u m + y m),
            ∀ (v : closedSpan(u)) (m : ℕ), v.val = u m → (T v).val = u m + y m := by
  let ε : ℝ := r / 2
  have hε : 0 < ε := by positivity
  have hεr : ε < r := half_lt_self _hr
  obtain ⟨B, hB⟩ := exists_hilbertBasisLift_closedSpan_equiv_orthogonal E₀ b
  let o : ℕ → E := fun m => (B m : E)
  let φ : ℕ → StrongDual ℂ E := fun m =>
    (B.coord m).comp E₀.orthogonal.orthogonalProjectionOnto
  have hφo : ∀ m n, φ m (o n) = if m = n then (1 : ℂ) else 0 := fun m n => by
    have hfix : E₀.orthogonal.orthogonalProjectionOnto (o n) = B n := by
      simp [o]
    simp only [φ, ContinuousLinearMap.comp_apply, hfix]
    by_cases hmn : m = n
    · simp [hmn, B.ortho, Pi.single_eq_same]
    · simp [hmn, B.ortho]
  obtain ⟨ε', hε'pos, c0, hc0, hc0lt⟩ :=
    NNReal.exists_pos_sum_of_countable (ε := 1) one_ne_zero ℕ
  let η : ℕ → ℝ := fun m => min (ε / 2) ((ε' m : ℝ) / (1 + ‖φ m‖))
  have hηpos : ∀ m, 0 < η m := fun m =>
    lt_min (by positivity) (div_pos (NNReal.coe_pos.mpr (hε'pos m)) (by positivity : 0 < 1 + ‖φ m‖))
  have hηle : ∀ m, η m ≤ ε / 2 := fun m => min_le_left _ _
  have hη0 : ∀ m, 0 ≤ η m := fun m => (hηpos m).le
  have hterm : ∀ m, ‖φ m‖ * η m ≤ (ε' m : ℝ) := fun m => by
    have hfrac : ‖φ m‖ / (1 + ‖φ m‖) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [norm_nonneg (φ m)]
    calc ‖φ m‖ * η m
        ≤ ‖φ m‖ * ((ε' m : ℝ) / (1 + ‖φ m‖)) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) (norm_nonneg _)
      _ = (ε' m : ℝ) * (‖φ m‖ / (1 + ‖φ m‖)) := by ring
      _ ≤ (ε' m : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hfrac (NNReal.coe_nonneg _)
      _ = (ε' m : ℝ) := mul_one _
  have hsumε' : Summable fun m => (ε' m : ℝ) := NNReal.summable_coe.mpr hc0.summable
  have hsumη : Summable fun m => ‖φ m‖ * η m :=
    Summable.of_nonneg_of_le (fun m => mul_nonneg (norm_nonneg _) (hη0 m)) hterm hsumε'
  have hKη : ∑' m, ‖φ m‖ * η m < 1 := by
    have hle := hsumη.tsum_le_tsum hterm hsumε'
    have heq : ∑' m, (ε' m : ℝ) = (c0 : ℝ) := (NNReal.hasSum_coe.mpr hc0).tsum_eq
    have hc1 : (c0 : ℝ) < 1 := NNReal.coe_lt_coe.mpr hc0lt
    linarith
  choose v hvmem using fun m => (Submodule.mem_map).mp (_himage m)
  have hv : ∀ m, v m ∈ V ∧ E₀.mkQ (v m) = E₀.mkQ (o m) := fun m =>
    ⟨(hvmem m).1, (hvmem m).2.trans (hB m).2.1.symm⟩
  obtain ⟨u, hu⟩ :=
    exists_hilbertBasisLift_closedSpan_equiv_perturb E₀ V o v hv _hdense η hηpos
  let z : ℕ → E := fun m => u m - o m
  have hzlt : ∀ m, ‖z m‖ < η m := fun m => by simpa [z] using (hu m).2.2.2
  have hzle : ∀ m, ‖z m‖ ≤ η m := fun m => (hzlt m).le
  have hcollar_u : ∀ m, ‖u m‖ ∈ Ioo (r - ε) (r' + ε) := fun m => by
    have hm := mem_Icc.mp (_hcollar m)
    have hlow : ‖o m‖ - ‖z m‖ ≤ ‖u m‖ := by
      have habs := abs_norm_sub_norm_le (u m) (o m)
      have hsub : u m - o m = z m := rfl
      rw [hsub] at habs
      linarith [abs_le.mp habs]
    have hupp : ‖u m‖ ≤ ‖o m‖ + ‖z m‖ := by
      have hzdef : z m = u m - o m := rfl
      have : u m = o m + z m := by rw [hzdef]; abel
      rw [this]
      exact norm_add_le _ _
    have hzn : ‖z m‖ < ε / 2 := lt_of_lt_of_le (hzlt m) (hηle m)
    rw [mem_Ioo]
    constructor
    · linarith [hm.1, (hB m).2.2, hzn, hε]
    · linarith [hm.2, (hB m).2.2, hzn, hε]
  have hbio : ∀ m n, b.coord m (b.basis n) = if m = n then (1 : ℂ) else 0 := fun m n => by
    by_cases hmn : m = n
    · simp [hmn, b.ortho, Pi.single_eq_same]
    · simp [hmn, b.ortho]
  have hu_lift : ∀ m, u m ∈ V ∧ E₀.mkQ (u m) = b m ∧ ‖u m‖ ∈ Icc (r - ε) (r' + ε) :=
    fun m => by
      have hm := hcollar_u m
      rw [mem_Ioo] at hm
      exact ⟨(hu m).1, (hu m).2.1.trans (hB m).2.1, mem_Icc.mpr ⟨hm.1.le, hm.2.le⟩⟩
  have hlift : IsEpsilonBasisLift E₀ V b.basis b.coord r r' ε u :=
    isEpsilonBasisLift_of_mkQ_eq E₀ V b.basis b.coord hbio hε hεr u hu_lift
  obtain ⟨eQ, hdenseQ, heQ⟩ := exists_hilbertBasisLift_closedSpan_equiv_dense E₀.orthogonal B
  have heQ' : ∀ c, (eQ c : E) = Finsupp.linearCombination ℂ o c := fun c => by
    simpa [o] using heQ c
  obtain ⟨eU, hdenseU, heU⟩ := exists_biorthogonalBasisLift_stable_denseRange u
  let K := ∑' m, ‖φ m‖ * η m
  have hK1 : 0 < 1 - K := by
    have hK0 : 0 ≤ K := tsum_nonneg fun m => mul_nonneg (norm_nonneg _) (hη0 m)
    linarith
  have hpert (c : ℕ →₀ ℂ) :=
    exists_biorthogonalBasisLift_stable_pert_le o z φ hφo η hη0 hzle hsumη c
  have hadd (c : ℕ →₀ ℂ) :
      Finsupp.linearCombination ℂ o c + Finsupp.linearCombination ℂ z c =
        Finsupp.linearCombination ℂ (fun m => o m + z m) c := by
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, smul_add, Finset.sum_add_distrib]
  have hu_eq : (fun m => o m + z m) = u := by
    ext m
    have hzdef : z m = u m - o m := rfl
    rw [hzdef]
    abel
  have hup (c : ℕ →₀ ℂ) :
      ‖Finsupp.linearCombination ℂ u c‖ ≤ (1 + K) * ‖Finsupp.linearCombination ℂ o c‖ := by
    calc ‖Finsupp.linearCombination ℂ u c‖
        = ‖Finsupp.linearCombination ℂ (fun m => o m + z m) c‖ := by rw [hu_eq]
      _ = ‖Finsupp.linearCombination ℂ o c + Finsupp.linearCombination ℂ z c‖ := by rw [← hadd]
      _ ≤ ‖Finsupp.linearCombination ℂ o c‖ + ‖Finsupp.linearCombination ℂ z c‖ := norm_add_le _ _
      _ ≤ ‖Finsupp.linearCombination ℂ o c‖ + K * ‖Finsupp.linearCombination ℂ o c‖ :=
          add_le_add_right (hpert c) _
      _ = (1 + K) * ‖Finsupp.linearCombination ℂ o c‖ := by ring
  have hdown (c : ℕ →₀ ℂ) :
      (1 - K) * ‖Finsupp.linearCombination ℂ o c‖ ≤ ‖Finsupp.linearCombination ℂ u c‖ := by
    have htri :
        ‖Finsupp.linearCombination ℂ o c‖ ≤
          ‖Finsupp.linearCombination ℂ u c‖ + ‖Finsupp.linearCombination ℂ z c‖ := by
      have : Finsupp.linearCombination ℂ o c =
          Finsupp.linearCombination ℂ (fun m => o m + z m) c +
            (-Finsupp.linearCombination ℂ z c) := by
        rw [← hadd]
        abel
      rw [this, hu_eq]
      simpa using norm_add_le (Finsupp.linearCombination ℂ u c) (-Finsupp.linearCombination ℂ z c)
    linarith [hpert c]
  have hnorm₁ : ∀ c, ‖eU c‖ ≤ (1 + K) * ‖eQ c‖ := fun c => by
    rw [← Submodule.norm_coe (eU c), ← Submodule.norm_coe (eQ c), heU, heQ']
    exact hup c
  have hnorm₂ : ∀ c, ‖eQ c‖ ≤ (1 - K)⁻¹ * ‖eU c‖ := fun c => by
    rw [← Submodule.norm_coe (eU c), ← Submodule.norm_coe (eQ c), heU, heQ']
    rw [← mul_le_mul_iff_of_pos_left hK1]
    calc (1 - K) * ‖Finsupp.linearCombination ℂ o c‖
        ≤ ‖Finsupp.linearCombination ℂ u c‖ := hdown c
      _ = (1 - K) * ((1 - K)⁻¹ * ‖Finsupp.linearCombination ℂ u c‖) := by
          rw [← mul_assoc, mul_inv_cancel₀ hK1.ne', one_mul]
  let fL := LinearEquiv.refl ℂ (ℕ →₀ ℂ)
  let T := fL.extend eQ eU hdenseQ ⟨1 + K, hnorm₁⟩ hdenseU ⟨(1 - K)⁻¹, hnorm₂⟩
  obtain ⟨Bs, hBs, _⟩ := exists_hilbertBasisLift_closedSpan_equiv_map T B
  have hval : ∀ m, (Bs m).val = u m := fun m => by
    rw [hBs]
    have hsingle : B m = eQ (Finsupp.single m 1) := by
      apply Subtype.ext
      rw [heQ', Finsupp.linearCombination_single, one_smul]
    rw [hsingle, LinearEquiv.extend_eq, LinearEquiv.refl_apply]
    rw [heU, Finsupp.linearCombination_single, one_smul]
  let φQ : ℕ → StrongDual ℂ E := fun m => (b.coord m).comp E₀.mkQL
  have hφQ : ∀ m n, φQ m (u n) = if m = n then (1 : ℂ) else 0 := fun m n => by
    have hmk : E₀.mkQ (u n) = b n := (hu n).2.1.trans (hB n).2.1
    simp only [φQ, ContinuousLinearMap.comp_apply, Submodule.mkQL_apply, hmk]
    exact hbio m n
  let slack : ℕ → ℝ := fun m => min (‖u m‖ - (r - ε)) ((r' + ε) - ‖u m‖)
  have hslack : ∀ m, 0 < slack m := fun m => by
    have hm := hcollar_u m
    rw [mem_Ioo] at hm
    exact lt_min (sub_pos.mpr hm.1) (sub_pos.mpr hm.2)
  obtain ⟨εδ, hεδpos, cδ, hcδ, hcδlt⟩ :=
    NNReal.exists_pos_sum_of_countable (ε := 1) one_ne_zero ℕ
  let δ : ℕ → ℝ := fun m => min (slack m) ((εδ m : ℝ) / (1 + ‖φQ m‖))
  have hδpos : ∀ m, 0 < δ m := fun m =>
    lt_min (hslack m) (div_pos (NNReal.coe_pos.mpr (hεδpos m)) (by positivity : 0 < 1 + ‖φQ m‖))
  have htermδ : ∀ m, ‖φQ m‖ * δ m ≤ (εδ m : ℝ) := fun m => by
    have hfrac : ‖φQ m‖ / (1 + ‖φQ m‖) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [norm_nonneg (φQ m)]
    calc ‖φQ m‖ * δ m
        ≤ ‖φQ m‖ * ((εδ m : ℝ) / (1 + ‖φQ m‖)) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) (norm_nonneg _)
      _ = (εδ m : ℝ) * (‖φQ m‖ / (1 + ‖φQ m‖)) := by ring
      _ ≤ (εδ m : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hfrac (NNReal.coe_nonneg _)
      _ = (εδ m : ℝ) := mul_one _
  have hsumεδ : Summable fun m => (εδ m : ℝ) := NNReal.summable_coe.mpr hcδ.summable
  have hsumδ : Summable fun m => ‖φQ m‖ * δ m :=
    Summable.of_nonneg_of_le (fun m => mul_nonneg (norm_nonneg _) (hδpos m).le) htermδ hsumεδ
  have hKδ : ∑' m, ‖φQ m‖ * δ m < 1 := by
    have hle := hsumδ.tsum_le_tsum htermδ hsumεδ
    have heq : ∑' m, (εδ m : ℝ) = (cδ : ℝ) := (NNReal.hasSum_coe.mpr hcδ).tsum_eq
    have hc1 : (cδ : ℝ) < 1 := NNReal.coe_lt_coe.mpr hcδlt
    linarith
  refine ⟨u, ε, hlift, ⟨Bs, hval⟩, ⟨T.symm⟩, δ, hδpos, fun y hy => ?_⟩
  have hyδ : ∀ m, ‖y m‖ ≤ δ m := fun m => (hy m).2.le
  have hδ0 : ∀ m, 0 ≤ δ m := fun m => (hδpos m).le
  refine ⟨?_, exists_biorthogonalBasisLift_stable_unique u y φQ hφQ δ hδ0 hyδ hsumδ hKδ⟩
  refine isEpsilonBasisLift_of_mkQ_eq E₀ V b.basis b.coord hbio hε hεr (fun m => u m + y m) ?_
  intro m
  have hym := hy m
  rw [Submodule.mem_inf] at hym
  refine ⟨V.add_mem (hu m).1 hym.1.1, ?_, ?_⟩
  · have hy0 : E₀.mkQ (y m) = 0 := by
      rw [Submodule.mkQ_apply]
      exact (Submodule.Quotient.mk_eq_zero _).mpr hym.1.2
    rw [map_add, (hu m).2.1.trans (hB m).2.1, hy0, add_zero]
  · have habs := abs_norm_sub_norm_le (u m + y m) (u m)
    have hsub : (u m + y m) - u m = y m := by abel
    rw [hsub] at habs
    have hm := hcollar_u m
    rw [mem_Ioo] at hm
    have hlow : ‖u m‖ - ‖y m‖ ≤ ‖u m + y m‖ := by linarith [abs_le.mp habs]
    have hupp : ‖u m + y m‖ ≤ ‖u m‖ + ‖y m‖ := norm_add_le _ _
    have hδlow : δ m ≤ ‖u m‖ - (r - ε) := (min_le_left _ _).trans (min_le_left _ _)
    have hδup : δ m ≤ (r' + ε) - ‖u m‖ := (min_le_left _ _).trans (min_le_right _ _)
    rw [mem_Icc]
    constructor
    · linarith [hym.2]
    · linarith [hym.2]

/-- Paper: Theorem 10.4.2.8, p. 463. At each admissible cutoff, the operator
obtained by spectral projection, convolution and cutoff is nuclear. -/
theorem spectralRestriction_nuclear (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) (_hband : innerBand)
    (φ : BruhatCompactSupport C𝔽) :
    IsNuclearOperator (spectralRestriction a hα hs hρ φ) := by
  have hφs : IsBruhatSmooth φ.val := (mem_bruhatSmoothSubmodule_iff _).mp φ.property.1
  have hc := continuous_of_bruhatSmooth hφs
  have hb := hc.bounded_above_of_compact_support (show HasCompactSupport φ.val from φ.property.2)
  have hm : IsModulation m𝔽 := ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
  have hsur : Function.Surjective m𝔽 := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.2.2.2.1
  obtain ⟨hT, _, _⟩ := truncatedHardySobolevConvolution_trace μ𝔽 m𝔽 (-α) α s (hStrip(hα)) hs φ.val
    hc.aemeasurable φ.property.2 hb hm hsur hφs hρ _hband
  have hconv := hardySobolevConvolution_eq_testAction μ𝔽 m𝔽 (-α) α s (hStrip(hα)) hs φ hc.aemeasurable hb
  have hn : IsNuclearOperator ((M(hρ)).comp (A(φ))) :=
    (congrArg (fun U : W₀ →L[ℂ] W₀ ↦ IsNuclearOperator ((M(hρ)).comp U)) hconv).mp hT
  exact mul_mem_nuclearEndomorphisms_right (H := W₀) Pspec ⟨_, hn⟩

-- In (10.4.2.21)–(10.4.2.24), use SpectralStripJetIndex and spectralZeroJet:
-- the zero is at a + b + it and the jet exponent is b + it. Proposition
-- 10.2.2.2 bounds dual jets. It gives no upper bound for the primal lifts,
-- and clustered ordinates obstruct such a bound on the critical line (R5).
-- The integral (10.4.2.26) is the squared rank-one norm. In (10.4.2.27)
-- one copy of each complex amplitude must be conjugated.

private theorem combine_trace_limits {p q : (ℝ → ℂ) → Prop} {z : ℂ}
    (hl : ∃ l, p l ∧ Tendsto l atTop (𝓝 z))
    (hd : ∀ l, p l → ∃ r, q r ∧ Tendsto (fun x ↦ r x - l x) atTop (𝓝 0)) :
    ∃ r, q r ∧ Tendsto r atTop (𝓝 z) := by
  obtain ⟨l, hl, hlim⟩ := hl
  obtain ⟨r, hr, hd⟩ := hd l hl
  exact ⟨r, hr, by simpa only [sub_add_cancel, zero_add] using hd.add hlim⟩

local notation "cutoffTraces(" op ", " eps ", " rho ", " test ", " t ")" =>
  (∀ᶠ R in atTop, ∃ hc : IsModulatedCutoff m𝔽 R ((eps) R) ((rho) R),
    let T := (op) a hα hs hc (test)
    ∃ hT : IsNuclearOperator (E := W₀) (F := W₀) T, (t) R = hilbertTrace (H := W₀) ⟨T, hT⟩)

/-- A nuclear operator admits a rank-one expansion with summable trace norms. -/
private theorem spectralRestriction_series
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : nuclearEndomorphisms H) :
    ∃ (a : ℕ → ℂ) (l : ℕ → H →L[ℂ] ℂ) (y : ℕ → H),
      Summable (fun n ↦ ‖a n‖ * (‖l n‖ * ‖y n‖)) ∧
      ∀ v, HasSum (fun n ↦ (a n * l n v) • y n) (T.val v) := by
  obtain ⟨a, l, y, ha, hl, hy, hseries⟩ := (isNuclearOperator_iff_isBanachNuclear _).mp T.property
  obtain ⟨L, hL, hL'⟩ := (Metric.isBounded_range_of_tendsto l hl).exists_pos_norm_le
  obtain ⟨Y, _, hY'⟩ := (Metric.isBounded_range_of_tendsto y hy).exists_pos_norm_le
  refine ⟨a, l, y, (ha.mul_right (L * Y)).of_nonneg_of_le (fun n ↦ by positivity) ?_, hseries⟩
  intro n
  exact mul_le_mul_of_nonneg_left (mul_le_mul (hL' _ (mem_range_self n))
    (hY' _ (mem_range_self n)) (norm_nonneg _) hL.le) (norm_nonneg _)

/-- Cyclicity for a nuclear factor and an arbitrary bounded factor. -/
theorem spectralRestriction_cyclic
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →L[ℂ] H) (T : nuclearEndomorphisms H) :
    hilbertTrace ⟨A * T.val, mul_mem_nuclearEndomorphisms_left A T⟩ =
      hilbertTrace ⟨T.val * A, mul_mem_nuclearEndomorphisms_right A T⟩ := by
  obtain ⟨a, l, y, hcost, hs⟩ := spectralRestriction_series T
  have hp (n : ℕ) : ‖a n‖ * (‖l n‖ * ‖A (y n)‖) ≤ (‖a n‖ * (‖l n‖ * ‖y n‖)) * ‖A‖ := by
    calc
      _ ≤ ‖a n‖ * (‖l n‖ * (‖A‖ * ‖y n‖)) := by gcongr; exact A.le_opNorm _
      _ = _ := by ring
  have hq (n : ℕ) : ‖a n‖ * (‖(l n).comp A‖ * ‖y n‖) ≤ (‖a n‖ * (‖l n‖ * ‖y n‖)) * ‖A‖ := by
    calc
      _ ≤ ‖a n‖ * ((‖l n‖ * ‖A‖) * ‖y n‖) := by gcongr; exact ContinuousLinearMap.opNorm_comp_le _ _
      _ = _ := by ring
  unfold hilbertTrace
  rw [tsum_hilbertDiagonal_eq_series _ _ a l (fun n ↦ A (y n))
    ((hcost.mul_right ‖A‖).of_nonneg_of_le (fun n ↦ by positivity) hp)
    (fun x ↦ by change HasSum _ (A (T.val x)); simpa only [map_smul] using A.hasSum (hs x))]
  exact (tsum_hilbertDiagonal_eq_series _ (T.val * A) a (fun n ↦ (l n).comp A) y
    ((hcost.mul_right ‖A‖).of_nonneg_of_le (fun n ↦ by positivity) hq)
    (fun x ↦ hs (A x))).symm

/-- If uniformly bounded operators converge weakly to zero, their traces against a fixed
nuclear operator tend to zero. -/
private theorem spectralRestriction_weak_trace
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : ℝ → H →L[ℂ] H) (T : nuclearEndomorphisms H)
    (C : ℝ) (hS : ∀ t, ‖S t‖ ≤ C)
    (hw : ∀ v (l : H →L[ℂ] ℂ), Tendsto (fun t ↦ l (S t v)) atTop (𝓝 0)) :
    Tendsto (fun t ↦ hilbertTrace ⟨S t * T.val, mul_mem_nuclearEndomorphisms_left (S t) T⟩)
      atTop (𝓝 0) := by
  obtain ⟨a, l, y, hcost, hs⟩ := spectralRestriction_series T
  have hdom (t : ℝ) (n : ℕ) :
      ‖a n‖ * (‖l n‖ * ‖S t (y n)‖) ≤ (‖a n‖ * (‖l n‖ * ‖y n‖)) * C := by
    have h := ((S t).le_opNorm (y n)).trans (mul_le_mul_of_nonneg_right (hS t) (norm_nonneg _))
    calc
      _ ≤ ‖a n‖ * (‖l n‖ * (C * ‖y n‖)) := by gcongr
      _ = _ := by ring
  have htr (t : ℝ) : hilbertTrace ⟨S t * T.val, mul_mem_nuclearEndomorphisms_left (S t) T⟩ =
      ∑' n, a n * l n (S t (y n)) :=
    tsum_hilbertDiagonal_eq_series _ _ _ _ _
      ((hcost.mul_right C).of_nonneg_of_le (fun n ↦ by positivity) (hdom t))
      (fun x ↦ by change HasSum _ (S t (T.val x)); simpa only [map_smul] using (S t).hasSum (hs x))
  simp_rw [htr]
  have h := tendsto_tsum_of_dominated_convergence (g := fun _ ↦ (0 : ℂ))
    (hcost.mul_right C) (fun n ↦ by simpa using (hw (y n) (l n)).const_mul (a n))
    (Eventually.of_forall fun t n ↦ (by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left ((l n).le_opNorm _) (norm_nonneg _)).trans (hdom t n)
      : ‖a n * l n (S t (y n))‖ ≤ (‖a n‖ * (‖l n‖ * ‖y n‖)) * C))
  simpa using h

/-- A one-sided approximation of the commutator bounds the difference of the two traces. -/
private theorem spectralRestriction_commutator_bound
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P A M B : H →L[ℂ] H) (hP : ‖P‖ ≤ 1) (hPA : IsNuclearOperator (P * A))
    (hMA : IsNuclearOperator (M * A)) (E : nuclearEndomorphisms H)
    (herr : M * A - A * M = A * B + E.val) :
    ‖hilbertTrace ⟨(M * A) * P, mul_mem_nuclearEndomorphisms_right P ⟨_, hMA⟩⟩ -
      hilbertTrace ⟨M * (P * A), mul_mem_nuclearEndomorphisms_left M ⟨_, hPA⟩⟩‖ ≤
      ‖hilbertTrace ⟨B * (P * A), mul_mem_nuclearEndomorphisms_left B ⟨_, hPA⟩⟩‖ + traceNorm E := by
  let PA : nuclearEndomorphisms H := ⟨P * A, hPA⟩
  let MA : nuclearEndomorphisms H := ⟨M * A, hMA⟩
  let left (U : H →L[ℂ] H) (T : nuclearEndomorphisms H) : nuclearEndomorphisms H :=
    ⟨U * T.val, mul_mem_nuclearEndomorphisms_left U T⟩
  let right (T : nuclearEndomorphisms H) (U : H →L[ℂ] H) : nuclearEndomorphisms H :=
    ⟨T.val * U, mul_mem_nuclearEndomorphisms_right U T⟩
  have hid : left P MA - right PA M = right PA B + left P E := by
    apply Subtype.ext
    change P * (M * A) - (P * A) * M = (P * A) * B + P * E.val
    simpa only [mul_sub, mul_add, mul_assoc] using congrArg (P * ·) herr
  obtain ⟨tr, htr⟩ := hilbertTrace_linear (H := H)
  have htrace : hilbertTrace (left P MA) - hilbertTrace (right PA M) =
      hilbertTrace (right PA B) + hilbertTrace (left P E) := by
    rw [← htr _, ← htr _, ← htr _, ← htr _, ← map_sub, ← map_add, hid]
  change ‖hilbertTrace (right MA P) - hilbertTrace (left M PA)‖ ≤
    ‖hilbertTrace (left B PA)‖ + traceNorm E
  rw [← spectralRestriction_cyclic P MA, spectralRestriction_cyclic M PA, htrace,
    ← spectralRestriction_cyclic B PA]
  exact (norm_add_le _ _).trans (add_le_add le_rfl ((norm_hilbertTrace_le (left P E)).trans
    ((traceNorm_mul_left_le P E).trans (mul_le_of_le_one_left (traceNorm_nonneg E) hP))))

/-- Paper: Theorem 10.4.2.8, pp. 463–464. The commutator of cutoff multiplication
and ambient convolution can be approximated in trace norm by products `A * B R`, where `A` is
convolution and the uniformly bounded operators `B R` tend to zero in the weak operator topology.
Deviation: This sufficient estimate involves only the weighted ambient space. In log-norm
coordinates the commutator is supported near the two ends of the cutoff interval. -/
private theorem spectralRestriction_cutoff_commutator_approx (φ : BruhatCompactSupport C𝔽)
    (ε : ℝ → ℝ) (ρ : ℝ → C𝔽 → ℝ) (_hε : Tendsto (fun R ↦ ε R * R) atTop (𝓝 0))
    (_hρ : ∀ᶠ R in atTop, IsModulatedCutoff m𝔽 R (ε R) (ρ R) ∧
      0 < R⁻¹ + ε R ∧ R⁻¹ + ε R < R - ε R) (η : ℝ) (_hη : 0 < η) :
    let A : W₀ →L[ℂ] W₀ := A(φ)
    ∃ (C : ℝ) (B : ℝ → W₀ →L[ℂ] W₀), (∀ R, ‖B R‖ ≤ C) ∧
      (∀ v (l : W₀ →L[ℂ] ℂ), Tendsto (fun R ↦ l (B R v)) atTop (𝓝 0)) ∧
      ∀ᶠ R in atTop, ∀ hc : IsModulatedCutoff m𝔽 R (ε R) (ρ R),
        let M : W₀ →L[ℂ] W₀ := M(hc)
        ∃ E : nuclearEndomorphisms W₀, M * A - A * M = A * B R + E.val ∧ traceNorm E < η := by sorry

/-- Paper: Theorem 10.4.2.8, pp. 463–464. The trace of the cutoff times the
spectral-to-geometric block tends to zero. By (10.4.1.11) and linearity of
the trace this is the difference of the traces of the two composition orders.
Gap: Footnote 8 leaves this estimate open. Arbitrary collar lifts need not be
orthogonal representatives, and (10.4.2.34) gives no summable rank-one bound. -/
theorem spectralRestriction_offDiagonal_trace_tendsto_zero (φ : BruhatCompactSupport C𝔽)
    (_hquot : quotientNuclear(φ)) (ε : ℝ → ℝ) (ρ : ℝ → C𝔽 → ℝ)
    (_hε : Tendsto (fun R ↦ ε R * R) atTop (𝓝 0))
    (_hρ : ∀ᶠ R in atTop, IsModulatedCutoff m𝔽 R (ε R) (ρ R) ∧
      0 < R⁻¹ + ε R ∧ R⁻¹ + ε R < R - ε R)
    (l : ℝ → ℂ)
    (_hl : cutoffTraces(spectralTruncatedConvolution, ε, ρ, φ, l)) :
    ∃ r : ℝ → ℂ, cutoffTraces(spectralRestriction, ε, ρ, φ, r) ∧
      Tendsto (fun R ↦ r R - l R) atTop (𝓝 0) := by
  classical
  let r (R : ℝ) : ℂ :=
    if h : IsModulatedCutoff m𝔽 R (ε R) (ρ R) ∧ 0 < R⁻¹ + ε R ∧ R⁻¹ + ε R < R - ε R then
      hilbertTrace ⟨_, spectralRestriction_nuclear a hα hs h.1 h.2 φ⟩ else 0
  have hr : cutoffTraces(spectralRestriction, ε, ρ, φ, r) := by
    filter_upwards [_hρ] with R h
    exact ⟨h.1, spectralRestriction_nuclear a hα hs h.1 h.2 φ, dite_eq_left h⟩
  refine ⟨r, hr, Metric.tendsto_nhds.mpr ?_⟩
  intro η hη
  obtain ⟨C, B, hC, hw, herror⟩ :=
    spectralRestriction_cutoff_commutator_approx hα hs φ ε ρ _hε _hρ (η / 2) (half_pos hη)
  have hPA := spectralProjection_convolution_nuclear (F := F) a hα hs φ _hquot
  have hlim := spectralRestriction_weak_trace B ⟨_, hPA⟩ C hC hw
  filter_upwards [hr, _hl, _hρ, herror, Metric.tendsto_nhds.mp hlim (η / 2) (half_pos hη)]
    with R hrR hlR hcut herr hsmall
  obtain ⟨hc, hn, hright⟩ := hrR
  obtain ⟨hc', hn', hleft⟩ := hlR
  obtain ⟨E, heq, hE⟩ := herr hc
  have hMA := (truncatedConvolution_trace_split (F := F) a hα hs hc hcut.2 φ _hquot).choose
  have hbound := spectralRestriction_commutator_bound Pspec (A(φ)) (M(hc)) (B R)
    (Submodule.starProjection_norm_le _) hPA hMA E heq
  rw [dist_zero_right] at hsmall ⊢
  rw [hright, hleft]
  exact hbound.trans_lt ((add_lt_add hsmall hE).trans_eq (add_halves η))

/-- Paper: Theorem 10.4.2.8, p. 463. As the cutoff radius tends to infinity
with width times radius tending to zero, the trace of convolution after
spectral projection tends to the quotient convolution trace.
Deviation: Quotient nuclearity is explicit. -/
theorem spectralRestriction_trace_tendsto (φ : BruhatCompactSupport C𝔽)
    (hquot : quotientNuclear(φ)) (ε : ℝ → ℝ) (ρ : ℝ → C𝔽 → ℝ)
    (_hε : Tendsto (fun R ↦ ε R * R) atTop (𝓝 0))
    (_hρ : ∀ᶠ R in atTop, IsModulatedCutoff m𝔽 R (ε R) (ρ R) ∧
      0 < R⁻¹ + ε R ∧ R⁻¹ + ε R < R - ε R) :
    ∃ traces : ℝ → ℂ, cutoffTraces(spectralRestriction, ε, ρ, φ, traces) ∧
      Tendsto traces atTop (𝓝 (hilbertTrace (H := H₀) ⟨Aₛ(φ), hquot⟩)) :=
  combine_trace_limits
    (p := fun t ↦ cutoffTraces(spectralTruncatedConvolution, ε, ρ, φ, t))
    (q := fun t ↦ cutoffTraces(spectralRestriction, ε, ρ, φ, t))
    (z := hilbertTrace (H := H₀) ⟨Aₛ(φ), hquot⟩)
    (spectralTruncatedConvolution_trace_tendsto (F := F) a hα hs φ hquot ε ρ _hε _hρ)
    (spectralRestriction_offDiagonal_trace_tendsto_zero (F := F) a hα hs φ hquot ε ρ _hε _hρ)

end Truncations

end RiemannMasullo
