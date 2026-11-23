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

section
open scoped TensorProduct ENNReal Pointwise ComplexInnerProductSpace

namespace CutoffWindow
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "tensorProductLeft" => (fun (B : H →L[ℂ] H) (z : StrongDual ℂ H ⊗[ℂ] H) ↦
  (⟨B * tensorToFiniteRank z,
    mul_mem_nuclearEndomorphisms_left B ⟨_, tensorToFiniteRank_mem_nuclearEndomorphisms z⟩⟩ : nuclearEndomorphisms H))

/-- Each projected finite tensor can be approximated using output vectors from the range of B. -/
private theorem approximate_tensor (Q B : H →L[ℂ] H) (hQ : ∀ x, Q x ∈ closure (range B))
    (z : StrongDual ℂ H ⊗[ℂ] H) (η : ℝ) (hη : 0 < η) :
    ∃ z' : StrongDual ℂ H ⊗[ℂ] H,
      traceNorm (tensorProductLeft Q z - tensorProductLeft B z') < η := by
  induction z using TensorProduct.inductionOn generalizing η with
  | tmul φ x =>
    obtain ⟨y, hy⟩ := Metric.mem_closure_range_iff.mp (hQ x) (η / (‖φ‖ + 1)) (by positivity)
    refine ⟨φ ⊗ₜ[ℂ] y, ?_⟩
    have heq : tensorProductLeft Q (φ ⊗ₜ[ℂ] x) - tensorProductLeft B (φ ⊗ₜ[ℂ] y) =
        ⟨φ.smulRight (Q x - B y), smulRight_mem_nuclearEndomorphisms _ _⟩ := by
      apply Subtype.ext
      ext v
      change Q (tensorToFiniteRank _ v) - B (tensorToFiniteRank _ v) = φ v • (Q x - B y)
      simp only [tensorToFiniteRank_tmul, map_smul, smul_sub]
    rw [heq, traceNorm_smulRight]
    rw [dist_eq_norm] at hy
    have hh := (lt_div_iff₀ (by positivity : 0 < ‖φ‖ + 1)).mp hy
    nlinarith [norm_nonneg (Q x - B y)]
  | add z w ihz ihw =>
    obtain ⟨z', hz'⟩ := ihz (η / 2) (half_pos hη)
    obtain ⟨w', hw'⟩ := ihw (η / 2) (half_pos hη)
    refine ⟨z' + w', ?_⟩
    have heq : tensorProductLeft Q (z + w) - tensorProductLeft B (z' + w') =
        (tensorProductLeft Q z - tensorProductLeft B z') +
        (tensorProductLeft Q w - tensorProductLeft B w') := by
      apply Subtype.ext
      change Q * tensorToFiniteRank (z + w) - B * tensorToFiniteRank (z' + w') = _
      simp only [map_add, mul_add, Submodule.coe_add, Submodule.coe_sub]
      abel
    rw [heq]
    exact (traceNorm_add_le _ _).trans_lt ((add_lt_add hz' hw').trans_eq (add_halves η))

/-- If the output of D lies in the closure of the range of B, then BF for finite-rank F
approximates D in trace norm. -/
private theorem range_factor_approx (B : H →L[ℂ] H) (D : nuclearEndomorphisms H)
    (hD : ∀ v, D.val v ∈ closure (range B)) (η : ℝ) (hη : 0 < η) :
    ∃ z : StrongDual ℂ H ⊗[ℂ] H, traceNorm (D - tensorProductLeft B z) < η := by
  let V := B.toLinearMap.range.topologicalClosure
  let Q := V.starProjection
  have hQ (v : H) : Q v ∈ closure (range B) := V.starProjection_apply_mem v
  have hfix : Q * D.val = D.val := by
    ext x
    exact V.starProjection_eq_self_iff.mpr (hD x)
  obtain ⟨z, hz⟩ := exists_tensorToFiniteRank_traceNorm_sub_lt D (half_pos hη)
  obtain ⟨z', hz'⟩ := approximate_tensor Q B hQ z (η / 2) (half_pos hη)
  let T : nuclearEndomorphisms H := ⟨_, tensorToFiniteRank_mem_nuclearEndomorphisms z⟩
  let E : nuclearEndomorphisms H := ⟨Q * (D - T).val, mul_mem_nuclearEndomorphisms_left Q (D - T)⟩
  have hE : traceNorm E ≤ traceNorm (D - T) := (traceNorm_mul_left_le Q (D - T)).trans
    (mul_le_of_le_one_left (traceNorm_nonneg _) V.starProjection_norm_le)
  have hsum : D - tensorProductLeft B z' = E + (tensorProductLeft Q z - tensorProductLeft B z') := by
    apply Subtype.ext
    change D.val - B * tensorToFiniteRank z' =
      Q * (D.val - tensorToFiniteRank z) + (Q * tensorToFiniteRank z - B * tensorToFiniteRank z')
    rw [mul_sub, hfix]
    abel
  refine ⟨z', ?_⟩
  change traceNorm (D - tensorProductLeft B z') < η
  rw [hsum]
  exact (traceNorm_add_le _ _).trans_lt ((add_lt_add (hE.trans_lt hz) hz').trans_eq (add_halves η))

local notation "CL(" U ")" => (U).toContinuousLinearEquiv.toContinuousLinearMap
local notation "move(" U ", " F ")" => (CL(U) * (F) * CL((U).symm))

/-- Algebraic tensors send weakly null vectors to strongly null vectors. -/
private theorem tensor_sends_weak_to_strong {ι : Type*} {l : Filter ι}
    (z : StrongDual ℂ H ⊗[ℂ] H) (v : ι → H)
    (hv : ∀ f : StrongDual ℂ H, Tendsto (fun i ↦ f (v i)) l (𝓝 0)) :
    Tendsto (fun i ↦ tensorToFiniteRank z (v i)) l (𝓝 0) := by
  induction z using TensorProduct.inductionOn with
  | tmul f y =>
    simpa only [tensorToFiniteRank_tmul, zero_smul] using (hv f).smul_const y
  | add z w hz hw =>
    simpa only [map_add, add_apply, add_zero] using hz.add hw

/-- Moving one fixed finite-rank operator to a weakly escaping window gives
a uniformly bounded, strongly null family. -/
private theorem moved_tensor_null {ι : Type*} {l : Filter ι}
    (U : ι → H ≃ₗᵢ[ℂ] H)
    (hU : ∀ v (f : StrongDual ℂ H), Tendsto (fun i ↦ f ((U i).symm v)) l (𝓝 0))
    (z : StrongDual ℂ H ⊗[ℂ] H) :
    (∀ i, ‖move(U i, tensorToFiniteRank z)‖ ≤ ‖tensorToFiniteRank z‖) ∧
      ∀ v, Tendsto (fun i ↦ move(U i, tensorToFiniteRank z) v) l (𝓝 0) := by
  constructor
  · intro i
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro v
    change ‖U i (tensorToFiniteRank z ((U i).symm v))‖ ≤ _
    simpa only [LinearIsometryEquiv.norm_map] using (tensorToFiniteRank z).le_opNorm ((U i).symm v)
  · intro v
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    change Tendsto (fun i ↦ ‖U i (tensorToFiniteRank z ((U i).symm v))‖) l (𝓝 0)
    simp only [LinearIsometryEquiv.norm_map]
    exact tendsto_zero_iff_norm_tendsto_zero.mp (tensor_sends_weak_to_strong z _ (hU v))

/-- A Hilbert space unitary has operator norm at most one. -/
private theorem unitary_opNorm_le_one (U : H ≃ₗᵢ[ℂ] H) : ‖CL(U)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  simp only [one_mul]
  exact (U.norm_map v).le

/-- Moving a trace-class error to its window cannot enlarge its trace norm. -/
private theorem move_trace_bound (U : H ≃ₗᵢ[ℂ] H) (T : nuclearEndomorphisms H) :
    ∃ E : nuclearEndomorphisms H, E.val = move(U, T.val) ∧ traceNorm E ≤ traceNorm T := by
  let N : nuclearEndomorphisms H := ⟨CL(U) * T.val, mul_mem_nuclearEndomorphisms_left CL(U) T⟩
  refine ⟨⟨N.val * CL(U.symm), mul_mem_nuclearEndomorphisms_right CL(U.symm) N⟩, rfl, ?_⟩
  exact (traceNorm_mul_right_le CL(U.symm) N).trans
    ((mul_le_of_le_one_left (traceNorm_nonneg N) (unitary_opNorm_le_one U.symm)).trans
      ((traceNorm_mul_left_le CL(U) T).trans (mul_le_of_le_one_left (traceNorm_nonneg T) (unitary_opNorm_le_one U))))

/-- A trace-class limit in one moving window, whose range lies in the closure of the
limiting convolution range, admits the required approximation by a fixed finite-rank
right factor translated with that window. -/
private theorem moving_window_factor (U : ℝ → H ≃ₗᵢ[ℂ] H)
    (hU : ∀ v (f : StrongDual ℂ H), Tendsto (fun R ↦ f ((U R).symm v)) atTop (𝓝 0))
    (A C : H →L[ℂ] H)
    (hA : ∀ v, Tendsto (fun R ↦ (U R).symm (A (U R v))) atTop (𝓝 (C v)))
    (D : ℝ → nuclearEndomorphisms H) (D₀ : nuclearEndomorphisms H)
    (hD : Tendsto (fun R ↦ traceNorm (D R - D₀)) atTop (𝓝 0))
    (hrange : ∀ v, D₀.val v ∈ closure (range C)) {η : ℝ} (hη : 0 < η) :
    ∃ (K : ℝ) (B : ℝ → H →L[ℂ] H), (∀ R, ‖B R‖ ≤ K) ∧
      (∀ v, Tendsto (fun R ↦ B R v) atTop (𝓝 0)) ∧
      ∀ᶠ R in atTop, ∃ E : nuclearEndomorphisms H,
        move(U R, (D R).val) = A * B R + E.val ∧ traceNorm E < η := by
  have hh : 0 < η / 3 := by positivity
  obtain ⟨z, hz⟩ := range_factor_approx C D₀ hrange _ hh
  let F := tensorToFiniteRank z
  let L (R : ℝ) := CL((U R).symm) * A * CL(U R)
  have hnull (v : H) : Tendsto (fun R ↦ (C - L R) v) atTop (𝓝 0) := by
    change Tendsto (fun R ↦ C v - (U R).symm (A (U R v))) atTop (𝓝 0)
    simpa only [sub_self] using (tendsto_const_nhds (x := C v)).sub (hA v)
  obtain ⟨hn, hnlim⟩ := tendsto_traceNorm_mul_finiteRank (fun R ↦ C - L R) hnull
    F (finiteDimensional_range_tensorToFiniteRank z)
  obtain ⟨hB, hw⟩ := moved_tensor_null U hU z
  refine ⟨‖F‖, fun R ↦ move(U R, F), hB, hw, ?_⟩
  filter_upwards [hD.eventually_lt_const hh, hnlim.eventually_lt_const hh] with R hDR hLR
  let T := D R - D₀
  let V := D₀ - tensorProductLeft C z
  let N : nuclearEndomorphisms H := ⟨(C - L R) * F, hn R⟩
  obtain ⟨E, hE, hnorm⟩ := move_trace_bound (U R) (T + V + N)
  refine ⟨E, ?_, hnorm.trans_lt ?_⟩
  · rw [hE]
    ext v
    change U R ((D R).val ((U R).symm v)) =
      A (U R (F ((U R).symm v))) + U R (((D R).val ((U R).symm v) - D₀.val ((U R).symm v)) +
        (D₀.val ((U R).symm v) - C (F ((U R).symm v))) +
        (C (F ((U R).symm v)) - (U R).symm (A (U R (F ((U R).symm v))))))
    simp only [map_add, map_sub, LinearIsometryEquiv.apply_symm_apply]
    abel
  · have h := (traceNorm_add_le (T + V) N).trans (add_le_add_left (traceNorm_add_le T V) (traceNorm N))
    change traceNorm T < η / 3 at hDR
    change traceNorm V < η / 3 at hz
    change traceNorm N < η / 3 at hLR
    linarith

/-- Combine the two moving edges. The hypotheses involve only fixed-window operators
and a local exact decomposition of the cutoff commutator. -/
private theorem cutoff_commutator_of_two_windows (A : H →L[ℂ] H) (valid : ℝ → Prop)
    (M : ∀ R, valid R → H →L[ℂ] H) (U : Bool → ℝ → H ≃ₗᵢ[ℂ] H)
    (hU : ∀ j v (f : StrongDual ℂ H), Tendsto (fun R ↦ f ((U j R).symm v)) atTop (𝓝 0))
    (C : Bool → H →L[ℂ] H)
    (hA : ∀ j v, Tendsto (fun R ↦ (U j R).symm (A (U j R v))) atTop (𝓝 (C j v)))
    (D : Bool → ℝ → nuclearEndomorphisms H) (D₀ : Bool → nuclearEndomorphisms H)
    (hD : ∀ j, Tendsto (fun R ↦ traceNorm (D j R - D₀ j)) atTop (𝓝 0))
    (hrange : ∀ j v, (D₀ j).val v ∈ closure (range (C j)))
    (hdec : ∀ᶠ R in atTop, ∀ h : valid R, M R h * A - A * M R h =
      move(U true R, (D true R).val) + move(U false R, (D false R).val))
    {η : ℝ} (hη : 0 < η) :
    ∃ (K : ℝ) (B : ℝ → H →L[ℂ] H), (∀ R, ‖B R‖ ≤ K) ∧
      (∀ v (f : StrongDual ℂ H), Tendsto (fun R ↦ f (B R v)) atTop (𝓝 0)) ∧
      ∀ᶠ R in atTop, ∀ h : valid R, ∃ E : nuclearEndomorphisms H,
        M R h * A - A * M R h = A * B R + E.val ∧ traceNorm E < η := by
  have h (j : Bool) := moving_window_factor (U j) (hU j) A (C j) (hA j) (D j) (D₀ j) (hD j)
    (hrange j) (half_pos hη)
  obtain ⟨K₁, B₁, hK₁, hw₁, he₁⟩ := h true
  obtain ⟨K₂, B₂, hK₂, hw₂, he₂⟩ := h false
  refine ⟨K₁ + K₂, fun R ↦ B₁ R + B₂ R,
    fun R ↦ (norm_add_le ..).trans (add_le_add (hK₁ R) (hK₂ R)), ?_, ?_⟩
  · intro v f
    have hlim : Tendsto (fun R ↦ (B₁ R + B₂ R) v) atTop (𝓝 0) := by
      simpa only [add_apply, add_zero] using (hw₁ v).add (hw₂ v)
    simpa only [Function.comp_def, map_zero] using (f.continuous.tendsto 0).comp hlim
  · filter_upwards [hdec, he₁, he₂] with R hR h₁ h₂
    obtain ⟨E₁, hE₁, hη₁⟩ := h₁
    obtain ⟨E₂, hE₂, hη₂⟩ := h₂
    intro hM
    refine ⟨E₁ + E₂, ?_, (traceNorm_add_le E₁ E₂).trans_lt ((add_lt_add hη₁ hη₂).trans_eq (add_halves η))⟩
    rw [hR hM, hE₁, hE₂, mul_add]
    change _ = _ + (E₁.val + E₂.val)
    abel

end
section

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [NormalSpace G] [MeasurableSpace G] [BorelSpace G]
variable (μ : Measure G) [μ.IsMulLeftInvariant] [μ.Regular]

/-- Approximate a square-integrable vector and keep a compactly supported representative. -/
private theorem approx_compact_L2 (v : Lp ℂ 2 μ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (w : Lp ℂ 2 μ) (g : G → ℂ), HasCompactSupport g ∧ (w : G → ℂ) =ᵐ[μ] g ∧ ‖v - w‖ ≤ δ := by
  obtain ⟨g, hg, hdist, _, hmem⟩ := (Lp.memLp v).exists_hasCompactSupport_eLpNorm_sub_le
    (by norm_num : (2 : ENNReal) ≠ ⊤) (ENNReal.ofReal_pos.mpr hδ).ne'
  refine ⟨hmem.toLp g, g, hg, hmem.coeFn_toLp, ?_⟩
  apply (ENNReal.ofReal_le_ofReal_iff hδ.le).mp
  rw [← dist_eq_norm, ← edist_dist]
  convert hdist using 1
  rw [← Lp.toLp_coeFn v (Lp.memLp v), Lp.edist_toLp_toLp, Lp.toLp_coeFn]

local notation "U(" g ")" =>
  Lp.compMeasurePreservingₗᵢ ℂ (fun y : G ↦ g⁻¹ * y) (measurePreserving_mul_left μ g⁻¹)

/-- The matrix coefficient of two compactly supported vectors vanishes outside the product
of their supports. -/
private theorem translate_inner_compact (v w : Lp ℂ 2 μ)
    {a b : G → ℂ} (ha : HasCompactSupport a) (hb : HasCompactSupport b)
    (hv : (v : G → ℂ) =ᵐ[μ] a) (hw : (w : G → ℂ) =ᵐ[μ] b) :
    ∀ᶠ g in cocompact G, inner ℂ w (U(g) v) = 0 := by
  filter_upwards [(hb.isCompact.mul ha.isCompact.inv).compl_mem_cocompact] with g hg
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [hw, Lp.coeFn_compMeasurePreserving v (measurePreserving_mul_left μ g⁻¹),
    (measurePreserving_mul_left μ g⁻¹).quasiMeasurePreserving.ae_eq_comp hv] with y hw hy hv
  change inner ℂ (w y) (Lp.compMeasurePreserving (fun p : G ↦ g⁻¹ * p)
    (measurePreserving_mul_left μ g⁻¹) v y) = 0
  change v (g⁻¹ * y) = a (g⁻¹ * y) at hv
  change _ = v (g⁻¹ * y) at hy
  rw [hw, hy, hv]
  by_cases hb' : b y = 0
  · rw [hb', inner_zero_left]
  have ha' : a (g⁻¹ * y) = 0 := by
    by_contra hh
    apply hg
    exact ⟨y, subset_tsupport _ hb', (g⁻¹ * y)⁻¹, Set.inv_mem_inv.mpr (subset_tsupport _ hh), by group⟩
  rw [ha', inner_zero_right]

/-- Translations of a fixed Haar L² vector are weakly null at infinity. -/
private theorem haar_translation_weak_zero (v : Lp ℂ 2 μ) (f : StrongDual ℂ (Lp ℂ 2 μ)) :
    Tendsto (fun g : G ↦ f (U(g) v)) (cocompact G) (𝓝 0) := by
  obtain ⟨w, rfl⟩ := (InnerProductSpace.toDual ℂ (Lp ℂ 2 μ)).surjective f
  change Tendsto (fun g : G ↦ inner ℂ w (U(g) v)) (cocompact G) (𝓝 0)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨w', b, hb, hw', hdw⟩ := approx_compact_L2 μ w (δ := (ε / 3) / (‖v‖ + 1)) (by positivity)
  obtain ⟨v', a, ha, hv', hdv⟩ := approx_compact_L2 μ v (δ := (ε / 3) / (‖w'‖ + 1)) (by positivity)
  have h₁ : ‖w - w'‖ * ‖v‖ ≤ ε / 3 := by
    have h := (le_div_iff₀ (by positivity : 0 < ‖v‖ + 1)).mp hdw
    nlinarith [norm_nonneg (w - w')]
  have h₂ : ‖w'‖ * ‖v - v'‖ ≤ ε / 3 := by
    have h := (le_div_iff₀ (by positivity : 0 < ‖w'‖ + 1)).mp hdv
    nlinarith [norm_nonneg (v - v')]
  filter_upwards [translate_inner_compact μ v' w' ha hb hv' hw'] with g hcompact
  have hsum : inner ℂ w (U(g) v) =
      inner ℂ (w - w') (U(g) v) + inner ℂ w' (U(g) (v - v')) := by
    rw [inner_sub_left, map_sub, inner_sub_right, hcompact, sub_zero]
    abel
  rw [dist_zero_right, hsum]
  refine (norm_add_le ..).trans_lt ?_
  have h₃ := norm_inner_le_norm (𝕜 := ℂ) (w - w') (U(g) v)
  have h₄ := norm_inner_le_norm (𝕜 := ℂ) w' (U(g) (v - v'))
  rw [LinearIsometry.norm_map] at h₃ h₄
  linarith

end
section

/-- Multiplication by the positive square root of a density sends its weighted L² space
unitarily onto unweighted L², with the pointwise formula for Haar representatives. -/
private theorem exists_unweight_L2 {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (w : X → ℝ≥0) (hw : Measurable w) (hp : ∀ x, 0 < w x) :
    ∃ U : Lp ℂ 2 (μ.withDensity (fun x ↦ (w x : ℝ≥0∞))) ≃ₗᵢ[ℂ] Lp ℂ 2 μ,
      ∀ v, (U v : X → ℂ) =ᵐ[μ] fun x ↦ (Real.sqrt (w x) : ℂ) * v x := by
  let ν := μ.withDensity (fun x ↦ (w x : ℝ≥0∞))
  let c (x : X) : ℂ := Real.sqrt (w x)
  have hμ : μ ≪ ν := withDensity_absolutelyContinuous' hw.coe_nnreal_ennreal.aemeasurable
    (.of_forall fun x ↦ by simpa using (hp x).ne')
  have hc : StronglyMeasurable c := (Complex.measurable_ofReal.comp
    (Real.continuous_sqrt.measurable.comp (measurable_coe_nnreal_real.comp hw))).stronglyMeasurable
  have hc0 (x : X) : c x ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hp x)).ne'
  have hc2 (x : X) : ‖c x‖ ^ 2 = (w x : ℝ) := by
    simp only [c, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (NNReal.coe_nonneg _)]
  have hmem (g : X → ℂ) (hg : StronglyMeasurable g) :
      MemLp g 2 ν ↔ MemLp (fun x ↦ c x * g x) 2 μ := by
    have hcg : StronglyMeasurable (fun x ↦ c x * g x) := hc.mul hg
    rw [memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable,
      memLp_two_iff_integrable_sq_norm hcg.aestronglyMeasurable]
    change Integrable _ (μ.withDensity _) ↔ _
    rw [integrable_withDensity_iff_integrable_smul hw]
    exact integrable_congr (.of_forall fun x ↦ by
      simp only [NNReal.smul_def, smul_eq_mul, norm_mul, mul_pow, hc2])
  let L (v : Lp ℂ 2 ν) := ((hmem v (Lp.stronglyMeasurable v)).mp (Lp.memLp v)).toLp _
  have hL (v : Lp ℂ 2 ν) : (L v : X → ℂ) =ᵐ[μ] fun x ↦ c x * v x := MemLp.coeFn_toLp _
  let J : Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 μ :=
    { toFun := L
      map_add' := fun v u ↦ by
        apply Lp.ext
        filter_upwards [hL (v + u), hL v, hL u, hμ.ae_le (Lp.coeFn_add v u), Lp.coeFn_add (L v) (L u)]
          with x h1 h2 h3 h4 h5
        rw [h1, h5, Pi.add_apply, h4, Pi.add_apply, h2, h3, mul_add]
      map_smul' := fun k v ↦ by
        apply Lp.ext
        filter_upwards [hL (k • v), hL v, hμ.ae_le (Lp.coeFn_smul k v), Lp.coeFn_smul k (L v)]
          with x h1 h2 h3 h4
        rw [h1, RingHom.id_apply, h4, Pi.smul_apply, h3, Pi.smul_apply, h2, smul_eq_mul, smul_eq_mul]
        ring }
  have hnorm (v : Lp ℂ 2 ν) : ‖J v‖ = ‖v‖ := by
    have hi : inner ℂ (J v) (J v) = inner ℂ v v := by
      rw [L2.inner_def, L2.inner_def]
      change _ = ∫ x, inner ℂ (v x) (v x) ∂μ.withDensity _
      rw [integral_withDensity_eq_integral_smul hw]
      refine integral_congr_ae ?_
      filter_upwards [hL v] with x hx
      change inner ℂ (L v x) (L v x) = (w x) • inner ℂ (v x) (v x)
      rw [hx, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
      simp only [norm_mul, NNReal.smul_def, Complex.real_smul]
      have h := congrArg Complex.ofReal
        (show (‖c x‖ * ‖v x‖) ^ 2 = (w x : ℝ) * ‖v x‖ ^ 2 by rw [mul_pow, hc2])
      change (Complex.ofReal (‖c x‖ * ‖v x‖)) ^ 2 =
        Complex.ofReal (w x : ℝ) * Complex.ofReal ‖v x‖ ^ 2
      rw [Complex.ofReal_mul]
      simpa only [Complex.ofReal_mul, Complex.ofReal_pow] using h
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hi
    have hsq : ‖J v‖ ^ 2 = ‖v‖ ^ 2 := by exact_mod_cast hi
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
  let S : Lp ℂ 2 ν →ₗᵢ[ℂ] Lp ℂ 2 μ := ⟨J, hnorm⟩
  have hsurj : Function.Surjective S := by
    intro v
    let g (x : X) := v x / c x
    have heq (x : X) : c x * g x = v x := by dsimp only [g]; field_simp [hc0 x]
    have hg : MemLp g 2 ν := (hmem g ((Lp.stronglyMeasurable v).div hc)).mpr
      (funext heq ▸ Lp.memLp v)
    refine ⟨hg.toLp g, Lp.ext ?_⟩
    filter_upwards [hL (hg.toLp g), hμ.ae_le hg.coeFn_toLp] with x hx hy
    change L (hg.toLp g) x = v x
    rw [hx, hy, heq]
  exact ⟨LinearIsometryEquiv.ofSurjective S hsurj, hL⟩

end
section
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [NormalSpace G] [MeasurableSpace G] [BorelSpace G]
variable (μ : Measure G) [μ.IsMulLeftInvariant] [μ.Regular]

local notation "τ(" g ")" =>
  Lp.compMeasurePreservingₗᵢ ℂ (fun y : G ↦ g⁻¹ * y) (measurePreserving_mul_left μ g⁻¹)

/-- Left translation preserves Haar measure and acts unitarily on L². -/
private theorem haar_unitary_translate (g : G) :
    ∃ U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ, (∀ v, U v = τ(g) v) ∧ (∀ v, U.symm v = τ(g⁻¹) v) := by
  let V := Lp ℂ 2 μ
  have hinv (t : G) (v : V) : τ(t) (τ(t⁻¹) v) = v := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_compMeasurePreserving (τ(t⁻¹) v) (measurePreserving_mul_left μ t⁻¹),
      (measurePreserving_mul_left μ t⁻¹).quasiMeasurePreserving.ae_eq_comp
        (Lp.coeFn_compMeasurePreserving v (measurePreserving_mul_left μ (t⁻¹)⁻¹))] with y h1 h2
    exact h1.trans (h2.trans (congrArg (fun p : G ↦ v p) (by group)))
  let T : V ≃ₗ[ℂ] V :=
    { (τ(g) : V →ₗᵢ[ℂ] V).toLinearMap with
      invFun := τ(g⁻¹)
      left_inv := fun v ↦ by
        change τ(g⁻¹) (τ(g) v) = v
        simpa only [inv_inv] using hinv g⁻¹ v
      right_inv := hinv g }
  exact ⟨⟨T, fun v ↦ (τ(g)).norm_map v⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩

/-- On a weighted Haar L² space, the normalized translations are unitaries that escape
weakly, with explicit square-root density ratios on Haar representatives. -/
private theorem weighted_escaping_translations (w : G → ℝ≥0) (hw : Measurable w) (hp : ∀ x, 0 < w x) :
    let W := Lp ℂ 2 (μ.withDensity (fun x ↦ (w x : ℝ≥0∞)))
    ∃ T : G → W ≃ₗᵢ[ℂ] W,
      (∀ g v, (T g v : G → ℂ) =ᵐ[μ] (fun x ↦ ((Real.sqrt (w (g⁻¹ * x)) : ℂ) /
        (Real.sqrt (w x) : ℂ)) * v (g⁻¹ * x))) ∧
      (∀ v (f : StrongDual ℂ W), Tendsto (fun g ↦ f (T g v)) (cocompact G) (𝓝 0)) ∧
      (∀ v (f : StrongDual ℂ W), Tendsto (fun g ↦ f ((T g).symm v)) (cocompact G) (𝓝 0)) := by
  intro W
  obtain ⟨J, hJ⟩ := exists_unweight_L2 μ w hw hp
  choose U hU hUi using haar_unitary_translate μ
  let T (g : G) := (J.trans (U g)).trans J.symm
  refine ⟨T, ?_, ?_, ?_⟩
  · intro g v
    have he : J (T g v) = τ(g) (J v) := (J.apply_symm_apply _).trans (hU g _)
    have h := hJ (T g v)
    rw [he] at h
    filter_upwards [h, Lp.coeFn_compMeasurePreserving (J v) (measurePreserving_mul_left μ g⁻¹),
      (measurePreserving_mul_left μ g⁻¹).quasiMeasurePreserving.ae_eq_comp (hJ v)] with x hx hy hz
    have hout : (Real.sqrt (w x) : ℂ) * T g v x =
        (Real.sqrt (w (g⁻¹ * x)) : ℂ) * v (g⁻¹ * x) := hx.symm.trans (hy.trans hz)
    have hpos : (Real.sqrt (w x) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hp x)).ne'
    field_simp [hpos]
    linear_combination hout
  · intro v f
    let L := f.comp J.symm.toContinuousLinearEquiv.toContinuousLinearMap
    have h := haar_translation_weak_zero μ (J v) L
    exact h.congr fun g ↦ congrArg L (hU g _).symm
  · intro v f
    let L := f.comp J.symm.toContinuousLinearEquiv.toContinuousLinearMap
    have h := (haar_translation_weak_zero μ (J v) L).comp
      (Homeomorph.inv G).isClosedEmbedding.tendsto_cocompact
    exact h.congr fun g ↦ congrArg L (hUi g _).symm

/-- The same normalized shifts for the real density in a weighted Sobolev measure. -/
private theorem weighted_escaping_real (w : G → ℝ) (hw : Measurable w) (hp : ∀ x, 0 < w x) :
    let W := Lp ℂ 2 (μ.withDensity fun x ↦ ENNReal.ofReal (w x))
    ∃ T : G → W ≃ₗᵢ[ℂ] W,
      (∀ g v, (T g v : G → ℂ) =ᵐ[μ] fun x ↦ ((Real.sqrt (w (g⁻¹ * x)) : ℂ) /
        (Real.sqrt (w x) : ℂ)) * v (g⁻¹ * x)) ∧
      ∀ v (f : StrongDual ℂ W), Tendsto (fun g ↦ f ((T g).symm v)) (cocompact G) (𝓝 0) := by
  intro W
  obtain ⟨T, hT, _, hTw⟩ := weighted_escaping_translations μ (fun x ↦ (w x).toNNReal) hw.real_toNNReal
    (fun x ↦ Real.toNNReal_pos.mpr (hp x))
  refine ⟨T, ?_, hTw⟩
  intro g v
  refine (hT g v).mono fun x hx ↦ hx.trans ?_
  have ha (y : G) : (Real.sqrt ((w y).toNNReal : ℝ) : ℂ) = (Real.sqrt (w y) : ℂ) :=
    congrArg (fun r : ℝ ↦ (Real.sqrt r : ℂ)) (Real.coe_toNNReal _ (hp y).le)
  exact congrArg (fun k : ℂ ↦ k * v (g⁻¹ * x)) (congrArg₂ (· / ·) (ha (g⁻¹ * x)) (ha x))

end
section
variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (m : G →ₜ* ℝ≥0ˣ)

local notation "N(" g ")" => (((m g).val : ℝ≥0) : ℝ)

/-- In the window centered at radius R, every fixed point off the unit-norm fiber eventually
has exactly its half-line cutoff value. -/
private theorem cutoff_right_edge {ε : ℝ → ℝ} {ρ : ℝ → G → ℝ}
    (hρ : ∀ᶠ R in atTop, IsModulatedCutoff m R (ε R) (ρ R))
    {u : ℝ → G} (hu : ∀ᶠ R in atTop, N(u R) = R) (x : G) (hx : N(x) ≠ 1) :
    ∀ᶠ R in atTop, ρ R (u R * x) = if N(x) < 1 then 1 else 0 := by
  have hxpos : 0 < N(x) := (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (m x).ne_zero))
  have hm (g k : G) : N(g * k) = N(g) * N(k) := by rw [map_mul, Units.val_mul, NNReal.coe_mul]
  by_cases hlt : N(x) < 1
  · rw [ite_eq_left hlt]
    have hgap : 0 < 1 - N(x) := sub_pos.mpr hlt
    filter_upwards [hρ, hu, eventually_ge_atTop (2 / N(x)), eventually_ge_atTop (1 / (1 - N(x))),
      eventually_ge_atTop (1 : ℝ)] with R hR hU h1 h2 h3
    apply hR.eq_one
    change R⁻¹ + ε R ≤ N(u R * x) ∧ N(u R * x) ≤ R - ε R
    rw [hm, hU]
    have hlo := (div_le_iff₀ hxpos).mp h1
    have hhi := (div_le_iff₀ hgap).mp h2
    have hrinv : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h3
    have heps := hR.outer_left_sub_width_pos
    constructor <;> nlinarith
  · rw [ite_eq_right hlt]
    have hgt : 1 < N(x) := lt_of_le_of_ne (le_of_not_gt hlt) hx.symm
    filter_upwards [hρ, hu, eventually_gt_atTop (0 : ℝ)] with R hR hU hRpos
    apply image_eq_zero_of_notMem_tsupport
    intro h
    have hupper := (hR.support_subset h).2
    change N(u R * x) ≤ R at hupper
    rw [hm, hU] at hupper
    exact (not_lt_of_ge hupper) (by simpa using (mul_lt_mul_of_pos_left hgt hRpos))

/-- Inversion exchanges the two edge profiles of an admissible cutoff. -/
private theorem cutoff_left_edge {ε : ℝ → ℝ} {ρ : ℝ → G → ℝ}
    (hρ : ∀ᶠ R in atTop, IsModulatedCutoff m R (ε R) (ρ R))
    {u : ℝ → G} (hu : ∀ᶠ R in atTop, N(u R) = R) (x : G) (hx : N(x) ≠ 1) :
    ∀ᶠ R in atTop, ρ R ((u R)⁻¹ * x) = if 1 < N(x) then 1 else 0 := by
  have hinv : N(x⁻¹) = N(x)⁻¹ := by rw [map_inv, Units.val_inv_eq_inv_val, NNReal.coe_inv]
  have hx' : N(x⁻¹) ≠ 1 := by simpa only [hinv, ne_eq, inv_eq_one] using hx
  filter_upwards [hρ, cutoff_right_edge m hρ hu x⁻¹ hx'] with R hR hrt
  have he := hR.inv_eq ((u R)⁻¹ * x)
  rw [mul_inv_rev, inv_inv, mul_comm x⁻¹, hrt, hinv] at he
  simpa only [inv_lt_one₀ (show 0 < N(x) from (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (m x).ne_zero)))] using he

/-- The logarithmic boundary fiber has measure zero because the image measure of a proper,
surjective norm is Haar on the nondiscrete group of positive reals. -/
private theorem ae_module_ne_one [MeasurableSpace G] [BorelSpace G] [T2Space G]
    (μ : Measure G) [μ.IsHaarMeasure] (hm : IsProperMap m) (hs : Surjective m) :
    ∀ᵐ x ∂μ, N(x) ≠ 1 := by
  let : MeasurableSpace ℝ≥0ˣ := borel _
  have : BorelSpace ℝ≥0ˣ := ⟨rfl⟩
  let e : ℝ≥0ˣ ≃ₜ ℝ := (Nonneg.unitsHomeomorphPos ℝ).trans Real.expOrderIso.toHomeomorph.symm
  have : LocallyCompactSpace ℝ≥0ˣ := e.isOpenEmbedding.locallyCompactSpace
  have : (𝓝[≠] (1 : ℝ≥0ˣ)).NeBot := by
    have h : (Filter.map e.symm (𝓝[≠] (e 1))).NeBot := inferInstance
    rwa [e.symm.map_punctured_nhds_eq, e.symm_apply_apply] at h
  have : (μ.map m).IsHaarMeasure := Measure.isHaarMeasure_map μ m.toMonoidHom m.continuous hs
    (isProperMap_iff_tendsto_cocompact.mp hm).2
  have h₁ : ∀ᵐ y ∂μ.map m, y ≠ 1 := by
    apply ae_iff.mpr
    simp
  have h₂ := (ae_map_iff m.continuous.measurable.aemeasurable (measurableSet_singleton (1 : ℝ≥0ˣ)).compl).mp h₁
  refine h₂.mono fun x hx he ↦ hx ?_
  exact Units.ext (Subtype.ext he)

/-- A section evaluated at radii tending to infinity escapes every fixed compact set. -/
private theorem norm_section_escapes {u : ℝ → G} (hu : ∀ᶠ R in atTop, N(u R) = R) :
    Tendsto u atTop (cocompact G) := by
  refine hasBasis_cocompact.tendsto_right_iff.mpr fun K hK ↦ ?_
  have hc : Continuous (fun x : G ↦ N(x)) :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)
  obtain ⟨C, hC⟩ := (hK.image hc).bddAbove
  filter_upwards [hu, eventually_gt_atTop C] with R hR hgt
  intro h
  exact (not_le_of_gt hgt) (hR ▸ hC ⟨u R, h, rfl⟩)

section
omit [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {X : Type*} [MeasurableSpace X]

/-- A real-valued multiplication operator on complex L² equals its adjoint. -/
private theorem multiplier_selfadjoint (ν : Measure X) (s : X → ℝ)
    (Q : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν)
    (hQ : ∀ v, (Q v : X → ℂ) =ᵐ[ν] fun x ↦ (s x : ℂ) * v x) : Q.adjoint = Q := by
  apply Eq.symm
  apply (ContinuousLinearMap.eq_adjoint_iff Q Q).mpr
  intro v u
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hQ v, hQ u] with x hv hu
  change inner ℂ (Q v x) (u x) = inner ℂ (v x) (Q u x)
  rw [hv, hu]
  simp [RCLike.inner_apply, mul_left_comm, mul_assoc]

/-- Bounded real multipliers whose symbols eventually agree pointwise almost everywhere
converge strongly on complex L². -/
private theorem multiplier_strong_of_ae_eventually_eq (ν : Measure X)
    (σ : ℝ → X → ℝ) (s : X → ℝ) (hσ : ∀ R, Measurable (σ R)) (hs : Measurable s)
    (hσb : ∀ R x, |σ R x| ≤ 1) (hsb : ∀ x, |s x| ≤ 1)
    (hlim : ∀ᵐ x ∂ν, ∀ᶠ R in atTop, σ R x = s x)
    (P : ℝ → Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) (Q : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν)
    (hP : ∀ R v, (P R v : X → ℂ) =ᵐ[ν] fun x ↦ (σ R x : ℂ) * v x)
    (hQ : ∀ v, (Q v : X → ℂ) =ᵐ[ν] fun x ↦ (s x : ℂ) * v x) (u : Lp ℂ 2 ν) :
    Tendsto (fun R ↦ P R u) atTop (𝓝 (Q u)) := by
  let f (R : ℝ) (x : X) := (σ R x : ℂ) * u x - (s x : ℂ) * u x
  have hu := Lp.aestronglyMeasurable u
  have hm (R) : AEStronglyMeasurable (f R) ν :=
    (((Complex.measurable_ofReal.comp (hσ R)).aestronglyMeasurable.mul hu).sub
    (((Complex.measurable_ofReal.comp hs).aestronglyMeasurable).mul hu))
  have hterm (y : ℝ) (hy : |y| ≤ 1) (x : X) : ‖(y : ℂ) * u x‖ ≤ ‖u x‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) hy
  have hb (R x) : ‖f R x‖ ≤ 2 * ‖u x‖ := by
    refine (norm_sub_le _ _).trans ?_
    linarith [hterm (σ R x) (hσb R x) x, hterm (s x) (hsb x) x]
  have hint : Integrable (fun x ↦ 4 * ‖u x‖ ^ 2) ν :=
    ((memLp_two_iff_integrable_sq_norm hu).mp (Lp.memLp u)).const_mul 4
  have hconv : Tendsto (fun R ↦ ∫ x, ‖f R x‖ ^ 2 ∂ν) atTop (𝓝 0) := by
    have h := tendsto_integral_filter_of_dominated_convergence (l := (atTop : Filter ℝ))
      (F := fun R : ℝ ↦ fun x : X ↦ ‖f R x‖ ^ 2) (f := fun _ : X ↦ (0 : ℝ))
      (fun x ↦ 4 * ‖u x‖ ^ 2) (.of_forall fun R ↦ (hm R).norm.pow 2)
      (.of_forall fun R ↦ .of_forall fun x ↦ ?_) hint ?_
    · simpa using h
    · rw [Real.norm_of_nonneg (sq_nonneg _)]
      nlinarith [hb R x, norm_nonneg (f R x), norm_nonneg (u x)]
    · filter_upwards [hlim] with x hx
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hx] with R hR
      simp [f, hR]
  have heq (R) : ‖P R u - Q u‖ ^ 2 = ∫ x, ‖f R x‖ ^ 2 ∂ν := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def, ← integral_re (L2.integrable_inner _ _)]
    refine integral_congr_ae ?_
    filter_upwards [hP R u, hQ u, Lp.coeFn_sub (P R u) (Q u)] with x hp hq hsub
    have h := (norm_sq_eq_re_inner (𝕜 := ℂ) ((P R u - Q u) x)).symm
    refine h.trans ?_
    rw [hsub]
    change ‖P R u x - Q u x‖ ^ 2 = ‖f R x‖ ^ 2
    rw [hp, hq]
  have hsq : Tendsto (fun R ↦ ‖P R u - Q u‖ ^ 2) atTop (𝓝 0) := by simpa only [heq] using hconv
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa using hsq.sqrt
end

/-- On any weighted Haar L² with absolutely continuous measure, the cutoff translated to
either boundary converges strongly to its real half-space multiplier. It has the original
translated symbol at every admissible radius. -/
private theorem translated_cutoff_strong [MeasurableSpace G] [BorelSpace G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    (μ : Measure G) [μ.IsHaarMeasure] (hm : IsProperMap m) (hs : Surjective m)
    (ν : Measure G) (hν : ν ≪ μ) {ε : ℝ → ℝ} {ρ : ℝ → G → ℝ}
    (hρ : ∀ᶠ R in atTop, IsModulatedCutoff m R (ε R) (ρ R))
    {u : ℝ → G} (hu : ∀ᶠ R in atTop, N(u R) = R) (j : Bool) :
    ∃ (P : ℝ → Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) (Q : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν),
      (∀ R, ‖P R‖ ≤ 1) ∧ ‖Q‖ ≤ 1 ∧ (∀ R, (P R).adjoint = P R) ∧ Q.adjoint = Q ∧
      (∀ v, Tendsto (fun R ↦ P R v) atTop (𝓝 (Q v))) ∧
      (∀ R, IsModulatedCutoff m R (ε R) (ρ R) → ∀ v, (P R v : G → ℂ) =ᵐ[ν]
        fun x ↦ (ρ R ((if j then u R else (u R)⁻¹) * x) : ℂ) * v x) ∧
      ∀ v, (Q v : G → ℂ) =ᵐ[ν] fun x ↦
        ((if (if j then N(x) < 1 else 1 < N(x)) then 1 else 0 : ℝ) : ℂ) * v x := by
  classical
  let σ (R : ℝ) (x : G) : ℝ := if IsModulatedCutoff m R (ε R) (ρ R)
    then ρ R ((if j then u R else (u R)⁻¹) * x) else 0
  let s (x : G) : ℝ := if (if j then N(x) < 1 else 1 < N(x)) then 1 else 0
  have hσ (R) : Measurable (σ R) := by
    by_cases h : IsModulatedCutoff m R (ε R) (ρ R)
    · simpa only [σ, ite_eq_left h, Function.comp_def, Pi.mul_apply, id_eq] using h.measurable.comp ((continuous_const.mul continuous_id).measurable :
        Measurable fun x : G ↦ (if j then u R else (u R)⁻¹) * x)
    · simp [σ, h]
  have hσb (R x) : |σ R x| ≤ 1 := by
    by_cases h : IsModulatedCutoff m R (ε R) (ρ R)
    · simpa [σ, h] using h.abs_le_one ((if j then u R else (u R)⁻¹) * x)
    · simp [σ, h]
  have hc : Continuous (fun x : G ↦ N(x)) :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)
  have hsm : Measurable s := by
    cases j
    · exact Measurable.ite (measurableSet_lt measurable_const hc.measurable) measurable_const measurable_const
    · exact Measurable.ite (measurableSet_lt hc.measurable measurable_const) measurable_const measurable_const
  have hsb (x) : |s x| ≤ 1 := by
    dsimp only [s]
    by_cases h : (if j then N(x) < 1 else 1 < N(x)) <;> simp only [h, ite_true, ite_false] <;> norm_num
  have hlim : ∀ᵐ x ∂ν, ∀ᶠ R in atTop, σ R x = s x := by
    filter_upwards [hν.ae_le (ae_module_ne_one m μ hm hs)] with x hx
    cases j
    · filter_upwards [hρ, cutoff_left_edge m hρ hu x hx] with R hR he
      simpa [σ, s, hR] using he
    · filter_upwards [hρ, cutoff_right_edge m hρ hu x hx] with R hR he
      simpa [σ, s, hR] using he
  refine ⟨fun R ↦ lpCutoffMultiplier ν (σ R) (hσ R) (hσb R), lpCutoffMultiplier ν s hsm hsb,
    fun R ↦ (exists_lpCutoffMultiplier ν (σ R) (hσ R) (hσb R)).choose_spec.1,
    (exists_lpCutoffMultiplier ν s hsm hsb).choose_spec.1,
    fun R ↦ multiplier_selfadjoint ν (σ R) _ (lpCutoffMultiplier_apply ν (σ R) (hσ R) (hσb R)),
    multiplier_selfadjoint ν s _ (lpCutoffMultiplier_apply ν s hsm hsb),
    multiplier_strong_of_ae_eventually_eq ν σ s hσ hsm hσb hsb hlim _ _
      (fun R ↦ lpCutoffMultiplier_apply ν (σ R) (hσ R) (hσb R))
      (lpCutoffMultiplier_apply ν s hsm hsb), ?_, lpCutoffMultiplier_apply ν s hsm hsb⟩
  intro R hR v
  refine (lpCutoffMultiplier_apply ν (σ R) (hσ R) (hσb R) v).mono fun x hx ↦ hx.trans ?_
  simp only [σ, ite_eq_left hR]

end
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "NucL(" A ", " T ")" =>
  (⟨(A) * (T).val, mul_mem_nuclearEndomorphisms_left (A) (T)⟩ : nuclearEndomorphisms H)
local notation "NucR(" A ", " T ")" =>
  (⟨(T).val * (A), mul_mem_nuclearEndomorphisms_right (A) (T)⟩ : nuclearEndomorphisms H)
local notation "Com(" A ", " T ")" => (NucL(A, T) - NucR(A, T))
local notation "Tensor(" z ")" =>
  (⟨tensorToFiniteRank (z), tensorToFiniteRank_mem_nuclearEndomorphisms (z)⟩ : nuclearEndomorphisms H)

/-- The trace norm of a difference is bounded by the sum of the two norms. -/
private theorem traceNorm_sub_le (T S : nuclearEndomorphisms H) : traceNorm (T - S) ≤ traceNorm T + traceNorm S := by
  let : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
  have hneg : traceNorm (-S) = traceNorm S := by
    have h := (traceNorm_normedSpaceCore (H := H)).norm_smul (-1 : ℂ) S
    simpa only [neg_one_smul, norm_neg, norm_one, one_mul] using h
  rw [sub_eq_add_neg, ← hneg]
  exact traceNorm_add_le _ _

/-- The trace norm of a commutator is bounded by twice the product of the operator and trace
norms. -/
private theorem traceNorm_commutator_le (A : H →L[ℂ] H) (T : nuclearEndomorphisms H) :
    traceNorm Com(A, T) ≤ 2 * ‖A‖ * traceNorm T := by
  have h := (traceNorm_sub_le NucL(A, T) NucR(A, T)).trans
    (add_le_add (traceNorm_mul_left_le A T) (traceNorm_mul_right_le A T))
  linarith

/-- Strong convergence of the operators and their adjoints gives trace-norm convergence of their
commutators with a finite tensor. -/
private theorem traceNorm_commutator_tensor_tendsto (S : ℝ → H →L[ℂ] H)
    (hS : ∀ v, Tendsto (fun R ↦ S R v) atTop (𝓝 0))
    (hSa : ∀ v, Tendsto (fun R ↦ (S R).adjoint v) atTop (𝓝 0))
    (z : StrongDual ℂ H ⊗[ℂ] H) :
    Tendsto (fun R ↦ traceNorm Com(S R, Tensor(z))) atTop (𝓝 0) := by
  induction z using TensorProduct.inductionOn with
  | tmul f y =>
    obtain ⟨v, hv⟩ := (InnerProductSpace.toDual ℂ H).surjective f
    have hl (R) : NucL(S R, Tensor(f ⊗ₜ[ℂ] y)) =
        ⟨f.smulRight (S R y), smulRight_mem_nuclearEndomorphisms ..⟩ := by
      apply Subtype.ext
      ext x
      change S R (tensorToFiniteRank _ x) = f x • S R y
      rw [tensorToFiniteRank_tmul, map_smul]
    let g (R) := InnerProductSpace.toDual ℂ H ((S R).adjoint v)
    have hr (R) : NucR(S R, Tensor(f ⊗ₜ[ℂ] y)) =
        ⟨(g R).smulRight y, smulRight_mem_nuclearEndomorphisms ..⟩ := by
      apply Subtype.ext
      ext x
      change tensorToFiniteRank (f ⊗ₜ[ℂ] y) (S R x) = (g R x) • y
      rw [tensorToFiniteRank_tmul, ← hv]
      change inner ℂ v (S R x) • y = inner ℂ ((S R).adjoint v) x • y
      rw [ContinuousLinearMap.adjoint_inner_left]
    have hlim : Tendsto (fun R ↦ ‖f‖ * ‖S R y‖ + ‖(S R).adjoint v‖ * ‖y‖) atTop (𝓝 0) := by
      simpa using (((hS y).norm.const_mul ‖f‖).add ((hSa v).norm.mul_const ‖y‖))
    refine squeeze_zero (fun R ↦ traceNorm_nonneg _) (fun R ↦ ?_) hlim
    rw [hl R, hr R]
    refine (traceNorm_sub_le _ _).trans ?_
    rw [traceNorm_smulRight, traceNorm_smulRight, show ‖g R‖ = ‖(S R).adjoint v‖ from
      (InnerProductSpace.toDual ℂ H).norm_map _]
  | add z w hz hw =>
    have heq (R) : Com(S R, Tensor(z + w)) = Com(S R, Tensor(z)) + Com(S R, Tensor(w)) := by
      apply Subtype.ext
      simp only [Submodule.coe_add, Submodule.coe_sub, map_add, mul_add, add_mul]
      abel
    simp_rw [heq]
    exact squeeze_zero (fun R ↦ traceNorm_nonneg _) (fun R ↦ traceNorm_add_le _ _) (by simpa using hz.add hw)

/-- Both sided products with a fixed trace-class kernel absorb a uniformly bounded
strongly and adjoint-strongly null family, in the commutator trace norm. -/
private theorem traceNorm_commutator_nuclear_tendsto (S : ℝ → H →L[ℂ] H) (hbound : ∀ R, ‖S R‖ ≤ 2)
    (hS : ∀ v, Tendsto (fun R ↦ S R v) atTop (𝓝 0))
    (hSa : ∀ v, Tendsto (fun R ↦ (S R).adjoint v) atTop (𝓝 0))
    (T : nuclearEndomorphisms H) :
    Tendsto (fun R ↦ traceNorm Com(S R, T)) atTop (𝓝 0) := by
  refine Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
  obtain ⟨z, hz⟩ := exists_tensorToFiniteRank_traceNorm_sub_lt T (by positivity : 0 < ε / 8)
  have h := (traceNorm_commutator_tensor_tendsto S hS hSa z).eventually_lt_const (half_pos hε)
  filter_upwards [h] with R hR
  have heq : Com(S R, T) = Com(S R, T - Tensor(z)) + Com(S R, Tensor(z)) := by
    apply Subtype.ext
    simp only [Submodule.coe_sub, Submodule.coe_add, mul_sub, sub_mul]
    abel
  have hbound' : traceNorm Com(S R, T - Tensor(z)) ≤ 4 * traceNorm (T - Tensor(z)) := by
    refine (traceNorm_commutator_le (S R) _).trans (mul_le_mul_of_nonneg_right ?_ (traceNorm_nonneg _))
    linarith [hbound R]
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (traceNorm_nonneg _), heq]
  change traceNorm (T - Tensor(z)) < ε / 8 at hz
  linarith [traceNorm_add_le Com(S R, T - Tensor(z)) Com(S R, Tensor(z))]

/-- Compressing to a fixed window, trace-norm convergence of the kernels and
strong convergence of contractive self-adjoint edge profiles imply trace-norm
convergence of their commutators. -/
private theorem cutoff_commutator_trace_limit
    (P : ℝ → H →L[ℂ] H) (Q : H →L[ℂ] H) (hP : ∀ R, ‖P R‖ ≤ 1) (hQ : ‖Q‖ ≤ 1)
    (hPa : ∀ R, (P R).adjoint = P R) (hQa : Q.adjoint = Q)
    (hlim : ∀ v, Tendsto (fun R ↦ P R v) atTop (𝓝 (Q v)))
    (K : ℝ → nuclearEndomorphisms H) (J : nuclearEndomorphisms H)
    (hK : Tendsto (fun R ↦ traceNorm (K R - J)) atTop (𝓝 0)) :
    Tendsto (fun R ↦ traceNorm (Com(P R, K R) - Com(Q, J))) atTop (𝓝 0) := by
  let S (R) := P R - Q
  have hSn (R) : ‖S R‖ ≤ 2 := (norm_sub_le ..).trans (by linarith [hP R])
  have hs (v) : Tendsto (fun R ↦ S R v) atTop (𝓝 0) := by
    simpa only [S, sub_apply, sub_self] using (hlim v).sub (tendsto_const_nhds (x := Q v))
  have hsa (v) : Tendsto (fun R ↦ (S R).adjoint v) atTop (𝓝 0) := by
    simpa only [S, map_sub, hPa, hQa] using hs v
  have heq (R) : Com(P R, K R) - Com(Q, J) = Com(P R, K R - J) + Com(S R, J) := by
    apply Subtype.ext
    simp only [S, Submodule.coe_add, Submodule.coe_sub, sub_mul, mul_sub]
    abel
  have hbase := traceNorm_commutator_nuclear_tendsto S hSn hs hsa J
  have htotal : Tendsto (fun R ↦ 2 * traceNorm (K R - J) + traceNorm Com(S R, J)) atTop (𝓝 0) := by
    simpa using (hK.const_mul 2).add hbase
  simp_rw [heq]
  refine squeeze_zero (fun R ↦ traceNorm_nonneg _) (fun R ↦ ?_) htotal
  refine (traceNorm_add_le _ _).trans (add_le_add ?_ le_rfl)
  exact (traceNorm_commutator_le (P R) _).trans (mul_le_mul_of_nonneg_right (by linarith [hP R]) (traceNorm_nonneg _))

end
section
variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (m : G →ₜ* ℝ≥0ˣ)
local notation "N(" g ")" => (((m g).val : ℝ≥0) : ℝ)
local notation "L(" g ")" => Real.log N(g)

/-- An admissible cutoff is one in the log interval shortened on each side by log 2,
and zero outside the full interval. -/
private theorem cutoff_log_plateau {R ε : ℝ} {ρ : G → ℝ}
    (hc : IsModulatedCutoff m R ε ρ) (hR : 2 ≤ R) (x : G) :
    (|L(x)| ≤ Real.log R - Real.log 2 → ρ x = 1) ∧ (Real.log R < |L(x)| → ρ x = 0) := by
  have hR0 : 0 < R := by linarith
  have hx : 0 < N(x) := NNReal.coe_pos.mpr (Units.zero_lt _)
  constructor
  · intro h
    have hl : 2 / R ≤ N(x) := by
      apply (Real.log_le_log_iff (by positivity) hx).mp
      rw [Real.log_div (by norm_num) hR0.ne']
      linarith [(abs_le.mp h).1]
    have hu : N(x) ≤ R / 2 := by
      apply (Real.log_le_log_iff hx (by positivity)).mp
      rw [Real.log_div hR0.ne' (by norm_num)]
      exact (abs_le.mp h).2
    have hε := hc.outer_left_sub_width_pos
    have hri : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    apply hc.eq_one
    change R⁻¹ + ε ≤ N(x) ∧ N(x) ≤ R - ε
    rw [div_eq_mul_inv] at hl
    constructor <;> linarith
  · intro h
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    obtain ⟨hl, hu⟩ := hc.support_subset hmem
    change R⁻¹ ≤ N(x) at hl
    change N(x) ≤ R at hu
    have hlo := Real.log_le_log (inv_pos.mpr hR0) hl
    rw [Real.log_inv] at hlo
    exact (not_le_of_gt h) (abs_le.mpr ⟨hlo, Real.log_le_log hx hu⟩)

/-- Two input/output points at distance at most B on the real line, one of which is
outside the plateau, both lie in a single translated window whenever their cutoff values differ. -/
private theorem paired_log_windows {a b t c B : ℝ} (hc : 0 ≤ c) (hB : 0 ≤ B)
    (ht : c + 2 * B < t) (hd : |a - b| ≤ B)
    (hinner : t-c < |a| ∨ t-c < |b|) (houter : |a| ≤ t ∨ |b| ≤ t) :
    (|a-t| ≤ c+B ∧ |b-t| ≤ c+B ∧ ¬ |a+t| ≤ c+B) ∨
    (|a+t| ≤ c+B ∧ |b+t| ≤ c+B ∧ ¬ |a-t| ≤ c+B) := by
  obtain ⟨hab, hba⟩ := abs_le.mp hd
  by_cases ha : 0 ≤ a
  · left
    rw [abs_of_nonneg ha] at hinner houter
    by_cases hb : 0 ≤ b
    · rw [abs_of_nonneg hb] at hinner houter
      rcases hinner with h | h <;> rcases houter with h' | h' <;>
        refine ⟨abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩, fun he ↦ ?_⟩ <;>
        linarith [(abs_le.mp he).2]
    · rw [abs_of_nonpos (le_of_not_ge hb)] at hinner houter
      rcases hinner with h | h <;> exfalso <;> linarith
  · right
    rw [abs_of_nonpos (le_of_not_ge ha)] at hinner houter
    by_cases hb : 0 ≤ b
    · rw [abs_of_nonneg hb] at hinner houter
      rcases hinner with h | h <;> exfalso <;> linarith
    · rw [abs_of_nonpos (le_of_not_ge hb)] at hinner houter
      rcases hinner with h | h <;> rcases houter with h' | h' <;>
        refine ⟨abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩, fun he ↦ ?_⟩ <;>
        linarith [(abs_le.mp he).1]

/-- For every compactly supported convolution kernel, its cutoff commutator kernel
splits exactly into the two fixed-width logarithmic windows at ±log R. Both the input and
output of each pair lie in the same window. The same window width works for all admissible
cutoff symbols and transition widths. -/
private theorem cutoff_commutator_kernel_split (φ : G → ℂ) (hφ : HasCompactSupport φ) :
    ∃ b : ℝ, 0 < b ∧ ∀ᶠ R : ℝ in atTop, ∀ {ε : ℝ} {ρ : G → ℝ}, IsModulatedCutoff m R ε ρ →
      ∀ x g : G,
        let y := g⁻¹ * x
        let K := ((ρ x - ρ y : ℝ) : ℂ) * φ g
        let t := Real.log R
        K = (if |L(x)-t| ≤ b ∧ |L(y)-t| ≤ b then K else 0) +
          (if |L(x)+t| ≤ b ∧ |L(y)+t| ≤ b then K else 0) := by
  have hlog : Continuous (fun x : G ↦ L(x)) :=
    (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)).log
      fun x ↦ NNReal.coe_ne_zero.mpr (m x).ne_zero
  obtain ⟨A, hA⟩ := (hφ.isCompact.image hlog.abs).bddAbove
  let B := max A 1
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_right ..)
  have hc : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨Real.log 2 + B, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℝ),
    Real.tendsto_log_atTop.eventually_gt_atTop (Real.log 2 + 2 * B)] with R hR ht
  intro ε ρ hcut x g
  dsimp only
  by_cases hφg : φ g = 0
  · simp [hφg]
  by_cases hdif : ρ x = ρ (g⁻¹ * x)
  · simp [hdif]
  have hg : |L(g)| ≤ B := (hA ⟨g, subset_tsupport _ (mem_support.mpr hφg), rfl⟩).trans (le_max_left ..)
  have hcoord : L(g⁻¹ * x) = L(x) - L(g) := by
    have hg0 : N(g) ≠ 0 := NNReal.coe_ne_zero.mpr (m g).ne_zero
    have hx0 : N(x) ≠ 0 := NNReal.coe_ne_zero.mpr (m x).ne_zero
    rw [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, NNReal.coe_mul, NNReal.coe_inv,
      Real.log_mul (inv_ne_zero hg0) hx0, Real.log_inv]
    ring
  obtain ⟨hx₁, hx₀⟩ := cutoff_log_plateau m hcut hR x
  obtain ⟨hy₁, hy₀⟩ := cutoff_log_plateau m hcut hR (g⁻¹ * x)
  have hlo : Real.log R - Real.log 2 < |L(x)| ∨ Real.log R - Real.log 2 < |L(g⁻¹ * x)| := by
    by_contra! h
    exact hdif ((hx₁ h.1).trans (hy₁ h.2).symm)
  have hhi : |L(x)| ≤ Real.log R ∨ |L(g⁻¹ * x)| ≤ Real.log R := by
    by_contra! h
    exact hdif ((hx₀ h.1).trans (hy₀ h.2).symm)
  have hxy : |L(x) - L(g⁻¹ * x)| ≤ B := by simpa only [hcoord, sub_sub_cancel] using hg
  rcases paired_log_windows hc.le hB.le ht hxy hlo hhi with h | h
  · simp only [h.1, h.2.1, h.2.2, true_and, false_and, ite_true, ite_false, add_zero]
  · simp only [h.1, h.2.1, h.2.2, true_and, false_and, ite_true, ite_false, zero_add]

section
variable [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
variable (μ : Measure G) [μ.IsHaarMeasure] (ν : Measure G)
local notation "W" => Lp ℂ 2 ν
local notation "Op" => W →L[ℂ] W

/-- Haar invariance transports a.e. input representatives through the group convolution kernel. -/
private theorem convolution_translate_rep {f h : G → ℂ} (he : f =ᵐ[μ] h) (x : G) :
    (fun g ↦ f (g⁻¹ * x)) =ᵐ[μ] (fun g ↦ h (g⁻¹ * x)) := by
  have hp : MeasurePreserving (fun g : G ↦ g⁻¹ * x) μ μ :=
    (measurePreserving_mul_right μ x).comp (Measure.measurePreserving_inv μ)
  exact hp.quasiMeasurePreserving.ae_eq_comp he

/-- The commutator has kernel (ρ(x)−ρ(g⁻¹x))φ(g), with integrability for a.e. output. -/
private theorem convolution_commutator_rep (hμ : μ ≪ ν) (φ r : G → ℂ) (A M : Op)
    (hA : ∀ v : W, ∀ᵐ x ∂μ, Integrable (fun g ↦ φ g * v (g⁻¹ * x)) μ ∧
      A v x = ∫ g, φ g * v (g⁻¹ * x) ∂μ)
    (hM : ∀ v : W, (M v : G → ℂ) =ᵐ[μ] fun x ↦ r x * v x) (v : W) :
    ∀ᵐ x ∂μ, Integrable (fun g ↦ ((r x - r (g⁻¹ * x)) * φ g) * v (g⁻¹ * x)) μ ∧
      (M * A - A * M) v x = ∫ g, ((r x - r (g⁻¹ * x)) * φ g) * v (g⁻¹ * x) ∂μ := by
  filter_upwards [hA v, hA (M v), hM (A v), hμ.ae_le (Lp.coeFn_sub (M (A v)) (A (M v)))]
    with x hAv hAm hMa hsub
  have he := convolution_translate_rep μ (hM v) x
  have hf : (fun g ↦ r x * (φ g * v (g⁻¹ * x)) - φ g * M v (g⁻¹ * x)) =ᵐ[μ]
      fun g ↦ ((r x - r (g⁻¹ * x)) * φ g) * v (g⁻¹ * x) := by
    filter_upwards [he] with g hg
    rw [show M v (g⁻¹ * x) = _ from hg]
    ring
  refine ⟨((hAv.1.const_mul _).sub hAm.1).congr hf, ?_⟩
  change (M (A v) - A (M v)) x = _
  rw [hsub]
  change M (A v) x - A (M v) x = _
  rw [hMa, hAv.2, hAm.2, ← integral_const_mul, ← integral_sub (hAv.1.const_mul _) hAm.1]
  exact integral_congr_ae hf

/-- Compressing any such kernel by a multiplier gives both of its scalar window factors. -/
private theorem kernel_compression_rep (K : G → G → ℂ) (D P : Op) (s : G → ℂ)
    (hD : ∀ v : W, ∀ᵐ x ∂μ, Integrable (fun g ↦ K x g * v (g⁻¹ * x)) μ ∧
      D v x = ∫ g, K x g * v (g⁻¹ * x) ∂μ)
    (hP : ∀ v : W, (P v : G → ℂ) =ᵐ[μ] fun x ↦ s x * v x) (v : W) :
    ∀ᵐ x ∂μ, Integrable (fun g ↦ (s x * s (g⁻¹ * x) * K x g) * v (g⁻¹ * x)) μ ∧
      (P * D * P) v x = ∫ g, (s x * s (g⁻¹ * x) * K x g) * v (g⁻¹ * x) ∂μ := by
  filter_upwards [hP (D (P v)), hD (P v)] with x hPDP hDP
  have hf : (fun g ↦ s x * (K x g * P v (g⁻¹ * x))) =ᵐ[μ]
      fun g ↦ (s x * s (g⁻¹ * x) * K x g) * v (g⁻¹ * x) := by
    filter_upwards [convolution_translate_rep μ (hP v) x] with g hg
    rw [show P v (g⁻¹ * x) = _ from hg]
    ring
  refine ⟨(hDP.1.const_mul _).congr hf, ?_⟩
  change P (D (P v)) x = _
  rw [hPDP, hDP.2, ← integral_const_mul]
  exact integral_congr_ae hf

/-- An almost-everywhere decomposition of an integral kernel gives the corresponding sum of the
two compressed operators. -/
private theorem kernel_compressions_add (hν : ν ≪ μ) (hμ : μ ≪ ν) (K : G → G → ℂ) (D P Q : Op)
    (p q : G → ℂ)
    (hD : ∀ v : W, ∀ᵐ x ∂μ, Integrable (fun g ↦ K x g * v (g⁻¹ * x)) μ ∧
      D v x = ∫ g, K x g * v (g⁻¹ * x) ∂μ)
    (hp : ∀ v : W, (P v : G → ℂ) =ᵐ[μ] fun x ↦ p x * v x)
    (hq : ∀ v : W, (Q v : G → ℂ) =ᵐ[μ] fun x ↦ q x * v x)
    (hK : ∀ x g, K x g = p x * p (g⁻¹ * x) * K x g + q x * q (g⁻¹ * x) * K x g) :
    D = P * D * P + Q * D * Q := by
  apply ContinuousLinearMap.ext
  intro v
  apply Lp.ext
  apply hν.ae_eq
  filter_upwards [hD v, kernel_compression_rep μ ν K D P p hD hp v,
    kernel_compression_rep μ ν K D Q q hD hq v,
    hμ.ae_le (Lp.coeFn_add ((P * D * P) v) ((Q * D * Q) v))] with x hd hp hq ha
  change D v x = (((P * D * P) v + (Q * D * Q) v) : W) x
  rw [ha]
  change D v x = (P * D * P) v x + (Q * D * Q) v x
  rw [hd.2, hp.2, hq.2, ← integral_add hp.1 hq.1]
  apply integral_congr_ae (.of_forall fun g ↦ ?_)
  exact (congrArg (· * v (g⁻¹ * x)) (hK x g)).trans (add_mul ..)

/-- On the weighted ambient model itself, the cutoff-convolution commutator equals
the sum of its two same-window compressions, with real contractive cutoff projections. -/
private theorem weighted_convolution_two_edge_localization (hν : ν ≪ μ) (hμ : μ ≪ ν)
    (φ : G → ℂ) (hφ : HasCompactSupport φ) (A : Op)
    (hA : ∀ v : W, ∀ᵐ x ∂μ, Integrable (fun g ↦ φ g * v (g⁻¹ * x)) μ ∧
      A v x = ∫ g, φ g * v (g⁻¹ * x) ∂μ) :
    ∃ b : ℝ, 0 < b ∧ ∀ᶠ R : ℝ in atTop, ∃ P Q : Op,
      (∀ v : W, (P v : G → ℂ) =ᵐ[μ] fun x ↦ if |L(x) - Real.log R| ≤ b then v x else 0) ∧
      (∀ v : W, (Q v : G → ℂ) =ᵐ[μ] fun x ↦ if |L(x) + Real.log R| ≤ b then v x else 0) ∧
      ∀ {ε : ℝ} {ρ : G → ℝ} (hc : IsModulatedCutoff m R ε ρ),
        let M := modulatedCutoffOperator m ν hc
        let D := M * A - A * M
        D = P * D * P + Q * D * Q := by
  obtain ⟨b, hb, hsplit⟩ := cutoff_commutator_kernel_split m φ hφ
  refine ⟨b, hb, ?_⟩
  filter_upwards [hsplit] with R hR
  let l (x : G) := L(x)
  have hl : Continuous l := (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)).log
    fun x ↦ NNReal.coe_ne_zero.mpr (m x).ne_zero
  let p (c : ℝ) (x : G) : ℝ := if |l x - c| ≤ b then 1 else 0
  have hpm (c) : Measurable (p c) := Measurable.ite
    (measurableSet_le ((hl.sub continuous_const).abs).measurable measurable_const) measurable_const measurable_const
  have hpb (c x) : |p c x| ≤ 1 := by dsimp only [p]; split <;> norm_num
  let P (c) := lpCutoffMultiplier ν (p c) (hpm c) (hpb c)
  have hP (c) (v : W) : (P c v : G → ℂ) =ᵐ[μ] fun x ↦ (p c x : ℂ) * v x :=
    hμ.ae_eq (lpCutoffMultiplier_apply ν (p c) (hpm c) (hpb c) v)
  have hpi (c) (v : W) : (P c v : G → ℂ) =ᵐ[μ] fun x ↦ if |l x - c| ≤ b then v x else 0 := by
    refine (hP c v).mono fun x hx ↦ hx.trans ?_
    dsimp only [p]
    split <;> simp_all only [Complex.ofReal_one, Complex.ofReal_zero, one_mul, zero_mul]
  refine ⟨P (Real.log R), P (-Real.log R), hpi _,
    (by simpa only [sub_neg_eq_add] using hpi (-Real.log R)), ?_⟩
  intro ε ρ hc
  dsimp only
  let M := modulatedCutoffOperator m ν hc
  let K (x g : G) := ((ρ x : ℂ) - (ρ (g⁻¹ * x) : ℂ)) * φ g
  have hK := convolution_commutator_rep μ ν hμ φ (fun x ↦ (ρ x : ℂ)) A M hA
    (fun v ↦ hμ.ae_eq (modulatedCutoffOperator_apply m ν hc v))
  refine kernel_compressions_add μ ν hν hμ K (M * A - A * M) _ _
    (fun x ↦ (p (Real.log R) x : ℂ)) (fun x ↦ (p (-Real.log R) x : ℂ)) hK (hP _) (hP _) ?_
  intro x g
  have he (a c : Prop) [Decidable a] [Decidable c] (z : ℂ) :
      (if a ∧ c then z else 0) =
        ((if a then 1 else 0 : ℝ) : ℂ) * ((if c then 1 else 0 : ℝ) : ℂ) * z := by
    by_cases h : a <;> by_cases h' : c <;> simp [h, h']
  have h := hR hc x g
  simp only [he, Complex.ofReal_sub] at h
  simpa only [K, p, l, sub_neg_eq_add] using h

end
section
variable [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
variable (μ : Measure G) [μ.IsHaarMeasure]
local notation "H(" a ", " b ", " s ")" => CompactIntervalSobolev μ (fun g : G ↦ L(g)) a b s
local notation "ν(" a ", " b ", " s ")" => (μ.withDensity fun x : G ↦ ENNReal.ofReal (intervalSobolevDensity a b s L(x)))

/-- The exact two-window identity holds for the Chapter 10 ambient Hardy–Sobolev
test action, with no additional hypotheses on the operator. -/
private theorem hardySobolev_test_commutator_windows (a b s : ℝ) (hab : a ≤ b) (hs : 0 ≤ s)
    (φ : BruhatCompactSupport G) :
    let A : H(a, b, s) →L[ℂ] H(a, b, s) := hardySobolevTestAction μ m a b s hab hs φ
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ R : ℝ in atTop, ∃ P Q : H(a, b, s) →L[ℂ] H(a, b, s),
      (∀ v : H(a, b, s), (P v : G → ℂ) =ᵐ[μ] fun x ↦ if |L(x) - Real.log R| ≤ d then v x else 0) ∧
      (∀ v : H(a, b, s), (Q v : G → ℂ) =ᵐ[μ] fun x ↦ if |L(x) + Real.log R| ≤ d then v x else 0) ∧
      ∀ {ε : ℝ} {ρ : G → ℝ} (hc : IsModulatedCutoff m R ε ρ),
        let M : H(a, b, s) →L[ℂ] H(a, b, s) := modulatedCutoffOperator m ν(a, b, s) hc
        let D := M * A - A * M
        D = P * D * P + Q * D * Q := by
  intro A
  have hν : ν(a, b, s) ≪ μ := withDensity_absolutelyContinuous ..
  have hlog : Continuous (fun x : G ↦ L(x)) :=
    (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)).log
      fun x ↦ NNReal.coe_ne_zero.mpr (m x).ne_zero
  have hw : Measurable (fun x : G ↦ intervalSobolevDensity a b s L(x)) := by
    have h : Measurable (intervalSobolevDensity a b s) := by unfold intervalSobolevDensity; fun_prop
    exact h.comp hlog.measurable
  have hμ : μ ≪ ν(a, b, s) := withDensity_absolutelyContinuous' hw.ennreal_ofReal.aemeasurable
    (.of_forall fun x ↦ (ENNReal.ofReal_pos.mpr (mul_pos (lt_max_of_lt_left (Real.exp_pos _))
      (Real.rpow_pos_of_pos (by positivity) _))).ne')
  have hc : Continuous φ.val := continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp φ.property.1)
  have hφ : AEMeasurable φ.val μ := hc.measurable.aemeasurable
  have hb := hc.bounded_above_of_compact_support (show HasCompactSupport φ.val from φ.property.2)
  refine weighted_convolution_two_edge_localization m μ ν(a, b, s) hν hμ φ.val φ.property.2 A ?_
  intro v
  have h := hardySobolevConvolution_apply μ m a b s hab hs φ.val hφ φ.property.2 hb v
  rw [hardySobolevConvolution_eq_testAction μ m a b s hab hs φ hφ hb] at h
  exact h

end

end
section

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local notation "CL(" U ")" => (U).toContinuousLinearEquiv.toContinuousLinearMap

/-- Pulling back a compressed commutator through a unitary transfers each of its two masks. -/
private theorem move_compressed_commutator (U : H ≃ₗᵢ[ℂ] H) (A S P Q M : H →L[ℂ] H)
    (hS : ∀ v, U (S v) = P (U v)) (hQ : ∀ v, U (Q v) = M (U v))
    (hSQ : ∀ v, S (Q v) = Q (S v)) :
    let K := S * (CL(U.symm) * A * CL(U)) * S
    CL(U) * (Q * K - K * Q) * CL(U.symm) = P * (M * A - A * M) * P := by
  intro K
  apply ContinuousLinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := U.surjective x
  change U ((Q * K - K * Q) (U.symm (U y))) = _
  rw [U.symm_apply_apply]
  change U (Q (K y) - K (Q y)) = P (M (A (P (U y))) - A (M (P (U y))))
  have hk (v : H) : K v = S (U.symm (A (U (S v)))) := rfl
  simp only [map_sub, hk]
  rw [← hSQ, hSQ y]
  simp only [hS, hQ, LinearIsometryEquiv.apply_symm_apply]

/-- The fixed-window limiting commutator has output in the closed range whenever
the central window and limiting half-line mask preserve that range. -/
private theorem localized_commutator_range (C P Q : H →L[ℂ] H)
    (hP : ∀ v ∈ closure (range C), P v ∈ closure (range C))
    (hQ : ∀ v ∈ closure (range C), Q v ∈ closure (range C)) (v : H) :
    (Q * (P * C * P) - (P * C * P) * Q) v ∈ closure (range C) := by
  let V := C.toLinearMap.range.topologicalClosure
  change Q (P (C (P v))) - P (C (P (Q v))) ∈ V
  exact V.sub_mem (hQ _ (hP _ (subset_closure ⟨_, rfl⟩))) (hP _ (subset_closure ⟨_, rfl⟩))
end

section
variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] (ν : Measure G)
local notation "W" => Lp ℂ 2 ν

/-- The scalar density factor in a normalized translation cancels from the
intertwining relation between multiplication operators. -/
private theorem weighted_multiplier_intertwines (hν : ν ≪ μ) (g : G) (a b : G → ℂ)
    (U : W ≃ₗᵢ[ℂ] W) (w : G → ℂ)
    (hU : ∀ v, (U v : G → ℂ) =ᵐ[μ] fun x ↦ w x * v (g⁻¹ * x))
    (P Q : W →L[ℂ] W) (hP : ∀ v, (P v : G → ℂ) =ᵐ[μ] fun x ↦ a x * v x)
    (hQ : ∀ v, (Q v : G → ℂ) =ᵐ[μ] fun x ↦ b x * v x) (hab : ∀ x, a (g⁻¹ * x) = b x) (v : W) :
    U (P v) = Q (U v) := by
  apply Lp.ext
  apply hν.ae_eq
  filter_upwards [hU (P v), hQ (U v), hU v,
    (measurePreserving_mul_left μ g⁻¹).quasiMeasurePreserving.ae_eq_comp (hP v)] with x h₁ h₂ h₃ h₄
  change P v (g⁻¹ * x) = a (g⁻¹ * x) * v (g⁻¹ * x) at h₄
  rw [h₁, h₂, h₃, h₄, hab]
  ring

/-- Multiplication operators commute even when their supplied representatives differ on null sets. -/
private theorem weighted_multipliers_commute (hν : ν ≪ μ) (P Q : W →L[ℂ] W) (p q : G → ℂ)
    (hP : ∀ v, (P v : G → ℂ) =ᵐ[μ] fun x ↦ p x * v x)
    (hQ : ∀ v, (Q v : G → ℂ) =ᵐ[μ] fun x ↦ q x * v x) (v : W) : P (Q v) = Q (P v) := by
  apply Lp.ext
  apply hν.ae_eq
  filter_upwards [hP (Q v), hQ (P v), hQ v, hP v] with x h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄]
  ring
end
end
section

/-- A compactly supported continuous test times a character and a logarithmic exponential
has an entire transform in the exponent. Only continuity and boundedness of the logarithm
on the support are needed. -/
private theorem compact_exponential_integral_entire {X : Type*} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    (f L : X → ℂ) (hf : Continuous f) (hfK : HasCompactSupport f) (hL : Continuous L) :
    Differentiable ℂ (fun z : ℂ ↦ ∫ x, f x * Complex.exp (z * L x) ∂μ) := by
  let G (z : ℂ) (x : X) := f x * Complex.exp (z * L x)
  have hd (z x) : HasDerivAt (fun w ↦ G w x) (f x * (Complex.exp (z * L x) * L x)) z := by
    simpa [G] using (((hasDerivAt_id z).mul_const (L x)).cexp.const_mul (f x))
  have hg (z) : (∫ x in tsupport f, G z x ∂μ) = ∫ x, G z x ∂μ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    simp [G, image_eq_zero_of_notMem_tsupport hx]
  intro z
  change DifferentiableAt ℂ (fun w ↦ ∫ x, G w x ∂μ) z
  simp_rw [← hg]
  apply (hasFDerivAt_integral_of_continuousOn_fderiv (𝕜 := ℂ) (F := G) (u := univ)
    (x₀ := z) univ_mem hfK.isCompact (isClosed_tsupport f).measurableSet
    hfK.isCompact.measure_lt_top.ne subset_rfl ?_ ?_ ?_).differentiableAt
  · apply Continuous.continuousOn
    exact (hf.comp continuous_snd).mul (Complex.continuous_exp.comp
      (continuous_fst.mul (hL.comp continuous_snd)))
  · exact fun x _ w _ ↦ (hd w x).differentiableAt.differentiableWithinAt
  · simp_rw [(hd _ _).hasFDerivAt.fderiv]
    apply Continuous.continuousOn
    have hd' : Continuous (fun p : ℂ × X ↦ f p.2 * (Complex.exp (p.1 * L p.2) * L p.2)) :=
      (hf.comp continuous_snd).mul ((Complex.continuous_exp.comp
        (continuous_fst.mul (hL.comp continuous_snd))).mul (hL.comp continuous_snd))
    exact (ContinuousLinearMap.toSpanSingletonLIE ℂ ℂ).continuous.comp hd'

/-- In a logarithmic Fourier chart a nonzero real-analytic multiplier is nonzero
almost everywhere, even when it has isolated real zeros. -/
private theorem logarithmic_multiplier_dichotomy (b : ℝ → ℂ) (hb : AnalyticOnNhd ℝ b univ)
    (μ : Measure ℝ) [NullSingletonClass μ] : (∀ x, b x = 0) ∨ ∀ᵐ x ∂μ, b x ≠ 0 := by
  rcases hb.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_univ with h | h
  · exact Or.inl fun x ↦ h (mem_univ x)
  · right
    have hc : ∀ᵐ x ∂μ.restrict univ, b x ≠ 0 := ae_restrict_le_codiscreteWithin (μ := μ) (U := (univ : Set ℝ)) MeasurableSet.univ h
    simpa only [Measure.restrict_univ] using hc

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*}

/-- If a Fourier model diagonalizes convolution by componentwise analytic scalar symbols,
then any self-adjoint mask that preserves the individual character components preserves
the closed convolution range. -/
private theorem closed_range_of_character_decomposition
    (C P : H →L[ℂ] H) (hP : P.adjoint = P)
    (U : H ≃ₗᵢ[ℂ] lp (fun _ : ι ↦ Lp ℂ 2 (volume : Measure ℝ)) 2)
    (b : ι → ℝ → ℂ) (hb : ∀ i, AnalyticOnNhd ℝ (b i) univ)
    (hd : ∀ v i, ((U (C.adjoint v)) i : ℝ → ℂ) =ᵐ[volume] fun t ↦
      (starRingEnd ℂ) (b i t) * U v i t)
    (hcomp : ∀ v i, U v i = 0 → U (P v) i = 0) :
    ∀ v ∈ closure (range C), P v ∈ closure (range C) := by
  have hker (v : H) (hv : C.adjoint v = 0) : C.adjoint (P v) = 0 := by
    apply U.injective
    rw [map_zero]
    apply lp.ext
    funext i
    change U (C.adjoint (P v)) i = 0
    rcases logarithmic_multiplier_dichotomy (b i) (hb i) volume with hin | hact
    · apply Lp.ext
      filter_upwards [hd (P v) i, Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with x hx hz
      simpa only [hin x, map_zero, zero_mul, hz, Pi.zero_apply] using hx
    · have hv' : U v i = 0 := by
        apply Lp.ext
        filter_upwards [hd v i, hact, Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with x hx hxi hz
        rw [hv, map_zero] at hx
        change (0 : Lp ℂ 2 (volume : Measure ℝ)) x = (starRingEnd ℂ) (b i x) * U v i x at hx
        rw [hz] at hx
        have hb' : (starRingEnd ℂ) (b i x) ≠ 0 := (map_ne_zero _).mpr hxi
        simpa only [hz, Pi.zero_apply] using (mul_eq_zero.mp hx.symm).resolve_left hb'
      apply Lp.ext
      filter_upwards [hd (P v) i, Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with x hx hz
      simpa only [hcomp v i hv', hz, Pi.zero_apply, mul_zero] using hx
  intro v hv
  have hV : C.range.topologicalClosure = C.adjoint.kerᗮ := by
    simpa using C.adjoint.orthogonal_ker.symm
  change v ∈ C.range.topologicalClosure at hv
  change P v ∈ C.range.topologicalClosure
  rw [hV] at hv ⊢
  intro u hu
  have hPu : P u ∈ C.adjoint.ker := hker u hu
  have h := hv (P u) hPu
  rw [← hP, ContinuousLinearMap.adjoint_inner_right]
  exact h
end

end
end CutoffWindow

namespace CutoffWindowBridge
section
variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
variable (m : G →ₜ* ℝ≥0ˣ) (μ : Measure G) [μ.IsHaarMeasure] (ν : Measure G)
local notation "W" => Lp ℂ 2 ν
local notation "Op" => W →L[ℂ] W
local notation "WU" => W ≃ₗᵢ[ℂ] W
local notation "logN" => (fun g : G ↦ Real.log ((m g).val : ℝ))
local notation "CL(" U ")" => (U).toContinuousLinearEquiv.toContinuousLinearMap
local notation "shift(" j ", " g ")" => (if (j : Bool) then g else (g)⁻¹)
local notation "signed(" j ", " x ")" => (if (j : Bool) then (x : ℝ) else (-x : ℝ))
local notation "centred(" d ", " x ")" => ((if |logN x| ≤ d then 1 else 0 : ℝ) : ℂ)
local notation "Com(" A ", " T ")" => ((⟨(A) * (T).val, mul_mem_nuclearEndomorphisms_left (A) (T)⟩ :
  nuclearEndomorphisms W) - (⟨(T).val * (A), mul_mem_nuclearEndomorphisms_right (A) (T)⟩ : nuclearEndomorphisms W))

/-- Combine the scalar cutoff limits, exact kernel localization, fixed-window convergence,
and radial Fourier range invariance on weighted Haar L². -/
private theorem commutator_approx (hproper : IsProperMap m) (hsur : Surjective m)
    (hμ : μ ≪ ν) (hν : ν ≪ μ) (A : Op) (u : ℝ → G) (hu : ∀ᶠ R in atTop, ((m (u R)).val : ℝ) = R)
    (T : G → WU) (w : G → G → ℂ)
    (ht : ∀ g v, (T g v : G → ℂ) =ᵐ[μ] fun x ↦ w g x * v (g⁻¹ * x))
    (hTw : ∀ v (f : StrongDual ℂ W), Tendsto (fun g ↦ f ((T g).symm v)) (cocompact G) (𝓝 0))
    (ε : ℝ → ℝ) (ρ : ℝ → G → ℝ) (hcut : ∀ᶠ R in atTop, IsModulatedCutoff m R (ε R) (ρ R))
    (hl : ∃ d : ℝ, 0 < d ∧ ∀ᶠ R in atTop, ∃ P Q : Op,
      (∀ v, (P v : G → ℂ) =ᵐ[μ] fun x ↦ if |logN x - Real.log R| ≤ d then v x else 0) ∧
      (∀ v, (Q v : G → ℂ) =ᵐ[μ] fun x ↦ if |logN x + Real.log R| ≤ d then v x else 0) ∧
      ∀ {δ : ℝ} {r : G → ℝ} (hc : IsModulatedCutoff m R δ r),
        let M : Op := modulatedCutoffOperator m ν hc
        let D := M * A - A * M
        D = P * D * P + Q * D * Q)
    (hwindow : ∀ d : ℝ, 0 < d → ∀ (S : Op), (∀ v, (S v : G → ℂ) =ᵐ[μ] fun x ↦ centred(d, x) * v x) →
      ∀ j : Bool, ∃ (C : Op) (J : nuclearEndomorphisms W) (K : ℝ → nuclearEndomorphisms W),
        (∀ (I : Set ℝ) [DecidablePred (· ∈ I)], MeasurableSet I → OrdConnected I →
          ∀ (P : Op), (∀ v, (P v : G → ℂ) =ᵐ[μ] fun x ↦ ((if logN x ∈ I then 1 else 0 : ℝ) : ℂ) * v x) →
            ∀ v ∈ closure (range C), P v ∈ closure (range C)) ∧
        (∀ v, Tendsto (fun R ↦ (T (shift(j, u R))).symm (A (T (shift(j, u R)) v))) atTop (𝓝 (C v))) ∧
        J.val = S * C * S ∧
        (∀ᶠ R in atTop, (K R).val = S *
          (CL((T (shift(j, u R))).symm) * A * CL(T (shift(j, u R)))) * S) ∧
        Tendsto (fun R ↦ traceNorm (K R - J)) atTop (𝓝 0))
    (η : ℝ) (hη : 0 < η) :
    ∃ (k : ℝ) (B : ℝ → Op), (∀ R, ‖B R‖ ≤ k) ∧
      (∀ v (f : StrongDual ℂ W), Tendsto (fun R ↦ f (B R v)) atTop (𝓝 0)) ∧
      ∀ᶠ R in atTop, ∀ hc : IsModulatedCutoff m R (ε R) (ρ R),
        let M : Op := modulatedCutoffOperator m ν hc
        ∃ E : nuclearEndomorphisms W, M * A - A * M = A * B R + E.val ∧ traceNorm E < η := by
  classical
  have hlog : Continuous (logN : G → ℝ) :=
    (NNReal.continuous_coe.comp (Units.continuous_val.comp (m).continuous)).log fun x ↦
      NNReal.coe_ne_zero.mpr (m x).ne_zero
  let U (j : Bool) (R : ℝ) : WU := T (shift(j, u R))
  have hU (j : Bool) (v : W) (f : StrongDual ℂ W) :
      Tendsto (fun R ↦ f ((U j R).symm v)) atTop (𝓝 0) := by
    have hu' := CutoffWindow.norm_section_escapes m hu
    cases j
    · exact (hTw v f).comp ((Homeomorph.inv G).isClosedEmbedding.tendsto_cocompact.comp hu')
    · exact (hTw v f).comp hu'
  obtain ⟨d, hd, hloc⟩ := hl
  let z (x : G) : ℝ := if |logN x| ≤ d then 1 else 0
  have hzm : Measurable z := Measurable.ite (measurableSet_le hlog.abs.measurable measurable_const)
    measurable_const measurable_const
  have hzb (x) : |z x| ≤ 1 := by dsimp only [z]; split <;> norm_num
  let S : Op := lpCutoffMultiplier ν z hzm hzb
  have hS (v : W) : (S v : G → ℂ) =ᵐ[μ] fun x ↦ centred(d, x) * v x :=
    hμ.ae_eq (lpCutoffMultiplier_apply ν z hzm hzb v)
  choose C J K hC hA hJ hK hKlim using hwindow d hd S hS
  choose B H hBn hHn hBa hHa hBH hB hH using fun j : Bool ↦
    CutoffWindow.translated_cutoff_strong m μ hproper hsur ν hν hcut hu j
  let D (j : Bool) (R : ℝ) := Com(B j R, K j R)
  let D₀ (j : Bool) := Com(H j, J j)
  have hD (j : Bool) : Tendsto (fun R ↦ traceNorm (D j R - D₀ j)) atTop (𝓝 0) :=
    CutoffWindow.cutoff_commutator_trace_limit (B j) (H j) (hBn j) (hHn j) (hBa j) (hHa j)
      (hBH j) (K j) (J j) (hKlim j)
  have hRange (j : Bool) (v : W) : (D₀ j).val v ∈ closure (range (C j)) := by
    change (H j * (J j).val - (J j).val * H j) v ∈ _
    rw [hJ j]
    apply CutoffWindow.localized_commutator_range
    · apply hC j
        (Icc (-d) d) measurableSet_Icc ordConnected_Icc S
      intro y
      simpa only [mem_Icc, abs_le] using hS y
    · have hpos (x : G) : 0 < ((m x).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
      cases j
      · apply hC false
          (Ioi 0) measurableSet_Ioi ordConnected_Ioi (H false)
        intro y
        simpa only [Bool.false_eq_true, ite_false, mem_Ioi, Real.log_pos_iff (hpos _).le]
          using hμ.ae_eq (hH false y)
      · apply hC true
          (Iio 0) measurableSet_Iio ordConnected_Iio (H true)
        intro y
        simpa only [ite_true, mem_Iio, Real.log_neg_iff (hpos _)] using hμ.ae_eq (hH true y)
  apply CutoffWindow.cutoff_commutator_of_two_windows A
    (fun R ↦ IsModulatedCutoff m R (ε R) (ρ R))
    (fun R hc ↦ (modulatedCutoffOperator m ν hc : Op)) U hU C hA D D₀ hD hRange _ hη
  filter_upwards [hloc, hu, hK true, hK false] with R hlocR huR hk₁ hk₂
  intro hc
  obtain ⟨V₁, V₂, hv₁, hv₂, hdec⟩ := hlocR
  let V (j : Bool) : Op := if j then V₁ else V₂
  let M : Op := modulatedCutoffOperator m ν hc
  have hM (v : W) := hμ.ae_eq (modulatedCutoffOperator_apply m ν hc v)
  let band (j : Bool) (x : G) : ℂ := (if |logN x - signed(j, Real.log R)| ≤ d then 1 else 0 : ℝ)
  have hV (j) (v : W) : (V j v : G → ℂ) =ᵐ[μ] fun x ↦ band j x * v x := by
    cases j
    · refine (hv₂ v).mono fun x hx ↦ hx.trans ?_
      simp only [band, Bool.false_eq_true, ite_false, sub_neg_eq_add]
      split <;> simp
    · refine (hv₁ v).mono fun x hx ↦ hx.trans ?_
      simp only [band, ite_true]
      split <;> simp
  have hmove (j : Bool) : CL(U j R) * (D j R).val * CL((U j R).symm) = V j * (M * A - A * M) * V j := by
    let g := shift(j, u R)
    have hgpos (x : G) : (((m x).val : ℝ) ≠ 0) := NNReal.coe_ne_zero.mpr (m x).ne_zero
    have hg : logN g = signed(j, Real.log R) := by
      cases j
      · change Real.log ((m (u R)⁻¹).val : ℝ) = -Real.log R
        rw [map_inv, Units.val_inv_eq_inv_val, NNReal.coe_inv, Real.log_inv, huR]
      · exact congrArg Real.log huR
    have hcoord (x : G) : logN (g⁻¹ * x) = logN x - signed(j, Real.log R) := by
      rw [← hg]
      change Real.log ((m (g⁻¹ * x)).val : ℝ) = _
      rw [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, NNReal.coe_mul, NNReal.coe_inv,
        Real.log_mul (inv_ne_zero (hgpos g)) (hgpos x), Real.log_inv]
      change -logN g + logN x = logN x - logN g
      ring
    have hs' (v : W) : U j R (S v) = V j (U j R v) := by
      refine CutoffWindow.weighted_multiplier_intertwines μ ν hν g _ _ (T g) _
        (ht g) S (V j) hS (hV j) (fun x ↦ ?_) v
      simp only [band, hcoord]
    have hb' (v : W) : (B j R v : G → ℂ) =ᵐ[μ] fun x ↦ (ρ R (g * x) : ℂ) * v x :=
      hμ.ae_eq (hB j R hc v)
    have hq' (v : W) : U j R (B j R v) = M (U j R v) := by
      refine CutoffWindow.weighted_multiplier_intertwines μ ν hν g _ _ (T g) _
        (ht g) (B j R) M hb' hM (fun x ↦ ?_) v
      rw [mul_inv_cancel_left]
    have hsq := CutoffWindow.weighted_multipliers_commute μ ν hν S (B j R) _ _ hS hb'
    have hk : (K j R).val = S * (CL((U j R).symm) * A * CL(U j R)) * S :=
      by cases j <;> assumption
    change CL(U j R) * (B j R * (K j R).val - (K j R).val * B j R) * CL((U j R).symm) = _
    rw [hk]
    exact CutoffWindow.move_compressed_commutator (U j R) A S (V j) (B j R) M hs' hq' hsq
  rw [hmove true, hmove false]
  exact hdec hc

end
end CutoffWindowBridge

end

section CutoffConvolutionLimits
open scoped ENNReal Pointwise TensorProduct ComplexInnerProductSpace


section
namespace CutoffDensity

/-- The density of a symmetric interval is an exponential in the absolute displacement times the
Sobolev polynomial. -/
private theorem density_abs (α s x : ℝ) (hα : 0 ≤ α) :
    intervalSobolevDensity (-α) α s x =
      Real.exp (2 * α * |x|) * (1 + x ^ 2) ^ (s / 2) := by
  unfold intervalSobolevDensity
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx, max_eq_right]
    exact Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hα hx])
  · have hx' : x ≤ 0 := le_of_not_ge hx
    rw [abs_of_nonpos hx', max_eq_left (Real.exp_le_exp.mpr (by nlinarith [mul_nonpos_of_nonneg_of_nonpos hα hx']))]
    ring_nf

/-- The shifted Sobolev polynomial ratio tends to one uniformly on a bounded interval. -/
private theorem ratio_error {t x L : ℝ} (ht : 0 < t) (hx : |x| ≤ L) (hL : L ≤ t) :
    |(1 + (t + x) ^ 2) / (1 + t ^ 2) - 1| ≤ 3 * L / t := by
  have hLn : 0 ≤ L := (abs_nonneg _).trans hx
  have hd : 0 < 1 + t ^ 2 := by positivity
  have heq : (1 + (t + x) ^ 2) / (1 + t ^ 2) - 1 = (2 * t * x + x * x) / (1 + t ^ 2) := by
    field_simp
    ring
  have hn : |2 * t * x + x * x| ≤ 3 * L * t := by
    calc
      _ ≤ |2 * t * x| + |x * x| := abs_add_le _ _
      _ = 2 * t * |x| + |x| * |x| := by simp [abs_mul, abs_of_pos ht]
      _ ≤ 2 * t * L + t * L := by
        exact add_le_add (mul_le_mul_of_nonneg_left hx (by positivity))
          (mul_le_mul (hx.trans hL) hx (abs_nonneg _) ht.le)
      _ = 3 * L * t := by ring
  rw [heq, abs_div, abs_of_pos hd, div_le_div_iff₀ hd ht]
  calc
    _ ≤ (3 * L * t) * t := mul_le_mul_of_nonneg_right hn ht.le
    _ = 3 * L * t ^ 2 := by ring
    _ ≤ 3 * L * (1 + t ^ 2) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- Past a positive endpoint the exponential factor separates from the polynomial ratio. -/
private theorem density_ratio {α s t x : ℝ} (hα : 0 ≤ α) (ht : 0 ≤ t) (hx : |x| ≤ t) :
    intervalSobolevDensity (-α) α s (t + x) / intervalSobolevDensity (-α) α s t =
      Real.exp (2 * α * x) * ((1 + (t + x) ^ 2) / (1 + t ^ 2)) ^ (s / 2) := by
  have htx : 0 ≤ t + x := by linarith [(abs_le.mp hx).1]
  rw [density_abs _ _ _ hα, density_abs _ _ _ hα, abs_of_nonneg ht, abs_of_nonneg htx,
    Real.div_rpow (by positivity) (by positivity),
    show 2 * α * (t + x) = 2 * α * t + 2 * α * x by ring, Real.exp_add]
  field_simp [ne_of_gt (Real.exp_pos _), ne_of_gt (Real.rpow_pos_of_pos (show 0 < 1 + t ^ 2 by positivity) (s / 2))]

/-- For any bounded displacement, the density ratio at the positive endpoint divided by its
limiting exponential tends to one. Reflecting the displacement gives the negative endpoint. -/
private theorem density_edge_limit (α s : ℝ) (hα : 0 ≤ α) (L : ℝ) (x : ℝ → ℝ) (hx : ∀ t, |x t| ≤ L) :
    Tendsto (fun t ↦ intervalSobolevDensity (-α) α s (t + x t) /
      intervalSobolevDensity (-α) α s t / Real.exp (2 * α * x t)) atTop (𝓝 1) := by
  have hpoly : Tendsto (fun t ↦ (1 + (t + x t) ^ 2) / (1 + t ^ 2)) atTop (𝓝 1) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) _ (g := fun t ↦ 3 * L / t)
      (tendsto_const_nhds.div_atTop tendsto_id)
    filter_upwards [eventually_ge_atTop L, eventually_gt_atTop (0 : ℝ)] with t hL ht
    exact ratio_error ht (hx t) hL
  have h := hpoly.rpow_const (p := s / 2) (Or.inl one_ne_zero)
  rw [Real.one_rpow] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop L, eventually_ge_atTop (0 : ℝ)] with t hL ht
  rw [density_ratio hα ht ((hx t).trans hL), mul_div_cancel_left₀ _ (Real.exp_ne_zero _)]

/-- The weight on a symmetric strip is even. -/
private theorem density_even (α s x : ℝ) (hα : 0 ≤ α) :
    intervalSobolevDensity (-α) α s (-x) = intervalSobolevDensity (-α) α s x := by
  rw [density_abs _ _ _ hα, density_abs _ _ _ hα, abs_neg, neg_sq]

/-- Evenness gives the normalized density limit at the negative endpoint. -/
private theorem density_negative_edge_limit (α s : ℝ) (hα : 0 ≤ α) (L : ℝ) (x : ℝ → ℝ)
    (hx : ∀ t, |x t| ≤ L) :
    Tendsto (fun t ↦ intervalSobolevDensity (-α) α s (-t + x t) /
      intervalSobolevDensity (-α) α s (-t) / Real.exp (-(2 * α * x t))) atTop (𝓝 1) := by
  have h := density_edge_limit α s hα L (fun t ↦ -x t) (fun t ↦ (abs_neg (x t)).trans_le (hx t))
  apply h.congr
  intro t
  rw [show -t + x t = -(t + -x t) by ring, density_even _ _ _ hα, density_even _ _ _ hα, mul_neg]

/-- A scalar estimate uniform over every bounded family of displacements is uniform on the interval. -/
private theorem uniform_of_bounded_displacements (F : ℝ → ℝ → ℝ) (d : ℝ) (hd : 0 ≤ d)
    (h : ∀ x : ℝ → ℝ, (∀ t, |x t| ≤ d) → Tendsto (fun t ↦ F t (x t)) atTop (𝓝 1)) :
    ∀ ε > 0, ∀ᶠ t in atTop, ∀ y : ℝ, |y| ≤ d → |F t y - 1| < ε := by
  classical
  intro ε hε
  let x (t : ℝ) := if H : ∃ y : ℝ, |y| ≤ d ∧ ε ≤ |F t y - 1| then H.choose else 0
  have hx (t : ℝ) : |x t| ≤ d := by
    by_cases H : ∃ y : ℝ, |y| ≤ d ∧ ε ≤ |F t y - 1|
    · simpa only [x, dite_eq_left H] using H.choose_spec.1
    · simpa only [x, dite_eq_right H, abs_zero] using hd
  filter_upwards [Metric.tendsto_nhds.mp (h x hx) ε hε] with t ht y hy
  by_contra! hbad
  have H : ∃ y : ℝ, |y| ≤ d ∧ ε ≤ |F t y - 1| := ⟨y, hy, hbad⟩
  have hz : ε ≤ |F t (x t) - 1| := by simpa only [x, dite_eq_left H] using H.choose_spec.2
  exact (not_lt_of_ge hz) (by simpa only [Real.dist_eq] using ht)

/-- On a bounded logarithmic window the square root and the reciprocal square root of
the normalized density error both converge uniformly to one, at either end. -/
private theorem uniform_sqrt_density_edge (α s d : ℝ) (hα : 0 ≤ α) (hd : 0 ≤ d) (j : Bool) :
    let w := intervalSobolevDensity (-α) α s
    let σ (x : ℝ) := if j then x else -x
    let E (t x : ℝ) := Real.sqrt ((w (σ t + x) / w (σ t)) / Real.exp (σ (2 * α * x)))
    ∀ ε > 0, ∀ᶠ t in atTop, ∀ x : ℝ, |x| ≤ d →
      |E t x - 1| < ε ∧ |(E t x)⁻¹ - 1| < ε := by
  intro w σ E
  have h (x : ℝ → ℝ) (hx : ∀ t, |x t| ≤ d) :
      Tendsto (fun t ↦ E t (x t)) atTop (𝓝 1) := by
    have hr : Tendsto (fun t ↦ (w (σ t + x t) / w (σ t)) / Real.exp (σ (2 * α * x t)))
        atTop (𝓝 1) := by
      cases j
      · simpa only [σ, w, Bool.false_eq_true, ite_false] using density_negative_edge_limit α s hα d x hx
      · simpa only [σ, w, ite_true] using density_edge_limit α s hα d x hx
    simpa only [Function.comp_def, Real.sqrt_one, E] using (Real.continuous_sqrt.tendsto 1).comp hr
  have hi (x : ℝ → ℝ) (hx : ∀ t, |x t| ≤ d) : Tendsto (fun t ↦ (E t (x t))⁻¹) atTop (𝓝 1) := by
    simpa only [inv_one] using (h x hx).inv₀ one_ne_zero
  intro ε hε
  filter_upwards [uniform_of_bounded_displacements E d hd h ε hε,
    uniform_of_bounded_displacements (fun t x ↦ (E t x)⁻¹) d hd hi ε hε] with t ht ht' x hx
  exact ⟨ht x hx, ht' x hx⟩

/-- A continuous scalar factor on a compact interval can be restored in a uniform ratio estimate. -/
private theorem uniform_restore_factor (d : ℝ) (f : ℝ → ℝ) (hf : Continuous f)
    (E : ℝ → ℝ → ℝ) (hE : ∀ ε > 0, ∀ᶠ t in atTop, ∀ x : ℝ, |x| ≤ d → |E t x - 1| < ε) :
    ∀ ε > 0, ∀ᶠ t in atTop, ∀ x : ℝ, |x| ≤ d → |E t x * f x - f x| < ε := by
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := -d) (b := d)).bddAbove_image hf.abs.continuousOn
  let M := |B| + 1
  have hM : 0 < M := by dsimp only [M]; positivity
  intro ε hε
  filter_upwards [hE (ε / M) (div_pos hε hM)] with t ht x hx
  have hbx : |f x| ≤ M := (hB (Set.mem_image_of_mem (fun x ↦ |f x|) (abs_le.mp hx))).trans
    (by dsimp only [M]; linarith [le_abs_self B])
  rw [← sub_one_mul, abs_mul]
  calc
    |E t x - 1| * |f x| ≤ |E t x - 1| * M := mul_le_mul_of_nonneg_left hbx (abs_nonneg _)
    _ < ε := (lt_div_iff₀ hM).mp (ht x hx)

/-- The actual input and output multiplication symbols converge uniformly on each central
logarithmic window, including their limiting exponential factors. -/
private theorem uniform_sobolev_edge_multipliers (α s d : ℝ) (hα : 0 ≤ α) (hd : 0 ≤ d) (j : Bool) :
    let w := intervalSobolevDensity (-α) α s
    let σ (x : ℝ) := if j then x else -x
    let q (t x : ℝ) := (Real.sqrt (w (σ t + x)) / Real.sqrt (w x)) / Real.sqrt (w (σ t))
    let q₀ (x : ℝ) := Real.exp (σ (α * x)) / Real.sqrt (w x)
    ∀ ε > 0, ∀ᶠ t in atTop, ∀ x : ℝ, |x| ≤ d →
      |q t x - q₀ x| < ε ∧ |(q t x)⁻¹ - (q₀ x)⁻¹| < ε := by
  intro w σ q q₀
  have hw : Continuous w := by
    exact continuous_intervalSobolevDensity (-α) α s
  have hp (x : ℝ) : 0 < w x := by
    dsimp only [w, intervalSobolevDensity]
    exact mul_pos (lt_max_of_lt_left (Real.exp_pos _)) (Real.rpow_pos_of_pos (by positivity) _)
  have hdp (x : ℝ) := Real.sqrt_pos.mpr (hp x)
  have hσ : Continuous σ := by cases j <;> dsimp [σ] <;> fun_prop
  have hc : Continuous q₀ := (Real.continuous_exp.comp (hσ.comp (continuous_const.mul continuous_id))).div
    (Real.continuous_sqrt.comp hw) (fun x ↦ (hdp x).ne')
  have hq (x : ℝ) : 0 < q₀ x := div_pos (Real.exp_pos _) (hdp x)
  let E (t x : ℝ) := Real.sqrt ((w (σ t + x) / w (σ t)) / Real.exp (σ (2 * α * x)))
  have hE := uniform_sqrt_density_edge α s d hα hd j
  have heq (t x : ℝ) : E t x * q₀ x = q t x := by
    have he : σ (2 * α * x) / 2 = σ (α * x) := by cases j <;> dsimp [σ] <;> ring
    dsimp only [E, q₀, q]
    rw [Real.sqrt_div (div_pos (hp _) (hp _)).le, Real.sqrt_div (hp _).le, ← Real.exp_half, he]
    field_simp [(Real.exp_pos _).ne', (hdp _).ne']
  have h₁ := uniform_restore_factor d q₀ hc E fun ε hε ↦ (hE ε hε).mono fun t ht x hx ↦ (ht x hx).1
  have h₂ := uniform_restore_factor d (fun x ↦ (q₀ x)⁻¹) (hc.inv₀ fun x ↦ (hq x).ne')
    (fun t x ↦ (E t x)⁻¹) fun ε hε ↦ (hE ε hε).mono fun t ht x hx ↦ (ht x hx).2
  intro ε hε
  filter_upwards [h₁ ε hε, h₂ ε hε] with t ht ht' x hx
  refine ⟨heq t x ▸ ht x hx, ?_⟩
  simpa only [← mul_inv, heq] using ht' x hx

end CutoffDensity

end

section
namespace CutoffLarge
variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (m : G →ₜ* ℝ≥0ˣ)

/-- Arbitrarily large logarithmic plateaux exist for every positive module. -/
private theorem exists_modulatedCutoff_large {R ε : ℝ} (hR : 2 ≤ R) (hε : 0 < ε) (he : ε < R⁻¹) :
    ∃ ρ : G → ℝ, IsModulatedCutoff m R ε ρ ∧ 0 < R⁻¹ + ε ∧ R⁻¹ + ε < R - ε := by
  have hpos : 0 < R := by linarith
  have hi : R⁻¹ ≤ (2 : ℝ)⁻¹ := (inv_le_inv₀ hpos (by norm_num)).mpr hR
  norm_num at hi
  have hband : R⁻¹ + ε < R - ε := by linarith
  have hlarge : 1 < R - ε := by linarith
  have hcomp : (R - ε)⁻¹ ≤ R⁻¹ + ε := by
    rw [inv_eq_one_div, div_le_iff₀ (by linarith)]
    nlinarith [mul_nonneg hε.le (by linarith : 0 ≤ R - R⁻¹ - ε), inv_mul_cancel₀ hpos.ne']
  let B : ContDiffBump (0 : ℝ) :=
    ⟨Real.log (R - ε), Real.log R, Real.log_pos hlarge,
      Real.log_lt_log (by linarith) (sub_lt_self _ hε)⟩
  let r (x : G) : ℝ := (m x).val
  have hr : Continuous r := NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)
  have hrpos (x : G) : 0 < r x := NNReal.coe_pos.mpr (Units.zero_lt _)
  let ρ (x : G) := B (Real.log (r x))
  have h1 : ρ 1 = 1 := by
    apply B.one_of_mem_closedBall
    simp [r, B.rIn_pos.le]
  refine ⟨ρ, ⟨hpos, hε, sub_pos.mpr he, by linarith, fun _ ↦ B.nonneg,
    fun x ↦ (abs_of_nonneg (B.nonneg (x := Real.log (r x)))) ▸ B.le_one, ?_, ?_, ?_, ?_, ?_⟩,
    add_pos (inv_pos.mpr hpos) hε, hband⟩
  · exact IsGreatest.csSup_eq ⟨⟨1, h1⟩, forall_mem_range.mpr fun _ ↦ B.le_one⟩
  · refine ⟨fun t ↦ B (Real.log t), ∅, fun _ ↦ rfl, by simp, ?_, by simp⟩
    simp only [Finset.coe_empty, sdiff_empty]
    exact B.contDiff.comp_contDiffOn (fun x hx ↦ (Real.contDiffAt_log.mpr (mem_Ioi.mp hx).ne').contDiffWithinAt)
  · intro x
    change B (Real.log ((m x).val : ℝ)) = B (Real.log ((m x⁻¹).val : ℝ))
    rw [map_inv, Units.val_inv_eq_inv_val, NNReal.coe_inv, Real.log_inv, B.neg]
  · apply closure_minimal _ (isClosed_Icc.preimage hr)
    intro x hx
    have hmem : Real.log (r x) ∈ support B := hx
    rw [B.support_eq, Metric.mem_ball, Real.dist_eq, sub_zero] at hmem
    obtain ⟨hl, hu⟩ := abs_lt.mp hmem
    change R⁻¹ ≤ r x ∧ r x ≤ R
    rw [← Real.log_le_log_iff (inv_pos.mpr hpos) (hrpos x), Real.log_inv,
      ← Real.log_le_log_iff (hrpos x) hpos]
    exact ⟨hl.le, hu.le⟩
  · intro x hx
    apply B.one_of_mem_closedBall
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le]
    change -Real.log (R - ε) ≤ _ ∧ _ ≤ Real.log (R - ε)
    rw [← Real.log_inv, Real.log_le_log_iff (inv_pos.mpr (by linarith)) (hrpos x),
      Real.log_le_log_iff (hrpos x) (by linarith)]
    exact ⟨hcomp.trans hx.1, hx.2⟩

/-- In particular one may choose a cofinal admissible family for the fixed-window nuclearity theorem. -/
private theorem exists_cofinal_cutoff :
    ∃ (ε : ℝ → ℝ) (ρ : ℝ → G → ℝ), ∀ᶠ R in atTop,
      IsModulatedCutoff m R (ε R) (ρ R) ∧ 0 < R⁻¹ + ε R ∧ R⁻¹ + ε R < R - ε R := by
  classical
  let ε (R : ℝ) := R⁻¹ / 2
  have he (R : ℝ) (h : 2 ≤ R) := exists_modulatedCutoff_large m (ε := ε R) h
    (by dsimp only [ε]; positivity) (by dsimp only [ε]; exact half_lt_self (inv_pos.mpr (by linarith)))
  let ρ (R : ℝ) := if h : 2 ≤ R then (he R h).choose else 0
  refine ⟨ε, ρ, ?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with R hR
  simpa only [ρ, dite_eq_left hR] using (he R hR).choose_spec

end CutoffLarge

end

section
namespace CutoffConjugated
variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
variable (μ : Measure G) [μ.IsHaarMeasure] (ν : Measure G)
local notation "W" => Lp ℂ 2 ν
local notation "Op" => W →L[ℂ] W

/-- Conjugating convolution by a density-normalized shift gives an output weight and the
reciprocal input weight. The normalization of these two weights cancels. -/
private theorem conjugated_convolution_rep (φ d : G → ℂ) (hd : ∀ x, d x ≠ 0) (A : Op)
    (hA : ∀ v : W, ∀ᵐ x ∂μ, A v x = ∫ g, φ g * v (g⁻¹ * x) ∂μ)
    (h : G) (U : W ≃ₗᵢ[ℂ] W)
    (hU : ∀ v, (U v : G → ℂ) =ᵐ[μ] fun x ↦ d (h⁻¹ * x) / d x * v (h⁻¹ * x))
    (c : ℂ) (hc : c ≠ 0) (v : W) :
    let q (x : G) := (d (h * x) / d x) / c
    ∀ᵐ x ∂μ, U.symm (A (U v)) x = q x * ∫ g, φ g * ((q (g⁻¹ * x))⁻¹ * v (g⁻¹ * x)) ∂μ := by
  intro q
  have hInv (w : W) : (U.symm w : G → ℂ) =ᵐ[μ] fun x ↦ d (h * x) / d x * w (h * x) := by
    have hrep := (measurePreserving_mul_left μ h).quasiMeasurePreserving.ae_eq_comp (hU (U.symm w))
    filter_upwards [hrep] with x hx
    change U (U.symm w) (h * x) = d (h⁻¹ * (h * x)) / d (h * x) * U.symm w (h⁻¹ * (h * x)) at hx
    rw [U.apply_symm_apply, inv_mul_cancel_left] at hx
    rw [hx]
    field_simp [hd]
  have hrep := (measurePreserving_mul_left μ h).quasiMeasurePreserving.ae_eq_comp (hA (U v))
  filter_upwards [hInv (A (U v)), hrep] with x huv hav
  change A (U v) (h * x) = ∫ g, φ g * U v (g⁻¹ * (h * x)) ∂μ at hav
  rw [huv, hav, ← integral_const_mul, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [CutoffWindow.convolution_translate_rep μ (hU v) (h * x)] with g hg
  change U v (g⁻¹ * (h * x)) = d (h⁻¹ * (g⁻¹ * (h * x))) / d (g⁻¹ * (h * x)) * v (h⁻¹ * (g⁻¹ * (h * x))) at hg
  rw [hg]
  have he : g⁻¹ * (h * x) = h * (g⁻¹ * x) := by ac_rfl
  simp only [he, inv_mul_cancel_left, q]
  field_simp [hd, hc]

/-- The pointwise kernel of a convolution bracketed by two different bounded multipliers. -/
private theorem sandwich_rep (φ : G → ℂ) (a b : G → ℂ) (A L R : Op)
    (hA : ∀ v : W, ∀ᵐ x ∂μ, A v x = ∫ g, φ g * v (g⁻¹ * x) ∂μ)
    (hL : ∀ v, (L v : G → ℂ) =ᵐ[μ] fun x ↦ a x * v x)
    (hR : ∀ v, (R v : G → ℂ) =ᵐ[μ] fun x ↦ b x * v x) (v : W) :
    ∀ᵐ x ∂μ, (L * A * R) v x = a x * ∫ g, φ g * (b (g⁻¹ * x) * v (g⁻¹ * x)) ∂μ := by
  filter_upwards [hL (A (R v)), hA (R v)] with x hl ha
  change L (A (R v)) x = _
  rw [hl, ha]
  apply congrArg (a x * ·)
  refine integral_congr_ae ?_
  filter_upwards [CutoffWindow.convolution_translate_rep μ (hR v) x] with g hg
  exact congrArg (φ g * ·) hg

/-- On a fixed sharp window every twisted kernel is a two-sided diagonal multiple
of a single fixed window compression of the untwisted convolution. -/
private theorem compress_twisted (hν : ν ≪ μ) (φ p q : G → ℂ) (hpp : ∀ x, p x * p x = p x)
    (A C P L R : Op)
    (hA : ∀ v : W, ∀ᵐ x ∂μ, A v x = ∫ g, φ g * v (g⁻¹ * x) ∂μ)
    (hC : ∀ v : W, ∀ᵐ x ∂μ, C v x = q x * ∫ g, φ g * ((q (g⁻¹ * x))⁻¹ * v (g⁻¹ * x)) ∂μ)
    (hP : ∀ v, (P v : G → ℂ) =ᵐ[μ] fun x ↦ p x * v x)
    (hL : ∀ v, (L v : G → ℂ) =ᵐ[μ] fun x ↦ (p x * q x) * v x)
    (hR : ∀ v, (R v : G → ℂ) =ᵐ[μ] fun x ↦ (p x * (q x)⁻¹) * v x) :
    P * C * P = L * (P * A * P) * R := by
  have hLP : L * P = L := by
    apply ContinuousLinearMap.ext
    intro v
    apply Lp.ext
    refine hν.ae_eq ?_
    filter_upwards [hL (P v), hP v, hL v] with x hl hp hl'
    change L (P v) x = L v x
    rw [hl, hp, hl', show (p x * q x) * (p x * v x) = (p x * p x) * (q x * v x) by ring, hpp]
    ring
  have hPR : P * R = R := by
    apply ContinuousLinearMap.ext
    intro v
    apply Lp.ext
    refine hν.ae_eq ?_
    filter_upwards [hP (R v), hR v] with x hp hr
    change P (R v) x = R v x
    rw [hp, hr, show p x * ((p x * (q x)⁻¹) * v x) = (p x * p x) * ((q x)⁻¹ * v x) by ring, hpp]
    ring
  rw [show L * (P * A * P) * R = (L * P) * A * (P * R) by noncomm_ring, hLP, hPR]
  apply ContinuousLinearMap.ext
  intro v
  apply Lp.ext
  refine hν.ae_eq ?_
  filter_upwards [hP (C (P v)), hC (P v), sandwich_rep μ ν φ _ _ A L R hA hL hR v] with x hp hc hreg
  change P (C (P v)) x = (L * A * R) v x
  rw [hp, hc, hreg, ← mul_assoc]
  apply congrArg ((p x * q x) * ·)
  refine integral_congr_ae ?_
  filter_upwards [CutoffWindow.convolution_translate_rep μ (hP v) x] with g hg
  rw [show P v (g⁻¹ * x) = _ from hg]
  ring

end CutoffConjugated

end

section
namespace CutoffTilted
variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
variable (m : G →ₜ* ℝ≥0ˣ) (μ : Measure G) [μ.IsHaarMeasure]
include m

/-- Zero-weight Chapter 9 convolution acts on ordinary Haar L². -/
private theorem exists_haar_convolution (ψ : G → ℂ) (hψ : Continuous ψ) (hK : HasCompactSupport ψ) :
    ∃ B : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ, ∀ v : Lp ℂ 2 μ,
      ∀ᵐ x ∂μ, B v x = ∫ g, ψ g * v (g⁻¹ * x) ∂μ := by
  let l (x : G) := Real.log ((m x).val : ℝ)
  let ν := μ.withDensity fun x : G ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 0 (l x))
  have he : ν = μ := by simp [ν, intervalSobolevDensity]
  suffices h : ∃ B : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν, ∀ v : Lp ℂ 2 ν,
      ∀ᵐ x ∂μ, B v x = ∫ g, ψ g * v (g⁻¹ * x) ∂μ by rwa [he] at h
  let hb := hψ.bounded_above_of_compact_support hK
  let B := hardySobolevConvolution μ m 0 0 0 le_rfl le_rfl ψ hψ.aemeasurable hK hb
  refine ⟨B, fun v ↦ ?_⟩
  exact (hardySobolevConvolution_apply μ m 0 0 0 le_rfl le_rfl ψ hψ.aemeasurable hK hb v).mono fun x hx ↦ hx.2

/-- A compactly supported Haar convolution transported by the square root of a positive
density defines a bounded operator on the original weighted space. -/
private theorem exists_unweighted_convolution_on_density (w : G → ℝ) (hw : Measurable w) (hp : ∀ x, 0 < w x)
    (ψ : G → ℂ) (hψ : Continuous ψ) (hK : HasCompactSupport ψ) :
    let ν := μ.withDensity fun x ↦ ENNReal.ofReal (w x)
    let d (x : G) : ℂ := Real.sqrt (w x)
    ∃ C : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν, ∀ v : Lp ℂ 2 ν, ∀ᵐ x ∂μ,
      C v x = (d x)⁻¹ * ∫ g, ψ g * (d (g⁻¹ * x) * v (g⁻¹ * x)) ∂μ := by
  intro ν d
  obtain ⟨J, hJ'⟩ := CutoffWindow.exists_unweight_L2 μ (fun x ↦ (w x).toNNReal) hw.real_toNNReal
    (fun x ↦ Real.toNNReal_pos.mpr (hp x))
  have hJ (v : Lp ℂ 2 ν) : (J v : G → ℂ) =ᵐ[μ] fun x ↦ d x * v x := by
    refine (hJ' v).mono fun x hx ↦ ?_
    exact hx.trans (congrArg (fun c : ℂ ↦ c * v x)
      (congrArg (fun r : ℝ ↦ (Real.sqrt r : ℂ)) (Real.coe_toNNReal _ (hp x).le)))
  obtain ⟨B, hB⟩ := exists_haar_convolution m μ ψ hψ hK
  let C : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν := J.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp (B.comp J.toContinuousLinearEquiv.toContinuousLinearMap)
  refine ⟨C, fun v ↦ ?_⟩
  have hinv := hJ (C v)
  have he : J (C v) = B (J v) := J.apply_symm_apply _
  rw [he] at hinv
  filter_upwards [hinv, hB (J v)] with x hx hb
  have hdx : d x ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hp x)).ne'
  calc
    C v x = (d x)⁻¹ * B (J v) x := (inv_mul_cancel_left₀ hdx _).symm.trans (congrArg ((d x)⁻¹ * ·) hx.symm)
    _ = _ := by
      rw [hb]
      apply congrArg ((d x)⁻¹ * ·)
      apply integral_congr_ae
      have hn : MeasurePreserving (fun g : G ↦ g⁻¹ * x) μ μ :=
        (measurePreserving_mul_right μ x).comp (Measure.measurePreserving_inv μ)
      filter_upwards [hn.quasiMeasurePreserving.ae_eq_comp (hJ v)] with g hg
      exact congrArg (ψ g * ·) hg

end CutoffTilted

end

section
namespace CutoffSandwich

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} {l : Filter ι}
local notation "Op" => H →L[ℂ] H
local notation "sandwich(" A ", " T ", " B ")" =>
  (⟨((A) * (T).val) * (B),
    mul_mem_nuclearEndomorphisms_right (B) (⟨(A) * (T).val,
      mul_mem_nuclearEndomorphisms_left (A) (T)⟩ : nuclearEndomorphisms H)⟩ : nuclearEndomorphisms H)

/-- Operator norm convergence of both multipliers gives trace norm convergence around
one fixed trace class operator. -/
private theorem traceNorm_sandwich_tendsto (T : nuclearEndomorphisms H) (L R : ι → Op) (A B : Op)
    (hL : Tendsto L l (𝓝 A)) (hR : Tendsto R l (𝓝 B)) :
    Tendsto (fun i ↦ traceNorm (sandwich(L i, T, R i) - sandwich(A, T, B))) l (𝓝 0) := by
  let : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
  let core := traceNorm_normedSpaceCore (H := H)
  have hbound (X Y : Op) : traceNorm sandwich(X, T, Y) ≤ ‖Y‖ * (‖X‖ * traceNorm T) :=
    (traceNorm_mul_right_le Y ⟨_, mul_mem_nuclearEndomorphisms_left X T⟩).trans
      (mul_le_mul_of_nonneg_left (traceNorm_mul_left_le X T) (norm_nonneg Y))
  have h (i : ι) : sandwich(L i, T, R i) - sandwich(A, T, B) =
      sandwich(L i - A, T, R i) + sandwich(A, T, R i - B) := by
    apply Subtype.ext
    simp only [Submodule.coe_sub, Submodule.coe_add, sub_mul, mul_sub]
    abel
  have hx : Tendsto (fun i ↦ ‖L i - A‖) l (𝓝 0) := by
    simpa only [sub_self, norm_zero] using (hL.sub (tendsto_const_nhds (x := A))).norm
  have hy : Tendsto (fun i ↦ ‖R i - B‖) l (𝓝 0) := by
    simpa only [sub_self, norm_zero] using (hR.sub (tendsto_const_nhds (x := B))).norm
  have hsmall : Tendsto
      (fun i ↦ ‖R i‖ * (‖L i - A‖ * traceNorm T) + ‖R i - B‖ * (‖A‖ * traceNorm T)) l (𝓝 0) := by
    simpa using (hR.norm.mul (hx.mul_const (traceNorm T))).add (hy.mul_const (‖A‖ * traceNorm T))
  refine squeeze_zero (fun i ↦ core.norm_nonneg _) (fun i ↦ ?_) hsmall
  rw [h i]
  exact (core.norm_triangle _ _).trans (add_le_add (hbound _ _) (hbound _ _))
end

section
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
local notation "W" => Lp ℂ 2 μ
variable {ι : Type*} {l : Filter ι}

/-- Uniform convergence of the scalar symbols implies convergence of the L² multipliers
in operator norm. -/
private theorem multiplier_opNorm_tendsto (F : ι → X → ℂ) (f : X → ℂ)
    (T : ι → W →L[ℂ] W) (S : W →L[ℂ] W)
    (hT : ∀ i v, (T i v : X → ℂ) =ᵐ[μ] fun x ↦ F i x * v x)
    (hS : ∀ v, (S v : X → ℂ) =ᵐ[μ] fun x ↦ f x * v x)
    (h : ∀ ε > 0, ∀ᶠ i in l, ∀ x, ‖F i x - f x‖ < ε) : Tendsto T l (𝓝 S) := by
  refine Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
  filter_upwards [h (ε/2) (half_pos hε)] with i hi
  rw [dist_eq_norm]
  refine lt_of_le_of_lt (ContinuousLinearMap.opNorm_le_bound _ (half_pos hε).le (fun v ↦ ?_)) (half_lt_self hε)
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [hT i v, hS v, Lp.coeFn_sub (T i v) (S v)] with x hx hy hxy
  change ‖(T i v - S v) x‖ ≤ ε / 2 * ‖v x‖
  rw [hxy]
  change ‖T i v x - S v x‖ ≤ _
  rw [hx, hy, ← sub_mul, norm_mul]
  exact mul_le_mul_of_nonneg_right (hi x).le (norm_nonneg _)
end

end CutoffSandwich

end

namespace CutoffFixed
section
variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (m : G →ₜ* ℝ≥0ˣ)
variable [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
variable (μ : Measure G) [μ.IsHaarMeasure]
local notation "FBlog(" x ")" => (Real.log ((m x).val : ℝ))
local notation "FBspace(" a ", " b ", " s ")" => CompactIntervalSobolev μ (fun g : G ↦ FBlog(g)) a b s
local notation "FBmeasure(" a ", " b ", " s ")" => (μ.withDensity fun x : G ↦ ENNReal.ofReal (intervalSobolevDensity a b s FBlog(x)))

/-- Each sharp bounded logarithmic compression of the actual test convolution is trace class.
One larger member of the given admissible family is identically one on the window. -/
private theorem hardySobolev_fixed_window_nuclear (a b s : ℝ) (hab : a ≤ b) (hs : 0 ≤ s)
    (hm : IsModulation m) (hms : Surjective m) (φ : BruhatCompactSupport G)
    (hφc : Continuous φ.val) (ε : ℝ → ℝ) (ρ : ℝ → G → ℝ) (hρ : ∀ᶠ R in atTop, IsModulatedCutoff m R (ε R) (ρ R) ∧
      0 < R⁻¹ + ε R ∧ R⁻¹ + ε R < R - ε R) (c d : ℝ) :
    let A : FBspace(a, b, s) →L[ℂ] FBspace(a, b, s) := hardySobolevTestAction μ m a b s hab hs φ
    ∃ P : FBspace(a, b, s) →L[ℂ] FBspace(a, b, s),
      (∀ v : FBspace(a, b, s), (P v : G → ℂ) =ᵐ[FBmeasure(a, b, s)]
        fun x ↦ if |FBlog(x) - c| ≤ d then v x else 0) ∧ IsNuclearOperator (P * A * P) := by
  intro A
  let p (x : G) : ℝ := if |FBlog(x) - c| ≤ d then 1 else 0
  have hlog : Continuous (fun x : G ↦ FBlog(x)) :=
    (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)).log
      fun x ↦ NNReal.coe_ne_zero.mpr (m x).ne_zero
  have hp : Measurable p := Measurable.ite
    (measurableSet_le ((hlog.sub continuous_const).abs).measurable measurable_const) measurable_const measurable_const
  have hb (x) : |p x| ≤ 1 := by dsimp only [p]; split <;> norm_num
  obtain ⟨P₀, _, hPmul⟩ := exists_lpCutoffMultiplier FBmeasure(a, b, s) p hp hb
  let P : FBspace(a, b, s) →L[ℂ] FBspace(a, b, s) := P₀
  have hP (v : FBspace(a, b, s)) : (P v : G → ℂ) =ᵐ[FBmeasure(a, b, s)]
      fun x ↦ if |FBlog(x) - c| ≤ d then v x else 0 := by
    refine (hPmul v).mono fun x hx ↦ hx.trans ?_
    dsimp only [p]
    split <;> simp_all only [Complex.ofReal_one, Complex.ofReal_zero, one_mul, zero_mul]
  obtain ⟨R, hc, hr, ht⟩ := (hρ.and ((eventually_ge_atTop (2 : ℝ)).and
    (Real.tendsto_log_atTop.eventually_ge_atTop (|c| + d + Real.log 2)))).exists
  let M : FBspace(a, b, s) →L[ℂ] FBspace(a, b, s) := modulatedCutoffOperator m FBmeasure(a, b, s) hc.1
  have heq : P * M = P := by
    apply ContinuousLinearMap.ext
    intro v
    apply Lp.ext
    filter_upwards [hP (M v), hP v, modulatedCutoffOperator_apply m FBmeasure(a, b, s) hc.1 v] with x h₁ h₂ h₃
    change P (M v) x = P v x
    rw [h₁, h₂]
    by_cases hx : |FBlog(x) - c| ≤ d
    · rw [ite_eq_left hx, ite_eq_left hx]
      have hlo : |FBlog(x)| ≤ |FBlog(x) - c| + |c| := by
        simpa only [sub_add_cancel] using abs_add_le (FBlog(x) - c) c
      have hc' := (CutoffWindow.cutoff_log_plateau m hc.1 hr x).1 (by linarith)
      simpa only [M, hc', Complex.ofReal_one, one_mul] using h₃
    · rw [ite_eq_right hx, ite_eq_right hx]
  have hφs := (mem_bruhatSmoothSubmodule_iff _).mp φ.property.1
  have hφb := hφc.bounded_above_of_compact_support (show HasCompactSupport φ.val from φ.property.2)
  obtain ⟨hT, _, _⟩ := truncatedHardySobolevConvolution_trace μ m a b s hab hs φ.val
    hφc.aemeasurable φ.property.2 hφb hm hms hφs hc.1 hc.2
  have hA := hardySobolevConvolution_eq_testAction μ m a b s hab hs φ hφc.aemeasurable hφb
  have hMA : IsNuclearOperator (M * A) :=
    (congrArg (fun U : FBspace(a, b, s) →L[ℂ] FBspace(a, b, s) ↦ IsNuclearOperator (M.comp U)) hA).mp hT
  have hPA : IsNuclearOperator (P * A) := by
    have h := mul_mem_nuclearEndomorphisms_left P (⟨M * A, hMA⟩ : nuclearEndomorphisms FBspace(a, b, s))
    change IsNuclearOperator (P * (M * A)) at h
    rwa [← mul_assoc, heq] at h
  exact ⟨P, hP, mul_mem_nuclearEndomorphisms_right P ⟨_, hPA⟩⟩

end
end CutoffFixed

namespace CutoffFactor
section
variable {X : Type*} [MeasurableSpace X] (ν : Measure X)
local notation "W" => Lp ℂ 2 ν

/-- Multiplication by an arbitrary bounded measurable symbol on L². -/
private theorem exists_bounded_multiplier (f : X → ℝ) (hf : Measurable f) (hb : ∃ B, ∀ x, |f x| ≤ B) :
    ∃ T : W →L[ℂ] W, ∀ v, (T v : X → ℂ) =ᵐ[ν] fun x ↦ (f x : ℂ) * v x := by
  obtain ⟨B, hB⟩ := hb
  let F (x : X) : ℂ := f x
  have hF : MemLp F (⊤ : ENNReal) ν := memLp_top_of_bound (Complex.measurable_ofReal.comp hf).aestronglyMeasurable
    B (.of_forall fun x ↦ by simpa only [F, Complex.norm_real, Real.norm_eq_abs] using hB x)
  let L := ContinuousLinearMap.mul ℂ ℂ
  exact ⟨L.holderL ν (⊤ : ENNReal) 2 2 (hF.toLp F), fun v ↦ (L.coeFn_holder (r := 2) (hF.toLp F) v).trans
    (hF.coeFn_toLp.mono fun x hx ↦ congrArg (· * v x) hx)⟩

/-- A continuous radial symbol cut to a fixed bounded logarithmic window defines a bounded multiplier. -/
private theorem exists_masked_multiplier (l : X → ℝ) (hl : Measurable l) (d : ℝ)
    (f : ℝ → ℝ) (hf : Continuous f) :
    ∃ T : W →L[ℂ] W, ∀ v, (T v : X → ℂ) =ᵐ[ν] fun x ↦
      ((if |l x| ≤ d then 1 else 0 : ℝ) : ℂ) * (f (l x) : ℂ) * v x := by
  let p (x : X) := if |l x| ≤ d then f (l x) else 0
  have hp : Measurable p := Measurable.ite (measurableSet_le (continuous_abs.measurable.comp hl) measurable_const)
    (hf.measurable.comp hl) measurable_const
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := -d) (b := d)).bddAbove_image hf.abs.continuousOn
  have hb (x : X) : |p x| ≤ max B 0 := by
    by_cases hx : |l x| ≤ d
    · simpa only [p, ite_eq_left hx] using
        (hB (mem_image_of_mem (fun x ↦ |f x|) (abs_le.mp hx))).trans (le_max_left B 0)
    · simpa only [p, ite_eq_right hx, abs_zero] using le_max_right B 0
  obtain ⟨T, hT⟩ := exists_bounded_multiplier ν p hp ⟨_, hb⟩
  refine ⟨T, fun v ↦ (hT v).mono fun x hx ↦ hx.trans ?_⟩
  dsimp only [p]
  split <;> simp

/-- The operator norm estimate for masked multipliers only uses the symbol difference inside the mask. -/
private theorem masked_multiplier_tendsto (l : X → ℝ) (d : ℝ) (F : ℝ → ℝ → ℝ) (f : ℝ → ℝ)
    (T : ℝ → W →L[ℂ] W) (S : W →L[ℂ] W)
    (hT : ∀ R v, (T R v : X → ℂ) =ᵐ[ν] fun x ↦
      ((if |l x| ≤ d then 1 else 0 : ℝ) : ℂ) * (F R (l x) : ℂ) * v x)
    (hS : ∀ v, (S v : X → ℂ) =ᵐ[ν] fun x ↦
      ((if |l x| ≤ d then 1 else 0 : ℝ) : ℂ) * (f (l x) : ℂ) * v x)
    (hF : ∀ ε > 0, ∀ᶠ R in atTop, ∀ x : ℝ, |x| ≤ d → |F R x - f x| < ε) :
    Tendsto T atTop (𝓝 S) := by
  apply CutoffSandwich.multiplier_opNorm_tendsto ν _ _ T S hT hS
  intro ε hε
  filter_upwards [hF ε hε] with R hR x
  by_cases hx : |l x| ≤ d
  · simpa only [ite_eq_left hx, Complex.ofReal_one, one_mul, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs] using hR (l x) hx
  · simp only [ite_eq_right hx, Complex.ofReal_zero, zero_mul, sub_self, norm_zero, hε]

end

section
variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
variable (μ : Measure G) [μ.IsHaarMeasure] (ν : Measure G)
local notation "W" => Lp ℂ 2 ν
local notation "Op" => W →L[ℂ] W
local notation "sand(" A ", " T ", " B ")" =>
  (⟨((A) * (T).val) * (B), mul_mem_nuclearEndomorphisms_right (B) (⟨(A) * (T).val,
    mul_mem_nuclearEndomorphisms_left (A) (T)⟩ : nuclearEndomorphisms W)⟩ : nuclearEndomorphisms W)

/-- Uniformly convergent positive radial weights on a fixed window reduce trace class
convergence to multiplying one fixed trace class compression on the two sides. -/
private theorem traceNorm_local_weighted_convolution (hν : ν ≪ μ) (hμ : μ ≪ ν) (l : G → ℝ)
    (hl : Measurable l) (d : ℝ) (φ : G → ℂ) (A C : Op) (F : ℝ → Op)
    (P : Op) (hP : ∀ v, (P v : G → ℂ) =ᵐ[μ] fun x ↦ ((if |l x| ≤ d then 1 else 0 : ℝ) : ℂ) * v x)
    (hnuc : IsNuclearOperator (P * A * P))
    (hA : ∀ v : W, ∀ᵐ x ∂μ, A v x = ∫ g, φ g * v (g⁻¹ * x) ∂μ)
    (q : ℝ → ℝ → ℝ) (q₀ : ℝ → ℝ) (hq : ∀ R, Continuous (q R)) (hq₀ : Continuous q₀)
    (hqp : ∀ R x, 0 < q R x) (hq₀p : ∀ x, 0 < q₀ x)
    (hC : ∀ v : W, ∀ᵐ x ∂μ, C v x = (q₀ (l x) : ℂ) *
      ∫ g, φ g * ((q₀ (l (g⁻¹ * x)) : ℂ)⁻¹ * v (g⁻¹ * x)) ∂μ)
    (hF : ∀ᶠ R in atTop, ∀ v : W, ∀ᵐ x ∂μ, F R v x = (q R (l x) : ℂ) *
      ∫ g, φ g * ((q R (l (g⁻¹ * x)) : ℂ)⁻¹ * v (g⁻¹ * x)) ∂μ)
    (hunif : ∀ ε > 0, ∀ᶠ R in atTop, ∀ x : ℝ, |x| ≤ d →
      |q R x - q₀ x| < ε ∧ |(q R x)⁻¹ - (q₀ x)⁻¹| < ε) :
    ∃ (J : nuclearEndomorphisms W) (K : ℝ → nuclearEndomorphisms W),
      J.val = P * C * P ∧ (∀ᶠ R in atTop, (K R).val = P * F R * P) ∧
      Tendsto (fun R ↦ traceNorm (K R - J)) atTop (𝓝 0) ∧
      Tendsto (fun R ↦ P * F R * P) atTop (𝓝 (P * C * P)) := by
  let p (x : G) : ℂ := ((if |l x| ≤ d then 1 else 0 : ℝ) : ℂ)
  have hpp (x : G) : p x * p x = p x := by dsimp only [p]; split <;> simp
  choose L hL using fun R ↦ exists_masked_multiplier ν l hl d (q R) (hq R)
  choose B hB using fun R ↦ exists_masked_multiplier ν l hl d (fun x ↦ (q R x)⁻¹)
    ((hq R).inv₀ fun x ↦ (hqp R x).ne')
  obtain ⟨L₀, hL₀⟩ := exists_masked_multiplier ν l hl d q₀ hq₀
  obtain ⟨B₀, hB₀⟩ := exists_masked_multiplier ν l hl d (fun x ↦ (q₀ x)⁻¹)
    (hq₀.inv₀ fun x ↦ (hq₀p x).ne')
  have hleft := masked_multiplier_tendsto ν l d q q₀ L L₀ hL hL₀
    (fun ε hε ↦ (hunif ε hε).mono fun R h x hx ↦ (h x hx).1)
  have hright := masked_multiplier_tendsto ν l d (fun R x ↦ (q R x)⁻¹) (fun x ↦ (q₀ x)⁻¹)
    B B₀ hB hB₀ (fun ε hε ↦ (hunif ε hε).mono fun R h x hx ↦ (h x hx).2)
  let N : nuclearEndomorphisms W := ⟨P * A * P, hnuc⟩
  have hLimit : P * C * P = L₀ * N.val * B₀ := by
    refine CutoffConjugated.compress_twisted μ ν hν φ p (fun x ↦ (q₀ (l x) : ℂ)) hpp A C P L₀ B₀
      hA hC hP (fun v ↦ hμ.ae_eq (hL₀ v)) (fun v ↦ ?_)
    simpa only [Complex.ofReal_inv] using hμ.ae_eq (hB₀ v)
  have hMoving : ∀ᶠ R in atTop, P * F R * P = L R * N.val * B R := by
    filter_upwards [hF] with R hr
    refine CutoffConjugated.compress_twisted μ ν hν φ p (fun x ↦ (q R (l x) : ℂ)) hpp A (F R) P (L R) (B R)
      hA hr hP (fun v ↦ hμ.ae_eq (hL R v)) (fun v ↦ ?_)
    simpa only [Complex.ofReal_inv] using hμ.ae_eq (hB R v)
  refine ⟨sand(L₀, N, B₀), fun R ↦ sand(L R, N, B R), hLimit.symm,
    hMoving.mono fun _ h ↦ h.symm, CutoffSandwich.traceNorm_sandwich_tendsto N L B L₀ B₀ hleft hright, ?_⟩
  rw [hLimit]
  exact ((hleft.mul (tendsto_const_nhds (x := N.val))).mul hright).congr' (hMoving.mono fun _ he ↦ he.symm)
end
end CutoffFactor

namespace CutoffLocalStrong

section
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
local notation "Op" => H →L[ℂ] H

/-- Finite propagation and operator norm convergence on each bounded window give strong
convergence everywhere for a uniformly bounded family. -/
private theorem strong_of_window_norm (F : ℝ → Op) (C : Op) (P : ℝ → Op)
    (K : ℝ) (hK : ∀ t, ‖F t‖ ≤ K)
    (hP : ∀ v, Tendsto (fun d ↦ P d v) atTop (𝓝 v))
    (hloc : ∀ d > 0, Tendsto (fun t ↦ P d * F t * P d) atTop (𝓝 (P d * C * P d)))
    (hprop : ∀ d > 0, ∃ D > 0, (P D * C * P D) * P d = C * P d ∧
      ∀ᶠ t in atTop, (P D * F t * P D) * P d = F t * P d) :
    ∀ v, Tendsto (fun t ↦ F t v) atTop (𝓝 (C v)) := by
  intro v
  refine Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
  let M := |K| + ‖C‖ + 1
  have hM : 0 < M := by dsimp only [M]; positivity
  let δ := (ε / 2) / M
  have hδ : 0 < δ := div_pos (half_pos hε) hM
  obtain ⟨d, hd, hdist⟩ := ((eventually_gt_atTop (0 : ℝ)).and
    (Metric.tendsto_nhds.mp (hP v) δ hδ)).exists
  obtain ⟨D, hD, hC, hF⟩ := hprop d hd
  have heval := ((ContinuousLinearMap.apply ℂ H (P d v)).continuous.tendsto _).comp (hloc D hD)
  have hcv : (P D * C * P D) (P d v) = C (P d v) :=
    congrArg (fun U : Op ↦ U v) hC
  have he : Tendsto (fun t ↦ F t (P d v)) atTop (𝓝 (C (P d v))) := by
    change Tendsto (fun t ↦ (P D * F t * P D) (P d v)) atTop (𝓝 ((P D * C * P D) (P d v))) at heval
    rw [hcv] at heval
    refine heval.congr' (hF.mono fun t ht ↦ ?_)
    exact congrArg (fun U : Op ↦ U v) ht
  filter_upwards [Metric.tendsto_nhds.mp he (ε/2) (half_pos hε)] with t ht
  have h1 : dist (F t v) (F t (P d v)) ≤ K * dist (P d v) v := by
    rw [dist_comm]
    exact ((F t).dist_le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hK t) dist_nonneg)
  have h2 := C.dist_le_opNorm (P d v) v
  have h3 : (K + ‖C‖) * dist (P d v) v < ε / 2 := by
    calc
      _ ≤ M * dist (P d v) v := mul_le_mul_of_nonneg_right (by dsimp only [M]; linarith [le_abs_self K]) dist_nonneg
      _ < ε / 2 := by rw [mul_comm]; exact (lt_div_iff₀ hM).mp hdist
  linarith [dist_triangle (F t v) (F t (P d v)) (C v),
    dist_triangle (F t (P d v)) (C (P d v)) (C v)]
end

section
variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
variable (μ : Measure G) [μ.IsHaarMeasure] (ν : Measure G)
local notation "W" => Lp ℂ 2 ν
local notation "Op" => W →L[ℂ] W

/-- A kernel supported in a bounded set of multiplicative shifts propagates a window
only by its logarithmic support radius, even after multiplication by density factors. -/
private theorem twisted_window_propagation (hν : ν ≪ μ) (l : G → ℝ)
    (hsub : ∀ g x, l (g⁻¹ * x) = l x - l g) (φ : G → ℂ) (b : ℝ)
    (hb : ∀ g, φ g ≠ 0 → |l g| ≤ b) (q : G → ℂ) (A : Op)
    (hA : ∀ v : W, ∀ᵐ x ∂μ, A v x = q x * ∫ g, φ g * ((q (g⁻¹ * x))⁻¹ * v (g⁻¹ * x)) ∂μ)
    (P : ℝ → Op) (hP : ∀ d v, (P d v : G → ℂ) =ᵐ[μ] fun x ↦ if |l x| ≤ d then v x else 0)
    (d D : ℝ) (hdD : d ≤ D) (hDb : d + b ≤ D) :
    (P D * A * P D) * P d = A * P d := by
  have hin (v : W) : P D (P d v) = P d v := by
    apply Lp.ext
    refine hν.ae_eq ?_
    filter_upwards [hP D (P d v), hP d v] with x hD hd
    rw [hD]
    by_cases hx : |l x| ≤ D
    · rw [ite_eq_left hx]
    · rw [ite_eq_right hx, hd, ite_eq_right (fun h ↦ hx (h.trans hdD))]
  apply ContinuousLinearMap.ext
  intro v
  change P D (A (P D (P d v))) = A (P d v)
  rw [hin]
  apply Lp.ext
  refine hν.ae_eq ?_
  filter_upwards [hP D (A (P d v)), hA (P d v)] with x hD ha
  rw [hD]
  by_cases hx : |l x| ≤ D
  · rw [ite_eq_left hx]
  · rw [ite_eq_right hx, ha]
    suffices h : (∫ g, φ g * ((q (g⁻¹ * x))⁻¹ * P d v (g⁻¹ * x)) ∂μ) = 0 by rw [h, mul_zero]
    apply integral_eq_zero_of_ae
    have hmp : MeasurePreserving (fun g : G ↦ g⁻¹ * x) μ μ :=
      (measurePreserving_mul_right μ x).comp (Measure.measurePreserving_inv μ)
    filter_upwards [hmp.quasiMeasurePreserving.ae_eq_comp (hP d v)] with g hg
    change P d v (g⁻¹ * x) = if |l (g⁻¹ * x)| ≤ d then v (g⁻¹ * x) else 0 at hg
    by_cases hφ : φ g = 0
    · simp [hφ]
    · have hy : ¬ |l (g⁻¹ * x)| ≤ d := by
        intro hh
        apply hx
        calc
          |l x| = |l (g⁻¹ * x) + l g| := by rw [hsub, sub_add_cancel]
          _ ≤ |l (g⁻¹ * x)| + |l g| := abs_add_le _ _
          _ ≤ _ := (add_le_add hh (hb g hφ)).trans hDb
      rw [hg, ite_eq_right hy, mul_zero, mul_zero]
      rfl
end
end CutoffLocalStrong

namespace CutoffWhole

/-- The sharp bounded logarithmic window multipliers converge strongly to the identity. -/
private theorem exhausting_windows {X : Type*} [CommGroup X] [TopologicalSpace X] [IsTopologicalGroup X] [T2Space X]
    [LocallyCompactSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (ν : Measure X)
    (l : X → ℝ) (hl : Measurable l) :
    ∃ P : ℝ → Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν,
      (∀ d v, (P d v : X → ℂ) =ᵐ[ν] fun x ↦ ((if |l x| ≤ d then 1 else 0 : ℝ) : ℂ) * v x) ∧
      ∀ v, Tendsto (fun d ↦ P d v) atTop (𝓝 v) := by
  let p (d : ℝ) (x : X) : ℝ := if |l x| ≤ d then 1 else 0
  have hm (d) : Measurable (p d) := Measurable.ite (measurableSet_le (continuous_abs.measurable.comp hl) measurable_const)
    measurable_const measurable_const
  have hb (d x) : |p d x| ≤ 1 := by dsimp only [p]; split <;> norm_num
  choose P _ hP using fun d ↦ exists_lpCutoffMultiplier ν (p d) (hm d) (hb d)
  have hlim : ∀ᵐ x ∂ν, ∀ᶠ d in atTop, p d x = 1 := .of_forall fun x ↦
    (eventually_ge_atTop (|l x|)).mono fun _ hd ↦ ite_eq_left hd
  refine ⟨P, hP, ?_⟩
  intro v
  exact CutoffWindow.multiplier_strong_of_ae_eventually_eq ν p (fun _ ↦ 1) hm measurable_const
    hb (by simp) hlim P (1 : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) hP (fun v ↦ .of_forall fun x ↦ by simp) v

section
variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
variable (μ : Measure G) [μ.IsHaarMeasure] (ν : Measure G)
local notation "W" => Lp ℂ 2 ν
local notation "Op" => W →L[ℂ] W
local notation "mask(" l ", " d ", " x ")" => ((if |l x| ≤ d then 1 else 0 : ℝ) : ℂ)
local notation "rep(" l ", " φ ", " q ", " v ", " x ")" =>
  ((q (l x) : ℂ) * ∫ g, φ g * ((q (l (g⁻¹ * x)) : ℂ)⁻¹ * v (g⁻¹ * x)) ∂μ)

/-- Local trace class convergence on each logarithmic window and bounded finite propagation
supply the full strong convergence of the conjugated convolutions. -/
private theorem strong_and_local (hν : ν ≪ μ) (hμ : μ ≪ ν) (l : G → ℝ)
    (hl : Continuous l) (hsub : ∀ g x, l (g⁻¹ * x) = l x - l g)
    (φ : G → ℂ) (hφK : HasCompactSupport φ) (A C : Op) (F : ℝ → Op)
    (k : ℝ) (hk : ∀ R, ‖F R‖ ≤ k)
    (hA : ∀ v : W, ∀ᵐ x ∂μ, A v x = ∫ g, φ g * v (g⁻¹ * x) ∂μ)
    (hnuc : ∀ d > 0, ∀ P : Op, (∀ v, (P v : G → ℂ) =ᵐ[μ] fun x ↦ mask(l, d, x) * v x) →
      IsNuclearOperator (P * A * P))
    (q : ℝ → ℝ → ℝ) (q₀ : ℝ → ℝ) (hq : ∀ R, Continuous (q R)) (hq₀ : Continuous q₀)
    (hqp : ∀ R x, 0 < q R x) (hq₀p : ∀ x, 0 < q₀ x)
    (hC : ∀ v : W, ∀ᵐ x ∂μ, C v x = rep(l, φ, q₀, v, x))
    (hF : ∀ᶠ R in atTop, ∀ v : W, ∀ᵐ x ∂μ, F R v x = rep(l, φ, (q R), v, x))
    (hunif : ∀ d > 0, ∀ ε > 0, ∀ᶠ R in atTop, ∀ x : ℝ, |x| ≤ d →
      |q R x - q₀ x| < ε ∧ |(q R x)⁻¹ - (q₀ x)⁻¹| < ε) :
    (∀ v, Tendsto (fun R ↦ F R v) atTop (𝓝 (C v))) ∧
    ∀ d > 0, ∀ P : Op, (∀ v, (P v : G → ℂ) =ᵐ[μ] fun x ↦ mask(l, d, x) * v x) →
      ∃ (J : nuclearEndomorphisms W) (K : ℝ → nuclearEndomorphisms W),
        J.val = P * C * P ∧ (∀ᶠ R in atTop, (K R).val = P * F R * P) ∧
        Tendsto (fun R ↦ traceNorm (K R - J)) atTop (𝓝 0) := by
  have hloc (d : ℝ) (hd : 0 < d) (P : Op)
      (hP : ∀ v, (P v : G → ℂ) =ᵐ[μ] fun x ↦ mask(l, d, x) * v x) :=
    CutoffFactor.traceNorm_local_weighted_convolution μ ν hν hμ l hl.measurable d φ A C F P hP
      (hnuc d hd P hP) hA q q₀ hq hq₀ hqp hq₀p hC hF (hunif d hd)
  constructor
  · obtain ⟨P, hPν, hPstrong⟩ := exhausting_windows ν l hl.measurable
    have hP (d : ℝ) (v : W) := hμ.ae_eq (hPν d v)
    have hmask (d : ℝ) (v : W) : (P d v : G → ℂ) =ᵐ[μ] fun x ↦ if |l x| ≤ d then v x else 0 := by
      refine (hP d v).mono fun x hx ↦ hx.trans ?_
      by_cases hx : |l x| ≤ d <;> simp [hx]
    obtain ⟨B, hB⟩ := hφK.bddAbove_image hl.abs.continuousOn
    have hb (g : G) (hg : φ g ≠ 0) : |l g| ≤ |B| :=
      (hB (mem_image_of_mem (fun x ↦ |l x|) (subset_tsupport _ hg))).trans (le_abs_self B)
    apply CutoffLocalStrong.strong_of_window_norm F C P k hk hPstrong
    · intro d hd
      obtain ⟨_, _, _, _, _, hOp⟩ := hloc d hd (P d) (hP d)
      exact hOp
    · intro d hd
      let D := d + |B| + 1
      have he (S : Op) (Q : G → ℂ) (hS : ∀ v : W, ∀ᵐ x ∂μ, S v x = Q x *
          ∫ g, φ g * ((Q (g⁻¹ * x))⁻¹ * v (g⁻¹ * x)) ∂μ) :=
        CutoffLocalStrong.twisted_window_propagation μ ν hν l hsub φ |B| hb Q S hS P hmask d D
          (by dsimp only [D]; linarith [abs_nonneg B]) (by dsimp only [D]; linarith)
      exact ⟨D, by dsimp only [D]; positivity, he C (fun x ↦ (q₀ (l x) : ℂ)) hC,
        hF.mono fun R hr ↦ he (F R) (fun x ↦ (q R (l x) : ℂ)) hr⟩
  · intro d hd P hP
    obtain ⟨J, K, hJ, hK, h1, _⟩ := hloc d hd P hP
    exact ⟨J, K, hJ, hK, h1⟩
end
end CutoffWhole

namespace CutoffActualLimit
variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
variable (m : G →ₜ* ℝ≥0ˣ) (μ : Measure G) [μ.IsHaarMeasure]

/-- The limiting exponentially tilted convolution is the same integral kernel as
the quotient of its limiting multiplication symbols. -/
private theorem tilted_rep_as_quotient (l : G → ℝ) (hsub : ∀ g x, l (g⁻¹ * x) = l x - l g)
    (k : ℝ) (w : ℝ → ℝ) (hw : ∀ x, 0 < w x) (φ v : G → ℂ) (x : G) :
    let H (y : G) : ℂ := Real.sqrt (w (l y))
    let q (t : ℝ) := Real.exp (k * t) / Real.sqrt (w t)
    (H x)⁻¹ * (∫ g, ((Real.exp (k * l g) : ℂ) * φ g) * (H (g⁻¹ * x) * v (g⁻¹ * x)) ∂μ) =
      (q (l x) : ℂ) * ∫ g, φ g * ((q (l (g⁻¹ * x)) : ℂ)⁻¹ * v (g⁻¹ * x)) ∂μ := by
  intro H q
  rw [← integral_const_mul, ← integral_const_mul]
  apply integral_congr_ae (.of_forall fun g ↦ ?_)
  have he : (Real.exp (k * l x) : ℂ) =
      (Real.exp (k * l g) : ℂ) * (Real.exp (k * l (g⁻¹ * x)) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add, hsub]
    ring_nf
  have hp (t : ℝ) : (Real.sqrt (w t) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hw t)).ne'
  have hn (t : ℝ) : (Real.exp (k * t) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  dsimp only [q, H]
  rw [Complex.ofReal_div, Complex.ofReal_div, he]
  field_simp [hp, hn]

local notation "lg(" x ")" => (Real.log ((m x).val : ℝ))
local notation "Den(" a ", " s ", " x ")" => (intervalSobolevDensity (-a) a s (lg(x)))
local notation "HS(" a ", " s ")" => (CompactIntervalSobolev μ (fun x : G ↦ lg(x)) (-a) a s)
local notation "sh(" j ", " g ")" => (if (j : Bool) then g else (g)⁻¹)
local notation "sg(" j ", " t ")" => (if (j : Bool) then (t : ℝ) else (-t : ℝ))
local notation "UC(" U ")" => (U).toContinuousLinearEquiv.toContinuousLinearMap

/-- At either end, the tilted convolution is the strong limit of the unitarily shifted
weighted test action, and its bounded logarithmic compressions are trace norm limits. -/
private theorem actual_tilted_window_limit (hm : IsModulation m) (hsur : Surjective m)
    (α s : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s) (hab : -α ≤ α)
    (φ : BruhatCompactSupport G) (hc : Continuous φ.val) (u : ℝ → G)
    (hu : ∀ᶠ R in atTop, ((m (u R)).val : ℝ) = R) (j : Bool)
    (U : G → HS(α, s) ≃ₗᵢ[ℂ] HS(α, s)) (hU : ∀ g v, (U g v : G → ℂ) =ᵐ[μ] fun x ↦
      ((Real.sqrt (Den(α, s, g⁻¹ * x)) : ℂ) / (Real.sqrt (Den(α, s, x)) : ℂ)) * v (g⁻¹ * x))
    (d : ℝ) (hd : 0 < d) (P : HS(α, s) →L[ℂ] HS(α, s)) (hP : ∀ v, (P v : G → ℂ) =ᵐ[μ]
      fun x ↦ ((if |lg(x)| ≤ d then 1 else 0 : ℝ) : ℂ) * v x) :
    let A : HS(α, s) →L[ℂ] HS(α, s) := hardySobolevTestAction μ m (-α) α s hab hs φ
    let T (R : ℝ) := U (sh(j, u R))
    ∃ (C : HS(α, s) →L[ℂ] HS(α, s)) (J : nuclearEndomorphisms (HS(α, s))) (K : ℝ → nuclearEndomorphisms (HS(α, s))),
      (∀ v, (C v : G → ℂ) =ᵐ[μ] fun x ↦ (Real.sqrt (Den(α, s, x)) : ℂ)⁻¹ * ∫ g,
        ((Real.exp (sg(j, α) * lg(g)) : ℂ) * φ.val g) * ((Real.sqrt (Den(α, s, g⁻¹ * x)) : ℂ) * v (g⁻¹ * x)) ∂μ) ∧
      (∀ v, Tendsto (fun R ↦ (T R).symm (A (T R v))) atTop (𝓝 (C v))) ∧
      J.val = P * C * P ∧ (∀ᶠ R in atTop, (K R).val = P * (UC((T R).symm) * A * UC(T R)) * P) ∧
      Tendsto (fun R ↦ traceNorm (K R - J)) atTop (𝓝 0) := by
  intro A T
  let l (x : G) := lg(x)
  let w := intervalSobolevDensity (-α) α s
  let ν := μ.withDensity fun x : G ↦ ENNReal.ofReal (w (l x))
  let D (x : G) : ℂ := Real.sqrt (w (l x))
  let k := sg(j, α)
  let ψ (x : G) : ℂ := (Real.exp (k * l x) : ℂ) * φ.val x
  have hl : Continuous l := (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)).log
    fun x ↦ NNReal.coe_ne_zero.mpr (m x).ne_zero
  have hpG (x : G) : ((m x).val : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr (m x).ne_zero
  have hmul (g x : G) : l (g * x) = l g + l x := by
    simp only [l, map_mul, Units.val_mul, NNReal.coe_mul, Real.log_mul (hpG g) (hpG x)]
  have hinv (g : G) : l g⁻¹ = -(l g) := by simp only [l, map_inv, Units.val_inv_eq_inv_val, NNReal.coe_inv, Real.log_inv]
  have hsub (g x : G) : l (g⁻¹ * x) = l x - l g := by rw [hmul, hinv]; ring
  have hcW : Continuous w := by
    exact continuous_intervalSobolevDensity (-α) α s
  have hp (x : ℝ) : 0 < w x := mul_pos (lt_max_of_lt_left (Real.exp_pos _))
    (Real.rpow_pos_of_pos (by positivity) _)
  have hsqrt (x) := Real.sqrt_pos.mpr (hp x)
  have hd₀ (x) : D x ≠ 0 := Complex.ofReal_ne_zero.mpr (hsqrt _).ne'
  have hw := hcW.comp hl
  have hν : ν ≪ μ := withDensity_absolutelyContinuous ..
  have hμ : μ ≪ ν := withDensity_absolutelyContinuous' hw.measurable.ennreal_ofReal.aemeasurable
    (.of_forall fun x ↦ (ENNReal.ofReal_pos.mpr (hp _)).ne')
  have hψ : Continuous ψ := (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
    (continuous_const.mul hl))).mul hc
  have hψK : HasCompactSupport ψ := (show HasCompactSupport φ.val from φ.property.2).mul_left
  obtain ⟨C, hC⟩ := CutoffTilted.exists_unweighted_convolution_on_density m μ _ hw.measurable
    (fun x ↦ hp _) ψ hψ hψK
  let A' (R : ℝ) := UC((T R).symm) * A * UC(T R)
  let t (R : ℝ) := sg(j, Real.log R)
  let q (R x : ℝ) := (Real.sqrt (w (t R + x)) / Real.sqrt (w x)) / Real.sqrt (w (t R))
  let q₀ (x : ℝ) := Real.exp (k * x) / Real.sqrt (w x)
  have hQ R : Continuous (q R) := ((Real.continuous_sqrt.comp (hcW.comp (continuous_const.add continuous_id))).div
    (Real.continuous_sqrt.comp hcW) fun x ↦ (hsqrt x).ne').div_const _
  have hQ₀ : Continuous q₀ := (Real.continuous_exp.comp (continuous_const.mul continuous_id)).div
    (Real.continuous_sqrt.comp hcW) fun x ↦ (hsqrt x).ne'
  have hqpos R x : 0 < q R x := div_pos (div_pos (hsqrt _) (hsqrt _)) (hsqrt _)
  have hq₀pos x : 0 < q₀ x := div_pos (Real.exp_pos _) (hsqrt _)
  have hcenter : ∀ᶠ R in atTop, l (sh(j, u R)) = t R := by
    filter_upwards [hu] with R hr
    have he : l (u R) = Real.log R := congrArg Real.log hr
    cases j <;> simp [t, hinv, he]
  have hA (v : HS(α, s)) : ∀ᵐ x ∂μ, A v x = ∫ g, φ.val g * v (g⁻¹ * x) ∂μ :=
    hardySobolevTestAction_apply μ m (-α) α s hab hs φ v
  have hmoved : ∀ᶠ R in atTop, ∀ v : HS(α, s), ∀ᵐ x ∂μ, A' R v x = (q R (l x) : ℂ) *
      ∫ g, φ.val g * ((q R (l (g⁻¹ * x)) : ℂ)⁻¹ * v (g⁻¹ * x)) ∂μ := by
    filter_upwards [hcenter] with R hr
    intro v
    have hq (y : G) : D (sh(j, u R) * y) / D y / (Real.sqrt (w (t R)) : ℂ) =
        (q R (l y) : ℂ) := by simp only [D, hmul, hr, q, Complex.ofReal_div]
    have ht := CutoffConjugated.conjugated_convolution_rep μ ν φ.val D hd₀ A hA (sh(j, u R)) (T R)
      (hU _) (Real.sqrt (w (t R)) : ℂ) (Complex.ofReal_ne_zero.mpr (hsqrt _).ne') v
    refine ht.mono fun x hx ↦ hx.trans ?_
    simp only [hq]
  have hfixed (v : HS(α, s)) : ∀ᵐ x ∂μ, C v x = (q₀ (l x) : ℂ) *
      ∫ g, φ.val g * ((q₀ (l (g⁻¹ * x)) : ℂ)⁻¹ * v (g⁻¹ * x)) ∂μ :=
    (hC v).mono fun x hx ↦ hx.trans (tilted_rep_as_quotient μ l hsub k w hp φ.val v x)
  have hunif (b : ℝ) (hb : 0 < b) (δ : ℝ) (hδ : 0 < δ) :
      ∀ᶠ R in atTop, ∀ x : ℝ, |x| ≤ b → |q R x - q₀ x| < δ ∧ |(q R x)⁻¹ - (q₀ x)⁻¹| < δ := by
    have hu := Real.tendsto_log_atTop.eventually
      (CutoffDensity.uniform_sobolev_edge_multipliers α s b hα hb.le j δ hδ)
    cases j <;> simpa only [q, q₀, k, w, t, Bool.false_eq_true, ite_false, ite_true, neg_mul] using hu
  have hbound (R : ℝ) : ‖A' R‖ ≤ ‖A‖ := by
    have h₁ := CutoffWindow.unitary_opNorm_le_one (T R).symm
    have h₂ := CutoffWindow.unitary_opNorm_le_one (T R)
    exact (norm_mul_le _ _).trans ((mul_le_of_le_one_right (norm_nonneg _) h₂).trans
      ((norm_mul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) h₁)))
  have hnuc (b : ℝ) (_hb : 0 < b) (S : HS(α, s) →L[ℂ] HS(α, s))
      (hS : ∀ v, (S v : G → ℂ) =ᵐ[μ] fun x ↦ ((if |l x| ≤ b then 1 else 0 : ℝ) : ℂ) * v x) :
      IsNuclearOperator (S * A * S) := by
    obtain ⟨ε, ρ, hρ⟩ := CutoffLarge.exists_cofinal_cutoff m
    obtain ⟨Q, hQ, hn⟩ := CutoffFixed.hardySobolev_fixed_window_nuclear m μ (-α) α s hab hs hm hsur φ hc ε ρ hρ 0 b
    have heq : Q = S := by
      apply ContinuousLinearMap.ext
      intro v
      apply Lp.ext
      filter_upwards [hQ v, hν.ae_eq (hS v)] with x hx hy
      rw [hx, hy, sub_zero]
      change (if |l x| ≤ b then _ else _) = _
      split <;> simp
    rwa [heq] at hn
  have hwhole := CutoffWhole.strong_and_local μ ν hν hμ l hl hsub φ.val φ.property.2 A C A' ‖A‖ hbound
    hA hnuc q q₀ hQ hQ₀ hqpos hq₀pos hfixed hmoved hunif
  refine ⟨C, ?_⟩
  exact (hwhole.2 d hd P hP).imp fun J hJ ↦ hJ.imp fun K hK ↦ ⟨hC, hwhole.1, hK⟩

end CutoffActualLimit

end CutoffConvolutionLimits

namespace CutoffSplit

section
open Function Filter MeasureTheory Set
open scoped NNReal ENNReal Topology
variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m) (ν : Measure G) [hν : ν.IsHaarMeasure]
  (ν₁ : Measure m.toMonoidHom.ker) [hν₁ : ν₁.IsHaarMeasure] (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ m)
local notation "K" => m.toMonoidHom.ker

include hm hν hν₁ hτ in
/-- With the product Haar normalization, dividing the compact-character transform by the
square root of the compact kernel's mass gives a surjective Hilbert-space isometry. -/
private theorem normalized_regularIsotypicTransform
    (hprod : (ν₁.prod positiveRealHaar).map (fun z : K × ℝ≥0ˣ ↦ (z.1 : G) * τ z.2) = ν) :
    ∃ (r : ℝ) (_ : 0 < r) (U : RegularL2 ν ≃ₗᵢ[ℂ]
        lp (fun _ : PontryaginDual K ↦ RegularL2 positiveRealHaar) 2),
      ∀ v, U v = (r : ℂ) • regularIsotypicTransform m hm ν ν₁ τ hτ v := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let d := Real.sqrt (ν₁.real univ)
  have hd : 0 < d := Real.sqrt_pos.mpr measureReal_univ_pos
  have hd' : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd.ne'
  obtain ⟨T, hT⟩ := regularIsotypicTransform_continuousLinear m hm ν ν₁ τ hτ
  have hn (v : RegularL2 ν) : ‖T v‖ = d * ‖v‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg hd.le (norm_nonneg _))).mp
    rw [hT, mul_pow, Real.sq_sqrt measureReal_nonneg]
    have hmap : (ν₁.prod positiveRealHaar).map (fun z : K × ℝ≥0ˣ ↦ (z.1 : G) * τ z.2) = (1 : ℝ≥0∞) • ν := by
      simpa only [one_smul] using hprod
    simpa only [ENNReal.toReal_one, mul_one] using regularIsotypicTransform_norm_sq m hm ν ν₁ τ hτ 1 hmap v
  let A : RegularL2 ν →ₗᵢ[ℂ] lp (fun _ : PontryaginDual K ↦ RegularL2 positiveRealHaar) 2 :=
    { toLinearMap := (d : ℂ)⁻¹ • T.toLinearMap
      norm_map' v := by
        change ‖(d : ℂ)⁻¹ • T v‖ = ‖v‖
        rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd, hn,
          inv_mul_cancel_left₀ hd.ne'] }
  have ha : Surjective A := by
    intro y
    obtain ⟨v, hv⟩ := regularIsotypicTransform_surjective m hm ν ν₁ τ hτ ((d : ℂ) • y)
    refine ⟨v, ?_⟩
    change (d : ℂ)⁻¹ • T v = y
    rw [hT, hv, smul_smul, inv_mul_cancel₀ hd', one_smul]
  refine ⟨d⁻¹, inv_pos.mpr hd, LinearIsometryEquiv.ofSurjective A ha, fun v ↦ ?_⟩
  change (d : ℂ)⁻¹ • T v = _
  rw [hT, Complex.ofReal_inv]

include hm hν₁ in
/-- The inverse compact coordinate used by the Section 4.3 transform also preserves
product Haar measure. -/
private theorem split_inverted_measure
    (hprod : (ν₁.prod positiveRealHaar).map (fun z : K × ℝ≥0ˣ ↦ (z.1 : G) * τ z.2) = ν) :
    MeasurePreserving (fun z : K × ℝ≥0ˣ ↦ (z.1 : G)⁻¹ * τ z.2) (ν₁.prod positiveRealHaar) ν := by
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  let : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let : SFinite positiveRealHaar := by unfold positiveRealHaar; infer_instance
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  have h : MeasurePreserving (fun z : K × ℝ≥0ˣ ↦ (z.1 : G) * τ z.2) (ν₁.prod positiveRealHaar) ν :=
    ⟨(continuous_subtype_val.comp continuous_fst).measurable.mul (τ.continuous.comp continuous_snd).measurable, hprod⟩
  exact h.comp ((Measure.measurePreserving_inv ν₁).prod (MeasurePreserving.id positiveRealHaar))

include hm hν hν₁ hτ in
/-- Multiplying by any bounded radial symbol multiplies each compact-character
component by the very same radial symbol. -/
private theorem regularIsotypicTransform_radial
    (hprod : (ν₁.prod positiveRealHaar).map (fun z : K × ℝ≥0ˣ ↦ (z.1 : G) * τ z.2) = ν)
    (p : ℝ≥0ˣ → ℂ) (P : RegularL2 ν →L[ℂ] RegularL2 ν)
    (hP : ∀ v, (P v : G → ℂ) =ᵐ[ν] fun x ↦ p (m x) * v x) (v : RegularL2 ν) (ω : PontryaginDual K) :
    (regularIsotypicTransform m hm ν ν₁ τ hτ (P v) ω : ℝ≥0ˣ → ℂ) =ᵐ[positiveRealHaar] fun t ↦
      p t * regularIsotypicTransform m hm ν ν₁ τ hτ v ω t := by
  let : SFinite positiveRealHaar := by unfold positiveRealHaar; infer_instance
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  have h := split_inverted_measure m hm ν ν₁ τ hprod
  have hpull := Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.ae_eq_comp
    (h.quasiMeasurePreserving.ae_eq_comp (hP v)))
  filter_upwards [regularIsotypicTransform_ae_eq m hm ν ν₁ τ hτ ω (P v),
    regularIsotypicTransform_ae_eq m hm ν ν₁ τ hτ ω v, hpull]
    with t hPv hv hp
  rw [hPv, hv, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hp] with k hk
  change P v ((k : G)⁻¹ * τ t) = p (m ((k : G)⁻¹ * τ t)) * v ((k : G)⁻¹ * τ t) at hk
  rw [hk, map_mul, map_inv, show m k.val = 1 from k.property, inv_one, one_mul, hτ]
  ring

include hτ in
/-- The section gives an extension trivial on its image, with exactly the chosen
character on the norm-one subgroup. -/
private theorem exists_regularIsotypic_sectionCharacters :
    ∃ γ : PontryaginDual K → PontryaginDual G,
      (∀ ω (k : K), γ ω k = ω k) ∧ ∀ ω t, γ ω (τ t) = 1 := by
  let P : G →ₜ* G := ContinuousMonoidHom.id G / τ.comp m
  have hP (g : G) : P g ∈ K := by
    change m (g / τ (m g)) = 1
    rw [map_div, hτ, div_self']
  let r : G →ₜ* K := ⟨P.toMonoidHom.codRestrict _ hP, P.continuous.subtype_mk _⟩
  refine ⟨fun ω ↦ ω.comp r, fun ω k ↦ congrArg ω (Subtype.ext ?_), fun ω t ↦ ?_⟩
  · change (k : G) / τ (m k.val) = k.val
    rw [show m k.val = 1 from k.property, map_one, div_one]
  · change ω (r (τ t)) = 1
    rw [show r (τ t) = 1 from Subtype.ext (by
      change τ t / τ (m (τ t)) = 1
      rw [hτ, div_self']), map_one]

include hm hν hν₁ hτ in
/-- The radial Fourier transform of the inverse-indexed compact coordinate is the full
group Fourier transform at the product character, under the product Haar normalization. -/
private theorem regularIsotypicTransform_fourier
    (hprod : (ν₁.prod positiveRealHaar).map (fun z : K × ℝ≥0ˣ ↦ (z.1 : G) * τ z.2) = ν)
    (γ : PontryaginDual G) (ω : PontryaginDual K)
    (hγω : ∀ k : K, γ k = ω k) (hγτ : ∀ t, γ (τ t) = 1) (v : RegularL2 ν)
    (hv : Integrable (v : G → ℂ) ν) :
      let u := regularIsotypicTransform m hm ν ν₁ τ hτ v ω⁻¹
      Integrable (u : ℝ≥0ˣ → ℂ) positiveRealHaar ∧ ∀ θ : PontryaginDual ℝ≥0ˣ,
        lcaFourier positiveRealHaar u θ = lcaFourier ν v (γ * (show PontryaginDual G from θ.comp m)) := by
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  let : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let : SFinite positiveRealHaar := by unfold positiveRealHaar; infer_instance
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let η := ν₁.prod positiveRealHaar
  let j (z : K × ℝ≥0ˣ) := (z.1 : G)⁻¹ * τ z.2
  have hpres : MeasurePreserving j η ν := split_inverted_measure m hm ν ν₁ τ hprod
  have hjm : Measurable j := hpres.measurable
  intro u
  let g (z : K × ℝ≥0ˣ) := star ((ω⁻¹ z.1 : Circle) : ℂ) * v (j z)
  have hvj := hpres.integrable_comp_of_integrable hv
  have hg : Integrable g η := by
    refine hvj.norm.mono' ?_ (.of_forall fun z ↦ ?_)
    · exact (continuous_subtype_val.comp ((ω⁻¹).continuous.comp continuous_fst)).star.aestronglyMeasurable.mul
        ((Lp.stronglyMeasurable v).comp_measurable hjm).aestronglyMeasurable
    · simp [g, Function.comp_apply]
  have hu : (u : ℝ≥0ˣ → ℂ) =ᵐ[positiveRealHaar] fun t ↦ ∫ k : K, g (k, t) ∂ν₁ := by
    simpa only [u, g, j] using regularIsotypicTransform_ae_eq m hm ν ν₁ τ hτ ω⁻¹ v
  refine ⟨hg.integral_prod_right.congr hu.symm, fun θ ↦ ?_⟩
  let w (z : K × ℝ≥0ˣ) := g z * star (θ z.2 : ℂ)
  have hw : Integrable w η := by
    refine hg.norm.mono' (hg.aestronglyMeasurable.mul
      ((continuous_subtype_val.comp (θ.continuous.comp continuous_snd)).star.aestronglyMeasurable)) ?_
    exact .of_forall fun z ↦ by simp [w]
  let χ : PontryaginDual G := γ * (show PontryaginDual G from θ.comp m)
  have hχ (k : K) (t : ℝ≥0ˣ) : χ (j (k, t)) = (ω k)⁻¹ * θ t := by
    change γ (j (k, t)) * θ (m (j (k, t))) = _
    rw [show j (k, t) = (k : G)⁻¹ * τ t from rfl, map_mul, map_inv, hγω, hγτ, mul_one, map_mul, map_inv,
      show m k.val = 1 from k.property, inv_one, one_mul, hτ]
  calc
    lcaFourier positiveRealHaar u θ = ∫ t, ∫ k, w (k, t) ∂ν₁ ∂positiveRealHaar := by
      refine integral_congr_ae (hu.mono fun t ht ↦ ?_)
      change u t * star (θ t : ℂ) = ∫ k, g (k, t) * star (θ t : ℂ) ∂ν₁
      rw [ht, integral_mul_const]
    _ = ∫ z, w z ∂η := (integral_prod_symm _ hw).symm
    _ = ∫ x : G, v x * star (χ x : ℂ) ∂η.map j := by
      have hi : AEStronglyMeasurable (fun x : G ↦ v x * star (χ x : ℂ)) (η.map j) :=
        (Lp.stronglyMeasurable v).aestronglyMeasurable.mul
          (continuous_subtype_val.comp χ.continuous).star.aestronglyMeasurable
      rw [integral_map hjm.aemeasurable hi]
      refine integral_congr_ae (.of_forall fun ⟨k, t⟩ ↦ ?_)
      change star ((ω⁻¹ k : Circle) : ℂ) * v (j (k, t)) * star (θ t : ℂ) =
        v (j (k, t)) * star (χ (j (k, t)) : ℂ)
      rw [hχ, Circle.coe_mul, star_mul', show ω⁻¹ k = (ω k)⁻¹ from rfl]
      ring
    _ = _ := by rw [hpres.map_eq]; rfl
end

section
open Function Filter MeasureTheory Set
open scoped NNReal ENNReal Topology

/-- The angular log-coordinate reparametrizes the entire dual of the positive reals. -/
private theorem radial_characters :
    ∃ e : Multiplicative ℝ ≃ₜ* PontryaginDual ℝ≥0ˣ, ∀ (t : ℝ) (x : ℝ≥0ˣ),
      e (Multiplicative.ofAdd t) x = Circle.exp (t * Real.log (x.val : ℝ)) := by
  let h : ℝ≥0ˣ ≃ₜ Multiplicative ℝ := (Nonneg.unitsHomeomorphPos ℝ).trans Real.expOrderIso.symm.toHomeomorph
  have hh (x : ℝ≥0ˣ) : (h x).toAdd = Real.log (x.val : ℝ) :=
    (Real.log_of_pos (NNReal.coe_pos.mpr (Units.zero_lt x))).symm
  let logE : ℝ≥0ˣ ≃ₜ* Multiplicative ℝ := ContinuousMulEquiv.mk' h (fun x y ↦ by
    change (h (x*y)).toAdd = (h x).toAdd + (h y).toAdd
    rw [hh, hh, hh, Units.val_mul, NNReal.coe_mul, Real.log_mul
      (NNReal.coe_pos.mpr (Units.zero_lt x)).ne' (NNReal.coe_pos.mpr (Units.zero_lt y)).ne'])
  let q : PontryaginDual (Multiplicative ℝ) ≃ₜ* PontryaginDual ℝ≥0ˣ :=
    { toFun := PontryaginDual.map (logE : ℝ≥0ˣ →ₜ* Multiplicative ℝ)
      invFun := PontryaginDual.map (logE.symm : Multiplicative ℝ →ₜ* ℝ≥0ˣ)
      map_mul' := (PontryaginDual.map (logE : ℝ≥0ˣ →ₜ* Multiplicative ℝ)).map_mul
      left_inv := fun χ ↦ PontryaginDual.ext fun x ↦ congrArg χ (logE.apply_symm_apply x)
      right_inv := fun χ ↦ PontryaginDual.ext fun x ↦ congrArg χ (logE.symm_apply_apply x)
      continuous_toFun := (PontryaginDual.map (logE : ℝ≥0ˣ →ₜ* Multiplicative ℝ)).continuous
      continuous_invFun := (PontryaginDual.map (logE.symm : Multiplicative ℝ →ₜ* ℝ≥0ˣ)).continuous }
  obtain ⟨R, hR⟩ := exists_realPontryaginDualEquiv
  let c : ℝ := 2 * Real.pi
  have hc : c ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
  let scale : Multiplicative ℝ ≃ₜ* Multiplicative ℝ :=
    ContinuousMulEquiv.mk' (show ℝ ≃ₜ ℝ from Homeomorph.mulLeft₀ c⁻¹ (inv_ne_zero hc))
      fun x y ↦ mul_add _ x.toAdd y.toAdd
  refine ⟨scale.trans (R.trans q), fun t x ↦ ?_⟩
  change R (Multiplicative.ofAdd (c⁻¹ * t)) (Multiplicative.ofAdd (h x).toAdd) = _
  rw [hh, hR]
  congr 1
  change c * (c⁻¹ * t * _) = _
  rw [mul_assoc c⁻¹, mul_inv_cancel_left₀ hc]

/-- In angular frequency the Plancherel unitary differs from the unnormalized log
Fourier integral by a single positive constant. -/
private theorem radial_plancherel :
    ∃ (θ : ℝ → PontryaginDual ℝ≥0ˣ) (a : ℝ) (_ : 0 < a)
      (W : Lp ℂ 2 positiveRealHaar ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ)),
      Continuous θ ∧ (∀ (t : ℝ) (x : ℝ≥0ˣ), θ t x = Circle.exp (t * Real.log (x.val : ℝ))) ∧
      ∀ (f : Lp ℂ 2 positiveRealHaar), Integrable (f : ℝ≥0ˣ → ℂ) positiveRealHaar →
        (W f : ℝ → ℂ) =ᵐ[volume] fun t ↦ (a : ℂ) * lcaFourier positiveRealHaar f (θ t) := by
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  let : MeasurableSpace (PontryaginDual ℝ≥0ˣ) := borel _
  let : BorelSpace (PontryaginDual ℝ≥0ˣ) := ⟨rfl⟩
  let : positiveRealHaar.IsHaarMeasure := positiveRealHaar_isHaarMeasure
  let : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let h := (Nonneg.unitsHomeomorphPos ℝ).trans Real.expOrderIso.toHomeomorph.symm
  let : LocallyCompactSpace ℝ≥0ˣ := h.isOpenEmbedding.locallyCompactSpace
  let μ : Measure (Multiplicative ℝ) := (volume : Measure ℝ)
  let hv : (volume : Measure ℝ).IsAddHaarMeasure := inferInstance
  let : μ.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := hv.toIsFiniteMeasureOnCompacts
      toIsOpenPosMeasure := hv.toIsOpenPosMeasure
      map_mul_left_eq_self := fun x ↦ hv.map_add_left_eq_self x.toAdd }
  obtain ⟨e, he⟩ := radial_characters
  obtain ⟨ν, hν, _⟩ := lcaPlancherelMeasure_existsUnique positiveRealHaar
  let : ν.IsHaarMeasure := hν.1
  let ρ := ν.map (e.symm : PontryaginDual ℝ≥0ˣ → Multiplicative ℝ)
  let : ρ.IsHaarMeasure := e.symm.isHaarMeasure_map ν
  let c := Measure.haarScalarFactor ρ μ
  have hc : 0 < c := Measure.haarScalarFactor_pos_of_isHaarMeasure _ _
  have hρ : ρ = c • μ := Measure.isMulLeftInvariant_eq_smul _ _
  have hρ' : μ.withDensity (fun _ ↦ (c : ℝ≥0∞)) = ρ := (withDensity_const _).trans hρ.symm
  have hμ : μ ≪ ρ := Measure.absolutelyContinuous_isHaarMeasure μ ρ
  obtain ⟨F, hF, _⟩ := lcaFourier_unitary positiveRealHaar ν hν
  have hsm : MeasurePreserving (e.symm : PontryaginDual ℝ≥0ˣ → Multiplicative ℝ) ν ρ :=
    ⟨e.symm.continuous.measurable, rfl⟩
  have hf : MeasurePreserving (e : Multiplicative ℝ → PontryaginDual ℝ≥0ˣ) ρ ν :=
    hsm.symm e.symm.toHomeomorph.toMeasurableEquiv
  let L : Lp ℂ 2 ν →ₗᵢ[ℂ] Lp ℂ 2 ρ := Lp.compMeasurePreservingₗᵢ ℂ e hf
  have hsur : Surjective L := by
    intro y
    refine ⟨Lp.compMeasurePreserving e.symm hsm y, Lp.ext ?_⟩
    filter_upwards [Lp.coeFn_compMeasurePreserving (Lp.compMeasurePreserving e.symm hsm y) hf,
      hf.quasiMeasurePreserving.ae_eq_comp (Lp.coeFn_compMeasurePreserving y hsm)] with t ha hb
    exact ha.trans (hb.trans (congrArg (fun q ↦ y q) (e.symm_apply_apply t)))
  let J := LinearIsometryEquiv.ofSurjective L hsur
  have hJ (f : Lp ℂ 2 ν) : (J f : Multiplicative ℝ → ℂ) =ᵐ[ρ] (f : _ → ℂ) ∘ e :=
    Lp.coeFn_compMeasurePreserving f hf
  obtain ⟨S, hS⟩ : ∃ S : Lp ℂ 2 ρ ≃ₗᵢ[ℂ] Lp ℂ 2 μ, ∀ v, (S v : Multiplicative ℝ → ℂ) =ᵐ[μ]
      fun t ↦ (Real.sqrt (c : ℝ) : ℂ) * v t := by
    rw [← hρ']
    exact CutoffWindow.exists_unweight_L2 μ (fun _ ↦ c) measurable_const (fun _ ↦ hc)
  refine ⟨fun t ↦ e (Multiplicative.ofAdd t), Real.sqrt (c : ℝ), Real.sqrt_pos.mpr hc,
    F.trans (J.trans S), e.continuous, he, fun f hi ↦ ?_⟩
  have hfp : (F f : PontryaginDual ℝ≥0ˣ → ℂ) =ᵐ[ν] lcaFourier positiveRealHaar f := by
    simpa only [Lp.toLp_coeFn] using hF f hi (Lp.memLp f)
  filter_upwards [hS (J (F f)), hμ.ae_eq (hJ (F f)), hμ.ae_eq (hf.quasiMeasurePreserving.ae_eq_comp hfp)]
    with t hs hj hfu
  change S (J (F f)) t = _
  rw [hs, hj]
  exact congrArg ((Real.sqrt (c : ℝ) : ℂ) * ·) hfu
end

section
open Function Filter MeasureTheory Set
open scoped Topology ENNReal ComplexInnerProductSpace

private theorem coordinate_summable {ι A B : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup B] [NormedSpace ℂ B] (e : ι ≃ ι) (w : A ≃ₗᵢ[ℂ] B)
    (v : lp (fun _ : ι ↦ A) 2) : Memℓp (fun i ↦ w (v (e i))) 2 := by
  apply memℓp_gen
  simp only [w.norm_map]
  exact e.summable_iff.mpr ((lp.memℓp v).summable (by norm_num))

/-- Reindexing a Hilbert sum and applying the same unitary at each index is unitary. -/
private theorem sum_coordinates {ι E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup H] [NormedSpace ℂ H] (σ : ι ≃ ι) (W : E ≃ₗᵢ[ℂ] H) :
    ∃ V : lp (fun _ : ι ↦ E) 2 ≃ₗᵢ[ℂ] lp (fun _ : ι ↦ H) 2, ∀ v i, V v i = W (v (σ i)) := by
  let V (v : lp (fun _ : ι ↦ E) 2) : lp (fun _ : ι ↦ H) 2 := ⟨_, coordinate_summable σ W v⟩
  let L : lp (fun _ : ι ↦ E) 2 →ₗ[ℂ] lp (fun _ : ι ↦ H) 2 :=
    { toFun := V
      map_add' v w := lp.ext (funext fun i ↦ W.map_add _ _)
      map_smul' z v := lp.ext (funext fun i ↦ W.map_smul z _) }
  let A : lp (fun _ : ι ↦ E) 2 →ₗᵢ[ℂ] lp (fun _ : ι ↦ H) 2 :=
    { toLinearMap := L
      norm_map' v := by
        apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
        have hv : HasSum (fun i ↦ ‖v i‖ ^ 2) (‖v‖ ^ 2) := by simpa using lp.hasSum_norm (by norm_num) v
        have hw : HasSum (fun i ↦ ‖V v i‖ ^ 2) (‖V v‖ ^ 2) := by simpa using lp.hasSum_norm (by norm_num) (V v)
        have hs : HasSum (fun i ↦ ‖v (σ i)‖ ^ 2) (‖v‖ ^ 2) := σ.hasSum_iff.mpr hv
        exact hw.unique (hs.congr_fun fun i ↦ congrArg (fun x : ℝ ↦ x ^ 2) (W.norm_map _)) }
  have hA : Surjective A := by
    intro v
    refine ⟨⟨_, coordinate_summable σ.symm W.symm v⟩, lp.ext (funext fun i ↦ ?_)⟩
    change W (W.symm (v (σ.symm (σ i)))) = v i
    rw [σ.symm_apply_apply, W.apply_symm_apply]
  exact ⟨LinearIsometryEquiv.ofSurjective A hA, fun _ _ ↦ rfl⟩

section
variable {ι H Y : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
/-- Testing the adjoint against vectors supported in one coordinate gives the adjoint
of that coordinate operator. -/
private theorem adjoint_coordinates (U : H ≃ₗᵢ[ℂ] lp (fun _ : ι ↦ Y) 2) (A : H →L[ℂ] H)
    (M : ι → Y →L[ℂ] Y) (hA : ∀ v i, U (A v) i = M i (U v i)) :
    ∀ v i, U (A.adjoint v) i = (M i).adjoint (U v i) := by
  classical
  intro v i
  apply ext_inner_left ℂ
  intro z
  let y := U.symm (lp.single 2 i z)
  have hy : U y = lp.single 2 i z := U.apply_symm_apply _
  have hAy : U (A y) = lp.single 2 i (M i z) := by
    apply lp.ext
    funext j
    change U (A y) j = _
    rw [hA, hy]
    by_cases h : j = i
    · subst j; simp
    · simp [h]
  calc
    inner ℂ z (U (A.adjoint v) i) = inner ℂ (lp.single 2 i z) (U (A.adjoint v)) :=
      (lp.inner_single_left i z (U (A.adjoint v))).symm
    _ = inner ℂ y (A.adjoint v) := by rw [← hy, U.inner_map_map]
    _ = inner ℂ (A y) v := A.adjoint_inner_right _ _
    _ = inner ℂ (U (A y)) (U v) := (U.inner_map_map _ _).symm
    _ = inner ℂ z ((M i).adjoint (U v i)) := by
      rw [hAy, lp.inner_single_left, ContinuousLinearMap.adjoint_inner_right]
end

/-- Both a bounded scalar multiplier and its adjoint have their pointwise
representatives on L² for arbitrary input classes. -/
private theorem scalar_multipliers {X : Type*} [MeasurableSpace X] (ν : Measure X) (b : X → ℂ)
    (hb : MemLp b ⊤ ν) : ∃ M : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν,
      (∀ v, (M v : X → ℂ) =ᵐ[ν] fun t ↦ b t * v t) ∧
      (∀ v, (M.adjoint v : X → ℂ) =ᵐ[ν] fun t ↦ star (b t) * v t) := by
  let mult := ContinuousLinearMap.mul ℂ ℂ
  let M := mult.holderL ν (⊤ : ENNReal) 2 2 (hb.toLp _)
  let N := mult.holderL ν (⊤ : ENNReal) 2 2 (hb.star.toLp _)
  have hM (v : Lp ℂ 2 ν) : (M v : X → ℂ) =ᵐ[ν] fun t ↦ b t * v t :=
    (mult.coeFn_holder (r := 2) (hb.toLp _) v).trans (hb.coeFn_toLp.mono fun t ht ↦ congrArg (· * v t) ht)
  have hN (v : Lp ℂ 2 ν) : (N v : X → ℂ) =ᵐ[ν] fun t ↦ star (b t) * v t :=
    (mult.coeFn_holder (r := 2) (hb.star.toLp _) v).trans (hb.star.coeFn_toLp.mono fun t ht ↦ congrArg (· * v t) ht)
  have hn : N = M.adjoint := (ContinuousLinearMap.eq_adjoint_iff N M).mpr fun v u ↦ by
    rw [L2.inner_def, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hN v, hM u] with t hn hm
    change inner ℂ (N v t) (u t) = inner ℂ (v t) (M u t)
    rw [hn, hm]
    simp [RCLike.inner_apply, mul_left_comm, mul_assoc]
  exact ⟨M, hM, fun v ↦ hn ▸ hN v⟩

section
variable {G ι : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
local notation "Y" => Lp ℂ 2 (volume : Measure ℝ)
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
/-- If a unitary agrees with the full Fourier transform at the split characters on
L¹ ∩ L², bounded Haar convolution is a multiplication operator on every component. -/
private theorem adjoint_convolution_coordinates (U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] lp (fun _ : ι ↦ Y) 2)
    (e : ι → ℝ → PontryaginDual G) (he : ∀ i, Continuous (e i)) (c : ℂ)
    (hU : ∀ (v : Lp ℂ 2 μ), Integrable (v : G → ℂ) μ → ∀ i,
      (U v i : ℝ → ℂ) =ᵐ[volume] fun t ↦ c * lcaFourier μ v (e i t))
    (ψ : G → ℂ) (hψ : Integrable ψ μ) (A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hA : ∀ v, (A v : G → ℂ) =ᵐ[μ] lcaConvolution μ ψ v) :
    ∀ v i, (U (A.adjoint v) i : ℝ → ℂ) =ᵐ[volume] fun t ↦ star (lcaFourier μ ψ (e i t)) * U v i t := by
  obtain ⟨f, hf⟩ := lcaFourier_zeroAtInfty μ hψ
  have htop (i : ι) : MemLp (fun t ↦ lcaFourier μ ψ (e i t)) ⊤ (volume : Measure ℝ) := by
    have hm : Continuous (fun t ↦ lcaFourier μ ψ (e i t)) := by
      rw [show (fun t ↦ lcaFourier μ ψ (e i t)) = f.toContinuousMap ∘ e i from
        funext fun t ↦ (hf (e i t)).symm]
      exact f.continuous.comp (he i)
    exact memLp_top_of_bound hm.aestronglyMeasurable ‖f.toBCF‖
      (.of_forall fun t ↦ (hf (e i t)) ▸ f.toBCF.norm_coe_le_norm _)
  choose M hM hMa using fun i ↦ scalar_multipliers (volume : Measure ℝ) _ (htop i)
  let D := {v : Lp ℂ 2 μ | Integrable (v : G → ℂ) μ}
  have hd : Dense D := by
    apply (Lp.simpleFunc.dense (E := ℂ) (p := 2) (μ := μ) ENNReal.ofNat_ne_top).mono
    intro v hv
    let g : Lp.simpleFunc ℂ 2 μ := ⟨v, hv⟩
    have hh : Integrable (Lp.simpleFunc.toSimpleFunc g) μ :=
      (SimpleFunc.memLp_iff_integrable two_ne_zero ENNReal.ofNat_ne_top).mp (Lp.simpleFunc.memLp g)
    exact hh.congr (Lp.simpleFunc.toSimpleFunc_eq_toFun g)
  have hdg (v : Lp ℂ 2 μ) (i : ι) : U (A v) i = M i (U v i) := by
    let p := lp.evalCLM ℂ (fun _ : ι ↦ Y) 2 i
    apply ((isClosed_eq (p.continuous.comp (U.continuous.comp A.continuous))
      ((M i).continuous.comp (p.continuous.comp U.continuous))).closure_subset_iff.mpr ?_) (hd v)
    intro g hg
    have hi : Integrable (A g : G → ℂ) μ := (lcaConvolution_integrable μ hψ hg).2.1.congr (hA g).symm
    apply Lp.ext
    have hv (χ : PontryaginDual G) : lcaFourier μ (A g) χ = lcaFourier μ (lcaConvolution μ ψ g) χ :=
      integral_congr_ae ((hA g).mono fun x hx ↦ congrArg (· * star (χ x : ℂ)) hx)
    filter_upwards [hU (A g) hi i, hU g hg i, hM i (U g i)] with t h₁ h₂ h₃
    change U (A g) i t = M i (U g i) t
    rw [h₁, h₃, h₂, hv, lcaFourier_convolution μ hψ hg, Pi.mul_apply]
    ring
  intro v i
  rw [adjoint_coordinates U A M hdg]
  exact hMa i _
end
end

section
open Function Filter MeasureTheory Set
open scoped NNReal ENNReal Topology
variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
variable (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m) (μ : Measure G) [hμ : μ.IsHaarMeasure]
    (κ : Measure m.toMonoidHom.ker) [hκ : κ.IsHaarMeasure] (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ m)
include hμ hκ hm hτ
local notation "X" => Lp ℂ 2 μ
local notation "Iκ" => PontryaginDual m.toMonoidHom.ker
local notation "Hκ" => lp (fun _ : Iκ ↦ Lp ℂ 2 (volume : Measure ℝ)) 2
local notation "logM(" x ")" => Real.log ((Units.val (m x) : ℝ≥0) : ℝ)
local notation "phase(" t ", " x ")" => Complex.exp (((t : ℝ) : ℂ) * (-Complex.I * (logM(x) : ℂ)))

/-- In angular log frequency, the compact-character and positive-real Plancherel
unitaries jointly diagonalize the adjoint of any bounded Haar convolution by an L¹
kernel. Every bounded radial multiplier preserves the vanishing of a whole component. -/
private theorem haar_fourier_model
    (hprod : (κ.prod positiveRealHaar).map (fun z : m.toMonoidHom.ker × ℝ≥0ˣ ↦ (z.1 : G) * τ z.2) = μ)
    (ψ : G → ℂ) (hψ : Integrable ψ μ) (B : X →L[ℂ] X)
    (hB : ∀ v, (B v : G → ℂ) =ᵐ[μ] lcaConvolution μ ψ v) :
    ∃ (γ : Iκ → PontryaginDual G) (U : X ≃ₗᵢ[ℂ] Hκ),
      (∀ ω (k : m.toMonoidHom.ker), γ ω k = ω k) ∧
      (∀ v ω, (U (B.adjoint v) ω : ℝ → ℂ) =ᵐ[volume] fun t ↦
        star (∫ x, (ψ x * star (γ ω x : ℂ)) * phase(t, x) ∂μ) * U v ω t) ∧
      ∀ (p : ℝ≥0ˣ → ℂ) (P : X →L[ℂ] X), (∀ v, (P v : G → ℂ) =ᵐ[μ] fun x ↦ p (m x) * v x) →
        ∀ v ω, U v ω = 0 → U (P v) ω = 0 := by
  obtain ⟨γ, hγ, hγτ⟩ := exists_regularIsotypic_sectionCharacters m τ hτ
  obtain ⟨a, ha, V, hV⟩ := normalized_regularIsotypicTransform m hm μ κ τ hτ hprod
  obtain ⟨θ, b, hb, W, hθc, hθ, hW⟩ := radial_plancherel
  obtain ⟨E, hE⟩ := sum_coordinates (Equiv.inv Iκ) W
  let U : X ≃ₗᵢ[ℂ] Hκ := V.trans E
  let T := regularIsotypicTransform m hm μ κ τ hτ
  have hcoord (v : X) (ω : Iκ) : U v ω = (a : ℂ) • W (T v ω⁻¹) := by
    change E (V v) ω = _
    rw [hE, hV]
    exact W.map_smul _ _
  let e (ω : Iκ) (t : ℝ) : PontryaginDual G := γ ω * PontryaginDual.map m (θ t)
  have he (ω : Iκ) : Continuous (e ω) := continuous_const.mul ((PontryaginDual.map m).continuous.comp hθc)
  let c : ℂ := (a : ℂ) * (b : ℂ)
  have huv (v : X) (hi : Integrable (v : G → ℂ) μ) (ω : Iκ) :
      (U v ω : ℝ → ℂ) =ᵐ[volume] fun t ↦ c * lcaFourier μ v (e ω t) := by
    have hF := regularIsotypicTransform_fourier m hm μ κ τ hτ hprod (γ ω) ω (hγ ω) (hγτ ω) v hi
    rw [hcoord]
    filter_upwards [Lp.coeFn_smul (a : ℂ) (W (T v ω⁻¹)), hW (T v ω⁻¹) hF.1] with t hx hy
    change ((a : ℂ) • W (T v ω⁻¹)) t = _
    rw [hx, Pi.smul_apply, smul_eq_mul, hy, hF.2 (θ t)]
    change (a : ℂ) * ((b : ℂ) * lcaFourier μ v (e ω t)) = c * _
    ring
  have hsymbol (ω : Iκ) (t : ℝ) : lcaFourier μ ψ (e ω t) =
      ∫ x, (ψ x * star (γ ω x : ℂ)) * phase(t, x) ∂μ := by
    apply integral_congr_ae
    filter_upwards with x
    change ψ x * star ((γ ω x * θ t (m x) : Circle) : ℂ) = _
    have hc : star (θ t (m x) : ℂ) = phase(t, x) := by
      change (starRingEnd ℂ) (θ t (m x) : ℂ) = _
      rw [hθ, Circle.coe_exp, ← Complex.exp_conj]
      congr 1
      push_cast
      simp [mul_comm, mul_left_comm]
    rw [Circle.coe_mul, star_mul', hc]
    ring
  refine ⟨γ, U, hγ, fun v ω ↦ ?_, fun p P hP v ω hv ↦ ?_⟩
  · have h := adjoint_convolution_coordinates μ U e he c huv ψ hψ B hB v ω
    simpa only [hsymbol] using h
  · have ha' : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
    have hzero : T v ω⁻¹ = 0 := by
      rw [hcoord] at hv
      exact W.injective ((smul_eq_zero.mp hv).resolve_left ha' |>.trans W.map_zero.symm)
    have hPzero : T (P v) ω⁻¹ = 0 := by
      apply Lp.ext
      filter_upwards [regularIsotypicTransform_radial m hm μ κ τ hτ hprod p P hP v ω⁻¹,
        Lp.coeFn_zero ℂ 2 positiveRealHaar] with r hr hz
      change T (P v) ω⁻¹ r = _
      change T (P v) ω⁻¹ r = p r * T v ω⁻¹ r at hr
      rw [hr, hzero, hz, Pi.zero_apply, mul_zero]
    rw [hcoord, hPzero, map_zero, smul_zero]
end

section
open Function Filter MeasureTheory Set
open scoped NNReal ENNReal Topology

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
variable (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m) (μ : Measure G) [hμ : μ.IsHaarMeasure]
    (κ : Measure m.toMonoidHom.ker) [hκ : κ.IsHaarMeasure] (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ m)
variable (w : G → ℝ) (hw : Measurable w) (hp : ∀ x, 0 < w x)
include hμ hκ hm hτ hw hp
local notation "X" => Lp ℂ 2 μ
local notation "H" => Lp ℂ 2 (μ.withDensity fun x ↦ ENNReal.ofReal (w x))
local notation "Iκ" => PontryaginDual m.toMonoidHom.ker
local notation "Hκ" => lp (fun _ : Iκ ↦ Lp ℂ 2 (volume : Measure ℝ)) 2
local notation "d(" x ")" => (Real.sqrt (w x) : ℂ)
local notation "CL(" U ")" =>
  ContinuousLinearEquiv.toContinuousLinearMap (LinearIsometryEquiv.toContinuousLinearEquiv (U))
local notation "phase(" t ", " x ")" => Complex.exp (((t : ℝ) : ℂ) *
  (-Complex.I * (Real.log ((Units.val (m x) : ℝ≥0) : ℝ) : ℂ)))

/-- Multiplication by the square root of the weight restores the Haar Fourier model
for the transported convolution, with the same radial component preservation. -/
private theorem weighted_fourier_model
    (hprod : (κ.prod positiveRealHaar).map (fun z : m.toMonoidHom.ker × ℝ≥0ˣ ↦ (z.1 : G) * τ z.2) = μ)
    (ψ : G → ℂ) (hψ : Integrable ψ μ) (C : H →L[ℂ] H)
    (hC : ∀ v : H, (C v : G → ℂ) =ᵐ[μ] fun x ↦ (d(x))⁻¹ *
      ∫ g, ψ g * (d(g⁻¹ * x) * v (g⁻¹ * x)) ∂μ) :
    ∃ (γ : Iκ → PontryaginDual G) (U : H ≃ₗᵢ[ℂ] Hκ),
      (∀ ω (k : m.toMonoidHom.ker), γ ω k = ω k) ∧
      (∀ v ω, (U (C.adjoint v) ω : ℝ → ℂ) =ᵐ[volume] fun t ↦
        star (∫ x, (ψ x * star (γ ω x : ℂ)) * phase(t, x) ∂μ) * U v ω t) ∧
      ∀ (p : ℝ≥0ˣ → ℂ) (P : H →L[ℂ] H), (∀ v, (P v : G → ℂ) =ᵐ[μ] fun x ↦ p (m x) * v x) →
        ∀ v ω, U v ω = 0 → U (P v) ω = 0 := by
  obtain ⟨J, hJ⟩ : ∃ J : H ≃ₗᵢ[ℂ] X, ∀ v, (J v : G → ℂ) =ᵐ[μ] fun x ↦ d(x) * v x := by
    obtain ⟨J, hJ'⟩ := CutoffWindow.exists_unweight_L2 μ (fun x ↦ (w x).toNNReal) hw.real_toNNReal
      (fun x ↦ Real.toNNReal_pos.mpr (hp x))
    refine ⟨J, fun v ↦ (hJ' v).mono fun x hx ↦ hx.trans ?_⟩
    exact congrArg (fun r : ℝ ↦ (Real.sqrt r : ℂ) * v x) (Real.coe_toNNReal _ (hp x).le)
  let B := CL(J).comp (C.comp CL(J.symm))
  have hB (z : X) : (B z : G → ℂ) =ᵐ[μ] lcaConvolution μ ψ z := by
    let u := J.symm z
    have hzu : (z : G → ℂ) =ᵐ[μ] fun x ↦ d(x) * u x := (J.apply_symm_apply z) ▸ hJ u
    filter_upwards [hJ (C u), hC u] with x hx hc
    change J (C u) x = ∫ g, ψ g * z (g⁻¹ * x) ∂μ
    rw [hx, hc, mul_inv_cancel_left₀ (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hp x)).ne')]
    have hpres : MeasurePreserving (fun g : G ↦ g⁻¹ * x) μ μ :=
      (measurePreserving_mul_right μ x).comp (Measure.measurePreserving_inv μ)
    refine integral_congr_ae ((hpres.quasiMeasurePreserving.ae_eq_comp hzu).mono fun g hg ↦ ?_)
    exact congrArg (ψ g * ·) hg.symm
  have hconj (v : H) : B (J v) = J (C v) := by
    change J (C (J.symm (J v))) = _
    rw [J.symm_apply_apply]
  have hadj (v : H) : J (C.adjoint v) = B.adjoint (J v) := by
    apply ext_inner_left ℂ
    intro y
    obtain ⟨z, rfl⟩ := J.surjective y
    rw [J.inner_map_map, ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_right,
      hconj, J.inner_map_map]
  obtain ⟨γ, V, hγ, hV, hmask⟩ := haar_fourier_model m hm μ κ τ hτ hprod ψ hψ B hB
  refine ⟨γ, J.trans V, hγ, fun v ω ↦ ?_, fun p P hP v ω hv ↦ ?_⟩
  · change (V (J (C.adjoint v)) ω : ℝ → ℂ) =ᵐ[volume] _
    rw [hadj]
    exact hV (J v) ω
  · let Q := CL(J).comp (P.comp CL(J.symm))
    have hQ (z : X) : (Q z : G → ℂ) =ᵐ[μ] fun x ↦ p (m x) * z x := by
      let u := J.symm z
      have hzu : (z : G → ℂ) =ᵐ[μ] fun x ↦ d(x) * u x := (J.apply_symm_apply z) ▸ hJ u
      filter_upwards [hJ (P u), hP u, hzu] with x hx hp hz
      change J (P u) x = _
      rw [hx, hp, hz]
      ring
    have h := hmask p Q hQ (J v) ω hv
    change V (J (P (J.symm (J v)))) ω = 0 at h
    rwa [J.symm_apply_apply] at h
end

section
open Function Filter MeasureTheory Set
open scoped NNReal ENNReal Topology
variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
variable (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m) (μ : Measure G) [hμ : μ.IsHaarMeasure]
  (κ : Measure m.toMonoidHom.ker) [hκ : κ.IsHaarMeasure] (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ m)
include hm hμ hκ hτ
local notation "ell(" x ")" => Real.log ((Units.val (m x) : ℝ≥0) : ℝ)
local notation "den(" a ", " s ", " x ")" => intervalSobolevDensity (-(a)) (a) (s) (ell(x))
local notation "H(" a ", " s ")" => Lp ℂ 2 (μ.withDensity fun x ↦ ENNReal.ofReal (den(a,s,x)))
local notation "d(" a ", " s ", " x ")" => (Real.sqrt (den(a,s,x)) : ℂ)
local notation "Iκ" => PontryaginDual m.toMonoidHom.ker
local notation "Hκ" => lp (fun _ : Iκ ↦ Lp ℂ 2 (volume : Measure ℝ)) 2

/-- Applying the split Fourier model to the interval Sobolev density and an exponentially
tilted compact test gives the weighted symbol and every radial interval mask. -/
private theorem tilted_interval_model
    (hprod : (κ.prod positiveRealHaar).map (fun z : m.toMonoidHom.ker × ℝ≥0ˣ ↦ (z.1 : G) * τ z.2) = μ)
    (α s β : ℝ) (φ : G → ℂ) (hφ : Continuous φ) (hk : HasCompactSupport φ)
    (C : H(α, s) →L[ℂ] H(α, s)) (hC : ∀ v, (C v : G → ℂ) =ᵐ[μ] fun x ↦ d(α, s, x)⁻¹ *
      ∫ g, ((Real.exp (β * ell(g)) : ℂ) * φ g) * (d(α, s, g⁻¹ * x) * v (g⁻¹ * x)) ∂μ) :
    ∃ (γ : Iκ → PontryaginDual G) (U : H(α, s) ≃ₗᵢ[ℂ] Hκ),
      (∀ ω (k : m.toMonoidHom.ker), γ ω k = ω k) ∧
      (∀ v ω, (U (C.adjoint v) ω : ℝ → ℂ) =ᵐ[volume] fun t ↦
        (starRingEnd ℂ) (∫ g, (φ g * (starRingEnd ℂ) (γ ω g : ℂ) * (Real.exp (β * ell(g)) : ℂ)) *
          Complex.exp ((t : ℂ) * (-Complex.I * (ell(g) : ℂ))) ∂μ) * U v ω t) ∧
      ∀ (I : Set ℝ) [DecidablePred (· ∈ I)], MeasurableSet I → OrdConnected I →
        ∀ (P : H(α, s) →L[ℂ] H(α, s)), (∀ v, (P v : G → ℂ) =ᵐ[μ] fun x ↦
          ((if ell(x) ∈ I then 1 else 0 : ℝ) : ℂ) * v x) → ∀ v ω, U v ω = 0 → U (P v) ω = 0 := by
  have hl : Continuous (fun x : G ↦ ell(x)) :=
    (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)).log fun x ↦
      NNReal.coe_ne_zero.mpr (m x).ne_zero
  have hw : Measurable (fun x : G ↦ den(α, s, x)) := by
    have h : Measurable (intervalSobolevDensity (-α) α s) := by unfold intervalSobolevDensity; fun_prop
    exact h.comp hl.measurable
  have hp (x : G) : 0 < den(α, s, x) :=
    mul_pos (lt_max_of_lt_left (Real.exp_pos _)) (Real.rpow_pos_of_pos (by positivity) _)
  let ψ (x : G) : ℂ := (Real.exp (β * ell(x)) : ℂ) * φ x
  have hψ : Continuous ψ := (Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul hl))).mul hφ
  have hψk : HasCompactSupport ψ := hk.mul_left
  obtain ⟨γ, U, hγ, hU, hP⟩ := weighted_fourier_model m hm μ κ τ hτ (fun x ↦ den(α, s, x)) hw hp hprod
    ψ (hψ.integrable_of_hasCompactSupport hψk) C hC
  refine ⟨γ, U, hγ, fun v ω ↦ ?_, fun I _ _ _ P hPv ↦ ?_⟩
  · refine (hU v ω).mono fun t ht ↦ ht.trans (congrArg (fun z : ℂ ↦ (starRingEnd ℂ) z * U v ω t) ?_)
    apply integral_congr_ae
    filter_upwards with x
    dsimp only [ψ]
    change ((Real.exp (β * ell(x)) : ℂ) * φ x) * (starRingEnd ℂ) (γ ω x : ℂ) * _ = _
    ring
  · exact hP (fun a ↦ ((if Real.log (a.val : ℝ) ∈ I then 1 else 0 : ℝ) : ℂ)) P hPv
end

end CutoffSplit

section CutoffWindowLimits

local notation "WOp" => W₀ →L[ℂ] W₀
local notation "WU" => W₀ ≃ₗᵢ[ℂ] W₀
local notation "CL(" U ")" => (U).toContinuousLinearEquiv.toContinuousLinearMap
local notation "weight(" x ")" => intervalSobolevDensity (-α) α s (logNorm x)
local notation "sqrtW(" x ")" => ((Real.sqrt (weight(x))) : ℂ)
local notation "shift(" j ", " g ")" => (if (j : Bool) then g else (g)⁻¹)
local notation "signed(" j ", " x ")" => (if (j : Bool) then (x : ℝ) else (-x : ℝ))
local notation "tilted(" φ ", " j ", " v ", " x ")" =>
  (sqrtW(x))⁻¹ * ∫ g, (((Real.exp (signed(j, α) * logNorm g)) : ℂ) * (φ : BruhatCompactSupport C𝔽).val g) *
     (sqrtW(g⁻¹ * x) * (v : W₀) (g⁻¹ * x)) ∂μ𝔽
local notation "weightedHaar" => ((μ𝔽).withDensity fun x : C𝔽 ↦ ENNReal.ofReal (weight(x)))
local notation "centred(" d ", " x ")" => ((if |logNorm x| ≤ d then 1 else 0 : ℝ) : ℂ)
/-- A choice of norm section at positive radii tends to infinity with its radius. -/
private theorem spectralRestriction_cutoff_positive_section :
    ∃ u : ℝ → C𝔽, ∀ᶠ R in atTop, ((m𝔽 (u R)).val : ℝ) = R := by
  classical
  have hsur : Surjective m𝔽 := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.2.2.2.1
  let u (R : ℝ) : C𝔽 := if h : 0 < R then
    (hsur (Units.mk0 R.toNNReal (Real.toNNReal_pos.mpr h).ne')).choose else 1
  have hu : ∀ᶠ R in atTop, ((m𝔽 (u R)).val : ℝ) = R := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    have h := (hsur (Units.mk0 R.toNNReal (Real.toNNReal_pos.mpr hR).ne')).choose_spec
    simp only [u, dite_eq_left hR, h, Units.val_mk0, Real.coe_toNNReal _ hR.le]
  exact ⟨u, hu⟩

/-- Haar measure and the measure defined by the strictly positive Sobolev density
have the same null sets. -/
private theorem spectralRestriction_cutoff_measure_equivalence :
    μ𝔽 ≪ weightedHaar ∧ weightedHaar ≪ μ𝔽 := by
  have hlog : Continuous (logNorm : C𝔽 → ℝ) :=
    (NNReal.continuous_coe.comp (Units.continuous_val.comp (m𝔽).continuous)).log fun x ↦
      NNReal.coe_ne_zero.mpr (m𝔽 x).ne_zero
  have hw : Measurable (fun x : C𝔽 ↦ weight(x)) := by
    have h : Measurable (intervalSobolevDensity (-α) α s) := by unfold intervalSobolevDensity; fun_prop
    exact h.comp hlog.measurable
  have hp (x : C𝔽) : 0 < weight(x) :=
    mul_pos (lt_max_of_lt_left (Real.exp_pos _)) (Real.rpow_pos_of_pos (by positivity) _)
  have hν : weightedHaar ≪ μ𝔽 := withDensity_absolutelyContinuous ..
  have hμ : μ𝔽 ≪ weightedHaar := withDensity_absolutelyContinuous' hw.ennreal_ofReal.aemeasurable
    (.of_forall fun x ↦ (ENNReal.ofReal_pos.mpr (hp x)).ne')
  exact ⟨hμ, hν⟩

/-- The density-normalized translations on the ambient Sobolev space are unitaries;
their inverses escape weakly when their group parameter escapes every compact set. -/
private theorem spectralRestriction_cutoff_normalized_shifts :
    ∃ T : C𝔽 → WU, (∀ g v, (T g v : C𝔽 → ℂ) =ᵐ[μ𝔽] fun x ↦
      (sqrtW(g⁻¹ * x) / sqrtW(x)) * v (g⁻¹ * x)) ∧
      ∀ v (f : StrongDual ℂ W₀), Tendsto (fun g ↦ f ((T g).symm v)) (cocompact C𝔽) (𝓝 0) := by
  have hlog : Continuous (logNorm : C𝔽 → ℝ) :=
    (NNReal.continuous_coe.comp (Units.continuous_val.comp (m𝔽).continuous)).log fun x ↦
      NNReal.coe_ne_zero.mpr (m𝔽 x).ne_zero
  have hw : Measurable (fun x : C𝔽 ↦ weight(x)) := by
    have h : Measurable (intervalSobolevDensity (-α) α s) := by unfold intervalSobolevDensity; fun_prop
    exact h.comp hlog.measurable
  have hp (x : C𝔽) : 0 < weight(x) :=
    mul_pos (lt_max_of_lt_left (Real.exp_pos _)) (Real.rpow_pos_of_pos (by positivity) _)
  exact CutoffWindow.weighted_escaping_real (G := C𝔽) μ𝔽 _ hw hp

/-- Paper: Theorem 10.4.2.8, pp. 463–464. After translation to one end of a symmetric strip
the ambient convolution tends strongly to its exponential tilt. On a fixed bounded logarithmic
window the compressed kernels converge in trace norm.
Deviation: This is a sufficient local kernel estimate for the unfinished cutoff argument. The square-root
density transports the ordinary Haar convolution back to the given weighted space. -/
private theorem spectralRestriction_tiltedConvolution_window_limit (φ : BruhatCompactSupport C𝔽)
    (u : ℝ → C𝔽) (hu : ∀ᶠ R in atTop, ((m𝔽 (u R)).val : ℝ) = R) (j : Bool)
    (U : C𝔽 → WU) (hU : ∀ g v, (U g v : C𝔽 → ℂ) =ᵐ[μ𝔽] fun x ↦
      (sqrtW(g⁻¹ * x) / sqrtW(x)) * v (g⁻¹ * x))
    (d : ℝ) (hd : 0 < d) (S : WOp) (hS : ∀ v, (S v : C𝔽 → ℂ) =ᵐ[μ𝔽]
      fun x ↦ centred(d, x) * v x) :
    let A : WOp := A(φ)
    let T (R : ℝ) := U (shift(j, u R))
    ∃ (C : WOp) (J : nuclearEndomorphisms W₀) (K : ℝ → nuclearEndomorphisms W₀),
      (∀ v, (C v : C𝔽 → ℂ) =ᵐ[μ𝔽] fun x ↦ tilted(φ, j, v, x)) ∧
      (∀ v, Tendsto (fun R ↦ (T R).symm (A (T R v))) atTop (𝓝 (C v))) ∧
      J.val = S * C * S ∧
      (∀ᶠ R in atTop, (K R).val = S * (CL((T R).symm) * A * CL(T R)) * S) ∧
      Tendsto (fun R ↦ traceNorm (K R - J)) atTop (𝓝 0) := by
  have hm : IsModulation m𝔽 := ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
  have hsur : Surjective m𝔽 := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.2.2.2.1
  have hc := continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp φ.property.1)
  exact CutoffActualLimit.actual_tilted_window_limit m𝔽 μ𝔽 hm hsur α s hα hs (hStrip(hα))
    φ hc u hu j U hU d hd S hS

local notation "kernelChars" => PontryaginDual ((m𝔽).toMonoidHom.ker)
local notation "charModel" => lp (fun _ : kernelChars ↦ Lp ℂ 2 (volume : Measure ℝ)) 2
local notation "charAmp(" φ ", " γ ", " j ", " x ")" =>
  ((φ : BruhatCompactSupport C𝔽).val x * (starRingEnd ℂ) ((γ : PontryaginDual C𝔽) x : ℂ)
    * (Real.exp (signed(j, α) * logNorm x) : ℂ))
local notation "charSymbol(" φ ", " γ ", " j ", " ξ ")" =>
  ∫ x, charAmp(φ, γ, j, x) * Complex.exp (((ξ : ℝ) : ℂ) * (-Complex.I * (logNorm x : ℂ))) ∂μ𝔽

/-- Paper: Theorem 10.4.2.8, pp. 463–464. In split Haar coordinates the compact-character
and logarithmic Fourier transforms diagonalize the adjoint of the fixed tilted convolution.
A physical radial interval mask preserves every compact-character component.
Deviation: The transform is normalized unitarily; logarithmic frequency is angular frequency. -/
private theorem spectralRestriction_tiltedConvolution_fourier_model (φ : BruhatCompactSupport C𝔽)
    (j : Bool) (C : WOp) (hC : ∀ v, (C v : C𝔽 → ℂ) =ᵐ[μ𝔽] fun x ↦ tilted(φ, j, v, x)) :
    ∃ (γ : kernelChars → PontryaginDual C𝔽) (U : W₀ ≃ₗᵢ[ℂ] charModel),
      (∀ ω (k : (m𝔽).toMonoidHom.ker), γ ω k = ω k) ∧
      (∀ v ω, (U (C.adjoint v) ω : ℝ → ℂ) =ᵐ[volume]
        fun t ↦ (starRingEnd ℂ) (charSymbol(φ, γ ω, j, t)) * U v ω t) ∧
      ∀ (I : Set ℝ) [DecidablePred (· ∈ I)], MeasurableSet I → OrdConnected I →
        ∀ (P : WOp), (∀ y, (P y : C𝔽 → ℂ) =ᵐ[μ𝔽] fun x ↦
          ((if logNorm x ∈ I then 1 else 0 : ℝ) : ℂ) * y x) →
        ∀ v ω, U v ω = 0 → U (P v) ω = 0 := by
  let q : (AdeleRing (𝓞 F) F)ˣ →ₜ* C𝔽 := ⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩
  let τ : ℝ≥0ˣ →ₜ* C𝔽 := q.comp ⟨canonicalIdeleNormSection F, canonicalIdeleNormSection_continuous F⟩
  have hτ : RightInverse τ (ideleClassNorm F) := canonicalIdeleNormSection_rightInverse F
  let : (normOneIdeleClassTamagawaMeasure F).IsHaarMeasure :=
    (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  have hm : IsModulation m𝔽 := ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
  have hφ := continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp φ.property.1)
  exact CutoffSplit.tilted_interval_model m𝔽 hm μ𝔽 (normOneIdeleClassTamagawaMeasure F) τ hτ
    (geometricTruncatedConvolution_trace_remainder_tendsto_normProduct F τ hτ).symm
    α s (signed(j, α)) φ.val hφ φ.property.2 C hC

/-- The logarithmic Fourier symbol of the actual tilted test is real analytic. -/
private theorem spectralRestriction_tiltedConvolution_symbol_analytic (φ : BruhatCompactSupport C𝔽)
    (γ : PontryaginDual C𝔽) (j : Bool) :
    AnalyticOnNhd ℝ (fun t : ℝ ↦ charSymbol(φ, γ, j, t)) univ := by
  let f (x : C𝔽) : ℂ := charAmp(φ, γ, j, x)
  let L (x : C𝔽) : ℂ := -Complex.I * (logNorm x : ℂ)
  have hlog : Continuous (logNorm : C𝔽 → ℝ) :=
    (NNReal.continuous_coe.comp (Units.continuous_val.comp (m𝔽).continuous)).log fun x ↦
      NNReal.coe_ne_zero.mpr (m𝔽 x).ne_zero
  have hφ : Continuous φ.val := continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp φ.property.1)
  have hγ : Continuous fun x : C𝔽 ↦ (γ x : ℂ) := continuous_subtype_val.comp γ.continuous
  have hf : Continuous f := (hφ.mul hγ.star).mul
    (Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul hlog)))
  have hfK : HasCompactSupport f :=
    ((φ.property.2.mul_right : HasCompactSupport (fun x : C𝔽 ↦ φ.val x * (starRingEnd ℂ) (γ x : ℂ))).mul_right)
  have hL : Continuous L := continuous_const.mul (Complex.continuous_ofReal.comp hlog)
  have hd := CutoffWindow.compact_exponential_integral_entire μ𝔽 f L hf hfK hL
  intro t _
  exact (hd.analyticAt (t : ℂ)).restrictScalars.comp (Complex.ofRealCLM.analyticAt t)

/-- Radial interval masks preserve the closed range because an active compact character
has a nonzero logarithmic Fourier multiplier almost everywhere. -/
private theorem spectralRestriction_tiltedConvolution_radial_range (φ : BruhatCompactSupport C𝔽)
    (j : Bool) (C : WOp) (hC : ∀ v, (C v : C𝔽 → ℂ) =ᵐ[μ𝔽] fun x ↦ tilted(φ, j, v, x))
    (I : Set ℝ) [DecidablePred (· ∈ I)] (hI : MeasurableSet I) (hord : OrdConnected I) (P : WOp)
    (hP : ∀ v, (P v : C𝔽 → ℂ) =ᵐ[μ𝔽] fun x ↦
      ((if logNorm x ∈ I then 1 else 0 : ℝ) : ℂ) * v x) :
    ∀ v ∈ closure (range C), P v ∈ closure (range C) := by
  obtain ⟨γ, U, _, hU, hmask⟩ := spectralRestriction_tiltedConvolution_fourier_model φ j C hC
  have hν : weightedHaar ≪ μ𝔽 := withDensity_absolutelyContinuous ..
  have hPa := CutoffWindow.multiplier_selfadjoint weightedHaar
    (fun x : C𝔽 ↦ if logNorm x ∈ I then (1 : ℝ) else 0) P (fun y ↦ hν.ae_eq (hP y))
  exact CutoffWindow.closed_range_of_character_decomposition C P hPa U _
    (fun ω ↦ spectralRestriction_tiltedConvolution_symbol_analytic φ (γ ω) j) hU (hmask I hI hord P hP)

/-- The concrete local convolution and Fourier statements provide the two inputs
to the finite-rank window argument at arbitrary tolerance. -/
private theorem spectralRestriction_tiltedConvolution_window_data (φ : BruhatCompactSupport C𝔽)
    (u : ℝ → C𝔽) (hu : ∀ᶠ R in atTop, ((m𝔽 (u R)).val : ℝ) = R)
    (T : C𝔽 → WU) (ht : ∀ g v, (T g v : C𝔽 → ℂ) =ᵐ[μ𝔽] fun x ↦
      (sqrtW(g⁻¹ * x) / sqrtW(x)) * v (g⁻¹ * x))
    (d : ℝ) (hd : 0 < d) (S : WOp) (hS : ∀ v, (S v : C𝔽 → ℂ) =ᵐ[μ𝔽]
      fun x ↦ centred(d, x) * v x) (j : Bool) :
    let A : WOp := A(φ)
    ∃ (C : WOp) (J : nuclearEndomorphisms W₀) (K : ℝ → nuclearEndomorphisms W₀),
      (∀ (I : Set ℝ) [DecidablePred (· ∈ I)], MeasurableSet I → OrdConnected I →
        ∀ (P : WOp), (∀ v, (P v : C𝔽 → ℂ) =ᵐ[μ𝔽] fun x ↦
          ((if logNorm x ∈ I then 1 else 0 : ℝ) : ℂ) * v x) →
          ∀ v ∈ closure (range C), P v ∈ closure (range C)) ∧
      (∀ v, Tendsto (fun R ↦ (T (shift(j, u R))).symm (A (T (shift(j, u R)) v))) atTop (𝓝 (C v))) ∧
      J.val = S * C * S ∧ (∀ᶠ R in atTop, (K R).val = S *
        (CL((T (shift(j, u R))).symm) * A * CL(T (shift(j, u R)))) * S) ∧
      Tendsto (fun R ↦ traceNorm (K R - J)) atTop (𝓝 0) := by
  intro A
  have h := spectralRestriction_tiltedConvolution_window_limit hα hs φ u hu j T ht d hd S hS
  refine h.imp fun C hc ↦ hc.imp fun J hJ ↦ hJ.imp fun K hK ↦ ⟨?_, hK.2⟩
  intro I instI hI hord P hP
  exact spectralRestriction_tiltedConvolution_radial_range φ j C hK.1 I hI hord P hP


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
        ∃ E : nuclearEndomorphisms W₀, M * A - A * M = A * B R + E.val ∧ traceNorm E < η := by
  classical
  let A : WOp := A(φ)
  have hsur : Surjective m𝔽 := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.2.2.2.1
  have hproper : IsProperMap m𝔽 := isProperMap_ideleClassNorm F
  let u := (spectralRestriction_cutoff_positive_section (F := F)).choose
  have hu := (spectralRestriction_cutoff_positive_section (F := F)).choose_spec
  have hmeas := spectralRestriction_cutoff_measure_equivalence (F := F) (α := α) (s := s)
  let T := (spectralRestriction_cutoff_normalized_shifts (F := F) (α := α) (s := s)).choose
  have hT := (spectralRestriction_cutoff_normalized_shifts (F := F) (α := α) (s := s)).choose_spec
  have hloc := CutoffWindow.hardySobolev_test_commutator_windows m𝔽 μ𝔽 (-α) α s (hStrip(hα)) hs φ
  exact CutoffWindowBridge.commutator_approx m𝔽 μ𝔽 weightedHaar hproper hsur hmeas.1 hmeas.2
    A u hu T _ hT.1 hT.2 ε ρ (_hρ.mono fun _ h ↦ h.1) hloc
    (spectralRestriction_tiltedConvolution_window_data hα hs φ u hu T hT.1) η _hη

end CutoffWindowLimits


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
