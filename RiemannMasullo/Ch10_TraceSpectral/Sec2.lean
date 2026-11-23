module

public import RiemannMasullo.Ch10_TraceSpectral.Sec1
public import RiemannMasullo.AppD_SchwartzBruhat.Sec3a_part2
public import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec1
import RiemannMasullo.ForMathlib.Analysis.Distribution.SchwartzJetClosure
import RiemannMasullo.ForMathlib.Analysis.Fourier.CompactGroup
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.RealDeriv
import all RiemannMasullo.Ch09_HardySobolev.Sec2
import all RiemannMasullo.Ch09_HardySobolev.Sec3

/-!
# Spectral Markushevich bases

Masullo, §10.2, pp. 438–447. The basis vectors in the negative spaces are
represented by functions modulo almost-everywhere equality.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set
open scoped Topology
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false

variable {F : Type*} [Field F] [NumberField F]

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" =>
  (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "logNorm" => (fun g : C𝔽 ↦ Real.log ((ideleClassNorm F g).val : ℝ))
local notation "W(" l ", " r ", " s ")" => CompactIntervalSobolev μ𝔽 logNorm l r s
local notation "W'(" l ", " r ", " s ")" => CompactIntervalSobolev μ𝔽 logNorm l r s true
local notation "Θ(" a ", " hI ", " hs ")" => globalThetaSobolev F a hI hs
local notation "ρ(" l ", " r ", " s ", " hI ", " hs ")" =>
  (hardySobolevTranslation μ𝔽 m𝔽 l r s hI hs).comp (ideleClassNorm F).ker.subtype
local notation "Wω(" hI ", " hs ", " ω ")" => actionIsotype (ρ(_, _, _, hI, hs)) ω
local notation "restriction" =>
  (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁ →ₜ* C𝔽)

local notation "hm𝔽" => (⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ :
  IsModulation m𝔽)
local notation "hms𝔽" => (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.2.2.2.1

section Quotients

/-- Paper: (10.2.1.1), p. 439, and (10.2.2.1), p. 445. The denominator is the
closed subspace from §10.1, giving the canonical norm on the quotient. -/
instance instClosedSpectralThetaSec2 (a : ℝ) {l r s : ℝ} (hI : l ≤ r) (hs : 0 ≤ s) :
    IsClosed (Θ(a, hI, hs) : Set W(l, r, s)) :=
  Submodule.isClosed_topologicalClosure _

/-- Paper: (10.2.1.2), p. 439, and (10.2.2.2), p. 445. The numerator of the
isotype quotient is a closed subspace of the ambient Hilbert space. -/
instance instClosedSpectralIsotypeSec2 {l r s : ℝ} (hI : l ≤ r) (hs : 0 ≤ s)
    (ω : PontryaginDual C₁) : IsClosed (Wω(hI, hs, ω) : Set W(l, r, s)) :=
  isClosed_actionIsotype (ρ(l, r, s, hI, hs)) ω

/-- Paper: (10.2.1.2), p. 439, and (10.2.2.2), p. 445. The isotype quotient
uses the closed intersection of the isotype with the theta subspace. -/
instance instClosedSpectralIsotypeThetaSec2 (a : ℝ) {l r s : ℝ} (hI : l ≤ r)
    (hs : 0 ≤ s) (ω : PontryaginDual C₁) :
    IsClosed ((Θ(a, hI, hs)).comap (Wω(hI, hs, ω)).subtype : Set ↥(Wω(hI, hs, ω))) :=
  (instClosedSpectralThetaSec2 (F := F) a hI hs).preimage continuous_subtype_val

variable (F) in
/-- Paper: (10.2.1.1), p. 439, and (10.2.2.1), p. 445. Divide the weighted
Sobolev space by the closure of the weighted polar-free theta functions.
Deviation: The line uses the compact interval with both endpoints zero, as in §9.2.

Kept as an `abbrev` for now (#5398): as a `def` with its own instances it breaks proofs and
statements that use it, see the issue. Do not copy this pattern: a new type synonym with
structure is a `def` with its own instances (`AGENTS.md`). -/
abbrev spectralSobolevQuotient (a : ℝ) {l r s : ℝ} (hI : l ≤ r) (hs : 0 ≤ s) :=
  W(l, r, s) ⧸ Θ(a, hI, hs)

/-- Paper: (10.2.1.1), p. 439, and (10.2.2.1), p. 445. A Sobolev vector has
zero spectral class exactly when it is in the closed weighted theta subspace. -/
theorem spectralSobolevQuotient_eq_zero (a : ℝ) {l r s : ℝ} (hI : l ≤ r) (hs : 0 ≤ s)
    (f : W(l, r, s)) : Θ(a, hI, hs).mkQ f = 0 ↔ f ∈ Θ(a, hI, hs) :=
  Submodule.Quotient.mk_eq_zero _

variable (F) in
/-- Paper: (10.2.1.2), p. 439, and (10.2.2.2), p. 445. Divide the ambient
norm-one isotype by its closed weighted theta subspace.

Kept as an `abbrev` for now (#5398): as a `def` with its own instances it breaks proofs and
statements that use it, see the issue. Do not copy this pattern: a new type synonym with
structure is a `def` with its own instances (`AGENTS.md`). -/
abbrev spectralSobolevIsotypeQuotient (a : ℝ) {l r s : ℝ} (hI : l ≤ r) (hs : 0 ≤ s)
    (ω : PontryaginDual C₁) :=
  ↥(Wω(hI, hs, ω)) ⧸ (Θ(a, hI, hs)).comap (Wω(hI, hs, ω)).subtype

/-- Paper: (10.2.1.2), p. 439, and (10.2.2.2), p. 445. The isotype quotient
maps isometrically onto the isotype of the full quotient by inclusion of
representatives. The isotype action is the restriction of the continuous
idele class group action on that quotient. -/
theorem spectralSobolevIsotypeQuotient_isometry (a : ℝ) {l r s : ℝ} (hI : l ≤ r)
    (hs : 0 ≤ s) (ω : PontryaginDual C₁) :
    let N := Θ(a, hI, hs)
    let Q := spectralSobolevQuotient F a hI hs
    let E := Wω(hI, hs, ω)
    ∃ ρQ : C𝔽 →* (Q →L[ℂ] Q),
      (∀ (g : C𝔽) (f : W(l, r, s)),
        ρQ g (N.mkQ f) = N.mkQ (hardySobolevTranslation μ𝔽 m𝔽 l r s hI hs g f)) ∧
      Continuous (fun p : C𝔽 × Q ↦ ρQ p.1 p.2) ∧
      ∃ U : spectralSobolevIsotypeQuotient F a hI hs ω ≃ₗᵢ[ℂ]
          actionIsotype (ρQ.comp (ideleClassNorm F).ker.subtype) ω,
        ∀ f : E, (U ((N.comap E.subtype).mkQ f) : Q) = N.mkQ f.val := by sorry

/-- Paper: (10.2.1.3), pp. 439–440, and (10.2.2.3), p. 445. The Sobolev
duality evaluates the unweighted bilinear product integral. -/
def spectralSobolevPairing {l r s : ℝ} (f : W(l, r, s)) (u : W'(l, r, s)) : ℂ :=
  ∫ g, f g * u g ∂μ𝔽

local notation "pair(" f ", " u ")" => spectralSobolevPairing (F := F) f u

local notation "T(" l ", " r ", " s ", " hI ", " hs ")" =>
  (modulatedIntervalSobolev_dual m𝔽 hm𝔽 μ𝔽 l r s hI hs).exists.choose

/-- Paper: (10.2.1.3), p. 440, and (10.2.2.3), p. 445. The pairing is
integrable and evaluates the ambient strong dual under its Sobolev isometry. -/
theorem spectralSobolevPairing_dual {l r s : ℝ} (hI : l ≤ r) (hs : 0 ≤ s)
    (Λ : StrongDual ℂ W(l, r, s)) (f : W(l, r, s)) :
    let T := T(l, r, s, hI, hs)
    Integrable (fun g ↦ f g * T Λ g) μ𝔽 ∧ Λ f = pair(f, T Λ) := by
  exact (modulatedIntervalSobolev_dual m𝔽 hm𝔽 μ𝔽 l r s hI hs).exists.choose_spec Λ f

/-- Conjugating a weighted L² vector and multiplying by the density gives a vector of the
reciprocal-weight space whose product integral with the original is its squared norm. -/
private theorem spectralSobolevPairing_isotype_conj {X : Type*} [MeasurableSpace X] (ν : Measure X)
    {ρ ρ' : X → ℝ} (hρ : Measurable ρ) (hρ' : Measurable ρ') (hpos : ∀ x, 0 < ρ x)
    (hpos' : ∀ x, 0 < ρ' x) (hr : ∀ x, ρ x * ρ' x = 1)
    (f : Lp ℂ 2 (ν.withDensity fun x ↦ ENNReal.ofReal (ρ x))) :
    ∃ g : Lp ℂ 2 (ν.withDensity fun x ↦ ENNReal.ofReal (ρ' x)),
      (g : X → ℂ) =ᵐ[ν] (fun x ↦ (ρ x : ℂ) * star (f x)) ∧
      ∫ x, f x * g x ∂ν = ((‖f‖ ^ 2 : ℝ) : ℂ) := by
  have hbase {ρ : X → ℝ} (hρ : Measurable ρ) (hpos : ∀ x, 0 < ρ x) :
      ν ≪ ν.withDensity fun x ↦ ENNReal.ofReal (ρ x) :=
    withDensity_absolutelyContinuous' hρ.ennreal_ofReal.aemeasurable
      (ae_of_all _ fun x ↦ (ENNReal.ofReal_pos.mpr (hpos x)).ne')
  let u : X → ℂ := fun x ↦ (ρ x : ℂ) * star (f x)
  have hsq (x : X) : ‖u x‖ ^ 2 * ρ' x = ‖f x‖ ^ 2 * ρ x := by
    calc
      _ = ‖f x‖ ^ 2 * (ρ x * (ρ x * ρ' x)) := by
        dsimp only [u]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hpos x), norm_star]
        ring
      _ = _ := by rw [hr, mul_one]
  have hmeas : AEStronglyMeasurable u (ν.withDensity fun x ↦ ENNReal.ofReal (ρ' x)) :=
    (Complex.measurable_ofReal.comp hρ).aestronglyMeasurable.mul
      (((Lp.aestronglyMeasurable f).mono_ac (hbase hρ hpos)).mono_ac
        (withDensity_absolutelyContinuous _ _)).star
  have hmem : MemLp u 2 (ν.withDensity fun x ↦ ENNReal.ofReal (ρ' x)) := by
    apply (memLp_two_iff_integrable_sq_norm hmeas).2
    apply (integrable_withDensity_iff hρ'.ennreal_ofReal
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)).2
    refine (weightedL2_norm_eq ν hρ hpos f).1.congr (ae_of_all _ fun x ↦ ?_)
    change ‖f x‖ ^ 2 * ρ x = ‖u x‖ ^ 2 * (ENNReal.ofReal (ρ' x)).toReal
    rw [ENNReal.toReal_ofReal (hpos' x).le, hsq]
  have hcoe : (hmem.toLp u : X → ℂ) =ᵐ[ν] u := (hbase hρ' hpos').ae_eq hmem.coeFn_toLp
  refine ⟨hmem.toLp u, hcoe, ?_⟩
  obtain ⟨hint, hnorm⟩ := weightedL2_norm_eq ν hρ hpos f
  have hI : ∫ x, ‖f x‖ ^ 2 * ρ x ∂ν = ‖f‖ ^ 2 := by
    rw [hnorm, Real.sq_sqrt (integral_nonneg fun x ↦ mul_nonneg (sq_nonneg _) (hpos x).le)]
  rw [← hI, ← integral_complex_ofReal]
  refine integral_congr_ae ?_
  filter_upwards [hcoe] with x hx
  rw [hx]
  dsimp only [u]
  rw [Complex.star_def, Complex.ofReal_mul, Complex.ofReal_pow, ← Complex.mul_conj']
  ring

/-- Paper: (10.2.1.3), p. 440, and (10.2.2.3), p. 445. The pairing on a
positive Sobolev isotype and the conjugate reciprocal-weight isotype is nondegenerate.
The negative-space isotype is specified by left translation of its representatives. -/
theorem spectralSobolevPairing_isotype {l r s : ℝ} (hI : l ≤ r) (hs : 0 ≤ s)
    (ω : PontryaginDual C₁) :
    let IsConjugate (u : W'(l, r, s)) :=
      ∀ k : C₁, (fun g ↦ u (k.val⁻¹ * g)) =ᵐ[μ𝔽] fun g ↦ (ω⁻¹ k : ℂ) * u g
    (∀ f : Wω(hI, hs, ω), f ≠ 0 →
      ∃ u : W'(l, r, s), IsConjugate u ∧ pair(f.val, u) ≠ 0) ∧
    ∀ u : W'(l, r, s), IsConjugate u → u ≠ 0 →
      ∃ f : Wω(hI, hs, ω), pair(f.val, u) ≠ 0 := by
  intro IsConjugate
  let w : C𝔽 → ℝ := fun g ↦ intervalSobolevDensity l r s (logNorm g)
  have hlog : Measurable logNorm :=
    (NNReal.continuous_coe.comp (Units.continuous_val.comp
      (isProperMap_ideleClassNorm F).continuous)).measurable.log
  have hw : Measurable w := (continuous_intervalSobolevDensity' l r s).measurable.comp hlog
  have hwpos : ∀ x, 0 < w x := fun x ↦ intervalSobolevDensity_pos l r s _
  have hwk : ∀ (k : C₁) g, w (k.val⁻¹ * g) = w g := by
    intro k g
    have hk : ideleClassNorm F k.val = 1 := k.2
    simp only [w, map_mul, map_inv, hk, inv_one, one_mul]
  have hbase : μ𝔽 ≪ (μ𝔽).withDensity (fun x ↦ ENNReal.ofReal (w x)) :=
    withDensity_absolutelyContinuous' hw.ennreal_ofReal.aemeasurable
      (ae_of_all _ fun x ↦ (ENNReal.ofReal_pos.mpr (hwpos x)).ne')
  have hwd : ((μ𝔽).withDensity fun x ↦ ENNReal.ofReal (w x)) ≪ μ𝔽 :=
    withDensity_absolutelyContinuous _ _
  have hiso (f : W(l, r, s)) : f ∈ Wω(hI, hs, ω) ↔
      ∀ k : C₁, (fun g ↦ f (k.val⁻¹ * g)) =ᵐ[μ𝔽] fun g ↦ (ω k : ℂ) * f g := by
    rw [mem_actionIsotype]
    refine forall_congr' fun k ↦ ?_
    have htr := hardySobolevTranslation_apply μ𝔽 m𝔽 l r s hI hs k.val f
    have hsm := hbase.ae_eq (Lp.coeFn_smul (ω k : ℂ) f)
    change hardySobolevTranslation μ𝔽 m𝔽 l r s hI hs k.val f = (ω k : ℂ) • f ↔ _
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
  refine ⟨fun f hf ↦ ?_, fun u hu hu0 ↦ ?_⟩
  · obtain ⟨u, hu, hpair⟩ : ∃ u : W'(l, r, s),
        (u : C𝔽 → ℂ) =ᵐ[μ𝔽] (fun x ↦ (w x : ℂ) * star (f.val x)) ∧
        ∫ x, f.val x * u x ∂μ𝔽 = ((‖f.val‖ ^ 2 : ℝ) : ℂ) :=
      spectralSobolevPairing_isotype_conj μ𝔽 (ρ := w) (ρ' := fun x ↦ (w x)⁻¹) hw hw.inv hwpos
        (fun x ↦ inv_pos.2 (hwpos x)) (fun x ↦ mul_inv_cancel₀ (hwpos x).ne') f.val
    refine ⟨u, fun k ↦ ?_, ?_⟩
    · have hfk := (hiso f.val).1 f.2 k
      have hu' := (hqmp k).ae_eq_comp hu
      filter_upwards [hu', hfk, hu] with g h1 h2 h3
      simp only [comp_apply] at h1
      rw [h1, h2, h3, hwk, star_mul']
      simp only [hωinv]
      ring
    · change ∫ g, f.val g * u g ∂μ𝔽 ≠ 0
      rw [hpair]
      exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.2 fun h ↦ hf (Subtype.ext h))
  · have key : ∃ f : W(l, r, s),
        (f : C𝔽 → ℂ) =ᵐ[μ𝔽] (fun x ↦ ((w x)⁻¹ : ℂ) * star (u x)) ∧
        ∫ x, u x * f x ∂μ𝔽 = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
      obtain ⟨f, hf, hpair⟩ := spectralSobolevPairing_isotype_conj μ𝔽
        (ρ := fun x ↦ if true = true then (w x)⁻¹ else w x)
        (ρ' := fun x ↦ if false = true then (w x)⁻¹ else w x)
        (by simp only [↓reduceIte]; exact hw.inv)
        (by simpa using hw) (by simpa using fun x ↦ inv_pos.2 (hwpos x)) (by simpa using hwpos)
        (fun x ↦ by simpa using inv_mul_cancel₀ (hwpos x).ne') u
      refine ⟨f, ?_, ?_⟩
      · filter_upwards [hf] with x hx
        rw [hx]
        simp only [↓reduceIte, Complex.ofReal_inv]
      · exact hpair
    obtain ⟨f, hf, hpair⟩ := key
    refine ⟨⟨f, (hiso f).2 fun k ↦ ?_⟩, ?_⟩
    · have hf' := (hqmp k).ae_eq_comp hf
      filter_upwards [hf', hu k, hf] with g h1 h2 h3
      simp only [comp_apply] at h1
      rw [h1, h2, h3, hwk, star_mul']
      simp only [hωinv, star_star]
      ring
    · change ∫ g, f g * u g ∂μ𝔽 ≠ 0
      simp_rw [mul_comm (f _)]
      rw [hpair]
      exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.2 hu0)

variable (F) in
/-- Paper: (10.2.1.3), p. 440, and (10.2.2.3), p. 445. Pull a functional
back along the quotient map and realize it in the reciprocal-weight Sobolev space. -/
def spectralSobolevDualEmbedding (a : ℝ) {l r s : ℝ} (hI : l ≤ r) (hs : 0 ≤ s) :
    StrongDual ℂ (spectralSobolevQuotient F a hI hs) →ₗ[ℂ] W'(l, r, s) :=
  (T(l, r, s, hI, hs)).toLinearEquiv.toLinearMap.comp
    ((Θ(a, hI, hs)).mkQL.precomp ℂ).toLinearMap

/-- A Hilbert quotient dual maps isometrically to the annihilator under an ambient duality. -/
private theorem spectralSobolevDualEmbedding_isometry_range_hilbert
    {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    (N : Submodule ℂ E) [IsClosed (N : Set E)]
    (T : StrongDual ℂ E ≃ₗᵢ[ℂ] V) (B : E → V → ℂ)
    (hB : ∀ (Λ : StrongDual ℂ E) (x : E), Λ x = B x (T Λ)) :
    Isometry (fun Λ : StrongDual ℂ (E ⧸ N) ↦ T (Λ.comp N.mkQL)) ∧
      Set.range (fun Λ : StrongDual ℂ (E ⧸ N) ↦ T (Λ.comp N.mkQL)) =
        {v : V | ∀ x ∈ N, B x v = 0} := by
  let P : StrongDual ℂ (E ⧸ N) →ₗ[ℂ] StrongDual ℂ E :=
    (N.mkQL.precomp ℂ).toLinearMap
  have hnorm (Λ : StrongDual ℂ (E ⧸ N)) : ‖P Λ‖ = ‖Λ‖ := by
    apply le_antisymm
    · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg Λ)
      intro x
      exact (Λ.le_opNorm (N.mkQL x)).trans
        (mul_le_mul_of_nonneg_left (Submodule.Quotient.norm_mk_le N x) (norm_nonneg Λ))
    · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (P Λ))
      intro q
      let v : Nᗮ := N.quotientEquivOrthogonal q
      have hv : N.mkQL v.val = q := by
        change (Submodule.Quotient.mk v.val : E ⧸ N) = q
        exact (N.quotientEquivOrthogonal_symm_eq_mk v.val v.property).symm.trans
          (N.quotientEquivOrthogonal.symm_apply_apply q)
      have hn : ‖v.val‖ = ‖q‖ := N.quotientEquivOrthogonal.norm_map q
      calc
        ‖Λ q‖ = ‖(P Λ) v.val‖ := by
          change ‖Λ q‖ = ‖Λ (N.mkQL v.val)‖
          rw [hv]
        _ ≤ ‖P Λ‖ * ‖v.val‖ := (P Λ).le_opNorm v.val
        _ = ‖P Λ‖ * ‖q‖ := by rw [hn]
  have hP : Isometry P := AddMonoidHomClass.isometry_of_norm P hnorm
  refine ⟨T.isometry.comp hP, ?_⟩
  ext v
  constructor
  · rintro ⟨Λ, rfl⟩ x hx
    rw [← hB (Λ.comp N.mkQL) x]
    change Λ (Submodule.Quotient.mk x) = 0
    rw [(Submodule.Quotient.mk_eq_zero N).mpr hx, map_zero]
  · intro hv
    let φ : StrongDual ℂ E := T.symm v
    have hφ : N ≤ φ.ker := by
      intro x hx
      change φ x = 0
      rw [hB φ x]
      change B x (T (T.symm v)) = 0
      rw [T.apply_symm_apply]
      exact hv x hx
    refine ⟨N.liftQL φ hφ, ?_⟩
    have hcomp : (N.liftQL φ hφ).comp N.mkQL = φ := by
      ext x
      rfl
    change T ((N.liftQL φ hφ).comp N.mkQL) = v
    rw [hcomp]
    exact T.apply_symm_apply v

/-- Paper: (10.2.1.3), p. 440, and (10.2.2.3), p. 445. Pullback along the
quotient identifies its strong dual isometrically with the theta annihilator. -/
theorem spectralSobolevDualEmbedding_isometry_range (a : ℝ) {l r s : ℝ} (hI : l ≤ r)
    (hs : 0 ≤ s) :
    let D := spectralSobolevDualEmbedding F a hI hs
    Isometry D ∧ range D = {u | ∀ f ∈ Θ(a, hI, hs), pair(f, u) = 0} := by
  exact spectralSobolevDualEmbedding_isometry_range_hilbert
    (E := W(l, r, s)) (V := W'(l, r, s))
    (Θ(a, hI, hs)) (T(l, r, s, hI, hs))
    (spectralSobolevPairing (F := F))
    (fun Λ f ↦ (spectralSobolevPairing_dual hI hs Λ f).2)

end Quotients

/-- Paper: Notation 10.2.1.1, p. 440, and Notation 10.2.2.1, p. 445.
Choose one continuous unitary extension for each norm-one character. -/
def IsSpectralBasepointChoice (χ : PontryaginDual C₁ → PontryaginDual C𝔽) : Prop :=
  ∀ ω, (χ ω).comp restriction = ω

/-- Paper: Notation 10.2.1.1, p. 440. A splitting of the idele class norm
provides unitary lifts for all the norm-one characters at once. -/
theorem exists_spectralBasepointChoice (F : Type*) [Field F] [NumberField F] :
    ∃ χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual (IdeleClassGroup (𝓞 F) F),
      IsSpectralBasepointChoice χ := by
  let C := IdeleClassGroup (𝓞 F) F
  let n : C →ₜ* ℝ≥0ˣ := ⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩
  let q : IdeleGroup (𝓞 F) F →ₜ* C := ⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩
  let σ : ℝ≥0ˣ →ₜ* C := q.comp
    ⟨canonicalIdeleNormSection F, canonicalIdeleNormSection_continuous F⟩
  have hσ : Function.RightInverse σ (ideleClassNorm F) := canonicalIdeleNormSection_rightInverse F
  let P : C →ₜ* C := ContinuousMonoidHom.id C / σ.comp n
  have hP (x : C) : P x ∈ (ideleClassNorm F).ker := by
    change ideleClassNorm F (x / σ (ideleClassNorm F x)) = 1
    rw [map_div, hσ, div_self']
  let r : C →ₜ* (ideleClassNorm F).ker := ⟨P.toMonoidHom.codRestrict _ hP, P.continuous.subtype_mk _⟩
  refine ⟨fun ω ↦ ω.comp r, fun ω ↦ ?_⟩
  ext x : 1
  change ω (r (x : C)) = ω x
  apply congrArg ω
  apply Subtype.ext
  change (x : C) / σ (ideleClassNorm F x) = x
  rw [show ideleClassNorm F (x : C) = 1 from x.property, map_one, div_one]

/-- Paper: (10.2.1.4), p. 440. In each component the norm twists of the
chosen extension give its unique complex parameter. -/
theorem IsSpectralBasepointChoice.existsUnique_normTwist
    {χ : PontryaginDual C₁ → PontryaginDual C𝔽} (_hχ : IsSpectralBasepointChoice χ)
    (ω : PontryaginDual C₁) (c : QuasiCharacter C𝔽)
    (_hc : ∀ g : C₁, c g.val = (ω g : ℂ)) :
    ∃! z : ℂ, c = ideleClassNormTwist (χ ω) z := by
  let q : IdeleGroup (𝓞 F) F →ₜ* C𝔽 := ⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩
  let σ : ℝ≥0ˣ →ₜ* C𝔽 := q.comp
    ⟨canonicalIdeleNormSection F, canonicalIdeleNormSection_continuous F⟩
  have hσ : Function.RightInverse σ (ideleClassNorm F) := canonicalIdeleNormSection_rightInverse F
  let j : Circle →ₜ* ℂ := ⟨Circle.coeHom, continuous_subtype_val⟩
  let d := c * j.comp (χ ω)⁻¹
  have hd (g : C𝔽) : d g = c g / (χ ω g : ℂ) := by
    change c g * (((χ ω g)⁻¹ : Circle) : ℂ) = _
    rw [Circle.coe_inv, div_eq_mul_inv]
  have hk (g : C₁) : d g = 1 := by
    have hres : χ ω (g : C𝔽) = ω g := DFunLike.congr_fun (_hχ ω) g
    rw [hd, _hc g, hres, div_self (Circle.coe_ne_zero _)]
  obtain ⟨z, hz, huniq⟩ := existsUnique_complexPower (d.comp σ)
  refine ⟨z, ?_, fun w hw ↦ ?_⟩
  · ext g : 1
    let t := ideleClassNorm F g
    have hg : g / σ t ∈ (ideleClassNorm F).ker := by
      change ideleClassNorm F (g / σ t) = 1
      rw [map_div, hσ t, div_self']
    have hr : d g = (((t : ℝ≥0) : ℝ) : ℂ) ^ z := calc
      d g = d (g / σ t) * d (σ t) := by rw [← map_mul, div_mul_cancel]
      _ = _ := by rw [hk ⟨_, hg⟩, one_mul]; exact hz t
    change c g = (χ ω g : ℂ) * _
    exact ((div_eq_iff (Circle.coe_ne_zero _)).mp ((hd g).symm.trans hr)).trans (mul_comm _ _)
  · apply huniq
    intro t
    change d (σ t) = _
    rw [hd, hw]
    change ((χ ω (σ t) : ℂ) * (((ideleClassNorm F (σ t)).val : ℝ) : ℂ) ^ w) / _ = _
    rw [hσ t, mul_div_cancel_left₀ _ (Circle.coe_ne_zero _)]

local notation "shift(" b ", " t ")" => ((b : ℝ) : ℂ) + (t : ℂ) * Complex.I
local notation "vanishingOrder(" χ ", " z ")" =>
  meromorphicOrderAt (continuedCompletedHeckeL χ) z

/-- Paper: (10.2.1.5), p. 440, and (10.2.2.4), p. 446. A zero jet is the
chosen base character times the norm twist and a power of the log norm.
The line jet has real offset zero. -/
def spectralZeroJet (χ : PontryaginDual C𝔽) (b t : ℝ) (k : ℕ) (g : C𝔽) : ℂ :=
  ideleClassNormTwist χ (shift(b, t)) g * (logNorm g : ℂ) ^ k

/-- Paper: (10.2.1.5), p. 440, and (10.2.2.4), p. 446. The zeroth jet at
twist zero is the base character.
Deviation: Sanity check in degree and twist zero. -/
theorem spectralZeroJet_zero (χ : PontryaginDual C𝔽) (g : C𝔽) :
    spectralZeroJet χ 0 0 0 g = (χ g : ℂ) := by
  unfold spectralZeroJet
  simp only [pow_zero, mul_one, Complex.ofReal_zero, zero_mul, add_zero]
  change (χ g : ℂ) * _ ^ (0 : ℂ) = _
  rw [Complex.cpow_zero, mul_one]

/-- Paper: (10.2.1.6), p. 440, and (10.2.2.5), p. 446. Truncate the
multiplicity to the number of integrable jet orders at the boundary.
Deviation: Use the ceiling of (s−1)/2. The floor of (s−1)/2+1 admits the
logarithmically divergent endpoint when (s−1)/2 is an integer. -/
def spectralBoundaryMultiplicity (s : ℝ) (N : ℕ) : ℕ :=
  min N (Nat.ceil ((s - 1) / 2))

/-- Paper: (10.2.1.6), p. 440, and (10.2.2.5), p. 446. An order survives
the boundary cutoff exactly when it is below the zero multiplicity and strictly
below the reciprocal-weight integrability threshold.
Deviation: The limiting jet is excluded. -/
theorem lt_spectralBoundaryMultiplicity (s : ℝ) (N k : ℕ) :
    k < spectralBoundaryMultiplicity s N ↔ k < N ∧ (k : ℝ) < (s - 1) / 2 := by
  rw [spectralBoundaryMultiplicity, lt_min_iff, Nat.lt_ceil]

/-- Paper: Remark 10.2.1.2, pp. 440–441. A Markushevich system in the paper's
Hilbert setting is biorthogonal and both linear spans are norm dense.
Deviation: An arbitrary index type permits a finite or empty enumeration. -/
def IsSpectralMarkushevichBasis {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (x : ι → E) (Λ : ι → StrongDual ℂ E) : Prop :=
  (∀ i, Λ i (x i) = 1) ∧ (∀ i j, i ≠ j → Λ j (x i) = 0) ∧
    Dense (Submodule.span ℂ (range x) : Set E) ∧
    Dense (Submodule.span ℂ (range Λ) : Set (StrongDual ℂ E))

/-- Paper: Remark 10.2.1.2, p. 440. The dense functional family determines
its biorthogonal vectors uniquely. -/
theorem IsSpectralMarkushevichBasis.unique_vectors {ι E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    {x y : ι → E} {Λ : ι → StrongDual ℂ E}
    (_hx : IsSpectralMarkushevichBasis x Λ) (_hy : IsSpectralMarkushevichBasis y Λ) :
    x = y := by
  funext i
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).mpr
  have he : ContinuousLinearMap.apply ℂ ℂ (x i) = ContinuousLinearMap.apply ℂ ℂ (y i) := by
    apply ContinuousLinearMap.ext_on _hx.2.2.2
    rintro _ ⟨j, rfl⟩
    change Λ j (x i) = Λ j (y i)
    by_cases hij : i = j
    · subst j
      exact (_hx.1 i).trans (_hy.1 i).symm
    · exact (_hx.2.1 i j hij).trans (_hy.2.1 i j hij).symm
  exact fun ℓ ↦ DFunLike.congr_fun he ℓ

local notation "multiplicity(" χ ", " z ")" => (vanishingOrder(χ, z)).untop₀.toNat

/-- Paper: Theorem 10.2.1.1, p. 440. Index the a-line jets by norm-one
characters, zero ordinates, and surviving derivative orders. Meromorphic order
excludes poles, even when the continuation has been assigned a value there.
Deviation: Apply the strict integrability cutoff of (10.2.1.6). -/
abbrev SpectralLineJetIndex (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (a s : ℝ) :=
  {j : PontryaginDual C₁ × ℝ × ℕ //
    j.2.2 < spectralBoundaryMultiplicity s (multiplicity(χ j.1, shift(a, j.2.1)))}

/-- Paper: Theorem 10.2.1.1, p. 440. Every admitted a-line jet has positive
derivative capacity, so its indexing point is a zero of the completed L-function. -/
theorem SpectralLineJetIndex.order_pos {χ : PontryaginDual C₁ → PontryaginDual C𝔽} {a s : ℝ}
    (j : SpectralLineJetIndex χ a s) : 0 < vanishingOrder(χ j.val.1, shift(a, j.val.2.1)) := by
  have key : ∀ o : WithTop ℤ, 0 < o.untop₀.toNat → 0 < o := by
    intro o h
    cases o with
    | top => simp at h
    | coe n =>
      rw [WithTop.untop₀_coe] at h
      exact_mod_cast (by omega : 0 < n)
  have h := j.2
  unfold spectralBoundaryMultiplicity at h
  exact key _ (by omega)

local notation "lineJet(" χ ", " j ")" => spectralZeroJet (χ (j).val.1) 0 (j).val.2.1 (j).val.2.2
local notation "stripJet(" χ ", " j ")" =>
  spectralZeroJet (χ (j).val.1) (j).val.2.1 (j).val.2.2.1 (j).val.2.2.2
local notation "L2μ'(" l ", " r ", " s ")" => (μ𝔽 |>.withDensity fun g ↦
  ENNReal.ofReal (intervalSobolevDensity l r s (logNorm g))⁻¹)

-- On p. 443 an outside-band evaluation vanishes on the band image. Its
-- dual inner product with an inside-band evaluation can be nonzero:
-- for s = 2 on the rational trivial component the Gram kernel is
-- proportional to exp(-|t-u|). The claimed orthogonal adjoint range fails.

/-- A logarithmic power below the strict cutoff is square-integrable for the reciprocal weight. -/
private theorem spectralLineJet_memLp_of_norm_sq
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m) (hms : Surjective m)
    (μ : Measure G) [μ.IsHaarMeasure] (s : ℝ) (k : ℕ)
    (hk : 2 * (k : ℝ) + 1 < s) (u : G → ℂ) (hu : Continuous u)
    (hnorm : ∀ g : G, ‖u g‖ ^ 2 = (Real.log ((m g).val : ℝ)) ^ (2 * k)) :
    MemLp u 2 (μ.withDensity fun g ↦
      ENNReal.ofReal (((1 + (Real.log ((m g).val : ℝ)) ^ 2) ^ (s / 2))⁻¹)) := by
  let ν : Measure G := canonicalModulatedHaar m hm
  let : ν.IsHaarMeasure :=
    (existsUnique_canonicalModulatedHaar m hm).exists.choose_spec.1
  have hν : Integrable (fun g : G ↦ (Real.log ((m g).val : ℝ)) ^ (2 * k) *
      ((1 + (Real.log ((m g).val : ℝ)) ^ 2) ^ (s / 2))⁻¹) ν :=
    (sobolev_log_preserving m hm hms).integrable_comp_of_integrable
      (integrable_pow_mul_rpow_inv hk)
  have hμ : Integrable (fun g : G ↦ (Real.log ((m g).val : ℝ)) ^ (2 * k) *
      ((1 + (Real.log ((m g).val : ℝ)) ^ 2) ^ (s / 2))⁻¹) μ := by
    rw [Measure.isMulLeftInvariant_eq_smul μ ν]
    exact hν.smul_measure_nnreal
  have hρpos (g : G) : 0 < (1 + (Real.log ((m g).val : ℝ)) ^ 2) ^ (s / 2) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hρ : Continuous (fun g : G ↦ (1 + (Real.log ((m g).val : ℝ)) ^ 2) ^ (s / 2)) :=
    ((continuous_const : Continuous (fun _ : G ↦ (1 : ℝ))).add
      ((continuous_logModule' m).pow 2)).rpow_const (fun g ↦ Or.inl (by
        change (1 : ℝ) + (Real.log ((m g).val : ℝ)) ^ 2 ≠ 0
        positivity))
  apply (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).2
  apply (integrable_withDensity_iff
    (hρ.inv₀ (fun g ↦ (hρpos g).ne')).measurable.ennreal_ofReal
    (ae_of_all μ fun _ ↦ ENNReal.ofReal_lt_top)).2
  refine hμ.congr (ae_of_all μ fun g ↦ ?_)
  dsimp only [Pi.inv_apply]
  rw [hnorm g, ENNReal.toReal_ofReal (inv_nonneg.mpr (hρpos g).le)]

/-- Paper: Theorem 10.2.1.1, p. 440. The admitted a-line jets are elements of
the reciprocal-weight Hilbert space.
Deviation: Exclude the divergent endpoint of (10.2.1.6). -/
theorem spectralLineJet_memLp (χ : PontryaginDual C₁ → PontryaginDual C𝔽) {a s : ℝ}
    (_hs : 1 < s) (j : SpectralLineJetIndex χ a s) :
    MemLp (lineJet(χ, j)) 2 (L2μ'(0, 0, s)) := by
  have horder : (j.val.2.2 : ℝ) < (s - 1) / 2 :=
    ((lt_spectralBoundaryMultiplicity s _ _).mp j.property).2
  have hk : 2 * (j.val.2.2 : ℝ) + 1 < s := by linarith
  let u : C𝔽 → ℂ := spectralZeroJet (χ j.val.1) 0 j.val.2.1 j.val.2.2
  have hu : Continuous u :=
    (ideleClassNormTwist (χ j.val.1)
      ((0 : ℂ) + (j.val.2.1 : ℂ) * Complex.I)).continuous.mul
      ((Complex.continuous_ofReal.comp (continuous_logModule' m𝔽)).pow j.val.2.2)
  have hnorm (g : C𝔽) : ‖u g‖ ^ 2 = (logNorm g) ^ (2 * j.val.2.2) := by
    have htwist : ‖ideleClassNormTwist (χ j.val.1)
        ((0 : ℂ) + (j.val.2.1 : ℂ) * Complex.I) g‖ = 1 := by
      change ‖(χ j.val.1 g : ℂ) *
        (((ideleClassNorm F g).val : ℝ) : ℂ) ^
          ((0 : ℂ) + (j.val.2.1 : ℂ) * Complex.I)‖ = 1
      rw [norm_mul, Circle.norm_coe, one_mul,
        Complex.norm_cpow_eq_rpow_re_of_pos
          (NNReal.coe_pos.mpr (Units.zero_lt (ideleClassNorm F g)))]
      simp
    change ‖ideleClassNormTwist (χ j.val.1)
      ((0 : ℂ) + (j.val.2.1 : ℂ) * Complex.I) g *
        (logNorm g : ℂ) ^ j.val.2.2‖ ^ 2 = _
    rw [norm_mul, htwist, one_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    calc
      (|logNorm g| ^ j.val.2.2) ^ 2 =
          (|logNorm g| ^ 2) ^ j.val.2.2 := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm j.val.2.2 2]
      _ = ((logNorm g) ^ 2) ^ j.val.2.2 :=
        congrArg (fun y : ℝ ↦ y ^ j.val.2.2) (sq_abs (logNorm g))
      _ = (logNorm g) ^ (2 * j.val.2.2) := (pow_mul _ _ _).symm
  have h := spectralLineJet_memLp_of_norm_sq m𝔽 hm𝔽 hms𝔽 μ𝔽 s j.val.2.2 hk u hu hnorm
  change MemLp u 2 ((μ𝔽).withDensity fun g ↦
    ENNReal.ofReal (((1 + (logNorm g) ^ 2) ^ (s / 2))⁻¹)) at h
  simpa only [intervalSobolevDensity, mul_zero, zero_mul, Real.exp_zero,
    max_self, one_mul, u] using h

-- For a family of admitted jets u, these are the two analytic inputs to
-- the Hilbert-space argument. Interpolants are lifted to the ambient space.
local notation "JetKernel(" a ", " hI ", " hs ", " u ")" =>
  (∀ f, f ∈ Θ(a, hI, hs) ↔ ∀ j, spectralSobolevPairing (F := F) f (u j) = 0)
local notation "JetInterpolation(" J ", " a ", " hI ", " hs ", " u ")" =>
  (∃ v : J → W(_, _, _), (∀ i, spectralSobolevPairing (F := F) (v i) (u i) = 1) ∧
    (∀ i j, i ≠ j → spectralSobolevPairing (F := F) (v i) (u j) = 0) ∧
    Dense (Submodule.span ℂ (range (fun i ↦ (Θ(a, hI, hs)).mkQ (v i))) :
      Set (spectralSobolevQuotient F a hI hs)))

/-- A total family of continuous functionals on a Hilbert space has norm-dense span. -/
private theorem spectralSobolevQuotient_basis_of_interpolation_dense_dual
    {Q J : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]
    (Λ : J → StrongDual ℂ Q)
    (h : ∀ q : Q, (∀ j, Λ j q = 0) → q = 0) :
    Dense (Submodule.span ℂ (Set.range Λ) : Set (StrongDual ℂ Q)) := by
  let R := InnerProductSpace.toDual ℂ Q
  let v : J → Q := fun j ↦ R.symm (Λ j)
  have hv : Dense (Submodule.span ℂ (Set.range v) : Set Q) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top,
      Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
    intro q hq
    apply h q
    intro j
    have hz := (Submodule.mem_orthogonal (Submodule.span ℂ (Set.range v)) q).mp hq
      (v j) (Submodule.subset_span (Set.mem_range_self j))
    simpa only [v, R, InnerProductSpace.toDual_symm_apply] using hz
  apply (R.surjective.denseRange.dense_image R.continuous hv).mono
  apply (Submodule.image_span_subset R.toLinearEquiv.toLinearMap
    (Set.range v) (Submodule.span ℂ (Set.range Λ))).mpr
  rintro _ ⟨j, rfl⟩
  change R (R.symm (Λ j)) ∈ Submodule.span ℂ (Set.range Λ)
  rw [R.apply_symm_apply]
  exact Submodule.subset_span (Set.mem_range_self j)

/-- Dense interpolants and a total lifted dual family form a spectral Markushevich basis. -/
private theorem spectralSobolevQuotient_basis_of_interpolation_construct
    {J E Q U : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]
    (q : E → Q) (hq : Function.Surjective q)
    (D : StrongDual ℂ Q → U) (b : E → U → ℂ) (u : J → U)
    (hpair : ∀ (Λ : StrongDual ℂ Q) (f : E), Λ (q f) = b f (D Λ))
    (hu : ∀ j, ∃ Λ : StrongDual ℂ Q, D Λ = u j)
    (hzero : ∀ f : E, (∀ j, b f (u j) = 0) → q f = 0)
    (hV : ∃ v : J → E,
      (∀ i, b (v i) (u i) = 1) ∧
      (∀ i j, i ≠ j → b (v i) (u j) = 0) ∧
      Dense (Submodule.span ℂ (Set.range (fun i ↦ q (v i))) : Set Q)) :
    ∃ (x : J → Q) (Λ : J → StrongDual ℂ Q), IsSpectralMarkushevichBasis x Λ ∧
      ∀ j, D (Λ j) = u j := by
  classical
  choose Λ hΛ using hu
  obtain ⟨v, hvself, hvcross, hvdense⟩ := hV
  have he (j : J) (f : E) : Λ j (q f) = b f (u j) :=
    (hpair (Λ j) f).trans (congrArg (b f) (hΛ j))
  refine ⟨fun j ↦ q (v j), Λ, ?_, hΛ⟩
  refine ⟨fun i ↦ (he i (v i)).trans (hvself i),
    fun i j hij ↦ (he j (v i)).trans (hvcross i j hij), hvdense, ?_⟩
  apply spectralSobolevQuotient_basis_of_interpolation_dense_dual Λ
  intro z hz
  obtain ⟨f, rfl⟩ := hq z
  apply hzero f
  intro j
  exact (he j f).symm.trans (hz j)

/-- Paper: Theorems 10.2.1.1 and 10.2.2.1, pp. 440, 446. A common kernel
identifies the closed dual span in the Hilbert quotient. A dense family of
interpolants then supplies the other half of the Markushevich basis. -/
theorem spectralSobolevQuotient_basis_of_interpolation {J : Type*}
    (a : ℝ) {l r s : ℝ} (hI : l ≤ r) (hs : 0 ≤ s) (u : J → W'(l, r, s))
    (_hK : JetKernel(a, hI, hs, u)) (_hV : JetInterpolation(J, a, hI, hs, u)) :
    let Q := spectralSobolevQuotient F a hI hs
    let D := spectralSobolevDualEmbedding F a hI hs
    ∃ (x : J → Q) (Λ : J → StrongDual ℂ Q), IsSpectralMarkushevichBasis x Λ ∧
      ∀ j, D (Λ j) = u j := by
  classical
  let N := globalThetaSobolev F a hI hs
  let D := spectralSobolevDualEmbedding F a hI hs
  have hpair (Λ : StrongDual ℂ (spectralSobolevQuotient F a hI hs))
      (f : W(l, r, s)) :
      Λ (N.mkQ f) = spectralSobolevPairing f (D Λ) := by
    exact (spectralSobolevPairing_dual hI hs (Λ.comp N.mkQL) f).2
  have hu (j : J) :
      ∃ Λ : StrongDual ℂ (spectralSobolevQuotient F a hI hs), D Λ = u j := by
    have hj : u j ∈ Set.range (spectralSobolevDualEmbedding F a hI hs) := by
      rw [(spectralSobolevDualEmbedding_isometry_range (F := F) a hI hs).2]
      exact fun f hf ↦ (_hK f).mp hf j
    exact hj
  refine spectralSobolevQuotient_basis_of_interpolation_construct
    (Q := spectralSobolevQuotient F a hI hs)
    N.mkQ N.mkQ_surjective D (spectralSobolevPairing (F := F)) u hpair hu ?_ _hV
  intro f hf
  exact (spectralSobolevQuotient_eq_zero a hI hs f).mpr ((_hK f).mpr hf)

local notation "lineHs(" hs ")" => le_of_lt (zero_lt_one.trans hs)
local notation "lineU(" χ ", " hs ")" =>
  (fun j ↦ (spectralLineJet_memLp χ hs j).toLp (lineJet(χ, j)))

/-- Paper: Theorem 10.2.1.1, p. 440. The norm-one dual and the discrete
zero sets in its charts give countably many admitted line jets. -/
theorem spectralLineJet_countable (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (a s : ℝ) :
    Countable (SpectralLineJetIndex χ a s) := by
  have hK : IsCompact ((ideleClassNorm F).ker : Set C𝔽) :=
    IsModulation.isCompact_ker (m := m𝔽) hm𝔽
  let : CompactSpace C₁ := isCompact_iff_compactSpace.mp hK
  let : LocallyCompactSpace C₁ := hK.isClosed.locallyCompactSpace
  let : SecondCountableTopology C₁ := Topology.IsInducing.subtypeVal.secondCountableTopology
  let : SecondCountableTopology Circle :=
    inferInstanceAs (SecondCountableTopology (Metric.sphere (0 : ℂ) 1))
  let : SecondCountableTopology (PontryaginDual C₁) :=
    (ContinuousMonoidHom.isEmbedding_toContinuousMap C₁ Circle).secondCountableTopology
  let : Countable (PontryaginDual C₁) := countable_of_Lindelof_of_discrete
  let Z (ω : PontryaginDual C₁) := {z : ℂ | 0 < multiplicity(χ ω, z)}
  have hc (ω : PontryaginDual C₁) : (Z ω).Countable := by
    have hm := (continuedCompletedHeckeL_spec (χ ω)).1.meromorphicOn
    have hcod : (Z ω)ᶜ ∈ Filter.codiscrete ℂ := by
      filter_upwards [hm.codiscreteWithin_setOfPred_meromorphicOrderAt_eq_zero_or_top] with z hz
      rcases hz.2 with h | h <;> simp [Z, h]
    let : DiscreteTopology (Z ω) := isDiscrete_iff_discreteTopology.mp
      (compl_mem_codiscrete_iff.mp hcod).2
    exact Set.countable_coe_iff.mp countable_of_Lindelof_of_discrete
  let W := ⋃ ω, Z ω
  let : Countable W := (Set.countable_iUnion hc).to_subtype
  have hz (j : SpectralLineJetIndex χ a s) : shift(a, j.val.2.1) ∈ W := by
    apply Set.mem_iUnion.mpr
    refine ⟨j.val.1, ?_⟩
    exact Nat.zero_lt_of_lt (lt_of_lt_of_le j.property (min_le_left _ _))
  let e (j : SpectralLineJetIndex χ a s) : PontryaginDual C₁ × W × ℕ :=
    (j.val.1, ⟨shift(a, j.val.2.1), hz j⟩, j.val.2.2)
  apply Function.Injective.countable (f := e)
  intro i j hij
  have him := congrArg (fun p : PontryaginDual C₁ × W × ℕ ↦ p.2.1.val.im) hij
  have hω := congrArg (fun p : PontryaginDual C₁ × W × ℕ ↦ p.1) hij
  have hk := congrArg (fun p : PontryaginDual C₁ × W × ℕ ↦ p.2.2) hij
  exact Subtype.ext (Prod.ext hω (Prod.ext (by simpa [e] using him) hk))

section TestDuality

local notation "E" => ModulatedExponentialDecay m𝔽 univ
local notation "ρE" => (exists_modulatedExponentialDecay_translationAction m𝔽 univ
  hm𝔽 hms𝔽 ordConnected_univ univ_nonempty).choose
local notation "Eω(" ω ")" => actionIsotype ((ρE).comp (ideleClassNorm F).ker.subtype) ω
local notation "ℬ₀" => ↥(adelePolarSubspace F)

/-- A jointly continuous family on a compact parameter space preserves sequence
convergence uniformly in the parameter. -/
private theorem existsUnique_spectralLineTestCompletion_uniform
    {H Z : Type*} [TopologicalSpace H] [CompactSpace H] [UniformSpace Z]
    (T : H → Z → Z) (hT : Continuous (fun p : H × Z ↦ T p.1 p.2))
    (u : ℕ → Z) (v : Z) (hu : Tendsto u atTop (𝓝 v)) :
    TendstoUniformly (fun n k ↦ T k (u n)) (fun k ↦ T k v) atTop := by
  intro U hU
  have hc : Continuous (fun p : Z × H ↦ T p.2 p.1) := hT.comp continuous_swap
  obtain ⟨V, hV, h⟩ := (isCompact_univ (X := H)).mem_uniformity_of_prod
    (f := fun f : Z ↦ fun k : H ↦ T k f)
    (s := univ) (q := v) hc.continuousOn (mem_univ v) (symm_le_uniformity hU)
  rw [nhdsWithin_univ] at hV
  filter_upwards [hu.eventually hV] with n hn k
  exact h (u n) hn k (mem_univ k)

/-- Compact character averaging preserves density of an equivariant map. -/
private theorem existsUnique_spectralLineTestCompletion_dense
    {H X Y : Type*} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H]
    [T2Space H] [MeasurableSpace H] [BorelSpace H] [CompactSpace H]
    [AddCommGroup X] [Module ℂ X] [UniformSpace X] [IsUniformAddGroup X]
    [T2Space X] [PolynormableSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
    (μ : Measure H) [μ.IsHaarMeasure]
    (σ : H →* (X →L[ℂ] X)) (τ : H →* (Y →L[ℂ] Y))
    (hσ : Continuous (fun p : H × X ↦ σ p.1 p.2))
    (hτ : Continuous (fun p : H × Y ↦ τ p.1 p.2))
    (hborn : ∀ p : Seminorm ℂ X,
      (∀ B : Set X, Bornology.IsVonNBounded ℂ B → BddAbove (p '' B)) → Continuous p)
    (ω : PontryaginDual H) (j : X →L[ℂ] Y) (hd : DenseRange j)
    (heq : ∀ k f, j (σ k f) = τ k (j f))
    (i : actionIsotype σ ω →L[ℂ] actionIsotype τ ω)
    (hi : ∀ f, (i f : Y) = j (f : X)) : DenseRange i := by
  letI : Module ℝ X := Module.restrictScalars ℝ ℂ X
  letI : IsScalarTower ℝ ℂ X := IsScalarTower.restrictScalars ℝ ℂ X
  letI : LocallyConvexSpace ℝ X :=
    (PolynormableSpace.withSeminorms ℂ X).toLocallyConvexSpace
  letI : NormedSpace ℝ Y := NormedSpace.complexToReal
  have hbornY (p : Seminorm ℂ Y)
      (hp : ∀ B : Set Y, Bornology.IsVonNBounded ℂ B → BddAbove (p '' B)) :
      Continuous p := by
    obtain ⟨M, hM⟩ := hp _ (NormedSpace.isVonNBounded_closedBall ℂ Y 1)
    have hball : p.closedBall 0 (max M 0 + 1) ∈ 𝓝 (0 : Y) := by
      refine Filter.mem_of_superset (Metric.closedBall_mem_nhds (0 : Y) zero_lt_one) ?_
      intro x hx
      rw [Seminorm.mem_closedBall_zero]
      exact (hM ⟨x, hx, rfl⟩).trans
        (le_of_lt <| lt_of_le_of_lt (le_max_left M 0) (lt_add_one _))
    exact p.continuous' hball
  obtain ⟨A, hA⟩ := (existsUnique_compactActionIsotypicAverage μ σ hσ
    hborn (existsUnique_spectralLineTestCompletion_uniform (Z := X)
      (fun k f ↦ σ k f) hσ) ω).exists
  obtain ⟨B, hB⟩ := (existsUnique_compactActionIsotypicAverage μ τ hτ
    hbornY (existsUnique_spectralLineTestCompletion_uniform (Z := Y)
      (fun k f ↦ τ k f) hτ) ω).exists
  have hrangeA := compactActionAverage_range μ σ hσ ω A hA
  have hrangeB := compactActionAverage_range μ τ hτ ω B hB
  let A' := A.codRestrict (actionIsotype σ ω) (by
    intro u
    rw [← hrangeA]
    exact ⟨u, rfl⟩)
  let B' := B.codRestrict (actionIsotype τ ω) (by
    intro u
    rw [← hrangeB]
    exact ⟨u, rfl⟩)
  have hsurj : Surjective B' := by
    intro u
    have hu : (u : Y) ∈ B.toLinearMap.range := hrangeB.symm ▸ u.property
    obtain ⟨v, hv⟩ := hu
    exact ⟨v, Subtype.ext hv⟩
  have hcomm (f : X) : j (A f) = B (j f) := by
    letI : SeparatingDual ℂ Y := locallyConvexSpace_separatingDual ℂ Y
    apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2
    intro φ
    obtain ⟨_, hs⟩ := hA f
    obtain ⟨_, ht⟩ := hB (j f)
    have hs' := LinearMap.congr_fun hs (φ.comp j)
    have ht' := LinearMap.congr_fun ht φ
    change φ (j (A f)) =
      ∫ k : H, φ (j (star (ω k : ℂ) • σ k f)) ∂μ.restrict univ at hs'
    change φ (B (j f)) =
      ∫ k : H, φ (star (ω k : ℂ) • τ k (j f)) ∂μ.restrict univ at ht'
    simpa only [map_smul j, heq, ← ht'] using hs'
  have hcomp : (i : _ → _) ∘ A' = (B' : _ → _) ∘ j :=
    funext fun f ↦ Subtype.ext ((hi (A' f)).trans (hcomm f))
  apply DenseRange.of_comp (g := A')
  rw [hcomp]
  exact hsurj.denseRange.comp hd B'.continuous

/-- Paper: (10.2.1.7), p. 441. The weighted completion map on exponential-decay
tests preserves the norm-one isotype and has dense image in its Sobolev isotype.
Its transpose evaluates by pairing with the weighted test.
Deviation: The transpose uses the conjugate isotype in the negative space.
The norm weight is applied to the full test space in the diagram. Appendix D's
two-sided decay topology uses growing exponential weights in log coordinates.
The decaying factors on p. 441 would all be bounded by the zeroth weight. -/
theorem existsUnique_spectralLineTestCompletion (a : ℝ) {s : ℝ} (hs : 0 ≤ s)
    (ω : PontryaginDual C₁) :
    ∃! i : Eω(ω) →L[ℂ] Wω(le_rfl (a := (0 : ℝ)), hs, ω),
      (∀ φ, ((i φ).val : C𝔽 → ℂ) =ᵐ[μ𝔽] modulationWeight m𝔽 a φ.val.val) ∧
        DenseRange i ∧
        ∃ T : W'(0, 0, s) →L[ℂ] StrongDual ℂ Eω(ω),
          (∀ u φ, T u φ = spectralSobolevPairing (F := F) (i φ).val u) ∧
          ∀ u, (∀ k : C₁, (fun g ↦ u (k.val⁻¹ * g)) =ᵐ[μ𝔽]
            fun g ↦ (ω⁻¹ k : ℂ) * u g) → T u = 0 → u = 0 := by
  have hshift : (fun b : ℝ ↦ b - a) '' univ = univ :=
    image_univ_of_surjective fun b ↦ ⟨b + a, add_sub_cancel_right b a⟩
  have hShiftEx : ∃ S : E ≃L[ℂ] E,
      ∀ f, (S f).val = modulationWeight m𝔽 a f.val :=
    (congrArg (fun J : Set ℝ ↦ ∃ S : E ≃L[ℂ] ModulatedExponentialDecay m𝔽 J,
      ∀ f, (S f).val = modulationWeight m𝔽 a f.val) hshift).mp
      (modulatedExponentialDecay_shift_equiv (G := C𝔽) m𝔽 univ hm𝔽 hms𝔽
        ordConnected_univ univ_nonempty a)
  let S := hShiftEx.choose
  have hS := hShiftEx.choose_spec
  have hDenseEx :=
    modulatedIntervalSobolev_dense (G := C𝔽) m𝔽 hm𝔽 0 0 s le_rfl hs univ
      isOpen_univ ordConnected_univ (subset_univ _)
  let j₀ := hDenseEx.choose
  have hj₀inj := hDenseEx.choose_spec.1
  have hj₀dense := hDenseEx.choose_spec.2.1
  have hj₀coe := hDenseEx.choose_spec.2.2
  have hEquivEx := globalThetaAmbient_equiv_canonical (F := F) hm𝔽 0 0 s
  let e := hEquivEx.choose
  have he := hEquivEx.choose_spec
  let j : E →L[ℂ] W(0, 0, s) :=
    e.symm.toContinuousLinearMap.comp (j₀.comp S.toContinuousLinearMap)
  have hjinj : Injective j := e.symm.injective.comp (hj₀inj.comp S.injective)
  have hjdense : DenseRange j := e.symm.surjective.denseRange.comp
    (hj₀dense.comp S.surjective.denseRange j₀.continuous) e.symm.continuous
  have hj (f : E) : (j f : C𝔽 → ℂ) =ᵐ[μ𝔽] modulationWeight m𝔽 a f.val := by
    have h₀ : (j₀ (S f) : C𝔽 → ℂ) =ᵐ[μ𝔽] (S f).val := by
      rw [ideleClassTamagawaMeasure_eq_smul_canonical (F := F)]
      exact Measure.ae_smul_measure (hj₀coe (S f)) _
    have he' := (he (j f)).1
    have hej : e (j f) = j₀ (S f) := by simp [j]
    rw [hej] at he'
    exact he'.symm.trans (h₀.trans (ae_of_all _ fun g ↦ congrFun (hS f) g))
  let σ : C₁ →* (E →L[ℂ] E) := (ρE).comp (ideleClassNorm F).ker.subtype
  let τ : C₁ →* (W(0, 0, s) →L[ℂ] W(0, 0, s)) := ρ(0, 0, s, le_rfl, hs)
  have hE := (exists_modulatedExponentialDecay_translationAction (G := C𝔽) m𝔽 univ
    hm𝔽 hms𝔽 ordConnected_univ univ_nonempty).choose_spec
  have hjρ (k : C₁) (f : E) : j (σ k f) = τ k (j f) := by
    apply Lp.ext
    apply (withDensity_absolutelyContinuous μ𝔽 _).ae_eq
    have htr := hardySobolevTranslation_apply μ𝔽 m𝔽 0 0 s le_rfl hs k.val (j f)
    have ht := (measurePreserving_mul_left μ𝔽 k.val⁻¹).quasiMeasurePreserving.ae_eq_comp (hj f)
    filter_upwards [hj (σ k f), htr, ht] with g hleft hright hcomp
    change (j f) (k.val⁻¹ * g) = (modulationWeight m𝔽 a f.val) (k.val⁻¹ * g) at hcomp
    have hweight : (modulationWeight m𝔽 a (σ k f).val) g =
        (modulationWeight m𝔽 a f.val) (k.val⁻¹ * g) := by
      have hk : m𝔽 k.val = 1 := k.property
      have hn : m𝔽 (k.val⁻¹ * g) = m𝔽 g := by
        rw [map_mul, map_inv, hk, inv_one, one_mul]
      change Complex.ofReal (((m𝔽 g).val : ℝ) ^ a) * ((ρE) k.val f).val g =
        Complex.ofReal (((m𝔽 (k.val⁻¹ * g)).val : ℝ) ^ a) * f.val (k.val⁻¹ * g)
      have hv := congrArg (fun z : ℂ ↦ Complex.ofReal (((m𝔽 g).val : ℝ) ^ a) * z)
        (hE.1 k.val f g)
      have hw := congrArg (fun t : ℝ≥0ˣ ↦
        Complex.ofReal ((t.val : ℝ) ^ a) * f.val (k.val⁻¹ * g)) hn.symm
      exact hv.trans hw
    exact hleft.trans (hweight.trans (hcomp.symm.trans hright.symm))
  let i : actionIsotype σ ω →L[ℂ] actionIsotype τ ω :=
    (j.comp (actionIsotype σ ω).subtypeL).codRestrict (actionIsotype τ ω) (by
      intro φ
      apply (mem_actionIsotype τ ω _).2
      intro k
      change τ k (j φ.val) = (ω k : ℂ) • j φ.val
      rw [← hjρ, ((mem_actionIsotype σ ω _).1 φ.property k), map_smul])
  have hicoe (φ : Eω(ω)) : ((i φ).val : C𝔽 → ℂ) =ᵐ[μ𝔽]
      modulationWeight m𝔽 a φ.val.val := hj φ.val
  letI : T2Space E := T2Space.of_injective_continuous (f := j) hjinj j.continuous
  let q : IdeleGroup (𝓞 F) F →ₜ* C𝔽 := ⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩
  let sectionNorm : ℝ≥0ˣ →ₜ* C𝔽 := q.comp
    ⟨canonicalIdeleNormSection F, canonicalIdeleNormSection_continuous F⟩
  have hsection : Function.RightInverse sectionNorm m𝔽 := canonicalIdeleNormSection_rightInverse F
  letI : CompleteSpace E := modulatedExponentialDecay_complete (G := C𝔽) m𝔽 univ hm𝔽
    ordConnected_univ univ_nonempty sectionNorm hsection
  letI : CompactSpace C₁ :=
    isCompact_iff_compactSpace.mp (IsModulation.isCompact_ker (m := m𝔽) hm𝔽)
  letI : MeasurableSpace C₁ := borel _
  letI : BorelSpace C₁ := ⟨rfl⟩
  have hσ : Continuous (fun p : C₁ × E ↦ σ p.1 p.2) :=
    hE.2.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hτ : Continuous (fun p : C₁ × W(0, 0, s) ↦ τ p.1 p.2) :=
    (exists_hardySobolevTranslation μ𝔽 m𝔽 0 0 s le_rfl hs).choose_spec.2.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hidense : DenseRange i := existsUnique_spectralLineTestCompletion_dense
    (H := C₁) (X := E) (Y := W(0, 0, s)) Measure.haar σ τ hσ hτ
    (modulatedExponentialDecay_bornological (G := C𝔽) m𝔽 univ hm𝔽 ordConnected_univ
      univ_nonempty sectionNorm hsection) ω j hjdense hjρ i (fun _ ↦ rfl)
  let D : StrongDual ℂ W(0, 0, s) ≃ₗᵢ[ℂ] W'(0, 0, s) :=
    (modulatedIntervalSobolev_dual m𝔽 hm𝔽 μ𝔽 0 0 s le_rfl hs).exists.choose
  let T' : W'(0, 0, s) →L[ℂ] StrongDual ℂ Eω(ω) :=
    (((actionIsotype τ ω).subtypeL.comp i).precomp ℂ).comp
      D.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hT (u : W'(0, 0, s)) (φ : Eω(ω)) :
      T' u φ = spectralSobolevPairing (F := F) (i φ).val u := by
    change (D.symm u) (i φ).val = _
    have h := (spectralSobolevPairing_dual le_rfl hs (D.symm u) (i φ).val).2
    change (D.symm u) (i φ).val = spectralSobolevPairing (F := F) (i φ).val
      (D (D.symm u)) at h
    exact h.trans (congrArg (spectralSobolevPairing (F := F) (i φ).val) (D.apply_symm_apply u))
  refine ⟨i, ⟨hicoe, hidense, T', hT, ?_⟩, ?_⟩
  · intro u hu hTu
    let Λ : StrongDual ℂ (actionIsotype τ ω) := (D.symm u).comp (actionIsotype τ ω).subtypeL
    have hΛ : Λ = 0 := by
      apply DFunLike.coe_injective
      apply hidense.equalizer Λ.continuous (0 : StrongDual ℂ (actionIsotype τ ω)).continuous
      funext φ
      change T' u φ = 0
      exact congrArg (fun L : StrongDual ℂ Eω(ω) ↦ L φ) hTu
    by_contra hu0
    obtain ⟨f, hf⟩ := (spectralSobolevPairing_isotype le_rfl hs ω).2 u hu hu0
    apply hf
    have h := (spectralSobolevPairing_dual le_rfl hs (D.symm u) f.val).2
    change (D.symm u) f.val = spectralSobolevPairing (F := F) f.val
      (D (D.symm u)) at h
    exact (h.trans (congrArg (spectralSobolevPairing (F := F) f.val)
      (D.apply_symm_apply u))).symm.trans
        (congrArg (fun L : StrongDual ℂ (actionIsotype τ ω) ↦ L f) hΛ)
  · intro i' hi'
    apply ContinuousLinearMap.ext
    intro φ
    apply Subtype.ext
    exact Lp.ext ((withDensity_absolutelyContinuous μ𝔽 _).ae_eq
      ((hi'.1 φ).trans (hicoe φ).symm))

/-- Paper: (10.2.1.8), pp. 441–442. Pullback sends a functional on the
isotypic Sobolev quotient injectively into the test dual and annihilates
the polar-free theta tests of that isotype.
Deviation: Pull back along the norm-weighted completion map of (10.2.1.7). -/
theorem spectralLineIsotypeDual_pullback (a : ℝ) {s : ℝ} (hs : 0 ≤ s) (ω : PontryaginDual C₁) :
    let hI : (0 : ℝ) ≤ 0 := le_rfl
    let N := (Θ(a, hI, hs)).comap (Wω(hI, hs, ω)).subtype
    let i := (existsUnique_spectralLineTestCompletion a hs ω).exists.choose
    let D : StrongDual ℂ (spectralSobolevIsotypeQuotient F a hI hs ω) →L[ℂ]
        StrongDual ℂ Eω(ω) := (N.mkQL.comp i).precomp ℂ
    Injective D ∧ ∀ Λ (φ : Eω(ω)) (f : ℬ₀), φ.val.val = homogeneousAdelicTheta ω f.val → D Λ φ = 0 := by
  intro hI N i D
  have hi := (existsUnique_spectralLineTestCompletion (F := F) a hs ω).exists.choose_spec
  constructor
  · have hd : DenseRange (N.mkQL.comp i) :=
      N.mkQ_surjective.denseRange.comp hi.2.1 N.mkQL.continuous
    intro Λ₁ Λ₂ hΛ
    apply DFunLike.coe_injective
    exact hd.equalizer Λ₁.continuous Λ₂.continuous
      (funext fun φ ↦ congrArg (fun T : StrongDual ℂ Eω(ω) ↦ T φ) hΛ)
  · intro Λ φ f hφ
    let x : globalPolarFreeThetaSubmodule (F := F) ω :=
      ⟨Submodule.Quotient.mk f.val, Submodule.mem_map.mpr ⟨f.val, f.property, rfl⟩⟩
    let j := (exists_globalHomogeneousThetaSobolevInclusion
      (F := F) (a := a) hI hs ω).choose
    have hj := (exists_globalHomogeneousThetaSobolevInclusion
      (F := F) (a := a) hI hs ω).choose_spec.2.2
    have he : (i φ).val = (j x).val.val := by
      apply Lp.ext
      apply (withDensity_absolutelyContinuous μ𝔽 _).ae_eq
      have hw : modulationWeight m𝔽 a φ.val.val =ᵐ[μ𝔽]
          modulationWeight m𝔽 a (homogeneousAdelicTheta ω f.val) :=
        Filter.Eventually.of_forall (congrFun (congrArg (modulationWeight m𝔽 a) hφ))
      exact (hi.1 φ).trans (hw.trans (hj f x rfl).2.symm)
    have hn : i φ ∈ N := by
      change (i φ).val ∈ Θ(a, hI, hs)
      rw [he]
      exact (j x).val.property
    change Λ (N.mkQ (i φ)) = 0
    exact (congrArg Λ ((Submodule.Quotient.mk_eq_zero N).mpr hn)).trans (map_zero Λ)

end TestDuality

/-- Every logarithmic moment of a function integrable against all quasi-characters is
integrable against every real norm twist. -/
private theorem spectralLineJet_functional_moment
    {G : Type*} [CommGroup G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    (m : G →ₜ* ℝ≥0ˣ) (μ : Measure G) (χ : QuasiCharacter G) (u : G → ℂ)
    (hu : ∀ c : QuasiCharacter G, Integrable (fun g ↦ u g * c g) μ) (σ : ℝ) (n : ℕ) :
    Integrable (fun g ↦ u g * (Real.log ((m g).val : ℝ) : ℂ) ^ n *
      quasiCharacterNormTwist m.toMonoidHom m.continuous χ (σ : ℂ) g) μ := by
  have hlog : Measurable (fun g ↦ Real.log ((m g).val : ℝ)) :=
    (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)).measurable.log
  let tw (w : ℝ) := quasiCharacterNormTwist m.toMonoidHom m.continuous χ (w : ℂ)
  have h1 := (hu (tw (σ + 1))).norm
  have h2 := (hu (tw (σ - 1))).norm
  have hmeas : AEStronglyMeasurable (fun g ↦ u g * (Real.log ((m g).val : ℝ) : ℂ) ^ n *
      quasiCharacterNormTwist m.toMonoidHom m.continuous χ (σ : ℂ) g) μ := by
    have hL : AEStronglyMeasurable (fun g ↦ (Real.log ((m g).val : ℝ) : ℂ) ^ n) μ :=
      ((Complex.measurable_ofReal.comp hlog).pow_const n).aestronglyMeasurable
    refine ((hu (tw σ)).aestronglyMeasurable.mul hL).congr (ae_of_all _ fun g ↦ ?_)
    simp only [Pi.mul_apply, tw]
    ring
  refine ((h1.add h2).const_mul (n.factorial : ℝ)).mono' hmeas (ae_of_all _ fun g ↦ ?_)
  set L := Real.log ((m g).val : ℝ) with hLdef
  have hnorm (w : ℝ) : ‖quasiCharacterNormTwist m.toMonoidHom m.continuous χ (w : ℂ) g‖ =
      ‖χ g‖ * Real.exp (w * L) := by
    rw [quasiCharacterNormTwist_eq_exp, norm_mul, ← Complex.ofReal_mul, Complex.norm_exp_ofReal]
  have hpow : |L| ^ n ≤ n.factorial * (Real.exp L + Real.exp (-L)) := by
    have h := Real.pow_div_factorial_le_exp |L| (abs_nonneg L) n
    have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
    have habs : Real.exp |L| ≤ Real.exp L + Real.exp (-L) := by
      rcases abs_cases L with ⟨h', _⟩ | ⟨h', _⟩ <;> rw [h'] <;>
        linarith [Real.exp_pos L, Real.exp_pos (-L)]
    rw [div_le_iff₀ hf] at h
    nlinarith
  change ‖u g * (L : ℂ) ^ n * tw σ g‖ ≤
    (n.factorial : ℝ) * (‖u g * tw (σ + 1) g‖ + ‖u g * tw (σ - 1) g‖)
  simp only [tw, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, hnorm]
  have hA : 0 ≤ ‖u g‖ * (‖χ g‖ * Real.exp (σ * L)) := by positivity
  have e1 : Real.exp ((σ + 1) * L) = Real.exp (σ * L) * Real.exp L := by
    rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp ((σ - 1) * L) = Real.exp (σ * L) * Real.exp (-L) := by
    rw [← Real.exp_add]; ring_nf
  rw [e1, e2]
  calc ‖u g‖ * |L| ^ n * (‖χ g‖ * Real.exp (σ * L))
      = (‖u g‖ * (‖χ g‖ * Real.exp (σ * L))) * |L| ^ n := by ring
    _ ≤ (‖u g‖ * (‖χ g‖ * Real.exp (σ * L))) * (n.factorial * (Real.exp L + Real.exp (-L))) :=
        mul_le_mul_of_nonneg_left hpow hA
    _ = _ := by ring

/-- The pairing of a weighted function with a line jet is the derivative of its
norm-twisted Mellin integral at the shifted point. -/
private theorem spectralLineJet_functional_deriv
    {G : Type*} [CommGroup G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    (m : G →ₜ* ℝ≥0ˣ) (μ : Measure G) (χ : QuasiCharacter G) (u : G → ℂ)
    (hu : ∀ c : QuasiCharacter G, Integrable (fun g ↦ u g * c g) μ) (a t : ℝ) (k : ℕ) :
    ∫ g, modulationWeight m a u g *
        (quasiCharacterNormTwist m.toMonoidHom m.continuous χ (((0 : ℝ) : ℂ) + (t : ℂ) * Complex.I) g *
          (Real.log ((m g).val : ℝ) : ℂ) ^ k) ∂μ =
      iteratedDeriv k (fun w ↦ ∫ g, u g *
        quasiCharacterNormTwist m.toMonoidHom m.continuous χ w g ∂μ)
        ((a : ℂ) + (t : ℂ) * Complex.I) := by
  obtain ⟨_, _, hderiv⟩ := iteratedDeriv_normTwist_moment m μ χ
    (α := a - 1) (β := a + 1) (fun σ _ n ↦ spectralLineJet_functional_moment m μ χ u hu σ n) k
    (z := (a : ℂ) + (t : ℂ) * Complex.I) (by simp)
  rw [hderiv]
  refine integral_congr_ae (ae_of_all _ fun g ↦ ?_)
  have hpos : 0 < ((m g).val : ℝ) := NNReal.coe_pos.mpr (pos_of_ne_zero (m g).ne_zero)
  change (((((m g).val : ℝ) ^ a : ℝ)) : ℂ) * u g * _ = _
  dsimp only
  rw [quasiCharacterNormTwist_eq_exp, quasiCharacterNormTwist_eq_exp,
    Real.rpow_def_of_pos hpos, Complex.ofReal_exp, Complex.ofReal_mul]
  have e : Complex.exp (((a : ℂ) + (t : ℂ) * Complex.I) * (Real.log ((m g).val : ℝ) : ℂ)) =
      Complex.exp ((Real.log ((m g).val : ℝ) : ℂ) * (a : ℂ)) *
        Complex.exp ((((0 : ℝ) : ℂ) + (t : ℂ) * Complex.I) * (Real.log ((m g).val : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [e]
  ring


/-- Every function in the two-sided decay space is integrable against every quasi-character. -/
private theorem spectralLineJet_functional_integrable
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m) (hms : Surjective m)
    (μ : Measure G) [μ.IsHaarMeasure] (φ : ModulatedExponentialDecay m univ)
    (c : QuasiCharacter G) : Integrable (fun g ↦ φ.val g * c g) μ :=
  modulatedFourierMellin_integrable m univ hm ordConnected_univ univ_nonempty μ isOpen_univ hms φ
    ⟨c, mem_univ _⟩

/-- Paper: (10.2.1.9), p. 442. A surviving line jet acts on the Sobolev
space by the integral of the input against that jet. On a weighted exponential-
decay test this is precisely the derivative in the existing Mellin chart. -/
theorem spectralLineJet_functional (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    {a s : ℝ} (hs : 1 < s) (j : SpectralLineJetIndex χ a s) :
    ∃ Λ : StrongDual ℂ W(0, 0, s),
      (∀ f : W(0, 0, s), Integrable (fun g ↦ f g * lineJet(χ, j) g) μ𝔽 ∧
        Λ f = ∫ g, f g * lineJet(χ, j) g ∂μ𝔽) ∧
      ∀ (φ : ModulatedExponentialDecay m𝔽 univ) (f : W(0, 0, s)),
        (f : C𝔽 → ℂ) =ᵐ[μ𝔽] modulationWeight m𝔽 a φ.val →
        Λ f = iteratedDeriv j.val.2.2 (fun z ↦ modulatedFourierMellin m𝔽 univ hm𝔽 μ𝔽
          φ.val (ideleClassNormTwist (χ j.val.1) z)) (shift(a, j.val.2.1)) := by
  have hs0 : (0 : ℝ) ≤ s := by linarith
  let Td := (modulatedIntervalSobolev_dual m𝔽 hm𝔽 μ𝔽 0 0 s le_rfl hs0).exists.choose
  let u : W'(0, 0, s) := (spectralLineJet_memLp χ hs j).toLp (lineJet(χ, j))
  have hac : μ𝔽 ≪ L2μ'(0, 0, s) := by
    refine withDensity_absolutelyContinuous' ?_ (ae_of_all _ fun g ↦ ?_)
    · exact ((continuous_intervalSobolevDensity' 0 0 s).measurable.comp
        (NNReal.continuous_coe.comp (Units.continuous_val.comp
          (isProperMap_ideleClassNorm F).continuous)).measurable.log).inv.ennreal_ofReal.aemeasurable
    · exact ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr (intervalSobolevDensity_pos 0 0 s _))
  have hae : (u : C𝔽 → ℂ) =ᵐ[μ𝔽] lineJet(χ, j) := hac.ae_le (MemLp.coeFn_toLp _)
  have hpair (f : W(0, 0, s)) : Integrable (fun g ↦ f g * lineJet(χ, j) g) μ𝔽 ∧
      Td.symm u f = ∫ g, f g * lineJet(χ, j) g ∂μ𝔽 := by
    have h := spectralSobolevPairing_dual le_rfl hs0 (Td.symm u) f
    have hTu : Td (Td.symm u) = u := Td.apply_symm_apply u
    have hc : (fun g ↦ f g * Td (Td.symm u) g) =ᵐ[μ𝔽] fun g ↦ f g * lineJet(χ, j) g := by
      rw [hTu]
      exact hae.mono fun g hg ↦ congrArg (f g * ·) hg
    exact ⟨h.1.congr hc, h.2.trans (integral_congr_ae hc)⟩
  refine ⟨Td.symm u, hpair, fun φ f hf ↦ ?_⟩
  let χq : QuasiCharacter C𝔽 :=
    (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp (χ j.val.1)
  have hc : (fun g ↦ f g * lineJet(χ, j) g) =ᵐ[μ𝔽]
      fun g ↦ modulationWeight m𝔽 a φ.val g *
        (quasiCharacterNormTwist (m𝔽).toMonoidHom (m𝔽).continuous χq (shift(0, j.val.2.1)) g *
          (Real.log ((m𝔽 g).val : ℝ) : ℂ) ^ j.val.2.2) :=
    hf.mono fun g hg ↦ by dsimp only; rw [hg]; rfl
  have key := spectralLineJet_functional_deriv m𝔽 μ𝔽 χq φ.val
    (spectralLineJet_functional_integrable m𝔽 hm𝔽 hms𝔽 μ𝔽 φ) a j.val.2.1 j.val.2.2
  have hF : (fun z ↦ modulatedFourierMellin m𝔽 univ hm𝔽 μ𝔽 φ.val
      (ideleClassNormTwist (χ j.val.1) z)) = fun w ↦ ∫ g, φ.val g *
        quasiCharacterNormTwist (m𝔽).toMonoidHom (m𝔽).continuous χq w g ∂μ𝔽 :=
    funext fun z ↦ modulatedFourierMellin_univ m𝔽 hm𝔽 μ𝔽 _ _
  rw [(hpair f).2, integral_congr_ae hc, hF]
  exact key

section

universe u v

/-- Integrating scalar multiples of a commutative action preserves every eigenspace. -/
private theorem spectral_integrated_action_eigenvector
    {G : Type u} [CommGroup G] [MeasurableSpace G] (μ : Measure G)
    {V : Type v} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (ρ : G →* (V →L[ℂ] V)) (f : G → ℂ) (u v : V)
    (hv : HasPettisIntegral (.positive μ) (fun g ↦ f g • ρ g u) v)
    (k : G) (c : ℂ) (hu : ρ k u = c • u) : ρ k v = c • v := by
  have hev (δ : StrongDual ℂ V) : δ v = ∫ g, δ (f g • ρ g u) ∂μ :=
    congrArg (fun z : PettisWeakCompletion V ↦
      (show Module.Dual ℂ (StrongDual ℂ V) from z) δ) hv.2
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2
  intro δ
  have he (g : G) : ρ k (f g • ρ g u) = c • (f g • ρ g u) := by
    rw [map_smul]
    have hc : ρ k (ρ g u) = ρ g (ρ k u) := by
      change (ρ k * ρ g) u = (ρ g * ρ k) u
      rw [← map_mul, ← map_mul, mul_comm k g]
    rw [hc, hu, map_smul, smul_comm]
  calc
    δ (ρ k v) = ∫ g, δ (ρ k (f g • ρ g u)) ∂μ :=
      hev (δ.comp (ρ k))
    _ = ∫ g, c • δ (f g • ρ g u) ∂μ :=
      integral_congr_ae (.of_forall fun g ↦ (congrArg δ (he g)).trans (map_smul δ c _))
    _ = c • δ v := by rw [integral_smul, ← hev δ]
    _ = δ (c • v) := (map_smul δ c v).symm

end

/-- Paper: (10.2.1.10), pp. 442–443. The band-limited approximate unit acts
by convolution on the fixed norm-one isotype and converges there strongly.
Deviation: The Fourier band is centered on the inverse lift for the
left-translation convention of §9.3. -/
theorem exists_spectralLineIsotypeConvolution (χ : PontryaginDual C𝔽) {s : ℝ} (hs : 0 ≤ s) :
    let hI : (0 : ℝ) ≤ 0 := le_rfl
    let E := Wω(hI, hs, χ.comp restriction)
    let A := (existsUnique_schwartzBruhat_zeroLineAction μ𝔽 m𝔽 s hs).exists.choose
    ∃ (φ : ℕ → SchwartzBruhat C𝔽) (P : ℕ → (E →L[ℂ] E)),
      (∀ n, ‖A (φ n)‖ ≤ 2) ∧
      (∀ n (k : C₁) g, (φ n) (k.val⁻¹ * g) = (χ k.val : ℂ) * (φ n) g) ∧
      (∀ n, tsupport (lcaFourier μ𝔽 (φ n)) ⊆
        modulatedFrequencyBand m𝔽 χ⁻¹ (-(n : ℝ)) n) ∧
      (∀ n (f : E), (P n f).val = A (φ n) f.val) ∧
      ∀ f : E, Tendsto (fun n ↦ P n f) atTop (𝓝 f) := by
  intro hI E A
  let τ := hardySobolevTranslation μ𝔽 m𝔽 0 0 s hI hs
  let B := (existsUnique_singletonDecay_lineAction μ𝔽 m𝔽 hm𝔽 hms𝔽 0 s hs).exists.choose
  have hB := (existsUnique_singletonDecay_lineAction μ𝔽 m𝔽 hm𝔽 hms𝔽 0 s hs).exists.choose_spec.1
  have hA := (existsUnique_schwartzBruhat_zeroLineAction μ𝔽 m𝔽 s hs).exists.choose_spec
  let e := (modulatedExponentialDecay_singleton_schwartz m𝔽 hm𝔽 hms𝔽 0).choose
  have he (f : ModulatedExponentialDecay m𝔽 {0}) : (e f : C𝔽 → ℂ) = f.val := by
    exact ((modulatedExponentialDecay_singleton_schwartz m𝔽 hm𝔽 hms𝔽 0).choose_spec f).trans
      (modulationWeight_zero m𝔽 f.val)
  have hAB (f : ModulatedExponentialDecay m𝔽 {0}) : A (e f) = B f := by
    apply ContinuousLinearMap.ext
    intro u
    have hp : (fun g ↦ (e f).val g • τ g u) = (fun g ↦ f.val g • τ g u) :=
      funext fun g ↦ congrArg (fun z : ℂ ↦ z • τ g u) (congrFun (he f) g)
    have hP : HasPettisIntegral (.positive μ𝔽) (fun g ↦ f.val g • τ g u) (A (e f) u) :=
      hp ▸ hA (e f) u
    exact hP.unique (hB f u)
  let φ := (exists_singletonDecay_isotype_approximation μ𝔽 m𝔽 hm𝔽 hms𝔽 0 s hs χ⁻¹).choose
  have hφ := (exists_singletonDecay_isotype_approximation μ𝔽 m𝔽 hm𝔽 hms𝔽 0 s hs χ⁻¹).choose_spec
  have hmem (n : ℕ) (u : E) : A (e (φ n)) u.val ∈ E := by
    apply (mem_actionIsotype _ _ _).mpr
    intro k
    exact spectral_integrated_action_eigenvector μ𝔽 τ (e (φ n)).val u.val
      (A (e (φ n)) u.val) (hA (e (φ n)) u.val) k.val (χ k.val : ℂ)
      ((mem_actionIsotype _ _ _).mp u.property k)
  let P (n : ℕ) : E →L[ℂ] E :=
    ((A (e (φ n))).comp E.subtypeL).codRestrict E (hmem n)
  refine ⟨fun n ↦ e (φ n), P, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    rw [hAB]
    exact hφ.1 n
  · intro n k g
    have hchar : star ((χ⁻¹) k.val : ℂ) = (χ k.val : ℂ) := by
      change star (((χ k.val)⁻¹ : Circle) : ℂ) = _
      rw [Circle.coe_inv_eq_conj]
      exact star_star _
    calc
      e (φ n) (k.val⁻¹ * g) = (φ n).val (k.val⁻¹ * g) := congrFun (he (φ n)) _
      _ = star ((χ⁻¹) k.val : ℂ) * (φ n).val g := hφ.2.1 n k g
      _ = (χ k.val : ℂ) * e (φ n) g := congrArg₂ (· * ·) hchar (congrFun (he (φ n)) g).symm
  · intro n
    simpa only [he, modulationWeight_zero] using hφ.2.2.1 n
  · intro n f
    rfl
  · intro f
    apply tendsto_subtype_rng.mpr
    change Tendsto (fun n ↦ A (e (φ n)) f.val) atTop (𝓝 f.val)
    have h : Tendsto (fun n ↦ B (φ n) f.val) atTop (𝓝 f.val) :=
      hφ.2.2.2 ⟨f.val, by simpa only [inv_inv] using f.property⟩
    exact h.congr' (Filter.Eventually.of_forall fun n ↦
      congrArg (fun T : W(0, 0, s) →L[ℂ] W(0, 0, s) ↦ T f.val) (hAB (φ n)).symm)

private theorem spectralJet_lp_norm_sq {μ : Measure C𝔽} (u : Lp ℂ 2 μ) :
    ‖u‖ ^ 2 = ∫ g : C𝔽, ‖u g‖ ^ 2 ∂μ := by
  have hre : (inner ℂ u u).re = ‖u‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) u
  rw [← hre, L2.inner_def]
  have hre_int : (∫ g : C𝔽, inner ℂ (u g) (u g) ∂μ).re =
      ∫ g : C𝔽, (inner ℂ (u g) (u g)).re ∂μ :=
    (Complex.reCLM.integral_comp_comm (L2.integrable_inner u u)).symm
  rw [hre_int]
  refine integral_congr_ae (ae_of_all _ fun g ↦ ?_)
  exact inner_self_eq_norm_sq (𝕜 := ℂ) (u g)

private theorem spectralZeroJet_continuous (χ : PontryaginDual C𝔽) (b t : ℝ) (k : ℕ) :
    Continuous (spectralZeroJet χ b t k) :=
  (ideleClassNormTwist χ (((b : ℝ) : ℂ) + (t : ℂ) * Complex.I)).continuous.mul
    ((Complex.continuous_ofReal.comp (continuous_logModule' m𝔽)).pow k)

private theorem spectralZeroJet_norm_sq (χ : PontryaginDual C𝔽) (b t : ℝ) (k : ℕ) (g : C𝔽) :
    ‖spectralZeroJet χ b t k g‖ ^ 2 = Real.exp (2 * b * logNorm g) * (logNorm g) ^ (2 * k) := by
  have hpos : 0 < ((ideleClassNorm F g).val : ℝ) :=
    NNReal.coe_pos.mpr (Units.zero_lt (ideleClassNorm F g))
  have htwist : ‖ideleClassNormTwist χ (((b : ℝ) : ℂ) + (t : ℂ) * Complex.I) g‖ =
      Real.exp (b * logNorm g) := by
    change ‖(χ g : ℂ) *
      (((ideleClassNorm F g).val : ℝ) : ℂ) ^ (((b : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ = _
    rw [norm_mul, Circle.norm_coe, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Real.rpow_def_of_pos hpos,
      mul_comm]
  change ‖ideleClassNormTwist χ (((b : ℝ) : ℂ) + (t : ℂ) * Complex.I) g *
    (logNorm g : ℂ) ^ k‖ ^ 2 = _
  rw [norm_mul, htwist, norm_pow, Complex.norm_real, Real.norm_eq_abs, mul_pow]
  have hexp : Real.exp (b * logNorm g) ^ 2 = Real.exp (2 * b * logNorm g) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hpow : (|logNorm g| ^ k) ^ 2 = (logNorm g) ^ (2 * k) := by
    calc
      (|logNorm g| ^ k) ^ 2 = (|logNorm g| ^ 2) ^ k := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm k 2]
      _ = ((logNorm g) ^ 2) ^ k := congrArg (fun y : ℝ ↦ y ^ k) (sq_abs (logNorm g))
      _ = (logNorm g) ^ (2 * k) := (pow_mul _ _ _).symm
  rw [hexp, hpow]

private theorem symmIntervalSobolevDensity_eq {α : ℝ} (hα : 0 ≤ α) (s x : ℝ) :
    intervalSobolevDensity (-α) α s x = Real.exp (2 * α * |x|) * (1 + x ^ 2) ^ (s / 2) := by
  unfold intervalSobolevDensity
  congr 1
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx, max_eq_right]
    exact Real.exp_le_exp.mpr (by nlinarith)
  · rw [abs_of_nonpos hx, max_eq_left]
    · congr 1
      ring
    · exact Real.exp_le_exp.mpr (by nlinarith)

private theorem symmIntervalSobolevDensity_pos {α : ℝ} (hα : 0 ≤ α) (s x : ℝ) :
    0 < intervalSobolevDensity (-α) α s x := by
  rw [symmIntervalSobolevDensity_eq hα]
  exact mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (by positivity) _)

private theorem symmIntervalSobolevDensity_inv_continuous {α : ℝ} (hα : 0 ≤ α) (s : ℝ) :
    Continuous (fun g : C𝔽 ↦ (intervalSobolevDensity (-α) α s (logNorm g))⁻¹) := by
  have hρ : Continuous (fun g : C𝔽 ↦ intervalSobolevDensity (-α) α s (logNorm g)) := by
    have heq : (fun g : C𝔽 ↦ intervalSobolevDensity (-α) α s (logNorm g)) =
        fun g : C𝔽 ↦ Real.exp (2 * α * |logNorm g|) * (1 + (logNorm g) ^ 2) ^ (s / 2) :=
      funext fun g ↦ symmIntervalSobolevDensity_eq hα s (logNorm g)
    rw [heq]
    exact (Real.continuous_exp.comp (continuous_const.mul (continuous_logModule' m𝔽).abs)).mul
      (((continuous_const : Continuous (fun _ : C𝔽 ↦ (1 : ℝ))).add
        ((continuous_logModule' m𝔽).pow 2)).rpow_const fun g ↦ Or.inl (by
          change (1 : ℝ) + (logNorm g) ^ 2 ≠ 0
          positivity))
  exact hρ.inv₀ fun g ↦ (symmIntervalSobolevDensity_pos hα s (logNorm g)).ne'

private theorem pow_mul_rpow_inv_continuous (k : ℕ) (s : ℝ) :
    Continuous (fun x : ℝ ↦ x ^ (2 * k) * ((1 + x ^ 2) ^ (s / 2))⁻¹) :=
  (continuous_id.pow (2 * k)).mul
    (((continuous_const.add (continuous_id.pow 2)).rpow_const fun x ↦
        Or.inl (by change (1 : ℝ) + x ^ 2 ≠ 0; positivity)).inv₀ fun x ↦
      (Real.rpow_pos_of_pos (by change (0 : ℝ) < 1 + x ^ 2; positivity) _).ne')

private theorem spectralLineJet_integral_pos {s : ℝ} (hs : 1 < s) {k : ℕ}
    (hkN : k < Nat.ceil ((s - 1) / 2)) :
    0 < ∫ g : C𝔽, (logNorm g) ^ (2 * k) * ((1 + (logNorm g) ^ 2) ^ (s / 2))⁻¹ ∂μ𝔽 := by
  have hk' : (k : ℝ) < (s - 1) / 2 := Nat.lt_ceil.mp hkN
  have hk : 2 * (k : ℝ) + 1 < s := by linarith
  let ν : Measure C𝔽 := canonicalModulatedHaar m𝔽 hm𝔽
  let : ν.IsHaarMeasure := (existsUnique_canonicalModulatedHaar m𝔽 hm𝔽).exists.choose_spec.1
  let fk : ℝ → ℝ := fun x ↦ x ^ (2 * k) * ((1 + x ^ 2) ^ (s / 2))⁻¹
  have hfk_int : Integrable fk volume := integrable_pow_mul_rpow_inv hk
  have hmp : MeasurePreserving (fun g : C𝔽 ↦ logNorm g) ν volume :=
    sobolev_log_preserving m𝔽 hm𝔽 hms𝔽
  have hlogm : AEMeasurable (fun g : C𝔽 ↦ logNorm g) ν :=
    (continuous_logModule' m𝔽).measurable.aemeasurable
  have hν_eq : ∫ g : C𝔽, fk (logNorm g) ∂ν = ∫ x : ℝ, fk x ∂volume := by
    rw [← hmp.map_eq,
      integral_map hlogm (pow_mul_rpow_inv_continuous k s).aestronglyMeasurable]
  have hvol_pos : 0 < ∫ x : ℝ, fk x ∂volume := by
    let c : ℝ := ((5 : ℝ) ^ (s / 2))⁻¹
    have hc : 0 < c := inv_pos.mpr (Real.rpow_pos_of_pos (by norm_num) _)
    have hind_int : Integrable ((Icc (1 : ℝ) 2).indicator fun _ ↦ c) volume :=
      (integrableOn_const (by simp)).integrable_indicator measurableSet_Icc
    have hle : ∀ x : ℝ, (Icc (1 : ℝ) 2).indicator (fun _ ↦ c) x ≤ fk x := by
      intro x
      by_cases hx : x ∈ Icc (1 : ℝ) 2
      · rw [indicator_of_mem hx]
        have hpow : (1 : ℝ) ≤ x ^ (2 * k) := one_le_pow₀ hx.1
        have hbase : 1 + x ^ 2 ≤ 5 := by nlinarith [hx.1, hx.2]
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

/-- Paper: Proposition 10.2.1.3 and (10.2.1.12), p. 443. A single annulus
contains all the a-line jet classes.
Deviation: Use the truncated multiplicity intended by the reference to
(10.2.1.6). The lower bound asserts disjointness from the open ball, which
also makes sense for an empty zero set. -/
theorem spectralLineJet_annulus (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice χ) {a s : ℝ} (hs : 1 < s) :
    ∃ C : ℝ, 0 < C ∧ ∀ j : SpectralLineJetIndex χ a s,
      let u := (spectralLineJet_memLp χ hs j).toLp (lineJet(χ, j))
      C⁻¹ ≤ ‖u‖ ∧ ‖u‖ ≤ C := by
  let N : ℕ := Nat.ceil ((s - 1) / 2)
  let I : ℕ → ℝ := fun k ↦
    ∫ g : C𝔽, (logNorm g) ^ (2 * k) * ((1 + (logNorm g) ^ 2) ^ (s / 2))⁻¹ ∂μ𝔽
  let r : ℕ → ℝ := fun k ↦ Real.sqrt (I k)
  have hnorm_sq : ∀ j : SpectralLineJetIndex χ a s,
      ‖(spectralLineJet_memLp χ hs j).toLp (lineJet(χ, j))‖ ^ 2 = I j.val.2.2 := by
    intro j
    let u := (spectralLineJet_memLp χ hs j).toLp (lineJet(χ, j))
    have h1 : ‖u‖ ^ 2 = ∫ g : C𝔽, ‖u g‖ ^ 2 ∂(L2μ'(0, 0, s)) := spectralJet_lp_norm_sq u
    have h2 : ∫ g : C𝔽, ‖u g‖ ^ 2 ∂(L2μ'(0, 0, s)) =
        ∫ g : C𝔽, (logNorm g) ^ (2 * j.val.2.2) ∂(L2μ'(0, 0, s)) := by
      refine integral_congr_ae ?_
      filter_upwards [MemLp.coeFn_toLp (spectralLineJet_memLp χ hs j)] with g hg
      rw [hg, spectralZeroJet_norm_sq]
      simp
    have h3 : ∫ g : C𝔽, (logNorm g) ^ (2 * j.val.2.2) ∂(L2μ'(0, 0, s)) = I j.val.2.2 := by
      have hdens : Continuous (fun g : C𝔽 ↦ (intervalSobolevDensity 0 0 s (logNorm g))⁻¹) := by
        simpa only [neg_zero] using symmIntervalSobolevDensity_inv_continuous (F := F) le_rfl s
      rw [integral_withDensity_eq_integral_toReal_smul hdens.measurable.ennreal_ofReal
        (ae_of_all μ𝔽 fun _ ↦ ENNReal.ofReal_lt_top)]
      refine integral_congr_ae (ae_of_all μ𝔽 fun g ↦ ?_)
      dsimp only
      have hdeq : (intervalSobolevDensity 0 0 s (logNorm g))⁻¹ =
          ((1 + (logNorm g) ^ 2) ^ (s / 2))⁻¹ := by
        simp only [intervalSobolevDensity, mul_zero, zero_mul, Real.exp_zero, max_self, one_mul]
      rw [smul_eq_mul, hdeq,
        ENNReal.toReal_ofReal (inv_nonneg.mpr (Real.rpow_pos_of_pos (by positivity) _).le),
        mul_comm]
    exact h1.trans (h2.trans h3)
  let C : ℝ := 1 + ∑ k ∈ Finset.range N, (r k + (r k)⁻¹)
  have hC_pos : 0 < C := by
    have hsum_nonneg : 0 ≤ ∑ k ∈ Finset.range N, (r k + (r k)⁻¹) :=
      Finset.sum_nonneg fun k _ ↦ add_nonneg (Real.sqrt_nonneg _) (inv_nonneg.mpr (Real.sqrt_nonneg _))
    linarith
  refine ⟨C, hC_pos, fun j ↦ ?_⟩
  have hjN : j.val.2.2 ∈ Finset.range N :=
    Finset.mem_range.mpr (lt_of_lt_of_le j.property (min_le_right _ _))
  have hr_pos : 0 < r j.val.2.2 :=
    Real.sqrt_pos.mpr (spectralLineJet_integral_pos hs (Finset.mem_range.mp hjN))
  have hnorm_eq : ‖(spectralLineJet_memLp χ hs j).toLp (lineJet(χ, j))‖ = r j.val.2.2 := by
    rw [← Real.sqrt_sq (norm_nonneg _), hnorm_sq j]
  have hterm_le : r j.val.2.2 + (r j.val.2.2)⁻¹ ≤ C := by
    have h1 : r j.val.2.2 + (r j.val.2.2)⁻¹ ≤ ∑ k ∈ Finset.range N, (r k + (r k)⁻¹) :=
      Finset.single_le_sum
        (fun k _ ↦ add_nonneg (Real.sqrt_nonneg _) (inv_nonneg.mpr (Real.sqrt_nonneg _))) hjN
    linarith
  dsimp only
  rw [hnorm_eq]
  refine ⟨?_, by linarith [inv_pos.mpr hr_pos]⟩
  have hinv_le : (r j.val.2.2)⁻¹ ≤ C := by linarith
  calc
    C⁻¹ ≤ ((r j.val.2.2)⁻¹)⁻¹ := inv_anti₀ (inv_pos.mpr hr_pos) hinv_le
    _ = r j.val.2.2 := inv_inv _

/-- Paper: Terminology 10.2.1.2, p. 444. A regular family has norms bounded
away from zero. -/
def IsRegularSpectralFamily {ι E : Type*} [Norm E] (x : ι → E) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ i, c ≤ ‖x i‖

/-- Paper: Terminology 10.2.1.2, p. 444. A family is normalized if its
norms are bounded above and the family is regular. -/
def IsNormalizedSpectralFamily {ι E : Type*} [Norm E] (x : ι → E) : Prop :=
  (∃ C : ℝ, ∀ i, ‖x i‖ ≤ C) ∧ IsRegularSpectralFamily x

/-- Paper: Terminology 10.2.1.2, p. 444. On normed-space sequences the
two conditions agree with the existing §4.1 terminology. -/
theorem spectralFamily_regular_normalized_iff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (x : ℕ → E) :
    (IsRegularSpectralFamily x ↔ SchauderBasis.IsRegular x) ∧
    (IsNormalizedSpectralFamily x ↔ SchauderBasis.IsNormalized x) := by
  have hr : IsRegularSpectralFamily x ↔ SchauderBasis.IsRegular x := by
    constructor
    · rintro ⟨c, hc, h⟩
      exact ⟨Metric.ball 0 c, Metric.ball_mem_nhds _ hc, fun n hn ↦
        (h n).not_gt (by simpa only [Metric.mem_ball, dist_zero_right] using hn)⟩
    · rintro ⟨U, hU, hx⟩
      obtain ⟨c, hc, hball⟩ := Metric.mem_nhds_iff.mp hU
      refine ⟨c, hc, fun n ↦ le_of_not_gt fun hn ↦ hx n (hball ?_)⟩
      simpa only [Metric.mem_ball, dist_zero_right] using hn
  refine ⟨hr, ?_⟩
  simp only [IsNormalizedSpectralFamily, SchauderBasis.IsNormalized, ← hr,
    NormedSpace.isVonNBounded_iff' ℂ, Set.forall_mem_range]
  exact and_comm

/-- Paper: Terminology 10.2.1.2, p. 444. A nonzero vector defines a regular
and normalized singleton family.
Deviation: Sanity check for the two predicates. -/
theorem spectralFamily_singleton_normalized {E : Type*} [NormedAddCommGroup E] (x : E)
    (_hx : x ≠ 0) : IsNormalizedSpectralFamily (fun _ : Unit ↦ x) := by
  exact ⟨⟨‖x‖, fun _ ↦ le_rfl⟩, ‖x‖, norm_pos_iff.mpr _hx, fun _ ↦ le_rfl⟩

-- TODO(paper-gap): The general claim about the Schauder property on p. 444
-- lacks a proof. The primal normalization invoked again on p. 451 is false:
-- close simple critical-line zeta zeros give jets at distance tending to zero,
-- so the corresponding biorthogonal vector norms are unbounded (ERRATA R5).

section BandProjections

attribute [local instance] instDualMeasurableSpaceSec3

/-- Orthogonal projections onto closures of subspaces converge strongly whenever each
vector has a convergent sequence of approximants in the corresponding subspaces. -/
private theorem spectralLineIsotype_bandProjections_of_approximants
    {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]
    (S : ℕ → Submodule ℂ Q)
    (happrox : ∀ q : Q, ∃ y : ℕ → Q,
      (∀ n, y n ∈ S n) ∧ Tendsto y atTop (𝓝 q)) :
    ∃ P : ℕ → (Q →L[ℂ] Q),
      (∀ n, Set.range (P n) = closure (S n : Set Q)) ∧
      (∀ n q y, y ∈ closure (S n : Set Q) → ‖q - P n q‖ ≤ ‖q - y‖) ∧
      ∀ q, Tendsto (fun n ↦ P n q) atTop (𝓝 q) := by
  let C (n : ℕ) := (S n).topologicalClosure
  let : ∀ n, CompleteSpace (C n) := fun n ↦
    (Submodule.isClosed_topologicalClosure (S n)).completeSpace_coe
  let P (n : ℕ) : Q →L[ℂ] Q := (C n).starProjection
  have hmin (n : ℕ) (q y : Q) (hy : y ∈ closure (S n : Set Q)) :
      ‖q - P n q‖ ≤ ‖q - y‖ := by
    change ‖q - (C n).starProjection q‖ ≤ ‖q - y‖
    rw [Submodule.starProjection_minimal]
    exact ciInf_le ⟨0, Set.forall_mem_range.mpr fun _ ↦ norm_nonneg _⟩
      (⟨y, hy⟩ : C n)
  refine ⟨P, ?_, hmin, ?_⟩
  · intro n
    change ((C n).starProjection.range : Set Q) = closure (S n : Set Q)
    rw [Submodule.range_starProjection]
    rfl
  · intro q
    obtain ⟨y, hy, hlim⟩ := happrox q
    apply tendsto_iff_dist_tendsto_zero.mpr
    refine squeeze_zero (fun n ↦ dist_nonneg) (fun n ↦ ?_)
      (tendsto_iff_dist_tendsto_zero.mp hlim)
    calc
      dist (P n q) q = ‖q - P n q‖ := by
        simpa only [dist_eq_norm] using norm_sub_rev (P n q) q
      _ ≤ ‖q - y n‖ := hmin n q (y n) (subset_closure (hy n))
      _ = dist (y n) q := by
        simpa only [dist_eq_norm] using norm_sub_rev q (y n)

/-- A Fourier band defines a submodule, and its image under a linear quotient map
agrees with the description using any almost-everywhere equal L² representative. -/
private theorem spectralLineIsotype_bandProjections_band_submodule
    {X Y E Q : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [AddCommGroup E] [Module ℂ E] [AddCommGroup Q] [Module ℂ Q]
    (μ : Measure X) (ν : Measure Y)
    (r : E → X → ℂ) (J : E →ₗ[ℂ] Lp ℂ 2 μ)
    (hJ : ∀ f, (J f : X → ℂ) =ᵐ[μ] r f)
    (q : E →ₗ[ℂ] Q) (U : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 ν) (band : Set Y) :
    ∃ S : Submodule ℂ Q, (S : Set Q) =
      {z : Q | ∃ f : E, z = q f ∧ ∃ u : Lp ℂ 2 μ,
        (u : X → ℂ) =ᵐ[μ] r f ∧ ∀ᵐ ψ ∂ν, ψ ∉ band → U u ψ = 0} := by
  let A : Submodule ℂ (Lp ℂ 2 ν) := {
    carrier := {v | ∀ᵐ ψ ∂ν, ψ ∉ band → v ψ = 0}
    zero_mem' := by
      filter_upwards [Lp.coeFn_zero (E := ℂ) (p := 2) (μ := ν)] with ψ hψ
      exact fun _ ↦ hψ
    add_mem' := by
      intro v w hv hw
      change ∀ᵐ ψ ∂ν, ψ ∉ band → (v + w) ψ = 0
      filter_upwards [Lp.coeFn_add v w, hv, hw] with ψ hψ hvψ hwψ
      intro hψband
      rw [hψ, Pi.add_apply, hvψ hψband, hwψ hψband, add_zero]
    smul_mem' := by
      intro c v hv
      change ∀ᵐ ψ ∂ν, ψ ∉ band → (c • v) ψ = 0
      filter_upwards [Lp.coeFn_smul c v, hv] with ψ hψ hvψ
      intro hψband
      rw [hψ, Pi.smul_apply, hvψ hψband, smul_zero]
  }
  refine ⟨(A.comap (U.comp J)).map q, ?_⟩
  ext z
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨f, rfl, J f, hJ f, hf⟩
  · rintro ⟨f, rfl, u, hu, hUu⟩
    refine ⟨f, ?_, rfl⟩
    have heq : u = J f := Lp.ext (hu.trans (hJ f).symm)
    change ∀ᵐ ψ ∂ν, ψ ∉ band → U (J f) ψ = 0
    simpa only [heq] using hUu

/-- Set-valued version of the projection argument, allowing the Fourier-band submodules
to be constructed independently from their concrete sets. -/
private theorem spectralLineIsotype_bandProjections_of_sets
    {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]
    (B : ℕ → Set Q) (hsub : ∀ n, ∃ S : Submodule ℂ Q, (S : Set Q) = B n)
    (happrox : ∀ q : Q, ∃ y : ℕ → Q,
      (∀ n, y n ∈ B n) ∧ Tendsto y atTop (𝓝 q)) :
    ∃ P : ℕ → (Q →L[ℂ] Q),
      (∀ n, Set.range (P n) = closure (B n)) ∧
      (∀ n q y, y ∈ closure (B n) → ‖q - P n q‖ ≤ ‖q - y‖) ∧
      ∀ q, Tendsto (fun n ↦ P n q) atTop (𝓝 q) := by
  choose S hS using hsub
  have happrox' : ∀ q : Q, ∃ y : ℕ → Q,
      (∀ n, y n ∈ S n) ∧ Tendsto y atTop (𝓝 q) := by
    intro q
    obtain ⟨y, hy, hlim⟩ := happrox q
    refine ⟨y, fun n ↦ ?_, hlim⟩
    change y n ∈ (S n : Set Q)
    rw [hS n]
    exact hy n
  obtain ⟨P, hrange, hmin, hlim⟩ :=
    spectralLineIsotype_bandProjections_of_approximants S happrox'
  refine ⟨P, fun n ↦ ?_, fun n q y hy ↦ ?_, hlim⟩
  · simpa only [hS n] using hrange n
  · apply hmin n q y
    simpa only [hS n] using hy

/-- A surjective continuous linear image of supported approximants admits strongly
convergent orthogonal projections onto the closures of the corresponding bands. -/
private theorem spectralLineIsotype_bandProjections_of_supported_approximants
    {X Y E Q : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]
    (μ : Measure X) (ν : Measure Y)
    (r : E → X → ℂ) (J : E →ₗ[ℂ] Lp ℂ 2 μ)
    (hJ : ∀ f, (J f : X → ℂ) =ᵐ[μ] r f)
    (q : E →L[ℂ] Q) (hq : Surjective q)
    (U : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 ν) (band : ℕ → Set Y)
    (R : ℕ → E → E)
    (hsupport : ∀ n f, ∀ᵐ ψ ∂ν, ψ ∉ band n → U (J (R n f)) ψ = 0)
    (hlim : ∀ f, Tendsto (fun n ↦ R n f) atTop (𝓝 f)) :
    let B (n : ℕ) := {z : Q | ∃ f : E, z = q f ∧ ∃ u : Lp ℂ 2 μ,
      (u : X → ℂ) =ᵐ[μ] r f ∧ ∀ᵐ ψ ∂ν, ψ ∉ band n → U u ψ = 0}
    ∃ P : ℕ → (Q →L[ℂ] Q),
      (∀ n, Set.range (P n) = closure (B n)) ∧
      (∀ n z y, y ∈ closure (B n) → ‖z - P n z‖ ≤ ‖z - y‖) ∧
      ∀ z, Tendsto (fun n ↦ P n z) atTop (𝓝 z) := by
  intro B
  have hmem (n : ℕ) (f : E) : q (R n f) ∈ B n :=
    ⟨R n f, rfl, J (R n f), hJ (R n f), hsupport n f⟩
  have happrox (z : Q) : ∃ y : ℕ → Q,
      (∀ n, y n ∈ B n) ∧ Tendsto y atTop (𝓝 z) := by
    obtain ⟨f, rfl⟩ := hq z
    refine ⟨fun n ↦ q (R n f), fun n ↦ hmem n f, ?_⟩
    exact q.continuous.continuousAt.tendsto.comp (hlim f)
  have hsub (n : ℕ) : ∃ S : Submodule ℂ Q, (S : Set Q) = B n := by
    exact spectralLineIsotype_bandProjections_band_submodule μ ν r J hJ
      q.toLinearMap U (band n)
  exact spectralLineIsotype_bandProjections_of_sets B hsub happrox

private theorem spectralLineIsotype_bandProjections_support_closed
    {X : Type*} [MeasurableSpace X] (ν : Measure X) (S : Set X)
    (hS : MeasurableSet S) :
    IsClosed {f : Lp ℂ 2 ν | ∀ᵐ x ∂ν, x ∉ S → f x = 0} := by
  obtain ⟨P, -, hP⟩ := hardySobolevCutoff_spec (μ := ν) hS
  have hset : {f : Lp ℂ 2 ν | ∀ᵐ x ∂ν, x ∉ S → f x = 0} =
      {f : Lp ℂ 2 ν | P f = f} := by
    ext f
    constructor
    · intro hf
      apply Lp.ext
      filter_upwards [(hP f).2.2, hf] with x hx hfx
      rw [hx]
      by_cases hxs : x ∈ S
      · exact Set.indicator_of_mem hxs _
      · rw [Set.indicator_of_notMem hxs, hfx hxs]
    · intro hf
      filter_upwards [(hP f).2.2] with x hx
      intro hxs
      rw [hf] at hx
      exact hx.trans (Set.indicator_of_notMem hxs _)
  rw [hset]
  exact isClosed_eq P.continuous continuous_id

private theorem spectralLineIsotype_bandProjections_dense_integrable
    {G : Type*} [TopologicalSpace G] [T2Space G] [LocallyCompactSpace G]
    [NormalSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ w : Measure G)
    [IsLocallyFiniteMeasure μ] [w.Regular] (hle : μ ≤ w) :
    Dense {u : Lp ℂ 2 w | Integrable (u : G → ℂ) μ} := by
  intro u
  apply EMetric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨r, hr, hlt⟩ := exists_between hε
  obtain ⟨f, hc, he, hf, hm⟩ :=
    (Lp.memLp u).exists_hasCompactSupport_eLpNorm_sub_le (by simp) hr.ne'
  refine ⟨hm.toLp f,
    (hf.integrable_of_hasCompactSupport hc).congr (ae_mono hle hm.coeFn_toLp.symm), ?_⟩
  rw [Lp.edist_def, eLpNorm_congr_ae (EventuallyEq.rfl.sub hm.coeFn_toLp)]
  exact he.trans_lt hlt

private theorem spectralLineIsotype_bandProjections_convolution_support
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (ν : Measure (PontryaginDual G))
    (hν : IsLCAPlancherelMeasure μ ν) (w : Measure G) [w.Regular]
    (hle : μ ≤ w) (J : Lp ℂ 2 w →L[ℂ] Lp ℂ 2 μ)
    (hJ : ∀ u, (J u : G → ℂ) =ᵐ[μ] (u : G → ℂ))
    (τ : G →* (Lp ℂ 2 w →L[ℂ] Lp ℂ 2 w))
    (hτ : ∀ g u, (τ g u : G → ℂ) =ᵐ[μ] fun x ↦ u (g⁻¹ * x))
    (hcτ : Continuous (fun z : G × Lp ℂ 2 w ↦ τ z.1 z.2))
    (φ : G → ℂ) (hφ : Integrable φ μ) (A : Lp ℂ 2 w →L[ℂ] Lp ℂ 2 w)
    (hA : ∀ u, HasPettisIntegral (.positive μ) (fun g ↦ φ g • τ g u) (A u))
    (u : Lp ℂ 2 w) :
    ∀ᵐ ψ ∂ν, ψ ∉ tsupport (lcaFourier μ φ) →
      (lcaFourier_unitary μ ν hν).exists.choose (J (A u)) ψ = 0 := by
  let : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  let U := (lcaFourier_unitary μ ν hν).exists.choose
  let S := tsupport (lcaFourier μ φ)
  have hclosed : IsClosed {u : Lp ℂ 2 w |
      ∀ᵐ ψ ∂ν, ψ ∉ S → U (J (A u)) ψ = 0} :=
    (spectralLineIsotype_bandProjections_support_closed ν S
      (isClosed_tsupport _).measurableSet).preimage
      (U.continuous.comp (J.continuous.comp A.continuous))
  have hD := spectralLineIsotype_bandProjections_dense_integrable μ w hle
  apply hclosed.closure_subset_iff.mpr ?_ (hD u)
  intro z hz
  let f := lcaConvolution μ φ z
  have hv : (J (A z) : G → ℂ) =ᵐ[μ] f :=
    pettis_convolution_haar_L2 μ J hJ τ hτ hcτ φ hφ z (A z) (hA z)
  have hf : MemLp f 2 μ := (Lp.memLp (J (A z))).ae_eq hv
  have heq : J (A z) = hf.toLp f := Lp.ext (hv.trans hf.coeFn_toLp.symm)
  have hFourier : (U (J (A z)) : PontryaginDual G → ℂ) =ᵐ[ν] lcaFourier μ f := by
    rw [heq]
    exact (lcaFourier_unitary μ ν hν).exists.choose_spec f
      (lcaConvolution_integrable μ hφ hz).2.1 hf
  filter_upwards [hFourier] with ψ hψ
  intro hψS
  rw [hψ, show lcaFourier μ f = _ from lcaFourier_convolution μ hφ hz,
    Pi.mul_apply, image_eq_zero_of_notMem_tsupport hψS, zero_mul]

private theorem spectralLineIsotype_bandProjections_zeroLine_support
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (m : G →ₜ* ℝ≥0ˣ) (s : ℝ) (hs : 0 ≤ s)
    (ν : Measure (PontryaginDual G)) (hν : IsLCAPlancherelMeasure μ ν) :
    let W := CompactIntervalSobolev μ (fun x ↦ Real.log ((m x).val : ℝ)) 0 0 s
    let A := (existsUnique_schwartzBruhat_zeroLineAction μ m s hs).exists.choose
    let U := (lcaFourier_unitary μ ν hν).exists.choose
    ∃ J : W →L[ℂ] Lp ℂ 2 μ,
      (∀ u, (J u : G → ℂ) =ᵐ[μ] (u : G → ℂ)) ∧
      ∀ (φ : SchwartzBruhat G) (u : W), ∀ᵐ ψ ∂ν,
        ψ ∉ tsupport (lcaFourier μ φ) → U (J (A φ u)) ψ = 0 := by
  intro W A U
  let w := μ.withDensity fun x ↦ ENNReal.ofReal
    (intervalSobolevDensity 0 0 s (Real.log ((m x).val : ℝ)))
  have hle : μ ≤ w := by
    calc
      μ = μ.withDensity 1 := withDensity_one.symm
      _ ≤ _ := withDensity_mono (.of_forall fun x ↦ by
        change 1 ≤ ENNReal.ofReal (intervalSobolevDensity 0 0 s _)
        rw [ENNReal.one_le_ofReal]
        simpa [intervalSobolevDensity] using Real.one_le_rpow
          (le_add_of_nonneg_right (sq_nonneg _)) (by linarith : 0 ≤ s / 2))
  let : IsLocallyFiniteMeasure w := IsLocallyFiniteMeasure.withDensity_ofReal
    ((continuous_intervalSobolevDensity 0 0 s).comp (continuous_logModule' m))
  obtain ⟨J, hJ⟩ := exists_L2_restriction w μ hle
  refine ⟨J, hJ, ?_⟩
  intro φ u
  exact spectralLineIsotype_bandProjections_convolution_support μ ν hν w hle J hJ
    (hardySobolevTranslation μ m 0 0 s le_rfl hs)
    (hardySobolevTranslation_apply μ m 0 0 s le_rfl hs)
    (exists_hardySobolevTranslation μ m 0 0 s le_rfl hs).choose_spec.2
    (φ : G → ℂ) ((schwartzBruhat_fourier_equiv μ).choose_spec φ).1 (A φ)
    ((existsUnique_schwartzBruhat_zeroLineAction μ m s hs).exists.choose_spec φ) u

/-- Paper: Remark 10.2.1.5, p. 444. The projections on the isotypic quotient
onto the closures of the images of the Fourier bands converge strongly to
the identity. Each orthogonal projection selects a closest element of its range.
Deviation: The Fourier bands use the inverse lift for left translation. -/
theorem spectralLineIsotype_bandProjections (χ : PontryaginDual C𝔽) (a : ℝ)
    {s : ℝ} (hs : 0 ≤ s) (ν : Measure (PontryaginDual C𝔽)) (hν : IsLCAPlancherelMeasure μ𝔽 ν) :
    let hI : (0 : ℝ) ≤ 0 := le_rfl
    let ω := χ.comp restriction
    let E := Wω(hI, hs, ω)
    let N := (Θ(a, hI, hs)).comap E.subtype
    let Q := spectralSobolevIsotypeQuotient F a hI hs ω
    let U := (lcaFourier_unitary μ𝔽 ν hν).exists.choose
    let B (n : ℕ) := {q : Q | ∃ f : E,
      q = N.mkQ f ∧ ∃ u : Lp ℂ 2 μ𝔽, (u : C𝔽 → ℂ) =ᵐ[μ𝔽] (f.val : C𝔽 → ℂ) ∧
        ∀ᵐ ψ ∂ν, ψ ∉ modulatedFrequencyBand m𝔽 χ⁻¹ (-(n : ℝ)) n → U u ψ = 0}
    ∃ P : ℕ → (Q →L[ℂ] Q),
      (∀ n, range (P n) = closure (B n)) ∧
      (∀ n q y, y ∈ closure (B n) → ‖q - P n q‖ ≤ ‖q - y‖) ∧
      ∀ q, Tendsto (fun n ↦ P n q) atTop (𝓝 q) := by
  intro hI ω E N Q U B
  have hrestriction :=
    spectralLineIsotype_bandProjections_zeroLine_support (G := C𝔽) μ𝔽 m𝔽 s hs ν hν
  let J := hrestriction.choose
  have hJ := hrestriction.choose_spec.1
  have hJsupp := hrestriction.choose_spec.2
  have hconvolution := exists_spectralLineIsotypeConvolution (F := F) χ hs
  let φ := hconvolution.choose
  let R := hconvolution.choose_spec.choose
  have hband := hconvolution.choose_spec.choose_spec.2.2.1
  have hR := hconvolution.choose_spec.choose_spec.2.2.2.1
  have hlim := hconvolution.choose_spec.choose_spec.2.2.2.2
  have hsupported (n : ℕ) (f : E) :
      ∀ᵐ ψ ∂ν, ψ ∉ modulatedFrequencyBand m𝔽 χ⁻¹ (-(n : ℝ)) n →
        U (J (R n f).val) ψ = 0 := by
    have hsupp := hJsupp (φ n) f.val
    rw [hR n f]
    filter_upwards [hsupp] with ψ hψ
    intro hψband
    exact hψ (fun hψsupp ↦ hψband (hband n hψsupp))
  let hEclosed : IsClosed (E : Set W(0, 0, s)) :=
    instClosedSpectralIsotypeSec2 (F := F) hI hs ω
  let : CompleteSpace E := hEclosed.completeSpace_coe
  let hNclosed : IsClosed (N : Set E) :=
    instClosedSpectralIsotypeThetaSec2 (F := F) a hI hs ω
  let : CompleteSpace N := hNclosed.completeSpace_coe
  exact spectralLineIsotype_bandProjections_of_supported_approximants
    (X := C𝔽) (Y := PontryaginDual C𝔽) (E := E) (Q := Q)
    μ𝔽 ν (fun f : E ↦ (f.val : C𝔽 → ℂ))
    (J.toLinearMap.comp E.subtype) (fun f ↦ hJ f.val)
    N.mkQL N.mkQ_surjective U.toLinearEquiv.toLinearMap
    (fun n ↦ modulatedFrequencyBand m𝔽 χ⁻¹ (-(n : ℝ)) n)
    (fun n f ↦ R n f) hsupported hlim

end BandProjections

/-- Paper: (10.2.2.5)–(10.2.2.6), p. 446. Keep the full multiplicity in
the strip interior and apply the boundary cutoff at the two endpoints.
Deviation: Extend by zero off the strip and use the strict boundary cutoff. -/
def spectralStripMultiplicity (α s b : ℝ) (N : ℕ) : ℕ :=
  if -α < b ∧ b < α then N
  else if b = -α ∨ b = α then spectralBoundaryMultiplicity s N else 0

/-- Paper: (10.2.2.5), p. 446. At either boundary the strip multiplicity
is the truncated multiplicity. -/
theorem spectralStripMultiplicity_boundary {α b : ℝ} (_hα : 0 ≤ α)
    (_hb : b = -α ∨ b = α) (s : ℝ) (N : ℕ) :
    spectralStripMultiplicity α s b N = spectralBoundaryMultiplicity s N := by
  unfold spectralStripMultiplicity
  split_ifs with h1
  · exfalso
    rcases _hb with rfl | rfl <;> linarith [h1.1, h1.2]
  · rfl

/-- Paper: (10.2.2.6), p. 446. At an interior point every order below the
zero multiplicity is retained. -/
theorem spectralStripMultiplicity_interior {α b : ℝ} (_hb : b ∈ Ioo (-α) α) (s : ℝ) (N : ℕ) :
    spectralStripMultiplicity α s b N = N := by
  unfold spectralStripMultiplicity
  rw [mem_Ioo] at _hb
  simp [_hb]

/-- Paper: Theorem 10.2.2.1, p. 446. Index the strip jets by the norm-one
component, real offset, ordinate, and surviving derivative order. The point
of evaluation has real part a+b. -/
abbrev SpectralStripJetIndex (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (a α s : ℝ) :=
  {j : PontryaginDual C₁ × ℝ × ℝ × ℕ //
    j.2.2.2 < spectralStripMultiplicity α s j.2.1
      (multiplicity(χ j.1, shift(a + j.2.1, j.2.2.1)))}

/-- Paper: Theorem 10.2.2.1, p. 446. Every strip jet is indexed by a
point in the closed strip and that point is a zero of the completed L-function. -/
theorem SpectralStripJetIndex.mem_strip_order_pos {χ : PontryaginDual C₁ → PontryaginDual C𝔽}
    {a α s : ℝ} (_hα : 0 ≤ α) (j : SpectralStripJetIndex χ a α s) :
    j.val.2.1 ∈ Icc (-α) α ∧
      0 < vanishingOrder(χ j.val.1, shift(a + j.val.2.1, j.val.2.2.1)) := by
  have key : ∀ o : WithTop ℤ, 0 < o.untop₀.toNat → 0 < o := by
    intro o h
    cases o with
    | top => simp at h
    | coe n =>
      rw [WithTop.untop₀_coe] at h
      exact_mod_cast (by omega : 0 < n)
  have h := j.2
  unfold spectralStripMultiplicity spectralBoundaryMultiplicity at h
  split_ifs at h with h1 h2
  · exact ⟨⟨h1.1.le, h1.2.le⟩, key _ (by omega)⟩
  · refine ⟨?_, key _ (by omega)⟩
    rw [mem_Icc]
    rcases h2 with h2 | h2 <;> constructor <;> linarith
  · omega

private theorem integrable_exp_neg_abs_mul_pow {c : ℝ} (hc : 0 < c) (k : ℕ) :
    Integrable (fun x : ℝ ↦ Real.exp (-c * |x|) * x ^ (2 * k)) volume := by
  have hcont : Continuous (fun x : ℝ ↦ Real.exp (-c * |x|) * x ^ (2 * k)) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_abs)).mul (continuous_id.pow (2 * k))
  let M : ℝ := ((2 * k).factorial : ℝ) / c ^ (2 * k) +
    ((2 * k + 2).factorial : ℝ) / c ^ (2 * k + 2)
  have hdom : Integrable (fun x : ℝ ↦ M * (1 + x ^ 2)⁻¹) volume :=
    integrable_inv_one_add_sq.const_mul M
  refine hdom.mono' hcont.aestronglyMeasurable (ae_of_all _ fun x ↦ ?_)
  have hnonneg : 0 ≤ Real.exp (-c * |x|) * x ^ (2 * k) :=
    mul_nonneg (Real.exp_pos _).le (Even.pow_nonneg (even_two_mul k) x)
  rw [Real.norm_of_nonneg hnonneg]
  have hu : 0 ≤ c * |x| := mul_nonneg hc.le (abs_nonneg x)
  have h1 : (c * |x|) ^ (2 * k) / ((2 * k).factorial : ℝ) ≤ Real.exp (c * |x|) :=
    Real.pow_div_factorial_le_exp (c * |x|) hu (2 * k)
  have h2 : (c * |x|) ^ (2 * k + 2) / ((2 * k + 2).factorial : ℝ) ≤ Real.exp (c * |x|) :=
    Real.pow_div_factorial_le_exp (c * |x|) hu (2 * k + 2)
  have hfac1 : (0 : ℝ) < ((2 * k).factorial : ℝ) := by positivity
  have hfac2 : (0 : ℝ) < ((2 * k + 2).factorial : ℝ) := by positivity
  have hc1 : 0 < c ^ (2 * k) := pow_pos hc _
  have hc2 : 0 < c ^ (2 * k + 2) := pow_pos hc _
  have hpow1 : x ^ (2 * k) ≤ (((2 * k).factorial : ℝ) / c ^ (2 * k)) * Real.exp (c * |x|) := by
    have hmul : (c * |x|) ^ (2 * k) ≤ ((2 * k).factorial : ℝ) * Real.exp (c * |x|) := by
      linarith [(div_le_iff₀ hfac1).mp h1]
    have hxa : |x| ^ (2 * k) = x ^ (2 * k) := by
      rw [pow_mul, sq_abs, ← pow_mul]
    rw [mul_pow, hxa] at hmul
    rw [div_mul_eq_mul_div, le_div_iff₀ hc1]
    linarith
  have hpow2 : x ^ (2 * k) * x ^ 2 ≤
      (((2 * k + 2).factorial : ℝ) / c ^ (2 * k + 2)) * Real.exp (c * |x|) := by
    have hmul : (c * |x|) ^ (2 * k + 2) ≤ ((2 * k + 2).factorial : ℝ) * Real.exp (c * |x|) := by
      linarith [(div_le_iff₀ hfac2).mp h2]
    have hxa : |x| ^ (2 * k + 2) = x ^ (2 * k) * x ^ 2 := by
      rw [pow_add, pow_mul, sq_abs, ← pow_mul]
    rw [mul_pow, hxa] at hmul
    rw [div_mul_eq_mul_div, le_div_iff₀ hc2]
    linarith
  have hsum : x ^ (2 * k) * (1 + x ^ 2) ≤ M * Real.exp (c * |x|) := by
    have : x ^ (2 * k) * (1 + x ^ 2) = x ^ (2 * k) + x ^ (2 * k) * x ^ 2 := by ring
    rw [this]
    have : M * Real.exp (c * |x|) =
        (((2 * k).factorial : ℝ) / c ^ (2 * k)) * Real.exp (c * |x|) +
        (((2 * k + 2).factorial : ℝ) / c ^ (2 * k + 2)) * Real.exp (c * |x|) := by
      dsimp only [M]
      ring
    linarith
  have hexp_neg : Real.exp (-c * |x|) = (Real.exp (c * |x|))⁻¹ := by
    rw [neg_mul, Real.exp_neg]
  rw [hexp_neg, inv_mul_eq_div, div_le_iff₀ (Real.exp_pos _), mul_comm (M * _), ← mul_assoc]
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity : (0 : ℝ) < 1 + x ^ 2)]
  linarith

private theorem stripJet_integrand_continuous (α s b : ℝ) (k : ℕ) :
    Continuous (fun x : ℝ ↦ Real.exp (2 * b * x - 2 * α * |x|) * x ^ (2 * k) *
      ((1 + x ^ 2) ^ (s / 2))⁻¹) :=
  ((Real.continuous_exp.comp
      ((continuous_const.mul continuous_id).sub (continuous_const.mul continuous_abs))).mul
    (continuous_id.pow (2 * k))).mul
    (((continuous_const.add (continuous_id.pow 2)).rpow_const fun x ↦
        Or.inl (by change (1 : ℝ) + x ^ 2 ≠ 0; positivity)).inv₀ fun x ↦
      (Real.rpow_pos_of_pos (by change (0 : ℝ) < 1 + x ^ 2; positivity) _).ne')

private theorem stripJet_integrand_eq {α : ℝ} (hα : 0 ≤ α) (s b : ℝ) (k : ℕ) (x : ℝ) :
    Real.exp (2 * b * x) * x ^ (2 * k) * (intervalSobolevDensity (-α) α s x)⁻¹ =
      Real.exp (2 * b * x - 2 * α * |x|) * x ^ (2 * k) * ((1 + x ^ 2) ^ (s / 2))⁻¹ := by
  rw [symmIntervalSobolevDensity_eq hα, mul_inv, Real.exp_sub, div_eq_mul_inv]
  ring

private theorem spectralStripJet_integrable {α s b : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) {k : ℕ}
    (h : (-α < b ∧ b < α) ∨ ((b = -α ∨ b = α) ∧ 2 * (k : ℝ) + 1 < s)) :
    Integrable (fun x : ℝ ↦ Real.exp (2 * b * x - 2 * α * |x|) * x ^ (2 * k) *
      ((1 + x ^ 2) ^ (s / 2))⁻¹) volume := by
  rcases h with ⟨hb1, hb2⟩ | ⟨hb, hk⟩
  · have hδ : 0 < α - |b| := by
      have : |b| < α := abs_lt.mpr ⟨hb1, hb2⟩
      linarith
    refine (integrable_exp_neg_abs_mul_pow (by linarith : 0 < 2 * (α - |b|)) k).mono'
      (stripJet_integrand_continuous α s b k).aestronglyMeasurable (ae_of_all _ fun x ↦ ?_)
    have hnonneg : 0 ≤ Real.exp (2 * b * x - 2 * α * |x|) * x ^ (2 * k) *
        ((1 + x ^ 2) ^ (s / 2))⁻¹ :=
      mul_nonneg (mul_nonneg (Real.exp_pos _).le (Even.pow_nonneg (even_two_mul k) x))
        (inv_nonneg.mpr (Real.rpow_pos_of_pos (by positivity) _).le)
    rw [Real.norm_of_nonneg hnonneg]
    have hbx : b * x ≤ |b| * |x| := by
      calc
        b * x ≤ |b * x| := le_abs_self _
        _ = |b| * |x| := abs_mul b x
    have hexp : Real.exp (2 * b * x - 2 * α * |x|) ≤ Real.exp (-(2 * (α - |b|)) * |x|) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hinv_le : ((1 + x ^ 2) ^ (s / 2))⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (Real.one_le_rpow (by nlinarith [sq_nonneg x]) (by linarith))
    calc
      Real.exp (2 * b * x - 2 * α * |x|) * x ^ (2 * k) * ((1 + x ^ 2) ^ (s / 2))⁻¹
        ≤ Real.exp (2 * b * x - 2 * α * |x|) * x ^ (2 * k) * 1 :=
          mul_le_mul_of_nonneg_left hinv_le
            (mul_nonneg (Real.exp_pos _).le (Even.pow_nonneg (even_two_mul k) x))
      _ = Real.exp (2 * b * x - 2 * α * |x|) * x ^ (2 * k) := mul_one _
      _ ≤ Real.exp (-(2 * (α - |b|)) * |x|) * x ^ (2 * k) :=
          mul_le_mul_of_nonneg_right hexp (Even.pow_nonneg (even_two_mul k) x)
  · refine (integrable_pow_mul_rpow_inv hk).mono'
      (stripJet_integrand_continuous α s b k).aestronglyMeasurable (ae_of_all _ fun x ↦ ?_)
    have hnonneg : 0 ≤ Real.exp (2 * b * x - 2 * α * |x|) * x ^ (2 * k) *
        ((1 + x ^ 2) ^ (s / 2))⁻¹ :=
      mul_nonneg (mul_nonneg (Real.exp_pos _).le (Even.pow_nonneg (even_two_mul k) x))
        (inv_nonneg.mpr (Real.rpow_pos_of_pos (by positivity) _).le)
    rw [Real.norm_of_nonneg hnonneg, mul_assoc]
    have hba : |b| = α := by
      rcases hb with rfl | rfl
      · rw [abs_neg, abs_of_nonneg hα]
      · exact abs_of_nonneg hα
    have hbx : b * x ≤ α * |x| := by
      calc
        b * x ≤ |b * x| := le_abs_self _
        _ = |b| * |x| := abs_mul b x
        _ = α * |x| := by rw [hba]
    have hexp : Real.exp (2 * b * x - 2 * α * |x|) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith)
    calc
      Real.exp (2 * b * x - 2 * α * |x|) * (x ^ (2 * k) * ((1 + x ^ 2) ^ (s / 2))⁻¹)
        ≤ 1 * (x ^ (2 * k) * ((1 + x ^ 2) ^ (s / 2))⁻¹) :=
          mul_le_mul_of_nonneg_right hexp
            (mul_nonneg (Even.pow_nonneg (even_two_mul k) x)
              (inv_nonneg.mpr (Real.rpow_pos_of_pos (by positivity) _).le))
      _ = x ^ (2 * k) * ((1 + x ^ 2) ^ (s / 2))⁻¹ := one_mul _

/-- Paper: Theorem 10.2.2.1, p. 446. The admitted strip jets are
square-integrable for the reciprocal strip weight.
Deviation: Exclude the divergent boundary endpoint of (10.2.2.5). -/
theorem spectralStripJet_memLp (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    {a α s : ℝ} (_hα : 0 ≤ α) (_hs : 0 ≤ s) (j : SpectralStripJetIndex χ a α s) :
    MemLp (stripJet(χ, j)) 2 (L2μ'(-α, α, s)) := by
  have hcond : (-α < j.val.2.1 ∧ j.val.2.1 < α) ∨
      ((j.val.2.1 = -α ∨ j.val.2.1 = α) ∧ 2 * (j.val.2.2.2 : ℝ) + 1 < s) := by
    have hj := j.property
    unfold spectralStripMultiplicity at hj
    split_ifs at hj with h1 h2
    · exact Or.inl h1
    · refine Or.inr ⟨h2, ?_⟩
      have horder : (j.val.2.2.2 : ℝ) < (s - 1) / 2 :=
        ((lt_spectralBoundaryMultiplicity s _ _).mp hj).2
      linarith
    · omega
  let ν : Measure C𝔽 := canonicalModulatedHaar m𝔽 hm𝔽
  let : ν.IsHaarMeasure := (existsUnique_canonicalModulatedHaar m𝔽 hm𝔽).exists.choose_spec.1
  have hν : Integrable (fun g : C𝔽 ↦
      Real.exp (2 * j.val.2.1 * logNorm g - 2 * α * |logNorm g|) *
        (logNorm g) ^ (2 * j.val.2.2.2) * ((1 + (logNorm g) ^ 2) ^ (s / 2))⁻¹) ν :=
    (sobolev_log_preserving m𝔽 hm𝔽 hms𝔽).integrable_comp_of_integrable
      (spectralStripJet_integrable _hα _hs hcond)
  have hμ : Integrable (fun g : C𝔽 ↦
      Real.exp (2 * j.val.2.1 * logNorm g - 2 * α * |logNorm g|) *
        (logNorm g) ^ (2 * j.val.2.2.2) * ((1 + (logNorm g) ^ 2) ^ (s / 2))⁻¹) μ𝔽 := by
    rw [Measure.isMulLeftInvariant_eq_smul μ𝔽 ν]
    exact hν.smul_measure_nnreal
  apply (memLp_two_iff_integrable_sq_norm
    (spectralZeroJet_continuous (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2).aestronglyMeasurable).2
  apply (integrable_withDensity_iff
    ((symmIntervalSobolevDensity_inv_continuous _hα s).measurable.ennreal_ofReal)
    (ae_of_all μ𝔽 fun _ ↦ ENNReal.ofReal_lt_top)).2
  refine hμ.congr (ae_of_all μ𝔽 fun g ↦ ?_)
  dsimp only
  rw [spectralZeroJet_norm_sq,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (symmIntervalSobolevDensity_pos _hα s (logNorm g)).le),
    stripJet_integrand_eq _hα]

local notation "stripI(" hα ")" => (neg_nonpos.mpr hα |>.trans hα)
local notation "stripU(" χ ", " hα ", " hs ")" =>
  (fun j ↦ (spectralStripJet_memLp χ hα hs j).toLp (stripJet(χ, j)))

section StripThetaAnnihilation

local notation "ℬ" => SchwartzBruhat (Multiplicative (AdeleRing (𝓞 F) F))

/-- Factorization on a right half-plane determines the equality of meromorphic
orders everywhere. -/
private theorem stripTheta_order_of_factor {Z L A : ℂ → ℂ} (hZ : Differentiable ℂ Z)
    (hL : MeromorphicOn L univ) (hA : AnalyticOnNhd ℂ A univ)
    (heq : ∀ z : ℂ, 1 < z.re → Z z = L z * A z) (w : ℂ) :
    meromorphicOrderAt Z w = meromorphicOrderAt L w + meromorphicOrderAt A w := by
  have hLA : MeromorphicOn (L * A) univ := hL.mul (fun z hz ↦ (hA z hz).meromorphicAt)
  have hzM : MeromorphicOn Z univ := fun z _ ↦ (hZ.analyticAt z).meromorphicAt
  have hd : MeromorphicOn (Z - L * A) univ := hzM.sub hLA
  have ho : meromorphicOrderAt (Z - L * A) 2 = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    have hnear : ∀ᶠ z in 𝓝 (2 : ℂ), 1 < z.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds] with z hz using sub_eq_zero.mpr (heq z hz)
  have hw := hd.meromorphicOrderAt_eq_top_of_isPreconnected isPreconnected_univ
    (mem_univ (2 : ℂ)) (mem_univ w) ho
  have he : Z =ᶠ[𝓝[≠] w] L * A :=
    (meromorphicOrderAt_eq_top_iff.mp hw).mono fun z hz ↦ sub_eq_zero.mp hz
  rw [meromorphicOrderAt_congr he, meromorphicOrderAt_mul (hL w (mem_univ w)) (hA w (mem_univ w)).meromorphicAt]

private theorem stripTheta_deriv_of_order {Z L : ℂ → ℂ} {w : ℂ} (hZ : AnalyticAt ℂ Z w)
    (ho : meromorphicOrderAt L w ≤ meromorphicOrderAt Z w) {k : ℕ}
    (hk : k < (meromorphicOrderAt L w).untop₀.toNat) : iteratedDeriv k Z w = 0 := by
  have hlt : (k : WithTop ℤ) < meromorphicOrderAt L w := by
    cases h : meromorphicOrderAt L w with
    | top => simp
    | coe n =>
      rw [h, WithTop.untop₀_coe] at hk
      exact WithTop.coe_lt_coe.mpr (by omega)
  have hl := hlt.trans_le ho
  rw [hZ.meromorphicOrderAt_eq] at hl
  apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (n := k+1) hZ).mp _ k (Nat.lt_succ_self k)
  cases h : analyticOrderAt Z w with
  | top => simp
  | coe n =>
    rw [h, ENat.map_natCast] at hl
    exact WithTop.coe_le_coe.mpr (by exact_mod_cast (show (k : ℤ) < n from WithTop.coe_lt_coe.mp hl))

/-- The normalized eigendistribution is the entire test factor and the two
orders add at every point. -/
private theorem stripTheta_mellin_factor_order (χ : PontryaginDual C𝔽) (f : adelePolarSubspace F) (w : ℂ) :
    let Z := fun z ↦ globalThetaMellinIntegral f.val (ideleClassNormTwist χ z)
    let L := continuedCompletedHeckeL χ
    let Φ := fun z ↦ (adelicEigendistribution_normalized χ).choose z f.val
    AnalyticAt ℂ Φ w ∧ meromorphicOrderAt Z w = meromorphicOrderAt L w + meromorphicOrderAt Φ w := by
  let Z (z : ℂ) := globalThetaMellinIntegral f.val (ideleClassNormTwist χ z)
  let L := continuedCompletedHeckeL χ
  obtain ⟨hf, hf'⟩ := (mem_adelePolarSubspace f.val).mp f.property
  have hZ : Differentiable ℂ Z := globalThetaMellinIntegral_entire_of_vanishing f.val hf hf' χ
  let D := (adelicEigendistribution_normalized χ).choose
  have hD := (adelicEigendistribution_normalized χ).choose_spec
  let d : ℂ := ((Real.sqrt |(NumberField.discr F : ℝ)|)⁻¹ : ℝ)
  let A (z : ℂ) := d * D z f.val
  have hE : AnalyticOnNhd ℂ (fun z ↦ D z f.val) univ := by
    let e : StrongDual ℂ ℬ →L[ℂ] ℂ := ContinuousLinearMap.applyₗ ℂ (RingHom.id ℂ) f.val
    have hE : Differentiable ℂ (e ∘ D) := by
      intro z
      have hd := hD.1.hasFDerivAt (isOpen_univ.mem_nhds (mem_univ z))
      have he : HasFDerivAt (e ∘ D) (e.comp (fderiv ℂ D z)) z := by
        apply HasFDerivAt.of_isLittleOTVS
        simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, map_sub]
          using e.isBigOTVS_comp.trans_isLittleOTVS hd.isLittleOTVS
      exact he.differentiableAt
    exact fun z _ ↦ hE.analyticAt z
  have hA : AnalyticOnNhd ℂ A univ := analyticOnNhd_const.mul hE
  have hσ (ψ : PontryaginDual C𝔽) (z : ℂ) := quasiCharacterAbscissa_of_unitary_twist
    (ideleClassNorm F) (isProperMap_ideleClassNorm F) (ideleClassNorm_ne_one (F := F))
    (ideleClassNormTwist ψ z) ψ z (fun _ ↦ rfl)
  have hfact (z : ℂ) (hz : 1 < z.re) : Z z = L z * A z := by
    let σ := quasiCharacterAbscissa (ideleClassNorm F) (isProperMap_ideleClassNorm F) (ideleClassNorm_ne_one (F := F))
    have h0 : σ 1 = 0 := by
      change Real.log ‖(1 : ℂ)‖ / _ = 0
      rw [norm_one, Real.log_one, zero_div]
    have hn : ideleClassNormTwist χ z ≠ 1 := fun h ↦ (zero_lt_one.trans hz).ne'
      ((hσ χ z).symm.trans ((congrArg σ h).trans h0))
    have hn' : ideleClassNormTwist χ z ≠ ideleClassNormTwist (1 : PontryaginDual C𝔽) 1 :=
      fun h ↦ hz.ne' ((hσ χ z).symm.trans ((congrArg σ h).trans (hσ _ 1)))
    have hzeta := congrFun (globalThetaMellinIntegral_eq_continuation_of_vanishing f.val hf hf')
      (ideleClassNormTwist χ z)
    refine hzeta.trans ((hD.2.2 z hn hn' f.val).trans ?_)
    rw [gaussianCompletedHeckeL_eq_completedHeckeL χ z hz]
    have h := (continuedCompletedHeckeL_spec χ).2 ⟨z,hz⟩
    change d * completedHeckeL χ ⟨z,hz⟩ * D z f.val = L z * (d * D z f.val)
    rw [← h]
    ring
  have he := stripTheta_order_of_factor hZ (continuedCompletedHeckeL_spec χ).1.meromorphicOn hA hfact w
  have hd : d ≠ 0 := Complex.ofReal_ne_zero.mpr (inv_ne_zero (Real.sqrt_pos.mpr
    (abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero F))).ne')
  have ha : meromorphicOrderAt A w = meromorphicOrderAt (fun z ↦ D z f.val) w :=
    meromorphicOrderAt_mul_of_ne_zero (g := fun _ ↦ d) analyticAt_const hd
  exact ⟨hE w (mem_univ w), he.trans (congrArg (meromorphicOrderAt L w + ·) ha)⟩

/-- The completed L-function divides each polar-free theta Mellin transform as
a germ; equality of orders holds wherever the normalized eigendistribution is nonzero. -/
private theorem stripTheta_mellin_order (χ : PontryaginDual C𝔽) (f : adelePolarSubspace F) (w : ℂ) :
    let Z := fun z ↦ globalThetaMellinIntegral f.val (ideleClassNormTwist χ z)
    let L := continuedCompletedHeckeL χ
    meromorphicOrderAt L w ≤ meromorphicOrderAt Z w ∧
      ((adelicEigendistribution_normalized χ).choose w f.val ≠ 0 →
        meromorphicOrderAt Z w = meromorphicOrderAt L w) := by
  obtain ⟨hA, he⟩ := stripTheta_mellin_factor_order χ f w
  refine ⟨(le_add_of_nonneg_right hA.meromorphicOrderAt_nonneg).trans he.symm.le, fun hu ↦ ?_⟩
  exact he.trans (by rw [hA.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hu, add_zero])

/-- The Mellin derivatives below the completed L-function’s order vanish. -/
private theorem stripTheta_mellin_zero (χ : PontryaginDual C𝔽) (f : adelePolarSubspace F)
    (w : ℂ) (k : ℕ) (hk : k < (meromorphicOrderAt (continuedCompletedHeckeL χ) w).untop₀.toNat) :
    iteratedDeriv k (fun z ↦ globalThetaMellinIntegral f.val (ideleClassNormTwist χ z)) w = 0 := by
  obtain ⟨hf, hf'⟩ := (mem_adelePolarSubspace f.val).mp f.property
  exact stripTheta_deriv_of_order (globalThetaMellinIntegral_entire_of_vanishing f.val hf hf' χ |>.analyticAt w)
    (stripTheta_mellin_order χ f w).1 hk

/-- Two translation differences kill the polar coordinates while preserving a
nonzero eigenfunctional of any distinct weight. -/
private theorem polarShift_preserve {E G : Type*} [AddCommGroup E] [Module ℂ E]
    (P : E →ₗ[ℂ] ℂ × ℂ) (D : E →ₗ[ℂ] ℂ) (τ : G → E → E) (c₀ c₁ c : G → ℂ)
    (hp₀ : ∀ g f, (P (τ g f)).1 = c₀ g * (P f).1)
    (hp₁ : ∀ g f, (P (τ g f)).2 = c₁ g * (P f).2)
    (hd : ∀ g f, D (τ g f) = c g * D f) (f : E) (hf : D f ≠ 0)
    {g h : G} (hg : c g ≠ c₀ g) (hh : c h ≠ c₁ h) : ∃ f' : P.ker, D f'.val ≠ 0 := by
  let x := τ g f - c₀ g • f
  let y := τ h x - c₁ h • x
  have h₀ : (P x).1 = 0 := by simp [x, hp₀]
  have hP : P y = 0 := by
    ext <;> simp [y, hp₀, hp₁, h₀]
  refine ⟨⟨y, hP⟩, ?_⟩
  have hval : D y = (c h - c₁ h) * (c g - c₀ g) * D f := by
    simp [y, x, hd]
    ring
  exact hval ▸ mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hh) (sub_ne_zero.mpr hg)) hf

private theorem stripTheta_normalized_nonzero_on_polar (χ : PontryaginDual C𝔽) (w : ℂ)
    (h₀ : ideleClassNormTwist χ w ≠ 1)
    (h₁ : ideleClassNormTwist χ w ≠ ideleClassNormTwist (1 : PontryaginDual C𝔽) 1) :
    ∃ f : adelePolarSubspace F, (adelicEigendistribution_normalized χ).choose w f.val ≠ 0 := by
  classical
  let c := ideleClassNormTwist χ w
  let n := ideleClassNormTwist (1 : PontryaginDual C𝔽) 1
  let D := (adelicEigendistribution_normalized χ).choose w
  have hD := ((adelicEigendistribution_normalized χ).choose_spec.2.1 w D).mp rfl
  let π : IdeleGroup (𝓞 F) F → C𝔽 := QuotientGroup.mk
  have hsep (d : QuasiCharacter C𝔽) (hne : c ≠ d) : ∃ g, c (π g) ≠ d (π g) := by
    by_contra! hall
    apply hne
    ext x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    exact hall g
  obtain ⟨g,hg⟩ := hsep 1 h₀
  obtain ⟨h,hh⟩ := hsep n h₁
  let P := adelePolarValues (F := F)
  let τ := schwartzBruhatUnitTranslate (R := AdeleRing (𝓞 F) F)
  let K := (adelicThetaLinearMap F).ker
  have hact := (existsUnique_globalThetaAction (F := F)).exists.choose_spec.2
  have hp₀ (g : IdeleGroup (𝓞 F) F) (f : ℬ) : (P (τ g f)).1 = (1 : QuasiCharacter C𝔽) (π g) * (P f).1 := by
    change (τ g f) (Multiplicative.ofAdd 0) = 1 * f (Multiplicative.ofAdd 0)
    rw [schwartzBruhatUnitTranslate_apply, mul_zero, one_mul]
  have hp₁ (g : IdeleGroup (𝓞 F) F) (f : ℬ) : (P (τ g f)).2 = n (π g) * (P f).2 := by
    have hh := globalThetaPolarValues_snd_translate (π g) (K.mkQL f)
    have hraw : (P (τ g f)).2 = ((ideleClassNorm F (π g)).val : ℝ) * (P f).2 :=
      (congrArg (fun x ↦ (globalThetaPolarValues (F := F) x).2) (hact g f).symm).trans hh
    change _ = ((1 : ℂ) * ((((ideleClassNorm F (π g)).val : ℝ) : ℂ) ^ (1 : ℂ))) * _
    simpa only [Complex.cpow_one, one_mul] using hraw
  exact polarShift_preserve P D.toLinearMap τ _ _ _ hp₀ hp₁ hD.1 (adelicStandardGaussian χ)
    (hD.2.trans_ne one_ne_zero) hg hh

/-- Paper: Theorem 3.4.3.3(2), p. 153, and Theorem 10.2.1.1, pp. 441–442.
At each twist away from the trivial character and the idelic norm, one polar-free
test attains the order of the completed Hecke L-function in its Mellin transform. -/
private theorem exists_globalThetaMellinIntegral_order_eq_of_regular (χ : PontryaginDual C𝔽) (w : ℂ)
    (h₀ : ideleClassNormTwist χ w ≠ 1)
    (h₁ : ideleClassNormTwist χ w ≠ ideleClassNormTwist (1 : PontryaginDual C𝔽) 1) :
    ∃ f : adelePolarSubspace F,
      meromorphicOrderAt (fun z ↦ globalThetaMellinIntegral f.val (ideleClassNormTwist χ z)) w =
        meromorphicOrderAt (continuedCompletedHeckeL χ) w := by
  obtain ⟨f, hf⟩ := stripTheta_normalized_nonzero_on_polar χ w h₀ h₁
  exact ⟨f, (stripTheta_mellin_order χ f w).2 hf⟩

/-- Paper: Proposition 3.2.1.3(2), p. 123. In a unitary chart the trivial
quasi-character and the idelic norm correspond to simple poles of the completed L-function. -/
private theorem continuedCompletedHeckeL_order_of_exceptional (χ : PontryaginDual C𝔽) (w : ℂ)
    (he : ideleClassNormTwist χ w = 1 ∨
      ideleClassNormTwist χ w = ideleClassNormTwist (1 : PontryaginDual C𝔽) 1) :
    meromorphicOrderAt (continuedCompletedHeckeL χ) w = -1 := by
  have h0 : ideleClassNormTwist (1 : PontryaginDual C𝔽) 0 = 1 := by
    ext1 g
    change 1 * ((((ideleClassNorm F g).val : ℝ) : ℂ) ^ (0 : ℂ)) = 1
    simp
  obtain ⟨z, hz, hc⟩ : ∃ z : ℂ, (z = 0 ∨ z = 1) ∧ ideleClassNormTwist χ w = ideleClassNormTwist (1 : PontryaginDual C𝔽) z := by
    rcases he with he | he
    · exact ⟨0, Or.inl rfl, he.trans h0.symm⟩
    · exact ⟨1, Or.inr rfl, he⟩
  have hres : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1 := by
    ext g : 1
    apply Subtype.ext
    have hu := DFunLike.congr_fun hc g.val
    change (χ g.val : ℂ) * ((((ideleClassNorm F g.val).val : ℝ) : ℂ) ^ w) =
      1 * ((((ideleClassNorm F g.val).val : ℝ) : ℂ) ^ z) at hu
    rw [g.property] at hu
    change (χ g.val : ℂ) = 1
    simpa only [Units.val_one, NNReal.coe_one, Complex.ofReal_one, Complex.one_cpow, mul_one] using hu
  obtain ⟨t, ⟨ht, hp₀, hp₁, _⟩, _⟩ := completedHeckeL_continuation_simplePoles χ _
    (continuedCompletedHeckeL_spec χ).1 (continuedCompletedHeckeL_spec χ).2 hres
  have heq : ideleClassNormTwist (1 : PontryaginDual C𝔽) (-Complex.I * (t : ℂ) + w) =
      ideleClassNormTwist (1 : PontryaginDual C𝔽) z := by
    simpa only [zero_add] using (ideleClassNormTwist_add_of_eq ht w).symm.trans (by simpa only [zero_add] using hc)
  let γ := quasiCharacterNormTwist (MonoidHom.id ℝ≥0ˣ) continuous_id 1 z
  have hγ (u : ℝ≥0ˣ) : γ u = ((u.val : ℝ) : ℂ) ^ z := one_mul _
  have hc' : z = -Complex.I * (t : ℂ) + w := by
    apply (existsUnique_complexPower γ).unique hγ
    intro u
    let g : C𝔽 := QuotientGroup.mk (canonicalIdeleNormSection F u)
    have hg : ideleClassNorm F g = u := canonicalIdeleNormSection_rightInverse F u
    have hu := DFunLike.congr_fun heq g
    change 1 * ((((ideleClassNorm F g).val : ℝ) : ℂ) ^ (-Complex.I * (t : ℂ) + w)) = 1 * ((((ideleClassNorm F g).val : ℝ) : ℂ) ^ z) at hu
    rw [hg, one_mul, one_mul] at hu
    exact (hγ u).trans hu.symm
  rcases hz with rfl | rfl
  · exact (congrArg (meromorphicOrderAt (continuedCompletedHeckeL χ)) (by linear_combination -hc' : w = Complex.I * t)).trans hp₀
  · exact (congrArg (meromorphicOrderAt (continuedCompletedHeckeL χ)) (by linear_combination -hc' : w = 1 + Complex.I * t)).trans hp₁

/-- Paper: Theorem 10.2.1.1, pp. 441–442, and Theorem 10.2.2.1, p. 446.
At every zero of the completed Hecke L-function, some polar-free theta test has
a Mellin transform with exactly its multiplicity. -/
private theorem exists_globalThetaMellinIntegral_order_eq_of_zero (χ : PontryaginDual C𝔽) (w : ℂ)
    (hw : 0 < meromorphicOrderAt (continuedCompletedHeckeL χ) w) :
    ∃ f : adelePolarSubspace F,
      meromorphicOrderAt (fun z ↦ globalThetaMellinIntegral f.val (ideleClassNormTwist χ z)) w =
        meromorphicOrderAt (continuedCompletedHeckeL χ) w := by
  have hn : ¬ (ideleClassNormTwist χ w = 1 ∨
      ideleClassNormTwist χ w = ideleClassNormTwist (1 : PontryaginDual C𝔽) 1) := by
    intro h
    rw [continuedCompletedHeckeL_order_of_exceptional χ w h] at hw
    exact (by decide : ¬ (0 : WithTop ℤ) < -1) hw
  exact exists_globalThetaMellinIntegral_order_eq_of_regular χ w (not_or.mp hn).1 (not_or.mp hn).2

/-- Paper: Theorem 10.2.2.1, p. 446, and (3.4.3.15), p. 153. On a polar-free test
the first nonvanishing Mellin derivative can attain the full Hecke multiplicity at
each admitted strip jet.
Deviation: This statement concerns derivatives of the test function's Mellin transform.
Only orders below the strict cutoff give continuous Sobolev moments at the boundary. -/
theorem SpectralStripJetIndex.exists_thetaMellin_first_nonvanishing
    {χ : PontryaginDual C₁ → PontryaginDual C𝔽} {a α s : ℝ} (j : SpectralStripJetIndex χ a α s) :
    let w := shift(a + j.val.2.1, j.val.2.2.1)
    let n := (meromorphicOrderAt (continuedCompletedHeckeL (χ j.val.1)) w).untop₀.toNat
    ∃ f : adelePolarSubspace F,
      let Z := fun u ↦ globalThetaMellinIntegral f.val (ideleClassNormTwist (χ j.val.1) u)
      (∀ k < n, iteratedDeriv k Z w = 0) ∧ iteratedDeriv n Z w ≠ 0 := by
  intro w n
  let L := continuedCompletedHeckeL (χ j.val.1)
  have hn : 0 < n := by
    have h : j.val.2.2.2 < spectralStripMultiplicity α s j.val.2.1 n := j.property
    unfold spectralStripMultiplicity spectralBoundaryMultiplicity at h
    split_ifs at h <;> omega
  have hn' : 0 < meromorphicOrderAt L w ∧ meromorphicOrderAt L w = (n : WithTop ℤ) := by
    change 0 < (meromorphicOrderAt L w).untop₀.toNat at hn
    change 0 < meromorphicOrderAt L w ∧ meromorphicOrderAt L w = ((meromorphicOrderAt L w).untop₀.toNat : WithTop ℤ)
    cases h : meromorphicOrderAt L w with
    | top => simp [h] at hn
    | coe z =>
      rw [h, WithTop.untop₀_coe] at hn
      rw [WithTop.untop₀_coe]
      exact ⟨WithTop.coe_lt_coe.mpr (by omega), WithTop.coe_eq_coe.mpr (by omega)⟩
  obtain ⟨f, hf⟩ := exists_globalThetaMellinIntegral_order_eq_of_zero (χ j.val.1) w hn'.1
  let Z := fun u ↦ globalThetaMellinIntegral f.val (ideleClassNormTwist (χ j.val.1) u)
  obtain ⟨hf₀,hf₁⟩ := (mem_adelePolarSubspace f.val).mp f.property
  have hZ : AnalyticAt ℂ Z w := (globalThetaMellinIntegral_entire_of_vanishing f.val hf₀ hf₁ (χ j.val.1)).analyticAt w
  have hz : meromorphicOrderAt Z w = (n : WithTop ℤ) := hf.trans hn'.2
  rw [hZ.meromorphicOrderAt_eq] at hz
  refine ⟨f, (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hZ).mp ?_⟩
  cases h : analyticOrderAt Z w with
  | top => simp [h] at hz
  | coe r =>
    rw [h, ENat.map_natCast] at hz
    congr 1
    exact_mod_cast (WithTop.coe_eq_coe.mp hz)

/-- A character with nonzero logarithmic derivative crosses each polar weight simply. -/
private theorem stripTheta_polarFactor_order {B : ℂ → ℂ} {w d : ℂ} (hB : AnalyticAt ℂ B w)
    (hD : HasDerivAt B d w) (hd : d ≠ 0) (hw : B w = 1 ∨ B w = 2) :
    meromorphicOrderAt (fun z ↦ (B z - 2) * (B z - 1)) w = 1 := by
  let A := fun z ↦ (B z - 2) * (B z - 1)
  have ha : AnalyticAt ℂ A w := (hB.sub analyticAt_const).mul (hB.sub analyticAt_const)
  have hv : A w = 0 := by rcases hw with h | h <;> simp [A, h]
  have hda : HasDerivAt A (d * (B w - 1) + (B w - 2) * d) w :=
    (hD.sub_const _).mul (hD.sub_const _)
  have hn : deriv A w ≠ 0 := by
    rw [hda.deriv]
    rcases hw with h | h <;> norm_num [h, hd]
  have ho : analyticOrderAt A w = 1 := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero (n := 1) ha).mpr
    ⟨fun k hk ↦ by simpa [Nat.lt_one_iff.mp hk] using hv, by simpa using hn⟩
  change meromorphicOrderAt A w = 1
  rw [ha.meromorphicOrderAt_eq, ho]
  rfl

/-- A double difference of the standard Gaussian removes both polar values. At
either exceptional weight its normalized Mellin factor has a simple zero. -/
private theorem stripTheta_exists_normalized_order_one (χ : PontryaginDual C𝔽) (w : ℂ)
    (he : ideleClassNormTwist χ w = 1 ∨ ideleClassNormTwist χ w = ideleClassNormTwist (1 : PontryaginDual C𝔽) 1) :
    ∃ f : adelePolarSubspace F,
      meromorphicOrderAt (fun z ↦ (adelicEigendistribution_normalized χ).choose z f.val) w = 1 := by
  let r : ℝ≥0ˣ := Units.mk0 2 (by norm_num)
  let g := canonicalIdeleNormSection F r
  let y : C𝔽 := QuotientGroup.mk g
  have hy : ideleClassNorm F y = r := canonicalIdeleNormSection_rightInverse F r
  let τ := schwartzBruhatUnitTranslate (R := AdeleRing (𝓞 F) F) g
  let G := adelicStandardGaussian χ
  let x := τ G - G
  let f := τ x - (2 : ℂ) • x
  let P := adelePolarValues (F := F)
  have h₀ (v : ℬ) : (P (τ v)).1 = (P v).1 := by
    change schwartzBruhatUnitTranslate g v (Multiplicative.ofAdd 0) = v (Multiplicative.ofAdd 0)
    rw [schwartzBruhatUnitTranslate_apply, mul_zero]
  have h₁ (v : ℬ) : (P (τ v)).2 = 2 * (P v).2 := by
    let K := (adelicThetaLinearMap F).ker
    have hact := (existsUnique_globalThetaAction (F := F)).exists.choose_spec.2 g v
    have hn := globalThetaPolarValues_snd_translate y (K.mkQL v)
    have hu : (P (τ v)).2 = ((ideleClassNorm F y).val : ℝ) * (P v).2 :=
      (congrArg (fun u ↦ (globalThetaPolarValues (F := F) u).2) hact.symm).trans hn
    rw [hy] at hu
    exact hu
  have hsub : f ∈ adelePolarSubspace F := by
    change P f = 0
    have hsa : (P x).1 = 0 := by simp [x, h₀]
    ext <;> simp [f, h₀, h₁, hsa]
  refine ⟨⟨f,hsub⟩, ?_⟩
  let D := (adelicEigendistribution_normalized χ).choose
  let B := fun z ↦ ideleClassNormTwist χ z y
  have hval : (fun z ↦ D z f) = fun z ↦ (B z - 2) * (B z - 1) := by
    funext z
    have hN := ((adelicEigendistribution_normalized χ).choose_spec.2.1 z (D z)).mp rfl
    have hD (v : ℬ) : D z (τ v) = B z * D z v := hN.1 g v
    have hG : D z G = 1 := hN.2
    simp [f, x, hD, hG]
    ring
  change meromorphicOrderAt (fun z ↦ D z f) w = 1
  rw [hval]
  have hB : B = fun z ↦ (χ y : ℂ) * Complex.exp (((Real.log 2 : ℝ) : ℂ) * z) := by
    funext z
    change (χ y : ℂ) * ((((ideleClassNorm F y).val : ℝ) : ℂ) ^ z) = _
    rw [hy]
    change (χ y : ℂ) * ((2 : ℂ) ^ z) = _
    rw [Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0)]
    congr 3
    norm_cast
  have hd : HasDerivAt B ((χ y : ℂ) * (Complex.exp (((Real.log 2 : ℝ) : ℂ) * w) * (Real.log 2 : ℝ))) w := by
    rw [hB]
    exact (((hasDerivAt_id w).const_mul _).cexp.const_mul _).congr_deriv (by simp)
  apply stripTheta_polarFactor_order (B := B) (by rw [hB]; fun_prop) hd
  · exact mul_ne_zero (Circle.coe_ne_zero _) (mul_ne_zero (Complex.exp_ne_zero _) (Complex.ofReal_ne_zero.mpr (Real.log_pos (by norm_num)).ne'))
  · rcases he with he | he
    · exact Or.inl (DFunLike.congr_fun he y)
    · refine Or.inr ((DFunLike.congr_fun he y).trans ?_)
      change 1 * ((((ideleClassNorm F y).val : ℝ) : ℂ) ^ (1 : ℂ)) = 2
      rw [hy, Complex.cpow_one, one_mul]
      rfl

/-- Paper: Theorems 3.4.3.3(2), p. 153, and 10.2.2.1, p. 446. At each fixed
point, the minimum vanishing order over all entire polar-free theta Mellin
transforms is the positive part of the completed Hecke divisor there.
Deviation: This pointwise consequence uses the Gaussian-normalized factorization
with its nonzero Tamagawa scalar. It includes both simple poles after cancellation. -/
theorem isLeast_globalThetaMellinIntegral_orders (χ : PontryaginDual C𝔽) (w : ℂ) :
    IsLeast (Set.range fun f : adelePolarSubspace F ↦
      meromorphicOrderAt (fun z ↦ globalThetaMellinIntegral f.val (ideleClassNormTwist χ z)) w)
      (max 0 (meromorphicOrderAt (continuedCompletedHeckeL χ) w)) := by
  let Z (f : adelePolarSubspace F) (z : ℂ) := globalThetaMellinIntegral f.val (ideleClassNormTwist χ z)
  let L := continuedCompletedHeckeL χ
  have hZ (f : adelePolarSubspace F) : 0 ≤ meromorphicOrderAt (Z f) w := by
    obtain ⟨hf, hf'⟩ := (mem_adelePolarSubspace f.val).mp f.property
    exact (globalThetaMellinIntegral_entire_of_vanishing f.val hf hf' χ |>.analyticAt w).meromorphicOrderAt_nonneg
  refine ⟨?_, ?_⟩
  · by_cases he : ideleClassNormTwist χ w = 1 ∨
        ideleClassNormTwist χ w = ideleClassNormTwist (1 : PontryaginDual C𝔽) 1
    · obtain ⟨f, hf⟩ := stripTheta_exists_normalized_order_one χ w he
      have hp : meromorphicOrderAt L w = -1 := continuedCompletedHeckeL_order_of_exceptional χ w he
      have h := (stripTheta_mellin_factor_order χ f w).2
      refine ⟨f, ?_⟩
      change meromorphicOrderAt (Z f) w = max 0 (meromorphicOrderAt L w)
      exact h.trans (by rw [hf, hp]; decide)
    · obtain ⟨f,hf⟩ := exists_globalThetaMellinIntegral_order_eq_of_regular χ w (not_or.mp he).1 (not_or.mp he).2
      exact ⟨f, hf.trans (max_eq_right (hf ▸ hZ f)).symm⟩
  · rintro _ ⟨f,rfl⟩
    exact max_le (hZ f) (stripTheta_mellin_order χ f w).1

/-- The unweighted Haar integral of a weighted polar-free theta function against an
admitted zero jet vanishes, including the center shift in its multiplicity. -/
private theorem stripTheta_weighted_moment_zero (χ : PontryaginDual C𝔽)
    (f : adelePolarSubspace F) (a b t : ℝ) (k : ℕ)
    (hk : k < (meromorphicOrderAt (continuedCompletedHeckeL χ) (shift(a + b, t))).untop₀.toNat) :
    ∫ g, modulationWeight m𝔽 a (adelicTheta f.val) g * spectralZeroJet χ b t k g ∂μ𝔽 = 0 := by
  let χq : QuasiCharacter C𝔽 :=
    (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ
  obtain ⟨hf, hf'⟩ := (mem_adelePolarSubspace f.val).mp f.property
  have hi := globalThetaMellinIntegral_integrable_of_vanishing f.val hf hf'
  have hz : (shift(a + b, t)).re ∈ Ioo (a+b-1) (a+b+1) := by simp
  obtain ⟨_, _, hderiv⟩ := iteratedDeriv_normTwist_moment m𝔽 μ𝔽 χq
    (fun σ _ n ↦ spectralLineJet_functional_moment m𝔽 μ𝔽 χq (adelicTheta f.val) hi σ n) k hz
  have h : (∫ g, modulationWeight m𝔽 a (adelicTheta f.val) g * spectralZeroJet χ b t k g ∂μ𝔽) =
      iteratedDeriv k (fun z ↦ globalThetaMellinIntegral f.val (ideleClassNormTwist χ z)) (shift(a+b,t)) := by
    refine (integral_congr_ae (ae_of_all _ fun g ↦ ?_)).trans hderiv.symm
    have hpos : 0 < ((m𝔽 g).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
    change ((((m𝔽 g).val : ℝ) ^ a : ℝ) : ℂ) * adelicTheta f.val g *
        (quasiCharacterNormTwist (m𝔽).toMonoidHom (m𝔽).continuous χq (shift(b,t)) g * (logNorm g : ℂ)^k) =
      adelicTheta f.val g * (logNorm g : ℂ)^k *
        quasiCharacterNormTwist (m𝔽).toMonoidHom (m𝔽).continuous χq (shift(a+b,t)) g
    rw [quasiCharacterNormTwist_eq_exp, quasiCharacterNormTwist_eq_exp,
      Real.rpow_def_of_pos hpos, Complex.ofReal_exp, Complex.ofReal_mul]
    have e : Complex.exp ((shift(a+b,t)) * (logNorm g : ℂ)) =
        Complex.exp ((logNorm g : ℂ) * (a : ℂ)) * Complex.exp ((shift(b,t)) * (logNorm g : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    change Complex.exp ((logNorm g : ℂ) * (a : ℂ)) * adelicTheta f.val g *
        (χq g * Complex.exp ((shift(b,t)) * (logNorm g : ℂ)) * (logNorm g : ℂ)^k) =
      adelicTheta f.val g * (logNorm g : ℂ)^k * (χq g * Complex.exp ((shift(a+b,t)) * (logNorm g : ℂ)))
    rw [e]
    ring
  exact h.trans (stripTheta_mellin_zero χ f _ k hk)

/-- Paper: Theorem 10.2.2.1, p. 446. Every strip jet annihilates the closed
weighted polar-free theta image.
Deviation: At a strip endpoint the jet order must be strictly below (s − 1) / 2. -/
theorem spectralStripJet_commonKernel_forward (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    {a α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (y : W(-α, α, s))
    (hy : y ∈ globalThetaSobolev F a (stripI(hα)) hs) (j : SpectralStripJetIndex χ a α s) :
    spectralSobolevPairing y ((spectralStripJet_memLp χ hα hs j).toLp (stripJet(χ, j))) = 0 := by
  let u : W'(-α, α, s) := (spectralStripJet_memLp χ hα hs j).toLp (stripJet(χ, j))
  let T := (modulatedIntervalSobolev_dual m𝔽 hm𝔽 μ𝔽 (-α) α s (stripI(hα)) hs).exists.choose
  let Λ := T.symm u
  have hp (v : W(-α, α, s)) : Λ v = spectralSobolevPairing v u :=
    (spectralSobolevPairing_dual (stripI(hα)) hs Λ v).2.trans
      (congrArg (spectralSobolevPairing v) (T.apply_symm_apply u))
  have habs : μ𝔽 ≪ L2μ'(-α, α, s) :=
    withDensity_absolutelyContinuous' (symmIntervalSobolevDensity_inv_continuous hα s).measurable.ennreal_ofReal.aemeasurable
      (.of_forall fun g ↦ ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr (symmIntervalSobolevDensity_pos hα s (logNorm g))))
  have hrep : (u : C𝔽 → ℂ) =ᵐ[μ𝔽] stripJet(χ, j) := habs.ae_le (MemLp.coeFn_toLp _)
  let E := (existsUnique_globalThetaSobolevEmbedding (F := F) a (-α) α s (stripI(hα)) hs).exists.choose
  have hgen (f : adelePolarSubspace F) : Λ (E (Submodule.Quotient.mk f)) = 0 := by
    rw [hp]
    have hE := (existsUnique_globalThetaSobolevEmbedding (F := F) a (-α) α s (stripI(hα)) hs).exists.choose_spec.2 f
    have hN {b : ℝ} (N : ℕ) : spectralStripMultiplicity α s b N ≤ N := by
      unfold spectralStripMultiplicity spectralBoundaryMultiplicity
      split_ifs <;> first | exact le_rfl | exact min_le_left _ _ | exact Nat.zero_le _
    exact (integral_congr_ae (hE.mul hrep)).trans (stripTheta_weighted_moment_zero
      (χ j.val.1) f a j.val.2.1 j.val.2.2.1 j.val.2.2.2 (j.property.trans_le (hN _)))
  have hR : E.toLinearMap.range ≤ Λ.ker := by
    rintro _ ⟨v, rfl⟩
    induction v using Submodule.Quotient.induction_on with
    | H f => exact hgen f
  exact (hp y).symm.trans ((E.toLinearMap.range.topologicalClosure_minimal hR Λ.isClosed_ker) hy)

/-- Paper: Theorem 10.2.2.1, p. 446. A Sobolev vector whose strip moments vanish
can be approximated in the strip norm by weighted polar-free theta tests.
Deviation: The boundary moments use the strict reciprocal-weight cutoff.
Gap: The finite-band projection argument on p. 443 does not construct these
approximants. The complementary projections only exhaust the span of the jet representers. -/
theorem spectralStripJet_approximation (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice χ) {a α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) :
    let u : SpectralStripJetIndex χ a α s → W'(-α, α, s) := stripU(χ, hα, hs)
    let E := (existsUnique_globalThetaSobolevEmbedding (F := F) a (-α) α s (stripI(hα)) hs).exists.choose
    ∀ y : W(-α, α, s), (∀ j, spectralSobolevPairing y (u j) = 0) → ∀ ε > (0 : ℝ),
      ∃ f : adelePolarSubspace F, ‖y - E (Submodule.Quotient.mk f)‖ < ε := by sorry

end StripThetaAnnihilation

/-- Paper: Theorem 10.2.2.1, p. 446. The weighted theta closure is the common
kernel of all surviving strip evaluations.
Gap: The complementary projections of §9.3 exhaust the orthogonal of the
common kernel. Identifying this kernel with the geometric theta closure
requires a separate approximation in the strip norm. -/
theorem spectralStripJet_commonKernel (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice χ) {a α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) :
    let u : SpectralStripJetIndex χ a α s → W'(-α, α, s) := stripU(χ, hα, hs)
    JetKernel(a, stripI(hα), hs, u) := by
  intro u y
  refine ⟨spectralStripJet_commonKernel_forward χ hα hs y, fun hy ↦ ?_⟩
  let E := (existsUnique_globalThetaSobolevEmbedding (F := F) a (-α) α s (stripI(hα)) hs).exists.choose
  change y ∈ closure (E.toLinearMap.range : Set W(-α, α, s))
  refine Metric.mem_closure_iff.mpr fun ε hε ↦ ?_
  obtain ⟨f, hf⟩ := spectralStripJet_approximation χ _hχ hα hs y hy ε hε
  exact ⟨_, ⟨Submodule.Quotient.mk f, rfl⟩, (dist_eq_norm _ _).trans_lt hf⟩

/-- Paper: Theorem 10.2.2.1, p. 446. The individual strip jets admit
interpolants whose classes span densely in the geometric quotient.
Gap: Orthogonal exhaustion by the evaluation representers does not establish
interpolation and density of the biorthogonal vectors. -/
theorem spectralStripJet_denseInterpolants (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice χ) {a α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) :
    let J := SpectralStripJetIndex χ a α s
    let u : J → W'(-α, α, s) := stripU(χ, hα, hs)
    JetInterpolation(J, a, stripI(hα), hs, u) := by sorry

/-- At width zero the real offset of each strip jet is zero, and its remaining
indices give exactly one line jet with the same function representative. -/
private theorem spectralLineJet_zeroWidth_indices (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (a s : ℝ) :
    ∃ e : SpectralLineJetIndex χ a s ≃ SpectralStripJetIndex χ a 0 s,
      ∀ i, stripJet(χ, e i) = lineJet(χ, i) := by
  let L := SpectralLineJetIndex χ a s
  let Z := SpectralStripJetIndex χ a 0 s
  have hoff (j : Z) : j.val.2.1 = 0 := by
    simpa using (SpectralStripJetIndex.mem_strip_order_pos (le_refl (0 : ℝ)) j).1
  have hmult (n : ℕ) : spectralStripMultiplicity 0 s 0 n = spectralBoundaryMultiplicity s n :=
    spectralStripMultiplicity_boundary le_rfl (Or.inr rfl) s n
  let e : L ≃ Z :=
    { toFun := fun i ↦ ⟨(i.val.1, 0, i.val.2.1, i.val.2.2), by
        simpa only [add_zero, hmult] using i.property⟩
      invFun := fun j ↦ ⟨(j.val.1, j.val.2.2.1, j.val.2.2.2), by
        simpa only [hoff j, add_zero, hmult] using j.property⟩
      left_inv := fun _ ↦ Subtype.ext rfl
      right_inv := fun j ↦ Subtype.ext (Prod.ext rfl (Prod.ext (hoff j).symm rfl)) }
  exact ⟨e, fun _ ↦ rfl⟩

/-- Transport a statement about the reindexed reciprocal-weight vectors from
the interval [−0, 0] to the identical line Sobolev space. -/
private theorem spectralLineJet_zeroWidth_transport (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (a : ℝ) {s : ℝ} (hs : 1 < s)
    (P : ∀ {l : ℝ}, l ≤ 0 → (SpectralLineJetIndex χ a s → W'(l, 0, s)) → Prop)
    (h : ∀ (e : SpectralLineJetIndex χ a s ≃ SpectralStripJetIndex χ a 0 s),
      P (stripI(le_refl (0 : ℝ))) (fun i ↦ stripU(χ, le_refl (0 : ℝ), lineHs(hs)) (e i))) :
    P (le_refl (0 : ℝ)) (lineU(χ, hs)) := by
  obtain ⟨e, he⟩ := spectralLineJet_zeroWidth_indices χ a s
  let claim (l : ℝ) (hl : l ≤ 0) := ∀ hm : ∀ i : SpectralLineJetIndex χ a s,
    MemLp (lineJet(χ, i)) 2 L2μ'(l, 0, s), P hl (fun i ↦ (hm i).toLp (lineJet(χ, i)))
  have hstrip : claim (-0) (stripI(le_refl (0 : ℝ))) := by
    intro hm
    have eqv : (fun i ↦ stripU(χ, le_refl (0 : ℝ), lineHs(hs)) (e i)) =
        fun i ↦ (hm i).toLp (lineJet(χ, i)) := by
      funext i
      exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall (congrFun (he i)))
    exact eqv ▸ h e
  have transport (l : ℝ) (hl : l ≤ 0) (hl0 : l = 0) : claim l hl → claim 0 le_rfl := by
    subst l
    exact id
  exact transport (-0) _ neg_zero hstrip (spectralLineJet_memLp χ hs)

section LineThetaSynthesis

open scoped SchwartzMap ContDiff Interval

/-- On Haar-integrable representatives, the zero-line Schwartz action is exactly
multiplication of Fourier transforms on every component. -/
private theorem lineProfile_fourier_action {s : ℝ} (hs : 0 ≤ s) (φ : SchwartzBruhat C𝔽)
    (u : CompactIntervalSobolev μ𝔽 logNorm 0 0 s) (hu : Integrable (u : C𝔽 → ℂ) μ𝔽) :
    let A := (existsUnique_schwartzBruhat_zeroLineAction μ𝔽 m𝔽 s hs).exists.choose
    Integrable (A φ u : C𝔽 → ℂ) μ𝔽 ∧
      lcaFourier μ𝔽 (A φ u) = lcaFourier μ𝔽 φ * lcaFourier μ𝔽 u := by
  intro A
  let w := (μ𝔽).withDensity fun g ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (logNorm g))
  have hle : μ𝔽 ≤ w := by
    calc
      μ𝔽 = (μ𝔽).withDensity 1 := withDensity_one.symm
      _ ≤ _ := withDensity_mono (.of_forall fun g ↦ by
        change 1 ≤ ENNReal.ofReal (intervalSobolevDensity 0 0 s _)
        rw [ENNReal.one_le_ofReal]
        simpa [intervalSobolevDensity] using Real.one_le_rpow
          (le_add_of_nonneg_right (sq_nonneg _)) (by linarith : 0 ≤ s / 2))
  obtain ⟨J, hJ⟩ := exists_L2_restriction w μ𝔽 hle
  have hφ := ((schwartzBruhat_fourier_equiv μ𝔽).choose_spec φ).1
  have hAe : (A φ u : C𝔽 → ℂ) =ᵐ[μ𝔽] lcaConvolution μ𝔽 φ u := (hJ _).symm.trans
    (pettis_convolution_haar_L2 μ𝔽 J hJ (hardySobolevTranslation μ𝔽 m𝔽 0 0 s le_rfl hs)
      (hardySobolevTranslation_apply μ𝔽 m𝔽 0 0 s le_rfl hs)
      (exists_hardySobolevTranslation μ𝔽 m𝔽 0 0 s le_rfl hs).choose_spec.2 φ hφ u (A φ u)
      ((existsUnique_schwartzBruhat_zeroLineAction μ𝔽 m𝔽 s hs).exists.choose_spec φ u))
  refine ⟨(lcaConvolution_integrable μ𝔽 hφ hu).2.1.congr hAe.symm, ?_⟩
  refine Eq.trans (b := lcaFourier μ𝔽 (lcaConvolution μ𝔽 φ u)) ?_ (lcaFourier_convolution μ𝔽 hφ hu)
  funext ψ
  exact integral_congr_ae (hAe.mul Filter.EventuallyEq.rfl)

local notation "WI(" s ")" => CompactIntervalSobolev μ𝔽 logNorm 0 0 s
local notation "Wχ(" χ ", " s ", " hs ")" =>
  actionIsotype ((hardySobolevTranslation μ𝔽 m𝔽 0 0 s le_rfl hs).comp (ideleClassNorm F).ker.subtype) ((χ).comp restriction)

private theorem lineProfile_sobolevLift (χ : PontryaginDual C𝔽) (s : ℝ) (hs : 0 ≤ s)
    (P : 𝓢(ℝ, ℂ) →L[ℂ] SchwartzBruhat C𝔽)
    (hP : ∀ p (k : C₁) x, P p (k.val⁻¹*x) = (χ k.val : ℂ) * P p x) :
    ∃ e : 𝓢(ℝ, ℂ) →ₗ[ℂ] Wχ(χ, s, hs), ∀ p, ((e p).val : C𝔽 → ℂ) =ᵐ[μ𝔽] (P p : C𝔽 → ℂ) := by
  let w := (μ𝔽).withDensity fun g ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (logNorm g))
  have hle : μ𝔽 ≤ w := by
    calc
      μ𝔽 = (μ𝔽).withDensity 1 := withDensity_one.symm
      _ ≤ _ := withDensity_mono (.of_forall fun g ↦ by
        change 1 ≤ ENNReal.ofReal (intervalSobolevDensity 0 0 s _)
        rw [ENNReal.one_le_ofReal]
        simpa [intervalSobolevDensity] using Real.one_le_rpow
          (le_add_of_nonneg_right (sq_nonneg _)) (by linarith : 0 ≤ s / 2))
  have hv (u : SchwartzBruhat C𝔽) : MemLp (u : C𝔽 → ℂ) 2 w := by
    have hmw : w = sobolevMeasure μ𝔽 (modulatedSobolevWeight m𝔽) s := intervalSobolev_zero_eq_sobolevMeasure m𝔽 μ𝔽 s
    exact (congrArg (fun v : Measure C𝔽 ↦ MemLp (u : C𝔽 → ℂ) 2 v) hmw).mpr (SchwartzBruhat.memLp_modulatedSobolev μ𝔽 m𝔽 u s hs)
  let j : SchwartzBruhat C𝔽 →ₗ[ℂ] WI(s) := {
    toFun := fun u ↦ (hv u).toLp u
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun _ _ ↦ rfl }
  have hj (u : SchwartzBruhat C𝔽) : (j u : C𝔽 → ℂ) =ᵐ[μ𝔽] (u : C𝔽 → ℂ) :=
    hle.absolutelyContinuous.ae_eq (hv u).coeFn_toLp
  have hmem (p : 𝓢(ℝ, ℂ)) : j (P p) ∈ Wχ(χ, s, hs) := by
    apply (mem_actionIsotype _ _ _).mpr
    intro k
    apply Lp.ext
    apply (withDensity_absolutelyContinuous μ𝔽 _).ae_eq
    have htr := (measurePreserving_mul_left μ𝔽 k.val⁻¹).quasiMeasurePreserving.ae_eq_comp (hj (P p))
    have hsm := hle.absolutelyContinuous.ae_eq (Lp.coeFn_smul (χ k.val : ℂ) (j (P p)))
    filter_upwards [hardySobolevTranslation_apply μ𝔽 m𝔽 0 0 s le_rfl hs k.val (j (P p)), htr, hsm, hj (P p)] with x h₁ h₂ h₃ h₄
    exact h₁.trans (h₂.trans ((hP p k x).trans ((congrArg ((χ k.val : ℂ) * ·) h₄.symm).trans h₃.symm)))
  let e := (j.comp P.toLinearMap).codRestrict Wχ(χ, s, hs) hmem
  exact ⟨e,fun p ↦ hj (P p)⟩

local notation "EXω(" χ ")" => actionIsotype
  (((exists_modulatedExponentialDecay_translationAction (G := C𝔽) m𝔽 univ hm𝔽 hms𝔽 ordConnected_univ univ_nonempty).choose).comp (ideleClassNorm F).ker.subtype)
  ((χ).comp restriction)
private theorem lineProfile_decay_as_schwartz (χ : PontryaginDual C𝔽) (f : EXω(χ)) :
    ∃ v : SchwartzBruhat C𝔽, (v : C𝔽 → ℂ) = f.val.val ∧
      ∀ (k : C₁) (x : C𝔽), v (k.val⁻¹*x) = (χ k.val : ℂ) * v x := by
  have hW : f.val.val ∈ schwartzBruhatSubmodule C𝔽 := by
    simpa only [modulationWeight_zero] using
      modulationWeight_mem_schwartzBruhat m𝔽 univ ⟨0, mem_univ _⟩ f.val
  let v : SchwartzBruhat C𝔽 := ⟨f.val.val,hW⟩
  have hρ := (exists_modulatedExponentialDecay_translationAction (G := C𝔽) m𝔽 univ
    hm𝔽 hms𝔽 ordConnected_univ univ_nonempty).choose_spec
  have hiso (k : C₁) (x : C𝔽) : v (k.val⁻¹*x) = (χ k.val : ℂ) * v x :=
    (hρ.1 k.val f.val x).symm.trans (congrArg (fun u : ModulatedExponentialDecay m𝔽 univ ↦ u.val x)
      ((mem_actionIsotype _ _ _).mp f.property k))
  exact ⟨v, rfl, hiso⟩

private theorem lineProfile_denseTestMap (χ : PontryaginDual C𝔽) (s : ℝ) (hs : 0 ≤ s) :
    ∃ i : EXω(χ) →L[ℂ] Wχ(χ, s, hs), DenseRange i ∧ ∀ f, ((i f).val : C𝔽 → ℂ) =ᵐ[μ𝔽] f.val.val := by
  let i := (existsUnique_spectralLineTestCompletion (F := F) 0 hs (χ.comp restriction)).exists.choose
  have hi := (existsUnique_spectralLineTestCompletion (F := F) 0 hs (χ.comp restriction)).exists.choose_spec
  exact ⟨i, hi.2.1, fun f ↦ (hi.1 f).trans (.of_forall fun g ↦ congrFun (modulationWeight_zero m𝔽 f.val.val) g)⟩

/-- The distribution-free chart is dense directly in the weighted norm. The
surjectivity on homogeneous Schwartz tests includes the norm-dense concentrated
exponential tests of §10.2.1. -/
private theorem lineProfile_denseEmbedding (χ : PontryaginDual C𝔽) (s : ℝ) (hs : 0 ≤ s)
    (P : 𝓢(ℝ, ℂ) →L[ℂ] SchwartzBruhat C𝔽)
    (honto : ∀ v : SchwartzBruhat C𝔽, (∀ (k : C₁) (x : C𝔽), v (k.val⁻¹*x) = (χ k.val : ℂ) * v x) → ∃ p, P p = v)
    (e : 𝓢(ℝ, ℂ) →ₗ[ℂ] Wχ(χ, s, hs)) (hrep : ∀ p, ((e p).val : C𝔽 → ℂ) =ᵐ[μ𝔽] (P p : C𝔽 → ℂ)) :
    DenseRange e := by
  let H := lineProfile_denseTestMap (F := F) χ s hs
  let i := H.choose
  have hi := H.choose_spec.2
  have hr (f : EXω(χ)) : i f ∈ range e := by
    let v := (lineProfile_decay_as_schwartz (F := F) χ f).choose
    have hv := (lineProfile_decay_as_schwartz (F := F) χ f).choose_spec
    let p := (honto v hv.2).choose
    have hp : P p = v := (honto v hv.2).choose_spec
    have hrep' : ((e p).val : C𝔽 → ℂ) =ᵐ[μ𝔽] f.val.val := (hrep p).trans
      (.of_forall fun g ↦ (congrArg (fun z : SchwartzBruhat C𝔽 ↦ z g) hp).trans (congrFun hv.1 g))
    exact ⟨p, Subtype.ext (Lp.ext ((withDensity_absolutelyContinuous μ𝔽 _).ae_eq (hrep'.trans (hi f).symm)))⟩
  exact H.choose_spec.1.mono (Set.range_subset_iff.mpr hr)

private theorem lineProfile_eq_of_fourier {s : ℝ} (u v : WI(s)) (hu : Integrable (u : C𝔽 → ℂ) μ𝔽)
    (hv : Integrable (v : C𝔽 → ℂ) μ𝔽) (h : ∀ ψ, lcaFourier μ𝔽 u ψ = lcaFourier μ𝔽 v ψ) : u = v := by
  let H := lcaFourier_L1 μ𝔽
  let f : Lp ℂ 1 μ𝔽 := hu.toL1 u
  let g : Lp ℂ 1 μ𝔽 := hv.toL1 v
  have hf : (f : C𝔽 → ℂ) =ᵐ[μ𝔽] (u : C𝔽 → ℂ) := hu.coeFn_toL1
  have hg : (g : C𝔽 → ℂ) =ᵐ[μ𝔽] (v : C𝔽 → ℂ) := hv.coeFn_toL1
  have hfg : H.choose f = H.choose g := by
    apply ZeroAtInftyContinuousMap.ext
    intro ψ
    rw [H.choose_spec.1 f ψ, H.choose_spec.1 g ψ]
    exact (integral_congr_ae (hf.mul EventuallyEq.rfl)).trans
      ((h ψ).trans (integral_congr_ae (hg.symm.mul EventuallyEq.rfl)))
  have hfg' : f = g := H.choose_spec.2.1 hfg
  have hrep : (f : C𝔽 → ℂ) =ᵐ[μ𝔽] (g : C𝔽 → ℂ) := by rw [hfg']
  exact Lp.ext ((withDensity_absolutelyContinuous μ𝔽 _).ae_eq (hf.symm.trans (hrep.trans hg)))

private theorem lineProfile_action_of_symbols {s : ℝ} (hs : 0 ≤ s) (φ : SchwartzBruhat C𝔽)
    (u v : WI(s)) (hu : Integrable (u : C𝔽 → ℂ) μ𝔽) (hv : Integrable (v : C𝔽 → ℂ) μ𝔽)
    (heq : ∀ ψ, lcaFourier μ𝔽 φ ψ * lcaFourier μ𝔽 u ψ = lcaFourier μ𝔽 v ψ) :
    (existsUnique_schwartzBruhat_zeroLineAction μ𝔽 m𝔽 s hs).exists.choose φ u = v := by
  have h := lineProfile_fourier_action (F := F) (s := s) hs φ u hu
  exact lineProfile_eq_of_fourier (F := F) (s := s) _ v h.1 hv (fun ψ ↦ (congrFun h.2 ψ).trans (heq ψ))

/-- Multiplication by an arbitrary real Schwartz profile in the frequency chart
equals the ambient zero-line action of its inverse Fourier kernel. -/
private theorem lineProfile_chart_intertwine (χ : PontryaginDual C𝔽) (s : ℝ) (hs : 0 ≤ s)
    (P : 𝓢(ℝ, ℂ) →L[ℂ] SchwartzBruhat C𝔽) (γ : ℝ → PontryaginDual C𝔽)
    (hF : ∀ p t, lcaFourier μ𝔽 (P p) (γ t) = p t)
    (hoff : ∀ p ψ, ψ ∉ range γ → lcaFourier μ𝔽 (P p) ψ = 0)
    (e : 𝓢(ℝ, ℂ) →ₗ[ℂ] Wχ(χ, s, hs)) (hrep : ∀ p, ((e p).val : C𝔽 → ℂ) =ᵐ[μ𝔽] (P p : C𝔽 → ℂ))
    (h p : 𝓢(ℝ, ℂ)) :
    let A := (existsUnique_schwartzBruhat_zeroLineAction μ𝔽 m𝔽 s hs).exists.choose
    A (P h) (e p).val = (e (SchwartzMap.smulLeftCLM ℂ (h : ℝ → ℂ) p)).val := by
  intro A
  have hi (p : 𝓢(ℝ, ℂ)) : Integrable ((e p).val : C𝔽 → ℂ) μ𝔽 := (SchwartzBruhat.integrable μ𝔽 (P p)).congr (hrep p).symm
  have hhat (p : 𝓢(ℝ, ℂ)) (ψ) : lcaFourier μ𝔽 (e p).val ψ = lcaFourier μ𝔽 (P p) ψ :=
    integral_congr_ae ((hrep p).mul EventuallyEq.rfl)
  let q := SchwartzMap.smulLeftCLM ℂ (h : ℝ → ℂ) p
  apply lineProfile_action_of_symbols (F := F) (s := s) hs (P h) (e p).val (e q).val (hi p) (hi q)
  intro ψ
  refine (congrArg (lcaFourier μ𝔽 (P h) ψ * ·) (hhat p ψ)).trans (Eq.trans ?_ (hhat q ψ).symm)
  by_cases hψ : ψ ∈ range γ
  · obtain ⟨t,rfl⟩ := hψ
    exact (congrArg₂ (· * ·) (hF h t) (hF p t)).trans
      (((SchwartzMap.smulLeftCLM_apply_apply h.hasTemperateGrowth p t).symm).trans (hF q t).symm)
  · rw [hoff h ψ hψ, zero_mul, hoff q ψ hψ]

private theorem lineProfile_chart_multiplier (χ : PontryaginDual C𝔽) (s : ℝ) (hs : 0 ≤ s)
    (P : 𝓢(ℝ, ℂ) →L[ℂ] SchwartzBruhat C𝔽) (e : 𝓢(ℝ, ℂ) →ₗ[ℂ] Wχ(χ, s, hs))
    (hint : ∀ h p : 𝓢(ℝ, ℂ), (existsUnique_schwartzBruhat_zeroLineAction μ𝔽 m𝔽 s hs).exists.choose (P h) (e p).val =
      (e (SchwartzMap.smulLeftCLM ℂ (h : ℝ → ℂ) p)).val) (h : 𝓢(ℝ, ℂ)) :
    ∃ T : Wχ(χ, s, hs) →L[ℂ] Wχ(χ, s, hs), ∀ p,
      T (e p) = e (SchwartzMap.smulLeftCLM ℂ (h : ℝ → ℂ) p) := by
  let A := (existsUnique_schwartzBruhat_zeroLineAction μ𝔽 m𝔽 s hs).exists.choose
  let E := Wχ(χ, s, hs)
  let τ := hardySobolevTranslation μ𝔽 m𝔽 0 0 s le_rfl hs
  have hmem (v : E) : A (P h) v.val ∈ E := by
    apply (mem_actionIsotype _ _ _).mpr
    intro k
    exact spectral_integrated_action_eigenvector μ𝔽 τ (P h : C𝔽 → ℂ) v.val _
      ((existsUnique_schwartzBruhat_zeroLineAction μ𝔽 m𝔽 s hs).exists.choose_spec _ _) k.val (χ k.val : ℂ)
      ((mem_actionIsotype _ _ _).mp v.property k)
  exact ⟨((A (P h)).comp E.subtypeL).codRestrict E hmem, fun p ↦ Subtype.ext (hint h p)⟩

private theorem lineProfile_compact_of_frequencyBand (χ : PontryaginDual C𝔽) (γ : ℝ → PontryaginDual C𝔽)
    (hγ : ∀ t x, γ t x = (χ x)⁻¹ * Circle.exp (-t * logNorm x)) (p : 𝓢(ℝ, ℂ))
    (φ : SchwartzBruhat C𝔽) (n : ℕ) (hF : ∀ t, lcaFourier μ𝔽 φ (γ t) = p t)
    (hband : tsupport (lcaFourier μ𝔽 φ) ⊆ modulatedFrequencyBand m𝔽 χ⁻¹ (-(n:ℝ)) n) :
    HasCompactSupport (p : ℝ → ℂ) := by
  obtain ⟨u, hu⟩ := exists_modulatedFrequencyLine m𝔽 hm𝔽 hms𝔽
  have hcurve (t : ℝ) : γ t = χ⁻¹ * (u (Multiplicative.ofAdd (-t))).val :=
    PontryaginDual.ext fun x ↦ (hγ t x).trans (congrArg ((χ x)⁻¹ * ·) (hu (-t) x).symm)
  have hcov : support (p : ℝ → ℂ) ⊆ Icc (-(n:ℝ)) n := by
    intro t ht
    have hh : γ t ∈ support (lcaFourier μ𝔽 φ) := by change lcaFourier μ𝔽 φ (γ t) ≠ 0; rwa [hF t]
    have hb := hband (subset_tsupport _ hh)
    obtain ⟨v, hv, hvψ⟩ := hb
    have heq : χ⁻¹ * (u (Multiplicative.ofAdd v)).val = γ t :=
      PontryaginDual.ext fun x ↦ (congrArg ((χ x)⁻¹ * ·) (hu v x)).trans (hvψ x).symm
    rw [hcurve] at heq
    have ht' : v = -t := congrArg Multiplicative.toAdd (u.injective (Subtype.ext (mul_left_cancel heq)))
    constructor <;> linarith [hv.1,hv.2]
  exact isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (closure_minimal hcov isClosed_Icc)

/-- The Chapter 10 isotype approximate identity has genuine compactly supported
ordinary Schwartz symbols in the normalized chart, and converges strongly in the
Sobolev norm of that isotype. -/
private theorem lineProfile_chart_approximateUnit (χ : PontryaginDual C𝔽) (s : ℝ) (hs : 0 ≤ s)
    (P : 𝓢(ℝ, ℂ) →L[ℂ] SchwartzBruhat C𝔽) (γ : ℝ → PontryaginDual C𝔽)
    (hγ : ∀ t x, γ t x = (χ x)⁻¹ * Circle.exp (-t * logNorm x))
    (hF : ∀ p t, lcaFourier μ𝔽 (P p) (γ t) = p t)
    (honto : ∀ v : SchwartzBruhat C𝔽, (∀ (k : C₁) (x : C𝔽), v (k.val⁻¹*x) = (χ k.val : ℂ) * v x) → ∃ p, P p = v)
    (e : 𝓢(ℝ, ℂ) →ₗ[ℂ] Wχ(χ, s, hs))
    (hint : ∀ h p : 𝓢(ℝ, ℂ), (existsUnique_schwartzBruhat_zeroLineAction μ𝔽 m𝔽 s hs).exists.choose (P h) (e p).val =
      (e (SchwartzMap.smulLeftCLM ℂ (h : ℝ → ℂ) p)).val) :
    ∃ (g : ℕ → 𝓢(ℝ, ℂ)) (T : ℕ → Wχ(χ, s, hs) →L[ℂ] Wχ(χ, s, hs)),
      (∀ n, HasCompactSupport (g n : ℝ → ℂ)) ∧ (∀ n p, T n (e p) = e (SchwartzMap.smulLeftCLM ℂ (g n : ℝ → ℂ) p)) ∧
      ∀ y, Tendsto (fun n ↦ T n y) atTop (𝓝 y) := by
  let H := exists_spectralLineIsotypeConvolution (F := F) χ hs
  let φ := H.choose
  let T := H.choose_spec.choose
  have hu := H.choose_spec.choose_spec
  let g (n : ℕ) := (honto (φ n) (hu.2.1 n)).choose
  have hg (n : ℕ) : P (g n) = φ n := (honto (φ n) (hu.2.1 n)).choose_spec
  refine ⟨g,T,fun n ↦ ?_, fun n p ↦ ?_, hu.2.2.2.2⟩
  · exact lineProfile_compact_of_frequencyBand (F := F) χ γ hγ (g n) (φ n) n
      (fun t ↦ (congrArg (fun f : SchwartzBruhat C𝔽 ↦ lcaFourier μ𝔽 f (γ t)) (hg n).symm).trans (hF (g n) t)) (hu.2.2.1 n)
  · apply Subtype.ext
    exact (hu.2.2.2.1 n (e p)).trans (((congrArg (fun f : SchwartzBruhat C𝔽 ↦
      (existsUnique_schwartzBruhat_zeroLineAction μ𝔽 m𝔽 s hs).exists.choose f (e p).val) (hg n).symm)).trans (hint (g n) p))

private theorem lineProfile_pettis_mem_closed {X V : Type*}
    [Group X] [MeasurableSpace X] (μ : Measure X) [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V] (K : Submodule ℂ V) (hK : IsClosed (K : Set V))
    (τ : X →* (V →L[ℂ] V)) (hτ : ∀ g, ∀ v ∈ K, τ g v ∈ K) {ψ : X → ℂ} {u b : V}
    (hu : u ∈ K) (hb : HasPettisIntegral (.positive μ) (fun g ↦ ψ g • τ g u) b) : b ∈ K := by
  have : CompleteSpace K := hK.completeSpace_coe
  rw [← K.orthogonal_orthogonal]
  intro w hw
  have hδ := congrArg
    (fun z : PettisWeakCompletion V ↦ (show Module.Dual ℂ (StrongDual ℂ V) from z)
      (innerSL ℂ w)) hb.2
  change innerSL ℂ w b = ∫ g, innerSL ℂ w (ψ g • τ g u) ∂μ at hδ
  rw [innerSL_apply_apply] at hδ
  rw [hδ]
  refine integral_eq_zero_of_ae (.of_forall fun g ↦ ?_)
  change innerSL ℂ w (ψ g • τ g u) = 0
  rw [innerSL_apply_apply]
  exact (K.mem_orthogonal' w).mp hw _ (K.smul_mem _ (hτ g u hu))

/-- All Schwartz convolutions on the zero-width line preserve the closed weighted
theta image, including the inverse transforms of arbitrary smooth compact frequency profiles. -/
private theorem lineProfile_preserves_theta (a : ℝ) {s : ℝ} (hs : 0 ≤ s) (φ : SchwartzBruhat C𝔽) :
    let K := globalThetaSobolev F a (le_rfl : (0 : ℝ) ≤ 0) hs
    let A := (existsUnique_schwartzBruhat_zeroLineAction μ𝔽 m𝔽 s hs).exists.choose
    ∀ v ∈ K, A φ v ∈ K := by
  intro K A v hv
  let τ := hardySobolevTranslation μ𝔽 m𝔽 0 0 s le_rfl hs
  obtain ⟨ρ, hρ, -, -⟩ := exists_globalThetaSobolevAction (F := F) a (le_rfl : (0 : ℝ) ≤ 0) hs
  have hτ (g : C𝔽) : ∀ v ∈ K, τ g v ∈ K := fun v hv ↦
    (hρ g ⟨v,hv⟩) ▸ (ρ g ⟨v,hv⟩).property
  exact lineProfile_pettis_mem_closed μ𝔽 K (Submodule.isClosed_topologicalClosure _) τ hτ hv
    ((existsUnique_schwartzBruhat_zeroLineAction μ𝔽 m𝔽 s hs).exists.choose_spec φ v)

/-- On the normalized line the ordinary Fourier transform of the centered theta
representative is its global theta Mellin transform, evaluated at the shifted center. -/
private theorem lineProfile_weightedTheta (χ : PontryaginDual C𝔽) (a : ℝ)
    (γ : ℝ → PontryaginDual C𝔽) (hγ : ∀ t x, γ t x = (χ x)⁻¹ * Circle.exp (-t * logNorm x))
    (f : adelePolarSubspace F) :
    Integrable (modulationWeight m𝔽 a (adelicTheta f.val)) μ𝔽 ∧ ∀ t,
      lcaFourier μ𝔽 (modulationWeight m𝔽 a (adelicTheta f.val)) (γ t) =
      globalThetaMellinIntegral f.val (ideleClassNormTwist χ (shift(a, t))) := by
  obtain ⟨hf,hf'⟩ := (mem_adelePolarSubspace f.val).mp f.property
  have hw (g : C𝔽) :
      adelicTheta f.val g * (ideleClassNormTwist (1 : PontryaginDual C𝔽) (a : ℂ)) g =
      modulationWeight m𝔽 a (adelicTheta f.val) g := by
    have hp : 0 < ((m𝔽 g).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
    change _ * ((1 : ℂ) * (((m𝔽 g).val : ℝ) : ℂ) ^ (a : ℂ)) = ((((m𝔽 g).val : ℝ) ^ a : ℝ) : ℂ) * _
    rw [one_mul, ← Complex.ofReal_cpow hp.le]
    exact mul_comm _ _
  refine ⟨(globalThetaMellinIntegral_integrable_of_vanishing f.val hf hf' _).congr (.of_forall hw), fun t ↦ ?_⟩
  apply integral_congr_ae
  refine .of_forall fun g ↦ ?_
  have hp : 0 < ((m𝔽 g).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hψ : γ t g = (χ g * Circle.exp (t * logNorm g))⁻¹ := by
    rw [hγ, neg_mul, Circle.exp_neg, mul_inv]
  have hph : star (γ t g : ℂ) = (χ g : ℂ) * Complex.exp (((t * logNorm g : ℝ) : ℂ) * Complex.I) := by
    rw [hψ, Circle.coe_inv_eq_conj, ← Complex.star_def, star_star, Circle.coe_mul, Circle.coe_exp]
  change modulationWeight m𝔽 a (adelicTheta f.val) g * star (γ t g : ℂ) = _
  rw [hph]
  change (((((m𝔽 g).val : ℝ) ^ a : ℝ) : ℂ) * adelicTheta f.val g) * _ =
    adelicTheta f.val g * ((χ g : ℂ) * ((((m𝔽 g).val : ℝ) : ℂ) ^ (shift(a, t))))
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne'), ← Complex.ofReal_log hp.le,
    Real.rpow_def_of_pos hp, Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_mul,
    mul_add, Complex.exp_add]
  rw [show (t : ℂ) * (logNorm g : ℂ) * Complex.I = (logNorm g : ℂ) * ((t : ℂ) * Complex.I) by ring]
  ring_nf
  rfl

/-- A Schwartz profile given by a multiplier times an adelic polar-free Mellin
transform belongs to the closed global theta space in the weighted isotype. -/
private theorem lineProfile_theta_generator (χ : PontryaginDual C𝔽) (a s : ℝ) (hs : 0 ≤ s)
    (P : 𝓢(ℝ, ℂ) →L[ℂ] SchwartzBruhat C𝔽) (γ : ℝ → PontryaginDual C𝔽)
    (hγ : ∀ t x, γ t x = (χ x)⁻¹ * Circle.exp (-t * logNorm x))
    (hF : ∀ p t, lcaFourier μ𝔽 (P p) (γ t) = p t)
    (hoff : ∀ p ψ, ψ ∉ range γ → lcaFourier μ𝔽 (P p) ψ = 0)
    (e : 𝓢(ℝ, ℂ) →ₗ[ℂ] Wχ(χ, s, hs)) (hrep : ∀ p, ((e p).val : C𝔽 → ℂ) =ᵐ[μ𝔽] (P p : C𝔽 → ℂ))
    (f : adelePolarSubspace F) (h p : 𝓢(ℝ, ℂ))
    (hp : ∀ t, p t = h t * globalThetaMellinIntegral f.val (ideleClassNormTwist χ (shift(a, t)))) :
    (e p).val ∈ globalThetaSobolev F a (le_rfl : (0:ℝ) ≤ 0) hs := by
  let E := (existsUnique_globalThetaSobolevEmbedding (F := F) a 0 0 s le_rfl hs).exists.choose
  let u := E (Submodule.Quotient.mk f)
  have hu := (existsUnique_globalThetaSobolevEmbedding (F := F) a 0 0 s le_rfl hs).exists.choose_spec.2 f
  have hm := lineProfile_weightedTheta χ a γ hγ f
  have hi : Integrable (u : C𝔽 → ℂ) μ𝔽 := hm.1.congr hu.symm
  have hv := (SchwartzBruhat.integrable μ𝔽 (P p)).congr (hrep p).symm
  have huF (t) : lcaFourier μ𝔽 u (γ t) = globalThetaMellinIntegral f.val (ideleClassNormTwist χ (shift(a, t))) :=
    (integral_congr_ae (hu.mul EventuallyEq.rfl)).trans (hm.2 t)
  have hEq : (existsUnique_schwartzBruhat_zeroLineAction μ𝔽 m𝔽 s hs).exists.choose (P h) u = (e p).val := by
    apply lineProfile_action_of_symbols (F := F) (s := s) hs (P h) u (e p).val hi hv
    intro ψ
    refine Eq.trans (b := lcaFourier μ𝔽 (P p) ψ) ?_ (integral_congr_ae ((hrep p).symm.mul EventuallyEq.rfl))
    by_cases hψ : ψ ∈ range γ
    · obtain ⟨t,rfl⟩ := hψ
      rw [hF, huF, hF, hp t]
    · rw [hoff h ψ hψ, zero_mul, hoff p ψ hψ]
  rw [← hEq]
  exact lineProfile_preserves_theta (F := F) a hs (P h) u
    (Submodule.le_topologicalClosure _ (LinearMap.mem_range_self E.toLinearMap _))

/-- The finite span of smooth symbols multiplied by compact Schwartz cutoffs
maps into a submodule once its individual Schwartz generators do. -/
private theorem lineProfile_theta_compact_ideal {E I : Type*} [AddCommMonoid E] [Module ℂ E]
    (e : 𝓢(ℝ, ℂ) →ₗ[ℂ] E) (N : Submodule ℂ E) (Z : I → ℝ → ℂ)
    (hZ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (Z i))
    (hgen : ∀ (i : I) (h p : 𝓢(ℝ, ℂ)), (∀ t, p t = h t * Z i t) → e p ∈ N)
    (p : 𝓢(ℝ, ℂ)) (hspan : (p : ℝ → ℂ) ∈ Submodule.span ℂ {v : ℝ → ℂ |
      ∃ (i : I) (h : 𝓢(ℝ, ℂ)), HasCompactSupport (h : ℝ → ℂ) ∧ ∀ t, v t = h t * Z i t}) :
    e p ∈ N := by
  let C : 𝓢(ℝ, ℂ) →ₗ[ℂ] (ℝ → ℂ) := { toFun := fun h ↦ h, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  have hle : Submodule.span ℂ {v : ℝ → ℂ | ∃ (i : I) (h : 𝓢(ℝ, ℂ)),
      HasCompactSupport (h : ℝ → ℂ) ∧ ∀ t, v t = h t * Z i t} ≤ (N.comap e).map C := by
    apply Submodule.span_le.mpr
    rintro v ⟨i,h,hc,hv⟩
    have heq : v = (h : ℝ → ℂ) * Z i := funext hv
    have hvc : HasCompactSupport v := heq ▸ hc.mul_right
    have hvd : ContDiff ℝ (⊤ : ℕ∞) v := heq ▸ (h.smooth _).mul (hZ i)
    let q := hvc.toSchwartzMap hvd
    exact ⟨q, hgen i h q hv, rfl⟩
  obtain ⟨q,hq,heq⟩ := hle hspan
  exact (show q = p from DFunLike.ext q p (congrFun heq)) ▸ hq

/-- A smooth one-variable function whose first `m` Taylor coefficients vanish is
smoothly divisible by the corresponding power of the coordinate, including at the point. -/
private theorem lineProfile_smooth_divide {f : ℝ → ℂ} (hf : ContDiff ℝ (∞) f)
    (a : ℝ) (m : ℕ) (hj : ∀ k < m, iteratedDeriv k f a = 0) :
    ∃ q : ℝ → ℂ, ContDiff ℝ (∞) q ∧ ∀ x, f x = ((x - a) ^ m : ℝ) • q x := by
  cases m with
  | zero => exact ⟨f, hf, fun x ↦ by simp⟩
  | succ n =>
    let D := iteratedDeriv (n+1) f
    let Z (x u : ℝ) := ((1-u)^n / n.factorial : ℝ) • D ((x-a)*u+a)
    let q (x : ℝ) := ∫ u in Ioc (0 : ℝ) 1, Z x u
    have hD : ContDiff ℝ (∞) D := by
      simpa only [D, iteratedDeriv_eq_iterate] using ContDiff.iterate_deriv (n+1) hf
    have hq : ContDiff ℝ (∞) q := by
      apply ContDiff.parametric_integral (μ := volume) (f := Z) isCompact_Icc (Ioc_subset_Icc_self) (by simp)
      change ContDiff ℝ (∞) (fun v : ℝ × ℝ ↦ ((1-v.2)^n / n.factorial : ℝ) • D ((v.1-a)*v.2+a))
      exact (by fun_prop : ContDiff ℝ (∞) (fun v : ℝ × ℝ ↦ (1-v.2)^n / (n.factorial : ℝ))).smul (hD.comp (by fun_prop))
    refine ⟨q, hq, fun x ↦ ?_⟩
    rcases eq_or_ne a x with rfl | hax
    · simpa using hj 0 (by omega)
    have hu : UniqueDiffOn ℝ (uIcc a x) := uniqueDiffOn_uIcc hax
    have hder (k : ℕ) (z : ℝ) (hz : z ∈ uIcc a x) : iteratedDerivWithin k f (uIcc a x) z = iteratedDeriv k f z :=
      iteratedDerivWithin_eq_iteratedDeriv hu ((hf.of_le (by simp)).contDiffAt) hz
    have hzero : taylorWithinEval f n (uIcc a x) a x = 0 := by
      rw [taylor_within_apply]
      apply Finset.sum_eq_zero
      intro k hk
      rw [hder _ _ left_mem_uIcc, hj k (Finset.mem_range.mp hk), smul_zero]
    let H (t : ℝ) := ((x-t)^n / n.factorial : ℝ) • D t
    have hF : f x = ∫ t in a..x, H t := by
      have h := taylor_integral_remainder (x := x) (x₀ := a) (n := n) ((hf.of_le (by simp)).contDiffOn)
      rw [hzero, sub_zero] at h
      refine h.trans (intervalIntegral.integral_congr fun t ht ↦ ?_)
      rw [hder _ _ ht]
    have hchange := intervalIntegral.smul_integral_comp_mul_add (a := (0:ℝ)) (b := 1) H (x-a) a
    have hh (u : ℝ) : H ((x-a)*u+a) = (x-a)^n • Z x u := by
      simp only [H, Z, smul_smul]
      rw [show x-((x-a)*u+a) = (x-a)*(1-u) by ring, mul_pow]
      congr 1
      ring
    rw [show q x = ∫ u in (0:ℝ)..1, Z x u from (intervalIntegral.integral_of_le (by norm_num)).symm]
    calc
      f x = ∫ t in a..x, H t := hF
      _ = (x-a) • ∫ u in (0:ℝ)..1, H ((x-a)*u+a) := by simpa only [zero_mul, one_mul, mul_zero, mul_one, zero_add, sub_add_cancel] using hchange.symm
      _ = (x-a) • (x-a)^n • ∫ u in (0:ℝ)..1, Z x u := by simp_rw [hh, intervalIntegral.integral_smul]
      _ = (x-a)^(n+1) • ∫ u in (0:ℝ)..1, Z x u := by rw [smul_smul, pow_succ']

/-- A frequency cutoff supported on a patch where a symbol has the prescribed
zero order turns local smooth division into a compactly supported multiplier. -/
private theorem lineProfile_compact_divide {p b e G : ℝ → ℂ} (hp : ContDiff ℝ (∞) p)
    (hb : ContDiff ℝ (∞) b) (hc : HasCompactSupport b) (a : ℝ) (m : ℕ)
    (hj : ∀ k < m, iteratedDeriv k p a = 0) (hone : ∀ x, p x ≠ 0 → b x = 1)
    (hunit : ∀ x ∈ tsupport b, ContDiffAt ℝ (∞) e x ∧ e x ≠ 0 ∧ G x = ((x-a)^m : ℝ) • e x) :
    ∃ h : ℝ → ℂ, ContDiff ℝ (∞) h ∧ HasCompactSupport h ∧ ∀ x, p x = h x * G x := by
  obtain ⟨q, hq, hdiv⟩ := lineProfile_smooth_divide hp a m hj
  let h := fun x ↦ b x * (q x / e x)
  have hh : ContDiff ℝ (∞) h := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ tsupport b
    · simpa only [h, div_eq_mul_inv] using hb.contDiffAt.mul (hq.contDiffAt.mul ((hunit x hx).1.fun_inv (hunit x hx).2.1))
    · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      exact (notMem_tsupport_iff_eventuallyEq.mp hx).mono fun y hy ↦ by simp [h, hy]
  refine ⟨h, hh, hc.mul_right, fun x ↦ ?_⟩
  have hp' : p x = b x * p x := by
    by_cases hx : p x = 0
    · simp [hx]
    · rw [hone x hx, one_mul]
  by_cases hx : x ∈ tsupport b
  · rw [hp', hdiv x, (hunit x hx).2.2]
    dsimp only [h]
    simp only [Complex.real_smul]
    field_simp [(hunit x hx).2.1]
  · rw [hp', show h x = 0 by simp [h, image_eq_zero_of_notMem_tsupport hx],
      image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_mul]

/-- On a vertical frequency line an exact complex analytic order gives a smooth
nonvanishing local unit times the corresponding power of the real coordinate. -/
private theorem lineProfile_analyticFactor {Z : ℂ → ℂ} (a t₀ : ℝ) (m : ℕ)
    (hZ : AnalyticAt ℂ Z ((a : ℂ) + (t₀ : ℂ) * Complex.I))
    (hord : meromorphicOrderAt Z ((a : ℂ) + (t₀ : ℂ) * Complex.I) = (m : WithTop ℤ)) :
    ∃ (U : Set ℝ) (e : ℝ → ℂ), IsOpen U ∧ t₀ ∈ U ∧ ∀ t ∈ U,
      ContDiffAt ℝ (∞) e t ∧ e t ≠ 0 ∧ Z ((a : ℂ) + (t : ℂ) * Complex.I) = ((t - t₀) ^ m : ℝ) • e t := by
  let A (t : ℝ) : ℂ := (a : ℂ) + (t : ℂ) * Complex.I
  have hA : ContDiff ℝ (∞) A := contDiff_const.add (Complex.ofRealCLM.contDiff.mul contDiff_const)
  have hz : analyticOrderAt Z (A t₀) = (m : ℕ∞) := by
    rw [hZ.meromorphicOrderAt_eq] at hord
    cases h : analyticOrderAt Z (A t₀) with
    | top => change (analyticOrderAt Z (A t₀)).map (fun n : ℕ ↦ (n : ℤ)) = _ at hord; simp [h] at hord
    | coe r =>
      change (analyticOrderAt Z (A t₀)).map (fun n : ℕ ↦ (n : ℤ)) = _ at hord
      rw [h, ENat.map_natCast] at hord
      congr 1
      exact_mod_cast (WithTop.coe_eq_coe.mp hord)
  obtain ⟨g, hg, hg₀, heq⟩ := hZ.analyticOrderAt_eq_natCast.mp hz
  let e (t : ℝ) := Complex.I ^ m * g (A t)
  have hall : ∀ᶠ z in 𝓝 (A t₀), AnalyticAt ℂ g z ∧ g z ≠ 0 ∧ Z z = (z - A t₀) ^ m • g z :=
    hg.eventually_analyticAt.and (hg.continuousAt.eventually_ne hg₀ |>.and heq)
  have hnear := hA.continuous.continuousAt.preimage_mem_nhds hall
  obtain ⟨U, hsub, hopen, ht₀⟩ := mem_nhds_iff.mp hnear
  refine ⟨U, e, hopen, ht₀, fun t ht ↦ ?_⟩
  obtain ⟨hg, hne, hform⟩ := hsub ht
  refine ⟨contDiffAt_const.mul ((hg.restrictScalars (𝕜 := ℝ)).contDiffAt.comp t hA.contDiffAt),
    mul_ne_zero (pow_ne_zero _ Complex.I_ne_zero) hne, ?_⟩
  rw [hform]
  simp only [e, A, smul_eq_mul, Complex.real_smul, Complex.ofReal_pow, Complex.ofReal_sub]
  rw [show (a : ℂ) + t * Complex.I - (a + t₀ * Complex.I) = (t - t₀) * Complex.I by ring, mul_pow, mul_assoc]

/-- Every fixed real frequency has a neighborhood and a single polar-free theta test
generating all smooth profiles there with vanishing Taylor jet through the local Hecke order.
The multiplier is a compactly supported Schwartz function on the whole frequency line. -/
private theorem lineProfile_theta_compact_patch (χ : PontryaginDual C𝔽) (a t₀ : ℝ) :
    let m := (meromorphicOrderAt (continuedCompletedHeckeL χ) (shift(a, t₀))).untop₀.toNat
    ∃ (f : adelePolarSubspace F) (r : ℝ), 0 < r ∧ ∀ (p : ℝ → ℂ), ContDiff ℝ (∞) p →
      tsupport p ⊆ Metric.ball t₀ r → (∀ k < m, iteratedDeriv k p t₀ = 0) →
      ∃ h : 𝓢(ℝ, ℂ), HasCompactSupport (h : ℝ → ℂ) ∧ ∀ t,
        p t = h t * globalThetaMellinIntegral f.val (ideleClassNormTwist χ (shift(a, t))) := by
  intro m
  let L := continuedCompletedHeckeL χ
  let w : ℂ := shift(a, t₀)
  obtain ⟨hL, hLval⟩ := continuedCompletedHeckeL_spec χ
  have hfinite : meromorphicOrderAt L w ≠ ⊤ := by
    apply hL.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
      isPreconnected_univ (x := 2) (mem_univ _) (mem_univ w)
    intro htop
    have hp : 0 < meromorphicOrderAt L 2 := htop ▸ WithTop.coe_lt_top (0 : ℤ)
    have hbad := completedHeckeL_continuation_zeros χ L hL hLval (by norm_num : 0 < (2 : ℂ).re) hp
    norm_num at hbad
  have hm : max 0 (meromorphicOrderAt L w) = (m : WithTop ℤ) := by
    change max 0 (meromorphicOrderAt L w) = ((meromorphicOrderAt L w).untop₀.toNat : WithTop ℤ)
    cases ho : meromorphicOrderAt L w with
    | top => exact (hfinite ho).elim
    | coe z =>
      rw [WithTop.untop₀_coe]
      change max ((0 : ℤ) : WithTop ℤ) (z : WithTop ℤ) = ((z.toNat : ℤ) : WithTop ℤ)
      rw [← WithTop.coe_max, WithTop.coe_eq_coe]
      omega
  obtain ⟨f, hf⟩ := (isLeast_globalThetaMellinIntegral_orders χ w).1
  obtain ⟨hf₀, hf₁⟩ := (mem_adelePolarSubspace f.val).mp f.property
  let Z := fun z ↦ globalThetaMellinIntegral f.val (ideleClassNormTwist χ z)
  have han : AnalyticAt ℂ Z w :=
    (globalThetaMellinIntegral_entire_of_vanishing f.val hf₀ hf₁ χ).analyticAt w
  obtain ⟨U, e, hU, ht₀, hu⟩ := lineProfile_analyticFactor a t₀ m han (hf.trans hm)
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds ht₀)
  let B : ContDiffBump t₀ := ⟨r / 4, r / 2, by positivity, by linarith⟩
  let b := fun t ↦ ((B t : ℝ) : ℂ)
  have hbs : tsupport b ⊆ U := by
    refine (tsupport_comp_subset Complex.ofReal_zero B).trans ?_
    rw [B.tsupport_eq]
    exact (Metric.closedBall_subset_ball (by change r / 2 < r; linarith)).trans hsub
  refine ⟨f, r / 4, by positivity, fun p hp hs hj ↦ ?_⟩
  have hone (t : ℝ) (ht : p t ≠ 0) : b t = 1 := by
    have ht' : t ∈ Metric.closedBall t₀ B.rIn :=
      Metric.ball_subset_closedBall (hs (subset_tsupport _ (mem_support.mpr ht)))
    simp [b, B.one_of_mem_closedBall ht']
  obtain ⟨h, hh, hc, heq⟩ := lineProfile_compact_divide (G := fun t ↦ Z (shift(a, t)))
    hp (Complex.ofRealCLM.contDiff.comp B.contDiff) (B.hasCompactSupport.comp_left Complex.ofReal_zero)
    t₀ m hj hone (fun t ht ↦ hu t (hbs ht))
  exact ⟨hc.toSchwartzMap hh, hc, heq⟩

/-- On an entire frequency component, any compactly supported smooth profile which
vanishes to full Hecke order at every zero is a finite linear combination of exact
theta profiles times compactly supported Schwartz multipliers. -/
private theorem lineProfile_theta_compact_span (χ : PontryaginDual C𝔽) (a : ℝ)
    (p : ℝ → ℂ) (hp : ContDiff ℝ (∞) p) (hc : HasCompactSupport p)
    (hj : ∀ (t : ℝ) (k : ℕ), k < (meromorphicOrderAt (continuedCompletedHeckeL χ) (shift(a, t))).untop₀.toNat →
      iteratedDeriv k p t = 0) :
    p ∈ Submodule.span ℂ {v : ℝ → ℂ | ∃ (f : adelePolarSubspace F) (h : 𝓢(ℝ, ℂ)),
      HasCompactSupport (h : ℝ → ℂ) ∧ ∀ t, v t = h t *
        globalThetaMellinIntegral f.val (ideleClassNormTwist χ (shift(a, t)))} := by
  classical
  let S := Submodule.span ℂ {v : ℝ → ℂ | ∃ (f : adelePolarSubspace F) (h : 𝓢(ℝ, ℂ)),
    HasCompactSupport (h : ℝ → ℂ) ∧ ∀ t, v t = h t *
      globalThetaMellinIntegral f.val (ideleClassNormTwist χ (shift(a, t)))}
  choose f r hr hpatch using fun t : ℝ ↦ lineProfile_theta_compact_patch χ a t
  have hlocal (i : ℝ) (q : ℝ → ℂ) (hq : ContDiff ℝ (∞) q) (hsub : tsupport q ⊆ Metric.ball i (r i)) :
      q * p ∈ S := by
    have hqp (k : ℕ) (hk : k < (meromorphicOrderAt (continuedCompletedHeckeL χ) (shift(a, i))).untop₀.toNat) :
        iteratedDeriv k (q * p) i = 0 := by
      rw [iteratedDeriv_mul (hq.of_le (by simp)).contDiffAt (hp.of_le (by simp)).contDiffAt]
      apply Finset.sum_eq_zero
      intro j _
      rw [hj i (k - j) ((Nat.sub_le _ _).trans_lt hk), mul_zero]
    obtain ⟨h, hh, heq⟩ := hpatch i (q * p) (hq.mul hp) (tsupport_mul_subset_left.trans hsub) hqp
    exact Submodule.subset_span ⟨f i, h, hh, heq⟩
  let B (i : ℝ) : ContDiffBump i := ⟨r i / 4, r i / 2, by have := hr i; positivity, by linarith [hr i]⟩
  let b (i t : ℝ) := ((B i t : ℝ) : ℂ)
  have hb (i : ℝ) : ContDiff ℝ (∞) (b i) := Complex.ofRealCLM.contDiff.comp (B i).contDiff
  have hbs (i : ℝ) : tsupport (b i) ⊆ Metric.ball i (r i) := by
    refine (tsupport_comp_subset Complex.ofReal_zero (B i)).trans ?_
    rw [(B i).tsupport_eq]
    exact Metric.closedBall_subset_ball (by change r i / 2 < r i; linarith [hr i])
  have hcov : tsupport p ⊆ ⋃ i : ℝ, Metric.ball i (r i / 4) :=
    fun x _ ↦ mem_iUnion.mpr ⟨x, Metric.mem_ball_self (by have := hr x; positivity)⟩
  obtain ⟨K, hK⟩ := hc.elim_finite_subcover (fun i : ℝ ↦ Metric.ball i (r i / 4))
    (fun _ ↦ Metric.isOpen_ball) hcov
  let Q (J : Finset ℝ) (t : ℝ) := ∏ i ∈ J, (1 - b i t)
  have hQins (J : Finset ℝ) (i : ℝ) (hi : i ∉ J) : Q (insert i J) = (1 - b i) * Q J := by
    funext t
    simp [Q, hi]
  have hQempty : Q ∅ = 1 := by funext t; simp [Q]
  have hQ (J : Finset ℝ) : ContDiff ℝ (∞) (Q J) := by
    induction J using Finset.induction_on with
    | empty => rw [hQempty]; exact contDiff_const
    | @insert i J hi ih => rw [hQins J i hi]; exact (contDiff_const.sub (hb i)).mul ih
  have hpart (J : Finset ℝ) : p - Q J * p ∈ S := by
    induction J using Finset.induction_on with
    | empty => simp [hQempty]
    | @insert i J hi ih =>
      rw [hQins J i hi, show p - ((1 - b i) * Q J) * p =
        (p - Q J * p) + (b i * Q J) * p by ring]
      exact S.add_mem ih (hlocal i (b i * Q J) ((hb i).mul (hQ J)) (tsupport_mul_subset_left.trans (hbs i)))
  have hzero : Q K * p = 0 := by
    funext t
    by_cases ht : p t = 0
    · simp [ht]
    · obtain ⟨i, hi, ht'⟩ := mem_iUnion₂.mp (hK (subset_tsupport _ (mem_support.mpr ht)))
      have hb1 : b i t = 1 := by
        have ht'' : t ∈ Metric.closedBall i (B i).rIn := Metric.ball_subset_closedBall ht'
        simp [b, (B i).one_of_mem_closedBall ht'']
      have hQt : Q K t = 0 := Finset.prod_eq_zero hi (by rw [hb1, sub_self])
      simp [hQt]
  change p ∈ S
  simpa only [hzero, sub_zero] using hpart K

/-- Every compact Schwartz profile with full Hecke zero multiplicities in its
Taylor jet gives a genuine element of the closed global weighted theta image. -/
private theorem lineProfile_hecke_compactIdeal (χ : PontryaginDual C𝔽) (a s : ℝ) (hs : 0 ≤ s)
    (P : 𝓢(ℝ, ℂ) →L[ℂ] SchwartzBruhat C𝔽) (γ : ℝ → PontryaginDual C𝔽)
    (hγ : ∀ t x, γ t x = (χ x)⁻¹ * Circle.exp (-t * logNorm x))
    (hF : ∀ p t, lcaFourier μ𝔽 (P p) (γ t) = p t)
    (hoff : ∀ p ψ, ψ ∉ range γ → lcaFourier μ𝔽 (P p) ψ = 0)
    (e : 𝓢(ℝ, ℂ) →ₗ[ℂ] Wχ(χ, s, hs)) (hrep : ∀ p, ((e p).val : C𝔽 → ℂ) =ᵐ[μ𝔽] (P p : C𝔽 → ℂ))
    (p : 𝓢(ℝ, ℂ)) (hc : HasCompactSupport (p : ℝ → ℂ))
    (hj : ∀ (t : ℝ) (k : ℕ), k < (meromorphicOrderAt (continuedCompletedHeckeL χ) (shift(a,t))).untop₀.toNat →
      iteratedDeriv k p t = 0) :
    (e p).val ∈ globalThetaSobolev F a (le_rfl : (0:ℝ) ≤ 0) hs := by
  let Z (f : adelePolarSubspace F) (t : ℝ) := globalThetaMellinIntegral f.val (ideleClassNormTwist χ (shift(a,t)))
  have hd (f : adelePolarSubspace F) : ContDiff ℝ (⊤ : ℕ∞) (Z f) := by
    obtain ⟨hf,hf'⟩ := (mem_adelePolarSubspace f.val).mp f.property
    have hE := globalThetaMellinIntegral_entire_of_vanishing f.val hf hf' χ
    exact (hE.contDiff.restrict_scalars ℝ).comp (contDiff_const.add (Complex.ofRealCLM.contDiff.mul contDiff_const))
  exact lineProfile_theta_compact_ideal ((Wχ(χ, s, hs)).subtype.comp e) _ Z hd
    (lineProfile_theta_generator χ a s hs P γ hγ hF hoff e hrep) p (lineProfile_theta_compact_span χ a p (p.smooth _) hc hj)

/-- Positive Hecke jet orders on a vertical frequency chart are locally finite. -/
private theorem continuedCompletedHeckeL_finite_vertical_zeros_on_compact (χ : PontryaginDual C𝔽) (a : ℝ) (K : Set ℝ) (hK : IsCompact K) :
    {t ∈ K | 0 < (meromorphicOrderAt (continuedCompletedHeckeL χ) (shift(a, t))).untop₀.toNat}.Finite := by
  let A (t : ℝ) := shift(a, t)
  let L := continuedCompletedHeckeL χ
  have hA : Continuous A := continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hi : Injective A := fun x y h ↦ by simpa [A, Complex.add_im, Complex.mul_im] using congrArg Complex.im h
  have hL : MeromorphicOn L (A '' K) := fun z _ ↦ (continuedCompletedHeckeL_spec χ).1.meromorphicOn z (mem_univ z)
  have hf := (MeromorphicOn.divisor L (A '' K)).finiteSupport (hK.image hA)
  apply (hf.preimage hi.injOn).subset
  rintro t ⟨ht, hpos⟩
  change MeromorphicOn.divisor L (A '' K) (A t) ≠ 0
  rw [hL.divisor_apply ⟨t, ht, rfl⟩]
  change 0 < (meromorphicOrderAt L (A t)).untop₀.toNat at hpos
  exact fun heq ↦ by rw [heq] at hpos; simp at hpos

/-- The frequency derivative of a Fourier integral is a log moment. Only
polynomial moments up to the requested order enter this real-variable formula. -/
private theorem iteratedDeriv_oscillatory_integral {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (L : X → ℝ) (hL : Measurable L) (f : X → ℂ) (k : ℕ)
    (hi : ∀ j ≤ k, Integrable (fun x ↦ f x * (L x : ℂ) ^ j) μ) (t : ℝ) :
    iteratedDeriv k (fun u : ℝ ↦ ∫ x, f x * Complex.exp (((u * L x : ℝ) : ℂ) * Complex.I) ∂μ) t =
      Complex.I ^ k * ∫ x, f x * (L x : ℂ) ^ k * Complex.exp (((t * L x : ℝ) : ℂ) * Complex.I) ∂μ := by
  let A (j : ℕ) (u : ℝ) (x : X) :=
    (f x * (L x : ℂ) ^ j) * Complex.I ^ j * Complex.exp (((u * L x : ℝ) : ℂ) * Complex.I)
  have hnorm (j u x) : ‖A j u x‖ = ‖f x * (L x : ℂ) ^ j‖ := by
    simp only [A, norm_mul, norm_pow, Complex.norm_I, one_pow, mul_one,
      Complex.norm_exp_ofReal_mul_I]
  have hmeas (j) (hj : j ≤ k) (u : ℝ) : AEStronglyMeasurable (A j u) μ := by
    refine ((hi j hj).aestronglyMeasurable.mul_const _).mul ?_
    exact (Complex.continuous_exp.measurable.comp
      ((Complex.continuous_ofReal.measurable.comp (hL.const_mul u)).mul_const _)).aestronglyMeasurable
  have hint (j) (hj : j ≤ k) (u : ℝ) : Integrable (A j u) μ :=
    (hi j hj).norm.mono' (hmeas j hj u) (.of_forall fun x ↦ (hnorm j u x).le)
  have hder (j) (hj : j+1 ≤ k) (u : ℝ) :
      HasDerivAt (fun v ↦ ∫ x, A j v x ∂μ) (∫ x, A (j+1) u x ∂μ) u := by
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := univ) univ_mem
      (.of_forall (hmeas j (by omega))) (hint j (by omega) u) (hmeas _ hj u)
      (.of_forall fun x v _ ↦ (hnorm (j+1) v x).le) (hi _ hj).norm ?_).2
    refine .of_forall fun x v _ ↦ ?_
    have hd := (((hasDerivAt_id v).mul_const (L x)).ofReal_comp.mul_const Complex.I).cexp
    convert hd.const_mul ((f x * (L x : ℂ)^j) * Complex.I^j) using 1
    · simp [A]
    · simp [A, pow_succ]
      ring
  have hall (j) (hj : j ≤ k) :
      iteratedDeriv j (fun u : ℝ ↦ ∫ x, f x * Complex.exp (((u * L x : ℝ) : ℂ) * Complex.I) ∂μ) =
        fun u ↦ ∫ x, A j u x ∂μ := by
    induction j with
    | zero => simp [A]
    | succ j ih =>
      rw [iteratedDeriv_succ, ih (by omega)]
      exact funext fun u ↦ (hder j hj u).deriv
  rw [hall k le_rfl, ← integral_const_mul]
  exact integral_congr_ae (.of_forall fun x ↦ by dsimp [A]; ring)

local notation "Hscalar(" s ")" => CompactIntervalSobolev volume id 0 0 s
local notation "nuF" => canonicalModulatedHaar m𝔽 hm𝔽
local notation "rad(" χ ", " u ")" => (fun x : C𝔽 ↦ ((χ⁻¹ x : Circle) : ℂ) * u (logNorm x))

local instance lineProfile_canonicalHaar : (nuF : Measure C𝔽).IsHaarMeasure :=
  (existsUnique_canonicalModulatedHaar m𝔽 hm𝔽).exists.choose_spec.1

private theorem lineProfile_radial_homogeneous (χ : PontryaginDual C𝔽) (u : ℝ → ℂ)
    (k : C₁) (x : C𝔽) : rad(χ, u) (k.val⁻¹*x) = (χ k.val : ℂ) * rad(χ, u) x := by
  have hm : m𝔽 (k.val⁻¹*x) = m𝔽 x := by
    rw [map_mul, map_inv, show m𝔽 k.val = 1 from k.property, inv_one, one_mul]
  change (((χ (k.val⁻¹*x))⁻¹ : Circle) : ℂ) * u (Real.log ((m𝔽 (k.val⁻¹*x)).val : ℝ)) =
    (χ k.val : ℂ) * ((((χ x)⁻¹ : Circle) : ℂ) * u (logNorm x))
  rw [hm, map_mul, map_inv, mul_inv_rev, inv_inv, Circle.coe_mul]
  ring_nf
  rfl

/-- Pullback by the log norm times the inverse character defines a bounded
map of the scalar singleton Sobolev space into the Tamagawa-weighted isotype. -/
private theorem lineProfile_weighted_radial (χ : PontryaginDual C𝔽) (s : ℝ) (hs : 0 ≤ s) :
    ∃ L : Hscalar(s) →L[ℂ] Wχ(χ, s, hs), ∀ u,
      ((L u).val : C𝔽 → ℂ) =ᵐ[μ𝔽] rad(χ, (u : ℝ → ℂ)) := by
  let ν := nuF
  let : ν.IsHaarMeasure := (existsUnique_canonicalModulatedHaar m𝔽 hm𝔽).exists.choose_spec.1
  let E := globalThetaAmbient_equiv_canonical (F := F) hm𝔽 0 0 s
  let B := E.choose
  let R := exists_modulatedIntervalSobolev_characterLogPullback m𝔽 hm𝔽 hms𝔽 χ⁻¹ 0 0 s
  let T : Hscalar(s) →L[ℂ] WI(s) := B.symm.toContinuousLinearMap.comp R.choose
  have ht (u : Hscalar(s)) : (T u : C𝔽 → ℂ) =ᵐ[μ𝔽] rad(χ, (u : ℝ → ℂ)) := by
    have hE := (E.choose_spec (T u)).1.symm
    have hB : B (T u) = R.choose u := B.apply_symm_apply _
    have hb : (B (T u) : C𝔽 → ℂ) =ᵐ[μ𝔽] (R.choose u : C𝔽 → ℂ) :=
      .of_forall fun g ↦ congrArg (fun v : ModulatedIntervalSobolev m𝔽 hm𝔽 0 0 s ↦ v g) hB
    exact hE.trans (hb.trans
      ((Measure.absolutelyContinuous_isHaarMeasure μ𝔽 ν).ae_eq (R.choose_spec.1 u)))
  have hac : μ𝔽 ≪ (μ𝔽).withDensity (fun x ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (logNorm x))) :=
    withDensity_absolutelyContinuous' (((continuous_intervalSobolevDensity' 0 0 s).measurable.comp
      (NNReal.continuous_coe.comp (Units.continuous_val.comp (m𝔽).continuous)).measurable.log).ennreal_ofReal.aemeasurable)
      (.of_forall fun x ↦ (ENNReal.ofReal_pos.mpr (intervalSobolevDensity_pos 0 0 s _)).ne')
  have hmem (u : Hscalar(s)) : T u ∈ Wχ(χ, s, hs) := by
    apply (mem_actionIsotype _ _ _).mpr
    intro k
    apply Lp.ext
    apply (withDensity_absolutelyContinuous μ𝔽 _).ae_eq
    have htr := (measurePreserving_mul_left μ𝔽 k.val⁻¹).quasiMeasurePreserving.ae_eq_comp (ht u)
    have hsm := hac.ae_eq (Lp.coeFn_smul (χ k.val : ℂ) (T u))
    filter_upwards [hardySobolevTranslation_apply μ𝔽 m𝔽 0 0 s le_rfl hs k.val (T u), htr, hsm, ht u] with x h₁ h₂ h₃ h₄
    exact h₁.trans (h₂.trans ((lineProfile_radial_homogeneous χ u k x).trans ((congrArg ((χ k.val : ℂ) * ·) h₄.symm).trans h₃.symm)))
  exact ⟨T.codRestrict _ hmem,ht⟩

private theorem lineProfile_scalar_has_schwartz (χ : PontryaginDual C𝔽) (f : PositiveRealExponentialDecay univ) :
    ∃ ψ : SchwartzBruhat C𝔽, ∀ x, ψ x = rad(χ, f.val) x := by
  exact (exists_modulatedIntervalSobolev_characterLogPullback m𝔽 hm𝔽 hms𝔽 χ⁻¹ 0 0 0).choose_spec.2 f

/-- Canonical logarithmic Haar coordinates give the Fourier transform of
a character-twisted scalar profile with the exact Tamagawa normalization. -/
private theorem lineProfile_scalar_fourier (χ : PontryaginDual C𝔽) (γ : ℝ → PontryaginDual C𝔽)
    (hγ : ∀ t x, γ t x = (χ x)⁻¹ * Circle.exp (-t * logNorm x))
    (f : PositiveRealExponentialDecay univ) (t : ℝ) :
    lcaFourier μ𝔽 rad(χ, f.val) (γ t) =
      ((Measure.haarScalarFactor μ𝔽 nuF : ℝ) : ℂ) *
        mellin (fun x ↦ f.val (Real.log x)) ((t : ℂ) * Complex.I) := by
  let ν := nuF
  let : ν.IsHaarMeasure := (existsUnique_canonicalModulatedHaar m𝔽 hm𝔽).exists.choose_spec.1
  have hfun (x : C𝔽) : rad(χ, f.val) x * star (γ t x : ℂ) =
      f.val (logNorm x) * Complex.exp (((t:ℂ)*Complex.I) * (logNorm x : ℂ)) := by
    have hψ : γ t x = (χ x * Circle.exp (t * logNorm x))⁻¹ := by rw [hγ,neg_mul,Circle.exp_neg,mul_inv]
    have hph : star (γ t x : ℂ) = (χ x : ℂ) * Complex.exp (((t * logNorm x : ℝ) : ℂ)*Complex.I) := by
      rw [hψ,Circle.coe_inv_eq_conj, ← Complex.star_def,star_star,Circle.coe_mul,Circle.coe_exp]
    change (((χ x)⁻¹ : Circle) : ℂ) * f.val (logNorm x) * star (γ t x : ℂ) = _
    rw [hph,Circle.coe_inv,Complex.ofReal_mul,show (t:ℂ)*(logNorm x : ℂ)*Complex.I = (t:ℂ)*Complex.I*(logNorm x : ℂ) by ring]
    field_simp [Circle.coe_ne_zero]
  have hprofile := (integral_congr_ae (.of_forall hfun) : lcaFourier μ𝔽 rad(χ, f.val) (γ t) = _)
  refine hprofile.trans ?_
  rw [mellin_logProfile]
  conv_lhs => rw [Measure.isMulLeftInvariant_eq_smul μ𝔽 ν,integral_smul_nnreal_measure]
  rw [NNReal.smul_def, Complex.real_smul]
  congr 1
  have hl := sobolev_log_preserving m𝔽 hm𝔽 hms𝔽
  have hc : Continuous f.val := by
    refine (logExponentialDecayTwist univ ⟨0,mem_univ _⟩ f).continuous.congr ?_
    intro x
    simpa using logExponentialDecayTwist_apply univ ⟨0,mem_univ _⟩ f x
  let q (x : ℝ) := f.val x * Complex.exp (((t:ℂ)*Complex.I)*(x:ℂ))
  have hq : Continuous q := hc.mul (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
  exact (integral_map hl.measurable.aemeasurable (f := q) hq.aestronglyMeasurable).symm.trans
    (congrArg (fun η : Measure ℝ ↦ ∫ x, q x ∂η) hl.map_eq)

/-- Restriction of an entire Mellin transform to the imaginary axis multiplies
its kth complex derivative by the kth power of the frequency phase. -/
private theorem lineProfile_vertical_scalar_derivative (f : PositiveRealExponentialDecay univ) (k : ℕ) (t : ℝ) :
    iteratedDeriv k (fun v : ℝ ↦ mellin (fun x ↦ f.val (Real.log x)) ((v : ℂ)*Complex.I)) t =
      Complex.I^k * iteratedDeriv k (mellin (fun x ↦ f.val (Real.log x))) ((t : ℂ)*Complex.I) := by
  let Z := positiveRealFourierMellin univ isOpen_univ ordConnected_univ univ_nonempty f
  have hZ : Z.val = mellin (fun x ↦ f.val (Real.log x)) :=
    funext fun w ↦ positiveRealFourierMellin_apply univ isOpen_univ ordConnected_univ univ_nonempty f w (mem_univ _)
  have hd : Differentiable ℂ Z.val := by simpa only [preimage_univ,differentiableOn_univ] using Z.property.2.1
  have hall (n : ℕ) : iteratedDeriv n (fun v : ℝ ↦ Z.val ((v : ℂ)*Complex.I)) =
      fun v : ℝ ↦ Complex.I^n * iteratedDeriv n Z.val ((v:ℂ)*Complex.I) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [iteratedDeriv_succ,ih]
      funext v
      have hD := (hd.contDiff.differentiable_iteratedDeriv' n ((v : ℂ)*Complex.I)).hasDerivAt
      have hC := (hD.comp (v : ℂ) ((hasDerivAt_id (v : ℂ)).mul_const Complex.I)).comp_ofReal
      have hh := (hC.const_mul (Complex.I^n)).deriv
      change deriv (fun x : ℝ ↦ Complex.I^n * iteratedDeriv n Z.val ((x:ℂ)*Complex.I)) v = _
      refine hh.trans ?_
      rw [iteratedDeriv_succ,pow_succ]
      simp only [one_mul]
      ring
  rw [← hZ]
  exact congrFun (hall k) t

private theorem lineProfile_scalar_chart_test (χ : PontryaginDual C𝔽)
    (P : 𝓢(ℝ, ℂ) →L[ℂ] SchwartzBruhat C𝔽) (γ : ℝ → PontryaginDual C𝔽)
    (hγ : ∀ t x, γ t x = (χ x)⁻¹ * Circle.exp (-t * logNorm x))
    (hF : ∀ p t, lcaFourier μ𝔽 (P p) (γ t) = p t)
    (honto : ∀ v : SchwartzBruhat C𝔽, (∀ (k : C₁) (x : C𝔽), v (k.val⁻¹*x) = (χ k.val : ℂ) * v x) → ∃ p, P p = v)
    (f : PositiveRealExponentialDecay univ) :
    ∃ p : 𝓢(ℝ, ℂ), (∀ x, P p x = rad(χ, f.val) x) ∧ ∀ t, p t = ((Measure.haarScalarFactor μ𝔽 nuF : ℝ) : ℂ) *
        mellin (fun x ↦ f.val (Real.log x)) ((t : ℂ) * Complex.I) := by
  obtain ⟨v,hv⟩ := lineProfile_scalar_has_schwartz (F := F) χ f
  have huv (k : C₁) (x : C𝔽) : v (k.val⁻¹*x) = (χ k.val : ℂ) * v x :=
    (hv _).trans ((lineProfile_radial_homogeneous χ f.val k x).trans (congrArg ((χ k.val : ℂ) * ·) (hv x).symm))
  obtain ⟨p,hp⟩ := honto v huv
  have heq (x : C𝔽) : P p x = rad(χ, f.val) x := (congrArg (fun u : SchwartzBruhat C𝔽 ↦ u x) hp).trans (hv x)
  refine ⟨p, heq, fun t ↦ (hF p t).symm.trans ?_⟩
  exact (congrArg (fun v : C𝔽 → ℂ ↦ lcaFourier μ𝔽 v (γ t)) (funext heq)).trans (lineProfile_scalar_fourier χ γ hγ f t)

private theorem lineProfile_scalar_test_in_chart (χ : PontryaginDual C𝔽) (s : ℝ) (hs : 0 ≤ s)
    (L : Hscalar(s) →L[ℂ] Wχ(χ, s, hs)) (hL : ∀ u, ((L u).val : C𝔽 → ℂ) =ᵐ[μ𝔽] rad(χ, (u : ℝ → ℂ)))
    (P : 𝓢(ℝ, ℂ) →L[ℂ] SchwartzBruhat C𝔽)
    (e : 𝓢(ℝ, ℂ) →ₗ[ℂ] Wχ(χ, s, hs)) (hrep : ∀ p, ((e p).val : C𝔽 → ℂ) =ᵐ[μ𝔽] (P p : C𝔽 → ℂ))
    (f : PositiveRealExponentialDecay univ) (u : Hscalar(s)) (hu : (u : ℝ → ℂ) =ᵐ[volume] f.val)
    (p : 𝓢(ℝ, ℂ)) (hp : ∀ x, P p x = rad(χ, f.val) x) :
    L u = e p := by
  have h := (Measure.absolutelyContinuous_isHaarMeasure μ𝔽 nuF).ae_eq
    ((sobolev_log_preserving m𝔽 hm𝔽 hms𝔽).quasiMeasurePreserving.ae_eq_comp hu)
  apply Subtype.ext
  apply Lp.ext
  apply (withDensity_absolutelyContinuous μ𝔽 _).ae_eq
  filter_upwards [hL u, h, hrep p] with x hx hx' hx''
  exact hx.trans ((congrArg (fun z : ℂ ↦ (χ⁻¹ x : ℂ)*z) hx').trans ((hp x).symm.trans hx''.symm))

private theorem lineProfile_scalar_endpoint_criterion (s : ℝ) (hs : 0 ≤ s) (c : ℂ) (hc : c ≠ 0)
    (t : ℝ) (k : ℕ) (Λ : Hscalar(s) →L[ℂ] ℂ)
    (h : ∀ (f : PositiveRealExponentialDecay univ) (u : Hscalar(s)), (u : ℝ → ℂ) =ᵐ[volume] f.val →
      Λ u = (c*Complex.I^k) * iteratedDeriv k (mellin (fun x ↦ f.val (Real.log x))) ((t : ℂ)*Complex.I)) :
    2 * (k : ℝ) + 1 < s := by
  apply (scalarIntervalSobolev_eval_boundary_iff 0 0 s le_rfl hs k ((t : ℂ)*Complex.I) (by simp)).mp
  refine ⟨(c*Complex.I^k)⁻¹ • Λ,fun f u hu ↦ ?_⟩
  change (c * Complex.I^k)⁻¹ * Λ u = _
  rw [h f u hu, inv_mul_cancel_left₀ (mul_ne_zero hc (pow_ne_zero k Complex.I_ne_zero))]

private theorem lineProfile_scalar_test_derivative (c : ℂ) (t : ℝ) (k : ℕ) (p : 𝓢(ℝ, ℂ)) (f : PositiveRealExponentialDecay univ)
    (hp : ∀ v, p v = c*mellin (fun x ↦ f.val (Real.log x)) ((v : ℂ) * Complex.I)) :
    iteratedDeriv k p t = (c*Complex.I^k)*iteratedDeriv k (mellin (fun x ↦ f.val (Real.log x))) ((t : ℂ)*Complex.I) := by
  have hpf : (p : ℝ → ℂ) = fun v : ℝ ↦ c * mellin (fun x ↦ f.val (Real.log x)) ((v : ℂ)*Complex.I) := funext hp
  rw [hpf,iteratedDeriv_const_mul_field,lineProfile_vertical_scalar_derivative,mul_assoc]

/-- An individual chart derivative extends to this isotype only in the exact
strict range prescribed by the scalar endpoint Sobolev theorem. -/
private theorem lineProfile_jet_endpoint_necessary (χ : PontryaginDual C𝔽) (s : ℝ) (hs : 0 ≤ s)
    (P : 𝓢(ℝ, ℂ) →L[ℂ] SchwartzBruhat C𝔽) (γ : ℝ → PontryaginDual C𝔽)
    (hγ : ∀ t x, γ t x = (χ x)⁻¹ * Circle.exp (-t * logNorm x))
    (hF : ∀ p t, lcaFourier μ𝔽 (P p) (γ t) = p t)
    (honto : ∀ v : SchwartzBruhat C𝔽, (∀ (k : C₁) (x : C𝔽), v (k.val⁻¹*x) = (χ k.val : ℂ) * v x) → ∃ p, P p = v)
    (e : 𝓢(ℝ, ℂ) →ₗ[ℂ] Wχ(χ, s, hs)) (hrep : ∀ p, ((e p).val : C𝔽 → ℂ) =ᵐ[μ𝔽] (P p : C𝔽 → ℂ))
    (t : ℝ) (k : ℕ) (Λ : StrongDual ℂ Wχ(χ, s, hs)) (hΛ : ∀ p, Λ (e p) = iteratedDeriv k p t) :
    2 * (k : ℝ) + 1 < s := by
  let H := lineProfile_weighted_radial (F := F) χ s hs
  let B := H.choose
  let c : ℂ := ((Measure.haarScalarFactor μ𝔽 nuF : ℝ) : ℂ)
  have hpos : 0 < (Measure.haarScalarFactor μ𝔽 nuF : ℝ) := by exact_mod_cast Measure.haarScalarFactor_pos_of_isHaarMeasure μ𝔽 nuF
  have hc : c ≠ 0 := Complex.ofReal_ne_zero.mpr hpos.ne'
  apply lineProfile_scalar_endpoint_criterion s hs c hc t k (Λ.comp B)
  intro f u hu
  let Htest := lineProfile_scalar_chart_test χ P γ hγ hF honto f
  let p := Htest.choose
  have heq := lineProfile_scalar_test_in_chart χ s hs B H.choose_spec P e hrep f u hu p Htest.choose_spec.1
  exact (congrArg Λ heq).trans ((hΛ p).trans (lineProfile_scalar_test_derivative c t k p f Htest.choose_spec.2))

private theorem lineJet_as_phase (η : PontryaginDual C𝔽) (t : ℝ) (n : ℕ) (g : C𝔽) :
    spectralZeroJet η 0 t n g =
      ((η g : ℂ) * Complex.exp (((t * logNorm g : ℝ) : ℂ) * Complex.I)) * (logNorm g : ℂ)^n := by
  have hp : (0 : ℝ) < ((ideleClassNorm F g).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
  change ((η g : ℂ) * (((ideleClassNorm F g).val : ℝ) : ℂ) ^ ((0 : ℂ) + (t : ℂ) * Complex.I)) * _ = _
  rw [zero_add, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne'),
    ← Complex.ofReal_log hp.le, Complex.ofReal_mul]
  ring_nf

/-- The real-frequency Fourier profile of a Sobolev vector differentiates at every
surviving order. With the conjugation used by the Fourier transform, its chart
runs through the inverses of the Mellin characters. -/
private theorem spectralLineJet_fourier_profile_derivative
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) {a s : ℝ} (hs : 1 < s)
    (j : SpectralLineJetIndex χ a s) (f : WI(s)) (Ψ : ℝ → PontryaginDual C𝔽)
    (hΨ : ∀ u g, star ((Ψ u) g : ℂ) = (χ j.val.1 g : ℂ) *
      Complex.exp (((u * logNorm g : ℝ) : ℂ) * Complex.I)) :
    iteratedDeriv j.val.2.2 (fun u ↦ lcaFourier μ𝔽 f (Ψ u)) j.val.2.1 =
      Complex.I ^ j.val.2.2 * spectralSobolevPairing f ((spectralLineJet_memLp χ hs j).toLp
        (spectralZeroJet (χ j.val.1) 0 j.val.2.1 j.val.2.2)) := by
  have hL : Measurable logNorm := (NNReal.continuous_coe.comp (Units.continuous_val.comp
    (isProperMap_ideleClassNorm F).continuous)).measurable.log
  have hi (n) (hn : n ≤ j.val.2.2) :
      Integrable (fun x ↦ (f x * (χ j.val.1 x : ℂ)) * (logNorm x : ℂ)^n) μ𝔽 := by
    let i : SpectralLineJetIndex χ a s := ⟨(j.val.1, j.val.2.1, n), hn.trans_lt j.property⟩
    have h := ((spectralLineJet_functional χ hs i).choose_spec.1 f).1
    refine h.norm.mono' ((((Lp.stronglyMeasurable f).measurable.mul
      (continuous_subtype_val.comp (χ j.val.1).continuous).measurable).mul
      ((Complex.measurable_ofReal.comp hL).pow_const n)).aestronglyMeasurable) (.of_forall fun x ↦ ?_)
    change _ ≤ ‖f x * spectralZeroJet (χ j.val.1) 0 j.val.2.1 n x‖
    rw [lineJet_as_phase]
    simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, mul_assoc, le_refl]
  have hp := iteratedDeriv_oscillatory_integral μ𝔽 logNorm hL _ _ hi j.val.2.1
  have hF (u : ℝ) : lcaFourier μ𝔽 f (Ψ u) = ∫ x, (f x * (χ j.val.1 x : ℂ)) *
      Complex.exp (((u * logNorm x : ℝ) : ℂ) * Complex.I) ∂μ𝔽 :=
    integral_congr_ae (.of_forall fun x ↦ (congrArg (f x * ·) (hΨ u x)).trans (mul_assoc _ _ _).symm)
  rw [show (fun u ↦ lcaFourier μ𝔽 f (Ψ u)) = _ from funext hF, hp]
  congr 1
  let z := spectralZeroJet (χ j.val.1) 0 j.val.2.1 j.val.2.2
  let v := (spectralLineJet_memLp χ hs j).toLp z
  have hac : μ𝔽 ≪ (μ𝔽).withDensity (fun x ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (logNorm x))⁻¹) :=
    withDensity_absolutelyContinuous'
      (((continuous_intervalSobolevDensity' 0 0 s).measurable.comp hL).inv.ennreal_ofReal.aemeasurable)
      (.of_forall fun x ↦ ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr (intervalSobolevDensity_pos 0 0 s _)))
  have hv : (v : C𝔽 → ℂ) =ᵐ[μ𝔽] z := hac.ae_eq (MemLp.coeFn_toLp _)
  apply integral_congr_ae
  filter_upwards [hv] with x hx
  change _ = f x * v x
  rw [hx, show z x = _ from lineJet_as_phase _ _ _ x]
  ring

private theorem lineJet_chart_star {ψ χ : PontryaginDual C𝔽} {t : ℝ}
    (hp : ∀ g, ψ g = (χ g)⁻¹ * Circle.exp (-t * logNorm g)) (x : C𝔽) :
    star (ψ x : ℂ) = (χ x : ℂ) * Complex.exp (((t * logNorm x : ℝ) : ℂ) * Complex.I) := by
  have h : ψ x = (χ x * Circle.exp (t * logNorm x))⁻¹ := by
    rw [hp, neg_mul, Circle.exp_neg, mul_inv]
  calc
    star (ψ x : ℂ) = star (((χ x * Circle.exp (t * logNorm x))⁻¹ : Circle) : ℂ) :=
      congrArg (fun c : Circle ↦ star (c : ℂ)) h
    _ = _ := by rw [Circle.coe_inv_eq_conj, ← Complex.star_def, star_star, Circle.coe_mul, Circle.coe_exp]

local notation "hs0(" hs ")" => (zero_le_one.trans (hs).le : (0:ℝ) ≤ _)
local notation "zeroVec(" χ ", " hs ", " j ")" =>
  (spectralLineJet_memLp χ hs j).toLp (spectralZeroJet (χ (j).val.1) 0 (j).val.2.1 (j).val.2.2)

/-- A bounded extension of an admitted evaluation on one isotype agrees by
density with the ambient Sobolev pairing, up to the Fourier derivative phase. -/
private theorem lineProfile_admitted_functional
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (ξ : PontryaginDual C₁) {a s : ℝ} (hs : 1 < s)
    (P : 𝓢(ℝ, ℂ) →L[ℂ] SchwartzBruhat C𝔽) (γ : ℝ → PontryaginDual C𝔽)
    (hγ : ∀ t x, γ t x = (χ ξ x)⁻¹ * Circle.exp (-t * logNorm x))
    (hF : ∀ p t, lcaFourier μ𝔽 (P p) (γ t) = p t)
    (e : 𝓢(ℝ, ℂ) →ₗ[ℂ] Wχ(χ ξ, s, hs0(hs))) (he : DenseRange e)
    (hrep : ∀ p, ((e p).val : C𝔽 → ℂ) =ᵐ[μ𝔽] (P p : C𝔽 → ℂ))
    (j : SpectralLineJetIndex χ a s) (hj : j.val.1 = ξ)
    (Λ : StrongDual ℂ Wχ(χ ξ, s, hs0(hs)))
    (hΛ : ∀ p, Λ (e p) = iteratedDeriv j.val.2.2 p j.val.2.1)
    (y : Wχ(χ ξ, s, hs0(hs))) :
    Λ y = Complex.I^j.val.2.2 * spectralSobolevPairing y.val zeroVec(χ, hs, j) := by
  let v := zeroVec(χ, hs, j)
  let T := (modulatedIntervalSobolev_dual m𝔽 hm𝔽 μ𝔽 0 0 s le_rfl hs0(hs)).exists.choose
  let Φ := T.symm v
  have hpair (x : WI(s)) : Φ x = spectralSobolevPairing x v :=
    (spectralSobolevPairing_dual (le_rfl : (0:ℝ) ≤ 0) hs0(hs) Φ x).2.trans
      (congrArg (spectralSobolevPairing x) (T.apply_symm_apply v))
  have hphase (t : ℝ) (x : C𝔽) : star (γ t x : ℂ) = (χ j.val.1 x : ℂ) *
    Complex.exp (((t*logNorm x : ℝ) : ℂ)*Complex.I) := by
    rw [hj]
    exact lineJet_chart_star (hγ t) x
  let R (z : Wχ(χ ξ, s, hs0(hs))) := Complex.I^j.val.2.2 * Φ z.val
  have hR (p : 𝓢(ℝ, ℂ)) : Λ (e p) = R (e p) := by
    have hhat : (fun t : ℝ ↦ lcaFourier μ𝔽 (e p).val (γ t)) = p := funext fun t ↦
      (integral_congr_ae ((hrep p).mul EventuallyEq.rfl)).trans (hF p t)
    have hd := spectralLineJet_fourier_profile_derivative χ hs j (e p).val γ hphase
    exact (hΛ p).trans (((congrArg (fun q : ℝ → ℂ ↦ iteratedDeriv j.val.2.2 q j.val.2.1) hhat).symm.trans hd).trans
      (congrArg (Complex.I^j.val.2.2 * ·) (hpair (e p).val).symm))
  have hfin : (Λ : Wχ(χ ξ, s, hs0(hs)) → ℂ) = R := he.equalizer Λ.continuous
    (continuous_const.mul (Φ.continuous.comp continuous_subtype_val)) (funext hR)
  exact (congrFun hfin y).trans (congrArg (Complex.I^j.val.2.2 * ·) (hpair y.val))

private theorem lineProfile_all_bounded_jets_vanish
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (ξ : PontryaginDual C₁) {a s : ℝ} (hs : 1 < s)
    (P : 𝓢(ℝ, ℂ) →L[ℂ] SchwartzBruhat C𝔽) (γ : ℝ → PontryaginDual C𝔽)
    (hγ : ∀ t x, γ t x = (χ ξ x)⁻¹ * Circle.exp (-t * logNorm x))
    (hF : ∀ p t, lcaFourier μ𝔽 (P p) (γ t) = p t)
    (honto : ∀ v : SchwartzBruhat C𝔽, (∀ (k : C₁) (x : C𝔽), v (k.val⁻¹*x) = (χ ξ k.val : ℂ) * v x) → ∃ p, P p = v)
    (e : 𝓢(ℝ, ℂ) →ₗ[ℂ] Wχ(χ ξ, s, hs0(hs))) (he : DenseRange e)
    (hrep : ∀ p, ((e p).val : C𝔽 → ℂ) =ᵐ[μ𝔽] (P p : C𝔽 → ℂ))
    (y : Wχ(χ ξ, s, hs0(hs)))
    (hy : ∀ j : SpectralLineJetIndex χ a s, j.val.1 = ξ → spectralSobolevPairing y.val zeroVec(χ,hs,j) = 0)
    (t : ℝ) (k : ℕ) (hk : k < (meromorphicOrderAt (continuedCompletedHeckeL (χ ξ)) (shift(a,t))).untop₀.toNat)
    (Λ : StrongDual ℂ Wχ(χ ξ, s, hs0(hs))) (hΛ : ∀ p, Λ (e p) = iteratedDeriv k p t) :
    Λ y = 0 := by
  have hc := lineProfile_jet_endpoint_necessary (χ ξ) s hs0(hs) P γ hγ hF honto e hrep t k Λ hΛ
  let j : SpectralLineJetIndex χ a s := ⟨(ξ,t,k), (lt_spectralBoundaryMultiplicity s _ k).mpr ⟨hk,by linarith⟩⟩
  exact (lineProfile_admitted_functional χ ξ hs P γ hγ hF e he hrep j rfl Λ hΛ y).trans (by rw [hy j rfl,mul_zero])

/-- Reverse norm-closure inclusion inside a single compact-character isotype on
a zero-width spectral line. Each surviving jet of this isotype is tested. -/
private theorem lineProfile_isotype_synthesis_chart
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (ξ : PontryaginDual C₁) {a s : ℝ} (hs : 1 < s)
    (P : 𝓢(ℝ, ℂ) →L[ℂ] SchwartzBruhat C𝔽) (γ : ℝ → PontryaginDual C𝔽)
    (hγ : ∀ t x, γ t x = (χ ξ x)⁻¹ * Circle.exp (-t * logNorm x))
    (hF : ∀ p t, lcaFourier μ𝔽 (P p) (γ t) = p t)
    (hoff : ∀ p ψ, ψ ∉ range γ → lcaFourier μ𝔽 (P p) ψ = 0)
    (honto : ∀ v : SchwartzBruhat C𝔽, (∀ (k : C₁) (x : C𝔽), v (k.val⁻¹*x) = (χ ξ k.val : ℂ) * v x) → ∃ p, P p = v)
    (e : 𝓢(ℝ, ℂ) →ₗ[ℂ] Wχ(χ ξ, s, hs0(hs))) (hrep : ∀ p, ((e p).val : C𝔽 → ℂ) =ᵐ[μ𝔽] (P p : C𝔽 → ℂ))
    (y : Wχ(χ ξ, s, hs0(hs)))
    (hy : ∀ j : SpectralLineJetIndex χ a s, j.val.1 = ξ → spectralSobolevPairing y.val zeroVec(χ,hs,j) = 0) :
    y.val ∈ globalThetaSobolev F a (le_rfl : (0:ℝ) ≤ 0) hs0(hs) := by
  let m (t : ℝ) := (meromorphicOrderAt (continuedCompletedHeckeL (χ ξ)) (shift(a,t))).untop₀.toNat
  let N := (globalThetaSobolev F a (le_rfl : (0:ℝ) ≤ 0) hs0(hs)).comap (Wχ(χ ξ, s, hs0(hs))).subtype
  have hN : IsClosed (N : Set Wχ(χ ξ, s, hs0(hs))) := (Submodule.isClosed_topologicalClosure _).preimage continuous_subtype_val
  have he := lineProfile_denseEmbedding (χ ξ) s hs0(hs) P honto e hrep
  have hint := lineProfile_chart_intertwine (χ ξ) s hs0(hs) P γ hF hoff e hrep
  let U := lineProfile_chart_approximateUnit (χ ξ) s hs0(hs) P γ hγ hF honto e hint
  let g := U.choose
  let T := U.choose_spec.choose
  have hT := U.choose_spec.choose_spec
  exact schwartzMap_mem_closedSubmodule_of_vanishing_jets m N hN e he
    (fun h _ ↦ lineProfile_chart_multiplier (χ ξ) s hs0(hs) P e hint h)
    (continuedCompletedHeckeL_finite_vertical_zeros_on_compact (χ ξ) a) (lineProfile_hecke_compactIdeal (χ ξ) a s hs0(hs) P γ hγ hF hoff e hrep)
    g hT.1 T hT.2.1 hT.2.2 y (lineProfile_all_bounded_jets_vanish χ ξ hs P γ hγ hF honto e he hrep y hy)

private theorem lineProfile_isotype_synthesis
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (ξ : PontryaginDual C₁) {a s : ℝ} (hs : 1 < s)
    (y : Wχ(χ ξ, s, hs0(hs)))
    (hy : ∀ j : SpectralLineJetIndex χ a s, j.val.1 = ξ → spectralSobolevPairing y.val zeroVec(χ,hs,j) = 0) :
    y.val ∈ globalThetaSobolev F a (le_rfl : (0:ℝ) ≤ 0) hs0(hs) := by
  let H := exists_schwartzBruhat_mellinFrequencyChart m𝔽 hm𝔽 hms𝔽 μ𝔽 (χ ξ)
  let P := H.choose
  let γ := H.choose_spec.choose
  have h := H.choose_spec.choose_spec
  let E := lineProfile_sobolevLift (χ ξ) s hs0(hs) P h.2.2.2.1
  exact lineProfile_isotype_synthesis_chart χ ξ hs P γ h.1 h.2.1 h.2.2.1 h.2.2.2.2 E.choose E.choose_spec y hy

/-- The character-weighted average of a continuous orbit belongs to its isotype.
Testing this vector against a continuous functional gives the Fourier coefficient
of the scalar orbit. -/
private theorem spectralLineJet_characterAverage {G E : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (μ : Measure G) [μ.IsHaarMeasure] (ρ : G →* (E →L[ℂ] E))
    (hρ : Continuous (fun p : G × E ↦ ρ p.1 p.2)) (ξ : PontryaginDual G) (y : E) :
    ∃ v ∈ actionIsotype ρ ξ, ∀ φ : StrongDual ℂ E, φ v = ∫ g, star (ξ g : ℂ) * φ (ρ g y) ∂μ := by
  let A (g : G) := star (ξ g : ℂ) • ρ g y
  have hA : Continuous A := (show Continuous (fun g ↦ star (ξ g : ℂ)) by fun_prop).smul
    (hρ.comp (continuous_id.prodMk continuous_const))
  have hi := hA.integrable_of_hasCompactSupport (μ := μ) (HasCompactSupport.of_compactSpace A)
  let v := ∫ g, A g ∂μ
  have hφ (φ : StrongDual ℂ E) : φ v = ∫ g, star (ξ g : ℂ) * φ (ρ g y) ∂μ := by
    refine (φ.integral_comp_comm hi).symm.trans ?_
    exact integral_congr_ae (.of_forall fun g ↦ φ.map_smul _ _)
  refine ⟨v, (mem_actionIsotype ..).mpr fun k ↦ ?_, hφ⟩
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).mpr
  intro φ
  have h := hφ (φ.comp (ρ k))
  rw [map_smul, hφ φ, smul_eq_mul, ← integral_const_mul, ← integral_mul_left_eq_self (μ := μ)
    (fun g ↦ (ξ k : ℂ) * (star (ξ g : ℂ) * φ (ρ g y))) k]
  apply h.trans (integral_congr_ae (.of_forall fun g ↦ ?_))
  simp only [ContinuousLinearMap.comp_apply, map_mul, Circle.coe_mul, star_mul', mul_apply_eq_comp]
  rw [mul_assoc (star (ξ k : ℂ)), ← mul_assoc (ξ k : ℂ)]
  simp [← Circle.coe_inv_eq_conj]
/-- A closed subspace containing all character components of a vector contains
the vector itself. Testing its compact orbit against a separating functional
reduces to uniqueness of Fourier coefficients on the compact abelian group. -/
private theorem lineProfile_compact_components {G E J : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.WeaklyRegular] (ρ : G →* (E →L[ℂ] E))
    (hρ : Continuous (fun p : G × E ↦ ρ p.1 p.2)) (N : Submodule ℂ E) (hN : IsClosed (N : Set E))
    (Λ : J → StrongDual ℂ E) (y : E) (hy : ∀ g j, Λ j (ρ g y) = 0)
    (hiso : ∀ (ξ : PontryaginDual G) (x : E), x ∈ actionIsotype ρ ξ → (∀ j, Λ j x = 0) → x ∈ N) :
    y ∈ N := by
  by_contra hny
  obtain ⟨φ,hne,hzero⟩ := exists_dual_eq_zero_on_submodule_of_notMem N hN hny
  let u (g : G) := φ (ρ g y)
  have hu : Continuous u := φ.continuous.comp (hρ.comp (continuous_id.prodMk continuous_const))
  have hcoeff (ξ : PontryaginDual G) : ∫ g, star (ξ g : ℂ) * u g ∂μ = 0 := by
    obtain ⟨v, hv, hm⟩ := spectralLineJet_characterAverage μ ρ hρ ξ y
    rw [← hm φ]
    apply hzero _ (hiso ξ v hv ?_)
    intro j
    rw [hm (Λ j)]
    exact integral_eq_zero_of_ae (.of_forall fun g ↦ by simp [hy g j])
  have hae := ae_eq_zero_of_character_integral_eq_zero μ (hu.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) hcoeff
  have heq := Measure.eq_of_ae_eq hae hu continuous_const
  exact hne (by simpa [u] using congrFun heq 1)

private theorem lineProfile_raw_normOne (χ : PontryaginDual C𝔽) (t : ℝ) (n : ℕ) (g : C₁) (x : C𝔽) :
    spectralZeroJet χ 0 t n (g.val*x) = (χ g.val : ℂ) * spectralZeroJet χ 0 t n x := by
  have hm : ideleClassNorm F (g.val*x) = ideleClassNorm F x := by rw [map_mul,g.property,one_mul]
  have hl : logNorm (g.val*x) = logNorm x := congrArg (fun z : ℝ≥0ˣ ↦ Real.log (z.val : ℝ)) hm
  rw [lineJet_as_phase,lineJet_as_phase,hl,map_mul,Circle.coe_mul]
  ring

private theorem lineProfile_integral_eigen {G : Type*} [CommGroup G] [MeasurableSpace G] [MeasurableMul₂ G]
    (μ : Measure G) [μ.IsMulLeftInvariant] (r f : G → ℂ) (g : G) (c : ℂ)
    (hr : ∀ x, r (g*x) = c * r x) :
    (∫ x, f (g⁻¹*x) * r x ∂μ) = c * ∫ x, f x * r x ∂μ := by
  rw [← integral_const_mul]
  refine (integral_mul_left_eq_self (μ := μ) (fun x ↦ f (g⁻¹*x) * r x) g).symm.trans ?_
  apply integral_congr_ae
  refine .of_forall fun x ↦ ?_
  change f (g⁻¹*(g*x)) * r (g*x) = c*(f x*r x)
  rw [inv_mul_cancel_left,hr]
  ring

private theorem lineProfile_jet_normOne_dual
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) {a s : ℝ} (hs : 1 < s)
    (j : SpectralLineJetIndex χ a s) : ∃ Λ : StrongDual ℂ WI(s),
      (∀ u, Λ u = spectralSobolevPairing u zeroVec(χ,hs,j)) ∧
      (∀ (g : C₁) u, Λ (hardySobolevTranslation μ𝔽 m𝔽 0 0 s le_rfl hs0(hs) g.val u) =
        (χ j.val.1 g.val : ℂ) * Λ u) ∧
      ∀ u, Λ u = ∫ x, u x * spectralZeroJet (χ j.val.1) 0 j.val.2.1 j.val.2.2 x ∂μ𝔽 := by
  let r := spectralZeroJet (χ j.val.1) 0 j.val.2.1 j.val.2.2
  let v := zeroVec(χ,hs,j)
  let H := spectralLineJet_functional χ hs j
  let Λ := H.choose
  have hΛ (u : WI(s)) : Λ u = ∫ x, u x * r x ∂μ𝔽 := (H.choose_spec.1 u).2
  have hv : (v : C𝔽 → ℂ) =ᵐ[μ𝔽] r := by
    have hL : Measurable logNorm := (NNReal.continuous_coe.comp (Units.continuous_val.comp (m𝔽).continuous)).measurable.log
    have hac : μ𝔽 ≪ (μ𝔽).withDensity (fun x ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (logNorm x))⁻¹) :=
      withDensity_absolutelyContinuous' (((continuous_intervalSobolevDensity' 0 0 s).measurable.comp hL).inv.ennreal_ofReal.aemeasurable)
        (.of_forall fun x ↦ ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr (intervalSobolevDensity_pos 0 0 s _)))
    exact hac.ae_eq (MemLp.coeFn_toLp _)
  refine ⟨Λ,fun u ↦ (hΛ u).trans (integral_congr_ae (EventuallyEq.rfl.mul hv.symm)),(fun g u ↦ ?_), hΛ⟩
  rw [hΛ,hΛ]
  have htr := hardySobolevTranslation_apply μ𝔽 m𝔽 0 0 s le_rfl hs0(hs) g.val u
  exact (integral_congr_ae (htr.mul EventuallyEq.rfl)).trans (lineProfile_integral_eigen μ𝔽 r u g.val _
    (lineProfile_raw_normOne (χ j.val.1) j.val.2.1 j.val.2.2 g))

/-- The common zero-jet kernel lies in the global weighted theta closure once that
inclusion is known on each compact-character isotype. -/
private theorem lineProfile_reverse_of_isotypes (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice χ) {a s : ℝ} (hs : 1 < s)
    (hiso : ∀ (ξ : PontryaginDual C₁) (z : Wχ(χ ξ, s, hs0(hs))),
      (∀ j : SpectralLineJetIndex χ a s, j.val.1 = ξ → spectralSobolevPairing z.val zeroVec(χ,hs,j) = 0) →
      z.val ∈ globalThetaSobolev F a (le_rfl : (0:ℝ) ≤ 0) hs0(hs))
    (y : WI(s)) (hy : ∀ j : SpectralLineJetIndex χ a s, spectralSobolevPairing y zeroVec(χ,hs,j) = 0) :
    y ∈ globalThetaSobolev F a (le_rfl : (0:ℝ) ≤ 0) hs0(hs) := by
  let : CompactSpace C₁ := (ideleClassGroup_finiteness F).2.1
  let κ : Measure C₁ := Measure.haar
  let : κ.IsHaarMeasure := inferInstanceAs (Measure.haar (G := C₁)).IsHaarMeasure
  let ρ := (hardySobolevTranslation μ𝔽 m𝔽 0 0 s le_rfl hs0(hs)).comp (ideleClassNorm F).ker.subtype
  have hρ : Continuous (fun p : C₁ × WI(s) ↦ ρ p.1 p.2) :=
    (exists_hardySobolevTranslation μ𝔽 m𝔽 0 0 s le_rfl hs0(hs)).choose_spec.2.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  let Λ (j : SpectralLineJetIndex χ a s) := (lineProfile_jet_normOne_dual χ hs j).choose
  have hΛ (j : SpectralLineJetIndex χ a s) := (lineProfile_jet_normOne_dual χ hs j).choose_spec
  apply lineProfile_compact_components κ ρ hρ _ (Submodule.isClosed_topologicalClosure _) Λ y
  · intro g j
    exact ((hΛ j).2.1 g y).trans (by rw [(hΛ j).1 y,hy j,mul_zero])
  · intro ξ z hz hAll
    have hz' : z ∈ Wχ(χ ξ, s, hs0(hs)) := by
      change z ∈ actionIsotype ρ ((χ ξ).comp restriction)
      rw [hχ ξ]
      exact hz
    exact hiso ξ ⟨z,hz'⟩ (fun j _ ↦ ((hΛ j).1 z).symm.trans (hAll j))

/-- At width zero the separating compact-character argument assembles the
local multiplier synthesis for every character into ambient norm closure. -/
private theorem spectralLineJet_commonKernel_reverse_proved (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice χ) {a s : ℝ} (hs : 1 < s)
    (y : WI(s)) (hy : ∀ j : SpectralLineJetIndex χ a s, spectralSobolevPairing y zeroVec(χ,hs,j) = 0) :
    y ∈ globalThetaSobolev F a (le_rfl : (0:ℝ) ≤ 0) hs0(hs) :=
  lineProfile_reverse_of_isotypes χ hχ hs (fun ξ ↦ lineProfile_isotype_synthesis χ ξ hs) y hy

private theorem spectralLineJet_commonKernel_forward_proved (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    {a s : ℝ} (hs : 1 < s) (y : WI(s)) (hy : y ∈ globalThetaSobolev F a (le_rfl : (0:ℝ) ≤ 0) hs0(hs))
    (j : SpectralLineJetIndex χ a s) : spectralSobolevPairing y zeroVec(χ,hs,j) = 0 := by
  let H := lineProfile_jet_normOne_dual χ hs j
  let Λ := H.choose
  let E := (existsUnique_globalThetaSobolevEmbedding (F := F) a 0 0 s le_rfl hs0(hs)).exists.choose
  have hgen (f : adelePolarSubspace F) : Λ (E (Submodule.Quotient.mk f)) = 0 := by
    have hE := (existsUnique_globalThetaSobolevEmbedding (F := F) a 0 0 s le_rfl hs0(hs)).exists.choose_spec.2 f
    have hk := ((lt_spectralBoundaryMultiplicity s _ _).mp j.property).1
    have hm := stripTheta_weighted_moment_zero (χ j.val.1) f a 0 j.val.2.1 j.val.2.2 (by simpa only [add_zero] using hk)
    exact (H.choose_spec.2.2 _).trans ((integral_congr_ae (hE.mul EventuallyEq.rfl)).trans hm)
  have hR : E.toLinearMap.range ≤ Λ.ker := by
    rintro _ ⟨v, rfl⟩
    induction v using Submodule.Quotient.induction_on with
    | H f => exact hgen f
  exact (H.choose_spec.1 y).symm.trans ((E.toLinearMap.range.topologicalClosure_minimal hR Λ.isClosed_ker) hy)

end LineThetaSynthesis

/-- Paper: Theorem 10.2.1.1, pp. 440–443. The weighted theta closure is
the common kernel of the admitted line jets.
Deviation: Compact frequency localization and the strict Sobolev jet cutoff supply the line approximation used on p. 443. -/
theorem spectralLineJet_commonKernel (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice χ) {a s : ℝ} (hs : 1 < s) :
    let u : SpectralLineJetIndex χ a s → W'(0, 0, s) := lineU(χ, hs)
    JetKernel(a, le_rfl (a := (0 : ℝ)), lineHs(hs), u) := by
  intro u y
  exact ⟨fun hy ↦ spectralLineJet_commonKernel_forward_proved χ hs y hy,
    spectralLineJet_commonKernel_reverse_proved χ _hχ hs y⟩

/-- Paper: Theorem 10.2.1.1, pp. 440–443. Single-jet interpolants have
representatives whose images span a dense subspace of the line quotient.
Gap: The interpolation and density asserted on p. 443 follow from the corresponding
strip assertion at width zero. -/
theorem spectralLineJet_denseInterpolants (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice χ) {a s : ℝ} (hs : 1 < s) :
    let J := SpectralLineJetIndex χ a s
    let u : J → W'(0, 0, s) := lineU(χ, hs)
    JetInterpolation(J, a, le_rfl (a := (0 : ℝ)), lineHs(hs), u) := by
  apply spectralLineJet_zeroWidth_transport χ a hs
    (fun hl u ↦ JetInterpolation(SpectralLineJetIndex χ a s, a, hl, lineHs(hs), u))
  intro e
  obtain ⟨v, hv, hc, hd⟩ :=
    spectralStripJet_denseInterpolants (a := a) χ _hχ (le_refl (0 : ℝ)) (lineHs(hs))
  refine ⟨v ∘ e, fun i ↦ hv (e i), fun i j hij ↦ hc (e i) (e j) (e.injective.ne hij), ?_⟩
  let q := (Θ(a, stripI(le_refl (0 : ℝ)), lineHs(hs))).mkQ
  change Dense (Submodule.span ℂ (range ((fun j ↦ q (v j)) ∘ e)) :
    Set (spectralSobolevQuotient F a (stripI(le_refl (0 : ℝ))) (lineHs(hs))))
  rwa [e.surjective.range_comp]

/-- Paper: Theorem 10.2.1.1 and Terminology 10.2.1.1, p. 440. The a-line
jets represent quotient functionals and admit a Markushevich biorthogonal family.
Deviation: Index directly by the admitted jets, so reindexing permits any
enumeration, including finite and empty families. Apply the strict cutoff. -/
theorem spectralLineMarkushevichBasis (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice χ) {a s : ℝ} (hs : 1 < s) :
    let J := SpectralLineJetIndex χ a s
    let Q := spectralSobolevQuotient F a (le_rfl (a := (0 : ℝ))) (le_of_lt (zero_lt_one.trans hs))
    let D := spectralSobolevDualEmbedding F a (le_rfl (a := (0 : ℝ))) (le_of_lt (zero_lt_one.trans hs))
    Countable J ∧ ∃ (x : J → Q) (Λ : J → StrongDual ℂ Q), IsSpectralMarkushevichBasis x Λ ∧
      ∀ j, D (Λ j) = (spectralLineJet_memLp χ hs j).toLp (lineJet(χ, j)) := by
  exact ⟨spectralLineJet_countable χ a s, spectralSobolevQuotient_basis_of_interpolation a
    (le_rfl (a := (0 : ℝ))) (lineHs(hs)) (lineU(χ, hs))
    (spectralLineJet_commonKernel χ hχ hs) (spectralLineJet_denseInterpolants χ hχ hs)⟩

/-- Paper: Corollary 10.2.1.4, p. 444. The a-line basis in the quotient dual
is normalized in the norm of its realization in the negative space.
Deviation: Apply the strict cutoff and allow finite or empty index types. -/
theorem spectralLineMarkushevichBasis_normalized
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (_hχ : IsSpectralBasepointChoice χ)
    {a s : ℝ} (hs : 1 < s) :
    let J := SpectralLineJetIndex χ a s
    let Q := spectralSobolevQuotient F a (le_rfl (a := (0 : ℝ))) (le_of_lt (zero_lt_one.trans hs))
    let D := spectralSobolevDualEmbedding F a (le_rfl (a := (0 : ℝ))) (le_of_lt (zero_lt_one.trans hs))
    ∃ (x : J → Q) (Λ : J → StrongDual ℂ Q), IsSpectralMarkushevichBasis x Λ ∧
      (∀ j, D (Λ j) = (spectralLineJet_memLp χ hs j).toLp (lineJet(χ, j))) ∧
      IsNormalizedSpectralFamily (fun j ↦ D (Λ j)) := by
  obtain ⟨x, Λ, hB, hD⟩ := (spectralLineMarkushevichBasis (a := a) χ _hχ hs).2
  obtain ⟨C, hC, hbound⟩ := spectralLineJet_annulus (a := a) χ _hχ hs
  refine ⟨x, Λ, hB, hD, ⟨C, ?_⟩, ⟨C⁻¹, inv_pos.mpr hC, ?_⟩⟩
  · intro j
    simpa only [hD j] using (hbound j).2
  · intro j
    simpa only [hD j] using (hbound j).1

/-- Paper: Theorem 10.2.2.1, p. 446. The discrete divisor in each norm
chart gives countably many strip jets over the countable norm-one dual. -/
theorem spectralStripJet_countable (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (a α s : ℝ) :
    Countable (SpectralStripJetIndex χ a α s) := by
  have hK : IsCompact ((ideleClassNorm F).ker : Set C𝔽) :=
    IsModulation.isCompact_ker (m := m𝔽) hm𝔽
  let : CompactSpace C₁ := isCompact_iff_compactSpace.mp hK
  let : LocallyCompactSpace C₁ := hK.isClosed.locallyCompactSpace
  let : SecondCountableTopology C₁ := Topology.IsInducing.subtypeVal.secondCountableTopology
  let : SecondCountableTopology Circle :=
    inferInstanceAs (SecondCountableTopology (Metric.sphere (0 : ℂ) 1))
  let : SecondCountableTopology (PontryaginDual C₁) :=
    (ContinuousMonoidHom.isEmbedding_toContinuousMap C₁ Circle).secondCountableTopology
  let : Countable (PontryaginDual C₁) := countable_of_Lindelof_of_discrete
  let Z (ω : PontryaginDual C₁) := {z : ℂ | 0 < multiplicity(χ ω, z)}
  have hc (ω : PontryaginDual C₁) : (Z ω).Countable := by
    have hm := (continuedCompletedHeckeL_spec (χ ω)).1.meromorphicOn
    have hcod : (Z ω)ᶜ ∈ Filter.codiscrete ℂ := by
      filter_upwards [hm.codiscreteWithin_setOfPred_meromorphicOrderAt_eq_zero_or_top] with z hz
      rcases hz.2 with h | h <;> simp [Z, h]
    let : DiscreteTopology (Z ω) := isDiscrete_iff_discreteTopology.mp
      (compl_mem_codiscrete_iff.mp hcod).2
    exact Set.countable_coe_iff.mp countable_of_Lindelof_of_discrete
  let W := ⋃ ω, Z ω
  let : Countable W := (Set.countable_iUnion hc).to_subtype
  have hz (j : SpectralStripJetIndex χ a α s) : shift(a + j.val.2.1, j.val.2.2.1) ∈ W := by
    apply Set.mem_iUnion.mpr
    refine ⟨j.val.1, ?_⟩
    have h := j.property
    change 0 < multiplicity(χ j.val.1, shift(a + j.val.2.1, j.val.2.2.1))
    unfold spectralStripMultiplicity spectralBoundaryMultiplicity at h
    split_ifs at h <;> omega
  let e (j : SpectralStripJetIndex χ a α s) : PontryaginDual C₁ × W × ℕ :=
    (j.val.1, ⟨shift(a + j.val.2.1, j.val.2.2.1), hz j⟩, j.val.2.2.2)
  apply Function.Injective.countable (f := e)
  intro i j hij
  have hre := congrArg (fun p : PontryaginDual C₁ × W × ℕ ↦ p.2.1.val.re) hij
  have him := congrArg (fun p : PontryaginDual C₁ × W × ℕ ↦ p.2.1.val.im) hij
  have hω := congrArg (fun p : PontryaginDual C₁ × W × ℕ ↦ p.1) hij
  have hk := congrArg (fun p : PontryaginDual C₁ × W × ℕ ↦ p.2.2) hij
  exact Subtype.ext (Prod.ext hω (Prod.ext (by simpa [e] using hre) (Prod.ext (by simpa [e] using him) hk)))

/-- Paper: Theorem 10.2.2.1 and Terminology 10.2.2.1, p. 446. The strip
jets represent quotient functionals and admit a Markushevich biorthogonal family.
Deviation: Exclude the divergent endpoint and allow finite or empty enumerations. -/
theorem spectralStripMarkushevichBasis (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice χ) {a α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) :
    let J := SpectralStripJetIndex χ a α s
    let Q := spectralSobolevQuotient F a (neg_nonpos.mpr hα |>.trans hα) hs
    let D := spectralSobolevDualEmbedding F a (neg_nonpos.mpr hα |>.trans hα) hs
    Countable J ∧ ∃ (x : J → Q) (Λ : J → StrongDual ℂ Q), IsSpectralMarkushevichBasis x Λ ∧
      ∀ j, D (Λ j) = (spectralStripJet_memLp χ hα hs j).toLp (stripJet(χ, j)) := by
  exact ⟨spectralStripJet_countable χ a α s, spectralSobolevQuotient_basis_of_interpolation a
    (stripI(hα)) hs (stripU(χ, hα, hs))
    (spectralStripJet_commonKernel χ hχ hα hs) (spectralStripJet_denseInterpolants χ hχ hα hs)⟩

private theorem spectralStripJet_norm_sq (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    {a α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (j : SpectralStripJetIndex χ a α s)
    (ν : Measure C𝔽) [ν.IsHaarMeasure] (hν : ν = canonicalModulatedHaar m𝔽 hm𝔽) :
    ‖(spectralStripJet_memLp χ hα hs j).toLp (stripJet(χ, j))‖ ^ 2 =
      (Measure.haarScalarFactor μ𝔽 ν : ℝ) *
        ∫ x : ℝ, Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) *
          ((1 + x ^ 2) ^ (s / 2))⁻¹ ∂volume := by
  let u := (spectralStripJet_memLp χ hα hs j).toLp (stripJet(χ, j))
  let f : ℝ → ℝ := fun x ↦
    Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) * ((1 + x ^ 2) ^ (s / 2))⁻¹
  have h1 : ‖u‖ ^ 2 = ∫ g : C𝔽, ‖u g‖ ^ 2 ∂(L2μ'(-α, α, s)) := spectralJet_lp_norm_sq u
  have h2 : ∫ g : C𝔽, ‖u g‖ ^ 2 ∂(L2μ'(-α, α, s)) =
      ∫ g : C𝔽, Real.exp (2 * j.val.2.1 * logNorm g) * (logNorm g) ^ (2 * j.val.2.2.2)
        ∂(L2μ'(-α, α, s)) := by
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (spectralStripJet_memLp χ hα hs j)] with g hg
    rw [hg, spectralZeroJet_norm_sq]
  have h3 : ∫ g : C𝔽, Real.exp (2 * j.val.2.1 * logNorm g) * (logNorm g) ^ (2 * j.val.2.2.2)
      ∂(L2μ'(-α, α, s)) = ∫ g : C𝔽, f (logNorm g) ∂μ𝔽 := by
    rw [integral_withDensity_eq_integral_toReal_smul
      ((symmIntervalSobolevDensity_inv_continuous hα s).measurable.ennreal_ofReal)
      (ae_of_all μ𝔽 fun _ ↦ ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (ae_of_all μ𝔽 fun g ↦ ?_)
    dsimp only [f]
    rw [smul_eq_mul,
      ENNReal.toReal_ofReal (inv_nonneg.mpr (symmIntervalSobolevDensity_pos hα s (logNorm g)).le),
      mul_comm, stripJet_integrand_eq hα]
  have hmp : MeasurePreserving (fun g : C𝔽 ↦ logNorm g) ν volume := by
    rw [hν]
    exact sobolev_log_preserving m𝔽 hm𝔽 hms𝔽
  have hlogm : AEMeasurable (fun g : C𝔽 ↦ logNorm g) ν :=
    (continuous_logModule' m𝔽).measurable.aemeasurable
  have hν_eq : ∫ g : C𝔽, f (logNorm g) ∂ν = ∫ x : ℝ, f x ∂volume := by
    rw [← hmp.map_eq,
      integral_map hlogm
        (stripJet_integrand_continuous α s j.val.2.1 j.val.2.2.2).aestronglyMeasurable]
  have h4 : ∫ g : C𝔽, f (logNorm g) ∂μ𝔽 = (Measure.haarScalarFactor μ𝔽 ν : ℝ) * ∫ x : ℝ, f x ∂volume := by
    conv_lhs => rw [Measure.isMulLeftInvariant_eq_smul μ𝔽 ν]
    rw [integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul, hν_eq]
  exact h1.trans (h2.trans (h3.trans h4))

/-- Paper: Proposition 10.2.2.2 and (10.2.2.8), pp. 446–447. A single
positive lower bound applies to the norms of all the strip jet classes.
Deviation: Use the strip zeros and reciprocal strip norm of Theorem 10.2.2.1.
Disjointness from the open ball also applies to the empty family. -/
theorem spectralStripJet_lowerBound (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice χ) {a α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s) :
    ∃ c : ℝ, 0 < c ∧ ∀ j : SpectralStripJetIndex χ a α s,
      let u := (spectralStripJet_memLp χ hα (le_of_lt (zero_lt_one.trans hs)) j).toLp (stripJet(χ, j))
      c ≤ ‖u‖ := by
  let ν : Measure C𝔽 := canonicalModulatedHaar m𝔽 hm𝔽
  let : ν.IsHaarMeasure := (existsUnique_canonicalModulatedHaar m𝔽 hm𝔽).exists.choose_spec.1
  let hs₀ : 0 ≤ s := le_of_lt (zero_lt_one.trans hs)
  let c₀ : ℝ := Real.exp (-8 * α) * ((5 : ℝ) ^ (s / 2))⁻¹
  have hc₀ : 0 < c₀ := mul_pos (Real.exp_pos _) (inv_pos.mpr (Real.rpow_pos_of_pos (by norm_num) _))
  have hfac_pos : 0 < (Measure.haarScalarFactor μ𝔽 ν : ℝ) := by
    exact_mod_cast (Measure.haarScalarFactor_pos_of_isHaarMeasure μ𝔽 ν)
  let c : ℝ := Real.sqrt ((Measure.haarScalarFactor μ𝔽 ν : ℝ) * c₀)
  refine ⟨c, Real.sqrt_pos.mpr (mul_pos hfac_pos hc₀), fun j ↦ ?_⟩
  dsimp only
  have hcond : (-α < j.val.2.1 ∧ j.val.2.1 < α) ∨
      ((j.val.2.1 = -α ∨ j.val.2.1 = α) ∧ 2 * (j.val.2.2.2 : ℝ) + 1 < s) := by
    have hj := j.property
    unfold spectralStripMultiplicity at hj
    split_ifs at hj with h1 h2
    · exact Or.inl h1
    · refine Or.inr ⟨h2, ?_⟩
      have horder : (j.val.2.2.2 : ℝ) < (s - 1) / 2 :=
        ((lt_spectralBoundaryMultiplicity s _ _).mp hj).2
      linarith
    · omega
  have hf_int : Integrable (fun x : ℝ ↦
      Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) *
        ((1 + x ^ 2) ^ (s / 2))⁻¹) volume :=
    spectralStripJet_integrable hα hs₀ hcond
  have hind_int : Integrable ((Icc (1 : ℝ) 2).indicator fun _ ↦ c₀) volume :=
    (integrableOn_const (by simp)).integrable_indicator measurableSet_Icc
  have hb : j.val.2.1 ∈ Icc (-α) α := (SpectralStripJetIndex.mem_strip_order_pos hα j).1
  have hle : ∀ x : ℝ, (Icc (1 : ℝ) 2).indicator (fun _ ↦ c₀) x ≤
      Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) *
        ((1 + x ^ 2) ^ (s / 2))⁻¹ := by
    intro x
    by_cases hx : x ∈ Icc (1 : ℝ) 2
    · rw [indicator_of_mem hx]
      have hxpos : 0 ≤ x := by linarith [hx.1]
      have hexp : Real.exp (-8 * α) ≤ Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) := by
        rw [abs_of_nonneg hxpos]
        exact Real.exp_le_exp.mpr (by nlinarith [hb.1, hx.1, hx.2])
      have hpow : (1 : ℝ) ≤ x ^ (2 * j.val.2.2.2) := one_le_pow₀ hx.1
      have hbase : 1 + x ^ 2 ≤ 5 := by nlinarith [hx.1, hx.2]
      have hrpow : (1 + x ^ 2) ^ (s / 2) ≤ (5 : ℝ) ^ (s / 2) :=
        Real.rpow_le_rpow (by positivity) hbase (by linarith)
      have hinv : ((5 : ℝ) ^ (s / 2))⁻¹ ≤ ((1 + x ^ 2) ^ (s / 2))⁻¹ :=
        inv_anti₀ (Real.rpow_pos_of_pos (by positivity) _) hrpow
      have hprod : Real.exp (-8 * α) ≤
          Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) := by
        calc
          Real.exp (-8 * α) = Real.exp (-8 * α) * 1 := (mul_one _).symm
          _ ≤ Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) :=
            mul_le_mul hexp hpow zero_le_one (Real.exp_pos _).le
      exact mul_le_mul hprod hinv
        (inv_nonneg.mpr (Real.rpow_pos_of_pos (by norm_num) _).le)
        (mul_nonneg (Real.exp_pos _).le (Even.pow_nonneg (even_two_mul _) x))
    · rw [indicator_of_notMem hx]
      exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (Even.pow_nonneg (even_two_mul _) x))
        (inv_nonneg.mpr (Real.rpow_pos_of_pos (by positivity) _).le)
  have hint_le : c₀ ≤ ∫ x : ℝ,
      Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) *
        ((1 + x ^ 2) ^ (s / 2))⁻¹ ∂volume := by
    have h1 := integral_mono hind_int hf_int hle
    have h2 : ∫ x : ℝ, (Icc (1 : ℝ) 2).indicator (fun _ ↦ c₀) x ∂volume = c₀ := by
      rw [integral_indicator measurableSet_Icc, setIntegral_const, Real.volume_real_Icc]
      norm_num
    linarith
  have hsq : (Measure.haarScalarFactor μ𝔽 ν : ℝ) * c₀ ≤
      ‖(spectralStripJet_memLp χ hα hs₀ j).toLp (stripJet(χ, j))‖ ^ 2 := by
    rw [spectralStripJet_norm_sq χ hα hs₀ j ν rfl]
    exact mul_le_mul_of_nonneg_left hint_le hfac_pos.le
  calc
    c = Real.sqrt ((Measure.haarScalarFactor μ𝔽 ν : ℝ) * c₀) := rfl
    _ ≤ Real.sqrt (‖(spectralStripJet_memLp χ hα hs₀ j).toLp (stripJet(χ, j))‖ ^ 2) :=
      Real.sqrt_le_sqrt hsq
    _ = ‖(spectralStripJet_memLp χ hα hs₀ j).toLp (stripJet(χ, j))‖ :=
      Real.sqrt_sq (norm_nonneg _)

/-- Paper: Proposition 10.2.2.2, pp. 446–447. A uniform strip estimate requires a
bound on admitted jet orders and a boundary margin for the nonintegrable powers.
Gap: The paper supplies neither estimate for the actual completed Hecke divisor. -/
theorem spectralStripJet_order_and_margin (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice χ) {a α s : ℝ} (_hα : 0 ≤ α) (_hs : 1 < s) :
    ∃ (K : ℕ) (δ : ℝ), 0 < δ ∧ ∀ j : SpectralStripJetIndex χ a α s,
      j.val.2.2.2 ≤ K ∧ ((s - 1) / 2 ≤ (j.val.2.2.2 : ℝ) → |j.val.2.1| ≤ α - δ) := by sorry

/-- Paper: Proposition 10.2.2.2, pp. 446–447. Finitely many integrable
boundary powers and a positive exponential margin on all other powers give
a uniform norm bound. -/
theorem spectralStripJet_upperBound_of_margin (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    {a α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s) (K : ℕ) (δ : ℝ) (_hδ : 0 < δ)
    (_h : ∀ j : SpectralStripJetIndex χ a α s, j.val.2.2.2 ≤ K ∧
      ((s - 1) / 2 ≤ (j.val.2.2.2 : ℝ) → |j.val.2.1| ≤ α - δ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ j : SpectralStripJetIndex χ a α s,
      ‖(spectralStripJet_memLp χ hα (lineHs(hs)) j).toLp (stripJet(χ, j))‖ ≤ C := by
  let ν : Measure C𝔽 := canonicalModulatedHaar m𝔽 hm𝔽
  let : ν.IsHaarMeasure := (existsUnique_canonicalModulatedHaar m𝔽 hm𝔽).exists.choose_spec.1
  let hs₀ : 0 ≤ s := lineHs(hs)
  let N : ℕ := Nat.ceil ((s - 1) / 2)
  let M_bdry : ℝ := ∑ m ∈ Finset.range N,
    ∫ x : ℝ, x ^ (2 * m) * ((1 + x ^ 2) ^ (s / 2))⁻¹ ∂volume
  let M_int : ℝ :=
    ∫ x : ℝ, Real.exp (-(2 * δ) * |x|) * (1 + x ^ (2 * K)) ∂volume
  have hfac_nonneg : 0 ≤ (Measure.haarScalarFactor μ𝔽 ν : ℝ) := NNReal.coe_nonneg _
  have hM_bdry_nonneg : 0 ≤ M_bdry :=
    Finset.sum_nonneg fun m _ ↦ integral_nonneg fun x ↦
      mul_nonneg (Even.pow_nonneg (even_two_mul m) x)
        (inv_nonneg.mpr (Real.rpow_pos_of_pos (by positivity) _).le)
  have hM_int_nonneg : 0 ≤ M_int :=
    integral_nonneg fun x ↦
      mul_nonneg (Real.exp_pos _).le (add_nonneg zero_le_one (Even.pow_nonneg (even_two_mul K) x))
  have hM_int_integrable : Integrable (fun x : ℝ ↦ Real.exp (-(2 * δ) * |x|) * (1 + x ^ (2 * K)))
      volume := by
    have h0 := integrable_exp_neg_abs_mul_pow (by linarith : 0 < 2 * δ) 0
    have hK := integrable_exp_neg_abs_mul_pow (by linarith : 0 < 2 * δ) K
    refine (h0.add hK).congr (ae_of_all _ fun x ↦ ?_)
    change Real.exp (-(2 * δ) * |x|) * x ^ (2 * 0) +
        Real.exp (-(2 * δ) * |x|) * x ^ (2 * K) =
      Real.exp (-(2 * δ) * |x|) * (1 + x ^ (2 * K))
    simp only [mul_zero, pow_zero, mul_one]
    ring
  let B : ℝ := 1 + (Measure.haarScalarFactor μ𝔽 ν : ℝ) * (M_bdry + M_int)
  have hB_pos : 0 < B := by
    have : 0 ≤ (Measure.haarScalarFactor μ𝔽 ν : ℝ) * (M_bdry + M_int) :=
      mul_nonneg hfac_nonneg (add_nonneg hM_bdry_nonneg hM_int_nonneg)
    linarith
  refine ⟨Real.sqrt B, Real.sqrt_pos.mpr hB_pos, fun j ↦ ?_⟩
  have hcond : (-α < j.val.2.1 ∧ j.val.2.1 < α) ∨
      ((j.val.2.1 = -α ∨ j.val.2.1 = α) ∧ 2 * (j.val.2.2.2 : ℝ) + 1 < s) := by
    have hj := j.property
    unfold spectralStripMultiplicity at hj
    split_ifs at hj with h1 h2
    · exact Or.inl h1
    · refine Or.inr ⟨h2, ?_⟩
      have horder : (j.val.2.2.2 : ℝ) < (s - 1) / 2 :=
        ((lt_spectralBoundaryMultiplicity s _ _).mp hj).2
      linarith
    · omega
  have hf_int : Integrable (fun x : ℝ ↦
      Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) *
        ((1 + x ^ 2) ^ (s / 2))⁻¹) volume :=
    spectralStripJet_integrable hα hs₀ hcond
  have hint_bound : ∫ x : ℝ,
      Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) *
        ((1 + x ^ 2) ^ (s / 2))⁻¹ ∂volume ≤ M_bdry + M_int := by
    by_cases hk : (j.val.2.2.2 : ℝ) < (s - 1) / 2
    · have hk' : 2 * (j.val.2.2.2 : ℝ) + 1 < s := by linarith
      have hb : j.val.2.1 ∈ Icc (-α) α := (SpectralStripJetIndex.mem_strip_order_pos hα j).1
      have hba : |j.val.2.1| ≤ α := abs_le.mpr hb
      have h1 : ∫ x : ℝ,
          Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) *
            ((1 + x ^ 2) ^ (s / 2))⁻¹ ∂volume ≤
          ∫ x : ℝ, x ^ (2 * j.val.2.2.2) * ((1 + x ^ 2) ^ (s / 2))⁻¹ ∂volume := by
        refine integral_mono hf_int (integrable_pow_mul_rpow_inv hk') fun x ↦ ?_
        have hbx : j.val.2.1 * x ≤ α * |x| := by
          calc
            j.val.2.1 * x ≤ |j.val.2.1 * x| := le_abs_self _
            _ = |j.val.2.1| * |x| := abs_mul _ _
            _ ≤ α * |x| := mul_le_mul_of_nonneg_right hba (abs_nonneg x)
        have hexp : Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) ≤ 1 :=
          Real.exp_le_one_iff.mpr (by linarith)
        rw [mul_assoc]
        calc
          Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) *
              (x ^ (2 * j.val.2.2.2) * ((1 + x ^ 2) ^ (s / 2))⁻¹)
            ≤ 1 * (x ^ (2 * j.val.2.2.2) * ((1 + x ^ 2) ^ (s / 2))⁻¹) :=
              mul_le_mul_of_nonneg_right hexp
                (mul_nonneg (Even.pow_nonneg (even_two_mul _) x)
                  (inv_nonneg.mpr (Real.rpow_pos_of_pos (by positivity) _).le))
          _ = x ^ (2 * j.val.2.2.2) * ((1 + x ^ 2) ^ (s / 2))⁻¹ := one_mul _
      have hjN : j.val.2.2.2 ∈ Finset.range N := Finset.mem_range.mpr (Nat.lt_ceil.mpr hk)
      have h2 : ∫ x : ℝ, x ^ (2 * j.val.2.2.2) * ((1 + x ^ 2) ^ (s / 2))⁻¹ ∂volume ≤ M_bdry :=
        Finset.single_le_sum
          (f := fun m ↦ ∫ x : ℝ, x ^ (2 * m) * ((1 + x ^ 2) ^ (s / 2))⁻¹ ∂volume)
          (fun m _ ↦ integral_nonneg fun x ↦
            mul_nonneg (Even.pow_nonneg (even_two_mul m) x)
              (inv_nonneg.mpr (Real.rpow_nonneg (by positivity) _))) hjN
      linarith
    · have hk_ge : (s - 1) / 2 ≤ (j.val.2.2.2 : ℝ) := not_lt.mp hk
      have hmargin : |j.val.2.1| ≤ α - δ := (_h j).2 hk_ge
      have hkK : j.val.2.2.2 ≤ K := (_h j).1
      have h1 : ∫ x : ℝ,
          Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) *
            ((1 + x ^ 2) ^ (s / 2))⁻¹ ∂volume ≤ M_int := by
        refine integral_mono hf_int hM_int_integrable fun x ↦ ?_
        have hbx : j.val.2.1 * x ≤ (α - δ) * |x| := by
          calc
            j.val.2.1 * x ≤ |j.val.2.1 * x| := le_abs_self _
            _ = |j.val.2.1| * |x| := abs_mul _ _
            _ ≤ (α - δ) * |x| := mul_le_mul_of_nonneg_right hmargin (abs_nonneg x)
        have hexp : Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) ≤ Real.exp (-(2 * δ) * |x|) :=
          Real.exp_le_exp.mpr (by nlinarith)
        have hpow : x ^ (2 * j.val.2.2.2) ≤ 1 + x ^ (2 * K) := by
          have hxa : x ^ (2 * j.val.2.2.2) = |x| ^ (2 * j.val.2.2.2) := by
            rw [pow_mul, ← sq_abs, ← pow_mul]
          have hxaK : x ^ (2 * K) = |x| ^ (2 * K) := by
            rw [pow_mul, ← sq_abs, ← pow_mul]
          rw [hxa, hxaK]
          rcases le_total |x| 1 with hx1 | hx1
          · have : |x| ^ (2 * j.val.2.2.2) ≤ 1 := pow_le_one₀ (abs_nonneg x) hx1
            linarith [pow_nonneg (abs_nonneg x) (2 * K)]
          · have : |x| ^ (2 * j.val.2.2.2) ≤ |x| ^ (2 * K) :=
              pow_le_pow_right₀ hx1 (Nat.mul_le_mul_left 2 hkK)
            linarith
        have hinv_le : ((1 + x ^ 2) ^ (s / 2))⁻¹ ≤ 1 :=
          inv_le_one_of_one_le₀ (Real.one_le_rpow (by nlinarith [sq_nonneg x]) (by linarith))
        calc
          Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) *
              ((1 + x ^ 2) ^ (s / 2))⁻¹
            ≤ Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) * 1 :=
              mul_le_mul_of_nonneg_left hinv_le
                (mul_nonneg (Real.exp_pos _).le (Even.pow_nonneg (even_two_mul _) x))
          _ = Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) := mul_one _
          _ ≤ Real.exp (-(2 * δ) * |x|) * (1 + x ^ (2 * K)) :=
              mul_le_mul hexp hpow (Even.pow_nonneg (even_two_mul _) x) (Real.exp_pos _).le
      linarith
  have hsq : ‖(spectralStripJet_memLp χ hα hs₀ j).toLp (stripJet(χ, j))‖ ^ 2 ≤ B := by
    rw [spectralStripJet_norm_sq χ hα hs₀ j ν rfl]
    have hmul : (Measure.haarScalarFactor μ𝔽 ν : ℝ) *
        ∫ x : ℝ, Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) *
          ((1 + x ^ 2) ^ (s / 2))⁻¹ ∂volume ≤
        (Measure.haarScalarFactor μ𝔽 ν : ℝ) * (M_bdry + M_int) :=
      mul_le_mul_of_nonneg_left hint_bound hfac_nonneg
    dsimp only [B]
    linarith
  calc
    ‖(spectralStripJet_memLp χ hα hs₀ j).toLp (stripJet(χ, j))‖
      = Real.sqrt (‖(spectralStripJet_memLp χ hα hs₀ j).toLp (stripJet(χ, j))‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt B := Real.sqrt_le_sqrt hsq

/-- Paper: Proposition 10.2.2.2 and (10.2.2.8), pp. 446–447. A single upper
bound applies to the norms of all the strip jet classes.
Deviation: Use the strip zeros and both cutoff equations of Theorem 10.2.2.1,
with the reciprocal strip norm throughout. -/
theorem spectralStripJet_upperBound (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice χ) {a α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s) :
    ∃ C : ℝ, 0 < C ∧ ∀ j : SpectralStripJetIndex χ a α s,
      let u := (spectralStripJet_memLp χ hα (le_of_lt (zero_lt_one.trans hs)) j).toLp (stripJet(χ, j))
      ‖u‖ ≤ C := by
  obtain ⟨K, δ, hδ, h⟩ := spectralStripJet_order_and_margin (a := a) χ _hχ hα hs
  exact spectralStripJet_upperBound_of_margin χ hα hs K δ hδ h

/-- Paper: Corollary 10.2.2.3, p. 447. The strip basis in the quotient dual
is normalized in the norm of its realization in the reciprocal strip space.
Deviation: Use the strip zeros and cutoff of Theorem 10.2.2.1. The ambient
negative space is the reciprocal strip space as specified by the pairing. -/
theorem spectralStripMarkushevichBasis_normalized
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (_hχ : IsSpectralBasepointChoice χ)
    {a α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s) :
    let hs₀ := le_of_lt (zero_lt_one.trans hs)
    let J := SpectralStripJetIndex χ a α s
    let Q := spectralSobolevQuotient F a (neg_nonpos.mpr hα |>.trans hα) hs₀
    let D := spectralSobolevDualEmbedding F a (neg_nonpos.mpr hα |>.trans hα) hs₀
    ∃ (x : J → Q) (Λ : J → StrongDual ℂ Q), IsSpectralMarkushevichBasis x Λ ∧
      (∀ j, D (Λ j) = (spectralStripJet_memLp χ hα hs₀ j).toLp (stripJet(χ, j))) ∧
      IsNormalizedSpectralFamily (fun j ↦ D (Λ j)) := by
  obtain ⟨x, Λ, hB, hD⟩ := (spectralStripMarkushevichBasis (a := a) χ _hχ hα
    (lineHs(hs))).2
  obtain ⟨C, _, hupper⟩ := spectralStripJet_upperBound (a := a) χ _hχ hα hs
  obtain ⟨c, hc, hlower⟩ := spectralStripJet_lowerBound (a := a) χ _hχ hα hs
  refine ⟨x, Λ, hB, hD, ⟨C, ?_⟩, ⟨c, hc, ?_⟩⟩
  · intro j
    simpa only [hD j] using hupper j
  · intro j
    simpa only [hD j] using hlower j

end RiemannMasullo
