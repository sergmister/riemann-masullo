module

public import RiemannMasullo.Ch10_TraceSpectral.Sec1
public import RiemannMasullo.AppD_SchwartzBruhat.Sec3a_part2
public import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec1
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

/-- Paper: Theorem 10.2.1.1, pp. 440–443. The weighted theta closure is
the common kernel of the admitted line jets.
Gap: The proof on p. 443 does not identify this closure in the line norm. -/
theorem spectralLineJet_commonKernel (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice χ) {a s : ℝ} (hs : 1 < s) :
    let u : SpectralLineJetIndex χ a s → W'(0, 0, s) := lineU(χ, hs)
    JetKernel(a, le_rfl (a := (0 : ℝ)), lineHs(hs), u) := by sorry

/-- Paper: Theorem 10.2.1.1, pp. 440–443. Single-jet interpolants have
representatives whose images span a dense subspace of the line quotient.
Gap: The asserted finite-band adjoint range does not supply these interpolants
and their density. -/
theorem spectralLineJet_denseInterpolants (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice χ) {a s : ℝ} (hs : 1 < s) :
    let J := SpectralLineJetIndex χ a s
    let u : J → W'(0, 0, s) := lineU(χ, hs)
    JetInterpolation(J, a, le_rfl (a := (0 : ℝ)), lineHs(hs), u) := by sorry

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

section TestDuality

local notation "E" => ModulatedExponentialDecay m𝔽 univ
local notation "ρE" => (exists_modulatedExponentialDecay_translationAction m𝔽 univ
  hm𝔽 hms𝔽 ordConnected_univ univ_nonempty).choose
local notation "Eω(" ω ")" => actionIsotype ((ρE).comp (ideleClassNorm F).ker.subtype) ω
local notation "ℬ₀" => ↥(adelePolarSubspace F)

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
            fun g ↦ (ω⁻¹ k : ℂ) * u g) → T u = 0 → u = 0 := by sorry

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

-- TODO(paper-gap): The general claim about the Schauder property on p. 444
-- lacks a proof. The primal normalization invoked again on p. 451 is false:
-- close simple critical-line zeta zeros give jets at distance tending to zero,
-- so the corresponding biorthogonal vector norms are unbounded (ERRATA R5).

section BandProjections

attribute [local instance] instDualMeasurableSpaceSec3

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
      ∀ q, Tendsto (fun n ↦ P n q) atTop (𝓝 q) := by sorry

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

/-- Paper: Theorem 10.2.2.1, p. 446. The weighted theta closure is the common
kernel of all surviving strip evaluations.
Gap: The complementary projections of §9.3 exhaust the orthogonal of the
common kernel. Identifying this kernel with the geometric theta closure
requires a separate approximation in the strip norm. -/
theorem spectralStripJet_commonKernel (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice χ) {a α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) :
    let u : SpectralStripJetIndex χ a α s → W'(-α, α, s) := stripU(χ, hα, hs)
    JetKernel(a, stripI(hα), hs, u) := by sorry

/-- Paper: Theorem 10.2.2.1, p. 446. The individual strip jets admit
interpolants whose classes span densely in the geometric quotient.
Gap: Orthogonal exhaustion by the evaluation representers does not establish
interpolation and density of the biorthogonal vectors. -/
theorem spectralStripJet_denseInterpolants (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice χ) {a α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) :
    let J := SpectralStripJetIndex χ a α s
    let u : J → W'(-α, α, s) := stripU(χ, hα, hs)
    JetInterpolation(J, a, stripI(hα), hs, u) := by sorry

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
