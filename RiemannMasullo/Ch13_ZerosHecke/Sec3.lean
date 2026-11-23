module

public import RiemannMasullo.Ch12_TraceGeometric.Sec5
import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.AppB_AnalyticNT.Sec4b
import RiemannMasullo.AppD_SchwartzBruhat.Sec1c
import all RiemannMasullo.AppD_SchwartzBruhat.Sec2b
import all RiemannMasullo.AppD_SchwartzBruhat.Sec3b

/-! # The divisor of the Hecke L-function

Masullo, §13.3.1, p. 522. The two sides of the proposed trace formula are
continuous on the Mellin-jet test subspace. The printed equality and codimension
claim are recorded in `Sec3_Printed.lean`.
-/

@[expose] public noncomputable section

open Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 instFiniteCompletionUnitsLocallyCompactSec4b
  instNormOneIdeleClassMeasurableSec4b

variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "U𝔽" => PontryaginDual C𝔽
local notation "D𝔽" => BruhatCompactSupport C𝔽
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "ord(" χ ", " s ")" =>
  MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ s
local notation "sectionCharacters(" τ ")" => {χ : U𝔽 // ∀ t, χ (τ t) = 1}

-- TODO(paper-gap): §§13.1 and 13.2 are headings with no text on p. 522.
-- TODO(paper-gap): Footnote 1 to Theorem 13.3.1.1 says “Correct statement.” The
-- cited `traceFormula` uses a positive-width strip, full zero orders and tests
-- vanishing on the norm-one classes. The manuscript gives no derivation of the
-- changes to the zero weights, test space or local coefficients.

/-- Paper: (13.3.1.1), p. 522. The spectral multiplicity is the order of the
completed Hecke zero capped at the degree of the number field. -/
def criticalTraceMultiplicity (χ : U𝔽) (s : ℂ) (_hs : 0 < ord(χ, s)) : ℕ :=
  min (ord(χ, s)).toNat (Module.finrank ℚ F)

/-- Paper: (13.3.1.1), p. 522. A zero whose order exceeds the field degree is
counted with weight equal to the degree. -/
theorem criticalTraceMultiplicity_of_degree_le (χ : U𝔽) (s : ℂ) (hs : 0 < ord(χ, s))
    (_h : Module.finrank ℚ F ≤ (ord(χ, s)).toNat) :
    criticalTraceMultiplicity χ s hs = Module.finrank ℚ F := by
  unfold criticalTraceMultiplicity
  exact min_eq_right _h

local notation "momentIntegrand(" χ ", " k ", " φ ")" =>
  (fun g : C𝔽 ↦ (φ : D𝔽).val g * spectralZeroJet (F := F) χ 0 0 k g)

private theorem criticalTraceMoment_isLinearMap_integrable (χ : U𝔽) (k : ℕ) (φ : D𝔽) :
    Integrable (fun g : C𝔽 ↦ (φ : D𝔽).val g * spectralZeroJet (F := F) χ 0 0 k g) μ𝔽 := by
  have hφ : Continuous (φ : D𝔽).val :=
    continuous_schwartzBruhat
      (⟨φ.val, bruhatCompactSupport_mem_schwartz φ.property⟩ : SchwartzBruhat C𝔽)
  have hc : HasCompactSupport (φ : D𝔽).val := φ.property.2
  have hlog : Continuous (fun g : C𝔽 ↦ Real.log ((ideleClassNorm F g).val : ℝ)) :=
    ((NNReal.continuous_coe.comp (Units.continuous_val.comp
      (isProperMap_ideleClassNorm F).continuous))).log fun g ↦
        ne_of_gt (NNReal.coe_pos.mpr (Units.zero_lt _))
  have hj : Continuous (spectralZeroJet (F := F) χ 0 0 k) := by
    unfold spectralZeroJet
    exact (ideleClassNormTwist χ _).continuous.mul
      ((Complex.continuous_ofReal.comp hlog).pow k)
  exact (hφ.mul hj).integrable_of_hasCompactSupport (hc.mul_right)

/-- Paper: (13.3.1.2), p. 522. A fixed character and jet order give a linear
functional by integration against the character times a power of the log norm. -/
theorem criticalTraceMoment_isLinearMap (χ : U𝔽) (k : ℕ) :
    IsLinearMap ℂ (fun φ : D𝔽 ↦ ∫ g, momentIntegrand(χ, k, φ) g ∂μ𝔽) := by
  refine ⟨fun φ ψ ↦ ?_, fun c φ ↦ ?_⟩
  · have e : (fun g : C𝔽 ↦ ((φ + ψ : D𝔽)).val g * spectralZeroJet (F := F) χ 0 0 k g) =
        fun g ↦ φ.val g * spectralZeroJet (F := F) χ 0 0 k g +
          ψ.val g * spectralZeroJet (F := F) χ 0 0 k g := by
      ext g
      exact add_mul _ _ _
    simp only [e]
    exact integral_add (criticalTraceMoment_isLinearMap_integrable χ k φ)
      (criticalTraceMoment_isLinearMap_integrable χ k ψ)
  · have e : (fun g : C𝔽 ↦ ((c • φ : D𝔽)).val g * spectralZeroJet (F := F) χ 0 0 k g) =
        fun g ↦ c * (φ.val g * spectralZeroJet (F := F) χ 0 0 k g) := by
      ext g
      exact mul_assoc _ _ _
    simp only [e]
    exact integral_const_mul c _

/-- Paper: (13.3.1.2), p. 522. The test subspace is the common kernel of the
first `[F : ℚ]` log-norm moments for each unitary character trivial on the section.
Deviation: The degree bounds the jet orders in each character, with no finite
codimension imposed on the common kernel. -/
def criticalTraceTestSubmodule (τ : ℝ≥0ˣ →ₜ* C𝔽) : Submodule ℂ D𝔽 :=
  ⨅ (χ : sectionCharacters(τ)) (k : Fin (Module.finrank ℚ F)),
    ((criticalTraceMoment_isLinearMap χ.val k.val).mk' _).ker

/-- Paper: (13.3.1.2), p. 522. Membership in the test subspace is equivalent to
the printed Mellin-derivative conditions at `−i x₀(χ)` for all unitary characters.
The continuous norm section and the exponent along it are given explicitly. -/
theorem mem_criticalTraceTestSubmodule_iff (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (_hτ : RightInverse τ (ideleClassNorm F)) (φ : D𝔽) :
    φ ∈ criticalTraceTestSubmodule τ ↔
      ∀ (χ : U𝔽) (x : ℝ),
        (∀ t : ℝ≥0ˣ, (χ (τ t) : ℂ) = ((t.val : ℝ) : ℂ) ^ ((x : ℂ) * Complex.I)) →
        ∀ k : Fin (Module.finrank ℚ F),
          iteratedDeriv k.val (fun s : ℂ ↦
            ∫ t : ℝ≥0ˣ, (χ (τ t) : ℂ) * ((t.val : ℝ) : ℂ) ^ s *
              (∫ g : C₁, φ.val (τ t * g.val) * (χ g.val : ℂ)
                ∂normOneIdeleClassTamagawaMeasure F) ∂positiveRealHaar)
            (-((x : ℂ) * Complex.I)) = 0 := by sorry

open scoped NumberField.AdeleRing in
/-- The finite sign idele with real coordinate one gives a nontrivial involution. -/
private theorem criticalTrace_rat_sign :
    ∃ g : IdeleClassGroup (𝓞 ℚ) ℚ, g ≠ 1 ∧ g ^ 2 = 1 := by
  have hs : ((1, -1) : 𝔸[ℚ]) * (1, -1) = 1 :=
    Prod.ext (one_mul _) ((neg_mul_neg 1 1).trans (one_mul 1))
  let s : IdeleGroup (𝓞 ℚ) ℚ := ⟨(1, -1), (1, -1), hs, hs⟩
  let q := QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 ℚ) ℚ)
  refine ⟨q s, ?_, ?_⟩
  · intro h
    obtain ⟨r, hr⟩ := (QuotientGroup.eq_one_iff s).mp h
    have hval := (congrArg Units.val hr).trans (show s.val = (1, -1) from rfl)
    have hreal := congrArg (fun x : 𝔸[ℚ] ↦ x.1 Rat.infinitePlace) hval
    change algebraMap ℚ Rat.infinitePlace.Completion r.val = 1 at hreal
    have hr₁ : r.val = 1 := (algebraMap ℚ Rat.infinitePlace.Completion).injective
      (hreal.trans (map_one _).symm)
    let v : HeightOneSpectrum (𝓞 ℚ) :=
      Rat.HeightOneSpectrum.primesEquiv.symm ⟨3, Nat.prime_three⟩
    have hfinite := congrArg (fun x : 𝔸[ℚ] ↦ x.2 v) hval
    change algebraMap ℚ (v.adicCompletion ℚ) r.val = -1 at hfinite
    rw [hr₁, map_one] at hfinite
    have : (1 : ℚ) = -1 := (algebraMap ℚ (v.adicCompletion ℚ)).injective
      (by simpa only [map_neg, map_one] using hfinite)
    norm_num at this
  · rw [← map_pow, sq]
    exact (congrArg q (Units.ext hs)).trans (map_one q)

open scoped ContDiff in
/-- A nonnegative bump near one has nonzero moment against characters with positive
real part on its support. -/
private theorem criticalTrace_exists_nonzero_moments (χ : U𝔽) :
    ∃ φ : D𝔽, ∀ η : U𝔽, (∀ x, 0 < (χ x : ℂ).re → 0 < (η x : ℂ).re) →
      (∫ x, φ.val x * (η x : ℂ) ∂μ𝔽) ≠ 0 := by
  have hχ : Continuous (fun x ↦ (χ x : ℂ).re) :=
    Complex.continuous_re.comp (continuous_subtype_val.comp χ.continuous)
  obtain ⟨v, hc, hs, hv⟩ := schwartzBruhat_exists_local_unit
    (U := {x | 0 < (χ x : ℂ).re}) (isOpen_lt continuous_const hχ)
    (x := 1) (by simp [map_one])
  let p (z : ℂ) : ℂ := (z.re ^ 2 : ℝ)
  have hp : ContDiff ℝ (∞) p := Complex.ofRealCLM.contDiff.comp (Complex.reCLM.contDiff.pow 2)
  have hzero : p 0 = 0 := by simp [p]
  obtain ⟨f, hf⟩ := compact_schwartzBruhat_comp hc hp hzero
  have hfs : tsupport f.val ⊆ tsupport v.val := hf ▸ tsupport_comp_subset hzero _
  have hfc : HasCompactSupport f.val := hc.of_isClosed_subset (isClosed_tsupport _) hfs
  have hf₁ : f.val 1 = 1 := by rw [hf, comp_apply, hv.eq_of_nhds]; norm_num [p]
  refine ⟨⟨f.val, (mem_bruhatSmoothSubmodule_iff _).mpr (schwartzBruhat_isBruhatSmooth f), hfc⟩, fun η hη ↦ ?_⟩
  let G (x : C𝔽) := f.val x * (η x : ℂ)
  have hG : Continuous G :=
    (continuous_schwartzBruhat f).mul (continuous_subtype_val.comp η.continuous)
  have hGc : HasCompactSupport G := hfc.mul_right
  have hnonneg (x) : 0 ≤ (G x).re := by
    by_cases hx : x ∈ tsupport f.val
    · have he := hη x (hs (hfs hx))
      change 0 ≤ (f.val x * (η x : ℂ)).re
      rw [hf]
      simpa only [p, Function.comp_def, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero] using mul_nonneg (sq_nonneg (v.val x).re) he.le
    · have hz := image_eq_zero_of_notMem_tsupport hx
      simp [G, hz]
  have hpos := (Complex.continuous_re.comp hG).integral_pos_of_hasCompactSupport_nonneg_ne_zero
    (μ := μ𝔽) (hGc.comp_left Complex.zero_re) hnonneg (x := 1) (by simp [G, hf₁])
  intro he
  exact hpos.ne' ((integral_re (hG.integrable_of_hasCompactSupport hGc)).trans
    (congrArg Complex.re he))

/-- Paper: Theorem 13.3.1.1, p. 522. The rational Mellin-jet test subspace has
codimension at least two, as witnessed by the trivial character and the character
modulo four on the norm-one classes.
Deviation: This replaces the printed codimension one over `ℚ` by a lower bound. -/
theorem criticalTraceTestSubmodule_rat_codimension_ge_two
    (τ : ℝ≥0ˣ →ₜ* IdeleClassGroup (𝓞 ℚ) ℚ) (_hτ : RightInverse τ (ideleClassNorm ℚ)) :
    2 ≤ Module.rank ℂ (BruhatCompactSupport (IdeleClassGroup (𝓞 ℚ) ℚ) ⧸
      criticalTraceTestSubmodule τ) := by
  let g := criticalTrace_rat_sign.choose
  have hg : g ≠ 1 := criticalTrace_rat_sign.choose_spec.1
  have hg₂ : g ^ 2 = 1 := criticalTrace_rat_sign.choose_spec.2
  have hn : ideleClassNorm ℚ g = 1 := sq_eq_one.mp (by rw [← map_pow, hg₂, map_one])
  let ψ := (exists_pontryaginDual_apply_ne_one hg).choose
  have hψ : ψ g ≠ 1 := (exists_pontryaginDual_apply_ne_one hg).choose_spec
  let n : IdeleClassGroup (𝓞 ℚ) ℚ →ₜ* ℝ≥0ˣ :=
    ⟨ideleClassNorm ℚ, (isProperMap_ideleClassNorm ℚ).continuous⟩
  -- Retract onto the norm-one classes so the character is trivial on the section.
  let r : IdeleClassGroup (𝓞 ℚ) ℚ →ₜ* IdeleClassGroup (𝓞 ℚ) ℚ :=
    ContinuousMonoidHom.id _ / τ.comp n
  let χ : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ) := ψ.comp r
  have hr (x) : r x = x / τ (ideleClassNorm ℚ x) := rfl
  have hχτ (t) : χ (τ t) = 1 := by
    change ψ (r (τ t)) = 1
    rw [hr, _hτ t, div_self', map_one]
  have hχg : (χ g : ℂ) = -1 := by
    have he : ψ (r g) = ψ g := by rw [hr, hn, map_one, div_one]
    change (ψ (r g) : ℂ) = -1
    rw [he]
    have hsq : (ψ g : ℂ) ^ 2 = 1 := by
      rw [← Circle.coe_pow, ← map_pow, hg₂, map_one, Circle.coe_one]
    exact (sq_eq_one_iff.mp hsq).resolve_left (fun h ↦ hψ (Subtype.ext h))
  let f := (criticalTrace_exists_nonzero_moments χ).choose
  have hf := (criticalTrace_exists_nonzero_moments χ).choose_spec
  let f' : SchwartzBruhat (IdeleClassGroup (𝓞 ℚ) ℚ) :=
    ⟨f.val, bruhatCompactSupport_mem_schwartz f.property⟩
  let v := schwartzBruhatTranslate g f'
  let u : BruhatCompactSupport (IdeleClassGroup (𝓞 ℚ) ℚ) :=
    ⟨v.val, (mem_bruhatSmoothSubmodule_iff _).mpr (schwartzBruhat_isBruhatSmooth v),
      f.property.2.comp_homeomorph (Homeomorph.mulLeft g⁻¹)⟩
  let M (η : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)) :=
    (criticalTraceMoment_isLinearMap η 0).mk' _
  have hM (η) (w : BruhatCompactSupport (IdeleClassGroup (𝓞 ℚ) ℚ)) :
      M η w = ∫ x, w.val x * (η x : ℂ) ∂ideleClassTamagawaMeasure ℚ := by
    change (∫ x, w.val x * spectralZeroJet η 0 0 0 x ∂ideleClassTamagawaMeasure ℚ) = _
    simp only [spectralZeroJet_zero]
  have hMu (η) : M η u = (η g : ℂ) * M η f := by
    let μ := ideleClassTamagawaMeasure ℚ
    let integrand x := u.val x * (η x : ℂ)
    calc
      M η u = ∫ x, integrand x ∂μ := hM η u
      _ = ∫ x, integrand (g * x) ∂μ :=
        (integral_mul_left_eq_self (μ := μ) integrand g).symm
      _ = ∫ x, (η g : ℂ) * (f.val x * (η x : ℂ)) ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x ↦ by
          change v (g * x) * (η (g * x) : ℂ) = _
          rw [schwartzBruhatTranslate_apply_mul, map_mul, Circle.coe_mul, mul_left_comm]
      _ = (η g : ℂ) * (∫ x, f.val x * (η x : ℂ) ∂μ) := integral_const_mul _ _
      _ = (η g : ℂ) * M η f := congrArg ((η g : ℂ) * ·) (hM η f).symm
  let L := (M 1).prod (M χ)
  have hL : criticalTraceTestSubmodule τ ≤ LinearMap.ker L := by
    intro w hw
    let k : Fin (Module.finrank ℚ ℚ) := ⟨0, by simp⟩
    have hm (η : {η : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ) // ∀ t, η (τ t) = 1}) :
        M η.val w = 0 := by
      have hle : criticalTraceTestSubmodule τ ≤ (M η.val).ker :=
        iInf_le_of_le η (iInf_le _ k)
      exact hle hw
    exact LinearMap.mem_ker.mpr (Prod.ext (hm ⟨1, by simp⟩) (hm ⟨χ, hχτ⟩))
  let A := M 1 f
  let B := M χ f
  have hA : A ≠ 0 := by
    rw [show A = M 1 f from rfl, hM]
    exact hf 1 (by simp)
  have hB : B ≠ 0 := by
    rw [show B = M χ f from rfl, hM]
    exact hf χ (fun _ h ↦ h)
  have hLf : L f = (A, B) := rfl
  have hLu : L u = (A, -B) := by
    change (M 1 u, M χ u) = (A, -B)
    refine Prod.ext ((hMu 1).trans ?_) ((hMu χ).trans ?_)
    · change (1 : ℂ) * A = A
      exact one_mul A
    · exact (congrArg (· * B) hχg).trans (neg_one_mul B)
  let Q := (criticalTraceTestSubmodule τ).liftQ L hL
  have hQ : Surjective Q := by
    intro z
    let a := z.1
    let b := z.2
    let c := (a / A + b / B) / 2
    let d := (a / A - b / B) / 2
    refine ⟨(criticalTraceTestSubmodule τ).mkQ (c • f + d • u), ?_⟩
    change L (c • f + d • u) = z
    calc
      L (c • f + d • u) = L (c • f) + L (d • u) := L.map_add _ _
      _ = c • (A, B) + d • (A, -B) :=
        congrArg₂ (· + ·) ((L.map_smul c f).trans (congrArg (c • ·) hLf))
          ((L.map_smul d u).trans (congrArg (d • ·) hLu))
      _ = z := by
        apply Prod.ext
        · change c * A + d * A = a
          dsimp [c, d]
          field_simp [hA, hB]
          ring
        · change c * B + d * (-B) = b
          dsimp [c, d]
          field_simp [hA, hB]
          ring
  calc
    2 = Module.rank ℂ (ℂ × ℂ) := by rw [rank_prod', Module.rank_self]; norm_num
    _ ≤ _ := Q.rank_le_of_surjective hQ

local notation "lineZeros(" τ ")" =>
  {z : sectionCharacters(τ) × ℂ // 0 < ord(z.1.val, z.2) ∧ z.2.re = 1 / 2}
local notation "mellinAt(" φ ", " χ ", " s ")" =>
  (∫ g : C𝔽, (φ : D𝔽).val g * ideleClassNormTwist (F := F) χ s g ∂μ𝔽)
local notation "zeroTerm(" φ ", " z ")" =>
  ((criticalTraceMultiplicity (z).val.1.val (z).val.2 (z).property.1 : ℂ) *
    mellinAt(φ, (z).val.1.val, (z).val.2 - 1 / 2))

/-- Paper: Theorem 13.3.1.1, (13.3.1.3), p. 522. The capped zero sum over the
critical line converges and gives a continuous linear functional on the test subspace.
Deviation: A norm section lists each quasi-character once by a unitary character
trivial on the section and a complex norm exponent. -/
theorem criticalTraceSpectral_converges (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (_hτ : RightInverse τ (ideleClassNorm F)) :
    ∃ L : criticalTraceTestSubmodule τ →L[ℂ] ℂ,
      ∀ φ : criticalTraceTestSubmodule τ,
        HasSum (fun z : lineZeros(τ) ↦ zeroTerm(φ.val, z)) (L φ) := by
  classical
  let n : C𝔽 →ₜ* ℝ≥0ˣ := ⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩
  let ι : C₁ →ₜ* C𝔽 := ⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩
  let p : C𝔽 →ₜ* C𝔽 := ContinuousMonoidHom.id C𝔽 / τ.comp n
  have hp (x : C𝔽) : p x ∈ (ideleClassNorm F).ker := by
    change ideleClassNorm F (x / τ (ideleClassNorm F x)) = 1
    rw [map_div, _hτ, div_self']
  let r : C𝔽 →ₜ* C₁ := ⟨p.toMonoidHom.codRestrict _ hp, p.continuous.subtype_mk _⟩
  let χ (ω : PontryaginDual C₁) : U𝔽 := ω.comp r
  have hχ : IsSpectralBasepointChoice χ := by
    intro ω
    ext g : 1
    change ω (r g.val) = ω g
    apply congrArg ω
    apply Subtype.ext
    change g.val / τ (ideleClassNorm F g.val) = g.val
    rw [show ideleClassNorm F g.val = 1 from g.property, map_one, div_one]
  have hnorm (ω) (t : ℝ≥0ˣ) : χ ω (τ t) = 1 := by
    change ω (r (τ t)) = 1
    rw [show r (τ t) = 1 from Subtype.ext (by change τ t / τ (ideleClassNorm F (τ t)) = 1; rw [_hτ, div_self']), map_one]
  let E : PontryaginDual C₁ ≃ sectionCharacters(τ) :=
    { toFun := fun ω ↦ ⟨χ ω, hnorm ω⟩
      invFun := fun η ↦ η.val.comp ι
      left_inv := hχ
      right_inv := fun η ↦ by
        apply Subtype.ext
        ext x : 1
        change η.val (x / τ (ideleClassNorm F x)) = η.val x
        rw [map_div, η.property, div_one] }
  let point (t : ℝ) : ℂ := ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I
  have hpoint (w : ℂ) (hw : w.re = 1 / 2) : point w.im = w := by
    apply Complex.ext <;> simp [point, hw]
  have hdiv (η : U𝔽) (w : ℂ) := MeromorphicOn.divisor_apply
    (continuedCompletedHeckeL_spec η).1.meromorphicOn (mem_univ w)
  have ordpos (η : U𝔽) (w : ℂ) :
      0 < ord(η, w) ↔ 0 < meromorphicOrderAt (continuedCompletedHeckeL η) w := by
    obtain ⟨hL, heq⟩ := continuedCompletedHeckeL_spec η
    have htwo : meromorphicOrderAt (continuedCompletedHeckeL η) 2 ≠ ⊤ := by
      intro h
      have hp' : 0 < meromorphicOrderAt (continuedCompletedHeckeL η) 2 := by
        rw [h]; exact WithTop.coe_lt_top (0 : ℤ)
      have hb := completedHeckeL_continuation_zeros η _ hL heq (by norm_num : 0 < (2 : ℂ).re) hp'
      norm_num at hb
    have ht := hL.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
      isPreconnected_univ (mem_univ _) (mem_univ w) htwo
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp ht
    rw [hdiv, ← hk, WithTop.untop₀_coe]
    exact WithTop.coe_lt_coe.symm
  let J := {z : PontryaginDual C₁ × ℝ //
    0 < meromorphicOrderAt (continuedCompletedHeckeL (χ z.1)) (point z.2)}
  let e : J ≃ lineZeros(τ) :=
    { toFun := fun z ↦ ⟨(E z.val.1, point z.val.2),
          (ordpos _ _).mpr z.property, by simp [point]⟩
      invFun := fun z ↦ ⟨(E.symm z.val.1, z.val.2.im), by
          have h := (ordpos _ _).mp z.property.1
          have he : χ (E.symm z.val.1) = z.val.1.val := congrArg Subtype.val (E.apply_symm_apply z.val.1)
          rwa [he, hpoint _ z.property.2]⟩
      left_inv := fun z ↦ Subtype.ext (Prod.ext (E.symm_apply_apply _) (by simp [point]))
      right_inv := fun z ↦ Subtype.ext (Prod.ext (E.apply_symm_apply _) (hpoint _ z.property.2)) }
  let s : ℝ := 2 * (Module.finrank ℚ F : ℝ) + 1
  have hs : 1 < s := by
    have hd : (0 : ℝ) < Module.finrank ℚ F := by exact_mod_cast (Module.finrank_pos (R := ℚ) (M := F))
    dsimp only [s]; linarith
  have hc : ⌈(s - 1) / 2⌉₊ = Module.finrank ℚ F := by simp [s]
  obtain ⟨D, hD⟩ := spectralLineConvolution_trace_distribution (F := F) (1 / 2) hs
  refine ⟨D.comp (criticalTraceTestSubmodule τ).subtypeL, fun φ ↦ ?_⟩
  obtain ⟨T, hT, -⟩ := spectralLineConvolution_traceNorm_continuous (F := F) (1 / 2) hs
  change HasSum _ (D φ.val)
  rw [hD φ.val (T φ.val) (hT φ.val)]
  apply e.hasSum_iff.mp
  apply ((spectralLineConvolution_trace (F := F) (1 / 2) χ hχ hs φ.val (T φ.val) (hT φ.val)).2).congr_fun
  intro z
  simp only [Function.comp_apply, e, Equiv.coe_fn_mk, E, criticalTraceMultiplicity, hdiv,
    spectralBoundaryMultiplicity, hc]
  have hshift : point z.val.2 - 1 / 2 = ((0 : ℝ) : ℂ) + (z.val.2 : ℂ) * Complex.I := by
    push_cast [point]; ring
  rw [hshift, (spectralConvolution_mellin_integrable (F := F) φ.val (χ z.val.1) _).2]
  rfl

local notation "finiteTerm(" v ", " b ")" =>
  ((Real.log ((v : V).asIdeal.absNorm : ℝ) : ℂ) * finiteConnesWeilPrincipalValue v 1 b)
local notation "finiteUnitMass(" v ")" =>
  ((finiteLocalMultiplicativeTamagawaMeasure F (v : V)
    (HeightOneSpectrum.adicCompletionIntegers F v).units).toReal : ℂ)
local notation "archTests" => ((w : InfinitePlace F) → BruhatCompactSupport w.Completionˣ)
local notation "finiteTests" => ((v : V) → BruhatCompactSupport (v.adicCompletion F)ˣ)
local notation "restrictsAtInfinity(" a ", " φ ")" =>
  (∀ w u, ((a : archTests) w).val u = (φ : D𝔽).val (IdeleClassGroup.ofCompletion (𝓞 F) F w u))
local notation "restrictsAtFinite(" b ", " φ ")" =>
  (∀ v u, ((b : finiteTests) v).val u = (φ : D𝔽).val (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u))

/-- Paper: Theorem 13.3.1.1, (13.3.1.3)–(13.3.1.5), p. 522. The finite-place
series converges, and the polar terms minus the local principal values form a
continuous linear functional on the test subspace. The local tests are pulled back
along the maps from the local multiplicative groups to the idele classes. -/
theorem criticalTraceGeometric_converges (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (_hτ : RightInverse τ (ideleClassNorm F)) :
    ∃ L : criticalTraceTestSubmodule τ →L[ℂ] ℂ,
      ∀ φ : criticalTraceTestSubmodule τ,
        ∃ (a : archTests) (b : finiteTests),
          restrictsAtInfinity(a, φ.val) ∧ restrictsAtFinite(b, φ.val) ∧
          HasSum (fun v : V ↦ finiteTerm(v, b v))
            (mellinAt(φ.val, 1, -1 / 2) + mellinAt(φ.val, 1, 1 / 2) -
              (∑ w : InfinitePlace F, infiniteConnesWeilPrincipalValue w (a w)) - L φ) := by sorry

/-- Paper: Theorem 13.3.1.1, (13.3.1.3)–(13.3.1.5), p. 522. On the Mellin-jet
test subspace the full zero divisor pairs against the test by the idelic explicit formula.
Deviation: This is the restriction of `idelicExplicitFormula` to the jet subspace.
It sums all completed zeros with full orders and uses the norm-one Tamagawa volume and
the canonical local factors. The capped critical-line equality is refuted in `Sec3_Printed.lean`. -/
theorem hasSum_fullDivisor_on_criticalTraceTests (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (_hτ : RightInverse τ (ideleClassNorm F)) (φ : criticalTraceTestSubmodule τ) :
    let zeros := {z : sectionCharacters(τ) × ℂ // 0 < ord(z.1.val, z.2)}
    let classVolume := ((normOneIdeleClassTamagawaMeasure F univ).toReal : ℂ)
    ∃ (a : archTests) (b : finiteTests),
      restrictsAtInfinity(a, φ.val) ∧ restrictsAtFinite(b, φ.val) ∧
      Summable (fun v : V ↦ finiteTerm(v, b v) / finiteUnitMass(v)) ∧
      HasSum (fun z : zeros ↦ (ord(z.val.1.val, z.val.2) : ℂ) *
          mellinAt(φ.val, z.val.1.val, z.val.2 - 1 / 2))
        (mellinAt(φ.val, 1, -1 / 2) + mellinAt(φ.val, 1, 1 / 2) - classVolume *
          ((∑ w : InfinitePlace F, infiniteConnesWeilPrincipalValue w (a w)) +
            ∑' v : V, finiteTerm(v, b v) / finiteUnitMass(v))) := by sorry

-- TODO(paper-gap): The inference to the divisor statement cites “Theorem ??”
-- without identifying the theorem to be combined with Theorem 13.3.1.1.
-- TODO(paper-gap): Theorem 13.3.1.2 has only a title. Footnotes 2 and 3 ask for
-- the statement, proof, and an approximation by tests tending to e^(−s|log t|)
-- for Re(s) > 1.

end RiemannMasullo
