module

public import RiemannMasullo.Ch11_ShellStructure.Sec2a
public import RiemannMasullo.Ch10_TraceSpectral.Sec4a
public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec4
import all RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.Ch05_ThetaZSpaces.Sec2b
import all RiemannMasullo.AppC_LCTVS.Sec3a_part2
import RiemannMasullo.Ch09_HardySobolev.Sec3

import all RiemannMasullo.Ch07_SchauderBasesZeta.Sec1b

/-! # Sobolev Paley–Wiener levels and orbital nuclearity

Masullo, §§11.2.1–11.2.2, pp. 487–491. The stage parameter lists the finite
places, with every archimedean place included implicitly.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

set_option quotPrecheck false
set_option maxSynthPendingDepth 8
set_option Elab.async false

variable {F : Type*} [Field F] [NumberField F]

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 instSIdeleQuotientMeasurableSpaceSec1

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" =>
  (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "mₛ(" S ")" =>
  (⟨sIdeleQuotientNorm F S, (isProperMap_sIdeleQuotientNorm F S).continuous⟩ :
    SIdeleQuotient F S →ₜ* ℝ≥0ˣ)
local notation "logNorm(" m ")" => (fun g ↦ Real.log (((m) g).val : ℝ))
local notation "h₀" => (le_rfl (a := (0 : ℝ)))
local notation "W(" s ")" => CompactIntervalSobolev μ𝔽 (logNorm(m𝔽)) 0 0 s
local notation "Wω(" hs ", " ω ")" =>
  actionIsotype ((hardySobolevTranslation μ𝔽 m𝔽 0 0 _ h₀ hs).comp
    (ideleClassNorm F).ker.subtype) ω
local notation "ω(" χ ")" =>
  (χ : PontryaginDual C𝔽).comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ :
    C₁ →ₜ* C𝔽)
local notation "A(" hs ", " φ ")" => hardySobolevTestAction μ𝔽 m𝔽 0 0 _ h₀ hs φ
local notation "supportedAboveOne(" φ ")" =>
  (tsupport (φ : BruhatCompactSupport C𝔽).val ⊆ {g | 1 ≤ ((m𝔽 g).val : ℝ)})

section Levels

variable {S : Finset (HeightOneSpectrum (𝓞 F))} {s : ℝ} (hs : 0 ≤ s)

-- Use the base [-0, 0] of §10.4 for its geometric projection and cutoff.
local notation "hGeo" => (neg_nonpos.mpr h₀ |>.trans h₀)
local notation "GeoIsotype(" ω ")" =>
  actionIsotype ((hardySobolevTranslation μ𝔽 m𝔽 (-(0 : ℝ)) 0 s hGeo hs).comp
    (ideleClassNorm F).ker.subtype) ω
local notation "geoAction(" φ ")" => hardySobolevTestAction μ𝔽 m𝔽 (-(0 : ℝ)) 0 s hGeo hs φ

local notation "Zₛ" => sAdelePolarSubspace F S
local notation "J₁" => (sIdeleQuotientNorm F S).ker
local notation "band(" K ")" =>
  ({f : Zₛ | f.val ∈ sLocalPWTests (S := S) (T := S) le_rfl K} : Set Zₛ)
local notation "localWeightedTheta(" a ", " ω ", " f ")" =>
  modulationWeight (mₛ(S)) a (sLocalHomogeneousAdelicThetaLinearMap F S ω (f : Zₛ).val)
local notation "globalWeightedTheta(" a ", " ω ", " f ")" =>
  modulationWeight m𝔽 a (homogeneousAdelicTheta ω (sAdeleSchwartzToGlobal F S (f : Zₛ).val))

local notation "localWMeasure" => (sLocalQuotientTamagawaMeasure F S).withDensity
  (fun g ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (logNorm(mₛ(S)) g)))
local notation "globalWMeasure" => (μ𝔽).withDensity
  (fun g ↦ ENNReal.ofReal (intervalSobolevDensity (-(0 : ℝ)) 0 s (logNorm(m𝔽) g)))
local notation "GeoW" => Lp ℂ 2 globalWMeasure
local notation "LocalW" => Lp ℂ 2 localWMeasure

/-- Paper: (11.2.1.1) and (11.2.1.6), pp. 487–488.
Local polar-free tests yield Sobolev vectors at positive twist.
Deviation: Use the positive range of the local Sobolev embedding from §10.1. -/
theorem sLocalPWTheta_memLp {a : ℝ} (_ha : 0 < a) (ω : PontryaginDual J₁) (f : Zₛ) :
    MemLp (localWeightedTheta(a, ω, f)) 2 localWMeasure := by
  let : BorelSpace (SIdeleQuotient F S) := ⟨rfl⟩
  let μ := sLocalQuotientTamagawaMeasure F S
  let r (g : SIdeleQuotient F S) : ℝ := (mₛ(S) g).val
  let θ := sLocalHomogeneousAdelicThetaLinearMap F S ω f.val
  let t := max s 0
  let b := a / 2
  have hb : 0 < b := half_pos _ha
  have hbb : b + b = a := add_halves a
  have hr (g) : 0 < r g := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hc : Continuous r := NNReal.continuous_coe.comp (Units.continuous_val.comp (mₛ(S)).continuous)
  obtain ⟨j, -, -, hj⟩ := exists_sLocalHomogeneousThetaSobolevInclusion (F := F) (S := S)
    hb (le_refl b) (show 0 ≤ t from le_max_right _ _) hb ω
  let u := (j (Submodule.Quotient.mk f.val)).val.val
  have hi := (globalThetaSobolev_norm_aux μ r hr hc.measurable b b b t θ u (hj f.val).2).1
  rw [hbb] at hi
  let d (g : SIdeleQuotient F S) := intervalSobolevDensity 0 0 t (Real.log (r g))
  have hd (g) : 0 ≤ d g := by dsimp [d, intervalSobolevDensity]; positivity
  have hm : Measurable d := by dsimp [d, intervalSobolevDensity]; fun_prop
  let Z (g : SIdeleQuotient F S) : ℂ := ((r g ^ a : ℝ) : ℂ) * θ g
  have hZ : Continuous Z := (Complex.continuous_ofReal.comp (hc.rpow_const fun g ↦ Or.inl (hr g).ne')).mul θ.continuous
  have mem : MemLp Z 2 (μ.withDensity fun g ↦ ENNReal.ofReal (d g)) := by
    apply (memLp_two_iff_integrable_sq_norm hZ.aestronglyMeasurable).2
    apply (integrable_withDensity_iff_integrable_smul' (ENNReal.measurable_ofReal.comp hm)
      (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)).2
    refine hi.congr (.of_forall fun g ↦ ?_)
    change ‖θ g‖ ^ 2 * intervalSobolevDensity a a t (Real.log (r g)) =
      (ENNReal.ofReal (d g)).toReal • ‖Z g‖ ^ 2
    rw [ENNReal.toReal_ofReal (hd g), smul_eq_mul]
    simp only [Z, d, norm_mul, mul_pow, Complex.norm_real,
      Real.rpow_def_of_pos (hr g), Real.norm_of_nonneg (Real.exp_pos _).le]
    have he := globalThetaSobolev_norm_density a 0 0 t (Real.log (r g))
    simp only [add_zero] at he
    rw [← he, mul_comm (Real.log (r g)) a]
    ring
  apply mem.mono_measure (withDensity_mono (.of_forall fun g ↦ ?_))
  apply ENNReal.ofReal_le_ofReal
  unfold d intervalSobolevDensity
  apply mul_le_mul_of_nonneg_left _ (le_trans (Real.exp_pos _).le (le_max_left _ _))
  exact Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg (Real.log (r g))])
    (div_le_div_of_nonneg_right (le_max_left s 0) (by norm_num))

/-- Paper: (11.2.1.1) and (11.2.1.6), pp. 487–488.
Send a local polar-free test to its weighted homogeneous theta class.
Deviation: Use the positive local twist of the Sobolev embedding. -/
def sLocalPWThetaSobolevMap {a : ℝ} (ha : 0 < a) (ω : PontryaginDual J₁)
    (f : Zₛ) :=
  MemLp.toLp (localWeightedTheta(a, ω, f))
    (sLocalPWTheta_memLp (F := F) (S := S) (s := s) ha ω f)

private theorem sLocalPWThetaSobolevMap_apply_ae_of_withDensity {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {w : α → ℝ} (hm : AEMeasurable w μ) (hw : ∀ x, 0 < w x) {P : α → Prop}
    (h : ∀ᵐ x ∂(μ.withDensity fun x ↦ ENNReal.ofReal (w x)), P x) : ∀ᵐ x ∂μ, P x := by
  have := (withDensity_absolutelyContinuous' (μ := μ) (f := fun x ↦ ENNReal.ofReal (w x))
    hm.ennreal_ofReal (Filter.Eventually.of_forall fun x ↦ (ENNReal.ofReal_pos.2 (hw x)).ne'))
  exact this.ae_le h

private theorem sLocalPWThetaSobolevMap_apply_dens_pos (a b s t : ℝ) :
    0 < intervalSobolevDensity a b s t :=
  mul_pos (lt_max_of_lt_left (Real.exp_pos _)) (Real.rpow_pos_of_pos (by positivity) _)

private theorem sLocalPWThetaSobolevMap_apply_dens_meas (a b s : ℝ) :
    Measurable (intervalSobolevDensity a b s) := by
  unfold intervalSobolevDensity
  fun_prop

/-- Paper: (11.2.1.1) and (11.2.1.6), pp. 487–488.
The local Sobolev map is represented almost everywhere by the weighted homogeneous theta. -/
theorem sLocalPWThetaSobolevMap_apply {a : ℝ} (ha : 0 < a) (ω : PontryaginDual J₁) (f : Zₛ) :
    (sLocalPWThetaSobolevMap (F := F) (S := S) (s := s) ha ω f : SIdeleQuotient F S → ℂ) =ᵐ[sLocalQuotientTamagawaMeasure F S]
      localWeightedTheta(a, ω, f) := by
  have : OpensMeasurableSpace (SIdeleQuotient F S) := ⟨le_of_eq rfl⟩
  have hm : Measurable (fun g : SIdeleQuotient F S ↦ Real.log (((mₛ(S)) g).val : ℝ)) :=
    Real.measurable_log.comp ((measurable_coe_nnreal_real).comp
      ((Units.continuous_val.comp (mₛ(S)).continuous).measurable))
  exact sLocalPWThetaSobolevMap_apply_ae_of_withDensity
    ((sLocalPWThetaSobolevMap_apply_dens_meas 0 0 s).comp hm).aemeasurable
    (fun _ ↦ sLocalPWThetaSobolevMap_apply_dens_pos _ _ _ _) (MemLp.coeFn_toLp _)

/-- Paper: (11.2.1.2) and (11.2.1.7), pp. 487–488.
Globalized polar-free tests yield weighted Sobolev vectors.
Deviation: Use direct integer-indicator insertion as in the repaired §7.3.2. -/
theorem globalPWTheta_memLp (a : ℝ) (ω : PontryaginDual C₁) (f : Zₛ) :
    MemLp (globalWeightedTheta(a, ω, f)) 2 globalWMeasure := by
  let f₀ : adelePolarSubspace F := ⟨sAdeleSchwartzToGlobal F S f.val,
    sAdeleSchwartzToGlobal_mem_polarSubspace f⟩
  let x : globalPolarFreeThetaSubmodule (F := F) ω :=
    ⟨Submodule.Quotient.mk f₀.val, ⟨f₀.val, f₀.property, rfl⟩⟩
  obtain ⟨j, -, -, hj⟩ := exists_globalHomogeneousThetaSobolevInclusion
    (F := F) (a := a) hGeo (le_max_right s 0) ω
  have he := (hj f₀ x rfl).2
  have hv := (Lp.memLp (j x).val.val).ae_eq ((withDensity_absolutelyContinuous _ _).ae_le he)
  apply hv.mono_measure (withDensity_mono (Filter.Eventually.of_forall fun g ↦ ?_))
  apply ENNReal.ofReal_le_ofReal
  unfold intervalSobolevDensity
  apply mul_le_mul_of_nonneg_left _ (le_trans (Real.exp_pos _).le (le_max_left _ _))
  exact Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg (logNorm(m𝔽) g)])
    (div_le_div_of_nonneg_right (le_max_left s 0) (by norm_num))

/-- Paper: (11.2.1.2) and (11.2.1.7), pp. 487–488.
Insert a local polar-free test and take its weighted global homogeneous theta class.
Deviation: Use direct integer-indicator insertion as in the repaired §7.3.2. -/
def globalPWThetaSobolevMap (a : ℝ) (ω : PontryaginDual C₁) (f : Zₛ) :=
  MemLp.toLp (globalWeightedTheta(a, ω, f))
    (globalPWTheta_memLp (F := F) (S := S) (s := s) a ω f)

/-- Paper: (11.2.1.2) and (11.2.1.7), pp. 487–488.
The global Sobolev map is represented almost everywhere by the weighted homogeneous theta. -/
theorem globalPWThetaSobolevMap_apply (a : ℝ) (ω : PontryaginDual C₁) (f : Zₛ) :
    (globalPWThetaSobolevMap (F := F) (S := S) (s := s) a ω f : C𝔽 → ℂ) =ᵐ[μ𝔽]
      globalWeightedTheta(a, ω, f) := by
  have hm : Measurable (fun g : C𝔽 ↦ Real.log (((m𝔽) g).val : ℝ)) :=
    Real.measurable_log.comp ((measurable_coe_nnreal_real).comp
      ((Units.continuous_val.comp (m𝔽).continuous).measurable))
  exact sLocalPWThetaSobolevMap_apply_ae_of_withDensity
    ((sLocalPWThetaSobolevMap_apply_dens_meas (-(0 : ℝ)) 0 s).comp hm).aemeasurable
    (fun _ ↦ sLocalPWThetaSobolevMap_apply_dens_pos _ _ _ _) (MemLp.coeFn_toLp _)

/-- Paper: Definition 11.2.1.1(1) and (11.2.1.1), p. 487.
The local absolute level is the weighted Sobolev closure of homogeneous theta
from zero-moment tests whose Fourier transforms lie in the box of size Λ.
Deviation: Use a positive local twist so the weighted theta functions belong to L². -/
def sLocalAbsolutePWSobolev (_hs : 0 ≤ s) {a : ℝ} (ha : 0 < a) (ω : PontryaginDual J₁) (Λ : ℝ) :
    Submodule ℂ LocalW :=
  (Submodule.span ℂ (range fun f : band(sLocalPWBox S Λ) ↦
    sLocalPWThetaSobolevMap (F := F) (S := S) (s := s) ha ω f.val)).topologicalClosure

/-- Paper: Definition 11.2.1.1(1) and (11.2.1.1), p. 487.
A box-limited polar-free test gives its weighted homogeneous theta vector in the local level.
Deviation: Use the positive local twist of the repaired definition. -/
theorem sLocalAbsolutePWSobolev_mem {a : ℝ} (ha : 0 < a) (ω : PontryaginDual J₁) (Λ : ℝ)
    (f : Zₛ) (_hf : f ∈ band(sLocalPWBox S Λ)) :
    sLocalPWThetaSobolevMap (F := F) (S := S) (s := s) ha ω f ∈ sLocalAbsolutePWSobolev (F := F) (S := S) hs ha ω Λ := by
  exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨⟨f, _hf⟩, rfl⟩)

-- TODO(paper-gap): (11.2.1.2) leaves X free. The box parameter here is Λ,
-- as indicated by the comparison with Λ^|S| in the proof on p. 489.

/-- Paper: Definition 11.2.1.1(1) and (11.2.1.2), p. 487.
The global absolute level is the Sobolev closure of the weighted homogeneous
theta image of the box-limited polar-free tests.
Deviation: Use X = Λ as in the comparison on p. 489. Insert directly from S
with the integer indicators of §7.3.2. Factoring this insertion at S′
gives the same global tests and preserves the two zero moments. -/
def globalAbsolutePWSobolev (_hs : 0 ≤ s) (a : ℝ) (ω : PontryaginDual C₁) (Λ : ℝ) :
    Submodule ℂ GeoW :=
  (Submodule.span ℂ (range fun f : band(sLocalPWBox S Λ) ↦
    globalPWThetaSobolevMap (F := F) (S := S) (s := s) a ω f.val)).topologicalClosure

/-- Paper: Definition 11.2.1.1(1) and (11.2.1.2), p. 487.
An inserted box-limited polar-free test gives its weighted homogeneous theta
vector in the global level.
Deviation: Use X = Λ and the direct integer-indicator insertion. -/
theorem globalAbsolutePWSobolev_mem (a : ℝ) (ω : PontryaginDual C₁) (Λ : ℝ)
    (f : Zₛ) (_hf : f ∈ band(sLocalPWBox S Λ)) :
    globalPWThetaSobolevMap (F := F) (S := S) (s := s) a ω f ∈ globalAbsolutePWSobolev (F := F) (S := S) hs a ω Λ := by
  exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨⟨f, _hf⟩, rfl⟩)

local notation "ambientGeom(" a ")" => geometricProjection (F := F) a h₀ hs
local notation "onIsotype(" ω ", " T ")" =>
  (GeoIsotype(ω)).orthogonalProjectionOnto.comp ((T).comp (GeoIsotype(ω)).subtypeL)
local notation "absLevel(" a ", " ω ", " Λ ")" =>
  (globalAbsolutePWSobolev (F := F) (S := S) hs a ω Λ).comap (GeoIsotype(ω)).subtype

-- TODO(paper-gap): (11.2.1.3) gives the PW level as the codomain but
-- describes the projection using the undefined HS_{Λ₀}. The definition
-- below follows the declared codomain and the proof of Theorem 11.2.1.2.

/-- Paper: Definition 11.2.1.1(2) and (11.2.1.3), p. 488.
The absolute truncation is the orthogonal projection onto the global absolute level.
Deviation: Use the level of (11.2.1.2) for the undefined HS symbol and include
the projected vector back into the ambient isotype. -/
def absolutePWProjection (a : ℝ) (ω : PontryaginDual C₁) (Λ : ℝ) :
    GeoIsotype(ω) →L[ℂ] GeoIsotype(ω) :=
  letI : IsClosed (absLevel(a, ω, Λ) : Set GeoIsotype(ω)) :=
    (Submodule.isClosed_topologicalClosure _).preimage continuous_subtype_val
  (absLevel(a, ω, Λ)).starProjection

/-- Paper: Definition 11.2.1.1(2), p. 488.
The absolute projection fixes vectors in the absolute level. -/
theorem absolutePWProjection_apply_of_mem (a : ℝ) (ω : PontryaginDual C₁) (Λ : ℝ)
    (u : GeoIsotype(ω)) (_hu : u ∈ absLevel(a, ω, Λ)) :
    absolutePWProjection (F := F) (S := S) hs a ω Λ u = u := by
  letI : IsClosed (absLevel(a, ω, Λ) : Set GeoIsotype(ω)) :=
    (Submodule.isClosed_topologicalClosure _).preimage continuous_subtype_val
  exact Submodule.starProjection_eq_self_iff.mpr _hu

/-- Paper: Definition 11.2.1.1(3), p. 488.
Absolute condensation first projects onto the absolute level, then convolves
and projects onto the weighted theta subspace. -/
def absolutePWCondensation (a : ℝ) (ω : PontryaginDual C₁) (Λ : ℝ)
    (φ : BruhatCompactSupport C𝔽) (_hφ : supportedAboveOne(φ)) :
    GeoIsotype(ω) →L[ℂ] GeoIsotype(ω) :=
  (onIsotype(ω, (ambientGeom(a)).comp (geoAction(φ)))).comp
    (absolutePWProjection (F := F) (S := S) hs a ω Λ)

/-- Paper: Definition 11.2.1.1(3), p. 488.
On the absolute level, condensation acts by convolution followed by the geometric projection. -/
theorem absolutePWCondensation_apply_of_mem (a : ℝ) (ω : PontryaginDual C₁) (Λ : ℝ)
    (φ : BruhatCompactSupport C𝔽) (hφ : supportedAboveOne(φ))
    (u : GeoIsotype(ω)) (_hu : u ∈ absLevel(a, ω, Λ)) :
    absolutePWCondensation (F := F) (S := S) hs a ω Λ φ hφ u =
      onIsotype(ω, (ambientGeom(a)).comp (geoAction(φ))) u := by
  have h := absolutePWProjection_apply_of_mem (F := F) (S := S) hs a ω Λ u _hu
  simp only [absolutePWCondensation, ContinuousLinearMap.comp_apply, h]

local notation "PicTrivial" => Subsingleton (CommRing.Pic ((S : Set V).integer F))
local notation "Pgeom(" a ", " ω ")" => onIsotype(ω, ambientGeom(a))

/-- Paper: Theorem 11.2.1.2(1), p. 488.
The absolute projections converge strongly to the isotypic geometric projection.
Deviation: The support assumption on the test function is used in part (2). -/
theorem absolutePWProjection_tendsto (a : ℝ) (ω : PontryaginDual C₁)
    (_hω : NormOneCharacterUnramifiedOutside ω S) (_hPic : PicTrivial) (u : GeoIsotype(ω)) :
    Tendsto (fun Λ ↦ absolutePWProjection (F := F) (S := S) hs a ω Λ u) atTop (𝓝 (Pgeom(a, ω) u)) :=
  by sorry

variable {R ε : ℝ} {ρ : IdeleClassGroup (𝓞 F) F → ℝ}

local notation "cutoffConv(" a ", " ω ", " hρ ", " φ ")" =>
  onIsotype(ω, geometricTruncatedConvolution (F := F) a h₀ hs hρ φ)
local notation "productTraceClass(" T ", " P ")" =>
  (⟨(T).val * (P), mul_mem_nuclearEndomorphisms_right (P) (T)⟩ : nuclearEndomorphisms _)

-- At a fixed cutoff the uncompressed operator may have a different trace.
-- On theta inputs Q A Q = A Q, so cutoff condensation only needs the
-- trace class of Mρ A Q. Cutoff convolution Mρ A is already trace class
-- by §9.3.3 (a larger smooth cutoff can be chosen to cover tsupport ρ).

/-- Every cutoff is absorbed by a larger cutoff satisfying the inner-band condition. -/
private theorem exists_nuclear_geometricPWRestriction_cover
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (m : G →ₜ* ℝ≥0ˣ) (R ε : ℝ) (ρ : G → ℝ) (hρ : IsModulatedCutoff m R ε ρ) :
    ∃ (L d : ℝ) (χ : G → ℝ), IsModulatedCutoff m L d χ ∧
      (0 < L⁻¹ + d ∧ L⁻¹ + d < L - d) ∧ ∀ x, ρ x * χ x = ρ x := by
  let L := R + 2
  let d := L⁻¹ / 4
  have hL : 2 < L := by dsimp [L]; linarith [hρ.radius_pos]
  have hLp : 0 < L := by linarith
  have hd : 0 < d := by dsimp [d]; positivity
  have hdlt : d < L⁻¹ := by dsimp [d]; nlinarith [inv_pos.mpr hLp]
  have hinv : L⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hdsmall : d < 1 / 2 := by dsimp [d]; linarith
  have hplateau : 1 < L - d := by linarith
  have hprod : 1 ≤ (L⁻¹ + d) * (L - d) := by
    have hh := mul_nonneg hd.le (show 0 ≤ L - L⁻¹ - d by linarith)
    nlinarith [inv_mul_cancel₀ hLp.ne']
  let B : ContDiffBump (0 : ℝ) :=
    ⟨Real.log (L - d), Real.log L, Real.log_pos hplateau,
      Real.log_lt_log (by linarith) (by linarith)⟩
  let r (x : G) : ℝ := (m x).val
  have hr : Continuous r := NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)
  have hpos (x : G) : 0 < r x := NNReal.coe_pos.mpr (Units.zero_lt _)
  let χ (x : G) := B (Real.log (r x))
  have h1 : χ 1 = 1 := by
    apply B.one_of_mem_closedBall
    simp [r, B.rIn_pos.le]
  have hcut : IsModulatedCutoff m L d χ := by
    refine ⟨hLp, hd, by linarith, by linarith, fun _ ↦ B.nonneg,
      fun x ↦ (abs_of_nonneg (B.nonneg (x := Real.log (r x)))) ▸ B.le_one,
      ?_, ?_, ?_, ?_, ?_⟩
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
      change L⁻¹ ≤ r x ∧ r x ≤ L
      rw [← Real.log_le_log_iff (inv_pos.mpr hLp) (hpos x), Real.log_inv,
        ← Real.log_le_log_iff (hpos x) hLp]
      exact ⟨hl.le, hu.le⟩
    · intro x hx
      apply B.one_of_mem_closedBall
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le]
      change -Real.log (L - d) ≤ _ ∧ _ ≤ Real.log (L - d)
      rw [← Real.log_inv, Real.log_le_log_iff (inv_pos.mpr (by linarith)) (hpos x),
        Real.log_le_log_iff (hpos x) (by linarith)]
      change L⁻¹ + d ≤ r x ∧ r x ≤ L - d at hx
      exact ⟨((inv_le_iff_one_le_mul₀ (by linarith : 0 < L - d)).mpr hprod).trans hx.1, hx.2⟩
  refine ⟨L, d, χ, hcut, ⟨by positivity, by linarith⟩, ?_⟩
  intro x
  by_cases hx : ρ x = 0
  · simp [hx]
  have hband := hρ.support_subset (subset_tsupport ρ (mem_support.mpr hx))
  have hR : R ≤ L - d := by dsimp [L] at *; linarith
  have hχ : χ x = 1 := by
    apply B.one_of_mem_closedBall
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le]
    change -Real.log (L - d) ≤ _ ∧ _ ≤ Real.log (L - d)
    rw [← Real.log_inv, Real.log_le_log_iff (inv_pos.mpr (by linarith)) (hpos x),
      Real.log_le_log_iff (hpos x) (by linarith)]
    exact ⟨(inv_anti₀ hρ.radius_pos hR).trans hband.1, hband.2.trans hR⟩
  rw [hχ, mul_one]
/-- Pointwise absorption of cutoff symbols gives absorption of their L² multipliers. -/
private theorem exists_nuclear_geometricPWRestriction_absorb
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (m : G →ₜ* ℝ≥0ˣ) (ν : Measure G) (R ε L d : ℝ) (ρ χ : G → ℝ)
    (hρ : IsModulatedCutoff m R ε ρ) (hχ : IsModulatedCutoff m L d χ)
    (hprod : ∀ x, ρ x * χ x = ρ x) :
    (modulatedCutoffOperator m ν hρ).comp (modulatedCutoffOperator m ν hχ) =
      modulatedCutoffOperator m ν hρ := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [modulatedCutoffOperator_apply m ν hρ (modulatedCutoffOperator m ν hχ u),
    modulatedCutoffOperator_apply m ν hχ u, modulatedCutoffOperator_apply m ν hρ u] with x hx hx' hy
  change modulatedCutoffOperator m ν hρ (modulatedCutoffOperator m ν hχ u) x = modulatedCutoffOperator m ν hρ u x
  rw [hx, hx', hy, ← mul_assoc, ← Complex.ofReal_mul, hprod]
/-- An admissible cutoff followed by Hardy–Sobolev convolution is nuclear. -/
private theorem exists_nuclear_geometricPWRestriction_admissible
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m) (hms : Surjective m)
    (a b s : ℝ) (hab : a ≤ b) (hs : 0 ≤ s) (φ : BruhatCompactSupport G)
    (L d : ℝ) (χ : G → ℝ) (hχ : IsModulatedCutoff m L d χ)
    (hband : 0 < L⁻¹ + d ∧ L⁻¹ + d < L - d) :
    IsNuclearOperator ((modulatedCutoffOperator m
      (μ.withDensity (fun x ↦ ENNReal.ofReal (intervalSobolevDensity a b s (Real.log ((m x).val : ℝ))))) hχ).comp
      (hardySobolevTestAction μ m a b s hab hs φ)) := by
  have hφs : IsBruhatSmooth φ.val := (mem_bruhatSmoothSubmodule_iff _).mp φ.property.1
  have hc := continuous_of_bruhatSmooth hφs
  have hb := hc.bounded_above_of_compact_support (show HasCompactSupport φ.val from φ.property.2)
  obtain ⟨hbig, _, _⟩ := truncatedHardySobolevConvolution_trace μ m a b s hab hs φ.val
    hc.aemeasurable φ.property.2 hb hm hms hφs hχ hband
  have hconv := hardySobolevConvolution_eq_testAction μ m a b s hab hs φ hc.aemeasurable hb
  exact (congrArg (fun U ↦ IsNuclearOperator ((modulatedCutoffOperator m
      (μ.withDensity (fun x ↦ ENNReal.ofReal (intervalSobolevDensity a b s (Real.log ((m x).val : ℝ))))) hχ).comp U)) hconv).mp hbig

/-- Bounded precomposition and postcomposition preserve nuclearity between Hilbert spaces. -/
private theorem exists_nuclear_geometricPWRestriction_compress
    (H J : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]
    (A : H →L[ℂ] H) (hA : IsNuclearOperator A) (S : J →L[ℂ] H) (R : H →L[ℂ] J) :
    IsNuclearOperator (R.comp (A.comp S)) := by
  obtain ⟨c, φ, y, hc, hφ, hy, hsum⟩ := (isNuclearOperator_iff_isBanachNuclear A).mp hA
  let pre := (ContinuousLinearMap.compL ℂ J H ℂ).flip S
  apply (isNuclearOperator_iff_isBanachNuclear _).mpr
  refine ⟨c, (fun n ↦ (φ n).comp S), R ∘ y, hc, ?_, ?_, ?_⟩
  · exact (pre.continuous.tendsto' 0 0 (map_zero pre)).comp hφ
  · exact (R.continuous.tendsto' 0 0 (map_zero R)).comp hy
  · intro x
    simpa only [map_smul, Function.comp_apply, ContinuousLinearMap.comp_apply] using R.hasSum (hsum (S x))
/-- A vector fixed by a compressed orthogonal projector is fixed by the ambient projector. -/
private theorem exists_nuclear_geometricPWRestriction_fixed
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (I K : Submodule ℂ H) [CompleteSpace I] [CompleteSpace K] (u : I)
    (hu : I.orthogonalProjectionOnto (K.starProjection (u : H)) = u) :
    K.starProjection (u : H) = u := by
  have hi := congrArg (fun v : I ↦ RCLike.re (inner ℂ v u)) hu
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right,
    K.re_inner_starProjection_eq_normSq] at hi
  have hnorm : ‖K.starProjection (u : H)‖ = ‖(u : H)‖ := by
    have hs : ‖K.starProjection (u : H)‖ ^ 2 = ‖(u : H)‖ ^ 2 := by
      simpa only [Submodule.starProjection_apply, Submodule.norm_coe, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.ofReal_re] using hi
    nlinarith [norm_nonneg (K.starProjection (u : H)), norm_nonneg (u : H)]
  exact K.starProjection_eq_self_iff.mpr ((K.mem_iff_norm_starProjection (u : H)).mpr hnorm)
/-- The two cutoff composition orders agree on inputs fixed by the compressed geometric projector. -/
private theorem exists_nuclear_geometricPWRestriction_agree
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (I K : Submodule ℂ H) [CompleteSpace I] [CompleteSpace K]
    (M A : H →L[ℂ] H)
    (hAK : K.starProjection.comp (A.comp K.starProjection) = A.comp K.starProjection)
    (P : I →L[ℂ] I)
    (hP : (I.orthogonalProjectionOnto.comp (K.starProjection.comp I.subtypeL)) * P = P) :
    (I.orthogonalProjectionOnto.comp (M.comp (A.comp (K.starProjection.comp I.subtypeL)))) * P =
      (I.orthogonalProjectionOnto.comp (M.comp (K.starProjection.comp (A.comp I.subtypeL)))) * P := by
  apply ContinuousLinearMap.ext
  intro u
  have hfix := congrArg (fun U : I →L[ℂ] I ↦ U u) hP
  have hp : K.starProjection (P u : H) = P u := exists_nuclear_geometricPWRestriction_fixed H I K (P u) hfix
  have ha := congrArg (fun U : H →L[ℂ] H ↦ U (P u)) hAK
  change K.starProjection (A (K.starProjection (P u : H))) = A (K.starProjection (P u : H)) at ha
  rw [hp] at ha
  change I.orthogonalProjectionOnto (M (A (K.starProjection (P u : H)))) = I.orthogonalProjectionOnto (M (K.starProjection (A (P u : H))))
  rw [hp, ha]


/-- Paper: Theorems 11.2.1.2(2) and 11.2.1.4(2), pp. 488–489.
The cutoff geometric restriction is trace class on the chosen isotype.
It agrees with cutoff geometric convolution after any map into theta.
Deviation: Use the right-compressed operator for the corrected limits. -/
theorem exists_nuclear_geometricPWRestriction (a : ℝ) (ω : PontryaginDual C₁)
    (φ : BruhatCompactSupport C𝔽) (hρ : IsModulatedCutoff m𝔽 R ε ρ) :
    ∃ T : nuclearEndomorphisms GeoIsotype(ω),
      T.val = onIsotype(ω, geometricRestriction (F := F) a h₀ hs hρ φ) ∧
      ∀ P : GeoIsotype(ω) →L[ℂ] GeoIsotype(ω), Pgeom(a, ω) * P = P →
        T.val * P = cutoffConv(a, ω, hρ, φ) * P := by
  have hcover : ∃ (L d : ℝ) (χ : C𝔽 → ℝ), IsModulatedCutoff m𝔽 L d χ ∧
      (0 < L⁻¹ + d ∧ L⁻¹ + d < L - d) ∧ ∀ x, ρ x * χ x = ρ x := by
    with_unfolding_all exact exists_nuclear_geometricPWRestriction_cover C𝔽 m𝔽 R ε ρ hρ
  obtain ⟨L, d, χ, hχ, hband, hprod⟩ := hcover
  let H := GeoW
  let I : Submodule ℂ H := GeoIsotype(ω)
  let K : Submodule ℂ H := globalThetaSobolev F a hGeo hs
  let M : H →L[ℂ] H := by with_unfolding_all exact modulatedCutoffOperator m𝔽 globalWMeasure hρ
  let A : H →L[ℂ] H := by with_unfolding_all exact geoAction(φ)
  letI : CompleteSpace I := by with_unfolding_all exact (instClosedSpectralIsotypeSec2 (F := F) hGeo hs ω).completeSpace_coe
  let N : H →L[ℂ] H := by with_unfolding_all exact modulatedCutoffOperator m𝔽 globalWMeasure hχ
  have hn : IsNuclearOperator (N.comp A) := by
    with_unfolding_all
      exact exists_nuclear_geometricPWRestriction_admissible C𝔽 μ𝔽 m𝔽
        ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
        (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.2.2.2.1 (-(0 : ℝ)) 0 s hGeo hs φ L d χ hχ hband
  have habsorb : M.comp N = M := exists_nuclear_geometricPWRestriction_absorb C𝔽 m𝔽 globalWMeasure R ε L d ρ χ hρ hχ hprod
  have hsmall : IsNuclearOperator (M.comp A) := by
    have hh := mul_mem_nuclearEndomorphisms_left M (⟨N.comp A, hn⟩ : nuclearEndomorphisms H)
    change IsNuclearOperator (M.comp (N.comp A)) at hh
    rwa [← ContinuousLinearMap.comp_assoc, habsorb] at hh
  let U : H →L[ℂ] H := M.comp (A.comp K.starProjection)
  have hU : IsNuclearOperator U := mul_mem_nuclearEndomorphisms_right K.starProjection
    (⟨M.comp A, hsmall⟩ : nuclearEndomorphisms H)
  have hnI := exists_nuclear_geometricPWRestriction_compress H I U hU I.subtypeL I.orthogonalProjectionOnto
  let T : nuclearEndomorphisms I := ⟨I.orthogonalProjectionOnto.comp (U.comp I.subtypeL), hnI⟩
  refine ⟨T, ?_, ?_⟩
  · with_unfolding_all rfl
  · intro P hP
    have hAK : K.starProjection.comp (A.comp K.starProjection) = A.comp K.starProjection := by
      with_unfolding_all exact geometricProjection_convolution_geometricProjection (F := F) a h₀ hs φ
    with_unfolding_all exact exists_nuclear_geometricPWRestriction_agree H I K M A hAK P hP

local notation "nuclearRestriction(" a ", " ω ", " hρ ", " φ ")" =>
  (exists_nuclear_geometricPWRestriction (F := F) hs a ω φ hρ).choose

/-- Uniformly bounded self-adjoint strongly null families kill nuclear operators on the right in trace norm. -/
private theorem absolutePWCondensation_traceNorm_tendsto_null
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Q : ℝ → H →L[ℂ] H) (hQ : ∀ x, Tendsto (fun i ↦ Q i x) atTop (𝓝 0))
    (hQa : ∀ i, (Q i).adjoint = Q i) (hQc : ∀ i x, ‖Q i x‖ ≤ 2 * ‖x‖)
    (T : nuclearEndomorphisms H) :
    Tendsto (fun i ↦ traceNorm ⟨T.val * Q i, mul_mem_nuclearEndomorphisms_right (Q i) T⟩)
      atTop (𝓝 0) := by
  obtain ⟨c, φ, y, hc, hφ, hy, hT⟩ := (isNuclearOperator_iff_isBanachNuclear T.val).mp T.property
  let u (n : ℕ) := (InnerProductSpace.toDual ℂ H).symm (φ n)
  have hu (n : ℕ) : ‖u n‖ = ‖φ n‖ := (InnerProductSpace.toDual ℂ H).symm.norm_map _
  let cost (i : ℝ) (n : ℕ) := ‖c n‖ * (‖Q i (u n)‖ * ‖y n‖)
  let bound (n : ℕ) := 2 * (‖c n‖ * (‖φ n‖ * ‖y n‖))
  have hcost_nonneg (i : ℝ) (n : ℕ) : 0 ≤ cost i n := by dsimp [cost]; positivity
  have hbound (i : ℝ) (n : ℕ) : ‖cost i n‖ ≤ bound n := by
    rw [Real.norm_of_nonneg (hcost_nonneg i n)]
    have hh := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right ((hQc i (u n)).trans_eq (congrArg (2 * ·) (hu n))) (norm_nonneg (y n)))
      (norm_nonneg (c n))
    dsimp only [cost, bound]
    nlinarith
  have hs : Summable bound := by
    obtain ⟨C, hC, hφC⟩ := (Metric.isBounded_range_of_tendsto φ hφ).exists_pos_norm_le
    obtain ⟨D, _, hyD⟩ := (Metric.isBounded_range_of_tendsto y hy).exists_pos_norm_le
    apply Summable.mul_left 2
    refine (hc.mul_right (C * D)).of_norm_bounded fun n ↦ ?_
    rw [Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul (hφC _ (mem_range_self n)) (hyD _ (mem_range_self n))
        (norm_nonneg _) hC.le) (norm_nonneg _)
  have hlim : Tendsto (fun i ↦ ∑' n, cost i n) atTop (𝓝 0) := by
    have hterm (n : ℕ) : Tendsto (fun i ↦ cost i n) atTop (𝓝 0) := by
      simpa [cost] using ((hQ (u n)).norm.mul_const ‖y n‖).const_mul ‖c n‖
    simpa only [tsum_zero] using
      tendsto_tsum_of_dominated_convergence hs hterm (Eventually.of_forall hbound)
  let : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
  refine squeeze_zero (fun _ ↦ (traceNorm_normedSpaceCore (H := H)).toCore.norm_nonneg _)
    ?_ hlim
  intro i
  let ψ (n : ℕ) : StrongDual ℂ H := c n • innerSL ℂ (Q i (u n))
  have hψ (n : ℕ) : ‖ψ n‖ * ‖y n‖ = cost i n := by
    simp only [ψ, cost, norm_smul, innerSL_apply_norm, mul_assoc]
  simp_rw [← hψ]
  refine traceNorm_le_of_rankOne_series _ ψ y
    ((hs.of_norm_bounded (hbound i)).congr fun n ↦ (hψ n).symm) fun x ↦ ?_
  have heval (n : ℕ) : ψ n x = c n * φ n (Q i x) := by
    have hinner := (Q i).adjoint_inner_left x (u n)
    rw [hQa] at hinner
    simp only [ψ, smul_apply, smul_eq_mul, innerSL_apply_apply, hinner, u, InnerProductSpace.toDual_symm_apply]
  simpa [heval, mul_apply_eq_comp] using hT (Q i x)
/-- A compressed ambient projection preserves the compressing subspace if it is a strong limit of orthogonal projections. -/
private theorem absolutePWCondensation_traceNorm_tendsto_preserves
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (I K : Submodule ℂ H) [CompleteSpace I] [CompleteSpace K]
    (levels : ℝ → Submodule ℂ I) [∀ i, CompleteSpace (levels i)]
    (hlim : ∀ u : I, Tendsto (fun i ↦ (levels i).starProjection u) atTop
      (𝓝 (I.orthogonalProjectionOnto (K.starProjection u)))) (u : I) :
    K.starProjection u ∈ I := by
  let w := K.starProjection (u : H)
  let z := I.orthogonalProjectionOnto w
  have hiC : Tendsto (fun i ↦ inner ℂ ((levels i).starProjection u) u) atTop (𝓝 (inner ℂ z u)) :=
    (hlim u).inner tendsto_const_nhds
  have hi := (RCLike.continuous_re.tendsto _).comp hiC
  have heq (i : ℝ) : RCLike.re (inner ℂ ((levels i).starProjection u) u) = ‖(levels i).starProjection u‖ ^ 2 := by
    with_unfolding_all simpa only [Submodule.starProjection_apply, Submodule.norm_coe] using (levels i).re_inner_starProjection_eq_normSq u
  have hn : Tendsto (fun i ↦ RCLike.re (inner ℂ ((levels i).starProjection u) u)) atTop (𝓝 (‖z‖ ^ 2)) := by
    simpa only [heq] using (hlim u).norm.pow 2
  have hz : RCLike.re (inner ℂ z u) = ‖z‖ ^ 2 := tendsto_nhds_unique hi hn
  have hw : RCLike.re (inner ℂ w (u : H)) = ‖w‖ ^ 2 := by
    with_unfolding_all simpa only [w, Submodule.starProjection_apply, Submodule.norm_coe] using K.re_inner_starProjection_eq_normSq (u : H)
  have hnorm : ‖I.starProjection w‖ = ‖w‖ := by
    have hh : RCLike.re (inner ℂ z u) = RCLike.re (inner ℂ w (u : H)) := by
      rw [show z = I.orthogonalProjectionOnto w from rfl, Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]
    have hsq : ‖I.starProjection w‖ ^ 2 = ‖w‖ ^ 2 := by
      change ‖z‖ ^ 2 = ‖w‖ ^ 2
      linarith
    nlinarith [norm_nonneg (I.starProjection w), norm_nonneg w]
  exact (I.mem_iff_norm_starProjection w).mpr hnorm
/-- Strong convergence of orthogonal projections preserves a right-supported nuclear operator in trace norm. -/
private theorem absolutePWCondensation_traceNorm_tendsto_projection
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (levels : ℝ → Submodule ℂ H) [∀ i, CompleteSpace (levels i)] (R : H →L[ℂ] H)
    (hlim : ∀ u, Tendsto (fun i ↦ (levels i).starProjection u) atTop (𝓝 (R u)))
    (T : nuclearEndomorphisms H) (hTR : T.val * R = T.val) :
    Tendsto (fun i ↦ traceNorm
      (⟨T.val * (levels i).starProjection, mul_mem_nuclearEndomorphisms_right (levels i).starProjection T⟩ - T))
      atTop (𝓝 0) := by
  have hRa : R.adjoint = R := by
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_right ℂ
    intro y
    rw [ContinuousLinearMap.adjoint_inner_left]
    have hl : Tendsto (fun i ↦ inner ℂ x ((levels i).starProjection y)) atTop (𝓝 (inner ℂ x (R y))) := tendsto_const_nhds.inner (hlim y)
    have hr : Tendsto (fun i ↦ inner ℂ ((levels i).starProjection x) y) atTop (𝓝 (inner ℂ (R x) y)) := (hlim x).inner tendsto_const_nhds
    have heq : (fun i ↦ inner ℂ x ((levels i).starProjection y)) = (fun i ↦ inner ℂ ((levels i).starProjection x) y) := by
      funext i
      exact (Submodule.inner_starProjection_left_eq_right (levels i) x y).symm
    rw [heq] at hl
    exact tendsto_nhds_unique hl hr
  have hR (x : H) : ‖R x‖ ≤ ‖x‖ :=
    le_of_tendsto' ((hlim x).norm) (fun i ↦ (levels i).norm_starProjection_apply_le x)
  let Q (i : ℝ) := (levels i).starProjection - R
  have hQ (x : H) : Tendsto (fun i ↦ Q i x) atTop (𝓝 0) := by
    simpa [Q] using (hlim x).sub (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ R x) atTop (𝓝 (R x)))
  have hQa (i : ℝ) : (Q i).adjoint = Q i := by
    simp only [Q, map_sub, (isSelfAdjoint_starProjection (levels i)).adjoint_eq, hRa]
  have hQc (i : ℝ) (x : H) : ‖Q i x‖ ≤ 2 * ‖x‖ := by
    exact (norm_sub_le ((levels i).starProjection x) (R x)).trans (by linarith [(levels i).norm_starProjection_apply_le x, hR x])
  have hh := absolutePWCondensation_traceNorm_tendsto_null H Q hQ hQa hQc T
  apply hh.congr'
  filter_upwards with i
  apply congrArg traceNorm
  apply Subtype.ext
  change T.val * ((levels i).starProjection - R) = T.val * (levels i).starProjection - T.val
  rw [mul_sub, hTR]
/-- The right-compressed nuclear operator is recovered by strongly convergent compressed projections. -/
private theorem absolutePWCondensation_traceNorm_tendsto_compressed
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (I K : Submodule ℂ H) [CompleteSpace I] [CompleteSpace K]
    (A : H →L[ℂ] H) (levels : ℝ → Submodule ℂ I) [∀ i, CompleteSpace (levels i)]
    (hlim : ∀ u : I, Tendsto (fun i ↦ (levels i).starProjection u) atTop
      (𝓝 (I.orthogonalProjectionOnto (K.starProjection u))))
    (T : nuclearEndomorphisms I)
    (hTval : T.val = I.orthogonalProjectionOnto.comp (A.comp (K.starProjection.comp I.subtypeL))) :
    Tendsto (fun i ↦ traceNorm
      (⟨T.val * (levels i).starProjection, mul_mem_nuclearEndomorphisms_right (levels i).starProjection T⟩ - T))
      atTop (𝓝 0) := by
  let R : I →L[ℂ] I := I.orthogonalProjectionOnto.comp (K.starProjection.comp I.subtypeL)
  apply absolutePWCondensation_traceNorm_tendsto_projection I levels R hlim T
  rw [hTval]
  apply ContinuousLinearMap.ext
  intro u
  change I.orthogonalProjectionOnto (A (K.starProjection (I.starProjection (K.starProjection (u : H))))) = I.orthogonalProjectionOnto (A (K.starProjection (u : H)))
  rw [I.starProjection_eq_self_iff.mpr (absolutePWCondensation_traceNorm_tendsto_preserves H I K levels hlim u),
    K.starProjection_eq_self_iff.mpr (K.starProjection_apply_mem (u : H))]


/-- Paper: Theorem 11.2.1.2(2) and (11.2.1.4), p. 488.
Right multiplication of cutoff geometric convolution by the absolute projections
converges in trace norm.
Deviation: For the fixed cutoff keep the right geometric projection in the
limit. Use the trace class of cutoff convolution on the geometric range. -/
theorem absolutePWCondensation_traceNorm_tendsto (a : ℝ) (ω : PontryaginDual C₁)
    (_hω : NormOneCharacterUnramifiedOutside ω S) (_hPic : PicTrivial)
    (φ : BruhatCompactSupport C𝔽) (_hφ : supportedAboveOne(φ))
    (hρ : IsModulatedCutoff m𝔽 R ε ρ) :
    let T := nuclearRestriction(a, ω, hρ, φ)
    Tendsto (fun Λ ↦ traceNorm
      (productTraceClass(T, absolutePWProjection (F := F) (S := S) hs a ω Λ) -
        T)) atTop (𝓝 0) := by
  intro T
  let I : Submodule ℂ GeoW := GeoIsotype(ω)
  let K : Submodule ℂ GeoW := globalThetaSobolev F a hGeo hs
  let levels (Λ : ℝ) : Submodule ℂ I := (globalAbsolutePWSobolev (F := F) (S := S) hs a ω Λ).comap I.subtype
  letI : CompleteSpace I := (instClosedSpectralIsotypeSec2 (F := F) hGeo hs ω).completeSpace_coe
  letI : ∀ Λ, CompleteSpace (levels Λ) := fun Λ ↦
    (show IsClosed (levels Λ : Set I) from (Submodule.isClosed_topologicalClosure _).preimage continuous_subtype_val).completeSpace_coe
  have hlim (u : I) : Tendsto (fun Λ ↦ (levels Λ).starProjection u) atTop
      (𝓝 (I.orthogonalProjectionOnto (K.starProjection u))) := by
    with_unfolding_all exact absolutePWProjection_tendsto (F := F) (S := S) hs a ω _hω _hPic u
  have hTval : T.val = I.orthogonalProjectionOnto.comp
      (((modulatedCutoffOperator m𝔽 globalWMeasure hρ).comp (geoAction(φ))).comp (K.starProjection.comp I.subtypeL)) := by
    with_unfolding_all exact (exists_nuclear_geometricPWRestriction (F := F) hs a ω φ hρ).choose_spec.1
  with_unfolding_all
    exact absolutePWCondensation_traceNorm_tendsto_compressed GeoW I K
      ((modulatedCutoffOperator m𝔽 globalWMeasure hρ).comp (geoAction(φ))) levels hlim T hTval

/-- Paper: Theorem 11.2.1.2(2) and (11.2.1.5), p. 488.
The traces of the cutoff absolute condensations converge to the trace of the
cutoff operator composed on the right with the geometric projection.
Deviation: Keep the right geometric projection at the fixed cutoff. -/
theorem absolutePWCondensation_trace_tendsto (a : ℝ) (ω : PontryaginDual C₁)
    (_hω : NormOneCharacterUnramifiedOutside ω S) (_hPic : PicTrivial)
    (φ : BruhatCompactSupport C𝔽) (_hφ : supportedAboveOne(φ))
    (hρ : IsModulatedCutoff m𝔽 R ε ρ) :
    let T := nuclearRestriction(a, ω, hρ, φ)
    Tendsto (fun Λ ↦ hilbertTrace
      (productTraceClass(T, absolutePWProjection (F := F) (S := S) hs a ω Λ))) atTop
      (𝓝 (hilbertTrace T)) := by
  have limit {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (T : nuclearEndomorphisms H) (A : ℝ → nuclearEndomorphisms H)
      (h : Tendsto (fun r ↦ traceNorm (A r - T)) atTop (𝓝 0)) :
      Tendsto (fun r ↦ hilbertTrace (A r)) atTop (𝓝 (hilbertTrace T)) := by
    obtain ⟨tr, htr⟩ := hilbertTrace_linear (H := H)
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp only [← htr, ← map_sub]
    simp only [htr]
    exact squeeze_zero (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_hilbertTrace_le _) h
  let T := nuclearRestriction(a, ω, hρ, φ)
  exact limit (H := ↥(GeoIsotype(ω))) T
    (fun r ↦ productTraceClass(T, absolutePWProjection (F := F) (S := S) hs a ω r))
    (absolutePWCondensation_traceNorm_tendsto (F := F) (S := S) hs a ω _hω _hPic φ _hφ hρ)

/-- Paper: Definition 11.2.1.3(1) and (11.2.1.6), p. 488.
The local invariant level completes the weighted theta image of zero-moment
tests with compact Fourier support in the product-norm region of size Λ.
Deviation: Use a positive local twist so the weighted theta functions belong to L². -/
def sLocalInvariantPWSobolev (_hs : 0 ≤ s) {a : ℝ} (ha : 0 < a) (ω : PontryaginDual J₁) (Λ : ℝ) :
    Submodule ℂ LocalW :=
  (Submodule.span ℂ (range fun f : band(sLocalPWProductRegion S Λ) ↦
    sLocalPWThetaSobolevMap (F := F) (S := S) (s := s) ha ω f.val)).topologicalClosure

/-- Paper: Definition 11.2.1.3(1) and (11.2.1.6), p. 488.
A polar-free test band-limited by product norm gives its weighted homogeneous
theta vector in the local invariant level.
Deviation: Use the positive local twist of the repaired definition. -/
theorem sLocalInvariantPWSobolev_mem {a : ℝ} (ha : 0 < a) (ω : PontryaginDual J₁) (Λ : ℝ)
    (f : Zₛ) (_hf : f ∈ band(sLocalPWProductRegion S Λ)) :
    sLocalPWThetaSobolevMap (F := F) (S := S) (s := s) ha ω f ∈ sLocalInvariantPWSobolev (F := F) (S := S) hs ha ω Λ := by
  exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨⟨f, _hf⟩, rfl⟩)

/-- Paper: Definition 11.2.1.3(1) and (11.2.1.7), p. 488.
The global invariant level completes the weighted homogeneous theta image
of the inserted polar-free tests with compact Fourier support in the product region.
Deviation: Use the integer-indicator insertion of §7.3.2 directly from S. -/
def globalInvariantPWSobolev (_hs : 0 ≤ s) (a : ℝ) (ω : PontryaginDual C₁) (Λ : ℝ) :
    Submodule ℂ GeoW :=
  (Submodule.span ℂ (range fun f : band(sLocalPWProductRegion S Λ) ↦
    globalPWThetaSobolevMap (F := F) (S := S) (s := s) a ω f.val)).topologicalClosure

/-- Paper: Definition 11.2.1.3(1) and (11.2.1.7), p. 488.
An inserted polar-free test band-limited by product norm gives its weighted
homogeneous theta vector in the global invariant level.
Deviation: Use the direct integer-indicator insertion. -/
theorem globalInvariantPWSobolev_mem (a : ℝ) (ω : PontryaginDual C₁) (Λ : ℝ)
    (f : Zₛ) (_hf : f ∈ band(sLocalPWProductRegion S Λ)) :
    globalPWThetaSobolevMap (F := F) (S := S) (s := s) a ω f ∈ globalInvariantPWSobolev (F := F) (S := S) hs a ω Λ := by
  exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨⟨f, _hf⟩, rfl⟩)

local notation "invLevel(" a ", " ω ", " Λ ")" =>
  (globalInvariantPWSobolev (F := F) (S := S) hs a ω Λ).comap (GeoIsotype(ω)).subtype

/-- Paper: Definition 11.2.1.3(2) and (11.2.1.8), p. 489.
The invariant truncation is the orthogonal projection onto the global invariant level.
Deviation: Include the projected vector back into the ambient isotype. -/
def invariantPWProjection (a : ℝ) (ω : PontryaginDual C₁) (Λ : ℝ) :
    GeoIsotype(ω) →L[ℂ] GeoIsotype(ω) :=
  letI : IsClosed (invLevel(a, ω, Λ) : Set GeoIsotype(ω)) :=
    (Submodule.isClosed_topologicalClosure _).preimage continuous_subtype_val
  (invLevel(a, ω, Λ)).starProjection

/-- Paper: Definition 11.2.1.3(2), p. 489.
The invariant projection fixes vectors in the invariant level. -/
theorem invariantPWProjection_apply_of_mem (a : ℝ) (ω : PontryaginDual C₁) (Λ : ℝ)
    (u : GeoIsotype(ω)) (_hu : u ∈ invLevel(a, ω, Λ)) :
    invariantPWProjection (F := F) (S := S) hs a ω Λ u = u := by
  letI : IsClosed (invLevel(a, ω, Λ) : Set GeoIsotype(ω)) :=
    (Submodule.isClosed_topologicalClosure _).preimage continuous_subtype_val
  exact Submodule.starProjection_eq_self_iff.mpr _hu

/-- Paper: Definition 11.2.1.3(3), p. 489.
Invariant condensation first projects onto the invariant level, then convolves
and projects onto the weighted theta subspace. -/
def invariantPWCondensation (a : ℝ) (ω : PontryaginDual C₁) (Λ : ℝ)
    (φ : BruhatCompactSupport C𝔽) (_hφ : supportedAboveOne(φ)) :
    GeoIsotype(ω) →L[ℂ] GeoIsotype(ω) :=
  (onIsotype(ω, (ambientGeom(a)).comp (geoAction(φ)))).comp
    (invariantPWProjection (F := F) (S := S) hs a ω Λ)

/-- Paper: Definition 11.2.1.3(3), p. 489.
On the invariant level, condensation acts by convolution followed by the geometric projection. -/
theorem invariantPWCondensation_apply_of_mem (a : ℝ) (ω : PontryaginDual C₁) (Λ : ℝ)
    (φ : BruhatCompactSupport C𝔽) (hφ : supportedAboveOne(φ))
    (u : GeoIsotype(ω)) (_hu : u ∈ invLevel(a, ω, Λ)) :
    invariantPWCondensation (F := F) (S := S) hs a ω Λ φ hφ u =
      onIsotype(ω, (ambientGeom(a)).comp (geoAction(φ))) u := by
  have h := invariantPWProjection_apply_of_mem (F := F) (S := S) hs a ω Λ u _hu
  simp only [invariantPWCondensation, ContinuousLinearMap.comp_apply, h]

/-- Projections onto levels squeezed between convergent levels and the target range converge. -/
private theorem invariantPWProjection_tendsto_squeeze
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (I K : Submodule ℂ H) [CompleteSpace I] [CompleteSpace K]
    (A B : ℝ → Submodule ℂ I) [∀ i, CompleteSpace (A i)] [∀ i, CompleteSpace (B i)]
    (hlim : ∀ u : I, Tendsto (fun i ↦ (A i).starProjection u) atTop
      (𝓝 (I.orthogonalProjectionOnto (K.starProjection u))))
    (g : ℝ → ℝ) (hg : Tendsto g atTop atTop) (hAB : ∀ᶠ i in atTop, A (g i) ≤ B i)
    (hBK : ∀ (i : ℝ) (w : I), w ∈ B i → (w : H) ∈ K) (u : I) :
    Tendsto (fun i ↦ (B i).starProjection u) atTop
      (𝓝 (I.orthogonalProjectionOnto (K.starProjection u))) := by
  have horth (i : ℝ) (w : I) (hw : w ∈ B i) :
      inner ℂ (I.orthogonalProjectionOnto (K.starProjection (u : H)) - u) w = 0 := by
    have h1 : inner ℂ (I.orthogonalProjectionOnto (K.starProjection (u : H))) w =
        inner ℂ (u : H) (w : H) := by
      rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right,
        Submodule.inner_starProjection_left_eq_right, K.starProjection_eq_self_iff.mpr (hBK i w hw)]
    rw [inner_sub_left, h1, Submodule.coe_inner, sub_self]
  have hle (i : ℝ) (hi : A (g i) ≤ B i) :
      ‖(B i).starProjection u - I.orthogonalProjectionOnto (K.starProjection (u : H))‖ ≤
        ‖(A (g i)).starProjection u - I.orthogonalProjectionOnto (K.starProjection (u : H))‖ := by
    have hb : (B i).starProjection u ∈ B i := (B i).starProjection_apply_mem u
    have ha : (A (g i)).starProjection u ∈ B i := hi ((A (g i)).starProjection_apply_mem u)
    have hw : (B i).starProjection u - (A (g i)).starProjection u ∈ B i := (B i).sub_mem hb ha
    have h0 : inner ℂ (I.orthogonalProjectionOnto (K.starProjection (u : H)) - (B i).starProjection u)
        ((B i).starProjection u - (A (g i)).starProjection u) = 0 := by
      rw [show I.orthogonalProjectionOnto (K.starProjection (u : H)) - (B i).starProjection u =
          (I.orthogonalProjectionOnto (K.starProjection (u : H)) - u) + (u - (B i).starProjection u)
          by abel, inner_add_left, horth i _ hw,
        Submodule.starProjection_inner_eq_zero (K := B i) u _ hw, add_zero]
    have hp := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h0
    rw [show I.orthogonalProjectionOnto (K.starProjection (u : H)) - (B i).starProjection u +
        ((B i).starProjection u - (A (g i)).starProjection u) =
        I.orthogonalProjectionOnto (K.starProjection (u : H)) - (A (g i)).starProjection u
        by abel] at hp
    rw [norm_sub_rev ((B i).starProjection u), norm_sub_rev ((A (g i)).starProjection u)]
    nlinarith [norm_nonneg (I.orthogonalProjectionOnto (K.starProjection (u : H)) - (A (g i)).starProjection u),
      norm_nonneg (I.orthogonalProjectionOnto (K.starProjection (u : H)) - (B i).starProjection u),
      norm_nonneg ((B i).starProjection u - (A (g i)).starProjection u)]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_
    (tendsto_iff_norm_sub_tendsto_zero.mp ((hlim u).comp hg))
  filter_upwards [hAB] with i hi using hle i hi

/-- Raising the level to the reciprocal of the place count tends to infinity and stays below it. -/
private theorem invariantPWProjection_tendsto_root (c : ℕ) :
    let g : ℝ → ℝ := fun Λ ↦ Λ ^ (1 / ((c : ℝ) + 1))
    Tendsto g atTop atTop ∧ ∀ᶠ Λ in atTop, 0 < g Λ ∧ g Λ ^ c ≤ Λ := by
  intro g
  let d : ℝ := (c : ℝ) + 1
  have hd : 0 < d := by positivity
  refine ⟨tendsto_rpow_atTop (one_div_pos.mpr hd), ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with Λ hΛ
  have hg : 0 < g Λ := Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < Λ) _
  refine ⟨hg, ?_⟩
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
  calc Λ ^ (1 / d * c) ≤ Λ ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hΛ (by
          rw [div_mul_eq_mul_div, one_mul, div_le_one hd]
          exact le_add_of_nonneg_right zero_le_one)
    _ = Λ := Real.rpow_one Λ

/-- A box of size Λ lies in every product region of size at least Λ to the number of places. -/
private theorem invariantPWProjection_tendsto_abs_le (a : ℝ) (ω : PontryaginDual C₁) {Λ Y : ℝ}
    (hΛ : 0 < Λ) (hY : Λ ^ (Fintype.card (InfinitePlace F) + S.card) ≤ Y) :
    globalAbsolutePWSobolev (F := F) (S := S) hs a ω Λ ≤
      globalInvariantPWSobolev (F := F) (S := S) hs a ω Y := by
  have hbox : sLocalPWBox S Λ ⊆ sLocalPWProductRegion S Y := by
    intro x hx
    have ha : (∏ w : InfinitePlace F, ‖x.1 w‖ ^ w.mult) ≤ Λ ^ Fintype.card (InfinitePlace F) := by
      simpa only [Finset.prod_const, Finset.card_univ] using
        (Finset.prod_le_prod₀ (s := Finset.univ) (g := fun _ : InfinitePlace F ↦ Λ)
          (fun w _ ↦ pow_nonneg (norm_nonneg (x.1 w)) w.mult) (fun w _ ↦ hx.1 w))
    have hf : (∏ v : S, ‖x.2 v‖) ≤ Λ ^ S.card := by
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_coe] using
        (Finset.prod_le_prod₀ (s := Finset.univ) (g := fun _ : S ↦ Λ)
          (fun v _ ↦ norm_nonneg (x.2 v)) (fun v _ ↦ hx.2 v))
    change _ * _ ≤ Y
    refine le_trans ?_ hY
    rw [pow_add]
    exact mul_le_mul ha hf (Finset.prod_nonneg fun v _ ↦ norm_nonneg (x.2 v))
      (pow_nonneg hΛ.le _)
  have htests : sLocalPWTests (S := S) (T := S) le_rfl (sLocalPWBox S Λ) ≤
      sLocalPWTests (S := S) (T := S) le_rfl (sLocalPWProductRegion S Y) :=
    Submodule.map_mono (Submodule.span_mono fun _ hf ↦ ⟨hf.1, hf.2.trans (Set.preimage_mono hbox)⟩)
  refine Submodule.topologicalClosure_mono (Submodule.span_mono ?_)
  rintro _ ⟨f, rfl⟩
  exact ⟨⟨f.val, htests f.property⟩, rfl⟩

/-- The global invariant levels lie in the weighted theta subspace. -/
private theorem invariantPWProjection_tendsto_le_theta (a : ℝ) (ω : PontryaginDual C₁) (Λ : ℝ) :
    globalInvariantPWSobolev (F := F) (S := S) hs a ω Λ ≤
      (globalThetaSobolev F a hGeo hs : Submodule ℂ GeoW) := by
  refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_topologicalClosure _)
  rw [Submodule.span_le]
  rintro _ ⟨f, rfl⟩
  let f₀ : adelePolarSubspace F := ⟨sAdeleSchwartzToGlobal F S f.val.val,
    sAdeleSchwartzToGlobal_mem_polarSubspace f.val⟩
  let x : globalPolarFreeThetaSubmodule (F := F) ω :=
    ⟨Submodule.Quotient.mk f₀.val, ⟨f₀.val, f₀.property, rfl⟩⟩
  obtain ⟨j, -, -, hj⟩ := exists_globalHomogeneousThetaSobolevInclusion
    (F := F) (a := a) hGeo hs ω
  have he := (hj f₀ x rfl).2
  have heq : globalPWThetaSobolevMap (F := F) (S := S) (s := s) a ω f.val = (j x).val.val := by
    apply Lp.ext
    exact (withDensity_absolutelyContinuous _ _).ae_le
      ((globalPWThetaSobolevMap_apply (F := F) (S := S) (s := s) a ω f.val).trans he.symm)
  change globalPWThetaSobolevMap (F := F) (S := S) (s := s) a ω f.val ∈
    (globalThetaSobolev F a hGeo hs : Submodule ℂ GeoW)
  rw [heq]
  exact (j x).val.property

/-- Paper: Theorem 11.2.1.4(1), p. 489.
The invariant projections converge strongly to the isotypic geometric projection.
Deviation: The support assumption on the test function is used in part (2). -/
theorem invariantPWProjection_tendsto (a : ℝ) (ω : PontryaginDual C₁)
    (_hω : NormOneCharacterUnramifiedOutside ω S) (_hPic : PicTrivial) (u : GeoIsotype(ω)) :
    Tendsto (fun Λ ↦ invariantPWProjection (F := F) (S := S) hs a ω Λ u) atTop (𝓝 (Pgeom(a, ω) u)) := by
  let c : ℕ := Fintype.card (InfinitePlace F) + S.card
  let g : ℝ → ℝ := fun Λ ↦ Λ ^ (1 / ((c : ℝ) + 1))
  let I : Submodule ℂ GeoW := GeoIsotype(ω)
  let K : Submodule ℂ GeoW := globalThetaSobolev F a hGeo hs
  let A (Λ : ℝ) : Submodule ℂ I := absLevel(a, ω, Λ)
  let B (Λ : ℝ) : Submodule ℂ I := invLevel(a, ω, Λ)
  letI : CompleteSpace I := (instClosedSpectralIsotypeSec2 (F := F) hGeo hs ω).completeSpace_coe
  letI : ∀ Λ, CompleteSpace (A Λ) := fun Λ ↦
    (show IsClosed (A Λ : Set I) from
      (Submodule.isClosed_topologicalClosure _).preimage continuous_subtype_val).completeSpace_coe
  letI : ∀ Λ, CompleteSpace (B Λ) := fun Λ ↦
    (show IsClosed (B Λ : Set I) from
      (Submodule.isClosed_topologicalClosure _).preimage continuous_subtype_val).completeSpace_coe
  have hpow : ∀ᶠ Λ in atTop, 0 < g Λ ∧ g Λ ^ c ≤ Λ := (invariantPWProjection_tendsto_root c).2
  have hAB : ∀ᶠ Λ in atTop, A (g Λ) ≤ B Λ := by
    filter_upwards [hpow] with Λ hΛ
    exact Submodule.comap_mono
      (invariantPWProjection_tendsto_abs_le (F := F) (S := S) hs a ω hΛ.1 hΛ.2)
  have hBK (Λ : ℝ) (w : I) (hw : w ∈ B Λ) : (w : GeoW) ∈ K :=
    invariantPWProjection_tendsto_le_theta (F := F) (S := S) hs a ω Λ hw
  have hlim (v : I) : Tendsto (fun Λ ↦ (A Λ).starProjection v) atTop
      (𝓝 (I.orthogonalProjectionOnto (K.starProjection v))) := by
    with_unfolding_all exact absolutePWProjection_tendsto (F := F) (S := S) hs a ω _hω _hPic v
  with_unfolding_all
    exact invariantPWProjection_tendsto_squeeze GeoW I K A B hlim g
      (invariantPWProjection_tendsto_root c).1 hAB hBK u

/-- Paper: Theorem 11.2.1.4(2) and (11.2.1.9), p. 489.
Right multiplication of cutoff geometric convolution by the invariant projections
converges in trace norm.
Deviation: For the fixed cutoff keep the right geometric projection in the
limit. Use the trace class of cutoff convolution on the geometric range. -/
theorem invariantPWCondensation_traceNorm_tendsto (a : ℝ) (ω : PontryaginDual C₁)
    (_hω : NormOneCharacterUnramifiedOutside ω S) (_hPic : PicTrivial)
    (φ : BruhatCompactSupport C𝔽) (_hφ : supportedAboveOne(φ))
    (hρ : IsModulatedCutoff m𝔽 R ε ρ) :
    let T := nuclearRestriction(a, ω, hρ, φ)
    Tendsto (fun Λ ↦ traceNorm
      (productTraceClass(T, invariantPWProjection (F := F) (S := S) hs a ω Λ) -
        T)) atTop (𝓝 0) := by
  intro T
  let I : Submodule ℂ GeoW := GeoIsotype(ω)
  let K : Submodule ℂ GeoW := globalThetaSobolev F a hGeo hs
  let levels (Λ : ℝ) : Submodule ℂ I := (globalInvariantPWSobolev (F := F) (S := S) hs a ω Λ).comap I.subtype
  letI : CompleteSpace I := (instClosedSpectralIsotypeSec2 (F := F) hGeo hs ω).completeSpace_coe
  letI : ∀ Λ, CompleteSpace (levels Λ) := fun Λ ↦
    (show IsClosed (levels Λ : Set I) from (Submodule.isClosed_topologicalClosure _).preimage continuous_subtype_val).completeSpace_coe
  have hlim (u : I) : Tendsto (fun Λ ↦ (levels Λ).starProjection u) atTop
      (𝓝 (I.orthogonalProjectionOnto (K.starProjection u))) := by
    with_unfolding_all exact invariantPWProjection_tendsto (F := F) (S := S) hs a ω _hω _hPic u
  have hTval : T.val = I.orthogonalProjectionOnto.comp
      (((modulatedCutoffOperator m𝔽 globalWMeasure hρ).comp (geoAction(φ))).comp (K.starProjection.comp I.subtypeL)) := by
    with_unfolding_all exact (exists_nuclear_geometricPWRestriction (F := F) hs a ω φ hρ).choose_spec.1
  with_unfolding_all
    exact absolutePWCondensation_traceNorm_tendsto_compressed GeoW I K
      ((modulatedCutoffOperator m𝔽 globalWMeasure hρ).comp (geoAction(φ))) levels hlim T hTval

/-- Paper: Theorem 11.2.1.4(2) and (11.2.1.10), p. 489.
The traces of the cutoff invariant condensations converge to the trace of the
cutoff operator composed on the right with the geometric projection.
Deviation: Keep the right geometric projection at the fixed cutoff. -/
theorem invariantPWCondensation_trace_tendsto (a : ℝ) (ω : PontryaginDual C₁)
    (_hω : NormOneCharacterUnramifiedOutside ω S) (_hPic : PicTrivial)
    (φ : BruhatCompactSupport C𝔽) (_hφ : supportedAboveOne(φ))
    (hρ : IsModulatedCutoff m𝔽 R ε ρ) :
    let T := nuclearRestriction(a, ω, hρ, φ)
    Tendsto (fun Λ ↦ hilbertTrace
      (productTraceClass(T, invariantPWProjection (F := F) (S := S) hs a ω Λ))) atTop
      (𝓝 (hilbertTrace T)) := by
  have limit {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (T : nuclearEndomorphisms H) (A : ℝ → nuclearEndomorphisms H)
      (h : Tendsto (fun r ↦ traceNorm (A r - T)) atTop (𝓝 0)) :
      Tendsto (fun r ↦ hilbertTrace (A r)) atTop (𝓝 (hilbertTrace T)) := by
    obtain ⟨tr, htr⟩ := hilbertTrace_linear (H := H)
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp only [← htr, ← map_sub]
    simp only [htr]
    exact squeeze_zero (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_hilbertTrace_le _) h
  let T := nuclearRestriction(a, ω, hρ, φ)
  exact limit (H := ↥(GeoIsotype(ω))) T
    (fun r ↦ productTraceClass(T, invariantPWProjection (F := F) (S := S) hs a ω r))
    (invariantPWCondensation_traceNorm_tendsto (F := F) (S := S) hs a ω _hω _hPic φ _hφ hρ)

end Levels

section Orbital

local notation "Sₚ(" p ")" => (finite_nuclearityPlacesAbove (F := F) p).toFinset
local notation "N(" p ", " hs ", " ω ")" => orbitalSobolevSubmodule F (Sₚ(p)) hs ω

variable (F) in
/-- Paper: (11.2.2.1), p. 489. The prime-indexed Sobolev quotient divides the
zero-line isotype by the closed principal-value subspace.
Deviation: Use the closure of the principal-value image from §11.2.0.
Zero-line theta density identifies the completed theta isotype with the ambient one.

Kept as an `abbrev` for now (#5398): as a `def` with its own instances it breaks proofs and
statements that use it, see the issue. Do not copy this pattern: a new type synonym with
structure is a `def` with its own instances (`AGENTS.md`). -/
abbrev PrimeOrbitalSobolevQuotient (p : HeightOneSpectrum (𝓞 ℚ)) {s : ℝ} (hs : 0 ≤ s)
    (ω : PontryaginDual C₁) :=
  ↥(Wω(hs, ω)) ⧸ N(p, hs, ω)

local notation "Q(" p ", " hs ", " ω ")" => PrimeOrbitalSobolevQuotient F p hs ω

/-- Paper: (11.2.2.1), p. 489. In the prime quotient a representative has
zero class exactly when it belongs to the closed principal-value subspace.
Deviation: Use the closed image from §11.2.0. -/
theorem primeOrbitalSobolevQuotient_mk_eq_zero (p : HeightOneSpectrum (𝓞 ℚ)) {s : ℝ} (hs : 0 ≤ s)
    (ω : PontryaginDual C₁) (u : Wω(hs, ω)) :
    ((N(p, hs, ω)).mkQ u : Q(p, hs, ω)) = 0 ↔ u ∈ N(p, hs, ω) :=
  Submodule.Quotient.mk_eq_zero _

/-- Paper: (11.2.2.1), p. 489. The prime quotient is separable in the quotient norm.
Deviation: Use the closed principal-value denominator. -/
theorem primeOrbitalSobolevQuotient_separable (p : HeightOneSpectrum (𝓞 ℚ))
    {s : ℝ} (hs : 0 ≤ s) (ω : PontryaginDual C₁) :
    TopologicalSpace.SeparableSpace Q(p, hs, ω) := by
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  let : SecondCountableTopology W(s) := Lp.SecondCountableTopology
  exact (N(p, hs, ω)).isQuotientMap_mkQL.separableSpace

/-- Paper: (11.2.2.1), p. 489. The prime quotient is complete in the quotient norm.
Deviation: Use the closed principal-value denominator. -/
theorem primeOrbitalSobolevQuotient_complete (p : HeightOneSpectrum (𝓞 ℚ))
    {s : ℝ} (hs : 0 ≤ s) (ω : PontryaginDual C₁) :
    CompleteSpace Q(p, hs, ω) := by
  let : CompleteSpace ↥(Wω(hs, ω)) :=
    (instClosedSpectralIsotypeSec2 (F := F) h₀ hs ω).completeSpace_coe
  exact Submodule.Quotient.completeSpace (N(p, hs, ω))

local notation "P" => adelePolarSubspace F
local notation "testQuot(" χ ")" =>
  (LinearMap.ker ((homogeneousAdelicThetaLinearMap F (ω(χ))).domRestrict P))
local notation "weightedTest(" hs ", " χ ", " f ")" =>
  ((existsUnique_globalThetaSobolevAverage (F := F) (a := 0) h₀ hs (ω(χ))).exists.choose
    (globalThetaSobolevInclusion F 0 h₀ hs (Submodule.Quotient.mk (f : P)))).val

/-- Paper: Paragraph after (11.2.2.1), p. 490.
The §7.4 test quotient maps densely into the Sobolev quotient. Its pulled-back norm
is the quotient seminorm of the weighted tests modulo the test principal-value image.
Deviation: Take the separated completion for the potentially degenerate seminorm. -/
theorem primeOrbitalSobolevQuotient_completion (χ : PontryaginDual C𝔽)
    (p : HeightOneSpectrum (𝓞 ℚ)) {s : ℝ} (hs : 0 ≤ s) :
    ∃ (i : (P ⧸ testQuot(χ)) →ₗ[ℂ] Wω(hs, ω(χ)))
      (j : FiniteNuclearityQuotient χ p →ₗ[ℂ] Q(p, hs, ω(χ))),
      (∀ f : P, ((i ((testQuot(χ)).mkQ f)) : W(s)) = weightedTest(hs, χ, f)) ∧
      (∀ f : P,
        j ((finiteNuclearityDenominator χ p).mkQ ((testQuot(χ)).mkQ f)) =
          (N(p, hs, ω(χ))).mkQ (i ((testQuot(χ)).mkQ f))) ∧
      (∀ u : P ⧸ testQuot(χ),
        ‖j ((finiteNuclearityDenominator χ p).mkQ u)‖ =
          ⨅ v : finiteNuclearityDenominator χ p, ‖i u - i v.val‖) ∧ DenseRange j := by sorry

variable (p : HeightOneSpectrum (𝓞 ℚ)) {s : ℝ} (hs : 0 ≤ s)
  (ω : PontryaginDual (ideleClassNorm F).ker)

local notation "Aω(" φ ")" => ContinuousLinearMap.restrict (A(hs, φ))
  (hardySobolevTestAction_preserves_spectralIsotype (F := F) h₀ hs ω φ)

/-- Paper: (11.2.2.1)–(11.2.2.3), pp. 489–490.
Convolution preserves the closed principal-value subspace of the zero-line isotype.
Deviation: Use the closure of the principal-value image. -/
theorem primeOrbitalSobolevSubmodule_convolution_invariant (φ : BruhatCompactSupport C𝔽) :
    N(p, hs, ω) ≤ ((N(p, hs, ω)).mkQL.comp (Aω(φ))).ker := by sorry

/-- An operator whose composite with the quotient map kills the denominator descends uniquely. -/
private theorem existsUnique_primeOrbitalSobolevConvolution_lift
    {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (N : Submodule ℂ E) (A : E →L[ℂ] E)
    (hN : N ≤ (N.mkQL.comp A).ker) :
    ∃! C : (E ⧸ N) →L[ℂ] (E ⧸ N),
      ∀ u : E, C (N.mkQ u) = N.mkQ (A u) := by
  let C : (E ⧸ N) →L[ℂ] (E ⧸ N) := N.liftQL (N.mkQL.comp A) hN
  refine ⟨C, fun u ↦ rfl, ?_⟩
  intro D hD
  apply ContinuousLinearMap.ext
  intro q
  obtain ⟨u, rfl⟩ := N.mkQ_surjective q
  exact hD u

/-- Paper: (11.2.2.3), p. 490.
The action on representatives determines a unique continuous linear map on the prime quotient.
Deviation: Use the closed principal-value denominator. -/
theorem existsUnique_primeOrbitalSobolevConvolution (φ : BruhatCompactSupport C𝔽) :
    ∃! C : Q(p, hs, ω) →L[ℂ] Q(p, hs, ω), ∀ u : Wω(hs, ω),
      C ((N(p, hs, ω)).mkQ u) = (N(p, hs, ω)).mkQ (Aω(φ) u) := by
  exact existsUnique_primeOrbitalSobolevConvolution_lift
    (N(p, hs, ω)) (Aω(φ))
    (primeOrbitalSobolevSubmodule_convolution_invariant (F := F) p hs ω φ)

/-- Paper: (11.2.2.3), p. 490.
The prime orbital action is the convolution operator descended to the zero-line quotient.
Deviation: Use the closed principal-value denominator. -/
def primeOrbitalSobolevConvolution (φ : BruhatCompactSupport C𝔽) :=
  (existsUnique_primeOrbitalSobolevConvolution (F := F) p hs ω φ).exists.choose

/-- Paper: (11.2.2.3), p. 490.
The orbital convolution of a quotient class is the class of the representative's convolution. -/
theorem primeOrbitalSobolevConvolution_mkQ (φ : BruhatCompactSupport C𝔽) (u : Wω(hs, ω)) :
    primeOrbitalSobolevConvolution (F := F) p hs ω φ ((N(p, hs, ω)).mkQ u) =
      (N(p, hs, ω)).mkQ (Aω(φ) u) := by
  exact (existsUnique_primeOrbitalSobolevConvolution (F := F) p hs ω φ).exists.choose_spec u

-- TODO(paper-gap): Corollary 11.2.0.5 bounds the jets but gives no upper
-- bound on their biorthogonals. The single-prime trace proof needs its own
-- estimate. For the §11.2.0 basis at one prime, multiplication by
-- |g|^(2πi / log p) shifts the jets unitarily and permutes their
-- biorthogonals. There are only finitely many orbits, including jet order.
-- In (11.2.2.12) the displayed summands act on the primal quotient. For
-- the transpose the input is a functional ℓ and each term is ℓ(ψⱼ) A'ηⱼ.
-- Page 496 invokes this expansion on PW levels and needs a common level
-- for its chosen representatives as well as the kernel comparison.

variable (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
variable (h₁ : 1 < s) (_hdeg : 2 * (Module.finrank ℚ F : ℝ) ≤ s)
variable (_hχ : ∀ v ∈ (finite_nuclearityPlacesAbove (F := F) p).toFinset,
  (ideleClassNormTwist χ 0).IsUnramifiedAt v)

include _hdeg _hχ

local notation "hs₁" => (zero_lt_one.trans h₁).le
local notation "OrbQ" => Q(p, hs₁, ω(χ))
local notation "OrbA(" φ ")" => primeOrbitalSobolevConvolution (F := F) p hs₁ (ω(χ)) φ

local notation "onClosedPrimeQuotient(" hs ", " ω ", " body ")" =>
  (let hN := instClosedOrbitalSobolevSubmoduleSec2a (F := F) (Sₚ(p)) hs ω
   letI : IsClosed (N(p, hs, ω) : Set Wω(hs, ω)) := hN
   letI : CompleteSpace ↥(Wω(hs, ω)) :=
     (instClosedSpectralIsotypeSec2 (F := F) h₀ hs ω).completeSpace_coe
   letI : CompleteSpace ↥(N(p, hs, ω)) := hN.completeSpace_coe
   letI : NormedAddCommGroup Q(p, hs, ω) := Submodule.Quotient.normedAddCommGroup (N(p, hs, ω))
   letI : InnerProductSpace ℂ Q(p, hs, ω) := Submodule.instQuotientInnerProductSpace (N(p, hs, ω))
   letI : CompleteSpace Q(p, hs, ω) := Submodule.Quotient.completeSpace (N(p, hs, ω))
   body)

/-- Paper: Theorem 11.2.2.1 and (11.2.2.3), p. 490.
Convolution by any compactly supported Bruhat test on the prime quotient is trace class.
Deviation: Use the quotient by the closed principal-value image. -/
theorem primeOrbitalSobolevConvolution_nuclear (φ : BruhatCompactSupport C𝔽) :
    onClosedPrimeQuotient(hs₁, ω(χ),
      letI : PolynormableSpace ℂ OrbQ := (norm_withSeminorms ℂ OrbQ).toPolynormableSpace
      IsNuclearOperator (OrbA(φ))) := by sorry

/-- Paper: Theorem 11.2.2.1 and (11.2.2.3), p. 490.
The convolution action lifts linearly to the trace class and is continuous in trace norm.
Deviation: Use the quotient by the closed principal-value image. -/
theorem primeOrbitalSobolevConvolution_traceNorm_continuous :
    onClosedPrimeQuotient(hs₁, ω(χ),
      ∃ L : BruhatCompactSupport C𝔽 →ₗ[ℂ] nuclearEndomorphisms OrbQ,
        (∀ φ, (L φ).val = OrbA(φ)) ∧ Tendsto (fun φ ↦ traceNorm (L φ)) (𝓝 0) (𝓝 0)) :=
  by sorry

/-- Paper: Theorem 11.2.2.1, p. 490.
Taking the trace of prime orbital convolution gives a distribution on the compactly
supported Bruhat test space.
Deviation: Use the quotient by the closed principal-value image. -/
theorem primeOrbitalSobolevConvolution_trace_distribution :
    onClosedPrimeQuotient(hs₁, ω(χ),
      ∃ D : StrongDual ℂ (BruhatCompactSupport C𝔽),
        ∀ (φ : BruhatCompactSupport C𝔽) (T : nuclearEndomorphisms OrbQ),
          T.val = OrbA(φ) → D φ = hilbertTrace T) := by
  have traceDistribution {X : Type _} {H : Type _} [AddCommGroup X] [Module ℂ X]
      [TopologicalSpace X] [IsTopologicalAddGroup X] [NormedAddCommGroup H]
      [InnerProductSpace ℂ H] [CompleteSpace H] (A : X → H →L[ℂ] H)
      (h : ∃ T : X →ₗ[ℂ] nuclearEndomorphisms H, (∀ x, (T x).val = A x) ∧
        Tendsto (fun x : X ↦ traceNorm (H := H) (T x)) (𝓝 0) (𝓝 0)) :
      ∃ D : StrongDual ℂ X, ∀ (x : X) (U : nuclearEndomorphisms H),
        U.val = A x → D x = hilbertTrace U := by
    obtain ⟨T, hT, ht⟩ := h
    obtain ⟨L, hL⟩ := hilbertTrace_linear (H := H)
    let D : X →ₗ[ℂ] ℂ := L.comp T
    have hb (x : X) : ‖D x‖ ≤ traceNorm (T x) :=
      (congrArg (fun c : ℂ ↦ ‖c‖) (hL (T x))).le.trans (norm_hilbertTrace_le (T x))
    have hd : Continuous D := continuous_of_continuousAt_zero D <| by
      change Tendsto D (𝓝 0) (𝓝 (D 0))
      rw [D.map_zero]
      exact squeeze_zero_norm hb ht
    refine ⟨⟨D, hd⟩, fun x U hU ↦ ?_⟩
    have heq : T x = U := Subtype.ext ((hT x).trans hU.symm)
    exact (hL (T x)).trans (congrArg (hilbertTrace (H := H)) heq)
  have hn := primeOrbitalSobolevConvolution_traceNorm_continuous (F := F) (p := p)
    (χ := χ) (h₁ := h₁) (_hdeg := _hdeg) (_hχ := _hχ)
  exact onClosedPrimeQuotient(hs₁, ω(χ), by
    apply traceDistribution (X := BruhatCompactSupport C𝔽) (H := OrbQ) (fun φ ↦ OrbA(φ))
    exact hn)

local notation "zeros" => {z : ℂ // reciprocalPartialHeckeEulerProduct χ (Sₚ(p)) z = 0}
local notation "mult(" z ")" => orbitalEulerMultiplicity χ (Sₚ(p)) z

/-- Paper: Theorem 11.2.2.1 and (11.2.2.4)–(11.2.2.5), p. 490.
The trace is the absolutely convergent sum of Mellin values at the zeros of the
reciprocal Euler product over the places above p, weighted by admissible multiplicity.
Deviation: Use the closed denominator and the strict boundary cutoff of §11.2.0.
Under the stated degree bound this cutoff agrees with the printed one. -/
theorem primeOrbitalSobolevConvolution_trace (φ : BruhatCompactSupport C𝔽) :
    onClosedPrimeQuotient(hs₁, ω(χ),
      ∀ (T : nuclearEndomorphisms OrbQ), T.val = OrbA(φ) →
        let term (z : zeros) :=
          (spectralBoundaryMultiplicity s (mult(z.val)) : ℂ) * nuclearityTestMellin χ φ z.val
        Summable (fun z ↦ ‖term z‖) ∧ HasSum term (hilbertTrace T)) := by sorry

include h₁ in
/-- Paper: Remark 11.2.2.2, p. 491.
The degree bound admits all jet orders below the multiplicity of a prime Euler zero.
The strict integrability cutoff then leaves that multiplicity unchanged. -/
theorem primeOrbitalMultiplicity_saturates (z : zeros) :
    spectralBoundaryMultiplicity s (mult(z.val)) = mult(z.val) := by
  classical
  let S := Sₚ(p)
  have hcard : S.card ≤ Module.finrank ℚ F := by
    let e (v : S) : p.asIdeal.primesOver (𝓞 F) :=
      ⟨v.val.asIdeal, v.val.isPrime, ⟨(congrArg HeightOneSpectrum.asIdeal
        (show v.val.under (𝓞 ℚ) = p from (finite_nuclearityPlacesAbove (F := F) p).mem_toFinset.mp v.property)).symm⟩⟩
    have hi : Function.Injective e := fun v w h ↦
      Subtype.ext (HeightOneSpectrum.ext (congrArg Subtype.val h))
    simpa only [Fintype.card_coe] using (Fintype.card_le_of_injective e hi).trans
      (reciprocalEulerProduct_over_prime_order_le_card_le (F := F) p)
  have hm : mult(z.val) ≤ Module.finrank ℚ F := by
    rw [orbitalEulerMultiplicity_eq_card]
    exact (Finset.card_filter_le _ _).trans hcard
  apply Nat.le_antisymm (min_le_left _ _)
  by_contra! hlt
  have hk : (spectralBoundaryMultiplicity s (mult(z.val)) : ℝ) + 1 ≤ Module.finrank ℚ F := by
    exact_mod_cast (Nat.succ_le_of_lt hlt).trans hm
  have himp := (lt_spectralBoundaryMultiplicity s (mult(z.val))
    (spectralBoundaryMultiplicity s (mult(z.val)))).mpr ⟨hlt, by linarith only [hk, _hdeg]⟩
  exact (lt_irrefl _ himp)

/-- Paper: Remark 11.2.2.2 and (11.2.2.13), p. 491.
The prime orbital convolution trace is independent of the Sobolev degree
once both degrees satisfy the two lower bounds.
Deviation: Use the quotient by the closed principal-value image. -/
theorem primeOrbitalSobolevConvolution_trace_eq_of_degree {s' : ℝ} (h₁' : 1 < s')
    (_hdeg' : 2 * (Module.finrank ℚ F : ℝ) ≤ s') (φ : BruhatCompactSupport C𝔽) :
    let hs' := (zero_lt_one.trans h₁').le
    onClosedPrimeQuotient(hs₁, ω(χ),
      onClosedPrimeQuotient(hs', ω(χ),
        ∀ (T : nuclearEndomorphisms OrbQ) (T' : nuclearEndomorphisms Q(p, hs', ω(χ))),
          T.val = OrbA(φ) →
          T'.val = primeOrbitalSobolevConvolution (F := F) p hs' (ω(χ)) φ →
          hilbertTrace T = hilbertTrace T')) := by
  dsimp only
  intro T T' hT hT'
  have hsum := (primeOrbitalSobolevConvolution_trace (F := F) p χ h₁ _hdeg _hχ φ T hT).2
  have hsum' := (primeOrbitalSobolevConvolution_trace (F := F) p χ h₁' _hdeg' _hχ φ T' hT').2
  apply hsum.unique
  apply hsum'.congr_fun
  intro z
  rw [primeOrbitalMultiplicity_saturates (F := F) p χ h₁ _hdeg _hχ z,
    primeOrbitalMultiplicity_saturates (F := F) p χ h₁' _hdeg' _hχ z]

end Orbital

end RiemannMasullo
