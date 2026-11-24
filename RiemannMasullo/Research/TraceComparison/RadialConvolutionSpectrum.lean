module

public import RiemannMasullo.Research.TraceComparison.SLocalQuotient
public import RiemannMasullo.External.Grh.Props.CompactLogMellin
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.Analysis.Fourier.Convolution
import RiemannMasullo.ForMathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Analysis.Analytic.Order

/-! # The untruncated radial convolution from the S-local comparison

After weighted periodization in the norm coordinate, the convolution uses ordinary
Lebesgue measure multiplied by the compact norm-one volume. On the unweighted
radial Hilbert space, Plancherel puts this convolution in multiplication form.
A null level set of its Fourier symbol cannot carry a continuous eigenfunctional.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology Complex
open scoped ENNReal NNReal NumberField.AdeleRing FourierTransform SchwartzMap InnerProductSpace ComplexConjugate
open RiemannMasullo.External.Grh

namespace RiemannMasullo.StripNuclearity

set_option quotPrecheck false

section LocalQuotient

attribute [local instance] instSIdeleQuotientMeasurableSpaceSec1 instSIdeleQuotientBorelSpaceSec1
  instSIdeleQuotientT2Sec1 instSIdeleQuotientLocallyCompactSec1 instSIdeleQuotientSecondCountableSec1
  instNormOneSIdeleQuotientMeasurableSpaceSec1
variable {F : Type*} [Field F] [NumberField F] {S : Finset (HeightOneSpectrum (𝓞 F))}
local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "Jₛ" => SIdeleQuotient F S
local notation "mS" => sIdeleQuotientNorm F S
local notation "μS" => sLocalQuotientTamagawaMeasure F S
local notation "vS" => (sLocalNormOneQuotientMeasure F S) univ
local notation "logS" => (fun y : Jₛ ↦ Real.log (((mS y).val):ℝ))

private theorem map_local_logNorm : (μS).map logS = vS • (volume : Measure ℝ) := by
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ _
  let : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let : SFinite positiveRealHaar := by unfold positiveRealHaar; infer_instance
  let G := (mS).ker
  let μ := sLocalNormOneQuotientMeasure F S
  let : BorelSpace G := ⟨rfl⟩
  let : CompactSpace G := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage (isCompact_singleton (x:=1)))
  let : μ.IsHaarMeasure := (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1
  let pr := Units.map (adeleProjection F S).toMonoidHom
  have hp : Continuous pr := (continuous_fst.prodMk (continuous_pi fun v : S ↦
    (RestrictedProduct.continuous_eval v.val).comp continuous_snd)).units_map _
  let τ : ℝ≥0ˣ →ₜ* Iₛ := ⟨pr.comp (canonicalIdeleNormSection F),hp.comp (canonicalIdeleNormSection_continuous F)⟩
  have hτ : RightInverse τ (sIdeleNorm F S) := sIdeleNorm_project_canonicalSection F S
  let j (x : G × ℝ≥0ˣ) := x.1.val * (QuotientGroup.mk (τ x.2) : Jₛ)
  have hj : Continuous j := (continuous_subtype_val.comp continuous_fst).mul
    (QuotientGroup.continuous_mk.comp (τ.continuous.comp continuous_snd))
  let l (t : ℝ≥0ˣ) := Real.log (t.val : ℝ)
  have hl : Measurable l := Real.measurable_log.comp (NNReal.continuous_coe.comp Units.continuous_val).measurable
  have hmap : positiveRealHaar.map l = volume := by
    let e : ℝ ≃ₜ ℝ≥0ˣ := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
    have hE : positiveRealHaar = volume.map e := by
      apply congrArg (fun h : ℝ → ℝ≥0ˣ ↦ volume.map h)
      funext y
      exact Units.ext (NNReal.eq (Real.coe_toNNReal _ (Real.exp_pos y).le))
    rw [hE,Measure.map_map hl e.continuous.measurable,show l ∘ e = id from funext fun y ↦ Real.log_exp y,Measure.map_id]
  have hcomp : (l ∘ mS) ∘ j = l ∘ Prod.snd := by
    funext p
    change l (mS (p.1.val * QuotientGroup.mk (τ p.2))) = l p.2
    rw [map_mul,MonoidHom.mem_ker.mp p.1.property,one_mul,sIdeleQuotientNorm_mk,hτ]
  change (μS).map (l ∘ mS) = _
  rw [← (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).2 τ hτ,
    Measure.map_map (hl.comp (isProperMap_sIdeleQuotientNorm F S).continuous.measurable) hj.measurable,
    hcomp,← Measure.map_map hl measurable_snd,Measure.map_snd_prod,Measure.map_smul,hmap]
  exact hl.aemeasurable

/-- In the norm coordinate the periodized S-local dilation acts on radial
inputs by ordinary additive convolution, with the compact norm-one mass.
This is the untruncated convolution of (12.4.1.7), pp. 515–516. -/
theorem sLocal_radial_convolution_logNorm (k u : ℝ → ℂ) (hk : Continuous k) (hu : Continuous u)
    (y : Jₛ) :
    lcaConvolution μS (k ∘ logS) (u ∘ logS) y =
      ((vS).toReal : ℂ) * ∫ t : ℝ, k t * u (logS y - t) := by
  let l : Jₛ → ℝ := logS
  have hm : Measurable l := Real.measurable_log.comp ((NNReal.continuous_coe.comp
    (Units.continuous_val.comp (isProperMap_sIdeleQuotientNorm F S).continuous)).measurable)
  have hlog (z : Jₛ) : l (z⁻¹ * y) = l y - l z := by
    dsimp [l]
    rw [map_mul,map_inv,Units.val_mul,Units.val_inv_eq_inv_val,NNReal.coe_mul,NNReal.coe_inv,
      Real.log_mul (inv_ne_zero (by exact_mod_cast (mS z).ne_zero)) (by exact_mod_cast (mS y).ne_zero),Real.log_inv]
    ring
  let T (t : ℝ) := k t * u (l y - t)
  have hT : Continuous T := hk.mul (hu.comp (continuous_const.sub continuous_id))
  calc
    _ = ∫ z : Jₛ, T (l z) ∂μS := integral_congr_ae (.of_forall fun z ↦ by
      change k (l z) * u (l (z⁻¹ * y)) = _
      rw [hlog])
    _ = ∫ t, T t ∂((μS).map l) := (integral_map hm.aemeasurable hT.aestronglyMeasurable).symm
    _ = _ := by rw [map_local_logNorm,integral_smul_measure,Complex.real_smul]

/-- The Schwartz convolution by the normalized kernel is exactly the
S-local quotient convolution on radial Schwartz inputs. -/
theorem sLocal_radial_schwartz_convolution (G : ℝ → ℂ) (hG : Continuous G) (k : 𝓢(ℝ,ℂ))
    (hk : ∀ t, k t = ((vS).toReal : ℂ) * G t) (u : 𝓢(ℝ,ℂ)) (y : Jₛ) :
    lcaConvolution μS (G ∘ logS) (u ∘ logS) y =
      SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) k u (logS y) := by
  rw [sLocal_radial_convolution_logNorm G u hG u.continuous, SchwartzMap.convolution_apply,
    MeasureTheory.convolution_def, ← integral_const_mul]
  apply integral_congr_ae (.of_forall fun t ↦ ?_)
  rw [ContinuousLinearMap.mul_apply',hk,mul_assoc]

end LocalQuotient

private theorem compactLogMellin_ae_ne_on_line (g : ℝ → ℂ) (hg : Continuous g) (hc : HasCompactSupport g)
    (h0 : compactLogMellin g 0 = 0) (C c₀ : ℂ) (hc₀ : c₀ ≠ 0) (e : ℝ → ℂ) (he : Function.Injective e) :
    ∀ᵐ t : ℝ, C * compactLogMellin g (e t) ≠ c₀ := by
  let Z := {z : ℂ | C * compactLogMellin g z = c₀}
  have hA : AnalyticOnNhd ℂ (fun z ↦ C * compactLogMellin g z - c₀) univ :=
    fun z _ ↦ (analyticAt_const.mul (analyticAt_compactLogMellin hg hc z)).sub analyticAt_const
  have hcod : Zᶜ ∈ codiscrete ℂ := by
    simpa only [Z, Set.preimage_compl, Set.preimage_singleton, sub_eq_zero] using
      hA.preimage_zero_mem_codiscrete (x := (0 : ℂ)) (by simpa only [h0,mul_zero,zero_sub,neg_ne_zero] using hc₀)
  have hcount := (HereditarilyLindelofSpace.isLindelof Z).countable_of_isDiscrete
    (compl_mem_codiscrete_iff.mp hcod).2
  rw [ae_iff]
  simpa [Z,Set.preimage] using (hcount.preimage he).measure_zero (volume : Measure ℝ)

local notation "RadL2" => Lp ℂ 2 (volume : Measure ℝ)
local notation "B" => ContinuousLinearMap.mul ℂ ℂ

/-- A Schwartz convolution with a symbol having null level set at a scalar
has no continuous eigenfunctional at that value on the ordinary radial L² space. -/
private theorem no_regular_schwartz_convolution_eigenfunctional (k : 𝓢(ℝ,ℂ)) (c₀ : ℂ)
    (hc₀ : ∀ᵐ x : ℝ, 𝓕 k x ≠ c₀) (l : StrongDual ℂ RadL2)
    (hl : ∀ h : 𝓢(ℝ,ℂ), l ((SchwartzMap.convolution B k h).toLp 2) = c₀ * l (h.toLp 2)) :
    l = 0 := by
  let F := Lp.fourierTransformₗᵢ ℝ ℂ
  let p := 𝓕 k
  let pc : 𝓢(ℝ,ℂ) := SchwartzMap.postcompCLM Complex.conjCLE.toContinuousLinearMap p
  let M (b : 𝓢(ℝ,ℂ)) : RadL2 →L[ℂ] RadL2 := (B).holderL volume ⊤ 2 2 (b.toLp ⊤)
  have hM (b : 𝓢(ℝ,ℂ)) (v : RadL2) : (M b v : ℝ → ℂ) =ᵐ[volume] fun x ↦ b x * v x := by
    simp only [M, ContinuousLinearMap.holderL_apply_apply]
    filter_upwards [ContinuousLinearMap.coeFn_holder (r := 2) B (b.toLp ⊤) v, b.coeFn_toLp ⊤] with x hx hbx
    simpa only [ContinuousLinearMap.mul_apply',hbx] using hx
  have hconv (h : 𝓢(ℝ,ℂ)) :
      F ((SchwartzMap.convolution B k h).toLp 2) = M p (F (h.toLp 2)) := by
    change 𝓕 ((SchwartzMap.convolution B k h).toLp 2) = M p (𝓕 (h.toLp 2))
    rw [SchwartzMap.toLp_fourier_eq,SchwartzMap.toLp_fourier_eq,SchwartzMap.fourier_convolution]
    apply Lp.ext
    filter_upwards [(SchwartzMap.pairing B p (𝓕 h)).coeFn_toLp 2,
      hM p ((𝓕 h).toLp 2), (𝓕 h).coeFn_toLp 2] with x hx hpx hf
    rw [hx,hpx,hf]
    rfl
  let t : RadL2 := F ((InnerProductSpace.toDual ℂ RadL2).symm l)
  have ht (v : RadL2) : ⟪t,F v⟫_ℂ = l v := (F.inner_map_map _ _).trans InnerProductSpace.toDual_symm_apply
  have hE : ∀ v : RadL2, ⟪t,M p v⟫_ℂ = c₀ * ⟪t,v⟫_ℂ := by
    intro v
    have hd := F.surjective.denseRange.comp (SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℂ)
      (μ := (volume : Measure ℝ)) (p := 2) (by norm_num)) F.continuous
    refine hd.induction_on (p := fun v ↦ ⟪t,M p v⟫_ℂ = c₀ * ⟪t,v⟫_ℂ) v (isClosed_eq ?_ ?_) ?_
    · exact continuous_const.inner (M p).continuous
    · exact continuous_const.mul (continuous_const.inner continuous_id)
    intro h
    simp only [Function.comp_apply,SchwartzMap.toLpCLM_apply]
    rw [← hconv,ht,ht,hl]
  have hAdj (v : RadL2) : ⟪M pc t,v⟫_ℂ = ⟪t,M p v⟫_ℂ := by
    rw [L2.inner_def,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hM pc t, hM p v] with x hl hr
    rw [hl,hr]
    change v x * conj (conj (p x) * t x) = p x * v x * conj (t x)
    rw [map_mul,conj_conj]
    ring
  have he : M pc t = conj c₀ • t := ext_inner_right ℂ (fun v ↦ by
    rw [hAdj,hE,inner_smul_left]
    simp)
  have ht0 : t = 0 := by
    apply Lp.ext
    filter_upwards [hM pc t,Lp.coeFn_smul (conj c₀) t,Lp.coeFn_zero ℂ 2 (volume : Measure ℝ),hc₀]
      with x hpc hs hz hn
    rw [he] at hpc
    rw [hz]
    apply (mul_eq_zero.mp (show (conj (p x) - conj c₀) * t x = 0 from ?_)).resolve_left
    · apply sub_ne_zero.mpr
      exact fun heq ↦ hn (by simpa using congrArg (starRingEnd ℂ) heq)
    · rw [sub_mul,sub_eq_zero]
      exact hpc.symm.trans hs
  ext v
  exact (ht v).symm.trans (by simp [ht0])

/-- The Fourier symbol of a centered scalar radial kernel has null level sets
at each nonzero scalar when the log-Mellin transform vanishes at zero. -/
theorem centered_radial_convolution_no_eigenfunctional
    (g : ℝ → ℂ) (hg : Continuous g) (hc : HasCompactSupport g) (h0 : compactLogMellin g 0 = 0)
    (C : ℂ) (k : 𝓢(ℝ,ℂ)) (hk : ∀ x : ℝ, k x = C * (Complex.exp ((x:ℂ)/2) * g x))
    (c : ℂ) (hn : c ≠ 0) (l : StrongDual ℂ RadL2)
    (hl : ∀ h : 𝓢(ℝ,ℂ), l ((SchwartzMap.convolution B k h).toLp 2) = c * l (h.toLp 2)) :
    l = 0 := by
  let e (t : ℝ) : ℂ := 1/2 + ((-(2 * Real.pi * t) : ℝ) : ℂ) * Complex.I
  have hinj : Function.Injective e := by
    intro x y h
    apply mul_left_cancel₀ (show (2 * Real.pi : ℝ) ≠ 0 by positivity)
    simpa [e,Complex.mul_im] using congrArg Complex.im h
  have hs (t : ℝ) : 𝓕 k t = C * compactLogMellin g (e t) := by
    rw [congrFun (SchwartzMap.fourier_coe k) t,Real.fourier_eq',compactLogMellin,← integral_const_mul]
    apply integral_congr_ae (.of_forall fun x ↦ ?_)
    rw [hk,smul_eq_mul]
    have he : e t * (x:ℂ) = ((-2 * Real.pi * inner ℝ x t : ℝ) : ℂ) * Complex.I + x/2 := by
      dsimp only [e]
      rw [Real.inner_apply]
      push_cast
      ring
    rw [he,Complex.exp_add]
    ring
  apply no_regular_schwartz_convolution_eigenfunctional k c _ l hl
  filter_upwards [compactLogMellin_ae_ne_on_line g hg hc h0 C c hn e hinj] with t ht
  simpa only [hs] using ht


end RiemannMasullo.StripNuclearity
