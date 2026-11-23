module

public import RiemannMasullo.Ch10_TraceSpectral.Sec1

import all RiemannMasullo.AppA_AlgebraicNT.Sec3
import all RiemannMasullo.Ch06_LocalGlobal.Sec2
import RiemannMasullo.ForMathlib.Analysis.Distribution.SchwartzSpace.Gaussian
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID

/-! # §10.1 assertions that are false as printed -/

@[expose] public noncomputable section

open Filter IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal ENNReal NumberField.AdeleRing

namespace RiemannMasullo

local instance instSIdeleQuotientMeasurableSpaceSec1Printed
    (F : Type*) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) :
    MeasurableSpace (SIdeleQuotient F S) := borel _

local instance instIdeleClassMeasurableSpaceSec1Printed (F : Type*) [Field F] [NumberField F] :
    MeasurableSpace (IdeleClassGroup (𝓞 F) F) := borel _

local instance instNormOneSIdeleQuotientMeasurableSpaceSec1Printed
    (F : Type*) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) :
    MeasurableSpace (sIdeleQuotientNorm F S).ker := borel _

/-- Paper: Before (10.1.1.2), p. 434. The interval norm is finite on every
weighted global polar-free theta function for every closed interval with interior. -/
def Printed.globalThetaSobolev_closedIntervals_finite : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (a s : ℝ), 0 ≤ s →
    ∀ I : Set ℝ, IsClosed I → OrdConnected I → (interior I).Nonempty →
    ∀ f : adelePolarSubspace F,
      let m := (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ :
        IdeleClassGroup (𝓞 F) F →ₜ* ℝ≥0ˣ)
      intervalSobolevENorm (ideleClassTamagawaMeasure F) (fun g ↦ Real.log ((m g).val : ℝ))
        I s (modulationWeight m a (adelicTheta f.val)) ≠ ⊤

/-- Paper: Before (10.1.1.2), p. 434. Take ℚ, I = [0,∞), a = s = 0, finite
integer indicators and the real test (3x² − 2πx⁴) exp(-πx²). It is the derivative
of x³ exp(-πx²) and vanishes at zero. Its theta is strictly negative on [2,3].
The integral over that shell grows at least as a positive constant times 2^(2b)
when the subinterval is [0,b]. -/
theorem Printed.globalThetaSobolev_closedIntervals_finite_false :
    ¬ Printed.globalThetaSobolev_closedIntervals_finite := by sorry

/-- Paper: Before Lemma 10.1.1.4, p. 435. A positive twist of every local theta
test is asserted to belong to the Sobolev space for the whole half-line (-a,∞). -/
def Printed.sLocalThetaSobolev_openHalfLine_finite : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (a s : ℝ), 0 < a → 0 ≤ s → ∀ f : SchwartzBruhat (Multiplicative (SAdeleRing F S)),
      let m := (⟨sIdeleQuotientNorm F S, (isProperMap_sIdeleQuotientNorm F S).continuous⟩ :
        SIdeleQuotient F S →ₜ* ℝ≥0ˣ)
      intervalSobolevENorm (sLocalQuotientTamagawaMeasure F S)
        (fun g ↦ Real.log ((m g).val : ℝ)) (Ioi (-a)) s
        (modulationWeight m a (sLocalAdelicThetaOnClasses F S f)) ≠ ⊤

/-- Paper: Before Lemma 10.1.1.4, p. 435.
The Gaussian theta dominates its term at the identity S-unit. -/
private theorem sLocalThetaSobolev_openHalfLine_finite_false_theta_lower
    (f : SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅)))
    (hf : ∀ x : SAdeleRing ℚ ∅, f (Multiplicative.ofAdd x) =
      ((Real.exp (-‖x.1 Rat.infinitePlace‖ ^ 2) : ℝ) : ℂ))
    (x : (SAdeleRing ℚ ∅)ˣ) :
    Real.exp (-‖x.val.1 Rat.infinitePlace‖ ^ 2) ≤
      ‖sLocalAdelicThetaOnClasses ℚ ∅ f (QuotientGroup.mk x)‖ := by
  have hs := ((sLocalAdelicTheta_hasSumUniformlyOn ℚ ∅ f {x} isCompact_singleton).hasSum
    rfl).summable
  rw [sLocalAdelicThetaOnClasses_mk, sLocalAdelicTheta_apply]
  simp only [hf] at hs ⊢
  rw [← Complex.ofReal_tsum, Complex.norm_real, Real.norm_eq_abs]
  refine le_trans ?_ (le_abs_self _)
  have hr := Complex.summable_ofReal.mp hs
  refine le_trans (le_of_eq ?_) (hr.le_tsum 1 fun _ _ ↦ (Real.exp_pos _).le)
  simp

/-- Paper: Before Lemma 10.1.1.4, p. 435.
The rational Gaussian has nonzero theta at a class of norm two. -/
private theorem sLocalThetaSobolev_openHalfLine_finite_false_witness :
    ∃ f : SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅)),
      ∃ g : SIdeleQuotient ℚ ∅,
        1 < ((sIdeleQuotientNorm ℚ ∅ g).val : ℝ) ∧
        sLocalAdelicThetaOnClasses ℚ ∅ f g ≠ 0 := by
  obtain ⟨E, hE⟩ := ratTrivialHomogeneousTheta_quotient_realEquiv
  let φ : SchwartzMap ℝ ℂ := (SchwartzMap.gaussian 1 one_pos).postcompCLM Complex.ofRealCLM
  have hf : ∀ x : SAdeleRing ℚ ∅, E φ (Multiplicative.ofAdd x) =
      ((Real.exp (-‖x.1 Rat.infinitePlace‖ ^ 2) : ℝ) : ℂ) := by
    intro x
    rw [hE]
    have hn (z : Rat.infinitePlace.Completion) : ‖InfinitePlace.Completion.ringEquivRealOfIsReal
        Rat.isReal_infinitePlace z‖ = ‖z‖ := by
      rw [← dist_zero_right, ← dist_zero_right z,
        ← map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace)]
      exact (InfinitePlace.Completion.isometryEquivRealOfIsReal
        Rat.isReal_infinitePlace).dist_eq z 0
    have hφ (y : ℝ) : φ y = ((Real.exp (-‖y‖ ^ 2) : ℝ) : ℂ) := by
      change Complex.ofRealCLM (SchwartzMap.gaussian 1 one_pos y) = _
      rw [SchwartzMap.gaussian_apply, Complex.ofRealCLM_apply, neg_mul, one_mul]
    rw [hφ, hn]
  obtain ⟨σ, hσ⟩ := sIdeleQuotientNorm_exists_section (F := ℚ) (S := ∅)
  let u : ℝ≥0ˣ := Units.mk0 2 (by norm_num)
  let g : SIdeleQuotient ℚ ∅ := σ u
  have hg : 1 < ((sIdeleQuotientNorm ℚ ∅ g).val : ℝ) := by
    rw [show sIdeleQuotientNorm ℚ ∅ g = u from hσ u]
    norm_num [u]
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective g
  have hpos := sLocalThetaSobolev_openHalfLine_finite_false_theta_lower (E φ) hf x
  refine ⟨E φ, g, hg, ?_⟩
  rw [← hx]
  exact norm_pos_iff.mp (lt_of_lt_of_le (Real.exp_pos _) hpos)

/-- Paper: Before Lemma 10.1.1.4, p. 435.
A continuous nonzero function at positive log norm has infinite whole half-line Sobolev norm. -/
private theorem sLocalThetaSobolev_openHalfLine_finite_false_unbounded
    {G : Type*} [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
    (μ : Measure G) [μ.IsOpenPosMeasure]
    (r : G → ℝ) (hr : Continuous r) (θ : G → ℂ) (hθ : Continuous θ)
    (g : G) (hrg : 0 < r g) (hθg : θ g ≠ 0) :
    intervalSobolevENorm μ r (Ioi (-1)) 0 θ = ⊤ := by
  let c := ‖θ g‖ / 2
  have hc : 0 < c := half_pos (norm_pos_iff.mpr hθg)
  have hcg : c < ‖θ g‖ := half_lt_self (norm_pos_iff.mpr hθg)
  let U := {x | c < ‖θ x‖} ∩ {x | r g / 2 < r x}
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const hθ.norm).inter (isOpen_lt continuous_const hr)
  have hgU : g ∈ U := ⟨hcg, half_lt_self hrg⟩
  have hUpos : μ U ≠ 0 := (hUo.measure_pos μ ⟨g, hgU⟩).ne'
  have hε : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.mpr hc).ne'
  have hbound : ∀ σ : ℝ, 0 ≤ σ → ENNReal.ofReal (Real.exp (σ * r g)) * μ U ≤
      (ENNReal.ofReal c)⁻¹ ^ (2 : ℝ≥0∞).toReal *
        intervalSobolevENorm μ r (Ioi (-1)) 0 θ ^ (2 : ℝ≥0∞).toReal := by
    intro σ hσ
    have hle : eLpNorm θ 2 (μ.withDensity fun x ↦
        ENNReal.ofReal (intervalSobolevDensity 0 σ 0 (r x))) ≤
        intervalSobolevENorm μ r (Ioi (-1)) 0 θ := by
      unfold intervalSobolevENorm
      exact le_iSup₂_of_le (⟨0, by norm_num⟩ : Ioi (-1 : ℝ))
        (⟨σ, by change -1 < σ; linarith⟩ : Ioi (-1 : ℝ)) le_rfl
    have hdens : ∀ x ∈ U, ENNReal.ofReal (Real.exp (σ * r g)) ≤
        ENNReal.ofReal (intervalSobolevDensity 0 σ 0 (r x)) := by
      intro x hx
      apply ENNReal.ofReal_le_ofReal
      have he : Real.exp (σ * r g) ≤ Real.exp (2 * σ * r x) :=
        Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hx.2.le hσ])
      simpa only [intervalSobolevDensity, zero_div, Real.rpow_zero, mul_one] using
        he.trans (le_max_right (Real.exp (2 * 0 * r x)) _)
    calc ENNReal.ofReal (Real.exp (σ * r g)) * μ U
        = ∫⁻ _ in U, ENNReal.ofReal (Real.exp (σ * r g)) ∂μ := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ x in U, ENNReal.ofReal (intervalSobolevDensity 0 σ 0 (r x)) ∂μ :=
          setLIntegral_mono' hUo.measurableSet hdens
      _ = (μ.withDensity fun x ↦ ENNReal.ofReal (intervalSobolevDensity 0 σ 0 (r x))) U :=
          (withDensity_apply _ hUo.measurableSet).symm
      _ ≤ (μ.withDensity fun x ↦ ENNReal.ofReal (intervalSobolevDensity 0 σ 0 (r x)))
            {x | ENNReal.ofReal c ≤ ‖θ x‖ₑ} := measure_mono fun x hx ↦ by
          rw [mem_ofPred_eq, ← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal hx.1.le
      _ ≤ (ENNReal.ofReal c)⁻¹ ^ (2 : ℝ≥0∞).toReal * eLpNorm θ 2 (μ.withDensity fun x ↦
            ENNReal.ofReal (intervalSobolevDensity 0 σ 0 (r x))) ^ (2 : ℝ≥0∞).toReal :=
          meas_ge_le_mul_pow_eLpNorm_eNorm _ two_ne_zero ENNReal.ofNat_ne_top hε
            fun h ↦ absurd h ENNReal.ofReal_ne_top
      _ ≤ _ := by gcongr
  by_contra htop
  have hBtop : (ENNReal.ofReal c)⁻¹ ^ (2 : ℝ≥0∞).toReal *
      intervalSobolevENorm μ r (Ioi (-1)) 0 θ ^ (2 : ℝ≥0∞).toReal ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by simp) (ENNReal.inv_ne_top.mpr hε))
      (ENNReal.rpow_ne_top_of_nonneg (by simp) htop)
  obtain ⟨K, hK, hKle⟩ : ∃ K : ℝ≥0∞, K ≠ ∞ ∧
      ∀ σ : ℝ, 0 ≤ σ → ENNReal.ofReal (Real.exp (σ * r g)) ≤ K :=
    ⟨_, ENNReal.div_ne_top hBtop hUpos, fun σ hσ ↦
      (ENNReal.le_div_iff_mul_le (Or.inl hUpos) (Or.inr hBtop)).mpr (hbound σ hσ)⟩
  have hlt : K.toReal < Real.exp (max 0 (K.toReal / r g) * r g) := by
    have h := (div_le_iff₀ hrg).mp (le_max_right 0 (K.toReal / r g))
    linarith [Real.add_one_le_exp (max 0 (K.toReal / r g) * r g)]
  exact absurd (hKle _ (le_max_left _ _))
    (not_le.mpr ((ENNReal.lt_ofReal_iff_toReal_lt hK).mpr hlt))

/-- Paper: Before Lemma 10.1.1.4, p. 435. For ℚ, S = {∞}, a = 1, s = 0,
and the real Gaussian, the weighted theta is positive throughout [2,3].
Already the intervals [0,b] give unbounded norms as b tends to infinity. -/
theorem Printed.sLocalThetaSobolev_openHalfLine_finite_false :
    ¬ Printed.sLocalThetaSobolev_openHalfLine_finite := by
  intro h
  obtain ⟨f, g, hg, hθg⟩ := sLocalThetaSobolev_openHalfLine_finite_false_witness
  let m : SIdeleQuotient ℚ ∅ →ₜ* ℝ≥0ˣ :=
    ⟨sIdeleQuotientNorm ℚ ∅, (isProperMap_sIdeleQuotientNorm ℚ ∅).continuous⟩
  let r : SIdeleQuotient ℚ ∅ → ℝ := fun x ↦ Real.log ((m x).val : ℝ)
  let θ := modulationWeight m 1 (sLocalAdelicThetaOnClasses ℚ ∅ f)
  have hr : Continuous r := by
    exact Real.continuousOn_log.comp_continuous
      (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous))
      (fun _ ↦ (NNReal.coe_pos.mpr (Units.zero_lt _)).ne')
  have hθ : Continuous θ := by
    dsimp [θ, modulationWeight]
    fun_prop
  have hrg : 0 < r g := Real.log_pos hg
  have hθg' : θ g ≠ 0 := by
    dsimp [θ, modulationWeight]
    exact mul_ne_zero (by exact_mod_cast (pow_ne_zero 1 (Units.ne_zero (m g)))) hθg
  have hHaar : (sLocalQuotientTamagawaMeasure ℚ ∅).IsHaarMeasure :=
    (sLocalQuotientTamagawaMeasure_isWeil (F := ℚ) (S := ∅)).1
  have hOpen : (sLocalQuotientTamagawaMeasure ℚ ∅).IsOpenPosMeasure :=
    hHaar.toIsOpenPosMeasure
  let : BorelSpace (SIdeleQuotient ℚ ∅) := ⟨rfl⟩
  have htop := @sLocalThetaSobolev_openHalfLine_finite_false_unbounded
    (SIdeleQuotient ℚ ∅) inferInstance inferInstance inferInstance
    (sLocalQuotientTamagawaMeasure ℚ ∅) hOpen r hr θ hθ g hrg hθg'
  have hfin := h ℚ ∅ 1 0 one_pos le_rfl f
  exact hfin htop


/-- Paper: Definition 10.1.1.1(2) and Remark 10.1.1.2, p. 434. As printed,
the integral defining the local norm is finite at every positive weight and
every compact nonempty interval. -/
def Printed.sLocalThetaSobolev_integrable : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (a α β s : ℝ), 0 < a → α ≤ β → 0 ≤ s →
    ∀ f : SchwartzBruhat (Multiplicative (SAdeleRing F S)),
      Integrable (fun g : SIdeleQuotient F S ↦ ‖sLocalAdelicThetaOnClasses F S f g‖ ^ 2 *
        intervalSobolevDensity (a + α) (a + β) s
          (Real.log ((sIdeleQuotientNorm F S g).val : ℝ))) (sLocalQuotientTamagawaMeasure F S)

private theorem sLocalThetaSobolev_integrable_false_measure {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsOpenPosMeasure]
    (N : G →* ℝ≥0ˣ) (hN : Continuous N) (hs : Function.Surjective N) :
    μ {g | ((N g : ℝ≥0) : ℝ) < 1} = ⊤ := by
  obtain ⟨t, ht⟩ := hs (Units.mk0 (2 : ℝ≥0) two_ne_zero)
  obtain ⟨g₀, hg₀⟩ := hs (Units.mk0 (3 / 4 : ℝ≥0) (by norm_num))
  have hcont : Continuous fun g ↦ ((N g : ℝ≥0) : ℝ) :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp hN)
  let A : Set G := {g | 1 / 2 < ((N g : ℝ≥0) : ℝ) ∧ ((N g : ℝ≥0) : ℝ) < 1}
  have hAo : IsOpen A :=
    (isOpen_lt continuous_const hcont).inter (isOpen_lt hcont continuous_const)
  have hg₀A : g₀ ∈ A := by
    simp only [A, mem_setOf_eq, hg₀, Units.val_mk0, NNReal.coe_div, NNReal.coe_ofNat]
    norm_num
  have hA0 : μ A ≠ 0 := (hAo.measure_pos μ ⟨g₀, hg₀A⟩).ne'
  let B (k : ℕ) : Set G := (fun g ↦ t ^ k * g) ⁻¹' A
  have hB (k : ℕ) (g : G) : g ∈ B k ↔
      1 / 2 < 2 ^ k * ((N g : ℝ≥0) : ℝ) ∧ 2 ^ k * ((N g : ℝ≥0) : ℝ) < 1 := by
    show (1 / 2 < ((N (t ^ k * g) : ℝ≥0) : ℝ) ∧ ((N (t ^ k * g) : ℝ≥0) : ℝ) < 1) ↔ _
    rw [map_mul, map_pow, ht]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0, NNReal.coe_mul,
      NNReal.coe_pow, NNReal.coe_ofNat]
  have hmeas (k : ℕ) : μ (B k) = μ A := measure_preimage_mul μ (t ^ k) A
  have hdisj : Pairwise (Function.onFun Disjoint B) := by
    have key (k l : ℕ) (h : k < l) (g : G) (h1 : g ∈ B k) (h2 : g ∈ B l) : False := by
      rw [hB] at h1 h2
      have h2l : (2 : ℝ) * 2 ^ k ≤ 2 ^ l := by
        calc (2 : ℝ) * 2 ^ k = 2 ^ (k + 1) := by ring
          _ ≤ 2 ^ l := pow_le_pow_right₀ (by norm_num) h
      have hr : 0 ≤ ((N g : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
      nlinarith
    intro k l hkl
    rw [Function.onFun, Set.disjoint_left]
    intro g h1 h2
    rcases lt_or_gt_of_ne hkl with h | h
    · exact key k l h g h1 h2
    · exact key l k h g h2 h1
  have hsub : (⋃ k, B k) ⊆ {g | ((N g : ℝ≥0) : ℝ) < 1} := by
    intro g hg
    obtain ⟨k, hk⟩ := mem_iUnion.mp hg
    rw [hB] at hk
    have h1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    have hr : 0 ≤ ((N g : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
    simp only [mem_setOf_eq]
    nlinarith
  refine eq_top_mono (measure_mono hsub) ?_
  rw [measure_iUnion hdisj (fun k ↦ (measurable_const_mul (t ^ k)) hAo.measurableSet)]
  simp only [hmeas]
  exact ENNReal.tsum_const_eq_top_of_ne_zero hA0


private theorem sLocalThetaSobolev_integrable_false_norm (x : (SAdeleRing ℚ ∅)ˣ) :
    ((sIdeleNorm ℚ ∅ x : ℝ≥0) : ℝ) = ‖x.val.1 Rat.infinitePlace‖ := by
  simp [sIdeleNorm]
  rw [Unique.eq_default Rat.infinitePlace]

private theorem sLocalThetaSobolev_integrable_false_theta
    (f : SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅)))
    (hf : ∀ x : SAdeleRing ℚ ∅, f (Multiplicative.ofAdd x) =
      ((Real.exp (-‖x.1 Rat.infinitePlace‖ ^ 2) : ℝ) : ℂ))
    (x : (SAdeleRing ℚ ∅)ˣ) :
    Real.exp (-‖x.val.1 Rat.infinitePlace‖ ^ 2) ≤
      ‖sLocalAdelicThetaOnClasses ℚ ∅ f (QuotientGroup.mk x)‖ := by
  have hs := ((sLocalAdelicTheta_hasSumUniformlyOn ℚ ∅ f {x} isCompact_singleton).hasSum
    rfl).summable
  rw [sLocalAdelicThetaOnClasses_mk, sLocalAdelicTheta_apply]
  simp only [hf] at hs ⊢
  rw [← Complex.ofReal_tsum, Complex.norm_real, Real.norm_eq_abs]
  refine le_trans ?_ (le_abs_self _)
  have hr := Complex.summable_ofReal.mp hs
  refine le_trans (le_of_eq ?_) (hr.le_tsum 1 fun _ _ ↦ (Real.exp_pos _).le)
  simp

/-- Paper: Definition 10.1.1.1(2) and Remark 10.1.1.2, p. 434.
For ℚ with S consisting of the real place, take f(x) = exp(-πx²), a = 1,
I = {-1} and s = 0. The two S-units give theta(t) = 2 exp(-πt²), whose
square is not integrable near zero against dt/t. -/
theorem Printed.sLocalThetaSobolev_integrable_false :
    ¬ Printed.sLocalThetaSobolev_integrable := by
  intro h
  obtain ⟨E, hE⟩ := ratTrivialHomogeneousTheta_quotient_realEquiv
  let φ : SchwartzMap ℝ ℂ := (SchwartzMap.gaussian 1 one_pos).postcompCLM Complex.ofRealCLM
  have hf : ∀ x : SAdeleRing ℚ ∅, E φ (Multiplicative.ofAdd x) =
      ((Real.exp (-‖x.1 Rat.infinitePlace‖ ^ 2) : ℝ) : ℂ) := by
    intro x
    rw [hE]
    have hn (z : Rat.infinitePlace.Completion) : ‖InfinitePlace.Completion.ringEquivRealOfIsReal
        Rat.isReal_infinitePlace z‖ = ‖z‖ := by
      rw [← dist_zero_right, ← dist_zero_right z,
        ← map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace)]
      exact (InfinitePlace.Completion.isometryEquivRealOfIsReal
        Rat.isReal_infinitePlace).dist_eq z 0
    have hφ (y : ℝ) : φ y = ((Real.exp (-‖y‖ ^ 2) : ℝ) : ℂ) := by
      change Complex.ofRealCLM (SchwartzMap.gaussian 1 one_pos y) = _
      rw [SchwartzMap.gaussian_apply, Complex.ofRealCLM_apply, neg_mul, one_mul]
    rw [hφ, hn]
  have hint := h ℚ ∅ 1 (-1) (-1) 0 one_pos le_rfl le_rfl (E φ)
  let θ := sLocalAdelicThetaOnClasses ℚ ∅ (E φ)
  have hint' : Integrable (fun g ↦ ‖θ g‖ ^ 2) (sLocalQuotientTamagawaMeasure ℚ ∅) :=
    hint.congr (Eventually.of_forall fun g ↦ by simp only [θ]; norm_num [intervalSobolevDensity])
  have : BorelSpace (SIdeleQuotient ℚ ∅) := ⟨rfl⟩
  have hW := sLocalQuotientTamagawaMeasure_isWeil (F := ℚ) (S := ∅)
  have : (sLocalQuotientTamagawaMeasure ℚ ∅).IsHaarMeasure := hW.1
  obtain ⟨σ, hσ⟩ := sIdeleQuotientNorm_exists_section (F := ℚ) (S := ∅)
  have hNc : Continuous (sIdeleQuotientNorm ℚ ∅) := (isProperMap_sIdeleQuotientNorm ℚ ∅).continuous
  have hB := sLocalThetaSobolev_integrable_false_measure (sLocalQuotientTamagawaMeasure ℚ ∅)
    (sIdeleQuotientNorm ℚ ∅) hNc hσ.surjective
  let B := {g : SIdeleQuotient ℚ ∅ | ((sIdeleQuotientNorm ℚ ∅ g : ℝ≥0) : ℝ) < 1}
  have hBm : MeasurableSet B :=
    (isOpen_lt (NNReal.continuous_coe.comp (Units.continuous_val.comp hNc))
      continuous_const).measurableSet
  have hlow : ∀ g ∈ B, ENNReal.ofReal (Real.exp (-1) ^ 2) ≤ ‖‖θ g‖ ^ 2‖ₑ := by
    intro g hg
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
    have hx : ‖x.val.1 Rat.infinitePlace‖ < 1 := by
      rw [← sLocalThetaSobolev_integrable_false_norm]
      exact hg
    have h1 := sLocalThetaSobolev_integrable_false_theta (E φ) hf x
    have h2 : Real.exp (-1) ≤ Real.exp (-‖x.val.1 Rat.infinitePlace‖ ^ 2) := by
      gcongr
      nlinarith [norm_nonneg (x.val.1 Rat.infinitePlace)]
    rw [Real.eNorm_eq_ofReal (by positivity)]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (Real.exp_pos _).le (h2.trans h1) 2)
  have hfin : (∫⁻ g, ‖‖θ g‖ ^ 2‖ₑ ∂sLocalQuotientTamagawaMeasure ℚ ∅) < ⊤ :=
    hint'.hasFiniteIntegral
  have hBdef : B = {g : SIdeleQuotient ℚ ∅ | ((sIdeleQuotientNorm ℚ ∅ g : ℝ≥0) : ℝ) < 1} := rfl
  have hge : ⊤ ≤ ∫⁻ g, ‖‖θ g‖ ^ 2‖ₑ ∂sLocalQuotientTamagawaMeasure ℚ ∅ :=
    calc (⊤ : ℝ≥0∞) = ENNReal.ofReal (Real.exp (-1) ^ 2) * sLocalQuotientTamagawaMeasure ℚ ∅ B := by
          rw [hBdef, hB, ENNReal.mul_top (by positivity)]
      _ = ∫⁻ _ in B, ENNReal.ofReal (Real.exp (-1) ^ 2) ∂sLocalQuotientTamagawaMeasure ℚ ∅ :=
          (setLIntegral_const B _).symm
      _ ≤ ∫⁻ g in B, ‖‖θ g‖ ^ 2‖ₑ ∂sLocalQuotientTamagawaMeasure ℚ ∅ :=
          setLIntegral_mono' hBm hlow
      _ ≤ _ := setLIntegral_le_lintegral B _
  exact absurd (lt_of_le_of_lt hge hfin) (lt_irrefl _)


/-- Paper: Proof of Lemma 10.1.1.4(1), p. 436. As printed, the density of
the weighted S-idele measure vanishes at infinity. -/
def Printed.sIdeleIntervalSobolevDensity_vanishesAtInfinity : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (α β s : ℝ), α ≤ β → 0 ≤ s →
    Tendsto (fun g : (SAdeleRing F S)ˣ ↦
      intervalSobolevDensity α β s (Real.log ((sIdeleNorm F S g).val : ℝ)))
      (cocompact _) (nhds 0)

private theorem sIdeleNorm_vanishesAtInfinity_false_cont (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    Continuous (sIdeleNorm F S) := by
  suffices H : Continuous (fun g ↦ sIdeleNorm F S g) from H
  simp only [sIdeleNorm, MonoidHom.mul_apply, MonoidHom.finsetProd_apply, MonoidHom.pow_apply,
    MonoidHom.comp_apply]
  refine Continuous.mul ?_ ?_
  · refine continuous_finsetProd _ fun w _ ↦ ?_
    refine Continuous.pow ?_ _
    exact (continuous_nnNorm.units_map _).comp
      ((((continuous_apply w).comp continuous_fst).units_map _))
  · refine continuous_finsetProd _ fun v _ ↦ ?_
    exact (continuous_nnNorm.units_map _).comp
      ((((continuous_apply v).comp continuous_snd).units_map _))

private theorem sIdeleNorm_vanishesAtInfinity_false_diag :
    ((sIdeleNorm ℚ (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))
      (Units.map ((algebraMap ℚ (InfiniteAdeleRing ℚ)).prod
        (RingHom.pi fun v : (∅ : Finset (HeightOneSpectrum (𝓞 ℚ))) ↦
          algebraMap ℚ (v.val.adicCompletion ℚ))).toMonoidHom (Units.mk0 (2 : ℚ) two_ne_zero))).val : ℝ) = 2 := by
  simp only [sIdeleNorm, MonoidHom.finsetProd_apply, MonoidHom.pow_apply,
    MonoidHom.comp_apply, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
  rw [Units.coe_prod, NNReal.coe_prod]
  have h2 := InfinitePlace.prod_eq_abs_norm (K := ℚ) 2
  rw [show (|(Algebra.norm ℚ) (2:ℚ)| : ℚ) = 2 by simp [Algebra.norm_self]] at h2
  rw [← (by norm_num : (((2:ℚ)) : ℝ) = 2), ← h2]
  refine Finset.prod_congr rfl fun w _ ↦ ?_
  rw [Units.val_pow_eq_pow_val, NNReal.coe_pow]
  congr 1
  change ‖(algebraMap ℚ (InfiniteAdeleRing ℚ) 2) w‖ = _
  rw [InfiniteAdeleRing.algebraMap_apply]
  exact AbsoluteValue.Completion.norm_coe (2 : WithAbs w.1)

private theorem sIdeleNorm_vanishesAtInfinity_false_noncompact :
    ¬ CompactSpace (SAdeleRing ℚ (∅ : Finset (HeightOneSpectrum (𝓞 ℚ))))ˣ := by
  intro hc
  let u := Units.map ((algebraMap ℚ (InfiniteAdeleRing ℚ)).prod
        (RingHom.pi fun v : (∅ : Finset (HeightOneSpectrum (𝓞 ℚ))) ↦
          algebraMap ℚ (v.val.adicCompletion ℚ))).toMonoidHom (Units.mk0 (2 : ℚ) two_ne_zero)
  have hu := sIdeleNorm_vanishesAtInfinity_false_diag
  have hcont : Continuous fun g : (SAdeleRing ℚ (∅ : Finset (HeightOneSpectrum (𝓞 ℚ))))ˣ ↦
      ((sIdeleNorm ℚ ∅ g).val : ℝ) :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp (sIdeleNorm_vanishesAtInfinity_false_cont ℚ ∅))
  obtain ⟨C, hC⟩ := (isCompact_range hcont).isBounded.subset_closedBall 0
  have hn : ∀ n : ℕ, ((sIdeleNorm ℚ ∅ (u ^ n)).val : ℝ) = 2 ^ n := fun n ↦ by
    rw [map_pow, Units.val_pow_eq_pow_val, NNReal.coe_pow, hu]
  obtain ⟨n, hn'⟩ := pow_unbounded_of_one_lt C (by norm_num : (1 : ℝ) < 2)
  have : ((sIdeleNorm ℚ ∅ (u ^ n)).val : ℝ) ∈ Metric.closedBall 0 C := hC ⟨u ^ n, rfl⟩
  rw [hn n] at this
  simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 ^ n)] at this
  linarith


/-- Paper: Proof of Lemma 10.1.1.4(1), p. 436. For ℚ with S the real place,
I = {1} and s = 0, the density is t² on the positive ideles t, so it
grows without bound as t tends to infinity. -/
theorem Printed.sIdeleIntervalSobolevDensity_vanishesAtInfinity_false :
    ¬ Printed.sIdeleIntervalSobolevDensity_vanishesAtInfinity := by
  intro h
  have h1 := h ℚ ∅ 0 0 0 le_rfl le_rfl
  have hconst : (fun g : (SAdeleRing ℚ (∅ : Finset (HeightOneSpectrum (𝓞 ℚ))))ˣ ↦
      intervalSobolevDensity 0 0 0 (Real.log ((sIdeleNorm ℚ ∅ g).val : ℝ))) = fun _ ↦ 1 := by
    funext g
    simp [intervalSobolevDensity]
  rw [hconst] at h1
  have : NoncompactSpace (SAdeleRing ℚ (∅ : Finset (HeightOneSpectrum (𝓞 ℚ))))ˣ :=
    not_compactSpace_iff.mp sIdeleNorm_vanishesAtInfinity_false_noncompact
  exact one_ne_zero (tendsto_nhds_unique h1 tendsto_const_nhds).symm

/-- Paper: Proposition 10.1.1.5, pp. 436–437. As printed, the global Sobolev
completion in the proposition uses theta functions of all Schwartz–Bruhat tests.
The proposed completion requires their weighted square integrability. -/
def Printed.globalThetaSobolev_allTests_integrable : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (a α β s : ℝ), α ≤ β → 0 ≤ s →
    ∀ f : SchwartzBruhat (Multiplicative (AdeleRing (𝓞 F) F)),
      Integrable (fun g : IdeleClassGroup (𝓞 F) F ↦ ‖adelicTheta f g‖ ^ 2 *
        intervalSobolevDensity (a + α) (a + β) s
          (Real.log ((ideleClassNorm F g).val : ℝ))) (ideleClassTamagawaMeasure F)

/-- Paper: Proposition 10.1.1.5, pp. 436–437. A test with vanishing value
at zero and Fourier value one has theta bounded below near norm zero. -/
private theorem globalThetaSobolev_allTests_integrable_false_lower_bound :
    ∃ f : SchwartzBruhat (Multiplicative (AdeleRing (𝓞 ℚ) ℚ)), ∃ ε : ℝ,
      0 < ε ∧ ∀ g : IdeleClassGroup (𝓞 ℚ) ℚ,
        ((ideleClassNorm ℚ g).val : ℝ) < ε → 1 ≤ ‖adelicTheta f g‖ := by
  obtain ⟨f, hf⟩ := adelePolarValues_surjective (F := ℚ) (0, 1)
  let z : Multiplicative (AdeleRing (𝓞 ℚ) ℚ) := Multiplicative.ofAdd 0
  let t (g : IdeleClassGroup (𝓞 ℚ) ℚ) : ℝ := ((ideleClassNorm ℚ g).val : ℝ)
  have hf₀ : f z = 0 := congrArg Prod.fst hf
  have hF₀ : adeleSchwartzFourier f z = 1 := congrArg Prod.snd hf
  obtain ⟨C, T, hC, hT, hsmall⟩ := adelicTheta_decay_small f 0
  refine ⟨f, min T (1 / (C + 1)), lt_min hT (by positivity), ?_⟩
  intro g hg
  have ht : 0 < t g := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hgt : t g < T := lt_of_lt_of_le hg (min_le_left _ _)
  have hgc : t g < 1 / (C + 1) := lt_of_lt_of_le hg (min_le_right _ _)
  have hbound : ‖adelicTheta f g - (t g)⁻¹ • (1 : ℂ)‖ ≤ C := by
    simpa only [t, z, hf₀, hF₀, add_zero, pow_zero, mul_one] using hsmall g hgt
  have hnorm : ‖(t g)⁻¹ • (1 : ℂ)‖ = (t g)⁻¹ := by
    simp only [norm_smul, norm_one, mul_one, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr ht)]
  have htri : ‖(t g)⁻¹ • (1 : ℂ)‖ ≤
      ‖adelicTheta f g‖ + ‖adelicTheta f g - (t g)⁻¹ • (1 : ℂ)‖ := by
    exact norm_le_norm_add_norm_sub _ _
  have hC1 : 0 < C + 1 := by linarith
  have hinv : C + 1 < (t g)⁻¹ := by
    exact (lt_inv_comm₀ ht hC1).mp (by simpa only [one_div] using hgc)
  rw [hnorm] at htri
  linarith

/-- Paper: Proposition 10.1.1.5, pp. 436–437. Every positive radius has
an infinite-measure small-norm region in the idele class group of ℚ. -/
private theorem globalThetaSobolev_allTests_integrable_false_small_norm_measure
    (ε : ℝ) (hε : 0 < ε) :
    ideleClassTamagawaMeasure ℚ
      {g : IdeleClassGroup (𝓞 ℚ) ℚ | ((ideleClassNorm ℚ g).val : ℝ) < ε} = ⊤ := by
  let : BorelSpace (IdeleClassGroup (𝓞 ℚ) ℚ) := ⟨rfl⟩
  let : (ideleClassTamagawaMeasure ℚ).IsHaarMeasure :=
    (ideleClassTamagawaMeasure_isWeil ℚ).1
  have hNc : Continuous (ideleClassNorm ℚ) := (isProperMap_ideleClassNorm ℚ).continuous
  have hs : Function.Surjective (ideleClassNorm ℚ) := by
    intro t
    refine ⟨QuotientGroup.mk (canonicalIdeleNormSection ℚ t), ?_⟩
    exact canonicalIdeleNormSection_rightInverse ℚ t
  have hB := sLocalThetaSobolev_integrable_false_measure
    (ideleClassTamagawaMeasure ℚ) (ideleClassNorm ℚ) hNc hs
  have hε0 : (⟨ε, hε.le⟩ : ℝ≥0) ≠ 0 := by
    intro h
    exact hε.ne' (by simpa using congrArg Subtype.val h)
  let t : ℝ≥0ˣ := Units.mk0 ⟨ε, hε.le⟩ hε0
  let u : IdeleClassGroup (𝓞 ℚ) ℚ := QuotientGroup.mk (canonicalIdeleNormSection ℚ t)
  have hu : ideleClassNorm ℚ u = t := canonicalIdeleNormSection_rightInverse ℚ t
  have hset : {g : IdeleClassGroup (𝓞 ℚ) ℚ |
      ((ideleClassNorm ℚ g).val : ℝ) < ε} =
      (fun g ↦ u⁻¹ * g) ⁻¹' {g | ((ideleClassNorm ℚ g).val : ℝ) < 1} := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, map_mul, map_inv, hu,
      Units.val_mul, Units.val_inv_eq_inv_val, NNReal.coe_mul, NNReal.coe_inv]
    change ((ideleClassNorm ℚ g).val : ℝ) < ε ↔
      ε⁻¹ * ((ideleClassNorm ℚ g).val : ℝ) < 1
    simpa only [mul_one] using
      ((inv_mul_lt_iff₀ hε).symm :
        ((ideleClassNorm ℚ g).val : ℝ) < ε * 1 ↔
          ε⁻¹ * ((ideleClassNorm ℚ g).val : ℝ) < 1)
  rw [hset, measure_preimage_mul (ideleClassTamagawaMeasure ℚ) u⁻¹, hB]

/-- Paper: Proposition 10.1.1.5, pp. 436–437. For ℚ, set a = s = 0
and I = {0}. The real Gaussian times the characteristic functions of the finite
integer rings has theta(t) = Σ_{n ≠ 0} exp(-πn²t²), asymptotic to 1/t at zero
on each norm-one fibre, so its square is not integrable. -/
theorem Printed.globalThetaSobolev_allTests_integrable_false :
    ¬ Printed.globalThetaSobolev_allTests_integrable := by
  let : BorelSpace (IdeleClassGroup (𝓞 ℚ) ℚ) := ⟨rfl⟩
  intro h
  obtain ⟨f, ε, hε, hθ⟩ := globalThetaSobolev_allTests_integrable_false_lower_bound
  have hint := h ℚ 0 0 0 0 le_rfl le_rfl f
  have hint' : Integrable (fun g : IdeleClassGroup (𝓞 ℚ) ℚ ↦ ‖adelicTheta f g‖ ^ 2)
      (ideleClassTamagawaMeasure ℚ) :=
    hint.congr (Eventually.of_forall fun g ↦ by norm_num [intervalSobolevDensity])
  let B := {g : IdeleClassGroup (𝓞 ℚ) ℚ | ((ideleClassNorm ℚ g).val : ℝ) < ε}
  have hNc : Continuous (ideleClassNorm ℚ) := (isProperMap_ideleClassNorm ℚ).continuous
  have hBm : MeasurableSet B :=
    (isOpen_lt (NNReal.continuous_coe.comp (Units.continuous_val.comp hNc))
      continuous_const).measurableSet
  have hlow : ∀ g ∈ B, (1 : ℝ≥0∞) ≤ ‖‖adelicTheta f g‖ ^ 2‖ₑ := by
    intro g hg
    have hsq : (1 : ℝ) ≤ ‖adelicTheta f g‖ ^ 2 := by
      nlinarith [hθ g hg]
    rw [Real.eNorm_eq_ofReal (sq_nonneg _)]
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hsq
  have hfin : (∫⁻ g, ‖‖adelicTheta f g‖ ^ 2‖ₑ ∂ideleClassTamagawaMeasure ℚ) < ⊤ :=
    hint'.hasFiniteIntegral
  have hB : ideleClassTamagawaMeasure ℚ B = ⊤ :=
    globalThetaSobolev_allTests_integrable_false_small_norm_measure ε hε
  have hge : ⊤ ≤ ∫⁻ g, ‖‖adelicTheta f g‖ ^ 2‖ₑ ∂ideleClassTamagawaMeasure ℚ :=
    calc (⊤ : ℝ≥0∞) = (1 : ℝ≥0∞) * ideleClassTamagawaMeasure ℚ B := by rw [hB]; simp
      _ = ∫⁻ _ in B, (1 : ℝ≥0∞) ∂ideleClassTamagawaMeasure ℚ :=
          (setLIntegral_const B _).symm
      _ ≤ ∫⁻ g in B, ‖‖adelicTheta f g‖ ^ 2‖ₑ ∂ideleClassTamagawaMeasure ℚ :=
          setLIntegral_mono' hBm hlow
      _ ≤ _ := setLIntegral_le_lintegral B _
  exact absurd (lt_of_le_of_lt hge hfin) (lt_irrefl _)

/-- A test quotient completes in its weighted function norm when its evaluation on
representatives gives an injective dense map to a closed subspace of the ambient L². -/
def Printed.IsFunctionCompletionMap {G B X W : Type*} [MeasurableSpace G]
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [NormedAddCommGroup W] [NormedSpace ℂ W]
    (μ : Measure G) (rep : W → G → ℂ) (H : Submodule ℂ W)
    (q : B → X) (θ : B → G → ℂ) (j : X →L[ℂ] H) : Prop :=
  IsClosed (H : Set W) ∧ Function.Injective j ∧ DenseRange j ∧
    ∀ f, rep (j (q f)).val =ᵐ[μ] θ f

/-- The product of the test quotient maps extends to a continuous injection of
the function-norm completions and factors through a surjective Hilbert-sum isometry.
The completions are quantified so the statement also makes sense when a proposed
test function fails to belong to the ambient L². -/
def Printed.HasHomogeneousSobolevFactorization {G B X W Ω : Type*} {Y : Ω → Type*}
    [MeasurableSpace G] [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [∀ i, AddCommGroup (Y i)] [∀ i, Module ℂ (Y i)] [∀ i, TopologicalSpace (Y i)]
    [NormedAddCommGroup W] [NormedSpace ℂ W]
    (μ : Measure G) (rep : W → G → ℂ) (q : B → X) (qω : ∀ i, B → Y i)
    (θ : B → G → ℂ) (θω : Ω → B → G → ℂ) : Prop :=
  ∃ (H : Submodule ℂ W) (K : Ω → Submodule ℂ W)
    (j : X →L[ℂ] H) (k : ∀ i, Y i →L[ℂ] K i)
    (Q : H →L[ℂ] (∀ i, K i)) (T : H ≃ₗᵢ[ℂ] lp (fun i ↦ ↥(K i)) 2),
    Printed.IsFunctionCompletionMap μ rep H q θ j ∧
    (∀ i, Printed.IsFunctionCompletionMap μ rep (K i) (qω i) (θω i) (k i)) ∧
    Function.Injective Q ∧ (∀ f i, Q (j (q f)) i = k i (qω i f)) ∧
    ∀ u i, Q u i = T u i

/-- Paper: Proposition 10.1.1.5(2), p. 437, (10.1.1.14). The product of the
global homogeneous quotient maps factors isometrically through the Hilbert sum.
The factors carry the norm of their weighted homogeneous functions. -/
def Printed.globalThetaSobolev_rawIsotypeDecomposition : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (a α β s : ℝ), α ≤ β → 0 ≤ s →
    let G := IdeleClassGroup (𝓞 F) F
    let m : G →ₜ* ℝ≥0ˣ := ⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩
    let μ := ideleClassTamagawaMeasure F
    let W := CompactIntervalSobolev μ (fun g ↦ Real.log ((m g).val : ℝ)) α β s
    Printed.HasHomogeneousSobolevFactorization (X := GlobalAdelicThetaSpace F)
      (Y := GlobalHomogeneousThetaSpace F) μ (fun u : W ↦ ⇑u)
      Submodule.Quotient.mk (fun _ ↦ Submodule.Quotient.mk)
      (fun f ↦ modulationWeight m a (adelicTheta f))
      (fun ω f ↦ modulationWeight m a (homogeneousAdelicTheta ω f))

open scoped ENNReal ComplexConjugate InnerProductSpace in
private theorem Printed.rawIsotype_orth {K : Type*} [CommGroup K] [TopologicalSpace K]
    [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (ν : Measure K) [ν.IsHaarMeasure]
    (ω₁ ω₂ : PontryaginDual K) (h : ω₁ ≠ ω₂) :
    ∫ x, (ω₁ x : ℂ) * conj (ω₂ x : ℂ) ∂ν = 0 := by
  obtain ⟨c, hc⟩ := DFunLike.ne_iff.mp h
  set I := ∫ x, (ω₁ x : ℂ) * conj (ω₂ x : ℂ) ∂ν
  have hinv : ∫ x, (ω₁ (c * x) : ℂ) * conj (ω₂ (c * x) : ℂ) ∂ν = I :=
    integral_mul_left_eq_self (fun x ↦ (ω₁ x : ℂ) * conj (ω₂ x : ℂ)) c
  have hsplit : ∫ x, (ω₁ (c * x) : ℂ) * conj (ω₂ (c * x) : ℂ) ∂ν =
      ((ω₁ c : ℂ) * conj (ω₂ c : ℂ)) * I := by
    rw [← integral_const_mul]
    congr 1; funext x
    simp only [map_mul, Circle.coe_mul, map_mul]; ring
  have hl : (ω₁ c : ℂ) * conj (ω₂ c : ℂ) ≠ 1 := by
    intro h1
    apply hc
    have h2 : (ω₂ c : ℂ) * conj (ω₂ c : ℂ) = 1 := by
      rw [Complex.mul_conj, Circle.normSq_coe, Complex.ofReal_one]
    have : (ω₁ c : ℂ) = (ω₂ c : ℂ) := by
      have hne : conj (ω₂ c : ℂ) ≠ 0 := by
        intro h0; rw [h0, mul_zero] at h2; exact zero_ne_one h2
      exact mul_right_cancel₀ hne (h1.trans h2.symm)
    exact Subtype.ext this
  have : ((ω₁ c : ℂ) * conj (ω₂ c : ℂ) - 1) * I = 0 := by
    rw [sub_mul, one_mul, ← hsplit, hinv, sub_self]
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hl)

open scoped ENNReal ComplexConjugate InnerProductSpace in
private theorem Printed.rawIsotype_bessel {K : Type*} [CommGroup K] [TopologicalSpace K]
    [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (ν : Measure K) [ν.IsHaarMeasure]
    (φ : C(K, ℂ)) (s : Finset (PontryaginDual K)) :
    ∑ ω ∈ s, ‖∫ x, φ x * (ω x : ℂ) ∂ν‖ ^ 2 ≤
      (ν univ).toReal * ‖ContinuousMap.toLp (E := ℂ) 2 ν ℂ φ‖ ^ 2 := by
  set V := (ν univ).toReal with hVdef
  have hV : 0 < V := ENNReal.toReal_pos (NeZero.ne _) (measure_ne_top _ _)
  let χ : PontryaginDual K → C(K, ℂ) := fun ω ↦
    ⟨fun x ↦ conj (ω x : ℂ), Complex.continuous_conj.comp (continuous_subtype_val.comp ω.continuous)⟩
  let c : ℝ := (Real.sqrt V)⁻¹
  let v : PontryaginDual K → Lp ℂ 2 ν := fun ω ↦ (c : ℂ) • ContinuousMap.toLp (E := ℂ) 2 ν ℂ (χ ω)
  have hc2 : c * c * V = 1 := by
    simp only [c]
    rw [← mul_inv, Real.mul_self_sqrt hV.le, inv_mul_cancel₀ hV.ne']
  have hv : Orthonormal ℂ v := by
    classical
    rw [orthonormal_iff_ite]
    intro i j
    simp only [v, inner_smul_left, inner_smul_right, ContinuousMap.inner_toLp, Complex.conj_ofReal]
    change (c : ℂ) * ((c : ℂ) * ∫ x, conj (j x : ℂ) * conj (conj (i x : ℂ)) ∂ν) = _
    simp only [Complex.conj_conj]
    split_ifs with hij
    · subst hij
      have h1 : ∀ x, conj (i x : ℂ) * (i x : ℂ) = 1 := fun x ↦ by
        rw [mul_comm, Complex.mul_conj, Circle.normSq_coe, Complex.ofReal_one]
      simp only [h1, integral_const]
      rw [← mul_assoc, ← Complex.ofReal_mul]
      simp only [Measure.real, Complex.real_smul, mul_one]
      exact_mod_cast hc2
    · have h0 := Printed.rawIsotype_orth ν i j hij
      have : ∫ x, conj (j x : ℂ) * (i x : ℂ) ∂ν = 0 := by
        rw [← h0]; congr 1; funext x; ring
      rw [this, mul_zero, mul_zero]
  have key := hv.sum_inner_products_le (x := ContinuousMap.toLp (E := ℂ) 2 ν ℂ φ) (s := s)
  have hin : ∀ ω, ⟪v ω, ContinuousMap.toLp (E := ℂ) 2 ν ℂ φ⟫_ℂ =
      (c : ℂ) * ∫ x, φ x * (ω x : ℂ) ∂ν := by
    intro ω
    simp only [v, inner_smul_left, ContinuousMap.inner_toLp, Complex.conj_ofReal]
    change (c : ℂ) * ∫ x, φ x * conj (conj (ω x : ℂ)) ∂ν = _
    simp only [Complex.conj_conj]
  simp only [hin, norm_mul, Complex.norm_real, mul_pow] at key
  rw [← Finset.mul_sum] at key
  have hcn : ‖c‖ ^ 2 * V = 1 := by
    rw [Real.norm_eq_abs, sq_abs, sq]; exact hc2
  calc ∑ ω ∈ s, ‖∫ x, φ x * (ω x : ℂ) ∂ν‖ ^ 2
      = V * (‖c‖ ^ 2 * ∑ ω ∈ s, ‖∫ x, φ x * (ω x : ℂ) ∂ν‖ ^ 2) := by
        rw [← mul_assoc, mul_comm V, hcn, one_mul]
    _ ≤ V * ‖ContinuousMap.toLp (E := ℂ) 2 ν ℂ φ‖ ^ 2 := by gcongr

open scoped ENNReal ComplexConjugate InnerProductSpace in
private theorem Printed.rawIsotype_besselENN {K : Type*} [CommGroup K] [TopologicalSpace K]
    [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (ν : Measure K) [ν.IsHaarMeasure]
    (φ : C(K, ℂ)) :
    ∑' ω : PontryaginDual K, ‖∫ x, φ x * (ω x : ℂ) ∂ν‖ₑ ^ 2 ≤ ν univ * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂ν := by
  have hL : ENNReal.ofReal (‖ContinuousMap.toLp (E := ℂ) 2 ν ℂ φ‖ ^ 2) =
      ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂ν := by
    rw [Lp.norm_def, ENNReal.ofReal_pow ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _),
      eLpNorm_congr_ae (φ.coeFn_toLp (p := 2) (𝕜 := ℂ) ν)]
    have := eLpNorm_nnreal_pow_eq_lintegral (μ := ν) (f := ⇑φ) (p := 2) two_ne_zero
      φ.continuous.aestronglyMeasurable
    simpa using this
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s ↦ ?_
  have hb := Printed.rawIsotype_bessel ν φ s
  calc ∑ ω ∈ s, ‖∫ x, φ x * (ω x : ℂ) ∂ν‖ₑ ^ 2
      = ENNReal.ofReal (∑ ω ∈ s, ‖∫ x, φ x * (ω x : ℂ) ∂ν‖ ^ 2) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ by positivity)]
        refine Finset.sum_congr rfl fun ω _ ↦ ?_
        rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]
    _ ≤ ENNReal.ofReal ((ν univ).toReal * ‖ContinuousMap.toLp (E := ℂ) 2 ν ℂ φ‖ ^ 2) :=
        ENNReal.ofReal_le_ofReal hb
    _ = ν univ * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂ν := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (measure_ne_top _ _), hL]

open scoped ENNReal ComplexConjugate InnerProductSpace in
private theorem Printed.rawIsotype_integrated {C : Type*} [CommGroup C] [TopologicalSpace C]
    [IsTopologicalGroup C] [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
    (K : Subgroup C) [CompactSpace K] (ν : Measure K) [ν.IsHaarMeasure]
    (μ : Measure C) [μ.IsMulLeftInvariant] [SFinite μ]
    (θ : C → ℂ) (hθ : Continuous θ) (Θ : PontryaginDual K → C → ℂ)
    (hΘc : ∀ ω, Continuous (Θ ω))
    (hΘ : ∀ ω g, Θ ω g = ∫ h, θ (h.val * g) * (ω h : ℂ) ∂ν) :
    ∑' ω, ∫⁻ g, ‖Θ ω g‖ₑ ^ 2 ∂μ ≤ ν univ ^ 2 * ∫⁻ g, ‖θ g‖ₑ ^ 2 ∂μ := by
  have hpt : ∀ g, ∑' ω, ‖Θ ω g‖ₑ ^ 2 ≤ ν univ * ∫⁻ h, ‖θ (h.val * g)‖ₑ ^ 2 ∂ν := by
    intro g
    simp only [hΘ]
    exact Printed.rawIsotype_besselENN ν ⟨fun h : K ↦ θ (h.val * g),
      hθ.comp (continuous_subtype_val.mul continuous_const)⟩
  have hmain : ∫⁻ g, ∑' ω, ‖Θ ω g‖ₑ ^ 2 ∂μ ≤ ν univ ^ 2 * ∫⁻ g, ‖θ g‖ₑ ^ 2 ∂μ := calc
    ∫⁻ g, ∑' ω, ‖Θ ω g‖ₑ ^ 2 ∂μ
      ≤ ∫⁻ g, ν univ * ∫⁻ h, ‖θ (h.val * g)‖ₑ ^ 2 ∂ν ∂μ := lintegral_mono hpt
    _ = ν univ * ∫⁻ g, ∫⁻ h, ‖θ (h.val * g)‖ₑ ^ 2 ∂ν ∂μ :=
        lintegral_const_mul' _ _ (measure_ne_top _ _)
    _ = ν univ * ∫⁻ h, ∫⁻ g, ‖θ (h.val * g)‖ₑ ^ 2 ∂μ ∂ν := by
        rw [lintegral_lintegral_swap]
        exact ((hθ.comp ((continuous_subtype_val.comp continuous_snd).mul
          continuous_fst)).measurable.enorm.pow_const 2).aemeasurable
    _ = ν univ * ∫⁻ h, ∫⁻ g, ‖θ g‖ₑ ^ 2 ∂μ ∂ν := by
        congr 1
        refine lintegral_congr fun h ↦ ?_
        exact lintegral_mul_left_eq_self (fun g ↦ ‖θ g‖ₑ ^ 2) h.val
    _ = ν univ ^ 2 * ∫⁻ g, ‖θ g‖ₑ ^ 2 ∂μ := by rw [lintegral_const, sq, mul_assoc, mul_comm (∫⁻ _, _ ∂μ)]
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s ↦ le_trans ?_ hmain
  rw [← lintegral_finsetSum' s (fun ω _ ↦ ((hΘc ω).measurable.enorm.pow_const 2).aemeasurable)]
  exact lintegral_mono fun g ↦ ENNReal.sum_le_tsum s

/-- Squared L² seminorm of a continuous function as a lower integral. -/
private theorem Printed.rawIsotype_eLpNorm_sq {C : Type*} [TopologicalSpace C]
    [MeasurableSpace C] [OpensMeasurableSpace C] [SecondCountableTopology C]
    (μ : Measure C) (φ : C → ℂ) (hφ : Continuous φ) :
    eLpNorm φ 2 μ ^ 2 = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ := by
  have := eLpNorm_nnreal_pow_eq_lintegral (μ := μ) (f := φ) (p := 2) two_ne_zero
    hφ.aestronglyMeasurable
  simpa using this

/-- A Hilbert-sum factorization of quotient maps equates the squared norm of
each total function with the sum of the squared norms of its components. -/
private theorem Printed.rawIsotype_factorization_norm {G B X Ω : Type*} {Y : Ω → Type*}
    [MeasurableSpace G] [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [∀ i, AddCommGroup (Y i)] [∀ i, Module ℂ (Y i)] [∀ i, TopologicalSpace (Y i)]
    {μ μ' : Measure G} {q : B → X} {qω : ∀ i, B → Y i}
    {θ : B → G → ℂ} {θω : Ω → B → G → ℂ}
    (h : Printed.HasHomogeneousSobolevFactorization (W := Lp ℂ 2 μ') μ (fun u ↦ ⇑u)
      q qω θ θω) (hμ : μ' = μ) (f : B) :
    eLpNorm (θ f) 2 μ < ⊤ ∧ ∑' i, eLpNorm (θω i f) 2 μ ^ 2 = eLpNorm (θ f) 2 μ ^ 2 := by
  subst hμ
  obtain ⟨H, K, j, k, Q, T, hj, hk, -, hQ, hT⟩ := h
  have e0 : eLpNorm (θ f) 2 μ' = eLpNorm (((j (q f) : H) : Lp ℂ 2 μ')) 2 μ' :=
    eLpNorm_congr_ae (hj.2.2.2 f).symm
  have ei : ∀ i, eLpNorm (θω i f) 2 μ' =
      eLpNorm (((T (j (q f)) i : K i) : Lp ℂ 2 μ')) 2 μ' := by
    intro i
    rw [← hT, hQ f i]
    exact eLpNorm_congr_ae ((hk i).2.2.2 f).symm
  have hs := lp.hasSum_norm (p := 2) (by norm_num) (T (j (q f)))
  rw [T.norm_map] at hs
  have hs' : HasSum (fun i ↦ (eLpNorm (((T (j (q f)) i : K i) : Lp ℂ 2 μ')) 2 μ').toReal ^ 2)
      ((eLpNorm (((j (q f) : H) : Lp ℂ 2 μ')) 2 μ').toReal ^ 2) := by
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hs
    exact hs
  refine ⟨e0 ▸ Lp.eLpNorm_lt_top _, ?_⟩
  have hsq : ∀ w : Lp ℂ 2 μ', eLpNorm w 2 μ' ^ 2 = ENNReal.ofReal ((eLpNorm w 2 μ').toReal ^ 2) :=
    fun w ↦ by
      rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
  simp only [ei, e0, hsq]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ by positivity) hs'.summable, hs'.tsum_eq]

/-- If the Hilbert-sum norm identity holds for one nonzero continuous theta function,
the norm-one group has mass at least one: Bessel bounds the components by the mass squared. -/
private theorem Printed.rawIsotype_contra {C : Type*} [CommGroup C] [TopologicalSpace C]
    [IsTopologicalGroup C] [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
    (K : Subgroup C) [CompactSpace K] (ν : Measure K) [ν.IsHaarMeasure]
    (μ : Measure C) [μ.IsMulLeftInvariant] [SFinite μ] [μ.IsOpenPosMeasure]
    (θ : C → ℂ) (hθ : Continuous θ) (Θ : PontryaginDual K → C → ℂ)
    (hΘc : ∀ ω, Continuous (Θ ω))
    (hΘ : ∀ ω g, Θ ω g = ∫ h, θ (h.val * g) * (ω h : ℂ) ∂ν)
    (hvol : ν univ < 1) (g0 : C) (hg0 : θ g0 ≠ 0)
    (hfin : eLpNorm θ 2 μ < ⊤) (heq : ∑' ω, eLpNorm (Θ ω) 2 μ ^ 2 = eLpNorm θ 2 μ ^ 2) :
    False := by
  have hb := Printed.rawIsotype_integrated K ν μ θ hθ Θ hΘc hΘ
  have hω : ∀ ω, ∫⁻ g, ‖Θ ω g‖ₑ ^ 2 ∂μ = eLpNorm (Θ ω) 2 μ ^ 2 :=
    fun ω ↦ (Printed.rawIsotype_eLpNorm_sq μ _ (hΘc ω)).symm
  simp only [hω] at hb
  rw [heq, ← Printed.rawIsotype_eLpNorm_sq μ θ hθ] at hb
  have he : eLpNorm θ 2 μ ^ 2 = 0 := by
    by_contra hne
    have hfin2 : eLpNorm θ 2 μ ^ 2 ≠ ⊤ := ENNReal.pow_ne_top hfin.ne
    have h1 : 1 ≤ ν univ ^ 2 := by
      exact (ENNReal.mul_le_mul_iff_left (a := 1) (b := ν univ ^ 2) hne hfin2).mp
        (by rwa [one_mul])
    exact absurd h1 (not_le.mpr (pow_lt_one₀ bot_le hvol two_ne_zero))
  have h0 : θ =ᵐ[μ] 0 :=
    (eLpNorm_eq_zero_iff two_ne_zero).mp (pow_eq_zero_iff two_ne_zero |>.mp he)
  exact hg0 (congrFun ((hθ.ae_eq_iff_eq μ continuous_const).mp h0) g0)

open scoped Classical in
/-- Over every number field some adelic theta function is nonzero: take a nonnegative
archimedean bump equal to one at the unit, times the indicator of the finite integers. -/
private theorem Printed.rawIsotype_exists_theta_ne_zero (F : Type) [Field F] [NumberField F] :
    ∃ (f : SchwartzBruhat (Multiplicative (AdeleRing (𝓞 F) F)))
      (g : IdeleClassGroup (𝓞 F) F), adelicTheta f g ≠ 0 := by
  let b : ContDiffBump (1 : mixedEmbedding.mixedSpace F) := ⟨1, 2, one_pos, one_lt_two⟩
  let bs : SchwartzMap (mixedEmbedding.mixedSpace F) ℂ :=
    HasCompactSupport.toSchwartzMap (f := fun x ↦ ((b x : ℝ) : ℂ))
      (b.hasCompactSupport.comp_left Complex.ofReal_zero)
      (Complex.ofRealCLM.contDiff.comp b.contDiff)
  let arch : SchwartzBruhat (Multiplicative (InfiniteAdeleRing F)) :=
    ⟨fun x ↦ bs (InfiniteAdeleRing.ringEquiv_mixedSpace F x.toAdd),
      (mem_archimedeanSchwartzBruhat_iff _).mpr ⟨bs, fun _ ↦ rfl⟩⟩
  obtain ⟨e, he⟩ := sAdeleSchwartz_inductiveTensor_equiv F (∅ : Finset (HeightOneSpectrum (𝓞 F)))
  let gg : ∀ w : (∅ : Finset (HeightOneSpectrum (𝓞 F))),
      SchwartzBruhat (Multiplicative (w.val.adicCompletion F)) :=
    fun w ↦ absurd w.2 (Finset.notMem_empty _)
  let f := sAdeleSchwartzToGlobal F ∅ (e (arch ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, gg w)))
  have hf : ∀ x : AdeleRing (𝓞 F) F, f (Multiplicative.ofAdd x) =
      if ∀ v : HeightOneSpectrum (𝓞 F), x.2 v ∈ v.adicCompletionIntegers F then
        ((b (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) : ℝ) : ℂ) else 0 := by
    intro x
    rw [sAdeleSchwartzToGlobal_apply, he]
    simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one, Finset.notMem_empty,
      not_false_eq_true, forall_const]
    split_ifs <;> rfl
  let T : Fˣ → ℂ := fun ξ ↦ f (Multiplicative.ofAdd
    (algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) * (1 : IdeleGroup (𝓞 F) F).val))
  have hT : ∀ ξ, T ξ = ((‖T ξ‖ : ℝ) : ℂ) := by
    intro ξ
    change f _ = ((‖f _‖ : ℝ) : ℂ)
    rw [hf]
    split_ifs
    · rw [Complex.norm_real, Real.norm_of_nonneg b.nonneg]
    · simp
  have hT1 : ‖T 1‖ = 1 := by
    change ‖f _‖ = 1
    rw [Units.val_one, map_one, Units.val_one, mul_one, hf, if_pos (fun v ↦ by
      change (1 : v.adicCompletion F) ∈ v.adicCompletionIntegers F
      exact one_mem _), Prod.fst_one, map_one, b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le),
      Complex.ofReal_one, norm_one]
  have hs : Summable fun ξ ↦ ‖T ξ‖ := by
    have := (adelicAverage_summableUniformlyOn f _
      (isCompact_singleton (x := ((1 : IdeleGroup (𝓞 F) F), (0 : AdeleRing (𝓞 F) F))))).summable
      (Set.mem_singleton _)
    simpa only [T, add_zero, mul_comm] using this
  refine ⟨f, QuotientGroup.mk (s := IdeleGroup.principalSubgroup (𝓞 F) F) 1, ?_⟩
  rw [adelicTheta_mk]
  change ∑' ξ, T ξ ≠ 0
  rw [tsum_congr hT, ← Complex.ofReal_tsum]
  have hpos : 0 < ∑' ξ, ‖T ξ‖ :=
    lt_of_lt_of_le (by rw [hT1]; exact one_pos) (hs.le_tsum 1 (fun _ _ ↦ norm_nonneg _))
  exact_mod_cast hpos.ne'

/-- The norm-one idele classes of ℚ(ζ₃) have Tamagawa mass π/(3√3) < 1. -/
private theorem Printed.rawIsotype_volume_lt_one :
    normOneIdeleClassTamagawaMeasure (CyclotomicField 3 ℚ) univ < 1 := by
  rw [normOneIdeleClassTamagawaMeasure_volume, ENNReal.ofReal_lt_one]
  have : IsCyclotomicExtension {(3:ℕ)} ℚ (CyclotomicField 3 ℚ) :=
    CyclotomicField.isCyclotomicExtension 3 ℚ
  have hh : NumberField.classNumber (CyclotomicField 3 ℚ) = 1 :=
    classNumber_eq_one_iff.mpr (IsCyclotomicExtension.Rat.three_pid _)
  have ht : Units.torsionOrder (CyclotomicField 3 ℚ) = 6 := by
    rw [IsCyclotomicExtension.Rat.torsionOrder_eq (n := 3)]; decide
  have hd : NumberField.discr (CyclotomicField 3 ℚ) = -3 := by
    rw [IsCyclotomicExtension.Rat.discr_prime 3 (CyclotomicField 3 ℚ)]
    norm_num
  have h1 : InfinitePlace.nrRealPlaces (CyclotomicField 3 ℚ) = 0 :=
    IsCyclotomicExtension.Rat.nrRealPlaces_eq_zero (n := 3) _ (by norm_num)
  have h2 : InfinitePlace.nrComplexPlaces (CyclotomicField 3 ℚ) = 1 := by
    rw [IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two 3]; decide
  have hR : Units.regulator (CyclotomicField 3 ℚ) = 1 := by
    have hc : Fintype.card (InfinitePlace (CyclotomicField 3 ℚ)) = 1 := by
      rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, h1, h2]
    have hall : ∀ a b : InfinitePlace (CyclotomicField 3 ℚ), a = b :=
      Fintype.card_le_one_iff.mp hc.le
    classical
    rw [Units.regulator_eq_det', Matrix.det_eq_one_of_card_eq_zero
      (Fintype.card_eq_zero_iff.mpr ⟨fun w ↦ w.2 (hall _ _)⟩), abs_one]
  rw [hh, ht, hd, h1, h2, hR]
  have hs : (1.7 : ℝ) < Real.sqrt 3 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hpi := Real.pi_lt_d2
  rw [div_lt_one (by positivity)]
  norm_num
  nlinarith

/-- The global statement fails over ℚ(ζ₃) with a = α = β = s = 0. -/
private theorem Printed.rawIsotype_global_aux (F : Type) [Field F] [NumberField F]
    (hvol : normOneIdeleClassTamagawaMeasure F univ < 1)
    (h : Printed.HasHomogeneousSobolevFactorization (X := GlobalAdelicThetaSpace F)
      (Y := GlobalHomogeneousThetaSpace F) (ideleClassTamagawaMeasure F)
      (fun u : CompactIntervalSobolev (ideleClassTamagawaMeasure F)
          (fun g ↦ Real.log ((ideleClassNorm F g).val : ℝ)) 0 0 0 ↦ ⇑u)
      Submodule.Quotient.mk (fun _ ↦ Submodule.Quotient.mk)
      (fun f ↦ modulationWeight (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ :
          IdeleClassGroup (𝓞 F) F →ₜ* ℝ≥0ˣ) 0 (adelicTheta f))
      (fun ω f ↦ modulationWeight (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ :
          IdeleClassGroup (𝓞 F) F →ₜ* ℝ≥0ˣ) 0 (homogeneousAdelicTheta ω f))) : False := by
  obtain ⟨f, g0, hg0⟩ := Printed.rawIsotype_exists_theta_ne_zero F
  have hF := Printed.rawIsotype_factorization_norm h
    (by simp [intervalSobolevDensity]) f
  simp only [modulationWeight_zero] at hF
  let : BorelSpace (IdeleClassGroup (𝓞 F) F) := ⟨rfl⟩
  let : T2Space (IdeleClassGroup (𝓞 F) F) := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.1
  let : LocallyCompactSpace (IdeleClassGroup (𝓞 F) F) :=
    (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.1
  let : SecondCountableTopology (IdeleClassGroup (𝓞 F) F) := by
    let := idele_secondCountable F
    exact inferInstanceAs (SecondCountableTopology
      (IdeleGroup (𝓞 F) F ⧸ IdeleGroup.principalSubgroup (𝓞 F) F))
  let : CompactSpace (ideleClassNorm F).ker := (ideleClassGroup_finiteness F).2.1
  let : (ideleClassTamagawaMeasure F).IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil F).1
  let : (normOneIdeleClassTamagawaMeasure F).IsHaarMeasure :=
    (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  exact Printed.rawIsotype_contra (ideleClassNorm F).ker (normOneIdeleClassTamagawaMeasure F)
    (ideleClassTamagawaMeasure F) (adelicTheta f) (adelicTheta f).continuous
    (fun ω ↦ homogeneousAdelicTheta ω f) (fun ω ↦ (homogeneousAdelicTheta ω f).continuous)
    (fun _ _ ↦ rfl) hvol g0 hg0 hF.1 hF.2

/-- Paper: Proposition 10.1.1.5(2), p. 437. Take ℚ(ζ₃), a = s = 0 and I = {0}, so the
weight is one. The isometry gives ‖θ‖² = Σ_ω ‖θ_ω‖² for every test function. By Bessel's
inequality for the characters of the norm-one classes, the right side is at most
vol(C¹)²‖θ‖², and vol(C¹) = π/(3√3) < 1. So every theta function would vanish, but a
nonnegative archimedean bump times the indicator of the finite integers has nonzero theta.
(The printed counterexample over ℚ(i), with norm-one mass π/4, works the same way.) -/
theorem Printed.globalThetaSobolev_rawIsotypeDecomposition_false :
    ¬ Printed.globalThetaSobolev_rawIsotypeDecomposition := fun h ↦
  Printed.rawIsotype_global_aux (CyclotomicField 3 ℚ) Printed.rawIsotype_volume_lt_one
    (h (CyclotomicField 3 ℚ) 0 0 0 0 le_rfl le_rfl)

/-- Paper: Proposition 10.1.1.5(2), p. 437, (10.1.1.15). The product of the
S-local homogeneous quotient maps factors isometrically through the Hilbert sum.
The factors carry the norm of their weighted homogeneous functions. -/
def Printed.sLocalThetaSobolev_rawIsotypeDecomposition : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (a α β s : ℝ), 0 < a → α ≤ β → 0 ≤ s → 0 < α →
    let G := SIdeleQuotient F S
    let m : G →ₜ* ℝ≥0ˣ := ⟨sIdeleQuotientNorm F S, (isProperMap_sIdeleQuotientNorm F S).continuous⟩
    let μ := sLocalQuotientTamagawaMeasure F S
    let W := CompactIntervalSobolev μ (fun g ↦ Real.log ((m g).val : ℝ)) α β s
    Printed.HasHomogeneousSobolevFactorization (X := SLocalAdelicThetaSpace F S)
      (Y := SLocalHomogeneousThetaSpace F S) μ (fun u : W ↦ ⇑u)
      Submodule.Quotient.mk (fun _ ↦ Submodule.Quotient.mk)
      (fun f ↦ modulationWeight m a (sLocalAdelicThetaOnClasses F S f))
      (fun ω f ↦ modulationWeight m a (sLocalHomogeneousAdelicThetaLinearMap F S ω f))

/-- Paper: Proposition 10.1.1.5(2), p. 437. Take ℚ(i), S consisting of the
complex place, a = 1, I = {1}, and s = 0. A nonzero radial Gaussian theta
function lies in the trivial isotype. Its raw average is π/2 times itself
and every other character average is zero, so the Hilbert sum norm grows by π/2. -/
theorem Printed.sLocalThetaSobolev_rawIsotypeDecomposition_false :
    ¬ Printed.sLocalThetaSobolev_rawIsotypeDecomposition := by sorry

/-- Paper: Theorem 10.1.2.1, p. 437. As printed, inversion in the idele class
group defines a continuous linear automorphism of the same ambient Sobolev space
for every compact nonempty interval. -/
def Printed.ideleClassSobolev_inversion_automorphism : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (α β s : ℝ), α ≤ β → 0 ≤ s →
    let μ := ideleClassTamagawaMeasure F
    let W := CompactIntervalSobolev μ
      (fun g ↦ Real.log ((ideleClassNorm F g).val : ℝ)) α β s
    ∃ J : W ≃L[ℂ] W, ∀ u : W,
      (J u : IdeleClassGroup (𝓞 F) F → ℂ) =ᵐ[μ] fun g ↦ u g⁻¹

open scoped ENNReal in
/-- On the weighted L² space with weight |x|² (I = {1}, s = 0) over a commutative group with a
module taking a value above one, inversion is not a bounded automorphism. It would conjugate
translation by g⁻¹ into translation by g, so its norm would be at most |g|⁻² times itself. -/
private theorem Printed.ideleClassSobolev_inversion_automorphism_false_aux {G : Type*}
    [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (m : G →ₜ* ℝ≥0ˣ) (g : G) (hg : 1 < ((m g).val : ℝ))
    (J : CompactIntervalSobolev μ (fun x ↦ Real.log ((m x).val : ℝ)) 1 1 0 ≃L[ℂ]
      CompactIntervalSobolev μ (fun x ↦ Real.log ((m x).val : ℝ)) 1 1 0)
    (hJ : ∀ u, (J u : G → ℂ) =ᵐ[μ] fun x ↦ u x⁻¹) : False := by
  set d : G → ℝ≥0∞ := fun x ↦ ENNReal.ofReal
    (if (false : Bool) then (intervalSobolevDensity 1 1 0 (Real.log ((m x).val : ℝ)))⁻¹
     else intervalSobolevDensity 1 1 0 (Real.log ((m x).val : ℝ))) with hd_def
  have hνμ : μ.withDensity d ≪ μ := withDensity_absolutelyContinuous μ d
  let T := hardySobolevTranslation μ m 1 1 0 le_rfl le_rfl
  have hinv : QuasiMeasurePreserving (Inv.inv : G → G) μ μ :=
    quasiMeasurePreserving_inv μ
  have hmul : QuasiMeasurePreserving (fun x : G ↦ g * x) μ μ :=
    (measurePreserving_mul_left μ g).quasiMeasurePreserving
  -- Inversion turns translation by g⁻¹ into translation by g.
  have hconj (u : CompactIntervalSobolev μ (fun x ↦ Real.log ((m x).val : ℝ)) 1 1 0) :
      J u = T g⁻¹ (J (T g⁻¹ u)) := by
    apply Lp.ext
    apply hνμ.ae_eq
    have h1 : (T g⁻¹ (J (T g⁻¹ u)) : G → ℂ) =ᵐ[μ] fun x ↦ (J (T g⁻¹ u) : G → ℂ) (g * x) := by
      simpa only [inv_inv] using hardySobolevTranslation_apply μ m 1 1 0 le_rfl le_rfl g⁻¹ _
    have h2 : (fun x ↦ (J (T g⁻¹ u) : G → ℂ) (g * x)) =ᵐ[μ]
        fun x ↦ (T g⁻¹ u : G → ℂ) (g * x)⁻¹ :=
      hmul.ae_eq_comp (hJ _)
    have h3 : (fun x ↦ (T g⁻¹ u : G → ℂ) (g * x)⁻¹) =ᵐ[μ]
        fun x ↦ (u : G → ℂ) (g * (g * x)⁻¹) := by
      have h := hardySobolevTranslation_apply μ m 1 1 0 le_rfl le_rfl g⁻¹ u
      simp only [inv_inv] at h
      exact (hinv.comp hmul).ae_eq_comp h
    filter_upwards [hJ u, h1, h2, h3] with x hx h1 h2 h3
    rw [hx, h1, h2, h3, mul_inv, ← mul_assoc, mul_inv_cancel, one_mul]
  -- Translation by g⁻¹ has norm at most |g|⁻¹ < 1.
  set L := Real.log ((m g).val : ℝ)
  have hL : 0 < L := Real.log_pos hg
  have hTnorm : ‖T g⁻¹‖ ≤ Real.exp (-L) := by
    have h := norm_hardySobolevTranslation_le μ m 1 1 0 le_rfl le_rfl g⁻¹
    have hlog : Real.log ((m g⁻¹).val : ℝ) = -L := by
      rw [map_inv, Units.val_inv_eq_inv_val, NNReal.coe_inv, Real.log_inv]
    simpa only [hlog, one_mul, max_self, zero_div, Real.rpow_zero, mul_one] using h
  have hq : Real.exp (-L) < 1 := by
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (neg_lt_zero.mpr hL)
  have hq0 : 0 ≤ Real.exp (-L) := (Real.exp_pos _).le
  have hJop : J.toContinuousLinearMap = (T g⁻¹).comp (J.toContinuousLinearMap.comp (T g⁻¹)) :=
    ContinuousLinearMap.ext hconj
  have hJn : ‖J.toContinuousLinearMap‖ ≤ Real.exp (-L) ^ 2 * ‖J.toContinuousLinearMap‖ := by
    calc ‖J.toContinuousLinearMap‖ = ‖(T g⁻¹).comp (J.toContinuousLinearMap.comp (T g⁻¹))‖ :=
          congrArg norm hJop
      _ ≤ ‖T g⁻¹‖ * (‖J.toContinuousLinearMap‖ * ‖T g⁻¹‖) :=
          (ContinuousLinearMap.opNorm_comp_le _ _).trans
            (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ Real.exp (-L) * (‖J.toContinuousLinearMap‖ * Real.exp (-L)) := by
          gcongr
      _ = Real.exp (-L) ^ 2 * ‖J.toContinuousLinearMap‖ := by ring
  have hJ0 : ‖J.toContinuousLinearMap‖ = 0 := by
    have hq2 : Real.exp (-L) ^ 2 < 1 := by nlinarith
    by_contra hne
    have hpos := lt_of_le_of_ne (norm_nonneg J.toContinuousLinearMap) (Ne.symm hne)
    nlinarith [mul_pos hpos (sub_pos.mpr hq2)]
  -- The space is nonzero: the indicator of a compact neighbourhood of 1 has positive norm.
  obtain ⟨K, hKc, hK1⟩ := exists_compact_mem_nhds (1 : G)
  have hKm : MeasurableSet K := hKc.measurableSet
  have hdc : Continuous fun x : G ↦ intervalSobolevDensity 1 1 0 (Real.log ((m x).val : ℝ)) := by
    have hl : Continuous fun x : G ↦ Real.log ((m x).val : ℝ) :=
      (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)).log
        fun x ↦ (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
    unfold intervalSobolevDensity
    fun_prop
  have hdpos (x : G) : 0 < intervalSobolevDensity 1 1 0 (Real.log ((m x).val : ℝ)) := by
    unfold intervalSobolevDensity
    exact mul_pos ((Real.exp_pos _).trans_le (le_max_left _ _)) (by positivity)
  have : IsLocallyFiniteMeasure (μ.withDensity d) := by
    simp only [hd_def, Bool.false_eq_true, ite_false]
    exact IsLocallyFiniteMeasure.withDensity_ofReal hdc
  have hfin : μ.withDensity d K ≠ ⊤ := hKc.measure_lt_top.ne
  have hpos : μ.withDensity d K ≠ 0 := by
    intro h0
    have hμν : μ ≪ μ.withDensity d := by
      refine withDensity_absolutelyContinuous' ?_ (.of_forall fun x ↦ ?_)
      · simp only [hd_def, Bool.false_eq_true, ite_false]
        exact hdc.measurable.ennreal_ofReal.aemeasurable
      · simp only [hd_def, Bool.false_eq_true, ite_false]
        exact (ENNReal.ofReal_pos.mpr (hdpos x)).ne'
    exact (Measure.measure_pos_of_mem_nhds μ hK1).ne' (hμν h0)
  let v : CompactIntervalSobolev μ (fun x ↦ Real.log ((m x).val : ℝ)) 1 1 0 :=
    indicatorConstLp 2 hKm hfin (1 : ℂ)
  have hv : v ≠ 0 := by
    intro h
    have hn := congrArg norm h
    rw [norm_zero, norm_indicatorConstLp' (by norm_num) hpos, norm_one, one_mul] at hn
    exact (Real.rpow_pos_of_pos (ENNReal.toReal_pos hpos hfin) _).ne' hn
  apply hv
  have hJv : J v = 0 := by
    rw [← norm_eq_zero]
    refine le_antisymm ?_ (norm_nonneg _)
    calc ‖J v‖ = ‖J.toContinuousLinearMap v‖ := rfl
      _ ≤ ‖J.toContinuousLinearMap‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
      _ = 0 := by rw [hJ0, zero_mul]
  have h := congrArg J.symm hJv
  rwa [ContinuousLinearEquiv.symm_apply_apply, map_zero] at h

/-- Paper: Theorem 10.1.2.1, p. 437. Take ℚ, I = {1} and s = 0. The indicator
of |g| < 1 is square integrable for t² dt/t in the norm coordinate t, while its
inverse pullback is the indicator of |g| > 1, which has infinite squared integral. -/
theorem Printed.ideleClassSobolev_inversion_automorphism_false :
    ¬ Printed.ideleClassSobolev_inversion_automorphism := by
  intro h
  obtain ⟨J, hJ⟩ := h ℚ 1 1 0 le_rfl le_rfl
  let : BorelSpace (IdeleClassGroup (𝓞 ℚ) ℚ) := ⟨rfl⟩
  let : T2Space (IdeleClassGroup (𝓞 ℚ) ℚ) := (ideleGroup_quotient.{_, 0} ℚ).2.2.2.2.2.1
  let : LocallyCompactSpace (IdeleClassGroup (𝓞 ℚ) ℚ) :=
    (ideleGroup_quotient.{_, 0} ℚ).2.2.2.2.2.2.1
  let : SecondCountableTopology (IdeleClassGroup (𝓞 ℚ) ℚ) := by
    let := idele_secondCountable ℚ
    exact inferInstanceAs (SecondCountableTopology
      (IdeleGroup (𝓞 ℚ) ℚ ⧸ IdeleGroup.principalSubgroup (𝓞 ℚ) ℚ))
  let : (ideleClassTamagawaMeasure ℚ).IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil ℚ).1
  let m : IdeleClassGroup (𝓞 ℚ) ℚ →ₜ* ℝ≥0ˣ :=
    ⟨ideleClassNorm ℚ, (isProperMap_ideleClassNorm ℚ).continuous⟩
  let t : ℝ≥0ˣ := Units.mk0 2 two_ne_zero
  let g : IdeleClassGroup (𝓞 ℚ) ℚ := QuotientGroup.mk (canonicalIdeleNormSection ℚ t)
  have hg : m g = t := canonicalIdeleNormSection_rightInverse ℚ t
  exact Printed.ideleClassSobolev_inversion_automorphism_false_aux
    (ideleClassTamagawaMeasure ℚ) m g (by rw [hg]; norm_num [t]) J hJ

/-- Paper: Announcement before Lemma 10.1.1.3, p. 435. In the a-line
notation the local Fourier transform extends at precisely the half weight. -/
def Printed.sLocalThetaSobolev_fourier_on_line : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (a s : ℝ) (ha : 0 < a) (hs : 0 ≤ s),
    let hp : 0 < a + 0 := by simpa using ha
    let H := ↥(sLocalThetaSobolev F S ha (le_refl (0 : ℝ)) hs hp)
    let j := sLocalThetaSobolevInclusion F S ha (le_refl (0 : ℝ)) hs hp
    (∃ T : H →L[ℂ] H, ∀ f : SchwartzBruhat (Multiplicative (SAdeleRing F S)),
      T (j (Submodule.Quotient.mk f)) =
        j (Submodule.Quotient.mk (sAdeleSchwartzFourier (F := F) (S := S) f))) ↔ a = 1 / 2

/-- Paper: Announcement before Lemma 10.1.1.3, p. 435. Take ℚ, S = {∞},
a = 1/2 and s = 2. For the even tests exp(-πx²) cos(2πNx) the input
norms are bounded, while the Fourier Gaussian peak at N gives a squared
norm growing at least as fast as (log N)². -/
theorem Printed.sLocalThetaSobolev_fourier_on_line_false :
    ¬ Printed.sLocalThetaSobolev_fourier_on_line := by sorry

end RiemannMasullo
